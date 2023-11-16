open Ll
open Llutil
open Asm
open Type


(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements that will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for 
     compiling local variable declarations
*)

type elt = 
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

(* The type of streams of LLVMLite instructions. Note that to improve performance,
 * we will emit the instructions in reverse order. That is, the LLVMLite code:
 *     %1 = mul i64 2, 2
 *     %2 = add i64 1, %1
 *     br label %l1
 * would be constructed as a stream as follows:
 *     I ("1", Binop (Mul, I64, Const 2L, Const 2L))
 *     >:: I ("2", Binop (Add, I64, Const 1L, Id "1"))
 *     >:: T (Br "l1")
 *)
type stream = elt list
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
    let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l ->
           begin match term_opt with
           | None -> 
              if (List.length insns) = 0 then (gs, einsns, [], None, blks)
              else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                               no terminator" l
           | Some term ->
              (gs, einsns, [], None, (l, {insns; term})::blks)
           end
        | T t  -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid,insn)  -> (gs, einsns, (uid,insn)::insns, term_opt, blks)
        | G (gid,gdecl) -> ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
        | E (uid,insn)  -> (gs, (uid, insn)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
    in
    match term_opt with
    | None -> failwith "build_cfg: entry block has no terminator" 
    | Some term -> 
       let insns = einsns @ insns in
       ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Asm.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Asm.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Asm.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id:Asm.id) (c:t) : (Ll.ty * Ll.operand) option =
    try Some (lookup_function id c) with _ -> None
  
end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The 
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Asm.ty -> Ll.ty = function
  | Asm.TBool  -> I1
  | Asm.TInt   -> I64
  | Asm.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Asm.rty -> Ll.ty = function
  | Asm.RString  -> I8
  | Asm.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Asm.RFun (ts, t) -> 
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Asm.ret_ty -> Ll.ty = function
  | Asm.RetVoid  -> Void
  | Asm.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Asm.binop -> Asm.ty * Asm.ty * Asm.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lte | Gte | Eq  | Neq | Lt  | Gt  -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Asm.unop -> Asm.ty * Asm.ty = function
  | Bitnot | Neg -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
   writing this, I think it could make sense to factor the Oat grammar in this
   way, which would make things clearerhw, I may do that for next time around.]]

 
   Consider globals7.oat (in hw5programs)

   /--------------- globals7.oat ------------------ 
   global arr = int[] null;

   int foo() { 
     var x = new int[3]; 
     arr = x; 
     x[2] = 3; 
     return arr[2]; 
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has 
       the same type as @arr 

   (2) @oat_alloc_array allocates len+1 i64's 

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7 


   (4) stores the resulting array value (itself a pointer) into %_x7 

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed 
      to by %_x7 

  (6) store the array value (a pointer) into @arr 

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] }, 
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7 

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },                
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr 

  (11)  calculate the array index offset

  (12) load the array value at the index 

*)

(* Global initialized arrays:

  There is another wrinkle: to compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast 
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* ) 
  @_global_arr5 = global { i64, [4 x i64] } 
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }

*) 



(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the satck, in bytes.  
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Asm.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t:Asm.ty) (size:Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]




(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression. 

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a 
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

*)
let rec cmp_exp (c:Ctxt.t) (exp:Asm.exp node) : Ll.ty * Ll.operand * stream =
  match exp.elt with
  | Id id -> begin match Ctxt.lookup_function_option id c with
      | None -> let uid = gensym id in
        let ty, op = Ctxt.lookup id c
        in let t = begin match ty with 
          Ptr typ -> typ | _ -> Void end in
        t, Id uid, [I (uid, Load (ty, op))] 
      | Some (t, f) -> t, f, [] end
  | CStr str -> let ans_id, str_id = gensym "s", gensym "string" in
    let str_t = Array (1+(String.length str), I8) in  
    Ptr I8, Id ans_id, [G (str_id, (str_t, GString str))] >::
    I (ans_id, Gep (Ptr str_t, Gid str_id, [Const 0L; Const 0L])) 
  | CNull rty -> cmp_ty (TRef rty), Null, [] 
  | CInt  i   -> cmp_ty TInt, Const i, []
  | CBool b   -> cmp_ty TBool, 
    Const (if b then 1L else 0L), [] 
  | CArr (ty, es) -> let size = List.length es |> Int64.of_int in
    let arr_ty, arr_id, arr_insns = oat_alloc_array ty (Const size) in
    let t = cmp_ty ty in 
    let init = gensym "index_ptr" in 
    let init_insns, tail = if size > 0L then 
        let _, first, insn = cmp_exp c (List.hd es) in 
        let insns = insn >@ lift 
          [ init, Gep   (arr_ty, arr_id, [Const 0L; Const 1L; Const 0L]);
            init, Store (t, first, Id init) ] in
            insns, List.tl es 
      else [],[] 
    in let insns, _ = List.fold_left 
           (fun (insns,prev) e -> 
              let _, op, code = cmp_exp c e  in
              let index = gensym "index_ptr" in 
                insns >@ code >@ lift 
              [ index, Gep   (Ptr t, prev, [Const 1L]);
                index, Store (t, op, Id index) ], Id index)
           ([], Id init) tail in 
    arr_ty, arr_id, arr_insns >@ init_insns >@ insns
  | NewArr (t, e) -> let _, size, prelude = cmp_exp c e in
    let arr_ty, arr_id, arr_insns = oat_alloc_array t size in
        arr_ty, arr_id, prelude >@ arr_insns 
  | Index (arr_e, ind_e) ->
    let t, arr, code  = cmp_exp c arr_e in
    let _, ind, code2 = cmp_exp c ind_e in
    let index = gensym "index_ptr" in
    let value = gensym "index" in
    let val_t = begin match t with 
      | Ptr (Struct [I64; Array(0, ty)]) -> ty 
      | _ -> Void end in
    val_t, Id value, code >@ code2 >@ lift
    [ index, Gep  (t, arr, [Const 0L; Const 1L; ind]);
      value, Load (Ptr val_t, Id index) ]
  | Call (e, es) -> 
    let params, insns = List.fold_left
        (fun (p, ins) expr -> 
           let t, op, i = cmp_exp c expr 
           in p @ [t,op], ins >@ i) 
        ([],[]) es in 
    let fty, fop, fcode = cmp_exp c e in
    let t = begin match fty with 
      | Ptr (Fun ( _, ret)) -> ret 
      | _ -> failwith "not a function" end
    in let ans_id = gensym "call" in 
    t, Id ans_id, insns >@ fcode >:: 
    I (ans_id, Call (t, fop, params)) 
  | Bop (bop, e1, e2) ->
    let op_ty, _, ans_ty = typ_of_binop bop in
    let _, op1, prelude  = cmp_exp c e1 in
    let _, op2, prelude2 = cmp_exp c e2 in
    let ans_id = gensym "binop" in 
    let  ans_t = cmp_ty ans_ty  in
    let      t = cmp_ty  op_ty  in 
    let ins = begin match bop with 
      | Add  -> Binop (Add,  t, op1, op2) 
      | Sub  -> Binop (Sub,  t, op1, op2)
      | Mul  -> Binop (Mul,  t, op1, op2)
      | Eq   -> Icmp  (Eq,   t, op1, op2)
      | Neq  -> Icmp  (Ne,   t, op1, op2)
      | Lt   -> Icmp  (Slt,  t, op1, op2)
      | Lte  -> Icmp  (Sle,  t, op1, op2)
      | Gt   -> Icmp  (Sgt,  t, op1, op2)
      | Gte  -> Icmp  (Sge,  t, op1, op2)
      | And  -> Binop (And,  t, op1, op2)
      | Or   -> Binop (Or,   t, op1, op2)
      | IAnd -> Binop (And,  t, op1, op2)
      | IOr  -> Binop (Or,   t, op1, op2)
      | Shl  -> Binop (Shl,  t, op1, op2)
      | Shr  -> Binop (Lshr, t, op1, op2)
      | Sar  -> Binop (Ashr, t, op1, op2)
    end in ans_t, Id ans_id, prelude >@ 
           prelude2 >:: I (ans_id, ins) 
  | Uop (uop, e) -> 
    let t, op, prelude = cmp_exp c e
    in let ans_id = gensym "unop" in 
    let insns = begin match uop with
      | Neg    -> [ ans_id, Binop (Mul, t, Const (-1L), op) ]  
      | Lognot -> [ ans_id, Binop (Xor, t, Const    1L, op) ] 
      | Bitnot -> let neg = gensym "neg" in 
                  [    neg, Binop (Mul, t, Const (-1L), op);
                    ans_id, Binop (Add, t, Const (-1L), Id neg) ] 
    end in t, Id ans_id, prelude >@ lift insns

(* Compile a statement in context c with return typ rt. Return a new context, 
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable 
     declarations
   
   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

 *)
let rec cmp_stmt (c:Ctxt.t) (rt:Ll.ty) (stmt:Asm.stmt node) : Ctxt.t * stream =
  match stmt.elt with 
  | Assn (lhs, e) -> let t, src, code = cmp_exp c e 
    in begin match lhs.elt with 
      | Id id -> let _, dest = Ctxt.lookup id c in 
        c, code >:: I (id, Store (t, src, dest))
      | Index (arr_e, ind_e) -> 
        let ty, arr, code2 = cmp_exp c arr_e in
        let  _, ind, code3 = cmp_exp c ind_e in
        let index = gensym "index_ptr" in 
        c, code >@ code2 >@ code3 >@ lift
        [ index, Gep (ty, arr, [Const 0L; Const 1L; ind]);
          index, Store (t, src, Id index) ] 
      | _ -> failwith "Invalid assignment." end 
  | Decl (uid, e) -> let slot = gensym uid 
    in let t, op, prelude = cmp_exp c e in
    Ctxt.add c uid (Ptr t, Id slot), 
    prelude>:: E (slot, Alloca t)>:: 
    I (slot, Store (t, op, Id slot)) 
  | Ret (e_opt) -> c, begin match e_opt with 
      | None   -> [ T (Ret (Void, None)) ]
      | Some e -> let t, op, code = cmp_exp c e 
        in code >:: T (Ret (t, Some op)) end  
  | SCall (e, es) ->
    let params, insns = List.fold_left
        (fun (p, ins) expr ->
           let t, op, i = cmp_exp c expr
           in p @ [t,op], ins >@ i)
        ([],[]) es in
    let fty, fop, fcode = cmp_exp c e in
    let t = begin match fty with
      | Ptr (Fun ( _, ret)) -> ret
      | _ -> failwith "not a function" end
    in let ans_id = gensym "call" in
    c, insns >@ fcode >:: 
    I (ans_id, Call (t, fop, params))
  | If (e, b1, b2) -> 
    let _, bool_id, bool_code = cmp_exp c e in
    let br1_id = gensym "branch" in 
    let br2_id = gensym "branch" in
    let after  = gensym "after"  in
    let c',  br1 = cmp_block c  rt b1 in  
    let c'', br2 = cmp_block c' rt b2 in 
    c'', bool_code >::
        T (Cbr (bool_id, br1_id, br2_id)) >:: 
         L br1_id >@ br1 >:: T (Br after) >:: 
         L br2_id >@ br2 >:: T (Br after) >:: L after
  | For (vs, e, s, b) -> 
    let c', insns = List.fold_left 
        (fun (c, code) (uid, e) -> 
           let var = gensym uid in
           let t, op, prelude = cmp_exp c e in
           Ctxt.add c uid (Ptr t, Id var), code >@ 
           prelude >:: E(var, Alloca t)>:: 
           I (var, Store (t, op, Id var))) 
        (c, []) vs in
    let loop  = gensym "for"  in 
    let body  = gensym "do"   in 
    let after = gensym "done" in
    let c'',br = cmp_block c' rt @@
      b @ begin match s with None -> [] | Some st -> [st] end
    in c'', insns >:: T (Br loop) >:: L loop >@ 
    begin match e with 
      | None -> [T (Br body)] 
      | Some expr -> let _, bool_id, bool_code = 
        cmp_exp c' expr in bool_code >:: 
        T (Cbr (bool_id, body, after)) end
    >:: L body >@ br >:: T (Br loop) >:: L after
  | While (e, b) -> 
    let loop  = gensym "while" in
    let body  = gensym "do"    in
    let after = gensym "done"  in 
    let c',br = cmp_block c rt b in
    let _, bool_id, bool_code = cmp_exp c e in 
    c', [T (Br loop)] >:: L loop >@  bool_code >:: 
      T (Cbr (bool_id, body, after)) >:: 
      L body >@ br >:: T (Br loop)   >:: L after


(* Compile a series of statements *)
and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Asm.block) : Ctxt.t * stream =
  List.fold_left (fun (c, code) s -> 
      let c', stmt_code = cmp_stmt c rt s in
      c', code >@ stmt_code
    ) (c,[]) stmts



(* Adds each function identifer to the context at an
   appropriately translated type.  

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c:Ctxt.t) (p:Asm.prog) : Ctxt.t =
    List.fold_left (fun c -> function
      | Asm.Gfdecl { elt={ frtyp; fname; args } } ->
         let ft = TRef (RFun (List.map fst args, frtyp)) in
         Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c
    ) c p 

(* Populate a context with bindings for global variables 
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C). 
*)
let cmp_global_ctxt (c:Ctxt.t) (p:Asm.prog) : Ctxt.t =
  List.fold_left (fun c -> function
      | Asm.Gvdecl { elt={name; init}; _ } ->
        let t, _, _ = cmp_exp c init in 
        Ctxt.add c name (Ptr t, Gid name)  
      | _ -> c) c p 

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from 
 *)
let cmp_fdecl (c:Ctxt.t) (f:Asm.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list =
  let {frtyp; args; body; _ } = f.elt in
  let c',arg_types,entry = List.fold_left 
      (fun (c,ts,e) arg -> 
         let t   = cmp_ty (fst arg) in
         let uid = gensym (snd arg) in  
         Ctxt.add c (snd arg) (Ptr t, Id uid), 
         ts @ [t], e >:: E (uid, Alloca t) >::
         I (uid, Store(t, Id (snd arg), Id uid)))
      (c,[],[]) args in
  let f_param = List.map snd args in 
  let f_ty = arg_types, cmp_ret_ty frtyp in 
  let _, code = cmp_block c' (snd f_ty) body in 
  let f_cfg, gdecls = cfg_of_stream (entry >@ code) in 
  { f_ty=f_ty; f_param=f_param ; f_cfg=f_cfg }, gdecls

(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)
let rec cmp_gexp c (e:Asm.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  match e.elt with 
  | CNull rty -> (cmp_ty (TRef rty), GNull), [] 
  | CBool b -> let i = if b then 1L else 0L 
    in (cmp_ty TBool, GInt i), [] 
  | CInt integer -> (cmp_ty TInt, GInt integer), [] 
  | CStr str -> let str_id = gensym "string" in  
    let str_t = Array (1 + (String.length str), I8) in 
    (Ptr I8, GBitcast (Ptr str_t, GGid str_id, Ptr I8)), 
    [str_id, (str_t, GString str)] 
  | CArr (t, es) -> let size = List.length es |> Int64.of_int in
    let elems, decls = List.fold_left
        (fun (params,decllst) e -> 
           let gdecl, decls' = cmp_gexp c e in 
           params @ [gdecl], decllst >@ decls') 
        ([],[]) es in
    let arr = gensym "global_array" in
    let init_arr_t = Struct [I64; Array(List.length es, cmp_ty t)]
    in let init_arr= Array(List.length es, cmp_ty t), GArray elems
    in let  arr_ty = cmp_ty @@ TRef (RArray t) in 
    (arr_ty, GBitcast (Ptr init_arr_t, GGid arr, arr_ty)), 
    decls >@ [arr, (init_arr_t, GStruct [I64, GInt size; init_arr])]  
  | _ -> failwith "Invalid global initializer." 


(* Oat internals function context ------------------------------------------- *)
let internals = [
    "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Asm.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt = 
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls = 
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Asm.Gvdecl { elt=gd } -> 
           let ll_gd, gs' = cmp_gexp c gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Asm.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
