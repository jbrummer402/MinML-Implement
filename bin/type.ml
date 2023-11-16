type t = (* MinCaml(caml2html: type_t) *)
| Unit
| Bool
| Int
| Float
| Fun of t list * t (* arguments are uncurried *)
| Tuple of t list
| Array of t
| Var of t option ref
type ty =
| TBool
| TInt
| TRef of rty
and rty =
| RString
| RArray of ty
| RFun of ty list * ret_ty
and
type ret_ty = 
| RetVoid
| RetVal of ty

type binop =
| Add
| Sub
| Mul
| Eq
| Neq
| Lt
| Lte
| Gt
| Gte
| And
| Or
| IAnd
| IOr
| Shl
| Shr
| Sar

type stmt =
| Assn of exp node * exp node
| Decl of vdecl
| Ret of exp node option
| SCall of exp node * exp node list
| If of exp node * stmt node list * stmt node list
| For of vdecl list * exp node option * stmt node option * stmt node list
| While of exp node * stmt node list

let gentyp () = Var(ref None) (* ���������ѿ����� *)
