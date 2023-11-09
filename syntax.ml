type t =
| Unit
| Bool of bool
| Int of int
| Float of float
| Not of t
| Neg of t
| Eq of t * t
| If of t * t * t
| LetRec of fundef * t
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }
