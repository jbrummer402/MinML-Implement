open Int

let bitop = function 
| And -> And(e1, e2)
| Or -> Or(e1, e2)
| Xor -> 
| Not
| LShift
| RShift -> shift_right e1