type atomicformula =
  | ATop
  | ABot
  | AVar of string

let eval_atomicformula (phi: atomicformula) (f: (string) -> (bool)) : 
  bool = match phi with
         | ATop -> true 
         | ABot -> false 
         | AVar i -> f i

