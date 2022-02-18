module myList
(* incorrect implementation: *)
let rec ins' = function 
  | x, []      -> [x]
  | x, (y::ys) -> if x < y then y::(x::ys) else (y::(ins'(x,ys)));

let rec sort' = function 
  | []      -> []
  | (x::xs) -> ins' (x, (sort' xs))
 




(* correct implementation: *)
let rec ins'' = function 
  | x, []      -> [x]
  | x, (y::ys) -> if x < y then x::(ins''(y, ys)) else (y::(ins''(x,ys)));

let rec sort'' = function 
  | []      -> []
  | (x::xs) -> ins'' (x, (sort'' xs))

(* binding name for testing: *)
let sort = sort'

