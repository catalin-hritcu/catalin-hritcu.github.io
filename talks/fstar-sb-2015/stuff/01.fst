(*val factorial: x:int{x>=0} -> Tot int *)
(* val factorial: int -> int   =   int -> ML int   -- inferred by default*)
(*val factorial : nat -> Tot nat*)
(* val factorial : x:int -> Pure int (requires (x >= 0)) (ensures (fun r -> r >= 1)) *)
(*val factorial : x:int{x>=0} -> Tot (r:int{r>=0})*)
(* val factorial : x:int{x>=4} -> Tot (r:int{r>=2}) *)
val factorial : x:nat -> Tot (r:int{r>=0})
let rec factorial n = if n = 0 then 1 else n * factorial (n - 1)

(*
val factorial_larger_than_four : x:int{x>=4} -> Lemma (factorial x >= 2)
let rec factorial_larger_than_four x = ()
*)

val factorial_is_monotone4 : x:nat{x > 2} -> Tot (r:unit{factorial x > x})
let rec factorial_is_monotone4 x =
  match x with
  | 3 -> ()
  | _ -> factorial_is_monotone4 (x-1)
