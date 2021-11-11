
module InsertionSort

open FStar.List.Tot

(* Check that a list is sorted *)
val sorted: list int -> Tot bool
let rec sorted l = match l with
    | [] | [_] -> true
    | x::y::xs -> (x <= y) && (sorted (y::xs))

(* Fact about sorted *)
val sorted_smaller: x:int
                ->  y:int
                ->  l:list int
                ->  Lemma (requires (sorted (x::l) /\ mem y l))
                          (ensures (x <= y))
                          [SMTPat (sorted (x::l)); SMTPat (mem y l)]
let rec sorted_smaller x y l = match l with
    | [] -> ()
    | z::zs -> if z=y then () else sorted_smaller x y zs

type permutation (l1:list int) (l2:list int) =
    length l1 = length l2 /\ (forall n. mem n l1 = mem n l2)

val insert : i:int -> l:list int{sorted l} -> Tot (r:(list int){sorted r /\ permutation (i::l) r})
let rec insert i l =
  match l with
  | [] -> [i]
  | hd::tl ->
     if i <= hd then i::l
     else hd::(insert i tl)

(* Insertion sort *)
val sort : l:list int -> Tot (m:list int{sorted m /\ permutation l m})
let rec sort l = match l with
    | [] -> []
    | x::xs -> insert x (sort xs)

(* TODO: strengthen the type of insert, or prove a lemma about it to
         make sort type-check *)
