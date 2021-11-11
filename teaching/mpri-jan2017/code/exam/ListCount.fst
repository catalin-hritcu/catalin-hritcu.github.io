module ListCount

let rec count (y:int) (xs:list int) : Tot nat (decreases xs) =
  match xs with
  | [] -> 0
  | x :: xs' -> (if x = y then 1 else 0) + count y xs'

let rec remove (y:int) (xs:list int) : Tot (list int) (decreases xs) =
  match xs with
  | [] -> []
  | x :: xs' -> if x = y then remove x xs' else x :: remove y xs'

let rec count_remove_eq (x:int) (xs:list int) :
    Lemma (count x (remove x xs) = 0)
= match xs with
  | [] -> ()
  | _ :: xs' -> count_remove_eq x xs'

let rec count_remove_neq (y1:int) (y2:int) (xs:list int) :
    Lemma (requires (y1 <> y2))
          (ensures (count y1 (remove y2 xs) = count y1 xs)) (decreases xs)
= match xs with
  | [] -> ()
  | _ :: xs' -> count_remove_neq y1 y2 xs'

(* Removing all elements in a list from another list *)

let rec remove_list (ys:list int) (xs:list int) : Tot (list int) (decreases ys) =
  match ys with
  | [] -> xs
  | y'::ys' -> remove y' (remove_list ys' xs)

val count_remove_list_mem (y:int) (ys:list int) (xs:list int) :
    Lemma (requires (count y ys > 0))
          (ensures (count y (remove_list ys xs) = 0))
let rec count_remove_list_mem y ys xs =
  match ys with
  | y' :: ys' -> if y = y'
                 then count_remove_eq y (remove_list ys' xs)
                 else (count_remove_neq y y' (remove_list ys' xs);
                       count_remove_list_mem y ys' xs)
(* Sketch: ys = y'::ys'
   TS: count y (remove_list (y'::ys') xs) = 0
   TS: count y (remove_all y' (remove_list ys' xs)) = 0
   Case y == y': by count_remove_eq the above holds directly
   Case y <> y': by count_remove_neq
     TS: count y (remove_list ys' xs) = 0
     which is immediate by the induction hypothesis *)

(* Funnier, would be to remove all tree elements from a list?
   At least they would be less likely to mix up the two :) *)

(* Showing that the elements not in ys were not affected *)
val count_remove_list_nmem (y:int) (ys:list int) (xs:list int) :
    Lemma (requires (count y ys = 0))
          (ensures (count y (remove_list ys xs) = count y xs))
let rec count_remove_list_nmem y ys xs =
  match ys with
  | [] -> () (* <-- this case would have prevented my bug *)
  | y' :: ys' -> if y <> y' then
                   (count_remove_neq y y' (remove_list ys' xs);
                    count_remove_list_nmem y ys' xs)

(* Removing exactly the first n occurences of x from xs *)

let rec remove_first (n:nat) (x:int) (xs:list int{count x xs >= n}) :
    Tot (list int) (decreases xs) =
  if n = 0 then xs else
  match xs with
  | [] -> []
  | x' :: xs' -> if x = x' then       remove_first (n-1) x xs'
                           else x' :: remove_first n     x xs'

(* this one is easy *)
let rec remove_first_remove (x:int) (xs:list int) :
    Lemma (remove x xs = remove_first (count x xs) x xs) =
  match xs with
  | [] -> ()
  | x'::xs'  -> remove_first_remove x xs'

let rec remove_one (x:int) (xs:list int{count x xs > 0}) : Tot (list int) =
  match xs with
  | x' :: xs' -> if x = x' then xs' else x' :: remove_one x xs'

let rec count_remove_first (n:nat) (x:int) (xs:list int{count x xs >= n}) :
    Lemma (requires True)
          (ensures (count x (remove_first n x xs) = count x xs - n)) (decreases xs)
= if n = 0 then () else
  match xs with
  | [] -> ()
  | x' :: xs' -> if x = x' then count_remove_first (n-1) x xs'
                           else count_remove_first n x xs'

(* this one is easy too, since I *have* to give them
   count_remove_first just to state this *)

let rec remove_first_remove_one (n:nat) (x:int) (xs:list int{count x xs >= n}) :
     Lemma (remove_first n x xs = (if n = 0 then xs
                                   else (count_remove_first (n-1) x xs;
                                         remove_one x (remove_first (n-1) x xs)))) =
  if n = 0 then () else
  match xs with
  | [] -> ()
  | x'::xs' -> remove_first_remove_one (if x = x' then n-1 else n) x xs'

(* Defining a silly variant of remove that we prove equivalent *)
(* Problem: this is very unnatural, which makes the proof unintuitive *)

let rec count_remove_one (x:int) (xs:list int{count x xs > 0}) :
    Lemma (requires True)
          (ensures (count x (remove_one x xs) = count x xs - 1)) (decreases xs)
= match xs with
  | x' :: xs' -> if x = x' then () else count_remove_one x xs'

let rec remove' (x:int) (xs:list int) :
    Tot (list int) (decreases (count x xs)) =
  if count x xs > 0 then (count_remove_one x xs; remove' x (remove_one x xs))
                    else xs

let rec remove'_cons (x:int) (x':int) (xs':list int) :
    Lemma (requires (x <> x'))
          (ensures (remove' x (x'::xs') = x' :: remove' x xs'))
          (decreases (count x (x'::xs'))) = 
  if count x xs' = 0 then ()
  else (count_remove_one x xs'; remove'_cons x x' (remove_one x xs'))

let rec remove_remove' (x:int) (xs:list int) :
    Lemma (requires True)
          (ensures (remove x xs = remove' x xs)) (decreases xs) = 
  match xs with
  | [] -> ()
  | x' :: xs' -> (remove_remove' x xs'; if x <> x' then remove'_cons x x' xs')
