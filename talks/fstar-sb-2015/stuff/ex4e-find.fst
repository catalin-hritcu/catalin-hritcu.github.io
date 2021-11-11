module Find

(*
val find: f:('a -> Tot bool) -> l:list 'a ->
      Tot (res:(option 'a){forall x. res = Some x ==> f x})
*)
(* For some reason this doesn't type-check
val find: f:('a -> Tot bool) -> l:list 'a ->
      Tot (res:(option 'a){is_Some res ==> f (Some.v res)})
*)
val find: f:('a -> Tot bool) -> l:list 'a -> Tot (option (x:'a{f x}))
let rec find f l = match l with 
  | [] -> None
  | hd::tl -> if f hd then Some hd else find f tl

val find': f:('a -> Tot bool) -> l:list 'a -> Tot (option 'a)
let rec find' f l = match l with 
  | [] -> None
  | hd::tl -> if f hd then Some hd else find' f tl

val find_correct: f:('a -> Tot bool) -> l:list 'a -> x: 'a ->
      Lemma (requires (find' f l = Some x)) (ensures (f x))
let rec find_correct f l x = match l with
  | [] -> ()
  | (y::l') -> if not (f y) then find_correct f l' x
