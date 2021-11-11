module BinaryTrees

type tree =
  | Leaf : tree
  | Node : root:int -> left:tree -> right:tree -> tree

val map : f:(int -> Tot int) -> tree -> Tot tree
let rec map f t =
  match t with
  | Leaf -> Leaf
  | Node n t1 t2 -> Node (f n) (map f t1) (map f t2)

val find : p:(int -> Tot bool) -> tree -> Tot (option int)
let rec find p t =
  match t with
  | Leaf -> None
  | Node n t1 t2 -> if p n then Some n else
                    if Some? (find p t1) then find p t1
                                         else find p t2

let map_option f o = match o with
                    | Some n -> Some (f n)
                    | None   -> None

let compose f1 f2 x = f1 (f2 x)

val map_find : p:(int -> Tot bool) -> f:(int -> Tot int) -> t:tree ->
  Lemma (find p (map f t) = map_option f (find (compose p f) t))
let rec map_find p f t =
  match t with
  | Leaf -> ()
  | Node n t1 t2 -> map_find p f t1; map_find p f t2

val revert : tree -> Tot tree
let rec revert t =
  match t with
  | Leaf -> Leaf
  | Node n t1 t2 -> Node n (revert t2) (revert t1)

(* simpler than for lists because revert is symmetric, while List.rev is not *)
val revert_involutive : t:tree -> Lemma (revert (revert t) = t)
let rec revert_involutive t =
  match t with
  | Leaf -> ()
  | Node n t1 t2 -> revert_involutive t1; revert_involutive t2

(* again, much simpler than for lists *)
val revert_injective : t1:tree -> t2:tree ->
  Lemma (requires (revert t1 = revert t2)) (ensures (t1 = t2))
let rec revert_injective t1 t2 =
  match t1, t2 with
  | Leaf, Leaf -> ()
  | Node n t11 t12, Node n t21 t22 -> revert_injective t11 t21;
                                      revert_injective t12 t22


val remove_root : t:tree{Node? t} -> Tot tree
let rec remove_root t =
  match t with
  | Node n t1 t2 -> if Leaf? t1 then t2
                    else Node (Node?.root t1) (remove_root t1) t2

val add_root : x:int -> t:tree -> Tot (t':tree{Node? t'}) (decreases t)
let rec add_root x t =
  match t with
  | Leaf -> Node x Leaf Leaf
  | Node n t1 t2 -> Node x (add_root n t1) t2

(* remove and add implemented this way round-trip *)
val remove_add_root : x:int -> t:tree ->
  Lemma (requires True) (ensures (remove_root (add_root x t) = t))
        (decreases t)
let rec remove_add_root x t =
  match t with
  | Leaf -> ()
  | Node n t1 t2 -> remove_add_root x t1

(* Does the converse hold? Not at all! Base case breaks and can't be fixed. *)
(* val add_remove_root : x:int -> t:tree{Node? t /\ Node? (Node?.left t)} -> *)
(*   Lemma (requires True) (ensures (add_root x (remove_root t) = t)) *)
(*         (decreases t) *)
(* let rec add_remove_root x t = *)
(*   match t with *)
(*   | Node n (Node m t11 t12) t2 -> if Node?t && Node? (Node?.left t11) *)
(*                                   then add_remove_root x t11 else admit() *)

let rec count (x:int) (t:tree) : Tot nat =
  match t with
  | Leaf -> 0
  | Node n t1 t2 -> (if n = x then 1 else 0) + count x t1 + count x t2

let rec remove (x:int) (t:tree{count x t > 0}) : Tot tree (decreases t) =
  match t with
  | Node n t1 t2 -> if x = n then remove_root t else
                    if count x t1 > 0 then Node n (remove x t1) t2
                                      else Node n t1 (remove x t2)

val count_remove_root : t:tree{Node? t} ->
    Lemma (ensures ((count (Node?.root t) (remove_root t)
                   = count (Node?.root t)              t - 1) /\
                    (forall y. y <> Node?.root t ==>
                       count y (remove_root t) = count y t)))
let rec count_remove_root t =
  match t with
  | Node n t1 t2 -> if Leaf? t1 then ()
                    else count_remove_root t1

(*
  t = Node n t1 t2
  
  Case t1 = Leaf
    TS(1): count n t2 = count n (Node n t1 t2) - 1
                   = 1 + count n Leaf + count n t2 - 1
    TS(2): forall y. y <> n ==> count y (remove_root t) = count y t
           TODO: write a proof sketch for this

  Case t1 = Node n' _ _
    TS(1): (count n (remove_root (Node n t1 t2))
       = count n              (Node n t1 t2)  - 1)
    TS(1): (count n (Node n' (remove_root t1) t2))
       = 1 + count n t1 + count n t2 - 1
    TS(1): (if n = n' then 1 else 0) + count n (remove_root t1) + count n t2
       = count n t1 + count n t2
    SubCase n = n'
      by IH(1): count n' (remove_root t1) = count n' t1 - 1
    SubCase n <> n'
      by IH(2): count n (remove_root t1) = count n t1
      
    TS(2): forall y. y <> n ==>
                       count y (remove_root t) = count y t)
           TODO: write a proof sketch for this

 *)

val count_remove : x:int -> t:tree{count x t > 0} ->
    Lemma (requires True)
          (ensures (count x (remove x t) = count x t - 1)) (decreases t)
let rec count_remove x t =
  match t with
  | Leaf -> ()
  | Node n t1 t2 -> if n = x then count_remove_root t else
                    if count x t1 > 0 then count_remove x t1
                                      else count_remove x t2
(*
  Case t = Node n t1 t2
  
  TS: (count x (remove x t) = count x t - 1)
  TS: (count x (remove x (Node n t1 t2)) = count x (Node n t1 t2) - 1)

  SCase n = x
  TS: (count x (remove_root (Node n t1 t2)) = count x (Node n t1 t2) - 1)
    by count_remove_root lemma

  SCase n <> x /\ count x t1 > 0
    TS: count x (Node n (remove x t1) t2)
      = (if n = x then 1 else 0) + count x t1 + count x t2 - 1
    TS: (if n = x then 1 else 0) + count (remove x t1) + count t2
      = (if n = x then 1 else 0) + count x t1 + count x t2 - 1
    TS: count (remove x t1) + count t2
      = count x t1 + count x t2 - 1
    IH: count (remove x t1) = count x t1 - 1

  SCase: n <> x /\ count x t1 = 0 -- TODO (similar)
*)

(* left and right rotation attempt *)

let rotate_left (t:tree{Node? t /\ Node? (Node?.left t)}) : tree =
  match t with
  | Node n t1 t2 -> Node (Node?.root t1) (remove_root t1) (add_root n t2)

let rotate_right (t:tree{Node? t /\ Node? (Node?.right t)}) : tree =
  match t with
  | Node n t1 t2 -> Node (Node?.root t2) (add_root n t1) (remove_root t2)

(* let rotate_left_right (t:tree{Node? t /\ Node? (Node?.right t)}) : *)
(*   Lemma (ensures (rotate_left (rotate_right t) = t)) *)
(* = admit() (\* doesn't work because add_remove_root doesn't work *\) *)

(* remove leftmost node might be easier? *)
