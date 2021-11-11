module AbstractQueue

  abstract type queue = list int

  abstract val is_empty : queue -> bool
  let is_empty = Nil?

  abstract val empty : q:queue{is_empty q}
  let empty = []

  abstract val enq : int -> queue -> q:queue{~(is_empty q)}
  let enq x xs = Cons x xs

  abstract val deq : q:queue{~(is_empty q)} -> queue
  let rec deq xs = match xs with
                   | [x] -> []
                   | x1::x2::xs -> x1 :: deq (x2::xs)

  abstract val front : q:queue{~(is_empty q)} -> int
  let rec front xs = match xs with
                     | [x] -> x
                     | x1::x2::xs -> front (x2::xs)

  (* let is_empty_empty () : *)
  (*   Lemma (is_empty empty = true) = () *)

  (* let is_empty_enq (i:int) (q:queue) : *)
  (*   Lemma (is_empty (enq i q) = false) = () *)

  let front_enq (i:int) (q:queue) :
    Lemma (front (enq i q) = (if is_empty q then i else front q)) = ()

  let deq_enq (i:int) (q:queue) :
    Lemma (deq (enq i q) = (if is_empty q then empty else enq i (deq q))) = ()
