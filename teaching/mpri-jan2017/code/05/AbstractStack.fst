module AbstractStack

  abstract type stack = list int

  abstract val is_empty : stack -> Tot bool
  let is_empty = Nil?

  abstract val empty : s:stack{is_empty s}
  let empty = []

  abstract val push : int -> stack -> Tot (s:stack{~(is_empty s)})
  let push x xs = Cons x xs

  abstract val pop : s:stack{~(is_empty s)} -> Tot stack
  let pop = Cons?.tl

  abstract val top : s:stack{~(is_empty s)} -> Tot int
  let top = Cons?.hd

  val top_push : i:int -> s:stack -> Lemma (top (push i s) = i)
  let top_push i s = ()

  val pop_push : i:int -> s:stack -> Lemma (pop (push i s) = s)
  let pop_push i s = ()

  val push_top_pop : s:stack{~(is_empty s)} ->
                       Lemma (ensures (s = push (top s) (pop s)))
  let push_top_pop s = ()
