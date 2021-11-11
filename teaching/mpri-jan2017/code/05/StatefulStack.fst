module StatefulStack

  open FStar.Heap
  open FStar.ST

  private val s : ref (list int)
  let s = alloc []

  abstract val is_empty_heap : h:heap -> GTot bool
  let is_empty_heap h = Nil? (sel h s)

  abstract val is_empty : unit -> ST bool (requires (fun _ -> True))
             (ensures (fun h0 b h1 -> b = is_empty_heap h1 /\ h0 == h1))
  let is_empty () = Nil? !s

  abstract val make_empty : unit -> ST unit (requires (fun _ -> True))
                                         (ensures (fun _ _ h -> is_empty_heap h))
  let make_empty () = s := []

  (* abstract val push : int -> stack -> Tot (s:stack{~(is_empty s)}) *)
  (* let push x xs = Cons x xs *)

  (* abstract val pop : s:stack{~(is_empty s)} -> Tot stack *)
  (* let pop = Cons?.tl *)

  (* abstract val top : s:stack{~(is_empty s)} -> Tot int *)
  (* let top = Cons?.hd *)
