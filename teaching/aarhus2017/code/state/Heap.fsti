module Heap

  val heap : Type
  val ref : Type -> Type

  val sel : #a:Type -> heap -> ref a -> GTot a
  val addr_of: #a:Type -> ref a -> GTot nat

  let modifies (s:FStar.TSet.set nat) (h0 h1 : heap) : Type0 =
  (forall (a:Type) (r:ref a).{:pattern (sel h1 r)}
    (~(addr_of r `FStar.TSet.mem` s)) ==> sel h1 r == sel h0 r)
