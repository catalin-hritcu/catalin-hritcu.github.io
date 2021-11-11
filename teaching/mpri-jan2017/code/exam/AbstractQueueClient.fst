module AbstractQueueClient

open AbstractQueue

let main() : unit =
  front_enq 3 (enq 2 (enq 1 empty));
  front_enq 2 (enq 1 empty);
  front_enq 1 empty;
  assert(front (enq 3 (enq 2 (enq 1 empty))) = 1);
  deq_enq 3 (enq 2 (enq 1 empty));
  deq_enq 2 (enq 1 empty);
  deq_enq 1 empty;  
  assert(deq (enq 3 (enq 2 (enq 1 empty))) == enq 3 (enq 2 empty))

(* Q1: How many instances of the front_enq lemma are needed to show
       that `front (enq 3 (enq 2 (enq 1 empty))) = 1`?
       Write down all the needed instances.
   Q2: Write a `deq_enq` lemma that allows you to prove that
       `deq (enq 3 (enq 2 (enq 1 empty))) == enq 3 (enq 2 empty)`.
 *)
