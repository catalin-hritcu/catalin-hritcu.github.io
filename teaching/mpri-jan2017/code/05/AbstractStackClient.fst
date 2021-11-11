module AbstractStackClient

open AbstractStack

let main() : Tot stack =
  let s = push 1 (push 2 (push 3 empty)) in
  let t = top s in
  let s' = pop s in
  (* pop s' -- Subtyping check failed;
       expected type (s:stack{~(is_empty s)}); got type stack *)
  
  (* call lemma explicitly; could also use SMT pattern to apply automatically *)
  pop_push 1 (push 2 (push 3 empty));
  pop s'
