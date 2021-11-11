(** * Induction: Proof by Induction *)

(* ################################################################# *)
(** * Review *)

(* QUIZ 

    To prove the following theorem, which tactics will we need besides
    [intros] and [reflexivity]?  (1) none, (2) [rewrite], (3)
    [destruct], (4) both [rewrite] and [destruct], or (5) can't be
    done with the tactics we've seen.

    Theorem review1: (orb true false) = true.
*)
(* /QUIZ *)

(* QUIZ 

    What about the next one?

    Theorem review2: forall b, (orb true b) = true.

    Which tactics do we need besides [intros] and [reflexivity]?  (1)
    none (2) [rewrite], (3) [destruct], (4) both [rewrite] and
    [destruct], or (5) can't be done with the tactics we've seen.
*)
(* /QUIZ *)

(* QUIZ 

    What if we change the order of the arguments of [orb]?

    Theorem review3: forall b, (orb b true) = true.

    Which tactics do we need besides [intros] and [reflexivity]?  (1)
    none (2) [rewrite], (3) [destruct], (4) both [rewrite] and
    [destruct], or (5) can't be done with the tactics we've seen.
*)
(* /QUIZ *)

(* QUIZ 

    What about this one?

    Theorem review4 : forall n : nat, 0 + n = n.

    (1) none, (2) [rewrite], (3) [destruct], (4) both [rewrite] and
    [destruct], or (5) can't be done with the tactics we've seen.
*)
(* /QUIZ *)

(* QUIZ 

    What about this?

    Theorem review5 : forall n : nat, n + 0 = n.

    (1) none, (2) [rewrite], (3) [destruct], (4) both [rewrite] and
    [destruct], or (5) can't be done with the tactics we've seen.
*)
(* /QUIZ *)

(* ################################################################# *)
(** * Separate Compilation *)

(** (First use [coqc] to compile [Basics.v] into [Basics.vo] so
    it can be imported here -- detailed instructions are in the full
    version of this chapter...) *)

From LF Require Export Basics.

(* ################################################################# *)
(** * Proof by Induction *)

(** We proved in the last chapter that [0] is a neutral element
    for [+] on the left using just [reflexivity].  The proof that it
    is also a neutral element on the _right_ is trickier... *)

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.
Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

(** And reasoning by cases using [destruct n] doesn't get us much
    further: the branch of the case analysis where we assume [n = 0]
    goes through fine, but in the branch where [n = S n'] for some [n'] we
    get stuck in exactly the same way. *)

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl.       (* ...but here we are stuck again *)
Abort.

(** We need a bigger hammer: the _principle of induction_ over
    natural numbers...

      - If [P(n)] is some proposition involving a natural number [n],
        and we want to show that [P] holds for _all_ numbers, we can
        reason like this:

         - show that [P(O)] holds
         - show that, if [P(n')] holds, then so does [P(S n')]
         - conclude that [P(n)] holds for all [n].

    For example... *)

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.  Qed.

(** Let's try this one together: *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORK IN CLASS *) Admitted.

(** Here's another related fact about addition, which we'll
    need later.  (The proof is left as an exercise.) *)

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* FILL IN HERE *) Admitted.

(* ################################################################# *)
(** * Proofs Within Proofs *)

(** Here's an alternate proof of [mult_0_plus], using an in-line
    assertion instead of a separate lemma.  New tactic: [assert]. *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.

(** Another example of [assert]... *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like plus_comm should do the trick! *)
  rewrite -> plus_comm.
  (* Doesn't work...Coq rewrites the wrong plus! *)
Abort.

(** To use [plus_comm] at the point where we need it, we can introduce
    a local lemma stating that [n + m = m + n] (for the particular [m]
    and [n] that we are talking about here), prove this lemma using
    [plus_comm], and then use it to do the desired rewrite. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.  Qed.

(* ################################################################# *)
(** * Formal vs. Informal Proof *)

(** "_Informal proofs are algorithms; formal proofs are code_." *)

(** An unreadable formal proof: *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Comments and bullets can make things a bit clearer... *)

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.   Qed.

(** ... but it's still nowhere near as readable for a human as
    a careful informal proof: *)

(** - _Theorem_: For any [n], [m] and [p],

      n + (m + p) = (n + m) + p.

    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show

        0 + (m + p) = (0 + m) + p.

      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where

        n' + (m + p) = (n' + m) + p.

      We must show

        (S n') + (m + p) = ((S n') + m) + p.

      By the definition of [+], this follows from

        S (n' + (m + p)) = S ((n' + m) + p),

      which is immediate from the induction hypothesis.  _Qed_. *)

(* ################################################################# *)
(** * More Exercises *)

(** **** Exercise: 3 stars, standard, recommended (mult_comm)  

    Use [assert] to help prove this theorem.  You shouldn't need to
    use induction on [plus_swap]. *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.

(** Now prove commutativity of multiplication.  You will probably
    want to define and prove a "helper" theorem to be used
    in the proof of this one. Hint: what is [n * (1 + k)]? *)

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (more_exercises)  

    Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before you hack!) *)

Check leb.

Theorem leb_refl : forall n:nat,
  true = (n <=? n).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_ble_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem S_nbeq_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (eqb_refl)  

    Prove the following theorem.  (Putting the [true] on the left-hand
    side of the equality may look odd, but this is how the theorem is
    stated in the Coq standard library, so we follow suit.  Rewriting
    works equally well in either direction, so we will have no problem
    using the theorem no matter which way we state it.) *)

Theorem eqb_refl : forall n : nat,
  true = (n =? n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

