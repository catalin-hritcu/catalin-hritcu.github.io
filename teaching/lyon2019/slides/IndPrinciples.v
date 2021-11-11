(** * IndPrinciples: Induction Principles *)

(** With the Curry-Howard correspondence and its realization in Coq in
    mind, we can now take a deeper look at induction principles. *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export ProofObjects.

(* ################################################################# *)
(** * Basics *)

(** The automatically generated _induction principle_ for [nat]: *)

Check nat_ind.
(*  ===> nat_ind :
           forall P : nat -> Prop,
              P 0  ->
              (forall n : nat, P n -> P (S n))  ->
              forall n : nat, P n  *)

(** In English: Suppose [P] is a property of natural numbers (that is,
      [P n] is a [Prop] for every [n]). To show that [P n] holds of all
      [n], it suffices to show:

      - [P] holds of [0]
      - for any [n], if [P] holds of [n], then [P] holds of [S n]. *)

(** We can directly use the induction principle with [apply]: *)

Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *) simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity.  Qed.

(** Why the [induction] tactic is nicer than [apply]:
     - [apply] requires extra manual bookkeeping (the [intros] in the
       inductive case)
     - [apply] requires [n] to be left universally quantified
     - [apply] requires us to manually specify the name of the induction
       principle. *)

(** Coq generates induction principles for every datatype defined with
    [Inductive], including those that aren't recursive. *)

(** These generated principles follow a similar pattern. If we define
    a type [t] with constructors [c1] ... [cn], Coq generates a
    theorem with this shape:

    t_ind : forall P : t -> Prop,
              ... case for c1 ... ->
              ... case for c2 ... -> ...
              ... case for cn ... ->
              forall n : t, P n

    The specific shape of each case depends on the arguments to the
    corresponding constructor. *)

(** If we define type [t] with constructors [c1] ... [cn],
    Coq generates:

    t_ind : forall P : t -> Prop,
              ... case for c1 ... ->
              ... case for c2 ... -> ...
              ... case for cn ... ->
              forall n : t, P n

    The specific shape of each case depends on the arguments to the
    corresponding constructor. *)

(** An example with no constructor arguments: *)

Inductive time : Type :=
  | day
  | night.

Check time_ind.
(* ===> time_ind : forall P : time -> Prop,
                          P day ->
                          P night ->
                          forall t : time, P t *)

(** Here's another example, this time with one of the constructors
    taking some arguments. *)

(** An example with constructor arguments: *)

Inductive natlist : Type :=
  | nnil
  | ncons (n : nat) (l : natlist).

Check natlist_ind.
(* ===>
   natlist_ind :
      forall P : natlist -> Prop,
         P nnil  ->
         (forall (n : nat) (l : natlist),
            P l -> P (ncons n l)) ->
         forall l : natlist, P l *)

(** In general, the automatically generated induction principle for
    inductive type [t] is formed as follows:

    - Each constructor [c] generates one case of the principle.
    - If [c] takes no arguments, that case is:

      "P holds of c"

    - If [c] takes arguments [x1:a1] ... [xn:an], that case is:

      "For all x1:a1 ... xn:an,
          if [P] holds of each of the arguments of type [t],
          then [P] holds of [c x1 ... xn]"
*)



(* ################################################################# *)
(** * Induction Principles in [Prop] *)

(** From what we've said so far, you might expect the
    inductive definition of [even]...

      Inductive even : nat -> Prop :=
      | ev_0 : even 0
      | ev_SS : forall n : nat, even n -> even (S (S n)).

    ...to give rise to an induction principle that looks like this...

    ev_ind_max : forall P : (forall n : nat, even n -> Prop),
         P O ev_0 ->
         (forall (m : nat) (E : even m),
            P m E ->
            P (S (S m)) (ev_SS m E)) ->
         forall (n : nat) (E : even n),
         P n E
*)

(** The induction priniciples Coq also automatically produces
   for inductively defined properties differ a little bit
   from the induction principles for data types. They are slightly
   less general than you might expect, but consequently easier to use: *)

Print even.
(* ===>
Inductive even : nat -> Prop :=
  | ev_0 : even 0
  | ev_SS : forall n : nat, even n -> even (S (S n))
*)

Check even_ind.
(* ===> even_ind
        : forall P : nat -> Prop,
          P 0 ->
          (forall n : nat, even n -> P n -> P (S (S n))) ->
          forall n : nat,
          even n -> P n *)

(** In particular, Coq has dropped the evidence term [E] as a
    parameter of the the proposition [P]. *)

(** In English, [even_ind] says: Suppose [P] is a property of natural
    numbers (that is, [P n] is a [Prop] for every [n]).  To show that [P n] 
    holds whenever [n] is even, it suffices to show:

      - [P] holds for [0],

      - for any [n], if [n] is even and [P] holds for [n], then [P]
        holds for [S (S n)]. *)

(** The precise form of an [Inductive] definition can affect the
    induction principle Coq generates. *)

Inductive le1 : nat -> nat -> Prop :=
     | le1_n : forall n, le1 n n
     | le1_S : forall n m, (le1 n m) -> (le1 n (S m)).

Notation "m <=1 n" := (le1 m n) (at level 70).

(** [n] could instead be a parameter:  *)

Inductive le2 (n:nat) : nat -> Prop :=
  | le2_n : le2 n n
  | le2_S m (H : le2 n m) : le2 n (S m).

Notation "m <=2 n" := (le2 m n) (at level 70).


Check le1_ind.
(* ===> forall P : nat -> nat -> Prop,
          (forall n : nat, P n n) ->
          (forall n m : nat, n <=1 m -> P n m -> P n (S m)) ->
          forall n n0 : nat, n <=1 n0 -> P n n0 *)

Check le2_ind.
(* ===>  forall (n : nat) (P : nat -> Prop),
           P n ->
           (forall m : nat, n <=2 m -> P m -> P (S m)) ->
           forall n0 : nat, n <=2 n0 -> P n0 *)

(** The latter is simpler, and corresponds to Coq's own
    definition. *)

(* ################################################################# *)
(** * Explicit Proof Objects for Induction (Optional) *)

    
(** Recall again the induction principle on naturals that Coq generates for
    us automatically from the Inductive declation for [nat]. *)

Check nat_ind.
(* ===> 
   nat_ind : forall P : nat -> Prop,
      P 0 -> 
      (forall n : nat, P n -> P (S n)) -> 
      forall n : nat, P n  *)

(** There's nothing magic about this induction lemma: it's just
   another Coq lemma that requires a proof.  Coq generates the proof
   automatically too...  *)

Print nat_ind.
(* ===> (after some slight tidying) 
nat_ind :=
    fun (P : nat -> Prop) 
        (f : P 0) 
        (f0 : forall n : nat, P n -> P (S n)) =>
          fix F (n : nat) : P n :=
             match n with
            | 0 => f
            | S n0 => f0 n0 (F n0)
            end.
*)

(** We can read this as follows: 
     Suppose we have evidence [f] that [P] holds on 0,  and 
     evidence [f0] that [forall n:nat, P n -> P (S n)].  
     Then we can prove that [P] holds of an arbitrary nat [n] via 
     a recursive function [F] (here defined using the expression 
     form [Fix] rather than by a top-level [Fixpoint] 
     declaration).  [F] pattern matches on [n]: 
      - If it finds 0, [F] uses [f] to show that [P n] holds.
      - If it finds [S n0], [F] applies itself recursively on [n0] 
         to obtain evidence that [P n0] holds; then it applies [f0] 
         on that evidence to show that [P (S n)] holds. 
    [F] is just an ordinary recursive function that happens to 
    operate on evidence in [Prop] rather than on terms in [Set].

*)

(**  We can adapt this approach to proving [nat_ind] to help prove
    _non-standard_ induction principles too.  As a motivating example, 
    suppose that we want to prove the following lemma, directly
    relating the [even] predicate we defined in [IndProp] 
    to the [evenb] function defined in [Basics]. *)

Lemma evenb_even : forall n: nat, evenb n = true -> even n. 
Proof.
  induction n; intros.
  - apply ev_0.
  - destruct n.
    + simpl in H. inversion H.
    + simpl in H.
      apply ev_SS.
Abort.

(** Attempts to prove this by standard induction on [n] fail in the case for
    [S (S n)],  because the induction hypothesis only tells us something about
    [S n], which is useless. There are various ways to hack around this problem; 
    for example, we _can_ use ordinary induction on [n] to prove this (try it!):

    [Lemma evenb_even' : forall n : nat,
     (evenb n = true -> even n) /\ (evenb (S n) = true -> even (S n))].

    But we can make a much better proof by defining and proving a
    non-standard induction principle that goes "by twos":
 *)

 Definition nat_ind2 : 
    forall (P : nat -> Prop), 
    P 0 -> 
    P 1 -> 
    (forall n : nat, P n -> P (S(S n))) -> 
    forall n : nat , P n :=
       fun P => fun P0 => fun P1 => fun PSS => 
          fix f (n:nat) := match n with 
                             0 => P0 
                           | 1 => P1 
                           | S (S n') => PSS n' (f n') 
                          end.

 (** Once you get the hang of it, it is entirely straightforward to
     give an explicit proof term for induction principles like this.
     Proving this as a lemma using tactics is much less intuitive.

     The [induction ... using] tactic variant gives a convenient way to
     utilize a non-standard induction principle like this. *)

Lemma evenb_even : forall n, evenb n = true -> even n.
Proof. 
 intros.  
 induction n as [ | |n'] using nat_ind2. 
 - apply ev_0.
 - simpl in H.
   inversion H.
 - simpl in H.
   apply ev_SS.
   apply IHn'.
   apply H. 
Qed.  

(* ################################################################# *)
(** * The Coq Trusted Computing Base *)

(** One issue that arises with any automated proof assistant is "why
    trust it?": what if there is a bug in the implementation that
    renders all its reasoning suspect?

    While it is impossible to allay such concerns completely, the fact
    that Coq is based on the Curry-Howard correspondence gives it a
    strong foundation. Because propositions are just types and proofs
    are just terms, checking that an alleged proof of a proposition is
    valid just amounts to _type-checking_ the term.  Type checkers are
    relatively small and straightforward programs, so the "trusted
    computing base" for Coq -- the part of the code that we have to
    believe is operating correctly -- is small too.

    What must a typechecker do?  Its primary job is to make sure that
    in each function application the expected and actual argument
    types match, that the arms of a [match] expression are constructor
    patterns belonging to the inductive type being matched over and
    all arms of the [match] return the same type, and so on.

    There are a few additional wrinkles:

    - Since Coq types can themselves be expressions, the checker must
      normalize these (by using the computation rules) before
      comparing them.

    - The checker must make sure that [match] expressions are
      _exhaustive_.  That is, there must be an arm for every possible
      constructor.  To see why, consider the following alleged proof
      object:

      Definition or_bogus : forall P Q, P \/ Q -> P :=
        fun (P Q : Prop) (A : P \/ Q) =>
           match A with
           | or_introl H => H
           end. 

      All the types here match correctly, but the [match] only
      considers one of the possible constructors for [or].  Coq's
      exhaustiveness check will reject this definition.

    - The checker must make sure that each [fix] expression
      terminates.  It does this using a syntactic check to make sure
      that each recursive call is on a subexpression of the original
      argument.  To see why this is essential, consider this alleged
      proof:

          Definition nat_false : forall (n:nat), False :=
             fix f (n:nat) : False := f n. 

      Again, this is perfectly well-typed, but (fortunately) Coq will
      reject it. *)

(** Note that the soundness of Coq depends only on the correctness of
    this typechecking engine, not on the tactic machinery.  If there
    is a bug in a tactic implementation (and this certainly does
    happen!), that tactic might construct an invalid proof term.  But
    when you type [Qed], Coq checks the term for validity from
    scratch.  Only lemmas whose proofs pass the type-checker can be
    used in further proof developments.  *)
