(** * IndProp: Inductively Defined Propositions *)
 
Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
Require Coq.omega.Omega.

(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and existential
    quantification.  In this chapter, we bring yet another new tool
    into the mix: _inductive definitions_. *)

(** In past chapters, we have seen two ways of stating that a number
    [n] is even: We can say

      (1) [evenb n = true], or

      (2) [exists k, n = double k].

    Yet another possibility is to say that [n] is even if we can
    establish its evenness from the following rules:

       - Rule [ev_0]: The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even. *)

(** Such definitions are often presented using _inference
    rules_, they consist of a line separating the _premises_ above
    from the _conclusion_ below: 

                              ------------             (ev_0)
                                 even 0

                                 even n
                            ----------------          (ev_SS)
                             even (S (S n))
*)

(** We can use a _proof tree_ to display the reasoning
    steps demonstrating that [4] is even: 

                             --------  (ev_0)
                              even 0
                             -------- (ev_SS)
                              even 2
                             -------- (ev_SS)
                              even 4
*)

(* ================================================================= *)
(** ** Inductive Definition of Evenness *)

(** Putting all of this together, we can translate the definition of
    evenness into a formal Coq definition using an [Inductive]
    declaration, where each constructor corresponds to an inference
    rule: *)

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).

(** We can think of the definition of [even] as defining a Coq
    property [even : nat -> Prop], together with primitive theorems
    [ev_0 : even 0] and [ev_SS : forall n, even n -> even (S (S n))]. *)

(** That definition can equivalently be written as follows...

  Inductive even : nat -> Prop :=
  | ev_0 : even 0
  | ev_SS : forall n, even n -> even (S (S n)).
*)

(** Such "constructor theorems" have the same status as proven
    theorems.  In particular, we can use Coq's [apply] tactic with the
    rule names to prove [even] for particular numbers... *)

Theorem ev_4 : even 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax: *)

Theorem ev_4' : even 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** We can also prove theorems that have hypotheses involving [even]. *)

Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _reason about_ such evidence.

    Introducing [even] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is even, but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are even (in the sense of [even]). *)

(** In other words, if someone gives us evidence [E] for the assertion
    [even n], then we know that [E] must have one of two shapes:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [even n']). *)

(** This suggests that it should be possible to do _induction_
    and _case analysis_ on evidence of evenness... *)

(* ================================================================= *)
(** ** Inversion on Evidence *)

(** We can prove our characterization of evidence for [even n],
    using [destruct]. *)

Theorem ev_inversion :
  forall (n : nat), even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
  - (* E = ev_0 : even 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : even (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(* QUIZ 

    Which tactics are needed to prove this goal?

  n : nat
  E : even n
  F : n = 1
  ======================
  true = false

   (1) [destruct]

   (2) [discriminate]

   (3) [destruct], [discriminate]

   (4) These tactics are not sufficient to solve the goal. *)
Lemma quiz_1_not_even : forall n, even n -> n = 1 -> true = false.
Proof.
  intros n E F.
  destruct E.
  - discriminate F.
  - discriminate F.
Qed.
(* /QUIZ *)

(** The following theorem can easily be proved using [destruct] on
    evidence. *)

Theorem ev_minus2 : forall n,
  even n -> even (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

(** However, this variation cannot easily be handled with [destruct]. *)

Theorem evSS_ev : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
Abort.

(** The proof is straightforward using our inversion lemma. *)

Theorem evSS_ev : forall n, even (S (S n)) -> even n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm.
   intro Heq. rewrite Heq. apply Hev.
Qed.

(** Coq provides a tactic called [inversion], which does the work of
    our inversion lemma and more besides. *)

Theorem evSS_ev' : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [| n' E' EQ].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductive
    properties, something that takes a bit more work using our
    inversion lemma. For example: *)
Theorem one_not_even : ~ even 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ even 1.
  intros H. inversion H. Qed.

(** We can use [inversion] to reprove some theorems from
    [Tactics.v]. *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** The tactic [inversion] actually works on any [H : P] where
    [P] is defined by [Inductive]:

      - For each constructor of [P], make a subgoal and replace [H] by
        how exactly this constructor could have been used to prove [P].
      - Discard contradictory subgoals (such as [ev_0] above).
      - Generate auxiliary equalities (as with [ev_SS] above). *)

(* QUIZ 

    Which tactics are needed to prove this goal,
    in addition to [simpl] and [apply]?

  n : nat
  E : even (n + 2)
  =====================
  even n

   (1) [inversion]

   (2) [inversion], [discriminate]

   (3) [inversion], [rewrite plus_comm]

   (4) [inversion], [rewrite plus_comm], [discriminate]

   (5) These tactics are not sufficient to prove the goal.

 *)
Lemma quiz_even_plus_2 : forall n, even (n + 2) -> even n.
Proof.
  intros n E.
  rewrite plus_comm in E.
  inversion E.
  apply H0.
Qed.
(* /QUIZ 

    Let's try to show that our new notion of evenness implies
    our earlier notion based on [double]. (The other direction 
    is left as an exercise.) *)

Lemma ev_even_firsttry : forall n,
  even n -> exists k, n = double k.
Proof.
(* WORK IN CLASS *) Admitted.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** Let's try our current lemma again: *)

Lemma ev_even : forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

(** As we will see in later chapters, induction on evidence is a
    recurring technique across many areas, and in particular when
    formalizing the semantics of programming languages, where many
    properties of interest are defined inductively. *)

(* ################################################################# *)
(** * Inductive Relations *)

(** Just as a single-argument proposition defines a _property_,
    a two-argument proposition defines a _relation_. *)

Module Playground.

(** One useful example is the "less than or equal to" relation on
    numbers. *)

Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).

(** Some sanity checks... *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORK IN CLASS *) Admitted.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORK IN CLASS *) Admitted.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORK IN CLASS *) Admitted.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 n (H: even (S n)) : next_even n (S n)
  | ne_2 n (H:even (S (S n))) : next_even n (S (S n)).

(* ################################################################# *)
(** * Case Study: Regular Expressions *)

(** Regular expressions are a simple language for describing sets of
    strings.  Their syntax is defined as follows: *)

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

(** We connect regular expressions and strings via the following
    rules, which define when a regular expression _matches_ some
    string:

      - The expression [EmptySet] does not match any string.

      - The expression [EmptyStr] matches the empty string [[]].

      - The expression [Char x] matches the one-character string [[x]].

      - If [re1] matches [s1], and [re2] matches [s2],
        then [App re1 re2] matches [s1 ++ s2].

      - If at least one of [re1] and [re2] matches [s],
        then [Union re1 re2] matches [s].

      - Finally, if we can write some string [s] as the concatenation
        of a sequence of strings [s = s_1 ++ ... ++ s_k], and the
        expression [re] matches each one of the strings [s_i],
        then [Star re] matches [s].

        As a special case, the sequence of strings may be empty, so
        [Star re] always matches the empty string [[]] no matter what
        [re] is. *)

(** We can easily translate this informal definition into an
    [Inductive] one as follows.  We use the notation [s =~ re] in
    place of [exp_match s re]; by "reserving" the notation before
    defining the [Inductive], we can use it in the definition! *)

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2) :
             (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1) :
                s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2) :
                s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re)) :
                 (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

(* QUIZ 

    Notice that this clause in our informal definition...

      - The expression [EmptySet] does not match any string.

    ... is not explicitly reflected in the above definition.  Do we
    need to add something?

   (1) Yes, we should add a rule for this.

   (2) No, one of the other rules already covers this case.

   (3) No, the _lack_ of a rule actually gives us the behavior we
       want.

*)
(* /QUIZ *)
Lemma quiz : forall T (s:list T), ~(s =~ EmptySet).
Proof. intros T s Hc. inversion Hc. Qed.
(** Again, for readability, we can also display this definition using
    inference-rule notation. *)

(**

                          ----------------                    (MEmpty)
                           [] =~ EmptyStr

                          ---------------                      (MChar)
                           [x] =~ Char x

                       s1 =~ re1    s2 =~ re2
                      -------------------------                 (MApp)
                       s1 ++ s2 =~ App re1 re2

                              s1 =~ re1
                        ---------------------                (MUnionL)
                         s1 =~ Union re1 re2

                              s2 =~ re2
                        ---------------------                (MUnionR)
                         s2 =~ Union re1 re2

                          ---------------                     (MStar0)
                           [] =~ Star re

                      s1 =~ re    s2 =~ Star re
                     ---------------------------            (MStarApp)
                        s1 ++ s2 =~ Star re
*)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** We can define helper functions for writing down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the list that it receives as an
    argument: *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** Something more interesting: *)

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
(* WORK IN CLASS *) Admitted.

(** Naturally, proofs about [exp_match] often require induction. *)

(** For example, suppose that we wanted to prove the following
    intuitive result: If a regular expression [re] matches some string
    [s], then all elements of [s] must occur as character literals
    somewhere in [re].

    To state this theorem, we first define a function [re_chars] that
    lists all characters that occur in a regular expression: *)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** This lemma from chapter [Logic] will be useful in the proof
    of the main theorem about [re_chars] below. *)

Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  - intros l' a. simpl. split.
    + intros H. right. apply H.
    + intros [[]|H]. apply H.
  - intros l'' a. simpl. rewrite IH. rewrite or_assoc.
    reflexivity. Qed.
(* Sooner: BCP: Recheck the HIDEFROMHTML stuff around here... *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORK IN CLASS *) Admitted.

(* ================================================================= *)
(** ** The [remember] Tactic *)

(** One potentially confusing feature of the [induction] tactic is
    that it will let you try to perform an induction over a term that
    isn't sufficiently general.  The effect of this is to lose
    information (much as [destruct] without an [eqn:] clause can do),
    and leave you unable to complete the proof.  Here's an example: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** A naive first attempt at setting up the induction.  (Note
    that we are performing induction on evidence!) *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** We can get through the first case... *)

  - (* MEmpty *)
    simpl. intros s2 H. apply H.

(** ... but most cases get stuck.  For [MChar], for instance, we
    must show that

    s2 =~ Char x' -> x' :: s2 =~ Char x',

    which is clearly impossible. *)

  - (* MChar. *) intros s2 H. simpl. (* Stuck... *)
Abort.

(** The problem is that [induction] over a Prop hypothesis only works
    properly with hypotheses that are completely general, i.e., ones
    in which all the arguments are variables, as opposed to more
    complex expressions, such as [Star re].

    An awkward way to solve this problem is "manually generalizing" 
    over the problematic expressions by adding explicit equality 
    hypotheses to the lemma: *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** This works, but it requires making the statement of the lemma
    a bit ugly, which is a shame.  Fortunately, there is a better way: *)

Abort.

(** The tactic [remember e as x] causes Coq to (1) replace all
    occurrences of the expression [e] by the variable [x], and (2) add
    an equation [x = e] to the context.  Here's how we can use it to
    show the above result: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

(** We now have [Heqre' : re' = Star re]. *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** The [Heqre'] is contradictory in most cases, allowing us to
    conclude immediately. *)

  - (* MEmpty *)  discriminate.
  - (* MChar *)   discriminate.
  - (* MApp *)    discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.

(** The interesting cases are those that correspond to [Star].  Note
    that the induction hypothesis [IH2] on the [MStarApp] case
    mentions an additional premise [Star re'' = Star re], which
    results from the equality generated by [remember]. *)

  - (* MStar0 *)
    injection Heqre'. intros Heqre'' s H. apply H.

  - (* MStarApp *)
    injection Heqre'. intros H0.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite H0. reflexivity.
      * apply H1.
Qed.

(* ################################################################# *)
(** * Case Study: Improving Reflection *)

(** We've seen that we often need to relate boolean
    computations to statements in [Prop].  Unfortunately, this can
    sometimes result in tedious proof scripts.  Consider: *)

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.
(** The first subcase (where [n =? m = true]) is a bit awkward.

    It would be annoying to have to do this kind of thing all the
    time. *)

(** We can streamline this by defining an inductive proposition that
    yields a better case-analysis principle for [n =? m].
    Instead of generating an equation such as [(n =? m) = true],
    which is generally not directly useful, this principle gives us
    right away the assumption we really need: [n = m]. *)

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H :   P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.

(** The only way to produce evidence for [reflect P true] is by
    showing [P] and using the [ReflectT] constructor.

    If we invert this reasoning, it says we can extract _evidence_ for
    [P] from evidence for [reflect P true]. *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORK IN CLASS *) Admitted.

(** (The right-to-left implication is left as an exercise.) *)

(** The advantage of [reflect] over the normal "if and only if"
    connective is that, by destructing a hypothesis or lemma of the
    form [reflect P b], we can perform case analysis on [b] while at
    the same time generating appropriate hypothesis in the two
    branches ([P] in the first subgoal and [~ P] in the second). *)

(** To use [reflect] to produce a better proof of
    [filter_not_empty_In], we begin by recasting the [eqb_iff_true]
    lemma in terms of [reflect]: *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(** A smoother proof of [filter_not_empty_In] now goes as follows.
    Notice how the calls to [destruct] and [rewrite] are combined into a
    single call to [destruct]. *)

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** This small example shows how reflection gives us a small gain in
    convenience; in larger developments, using [reflect] consistently
    can often lead to noticeably shorter and clearer proof scripts.
    We'll see many more examples in later chapters and in _Programming
    Language Foundations_.

    The use of the [reflect] property has been popularized by
    _SSReflect_, a Coq library that has been used to formalize
    important results in mathematics, including as the 4-color theorem
    and the Feit-Thompson theorem.  The name SSReflect stands for
    _small-scale reflection_, i.e., the pervasive use of reflection to
    simplify small proof steps with boolean computations. *)

