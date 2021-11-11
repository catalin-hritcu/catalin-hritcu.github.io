(** * Lists: Working with Structured Data *)

From LF Require Export Induction.
Module NatList.

(* ################################################################# *)
(** * Pairs of Numbers *)

(** Here's an [Inductive] with just one constructor (taking two
    arguments): *)

Inductive natprod : Type :=
| pair (n1 n2 : nat).

Check (pair 3 5).

(** We define extraction functions by pattern matching. *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

(** A nicer notation for pairs: *)

Notation "( x , y )" := (pair x y).

(** The new pair notation can be used both in expressions and in
    pattern matches. *)

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(** Let's try to prove a few simple facts about pairs.

    If we state things in a slightly peculiar way, we can complete
    proofs with just reflexivity (and its built-in simplification): *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

(** But [reflexivity] is not enough if we state the lemma in a more
    natural way: *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

(** Solution: use [destruct]. *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.

(* ################################################################# *)
(** * Lists of Numbers *)

(** An inductive definition of _lists_ of numbers: *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(** Some notation for lists to make our lives easier: *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** Now these all mean exactly the same thing: *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(* ----------------------------------------------------------------- *)
(** *** Repeat *)

(** Some useful list-manipulation functions: *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(* ----------------------------------------------------------------- *)
(** *** Length *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* ----------------------------------------------------------------- *)
(** *** Append *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Head (With Default) and Tail *)

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.

(* QUIZ 

    What does the following function do? *)

Fixpoint foo (n:nat) : natlist :=
  match n with
  | 0 => nil
  | S n' => n :: (foo n')
  end.

(** (Submit any response when you have the answer.) *)
(* /QUIZ *)

(* ################################################################# *)
(** * Reasoning About Lists *)

(** As for numbers, some proofs about list functions need only
    simplification... *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(** ...and some need case analysis. *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.  Qed.

(** Usually, though, interesting theorems about lists require
    induction for their proofs. *)

(* ================================================================= *)
(** ** Induction on Lists *)

(** Coq generates an induction principle for every [Inductive]
    definition, including lists.  We can use the [induction] tactic on
    lists to prove things like the associativity of list-append... *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** For comparison, here is an informal proof of the same theorem. *)

(** _Theorem_: For all lists [l1], [l2], and [l3],
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)].

   _Proof_: By induction on [l1].

   - First, suppose [l1 = []].  We must show

       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),

     which follows directly from the definition of [++].

   - Next, suppose [l1 = n::l1'], with

       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)

     (the induction hypothesis). We must show

       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).

     By the definition of [++], this follows from

       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),

     which is immediate from the induction hypothesis.  [] *)

(* ----------------------------------------------------------------- *)
(** *** Reversing a List *)

(** A bigger example of induction over lists. *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [rev] *)

(** Let's try to prove [length (rev l) = length l]. *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = n :: l' *)
    simpl.
    rewrite <- IHl'.
Abort.

(** We can prove a lemma to bridge the gap. *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORK IN CLASS *) Admitted.

(** Now we can complete the original proof. *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'. rewrite plus_comm.
    reflexivity.
Qed.

(* QUIZ 

    To prove the following theorem, which tactics will we need besides
    [intros], [simpl], [rewrite], and [reflexivity]?  (1) none, (2) [destruct],
    (3) [induction on n], (4) [induction on l], or (5) can't be
    done with the tactics we've seen.

      Theorem foo1 : forall n :nat, forall l: natlist,
        repeat n 0 = l -> length l = 0.
*)
(* /QUIZ *)

(* QUIZ 

    What about the next one?

      Theorem foo2 :  forall n m:nat, forall l: natlist,
        repeat n m = l -> length l = m.

    Which tactics do we need besides [intros], [simpl], [rewrite], and
    [reflexivity]?  (1) none, (2) [destruct],
    (3) [induction on m], (4) [induction on l], or (5) can't be
    done with the tactics we've seen.
*)
(* /QUIZ *)

(* QUIZ *)

(** What about this one?

      Theorem foo3: forall n :nat, forall l1 l2: natlist,
        l1 ++ [n] = l2 -> (1 <=? (length l2)) = true.

    Which tactics do we need besides [intros], [simpl], [rewrite], and
    [reflexivity]?  (1) none, (2) [destruct],
    (3) [induction on n], (4) [induction on l1], (5) [induction on l2],
    (6) can't be done with the tactics we've seen.
*)
(* /QUIZ *)

(* ################################################################# *)
(** * Options *)

(** We'd like to write a function to retrieve the [n]th element
    of a list, but what if the list is too short? *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42  (* arbitrary! *)
  | a :: l' => match n =? O with
               | true => a
               | false => nth_bad l' (pred n)
               end
  end.

(** The solution: [natoption]. *)

Inductive natoption : Type :=
  | Some (n : nat)
  | None.


Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n =? O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(** We can also write this function using Coq's "if" expressions. *)

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if n =? O then Some a
               else nth_error' l' (pred n)
  end.

End NatList.

(* ################################################################# *)
(** * Partial Maps *)

(** As a final illustration of how data structures can be defined in
    Coq, here is a simple _partial map_ data type, analogous to the
    map or dictionary data structures found in most programming
    languages. *)

(** First, we define a new inductive datatype [id] to serve as the
    "keys" of our partial maps. *)

Inductive id : Type :=
  | Id (n : nat).

(** Internally, an [id] is just a number.  Introducing a separate type
    by wrapping each nat with the tag [Id] makes definitions more
    readable and gives us the flexibility to change representations
    later if we wish. *)

(** We'll also need an equality test for [id]s: *)

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

(** **** Exercise: 1 star, standard (eqb_id_refl)  *)
Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Now we define the type of partial maps: *)

Module PartialMap.
Export NatList.
  
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

(** The [update] function overrides the entry for a given key in a
    partial map by shadowing it with a new one (or simply adds a new
    entry if the given key is not already present). *)

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

(** We can define functions on [partial_map] by pattern
    matching, as always. *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

(* QUIZ 

    Is the following claim true or false? *)
Theorem quiz1 : forall (d : partial_map)
                       (x : id) (v: nat),
  find x (update d x v) = Some v.

Proof.
(* FILL IN HERE *) Admitted.

(** (1) True

    (2) False

    (3) Not sure
*)
(* /QUIZ *)

(* QUIZ 

    Is the following claim true or false? *)

Theorem quiz2 : forall (d : partial_map)
                       (x y : id) (o: nat),
  eqb_id x y = false ->
  find x (update d y o) = find x d.
Proof.
(* FILL IN HERE *) Admitted.

(** (1) True

    (2) False

    (3) Not sure
*)

(* /QUIZ *)
End PartialMap.

