
Definition reflexive {A:Type} (R : A -> A -> Prop) : Prop :=
  forall a, R a a.

Definition transitive {A:Type} (R : A -> A -> Prop) : Prop :=
  forall a b c, R a b -> R b c -> R a c.


Inductive multi {A:Type} (R : A -> A -> Prop) : A -> A -> Prop :=
  | MRefl  : forall a, multi R a a
  | MOne   : forall a b, R a b -> multi R a b
  | MTrans : forall a b c, multi R a b -> multi R b c -> multi R a c.


Lemma multi_reflexive : forall A (R : A -> A -> Prop),
  reflexive (multi R).
Proof. intros A R. unfold reflexive. apply MRefl. Qed.

Lemma multi_transitive : forall A (R : A -> A -> Prop),
  transitive (multi R).
Proof. intros A R. unfold transitive. apply MTrans. Qed.

Lemma multi_includes : forall A (R : A -> A -> Prop),
  (forall a b, R a b -> multi R a b).
Proof. intros A R. apply MOne. Qed.


Lemma multi_smallest : forall {A} (multi':(A->A->Prop)->(A->A->Prop))
                                  (R:A->A->Prop),
  reflexive (multi' R) ->
  transitive (multi' R) ->
  (forall a b, R a b -> multi' R a b) ->
  (forall a b, multi R a b -> multi' R a b).
Proof.
  intros A multi' R Hrefl Htrans HR a b HRab.
  inversion HRab as [a' E1 E2 |
                     a' b' H E1 E2 |
                     a' ab b' H1 H2 E1 E2].
  - apply Hrefl.
  - apply HR. apply H.
  - apply (Htrans a ab b).
Abort.


Lemma multi_smallest : forall {A} (multi':(A->A->Prop)->(A->A->Prop))
                                  (R:A->A->Prop),
  reflexive (multi' R) ->
  transitive (multi' R) ->
  (forall a b, R a b -> multi' R a b) ->
  (forall a b, multi R a b -> multi' R a b).
Proof.
  intros A multi' R Hrefl Htrans HR a b HRab.
  induction HRab as [a'|
                     a' b' H |
                     a' ab b' H1 IH1 H2 IH2].
  - apply Hrefl.
  - apply HR. apply H. 
  - apply (Htrans a' ab b'). apply IH1. apply IH2.
Qed.


Inductive steps {A:Type} (R : A -> A -> Prop) : A -> A -> Prop :=
  | SRefl : forall a, steps R a a
  | SStep : forall a b c, R a b -> steps R b c -> steps R a c.


Lemma steps_reflexive : forall A (R : A -> A -> Prop),
  reflexive (steps R).
Proof. intros A R. unfold reflexive. apply SRefl. Qed.

Lemma steps_transitive : forall A (R : A -> A -> Prop),
  transitive (steps R).
Proof.
  intros A R. unfold transitive.
  intros a b c HRab HRbc. generalize dependent c.
  induction HRab as [a | a b c HRab HRbc IH].
  + intros c HRac. apply HRac.
  + intros d HRcd. apply (SStep R a b d).
    apply HRab. apply IH. apply HRcd.
Qed.

Lemma steps_includes : forall A (R : A -> A -> Prop),
  (forall a b, R a b -> steps R a b).
Proof. intros A R a b HRab. apply (SStep R a b b).
       apply HRab. apply SRefl. Qed.


Lemma multi_steps : forall {A} (R : A -> A -> Prop),
  forall a b, multi R a b <-> steps R a b.
Proof.
  intros A R a b. split.
  - apply multi_smallest.
    + apply steps_reflexive.
    + apply steps_transitive.
    + apply steps_includes.
  - intros H. induction H as [a | a b c HRab HRbc IH].
    + apply MRefl.
    + apply (MTrans R a b c). apply MOne. apply HRab. apply IH.
Qed.
