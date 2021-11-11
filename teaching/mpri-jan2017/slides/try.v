
Variable st : Type.

Lemma xxx : forall (fpre : st -> Prop) (fpost : st -> nat -> st -> Prop),
            exists (fpre₁ fpre₂ : st -> Prop)
                   (fpost₁ fpost₂ : st -> nat -> st -> Prop),
            forall (p : nat -> st -> Prop) (h₀ : st),
    (fpre h₀ /\ (forall x₂ h₂, fpost h₀ x₂ h₂ -> p x₂ h₂))
<-> (fpre₁ h₀ /\ (forall x₁ h₁, fpost₁ h₀ x₁ h₁ -> fpre₂ h₁ /\ forall x₂ h₂, fpost₂ h₁ x₂ h₂ -> p x₂ h₂)).
Proof.
  intros.
  exists fpre.
  eexists.
  eexists.
  repeat eexists.
  - exact (proj1 H).
  - admit.
  - intros. apply (proj2 H).
    (* fpost₁ = forall h₂, fpost₂ h₁ x₁ h₂ -> fpost h₀ x₂ h₂ *)
    admit.
  - tauto.
  - intros. destruct H as [H1 H2]. edestruct H2. Focus 2.
    apply H3. admit.
Admitted.
