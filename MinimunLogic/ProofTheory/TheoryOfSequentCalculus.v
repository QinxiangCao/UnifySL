Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.

Section PropertiesOfSequentCalculus.

Context (L: Language)
        (Gamma: ProofTheory L).
 
Definition DerivableRefl: Prop :=
  forall x: expr, empty_context;; x |-- x.

Definition DeductionWeaken: Prop :=
  forall (Phi Psi: context) (x: expr), Included _ Phi Psi -> Phi |-- x -> Psi |-- x.

Definition DerivableAssu: Prop :=
  forall (Phi: context) (x: expr), Ensembles.In _ Phi x -> Phi |-- x.

Definition DeductionSubst: Prop :=
  forall (Phi: context) (x y: expr), Phi |-- x -> Phi;; x |-- y -> Phi |-- y.

Context {minL: MinimunLanguage L}.

Definition DeductionMP: Prop :=
  forall (Phi: context) (x y: expr), Phi |-- x -> Phi |-- x --> y -> Phi |-- y.

Definition DeductionImpIntro: Prop :=
  forall (Phi: context) (x y: expr), Phi;; x |-- y -> Phi |-- x --> y.

Definition DeductionImpElim: Prop :=
  forall (Phi: context) (x y: expr), Phi |-- x --> y -> Phi;; x |-- y.

End PropertiesOfSequentCalculus.

Section TheoryOfSequentCalculus.

Context {L: Language}
        {Gamma: ProofTheory L}
        {minL: MinimunLanguage L}.

Lemma DerivableRefl_DeductionWeaken_2_DerivableAssu:
  DerivableRefl L Gamma ->
  DeductionWeaken L Gamma ->
  DerivableAssu L Gamma.
Proof.
  intros.
  intros ? ? ?.
  eapply H0; [| apply H].
  intros ? ?.
  destruct H2.
  + destruct H2.
  + destruct H2; auto.
Qed.

Lemma DerivableAssu_2_DerivableRefl:
  DerivableAssu L Gamma ->
  DerivableRefl L Gamma.
Proof.
  intros.
  intros ?.
  apply H.
  right.
  constructor.
Qed.

Lemma DeductionMP_DerivableAssu_DeductionWeaken_2_DeductionImpElim:
  DeductionMP L Gamma ->
  DerivableAssu L Gamma ->
  DeductionWeaken L Gamma ->
  DeductionImpElim L Gamma.
Proof.
  intros.
  intros ? ? ? ?.
  eapply H.
  + apply H0.
    right.
    constructor.
  + eapply H1; [| exact H2].
    intros ? ?.
    left.
    auto.
Qed.

Lemma DeductionImpIntro_DeductionMP_2_DeductionSubst:
  DeductionImpIntro L Gamma ->
  DeductionMP L Gamma ->
  DeductionSubst L Gamma.
Proof.
  intros.
  intros ? ? ? ? ?.
  apply H in H2.
  revert H1 H2; apply H0.
Qed.

Lemma DeductionImpElim_DeductionSubst_2_DeductionMP:
  DeductionImpElim L Gamma ->
  DeductionSubst L Gamma ->
  DeductionMP L Gamma.
Proof.
  intros.
  intros ? ? ? ? ?.
  apply H in H2.
  revert H1 H2; apply H0.
Qed.

End TheoryOfSequentCalculus.
