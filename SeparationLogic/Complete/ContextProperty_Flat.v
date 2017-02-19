Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.HenkinCompleteness.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Definition context_join {L: Language} {sL: SeparationLanguage L} {Gamma: ProofTheory L} (Phi1 Phi2 Phi: context): Prop :=
  forall x y, Phi1 |-- x -> Phi2 |-- y -> Phi |-- x * y.

Definition context_sepcon {L: Language} {sL: SeparationLanguage L} {Gamma: ProofTheory L} (Phi Psi: context): context :=
  fun z => exists x y, z = x * y /\ Phi |-- x /\ Psi |-- y.

Definition Linderbaum_sepcon_right
           {L: Language}
           {sL: SeparationLanguage L}
           {Gamma: ProofTheory L}
           (P: context -> Prop): Prop :=
  forall (Phi1 Phi2: context) (Psi: sig P),
    context_join Phi1 Phi2 (proj1_sig Psi) ->
    exists Psi2: sig P,
      Included _ Phi2 (proj1_sig Psi2) /\
      context_join Phi1 (proj1_sig Psi2) (proj1_sig Psi).

Definition Linderbaum_sepcon_left
           {L: Language}
           {sL: SeparationLanguage L}
           {Gamma: ProofTheory L}
           (P: context -> Prop): Prop :=
  forall (Phi1 Phi2: context) (Psi: sig P),
    context_join Phi1 Phi2 (proj1_sig Psi) ->
    exists Psi1: sig P,
      Included _ Phi1 (proj1_sig Psi1) /\
      context_join (proj1_sig Psi1) Phi2 (proj1_sig Psi).

Lemma context_sepcon_context_join {L: Language} {nL: NormalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma}:
  forall Phi1 Phi2,
    context_join Phi1 Phi2 (context_sepcon Phi1 Phi2).
Proof.
  intros.
  hnf; intros.
  apply derivable_assum.
  exists x, y.
  auto.
Qed.

Lemma context_sepcon_context_join' {L: Language} {nL: NormalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma}:
  forall Phi1 Phi2 Phi,
    Included _ (context_sepcon Phi1 Phi2) Phi ->
    context_join Phi1 Phi2 Phi.
Proof.
  intros.
  hnf; intros.
  apply derivable_assum, H.
  exists x, y.
  auto.
Qed.

Lemma context_sepcon_derivable {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}:
  forall (Phi Psi: context) z,
    context_sepcon Phi Psi |-- z ->
    exists x y, |-- x * y --> z /\ Phi |-- x /\ Psi |-- y.
Proof.
  intros.
  rewrite derivable_provable in H.
  destruct H as [xs [? ?]].
  revert z H0; induction H; intros.
  + exists TT, TT.
    split; [| split].
    - apply aux_minimun_rule00; auto.
    - apply derivable_impp_refl.
    - apply derivable_impp_refl.
  + pose proof provable_multi_imp_arg_switch1 l x z.
    pose proof modus_ponens _ _ H2 H1.
    specialize (IHForall _ H3); clear H1 H2 H3.
    destruct H as [x' [y' [? [? ?]]]]; subst x.
    destruct IHForall as [x [y [? [? ?]]]].
    exists (x && x'), (y && y').
    split; [| split].
    - clear l H0 H1 H2 H3 H4.
      rewrite (provable_sepcon_andp_right (x && x') y y').
      rewrite (provable_sepcon_andp_left x x' y).
      rewrite (provable_sepcon_andp_left x x' y').
      rewrite (andp_elim1 (x * y) _).
      rewrite (andp_elim2 _ (x' * y')).
      rewrite provable_derivable.
      rewrite <- deduction_theorem.
      pose proof derivable_assum1 empty_context ((x * y) && (x' * y')).
      pose proof deduction_andp_elim1 _ _ _ H0.
      pose proof deduction_andp_elim2 _ _ _ H0.
      apply (deduction_weaken0 (Union _ empty_context (Singleton _ (x * y && (x' * y'))))) in H.
      pose proof deduction_modus_ponens _ _ _ H1 H.
      pose proof deduction_modus_ponens _ _ _ H2 H3.
      auto.
    - apply deduction_andp_intros; auto.
    - apply deduction_andp_intros; auto.
Qed.

Lemma wand_deduction_theorem {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}:
  forall (Phi: context) x y,
    context_sepcon Phi (Union _ empty_context (Singleton _ x)) |-- y <->
    Phi |-- x -* y.
Proof.
  intros.
  split; intros.
  + apply context_sepcon_derivable in H.
    destruct H as [x' [y' [? [? ?]]]].
    rewrite deduction_theorem, <- provable_derivable in H1.
    rewrite <- H1 in H.
    apply wand_sepcon_adjoint in H.
    rewrite H in H0; auto.
  + rewrite <- (provable_wand_sepcon_modus_ponens1 x y).
    apply derivable_assum.
    exists (x -* y), x.
    split; [| split]; auto.
    rewrite deduction_theorem.
    apply derivable_impp_refl.
Qed.

