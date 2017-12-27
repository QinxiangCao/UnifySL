Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun2.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Section DerivableRulesFromPatterns.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {prodp: expr -> expr -> expr}
        {e: expr}
        {Mono: Monotonicity L Gamma prodp}
        {Assoc: Associativity L Gamma prodp}
        {LU: LeftUnit L Gamma e prodp}
        {RU: RightUnit L Gamma e prodp}.

Lemma assoc_fold_left_fold_right_equiv: forall xs,
  |-- fold_left prodp xs e <--> fold_right prodp e xs.
Proof.
  intros.
  apply solve_andp_intros.
  + apply assoc_fold_left_fold_right.
  + apply assoc_fold_right_fold_left.
Qed.

End DerivableRulesFromPatterns.

Section ProofTheoryPatterns.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}.

Lemma Build_LeftUnit': forall {e: expr} {prodp: expr -> expr -> expr},
  (forall x: expr, |-- prodp e x <--> x) ->
  LeftUnit L Gamma e prodp.
Proof.
  intros.
  constructor; intros; specialize (H x); revert H; AddSequentCalculus Gamma.
  + rewrite !provable_derivable.
    intros.
    eapply deduction_andp_elim1; eauto.
  + rewrite !provable_derivable.
    intros.
    eapply deduction_andp_elim2; eauto.
Qed.

Lemma Build_RightUnit': forall {e: expr} {prodp: expr -> expr -> expr},
  (forall x: expr, |-- prodp x e <--> x) ->
  RightUnit L Gamma e prodp.
Proof.
  intros.
  constructor; intros; specialize (H x); revert H; AddSequentCalculus Gamma.
  + rewrite !provable_derivable.
    intros.
    eapply deduction_andp_elim1; eauto.
  + rewrite !provable_derivable.
    intros.
    eapply deduction_andp_elim2; eauto.
Qed.

Lemma Build_Associativity': forall {prodp: expr -> expr -> expr},
  (forall x y z: expr, |-- prodp (prodp x y) z <--> prodp x (prodp y z)) ->
  Associativity L Gamma prodp.
Proof.
  intros.
  constructor; intros; specialize (H x y z); revert H; AddSequentCalculus Gamma.
  + rewrite !provable_derivable.
    intros.
    eapply deduction_andp_elim2; eauto.
  + rewrite !provable_derivable.
    intros.
    eapply deduction_andp_elim1; eauto.
Qed.

End ProofTheoryPatterns.

Section PatternInstances.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}.

Lemma impp_andp_Adjoint: Adjointness L Gamma andp impp.
Proof.
  constructor; AddSequentCalculus Gamma.
  intros; split; intros.
  + eapply modus_ponens; [| exact H].
    apply impp_uncurry.
  + eapply modus_ponens; [| exact H].
    apply impp_curry.
Qed.

Lemma andp_Comm: Commutativity L Gamma andp.
Proof.
  constructor.
  AddSequentCalculus Gamma.
  intros.
  rewrite provable_derivable.
  eapply deduction_andp_elim1.
  rewrite <- provable_derivable.
  apply andp_comm.
Qed.

Lemma andp_Mono: Monotonicity L Gamma andp.
Proof.
  eapply @Adjoint2Mono.
  + auto.
  + apply impp_andp_Adjoint.
  + apply andp_Comm.
Qed.

Lemma andp_LU: LeftUnit L Gamma TT andp.
Proof.
  intros.
  apply Build_LeftUnit'.
  intros.
  apply truep_andp.
Qed.

Lemma andp_RU: RightUnit L Gamma TT andp.
Proof.
  intros.
  apply Build_RightUnit'.
  intros.
  apply andp_truep.
Qed.

Lemma andp_Assoc: Associativity L Gamma andp.
Proof.
  intros.
  apply Build_Associativity'.
  intros.
  apply andp_assoc.
Qed.

End PatternInstances.

Section DerivableRules.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}.

Definition multi_and (xs: list expr): expr := fold_left andp xs truep.

Lemma multi_and_spec: forall (xs: list expr),
  |-- multi_and xs <--> fold_right andp TT xs.
Proof.
  intros.
  unfold multi_and.
  pose proof @assoc_fold_left_fold_right_equiv _ _ _ _ _ _ andp TT andp_Mono andp_Assoc andp_LU andp_RU.
  auto.
Qed.

Lemma multi_and_multi_imp: forall (xs: list expr) (y: expr),
  |-- (multi_and xs --> y) <--> (multi_imp xs y).
Proof.
  intros.
  unfold multi_imp.
  rewrite multi_and_spec.
  induction xs as [| x xs].
  + simpl.
    apply truep_impp.
  + simpl.
    rewrite <- impp_curry_uncurry.
    apply impp_proper_iffp; [apply provable_iffp_refl |].
    auto.
Qed.

End DerivableRules.