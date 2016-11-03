Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.
Require Import Logic.HenkinCompleteness.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.MinimunPropositionalLogic.
Require Import Logic.PropositionalLogic.ClassicalPropositionalLogic.
Require Import Logic.PropositionalLogic.TrivialSemantics.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Definition MCS (Var: Type): Type := sig (maximal_consistent (ClassicalPropositionalLogic.G Var)).

Definition canonical_model {Var: Type} (Phi: MCS Var): @model _ (TrivialSemantics.SM Var) :=
  fun p => (proj1_sig Phi (PropositionalLanguage.varp p)).

Lemma truth_lemma {Var: Type}: forall (Phi: MCS Var) x, canonical_model Phi |= x <-> proj1_sig Phi x.
Proof.
  intros.
  revert x.
  pose proof @MCS_element_derivable _ _ _ _ _ _ (ClassicalPropositionalLogic.cpG Var) (proj1_sig Phi) (proj2_sig Phi).
  pose proof @TrivialSemantics.mendelson_consistent Var.
  pose proof @classic_mendelson_consistent _ _ _ _  _ _ (ClassicalPropositionalLogic.cpG Var).
  apply (@truth_lemma_from_syntactic_reduction  _ _ (PropositionalLanguage.nMendelsonReduction) _ _ H1 H0 _ _ H).
  intros.
  clear H0 H1.
  induction x; try solve [inversion H2].
  + destruct H2.
    specialize (IHx1 H0).
    specialize (IHx2 H1).
    pose proof @MCS_impp_iff _ _ _ _ _ _ (ClassicalPropositionalLogic.cpG Var) (proj1_sig Phi) (proj2_sig Phi) x1 x2.
    simpl in *.
    unfold TrivialSemantics.sem_imp.
    tauto.
  + specialize (IHx H2).
    pose proof @MCS_negp_iff _ _ _ _ _ _ (ClassicalPropositionalLogic.cpG Var) (proj1_sig Phi) (proj2_sig Phi) x.
    simpl in *.
    unfold TrivialSemantics.sem_neg.
    tauto.
  + simpl.
    rewrite H.
    split; auto; intros _.
    rewrite derivable_provable; exists nil.
    split; auto.
    apply (ClassicalPropositionalLogic.true_provable).
  + simpl.
    unfold canonical_model.
    tauto.
Qed.

Theorem complete_classical_trivial (Var: Type): strongly_complete (ClassicalPropositionalLogic.G Var) (TrivialSemantics.SM Var).
Proof.
  assert (forall Phi, consistent (ClassicalPropositionalLogic.G Var) Phi -> satisfiable Phi).
  + intros.
    assert (exists Psi, Included _ Phi Psi /\ maximal_consistent (ClassicalPropositionalLogic.G Var) Psi).
    admit. (* Use linderbum to construct MCS *)
    destruct H0 as [Psi [? ?]].
    exists (canonical_model (exist _ Psi H1)).
    intros.
    apply truth_lemma.
    simpl.
    apply H0; auto.
  + hnf; intros.
    specialize (H (Union _ Phi (Singleton _ (~~ x)))).
    unfold consistent in H.
    apply Classical_Prop.NNPP.
    intro.
    assert (satisfiable (Union expr Phi (Singleton expr (~~ x)))).
    Focus 1. {
      apply H.
      intro; apply H1.
      rewrite (@deduction_theorem _ _ _ _ _ (ClassicalPropositionalLogic.mpG Var)) in H2.
      clear - H2.
      apply (@aux_classic_theorem05 _ _ _ _ _ _ (ClassicalPropositionalLogic.cpG Var)); auto.
    } Unfocus.
    destruct H2 as [m ?].
    specialize (H0 m).
    pose proof (H2 (~~ x) (Union_intror _ _ _ _ (In_singleton _ _))).
    pose proof (fun x H => H2 x (Union_introl _ _ _ _ H)).
    specialize (H0 H4).
    clear - H0 H3.
    simpl in *; auto.
Qed.

