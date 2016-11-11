Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.MinimunLogic.SyntacticReduction.
Require Import Logic.MinimunLogic.ContextProperty.
Require Import Logic.MinimunLogic.HenkinCompleteness.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ClassicalPropositionalLogic.
Require Import Logic.PropositionalLogic.TrivialSemantics.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Section Completeness.

Context (Var: Type).
Context (CV: Countable Var).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.
Instance R: SyntacticReduction L := MendelsonReduction.
Instance nR: NormalSyntacticReduction L R := PropositionalLanguage.nMendelsonReduction.
Instance G: ProofTheory L := ClassicalPropositionalLogic.G Var.
Instance nG: NormalProofTheory L G := ClassicalPropositionalLogic.nG Var.
Instance mpG: MinimunPropositionalLogic L G := ClassicalPropositionalLogic.mpG Var.
Instance rcG: ReductionConsistentProofTheory MendelsonReduction G := ClassicalPropositionalLogic.rcG Var.
Instance cpG: ClassicalPropositionalLogic L G := ClassicalPropositionalLogic.cpG Var.
Instance SM: Semantics L := TrivialSemantics.SM Var.
Instance rcSM: ReductionConsistentSemantics MendelsonReduction SM := TrivialSemantics.rcSM Var.

Definition MCS: Type := sig maximal_consistent.

Definition canonical_model (Phi: MCS): model :=
  fun p => (proj1_sig Phi (PropositionalLanguage.varp p)).

Lemma Lindenbaum_lemma:
  forall Phi,
    consistent Phi ->
    exists Psi,
      Included _ Phi Psi /\ maximal_consistent Psi.
Proof.
  intros.
  assert (Countable expr) by (apply PropositionalLanguage.formula_countable; auto).
  set (step :=
          fun n Phi x =>
             Phi x \/
            (inj_R _ _ X x n /\ consistent (Union _ Phi (Singleton _ x)))).
  exists (LindenbaumConstruction step Phi).
  split; [| rewrite maximal_consistent_spec; split].
  + apply (Lindenbaum_spec_included _ _ 0).
  + unfold consistent.
    apply (Lindenbaum_spec_pos _ _
            (fun xs => |-- multi_imp xs FF)
            (fun Phi => Phi |-- FF)).
    - intros; apply derivable_provable.
    - intros ? ? ? ?; left; auto.
    - apply H.
    - intros.
      destruct (Classical_Prop.classic (exists x, inj_R _ _ X x n /\ consistent (Union _ S (Singleton _ x)))) as [[x [? ?]] |].
      * intro; apply H2; clear H2.
        eapply derivable_weaken; [| exact H3].
        hnf; intros ? [? | [? ?]]; [left; auto |].
        pose proof in_inj _ _ X _ _ _ H1 H2.
        subst; right; constructor.
      * intro; apply H0; clear H0.
        eapply derivable_weaken; [| exact H2].
        hnf; intros ? [? | [? ?]]; [auto |].
        exfalso; apply H1; clear H1.
        exists x; auto.
  + intros.
    destruct (im_inj _ _ X x) as [n ?].
    apply (Lindenbaum_spec_neg _ _ _ (S n)).
    simpl.
    unfold step at 1.
    unfold consistent.
    right; split; auto.
    intro; apply H0; clear H0.
    rewrite deduction_theorem in H2 |- *.
    eapply derivable_weaken; [| exact H2].
    apply (Lindenbaum_spec_included _ _ n); auto.
Qed.

Lemma truth_lemma: forall (Phi: MCS) x, canonical_model Phi |= x <-> proj1_sig Phi x.
Proof.
  intros.
  revert x.
  pose proof MCS_element_derivable (proj1_sig Phi) (proj2_sig Phi).
  apply (truth_lemma_from_syntactic_reduction _ _ _ _ _ H).
  intros.
  induction x; try solve [inversion H0].
  + destruct H0.
    specialize (IHx1 H0).
    specialize (IHx2 H1).
    pose proof MCS_impp_iff (proj1_sig Phi) (proj2_sig Phi) x1 x2.
    simpl in *.
    unfold TrivialSemantics.sem_imp.
    tauto.
  + specialize (IHx H0).
    pose proof MCS_negp_iff (proj1_sig Phi) (proj2_sig Phi) x.
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

Theorem complete_classical_trivial: strongly_complete (ClassicalPropositionalLogic.G Var) (TrivialSemantics.SM Var).
Proof.
  assert (forall Phi, consistent Phi -> satisfiable Phi).
  + intros.
    assert (exists Psi, Included _ Phi Psi /\ maximal_consistent Psi)
      by (apply Lindenbaum_lemma; auto).
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
      rewrite deduction_theorem in H2.
      clear - H2.
      apply aux_classic_theorem05; auto.
    } Unfocus.
    destruct H2 as [m ?].
    specialize (H0 m).
    pose proof (H2 (~~ x) (Union_intror _ _ _ _ (In_singleton _ _))).
    pose proof (fun x H => H2 x (Union_introl _ _ _ _ H)).
    specialize (H0 H4).
    clear - H0 H3.
    simpl in *; auto.
Qed.

End Completeness.
