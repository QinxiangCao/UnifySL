Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.HenkinCompleteness.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Intuitionistic.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Classical.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Trivial.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section Lindenbaum_Trivial.

Context {L: Language}
        {nL: NormalLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {nGamma: NormalProofTheory L Gamma}
        {mpGamma: MinimunPropositionalLogic L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {cpGamma: ClassicalPropositionalLogic L Gamma}.

Hypothesis CE: Countable expr.

Lemma Lindenbaum_lemma:
  forall Phi,
    consistent Phi ->
    exists Psi,
      Included _ Phi Psi /\ maximal_consistent Psi.
Proof.
  intros.
  set (step :=
          fun n Phi x =>
             Phi x \/
            (CE x n /\ consistent (Union _ Phi (Singleton _ x)))).
  exists (LindenbaumConstruction step Phi).
  split; [| rewrite maximal_consistent_spec; split].
  + apply (Lindenbaum_spec_included _ _ 0).
  + rewrite consistent_spec.
    apply (Lindenbaum_spec_pos _ _
            (fun xs => |-- multi_imp xs FF)
            (fun Phi => Phi |-- FF)).
    - intros; apply derivable_provable.
    - intros ? ? ? ?; left; auto.
    - rewrite consistent_spec in H; apply H.
    - intros.
      destruct (Classical_Prop.classic (exists x, CE x n /\ consistent (Union _ S (Singleton _ x)))) as [[x [? ?]] |].
      * rewrite consistent_spec in H2.
        intro; apply H2; clear H2.
        eapply deduction_weaken; [| exact H3].
        hnf; intros ? [? | [? ?]]; [left; auto |].
        pose proof in_inj _ _ CE _ _ _ H1 H2.
        subst; right; constructor.
      * intro; apply H0; clear H0.
        eapply deduction_weaken; [| exact H2].
        hnf; intros ? [? | [? ?]]; [auto |].
        exfalso; apply H1; clear H1.
        exists x; auto.
  + intros.
    destruct (im_inj _ _ CE x) as [n ?].
    apply (Lindenbaum_spec_neg _ _ _ (S n)).
    simpl.
    unfold step at 1.
    rewrite consistent_spec in H0 |- *.
    right; split; auto.
    intro; apply H0; clear H0.
    rewrite deduction_theorem in H2 |- *.
    eapply deduction_weaken; [| exact H2].
    apply (Lindenbaum_spec_included _ _ n); auto.
Qed.

End Lindenbaum_Trivial.
