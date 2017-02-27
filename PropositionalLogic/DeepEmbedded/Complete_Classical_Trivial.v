Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Intuitionistic.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Classical.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Trivial.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Trivial.
Require Import Logic.PropositionalLogic.Complete.Truth_Trivial.
Require Import Logic.PropositionalLogic.Complete.Complete_Trivial.
Require Logic.PropositionalLogic.DeepEmbedded.PropositionalLanguage.
Require Logic.PropositionalLogic.DeepEmbedded.IntuitionisticLogic.
Require Logic.PropositionalLogic.DeepEmbedded.DeMorganLogic.
Require Logic.PropositionalLogic.DeepEmbedded.GodelDummettLogic.
Require Logic.PropositionalLogic.DeepEmbedded.ClassicalLogic.
Require Logic.PropositionalLogic.DeepEmbedded.TrivialSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Local Open Scope kripke_model_class.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.

Section Complete.

Context (Var: Type) (CV: Countable Var).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.

Instance Classical_G: ProofTheory L := ClassicalLogic.G Var.
Instance Trivial_MD: Model := TrivialSemantics.MD Var.
Instance Trivial_SM: Semantics L Trivial_MD := TrivialSemantics.SM Var.

Section General_Completeness.

Context {Gamma: ProofTheory L}
        {nGamma: NormalProofTheory L Gamma}
        {mpGamma: MinimunPropositionalLogic L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {cpGamma: ClassicalPropositionalLogic L Gamma}.

Lemma MC: at_least_maximal_consistent maximal_consistent.
Proof. hnf; intros; auto. Qed.

Lemma LIN_CONSI: Linderbaum_consistent maximal_consistent.
Proof.
  hnf; intros.
  pose proof Lindenbaum_lemma
    (PropositionalLanguage.formula_countable Var CV) _ H
  as [Psi [? ?]].
  exists (exist _ Psi H1); auto.
Qed.

Definition canonical_frame: Type := sig maximal_consistent.

Definition canonical_eval: Var -> canonical_frame -> Prop :=
  fun p a => proj1_sig a (PropositionalLanguage.varp p).

Definition kMD: KripkeModel (TrivialSemantics.MD Var) :=
  Build_KripkeModel (TrivialSemantics.MD Var)
    unit (fun _ => canonical_frame) (fun u a v => canonical_eval v a).

Definition canonical_Kmodel: @Kmodel (TrivialSemantics.MD Var) kMD := tt.

Definition rel: bijection (Kworlds canonical_Kmodel) (sig maximal_consistent) := bijection_refl.

Lemma TRUTH:
  forall x: expr, forall m Phi, rel m Phi ->
    (KRIPKE: canonical_Kmodel, m |= x <-> proj1_sig Phi x).
Proof.
  induction x.
  + exact (truth_lemma_andp maximal_consistent rel MC x1 x2 IHx1 IHx2).
  + exact (truth_lemma_orp maximal_consistent rel MC x1 x2 IHx1 IHx2).
  + exact (truth_lemma_impp maximal_consistent rel MC x1 x2 IHx1 IHx2).
  + exact (truth_lemma_falsep maximal_consistent rel MC).
  + intros; change (m = Phi) in H; subst; reflexivity.
Qed.

End General_Completeness.

Section Classical_Completeness.

Instance Classical_nG: NormalProofTheory L Classical_G := ClassicalLogic.nG Var.
Instance Classical_mpG: MinimunPropositionalLogic L Classical_G := ClassicalLogic.mpG Var.
Instance Classical_ipG: IntuitionisticPropositionalLogic L Classical_G := ClassicalLogic.ipG Var.
Instance Classical_cpG: ClassicalPropositionalLogic L Classical_G := ClassicalLogic.cpG Var.

Existing Instance kMD.

Theorem complete_Classical_Trivial:
  strongly_complete Classical_G Trivial_SM (AllModel _).
Proof.
  assert (strongly_complete Classical_G Trivial_SM
           (KripkeModelClass _ (fun _ => True))).
  Focus 2. {
    hnf; intros.
    apply (H Phi x).
    hnf; intros.
    apply H0; auto.
    hnf; auto.
  } Unfocus.
  apply (@general_completeness L _ _ Classical_G _ _ _ _
           _ _ _ Trivial_SM _ _ maximal_consistent rel LIN_CONSI TRUTH); auto.
Qed.

End Classical_Completeness.

End Complete.
