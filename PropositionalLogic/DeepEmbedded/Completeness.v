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
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Complete.Truth_Kripke.
Require Import Logic.PropositionalLogic.Complete.Canonical_Kripke.
Require Import Logic.PropositionalLogic.Complete.Complete_Kripke.
Require Logic.PropositionalLogic.DeepEmbedded.PropositionalLanguage.
Require Logic.PropositionalLogic.DeepEmbedded.IntuitionisticLogic.
Require Logic.PropositionalLogic.DeepEmbedded.DeMorganLogic.
Require Logic.PropositionalLogic.DeepEmbedded.GodelDummettLogic.
Require Logic.PropositionalLogic.DeepEmbedded.ClassicalLogic.
Require Logic.PropositionalLogic.DeepEmbedded.TrivialSemantics.
Require Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.

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

Instance Intuitionistic_G: ProofTheory L := IntuitionisticLogic.G Var.
Instance DeMorgan_G: ProofTheory L := DeMorganLogic.G Var.
Instance GodelDummett_G: ProofTheory L := GodelDummettLogic.G Var.
Instance Classical_G: ProofTheory L := ClassicalLogic.G Var.
Instance Trivial_MD: Model := TrivialSemantics.MD Var.
Instance Trivial_SM: Semantics L Trivial_MD := TrivialSemantics.SM Var.
Instance Kripke_MD: Model := KripkeSemantics.MD Var.
Instance Kripke_kMD: KripkeModel Kripke_MD := KripkeSemantics.kMD Var.
Instance Kripke_R (M: Kmodel): Relation (Kworlds M) := KripkeSemantics.R Var M.
Instance Kripke_SM: Semantics L Kripke_MD := KripkeSemantics.SM Var.
Instance Kripke_kpSM (M: Kmodel): KripkePropositionalSemantics L Kripke_MD M Kripke_SM := KripkeSemantics.kpSM Var M.

Section Complete_Kripke.

Section General_Completeness.

Context {Gamma: ProofTheory L}
        {nGamma: NormalProofTheory L Gamma}
        {mpGamma: MinimunPropositionalLogic L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}.

Definition DDC: context -> Prop := fun Psi =>
  derivable_closed Psi /\ orp_witnessed Psi /\ consistent Psi.

Lemma DER: at_least_derivable_closed DDC.
Proof. hnf; intros ? [? [? ?]]; auto. Qed.

Lemma ORP: at_least_orp_witnessed DDC.
Proof. hnf; intros ? [? [? ?]]; auto. Qed.

Lemma CONSI: at_least_consistent DDC.
Proof. hnf; intros ? [? [? ?]]; auto. Qed.

Lemma LIN_DER: Linderbaum_derivable DDC.
Proof.
  hnf; intros.
  pose proof Lindenbaum_lemma
    (PropositionalLanguage.formula_countable Var CV)  _ _ H
  as [Psi [? [? ?]]].
  exists (exist _ Psi H2); auto.
Qed.

Definition canonical_frame: KripkeSemantics.frame :=
  KripkeSemantics.Build_frame (sig DDC) (fun a b => Included _ (proj1_sig a) (proj1_sig b)).

Definition canonical_eval: Var -> KripkeSemantics.sem canonical_frame :=
  fun p a => proj1_sig a (PropositionalLanguage.varp p).

Definition canonical_Kmodel: @Kmodel (KripkeSemantics.MD Var) (KripkeSemantics.kMD Var) :=
  KripkeSemantics.Build_Kmodel Var canonical_frame canonical_eval.

Definition rel: bijection (Kworlds canonical_Kmodel) (sig DDC) := bijection_refl.

Definition H_R:
  forall m n Phi Psi, rel m Phi -> rel n Psi ->
    (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).
Proof.
  intros.
  change (m = Phi) in H.
  change (n = Psi) in H0.
  subst; reflexivity.
Qed.

Lemma TRUTH:
  forall x: expr, forall m Phi, rel m Phi ->
    (KRIPKE: canonical_Kmodel, m |= x <-> proj1_sig Phi x).
Proof.
  induction x.
  + exact (truth_lemma_andp DDC rel DER x1 x2 IHx1 IHx2).
  + exact (truth_lemma_orp DDC rel DER ORP x1 x2 IHx1 IHx2).
  + exact (truth_lemma_impp DDC rel H_R DER LIN_DER x1 x2 IHx1 IHx2).
  + exact (truth_lemma_falsep DDC rel CONSI).
  + intros; change (m = Phi) in H; subst; reflexivity.
Qed.

End General_Completeness.

Section Intuitionistic_Completeness.

Instance Intuitionistic_nG: NormalProofTheory L Intuitionistic_G := IntuitionisticLogic.nG Var.
Instance Intuitionistic_mpG: MinimunPropositionalLogic L Intuitionistic_G := IntuitionisticLogic.mpG Var.
Instance Intuitionistic_ipG: IntuitionisticPropositionalLogic L Intuitionistic_G := IntuitionisticLogic.ipG Var.

Import Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.

Theorem complete_intuitionistic_Kripke_all:
  strongly_complete Intuitionistic_G Kripke_SM
    (KripkeModelClass _ (Kmodel_Monotonic + Kmodel_PreOrder)).
Proof.
  apply (@general_completeness _ _ _ _ _ _ _ _ _ _ DDC rel LIN_DER DER TRUTH).
  constructor; hnf.
  + intros.
    exact (denote_monotonic DDC rel H_R
             (PropositionalLanguage.varp v)
             (TRUTH (PropositionalLanguage.varp v))).
  + exact (po_R DDC rel H_R).
Qed.

End Intuitionistic_Completeness.
  
Section DeMorgan_Completeness.

Instance DeMorgan_nG: NormalProofTheory L DeMorgan_G := DeMorganLogic.nG Var.
Instance DeMorgan_mpG: MinimunPropositionalLogic L DeMorgan_G := DeMorganLogic.mpG Var.
Instance DeMorgan_ipG: IntuitionisticPropositionalLogic L DeMorgan_G := DeMorganLogic.ipG Var.
Instance DeMorgan_dmpG: DeMorganPropositionalLogic L DeMorgan_G := DeMorganLogic.dmpG Var.

Import Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.

Theorem complete_DeMorgan_Kripke_branch_join:
  strongly_complete DeMorgan_G Kripke_SM
    (KripkeModelClass _ (Kmodel_Monotonic + Kmodel_PreOrder + Kmodel_BranchJoin)).
Proof.
  apply (@general_completeness _ _ _ _ _ _ _ _ _ _ DDC rel LIN_DER DER TRUTH).
  constructor; [split |]; hnf.
  + intros.
    exact (denote_monotonic DDC rel H_R
             (PropositionalLanguage.varp v)
             (TRUTH (PropositionalLanguage.varp v))).
  + exact (po_R DDC rel H_R).
  + exact (DeMorgan_canonical_branch_join DDC rel H_R DER ORP CONSI LIN_DER).
Qed.

End DeMorgan_Completeness.

Section GodelDummett_Completeness.

Instance GodelDummett_nG: NormalProofTheory L GodelDummett_G := GodelDummettLogic.nG Var.
Instance GodelDummett_mpG: MinimunPropositionalLogic L GodelDummett_G := GodelDummettLogic.mpG Var.
Instance GodelDummett_ipG: IntuitionisticPropositionalLogic L GodelDummett_G := GodelDummettLogic.ipG Var.
Instance GodelDummett_gdpG: GodelDummettPropositionalLogic L GodelDummett_G := GodelDummettLogic.gdpG Var.

Import Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.

Theorem complete_GodelDummett_Kripke_no_branch:
  strongly_complete GodelDummett_G Kripke_SM
    (KripkeModelClass _ (Kmodel_Monotonic + Kmodel_PreOrder + Kmodel_NoBranch)).
Proof.
  apply (@general_completeness _ _ _ _ _ _ _ _ _ _ DDC rel LIN_DER DER TRUTH).
  constructor; [split |]; hnf.
  + intros.
    exact (denote_monotonic DDC rel H_R
             (PropositionalLanguage.varp v)
             (TRUTH (PropositionalLanguage.varp v))).
  + exact (po_R DDC rel H_R).
  + exact (GodelDummett_canonical_no_branch DDC rel H_R DER ORP).
Qed.

End GodelDummett_Completeness.

Section Classical_Completeness.

Instance Classical_nG: NormalProofTheory L Classical_G := ClassicalLogic.nG Var.
Instance Classical_mpG: MinimunPropositionalLogic L Classical_G := ClassicalLogic.mpG Var.
Instance Classical_ipG: IntuitionisticPropositionalLogic L Classical_G := ClassicalLogic.ipG Var.
Instance Classical_cpG: ClassicalPropositionalLogic L Classical_G := ClassicalLogic.cpG Var.

Import Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.

Theorem complete_Classical_Kripke_identity:
  strongly_complete Classical_G Kripke_SM
    (KripkeModelClass _ (Kmodel_Monotonic + Kmodel_PreOrder + Kmodel_Identity)).
Proof.
  apply (@general_completeness _ _ _ _ _ _ _ _ _ _ DDC rel LIN_DER DER TRUTH).
  constructor; [split |]; hnf.
  + intros.
    exact (denote_monotonic DDC rel H_R
             (PropositionalLanguage.varp v)
             (TRUTH (PropositionalLanguage.varp v))).
  + exact (po_R DDC rel H_R).
  + exact (classical_canonical_ident DDC rel H_R DER ORP CONSI).
Qed.

End Classical_Completeness.

End Complete_Kripke.

End Complete.
