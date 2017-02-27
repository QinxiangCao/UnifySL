Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Intuitionistic.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Complete.Truth_Kripke.
Require Import Logic.PropositionalLogic.Complete.Canonical_Kripke.
Require Import Logic.PropositionalLogic.Complete.Complete_Kripke.
Require Import Logic.SeparationLogic.Complete.ContextProperty_Flat.
Require Import Logic.SeparationLogic.Complete.Lindenbaum_Flat.
Require Import Logic.SeparationLogic.Complete.Truth_Flat.
Require Import Logic.SeparationLogic.Complete.Canonical_Flat.
Require Import Logic.SeparationLogic.DeepEmbedded.Parameter.
Require Logic.SeparationLogic.DeepEmbedded.SeparationEmpLanguage.
Require Logic.SeparationLogic.DeepEmbedded.FlatSemantics.
Require Logic.SeparationLogic.DeepEmbedded.ParametricSeparationLogic.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Local Open Scope kripke_model_class.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.

Section Complete.

Context (Var: Type).
Context (CV: Countable Var).
Context (SLP: SL_Parameter).

Instance L: Language := SeparationEmpLanguage.L Var.
Instance nL: NormalLanguage L := SeparationEmpLanguage.nL Var.
Instance pL: PropositionalLanguage L := SeparationEmpLanguage.pL Var.
Instance sL: SeparationLanguage L := SeparationEmpLanguage.sL Var.
Instance s'L: SeparationEmpLanguage L := SeparationEmpLanguage.s'L Var.

Instance G: ProofTheory L := ParametricSeparationLogic.G Var SLP.
Instance nG: NormalProofTheory L G := ParametricSeparationLogic.nG Var SLP.
Instance mpG: MinimunPropositionalLogic L G := ParametricSeparationLogic.mpG Var SLP.
Instance ipG: IntuitionisticPropositionalLogic L G := ParametricSeparationLogic.ipG Var SLP.
Instance sG: SeparationLogic L G := ParametricSeparationLogic.sG Var SLP.
Instance eG: EmpSeparationLogic L G := ParametricSeparationLogic.eG Var SLP.
Instance ParG: ParametricSeparationLogic.Parametric_SeparationLogic SLP L G := ParametricSeparationLogic.ParG Var SLP.

Instance MD: Model := FlatSemantics.MD Var.
Instance kMD: KripkeModel MD := FlatSemantics.kMD Var.
Instance R (M: Kmodel): Relation (Kworlds M):= FlatSemantics.R Var M.
Instance J (M: Kmodel): Join (Kworlds M):= FlatSemantics.J Var M.

Instance SM: Semantics L MD := FlatSemantics.SM Var.
Instance kpSM (M: Kmodel): KripkePropositionalSemantics L MD M SM := FlatSemantics.kpSM Var M.
Instance fsSM (M: Kmodel): FlatSemantics.SeparatingSemantics L MD M SM := FlatSemantics.fsSM Var M.
Instance feSM (M: Kmodel): FlatSemantics.EmpSemantics L MD M SM := FlatSemantics.feSM Var M.

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
    (SeparationEmpLanguage.formula_countable Var CV) _ _ H
  as [Psi [? [? ?]]].
  exists (exist _ Psi H2); auto.
Qed.

Lemma LIN_SR: Linderbaum_sepcon_right DDC.
Proof.
  hnf; intros.
  pose proof Lindenbaum_lemma_right
    (SeparationEmpLanguage.formula_countable Var CV) _ _  _ H (proj2_sig Psi)
  as [Psi2 [? [? ?]]].
  exists (exist _ Psi2 H2); auto.
Qed.

Lemma LIN_SL: Linderbaum_sepcon_left DDC.
Proof. rewrite Linderbaum_sepcon_equiv. apply LIN_SR. Qed.

Definition canonical_frame: FlatSemantics.frame :=
  FlatSemantics.Build_frame (sig DDC)
    (fun a b => Included _ (proj1_sig a) (proj1_sig b))
    (fun a b c => context_join (proj1_sig a) (proj1_sig b) (proj1_sig c)).

Definition canonical_eval: Var -> FlatSemantics.sem canonical_frame :=
  fun p a => proj1_sig a (SeparationEmpLanguage.varp p).

Definition canonical_Kmodel: @Kmodel (FlatSemantics.MD Var) (FlatSemantics.kMD Var) :=
  FlatSemantics.Build_Kmodel Var canonical_frame canonical_eval.

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

Definition H_J:
  forall m1 m2 m Phi1 Phi2 Phi, rel m1 Phi1 -> rel m2 Phi2 -> rel m Phi ->
    (join m1 m2 m <-> context_join (proj1_sig Phi1) (proj1_sig Phi2) (proj1_sig Phi)).
Proof.
  intros.
  change (m = Phi) in H1.
  change (m1 = Phi1) in H.
  change (m2 = Phi2) in H0.
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
  + exact (truth_lemma_sepcon DDC rel H_J DER LIN_SL LIN_SR x1 x2 IHx1 IHx2).
  + exact (truth_lemma_wand DDC rel H_J DER LIN_DER LIN_SR x1 x2 IHx1 IHx2).
  + exact (truth_lemma_emp DDC rel H_R H_J DER LIN_DER LIN_SR).
  + exact (truth_lemma_falsep DDC rel CONSI).
  + intros; change (m = Phi) in H; subst; reflexivity.
Qed.

Context (SAP: SA_Parameter).

Hypothesis PC: Parameter_coincide SLP SAP.

Theorem ParametricCompleteness:
  strongly_complete G SM
    (KripkeModelClass _
      (FlatSemantics.Kmodel_Monotonic +
       FlatSemantics.Kmodel_PreOrder +
       FlatSemantics.Kmodel_SeparationAlgebra +
       FlatSemantics.Kmodel_UpwardsClosed +
       FlatSemantics.Kmodel_DownwardsClosed +
       FlatSemantics.Kmodel_Unital +
       FlatSemantics.Parametric_Kmodel_Class SAP)).
Proof.
  apply (@general_completeness _ _ _ _ _ _ _ _ _ _ DDC rel LIN_DER DER TRUTH).
  split; [split; [split; [split; [split; [split |] |] |] |] |].
  + hnf; intros.
    exact (denote_monotonic DDC rel H_R
             (SeparationEmpLanguage.varp v)
             (TRUTH (SeparationEmpLanguage.varp v))).
  + exact (po_R DDC rel H_R).
  + exact (SA DDC rel H_J LIN_SR).
  + exact (uSA DDC rel H_R H_J DER).
  + exact (dSA DDC rel H_R H_J DER).
  + exact (unitSA DDC rel H_R H_J DER LIN_SR TRUTH).
  + inversion PC.
    constructor; intros HH; rewrite HH in *.
    - pose proof ParametricSeparationLogic.Parametric_C H.
      exact (classical_canonical_ident DDC rel H_R DER ORP CONSI).
    - pose proof ParametricSeparationLogic.Parametric_GD H0.
      exact (GodelDummett_canonical_no_branch DDC rel H_R DER ORP).
    - pose proof ParametricSeparationLogic.Parametric_DM H1.
      exact (DeMorgan_canonical_branch_join DDC rel H_R DER ORP CONSI LIN_DER).
    - pose proof ParametricSeparationLogic.Parametric_GC H2.
      exact (garbage_collected_canonical_increaing DDC rel H_R H_J DER).
    - pose proof ParametricSeparationLogic.Parametric_NE H3.
      exact (nonsplit_canonical_split_smaller DDC rel H_R H_J DER TRUTH).
    - pose proof ParametricSeparationLogic.Parametric_ED H4.
      exact (dup_canonical_incr_join DDC rel H_J DER TRUTH).
Qed.

End Complete.
