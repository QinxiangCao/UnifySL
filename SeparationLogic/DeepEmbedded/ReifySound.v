Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.WeakClassical.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.DeepEmbedded.Parameter.
Require Logic.SeparationLogic.DeepEmbedded.SeparationEmpLanguage.
Require Logic.SeparationLogic.DeepEmbedded.ParametricSeparationLogic.
Require Import Logic.SeparationLogic.DeepEmbedded.Reify.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Theorem reification_sound (PAR: SL_Parameter) {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {ParGamma: ParametricSeparationLogic.Parametric_SeparationLogic PAR L Gamma}:
  forall (tbl: list expr) (x: @SeparationEmpLanguage.expr nat),
    ParametricSeparationLogic.provable nat PAR x ->
    |-- reflect L tbl x.
Proof.
  intros.
  destruct ParGamma.
  induction H.
  + simpl; apply (modus_ponens (reflect L tbl x) (reflect L tbl y)); auto.
  + exact (axiom1 (reflect L tbl x) (reflect L tbl y)).
  + exact (axiom2 (reflect L tbl x) (reflect L tbl y) (reflect L tbl z)).
  + exact (andp_intros (reflect L tbl x) (reflect L tbl y)).
  + exact (andp_elim1 (reflect L tbl x) (reflect L tbl y)).
  + exact (andp_elim2 (reflect L tbl x) (reflect L tbl y)).
  + exact (orp_intros1 (reflect L tbl x) (reflect L tbl y)).
  + exact (orp_intros2 (reflect L tbl x) (reflect L tbl y)).
  + exact (orp_elim (reflect L tbl x) (reflect L tbl y) (reflect L tbl z)).
  + exact (falsep_elim (reflect L tbl x)).
  + specialize (Parametric_WC H). exact (weak_excluded_middle (reflect L tbl x)).
  + specialize (Parametric_GD H). exact (impp_choice (reflect L tbl x) (reflect L tbl y)).
  + specialize (Parametric_C H). exact (excluded_middle (reflect L tbl x)).
  + exact (sepcon_comm (reflect L tbl x) (reflect L tbl y)).
  + exact (sepcon_assoc (reflect L tbl x) (reflect L tbl y) (reflect L tbl z)).
  + simpl; apply (wand_sepcon_adjoint (reflect L tbl x) (reflect L tbl y) (reflect L tbl z)); auto.
  + simpl; apply (wand_sepcon_adjoint (reflect L tbl x) (reflect L tbl y) (reflect L tbl z)); auto.
  + simpl; apply (sepcon_mono (reflect L tbl x1) (reflect L tbl x2) (reflect L tbl y1) (reflect L tbl y2)); auto.
  + specialize (Parametric_GC H). exact (sepcon_elim1 (reflect L tbl x) (reflect L tbl y)).
  + specialize (Parametric_EMP H). exact (sepcon_emp (reflect L tbl x)).
  + specialize (Parametric_EXT H). exact (sepcon_ext (reflect L tbl x)).
Qed.
