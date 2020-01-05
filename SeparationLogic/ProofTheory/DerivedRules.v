Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Section DerivedRules.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipAX: IntuitionisticPropositionalLogic L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}.

Lemma provable_sepcon_andp_left: forall (x y z: expr),
  |-- (x && y) * z --> (x * z) && (y * z).
Proof.
  intros.
  apply solve_impp_andp.
  + apply sepcon_mono.
    - apply andp_elim1.
    - apply provable_impp_refl.
  + apply sepcon_mono.
    - apply andp_elim2.
    - apply provable_impp_refl.
Qed.

Lemma provable_sepcon_andp_right: forall (x y z: expr),
  |-- x * (y && z) --> (x * y) && (x * z).
Proof.
  intros.
  rewrite !(sepcon_comm x).
  apply provable_sepcon_andp_left.
Qed.

Lemma provable_truep_sepcon_truep {ExtsGamma: ExtSeparationLogic L Gamma}:
  |-- TT * TT <--> TT.
Proof.
  intros.
  apply solve_andp_intros.
  + apply solve_impp_elim_left.
    apply provable_impp_refl.
  + apply sepcon_ext.
Qed.

(* TODO: move this to TheoryOfSeparationAxioms. *)
Lemma GC_Ext_Classical_collapse_aux
      {sepcon_orp_AX: SepconOrAxiomatization L Gamma}
      {cpGamma: ClassicalPropositionalLogic L Gamma}
      {gcsGamma: GarbageCollectSeparationLogic L Gamma}
      {ExtsGamma: ExtSeparationLogic L Gamma}:
  forall (x: expr), |-- x --> x * x.
Proof.
  intros.
  rewrite (sepcon_ext x) at 1.
  assert (|-- TT --> x || ~~ x) by (apply solve_impp_elim_left, excluded_middle).
  rewrite H; clear H.
  rewrite sepcon_orp_distr_l.
  apply solve_orp_impp; [apply provable_impp_refl |].
  rewrite <- (andp_dup (x * ~~ x)).
  rewrite sepcon_elim1 at 1.
  rewrite sepcon_elim2 at 1.
  AddSequentCalculus.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  apply deduction_falsep_elim.
  apply deduction_modus_ponens with x.
  + apply deduction_andp_elim1 with (~~x).
    solve_assum.
  + apply deduction_andp_elim2 with x.
    solve_assum.
Qed.

(* TODO: move this to TheoryOfSeparationAxioms. *)
Theorem GC_Ext_Classical_collapse
        {sepcon_orp_AX: SepconOrAxiomatization L Gamma}
        {cpGamma: ClassicalPropositionalLogic L Gamma}
        {gcsGamma: GarbageCollectSeparationLogic L Gamma}
        {ExtsGamma: ExtSeparationLogic L Gamma}:
  forall (x y: expr), |-- x * y <--> x && y.
Proof.
  intros.
  apply solve_andp_intros.
  + apply solve_impp_andp.
    - apply sepcon_elim1.
    - apply sepcon_elim2.
  + rewrite (GC_Ext_Classical_collapse_aux (x && y)).
    apply sepcon_mono.
    - apply andp_elim1.
    - apply andp_elim2.
Qed.

Context {empL: EmpLanguage L}
        {empAX: EmpAxiomatization L Gamma}.

Lemma derivable_emp {gcsGamma: GarbageCollectSeparationLogic L Gamma}:
  forall (x y: expr), |-- emp.
Proof.
  intros.
  rewrite <- (sepcon_elim2 TT emp).
  rewrite sepcon_emp.
  apply provable_impp_refl.
Qed.

End DerivedRules.
