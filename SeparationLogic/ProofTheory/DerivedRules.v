Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
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
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma}.

Lemma provable_sepcon_comm_iffp: forall (x y: expr),
  |-- x * y <--> y * x.
Proof.
  intros.
  apply solve_andp_intros;
  apply sepcon_comm.
Qed.

Lemma provable_sepcon_orp_left: forall (x y z: expr),
  |-- (x || y) * z <--> x * z || y * z.
Proof.
  intros.
  apply solve_andp_intros.
  + apply wand_sepcon_adjoint.
    apply solve_orp_impp; apply wand_sepcon_adjoint.
    - apply orp_intros1.
    - apply orp_intros2.
  + apply solve_orp_impp.
    - apply sepcon_mono.
      * apply orp_intros1.
      * apply provable_impp_refl.
    - apply sepcon_mono.
      * apply orp_intros2.
      * apply provable_impp_refl.
Qed.

Lemma provable_sepcon_orp_right: forall (x y z: expr),
  |-- x * (y || z) <--> x * y || x * z.
Proof.
  intros.
  unfold iffp.
  rewrite (sepcon_comm x (y || z)) at 1.
  rewrite <- (sepcon_comm (y || z) x) at 1.
  rewrite <- (sepcon_comm y x) at 1.
  rewrite (sepcon_comm x y) at 1.
  rewrite <- (sepcon_comm z x) at 1.
  rewrite (sepcon_comm x z) at 1.
  apply provable_sepcon_orp_left.
Qed.

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
  rewrite !(provable_sepcon_comm_iffp x).
  apply provable_sepcon_andp_left.
Qed.

Lemma provable_FF_sepcon: forall (x: expr),
  |-- FF * x --> FF.
Proof.
  intros.
  apply wand_sepcon_adjoint.
  apply falsep_elim.
Qed.

Lemma provable_sepcon_FF: forall (x: expr),
  |-- x * FF --> FF.
Proof.
  intros.
  rewrite (sepcon_comm x FF).
  apply provable_FF_sepcon.
Qed.

Lemma provable_wand_sepcon_modus_ponens1: forall (x y: expr),
  |-- (x -* y) * x --> y.
Proof.
  intros.
  apply wand_sepcon_adjoint.
  apply provable_impp_refl.
Qed.

Lemma provable_wand_sepcon_modus_ponens2: forall (x y: expr),
  |-- x * (x -* y) --> y.
Proof.
  intros.
  rewrite (sepcon_comm x (x -* y)).
  apply provable_wand_sepcon_modus_ponens1.
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

Lemma derivable_emp {s'L: SeparationEmpLanguage L} {eGamma: EmpSeparationLogic L Gamma} {gcsGamma: GarbageCollectSeparationLogic L Gamma}: forall (x y: expr),
  |-- emp.
Proof.
  intros.
  rewrite <- (sepcon_elim2 TT emp).
  rewrite sepcon_emp.
  apply provable_impp_refl.
Qed.

Lemma GC_Ext_Classical_collapse_aux {cpGamma: ClassicalPropositionalLogic L Gamma} {gcsGamma: GarbageCollectSeparationLogic L Gamma} {ExtsGamma: ExtSeparationLogic L Gamma}: forall (x: expr),
  |-- x --> x * x.
Proof.
  intros.
  rewrite (sepcon_ext x) at 1.
  assert (|-- TT --> x || ~~ x) by (apply solve_impp_elim_left, excluded_middle).
  rewrite H; clear H.
  rewrite provable_sepcon_orp_right.
  apply solve_orp_impp; [apply provable_impp_refl |].
  rewrite <- (andp_dup (x * ~~ x)).
  rewrite sepcon_elim1 at 1.
  rewrite sepcon_elim2 at 1.
  clear sGamma gcsGamma ExtsGamma.
  AddSequentCalculus Gamma.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  apply deduction_falsep_elim.
  apply deduction_modus_ponens with x.
  + apply deduction_andp_elim1 with (~~x).
    solve_assum.
  + apply deduction_andp_elim2 with x.
    solve_assum.
Qed.

Theorem GC_Ext_Classical_collapse {cpGamma: ClassicalPropositionalLogic L Gamma} {gcsGamma: GarbageCollectSeparationLogic L Gamma} {ExtsGamma: ExtSeparationLogic L Gamma}: forall (x y: expr),
  |-- x * y <--> x && y.
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

End DerivedRules.
