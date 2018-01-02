Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Sorting.Permutation.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.List_Func_ext.
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
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Definition iter_sepcon {L: Language} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L} (xs: list expr) : expr := fold_left sepcon xs emp.

Definition iter_wand {L: Language} {sL: SeparationLanguage L} (xs: list expr) (y: expr) : expr := fold_right wand y xs.

Section IterSepconRules.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {s'L: SeparationEmpLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma}
        {EmpGamma: EmpSeparationLogic L Gamma}.

Lemma sepcon_iter_sepcon:
  forall xs ys,
    |-- iter_sepcon xs * iter_sepcon ys <--> iter_sepcon (xs ++ ys).
Proof.
  intros.
  apply 
  destruct xs as [| x xs], ys as [| y ys].
  + simpl.
    apply sepcon_emp.
  + simpl.
    rewrite provable_sepcon_comm_iffp.
    apply sepcon_emp.
  + simpl.
    rewrite app_nil_r.
    apply sepcon_emp.
  + apply sepcon_iter_sepcon'.
Qed.

Instance proper_iter_sepcon'_iffp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (default: expr):
  Proper (Forall2 (fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y)) (iter_sepcon' default).
Proof.
  intros.
  apply proper_semi_group_fold.
  apply sepcon_proper_iffp.
Qed.

Instance proper_iter_sepcon'_Permutation {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (default: expr):
  Proper (@Permutation expr ==> (fun x y => |-- iffp x y)) (iter_sepcon' default).
Proof.
  intros.
  hnf; intros.
  apply (@comm_semi_group_fold_perm expr _ provable_iffp_equiv sepcon sepcon_proper_iffp default); auto.
  + intros.
    apply provable_sepcon_comm_iffp.
  + intros.
    apply (@Equivalence_Symmetric _ _ provable_iffp_equiv).
    apply sepcon_assoc.
Qed.
