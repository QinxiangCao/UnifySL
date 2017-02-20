Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Sorting.Permutation.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.List_Func_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Definition iter_sepcon' {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} (default: expr) (xs: list expr) : expr := semi_group_fold default sepcon xs.

Definition iter_sepcon {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L} (xs: list expr) : expr := iter_sepcon' emp xs.

Definition iter_wand {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L} (xs: list expr) (y: expr) : expr := fold_right wand y xs.

Lemma sepcon_iter_sepcon' {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}:
  forall (default: expr) x xs y ys,
    |-- iter_sepcon' default (x :: xs) * iter_sepcon' default (y :: ys) <-->
        iter_sepcon' default ((x :: xs) ++ (y :: ys)).
Proof.
  intros.
  apply (@Equivalence_Symmetric _ _ provable_iffp_equiv).
  apply (@semi_group_fold_app expr _ provable_iffp_equiv sepcon sepcon_proper_iffp default).
  + intros.
    apply (@Equivalence_Symmetric _ _ provable_iffp_equiv).
    apply sepcon_assoc.
  + intro; congruence.
  + intro; congruence.
Qed.

Lemma sepcon_iter_sepcon {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {eGamma: SeparationEmpLogic L Gamma} {ueGamma: UnitalSeparationLogic L Gamma}:
  forall xs ys,
    |-- iter_sepcon xs * iter_sepcon ys <--> iter_sepcon (xs ++ ys).
Proof.
  intros.
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
