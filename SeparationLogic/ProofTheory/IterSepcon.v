Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Sorting.Permutation.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.List_Func_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Section IterSepconRules.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {empL: EmpLanguage L}
        {iter_sepcon_L: IterSepconLanguage L}
        {iter_wand_L: IterWandLanguage L}
        {iter_sepcon_Def: NormalIterSepcon L}
        {iter_wand_Def: NormalIterWand L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipAX: IntuitionisticPropositionalLogic L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}
        {wandAX: WandAxiomatization L Gamma}
        {empAX: EmpAxiomatization L Gamma}.

Lemma sepcon_iter_sepcon:
  forall xs ys,
    |-- iter_sepcon xs * iter_sepcon ys <--> iter_sepcon (xs ++ ys).
Proof.
  intros.
  rewrite !iter_sepcon_def.
  apply (@assoc_prodp_fold_left_equiv _ _ _ _ _ _ _ _ sepcon_Mono sepcon_Assoc sepcon_LU sepcon_RU).
Qed.

Lemma sepcon_iter_unfold_right_assoc:
  forall xs,
    |-- iter_sepcon xs <-->
        (fix f xs :=
           match xs with
           | nil => emp
           | cons x nil => x
           | cons x xs0 => x * f xs0
           end) xs.
Proof.
  intros.
  rewrite iter_sepcon_def.
  pose proof @assoc_fold_left_fold_right_equiv _ _ _ _ _ _ sepcon emp sepcon_Mono sepcon_Assoc sepcon_LU sepcon_RU.
  rewrite H.
  pose proof @fold_right_prodp_unfold _ _ _ _ _ _ sepcon sepcon_Mono emp sepcon_RU.
  apply H0.
Qed.

Lemma sepcon_iter_unfold_left_assoc:
  forall xs,
    |-- iter_sepcon xs <-->
        match xs with
        | nil => emp
        | x :: xs0 => (fix f xs x :=
                         match xs with
                         | nil => x
                         | x0 :: xs0 => f xs0 (x * x0)
                         end) xs0 x
        end.
Proof.
  intros.
  rewrite iter_sepcon_def.
  pose proof @fold_left_prodp_unfold _ _ _ _ _ _ sepcon sepcon_Mono emp sepcon_LU.
  apply H.
Qed.

(* TODO: Should this really be an instance? *)
Instance proper_iter_sepcon_impp:
  Proper (Forall2 (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) iter_sepcon.
Proof.
  intros.
  hnf; intros.
  rewrite !iter_sepcon_def.
  exact (proper_fold_left' sepcon _ _ H emp emp (provable_impp_refl _)).
Qed.

(* TODO: Should this really be an instance? *)
Instance proper_iter_sepcon_iffp:
  Proper (Forall2 (fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y)) iter_sepcon.
Proof.
  intros.
  hnf; intros.
  rewrite !iter_sepcon_def.
  exact (proper_fold_left' sepcon _ _ H emp emp (provable_iffp_refl _)).
Qed.

(* TODO: Should this really be an instance? *)
Instance proper_iter_sepcon_Permutation: Proper (@Permutation expr ==> (fun x y => |-- iffp x y)) iter_sepcon.
Proof.
  intros.
  hnf; intros.
  rewrite !iter_sepcon_def.
  apply (@assoc_fold_left_Permutation _ _ _ _ _ _ _ sepcon_Mono sepcon_Comm sepcon_Assoc); auto.
Qed.

End IterSepconRules.
