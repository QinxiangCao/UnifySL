Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Section RewriteClass.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {wandL: WandLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {sepconAX: SepconAxiomatization L Gamma}
        {wandAX: WandAxiomatization L Gamma}.

Instance sepcon_proper_impp: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) sepcon.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  apply sepcon_mono; auto.
Qed.

Instance wand_proper_impp: Proper ((fun x y => |-- impp x y) --> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) wand.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  unfold Basics.flip in H.
  apply wand_mono; auto.
Qed.

Context {pL: PropositionalLanguage L}
        {ipAX: IntuitionisticPropositionalLogic L Gamma}.

Instance sepcon_proper_iffp: Proper ((fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y)) sepcon.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  apply solve_andp_intros.
  + apply sepcon_mono.
    - rewrite H; apply provable_impp_refl.
    - rewrite H0; apply provable_impp_refl.
  + apply sepcon_mono.
    - rewrite H; apply provable_impp_refl.
    - rewrite H0; apply provable_impp_refl.
Qed.

Instance wand_proper_iffp: Proper ((fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y)) wand.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  apply solve_andp_intros.
  + apply wand_mono.
    - rewrite H; apply provable_impp_refl.
    - rewrite H0; apply provable_impp_refl.
  + apply wand_mono.
    - rewrite H; apply provable_impp_refl.
    - rewrite H0; apply provable_impp_refl.
Qed.

End RewriteClass.

Existing Instances sepcon_proper_impp wand_proper_impp sepcon_proper_iffp wand_proper_iffp.
