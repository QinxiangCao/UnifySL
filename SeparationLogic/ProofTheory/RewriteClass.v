Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Coqlib.
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

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Instance sepcon_proper_impp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) sepcon.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  apply sepcon_mono; auto.
Qed.

Instance wand_proper_impp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: Proper ((fun x y => |-- impp x y) --> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) wand.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  unfold Basics.flip in H.
  apply wand_sepcon_adjoint.
  rewrite provable_derivable in H0 |- *.
  eapply deduction_impp_trans; [clear H0 | apply H0].
  eapply deduction_impp_trans with ((x1 -* y1) * x1).
  + rewrite <- provable_derivable.
    apply sepcon_mono; [apply provable_impp_refl | apply H].
  + rewrite <- provable_derivable.
    apply wand_sepcon_adjoint.
    apply provable_impp_refl.
Qed.

Instance sepcon_proper_iffp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: Proper ((fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y)) sepcon.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite provable_derivable in H, H0 |- *.
  pose proof deduction_andp_elim1 _ _ _ H.
  pose proof deduction_andp_elim2 _ _ _ H.
  pose proof deduction_andp_elim1 _ _ _ H0.
  pose proof deduction_andp_elim2 _ _ _ H0.
  apply deduction_andp_intros; rewrite <- provable_derivable in H1, H2, H3, H4 |- *.
  + rewrite H1, H3.
    apply provable_impp_refl.
  + rewrite H2, H4.
    apply provable_impp_refl.
Qed.

Instance wand_proper_iffp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: Proper ((fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y) ==> (fun x y => |-- iffp x y)) wand.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite provable_derivable in H, H0 |- *.
  pose proof deduction_andp_elim1 _ _ _ H.
  pose proof deduction_andp_elim2 _ _ _ H.
  pose proof deduction_andp_elim1 _ _ _ H0.
  pose proof deduction_andp_elim2 _ _ _ H0.
  apply deduction_andp_intros; rewrite <- provable_derivable in H1, H2, H3, H4 |- *.
  + rewrite H2, H3.
    apply provable_impp_refl.
  + rewrite H1, H4.
    apply provable_impp_refl.
Qed.
