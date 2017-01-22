Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Instance andp_proper_impp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma}: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) andp.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite provable_derivable.
  rewrite <- !deduction_theorem.
  apply (deduction_weaken0 (Union expr empty_context (Singleton expr (x1 && y1)))) in H.
  apply (deduction_weaken0 (Union expr empty_context (Singleton expr (x1 && y1)))) in H0.
  pose proof derivable_assum1 empty_context (x1 && y1).
  pose proof deduction_andp_elim1 _ _ _ H1.
  pose proof deduction_andp_elim2 _ _ _ H1.
  pose proof deduction_modus_ponens _ _ _ H2 H.
  pose proof deduction_modus_ponens _ _ _ H3 H0.
  apply deduction_andp_intros; auto.
Qed.

Instance orp_proper_impp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma}: Proper ((fun x y => |-- impp x y) ==> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) orp.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite provable_derivable in H, H0 |- *.
  apply deduction_orp_elim.
  + eapply deduction_impp_trans; [exact H |].
    apply derivable_orp_intros1.
  + eapply deduction_impp_trans; [exact H0 |].
    apply derivable_orp_intros2.
Qed.

Instance provable_iffp_rewrite {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma}: RewriteRelation (fun x y => |-- x <--> y).

Instance provable_iffp_equiv {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma}: Equivalence (fun x y => |-- x <--> y).
Proof.
  constructor.
  + hnf; intros.
    rewrite provable_derivable.
    apply deduction_andp_intros; apply derivable_impp_refl.
  + hnf; intros.
    rewrite provable_derivable in H |- *.
    pose proof deduction_andp_elim1 _ _ _ H.
    pose proof deduction_andp_elim2 _ _ _ H.
    apply deduction_andp_intros; auto.
  + hnf; intros.
    rewrite provable_derivable in H, H0 |- *.
    pose proof deduction_andp_elim1 _ _ _ H.
    pose proof deduction_andp_elim2 _ _ _ H.
    pose proof deduction_andp_elim1 _ _ _ H0.
    pose proof deduction_andp_elim2 _ _ _ H0.
    apply deduction_andp_intros; eapply deduction_impp_trans; eauto.
Qed.

Instance provable_proper_iffp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} : Proper ((fun x y => |-- x <--> y) ==> iff) provable.
Proof.
  intros.
  hnf; intros.
  rewrite provable_derivable in H.
  rewrite provable_derivable.
  rewrite provable_derivable.
  pose proof deduction_andp_elim1 _ _ _ H.
  pose proof deduction_andp_elim2 _ _ _ H.
  split; intro;
  eapply deduction_modus_ponens; eauto.
Qed.

Instance derivable_proper_iffp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} : Proper (eq ==> (fun x y => |-- x <--> y) ==> iff) derivable.
Proof.
  hnf; intros Phi Phi' ?; subst Phi'.
  hnf; intros x1 x2 ?.
  apply (deduction_weaken0 Phi) in H.
  pose proof deduction_andp_elim1 _ _ _ H.
  pose proof deduction_andp_elim2 _ _ _ H.
  split; intro;
  eapply deduction_modus_ponens; eauto.
Qed.

Instance impp_proper_iffp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} : Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) impp.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite provable_derivable in H.
  rewrite provable_derivable in H0.
  rewrite provable_derivable.
  pose proof deduction_andp_elim1 _ _ _ H.
  pose proof deduction_andp_elim2 _ _ _ H.
  pose proof deduction_andp_elim1 _ _ _ H0.
  pose proof deduction_andp_elim2 _ _ _ H0.
  rewrite <- provable_derivable in H1.
  rewrite <- provable_derivable in H2.
  rewrite <- provable_derivable in H3.
  rewrite <- provable_derivable in H4.
  apply deduction_andp_intros; rewrite <- provable_derivable.
  + apply impp_proper_impp; auto.
  + apply impp_proper_impp; auto.
Qed.

Instance andp_proper_iffp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma}: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) andp.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite provable_derivable in H.
  rewrite provable_derivable in H0.
  rewrite provable_derivable.
  pose proof deduction_andp_elim1 _ _ _ H.
  pose proof deduction_andp_elim2 _ _ _ H.
  pose proof deduction_andp_elim1 _ _ _ H0.
  pose proof deduction_andp_elim2 _ _ _ H0.
  rewrite <- provable_derivable in H1.
  rewrite <- provable_derivable in H2.
  rewrite <- provable_derivable in H3.
  rewrite <- provable_derivable in H4.
  apply deduction_andp_intros; rewrite <- provable_derivable.
  + apply andp_proper_impp; auto.
  + apply andp_proper_impp; auto.
Qed.

Instance orp_proper_iffp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma}: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) orp.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  rewrite provable_derivable in H.
  rewrite provable_derivable in H0.
  rewrite provable_derivable.
  pose proof deduction_andp_elim1 _ _ _ H.
  pose proof deduction_andp_elim2 _ _ _ H.
  pose proof deduction_andp_elim1 _ _ _ H0.
  pose proof deduction_andp_elim2 _ _ _ H0.
  rewrite <- provable_derivable in H1.
  rewrite <- provable_derivable in H2.
  rewrite <- provable_derivable in H3.
  rewrite <- provable_derivable in H4.
  apply deduction_andp_intros; rewrite <- provable_derivable.
  + apply orp_proper_impp; auto.
  + apply orp_proper_impp; auto.
Qed.

Instance iffp_proper_iffp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma}: Proper ((fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y) ==> (fun x y => |-- x <--> y)) iffp.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  unfold iffp.
  rewrite H, H0.
  rewrite provable_derivable.
  apply deduction_andp_intros; apply derivable_impp_refl.
Qed.


