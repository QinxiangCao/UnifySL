Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.

Local Open Scope logic_base.
Local Open Scope syntax.

Instance provable_impp_rewrite {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L}: RewriteRelation (fun x y => |-- x --> y).

Instance provable_impp_refl {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma}: Reflexive (fun x y => |-- x --> y).
Proof.
  intros.
  hnf; intros.
  apply provable_impp_refl.
Qed.

Instance provable_proper_impp {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} : Proper ((fun x y => |-- impp x y) ==> Basics.impl) provable.
Proof.
  intros.
  hnf; intros.
  intro.
  eapply modus_ponens; eauto.
Qed.

Instance derivable_proper_impp {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} : Proper (eq ==> (fun x y => |-- impp x y) ==> Basics.impl) derivable.
Proof.
  hnf; intros Phi Phi' ?; subst Phi'.
  hnf; intros x1 x2 ?.
  intro.
  apply (deduction_weaken0 Phi) in H.
  exact (deduction_modus_ponens _ _ _ H0 H).
Qed.

Instance impp_proper_impp {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} : Proper ((fun x y => |-- impp x y) --> (fun x y => |-- impp x y) ==> (fun x y => |-- impp x y)) impp.
Proof.
  hnf; intros x1 x2 ?.
  hnf; intros y1 y2 ?.
  unfold Basics.flip in H.
  rewrite provable_derivable.
  rewrite <- !deduction_theorem.
  apply (deduction_weaken0 (Union expr (Union expr empty_context (Singleton expr (x1 --> y1))) (Singleton expr x2))) in H.
  apply (deduction_weaken0 (Union expr (Union expr empty_context (Singleton expr (x1 --> y1))) (Singleton expr x2))) in H0.
  pose proof derivable_assum1 (Union expr empty_context (Singleton expr (x1 --> y1))) x2.
  pose proof derivable_assum1 empty_context (x1 --> y1).
  apply (deduction_weaken1 _ x2) in H2.
  pose proof deduction_modus_ponens _ _ _ H1 H.
  pose proof deduction_modus_ponens _ _ _ H3 H2.
  pose proof deduction_modus_ponens _ _ _ H4 H0.
  auto.
Qed.

Goal forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) y1 y2,
  |-- y1 --> y2 ->
  Phi |-- y1 ->
  Phi |-- y2.
Proof.
  intros.
  rewrite <- H.
  auto.
Qed.

Goal forall {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} (Phi: context) x1 y1 x2 y2,
  |-- x2 --> x1 ->
  |-- y1 --> y2 ->
  Phi |-- x1 --> y1 ->
  Phi |-- x2 --> y2.
Proof.
  intros.
  rewrite <- H0, H.
  auto.
Qed.
