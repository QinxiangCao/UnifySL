Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.SeparationLogic.Semantics.

Class SABigStepSemantics (Imp: ImperativeProgrammingLanguage) (state: Type) {SA: SeparationAlgebra state} (BSS: BigStepSemantics Imp state): Type := {
  safety_preserve: forall m mf m' c, join m mf m' -> safe m c -> safe m' c;
  terminate_preserve: forall m mf m' c, join m mf m' -> term_norm m c -> term_norm m' c;
  frame_property: forall m mf m' c n', join m mf m' -> safe m c -> access m' c (Terminating n') -> exists n, join n mf n' /\ access m c (Terminating n)
}.

Class HoareLogic (Imp: ImperativeProgrammingLanguage) (L: Language): Type := {
  triple: expr -> cmd -> expr -> Prop
}.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.

Existing Instance unit_kMD.

Definition triple_partial_valid {Imp: ImperativeProgrammingLanguage} {L: Language} {MD: Model} {BSS: BigStepSemantics Imp (model)} {SM: Semantics L MD} (Pre: expr) (c: cmd) (Post: expr): Prop :=
  forall (s_pre: model) (ms_post: MetaState model),
  KRIPKE: s_pre |= Pre ->
  access s_pre c ms_post ->
  match ms_post with
  | Error => False
  | NonTerminating => True
  | Terminating s_post => KRIPKE: s_post |= Post
  end.

Definition triple_total_valid {Imp: ImperativeProgrammingLanguage} {L: Language} {MD: Model} {BSS: BigStepSemantics Imp (model)} {SM: Semantics L MD} (Pre: expr) (c: cmd) (Post: expr): Prop :=
  forall (s_pre: model) (ms_post: MetaState model),
  KRIPKE: s_pre |= Pre ->
  access s_pre c ms_post ->
  match ms_post with
  | Error => False
  | NonTerminating => False
  | Terminating s_post => KRIPKE: s_post |= Post
  end.

Section soundness.

Context {Imp: ImperativeProgrammingLanguage} {MD: Model} {BSS: BigStepSemantics Imp model} {nBSS: NormalBigStepSemantics Imp model BSS} {SA: SeparationAlgebra model} {SA_BSS: SABigStepSemantics Imp model BSS}.

Context {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L MD} {kiM: KripkeIntuitionisticModel model} {kiSM: KripkeIntuitionisticSemantics L MD tt SM} {fsSM: FlatSemantics.FlatSemantics L MD tt SM}.

Lemma hoare_frame_partial_sound: forall c P Q F,
  triple_partial_valid P c Q ->
  triple_partial_valid (P * F) c (Q * F).
Proof.
  intros.
  unfold triple_partial_valid in *.
  intros s ms ? ?.
  rewrite FlatSemantics.sat_sepcon in H0.
  destruct H0 as [m [f [? [? ?]]]].
  assert (safe m c) by exact (H m Error H2).
  destruct ms as [| | n'].
  + pose proof safety_preserve _ _ _ c H0.
    revert H1; apply H5; auto.
  + auto.
  + destruct (frame_property _ _ _ _ _ H0 H4 H1) as [n [? ?]].
    rewrite FlatSemantics.sat_sepcon.
    exists n, f.
    split; [| split]; auto.
    apply (H m _ H2 H6).
Qed.

Lemma hoare_frame_total_sound: forall c P Q F,
  triple_total_valid P c Q ->
  triple_total_valid (P * F) c (Q * F).
Proof.
  intros.
  unfold triple_partial_valid in *.
  intros s ms ? ?.
  rewrite FlatSemantics.sat_sepcon in H0.
  destruct H0 as [m [f [? [? ?]]]].
  assert (safe m c) by exact (H m Error H2).
  assert (term_norm m c) by exact (conj (H m Error H2) (H m NonTerminating H2)).
  destruct ms as [| | n'].
  + pose proof safety_preserve _ _ _ c H0.
    revert H1; apply H6; auto.
  + pose proof terminate_preserve _ _ _ c H0.
    revert H1; apply H6; auto.
  + destruct (frame_property _ _ _ _ _ H0 H4 H1) as [n [? ?]].
    rewrite FlatSemantics.sat_sepcon.
    exists n, f.
    split; [| split]; auto.
    apply (H m _ H2 H7).
Qed.

End soundness.
