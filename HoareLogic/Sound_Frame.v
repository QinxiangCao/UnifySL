Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.SeparationLogic.Semantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.BigStepSemantics.
Require Import Logic.HoareLogic.HoareLogic_Sequential.

(* TODO: use lift_join to define this type class. *)
Class SABigStepSemantics (P: ProgrammingLanguage) (state: Type) {J: Join state} (BSS: BigStepSemantics P state): Type := {
  safety_preserve: forall m mf m' c, join m mf m' -> safe m c -> safe m' c;
  terminate_preserve: forall m mf m' c, join m mf m' -> term_norm m c -> term_norm m' c;
  frame_property: forall m mf m' c n', join m mf m' -> safe m c -> access m' c (Terminating n') -> exists n, join n mf n' /\ access m c (Terminating n)
}.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.

Section soundness.

Existing Instance unit_kMD.

Context {P: ProgrammingLanguage}
        {MD: Model}
        {BSS: BigStepSemantics P model}
        {nBSS: NormalBigStepSemantics P model BSS}
        {J: Join model}
        {SA_BSS: SABigStepSemantics P model BSS}.

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
