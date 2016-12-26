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
        {BSS: BigStepSemantics P model}.

Context {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L MD} {kiM: KripkeIntuitionisticModel model} {kiSM: KripkeIntuitionisticSemantics L MD tt SM}.

Lemma hoare_consequence_partial_sound: forall c P1 P2 Q1 Q2,
  valid (AllModel _) (P2 --> P1) ->
  valid (AllModel _) (Q1 --> Q2) ->
  triple_partial_valid P1 c Q1 ->
  triple_partial_valid P2 c Q2.
Proof.
  intros.
  unfold triple_partial_valid in *.
  intros s ms ? ?.
  specialize (H1 s ms).
  specialize (H (KRIPKE: s) I).
  rewrite sat_impp in H.
  apply (H s) in H2; [| reflexivity].
  specialize (H1 H2 H3); clear H2 H3.
  destruct ms as [| | s']; auto.
  specialize (H0 (KRIPKE: s') I).
  rewrite sat_impp in H0.
  apply (H0 s'); auto.
  reflexivity.
Qed.

Lemma hoare_consequence_total_sound: forall c P1 P2 Q1 Q2,
  valid (AllModel _) (P2 --> P1) ->
  valid (AllModel _) (Q1 --> Q2) ->
  triple_total_valid P1 c Q1 ->
  triple_total_valid P2 c Q2.
Proof.
  intros.
  unfold triple_total_valid in *.
  intros s ms ? ?.
  specialize (H1 s ms).
  specialize (H (KRIPKE: s) I).
  rewrite sat_impp in H.
  apply (H s) in H2; [| reflexivity].
  specialize (H1 H2 H3); clear H2 H3.
  destruct ms as [| | s']; auto.
  specialize (H0 (KRIPKE: s') I).
  rewrite sat_impp in H0.
  apply (H0 s'); auto.
  reflexivity.
Qed.

End soundness.
