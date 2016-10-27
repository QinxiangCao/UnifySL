Require Import Logic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ClassicalPropositionalLogic.
Require Import Logic.PropositionalLogic.TrivialSemantics.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Definition MCS (Var: Type): Type := sig (maximal_consistent (ClassicalPropositionalLogic.G Var)).

Definition canonical_model {Var: Type} (Phi: MCS Var): @model _ (TrivialSemantics.SM Var) :=
  fun p => (proj1_sig Phi (PropositionalLanguage.varp p)).

Lemma truth_lemma {Var: Type}: forall (Phi: MCS Var) x, canonical_model Phi |= x <-> proj1_sig Phi x.
Proof.
  intros.
Abort.