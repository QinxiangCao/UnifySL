Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ClassicalPropositionalLogic.
Require Import Logic.PropositionalLogic.TrivialSemantics.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Lemma sound_modus_ponens {Var: Type}:
  forall x y: @expr (PropositionalLanguage.L Var),
    forall m: @model _ (TrivialSemantics.SM Var),
      m |= (x --> y) -> m |= x -> m |= y.
Proof.
  intros.
  apply H; auto.
Qed.

Lemma sound_axiom1 {Var: Type}:
  forall x y: @expr (PropositionalLanguage.L Var),
    forall m: @model _ (TrivialSemantics.SM Var),
      m |= x --> y --> x.
Proof.
  intros; intros ? ?; auto.
Qed.

Lemma sound_axiom2 {Var: Type}:
  forall x y z: @expr (PropositionalLanguage.L Var),
    forall m: @model _ (TrivialSemantics.SM Var),
      m |= (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
  intros.
  simpl.
  intros ? ? ?.
  specialize (H H1).
  specialize (H0 H1).
  auto.
Qed.

Lemma sound_axiom3 {Var: Type}:
  forall x y: @expr (PropositionalLanguage.L Var),
    forall m: @model _ (TrivialSemantics.SM Var),
      m |= (~~ y --> x) --> (~~ y --> ~~ x) --> y.
Proof.
  intros.
  simpl; intros ? ?.
  destruct (Classical_Prop.classic (TrivialSemantics.denotation y m)); auto.
  specialize (H H1).
  specialize (H0 H1).
  contradiction.
Qed.

Theorem sound_classical_trivial (Var: Type): sound (ClassicalPropositionalLogic.G Var) (TrivialSemantics.SM Var).
Proof.
  hnf; intros.
  intro m.
  induction H.
  + rewrite <- (sat_reduce x y m H); auto.
  + rewrite -> (sat_reduce x y m H); auto.
  + pose proof sound_modus_ponens x y.
    exact (H1 m IHprovable1 IHprovable2).
  + apply sound_axiom1.
  + apply sound_axiom2.
  + apply sound_axiom3.
  + apply I.
Qed.
