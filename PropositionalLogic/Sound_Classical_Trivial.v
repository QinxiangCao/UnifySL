Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.MinimunLogic.ContextProperty.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.IntuitionisticPropositionalLogic.
Require Import Logic.PropositionalLogic.ClassicalPropositionalLogic.
Require Import Logic.PropositionalLogic.TrivialSemantics.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Lemma sound_modus_ponens {Var: Type}:
  forall x y: @expr (PropositionalLanguage.L Var),
    forall m: @model (TrivialSemantics.MD Var),
      m |= (x --> y) -> m |= x -> m |= y.
Proof.
  intros.
  apply H; auto.
Qed.

Lemma sound_axiom1 {Var: Type}:
  forall x y: @expr (PropositionalLanguage.L Var),
    forall m: @model (TrivialSemantics.MD Var),
      m |= x --> y --> x.
Proof.
  intros; intros ? ?; auto.
Qed.

Lemma sound_axiom2 {Var: Type}:
  forall x y z: @expr (PropositionalLanguage.L Var),
    forall m: @model (TrivialSemantics.MD Var),
      m |= (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
  intros.
  simpl.
  intros ? ? ?.
  specialize (H H1).
  specialize (H0 H1).
  auto.
Qed.

Lemma sound_andp_intros {Var: Type}:
  forall x y: @expr (PropositionalLanguage.L Var),
    forall m: @model (TrivialSemantics.MD Var),
      m |= x --> y --> x && y.
Proof.
  intros.
  simpl; intros ? ?.
  unfold TrivialSemantics.sem_and.
  auto.
Qed.

Lemma sound_andp_elim1 {Var: Type}:
  forall x y: @expr (PropositionalLanguage.L Var),
    forall m: @model (TrivialSemantics.MD Var),
      m |= x && y --> x.
Proof.
  intros.
  simpl; intros [? ?].
  auto.
Qed.

Lemma sound_andp_elim2 {Var: Type}:
  forall x y: @expr (PropositionalLanguage.L Var),
    forall m: @model (TrivialSemantics.MD Var),
      m |= x && y --> y.
Proof.
  intros.
  simpl; intros [? ?].
  auto.
Qed.

Lemma sound_orp_intros1 {Var: Type}:
  forall x y: @expr (PropositionalLanguage.L Var),
    forall m: @model (TrivialSemantics.MD Var),
      m |= x --> x || y.
Proof.
  intros.
  simpl; intros ?.
  unfold TrivialSemantics.sem_or.
  auto.
Qed.

Lemma sound_orp_intros2 {Var: Type}:
  forall x y: @expr (PropositionalLanguage.L Var),
    forall m: @model (TrivialSemantics.MD Var),
      m |= y --> x || y.
Proof.
  intros.
  simpl; intros ?.
  unfold TrivialSemantics.sem_or.
  auto.
Qed.

Lemma sound_orp_elim {Var: Type}:
  forall x y z: @expr (PropositionalLanguage.L Var),
    forall m: @model (TrivialSemantics.MD Var),
      m |= (x --> z) --> (y --> z) --> (x || y --> z).
Proof.
  intros.
  simpl.
  unfold TrivialSemantics.sem_or, TrivialSemantics.sem_imp.
  intros; tauto.
Qed.

Lemma sound_falsep_elim {Var: Type}:
  forall x: @expr (PropositionalLanguage.L Var),
    forall m: @model (TrivialSemantics.MD Var),
      m |= FF --> x.
Proof.
  intros.
  intros [].
Qed.

Lemma sound_excluded_middle {Var: Type}:
  forall x: @expr (PropositionalLanguage.L Var),
    forall m: @model (TrivialSemantics.MD Var),
      m |= x || (x --> FF).
Proof.
  intros.
  simpl.
  unfold TrivialSemantics.sem_or, TrivialSemantics.sem_imp.
  tauto.
Qed.

Theorem sound_classical_trivial (Var: Type): sound (ClassicalPropositionalLogic.G Var) (TrivialSemantics.SM Var).
Proof.
  hnf; intros.
  intro m.
  induction H.
  + pose proof sound_modus_ponens x y.
    exact (H1 m IHprovable1 IHprovable2).
  + apply sound_axiom1.
  + apply sound_axiom2.
  + apply sound_andp_intros.
  + apply sound_andp_elim1. 
  + apply sound_andp_elim2.
  + apply sound_orp_intros1.
  + apply sound_orp_intros2.
  + apply sound_orp_elim.
  + apply sound_falsep_elim.
  + apply sound_excluded_middle.
Qed.

