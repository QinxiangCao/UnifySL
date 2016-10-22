Require Import Logic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ClassicalPropositionalLogic.
Require Import Logic.PropositionalLogic.TrivialSemantics.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Lemma sound_ImpNegAsPrime {Var: Type}:
  forall x y: @expr (PropositionalLanguage.L Var),
    ImpNegAsPrime.atomic_reduce x y ->
    forall m: @model _ (TrivialSemantics.SM Var), m |= x <-> m |= y.
Proof.
  intros; split; intros; destruct H; auto.
Qed.

Lemma sound_ReduceIff {Var: Type}:
  forall x y: @expr (PropositionalLanguage.L Var),
    ReduceIff.atomic_reduce x y ->
    forall m: @model _ (TrivialSemantics.SM Var), m |= x <-> m |= y.
Proof.
  intros; split; intros; destruct H; auto.
Qed.

Lemma sound_ReduceTrueFalse {Var: Type}:
  forall x y: @expr (PropositionalLanguage.L Var),
    ReduceTrueFalse.atomic_reduce x y ->
    forall m: @model _ (TrivialSemantics.SM Var), m |= x <-> m |= y.
Proof.
  intros; split; intros; destruct H.
  + simpl in H0.
    inversion H0.
  + simpl; intro; auto.
  + specialize (H0 I).
    inversion H0.
  + exact I.
Qed.

Lemma sound_disjunction {Var: Type}:
  forall reduce1 reduce2: relation (@expr (PropositionalLanguage.L Var)),
    (forall x y, reduce1 x y -> forall m: @model _ (TrivialSemantics.SM Var), m |= x <-> m |= y) ->
    (forall x y, reduce2 x y -> forall m: @model _ (TrivialSemantics.SM Var), m |= x <-> m |= y) ->
    (forall x y, relation_disjunction reduce1 reduce2 x y -> forall m: @model _ (TrivialSemantics.SM Var), m |= x <-> m |= y).
Proof.
  intros.
  destruct H1.
  + apply H; auto.
  + apply H0; auto.
Qed.

Lemma sound_prop_congr {Var: Type}:
  forall reduce: relation (@expr (PropositionalLanguage.L Var)),
    (forall x y, reduce x y -> forall m: @model _ (TrivialSemantics.SM Var), m |= x <-> m |= y) ->
    (forall x y, prop_congr reduce x y -> forall m: @model _ (TrivialSemantics.SM Var), m |= x <-> m |= y).
Proof.
  intros.
  induction H0.
  + apply H; auto.
  + simpl in *.
    unfold TrivialSemantics.sem_and, TrivialSemantics.sem_neg, TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_or, TrivialSemantics.sem_neg, TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_iff, TrivialSemantics.sem_and, TrivialSemantics.sem_neg, TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_neg; simpl.
    tauto.
Qed.

Lemma sound_clos_refl_trans {Var: Type}:
  forall reduce: relation (@expr (PropositionalLanguage.L Var)),
    (forall x y, reduce x y -> forall m: @model _ (TrivialSemantics.SM Var), m |= x <-> m |= y) ->
    (forall x y, clos_refl_trans expr reduce x y -> forall m: @model _ (TrivialSemantics.SM Var), m |= x <-> m |= y).
Proof.
  intros.
  induction H0.
  + apply H; auto.
  + tauto.
  + tauto.
Qed.

Lemma sound_reduce {Var: Type}:
  forall x y: @expr (PropositionalLanguage.L Var), reduce x y ->
    forall m: @model _ (TrivialSemantics.SM Var), m |= x <-> m |= y.
Proof.
  apply sound_clos_refl_trans.
  apply sound_prop_congr.
  repeat apply sound_disjunction.
  + apply sound_ImpNegAsPrime.
  + apply sound_ReduceIff.
  + apply sound_ReduceTrueFalse.
Qed.

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
  + pose proof sound_reduce x y H.
    exact (proj1 (H1 m) IHprovable).
  + pose proof sound_modus_ponens x y.
    exact (H1 m IHprovable1 IHprovable2).
  + apply sound_axiom1.
  + apply sound_axiom2.
  + apply sound_axiom3.
Qed.
