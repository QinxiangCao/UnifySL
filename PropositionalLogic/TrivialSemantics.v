Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Coq.Logic.Classical_Prop.

Module TrivialSemantics.

Import PropositionalLanguage.

Definition model (Var: Type): Type := Var -> Prop.

Definition sem_imp {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  fun m => X m -> Y m.

Definition sem_neg {model: Type} (X: Ensemble model): Ensemble model :=
  fun m => ~ X m.

Definition sem_and {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  sem_neg (sem_imp X (sem_neg Y)).

Definition sem_or {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  sem_imp (sem_neg X) Y.

Definition sem_iff {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  sem_and (sem_imp X Y) (sem_imp Y X).

Fixpoint denotation {Var: Type} (x: expr Var): Ensemble (model Var) :=
  match x with
  | andp y z => sem_and (denotation y) (denotation z)
  | orp y z => sem_or (denotation y) (denotation z)
  | impp y z => sem_imp (denotation y) (denotation z)
  | iffp y z => sem_iff (denotation y) (denotation z)
  | negp y => sem_neg (denotation y)
  | truep => fun _ => True
  | falsep => fun _ => False
  | varp p => fun m => m p
  end.

Instance SM (Var: Type): Semantics (PropositionalLanguage.L Var) :=
  Build_Semantics (PropositionalLanguage.L Var) (model Var) (fun m x => denotation x m).

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Lemma ImpNegAsPrime_consistent {Var: Type}:
  forall x y: expr Var,
    @ImpNegAsPrime.atomic_reduce (L Var) (nL Var) (pL Var) x y ->
    forall m: model Var, denotation x m <-> denotation y m.
Proof.
  intros; split; intros; destruct H; auto.
Qed.

Lemma ReduceIff_consistent {Var: Type}:
  forall x y: expr Var,
    @ReduceIff.atomic_reduce (L Var) (nL Var) (pL Var) x y ->
    forall m: model Var, denotation x m <-> denotation y m.
Proof.
  intros; split; intros; destruct H; auto.
Qed.

Lemma ReduceFalse_consistent {Var: Type}:
  forall x y: expr Var,
    @ReduceFalse.atomic_reduce (L Var) (nL Var) (pL Var) x y ->
    forall m: model Var, denotation x m <-> denotation y m.
Proof.
  intros; split; intros; destruct H.
  + simpl in H0.
    inversion H0.
  + specialize (H0 I).
    inversion H0.
Qed.

Lemma disjunction_reduce_consistent {Var: Type}:
  forall reduce1 reduce2: relation (expr Var),
    (forall x y, reduce1 x y -> forall m: model Var, denotation x m <-> denotation y m) ->
    (forall x y, reduce2 x y -> forall m: model Var, denotation x m <-> denotation y m) ->
    forall x y, relation_disjunction reduce1 reduce2 x y ->
    forall m: model Var, denotation x m <-> denotation y m.
Proof.
  intros.
  destruct H1.
  + apply H; auto.
  + apply H0; auto.
Qed.

Lemma propag_reduce_consistent {Var: Type}:
  forall reduce: relation (expr Var),
    (forall x y, reduce x y -> forall m: model Var, denotation x m <-> denotation y m) ->
    (forall x y, @propag_reduce (L Var) reduce x y -> forall m: model Var, denotation x m <-> denotation y m).
Proof.
  intros.
  destruct H0.
  induction p as [| [| | | | | | | |]].
  + simpl; apply H; auto.
  + simpl in *.
    unfold TrivialSemantics.sem_and, TrivialSemantics.sem_neg, TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_and, TrivialSemantics.sem_neg, TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_or, TrivialSemantics.sem_neg, TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_or, TrivialSemantics.sem_neg, TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_iff, TrivialSemantics.sem_and, TrivialSemantics.sem_neg, TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_iff, TrivialSemantics.sem_and, TrivialSemantics.sem_neg, TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_neg; simpl.
    tauto.
Qed.

Lemma mendelson_consistent {Var: Type}: reduction_consistent_semantics (MendelsonReduction Var) (SM Var).
Proof.
  apply reduction_consistent_semantics_spec.
  apply propag_reduce_consistent.
  repeat apply disjunction_reduce_consistent.
  + apply ImpNegAsPrime_consistent.
  + apply ReduceIff_consistent.
  + apply ReduceFalse_consistent.
Qed.

End TrivialSemantics.

