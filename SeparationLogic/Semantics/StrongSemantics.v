Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Definition wand {worlds: Type} {R: Relation worlds} {J: Join worlds} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => forall m0 m1 m2, m <= m0 -> join m0 m1 m2 -> X m1 -> Y m2.

Definition emp {worlds: Type} {R: Relation worlds} {J: Join worlds}: Ensemble worlds := increasing'.

Lemma wand_closed
      {worlds: Type}
      {R: Relation worlds}
      {kiM: KripkeIntuitionisticModel worlds}
      {J: Join worlds}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (wand X Y).
Proof.
  intros.
  hnf; intros.
  hnf in H2 |- *.
  intros ? ? ? ?; apply H2.
  etransitivity; eauto.
Qed.

Lemma emp_closed
      {worlds: Type}
      {R: Relation worlds}
      {kiM: KripkeIntuitionisticModel worlds}
      {J: Join worlds}:
  upwards_closed_Kdenote emp.
Proof.
  intros.
  hnf; intros.
  hnf in H0 |- *.
  intros ? ?; apply H0.
  etransitivity; eauto.
Qed.
