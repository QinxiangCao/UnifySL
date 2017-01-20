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

Definition sepcon {worlds: Type} {J: Join worlds} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => exists m1 m2, join m1 m2 m /\ X m1 /\ Y m2.

Lemma sepcon_closed
      {worlds: Type}
      {R: Relation worlds}
      {kiM: KripkeIntuitionisticModel worlds}
      {J: Join worlds}
      {SA: SeparationAlgebra worlds}
      {uSA: UpwardsClosedSeparationAlgebra worlds}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (sepcon X Y).
Proof.
  intros.
  hnf; intros.
  hnf in H2 |- *.
  destruct H2 as [n1 [n2 [? [? ?]]]].
  destruct (join_Korder_up _ _ _ _ H2 H1) as [m1 [m2 [? [? ?]]]].
  exists m1, m2.
  split; [| split]; auto.
  + apply (H n1); auto.
  + apply (H0 n2); auto.
Qed.
