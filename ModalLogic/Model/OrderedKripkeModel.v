Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.ModalLogic.Model.KripkeModel.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Class UpwardsClosedOrderedKripkeModel (worlds: Type) {R1: KI.Relation worlds} {R2: KM.Relation worlds} := {
  KM_relation_up: forall m m' n', m <= m' -> KM.Krelation m' n' -> exists n, n <= n' /\ KM.Krelation m n
}.
