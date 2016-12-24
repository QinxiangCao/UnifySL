Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.

Inductive MetaState (state: Type): Type :=
  | Error: MetaState state
  | NonTerminating: MetaState state
  | Terminating: state -> MetaState state.

Arguments Error {_}.
Arguments NonTerminating {_}.
Arguments Terminating {_} _.

Inductive lift_relation {state: Type} (R: state -> MetaState state -> Prop):
  MetaState state-> MetaState state -> Prop :=
| lift_relation_Error:
    lift_relation R Error Error
| lift_relation_NonTerminating:
    lift_relation R NonTerminating NonTerminating
| lift_relation_Terminating:
    forall s ms, R s ms -> lift_relation R (Terminating s) ms.

Inductive lift_Korder
          {state: Type}
          {ki_state: KripkeIntuitionisticModel state}:
  MetaState state -> MetaState state -> Prop :=
| lift_Korder_Error:
    lift_Korder Error Error
| lift_Korder_NonTerminating:
    lift_Korder NonTerminating NonTerminating
| lift_Korder_Terminating:
    forall x y, Korder x y -> lift_Korder (Terminating x) (Terminating y).

Inductive lift_join
          {state: Type}
          {J_state: Join state}:
  MetaState state -> MetaState state -> MetaState state -> Prop :=
| lift_join_Error1:
    forall mx my, lift_join Error mx my
| lift_join_Error2:
    forall mx my, lift_join mx Error my
| lift_join_NonTerminating1:
    forall x, lift_join NonTerminating (Terminating x) NonTerminating
| lift_join_NonTerminating2:
    forall x, lift_join (Terminating x) NonTerminating NonTerminating
| lift_join_NonTerminating3:
    lift_join NonTerminating NonTerminating NonTerminating
| lift_join_Terminating:
    forall x y z,
      join x y z ->
      lift_join (Terminating x) (Terminating y) (Terminating z).

Definition lift_function {A B: Type} (f: A -> B): MetaState A -> MetaState B :=
  fun ma =>
  match ma with
  | NonTerminating => NonTerminating
  | Error => Error
  | Terminating a => Terminating (f a)
  end.


(*
Instance MetaState_SA (state: Type) {SA: SeparationAlgebra state}: SeparationAlgebra (MetaState state).
*)

