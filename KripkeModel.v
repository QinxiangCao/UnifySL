Record KripkeModel (X: Type): Type := {
  Kworlds: X -> Type;
  Krelation: forall (x: X), Kworlds x -> Kworlds x -> Prop
}.

Record KripkeModel2 (X: Type): Type := {
  K2worlds: X -> Type;
  K2relation: forall (x: X), K2worlds x -> K2worlds x -> K2worlds x -> Prop
}.

Definition n_relation (A: Type): nat -> Type :=
  fix n_relation (n: nat): Type :=
    match n with
    | O => Prop
    | S n0 => A -> n_relation n0
    end.

Record GeneralKripkeModel (n: nat) (X: Type): Type := {
  GKworlds: X -> Type;
  GKrelation: forall (x: X), n_relation (GKworlds x) n
}.

