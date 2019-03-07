Ltac when b t :=
  match b with
  | true => t
  | false => idtac
  end.

Inductive Name := BuildName T (x : T).
Arguments BuildName [T].