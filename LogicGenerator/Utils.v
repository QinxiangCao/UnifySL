Ltac when b t :=
  match b with
  | true => t
  | false => idtac
  end.
