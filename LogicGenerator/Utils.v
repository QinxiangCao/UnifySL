Open Scope list_scope.

Tactic Notation "when" constr(b) ":" tactic3(t) :=
  match b with
  | true => t
  | false => idtac
  end.

Inductive Name := BuildName T (x : T).
Arguments BuildName [T].

Ltac dolist f names :=
  let rec dolist' ns :=
      match ns with
      | nil => idtac
      | ?x :: ?ns' => f x; dolist' ns'
      end
  in dolist' ltac:(eval red in names).
