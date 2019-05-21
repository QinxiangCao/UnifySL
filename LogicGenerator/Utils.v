Open Scope list_scope.

Tactic Notation "when" constr(b) ":" tactic3(t) :=
  match b with
  | true => t
  | false => idtac
  end.

Inductive Name := BuildName T (x : T).
Arguments BuildName [T].

Module NameListNotations.
Notation "[ ]" := nil.
Notation "[ x ]" := (cons (BuildName x) nil).
Notation "[ x ; y ; .. ; z ]" :=
  (cons (BuildName x) (cons (BuildName y) .. (cons (BuildName z) nil) ..)).
End NameListNotations.

Tactic Notation "dolist" tactic0(f) constr(names) :=
  let rec dolist' ns :=
      match ns with
      | nil => idtac
      | ?x :: ?ns' => f x; dolist' ns'
      end
  in dolist' ltac:(eval red in names).
