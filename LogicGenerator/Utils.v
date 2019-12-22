Open Scope list_scope.

Tactic Notation "when" constr(b) ":" tactic3(t) :=
  match b with
  | true => t
  | false => idtac
  end.

Inductive Name := BuildName T (x : T).
Arguments BuildName [T].

Module NameListNotations.
Notation "[ ]" := (@nil Name).
Notation "[ x ]" := (cons (BuildName x) nil).
Notation "[ x ; y ; .. ; z ]" :=
  (cons (BuildName x) (cons (BuildName y) .. (cons (BuildName z) nil) ..)).
End NameListNotations.

Ltac in_name_list n l :=
  match l with
  | nil => constr:(false)
  | cons (BuildName n) _ => constr:(true)
  | cons _ ?l' => in_name_list n l'
  end.
  
Tactic Notation "dolist" tactic0(f) constr(names) :=
  let rec dolist' ns :=
      match ns with
      | nil => idtac
      | ?x :: ?ns' => f x; dolist' ns'
      end
  in dolist' ltac:(eval hnf in names).

Local Ltac print_when f p :=
  match p with
  | (?b, ?names) => when b: dolist f names
  end.

Tactic Notation "dolist_when" tactic0(f) constr(tbl) :=
  dolist (print_when f) tbl.

Ltac remove_arg x :=
  match x with
  | ?y ?z => remove_arg y
  | _ => x
  end.

