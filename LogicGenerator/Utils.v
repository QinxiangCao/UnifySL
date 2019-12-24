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

Ltac map_fst_tac x :=
  match x with
  | nil => constr:(@nil Name)
  | cons (BuildName (pair ?A ?B)) ?y =>
    let res := map_fst_tac y in
    constr:(cons (BuildName A) res)
  end.

Notation "'map_fst' l" := ltac:(let l' := eval hnf in l in
                                let x := map_fst_tac l' in exact x) (at level 99).
    
Ltac inj_with_hint_tac x l1 l2 :=
  match l1 with
  | cons x _ =>
    match l2 with
    | cons ?a _ => a
    | _ => fail 1000 "inj_with_hint fails since two arguments are not with the same length, or l2 is not fully computed." x l1 l2
    end
  | cons _ ?l1' =>
    match l2 with
    | cons _ ?l2' => inj_with_hint_tac x l1' l2'
    | _ => fail 2 "inj_with_hint fails since two arguments are not with the same length, or l2 is not fully computed." x l1 l2
    end
  | nil => fail 1 "inj_with_hint fails since it finds nothing" x
  | _ => fail 1000 "inj_with_hint fails since l1 is not fully computed."
  end.

(* Suppose the return value should has type (list Name) *)
Ltac map_with_hint_tac l1 l2 l :=
  match l with
  | nil => constr:(@nil Name)
  | cons ?x ?l0 => let a := inj_with_hint_tac x l1 l2 in
                   let l' := map_with_hint_tac l1 l2 l0 in
                   constr:(cons a l')
  end.

Notation "'map_with_hint' '(' l1 ',' l2 ')' l" :=
  ltac:(let l1' := eval hnf in l1 in
        let l2' := eval hnf in l2 in
        let l' := eval compute in l in
        let res := map_with_hint_tac l1' l2' l' in
        exact res)
  (at level 99).

