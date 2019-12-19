Require Import Coq.Lists.List.
Import ListNotations.

(** * What users need to know **)
(** ** Parameters *)

Inductive connective :=
| impp
| andp
| orp
| falsep
| truep
| negp
| iffp
| sepcon
| wand
| multi_impp.

Inductive judgement :=
| provable
| derivable
| corable.

Inductive type :=
| prog_state
| expr
| context.

Inductive how_connective :=
| primitive_connective (c: connective)
| ___predicate_over_states (mono: bool) (c: connective)
| FROM_andp_impp_TO_iffp
| FROM_falsep_impp_TO_negp
| FROM_falsep_impp_TO_truep
| FROM_impp_TO_multi_impp.

Definition primitive_connectives := map primitive_connective.
Definition predicate_over_states := ___predicate_over_states false.
Definition mpredicate_over_states := ___predicate_over_states true.
Definition predicates_over_states := map predicate_over_states.
Definition mpredicates_over_states := map mpredicate_over_states.

Inductive how_judgement :=
| primitive_judgement (j: judgement)
| ___USE_valid_FOR_provable (mono: bool)
| ___USE_consequence_FOR_derivable (mono fin: bool)
| FROM_provable_TO_derivable
| FROM_derivable_TO_provable.

Definition USE_valid_FOR_provable := ___USE_valid_FOR_provable false.
Definition USE_mono_valid_FOR_provable := ___USE_valid_FOR_provable true.
Definition USE_conseq_FOR_derivable :=
  ___USE_consequence_FOR_derivable false false.
Definition USE_mono_conseq_FOR_derivable :=
  ___USE_consequence_FOR_derivable true false.
Definition USE_fin_conseq_FOR_derivable :=
  ___USE_consequence_FOR_derivable false true.
Definition USE_mono_fin_conseq_FOR_derivable :=
  ___USE_consequence_FOR_derivable true true.

Inductive optional_proof_rule :=
| de_morgan
| godel_dummett
| classical
| garbage_collected_sl
.

(** * What users need not to know **)
(** ** Parameters *)

Inductive how_type :=
| primitive_type (t: type)
| FROM_predicate_over_states_TO_expr
| FROM_mpredicate_over_states_TO_expr
| FROM_ensemble_expr_TO_context
.

Notation "'ht_restriction'" := (list how_type).

(** ** Attributes *)

(* infered how-type of how-connective *)
Definition ITOC (hc: how_connective): ht_restriction :=
match hc with
| primitive_connective c => []
| ___predicate_over_states false c => [FROM_predicate_over_states_TO_expr]
| ___predicate_over_states true c => [FROM_mpredicate_over_states_TO_expr]
| FROM_andp_impp_TO_iffp => []
| FROM_falsep_impp_TO_negp => []
| FROM_falsep_impp_TO_truep => []
| FROM_impp_TO_multi_impp => []
end.

(* infered how-type of how-judgement *)
Definition ITOJ (hj: how_judgement): ht_restriction :=
match hj with
| primitive_judgement j =>
    match j with
    | derivable => [FROM_ensemble_expr_TO_context]
    | _ => []
    end
| ___USE_valid_FOR_provable false => [FROM_predicate_over_states_TO_expr]
| ___USE_valid_FOR_provable true => [FROM_mpredicate_over_states_TO_expr]
| ___USE_consequence_FOR_derivable false _ => [FROM_predicate_over_states_TO_expr
                                              ;FROM_ensemble_expr_TO_context
                                              ]
| ___USE_consequence_FOR_derivable true _ => [FROM_mpredicate_over_states_TO_expr
                                             ;FROM_ensemble_expr_TO_context
                                             ]
| FROM_provable_TO_derivable => [FROM_ensemble_expr_TO_context]
| FROM_derivable_TO_provable => [FROM_ensemble_expr_TO_context]
end.

(* generated connective *)
Definition GenC (hc: how_connective): connective :=
match hc with
| primitive_connective c => c
| ___predicate_over_states _ c => c
| FROM_andp_impp_TO_iffp => iffp
| FROM_falsep_impp_TO_negp => negp
| FROM_falsep_impp_TO_truep => truep
| FROM_impp_TO_multi_impp => multi_impp
end.

(* generated judgement *)
Definition GenJ (hj: how_judgement): judgement :=
match hj with
| primitive_judgement j => j
| ___USE_valid_FOR_provable _ => provable
| ___USE_consequence_FOR_derivable _ _ => derivable
| FROM_provable_TO_derivable => derivable
| FROM_derivable_TO_provable => provable
end.

(* generated type *)
Definition GenT (ht: how_type): type :=
match ht with
| primitive_type t => t
| FROM_predicate_over_states_TO_expr => expr
| FROM_mpredicate_over_states_TO_expr => expr
| FROM_ensemble_expr_TO_context => context
end.

(* depended types of connectives *)
Definition DTOC (c: connective): list type :=
match c with
| impp
| andp
| orp
| falsep
| truep
| negp
| iffp
| sepcon
| wand
| multi_impp => [expr]
end.

(* depended types of judgements *)
Definition DTOJ (j: judgement): list type :=
match j with
| provable => [expr]
| derivable => [context; expr]
| corable => [expr]
end.

(* dependent connectives of how-connective *)
Definition DCOC (hc: how_connective): list connective :=
match hc with
| primitive_connective c => []
| ___predicate_over_states _ c => []
| FROM_andp_impp_TO_iffp => [andp; impp]
| FROM_falsep_impp_TO_negp => [falsep; impp]
| FROM_falsep_impp_TO_truep => [falsep; impp]
| FROM_impp_TO_multi_impp => [impp]
end.

(* dependent judgements of how-judgement *)
Definition DJOJ (hj: how_judgement): list judgement :=
match hj with
| primitive_judgement j => []
| ___USE_valid_FOR_provable _ => []
| ___USE_consequence_FOR_derivable _ _ => []
| FROM_provable_TO_derivable => [provable]
| FROM_derivable_TO_provable => [derivable]
end.

(* depended types of types *)
Definition DTOT (ht: how_type): list type :=
match ht with
| primitive_type t => []
| FROM_predicate_over_states_TO_expr => [prog_state]
| FROM_mpredicate_over_states_TO_expr => [prog_state]
| FROM_ensemble_expr_TO_context => [expr]
end.

(** ** Checking functions **)

(* TODO Check Standard Library *)
Module Type DecTypeSig.

  Parameter Inline t: Type.

  Parameter eqb: t -> t -> bool.

End DecTypeSig.

Definition force_val_list {T: Type} (ol: option (list T)): list T :=
  match ol with
  | Some l => l
  | None => nil
  end.

Module ListFunOverDecType (DTS: DecTypeSig).
Import DTS.
  
Definition shrink (l: list t): list t :=
  fold_right (fun x l => if (existsb (eqb x) l) then l else x :: l) [] l.

Definition set_minus (l1 l2: list t): list t :=
  filter (fun x => negb (existsb (eqb x) l2)) l1.

Definition set_minus1 (l: list t) (x: t): list t :=
  filter (fun x0 => negb (eqb x0 x)) l.

Fixpoint test_no_dup (l: list t): bool :=
  match l with
  | nil => true
  | x :: l0 => negb (existsb (eqb x) l0) && test_no_dup l0
  end.

Section topo_sort.

Fixpoint pick_one (cur: list (list t * t)): option t :=
  match cur with
  | nil => None
  | (nil, x) :: _ => Some x
  | _ :: cur0 => pick_one cur0
  end.

Definition reduce_one (cur: list (list t * t)) (x: t): list (list t * t) :=
  filter
    (fun d => negb (eqb x (snd d)))
    (map (fun d => (set_minus1 (fst d) x, snd d)) cur).

Fixpoint topo_sort_rec
         (cur: list (list t * t)) (res: list t) (n: nat): option (list t) :=
  match n with
  | O => Some res
  | S n0 => let ox := pick_one cur in
            match ox with
            | None => None
            | Some x => let cur0 := reduce_one cur x in
                        topo_sort_rec cur0 (x :: res) n0
            end
  end.

Definition topo_sort (diag: list (list t * t)) :=
  let res := topo_sort_rec diag nil (length diag) in
  match res with
  | None => None
  | Some l => Some (rev l)
  end.

End topo_sort.

End ListFunOverDecType.

Module CType <: DecTypeSig.

Definition t := type.

Definition eqb (t1 t2: type) :=
  match t1, t2 with
  | expr, expr => true
  | context, context => true
  | prog_state, prog_state => true
  | _, _ => false
  end.

End CType.

Module CTypeList := ListFunOverDecType CType.

Module HowType <: DecTypeSig.

Definition t := how_type.

Definition eqb (ht1 ht2: how_type) :=
  match ht1, ht2 with
  | primitive_type t1, primitive_type t2 => CType.eqb t1 t2
  | FROM_predicate_over_states_TO_expr, FROM_predicate_over_states_TO_expr => true
  | FROM_mpredicate_over_states_TO_expr, FROM_mpredicate_over_states_TO_expr => true
  | FROM_ensemble_expr_TO_context, FROM_ensemble_expr_TO_context => true
  | _, _ => false
  end.

End HowType.

Module HowTypeList := ListFunOverDecType HowType.

Module Connective <: DecTypeSig.

Definition t := connective.

Definition eqb (c1 c2: connective) :=
match c1, c2 with
| impp, impp
| andp, andp
| orp, orp
| falsep, falsep
| truep, truep
| negp, negp
| iffp, iffp
| sepcon, sepcon
| wand, wand
| multi_impp, multi_impp => true
| _, _ => false
end.

End Connective.

Module ConnectiveList := ListFunOverDecType Connective.

Module Judgement <: DecTypeSig.

Definition t := judgement.

Definition eqb (j1 j2: judgement) :=
match j1, j2 with
| provable, provable
| derivable, derivable
| corable, corable => true
| _, _ => false
end.

End Judgement.

Module JudgementList := ListFunOverDecType Judgement.

Definition ht_restriction_merge (r1 r2: ht_restriction): ht_restriction :=
  r1 ++ r2.

Definition ht_restriction_feasible (r: ht_restriction): bool :=
  Nat.eqb (length (HowTypeList.shrink r)) (length (CTypeList.shrink (map GenT r))).

Section ComputeHT.

Variable hcs: list how_connective.
Variable hjs: list how_judgement.

Let cs := map GenC hcs.

Let js := map GenJ hjs.

Let hcs_no_dup :=
  ConnectiveList.test_no_dup cs.

Let hjs_no_dup :=
  JudgementList.test_no_dup js.

Let inferred_hts :=
  HowTypeList.shrink (concat (map ITOC hcs ++ map ITOJ hjs)).

Let feasible :=
  ht_restriction_feasible inferred_hts.

Let ts :=
  CTypeList.shrink (concat (map DTOC cs ++ map DTOJ js)).

Let hts :=
  inferred_hts ++
  map primitive_type (CTypeList.set_minus ts (map GenT inferred_hts)).

Let ht_diag :=
  map (fun ht => (DTOT ht, GenT ht)) hts.

Let hc_diag :=
  map (fun hc => (DCOC hc, GenC hc)) hcs.

Let hj_diag :=
  map (fun hj => (DJOJ hj, GenJ hj)) hjs.

Let ht_order :=
  CTypeList.topo_sort ht_diag.

Let hc_order :=
  ConnectiveList.topo_sort hc_diag.

Let hj_order :=
  JudgementList.topo_sort hj_diag.

Definition test_no_dup_defs := (hcs_no_dup && hjs_no_dup)%bool.
Definition test_type_defs_consistent := feasible.
Definition how_types_define := hts.
Definition test_order_loop :=
  match ht_order, hc_order, hj_order with
  | Some _, Some _, Some _ => true
  | _, _, _ => false
  end.
Definition type_order := force_val_list ht_order.
Definition connective_order := force_val_list hc_order.
Definition judgement_order := force_val_list hj_order.

End ComputeHT.

Module test1.

Definition how_connectives :=
  [primitive_connective impp
  ;primitive_connective andp
  ;primitive_connective orp
  ;primitive_connective falsep
  ;primitive_connective sepcon
  ;primitive_connective wand
  ;FROM_andp_impp_TO_iffp
  ;FROM_falsep_impp_TO_negp
  ;FROM_falsep_impp_TO_truep
  ;FROM_impp_TO_multi_impp
  ].

Definition how_judgements :=
  [primitive_judgement provable
  ;FROM_provable_TO_derivable
  ].

Eval compute in (test_no_dup_defs how_connectives how_judgements).
Eval compute in (test_type_defs_consistent how_connectives how_judgements).
Eval compute in (test_order_loop how_connectives how_judgements).
Eval compute in (how_types_define how_connectives how_judgements).
Eval compute in (type_order how_connectives how_judgements).
Eval compute in (connective_order how_connectives).
Eval compute in (judgement_order how_judgements).

End test1.

Module test2.

Definition how_connectives :=
  [primitive_connective impp
  ;primitive_connective andp
  ;primitive_connective orp
  ;primitive_connective falsep
  ;primitive_connective sepcon
  ;primitive_connective wand
  ;FROM_andp_impp_TO_iffp
  ;FROM_falsep_impp_TO_negp
  ;FROM_falsep_impp_TO_truep
  ;FROM_impp_TO_multi_impp
  ].

Definition how_judgements :=
  [primitive_judgement derivable
  ;FROM_derivable_TO_provable
  ].

Eval compute in (test_no_dup_defs how_connectives how_judgements).
Eval compute in (test_type_defs_consistent how_connectives how_judgements).
Eval compute in (test_order_loop how_connectives how_judgements).
Eval compute in (how_types_define how_connectives how_judgements).
Eval compute in (type_order how_connectives how_judgements).
Eval compute in (connective_order how_connectives).
Eval compute in (judgement_order how_judgements).

End test2.
