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
| emp
| multi_imp
| empty_context.

Inductive judgement :=
| provable
| derivable
| corable.

Inductive type :=
| prog_state
| expr
| context.

Inductive parameter :=
| CP (c: connective)
| JP (j: judgement)
| TP (t: type).

Coercion CP: connective >-> parameter.
Coercion JP: judgement >-> parameter.
Coercion TP: type >-> parameter.

Inductive how_connective :=
| primitive_connective (c: connective)
| ___predicate_over_states (mono: bool) (c: connective)
| FROM_andp_impp_TO_iffp
| FROM_falsep_impp_TO_negp
| FROM_falsep_impp_TO_truep
| FROM_impp_TO_multi_imp
| FROM_empty_set_TO_empty_context.

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

Inductive rule_classes :=
| provability_OF_impp
| provability_OF_propositional_connectives
| provability_OF_de_morgan
| provability_OF_godel_dummett
| provability_OF_classical_logic
| provability_OF_separation_logic
| provability_OF_emp_rule
| provability_OF_garbage_collected_sl
| derivitive_OF_impp
| derivitive_OF_propositional_connectives
| derivitive_OF_finite_derivation
| derivitive_OF_de_morgan
| derivitive_OF_godel_dummett
| derivitive_OF_classical_logic
| GEN_derivable_FROM_provable
| GEN_provable_FROM_derivable
.

Inductive optional_proof_rule :=
| de_morgan
| godel_dummett
| classical
| garbage_collected_sl
.

Inductive type_classes :=
| Language
.

Inductive connective_classes :=
| MinimumLanguage
| PropositionalLanguage
| SeparationLanguage
| EmpSeparationLanguage
.

Inductive judgement_classes :=
| Provable
| Derivable
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

(** ** Output *)

Module Output.
Record output: Type := {
  primitive_types: list type;
  transparent_types: list type;
  derived_types: list how_type;
  primitive_connectives: list connective;
  transparent_connectives: list connective;
  derived_connectives: list how_connective;
  primitive_judgements: list judgement;
  transparent_judgements: list judgement;
  derived_judgements: list how_judgement;
                           
}.
End Output.
                  
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
| FROM_impp_TO_multi_imp => []
| FROM_empty_set_TO_empty_context => [FROM_ensemble_expr_TO_context]
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
| FROM_impp_TO_multi_imp => multi_imp
| FROM_empty_set_TO_empty_context => empty_context
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
| emp
| multi_imp => [expr]
| empty_context => [context]
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
| FROM_impp_TO_multi_imp => [impp]
| FROM_empty_set_TO_empty_context => []
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

(* depended connectives of proof-theories *)
Definition DCOP (p: optional_proof_rule): list connective :=
match p with
| de_morgan => [negp; orp]
| godel_dummett => [impp; orp]
| classical => [negp; orp]
| garbage_collected_sl => [sepcon]
end.

(** ** Checking functions **)

Definition force_val_list {T: Type} (ol: option (list T)): list T :=
  match ol with
  | Some l => l
  | None => nil
  end.

Definition is_Some {T: Type} (o: option T): bool :=
  match o with
  | Some _ => true
  | _ => false
  end.

Definition is_nil {T: Type} (l: list T): bool :=
  match l with
  | nil => true
  | _ => false
  end.

Fixpoint valid_sublist {T: Type} (ol: list (option T)): list T :=
  match ol with
  | nil => nil
  | (Some x) :: ol0 => x :: valid_sublist ol0
  | None :: ol0 => valid_sublist ol0
  end.

(* TODO Check Standard Library *)
Module Type DecTypeSig.

  Parameter Inline t: Type.

  Parameter eqb: t -> t -> bool.

End DecTypeSig.

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

Definition test_sublist (l1 l2: list t): bool :=
  forallb (fun x => existsb (eqb x) l2) l1.

Fixpoint inv_with_hint {A: Type} (f: A -> t) (hint: list A) (x: t): option A :=
  match hint with
  | nil => None
  | a :: hint0 => if eqb x (f a) then Some a else inv_with_hint f hint0 x
  end.

Definition map_inv_with_hint {A: Type}
           (f: A -> t) (hint: list A) (l: list t): list A :=
  valid_sublist (map (inv_with_hint f hint) l).

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
| emp, emp
| multi_imp, multi_imp
| empty_context, empty_context => true
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

Definition parameter2type (p: parameter) :=
  match p with
  | TP t => Some t
  | _ => None
  end.

Definition parameter2connective (p: parameter) :=
  match p with
  | CP c => Some c
  | _ => None
  end.

Definition parameter2judgement (p: parameter) :=
  match p with
  | JP j => Some j
  | _ => None
  end.

Definition pick_types (p : list parameter): list type :=
  valid_sublist (map parameter2type p).

Definition pick_connectives (p : list parameter): list connective :=
  valid_sublist (map parameter2connective p).

Definition pick_judgements (p : list parameter): list judgement :=
  valid_sublist (map parameter2judgement p).

Definition is_primitive_type (ht: how_type): option type :=
  match ht with
  | primitive_type t => Some t
  | _ => None
  end.

Definition is_primitive_connective (hc: how_connective): option connective :=
  match hc with
  | primitive_connective c => Some c
  | _ => None
  end.

Definition is_primitive_judgement (hj: how_judgement): option judgement :=
  match hj with
  | primitive_judgement j => Some j
  | _ => None
  end.

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

Let ts_diag :=
  map (fun ht => (DTOT ht, GenT ht)) hts.

Let cs_diag :=
  map (fun hc => (DCOC hc, GenC hc)) hcs.

Let js_diag :=
  map (fun hj => (DJOJ hj, GenJ hj)) hjs.

Let primitive_ts :=
  valid_sublist (map is_primitive_type hts).

Let primitive_cs :=
  valid_sublist (map is_primitive_connective hcs).

Let primitive_js :=
  valid_sublist (map is_primitive_judgement hjs).

Let ts_order :=
  CTypeList.topo_sort ts_diag.

Let cs_order :=
  ConnectiveList.topo_sort cs_diag.

Let js_order :=
  JudgementList.topo_sort js_diag.

Let derived_ts :=
  CTypeList.map_inv_with_hint GenT hts
    (CTypeList.set_minus (force_val_list ts_order) primitive_ts).

Let derived_cs :=
  ConnectiveList.map_inv_with_hint GenC hcs
    (ConnectiveList.set_minus (force_val_list cs_order) primitive_cs).

Let derived_js :=
  JudgementList.map_inv_with_hint GenJ hjs
    (JudgementList.set_minus (force_val_list js_order) primitive_js).

Variable transparent_names: list parameter.

Let transparent_ts :=
  pick_types transparent_names.

Let transparent_cs :=
  pick_connectives transparent_names.

Let transparent_js :=
  pick_judgements transparent_names.

Let legal_tt :=
  (CTypeList.test_sublist transparent_ts primitive_ts &&
   CTypeList.test_no_dup transparent_ts)%bool.

Let legal_tc :=
  (ConnectiveList.test_sublist transparent_cs primitive_cs &&
   ConnectiveList.test_no_dup transparent_cs)%bool.

Let legal_tj :=
  (JudgementList.test_sublist transparent_js primitive_js &&
   JudgementList.test_no_dup transparent_js)%bool.

Variable optional_rules: list optional_proof_rule.

Let needed_connective :=
  ConnectiveList.shrink (concat (map DCOP optional_rules)).

Definition test_no_dup_defs := (hcs_no_dup && hjs_no_dup)%bool.
Definition test_type_defs_consistent := feasible.
Definition how_types_define := hts.
Definition test_order_loop :=
  (is_Some ts_order && is_Some cs_order && is_Some js_order)%bool.
Definition test_legal_transp_names := (legal_tt && legal_tc && legal_tj)%bool.
Definition test_legal_rules := ConnectiveList.test_sublist needed_connective cs.

Definition result: Output.output :=
  Output.Build_output
    primitive_ts
    transparent_ts
    derived_ts
    primitive_cs
    transparent_cs
    derived_cs
    primitive_js
    transparent_js
    derived_js
    .
Definition __cs := cs_order.
Definition __cs_diag := cs_diag.    
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
  ;FROM_impp_TO_multi_imp
  ].

Definition how_judgements :=
  [primitive_judgement provable
  ;FROM_provable_TO_derivable
  ].

Definition transparent_names :=
  [expr:parameter].

Eval compute in (test_no_dup_defs how_connectives how_judgements).
Eval compute in (test_type_defs_consistent how_connectives how_judgements).
Eval compute in (test_order_loop how_connectives how_judgements).
Eval compute in (how_types_define how_connectives how_judgements).
Eval compute in (result how_connectives how_judgements transparent_names).

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
  ;FROM_impp_TO_multi_imp
  ].

Definition how_judgements :=
  [primitive_judgement derivable
  ;FROM_derivable_TO_provable
  ].

Definition transparent_names :=
  [expr:parameter; andp:parameter].

Eval compute in (test_no_dup_defs how_connectives how_judgements).
Eval compute in (test_type_defs_consistent how_connectives how_judgements).
Eval compute in (test_order_loop how_connectives how_judgements).
Eval compute in (how_types_define how_connectives how_judgements).
Eval compute in (result how_connectives how_judgements transparent_names).

End test2.

Module test3.

Definition how_connectives :=
  [primitive_connective impp
  ;primitive_connective andp
  ;primitive_connective orp
  ;primitive_connective falsep
  ;primitive_connective sepcon
  ;primitive_connective wand
  ;primitive_connective emp
  ;FROM_andp_impp_TO_iffp
  ;FROM_falsep_impp_TO_negp
  ;FROM_falsep_impp_TO_truep
  ;FROM_impp_TO_multi_imp
  ;FROM_empty_set_TO_empty_context
  ].

Definition how_judgements :=
  [primitive_judgement provable
  ;FROM_provable_TO_derivable
  ].

Definition transparent_names :=
  [expr:parameter].

Eval compute in (test_no_dup_defs how_connectives how_judgements).
Eval compute in (test_type_defs_consistent how_connectives how_judgements).
Eval compute in (test_order_loop how_connectives how_judgements).
Eval compute in (how_types_define how_connectives how_judgements).
Eval compute in (result how_connectives how_judgements transparent_names).

End test3.

(*
Definition primitive_types :=
Definition transparent_types :=
Definition derived_types :=
Definition primitive_connectives :=
Definition transparent_connectives :=
Definition derived_connectives :=
Definition primitive_judgements :=
Definition transparent_judgements :=
Definition derived_judgements :=
Definition primary_rules: list Name :=
Definition derived_rules :=
Definition derived_instances :=
*)
