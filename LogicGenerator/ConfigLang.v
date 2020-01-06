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

Inductive rule_class :=
| provability_OF_impp
| provability_OF_propositional_connectives
| provability_OF_de_morgan
| provability_OF_godel_dummett
| provability_OF_classical_logic
| provability_OF_sepcon_rule
| provability_OF_wand_rule
| provability_OF_emp_rule
| provability_OF_sepcon_orp_rule
| provability_OF_sepcon_falsep_rule
| provability_OF_sepcon_rule_AS_weak
| provability_OF_sepcon_rule_AS_weak_iffp
| provability_OF_sepcon_rule_AS_mono
| provability_OF_emp_rule_AS_iffp
| provability_OF_garbage_collected_sl
| derivitive_OF_basic_setting
| derivitive_OF_finite_derivation
| derivitive_OF_impp
| derivitive_OF_propositional_connectives
| derivitive_OF_de_morgan
| derivitive_OF_godel_dummett
| derivitive_OF_classical_logic
| GEN_derivable_FROM_provable
| GEN_provable_FROM_derivable
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

Inductive type_class :=
| Language
.

Inductive connective_class :=
| MinimumLanguage
| PropositionalLanguage
| SepconLanguage
| WandLanguage
| EmpLanguage
.

Inductive judgement_class :=
| Provable
| Derivable
.

Inductive any_class :=
| TC (tc: type_class)
| CC (cc: connective_class)
| JC (jc: judgement_class)
| RC (rc: rule_class)
.

Definition how_instance: Type := nat.

Definition primary_rule: Type := nat.

Definition derived_rule: Type := nat.

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
  primitive_classes: list any_class;
  refl_classes_for_derivation: list any_class;
  derived_classes: list how_instance;
  primary_rules: list primary_rule;
  derived_rules: list derived_rule;
  derived_rules_as_instance: list derived_rule
}.
End Output.

(** ** Auxiliary functions *)

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

  Axiom eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).

End DecTypeSig.

Module ListFunOverDecType (DTS: DecTypeSig).
Import DTS.
  
Definition shrink (l: list t): list t :=
  fold_right (fun x l => if (existsb (eqb x) l) then l else x :: l) [] l.

Definition set_minus (l1 l2: list t): list t :=
  filter (fun x => negb (existsb (eqb x) l2)) l1.

Definition set_minus1 (l: list t) (x: t): list t :=
  filter (fun x0 => negb (eqb x0 x)) l.

Definition test_element (x: t) (l: list t): bool :=
  existsb (eqb x) l.

Fixpoint test_no_dup (l: list t): bool :=
  match l with
  | nil => true
  | x :: l0 => negb (test_element x l0) && test_no_dup l0
  end.

Definition test_sublist (l1 l2: list t): bool :=
  forallb (fun x => test_element x l2) l1.

Fixpoint inv_with_hint {A: Type} (f: A -> t) (hint: list A) (x: t): option A :=
  match hint with
  | nil => None
  | a :: hint0 => if eqb x (f a) then Some a else inv_with_hint f hint0 x
  end.

Definition map_inv_with_hint {A: Type}
           (f: A -> t) (hint: list A) (l: list t): list A :=
  valid_sublist (map (inv_with_hint f hint) l).

Fixpoint inj_with_hint {A: Type} (l1: list t) (l2: list A) (x: t) :=
  match l1, l2 with
  | cons a l1', cons v l2' =>
    if eqb a x then Some v else inj_with_hint l1' l2' x
  | _, _ => None
  end.

Definition map_with_hint {A: Type} (l1: list t) (l2: list A) (l: list t) :=
  valid_sublist (map (inj_with_hint l1 l2) l).

Section topo_sort.

Fixpoint pick_one {A: Type} (cur: list (list t * t * A)): option (t * A) :=
  match cur with
  | nil => None
  | (nil, x, a) :: _ => Some (x, a)
  | _ :: cur0 => pick_one cur0
  end.

Definition reduce_one {A: Type}
           (cur: list (list t * t * A)) (x: t): list (list t * t * A) :=
  filter
    (fun d => negb (eqb x (snd (fst d))))
    (map (fun d => (set_minus1 (fst (fst d)) x, snd (fst d), snd d)) cur).

Fixpoint topo_sort_rec {A: Type}
         (cur: list (list t * t * A)) (res: list A) (n: nat): list A :=
  match n with
  | O => res
  | S n0 => let ox := pick_one cur in
            match ox with
            | None => res
            | Some (x, a) => let cur0 := reduce_one cur x in
                             topo_sort_rec cur0 (a :: res) n0
            end
  end.

Definition topo_sort {A: Type} (diag: list (list t * t * A)) :=
  let res := topo_sort_rec diag nil (length diag) in
  rev res.

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

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
Qed.

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

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
  pose proof CType.eqb_spec t0 t1.
  destruct (CType.eqb t0 t1).
  + inversion H; constructor.
    subst; auto.
  + inversion H; constructor.
    congruence.
Qed.

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

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
Qed.

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

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
Qed.

End Judgement.

Module JudgementList := ListFunOverDecType Judgement.

Module CTypeClass.

Definition t := type_class.

Definition eqb (tc1 tc2: type_class) :=
match tc1, tc2 with
| Language, Language => true
end.

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
Qed.

End CTypeClass.

Module CTypeClassList := ListFunOverDecType CTypeClass.

Module ConnectiveClass.

Definition t := connective_class.

Definition eqb (cc1 cc2: connective_class) :=
match cc1, cc2 with
| MinimumLanguage, MinimumLanguage => true
| PropositionalLanguage, PropositionalLanguage => true
| SepconLanguage, SepconLanguage => true
| WandLanguage, WandLanguage => true
| EmpLanguage, EmpLanguage => true
| _, _ => false
end.

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
Qed.

End ConnectiveClass.

Module ConnectiveClassList := ListFunOverDecType ConnectiveClass.

Module JudgementClass.

Definition t := judgement_class.

Definition eqb (jc1 jc2: judgement_class) :=
match jc1, jc2 with
| Provable, Provable => true
| Derivable, Derivable => true
| _, _ => false
end.

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
Qed.

End JudgementClass.

Module JudgementClassList := ListFunOverDecType JudgementClass.

Module RuleClass.

Definition t := rule_class.

Definition eqb (rc1 rc2: rule_class) :=
match rc1, rc2 with
| provability_OF_impp, provability_OF_impp => true
| provability_OF_propositional_connectives, provability_OF_propositional_connectives => true
| provability_OF_de_morgan, provability_OF_de_morgan => true
| provability_OF_godel_dummett, provability_OF_godel_dummett => true
| provability_OF_classical_logic, provability_OF_classical_logic => true
| provability_OF_sepcon_rule, provability_OF_sepcon_rule => true
| provability_OF_wand_rule, provability_OF_wand_rule => true
| provability_OF_emp_rule, provability_OF_emp_rule => true
| provability_OF_sepcon_orp_rule, provability_OF_sepcon_orp_rule => true
| provability_OF_sepcon_falsep_rule, provability_OF_sepcon_falsep_rule => true
| provability_OF_sepcon_rule_AS_weak, provability_OF_sepcon_rule_AS_weak => true
| provability_OF_sepcon_rule_AS_weak_iffp, provability_OF_sepcon_rule_AS_weak_iffp => true
| provability_OF_sepcon_rule_AS_mono, provability_OF_sepcon_rule_AS_mono => true
| provability_OF_emp_rule_AS_iffp, provability_OF_emp_rule_AS_iffp => true
| provability_OF_garbage_collected_sl, provability_OF_garbage_collected_sl => true
| derivitive_OF_basic_setting, derivitive_OF_basic_setting => true
| derivitive_OF_finite_derivation, derivitive_OF_finite_derivation => true
| derivitive_OF_impp, derivitive_OF_impp => true
| derivitive_OF_propositional_connectives, derivitive_OF_propositional_connectives => true
| derivitive_OF_de_morgan, derivitive_OF_de_morgan => true
| derivitive_OF_godel_dummett, derivitive_OF_godel_dummett => true
| derivitive_OF_classical_logic, derivitive_OF_classical_logic => true
| GEN_derivable_FROM_provable, GEN_derivable_FROM_provable => true
| GEN_provable_FROM_derivable, GEN_provable_FROM_derivable => true
| _, _ => false
end.

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
Qed.

End RuleClass.

Module RuleClassList := ListFunOverDecType RuleClass.

Module AllClass.

Definition t := any_class.

Definition eqb (ac1 ac2: any_class) :=
match ac1, ac2 with
| TC tc1, TC tc2 => CTypeClass.eqb tc1 tc2
| CC cc1, CC cc2 => ConnectiveClass.eqb cc1 cc2
| JC jc1, JC jc2 => JudgementClass.eqb jc1 jc2
| RC rc1, RC rc2 => RuleClass.eqb rc1 rc2
| _, _ => false
end.

Lemma eqb_spec: forall x y, Bool.reflect (x = y) (eqb x y).
Proof.
  intros.
  destruct x, y; simpl;
    try constructor; try solve [auto | congruence].
  + pose proof CTypeClass.eqb_spec tc tc0.
    destruct (CTypeClass.eqb tc tc0); inversion H; constructor; congruence.
  + pose proof ConnectiveClass.eqb_spec cc cc0.
    destruct (ConnectiveClass.eqb cc cc0); inversion H; constructor; congruence.
  + pose proof JudgementClass.eqb_spec jc jc0.
    destruct (JudgementClass.eqb jc jc0); inversion H; constructor; congruence.
  + pose proof RuleClass.eqb_spec rc rc0.
    destruct (RuleClass.eqb rc rc0); inversion H; constructor; congruence.
Qed.

End AllClass.

Module AllClassList := ListFunOverDecType AllClass.

Module NatList := ListFunOverDecType PeanoNat.Nat.
