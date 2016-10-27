Require Import Logic.LogicBase.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Relations.Relation_Operators.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.

Inductive propag_reduce {L: Language} (atomic_reduce: expr -> expr -> Prop): expr -> expr -> Prop :=
  propag_reduce_spec: forall x y p, atomic_reduce x y ->
    propag_reduce atomic_reduce (propagation_denote p x) (propagation_denote p y).

Class SyntacticReduction (L: Language) : Type := {
  atomic_reduce: expr -> expr -> Prop;
  single_step_reduce := propag_reduce atomic_reduce;
  reduce := clos_refl_trans _ single_step_reduce
(*
  normal_form: expr -> Prop;
  normal_form_spec1: forall x, normal_form x <-> ~ exists y, single_step_reduce x y;
  reduce_function: expr -> expr;
  reduce_function_sound: forall x, reduce x (reduce_function x);
  reduce_function_normal: forall x, normal_form (reduce_function x);
  atomic_reduce_preserve_reduce_function:
    forall x y, atomic_reduce x y -> reduce_function x = reduce_function y;
  single_propagation_preserve_reduce_function:
    forall x y sp, reduce_function x = reduce_function y ->
      reduce_function (single_propagation_denote sp x) = reduce_function (single_propagation_denote sp y)
*)
}.

(*
Lemma single_step_reduce_preserve_reduce_function {L: Language} {SD: SyntacticReduction L}:
  forall x y, single_step_reduce x y -> reduce_function x = reduce_function y.
Proof.
  intros.
  destruct H.
  induction p; simpl.
  + apply atomic_reduce_preserve_reduce_function; auto.
  + apply single_propagation_preserve_reduce_function; auto.
Qed.

Lemma reduce_preserve_reduce_function {L: Language} {SD: SyntacticReduction L}:
  forall x y, reduce x y -> reduce_function x = reduce_function y.
Proof.
  intros.
  induction H.
  + apply single_step_reduce_preserve_reduce_function; auto.
  + reflexivity.
  + etransitivity; eauto.
Qed.

Lemma normal_form_spec2 {L: Language} {SD: SyntacticReduction L}:
  forall x, normal_form x <-> reduce_function x = x.
Proof.
  intros.
  split; intros.
  + pose proof reduce_function_sound x.
    rewrite normal_form_spec1 in H.
    remember (reduce_function x) as y; clear Heqy.
    induction H0.
    - exfalso.
      apply H; exists y; auto.
    - auto.
    - specialize (IHclos_refl_trans1 H).
      subst y.
      specialize (IHclos_refl_trans2 H).
      auto.
  + rewrite <- H; apply reduce_function_normal.
Qed.

Lemma reduce_unique {L: Language} {SD: SyntacticReduction L}:
  forall x y, normal_form y -> reduce x y -> reduce_function x = y.
Proof.
  intros.
  apply reduce_preserve_reduce_function in H0.
  apply normal_form_spec2 in H.
  congruence.
Qed.

*)