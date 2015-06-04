Require Import IntuitionisticLogic.base.
Require Import IntuitionisticLogic.Wf.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Compare_dec.
Local Open Scope IPC_scope.

Section RelationLib.

Variable A: Type.

Section Intersection.

Variables R1 R2: relation A.

Definition intersection x y := R1 x y /\ R2 x y.

End Intersection.

Section RelationDef.

Variables R eqA: relation A.

Class Total: Prop := {
  totality: forall x y, R x y \/ R y x
}.

Class StrictTotal: Prop := {
  strict_totality: forall x y, R x y \/ x = y \/ R y x
}.

Class StrictTotalViaEquiv: Prop := {
  strict_totality_via_equiv: forall x y, R x y \/ eqA x y \/ R y x
}.

Class Antisymmetric: Prop := {
  antisymmetry: forall x y, R x y -> R y x -> x = y
}.

Class AntisymViaEquiv: Prop := {
  antisymmetry_via_equiv: forall x y, R x y -> R y x -> eqA x y
}.

Class IrreflViaEquiv: Prop := {
  irreflexivity_via_equiv: forall x y, eqA x y -> R x y -> False
}.

Class WeakTotalOrder: Prop := {
  WeakTotalOrder_Reflexive: Reflexive R;
  WeakTotalOrder_Transitive: Transitive R;
  WeakTotalOrder_Total: Total
}.

Class TotalOrder: Prop := {
  TotalOrder_Reflexive: Reflexive R;
  TotalOrder_Antisymmetric: Antisymmetric;
  TotalOrder_Transitive: Transitive R;
  TotalOrder_Total: Total
}.

Class StrictTotalOrder: Prop := {
  StrictTotalOrder_Irreflexive: Irreflexive R;
  StrictTotalOrder_Asymmetric: Asymmetric R;
  StrictTotalOrder_Transitive: Transitive R;
  StrictTotalOrder_StrictTotal: StrictTotal
}.

Class StrictTotalOrderViaEquiv: Prop := {
  StrictTotalOrderViaEquiv_EqIsEquiv: Equivalence eqA;
  StrictTotalOrderViaEquiv_IrreflViaEquiv: IrreflViaEquiv;
  StrictTotalOrderViaEquiv_Asymmetric: Asymmetric R;
  StrictTotalOrderViaEquiv_Transitive: Transitive R;
  StrictTotalOrderViaEquiv_StrictTotal: StrictTotalViaEquiv
}.

Class StrictWellOrder: Prop := {
  StrictWellOrder_StrictTotalOrder: StrictTotalOrder;
  StrictWellOrder_WellFounded: well_founded R
}.

End RelationDef.

Variable R1 R2 eqA1 eqA2: relation A.

Lemma intersection_Reflexive: Reflexive R1 -> Reflexive R2 -> Reflexive (intersection R1 R2).
Proof.
  intros ? ? x.
  split; apply reflexivity.
Qed.

Lemma intersection_Symmetric: Symmetric R1 -> Symmetric R2 -> Symmetric (intersection R1 R2).
Proof.
  intros ? ? x y [? ?].
  split; apply symmetry; auto.
Qed.

Lemma intersection_Transitive: Transitive R1 -> Transitive R2 -> Transitive (intersection R1 R2).
Proof.
  intros ? ? x y z [? ?] [? ?].
  split; eapply transitivity; eauto.
Qed.

Definition StrictBiKey x y := R1 x y \/ (eqA1 x y /\ R2 x y).

Lemma BiKey_StrictTotalOrderViaEquiv:
  StrictTotalOrderViaEquiv R1 eqA1 ->
  StrictTotalOrderViaEquiv R2 eqA2 ->
  StrictTotalOrderViaEquiv StrictBiKey (fun x y => eqA1 x y /\ eqA2 x y).
Proof.
  intros; unfold StrictBiKey.
  constructor.
SearchAbout Equivalence.
  + constructor; intros.
    destruct H2 as [? | [? ?]].
    - apply StrictTotalOrderViaEquiv_IrreflViaEquiv in H.
      pose proof (irreflexivity_via_equiv R1 eqA1 x y).
      tauto.
    - apply StrictTotalOrderViaEquiv_IrreflViaEquiv in H0.
      pose proof (irreflexivity_via_equiv R2 eqA2 x y).
      tauto.
  + intros x y [? | [? ?]] [? | [? ?]].
    - pose proof StrictTotalOrderViaEquiv_Asymmetric R1 eqA1 x y.
      tauto.
    - apply StrictTotalOrderViaEquiv_IrreflViaEquiv in H.
      pose proof (irreflexivity_via_equiv R1 eqA1 x y).
      
Admitted.

Lemma BiKey_StrictTotalOrder:
  StrictTotalOrderViaEquiv R1 eqA1 ->
  StrictTotalOrder R2 ->
  StrictTotalOrder StrictBiKey.
Proof.
Admitted.

Section enumerate.

Variable venv: Var_env.
Variable lt_var: Var -> Var -> Prop.
Hypothesis Wf: well_founded lt_var.
Hypothesis TO: TotalOrder lt_var.

Fixpoint level (e: Term) : nat :=
  match e with
  | andp e1 e2 => max (level e1) (level e2) + 1
  | orp e1 e2 => max (level e1) (level e2) + 1
  | impp e1 e2 => max (level e1) (level e2) + 1
  | falsep => 0
  | varp _ => 0
  end.

Fixpoint trivial_lt (e1 e2: Term): Prop :=
  match e1, e2 with
  | falsep, falsep => False
  | falsep, _ => True
  | _, falsep => False
  | varp v1, varp v2 => lt_var v1 v2
  | varp _, _ => True
  | _, varp _ => False
  | andp e11 e12, andp e21 e22 => trivial_lt e11 e21 \/ (e11 = e21 /\ trivial_lt e12 e22)
  | andp _ _, _ => True
  | _, andp _ _ => False
  | orp e11 e12, orp e21 e22 => trivial_lt e11 e21 \/ (e11 = e21 /\ trivial_lt e12 e22)
  | orp _ _, _ => True
  | _, orp _ _ => False
  | impp e11 e12, impp e21 e22 => trivial_lt e11 e21 \/ (e11 = e21 /\ trivial_lt e12 e22)
  end.

Definition lt_Term (e1 e2: Term): Prop :=
  (level e1 < level e2) \/ (level e1 = level e2 /\ trivial_lt e1 e2).



Definition 
