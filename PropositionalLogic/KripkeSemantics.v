Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.

Module KripkeSemantics.

Import PropositionalLanguage.

Record frame: Type := {
  frame_type: Type;
  frame_order: relation frame_type; (* <= *)
  frame_preorder: PreOrder frame_order;
  frame_partialorder: PartialOrder eq frame_order
}.

Infix "<=" := (frame_order _): KripkeSemantics.

Local Open Scope KripkeSemantics.

Definition sem (f: frame) := sig (fun s: Ensemble (frame_type f) => forall x y, x <= y -> s y -> s x).

Program Definition sem_and {f: frame} (X: sem f) (Y: sem f): sem f :=
  fun x: frame_type f => X x /\ Y x.
Next Obligation.
  split.
  + eapply (proj2_sig X); eauto.
  + eapply (proj2_sig Y); eauto.
Qed.

Program Definition sem_or {f: frame} (X: sem f) (Y: sem f): sem f :=
  fun x: frame_type f => X x \/ Y x.
Next Obligation.
  destruct H0; [left | right].
  + eapply (proj2_sig X); eauto.
  + eapply (proj2_sig Y); eauto.
Qed.

Program Definition sem_imp {f: frame} (X: sem f) (Y: sem f): sem f :=
  fun x: frame_type f =>
    forall y: frame_type f, y <= x -> X y -> Y y.
Next Obligation.
  revert H2; apply H0.
  pose proof @PreOrder_Transitive _ _ (frame_preorder f).
  transitivity x; auto.
Qed.

Program Definition sem_true {f: frame}: sem f :=
  fun x: frame_type f => True.

Program Definition sem_false {f: frame}: sem f :=
  fun x: frame_type f => False.

Definition sem_neg {f: frame} (X: sem f): sem f :=
  sem_imp X sem_false.

Definition sem_iff {f: frame} (X: sem f) (Y: sem f): sem f :=
  sem_and (sem_imp X Y) (sem_imp Y X).

Definition denotation {Var: Type} (f: frame) (eval: Var -> sem f): expr Var -> sem f :=
  fix denotation (x: expr Var): sem f:=
  match x with
  | andp y z => sem_and (denotation y) (denotation z)
  | orp y z => sem_or (denotation y) (denotation z)
  | impp y z => sem_imp (denotation y) (denotation z)
  | iffp y z => sem_iff (denotation y) (denotation z)
  | negp y => sem_neg (denotation y)
  | truep => sem_true
  | falsep => sem_false
  | varp p => eval p
  end.

Record model {Var: Type} : Type := {
  model_frame: frame;
  model_var: Var -> sem model_frame;
  elm: frame_type model_frame
}.

Implicit Arguments model.

Instance SM (Var: Type): Semantics (PropositionalLanguage.L Var) :=
  Build_Semantics (PropositionalLanguage.L Var) (model Var) (fun m x => proj1_sig (denotation (model_frame m) (model_var m) x) (elm m)).

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Lemma ImpAndOrAsPrime_consistent {Var: Type}:
  forall x y: expr Var,
    @ImpAndOrAsPrime.atomic_reduce (L Var) (nL Var) (pL Var) x y ->
    forall f eval v, proj1_sig (denotation f eval x) v <-> proj1_sig (denotation f eval y) v.
Proof.
  intros; split; intros; destruct H; auto.
Qed.

Lemma ReduceIff_consistent {Var: Type}:
  forall x y: expr Var,
    @ReduceIff.atomic_reduce (L Var) (nL Var) (pL Var) x y ->
    forall f eval v, proj1_sig (denotation f eval x) v <-> proj1_sig (denotation f eval y) v.
Proof.
  intros; split; intros; destruct H; auto.
Qed.

Lemma ReduceTrue_consistent {Var: Type}:
  forall x y: expr Var,
    @ReduceTrue.atomic_reduce (L Var) (nL Var) (pL Var) x y ->
    forall f eval v, proj1_sig (denotation f eval x) v <-> proj1_sig (denotation f eval y) v.
Proof.
  intros; split; intros; destruct H.
  + hnf; intros; auto.
  + hnf; auto.
Qed.

Lemma disjunction_reduce_consistent {Var: Type}:
  forall reduce1 reduce2: relation (expr Var),
    (forall x y, reduce1 x y -> forall f eval v, proj1_sig (denotation f eval x) v <-> proj1_sig (denotation f eval y) v) ->
    (forall x y, reduce2 x y -> forall f eval v, proj1_sig (denotation f eval x) v <-> proj1_sig (denotation f eval y) v) ->
    forall x y, relation_disjunction reduce1 reduce2 x y ->
    forall f eval v, proj1_sig (denotation f eval x) v <-> proj1_sig (denotation f eval y) v.
Proof.
  intros.
  destruct H1.
  + apply H; auto.
  + apply H0; auto.
Qed.

Lemma propag_reduce_consistent {Var: Type}:
  forall reduce: relation (expr Var),
    (forall x y, reduce x y -> forall f eval v, proj1_sig (denotation f eval x) v <-> proj1_sig (denotation f eval y) v) ->
    (forall x y, @propag_reduce (L Var) reduce x y -> forall f eval v, proj1_sig (denotation f eval x) v <-> proj1_sig (denotation f eval y) v).
Proof.
  intros.
  destruct H0.
  revert v; induction p as [| [| | | | | | | |]]; intros.
  + simpl; apply H; auto.
  + specialize (IHp v).
    simpl in *.
    tauto.
  + specialize (IHp v).
    simpl in *.
    tauto.
  + specialize (IHp v).
    simpl in *.
    tauto.
  + specialize (IHp v).
    simpl in *.
    tauto.
  + simpl in *.
    split; intros HH u Hu; specialize (HH u Hu); specialize (IHp u); tauto.
  + simpl in *.
    split; intros HH u Hu; specialize (HH u Hu); specialize (IHp u); tauto.
  + simpl in *.
    apply Morphisms_Prop.and_iff_morphism.
    - simpl in *.
      split; intros HH u Hu; specialize (HH u Hu); specialize (IHp u); tauto.
    - simpl in *.
      split; intros HH u Hu; specialize (HH u Hu); specialize (IHp u); tauto.
  + simpl in *.
    apply Morphisms_Prop.and_iff_morphism.
    - simpl in *.
      split; intros HH u Hu; specialize (HH u Hu); specialize (IHp u); tauto.
    - simpl in *.
      split; intros HH u Hu; specialize (HH u Hu); specialize (IHp u); tauto.
  + simpl in *.
    split; intros HH u Hu; specialize (HH u Hu); specialize (IHp u); tauto.
Qed.

Lemma intuitionistic_consistent {Var: Type}: reduction_consistent_semantics IntuitionisticReduction (SM Var).
Proof.
  apply reduction_consistent_semantics_spec.
  simpl.
  intros.
  destruct m as [f eval v]; simpl.
  revert x y H f eval v; apply propag_reduce_consistent.
  repeat apply disjunction_reduce_consistent.
  + apply ImpAndOrAsPrime_consistent.
  + apply ReduceIff_consistent.
  + apply ReduceTrue_consistent.
Qed.

End KripkeSemantics.

