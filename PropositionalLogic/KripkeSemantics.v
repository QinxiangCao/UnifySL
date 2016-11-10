Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.
Require Import Logic.KripkeModel.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.
(*
Class KripkeIntuitionisticSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (SM: Semantics L) {rcSM: ReductionConsistentSemantics IntuitionisticReduction SM}: Type := {
  Kripke_model: Type;
  frame_worlds: Kripke_model -> Type;
  frame_relation: forall {m: Kripe_model}, frame_type m -> frame_type m -> Prop;
  build_model: forall m: Kripke_model, frame_type m -> model;
  sem_impp: forall m x y, m |= x --> y <-> (m |= x -> m |= y);
  sem_negp: forall m x, m |= ~~ x <-> ~ m |= x;
  sem_truep: forall m, m |= TT
}.
*)
Module KripkeSemantics.

Import PropositionalLanguage.

Record frame: Type := {
  frame_type: Type;
  frame_order: relation frame_type; (* <= *)
  frame_preorder: PreOrder frame_order
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

Lemma RPC {Var: Type}: ReductionPropagationConsistent (SM Var).
Proof.
  hnf; intros; simpl in *.
  destruct m as [F eval v].
  pose proof (fun v => H (Build_model _ F eval v)).
  revert v; simpl in H0; clear H.
  destruct sp; intros.
  + specialize (H0 v).
    simpl in *.
    tauto.
  + specialize (H0 v).
    simpl in *.
    tauto.
  + specialize (H0 v).
    simpl in *.
    tauto.
  + specialize (H0 v).
    simpl in *.
    tauto.
  + simpl in *.
    split; intros HH u Hu; specialize (HH u Hu); specialize (H0 u); tauto.
  + simpl in *.
    split; intros HH u Hu; specialize (HH u Hu); specialize (H0 u); tauto.
  + simpl in *.
    apply Morphisms_Prop.and_iff_morphism.
    - simpl in *.
      split; intros HH u Hu; specialize (HH u Hu); specialize (H0 u); tauto.
    - simpl in *.
      split; intros HH u Hu; specialize (HH u Hu); specialize (H0 u); tauto.
  + simpl in *.
    apply Morphisms_Prop.and_iff_morphism.
    - simpl in *.
      split; intros HH u Hu; specialize (HH u Hu); specialize (H0 u); tauto.
    - simpl in *.
      split; intros HH u Hu; specialize (HH u Hu); specialize (H0 u); tauto.
  + simpl in *.
    split; intros HH u Hu; specialize (HH u Hu); specialize (H0 u); tauto.
Qed.

Instance rcSM (Var: Type): ReductionConsistentSemantics IntuitionisticReduction (SM Var).
Proof.
  apply Build_ReductionConsistentSemantics.
  + hnf; intros.
    revert x y H m.
    repeat apply disjunction_reduce_consistent; intros.
    - apply ImpAndOrAsPrime_consistent; auto.
    - apply ReduceIff_consistent; auto.
    - apply ReduceTrue_consistent; auto.
  + apply RPC.
Qed.

End KripkeSemantics.

