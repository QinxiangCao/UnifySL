Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Relations.Relation_Operators.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.
Require Import Logic.LogicBase.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.MinimunLogic.

Inductive propag_reduce {L: Language} (atomic_reduce: expr -> expr -> Prop): expr -> expr -> Prop :=
  propag_reduce_spec: forall x y p, atomic_reduce x y ->
    propag_reduce atomic_reduce (propagation_denote p x) (propagation_denote p y).

Class SyntacticReduction (L: Language) : Type := {
  atomic_reduce: expr -> expr -> Prop;
  single_step_reduce := propag_reduce atomic_reduce;
  reduce := clos_refl_trans _ single_step_reduce
}.

Class NormalSyntacticReduction (L: Language) (R: SyntacticReduction L) : Type := {
  normal_form: expr -> Prop;
  reduce_to_norm: forall x, exists y, reduce x y /\ normal_form y
}.

Definition context_reduce {L: Language} {R: SyntacticReduction L} (Phi Psi: context): Prop :=
  (forall x, Phi x -> exists y, reduce x y /\ Psi y) /\
  (forall y, Psi y -> exists x, reduce x y /\ Phi x).

Local Open Scope logic_base.

Definition AtomicReductionConsistentProvable {L: Language} {nL: NormalLanguage L} (atomic_reduce: expr -> expr -> Prop) (Gamma: ProofTheory L): Prop :=
  forall x y, atomic_reduce x y -> (|-- x --> y /\ |-- y --> x).

Definition ReductionPropagationConsistentProvable {L: Language} {nL: NormalLanguage L} (Gamma: ProofTheory L): Prop :=
  forall x y sp,
   (|-- x --> y /\ |-- y --> x) ->
   (|-- single_propagation_denote sp x --> single_propagation_denote sp y /\
    |-- single_propagation_denote sp y --> single_propagation_denote sp x).

Definition AtomicReductionConsistentSemantics {L: Language} (atomic_reduce: expr -> expr -> Prop) (SM: Semantics L): Prop :=
  forall x y m, atomic_reduce x y -> (m |= x <-> m |= y).

Definition ReductionPropagationConsistentSemantics {L: Language} (SM: Semantics L): Prop :=
  forall x y sp,
   (forall m, m |= x <-> m |= y) ->
   (forall m, m |= single_propagation_denote sp x <-> m |= single_propagation_denote sp y).

Definition ReductionConsistentProvable {L: Language} (R: SyntacticReduction L) (Gamma: ProofTheory L): Prop :=
  forall x y, reduce x y -> (|-- x <-> |-- y).

Class ReductionConsistentSemantics {L: Language} (R: SyntacticReduction L) (SM: Semantics L): Prop :=
  sat_reduce: forall x y m, reduce x y -> (m |= x <-> m |= y).

Class ReductionConsistentProofTheory {L: Language} (R: SyntacticReduction L) (Gamma: ProofTheory L): Prop := {
  provable_reduce: forall x y, reduce x y -> (|-- x <-> |-- y);
  derivable_reduce: forall Phi Psi x y, context_reduce Phi Psi -> reduce x y -> (Phi |-- x <-> Psi |-- y)
}.

(* Properties *)

Lemma propagation_propagation_denote {L: Language}: forall p1 p2 x,
  propagation_denote p1 (propagation_denote p2 x) = propagation_denote (p1 ++ p2) x.
Proof.
  intros.
  induction p1.
  + reflexivity.
  + simpl.
    f_equal; auto.
Qed.

Lemma propag_reduce_propag_reduce {L: Language}: forall r x y,
  propag_reduce (propag_reduce r) x y -> propag_reduce r x y.
Proof.
  intros.
  destruct H.
  destruct H.
  rewrite !propagation_propagation_denote.
  constructor; auto.
Qed.

Lemma propag_reduce_reduce {L: Language} {R: SyntacticReduction L}: forall x y,
  propag_reduce reduce x y -> reduce x y.
Proof.
  intros.
  destruct H.
  induction H.
  + apply rt_step.
    unfold single_step_reduce in *.
    destruct H.
    rewrite !propagation_propagation_denote.
    constructor; auto.
  + apply rt_refl.
  + eapply rt_trans; eauto.
Qed.

Lemma reduce_step {L: Language} {R: SyntacticReduction L}:
  forall x y, atomic_reduce x y -> reduce x y.
Proof.
  intros.
  apply rt_step.
  apply (propag_reduce_spec _ _ _ nil); auto.
Qed.

Lemma reduce_refl {L: Language} {R: SyntacticReduction L}:
  forall x, reduce x x.
Proof. intros. apply rt_refl; auto. Qed.

Lemma reduce_trans {L: Language} {R: SyntacticReduction L}:
  forall x y z, reduce x y -> reduce y z -> reduce x z.
Proof. intros. eapply rt_trans; eauto. Qed.

Lemma context_reduce_refl {L: Language} {R: SyntacticReduction L}:
  forall Phi, context_reduce Phi Phi.
Proof.
  intros.
  hnf; split.
  + intros; exists x.
    split; auto.
    apply reduce_refl.
  + intros; exists y.
    split; auto.
    apply reduce_refl.
Qed.

Lemma context_reduce_trans {L: Language} {R: SyntacticReduction L}:
  forall Phi Phi' Phi'', context_reduce Phi Phi' -> context_reduce Phi' Phi'' -> context_reduce Phi Phi''.
Proof.
  intros.
  hnf; split.
  + intros.
    destruct (proj1 H x H1) as [y [? ?]].
    destruct (proj1 H0 y H3) as [z [? ?]].
    exists z; split; auto.
    eapply reduce_trans; eauto.
  + intros z ?.
    destruct (proj2 H0 z H1) as [y [? ?]].
    destruct (proj2 H y H3) as [x [? ?]].
    exists x; split; auto.
    eapply reduce_trans; eauto.
Qed.

Lemma imp_reduce {L: Language} {nL: NormalLanguage L} {R: SyntacticReduction L}:
  forall x1 x2 y1 y2,
    reduce x1 x2 ->
    reduce y1 y2 ->
    reduce (impp x1 y1) (impp x2 y2).
Proof.
  intros.
  eapply reduce_trans.
  + apply propag_reduce_reduce.
    rewrite <- imp1_propag_denote.
    apply (propag_reduce_spec _ _ _ (imp1_propag y1 :: nil) H).
  + simpl; rewrite imp1_propag_denote.
    apply propag_reduce_reduce.
    rewrite <- !imp2_propag_denote.
    apply (propag_reduce_spec _ _ _ (imp2_propag x2 :: nil) H0).
Qed.

Lemma multi_imp_reduce {L: Language} {nL: NormalLanguage L} {R: SyntacticReduction L}:
  forall xs1 xs2 y1 y2,
    Forall2 reduce xs1 xs2 ->
    reduce y1 y2 ->
    reduce (multi_imp xs1 y1) (multi_imp xs2 y2).
Proof.
  intros.
  induction H.
  + auto.
  + simpl.
    apply imp_reduce; auto.
Qed.

Lemma disjunction_reduce_consistent_provable {L: Language} {nL: NormalLanguage L} (Gamma: ProofTheory L):
  forall reduce1 reduce2: relation expr,
    AtomicReductionConsistentProvable reduce1 Gamma ->
    AtomicReductionConsistentProvable reduce2 Gamma ->
    AtomicReductionConsistentProvable (relation_disjunction reduce1 reduce2) Gamma.
Proof.
  intros.
  hnf; intros.
  destruct H1.
  + apply H; auto.
  + apply H0; auto.
Qed.

Lemma Build1_ReductionConsistentProofTheory {L: Language} {nL: NormalLanguage L} {R: SyntacticReduction L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma}:
  ReductionConsistentProvable R Gamma ->
  ReductionConsistentProofTheory R Gamma.
Proof.
  constructor; auto.
  intros.
  split; intros; rewrite derivable_provable in H2 |- *.
  - destruct H2 as [xs [? ?]].
    destruct H0.
    pose proof fin_subset_match Phi Psi H0 xs H2.
    destruct H5 as [ys [? ?]].
    exists ys; split; auto.
    erewrite <- (H _ _); eauto.
    apply multi_imp_reduce; auto.
  - destruct H2 as [ys [? ?]].
    destruct H0.
    pose proof fin_subset_match Psi Phi H4 ys H2.
    destruct H5 as [xs [? ?]].
    exists xs; split; auto.
    erewrite -> (H _ _); eauto.
    apply multi_imp_reduce; auto.
    apply Forall2_lr_rev; auto.
Qed.


Lemma Build2_ReductionConsistentProofTheory {L: Language} {nL: NormalLanguage L} {R: SyntacticReduction L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma}:
  AtomicReductionConsistentProvable reduce Gamma ->
  ReductionConsistentProofTheory R Gamma.
Proof.
  intros.
  apply Build1_ReductionConsistentProofTheory.
  hnf; intros.
  specialize (H _ _ H0).
  clear H0; destruct H.
  split; intros.
  + eapply modus_ponens; eauto.
  + eapply modus_ponens; eauto.
Qed.

Lemma Build3_ReductionConsistentProofTheory {L: Language} {nL: NormalLanguage L} {R: SyntacticReduction L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma}:
  AtomicReductionConsistentProvable atomic_reduce Gamma ->
  ReductionPropagationConsistentProvable Gamma ->
  ReductionConsistentProofTheory R Gamma.
Proof.
  intros.
  apply Build2_ReductionConsistentProofTheory.
  hnf; intros.
  induction H1.
  + destruct H1.
    induction p.
    - intros; apply H; auto.
    - apply H0; auto.
  + split; apply imp_refl.
  + destruct IHclos_refl_trans1, IHclos_refl_trans2.
    split; eapply imp_trans; eauto.
Qed.

Lemma disjunction_reduce_consistent_semantics {L: Language} (SM: Semantics L):
  forall reduce1 reduce2: relation expr,
    (forall x y, reduce1 x y -> forall m, m |= x <-> m |= y) ->
    (forall x y, reduce2 x y -> forall m, m |= x <-> m |= y) ->
    forall x y, relation_disjunction reduce1 reduce2 x y ->
    forall m, m |= x <-> m |= y.
Proof.
  intros.
  destruct H1.
  + apply H; auto.
  + apply H0; auto.
Qed.

Lemma Build_ReductionConsistentSemantics {L: Language} {R: SyntacticReduction L} {SM: Semantics L}:
  AtomicReductionConsistentSemantics atomic_reduce SM ->
  ReductionPropagationConsistentSemantics SM ->
  ReductionConsistentSemantics R SM.
Proof.
  intros.
  hnf; intros.
  induction H1; [| tauto | tauto].
  destruct H1.
  revert m; induction p.
  + intros; apply H; auto.
  + apply H0; auto.
Qed.
