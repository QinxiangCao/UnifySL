Require Import Coq.Logic.Classical_Prop.
Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.
Require Import Omega.

Local Open Scope logic_base.

Lemma truth_lemma_from_syntactic_reduction {L: Language} (R: SyntacticReduction L) {sR: NormalSyntacticReduction L R} (SM: Semantics L) (Gamma: ProofTheory L):
  reduction_consistent_prooftheory R Gamma ->
  reduction_consistent_semantics R SM ->
  forall (canonical_model: model) (Phi: context),
    (forall x, Phi x <-> Phi |-- x) ->
    (forall x: expr, normal_form x -> (canonical_model |= x <-> Phi x)) ->
    (forall x: expr, canonical_model |= x <-> Phi x).
Proof.
  intros.
  destruct (reduce_to_norm x) as [y [? ?]].
  specialize (H2 y H4).
  destruct H as [_ ?];
  specialize (H Phi Phi x y (context_reduce_refl _) H3).
  specialize (H0 x y canonical_model H3).
  pose proof H1 x.
  pose proof H1 y.
  tauto.
Qed.

Lemma contrapositive_strongly_complete {L: Language} (R: SyntacticReduction L) {sR: NormalSyntacticReduction L R} (SM: Semantics L) (Gamma: ProofTheory L):
  (forall Phi x, ~ Phi |-- x -> ~ Phi |== x) ->
  strongly_complete Gamma SM.
Proof.
  intros.
  hnf; intros.
  specialize (H Phi x).
  tauto.
Qed.

Definition LindenbaumChain {A: Type} (step: nat -> Ensemble A -> Ensemble A) (init: Ensemble A): nat -> Ensemble A :=
  fix l (n: nat): Ensemble A :=
    match n with
    | 0 => init
    | S n => step n (l n)
    end.

Definition LindenbaumConstruction {A: Type} (step: nat -> Ensemble A -> Ensemble A) (init: Ensemble A): Ensemble A :=
  fun a => exists n, LindenbaumChain step init n a.

Definition Lindenbaum_spec_included {A: Type}: forall (step: nat -> Ensemble A -> Ensemble A) (init: Ensemble A) n ,
  Included _ (LindenbaumChain step init n) (LindenbaumConstruction step init).
Proof.
  intros.
  intros ? ?.
  exists n; auto.
Qed.

Definition Lindenbaum_spec_pos {A: Type}: forall (step: nat -> Ensemble A -> Ensemble A) (init: Ensemble A) (Pl: list A -> Prop) (Ps: Ensemble A -> Prop),
  (forall S, Ps S <-> exists l, Forall S l /\ Pl l) ->
  (forall n S, Included _ S (step n S)) ->
  ~ Ps init ->
  (forall n S, ~ Ps S -> ~ Ps (step n S)) ->
  ~ Ps (LindenbaumConstruction step init).
Proof.
  intros.

  assert (forall n m, n <= m -> Included _ (LindenbaumChain step init n) (LindenbaumChain step init m)).
  Focus 1. {
    clear - H0.
    intros.
    induction H.
    - intros ? ?; auto.
    - intros ? ?.
      apply H0; auto.
  } Unfocus.
  clear H0; rename H3 into H0.
      
  rewrite H; intros [l [? ?]].
  unfold LindenbaumConstruction in H3.

  assert (exists n, Forall (LindenbaumChain step init n) l).
  Focus 1. {
    clear - H3 H0.
    induction H3.
    + exists 0; constructor.
    + destruct IHForall as [n1 ?].
      destruct H as [n2 ?].
      exists (max n1 n2).
      constructor.
      - apply (H0 n2); auto.
        apply Max.le_max_r.
      - revert H1; apply Forall_impl; intros.
        apply (H0 n1); auto.
        apply Max.le_max_l.
  } Unfocus.
  clear H3; rename H5 into H3.

  assert (forall n, ~ Ps (LindenbaumChain step init n)).
  Focus 1. {
    induction n.
    + auto.
    + apply H2; auto.
  } Unfocus.

  destruct H3 as [n ?].
  specialize (H5 n).
  rewrite H in H5.
  apply H5; clear H5.
  exists l; auto.
Qed.

Definition Lindenbaum_spec_neg {A: Type}: forall (step: nat -> Ensemble A -> Ensemble A) (init: Ensemble A) a n,
  LindenbaumChain step init n a ->
  LindenbaumConstruction step init a.
Proof.
  intros.
  exists n; auto.
Qed.
