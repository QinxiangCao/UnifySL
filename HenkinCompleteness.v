Require Import Coq.Logic.Classical_Prop.
Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.

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