Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Stream.SigStream.
Require Import Logic.lib.Stream.SigStream.
Require Import Logic.lib.Stream.StreamFunctions.

Lemma cut2_exists {A: Type}: forall (h: stream A) (P: A -> Prop),
  (exists h1 h2,
     is_fin_stream h1 /\
     h = stream_app h1 h2 /\
     (forall n a, h1 n = Some a -> ~ P a) /\
     (exists a, h2 0 = Some a /\ P a)) \/
  (forall n a, h n = Some a -> ~ P a).
Proof.
  intros.
  destruct (classic (exists n a, h n = Some a /\ P a)).
  + left.
    apply (dec_inh_nat_subset_has_unique_least_element
             _ (fun n => classic _)) in H.
    destruct H as [n [[? ?] _]].
    destruct H as [a [? ?]].
    exists (fstn_stream n h), (skipn_stream n h).
    split; [| split; [| split]].
    - apply fstn_stream_is_fin_stream.
    - symmetry; apply stream_app_fstn_skipn.
    - clear H H1 a.
      intros; intro.
      destruct (lt_dec n0 n);
        [| rewrite fstn_stream_None in H by omega; congruence].
      rewrite fstn_stream_Some in H by auto.
      specialize (H0 n0 (ex_intro _ a (conj H H1))).
      omega.
    - exists a; split; auto.
  + right.
    firstorder.
Qed.
