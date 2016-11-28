Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.HoareLogic.ImperativeLanguage.

Class HoareLogic (Imp: ImperativeProgrammingLanguage) (L: Language): Type := {
  triple: expr -> cmd -> expr -> Prop
}.

Local Open Scope logic_base.
(*
Definition triple_valid {Imp: ImperativeProgrammingLanguage} {nImp: NormalImperativeProgrammingLanguage Imp} {L: Language} {MD: Model} {sss: SmallStepSemantics Imp MD} {SM: Semantics L MD} (guard: exceptional_state -> Prop) (Pre: expr) (c: cmd) (Post: expr): Prop :=
  forall (s_pre: state) (ms_post: state + exceptional_state), access (inl s_pre) c ms_post -> s_pre |= Pre ->
  match ms_post with
  | inl s_post => s_post |= Post
  | inr e => guard e
  end.

Section soundness.

Context {Imp: ImperativeProgrammingLanguage} {nImp: NormalImperativeProgrammingLanguage Imp} {MD: Model} {sss: SmallStepSemantics Imp MD}.

Lemma exception_go_nowhere: forall e c ms,
  access (inr e) c ms <->
  ms = inr e.
Proof.
  intros.
  split; intros.
  + hnf in H.
    remember (fmap_pair_cmd (inr e) c) as mcs1 eqn:?H.
    remember (fmap_pair_cmd ms Sskip) as mcs2 eqn:?H.
    induction H.
    - subst.
      destruct ms; inversion H1.
      subst; auto.
    - subst.
      inversion H0.
  + subst.
    hnf.
    simpl.
    apply iter_step_refl.
Qed.

Lemma aux_sequence_sound: forall c1 c2 ms1 ms3,
  access ms1 (Ssequence c1 c2) ms3 ->
  exists ms2,
  access ms1 c1 ms2 /\ access ms2 c2 ms3.
Proof.
  intros.
  destruct ms1 as [s1 | e1].
  Focus 2. {
    exists (inr e1).
    rewrite exception_go_nowhere in H.
    subst.
    split; rewrite exception_go_nowhere; auto.
  } Unfocus.
  unfold access in H.
  remember (fmap_pair_cmd (inl s1) (Ssequence c1 c2)) as mcs1 eqn:?H.
  remember (fmap_pair_cmd ms3 Sskip) as mcs2 eqn:?H.
  revert c1 H0.
  induction H; intros; subst.
  + destruct ms3 as [s3 | e3]; inversion H0.
    apply neq_Sskip_Ssequence in H1; contradiction.
  + rename IHiter_step into IH.
    specialize (IH eq_refl).
    inversion H2; subst; clear H2.

Context {L: Language} {SM: Semantics L MD} (guard: exceptional_state -> Prop).

Lemma hoare_sequence_sound: forall c1 c2 P Q R,
  triple_valid guard P c1 Q ->
  triple_valid guard Q c2 R ->
  triple_valid guard P (Ssequence c1 c2) R.
Proof.
  intros.
  hnf; intros.
  unfold access in H1.
  remember (fmap_pair_cmd (inl s_pre) (Ssequence c1 c2)) as mcs1 eqn:?H.
  remember (fmap_pair_cmd ms_post Sskip) as mcs2 eqn:?H.
  revert P c1 H H2 H3.
  induction H1; intros; subst.
  + destruct ms_post as [s_post | e]; [| inversion H3].
    inversion H3; clear H3.
    apply neq_Sskip_Ssequence in H4; contradiction.
  + rename IHiter_step into IH.
    specialize (IH eq_refl).
Abort.

End soundness.
*)