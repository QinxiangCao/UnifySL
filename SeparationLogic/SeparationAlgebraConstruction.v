Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.

Local Open Scope logic_base.
Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section UpwardsClosure.
  Context {worlds: Type}
          {kiM: KripkeIntuitionisticModel worlds}
          {J: Join worlds}
          {SA: SeparationAlgebra worlds}
          {dSA: DownwardsClosedSeparationAlgebra worlds}.

  (** *Upwards CLosure*)
Definition UpwardsClosure_J: Join worlds.
Proof. intros m1 m2 m; exact (exists n, n <= m /\ join m1 m2 n).
Defined.

Definition UpwardsClosure_SA:
  @SeparationAlgebra worlds (UpwardsClosure_J).
Proof.
  constructor.
  + intros.
    destruct H as [n [? ?]].
    exists n.
    split; auto.
    apply join_comm; auto.
  + intros.
    rename mx into mx', my into my', mz into mz'.
    destruct H as [mxy' [? ?]].
    destruct H0 as [mxyz' [? ?]].
    destruct (join_Korder_down _ _ _ _ mz' H2 H) as [mxyz'' [? ?]]; [reflexivity |].
    destruct (join_assoc _ _ _ _ _ H1 H3) as [myz' [? ?]].
    exists myz'.
    split.
    - exists myz'; split; auto.
      reflexivity.
    - exists mxyz''; split; auto.
      etransitivity; eauto.
Defined.

Lemma UpwardsClosure_increasing:
  forall m, @increasing _ _ J m <-> @increasing _ _ (UpwardsClosure_J) m.
Proof.
  intros.
  unfold increasing; split; intros.
  + destruct H0 as [n0 [? ?]].
    etransitivity; eauto.
  + apply H.
    exists n'.
    split; auto.
    reflexivity.
Qed.

Definition UpwardsClosure_UpwardsClosed:
  @UpwardsClosedSeparationAlgebra worlds (UpwardsClosure_J) _.
Proof.
  intros until m2; intros.
  exists m1, m2.
  split; [| split]; [| reflexivity | reflexivity].
  destruct H as [n' [? ?]].
  exists n'.
  split; auto; etransitivity; eauto.
Defined.

Definition UpwardsClosure_DownwardsClosed:
  @DownwardsClosedSeparationAlgebra worlds (UpwardsClosure_J) _.
Proof.
  intros until n2; intros.
  simpl in *.
  destruct H as [n [? ?]].
  destruct (join_Korder_down _ _ _ _ _ H2 H0 H1) as [n' [? ?]].
  exists n; split; auto.
  exists n'; split; auto.
Defined.

Context   {USA: UnitalSeparationAlgebra worlds}
          {gcSA: GarbageCollectSeparationAlgebra worlds}.

Definition UpwardsClosure_USA:
  @UnitalSeparationAlgebra worlds _ (UpwardsClosure_J).
Proof.
  constructor.
  - intros.
    simpl.
    destruct (incr_exists n) as [u [? ?]].
    destruct H as [n' [H1 H2]].
    exists u; split; auto.
    + exists n'; split; auto.
      exists n; split; auto; reflexivity.
    + rewrite <- UpwardsClosure_increasing; auto.
Defined.

Definition UpwardsClosure_gcSA:
  @GarbageCollectSeparationAlgebra worlds _ (UpwardsClosure_J).
Proof.
  constructor.
  simpl.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  destruct H as [n [? ?]].
  etransitivity; eauto.
  eapply join_has_order1; eauto.
Qed.

End UpwardsClosure.

Section DownwardsClosure.
  Context {worlds : Type}
          {kiM: KripkeIntuitionisticModel worlds}
          {J: Join worlds}
          {SA: SeparationAlgebra worlds}
          {dSA: UpwardsClosedSeparationAlgebra worlds}.

  (** *Downwards CLosure*)

Definition DownwardsClosure_J: Join worlds.
Proof. exact (fun m1 m2 m: worlds => exists n1 n2, m1 <= n1 /\ m2 <= n2 /\ join n1 n2 m).
Defined.

Definition DownwardsClosure_SA:
  @SeparationAlgebra worlds (DownwardsClosure_J).
Proof.
  constructor.
  + (* join_comm *)
    intros.
    destruct H as [n1 [n2 [? [? ?]]]].
    exists n2, n1.
    split; [| split]; auto.
    apply join_comm; auto.
  + (* join_assoc *)
    intros.
    pose proof Korder_PreOrder as H_PreOrder.
    destruct H as [mx'' [my'' [? [? ?]]]].
    destruct H0 as [mxy' [mz' [? [? ?]]]].
    destruct (join_Korder_up _ _ _ _ H2 H0) as [mx' [my' [? [? ?]]]].
    destruct (join_assoc _ _ _ _ _ H5 H4) as [myz' [? ?]].
    exists myz'.
    split.
    - exists my', mz'; split; [| split]; auto.
      etransitivity; eauto.
    - exists mx', myz'; split; [| split]; auto.
      * etransitivity; eauto.
      * reflexivity.
Defined.

(*
Lemma DownwardsClosure_nonpositive: forall m, @nonpositive _ _ J m <-> @nonpositive _ _ (DownwardsClosure_SA) m.
Proof.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  unfold nonpositive; split; intros.
  + destruct H0 as [m0 [n0 [? [? ?]]]].
    
    pose proof nonpos_up _ _ H0.
    apply H3 in H.
    unfold nonpositive in H.
    specialize (H _ _ H2).
    etransitivity; eauto.
  + apply H.
    exists m, n.
    split; [| split]; auto; reflexivity.
Qed.
*)
Definition DownwardsClosure_DownwardsClosed:
  @DownwardsClosedSeparationAlgebra worlds (DownwardsClosure_J) _.
Proof.
  intros until n2; intros.
  exists m.
  split; [| reflexivity].
  destruct H as [m1' [m2' [? [? ?]]]].
  exists m1', m2'.
  split; [| split]; auto; etransitivity; eauto.
Qed.

Definition DownwardsClosure_UpwardsClosed : @UpwardsClosedSeparationAlgebra worlds (DownwardsClosure_J) _.
Proof.
  intros until m2; intros.
  simpl in *.
  destruct H as [n1 [n2 [? [? ?]]]].
  destruct (join_Korder_up _ _ _ _ H2 H0) as [n1' [n2' [? [? ?]]]].
  exists n1, n2; split; [| split]; auto.
  exists n1', n2'; split; [| split]; auto.
Qed.
(*
Definition DownwardsClosure_USA: @UnitalSeparationAlgebra worlds _ (DownwardsClosure_SA).
Proof.
  constructor.
  - intros.
    simpl.
    destruct (nonpos_exists n) as [u [? ?]].
    destruct H as [n' [H1 H2]].
    exists u; split; auto.
    + exists n'; split; auto.
      exists u, n'; split; [| split]; auto; reflexivity.
    + rewrite <- DownwardsClosure_nonpositive; auto.
  - intros ? ? ?.
    rewrite <- !DownwardsClosure_nonpositive.
    apply nonpos_up; auto.
Defined.
*)

Context   {USA: UnitalSeparationAlgebra worlds}
          {gcSA: GarbageCollectSeparationAlgebra worlds}.


Definition DownwardsClosure_gcSA: @GarbageCollectSeparationAlgebra worlds _ (DownwardsClosure_J).
Proof.
  constructor.
  simpl.
  intros.
  destruct H as [n1 [n2 [? [? ?]]]].
  etransitivity; [eauto |].
  eapply join_has_order1; eauto.
Qed.

End DownwardsClosure.
