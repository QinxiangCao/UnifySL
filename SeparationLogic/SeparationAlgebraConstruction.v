Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.

Local Open Scope logic_base.
Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section DownwardsClosure.
  Context {worlds: Type}
          {kiM: KripkeIntuitionisticModel worlds}
          {J: Join worlds}
          {SA: SeparationAlgebra worlds}
          {USA: UnitalSeparationAlgebra worlds}
          {uSA: UpwardsClosedSeparationAlgebra worlds}
          {gcSA: GarbageCollectSeparationAlgebra worlds}.

  (** *Downwards CLosure*)
Definition DownwardsClosure_SA: Join worlds.
Proof. intros m1 m2 m; exact (exists n, Korder m n /\ join m1 m2 n).
Defined.

Definition DownwardsClosure_nSA:
  @SeparationAlgebra worlds (DownwardsClosure_SA).
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
    destruct (join_Korder_up _ _ _ _ mz' H2 H) as [mxyz'' [? ?]]; [reflexivity |].
    destruct (join_assoc _ _ _ _ _ H1 H3) as [myz' [? ?]].
    exists myz'.
    split.
    - exists myz'; split; auto.
      reflexivity.
    - exists mxyz''; split; auto.
      etransitivity; eauto.
Defined.

Lemma DownwardsClosure_nonpositive:
  forall m, @nonpositive _ _ J m <-> @nonpositive _ _ (DownwardsClosure_SA) m.
Proof.
  intros.
  unfold nonpositive; split; intros.
  + destruct H0 as [n0 [? ?]].
    etransitivity; eauto.
  + apply H.
    exists n'.
    split; auto.
    reflexivity.
Qed.

Definition DownwardsClosure_DownwardsClosed:
  @DownwardsClosedSeparationAlgebra worlds (DownwardsClosure_SA) _.
Proof.
  intros until m2; intros.
  exists m1, m2.
  split; [| split]; [| reflexivity | reflexivity].
  destruct H as [n' [? ?]].
  exists n'.
  split; auto; etransitivity; eauto.
Defined.

Definition DownwardsClosure_UpwardsClosed:
  @UpwardsClosedSeparationAlgebra worlds (DownwardsClosure_SA) _.
Proof.
  intros until n2; intros.
  simpl in *.
  destruct H as [n [? ?]].
  destruct (join_Korder_up _ _ _ _ _ H2 H0 H1) as [n' [? ?]].
  exists n; split; auto.
  exists n'; split; auto.
Defined.

Definition DownwardsClosure_USA:
  @UnitalSeparationAlgebra worlds _ (DownwardsClosure_SA).
Proof.
  eapply UpwardsClosed_nUSA.
  - apply DownwardsClosure_UpwardsClosed.
  - intros.
    simpl.
    destruct (nonpos_exists n) as [u [? ?]].
    destruct H as [n' [H1 H2]].
    exists u; split; auto.
    exists n'; split; auto.
    unfold join, DownwardsClosure_SA.
    exists n; split; auto.
    reflexivity.
    rewrite <- DownwardsClosure_nonpositive; auto.
Defined.

Definition DownwardsClosure_gcSA:
  @GarbageCollectSeparationAlgebra worlds _ (DownwardsClosure_SA).
Proof.
  constructor.
  simpl.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  destruct H as [n [? ?]].
  etransitivity; eauto.
  eapply join_has_order1; eauto.
Qed.

End DownwardsClosure.

Section UpwardsClosure.
  Context {worlds : Type}
          {kiM: KripkeIntuitionisticModel worlds}
          {J: Join worlds}
          {SA: SeparationAlgebra worlds}
          {dSA: DownwardsClosedSeparationAlgebra worlds}
          {USA: UnitalSeparationAlgebra worlds}
          {gcSA: GarbageCollectSeparationAlgebra worlds}.


  (** *Upwards CLosure*)

Definition UpwardsClosure_SA: Join worlds.
Proof. exact (fun m1 m2 m: worlds => exists n1 n2, n1 <= m1 /\ n2 <= m2 /\ join n1 n2 m).
Defined.

Definition UpwardsClosure_nSA:
  @SeparationAlgebra worlds (UpwardsClosure_SA).
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
    destruct (join_Korder_down _ _ _ _ H2 H0) as [mx' [my' [? [? ?]]]].
    destruct (join_assoc _ _ _ _ _ H5 H4) as [myz' [? ?]].
    exists myz'.
    split.
    - exists my', mz'; split; [| split]; auto.
      etransitivity; eauto.
    - exists mx', myz'; split; [| split]; auto.
      * etransitivity; eauto.
      * reflexivity.
Defined.

Lemma UpwardsClosure_nonpositive: forall m, @nonpositive _ _ J m <-> @nonpositive _ _ (UpwardsClosure_SA) m.
Proof.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  unfold nonpositive; split; intros.
  + destruct H0 as [m0 [n0 [? [? ?]]]].
    pose proof nonpos_down _ _ H0 H.
    unfold nonpositive in H3.
    etransitivity; eauto.
  + unfold nonpositive.
    intros; apply H.
    exists m, n.
    split; [| split]; auto; reflexivity.
Qed.



Definition UpwardsClosure_UpwardsClosed:
  @UpwardsClosedSeparationAlgebra worlds (UpwardsClosure_SA) _.
Proof.
  intros until n2; intros.
  exists m.
  split; [| reflexivity].
  destruct H as [m1' [m2' [? [? ?]]]].
  exists m1', m2'.
  split; [| split]; auto; etransitivity; eauto.
Qed.

Definition UpwardsClosure_DownwardsClosed : @DownwardsClosedSeparationAlgebra worlds (UpwardsClosure_SA) _.
Proof.
  intros until m2; intros.
  simpl in *.
  destruct H as [n1 [n2 [? [? ?]]]].
  destruct (join_Korder_down _ _ _ _ H2 H0) as [n1' [n2' [? [? ?]]]].
  exists n1, n2; split; [| split]; auto.
  exists n1', n2'; split; [| split]; auto.
Qed.

Definition UpwardsClosure_USA: @UnitalSeparationAlgebra worlds _ (UpwardsClosure_SA).
Proof.
  constructor.
  - intros.
    simpl.
    destruct (nonpos_exists n) as [u [? ?]].
    destruct H as [n' [H1 H2]].
    exists u; split; auto.
    + exists n'; split; auto.
      exists u, n'; split; [| split]; auto; reflexivity.
    + rewrite <- UpwardsClosure_nonpositive; auto.
  - intros.
    rewrite <- UpwardsClosure_nonpositive in H0 |- *.
    revert H H0; apply nonpos_down.
Defined.

Definition UpwardsClosure_gcSA: @GarbageCollectSeparationAlgebra worlds _ (UpwardsClosure_SA).
Proof.
  constructor.
  simpl.
  intros.
  destruct H as [n1 [n2 [? [? ?]]]].
  etransitivity; [| eauto].
  eapply join_has_order1; eauto.
Qed.

End UpwardsClosure.
