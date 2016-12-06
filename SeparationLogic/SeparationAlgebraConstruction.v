Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.

Local Open Scope logic_base.
Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section SeparationAlgebraConstructions.
  Context {worlds: Type} (kiM: KripkeIntuitionisticModel worlds).

  (** *Downwards CLosure*)
Definition DownwardsClosure_SA
           {J: Join worlds}: Join worlds.
Proof. intros m1 m2 m; exact (exists n, Korder m n /\ join _ m1 m2 n).
Defined.

Definition DownwardsClosure_nSA
           {J: Join worlds}
           {SA: SeparationAlgebra worlds}
           {uSA: UpwardsClosedSeparationAlgebra worlds}:
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
    destruct (join_Korder_up _ _ _ _ _ mz' H2 H) as [mxyz'' [? ?]]; [reflexivity |].
    destruct (join_assoc _ _ _ _ _ _ H1 H3) as [myz' [? ?]].
    exists myz'.
    split.
    - exists myz'; split; auto.
      reflexivity.
    - exists mxyz''; split; auto.
      etransitivity; eauto.
Defined.

Lemma DownwardsClosure_pre_unit
      {J: Join worlds}
      {SA: SeparationAlgebra worlds}
      {uSA: UpwardsClosedSeparationAlgebra worlds}:
  forall m, @pre_unit _ _ J m <-> @pre_unit _ _ (DownwardsClosure_SA) m.
Proof.
  intros.
  unfold pre_unit; split; intros.
  + destruct H0 as [n0 [? ?]].
    etransitivity; eauto.
  + apply H.
    exists n'.
    split; auto.
    reflexivity.
Qed.

Definition DownwardsClosure_DownwardsClosed
           {J: Join worlds}
           {SA: SeparationAlgebra worlds}
           {uSA: UpwardsClosedSeparationAlgebra worlds}:
  @DownwardsClosedSeparationAlgebra worlds (DownwardsClosure_SA) _.
Proof.
  intros until m2; intros.
  exists m1, m2.
  split; [| split]; [| reflexivity | reflexivity].
  destruct H as [n' [? ?]].
  exists n'.
  split; auto; etransitivity; eauto.
Defined.

Definition DownwardsClosure_UpwardsClosed
           {J: Join worlds}
           {SA: SeparationAlgebra worlds}
           {uSA: UpwardsClosedSeparationAlgebra worlds}:
  @UpwardsClosedSeparationAlgebra worlds (DownwardsClosure_SA) _.
Proof.
  intros until n2; intros.
  simpl in *.
  destruct H as [n [? ?]].
  destruct (join_Korder_up _ _ _ _ _ _ H2 H0 H1) as [n' [? ?]].
  exists n; split; auto.
  exists n'; split; auto.
Defined.

Definition DownwardsClosure_USA
           {J: Join worlds}
           {SA: SeparationAlgebra worlds}
           {upSA: UpwardsClosedSeparationAlgebra worlds}
           {USA: UnitarySeparationAlgebra worlds}:
  @UnitarySeparationAlgebra worlds _ (DownwardsClosure_SA).
Proof.
  eapply UpwardsClosed_nUSA.
  - apply DownwardsClosure_UpwardsClosed.
  - intros.
    simpl.
    destruct (unit_exists _ n) as [u [? ?]].
    exists u; split; auto.
    exists n; split; auto.
    rewrite <- DownwardsClosure_pre_unit; auto.
Defined.

Definition DownwardsClosure_gcSA
           {J: Join worlds}
           {SA: SeparationAlgebra worlds}
           {uSA: UpwardsClosedSeparationAlgebra worlds}
           {gcSA: GarbageCollectSeparationAlgebra worlds}:
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


  (** *Upwards CLosure*)

Definition UpwardsClosure_SA
           {J: Join worlds}: SeparationAlgebra worlds :=
  Build_SeparationAlgebra _
                          (fun m1 m2 m: worlds => exists n1 n2, n1 <= m1 /\ n2 <= m2 /\ join n1 n2 m).

Definition UpwardsClosure_nSA {worlds: Type} {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds} {dSA: DownwardsClosedSeparationAlgebra worlds}: @NormalSeparationAlgebra worlds (UpwardsClosure_SA worlds).
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

Lemma UpwardsClosure_pre_unit {worlds: Type} {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds} {dSA: DownwardsClosedSeparationAlgebra worlds} {USA: UnitarySeparationAlgebra worlds} {nUSA: NormalUnitarySeparationAlgebra worlds}: forall m, @pre_unit _ _ SA m <-> @pre_unit _ _ (UpwardsClosure_SA worlds) m.
Proof.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  unfold pre_unit; split; intros.
  + destruct H0 as [m0 [n0 [? [? ?]]]].
    pose proof unit_down _ _ H0 H.
    unfold pre_unit in H3.
    etransitivity; eauto.
  + unfold pre_unit.
    intros; apply H.
    exists m, n.
    split; [| split]; auto; reflexivity.
Qed.

Definition UpwardsClosure_USA (worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds} {dSA: DownwardsClosedSeparationAlgebra worlds} {USA: UnitarySeparationAlgebra worlds} {nUSA: NormalUnitarySeparationAlgebra worlds}: @UnitarySeparationAlgebra worlds _ (UpwardsClosure_SA worlds).
Proof.
  constructor.
  intros.
  simpl.
  pose proof Korder_PreOrder as H_PreOrder.
  destruct (unit_exists n) as [u [? ?]].
  exists u; split; auto.
  + exists u, n; split; [| split]; auto; reflexivity.
  + rewrite <- UpwardsClosure_pre_unit; auto.
Defined.

Definition UpwardsClosure_UpwardsClosed {worlds: Type} {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds} {dSA: DownwardsClosedSeparationAlgebra worlds}: @UpwardsClosedSeparationAlgebra worlds _ (UpwardsClosure_SA worlds).
Proof.
  constructor.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  exists m.
  split; [| reflexivity].
  destruct H as [m1' [m2' [? [? ?]]]].
  exists m1', m2'.
  split; [| split]; auto; etransitivity; eauto.
Qed.

Definition UpwardsClosure_DownwardsClosed {worlds: Type} {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds} {dSA: DownwardsClosedSeparationAlgebra worlds}: @DownwardsClosedSeparationAlgebra worlds _ (UpwardsClosure_SA worlds).
Proof.
  constructor.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  simpl in *.
  destruct H as [n1 [n2 [? [? ?]]]].
  destruct (join_Korder_down _ _ _ _ H2 H0) as [n1' [n2' [? [? ?]]]].
  exists n1, n2; split; [| split]; auto.
  exists n1', n2'; split; [| split]; auto.
Qed.

Definition UpwardsClosure_nUSA {worlds: Type} {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds} {dSA: DownwardsClosedSeparationAlgebra worlds} {USA: UnitarySeparationAlgebra worlds} {nUSA: NormalUnitarySeparationAlgebra worlds}: @NormalUnitarySeparationAlgebra worlds _ (UpwardsClosure_SA worlds) (UpwardsClosure_USA worlds).
Proof.
  constructor.
  intros.
  rewrite <- UpwardsClosure_pre_unit in H0 |- *.
  revert H H0; apply unit_down.
Qed.

Definition UpwardsClosure_gcSA {worlds: Type} {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds} {dSA: DownwardsClosedSeparationAlgebra worlds} {gcSA: GarbageCollectSeparationAlgebra worlds}: @GarbageCollectSeparationAlgebra worlds _ (UpwardsClosure_SA worlds).
Proof.
  constructor.
  simpl.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  destruct H as [n1 [n2 [? [? ?]]]].
  etransitivity; [| eauto].
  eapply join_has_order1; eauto.
Qed.
