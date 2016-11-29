Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.

Local Open Scope logic_base.
Local Open Scope KripkeSemantics.

Definition DownwardsClosure_SA (worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds}: SeparationAlgebra worlds :=
  Build_SeparationAlgebra _ (fun m1 m2 m: worlds => exists n, Korder m n /\ join m1 m2 n).

Definition DownwardsClosure_nSA {worlds: Type} {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds} {uSA: UpwardsClosedSeparationAlgebra worlds}: @NormalSeparationAlgebra worlds (DownwardsClosure_SA worlds).
Proof.
  constructor.
  + intros.
    destruct H as [n [? ?]].
    exists n.
    split; auto.
    apply join_comm; auto.
  + intros.
    pose proof Korder_PreOrder as H_PreOrder.
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

Definition DownwardsClosure_USA (worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds} {uSA: UpwardsClosedSeparationAlgebra worlds} {USA: UnitarySeparationAlgebra worlds} {nUSA: NormalUnitarySeparationAlgebra worlds}: @UnitarySeparationAlgebra worlds _ (DownwardsClosure_SA worlds).
Proof.
  apply (Build_UnitarySeparationAlgebra _ _ _ unit).
  + intros.
    simpl.
    pose proof Korder_PreOrder as H_PreOrder.
    rewrite unit_spec.
    split; intros.
    - destruct H0 as [n0 [? ?]].
      etransitivity; eauto.
    - apply H.
      exists n'.
      split; auto.
      reflexivity.
  + intros.
    simpl.
    pose proof Korder_PreOrder as H_PreOrder.
    destruct (unit_exists n) as [u [? ?]].
    exists u; split; auto.
    exists n; split; auto.
    reflexivity.
Defined.

Definition DownwardsClosure_DownwardsClosed {worlds: Type} {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds} {uSA: UpwardsClosedSeparationAlgebra worlds}: @DownwardsClosedSeparationAlgebra worlds _ (DownwardsClosure_SA worlds).
Proof.
  constructor.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  exists m1, m2.
  split; [| split]; [| reflexivity | reflexivity].
  destruct H as [n' [? ?]].
  exists n'.
  split; auto; etransitivity; eauto.
Defined.

Definition DownwardsClosure_UpwardsClosed {worlds: Type} {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds} {uSA: UpwardsClosedSeparationAlgebra worlds}: @UpwardsClosedSeparationAlgebra worlds _ (DownwardsClosure_SA worlds).
Proof.
  constructor.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  simpl in *.
  destruct H as [n [? ?]].
  destruct (join_Korder_up _ _ _ _ _ H2 H0 H1) as [n' [? ?]].
  exists n; split; auto.
  exists n'; split; auto.
Defined.

Definition DownwardsClosure_nUSA {worlds: Type} {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds} {uSA: UpwardsClosedSeparationAlgebra worlds} {USA: UnitarySeparationAlgebra worlds} {nUSA: NormalUnitarySeparationAlgebra worlds}: @NormalUnitarySeparationAlgebra worlds _ (DownwardsClosure_SA worlds) (DownwardsClosure_USA worlds).
Proof.
  constructor.
  simpl.
  apply unit_down.
Qed.

Definition DownwardsClosure_gcSA {worlds: Type} {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds} {uSA: UpwardsClosedSeparationAlgebra worlds} {gcSA: GarbageCollectSeparationAlgebra worlds}: @GarbageCollectSeparationAlgebra worlds _ (DownwardsClosure_SA worlds).
Proof.
  constructor.
  simpl.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  destruct H as [n [? ?]].
  etransitivity; eauto.
  eapply join_has_order1; eauto.
Qed.

Definition UpwardsClosure_SA (worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds}: SeparationAlgebra worlds :=
  Build_SeparationAlgebra _ (fun m1 m2 m: worlds => exists n1 n2, n1 <= m1 /\ n2 <= m2 /\ join n1 n2 m).

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

Definition UpwardsClosure_USA (worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds} {dSA: DownwardsClosedSeparationAlgebra worlds} {USA: UnitarySeparationAlgebra worlds} {nUSA: NormalUnitarySeparationAlgebra worlds}: @UnitarySeparationAlgebra worlds _ (UpwardsClosure_SA worlds).
Proof.
  apply (Build_UnitarySeparationAlgebra _ _ _ unit).
  + intros.
    simpl.
    pose proof Korder_PreOrder as H_PreOrder.
    split; intros.
    - destruct H0 as [m0 [n0 [? [? ?]]]].
      pose proof unit_down _ _ H0 H.
      rewrite unit_spec in H3.
      etransitivity; eauto.
    - rewrite unit_spec.
      intros; apply H.
      exists m, n.
      split; [| split]; auto; reflexivity.
  + intros.
    simpl.
    pose proof Korder_PreOrder as H_PreOrder.
    destruct (unit_exists n) as [u [? ?]].
    exists u; split; auto.
    exists u, n; split; [| split]; auto; reflexivity.
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
  simpl.
  apply unit_down.
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
