Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.

Local Open Scope logic_base.
Local Open Scope KripkeSemantics.

Definition DownwardsClosureSA {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M} {uSA: UpwardsClosedSeparationAlgebra MD M}: SeparationAlgebra MD M.
Proof.
  apply (Build_SeparationAlgebra _ _ _ (fun (m1 m2 m: Kworlds M) => exists n, Korder m n /\ join m1 m2 n)).
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

Definition DownwardsClosure_DownwardsClosed {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M} {uSA: UpwardsClosedSeparationAlgebra MD M}: @DownwardsClosedSeparationAlgebra MD _ M _ (DownwardsClosureSA M).
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

Definition DownwardsClosure_UpwardsClosed {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M} {uSA: UpwardsClosedSeparationAlgebra MD M}: @UpwardsClosedSeparationAlgebra MD _ M _ (DownwardsClosureSA M).
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

Definition UpwardsClosureSA {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M} {dSA: DownwardsClosedSeparationAlgebra MD M}: SeparationAlgebra MD M.
Proof.
  apply (Build_SeparationAlgebra _ _ _ (fun (m1 m2 m: Kworlds M) => exists n1 n2, n1 <= m1 /\ n2 <= m2 /\ join n1 n2 m)).
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

Definition UpwardsClosureSA_UpwardsClosed {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA_D: SeparationAlgebra MD M} {dSA: DownwardsClosedSeparationAlgebra MD M}: @UpwardsClosedSeparationAlgebra MD _ M _ (UpwardsClosureSA M).
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

Definition UpwardsClosureSA_DownwardsClosed {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA_D: SeparationAlgebra MD M} {dSA: DownwardsClosedSeparationAlgebra MD M}: @DownwardsClosedSeparationAlgebra MD _ M _ (UpwardsClosureSA M).
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

