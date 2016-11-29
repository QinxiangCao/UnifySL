Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.SeparationLogic.SeparationAlgebraConstruction.
Require Import Logic.SeparationLogic.Semantics. Import Logic.SeparationLogic.Semantics.UpwardsSemantics.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.
Local Open Scope SeparationLogic.
Local Open Scope KripkeSemantics.

Module Upwards2Downwards.

Definition dsSM {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel (Kworlds M)} {SA: SeparationAlgebra (Kworlds M)} {nSA: NormalSeparationAlgebra (Kworlds M)} {uSA: UpwardsClosedSeparationAlgebra (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {usSM: UpwardsSemantics L MD M SM}: @DownwardsSemantics.DownwardsSemantics L _ _ _ MD _ M kiM (DownwardsClosure_SA (Kworlds M)) SM kiSM.
Proof.
  constructor.
  + (* sat_sepcon *)
    intros.
    pose proof Korder_PreOrder as H_PreOrder.
    rewrite UpwardsSemantics.sat_sepcon.
    split; intros.
    - destruct H as [m0 [m1 [m2 [? [? [? ?]]]]]].
      exists m1, m2.
      split; [| split]; auto.
      exists m0; split; auto.
    - destruct H as [m1 [m2 [[n [? ?]] [? ?]]]].
      exists n, m1, m2.
      split; [| split; [| split]]; auto.
  + (* sat_wand *)
    intros.
    pose proof Korder_PreOrder as H_PreOrder.
    rewrite UpwardsSemantics.sat_wand.
    split; intros.
    - rename m0 into m'.
      destruct H1 as [m2' [? ?]].
      destruct (join_Korder_up _ _ _ _ m1 H3 H0) as [m2'' [? ?]]; [reflexivity |].
      eapply sat_mono; eauto.
      eapply sat_mono; eauto.
    - apply (H m m1 m2); auto.
      * reflexivity.
      * exists m2; split; auto.
        reflexivity.
Defined.

Definition UsSM {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {uSL: UnitarySeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel (Kworlds M)} {SA: SeparationAlgebra (Kworlds M)} {nSA: NormalSeparationAlgebra (Kworlds M)} {uSA: UpwardsClosedSeparationAlgebra (Kworlds M)} {USA: UnitarySeparationAlgebra (Kworlds M)} {nUSA: NormalUnitarySeparationAlgebra (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {usSM: UpwardsSemantics L MD M SM} {UsSM: UnitarySemantics L MD M SM} : @UnitarySemantics L _ _ _ _ MD _ M kiM (DownwardsClosure_SA (Kworlds M)) (DownwardsClosure_USA (Kworlds M)) SM kiSM.
Proof.
  constructor.
  pose proof Korder_PreOrder as H_PreOrder.
  intros; simpl.
  rewrite <- DownwardsClosure_pre_unit.
  apply sat_emp.
Qed.

End Upwards2Downwards.

Module Upwards2Flat.

Definition fsSM {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel (Kworlds M)} {SA: SeparationAlgebra (Kworlds M)} {nSA: NormalSeparationAlgebra (Kworlds M)} {uSA: UpwardsClosedSeparationAlgebra (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {usSM: UpwardsSemantics L MD M SM}: @FlatSemantics.FlatSemantics L _ _ _ MD _ M kiM (DownwardsClosure_SA (Kworlds M)) SM kiSM.
Proof.
  constructor.
  + (* sat_sepcon *)
    intros.
    pose proof Korder_PreOrder as H_PreOrder.
    rewrite UpwardsSemantics.sat_sepcon.
    split; intros.
    - destruct H as [m0 [m1 [m2 [? [? [? ?]]]]]].
      exists m1, m2.
      split; [| split]; auto.
      exists m0; split; auto.
    - destruct H as [m1 [m2 [[n [? ?]] [? ?]]]].
      exists n, m1, m2.
      split; [| split; [| split]]; auto.
  + (* sat_wand *)
    intros.
    pose proof Korder_PreOrder as H_PreOrder.
    rewrite UpwardsSemantics.sat_wand.
    simpl in *.
    split; intros.
    - destruct H0 as [m2' [? ?]].
      eapply sat_mono; eauto.
    - apply (H m1 m2); auto.
      exists m2; split; auto.
      reflexivity.
Defined.

Definition UsSM {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {uSL: UnitarySeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel (Kworlds M)} {SA: SeparationAlgebra (Kworlds M)} {nSA: NormalSeparationAlgebra (Kworlds M)} {uSA: UpwardsClosedSeparationAlgebra (Kworlds M)} {USA: UnitarySeparationAlgebra (Kworlds M)} {nUSA: NormalUnitarySeparationAlgebra (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {usSM: UpwardsSemantics L MD M SM} {UsSM: UnitarySemantics L MD M SM} : @UnitarySemantics L _ _ _ _ MD _ M kiM (DownwardsClosure_SA (Kworlds M)) (DownwardsClosure_USA (Kworlds M)) SM kiSM.
Proof.
  constructor.
  pose proof Korder_PreOrder as H_PreOrder.
  intros; simpl.
  rewrite <- DownwardsClosure_pre_unit.
  apply sat_emp.
Qed.

End Upwards2Flat.
