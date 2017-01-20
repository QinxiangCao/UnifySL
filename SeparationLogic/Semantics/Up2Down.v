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
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.

Module Upwards2Downwards.

Definition usSM {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel (Kworlds M)} {J: Join (Kworlds M)} {SA: SeparationAlgebra (Kworlds M)} {dSA: UpwardsClosedSeparationAlgebra (Kworlds M)} (SM: Semantics L MD) {kiSM: KripkeIntuitionisticSemantics L MD M SM} {usSM: UpwardsSemantics L MD M SM}: @DownwardsSemantics.DownwardsSemantics L nL pL SL MD kMD M kiM (DownwardsClosure_J) SM kiSM.
Proof.
  constructor.
  + (* sat_sepcon *)
    intros.
    pose proof Korder_PreOrder as H_PreOrder.
    rewrite UpwardsSemantics.sat_sepcon.
    split; intros.
    - destruct H as [m1 [m2 [? [? ?]]]].
      exists m, m1, m2.
      split; [reflexivity |].
      split; [| split]; auto.
      exists m1, m2.
      split; [| split]; auto; reflexivity.
    - destruct H as [m0 [m1 [m2 [? [[n1 [n2 [? [? ?]]]] [? ?]]]]]].
      destruct (join_Korder_up m0 m _ _ H2 H) as [n1' [n2' [? [? ?]]]].
      exists n1', n2'.
      split; [| split]; auto; eapply sat_mono; eauto; eapply sat_mono; eauto.
  + (* sat_wand *)
    intros.
    pose proof Korder_PreOrder as H_PreOrder.
    rewrite UpwardsSemantics.sat_wand.
    split; intros.
    - destruct H0 as [m' [m1' [? [? ?]]]].
      apply (H  _ _ _ H0 H3).
      eapply sat_mono; eauto.
    - apply (H m1 m2); auto.
      exists m0, m1.
      split; [| split]; auto.
      reflexivity.
Defined.

(*
Definition UsSM {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {uSL: UnitarySeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel (Kworlds M)} {J: Join (Kworlds M)} {SA: SeparationAlgebra (Kworlds M)} {dSA: UpwardsClosedSeparationAlgebra (Kworlds M)} {USA: UnitalSeparationAlgebra (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {dsSM: UpwardsSemantics L MD M SM} {UsSM: UnitalSemantics L MD M SM} : @UnitalSemantics L _ _ _ _ MD _ M kiM (DownwardsClosure_SA) SM kiSM.
Proof.
  intros m; simpl.
  rewrite <- DownwardsClosure_nonpositive.
  apply sat_emp.
Qed.
*)

End Upwards2Downwards.

Module Upwards2Flat.

Definition fsSM {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel (Kworlds M)} {J: Join (Kworlds M)} {SA: SeparationAlgebra (Kworlds M)} {dSA: UpwardsClosedSeparationAlgebra (Kworlds M)} (SM: Semantics L MD) {kiSM: KripkeIntuitionisticSemantics L MD M SM} {usSM: UpwardsSemantics L MD M SM}: @FlatSemantics.FlatSemantics L nL pL SL MD kMD M kiM (DownwardsClosure_J) SM kiSM.
Proof.
  constructor.
  + (* sat_sepcon *)
    intros.
    pose proof Korder_PreOrder as H_PreOrder.
    rewrite UpwardsSemantics.sat_sepcon.
    simpl in *.
    split; intros.
    - destruct H as [m1 [m2 [? [? ?]]]].
      exists m1, m2.
      split; [| split]; auto.
      exists m1, m2.
      split; [| split]; auto; reflexivity.
    - destruct H as [m1 [m2 [[n1 [n2 [? [? ?]]]] [? ?]]]].
      exists n1, n2.
      split; [| split]; auto; eapply sat_mono; eauto.
  + (* sat_wand *)
    intros.
    pose proof Korder_PreOrder as H_PreOrder.
    rewrite UpwardsSemantics.sat_wand.
    split; intros.
    - destruct H0 as [m' [m1' [? [? ?]]]].
      apply (H  _ _ _ H0 H3).
      eapply sat_mono; eauto.
    - apply (H m1 m2); auto.
      exists m0, m1.
      split; [| split]; auto.
      reflexivity.
Defined.
(*
Definition UsSM {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {uSL: UnitarySeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel (Kworlds M)} {J: Join (Kworlds M)} {SA: SeparationAlgebra (Kworlds M)} {dSA: UpwardsClosedSeparationAlgebra (Kworlds M)} {USA: UnitalSeparationAlgebra (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {dsSM: UpwardsSemantics L MD M SM} {UsSM: UnitalSemantics L MD M SM} : @UnitalSemantics L _ _ _ _ MD _ M kiM (DownwardsClosure_SA) SM kiSM.
Proof.
  intros m; simpl.
  rewrite <- DownwardsClosure_nonpositive.
  apply sat_emp.
Qed.
*)
End Upwards2Flat.
