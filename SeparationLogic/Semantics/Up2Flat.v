Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.DownwardsClosure.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Logic.SeparationLogic.Semantics.UpwardsSemantics.
Require Logic.SeparationLogic.Semantics.FlatSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.

Module Up2Flat.
Section Up2Flat.

Context {L: Language}
        {nL: NormalLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {kiM: KripkeIntuitionisticModel (Kworlds M)}
        {J: Join  (Kworlds M)}
        {SA: SeparationAlgebra (Kworlds M)}
        {uSA: UpwardsClosedSeparationAlgebra (Kworlds M)}
        {SM: Semantics L MD}
        {kiSM: KripkeIntuitionisticSemantics L MD M SM}
        {usSM: UpwardsSemantics.SeparatingSemantics L MD M SM}.

Definition fsSM: @FlatSemantics.SeparatingSemantics L sL MD kMD M _ (DownwardsClosure_J) SM.
Proof.
  constructor.
  + (* sat_sepcon *)
    intros.
    unfold WeakSemantics.sepcon.
    split; unfold Included, Ensembles.In; intros m ?.
    - rewrite (app_same_set (UpwardsSemantics.denote_sepcon _ _) m) in H.
      destruct H as [m1 [m2 [? [? ?]]]].
      exists m1, m2.
      split; [| split]; auto.
      exists m1, m2.
      split; [| split]; auto; reflexivity.
    - rewrite (app_same_set (UpwardsSemantics.denote_sepcon _ _) m).
      destruct H as [m1 [m2 [[n1 [n2 [? [? ?]]]] [? ?]]]].
      exists n1, n2.
      split; [| split]; auto; eapply sat_mono; eauto.
  + (* sat_wand *)
    intros.
    unfold WeakSemantics.wand.
    split; unfold Included, Ensembles.In; intros m ?.
    - rewrite (app_same_set (UpwardsSemantics.denote_wand _ _) m) in H.
      intros.
      destruct H0 as [m' [m1' [? [? ?]]]].
      apply (H  _ _ _ H0 H3).
      eapply sat_mono; eauto.
    - rewrite (app_same_set (UpwardsSemantics.denote_wand _ _) m).
      hnf; intros.
      apply (H m1 m2); auto.
      exists m0, m1.
      split; [| split]; auto.
      reflexivity.
Qed.

Definition feSM {s'L: SeparationEmpLanguage L} {USA': UnitalSeparationAlgebra' (Kworlds M)} {ueSM: UpwardsSemantics.EmpSemantics L MD M SM}: @FlatSemantics.EmpSemantics L _ _ MD _ M _ (DownwardsClosure_J) SM.
Proof.
  constructor;
  intros m; simpl; unfold Ensembles.In; unfold WeakSemantics.emp;
  rewrite <- DownwardsClosure_increasing;
  apply UpwardsSemantics.denote_emp.
Qed.

End Up2Flat.
End Up2Flat.

(*
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
*)
