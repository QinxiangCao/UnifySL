Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.SeparationLogic.UpwardsSemantics.
Require Import Logic.SeparationLogic.DownwardsSemantics.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.
Local Open Scope SeparationLogic.

Section Upwards2Downwards.

Context {MD: Model} {kMD: KripkeModel MD} {kiMD: KripkeIntuitionisticModel MD} {SA: SeparationAlgebra MD}.

Definition u2d_SA: SeparationAlgebra MD.
  apply (Build_SeparationAlgebra _ _ (fun M (m1 m2 m: Kworlds M) => exists n, Korder m n /\ join m1 m2 n)).
  + intros.
    destruct H as [n [? ?]].
    exists n.
    split; auto.
    apply join_comm; auto.
  + intros.
    pose proof Korder_PreOrder M as H_PreOrder.
    rename mx into mx', my into my', mz into mz'.
    destruct H as [mxy' [? ?]].
    destruct H0 as [mxyz' [? ?]].
    destruct (join_Korder _ _ _ _ mz' H2 H) as [mxyz'' [? ?]]; [reflexivity |].
    destruct (join_assoc _ _ _ _ _ H1 H3) as [myz' [? ?]].
    exists myz'.
    split.
    - exists myz'; split; auto.
      reflexivity.
    - exists mxyz''; split; auto.
      etransitivity; eauto.

Context {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L}  {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD SM} {dsSM: DownwardsSemantics L MD SM}.

Definition u2d_sSM {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L} {pkSM: PreKripkeSemantics L SM} {kiM: KripkeIntuitionisticModel L SM} {kiSM: KripkeIntuitionisticSemantics L SM} (usSM: UpwardsSemantics L SM): DownwardsSemantics L SM.
  refine (Build_DownwardsSemantics _ _ _ _ _ _ _ _ (fun M (m1 m2 m: Kworlds M) => exists n, Korder m n /\ UpwardsSemantics.join m1 m2 n) _ _ _ _ _).
  + (* join_Korder *)
    intros.
    pose proof Korder_PreOrder M as H_PreOrder.
    exists m1, m2.
    split; [| split]; [| reflexivity | reflexivity].
    destruct H as [n' [? ?]].
    exists n'.
    split; auto; etransitivity; eauto.
  + (* sat_sepcon *)
    intros.
    pose proof Korder_PreOrder M as H_PreOrder.
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
    pose proof Korder_PreOrder M as H_PreOrder.
    rewrite UpwardsSemantics.sat_wand.
    split; intros.
    - rename m0 into m'.
      destruct H1 as [m2' [? ?]].
      destruct (UpwardsSemantics.join_Korder M _ _ _ _ m1 H3 H0) as [m2'' [? ?]]; [reflexivity |].
      eapply sat_mono; eauto.
      eapply sat_mono; eauto.
    - apply (H m m1 m2); auto.
      * reflexivity.
      * exists m2; split; auto.
        reflexivity.
Defined.
