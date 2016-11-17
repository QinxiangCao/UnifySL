Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.DownwardsSemantics.
Require Import Logic.SeparationLogic.UpwardsSemantics.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.
Local Open Scope SeparationLogic.

Definition d2u_sSM {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L} {pkSM: PreKripkeSemantics L SM} {kiSM: KripkeIntuitionisticSemantics L SM} (dsSM: DownwardsSemantics L SM): UpwardsSemantics L SM.
  refine (Build_UpwardsSemantics _ _ _ _ _ _ _ (fun M (m1 m2 m: Kworlds M) => exists n1 n2, Korder n1 m1 /\ Korder n2 m2 /\ DownwardsSemantics.join n1 n2 m) _ _ _ _ _).
  + (* join_comm *)
    intros.
    destruct H as [n1 [n2 [? [? ?]]]].
    exists n2, n1.
    split; [| split]; auto.
    apply DownwardsSemantics.join_comm; auto.
  + (* join_assoc *)
    admit.
  + (* join_Korder *)
    intros.
    pose proof Korder_PreOrder M as H_PreOrder.
    exists m.
    split; [| reflexivity].
    destruct H as [m1' [m2' [? [? ?]]]].
    exists m1', m2'.
    split; [| split]; auto; etransitivity; eauto.     
  + (* sat_sepcon *)
    intros.
    pose proof Korder_PreOrder M as H_PreOrder.
    rewrite DownwardsSemantics.sat_sepcon.
    split; intros.
    - destruct H as [m1 [m2 [? [? ?]]]].
      exists m, m1, m2.
      split; [reflexivity |].
      split; [| split]; auto.
      exists m1, m2.
      split; [| split]; auto; reflexivity.
    - destruct H as [m0 [m1 [m2 [? [[n1 [n2 [? [? ?]]]] [? ?]]]]]].
      destruct (DownwardsSemantics.join_Korder M m0 m _ _ H2 H) as [n1' [n2' [? [? ?]]]].
      exists n1', n2'.
      split; [| split]; auto; eapply sat_mono; eauto; eapply sat_mono; eauto.
  + (* sat_wand *)
    intros.
    pose proof Korder_PreOrder M as H_PreOrder.
    rewrite DownwardsSemantics.sat_wand.
    split; intros.
    - destruct H0 as [m' [m1' [? [? ?]]]].
      apply (H  _ _ _ H0 H3).
      eapply sat_mono; eauto.
    - apply (H m1 m2); auto.
      exists m0, m1.
      split; [| split]; auto.
      reflexivity.
Defined.
