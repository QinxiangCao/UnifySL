Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.DownUpSemantics_Fail.
Require Import Logic.PropositionalLogic.IntuitionisticPropositionalLogic.
Require Import Logic.SeparationLogic.SeparationLogic.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.
Local Open Scope SeparationLogic.

Lemma sound_sepcon_comm {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L} {pkS: PreKripkeSemantics L SM} {kiSM: KripkeIntuitionisticSemantics L SM} {dusSM: DownUpSemantics L SM}:
  forall x y: expr,
    forall M m,
      KRIPKE: M, m |= x * y --> y * x.
Proof.
  intros.
  pose proof Korder_PreOrder M as H_PreOrder.
  rewrite sat_impp; intros.
  rewrite sat_sepcon in H0 |- *; intros.
  destruct H0 as [m0 [m1 [m2 [? [? [? ?]]]]]].
  exists m0, m2, m1.
  split; [| split; [| split]]; auto.
  apply join_comm; auto.
Qed.

Lemma sound_sepcon_assoc {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L} {pkS: PreKripkeSemantics L SM} {kiSM: KripkeIntuitionisticSemantics L SM} {dusSM: DownUpSemantics L SM}:
  forall x y z: expr,
    forall M m,
      KRIPKE: M, m |= x * (y * z) <--> (x * y) * z.
Proof.
  intros.
  unfold iffp.
  rewrite sat_andp.
  split; intros.
  + rewrite sat_impp; intros.
    rewrite sat_sepcon in H0.
    destruct H0 as [m0 [m1 [m2 [? [? [? ?]]]]]].
    (* fail *)
Abort.