Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.SeparationLogic.UpwardsSemantics.
Require Import Logic.PropositionalLogic.IntuitionisticPropositionalLogic.
Require Import Logic.SeparationLogic.SeparationLogic.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.
Local Open Scope SeparationLogic.
Local Open Scope KripkeSemantics.

Lemma sound_sepcon_comm {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {usSM: UpwardsSemantics L MD M SM}:
  forall x y: expr,
    forall m,
      KRIPKE: M, m |= x * y --> y * x.
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_sepcon in H0 |- *; intros.
  destruct H0 as [m0 [m1 [m2 [? [? [? ?]]]]]].
  exists m0, m2, m1.
  split; [| split]; auto.
  apply join_comm; auto.
Qed.

Lemma sound_sepcon_assoc {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M} {uSA: UpwardsClosedSeparationAlgebra MD M} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {usSM: UpwardsSemantics L MD M SM}:
  forall x y z: expr,
    forall m,
      KRIPKE: M, m |= x * (y * z) <--> (x * y) * z.
Proof.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  unfold iffp.
  rewrite sat_andp.
  split; intros.
  + rewrite sat_impp; intros.
    rewrite sat_sepcon in H0.
    destruct H0 as [n' [mx' [myz' [? [? [? ?]]]]]].
    rewrite sat_sepcon in H3.
    destruct H3 as [myz'' [my'' [mz'' [? [? [? ?]]]]]].
    apply join_comm in H1.
    apply join_comm in H4.
    assert (mx' <= mx') by reflexivity.
    destruct (join_Korder_up _ _ _ _ _ H1 H3 H7) as [n'' [? ?]].
    destruct (join_assoc mz'' my'' mx' myz'' n'' H4 H8) as [mxy'' [? ?]].
    apply join_comm in H10.
    apply join_comm in H11.
    rewrite sat_sepcon.
    exists n'', mxy'', mz''.
    split; [| split; [| split]]; auto.
    - etransitivity; eauto.
    - rewrite sat_sepcon.
      exists mxy'', mx', my''.
      split; [| split; [| split]]; auto.
      reflexivity.
  + rewrite sat_impp; intros.
    rewrite sat_sepcon in H0.
    destruct H0 as [n' [mxy' [mz' [? [? [? ?]]]]]].
    rewrite sat_sepcon in H2.
    destruct H2 as [mxy'' [mx'' [my'' [? [? [? ?]]]]]].
    assert (Korder mz' mz') by reflexivity.
    destruct (join_Korder_up _ _ _ _ _ H1 H2 H7) as [n'' [? ?]].
    destruct (join_assoc mx'' my'' mz' mxy'' n'' H4 H8) as [myz'' [? ?]].
    rewrite sat_sepcon.
    exists n'', mx'', myz''.
    split; [| split; [| split]]; auto.
    - etransitivity; eauto.
    - rewrite sat_sepcon.
      exists myz'', my'', mz'.
      split; [| split; [| split]]; auto.
      reflexivity.
Qed.

Lemma sound_wand_sepcon_adjoint {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {usSM: UpwardsSemantics L MD M SM}:
  forall x y z: expr,
   (forall m, KRIPKE: M, m |= x * y --> z) <-> (forall m, KRIPKE: M, m |= x --> (y -* z)).
Proof.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  split; intro.
  + assert (ASSU: forall m0 m1 m2 m, Korder m m0 -> join m1 m2 m0 -> KRIPKE: M, m1 |= x -> KRIPKE: M, m2 |= y -> KRIPKE: M, m |= z).
    Focus 1. {
      intros.
      specialize (H m).
      rewrite sat_impp in H.
      apply (H m); [reflexivity |].
      rewrite sat_sepcon.
      exists m0, m1, m2; auto.
    } Unfocus.
    clear H.
    intros.
    rewrite sat_impp; intros.
    rewrite sat_wand; intros.
    apply (ASSU m2 n m1 m2); auto.
    reflexivity.
  + assert (ASSU: forall m1 m2 m, join m m1 m2 -> KRIPKE: M, m |= x -> KRIPKE: M, m1 |= y -> KRIPKE: M, m2 |= z).
    Focus 1. {
      intros.
      specialize (H m).
      rewrite sat_impp in H.
      revert m1 m2 H0 H2.
      rewrite <- sat_wand.
      apply (H m); [reflexivity | auto].
    } Unfocus.
    intros.
    rewrite sat_impp; intros.
    rewrite sat_sepcon in H1.
    destruct H1 as [m0 [m1 [m2 [? [? [? ?]]]]]].
    pose proof (ASSU m2 m0 m1 H2 H3 H4).
    eapply sat_mono; eauto.
Qed.

Lemma sound_sepcon_mono {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {usSM: UpwardsSemantics L MD M SM}:
  forall x1 x2 y1 y2: expr,
   (forall m, KRIPKE: M, m |= x1 --> x2) ->
   (forall m, KRIPKE: M, m |= y1 --> y2) ->
   (forall m, KRIPKE: M, m |= x1 * y1 --> x2 * y2).
Proof.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  assert (ASSUx: forall m, KRIPKE: M, m |= x1 -> KRIPKE: M, m |= x2).
  Focus 1. {
    intros.
    specialize (H m0).
    rewrite sat_impp in H.
    apply (H m0); [reflexivity | auto].
  } Unfocus.
  assert (ASSUy: forall m, KRIPKE: M, m |= y1 -> KRIPKE: M, m |= y2).
  Focus 1. {
    intros.
    specialize (H0 m0).
    rewrite sat_impp in H0.
    apply (H0 m0); [reflexivity | auto].
  } Unfocus.
  rewrite sat_impp; intros.
  rewrite sat_sepcon in H2 |- *.
  destruct H2 as [m0 [m1 [m2 [? [? [? ?]]]]]].
  exists m0, m1, m2; auto.
Qed.

Lemma sound_sepcon_emp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {uSL: UnitarySeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M} {USA: UnitarySeparationAlgebra MD M} {uSA: UpwardsClosedSeparationAlgebra MD M} {uUSA: UpwardsClosedUnitarySeparationAlgebra MD M} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {usSM: UpwardsSemantics L MD M SM} {uUsSM: UnitaryUpwardsSemantics L MD M SM}:
  forall x: expr,
    forall m, KRIPKE: M, m |= x * emp <--> x.
Proof.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  unfold iffp.
  rewrite sat_andp.
  split.
  + rewrite sat_impp; intros.
    clear m H.
    rewrite sat_sepcon in H0.
    destruct H0 as [m'' [m' [u [? [? [? ?]]]]]].
    rewrite sat_emp in H2.
    destruct H2 as [u' [? ?]].
    destruct (join_Korder_up _ _ _ m' u' H0) as [m''' [? ?]]; [reflexivity | auto |].
    apply join_comm in H4.
    rewrite unit_spec in H3.
    apply H3 in H4.
    subst m'''.
    eapply sat_mono; eauto.
    eapply sat_mono; eauto.
  + rewrite sat_impp; intros.
    rewrite sat_sepcon.
    destruct (unit_exists n) as [u [? ?]].
    exists n, n, u.
    split; [| split; [| split]]; auto.
    - reflexivity.
    - apply join_comm; auto.
    - rewrite sat_emp.
      exists u; split; auto.
      reflexivity.
Qed.

Lemma sound_sepcon_elim {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M} {GC: GarbageCollectSeparationAlgebra MD M} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {usSM: UpwardsSemantics L MD M SM}:
  forall x y: expr,
    forall m, KRIPKE: M, m |= x * y --> x.
Proof.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  rewrite sat_impp; intros.
  rewrite sat_sepcon in H0.
  destruct H0 as [m0 [m1 [m2 [? [? [? ?]]]]]].
  apply join_has_order1 in H1.
  eapply sat_mono; eauto.
  eapply sat_mono; eauto.
Qed.

