Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.ModalLogic.Model.OrderedKripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.ModalLogic.Semantics.Flat.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Lemma sound_axiom_K {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L}  {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {kiM: KripkeIntuitionisticModel (Kworlds M)} {R2: KM.Relation (Kworlds M)} {ukmM: UpwardsClosedOrderedKripkeModel (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {fmSM: FlatModalSemantics L MD M SM}:
  forall x y (m: Kworlds M),
    KRIPKE: M, m |= boxp (x --> y) --> (boxp x --> boxp y).
Proof.
  intros.
  rewrite sat_impp.
  intros m' ? ?.
  rewrite sat_impp.
  intros m'' ? ?.
  rewrite sat_boxp in H0, H2 |- *.
  intros n'' ?.
  destruct (KM_relation_up _ _ _ H1 H3) as [n' [? ?]].
  specialize (H2 _ H3).
  specialize (H0 _ H5).
  rewrite sat_impp in H0.
  exact (H0 n'' H4 H2).
Qed.

Lemma sound_rule_N {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L}  {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {kiM: KripkeIntuitionisticModel (Kworlds M)} {R2: KM.Relation (Kworlds M)} {ukmM: UpwardsClosedOrderedKripkeModel (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {fmSM: FlatModalSemantics L MD M SM}:
  forall x,
    (forall (m: Kworlds M), KRIPKE: M, m |= x) ->
    (forall (m: Kworlds M), KRIPKE: M, m |= boxp x).
Proof.
  intros.
  rewrite sat_boxp.
  intros; apply H; auto.
Qed.
