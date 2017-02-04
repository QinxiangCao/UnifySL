Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.ModalLogic.Semantics.Kripke.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.
Import KripkeModelFamilyNotation.

Lemma sound_axiom_K {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L}  {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM} {kmSM: KripkeModalSemantics L MD M SM}:
  forall x y (m: Kworlds M),
    KRIPKE: M, m |= boxp (x --> y) --> (boxp x --> boxp y).
Proof.
  intros.
  rewrite !sat_impp, !sat_boxp.
  intros.
  specialize (H _ H1).
  specialize (H0 _ H1).
  rewrite sat_impp in H.
  auto.
Qed.

Lemma sound_rule_N {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L}  {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM} {kmSM: KripkeModalSemantics L MD M SM}:
  forall x,
    (forall (m: Kworlds M), KRIPKE: M, m |= x) ->
    (forall (m: Kworlds M), KRIPKE: M, m |= boxp x).
Proof.
  intros.
  rewrite sat_boxp.
  intros; apply H; auto.
Qed.
