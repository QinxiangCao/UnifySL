Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Trivial.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Lemma sound_modus_ponens {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM}:
  forall x y m,
    m |= (x --> y) -> m |= x -> m |= y.
Proof.
  intros.
  rewrite sat_impp in H.
  apply H; auto.
Qed.

Lemma sound_axiom1 {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM}:
  forall x y m,
    m |= x --> y --> x.
Proof.
  intros.
  rewrite !sat_impp.
  intros ? ?; auto.
Qed.

Lemma sound_axiom2 {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM}:
  forall x y z m,
    m |= (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
  intros.
  rewrite !sat_impp.
  intros ? ? ?.
  specialize (H H1).
  specialize (H0 H1).
  auto.
Qed.

Lemma sound_andp_intros {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM}:
  forall x y m,
    m |= x --> y --> x && y.
Proof.
  intros.
  rewrite !sat_impp, sat_andp.
  simpl; intros ? ?.
  auto.
Qed.

Lemma sound_andp_elim1 {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM}:
  forall x y m,
    m |= x && y --> x.
Proof.
  intros.
  rewrite !sat_impp, sat_andp.
  intros [? ?].
  auto.
Qed.

Lemma sound_andp_elim2 {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM}:
  forall x y m,
    m |= x && y --> y.
Proof.
  intros.
  rewrite !sat_impp, sat_andp.
  intros [? ?].
  auto.
Qed.

Lemma sound_orp_intros1 {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM}:
  forall x y m,
    m |= x --> x || y.
Proof.
  intros.
  rewrite !sat_impp, sat_orp.
  auto.
Qed.

Lemma sound_orp_intros2 {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM}:
  forall x y m,
      m |= y --> x || y.
Proof.
  intros.
  rewrite !sat_impp, sat_orp.
  auto.
Qed.

Lemma sound_orp_elim {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM}:
  forall x y z m,
    m |= (x --> z) --> (y --> z) --> (x || y --> z).
Proof.
  intros.
  rewrite !sat_impp, sat_orp.
  tauto.
Qed.

Lemma sound_falsep_elim {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM}:
  forall x m,
    m |= FF --> x.
Proof.
  intros.
  rewrite sat_impp, sat_falsep.
  intros [].
Qed.

Lemma sound_excluded_middle {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {SM: Semantics L MD} {tpSM: TrivialPropositionalSemantics L MD SM}:
  forall x m,
    m |= x || (x --> FF).
Proof.
  intros.
  rewrite sat_orp, sat_impp, sat_falsep.
  tauto.
Qed.
(*

*)
