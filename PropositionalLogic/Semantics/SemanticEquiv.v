Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Logic.PropositionalLogic.Semantics.Kripke.
Require Logic.PropositionalLogic.Semantics.Trivial.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section SemanticEquiv.

Context {L: Language}
        {nL: NormalLanguage L}
        {pL: PropositionalLanguage L}
        {MD: Model}
        {SM: Semantics L MD}.

Lemma eqR_KripkeIntuitionistic: @Kripke.KripkeIntuitionisticSemantics L MD (unit_kMD _) tt eq SM.
Proof.
  constructor.
  intros; hnf; intros.
  hnf in H; subst.
  auto.
Qed.

Lemma Trivial2Kripke {tpSM: Trivial.TrivialPropositionalSemantics L MD SM}: 
  @Kripke.KripkePropositionalSemantics L nL pL MD (unit_kMD _) tt eq SM.
Proof.
  constructor.
  + intros.
    change (@Kdenotation L MD (unit_kMD _) tt SM) with denotation.
    rewrite Trivial.denote_impp.
    split; unfold Included, Ensembles.In; intros.
    - hnf; intros.
      hnf in H0; subst.
      apply H, H1.
    - hnf; intros; apply (H x0); auto.
      reflexivity.
  + intros.
    change (@Kdenotation L MD (unit_kMD _) tt SM) with denotation.
    rewrite Trivial.denote_andp.
    reflexivity.
  + intros.
    change (@Kdenotation L MD (unit_kMD _) tt SM) with denotation.
    rewrite Trivial.denote_orp.
    reflexivity.
  + intros.
    change (@Kdenotation L MD (unit_kMD _) tt SM) with denotation.
    rewrite Trivial.denote_falsep.
    reflexivity.
Qed.

End SemanticEquiv.