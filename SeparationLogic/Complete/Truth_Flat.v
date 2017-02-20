Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.HenkinCompleteness.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.SeparationLogic.Complete.ContextProperty_Flat.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section TruthLemma.

Context {L: Language}
        {nL: NormalLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {Gamma: ProofTheory L}
        {nGamma: NormalProofTheory L Gamma}
        {mpGamma: MinimunPropositionalLogic L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {J: Join (Kworlds M)}
        {SM: Semantics L MD}
        {fsSM: SeparatingSemantics L MD M SM}.

Context (P: context -> Prop)
        (rel: bijection (Kworlds M) (sig P)).

Hypothesis H_R: forall m n Phi Psi, rel m Phi -> rel n Psi -> (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).

Hypothesis H_J: forall m1 m2 m Phi1 Phi2 Phi, rel m1 Phi1 -> rel m2 Phi2 -> rel m Phi -> (join m1 m2 m <-> context_join (proj1_sig Phi1) (proj1_sig Phi2) (proj1_sig Phi)).

Lemma truth_lemma_sepcon
      (DER: at_least_derivable_closed P)
      (LIN_SL: Linderbaum_sepcon_left P)
      (LIN_SR: Linderbaum_sepcon_right P)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x * y <-> proj1_sig Phi (x * y)).
Proof.
  intros.
  rewrite sat_sepcon.
  split; intros.
  + destruct H0 as [m1 [m2 [? [? ?]]]].
    destruct (im_bij _ _ rel m1) as [Phi1 ?].
    destruct (im_bij _ _ rel m2) as [Phi2 ?].
    erewrite IHx in H1 by eauto.
    erewrite IHy in H2 by eauto.
    erewrite H_J in H0 by eauto.
    rewrite derivable_closed_element_derivable by (apply DER, (proj2_sig Phi)).
    apply H0.
    - rewrite <- derivable_closed_element_derivable by (apply DER, (proj2_sig Phi1)); auto.
    - rewrite <- derivable_closed_element_derivable by (apply DER, (proj2_sig Phi2)); auto.
  + rewrite derivable_closed_element_derivable in H0 by (apply DER, (proj2_sig Phi)).
    assert (context_join (Union _ empty_context (Singleton _ x))
             (Union _ empty_context (Singleton _ y)) (proj1_sig Phi)).
    Focus 1. {
      hnf; intros.
      rewrite deduction_theorem, <- provable_derivable in H1, H2.
      rewrite <- H1, <- H2.
      auto.
    } Unfocus.
    apply LIN_SL in H1.
    destruct H1 as [Phi1 [? ?]].
    apply LIN_SR in H2.
    destruct H2 as [Phi2 [? ?]].
    destruct (su_bij _ _ rel Phi1) as [m1 ?].
    destruct (su_bij _ _ rel Phi2) as [m2 ?].
    exists m1, m2.
    erewrite H_J, IHx, IHy by eauto.
    split; [| split]; auto.
    - apply H1; right; constructor.
    - apply H2; right; constructor.
Qed.

Lemma truth_lemma_wand
      (DER: at_least_derivable_closed P)
      (LIN_DER: Linderbaum_derivable P)
      (LIN_SR: Linderbaum_sepcon_right P)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x -* y <-> proj1_sig Phi (x -* y)).
Proof.
  intros.
  rewrite sat_wand.
  split; intros.
  + rewrite derivable_closed_element_derivable by (apply DER, (proj2_sig Phi)); auto.
    rewrite <- wand_deduction_theorem.
    apply NNPP; intro.
    apply LIN_DER in H1.
    destruct H1 as [Phi2 [? ?]].
    apply context_sepcon_context_join' in H1.
    apply H2; clear H2.
    rewrite <- derivable_closed_element_derivable by (apply DER, (proj2_sig Phi2)); auto.
    apply LIN_SR in H1.
    destruct H1 as [Phi1 [? ?]].
    destruct (su_bij _ _ rel Phi1) as [m1 ?].
    destruct (su_bij _ _ rel Phi2) as [m2 ?].
    erewrite <- IHy by eauto.
    erewrite <- H_J in H2 by eauto.
    apply (H0 _ _ H2).
    erewrite IHx by eauto.
    apply H1; right; constructor.
  + destruct (im_bij _ _ rel m1) as [Phi1 ?].
    destruct (im_bij _ _ rel m2) as [Phi2 ?].
    erewrite IHy by eauto.
    erewrite IHx in H2 by eauto.
    erewrite H_J in H1 by eauto.
    rewrite derivable_closed_element_derivable in H0 by (apply DER, (proj2_sig Phi)).
    rewrite derivable_closed_element_derivable in H2 by (apply DER, (proj2_sig Phi1)).
    rewrite derivable_closed_element_derivable by (apply DER, (proj2_sig Phi2)).
    specialize (H1 _ _ H0 H2).
    rewrite provable_wand_sepcon_modus_ponens1 in H1; auto.
Qed.

Context {s'L: SeparationEmpLanguage L}
        {eGamma: SeparationEmpLogic L Gamma}
        {feSM: EmpSemantics L MD M SM}.

Lemma truth_lemma_emp
      (DER: at_least_derivable_closed P):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= emp <-> proj1_sig Phi emp).
Proof.
  intros.
  rewrite sat_emp.
  split; intros.
  + rewrite derivable_closed_element_derivable by (apply DER, (proj2_sig Phi)); auto.
    rewrite <- (provable_wand_sepcon_modus_ponens1 emp).
    rewrite <- sepcon_emp_l.
Qed.

End TruthLemma.