Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.HenkinCompleteness.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section TruthLemma.

Context {L: Language}
        {nL: NormalLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {nGamma: NormalProofTheory L Gamma}
        {mpGamma: MinimunPropositionalLogic L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {SM: Semantics L MD}
        {kpSM: KripkePropositionalSemantics L MD M SM}.

Context (P: context -> Prop)
        (rel: bijection (Kworlds M) (sig P)).

Hypothesis H_R: forall m n Phi Psi, rel m Phi -> rel n Psi -> (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).

Lemma truth_lemma_falsep (CONSI: at_least_consistent P):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= falsep <-> proj1_sig Phi falsep).
Proof.
  intros.
  rewrite sat_falsep.
  pose proof proj2_sig Phi.
  pose proof CONSI _ H0.
  rewrite consistent_spec in H1.
  split; [intros [] |].
  intro; apply H1.
  apply derivable_assum; auto.
Qed.
        
Lemma truth_lemma_andp
      (DER: at_least_derivable_closed P)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x && y <-> proj1_sig Phi (x && y)).
Proof.
  intros.
  rewrite sat_andp.
  rewrite DCS_andp_iff by (apply DER, (proj2_sig Phi)).
  apply Morphisms_Prop.and_iff_morphism; auto.
Qed.

Lemma truth_lemma_orp
      (DER: at_least_derivable_closed P)
      (ORP: at_least_orp_witnessed P)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x || y <-> proj1_sig Phi (x || y)).
Proof.
  intros.
  rewrite sat_orp.
  rewrite DCS_orp_iff.
    2: apply DER, (proj2_sig Phi).
    2: apply ORP, (proj2_sig Phi).
  apply Morphisms_Prop.or_iff_morphism; auto.
Qed.

Lemma truth_lemma_impp
      (DER: at_least_derivable_closed P)
      (LIN_DER: Linderbaum_derivable P)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x --> y <-> proj1_sig Phi (x --> y)).
Proof.
  intros.
  rewrite sat_impp.
  split; intros.
  + rewrite derivable_closed_element_derivable by (apply DER, (proj2_sig Phi)).
    rewrite <- deduction_theorem.
    apply NNPP; intro.
    apply LIN_DER in H1.
    destruct H1 as [Psi [? ?]].
    apply H2; clear H2.
    assert (Included _ (proj1_sig Phi) (proj1_sig Psi)) by (intros ? ?; apply H1; left; auto).
    assert (proj1_sig Psi x) by (apply H1; right; constructor; auto).
    clear H1.
    destruct (su_bij _ _ rel Psi) as [n ?].
    rewrite <- derivable_closed_element_derivable by (apply DER, (proj2_sig Psi)).
    rewrite <- (IHx _ _ H1) in H3.
    rewrite <- (IHy _ _ H1).
    apply H0; auto.
    erewrite H_R by eauto.
    auto.
  + destruct (im_bij _ _ rel n) as [Psi ?].
    rewrite (IHx _ _ H3) in H2.
    rewrite (IHy _ _ H3).
    rewrite derivable_closed_element_derivable in H2 |- * by (apply DER, (proj2_sig Psi)).
    eapply deduction_modus_ponens; [exact H2 |].
    rewrite <- derivable_closed_element_derivable by (apply DER, (proj2_sig Psi)).
    erewrite H_R in H1 by eauto.
    apply H1; auto.
Qed.

End Canonical.


