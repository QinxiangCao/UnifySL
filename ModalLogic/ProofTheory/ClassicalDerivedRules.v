Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.ModalLogic.ProofTheory.ModalLogic.
Require Import Logic.ModalLogic.ProofTheory.RewriteClass.
Require Import Logic.ModalLogic.ProofTheory.IntuitionisticDerivedRules.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.

Section ClassicalderivedRules.

Context {L: Language}
        {nL: NormalLanguage L}
        {pL: PropositionalLanguage L}
        {mL: ModalLanguage L}
        {Gamma: ProofTheory L}
        {nGamma: NormalProofTheory L Gamma}
        {mpGamma: MinimunPropositionalLogic L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {cpGamma: ClassicalPropositionalLogic L Gamma}
        {KmGamma: SystemK L Gamma}.

Lemma diamondp_orp: forall x y, |-- diamondp (x || y) <--> (diamondp x || diamondp y).
Proof.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros; [| rewrite <- provable_derivable; apply orp_diamondp].
  unfold diamondp.
  rewrite <- demorgan_negp_andp.
  apply deduction_contrapositivePP.
  rewrite <- provable_derivable.
  rewrite <- boxp_andp.
  rewrite demorgan_negp_orp.
  apply provable_impp_refl.
Qed.

Instance PropositionalTransparentModality2StrongPropositionalTransparentModality {pmGamma: PropositionalTransparentModality L Gamma}: StrongPropositionalTransparentModality L Gamma.
Proof.
  constructor.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros; [apply derivable_axiom_K |].
  rewrite (impp2orp x y), (impp2orp (boxp x) (boxp y)).
  rewrite boxp_orp.
  apply deduction_orp_elim; [| apply derivable_orp_intros2].
  rewrite <- deduction_theorem.
  apply deduction_orp_intros1.
  apply (deduction_modus_ponens _ (boxp (x || ~~ x))).
  + apply deduction_weaken0.
    apply rule_N.
    apply excluded_middle.
  + rewrite boxp_orp.
    apply deduction_orp_elim; [| apply derivable_impp_refl].
    rewrite <- deduction_theorem.
    apply deduction_falsep_elim.
    rewrite -> deduction_theorem.
    apply derivable_assum1.
Qed.

End ClassicalderivedRules.
