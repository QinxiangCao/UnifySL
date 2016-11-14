Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.MinimunLogic.ContextProperty.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.IntuitionisticPropositionalLogic.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Class GodelDummettPropositionalLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} := {
  impp_choice: forall x y, |-- (x --> y) || (y --> x)
}.

Lemma derivable_impp_choice: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {wpGamma: GodelDummettPropositionalLogic L Gamma} (Phi: context) (x y: expr),
  Phi |-- (x --> y) || (y --> x).
Proof.
  intros.
  pose proof impp_choice x.
  apply deduction_weaken0; auto.
Qed.

Lemma derivable_weak_excluded_middle: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {wpGamma: GodelDummettPropositionalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- ~~ x || ~~ ~~ x.
Proof.
  intros.
  pose proof derivable_impp_choice Phi x (~~ x).
  
  assert (Phi |-- (x --> ~~ x) --> (x --> FF)).
  Focus 1. {
    rewrite <- deduction_theorem.
    rewrite <- deduction_theorem.
    eapply deduction_weaken with (Union _ (Union _ (Union _ Phi (Singleton _ (x --> ~~ x))) (Singleton _ x)) (Singleton _ x)).
    + intros y ?.
      destruct H0; [| right; auto].
      destruct H0; [| right; auto].
      left; auto.
    + rewrite deduction_theorem.
      rewrite deduction_theorem.
      apply derivable_assum1.
  } Unfocus.
  assert (Phi |-- (~~ x --> x) --> (~~ x --> FF)).
  Focus 1. {
    rewrite <- deduction_theorem.
    pose proof derivable_assum1 Phi (~~ x --> x).
    set (Psi := Union expr Phi (Singleton expr (~~ x --> x))) in H1 |- *; clearbody Psi.
    rewrite <- deduction_theorem in H1 |- *.
    pose proof derivable_assum1 Psi (~~ x).
    pose proof deduction_modus_ponens _ _ _ H1 H2.
    auto.
  } Unfocus.

  rewrite <- deduction_theorem in H0, H1.
  apply (deduction_orp_intros1 _ _ (~~ x --> FF)) in H0.
  apply (deduction_orp_intros2 _ (x --> FF)) in H1.
  rewrite deduction_theorem in H0, H1.
  pose proof deduction_orp_elim _ _ _ _ H0 H1.
  pose proof deduction_modus_ponens _ _ _ H H2.
  auto.
Qed.
(*
Lemma DCS_negp_iff: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} (Phi: context),
  derivable_closed Phi ->
  orp_witnessed Phi ->
  consistent Phi ->
  (forall x: expr, Phi x <-> ~ Phi (~~ x)).
Proof.
  intros.
  split; intros.
  + rewrite derivable_closed_element_derivable in H2 |- * by auto.
    intro.
    pose proof deduction_modus_ponens _ _ _ H2 H3.
    rewrite consistent_spec in H1; apply H1; auto.
  + rewrite derivable_closed_element_derivable in H2 |- * by auto.
    pose proof derivable_excluded_middle Phi x.
    specialize (H0 x (~~ x)).
    rewrite derivable_closed_element_derivable in H0 by auto.
    apply H0 in H3.
    destruct H3; rewrite derivable_closed_element_derivable in H3 by auto; auto.
    tauto.
Qed.
*)
Module GodelDummettPropositionalLogic.
Section GodelDummettPropositionalLogic.

Context (Var: Type).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
| impp_choice: forall x y, provable ((x --> y) || (y --> x)).

Instance G: ProofTheory L := Build_AxiomaticProofTheory provable.

Instance nG: NormalProofTheory L G := Build_nAxiomaticProofTheory provable.

Instance mpG: MinimunPropositionalLogic L G.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance ipG: IntuitionisticPropositionalLogic L G.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.

Instance wpG: GodelDummettPropositionalLogic L G.
Proof.
  constructor.
  apply impp_choice.
Qed.

End GodelDummettPropositionalLogic.
End GodelDummettPropositionalLogic.

