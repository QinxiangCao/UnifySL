Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.WeakClassical.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.

Class SystemK (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} := {
  axiom_K: forall x y, |-- boxp (x --> y) --> (boxp x --> boxp y); (* a.k.a. Distribution Axiom *)
  rule_N: forall x, |-- x -> |-- boxp x (* a.k.a. Necessitation Rule *)
}.

Class SystemT (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {KmGamma: SystemK L Gamma} := {
  axiom_T: forall x, |-- boxp x --> x
}.

Class System4 (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {KmGamma: SystemK L Gamma} {TmGamma: SystemT L Gamma}:= {
  axiom_4: forall x, |-- boxp x --> boxp (boxp x)
}.

Class SystemD (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} {KmGamma: SystemK L Gamma} := {
  axiom_D: forall x, |-- boxp x --> diamondp x
}.

Class SystemB (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} {KmGamma: SystemK L Gamma} := {
  axiom_B: forall x, |-- x --> boxp (diamondp x)
}.

Class System5 (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} {KmGamma: SystemK L Gamma} {TmGamma: SystemT L Gamma} {s4mGamma: System4 L Gamma}:= {
  axiom_5: forall x, |-- diamondp x --> boxp (diamondp x)
}.

Section ModalLogic.

Context {L: Language}
        {nL: NormalLanguage L}
        {pL: PropositionalLanguage L}
        {mL: ModalLanguage L}
        {Gamma: ProofTheory L}
        {nGamma: NormalProofTheory L Gamma}
        {mpGamma: MinimunPropositionalLogic L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {KmGamma: SystemK L Gamma}.

Lemma derivable_axiom_K: forall Phi x y,
  Phi |-- boxp (x --> y) --> (boxp x --> boxp y).
Proof.
  intros.
  apply deduction_weaken0.
  apply axiom_K.
Qed.

Lemma deduction_axiom_K: forall Phi x y,
  Phi |-- boxp (x --> y) ->
  Phi |-- boxp x --> boxp y.
Proof.
  intros.
  eapply deduction_modus_ponens; eauto.
  apply derivable_axiom_K.
Qed.

Lemma derivable_axiom_T {TmGamma: SystemT L Gamma}: forall Phi x ,
  Phi |-- boxp x --> x.
Proof.
  intros.
  apply deduction_weaken0.
  apply axiom_T.
Qed.

Lemma deduction_axiom_T {TmGamma: SystemT L Gamma}: forall Phi x ,
  Phi |-- boxp x ->
  Phi |-- x.
Proof.
  intros.
  eapply deduction_modus_ponens; eauto.
  apply derivable_axiom_T.
Qed.

End ModalLogic.

