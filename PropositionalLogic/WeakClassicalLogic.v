(* M. Dummett. A propositional calculus with denumerable matrix. J. Symbolic Logic, 24(2):97–106, 1959. *)
(* K. G¨odel. On the intuitionistic propositional calculus. In S. Feferman, J. W. D. Jr, S. C. Kleene, G. H. Moore, R. M. Solovay, and J. van Heijenoort, editors, Collected Works, volume 1. Oxford University Press, 1986. *)

Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.MinimunLogic.ContextProperty.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.IntuitionisticPropositionalLogic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class WeakClassicalLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} := {
  weak_excluded_middle: forall x, |-- ~~ x || ~~ ~~ x
}.

Lemma derivable_weak_excluded_middle: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {wpGamma: WeakClassicalLogic L Gamma} (Phi: context) (x: expr),
  Phi |-- ~~ x || ~~ ~~ x.
Proof.
  intros.
  pose proof weak_excluded_middle x.
  apply deduction_weaken0; auto.
Qed.

Module WeakClassicalLogic.
Section WeakClassicalLogic.

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
| weak_excluded_middle: forall x, provable (~~ x || ~~ ~~ x).

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

Instance wcG: WeakClassicalLogic L G.
Proof.
  constructor.
  apply weak_excluded_middle.
Qed.

End WeakClassicalLogic.
End WeakClassicalLogic.

