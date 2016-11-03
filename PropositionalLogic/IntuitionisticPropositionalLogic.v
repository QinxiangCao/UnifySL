Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.MinimunPropositionalLogic.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Class IntuitionisticPropositionalLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) {mpGamma: MinimunPropositionalLogic L Gamma} := {
  syntactic_reduction_rule: forall x y, @reduce _ IntuitionisticReduction x y -> (|-- x <-> |-- y);
  andp_intros: forall x y, |-- x --> y --> x && y;
  andp_elim1: forall x y, |-- x && y --> x;
  andp_elim2: forall x y, |-- x && y --> y;
  orp_intros1: forall x y, |-- x --> x || y;
  orp_intros2: forall x y, |-- y --> x || y;
  orp_elim: forall x y z, |-- (x --> z) --> (y --> z) --> (x || y --> z);
  falsep_elim: forall x, |-- FF --> x
}.

