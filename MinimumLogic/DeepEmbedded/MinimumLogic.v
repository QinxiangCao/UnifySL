Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Logic.MinimumLogic.DeepEmbedded.MinimumLanguage.

Local Open Scope logic_base.
Local Open Scope syntax.

Section MinimumLogic.

Context (Var: Type).

Instance L: Language := MinimumLanguage.L Var.
Instance minL: MinimumLanguage L := MinimumLanguage.minL Var.

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z)).

Instance GP: Provable L := Build_Provable L provable.

Instance GD: Derivable L := Provable2Derivable.

Instance AX: NormalAxiomatization L GP GD := Provable2Derivable_Normal.

Instance minAX: MinimumAxiomatization L GP.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Instance SC: NormalSequentCalculus L GP GD := Axiomatization2SequentCalculus_SC.

Instance bSC: BasicSequentCalculus L GD := Axiomatization2SequentCalculus_bSC.

Instance fwSC: FiniteWitnessedSequentCalculus L GD := Axiomatization2SequentCalculus_fwSC.

Instance minSC: MinimumSequentCalculus L GD := Axiomatization2SequentCalculus_minSC.

End MinimumLogic.
