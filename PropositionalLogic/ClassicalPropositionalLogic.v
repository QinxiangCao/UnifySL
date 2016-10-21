Require Import Logic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope PropositionalLogic.

Section ClassicalPropositionalLogic.

Context {Var: Type}.

Definition reduce: expr Var -> expr Var -> Prop :=
  syntax_reduce
   (fun x y =>
      ImpNegAsPrime.atomic_reduce x y \/
      ReduceIff.atomic_reduce x y \/
      ReduceTrueFalse.atomic_reduce x y).

Inductive provable: expr Var -> Prop :=
| syntactic_reduction_rule: forall x y, reduce x y -> provable x -> provable y
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| axiom3: forall x y, provable ((~~ y --> x) --> (~~ y --> ~~ x) --> y).

End ClassicalPropositionalLogic.

Instance ClassicalPropositionLogic (Var: Type): ProofTheory (PropositionalLanguage Var) :=
  AxiomaticProofTheory_ProofTheory
   (AxiomaticProofTheory.Build_ProofTheory (PropositionalLanguage Var) provable).
