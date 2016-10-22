Require Import Logic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope PropositionalLogic.

Section ClassicalPropositionalLogicSection.

Context {L: PropositionalLanguage}.

Definition reduce: relation expr:=
  clos_refl_trans _
   (prop_congr
     (relation_disjunction
        ImpNegAsPrime.atomic_reduce
        (relation_disjunction
          ReduceIff.atomic_reduce
          ReduceTrueFalse.atomic_reduce))).

Class ClassicalPropositionalLogic := {
  provable: expr -> Prop;
  syntactic_reduction_rule: forall x y, reduce x y -> provable x -> provable y;
  modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y;
  axiom1: forall x y, provable (x --> (y --> x));
  axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z));
  axiom3: forall x y, provable ((~~ y --> x) --> (~~ y --> ~~ x) --> y)
}.

Instance ClassicalPropositionalLogic_ProofTheory (Gamma: ClassicalPropositionalLogic):
  ProofTheory (PropositionalLanguage_Language L) :=
  AxiomaticProofTheory_ProofTheory
   (AxiomaticProofTheory.Build_ProofTheory (PropositionalLanguage_Language L) provable).

End ClassicalPropositionalLogicSection.

Module ClassicalPropositionalLogic.

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
