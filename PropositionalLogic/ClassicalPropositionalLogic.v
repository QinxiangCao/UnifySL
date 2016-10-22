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

Implicit Arguments ClassicalPropositionalLogic.

Local Open Scope logic_base.

Existing Instance ClassicalPropositionalLogic_ProofTheory.

Lemma imp_refl: forall {L: PropositionalLanguage} {Gamma: ClassicalPropositionalLogic L} (x: expr), |-- (x --> x).
Proof.
  intros.
  pose proof axiom2 x (x --> x) x.
  pose proof axiom1 x (x --> x).
  pose proof axiom1 x x.
  pose proof modus_ponens _ _ H H0.
  pose proof modus_ponens _ _ H2 H1.
  auto.
Qed.

Module ClassicalPropositionalLogic.
Section ClassicalPropositionalLogic.
Context (Var: Type).

Definition CPL := PropositionalLanguage.PropositionalLanguage Var.
Existing Instance CPL.

Inductive provable: PropositionalLanguage.expr Var -> Prop :=
| syntactic_reduction_rule: forall x y: PropositionalLanguage.expr Var, reduce x y -> provable x -> provable y
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| axiom3: forall x y, provable ((~~ y --> x) --> (~~ y --> ~~ x) --> y).

Instance ClassicalPropositionLogic: ClassicalPropositionalLogic _ :=
  Build_ClassicalPropositionalLogic provable syntactic_reduction_rule modus_ponens axiom1 axiom2 axiom3.

End ClassicalPropositionalLogic.
End ClassicalPropositionalLogic.

