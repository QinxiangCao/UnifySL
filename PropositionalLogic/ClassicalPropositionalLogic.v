Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Definition reduce {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L}: relation expr:=
  clos_refl_trans _
   (propag_reduce
     (relation_disjunction
        ImpNegAsPrime.atomic_reduce
        (relation_disjunction
          ReduceIff.atomic_reduce
          ReduceFalse.atomic_reduce))).

Class ClassicalPropositionalLogic (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) := {
  syntactic_reduction_rule1: forall x y, reduce x y -> |-- x -> |-- y;
  syntactic_reduction_rule2: forall x y, reduce x y -> |-- y -> |-- x;
  modus_ponens: forall x y, |-- (x --> y) -> |-- x -> |-- y;
  axiom1: forall x y, |-- (x --> (y --> x));
  axiom2: forall x y z, |-- ((x --> y --> z) --> (x --> y) --> (x --> z));
  axiom3: forall x y, |-- ((~~ y --> x) --> (~~ y --> ~~ x) --> y);
  true_provable: provable TT
}.

Lemma imp_refl: forall (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} (x: expr), |-- x --> x.
Proof.
  intros.
  pose proof axiom2 x (x --> x) x.
  pose proof axiom1 x (x --> x).
  pose proof axiom1 x x.
  pose proof modus_ponens _ _ H H0.
  pose proof modus_ponens _ _ H2 H1.
  auto.
Qed.

Lemma add_imp_left: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} (x y: expr), |-- x -> |-- y --> x.
Proof.
  intros.
  pose proof axiom1 x y.
  eapply modus_ponens; eauto.
Qed.

Lemma imp_trans: forall {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L} {cpGamma: ClassicalPropositionalLogic L Gamma} (x y z: expr), |-- x --> y -> |-- y --> z -> |-- x --> z.
Proof.
  intros.
  pose proof add_imp_left _ x H0.
  pose proof axiom2 x y z.
  pose proof modus_ponens _ _ H2 H1.
  pose proof modus_ponens _ _ H3 H.
  auto.
Qed.

Module ClassicalPropositionalLogic.
Section ClassicalPropositionalLogic.

Context (Var: Type).

Inductive provable: @expr (PropositionalLanguage.L Var) -> Prop :=
| syntactic_reduction_rule1: forall x y, reduce x y -> provable x -> provable y
| syntactic_reduction_rule2: forall x y, reduce x y -> provable y -> provable x
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| axiom3: forall x y, provable ((~~ y --> x) --> (~~ y --> ~~ x) --> y)
| true_provable: provable TT.
(* Elliott Mendelson, Introduction to Mathematical Logic, Second Edition (New York: D. Van Nostrand, 1979) *)

Instance AG: AxiomaticProofTheory.AxiomaticProofTheory (PropositionalLanguage.L Var) :=
  AxiomaticProofTheory.Build_AxiomaticProofTheory (PropositionalLanguage.L Var) provable.

Instance G: ProofTheory (PropositionalLanguage.L Var) := AxiomaticProofTheory.G AG.

Instance cpG: ClassicalPropositionalLogic (PropositionalLanguage.L Var) G.
Proof.
  constructor.
  + apply syntactic_reduction_rule1.
  + apply syntactic_reduction_rule2.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
  + apply axiom3.
  + apply true_provable.
Qed.

End ClassicalPropositionalLogic.
End ClassicalPropositionalLogic.

