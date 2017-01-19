Require Import Coq.Logic.ProofIrrelevance.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.

Class PropositionalLanguage (L: Language) {nL: NormalLanguage L}: Type := {
  andp : expr -> expr -> expr;
  orp : expr -> expr -> expr;
  falsep: expr
}.

Definition negp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} (x: expr): expr := impp x falsep.
Definition iffp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} (x y: expr): expr := andp (impp x y) (impp y x).
Definition truep {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L}: expr := impp falsep falsep.

Module PropositionalLanguageNotation.

Notation "x && y" := (andp x y) (at level 40, left associativity) : syntax.
Notation "x || y" := (orp x y) (at level 50, left associativity) : syntax.
Notation "x <--> y" := (iffp x y) (at level 60, no associativity) : syntax.
Notation "~~ x" := (negp x) (at level 35) : syntax.
Notation "'FF'" := falsep : syntax.
Notation "'TT'" := truep : syntax.

End PropositionalLanguageNotation.

Definition orp_witnessed {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L}: context -> Prop :=
  fun Phi => forall x y, Phi (orp x y) -> Phi x \/ Phi y.

