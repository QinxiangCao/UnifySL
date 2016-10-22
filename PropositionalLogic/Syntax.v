Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Relations.Relation_Operators.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.
Require Import Logic.LogicBase.

Class PropositionalLanguage (L: Language) {nL: NormalLanguage L}: Type := {
  andp : expr -> expr -> expr;
  orp : expr -> expr -> expr;
  iffp : expr -> expr -> expr;
  negp : expr -> expr;
  truep : expr
}.

Notation "x && y" := (andp x y) (at level 40, left associativity) : PropositionalLogic.
Notation "x || y" := (orp x y) (at level 50, left associativity) : PropositionalLogic.
Notation "x --> y" := (imp x y) (at level 55, right associativity) : PropositionalLogic.
Notation "x <--> y" := (iffp x y) (at level 60, no associativity) : PropositionalLogic.
Notation "~~ x" := (negp x) (at level 35) : PropositionalLogic.
Notation "'FF'" := falsep : PropositionalLogic.
Notation "'TT'" := truep : PropositionalLogic.

Local Open Scope PropositionalLogic.

Inductive prop_congr {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {atomic_reduce: relation expr}: relation expr :=
| atomic_step: forall x y, atomic_reduce x y -> prop_congr x y
| andp_congr: forall x1 x2 y1 y2, prop_congr x1 y1 -> prop_congr x2 y2 -> prop_congr (x1 && x2) (y1 && y2)
| orp_congr: forall x1 x2 y1 y2, prop_congr x1 y1 -> prop_congr x2 y2 -> prop_congr (x1 || x2) (y1 || y2)
| imp_congr: forall x1 x2 y1 y2, prop_congr x1 y1 -> prop_congr x2 y2 -> prop_congr (x1 --> x2) (y1 --> y2)
| iffp_congr: forall x1 x2 y1 y2, prop_congr x1 y1 -> prop_congr x2 y2 -> prop_congr (x1 <--> x2) (y1 <--> y2)
| negp_congr: forall x y, prop_congr x y -> prop_congr (~~ x) (~~ y)
.

(* Locate clos_refl_trans. *)

Arguments prop_congr {L} {nL} {pL} atomic_reduce _ _.

Module ImpNegAsPrime.

Inductive atomic_reduce {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L}: expr -> expr -> Prop :=
| andp_reduce: forall x y, atomic_reduce (x && y) (~~ (x --> ~~ y))
| orp_reduce: forall x y, atomic_reduce (x || y) (~~ x --> y)
.

End ImpNegAsPrime.

Module ImpAndOrAsPrime.

Inductive atomic_reduce {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L}: expr -> expr -> Prop :=
| negp_reduce: forall x, atomic_reduce (~~ x) (x --> FF)
.

End ImpAndOrAsPrime.

Module ReduceIff.

Inductive atomic_reduce {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L}: expr -> expr -> Prop :=
| iff_reduce: forall x y, atomic_reduce (x <--> y) ((x --> y) && (y --> x)).

End ReduceIff.

Module ReduceTrueFalse.

Inductive atomic_reduce {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L}: expr -> expr -> Prop :=
| falsep_reduce: atomic_reduce FF (~~ TT)
| truep_reduce: forall x, atomic_reduce TT (x --> x).

End ReduceTrueFalse.

Module PropositionalLanguage.

Inductive expr {Var: Type}: Type :=
  | andp : expr -> expr -> expr
  | orp : expr -> expr -> expr
  | imp : expr -> expr -> expr
  | iffp : expr -> expr -> expr
  | negp : expr -> expr
  | truep : expr
  | falsep : expr
  | varp : Var -> expr.

Implicit Arguments expr.

Instance L (Var: Type): Language := Build_Language (expr Var).
Instance nL (Var: Type): NormalLanguage (L Var) := Build_NormalLanguage (L Var) falsep imp.
Instance pL (Var: Type): PropositionalLanguage (L Var) := Build_PropositionalLanguage (L Var) (nL Var) andp orp iffp negp truep.

End PropositionalLanguage.

