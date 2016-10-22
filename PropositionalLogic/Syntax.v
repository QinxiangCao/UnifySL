Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Relations.Relation_Operators.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.
Require Import Logic.LogicBase.

Class PropositionalLanguage: Type := {
  expr: Type;
  andp : expr -> expr -> expr;
  orp : expr -> expr -> expr;
  imp : expr -> expr -> expr;
  iffp : expr -> expr -> expr;
  negp : expr -> expr;
  truep : expr;
  falsep : expr
}.

Instance PropositionalLanguage_Language (L: PropositionalLanguage): Language :=
  Build_Language expr.

Instance PropositionalLanguage__nLanguage (L: PropositionalLanguage):  NormalLanguage _ :=
  Build_NormalLanguage (PropositionalLanguage_Language L) falsep imp.

Notation "x && y" := (andp x y) (at level 40, left associativity) : PropositionalLogic.
Notation "x || y" := (orp x y) (at level 50, left associativity) : PropositionalLogic.
Notation "x --> y" := (imp x y) (at level 55, right associativity) : PropositionalLogic.
Notation "x <--> y" := (iffp x y) (at level 60, no associativity) : PropositionalLogic.
Notation "~~ x" := (negp x) (at level 35) : PropositionalLogic.
Notation "'FF'" := falsep : PropositionalLogic.
Notation "'TT'" := truep : PropositionalLogic.

Local Open Scope PropositionalLogic.

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

Instance PropositionalLanguage (Var: Type): PropositionalLanguage :=
  Build_PropositionalLanguage (expr Var) andp orp imp iffp negp truep falsep.

End PropositionalLanguage.

Inductive prop_congr {L: PropositionalLanguage} {atomic_reduce: relation expr}: relation expr :=
| atomic_step: forall x y, atomic_reduce x y -> prop_congr x y
| andp_congr: forall x1 x2 y1 y2, prop_congr x1 y1 -> prop_congr x2 y2 -> prop_congr (x1 && x2) (y1 && y2)
| orp_congr: forall x1 x2 y1 y2, prop_congr x1 y1 -> prop_congr x2 y2 -> prop_congr (x1 || x2) (y1 || y2)
| imp_congr: forall x1 x2 y1 y2, prop_congr x1 y1 -> prop_congr x2 y2 -> prop_congr (x1 --> x2) (y1 --> y2)
| iffp_congr: forall x1 x2 y1 y2, prop_congr x1 y1 -> prop_congr x2 y2 -> prop_congr (x1 <--> x2) (y1 <--> y2)
| negp_congr: forall x y, prop_congr x y -> prop_congr (~~ x) (~~ y)
.

(* Locate clos_refl_trans. *)

Arguments prop_congr {L} atomic_reduce _ _.

Module ImpNegAsPrime.

Inductive atomic_reduce {L: PropositionalLanguage}: expr -> expr -> Prop :=
| andp_reduce: forall x y, atomic_reduce (x && y) (~~ (x --> ~~ y))
| orp_reduce: forall x y, atomic_reduce (x || y) (~~ x --> y)
.

End ImpNegAsPrime.

Module ImpAndOrAsPrime.

Inductive atomic_reduce {L: PropositionalLanguage}: expr -> expr -> Prop :=
| negp_reduce: forall x, atomic_reduce (~~ x) (x --> FF)
.

End ImpAndOrAsPrime.

Module ReduceIff.

Inductive atomic_reduce {L: PropositionalLanguage}: expr -> expr -> Prop :=
| iff_reduce: forall x y, atomic_reduce (x <--> y) ((x --> y) && (y --> x)).

End ReduceIff.

Module ReduceTrueFalse.

Inductive atomic_reduce {L: PropositionalLanguage}: expr -> expr -> Prop :=
| falsep_reduce: atomic_reduce FF (~~ TT)
| truep_reduce: forall x, atomic_reduce TT (x --> x).

End ReduceTrueFalse.


