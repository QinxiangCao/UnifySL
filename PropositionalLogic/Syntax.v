Require Import Logic.LogicBase.

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

Notation "x && y" := (andp x y) (at level 40, left associativity) : PropositionalLogic.
Notation "x || y" := (orp x y) (at level 50, left associativity) : PropositionalLogic.
Notation "x --> y" := (imp x y) (at level 55, right associativity) : PropositionalLogic.
Notation "x <--> y" := (iffp x y) (at level 60, no associativity) : PropositionalLogic.
Notation "~~ x" := (negp x) (at level 35) : PropositionalLogic.
Notation "'FF'" := falsep : PropositionalLogic.
Notation "'TT'" := truep : PropositionalLogic.

Local Open Scope PropositionalLogic.

Instance PropositionalLanguage (Var: Type): Language := Build_Language (expr Var).

Instance nPropositionalLanguage (Var: Type): NormalLanguage (PropositionalLanguage Var) :=
  Build_NormalLanguage (PropositionalLanguage Var) FF imp.

Inductive syntax_reduce {Var: Type} {atomic_reduce: expr Var -> expr Var -> Prop}:  expr Var -> expr Var -> Prop :=
| atomic_step: forall x y, atomic_reduce x y -> syntax_reduce x y
| reduce_refl: forall x, syntax_reduce x x
| reduce_trans: forall x y z, syntax_reduce x y -> syntax_reduce y z -> syntax_reduce x z
| andp_congr: forall x1 x2 y1 y2, syntax_reduce x1 y1 -> syntax_reduce x2 y2 -> syntax_reduce (x1 && x2) (y1 && y2)
| orp_congr: forall x1 x2 y1 y2, syntax_reduce x1 y1 -> syntax_reduce x2 y2 -> syntax_reduce (x1 || x2) (y1 || y2)
| imp_congr: forall x1 x2 y1 y2, syntax_reduce x1 y1 -> syntax_reduce x2 y2 -> syntax_reduce (x1 --> x2) (y1 --> y2)
| iffp_congr: forall x1 x2 y1 y2, syntax_reduce x1 y1 -> syntax_reduce x2 y2 -> syntax_reduce (x1 <--> x2) (y1 <--> y2)
| negp_congr: forall x y, syntax_reduce x y -> syntax_reduce (~~ x) (~~ y)
.

Arguments syntax_reduce {Var} atomic_reduce _ _.

Module ImpNegAsPrime.

Inductive atomic_reduce {Var: Type}: expr Var -> expr Var -> Prop :=
| andp_reduce: forall x y, atomic_reduce (x && y) (~~ (x --> ~~ y))
| orp_reduce: forall x y, atomic_reduce (x || y) (~~ x --> y)
.

End ImpNegAsPrime.

Module ImpAndOrAsPrime.

Inductive atomic_reduce {Var: Type}: expr Var -> expr Var -> Prop :=
| negp_reduce: forall x, atomic_reduce (~~ x) (x --> FF)
.

End ImpAndOrAsPrime.

Module ReduceIff.

Inductive atomic_reduce {Var: Type}: expr Var -> expr Var -> Prop :=
| iff_reduce: forall x y, atomic_reduce (x <--> y) ((x --> y) && (y --> x)).

End ReduceIff.

Module ReduceTrueFalse.

Inductive atomic_reduce {Var: Type}: expr Var -> expr Var -> Prop :=
| falsep_reduce: atomic_reduce FF (~~ TT)
| truep_reduce: forall x, atomic_reduce TT (x --> x).

End ReduceTrueFalse.


