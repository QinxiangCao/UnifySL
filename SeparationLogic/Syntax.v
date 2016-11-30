Require Import Coq.Logic.ProofIrrelevance.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.

Class SeparationLanguage (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L}: Type := {
  sepcon : expr -> expr -> expr;
  wand : expr -> expr -> expr
}.

Class UnitarySeparationLanguage (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L}: Type := {
  emp: expr
}.

Module SeparationLogicNotation.

Notation "x * y" := (sepcon x y) (at level 40, left associativity) : syntax.
Notation "x -* y" := (wand x y) (at level 55, right associativity) : syntax.

End SeparationLogicNotation.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Module SeparationLanguage.

Inductive expr {Var: Type}: Type :=
  | andp : expr -> expr -> expr
  | orp : expr -> expr -> expr
  | impp : expr -> expr -> expr
  | falsep : expr
  | sepcon : expr -> expr -> expr
  | wand : expr -> expr -> expr
  | varp : Var -> expr.

Implicit Arguments expr.

Instance L (Var: Type): Language :=
  Build_Language (expr Var).

Instance nL (Var: Type): NormalLanguage (L Var) :=
  Build_NormalLanguage (L Var) impp.

Instance pL (Var: Type): PropositionalLanguage (L Var) :=
  Build_PropositionalLanguage (L Var) (nL Var) andp orp falsep.

Instance sL (Var: Type): SeparationLanguage (L Var) :=
  Build_SeparationLanguage (L Var) (nL Var) (pL Var) sepcon wand.

End SeparationLanguage.

Module UnitarySeparationLanguage.

Inductive expr {Var: Type}: Type :=
  | andp : expr -> expr -> expr
  | orp : expr -> expr -> expr
  | impp : expr -> expr -> expr
  | falsep : expr
  | sepcon : expr -> expr -> expr
  | wand : expr -> expr -> expr
  | emp : expr
  | varp : Var -> expr.

Implicit Arguments expr.

Instance L (Var: Type): Language :=
  Build_Language (expr Var).

Instance nL (Var: Type): NormalLanguage (L Var) :=
  Build_NormalLanguage (L Var) impp.

Instance pL (Var: Type): PropositionalLanguage (L Var) :=
  Build_PropositionalLanguage (L Var) (nL Var) andp orp falsep.

Instance sL (Var: Type): SeparationLanguage (L Var) :=
  Build_SeparationLanguage (L Var) (nL Var) (pL Var) sepcon wand.

Instance usL (Var: Type): UnitarySeparationLanguage (L Var) :=
  Build_UnitarySeparationLanguage (L Var) (nL Var) (pL Var) (sL Var) emp.

End UnitarySeparationLanguage.

