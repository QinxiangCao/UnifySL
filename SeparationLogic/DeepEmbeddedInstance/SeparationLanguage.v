Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

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
  Build_SeparationLanguage (L Var) sepcon wand.
