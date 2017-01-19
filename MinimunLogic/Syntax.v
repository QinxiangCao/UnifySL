Require Import Logic.GeneralLogic.Base.

Class NormalLanguage (L: Language): Type := {
  impp: expr -> expr -> expr
}.

Notation "x --> y" := (impp x y) (at level 55, right associativity) : syntax.
