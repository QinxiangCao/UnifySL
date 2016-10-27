Require Import Logic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Coq.Logic.Classical_Prop.

Module TrivialSemantics.

Import PropositionalLanguage.

Definition model (Var: Type): Type := Var -> Prop.

Definition sem_imp {Var: Type} (X: Ensemble (model Var)) (Y: Ensemble (model Var)): Ensemble (model Var) :=
  fun m => X m -> Y m.

Definition sem_neg {Var: Type} (X: Ensemble (model Var)): Ensemble (model Var) :=
  fun m => ~ X m.

Definition sem_and {Var: Type} (X: Ensemble (model Var)) (Y: Ensemble (model Var)): Ensemble (model Var) :=
  sem_neg (sem_imp X (sem_neg Y)).

Definition sem_or {Var: Type} (X: Ensemble (model Var)) (Y: Ensemble (model Var)): Ensemble (model Var) :=
  sem_imp (sem_neg X) Y.

Definition sem_iff {Var: Type} (X: Ensemble (model Var)) (Y: Ensemble (model Var)): Ensemble (model Var) :=
  sem_and (sem_imp X Y) (sem_imp Y X).

Fixpoint denotation {Var: Type} (x: expr Var): Ensemble (model Var) :=
  match x with
  | andp y z => sem_and (denotation y) (denotation z)
  | orp y z => sem_or (denotation y) (denotation z)
  | impp y z => sem_imp (denotation y) (denotation z)
  | iffp y z => sem_iff (denotation y) (denotation z)
  | negp y => sem_neg (denotation y)
  | truep => fun _ => True
  | falsep => fun _ => False
  | varp p => fun m => m p
  end.

Instance SM (Var: Type): Semantics (PropositionalLanguage.L Var) :=
  Build_Semantics (PropositionalLanguage.L Var) (model Var) (fun m x => denotation x m).

End TrivialSemantics.
