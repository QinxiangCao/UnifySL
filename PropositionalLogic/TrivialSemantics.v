Require Import Coq.Logic.Classical_Prop.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Class TrivialPropositionalSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (SM: Semantics L): Type := {
  sat_andp: forall m x y, m |= x && y <-> (m |= x /\ m |= y);
  sat_orp: forall m x y, m |= x || y <-> (m |= x \/ m |= y);
  sat_impp: forall m x y, m |= x --> y <-> (m |= x -> m |= y);
  sat_falsep: forall m, ~ m |= FF
}.

Module TrivialSemantics.

Import PropositionalLanguage.

Definition model (Var: Type): Type := Var -> Prop.

Definition sem_imp {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  fun m => X m -> Y m.

Definition sem_and {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  fun m => X m /\ Y m.

Definition sem_or {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  fun m => X m \/ Y m.

Fixpoint denotation {Var: Type} (x: expr Var): Ensemble (model Var) :=
  match x with
  | andp y z => sem_and (denotation y) (denotation z)
  | orp y z => sem_or (denotation y) (denotation z)
  | impp y z => sem_imp (denotation y) (denotation z)
  | falsep => fun _ => False
  | varp p => fun m => m p
  end.

Instance SM (Var: Type): Semantics (PropositionalLanguage.L Var) :=
  Build_Semantics (PropositionalLanguage.L Var) (model Var) (fun m x => denotation x m).

Instance tpSM (Var: Type): TrivialPropositionalSemantics (L Var) (SM Var).
Proof.
  constructor.
  + simpl; intros.
    unfold sem_and; tauto.
  + simpl; intros.
    unfold sem_or; tauto.
  + simpl; intros.
    unfold sem_imp; tauto.
  + simpl; intros; auto.
Qed.

End TrivialSemantics.

