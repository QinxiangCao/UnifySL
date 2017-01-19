Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.TrivialSemantics.
Require Import Logic.PropositionalLogic.DeepEmbeddedInstance.PropositionalLanguage.

Definition model (Var: Type): Type := Var -> Prop.

Fixpoint denotation {Var: Type} (x: expr Var): Ensemble (model Var) :=
  match x with
  | andp y z => Semantics.andp (denotation y) (denotation z)
  | orp y z => Semantics.orp (denotation y) (denotation z)
  | impp y z => Semantics.impp (denotation y) (denotation z)
  | falsep => Semantics.falsep
  | varp p => fun m => m p
  end.

Instance MD (Var: Type): Model :=
  Build_Model (model Var).

Instance SM (Var: Type): Semantics (PropositionalLanguage.L Var) (MD Var)  :=
  Build_Semantics (PropositionalLanguage.L Var) (MD Var) denotation.

Instance tpSM (Var: Type): TrivialPropositionalSemantics (L Var) (MD Var) (SM Var).
Proof.
  constructor.
  + simpl; intros.
    apply Same_set_refl.
  + simpl; intros.
    apply Same_set_refl.
  + simpl; intros.
    apply Same_set_refl.
  + simpl; intros.
    apply Same_set_refl.
Qed.
