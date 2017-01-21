Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.KripkeModel.
Require Import Logic.PropositionalLogic.DeepEmbeddedInstance.PropositionalLanguage.

Import PropositionalLanguage.

Record frame: Type := {
  underlying_set:> Type;
  Krelation: relation underlying_set; (* <= *)
  Krelation_Preorder: PreOrder Krelation
}.

Infix "<=" := (Krelation _): TheKripkeSemantics.

Local Open Scope TheKripkeSemantics.

Definition sem (f: frame) := @MonoEnsemble (underlying_set f) (Krelation f).

Definition denotation {Var: Type} (F: frame) (eval: Var -> sem F): expr Var -> sem F :=
  fix denotation (x: expr Var): sem F:=
  match x with
  | andp y z => @SemanticsMono.andp F (Krelation F) (Krelation_Preorder F) (denotation y) (denotation z)
  | orp y z => @SemanticsMono.orp F (Krelation F) (Krelation_Preorder F) (denotation y) (denotation z)
  | impp y z => @SemanticsMono.impp F (Krelation F) (Krelation_Preorder F) (denotation y) (denotation z)
  | falsep => @SemanticsMono.falsep F (Krelation F)
  | varp p => eval p
  end.

Section KripkeSemantics.
Context (Var: Type).

Record Kmodel : Type := {
  underlying_frame :> frame;
  Kvar: Var -> sem underlying_frame
}.

Record model: Type := {
  underlying_model :> Kmodel;
  elm: underlying_model
}.

Instance L: Language := PropositionalLanguage.L Var.
Instance MD: Model := Build_Model model.

Instance kMD: KripkeModel MD :=
  Build_KripkeModel _
    Kmodel
    (fun M => M)
    (fun M m => Build_model M m).

Instance R (M: Kmodel): Relation (Kworlds M) :=
  @Krelation M.

Instance kiM (M: Kmodel): KripkeIntuitionisticModel (Kworlds M) :=
  @Krelation_Preorder M.

Instance SM: Semantics L MD :=
  Build_Semantics L MD (fun x M => proj1_sig (denotation M (Kvar M) x) (elm M)).

Instance kiSM (M: Kmodel): KripkeIntuitionisticSemantics L MD M SM.
Proof.
  apply Build_KripkeIntuitionisticSemantics.
  + hnf; simpl; intros.
    eapply (proj2_sig (denotation M (Kvar M) x)); eauto.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
Defined.

Definition Kmodel_Identity: Kmodel -> Prop := fun M =>
  IdentityKripkeIntuitionisticModel (Kworlds M).

Definition Kmodel_NoBranch: Kmodel -> Prop := fun M =>
  NoBranchKripkeIntuitionisticModel (Kworlds M).

Definition Kmodel_BranchJoin: Kmodel -> Prop := fun M =>
  BranchJoinKripkeIntuitionisticModel (Kworlds M).

End KripkeSemantics.
