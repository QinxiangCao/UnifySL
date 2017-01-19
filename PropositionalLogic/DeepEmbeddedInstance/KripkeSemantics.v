Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.DeepEmbeddedInstance.PropositionalLanguage.

Module KripkeSemantics.

Import PropositionalLanguage.

Record frame: Type := {
  underlying_set:> Type;
  Krelation: relation underlying_set; (* <= *)
  Krelation_Preorder: PreOrder Krelation
}.

Infix "<=" := (Krelation _): TheKripkeSemantics.

Local Open Scope TheKripkeSemantics.

Definition sem (f: frame) := sig (fun s: Ensemble f => forall x y, x <= y -> s x -> s y).

Program Definition sem_and {F: frame} (X: sem F) (Y: sem F): sem F := Semantics.andp X Y.
Next Obligation.
  destruct H0.
  split.
  + eapply (proj2_sig X); eauto.
  + eapply (proj2_sig Y); eauto.
Qed.

Program Definition sem_or {F: frame} (X: sem F) (Y: sem F): sem F :=
  fun x: F => X x \/ Y x.
Next Obligation.
  destruct H0; [left | right].
  + eapply (proj2_sig X); eauto.
  + eapply (proj2_sig Y); eauto.
Qed.

Program Definition sem_imp {F: frame} (X: sem F) (Y: sem F): sem F :=
  fun x: F =>
    forall y: F, x <= y -> X y -> Y y.
Next Obligation.
  revert H2; apply H0.
  pose proof @PreOrder_Transitive _ _ (Korder_preorder F).
  transitivity y; auto.
Qed.

Program Definition sem_true {F: frame}: sem F :=
  fun x: F => True.

Program Definition sem_false {F: frame}: sem F :=
  fun x: F => False.

Definition sem_neg {F: frame} (X: sem F): sem F :=
  sem_imp X sem_false.

Definition sem_iff {F: frame} (X: sem F) (Y: sem F): sem F :=
  sem_and (sem_imp X Y) (sem_imp Y X).

Definition denotation {Var: Type} (F: frame) (eval: Var -> sem F): expr Var -> sem F :=
  fix denotation (x: expr Var): sem F:=
  match x with
  | andp y z => sem_and (denotation y) (denotation z)
  | orp y z => sem_or (denotation y) (denotation z)
  | impp y z => sem_imp (denotation y) (denotation z)
  | falsep => sem_false
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

Instance kiM (M: Kmodel): KripkeIntuitionisticModel (Kworlds M) :=
  Build_KripkeIntuitionisticModel (Kworlds M) (Korder M) (Korder_preorder _).

Instance SM: Semantics L MD :=
  Build_Semantics L MD
   (fun M x => proj1_sig (denotation M (Kvar M) x) (elm M)).

Instance kiSM (M: Kmodel): KripkeIntuitionisticSemantics L MD M SM.
Proof.
  apply Build_KripkeIntuitionisticSemantics.
  + hnf; simpl; intros.
    eapply (proj2_sig (denotation M (Kvar M) x)); eauto.
  + split; auto.
  + split; auto.
  + split; auto.
  + intros; simpl. auto.
Defined.

Definition Kmodel_Identity: Kmodel -> Prop := fun M =>
  IdentityKripkeIntuitionisticModel (Kworlds M).

Definition Kmodel_NoBranch: Kmodel -> Prop := fun M =>
  NoBranchKripkeIntuitionisticModel (Kworlds M).

Definition Kmodel_BranchJoin: Kmodel -> Prop := fun M =>
  BranchJoinKripkeIntuitionisticModel (Kworlds M).

End KripkeSemantics.
End KripkeSemantics.
