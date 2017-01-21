Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.SeparationLogic.DeepEmbeddedInstance.SeparationEmpLanguage.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Record frame: Type := {
  underlying_set:> Type;
  Krelation: relation underlying_set; (* <= *)
  Krelation_Preorder: PreOrder Krelation;
  R: Relation underlying_set := Krelation;
  kiM: KripkeIntuitionisticModel underlying_set := Krelation_Preorder;
  J: Join underlying_set;
  SA: SeparationAlgebra underlying_set;
  dSA: DownwardsClosedSeparationAlgebra underlying_set;
  uSA: UpwardsClosedSeparationAlgebra underlying_set
}.

Infix "<=" := (Krelation _): TheKripkeSemantics.

Local Open Scope TheKripkeSemantics.

Definition sem (f: frame) := @sig (_ -> Prop) (@upwards_closed_Kdenote f (Krelation f)).

Program Definition denotation {Var: Type} (F: frame) (eval_emp: sem F) (eval: Var -> sem F): expr Var -> sem F :=
  fix denotation (x: expr Var): sem F:=
  match x with
  | andp y z => @Semantics.andp F (denotation y) (denotation z)
  | orp y z => Semantics.orp (denotation y) (denotation z)
  | impp y z => @Semantics.impp F (Krelation F) (denotation y) (denotation z)
  | sepcon y z => @WeakSemantics.sepcon F (J F) (denotation y) (denotation z)
  | wand y z => @WeakSemantics.wand F (J F) (denotation y) (denotation z)
  | emp => @WeakSemantics.emp F (Krelation F) (J F)
  | falsep => Semantics.falsep
  | varp p => eval p
  end.
Next Obligation.
  apply (@Semantics.andp_closed F (Krelation F) (Krelation_Preorder F));
  apply (proj2_sig (denotation _)).
Defined.
Next Obligation.
  apply (@Semantics.orp_closed F (Krelation F) (Krelation_Preorder F));
  apply (proj2_sig (denotation _)).
Defined.
Next Obligation.
  apply (@Semantics.impp_closed F (Krelation F) (Krelation_Preorder F));
  apply (proj2_sig (denotation _)).
Defined.
Next Obligation.
  apply (@WeakSemantics.sepcon_closed F (Krelation F) (Krelation_Preorder F) (J F) (SA F) (uSA F));
  apply (proj2_sig (denotation _)).
Defined.
Next Obligation.
  apply (@WeakSemantics.wand_closed F (Krelation F) (Krelation_Preorder F) (J F) (SA F) (dSA F));
  apply (proj2_sig (denotation _)).
Defined.
Next Obligation.
  apply (@WeakSemantics.emp_closed F (Krelation F) (Krelation_Preorder F) (J F) (SA F) (dSA F)).
Defined.
Next Obligation.
  apply (@Semantics.falsep_closed F (Krelation F)).
Defined.

Section KripkeSemantics.
Context (Var: Type).

Record Kmodel : Type := {
  underlying_frame :> frame;
  Kemp: sem underlying_frame;
  Kvar: Var -> sem underlying_frame
}.

Record model: Type := {
  underlying_model :> Kmodel;
  elm: underlying_model
}.

Instance L: Language := SeparationEmpLanguage.L Var.
Instance MD: Model := Build_Model model.

Instance kMD: KripkeModel MD :=
  Build_KripkeModel _
    Kmodel
    (fun M => M)
    (fun M m => Build_model M m).

Existing Instances kiM J SA dSA uSA.

Instance SM: Semantics L MD :=
  Build_Semantics L MD
   (fun M x => proj1_sig (denotation M (Kemp M) (Kvar M) x) (elm M)).

Instance kiSM (M: Kmodel): KripkeIntuitionisticSemantics L MD M SM.
Proof.
  apply Build_KripkeIntuitionisticSemantics.
  + hnf; simpl; intros.
    eapply (proj2_sig (denotation M (Kemp M) (Kvar M) x)); eauto.
  + split; auto.
  + split; auto.
  + split; auto.
  + intros; simpl. auto.
Defined.

Instance fsSM (M: Kmodel): FlatSemantics.FlatSemantics L MD M SM.
Proof.
  apply FlatSemantics.Build_FlatSemantics.
  + intros.
    simpl; reflexivity.
  + intros.
    simpl; reflexivity.
Defined.

(*
Instance UsSM (M: Kmodel): UnitalSemantics L MD M SM.
Proof.
  hnf; intros.
  simpl; reflexivity.
Defined.
*)

Definition Kmodel_Identity: Kmodel -> Prop := fun M =>
  IdentityKripkeIntuitionisticModel (Kworlds M).

Definition Kmodel_NoBranch: Kmodel -> Prop := fun M =>
  NoBranchKripkeIntuitionisticModel (Kworlds M).

Definition Kmodel_BranchJoin: Kmodel -> Prop := fun M =>
  BranchJoinKripkeIntuitionisticModel (Kworlds M).

(* TODO: the name should be nonpositive *)
Definition Kmodel_GarbageCollect: Kmodel -> Prop := fun M =>
  GarbageCollectSeparationAlgebra (Kworlds M).

Definition Kmodel_Unital: Kmodel -> Prop := fun M =>
  (forall m: Kworlds M, proj1_sig (Kemp M) m <-> proj1_sig sem_emp m) /\
  UnitalSeparationAlgebra (Kworlds M).

Definition Kmodel_Residual: Kmodel -> Prop := fun M =>
  ResidualSeparationAlgebra (Kworlds M).


Require Import Logic.SeparationLogic.SoundCompleteParameter.

Record Kmodel_ParClass (PAR: SA_Parameter) (M: Kmodel): Prop := {
  SA_ID: ID PAR = true -> IdentityKripkeIntuitionisticModel (Kworlds M);
  SA_NB: NB PAR = true -> NoBranchKripkeIntuitionisticModel (Kworlds M);
  SA_BJ: BJ PAR = true -> BranchJoinKripkeIntuitionisticModel (Kworlds M);
  SA_GC: GC PAR = true -> GarbageCollectSeparationAlgebra (Kworlds M);
  SA_Uni: Uni PAR = true -> UnitalSeparationAlgebra (Kworlds M)
}.

End KripkeSemantics.
End FlatSemanticsModel.
