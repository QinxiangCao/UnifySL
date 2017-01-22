Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Logic.SeparationLogic.Semantics.WeakSemanticsMono.
Require Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.SeparationLogic.DeepEmbedded.SeparationEmpLanguage.

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
  Frame_join: Join underlying_set;
  Frame_SA: SeparationAlgebra underlying_set;
  Frame_downwards: @DownwardsClosedSeparationAlgebra underlying_set Krelation Frame_join;
  Frame_upwards: @UpwardsClosedSeparationAlgebra underlying_set Krelation Frame_join
}.

Infix "<=" := (Krelation _): TheKripkeSemantics.

Local Open Scope TheKripkeSemantics.

Definition sem (f: frame) := @MonoEnsemble (underlying_set f) (Krelation f).

Definition denotation {Var: Type} (F: frame) (eval_emp: sem F) (eval: Var -> sem F): expr Var -> sem F :=
  fix denotation (x: expr Var): sem F:=
  match x with
  | andp y z => @SemanticsMono.andp F (Krelation F) (Krelation_Preorder F) (denotation y) (denotation z)
  | orp y z => @SemanticsMono.orp F (Krelation F) (Krelation_Preorder F) (denotation y) (denotation z)
  | impp y z => @SemanticsMono.impp F (Krelation F) (Krelation_Preorder F) (denotation y) (denotation z)
  | sepcon y z => @WeakSemanticsMono.sepcon F (Krelation F) (Krelation_Preorder F) (Frame_join F) (Frame_SA F) (Frame_upwards F) (denotation y) (denotation z)
  | wand y z => @WeakSemanticsMono.wand F (Krelation F) (Krelation_Preorder F) (Frame_join F) (Frame_SA F) (Frame_downwards F) (denotation y) (denotation z)
  | emp => eval_emp
  | falsep => @SemanticsMono.falsep F (Krelation F)
  | varp p => eval p
  end.

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

Instance SM: Semantics L MD :=
  Build_Semantics L MD (fun x M => proj1_sig (denotation M (Kemp M) (Kvar M) x) (elm M)).

Instance R (M: Kmodel): Relation (Kworlds M) :=
  @Krelation M.

Instance kiM (M: Kmodel): KripkeIntuitionisticModel (Kworlds M) :=
  @Krelation_Preorder M.

Instance J (M: Kmodel): Join (Kworlds M) :=
  @Frame_join M.

Instance SA (M: Kmodel): SeparationAlgebra (Kworlds M) :=
  @Frame_SA M.

Instance uSA (M: Kmodel): UpwardsClosedSeparationAlgebra (Kworlds M) :=
  @Frame_upwards M.

Instance dSA (M: Kmodel): DownwardsClosedSeparationAlgebra (Kworlds M) :=
  @Frame_downwards M.

Instance kiSM (M: Kmodel): KripkeIntuitionisticSemantics L MD M SM.
Proof.
  apply Build_KripkeIntuitionisticSemantics.
  + hnf; simpl; intros.
    eapply (proj2_sig (denotation M (Kemp M) (Kvar M) x)); eauto.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
Defined.

Instance fsSM (M: Kmodel): FlatSemantics.SeparatingSemantics L MD M SM.
Proof.
  apply FlatSemantics.Build_SeparatingSemantics.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
Defined.

Instance feSM (M: Kmodel): Same_set _ (proj1_sig (Kemp M)) (WeakSemantics.emp) -> FlatSemantics.EmpSemantics L MD M SM.
Proof.
  intros; hnf; intros.
  auto.
Defined.

Definition Kmodel_Identity: Kmodel -> Prop := fun M =>
  IdentityKripkeIntuitionisticModel (Kworlds M).

Definition Kmodel_NoBranch: Kmodel -> Prop := fun M =>
  NoBranchKripkeIntuitionisticModel (Kworlds M).

Definition Kmodel_BranchJoin: Kmodel -> Prop := fun M =>
  BranchJoinKripkeIntuitionisticModel (Kworlds M).

Definition Kmodel_Increasing: Kmodel -> Prop := fun M =>
  IncreasingSeparationAlgebra (Kworlds M).

Definition Kmodel_Unital: Kmodel -> Prop := fun M =>
  (forall m: Kworlds M, proj1_sig (Kemp M) m <-> WeakSemantics.emp m) /\
  UnitalSeparationAlgebra (Kworlds M).

Definition Kmodel_Residual: Kmodel -> Prop := fun M =>
  ResidualSeparationAlgebra (Kworlds M).

Require Import Logic.SeparationLogic.DeepEmbedded.Parameter.

Record Parametric_Kmodel_Class (PAR: SA_Parameter) (M: Kmodel): Prop := {
  SA_ID: ID PAR = true -> IdentityKripkeIntuitionisticModel (Kworlds M);
  SA_NB: NB PAR = true -> NoBranchKripkeIntuitionisticModel (Kworlds M);
  SA_BJ: BJ PAR = true -> BranchJoinKripkeIntuitionisticModel (Kworlds M);
  SA_INCR: INCR PAR = true -> IncreasingSeparationAlgebra (Kworlds M);
  SA_UNI: UNI PAR = true -> UnitalSeparationAlgebra (Kworlds M);
  SA_RES: RES PAR = true -> ResidualSeparationAlgebra (Kworlds M)
}.

End KripkeSemantics.
