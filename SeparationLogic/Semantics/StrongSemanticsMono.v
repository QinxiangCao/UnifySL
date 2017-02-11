Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Ensembles.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Logic.SeparationLogic.Semantics.StrongSemantics.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Program Definition sepcon
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}
      (X Y: MonoEnsemble worlds): MonoEnsemble worlds :=
  StrongSemantics.sepcon X Y.
Next Obligation.
  apply (@StrongSemantics.sepcon_closed worlds R po_R J);
  apply (proj2_sig _).
Defined.

Program Definition wand
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}
      (X Y: MonoEnsemble worlds): MonoEnsemble worlds :=
  StrongSemantics.wand X Y.
Next Obligation.
  apply (@StrongSemantics.wand_closed worlds R po_R J);
  apply (proj2_sig _).
Defined.

Program Definition emp
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}: MonoEnsemble worlds :=
  StrongSemantics.emp.
Next Obligation.
  apply (@StrongSemantics.emp_closed worlds R po_R J);
  apply (proj2_sig _).
Defined.