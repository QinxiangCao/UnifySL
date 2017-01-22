Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Ensembles.
Require Import Logic.lib.Coqlib.
Require Import Logic.PropositionalLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Logic.SeparationLogic.Semantics.WeakSemantics.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Program Definition sepcon
      {worlds: Type}
      {R: Relation worlds}
      {kiM: KripkeIntuitionisticModel worlds}
      {J: Join worlds}
      {SA: SeparationAlgebra worlds}
      {uSA: UpwardsClosedSeparationAlgebra worlds}
      (X Y: MonoEnsemble worlds): MonoEnsemble worlds :=
  WeakSemantics.sepcon X Y.
Next Obligation.
  apply (@WeakSemantics.sepcon_closed worlds R kiM J SA uSA);
  apply (proj2_sig _).
Defined.

Program Definition wand
      {worlds: Type}
      {R: Relation worlds}
      {kiM: KripkeIntuitionisticModel worlds}
      {J: Join worlds}
      {SA: SeparationAlgebra worlds}
      {dSA: DownwardsClosedSeparationAlgebra worlds}
      (X Y: MonoEnsemble worlds): MonoEnsemble worlds :=
  WeakSemantics.wand X Y.
Next Obligation.
  apply (@WeakSemantics.wand_closed worlds R kiM J SA dSA);
  apply (proj2_sig _).
Defined.

Program Definition emp
      {worlds: Type}
      {R: Relation worlds}
      {kiM: KripkeIntuitionisticModel worlds}
      {J: Join worlds}
      {SA: SeparationAlgebra worlds}
      {dSA: DownwardsClosedSeparationAlgebra worlds}: MonoEnsemble worlds :=
  WeakSemantics.emp.
Next Obligation.
  apply (@WeakSemantics.emp_closed worlds R kiM J SA dSA);
  apply (proj2_sig _).
Defined.