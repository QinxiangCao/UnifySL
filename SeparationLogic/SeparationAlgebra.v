Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.KripkeSemantics.

Local Open Scope KripkeSemantics.

Class SeparationAlgebra (MD: Model) {kMD: KripkeModel MD} (M: Kmodel): Type := {
  join: Kworlds M -> Kworlds M -> Kworlds M -> Prop;
  join_comm: forall m1 m2 m: Kworlds M, join m1 m2 m -> join m2 m1 m;
  join_assoc: forall mx my mz mxy mxyz: Kworlds M, join mx my mxy -> join mxy mz mxyz -> exists myz, join my mz myz /\ join mx myz mxyz
}.

Class GarbageCollectSeparationAlgebra (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M}: Type := {
  join_has_order1: forall (m1 m2 m: Kworlds M), join m1 m2 m -> m <= m1
}.

Class UnitarySeparationAlgebra (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M}: Type := {
  unit: Kworlds M -> Prop
}.
