Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.KripkeSemantics.

Class SeparationAlgebra (MD: Model) {kMD: KripkeModel MD}: Type := {
  join: forall {M: Kmodel}, Kworlds M -> Kworlds M -> Kworlds M -> Prop;
  join_comm: forall M (m1 m2 m: Kworlds M), join m1 m2 m -> join m2 m1 m;
  join_assoc: forall M (mx my mz mxy mxyz: Kworlds M), join mx my mxy -> join mxy mz mxyz -> exists myz, join my mz myz /\ join mx myz mxyz
}.

Class UnitarySeparationAlgebra (MD: Model) {kMD: KripkeModel MD} {kiMD: KripkeIntuitionisticModel MD} {SA: SeparationAlgebra MD}: Type := {
  unit: forall {M: Kmodel}, Kworlds M -> Prop
}.
