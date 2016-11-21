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

Class DownwardsClosedSeparationAlgebra (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M}: Type := {
  join_Korder_down: forall (m n m1 m2: Kworlds M), join m1 m2 m -> n <= m -> exists n1 n2, join n1 n2 n /\ n1 <= m1 /\ n2 <= m2
}.

Class UpwardsClosedSeparationAlgebra (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M}: Type := {
  join_Korder_up: forall (m1 m2 m n1 n2: Kworlds M), join m1 m2 m -> m1 <= n1 -> m2 <= n2 -> exists n, join n1 n2 n /\ m <= n
}.

(* David J. Pym, Peter W. O’Hearn, and Hongseok Yang. Possible worlds and resources: the semantics of BI. *)

(* This join_Korder is equivalent with the following because Korder is reflexive.
  join_Korder: forall M (m1 m2 m n1 : Kworlds M), join m1 m2 m -> Korder m1 n1 -> exists n, join n1 m2 n /\ Korder m n;

It is necessary to be this strong, or else sepcon_assoc will be unsound, e.g. the following weaker version causes unsoundness:
  join_Korder: forall M (m1 m2 m n1: Kworlds M), join m1 m2 m -> Korder m1 n1 -> exists n2 n, join n1 n2 n /\ Korder m2 n2 /\ Korder m n;  *)

