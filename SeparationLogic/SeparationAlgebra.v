Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.KripkeSemantics.

Local Open Scope KripkeSemantics.

Class SeparationAlgebra (worlds: Type): Type := {
  join: worlds -> worlds -> worlds -> Prop
}.

Class NormalSeparationAlgebra (worlds: Type) {SA: SeparationAlgebra worlds}: Type := {
  join_comm: forall m1 m2 m: worlds, join m1 m2 m -> join m2 m1 m;
  join_assoc: forall mx my mz mxy mxyz: worlds, join mx my mxy -> join mxy mz mxyz -> exists myz, join my mz myz /\ join mx myz mxyz
}.

Class GarbageCollectSeparationAlgebra (worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds}: Type := {
  join_has_order1: forall (m1 m2 m: worlds), join m1 m2 m -> m <= m1
}.

Class UnitarySeparationAlgebra (worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds}: Type := {
  unit: worlds -> Prop;
  unit_spec: forall m: worlds, unit m <-> forall n n', join m n n' -> n' <= n;
  unit_exists: forall n: worlds, exists m, join m n n /\ unit m
}.

Class NormalUnitarySeparationAlgebra (worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {USA: UnitarySeparationAlgebra worlds}: Type := {
  unit_down: forall n m: worlds, n <= m -> unit m -> unit n
}.

Class DownwardsClosedSeparationAlgebra (worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds}: Type := {
  join_Korder_down: forall m n m1 m2: worlds, join m1 m2 m -> n <= m -> exists n1 n2, join n1 n2 n /\ n1 <= m1 /\ n2 <= m2
}.

Class UpwardsClosedSeparationAlgebra (worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds}: Type := {
  join_Korder_up: forall m1 m2 m n1 n2: worlds, join m1 m2 m -> m1 <= n1 -> m2 <= n2 -> exists n, join n1 n2 n /\ m <= n
}.

(* David J. Pym, Peter W. O’Hearn, and Hongseok Yang. Possible worlds and resources: the semantics of BI. *)

(* This join_Korder is equivalent with the following because Korder is reflexive.
  join_Korder: forall M (m1 m2 m n1 : Kworlds M), join m1 m2 m -> Korder m1 n1 -> exists n, join n1 m2 n /\ Korder m n;

It is necessary to be this strong, or else sepcon_assoc will be unsound, e.g. the following weaker version causes unsoundness:
  join_Korder: forall M (m1 m2 m n1: Kworlds M), join m1 m2 m -> Korder m1 n1 -> exists n2 n, join n1 n2 n /\ Korder m2 n2 /\ Korder m n;  *)

Definition UpwardsClosed_nUSA (worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {uSA: UpwardsClosedSeparationAlgebra worlds} {USA: UnitarySeparationAlgebra worlds}: NormalUnitarySeparationAlgebra worlds.
Proof.
  constructor.
  intros.
  pose proof Korder_PreOrder as H_PreOrder.
  rewrite unit_spec in H0 |- *.
  intros.
  destruct (join_Korder_up _ _ _ _ n0 H1 H) as [n'' [? ?]]; [reflexivity |].
  etransitivity; eauto.
Qed.

