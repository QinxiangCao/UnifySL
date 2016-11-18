Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.
Local Open Scope KripkeSemantics.
Local Open Scope SeparationLogic.

Class DownwardsClosedSeparationAlgebra (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M}: Type := {
  join_Korder_down: forall (m n m1 m2: Kworlds M), join m1 m2 m -> n <= m -> exists n1 n2, join n1 n2 n /\ n1 <= m1 /\ n2 <= m2
}.

Class DownwardsSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M} (SM: Semantics L MD) {kiSM: KripkeIntuitionisticSemantics L MD M SM}: Type := {
  sat_sepcon: forall m x y, KRIPKE: M , m |= x * y <-> exists m1 m2, join m1 m2 m /\ KRIPKE: M , m1 |= x /\ KRIPKE: M, m2 |= y;
  sat_wand: forall m x y, KRIPKE: M , m |= x -* y <-> forall m0 m1 m2, m0 <= m -> join m0 m1 m2 -> KRIPKE: M , m1 |= x -> KRIPKE: M, m2 |= y
}.

Class DownwardsClosedUnitarySeparationAlgebra (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M} {USA: UnitarySeparationAlgebra MD M}: Type := {
  unit_spec : forall m: Kworlds M, unit m <-> forall n n', join m n n' -> n' <= n;
  unit_exists: forall n: Kworlds M, exists m, join m n n /\ (forall m', m' <= m -> unit m')
}.

Class UnitaryDownwardsSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {uSL: UnitarySeparationLanguage L} (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SA: SeparationAlgebra MD M} {USA: UnitarySeparationAlgebra MD M} (SM: Semantics L MD) {kiSM: KripkeIntuitionisticSemantics L MD M SM} {dsSM: DownwardsSemantics L MD M SM}: Type := {
  sat_emp: forall (m: Kworlds M), KRIPKE: M, m |= emp <-> forall n, n <= m -> unit n
}.

