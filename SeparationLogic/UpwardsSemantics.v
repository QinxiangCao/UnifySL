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

Class UpwardsClosedSeparationAlgebra (MD: Model) {kMD: KripkeModel MD} {kiMD: KripkeIntuitionisticModel MD} {SA: SeparationAlgebra MD} (M: Kmodel): Type := {
  join_Korder: forall (m1 m2 m n1 n2: Kworlds M), join m1 m2 m -> m1 <= n1 -> m2 <= n2 -> exists n, join n1 n2 n /\ m <= n
}.

(* David J. Pym, Peter W. O’Hearn, and Hongseok Yang. Possible worlds and resources: the semantics of BI. *)

(* This join_Korder is equivalent with the following because Korder is reflexive.
  join_Korder: forall M (m1 m2 m n1 : Kworlds M), join m1 m2 m -> Korder m1 n1 -> exists n, join n1 m2 n /\ Korder m n;

It is necessary to be this strong, or else sepcon_assoc will be unsound, e.g. the following weaker version causes unsoundness:
  join_Korder: forall M (m1 m2 m n1: Kworlds M), join m1 m2 m -> Korder m1 n1 -> exists n2 n, join n1 n2 n /\ Korder m2 n2 /\ Korder m n;  *)

Class UpwardsSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} (MD: Model) {kMD: KripkeModel MD} {kiMD: KripkeIntuitionisticModel MD} {SA: SeparationAlgebra MD} (SM: Semantics L MD) {kiSM: KripkeIntuitionisticSemantics L MD SM}: Type := {
  sat_sepcon: forall M m x y, KRIPKE: M , m |= x * y <-> exists m0 m1 m2, m <= m0 /\ join m1 m2 m0 /\ KRIPKE: M , m1 |= x /\ KRIPKE: M, m2 |= y;
  sat_wand: forall M m x y, KRIPKE: M , m |= x -* y <-> forall m1 m2, join m m1 m2 -> KRIPKE: M , m1 |= x -> KRIPKE: M, m2 |= y
}.

Class UpwardsClosedUnitarySeparationAlgebra (MD: Model) {kMD: KripkeModel MD} {kiMD: KripkeIntuitionisticModel MD} {SA: SeparationAlgebra MD} {USA: UnitarySeparationAlgebra MD} (M: Kmodel): Type := {
  unit_spec: forall m: Kworlds M, unit m <-> forall n n', join m n n' -> n = n';
  unit_exists: forall n: Kworlds M, exists m, join m n n /\ unit m
}.

Class UnitaryUpwardsSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {uSL: UnitarySeparationLanguage L} (MD: Model) {kMD: KripkeModel MD} {kiMD: KripkeIntuitionisticModel MD} {SA: SeparationAlgebra MD} {USA: UnitarySeparationAlgebra MD} (SM: Semantics L MD) {kiSM: KripkeIntuitionisticSemantics L MD SM} {usSM: UpwardsSemantics L MD SM}: Type := {
  sat_emp: forall M (m: Kworlds M), KRIPKE: M, m |= emp <-> exists n, m <= n /\ unit n
}.

