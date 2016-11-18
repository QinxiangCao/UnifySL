Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.
Local Open Scope SeparationLogic.

Class DownwardsSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} (SM: Semantics L) {pkSM: PreKripkeSemantics L SM} {kiM: KripkeIntuitionisticModel L SM} {kiSM: KripkeIntuitionisticSemantics L SM} : Type := {
  join: forall {M: Kmodel}, Kworlds M -> Kworlds M -> Kworlds M -> Prop;
  join_comm: forall M (m1 m2 m: Kworlds M), join m1 m2 m -> join m2 m1 m;
  join_assoc: forall M (mx my mz mxy mxyz: Kworlds M), join mx my mxy -> join mxy mz mxyz -> exists myz, join my mz myz /\ join mx myz mxyz;
  join_Korder: forall M (m n m1 m2: Kworlds M), join m1 m2 m -> Korder n m -> exists n1 n2, join n1 n2 n /\ Korder n1 m1 /\ Korder n2 m2;
  sat_sepcon: forall M m x y, KRIPKE: M , m |= x * y <-> exists m1 m2, join m1 m2 m /\ KRIPKE: M , m1 |= x /\ KRIPKE: M, m2 |= y;
  sat_wand: forall M m x y, KRIPKE: M , m |= x -* y <-> forall m0 m1 m2, Korder m0 m -> join m0 m1 m2 -> KRIPKE: M , m1 |= x -> KRIPKE: M, m2 |= y
}.

Class UnitaryDownwardsSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {uSL: UnitarySeparationLanguage L} (SM: Semantics L) {pkSM: PreKripkeSemantics L SM} {kiM: KripkeIntuitionisticModel L SM} {kiSM: KripkeIntuitionisticSemantics L SM} {dsSM: DownwardsSemantics L SM}: Type := {
  unit := fun M (m: Kworlds M) => forall n n', join m n n' -> Korder n' n;
  unit_exists: forall M (n: Kworlds M), exists m, join m n n /\ (forall m', Korder m' m -> unit M m');
  sat_emp: forall M (m: Kworlds M), KRIPKE: M, m |= emp <-> forall n, Korder n m -> unit M n
}.

