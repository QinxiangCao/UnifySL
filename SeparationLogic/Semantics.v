Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Module DownwardsSemantics.

Class DownwardsSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel (Kworlds M)} {SA: SeparationAlgebra (Kworlds M)} (SM: Semantics L MD) {kiSM: KripkeIntuitionisticSemantics L MD M SM}: Type := {
  sat_sepcon: forall m x y, KRIPKE: M , m |= x * y <-> exists m1 m2, join m1 m2 m /\ KRIPKE: M , m1 |= x /\ KRIPKE: M, m2 |= y;
  sat_wand: forall m x y, KRIPKE: M , m |= x -* y <-> forall m0 m1 m2, m0 <= m -> join m0 m1 m2 -> KRIPKE: M , m1 |= x -> KRIPKE: M, m2 |= y
}.

End DownwardsSemantics.

Module UpwardsSemantics.

Class UpwardsSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel (Kworlds M)} {SA: SeparationAlgebra (Kworlds M)} (SM: Semantics L MD) {kiSM: KripkeIntuitionisticSemantics L MD M SM}: Type := {
  sat_sepcon: forall m x y, KRIPKE: M , m |= x * y <-> exists m0 m1 m2, m <= m0 /\ join m1 m2 m0 /\ KRIPKE: M , m1 |= x /\ KRIPKE: M, m2 |= y;
  sat_wand: forall m x y, KRIPKE: M , m |= x -* y <-> forall m1 m2, join m m1 m2 -> KRIPKE: M , m1 |= x -> KRIPKE: M, m2 |= y
}.

End UpwardsSemantics.

Module FlatSemantics.

Class FlatSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel (Kworlds M)} {SA: SeparationAlgebra (Kworlds M)} (SM: Semantics L MD) {kiSM: KripkeIntuitionisticSemantics L MD M SM}: Type := {
  sat_sepcon: forall m x y, KRIPKE: M , m |= x * y <-> exists m1 m2, join m1 m2 m /\ KRIPKE: M , m1 |= x /\ KRIPKE: M, m2 |= y;
  sat_wand: forall m x y, KRIPKE: M , m |= x -* y <-> forall m1 m2, join m m1 m2 -> KRIPKE: M , m1 |= x -> KRIPKE: M, m2 |= y
}.

End FlatSemantics.

Class UnitarySemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {uSL: UnitarySeparationLanguage L} (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel (Kworlds M)} {SA: SeparationAlgebra (Kworlds M)} {USA: UnitarySeparationAlgebra (Kworlds M)} (SM: Semantics L MD) {kiSM: KripkeIntuitionisticSemantics L MD M SM}: Type := {
  sat_emp: forall (m: Kworlds M), KRIPKE: M, m |= emp <-> pre_unit m
}.
