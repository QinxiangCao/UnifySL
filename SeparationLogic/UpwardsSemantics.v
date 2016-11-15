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

Class UpwardsSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} (SM: Semantics L) {pkSM: PreKripkeSemantics L SM} {kiSM: KripkeIntuitionisticSemantics L SM} : Type := {
  join: forall {M: Kmodel}, Kworlds M -> Kworlds M -> Kworlds M -> Prop;
  join_comm: forall M (m1 m2 m: Kworlds M), join m1 m2 m -> join m2 m1 m;
  join_assoc: forall M (mx my mz mxy mxyz: Kworlds M), join mx my mxy -> join mxy mz mxyz -> exists myz, join my mz myz /\ join mx myz mxyz;
  join_Korder: forall M (m1 m2 m n1 n2: Kworlds M), join m1 m2 m -> Korder m1 n1 -> Korder m2 n2 -> exists n, join n1 n2 n /\ Korder m n;
  sat_sepcon: forall M m x y, KRIPKE: M , m |= x * y <-> exists m0 m1 m2, Korder m m0 /\ join m1 m2 m0 /\ KRIPKE: M , m1 |= x /\ KRIPKE: M, m2 |= y;
  sat_wand: forall M m x y, KRIPKE: M , m |= x -* y <-> forall m1 m2, join m m1 m2 -> KRIPKE: M , m1 |= x -> KRIPKE: M, m2 |= y
}.

(* David J. Pym, Peter W. O’Hearn, and Hongseok Yang. Possible worlds and resources: the semantics of BI. *)

(* This join_Korder is equivalent with the following because Korder is reflexive.
  join_Korder: forall M (m1 m2 m n1 : Kworlds M), join m1 m2 m -> Korder m1 n1 -> exists n, join n1 m2 n /\ Korder m n;

It is necessary to be this strong, or else sepcon_assoc will be unsound, e.g. the following weaker version causes unsoundness:
  join_Korder: forall M (m1 m2 m n1: Kworlds M), join m1 m2 m -> Korder m1 n1 -> exists n2 n, join n1 n2 n /\ Korder m2 n2 /\ Korder m n;  *)

Class UnitaryUpwardsSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {uSL: UnitarySeparationLanguage L} (SM: Semantics L) {pkSM: PreKripkeSemantics L SM} {kiSM: KripkeIntuitionisticSemantics L SM} {usSM: UpwardsSemantics L SM}: Type := {
  unit := fun M (m: Kworlds M) => forall n n', join m n n' -> n = n';
  unit_exists: forall M (n: Kworlds M), exists m, join m n n /\ unit M m;
  sat_emp: forall M (m: Kworlds M), KRIPKE: M, m |= emp <-> exists n, Korder m n /\ unit M n
}.

