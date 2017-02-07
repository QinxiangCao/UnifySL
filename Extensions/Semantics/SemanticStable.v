Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Module SS.

Class Relation (worlds: Type): Type :=
  Krelation: worlds -> Ensemble worlds.

End SS.

Export SS.

Module Semantics.

Definition stable {worlds: Type} {R: Relation worlds} (X: Ensemble worlds): Prop := forall m n, R m n -> (X m <-> X n).

End Semantics.

Class KripkeIntuitionisticBisStable (worlds: Type) {R1: KI.Relation worlds} {R2: Relation worlds}: Type := {
  KI_bis_stable:
    forall m n, R2 m n ->
      (forall m', m <= m' -> exists n', n <= n' /\ R2 m' n') /\
       (forall n', n <= n' -> exists m', m <= m' /\ R2 m' n')
}.

Class KripkeModalBisStable (worlds: Type) {R1: KM.Relation worlds} {R2: Relation worlds}: Type := {
  KM_bis_stable:
    forall m n, R2 m n ->
      (forall m', KM.Krelation m m' -> exists n', KM.Krelation n n' /\ R2 m' n') /\
       (forall n', KM.Krelation n n' -> exists m', KM.Krelation m m' /\ R2 m' n')
}.

Class KripkeModalAbsorbStable (worlds: Type) {R1: KM.Relation worlds} {R2: Relation worlds}: Type := {
  KM_absorb_stable: forall m n, R1 m n -> R2 m n
}.

Class SeparationAlgebraBisStable (worlds: Type) {J: Join worlds} {R: Relation worlds}: Type := {
  split_bis_stable:
    forall m n, R m n ->
      (forall m1 m2, join m1 m2 m -> exists n1 n2, join n1 n2 n /\ R m1 n1 /\ R m2 n2) /\
       (forall n1 n2, join n1 n2 n -> exists m1 m2, join m1 m2 m /\ R m1 n1 /\ R m2 n2);
  extend_bis_stable:
    forall m n, R m n ->
      (forall m1 m2, join m m1 m2 -> exists n1 n2, join n n1 n2 /\ R m1 n1 /\ R m2 n2) /\
       (forall n1 n2, join n n1 n2 -> exists m1 m2, join m m1 m2 /\ R m1 n1 /\ R m2 n2)
}.

Require Import Logic.GeneralLogic.Base.

Class SemanticStable (L: Language) (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {R: Relation (Kworlds M)} (SM: Semantics L MD): Type := {
  semantic_stable: expr -> Prop;
  denote_stable: forall x, semantic_stable x <-> Semantics.stable (Kdenotation M x)
}.

