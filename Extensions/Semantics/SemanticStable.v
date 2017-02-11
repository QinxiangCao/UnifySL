Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.DownwardsClosure.

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

Class SeparationAlgebraAbsorbStable (worlds: Type) {R1: KI.Relation worlds} {J: Join worlds} {R2: Relation worlds}: Type := {
  SA_absorb_stable:
    forall m m1 m2, join m1 m2 m ->
      exists n1 n2, join n1 n2 m /\ R2 n1 m /\ R2 n2 m /\ m1 <= n1 /\ m2 <= n2
}.

Class StrongSeparationAlgebraAbsorbStable (worlds: Type) {J: Join worlds} {R: Relation worlds}: Type := {
  strong_SA_absorb_stable:
    forall m m1 m2, join m1 m2 m -> R m1 m /\ R m2 m
}.

Lemma DownwardsClosure_SAAbsorbStable (worlds: Type) {R1: KI.Relation worlds} {po_R: PreOrder KI.Krelation} {J: Join worlds} {R2: Relation worlds} {SA_abs': StrongSeparationAlgebraAbsorbStable worlds}: @SeparationAlgebraAbsorbStable worlds R1 DownwardsClosure_J R2.
Proof.
  constructor.
  intros.
  hnf in H.
  destruct H as [n1 [n2 [? [? ?]]]].
  exists n1, n2.
  split; [| split; [| split; [| split ]]]; auto.
  + exists n1, n2.
    split; [| split]; auto; reflexivity.
  + destruct (strong_SA_absorb_stable _ _ _ H1); auto.
  + destruct (strong_SA_absorb_stable _ _ _ H1); auto.
Qed.

Require Import Logic.GeneralLogic.Base.

Class SemanticStable (L: Language) (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {R: Relation (Kworlds M)} (SM: Semantics L MD): Type := {
  semantic_stable: expr -> Prop;
  denote_stable: forall x, semantic_stable x <-> Semantics.stable (Kdenotation M x)
}.

