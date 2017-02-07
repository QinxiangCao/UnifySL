Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.GeneralLogic.KripkeModel.

Module SS.

Class Relation (worlds: Type): Type :=
  Krelation: worlds -> Ensemble worlds.

End SS.

Export SS.

Module Semantics.

Definition stable {worlds: Type} {R: Relation worlds} {EqR: Equivalence R} (X: Ensemble worlds): Prop := forall m n, R m n -> (X m <-> X n).

End Semantics.

Module SemanticsMono.

Definition stable {worlds: Type} {R1: KI.Relation worlds} {R2: Relation worlds} {EqR2: Equivalence R2} (X: MonoEnsemble worlds): Prop := forall m n, R2 m n -> (proj1_sig X m <-> proj1_sig X n).

End SemanticsMono.

Require Import Logic.GeneralLogic.Base.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Class KripkeIntuitionisticStable (L: Language) (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {R1: KI.Relation (Kworlds M)} {R2: Relation (Kworlds M)} (SM: Semantics L MD): Type := {
  bis_stable:
    forall m n, R2 m n ->
      (forall m', m <= m' -> exists n', n <= n' /\ R2 m' n') /\
       (forall n', n <= n' -> exists m', m <= m' /\ R2 m' n')
}.