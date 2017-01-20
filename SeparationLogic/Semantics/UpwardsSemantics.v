Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Module Semantics.

Definition sepcon {worlds: Type} {J: Join worlds} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => exists m1 m2, join m1 m2 m /\ X m1 /\ Y m2.

Definition wand {worlds: Type} {R: Relation worlds} {J: Join worlds} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => forall m0 m1 m2, m <= m0 -> join m0 m1 m2 -> X m1 -> Y m2.

Definition emp {worlds: Type} {R: Relation worlds} {J: Join worlds}: Ensemble worlds := increasing'.

Lemma sepcon_closed
      {worlds: Type}
      {R: Relation worlds}
      {kiM: KripkeIntuitionisticModel worlds}
      {J: Join worlds}
      {SA: SeparationAlgebra worlds}
      {uSA: UpwardsClosedSeparationAlgebra worlds}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (sepcon X Y).
Proof.
  intros.
  hnf; intros.
  hnf in H2 |- *.
  destruct H2 as [n1 [n2 [? [? ?]]]].
  destruct (join_Korder_up _ _ _ _ H2 H1) as [m1 [m2 [? [? ?]]]].
  exists m1, m2.
  split; [| split]; auto.
  + apply (H n1); auto.
  + apply (H0 n2); auto.
Qed.

Lemma wand_closed
      {worlds: Type}
      {R: Relation worlds}
      {kiM: KripkeIntuitionisticModel worlds}
      {J: Join worlds}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (wand X Y).
Proof.
  intros.
  hnf; intros.
  hnf in H2 |- *.
  intros ? ? ? ?; apply H2.
  etransitivity; eauto.
Qed.

Lemma emp_closed
      {worlds: Type}
      {R: Relation worlds}
      {kiM: KripkeIntuitionisticModel worlds}
      {J: Join worlds}:
  upwards_closed_Kdenote emp.
Proof.
  intros.
  hnf; intros.
  hnf in H0 |- *.
  intros ? ?; apply H0.
  etransitivity; eauto.
Qed.

End Semantics.

Class SeparatingSemantics
      (L: Language)
      {sL: SeparationLanguage L}
      (MD: Model)
      {kMD: KripkeModel MD}
      (M: Kmodel)
      {R: Relation (Kworlds M)}
      {J: Join (Kworlds M)}
      (SM: Semantics L MD): Type :=
{
  denote_sepcon: forall x y, Same_set _ (Kdenotation M (x * y)) (Semantics.sepcon (Kdenotation M x) (Kdenotation M y));
  denote_wand: forall x y, Same_set _ (Kdenotation M (x -* y)) (Semantics.wand (Kdenotation M x) (Kdenotation M y))
}.

Class EmpSemantics
      (L: Language)
      {sL: SeparationLanguage L}
      {s'L: SeparationEmpLanguage L}
      (MD: Model)
      {kMD: KripkeModel MD}
      (M: Kmodel)
      {R: Relation (Kworlds M)}
      {J: Join (Kworlds M)}
      (SM: Semantics L MD): Type :=
  denote_emp: Same_set _ (Kdenotation M emp) Semantics.emp.

Lemma sat_sepcon
      {L: Language}
      {sL: SeparationLanguage L}
      {MD: Model}
      {kMD: KripkeModel MD}
      {M: Kmodel}
      {R: Relation (Kworlds M)}
      {J: Join (Kworlds M)}
      {SM: Semantics L MD}
      {usSM: SeparatingSemantics L MD M SM}:
  forall m x y,
    KRIPKE: M , m |= x * y <->
    exists m1 m2, join m1 m2 m /\
                  KRIPKE: M , m1 |= x /\
                  KRIPKE: M, m2 |= y.
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_sepcon x y).
  split; [apply H | apply H0].
Qed.

Lemma sat_wand
      {L: Language}
      {sL: SeparationLanguage L}
      {MD: Model}
      {kMD: KripkeModel MD}
      {M: Kmodel}
      {R: Relation (Kworlds M)}
      {J: Join (Kworlds M)}
      {SM: Semantics L MD}
      {usSM: SeparatingSemantics L MD M SM}:
  forall m x y,
    KRIPKE: M , m |= x -* y <->
    forall m0 m1 m2, m <= m0 ->
                     join m0 m1 m2 ->
                     KRIPKE: M , m1 |= x ->
                     KRIPKE: M, m2 |= y.
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_wand x y).
  split; [apply H | apply H0].
Qed.

Lemma sat_emp
      {L: Language}
      {sL: SeparationLanguage L}
      {s'L: SeparationEmpLanguage L}
      {MD: Model}
      {kMD: KripkeModel MD}
      {M: Kmodel}
      {R: Relation (Kworlds M)}
      {J: Join (Kworlds M)}
      {SM: Semantics L MD}
      {ueSM: EmpSemantics L MD M SM}:
  forall (m: Kworlds M), KRIPKE: M, m |= emp <-> increasing' m.
Proof.
  intros; simpl.
  unfold satisfies.
  destruct denote_emp.
  split; [apply H | apply H0].
Qed.
