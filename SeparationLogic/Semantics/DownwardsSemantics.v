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

Definition sepcon {worlds: Type} {R: Relation worlds} {J: Join worlds} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => exists m0 m1 m2, m0 <= m /\ join m1 m2 m0 /\ X m1 /\ Y m2.

Definition wand {worlds: Type} {J: Join worlds} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => forall m1 m2, join m m1 m2 -> X m1 -> Y m2.

Definition emp {worlds: Type} {R: Relation worlds} {J: Join worlds}: Ensemble worlds := increasing.

Lemma sepcon_closed
      {worlds: Type}
      {R: Relation worlds}
      {kiM: KripkeIntuitionisticModel worlds}
      {J: Join worlds}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (sepcon X Y).
Proof.
  intros.
  hnf; intros.
  hnf in H2 |- *.
  destruct H2 as [n0 [n1 [n2 [? [? [? ?]]]]]].
  exists n0, n1, n2; split; [| split; [| split]]; auto.
  etransitivity; eauto.
Qed.

Lemma wand_closed
      {worlds: Type}
      {R: Relation worlds}
      {kiM: KripkeIntuitionisticModel worlds}
      {J: Join worlds}
      {SA: SeparationAlgebra worlds}
      {dSA: DownwardsClosedSeparationAlgebra worlds}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (wand X Y).
Proof.
  intros.
  hnf; intros.
  hnf in H2 |- *.
  intros.
  destruct (join_Korder_down _ _ _ _ _ H3 H1 ltac:(reflexivity)) as [m2' [? ?]].
  apply (H0 m2'); auto.
  apply (H2 m1); auto.
Qed.

Lemma emp_closed
      {worlds: Type}
      {R: Relation worlds}
      {kiM: KripkeIntuitionisticModel worlds}
      {J: Join worlds}
      {SA: SeparationAlgebra worlds}
      {dSA: DownwardsClosedSeparationAlgebra worlds}:
  upwards_closed_Kdenote emp.
Proof.
  intros.
  hnf; intros.
  hnf in H0 |- *.
  intros.
  destruct (join_Korder_down _ _ _ _ _ H1 H ltac:(reflexivity)) as [n'' [? ?]].
  etransitivity; eauto.
Qed.

End Semantics.

Class SeparatingSemantics
      (L: Language)
      {SL: SeparationLanguage L}
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
      {dsSM: SeparatingSemantics L MD M SM}:
  forall m x y,
    KRIPKE: M , m |= x * y <->
    exists m0 m1 m2, m0 <= m /\
                     join m1 m2 m0 /\
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
      {dsSM: SeparatingSemantics L MD M SM}:
  forall m x y,
    KRIPKE: M , m |= x -* y <->
    forall m1 m2, join m m1 m2 ->
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
      {deSM: EmpSemantics L MD M SM}:
  forall (m: Kworlds M), KRIPKE: M, m |= emp <-> increasing m.
Proof.
  intros; simpl.
  unfold satisfies.
  destruct denote_emp.
  split; [apply H | apply H0].
Qed.
