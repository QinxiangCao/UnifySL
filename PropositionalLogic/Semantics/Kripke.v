Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Module Semantics.

Definition impp {worlds: Type} {R: Relation worlds} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => forall n, m <= n -> X n -> Y n.

Definition andp {worlds: Type} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => X m /\ Y m.

Definition orp {worlds: Type} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => X m \/ Y m.

Definition falsep {worlds: Type}: Ensemble worlds := fun m => False.

Lemma impp_closed {worlds: Type} {R: Relation worlds} {kiM: KripkeIntuitionisticModel worlds}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (impp X Y).
Proof.
  intros.
  hnf; intros.
  hnf in H2 |- *.
  intros ? ?; apply H2.
  etransitivity; eauto.
Qed.

Lemma andp_closed {worlds: Type} {R: Relation worlds} {kiM: KripkeIntuitionisticModel worlds}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (andp X Y).
Proof.
  intros.
  hnf; intros.
  destruct H2.
  split.
  + apply (H n); auto.
  + apply (H0 n); auto.
Qed.

Lemma orp_closed {worlds: Type} {R: Relation worlds} {kiM: KripkeIntuitionisticModel worlds}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (orp X Y).
Proof.
  intros.
  hnf; intros.
  destruct H2; [left | right].
  + apply (H n); auto.
  + apply (H0 n); auto.
Qed.

Lemma falsep_closed {worlds: Type} {R: Relation worlds}:
  upwards_closed_Kdenote falsep.
Proof.
  intros.
  hnf; intros.
  inversion H0.
Qed.

End Semantics.

Module SemanticsMono.

Program Definition impp {worlds: Type} {R: Relation worlds} {kiM: KripkeIntuitionisticModel worlds} (X Y: MonoEnsemble worlds): MonoEnsemble worlds :=
  Semantics.impp X Y.
Next Obligation.
  apply (@Semantics.impp_closed worlds R kiM);
  apply (proj2_sig _).
Defined.

Program Definition andp {worlds: Type} {R: Relation worlds} {kiM: KripkeIntuitionisticModel worlds} (X Y: MonoEnsemble worlds): MonoEnsemble worlds :=
  Semantics.andp X Y.
Next Obligation.
  apply (@Semantics.andp_closed worlds R kiM);
  apply (proj2_sig _).
Defined.

Program Definition orp {worlds: Type} {R: Relation worlds} {kiM: KripkeIntuitionisticModel worlds} (X Y: MonoEnsemble worlds): MonoEnsemble worlds :=
  Semantics.orp X Y.
Next Obligation.
  apply (@Semantics.orp_closed worlds R kiM);
  apply (proj2_sig _).
Defined.

Program Definition falsep {worlds: Type} {R: Relation worlds}: MonoEnsemble worlds :=
  Semantics.falsep.
Next Obligation.
  apply (@Semantics.falsep_closed worlds R);
  apply (proj2_sig _).
Defined.

End SemanticsMono.

Class KripkeIntuitionisticSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {R: Relation (Kworlds M)} {kiM: KripkeIntuitionisticModel (Kworlds M)} (SM: Semantics L MD) : Type := {
  denote_closed: forall x, upwards_closed_Kdenote (Kdenotation M x);
  denote_impp: forall x y, Same_set _ (Kdenotation M (x --> y)) (Semantics.impp (Kdenotation M x) (Kdenotation M y));
  denote_andp: forall x y, Same_set _ (Kdenotation M (x && y)) (Semantics.andp (Kdenotation M x) (Kdenotation M y));
  denote_orp: forall x y, Same_set _ (Kdenotation M (x || y)) (Semantics.orp (Kdenotation M x) (Kdenotation M y));
  denote_falsep: Same_set _ (Kdenotation M FF) Semantics.falsep
}.

Lemma sat_mono {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {kiM: KripkeIntuitionisticModel (Kworlds M)} {SM: Semantics L MD} {kSM: KripkeIntuitionisticSemantics L MD M SM}: forall m n x, m <= n -> KRIPKE: M , m |= x -> KRIPKE: M , n |= x.
Proof.
  intros ? ? ? ?.
  unfold satisfies.
  apply (denote_closed x); auto.
Qed.

Lemma sat_impp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {kiM: KripkeIntuitionisticModel (Kworlds M)} {SM: Semantics L MD} {kSM: KripkeIntuitionisticSemantics L MD M SM}: forall m x y, KRIPKE: M , m |= x --> y <-> (forall n, m <= n -> KRIPKE: M , n |= x -> KRIPKE: M , n |= y).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_impp x y).
  split; [apply H | apply H0].
Qed.

Lemma sat_andp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {kiM: KripkeIntuitionisticModel (Kworlds M)} {SM: Semantics L MD} {kSM: KripkeIntuitionisticSemantics L MD M SM}: forall m x y, KRIPKE: M , m |= x && y <-> (KRIPKE: M , m |= x /\ KRIPKE: M , m |= y).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_andp x y).
  split; [apply H | apply H0].
Qed.

Lemma sat_orp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {kiM: KripkeIntuitionisticModel (Kworlds M)} {SM: Semantics L MD} {kSM: KripkeIntuitionisticSemantics L MD M SM}: forall m x y, KRIPKE: M , m |= x || y <-> (KRIPKE: M , m |= x \/ KRIPKE: M , m |= y).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_orp x y).
  split; [apply H | apply H0].
Qed.

Lemma sat_falsep {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {kiM: KripkeIntuitionisticModel (Kworlds M)} {SM: Semantics L MD} {kSM: KripkeIntuitionisticSemantics L MD M SM}: forall m, KRIPKE: M , m |= FF <-> False.
Proof.
  intros; simpl.
  unfold satisfies.
  destruct denote_falsep.
  split; [apply H | apply H0].
Qed.
