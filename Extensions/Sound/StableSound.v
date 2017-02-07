Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.Extensions.Semantics.SemanticStable.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Module Sound_Trivial.

Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.ModalLogic.Semantics.Kripke.

Lemma sound_impp_stable {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: SS.Relation (Kworlds M)} {SM: Semantics L MD} {trSM: TrivialPropositionalSemantics L MD SM} {stableSM: SemanticStable L MD M SM}:
  forall x y: expr,
    semantic_stable x -> semantic_stable y -> semantic_stable (x --> y).
Proof.
  intros.
  rewrite denote_stable in H, H0 |- *.
  unfold Semantics.stable in *.
  intros.
  unfold Kdenotation in *; simpl in *.
  rewrite !(app_same_set (denote_impp _ _)).
  unfold Semantics.impp; simpl.
  specialize (H _ _ H1).
  specialize (H0 _ _ H1).
  tauto.
Qed.

Lemma sound_andp_stable {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: SS.Relation (Kworlds M)} {SM: Semantics L MD} {trSM: TrivialPropositionalSemantics L MD SM} {stableSM: SemanticStable L MD M SM}:
  forall x y: expr,
    semantic_stable x -> semantic_stable y -> semantic_stable (x && y).
Proof.
  intros.
  rewrite denote_stable in H, H0 |- *.
  unfold Semantics.stable in *.
  intros.
  unfold Kdenotation in *; simpl in *.
  rewrite !(app_same_set (denote_andp _ _)).
  unfold Semantics.andp; simpl.
  specialize (H _ _ H1).
  specialize (H0 _ _ H1).
  tauto.
Qed.

Lemma sound_orp_stable {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: SS.Relation (Kworlds M)} {SM: Semantics L MD} {trSM: TrivialPropositionalSemantics L MD SM} {stableSM: SemanticStable L MD M SM}:
  forall x y: expr,
    semantic_stable x -> semantic_stable y -> semantic_stable (x || y).
Proof.
  intros.
  rewrite denote_stable in H, H0 |- *.
  unfold Semantics.stable in *.
  intros.
  unfold Kdenotation in *; simpl in *.
  rewrite !(app_same_set (denote_orp _ _)).
  unfold Semantics.orp; simpl.
  specialize (H _ _ H1).
  specialize (H0 _ _ H1).
  tauto.
Qed.

Lemma sound_falsep_stable {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: SS.Relation (Kworlds M)} {SM: Semantics L MD} {trSM: TrivialPropositionalSemantics L MD SM} {stableSM: SemanticStable L MD M SM}:
  semantic_stable falsep.
Proof.
  intros.
  rewrite denote_stable.
  unfold Semantics.stable.
  intros.
  unfold Kdenotation.
  rewrite !(app_same_set denote_falsep).
  reflexivity.
Qed.

Lemma sound_boxp_stable {L: Language} {nL: NormalLanguage L} {mL: ModalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KM.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {KMbis: KripkeModalBisStable (Kworlds M)} {SM: Semantics L MD} {kmSM: KripkeModalSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x: expr,
    semantic_stable x -> semantic_stable (boxp x).
Proof.
  intros.
  rewrite denote_stable in H |- *.
  unfold Semantics.stable in *.
  intros.
  rewrite !(app_same_set (denote_boxp _)).
  unfold Semantics.boxp; simpl.
  pose proof KM_bis_stable _ _ H0.
  split; intros.
  + destruct H1 as [_ ?].
    specialize (H1 _ H3).
    destruct H1 as [m0 [? ?]].
    specialize (H2 _ H1).
    specialize (H _ _ H4).
    tauto.
  + rename n0 into m0.
    destruct H1 as [? _].
    specialize (H1 _ H3).
    destruct H1 as [n0 [? ?]].
    specialize (H2 _ H1).
    specialize (H _ _ H4).
    tauto.
Qed.

Lemma sound_boxp_absorb_stable {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KM.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {KMabs: KripkeModalAbsorbStable (Kworlds M)} {SM: Semantics L MD} {trSM: TrivialPropositionalSemantics L MD SM} {kmSM: KripkeModalSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x: expr,
    semantic_stable x ->
    (forall (m: Kworlds M), KRIPKE: M, m |= x --> boxp x).
Proof.
  intros.
  rewrite sat_impp, sat_boxp.
  intros.
  rewrite denote_stable in H.
  unfold Semantics.stable in H.
  apply KM_absorb_stable in H1.
  specialize (H _ _ H1).
  tauto.
Qed.

End Sound_Trivial.

Module Sound_KripkeIntuitionistic.

Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.ModalLogic.Semantics.Flat.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.

Lemma sound_impp_stable {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {KIbis: KripkeIntuitionisticBisStable (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x y: expr,
    semantic_stable x -> semantic_stable y -> semantic_stable (x --> y).
Proof.
  intros.
  rewrite denote_stable in H, H0 |- *.
  unfold Semantics.stable in *.
  intros.
  rewrite !(app_same_set (denote_impp _ _)).
  unfold Semantics.impp; simpl.
  pose proof KI_bis_stable _ _ H1.
  split; intros.
  + destruct H2 as [_ ?].
    specialize (H2 _ H4).
    destruct H2 as [m0 [? ?]].
    specialize (H3 _ H2).
    specialize (H _ _ H6).
    specialize (H0 _ _ H6).
    tauto.
  + rename n0 into m0.
    destruct H2 as [? _].
    specialize (H2 _ H4).
    destruct H2 as [n0 [? ?]].
    specialize (H3 _ H2).
    specialize (H _ _ H6).
    specialize (H0 _ _ H6).
    tauto.
Qed.

Lemma sound_andp_stable {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x y: expr,
    semantic_stable x -> semantic_stable y -> semantic_stable (x && y).
Proof.
  intros.
  rewrite denote_stable in H, H0 |- *.
  unfold Semantics.stable in *.
  intros.
  rewrite !(app_same_set (denote_andp _ _)).
  unfold Semantics.andp; simpl.
  specialize (H _ _ H1).
  specialize (H0 _ _ H1).
  tauto.
Qed.

Lemma sound_orp_stable {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x y: expr,
    semantic_stable x -> semantic_stable y -> semantic_stable (x || y).
Proof.
  intros.
  rewrite denote_stable in H, H0 |- *.
  unfold Semantics.stable in *.
  intros.
  rewrite !(app_same_set (denote_orp _ _)).
  unfold Semantics.orp; simpl.
  specialize (H _ _ H1).
  specialize (H0 _ _ H1).
  tauto.
Qed.

Lemma sound_falsep_stable {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  semantic_stable falsep.
Proof.
  intros.
  rewrite denote_stable.
  unfold Semantics.stable.
  intros.
  rewrite !(app_same_set denote_falsep).
  reflexivity.
Qed.

Lemma sound_boxp_stable {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: KM.Relation (Kworlds M)} {R3: SS.Relation (Kworlds M)} {KMbis: KripkeModalBisStable (Kworlds M)} {SM: Semantics L MD} {fmSM: FlatModalSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x: expr,
    semantic_stable x -> semantic_stable (boxp x).
Proof.
  intros.
  rewrite denote_stable in H |- *.
  unfold Semantics.stable in *.
  intros.
  rewrite !(app_same_set (denote_boxp _)).
  unfold Semantics.boxp; simpl.
  pose proof KM_bis_stable _ _ H0.
  split; intros.
  + destruct H1 as [_ ?].
    specialize (H1 _ H3).
    destruct H1 as [m0 [? ?]].
    specialize (H2 _ H1).
    specialize (H _ _ H4).
    tauto.
  + rename n0 into m0.
    destruct H1 as [? _].
    specialize (H1 _ H3).
    destruct H1 as [n0 [? ?]].
    specialize (H2 _ H1).
    specialize (H _ _ H4).
    tauto.
Qed.

Lemma sound_boxp_absorb_stable {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {mL: ModalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: KM.Relation (Kworlds M)} {R3: SS.Relation (Kworlds M)} {KMabs: KripkeModalAbsorbStable (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM} {fmSM: FlatModalSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x: expr,
    semantic_stable x ->
    (forall (m: Kworlds M), KRIPKE: M, m |= x --> boxp x).
Proof.
  intros.
  rewrite sat_impp.
  intros.
  rewrite sat_boxp.
  intros.
  rewrite denote_stable in H.
  unfold Semantics.stable in H.
  apply KM_absorb_stable in H2.
  specialize (H _ _ H2).
  tauto.
Qed.

Lemma sound_sepcon_stable {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: SS.Relation (Kworlds M)} {J: Join (Kworlds M)} {SAbis: SeparationAlgebraBisStable (Kworlds M)} {SM: Semantics L MD} {fsSM: SeparatingSemantics L MD M SM} {stableSM: SemanticStable L MD M SM}:
  forall x y: expr,
    semantic_stable x -> semantic_stable y -> semantic_stable (x * y).
Proof.
  intros.
  rewrite denote_stable in H, H0 |- *.
  unfold Semantics.stable in *.
  intros.
  rewrite !(app_same_set (denote_sepcon _ _)).
  unfold WeakSemantics.sepcon; simpl.
  pose proof split_bis_stable _ _ H1.
  split; intros.
  + destruct H2 as [? _].
    destruct H3 as [m1 [m2 [? [? ?]]]].
    specialize (H2 _ _ H3).
    destruct H2 as [n1 [n2 [? [? ?]]]].
    exists n1, n2.
    specialize (H _ _ H6).
    specialize (H0 _ _ H7).
    tauto.
  + destruct H2 as [_ ?].
    destruct H3 as [n1 [n2 [? [? ?]]]].
    specialize (H2 _ _ H3).
    destruct H2 as [m1 [m2 [? [? ?]]]].
    exists m1, m2.
    specialize (H _ _ H6).
    specialize (H0 _ _ H7).
    tauto.
Qed.

End Sound_KripkeIntuitionistic.
