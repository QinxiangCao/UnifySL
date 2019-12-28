Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Require Import Logic.MinimumLogic.Sound.Sound_Classical_Trivial.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Sound.Sound_Classical_Trivial.

(* TODO: split part of this file into MinimumLogic folder. *)

Instance Pred_minL (A: Type): MinimumLanguage (Pred_L A) := Build_MinimumLanguage (Pred_L A) Semantics.impp.
Instance Pred_pL (A: Type): PropositionalLanguage (Pred_L A) := Build_PropositionalLanguage (Pred_L A) Semantics.andp Semantics.orp Semantics.falsep.

Instance Pred_tminSM (A: Type): TrivialMinimumSemantics (Pred_L A) (Build_Model A) (Pred_SM A).
Proof.
  constructor.
  intros; apply Same_set_refl.
Qed.

Instance Pred_tpSM (A: Type): TrivialPropositionalSemantics (Pred_L A) (Build_Model A) (Pred_SM A).
Proof.
  constructor.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
  + apply Same_set_refl.
Qed.

Instance Pred_Gamma (A: Type): Provable (Pred_L A) :=
  Build_Provable (Pred_L A) (fun x: expr => forall a: A, x a).

Instance Pred_minAX (A: Type): MinimumAxiomatization (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  + intros x y ? ? m.
    pose proof @sound_modus_ponens (Pred_L A) _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) x y.
    exact (H1 m (H m) (H0 m)).
  + intros x y.
    exact (@sound_axiom1 (Pred_L A) _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) x y).
  + intros x y z.
    exact (@sound_axiom2 (Pred_L A) _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) x y z).
Qed.

Instance Pred_ipAX (A: Type): IntuitionisticPropositionalLogic (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  + intros x y.
    exact (@sound_andp_intros (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) (Pred_tpSM A) x y).
  + intros x y.
    exact (@sound_andp_elim1 (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) (Pred_tpSM A) x y).
  + intros x y.
    exact (@sound_andp_elim2 (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) (Pred_tpSM A) x y).
  + intros x y.
    exact (@sound_orp_intros1 (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) (Pred_tpSM A) x y).
  + intros x y.
    exact (@sound_orp_intros2 (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) (Pred_tpSM A) x y).
  + intros x y z.
    exact (@sound_orp_elim (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) (Pred_tpSM A) x y z).
  + intros x.
    exact (@sound_falsep_elim (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) (Pred_tpSM A) x).
Qed.

Instance Pred_cpGamma (A: Type): ClassicalPropositionalLogic (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  intros x.
  exact (@sound_excluded_middle (Pred_L A) _ _ (Build_Model A) (Pred_SM A) (Pred_tminSM A) (Pred_tpSM A) x).
Qed.

Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.MinimumLogic.Semantics.SemanticEquiv.
Require Import Logic.PropositionalLogic.Semantics.Kripke.

Instance Pred_kiSM (A: Type): @KripkeIntuitionisticSemantics (Pred_L A) (Build_Model A) (unit_kMD _) tt eq (Pred_SM A) :=
  @eqR_KripkeIntuitionistic _ _ _.

Instance Pred_kminSM (A: Type): @KripkeMinimumSemantics (Pred_L A) (Pred_minL A) (Build_Model A) (unit_kMD _) tt eq (Pred_SM A) :=
  @Trivial2Kripke _ _ _ _ (Pred_tminSM A).

Instance Pred_kpSM (A: Type): @KripkePropositionalSemantics (Pred_L A) (Pred_minL A) (Pred_pL A) (Build_Model A) (unit_kMD _) tt eq (Pred_SM A) (Pred_kminSM A).
Proof.
  constructor.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
  + apply Same_set_refl.
Qed.
