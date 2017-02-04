Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Sound.Sound_Kripke.
Require Import Logic.GeneralLogic.ShallowEmbedded.MonoPredicateAsLang.

Instance MonoPred_nL (A: Type) {R: Relation A} {kiM: KripkeIntuitionisticModel A}: NormalLanguage (MonoPred_L A) := Build_NormalLanguage (MonoPred_L A) SemanticsMono.impp.
Instance MonoPred_pL (A: Type) {R: Relation A} {kiM: KripkeIntuitionisticModel A}: PropositionalLanguage (MonoPred_L A) := Build_PropositionalLanguage (MonoPred_L A) (MonoPred_nL A) SemanticsMono.andp SemanticsMono.orp SemanticsMono.falsep.

Instance MonoPred_kiSM (A: Type) {R: Relation A} {kiM: KripkeIntuitionisticModel A}: KripkeIntuitionisticSemantics (MonoPred_L A) (Build_Model A) (tt: @Kmodel _ (unit_kMD (Build_Model A))) (MonoPred_SM A).
Proof.
  constructor.
  + intros; apply (proj2_sig _).
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
  + apply Same_set_refl.
Qed.

Instance MonoPred_Gamma (A: Type) {R: Relation A} {kiM: KripkeIntuitionisticModel A}: ProofTheory (MonoPred_L A) := Build_AxiomaticProofTheory (fun x: expr => forall a: A, proj1_sig x a).

Instance MonoPred_nGamma (A: Type) {R: Relation A} {kiM: KripkeIntuitionisticModel A}: NormalProofTheory (MonoPred_L A) (MonoPred_Gamma A) := Build_nAxiomaticProofTheory (fun x: expr => forall a: A, proj1_sig x a).

Instance MonoPred_mpGamma (A: Type) {R: Relation A} {kiM: KripkeIntuitionisticModel A}: MinimunPropositionalLogic (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  + intros x y ? ? m.
    pose proof @sound_modus_ponens (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R kiM (MonoPred_SM A) (MonoPred_kiSM A) x y.
    exact (H1 m (H m) (H0 m)).
  + intros x y.
    exact (@sound_axiom1 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R kiM (MonoPred_SM A) (MonoPred_kiSM A) x y).
  + intros x y z.
    exact (@sound_axiom2 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R kiM (MonoPred_SM A) (MonoPred_kiSM A) x y z).
Qed.

Instance MonoPred_ipGamma (A: Type) {R: Relation A} {kiM: KripkeIntuitionisticModel A}: IntuitionisticPropositionalLogic (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  + intros x y.
    exact (@sound_andp_intros (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R kiM (MonoPred_SM A) (MonoPred_kiSM A) x y).
  + intros x y.
    exact (@sound_andp_elim1 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R kiM (MonoPred_SM A) (MonoPred_kiSM A) x y).
  + intros x y.
    exact (@sound_andp_elim2 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R kiM (MonoPred_SM A) (MonoPred_kiSM A) x y).
  + intros x y.
    exact (@sound_orp_intros1 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R kiM (MonoPred_SM A) (MonoPred_kiSM A) x y).
  + intros x y.
    exact (@sound_orp_intros2 (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R kiM (MonoPred_SM A) (MonoPred_kiSM A) x y).
  + intros x y z.
    exact (@sound_orp_elim (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R kiM (MonoPred_SM A) (MonoPred_kiSM A) x y z).
  + intros x.
    exact (@sound_falsep_elim (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R kiM (MonoPred_SM A) (MonoPred_kiSM A) x).
Qed.

Instance MonoPred_gdpGamma (A: Type) {R: Relation A} {kiM: KripkeIntuitionisticModel A} {nkiM: NoBranchKripkeIntuitionisticModel A}: GodelDummettPropositionalLogic (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  intros x y.
  exact (@sound_impp_choice_no_branch (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R kiM nkiM (MonoPred_SM A) (MonoPred_kiSM A) x y).
Qed.

Instance MonoPred_dmpGamma (A: Type) {R: Relation A} {kiM: KripkeIntuitionisticModel A} {bkiM: BranchJoinKripkeIntuitionisticModel A}: DeMorganPropositionalLogic (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  intros x.
  exact (@sound_weak_excluded_middle_branch_join (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R kiM bkiM (MonoPred_SM A) (MonoPred_kiSM A) x).
Qed.

Instance MonoPred_cpGamma (A: Type) {R: Relation A} {kiM: KripkeIntuitionisticModel A} {ikiM: IdentityKripkeIntuitionisticModel A}: ClassicalPropositionalLogic (MonoPred_L A) (MonoPred_Gamma A).
Proof.
  constructor.
  intros x.
  exact (@sound_excluded_middle_ident (MonoPred_L A) _ _ (Build_Model A) (unit_kMD (Build_Model A)) tt R kiM ikiM (MonoPred_SM A) (MonoPred_kiSM A) x).
Qed.
