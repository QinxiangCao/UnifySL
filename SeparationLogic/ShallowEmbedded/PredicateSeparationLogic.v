Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.RelationPairs_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ShallowEmbedded.PredicatePropositionalLogic.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Import Logic.SeparationLogic.Semantics.StrongSemantics.
Require Import Logic.SeparationLogic.Sound.Sound_Flat.

Instance Pred_sepconL (A: Type) {J: Join A}: SepconLanguage (Pred_L A) :=
  Build_SepconLanguage (Pred_L A) WeakSemantics.sepcon.

Instance Pred_wandL (A: Type) {J: Join A}: WandLanguage (Pred_L A) :=
  Build_WandLanguage (Pred_L A) WeakSemantics.wand.

Instance Pred_empL (A: Type) {J: Join A}: EmpLanguage (Pred_L A) := 
  Build_EmpLanguage (Pred_L A) (@WeakSemantics.emp _ eq J).

Instance Pred_fsSM (A: Type) {J: Join A}: @FlatSemantics.SeparatingSemantics (Pred_L A) (Pred_sepconL A) (Pred_wandL A) (Build_Model A) (unit_kMD _) tt eq J (Pred_SM A).
Proof.
  constructor.
  + intros; apply Same_set_refl.
  + intros; apply Same_set_refl.
Qed.

Instance Pred_feSM (A: Type) {J: Join A}: @FlatSemantics.EmpSemantics (Pred_L A) (Pred_sepconL A) (Pred_wandL A)  (Pred_empL A) (Build_Model A) (unit_kMD _) tt eq J (Pred_SM A).
Proof.
  apply Same_set_refl.
Qed.

Instance Pred_sepconAX_weak (A: Type) {J: Join A} {SA: SeparationAlgebra A}: SepconAxiomatization_weak (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  + intros x y.
    exact (@sound_sepcon_comm (Pred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt eq J SA (Pred_SM A) (Pred_kminSM A) (Pred_fsSM A) x y).
  + intros x y.
    exact (@sound_sepcon_assoc1 (Pred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt eq J SA (Pred_SM A) (Pred_kminSM A) (Pred_fsSM A) x y).
Qed.

Instance Pred_wandAX (A: Type) {J: Join A} {SA: SeparationAlgebra A}: WandAxiomatization (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  intros x y z.
  exact (@sound_wand_sepcon_adjoint (Pred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt eq (eq_preorder _) J (Pred_SM A) (Pred_kminSM A) (Pred_fsSM A) x y z).
Qed.

Instance Pred_sepconAX (A: Type) {J: Join A} {SA: SeparationAlgebra A}: SepconAxiomatization (Pred_L A) (Pred_Gamma A).
Proof.
  eapply @SepconAxiomatizationWeak2SepconAxiomatization;
  try typeclasses eauto.
  eapply @Adj2SepconMono;
  try typeclasses eauto.
Qed.

Instance Pred_gcsGamma (A: Type) {J: Join A} {SA: SeparationAlgebra A} {incrSA: @IncreasingSeparationAlgebra A eq J}: GarbageCollectSeparationLogic (Pred_L A) (Pred_Gamma A).
Proof.
  intros.
  constructor.
  intros x y.
  exact (@sound_sepcon_elim1 (Pred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt eq J SA (Pred_SM A) (Pred_kiSM A) (Pred_kminSM A) (Pred_fsSM A) incrSA x y).
Qed.

Instance Pred_EmpsGamma (A: Type) {J: Join A} {SA: SeparationAlgebra A} {USA: @UnitalSeparationAlgebra A eq J}: EmpAxiomatization (Pred_L A) (Pred_Gamma A).
Proof.
  constructor.
  + intros x.
    exact (@sound_sepcon_emp1 (Pred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt eq J SA(Pred_SM A) (Pred_kiSM A) (Pred_kminSM A) (Pred_fsSM A) _ (Pred_feSM A) USA x).
  + intros x.
    exact (@sound_sepcon_emp2 (Pred_L A) _ _ _ (Build_Model A) (unit_kMD _) tt eq J SA(Pred_SM A) (Pred_kiSM A) (Pred_kminSM A) (Pred_fsSM A) _ (Pred_feSM A) USA x).
Qed.

