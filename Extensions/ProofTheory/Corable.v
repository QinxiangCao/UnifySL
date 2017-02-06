Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.Extensions.ProofTheory.Stable.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Class Corable (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} := {
  corable: expr -> Prop;
  corable_pstable: PropositionalStable L Gamma corable;
  corable_sstable: SeparationStable L Gamma corable;
  corable_andp_sepcon1: forall x y z, corable x -> |-- (x && y) * z <--> x && (y * z)
}.

Section Corable.

Context {L: Language}
        {nL: NormalLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {Gamma: ProofTheory L}
        {nGamma: NormalProofTheory L Gamma}
        {mpGamma: MinimunPropositionalLogic L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma}
        {CosGamma: Corable L Gamma}.

Lemma corable_andp: forall x y, corable x -> corable y -> corable (x && y).
Proof. intros. apply (@andp_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_orp: forall x y, corable x -> corable y -> corable (x || y).
Proof. intros. apply (@orp_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_impp: forall x y, corable x -> corable y -> corable (x --> y).
Proof. intros. apply (@impp_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_iffp: forall x y, corable x -> corable y -> corable (x <--> y).
Proof. intros. apply (@iffp_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_falsep: corable FF.
Proof. apply (@falsep_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_truep: corable TT.
Proof. apply (@truep_stable L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_sepcon: forall x y, corable x -> corable y -> corable (x * y).
Proof. intros. apply (@sepcon_stable L _ _ Gamma corable corable_sstable); auto. Qed.

Lemma corable_wand: forall x y, corable x -> corable y -> corable (x -* y).
Proof. intros. apply (@wand_stable L _ _ Gamma corable corable_sstable); auto. Qed.

Instance corable_proper_iff: Proper ((fun x y => |-- x <--> y) ==> iff) corable.
Proof. apply (@stable_proper_iffp L _ _ Gamma corable corable_pstable); auto. Qed.

Lemma corable_andp_sepcon2: forall x y z, corable y -> |-- (x && y) * z <--> y && (x * z).
Proof.
  intros.
  rewrite andp_comm.
  apply corable_andp_sepcon1; auto.
Qed.

Lemma corable_sepcon_andp1: forall x y z, corable y -> |-- x * (y && z) <--> y && (x * z).
Proof.
  intros.
  rewrite provable_sepcon_comm_iffp.
  rewrite (provable_sepcon_comm_iffp x z).
  apply corable_andp_sepcon1; auto.
Qed.

Lemma corable_sepcon_andp2: forall x y z, corable z -> |-- x * (y && z) <--> z && (x * y).
Proof.
  intros.
  rewrite andp_comm.
  apply corable_sepcon_andp1; auto.
Qed.

End Corable.




