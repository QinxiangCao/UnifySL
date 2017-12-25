Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun2.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.

Class Adjointness (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L) (prodp funcp: expr -> expr -> expr): Prop := {
  adjoint: forall x y z, |-- prodp x y --> z <-> |-- x --> (funcp y z)
}.

Class Commutativity (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L) (prodp: expr -> expr -> expr): Prop := {
  prodp_comm_impp: forall x y, |-- prodp x y --> prodp y x
}.

Class Associativity (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L) (prodp: expr -> expr -> expr): Prop := {
  prodp_assoc1: forall x y z, |-- prodp x (prodp y z) --> prodp (prodp x y) z;
  prodp_assoc2: forall x y z, |-- prodp (prodp x y) z --> prodp x (prodp y z)
}.

Class LeftUnit (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L) (unit: expr) (prodp: expr -> expr -> expr): Prop := {
  left_unit1: forall x, |-- prodp unit x --> x;
  left_unit2: forall x, |-- x --> prodp unit x
}.

Section AdjointTheorems.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}
        {prodp funcp: expr -> expr -> expr}
        {Adj: Adjointness L Gamma prodp funcp}.

Lemma prodp_mono1: forall x1 x2 y, |-- x1 --> x2 -> |-- prodp x1 y --> prodp x2 y.
Proof.
  intros.
  apply adjoint.
  rewrite H.
  apply adjoint.
  apply provable_impp_refl.
Qed.

Lemma funcp_mono2: forall x y1 y2, |-- y1 --> y2 -> |-- funcp x y1 --> funcp x y2.
Proof.
  intros.
  apply adjoint.
  rewrite <- H.
  apply adjoint.
  apply provable_impp_refl.
Qed.

Lemma adjoint_modus_ponens:
  forall x y, |-- prodp (funcp x y) x --> y.
Proof.
  intros.
  apply adjoint.
  apply provable_impp_refl.
Qed.

Lemma adjoint_iter:
  forall x xs y,
    |-- fold_left prodp xs x --> y <-> |-- x --> (fold_right funcp y xs).
Proof.
  intros.
  revert x; induction xs; intros; simpl in *.
  + reflexivity.
  + rewrite <- adjoint.
    auto.
Qed.

Section AdjointCommutativeTheorems.

Context {Comm: Commutativity L Gamma prodp}.

Lemma prodp_mono: forall x1 y1 x2 y2, |-- x1 --> x2 -> |-- y1 --> y2 -> |-- prodp x1 y1 --> prodp x2 y2.
Proof.
  intros.
  apply aux_minimun_rule02 with (prodp x2 y1).
  + apply prodp_mono1; auto.
  + rewrite (prodp_comm_impp x2 y1).
    rewrite <- (prodp_comm_impp y2 x2).
    apply prodp_mono1; auto.
Qed.

Lemma funcp_mono: forall x1 y1 x2 y2, |-- x2 --> x1 -> |-- y1 --> y2 -> |-- funcp x1 y1 --> funcp x2 y2.
Proof.
  intros.
  apply adjoint.
  rewrite <- H0.
  rewrite <- (adjoint_modus_ponens x1 y1) at 2.
  apply prodp_mono.
  + apply provable_impp_refl.
  + auto.
Qed.

End AdjointCommutativeTheorems.

End AdjointTheorems.
