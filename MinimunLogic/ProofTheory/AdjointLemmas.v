Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.List_Func_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Adjoint.
Require Import Logic.MinimunLogic.ProofTheory.Minimun1.
Require Import Logic.MinimunLogic.ProofTheory.Minimun2.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.

Module Adjoint.

Section Adjoint.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {mAX: MinimunAxiomatization L Gamma}
        {prodp funcp: expr -> expr -> expr}
        {adjGamma: AdjointProofTheory L Gamma prodp funcp}.

Lemma modus_ponens:
  forall x y, |-- prodp (funcp x y) x --> y.
Proof.
  intros.
  apply adjoint.
  apply provable_impp_refl.
Qed.

Lemma funcp_mono: forall x1 y1 x2 y2, |-- x2 --> x1 -> |-- y1 --> y2 -> |-- funcp x1 y1 --> funcp x2 y2.
Proof.
  intros.
  apply adjoint.
  rewrite <- H0.
  rewrite <- (modus_ponens x1 y1) at 2.
  apply prodp_mono.
  + apply provable_impp_refl.
  + auto.
Qed.

Lemma curry_iter:
  forall default xs y,
    not_nil xs ->
    |-- funcp (iter_prodp default prodp xs) y --> iter_funcp funcp xs y.
Proof.
  intros.
  destruct xs as [| x xs]; [exfalso; apply H; auto |].
  clear H.
  revert x; induction xs; intros; simpl in *.
  + apply provable_impp_refl.
  + specialize (IHxs (prodp x a)).
    rewrite IHxs.
    apply -> adjoint.
    apply -> adjoint.
    rewrite assoc2.
    apply modus_ponens.
Qed.

Lemma uncurry_iter:
  forall default xs y,
    not_nil xs ->
    |-- iter_funcp funcp xs y --> funcp (iter_prodp default prodp xs) y.
Proof.
  intros.
  destruct xs as [| x xs]; [exfalso; apply H; auto |].
  clear H.
  revert x; induction xs; intros; simpl in *.
  + apply provable_impp_refl.
  + specialize (IHxs (prodp x a)).
    rewrite <- IHxs.
    apply -> adjoint.
    rewrite assoc1.
    rewrite <- (modus_ponens a (iter_funcp funcp xs y)) at 2.
    apply prodp_mono; [| apply provable_impp_refl].
    apply modus_ponens.
Qed.

End Adjoint.

End Adjoint.

