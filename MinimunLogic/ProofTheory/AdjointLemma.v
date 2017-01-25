Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.List_Func_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Adjoint.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.

Local Open Scope logic_base.
Local Open Scope syntax.

Module Adjoint.

Lemma modus_ponens {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {prodp funcp: expr -> expr -> expr} {adjGamma: AdjointProofTheory L Gamma prodp funcp}:
  forall x y,
  |-- prodp (funcp x y) x --> y.
Proof.
  intros.
  apply adjoint.
  apply provable_impp_refl.
Qed.

Lemma curry_iter {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {prodp funcp: expr -> expr -> expr} {adjGamma: AdjointProofTheory L Gamma prodp funcp}:
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

Lemma uncurry_iter {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {prodp funcp: expr -> expr -> expr} {adjGamma: AdjointProofTheory L Gamma prodp funcp}:
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
Abort.

End Adjoint.