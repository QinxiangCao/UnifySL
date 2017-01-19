Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.

Definition multi_imp {L: Language} {nL: NormalLanguage L} (xs: list expr) (y: expr): expr :=
  fold_right impp y xs.

Class NormalProofTheory (L: Language) {nL: NormalLanguage L} (Gamma: ProofTheory L): Type := {
  derivable_provable: forall Phi y, derivable Phi y <->
                        exists xs, Forall (fun x => Phi x) xs /\ provable (multi_imp xs y)
}.

Lemma provable_derivable {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma}: forall x, provable x <-> derivable empty_context x.
Proof.
  intros.
  rewrite derivable_provable.
  split; intros.
  + exists nil; split; auto.
  + destruct H as [xs [? ?]].
    destruct xs; [auto |].
    inversion H; subst.
    inversion H3.
Qed.

Lemma deduction_weaken {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma}: forall Phi Psi x,
  Included _ Phi Psi ->
  Phi |-- x ->
  Psi |-- x.
Proof.
  intros.
  rewrite derivable_provable in H0 |- *.
  destruct H0 as [xs [? ?]].
  exists xs; split; auto.
  revert H0; apply Forall_impl.
  auto.
Qed.

Lemma deduction_weaken1 {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma}: forall Phi x y,
  Phi |-- y ->
  Union _ Phi (Singleton _ x) |-- y.
Proof.
  intros.
  eapply deduction_weaken; eauto.
  intros ? ?; left; auto.
Qed.

Lemma deduction_weaken0 {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma}: forall Phi y,
  |-- y ->
  Phi |-- y.
Proof.
  intros.
  rewrite provable_derivable in H.
  eapply deduction_weaken; eauto.
  intros ? [].
Qed.

Lemma deduction_impp_elim {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma}: forall Phi x y,
  Phi |-- impp x y ->
  Union _ Phi (Singleton _ x) |-- y.
Proof.
  intros.
  rewrite derivable_provable in H |- *.
  destruct H as [xs [? ?]].
  exists (xs ++ (x :: nil)).
  split.
  + rewrite Forall_app_iff; split.
    - revert H; apply Forall_impl.
      intros.
      left; auto.
    - constructor; auto.
      right. constructor.
  + replace (multi_imp (xs ++ x :: nil) y) with (multi_imp xs (impp x y)); auto.
    clear.
    induction xs; auto.
    simpl; f_equal; auto.
Qed.

Definition Build_AxiomaticProofTheory {L: Language} {nL: NormalLanguage L} (Provable: expr -> Prop): ProofTheory L :=
  Build_ProofTheory L Provable
   (fun Phi y => exists xs, Forall (fun x => Phi x) xs /\ Provable (multi_imp xs y)).

Definition Build_nAxiomaticProofTheory {L: Language} {nL: NormalLanguage L} (Provable: expr -> Prop): NormalProofTheory L (Build_AxiomaticProofTheory Provable) :=
  Build_NormalProofTheory L nL (Build_AxiomaticProofTheory Provable) (fun _ _ => iff_refl _).

Definition Build_SequentCalculus {L: Language} {nL: NormalLanguage L} (Derivable: context -> expr -> Prop): ProofTheory L :=
  Build_ProofTheory L (fun x => Derivable (Empty_set _) x) Derivable.

