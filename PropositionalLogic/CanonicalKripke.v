Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.MinimunLogic.SyntacticReduction.
Require Import Logic.MinimunLogic.ContextProperty.
Require Import Logic.MinimunLogic.HenkinCompleteness.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.IntuitionisticPropositionalLogic.
Require Import Logic.PropositionalLogic.KripkeSemantics.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Section Completeness.

Context (Var: Type).
Context (CV: Countable Var).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.
Instance R: SyntacticReduction L := IntuitionisticReduction.
Instance nR: NormalSyntacticReduction L R := PropositionalLanguage.nIntuitionisticReduction.

Definition DCS (Gamma: ProofTheory L): Type := sig (fun Phi =>
  derivable_closed Phi /\
  orp_witnessed Phi /\
  consistent Phi).

Record canonical (Gamma: ProofTheory L) {SM: Semantics L} {icSM: ReductionConsistentSemantics IntuitionisticReduction SM} {pkSM: PreKripkeSemantics L SM} {kiSM: KripkeIntuitionisticSemantics L SM} (M: Kmodel): Type := {
  underlying_surj :> surjection (Kworlds M) (DCS Gamma);
  canonical_relation_sound: forall m n m' n',
    underlying_surj m m' ->
    underlying_surj n n' ->
    Korder m n ->
    Included _ (proj1_sig n') (proj1_sig m');
  canonical_relation_complete: forall n m' n',
    underlying_surj n n' ->
    Included _ (proj1_sig n') (proj1_sig m') ->
    exists m,
    underlying_surj m m' /\ Korder m n
}.

Lemma Lindenbaum_lemma {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {icGamma: ReductionConsistentProofTheory IntuitionisticReduction Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma}:
  forall Phi x,
    ~ Phi |-- x ->
    exists Psi,
      Included _ Phi Psi /\
      ~ Psi |-- x /\
      derivable_closed Psi /\
      orp_witnessed Psi /\
      consistent Psi.
Proof.
  intros.
  assert (Countable expr) by (apply PropositionalLanguage.formula_countable; auto).
  set (step :=
          fun n Phi x0 =>
             Phi x0 \/
            (X x0 n /\
             ~ (Union _ Phi (Singleton _ x0)) |-- x)).
  exists (LindenbaumConstruction step Phi).
  assert (Included expr Phi (LindenbaumConstruction step Phi) /\
          ~ LindenbaumConstruction step Phi |-- x /\
          (~ LindenbaumConstruction step Phi |-- x ->
           derivable_closed (LindenbaumConstruction step Phi)) /\
          (~ LindenbaumConstruction step Phi |-- x ->
           orp_witnessed (LindenbaumConstruction step Phi))).
  Focus 2. {
    destruct H0 as [? [? [? ?]]].
    split; [| split; [| split; [| split]]]; auto.
    intro; apply H1.
    pose proof falsep_elim_derivable (LindenbaumConstruction step Phi) x.
    eapply derivable_modus_ponens; [exact H4 | exact H5].
  } Unfocus.
  split; [| split; [| split]].
  + apply (Lindenbaum_spec_included _ _ 0).
  + apply (Lindenbaum_spec_pos _ _
            (fun xs => |-- multi_imp xs x)
            (fun Phi => Phi |-- x)).
    - intros; apply derivable_provable.
    - intros ? ? ? ?; left; auto.
    - apply H.
    - intros.
      destruct (Classical_Prop.classic (exists x0, X x0 n /\ ~ (Union _ S (Singleton _ x0)) |-- x)) as [[x0 [? ?]] |].
      * intro; apply H2; clear H2.
        eapply derivable_weaken; [| exact H3].
        hnf; intros ? [? | [? ?]]; [left; auto |].
        pose proof in_inj _ _ X _ _ _ H1 H2.
        subst; right; constructor.
      * intro; apply H0; clear H0.
        eapply derivable_weaken; [| exact H2].
        hnf; intros ? [? | [? ?]]; [auto |].
        exfalso; apply H1; clear H1.
        exists x0; auto.
  + intros; hnf; intros.
    destruct (im_inj _ _ X x0) as [n ?].
    apply (Lindenbaum_spec_neg _ _ _ (S n)).
    simpl.
    unfold step at 1.
    right; split; auto.
    intro.
    rewrite deduction_theorem in H3.
    eapply derivable_weaken in H3; [| apply (Lindenbaum_spec_included _ _ n)].
    pose proof derivable_modus_ponens _ _ _ H1 H3.
    auto.
  + intros; hnf; intros x0 y0 ?.
    destruct (im_inj _ _ X x0) as [nx ?].
    destruct (im_inj _ _ X y0) as [ny ?].
    assert (LindenbaumChain step Phi (S nx) x0 \/ LindenbaumChain step Phi (S ny) y0) as HH;
      [| destruct HH as [HH | HH]; apply Lindenbaum_spec_neg in HH; auto].
    simpl.
    unfold step at 1 3.
    assert (~ Union _ (LindenbaumChain step Phi nx) (Singleton _ x0) |-- x \/
            ~ Union _ (LindenbaumChain step Phi ny) (Singleton _ y0) |-- x) as HH;
      [| destruct HH as [HH | HH]; auto].
    apply Classical_Prop.not_and_or; intros [? ?].
    rewrite deduction_theorem in H4, H5.
    eapply derivable_weaken in H4; [| apply (Lindenbaum_spec_included _ _ nx)].
    eapply derivable_weaken in H5; [| apply (Lindenbaum_spec_included _ _ ny)].
    pose proof orp_elim_derivable (LindenbaumConstruction step Phi) x0 y0 x.
    pose proof derivable_modus_ponens _ _ _ H4 H6.
    pose proof derivable_modus_ponens _ _ _ H5 H7.
    apply (derivable_assum _ (x0 || y0)) in H1.
    pose proof derivable_modus_ponens _ _ _ H1 H8.
    auto.
Qed.

Lemma truth_lemma {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {icGamma: ReductionConsistentProofTheory IntuitionisticReduction Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {SM: Semantics L} {icSM: ReductionConsistentSemantics IntuitionisticReduction SM} {pkSM: PreKripkeSemantics L SM} {kiSM: KripkeIntuitionisticSemantics L SM}:
  forall M (X: canonical Gamma M),
   (forall m Phi v,
      X m Phi ->
      (KRIPKE: M, m |= PropositionalLanguage.varp v <-> proj1_sig Phi (PropositionalLanguage.varp v))) ->
   (forall m Phi,
      X m Phi ->
      forall x, KRIPKE: M, m |= x <-> proj1_sig Phi x).
Proof.
  intros.
  rename H into ATOM_ASSUM, H0 into H.
  revert x.
  pose proof (fun Phi: DCS Gamma => derivable_closed_element_derivable (proj1_sig Phi) (proj1 (proj2_sig Phi))).
  apply (truth_lemma_from_syntactic_reduction _ _ _ _ _ (H0 Phi)).
  intros.
  revert Phi m H.
  induction x; try solve [inversion H1]; intros.
  + destruct H1.
    specialize (IHx1 H1 Phi m H).
    specialize (IHx2 H2 Phi m H).
    pose proof DCS_andp_iff (proj1_sig Phi) (proj1 (proj2_sig Phi)) x1 x2.
    change (PropositionalLanguage.andp x1 x2) with (x1 && x2).
    rewrite sat_andp.
    tauto.
  + destruct H1.
    specialize (IHx1 H1 Phi m H).
    specialize (IHx2 H2 Phi m H).
    pose proof DCS_orp_iff (proj1_sig Phi) (proj1 (proj2_sig Phi)) (proj1 (proj2 (proj2_sig Phi))) x1 x2.
    simpl in *.
    change (PropositionalLanguage.orp x1 x2) with (x1 || x2).
    rewrite sat_orp.
    tauto.
  + destruct H1.
    specialize (IHx1 H1).
    specialize (IHx2 H2).
    split.
    - intros.
      rewrite H0.
      change (PropositionalLanguage.impp x1 x2) with (x1 --> x2) in *.
      apply deduction_theorem.
      apply Classical_Prop.NNPP; intro.
      pose proof Lindenbaum_lemma _ _ H4.
      destruct H5 as [Psi' [? [? ?]]].
      set (Psi := exist _ Psi' H7: DCS Gamma).
      change Psi' with (proj1_sig Psi) in H5, H6.
      clearbody Psi; clear Psi' H7.
      rewrite sat_impp in H3.
      assert (Included _ (proj1_sig Phi) (proj1_sig Psi)) by (hnf; intros; apply H5; left; auto).
      destruct (canonical_relation_complete _ _ X m Psi Phi H H7) as [n [? ?]].
      specialize (H3 n H9).
      rewrite IHx1, IHx2 in H3 by eauto.
      assert (proj1_sig Psi x1) by (apply H5; right; constructor).
      specialize (H3 H10).
      specialize (H0 Psi x2).
      rewrite H0 in H3; auto.
    - intros.
      change (PropositionalLanguage.impp x1 x2) with (x1 --> x2) in *.
      rewrite sat_impp; intros n ?H.
      destruct (im_surj _ _ X n) as [Psi ?].
      rewrite IHx1, IHx2 by eauto.
      intros.
      rewrite H0 in H3, H6 |- *.
      eapply canonical_relation_sound in H4; [| eauto | eauto].
      eapply derivable_weaken in H3; [| exact H4].
      eapply derivable_modus_ponens; [exact H6 | exact H3].
  + pose proof sat_falsep M m.
    split; [intros; tauto | intros].
    rewrite H0 in H3.
    pose proof proj2_sig Phi.
    destruct H4 as [_ [_ ?]].
    exfalso; apply H4; auto.
  + auto.
Qed.

End Completeness.
