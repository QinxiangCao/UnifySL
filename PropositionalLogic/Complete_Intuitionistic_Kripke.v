Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
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
Instance G: ProofTheory L := IntuitionisticPropositionalLogic.G Var.
Instance nG: NormalProofTheory L G := IntuitionisticPropositionalLogic.nG Var.
Instance mpG: MinimunPropositionalLogic L G := IntuitionisticPropositionalLogic.mpG Var.
Instance ipG: IntuitionisticPropositionalLogic L G := IntuitionisticPropositionalLogic.ipG Var.
Instance MD: Model := KripkeSemantics_All.MD Var.
Instance kMD: KripkeModel MD := KripkeSemantics_All.kMD Var.
Instance kiM (M: Kmodel): KripkeIntuitionisticModel MD M:= KripkeSemantics_All.kiM Var M.
Instance SM: Semantics L MD := KripkeSemantics_All.SM Var.
Instance kiSM (M: Kmodel): KripkeIntuitionisticSemantics L MD M SM := KripkeSemantics_All.kiSM Var M.

Definition DCS: Type := sig (fun Phi =>
  derivable_closed Phi /\
  orp_witnessed Phi /\
  consistent Phi).

Definition canonical_frame: KripkeSemantics.frame.
  refine (KripkeSemantics.Build_frame DCS (fun a b => Included _ (proj1_sig b) (proj1_sig a)) _).
  constructor.
  + hnf; intros.
    hnf; intros; auto.
  + hnf; intros.
    hnf; intros; auto.
Defined.

Program Definition canonical_eval: Var -> KripkeSemantics.sem canonical_frame :=
  fun p a => a (PropositionalLanguage.varp p).
Next Obligation.
  apply H; auto.
Qed.

Definition canonical_Kmodel: KripkeSemantics_All.Kmodel Var :=
  KripkeSemantics_All.Build_Kmodel Var canonical_frame canonical_eval.

Definition canonical_model (Phi: DCS): model :=
  KripkeSemantics_All.Build_model Var canonical_Kmodel Phi.

Lemma Lindenbaum_lemma:
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
    rewrite consistent_spec.
    intro; apply H1.
    pose proof deduction_falsep_elim _ x H4.
    auto.
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
        eapply deduction_weaken; [| exact H3].
        hnf; intros ? [? | [? ?]]; [left; auto |].
        pose proof in_inj _ _ X _ _ _ H1 H2.
        subst; right; constructor.
      * intro; apply H0; clear H0.
        eapply deduction_weaken; [| exact H2].
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
    eapply deduction_weaken in H3; [| apply (Lindenbaum_spec_included _ _ n)].
    pose proof deduction_modus_ponens _ _ _ H1 H3.
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
    eapply deduction_weaken in H4; [| apply (Lindenbaum_spec_included _ _ nx)].
    eapply deduction_weaken in H5; [| apply (Lindenbaum_spec_included _ _ ny)].
    pose proof deduction_orp_elim (LindenbaumConstruction step Phi) x0 y0 x H4 H5.
    apply (derivable_assum _ (x0 || y0)) in H1.
    pose proof deduction_modus_ponens _ _ _ H1 H6.
    auto.
Qed.

Lemma truth_lemma: forall (Phi: DCS) x, canonical_model Phi |= x <-> proj1_sig Phi x.
Proof.
  intros.
  pose proof (fun Phi: DCS => derivable_closed_element_derivable (proj1_sig Phi) (proj1 (proj2_sig Phi))).
  revert Phi.
  induction x; try solve [inversion H0]; intros.
  + specialize (IHx1 Phi).
    specialize (IHx2 Phi).
    pose proof DCS_andp_iff (proj1_sig Phi) (proj1 (proj2_sig Phi)) x1 x2.
    simpl in *.
    unfold KripkeSemantics.sem_and.
    tauto.
  + specialize (IHx1 Phi).
    specialize (IHx2 Phi).
    pose proof DCS_orp_iff (proj1_sig Phi) (proj1 (proj2_sig Phi)) (proj1 (proj2 (proj2_sig Phi))) x1 x2.
    simpl in *.
    unfold KripkeSemantics.sem_or.
    tauto.
  + split.
    - intros.
      rewrite H.
      apply (@deduction_theorem _ _ _ _ (IntuitionisticPropositionalLogic.mpG Var)).
      apply Classical_Prop.NNPP; intro.
      pose proof Lindenbaum_lemma _ _ H1.
      destruct H2 as [Psi [? [? ?]]].
      hnf in H0.
      specialize (H0 (exist _ Psi H4)).
      assert (Included _ (proj1_sig Phi) Psi) by (hnf; intros; apply H2; left; auto).
      specialize (H0 H5).
      simpl in IHx1, IHx2.
      simpl in H0.
      rewrite IHx1, IHx2 in H0; simpl in H0.
      assert (Psi x1) by (apply H2; right; constructor).
      specialize (H0 H6).
      specialize (H (exist _ Psi H4) x2); simpl in H.
      rewrite H in H0; auto.
    - intros.
      hnf; intros Psi ?H.
      change DCS in Psi.
      simpl in H1.
      simpl in IHx1, IHx2.
      rewrite IHx1, IHx2.
      intros.
      rewrite H in H0, H2 |- *.
      eapply deduction_weaken in H0; [| exact H1].
      eapply deduction_modus_ponens; [exact H2 | exact H0].
  + simpl.
    split; [intros [] | intros].
    rewrite H in H0.
    pose proof proj2_sig Phi.
    destruct H1 as [_ [_ ?]].
    rewrite consistent_spec in H1; apply H1; auto.
  + simpl.
    unfold canonical_model.
    tauto.
Qed.

Theorem complete_intuitionistic_kripke: strongly_complete G SM.
Proof.
  assert (forall Phi x, ~ Phi |-- x -> ~ Phi |== x).
  + intros.
    assert (exists Psi: DCS, Included _ Phi (proj1_sig Psi) /\ ~ proj1_sig Psi |-- x).
    Focus 1. {
      apply Lindenbaum_lemma in H.
      destruct H as [Psi [? [? ?]]].
      exists (exist _ Psi H1).
      simpl; auto.
    } Unfocus.
    destruct H0 as [Psi [? ?]].
    intro.
    specialize (H2 (canonical_model Psi)).
    apply H1.
    rewrite <- derivable_closed_element_derivable by (exact (proj1 (proj2_sig Psi))).
    apply truth_lemma.
    apply H2; intros.
    apply truth_lemma.
    apply H0; auto.
  + hnf; intros.
    apply Classical_Prop.NNPP; intro; revert H0.
    apply H; auto.
Qed.

End Completeness.
