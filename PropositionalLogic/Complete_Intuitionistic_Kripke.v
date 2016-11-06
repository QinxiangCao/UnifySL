Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.
Require Import Logic.HenkinCompleteness.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.MinimunPropositionalLogic.
Require Import Logic.PropositionalLogic.IntuitionisticPropositionalLogic.
Require Import Logic.PropositionalLogic.KripkeSemantics.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Definition DCS (Var: Type): Type := sig (fun Phi =>
  @derivable_closed _ _ (IntuitionisticPropositionalLogic.G Var) Phi /\
  @orp_witnessed _ _ _ (IntuitionisticPropositionalLogic.G Var) Phi /\
  consistent (IntuitionisticPropositionalLogic.G Var) Phi).

Definition canonical_frame (Var: Type): KripkeSemantics.frame.
  refine (KripkeSemantics.Build_frame (DCS Var) (fun a b => Included _ (proj1_sig b) (proj1_sig a)) _).
  constructor.
  + hnf; intros.
    hnf; intros; auto.
  + hnf; intros.
    hnf; intros; auto.
Defined.

Program Definition canonical_eval (Var: Type): Var -> KripkeSemantics.sem (canonical_frame Var) :=
  fun p a => a (PropositionalLanguage.varp p).
Next Obligation.
  apply H; auto.
Qed.

Definition canonical_model {Var: Type} (Phi: DCS Var): @model _ (KripkeSemantics.SM Var) :=
  KripkeSemantics.Build_model Var (canonical_frame Var) (canonical_eval Var) Phi.

Lemma Lindenbaum_lemma {Var: Type}: Countable Var ->
  forall Phi x,
    ~ @derivable _ (IntuitionisticPropositionalLogic.G Var) Phi x ->
    exists Psi,
      Included _ Phi Psi /\
      ~ @derivable _ (IntuitionisticPropositionalLogic.G Var) Psi x /\
      @derivable_closed _ _ (IntuitionisticPropositionalLogic.G Var) Psi /\
      @orp_witnessed _ _ _ (IntuitionisticPropositionalLogic.G Var) Psi /\
      consistent (IntuitionisticPropositionalLogic.G Var) Psi.
Proof.
  intros.
  apply PropositionalLanguage.formula_countable in X.
  set (step :=
          fun n Phi x0 =>
             Phi x0 \/
            (inj_R _ _ X x0 n /\
             ~ @derivable _ (IntuitionisticPropositionalLogic.G Var) (Union _ Phi (Singleton _ x0)) x)).
  exists (LindenbaumConstruction step Phi).
  assert (Included expr Phi (LindenbaumConstruction step Phi) /\
          ~ @derivable _ (IntuitionisticPropositionalLogic.G Var) (LindenbaumConstruction step Phi) x /\
          (~ @derivable _ (IntuitionisticPropositionalLogic.G Var) (LindenbaumConstruction step Phi) x ->
           @derivable_closed _ _ (IntuitionisticPropositionalLogic.G Var) (LindenbaumConstruction step Phi)) /\
          (~ @derivable _ (IntuitionisticPropositionalLogic.G Var) (LindenbaumConstruction step Phi) x ->
           @orp_witnessed _ _ _ (IntuitionisticPropositionalLogic.G Var) (LindenbaumConstruction step Phi))).
  Focus 2. {
    destruct H0 as [? [? [? ?]]].
    split; [| split; [| split; [| split]]]; auto.
    intro; apply H1.
    pose proof @falsep_elim_derivable _ _ _ _ _ _ (IntuitionisticPropositionalLogic.ipG Var) (LindenbaumConstruction step Phi) x.
    eapply (@derivable_modus_ponens _ _ _ _ _ (IntuitionisticPropositionalLogic.mpG Var) (LindenbaumConstruction step Phi)); [exact H4 | exact H5].
  } Unfocus.
  split; [| split; [| split]].
  + apply (Lindenbaum_spec_included _ _ 0).
  + apply (Lindenbaum_spec_pos _ _
            (fun xs => @provable _ (IntuitionisticPropositionalLogic.G Var) (multi_imp xs x))
            (fun Phi => @derivable _ (IntuitionisticPropositionalLogic.G Var) Phi x)).
    - intros; apply derivable_provable.
    - intros ? ? ? ?; left; auto.
    - apply H.
    - intros.
      destruct (Classical_Prop.classic (exists x0, inj_R _ _ X x0 n /\ ~ @derivable _ (IntuitionisticPropositionalLogic.G Var) (Union _ S (Singleton _ x0)) x)) as [[x0 [? ?]] |].
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
    rewrite (@deduction_theorem _ _ _ _ _ (IntuitionisticPropositionalLogic.mpG Var)) in H3.
    eapply derivable_weaken in H3; [| apply (Lindenbaum_spec_included _ _ n)].
    pose proof @derivable_modus_ponens _ _ _ _ _ (IntuitionisticPropositionalLogic.mpG Var) _ _ _ H1 H3.
    auto.
  + intros; hnf; intros x0 y0 ?.
    destruct (im_inj _ _ X x0) as [nx ?].
    destruct (im_inj _ _ X y0) as [ny ?].
    assert (LindenbaumChain step Phi (S nx) x0 \/ LindenbaumChain step Phi (S ny) y0) as HH;
      [| destruct HH as [HH | HH]; apply Lindenbaum_spec_neg in HH; auto].
    simpl.
    unfold step at 1 3.
    assert (~ @derivable _ (IntuitionisticPropositionalLogic.G Var) (Union _ (LindenbaumChain step Phi nx) (Singleton _ x0)) x \/ ~ @derivable _ (IntuitionisticPropositionalLogic.G Var) (Union _ (LindenbaumChain step Phi ny) (Singleton _ y0)) x) as HH;
      [| destruct HH as [HH | HH]; auto].
    apply Classical_Prop.not_and_or; intros [? ?].
    rewrite (@deduction_theorem _ _ _ _ _ (IntuitionisticPropositionalLogic.mpG Var)) in H4, H5.
    eapply derivable_weaken in H4; [| apply (Lindenbaum_spec_included _ _ nx)].
    eapply derivable_weaken in H5; [| apply (Lindenbaum_spec_included _ _ ny)].
    pose proof @orp_elim_derivable _ _ _ _ _ _ (IntuitionisticPropositionalLogic.ipG Var) (LindenbaumConstruction step Phi) x0 y0 x.
    pose proof @derivable_modus_ponens _ _ _ _ _ (IntuitionisticPropositionalLogic.mpG Var) _ _ _ H4 H6.
    pose proof @derivable_modus_ponens _ _ _ _ _ (IntuitionisticPropositionalLogic.mpG Var) _ _ _ H5 H7.
    apply (@derivable_assum _ _ _ _ _ (IntuitionisticPropositionalLogic.mpG Var) _ (x0 || y0)) in H1.
    pose proof @derivable_modus_ponens _ _ _ _ _ (IntuitionisticPropositionalLogic.mpG Var) _ _ _ H1 H8.
    auto.
Qed.

Lemma truth_lemma {Var: Type} {CV: Countable Var}: forall (Phi: DCS Var) x, canonical_model Phi |= x <-> proj1_sig Phi x.
Proof.
  intros.
  revert x.
  pose proof (fun Phi: DCS Var => @derivable_closed_element_derivable _ _ _ _ _ (IntuitionisticPropositionalLogic.mpG Var) (proj1_sig Phi) (proj1 (proj2_sig Phi))).
  pose proof @KripkeSemantics.intuitionistic_consistent Var.
  pose proof @intuitionistic_reduction_consistent _ _ _ _  _ _ (IntuitionisticPropositionalLogic.ipG Var).
  apply (@truth_lemma_from_syntactic_reduction  _ _ (PropositionalLanguage.nIntuitionisticReduction) _ _ H1 H0 _ _ (H Phi)).
  intros.
  clear H0 H1.
  revert Phi.
  induction x; try solve [inversion H2]; intros.
  + destruct H2.
    specialize (IHx1 H0 Phi).
    specialize (IHx2 H1 Phi).
    pose proof @DCS_andp_iff _ _ _ _ _ _ (IntuitionisticPropositionalLogic.ipG Var) (proj1_sig Phi) (proj1 (proj2_sig Phi)) x1 x2.
    simpl in *.
    unfold KripkeSemantics.sem_and.
    tauto.
  + destruct H2.
    specialize (IHx1 H0 Phi).
    specialize (IHx2 H1 Phi).
    pose proof @DCS_orp_iff _ _ _ _ _ _ (IntuitionisticPropositionalLogic.ipG Var) (proj1_sig Phi) (proj1 (proj2_sig Phi)) (proj1 (proj2 (proj2_sig Phi))) x1 x2.
    simpl in *.
    unfold KripkeSemantics.sem_or.
    tauto.
  + destruct H2.
    specialize (IHx1 H0).
    specialize (IHx2 H1).
    split.
    - intros.
      rewrite H.
      apply (@deduction_theorem _ _ _ _ _ (IntuitionisticPropositionalLogic.mpG Var)).
      apply Classical_Prop.NNPP; intro.
      pose proof Lindenbaum_lemma CV _ _ H3.
      destruct H4 as [Psi [? [? ?]]].
      hnf in H2.
      specialize (H2 (exist _ Psi H6)).
      assert (Included _ (proj1_sig Phi) Psi) by (hnf; intros; apply H4; left; auto).
      specialize (H2 H7).
      simpl in IHx1, IHx2.
      change (KripkeSemantics.model_frame (canonical_model Phi)) with (canonical_frame Var) in H2.
      change (KripkeSemantics.model_var (canonical_model Phi)) with (canonical_eval Var) in H2.
      rewrite IHx1, IHx2 in H2; simpl in H2.
      assert (Psi x1) by (apply H4; right; constructor).
      specialize (H2 H8).
      specialize (H (exist _ Psi H6) x2); simpl in H.
      rewrite H in H2; auto.
    - intros.
      hnf; intros Psi ?H.
      change (DCS Var) in Psi.
      simpl in H3.
      change (KripkeSemantics.model_frame (canonical_model Phi)) with (canonical_frame Var).
      change (KripkeSemantics.model_var (canonical_model Phi)) with (canonical_eval Var).
      simpl in IHx1, IHx2.
      rewrite IHx1, IHx2.
      intros.
      rewrite H in H2, H4 |- *.
      eapply derivable_weaken in H2; [| exact H3].
      exact (@derivable_modus_ponens _ _ _ _ _ (IntuitionisticPropositionalLogic.mpG Var) _ _ _ H4 H2).
  + simpl.
    split; [intros [] | intros].
    rewrite H in H0.
    pose proof proj2_sig Phi.
    destruct H1 as [_ [_ ?]].
    apply H1; auto.
  + simpl.
    unfold canonical_model.
    tauto.
Qed.

Theorem complete_intuitionistic_kripke (Var: Type) (CV: Countable Var): strongly_complete (IntuitionisticPropositionalLogic.G Var) (KripkeSemantics.SM Var).
Abort.
(*
Proof.
  assert (forall Phi x, consistent (ClassicalPropositionalLogic.G Var) Phi -> satisfiable Phi).
  + intros.
    assert (exists Psi, Included _ Phi Psi /\ maximal_consistent (ClassicalPropositionalLogic.G Var) Psi)
      by (apply Lindenbaum_lemma; auto).
    destruct H0 as [Psi [? ?]].
    exists (canonical_model (exist _ Psi H1)).
    intros.
    apply truth_lemma.
    simpl.
    apply H0; auto.
  + hnf; intros.
    specialize (H (Union _ Phi (Singleton _ (~~ x)))).
    unfold consistent in H.
    apply Classical_Prop.NNPP.
    intro.
    assert (satisfiable (Union expr Phi (Singleton expr (~~ x)))).
    Focus 1. {
      apply H.
      intro; apply H1.
      rewrite (@deduction_theorem _ _ _ _ _ (ClassicalPropositionalLogic.mpG Var)) in H2.
      clear - H2.
      apply (@aux_classic_theorem05 _ _ _ _ _ _ (ClassicalPropositionalLogic.cpG Var)); auto.
    } Unfocus.
    destruct H2 as [m ?].
    specialize (H0 m).
    pose proof (H2 (~~ x) (Union_intror _ _ _ _ (In_singleton _ _))).
    pose proof (fun x H => H2 x (Union_introl _ _ _ _ H)).
    specialize (H0 H4).
    clear - H0 H3.
    simpl in *; auto.
Qed.

*)