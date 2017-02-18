Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.HenkinCompleteness.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Complete.Canonical_Kripke.
Require Logic.PropositionalLogic.DeepEmbedded.PropositionalLanguage.
Require Logic.PropositionalLogic.DeepEmbedded.IntuitionisticLogic.
Require Logic.PropositionalLogic.DeepEmbedded.DeMorganLogic.
Require Logic.PropositionalLogic.DeepEmbedded.GodelDummettLogic.
Require Logic.PropositionalLogic.DeepEmbedded.ClassicalLogic.
Require Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section GeneralCanonical.

Context (Var: Type).
Context (CV: Countable Var).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.
Instance MD: Model := KripkeSemantics.MD Var.
Instance kMD: KripkeModel MD := KripkeSemantics.kMD Var.
Instance R (M: Kmodel): Relation (Kworlds M):= KripkeSemantics.R Var M.
Instance po_R (M: Kmodel): PreOrder (@KI.Krelation _ (R M)):= KripkeSemantics.po_R Var M.
Instance SM: Semantics L MD := KripkeSemantics.SM Var.
Instance kiSM (M: Kmodel): KripkeIntuitionisticSemantics L MD M SM := KripkeSemantics.kiSM Var M.

Definition DCS (Gamma: ProofTheory L): Type := sig (fun Phi =>
  derivable_closed Phi /\
  orp_witnessed Phi /\
  consistent Phi).

Lemma DCS_ext {Gamma: ProofTheory L}: forall m n: DCS Gamma,
  m = n <-> (forall x: expr, proj1_sig m x <-> proj1_sig n x).
Proof.
  intros.
  split; [intros; subst; reflexivity |].
  intros.
  destruct m as [m ?H], n as [n ?H].
  simpl in H.
  assert (m = n).
  + apply Extensionality_Ensembles.
    split; unfold Included, Ensembles.In; intros; apply H; auto.
  + subst n.
    assert (H0 = H1) by apply proof_irrelevance.
    subst H1; auto.
Qed.
(*
Record canonical (Gamma: ProofTheory L) {MD: Model} {kMD: KripkeModel MD}  (M: Kmodel) {kiM: KripkeIntuitionisticModel (Kworlds M)} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}: Type := {
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
*)
Lemma Lindenbaum_lemma {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma}:
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

Definition canonical_frame {Gamma: ProofTheory L}: KripkeSemantics.frame.
  refine (KripkeSemantics.Build_frame (DCS Gamma) (fun a b => Included _ (proj1_sig a) (proj1_sig b)) _).
  constructor.
  + hnf; intros.
    hnf; intros; auto.
  + hnf; intros.
    hnf; intros; auto.
Defined.

Program Definition canonical_eval {Gamma: ProofTheory L}: Var -> KripkeSemantics.sem canonical_frame :=
  fun p a => a (PropositionalLanguage.varp p).
Next Obligation.
  hnf; intros.
  apply H; auto.
Qed.

Definition canonical_Kmodel {Gamma: ProofTheory L}: @Kmodel (KripkeSemantics.MD Var) (KripkeSemantics.kMD Var) :=
  KripkeSemantics.Build_Kmodel Var canonical_frame canonical_eval.

Definition canonical_model {Gamma: ProofTheory L} (Phi: DCS Gamma) : @model (KripkeSemantics.MD Var) :=
  KripkeSemantics.Build_model Var canonical_Kmodel Phi.

Lemma truth_lemma {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma}:
  forall Phi x,
    KRIPKE: canonical_Kmodel, Phi |= x <-> proj1_sig Phi x.
Proof.
  intros.
  change (DCS Gamma) in Phi.
  pose proof (fun Phi: DCS Gamma => derivable_closed_element_derivable (proj1_sig Phi) (proj1 (proj2_sig Phi))).
  revert Phi.
  induction x; intros.
  + specialize (IHx1 Phi).
    specialize (IHx2 Phi).
    pose proof DCS_andp_iff (proj1_sig Phi) (proj1 (proj2_sig Phi)) x1 x2.
    change (PropositionalLanguage.andp x1 x2) with (x1 && x2).
    rewrite sat_andp.
    tauto.
  + specialize (IHx1 Phi).
    specialize (IHx2 Phi).
    pose proof DCS_orp_iff (proj1_sig Phi) (proj1 (proj2_sig Phi)) (proj1 (proj2 (proj2_sig Phi))) x1 x2.
    change (PropositionalLanguage.orp x1 x2) with (x1 || x2).
    rewrite sat_orp.
    tauto.
  + split.
    - intros.
      rewrite H.
      change (PropositionalLanguage.impp x1 x2) with (x1 --> x2) in *.
      apply deduction_theorem.
      apply Classical_Prop.NNPP; intro.
      pose proof Lindenbaum_lemma _ _ H1.
      destruct H2 as [Psi' [? [? ?]]].
      set (Psi := exist _ Psi' H4: DCS Gamma).
      change Psi' with (proj1_sig Psi) in H2, H3.
      clearbody Psi; clear Psi' H4.
      rewrite sat_impp in H0.
      assert (Included _ (proj1_sig Phi) (proj1_sig Psi)) by (hnf; intros; apply H2; left; auto).
      specialize (H0 Psi H4).
      rewrite IHx1, IHx2 in H0 by eauto.
      assert (proj1_sig Psi x1) by (apply H2; right; constructor).
      specialize (H0 H5).
      specialize (H Psi x2).
      rewrite H in H0; auto.
    - intros.
      change (PropositionalLanguage.impp x1 x2) with (x1 --> x2) in *.
      rewrite sat_impp; intros Psi ?H.
      rewrite IHx1, IHx2 by eauto.
      intros.
      rewrite H in H0, H2 |- *.
      eapply deduction_weaken in H0; [| exact H1].
      eapply deduction_modus_ponens; [exact H2 | exact H0].
  + pose proof @sat_falsep _ _ _ MD kMD canonical_Kmodel _ _ _ Phi.
    split; [intros; tauto | intros].
    rewrite H in H1.
    pose proof proj2_sig Phi.
    destruct H2 as [_ [_ ?]].
    rewrite consistent_spec in H2.
    exfalso; apply H2; auto.
  + simpl.
    reflexivity.
Qed.

End GeneralCanonical.

Module Canonical_All.

Section Canonical_All.

Context (Var: Type).
Context (CV: Countable Var).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.
Instance G: ProofTheory L := IntuitionisticLogic.G Var.
Instance nG: NormalProofTheory L G := IntuitionisticLogic.nG Var.
Instance mpG: MinimunPropositionalLogic L G := IntuitionisticLogic.mpG Var.
Instance ipG: IntuitionisticPropositionalLogic L G := IntuitionisticLogic.ipG Var.
Instance MD: Model := KripkeSemantics.MD Var.
Instance kMD: KripkeModel MD := KripkeSemantics.kMD Var.
Instance R (M: Kmodel): Relation (Kworlds M):= KripkeSemantics.R Var M.
Instance po_R (M: Kmodel): PreOrder (@KI.Krelation _ (R M)):= KripkeSemantics.po_R Var M.
Instance SM: Semantics L MD := KripkeSemantics.SM Var.
Instance kiSM (M: Kmodel): KripkeIntuitionisticSemantics L MD M SM := KripkeSemantics.kiSM Var M.

Lemma truth_lemma: forall (Phi: DCS Var G) x, canonical_model Var Phi |= x <-> proj1_sig Phi x.
Proof.
  intros.
  apply (truth_lemma Var CV).
Qed.

Theorem complete_intuitionistic_kripke: strongly_complete G SM (AllModel _).
Proof.
  assert (forall Phi x, ~ Phi |-- x -> ~ consequence (AllModel _) Phi x).
  + intros.
    assert (exists Psi: DCS Var G, Included _ Phi (proj1_sig Psi) /\ ~ proj1_sig Psi |-- x).
    Focus 1. {
      apply (Lindenbaum_lemma Var CV) in H.
      destruct H as [Psi [? [? ?]]].
      exists (exist _ Psi H1).
      simpl; auto.
    } Unfocus.
    destruct H0 as [Psi [? ?]].
    intro.
    specialize (H2 (canonical_model Var Psi)).
    apply H1.
    rewrite <- derivable_closed_element_derivable by (exact (proj1 (proj2_sig Psi))).
    rewrite <- truth_lemma.
    apply H2; intros; [hnf; auto |].
    apply truth_lemma.
    apply H0; auto.
  + hnf; intros.
    apply Classical_Prop.NNPP; intro; revert H0.
    apply H; auto.
Qed.

End Canonical_All.

End Canonical_All.

Module Canonical_Identity.

Section Canonical_Identity.

Context (Var: Type).
Context (CV: Countable Var).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.
Instance G: ProofTheory L := ClassicalLogic.G Var.
Instance nG: NormalProofTheory L G := ClassicalLogic.nG Var.
Instance mpG: MinimunPropositionalLogic L G := ClassicalLogic.mpG Var.
Instance ipG: IntuitionisticPropositionalLogic L G := ClassicalLogic.ipG Var.
Instance cpG: ClassicalPropositionalLogic L G := ClassicalLogic.cpG Var.
Instance MD: Model := KripkeSemantics.MD Var.
Instance kMD: KripkeModel MD := KripkeSemantics.kMD Var.
Instance R (M: Kmodel): Relation (Kworlds M):= KripkeSemantics.R Var M.
Instance po_R (M: Kmodel): PreOrder (@KI.Krelation _ (R M)):= KripkeSemantics.po_R Var M.
Instance SM: Semantics L MD := KripkeSemantics.SM Var.
Instance kiSM (M: Kmodel): KripkeIntuitionisticSemantics L MD M SM := KripkeSemantics.kiSM Var M.

Lemma classical_canonical_ident: forall Psi: DCS Var G, KripkeModelClass (KripkeSemantics.MD Var) (KripkeSemantics.Kmodel_Identity Var)
  (canonical_model Var Psi).
Proof.
  intros.
  unfold canonical_model; constructor.
  hnf; constructor.
  intros.
  apply DCS_ext.
  intros.
  split; auto; [apply H |].
  intros.
  rewrite DCS_negp_iff in H0 by (destruct (proj2_sig n); tauto).
  assert (~ proj1_sig m (~~ x)) by (intro; apply H0, H; auto).
  rewrite DCS_negp_iff by (destruct (proj2_sig m); tauto).
  auto.
Qed.

Lemma truth_lemma: forall (Phi: DCS Var G) x, canonical_model Var Phi |= x <-> proj1_sig Phi x.
Proof.
  intros.
  apply (truth_lemma Var CV).
Qed.

Theorem complete_classical_kripke_ident: strongly_complete G SM (@KripkeModelClass (KripkeSemantics.MD Var) (KripkeSemantics.kMD Var) (KripkeSemantics.Kmodel_Identity _)).
Proof.
  assert (forall Phi x, ~ Phi |-- x -> ~ consequence (@KripkeModelClass (KripkeSemantics.MD Var) (KripkeSemantics.kMD Var) (KripkeSemantics.Kmodel_Identity _)) Phi x).
  + intros.
    assert (exists Psi: DCS Var G, Included _ Phi (proj1_sig Psi) /\ ~ proj1_sig Psi |-- x).
    Focus 1. {
      apply (Lindenbaum_lemma Var CV) in H.
      destruct H as [Psi [? [? ?]]].
      exists (exist _ Psi H1).
      simpl; auto.
    } Unfocus.
    destruct H0 as [Psi [? ?]].
    intro.
    specialize (H2 (canonical_model Var Psi)).
    apply H1.
    rewrite <- derivable_closed_element_derivable by (exact (proj1 (proj2_sig Psi))).
    rewrite <- truth_lemma.
    apply H2; [apply classical_canonical_ident |]; intros.
    apply truth_lemma.
    apply H0; auto.
  + hnf; intros.
    apply Classical_Prop.NNPP; intro; revert H0.
    apply H; auto.
Qed.

End Canonical_Identity.

End Canonical_Identity.

Module Canonical_NoBranch.

Section Canonical_NoBranch.

Context (Var: Type).
Context (CV: Countable Var).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.
Instance G: ProofTheory L := GodelDummettLogic.G Var.
Instance nG: NormalProofTheory L G := GodelDummettLogic.nG Var.
Instance mpG: MinimunPropositionalLogic L G := GodelDummettLogic.mpG Var.
Instance ipG: IntuitionisticPropositionalLogic L G := GodelDummettLogic.ipG Var.
Instance gdG: GodelDummettPropositionalLogic L G := GodelDummettLogic.gdpG Var.
Instance MD: Model := KripkeSemantics.MD Var.
Instance kMD: KripkeModel MD := KripkeSemantics.kMD Var.
Instance R (M: Kmodel): Relation (Kworlds M):= KripkeSemantics.R Var M.
Instance po_R (M: Kmodel): PreOrder (@KI.Krelation _ (R M)):= KripkeSemantics.po_R Var M.
Instance SM: Semantics L MD := KripkeSemantics.SM Var.
Instance kiSM (M: Kmodel): KripkeIntuitionisticSemantics L MD M SM := KripkeSemantics.kiSM Var M.

Lemma truth_lemma: forall (Phi: DCS Var G) x, canonical_model Var Phi |= x <-> proj1_sig Phi x.
Proof.
  intros.
  apply (truth_lemma Var CV).
Qed.

Lemma Godel_Dummett_canonical_no_branch: forall Psi: DCS Var G, KripkeModelClass (KripkeSemantics.MD Var) (KripkeSemantics.Kmodel_NoBranch Var) (canonical_model Var Psi).
Proof.
  intros.
  unfold canonical_model; constructor.
  hnf; constructor.
  intros.
  destruct (classic (Included _ (proj1_sig m2) (proj1_sig m1))); auto.
  destruct (classic (Included _ (proj1_sig m1) (proj1_sig m2))); auto.
  exfalso.
  unfold Included, Ensembles.In in H, H0, H1, H2.
  apply not_all_ex_not in H1.
  apply not_all_ex_not in H2.
  destruct H1 as [x1 ?], H2 as [x2 ?].
  pose proof GodelDummett.derivable_impp_choice (proj1_sig n) x1 x2.
  rewrite <- derivable_closed_element_derivable in H3 by (destruct (proj2_sig n); tauto).
  pose proof (proj1 (proj2 (proj2_sig n))).
  apply H4 in H3; clear H4.
  destruct H3; pose proof H3; apply H in H3; apply H0 in H4.
  + rewrite derivable_closed_element_derivable in H3 by (destruct (proj2_sig m1); tauto).
    rewrite derivable_closed_element_derivable in H4 by (destruct (proj2_sig m2); tauto).
    pose proof (fun HH => deduction_modus_ponens _ _ _ HH H3).
    pose proof (fun HH => deduction_modus_ponens _ _ _ HH H4).
    rewrite <- !derivable_closed_element_derivable in H5 by (destruct (proj2_sig m1); tauto).
    rewrite <- !derivable_closed_element_derivable in H6 by (destruct (proj2_sig m2); tauto).
    clear - H1 H2 H5 H6.
    tauto.
  + rewrite derivable_closed_element_derivable in H3 by (destruct (proj2_sig m1); tauto).
    rewrite derivable_closed_element_derivable in H4 by (destruct (proj2_sig m2); tauto).
    pose proof (fun HH => deduction_modus_ponens _ _ _ HH H3).
    pose proof (fun HH => deduction_modus_ponens _ _ _ HH H4).
    rewrite <- !derivable_closed_element_derivable in H5 by (destruct (proj2_sig m1); tauto).
    rewrite <- !derivable_closed_element_derivable in H6 by (destruct (proj2_sig m2); tauto).
    clear - H1 H2 H5 H6.
    tauto.
Qed.

Theorem complete_GodelDummett_kripke_no_branch: strongly_complete G SM (@KripkeModelClass (KripkeSemantics.MD Var) (KripkeSemantics.kMD Var) (KripkeSemantics.Kmodel_NoBranch _)).
Proof.
  assert (forall Phi x, ~ Phi |-- x -> ~ consequence (@KripkeModelClass (KripkeSemantics.MD Var) (KripkeSemantics.kMD Var) (KripkeSemantics.Kmodel_NoBranch _)) Phi x).
  + intros.
    assert (exists Psi: DCS Var G, Included _ Phi (proj1_sig Psi) /\ ~ proj1_sig Psi |-- x).
    Focus 1. {
      apply (Lindenbaum_lemma Var CV) in H.
      destruct H as [Psi [? [? ?]]].
      exists (exist _ Psi H1).
      simpl; auto.
    } Unfocus.
    destruct H0 as [Psi [? ?]].
    intro.
    specialize (H2 (canonical_model Var Psi)).
    apply H1.
    rewrite <- derivable_closed_element_derivable by (exact (proj1 (proj2_sig Psi))).
    rewrite <- truth_lemma.
    apply H2; [apply Godel_Dummett_canonical_no_branch |]; intros.
    apply truth_lemma.
    apply H0; auto.
  + hnf; intros.
    apply Classical_Prop.NNPP; intro; revert H0.
    apply H; auto.
Qed.

End Canonical_NoBranch.

End Canonical_NoBranch.

Module Canonical_BranchJoin.

Section Canonical_BranchJoin.

Context (Var: Type).
Context (CV: Countable Var).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.
Instance G: ProofTheory L := DeMorganLogic.G Var.
Instance nG: NormalProofTheory L G := DeMorganLogic.nG Var.
Instance mpG: MinimunPropositionalLogic L G := DeMorganLogic.mpG Var.
Instance ipG: IntuitionisticPropositionalLogic L G := DeMorganLogic.ipG Var.
Instance dmpG: DeMorganPropositionalLogic L G := DeMorganLogic.dmpG Var.
Instance MD: Model := KripkeSemantics.MD Var.
Instance kMD: KripkeModel MD := KripkeSemantics.kMD Var.
Instance R (M: Kmodel): Relation (Kworlds M):= KripkeSemantics.R Var M.
Instance po_R (M: Kmodel): PreOrder (@KI.Krelation _ (R M)):= KripkeSemantics.po_R Var M.
Instance SM: Semantics L MD := KripkeSemantics.SM Var.
Instance kiSM (M: Kmodel): KripkeIntuitionisticSemantics L MD M SM := KripkeSemantics.kiSM Var M.

Lemma truth_lemma: forall (Phi: DCS Var G) x, canonical_model Var Phi |= x <-> proj1_sig Phi x.
Proof.
  intros.
  apply (truth_lemma Var CV).
Qed.

Lemma weak_classical_canonical_branch_join: forall Psi: DCS Var G, KripkeModelClass (KripkeSemantics.MD Var) (KripkeSemantics.Kmodel_BranchJoin Var) (canonical_model Var Psi).
Proof.
  intros.
  unfold canonical_model; constructor.
  hnf; constructor.
  intros.
  change (DCS Var G) in m1, m2, n.
  destruct (proj2_sig m1) as [? [_ ?]].
  destruct (proj2_sig m2) as [? [_ ?]].
  destruct (proj2_sig n) as [? [? ?]].
  assert (~ (Union _ (proj1_sig m1) (proj1_sig m2)) |-- FF).
  Focus 1. {
    intro.
    apply derivable_closed_union_derivable in H8; [| auto].
    destruct H8 as [x [? ?]].
    rewrite derivable_closed_element_derivable in H8 by auto.
    pose proof DeMorgan.derivable_weak_excluded_middle (proj1_sig n) x.
    rewrite <- derivable_closed_element_derivable in H10 by auto.
    apply (H6 (~~ x)) in H10.
    destruct H10.
    + apply H0 in H10; unfold Ensembles.In in H10.
      rewrite derivable_closed_element_derivable in H10 by auto.
      pose proof deduction_modus_ponens _ _ _ H8 H10.
      rewrite consistent_spec in H4; auto.
    + apply H in H10; unfold Ensembles.In in H10.
      rewrite derivable_closed_element_derivable in H10 by auto.
      pose proof deduction_modus_ponens _ _ _ H9 H10.
      rewrite consistent_spec in H2; auto.
  } Unfocus.
  destruct (Lindenbaum_lemma _ CV  _ _ H8) as [m' [? [_ ?]]].
  set (m := exist _ m' H10: DCS Var G).
  change m' with (proj1_sig m) in H9.
  clearbody m; clear m' H10.
  exists m.
  split.
  + intros ? ?; apply H9; left; auto.
  + intros ? ?; apply H9; right; auto.
Qed.

Theorem complete_weak_classical_kripke_branch_join: strongly_complete G SM (@KripkeModelClass (KripkeSemantics.MD Var) (KripkeSemantics.kMD Var) (KripkeSemantics.Kmodel_BranchJoin _)).
Proof.
  assert (forall Phi x, ~ Phi |-- x -> ~ consequence (@KripkeModelClass (KripkeSemantics.MD Var) (KripkeSemantics.kMD Var) (KripkeSemantics.Kmodel_BranchJoin _)) Phi x).
  + intros.
    assert (exists Psi: DCS Var G, Included _ Phi (proj1_sig Psi) /\ ~ proj1_sig Psi |-- x).
    Focus 1. {
      apply (Lindenbaum_lemma Var CV) in H.
      destruct H as [Psi [? [? ?]]].
      exists (exist _ Psi H1).
      simpl; auto.
    } Unfocus.
    destruct H0 as [Psi [? ?]].
    intro.
    specialize (H2 (canonical_model Var Psi)).
    apply H1.
    rewrite <- derivable_closed_element_derivable by (exact (proj1 (proj2_sig Psi))).
    rewrite <- truth_lemma.
    apply H2; [apply weak_classical_canonical_branch_join |]; intros.
    apply truth_lemma.
    apply H0; auto.
  + hnf; intros.
    apply Classical_Prop.NNPP; intro; revert H0.
    apply H; auto.
Qed.

End Canonical_BranchJoin.

End Canonical_BranchJoin.
