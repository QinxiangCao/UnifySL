Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.MinimunLogic.ContextProperty.
Require Import Logic.MinimunLogic.HenkinCompleteness.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.IntuitionisticPropositionalLogic.
Require Import Logic.PropositionalLogic.GodelDummettLogic.
Require Import Logic.PropositionalLogic.ClassicalPropositionalLogic.
Require Import Logic.PropositionalLogic.KripkeSemantics.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Section GeneralCanonical.

Context (Var: Type).
Context (CV: Countable Var).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.

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

Record canonical (Gamma: ProofTheory L) {MD: Model} {kMD: KripkeModel MD}  (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}: Type := {
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

Lemma truth_lemma {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {MD: Model} {kMD: KripkeModel MD} (M: Kmodel) {kiM: KripkeIntuitionisticModel MD M} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD M SM}:
  forall (X: canonical Gamma M),
   (forall m Phi v,
      X m Phi ->
      (KRIPKE: M, m |= PropositionalLanguage.varp v <-> proj1_sig Phi (PropositionalLanguage.varp v))) ->
   (forall m Phi,
      X m Phi ->
      forall x, KRIPKE: M, m |= x <-> proj1_sig Phi x).
Proof.
  intros.
  rename H into ATOM_ASSUM, H0 into H.
  pose proof (fun Phi: DCS Gamma => derivable_closed_element_derivable (proj1_sig Phi) (proj1 (proj2_sig Phi))).
  revert Phi m H.
  induction x; try solve [inversion H1]; intros.
  + specialize (IHx1 Phi m H).
    specialize (IHx2 Phi m H).
    pose proof DCS_andp_iff (proj1_sig Phi) (proj1 (proj2_sig Phi)) x1 x2.
    change (PropositionalLanguage.andp x1 x2) with (x1 && x2).
    rewrite sat_andp.
    tauto.
  + specialize (IHx1 Phi m H).
    specialize (IHx2 Phi m H).
    pose proof DCS_orp_iff (proj1_sig Phi) (proj1 (proj2_sig Phi)) (proj1 (proj2 (proj2_sig Phi))) x1 x2.
    simpl in *.
    change (PropositionalLanguage.orp x1 x2) with (x1 || x2).
    rewrite sat_orp.
    tauto.
  + split.
    - intros.
      rewrite H0.
      change (PropositionalLanguage.impp x1 x2) with (x1 --> x2) in *.
      apply deduction_theorem.
      apply Classical_Prop.NNPP; intro.
      pose proof Lindenbaum_lemma _ _ H2.
      destruct H3 as [Psi' [? [? ?]]].
      set (Psi := exist _ Psi' H5: DCS Gamma).
      change Psi' with (proj1_sig Psi) in H3, H4.
      clearbody Psi; clear Psi' H5.
      rewrite sat_impp in H1.
      assert (Included _ (proj1_sig Phi) (proj1_sig Psi)) by (hnf; intros; apply H3; left; auto).
      destruct (canonical_relation_complete _ _ X m Psi Phi H H5) as [n [? ?]].
      specialize (H1 n H7).
      rewrite IHx1, IHx2 in H1 by eauto.
      assert (proj1_sig Psi x1) by (apply H3; right; constructor).
      specialize (H1 H8).
      specialize (H0 Psi x2).
      rewrite H0 in H1; auto.
    - intros.
      change (PropositionalLanguage.impp x1 x2) with (x1 --> x2) in *.
      rewrite sat_impp; intros n ?H.
      destruct (im_surj _ _ X n) as [Psi ?].
      rewrite IHx1, IHx2 by eauto.
      intros.
      rewrite H0 in H1, H4 |- *.
      eapply canonical_relation_sound in H2; [| eauto | eauto].
      eapply deduction_weaken in H1; [| exact H2].
      eapply deduction_modus_ponens; [exact H4 | exact H1].
  + pose proof sat_falsep m.
    split; [intros; tauto | intros].
    rewrite H0 in H2.
    pose proof proj2_sig Phi.
    destruct H3 as [_ [_ ?]].
    rewrite consistent_spec in H3.
    exfalso; apply H3; auto.
  + auto.
Qed.

End GeneralCanonical.

Module Canonical_All.

Section Canonical_All.

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

Definition canonical_frame: KripkeSemantics.frame.
  refine (KripkeSemantics.Build_frame (DCS Var G) (fun a b => Included _ (proj1_sig b) (proj1_sig a)) _).
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

Definition canonical_model (Phi: DCS Var G): model :=
  KripkeSemantics_All.Build_model Var canonical_Kmodel Phi.

Definition canonical_Kmodel_surjection: surjection (Kworlds  canonical_Kmodel) (DCS Var G).
Proof.
  apply (FBuild_surjection _ _ id).
  hnf; intros.
  exists b; auto.
Defined.

Lemma canonical_model_canonical: canonical Var G canonical_Kmodel.
Proof.
  intros.
  apply (Build_canonical _ _ _ _ _ _ _ _ canonical_Kmodel_surjection).
  + intros.
    change (DCS Var G) in m, n.
    change (m = m') in H.
    change (n = n') in H0.
    subst n' m'.
    auto.
  + intros.
    change (DCS Var G) in n, m'.
    change (n = n') in H.
    subst n.
    exists m'.
    split; auto.
    change (m' = m').
    auto.
Defined.

Lemma truth_lemma: forall (Phi: DCS Var G) x, canonical_model Phi |= x <-> proj1_sig Phi x.
Proof.
  intros.
  apply (truth_lemma Var CV _ canonical_model_canonical).
  + intros.
    hnf in H; unfold id in H; subst Phi0.
    reflexivity.
  + reflexivity.
Qed.

Theorem complete_intuitionistic_kripke: strongly_complete G SM.
Proof.
  assert (forall Phi x, ~ Phi |-- x -> ~ Phi |== x).
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
    specialize (H2 (canonical_model Psi)).
    apply H1.
    rewrite <- derivable_closed_element_derivable by (exact (proj1 (proj2_sig Psi))).
    rewrite <- truth_lemma.
    apply H2; intros.
    apply truth_lemma.
    apply H0; auto.
  + hnf; intros.
    apply Classical_Prop.NNPP; intro; revert H0.
    apply H; auto.
Qed.

End Canonical_All.

End Canonical_All.

Module Canonical_Identical.

Section Canonical_Identical.

Context (Var: Type).
Context (CV: Countable Var).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.
Instance G: ProofTheory L := ClassicalPropositionalLogic.G Var.
Instance nG: NormalProofTheory L G := ClassicalPropositionalLogic.nG Var.
Instance mpG: MinimunPropositionalLogic L G := ClassicalPropositionalLogic.mpG Var.
Instance ipG: IntuitionisticPropositionalLogic L G := ClassicalPropositionalLogic.ipG Var.
Instance cpG: ClassicalPropositionalLogic L G := ClassicalPropositionalLogic.cpG Var.
Instance MD: Model := KripkeSemantics_Identical.MD Var.
Instance kMD: KripkeModel MD := KripkeSemantics_Identical.kMD Var.
Instance kiM (M: Kmodel): KripkeIntuitionisticModel MD M := KripkeSemantics_Identical.kiM Var M.
Instance ikiM (M: Kmodel): IdenticalKripkeIntuitionisticModel MD M := KripkeSemantics_Identical.ikiM Var M.
Instance SM: Semantics L MD := KripkeSemantics_Identical.SM Var.
Instance kiSM (M: Kmodel): KripkeIntuitionisticSemantics L MD M SM := KripkeSemantics_Identical.kiSM Var M.

Definition canonical_frame: KripkeSemantics.frame.
  refine (KripkeSemantics.Build_frame (DCS Var G) (fun a b => Included _ (proj1_sig b) (proj1_sig a)) _).
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

Program Definition canonical_Kmodel: @KripkeSemantics_Identical.Kmodel Var :=
  KripkeSemantics_Identical.Build_Kmodel Var canonical_frame canonical_eval _.
Next Obligation.
  apply DCS_ext.
  intros.
  split; auto; [| apply H].
  intros.
  rewrite DCS_negp_iff in H0 by (destruct (proj2_sig m); tauto).
  assert (~ proj1_sig n (~~ x)) by (intro; apply H0, H; auto).
  rewrite DCS_negp_iff by (destruct (proj2_sig n); tauto).
  auto.
Qed.

Definition canonical_model (Phi: DCS Var G): model :=
  KripkeSemantics_Identical.Build_model Var canonical_Kmodel Phi.

Definition canonical_Kmodel_surjection: surjection (Kworlds canonical_Kmodel) (DCS Var G).
Proof.
  apply (FBuild_surjection _ _ id).
  hnf; intros.
  exists b; auto.
Defined.

Lemma canonical_model_canonical: canonical Var G canonical_Kmodel.
Proof.
  intros.
  apply (Build_canonical _ _ _ _ _ _ _ _ canonical_Kmodel_surjection).
  + intros.
    change (DCS Var G) in m, n.
    change (m = m') in H.
    change (n = n') in H0.
    subst n' m'.
    auto.
  + intros.
    change (DCS Var G) in n, m'.
    change (n = n') in H.
    subst n.
    exists m'.
    split; auto.
    change (m' = m').
    auto.
Defined.

Lemma truth_lemma: forall (Phi: DCS Var G) x, canonical_model Phi |= x <-> proj1_sig Phi x.
Proof.
  intros.
  apply (truth_lemma Var CV _ canonical_model_canonical).
  + intros.
    hnf in H; unfold id in H; subst Phi0.
    reflexivity.
  + reflexivity.
Qed.

Theorem complete_intuitionistic_kripke: strongly_complete G SM.
Proof.
  assert (forall Phi x, ~ Phi |-- x -> ~ Phi |== x).
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
    specialize (H2 (canonical_model Psi)).
    apply H1.
    rewrite <- derivable_closed_element_derivable by (exact (proj1 (proj2_sig Psi))).
    rewrite <- truth_lemma.
    apply H2; intros.
    apply truth_lemma.
    apply H0; auto.
  + hnf; intros.
    apply Classical_Prop.NNPP; intro; revert H0.
    apply H; auto.
Qed.

End Canonical_Identical.

End Canonical_Identical.

Module Canonical_NoBranch.

Section Canonical_NoBranch.

Context (Var: Type).
Context (CV: Countable Var).

Instance L: Language := PropositionalLanguage.L Var.
Instance nL: NormalLanguage L := PropositionalLanguage.nL Var.
Instance pL: PropositionalLanguage L := PropositionalLanguage.pL Var.
Instance G: ProofTheory L := GodelDummettPropositionalLogic.G Var.
Instance nG: NormalProofTheory L G := GodelDummettPropositionalLogic.nG Var.
Instance mpG: MinimunPropositionalLogic L G := GodelDummettPropositionalLogic.mpG Var.
Instance ipG: IntuitionisticPropositionalLogic L G := GodelDummettPropositionalLogic.ipG Var.
Instance wpG: GodelDummettPropositionalLogic L G := GodelDummettPropositionalLogic.wpG Var.
Instance MD: Model := KripkeSemantics_NoBranch.MD Var.
Instance kMD: KripkeModel MD := KripkeSemantics_NoBranch.kMD Var.
Instance kiM (M: Kmodel): KripkeIntuitionisticModel MD M:= KripkeSemantics_NoBranch.kiM Var M.
Instance nkiM (M: Kmodel): NoBranchKripkeIntuitionisticModel MD M:= KripkeSemantics_NoBranch.nkiM Var M.
Instance SM: Semantics L MD := KripkeSemantics_NoBranch.SM Var.
Instance kiSM (M: Kmodel): KripkeIntuitionisticSemantics L MD M SM := KripkeSemantics_NoBranch.kiSM Var M.

Definition canonical_frame: KripkeSemantics.frame.
  refine (KripkeSemantics.Build_frame (DCS Var G) (fun a b => Included _ (proj1_sig b) (proj1_sig a)) _).
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

Program Definition canonical_Kmodel: @KripkeSemantics_NoBranch.Kmodel Var :=
  KripkeSemantics_NoBranch.Build_Kmodel Var canonical_frame canonical_eval _.
Next Obligation.
  destruct (classic (Included _ (proj1_sig m2) (proj1_sig m1))); auto.
  destruct (classic (Included _ (proj1_sig m1) (proj1_sig m2))); auto.
  exfalso.
  unfold Included, Ensembles.In in H, H0, H1, H2.
  apply not_all_ex_not in H1.
  apply not_all_ex_not in H2.
  destruct H1 as [x1 ?], H2 as [x2 ?].
  pose proof derivable_impp_choice (proj1_sig n) x1 x2.
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

Definition canonical_model (Phi: DCS Var G): model :=
  KripkeSemantics_NoBranch.Build_model Var canonical_Kmodel Phi.

Definition canonical_Kmodel_surjection: surjection (Kworlds canonical_Kmodel) (DCS Var G).
Proof.
  apply (FBuild_surjection _ _ id).
  hnf; intros.
  exists b; auto.
Defined.

Lemma canonical_model_canonical: canonical Var G canonical_Kmodel.
Proof.
  intros.
  apply (Build_canonical _ _ _ _ _ _ _ _ canonical_Kmodel_surjection).
  + intros.
    change (DCS Var G) in m, n.
    change (m = m') in H.
    change (n = n') in H0.
    subst n' m'.
    auto.
  + intros.
    change (DCS Var G) in n, m'.
    change (n = n') in H.
    subst n.
    exists m'.
    split; auto.
    change (m' = m').
    auto.
Defined.

Lemma truth_lemma: forall (Phi: DCS Var G) x, canonical_model Phi |= x <-> proj1_sig Phi x.
Proof.
  intros.
  apply (truth_lemma Var CV _ canonical_model_canonical).
  + intros.
    hnf in H; unfold id in H; subst Phi0.
    reflexivity.
  + reflexivity.
Qed.

Theorem complete_intuitionistic_kripke: strongly_complete G SM.
Proof.
  assert (forall Phi x, ~ Phi |-- x -> ~ Phi |== x).
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
    specialize (H2 (canonical_model Psi)).
    apply H1.
    rewrite <- derivable_closed_element_derivable by (exact (proj1 (proj2_sig Psi))).
    rewrite <- truth_lemma.
    apply H2; intros.
    apply truth_lemma.
    apply H0; auto.
  + hnf; intros.
    apply Classical_Prop.NNPP; intro; revert H0.
    apply H; auto.
Qed.

End Canonical_NoBranch.

End Canonical_NoBranch.
