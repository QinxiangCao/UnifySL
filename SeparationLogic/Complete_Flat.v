(* Split it into General proofs and the proof for DeepEmbedded *)
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.HenkinCompleteness.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.PropositionalLogic.Complete.Complete_Kripke.
Require Import Logic.SeparationLogic.DeepEmbedded.Parameter.
Require Logic.SeparationLogic.DeepEmbedded.SeparationEmpLanguage.
Require Logic.SeparationLogic.DeepEmbedded.FlatSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section GeneralCanonical.

Context (Var: Type).
Context (CV: Countable Var).
Context (SLP: SL_Parameter).

Instance L: Language := SeparationEmpLanguage.L Var.
Instance nL: NormalLanguage L := SeparationEmpLanguage.nL Var.
Instance pL: PropositionalLanguage L := SeparationEmpLanguage.pL Var.
Instance sL: SeparationLanguage L := SeparationEmpLanguage.sL Var.
Instance s'L: SeparationEmpLanguage L := SeparationEmpLanguage.s'L Var.
(*
Instance G: ProofTheory L := SeparationLogic.G Var SLP.
Instance nG: NormalProofTheory L G := SeparationLogic.nG Var SLP.
Instance mpG: MinimunPropositionalLogic L G := SeparationLogic.mpG Var SLP.
Instance ipG: IntuitionisticPropositionalLogic L G := SeparationLogic.ipG Var SLP.
*)
Instance MD: Model := FlatSemantics.MD Var.
Instance kMD: KripkeModel MD := FlatSemantics.kMD Var.
Instance R (M: Kmodel): Relation (Kworlds M):= FlatSemantics.R Var M.
Instance po_R (M: Kmodel): PreOrder (@KI.Krelation _ (R M)):= FlatSemantics.po_R Var M.
Instance J (M: Kmodel): Join (Kworlds M):= FlatSemantics.J Var M.
Instance SA (M: Kmodel): SeparationAlgebra (Kworlds M):= FlatSemantics.SA Var M.
Instance uSA (M: Kmodel): UpwardsClosedSeparationAlgebra (Kworlds M):= FlatSemantics.uSA Var M.
Instance dSA (M: Kmodel): DownwardsClosedSeparationAlgebra (Kworlds M):= FlatSemantics.dSA Var M.

Instance SM: Semantics L MD := FlatSemantics.SM Var.
Instance kiSM (M: Kmodel): KripkeIntuitionisticSemantics L MD M SM := FlatSemantics.kiSM Var M.
Instance fsSM (M: Kmodel): FlatSemantics.SeparatingSemantics L MD M SM := FlatSemantics.fsSM Var M.
Instance feSM (M: Kmodel): Same_set _ _ (WeakSemantics.emp) -> FlatSemantics.EmpSemantics L MD M SM := FlatSemantics.feSM Var M.

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

Lemma Lindenbaum_lemma1 {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma}:
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
  assert (Countable expr) by (apply SeparationEmpLanguage.formula_countable; auto).
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

Lemma Lindenbaum_lemma2_right {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}:
  forall Phi1 Phi2 Phi,
    (forall x y, Phi1 |-- x -> Phi |-- y -> Phi2 |-- x * y) ->
    (derivable_closed Phi2 /\ orp_witnessed Phi2 /\ consistent Phi2) ->
    exists Psi,
      Included _ Phi Psi /\
      (forall x y, Phi1 |-- x -> Psi |-- y -> Phi2 |-- x * y) /\
      derivable_closed Psi /\
      orp_witnessed Psi /\
      consistent Psi.
Proof.
  intros ? ? ? ? [Phi2_DC [Phi2_OW Phi2_C]].
  assert (Countable expr) by (apply SeparationEmpLanguage.formula_countable; auto).
  set (step :=
          fun n Phi x0 =>
             Phi x0 \/
            (X x0 n /\
             (forall x y, Phi1 |-- x -> Phi |-- x0 --> y -> Phi2 |-- x * y))).
  exists (LindenbaumConstruction step Phi).
  assert (Included expr Phi (LindenbaumConstruction step Phi) /\
          (forall x y,
            Phi1 |-- x ->
            LindenbaumConstruction step Phi |-- y ->
            Phi2 |-- x * y) /\
          ((forall x y,
            Phi1 |-- x ->
            LindenbaumConstruction step Phi |-- y ->
            Phi2 |-- x * y) ->
           derivable_closed (LindenbaumConstruction step Phi)) /\
          ((forall x y,
            Phi1 |-- x ->
            LindenbaumConstruction step Phi |-- y ->
            Phi2 |-- x * y) ->
           orp_witnessed (LindenbaumConstruction step Phi)) /\
          ((forall x y,
            Phi1 |-- x ->
            LindenbaumConstruction step Phi |-- y ->
            Phi2 |-- x * y) ->
           consistent (LindenbaumConstruction step Phi))).
  Focus 2. {
    destruct H0 as [? [? [? [? ?]]]].
    split; [| split; [| split; [| split]]]; auto.
  } Unfocus.
  split; [| split; [| split; [| split]]].
  + apply (Lindenbaum_spec_included _ _ 0).
  + intros.
    apply NNPP.
    intro; revert H1.
    apply (Lindenbaum_spec_pos _ _
            (fun xs => |-- multi_imp xs y)
            (fun Phi => Phi |-- y)).
    - intros; apply derivable_provable.
    - intros ? ? ? ?; left; auto.
    - intro; apply H2; clear H2.
      apply (H x y); auto.
    - intros.
      destruct (Classical_Prop.classic (exists y0, X y0 n /\ (forall x y, Phi1 |-- x -> S |-- y0 --> y -> Phi2 |-- x * y))) as [[y0 [? ?]] |].
      * intro; apply H2; clear H2.
        specialize (H4 _ y H0).
        apply H4; clear H4.
        rewrite <- deduction_theorem.
        eapply deduction_weaken; [| exact H5].
        hnf; intros ? [? | [? ?]]; [left; auto |].
        pose proof in_inj _ _ X _ _ _ H2 H3.
        subst; right; constructor.
      * intro; apply H1; clear H1.
        eapply deduction_weaken; [| exact H4].
        hnf; intros ? [? | [? ?]]; [auto |].
        exfalso; apply H3; clear H3.
        exists x0; auto.
  + intros; hnf; intros.
    destruct (im_inj _ _ X x) as [n ?].
    apply (Lindenbaum_spec_neg _ _ _ (S n)).
    simpl.
    unfold step at 1.
    right; split; auto.
    intros.
    eapply deduction_weaken in H4; [| apply (Lindenbaum_spec_included _ _ n)].
    pose proof deduction_modus_ponens _ _ _ H1 H4.
    auto.
  + intros; hnf; intros x0 y0 ?.
    destruct (im_inj _ _ X x0) as [nx ?].
    destruct (im_inj _ _ X y0) as [ny ?].
    assert (LindenbaumChain step Phi (S nx) x0 \/ LindenbaumChain step Phi (S ny) y0) as HH;
      [| destruct HH as [HH | HH]; apply Lindenbaum_spec_neg in HH; auto].
    simpl.
    unfold step at 1 3.
    assert ((forall x y,
              Phi1 |-- x ->
              LindenbaumChain step Phi nx |-- x0 --> y ->
              Phi2 |-- x * y) \/
            (forall x y,
              Phi1 |-- x ->
              LindenbaumChain step Phi ny |-- y0 --> y ->
              Phi2 |-- x * y)) as HH;
      [| destruct HH as [HH | HH]; auto].
    assert ((forall x y,
              Phi1 |-- x ->
              LindenbaumConstruction step Phi |-- x0 --> y ->
              Phi2 |-- x * y) \/
            (forall x y,
              Phi1 |-- x ->
              LindenbaumConstruction step Phi |-- y0 --> y ->
              Phi2 |-- x * y)) as HH;
      [
      | destruct HH as [HH | HH]; [left | right];
        intros xx yy ? ?; apply (HH xx yy); auto;
        eapply deduction_weaken;
        [apply (Lindenbaum_spec_included _ _ nx) | auto
        |apply (Lindenbaum_spec_included _ _ ny) | auto ]].

    clear nx ny H2 H3.
    apply NNPP.
    intro.
    apply Classical_Prop.not_or_and in H2; destruct H2.
    apply Classical_Pred_Type.not_all_ex_not in H2.
    apply Classical_Pred_Type.not_all_ex_not in H3.
    destruct H2 as [x'' ?], H3 as [y'' ?].
    apply Classical_Pred_Type.not_all_ex_not in H2.
    apply Classical_Pred_Type.not_all_ex_not in H3.
    destruct H2 as [x' ?], H3 as [y' ?].
    apply imply_to_and in H2.
    apply imply_to_and in H3.
    destruct H2, H3.
    apply imply_to_and in H4.
    apply imply_to_and in H5.
    destruct H4, H5.

    rewrite <- deduction_theorem in H4.
    apply (deduction_orp_intros1 _ _ y') in H4.
    rewrite deduction_theorem in H4.
    rewrite <- deduction_theorem in H5.
    apply (deduction_orp_intros2 _ x') in H5.
    rewrite deduction_theorem in H5.
    pose proof deduction_orp_elim _ _ _ _ H4 H5.
    pose proof deduction_modus_ponens _ _ _ (derivable_assum _ _ H1) H8.
    pose proof deduction_andp_intros _ _ _ H2 H3.
    clear H2 H3 H4 H5 H8.
    pose proof H0 _ _ H10 H9.
    pose proof derivable_sepcon_orp_right Phi2 (x'' && y'') x' y'.
    apply deduction_andp_elim1 in H3.
    pose proof deduction_modus_ponens _ _ _ H2 H3.
    rewrite <- derivable_closed_element_derivable in H4 by auto.
    apply Phi2_OW in H4.
    rewrite !(derivable_closed_element_derivable Phi2) in H4 by auto.
    clear H10 H2 H3.
    destruct H4.
    - pose proof derivable_sepcon_andp_left Phi2 x'' y'' x'.
      pose proof deduction_modus_ponens _ _ _ H2 H3.
      apply deduction_andp_elim1 in H4; auto.
    - pose proof derivable_sepcon_andp_left Phi2 x'' y'' y'.
      pose proof deduction_modus_ponens _ _ _ H2 H3.
      apply deduction_andp_elim2 in H4; auto.
  + intros.
    rewrite consistent_spec in Phi2_C |- *; intro.
    pose proof derivable_impp_refl Phi1 FF.
    specialize (H0  _ _ H2 H1).
    pose proof derivable_sepcon_FF Phi2 TT.
    pose proof deduction_modus_ponens _ _ _ H0 H3.
    auto.
Qed.

Lemma Lindenbaum_lemma2_left {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}:
  forall Phi1 Phi2 Phi,
    (forall x y, Phi |-- x -> Phi1 |-- y -> Phi2 |-- x * y) ->
    (derivable_closed Phi2 /\ orp_witnessed Phi2 /\ consistent Phi2) ->
    exists Psi,
      Included _ Phi Psi /\
      (forall x y, Psi |-- x -> Phi1 |-- y -> Phi2 |-- x * y) /\
      derivable_closed Psi /\
      orp_witnessed Psi /\
      consistent Psi.
Proof.
  intros.
  destruct (Lindenbaum_lemma2_right Phi1 Phi2 Phi) as [Psi [? [? ?]]]; auto.
  + intros.
    rewrite <- (sepcon_comm y x).
    apply H; auto.
  + exists Psi.
    split; [| split]; auto.
    intros.
    rewrite <- (sepcon_comm y x).
    apply H2; auto.
Qed.

Definition context_sepcon {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (Phi Psi: context): context :=
  fun z => exists x y, z = x * y /\ Phi |-- x /\ Psi |-- y.

Lemma context_sepcon_derivable {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}:
  forall (Phi Psi: context) z,
    context_sepcon Phi Psi |-- z ->
    exists x y, |-- x * y --> z /\ Phi |-- x /\ Psi |-- y.
Proof.
  intros.
  rewrite derivable_provable in H.
  destruct H as [xs [? ?]].
  revert z H0; induction H; intros.
  + exists TT, TT.
    split; [| split].
    - apply aux_minimun_rule00; auto.
    - apply derivable_impp_refl.
    - apply derivable_impp_refl.
  + pose proof provable_multi_imp_arg_switch1 l x z.
    pose proof modus_ponens _ _ H2 H1.
    specialize (IHForall _ H3); clear H1 H2 H3.
    destruct H as [x' [y' [? [? ?]]]]; subst x.
    destruct IHForall as [x [y [? [? ?]]]].
    exists (x && x'), (y && y').
    split; [| split].
    - clear l H0 H1 H2 H3 H4.
      rewrite (provable_sepcon_andp_right (x && x') y y').
      rewrite (provable_sepcon_andp_left x x' y).
      rewrite (provable_sepcon_andp_left x x' y').
      rewrite (andp_elim1 (x * y) _).
      rewrite (andp_elim2 _ (x' * y')).
      rewrite provable_derivable.
      rewrite <- deduction_theorem.
      pose proof derivable_assum1 empty_context ((x * y) && (x' * y')).
      pose proof deduction_andp_elim1 _ _ _ H0.
      pose proof deduction_andp_elim2 _ _ _ H0.
      apply (deduction_weaken0 (Union _ empty_context (Singleton _ (x * y && (x' * y'))))) in H.
      pose proof deduction_modus_ponens _ _ _ H1 H.
      pose proof deduction_modus_ponens _ _ _ H2 H3.
      auto.
    - apply deduction_andp_intros; auto.
    - apply deduction_andp_intros; auto.
Qed.

Instance DCS_R {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: Relation (DCS Gamma) := fun a b => Included _ (proj1_sig a) (proj1_sig b).

Instance po_DCS_R {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: PreOrder (@KI.Krelation _ DCS_R).
Proof.
  constructor.
  + hnf; intros.
    hnf; intros; auto.
  + hnf; intros.
    hnf; intros; auto.
Qed.

Instance DCS_J {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: Join (DCS Gamma) := (fun a b c => forall x y, proj1_sig a x -> proj1_sig b y -> proj1_sig c (x * y)).

Instance DCS_SA {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: SeparationAlgebra (DCS Gamma).
Proof.
  pose proof (fun Phi: DCS Gamma => derivable_closed_element_derivable (proj1_sig Phi) (proj1 (proj2_sig Phi))) as ED.
  constructor.
  + intros; simpl in *.
    intros x y ? ?.
    specialize (H y x H1 H0).
    pose proof proj2_sig m.
    destruct H2 as [? _].
    rewrite ED in H |- *.
    rewrite <- (@sepcon_comm _ _ _ _ _ _ _ _ sGamma y x).
    auto.
  + intros.
    set (Phi := context_sepcon (proj1_sig my) (proj1_sig mz)).
    assert (forall x yz,
              proj1_sig mx |-- x ->
              Phi |-- yz ->
              proj1_sig mxyz |-- (x * yz)).
    Focus 1. {
      intros.
      destruct (context_sepcon_derivable _ _ _ H2) as [y [z [? [? ?]]]].
      rewrite <- H3.
      rewrite (sepcon_assoc x y z).
      rewrite <- ED in H1, H4, H5.
      specialize (H _ _ H1 H4).
      specialize (H0 _ _ H H5).
      rewrite <- ED; auto.
    } Unfocus.
    destruct (Lindenbaum_lemma2_right
               (proj1_sig mx) (proj1_sig mxyz) Phi H1 (proj2_sig mxyz))
      as [Psi [? [? ?]]].
    set (myz := exist _ Psi H4 : DCS Gamma).
    change Psi with (proj1_sig myz) in H2, H3;
    clearbody myz; clear Psi H4.
    exists myz.
    split.
    - hnf; intros.
      apply H2; unfold Ensembles.In.
      subst Phi; hnf.
      rewrite ED in H4, H5.
      exists x, y; auto.
    - hnf; intros x yz ? ?.
      rewrite ED in H4, H5 |- *.
      apply H3; auto.
Qed.

Instance DCS_uSA {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: UpwardsClosedSeparationAlgebra (DCS Gamma).
Proof.
  hnf; intros.
  exists m1, m2.
  split; [| split]; [| reflexivity ..].
  hnf; intros.
  apply H0.
  apply H; auto.
Qed.

Instance DCS_dSA {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: DownwardsClosedSeparationAlgebra (DCS Gamma).
Proof.
  hnf; intros.
  exists m.
  split; [| reflexivity].
  hnf; intros.
  apply H; auto.
  + apply H0; auto.
  + apply H1; auto.
Qed.

Definition canonical_frame {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: FlatSemantics.frame :=
  FlatSemantics.Build_frame (DCS Gamma) DCS_R po_DCS_R DCS_J DCS_SA DCS_dSA DCS_uSA.

Program Definition canonical_emp {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: FlatSemantics.sem canonical_frame :=
  fun a => a (SeparationEmpLanguage.emp).
Next Obligation.
  hnf; intros.
  apply H; auto.
Qed.

Program Definition canonical_eval {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: Var -> FlatSemantics.sem canonical_frame :=
  fun p a => a (SeparationEmpLanguage.varp p).
Next Obligation.
  hnf; intros.
  apply H; auto.
Qed.

Definition canonical_Kmodel {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: @Kmodel MD kMD :=
  FlatSemantics.Build_Kmodel Var canonical_frame canonical_emp canonical_eval.

Definition canonical_model {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}(Phi: DCS Gamma) : @model MD :=
  FlatSemantics.Build_model Var canonical_Kmodel Phi.

Lemma truth_lemma {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}:
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
    change (SeparationEmpLanguage.andp x1 x2) with (x1 && x2).
    rewrite sat_andp.
    tauto.
  + specialize (IHx1 Phi).
    specialize (IHx2 Phi).
    pose proof DCS_orp_iff (proj1_sig Phi) (proj1 (proj2_sig Phi)) (proj1 (proj2 (proj2_sig Phi))) x1 x2.
    change (SeparationEmpLanguage.orp x1 x2) with (x1 || x2).
    rewrite sat_orp.
    tauto.
  + split.
    - intros.
      rewrite H.
      change (SeparationEmpLanguage.impp x1 x2) with (x1 --> x2) in *.
      apply deduction_theorem.
      apply Classical_Prop.NNPP; intro.
      pose proof Lindenbaum_lemma1 _ _ H1.
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
      change (SeparationEmpLanguage.impp x1 x2) with (x1 --> x2) in *.
      rewrite sat_impp; intros Psi ?H.
      rewrite IHx1, IHx2 by eauto.
      intros.
      rewrite H in H0, H2 |- *.
      eapply deduction_weaken in H0; [| exact H1].
      eapply deduction_modus_ponens; [exact H2 | exact H0].
  + change (SeparationEmpLanguage.sepcon x1 x2) with (x1 * x2).
    rewrite sat_sepcon.
    split.
    - intros [Phi1 [Phi2 [? [? ?]]]].
      rewrite (IHx1 Phi1) in H1.
      rewrite (IHx2 Phi2) in H2.
      apply H0; auto.
    - intros.
      rewrite H in H0.
      pose proof Lindenbaum_lemma2_left (Union _ empty_context (Singleton _ x2)) (proj1_sig Phi) (Union _ empty_context (Singleton _ x1)) as [Phi1' [? [? ?]]].
      Focus 1. {
        intros x1' x2' ? ?.
        rewrite deduction_theorem in H1, H2.
        rewrite <- provable_derivable in H1, H2.
        rewrite <- H1, <- H2; auto.
      } Unfocus.
      Focus 1. { exact (proj2_sig Phi). } Unfocus.
      set (Phi1 := exist _ Phi1' H3 : DCS Gamma).
      change Phi1' with (proj1_sig Phi1) in H1, H2.
      assert (proj1_sig Phi1 x1) by (apply (H1 x1); right; constructor).
      clearbody Phi1; clear Phi1' H1 H3.

      pose proof Lindenbaum_lemma2_right (proj1_sig Phi1) (proj1_sig Phi) (Union _ empty_context (Singleton _ x2)) as [Phi2' [? [? ?]]].
      Focus 1. {
        intros x1' x2' ? ?.
        apply H2; auto.
      } Unfocus.
      Focus 1. { exact (proj2_sig Phi). } Unfocus.
      set (Phi2 := exist _ Phi2' H5 : DCS Gamma).
      change Phi2' with (proj1_sig Phi2) in H1, H3.
      assert (proj1_sig Phi2 x2) by (apply (H1 x2); right; constructor).
      clearbody Phi2; clear Phi2' H1 H2 H5.

      exists Phi1, Phi2.
      split; [| split].
      * hnf; intros.
        rewrite H in H1, H2 |- *.
        apply H3; auto.
      * rewrite (IHx1 Phi1); auto.
      * rewrite (IHx2 Phi2); auto.
  + change (SeparationEmpLanguage.wand x1 x2) with (x1 -* x2).
    rewrite sat_wand.
    split.
    - intros.
      destruct (Classical_Prop.classic (context_sepcon (proj1_sig Phi) (Union (@expr L) empty_context (Singleton _ x1)) |-- x2)).
      * destruct (context_sepcon_derivable _ _ _ H1) as [x [x1' [? [? ?]]]].
        rewrite deduction_theorem, <- provable_derivable in H4.
        rewrite <- H4 in H2.
        apply wand_sepcon_adjoint in H2.
        rewrite H2 in H3.
        rewrite H; auto.
      * exfalso.
        pose proof Lindenbaum_lemma1 _ _ H1 as [Phi2' [? [? ?]]].
        set (Phi2 := exist _ Phi2' H4 : DCS Gamma).
        change Phi2' with (proj1_sig Phi2) in H2, H3.
        assert (forall x x1', proj1_sig Phi |-- x -> Union (@expr L) empty_context (Singleton _ x1) |-- x1' -> proj1_sig Phi2 |-- x * x1').
        Focus 1. {
          intros.
          rewrite <- H.
          apply (H2 (x * x1')).
          exists x, x1'; auto.
        } Unfocus.
        clearbody Phi2; clear Phi2' H1 H2 H4.
        pose proof Lindenbaum_lemma2_right _ _ _ H5 (proj2_sig Phi2)
          as [Phi1' [? [? ?]]].
        set (Phi1 := exist _ Phi1' H4 : DCS Gamma).
        change Phi1' with (proj1_sig Phi1) in H1, H2.
        assert (proj1_sig Phi1 x1) by (apply (H1 x1); right; constructor).
        clearbody Phi1; clear Phi1' H1 H4 H5.
        specialize (H0 Phi1 Phi2).
        rewrite IHx1, IHx2 in H0.
        apply H3; rewrite <- H; apply H0; auto.
        hnf; intros.
        rewrite H in H1, H4 |- *; apply H2; auto.
    - intros ? Phi1 Phi2 ? ?.
      rewrite IHx1 in H2; rewrite IHx2.
      specialize (H1 _ _ H0 H2).
      rewrite H in H1 |- *.
      rewrite provable_wand_sepcon_modus_ponens1 in H1.
      auto.
  + reflexivity.
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

Lemma classical_canonical_ident {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {cpGamma: ClassicalPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: forall Psi: DCS Gamma, KripkeModelClass _ (FlatSemantics.Kmodel_Identity Var)
  (canonical_model Psi).
Proof.
  intros.
  unfold canonical_model; constructor.
  hnf; constructor.
  intros.
  change (DCS Gamma) in m, n.
  rewrite (@DCS_ext Gamma).
  intros.
  split; auto; [apply H |].
  intros.
  rewrite DCS_negp_iff in H0 by (destruct (proj2_sig n); tauto).
  assert (~ proj1_sig m (~~ x)) by (intro; apply H0, H; auto).
  rewrite DCS_negp_iff by (destruct (proj2_sig m); tauto).
  auto.
Qed.

Lemma Godel_Dummett_canonical_no_branch {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {gdpGamma: GodelDummettPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: forall Psi: DCS Gamma, KripkeModelClass _ (FlatSemantics.Kmodel_NoBranch Var) (canonical_model Psi).
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

Lemma weak_classical_canonical_branch_join {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {dmpGamma: DeMorganPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: forall Psi: DCS Gamma, KripkeModelClass _ (FlatSemantics.Kmodel_BranchJoin Var) (canonical_model Psi).
Proof.
  intros.
  unfold canonical_model; constructor.
  hnf; constructor.
  intros.
  change (DCS Gamma) in m1, m2, n.
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
  destruct (Lindenbaum_lemma1 _ _ H8) as [m' [? [_ ?]]].
  set (m := exist _ m' H10: DCS Gamma).
  change m' with (proj1_sig m) in H9.
  clearbody m; clear m' H10.
  exists m.
  split.
  + intros ? ?; apply H9; left; auto.
  + intros ? ?; apply H9; right; auto.
Qed.

Lemma garbage_collected_canonical_nonpos {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {gcGamma: GarbageCollectSeparationLogic L Gamma}: forall Psi: DCS Gamma, KripkeModelClass _ (FlatSemantics.Kmodel_Increasing Var) (canonical_model Psi).
Proof.
  intros.
  pose proof (fun Phi: DCS Gamma => derivable_closed_element_derivable (proj1_sig Phi) (proj1 (proj2_sig Phi))) as ED.
  unfold canonical_model; constructor.
  hnf; constructor.
  intros m.
  hnf; intros m1 m2.
  change (DCS Gamma) in m1, m2, m.
  hnf; unfold Ensembles.In; intros.
  hnf; unfold Ensembles.In; intros.
  apply join_comm in H.
  specialize (H x TT H0).
  rewrite !ED in H.
  specialize (H (derivable_impp_refl _ _)).
  apply deduction_sepcon_elim1 in H.
  rewrite ED; auto.
Qed.

Lemma emp_canonical_unital {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {EmpSGamma: EmpSeparationLogic L Gamma}: forall Psi: DCS Gamma, KripkeModelClass _ (FlatSemantics.Kmodel_Unital Var) (canonical_model Psi).
Proof.
  intros.
  constructor; clear Psi.
  pose proof (fun Phi: DCS Gamma => derivable_closed_element_derivable (proj1_sig Phi) (proj1 (proj2_sig Phi))) as ED.
  assert (forall Phi: Kworlds canonical_Kmodel, proj1_sig Phi emp -> increasing Phi) as HH1a.
  Focus 1. {
    intros.
    hnf; intros Psi Psi' ?.
    hnf; unfold Ensembles.In; intros.
    specialize (H0 emp x H H1).
    rewrite ED in H0 |- *.
    rewrite sepcon_comm, sepcon_emp in H0; auto.
  } Unfocus.
  assert (forall Phi: Kworlds canonical_Kmodel, increasing Phi -> proj1_sig Phi emp) as HH2b.
  Focus 1. {
    intros.
    set (Phi1' := Union _ empty_context (Singleton _ emp)).
    set (Phi2' := context_sepcon (proj1_sig Phi) Phi1').
    assert (Phi2' |-- emp).
    Focus 1. {
      apply NNPP.
      intro.
      destruct (Lindenbaum_lemma1 _ _ H0) as [Phi2'' [? [? ?]]].
      set (Phi2 := exist _ Phi2'' H3: DCS Gamma).
      assert (forall x y, proj1_sig Phi |-- x ->
                          Phi1' |-- y ->
                          proj1_sig Phi2 |-- x * y).
      Focus 1. {
        intros.
        rewrite <- ED.
        apply H1; exists x, y; auto.
      } Unfocus.
      change Phi2'' with (proj1_sig Phi2) in H2.
      clearbody Phi2; clear Phi2'' H0 H1 H3 Phi2'.
      destruct (Lindenbaum_lemma2_right _ _ _ H4 (proj2_sig Phi2))
        as [Phi1'' [? [? ?]]].
      set (Phi1 := exist _ Phi1'' H3: DCS Gamma).
      assert (proj1_sig Phi1 emp).
      Focus 1. {
        apply H0.
        subst Phi1'.
        right.
        constructor.
      } Unfocus.
      change Phi1'' with (proj1_sig Phi1) in H1.
      clearbody Phi1; clear Phi1'' Phi1' H4 H3 H0.
      assert (join Phi Phi1 Phi2).
      Focus 1. {
        hnf; intros ? ?.
        rewrite !ED; auto.
      } Unfocus.
      specialize (H Phi1 Phi2 H0); clear H0.
      pose proof H _ H5; unfold Ensembles.In in *.
      rewrite ED in H0.
      auto.
    } Unfocus.
    apply context_sepcon_derivable in H0.
    destruct H0 as [x [y [? [? ?]]]].
    subst Phi1'; rewrite deduction_theorem, <- provable_derivable in H2.
    rewrite <- H2 in H0.
    apply wand_sepcon_adjoint in H0.
    rewrite H0 in H1.
    rewrite <- (sepcon_emp (emp -* emp)) in H1.
    rewrite provable_wand_sepcon_modus_ponens1, <- ED in H1.
    auto.
  } Unfocus.
  assert (forall Phi: Kworlds canonical_Kmodel, proj1_sig Phi emp <-> increasing Phi) as HH
    by (intros; split; [apply HH1a | apply HH2b]; auto).
  clear HH1a HH2b.
  constructor; [| constructor].
  + simpl; intros.
    rewrite <- HH.
    reflexivity.
  + intros Phi.
    assert (forall x y, proj1_sig Phi |-- x -> Union _ empty_context (Singleton _ emp) |-- y -> proj1_sig Phi |-- x * y).
    Focus 1. {
      intros.
      rewrite deduction_theorem, <- provable_derivable in H0.
      rewrite <- H0.
      rewrite sepcon_emp; auto.
    } Unfocus.
    destruct (Lindenbaum_lemma2_right _ _ _ H (proj2_sig Phi))
      as [Psi' [? [? ?]]].
    set (Psi := exist _ Psi' H2: DCS Gamma).
    change Psi' with (proj1_sig Psi) in H0, H1.
    clearbody Psi; clear Psi' H2.
    exists Psi.
    split.
    - exists Phi.
      split; [| reflexivity].
      hnf; intros.
      rewrite ED, <- sepcon_comm.
      apply H1; rewrite <- ED; auto.
    - rewrite <- HH.
      apply H0.
      right; constructor.
Qed.

Lemma ext_canonical_residual {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {ExtSGamma: ExtSeparationLogic L Gamma}: forall Psi: DCS Gamma, KripkeModelClass _ (FlatSemantics.Kmodel_Residual Var) (canonical_model Psi).
Proof.
  constructor.
  constructor.
  clear Psi.
  pose proof (fun Phi: DCS Gamma => derivable_closed_element_derivable (proj1_sig Phi) (proj1 (proj2_sig Phi))) as ED.
  intros Phi.
  change (DCS Gamma) in Phi.
  assert (forall x y, Union _ empty_context (Singleton _ TT) |-- x ->
            proj1_sig Phi |-- y -> proj1_sig Phi |-- x * y).
  Focus 1. {
    intros.
    rewrite deduction_theorem, <- provable_derivable in H.
    rewrite <- H.
    rewrite <- sepcon_comm, <- sepcon_ext; auto.
  } Unfocus.
  destruct (Lindenbaum_lemma2_left _ _ _ H (proj2_sig Phi))
      as [Psi' [? [? ?]]].
  set (Psi := exist _ Psi' H2: DCS Gamma).
  change Psi' with (proj1_sig Psi) in H1.
  clearbody Psi; clear Psi' H0 H2.
  exists Psi.
  exists Phi.
  split; [| reflexivity].
  hnf; intros.
  rewrite ED in H0, H2 |- *; auto.
Qed.

End GeneralCanonical.



