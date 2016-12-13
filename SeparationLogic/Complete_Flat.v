Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.MinimunLogic.ContextProperty.
Require Import Logic.MinimunLogic.RewriteClass.
Require Import Logic.MinimunLogic.HenkinCompleteness.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.PropositionalLogic.Complete_Kripke.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.SeparationLogic.Semantics. Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.PropositionalLogic.IntuitionisticPropositionalLogic.
Require Import Logic.PropositionalLogic.RewriteClass.
Require Import Logic.SeparationLogic.SeparationLogic.
Require Import Logic.SeparationLogic.SoundCompleteParameter.

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

Instance L: Language := UnitarySeparationLanguage.L Var.
Instance nL: NormalLanguage L := UnitarySeparationLanguage.nL Var.
Instance pL: PropositionalLanguage L := UnitarySeparationLanguage.pL Var.
Instance sL: SeparationLanguage L := UnitarySeparationLanguage.sL Var.
Instance usL: UnitarySeparationLanguage L := UnitarySeparationLanguage.usL Var.
(*
Instance G: ProofTheory L := SeparationLogic.G Var SLP.
Instance nG: NormalProofTheory L G := SeparationLogic.nG Var SLP.
Instance mpG: MinimunPropositionalLogic L G := SeparationLogic.mpG Var SLP.
Instance ipG: IntuitionisticPropositionalLogic L G := SeparationLogic.ipG Var SLP.
*)
Instance MD: Model := FlatSemanticsModel.MD Var.
Instance kMD: KripkeModel MD := FlatSemanticsModel.kMD Var.
Instance kiM (M: Kmodel): KripkeIntuitionisticModel (Kworlds M):= FlatSemanticsModel.kiM (FlatSemanticsModel.underlying_frame Var M).
Instance J (M: Kmodel): Join (Kworlds M):= FlatSemanticsModel.J (FlatSemanticsModel.underlying_frame Var M).
Instance SA (M: Kmodel): SeparationAlgebra (Kworlds M):= FlatSemanticsModel.SA (FlatSemanticsModel.underlying_frame Var M).
Instance dSA (M: Kmodel): DownwardsClosedSeparationAlgebra (Kworlds M):= FlatSemanticsModel.dSA (FlatSemanticsModel.underlying_frame Var M).
Instance uSA (M: Kmodel): UpwardsClosedSeparationAlgebra (Kworlds M):= FlatSemanticsModel.uSA (FlatSemanticsModel.underlying_frame Var M).

Instance SM: Semantics L MD := FlatSemanticsModel.SM Var.
Instance kiSM (M: Kmodel): KripkeIntuitionisticSemantics L MD M SM := FlatSemanticsModel.kiSM Var M.
Instance fsSM (M: Kmodel): FlatSemantics.FlatSemantics L MD M SM := FlatSemanticsModel.fsSM Var M.
Instance UsSM (M: Kmodel): UnitarySemantics L MD M SM := FlatSemanticsModel.UsSM Var M.
Locate derivable_closed.
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
  assert (Countable expr) by (apply UnitarySeparationLanguage.formula_countable; auto).
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

Lemma Lindenbaum_lemma2 {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}:
  forall Phi1 Phi2 Phi,
    (forall x y, Phi1 |-- x -> Phi |-- y -> Phi2 |-- x * y) ->
    derivable_closed Phi2 ->
    orp_witnessed Phi2 ->
    consistent Phi2 ->
    exists Psi,
      Included _ Phi Psi /\
      (forall x y, Phi1 |-- x -> Psi |-- y -> Phi2 |-- x * y) /\
      derivable_closed Psi /\
      orp_witnessed Psi /\
      consistent Psi.
Proof.
  intros ? ? ? ? Phi2_DC Phi2_OW Phi2_C.
  assert (Countable expr) by (apply UnitarySeparationLanguage.formula_countable; auto).
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

Definition context_sepcon {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} (Phi Psi: context): context :=
  fun z => exists x y, z = x * y /\ Phi x /\ Psi y.

Lemma context_sepcon_derivable_closed {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}:
  forall (Phi Psi: context) z,
    derivable_closed Phi ->
    derivable_closed Psi ->
    context_sepcon Phi Psi |-- z ->
    exists x y, |-- x * y --> z /\ Phi x /\ Psi y.
Proof.
  intros.
  rewrite derivable_provable in H1.
  destruct H1 as [xs [? ?]].
  revert z H2; induction H1; intros.
  + exists TT, TT.
    split; [| split].
    - apply aux_minimun_rule00; auto.
    - rewrite derivable_closed_element_derivable by auto.
      apply derivable_impp_refl.
    - rewrite derivable_closed_element_derivable by auto.
      apply derivable_impp_refl.
  + pose proof provable_multi_imp_arg_switch1 l x z.
    pose proof modus_ponens _ _ H4 H3.
    specialize (IHForall _ H5); clear H3 H4 H5.
    destruct H1 as [x' [y' [? [? ?]]]]; subst x.
    destruct IHForall as [x [y [? [? ?]]]].
    exists (x && x'), (y && y').
    split; [| split].
    - clear l H2 H3 H4 H5 H6.
      rewrite (provable_sepcon_andp_right (x && x') y y').
      rewrite (provable_sepcon_andp_left x x' y).
      rewrite (provable_sepcon_andp_left x x' y').
      rewrite (andp_elim1 (x * y) _).
      rewrite (andp_elim2 _ (x' * y')).
      rewrite provable_derivable.
      rewrite <- deduction_theorem.
      pose proof derivable_assum1 empty_context ((x * y) && (x' * y')).
      pose proof deduction_andp_elim1 _ _ _ H2.
      pose proof deduction_andp_elim2 _ _ _ H2.
      apply (deduction_weaken0 (Union _ empty_context (Singleton _ (x * y && (x' * y'))))) in H1.
      pose proof deduction_modus_ponens _ _ _ H3 H1.
      pose proof deduction_modus_ponens _ _ _ H4 H5.
      auto.
    - rewrite derivable_closed_element_derivable in H3, H5 |- * by auto.
      apply deduction_andp_intros; auto.
    - rewrite derivable_closed_element_derivable in H4, H6 |- * by auto.
      apply deduction_andp_intros; auto.
Qed.

Definition canonical_frame {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: FlatSemanticsModel.frame.
Proof.
  refine (FlatSemanticsModel.Build_frame (DCS Gamma) (fun a b => Included _ (proj1_sig b) (proj1_sig a)) _ (fun a b c => forall x y, proj1_sig a x -> proj1_sig b y -> proj1_sig c (x * y)) _ _ _).
  Unshelve.
  Focus 5. shelve.
  Focus 5. shelve.
  Focus 5. shelve.
  Focus 4. {
    constructor.
    + hnf; intros.
      hnf; intros; auto.
    + hnf; intros.
      hnf; intros; auto.
  } Unfocus.
  + pose proof (fun Phi: DCS Gamma => derivable_closed_element_derivable (proj1_sig Phi) (proj1 (proj2_sig Phi))) as ED.
    constructor.
    - intros; simpl in *.
      intros x y ? ?.
      specialize (H y x H1 H0).
      pose proof proj2_sig m.
      destruct H2 as [? _].
      rewrite ED in H |- *.
      rewrite <- (@sepcon_comm _ _ _ _ _ _ _ _ sGamma y x).
      auto.
    - intros.
      set (Phi := context_sepcon (proj1_sig my) (proj1_sig mz)).
      assert (forall x yz,
                proj1_sig mx |-- x ->
                Phi |-- yz ->
                proj1_sig mxyz |-- (x * yz)).
      Focus 1. {
        intros.
        destruct (context_sepcon_derivable_closed (proj1_sig my) (proj1_sig mz) yz) as [y [z [? [? ?]]]].
        1: destruct (proj2_sig my); auto.
        1: destruct (proj2_sig mz); auto.
        1: auto.
        rewrite <- H3.
        rewrite (sepcon_assoc x y z).
        rewrite <- ED in H1.
        specialize (H _ _ H1 H4).
        specialize (H0 _ _ H H5).
        rewrite <- ED; auto.
      } Unfocus.
      destruct (Lindenbaum_lemma2 (proj1_sig mx) (proj1_sig mxyz) Phi H1)
        as [Psi [? [? ?]]];
        [destruct (proj2_sig mxyz) as [? [? ?]]; auto .. |].
      set (myz := exist _ Psi H4 : DCS Gamma).
      change Psi with (proj1_sig myz) in H2, H3;
      clearbody myz; clear Psi H4.
      exists myz.
      split.
      * hnf; intros.
        apply H2; unfold Ensembles.In.
        subst Phi; hnf.
        exists x, y; auto.
      * hnf; intros x yz ? ?.
        rewrite ED in H4, H5 |- *.
        apply H3; auto.
  + hnf; intros.
    exists m1, m2.
    split; [| split]; [| reflexivity ..].
    hnf; intros.
    apply H0.
    apply H; auto.
  + hnf; intros.
    exists m.
    split; [| reflexivity].
    hnf; intros.
    apply H; auto.
    - apply H0; auto.
    - apply H1; auto.
Defined.

Program Definition canonical_eval {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}: Var -> FlatSemanticsModel.sem canonical_frame :=
  fun p a => a (UnitarySeparationLanguage.varp p).
Next Obligation.
  apply H; auto.
Qed.

