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

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Section Lindenbaum_Flat.

Context {L: Language}
        {nL: NormalLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {Gamma: ProofTheory L}
        {nGamma: NormalProofTheory L Gamma}
        {mpGamma: MinimunPropositionalLogic L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma}.

Hypothesis CE: Countable expr.

Lemma Lindenbaum_lemma_right:
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
  set (step :=
          fun n Phi x0 =>
             Phi x0 \/
            (CE x0 n /\
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
      destruct (Classical_Prop.classic (exists y0, CE y0 n /\ (forall x y, Phi1 |-- x -> S |-- y0 --> y -> Phi2 |-- x * y))) as [[y0 [? ?]] |].
      * intro; apply H2; clear H2.
        specialize (H4 _ y H0).
        apply H4; clear H4.
        rewrite <- deduction_theorem.
        eapply deduction_weaken; [| exact H5].
        hnf; intros ? [? | [? ?]]; [left; auto |].
        pose proof in_inj _ _ CE _ _ _ H2 H3.
        subst; right; constructor.
      * intro; apply H1; clear H1.
        eapply deduction_weaken; [| exact H4].
        hnf; intros ? [? | [? ?]]; [auto |].
        exfalso; apply H3; clear H3.
        exists x0; auto.
  + intros; hnf; intros.
    destruct (im_inj _ _ CE x) as [n ?].
    apply (Lindenbaum_spec_neg _ _ _ (S n)).
    simpl.
    unfold step at 1.
    right; split; auto.
    intros.
    eapply deduction_weaken in H4; [| apply (Lindenbaum_spec_included _ _ n)].
    pose proof deduction_modus_ponens _ _ _ H1 H4.
    auto.
  + intros; hnf; intros x0 y0 ?.
    destruct (im_inj _ _ CE x0) as [nx ?].
    destruct (im_inj _ _ CE y0) as [ny ?].
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

End Lindenbaum_Flat.