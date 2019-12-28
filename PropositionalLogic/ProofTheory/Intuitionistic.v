Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

(* TODO: rename it to IntuitionisticPropositionalAxiomatization. *)
Class IntuitionisticPropositionalLogic (L: Language) {minL: MinimumLanguage L} {pL: PropositionalLanguage L} (Gamma: Provable L) {minAX: MinimumAxiomatization L Gamma} := {
  andp_intros: forall x y, |-- x --> y --> x && y;
  andp_elim1: forall x y, |-- x && y --> x;
  andp_elim2: forall x y, |-- x && y --> y;
  orp_intros1: forall x y, |-- x --> x || y;
  orp_intros2: forall x y, |-- y --> x || y;
  orp_elim: forall x y z, |-- (x --> z) --> (y --> z) --> (x || y --> z);
  falsep_elim: forall x, |-- FF --> x
}.

Class IntuitionisticPropositionalSequentCalculus (L: Language) {pL: PropositionalLanguage L} (Gamma: Derivable L) := {
  deduction_andp_intros: forall Phi x y, Phi |-- x -> Phi |-- y -> Phi |-- x && y;
  deduction_andp_elim1: forall Phi x y, Phi |-- x && y -> Phi |-- x;
  deduction_andp_elim2: forall Phi x y, Phi |-- x && y -> Phi |-- y;
  deduction_orp_intros1: forall Phi x y, Phi |-- x -> Phi |-- x || y;
  deduction_orp_intros2: forall Phi x y, Phi |-- y -> Phi |-- x || y;
  deduction_orp_elim: forall Phi x y z, Phi;; x |-- z -> Phi ;; y |-- z -> Phi;; x || y |-- z;
  deduction_falsep_elim: forall Phi x, Phi |-- FF -> Phi |-- x
}.

Section DerivableRulesFromSequentCalculus1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: Derivable L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimumSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}.

Lemma derivable_andp_intros: forall (Phi: context) (x y: expr),
  Phi |-- x --> y --> x && y.
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_andp_intros; solve_assum.
Qed.

Lemma derivable_andp_elim1: forall (Phi: context) (x y: expr),
  Phi |-- x && y --> x.
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_andp_elim1 with y; solve_assum.
Qed.

Lemma derivable_andp_elim2: forall (Phi: context) (x y: expr),
  Phi |-- x && y --> y.
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_andp_elim2 with x; solve_assum.
Qed.

Lemma derivable_orp_intros1: forall (Phi: context) (x y: expr),
  Phi |-- x --> x || y.
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_orp_intros1; solve_assum.
Qed.

Lemma derivable_orp_intros2: forall (Phi: context) (x y: expr),
  Phi |-- y --> x || y.
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_orp_intros2; solve_assum.
Qed.

Lemma derivable_orp_elim: forall (Phi: context) (x y z: expr),
  Phi |-- (x --> z) --> (y --> z) --> (x || y --> z).
Proof.
  intros.
  rewrite <- !deduction_theorem.
  apply deduction_orp_elim.
  + rewrite deduction_theorem; solve_assum.
  + rewrite deduction_theorem; solve_assum.
Qed.

Lemma derivable_falsep_elim: forall (Phi: context) (x: expr),
  Phi |-- FF --> x.
Proof.
  intros.
  rewrite <- deduction_theorem.
  apply deduction_falsep_elim; solve_assum.
Qed.

Lemma deduction_orp_elim': forall (Phi: context) (x y z: expr),
  Phi |-- x --> z ->
  Phi |-- y --> z ->
  Phi |-- x || y --> z.
Proof.
  intros.
  rewrite <- deduction_theorem in H, H0 |- *.
  apply deduction_orp_elim; auto.
Qed.

Lemma derivable_double_negp_intros: forall (Phi: context) (x: expr),
  Phi |-- x --> ~~ ~~ x.
Proof.
  intros.
  unfold negp.
  apply derivable_modus_ponens.
Qed.

Lemma deduction_double_negp_intros: forall (Phi: context) (x: expr),
  Phi |-- x ->
  Phi |-- ~~ ~~ x.
Proof.
  intros.
  eapply deduction_modus_ponens; eauto.
  apply derivable_double_negp_intros.
Qed.

Lemma derivable_contradiction_elim: forall (Phi: context) (x y: expr),
  Phi |-- x --> ~~ x --> y.
Proof.
  intros.
  pose proof derivable_double_negp_intros Phi x.
  pose proof derivable_falsep_elim Phi y.

  unfold negp at 1 in H.
  rewrite <- !deduction_theorem in H |- *.
  apply (deduction_weaken1 _ x) in H0.
  apply (deduction_weaken1 _ (~~ x)) in H0.
  pose proof deduction_modus_ponens _ _ _ H H0.
  auto.
Qed.

Lemma deduction_contradiction_elim: forall (Phi: context) (x y: expr),
  Phi |-- x ->
  Phi |-- ~~ x ->
  Phi |-- y.
Proof.
  intros.
  pose proof derivable_contradiction_elim Phi x y.
  pose proof deduction_modus_ponens _ _ _ H H1.
  pose proof deduction_modus_ponens _ _ _ H0 H2.
  auto.
Qed.

Lemma derivable_iffp_refl: forall (Phi: context) (x: expr),
  Phi |-- x <--> x.
Proof.
  intros.
  apply deduction_andp_intros; apply derivable_impp_refl.
Qed.

End DerivableRulesFromSequentCalculus1.

Section SequentCalculus2Axiomatization.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {SC: NormalSequentCalculus L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {ipSC: IntuitionisticPropositionalSequentCalculus L GammaD}
        {minAX: MinimumAxiomatization L GammaP}.

Lemma SequentCalculus2Axiomatization_ipAX: IntuitionisticPropositionalLogic L GammaP.
Proof.
  constructor; intros; rewrite provable_derivable.
  + apply derivable_andp_intros.
  + apply derivable_andp_elim1.
  + apply derivable_andp_elim2.
  + apply derivable_orp_intros1.
  + apply derivable_orp_intros2.
  + apply derivable_orp_elim.
  + apply derivable_falsep_elim.
Qed.

End SequentCalculus2Axiomatization.

Instance reg_SequentCalculus2Axiomatization_ipAX:
  RegisterClass D2P_reg (fun ipAX: unit => @SequentCalculus2Axiomatization_ipAX) 2.
Qed.

Section Axiomatization2SequentCalculus.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {AX: NormalAxiomatization L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {minAX: MinimumAxiomatization L GammaP}
        {ipGamma: IntuitionisticPropositionalLogic L GammaP}.

Lemma Axiomatization2SequentCalculus_ipSC:
  IntuitionisticPropositionalSequentCalculus L GammaD.
Proof.
  pose proof Axiomatization2SequentCalculus_SC.
  pose proof Axiomatization2SequentCalculus_bSC.
  pose proof Axiomatization2SequentCalculus_minSC.
  constructor; intros.
  + apply deduction_modus_ponens with y; auto.
    apply deduction_modus_ponens with x; auto.
    apply deduction_weaken0.
    apply andp_intros.
  + apply deduction_modus_ponens with (x && y); auto.
    apply deduction_weaken0.
    apply andp_elim1.
  + apply deduction_modus_ponens with (x && y); auto.
    apply deduction_weaken0.
    apply andp_elim2.
  + apply deduction_modus_ponens with x; auto.
    apply deduction_weaken0.
    apply orp_intros1.
  + apply deduction_modus_ponens with y; auto.
    apply deduction_weaken0.
    apply orp_intros2.
  + rewrite deduction_theorem in H2, H3 |- *.
    apply deduction_modus_ponens with (y --> z); auto.
    apply deduction_modus_ponens with (x --> z); auto.
    apply deduction_weaken0.
    apply orp_elim.
  + apply deduction_modus_ponens with FF; auto.
    apply deduction_weaken0.
    apply falsep_elim.
Qed.

End Axiomatization2SequentCalculus.

Instance reg_Axiomatization2SequentCalculus_ipSC:
  RegisterClass P2D_reg (fun ipSC: unit => @Axiomatization2SequentCalculus_ipSC) 4.
Qed.

Section DerivableRulesFromAxiomatization1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}.

Lemma solve_andp_intros: forall x y: expr,
  |-- x -> |-- y -> |-- x && y.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable in H, H0 |- *.
  apply deduction_andp_intros; auto.
Qed.

Lemma solve_andp_elim1: forall x y: expr,
  |-- x && y -> |-- x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable in H |- *.
  eapply deduction_andp_elim1; eauto.
Qed.

Lemma solve_andp_elim2: forall x y: expr,
  |-- x && y -> |-- y.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable in H |- *.
  eapply deduction_andp_elim2; eauto.
Qed.

Lemma solve_impp_elim_left: forall x y: expr,
  |-- y -> |-- x --> y.
Proof.
  intros.
  eapply modus_ponens.
  + apply axiom1.
  + auto.
Qed.

Lemma solve_orp_impp: forall x y z: expr,
  |-- x --> z -> |-- y --> z -> |-- x || y --> z.
Proof.
  intros.
  eapply modus_ponens; [| exact H0].
  eapply modus_ponens; [| exact H].
  apply orp_elim.
Qed.

Lemma solve_orp_intros1: forall x y: expr,
  |-- x -> |-- x || y.
Proof.
  intros.
  eapply modus_ponens; [| exact H].
  apply orp_intros1.
Qed.

Lemma solve_orp_intros2: forall x y: expr,
  |-- y -> |-- x || y.
Proof.
  intros.
  eapply modus_ponens; [| exact H].
  apply orp_intros2.
Qed.

Lemma solve_impp_andp: forall x y z: expr,
  |-- x --> y -> |-- x --> z -> |-- x --> y && z.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable in H, H0 |- *.
  rewrite <- deduction_theorem in H, H0 |- *.
  apply deduction_andp_intros; auto.
Qed.

Lemma double_negp_intros: forall (x: expr),
  |-- x --> ~~ ~~ x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply derivable_double_negp_intros.
Qed.

Lemma provable_iffp_refl: forall (x: expr),
  |-- x <--> x.
Proof.
  AddSequentCalculus.
  intros.
  apply solve_andp_intros;
  apply provable_impp_refl.
Qed.

Lemma contrapositivePP: forall (x y: expr),
  |-- (y --> x) --> ~~ x --> ~~ y.
Proof.
  intros.
  eapply modus_ponens; [apply provable_impp_arg_switch |].
  apply aux_minimun_theorem00.
Qed.

Lemma contrapositivePN: forall (x y: expr),
  |-- (y --> ~~ x) --> (x --> ~~ y).
Proof.
  intros.
  apply provable_impp_arg_switch.
Qed.

End DerivableRulesFromAxiomatization1.

Section DerivableRulesFromSequentCalculus2.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: Derivable L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimumSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}.

Lemma deduction_contrapositivePP: forall Phi (x y: expr),
  Phi |-- y --> x ->
  Phi |-- ~~ x --> ~~ y.
Proof.
  AddAxiomatization.
  intros.
  eapply deduction_modus_ponens; eauto.
  apply deduction_weaken0.
  apply contrapositivePP.
Qed.

Lemma deduction_contrapositivePN: forall Phi (x y: expr),
  Phi |-- y --> ~~ x ->
  Phi |-- x --> ~~ y.
Proof.
  AddAxiomatization.
  intros.
  eapply deduction_modus_ponens; eauto.
  apply deduction_weaken0.
  apply contrapositivePN.
Qed.

End DerivableRulesFromSequentCalculus2.

Section DerivableRulesFromAxiomatization2.

Context {L: Language}
        {minL: MinimumLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}.

Lemma demorgan_orp_negp: forall (x y: expr),
  |-- ~~ x || ~~ y --> ~~ (x && y).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  unfold negp at 3.
  rewrite <- !deduction_theorem.
  apply (deduction_modus_ponens _ (~~ x || ~~ y)).
  + apply deduction_weaken1.
    apply derivable_assum1.
  + apply deduction_orp_elim'.
    - rewrite <- deduction_theorem.
      apply (deduction_modus_ponens _ x); [| apply derivable_assum1].
      apply deduction_weaken1.
      eapply deduction_andp_elim1.
      apply derivable_assum1.
    - rewrite <- deduction_theorem.
      apply (deduction_modus_ponens _ y); [| apply derivable_assum1].
      apply deduction_weaken1.
      eapply deduction_andp_elim2.
      apply derivable_assum1.
Qed.

Lemma demorgan_negp_orp: forall (x y: expr),
  |-- ~~ (x || y) <--> (~~ x && ~~ y).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros. 
    - rewrite deduction_theorem.
      apply deduction_contrapositivePP.
      rewrite <- provable_derivable.
      apply orp_intros1.
    - rewrite deduction_theorem.
      apply deduction_contrapositivePP.
      rewrite <- provable_derivable.
      apply orp_intros2.
  + rewrite <- deduction_theorem.
    apply deduction_orp_elim'.
    - eapply deduction_andp_elim1.
      apply derivable_assum1.
    - eapply deduction_andp_elim2.
      apply derivable_assum1.
Qed.

Lemma provable_truep: |-- TT.
Proof.
  apply provable_impp_refl.
Qed.

Lemma andp_comm: forall (x y: expr),
  |-- x && y <--> y && x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros.
    - eapply deduction_andp_elim2.
      apply derivable_assum1.
    - eapply deduction_andp_elim1.
      apply derivable_assum1.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros.
    - eapply deduction_andp_elim2.
      apply derivable_assum1.
    - eapply deduction_andp_elim1.
      apply derivable_assum1.
Qed.

Lemma andp_assoc: forall (x y z: expr),
  |-- x && y && z <--> x && (y && z).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros; [| apply deduction_andp_intros].
    - eapply deduction_andp_elim1.
      eapply deduction_andp_elim1.
      apply derivable_assum1.
    - eapply deduction_andp_elim2.
      eapply deduction_andp_elim1.
      apply derivable_assum1.
    - eapply deduction_andp_elim2.
      apply derivable_assum1.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros; [apply deduction_andp_intros |].
    - eapply deduction_andp_elim1.
      apply derivable_assum1.
    - eapply deduction_andp_elim1.
      eapply deduction_andp_elim2.
      apply derivable_assum1.
    - eapply deduction_andp_elim2.
      eapply deduction_andp_elim2.
      apply derivable_assum1.
Qed.

Lemma orp_comm: forall (x y: expr),
  |-- x || y <--> y || x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply deduction_orp_elim'; rewrite <- provable_derivable.
    - apply orp_intros2.
    - apply orp_intros1.
  + apply deduction_orp_elim'; rewrite <- provable_derivable.
    - apply orp_intros2.
    - apply orp_intros1.
Qed.

Lemma orp_assoc: forall (x y z: expr),
  |-- x || y || z <--> x || (y || z).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply deduction_orp_elim'; [apply deduction_orp_elim' |]; rewrite <- deduction_theorem.
    - apply deduction_orp_intros1.
      apply derivable_assum1.
    - apply deduction_orp_intros2.
      apply deduction_orp_intros1.
      apply derivable_assum1.
    - apply deduction_orp_intros2.
      apply deduction_orp_intros2.
      apply derivable_assum1.
  + apply deduction_orp_elim'; [| apply deduction_orp_elim']; rewrite <- deduction_theorem.
    - apply deduction_orp_intros1.
      apply deduction_orp_intros1.
      apply derivable_assum1.
    - apply deduction_orp_intros1.
      apply deduction_orp_intros2.
      apply derivable_assum1.
    - apply deduction_orp_intros2.
      apply derivable_assum1.
Qed.

Lemma andp_truep: forall (x: expr),
  |-- x && TT <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply derivable_andp_elim1.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros.
    - apply derivable_assum1.
    - apply derivable_impp_refl.
Qed.

Lemma truep_andp: forall (x: expr),
  |-- TT && x <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply derivable_andp_elim2.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros.
    - apply derivable_impp_refl.
    - apply derivable_assum1.
Qed.

Lemma falsep_orp: forall (x: expr),
  |-- FF || x <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply deduction_orp_elim'.
    - apply derivable_falsep_elim.
    - apply derivable_impp_refl.
  + apply derivable_orp_intros2.
Qed.

Lemma orp_falsep: forall (x: expr),
  |-- x || FF <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply deduction_orp_elim'.
    - apply derivable_impp_refl.
    - apply derivable_falsep_elim.
  + apply derivable_orp_intros1.
Qed.

Lemma truep_impp: forall (x: expr),
  |-- (TT --> x) <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + rewrite <- deduction_theorem.
    apply deduction_modus_ponens with TT.
    - apply deduction_weaken0.
      apply provable_truep.
    - solve_assum.
  + apply derivable_axiom1.
Qed.

Lemma andp_dup: forall (x: expr),
  |-- x && x <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply derivable_andp_elim1.
  + rewrite <- deduction_theorem.
    apply deduction_andp_intros; apply derivable_assum1.
Qed.

Lemma orp_dup: forall (x: expr),
  |-- x || x <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_andp_intros.
  + apply deduction_orp_elim'; apply derivable_impp_refl.
  + apply derivable_orp_intros1.
Qed.

Lemma impp_curry: forall (x y z: expr),
  |-- (x --> y --> z) --> (x && y --> z).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  rewrite <- !deduction_theorem.
  apply deduction_modus_ponens with y.
  + apply deduction_andp_elim2 with x.
    solve_assum.
  + apply deduction_modus_ponens with x.
    - apply deduction_andp_elim1 with y.
      solve_assum.
    - solve_assum.
Qed.

Lemma impp_uncurry: forall (x y z: expr),
  |-- (x && y --> z) --> (x --> y --> z).
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  rewrite <- !deduction_theorem.
  apply deduction_modus_ponens with (x && y).
  + apply deduction_andp_intros;
    solve_assum.
  + solve_assum.
Qed.

Lemma impp_curry_uncurry: forall (x y z: expr),
  |-- (x --> y --> z) <--> (x && y --> z).
Proof.
  AddSequentCalculus.
  intros.
  apply solve_andp_intros.
  + apply impp_curry.
  + apply impp_uncurry.
Qed.

End DerivableRulesFromAxiomatization2.

