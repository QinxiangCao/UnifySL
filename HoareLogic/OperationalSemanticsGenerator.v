Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.NatChoice.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.SimpleSmallStepSemantics.
Require Import Logic.HoareLogic.SmallStepSemantics.
Require Import Logic.HoareLogic.BigStepSemantics.

Instance SSS_SimpleSSS {P: ProgrammingLanguage} {state: Type} (SSSS: SimpleSmallStepSemantics P state): SmallStepSemantics P state.
Proof.
  refine (Build_SmallStepSemantics _ _ SimpleSmallStepSemantics.step _).
  intros.
  destruct (classic (exists cs0, simple_step cs cs0)).
  + destruct H as [cs0 ?].
    exists (Terminating cs0).
    auto.
  + exists Error.
    simpl.
    intros ? ?; apply H; clear H.
    exists cs0; auto.
Defined.

Instance BSS_SSS {P: ProgrammingLanguage} {Imp: ImperativeProgrammingLanguage P} {state: Type} (SSS: SmallStepSemantics P state): BigStepSemantics P state.
Proof.
  refine (Build_BigStepSemantics _ _ SmallStepSemantics.access _).
  intros.
  apply NNPP; intro.
  pose proof not_ex_all_not _ _ H.
  pose proof H0 Error.
  pose proof H0 NonTerminating.
  pose proof (fun s => H0 (Terminating s)).
  clear H H0.
  simpl in H1, H2, H3.
  apply not_or_and in H2; destruct H2.
  apply H0.
  split; auto.
  apply (nat_coinduction
          (fun cs => clos_refl_trans _ lift_step
                       (Terminating (c, s)) (Terminating cs))
          (fun cs1 cs2 => step cs1 (Terminating cs2))).
  + apply rt_refl.
  + intros [c0 s0] ?.
    destruct (step_defined (c0, s0)) as [mcs ?].
    destruct mcs as [| | [c1 s1]].
    - exfalso; apply H1.
      left.
      apply rt_trans with (Terminating (c0, s0)); auto.
      apply rt_step.
      constructor; auto.
    - exfalso; apply H.
      apply rt_trans with (Terminating (c0, s0)); auto.
      apply rt_step.
      constructor; auto.
    - exists (c1, s1).
      split; auto.
      apply rt_trans with (Terminating (c0, s0)); auto.
      apply rt_step.
      constructor; auto.
Defined.

Module Partial.

Export SmallStepSemantics.Partial.
Export BigStepSemantics.Partial.

Instance iBSS_SSS {P: ProgrammingLanguage} {iP: ImperativeProgrammingLanguage P} {niP: NormalImperativeProgrammingLanguage P} {state: Type} {kiM: KripkeIntuitionisticModel state} (SSS: SmallStepSemantics P state) {iSSS: ImpSmallStepSemantics P state SSS}: ImpBigStepSemantics P state (BSS_SSS SSS).
Proof.
  refine (Build_ImpBigStepSemantics _ _ _ _ _ _ eval_bool_stable _ _ _).
  + simpl; intros.
    destruct H.
    - assert (
        exists ms' ms'',
        clos_refl_trans _ lift_step (Terminating (c1, s)) (lift_function (pair Sskip) ms') /\
        decrease ms' ms'' /\
        clos_refl_trans _ lift_step (lift_function (pair c2) ms'') (lift_function (pair Sskip) ms)).
      Focus 2. {
        destruct H0 as [ms' [ms'' [? [? ?]]]]; exists ms', ms''.
        split; [| split]; auto.
        + left; auto.
        + pose proof clos_refl_trans_lift_relation_forward _ _ _ H2.
          pose proof lift_function_rev _ _ _ (@eq_refl _ (lift_function (pair Sskip) ms)).
          destruct ms''; simpl in H3; try rewrite H3 in H4.
          - subst; constructor.
          - subst; constructor.
          - clear H3 H4; constructor.
            left; auto.
      } Unfocus.
      remember (Terminating (Ssequence c1 c2, s)) eqn:?H.
      remember (lift_function (pair Sskip) ms) eqn:?H.
      rewrite clos_rt_rt1n_iff in H.
      revert c1 s H0 H1; induction H; intros.
      * exfalso.
        subst.
        destruct ms; inversion H1; subst.
        apply Ssequence_Sskip in H0; auto.
      * subst; inversion H; subst; clear H.
        pose proof step_Ssequence _ _ _ _ H2.
        destruct H as [? | ?].
       ++ destruct H as [ms' [? [? ?]]].
          exists (Terminating s), ms'.
          subst c1.
          split; [| split]; auto.
         -- apply rt_refl.
         -- subst.
            rewrite clos_rt_rt1n_iff; auto.
       ++ destruct H as [ms' [? ?]].
          destruct ms' as [| | [c' s']].
         -- exists Error, Error.
            split; [| split].
           ** apply rt_step; constructor; auto.
           ** constructor.
           ** subst.
              rewrite clos_rt_rt1n_iff; auto.
         -- exists NonTerminating, NonTerminating.
            split; [| split].
           ** apply rt_step; constructor; auto.
           ** constructor.
           ** subst.
              rewrite clos_rt_rt1n_iff; auto.
         -- destruct (IHclos_refl_trans_1n c' s') as [ms' [ms'' [? [? ?]]]]; auto.
            exists ms', ms''.
            split; [| split]; auto.
            rewrite clos_rt_rt1n_iff.
            apply (@Relation_Operators.rt1n_trans _ _ _ (Terminating (c', s'))).
           ** constructor; auto.
           ** rewrite clos_rt_rt1n_iff in H3; auto.
Abort.


End Partial.