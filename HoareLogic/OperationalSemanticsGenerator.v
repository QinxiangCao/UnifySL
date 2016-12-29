Require Import Coq.omega.Omega.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.NatChoice.
Require Import Logic.lib.Stream.SigStream.
Require Import Logic.lib.Stream.StreamFunctions.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.Trace.
Require Import Logic.HoareLogic.SimpleSmallStepSemantics.
Require Import Logic.HoareLogic.SmallStepSemantics.
Require Import Logic.HoareLogic.LocalTraceSemantics.
Require Import Logic.HoareLogic.BigStepSemantics.

Instance SSS_SimpleSSS
         {P: ProgrammingLanguage}
         {state: Type}
         (SSSS: SimpleSmallStepSemantics P state)
         (final_state: cmd * state -> Prop):
  SmallStepSemantics P state :=
  Build_SmallStepSemantics _ _ (SimpleSmallStepSemantics.step final_state).

Instance LTS_SSS
         {P: ProgrammingLanguage}
         {iP: ImperativeProgrammingLanguage P}
         {state: Type}
         (SSS: SmallStepSemantics P state):
  LocalTraceSemantics P state.
Proof.
  refine (Build_LocalTraceSemantics _ _ SmallStepSemantics.denote _ _).
  + intros.
    destruct (classic (exists mcs, step (c, s) mcs)).
    - destruct H as [mcs ?].
      pose (Q := fun p: option ((cmd * state) *
                                MetaState (cmd * state)) =>
                 match p with
                 | Some (cs, mcs) => step cs mcs
                 | None => True
                 end).
      pose (R := fun p1 p2: option ((cmd * state) *
                                    MetaState (cmd * state)) =>
                   match p1, p2 with
                   | None, Some _ => False
                   | None, None => True
                   | Some (_, Error), None => True
                   | Some (_, NonTerminating), None => True
                   | Some (_, Terminating cs), None => ~ exists mcs, step cs mcs
                   | Some (_, mcs), Some (cs, _) => mcs = Terminating cs
                   end).
      destruct (nat_coinduction' Q R (Some ((c, s), mcs)) H) as [_ctr [? [? ?]]].
      * clear c s mcs H.
        intros [[cs [| | cs']] |] ?.
       ++ exists None; simpl; auto.
       ++ exists None; simpl; auto.
       ++ destruct (classic (exists mcs, step cs' mcs)) as [[mcs ?] | ?].
         -- exists (Some (cs', mcs)); simpl; auto.
         -- exists None; simpl; auto.
       ++ exists None; simpl; auto.
      * assert (forall k1 k2, k1 < k2 -> _ctr k1 = None -> _ctr k2 = None).
        Focus 1. {
          intros.
          assert (k1 <= k2) by omega; clear H3.
          induction H5.
          + auto.
          + specialize (H1 m).
            rewrite IHle in H1; simpl in H1.
            destruct (_ctr (S m)); auto; tauto.
        } Unfocus.
        pose (ctr := exist _ _ctr H3: trace (cmd * state)).
        change _ctr with (stream_get ctr) in H0, H1, H2.
        clearbody ctr; clear _ctr H3.
        exists (stream_map (fun p => match p with ((c, s), mcs) => (s, lift_function snd mcs) end) ctr).
        destruct (n_stream_or_inf_stream ctr) as [[[| k] ?] | ?].
       ++ exfalso; destruct H3 as [? _]; congruence.
       ++ destruct (ctr k) eqn:?H; [| pose proof (proj2 H3 k (le_n _)); congruence].
          destruct p as [cs' mcs'].
          refine (conj (SmallStepSemantics.Build_denote _ _ _ c _ ctr _ _ s mcs' _ _ eq_refl) _).
         -- clear k c s mcs cs' mcs' H0 H H3 H4.
            hnf; intros.
            specialize (H1 k); subst R; simpl in H1.
            rewrite H, H0 in H1.
            destruct ms; tauto.
         -- clear k c s mcs cs' mcs' H0 H H3 H4.
            intros.
            specialize (H2 k); subst Q; simpl in H2.
            rewrite H in H2; auto.
         -- eapply begin_end_fin; eauto.
         -- clear c s mcs H0 H.
            destruct H3 as [? _].
            specialize (H1 k); subst R; simpl in H1.
            rewrite H, H4 in H1.
            destruct mcs'; auto.
            destruct p; firstorder.
         -- destruct cs' as [c' s'].
            exists (lift_function snd mcs'); eapply begin_end_fin.
           ** apply stream_map_n_stream; eauto.
           ** rewrite stream_map_spec, H0.
              reflexivity.
           ** rewrite stream_map_spec, H4.
              reflexivity.
       ++ refine (conj (SmallStepSemantics.Build_denote _ _ _ c _ ctr _ _ s NonTerminating _ _ eq_refl) _).
         -- clear c s mcs H0 H H3.
            hnf; intros.
            specialize (H1 k); subst R; simpl in H1.
            rewrite H, H0 in H1.
            destruct ms; tauto.
         -- clear c s mcs H0 H H3.
            intros.
            specialize (H2 k); subst Q; simpl in H2.
            rewrite H in H2; auto.
         -- eapply begin_end_inf; eauto.
         -- auto.
         -- exists NonTerminating; eapply begin_end_inf.
           ** apply stream_map_inf_stream; eauto.
           ** rewrite stream_map_spec, H0.
              reflexivity.
    - exists empty_stream.
      refine (conj (SmallStepSemantics.Build_denote _ _ _ c empty_stream empty_stream _ _ s (Terminating (c, s)) _ _ _) _).
      * hnf; intros.
        rewrite empty_stream_spec in H0; congruence.
      * intros.
        rewrite empty_stream_spec in H0; congruence.
      * apply begin_end_empty.
      * firstorder.
      * symmetry; apply stream_map_empty_stream.
      * exists (Terminating s).
        apply begin_end_empty.
  + intros.
    destruct H as [? ? _ _ _ _ _ ?].
    hnf; intros.
    rewrite tr_ctr, stream_map_spec in H, H0.
    specialize (ctr_sequential k).
    destruct (ctr k) as [[[c0 s0] mcs] |]; [| congruence].
    inversion H; subst s0 ms; clear H.
    destruct (ctr (S k)) as [[[c'0 s'0] mcs'] |]; [| congruence].
    inversion H0; subst s'0 ms'; clear H0.
    specialize (ctr_sequential _ _ _ _ eq_refl eq_refl).
    subst mcs; auto.
Defined.

Instance BSS_LTS
         {P: ProgrammingLanguage}
         {state: Type}
         (LTS: LocalTraceSemantics P state):
  BigStepSemantics P state.
Proof.
  refine (Build_BigStepSemantics _ _ LocalTraceSemantics.access _).
  intros.
  pose proof denote_defined c s as [tr [? ?]].
  destruct H0 as [ms ?].
  exists ms, tr.
  auto.
Defined.

Module Partial.

Export SmallStepSemantics.Partial.
Export LocalTraceSemantics.Partial.
Export BigStepSemantics.Partial.

Instance iLTS_SSS {P: ProgrammingLanguage} {iP: ImperativeProgrammingLanguage P} {niP: NormalImperativeProgrammingLanguage P} {state: Type} {kiM: KripkeIntuitionisticModel state} (SSS: SmallStepSemantics P state) {iSSS: ImpSmallStepSemantics P state SSS}: ImpLocalTraceSemantics P state (LTS_SSS SSS).
Proof.
  refine (Build_ImpLocalTraceSemantics _ _ _ _ _ _ eval_bool_stable _ _ _ _).
  + intros.
    destruct H as [ctr _ ? ? mcs' ? _ ?].
    inversion ctr_begin_end_state.
    - subst.
      rewrite stream_map_empty_stream.
      apply empty_stream_is_empty.
    - rename ms into mcs.
      subst.
      exfalso.
      pose proof ctr_sound 0 (Sskip, s) mcs H0.
      rewrite step_Sskip in H2; auto.
    - rename ms into mcs.
      subst.
      exfalso.
      pose proof ctr_sound 0 (Sskip, s) mcs H0.
      rewrite step_Sskip in H1; auto.
  + intros.
Abort.

End Partial.