Require Import Coq.Relations.Relation_Operators.
Require Import Logic.lib.Stream.SigStream.
Require Import Logic.lib.Stream.StreamFunctions.
Require Import Coq.Relations.Relation_Operators.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.Trace.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Class SmallStepSemantics_cmd (P: ProgrammingLanguage) (state: Type): Type := {
  step_cmd: cmd * state -> MetaState (cmd * state) -> Prop
}.

Definition step_cmd_safe
           {P: ProgrammingLanguage}
           (state: Type)
           {SSS: SmallStepSemantics_cmd P state}
           (cs: cmd * state):
  Prop :=
  ~ step_cmd cs Error.

Definition step_cmd_term_norm
           {P: ProgrammingLanguage}
           {state: Type}
           {SSS: SmallStepSemantics_cmd P state}
           (cs: cmd * state):
  Prop :=
  ~ step_cmd cs Error /\ ~ step_cmd cs NonTerminating.

Inductive lift_step_term {P: ProgrammingLanguage} {CS: ControlStack} {Cont: Continuation P CS} {state: Type} (step': (cont * state) -> (cont * state) -> Prop) : (cont * state) -> MetaState (cont * state) -> Prop :=
| lift_term: forall cs1 cs2, step' cs1 cs2 -> lift_step_term step' cs1 (Terminating cs2)
.

Class SmallStepSemantics {P: ProgrammingLanguage} {CS: ControlStack} (Cont: Continuation P CS) (state: Type): Type := {
  step: cont * state -> MetaState (cont * state) -> Prop;
  zerostep: cont -> cont -> Prop;
}.

Definition step_safe
           {P: ProgrammingLanguage}
           {CS: ControlStack}
           {Cont: Continuation P CS}
           {state: Type}
           {SSS: SmallStepSemantics Cont state}
           (cs: cont * state):
  Prop :=
  ~ step cs Error.

Definition step_term_norm
           {P: ProgrammingLanguage}
           {CS: ControlStack}
           {Cont: Continuation P CS}
           {state: Type}
           {SSS: SmallStepSemantics Cont state}
           (cs: cont * state):
  Prop :=
  ~ step cs Error /\ ~ step cs NonTerminating.

Class SASmallStepSemantics {P: ProgrammingLanguage} {CS: ControlStack} {Cont: Continuation P CS} {state: Type} {J: Join state} {state_R: Relation state} (SSS: SmallStepSemantics Cont state): Type := {
  frame_property: forall (m mf m': cont * state) n', join (snd m) (snd mf) (snd m') -> step_safe m -> step m' n' -> exists n nf, snd nf <= snd mf /\ @lift_join _ (@prod_Join cont state (equiv_Join) J) n (Terminating nf) n' /\ step m n
}.

(*
Record denote
       {P: ProgrammingLanguage}
       {state: Type}
       {SSS: SmallStepSemantics P state}
       (c: cmd)
       (tr: trace state): Prop :=
{
  ctr: trace (cmd * state);
  ctr_sequential: sequential_trace ctr;
  ctr_sound: sound_trace step ctr;
  s: state;
  mcs: MetaState (cmd * state);
  ctr_begin_end_state: begin_end_state (c, s) ctr mcs;
  end_state_valid: match mcs with
                   | NonTerminating => True
                   | Error => True
                   | Terminating (c', s') => forall mcs'', ~ step (c', s') mcs''
                   end;
  tr_ctr: tr = ctrace2trace ctr
}.
*)

Definition access {P: ProgrammingLanguage} {CS: ControlStack} {Cont: Continuation P CS} {state: Type} {SSS: SmallStepSemantics Cont state} (s: state) (c: cont) (ms: MetaState state) :=
  clos_refl_trans _ (lift_relation step) (Terminating (c, s)) (lift_function (pair (Creturn empty_stack)) ms) \/
  ms = NonTerminating /\ exists cs: nat -> cont * state, cs 0 = (c, s) /\ forall k, step (cs k) (Terminating (cs (S k))).

Module ImpSmallStepSemantics (D: FORWARD).

Export D.

(*
Class ImpSmallStepSemantics (P: ProgrammingLanguage) {iP: ImperativeProgrammingLanguage P} (state: Type) {state_R: Relation state} (SSS: SmallStepSemantics P state): Type := {
  eval_bool: state -> bool_expr -> Prop;
  eval_bool_stable: forall b, Krelation_stable_Kdenote (fun s => eval_bool s b);
  step_defined: forall c s, c <> Sskip -> exists mcs, step (c, s) mcs;
  step_Sskip: forall s mcs, step (Sskip, s) mcs <-> False;
  step_Ssequence: forall c1 c2 s mcs,
    step (Ssequence c1 c2, s) mcs ->
    (exists ms', c1 = Sskip /\ forward (Terminating s) ms' /\ mcs = lift_function (pair c2) ms') \/
    (exists mcs', step (c1, s) mcs' /\ mcs = lift_function (fun cs => (Ssequence (fst cs) c2, snd cs)) mcs');
  step_Sifthenelse: forall b c1 c2 s mcs,
    step (Sifthenelse b c1 c2, s) mcs ->
    (eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair c1) ms') \/
    (~ eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair c2) ms');
  step_Swhile: forall b c s mcs,
    step (Swhile b c, s) mcs ->
    (eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair (Ssequence c (Swhile b c))) ms') \/
    (~ eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair Sskip) ms')
}.
*)

Class ImpSmallStepSemantics
      {P: ProgrammingLanguage} {iP: ImperativeProgrammingLanguage P}
      {CS: ControlStack} {lCS: LinearControlStack CS}
      {Cont: Continuation P CS} {iCont: ImperativeProgrammingLanguageContinuation Cont}
      {state: Type} {state_R: Relation state}
      (SSS: SmallStepSemantics Cont state): Type := {
  eval_bool: state -> bool_expr -> Prop;
  eval_bool_stable: forall b, Krelation_stable_Kdenote (fun s => eval_bool s b);
  zerostep_spec: forall c1 c2 s,
      zerostep c1 c2 ->
      step (c1, s) (Terminating (c2, s)) \/ forall mcs, step (c2, s) mcs -> step (c1, s) mcs;
  step_defined: forall c s, ~ zerostep c (Creturn empty_stack) -> exists mcs, step (c, s) mcs;
  zerostep_Ceval_Sskip: forall cs,
      zerostep (Ceval Sskip cs) (Creturn cs);
  step_Ceval_Sskip_emptystack: forall s mcs,
      step (Ceval Sskip empty_stack, s) mcs <-> False;
  zerostep_Ceval_Ssequence: forall c1 c2 cs,
      zerostep (Ceval (Ssequence c1 c2) cs)  (Ceval c1 (cons (Fsequence c2) cs));
  step_Ceval_Sifthenelse: forall b c1 c2 cs s mcs,
      step (Ceval (Sifthenelse b c1 c2) cs, s) mcs ->
      (eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair (Ceval c1 cs)) ms') \/
      (~ eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair (Ceval c2 cs)) ms');
  step_Ceval_Swhile: forall b c cs s mcs,
      step (Ceval (Swhile b c) cs, s) mcs -> mcs = (Terminating (Creturn (cons (Fwhile b c) cs), s));
  zerostep_Creturn_Fsequence: forall c cs,
      zerostep (Creturn (cons (Fsequence c) cs)) (Ceval c cs);
  step_Creturn_Fwhile: forall b c cs s mcs,
      step (Creturn (cons (Fwhile b c) cs), s) mcs ->
      (eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair (Ceval c (cons (Fwhile b c) cs))) ms') \/
      (~ eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair (Creturn cs)) ms');
}.

Class ImpSmallStepSemantics_SbreakScontinue
      {P: ProgrammingLanguage} {iP: ImperativeProgrammingLanguage P} {iP_bc: ImperativeProgrammingLanguage_SbreakScontinue P}
      {CS: ControlStack} {lCS: LinearControlStack CS}
      {Cont: Continuation P CS} {iCont: ImperativeProgrammingLanguageContinuation Cont} {iCont_bc: ImperativeProgrammingLanguageContinuation_CbreakCcontinue Cont}
      {state: Type} {state_R: Relation state}
      (SSS: SmallStepSemantics Cont state) {iSSS: ImpSmallStepSemantics SSS}: Type := {
  step_Cbreak_Fsequence: forall c cs s mcs,
    step (Cbreak (cons (Fsequence c) cs), s) mcs ->
    mcs = Terminating (Cbreak cs, s);
  step_Cbreak_Fwhile: forall b c cs s mcs,
    step (Cbreak (cons (Fwhile b c) cs), s) mcs ->
    mcs = Terminating (Creturn cs, s);
  step_Ccontinue_Fsequence: forall c cs s mcs,
    step (Ccontinue (cons (Fsequence c) cs), s) mcs ->
    mcs = Terminating (Ccontinue cs, s);
  step_Ccontinue_Fwhile: forall b c cs s mcs,
    step (Ccontinue (cons (Fwhile b c) cs), s) mcs ->
    (eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair (Ceval c (cons (Fwhile b c) cs))) ms') \/
    (~ eval_bool s b /\ exists ms', forward (Terminating s) ms' /\ mcs = lift_function (pair (Creturn cs)) ms');
}.

End ImpSmallStepSemantics.

Module Partial := ImpSmallStepSemantics (ProgramState.Partial).

Module Total := ImpSmallStepSemantics (ProgramState.Total).

(*
Instance Total2Partial_ImpSmallStepSemantics {P: ProgrammingLanguage} {iP: ImperativeProgrammingLanguage P} (state: Type) {state_R: Relation state} {SSS: SmallStepSemantics P state} (iSSS: Total.ImpSmallStepSemantics P state SSS): Partial.ImpSmallStepSemantics P state SSS.
Proof.
  refine (Partial.Build_ImpSmallStepSemantics _ _ _ _ _ Total.eval_bool Total.eval_bool_stable _ _ _ _ _).
  + apply Total.step_defined.
  + apply Total.step_Sskip.
  + intros.
    pose proof Total.step_Ssequence c1 c2 s mcs H
      as [[ms' [? [? ?]]] | [ms' [? ?]]].
    - left; exists ms'; split; [| split]; auto.
      apply Total2Partial_forward; auto.
    - right; exists ms'; auto.
  + intros.
    pose proof Total.step_Sifthenelse b c1 c2 s mcs H
      as [[? [ms' [? ?]]] | [? [ms' [? ?]]]].
    - left; split; auto.
      exists ms'; split; auto.
      apply Total2Partial_forward; auto.
    - right; split; auto.
      exists ms'; split; auto.
      apply Total2Partial_forward; auto.
  + intros.
    pose proof Total.step_Swhile b c s mcs H
      as [[? [ms' [? ?]]] | [? [ms' [? ?]]]].
    - left; split; auto.
      exists ms'; split; auto.
      apply Total2Partial_forward; auto.
    - right; split; auto.
      exists ms'; split; auto.
      apply Total2Partial_forward; auto.
Qed.
*)

(*
Instance Total2Partial_ImpSmallStepSemantics {P: ProgrammingLanguage} {iP: ImperativeProgrammingLanguage P} {CS: ControlStack} {lCS: LinearControlStack CS} {Cont: Continuation P CS} {iCont: ImperativeProgrammingLanguageContinuation Cont} (state: Type) {state_R: Relation state} {SSS: SmallStepSemantics Cont state} (iSSS: Total.ImpSmallStepSemantics SSS): Partial.ImpSmallStepSemantics SSS.
Proof.
  refine (Partial.Build_ImpSmallStepSemantics _ _ _ _ _ _ _ _ _ Total.eval_bool Total.eval_bool_stable _ _ _ _ _ _ _).
  + apply Total.step_Ceval_Sskip.
  + apply Total.step_Ceval_Sskip_emptystack.
  + apply Total.step_Ceval_Ssequence.
  + intros.
    pose proof Total.step_Ceval_Sifthenelse b c1 c2 cs s mcs H
      as [[? [ms' [? ?]]] | [? [ms' [? ?]]]].
    - left; split; auto.
      exists ms'; split; auto.
      apply Total2Partial_forward; auto.
    - right; split; auto.
      exists ms'; split; auto.
      apply Total2Partial_forward; auto.
  + apply Total.step_Ceval_Swhile.
  + apply Total.step_Creturn_Fsequence.
  + intros.
    pose proof Total.step_Creturn_Fwhile b c cs s mcs H
      as [[? [ms' [? ?]]] | [? [ms' [? ?]]]].
    - left; split; auto.
      exists ms'; split; auto.
      apply Total2Partial_forward; auto.
    - right; split; auto.
      exists ms'; split; auto.
      apply Total2Partial_forward; auto.
Qed.
*)