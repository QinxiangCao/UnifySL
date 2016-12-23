Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.NatChoice.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.HoareLogic.ImperativeLanguage.

Inductive MetaState (state: Type): Type :=
  | Error: MetaState state
  | NonTerminating: MetaState state
  | Terminating: state -> MetaState state.

Arguments Error {_}.
Arguments NonTerminating {_}.
Arguments Terminating {_} _.

Inductive lift_relation {state: Type} (R: state -> MetaState state -> Prop):
  MetaState state-> MetaState state -> Prop :=
| lift_relation_Error:
    lift_relation R Error Error
| lift_relation_NonTerminating:
    lift_relation R NonTerminating NonTerminating
| lift_relation_Terminating:
    forall s ms, R s ms -> lift_relation R (Terminating s) ms.

Inductive lift_Korder
          {state: Type}
          {ki_state: KripkeIntuitionisticModel state}:
  MetaState state -> MetaState state -> Prop :=
| lift_Korder_Error:
    lift_Korder Error Error
| lift_Korder_NonTerminating:
    lift_Korder NonTerminating NonTerminating
| lift_Korder_Terminating:
    forall x y, Korder x y -> lift_Korder (Terminating x) (Terminating y).

Inductive lift_join
          {state: Type}
          {J_state: Join state}:
  MetaState state -> MetaState state -> MetaState state -> Prop :=
| lift_join_Error1:
    forall mx my, lift_join Error mx my
| lift_join_Error2:
    forall mx my, lift_join mx Error my
| lift_join_NonTerminating1:
    forall x, lift_join NonTerminating (Terminating x) NonTerminating
| lift_join_NonTerminating2:
    forall x, lift_join (Terminating x) NonTerminating NonTerminating
| lift_join_NonTerminating3:
    lift_join NonTerminating NonTerminating NonTerminating
| lift_join_Terminating:
    forall x y z,
      join x y z ->
      lift_join (Terminating x) (Terminating y) (Terminating z).

(*
Instance MetaState_SA (state: Type) {SA: SeparationAlgebra state}: SeparationAlgebra (MetaState state).
*)

Class BigStepSemantics (P: ProgrammingLanguage) (state: Type): Type := {
  access: state -> cmd -> MetaState state -> Prop
}.

Class SmallStepSemantics (P: ProgrammingLanguage) (state: Type): Type := {
  step: cmd * state -> MetaState (cmd * state) -> Prop
}.

Class SimpleSmallStepSemantics (P: ProgrammingLanguage) (state: Type): Type := {
  simple_step: cmd * state -> cmd * state -> Prop
}.

Definition lift_access
          {P: ProgrammingLanguage}
          {state: Type}
          {BSS: BigStepSemantics P state}
          (ms1: MetaState state)
          (c: cmd)
          (ms2: MetaState state): Prop :=
  lift_relation (fun s => access s c) ms1 ms2.

Definition lift_step
          {P: ProgrammingLanguage}
          {state: Type}
          {SSS: SmallStepSemantics P state}
          (mcs1: MetaState (cmd * state))
          (mcs2: MetaState (cmd * state)): Prop :=
  lift_relation (fun cs => step cs) mcs1 mcs2.

Definition safe
           {P: ProgrammingLanguage}
           {state: Type}
           {BSS: BigStepSemantics P state}
           (s: state)
           (c: cmd):
  Prop :=
  ~ access s c Error.

Definition term_norm
           {P: ProgrammingLanguage}
           {state: Type}
           {BSS: BigStepSemantics P state}
           (s: state)
           (c: cmd):
  Prop :=
  ~ access s c Error /\ ~ access s c NonTerminating.

Class NormalBigStepSemantics (P: ProgrammingLanguage) (state: Type) (BSS: BigStepSemantics P state): Type := {
  access_defined: forall s c, exists ms, access s c ms
}.

Class NormalSmallStepSemantics (P: ProgrammingLanguage) (state: Type) (SSS: SmallStepSemantics P state): Type := {
  step_defined: forall cs, exists mcs, step cs mcs
}.

(****************************************************)
(* Generators                                       *)
(****************************************************)

Definition step' {P: ProgrammingLanguage} {state: Type} {SSSS: SimpleSmallStepSemantics P state} (cs: cmd * state) (mcs: MetaState (cmd * state)) :=
  match mcs with
  | Terminating cs0 => simple_step cs cs0
  | NonTerminating => False
  | Error => forall cs0, ~ simple_step cs cs0
  end.

Instance SSS_SimpleSSS {P: ProgrammingLanguage} {state: Type} (SSSS: SimpleSmallStepSemantics P state): SmallStepSemantics P state :=
  Build_SmallStepSemantics _ _ step'.

Instance nSSS_SimpleSSS {P: ProgrammingLanguage} {state: Type} (SSSS: SimpleSmallStepSemantics P state): NormalSmallStepSemantics P state (SSS_SimpleSSS SSSS).
Proof.
  constructor.
  intros.
  destruct (classic (exists cs0, simple_step cs cs0)).
  + destruct H as [cs0 ?].
    exists (Terminating cs0).
    auto.
  + exists Error.
    simpl.
    intros ? ?; apply H; clear H.
    exists cs0; auto.
Qed.

Definition access' {P: ProgrammingLanguage} {Imp: ImperativeProgrammingLanguage P} {state: Type} {SSS: SmallStepSemantics P state} (s: state) (c: cmd) (ms: MetaState state) :=
  
    match ms with
    | Terminating s0 => clos_refl_trans _ lift_step (Terminating (c, s))  (Terminating (Sskip, s0))
    | NonTerminating => clos_refl_trans _ lift_step (Terminating (c, s)) NonTerminating \/ exists cs: nat -> cmd * state, cs 0 = (c, s) /\ forall k, step (cs k) (Terminating (cs (S k)))
    | Error => clos_refl_trans _ lift_step (Terminating (c, s)) Error
    end.

Instance BSS_SSS {P: ProgrammingLanguage} {Imp: ImperativeProgrammingLanguage P} {state: Type} (SSS: SmallStepSemantics P state): BigStepSemantics P state :=
  Build_BigStepSemantics _ _ access'.

Instance nBSS_SSS {P: ProgrammingLanguage} {Imp: ImperativeProgrammingLanguage P} {state: Type} (SSS: SmallStepSemantics P state) {nSSS: NormalSmallStepSemantics P state SSS}: NormalBigStepSemantics P state (BSS_SSS SSS).
Proof.
  constructor.
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
  apply (nat_coinduction
          (fun cs => clos_refl_trans _ lift_step
                       (Terminating (c, s)) (Terminating cs))
          (fun cs1 cs2 => step cs1 (Terminating cs2))).
  + apply rt_refl.
  + intros [c0 s0] ?.
    destruct (step_defined (c0, s0)) as [mcs ?].
    destruct mcs as [| | [c1 s1]].
    - exfalso; apply H1.
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
Qed.
