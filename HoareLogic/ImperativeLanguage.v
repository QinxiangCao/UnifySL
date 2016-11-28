Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.SeparationLogic.SeparationAlgebra.

Class ImperativeProgrammingLanguage: Type := {
  cmd: Type
}.

Class BigStepSemantics (Imp: ImperativeProgrammingLanguage) (MD: Model): Type := {
  state := model;
  exceptional_state: Type;
  access: state + exceptional_state -> cmd -> state + exceptional_state -> Prop
}.

(*

Class FrameBigStepSemantics (Imp: ImperativeProgrammingLanguage) (MD: Model) {kMD: KripkeModel MD} {SA: forall M: Kmodel, SeparationAlgebra MD M} (BSS: BigStepSemantics Imp MD): Type := {
  frame_property: forall 
}.
*)
(*
Class NormalImperativeProgrammingLanguage (Imp: ImperativeProgrammingLanguage): Type := {
  Ssequence: cmd -> cmd -> cmd;
  Sskip: cmd;
  neq_Sskip_Ssequence: forall c1 c2, Sskip <> Ssequence c1 c2
}.

Class SmallStepSemantics (Imp: ImperativeProgrammingLanguage) (MD: Model): Type := {
  state := model;
  exceptional_state: Type;
  step: cmd * state -> cmd * state + exceptional_state -> Prop
}.

Definition fmap_sum_left {A1 A2 B: Type} (f: A1 -> A2) (x: A1 + B): A2 + B :=
  match x with
  | inl a => inl (f a)
  | inr b => inr b
  end.

Definition fmap_Sseq {Imp: ImperativeProgrammingLanguage} {nImp: NormalImperativeProgrammingLanguage Imp} {MD: Model} {sss: SmallStepSemantics Imp MD} (mcs: cmd * state + exceptional_state) (c0: cmd) :=
  fmap_sum_left (fun cs: cmd * state => let (c, s) := cs in (Ssequence c c0, s)) mcs.

Definition fmap_pair_cmd {Imp: ImperativeProgrammingLanguage} {nImp: NormalImperativeProgrammingLanguage Imp} {MD: Model} {sss: SmallStepSemantics Imp MD} (ms: state + exceptional_state) (c: cmd) :=
  fmap_sum_left (pair c) ms.

Class NormalSmallStepSemantics (Imp: ImperativeProgrammingLanguage) {nImp: NormalImperativeProgrammingLanguage Imp} (MD: Model) (sss: SmallStepSemantics Imp MD): Type := {
  step_Ssequence1: forall c1 c2 s1 mcs2,
    c2 <> Sskip ->
    ((exists mcs1, step (c1, s1) mcs1 /\ mcs2 = fmap_Sseq mcs1 c2) <->
     step (Ssequence c1 c2, s1) mcs2);
  step_Ssequence2: forall c s mcs,
    step (c, s) mcs <->
    step (Ssequence Sskip c, s) mcs;
  step_progress: forall c s, c = Sskip <-> exists mcs, step (c, s) mcs
}.

Inductive iter_step {Imp: ImperativeProgrammingLanguage} {nImp: NormalImperativeProgrammingLanguage Imp} {MD: Model} {sss: SmallStepSemantics Imp MD}: cmd * state + exceptional_state -> cmd * state + exceptional_state -> Prop :=
| iter_step_refl: forall mcs, iter_step mcs mcs
| iter_step_step: forall cs mcs1 mcs2, step cs mcs1 -> iter_step mcs1 mcs2 -> iter_step (inl cs) mcs2.

Definition access {Imp: ImperativeProgrammingLanguage} {nImp: NormalImperativeProgrammingLanguage Imp} {MD: Model} {sss: SmallStepSemantics Imp MD} (ms_init: state + exceptional_state) (c: cmd) (ms_end: state + exceptional_state): Prop :=
  iter_step (fmap_pair_cmd ms_init c) (fmap_pair_cmd ms_end Sskip).
*)