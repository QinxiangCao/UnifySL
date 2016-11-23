Require Import Logic.MinimunLogic.LogicBase.

Class ImperativeProgrammingLanguage: Type := {
  cmd: Type
}.

Class NormalImperativeProgrammingLanguage (Imp: ImperativeProgrammingLanguage): Type := {
  Ssequence: cmd -> cmd -> cmd;
  Sskip: cmd;
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

Inductive access {Imp: ImperativeProgrammingLanguage} {nImp: NormalImperativeProgrammingLanguage Imp} {MD: Model} {sss: SmallStepSemantics Imp MD}: cmd * state + exceptional_state -> cmd * state + exceptional_state -> Prop :=
| access_refl: forall mcs, access mcs mcs
| access_step: forall cs mcs, step cs mcs -> access (inl cs) mcs
| access_trans: forall mcs1 mcs2 mcs3, access mcs1 mcs2 -> access mcs2 mcs3 -> access mcs1 mcs3.
