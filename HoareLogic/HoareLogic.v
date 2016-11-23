Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.HoareLogic.ImperativeLanguage.

Class HoareLogic (Imp: ImperativeProgrammingLanguage) (L: Language): Type := {
  triple: expr -> cmd -> expr -> Prop
}.

Local Open Scope logic_base.

Definition triple_valid {Imp: ImperativeProgrammingLanguage} {nImp: NormalImperativeProgrammingLanguage Imp} {L: Language} {MD: Model} {sss: SmallStepSemantics Imp MD} {SM: Semantics L MD} (guard: exceptional_state -> Prop) (Pre: expr) (c: cmd) (Post: expr): Prop :=
  (forall (s_pre: state) (s_post: exceptional_state), access (inl (c, s_pre)) (inr s_post) -> s_pre |= Pre -> guard s_post) /\
  (forall (s_pre: state) (s_post: state), access (inl (c, s_pre)) (inl (Sskip, s_post)) -> s_pre |= Pre -> s_post |= Post).

Section soundness.

Context {Imp: ImperativeProgrammingLanguage} {nImp: NormalImperativeProgrammingLanguage Imp} {L: Language} {MD: Model} {sss: SmallStepSemantics Imp MD} {SM: Semantics L MD} (guard: exceptional_state -> Prop).

Lemma hoare_sequence_sound: forall c1 c2 P Q R,
  triple_valid guard P c1 Q ->
  triple_valid guard Q c2 R ->
  triple_valid guard P (Ssequence c1 c2) R.
Proof.
  intros.
  split; intros.
  + remember (inl (Ssequence c1 c2, s_pre)) as mcs1 eqn:?H.
    remember (inr s_post) as mcs2 eqn:?H.
    revert c1 H H3.
    induction H1; intros; subst.
    - inversion H3.
    - inversion H3; subst; clear H3.
Abort.

End soundness.