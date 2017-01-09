Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.SeparationLogic.Semantics.
Require Import Logic.SeparationLogic.SemanticsExtension.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.BigStepSemantics.
Require Import Logic.HoareLogic.ConcurrentSemantics.
Require Import Logic.HoareLogic.HoareLogic_Sequential.
Require Import Logic.HoareLogic.HoareLogic_Concurrent.

Definition Inv_free
           {resource state: Type}
           (r: resource)
           (Inv: list (resource * (state -> Prop))): Prop :=
  fold_right or True (map (fun ri => fst ri = r) Inv).

Inductive Inv_cons {resource state: Type} (r: resource) (I: state -> Prop):
  list (resource * (state -> Prop)) ->
  list (resource * (state -> Prop)) ->
  Prop :=
| Inv_cons_spec: forall Inv1 Inv2,
   Inv_free r Inv1 ->
   Inv_free r Inv2 ->
   Inv_cons r I (Inv1 ++ Inv2) (Inv1 ++ (r, I) :: Inv2).

Module Resource_BigStepSemantics (D: DECREASE).

Export D.

Class Resource_BigStepSemantics
      (P: ProgrammingLanguage)
      {cP: ConcurrentProgrammingLanguage P}
      {rcP: Resource_ConcurrentProgrammingLanguage P}
      (state: Type)
      {J: Join state}
      {kiM: KripkeIntuitionisticModel state}
      (TLBSS: ThreadLocalBigStepSemantics P state
                (list (resource * (state -> Prop)))): Type :=
{
  access_Sparallel:
    forall (r: resource) (*I: state -> Prop*) Inv
      c1 c2 (m: state) (n: MetaState state),
    tl_access Inv m (Sparallel c1 c2) n ->
    exists (m1 m2: state) (n1' n2' n1 n2: MetaState state),
    join m1 m2 m /\
    tl_access Inv m1 c1 n1' /\
    tl_access Inv m2 c2 n2' /\
    decrease n1' n1 /\
    decrease n2' n2 /\
    strong_lift_join n1 n2 n;
  access_Sresource:
    forall (I: state -> Prop) Inv Inv' (r: resource) c m n,
    Inv_cons r I Inv Inv' ->
    tl_access Inv' m (Sresource r c) n ->
    exists m' n1 n2 n3 m_acq,
    least_cut m I m' /\
    decrease (Terminating m') n1 /\
    lift_tl_access Inv n1 c n2 /\
    decrease n2 n3 /\
    strong_lift_join n3 (Terminating m_acq) n /\
    I m_acq
}.

End Resource_BigStepSemantics.

Module Partial := Resource_BigStepSemantics (ProgramState.Partial).
Module Total := Resource_BigStepSemantics (ProgramState.Total).

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.

Section soundness.

Definition sem_precise
        {L: Language}
        {MD: Model}
        {J: Join model}
        {kiM: KripkeIntuitionisticModel model}
        {SM: Semantics L MD}
        (x: expr): Prop :=
  model_precise (fun m => KRIPKE: m |= x).

Lemma sem_precise_spec
        {L: Language}
        {nL: NormalLanguage L}
        {pL: PropositionalLanguage L}
        {SL: SeparationLanguage L}
        {MD: Model}
        {J: Join model}
        {kiM: KripkeIntuitionisticModel model}
        {SM: Semantics L MD}
        {kiSM: KripkeIntuitionisticSemantics L MD (tt: @Kmodel MD (unit_kMD _)) SM}
        {fsSM: FlatSemantics.FlatSemantics L MD (tt: @Kmodel MD (unit_kMD _)) SM}:
  forall m n P Q,
    sem_precise P ->
    least_cut m (fun m => KRIPKE: m |= P) n ->
    KRIPKE: m |= P * Q ->
    KRIPKE: n |= Q.
Proof.
  intros.
  rewrite FlatSemantics.sat_sepcon in H1.
  destruct H1 as [m1 [m2 [? [? ?]]]].
  destruct H0 as [? ?].
  destruct H0 as [mf [? ?]].
  specialize (H4 m2).
  eapply sat_mono; [| eassumption].
  apply H4.
  exists m1; split; auto.
Qed.

Import Partial.

Context {P: ProgrammingLanguage} {cP: ConcurrentProgrammingLanguage P} {rcP: Resource_ConcurrentProgrammingLanguage P} {MD: Model} {TLBSS: ThreadLocalBigStepSemantics P model (list (resource * (model -> Prop)))} {J: Join model} {kiM: KripkeIntuitionisticModel model} {R_BSS: Resource_BigStepSemantics P model TLBSS}.

Context {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD (tt: @Kmodel MD (unit_kMD _)) SM} {fsSM: FlatSemantics.FlatSemantics L MD (tt: @Kmodel MD (unit_kMD _)) SM}.

Lemma hoare_resource_partial_sound: forall
  (r: resource)
  (I: expr)
  (Inv Inv': list (resource * (model -> Prop)))
  c P Q,
  guarded_triple_partial_valid Inv (I * P) c (I * Q) ->
  Inv_cons r (fun s: model => s |= I) Inv Inv' ->
  sem_precise I ->
  guarded_triple_partial_valid Inv' P (Sresource r c) Q.
Proof.
  intros.
  unfold guarded_triple_partial_valid, triple_partial_valid in *.
  intros s ms ? ?.
  apply (access_Sresource (fun m => KRIPKE: m |= I) Inv) in H3; auto.
  destruct H3 as [m' [n1 [n2 [m_acq [n3 [? [? [? [? [? ?]]]]]]]]]].
  destruct ms as [| | ?s].
  + inversion H7; subst.
    inversion H6; subst.
    pose proof sem_precise_spec.
Abort.
    

End soundness.
