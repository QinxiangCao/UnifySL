Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.SeparationLogic.Semantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.SequentialSemantics.
Require Import Logic.HoareLogic.ConcurrentSemantics.
Require Import Logic.HoareLogic.HoareLogic_Sequential.

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

Class Resource_BigStepSemantics
      (P: ProgrammingLanguage)
      {rcP: Resource_ConcurrentProgrammingLanguage P}
      (state: Type)
      {J: Join state}
      (TLBSS: ThreadLocalBigStepSemantics P state
                (list (resource * (state -> Prop)))): Type :=
{
  access_Sresource:
    forall (r: resource) (I: state -> Prop) Inv Inv'
      c m1 m_acq m1' m2 m_rel m2',
    tl_access Inv m1 c (Terminating m2) ->
    join m1' m_acq m1 ->
    join m2' m_rel m2 ->
    Inv_cons r I Inv Inv' ->
    I m_acq ->
    I m_rel ->
    tl_access Inv' m1' (Sresource r c) (Terminating m2')
}.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.

Section soundness.

Existing Instance unit_kMD.

Context {P: ProgrammingLanguage} {rcP: Resource_ConcurrentProgrammingLanguage P} {MD: Model} {TLBSS: ThreadLocalBigStepSemantics P model (list (resource * (model -> Prop)))} {J: Join model} {R_BSS: Resource_BigStepSemantics P model TLBSS}.

Context {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L MD} {kiM: KripkeIntuitionisticModel model} {kiSM: KripkeIntuitionisticSemantics L MD tt SM} {fsSM: FlatSemantics.FlatSemantics L MD tt SM}.

(*
Lemma hoare_resource_partial_sound: forall r I Inv Inv' c P Q F,
  guarded_triple_partial_valid Inv (P * I) c (Q * F) ->
  triple_partial_valid (P * F) c (Q * F).
Proof.
  intros.
  unfold triple_partial_valid in *.
  intros s ms ? ?.
*)
End soundness.
