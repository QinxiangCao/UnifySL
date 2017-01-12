Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Definition cut {worlds: Type} {J: Join worlds} {kiM: KripkeIntuitionisticModel worlds} (m: worlds) (P: worlds -> Prop) (n: worlds) : Prop :=
  exists m', join m' n m /\ P m'.

Definition greatest_cut {worlds: Type} {J: Join worlds} {kiM: KripkeIntuitionisticModel worlds} (m: worlds) (P: worlds -> Prop) (n: worlds) : Prop :=
  cut m P n /\ (forall n', cut m P n' -> n' <= n).

Definition model_precise {worlds: Type} {J: Join worlds} {kiM: KripkeIntuitionisticModel worlds} (P: worlds -> Prop): Prop :=
  forall m n, cut m P n ->
    exists n, greatest_cut m P n.

Require Import Logic.SeparationLogic.Semantics.

Definition sem_precise
        {L: Language}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {kiM: KripkeIntuitionisticModel (Kworlds M)}
        {J: Join (Kworlds M)}
        {SM: Semantics L MD}
        (x: expr): Prop :=
  model_precise (fun m => KRIPKE: M, m |= x).
