Require Export Coq.Sets.Ensembles.
Require Export Coq.Lists.List.
Require Import Logic.lib.Coqlib.

Class Language: Type := {
  expr: Type;
  single_propagation: Type;
  single_propagation_denote: single_propagation -> expr -> expr
}.

Fixpoint propagation_denote {L: Language} (p: list single_propagation) (x: expr): expr :=
  match p with
  | nil => x
  | sp :: p0 => single_propagation_denote sp (propagation_denote p0 x)
  end.

Definition context {L: Language}: Type := Ensemble expr.

Definition empty_context {L: Language}: context := Empty_set _.

Class ProofTheory (L: Language): Type := {
  provable: expr -> Prop;
  derivable: context -> expr -> Prop
}.

Class Semantics (L: Language): Type := {
  model: Type;
  satisfies: model -> expr -> Prop
}.

Definition consistent {L: Language} {Gamma: ProofTheory L}: context -> Prop :=
  fun Phi =>
    exists x: expr, ~ derivable Phi x.

Definition consequence {L: Language} {SM: Semantics L}: context -> expr -> Prop :=
  fun Phi y =>
    forall m: model, (forall x, Phi x -> satisfies m x) -> satisfies m y.

Definition valid {L: Language} {SM: Semantics L}: expr -> Prop :=
  fun x =>
    forall m: model, satisfies m x.

Definition satisfiable {L: Language} {SM: Semantics L}: context -> Prop :=
  fun Phi =>
    exists m: model, forall x: expr, Phi x -> satisfies m x.

Definition sound {L: Language} (Gamma: ProofTheory L) (SM: Semantics L): Prop :=
  forall x: expr, provable x -> valid x.

Definition weakly_complete {L: Language} (Gamma: ProofTheory L) (SM: Semantics L): Prop :=
  forall x: expr, valid x -> provable x.

Definition strongly_complete {L: Language} (Gamma: ProofTheory L) (SM: Semantics L): Prop :=
  forall (Phi: context) (x: expr), consequence Phi x -> derivable Phi x.

Notation "m  |=  x" := (satisfies m x) (at level 60, no associativity) : logic_base.
Notation "|==  x" := (valid x) (at level 61, no associativity) : logic_base.
Notation "Phi  |==  x" := (consequence Phi x) (at level 60, no associativity) : logic_base.
Notation "|--  x" := (provable x) (at level 61, no associativity) : logic_base.
Notation "Phi  |--  x" := (derivable Phi x) (at level 60, no associativity) : logic_base.


