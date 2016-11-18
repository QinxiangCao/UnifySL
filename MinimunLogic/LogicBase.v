Require Export Coq.Sets.Ensembles.
Require Export Coq.Lists.List.
Require Import Logic.lib.Coqlib.

Class Language: Type := {
  expr: Type
}.

Definition context {L: Language}: Type := Ensemble expr.

Definition empty_context {L: Language}: context := Empty_set _.

Class ProofTheory (L: Language): Type := {
  provable: expr -> Prop;
  derivable: context -> expr -> Prop
}.

Class Model: Type := {
  model: Type
}.

Class Semantics (L: Language) (MD: Model): Type := {
  satisfies: model -> expr -> Prop
}.

Class NormalLanguage (L: Language): Type := {
  impp: expr -> expr -> expr
}.

Class KripkeModel (MD: Model): Type := {
  Kmodel: Type;
  Kworlds: Kmodel -> Type;
  build_model: forall M: Kmodel, Kworlds M -> model
}.

Definition consistent {L: Language} {Gamma: ProofTheory L}: context -> Prop :=
  fun Phi =>
    exists x: expr, ~ derivable Phi x.

Definition consequence {L: Language} {MD: Model} {MD: Model} {SM: Semantics L MD}: context -> expr -> Prop :=
  fun Phi y =>
    forall m: model, (forall x, Phi x -> satisfies m x) -> satisfies m y.

Definition valid {L: Language} {MD: Model} {SM: Semantics L MD}: expr -> Prop :=
  fun x =>
    forall m: model, satisfies m x.

Definition satisfiable {L: Language} {MD: Model} {SM: Semantics L MD}: context -> Prop :=
  fun Phi =>
    exists m: model, forall x: expr, Phi x -> satisfies m x.

Definition sound {L: Language} (Gamma: ProofTheory L) {MD: Model} (SM: Semantics L MD): Prop :=
  forall x: expr, provable x -> valid x.

Definition weakly_complete {L: Language} (Gamma: ProofTheory L) {MD: Model} (SM: Semantics L MD): Prop :=
  forall x: expr, valid x -> provable x.

Definition strongly_complete {L: Language} (Gamma: ProofTheory L) {MD: Model} (SM: Semantics L MD): Prop :=
  forall (Phi: context) (x: expr), consequence Phi x -> derivable Phi x.

Notation "m  |=  x" := (satisfies m x) (at level 70, no associativity) : logic_base.
Notation "|==  x" := (valid x) (at level 71, no associativity) : logic_base.
Notation "Phi  |==  x" := (consequence Phi x) (at level 70, no associativity) : logic_base.
Notation "|--  x" := (provable x) (at level 71, no associativity) : logic_base.
Notation "Phi  |--  x" := (derivable Phi x) (at level 70, no associativity) : logic_base.
Notation "'KRIPKE:'  M , m" := (build_model M m) (at level 59, no associativity) : logic_base.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : logic_base.



