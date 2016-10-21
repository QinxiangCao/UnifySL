Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.

Class Language: Type := {
  expr: Type
}.

Class NormalLanguage (L: Language): Type := {
  FF: expr;
  imp: expr -> expr -> expr
}.

Definition context {L: Language}: Type := Ensemble expr.

Definition empty_context {L: Language}: context := Empty_set _.

Class ProofTheory (L: Language): Type := {
  provable: expr -> Prop;
  derivable: context -> expr -> Prop;
  provable_derivable: forall x, provable x <-> derivable empty_context x
}.

Definition consistent {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L}: context -> Prop :=
  fun Phi => ~ derivable Phi FF.

Class Semantics (L: Language): Type := {
  model: Type;
  satisfies: model -> expr -> Prop
}.

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


Module AxiomaticProofTheory.

Class ProofTheory (L: Language): Type := {
  provable: expr -> Prop
}.

Definition multi_imp {L: Language} {nL: NormalLanguage L}: list expr -> expr -> expr :=
  fix f (xs: list expr) (y: expr): expr :=
    match xs with
    | nil => y
    | x0 :: xs' => imp x0 (f xs' y)
    end.

Definition derivable {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L}: context -> expr -> Prop :=
  fun Phi y =>
    exists xs, Included expr (fun x => In x xs) Phi /\ provable (multi_imp xs y).

Lemma provable_derivable {L: Language} {nL: NormalLanguage L} {Gamma: ProofTheory L}: forall x, provable x <-> derivable empty_context x.
Proof.
  intros.
  split; intros.
  + exists nil; split; auto.
    hnf; intros.
    inversion H0.
  + destruct H as [xs [? ?]].
    destruct xs; [auto |].
    specialize (H e (or_introl eq_refl)).
    inversion H.
Qed.

End AxiomaticProofTheory.

Instance AxiomaticProofTheory_ProofTheory {L: Language} {nL: NormalLanguage L} (Gamma: AxiomaticProofTheory.ProofTheory L): ProofTheory L :=
  Build_ProofTheory L AxiomaticProofTheory.provable AxiomaticProofTheory.derivable AxiomaticProofTheory.provable_derivable.

Module SequentCalculus.

Class ProofTheory (L: Language): Type := {
  derivable: context -> expr -> Prop
}.

Definition provable {L: Language} {Gamma: ProofTheory L}: expr -> Prop :=
  fun x => derivable (Empty_set _) x.

End SequentCalculus.

Instance SequentCalculus {L: Language} (Gamma: SequentCalculus.ProofTheory L): ProofTheory L :=
  Build_ProofTheory L SequentCalculus.provable SequentCalculus.derivable (fun x => iff_refl _).

Notation "m  |=  x" := (satisfies m x) (at level 60, no associativity) : logic_base.
Notation "|==  x" := (valid x) (at level 61, no associativity) : logic_base.
Notation "Phi  |==  x" := (consequence Phi x) (at level 60, no associativity) : logic_base.
Notation "|--  x" := (provable x) (at level 61, no associativity) : logic_base.
Notation "Phi  |--  x" := (derivable Phi x) (at level 60, no associativity) : logic_base.

