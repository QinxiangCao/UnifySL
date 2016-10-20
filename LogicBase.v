Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.

Class Language: Type := {
  expr: Type
}.

Class NormalLanguage {L: Language}: Type := {
  FF: expr;
  imp: expr -> expr -> expr
}.

Definition context {L: Language}: Type := Ensemble expr.

Class ProofTheory (L: Language): Type := {
  provable: expr -> Prop;
  derives: context -> expr -> Prop
}.

Definition consistent {L: Language} {nL: NormalLanguage} {Sigma: ProofTheory L}: context -> Prop :=
  fun Gamma => ~ derives Gamma FF.

Module AxiomaticProofTheory.

Class ProofTheory (L: Language): Type := {
  provable: expr -> Prop
}.

Definition multi_imp {L: Language} {nL: NormalLanguage}: list expr -> expr -> expr :=
  fix f (xs: list expr) (y: expr): expr :=
    match xs with
    | nil => y
    | x0 :: xs' => imp x0 (f xs' y)
    end.

Definition derives {L: Language} {nL: NormalLanguage} {Sigma: ProofTheory L}: context -> expr -> Prop :=
  fun Gamma y =>
    exists xs, Included expr (fun x => In x xs) Gamma /\ provable (multi_imp xs y).

End AxiomaticProofTheory.

Instance AxiomaticProofTheory_ProofTheory {L: Language} {nL: NormalLanguage} (Sigma: AxiomaticProofTheory.ProofTheory L): ProofTheory L :=
  Build_ProofTheory L AxiomaticProofTheory.provable (AxiomaticProofTheory.derives).

Module SequentCalculus.

Class ProofTheory (L: Language): Type := {
  derives: context -> expr -> Prop
}.

Definition provable {L: Language} {Sigma: ProofTheory L}: expr -> Prop :=
  fun x => derives (Empty_set _) x.

End SequentCalculus.

Instance SequentCalculus {L: Language} (Sigma: SequentCalculus.ProofTheory L): ProofTheory L :=
  Build_ProofTheory L SequentCalculus.provable SequentCalculus.derives.

Class Semantics (L: Language): Type := {
  model: Type;
  satisfies: model -> expr -> Prop
}.

Definition consequence {L: Language} {SM: Semantics L}: context -> expr -> Prop :=
  fun Gamma y =>
    forall m: model, (forall x, Gamma x -> satisfies m x) -> satisfies m y.

Definition valid {L: Language} {SM: Semantics L}: expr -> Prop :=
  fun x =>
    forall m: model, satisfies m x.

Definition satisfiable {L: Language} {SM: Semantics L}: context -> Prop :=
  fun Gamma =>
    exists m: model, forall x: expr, Gamma x -> satisfies m x.

Definition sound {L: Language} (Sigma: ProofTheory L) (SM: Semantics L): 
