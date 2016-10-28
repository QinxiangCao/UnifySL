Require Export Coq.Sets.Ensembles.
Require Export Coq.Lists.List.

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

Class NormalLanguage (L: Language): Type := {
  falsep: expr;
  impp: expr -> expr -> expr;
  imp1_propag: expr -> single_propagation;
  imp2_propag: expr -> single_propagation;
  imp1_propag_denote: forall x y, single_propagation_denote (imp1_propag x) y = impp y x;
  imp2_propag_denote: forall x y, single_propagation_denote (imp2_propag x) y = impp x y
}.

Definition context {L: Language}: Type := Ensemble expr.

Definition empty_context {L: Language}: context := Empty_set _.

Class ProofTheory (L: Language): Type := {
  provable: expr -> Prop;
  derivable: context -> expr -> Prop
}.

Definition multi_imp {L: Language} {nL: NormalLanguage L}: list expr -> expr -> expr :=
  fix f (xs: list expr) (y: expr): expr :=
    match xs with
    | nil => y
    | x0 :: xs' => impp x0 (f xs' y)
    end.

Class NormalProofTheory (L: Language) {nL: NormalLanguage L} (Gamma: ProofTheory L): Type := {
  provable_derivable: forall x, provable x <-> derivable empty_context x;
  derivable_provable: forall Phi y, derivable Phi y <->
                        exists xs, Forall (fun x => Phi x) xs /\ provable (multi_imp xs y)
}.

Definition consistent {L: Language} {nL: NormalLanguage L} (Gamma: ProofTheory L): context -> Prop :=
  fun Phi => ~ derivable Phi falsep.

Definition maximal_consistent {L: Language} {nL: NormalLanguage L} (Gamma: ProofTheory L): context -> Prop :=
  fun Phi => consistent Gamma Phi /\ forall Psi, consistent Gamma Psi -> Included _ Phi Psi -> Included _ Psi Phi.

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

Class AxiomaticProofTheory (L: Language): Type := {
  provable: expr -> Prop
}.

Definition derivable {L: Language} {nL: NormalLanguage L} {Gamma: AxiomaticProofTheory L}: context -> expr -> Prop :=
  fun Phi y =>
    exists xs, Forall (fun x => Phi x) xs /\ provable (multi_imp xs y).

Lemma provable_derivable {L: Language} {nL: NormalLanguage L} {Gamma: AxiomaticProofTheory L}: forall x, provable x <-> derivable empty_context x.
Proof.
  intros.
  split; intros.
  + exists nil; split; auto.
  + destruct H as [xs [? ?]].
    destruct xs; [auto |].
    inversion H; subst.
    inversion H3.
Qed.

Instance G {L: Language} {nL: NormalLanguage L} (Gamma: AxiomaticProofTheory L): ProofTheory L :=
  Build_ProofTheory L provable derivable.

Instance nG {L: Language} {nL: NormalLanguage L} (Gamma: AxiomaticProofTheory L): NormalProofTheory L (G Gamma) :=
  Build_NormalProofTheory L nL (G Gamma) provable_derivable (fun _ _ => iff_refl _).

End AxiomaticProofTheory.

Module SequentCalculus.

Class ProofTheory (L: Language): Type := {
  derivable: context -> expr -> Prop
}.

Definition provable {L: Language} {Gamma: ProofTheory L}: expr -> Prop :=
  fun x => derivable (Empty_set _) x.

(*
Instance SequentCalculus {L: Language} (Gamma: SequentCalculus.ProofTheory L): ProofTheory L :=
  Build_ProofTheory L SequentCalculus.provable SequentCalculus.derivable (fun x => iff_refl _).
*)

End SequentCalculus.

Notation "m  |=  x" := (satisfies m x) (at level 60, no associativity) : logic_base.
Notation "|==  x" := (valid x) (at level 61, no associativity) : logic_base.
Notation "Phi  |==  x" := (consequence Phi x) (at level 60, no associativity) : logic_base.
Notation "|--  x" := (provable x) (at level 61, no associativity) : logic_base.
Notation "Phi  |--  x" := (derivable Phi x) (at level 60, no associativity) : logic_base.

