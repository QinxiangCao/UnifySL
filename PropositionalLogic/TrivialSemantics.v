Require Import Coq.Logic.Classical_Prop.
Require Import Logic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.MinimunLogic.SyntacticReduction.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Class TrivialPropositionalSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (SM: Semantics L) {rcSM: ReductionConsistentSemantics MendelsonReduction SM}: Type := {
  sat_impp: forall m x y, m |= x --> y <-> (m |= x -> m |= y);
  sat_negp: forall m x, m |= ~~ x <-> ~ m |= x;
  sat_truep: forall m, m |= TT
}.

(*
  sem_falsep: forall m, ~ m |= FF;
  sem_andp: forall m x y, m |= x && y <-> m |= ~~ (x --> ~~ y);
  sem_orp: forall m x y, m |= x || y <-> m |= ~~ x --> y;
  sem_iffp: forall m x y, m |= (x <--> y) <-> m |= (x --> y) && (y --> x)
*)

Module TrivialSemantics.

Import PropositionalLanguage.

Definition model (Var: Type): Type := Var -> Prop.

Definition sem_imp {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  fun m => X m -> Y m.

Definition sem_neg {model: Type} (X: Ensemble model): Ensemble model :=
  fun m => ~ X m.

Definition sem_and {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  sem_neg (sem_imp X (sem_neg Y)).

Definition sem_or {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  sem_imp (sem_neg X) Y.

Definition sem_iff {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  sem_and (sem_imp X Y) (sem_imp Y X).

Fixpoint denotation {Var: Type} (x: expr Var): Ensemble (model Var) :=
  match x with
  | andp y z => sem_and (denotation y) (denotation z)
  | orp y z => sem_or (denotation y) (denotation z)
  | impp y z => sem_imp (denotation y) (denotation z)
  | iffp y z => sem_iff (denotation y) (denotation z)
  | negp y => sem_neg (denotation y)
  | truep => fun _ => True
  | falsep => fun _ => False
  | varp p => fun m => m p
  end.

Instance SM (Var: Type): Semantics (PropositionalLanguage.L Var) :=
  Build_Semantics (PropositionalLanguage.L Var) (model Var) (fun m x => denotation x m).

Lemma ImpNegAsPrime_consistent {Var: Type}:
  forall x y: expr Var,
    @ImpNegAsPrime.atomic_reduce (L Var) (nL Var) (pL Var) x y ->
    forall m: model Var, denotation x m <-> denotation y m.
Proof.
  intros; split; intros; destruct H; auto.
Qed.

Lemma ReduceIff_consistent {Var: Type}:
  forall x y: expr Var,
    @ReduceIff.atomic_reduce (L Var) (nL Var) (pL Var) x y ->
    forall m: model Var, denotation x m <-> denotation y m.
Proof.
  intros; split; intros; destruct H; auto.
Qed.

Lemma ReduceFalse_consistent {Var: Type}:
  forall x y: expr Var,
    @ReduceFalse.atomic_reduce (L Var) (nL Var) (pL Var) x y ->
    forall m: model Var, denotation x m <-> denotation y m.
Proof.
  intros; split; intros; destruct H.
  + simpl in H0.
    inversion H0.
  + specialize (H0 I).
    inversion H0.
Qed.

Lemma RPC {Var: Type}: ReductionPropagationConsistentSemantics (SM Var).
Proof.
  hnf; intros; simpl in *.
  specialize (H m).
  destruct sp.
  + simpl in *.
    unfold TrivialSemantics.sem_and, TrivialSemantics.sem_neg, TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_and, TrivialSemantics.sem_neg, TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_or, TrivialSemantics.sem_neg, TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_or, TrivialSemantics.sem_neg, TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_iff, TrivialSemantics.sem_and, TrivialSemantics.sem_neg, TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_iff, TrivialSemantics.sem_and, TrivialSemantics.sem_neg, TrivialSemantics.sem_imp; simpl.
    tauto.
  + simpl in *.
    unfold TrivialSemantics.sem_neg; simpl.
    tauto.
Qed.

Instance rcSM (Var: Type): ReductionConsistentSemantics MendelsonReduction (SM Var).
Proof.
  apply Build_ReductionConsistentSemantics.
  + hnf; intros.
    revert x y H m.
    repeat apply disjunction_reduce_consistent_semantics.
    - apply ImpNegAsPrime_consistent.
    - apply ReduceIff_consistent.
    - apply ReduceFalse_consistent.
  + apply RPC.
Qed.

Instance tpSM (Var: Type): TrivialPropositionalSemantics (L Var) (SM Var).
Proof.
  constructor.
  + simpl; intros.
    unfold sem_imp; tauto.
  + simpl; intros.
    unfold sem_neg; tauto.
  + simpl; intros; auto.
Qed.

End TrivialSemantics.

