Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Class PreKripkeSemantics (L: Language) (SM: Semantics L): Type := {
  Kmodel: Type;
  Kworlds: Kmodel -> Type;
  build_model: forall M: Kmodel, Kworlds M -> model
}.

Notation "'KRIPKE:'  M , m" := (build_model M m) (at level 59, no associativity) : logic_base.

Class KripkeIntuitionisticSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (SM: Semantics L) {rcSM: ReductionConsistentSemantics IntuitionisticReduction SM} {pkSM: PreKripkeSemantics L SM}: Type := {
  Korder: forall {M: Kmodel}, Kworlds M -> Kworlds M -> Prop; (* <= *)
  sat_mono: forall M m n x, Korder m n -> KRIPKE: M , n |= x -> KRIPKE: M , m |= x;
  sat_impp: forall M m x y, KRIPKE: M , m |= x --> y <-> (forall n, Korder n m -> KRIPKE: M , n |= x -> KRIPKE: M , n |= y);
  sat_andp: forall M m x y, KRIPKE: M , m |= x && y <-> (KRIPKE: M , m |= x /\ KRIPKE: M , m |= y);
  sat_orp: forall M m x y, KRIPKE: M , m |= x || y <-> (KRIPKE: M , m |= x \/ KRIPKE: M , m |= y);
  sat_falsep: forall M m, ~ KRIPKE: M , m |= FF
}.

Module KripkeSemantics.

Import PropositionalLanguage.

Record frame: Type := {
  underlying_set:> Type;
  Korder: relation underlying_set; (* <= *)
  Korder_preorder: PreOrder Korder
}.

Infix "<=" := (Korder _): KripkeSemantics.

Local Open Scope KripkeSemantics.

Definition sem (f: frame) := sig (fun s: Ensemble f => forall x y, x <= y -> s y -> s x).

Program Definition sem_and {F: frame} (X: sem F) (Y: sem F): sem F :=
  fun x: F => X x /\ Y x.
Next Obligation.
  split.
  + eapply (proj2_sig X); eauto.
  + eapply (proj2_sig Y); eauto.
Qed.

Program Definition sem_or {F: frame} (X: sem F) (Y: sem F): sem F :=
  fun x: F => X x \/ Y x.
Next Obligation.
  destruct H0; [left | right].
  + eapply (proj2_sig X); eauto.
  + eapply (proj2_sig Y); eauto.
Qed.

Program Definition sem_imp {F: frame} (X: sem F) (Y: sem F): sem F :=
  fun x: F =>
    forall y: F, y <= x -> X y -> Y y.
Next Obligation.
  revert H2; apply H0.
  pose proof @PreOrder_Transitive _ _ (Korder_preorder F).
  transitivity x; auto.
Qed.

Program Definition sem_true {F: frame}: sem F :=
  fun x: F => True.

Program Definition sem_false {F: frame}: sem F :=
  fun x: F => False.

Definition sem_neg {F: frame} (X: sem F): sem F :=
  sem_imp X sem_false.

Definition sem_iff {F: frame} (X: sem F) (Y: sem F): sem F :=
  sem_and (sem_imp X Y) (sem_imp Y X).

Definition denotation {Var: Type} (F: frame) (eval: Var -> sem F): expr Var -> sem F :=
  fix denotation (x: expr Var): sem F:=
  match x with
  | andp y z => sem_and (denotation y) (denotation z)
  | orp y z => sem_or (denotation y) (denotation z)
  | impp y z => sem_imp (denotation y) (denotation z)
  | iffp y z => sem_iff (denotation y) (denotation z)
  | negp y => sem_neg (denotation y)
  | truep => sem_true
  | falsep => sem_false
  | varp p => eval p
  end.

Lemma ImpAndOrAsPrime_consistent {Var: Type}:
  forall x y: expr Var,
    @ImpAndOrAsPrime.atomic_reduce (L Var) (nL Var) (pL Var) x y ->
    forall f eval v, proj1_sig (denotation f eval x) v <-> proj1_sig (denotation f eval y) v.
Proof.
  intros; split; intros; destruct H; auto.
Qed.

Lemma ReduceIff_consistent {Var: Type}:
  forall x y: expr Var,
    @ReduceIff.atomic_reduce (L Var) (nL Var) (pL Var) x y ->
    forall f eval v, proj1_sig (denotation f eval x) v <-> proj1_sig (denotation f eval y) v.
Proof.
  intros; split; intros; destruct H; auto.
Qed.

Lemma ReduceTrue_consistent {Var: Type}:
  forall x y: expr Var,
    @ReduceTrue.atomic_reduce (L Var) (nL Var) (pL Var) x y ->
    forall f eval v, proj1_sig (denotation f eval x) v <-> proj1_sig (denotation f eval y) v.
Proof.
  intros; split; intros; destruct H.
  + hnf; intros; auto.
  + hnf; auto.
Qed.

Lemma RPC_aux {Var: Type}: forall  F eval (x y: expr Var) sp,
  (forall v, proj1_sig (denotation F eval x) v <-> proj1_sig (denotation F eval y) v) ->
  (forall v, proj1_sig (denotation F eval (single_propagation_denote sp x)) v <->
             proj1_sig (denotation F eval (single_propagation_denote sp y)) v).
Proof.
  intros.
  destruct sp; intros.
  + specialize (H v).
    simpl in *.
    tauto.
  + specialize (H v).
    simpl in *.
    tauto.
  + specialize (H v).
    simpl in *.
    tauto.
  + specialize (H v).
    simpl in *.
    tauto.
  + simpl in *.
    split; intros HH u Hu; specialize (HH u Hu); specialize (H u); tauto.
  + simpl in *.
    split; intros HH u Hu; specialize (HH u Hu); specialize (H u); tauto.
  + simpl in *.
    apply Morphisms_Prop.and_iff_morphism.
    - simpl in *.
      split; intros HH u Hu; specialize (HH u Hu); specialize (H u); tauto.
    - simpl in *.
      split; intros HH u Hu; specialize (HH u Hu); specialize (H u); tauto.
  + simpl in *.
    apply Morphisms_Prop.and_iff_morphism.
    - simpl in *.
      split; intros HH u Hu; specialize (HH u Hu); specialize (H u); tauto.
    - simpl in *.
      split; intros HH u Hu; specialize (HH u Hu); specialize (H u); tauto.
  + simpl in *.
    split; intros HH u Hu; specialize (HH u Hu); specialize (H u); tauto.
Qed.

End KripkeSemantics.

Module KripkeSemantics_All.

Import KripkeSemantics.

Record Kmodel {Var: Type} : Type := {
  underlying_frame :> frame;
  Kvar: Var -> sem underlying_frame
}.

Record model {Var: Type}: Type := {
  underlying_model :> @Kmodel Var;
  elm: underlying_model
}.

Implicit Arguments model.

Instance SM (Var: Type): Semantics (PropositionalLanguage.L Var) :=
  Build_Semantics (PropositionalLanguage.L Var)
   (@model Var)
   (fun M x => proj1_sig (denotation M (Kvar M) x) (elm M)).

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Lemma RPC {Var: Type}: ReductionPropagationConsistentSemantics (SM Var).
Proof.
  hnf; intros; simpl in *.
  destruct m as [M v].
  pose proof (fun v => H (Build_model _ M v)).
  revert v; simpl in H0; clear H. simpl.
  apply RPC_aux; auto.
Qed.

Instance rcSM (Var: Type): ReductionConsistentSemantics IntuitionisticReduction (SM Var).
Proof.
  apply Build_ReductionConsistentSemantics.
  + hnf; intros.
    revert x y H m.
    repeat apply disjunction_reduce_consistent_semantics; intros.
    - apply ImpAndOrAsPrime_consistent; auto.
    - apply ReduceIff_consistent; auto.
    - apply ReduceTrue_consistent; auto.
  + apply RPC.
Qed.

Instance pkSM (Var: Type): PreKripkeSemantics (PropositionalLanguage.L Var) (SM Var) :=
  Build_PreKripkeSemantics _ (SM Var)
   Kmodel
   (fun M => M)
   (fun M m => Build_model _ M m).

Instance kiSM (Var: Type): KripkeIntuitionisticSemantics (PropositionalLanguage.L Var) (SM Var).
Proof.
  apply (Build_KripkeIntuitionisticSemantics _ _ _ _ _ (pkSM Var) (fun M => Korder M)).
  + hnf; simpl; intros.
    eapply (proj2_sig (denotation M (Kvar M) x)); eauto.
  + split; auto.
  + split; auto.
  + split; auto.
  + intros; simpl. auto.
Qed.

End KripkeSemantics_All.

Module KripkeSemantics_Reflexive.

Import KripkeSemantics.

Import KripkeSemantics.

Record Kmodel {Var: Type} : Type := {
  underlying_frame :> frame;
  Kvar: Var -> sem underlying_frame;
  frame_reflexive: Reflexive (Korder underlying_frame)
}.

Record model {Var: Type}: Type := {
  underlying_model :> @Kmodel Var;
  elm: underlying_model
}.

Implicit Arguments model.

Instance SM (Var: Type): Semantics (PropositionalLanguage.L Var) :=
  Build_Semantics (PropositionalLanguage.L Var)
   (@model Var)
   (fun M x => proj1_sig (denotation M (Kvar M) x) (elm M)).

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Lemma RPC {Var: Type}: ReductionPropagationConsistentSemantics (SM Var).
Proof.
  hnf; intros; simpl in *.
  destruct m as [M v].
  pose proof (fun v => H (Build_model _ M v)).
  revert v; simpl in H0; clear H. simpl.
  apply RPC_aux; auto.
Qed.

Instance rcSM (Var: Type): ReductionConsistentSemantics IntuitionisticReduction (SM Var).
Proof.
  apply Build_ReductionConsistentSemantics.
  + hnf; intros.
    revert x y H m.
    repeat apply disjunction_reduce_consistent_semantics; intros.
    - apply ImpAndOrAsPrime_consistent; auto.
    - apply ReduceIff_consistent; auto.
    - apply ReduceTrue_consistent; auto.
  + apply RPC.
Qed.

Instance pkSM (Var: Type): PreKripkeSemantics (PropositionalLanguage.L Var) (SM Var) :=
  Build_PreKripkeSemantics _ (SM Var)
   Kmodel
   (fun M => M)
   (fun M m => Build_model _ M m).

Instance kiSM (Var: Type): KripkeIntuitionisticSemantics (PropositionalLanguage.L Var) (SM Var).
Proof.
  apply (Build_KripkeIntuitionisticSemantics _ _ _ _ _ (pkSM Var) (fun M => Korder M)).
  + hnf; simpl; intros.
    eapply (proj2_sig (denotation M (Kvar M) x)); eauto.
  + split; auto.
  + split; auto.
  + split; auto.
  + intros; simpl. auto.
Qed.

End KripkeSemantics_Reflexive.

