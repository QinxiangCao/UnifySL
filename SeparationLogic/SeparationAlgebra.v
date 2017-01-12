Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.KripkeSemantics.

Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.


Class Join (worlds: Type): Type := join: worlds -> worlds -> worlds -> Prop.

Class SeparationAlgebra (worlds: Type) {SA: Join worlds}: Type :=
  {
    join_comm: forall m1 m2 m: worlds, join m1 m2 m -> join m2 m1 m;
    join_assoc: forall mx my mz mxy mxyz: worlds,
        join mx my mxy ->
        join mxy mz mxyz ->
        exists myz, join my mz myz /\ join mx myz mxyz
  }.

Definition increasing
           {worlds: Type}
           {kiM: KripkeIntuitionisticModel worlds}
           {J: Join worlds}: worlds -> Prop :=
  fun m => forall n n', join m n n' -> n <= n'.

Definition unit_element
           {worlds: Type}
           {kiM: KripkeIntuitionisticModel worlds}
           {J: Join worlds}: worlds -> Prop :=
  fun e => forall n n', join e n n' -> n = n'.

(* 
 * In a separation algebra with discrete order, 
 * an element is increasing iff it is a unit.*)
Lemma disc_incr_unit
           {worlds: Type}
           {kiM: KripkeIntuitionisticModel worlds}
           {J: Join worlds}:
  IdentityKripkeIntuitionisticModel worlds ->
  forall e, increasing e <-> unit_element e.
Proof.
  intros;
  split; intros; hnf; intros.
  - hnf; intros.
    apply H.
    apply H0; auto.
  - apply H0 in H1; subst;
    reflexivity.
Qed.

Class IncreasingSeparationAlgebra
      (worlds: Type)
      {kiM: KripkeIntuitionisticModel worlds}
      {J: Join worlds }: Type :=
  { all_increasing: forall x: worlds, increasing x }.

  (* -Legacy definition-            *
   * Garbage Collected algebra      *
   * Is equivalent to increasing *)  
  Class GarbageCollectSeparationAlgebra(worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {J: Join worlds }: Type :=
  {
    join_has_order1: forall (m1 m2 m: worlds), join m1 m2 m -> m1 <= m
  }.
Lemma Increasing2GarbageCollect:
  forall
    (worlds: Type) {kiM: KripkeIntuitionisticModel worlds}
    {J: Join worlds }{SA: SeparationAlgebra worlds},
    GarbageCollectSeparationAlgebra worlds ->
    IncreasingSeparationAlgebra worlds.
Proof.
  intros.
  constructor; intros; hnf; intros.
  eapply join_has_order1.
  eapply join_comm. eassumption.
Qed.

Lemma GarbageCollect2Increasing:
  forall (worlds: Type) {kiM: KripkeIntuitionisticModel worlds}
    {J: Join worlds }{SA: SeparationAlgebra worlds},
    IncreasingSeparationAlgebra worlds ->
    GarbageCollectSeparationAlgebra worlds.
Proof.
  intros.
  constructor; intros.
  pose (all_increasing m2).
  apply i; apply join_comm; assumption.
Qed.

Definition residue
           {worlds: Type}
           {kiM: KripkeIntuitionisticModel worlds}
           {J: Join worlds}
           (m n: worlds): Prop :=
  exists n', join n n' m /\ m <= n'.


Class ResidualSeparationAlgebra(worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {J: Join worlds}: Type :=
  {
    residue_exists: forall n: worlds, exists m, residue n m;
  }.

Class UnitalSeparationAlgebra(worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {J: Join worlds}: Type :=
  {
    incr_exists: forall n: worlds, exists m, residue n m /\ increasing m
  }.

(* A unital separation algebra is residual. *)
Lemma unital_is_residual
  {worlds: Type}
    {kiM: KripkeIntuitionisticModel worlds}
    {J: Join worlds}:
  UnitalSeparationAlgebra worlds ->
  ResidualSeparationAlgebra worlds.
Proof.
  constructor; intros.
  destruct (incr_exists n) as [m [RES _]].
  exists m; auto.
Qed.

(*A increasing separation algebras is unital 
 * iff it is residual.*)
Lemma incr_unital_iff_residual
  {worlds: Type}
    {kiM: KripkeIntuitionisticModel worlds}
    {J: Join worlds} :
  IncreasingSeparationAlgebra worlds ->
  UnitalSeparationAlgebra worlds <->
  ResidualSeparationAlgebra worlds.
Proof.
  intros; split.
  - apply unital_is_residual; auto.
  - constructor; intros.
    destruct (residue_exists n) as [m RES].
    exists m; split; auto.
    apply all_increasing.
Qed.

Class UpwardsClosedSeparationAlgebra (worlds: Type) {J: Join worlds}
      {kiM: KripkeIntuitionisticModel worlds} : Type :=
  join_Korder_up: forall m n m1 m2: worlds,
    join m1 m2 m -> m <= n ->
    exists n1 n2, join n1 n2 n /\ m1 <= n1 /\ m2 <= n2.

Class DownwardsClosedSeparationAlgebra(worlds: Type) {J: Join worlds}
      {kiM: KripkeIntuitionisticModel worlds}: Type :=
  join_Korder_down: forall m1 m2 m n1 n2: worlds,
    join m1 m2 m -> n1 <= m1 -> n2 <= m2 ->
    exists n, join n1 n2 n /\ n <= m.

(* David J. Pym, Peter W. O’Hearn, and Hongseok Yang. Possible worlds and resources: the semantics of BI. *)

(* This join_Korder is equivalent with the following because Korder is reflexive.
  join_Korder: forall M (m1 m2 m n1 : Kworlds M), join m1 m2 m -> Korder m1 n1 -> exists n, join n1 m2 n /\ Korder m n;

It is necessary to be this strong, or else sepcon_assoc will be unsound, e.g. the following weaker version causes unsoundness:
  join_Korder: forall M (m1 m2 m n1: Kworlds M), join m1 m2 m -> Korder m1 n1 -> exists n2 n, join n1 n2 n /\ Korder m2 n2 /\ Korder m n;  *)

