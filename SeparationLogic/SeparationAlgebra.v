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


Definition nonpositive
           {worlds: Type}
           {kiM: KripkeIntuitionisticModel worlds}
           {J: Join worlds}: worlds -> Prop :=
  fun m => forall n n', join m n n' -> n' <= n.

Definition unit_for
           {worlds: Type}
           {kiM: KripkeIntuitionisticModel worlds}
           {J: Join worlds}: worlds -> worlds -> Prop :=
  fun m e => forall n, join e m n -> m = n.

Definition unit
           {worlds: Type}
           {kiM: KripkeIntuitionisticModel worlds}
           {J: Join worlds}: worlds -> Prop :=
  (* fun e => forall n n', join m n n' -> n'= n.*)
  fun e => forall m, unit_for m e.

(* 
 * In a separation algebra with discrete order, 
 * an element is nonpositive iff it is a unit.*)
Lemma disc_nonpos_unit
           {worlds: Type}
           {kiM: KripkeIntuitionisticModel worlds}
           {J: Join worlds}:
  IdentityKripkeIntuitionisticModel worlds ->
  forall e, nonpositive e <-> unit e.
Proof.
  intros;
  split; intros; hnf; intros.
  - hnf; intros.
    symmetry; apply H.
    apply H0; auto.
  - apply H0 in H1; subst.
    reflexivity.
Qed.

Class NonpositiveSeparationAlgebra
      (worlds: Type)
      {kiM: KripkeIntuitionisticModel worlds}
      {J: Join worlds }: Type :=
  { all_nonpositive: forall x: worlds, nonpositive x }.

  (* -Legacy definition-            *
   * Garbage Collected algebra      *
   * Is equivalent to nonpositivity *)  
  Class GarbageCollectSeparationAlgebra(worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {J: Join worlds }: Type :=
  {
    join_has_order1: forall (m1 m2 m: worlds), join m1 m2 m -> m <= m1
  }.
Lemma Nonpositive2GarbageCollect:
  forall
    (worlds: Type) {kiM: KripkeIntuitionisticModel worlds}
    {J: Join worlds }{SA: SeparationAlgebra worlds},
    GarbageCollectSeparationAlgebra worlds ->
    NonpositiveSeparationAlgebra worlds.
Proof.
  intros.
  constructor; intros; hnf; intros.
  eapply join_has_order1.
  eapply join_comm. eassumption.
Qed.

Lemma GarbageCollect2Nonpositive:
  forall (worlds: Type) {kiM: KripkeIntuitionisticModel worlds}
    {J: Join worlds }{SA: SeparationAlgebra worlds},
    NonpositiveSeparationAlgebra worlds ->
    GarbageCollectSeparationAlgebra worlds.
Proof.
  intros.
  constructor; intros.
  pose (all_nonpositive m2).
  apply n; apply join_comm; assumption.
Qed.
  
Definition residue
           {worlds: Type}
           {kiM: KripkeIntuitionisticModel worlds}
           {J: Join worlds}
           (m n: worlds): Prop :=
  exists n', join n n' m /\ n' <= m.


Class ResidualSeparationAlgebra(worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {J: Join worlds}: Type :=
  {
    residue_exists: forall n: worlds, exists m, residue n m;
  }.

Class UnitalSeparationAlgebra(worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {J: Join worlds}: Type :=
  {
    unit_exists: forall n: worlds, exists m, residue n m /\ nonpositive m ;
    unit_down: forall n m: worlds, n <= m -> nonpositive m -> nonpositive n
  }.


(* In a separation algebra with discrete order
 * and deterministic functional join, 
 * an element has a residue iff it has a unit. *)
Definition functional_join
           {worlds: Type}
           (J: Join worlds):=
  forall a b c c',
    join a b c -> join a b c' -> c = c'.

(*
Lemma disc_unit_residue
           {worlds: Type}
           {kiM: KripkeIntuitionisticModel worlds}
           {J: Join worlds}
           (m n: worlds):
  IdentityKripkeIntuitionisticModel worlds ->
  functional_join J ->
  forall n e, residue n e <-> unit_for n e.
Proof.
  intros; split; intros; hnf; intros.
  - destruct H1 as [n' [JOIN ORD]].
    apply H in ORD; subst.
    eapply H0; eauto.
  - exists n; split.
    unfold unit_for in H1.*)
  
(* Similarly, the algebra with discrete order is 
 * unital iff residual. *)
Lemma disc_unital_residual
           {worlds: Type}
           {kiM: KripkeIntuitionisticModel worlds}
           {J: Join worlds}:
  IdentityKripkeIntuitionisticModel worlds ->
  ResidualSeparationAlgebra worlds <->
  UnitalSeparationAlgebra worlds.
Proof.
  intros; split; intros; hnf; intros.
  Focus 2.
  - constructor.
    intros.
    destruct (unit_exists n) as [m RES].
    
  - constructor; intros.
    + destruct (residue_exists n) as [m RES].
      exists m; split; auto.
      unfold nonpositive.
      destruct RES as [N [HH1 HH2]].


Class DownwardsClosedSeparationAlgebra(worlds: Type) {J: Join worlds}
      {kiM: KripkeIntuitionisticModel worlds} : Type :=
  join_Korder_down: forall m n m1 m2: worlds,
    join m1 m2 m -> n <= m ->
    exists n1 n2, join n1 n2 n /\ n1 <= m1 /\ n2 <= m2.

Class UpwardsClosedSeparationAlgebra(worlds: Type) {J: Join worlds}
      {kiM: KripkeIntuitionisticModel worlds}: Type :=
  join_Korder_up: forall m1 m2 m n1 n2: worlds,
    join m1 m2 m -> m1 <= n1 -> m2 <= n2 ->
    exists n, join n1 n2 n /\ m <= n.

(* David J. Pym, Peter W. O’Hearn, and Hongseok Yang. Possible worlds and resources: the semantics of BI. *)

(* This join_Korder is equivalent with the following because Korder is reflexive.
  join_Korder: forall M (m1 m2 m n1 : Kworlds M), join m1 m2 m -> Korder m1 n1 -> exists n, join n1 m2 n /\ Korder m n;

It is necessary to be this strong, or else sepcon_assoc will be unsound, e.g. the following weaker version causes unsoundness:
  join_Korder: forall M (m1 m2 m n1: Kworlds M), join m1 m2 m -> Korder m1 n1 -> exists n2 n, join n1 n2 n /\ Korder m2 n2 /\ Korder m n;  *)

Definition UpwardsClosed_nUSA(worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {J: Join worlds} {uSA: UpwardsClosedSeparationAlgebra worlds}:
  forall (unit_exists: forall n: worlds, exists m,  residue n m /\ nonpositive m),
    UnitalSeparationAlgebra worlds .
Proof.
  intros; constructor; auto.
  intros n m ineq preU.
  pose proof Korder_PreOrder as H_PreOrder.
  unfold nonpositive in *.
  intros.
  destruct (join_Korder_up _ _ _ _ n0 H ineq) as [n'' [? ?]]; [reflexivity |].
  etransitivity; eauto.
Qed.

