Require Import Coq.Logic.ChoiceFacts.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalChoice.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.SeparationLogic.SeparationAlgebraGenerators.

Require Import Coq.omega.Omega.

(***********************************)
(* ALGEBRAS ON NATURALS            *)
(***********************************)

Section nat_algs.

Definition nat_kiM: KripkeIntuitionisticModel nat:=
    Build_KripkeIntuitionisticModel _ _ NPeano.Nat.le_preorder.

(** *Index algebras *)
  Inductive delta3 {T:Type}: T -> T -> T -> Prop:=
    |Delta3 a: delta3 a a a.

  Definition indexAlg: @SeparationAlgebra nat delta3.
  Proof. constructor; intros.
         - inversion H; constructor.
         - inversion H; inversion H0; subst.
           exists mxyz; split; constructor.
  Defined.

  (* downwards-closed*)
  Instance IndexAlg_dSA:
    @DownwardsClosedSeparationAlgebra _ delta3 nat_kiM.
  Proof.
    hnf; intros.
    inversion H; subst.
    exists n, n. repeat split; auto.
  Qed.

  (* Nonpositive*)
  Instance IndexAlg_nonpositive:
    @NonpositiveSeparationAlgebra _ nat_kiM  delta3.
  Proof.
    constructor; intro.
    hnf; intros. inversion H; subst.
    reflexivity.
  Qed.

  (*Residual*)
  Instance IndexAlg_residual:
    @ResidualSeparationAlgebra _ nat_kiM  delta3.
  Proof.
    constructor; intro.
    exists n, n; split.
    constructor.
    reflexivity.
  Qed.

  (* Unital *)
Instance IndexAlg_unital:
  @UnitalSeparationAlgebra _ nat_kiM  delta3.
Proof.
  apply nonpos_unital_iff_residual.
  apply IndexAlg_nonpositive.
  apply IndexAlg_residual.
Qed.

(** *Minimum Algebra*)
Inductive min_Join: nat -> nat -> nat -> Prop:=
  |min_j x y z: z <= x -> z<= y -> min_Join x y z.

Definition minAlg: @SeparationAlgebra nat min_Join.
Proof. constructor; intros.
         - inversion H; subst; constructor; auto.
         - inversion H; inversion H0; subst.
           exists (Min.min my mz); split; constructor.
           + apply Min.le_min_l.
           + apply Min.le_min_r.
           + transitivity mxy; auto.
           + apply Min.min_glb.
             * transitivity mxy; auto.
             * auto.
Qed.

  (* downwards-closed*)
  Instance minAlg_dSA:
    @DownwardsClosedSeparationAlgebra _ min_Join nat_kiM.
  Proof.
    hnf; intros.
    inversion H;  subst.
    exists m1, m2; split; constructor;
    first[ solve[transitivity m; auto] | reflexivity].
  Qed.


  (* upwards-closed*)
  Instance minAlg_uSA:
    @UpwardsClosedSeparationAlgebra _ min_Join nat_kiM.
  Proof.
    hnf; intros.
    inversion H; subst.
    exists m; split ; constructor.
    - transitivity m1; auto.
    - transitivity m2; auto.
  Qed.

  (* Nonpositive*)
  Instance minAlg_nonpositive:
    @NonpositiveSeparationAlgebra _ nat_kiM  min_Join.
  Proof.
    constructor; intro.
    hnf; intros. inversion H; subst; auto.
  Qed.

  (*Residual*)
  Instance minAlg_residual:
    @ResidualSeparationAlgebra _ nat_kiM   min_Join.
  Proof.
    constructor; intro.
    exists n, n; split.
    constructor; reflexivity.
    reflexivity.
  Qed.

  (* Unital *)
  Instance minAlg_unital:
    @UnitalSeparationAlgebra _ nat_kiM  min_Join.
  Proof.
    apply nonpos_unital_iff_residual.
    apply minAlg_nonpositive.
    apply minAlg_residual.
  Qed.

  
  (** *Minimum Algebra*)
  Record natPlus: Type:=
    { n:> nat;
      is_pos: 0 < n}.


Inductive sum_Join: natPlus -> natPlus -> natPlus -> Prop:=
  |sum_j (x y z:natPlus): x + y = z -> sum_Join x y z.

Definition lep (n m:natPlus):= n <= m.
Lemma lep_preorder: RelationClasses.PreOrder lep.
Proof.
  constructor;
  hnf; intros;
  try apply NPeano.Nat.le_preorder.
  destruct x, y, z;
    unfold lep in *; simpl in *;
    omega.
Qed.

Definition natPlus_kiM: KripkeIntuitionisticModel natPlus:=
    Build_KripkeIntuitionisticModel _ _ lep_preorder.

Definition sumAlg: @SeparationAlgebra _ sum_Join.
Proof. constructor; intros.
       - inversion H; subst.
         rewrite NPeano.Nat.add_comm in H0;
         constructor; auto.
       - inversion H; inversion H0; subst.
         exists (Build_natPlus (my+mz)
            ltac:(destruct my, mz; simpl in *; omega))
         ; split; try constructor; simpl;
         omega.
Qed.

(* downwards-closed*)
Instance sumAlg_dSA:
  @DownwardsClosedSeparationAlgebra _ sum_Join natPlus_kiM.
Proof.
  hnf; intros.
  inversion H;  subst.
  simpl in H0.
  destruct (le_lt_dec n m1).
  - exists n, 0; split; constructor; simpl; try omega.
  - exists m1, (n - m1); split; constructor; simpl; try omega.
Qed.

  (* upwards-closed*)
  Instance sumAlg_uSA:
    @UpwardsClosedSeparationAlgebra _ sum_Join indexAlg_kiM.
  Proof.
    hnf; intros.
    simpl in H0, H1.
    inversion H; subst.
    exists (n1 + n2); split; simpl; try constructor; try omega.
  Qed.
  
  (* Nonpositive*)
  Instance minAlg_nonpositive:
    @NonpositiveSeparationAlgebra _ indexAlg_kiM  min_Join.
  Proof.
    constructor; intro.
    hnf; intros. inversion H; subst; auto.
  Qed.

  (*Residual*)
  Instance minAlg_residual:
    @ResidualSeparationAlgebra _ indexAlg_kiM   min_Join.
  Proof.
    constructor; intro.
    exists n, n; split.
    constructor; reflexivity.
    reflexivity.
  Qed.

  (* Unital *)
  Instance minAlg_unital:
    @UnitalSeparationAlgebra _ indexAlg_kiM  min_Join.
  Proof.
    apply nonpos_unital_iff_residual.
    apply minAlg_nonpositive.
    apply minAlg_residual.
  Qed.

    
(***********************************)
(* HEAPS                           *)
(***********************************)

Section heaps.
  Context (addr val: Type).

Definition Heap: Type := addr -> option val.

Instance Heap_Join: Join Heap :=
  @fun_Join _ _ (@option_Join _ (equiv_Join)).

Instance Heap_SA: SeparationAlgebra Heap :=
  @fun_SA _ _ _ (@option_SA _ _ (equiv_SA)).

(** * Discrete heap *)
Instance discHeap_kiM: KripkeIntuitionisticModel Heap :=
  identity_kiM.

Program Instance discHeap_ikiM: IdentityKripkeIntuitionisticModel Heap.

(*Downwards-closed*)
Instance discHeap_dSA:
  @DownwardsClosedSeparationAlgebra Heap Heap_Join discHeap_kiM.
Proof.
  eapply ikiM_dSA.
Qed.

(*Upwards-closed*)
Instance discHeap_uSA:
  @UpwardsClosedSeparationAlgebra Heap Heap_Join discHeap_kiM.
Proof.
  eapply ikiM_uSA.
Qed.

(*Empty heap is decreasing element*)
Lemma discHeap_empty_decreasing:
  @nonpositive Heap discHeap_kiM Heap_Join (fun _ => None).
Proof. hnf; intros.
       hnf.
       extensionality x; specialize (H  x).
       inversion H; reflexivity.
Qed.

(*Unital*)
Instance discHeap_unital:
  @UnitalSeparationAlgebra Heap discHeap_kiM Heap_Join.
Proof.
  constructor; intros.
  - exists (fun _ => None); split.
    + exists n; split.
      * hnf; intros.
        unfold join.
        destruct (n x); constructor.
      * hnf; intros.
        reflexivity.
    + hnf; intros.
      hnf; extensionality x.
      specialize (H x).
      inversion H; reflexivity.
  - hnf; intros.
    inversion H; subst.
    apply H0 in H1.
    inversion H1.
    reflexivity.
Qed.

(*Residual*)
Instance discHeap_residual:
  @ResidualSeparationAlgebra Heap discHeap_kiM Heap_Join.
Proof. apply unital_is_residual; apply discHeap_unital. Qed.
  

(** * Monotonic heap*)
Instance monHeap_kiM: KripkeIntuitionisticModel Heap :=
  @fun_kiM _ _ (@option_kiM _ (identity_kiM)).

Instance identity_ikiM (A: Type): @IdentityKripkeIntuitionisticModel _ (@identity_kiM A).
Proof.
  constructor; intros; auto.
Qed.

(* Downwards-closed*)
Instance monHeap_dSA:
  @DownwardsClosedSeparationAlgebra Heap Heap_Join monHeap_kiM.
Proof.
  eapply fun_dSA.
  eapply option_dSA.
  eapply ikiM_dSA.
Qed.  

(*Upwards-closed*)
Definition monHeap_uSA:
  @UpwardsClosedSeparationAlgebra Heap Heap_Join monHeap_kiM.
Proof.
  eapply fun_uSA.
  eapply option_uSA.
  - eapply ikiM_uSA.
  - apply equiv_SA.
  - apply equiv_gcSA.
Qed.

(* Nonpositive *)
Instance monHeap_nonpositive:
  @NonpositiveSeparationAlgebra Heap monHeap_kiM Heap_Join .
Proof.
  constructor; intros.
  hnf; intros.
  hnf; intros.
  specialize (H x0).
  inversion H; constructor.
  - reflexivity.
  - inversion H3. subst; reflexivity.
Qed.

(* Residual *)
Instance monHeap_residual:
  @ResidualSeparationAlgebra Heap monHeap_kiM Heap_Join .
Proof.
  constructor; intros.
  exists (fun _ => None).
  hnf; intros.
  exists n; split.
  - hnf; intros x; destruct (n x); constructor.
  - reflexivity.
Qed.

(* Unital *)
Instance monHeap_unital:
  @UnitalSeparationAlgebra Heap monHeap_kiM Heap_Join .
Proof.
  apply nonpos_unital_iff_residual.
  apply monHeap_nonpositive.
  apply monHeap_residual.
Qed.
  
End heaps.


Class SeparationAlgebra_unit (worlds: Type) {J: Join worlds} := {
  unit: worlds;
  unit_join: forall n, join n unit n;
  unit_spec: forall n m, join n unit m -> n = m
}.

(***********************************)
(* More examples                   *)
(***********************************)
(*
Program Definition nat_le_kiM: KripkeIntuitionisticModel nat := 
  Build_KripkeIntuitionisticModel nat (fun a b => a <= b) _.
Next Obligation.
  constructor; hnf; intros.
  + apply le_n.
  + eapply NPeano.Nat.le_trans; eauto.
Qed.

(* TODO: Probably don't need this one. *)
Program Definition SAu_kiM (worlds: Type) {J: Join worlds} {SA: SeparationAlgebra worlds} {SAu: SeparationAlgebra_unit worlds} : KripkeIntuitionisticModel worlds :=
  Build_KripkeIntuitionisticModel worlds (fun a b => exists b', join b b' a) _.
Next Obligation.
  constructor; hnf; intros.
  + exists unit; apply unit_join.
  + destruct H as [? ?], H0 as [? ?].
    destruct (join_assoc _ _ _ _ _ H0 H) as [? [? ?]].
    exists x2; auto.
Qed.

Definition Stack (LV val: Type): Type := LV -> val.

Definition StepIndex_kiM (worlds: Type) {kiM: KripkeIntuitionisticModel worlds}: KripkeIntuitionisticModel (nat * worlds) := @prod_kiM _ _ nat_le_kiM kiM.

Definition StepIndex_Join (worlds: Type) {J: Join worlds}: Join (nat * worlds) :=
  @prod_Join _ _ (equiv_Join _) J.

Definition StepIndex_SA (worlds: Type) {J: Join worlds} {SA: SeparationAlgebra worlds}:
  @SeparationAlgebra (nat * worlds) (StepIndex_Join worlds) := @prod_SA _ _ _ _ (equiv_SA _) SA.

Definition StepIndex_dSA (worlds: Type) {kiM: KripkeIntuitionisticModel worlds}
           {J: Join worlds} {dSA: DownwardsClosedSeparationAlgebra worlds}:
  @DownwardsClosedSeparationAlgebra (nat * worlds) (StepIndex_Join worlds) (StepIndex_kiM worlds):= @prod_dSA _ _ _ _ _ _ (@identity_dSA _ nat_le_kiM) dSA.

*)