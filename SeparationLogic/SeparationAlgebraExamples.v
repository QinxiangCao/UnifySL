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

  
(** *Minimum Algebra on NAT*)

Inductive sum_Join: nat -> nat -> nat -> Prop:=
  |sum_j x y z: x + y = z -> sum_Join x y z.

Definition sumAlg: @SeparationAlgebra _ sum_Join.
Proof. constructor; intros.
       - inversion H; subst.
         rewrite NPeano.Nat.add_comm;
         constructor; auto.
       - inversion H; inversion H0; subst.
         exists (my+mz)
         ; split; try constructor; simpl;
         omega.
Qed.

(* downwards-closed*)
Instance sumAlg_dSA:
  @DownwardsClosedSeparationAlgebra _ sum_Join nat_kiM.
Proof.
  hnf; intros.
  simpl in H0.
  inversion H;  subst.
  destruct (le_lt_dec n m1).
  - exists n, 0; split; constructor; simpl; try omega.
  - exists m1, (n - m1); split; constructor; simpl; try omega.
Qed.

  (* upwards-closed*)
  Instance sumAlg_uSA:
    @UpwardsClosedSeparationAlgebra _ sum_Join nat_kiM.
  Proof.
    hnf; intros.
    simpl in H0, H1.
    inversion H; subst.
    exists (n1 + n2); split; simpl; try constructor; try omega.
  Qed.
  
  (* The only nonpositive is 0*)
  Lemma sumAlg_zero_decreasing:
  @nonpositive nat nat_kiM sum_Join 0.
  Proof. hnf; intros.
       hnf.
       inversion H; subst; omega.
  Qed.
  Lemma sumAlg_zero_decreasing_only:
    forall x,
  @nonpositive nat nat_kiM sum_Join x -> x = 0.
  Proof.
    intros.
    specialize (H 1 (x+1) ltac:(constructor; omega)).
    simpl in H; omega.
  Qed.
  
  (* Unital *)
  Instance sumAlg_unital:
    @UnitalSeparationAlgebra _ nat_kiM  sum_Join.
  Proof.
    constructor; intros.
    - exists 0; split.
      + exists n; split; simpl; try constructor; omega.
      + hnf; intros.
        inversion H; subst; simpl;
        omega.
    - apply sumAlg_zero_decreasing_only in H0; subst.
      simpl in H.
      replace n with 0 by omega.
      apply sumAlg_zero_decreasing.
  Qed.
  
  (*Residual*)
  Instance sumAlg_residual:
    @ResidualSeparationAlgebra _ nat_kiM sum_Join.
  Proof.
    constructor; intro.
    exists n, 0; split.
    constructor; omega.
    simpl; omega.
  Qed.


(** *Minimum Algebra on Positive integers*)
  
  Record natPlus: Type:=
   natp { nat_p:> nat;
      is_pos: 0 < nat_p}.


Inductive sump_Join: natPlus -> natPlus -> natPlus -> Prop:=
  |sump_j (x y z:natPlus): x + y = z -> sump_Join x y z.

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

Definition sumpAlg: @SeparationAlgebra _ sump_Join.
Proof. constructor; intros.
       - inversion H; subst.
         rewrite NPeano.Nat.add_comm in H0;
           constructor; auto.
       - inversion H; inversion H0; subst.
         exists (natp (my+mz)
                          ltac:(destruct my, mz; simpl in *; omega))
         ; split; try constructor; simpl;
         omega.
Qed.

(* it is NOT downwards-closed*)
Instance sumpAlg_dSA:
  @DownwardsClosedSeparationAlgebra _ sump_Join natPlus_kiM.
Proof.
  hnf; intros.
  simpl in H0.
  inversion H;  subst.
Abort.
 
(* upwards-closed*)
Instance sumpAlg_uSA:
  @UpwardsClosedSeparationAlgebra _ sump_Join natPlus_kiM.
Proof.
  hnf; intros.
  simpl in H0, H1.
  inversion H; subst.
  unfold lep in *.
  destruct m1, m2, m, n1, n2; simpl in *.
  exists (natp (nat_p3 + nat_p4) ltac:(simpl in *; omega));
    split; simpl; try constructor; try omega.
  reflexivity.
  unfold lep; simpl.
  rewrite <- H2; omega.
Qed.
  
  (*it is NOT Residual*)
  Instance sumpAlg_residual:
    @ResidualSeparationAlgebra _ natPlus_kiM sump_Join.
  Proof.
    constructor; intro.
    unfold residue.
  Abort.



(** *sum Algebra inverted*)
  
Definition natinv_kiM: KripkeIntuitionisticModel nat.
Proof. eapply (@Build_KripkeIntuitionisticModel nat ge).
       constructor.
       - hnf; intros.
         apply NPeano.Nat.le_preorder.
       - hnf; intros.
         eapply NPeano.Nat.le_preorder; eauto.
Defined.
  
Definition suminvAlg: @SeparationAlgebra _ sum_Join.
Proof. constructor; intros.
       - inversion H; subst.
         rewrite NPeano.Nat.add_comm;
         constructor; auto.
       - inversion H; inversion H0; subst.
         exists (my+mz)
         ; split; try constructor; simpl;
         omega.
Qed.

(* downwards-closed*)
Instance suminvAlg_dSA:
  @DownwardsClosedSeparationAlgebra _ sum_Join natinv_kiM.
Proof.
  hnf; intros.
  simpl in H0.
  inversion H;  subst.
  destruct (le_ge_dec m1 m2).
  - exists m1, (n- m1). split; constructor; simpl; try omega.
  - exists (n-m2), m2. split; constructor; simpl; try omega.
Qed.

(* upwards-closed*)
Instance suminvAlg_uSA:
  @UpwardsClosedSeparationAlgebra _ sum_Join natinv_kiM.
Proof.
  hnf; intros.
  simpl in H0, H1.
  inversion H; subst.
  exists (n1 + n2); split; simpl; try constructor; try omega.
Qed.


  (*Residual*)
  Instance suminvAlg_nonpositive:
    @NonpositiveSeparationAlgebra _ natinv_kiM sum_Join.
  Proof.
    constructor; intro.
    hnf; intros.
    inversion H; subst.
    hnf. omega.
  Qed.

  
  (*Residual*)
  Instance suminvAlg_residual:
    @ResidualSeparationAlgebra _ natinv_kiM sum_Join.
  Proof.
    constructor; intro.
    exists 0, n; split.
    constructor; omega.
    reflexivity.
  Qed.
  
  (* Unital *)
  Instance suminvAlg_unital:
    @UnitalSeparationAlgebra _ natinv_kiM  sum_Join.
  Proof.
    apply nonpos_unital_iff_residual.
    apply suminvAlg_nonpositive.
    apply suminvAlg_residual.
  Qed.
End nat_algs.


(***********************************)
(* ALGEBRAS ON RATIONALS           *)
(***********************************)

Require Import Coq.QArith.QArith.
(*Require Import Coq.Reals.Rdefinitions.*)
(*Q overloads <= !*)
Require Import Ring.


(** *Minimum Algebra on Positive rationals*)
  (*
  Record QPlus: Type:=
   qp { q_p:> Q;
      qis_pos: (0 < q_p)}.


  Inductive sumqp_Join: QPlus -> QPlus -> QPlus -> Prop:=
  |sumqp_j (x y z:QPlus): (x + y) = z -> sumqp_Join x y z.

Definition leqp (n m:QPlus):= (n <= m).
Lemma leqp_preorder: RelationClasses.PreOrder leqp.
Proof.
  constructor;
  hnf; intros.
  unfold leqp.
  - apply Qle_refl.
  - eapply Qle_trans; eauto.
Qed.

Definition QPlus_kiM: KripkeIntuitionisticModel QPlus:=
    Build_KripkeIntuitionisticModel _ _ leqp_preorder.

Definition qpAlg: @SeparationAlgebra _ sumqp_Join.
Proof. constructor; intros.
       - inversion H; subst.
         destruct m1, m2, m.
         simpl in *.
         rewrite Qplus_comm in H0. ;
           constructor; auto.
       - inversion H; inversion H0; subst.
         assert (HH: 0 < (my+mz)).
         { destruct my, mz; simpl.
           replace 0 with (0+0) by reflexivity.
           apply Qplus_lt_le_compat; auto.
           apply Qlt_le_weak; auto. }
           
         exists (qp (my+mz) HH); split; simpl;
         constructor; simpl.
         reflexivity.
         rewrite <- H5, <-H1.
         apply Qplus_assoc.
Qed.

(* it is NOT downwards-closed*)
Instance sumqpAlg_dSA:
  @DownwardsClosedSeparationAlgebra _ sumqp_Join QPlus_kiM.
Proof.
  hnf; intros.
  simpl in H0.
  unfold leqp in H0.
  inversion H;  subst.
  rewrite <- H1 in H0.
  destruct (Qlt_le_dec (n/(1+1)) m1).
  assert (HH: 0 < n / (1 + 1)).
  { apply Qlt_shift_div_l.
    - rewrite <- (Qplus_0_l 0).
      apply Qplus_lt_le_compat.
      unfold Qlt; simpl; omega.
      unfold Qle; simpl; omega.
    - rewrite Qmult_0_l.
      destruct n; auto. }
  exists (qp (n / (1 + 1)) HH), (qp (n / (1 + 1)) HH); split.
  - constructor; simpl.
    
  simpl.
  - exists bindings_list
Abort.
 
(* upwards-closed*)
Instance sumpAlg_uSA:
  @UpwardsClosedSeparationAlgebra _ sump_Join natPlus_kiM.
Proof.
  hnf; intros.
  simpl in H0, H1.
  inversion H; subst.
  unfold lep in *.
  destruct m1, m2, m, n1, n2; simpl in *.
  exists (natp (nat_p3 + nat_p4) ltac:(simpl in *; omega));
    split; simpl; try constructor; try omega.
  reflexivity.
  unfold lep; simpl.
  rewrite <- H2; omega.
Qed.
  
  (*it is NOT Residual*)
  Instance sumpAlg_residual:
    @ResidualSeparationAlgebra _ natPlus_kiM sump_Join.
  Proof.
    constructor; intro.
    unfold residue.
  Abort.
*)

    
(***********************************)
(* Regular HEAPS                   *)
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


(***********************************)
(* TYPED HEAPS                     *)
(***********************************)

Section typed_heaps.

  Inductive htype:=
  |char
  |short1
  |short2.
  
 Record THeap: Type :=
    { theap:> nat -> option htype;
      th_wf1: forall n, theap n = Some short1 <->
                   theap (S n) = Some short2}.
Instance THeap_Join': Join (nat -> option htype) :=
  @fun_Join _ _ (@option_Join _ (equiv_Join)).
  
Inductive THeap_Join: Join THeap :=
| th_join (h1 h2 h3: THeap): THeap_Join' h1 h2 h3 ->
                             THeap_Join h1 h2 h3.

Instance THeap_SA': @SeparationAlgebra _ THeap_Join':=
  @fun_SA _ _ _ (@option_SA _ _ (equiv_SA)).

Instance THeap_SA: @SeparationAlgebra THeap THeap_Join.
Proof.
  constructor; intros.
  - inversion H; subst.
    constructor. apply join_comm; auto.
  - inversion H; inversion H0; subst.
    pose ( join_assoc _ _  _ _ _ H1 H5) as HH.
    destruct HH as [myz' HH].
    assert (forall n, myz' n = Some short1 <->
                 myz' (S n) = Some short2).
    { intros; split.
    
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