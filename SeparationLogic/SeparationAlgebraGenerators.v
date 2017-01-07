Require Import Coq.Logic.ChoiceFacts.
Require Import Coq.Logic.ClassicalChoice.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.

(***********************************)
(* Separation Algebra Generators   *)
(***********************************)

Section unitSA.
  Definition unit_Join: Join unit:=  (fun _ _ _ => True).

  Definition unit_SA: @SeparationAlgebra unit unit_Join.
  Proof.
    constructor.
    + intros. constructor.
    + intros; exists tt; split; constructor.
  Qed.

  Program Definition unit_kiM: KripkeIntuitionisticModel unit:=
    Build_KripkeIntuitionisticModel unit (fun _ _=> True) _.
  Next Obligation.
    constructor; auto.
  Defined.
  
  
  (* Unit algebra is downwards closed *)
  Definition unit_dSA:
    @DownwardsClosedSeparationAlgebra unit (unit_Join) unit_kiM.
  Proof.
    intros; exists tt, tt; intuition.
  Qed.

  (* Unit algebra is downwards closed *)
  Definition unit_uSA:
    @UpwardsClosedSeparationAlgebra unit (unit_Join) unit_kiM.
  Proof.
    intros; exists tt; intuition.
  Qed.

  (*Nonpositive*)
  Instance unit_nonposSA:
    @NonpositiveSeparationAlgebra unit unit_kiM (unit_Join).
  Proof.
    constructor; intros; hnf; intros.
    constructor.
  Qed.

  Instance residual_nonposSA:
    @ResidualSeparationAlgebra unit unit_kiM (unit_Join).
  Proof.
    constructor; intros.
    exists tt; exists tt; split; constructor.
  Qed.
  
  Definition unital_nonposSA:
    @UnitalSeparationAlgebra unit unit_kiM (unit_Join).
  Proof.
    apply nonpos_unital_iff_residual; auto.
    apply unit_nonposSA.
    apply residual_nonposSA.
  Qed.

End unitSA.


Section equivSA.
  Context {worlds: Type}.
  
  Definition equiv_Join: Join worlds:=  (fun a b c => a = c /\ b = c).

  Definition equiv_SA: @SeparationAlgebra worlds equiv_Join.
  Proof.
    constructor.
    + intros.
      inversion H.
      split; tauto.
    + intros.
      simpl in *.
      destruct H, H0.
      subst mx my mxy mz.
      exists mxyz; do 2 split; auto.
  Qed.

  (* Identity algebra is downwards closed *)
  (* Identity is NOT upwards closed *)
  Definition identity_dSA {kiM: KripkeIntuitionisticModel worlds}:
    @DownwardsClosedSeparationAlgebra worlds (equiv_Join) kiM.
  Proof.
    intros until m2; intros.
    destruct H; subst m1 m2.
    exists n, n; do 2 split; auto.
  Qed.
  
  Program Definition identity_kiM: KripkeIntuitionisticModel worlds := Build_KripkeIntuitionisticModel worlds (fun a b => a = b) _.
  Next Obligation.
    constructor; hnf; intros.
    + auto.
    + subst; auto.
  Qed.
  
  Definition equiv_gcSA: @GarbageCollectSeparationAlgebra
                           worlds identity_kiM equiv_Join.
  Proof.
    constructor; intros.
    inversion H; subst.
    constructor.
  Qed.

  Instance identity_ikiM: @IdentityKripkeIntuitionisticModel worlds (identity_kiM).
  Proof.
    constructor.
    intros; auto.
  Qed.

  Definition ikiM_dSA {kiM: KripkeIntuitionisticModel worlds} {ikiM: IdentityKripkeIntuitionisticModel worlds} {J: Join worlds}: DownwardsClosedSeparationAlgebra worlds.
  Proof.
    intros until m2; intros.
    apply Korder_identity in H0.
    subst n.
    exists m1, m2.
    split; [| split]; auto; reflexivity.
  Qed.

  Definition ikiM_uSA {kiM: KripkeIntuitionisticModel worlds} {ikiM: IdentityKripkeIntuitionisticModel worlds} {J: Join worlds}: UpwardsClosedSeparationAlgebra worlds.
  Proof.
    intros until n2; intros.
    apply Korder_identity in H0.
    apply Korder_identity in H1.
    subst n1 n2.
    exists m.
    split; auto; reflexivity.
  Qed.

  (*Identity is NOT necessarily nonpositive*)

  (*Identity is NOT necessarily unital*)

  (*Identity is NOT necessarily residual*)
  
End equivSA.

Section optionSA.
  Context (worlds: Type).
  
  Inductive option_join {J: Join worlds}: option worlds -> option worlds -> option worlds -> Prop :=
  | None_None_join: option_join None None None
  | None_Some_join: forall a, option_join None (Some a) (Some a)
  | Some_None_join: forall a, option_join (Some a) None (Some a)
  | Some_Some_join: forall a b c, join a b c -> option_join (Some a) (Some b) (Some c).

  Definition option_Join {SA: Join worlds}: Join (option worlds):=
    (@option_join SA).
  
  Definition option_SA
             {J: Join worlds}
             {SA: SeparationAlgebra worlds}:
    @SeparationAlgebra (option worlds) (option_Join).
  Proof.
    constructor.
    + intros.
      simpl in *.
      destruct H.
    - apply None_None_join.
    - apply Some_None_join.
    - apply None_Some_join.
    - apply Some_Some_join.
      apply join_comm; auto.
      + intros.
        simpl in *.
        inversion H; inversion H0; clear H H0; subst;
        try inversion H4; try inversion H5; try inversion H6; subst;
        try congruence;
        [.. | destruct (join_assoc _ _ _ _ _ H1 H5) as [? [? ?]];
           eexists; split; apply Some_Some_join; eassumption];
        eexists; split;
        try solve [ apply None_None_join | apply Some_None_join
                    | apply None_Some_join | apply Some_Some_join; eauto].
  Qed.

  Inductive option_order
            {kiM: KripkeIntuitionisticModel worlds}: option worlds -> option worlds -> Prop :=
  | None_None_order: option_order None None
  | Some_None_order: forall a, option_order (Some a) None
  | Some_Some_order: forall a b, Korder a b -> option_order (Some a) (Some b).

  Program Definition option_kiM {kiM: KripkeIntuitionisticModel worlds}: KripkeIntuitionisticModel (option worlds) :=
    Build_KripkeIntuitionisticModel (option worlds) (@option_order _) _.
  Next Obligation.
    pose proof Korder_PreOrder as H_PreOrder.
    constructor; hnf; intros.
    + destruct x.
    - constructor; reflexivity.
    - constructor.
      + inversion H; inversion H0; subst; try first [congruence | constructor].
        inversion H5; subst.
        etransitivity; eauto.
  Defined.

  (* Downwards closed*)
  Program Definition option_dSA
             {J: Join worlds}
             {kiM: KripkeIntuitionisticModel worlds}
             (dSA: DownwardsClosedSeparationAlgebra worlds)
             : @DownwardsClosedSeparationAlgebra (option worlds) (option_Join) (option_kiM).
  Proof.
    hnf; intros.
    inversion H; subst.
    - inversion H0; subst.
      + exists None, None; repeat split; try constructor.
      + exists (Some a), None; repeat split; try constructor.
    - inversion H0; subst.
      exists None, (Some a0); repeat split; try constructor; auto.
    - inversion H0; subst.
      exists (Some a0), None; repeat split; try constructor; auto.
    - inversion H0; subst.
      destruct
        (dSA  _ _ _ _ H1 H4) as [n1 [n2 [HH1 [HH2 HH3]]]].
      exists (Some n1), (Some n2); repeat split; try constructor; auto.
  Qed.

  (* Upwards closed IF the algebra is Nonpositive*)
  Program Definition option_uSA
             {J: Join worlds}
             {kiM: KripkeIntuitionisticModel worlds}
             (dSA: UpwardsClosedSeparationAlgebra worlds)
             {SA: SeparationAlgebra worlds}
             {gcSA: GarbageCollectSeparationAlgebra worlds}
    : @UpwardsClosedSeparationAlgebra (option worlds) (option_Join) (option_kiM).
  Proof.
    hnf; intros.
    inversion H0; [ | | inversion H1]; subst.
    - exists n2; inversion H; subst; split; auto;
      destruct n2; constructor.
    - exists n2; inversion H; subst; split; auto;
      destruct n2; constructor.
      + inversion H1.
      + inversion H; subst.
        apply join_comm in H6.
        apply join_has_order1 in H6.
        inversion H1; subst.
        transitivity b; auto.
    - exists (Some b); split; try constructor.
      inversion H; subst; auto.
    - exists (Some b); split; try constructor.
      transitivity (Some a); auto.
      inversion H; subst.
      constructor; eapply join_has_order1. eassumption.
    - inversion H; subst.
      destruct (dSA _ _ _ _ _ H6 H2 H5) as [n [HH1 HH2]].
      exists (Some n); split; constructor; auto.
  Qed.

  

End optionSA.
  
Section exponentialSA.
  Definition fun_Join (A B: Type) {J_B: Join B}: Join (A -> B) :=
    (fun a b c => forall x, join (a x) (b x) (c x)).

  Definition fun_SA
             (A B: Type)
             {Join_B: Join B}
             {SA_B: SeparationAlgebra B}: @SeparationAlgebra (A -> B) (fun_Join A B).
  Proof.
    constructor.
    + intros.
      simpl in *.
      intros x; specialize (H x).
      apply join_comm; auto.
    + intros.
      simpl in *.
      destruct (choice (fun x fx => join (my x) (mz x) fx /\ join (mx x) fx (mxyz x) )) as [myz ?].
    - intros x; specialize (H x); specialize (H0 x).
      apply (join_assoc _ _ _ _ _ H H0); auto.
    - exists myz; firstorder.
  Qed.

  
  Program Definition fun_kiM (A B: Type) {kiM_B: KripkeIntuitionisticModel B}: KripkeIntuitionisticModel (A -> B) :=
    Build_KripkeIntuitionisticModel _ (fun a b => forall x, Korder (a x) (b x)) _.
  Next Obligation.
    pose proof Korder_PreOrder as H_PreOrder.
    constructor; hnf; intros.
    + reflexivity.
    + specialize (H x0); specialize (H0 x0).
      etransitivity; eauto.
  Qed.

  (* Exponential is downwards closed *)
  Program Definition fun_dSA 
             (A B: Type)
             {J_B: Join B}
             {kiM_B: KripkeIntuitionisticModel B}
             (dSA_B: DownwardsClosedSeparationAlgebra B)
             : @DownwardsClosedSeparationAlgebra (A -> B) (fun_Join A B) (fun_kiM A B).
  Proof.
    hnf; intros.
    unfold join, fun_Join in H.
    unfold Korder, fun_kiM in H0.
    destruct (choice (fun x nn => join (fst nn) (snd nn) (n x) /\
                               Korder (fst nn) (m1 x) /\
                               Korder (snd nn) (m2 x)))
      as [nn H1].
    intros x.
    destruct (dSA_B (m x) (n x) (m1 x) (m2 x) (H x) (H0 x)) as [x1 [x2 ?]];
      exists (x1, x2); auto.
    exists (fun x => fst (nn x)), (fun x => snd (nn x)).
    simpl; repeat split; intros x; specialize (H1 x); destruct H1 as [H1 [H2 H3]];
    assumption.
  Qed.

  
  (* Exponential is upwards closed *)
  Program Definition fun_uSA 
             (A B: Type)
             {J_B: Join B}
             {kiM_B: KripkeIntuitionisticModel B}
             (uSA_B: UpwardsClosedSeparationAlgebra B)
             : @UpwardsClosedSeparationAlgebra (A -> B) (fun_Join A B) (fun_kiM A B).
  Proof.
    hnf; intros.
    unfold join, fun_Join in H.
    unfold Korder, fun_kiM in H0.
    destruct (choice (fun x n => join (n1 x) (n2 x) (n) /\
                               Korder (m x) (n)))
      as [n H2].
    intros x.
    destruct (uSA_B (m1 x) (m2 x) (m x) (n1 x) (n2 x) (H x) (H0 x)) as [x1 [x2 ?]]; auto;
    exists x1; auto.

    exists n; split; hnf; intros x; specialize (H2 x); destruct H2; auto.
  Qed.
  
  (* Exponential is nonpositive *)
  Program Definition fun_npSA 
             (A B: Type)
             {J_B: Join B}
             {kiM_B: KripkeIntuitionisticModel B}
             (np_B: NonpositiveSeparationAlgebra B)
             : @NonpositiveSeparationAlgebra (A -> B) (fun_kiM A B)  (fun_Join A B).
  Proof.
    constructor; intros.
    hnf; intros.
    hnf; intros.
    specialize (H x0).
    eapply all_nonpositive; eauto.
  Qed.

    
  (* Exponential is Unital*)
  Program Definition fun_unitSA 
             (A B: Type)
             {J_B: Join B}
             {kiM_B: KripkeIntuitionisticModel B}
             (np_B: UnitalSeparationAlgebra B)
             : @UnitalSeparationAlgebra (A -> B) (fun_kiM A B)  (fun_Join A B).
  Proof.
    constructor; intros.
    - destruct (choice (fun x mx => residue (n x) mx /\ nonpositive mx)) as [M HH].
      { intros;
        specialize (nonpos_exists (n x)); intros [y HH];
        exists y; auto. }
      exists M; split.
      + cut (forall x, residue (n x) (M x)).
        * clear; unfold residue; intros.
          apply choice in H; destruct H as [n' H].
          exists n'; split; hnf; intros x;
          specialize (H x); destruct H; auto.
        * intros x; specialize (HH x); destruct HH; auto.
      + unfold nonpositive; intros.
        unfold join, fun_Join in H.
        hnf; intros x.
        specialize (HH x); destruct HH as [ _ HH].
        apply HH.
        auto.
    - hnf; intros.
      hnf; intros.
      eapply nonpos_down.
      eapply H0.
    
    unfold residue, nonpositive.
    
    unfold join, fun_Join.
    unfold Korder, fun_kiM.
Abort.
(*    
    - destruct (choice (fun )).
    hnf; intros.
    hnf; intros.
    specialize (H x0).
    eapply all_nonpositive; eauto.
  Qed.
*)    
End exponentialSA.

Section sumSA.
  Inductive sum_worlds {worlds1 worlds2}: Type:
    Type:=
  | lw (w:worlds1): sum_worlds
  | rw (w:worlds2): sum_worlds.

  Inductive sum_join {A B: Type} {J1: Join A} {J2: Join B}:
    @sum_worlds A B ->
    @sum_worlds A B ->
    @sum_worlds A B-> Prop :=
  | left_join a b c:
      join a b c ->
      sum_join (lw a) (lw b) (lw c)
  | right_join a b c:
      join a b c ->
      sum_join (rw a) (rw b) (rw c).

  Definition sum_Join (A B: Type) {Join_A: Join A} {Join_B: Join B}: Join (@sum_worlds A B) :=
    (@sum_join A B Join_A Join_B).

  Definition sum_SA (A B: Type) {Join_A: Join A} {Join_B: Join B} {SA_A: SeparationAlgebra A} {SA_B: SeparationAlgebra B}: @SeparationAlgebra (@sum_worlds A B) (sum_Join A B).
  Proof.
    constructor.
    - intros; inversion H;
      constructor; apply join_comm; auto.
    - intros.
      inversion H; subst;
      inversion H0;
      destruct (join_assoc _ _ _ _ _ H1 H3) as [myz [HH1 HH2]].
      + exists (lw myz); split; constructor; auto.
      + exists (rw myz); split; constructor; auto.
  Qed.

  
  (*Disjoint order (parallel composition)*)
  Inductive disjsum_order {A B: Type}
            {kiM_A: KripkeIntuitionisticModel A}
            {kiM_B: KripkeIntuitionisticModel B}:
    @sum_worlds A B -> @sum_worlds A B -> Prop:=
  | lordd a1 a2: disjsum_order (lw a1) (lw a2)
  | rordd b1 b2: disjsum_order (rw b1) (rw b2).

  Program Definition disjsum_kiM (A B: Type) {kiM_A: KripkeIntuitionisticModel A} {kiM_B: KripkeIntuitionisticModel B}: KripkeIntuitionisticModel (@sum_worlds A B) :=
    Build_KripkeIntuitionisticModel _ disjsum_order  _.
  Next Obligation.
    constructor; hnf; intros.
    - destruct x; constructor.
    - inversion H; subst; inversion H0; subst;
      constructor.
  Qed.

  (*Linear order (series composition)*)
  Inductive ordsum_order {A B: Type}
            {kiM_A: KripkeIntuitionisticModel A}
            {kiM_B: KripkeIntuitionisticModel B}:
    @sum_worlds A B -> @sum_worlds A B -> Prop:=
  | lordo a1 a2: ordsum_order (lw a1) (lw a2)
  | rordo b1 b2: ordsum_order (rw b1) (rw b2)
  | landr a b: ordsum_order (lw a) (rw b).

  Program Definition ordsum_kiM (A B: Type) {kiM_A: KripkeIntuitionisticModel A} {kiM_B: KripkeIntuitionisticModel B}: KripkeIntuitionisticModel (@sum_worlds A B) :=
    Build_KripkeIntuitionisticModel _ ordsum_order  _.
  Next Obligation.
    constructor; hnf; intros.
    - destruct x; constructor.
    - inversion H; subst; inversion H0; subst;
      constructor.
  Qed.

End sumSA.

Section productSA.
  
  Definition prod_Join (A B: Type) {Join_A: Join A} {Join_B: Join B}: Join (A * B) :=
    (fun a b c => join (fst a) (fst b) (fst c) /\ join (snd a) (snd b) (snd c)).

  Definition prod_SA (A B: Type) {Join_A: Join A} {Join_B: Join B} {SA_A: SeparationAlgebra A} {SA_B: SeparationAlgebra B}: @SeparationAlgebra (A * B) (prod_Join A B).
  Proof.
    constructor.
    + intros.
      simpl in *.
      destruct H; split;
      apply join_comm; auto.
    + intros.
      simpl in *.
      destruct H, H0.
      destruct (join_assoc _ _ _ _ _ H H0) as [myz1 [? ?]].
      destruct (join_assoc _ _ _ _ _ H1 H2) as [myz2 [? ?]].
      exists (myz1, myz2).
      do 2 split; auto.
  Qed.

  Program Definition prod_kiM (A B: Type) {kiM_A: KripkeIntuitionisticModel A} {kiM_B: KripkeIntuitionisticModel B}: KripkeIntuitionisticModel (A * B) :=
    Build_KripkeIntuitionisticModel _ (fun a b => Korder (fst a) (fst b) /\ Korder (snd a) (snd b)) _.
  Next Obligation.
    pose proof @Korder_PreOrder _ kiM_A as H_PreOrder_A.
    pose proof @Korder_PreOrder _ kiM_B as H_PreOrder_B.
    constructor; hnf; intros.
    + split; reflexivity.
    + destruct H, H0.
      split; etransitivity; eauto.
  Qed.

  Definition prod_dSA {A B: Type} {kiM_A: KripkeIntuitionisticModel A} {kiM_B: KripkeIntuitionisticModel B} {Join_A: Join A} {Join_B: Join B} {dSA_A: DownwardsClosedSeparationAlgebra A} {dSA_B: DownwardsClosedSeparationAlgebra B}: @DownwardsClosedSeparationAlgebra (A * B) (@prod_Join _ _ Join_A Join_B) (@prod_kiM _ _ kiM_A kiM_B).
  Proof.
    intros until m2; intros.
    destruct H, H0.
    destruct (join_Korder_down _ _ _ _ H H0) as [fst_n1 [fst_n2 [? [? ?]]]].
    destruct (join_Korder_down _ _ _ _ H1 H2) as [snd_n1 [snd_n2 [? [? ?]]]].
    exists (fst_n1, snd_n1), (fst_n2, snd_n2).
    do 2 split; simpl; auto.
  Qed.

  Definition prod_uSA {A B: Type} {kiM_A: KripkeIntuitionisticModel A} {kiM_B: KripkeIntuitionisticModel B} {Join_A: Join A} {Join_B: Join B} {uSA_A: UpwardsClosedSeparationAlgebra A} {uSA_B: UpwardsClosedSeparationAlgebra B}: @UpwardsClosedSeparationAlgebra (A * B) (@prod_Join _ _ Join_A Join_B) (@prod_kiM _ _ kiM_A kiM_B) .
  Proof.
    intros until n2; intros.
    destruct H, H0, H1.
    destruct (join_Korder_up _ _ _ _ _ H H0 H1) as [fst_n [? ?]].
    destruct (join_Korder_up _ _ _ _ _ H2 H3 H4) as [snd_n [? ?]].
    exists (fst_n, snd_n).
    do 2 split; simpl; auto.
  Qed.

End productSA.

Class SeparationAlgebra_unit (worlds: Type) {J: Join worlds} := {
                                                                 unit: worlds;
                                                                 unit_join: forall n, join n unit n;
                                                                 unit_spec: forall n m, join n unit m -> n = m
                                                               }.

(***********************************)
(* Preorder examples               *)
(***********************************)


(***********************************)
(* dSA uSA examples                *)
(***********************************)


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

Definition Heap (addr val: Type): Type := addr -> option val.

Instance Heap_Join (addr val: Type): Join (Heap addr val) :=
  @fun_Join _ _ (@option_Join _ (equiv_Join _)).

Instance Heap_SA (addr val: Type): SeparationAlgebra (Heap addr val) :=
  @fun_SA _ _ _ (@option_SA _ _ (equiv_SA _)).

Instance mfHeap_kiM (addr val: Type): KripkeIntuitionisticModel (Heap addr val) :=
  identity_kiM _.

Instance gcHeap_kiM (addr val: Type): KripkeIntuitionisticModel (Heap addr val) :=
  @fun_kiM _ _ (@option_kiM _ (identity_kiM _)).

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