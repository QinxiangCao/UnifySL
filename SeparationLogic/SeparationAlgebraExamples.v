Require Import Coq.Logic.ChoiceFacts.
Require Import Coq.Logic.ClassicalChoice.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.

(***********************************)
(* SA examples                     *)
(***********************************)

Definition identity_SA (worlds: Type): SeparationAlgebra worlds :=
  Build_SeparationAlgebra _ (fun a b c => a = c /\ b = c).

Definition identity_nSA (worlds: Type): @NormalSeparationAlgebra worlds (identity_SA worlds).
Proof.
  constructor.
  + intros.
    simpl in *.
    tauto.
  + intros.
    simpl in *.
    destruct H, H0.
    subst mx my mxy mz.
    exists mxyz; auto.
Qed.

Inductive option_join {worlds: Type} {SA: SeparationAlgebra worlds}: option worlds -> option worlds -> option worlds -> Prop :=
  | None_None_join: option_join None None None
  | None_Some_join: forall a, option_join None (Some a) (Some a)
  | Some_None_join: forall a, option_join (Some a) None (Some a)
  | Some_Some_join: forall a b c, join a b c -> option_join (Some a) (Some b) (Some c).

Definition option_SA (worlds: Type) {SA: SeparationAlgebra worlds}: SeparationAlgebra (option worlds) :=
  Build_SeparationAlgebra _ (@option_join worlds SA).

Definition option_nSA (worlds: Type) {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds}: @NormalSeparationAlgebra (option worlds) (option_SA worlds).
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

Definition fun_SA (A B: Type) {SA_B: SeparationAlgebra B}: SeparationAlgebra (A -> B) :=
  Build_SeparationAlgebra _ (fun a b c => forall x, join (a x) (b x) (c x)).

Definition fun_nSA (A B: Type) {SA_B: SeparationAlgebra B} {nSA_B: NormalSeparationAlgebra B}: @NormalSeparationAlgebra (A -> B) (fun_SA A B).
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

Definition prod_SA (A B: Type) {SA_A: SeparationAlgebra A} {SA_B: SeparationAlgebra B}: SeparationAlgebra (A * B) :=
  Build_SeparationAlgebra _ (fun a b c => join (fst a) (fst b) (fst c) /\ join (snd a) (snd b) (snd c)).

Definition prod_nSA (A B: Type) {SA_A: SeparationAlgebra A} {SA_B: SeparationAlgebra B} {nSA_A: NormalSeparationAlgebra A} {nSA_B: NormalSeparationAlgebra B}: @NormalSeparationAlgebra (A * B) (prod_SA A B).
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
    auto.
Qed.

Class SeparationAlgebra_unit (worlds: Type) {SA: SeparationAlgebra worlds} := {
  unit: worlds;
  unit_join: forall n, join n unit n;
  unit_spec: forall n m, join n unit m -> n = m
}.

(***********************************)
(* Preorder examples               *)
(***********************************)

Program Definition identity_kiM (worlds: Type): KripkeIntuitionisticModel worlds := Build_KripkeIntuitionisticModel worlds (fun a b => a = b) _.
Next Obligation.
  constructor; hnf; intros.
  + auto.
  + subst; auto.
Qed.

Definition identity_ikiM (worlds: Type): @IdentityKripkeIntuitionisticModel worlds (identity_kiM worlds).
Proof.
  constructor.
  intros; auto.
Qed.

Inductive option_order {worlds: Type} {kiM: KripkeIntuitionisticModel worlds}: option worlds -> option worlds -> Prop :=
  | None_None_order: option_order None None
  | Some_None_order: forall a, option_order (Some a) None
  | Some_Some_order: forall a b, Korder a b -> option_order (Some a) (Some b).

Program Definition option_kiM (worlds: Type) {kiM: KripkeIntuitionisticModel worlds}: KripkeIntuitionisticModel (option worlds) :=
  Build_KripkeIntuitionisticModel (option worlds) (@option_order worlds _) _.
Next Obligation.
  pose proof Korder_PreOrder as H_PreOrder.
  constructor; hnf; intros.
  + destruct x.
    - constructor; reflexivity.
    - constructor.
  + inversion H; inversion H0; subst; try first [congruence | constructor].
    inversion H5; subst.
    etransitivity; eauto.
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

(***********************************)
(* dSA uSA examples                *)
(***********************************)

Definition ikiM_dSA {worlds: Type} {kiM: KripkeIntuitionisticModel worlds} {ikiM: IdentityKripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds}: DownwardsClosedSeparationAlgebra worlds.
Proof.
  constructor.
  pose proof Korder_PreOrder as H_PreOrder.
  simpl; intros.
  apply Korder_identity in H0.
  subst n.
  exists m1, m2.
  split; [| split]; auto; reflexivity.
Qed.

Definition ikiM_uSA {worlds: Type} {kiM: KripkeIntuitionisticModel worlds} {ikiM: IdentityKripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds}: UpwardsClosedSeparationAlgebra worlds.
Proof.
  constructor.
  pose proof Korder_PreOrder as H_PreOrder.
  simpl; intros.
  apply Korder_identity in H0.
  apply Korder_identity in H1.
  subst n1 n2.
  exists m.
  split; auto; reflexivity.
Qed.

Definition identity_dSA {worlds: Type} {kiM: KripkeIntuitionisticModel worlds}: @DownwardsClosedSeparationAlgebra worlds kiM (identity_SA _).
Proof.
  constructor.
  simpl; intros.
  destruct H; subst m1 m2.
  exists n, n; auto.
Qed.

Definition prod_dSA {A B: Type} {kiM_A: KripkeIntuitionisticModel A} {kiM_B: KripkeIntuitionisticModel B} {SA_A: SeparationAlgebra A} {SA_B: SeparationAlgebra B} {dSA_A: DownwardsClosedSeparationAlgebra A} {dSA_B: DownwardsClosedSeparationAlgebra B}: @DownwardsClosedSeparationAlgebra (A * B) (@prod_kiM _ _ kiM_A kiM_B) (@prod_SA _ _ SA_A SA_B).
Proof.
  constructor.
  simpl; intros.
  destruct H, H0.
  destruct (join_Korder_down _ _ _ _ H H0) as [fst_n1 [fst_n2 [? [? ?]]]].
  destruct (join_Korder_down _ _ _ _ H1 H2) as [snd_n1 [snd_n2 [? [? ?]]]].
  exists (fst_n1, snd_n1), (fst_n2, snd_n2).
  auto.
Qed.

Definition prod_uSA {A B: Type} {kiM_A: KripkeIntuitionisticModel A} {kiM_B: KripkeIntuitionisticModel B} {SA_A: SeparationAlgebra A} {SA_B: SeparationAlgebra B} {uSA_A: UpwardsClosedSeparationAlgebra A} {uSA_B: UpwardsClosedSeparationAlgebra B}: @UpwardsClosedSeparationAlgebra (A * B) (@prod_kiM _ _ kiM_A kiM_B) (@prod_SA _ _ SA_A SA_B).
Proof.
  constructor.
  simpl; intros.
  destruct H, H0, H1.
  destruct (join_Korder_up _ _ _ _ _ H H0 H1) as [fst_n [? ?]].
  destruct (join_Korder_up _ _ _ _ _ H2 H3 H4) as [snd_n [? ?]].
  exists (fst_n, snd_n).
  auto.
Qed.

(***********************************)
(* More examples                   *)
(***********************************)

Program Definition nat_le_kiM: KripkeIntuitionisticModel nat := 
  Build_KripkeIntuitionisticModel nat (fun a b => a <= b) _.
Next Obligation.
  constructor; hnf; intros.
  + apply le_n.
  + eapply NPeano.Nat.le_trans; eauto.
Qed.

(* TODO: Probably don't need this one. *)
Program Definition SAu_kiM (worlds: Type) {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds} {SAu: SeparationAlgebra_unit worlds} : KripkeIntuitionisticModel worlds :=
  Build_KripkeIntuitionisticModel worlds (fun a b => exists b', join b b' a) _.
Next Obligation.
  constructor; hnf; intros.
  + exists unit; apply unit_join.
  + destruct H as [? ?], H0 as [? ?].
    destruct (join_assoc _ _ _ _ _ H0 H) as [? [? ?]].
    exists x2; auto.
Qed.

Definition Heap (addr val: Type): Type := addr -> option val.

Instance Heap_SA (addr val: Type): SeparationAlgebra (Heap addr val) :=
  @fun_SA _ _ (@option_SA _ (identity_SA _)).

Instance Heap_nSA (addr val: Type): NormalSeparationAlgebra (Heap addr val) :=
  @fun_nSA _ _ _ (@option_nSA _ _ (identity_nSA _)).

Instance mfHeap_kiM (addr val: Type): KripkeIntuitionisticModel (Heap addr val) :=
  identity_kiM _.

Instance gcHeap_kiM (addr val: Type): KripkeIntuitionisticModel (Heap addr val) :=
  @fun_kiM _ _ (@option_kiM _ (identity_kiM _)).

Definition Stack (LV val: Type): Type := LV -> val.

Definition StepIndex_kiM (worlds: Type) {kiM: KripkeIntuitionisticModel worlds}: KripkeIntuitionisticModel (nat * worlds) := @prod_kiM _ _ nat_le_kiM kiM.

Definition StepIndex_SA (worlds: Type) {SA: SeparationAlgebra worlds}: SeparationAlgebra (nat * worlds) := @prod_SA _ _ (identity_SA _) SA.

Definition StepIndex_nSA (worlds: Type) {SA: SeparationAlgebra worlds} {nSA: NormalSeparationAlgebra worlds}: @NormalSeparationAlgebra (nat * worlds) (StepIndex_SA worlds) := @prod_nSA _ _ _ _ (identity_nSA _) nSA.

Definition StepIndex_dSA (worlds: Type) {kiM: KripkeIntuitionisticModel worlds} {SA: SeparationAlgebra worlds} {dSA: DownwardsClosedSeparationAlgebra worlds}: @DownwardsClosedSeparationAlgebra (nat * worlds) (StepIndex_kiM worlds) (StepIndex_SA worlds) := @prod_dSA _ _ _ _ _ _ (@identity_dSA _ nat_le_kiM) dSA.

