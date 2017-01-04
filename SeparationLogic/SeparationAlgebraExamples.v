Require Import Coq.Logic.ChoiceFacts.
Require Import Coq.Logic.ClassicalChoice.
Require Import Logic.PropositionalLogic.KripkeSemantics.
Require Import Logic.SeparationLogic.SeparationAlgebra.
Require Import Logic.SeparationLogic.SeparationAlgebraGenerators.

(***********************************)
(* SA examples                     *)
(***********************************)

Section heaps.

Definition Heap (addr val: Type): Type := addr -> option val.

Instance Heap_Join (addr val: Type): Join (Heap addr val) :=
  @fun_Join _ _ (@option_Join _ (equiv_Join)).

Instance Heap_SA (addr val: Type): SeparationAlgebra (Heap addr val) :=
  @fun_SA _ _ _ (@option_SA _ _ (equiv_SA)).

(* Discrete heap *)
Instance discHeap_kiM (addr val: Type): KripkeIntuitionisticModel (Heap addr val) :=
  identity_kiM.

Program Instance discHeap_ikiM (addr val: Type): IdentityKripkeIntuitionisticModel (Heap addr val).

Instance discHeap_dSA (addr val: Type):
  @DownwardsClosedSeparationAlgebra (Heap addr val) (Heap_Join addr val) (discHeap_kiM  addr val).
Proof.
  eapply ikiM_dSA.
Qed.  

Instance discHeap_uSA (addr val: Type):
  @UpwardsClosedSeparationAlgebra (Heap addr val) (Heap_Join addr val) (discHeap_kiM  addr val).
Proof.
  eapply ikiM_uSA.
Qed.

(* Monotonic heap*)
Instance monHeap_kiM (addr val: Type): KripkeIntuitionisticModel (Heap addr val) :=
  @fun_kiM _ _ (@option_kiM _ (identity_kiM)).

Instance identity_ikiM (A: Type): @IdentityKripkeIntuitionisticModel _ (@identity_kiM A).
Proof.
  constructor; intros; auto.
Qed.
    
Instance monHeap_dSA (addr val: Type):
  @DownwardsClosedSeparationAlgebra (Heap addr val) (Heap_Join addr val) (monHeap_kiM  addr val).
Proof.
  eapply fun_dSA.
  eapply option_dSA.
  eapply ikiM_dSA.
Qed.  

Definition monHeap_uSA (addr val: Type):
  @UpwardsClosedSeparationAlgebra (Heap addr val) (Heap_Join addr val) (monHeap_kiM  addr val).
Proof.
  eapply fun_uSA.
  eapply option_uSA.
  - eapply ikiM_uSA.
  - apply equiv_SA.
  - admit.
Admitted.
  
  
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