Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Class PreKripkeSemantics (L: Language) (SM: Semantics L): Type := {
  Kmodel: Type;
  Kworlds: Kmodel -> Type;
  build_model: forall M: Kmodel, Kworlds M -> model
}.

Notation "'KRIPKE:'  M , m" := (build_model M m) (at level 59, no associativity) : logic_base.

Class KripkeIntuitionisticModel (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (SM: Semantics L) {pkSM: PreKripkeSemantics L SM}: Type := {
  Korder: forall {M: Kmodel}, Kworlds M -> Kworlds M -> Prop; (* <= *)
  Korder_PreOrder: forall M, PreOrder (@Korder M)
}.

Class IdenticalKripkeIntuitionisticModel (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (SM: Semantics L) {pkSM: PreKripkeSemantics L SM} {kiM: KripkeIntuitionisticModel L SM}: Type := {
  Korder_identical: forall M (m n: Kworlds M), Korder m n -> m = n
}.

Class NoBranchKripkeIntuitionisticModel (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (SM: Semantics L) {pkSM: PreKripkeSemantics L SM} {kiM: KripkeIntuitionisticModel L SM}: Type := {
  Korder_no_branch: forall M (m1 m2 n: Kworlds M), Korder m1 n -> Korder m2 n -> Korder m1 m2 \/ Korder m2 m1
}.

Class KripkeIntuitionisticSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (SM: Semantics L) {pkSM: PreKripkeSemantics L SM} {kiM: KripkeIntuitionisticModel L SM} : Type := {
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
  | falsep => sem_false
  | varp p => eval p
  end.

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

Instance pkSM (Var: Type): PreKripkeSemantics (PropositionalLanguage.L Var) (SM Var) :=
  Build_PreKripkeSemantics _ (SM Var)
   Kmodel
   (fun M => M)
   (fun M m => Build_model _ M m).

Instance kiM (Var: Type): KripkeIntuitionisticModel (PropositionalLanguage.L Var) (SM Var).
Proof.
  apply (Build_KripkeIntuitionisticModel _ _ _ _ (pkSM Var) (fun M => Korder M)).
  intros.
  apply Korder_preorder.
Defined.

Instance kiSM (Var: Type): KripkeIntuitionisticSemantics (PropositionalLanguage.L Var) (SM Var).
Proof.
  apply (Build_KripkeIntuitionisticSemantics _ _ _ _ (pkSM Var) _).
  + hnf; simpl; intros.
    eapply (proj2_sig (denotation M (Kvar M) x)); eauto.
  + split; auto.
  + split; auto.
  + split; auto.
  + intros; simpl. auto.
Defined.

End KripkeSemantics_All.

Module KripkeSemantics_Identical.

Import KripkeSemantics.

Import KripkeSemantics.

Record Kmodel {Var: Type} : Type := {
  underlying_frame :> frame;
  Kvar: Var -> sem underlying_frame;
  frame_ident: forall m n, Korder underlying_frame m n -> m = n
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

Instance pkSM (Var: Type): PreKripkeSemantics (PropositionalLanguage.L Var) (SM Var) :=
  Build_PreKripkeSemantics _ (SM Var)
   Kmodel
   (fun M => M)
   (fun M m => Build_model _ M m).

Instance kiM (Var: Type): KripkeIntuitionisticModel (PropositionalLanguage.L Var) (SM Var).
Proof.
  apply (Build_KripkeIntuitionisticModel _ _ _ _ (pkSM Var) (fun M => Korder M)).
  intros.
  apply Korder_preorder.
Defined.

Instance ikiM (Var: Type): IdenticalKripkeIntuitionisticModel (PropositionalLanguage.L Var) (SM Var).
Proof.
  apply (Build_IdenticalKripkeIntuitionisticModel _ _ _ _ (pkSM Var) _).
  intros.
  apply frame_ident; auto.
Defined.

Instance kiSM (Var: Type): KripkeIntuitionisticSemantics (PropositionalLanguage.L Var) (SM Var).
Proof.
  apply (Build_KripkeIntuitionisticSemantics _ _ _ _ (pkSM Var) _).
  + hnf; simpl; intros.
    eapply (proj2_sig (denotation M (Kvar M) x)); eauto.
  + split; auto.
  + split; auto.
  + split; auto.
  + intros; simpl. auto.
Defined.

End KripkeSemantics_Identical.

Module KripkeSemantics_NoBranch.

Import KripkeSemantics.

Import KripkeSemantics.

Record Kmodel {Var: Type} : Type := {
  underlying_frame :> frame;
  Kvar: Var -> sem underlying_frame;
  frame_no_branch: forall m1 m2 n, Korder underlying_frame m1 n -> Korder underlying_frame m2 n -> Korder underlying_frame m1 m2 \/ Korder underlying_frame m2 m1
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

Instance pkSM (Var: Type): PreKripkeSemantics (PropositionalLanguage.L Var) (SM Var) :=
  Build_PreKripkeSemantics _ (SM Var)
   Kmodel
   (fun M => M)
   (fun M m => Build_model _ M m).

Instance kiM (Var: Type): KripkeIntuitionisticModel (PropositionalLanguage.L Var) (SM Var).
Proof.
  apply (Build_KripkeIntuitionisticModel _ _ _ _ (pkSM Var) (fun M => Korder M)).
  intros.
  apply Korder_preorder.
Defined.

Instance nkiM (Var: Type): NoBranchKripkeIntuitionisticModel (PropositionalLanguage.L Var) (SM Var).
Proof.
  apply (Build_NoBranchKripkeIntuitionisticModel _ _ _ _ (pkSM Var) _).
  apply frame_no_branch; auto.
Defined.

Instance kiSM (Var: Type): KripkeIntuitionisticSemantics (PropositionalLanguage.L Var) (SM Var).
Proof.
  apply (Build_KripkeIntuitionisticSemantics _ _ _ _ (pkSM Var) _).
  + hnf; simpl; intros.
    eapply (proj2_sig (denotation M (Kvar M) x)); eauto.
  + split; auto.
  + split; auto.
  + split; auto.
  + intros; simpl. auto.
Defined.

End KripkeSemantics_NoBranch.

