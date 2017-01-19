Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.

Class KripkeIntuitionisticModel (worlds: Type): Type := {
  Korder: worlds -> worlds -> Prop; (* <= *)
  Korder_PreOrder:> PreOrder Korder
}.

Module KripkeModelNotation_Intuitionistic.

Infix "<=" := Korder: kripke_model.

End KripkeModelNotation_Intuitionistic.

Import KripkeModelNotation_Intuitionistic.

Class IdentityKripkeIntuitionisticModel (worlds: Type) {kiW: KripkeIntuitionisticModel worlds} : Prop := {
  Korder_identity: forall m n: worlds, m <= n -> m = n
}.

Class NoBranchKripkeIntuitionisticModel (worlds: Type) {kiW: KripkeIntuitionisticModel worlds} : Prop := {
  Korder_no_branch: forall m1 m2 n: worlds, n <= m1 -> n <= m2 -> m1 <= m2 \/ m2 <= m1
}.

Class BranchJoinKripkeIntuitionisticModel (worlds: Type) {kiW: KripkeIntuitionisticModel worlds} : Prop := {
  Korder_branch_join: forall m1 m2 n: worlds, n <= m1 -> n <= m2 -> exists m, m1 <= m /\ m2 <= m
}.

Definition Korder_stable {worlds: Type} {kiW: KripkeIntuitionisticModel worlds} (P: worlds -> Prop): Prop :=
  forall w1 w2, w1 <= w2 -> (P w1 <-> P w2).

Class KripkeIntuitionisticSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {kiW: KripkeIntuitionisticModel (Kworlds M)} (SM: Semantics L MD) : Type := {
  sat_mono: forall m n x, m <= n -> KRIPKE: M , m |= x -> KRIPKE: M , n |= x;
  sat_impp: forall m x y, KRIPKE: M , m |= x --> y <-> (forall n, m <= n -> KRIPKE: M , n |= x -> KRIPKE: M , n |= y);
  sat_andp: forall m x y, KRIPKE: M , m |= x && y <-> (KRIPKE: M , m |= x /\ KRIPKE: M , m |= y);
  sat_orp: forall m x y, KRIPKE: M , m |= x || y <-> (KRIPKE: M , m |= x \/ KRIPKE: M , m |= y);
  sat_falsep: forall m, ~ KRIPKE: M , m |= FF
}.

Module KripkeSemantics.

Import PropositionalLanguage.

Record frame: Type := {
  underlying_set:> Type;
  Korder: relation underlying_set; (* <= *)
  Korder_preorder: PreOrder Korder
}.

Infix "<=" := (Korder _): TheKripkeSemantics.

Local Open Scope TheKripkeSemantics.

Definition sem (f: frame) := sig (fun s: Ensemble f => forall x y, x <= y -> s x -> s y).

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
    forall y: F, x <= y -> X y -> Y y.
Next Obligation.
  revert H2; apply H0.
  pose proof @PreOrder_Transitive _ _ (Korder_preorder F).
  transitivity y; auto.
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

Section KripkeSemantics.
Context (Var: Type).

Record Kmodel : Type := {
  underlying_frame :> frame;
  Kvar: Var -> sem underlying_frame
}.

Record model: Type := {
  underlying_model :> Kmodel;
  elm: underlying_model
}.

Instance L: Language := PropositionalLanguage.L Var.
Instance MD: Model := Build_Model model.

Instance kMD: KripkeModel MD :=
  Build_KripkeModel _
    Kmodel
    (fun M => M)
    (fun M m => Build_model M m).

Instance kiM (M: Kmodel): KripkeIntuitionisticModel (Kworlds M) :=
  Build_KripkeIntuitionisticModel (Kworlds M) (Korder M) (Korder_preorder _).

Instance SM: Semantics L MD :=
  Build_Semantics L MD
   (fun M x => proj1_sig (denotation M (Kvar M) x) (elm M)).

Instance kiSM (M: Kmodel): KripkeIntuitionisticSemantics L MD M SM.
Proof.
  apply Build_KripkeIntuitionisticSemantics.
  + hnf; simpl; intros.
    eapply (proj2_sig (denotation M (Kvar M) x)); eauto.
  + split; auto.
  + split; auto.
  + split; auto.
  + intros; simpl. auto.
Defined.

Definition Kmodel_Identity: Kmodel -> Prop := fun M =>
  IdentityKripkeIntuitionisticModel (Kworlds M).

Definition Kmodel_NoBranch: Kmodel -> Prop := fun M =>
  NoBranchKripkeIntuitionisticModel (Kworlds M).

Definition Kmodel_BranchJoin: Kmodel -> Prop := fun M =>
  BranchJoinKripkeIntuitionisticModel (Kworlds M).

End KripkeSemantics.
End KripkeSemantics.
