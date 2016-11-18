Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Class KripkeIntuitionisticModel (MD: Model) {kMD: KripkeModel MD}: Type := {
  Korder: forall {M: Kmodel}, Kworlds M -> Kworlds M -> Prop; (* <= *)
  Korder_PreOrder: forall M, PreOrder (@Korder M)
}.

Infix "<=" := Korder: KripkeSemantics.
Local Open Scope KripkeSemantics.

Class IdenticalKripkeIntuitionisticModel(MD: Model) {kMD: KripkeModel MD} {kiMD: KripkeIntuitionisticModel MD} (M: Kmodel): Type := {
  Korder_identical: forall (m n: Kworlds M), m <= n -> m = n
}.

Class NoBranchKripkeIntuitionisticModel (MD: Model) {kMD: KripkeModel MD} {kiMD: KripkeIntuitionisticModel MD} (M: Kmodel): Type := {
  Korder_no_branch: forall (m1 m2 n: Kworlds M), m1 <= n -> m2 <= n -> m1 <= m2 \/ m2 <= m1
}.

Class KripkeIntuitionisticSemantics (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (MD: Model) {kMD: KripkeModel MD} {kiMD: KripkeIntuitionisticModel MD} (SM: Semantics L MD) : Type := {
  sat_mono: forall M m n x, m <= n -> KRIPKE: M , n |= x -> KRIPKE: M , m |= x;
  sat_impp: forall M m x y, KRIPKE: M , m |= x --> y <-> (forall n, n <= m -> KRIPKE: M , n |= x -> KRIPKE: M , n |= y);
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

Infix "<=" := (Korder _): TheKripkeSemantics.

Local Open Scope TheKripkeSemantics.

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

Section KripkeSemantics_All.

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

Instance kiMD: KripkeIntuitionisticModel MD :=
  Build_KripkeIntuitionisticModel _ _
    (fun M => Korder M)
    (fun M => Korder_preorder _).

Instance SM: Semantics L MD :=
  Build_Semantics L MD
   (fun M x => proj1_sig (denotation M (Kvar M) x) (elm M)).

Instance kiSM: KripkeIntuitionisticSemantics L MD SM.
Proof.
  apply Build_KripkeIntuitionisticSemantics.
  + hnf; simpl; intros.
    eapply (proj2_sig (denotation M (Kvar M) x)); eauto.
  + split; auto.
  + split; auto.
  + split; auto.
  + intros; simpl. auto.
Defined.

End KripkeSemantics_All.
End KripkeSemantics_All.

Module KripkeSemantics_Identical.

Import KripkeSemantics.

Section KripkeSemantics_Identical.

Context (Var: Type).

Record Kmodel : Type := {
  underlying_frame :> frame;
  Kvar: Var -> sem underlying_frame;
  frame_ident: forall m n, Korder underlying_frame m n -> m = n
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

Instance kiMD: KripkeIntuitionisticModel MD :=
  Build_KripkeIntuitionisticModel _ _
    (fun M => Korder M)
    (fun M => Korder_preorder _).

Instance SM: Semantics L MD :=
  Build_Semantics L MD
   (fun M x => proj1_sig (denotation M (Kvar M) x) (elm M)).

Instance kiSM: KripkeIntuitionisticSemantics L MD SM.
Proof.
  apply Build_KripkeIntuitionisticSemantics.
  + hnf; simpl; intros.
    eapply (proj2_sig (denotation M (Kvar M) x)); eauto.
  + split; auto.
  + split; auto.
  + split; auto.
  + intros; simpl. auto.
Defined.

End KripkeSemantics_Identical.

End KripkeSemantics_Identical.

Module KripkeSemantics_NoBranch.

Import KripkeSemantics.

Section KripkeSemantics_NoBranch.

Context (Var: Type).

Record Kmodel  : Type := {
  underlying_frame :> frame;
  Kvar: Var -> sem underlying_frame;
  frame_no_branch: forall m1 m2 n, Korder underlying_frame m1 n -> Korder underlying_frame m2 n -> Korder underlying_frame m1 m2 \/ Korder underlying_frame m2 m1
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

Instance kiMD: KripkeIntuitionisticModel MD :=
  Build_KripkeIntuitionisticModel _ _
    (fun M => Korder M)
    (fun M => Korder_preorder _).

Instance SM: Semantics L MD :=
  Build_Semantics L MD
   (fun M x => proj1_sig (denotation M (Kvar M) x) (elm M)).

Instance kiSM: KripkeIntuitionisticSemantics L MD SM.
Proof.
  apply Build_KripkeIntuitionisticSemantics.
  + hnf; simpl; intros.
    eapply (proj2_sig (denotation M (Kvar M) x)); eauto.
  + split; auto.
  + split; auto.
  + split; auto.
  + intros; simpl. auto.
Defined.

End KripkeSemantics_NoBranch.
End KripkeSemantics_NoBranch.

