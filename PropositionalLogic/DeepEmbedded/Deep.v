Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Inductive expr : Type :=
| andp : expr -> expr -> expr
| orp : expr -> expr -> expr
| impp : expr -> expr -> expr
| falsep : expr
| varp : nat -> expr
.

Fixpoint beq e1 e2 :=
  match e1, e2 with
  | falsep , falsep => true
  | varp x, varp y => EqNat.beq_nat x y
  | andp p11 p12, andp p21 p22 => andb (beq p11 p21) (beq p12 p22)
  | orp p11 p12, orp p21 p22 => andb (beq p11 p21) (beq p12 p22)
  | impp p11 p12, impp p21 p22 => andb (beq p11 p21) (beq p12 p22)
  | _, _ => false
  end.

Theorem beq_eq : forall e1 e2, beq e1 e2 = true <-> e1 = e2.
Proof.
  split.
  - generalize dependent e2.
    induction e1; intros; destruct e2; simpl in H;
      try congruence; auto using EqNat.beq_nat_true.
    all: apply andb_prop in H; destruct H;
      rewrite (IHe1_1 _ H); rewrite (IHe1_2 _ H0); reflexivity.
  - intros. subst e2.
    induction e1; simpl; auto using andb_true_intro, EqNat.beq_nat_refl.
Qed.

Local Instance L : Language := Build_Language expr .

Local Instance minL : MinimumLanguage L := Build_MinimumLanguage L impp.

Local Instance pL : PropositionalLanguage L :=
  Build_PropositionalLanguage L andp orp falsep.

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
.

Local Instance GP: Provable L := Build_Provable _ provable.

Local Instance minAX: MinimumAxiomatization L GP.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

Local Instance ipG: IntuitionisticPropositionalLogic L GP.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
  + apply falsep_elim.
Qed.
