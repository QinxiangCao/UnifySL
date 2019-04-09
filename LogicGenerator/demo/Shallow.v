Require Import Generated.
Require Import ZArith.

Module NaiveLang.
  Definition expr := (nat -> Z) -> Prop.

  Definition impp (e1 e2 : expr) : expr := fun st => e1 st -> e2 st.
  Definition andp (e1 e2 : expr) : expr := fun st => e1 st /\ e2 st.
  Definition orp  (e1 e2 : expr) : expr := fun st => e1 st \/ e2 st.
  Definition falsep : expr := fun st => False.

  Definition provable (e : expr) : Prop := forall st, e st.

  Lemma modus_ponens :
    forall x y : expr, provable (impp x y) -> provable x -> provable y.
  Proof. unfold provable, impp. auto. Qed.

  Lemma axiom1 : forall x y : expr, provable (impp x (impp y x)).
  Proof. unfold provable, impp. auto. Qed.

  Lemma axiom2 : forall x y z : expr,
      provable (impp (impp x (impp y z)) (impp (impp x y) (impp x z))).
  Proof. unfold provable, impp. auto. Qed.

  Lemma andp_intros :
    forall x y : expr, provable (impp x (impp y (andp x y))).
  Proof. unfold provable, impp, andp. auto. Qed.

  Lemma andp_elim1 : forall x y : expr, provable (impp (andp x y) x).
  Proof. unfold provable, impp, andp. tauto. Qed.

  Lemma andp_elim2 : forall x y : expr, provable (impp (andp x y) y).
  Proof. unfold provable, impp, andp. tauto. Qed.

  Lemma orp_intros1 : forall x y : expr, provable (impp x (orp x y)).
  Proof. unfold provable, impp, orp. auto. Qed.

  Lemma orp_intros2 : forall x y : expr, provable (impp y (orp x y)).
  Proof. unfold provable, impp, orp. auto. Qed.

  Lemma orp_elim : forall x y z : expr,
      provable (impp (impp x z) (impp (impp y z) (impp (orp x y) z))).
  Proof. unfold provable, impp, orp. tauto. Qed.

  Lemma falsep_elim : forall x : expr, provable (impp falsep x).
  Proof. unfold provable, impp, falsep. destruct 1. Qed.
End NaiveLang.

Module Language <: LanguageSig.
  Definition Var := unit.
  Definition expr := NaiveLang.expr.
  Definition impp := NaiveLang.impp.
  Definition andp := NaiveLang.andp.
  Definition orp := NaiveLang.orp.
  Definition falsep := NaiveLang.falsep.
End Language.

Module Logic <: LogicSig Language.
  Definition provable := NaiveLang.provable.
  Definition modus_ponens := NaiveLang.modus_ponens.
  Definition axiom1 := NaiveLang.axiom1.
  Definition axiom2 := NaiveLang.axiom2.
  Definition andp_intros := NaiveLang.andp_intros.
  Definition andp_elim1 := NaiveLang.andp_elim1.
  Definition andp_elim2 := NaiveLang.andp_elim2.
  Definition orp_intros1 := NaiveLang.orp_intros1.
  Definition orp_intros2 := NaiveLang.orp_intros2.
  Definition orp_elim := NaiveLang.orp_elim.
  Definition falsep_elim := NaiveLang.falsep_elim.
End Logic.

Module Test.
  Module DerivedTheorems := LogicTheorem Language Logic.
  Import NaiveLang.

  Theorem provable_impp_refl : forall e : expr, provable (impp e e).
  Proof. apply DerivedTheorems.provable_impp_refl. Qed.
  Print Assumptions provable_impp_refl.
End Test.