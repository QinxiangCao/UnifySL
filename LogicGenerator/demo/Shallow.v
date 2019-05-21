Require Import ZArith.

Module NaiveLang.
  Definition expr := (nat -> Z) -> Prop.

  Definition impp (e1 e2 : expr) : expr := fun st => e1 st -> e2 st.
  Definition andp (e1 e2 : expr) : expr := fun st => e1 st /\ e2 st.
  Definition orp  (e1 e2 : expr) : expr := fun st => e1 st \/ e2 st.
  Definition falsep : expr := fun st => False.
  Definition iffp (e1 e2 : expr) : expr := andp (impp e1 e2) (impp e2 e1).
  Parameter sepcon : expr -> expr -> expr.
  Parameter wand : expr -> expr -> expr.

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

  Axiom sepcon_comm_impp: forall x y, provable (impp (sepcon x y) (sepcon y x)).
  Axiom sepcon_assoc: forall x y z,
      provable (iffp (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)).
  Axiom wand_sepcon_adjoint: forall x y z,
      provable (impp (sepcon x y) z) <-> provable (impp x (wand y z)).
End NaiveLang.
