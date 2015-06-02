(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * This module proves the validity of
    - well-founded recursion (also known as course of values)
    - well-founded induction
    from a well-founded ordering on a given set *)

Set Implicit Arguments.

Require Import Notations.
Require Import Logic.
Require Import Datatypes.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

(** Well-founded induction principle on [Prop] *)

Section Well_founded.

 Variable A : Type.
 Variable R : A -> A -> Prop.

 (** The accessibility predicate is defined to be non-informative *)
 (** (Acc_rect is automatically defined because Acc is a singleton type) *)

 Inductive Acc (x: A) : Prop :=
     Acc_intro : (forall y:A, R y x -> Acc y) -> Acc x.

 Lemma Acc_inv : forall x:A, Acc x -> forall y:A, R y x -> Acc y.
  destruct 1; trivial.
 Defined.

 Global Implicit Arguments Acc_inv [x y] [x].

 (** A relation is well-founded if every element is accessible *)

 Definition well_founded := forall a:A, Acc a.

 (** Well-founded induction on [Set] and [Prop] *)

 Hypothesis Rwf : well_founded.

 Theorem well_founded_induction_type :
  forall P:A -> Type,
    (forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.
 Proof.
  intros; apply Acc_rect; auto.
 Defined.

 Theorem well_founded_induction :
  forall P:A -> Set,
    (forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.
 Proof.
  exact (fun P:A -> Set => well_founded_induction_type P).
 Defined.

 Theorem well_founded_ind :
  forall P:A -> Prop,
    (forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.
 Proof.
  exact (fun P:A -> Prop => well_founded_induction_type P).
 Defined.

(** Well-founded fixpoints *)

 Section FixPoint.

  Variable P : A -> Type.
  Variable F : forall x:A, (forall y:A, R y x -> P y) -> P x.

  Fixpoint Fix_F (x:A) (a:Acc x) : P x :=
    F (fun (y:A) (h:R y x) => Fix_F (Acc_inv a h)).

  Scheme Acc_inv_dep := Induction for Acc Sort Prop.

  Lemma Fix_F_eq :
   forall (x:A) (r:Acc x),
     F (fun (y:A) (p:R y x) => Fix_F (x:=y) (Acc_inv r p)) = Fix_F (x:=x) r.
  Proof.
    intros.
    destruct r.
    simpl.
    auto.
  Qed.

  Definition Fix (x:A) := Fix_F (Rwf x).

  (** Proof that [well_founded_induction] satisfies the fixpoint equation.
      It requires an extra property of the functional *)

  Variable EQ : forall a, P a -> P a -> Prop.
  Variable Equiv: forall a: A, Equivalence (@EQ a).

  Hypothesis
    F_ext :
      forall (x:A) (f g:forall y:A, R y x -> P y),
        (forall (y:A) (p:R y x), EQ (f y p) (g y p)) -> EQ (F f) (F g).

  Lemma Fix_F_inv : forall (x:A) (r s:Acc x), EQ (Fix_F r) (Fix_F s).
  Proof.
   intro x; induction (Rwf x); intros.
   rewrite <- (Fix_F_eq r); rewrite <- (Fix_F_eq s); intros.
   apply F_ext; auto.
  Qed.

  Lemma Fix_eq : forall x:A, EQ (Fix x) (F (fun (y:A) (p:R y x) => Fix y)).
  Proof.
   intro x; unfold Fix.
   rewrite <- Fix_F_eq.
   apply F_ext; intros.
   apply Fix_F_inv.
  Qed.

 End FixPoint.

End Well_founded.
