Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.

Lemma fin_subset_match {A B: Type} {P: A -> B -> Prop}: forall (X: Ensemble A) (Y: Ensemble B),
  (forall x, X x -> exists y, P x y /\ Y y) ->
  forall xs, Forall (fun x => X x) xs -> exists ys, Forall2 P xs ys /\ Forall (fun y => Y y) ys.
Proof.
  intros.
  induction xs as [| x0 xs].
  + exists nil; split; constructor.
  + inversion H0; subst.
    specialize (IHxs H4).
    destruct IHxs as [ys [? ?]].
    specialize (H x0 H3).
    destruct H as [y0 [? ?]].
    exists (y0 :: ys).
    split; constructor; auto.
Qed.

Lemma Forall2_lr_rev {A B: Type} {P: A -> B -> Prop}: forall xs ys,
  Forall2 (fun y x => P x y) ys xs ->
  Forall2 P xs ys.
Proof.
  intros.
  induction H; auto.
Qed.

(* This one copy from RamifyCoq *)
Lemma Forall_app_iff: forall {A : Type} (P : A -> Prop) (l1 l2 : list A), Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
Proof.
  intros; induction l1; intros.
  + simpl.
    assert (Forall P nil) by constructor; tauto.
  + simpl; split; intros.
    - inversion H; subst; split; try tauto.
      constructor; auto; tauto.
    - destruct H.
      inversion H; subst.
      constructor; auto; tauto.
Qed.

Inductive remove_rel {A: Type}: A -> list A -> list A -> Prop :=
| remove_rel_nil: forall a, remove_rel a nil nil
| remove_rel_cons_eq: forall a xs ys, remove_rel a xs ys -> remove_rel a (a :: xs) ys
| remove_rel_cons_neq: forall a b xs ys, a <> b -> remove_rel a xs ys -> remove_rel a (b :: xs) (b :: ys).

Lemma remove_rel_In: forall (A : Type) (l1 l2 : list A) (x : A), remove_rel x l1 l2 -> ~ In x l2.
Proof.
  intros.
  induction H.
  + intros [].
  + auto.
  + intros [|]; auto.
Qed.

Lemma remove_rel_exist: forall (A : Type) (l1 : list A) (x : A) (DEC: forall y, x = y \/ x <> y), exists l2, remove_rel x l1 l2.
Proof.
  intros.
  induction l1.
  + exists nil.
    apply remove_rel_nil.
  + destruct IHl1 as [l2 ?].
    destruct (DEC a).
    - exists l2; subst.
      apply remove_rel_cons_eq; auto.
    - exists (a :: l2); subst.
      apply remove_rel_cons_neq; auto.
Qed.
