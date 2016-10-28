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