(* Copied from RamifyCoq project *)

Require Import Coq.Classes.Morphisms.
Require Export Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Relation_ext.
Require Import Logic.lib.Equivalence_ext.
Require Export Coq.Lists.List.

Local Open Scope equiv_scope.

Section ListFun2.

Context {A B: Type}.
Context {RA: relation A}.
Context {RB: relation B}.
Context {EqRA: Equivalence RA}.
Context {EqRB: Equivalence RB}.

Instance proper_fold_left: forall (f: A -> B -> A) {Proper_f: Proper (equiv ==> equiv ==> equiv) f}, Proper (Forall2 equiv ==> equiv ==> equiv) (fold_left f).
Proof.
  intros.
  hnf; intros.
  induction H; hnf; intros; simpl.
  + auto.
  + apply IHForall2.
    apply Proper_f; auto.
Qed.

Lemma monoid_fold_left_tail: forall {f: A -> B -> A} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (e: A) a l,
  fold_left f (l ++ a :: nil) e === f (fold_left f l e) a.
Proof.
  intros.
  simpl.
  pose proof (proper_fold_left f).
  revert e; induction l; intros; simpl.
  + reflexivity.
  + apply IHl.
Qed.

End ListFun2.

Section ListFun1.

Context {A: Type}.
Context {RA: relation A}.
Context {EqRA: Equivalence RA}.

Lemma monoid_fold_left_head: forall {f} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (e: A) a l,
  (forall x, f e x === x) ->
  (forall x, f x e === x) ->
  (forall x y z, f (f x y) z === f x (f y z)) ->
  fold_left f (a :: l) e === f a (fold_left f l e).
Proof.
  intros.
  simpl.
  pose proof (proper_fold_left f).
  rewrite H.
  revert a; induction l; intros; simpl.
  + symmetry; auto.
  + rewrite (IHl (f a0 a)), H, (IHl a).
    rewrite H1.
    reflexivity.
Qed.

Lemma monoid_fold_symm: forall {f} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (e: A) l,
  (forall x, f e x === x) ->
  (forall x, f x e === x) ->
  (forall x y z, f (f x y) z === f x (f y z)) ->
  fold_left f l e === fold_right f e l.
Proof.
  intros.
  pose proof (proper_fold_left f).
  destruct l.
  + simpl.
    reflexivity.
  + simpl.
    rewrite H.
    revert a; induction l; intros; simpl.
    - symmetry; auto.
    - rewrite <- H1.
      apply IHl.
Qed.

Lemma monoid_fold_left_app: forall {f} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (e: A) l l',
  (forall x, f e x === x) ->
  (forall x, f x e === x) ->
  (forall x y z, f (f x y) z === f x (f y z)) ->
  fold_left f (l ++ l') e === f (fold_left f l e) (fold_left f l' e).
Proof.
  intros.
  rewrite fold_left_app.
  generalize (fold_left f l e) as a; clear l; intros.
  pose proof @monoid_fold_left_head f _ e a l'.
  simpl in H2.
  pose proof (proper_fold_left f).
  rewrite H in H2.
  auto.
Qed.
  
End ListFun1.

(* Above is copied from RamifyCoq project *)

Definition not_nil {A: Type} (l: list A): Prop := l <> nil.

Lemma not_nil_app_l {A: Type}: forall (l l': list A), not_nil l -> not_nil (l ++ l').
Proof.
  intros.
  hnf in *.
  destruct l;intros; simpl in *; congruence.
Qed.

Definition partial_monoid_fold {A: Type} (default: A) (f: A -> A -> A) (l: list A): A :=
  match l with
  | nil => default
  | a :: l0 => fold_left f l0 a
  end.

Section ListFun1'.

Context {A: Type}.
Context {RA: relation A}.
Context {EqRA: Equivalence RA}.

Lemma partial_monoid_fold_app: forall {f} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (default: A) l l',
  (forall x y z, f (f x y) z === f x (f y z)) ->
  not_nil l ->
  not_nil l' ->
  partial_monoid_fold default f (l ++ l') === f (partial_monoid_fold default f l) (partial_monoid_fold default f l').
Proof.
  intros.
  destruct l as [| a l], l' as [| a' l']; hnf in H0, H1; try congruence; clear H0 H1.
  revert a; induction l; intros.
  + simpl.
    revert a'; induction l'; intros.
    - simpl.
      reflexivity.
    - specialize (IHl' (f a' a0)).
      simpl in *.
      rewrite <- IHl'; clear IHl'.
      specialize (H a a' a0).
      set (b := f (f a a') a0) in H |- *.
      set (c := f a (f a' a0)) in H |- *.
      clearbody b c; clear a a' a0.
      revert b c H; induction l'; intros.
      * auto.
      * simpl.
        apply IHl'.
        rewrite H; reflexivity.
  + exact (IHl (f a0 a)).
Qed.

Lemma partial_monoid_fold_concat: forall {f} {Proper_f: Proper (equiv ==> equiv ==> equiv) f} (default: A) ls,
  (forall x y z, f (f x y) z === f x (f y z)) ->
  Forall not_nil ls ->
  partial_monoid_fold default f (concat ls) === partial_monoid_fold default f (map (partial_monoid_fold default f) ls).
Proof.
  intros.
  destruct H0; [reflexivity |].
  revert x H0; induction H1; intros.
  + simpl.
    rewrite app_nil_r.
    reflexivity.
  + Opaque partial_monoid_fold.
    simpl.
    rewrite partial_monoid_fold_app; auto.
      2: apply not_nil_app_l; auto.
    specialize (IHForall x H0).
    simpl in IHForall.
    rewrite IHForall.
    change (partial_monoid_fold default f x0 :: partial_monoid_fold default f x :: map (partial_monoid_fold default f) l)
      with ((partial_monoid_fold default f x0 :: nil) ++ partial_monoid_fold default f x :: map (partial_monoid_fold default f) l).
    rewrite partial_monoid_fold_app by (auto; intro; congruence).
    reflexivity.
    Transparent partial_monoid_fold.
Qed.

End ListFun1'.