Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.

Definition remove1 {A: Type} (test: A -> bool): list A -> option (list A) :=
  fix remove1 xs :=
    match xs with
    | nil => None
    | x :: xs0 => if test x then Some xs0 else
       match remove1 xs0 with
       | Some xs0' => Some (x :: xs0')
       | None => None
       end
    end.

Lemma remove1_sound {A: Type}: forall (test: A -> bool) (l l': list A),
  remove1 test l = Some l' ->
  exists a, test a = true /\ Permutation (a :: l') l.
Proof.
  intros.
  revert l' H; induction l; intros.
  + inversion H.
  + simpl in H.
    destruct (test a) eqn:?H.
    - exists a; inversion H; subst.
      split; auto.
    - destruct (remove1 test l) eqn:?H; inversion H.
      subst.
      clear H H0.
      specialize (IHl _ eq_refl).
      destruct IHl as [a0 [? ?]]; exists a0.
      split; auto.
      transitivity (a :: a0 :: l0).
      * constructor.
      * constructor; auto.
Qed.

Definition remove1s {A: Type} (eqb: A -> A -> bool) (orig: list A): list A -> option (list A) :=
  fold_right
    (fun a Orig =>
       match Orig with
       | Some orig => remove1 (eqb a) orig
       | None => None
       end) (Some orig).

Lemma remove1s_sound {A: Type}: forall (eqb: A -> A -> bool) (l l' l'': list A),
  (forall x y, eqb x y = true <-> x = y) ->
  remove1s eqb l l' = Some l'' ->
  Permutation (l' ++ l'') l.
Proof.
  intros.
  revert l l'' H0; induction l'; intros.
  + simpl in H0.
    inversion H0; auto.
  + simpl in H0.
    destruct (remove1s eqb l l') eqn:?H; inversion H0; clear H0.
    apply IHl' in H1.
    apply remove1_sound in H3.
    destruct H3 as [a' [? ?]].
    apply H in H0; subst a'.
    rewrite <- H1.
    rewrite <- H2.
    change (l' ++ a :: l'') with (l' ++ (a :: nil) ++ l'').
    rewrite app_assoc.
    apply Permutation_app_tail.
    apply Permutation_cons_append.
Qed.

