Require Import Coq.Logic.FunctionalExtensionality.

Class Var_env : Type := {
  Var : Type;
  var_eq: forall v1 v2: Var, {v1 = v2} + {v1 <> v2}
}.

Section IPC.

Context {venv: Var_env}.

Inductive Term: Type :=
  | andp : Term -> Term -> Term
  | orp : Term -> Term -> Term
  | impp : Term -> Term -> Term
  | falsep : Term
  | varp : Var -> Term.

Notation "x && y" := (andp x y) (at level 40, left associativity) : IPC_scope.
Notation "x || y" := (orp x y) (at level 50, left associativity) : IPC_scope.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : IPC_scope.
Notation "'FF'" := falsep : IPC_scope.

Local Open Scope IPC_scope.

Definition term_eq: forall t1 t2: Term, {t1 = t2} + {t1 <> t2}.
Proof.
  induction t1; intros.
  + destruct t2; try solve [right; congruence].
    destruct (IHt1_1 t2_1), (IHt1_2 t2_2); [left | right | right | right]; congruence.
  + destruct t2; try solve [right; congruence].
    destruct (IHt1_1 t2_1), (IHt1_2 t2_2); [left | right | right | right]; congruence.
  + destruct t2; try solve [right; congruence].
    destruct (IHt1_1 t2_1), (IHt1_2 t2_2); [left | right | right | right]; congruence.
  + destruct t2; try solve [right; congruence].
    left; auto.
  + destruct t2; try solve [right; congruence].
    destruct (var_eq v v0); [left | right]; congruence.
Defined.

Definition Context := Term -> bool.

Definition EmptyContext : Context := fun _ => false.

Definition ExtendContext (ctx: Context) (t: Term) : Context :=
  fun t0 => if term_eq t0 t then true else ctx t0.

Notation "ctx ;; t" := (ExtendContext ctx t) (at level 65, left associativity) : IPC_scope.

Class Semantic : Type := mk_sem {
  ModelType : Type;
  satisfy : ModelType -> Term -> Prop
}.

Definition valid {sem: Semantic} (t: Term) : Prop :=
  forall M, @satisfy sem M t.

Definition sem_conseq {sem: Semantic} (ctx : Context) (t: Term) : Prop :=
  forall M, (forall t0, ctx t0 = true -> @satisfy sem M t0) -> @satisfy sem M t.

Notation "M  |=  t" := (satisfy M t) (at level 60, no associativity) : IPC_scope.

Notation "|==  t" := (valid t) (at level 61, no associativity) : IPC_scope.

Notation "ctx  |==  t" := (sem_conseq ctx t) (at level 60, no associativity) : IPC_scope.

Class ProofTheory : Type := mk_pt {
  derivable : Context -> Term -> Prop
}.

Notation "ctx  |--  t" := (derivable ctx t) (at level 60, no associativity) : IPC_scope.

Definition provable {pt: ProofTheory} t := EmptyContext |-- t.

Notation "|--  t" := (provable t) (at level 61, no associativity) : IPC_scope.

Definition sound (sem: Semantic) (pt: ProofTheory) : Prop :=
  forall ctx t, ctx |-- t -> ctx |== t.
  
Definition weak_complete (sem: Semantic) (pt: ProofTheory) : Prop :=
  forall t, |== t -> |-- t.

Definition strong_complete (sem: Semantic) (pt: ProofTheory) : Prop :=
  forall ctx t, ctx |== t -> ctx |-- t.

Inductive IPC_derive: Context -> Term -> Prop :=
  | assum : forall ctx a, ctx a = true -> IPC_derive ctx a
  | and_elim_l : forall ctx a b, IPC_derive ctx (a && b) -> IPC_derive ctx a
  | and_elim_r : forall ctx a b, IPC_derive ctx (a && b) -> IPC_derive ctx b
  | and_intro : forall ctx a b, IPC_derive ctx a -> IPC_derive ctx b -> IPC_derive ctx (a && b)
  | or_elim : forall ctx a b c, IPC_derive ctx (a || b) ->
                IPC_derive (ctx;;a) c -> IPC_derive (ctx;;b) c -> IPC_derive ctx c
  | or_intro_l : forall ctx a b, IPC_derive ctx a -> IPC_derive ctx (a || b)
  | or_intro_r : forall ctx a b, IPC_derive ctx b -> IPC_derive ctx (a || b)
  | imp_elim : forall ctx a b, IPC_derive ctx a -> IPC_derive ctx (a --> b) -> IPC_derive ctx b
  | imp_intro : forall ctx a b, IPC_derive (ctx;;a) b -> IPC_derive ctx (a --> b)
  | false_elim : forall ctx a, IPC_derive ctx falsep -> IPC_derive ctx a.

Instance IPC : ProofTheory := mk_pt IPC_derive.

Lemma IPC_weakening: forall ctx1 ctx2 t,
  (forall t0, ctx1 t0 = true -> ctx2 t0 = true) ->
  ctx1 |-- t -> ctx2 |-- t.
Proof.
  intros.
  revert ctx2 H.
  induction H0; intros.
  + apply assum.
    apply H0; auto.
  + apply and_elim_l with b.
    apply IHIPC_derive; auto.
  + apply and_elim_r with a.
    apply IHIPC_derive; auto.
  + apply and_intro.
    - apply IHIPC_derive1; auto.
    - apply IHIPC_derive2; auto.
  + apply or_elim with (a := a) (b := b).
    - apply IHIPC_derive1; auto.
    - apply IHIPC_derive2; auto.
      intro t.
      specialize (H t).
      unfold ExtendContext.
      destruct (term_eq t a); tauto.
    - apply IHIPC_derive3; auto.
      intro t.
      specialize (H t).
      unfold ExtendContext.
      destruct (term_eq t b); tauto.
  + apply or_intro_l.
    apply IHIPC_derive; auto.
  + apply or_intro_r.
    apply IHIPC_derive; auto.
  + apply imp_elim with a.
    - apply IHIPC_derive1; auto.
    - apply IHIPC_derive2; auto.
  + apply imp_intro.
    apply IHIPC_derive; auto.
    intro t.
    specialize (H t).
    unfold ExtendContext.
    destruct (term_eq t a); tauto.
  + apply false_elim.
    apply IHIPC_derive; auto.
Qed.

Lemma IPC_substitution: forall ctx1 ctx2 t,
  (forall t0, ctx2 t0 = true -> ctx1 |-- t0) ->
  ctx2 |-- t ->
  ctx1 |-- t.
Proof.
  intros.
  revert ctx1 H; induction H0; intros.
  + apply H0; auto.
  + apply and_elim_l with b.
    apply IHIPC_derive; auto.
  + apply and_elim_r with a.
    apply IHIPC_derive; auto.
  + apply and_intro.
    - apply IHIPC_derive1; auto.
    - apply IHIPC_derive2; auto.
  + apply or_elim with (a := a) (b := b).
    - apply IHIPC_derive1; auto.
    - apply IHIPC_derive2; auto.
      unfold ExtendContext.
      intros t ?.
      destruct (term_eq t a).
      * apply assum.
        subst.
        destruct (term_eq a a); congruence.
      * apply IPC_weakening with ctx1; auto.
        intros.
        destruct (term_eq t0 a); congruence.
    - apply IHIPC_derive3; auto.
      unfold ExtendContext.
      intros t ?.
      destruct (term_eq t b).
      * apply assum.
        subst.
        destruct (term_eq b b); congruence.
      * apply IPC_weakening with ctx1; auto.
        intros.
        destruct (term_eq t0 b); congruence.
  + apply or_intro_l.
    apply IHIPC_derive; auto.
  + apply or_intro_r.
    apply IHIPC_derive; auto.
  + apply imp_elim with a.
    - apply IHIPC_derive1; auto.
    - apply IHIPC_derive2; auto.
  + apply imp_intro.
    apply IHIPC_derive; auto.
    unfold ExtendContext.
    intros t ?.
    destruct (term_eq t a).
    * apply assum.
      subst.
      destruct (term_eq a a); congruence.
    * apply IPC_weakening with ctx1; auto.
      intros.
      destruct (term_eq t0 a); congruence.
  + apply false_elim.
    apply IHIPC_derive; auto.
Qed.
    
    
Section KripkeSemantic.

Class Frame : Type := {
  Worlds: Type;
  access: Worlds -> Worlds -> Prop;
  access_refl: forall w, access w w;
  access_trans: forall u v w, access u v -> access v w -> access u w
}.

Class Model: Type := {
  F: Frame;
  eval: Worlds -> Var -> bool;
  hereditary: forall w v: Worlds, access w v -> (forall x: Var, eval w x = true -> eval v x = true)
}.

Existing Instance F.

Class KripkeSem : Type := {
  M: Model;
  Kripke_Sat : Worlds -> Term -> Prop;
  satisfy_ind: forall (w: Worlds) (t: Term),
    Kripke_Sat w t <->
    match t with
    | andp t1 t2 => Kripke_Sat w t1 /\ Kripke_Sat w t2
    | orp t1 t2 => Kripke_Sat w t1 \/ Kripke_Sat w t2
    | impp t1 t2 => forall v, access w v -> Kripke_Sat v t1 -> Kripke_Sat v t2
    | falsep => False
    | varp x => eval w x = true
    end
}.

Lemma Kripke_Sat_mono: forall `{KripkeSem} w v t, access w v -> Kripke_Sat w t -> Kripke_Sat v t.
Proof.
  intros.
  induction t; apply satisfy_ind in H1; apply satisfy_ind.
  + tauto.
  + tauto.
  + intros.
    specialize (H1 v0 (access_trans _ _ _ H0 H2)).
    tauto.
  + tauto.
  + eapply hereditary; eauto.
Qed.

Existing Instance M.

Class PointModel: Type := {
  KS: KripkeSem;
  w: Worlds
}.

Existing Instance KS.

End KripkeSemantic.

Instance Kripke_sem: Semantic := mk_sem PointModel (fun KM t => Kripke_Sat w t).

Fixpoint denote (f: Var -> Prop) (t: Term) : Prop :=
  match t with
  | andp t1 t2 => denote f t1 /\ denote f t2
  | orp t1 t2 => denote f t1 \/ denote f t2
  | impp t1 t2 => denote f t1 -> denote f t2
  | falsep => False
  | varp x => f x
  end.

Definition Trivial_sem: Semantic := mk_sem (Var -> Prop) denote.

Lemma sound_Trivial_IPC: sound Trivial_sem IPC.
Proof.
  unfold sound.
  intros.
  induction H; intros M CONTEXT.
  + apply CONTEXT.
    auto.
  + specialize (IHIPC_derive M CONTEXT).
    simpl in IHIPC_derive |- *.
    tauto.
  + specialize (IHIPC_derive M CONTEXT).
    simpl in IHIPC_derive |- *.
    tauto.
  + specialize (IHIPC_derive1 M CONTEXT).
    specialize (IHIPC_derive2 M CONTEXT).
    simpl in IHIPC_derive1, IHIPC_derive2 |- *.
    tauto.
  + specialize (IHIPC_derive1 M CONTEXT).
    destruct IHIPC_derive1.
    - assert (CONTEXT_a: forall t0 : Term, (ctx;; a) t0 = true -> M |= t0).
      Focus 1. {
        intros.
        unfold ExtendContext in H3.
        destruct (term_eq t0 a).
        + subst; exact H2.
        + apply CONTEXT; auto.
      } Unfocus.
      exact (IHIPC_derive2 M CONTEXT_a).
    - assert (CONTEXT_b: forall t0 : Term, (ctx;; b) t0 = true -> M |= t0).
      Focus 1. {
        intros.
        unfold ExtendContext in H3.
        destruct (term_eq t0 b).
        + subst; exact H2.
        + apply CONTEXT; auto.
      } Unfocus.
      exact (IHIPC_derive3 M CONTEXT_b).
  + specialize (IHIPC_derive M CONTEXT).
    simpl in IHIPC_derive |- *.
    tauto.
  + specialize (IHIPC_derive M CONTEXT).
    simpl in IHIPC_derive |- *.
    tauto.
  + specialize (IHIPC_derive1 M CONTEXT).
    specialize (IHIPC_derive2 M CONTEXT).
    simpl in IHIPC_derive1, IHIPC_derive2 |- *.
    tauto.
  + simpl; intros.
    assert (CONTEXT_a: forall t0 : Term, (ctx;; a) t0 = true -> M |= t0).
    Focus 1. {
      intros.
      unfold ExtendContext in H1.
      destruct (term_eq t0 a).
      + subst; exact H0.
      + apply CONTEXT; auto.
    } Unfocus.
    specialize (IHIPC_derive M CONTEXT_a).
    exact IHIPC_derive.
  + specialize (IHIPC_derive M CONTEXT).
    simpl in IHIPC_derive |- *.
    tauto.
Qed.

Lemma sound_Kripke_IPC: sound Kripke_sem IPC.
Proof.
  unfold sound.
  intros.
  induction H; intros M CONTEXT.
  + apply CONTEXT.
    auto.
  + specialize (IHIPC_derive M CONTEXT).
    simpl in IHIPC_derive |- *.
    apply satisfy_ind in IHIPC_derive.
    tauto.
  + specialize (IHIPC_derive M CONTEXT).
    simpl in IHIPC_derive |- *.
    apply satisfy_ind in IHIPC_derive.
    tauto.
  + specialize (IHIPC_derive1 M CONTEXT).
    specialize (IHIPC_derive2 M CONTEXT).
    simpl in IHIPC_derive1, IHIPC_derive2 |- *.
    apply satisfy_ind.
    tauto.
  + specialize (IHIPC_derive1 M CONTEXT).
    simpl in IHIPC_derive1; apply satisfy_ind in IHIPC_derive1.
    destruct IHIPC_derive1.
    - assert (CONTEXT_a: forall t0 : Term, (ctx;; a) t0 = true -> M |= t0).
      Focus 1. {
        intros.
        unfold ExtendContext in H3.
        destruct (term_eq t0 a).
        + subst; exact H2.
        + apply CONTEXT; auto.
      } Unfocus.
      exact (IHIPC_derive2 M CONTEXT_a).
    - assert (CONTEXT_b: forall t0 : Term, (ctx;; b) t0 = true -> M |= t0).
      Focus 1. {
        intros.
        unfold ExtendContext in H3.
        destruct (term_eq t0 b).
        + subst; exact H2.
        + apply CONTEXT; auto.
      } Unfocus.
      exact (IHIPC_derive3 M CONTEXT_b).
  + specialize (IHIPC_derive M CONTEXT).
    simpl in IHIPC_derive |- *.
    apply satisfy_ind.
    tauto.
  + specialize (IHIPC_derive M CONTEXT).
    simpl in IHIPC_derive |- *.
    apply satisfy_ind.
    tauto.
  + specialize (IHIPC_derive1 M CONTEXT).
    specialize (IHIPC_derive2 M CONTEXT).
    simpl in IHIPC_derive1, IHIPC_derive2 |- *.
    apply satisfy_ind in IHIPC_derive2.
    specialize (IHIPC_derive2 w (access_refl _)).
    tauto.
  + simpl.
    apply satisfy_ind.
    intros.
    rename M into M0.
    pose (Build_PointModel KS v) as M1.
    assert (CONTEXT_a: forall t0 : Term, (ctx;; a) t0 = true -> M1 |= t0).
    Focus 1. {
      intros.
      unfold ExtendContext in H2.
      destruct (term_eq t0 a).
      + subst; exact H1.
      + specialize (CONTEXT t0 H2).
        simpl.
        apply Kripke_Sat_mono with w; auto.
    } Unfocus.
    specialize (IHIPC_derive M1 CONTEXT_a).
    exact IHIPC_derive.
  + specialize (IHIPC_derive M CONTEXT).
    simpl in IHIPC_derive |- *.
    apply satisfy_ind in IHIPC_derive.
    tauto.
Qed.

End IPC.

Module IPC_Notation.
Notation "x && y" := (andp x y) (at level 40, left associativity) : IPC_scope.
Notation "x || y" := (orp x y) (at level 50, left associativity) : IPC_scope.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : IPC_scope.
Notation "'FF'" := falsep : IPC_scope.
Notation "ctx ;; t" := (ExtendContext ctx t) (at level 65, left associativity) : IPC_scope.
Notation "M  |=  t" := (satisfy M t) (at level 60, no associativity) : IPC_scope.
Notation "|==  t" := (valid t) (at level 61, no associativity) : IPC_scope.
Notation "ctx  |==  t" := (sem_conseq ctx t) (at level 60, no associativity) : IPC_scope.
Notation "ctx  |--  t" := (derivable ctx t) (at level 60, no associativity) : IPC_scope.
Notation "|--  t" := (provable t) (at level 61, no associativity) : IPC_scope.
End IPC_Notation.

Module CanonicalModel.

Context {venv: Var_env}.

Existing Instance IPC.
Import IPC_Notation.
Local Open Scope IPC_scope.

Context (IPC_classic: forall ctx t, {ctx |-- t} + {~ ctx |-- t}).

Definition W := {w: Context & 
                   (forall t, w |-- t -> w t = true) /\
                   (forall t1 t2, w (t1 || t2) = true -> w t1 = true \/ w t2 = true)}.

Definition R (w v: W) := match w, v with existT w _, existT v _ => forall t, w t = true -> v t = true end.

Definition gen (ctx: Context) : Context := fun t => if IPC_classic ctx t then true else false.

Lemma gen_derive: forall ctx t, ctx |-- t <-> gen ctx |-- t.
Proof.
  intros; split; intros.
  + apply assum.
    unfold gen.
    destruct (IPC_classic ctx t); tauto.
  + apply IPC_substitution with (gen ctx); auto.
    clear; intros.
    unfold gen in H.
    destruct (IPC_classic ctx t0); congruence.
Qed.

Definition Gen (ctx: Context) : W.
  exists (gen ctx).
  split.
  + intros.
    apply gen_derive in H.
    unfold gen.
    destruct (IPC_classic ctx t); congruence.
  + 

Definition F: Frame.
  apply (Build_Frame W R).
  + intros.
    unfold R.
    destruct w0; simpl.
    intros; auto.
  + unfold R.
    intros u v w.
    destruct u, v, w.
    intros.
    specialize (H t).
    specialize (H0 t).
    tauto.
Defined.

Definition V (w: W) (v: Var) : bool := let (w, _) := w in (w (varp v)).

Definition M: Model.
  apply (Build_Model F V).
  intros w v ? x.
  simpl in H.
  unfold R in H; unfold V; destruct w, v.
  apply H.
Defined.


Instance CanonicalModel: KripkeSem.
  apply (Build_KripkeSem M (fun w t => let (w, _) := w in w t = true)).
  intros w t; revert w; induction t; intros [w Hw].
  + split; intros; [split |]; apply (proj1 Hw).
    - apply and_elim_l with t2.
      apply assum; auto.
    - apply and_elim_r with t1.
      apply assum; auto.
    - apply and_intro; apply assum; tauto.
  + split; [intro | intros [? | ?]].
    - exact (proj2 Hw t1 t2 H).
    - apply (proj1 Hw).
      apply or_intro_l.
      apply assum; auto.
    - apply (proj1 Hw).
      apply or_intro_r.
      apply assum; auto.
  + split; intros.
    - simpl in H0.
      destruct v as [v Hv].
      assert (IPC_derive (w;; t1) t2).
      Focus 1. {
        apply imp_elim with t1.
        + apply assum.
          unfold ExtendContext.
          destruct (term_eq t1 t1); congruence.
        + apply IPC_weakening with w.
          - clear.
            intros.
            unfold ExtendContext.
            destruct (term_eq t0 t1); congruence.
          - apply assum; auto.
      } Unfocus.
      apply (proj1 Hv).
      apply IPC_weakening with (w;; t1); auto.
      clear - H1 H0.
      unfold ExtendContext.
      intros.
      destruct (term_eq t0 t1).
      * subst. auto.
      * apply H0; auto.
    - apply (proj1 Hw).
      simpl in H.
      specialize (
      
    
Lemma complete_Kripke_IPC: strong_complete Kripke_sem IPC.
Proof.
  unfold strong_complete.
  intros.
  pose ( (fun w v => match w, v with existT w _, existT v _ => forall t, w t = true -> v t = true end)).  : Type := {
  Worlds: Type;
  access: Worlds -> Worlds -> bool;
  access_refl: forall w, access w w = true;
  access_trans: forall u v w, access u v = true -> access v w = true -> access u w = true
}.