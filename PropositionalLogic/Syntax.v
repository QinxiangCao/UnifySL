Require Import Coq.Logic.ProofIrrelevance.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.MinimunLogic.SyntacticReduction.

Class PropositionalLanguage (L: Language) {nL: NormalLanguage L}: Type := {
  andp : expr -> expr -> expr;
  orp : expr -> expr -> expr;
  iffp : expr -> expr -> expr;
  negp : expr -> expr;
  truep : expr;
  and1_propag: expr -> single_propagation;
  and2_propag: expr -> single_propagation;
  or1_propag: expr -> single_propagation;
  or2_propag: expr -> single_propagation;
  iff1_propag: expr -> single_propagation;
  iff2_propag: expr -> single_propagation;
  neg_propag: single_propagation;
  and1_propag_denote: forall x y, single_propagation_denote (and1_propag x) y = andp y x;
  and2_propag_denote: forall x y, single_propagation_denote (and2_propag x) y = andp x y;
  or1_propag_denote: forall x y, single_propagation_denote (or1_propag x) y = orp y x;
  or2_propag_denote: forall x y, single_propagation_denote (or2_propag x) y = orp x y;
  iff1_propag_denote: forall x y, single_propagation_denote (iff1_propag x) y = iffp y x;
  iff2_propag_denote: forall x y, single_propagation_denote (iff2_propag x) y = iffp x y;
  neg_propag_denote: forall x, single_propagation_denote neg_propag x = negp x
}.

Inductive PropositionalPropag (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L}: single_propagation -> Prop :=
  | imp1_prop_propag: forall x: expr, PropositionalPropag L (imp1_propag x)
  | imp2_prop_propag: forall x: expr, PropositionalPropag L (imp2_propag x)
  | and1_prop_propag: forall x: expr, PropositionalPropag L (and1_propag x)
  | and2_prop_propag: forall x: expr, PropositionalPropag L (and2_propag x)
  | or1_prop_propag: forall x: expr, PropositionalPropag L (or1_propag x)
  | or2_prop_propag: forall x: expr, PropositionalPropag L (or2_propag x)
  | iff1_prop_propag: forall x: expr, PropositionalPropag L (iff1_propag x)
  | iff2_prop_propag: forall x: expr, PropositionalPropag L (iff2_propag x)
  | neg_prop_propag: PropositionalPropag L neg_propag.

Notation "x && y" := (andp x y) (at level 40, left associativity) : PropositionalLogic.
Notation "x || y" := (orp x y) (at level 50, left associativity) : PropositionalLogic.
Notation "x <--> y" := (iffp x y) (at level 60, no associativity) : PropositionalLogic.
Notation "~~ x" := (negp x) (at level 35) : PropositionalLogic.
Notation "'TT'" := truep : PropositionalLogic.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Lemma and_reduce {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {R: SyntacticReduction L}:
  forall x1 x2 y1 y2,
    reduce x1 x2 ->
    reduce y1 y2 ->
    reduce (x1 && y1) (x2 && y2).
Proof.
  intros.
  eapply reduce_trans.
  + apply propag_reduce_reduce.
    rewrite <- and1_propag_denote.
    apply (propag_reduce_spec _ _ _ (and1_propag y1 :: nil) H).
  + simpl; rewrite and1_propag_denote.
    apply propag_reduce_reduce.
    rewrite <- !and2_propag_denote.
    apply (propag_reduce_spec _ _ _ (and2_propag x2 :: nil) H0).
Qed.

Lemma or_reduce {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {R: SyntacticReduction L}:
  forall x1 x2 y1 y2,
    reduce x1 x2 ->
    reduce y1 y2 ->
    reduce (x1 || y1) (x2 || y2).
Proof.
  intros.
  eapply reduce_trans.
  + apply propag_reduce_reduce.
    rewrite <- or1_propag_denote.
    apply (propag_reduce_spec _ _ _ (or1_propag y1 :: nil) H).
  + simpl; rewrite or1_propag_denote.
    apply propag_reduce_reduce.
    rewrite <- !or2_propag_denote.
    apply (propag_reduce_spec _ _ _ (or2_propag x2 :: nil) H0).
Qed.

Lemma iff_reduce {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {R: SyntacticReduction L}:
  forall x1 x2 y1 y2,
    reduce x1 x2 ->
    reduce y1 y2 ->
    reduce (x1 <--> y1) (x2 <--> y2).
Proof.
  intros.
  eapply reduce_trans.
  + apply propag_reduce_reduce.
    rewrite <- iff1_propag_denote.
    apply (propag_reduce_spec _ _ _ (iff1_propag y1 :: nil) H).
  + simpl; rewrite iff1_propag_denote.
    apply propag_reduce_reduce.
    rewrite <- !iff2_propag_denote.
    apply (propag_reduce_spec _ _ _ (iff2_propag x2 :: nil) H0).
Qed.

Lemma neg_reduce {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {R: SyntacticReduction L}:
  forall x1 x2, reduce x1 x2 -> reduce (~~ x1) (~~ x2).
Proof.
  intros.
  apply propag_reduce_reduce.
  rewrite <- !neg_propag_denote.
  apply (propag_reduce_spec _ _ _ (neg_propag :: nil) H).
Qed.

Module ImpNegAsPrime.

Inductive atomic_reduce {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L}: expr -> expr -> Prop :=
| andp_reduce: forall x y, atomic_reduce (x && y) (~~ (x --> ~~ y))
| orp_reduce: forall x y, atomic_reduce (x || y) (~~ x --> y)
.

End ImpNegAsPrime.

Module ImpAndOrAsPrime.

Inductive atomic_reduce {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L}: expr -> expr -> Prop :=
| negp_reduce: forall x, atomic_reduce (~~ x) (x --> FF)
.

End ImpAndOrAsPrime.

Module ReduceIff.

Inductive atomic_reduce {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L}: expr -> expr -> Prop :=
| iff_reduce: forall x y, atomic_reduce (x <--> y) ((x --> y) && (y --> x)).

End ReduceIff.

Module ReduceFalse.

Inductive atomic_reduce {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L}: expr -> expr -> Prop :=
| falsep_reduce: atomic_reduce FF (~~ TT).

End ReduceFalse.

Module ReduceTrue.

Inductive atomic_reduce {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L}: expr -> expr -> Prop :=
| truep_reduce: atomic_reduce TT (FF --> FF).

End ReduceTrue.

Definition MendelsonReduction {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L}: SyntacticReduction L :=
  Build_SyntacticReduction _
    (relation_disjunction
       ImpNegAsPrime.atomic_reduce
       (relation_disjunction
         ReduceIff.atomic_reduce
         ReduceFalse.atomic_reduce)).

Definition IntuitionisticReduction {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L}: SyntacticReduction L :=
  Build_SyntacticReduction _
    (relation_disjunction
       ImpAndOrAsPrime.atomic_reduce
       (relation_disjunction
         ReduceIff.atomic_reduce
         ReduceTrue.atomic_reduce)).

Definition orp_witnessed {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L}: context -> Prop :=
  fun Phi => forall x y, Phi (x || y) -> Phi x \/ Phi y.

Module PropositionalLanguage.

Inductive expr {Var: Type}: Type :=
  | andp : expr -> expr -> expr
  | orp : expr -> expr -> expr
  | impp : expr -> expr -> expr
  | iffp : expr -> expr -> expr
  | negp : expr -> expr
  | truep : expr
  | falsep : expr
  | varp : Var -> expr.

Implicit Arguments expr.

Inductive single_propagation {Var: Type}: Type :=
  | and1_propag : expr Var -> single_propagation
  | and2_propag : expr Var -> single_propagation
  | or1_propag : expr Var -> single_propagation
  | or2_propag : expr Var -> single_propagation
  | imp1_propag : expr Var -> single_propagation
  | imp2_propag : expr Var -> single_propagation
  | iff1_propag : expr Var -> single_propagation
  | iff2_propag : expr Var -> single_propagation
  | neg_propag : single_propagation
.

Implicit Arguments single_propagation.

Definition single_propagation_denote {Var: Type} (sp: single_propagation Var) (x: expr Var): expr Var :=
  match sp with
  | and1_propag y => andp x y
  | and2_propag y => andp y x
  | or1_propag y => orp x y
  | or2_propag y => orp y x
  | imp1_propag y => impp x y
  | imp2_propag y => impp y x
  | iff1_propag y => iffp x y
  | iff2_propag y => iffp y x
  | neg_propag => negp x
  end.

Instance L (Var: Type): Language :=
  Build_Language (expr Var) (single_propagation Var) single_propagation_denote.

Instance nL (Var: Type): NormalLanguage (L Var) :=
  Build_NormalLanguage (L Var) falsep impp imp1_propag imp2_propag (fun _ _ => eq_refl) (fun _ _ => eq_refl).

Instance pL (Var: Type): PropositionalLanguage (L Var) :=
  Build_PropositionalLanguage (L Var) (nL Var) andp orp iffp negp truep
    and1_propag and2_propag or1_propag or2_propag iff1_propag iff2_propag neg_propag
    (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ _ => eq_refl)
    (fun _ _ => eq_refl) (fun _ _ => eq_refl) (fun _ => eq_refl).

Definition mendelson_andp {Var: Type} (x y: expr Var): expr Var := negp (impp x (negp y)).

Definition mendelson_orp {Var: Type} (x y: expr Var): expr Var := impp (negp x) y.

Definition mendelson_iffp {Var: Type} (x y: expr Var): expr Var := mendelson_andp (impp x y) (impp y x).

Fixpoint mendelson_reduce {Var: Type} (x: expr Var): expr Var :=
  match x with
  | andp y z => mendelson_andp (mendelson_reduce y) (mendelson_reduce z)
  | orp y z => mendelson_orp (mendelson_reduce y) (mendelson_reduce z)
  | impp y z => impp (mendelson_reduce y) (mendelson_reduce z)
  | iffp y z => mendelson_iffp (mendelson_reduce y) (mendelson_reduce z)
  | negp y => negp (mendelson_reduce y)
  | truep => truep
  | falsep => negp truep
  | varp p => varp p
  end.

Fixpoint mendelson_normal_form {Var: Type} (x: expr Var): Prop :=
  match x with
  | andp y z => False
  | orp y z => False
  | impp y z => mendelson_normal_form y /\ mendelson_normal_form z
  | iffp y z => False
  | negp y => mendelson_normal_form y
  | truep => True
  | falsep => False
  | varp p => True
  end.

Definition nMendelsonReduction {Var: Type}: NormalSyntacticReduction (L Var) MendelsonReduction.
  refine (Build_NormalSyntacticReduction (L Var) _ mendelson_normal_form _).
  intros; exists (mendelson_reduce x); split.
  + induction x.
    - simpl; unfold mendelson_andp.
      eapply reduce_trans.
      * apply (@and_reduce (L Var) (nL Var) (pL Var) MendelsonReduction _ _ _ _ IHx1 IHx2).
      * apply reduce_step.
        left; apply @ImpNegAsPrime.andp_reduce.
    - simpl; unfold mendelson_orp.
      eapply reduce_trans.
      * apply (@or_reduce (L Var) (nL Var) (pL Var) MendelsonReduction _ _ _ _ IHx1 IHx2).
      * apply reduce_step.
        left; apply @ImpNegAsPrime.orp_reduce.
    - simpl.
      apply (@imp_reduce (L Var) (nL Var) MendelsonReduction _ _ _ _ IHx1 IHx2).
    - simpl; unfold mendelson_iffp, mendelson_andp.
      eapply reduce_trans; [| eapply reduce_trans].
      * apply (@iff_reduce (L Var) (nL Var) (pL Var) MendelsonReduction _ _ _ _ IHx1 IHx2).
      * apply reduce_step.
        right; left; apply @ReduceIff.iff_reduce.
      * simpl.
        apply reduce_step.
        left; apply @ImpNegAsPrime.andp_reduce.
    - simpl.
      apply (@neg_reduce (L Var) (nL Var) (pL Var) MendelsonReduction _ _ IHx).
    - apply reduce_refl.
    - apply reduce_step.
      right; right; apply @ReduceFalse.falsep_reduce.
    - apply reduce_refl.
  + induction x; simpl; auto.
Defined.

Definition intuitionistic_iffp {Var: Type} (x y: expr Var): expr Var := andp (impp x y) (impp y x).

Definition intuitionistic_negp {Var: Type} (x: expr Var): expr Var := impp x falsep.

Fixpoint intuitionistic_reduce {Var: Type} (x: expr Var): expr Var :=
  match x with
  | andp y z => andp (intuitionistic_reduce y) (intuitionistic_reduce z)
  | orp y z => orp (intuitionistic_reduce y) (intuitionistic_reduce z)
  | impp y z => impp (intuitionistic_reduce y) (intuitionistic_reduce z)
  | iffp y z => intuitionistic_iffp (intuitionistic_reduce y) (intuitionistic_reduce z)
  | negp y => intuitionistic_negp (intuitionistic_reduce y)
  | truep => impp falsep falsep
  | falsep => falsep
  | varp p => varp p
  end.

Fixpoint intuitionistic_normal_form {Var: Type} (x: expr Var): Prop :=
  match x with
  | andp y z => intuitionistic_normal_form y /\ intuitionistic_normal_form z
  | orp y z => intuitionistic_normal_form y /\ intuitionistic_normal_form z
  | impp y z => intuitionistic_normal_form y /\ intuitionistic_normal_form z
  | iffp y z => False
  | negp y => False
  | truep => False
  | falsep => True
  | varp p => True
  end.

Definition nIntuitionisticReduction {Var: Type}: NormalSyntacticReduction (L Var) IntuitionisticReduction.
  refine (Build_NormalSyntacticReduction (L Var) _ intuitionistic_normal_form _).
  intros; exists (intuitionistic_reduce x); split.
  + induction x.
    - simpl.
      apply (@and_reduce (L Var) (nL Var) (pL Var) IntuitionisticReduction _ _ _ _ IHx1 IHx2).
    - apply (@or_reduce (L Var) (nL Var) (pL Var) IntuitionisticReduction _ _ _ _ IHx1 IHx2).
    - simpl.
      apply (@imp_reduce (L Var) (nL Var) IntuitionisticReduction _ _ _ _ IHx1 IHx2).
    - simpl; unfold intuitionistic_iffp.
      eapply reduce_trans.
      * apply (@iff_reduce (L Var) (nL Var) (pL Var) IntuitionisticReduction _ _ _ _ IHx1 IHx2).
      * apply reduce_step.
        right. left. apply @ReduceIff.iff_reduce.
    - simpl; unfold intuitionistic_negp.
      eapply reduce_trans.
      * apply (@neg_reduce (L Var) (nL Var) (pL Var) IntuitionisticReduction _ _ IHx).
      * apply reduce_step.
        left. apply @ImpAndOrAsPrime.negp_reduce.
    - apply reduce_step.
      right. right. apply @ReduceTrue.truep_reduce.
    - apply reduce_refl.
    - apply reduce_refl.
  + induction x; simpl; auto.
Defined.

Definition rank {Var: Type}: expr Var -> nat :=
  fix rank (x: expr Var): nat :=
    match x with
    | andp y z => 1 + rank y + rank z
    | orp y z => 1 + rank y + rank z
    | impp y z => 1 + rank y + rank z
    | iffp y z => 1 + rank y + rank z
    | negp y => 1 + rank y
    | truep => 0
    | falsep => 0
    | varp p => 0
    end.

Definition formula_countable: forall Var, Countable Var -> Countable (expr Var).
  intros.
  assert (forall n, Countable (sig (fun x: expr Var => rank x <= n))).
  + induction n.
    - apply (@bijection_Countable _ (Var + unit + unit)%type); [| solve_Countable].
      apply bijection_sym.
      apply (FBuild_bijection _ _ (fun x =>
               match x with
               | inl (inl p) => exist (fun x: expr Var => rank x <= 0) (varp p) (le_n 0)
               | inl (inr _) => exist (fun x: expr Var => rank x <= 0) truep (le_n 0)
               | inr _ => exist (fun x: expr Var => rank x <= 0) falsep (le_n 0)
               end)).
      * hnf; intros.
        destruct a1 as [[? | []] | []], a2 as [[? | []] | []]; inversion H; auto.
      * hnf; intros.
        destruct b as [[] HH]; try solve [inversion HH].
        1: exists (inl (inr tt)); eauto; f_equal; apply proof_irrelevance.
        1: exists (inr tt); eauto; f_equal; apply proof_irrelevance.
        1: exists (inl (inl v)); eauto; f_equal; apply proof_irrelevance.
    - set (s := sig (fun x: expr Var => rank x <= n)).
      apply (@injection_Countable _ (s * s + s * s + s * s + s * s + s + unit + unit + Var)%type); [| solve_Countable].
      apply (Build_injection _ _ (fun x y =>
        match y with
        | inl (inl (inl (inl (inl (inl (inl (exist y _, exist z _))))))) => proj1_sig x = andp y z
        | inl (inl (inl (inl (inl (inl (inr (exist y _, exist z _))))))) => proj1_sig x = orp y z
        | inl (inl (inl (inl (inl (inr (exist y _, exist z _)))))) => proj1_sig x = impp y z
        | inl (inl (inl (inl (inr (exist y _, exist z _))))) => proj1_sig x = iffp y z
        | inl (inl (inl (inr (exist y _)))) => proj1_sig x = negp y
        | inl (inl (inr _)) => proj1_sig x = truep
        | inl (inr _) => proj1_sig x = falsep
        | inr p => proj1_sig x = varp p
        end)).
      * hnf; intros.
        destruct a as [[y z | y z | y z | y z | y | | | p] ?H].
        (* 1 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inl (inl (inl (inl (inl (exist _ y H0, exist _ z H1)))))))); auto.
        (* 2 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inl (inl (inl (inl (inr (exist _ y H0, exist _ z H1)))))))); auto.
        (* 3 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inl (inl (inl (inr (exist _ y H0, exist _ z H1))))))); auto.
        (* 4 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inl (inl (inr (exist _ y H0, exist _ z H1)))))); auto.
        (* 5 *) simpl in H. assert (rank y <= n) by omega.
                exists (inl (inl (inl (inr (exist _ y H0))))); auto.
        (* 6 *) exists (inl (inl (inr tt))); auto.
        (* 7 *) exists (inl (inr tt)); auto.
        (* 8 *) exists (inr p); auto.
      * hnf; intros.
        destruct a as [[y z | y z | y z | y z | y | | | p] ?H];
        destruct b1 as [[[[[[[[[y1 ?H] [z1 ?H]] | [[y1 ?H] [z1 ?H]]] | [[y1 ?H] [z1 ?H]]] | [[y1 ?H] [z1 ?H]]]| [y1 ?]]| ] |] | p1]; try solve [inversion H];
        destruct b2 as [[[[[[[[[y2 ?H] [z2 ?H]] | [[y2 ?H] [z2 ?H]]] | [[y2 ?H] [z2 ?H]]] | [[y2 ?H] [z2 ?H]]]| [y2 ?]]| ] |] | p2]; try solve [inversion H0].
        (* 1 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 2 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 3 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 4 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 5 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 6 *) destruct u, u0; auto.
        (* 7 *) destruct u, u0; auto.
        (* 8 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
      * hnf; intros.
        destruct b as [[[[[[[[[y ?H] [z ?H]] | [[y ?H] [z ?H]]] | [[y ?H] [z ?H]]] | [[y ?H] [z ?H]]]| [y ?]]| ] |] | p];
        destruct a1 as [[y1 z1 | y1 z1 | y1 z1 | y1 z1 | y1 | | | p1] ?H]; try solve [inversion H];
        destruct a2 as [[y2 z2 | y2 z2 | y2 z2 | y2 z2 | y2 | | | p2] ?H]; try solve [inversion H0].
        (* 1 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 2 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 3 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 4 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 5 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 6 *) f_equal; apply proof_irrelevance.
        (* 7 *) f_equal; apply proof_irrelevance.
        (* 8 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
  + apply (@injection_Countable _ (sigT (fun n => sig (fun x: expr Var => rank x <= n)))); [| solve_Countable; auto].
    apply (FBuild_injection _ _ (fun x => existT _ (rank x) (exist _ x (le_n _)))).
    hnf; intros.
    simpl in H.
    inversion H; auto.
Qed. (* 20 seconds *)

End PropositionalLanguage.

