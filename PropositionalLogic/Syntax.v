Require Import Logic.LogicBase.
Require Import Logic.SyntacticReduction.

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

Notation "x && y" := (andp x y) (at level 40, left associativity) : PropositionalLogic.
Notation "x || y" := (orp x y) (at level 50, left associativity) : PropositionalLogic.
Notation "x --> y" := (impp x y) (at level 55, right associativity) : PropositionalLogic.
Notation "x <--> y" := (iffp x y) (at level 60, no associativity) : PropositionalLogic.
Notation "~~ x" := (negp x) (at level 35) : PropositionalLogic.
Notation "'FF'" := falsep : PropositionalLogic.
Notation "'TT'" := truep : PropositionalLogic.

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
| andp_reduce: forall x y, atomic_reduce (x && y ) (~~ (x --> ~~ y))
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
       ReduceIff.atomic_reduce).

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
        apply (@propag_reduce_spec (L Var) _ _ _ nil).
        left; apply @ImpNegAsPrime.andp_reduce.
    - simpl; unfold mendelson_orp.
      eapply reduce_trans.
      * apply (@or_reduce (L Var) (nL Var) (pL Var) MendelsonReduction _ _ _ _ IHx1 IHx2).
      * apply reduce_step.
        apply (@propag_reduce_spec (L Var) _ _ _ nil).
        left; apply @ImpNegAsPrime.orp_reduce.
    - simpl.
      apply (@imp_reduce (L Var) (nL Var) MendelsonReduction _ _ _ _ IHx1 IHx2).
    - simpl; unfold mendelson_iffp, mendelson_andp.
      eapply reduce_trans; [| eapply reduce_trans].
      * apply (@iff_reduce (L Var) (nL Var) (pL Var) MendelsonReduction _ _ _ _ IHx1 IHx2).
      * apply reduce_step.
        eapply (@propag_reduce_spec (L Var) _ _ _ nil).
        right; left; apply @ReduceIff.iff_reduce.
      * simpl.
        apply reduce_step.
        eapply (@propag_reduce_spec (L Var) _ _ _ nil).
        left; apply @ImpNegAsPrime.andp_reduce.
    - simpl.
      apply (@neg_reduce (L Var) (nL Var) (pL Var) MendelsonReduction _ _ IHx).
    - apply reduce_refl.
    - apply reduce_step.
      eapply (@propag_reduce_spec (L Var) _ _ _ nil).
      right; right; apply @ReduceFalse.falsep_reduce.
    - apply reduce_refl.
  + induction x; simpl; auto.
Defined.

End PropositionalLanguage.

