Require Import Coq.Logic.ProofIrrelevance.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.

Class PropositionalLanguage (L: Language) {nL: NormalLanguage L}: Type := {
  andp : expr -> expr -> expr;
  orp : expr -> expr -> expr;
  falsep: expr
}.

Definition negp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} (x: expr): expr := impp x falsep.
Definition iffp {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} (x y: expr): expr := andp (impp x y) (impp y x).
Definition truep {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L}: expr := impp falsep falsep.

Notation "x && y" := (andp x y) (at level 40, left associativity) : PropositionalLogic.
Notation "x || y" := (orp x y) (at level 50, left associativity) : PropositionalLogic.
Notation "x <--> y" := (iffp x y) (at level 60, no associativity) : PropositionalLogic.
Notation "~~ x" := (negp x) (at level 35) : PropositionalLogic.
Notation "'FF'" := falsep : PropositionalLogic.
Notation "'TT'" := truep : PropositionalLogic.

Local Open Scope logic_base.
Local Open Scope PropositionalLogic.

Definition orp_witnessed {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {Gamma: ProofTheory L}: context -> Prop :=
  fun Phi => forall x y, Phi (x || y) -> Phi x \/ Phi y.

Module PropositionalLanguage.

Inductive expr {Var: Type}: Type :=
  | andp : expr -> expr -> expr
  | orp : expr -> expr -> expr
  | impp : expr -> expr -> expr
  | falsep : expr
  | varp : Var -> expr.

Implicit Arguments expr.

Instance L (Var: Type): Language :=
  Build_Language (expr Var).

Instance nL (Var: Type): NormalLanguage (L Var) :=
  Build_NormalLanguage (L Var) impp.

Instance pL (Var: Type): PropositionalLanguage (L Var) :=
  Build_PropositionalLanguage (L Var) (nL Var) andp orp falsep.

Definition rank {Var: Type}: expr Var -> nat :=
  fix rank (x: expr Var): nat :=
    match x with
    | andp y z => 1 + rank y + rank z
    | orp y z => 1 + rank y + rank z
    | impp y z => 1 + rank y + rank z
    | falsep => 0
    | varp p => 0
    end.

Definition formula_countable: forall Var, Countable Var -> Countable (expr Var).
  intros.
  assert (forall n, Countable (sig (fun x: expr Var => rank x <= n))).
  + induction n.
    - apply (@bijection_Countable _ (Var + unit)%type); [| solve_Countable].
      apply bijection_sym.
      apply (FBuild_bijection _ _ (fun x =>
               match x with
               | inl p => exist (fun x: expr Var => rank x <= 0) (varp p) (le_n 0)
               | inr _ => exist (fun x: expr Var => rank x <= 0) falsep (le_n 0)
               end)).
      * hnf; intros.
        destruct a1 as [? | []], a2 as [? | []]; inversion H; auto.
      * hnf; intros.
        destruct b as [[] HH]; try solve [inversion HH].
        1: exists (inr tt); eauto; f_equal; apply proof_irrelevance.
        1: exists (inl v); eauto; f_equal; apply proof_irrelevance.
    - set (s := sig (fun x: expr Var => rank x <= n)).
      apply (@injection_Countable _ (s * s + s * s + s * s + unit + Var)%type); [| solve_Countable].
      apply (Build_injection _ _ (fun x y =>
        match y with
        | inl (inl (inl (inl (exist y _, exist z _)))) => proj1_sig x = andp y z
        | inl (inl (inl (inr (exist y _, exist z _)))) => proj1_sig x = orp y z
        | inl (inl (inr (exist y _, exist z _))) => proj1_sig x = impp y z
        | inl (inr _) => proj1_sig x = falsep
        | inr p => proj1_sig x = varp p
        end)).
      * hnf; intros.
        destruct a as [[y z | y z | y z | | p] ?H].
        (* 1 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inl (inl (exist _ y H0, exist _ z H1))))); auto.
        (* 2 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inl (inr (exist _ y H0, exist _ z H1))))); auto.
        (* 3 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inr (exist _ y H0, exist _ z H1)))); auto.
        (* 4 *) exists (inl (inr tt)); auto.
        (* 5 *) exists (inr p); auto.
      * hnf; intros.
        destruct a as [[y z | y z | y z | | p] ?H];
        destruct b1 as [[[[[[y1 ?H] [z1 ?H]] | [[y1 ?H] [z1 ?H]]] | [[y1 ?H] [z1 ?H]]] |] | p1]; try solve [inversion H];
        destruct b2 as [[[[[[y2 ?H] [z2 ?H]] | [[y2 ?H] [z2 ?H]]] | [[y2 ?H] [z2 ?H]]] |] | p2]; try solve [inversion H0].
        (* 1 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 2 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 3 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 4 *) destruct u, u0; auto.
        (* 5 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
      * hnf; intros.
        destruct b as [[[[[[y ?H] [z ?H]] | [[y ?H] [z ?H]]] | [[y ?H] [z ?H]]] |] | p];
        destruct a1 as [[y1 z1 | y1 z1 | y1 z1 | | p1] ?H]; try solve [inversion H];
        destruct a2 as [[y2 z2 | y2 z2 | y2 z2 | | p2] ?H]; try solve [inversion H0].
        (* 1 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 2 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 3 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 4 *) f_equal; apply proof_irrelevance.
        (* 5 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
  + apply (@injection_Countable _ (sigT (fun n => sig (fun x: expr Var => rank x <= n)))); [| solve_Countable; auto].
    apply (FBuild_injection _ _ (fun x => existT _ (rank x) (exist _ x (le_n _)))).
    hnf; intros.
    simpl in H.
    inversion H; auto.
Qed. (* 20 seconds *)

End PropositionalLanguage.

