Require Import Coq.Logic.ProofIrrelevance.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Omega.

Class SeparationLanguage (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L}: Type := {
  sepcon : expr -> expr -> expr;
  wand : expr -> expr -> expr
}.

Class UnitarySeparationLanguage (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L}: Type := {
  emp: expr
}.

Module SeparationLogicNotation.

Notation "x * y" := (sepcon x y) (at level 40, left associativity) : syntax.
Notation "x -* y" := (wand x y) (at level 55, right associativity) : syntax.

End SeparationLogicNotation.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Module SeparationLanguage.

Inductive expr {Var: Type}: Type :=
  | andp : expr -> expr -> expr
  | orp : expr -> expr -> expr
  | impp : expr -> expr -> expr
  | falsep : expr
  | sepcon : expr -> expr -> expr
  | wand : expr -> expr -> expr
  | varp : Var -> expr.

Implicit Arguments expr.

Instance L (Var: Type): Language :=
  Build_Language (expr Var).

Instance nL (Var: Type): NormalLanguage (L Var) :=
  Build_NormalLanguage (L Var) impp.

Instance pL (Var: Type): PropositionalLanguage (L Var) :=
  Build_PropositionalLanguage (L Var) (nL Var) andp orp falsep.

Instance sL (Var: Type): SeparationLanguage (L Var) :=
  Build_SeparationLanguage (L Var) (nL Var) (pL Var) sepcon wand.

End SeparationLanguage.

Module UnitarySeparationLanguage.

Inductive expr {Var: Type}: Type :=
  | andp : expr -> expr -> expr
  | orp : expr -> expr -> expr
  | impp : expr -> expr -> expr
  | sepcon : expr -> expr -> expr
  | wand : expr -> expr -> expr
  | emp : expr
  | falsep : expr
  | varp : Var -> expr.

Implicit Arguments expr.

Instance L (Var: Type): Language :=
  Build_Language (expr Var).

Instance nL (Var: Type): NormalLanguage (L Var) :=
  Build_NormalLanguage (L Var) impp.

Instance pL (Var: Type): PropositionalLanguage (L Var) :=
  Build_PropositionalLanguage (L Var) (nL Var) andp orp falsep.

Instance sL (Var: Type): SeparationLanguage (L Var) :=
  Build_SeparationLanguage (L Var) (nL Var) (pL Var) sepcon wand.

Instance usL (Var: Type): UnitarySeparationLanguage (L Var) :=
  Build_UnitarySeparationLanguage (L Var) (nL Var) (pL Var) (sL Var) emp.

Definition rank {Var: Type}: expr Var -> nat :=
  fix rank (x: expr Var): nat :=
    match x with
    | andp y z => 1 + rank y + rank z
    | orp y z => 1 + rank y + rank z
    | impp y z => 1 + rank y + rank z
    | sepcon y z => 1 + rank y + rank z
    | wand y z => 1 + rank y + rank z
    | emp => 0
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
               | inl (inr _) => exist (fun x: expr Var => rank x <= 0) emp (le_n 0)
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
      apply (@injection_Countable _ (s * s + s * s + s * s + s * s + s * s + unit + unit + Var)%type); [| solve_Countable].

      apply (Build_injection _ _ (fun x y =>
        match y with
        | inl (inl (inl (inl (inl (inl (inl (exist _ y _, exist _ z _))))))) => proj1_sig x = andp y z
        | inl (inl (inl (inl (inl (inl (inr (exist _ y _, exist _ z _))))))) => proj1_sig x = orp y z
        | inl (inl (inl (inl (inl (inr (exist _ y _, exist _ z _)))))) => proj1_sig x = impp y z
        | inl (inl (inl (inl (inr (exist _ y _, exist _ z _))))) => proj1_sig x = sepcon y z
        | inl (inl (inl (inr (exist _ y _, exist _ z _)))) => proj1_sig x = wand y z
        | inl (inl (inr _)) => proj1_sig x = emp
        | inl (inr _) => proj1_sig x = falsep
        | inr p => proj1_sig x = varp p
        end)).
      * hnf; intros.
        destruct a as [[y z | y z | y z | y z | y z | | | p] ?H].
        (* 1 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inl (inl (inl (inl (inl (exist _ y H0, exist _ z H1)))))))); auto.
        (* 2 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inl (inl (inl (inl (inr (exist _ y H0, exist _ z H1)))))))); auto.
        (* 3 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inl (inl (inl (inr (exist _ y H0, exist _ z H1))))))); auto.
        (* 4 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inl (inl (inr (exist _ y H0, exist _ z H1)))))); auto.
        (* 5 *) simpl in H. assert (rank y <= n) by omega. assert (rank z <= n) by omega.
                exists (inl (inl (inl (inr (exist _ y H0, exist _ z H1))))); auto.
        (* 6 *) exists (inl (inl (inr tt))); auto.
        (* 7 *) exists (inl (inr tt)); auto.
        (* 8 *) exists (inr p); auto.
      * hnf; intros.
        destruct a as [[y z | y z | y z | y z | y z | | | p] ?H];
        destruct b1 as [[[[[[[[[y1 ?H] [z1 ?H]] | [[y1 ?H] [z1 ?H]]] | [[y1 ?H] [z1 ?H]]] | [[y1 ?H] [z1 ?H]]] | [[y1 ?H] [z1 ?H]]] |] |] | p1]; try solve [inversion H];
        destruct b2 as [[[[[[[[[y2 ?H] [z2 ?H]] | [[y2 ?H] [z2 ?H]]] | [[y2 ?H] [z2 ?H]]] | [[y2 ?H] [z2 ?H]]] | [[y2 ?H] [z2 ?H]]] |] |] | p2]; try solve [inversion H0].
        (* 1 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 2 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 3 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 4 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 5 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 6 *) destruct u, u0; auto.
        (* 7 *) destruct u, u0; auto.
        (* 8 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
      * hnf; intros.
        destruct b as [[[[[[[[[y ?H] [z ?H]] | [[y ?H] [z ?H]]] | [[y ?H] [z ?H]]] | [[y ?H] [z ?H]]] | [[y ?H] [z ?H]]] |] |] | p];
        destruct a1 as [[y1 z1 | y1 z1 | y1 z1 | y1 z1 | y1 z1 | | | p1] ?H]; try solve [inversion H];
        destruct a2 as [[y2 z2 | y2 z2 | y2 z2 | y2 z2 | y2 z2 | | | p2] ?H]; try solve [inversion H0].
        (* 1 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 2 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 3 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 4 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 5 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
        (* 6 *) f_equal; apply proof_irrelevance.
        (* 7 *) f_equal; apply proof_irrelevance.
        (* 8 *) inversion H; inversion H0; subst; subst; repeat f_equal; apply proof_irrelevance.
  + apply (@injection_Countable _ (sigT (fun n => sig (fun x: expr Var => rank x <= n)))); [| solve_Countable; auto].
    apply (FBuild_injection _ _ (fun x0 => existT (fun n => sig (fun x => rank x <= n)) (rank x0) (exist (fun x => rank x <= rank x0) x0 (le_n (rank x0))))).
    hnf; intros.
    simpl in H.
    inversion H; auto.
Qed. (* 9 seconds *)

End UnitarySeparationLanguage.

