Require Import Logic.lib.SublistT.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class BinderLanguage: Type := {
(* parameter *)
  type: Type;
  binded_term: list type -> type -> Type;
  ins_term: forall (t0 t: type) (ts: list type), binded_term (t :: ts) t0 -> binded_term ts t-> binded_term ts t0;
  var_term: forall (t: type) (ts: list type), binded_term (t :: ts) t;
  lift_term: forall (t: type) (ts1 ts2: list type) (g: sublistT ts1 ts2), binded_term ts1 t -> binded_term ts2 t;
  binded_L :> list type -> Language;
  binded_expr := fun ts => @expr (binded_L ts);
  ins_expr: forall (t: type) (ts: list type), binded_expr (t :: ts) -> binded_term ts t -> binded_expr ts;
  lift_expr: forall (ts1 ts2: list type) (g: sublistT ts1 ts2), binded_expr ts1 -> binded_expr ts2;
(* soundness *)

  lift_term_nil_nil:
    forall t (e: binded_term nil t),
      lift_term t nil nil sublistT_nil_nil e = e;
  lift_term_cons:
    forall t t0 ts1 ts2 (g: sublistT ts1 ts2) (e: binded_term ts1 t) (e0: binded_term ts2 t0),
      ins_term _ _ _ (lift_term t _ _ (sublistT_cons t0 g) e) e0 = lift_term t _ _ g e;
  lift_term_cons_cons:
    forall t t0 ts1 ts2 (g: sublistT ts1 ts2) (e: binded_term (t0 :: ts1) t) (e0: binded_term ts1 t0),
      ins_term _ _ _ (lift_term t _ _ (sublistT_cons_cons t0 g) e) (lift_term t0 _ _ g e0) =
      lift_term t _ _ g (ins_term _ _ _ e e0);
  lift_expr_nil_nil:
    forall (x: binded_expr nil),
      lift_expr nil nil sublistT_nil_nil x = x;
  lift_expr_cons:
    forall t0 ts1 ts2 (g: sublistT ts1 ts2) (x: binded_expr ts1) (e: binded_term ts2 t0),
      ins_expr _ _ (lift_expr _ _ (sublistT_cons t0 g) x) e = lift_expr _ _ g x;
  lift_expr_cons_cons:
    forall t0 ts1 ts2 (g: sublistT ts1 ts2) (x: binded_expr (t0 :: ts1)) (e: binded_term ts1 t0),
      ins_expr _ _ (lift_expr _ _ (sublistT_cons_cons t0 g) x) (lift_term t0 _ _ g e) =
      lift_expr _ _ g (ins_expr _ _ x e)
}.

Arguments binded_term {_} _ _.
Arguments ins_term {_} {_} {_} {_} _ _.
Arguments var_term {_} {_} {_}.
Arguments lift_term {_} {_} {_} {_} _ _.
Arguments binded_expr {_} _.
Arguments ins_expr {_} {_} {_} _ _.
Arguments lift_expr {_} {_} {_} _ _.

Class QuantifierLanguage (BL: BinderLanguage): Type := {
  allp: forall t ts, binded_expr (t :: ts) -> binded_expr ts;
  exp: forall t ts, binded_expr (t :: ts) -> binded_expr ts;
  lift_allp: forall t ts1 ts2 (g: sublistT ts1 ts2) (x: binded_expr (t :: ts1)), lift_expr g (allp t ts1 x) = allp t ts2 (lift_expr (sublistT_cons_cons t g) x);
  lift_exp: forall t ts1 ts2 (g: sublistT ts1 ts2) (x: binded_expr (t :: ts1)), lift_expr g (exp t ts1 x) = exp t ts2 (lift_expr (sublistT_cons_cons t g) x)
}.

Arguments allp {_} {_} {_} {_} _.
Arguments exp {_} {_} {_} {_} _.

Class NormalBinderLanguage (BL: BinderLanguage): Type := {
  binded_nL:> forall ts, NormalLanguage (binded_L ts);
  lift_impp:
    forall ts1 ts2 (g: sublistT ts1 ts2) (x y: binded_expr ts1),
      lift_expr g (x --> y) = lift_expr g x --> lift_expr g y
}.

Class PropositionalBinderLanguage (BL: BinderLanguage) {nBL: NormalBinderLanguage BL}: Type := {
  binded_pL:> forall ts, PropositionalLanguage (binded_L ts);
  lift_andp:
    forall ts1 ts2 (g: sublistT ts1 ts2) (x y: binded_expr ts1),
      lift_expr g (x && y) = lift_expr g x && lift_expr g y;
  lift_orp:
    forall ts1 ts2 (g: sublistT ts1 ts2) (x y: binded_expr ts1),
      lift_expr g (x || y) = lift_expr g x || lift_expr g y
}.