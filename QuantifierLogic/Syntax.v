Require Import Logic.GeneralLogic.Base.

Class BinderLanguage: Type := {
  type: Type;
  term: type -> Type;
  binded_expr: list type -> Type;
  expr_instantiate: forall (t0: type) (ts: list type), binded_expr (t0 :: ts) -> term t0 -> binded_expr ts
}.

Arguments binded_expr {_} _.
Arguments expr_instantiate {_} {_} {_} _ _.

Definition is_const {BL: BinderLanguage} {t: type} (x: binded_expr (t :: nil)): Prop :=
  forall e1 e2, expr_instantiate x e1 = expr_instantiate x e2.

Instance QuantifierLanguage2Language (BL: BinderLanguage): Language := Build_Language (binded_expr nil).

Class QuantifierLanguage (BL: BinderLanguage): Type := {
  allp: forall t, binded_expr (t :: nil) -> expr;
  exp: forall t, binded_expr (t :: nil) -> expr
}.

Arguments allp {_} {_} {_} _.
Arguments exp {_} {_} {_} _.

