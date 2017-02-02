Require Import Logic.GeneralLogic.Base.

Class BinderLanguage: Type := {
  type: Type;
  term: type -> Type;
  binded_L :> list type -> Language;
  binded_expr := fun ts => @expr (binded_L ts);
  expr_instantiate: forall (t: type) (ts: list type), binded_expr (t :: ts) -> term t -> binded_expr ts;
  lift: forall (t: type) (ts: list type), binded_expr ts -> binded_expr (t :: ts);
  lift_sound: forall (t: type) (ts: list type) (x: binded_expr ts) (e: term t), expr_instantiate t ts (lift t ts x) e = x
}.

Arguments binded_expr {_} _.
Arguments expr_instantiate {_} {_} {_} _ _.
Arguments lift {_} _ {_} _.

Class QuantifierLanguage (BL: BinderLanguage): Type := {
  allp: forall t ts, binded_expr (t :: ts) -> binded_expr ts;
  exp: forall t ts, binded_expr (t :: ts) -> binded_expr ts
}.

Arguments allp {_} {_} {_} {_} _.
Arguments exp {_} {_} {_} {_} _.

