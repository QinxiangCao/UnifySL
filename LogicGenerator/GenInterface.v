Require Import LogicGenerator.Utils.
Require LogicGenerator.Config.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.

Section Generate.
Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {minAX: MinimunAxiomatization L Gamma}.

Ltac print_theorem name :=
  match type of name with
  | ?type => idtac "Axiom" name ":" type "."
  end.

Goal False.
  let minimum := eval cbv in Config.minimum in
  let propositional := eval cbv in Config.propositional in

  idtac "Module Type LanguageSig.";
  idtac "Parameter Var : Type.";
  idtac "Parameter expr : Type.";
  when minimum ltac:(
    idtac "Parameter impp : expr -> expr -> expr.";
    idtac "Parameter varp : Var -> expr."
  );
  when propositional ltac:(
    idtac "Parameter andp : expr -> expr -> expr.";
    idtac "Parameter orp : expr -> expr -> expr.";
    idtac "Parameter negp : expr -> expr -> expr."
  );
  idtac "End LanguageSig.";

  idtac "Module Type LogicSig (L : LanguageSig).";
  idtac "Import L.";
  idtac "Parameter provable : expr -> Prop.";
  when minimum ltac:(
    idtac "Parameter modus_ponens : forall x y : expr, provable (impp x y) -> provable x -> provable y.";
    idtac "Parameter axiom1 : forall x y : expr, provable (impp x (impp y x)).";
    idtac "Parameter axiom2 : forall x y z : expr, provable (impp (impp x (impp y z)) (impp (impp x y) (impp x z)))."
  );
  idtac "End LogicSig.";

  idtac "Module Type LogicTheoremSig (L : LanguageSig) (Lg : LogicSig L).";
  idtac "Import L Lg.";
  when minimum ltac:(
    print_theorem provable_impp_refl;
    print_theorem provable_impp_arg_switch
  );
  idtac "End LogicTheoremSig.".
Abort.

End Generate.