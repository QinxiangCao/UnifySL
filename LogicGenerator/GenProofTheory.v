Require Import LogicGenerator.Utils.
Require LogicGenerator.Config.

Ltac print_theorem name :=
  idtac "Definition" name ":=" name ".".

Goal False.
  let minimum := eval cbv in Config.minimum in
  let propositional := eval cbv in Config.propositional in
  idtac "Require Import Logic.MinimunLogic.ProofTheory.Minimun.";
  idtac "Module LogicTheorem (L : LanguageSig) (Lg : LogicSig L) : LogicTheoremSig L Lg.";
  idtac "Module Insts := MakeInstances L Lg.";
  print_theorem provable_impp_refl;
  print_theorem provable_impp_arg_switch;
  idtac "End LogicTheorem.".
Abort.