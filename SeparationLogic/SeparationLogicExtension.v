Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.MinimunLogic.LogicBase.
Require Import Logic.MinimunLogic.MinimunLogic.
Require Import Logic.MinimunLogic.ContextProperty.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.IntuitionisticPropositionalLogic.
Require Import Logic.PropositionalLogic.GodelDummettLogic.
Require Import Logic.PropositionalLogic.ClassicalPropositionalLogic.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.SeparationLogic.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Class SeparationLogic_Precise (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {SL: SeparationLogic L Gamma}:= {
  precise: expr -> Prop;
  precise_sepcon: forall x y, precise x -> precise y -> precise (x * y);
  precise_impp: forall x y, |-- x --> y -> precise y -> precise x;
  sepcon_cancel: forall x y z, |-- (x * z) --> (y * z) -> precise z -> |-- (x --> y)
}.

Class SeparationLogic_PureFact (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {SL: SeparationLogic L Gamma}:= {
  pure_fact: expr -> Prop;
  pure_falsep: pure_fact FF;
  pure_andp: forall x y, pure_fact x -> pure_fact y -> pure_fact (x && y);
  pure_orp: forall x y, pure_fact x -> pure_fact y -> pure_fact (x || y);
  pure_impp: forall x y, pure_fact x -> pure_fact y -> pure_fact (x --> y);
  pure_specon: forall x y, pure_fact x -> pure_fact y -> pure_fact (x * y);
  pure_wand: forall x y, pure_fact x -> pure_fact y -> pure_fact (x -* y);
  andp_sepcon: forall x y z, pure_fact x -> |-- (x && (y * z)) <--> ((x && y) * z)
}.

