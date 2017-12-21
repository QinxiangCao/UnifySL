Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Kripke.

Local Open Scope logic_base.
Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section Lindenbaum_Kripke.

Context {L: Language}
        {Gamma: ProofTheory L}.

Hypothesis CE: Countable expr.

Lemma Lindenbaum_constructable_DS: forall P,
  
    Lindenbaum_constructable P derivable_closed.

End Lindenbaum_Kripke.
