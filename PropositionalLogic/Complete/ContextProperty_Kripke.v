Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.HenkinCompleteness.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Definition at_least_derivable_closed
           {L: Language}
           {Gamma: ProofTheory L}
           (P: context -> Prop): Prop :=
  forall Phi, P Phi -> derivable_closed Phi.

Definition at_least_consistent
           {L: Language}
           {Gamma: ProofTheory L}
           (P: context -> Prop): Prop :=
  forall Phi, P Phi -> consistent Phi.

Definition at_least_orp_witnessed
           {L: Language}
           {nL: NormalLanguage L}
           {pL: PropositionalLanguage L}
           {Gamma: ProofTheory L}
           (P: context -> Prop): Prop :=
  forall Phi, P Phi -> orp_witnessed Phi.

Definition Linderbaum_derivable
           {L: Language}
           {nL: NormalLanguage L}
           {Gamma: ProofTheory L}
           (P: context -> Prop): Prop :=
  forall Phi x, ~ Phi |-- x -> exists Psi: sig P, Included _ Phi (proj1_sig Psi) /\ ~ (proj1_sig Psi) |-- x.
