Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.

Class PropositionalStable (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} (Gamma: ProofTheory L) (stable: expr -> Prop) := {
  impp_stable: forall x y, stable x -> stable y -> stable (x --> y);
  andp_stable: forall x y, stable x -> stable y -> stable (x && y);
  orp_stable: forall x y, stable x -> stable y -> stable (x || y);
  falsep_Stable: stable FF
}.

Class ModalStable (L: Language) {nL: NormalLanguage L} {mL: ModalLanguage L} (Gamma: ProofTheory L) (stable: expr -> Prop) := {
  boxp_stable: forall x, stable x -> stable (boxp x)
}.

Class ModalAborbStable (L: Language) {nL: NormalLanguage L} {mL: ModalLanguage L} (Gamma: ProofTheory L) (stable: expr -> Prop) := {
  boxp_absorb_stable: forall x, stable x -> |-- x --> boxp x
}.
