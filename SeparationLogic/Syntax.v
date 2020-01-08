Require Import Logic.GeneralLogic.Base.

Class SepconLanguage (L: Language): Type := {
  sepcon : expr -> expr -> expr
}.

Class WandLanguage (L: Language): Type := {
  wand : expr -> expr -> expr
}.

Class EmpLanguage (L: Language): Type := {
  emp: expr
}.

Module SeparationLogicNotation.

Notation "x * y" := (sepcon x y) (at level 40, left associativity) : syntax.
Notation "x -* y" := (wand x y) (at level 55, right associativity) : syntax.

End SeparationLogicNotation.

Class IterSepconLanguage (L: Language): Type := {
  iter_sepcon : list expr -> expr
}.

Class IterWandLanguage (L: Language): Type := {
  iter_wand : list expr -> expr -> expr
}.

Class NormalIterSepcon
      (L: Language)
      {sepconL: SepconLanguage L}
      {empL: EmpLanguage L}
      {iter_sepcon_L: IterSepconLanguage L}: Prop := {
  iter_sepcon_def: forall xs, 
    iter_sepcon xs = fold_left sepcon xs emp
}.

Class NormalIterWand
      (L: Language)
      {wandL: WandLanguage L}
      {iter_wand_L: IterWandLanguage L}: Prop := {
  iter_wand_def: forall xs y,
    iter_wand xs y = fold_right wand y xs
}.

Definition Sepcon2IterSepcon
           {L: Language}
           {sepconL: SepconLanguage L}
           {empL: EmpLanguage L}: IterSepconLanguage L :=
  Build_IterSepconLanguage L (fun xs => fold_left sepcon xs emp).

Definition Wand2IterWand
           {L: Language}
           {wandL: WandLanguage L}: IterWandLanguage L :=
  Build_IterWandLanguage L (fun xs y => fold_right wand y xs).

Lemma Sepcon2IterSepcon_Normal
      {L: Language}
      {sepconL: SepconLanguage L}
      {empL: EmpLanguage L}:
  @NormalIterSepcon L _ _ Sepcon2IterSepcon.
Proof.
  intros.
  constructor.
  intros; reflexivity.
Qed.

Lemma Wand2IterWand_Normal
      {L: Language}
      {wandL: WandLanguage L}:
  @NormalIterWand L _ Wand2IterWand.
Proof.
  intros.
  constructor.
  intros; reflexivity.
Qed.



           


           
