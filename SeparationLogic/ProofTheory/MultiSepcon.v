Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.WeakClassical.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Definition multi_sepcon' {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} (default: expr) (xs: list expr) : expr :=
  match xs with
  | nil => default
  | x :: xs0 => fold_left sepcon xs0 x
  end.

Definition  multi_sepcon {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L} (xs: list expr) : expr := multi_sepcon' emp xs.

Lemma sepcon_multi_sepcon' {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}:
  forall (default: expr) x xs y ys,
    |-- multi_sepcon' default (x :: xs) * multi_sepcon' default (y :: ys) <-->
        multi_sepcon' default ((x :: xs) ++ (y :: ys)).
Proof.
  intros.
  revert x; induction xs; intros.
  + simpl.
    revert y; induction ys; intros.
    - simpl.
      apply provable_iffp_refl.
    - specialize (IHys (y * a)).
      simpl in *.
      rewrite IHys; clear IHys.
      pose proof sepcon_assoc x y a.
      set (x' := x * (y * a)) in H |- *.
      set (y' := x * y * a) in H |- *.
      clearbody x' y'; clear x y a.
      revert x' y' H; induction ys; intros.
      * auto.
      * simpl.
        apply IHys.
        rewrite H; apply provable_iffp_refl.
  + specialize (IHxs (x * a)).
    auto.
Qed.

Lemma sepcon_multi_sepcon {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L} {Gamma: ProofTheory L} {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma} {EmpGamma: EmpSeparationLogic L Gamma}:
  forall xs ys,
    |-- multi_sepcon xs * multi_sepcon ys <--> multi_sepcon (xs ++ ys).
Proof.
  intros.
  destruct xs as [| x xs], ys as [| y ys].
  + simpl.
    apply sepcon_emp.
  + simpl.
    rewrite provable_sepcon_comm_iffp.
    apply sepcon_emp.
  + simpl.
    rewrite app_nil_r.
    apply sepcon_emp.
  + apply sepcon_multi_sepcon'.
Qed.