Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.WeakClassical.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.MultiSepcon.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

(*
Lemma cancel_sound {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}:
  forall x1 x2 y1 y2 f,
    |-- x1 <--> x2 ->
    |-- y1 <--> y2 ->
    |-- x1 * y1 <--> f x1 * f y1.
Proof.
  intros.
  rewrite H at 1.
, H0.
*)

Lemma cancel_sound {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} (Gamma: ProofTheory L) {nGamma: NormalProofTheory L Gamma} {mpGamma: MinimunPropositionalLogic L Gamma} {ipGamma: IntuitionisticPropositionalLogic L Gamma} {sGamma: SeparationLogic L Gamma}:
  forall x1 x2 y1 y2 f1 f2,
    |-- x1 --> y1 * f1 ->
    |-- f1 --> f2 ->
    |-- y2 * f2 --> x2 ->
    |-- y1 --> y2 ->
    |-- x1 --> x2.
Proof.
  intros.
  rewrite H, <- H1.
  apply sepcon_mono; auto.
Qed.


Section DeepEmbedded.

Require Import Logic.SeparationLogic.DeepEmbedded.Parameter.
Require Logic.SeparationLogic.DeepEmbedded.SeparationEmpLanguage.
Require Logic.SeparationLogic.DeepEmbedded.ParametricSeparationLogic.

Context {Var: Type} {PAR: SL_Parameter} (Var_eqb: Var -> Var -> bool).

Instance L: Language := SeparationEmpLanguage.L Var.
Instance nL: NormalLanguage L := SeparationEmpLanguage.nL Var.
Instance pL: PropositionalLanguage L := SeparationEmpLanguage.pL Var.
Instance sL: SeparationLanguage L := SeparationEmpLanguage.sL Var.
Instance s'L: SeparationEmpLanguage L := SeparationEmpLanguage.s'L Var.
Instance G: ProofTheory L := ParametricSeparationLogic.G Var PAR.
Instance nG: NormalProofTheory L G := ParametricSeparationLogic.nG Var PAR.
Instance mpG: MinimunPropositionalLogic L G := ParametricSeparationLogic.mpG Var PAR.
Instance ipG: IntuitionisticPropositionalLogic L G := ParametricSeparationLogic.ipG Var PAR.
Instance sG: SeparationLogic L G := ParametricSeparationLogic.sG Var PAR.

(* Solver *)
Fixpoint sepcon_flatten (x: @expr L): list (@expr L) :=
  match x with
  | SeparationEmpLanguage.sepcon y z => sepcon_flatten y ++ sepcon_flatten z
  | _ => x :: nil
  end.

Fixpoint wand_flatten' (x: @expr L): list (@expr L) * @expr L :=
  match x with
  | SeparationEmpLanguage.wand y z =>
      match wand_flatten' z with
      | (ys, z') => (y :: ys, z')
      end
  | _ => (nil, x)
  end.

Definition wand_flatten (x: @expr L): list (@expr L) * list (@expr L) :=
  match wand_flatten' x with
  | (ys, y) => (concat (map sepcon_flatten ys), sepcon_flatten y)
  end.

Definition filter_wand (ws: list (list (@expr L) * list (@expr L))): list (list (@expr L) * list (@expr L)) :=
  filter (fun w => match fst w with nil => false | _ => true end) ws.

Definition filter_sepcon (ws: list (list (@expr L) * list (@expr L))): list (@expr L) :=
  concat (map snd (filter (fun w => match fst w with nil => true | _ => false end) ws)).

Definition remove1 {A: Type} (test: A -> bool): list A -> option (list A) :=
  fix remove1 xs :=
    match xs with
    | nil => None
    | x :: xs0 => if test x then Some xs0 else
       match remove1 xs0 with
       | Some xs0' => Some (x :: xs0')
       | None => None
       end
    end.

Definition remove1s {A: Type} (eqb: A -> A -> bool) (orig: list A): list A -> option (list A) :=
  fold_right
    (fun a Orig =>
       match Orig with
       | Some orig => remove1 (eqb a) orig
       | None => None
       end) (Some orig).

Definition replace_sepcon (orig rm subs: list (@expr L)): option (list (@expr L)) :=
  match remove1s (SeparationEmpLanguage.expr_eqb Var_eqb) orig rm with
  | Some mid => Some (subs ++ mid)
  | None => None
  end.

(* Soundness *)

Lemma sepcon_flatten_not_nil: forall (x: @expr L),
  exists x0 xs, sepcon_flatten x = x0 :: xs.
Proof.
  intros.
  induction x; try (eexists; exists nil; reflexivity).
  destruct IHx1 as [y1 [ys1 ?]].
  destruct IHx2 as [y2 [ys2 ?]].
  exists y1, (ys1 ++ y2 :: ys2).
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma sepcon_flatten_multi_sepcon: forall (x: @expr L),
  |-- x <--> multi_sepcon' FF (sepcon_flatten x).
Proof.
  intros.
  induction x; try (destruct provable_iffp_equiv as [HH _ _]; apply HH).
  change (SeparationEmpLanguage.sepcon x1 x2) with (x1 * x2).
  simpl sepcon_flatten.
  pose proof sepcon_flatten_not_nil x1.
  pose proof sepcon_flatten_not_nil x2.
  set (xs1 := sepcon_flatten x1) in IHx1, H |- *.
  set (xs2 := sepcon_flatten x2) in IHx2, H0 |- *.
  change (SeparationEmpLanguage.expr Var) with (@expr L) in *.
  clearbody xs1 xs2.
  revert IHx1 IHx2 H H0.
  specialize sG.
  generalize ipG.
  generalize mpG.
  generalize nG.
  generalize G.
  revert x1 x2 xs1 xs2.
  generalize sL.
  generalize pL.
  generalize nL.
  generalize L.
  clear.
  intros L nL pL sL x1 x2 xs1 xs2 G nG mpG ipG sG.
  intros.
  rewrite IHx1, IHx2.
  destruct H as [y1 [ys1 ?]].
  destruct H0 as [y2 [ys2 ?]].
  subst.
  apply sepcon_multi_sepcon'.
Qed.

End DeepEmbedded.