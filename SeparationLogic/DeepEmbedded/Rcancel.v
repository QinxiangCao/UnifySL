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
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
Require Import Logic.SeparationLogic.DeepEmbedded.SolverBase.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

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


Section Solver.

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

(* Normal Form *)
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

Definition NormForm: Type := list (list (@expr L) * list (@expr L)) * list (@expr L) * list (@expr L).

Definition norm (x: @expr L): option NormForm :=
  match x with
  | SeparationEmpLanguage.impp y z =>
      let r := sepcon_flatten z in
      let l := map wand_flatten (sepcon_flatten y) in
      Some (filter_wand l, filter_sepcon l, r)
  | _ => None
  end.

Definition denorm (n: NormForm) : @expr L :=
  match n with
  | (ws, ss, r) =>
       SeparationEmpLanguage.impp
         (iter_sepcon (map (fun w => SeparationEmpLanguage.wand
                                        (iter_sepcon (fst w)) (iter_sepcon (snd w))) ws ++ ss))
         (iter_sepcon r)
  end.

(* Solver *)

(* Always try every single one *)
(* Other choices include: succeed if at least one succeed, like remove1
                          succeed if every one succeed, like remove1s *)
Definition general_cancel {A B: Type} (solver: A -> B -> option B): list A -> B -> option (list A * B) :=
  fix cancel xs y :=
    match xs with
    | nil => None
    | x :: xs0 =>
       match cancel xs0 y with
       | Some (xs0', y') =>
           match solver x y' with
           | Some y'' => Some (xs0', y'')
           | None => Some (x :: xs0', y')
           end
       | None =>
           match solver x y with
           | Some y' => Some (xs0, y')
           | None => None
           end
       end
    end.

Definition replace_sepcon (orig rm subs: list (@expr L)): option (list (@expr L)) :=
  match remove1s (SeparationEmpLanguage.expr_eqb Var_eqb) orig rm with
  | Some mid => Some (subs ++ mid)
  | None => None
  end.

Definition cancel_wand_nowand (left: list (@expr L) * list (@expr L)) (right: list (@expr L)): option (list (@expr L)) :=
  replace_sepcon right (snd left) (fst left).

Definition cancel_nowand_nowand (left: @expr L) (right: list (@expr L)): option (list (@expr L)) :=
  remove1 (SeparationEmpLanguage.expr_eqb Var_eqb left) right.

Definition solve_cancel1 (ws: list (list (@expr L) * list (@expr L))) (ss: list (@expr L)) (orig: list (@expr L)) :
  option NormForm :=
  match general_cancel cancel_wand_nowand ws orig with
  | Some (ws', orig') =>
    match general_cancel cancel_nowand_nowand ss orig' with
    | Some (ss', orig'') => Some ((ws', ss'), orig'')
    | None => Some ((ws', ss), orig')
    end
  | None =>
    match general_cancel cancel_nowand_nowand ss orig with
    | Some (ss', orig') => Some ((ws, ss'), orig')
    | None => None
    end
  end.

Fixpoint increamental_solver {A: Type} (solver: A -> option A) (fuel: nat) (a: A): A :=
  match fuel with
  | 0 => a
  | S fuel' =>
     match solver a with
     | Some a' => increamental_solver solver fuel' a'
     | None => a
     end
  end.

Definition cancel' (state: list (list (@expr L) * list (@expr L)) * list (@expr L) * list (@expr L)): (list (list (@expr L) * list (@expr L)) * list (@expr L) * list (@expr L)) :=
  increamental_solver (fun s => solve_cancel1 (fst (fst s)) (snd (fst s)) (snd s)) (length (fst (fst state)) + length (snd (fst state))) state.

Definition cancel (x: @expr L): @expr L :=
  match x with
  | SeparationEmpLanguage.impp y z =>
      let r := sepcon_flatten z in
      let zs := map wand_flatten (sepcon_flatten y) in
      let ws := filter_wand zs in
      let ss := filter_sepcon zs in
      let res := cancel' (ws, ss, r) in
      match res with
      | (ws, ss, r) =>
          SeparationEmpLanguage.impp
            (SeparationEmpLanguage.sepcon
               (iter_sepcon (map (fun w => SeparationEmpLanguage.wand
                                              (iter_sepcon (fst w)) (iter_sepcon (snd w))) ws))
               (iter_sepcon ss))
            (iter_sepcon r)
      end
  | _ => x
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

Lemma sepcon_flatten_sound': forall (default x: @expr L),
  |-- x <--> iter_sepcon' default (sepcon_flatten x).
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
  revert default x1 x2 xs1 xs2.
  generalize sL.
  generalize pL.
  generalize nL.
  generalize L.
  clear.
  intros L nL pL sL default x1 x2 xs1 xs2 G nG mpG ipG sG.
  intros.
  rewrite IHx1, IHx2.
  destruct H as [y1 [ys1 ?]].
  destruct H0 as [y2 [ys2 ?]].
  subst.
  apply sepcon_iter_sepcon'.
Qed.

Lemma wand_flatten'_sound: forall (x: @expr L),
  let wf := wand_flatten' x in
  |-- x <--> iter_wand (fst wf) (snd wf).
Proof.
  intros.
  subst wf.
  induction x; try apply (@Equivalence_Reflexive _ _ (@provable_iffp_equiv L nL pL G nG mpG ipG)).
  simpl iter_wand.
  destruct (wand_flatten' x2) as [l r].
  simpl fst in *; simpl snd in *.
  simpl iter_wand.
  apply (@wand_proper_iffp L nL pL sL G nG mpG ipG sG); auto.
  apply (@Equivalence_Reflexive _ _ (@provable_iffp_equiv L nL pL G nG mpG ipG)).
Qed.

Lemma wand_flatten_sound: forall (default x: @expr L),
  let wf := wand_flatten x in
  |-- x <--> iter_wand (fst wf) (iter_sepcon' default (snd wf)).
Proof.
  intros.
  subst wf.
  eapply (@Equivalence_Transitive _ _ (@provable_iffp_equiv L nL pL G nG mpG ipG)); [apply wand_flatten'_sound |].
Abort.

Lemma sepcon_flatten_sound: forall (x: @expr L),
  |-- x <--> iter_sepcon (sepcon_flatten x).
Proof.
  intros.
  apply sepcon_flatten_sound'.
Qed.

Lemma norm_sound: forall (x: @expr L) (n: NormForm),
  norm x = Some n ->
  |-- x <--> denorm n.
Proof.
  intros.
  destruct x; try solve [inversion H].
  simpl in H.
  inversion H; clear H; subst n.
  apply (@impp_proper_iffp L nL pL G nG mpG ipG).
  + pose proof sepcon_flatten_sound x1.
    eapply (@Equivalence_Transitive _ _ (@provable_iffp_equiv L nL pL G nG mpG ipG)); [exact H |].
    set (xs := sepcon_flatten x1).
    clearbody xs; clear x1 x2 H.
    eapply (@Equivalence_Transitive _ _ (@provable_iffp_equiv L nL pL G nG mpG ipG)).
Abort.

End Solver.

Section Test.

Require Import Logic.SeparationLogic.DeepEmbedded.Reify.

Context {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L} {P Q R: expr}.

Ltac cancel L x :=
  match reify_expr' L x (pair (@nil (@expr L)) 0) with
  | pair (pair ?tbl _) ?x0 =>
      let tbl' := tactic_rev tbl in
      assert (reflect L tbl' x0 = x); [try reflexivity |];
      pose (reflect L tbl' (cancel Nat.eqb x0))
  end.

Goal False.
cancel L (P * Q * (Q -* R) --> P * R).
simpl in e.
Abort.

End Test.
