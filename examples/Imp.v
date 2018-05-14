(* The language and semantics in this file is mainly copied from software foundation. Benjamin C. Pierce, Arthur Azevedo de Amorim, Chris Casinghino, Marco Gaboardi, Michael Greenberg, Catalin Hritcu, Vilhelm Sjöberg, and Brent Yorgey. http://www.cis.upenn.edu/ bcpierce/sf. *)

Require Import Coq.ZArith.ZArith.

Section Imp.

Context {Var: Type}.

Definition state := Var -> Z.

Definition update (st : state) (x : Var) (n : Z) (st': state): Prop :=
  st' x = n /\
  (forall x0, x0 <> x -> st x0 = st' x0).

Inductive aexp : Type :=
  | AVar : Var -> aexp
  | ANum : Z -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (st : state) (a : aexp) : Z :=
  match a with
  | AVar x => st x
  | ANum n => n
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => Zeq_bool (aeval st a1) (aeval st a2)
  | BLe a1 a2   => Zle_bool (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Inductive cmd : Type :=
  | CSkip : cmd
  | CAss : Var -> aexp -> cmd
  | CSeq : cmd -> cmd -> cmd
  | CIf : bexp -> cmd -> cmd -> cmd
  | CWhile : bexp -> cmd -> cmd.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Reserved Notation " t '/' st '==>' t' '/' st' " 
                  (at level 40, st at level 39, t' at level 39).

Inductive cstep : (cmd * state) -> (cmd * state) -> Prop :=
  | CS_Ass : forall st st' i n a,
      aeval st a = n ->
      update st i n st' ->
      (i ::= a) / st ==> SKIP / st'
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ==> c1' / st' ->
      (c1 ;; c2) / st ==> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ==> c2 / st
  | CS_IfTrue : forall st b c1 c2,
      beval st b = true ->
      IFB b THEN c1 ELSE c2 FI / st ==> c1 / st
  | CS_IfFalse : forall st b c1 c2,
      beval st b = false ->
      IFB b THEN c1 ELSE c2 FI / st ==> c2 / st
  | CS_WhileTrue : forall st b c1,
      beval st b = true ->
      (WHILE b DO c1 END) / st ==> (c1;; (WHILE b DO c1 END)) / st
  | CS_WhileFalse : forall st b c1,
      beval st b = false ->
      (WHILE b DO c1 END) / st ==> SKIP / st

  where " t '/' st '==>' t' '/' st' " := (cstep (t,st) (t',st')).

Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.SmallStepSemantics.

Instance cexp_bare: ProgrammingLanguage:= {
  cmd := Imp.cmd;
  normal_form := fun c => match c with
                       | CSkip => True
                       | _ => False
                       end;
}.

Instance cexp_imp: ImperativeProgrammingLanguage _ := {
  bool_expr := bexp;
}.
Proof.
  + apply CSeq.
  + apply CIf.
  + apply CWhile.
  + apply CSkip.
Defined.

Inductive cmd_frame : Type :=
| seq_frame : cmd -> cmd_frame
| while_frame : bexp -> cmd -> cmd_frame
.

Instance cexp_cs_bare : ControlStack:= {
  stack := list cmd_frame;
  frame := cmd_frame;
  empty_stack := nil;
}.

Require Import List.

Instance cexp_cs : LinearControlStack cexp_cs_bare := {}.
Proof.
  apply cons.
Defined.

Definition depth := nat.

Fixpoint cexp_restore (c : cmd) (s : list cmd_frame) : cmd * depth :=
  match s with
  | nil => (c, 0)
  | (seq_frame c' :: s') => let (c0, d) := cexp_restore (c ;; c') s' in (c0, S d)
  | (while_frame b c' :: s') => let (c0, d) := cexp_restore (c ;; WHILE b DO c' END) s' in (c0, S d)
  end.

Instance cexp_cont_bare : Continuation cexp_bare cexp_cs_bare := {
  cont := cmd * depth;
}.
Proof.
  + apply (fun c s => cexp_restore c s).
  + apply (fun c s => cexp_restore c s).
Defined.

Instance cexp_cont : ImperativeProgrammingLanguageContinuation cexp_cont_bare := {}.
Proof.
  + apply seq_frame.
  + apply while_frame.
Defined.

Inductive cstep_cont : (cmd * depth) * state -> (cmd * depth) * state -> Prop :=
| cstep_lift: forall c1 c2 s1 s2 n, cstep (c1, s1) (c2, s2) -> cstep_cont ((c1, n), s1) ((c2, n), s2).

(*
Inductive cexp_zerostep: (cmd * depth) -> (cmd * depth) -> Prop :=
| cexp_zerostep_skip_restore: forall c s, c = cexp_restore SKIP s -> cexp_zerostep (c, evaluating) (c, returning)
| cexp_zerostep_seq_seq: forall c1 c2 s, cexp_zerostep (c1 ;; c2, evaluating) (c1
.

Instance cexp_sss : SmallStepSemantics cexp_cont_bare state := {
  step := lift_step_zero (lift_step_term cstep_cont) cexp_zerostep;
}.

Require Import Coq.Sets.Ensembles.

Instance state_rel : KripkeModel.KI.Relation state := {}.
Proof.
  unfold Ensemble.
  intros b1 b2.
  apply (b1 = b2).
Defined.

(*
Lemma cexp_restore_to_seq: 
  forall c c' cs', exists c1 c2, cexp_restore c (c' :: cs') = (c1 ;; c2).
Proof.
  intros c c' cs'.
  generalize dependent c'.
  generalize dependent c.
  induction cs'.
  - intros.
    exists c.
    destruct c'.
    + exists c0. reflexivity.
    + exists (WHILE b DO c0 END). reflexivity.
  - intros.
    destruct cs'.
    + destruct c'.
      * exists (c ;; c0).
        destruct a.
        exists c1.
        reflexivity.
        exists (WHILE b DO c1 END).
        reflexivity.
      * exists (c ;; WHILE b DO c0 END).
        destruct a.
        exists c1.
        reflexivity.
        exists (WHILE b0 DO c1 END).
        reflexivity.
    + destruct c';
        [ destruct (IHcs' (c ;; c1) a) as [x1 [x2 IH]] 
        | destruct (IHcs' (c ;; WHILE b DO c1 END) a) as [x1 [x2 IH]]];
        exists x1; exists x2;
          apply IH.
Qed. 
*)

Instance cexp_isss : Total.ImpSmallStepSemantics cexp_sss := {}.
Proof.
  - intros s bexp.
    apply (Bool.Is_true (beval s bexp)).
  - intros.
    unfold KripkeModel.Krelation_stable_Kdenote.
    unfold KripkeModel.KI.Krelation.
    intros.
    unfold state_rel in H. subst.
    apply iff_refl.
  - intros.
    simpl in H.
    destruct c; inversion H; clear H.
    simpl in H0.
    inversion H0; subst; clear H0.
    + simpl.
      inversion H3; subst; clear H3.
      reflexivity.
    + inversion H3; subst; clear H3.
      * exfalso.
        apply H5.
        exists (cexp_restore SKIP cs, returning).
        eapply cexp_zerostep_skip_restore with (s := cs).
        reflexivity.
      * inversion H.
  - intros.
    inversion H; subst; clear H.
    + inversion H3; subst; clear H3.
      Admitted.

*)