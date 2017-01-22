Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Logic.SeparationLogic.DeepEmbedded.SeparationEmpLanguage.
(*
Require Import Logic.SeparationLogic.DeepEmbedded.Parameter.
Require Import Logic.SeparationLogic.DeepEmbedded.ParametricSeparationLogic.
*)

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Definition reflect (L: Language) {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L} (tbl: list expr): @SeparationEmpLanguage.expr nat -> expr :=
  fix reflect (x: @SeparationEmpLanguage.expr nat): expr :=
    match x with
    | SeparationEmpLanguage.andp y z => andp (reflect y) (reflect z)
    | SeparationEmpLanguage.orp y z => orp (reflect y) (reflect z)
    | SeparationEmpLanguage.impp y z => impp (reflect y) (reflect z)
    | SeparationEmpLanguage.sepcon y z => sepcon (reflect y) (reflect z)
    | SeparationEmpLanguage.wand y z => wand (reflect y) (reflect z)
    | SeparationEmpLanguage.emp => emp
    | SeparationEmpLanguage.falsep => falsep
    | SeparationEmpLanguage.varp n => nth n tbl TT
    end.

Ltac search_expr' x l l0 :=
  match l with
  | pair (cons x ?l_l) (S ?l_len) =>
      constr:(pair l0 l_len)
  | pair (cons ?y ?l_l) (S ?l_len) =>
      search_expr' x (pair l_l l_len) l0
  | pair nil 0 =>
      match l0 with
      | pair ?l0_l ?l0_len => constr:(pair (pair (cons x l0_l) (S l0_len)) l0_len)
      end
  end.

Ltac search_expr x l := search_expr' x l l.

Ltac reify_expr' L x l :=
  match x with
  | @impp L _ ?y ?z =>
      match reify_expr' L y l with
      | pair ?l' ?y0 =>
      match reify_expr' L z l' with
      | pair ?l'' ?z0 =>
          constr:(pair l'' (@SeparationEmpLanguage.impp nat y0 z0))
      end end
  | _ =>
      match search_expr x l with
      | pair ?l' ?n =>
          constr:(pair l' (@SeparationEmpLanguage.varp nat n))
      end
  end.

Ltac reify_expr L x :=
  match reify_expr' L x (pair (@nil (@expr L)) 0) with
  | pair (pair ?tbl _) ?x0 =>
      assert (reflect L (rev tbl) x0 = x); [try reflexivity |]
  end.

Section Test.

Context {L: Language} {nL: NormalLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {s'L: SeparationEmpLanguage L}.
Goal False.
reify_expr L (FF --> TT).
reify_expr L (TT --> (FF --> TT)).
Abort.

End Test.