Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.List_Func_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.

Class AdjointProofTheory (L: Language) {minL: MinimunLanguage L} (Gamma: ProofTheory L) (prodp funcp: expr -> expr -> expr) := {
  adjoint: forall x y z, |-- prodp x y --> z <-> |-- x --> (funcp y z);
  assoc1: forall x y z, |-- prodp x (prodp y z) --> prodp (prodp x y) z;
  prodp_mono: forall x1 y1 x2 y2, |-- x1 --> x2 -> |-- y1 --> y2 -> |-- prodp x1 y1 --> prodp x2 y2;
  assoc2: forall x y z, |-- prodp (prodp x y) z --> prodp x (prodp y z)
}.

Definition iter_funcp {L: Language} (funcp: expr -> expr -> expr) (xs: list expr) (y: expr) :=
  fold_right funcp y xs.

Definition iter_prodp {L: Language} (default: expr) (prodp: expr -> expr -> expr) (xs: list expr) :=
  semi_group_fold default prodp xs.

Lemma adjoint_iter {L: Language} {minL: MinimunLanguage L} {Gamma: ProofTheory L} {prodp funcp: expr -> expr -> expr} {adjGamma: AdjointProofTheory L Gamma prodp funcp}:
  forall default x xs y,
    |-- iter_prodp default prodp (x :: xs) --> y <-> |-- x --> (iter_funcp funcp xs y).
Proof.
  intros.
  revert x; induction xs; intros; simpl in *.
  + reflexivity.
  + rewrite <- adjoint.
    apply IHxs.
Qed.


