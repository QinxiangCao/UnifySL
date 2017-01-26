Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimunLogic.ProofTheory.ContextProperty.
Require Import Logic.QuantifierLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.

Class QuantifierlLogic (BL: BinderLanguage) {nL: NormalLanguage _} {qL: QuantifierLanguage BL} (Gamma: ProofTheory _) {nGamma: NormalProofTheory _ Gamma} {mpGamma: MinimunPropositionalLogic _ Gamma} := {
  allp_elim: forall (t: type) (x: binded_expr (t :: nil)) (e: term t),
    |-- allp x --> expr_instantiate x e;
  allp_intros: forall (t: type) (x: expr) (y: binded_expr (t :: nil)) (e: term t),
    is_const y ->
    |-- x --> expr_instantiate y e ->
    |-- x --> allp y;
  exp_intros: forall (t: type) (x: binded_expr (t :: nil)) (e: term t),
    |-- expr_instantiate x e --> exp x;
  exp_elim: forall (t: type) (x: binded_expr (t :: nil)) (y: expr) (e: term t),
    is_const x ->
    |-- expr_instantiate x e --> y ->
    |-- exp x --> y
}.

