Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.PropositionalLogic.KripkeModel.

Instance PredLanguage (A: Type) {R: Relation A} : Language := Build_Language (MonoEnsemble A).

Instance PredProofTheory (A: Type) {R: Relation A}: ProofTheory (PredLanguage A) := Build_ProofTheory (PredLanguage A) (fun x => forall a, proj1_sig x a) (fun Phi x => forall a, (forall y, Phi y -> proj1_sig y a) -> proj1_sig x a).

Instance PredSemantics (A: Type) {R: Relation A}: Semantics (PredLanguage A) (Build_Model A) := Build_Semantics (PredLanguage A) (Build_Model A) (fun x => proj1_sig x).
