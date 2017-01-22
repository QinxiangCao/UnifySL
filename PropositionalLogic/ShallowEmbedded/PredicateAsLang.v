Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.omega.Omega.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.

Instance PredLanguage (A: Type) : Language := Build_Language (A -> Prop).

Instance PredProofTheory (A: Type): ProofTheory (PredLanguage A) := Build_ProofTheory (PredLanguage A) (fun x => forall a, x a) (fun Phi x => forall a, (forall y, Phi y -> y a) -> x a).

Instance PredSemantics (A: Type): Semantics (PredLanguage A) (Build_Model A) := Build_Semantics (PredLanguage A) (Build_Model A) (fun x => x).
