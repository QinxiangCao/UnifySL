Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Normal.

Local Open Scope logic_base.
Local Open Scope syntax.

(* TODO: move or remove the following lemma. *)

Lemma union_derivable {L: Language} {minL: MinimunLanguage L} {Gamma: ProofTheory L} {AX: NormalAxiomatization L Gamma} {minAX: MinimunAxiomatization L Gamma}:
  forall (Phi1 Phi2: context) (x: expr),
    Union _ Phi1 Phi2 |-- x <->
    exists xs, Forall Phi2 xs /\ Phi1 |-- multi_imp xs x.
Proof.
  intros.
  split; intros.
  + rewrite derivable_provable in H.
    destruct H as [xs [? ?]].
    pose proof provable_multi_imp_split _ _ _ _ H H0.
    destruct H1 as [xs1 [xs2 [? [? ?]]]].
    exists xs2.
    split; auto.
    rewrite derivable_provable.
    exists xs1; auto.
  + destruct H as [xs2 [? ?]].
    rewrite derivable_provable in H0.
    destruct H0 as [xs1 [? ?]].
    unfold multi_imp in H1.
    rewrite <- fold_right_app in H1.
    fold (multi_imp (xs1 ++ xs2) x) in H1.
    rewrite derivable_provable.
    exists (xs1 ++ xs2).
    split; auto.
    rewrite Forall_app_iff; split;
    eapply Forall_impl; try eassumption.
    - intros; left; auto.
    - intros; right; auto.
Qed.






