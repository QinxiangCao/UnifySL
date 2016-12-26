Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Stream.SigStream.

Definition fin_stream {A: Type} (h: list A) : stream A.
  exists (fun n => nth_error h n).
  intros.
  rewrite nth_error_None_iff in H0 |- *.
  omega.
Defined.

Definition inf_stream {A: Type} (h: nat -> A) : stream A.
  exists (fun n => Some (h n)).
  intros.
  congruence.
Defined.

Definition empty_stream {A: Type}: stream A := fin_stream nil.

Definition partial_stream_len {A: Type} (h: stream A) (n: nat): option nat :=
  match h n with
  | Some _ => None
  | None => Some
    ((fix f (m: nat): nat :=
       match h m with
       | Some _ => S m
       | None => match m with
                 | 0 => 0
                 | S m0 => f m0
                 end
       end) n)
  end.

Lemma partial_stream_len_mono1: forall {A: Type} (h: stream A) (x y: nat), x <= y -> partial_stream_len h y = None -> partial_stream_len h x = None.
Proof.
  intros.
  unfold partial_stream_len in *.
  destruct (h y) eqn:?H; try congruence.
  pose proof (stream_sound2 h x y H) as [? ?]; [eauto |].
  rewrite H2; auto.
Qed.

Lemma partial_stream_len_mono2: forall {A: Type} (h: stream A) (x y n: nat), x <= y -> partial_stream_len h x = Some n -> partial_stream_len h y = Some n.
Proof.
  intros.
  unfold partial_stream_len in *.
  destruct (h x) eqn:?H; try congruence.
  pose proof (stream_sound1 h x y H H1).
  inversion H0.
  rewrite H2, H4; clear H0.
  f_equal.
  revert n H4; induction H; intros; auto.
  pose proof (stream_sound1 h x m H H1).
  specialize (IHle H0 _ H4).
  rewrite IHle; clear IHle.
  rewrite H2; auto.
Qed.

Program Definition stream_app {A: Type} (h1 h2: stream A): stream A :=
  fun n: nat =>
    match partial_stream_len h1 n return option A with
    | None => h1 n
    | Some m => h2 (n - m)
    end.
Next Obligation.
  destruct (partial_stream_len h1 x) eqn:?H.
  + pose proof H1.
    apply (partial_stream_len_mono2 h1 x y n) in H1; [| omega].
    rewrite H1.
    apply (stream_sound1 h2 (x - n) (y - n)); auto.
    omega.
  + unfold partial_stream_len in H1.
    rewrite H0 in H1.
    congruence.
Qed.

Fixpoint partial_stream_clen {A: Type} (h: nat -> stream A) (n: nat): nat * nat :=
  match n with
  | 0 => (0, 0)
  | S n => let (k, m) := partial_stream_clen h n in
           match h k (S m) with
           | Some _ => (k, S m)
           | None => (S k, 0)
           end
  end.

Fixpoint partial_stream_clen' {A: Type} (h: nat -> stream A) (n: nat): option (nat * nat) :=
  let (k, m) := partial_stream_clen h n in
  match n with
  | 0 => match h k m with
         | Some _ => Some (k, m)
         | None => None
         end
  | S n => match h k m, partial_stream_clen' h n with
           | Some _, Some _ => Some (k, m)
           | _, _ => None
           end
  end.

Program Definition stream_capp {A: Type} (h: nat -> stream A): stream A :=
  fun n: nat =>
    match partial_stream_clen' h n return option A with
    | Some (k, m) => h k m
    | None => None
    end.
Next Obligation.
Admitted.

