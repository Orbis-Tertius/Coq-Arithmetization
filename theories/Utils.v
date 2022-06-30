From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrnat seq fintype tuple.

Definition drop_index {T} (m : nat) (s : seq T) : seq T := 
  take m s ++ behead (drop m s).

Theorem drop_index_length {T} : forall (s : seq T) (m : nat),
  m < length s -> length (drop_index m s) = length s - 1.
Proof.
  elim;[auto|].
  unfold drop_index.
  simpl; move=> a l IH [|m] mlt;[sauto|].
  simpl; rewrite IH; auto.
  destruct (length l);[fcrush|sauto q: on].
Qed.

Theorem drop_index_length_high {T} : forall (s : seq T) (m : nat),
  length s <= m -> length (drop_index m s) = length s.
Proof.
  elim;[auto|].
  unfold drop_index.
  simpl; move=> a l IH [|m] mlt;[fcrush|].
  simpl; by rewrite IH.
Qed.

Theorem drop_index_head {T} (t : T) (s : seq T) : 
  drop_index 0 (t :: s) = s.
Proof. reflexivity. Qed.

Theorem drop_index_step {T} (m : nat) (t : T) (s : seq T) : 
  drop_index (m.+1) (t :: s) = t :: drop_index m s.
Proof. reflexivity. Qed.

Theorem drop_index_nth_low {T} : forall i j (s : seq T) d,
  j < i ->
  nth d (drop_index i s) j = nth d s j.
Proof.
  elim;[fcrush|].
  move=> i iH j [|x s] d jtl;sauto.
Qed.

Theorem drop_index_nth_high {T} : forall i j (s : seq T) d,
  i < j ->
  nth d (drop_index i s) (j - 1) = nth d s j.
Proof.
  elim;destruct j;try fcrush.
  move=> [|x s] d jg;[sauto use: nth_nil|].
  replace (j.+1 - 1) with j;[|sauto q:on].
  simpl.
  symmetry; rewrite <- H; [|auto].
  destruct j;[fcrush|].
  by replace (j.+1 - 1) with j;[|sauto q:on].
Qed.

Theorem index_low_decr {i} {j} {T} {s : seq T} :
  i < j -> j < length s -> j - 1 < length (drop_index i s).
Proof.
  move=> ltij ltj.
  rewrite drop_index_length;[sauto lq: on|hauto use: ltn_trans].
Qed.

Theorem decr_index_const  {i} {j} {T} {s : seq T}
  (ltj : j < length s) (ltjm : j - 1 < length (drop_index i s)) : 
  i < j -> 
  tnth (in_tuple (drop_index i s)) (Ordinal ltjm) =
  tnth (in_tuple s) (Ordinal ltj).
Proof.
  move=>ltij.
  destruct s as [|a s];[fcrush|].
  do 2 rewrite (tnth_nth a).
  move: s a j i ltj ltij ltjm.
  elim;[fcrush|].
  move=> b s IHs a j i ltj ltij ltjm.
  simpl; simpl in IHs.
  destruct j as [|j];[fcrush|].
  replace (j.+1 - 1) with j;[|sauto lq:on].
  destruct j, i; try fcrush.
  rewrite drop_index_step.
  simpl.
  destruct i;[fcrush|].
  destruct j;[fcrush|].
  change (nth a (drop_index i.+1 (b :: s)) j.+1)
    with (nth a (drop_index i.+1 (a :: s)) j.+1).
  replace (j.+1) with (j.+2 - 1) at 1;[|sauto lq:on].
  rewrite IHs; sauto.
Qed.

Theorem low_index_bound {i} {j} {T} {s : seq T} :
  j < length s -> j < i -> j < length (drop_index i s).
Proof.
  move=> ltj ltji.
  destruct (i < length s) eqn:lti.
  - rewrite drop_index_length;[|sauto].
    apply (leq_ltn_trans (n := i-1));sauto.
  - rewrite drop_index_length_high;[auto|].
    rewrite leqNgt; hauto.
Qed.

Theorem low_index_const {i} {j} {T} {s : seq T}
  (ltj : j < length s) (ltjm : j < length (drop_index i s)) : 
  j < i -> 
  tnth (in_tuple (drop_index i s)) (Ordinal ltjm) =
  tnth (in_tuple s) (Ordinal ltj).
Proof.
  move=>ltij.
  destruct s as [|a s];[fcrush|].
  do 2 rewrite (tnth_nth a).
  move: s a j i ltj ltij ltjm.
  elim;[fcrush|].
  move=> b s IHs a j i ltj ltij ltjm.
  simpl; simpl in IHs.
  destruct i as [|i];[fcrush|].
  simpl.
  destruct j as [|j];[auto|].
  rewrite drop_index_step.
  simpl.
  destruct i as [|i];[fcrush|].
  destruct j as [|j];[fcrush|].
  change (nth a (drop_index i.+1 (b :: s)) j.+1)
    with (nth a (drop_index i.+1 (a :: s)) j.+1).
  rewrite IHs; sauto.
Qed.

Theorem tnth_tuple_index {T} {s : seq T} (x : T) {i} (lti : i < length s) :
  tnth (in_tuple (x :: s)) (Ordinal (n:=length (x :: s)) (m:=i.+1) lti) = 
  tnth (in_tuple s) (Ordinal lti).
Proof. by do 2 rewrite (tnth_nth x). Qed.
