From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import Program.

Notation "|[ v ]|" := {n : nat | n < v} : type_scope.

Definition inlMap {A B C} (f : A -> C) (c : A + B) : C + B :=
  match c with
  | inl a => inl (f a)
  | inr b => inr b
  end.

Definition inrMap {A B C} (f : B -> C) (c : A + B) : A + C :=
  match c with
  | inl a => inl a
  | inr b => inr (f b)
  end.

Definition drop_index {T} (m : nat) (s : seq T) : seq T := 
  take m s ++ behead (drop m s).

Theorem drop_index_length {T} : forall (s : seq T) (m : nat),
  m < length s -> length (drop_index m s) = (length s).-1.
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
  nth d (drop_index i s) (j.-1) = nth d s j.
Proof.
  elim;destruct j;try fcrush.
  move=> [|x s] d jg;[sauto use: nth_nil|].
  simpl.
  symmetry; rewrite <- H; [|auto].
  destruct j;[fcrush|].
  sauto q:on.
Qed.

Theorem index_low_decr {i} {j} {T} {s : seq T} :
  i < j -> j < length s -> j.-1 < length (drop_index i s).
Proof.
  move=> ltij ltj.
  rewrite drop_index_length;[sauto lq: on|hauto use: ltn_trans].
Qed.

Theorem decr_index_const  {i} {j} {T} {s : seq T}
  (ltj : j < length s) (ltjm : j.-1 < length (drop_index i s)) : 
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
  destruct j, i; try fcrush.
  rewrite drop_index_step.
  simpl.
  destruct i;[fcrush|].
  destruct j;[fcrush|].
  change (nth a (drop_index i.+1 (b :: s)) j.+1)
    with (nth a (drop_index i.+1 (a :: s)) j.+1).
  replace (j.+1) with (j.+2.-1) at 1;[|sauto lq:on].
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


(*tnth : forall (n : nat) (T : Type), n.-tuple T -> {m : m < n} -> T*)

Definition lnth {T} (s : seq T) (i : {m | m < length s}) : T.
  apply (tnth (in_tuple s)).
  destruct i as [i lti].
  by exists i.
Defined.

Theorem map_length {A B} (f : A -> B) (s : seq A) : length [seq f i | i <- s] = length s.
Proof. move: s; elim; hauto q:on. Qed.

Theorem Ordinal_Rect n n2 m (i : m < n) (e : n = n2) :
  (eq_rect _ _ (Ordinal (n:=n) (m:=m) i) _ e) = Ordinal (eq_rect _ (fun x => m < x) i _ e).
Proof. by destruct e. Qed.

Theorem map_nth {A B} (f : A -> B) (s : seq A) (o : 'I_(length [seq f i | i <- s])) :
  tnth (in_tuple [seq f i | i <- s]) o = 
  f (tnth (in_tuple s) (eq_rect _ _ o _ (map_length _ _))).
Proof.
  move: s o; elim;[move=> [x xlt]; fcrush|].
  simpl.
  move=> a l IH o.
  destruct o.
  rewrite Ordinal_Rect.
  rewrite (tnth_nth (f a)).
  rewrite (tnth_nth a).
  destruct m;[reflexivity|].
  simpl.
  assert (m < length [seq f i | i <- l]) as H;[hauto|].
  transitivity (tnth (in_tuple [seq f i0 | i0 <- l]) (Ordinal H));[
  by rewrite (tnth_nth (f a))|].
  rewrite IH.
  rewrite Ordinal_Rect.
  by rewrite (tnth_nth a).
Qed.

Theorem map_lnth {A B} (f : A -> B) (s : seq A) (o : {m | m < length [seq f i | i <- s]}) :
  lnth [seq f i | i <- s] o = 
  f (lnth (in_tuple s) (eq_rect _ (fun x => {m : nat | m < x}) o _ (map_length _ _))).
Proof.
  unfold lnth.
  rewrite map_nth.
  do 2 f_equal.
  destruct o; simpl.
  apply ord_inj.
  by transitivity (Ordinal 
     (proj2_sig (eq_rect _ (fun x0 : nat => {m : nat | m < x0}) (exist _ x i) 
     (length s) (map_length f s))));[destruct (map_length f s)|destruct (eq_rect _ _ _ _)].
Qed.

Theorem map_nth_2 {A B} (f : A -> B) (s : seq A) (o : 'I_(length s)) :
  f (tnth (in_tuple s) o) 
  = tnth (in_tuple [seq f i | i <- s]) (eq_rect _ _ o _ (esym (map_length f _))).
Proof.
  move: s o; elim;[move=> [x xlt]; fcrush|].
  simpl.
  move=> a l IH o.
  destruct o.
  rewrite Ordinal_Rect.
  rewrite (tnth_nth (f a)).
  rewrite (tnth_nth a).
  destruct m;[reflexivity|].
  simpl.
  assert (m < length l) as H;[hauto|].
  transitivity (f (tnth (in_tuple l) (Ordinal H)));[
  by rewrite (tnth_nth a)|].
  rewrite IH.
  rewrite Ordinal_Rect.
  by rewrite (tnth_nth (f a)).
Qed.

Lemma map_nth_3_lem 
  {A T} {a b} (P Q : A -> Type) (tt : forall a, P a -> Q a -> T)
  (e : a = b) (pa : P a) (qb : Q b) :
  tt _ (eq_rect _ _ pa _ e) qb =
  tt _ pa (eq_rect _ _ qb _ (esym e)).
Proof. by destruct e. Qed.

Theorem map_nth_3 {A B} (f : A -> B) (s : seq A) (o : 'I_(length s)) :
  f (tnth (in_tuple s) o) 
  = tnth (eq_rect _ (fun i => i.-tuple B) (in_tuple [seq f i | i <- s])
         _ 
         (map_length f _)) o.
Proof.
  rewrite map_nth_2.
  by rewrite (map_nth_3_lem _ _ (fun x => @tnth x B) _ _ _).
Qed.


Definition idx_ord_iso {n} : {m : nat | m < n} -> 'I_n.
  move=> [i lti].
  by exists i.
Defined.

Definition ord_idx_iso {n} : 'I_n -> {m : nat | m < n}.
  move=> [i lti].
  by exists i.
Defined.

Theorem idx_ord_iso_canc {n} : forall i : {m : nat | m < n}, ord_idx_iso (idx_ord_iso i) = i.
  by move=> [i lti].
Qed.

Theorem ord_idx_iso_canc {n} : forall i : 'I_n, idx_ord_iso (ord_idx_iso i) = i.
  by move=> [i lti].
Qed.

Definition mktuple_idx {n} {T} : ({m : nat | m < n} -> T) -> n.-tuple T.
  move=> f.
  apply mktuple=> o.
  apply f, ord_idx_iso, o.
Defined.

Definition tnth_idx {n} {T} : n.-tuple T -> ({m : nat | m < n} -> T).
  move=> f i.
  apply idx_ord_iso in i.
  move: i.
  by apply tnth.
Defined.

Theorem mktuple_idx_canc {n} {T} : forall f : {m : nat | m < n} -> T, tnth_idx (mktuple_idx f) = f.
  move=> f.
  apply functional_extensionality.
  move=> [x ltx].
  unfold tnth_idx, mktuple_idx.
  by rewrite tnth_mktuple.
Qed.

Theorem mktuple_tnth : 
  forall [n : nat] [T' : Type] (t : n.-tuple T'),
  mktuple (tnth t) = t.
Proof.
  move=> n T t.
  symmetry; apply (tuple_map_ord t).
Qed.

Theorem tnth_idx_canc {n} {T} : forall t : n.-tuple T, mktuple_idx (tnth_idx t) = t.
  move=> t.
  unfold tnth_idx, mktuple_idx.
  transitivity [tuple tnth t o | o < n].
  f_equal; apply functional_extensionality=> x.
  by rewrite ord_idx_iso_canc.
  apply mktuple_tnth.
Qed.


Program Definition Subargs {n B} (f : forall i : {m : nat | m < n.+1}, B i) (i : {i : nat | i < n}) : B i := f i.

Program Definition ArgExtend {n B} (b : B) (f : {m : nat | m < n} -> B) (i : {m : nat | m < n.+1}) :=
  match i < n with
  | true => f i
  | false => b
  end.

Lemma OptionArgs_Lem {B} (i : {m : nat | m < 0}) : B i.
Proof. fcrush. Qed.

(*Propagated options up to function application *)
Program Fixpoint OptionArgs {n} {B : nat -> Type} (f : forall i : {m : nat | m < n}, option (B i)) :
  option (forall i : {m : nat | m < n}, B i) :=
  match n with
  | 0 => Some OptionArgs_Lem
  | n.+1 => 
    obind (fun fn : B n =>
      obind (fun f : forall i : {m : nat | m < n}, B (` i) =>
        Some (fun j : {m : nat | m < n.+1} =>
          (if Nat.eqb j n as b0 return (Nat.eqb j n = b0 -> B j)
            then fun jn0 : Nat.eqb (` j) n = true => 
              fn
            else fun jn1 : Nat.eqb j n = false => 
              f j
          ) (erefl (Nat.eqb j n)))) 
        (OptionArgs (Subargs f))) 
      (f n)
  end.
Next Obligation.
  by apply (elimT (PeanoNat.Nat.eqb_spec _ _)) in jn0.
Qed.
Next Obligation.
  apply EqNat.beq_nat_false, Compare_dec.not_eq in jn1.
  assert ((j < n) \/ (n < j));[by destruct jn1;[left|right];apply (introT ltP)|clear jn1].
  hauto use: contra_ltn_leq.
Qed.

Lemma NoFractions {j k} : ~ (j < k /\ k < j.+1).
  move: k; elim j.
  - move=> [|k] [H0 H1]; fcrush.
  - move=> n IH k [H0 H1].
    destruct k;[fcrush|].
    replace (n.+1 < k.+1) with (n < k) in H0;[|sfirstorder].
    replace (k.+1 < n.+2) with (k < n.+1) in H1;[|sfirstorder].
    assert (n < k /\ k < n.+1);[auto|apply (IH k H)].
Qed.

Theorem dep_if_case_true {T}
  (p : bool)
  (t : p = true) 
  (a : p = true -> T) 
  (b : p = false -> T) :
  (if p as b return p = b -> T then a else b) (erefl _) = a t.
Proof.
  destruct p.
  f_equal. apply proof_irrelevance.
  fcrush.
Qed.

Theorem dep_if_case_false {T}
  (p : bool)
  (t : p = false) 
  (a : p = true -> T) 
  (b : p = false -> T) :
  (if p as b return p = b -> T then a else b) (erefl _) = b t.
Proof.
  destruct p.
  fcrush.
  f_equal. apply proof_irrelevance.
Qed.

Ltac dep_if_case b :=
  let t := fresh "dep_if_case_DUMMY" in
  pose t := b;assert (b = t);
  [trivial|destruct t;[rewrite dep_if_case_true|rewrite dep_if_case_false]].

Record Sigma11Model : Type :=
    mkSigma11Model {
        R : ringType;
        (*lt should be a strict, total order with a least element*)
        lt : relation R;
        so : StrictOrder lt;
        lt_total : forall x y, (lt x y) + ((x==y) + (lt y x));
        lt_dec x y :=
          match lt_total x y with
          | inl _ => true
          | inr _ => false
          end;
        min : R;
        least_elem : forall x, lt min x
      }.
