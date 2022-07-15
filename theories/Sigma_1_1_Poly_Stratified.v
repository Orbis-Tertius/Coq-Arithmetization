From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import Program.

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


Section Sigma_1_1_Internal.

Definition SOctx := seq nat.
Definition FOctx := nat.

Inductive RingTerm {soctx : SOctx} {foctx : FOctx} : Type :=
| RingVar : {m : nat | m < foctx} -> RingTerm
| RingFun : forall (i : {m : nat | m < length soctx}),
            ({m : nat | m < lnth soctx i} -> RingTerm) ->
            RingTerm
| RingMinusOne : RingTerm
| RingPlusOne : RingTerm
| RingZero : RingTerm
| RingPlus : RingTerm -> RingTerm -> RingTerm
| RingTimes : RingTerm -> RingTerm -> RingTerm.

Program Fixpoint RingTermFOQuote {soctx} {foctx}
  (r : @RingTerm soctx foctx) : RingTerm (soctx := soctx) (foctx := foctx.+1) :=
  match r with
  | RingVar m => RingVar (m.+1)
  | RingFun i f => RingFun i (fun x => RingTermFOQuote (f x))
  | RingMinusOne => RingMinusOne
  | RingPlusOne => RingPlusOne
  | RingZero => RingZero
  | RingPlus r1 r2 => RingPlus (RingTermFOQuote r1) (RingTermFOQuote r2)
  | RingTimes r1 r2 => RingTimes (RingTermFOQuote r1) (RingTermFOQuote r2)
  end.

Program Fixpoint RingTermSOQuote {soctx} {foctx} {bs}
  (r : @RingTerm soctx foctx) : @RingTerm (bs :: soctx) foctx :=
  match r with
  | RingVar m => RingVar m
  | RingFun i f => RingFun (i.+1) (fun x => RingTermSOQuote (f x))
  | RingMinusOne => RingMinusOne
  | RingPlusOne => RingPlusOne
  | RingZero => RingZero
  | RingPlus r1 r2 => RingPlus (RingTermSOQuote r1) (RingTermSOQuote r2)
  | RingTimes r1 r2 => RingTimes (RingTermSOQuote r1) (RingTermSOQuote r2)
  end.
Next Obligation.
  simpl in H.
  unfold lnth in H; unfold lnth.
  by do 2 rewrite (tnth_nth 0) in H *.
Qed.

Program Fixpoint RingTermFOSubst {soctx : SOctx} {foctx : FOctx}
  (i : {m : nat | m < foctx})
  (t : @RingTerm soctx (foctx.-1)) (r : @RingTerm soctx foctx) :
  @RingTerm soctx (foctx.-1) :=
  match r with
  | RingVar m => 
    match (Nat.compare i m) with
    | Eq => t
    | Lt => RingVar (m.-1)
    | Gt => RingVar m
    end
  | RingFun j f => RingFun j (fun x => RingTermFOSubst i t (f x))
  | RingMinusOne => RingMinusOne
  | RingPlusOne => RingPlusOne
  | RingZero => RingZero
  | RingPlus r1 r2 => RingPlus (RingTermFOSubst i t r1) (RingTermFOSubst i t r2)
  | RingTimes r1 r2 => RingTimes (RingTermFOSubst i t r1) (RingTermFOSubst i t r2)
  end.
Next Obligation.
  symmetry in Heq_anonymous.
  rewrite <- Compare_dec.nat_compare_lt in Heq_anonymous.
  apply (introT (b := i < m) ltP) in Heq_anonymous.
  sauto lq: on.
Qed.
Next Obligation.
  symmetry in Heq_anonymous.
  rewrite <- Compare_dec.nat_compare_gt in Heq_anonymous.
  apply (introT (b := m < i) ltP) in Heq_anonymous.
  hauto lq: on use: leq_ltn_trans unfold: Nat.pred.
Qed.

(*Substitution acts as an unquote when applied after quoting.*)
Theorem FOsubsts_unquote {soctx : SOctx} {foctx : FOctx} :
  forall (x : @RingTerm soctx foctx)
         (e : @RingTerm soctx foctx)
         (H : 0 < foctx.+1),
  RingTermFOSubst (exist _ 0 H) x (RingTermFOQuote e) = e.
Proof.
  move=> x; elim; try hauto q:on.
  - move=> [i lti] H.
    cbn; do 2 f_equal; apply proof_irrelevance.
  - move=> [i lti] t rH H.
    cbn.
    f_equal.
    apply functional_extensionality.
    move => [m ltm].
    by rewrite rH.
Qed.

Program Fixpoint RingTermSOSubst {soctx : SOctx} {foctx : FOctx}
  (i : { m : nat | m < length soctx})
  (f : ({m : nat | m < lnth soctx i} -> @RingTerm (drop_index i soctx) foctx) 
       -> @RingTerm (drop_index i soctx) foctx)
  (r : @RingTerm soctx foctx) : @RingTerm (drop_index i soctx) foctx :=
  match r with
  | RingVar m => RingVar m
  | RingFun j t =>
    match (Nat.compare i j) with
    | Eq => f (fun x => RingTermSOSubst i f (t x))
    | Lt => RingFun (j.-1) (fun x => RingTermSOSubst i f (t x))
    | Gt => RingFun j (fun x => RingTermSOSubst i f (t x))
    end
  | RingMinusOne => RingMinusOne
  | RingPlusOne => RingPlusOne
  | RingZero => RingZero
  | RingPlus r1 r2 => RingPlus (RingTermSOSubst i f r1) (RingTermSOSubst i f r2)
  | RingTimes r1 r2 => RingTimes (RingTermSOSubst i f r1) (RingTermSOSubst i f r2)
  end.
Next Obligation.
  symmetry in Heq_anonymous.
  apply Compare_dec.nat_compare_eq in Heq_anonymous.
  by rewrite (subset_eq_compat _ (fun m => m < length soctx) j i H0 H1).
Qed.
Next Obligation.
  symmetry in Heq_anonymous.
  apply Compare_dec.nat_compare_lt, (introT (b := i < j) ltP) in Heq_anonymous.
  destruct j;[fcrush|simpl].
  clear t f Heq_anonymous foctx.
  move: i j soctx H H0; elim.
  by move=> j [|n soctx].
  move=> i IH [|n [|m soctx]] lt;[fcrush|hauto|hauto].
Qed.
Next Obligation.
  unfold lnth; unfold lnth in H.
  do 2 rewrite (tnth_nth 0) in H *.
  simpl in H; simpl.
  symmetry in Heq_anonymous.
  apply Compare_dec.nat_compare_lt, (introT (b := i < j) ltP) in Heq_anonymous.
  clear f t foctx.
  move: soctx i j H H0 H1 Heq_anonymous; elim.
  by move=> i [|j].
  move=> n soctx IH i j ltx ltj lti ltij.
  destruct j;[fcrush|simpl].
  destruct i;[exact ltx|].
  apply (IH i); auto.
  by destruct j. 
Qed.
Next Obligation.
  symmetry in Heq_anonymous.
  apply Compare_dec.nat_compare_gt, (introT (b := j < i) ltP) in Heq_anonymous.
  clear t f foctx.
  move: i j soctx H H0 Heq_anonymous; elim.
  by move=> j [|].
  move=> i IH j [|n soctx] ltj lti ltji;[fcrush|].
  change (length _) with ((length (drop_index i soctx)).+1).
  destruct j;auto.
  assert (j < length (drop_index i soctx));auto.
Qed.
Next Obligation.
  unfold lnth; unfold lnth in H.
  do 2 rewrite (tnth_nth 0) in H *.
  simpl in H; simpl.
  symmetry in Heq_anonymous.
  apply Compare_dec.nat_compare_gt, (introT (b := j < i) ltP) in Heq_anonymous.
  clear f t foctx.
  move: soctx i j H H0 H1 Heq_anonymous; elim.
  by move=> i [|j].
  move=> n soctx IH i j ltx ltj lti ltij.
  destruct j, i; auto.
  by apply (IH i).
Qed.

Lemma SOsubsts_unquote_lem {soctx} {foctx}
  (i j : {m : nat | m < length soctx})
  (fi : {m : nat | m < lnth soctx i} -> @RingTerm soctx foctx)
  (fj : {m : nat | m < lnth soctx j} -> @RingTerm soctx foctx)
  (p : i = j) : eq_rect i (fun x => {m : nat | m < lnth soctx x} -> RingTerm) fi j p = fj
  -> RingFun i fi = RingFun j fj.
Proof.
  destruct p.
  simpl.
  by intros [].
Qed.

Theorem SOsubsts_unquote {soctx : SOctx} {foctx : FOctx} :
  forall n
         (e : @RingTerm soctx foctx)
         (H : 0 < length (n :: soctx)) f,
  RingTermSOSubst (exist _ 0 H) f (RingTermSOQuote (bs := n) e) = e.
Proof.
  move=> n r lt0 f.
  move: r; elim; try hauto.
  move=> [i lti] r IH.
  simpl.
  remember (RingTermSOSubst_obligation_3 _ _ _ _ _ _ _ _ _) as dummy1; clear Heqdummy1.
  remember (RingTermSOSubst_obligation_2 _ _ _ _ _ _ _ _) as dummy2; clear Heqdummy2.
  change (drop_index 0 (n :: soctx)) with soctx.
  assert ((exist (fun m : nat => m < length soctx) i lti)
          = exist (fun m : nat => m < length soctx) i (dummy2 (erefl Lt))) as H.
  f_equal; apply eq_irrelevance.
  symmetry.
  apply (SOsubsts_unquote_lem _ _ _ _ H).
  apply functional_extensionality. 
  move=> [x ltx].
  rewrite IH.
  remember (RingTermSOQuote_obligation_2 _ _ _ _ _ _ _ _) as dummy3; clear Heqdummy3.
  simpl in dummy3; clear dummy1.
  destruct H.
  simpl; clear dummy2.
  do 2 f_equal; apply eq_irrelevance.
Qed.

Inductive ZerothOrderFormula {soctx : SOctx} {foctx : FOctx} : Type :=
| ZOTrue : ZerothOrderFormula
| ZOFalse : ZerothOrderFormula
| ZONot : ZerothOrderFormula -> ZerothOrderFormula
| ZOAnd : ZerothOrderFormula ->
          ZerothOrderFormula ->
          ZerothOrderFormula
| ZOOr : ZerothOrderFormula ->
         ZerothOrderFormula ->
         ZerothOrderFormula
| ZOImp : ZerothOrderFormula ->
          ZerothOrderFormula ->
          ZerothOrderFormula
| ZOEq : @RingTerm soctx foctx -> 
         @RingTerm soctx foctx ->
         ZerothOrderFormula.


(*
Program Fixpoint ZerothOrderFormulaFOSubst_pro {soctx : SOctx} {foctx : FOctx} 
  (i : {n : nat | n < foctx}) (t : @RingTerm soctx foctx.-1)
  (s : @ZerothOrderFormula soctx foctx) : @ZerothOrderFormula soctx foctx.-1 :=
  match s with
  | ZOTrue => ZOTrue
  | ZOFalse => ZOFalse
  | ZONot s => ZONot (ZerothOrderFormulaFOSubst_pro i t s)
  | ZOAnd s1 s2 => ZOAnd (ZerothOrderFormulaFOSubst_pro i t s1)
                         (ZerothOrderFormulaFOSubst_pro i t s2)
  | ZOOr s1 s2 => ZOOr (ZerothOrderFormulaFOSubst_pro i t s1)
                       (ZerothOrderFormulaFOSubst_pro i t s2)
  | ZOImp s1 s2 => ZOImp (ZerothOrderFormulaFOSubst_pro i t s1)
                         (ZerothOrderFormulaFOSubst_pro i t s2)
  | ZOEq r1 r2 => ZOEq (RingTermFOSubst_pro i t s1)
                       (RingTermFOSubst_pro i t s2)
  end.
*)

Definition ZerothOrderFormulaFOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_foctx),
  @RingTerm soctx foctx.-1 ->
  @ZerothOrderFormula soctx foctx ->
  @ZerothOrderFormula soctx foctx.-1.
  intros i t s.
  induction s.
  - exact ZOTrue.
  - exact ZOFalse.
  - exact (ZONot IHs).
  - exact (ZOAnd IHs1 IHs2).
  - exact (ZOOr IHs1 IHs2).
  - exact (ZOImp IHs1 IHs2).
  - exact (ZOEq (RingTermFOSubst i t r) (RingTermFOSubst i t r0)).
Defined.

Definition ZerothOrderFormulaSOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_(length soctx)),
  (('I_(tnth (in_tuple soctx) i) -> 
   @RingTerm (drop_index i soctx) foctx) -> 
   @RingTerm (drop_index i soctx) foctx) ->
  @ZerothOrderFormula soctx foctx ->
  @ZerothOrderFormula (drop_index i soctx) foctx.
  intros i f s.
  induction s.
  - exact ZOTrue.
  - exact ZOFalse.
  - exact (ZONot IHs).
  - exact (ZOAnd IHs1 IHs2).
  - exact (ZOOr IHs1 IHs2).
  - exact (ZOImp IHs1 IHs2).
  - exact (ZOEq (RingTermSOSubst i f r) (RingTermSOSubst i f r0)).
Defined.

Inductive FirstOrderFormula {soctx : SOctx} {foctx : FOctx} : Type :=
| ZO : @ZerothOrderFormula soctx foctx -> FirstOrderFormula
| FOExists : @RingTerm soctx foctx -> FirstOrderFormula (foctx := foctx.+1) -> FirstOrderFormula
| FOForall : @RingTerm soctx foctx -> FirstOrderFormula (foctx := foctx.+1) -> FirstOrderFormula. 

(*
Program Fixpoint FirstOrderFormulaFOSubst {soctx : SOctx} {foctx : FOctx}
  (i : {n : nat | n < foctx}) (t : @RingTerm soctx foctx.-1)
  (s : @FirstOrderFormula soctx foctx) : @FirstOrderFormula soctx foctx.-1 :=
  match s with
  | ZO z => ZO (ZerothOrderFormulaFOSubst i t z)
  | FOExists b f => FOExists (RingTermFOSubst i t b)
                             (FirstOrderFormulaFOSubst (i.+1) (RingTermFOQuote t) f)
  | FOForall b f => FOForall (RingTermFOSubst i t b)
                             (FirstOrderFormulaFOSubst (i.+1) (RingTermFOQuote t) f)
  end.
*)

Definition FirstOrderFormulaFOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_foctx),
  @RingTerm soctx foctx.-1 ->
  @FirstOrderFormula soctx foctx ->
  @FirstOrderFormula soctx foctx.-1.
  intros i t s.
  induction s.
  - exact (ZO (ZerothOrderFormulaFOSubst i t z)).
  - apply (FOExists (RingTermFOSubst i t r)).
    destruct i as [i lti].
    assert (i.+1 < foctx.+1) as H;[auto|].
    destruct foctx;[fcrush|].
    apply (IHs (Ordinal (m := i.+1) H)).
    apply RingTermFOQuote.
    exact t.
  - apply (FOForall (RingTermFOSubst i t r)).
    destruct i as [i lti].
    assert (i.+1 < foctx.+1) as H;[auto|].
    destruct foctx;[fcrush|].
    apply (IHs (Ordinal (m := i.+1) H)).
    apply RingTermFOQuote.
    exact t.
Defined.

Definition FirstOrderFormulaSOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_(length soctx)),
  (('I_(tnth (in_tuple soctx) i) -> 
   @RingTerm (drop_index i soctx) foctx) -> 
   @RingTerm (drop_index i soctx) foctx) ->
  @FirstOrderFormula soctx foctx ->
  @FirstOrderFormula (drop_index i soctx) foctx.
  intros i f s.
  induction s.
  - exact (ZO (ZerothOrderFormulaSOSubst i f z)).
  - apply (FOExists (RingTermSOSubst i f r)).
    apply IHs.
    intro t.
    assert (0 < foctx.+1) as H;[auto|].
    apply (fun x => RingTermFOQuote (f x)).
    exact (fun x => (RingTermFOSubst (Ordinal H) RingZero (t x))).
  - apply (FOForall (RingTermSOSubst i f r)).
    apply IHs.
    intro t.
    assert (0 < foctx.+1) as H;[auto|].
    apply (fun x => RingTermFOQuote (f x)).
    exact (fun x => (RingTermFOSubst (Ordinal H) RingZero (t x))).
Defined.

Inductive SecondOrderFormula {soctx : SOctx} {foctx : FOctx} : Type :=
| FO : @FirstOrderFormula soctx foctx -> 
       SecondOrderFormula
| SOExists : forall (y : @RingTerm soctx foctx) (bs : seq (@RingTerm soctx foctx)), 
              SecondOrderFormula (soctx := length bs :: soctx) ->
              SecondOrderFormula.

Program Fixpoint SecondOrderFormulaFOSubst {soctx : SOctx} {foctx : FOctx}
  (i : 'I_foctx) (t : @RingTerm soctx foctx.-1)
  (s : @SecondOrderFormula soctx foctx) : @SecondOrderFormula soctx foctx.-1 :=
  match s with
  | FO f => FO (FirstOrderFormulaFOSubst i t f)
  | SOExists y bs f => 
    SOExists (RingTermFOSubst i t y) 
             [ seq (RingTermFOSubst i t r) | r <- bs ]
             (SecondOrderFormulaFOSubst i (RingTermSOQuote (bs := length bs) t) f)
  end.
Next Obligation.
  clear f.
  f_equal.
  move: bs; elim; hauto.
Qed.

Definition SecondOrderFormulaSOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_(length soctx)),
  (('I_(tnth (in_tuple soctx) i) -> 
   @RingTerm (drop_index i soctx) foctx) -> 
   @RingTerm (drop_index i soctx) foctx) ->
  @SecondOrderFormula soctx foctx ->
  @SecondOrderFormula (drop_index i soctx) foctx.
  move=> i f X;move: i f.
  induction X; move=>i f2.
  - exact (FO (FirstOrderFormulaSOSubst _ f2 f)).
  - apply (SOExists (RingTermSOSubst i f2 y) [ seq (RingTermSOSubst i f2 r) | r <- bs ]).
    assert (i.+1 < length (length bs :: soctx)) as H;[destruct i; auto|].
    rewrite map_length.
    apply (IHX (Ordinal (m := i.+1) H)).
    move=> t.
    apply RingTermSOQuote.
    apply: f2.
    move=> jo.
    replace (tnth (in_tuple (length bs :: soctx))
             (Ordinal (n:=length (length bs :: soctx)) (m:=i.+1) H))
       with (tnth (in_tuple soctx) i) in t;
    [|by do 2 rewrite (tnth_nth 0)].
    apply t in jo; clear t.
    assert (forall ctx, 0 < length (length bs :: ctx)) as H0;[fcrush|].
    apply (RingTermSOSubst (Ordinal (H0 _)) (fun _ => RingZero)).
    exact jo.
Defined.

(*
Example sigma11_1 : @SecondOrderFormula nil 0.
  apply (SOExists 5 [::2;3;4]).
  apply (SOExists 3 [::1;2]).
  apply FO.
  apply (FOExists 7).
  apply (FOForall 6).
  apply (FOExists 5).
  apply ZO.
  apply ZOOr.
  apply ZOAnd.
  apply ZOEq.
  apply RingPlusOne.
  apply (RingVar (inord 0)).
  apply ZOEq.
  apply (RingFun (soctx := [::_;_]) (inord 0)).
  intros [i lt].
  destruct i;[apply RingPlusOne|].
  destruct i;[apply RingMinusOne|].
  unfold in_tuple, tnth, tval in lt.
  rewrite inordK in lt;[|auto]; cbn in lt; inversion lt.
  apply (RingFun (soctx := [::_;_]) (inord 1)).
  intros [i lt].
  destruct i;[apply RingPlusOne|].
  destruct i;[apply RingMinusOne|].
  destruct i;[apply RingZero|].
  unfold in_tuple, tnth, tval in lt.
  rewrite inordK in lt;[|auto];cbn in lt;inversion lt.
  apply ZOTrue.
Defined.

Example sigma11_2 : @SecondOrderFormula nil 0 :=
  SOExists 5 [:: 2; 3; 4] (SOExists 3 [:: 1; 2]
	(FO (FOExists 7 (FOForall 6 (FOExists 5 (ZO
  (ZOOr
    (ZOAnd 
      (ZOEq RingPlusOne (RingVar (inord 0)))
      (ZOEq
        (RingFun (soctx := [:: _; _]) (inord 0)
          (fun X  =>
            match X with
            | @Ordinal _ i _ =>
                match i with
                | 0 => RingPlusOne
                | _.+1 => RingMinusOne
                end
            end))
        (RingFun (soctx := [:: _; _]) (inord 1)
          (fun X =>
            match X with
            | @Ordinal _ i _ =>
                match i with
                | 0 => RingPlusOne
                | 1 => RingMinusOne
                | _.+2 => RingZero
                end
            end))
      )) ZOTrue))))))).
*)

End Sigma_1_1_Internal.



Section Sigma_1_1_Denotation.

Record SecondOrderFormulaModel : Type :=
    mkSecondOrderFormulaModel {
        R : ringType;
        (*lt should be a strict, total order with a least element*)
        lt : relation R;
        so : StrictOrder lt;
        lt_total : forall x y, lt x y \/ x==y \/ lt y x;
        min : R;
        least_elem : forall x, lt min x
      }.

Program Definition Subargs {n B} (f : {m : nat | m < n.+1} -> B) (i : {i : nat | i < n}) : B := f i.

Program Definition ArgExtend {n B} (b : B) (f : {m : nat | m < n} -> B) (i : {m : nat | m < n.+1}) :=
  match i < n with
  | true => f i
  | false => b
  end.

Lemma OptionArgs_Lem {B} (i : {m : nat | m < 0}) : B.
Proof. fcrush. Qed.

(*Propagated options up to function argument*)
Program Fixpoint OptionArgs {n B} (f : {m : nat | m < n} -> option B) :
  option ({m : nat | m < n} -> B) :=
  match n with
  | 0 => Some OptionArgs_Lem
  | n.+1 => 
    Option.bind
      (fun f' => 
        Option.bind
          (fun b => Some (ArgExtend b f'))
          (f n) )
      (OptionArgs (Subargs f))
  end.

(*Interpreting a ring term with free variables as a function from ring elems. and functions. *)
Definition Ring_Denote (M : SecondOrderFormulaModel)
  (v1 : seq (R M))
  (v2 : seq {n : nat & 
            {y : (R M) & 
            {bs : n.-tuple (R M) & 
            (forall i : 'I_n, { r : R M | lt M r (tnth bs i) }) -> { r : R M | lt M r y }
            }}})
  (s : @RingTerm [seq projT1 i | i <- v2] (length v1)) :
  option (R M).
  move:s; elim.
  - move=> idx; exact (Some (tnth (in_tuple v1) idx)).
  - move=> idx _ IH.
    rewrite map_nth in IH.
    destruct (tnth _ _) as [n[y[bs f]]]; simpl in IH.
    exact (f IH).
  - exact (Some (-1)%R).
  - exact (Some 1%R).
  - exact (Some 0%R).
  - move=> _ r1 _ r2; exact (r1 + r2)%R.
  - move=> _ r1 _ r2; exact (r1 * r2)%R.
Defined.

Fixpoint ZerothOrder_Denote (M : SecondOrderFormulaModel) 
  (v1 : seq (R M))
  (v2 : seq {n : nat & 
            {y : (R M) & 
            {bs : n.-tuple (R M) & 
            {f : ('I_n -> R M) -> R M | 
            (forall (t : 'I_n -> R M), (forall x : 'I_n, lt M (t x) (tnth bs x)) -> lt M (f t) y)
            }}}})
  (f : @ZerothOrderFormula [seq projT1 i | i <- v2] (length v1)) : Prop :=
  match f with
  | ZOTrue => true
  | ZOFalse => false
  | ZONot f => not (ZerothOrder_Denote M v1 v2 f)
  | ZOAnd f1 f2 => (ZerothOrder_Denote M v1 v2 f1) /\ (ZerothOrder_Denote M v1 v2 f2)
  | ZOOr f1 f2 => (ZerothOrder_Denote M v1 v2 f1) \/ (ZerothOrder_Denote M v1 v2 f2)
  | ZOImp f1 f2 => (ZerothOrder_Denote M v1 v2 f1) -> (ZerothOrder_Denote M v1 v2 f2)
  | ZOEq r1 r2 => Ring_Denote M v1 v2 r1 = Ring_Denote M v1 v2 r2
  end.

Fixpoint FirstOrder_Denote (M : SecondOrderFormulaModel) 
  (v1 : seq (R M))
  (v2 : seq {n : nat & 
            {y : (R M) & 
            {bs : n.-tuple (R M) & 
            {f : ('I_n -> R M) -> R M | 
            (forall (t : 'I_n -> R M), (forall x : 'I_n, lt M (t x) (tnth bs x)) -> lt M (f t) y)
            }}}})
  (f : @FirstOrderFormula [seq projT1 i | i <- v2] (length v1)) : Prop :=
  match f with
  | ZO z => ZerothOrder_Denote M v1 v2 z
  | FOExists n f => 
    exists (r : R M), 
      lt M r (naturalRingElement n) /\
      FirstOrder_Denote M (r :: v1) v2 f
  | FOForall n f =>
    forall (r : R M), 
      lt M r (naturalRingElement n) ->
      FirstOrder_Denote M (r :: v1) v2 f
  end.

(*Interpreting a ring term with free variables as a function from ring elems. and functions. *)
Program Fixpoint SecondOrder_Denote (M : SecondOrderFormulaModel) 
  (v1 : seq (R M))
  (v2 : seq {n : nat & 
            {y : (R M) & 
            {bs : n.-tuple (R M) & 
            {f : ('I_n -> R M) -> R M | 
            (forall (t : 'I_n -> R M), (forall x : 'I_n, lt M (t x) (tnth bs x)) -> lt M (f t) y)
            }}}})
  (f : @SecondOrderFormula [seq projT1 i | i <- v2] (length v1)) : Prop :=
  match f with
  | FO f => FirstOrder_Denote M v1 v2 f
  | SOExists y bs f => 
    exists (rf : ('I_(length bs) -> R M) -> R M)
    (p : forall (t : 'I_(length bs) -> R M),
          (forall x : 'I_(length bs), 
            lt M (t x) (naturalRingElement (tnth (in_tuple bs) x))) ->
            lt M (rf t) (naturalRingElement y)),
    SecondOrder_Denote M v1 
      (existT _ (length bs) 
      (existT _ (naturalRingElement y) 
      (existT _ (in_tuple (map naturalRingElement bs))
      (exist _ rf p))) :: v2) f
  end.
Next Obligation.
  by rewrite <- (map_length (@naturalRingElement (R M))).
Qed.
Next Obligation.
  rewrite map_nth_3.
  do 2 f_equal.
  apply proof_irrelevance.
Qed.

(*
Note: This is impossible. Consider if one of the bs bounds is 0; then it's impossible
      for any applied argument to type check. Bounds should be part of the proposition,
      not enforced on the type level.

Definition Sigma11_Pred (M : SecondOrderFormulaModel)
  (v1 : seq (R M))
  (v2 : seq {n : nat & 
            {y : (R M) & 
            {bs : n.-tuple (R M) & 
            ((forall o : 'I_n, {r : (R M) | lt M r (tnth bs o)}) -> {r : R M | lt M r y})}}})
  (s : @RingTerm [seq projT1 i | i <- v2] (length v1)) :
  R M := ...
*)

End Sigma_1_1_Denotation.
