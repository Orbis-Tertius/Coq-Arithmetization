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

Program Fixpoint ZerothOrderFormulaFOSubst {soctx : SOctx} {foctx : FOctx} 
  (i : {n : nat | n < foctx}) (t : @RingTerm soctx foctx.-1)
  (s : @ZerothOrderFormula soctx foctx) : @ZerothOrderFormula soctx foctx.-1 :=
  match s with
  | ZOTrue => ZOTrue
  | ZOFalse => ZOFalse
  | ZONot s => ZONot (ZerothOrderFormulaFOSubst i t s)
  | ZOAnd s1 s2 => ZOAnd (ZerothOrderFormulaFOSubst i t s1)
                         (ZerothOrderFormulaFOSubst i t s2)
  | ZOOr s1 s2 => ZOOr (ZerothOrderFormulaFOSubst i t s1)
                       (ZerothOrderFormulaFOSubst i t s2)
  | ZOImp s1 s2 => ZOImp (ZerothOrderFormulaFOSubst i t s1)
                         (ZerothOrderFormulaFOSubst i t s2)
  | ZOEq r1 r2 => ZOEq (RingTermFOSubst i t r1)
                       (RingTermFOSubst i t r2)
  end.


Program Fixpoint ZerothOrderFormulaSOSubst {soctx : SOctx} {foctx : FOctx} 
  (i : {n : nat | n < length soctx}) 
  (f : ({m | m < lnth soctx i} -> 
       @RingTerm (drop_index i soctx) foctx) -> 
       @RingTerm (drop_index i soctx) foctx)
  (s : @ZerothOrderFormula soctx foctx) : @ZerothOrderFormula (drop_index i soctx) foctx :=
  match s with
  | ZOTrue => ZOTrue
  | ZOFalse => ZOFalse
  | ZONot s => ZONot (ZerothOrderFormulaSOSubst i f s)
  | ZOAnd s1 s2 => ZOAnd (ZerothOrderFormulaSOSubst i f s1)
                         (ZerothOrderFormulaSOSubst i f s2)
  | ZOOr s1 s2 => ZOOr (ZerothOrderFormulaSOSubst i f s1)
                       (ZerothOrderFormulaSOSubst i f s2)
  | ZOImp s1 s2 => ZOImp (ZerothOrderFormulaSOSubst i f s1)
                         (ZerothOrderFormulaSOSubst i f s2)
  | ZOEq r1 r2 => ZOEq (RingTermSOSubst i f r1)
                       (RingTermSOSubst i f r2)
  end.

Inductive FirstOrderFormula {soctx : SOctx} {foctx : FOctx} : Type :=
| ZO : @ZerothOrderFormula soctx foctx -> FirstOrderFormula
| FOExists : @RingTerm soctx foctx -> FirstOrderFormula (foctx := foctx.+1) -> FirstOrderFormula
| FOForall : @RingTerm soctx foctx -> FirstOrderFormula (foctx := foctx.+1) -> FirstOrderFormula. 

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
Next Obligation.
  by destruct foctx.
Qed.
Next Obligation.
  by destruct foctx.
Qed.
Next Obligation.
  by destruct foctx.
Qed.
Next Obligation.
  by destruct foctx.
Qed.

(*Is this correct? Substitution should occure after quoting so things aren't deleted.*)
Program Fixpoint FirstOrderFormulaSOSubst {soctx : SOctx} {foctx : FOctx}
  (i : {n : nat | n < length soctx})
  (f : ({m | m < lnth soctx i} -> 
       @RingTerm (drop_index i soctx) foctx) -> 
       @RingTerm (drop_index i soctx) foctx)
  (s : @FirstOrderFormula soctx foctx) : @FirstOrderFormula (drop_index i soctx) foctx :=
  match s with
  | ZO z => ZO (ZerothOrderFormulaSOSubst i f z)
  | FOExists b o => FOExists (RingTermSOSubst i f b)
                             (FirstOrderFormulaSOSubst i (fun t => RingTermFOQuote (f (fun x => RingTermFOSubst 0 RingZero (t x)))) o)
  | FOForall b o => FOForall (RingTermSOSubst i f b)
                             (FirstOrderFormulaSOSubst i (fun t => RingTermFOQuote (f (fun x => RingTermFOSubst 0 RingZero (t x)))) o)
  end.

Inductive SecondOrderFormula {soctx : SOctx} {foctx : FOctx} : Type :=
| FO : @FirstOrderFormula soctx foctx -> 
       SecondOrderFormula
| SOExists : forall (y : @RingTerm soctx foctx) (bs : seq (@RingTerm soctx foctx)), 
              SecondOrderFormula (soctx := length bs :: soctx) ->
              SecondOrderFormula.

Program Fixpoint SecondOrderFormulaFOSubst {soctx : SOctx} {foctx : FOctx}
  (i : {n : nat | n < foctx}) (t : @RingTerm soctx foctx.-1)
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

(*Is this correct? Substitution should occure after quoting so things aren't deleted.*)
Program Fixpoint SecondOrderFormulaSOSubst {soctx : SOctx} {foctx : FOctx}
  (i : {n : nat | n < length soctx})
  (f : ({m | m < lnth soctx i} -> 
       @RingTerm (drop_index i soctx) foctx) -> 
       @RingTerm (drop_index i soctx) foctx)
  (s : @SecondOrderFormula soctx foctx) :
  @SecondOrderFormula (drop_index i soctx) foctx :=
  match s with
  | FO o => FO (FirstOrderFormulaSOSubst i f o)
  | SOExists y bs o => 
    SOExists (RingTermSOSubst i f y)
             [seq RingTermSOSubst i f r | r <- bs]
             (SecondOrderFormulaSOSubst (i.+1 : {m | m < length (length bs :: soctx)})
                (fun t => RingTermSOQuote (f (fun x => RingTermSOSubst 0 (fun=> RingZero) (t x))))
                o)
  end.
Next Obligation.
  unfold lnth;   unfold lnth in H.
  by do 2 rewrite (tnth_nth 0) in H *.
Qed.
Next Obligation.
  by rewrite map_length.
Qed.

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
        lt_total : forall x y, (lt x y) + ((x==y) + (lt y x));
        min : R;
        least_elem : forall x, lt min x
      }.

Program Definition Subargs {n B} (f : forall i : {m : nat | m < n.+1}, B i) (i : {i : nat | i < n}) : B i := f i.

Program Definition ArgExtend {n B} (b : B) (f : {m : nat | m < n} -> B) (i : {m : nat | m < n.+1}) :=
  match i < n with
  | true => f i
  | false => b
  end.

Lemma OptionArgs_Lem {B} (i : {m : nat | m < 0}) : B i.
Proof. fcrush. Qed.

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

(*Interpreting a ring term with free variables as a function from ring elems. and functions. *)
Program Fixpoint Ring_Denote (M : SecondOrderFormulaModel)
  (v1 : seq (R M))
  (v2 : seq {y : (R M) & 
            {bs : seq (R M) & 
            (forall i : {m | m < length bs}, { r : R M | lt M r (lnth bs i) }) -> { r : R M | lt M r y }
            }})
  (r : @RingTerm [seq length (projT1 (projT2 i)) | i <- v2] (length v1)) :
  option (R M) :=
  match r with
  | RingVar m => Some (lnth v1 m)
  | RingFun i t =>
    obind (fun t : {m : nat | m < lnth [seq length (projT1 (projT2 i)) | i <- v2] i} -> RingTerm =>

      )
      (OptionArgs (fun x => Ring_Denote M v1 v2 t x))
  | RingMinusOne => Some (-1)%R
  | RingPlusOne => Some 1%R
  | RingZero => Some 0%R
  | RingPlus r1 r2 => (Ring_Denote M v1 v2 r1) + (Ring_Denote M v1 v2 r2)
  | RingTimes r1 r2 => (Ring_Denote M v1 v2 r1) * (Ring_Denote M v1 v2 r2)
  end.


(*Interpreting a ring term with free variables as a function from ring elems. and functions. *)
Definition Ring_Denote (M : SecondOrderFormulaModel)
  (v1 : seq (R M))
  (v2 : seq {y : (R M) & 
            {bs : seq (R M) & 
            (forall i : {m | m < length bs}, { r : R M | lt M r (lnth bs i) }) -> { r : R M | lt M r y }
            }})
  (s : @RingTerm [seq length (projT1 (projT2 i)) | i <- v2] (length v1)) :
  option (R M).
  move:s; elim.
  - move=> idx; exact (Some (lnth (in_tuple v1) idx)).
  - move=> idx _ IH.
    rewrite map_lnth in IH.
    destruct (lnth _ _) as [y[bs f]]; simpl in IH.
    assert (forall i : {m : nat | m < length bs}, option {r : R M | lt M r (lnth bs i)}).
    * move=> i.
      apply (fun x => obind x (IH i)).
      intro r.
      destruct (lt_total M r (lnth bs i)).
      + apply Some; exists r; assumption.
      + exact None.
    clear IH.
    apply OptionArgs in X.
    apply (fun x => obind x X); clear X.
    move=> x.
    apply f in x.
    exact (Some (` x)).
  - exact (Some (-1)%R).
  - exact (Some 1%R).
  - exact (Some 0%R).
  - move=> _ r1 _ r2; exact (obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) r2) r1).
  - move=> _ r1 _ r2; exact (obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) r2) r1).
Defined.

(*
Definition Ring_Denote (M : SecondOrderFormulaModel)
  (v1 : seq (R M))
  (v2 : seq {y : (R M) & 
            {bs : seq (R M) & 
            (forall i : {m | m < length bs}, { r : R M | lt M r (lnth bs i) }) -> { r : R M | lt M r y }
            }})
  (s : @RingTerm [seq length (projT1 (projT2 i)) | i <- v2] (length v1)) :
  option (R M) :=
  match r with
  | RingVar m => Some (lnth v1 m)
  | RingFun i f => RingFun (i.+1) (fun x => RingTermSOQuote (f x))
  | RingMinusOne => Some (-1)%R
  | RingPlusOne => Some 1%R
  | RingZero => Some 0%R
  | RingPlus r1 r2 => (Ring_Denote M v1 v2 r1) + (Ring_Denote M v1 v2 r2)
  | RingTimes r1 r2 => (Ring_Denote M v1 v2 r1) * (Ring_Denote M v1 v2 r2)
  end.
*)

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
