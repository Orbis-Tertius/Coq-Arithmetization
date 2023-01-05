From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import Program.

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
| RingTimes : RingTerm -> RingTerm -> RingTerm
| RingInd : RingTerm -> RingTerm -> RingTerm.

Inductive PolyTerm {foctx : FOctx} : Type :=
| PolyVar : {m : nat | m < foctx} -> PolyTerm
| PolyMinusOne : PolyTerm
| PolyPlusOne : PolyTerm
| PolyZero : PolyTerm
| PolyPlus : PolyTerm -> PolyTerm -> PolyTerm
| PolyTimes : PolyTerm -> PolyTerm -> PolyTerm.

Fixpoint Poly_Ring {soctx : SOctx} {foctx : FOctx} 
  (r : @PolyTerm foctx) : @RingTerm soctx foctx :=
  match r with
  | PolyVar m => RingVar m
  | PolyMinusOne => RingMinusOne
  | PolyPlusOne => RingPlusOne
  | PolyZero => RingZero
  | PolyPlus r1 r2 => RingPlus (Poly_Ring r1) (Poly_Ring r2)
  | PolyTimes r1 r2 => RingTimes (Poly_Ring r1) (Poly_Ring r2)
  end.

Program Fixpoint RingTermFOQuote {soctx} {foctx}
  (r : @RingTerm soctx foctx) : @RingTerm soctx (foctx.+1) :=
  match r with
  | RingVar m => RingVar (m.+1)
  | RingFun i f => RingFun i (fun x => RingTermFOQuote (f x))
  | RingMinusOne => RingMinusOne
  | RingPlusOne => RingPlusOne
  | RingZero => RingZero
  | RingPlus r1 r2 => RingPlus (RingTermFOQuote r1) (RingTermFOQuote r2)
  | RingTimes r1 r2 => RingTimes (RingTermFOQuote r1) (RingTermFOQuote r2)
  | RingInd r1 r2 => RingInd (RingTermFOQuote r1) (RingTermFOQuote r2)
  end.

Program Fixpoint PolyTermFOQuote {foctx}
  (r : @PolyTerm foctx) : @PolyTerm (foctx.+1) :=
  match r with
  | PolyVar m => PolyVar (m.+1)
  | PolyMinusOne => PolyMinusOne
  | PolyPlusOne => PolyPlusOne
  | PolyZero => PolyZero
  | PolyPlus r1 r2 => PolyPlus (PolyTermFOQuote r1) (PolyTermFOQuote r2)
  | PolyTimes r1 r2 => PolyTimes (PolyTermFOQuote r1) (PolyTermFOQuote r2)
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
  | RingInd r1 r2 => RingInd (RingTermSOQuote r1) (RingTermSOQuote r2)
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
  | RingInd r1 r2 => RingInd (RingTermFOSubst i t r1) (RingTermFOSubst i t r2)
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

Program Fixpoint PolyTermFOSubst {foctx : FOctx}
  (i : {m : nat | m < foctx})
  (t : @PolyTerm (foctx.-1)) (r : @PolyTerm foctx) :
  @PolyTerm (foctx.-1) :=
  match r with
  | PolyVar m => 
    match (Nat.compare i m) with
    | Eq => t
    | Lt => PolyVar (m.-1)
    | Gt => PolyVar m
    end
  | PolyMinusOne => PolyMinusOne
  | PolyPlusOne => PolyPlusOne
  | PolyZero => PolyZero
  | PolyPlus r1 r2 => PolyPlus (PolyTermFOSubst i t r1) (PolyTermFOSubst i t r2)
  | PolyTimes r1 r2 => PolyTimes (PolyTermFOSubst i t r1) (PolyTermFOSubst i t r2)
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
Theorem Ring_FO_Unquote {soctx : SOctx} {foctx : FOctx} :
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

(*Substitution acts as an unquote when applied after quoting.*)
Theorem Poly_FO_Unquote {foctx : FOctx} :
  forall (x : @PolyTerm foctx)
         (e : @PolyTerm foctx)
         (H : 0 < foctx.+1),
  PolyTermFOSubst (exist _ 0 H) x (PolyTermFOQuote e) = e.
Proof.
  move=> x; elim; try hauto q:on.
  - move=> [i lti] H.
    cbn; do 2 f_equal; apply proof_irrelevance.
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
  | RingInd r1 r2 => RingInd (RingTermSOSubst i f r1) (RingTermSOSubst i f r2)
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
| FOExists : @PolyTerm foctx -> FirstOrderFormula (foctx := foctx.+1) -> FirstOrderFormula
| FOForall : @PolyTerm foctx -> FirstOrderFormula (foctx := foctx.+1) -> FirstOrderFormula. 

Program Fixpoint FirstOrderFormulaFOSubst {soctx : SOctx} {foctx : FOctx}
  (i : {n : nat | n < foctx}) (t : @PolyTerm foctx.-1)
  (s : @FirstOrderFormula soctx foctx) : @FirstOrderFormula soctx foctx.-1 :=
  match s with
  | ZO z => ZO (ZerothOrderFormulaFOSubst i (Poly_Ring t) z)
  | FOExists b f => FOExists (PolyTermFOSubst i t b)
                             (FirstOrderFormulaFOSubst (i.+1) (PolyTermFOQuote t) f)
  | FOForall b f => FOForall (PolyTermFOSubst i t b)
                             (FirstOrderFormulaFOSubst (i.+1) (PolyTermFOQuote t) f)
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
  | FOExists b o => FOExists b
                             (FirstOrderFormulaSOSubst i (fun t => RingTermFOQuote (f (fun x => RingTermFOSubst 0 RingZero (t x)))) o)
  | FOForall b o => FOForall b
                             (FirstOrderFormulaSOSubst i (fun t => RingTermFOQuote (f (fun x => RingTermFOSubst 0 RingZero (t x)))) o)
  end.

Inductive SecondOrderFormula {soctx : SOctx} {foctx : FOctx} : Type :=
| FO : @FirstOrderFormula soctx foctx -> 
       SecondOrderFormula
| SOExists : forall (y : @PolyTerm foctx) (bs : seq (@PolyTerm foctx)), 
              SecondOrderFormula (soctx := length bs :: soctx) ->
              SecondOrderFormula.

Program Fixpoint SecondOrderFormulaFOSubst {soctx : SOctx} {foctx : FOctx}
  (i : {n : nat | n < foctx}) (t : @PolyTerm foctx.-1)
  (s : @SecondOrderFormula soctx foctx) : @SecondOrderFormula soctx foctx.-1 :=
  match s with
  | FO f => FO (FirstOrderFormulaFOSubst i t f)
  | SOExists y bs f => 
    SOExists (PolyTermFOSubst i t y) 
             [ seq (PolyTermFOSubst i t r) | r <- bs ]
             (SecondOrderFormulaFOSubst i t f)
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
    SOExists y bs
      (SecondOrderFormulaSOSubst (i.+1 : {m | m < length (length bs :: soctx)})
        (fun t => RingTermSOQuote (f (fun x => RingTermSOSubst 0 (fun=> RingZero) (t x))))
        o)
  end.
Next Obligation.
  unfold lnth; unfold lnth in H.
  by do 2 rewrite (tnth_nth 0) in H *.
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

(*How to write this nicer?*)
Definition Rin_Denot_con (M : Sigma11Model)
  (v1 : seq (R M))
  (v2 : seq {y : (R M) & 
            {bs : seq (R M) & 
            (forall i : {m | m < length bs}, { r : R M | lt M r (lnth bs i) }) -> { r : R M | lt M r y }
            }}) : 
  forall i : {m : nat | m < length [seq length (projT1 (projT2 i)) | i <- v2]},
  ({m : nat | m < lnth [seq length (projT1 (projT2 i0)) | i0 <- v2] i} -> option (R M))
  -> option (R M).
    move=> idx IH.
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
    assert (forall i : {m : nat | m < length bs},
    option {r : R M | lt M r (nth 0%R bs (` i))}) as X'.
    move=>i.
    replace {r : R M | lt M r (nth 0%R bs (` i))}
       with {r : R M | lt M r (lnth bs i)}.
    apply X.
    f_equal.
    apply functional_extensionality=> x.
    f_equal.
    unfold lnth; rewrite (tnth_nth 0%R).
    by destruct i. 
    clear X.
    apply (OptionArgs (B := fun x => {r : R M | lt M r (nth 0%R bs x)})) in X'.
    apply (fun x => obind x X'); clear X'.
    move=> x.
    assert (forall i : {m : nat | m < length bs}, {r : R M | lt M r (lnth bs i)}) as x'.
    move=> i.
    replace {r : R M | lt M r (lnth bs i)} with {r : R M | lt M r (nth 0%R bs (` i))}.
    apply x.
    f_equal; apply functional_extensionality=> x0; f_equal.
    unfold lnth; rewrite (tnth_nth 0%R); by destruct i. clear x.
    apply f in x'.
    exact (Some (` x')).
Defined.

(*Interpreting a ring term with free variables as a function from ring elems. and functions. *)
Program Fixpoint Ring_Denote (M : Sigma11Model)
  (v1 : seq (R M))
  (v2 : seq {y : (R M) & 
            {bs : seq (R M) & 
            (forall i : {m | m < length bs}, { r : R M | lt M r (lnth bs i) }) -> { r : R M | lt M r y }
            }})
  (r : @RingTerm [seq length (projT1 (projT2 i)) | i <- v2] (length v1)) :
  option (R M) :=
  match r with
  | RingVar m => Some (lnth v1 m)
  | RingFun i t => Rin_Denot_con M v1 v2 i (fun x => Ring_Denote M v1 v2 (t x))
  | RingMinusOne => Some (-1)%R
  | RingPlusOne => Some 1%R
  | RingZero => Some 0%R
  | RingPlus r1 r2 => 
    (obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) (Ring_Denote M v1 v2 r2)) (Ring_Denote M v1 v2 r1))
  | RingTimes r1 r2 => 
    (obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) (Ring_Denote M v1 v2 r2)) (Ring_Denote M v1 v2 r1))
  | RingInd r1 r2 => 
    (obind (fun r1 => obind (fun r2 => 
      match lt_total M r1 r2 with
      | inl _ => Some 1%R
      | inr _ => Some 0%R
      end) (Ring_Denote M v1 v2 r2)) (Ring_Denote M v1 v2 r1))
  end.

(*Interpreting a ring term with free variables as a function from ring elems. and functions. *)
Program Fixpoint Poly_Denote (M : Sigma11Model)
  (v1 : seq (R M))
  (r : @PolyTerm (length v1)) : R M :=
  match r with
  | PolyVar m => lnth v1 m
  | PolyMinusOne => (-1)%R
  | PolyPlusOne => 1%R
  | PolyZero => 0%R
  | PolyPlus r1 r2 => Poly_Denote M v1 r2 + Poly_Denote M v1 r1
  | PolyTimes r1 r2 => Poly_Denote M v1 r2 * Poly_Denote M v1 r1
  end.

Fixpoint ZerothOrder_Denote (M : Sigma11Model) 
  (v1 : seq (R M))
  (v2 : seq {y : (R M) & 
            {bs : seq (R M) & 
            (forall i : {m | m < length bs}, { r : R M | lt M r (lnth bs i) }) -> { r : R M | lt M r y }
            }})
  (f : @ZerothOrderFormula [seq length (projT1 (projT2 i)) | i <- v2] (length v1)) : Prop :=
  match f with
  | ZOTrue => true
  | ZOFalse => false
  | ZONot f => not (ZerothOrder_Denote M v1 v2 f)
  | ZOAnd f1 f2 => (ZerothOrder_Denote M v1 v2 f1) /\ (ZerothOrder_Denote M v1 v2 f2)
  | ZOOr f1 f2 => (ZerothOrder_Denote M v1 v2 f1) \/ (ZerothOrder_Denote M v1 v2 f2)
  | ZOImp f1 f2 => (ZerothOrder_Denote M v1 v2 f1) -> (ZerothOrder_Denote M v1 v2 f2)
  | ZOEq r1 r2 => 
    match Ring_Denote M v1 v2 r1 with
    | None => false
    | Some r1 =>
      match Ring_Denote M v1 v2 r2 with
      | None => false
      | Some r2 => r1 = r2
      end
    end
  end.

Fixpoint FirstOrder_Denote (M : Sigma11Model) 
  (v1 : seq (R M))
  (v2 : seq {y : (R M) & 
            {bs : seq (R M) & 
            (forall i : {m | m < length bs}, { r : R M | lt M r (lnth bs i) }) -> { r : R M | lt M r y }
            }})
  (f : @FirstOrderFormula [seq length (projT1 (projT2 i)) | i <- v2] (length v1)) : Prop :=
  match f with
  | ZO z => ZerothOrder_Denote M v1 v2 z
  | FOExists p f => 
    exists (r : R M), 
      lt M r (Poly_Denote M v1 p) /\
      FirstOrder_Denote M (r :: v1) v2 f
  | FOForall p f =>
    forall (r : R M), 
      lt M r (Poly_Denote M v1 p) ->
      FirstOrder_Denote M (r :: v1) v2 f
  end.

Fixpoint otraverse {T} (s : seq (option T)) : option (seq T) :=
  match s with
  | [::] => Some [::]
  | (x :: xs) =>
    obind (fun x => obind (fun xs => Some (x :: xs)) (otraverse xs)) x
  end.

(*Interpreting a ring term with free variables as a function from ring elems. and functions. *)
Program Fixpoint SecondOrder_Denote (M : Sigma11Model) 
  (v1 : seq (R M))
  (v2 : seq {y : (R M) & 
            {bs : seq (R M) & 
            (forall i : {m | m < length bs}, { r : R M | lt M r (lnth bs i) }) -> { r : R M | lt M r y }
            }})
  (f : @SecondOrderFormula [seq length (projT1 (projT2 i)) | i <- v2] (length v1)) : Prop :=
  match f with
  | FO f => FirstOrder_Denote M v1 v2 f
  | SOExists y bs f =>
    let y' := Poly_Denote M v1 y in
    let bs' := [seq Poly_Denote M v1 i | i <- bs] in
    exists rf : (forall i : {m | m < length bs}, { r : R M | lt M r (lnth bs' i) }) 
              -> { r : R M | lt M r y' },
    SecondOrder_Denote M v1 
    (existT _ y' (existT _ bs' rf) :: v2) f
  end.
Next Obligation.
  by rewrite map_length.
Qed.
Next Obligation.
  by rewrite map_length.
Qed.

End Sigma_1_1_Denotation.
