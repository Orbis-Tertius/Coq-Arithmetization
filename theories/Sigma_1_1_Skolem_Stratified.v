From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import Program.

Section Sigma_1_1_Skolem.

Definition SOctx := seq nat.
Definition FOctx := nat.

Inductive SkolemRingTerm {soctx : SOctx} {uni exi : FOctx} : Type :=
| SkolemRingUniVar : {m : nat | m < uni} -> SkolemRingTerm
| SkolemRingExiVar : {m : nat | m < exi} -> SkolemRingTerm
| SkolemRingFun : forall (i : {m : nat | m < length soctx}),
            ({m : nat | m < lnth soctx i} -> SkolemRingTerm) ->
            SkolemRingTerm
| SkolemRingMinusOne : SkolemRingTerm
| SkolemRingPlusOne : SkolemRingTerm
| SkolemRingZero : SkolemRingTerm
| SkolemRingPlus : SkolemRingTerm -> SkolemRingTerm -> SkolemRingTerm
| SkolemRingTimes : SkolemRingTerm -> SkolemRingTerm -> SkolemRingTerm
| SkolemRingInd : SkolemRingTerm -> SkolemRingTerm -> SkolemRingTerm.

Inductive SkolemPolyTerm {uni exi : FOctx} : Type :=
| SkolemPolyUniVar : {m : nat | m < uni} -> SkolemPolyTerm
| SkolemPolyExiVar : {m : nat | m < exi} -> SkolemPolyTerm
| SkolemPolyMinusOne : SkolemPolyTerm
| SkolemPolyPlusOne : SkolemPolyTerm
| SkolemPolyZero : SkolemPolyTerm
| SkolemPolyPlus : SkolemPolyTerm -> SkolemPolyTerm -> SkolemPolyTerm
| SkolemPolyTimes : SkolemPolyTerm -> SkolemPolyTerm -> SkolemPolyTerm.

Fixpoint SkolemPoly_SkolemRing {soctx : SOctx} {uni exi : FOctx}
  (r : @SkolemPolyTerm uni exi) : @SkolemRingTerm soctx uni exi :=
  match r with
  | SkolemPolyUniVar m => SkolemRingUniVar m
  | SkolemPolyExiVar m => SkolemRingExiVar m
  | SkolemPolyMinusOne => SkolemRingMinusOne
  | SkolemPolyPlusOne => SkolemRingPlusOne
  | SkolemPolyZero => SkolemRingZero
  | SkolemPolyPlus r1 r2 => SkolemRingPlus (SkolemPoly_SkolemRing r1) (SkolemPoly_SkolemRing r2)
  | SkolemPolyTimes r1 r2 => SkolemRingTimes (SkolemPoly_SkolemRing r1) (SkolemPoly_SkolemRing r2)
  end.

Inductive SkolemZerothOrderFormula {soctx : SOctx} {uni exi : FOctx} : Type :=
| SkolemZOTrue : SkolemZerothOrderFormula
| SkolemZOFalse : SkolemZerothOrderFormula
| SkolemZONot : SkolemZerothOrderFormula -> SkolemZerothOrderFormula
| SkolemZOAnd : SkolemZerothOrderFormula ->
                SkolemZerothOrderFormula ->
                SkolemZerothOrderFormula
| SkolemZOOr : SkolemZerothOrderFormula ->
               SkolemZerothOrderFormula ->
               SkolemZerothOrderFormula
| SkolemZOImp : SkolemZerothOrderFormula ->
                SkolemZerothOrderFormula ->
                SkolemZerothOrderFormula
| SkolemZOEq : @SkolemRingTerm soctx uni exi -> 
               @SkolemRingTerm soctx uni exi ->
               SkolemZerothOrderFormula.

Inductive SkolemFirstOrderFormula {soctx : SOctx} {uni exi : FOctx} : Type :=
| SkolemZO : @SkolemZerothOrderFormula soctx uni exi -> SkolemFirstOrderFormula
| SkolemFOForall : @SkolemPolyTerm uni exi -> SkolemFirstOrderFormula (uni := uni.+1) -> SkolemFirstOrderFormula. 

Inductive SkolemSecondOrderFormula {soctx : SOctx} {uni exi : FOctx} : Type :=
| SkolemFO : @SkolemFirstOrderFormula soctx uni exi -> SkolemSecondOrderFormula
| SkolemSOExists : forall (y : @SkolemPolyTerm uni exi) (bs : seq (@SkolemPolyTerm uni exi)), 
                    SkolemSecondOrderFormula (soctx := length bs :: soctx) ->
                    SkolemSecondOrderFormula.

End Sigma_1_1_Skolem.



Section Sigma_1_1_Skolem_Denotation.

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
Program Fixpoint SkolemRing_Denote (M : Sigma11Model)
  (uv : seq (R M))
  (sf : seq ((length uv).-tuple (R M) -> R M))
  (v2 : seq {y : (R M) & 
            {bs : seq (R M) & 
            (forall i : {m | m < length bs}, { r : R M | lt M r (lnth bs i) }) -> { r : R M | lt M r y }
            }})
  (r : @SkolemRingTerm [seq length (projT1 (projT2 i)) | i <- v2] (length uv) (length sf)) :
  option (R M) :=
  match r with
  | SkolemRingUniVar m => Some (lnth uv m)
  | SkolemRingExiVar m => Some (lnth sf m (in_tuple uv))
  | SkolemRingFun i t => Rin_Denot_con M uv v2 i (fun x => SkolemRing_Denote M uv sf v2 (t x))
  | SkolemRingMinusOne => Some (-1)%R
  | SkolemRingPlusOne => Some 1%R
  | SkolemRingZero => Some 0%R
  | SkolemRingPlus r1 r2 => 
    (obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) (SkolemRing_Denote M uv sf v2 r2)) (SkolemRing_Denote M uv sf v2 r1))
  | SkolemRingTimes r1 r2 => 
    (obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) (SkolemRing_Denote M uv sf v2 r2)) (SkolemRing_Denote M uv sf v2 r1))
  | SkolemRingInd r1 r2 => 
    (obind (fun r1 => obind (fun r2 => 
      match lt_total M r1 r2 with
      | inl _ => Some 1%R
      | inr _ => Some 0%R
      end) (SkolemRing_Denote M uv sf v2 r2)) (SkolemRing_Denote M uv sf v2 r1))
  end.


Program Fixpoint Default_Extend {T} {n} {r} (d : T) (s : n.-tuple T) : (n + r).-tuple T :=
  match r with
  | 0 => s
  | r.+1 => cons_tuple d (Default_Extend (r := r) d s)
  end.
Next Obligation.
  hauto use: addn1, addSnnS inv: nat.
Qed.
Next Obligation.
  hauto use: addn1, addSnnS inv: nat.
Qed.

(*Interpreting a ring term with free variables as a function from ring elems. and functions. *)
Program Fixpoint SkolemPoly_Denote (M : Sigma11Model)
  (uv : seq (R M))
  {d} (sf : seq ((length uv + d).-tuple (R M) -> R M))
  (r : @SkolemPolyTerm (length uv) (length sf)) : R M :=
  match r with
  | SkolemPolyUniVar m => lnth uv m
  | SkolemPolyExiVar m => lnth sf m (Default_Extend 0%R (in_tuple uv))
  | SkolemPolyMinusOne => (-1)%R
  | SkolemPolyPlusOne => 1%R
  | SkolemPolyZero => 0%R
  | SkolemPolyPlus r1 r2 => SkolemPoly_Denote M uv sf r2 + SkolemPoly_Denote M uv sf r1
  | SkolemPolyTimes r1 r2 => SkolemPoly_Denote M uv sf r2 * SkolemPoly_Denote M uv sf r1
  end.

Fixpoint ZerothOrder_Denote (M : Sigma11Model) 
  (v1 : seq (R M))
  (v2 : seq {y : (R M) & 
            {bs : seq (R M) & 
            (forall i : {m | m < length bs}, { r : R M | lt M r (lnth bs i) }) -> { r : R M | lt M r y }
            }})
  (f : @SkolemZerothOrderFormula [seq length (projT1 (projT2 i)) | i <- v2] (length v1)) : Prop :=
  match f with
  | SkolemZOTrue => true
  | SkolemZOFalse => false
  | SkolemZONot f => not (ZerothOrder_Denote M v1 v2 f)
  | SkolemZOAnd f1 f2 => (ZerothOrder_Denote M v1 v2 f1) /\ (ZerothOrder_Denote M v1 v2 f2)
  | SkolemZOOr f1 f2 => (ZerothOrder_Denote M v1 v2 f1) \/ (ZerothOrder_Denote M v1 v2 f2)
  | SkolemZOImp f1 f2 => (ZerothOrder_Denote M v1 v2 f1) -> (ZerothOrder_Denote M v1 v2 f2)
  | SkolemZOEq r1 r2 => 
    match SkolemRing_Denote M v1 v2 r1 with
    | None => false
    | Some r1 =>
      match SkolemRing_Denote M v1 v2 r2 with
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
  (f : @SkolemFirstOrderFormula [seq length (projT1 (projT2 i)) | i <- v2] (length v1)) : Prop :=
  match f with
  | SkolemZO z => ZerothOrder_Denote M v1 v2 z
  | FOExists p f => 
    exists (r : R M), 
      lt M r (SkolemPoly_Denote M v1 p) /\
      FirstOrder_Denote M (r :: v1) v2 f
  | FOForall p f =>
    forall (r : R M), 
      lt M r (SkolemPoly_Denote M v1 p) ->
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
  (f : @SkolemSecondOrderFormula [seq length (projT1 (projT2 i)) | i <- v2] (length v1)) : Prop :=
  match f with
  | FO f => FirstOrder_Denote M v1 v2 f
  | SOExists y bs f =>
    let y' := SkolemPoly_Denote M v1 y in
    let bs' := [seq SkolemPoly_Denote M v1 i | i <- bs] in
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
