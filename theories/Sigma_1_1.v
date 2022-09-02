From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import Program.

Section Sigma_1_1_Internal.

Definition FreeFOctx := nat.
Definition ExiFOctx := nat.
Definition UniFOctx := nat.
Definition FreeSOctx := seq nat.
Definition ExiSOctx := seq nat.
Record Ctx := mkCtx
  { freeFOctx : FreeFOctx
  ; exiFOctx : ExiFOctx
  ; uniFOctx : UniFOctx
  ; freeSOctx : FreeSOctx
  ; exiSOctx : ExiSOctx
  }.
Definition updateExiFO (new : ExiFOctx) (ctx : Ctx) : Ctx := 
  match ctx with
  | {| freeFOctx := freeFOctx; exiFOctx := exiFOctx; uniFOctx := uniFOctx; freeSOctx := freeSOctx; exiSOctx := exiSOctx |} =>
    {| freeFOctx := freeFOctx; exiFOctx := new; uniFOctx := uniFOctx; freeSOctx := freeSOctx; exiSOctx := exiSOctx |}
  end.
Definition updateUniFO (new : UniFOctx) (ctx : Ctx) : Ctx := 
  match ctx with
  | {| freeFOctx := freeFOctx; exiFOctx := exiFOctx; uniFOctx := uniFOctx; freeSOctx := freeSOctx; exiSOctx := exiSOctx |} =>
    {| freeFOctx := freeFOctx; exiFOctx := exiFOctx; uniFOctx := new; freeSOctx := freeSOctx; exiSOctx := exiSOctx |}
  end.
Definition updateExiSO (new : ExiSOctx) (ctx : Ctx) : Ctx := 
  match ctx with
  | {| freeFOctx := freeFOctx; exiFOctx := exiFOctx; uniFOctx := uniFOctx; freeSOctx := freeSOctx; exiSOctx := exiSOctx |} =>
    {| freeFOctx := freeFOctx; exiFOctx := exiFOctx; uniFOctx := uniFOctx; freeSOctx := freeSOctx; exiSOctx := new |}
  end.

Inductive RingTerm {ctx : Ctx} : Type :=
| RingFVar : {m : nat | m < freeFOctx ctx} -> RingTerm
| RingEVar : {m : nat | m < exiFOctx ctx} -> RingTerm
| RingUVar : {m : nat | m < uniFOctx ctx} -> RingTerm
| RingFFun : forall (i : {m : nat | m < length (freeSOctx ctx)}),
             ({m : nat | m < lnth (freeSOctx ctx) i} -> RingTerm) ->
             RingTerm
| RingEFun : forall (i : {m : nat | m < length (exiSOctx ctx)}),
             ({m : nat | m < lnth (exiSOctx ctx) i} -> RingTerm) ->
             RingTerm
| RingMinusOne : RingTerm
| RingPlusOne : RingTerm
| RingZero : RingTerm
| RingPlus : RingTerm -> RingTerm -> RingTerm
| RingTimes : RingTerm -> RingTerm -> RingTerm
| RingInd : RingTerm -> RingTerm -> RingTerm.

Inductive PolyTerm {ctx : Ctx} : Type :=
| PolyFVar : {m : nat | m < freeFOctx ctx} -> PolyTerm
| PolyEVar : {m : nat | m < exiFOctx ctx} -> PolyTerm
| PolyUVar : {m : nat | m < uniFOctx ctx} -> PolyTerm
| PolyFFun : forall (i : {m : nat | m < length (freeSOctx ctx)}),
             ({m : nat | m < lnth (freeSOctx ctx) i} -> PolyTerm) ->
             PolyTerm
| PolyEFun : forall (i : {m : nat | m < length (exiSOctx ctx)}),
             ({m : nat | m < lnth (exiSOctx ctx) i} -> PolyTerm) ->
             PolyTerm
| PolyMinusOne : PolyTerm
| PolyPlusOne : PolyTerm
| PolyZero : PolyTerm
| PolyPlus : PolyTerm -> PolyTerm -> PolyTerm
| PolyTimes : PolyTerm -> PolyTerm -> PolyTerm.

Fixpoint Poly_Ring {ctx : Ctx}
  (r : @PolyTerm ctx) : @RingTerm ctx :=
  match r with
  | PolyFVar m => RingFVar m
  | PolyEVar m => RingEVar m
  | PolyUVar m => RingUVar m
  | PolyFFun i t => RingFFun i (fun j => Poly_Ring (t j))
  | PolyEFun i t => RingEFun i (fun j => Poly_Ring (t j))
  | PolyMinusOne => RingMinusOne
  | PolyPlusOne => RingPlusOne
  | PolyZero => RingZero
  | PolyPlus r1 r2 => RingPlus (Poly_Ring r1) (Poly_Ring r2)
  | PolyTimes r1 r2 => RingTimes (Poly_Ring r1) (Poly_Ring r2)
  end.

Inductive ZerothOrderFormula {ctx : Ctx} : Type :=
| ZOTrue : ZerothOrderFormula
| ZOFalse : ZerothOrderFormula
| ZONot : ZerothOrderFormula -> ZerothOrderFormula
| ZOAnd : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOOr : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOImp : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOEq : @RingTerm ctx -> @RingTerm ctx -> ZerothOrderFormula.

Inductive FirstOrderFormula {ctx : Ctx} : Type :=
| ZO : @ZerothOrderFormula ctx -> FirstOrderFormula
| FOExists : @PolyTerm ctx -> FirstOrderFormula (ctx := updateExiFO ((exiFOctx ctx).+1) ctx) -> FirstOrderFormula
| FOForall : @PolyTerm ctx -> FirstOrderFormula (ctx := updateUniFO ((uniFOctx ctx).+1) ctx) -> FirstOrderFormula.

Inductive SecondOrderFormula {ctx : Ctx} : Type :=
| FO : @FirstOrderFormula ctx -> SecondOrderFormula
| SOExists : forall (y : @PolyTerm ctx) (bs : seq (@PolyTerm ctx)), 
             SecondOrderFormula (ctx := updateExiSO (length bs :: exiSOctx ctx) ctx) ->
             SecondOrderFormula.

End Sigma_1_1_Internal.



Section Sigma_1_1_Denotation.

Definition emptyTuple {A} : |[0]| -> A. fcrush. Defined.
Program Fixpoint option_tuple {A} {l : nat} (t : {n : nat | n < l} -> option A) : option ({n : nat | n < l} -> A) := 
  match l with
  | 0 => Some emptyTuple
  | m.+1 =>
    let most : {n : nat | n < m} -> option A := fun x => t x in
    let r : option ({n : nat | n < m} -> A) := option_tuple most in
    let last : option A := t m in
    obind (fun last => obind (fun r => Some (
      fun x : {n : nat | n < m.+1} => 
      (if x < m as b return x < m = b -> A 
       then (fun _ => r (x : {n : nat | n < m}) )
       else (fun _ => last)) (erefl _)
    )) r) last
  end.

Program Fixpoint Ring_Denote (M : Sigma11Model)
  (freeV : seq (R M))
  (exiV : seq (R M))
  (uniV : seq (R M))
  (freeF : seq {n : nat & (({m : nat | m < n} -> R M) -> option (R M))})
  (exiF : seq {n : nat & (({m : nat | m < n} -> R M) -> option (R M))})
  (r : @RingTerm {| freeFOctx := length freeV; exiFOctx := length exiV; uniFOctx := length uniV
                 ; freeSOctx := map (fun x => projT1 x) freeF; exiSOctx := map (fun x => projT1 x) exiF |}) : 
  option (R M) :=
  match r with
  | RingFVar m => Some (lnth freeV m)
  | RingEVar m => Some (lnth exiV m)
  | RingUVar m => Some (lnth uniV m)
  | RingFFun i t => 
    let t' : {m : nat | m < projT1 (lnth freeF i)} -> option (R M) 
           := fun x => Ring_Denote M freeV exiV uniV freeF exiF (t x) in
    let t'' : option ({m : nat | m < projT1 (lnth freeF i)} -> (R M))
           := option_tuple t' in
    obind (fun t => projT2 (lnth freeF i) t) t''
  | RingEFun i t => 
    let t' : {m : nat | m < projT1 (lnth exiF i)} -> option (R M) 
           := fun x => Ring_Denote M freeV exiV uniV freeF exiF (t x) in
    let t'' : option ({m : nat | m < projT1 (lnth exiF i)} -> (R M))
           := option_tuple t' in
    obind (fun t => projT2 (lnth exiF i) t) t''
  | RingMinusOne => Some (-1)%R
  | RingPlusOne => Some 1%R
  | RingZero => Some 0%R
  | RingPlus r1 r2 => 
    let d1 := Ring_Denote M freeV exiV uniV freeF exiF r1 in
    let d2 := Ring_Denote M freeV exiV uniV freeF exiF r2 in
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) d2) d1
  | RingTimes r1 r2 => 
    let d1 := Ring_Denote M freeV exiV uniV freeF exiF r1 in
    let d2 := Ring_Denote M freeV exiV uniV freeF exiF r2 in
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) d2) d1
  | RingInd r1 r2 => 
    let d1 := Ring_Denote M freeV exiV uniV freeF exiF r1 in
    let d2 := Ring_Denote M freeV exiV uniV freeF exiF r2 in
    (obind (fun r1 => obind (fun r2 => 
      match lt_total M r1 r2 with
      | inl _ => Some 1%R
      | inr _ => Some 0%R
      end) d2) d1)
  end.
Next Obligation. by clear t; rewrite map_length in H. Qed.
Next Obligation.
  rewrite map_lnth.
  remember (Ring_Denote_obligation_1 _ _ _ _ _ _ _ _ _ _) as D; clear HeqD.
  replace (lnth _ _) with (lnth freeF (exist _ i D));trivial.
  clear H; f_equal.
  destruct (map_length _ _).
  by apply subset_eq_compat.
Qed.
Next Obligation. by clear t; rewrite map_length in H. Qed.
Next Obligation.
  rewrite map_lnth.
  remember (Ring_Denote_obligation_3 _ _ _ _ _ _ _ _ _ _) as D; clear HeqD.
  replace (lnth _ _) with (lnth exiF (exist _ i D));trivial.
  clear H; f_equal.
  destruct (map_length _ _).
  by apply subset_eq_compat.
Qed.

Definition Poly_Denote (M : Sigma11Model)
  (freeV : seq (R M))
  (exiV : seq (R M))
  (uniV : seq (R M))
  (freeF : seq {n : nat & (({m : nat | m < n} -> R M) -> option (R M))})
  (exiF : seq {n : nat & (({m : nat | m < n} -> R M) -> option (R M))})
  (r : @PolyTerm {| freeFOctx := length freeV; exiFOctx := length exiV; uniFOctx := length uniV
                 ; freeSOctx := map (fun x => projT1 x) freeF; exiSOctx := map (fun x => projT1 x) exiF |}) : 
  option (R M) := @Ring_Denote M freeV exiV uniV freeF exiF (Poly_Ring r).

Fixpoint ZerothOrder_Denote (M : Sigma11Model) 
  (freeV : seq (R M))
  (exiV : seq (R M))
  (uniV : seq (R M))
  (freeF : seq {n : nat & (({m : nat | m < n} -> R M) -> option (R M))})
  (exiF : seq {n : nat & (({m : nat | m < n} -> R M) -> option (R M))})
  (f : @ZerothOrderFormula 
          {| freeFOctx := length freeV; exiFOctx := length exiV; uniFOctx := length uniV
          ; freeSOctx := map (fun x => projT1 x) freeF; exiSOctx := map (fun x => projT1 x) exiF |}) : Prop :=
  match f with
  | ZOTrue => true
  | ZOFalse => false
  | ZONot f => not (ZerothOrder_Denote M freeV exiV uniV freeF exiF f)
  | ZOAnd f1 f2 => (ZerothOrder_Denote M freeV exiV uniV freeF exiF f1) /\ (ZerothOrder_Denote M freeV exiV uniV freeF exiF f2)
  | ZOOr f1 f2 => (ZerothOrder_Denote M freeV exiV uniV freeF exiF f1) \/ (ZerothOrder_Denote M freeV exiV uniV freeF exiF f2)
  | ZOImp f1 f2 => (ZerothOrder_Denote M freeV exiV uniV freeF exiF f1) -> (ZerothOrder_Denote M freeV exiV uniV freeF exiF f2)
  | ZOEq r1 r2 => 
    match Ring_Denote M freeV exiV uniV freeF exiF r1 with
    | None => false
    | Some r1 =>
      match Ring_Denote M freeV exiV uniV freeF exiF r2 with
      | None => false
      | Some r2 => r1 = r2
      end
    end
  end.

Fixpoint FirstOrder_Denote (M : Sigma11Model) 
  (freeV : seq (R M))
  (exiV : seq (R M))
  (uniV : seq (R M))
  (freeF : seq {n : nat & (({m : nat | m < n} -> R M) -> option (R M))})
  (exiF : seq {n : nat & (({m : nat | m < n} -> R M) -> option (R M))})
  (f : @FirstOrderFormula 
          {| freeFOctx := length freeV; exiFOctx := length exiV; uniFOctx := length uniV
          ; freeSOctx := map (fun x => projT1 x) freeF; exiSOctx := map (fun x => projT1 x) exiF |}) : Prop :=
  match f with
  | ZO z => ZerothOrder_Denote M freeV exiV uniV freeF exiF z
  | FOExists p f => 
    let op := Poly_Denote M freeV exiV uniV freeF exiF p in
    match op with
    | None => False
    | Some p' => exists (r : R M), lt M r p' /\ FirstOrder_Denote M freeV (r :: exiV) uniV freeF exiF f
    end
  | FOForall p f =>
    let op := Poly_Denote M freeV exiV uniV freeF exiF p in
    match op with
    | None => False
    | Some p' => forall (r : R M),  lt M r p' -> FirstOrder_Denote M freeV exiV (r :: uniV) freeF exiF f
    end
  end.

Definition SO_Bound_Check (M : Sigma11Model) 
  (n : nat)
  (y : R M)
  (bs : {m : nat | m < n} -> R M)
  (f : ({m : nat | m < n} -> R M) -> option (R M)) : Prop :=
forall (ins : {m : nat | m < n} -> R M) (out : R M),
  f ins = Some out ->
  (forall x : {m : nat | m < n}, lt M (ins x) (bs x)) /\ lt M out y.

Fixpoint SecondOrder_Denote (M : Sigma11Model) 
  (freeV : seq (R M))
  (exiV : seq (R M))
  (uniV : seq (R M))
  (freeF : seq {n : nat & (({m : nat | m < n} -> R M) -> option (R M))})
  (exiF : seq {n : nat & (({m : nat | m < n} -> R M) -> option (R M))})
  (f : @SecondOrderFormula 
          {| freeFOctx := length freeV; exiFOctx := length exiV; uniFOctx := length uniV
          ; freeSOctx := map (fun x => projT1 x) freeF; exiSOctx := map (fun x => projT1 x) exiF |}) : Prop :=
  match f with
  | FO f => FirstOrder_Denote M freeV exiV uniV freeF exiF f
  | SOExists y bs f => 
    let y' : option (R M) := Poly_Denote M freeV exiV uniV freeF exiF y in
    let bs' : option ({m : nat | m < length bs} -> R M) := 
        option_tuple (fun m => Poly_Denote M freeV exiV uniV freeF exiF (lnth bs m)) in
    match y' with
    | None => false
    | Some y' =>
      match bs' with
      | None => false
      | Some bs' =>
        exists a : ({m : nat | m < length bs} -> R M) -> option (R M),
          SO_Bound_Check M (length bs) y' bs' a 
          /\ SecondOrder_Denote M freeV exiV uniV freeF (existT _ (length bs) a :: exiF) f
      end
    end
  end.

End Sigma_1_1_Denotation.
