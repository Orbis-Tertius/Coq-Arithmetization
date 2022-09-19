From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import CoqArith.Sigma_1_1.
Require Import Program.

Section NoQuantDef.

Record NoQuant {ctx} : Type :=
  mkNoQuant {
    nu : {s : |[exiV ctx]| -> { m : nat | m <= uniV ctx } | forall i j : |[exiV ctx]|, (` i) <= (` j) -> (` (s j)) <= (` (s i))};
    uniVBounds : |[uniV ctx]| -> @PolyTerm ctx;
    exiVBounds : |[exiV ctx]| -> @PolyTerm ctx;
    exiFOutputBounds : |[exiF ctx]| -> @PolyTerm ctx;
    exiFInputBounds : forall (i : |[exiF ctx]|), |[exiFA ctx i]| -> @PolyTerm ctx;
    formula : unit + @ZerothOrderFormula ctx
  }.

Record NoQuantInstance {ctx} {R : RingData} : Type :=
  mkNoQuantInstance { 
    freeVInst : |[freeV ctx]| -> T R;
    freeFInst : forall i : |[freeF ctx]|, (|[freeFA ctx i]| -> T R) -> option (T R);
  }.

Record NoQuantAdvice {ctx} {R : RingData} : Type :=
  mkNoQuantAdvice { 
    exiVAdv : |[exiV ctx]| -> (|[uniV ctx]| -> T R) -> T R;
    exiFAdv : forall i : |[exiF ctx]|, (|[exiFA ctx i]| -> T R) -> option (T R);
  }.

Definition indFun (R : RingData) (x y : T R) : T R := if lt_dec R x y then 1%R else 0%R.

Fixpoint NoQuantPolyDenotation {ctx} {R}
  (inst : @NoQuantInstance ctx R)
  (adv : @NoQuantAdvice ctx R)
  (p : @PolyTerm ctx) :
  (|[uniV ctx]| -> T R) -> option (T R) :=
  match p with
  | PolyFVar i => fun _ => Some (freeVInst inst i)
  | PolyEVar i => fun u => Some (exiVAdv adv i u)
  | PolyUVar i =>  fun u => Some (u i)
  | PolyFFun i t => fun u =>
    obind (fun t => freeFInst inst i t) (option_tuple (fun x => NoQuantPolyDenotation inst adv (t x) u))
  | PolyEFun i t => fun u =>
    obind (fun t => exiFAdv adv i t) (option_tuple (fun x => NoQuantPolyDenotation inst adv (t x) u))
  | PolyMinusOne => fun _ => Some (-1)%R
  | PolyPlusOne => fun _ => Some 1%R
  | PolyZero => fun _ => Some 0%R
  | PolyPlus p1 p2 => fun u =>
    let d1 := NoQuantPolyDenotation inst adv p1 u in
    let d2 := NoQuantPolyDenotation inst adv p2 u in
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) d2) d1
  | PolyTimes p1 p2 => fun u =>
    let r1 := NoQuantPolyDenotation inst adv p1 u in
    let r2 := NoQuantPolyDenotation inst adv p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) r2) r1
  | PolyInd p1 p2 => fun u =>
    let r1 := NoQuantPolyDenotation inst adv p1 u in
    let r2 := NoQuantPolyDenotation inst adv p2 u in 
    obind (fun r1 => obind (fun r2 => Some (indFun R r1 r2)) r2) r1
  end.

Program Fixpoint NoQuantPropDenotation {ctx} {R}
  (inst : @NoQuantInstance ctx R)
  (adv : @NoQuantAdvice ctx R)
  (p : @ZerothOrderFormula ctx) :
  (|[uniV ctx]| -> T R) -> Prop :=
  match p with
  | ZONot p => fun u => 
    let r := NoQuantPropDenotation inst adv p u in
    not r
  | ZOAnd p1 p2 => fun u => 
    let r1 := NoQuantPropDenotation inst adv p1 u in
    let r2 := NoQuantPropDenotation inst adv p2 u in
    r1 /\ r2
  | ZOOr p1 p2 => fun u => 
    let r1 := NoQuantPropDenotation inst adv p1 u in
    let r2 := NoQuantPropDenotation inst adv p2 u in
    r1 \/ r2
  | ZOImp p1 p2 => fun u => 
    let r1 := NoQuantPropDenotation inst adv p1 u in
    let r2 := NoQuantPropDenotation inst adv p2 u in
    r1 -> r2
  | ZOEq p1 p2 => fun u => 
    let r1 := NoQuantPolyDenotation inst adv p1 u in
    let r2 := NoQuantPolyDenotation inst adv p2 u in
    match r1 with
    | None => false
    | Some r1 =>
      match r2 with
      | None => false
      | Some r2 => r1 = r2
      end
    end
  end.

Definition UProp {ctx} {R}
  f (inst : @NoQuantInstance ctx R) (adv : NoQuantAdvice) 
  (t : |[uniV ctx]| -> T R) : Prop :=
  let ev i := NoQuantPolyDenotation inst adv (uniVBounds f i) in
  forall i, 
    match (ev i t) with
    | None => false
    | Some e => lt R (t i) e
    end.

Definition U {ctx} {R}
  f (inst : @NoQuantInstance ctx R) (adv : NoQuantAdvice) : Type 
  := { t : |[uniV ctx]| -> T R | UProp f inst adv t }.

Definition NoQuantFormulaCondition {ctx} {R}
  f (inst : @NoQuantInstance ctx R) (adv : NoQuantAdvice) : Prop :=
  exists p, formula f = inr p /\ forall u, NoQuantPropDenotation inst adv p u = true.

Definition NoQuantFOBoundCondition {ctx} {R}
  f (inst : @NoQuantInstance ctx R) (adv : NoQuantAdvice) : Prop :=
  forall u : U f inst adv, forall i : |[exiV ctx]|,
  let B := NoQuantPolyDenotation inst adv (exiVBounds f i) (` u) in
  match B with
  | None => false
  | Some B => lt R (exiVAdv adv i (` u)) B
  end.

(* Note: This covers both conditions 5 and 6 in the paper *)
Definition NoQuantSOBoundCondition {ctx} {R}
  f (inst : @NoQuantInstance ctx R) (adv : NoQuantAdvice) : Prop :=
  forall u : U f inst adv, forall i : |[exiF ctx]|,
  let B := NoQuantPolyDenotation inst adv (exiFOutputBounds f i) (` u) in
  let G (j : |[exiFA ctx i]|) := NoQuantPolyDenotation inst adv (exiFInputBounds f i j) (` u) in
  forall (t : |[exiFA ctx i]| -> T R) (out : T R),
  exiFAdv adv i t = Some out ->
  match B with
  | None => false
  | Some B => lt R out B /\ forall x,
    match G x with
    | None => false
    | Some Gx => lt R (t x) Gx
    end
  end.

Program Definition NoQuantExiStratCondition {ctx} {R}
  f (inst : @NoQuantInstance ctx R) (adv : @NoQuantAdvice ctx R) : Prop :=
  forall i : |[exiV ctx]|, forall m : |[nu f i]| -> T R,
  exists C, forall n : |[uniV ctx - nu f i]| -> T R,
  exiVAdv adv i (TupConcat m n) = C.
Next Obligation.
  destruct ((` (nu f)) (exist (fun n : nat => n < _) i H0)); simpl in *.
  replace (x0 + (uniV ctx - x0)) with (uniV ctx); auto.
  remember (uniV ctx) as U; clear HeqU H x n m H0 adv inst f i.
  sfirstorder use: subnKC.
Qed.

Definition NoQuantDenotation {ctx} {R} f (i : @NoQuantInstance ctx R) : Prop :=
  exists (a : NoQuantAdvice),
    NoQuantFormulaCondition f i a /\
    NoQuantFOBoundCondition f i a /\
    NoQuantSOBoundCondition f i a /\
    NoQuantExiStratCondition f i a.

End NoQuantDef.

Section NoQuantTranslation.

Definition ZO_NoQuant {ctx} (f : @ZerothOrderFormula ctx) (n : @NoQuant ctx) : @NoQuant ctx :=
  {| nu := nu n
   ; uniVBounds := uniVBounds n
   ; exiVBounds := exiVBounds n
   ; exiFOutputBounds := exiFOutputBounds n
   ; exiFInputBounds := exiFInputBounds n
   ; formula := inr f
  |}.

Fixpoint FOCtxMod {ctx} (f : @FirstOrderFormula ctx) : Sigma11Ctx :=
  match f with
  | ZO z => ctx
  | FOExists p f => FOCtxMod f
  | FOForall p f => FOCtxMod f
  end.

Program Fixpoint LiftPolyExi {ctx} (p : @PolyTerm ctx) : @PolyTerm (incExiV ctx) :=
  match p with
  | PolyFVar m => PolyFVar m
  | PolyEVar m => PolyEVar m.+1
  | PolyUVar m => PolyUVar m
  | PolyFFun i t => PolyFFun i (fun x => LiftPolyExi (t x))
  | PolyEFun i t => PolyEFun i (fun x => LiftPolyExi (t x))
  | PolyMinusOne => PolyMinusOne
  | PolyPlusOne => PolyPlusOne
  | PolyZero => PolyZero
  | PolyPlus r1 r2 => PolyPlus (LiftPolyExi r1) (LiftPolyExi r2)
  | PolyTimes r1 r2 => PolyTimes (LiftPolyExi r1) (LiftPolyExi r2)
  | PolyInd r1 r2 => PolyInd (LiftPolyExi r1) (LiftPolyExi r2)
  end.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. 
  remember (LiftPolyExi_obligation_4 _ _ _ _ _) as P; clear HeqP; simpl in P.
  by destruct ctx; replace H0 with P;[|apply eq_irrelevance].
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  remember (LiftPolyExi_obligation_6 _ _ _ _ _) as P; clear HeqP; simpl in P.
  by destruct ctx; replace H0 with P;[|apply eq_irrelevance].
Qed.

Program Fixpoint LiftPolyUni {ctx} (p : @PolyTerm ctx) : @PolyTerm (incUniV ctx) :=
  match p with
  | PolyFVar m => PolyFVar m
  | PolyEVar m => PolyEVar m
  | PolyUVar m => PolyUVar m.+1
  | PolyFFun i t => PolyFFun i (fun x => LiftPolyUni (t x))
  | PolyEFun i t => PolyEFun i (fun x => LiftPolyUni (t x))
  | PolyMinusOne => PolyMinusOne
  | PolyPlusOne => PolyPlusOne
  | PolyZero => PolyZero
  | PolyPlus r1 r2 => PolyPlus (LiftPolyUni r1) (LiftPolyUni r2)
  | PolyTimes r1 r2 => PolyTimes (LiftPolyUni r1) (LiftPolyUni r2)
  | PolyInd r1 r2 => PolyInd (LiftPolyUni r1) (LiftPolyUni r2)
  end.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. 
  remember (LiftPolyUni_obligation_4 _ _ _ _ _) as P; clear HeqP; simpl in P.
  by destruct ctx; replace H0 with P;[|apply eq_irrelevance].
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  remember (LiftPolyUni_obligation_6 _ _ _ _ _) as P; clear HeqP; simpl in P.
  by destruct ctx; replace H0 with P;[|apply eq_irrelevance].
Qed.

Fixpoint LiftPropExi {ctx} (p : @ZerothOrderFormula ctx) : @ZerothOrderFormula (incExiV ctx) :=
  match p with
  | ZONot f => ZONot (LiftPropExi f)
  | ZOAnd f1 f2 => ZOAnd (LiftPropExi f1) (LiftPropExi f2)
  | ZOOr f1 f2 => ZOOr (LiftPropExi f1) (LiftPropExi f2)
  | ZOImp f1 f2 => ZOImp (LiftPropExi f1) (LiftPropExi f2)
  | ZOEq r1 r2 => ZOEq (LiftPolyExi r1) (LiftPolyExi r2)
  end.

Fixpoint LiftPropUni {ctx} (p : @ZerothOrderFormula ctx) : @ZerothOrderFormula (incUniV ctx) :=
  match p with
  | ZONot f => ZONot (LiftPropUni f)
  | ZOAnd f1 f2 => ZOAnd (LiftPropUni f1) (LiftPropUni f2)
  | ZOOr f1 f2 => ZOOr (LiftPropUni f1) (LiftPropUni f2)
  | ZOImp f1 f2 => ZOImp (LiftPropUni f1) (LiftPropUni f2)
  | ZOEq r1 r2 => ZOEq (LiftPolyUni r1) (LiftPolyUni r2)
  end.

Program Definition AddExiVBound {ctx} (p : @PolyTerm ctx) (n : @NoQuant ctx) : @NoQuant (incExiV ctx) :=
  {| nu := ExtendAt0N (uniV ctx) (nu n)
   ; uniVBounds := fun x => LiftPolyExi (uniVBounds n x)
   ; exiVBounds := fun x => LiftPolyExi (ExtendAt0N p (exiVBounds n) x)
   ; exiFOutputBounds := fun x => LiftPolyExi (exiFOutputBounds n x)
   ; exiFInputBounds := fun x y => LiftPolyExi (exiFInputBounds n x y)
   ; formula := inrMap LiftPropExi (formula n)
  |}.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  unfold ExtendAt0N; dep_if_case (x == 0); auto.
  by destruct ctx.
  by destruct ((` (nu n)) _), ctx.
Qed.
Next Obligation. 
  unfold ExtendAt0N; dep_if_case (j == 0); auto.
  rewrite dep_if_case_true; auto.
  by destruct i, j.
  dep_if_case (i == 0); auto.
  by destruct ((` (nu n)) _), ctx. 
  destruct (nu n).
  apply i0.
  by destruct i, j.
Qed.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. 
  remember (AddExiVBound_obligation_7 _ _ _ _ _) as P; clear HeqP; simpl in P.
  by destruct ctx; replace P with H0;[|apply eq_irrelevance].
Qed.

Program Definition AddUniVBound {ctx} (p : @PolyTerm ctx) (n : @NoQuant ctx) : @NoQuant (incUniV ctx) :=
  {| nu := nu n
   ; uniVBounds := fun x => LiftPolyUni (ExtendAt0N p (uniVBounds n) x)
   ; exiVBounds := fun x => LiftPolyUni (exiVBounds n x)
   ; exiFOutputBounds := fun x => LiftPolyUni (exiFOutputBounds n x)
   ; exiFInputBounds := fun x y => LiftPolyUni (exiFInputBounds n x y)
   ; formula := inrMap LiftPropUni (formula n)
  |}.
Next Obligation. by destruct ctx. Qed.
Next Obligation. by destruct (` (nu n)), ctx; auto. Qed.
Next Obligation. by destruct nu; apply i0. Qed.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. 
  remember (AddUniVBound_obligation_7 _ _ _ _ _) as P; clear HeqP; simpl in P.
  by destruct ctx; replace P with H0;[|apply eq_irrelevance].
Qed.

Program Fixpoint FO_NoQuant {ctx} (f : @FirstOrderFormula ctx) (n : @NoQuant ctx) : @NoQuant (FOCtxMod f) :=
  match f with
  | ZO z => ZO_NoQuant z n
  | FOExists p f => FO_NoQuant f (AddExiVBound p n)
  | FOForall p f => FO_NoQuant f (AddUniVBound p n)
  end.

Program Fixpoint LiftPolyExiF {ctx} {a} (p : @PolyTerm ctx) : @PolyTerm (addExiF a ctx) :=
  match p with
  | PolyFVar m => PolyFVar m
  | PolyEVar m => PolyEVar m
  | PolyUVar m => PolyUVar m
  | PolyFFun i t => PolyFFun i (fun x => LiftPolyExiF (t x))
  | PolyEFun i t => PolyEFun i.+1 (fun x => LiftPolyExiF (t x))
  | PolyMinusOne => PolyMinusOne
  | PolyPlusOne => PolyPlusOne
  | PolyZero => PolyZero
  | PolyPlus r1 r2 => PolyPlus (LiftPolyExiF r1) (LiftPolyExiF r2)
  | PolyTimes r1 r2 => PolyTimes (LiftPolyExiF r1) (LiftPolyExiF r2)
  | PolyInd r1 r2 => PolyInd (LiftPolyExiF r1) (LiftPolyExiF r2)
  end.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. 
  remember (LiftPolyExiF_obligation_4 _ _ _ _ _ _) as P; clear HeqP; simpl in P.
  by destruct ctx; replace H0 with P;[|apply eq_irrelevance].
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  destruct ctx; simpl in *.
  unfold ExtendAt0N in H; simpl in H.
  remember (Utils.ExtendAt0N_obligation_2 _ _ _) as P; clear HeqP; simpl in P.
  by replace H0 with P;[|apply eq_irrelevance].
Qed.

Fixpoint LiftPropExiF {ctx} {a} (p : @ZerothOrderFormula ctx) : @ZerothOrderFormula (addExiF a ctx) :=
  match p with
  | ZONot f => ZONot (LiftPropExiF f)
  | ZOAnd f1 f2 => ZOAnd (LiftPropExiF f1) (LiftPropExiF f2)
  | ZOOr f1 f2 => ZOOr (LiftPropExiF f1) (LiftPropExiF f2)
  | ZOImp f1 f2 => ZOImp (LiftPropExiF f1) (LiftPropExiF f2)
  | ZOEq r1 r2 => ZOEq (LiftPolyExiF r1) (LiftPolyExiF r2)
  end.

Program Definition AddExiFBound {ctx} (p : @PolyTerm ctx) (bs : seq (@PolyTerm ctx)) (n : @NoQuant ctx) : 
  @NoQuant (addExiF (length bs) ctx) :=
  {| nu := nu n
   ; uniVBounds := fun x => LiftPolyExiF (a := length bs) (uniVBounds n x)
   ; exiVBounds := fun x => LiftPolyExiF (a := length bs) (exiVBounds n x)
   ; exiFOutputBounds := fun x => LiftPolyExiF (a := length bs) (ExtendAt0N p (exiFOutputBounds n) x)
   ; exiFInputBounds := fun i =>
    (if i == 0 as b return (i == 0) = b -> |[exiFA (addExiF (length bs) ctx) i]| -> @PolyTerm (addExiF (length bs) ctx)
    then fun _ j => LiftPolyExiF (lnth bs j)
    else fun _ j => LiftPolyExiF (exiFInputBounds n (i.-1) j)) (erefl _)
(* fun x y => LiftPolyExiF (ExtendAt0N (lnth bs) (exiFInputBounds n) x y) *)
   ; formula := inrMap LiftPropExiF (formula n)
  |}.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  by destruct ((` (nu n)) _), ctx.
Qed.
Next Obligation. by destruct nu, ctx; apply i0. Qed.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct i, ctx. Qed.
Next Obligation. by destruct i, ctx. Qed.
Next Obligation.
  remember (AddExiFBound_obligation_8 _ _ _ _ _ _ _ ) as P; clear HeqP; simpl in P.
  destruct i, ctx;[fcrush|simpl in *].
  unfold ExtendAt0N in H; simpl in H.
  remember (Utils.ExtendAt0N_obligation_2 _ _ _) as Q; clear HeqQ; simpl in Q.
  by replace P with Q;[|apply eq_irrelevance].
Qed.
Next Obligation.
  destruct ctx; simpl in *.
  unfold ExtendAt0N in H; simpl in H.
  rewrite dep_if_case_true in H; auto.
Qed.

Fixpoint SOCtxMod {ctx} (f : @SecondOrderFormula ctx) : Sigma11Ctx :=
  match f with
  | FO f => FOCtxMod f
  | SOExists y bs f => SOCtxMod f
  end.

Fixpoint SO_NoQuant {ctx} (f : @SecondOrderFormula ctx) (n : @NoQuant ctx) : @NoQuant (SOCtxMod f) :=
  match f with
  | FO f => FO_NoQuant f n
  | SOExists y bs f => SO_NoQuant f (AddExiFBound y bs n)
  end.

End NoQuantTranslation.

Section NoQuantCorrect.


Program Definition ModelInstance {ctx} {R} (M : @Sigma11Model R) : @NoQuantInstance ctx R :=
  {| freeVInst := freeV_F R M
   ; freeFInst := fun x => freeF_S R M x (freeFA ctx x)
  |}.

Definition SOContext freeV freeF freeFA exiF exiFA : Sigma11Ctx := 
  {| freeV := freeV
   ; freeF := freeF
   ; freeFA := freeFA
   ; exiV := 0
   ; exiF := exiF
   ; exiFA := exiFA
   ; uniV := 0 |}.

Program Definition SONoQuant {freeV freeF freeFA exiF exiFA} 
  exiFOutputBounds exiFInputBounds: 
  @NoQuant (SOContext freeV freeF freeFA exiF exiFA) :=
  {| nu := emptyTuple
   ; uniVBounds := emptyTuple
   ; exiVBounds := emptyTuple
   ; exiFOutputBounds := exiFOutputBounds
   ; exiFInputBounds := exiFInputBounds
   ; formula := inl ()
  |}.


Theorem SO_NOQuant_Sound {freeV freeF freeFA exiF exiFA R} (M : @Sigma11Model R) 
  (f : @SecondOrderFormula (SOContext freeV freeF freeFA exiF exiFA)) ys bss :
  NoQuantDenotation (SO_NoQuant f (SONoQuant ys bss)) (ModelInstance M) ->
  SecondOrder_Denote R f M.
induction f.
Admitted.


Definition EmptyContext freeV freeF freeFA : Sigma11Ctx := 
  {| freeV := freeV
   ; freeF := freeF
   ; freeFA := freeFA
   ; exiV := 0
   ; exiF := 0
   ; exiFA := emptyTuple
   ; uniV := 0 |}.

Program Definition EmptyNoQuant {freeV freeF freeFA} : @NoQuant (EmptyContext freeV freeF freeFA) :=
  {| nu := emptyTuple
   ; uniVBounds := emptyTuple
   ; exiVBounds := emptyTuple
   ; exiFOutputBounds := emptyTuple
   ; exiFInputBounds := emptyTuple
   ; formula := inl ()
  |}.

Theorem SO_NOQuant_Sound {freeV freeF freeFA R} (M : @Sigma11Model R) 
  (f : @SecondOrderFormula (EmptyContext freeV freeF freeFA)) :
  NoQuantDenotation (SO_NoQuant f EmptyNoQuant) (ModelInstance M) ->
  SecondOrder_Denote R f M.
Admitted.

Theorem SO_NOQuant_Complete {freeV freeF freeFA R} (M : @Sigma11Model R) 
  (f : @SecondOrderFormula (EmptyContext freeV freeF freeFA)) :
  SecondOrder_Denote R f M ->
  NoQuantDenotation (SO_NoQuant f EmptyNoQuant) (ModelInstance M).
Admitted.

Theorem SO_NOQuant_Correct {freeV freeF freeFA R} (M : @Sigma11Model R) 
  (f : @SecondOrderFormula (EmptyContext freeV freeF freeFA)) :
  SecondOrder_Denote R f M <->
  NoQuantDenotation (SO_NoQuant f EmptyNoQuant) (ModelInstance M).
Proof. qauto use: SO_NOQuant_Complete, SO_NOQuant_Sound. Qed.

End NoQuantCorrect.