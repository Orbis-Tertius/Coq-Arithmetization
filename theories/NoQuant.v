From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import CoqArith.Sigma_1_1.
Require Import Program.

Section NoQuantDef.

Variables D : RingData.

Record NoQuant
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV} : Type :=
  mkNoQuant {
    nu : {s : |[exiV]| -> { m : nat | m <= uniV } | forall i j : |[exiV]|, (` i) <= (` j) -> (` (s j)) <= (` (s i))};
    uniVBounds : |[uniV]| -> @PolyTerm freeV freeF freeFA exiV exiF exiFA uniV;
    exiVBounds : |[exiV]| -> @PolyTerm freeV freeF freeFA exiV exiF exiFA uniV;
    exiFOutputBounds : |[exiF]| -> @PolyTerm freeV freeF freeFA exiV exiF exiFA uniV;
    exiFInputBounds : forall (i : |[exiF]|), |[exiFA i]| -> @PolyTerm freeV freeF freeFA exiV exiF exiFA uniV;
    formula : unit + @ZerothOrderFormula freeV freeF freeFA exiV exiF exiFA uniV
  }.

Record NoQuantInstance {freeV freeF} {freeFA : |[freeF]| -> nat} : Type :=
  mkNoQuantInstance { 
    freeVInst : |[freeV]| -> T D;
    freeFInst : forall i : |[freeF]|, (|[freeFA i]| -> T D) -> option (T D);
  }.

Record NoQuantAdvice {exiV exiF} {exiFA : |[exiF]| -> nat} {uniV} : Type :=
  mkNoQuantAdvice { 
    exiVAdv : |[exiV]| -> (|[uniV]| -> T D) -> T D;
    exiFAdv : forall i : |[exiF]|, (|[exiFA i]| -> T D) -> option (T D);
  }.

Fixpoint NoQuantPolyDenotation
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (inst : @NoQuantInstance freeV freeF freeFA)
  (adv : @NoQuantAdvice exiV exiF exiFA uniV)
  (p : @PolyTerm freeV freeF freeFA exiV exiF exiFA uniV) :
  (|[uniV]| -> T D) -> option (T D) :=
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
    obind (fun r1 => obind (fun r2 => Some (indFun D r1 r2)) r2) r1
  end.

Program Fixpoint NoQuantPropDenotation
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (inst : @NoQuantInstance freeV freeF freeFA)
  (adv : @NoQuantAdvice exiV exiF exiFA uniV)
  (p : @ZerothOrderFormula freeV freeF freeFA exiV exiF exiFA uniV) :
  (|[uniV]| -> T D) -> Prop :=
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

Definition UProp
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (f : NoQuant) 
  (inst : @NoQuantInstance freeV freeF freeFA)
  (adv : @NoQuantAdvice exiV exiF exiFA uniV)
  (t : |[uniV]| -> T D) : Prop :=
  let ev i := NoQuantPolyDenotation inst adv (uniVBounds f i) in
  forall i, 
    match (ev i t) with
    | None => false
    | Some e => lt D (t i) e
    end.

Definition U
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (f : @NoQuant freeV freeF freeFA exiV exiF exiFA uniV) 
  (inst : NoQuantInstance) (adv : NoQuantAdvice) : Type 
  := { t : |[uniV]| -> T D | UProp f inst adv t }.

Definition NoQuantFormulaCondition 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (f : @NoQuant freeV freeF freeFA exiV exiF exiFA uniV) 
  (inst : NoQuantInstance) (adv : NoQuantAdvice) : Prop :=
  exists p, formula f = inr p /\ forall u, NoQuantPropDenotation inst adv p u = true.

Definition NoQuantFOBoundCondition 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (f : @NoQuant freeV freeF freeFA exiV exiF exiFA uniV) 
  (inst : NoQuantInstance) (adv : NoQuantAdvice) : Prop :=
  forall u : U f inst adv, forall i : |[exiV]|,
  let B := NoQuantPolyDenotation inst adv (exiVBounds f i) (` u) in
  match B with
  | None => false
  | Some B => lt D (exiVAdv adv i (` u)) B
  end.

(* Note: This covers both conditions 5 and 6 in the paper *)
Definition NoQuantSOBoundCondition
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (f : @NoQuant freeV freeF freeFA exiV exiF exiFA uniV) 
  (inst : NoQuantInstance) (adv : NoQuantAdvice) : Prop :=
  forall u : U f inst adv, forall i : |[exiF]|,
  let B := NoQuantPolyDenotation inst adv (exiFOutputBounds f i) (` u) in
  let G (j : |[exiFA i]|) := NoQuantPolyDenotation inst adv (exiFInputBounds f i j) (` u) in
  forall (t : |[exiFA i]| -> T D) (out : T D),
  exiFAdv adv i t = Some out ->
  match B with
  | None => false
  | Some B => lt D out B /\ forall x,
    match G x with
    | None => false
    | Some Gx => lt D (t x) Gx
    end
  end.

Program Definition NoQuantExiStratCondition 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (f : @NoQuant freeV freeF freeFA exiV exiF exiFA uniV) 
  (inst : @NoQuantInstance freeV freeF freeFA)
  (adv : @NoQuantAdvice exiV exiF exiFA uniV) : Prop :=
  forall i : |[exiV]|, forall m : |[nu f i]| -> T D,
  exists C, forall n : |[uniV - nu f i]| -> T D,
  exiVAdv adv i (TupConcat m n) = C.
Next Obligation.
  destruct ((` (nu f)) (exist (fun n : nat => n < _) i H0)); simpl in *.
  replace (x0 + (uniV - x0)) with (uniV); auto.
  remember (uniV) as U; clear HeqU H x n m H0 adv inst f i.
  sfirstorder use: subnKC.
Qed.

Definition NoQuantDenotation
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (f : @NoQuant freeV freeF freeFA exiV exiF exiFA uniV) 
  (i : NoQuantInstance): Prop :=
  exists (a : NoQuantAdvice),
    NoQuantFormulaCondition f i a /\
    NoQuantFOBoundCondition f i a /\
    NoQuantSOBoundCondition f i a /\
    NoQuantExiStratCondition f i a.

End NoQuantDef.

Section NoQuantTranslation.

Definition ZO_NoQuant 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (f : @ZerothOrderFormula freeV freeF freeFA exiV exiF exiFA uniV) 
  (n : NoQuant) : NoQuant :=
  {| nu := nu n
   ; uniVBounds := uniVBounds n
   ; exiVBounds := exiVBounds n
   ; exiFOutputBounds := exiFOutputBounds n
   ; exiFInputBounds := exiFInputBounds n
   ; formula := inr f
  |}.

Program Fixpoint LiftPolyExi 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV} 
  (p : @PolyTerm freeV freeF freeFA exiV exiF exiFA uniV) : 
  @PolyTerm freeV freeF freeFA (exiV.+1) exiF exiFA uniV :=
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

Program Fixpoint LiftPolyUni 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV} 
  (p : @PolyTerm freeV freeF freeFA exiV exiF exiFA uniV) : 
  @PolyTerm freeV freeF freeFA exiV exiF exiFA (uniV.+1) :=
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

Fixpoint LiftPropExi 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (p : @ZerothOrderFormula freeV freeF freeFA exiV exiF exiFA uniV) : 
  @ZerothOrderFormula freeV freeF freeFA (exiV.+1) exiF exiFA uniV :=
  match p with
  | ZONot f => ZONot (LiftPropExi f)
  | ZOAnd f1 f2 => ZOAnd (LiftPropExi f1) (LiftPropExi f2)
  | ZOOr f1 f2 => ZOOr (LiftPropExi f1) (LiftPropExi f2)
  | ZOImp f1 f2 => ZOImp (LiftPropExi f1) (LiftPropExi f2)
  | ZOEq r1 r2 => ZOEq (LiftPolyExi r1) (LiftPolyExi r2)
  end.

Fixpoint LiftPropUni 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (p : @ZerothOrderFormula freeV freeF freeFA exiV exiF exiFA uniV) : 
  @ZerothOrderFormula freeV freeF freeFA exiV exiF exiFA (uniV.+1) :=
  match p with
  | ZONot f => ZONot (LiftPropUni f)
  | ZOAnd f1 f2 => ZOAnd (LiftPropUni f1) (LiftPropUni f2)
  | ZOOr f1 f2 => ZOOr (LiftPropUni f1) (LiftPropUni f2)
  | ZOImp f1 f2 => ZOImp (LiftPropUni f1) (LiftPropUni f2)
  | ZOEq r1 r2 => ZOEq (LiftPolyUni r1) (LiftPolyUni r2)
  end.

Program Definition AddExiVBound 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (p : @PolyTerm freeV freeF freeFA exiV exiF exiFA uniV)
  (n : @NoQuant freeV freeF freeFA exiV exiF exiFA uniV) : 
  @NoQuant freeV freeF freeFA (exiV.+1) exiF exiFA uniV :=
  {| nu := ExtendAt0N (uniV) (nu n)
   ; uniVBounds := fun x => LiftPolyExi (uniVBounds n x)
   ; exiVBounds := fun x => LiftPolyExi (ExtendAt0N p (exiVBounds n) x)
   ; exiFOutputBounds := fun x => LiftPolyExi (exiFOutputBounds n x)
   ; exiFInputBounds := fun x y => LiftPolyExi (exiFInputBounds n x y)
   ; formula := inrMap LiftPropExi (formula n)
  |}.
Next Obligation.
  unfold ExtendAt0N.
  dep_if_case (x == 0); auto.
  by destruct ((` (nu n)) _).
Qed.
Next Obligation.
  unfold ExtendAt0N.
  dep_if_case (j == 0); auto.
  rewrite dep_if_case_true; auto.
  destruct i;[auto|apply EEConvert.1 in H2;fcrush].
  dep_if_case (i == 0); auto.
  by destruct ((` (nu n)) _).
  by destruct (nu n); apply i0; destruct i, j.
Qed.

Program Definition AddUniVBound 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (p : @PolyTerm freeV freeF freeFA exiV exiF exiFA uniV)
  (n : @NoQuant freeV freeF freeFA exiV exiF exiFA uniV) : 
  @NoQuant freeV freeF freeFA exiV exiF exiFA (uniV.+1) :=
  {| nu := nu n
   ; uniVBounds := fun x => LiftPolyUni (ExtendAt0N p (uniVBounds n) x)
   ; exiVBounds := fun x => LiftPolyUni (exiVBounds n x)
   ; exiFOutputBounds := fun x => LiftPolyUni (exiFOutputBounds n x)
   ; exiFInputBounds := fun x y => LiftPolyUni (exiFInputBounds n x y)
   ; formula := inrMap LiftPropUni (formula n)
  |}.
Next Obligation. by destruct (` (nu n)); auto. Qed.
Next Obligation. by destruct nu; apply i0. Qed.

Fixpoint FOExiMod 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (f : @FirstOrderFormula freeV freeF freeFA exiV exiF exiFA uniV) : nat :=
  match f with
  | ZO z => exiV
  | FOExists p f => FOExiMod f
  | FOForall p f => FOExiMod f
  end.

Fixpoint FOUniMod 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (f : @FirstOrderFormula freeV freeF freeFA exiV exiF exiFA uniV) : nat :=
  match f with
  | ZO z => uniV
  | FOExists p f => FOUniMod f
  | FOForall p f => FOUniMod f
  end.

Fixpoint FO_NoQuant 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (f : @FirstOrderFormula freeV freeF freeFA exiV exiF exiFA uniV)
  (n : @NoQuant freeV freeF freeFA exiV exiF exiFA uniV) : 
  @NoQuant freeV freeF freeFA (FOExiMod f) exiF exiFA (FOUniMod f) :=
  match f with
  | ZO z => ZO_NoQuant z n
  | FOExists p f => FO_NoQuant f (AddExiVBound p n)
  | FOForall p f => FO_NoQuant f (AddUniVBound p n)
  end.

Program Fixpoint LiftPolyExiF 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  {a} 
  (p : @PolyTerm freeV freeF freeFA exiV exiF exiFA uniV) : 
  @PolyTerm freeV freeF freeFA exiV (exiF.+1) (ExtendAt0N a exiFA) uniV :=
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
Next Obligation.
  unfold ExtendAt0N in H; simpl in H.
  remember (Utils.ExtendAt0N_obligation_2 _ _ _) as P; clear HeqP; simpl in P.
  by replace H0 with P;[|apply eq_irrelevance].
Qed.

Fixpoint LiftPropExiF 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  {a} 
  (p : @ZerothOrderFormula freeV freeF freeFA exiV exiF exiFA uniV) : 
  @ZerothOrderFormula freeV freeF freeFA exiV (exiF.+1) (ExtendAt0N a exiFA) uniV :=
  match p with
  | ZONot f => ZONot (LiftPropExiF f)
  | ZOAnd f1 f2 => ZOAnd (LiftPropExiF f1) (LiftPropExiF f2)
  | ZOOr f1 f2 => ZOOr (LiftPropExiF f1) (LiftPropExiF f2)
  | ZOImp f1 f2 => ZOImp (LiftPropExiF f1) (LiftPropExiF f2)
  | ZOEq r1 r2 => ZOEq (LiftPolyExiF r1) (LiftPolyExiF r2)
  end.

Program Definition AddExiFBound 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (p : @PolyTerm freeV freeF freeFA exiV exiF exiFA uniV)
  (bs : seq (@PolyTerm freeV freeF freeFA exiV exiF exiFA uniV)) 
  (n : @NoQuant freeV freeF freeFA exiV exiF exiFA uniV) : 
  @NoQuant freeV freeF freeFA exiV (exiF.+1) (ExtendAt0N (length bs) exiFA) uniV :=
  {| nu := nu n
   ; uniVBounds := fun x => LiftPolyExiF (a := length bs) (uniVBounds n x)
   ; exiVBounds := fun x => LiftPolyExiF (a := length bs) (exiVBounds n x)
   ; exiFOutputBounds := fun x => LiftPolyExiF (a := length bs) (ExtendAt0N p (exiFOutputBounds n) x)
   ; exiFInputBounds := fun i =>
    (if i == 0 as b return (i == 0) = b -> |[ExtendAt0N (length bs) exiFA i]| -> PolyTerm
    then fun _ j => LiftPolyExiF (lnth bs j)
    else fun _ j => LiftPolyExiF (exiFInputBounds n (i.-1) j)) (erefl _)
(* fun x y => LiftPolyExiF (ExtendAt0N (lnth bs) (exiFInputBounds n) x y) *)
   ; formula := inrMap LiftPropExiF (formula n)
  |}.
Next Obligation. by destruct i. Qed.
Next Obligation.
  unfold ExtendAt0N in H.
  change (exist _ ?x _ == exist _ ?y _) with (x == y) in *.
  remember (AddExiFBound_obligation_2 _ _ _ _ _ _ _ _ _ _ _) as P; clear HeqP; simpl in P.
  rewrite dep_if_case_false in H; simpl in H.
  remember (Utils.ExtendAt0N_obligation_2 _ _ _) as Q; clear HeqQ; simpl in Q.
  by replace P with Q;[|apply eq_irrelevance].
Qed.
Next Obligation.
  unfold ExtendAt0N in H.
  by rewrite dep_if_case_true in H.
Qed.

Fixpoint SOExiFMod 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiF} {exiFA : |[exiF]| -> nat}
  (f : @SecondOrderFormula freeV freeF freeFA exiF exiFA) : nat :=
  match f with
  | FO f => exiF
  | SOExists y bs f => SOExiFMod f
  end.

Fixpoint SOExiFAMod 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiF} {exiFA : |[exiF]| -> nat}
  (f : @SecondOrderFormula freeV freeF freeFA exiF exiFA) : |[SOExiFMod f]| -> nat :=
  match f with
  | FO _ => exiFA
  | SOExists y bs f => SOExiFAMod f
  end.

Fixpoint SOExiMod 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiF} {exiFA : |[exiF]| -> nat}
  (f : @SecondOrderFormula freeV freeF freeFA exiF exiFA) : nat :=
  match f with
  | FO f => FOExiMod f
  | SOExists y bs f => SOExiMod f
  end.

Fixpoint SOUniMod 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiF} {exiFA : |[exiF]| -> nat}
  (f : @SecondOrderFormula freeV freeF freeFA exiF exiFA) : nat :=
  match f with
  | FO f => FOUniMod f
  | SOExists y bs f => SOUniMod f
  end.

Fixpoint SO_NoQuant 
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiF} {exiFA : |[exiF]| -> nat}
  (f : @SecondOrderFormula freeV freeF freeFA exiF exiFA) 
  (n : @NoQuant freeV freeF freeFA 0 exiF exiFA 0) : 
  @NoQuant freeV freeF freeFA (SOExiMod f) (SOExiFMod f) (SOExiFAMod f) (SOUniMod f) :=
  match f with
  | FO f => FO_NoQuant f n
  | SOExists y bs f => SO_NoQuant f (AddExiFBound y bs n)
  end.

End NoQuantTranslation.

Section NoQuantCorrect.

Variables D : RingData.

Program Definition ModelInstance
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  (M : @Sigma11Model D) : @NoQuantInstance D freeV freeF freeFA :=
  {| freeVInst := freeV_F D M
   ; freeFInst := fun x => freeF_S D M x (freeFA x)
  |}.

Program Definition SONoQuant {freeV freeF freeFA exiF exiFA} 
  exiFOutputBounds exiFInputBounds: 
  @NoQuant freeV freeF freeFA 0 exiF exiFA 0 :=
  {| nu := emptyTuple
   ; uniVBounds := emptyTuple
   ; exiVBounds := emptyTuple
   ; exiFOutputBounds := exiFOutputBounds
   ; exiFInputBounds := exiFInputBounds
   ; formula := inl ()
  |}.


Fixpoint FOModelMod
  {freeV freeF} {freeFA : |[freeF]| -> nat}
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  uniV
  (f : @FirstOrderFormula freeV freeF freeFA exiV exiF exiFA uniV) : Type :=
match f with
| ZO f => @Sigma11Model D
| FOExists p f => (|[uniV]| -> T D) -> FOModelMod uniV f
| FOForall p f => FOModelMod (uniV.+1) f
end.

Fixpoint SOModelMod 
  {freeV freeF freeFA exiF exiFA}
  (f : @SecondOrderFormula freeV freeF freeFA exiF exiFA) : Type :=
match f with
| FO f => FOModelMod 0 f
| SOExists y bs f => ((|[length bs]| -> T D) -> option (T D)) -> SOModelMod f
end.

Arguments SecondOrderFormula _ _ _ _ _ : clear implicits.
Arguments FirstOrderFormula _ _ _ _ _ _ _ : clear implicits.

Theorem SO_NOQuant_Sound 
  {freeV freeF freeFA exiF exiFA} 
  (M : @Sigma11Model D) 
  (f : @SecondOrderFormula freeV freeF freeFA exiF exiFA) ys bss :
  NoQuantDenotation D (SO_NoQuant f (SONoQuant ys bss)) (ModelInstance M) ->
  SecondOrder_Denote D f M.
move: M.
induction f.
2:{
  intros M H.
  simpl in H.  
  simpl.
  remember (Poly_Denote D y M) as D1.
  destruct D1.
  remember (option_tuple
    (fun m : {n : nat | n < length bs} => Poly_Denote D (lnth bs m) M)) as D2.
  destruct D2.
  destruct H as [[exiVAdv exiFAdv] [H0 [H1 [H2 H3]]]].
  assert (0 < SOExiFMod f).
  2:{
  remember (exiFAdv (exist _ 0 H)) as f0.
  replace (length bs)
     with (SOExiFAMod f (exist (fun n0 : nat => n0 < SOExiFMod f) 0 H)) in f0.
  replace (SOExiFAMod f (exist (fun n0 : nat => n0 < SOExiFMod f) 0 H))
     with (length bs) in f0.
  Search sig.
  Unset Printing Notations.
  clear HeqD2 s0 HeqD1 s H3 H2 H1 H0 exiFAdv exiVAdv M IHf bss ys y D.
  induction f; auto.
  unfold SOExiMod.
  remember (exiFAdv 0) as Cool.
  remember (ex_proj1 H) as adv.
  destruct y.
  unfold AddExiFBound.
Admitted.

Program Definition EmptyNoQuant {freeV freeF freeFA} : @NoQuant freeV freeF freeFA 0 0 emptyTuple 0 :=
  {| nu := emptyTuple
   ; uniVBounds := emptyTuple
   ; exiVBounds := emptyTuple
   ; exiFOutputBounds := emptyTuple
   ; exiFInputBounds := emptyTuple
   ; formula := inl ()
  |}.

Theorem SO_NOQuant_Sound_E {freeV freeF freeFA} (M : @Sigma11Model D) 
  (f : @SecondOrderFormula freeV freeF freeFA 0 emptyTuple) :
  NoQuantDenotation D (SO_NoQuant f EmptyNoQuant) (ModelInstance M) ->
  SecondOrder_Denote D f M.
Admitted.

Theorem SO_NOQuant_Complete_E {freeV freeF freeFA} (M : @Sigma11Model D) 
  (f : @SecondOrderFormula freeV freeF freeFA 0 emptyTuple) :
  SecondOrder_Denote D f M ->
  NoQuantDenotation D (SO_NoQuant f EmptyNoQuant) (ModelInstance M).
Admitted.

Theorem SO_NOQuant_Correct {freeV freeF freeFA} (M : @Sigma11Model D) 
  (f : @SecondOrderFormula freeV freeF freeFA 0 emptyTuple) :
  SecondOrder_Denote D f M <->
  NoQuantDenotation D (SO_NoQuant f EmptyNoQuant) (ModelInstance M).
Proof. qauto use: SO_NOQuant_Complete_E, SO_NOQuant_Sound_E. Qed.

End NoQuantCorrect.