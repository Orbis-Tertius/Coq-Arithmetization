From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import CoqArith.Sigma_1_1.
Require Import Program.

Section SemicircuitDef.

Record SemicircuitCtx {subCtx : Sigma11Ctx} := mkSemicircuitCtx
  { freeFC : |[freeF subCtx]| -> nat (*Number of free function calls*)
  ; exiFC : |[exiF subCtx]| -> nat (*Number of exi function calls*)
  ; indC : nat (*Number of ind function calls*)
  }.

(* <P> in the paper *)
Inductive SemicircuitPolyConstraint {subCtx} {ctx : @SemicircuitCtx subCtx} : Type :=
| PolyConsZero : SemicircuitPolyConstraint
| PolyConsPlusOne : SemicircuitPolyConstraint
| PolyConsMinusOne : SemicircuitPolyConstraint
| PolyConsPlus : SemicircuitPolyConstraint -> SemicircuitPolyConstraint -> SemicircuitPolyConstraint
| PolyConsTimes : SemicircuitPolyConstraint -> SemicircuitPolyConstraint -> SemicircuitPolyConstraint
| PolyConsInd : |[indC ctx]| -> SemicircuitPolyConstraint
| PolyConsFreeV : |[freeV subCtx]| -> SemicircuitPolyConstraint
| PolyConsExiV : |[exiV subCtx]| -> SemicircuitPolyConstraint
| PolyConsUniV : |[uniV subCtx]| -> SemicircuitPolyConstraint
| PolyConsFreeF : forall x : |[freeF subCtx]|, |[freeFC ctx x]| -> SemicircuitPolyConstraint
| PolyConsExiF : forall x : |[exiF subCtx]|, |[exiFC ctx x]| -> SemicircuitPolyConstraint.

(* <S> in the paper *)
Inductive SemicircuitPropConstraint {subCtx} {ctx : @SemicircuitCtx subCtx} : Type :=
| ZOConsNot : SemicircuitPropConstraint -> SemicircuitPropConstraint
| ZOConsAnd : SemicircuitPropConstraint ->
              SemicircuitPropConstraint ->
              SemicircuitPropConstraint
| ZOConsOr : SemicircuitPropConstraint ->
              SemicircuitPropConstraint ->
              SemicircuitPropConstraint
| ZOConsImp : SemicircuitPropConstraint ->
              SemicircuitPropConstraint ->
              SemicircuitPropConstraint
| ZOConsEq : @SemicircuitPolyConstraint _ ctx
          -> @SemicircuitPolyConstraint _ ctx
          -> SemicircuitPropConstraint.

Record SemiCircuit {ctx} : Type :=
  mkSemiCircuit {
    Ctx : @SemicircuitCtx ctx;
    freeFCalls := freeFC Ctx; (* r in paper *)
    exiFCalls := exiFC Ctx; (* q in paper *)
    indCalls := indC Ctx; 
    nu : {s : |[exiV ctx]| -> { m : nat | m <= uniV ctx } | forall i j : |[exiV ctx]|, (` i) <= (` j) -> (` (s j)) <= (` (s i))};
    polyConstraints : seq (@SemicircuitPolyConstraint _ Ctx);
    indArgs : |[indCalls]| -> (|[length polyConstraints]| * |[length polyConstraints]|);
    (* w in paper *)
    freeFArgs : forall (i : |[freeF ctx]|), |[freeFCalls i]| -> |[freeFA ctx i]| -> |[length polyConstraints]|;
    (* omega in paper *)
    exiFArgs : forall (i : |[exiF ctx]|), |[exiFCalls i]| -> |[exiFA ctx i]| -> |[length polyConstraints]|;
    (* V in paper *)
    uniVBounds : |[uniV ctx]| -> |[length polyConstraints]|;
    (* S in paper *)
    exiVBounds : |[exiV ctx]| -> |[length polyConstraints]|;
    (* B in paper *)
    exiFOutputBounds : |[exiF ctx]| -> |[length polyConstraints]|;
    (* G in paper *)
    exiFInputBounds : forall (i : |[exiF ctx]|), |[exiFA ctx i]| -> |[length polyConstraints]|;
    formula : unit + @SemicircuitPropConstraint _ Ctx
  }.

Record SemiCircuitInstance {ctx} {R : RingData} {c : @SemicircuitCtx ctx} : Type :=
  mkSemiCircuitInstance { 
    (* v in paper *)
    freeVInst : |[freeV ctx]| -> T R;
    (* f in paper *)
    freeFInst : forall i : |[freeF ctx]|, (|[freeFA ctx i]| -> T R) -> option (T R);
  }.

Record SemiCircuitAdvice {ctx} {R : RingData} {c : @SemicircuitCtx ctx} : Type :=
  mkSemiCircuitAdvice { 
    (* s in paper *)
    exiVAdv : |[exiV ctx]| -> (|[uniV ctx]| -> T R) -> T R;
    (* g in paper *)
    exiFAdv : forall i : |[exiF ctx]|, (|[exiFA ctx i]| -> T R) -> option (T R);
    (* o in paper *)
    freeFCallOut : forall i : |[freeF ctx]|, |[freeFC c i]| -> (|[uniV ctx]| -> T R) -> option (T R);
    (* sigma in paper *)
    exiFCallOut : forall i : |[exiF ctx]|, |[exiFC c i]| -> (|[uniV ctx]| -> T R) -> option (T R);
    indCallOut : |[indC c]| -> (|[uniV ctx]| -> T R) -> option (T R);
  }.

Definition indFun (R : RingData) (x y : T R) : T R := if lt_dec R x y then 1%R else 0%R.

Fixpoint SemicircuitPolyDenotation {ctx} {R} {c}
  (inst : @SemiCircuitInstance ctx R c)
  (adv : @SemiCircuitAdvice ctx R c)
  (p : @SemicircuitPolyConstraint ctx c) :
  (|[uniV ctx]| -> T R) -> option (T R) :=
  match p with
  | PolyConsZero => fun _ => Some 0%R
  | PolyConsPlusOne => fun _ => Some 1%R
  | PolyConsMinusOne => fun _ => Some (-1)%R
  | PolyConsPlus p1 p2 => fun u =>
    let r1 := SemicircuitPolyDenotation inst adv p1 u in
    let r2 := SemicircuitPolyDenotation inst adv p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) r2) r1
  | PolyConsTimes p1 p2 => fun u =>
    let r1 := SemicircuitPolyDenotation inst adv p1 u in
    let r2 := SemicircuitPolyDenotation inst adv p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) r2) r1
  | PolyConsInd i => indCallOut adv i
  | PolyConsFreeV i => fun _ => Some (freeVInst inst i)
  | PolyConsExiV i => fun u => Some (exiVAdv adv i u)
  | PolyConsUniV i => fun u => Some (u i)
  | PolyConsFreeF i j => freeFCallOut adv i j
  | PolyConsExiF i j => exiFCallOut adv i j
  end.

Program Fixpoint SemicircuitPropDenotation {ctx} {R} {c}
  (inst : @SemiCircuitInstance ctx R c)
  (adv : @SemiCircuitAdvice ctx R c)
  (p : @SemicircuitPropConstraint ctx c) :
  (|[uniV ctx]| -> T R) -> Prop :=
  match p with
  | ZOConsNot p => fun u => 
    let r := SemicircuitPropDenotation inst adv p u in
    not r
  | ZOConsAnd p1 p2 => fun u => 
    let r1 := SemicircuitPropDenotation inst adv p1 u in
    let r2 := SemicircuitPropDenotation inst adv p2 u in
    r1 /\ r2
  | ZOConsOr p1 p2 => fun u => 
    let r1 := SemicircuitPropDenotation inst adv p1 u in
    let r2 := SemicircuitPropDenotation inst adv p2 u in
    r1 \/ r2
  | ZOConsImp p1 p2 => fun u => 
    let r1 := SemicircuitPropDenotation inst adv p1 u in
    let r2 := SemicircuitPropDenotation inst adv p2 u in
    r1 -> r2
  | ZOConsEq p1 p2 => fun u => 
    let r1 := SemicircuitPolyDenotation inst adv p1 u in
    let r2 := SemicircuitPolyDenotation inst adv p2 u in
    match r1 with
    | None => false
    | Some r1 =>
      match r2 with
      | None => false
      | Some r2 => r1 = r2
      end
    end
  end.

Definition UProp {ctx} {R} {c}
                 (inst : @SemiCircuitInstance ctx R (Ctx c)) (adv : @SemiCircuitAdvice ctx R (Ctx c)) 
                 (t : |[uniV ctx]| -> T R) : Prop :=
  let ev i := SemicircuitPolyDenotation inst adv (lnth (polyConstraints c) (uniVBounds c i)) in
  forall i, 
    match (ev i t) with
    | None => false
    | Some e => lt R (t i) e
    end.

Definition U {ctx} {R} {c}
             (inst : @SemiCircuitInstance ctx R (Ctx c)) (adv : @SemiCircuitAdvice ctx R (Ctx c)) : Type 
  := { t : |[uniV ctx]| -> T R | UProp inst adv t }.

Definition SemiCircuitFormulaCondition {ctx} {R} {c}
  (inst : @SemiCircuitInstance ctx R (Ctx c))
  (adv : @SemiCircuitAdvice ctx R (Ctx c)) : Prop :=
  exists p, formula c = inr p /\ forall u, SemicircuitPropDenotation inst adv p u = true.

Definition SemiCircuitFreeFunCondition {ctx} {R} {c}
  (inst : @SemiCircuitInstance ctx R (Ctx c))
  (adv : @SemiCircuitAdvice ctx R (Ctx c)) : Prop :=
  forall u : U inst adv, forall i : |[freeF ctx]|, forall j : |[freeFCalls c i]|,
  let t (a : |[freeFA ctx i]|) : option (T R)
      := SemicircuitPolyDenotation inst adv (lnth (polyConstraints c) (freeFArgs c i j a)) (` u) in
  match OptionArgs (B := fun _ => _) t with
  | None => false
  | Some t => freeFInst inst i t = freeFCallOut adv i j (` u)
  end.

Definition SemiCircuitexiFCondition {ctx} {R} {c}
  (inst : @SemiCircuitInstance ctx R (Ctx c))
  (adv : @SemiCircuitAdvice ctx R (Ctx c)) : Prop :=
  forall u : U inst adv, forall i : |[exiF ctx]|, forall j : |[exiFCalls c i]|,
  let t (a : |[exiFA ctx i]|) : option (T R)
      := SemicircuitPolyDenotation inst adv (lnth (polyConstraints c) (exiFArgs c i j a)) (` u) in
  match OptionArgs (B := fun _ => _) t with
  | None => false
  | Some t => exiFAdv adv i t = exiFCallOut adv i j (` u)
  end.

Definition SemiCircuitIndCondition {ctx} {R} {c}
  (inst : @SemiCircuitInstance ctx R (Ctx c))
  (adv : @SemiCircuitAdvice ctx R (Ctx c)) : Prop :=
  forall u : U inst adv, forall i : |[indCalls c]|,
  let (a1, a2) := indArgs c i in
  let b1 : option (T R) := SemicircuitPolyDenotation inst adv (lnth (polyConstraints c) a1) (` u) in
  let b2 : option (T R) := SemicircuitPolyDenotation inst adv (lnth (polyConstraints c) a2) (` u) in
  obind (fun b1 => obind (fun b2 => Some (indFun R b1 b2)) b2) b1
  = indCallOut adv i (` u).

Definition SemiCircuitFOBoundCondition {ctx} {R} {c}
  (inst : @SemiCircuitInstance ctx R (Ctx c))
  (adv : @SemiCircuitAdvice ctx R (Ctx c)) : Prop :=
  forall u : U inst adv, forall i : |[exiV ctx]|,
  let B := SemicircuitPolyDenotation inst adv (lnth (polyConstraints c) (exiVBounds c i)) (` u) in
  match B with
  | None => false
  | Some B => lt R (exiVAdv adv i (` u)) B
  end.

(* Note: This covers both conditions 5 and 6 in the paper *)
Definition SemiCircuitSOBoundCondition {ctx} {R} {c}
  (inst : @SemiCircuitInstance ctx R (Ctx c))
  (adv : @SemiCircuitAdvice ctx R (Ctx c)) : Prop :=
  forall u : U inst adv, forall i : |[exiF ctx]|,
  let B := SemicircuitPolyDenotation inst adv (lnth (polyConstraints c) (exiFOutputBounds c i)) (` u) in
  let G (j : |[exiFA ctx i]|) := SemicircuitPolyDenotation inst adv (lnth (polyConstraints c) (exiFInputBounds c i j)) (` u) in
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

Program Definition SemiCircuitExiStratCondition {ctx} {R} {c}
  (inst : @SemiCircuitInstance ctx R (Ctx c))
  (adv : @SemiCircuitAdvice ctx R (Ctx c)) : Prop :=
  forall i : |[exiV ctx]|, forall m : |[nu c i]| -> T R,
  exists C, forall n : |[uniV ctx - nu c i]| -> T R,
  exiVAdv adv i (TupConcat m n) = C.
Next Obligation.
  destruct ((` (nu c)) (exist (fun n : nat => n < _) i H0)); simpl in *.
  replace (x0 + (uniV ctx - x0)) with (uniV ctx); auto.
  remember (uniV ctx) as U; clear HeqU H x n m H0 adv inst c i.
  sfirstorder use: subnKC.
Qed.

Definition SemiCircuitDenotation {ctx} {R} {c} (i : @SemiCircuitInstance ctx R (Ctx c)) : Prop :=
  exists (a : SemiCircuitAdvice),
    SemiCircuitFormulaCondition i a /\
    SemiCircuitFreeFunCondition i a /\
    SemiCircuitIndCondition i a /\
    SemiCircuitexiFCondition i a /\
    SemiCircuitFOBoundCondition i a /\
    SemiCircuitSOBoundCondition i a /\
    SemiCircuitExiStratCondition i a.

End SemicircuitDef.
