From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import CoqArith.Sigma_1_1.
Require Import Program.

Section SemicircuitDef.

Record SemicircuitCtx := mkSemicircuitCtx
  { subCtx : Sigma11Ctx
  ; freeVS := freeV subCtx
  ; freeFS := freeF subCtx
  ; freeFSA := freeFA subCtx
  ; exiVS := exiV subCtx
  ; exiFS := exiF subCtx
  ; exiFSA := exiFA subCtx
  ; uniVS := uniV subCtx
  ; freeFC : |[freeF subCtx]| -> nat (*Number of free function calls*)
  ; exiFC : |[exiF subCtx]| -> nat (*Number of exi function calls*)
  ; indC : nat (*Number of ind function calls*)
  }.

(* <P> in the paper *)
Inductive SemicircuitPolyConstraint {ctx : SemicircuitCtx} : Type :=
| PolyConsZero : SemicircuitPolyConstraint
| PolyConsPlusOne : SemicircuitPolyConstraint
| PolyConsMinusOne : SemicircuitPolyConstraint
| PolyConsPlus : SemicircuitPolyConstraint -> SemicircuitPolyConstraint -> SemicircuitPolyConstraint
| PolyConsTimes : SemicircuitPolyConstraint -> SemicircuitPolyConstraint -> SemicircuitPolyConstraint
| PolyConsInd : |[indC ctx]| -> SemicircuitPolyConstraint
| PolyConsFreeV : |[freeVS ctx]| -> SemicircuitPolyConstraint
| PolyConsExiV : |[exiVS ctx]| -> SemicircuitPolyConstraint
| PolyConsUniV : |[uniVS ctx]| -> SemicircuitPolyConstraint
| PolyConsFreeF : forall x : |[freeFS ctx]|, |[freeFC ctx x]| -> SemicircuitPolyConstraint
| PolyConsExiF : forall x : |[exiFS ctx]|, |[exiFC ctx x]| -> SemicircuitPolyConstraint.

(* <S> in the paper *)
Inductive SemicircuitPropConstraint {ctx : SemicircuitCtx} : Type :=
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
| ZOConsEq : @SemicircuitPolyConstraint ctx
          -> @SemicircuitPolyConstraint ctx
          -> SemicircuitPropConstraint.

Record SemiCircuit : Type :=
  mkSemiCircuit {
    Ctx : SemicircuitCtx;
    freeVN := freeVS Ctx; (* n in paper *)
    freeFN := freeFS Ctx; (* Number of free functions *)
    freeFArity := freeFSA Ctx; (* a in paper *)
    exiVN := exiVS Ctx; (* m in paper *)
    exiFN := exiFS Ctx; (* Number of SO existential functions *)
    exiFArity := exiFSA Ctx; (* b in paper *)
    uniVN := uniVS Ctx; (* u in paper *)
    freeFCalls := freeFC Ctx; (* r in paper *)
    exiFCalls := exiFC Ctx; (* q in paper *)
    indCalls := indC Ctx; 
    nu : {s : |[exiVN]| -> { m : nat | m <= uniVN } | forall i j : |[exiVN]|, (` i) <= (` j) -> (` (s j)) <= (` (s i))};
    polyConstraints : seq (@SemicircuitPolyConstraint Ctx);
    indArgs : |[indCalls]| -> (|[length polyConstraints]| * |[length polyConstraints]|);
    (* w in paper *)
    freeFArgs : forall (i : |[freeFN]|), |[freeFCalls i]| -> |[freeFArity i]| -> |[length polyConstraints]|;
    (* omega in paper *)
    exiFArgs : forall (i : |[exiFN]|), |[exiFCalls i]| -> |[exiFArity i]| -> |[length polyConstraints]|;
    (* V in paper *)
    uniVBounds : |[uniVN]| -> |[length polyConstraints]|;
    (* S in paper *)
    exiVBounds : |[exiVN]| -> |[length polyConstraints]|;
    (* B in paper *)
    exiFOutputBounds : |[exiFN]| -> |[length polyConstraints]|;
    (* G in paper *)
    exiFInputBounds : forall (i : |[exiFN]|), |[exiFArity i]| -> |[length polyConstraints]|;
    formula : unit + @SemicircuitPropConstraint Ctx
  }.

Record SemiCircuitInstance {R : RingData} {c : SemicircuitCtx} : Type :=
  mkSemiCircuitInstance { 
    (* v in paper *)
    freeVInst : |[freeVS c]| -> T R;
    (* f in paper *)
    freeFInst : forall i : |[freeFS c]|, (|[freeFSA c i]| -> T R) -> option (T R);
  }.

Record SemiCircuitAdvice {R : RingData} {c : SemicircuitCtx} : Type :=
  mkSemiCircuitAdvice { 
    (* s in paper *)
    exiVAdv : |[exiVS c]| -> (|[uniVS c]| -> T R) -> T R;
    (* g in paper *)
    exiFAdv : forall i : |[exiFS c]|, (|[exiFSA c i]| -> T R) -> option (T R);
    (* o in paper *)
    freeFCallOut : forall i : |[freeFS c]|, |[freeFC c i]| -> (|[uniVS c]| -> T R) -> T R;
    (* sigma in paper *)
    exiFCallOut : forall i : |[exiFS c]|, |[exiFC c i]| -> (|[uniVS c]| -> T R) -> T R;
    indCallOut : |[indC c]| -> (|[uniVS c]| -> T R) -> T R;
  }.

Definition indFun (R : RingData) (x y : T R) : T R := if lt_dec R x y then 1%R else 0%R.

Fixpoint SemicircuitPolyDenotation {R} {c}
  (inst : @SemiCircuitInstance R c)
  (adv : @SemiCircuitAdvice R c)
  (p : @SemicircuitPolyConstraint c) :
  (|[uniVS c]| -> T R) -> T R :=
  match p with
  | PolyConsZero => fun _ => 0%R
  | PolyConsPlusOne => fun _ => 1%R
  | PolyConsMinusOne => fun _ => (-1)%R
  | PolyConsPlus p1 p2 => fun u =>
    let r1 := SemicircuitPolyDenotation inst adv p1 u in
    let r2 := SemicircuitPolyDenotation inst adv p2 u in 
    (r1 + r2)%R
  | PolyConsTimes p1 p2 => fun u =>
    let r1 := SemicircuitPolyDenotation inst adv p1 u in
    let r2 := SemicircuitPolyDenotation inst adv p2 u in 
    (r1 * r2)%R
  | PolyConsInd i => indCallOut adv i
  | PolyConsFreeV i => fun _ => freeVInst inst i
  | PolyConsExiV i => exiVAdv adv i
  | PolyConsUniV i => fun u => u i
  | PolyConsFreeF i j => freeFCallOut adv i j
  | PolyConsExiF i j => exiFCallOut adv i j
  end.

Program Fixpoint SemicircuitPropDenotation {R} {c}
  (inst : @SemiCircuitInstance R c)
  (adv : @SemiCircuitAdvice R c)
  (p : @SemicircuitPropConstraint c) :
  (|[uniVS c]| -> T R) -> Prop :=
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
    r1 = r2
  end.

Definition UProp {R} {c}
                 (inst : @SemiCircuitInstance R (Ctx c)) (adv : @SemiCircuitAdvice R (Ctx c)) 
                 (t : |[uniVN c]| -> T R) : Prop :=
  let ev i := SemicircuitPolyDenotation inst adv (lnth (polyConstraints c) (uniVBounds c i)) in
  forall i, lt R (t i) (ev i t).

Definition U {R} {c}
             (inst : @SemiCircuitInstance R (Ctx c)) (adv : @SemiCircuitAdvice R (Ctx c)) : Type 
  := { t : |[uniVN c]| -> T R | UProp inst adv t }.

Definition SemiCircuitFormulaCondition {R} {c}
  (inst : @SemiCircuitInstance R (Ctx c))
  (adv : @SemiCircuitAdvice R (Ctx c)) : Prop :=
  exists p, formula c = inr p /\ forall u, SemicircuitPropDenotation inst adv p u = true.

Definition SemiCircuitFreeFunCondition {R} {c}
  (inst : @SemiCircuitInstance R (Ctx c))
  (adv : @SemiCircuitAdvice R (Ctx c)) : Prop :=
  forall u : U inst adv, forall i : |[freeFN c]|, forall j : |[freeFCalls c i]|,
  let t (a : |[freeFArity c i]|) : T R
      := SemicircuitPolyDenotation inst adv (lnth (polyConstraints c) (freeFArgs c i j a)) (` u) in
  freeFInst inst i t = Some (freeFCallOut adv i j (` u)).

Definition SemiCircuitexiFCondition {R} {c}
  (inst : @SemiCircuitInstance R (Ctx c))
  (adv : @SemiCircuitAdvice R (Ctx c)) : Prop :=
  forall u : U inst adv, forall i : |[exiFN c]|, forall j : |[exiFCalls c i]|,
  let t (a : |[exiFArity c i]|) : T R
      := SemicircuitPolyDenotation inst adv (lnth (polyConstraints c) (exiFArgs c i j a)) (` u) in
  exiFAdv adv i t = Some (exiFCallOut adv i j (` u)).

Definition SemiCircuitIndCondition {R} {c}
  (inst : @SemiCircuitInstance R (Ctx c))
  (adv : @SemiCircuitAdvice R (Ctx c)) : Prop :=
  forall u : U inst adv, forall i : |[indCalls c]|,
  let (a1, a2) := indArgs c i in
  let b1 : T R := SemicircuitPolyDenotation inst adv (lnth (polyConstraints c) a1) (` u) in
  let b2 : T R := SemicircuitPolyDenotation inst adv (lnth (polyConstraints c) a2) (` u) in
  indFun R b1 b2 = indCallOut adv i (` u).

Definition SemiCircuitFOBoundCondition {R} {c}
  (inst : @SemiCircuitInstance R (Ctx c))
  (adv : @SemiCircuitAdvice R (Ctx c)) : Prop :=
  forall u : U inst adv, forall i : |[exiVN c]|,
  let B := SemicircuitPolyDenotation inst adv (lnth (polyConstraints c) (exiVBounds c i)) (` u) in
  lt R (exiVAdv adv i (` u)) B.

(* Note: This covers both conditions 5 and 6 in the paper *)
Definition SemiCircuitSOBoundCondition {R} {c}
  (inst : @SemiCircuitInstance R (Ctx c))
  (adv : @SemiCircuitAdvice R (Ctx c)) : Prop :=
  forall u : U inst adv, forall i : |[exiFN c]|,
  let B := SemicircuitPolyDenotation inst adv (lnth (polyConstraints c) (exiFOutputBounds c i)) (` u) in
  let G (j : |[exiFArity c i]|) := SemicircuitPolyDenotation inst adv (lnth (polyConstraints c) (exiFInputBounds c i j)) (` u) in
  forall (t : |[exiFArity c i]| -> T R) (out : T R),
  exiFAdv adv i t = Some out ->
  (forall x, lt R (t x) (G x)) /\ lt R out B.

Program Definition SemiCircuitExiStratCondition {R} {c}
  (inst : @SemiCircuitInstance R (Ctx c))
  (adv : @SemiCircuitAdvice R (Ctx c)) : Prop :=
  forall i : |[exiVN c]|, forall m : |[nu c i]| -> T R,
  exists C, forall n : |[uniVN c - nu c i]| -> T R,
  exiVAdv adv i (TupConcat m n) = C.
Next Obligation.
  destruct ((` (nu c)) (exist (fun n : nat => n < exiVN c) i H0)); simpl in *.
  replace (x0 + (uniVN c - x0)) with (uniVN c); auto.
  remember (uniVN c) as U; clear HeqU H x n m H0 adv inst c i.
  sfirstorder use: subnKC.
Qed.

Definition SemiCircuitDenotation {R} {c} (i : @SemiCircuitInstance R (Ctx c)) : Prop :=
  exists (a : SemiCircuitAdvice),
    SemiCircuitFormulaCondition i a /\
    SemiCircuitFreeFunCondition i a /\
    SemiCircuitIndCondition i a /\
    SemiCircuitexiFCondition i a /\
    SemiCircuitFOBoundCondition i a /\
    SemiCircuitSOBoundCondition i a /\
    SemiCircuitExiStratCondition i a.

End SemicircuitDef.
