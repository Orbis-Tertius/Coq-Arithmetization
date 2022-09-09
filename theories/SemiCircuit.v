From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import CoqArith.Sigma_1_1.
Require Import Program.

Section SemicircuitDef.

Theorem Hole {A : Type} : A.
Admitted.

Record SemicircuitCtx := mkSemicircuitCtx
  { subCtx : Sigma11Ctx
  ; freeVS := freeV subCtx
  ; freeFS := freeF subCtx
  ; freeFSA := freeFA subCtx
  ; exiVS := exiV subCtx
  ; exiFS := exiF subCtx
  ; exiFSA := exiFA subCtx
  ; uniVS := uniV subCtx
  ; freeFC : |[freeF subCtx]| -> nat (*Number of function calls*)
  ; exiFC : |[exiF subCtx]| -> nat (*Number of function calls*)
  }.

(* <P> in the paper *)
Inductive SemicircuitPolyConstraint {ctx : SemicircuitCtx} : Type :=
| PolyConsZero : SemicircuitPolyConstraint
| PolyConsPlusOne : SemicircuitPolyConstraint
| PolyConsMinusOne : SemicircuitPolyConstraint
| PolyConsPlus : SemicircuitPolyConstraint -> SemicircuitPolyConstraint -> SemicircuitPolyConstraint
| PolyConsTimes : SemicircuitPolyConstraint -> SemicircuitPolyConstraint -> SemicircuitPolyConstraint
| PolyConsInd : SemicircuitPolyConstraint -> SemicircuitPolyConstraint -> SemicircuitPolyConstraint
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
    nu : {s : |[exiVN]| -> { m : nat | m <= uniVN } | forall i j : |[exiVN]|, (` i) <= (` j) -> (` (s j)) <= (` (s i))};
    polyConstraints : seq (@SemicircuitPolyConstraint Ctx);
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

Record SemiCircuitInstance (M : RingData) (c : SemiCircuit) : Type :=
  mkSemiCircuitInstance { 
    freeVInst : |[freeVN c]| -> T M;
    freeFInst : forall i : |[freeFN c]|, (|[freeFArity c i]| -> T M) -> option (T M);
  }.

Record SemiCircuitAdvice (M : RingData) (c : SemiCircuit) : Type :=
  mkSemiCircuitAdvice { 
    exiFInst : forall i : |[exiFN c]|, (|[exiFArity c i]| -> T M) -> option (T M);
    (* s in paper *)
    exiVInst : |[exiVN c]| -> (|[uniVN c]| -> T M) -> T M;
    (* o in paper *)
    freeFCallOut : forall i : |[freeFN c]|, |[freeFCalls c i]| -> (|[uniVN c]| -> T M) -> T M;
    (* sigma in paper *)
    exiFCallOut : forall i : |[exiFN c]|, |[exiFCalls c i]| -> (|[uniVN c]| -> T M) -> T M;
  }.

Definition indFun (M : RingData) (x y : T M) : T M := if lt_dec M x y then 1%R else 0%R.

Fixpoint SemicircuitPolyDenotation
  (M : RingData) (c : SemiCircuit)
  (inst : SemiCircuitInstance M c)
  (adv : SemiCircuitAdvice M c)
  (p : @SemicircuitPolyConstraint (Ctx c)) :
  (|[uniVN c]| -> T M) -> T M :=
  match p with
  | PolyConsZero => fun _ => 0%R
  | PolyConsPlusOne => fun _ => 1%R
  | PolyConsMinusOne => fun _ => (-1)%R
  | PolyConsPlus p1 p2 => fun u =>
    let r1 := SemicircuitPolyDenotation M c inst adv p1 u in
    let r2 := SemicircuitPolyDenotation M c inst adv p2 u in 
    (r1 + r2)%R
  | PolyConsTimes p1 p2 => fun u =>
    let r1 := SemicircuitPolyDenotation M c inst adv p1 u in
    let r2 := SemicircuitPolyDenotation M c inst adv p2 u in 
    (r1 * r2)%R
  | PolyConsInd p1 p2 => fun u => 
    let r1 := SemicircuitPolyDenotation M c inst adv p1 u in
    let r2 := SemicircuitPolyDenotation M c inst adv p2 u in
    indFun M r1 r2
  | PolyConsFreeV i => fun _ => freeVInst _ _ inst i
  | PolyConsExiV i => exiVInst _ _ adv i
  | PolyConsUniV i => fun u => u i
  | PolyConsFreeF i j => freeFCallOut _ _ adv i j
  | PolyConsExiF i j => exiFCallOut _ _ adv i j
  end.

Program Fixpoint SemicircuitPropDenotation
  (M : RingData) (c : SemiCircuit)
  (inst : SemiCircuitInstance M c)
  (adv : SemiCircuitAdvice M c)
  (p : @SemicircuitPropConstraint (Ctx c)) :
  (|[uniVN c]| -> T M) -> Prop :=
  match p with
  | ZOConsNot p => fun u => 
    let r := SemicircuitPropDenotation M c inst adv p u in
    not r
  | ZOConsAnd p1 p2 => fun u => 
    let r1 := SemicircuitPropDenotation M c inst adv p1 u in
    let r2 := SemicircuitPropDenotation M c inst adv p2 u in
    r1 /\ r2
  | ZOConsOr p1 p2 => fun u => 
    let r1 := SemicircuitPropDenotation M c inst adv p1 u in
    let r2 := SemicircuitPropDenotation M c inst adv p2 u in
    r1 \/ r2
  | ZOConsImp p1 p2 => fun u => 
    let r1 := SemicircuitPropDenotation M c inst adv p1 u in
    let r2 := SemicircuitPropDenotation M c inst adv p2 u in
    r1 -> r2
  | ZOConsEq p1 p2 => fun u => 
    let r1 := SemicircuitPolyDenotation M c inst adv p1 u in
    let r2 := SemicircuitPolyDenotation M c inst adv p2 u in
    r1 = r2
  end.

Definition UProp {c : SemiCircuit} {M : RingData}
                 (inst : SemiCircuitInstance M c) (adv : SemiCircuitAdvice M c) 
                 (t : |[uniVN c]| -> T M) : Prop :=
  let ev i := SemicircuitPolyDenotation M c inst adv (lnth (polyConstraints c) (uniVBounds c i)) in
  forall i, lt M (t i) (ev i t).

Definition U {c : SemiCircuit} {M : RingData}
             (inst : SemiCircuitInstance M c) (adv : SemiCircuitAdvice M c) : Type 
  := { t : |[uniVN c]| -> T M | UProp inst adv t }.

Definition SemiCircuitFormulaCondition
  (M : RingData) (c : SemiCircuit)
  (inst : SemiCircuitInstance M c)
  (adv : SemiCircuitAdvice M c) : Prop :=
  exists p, formula c = inr p /\ forall u, SemicircuitPropDenotation M c inst adv p u = true.

Definition SemiCircuitFreeFunCondition
  (M : RingData) (c : SemiCircuit)
  (inst : SemiCircuitInstance M c)
  (adv : SemiCircuitAdvice M c) : Prop :=
  forall u : U inst adv, forall i : |[freeFN c]|, forall j : |[freeFCalls c i]|,
  let t (a : |[freeFArity c i]|) : T M
      := SemicircuitPolyDenotation M c inst adv (lnth (polyConstraints c) (freeFArgs c i j a)) (` u) in
  freeFInst _ _ inst i t = Some (freeFCallOut M c adv i j (` u)).

Definition SemiCircuitexiFCondition
  (M : RingData) (c : SemiCircuit)
  (inst : SemiCircuitInstance M c)
  (adv : SemiCircuitAdvice M c) : Prop :=
  forall u : U inst adv, forall i : |[exiFN c]|, forall j : |[exiFCalls c i]|,
  let t (a : |[exiFArity c i]|) : T M
      := SemicircuitPolyDenotation M c inst adv (lnth (polyConstraints c) (exiFArgs c i j a)) (` u) in
  exiFInst _ _ adv i t = Some (exiFCallOut M c adv i j (` u)).

Definition SemiCircuitFOBoundCondition
  (M : RingData) (c : SemiCircuit)
  (inst : SemiCircuitInstance M c)
  (adv : SemiCircuitAdvice M c) : Prop :=
  forall u : U inst adv, forall i : |[exiVN c]|,
  let B := SemicircuitPolyDenotation M c inst adv (lnth (polyConstraints c) (exiVBounds c i)) (` u) in
  lt M (exiVInst _ _ adv i (` u)) B.

(* Note: This covers both conditions 5 and 6 in the paper *)
Definition SemiCircuitSOBoundCondition
  (M : RingData) (c : SemiCircuit)
  (inst : SemiCircuitInstance M c)
  (adv : SemiCircuitAdvice M c) : Prop :=
  forall u : U inst adv, forall i : |[exiFN c]|,
  let B := SemicircuitPolyDenotation M c inst adv (lnth (polyConstraints c) (exiFOutputBounds c i)) (` u) in
  let G (j : |[exiFArity c i]|) := SemicircuitPolyDenotation M c inst adv (lnth (polyConstraints c) (exiFInputBounds c i j)) (` u) in
  forall (t : |[exiFArity c i]| -> T M) (out : T M),
  exiFInst _ _ adv i t = Some out ->
  (forall x, lt M (t x) (G x)) /\ lt M out B.

Program Definition SemiCircuitExiStratCondition
  (M : RingData) (c : SemiCircuit)
  (inst : SemiCircuitInstance M c)
  (adv : SemiCircuitAdvice M c) : Prop :=
  forall i : |[exiVN c]|, forall m : |[nu c i]| -> T M,
  forall n1 n2 : |[uniVN c - nu c i]| -> T M,
  forall H1 : UProp inst adv (TupConcat m n1),
  forall H2 : UProp inst adv (TupConcat m n2),
  exiVInst _ _ adv i (TupConcat m n1) = exiVInst _ _ adv i (TupConcat m n2).
Next Obligation.
  destruct ((` (nu c)) (exist (fun n : nat => n < exiVN c) i H0)); simpl in *.
  replace (x0 + (uniVN c - x0)) with (uniVN c); auto.
  remember (uniVN c) as U; clear HeqU H x n1 n2 m H0 adv inst c M i.
  sfirstorder use: subnKC.
Qed.
Next Obligation.
  clear H1.
  destruct ((` (nu c)) (exist (fun n : nat => n < exiVN c) i H0)); simpl in *.
  replace (x0 + (uniVN c - x0)) with (uniVN c); auto.
  remember (uniVN c) as U; clear HeqU H x n1 n2 m H0 adv inst c M i.
  sfirstorder use: subnKC.
Qed.
Next Obligation.
  clear H2 H1.
  destruct ((` (nu c)) (exist (fun n : nat => n < exiVN c) i H0)); simpl in *.
  replace (x0 + (uniVN c - x0)) with (uniVN c); auto.
  remember (uniVN c) as U; clear HeqU H x n1 n2 m H0 adv inst c M i.
  sfirstorder use: subnKC.
Qed.
Next Obligation.
  clear H2 H1.
  destruct ((` (nu c)) (exist (fun n : nat => n < exiVN c) i H0)); simpl in *.
  replace (x0 + (uniVN c - x0)) with (uniVN c); auto.
  remember (uniVN c) as U; clear HeqU H x n1 n2 m H0 adv inst c M i.
  sfirstorder use: subnKC.
Qed.

Definition SemiCircuitDenotation (M : RingData)
  (c : SemiCircuit) (i : SemiCircuitInstance M c) : Prop :=
  exists (a : SemiCircuitAdvice M c),
    SemiCircuitFormulaCondition M c i a /\
    SemiCircuitFreeFunCondition M c i a /\
    SemiCircuitexiFCondition M c i a /\
    SemiCircuitFOBoundCondition M c i a /\
    SemiCircuitSOBoundCondition M c i a /\
    SemiCircuitExiStratCondition M c i a.

End SemicircuitDef.

Section SemicircuitTranslation.

Program Definition fseqSnoc {A} {n : nat} (a : A) (f : |[n]| -> A) (m : |[n.+1]|) : A :=
  (if m < n as b return m < n = b -> A
   then fun _ => f m
   else fun _ => a) (erefl _).

Program Definition fseqCCat {A} {n m : nat} (x : |[n]| -> A) (y : |[m]| -> A) (l : |[n + m]|) : A :=
  (if l < n as b return l < n = b -> A
   then fun _ => x l
   else fun _ => y (l - n)) (erefl _).
Next Obligation.
  by assert (~ (l < n));[ hauto
                        | assert (n <= l);[ apply (contra_not_leq (P := l < n))
                                          | qauto use: ltn_subLR]].
Qed.

(*Convert constraint to one over context with additional function calls*)
Program Fixpoint PolyCallCastFree {ctx}
  {newC : |[freeFS ctx]| -> nat}
  (p : @SemicircuitPolyConstraint ctx) :
  @SemicircuitPolyConstraint {| subCtx := subCtx ctx
                              ; freeFC := fun x => freeFC ctx x + newC x
                              ; exiFC := exiFC ctx|} := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyCallCastFree p1 in
    let r2 := PolyCallCastFree p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyCallCastFree p1 in
    let r2 := PolyCallCastFree p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd p1 p2 =>
    let r1 := PolyCallCastFree p1 in
    let r2 := PolyCallCastFree p2 in 
    PolyConsInd r1 r2
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsExiV i => PolyConsExiV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF i j
  end.
Next Obligation. qauto use: ltn_addr. Qed.

Program Fixpoint PolyCallCastExi {ctx}
  {newC : |[exiFS ctx]| -> nat}
  (p : @SemicircuitPolyConstraint ctx) :
  @SemicircuitPolyConstraint {| subCtx := subCtx ctx
                              ; freeFC := freeFC ctx
                              ; exiFC := fun x => exiFC ctx x + newC x|} := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyCallCastExi p1 in
    let r2 := PolyCallCastExi p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyCallCastExi p1 in
    let r2 := PolyCallCastExi p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd p1 p2 =>
    let r1 := PolyCallCastExi p1 in
    let r2 := PolyCallCastExi p2 in 
    PolyConsInd r1 r2
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsExiV i => PolyConsExiV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF i j
  end.
Next Obligation. qauto use: ltn_addr. Qed.

Program Fixpoint PolyCallCast {ctx}
    {newFC : |[freeFS ctx]| -> nat}
    {newEC : |[exiFS ctx]| -> nat}
    (p : @SemicircuitPolyConstraint ctx) :
    @SemicircuitPolyConstraint {| subCtx := subCtx ctx
                               ; freeFC := fun x => freeFC ctx x + newFC x
                               ; exiFC := fun x => exiFC ctx x + newEC x|} := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyCallCast p1 in
    let r2 := PolyCallCast p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyCallCast p1 in
    let r2 := PolyCallCast p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd p1 p2 =>
    let r1 := PolyCallCast p1 in
    let r2 := PolyCallCast p2 in 
    PolyConsInd r1 r2
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsExiV i => PolyConsExiV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF i j
  end.
Solve All Obligations with qauto use: ltn_addr.

(*Lift new polynomial args so names don't conflict with arguments from other polynomials *)
Program Fixpoint PolyCallLift {ctx}
    {newFC : |[freeFS ctx]| -> nat}
    {newEC : |[exiFS ctx]| -> nat}
    (p : @SemicircuitPolyConstraint ctx) :
    @SemicircuitPolyConstraint {| subCtx := subCtx ctx
                                ; freeFC := fun x => newFC x + freeFC ctx x
                                ; exiFC := fun x => newEC x +  exiFC ctx x|} := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyCallLift p1 in
    let r2 := PolyCallLift p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyCallLift p1 in
    let r2 := PolyCallLift p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd p1 p2 =>
    let r1 := PolyCallLift p1 in
    let r2 := PolyCallLift p2 in 
    PolyConsInd r1 r2
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsExiV i => PolyConsExiV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i (newFC i + j)
  | PolyConsExiF i j => PolyConsExiF i (newEC i + j)
  end.
Solve All Obligations with qauto use: ltn_add2l.

(*Cast a sequence of polynomials so they have no conflicting variables. *)
Fixpoint PolyCallSeqFuse {ctx : Sigma11Ctx} 
  (s : seq { freeFCalls : |[freeF ctx]| -> nat & { exiFCalls : |[exiF ctx]| -> nat & 
      @SemicircuitPolyConstraint {| subCtx := ctx
                                  ; freeFC := freeFCalls
                                  ; exiFC := exiFCalls |}
      } }) :
  seq (@SemicircuitPolyConstraint {| subCtx := ctx
                                   ; freeFC := (fun x => sumn [seq projT1 i x | i <- s])
                                   ; exiFC := (fun x => sumn [seq projT1 (projT2 i) x | i <- s]) |}) :=
  match s with
  | [::] => [::]
  | existT a (existT b x) :: xs => 
    PolyCallCast x :: map PolyCallLift (PolyCallSeqFuse xs)
  end.

Record PolyConversionData {ctx : Sigma11Ctx} : Type := mkPolyConvertData {
  newFreeFCalls : |[freeF ctx]| -> nat ;
  newExiFCalls : |[exiF ctx]| -> nat ;
  newPolys : seq (@SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls; exiFC := newExiFCalls |}) ;
  newFreeArgs : forall (i : |[freeF ctx]|), |[newFreeFCalls i]| -> |[freeFA ctx i]| -> |[length newPolys]| ;
  newExiArgs : forall (i : |[exiF ctx]|), |[newExiFCalls i]| -> |[exiFA ctx i]| -> |[length newPolys]|
  }.

Definition PolyConversionEmptyData {ctx}: 
  @PolyConversionData ctx :=
  {| newFreeFCalls := fun _ => 0; newExiFCalls := fun _ => 0; newPolys := [::]
   ; newFreeArgs := fun x => emptyTuple; newExiArgs := fun x => emptyTuple|}.

Program Definition PolyConversionCombineData {ctx}
  (d1 d2 : @PolyConversionData ctx) : @PolyConversionData ctx :=
  match d1, d2 with
  | {| newFreeFCalls := nffc1; newExiFCalls := nefc1; newPolys := polys1; newFreeArgs := fcal1; newExiArgs := ecal1 |}
  , {| newFreeFCalls := nffc2; newExiFCalls := nefc2; newPolys := polys2; newFreeArgs := fcal2; newExiArgs := ecal2 |}
  => {| newFreeFCalls := fun x => nffc1 x + nffc2 x
      ; newExiFCalls := fun x => nefc1 x + nefc2 x
      ; newPolys := map PolyCallCast polys1 ++ map PolyCallLift polys2
      ; newFreeArgs := fun i j => (
        if j < nffc1 i as b return j < nffc1 i = b -> |[freeFA ctx i]| -> |[length (map PolyCallCast polys1 ++ map PolyCallLift polys2)]|
        then fun _ => fcal1 i j
        else fun _ => fcal2 i (j - nffc1 i)
      ) (erefl _)
      ; newExiArgs := fun i j => (
        if j < nefc1 i as b return j < nefc1 i = b -> |[exiFA ctx i]| -> |[length (map PolyCallCast polys1 ++ map PolyCallLift polys2)]|
        then fun _ => ecal1 i j
        else fun _ => ecal2 i (j - nefc1 i)
      ) (erefl _) |}
  end.
Next Obligation.
  change (length ?n) with (size n); rewrite size_cat; do 2 rewrite size_map.
  by destruct (fcal1 _); apply ltn_addr.
Qed.
Next Obligation.
  assert (~ (j < nffc1 (exist _ i H0)));[hauto|].
  assert (nffc1 (exist _ i H0) <= j);[by apply (contra_not_leq (P := j < nffc1 (exist _ i H0)))|].
  qauto use: ltn_subLR, ltn_addr.
Qed.
Next Obligation.
  change (length ?n) with (size n); rewrite size_cat; do 2 rewrite size_map.
  by destruct (fcal2 _); apply ltn_addl.
Qed.
Next Obligation.
  change (length ?n) with (size n); rewrite size_cat; do 2 rewrite size_map.
  by destruct (ecal1 _); apply ltn_addr.
Qed.
Next Obligation.
  assert (~ (j < nefc1 (exist _ i H0)));[hauto|].
  assert (nefc1 (exist _ i H0) <= j);[by apply (contra_not_leq (P := j < nefc1 (exist _ i H0)))|].
  qauto use: ltn_subLR, ltn_addr.
Qed.
Next Obligation.
  change (length ?n) with (size n); rewrite size_cat; do 2 rewrite size_map.
  by destruct (ecal2 _); apply ltn_addl.
Qed.

(*Reform output of PolyConvert in preparation for PolyCallSeqFuse *)
Definition OutReform {ctx}
  (s : { d : @PolyConversionData ctx &  
    @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d |} }) :
  { freeFCalls : |[freeF ctx]| -> nat & { exiFCalls : |[exiF ctx]| -> nat & 
      @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := freeFCalls; exiFC := exiFCalls |}  
      } } := 
  match s with
  | existT {| newFreeFCalls := nffc1; newExiFCalls := nefc1; newPolys := _; newFreeArgs := _; newExiArgs := _ |}
           p => existT _ nffc1 (existT _ nefc1 p)
  end.

(*Call for a single function*)
Definition SingleCall {FN} (i : |[FN]|) (j : |[FN]|) : nat :=
  (if j == i as b return (j == i) = b -> nat 
   then fun _ => 1
   else fun _ => 0) (erefl _).

(*Add new call to a function*)
Definition AddCall {FN} (FCalls : |[FN]| -> nat) (j : |[FN]|) : |[FN]| -> nat :=
  fun i => FCalls i + SingleCall j i.

(*Add polynomial addresses from a new to call function*)
Program Definition AddPolys {FN} {n} {m} (FCalls : |[FN]| -> nat) (FArity : |[FN]| -> nat)
  (j : |[FN]|) (k : |[FArity j]| -> |[m]|)
  (freeCalls : forall (i : |[FN]|), |[FCalls i]| -> |[FArity i]| -> |[n]|)
  (i : |[FN]|) : |[AddCall FCalls j i]| -> |[FArity i]| -> |[n + m]| := (
    if i == j as b return (i == j) = b -> |[AddCall FCalls j i]| -> |[FArity i]| -> |[n + m]| 
    then fun _ c => (
      (*If we're looking at the last call*)
      if c == FCalls i as b return (c == FCalls i) = b -> |[FArity i]| -> |[n + m]|
      then fun _ x => n + k x
      else fun _ => freeCalls i c
      ) (erefl _)
    else fun _ => freeCalls i
  ) (erefl _).
Next Obligation.
  unfold AddCall in H.
  unfold SingleCall in H.
  rewrite dep_if_case_false in H; auto.
  remember (FCalls _) as F; clear HeqF.
  replace (F + 0) with F in H; auto.
  clear k; hauto use: addSn, add1n, addSnnS, addn1 inv: nat.
Qed.
Next Obligation. destruct (freeCalls _); hauto use: ltn_addr. Qed.
Next Obligation.
  unfold AddCall, SingleCall.
  rewrite dep_if_case_true; auto.
  remember (FCalls _) as F; clear HeqF.
  replace (F + 1) with (F.+1);[sfirstorder|hauto use: addn1].
Qed.
Next Obligation.
  apply EEFConvert in e0; simpl in e0.
  unfold AddCall, SingleCall in H; rewrite dep_if_case_true in H; auto.
  remember (FCalls _) as F; clear HeqF.
  move: F e0 H;elim: c;[move=>[|F];hauto|]=>c IH [|F] e0 H;auto.
  apply IH; auto.
Qed.
Next Obligation. destruct (freeCalls _); hauto use: ltn_addr. Qed.
Next Obligation.
  clear e0; apply EEConvert, (subset_eq_compat _ (fun n : nat => n < FN) _ _ H1 H2) in e; hauto.
Qed.
Next Obligation. by destruct (k _); rewrite ltn_add2l. Qed.

(*Add a list of circuit constraints associated to a free fun call to data*)
Program Definition FreeCallIncorp {ctx}
  (d : @PolyConversionData ctx) (i : |[freeF ctx]|) :
  forall s : seq (@SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d |}),
  length s = freeFA ctx i -> @PolyConversionData ctx :=
  match d with
  | {| newFreeFCalls := nffc; newExiFCalls := nefc; newPolys := plys; newFreeArgs := nfc; newExiArgs := nec |} =>
    fun ps ls =>
    {| newFreeFCalls := AddCall nffc i
    ;  newExiFCalls := nefc
    ;  newPolys := map (PolyCallCastFree (newC := SingleCall i)) (plys ++ ps)
    ;  newFreeArgs := AddPolys nffc (freeFA ctx) i (cRangeFun 0 (freeFA ctx i)) nfc 
    ;  newExiArgs := nec |}
  end.
Next Obligation.
  destruct (AddPolys _ _ _ _ _ _); simpl.
  rewrite map_length; change (length ?x) with (size x).
  rewrite size_cat; change (size ?x) with (length x).
  by rewrite ls.
Qed.
Next Obligation.
  destruct (nec _ _ _); simpl.
  rewrite map_length; change (length ?x) with (size x).
  rewrite size_cat; change (size ?x) with (length x).
  hauto use: ltnW, ltn_addr, ltnS.
Qed.

(*Add a list of circuit constraints associated to an exi fun call to data*)
Program Definition ExiCallIncorp {ctx}
  (d : @PolyConversionData ctx) (i : |[exiF ctx]|) :
  forall s : seq (@SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d |}),
  length s = exiFA ctx i ->
  @PolyConversionData ctx :=
  match d with
  | {| newFreeFCalls := nffc; newExiFCalls := nefc; newPolys := plys; newFreeArgs := nfc; newExiArgs := nec |} =>
    fun ps ls =>
    {| newFreeFCalls := nffc
    ;  newExiFCalls := AddCall nefc i
    ;  newPolys := map (PolyCallCastExi (newC := SingleCall i)) (plys ++ ps)
    ;  newFreeArgs := nfc 
    ;  newExiArgs := AddPolys nefc (exiFA ctx) i (cRangeFun 0 (exiFA ctx i)) nec |}
  end.
Next Obligation.
  destruct (nfc _ _ _); simpl.
  rewrite map_length; change (length ?x) with (size x).
  rewrite size_cat; change (size ?x) with (length x).
  hauto use: ltnW, ltn_addr, ltnS.
Qed.
Next Obligation.
  destruct (AddPolys _ _ _ _ _ _); simpl.
  rewrite map_length; change (length ?x) with (size x).
  rewrite size_cat; change (size ?x) with (length x).
  by rewrite ls.
Qed.

Program Definition PolyConvertLem3 {T} {n} {f : |[n]| -> T} {i : |[n]|} :
  f i = lnth [seq f i | i <- cRange 0 n] i := erefl _.
Next Obligation. by rewrite map_length (length_cRange (n := 0) (m := n)). Qed.
Next Obligation. 
  unfold lnth.
  rewrite (tnth_nth (f (exist (fun n0 : nat => n0 < n) i H))).
  simpl; rewrite nth_map; f_equal.
  rewrite (nth_cRange (m := 0) (n := n)).
  by apply subset_eq_compat.
Qed.

Theorem PolymorphicEqElim 
  {T S}  {fam : Type -> Type}
  {P : S -> Type} 
  {f : forall x, fam x -> T}
  {x y}
  {e : x = y}
  {s : fam (P x)} :
  f _ (eq_rect _ (fun x => fam (P x)) s _ e) = f _ s.
Proof. by destruct e. Qed.

Lemma PolyConvertFreeCaseLem {ctx} {D : @PolyConversionData ctx} {i : |[freeF ctx]|} {B} {e} :
  newFreeFCalls D i < newFreeFCalls (FreeCallIncorp D i B e) i.
Proof.
  destruct D; simpl.
  unfold AddCall.
  unfold SingleCall.
  rewrite dep_if_case_true;[by rewrite EEConvert|].
  hauto use: ltnSn, addn1, contra_ltn_leq.
Qed.

Program Definition PolyConvertFreeCase {ctx} 
  (i : |[freeF ctx]|) 
  (t : |[freeFA ctx i]| ->
    { d : @PolyConversionData ctx &  
    @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d |} }) :
  { d : @PolyConversionData ctx &  
    @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d |} } := 
  (* We start with a function name and a list of data and constraints that needs to be fused together *)
  (* The first thing we need to do is fuse this list of data into a single peice of data*)
  let rs : seq {d : @PolyConversionData ctx 
                  & @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d |} } 
         := [seq t i | i <- cRange 0 (freeFA ctx i) ] in
  let data : @PolyConversionData ctx := foldr PolyConversionCombineData PolyConversionEmptyData [seq projT1 i | i <- rs] in

  (* We also need consolidate all the polynomial constraints into a single list and add those to the data*)
  let polys : seq (@SemicircuitPolyConstraint {| subCtx := ctx
                      ; freeFC := newFreeFCalls data
                      ; exiFC := newExiFCalls data |})
               := eq_rect _ (fun x => seq (@SemicircuitPolyConstraint {| subCtx := _; freeFC := _; exiFC := x |})) (
                  eq_rect _ (fun x => seq (@SemicircuitPolyConstraint {| subCtx := _; freeFC := x; exiFC := _ |})) 
                  (PolyCallSeqFuse (map OutReform rs)) _ _) _ _ in
  let data2 : @PolyConversionData ctx := FreeCallIncorp data i polys _ in

  (*We return a call the the most recently added function *)
  existT _ data2 (PolyConsFreeF i (newFreeFCalls data i)).
Next Obligation.
  apply functional_extensionality.
  elim: [seq t i0 | i0 <- cRange 0 _]; auto.
  move=> [d p] l IH x.
  transitivity ((projT1 (OutReform (existT _ d p)) x) + sumn [seq projT1 i x | i <- [seq OutReform j | j <- l]]); auto.
  rewrite IH.
  destruct d, x.
  by simpl; destruct (foldr PolyConversionCombineData PolyConversionEmptyData [seq projT1 i0 | i0 <- l]).
Qed.
Next Obligation.
  apply functional_extensionality.
  elim: [seq t i0 | i0 <- cRange 0 _]; auto.
  move=> [d p] l IH x.
  transitivity ((projT1 (projT2 (OutReform (existT _ d p))) x) + sumn [seq projT1 (projT2 i) x | i <- [seq OutReform j | j <- l]]); auto.
  rewrite IH.
  destruct d, x.
  by simpl; destruct (foldr PolyConversionCombineData PolyConversionEmptyData [seq projT1 i0 | i0 <- l]).
Qed.
Next Obligation.
  do 2 rewrite PolymorphicEqElim.
  remember (freeFA _ _) as F; clear HeqF.
  remember [seq OutReform i | i <- [seq t i0 | i0 <- cRange 0 F]] as L;
  transitivity (length [seq OutReform i | i <- [seq t i0 | i0 <- cRange 0 F]]);[
  |do 2 rewrite map_length; apply (length_cRange (n := 0) (m := F))].
  transitivity (length L);[clear HeqL|hauto].
  elim: L;[auto|].
  move=> [d [b x]] L IH.
  qauto use: map_length q:on.
Qed.
Next Obligation. apply PolyConvertFreeCaseLem. Qed.

Lemma PolyConvertExiCaseLem {ctx} {D : @PolyConversionData ctx} {i : |[exiF ctx]|} {B} {e} :
  newExiFCalls D i < newExiFCalls (ExiCallIncorp D i B e) i.
Proof.
  destruct D; simpl.
  unfold AddCall.
  unfold SingleCall.
  rewrite dep_if_case_true;[by rewrite EEConvert|].
  hauto use: ltnSn, addn1, contra_ltn_leq.
Qed.

Program Definition PolyConvertExiCase {ctx} 
  (i : |[exiF ctx]|) 
  (t : |[exiFA ctx i]| ->
    { d : @PolyConversionData ctx &  
    @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d |} }) :
  { d : @PolyConversionData ctx &  
    @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d |} } := 
  (* We start with a function name and a list of data and constraints that needs to be fused together *)
  (* The first thing we need to do is fuse this list of data into a single peice of data*)
  let rs : seq {d : @PolyConversionData ctx 
                  & @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d |} } 
         := [seq t i | i <- cRange 0 (exiFA ctx i) ] in
  let data : @PolyConversionData ctx := foldr PolyConversionCombineData PolyConversionEmptyData [seq projT1 i | i <- rs] in

  (* We also need consolidate all the polynomial constraints into a single list and add those to the data*)
  let polys : seq (@SemicircuitPolyConstraint {| subCtx := ctx
                      ; freeFC := newFreeFCalls data
                      ; exiFC := newExiFCalls data |})
               := eq_rect _ (fun x => seq (@SemicircuitPolyConstraint {| subCtx := _; freeFC := _; exiFC := x |})) (
                  eq_rect _ (fun x => seq (@SemicircuitPolyConstraint {| subCtx := _; freeFC := x; exiFC := _ |})) 
                  (PolyCallSeqFuse (map OutReform rs)) _ _) _ _ in
  let data2 : @PolyConversionData ctx := ExiCallIncorp data i polys _ in

  (*We return a call the the most recently added function *)
  existT _ data2 (PolyConsExiF i (newExiFCalls data i)).
Next Obligation.
  apply functional_extensionality.
  elim: [seq t i0 | i0 <- cRange 0 _]; auto.
  move=> [d p] l IH x.
  transitivity ((projT1 (OutReform (existT _ d p)) x) + sumn [seq projT1 i x | i <- [seq OutReform j | j <- l]]); auto.
  rewrite IH.
  destruct d, x.
  by simpl; destruct (foldr PolyConversionCombineData PolyConversionEmptyData [seq projT1 i0 | i0 <- l]).
Qed.
Next Obligation.
  apply functional_extensionality.
  elim: [seq t i0 | i0 <- cRange 0 _]; auto.
  move=> [d p] l IH x.
  transitivity ((projT1 (projT2 (OutReform (existT _ d p))) x) + sumn [seq projT1 (projT2 i) x | i <- [seq OutReform j | j <- l]]); auto.
  rewrite IH.
  destruct d, x.
  by simpl; destruct (foldr PolyConversionCombineData PolyConversionEmptyData [seq projT1 i0 | i0 <- l]).
Qed.
Next Obligation.
  do 2 rewrite PolymorphicEqElim.
  remember (exiFA _ _) as F; clear HeqF.
  remember [seq OutReform i | i <- [seq t i0 | i0 <- cRange 0 F]] as L;
  transitivity (length [seq OutReform i | i <- [seq t i0 | i0 <- cRange 0 F]]);[
  |do 2 rewrite map_length; apply (length_cRange (n := 0) (m := F))].
  transitivity (length L);[clear HeqL|hauto].
  elim: L;[auto|].
  move=> [d [b x]] L IH.
  qauto use: map_length q:on.
Qed.
Next Obligation. apply PolyConvertExiCaseLem. Qed.

(*Construct a polynomial constraint, new calls within that constraint, simultanious with data to modify a semicircuit *)
Program Fixpoint PolyConvert {ctx} (r : @PolyTerm ctx) :
  { d : @PolyConversionData ctx &  
    @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d |} } := 
  match r with
  | PolyFVar m => existT _ PolyConversionEmptyData (PolyConsFreeV m)
  | PolyEVar m => existT _ PolyConversionEmptyData (PolyConsExiV m)
  | PolyUVar m => existT _ PolyConversionEmptyData (PolyConsUniV m)
  | PolyFFun i t => PolyConvertFreeCase i (fun x => PolyConvert (t x))
  | PolyEFun i t => PolyConvertExiCase i (fun x => PolyConvert (t x))
  | PolyMinusOne => existT _ PolyConversionEmptyData PolyConsMinusOne
  | PolyPlusOne => existT _ PolyConversionEmptyData PolyConsPlusOne
  | PolyZero => existT _ PolyConversionEmptyData PolyConsZero
  | PolyPlus r1 r2 => 
    let (d1, p1) := PolyConvert r1 in
    let (d2, p2) := PolyConvert r2 in
    existT _ (PolyConversionCombineData d1 d2)
             (PolyConsPlus (PolyCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) p1) 
                           (PolyCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) p2))
  | PolyTimes r1 r2 => 
    let (d1, p1) := PolyConvert r1 in
    let (d2, p2) := PolyConvert r2 in
    existT _ (PolyConversionCombineData d1 d2)
             (PolyConsTimes (PolyCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) p1) 
                            (PolyCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) p2))
  | PolyInd r1 r2 => 
    let (d1, p1) := PolyConvert r1 in
    let (d2, p2) := PolyConvert r2 in
    existT _ (PolyConversionCombineData d1 d2)
             (PolyConsInd (PolyCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) p1) 
                          (PolyCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) p2))
  end.
Next Obligation. by f_equal; apply functional_extensionality;move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; apply functional_extensionality;move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; apply functional_extensionality;move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; apply functional_extensionality;move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; apply functional_extensionality;move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; apply functional_extensionality;move=>[x ltx];destruct d1, d2. Qed.


(*Convert constraint to one with new function with no calls*)
Fixpoint PropCallCast {ctx}
    {newFC : |[freeFS ctx]| -> nat}
    {newEC : |[exiFS ctx]| -> nat}
    (p : @SemicircuitPropConstraint ctx) :
    @SemicircuitPropConstraint {| subCtx := subCtx ctx
                               ; freeFC := fun x => freeFC ctx x + newFC x
                               ; exiFC := fun x => exiFC ctx x + newEC x|} := 
  match p with
  | ZOConsNot p =>
    let r := PropCallCast p in
    ZOConsNot r
  | ZOConsAnd p1 p2 =>
    let r1 := PropCallCast p1 in
    let r2 := PropCallCast p2 in
    ZOConsAnd r1 r2
  | ZOConsOr p1 p2 =>
    let r1 := PropCallCast p1 in
    let r2 := PropCallCast p2 in
    ZOConsOr r1 r2
  | ZOConsImp p1 p2 =>
    let r1 := PropCallCast p1 in
    let r2 := PropCallCast p2 in
    ZOConsImp r1 r2
  | ZOConsEq p1 p2 =>
    let r1 := PolyCallCast p1 in
    let r2 := PolyCallCast p2 in
    ZOConsEq r1 r2
  end.

Fixpoint PropCallLift {ctx}
    {newFC : |[freeFS ctx]| -> nat}
    {newEC : |[exiFS ctx]| -> nat}
    (p : @SemicircuitPropConstraint ctx) :
    @SemicircuitPropConstraint {| subCtx := subCtx ctx
                               ; freeFC := fun x => newFC x + freeFC ctx x
                               ; exiFC := fun x => newEC x + exiFC ctx x|} := 
  match p with
  | ZOConsNot p =>
    let r := PropCallLift p in
    ZOConsNot r
  | ZOConsAnd p1 p2 =>
    let r1 := PropCallLift p1 in
    let r2 := PropCallLift p2 in
    ZOConsAnd r1 r2
  | ZOConsOr p1 p2 =>
    let r1 := PropCallLift p1 in
    let r2 := PropCallLift p2 in
    ZOConsOr r1 r2
  | ZOConsImp p1 p2 =>
    let r1 := PropCallLift p1 in
    let r2 := PropCallLift p2 in
    ZOConsImp r1 r2
  | ZOConsEq p1 p2 =>
    let r1 := PolyCallLift p1 in
    let r2 := PolyCallLift p2 in
    ZOConsEq r1 r2
  end.

(*Construct a proposition constraint, new calls within that constraint, simultanious with data to modify a semicircuit *)
Program Fixpoint PropConvert {ctx} (r : @ZerothOrderFormula ctx) :
  { d : @PolyConversionData ctx &  
    @SemicircuitPropConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d |} } := 
  match r with
  | ZONot f => 
    let (d, p) := PropConvert f in
    existT _ d (ZOConsNot p)
  | ZOAnd f1 f2 => 
    let (d1, p1) := PropConvert f1 in
    let (d2, p2) := PropConvert f2 in
    existT _ (PolyConversionCombineData d1 d2)
             (ZOConsAnd (PropCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) p1) 
                        (PropCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) p2))
  | ZOOr f1 f2 => 
    let (d1, p1) := PropConvert f1 in
    let (d2, p2) := PropConvert f2 in
    existT _ (PolyConversionCombineData d1 d2)
             (ZOConsOr (PropCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) p1) 
                       (PropCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) p2))
  | ZOImp f1 f2 => 
    let (d1, p1) := PropConvert f1 in
    let (d2, p2) := PropConvert f2 in
    existT _ (PolyConversionCombineData d1 d2)
             (ZOConsImp (PropCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) p1) 
                        (PropCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) p2))
  | ZOEq r1 r2 => 
    let (d1, p1) := PolyConvert r1 in
    let (d2, p2) := PolyConvert r2 in
    existT _ (PolyConversionCombineData d1 d2)
             (ZOConsEq (PolyCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) p1) 
                       (PolyCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) p2))
  end.
Next Obligation. by f_equal; apply functional_extensionality;move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; apply functional_extensionality;move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; apply functional_extensionality;move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; apply functional_extensionality;move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; apply functional_extensionality;move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; apply functional_extensionality;move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; apply functional_extensionality;move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; apply functional_extensionality;move=>[x ltx];destruct d1, d2. Qed.

(*Integrate generated polynomial constraint data into a semicircuit*)
Program Definition IntegrateConversionData
  (c : SemiCircuit)
  (d : @PolyConversionData (subCtx (Ctx c))) : SemiCircuit :=
  {| Ctx := {| subCtx := subCtx (Ctx c) 
              ; freeFC := fun x => freeFCalls c x + newFreeFCalls d x
              ; exiFC := fun x => exiFCalls c x + newExiFCalls d x|}
    ; nu := nu c
    ; polyConstraints := map (PolyCallCast) (polyConstraints c) ++ map PolyCallLift (newPolys d)
    ; freeFArgs := fun i (j : |[freeFCalls c i + newFreeFCalls d i]|) =>
      (if j < freeFCalls c i as b return (j < freeFCalls c i) = b -> |[freeFArity c i]| -> |[length (map PolyCallCast (polyConstraints c) ++ map PolyCallLift (newPolys d))]|
      then fun _ => freeFArgs c i j
      else fun _ x => length (polyConstraints c) 
                    + newFreeArgs d i (j - freeFCalls c i) x) (erefl _)
    ; exiFArgs := fun i (j : |[exiFCalls c i + newExiFCalls d i]|) =>
      (if j < exiFCalls c i as b return (j < exiFCalls c i) = b -> |[exiFArity c i]| -> |[length (map PolyCallCast (polyConstraints c) ++ map PolyCallLift (newPolys d))]|
      then fun _ => exiFArgs c i j
      else fun _ x => length (polyConstraints c) 
                    + newExiArgs d i (j - exiFCalls c i) x) (erefl _)
    ; uniVBounds := uniVBounds c
    ; exiVBounds := exiVBounds c
    ; exiFOutputBounds := exiFOutputBounds c
    ; exiFInputBounds := exiFInputBounds c
    ; formula := inrMap PropCallCast (formula c)
  |}.
Next Obligation.
  destruct (freeFArgs _ _).
  change (length ?n) with (size n); rewrite size_cat; do 2 rewrite size_map; change (size ?n) with (length n).
  qauto use: leq_addl, ltn_addr, addSnnS.
Qed.
Next Obligation.
  remember (freeFCalls _ _) as F; clear HeqF.
  by assert (~ (j < F));[ hauto
                        | assert (F <= j);[ apply (contra_not_leq (P := j < F))
                                          | qauto use: ltn_subLR]].
Qed.
Next Obligation.
  destruct (newFreeArgs _ _).
  change (length ?n) with (size n); rewrite size_cat; do 2 rewrite size_map; change (size ?n) with (length n).
  by rewrite ltn_add2l.
Qed.
Next Obligation.
  destruct (exiFArgs _ _).
  change (length ?n) with (size n); rewrite size_cat; do 2 rewrite size_map; change (size ?n) with (length n).
  by apply ltn_addr.
Qed.
Next Obligation.
  remember (exiFCalls _ _) as F; clear HeqF.
  by assert (~ (j < F));[ hauto
                        | assert (F <= j);[ apply (contra_not_leq (P := j < F))
                                          | qauto use: ltn_subLR]].
Qed.
Next Obligation.
  destruct (newExiArgs _ _).
  change (length ?n) with (size n); rewrite size_cat; do 2 rewrite size_map; change (size ?n) with (length n).
  simpl.
  by rewrite ltn_add2l.
Qed.
Next Obligation. 
  destruct (uniVBounds _ _).
  change (length ?n) with (size n); rewrite size_cat; do 2 rewrite size_map; change (size ?n) with (length n).
  by apply ltn_addr.
Qed.
Next Obligation. 
  destruct (exiVBounds _ _).
  change (length ?n) with (size n); rewrite size_cat; do 2 rewrite size_map; change (size ?n) with (length n).
  by apply ltn_addr.
Qed.
Next Obligation. 
  destruct (exiFOutputBounds _ _).
  change (length ?n) with (size n); rewrite size_cat; do 2 rewrite size_map; change (size ?n) with (length n).
  by apply ltn_addr.
Qed.
Next Obligation. 
  destruct (exiFInputBounds _ _).
  change (length ?n) with (size n); rewrite size_cat; do 2 rewrite size_map; change (size ?n) with (length n).
  by apply ltn_addr.
Qed.

Definition Translate_ZerothOrderFormula 
  (c : SemiCircuit)
  (f : @ZerothOrderFormula (subCtx (Ctx c))) : SemiCircuit :=
  let (d, p) := PropConvert f in
  let c0 := IntegrateConversionData c d in
  {| Ctx := Ctx c0
   ; nu := nu c0
   ; polyConstraints := polyConstraints c0
   ; freeFArgs := freeFArgs c0
   ; exiFArgs := exiFArgs c0
   ; uniVBounds := uniVBounds c0
   ; exiVBounds := exiVBounds c0
   ; exiFOutputBounds := exiFOutputBounds c0
   ; exiFInputBounds := exiFInputBounds c0
   ; formula := inr (PropCallLift p)
  |}.

Program Fixpoint PolyLiftExiV {ctx}
  (p : @SemicircuitPolyConstraint ctx) :
    @SemicircuitPolyConstraint {| subCtx := incExiV (subCtx ctx)
                                ; freeFC := freeFC ctx
                                ; exiFC := exiFC ctx|} := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyLiftExiV p1 in
    let r2 := PolyLiftExiV p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyLiftExiV p1 in
    let r2 := PolyLiftExiV p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd p1 p2 =>
    let r1 := PolyLiftExiV p1 in
    let r2 := PolyLiftExiV p2 in 
    PolyConsInd r1 r2
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsExiV i => PolyConsExiV i.+1
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF i j
  end.
Next Obligation. by destruct (subCtx ctx). Qed. Next Obligation. by destruct (subCtx ctx). Qed.
Next Obligation. by unfold freeVS in *; simpl; destruct (subCtx ctx). Qed. 
Next Obligation. by unfold exiVS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation. by unfold uniVS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation. by clear H; unfold freeFS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation.
  remember (PolyLiftExiV_obligation_1 _ _) as P; clear HeqP; simpl in P.
  replace P with H0; auto.
  apply eq_irrelevance.
Qed.
Next Obligation. by clear H; unfold exiFS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation.
  remember (PolyLiftExiV_obligation_2 _ _) as P; clear HeqP; simpl in P.
  replace P with H0; auto.
  apply eq_irrelevance.
Qed.

Program Fixpoint PropLiftExiV {ctx}
  (p : @SemicircuitPropConstraint ctx) :
  @SemicircuitPropConstraint {| subCtx := incExiV (subCtx ctx)
                              ; freeFC := freeFC ctx
                              ; exiFC := exiFC ctx|} := 
  match p with
  | ZOConsNot p =>
    let r := PropLiftExiV p in
    ZOConsNot r
  | ZOConsAnd p1 p2 =>
    let r1 := PropLiftExiV p1 in
    let r2 := PropLiftExiV p2 in
    ZOConsAnd r1 r2
  | ZOConsOr p1 p2 =>
    let r1 := PropLiftExiV p1 in
    let r2 := PropLiftExiV p2 in
    ZOConsOr r1 r2
  | ZOConsImp p1 p2 =>
    let r1 := PropLiftExiV p1 in
    let r2 := PropLiftExiV p2 in
    ZOConsImp r1 r2
  | ZOConsEq p1 p2 =>
    let r1 := PolyLiftExiV p1 in
    let r2 := PolyLiftExiV p2 in
    ZOConsEq r1 r2
  end.

Program Fixpoint PolyLiftUniV {ctx}
  (p : @SemicircuitPolyConstraint ctx) :
    @SemicircuitPolyConstraint {| subCtx := incUniV (subCtx ctx)
                                ; freeFC := freeFC ctx
                                ; exiFC := exiFC ctx|} := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyLiftUniV p1 in
    let r2 := PolyLiftUniV p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyLiftUniV p1 in
    let r2 := PolyLiftUniV p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd p1 p2 =>
    let r1 := PolyLiftUniV p1 in
    let r2 := PolyLiftUniV p2 in 
    PolyConsInd r1 r2
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsExiV i => PolyConsExiV i
  | PolyConsUniV i => PolyConsUniV i.+1
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF i j
  end.
Next Obligation. by destruct (subCtx ctx). Qed. Next Obligation. by destruct (subCtx ctx). Qed.
Next Obligation. by unfold freeVS in *; simpl; destruct (subCtx ctx). Qed. 
Next Obligation. by unfold exiVS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation. by unfold uniVS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation. by clear H; unfold freeFS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation.
  remember (PolyLiftUniV_obligation_1 _ _) as P; clear HeqP; simpl in P.
  replace P with H0; auto.
  apply eq_irrelevance.
Qed.
Next Obligation. by clear H; unfold exiFS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation.
  remember (PolyLiftUniV_obligation_2 _ _) as P; clear HeqP; simpl in P.
  replace P with H0; auto.
  apply eq_irrelevance.
Qed.

Program Fixpoint PropLiftUniV {ctx}
  (p : @SemicircuitPropConstraint ctx) :
  @SemicircuitPropConstraint {| subCtx := incUniV (subCtx ctx)
                              ; freeFC := freeFC ctx
                              ; exiFC := exiFC ctx|} := 
  match p with
  | ZOConsNot p =>
    let r := PropLiftUniV p in
    ZOConsNot r
  | ZOConsAnd p1 p2 =>
    let r1 := PropLiftUniV p1 in
    let r2 := PropLiftUniV p2 in
    ZOConsAnd r1 r2
  | ZOConsOr p1 p2 =>
    let r1 := PropLiftUniV p1 in
    let r2 := PropLiftUniV p2 in
    ZOConsOr r1 r2
  | ZOConsImp p1 p2 =>
    let r1 := PropLiftUniV p1 in
    let r2 := PropLiftUniV p2 in
    ZOConsImp r1 r2
  | ZOConsEq p1 p2 =>
    let r1 := PolyLiftUniV p1 in
    let r2 := PolyLiftUniV p2 in
    ZOConsEq r1 r2
  end.

(*Add a new existentially quantified first order variable to semicircuit *)
Program Definition SemicircuitExiInc (c : SemiCircuit) (p : @SemicircuitPolyConstraint (Ctx c)): SemiCircuit :=
  {| Ctx := {| subCtx := incExiV (subCtx (Ctx c))
              ; freeFC := freeFC (Ctx c)
              ; exiFC := exiFC (Ctx c)|}
  ; nu := fun i =>
    (if i == 0 as b return (i == 0) = b -> nat
     then fun _ => uniV (subCtx (Ctx c))
     else fun _ => nu c (i.-1)) (erefl _)
  ; polyConstraints := map PolyLiftExiV (rcons (polyConstraints c) p)
  ; freeFArgs := freeFArgs c
  ; exiFArgs := exiFArgs c
  ; uniVBounds := uniVBounds c
  ; exiVBounds := fun i =>
    (if i == 0 as b return (i == 0) = b -> |[length (map PolyLiftExiV (rcons (polyConstraints c) p))]|
    then fun _ => length (polyConstraints c)
    else fun _ => exiVBounds c (i.-1)) (erefl _)
  ; exiFOutputBounds := exiFOutputBounds c
  ; exiFInputBounds := exiFInputBounds c
  ; formula := inrMap PropLiftExiV (formula c)
  |}.
Next Obligation.
  remember (PolyLiftExiV_obligation_1 _ _) as P; clear HeqP; simpl in P.
  destruct c, Ctx0, subCtx0; simpl in *.
  replace P with H1;auto.
  apply eq_irrelevance.
Qed.
Next Obligation.
  destruct (freeFArgs _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation.
  remember (PolyLiftExiV_obligation_2 _ _) as P; clear HeqP; simpl in P.
  destruct c, Ctx0, subCtx0; simpl in *.
  replace P with H1;auto.
  apply eq_irrelevance.
Qed.
Next Obligation.
  destruct (exiFArgs _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct c, Ctx0, subCtx0. Qed.
Next Obligation.
  destruct (uniVBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct c, Ctx0, subCtx0. Qed.
Next Obligation.
  destruct (exiFOutputBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct c, Ctx0, subCtx0. Qed.
Next Obligation.
  remember (SemicircuitExiInc_obligation_9 _ _ _) as P; clear HeqP; simpl in P.
  destruct c, Ctx0, subCtx0; simpl in *.
  replace P with H0;auto.
  apply eq_irrelevance.
Qed.
Next Obligation.
  destruct (exiFInputBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct c, Ctx0, subCtx0. Qed.
Next Obligation.
  assert ((i == 0) = false);[exact e|clear e].
  destruct c, Ctx0, subCtx0; simpl in *.
  unfold exiVS, exiVN, Ctx, exiVS, subCtx, Sigma_1_1.exiV in *.
  assert (i <> 0);[by rewrite <- EEFConvert|].
  by destruct i;[fcrush|].
Qed.
Next Obligation.
  change (exist _ ?x _ == exist _ ?y _) with (x == y).
  dep_if_case (i == 0); auto.
  by destruct (Ctx c), subCtx0.
  destruct ((` (nu c)) _).
  clear H.
  by destruct c, Ctx0, subCtx0.
Qed.
Next Obligation.
  change (exist _ ?x _ == exist _ ?y _) with (x == y).
  dep_if_case (j == 0); auto.
  assert (j = 0);[by rewrite <- EEConvert|].
  assert (i = 0). rewrite H3 in H;destruct i;[auto|fcrush].
  rewrite <- EEConvert in H4.
  rewrite dep_if_case_true; auto.
  dep_if_case (i == 0); auto.
  destruct (` (nu c) _).
  by destruct c, Ctx0, subCtx0.
  destruct (nu c).
  simpl.
  apply i0.
  simpl.
  destruct i, j;auto.
Qed.
Next Obligation. by destruct (exiVS _);[fcrush|]. Qed.
Next Obligation. 
  assert ((i == 0) = false);[exact e|clear e].
  destruct c, Ctx0, subCtx0; simpl in *.
  unfold exiVS, exiVN, Ctx, exiVS, subCtx, Sigma_1_1.exiV in *.
  assert (i <> 0);[by rewrite <- EEFConvert|].
  by destruct i;[fcrush|].
Qed.
Next Obligation. 
  destruct (exiVBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. rewrite map_length length_rcons; sfirstorder. Qed.

(*Add a new universally quantified first order variable to semicircuit *)
Program Definition SemicircuitUniInc (c : SemiCircuit) (p : @SemicircuitPolyConstraint (Ctx c)): SemiCircuit :=
  {| Ctx := {| subCtx := incUniV (subCtx (Ctx c))
              ; freeFC := freeFC (Ctx c)
              ; exiFC := exiFC (Ctx c)|}
  ; nu := nu c
  ; polyConstraints := map PolyLiftUniV (rcons (polyConstraints c) p)
  ; freeFArgs := freeFArgs c
  ; exiFArgs := exiFArgs c
  ; uniVBounds := fun i =>
    (if i == 0 as b return (i == 0) = b -> |[length (map PolyLiftUniV (rcons (polyConstraints c) p))]|
    then fun _ => length (polyConstraints c)
    else fun _ => uniVBounds c (i.-1)) (erefl _)
  ; exiVBounds := exiVBounds c
  ; exiFOutputBounds := exiFOutputBounds c
  ; exiFInputBounds := exiFInputBounds c
  ; formula := inrMap PropLiftUniV (formula c)
  |}.
Next Obligation. by destruct c, Ctx0, subCtx0. Qed.
Next Obligation.
  destruct (` (nu c)).
  clear H.  
  by destruct c, Ctx0, subCtx0; apply leqW.
Qed.
Next Obligation.
  destruct (nu c).
  by apply i0.
Qed.
Next Obligation.
  remember (PolyLiftUniV_obligation_1 _ _) as P; clear HeqP; simpl in P.
  destruct c, Ctx0, subCtx0; simpl in *.
  replace P with H1;auto.
  apply eq_irrelevance.
Qed.
Next Obligation.
  destruct (freeFArgs _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation.
  remember (PolyLiftUniV_obligation_2 _ _) as P; clear HeqP; simpl in P.
  destruct c, Ctx0, subCtx0; simpl in *.
  replace P with H1;auto.
  apply eq_irrelevance.
Qed.
Next Obligation.
  destruct (exiFArgs _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct c, Ctx0, subCtx0. Qed.
Next Obligation.
  destruct (exiVBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct c, Ctx0, subCtx0. Qed.
Next Obligation.
  destruct (exiFOutputBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct c, Ctx0, subCtx0. Qed.
Next Obligation.
  remember (SemicircuitUniInc_obligation_12 _ _ _) as P; clear HeqP; simpl in P.
  destruct c, Ctx0, subCtx0; simpl in *.
  replace P with H0;auto.
  apply eq_irrelevance.
Qed.
Next Obligation.
  destruct (exiFInputBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct c, Ctx0, subCtx0. Qed.
Next Obligation.
  assert ((i == 0) = false);[exact e|clear e].
  destruct c, Ctx0, subCtx0; simpl in *.
  unfold exiVS, exiVN, Ctx, exiVS, subCtx, Sigma_1_1.exiV in *.
  assert (i <> 0);[by rewrite <- EEFConvert|].
  by destruct i;[fcrush|].
Qed.
Next Obligation.
  destruct (uniVBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. rewrite map_length length_rcons; sfirstorder. Qed.

Fixpoint Translate_FirstOrderFormula 
  (c : SemiCircuit)
  (f : @FirstOrderFormula (subCtx (Ctx c))) : SemiCircuit :=
  match f with
  | ZO f => Translate_ZerothOrderFormula c f
  | FOExists b f =>
    let (da, bo) := PolyConvert b in
    let c0 := IntegrateConversionData c da in
    let c1 := SemicircuitExiInc c0 (PolyCallLift bo) in
    Translate_FirstOrderFormula c1 f
  | FOForall b f => 
    let (da, bo) := PolyConvert b in
    let c0 := IntegrateConversionData c da in
    let c1 := SemicircuitUniInc c0 (PolyCallLift bo) in
    Translate_FirstOrderFormula c1 f
  end.

Program Fixpoint PolyLiftAddExiF {ctx}
  (a : nat)
  (p : @SemicircuitPolyConstraint ctx) :
    @SemicircuitPolyConstraint {| subCtx := addExiF a (subCtx ctx)
                                ; freeFC := freeFC ctx
                                ; exiFC := fun i =>
          ( if i == 0 as b return (i == 0) = b -> nat
            then fun _ => 0
            else fun _ => exiFC ctx (i.-1) ) (erefl _)
    |} := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyLiftAddExiF a p1 in
    let r2 := PolyLiftAddExiF a p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyLiftAddExiF a p1 in
    let r2 := PolyLiftAddExiF a p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd p1 p2 =>
    let r1 := PolyLiftAddExiF a p1 in
    let r2 := PolyLiftAddExiF a p2 in 
    PolyConsInd r1 r2
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsExiV i => PolyConsExiV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF (i.+1) j
  end.
Next Obligation. by destruct (subCtx ctx). Qed.
Next Obligation. destruct (exiF (addExiF a (subCtx ctx)));[fcrush|auto]. Qed.
Next Obligation.
  assert (i <> 0);[by rewrite <- EEFConvert|clear e].
  destruct i;[fcrush|].
  simpl.
  by destruct (subCtx ctx).
Qed.
Next Obligation. by unfold freeVS in *; simpl; destruct (subCtx ctx). Qed. 
Next Obligation. by unfold exiVS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation. by unfold uniVS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation. by clear H; unfold freeFS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation.
  remember (PolyLiftAddExiF_obligation_1 _ _ _) as P; clear HeqP; simpl in P.
  replace P with H0; auto.
  apply eq_irrelevance.
Qed.
Next Obligation. by clear H; unfold exiFS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation.
  remember (PolyLiftAddExiF_obligation_3 _ _ _ _) as P; clear HeqP; simpl in P.
  replace P with H0; auto.
  apply eq_irrelevance.
Qed.

Program Fixpoint PropLiftAddExiF {ctx}
  (a : nat)
  (p : @SemicircuitPropConstraint ctx) :
    @SemicircuitPropConstraint {| subCtx := addExiF a (subCtx ctx)
                                ; freeFC := freeFC ctx
                                ; exiFC := fun i =>
          ( if i == 0 as b return (i == 0) = b -> nat
            then fun _ => 0
            else fun _ => exiFC ctx (i.-1) ) (erefl _)
    |} := 
  match p with
  | ZOConsNot p =>
    let r := PropLiftAddExiF a p in
    ZOConsNot r
  | ZOConsAnd p1 p2 =>
    let r1 := PropLiftAddExiF a p1 in
    let r2 := PropLiftAddExiF a p2 in
    ZOConsAnd r1 r2
  | ZOConsOr p1 p2 =>
    let r1 := PropLiftAddExiF a p1 in
    let r2 := PropLiftAddExiF a p2 in
    ZOConsOr r1 r2
  | ZOConsImp p1 p2 =>
    let r1 := PropLiftAddExiF a p1 in
    let r2 := PropLiftAddExiF a p2 in
    ZOConsImp r1 r2
  | ZOConsEq p1 p2 =>
    let r1 := PolyLiftAddExiF a p1 in
    let r2 := PolyLiftAddExiF a p2 in
    ZOConsEq r1 r2
  end.

Program Definition SemicircuitExiFAdd 
  (c : SemiCircuit) 
  (y : @SemicircuitPolyConstraint (Ctx c))
  (bs : seq (@SemicircuitPolyConstraint (Ctx c))) : SemiCircuit :=
  {| Ctx := {| subCtx := addExiF (length bs) (subCtx ctx)
                                ; freeFC := freeFC ctx
                                ; exiFC := fun i =>
          ( if i == 0 as b return (i == 0) = b -> nat
            then fun _ => 0
            else fun _ => exiFC ctx (i.-1) ) (erefl _)
          |}
  ; nu := nu c
  ; polyConstraints := map (PolyLiftExiV (length bs)) (rcons (polyConstraints c) p)
  ; freeFArgs := freeFArgs c
  ; exiFArgs := exiFArgs c
  ; uniVBounds := uniVBounds c
  ; exiVBounds := 
  ; exiFOutputBounds := fun i =>
    (if i == 0 as b return (i == 0) = b -> |[length (map PolyLiftExiV (rcons (polyConstraints c) p))]|
    then fun _ => ???
    else fun _ => exiFOutputBounds c (i.-1)) (erefl _)
  ; exiFInputBounds := fun i =>
    (if i == 0 as b return (i == 0) = b -> |[length (map PolyLiftExiV (rcons (polyConstraints c) p))]|
    then fun _ => ???
    else fun _ => exiFInputBounds c (i.-1)) (erefl _)
  ; formula := inrMap PropLiftExiV (formula c)
  |}.


Program Fixpoint Translate_SecondOrderFormula 
  (c : SemiCircuit)
  (f : @SecondOrderFormula (subCtx (Ctx c))) : SemiCircuit :=
  match f with
  | FO f => Translate_FirstOrderFormula c f
  | SOExists y bs f => 
    let (day, boy) := PolyConvert y in
    let c0 := IntegrateConversionData c day in
    let boy0 : @SemicircuitPolyConstraint (Ctx c0) := PolyCallLift boy in
    let bs' := map PolyConvert bs in
    let dabs := foldr PolyConversionCombineData PolyConversionEmptyData [seq projT1 i | i <- bs'] in
    let c1 := IntegrateConversionData c0 dabs in
    let boy1 : @SemicircuitPolyConstraint (Ctx c1) := PolyCallCast boy0 in
    let bobs := PolyCallSeqFuse (map OutReform bs') in
    let bobs1 : seq (@SemicircuitPolyConstraint (Ctx c1))
             := Hole in
    let c2 := SemicircuitExiFAdd c1 boy1 bobs1 in
    Translate_SecondOrderFormula c2 f
  end.