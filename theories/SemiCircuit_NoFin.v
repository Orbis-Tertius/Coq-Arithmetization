From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun zmodp ssrbool ssrnat ssralg seq fintype finalg tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.
From Coq Require Import ClassicalChoice.

Require Import CoqArith.Utils.

Require Import CoqArith.Sigma_1_1.
Require Import CoqArith.Prenex.
Require Import Program.

Section SemicircuitDef.

Variable (FSize : nat).

(* Record SemicircuitCtx {subCtx : Sigma11Ctx} := mkSemicircuitCtx
  { freeFC : |[freeF subCtx]| -> nat (*Number of free function calls*)
  ; exiFC : |[exiF subCtx]| -> nat (*Number of exi function calls*)
  ; indC : nat (*Number of ind function calls*)
  }. *)

(* <P> in the paper *)
Inductive SCPoly {E : seq nat} : Type :=
| PolyConsUndef : SCPoly
| PolyConsZero : SCPoly
| PolyConsPlusOne : SCPoly
| PolyConsMinusOne : SCPoly
| PolyConsPlus : SCPoly -> SCPoly -> SCPoly
| PolyConsTimes : SCPoly -> SCPoly -> SCPoly
| PolyConsInd : nat -> SCPoly
| PolyConsFreeV : nat -> SCPoly
| PolyConsUniV : nat -> SCPoly
| PolyConsFreeF : forall i j : nat, SCPoly
| PolyConsExiF : forall (i : |[length E]|), nat -> SCPoly.

(* <S> in the paper *)
Inductive SCProp {E} : Type :=
| ZOConsNot : SCProp -> SCProp
| ZOConsAnd : SCProp -> SCProp -> SCProp
| ZOConsOr : SCProp -> SCProp -> SCProp
| ZOConsImp : SCProp -> SCProp -> SCProp
| ZOConsEq : @SCPoly E -> @SCPoly E -> SCProp.

Record SemiCircuit {E} : Type :=
  mkSemiCircuit {
    (* nu : {s : |[exiV ctx]| -> { m : nat | m <= uniV ctx } | forall i j : |[exiV ctx]|, (` i) <= (` j) -> (` (s j)) <= (` (s i))}; *)
    indArgs0 : nat -> (@SCPoly E * @SCPoly E);
    indArgsS : forall x : |[length E]|, 
               nat -> (@SCPoly E * @SCPoly E );
    (* w in paper *)
    freeFArgs0 : forall i a : nat, nat -> (|[a]| -> @SCPoly E);
    freeFArgsS : forall x : |[length E]|, 
                 forall i a j: nat, (|[a]| -> @SCPoly E);
    (* omega in paper *)
    exiArgs0 : forall i, nat -> (|[lnth E i]| -> @SCPoly E);
    exiArgsS : forall x : |[length E]|, 
                 forall i, nat -> (|[lnth E i]| -> @SCPoly E);
    (* V in paper *)
    uniVBoundsSC : seq (@SCPoly E);
    (* S, G and B in paper *)
    exiFBoundsSC : forall i, (|[lnth E i]| -> @SCPoly E) * @SCPoly E;
    formulaSC : @SCProp E
  }.

(* Record SCInstance {ctx} {R : RingData} {c : @SemicircuitCtx ctx} : Type :=
  mkSCInstance { 
    (* v in paper *)
    freeVInst : |[freeV ctx]| -> T R;
    (* f in paper *)
    freeFInst : forall i : |[freeF ctx]|, (|[freeFA ctx i]| -> T R) -> option 'F_FSize;
  }. *)

Record SCAdvice {E} {M : @Sigma11Model FSize} : Type :=
  mkSCAdvice { 
    (* s and g in paper *)
    exiAdv : forall i, (|[lnth E i]| -> 'F_FSize) -> option 'F_FSize;
    (*Arguments are: which bound, which call*)
    indCallOut0 : nat -> (nat -> 'F_FSize) -> option 'F_FSize;
    indCallOutS : forall x : |[length E]|, nat -> (nat -> 'F_FSize) -> option 'F_FSize;
    (* sigma in paper *)
    (*Arguments are: which bound, which function, which call*)
    exiCallOut0 : forall i j : nat, (nat -> 'F_FSize) -> option 'F_FSize;
    exiCallOutS : forall x : |[length E]|, forall i j : nat, (nat -> 'F_FSize) -> option 'F_FSize;
    (* o in paper *)
    (*Arguments are: which bound, which function, which call*)
    freeFCallOut0 : forall i j : nat, (nat -> 'F_FSize) -> option 'F_FSize;
    freeFCallOutS : forall x : |[length E]|, forall i j : nat, (nat -> 'F_FSize) -> option 'F_FSize;
  }.

Fixpoint SCPolyDenotation0 {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  (p : @SCPoly E) :
  (nat -> 'F_FSize) -> option 'F_FSize :=
  match p with
  | PolyConsUndef => fun _ => None
  | PolyConsZero => fun _ => Some 0%R
  | PolyConsPlusOne => fun _ => Some 1%R
  | PolyConsMinusOne => fun _ => Some (-1)%R
  | PolyConsPlus p1 p2 => fun u =>
    let r1 := SCPolyDenotation0 adv p1 u in
    let r2 := SCPolyDenotation0 adv p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) r2) r1
  | PolyConsTimes p1 p2 => fun u =>
    let r1 := SCPolyDenotation0 adv p1 u in
    let r2 := SCPolyDenotation0 adv p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) r2) r1
  | PolyConsInd i => indCallOut0 adv i
  | PolyConsFreeV i => fun _ => Some (V_F _ M i)
  | PolyConsUniV i => fun u => Some (u i)
  | PolyConsFreeF i j => freeFCallOut0 adv i j
  | PolyConsExiF i j => exiCallOut0 adv (` i) j
  end.

Fixpoint SCPolyDenotationS {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  x (p : @SCPoly E) :
  (nat -> 'F_FSize) -> option 'F_FSize :=
  match p with
  | PolyConsUndef => fun _ => None
  | PolyConsZero => fun _ => Some 0%R
  | PolyConsPlusOne => fun _ => Some 1%R
  | PolyConsMinusOne => fun _ => Some (-1)%R
  | PolyConsPlus p1 p2 => fun u =>
    let r1 := SCPolyDenotationS adv x p1 u in
    let r2 := SCPolyDenotationS adv x p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) r2) r1
  | PolyConsTimes p1 p2 => fun u =>
    let r1 := SCPolyDenotationS adv x p1 u in
    let r2 := SCPolyDenotationS adv x p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) r2) r1
  | PolyConsInd i => indCallOutS adv x i
  | PolyConsFreeV i => fun _ => Some (V_F _ M i)
  | PolyConsUniV i => fun u => Some (u i)
  | PolyConsFreeF i j => freeFCallOutS adv x i j
  | PolyConsExiF i j => exiCallOutS adv x (` i) j
  end.

Fixpoint SCPropDenotation {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  (p : @SCProp E) :
  (nat -> 'F_FSize) -> option bool :=
  match p with
  | ZOConsNot p => fun u => 
    let r := SCPropDenotation adv p u in
    obind (fun r1 => Some (negb r)) r
  | ZOConsAnd p1 p2 => fun u => 
    let r1 := SCPropDenotation adv p1 u in
    let r2 := SCPropDenotation adv p2 u in
    obind (fun r1 => obind (fun r2 => Some (r1 && r2)) r2) r1
  | ZOConsOr p1 p2 => fun u => 
    let r1 := SCPropDenotation adv p1 u in
    let r2 := SCPropDenotation adv p2 u in
    obind (fun r1 => obind (fun r2 => Some (r1 || r2)) r2) r1
  | ZOConsImp p1 p2 => fun u => 
    let r1 := SCPropDenotation adv p1 u in
    let r2 := SCPropDenotation adv p2 u in
    obind (fun r1 => obind (fun r2 => Some (r1 ==> r2)) r2) r1
  | ZOConsEq p1 p2 => fun u => 
    let r1 := SCPolyDenotation0 adv p1 u in
    let r2 := SCPolyDenotation0 adv p2 u in
    obind (fun r1 => obind (fun r2 => Some (r1 == r2)) r2) r1
  end.

(* Definition UProp {ctx} {R} {c}
                 (inst : @SCInstance ctx R (Ctx c)) (adv : @SCAdvice ctx R (Ctx c)) 
                 (t : |[uniV ctx]| -> T R) : Prop :=
  let ev i := SCPolyDenotation inst adv (lnth (polyConstraints c) (uniVBoundsSC c i)) in
  forall i, 
    match (ev i t) with
    | None => false
    | Some e => lt R (t i) e
    end.

Definition U {ctx} {R} {c}
             (inst : @SCInstance ctx R (Ctx c)) (adv : @SCAdvice ctx R (Ctx c)) : Type 
  := { t : |[uniV ctx]| -> T R | UProp inst adv t }. *)


Definition SCInBound0 {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  (r : 'F_FSize)
  (b : SCPoly) 
  (t : nat -> 'F_FSize) : bool :=
  match SCPolyDenotation0 adv b t with
  | None => false
  | Some e => r < e
  end.

Definition SCInBoundS {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) x
  (r : 'F_FSize)
  (b : SCPoly) 
  (t : nat -> 'F_FSize) : bool :=
  match SCPolyDenotationS adv x b t with
  | None => false
  | Some e => r < e
  end.

(*A collection of universal variables within *)
Program Definition SCU {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) 
  (f : @SemiCircuit E) : Type 
  := { u : |[length (uniVBoundsSC f)]| -> 'F_FSize | 
       forall j : |[length (uniVBoundsSC f)]|,
       forall v : nat -> 'F_FSize, 
       SCInBound0 adv (u j) (lnth (uniVBoundsSC f) j) (MakeU u v)
    }.

Program Definition SCFormulaCondition {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (f : SemiCircuit) : Prop :=
  forall (u : SCU adv f), 
  SCPropDenotation adv (formulaSC f) (MakeU u (fun _ => 0%R)) == Some true.

(* Program Definition SCB {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) 
  (f : @SemiCircuit E) (x : |[length E]|) : Type 
  := { u : |[lnth E x]| -> 'F_FSize | 
       forall j : |[lnth E x]|,
       forall v : nat -> 'F_FSize, 
       SCInBoundS adv x (u j) ((exiFBoundsSC f x).1 j) (MakeU u v)
    }. *)

Program Definition SCIndCondition0 {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall u : SCU adv c, forall i,
  let (a1, a2) := indArgs0 c i in
  let b1 : option 'F_FSize := SCPolyDenotation0 adv a1 (MakeU u v) in
  let b2 : option 'F_FSize := SCPolyDenotation0 adv a2 (MakeU u v) in
  obind (fun b1 => obind (fun b2 => Some (indFun b1 b2)) b2) b1
  = indCallOut0 adv i (MakeU u v).

Program Definition SCIndConditionS {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  (c : @SemiCircuit E) : Prop :=
  forall v : nat -> 'F_FSize, forall x : |[length E]|, forall i,
  forall (ins : |[lnth E x]| -> 'F_FSize) (out : 'F_FSize),
  exiAdv adv x ins == Some out -> 
  let (a1, a2) := indArgsS c x i in
  let b1 : option 'F_FSize := SCPolyDenotationS adv x a1 (MakeU ins v) in
  let b2 : option 'F_FSize := SCPolyDenotationS adv x a2 (MakeU ins v) in
  obind (fun b1 => obind (fun b2 => Some (indFun b1 b2)) b2) b1
  = indCallOutS adv x i (MakeU ins v).

Program Definition SCExiFCondition0 {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall u : SCU adv c, forall (i : |[length E]|) j,
  let t (a : |[lnth E i]|) : option 'F_FSize
      := SCPolyDenotation0 adv (exiArgs0 c i j a) (MakeU u v) in
  obind (fun t => exiAdv adv i t) (option_fun t)  
  = exiCallOut0 adv i j (MakeU u v).

Program Definition SCExiFConditionS {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  (c : @SemiCircuit E) : Prop :=
  forall v : nat -> 'F_FSize, forall x, forall (i : |[length E]|) j,
  forall (ins : |[lnth E x]| -> 'F_FSize) (out : 'F_FSize),
  exiAdv adv x ins == Some out -> 
  let t (a : |[lnth E i]|) : option 'F_FSize
      := SCPolyDenotationS adv x (exiArgsS c x i j a) (MakeU ins v) in
  obind (fun t => exiAdv adv i t) (option_fun t)  
  = exiCallOutS adv x i j (MakeU ins v).

Program Definition SCFreeFCondition0 {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall u : SCU adv c, forall (i : |[length E]|) j,
  let t a : option 'F_FSize
      := SCPolyDenotation0 adv (freeFArgs0 c i (projT1 (F_S _ M i)) j a) (MakeU u v) in
  obind (fun t => projT2 (F_S _ M i) t) (option_fun t)
  = freeFCallOut0 adv i j (MakeU u v).

Program Definition SCFreeFConditionS {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) 
  (c : @SemiCircuit E) : Prop :=
  forall v : nat -> 'F_FSize, forall x, forall (i : |[length E]|) j,
  forall (ins : |[lnth E x]| -> 'F_FSize) (out : 'F_FSize),
  exiAdv adv x ins == Some out -> 
  let t a : option 'F_FSize
      := SCPolyDenotationS adv x (freeFArgsS c x i (projT1 (F_S _ M i)) j a) (MakeU ins v) in
  obind (fun t => projT2 (F_S _ M i) t) (option_fun t)
  = freeFCallOutS adv x i j (MakeU ins v).

Program Definition SCUniversalCondition {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) 
  (c : @SemiCircuit E) : Prop :=
  forall (u : nat -> 'F_FSize) (i : |[length (uniVBoundsSC c)]|),
    (forall j : |[i]|, SCInBound0 adv (u j) (lnth (uniVBoundsSC c) j) u) ->
    exists o, SCPolyDenotation0 adv (lnth (uniVBoundsSC c) i) u = Some o.
Next Obligation. strivial use: ltn_trans. Qed.

Program Fixpoint SCFunBounds {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (x : |[length E]|) {a}
  (ins : |[a]| -> 'F_FSize) (out : 'F_FSize)
  (insB : |[a]| -> SCPoly) (outB : SCPoly) :
  (nat -> 'F_FSize) -> bool := fun u =>
  match a with
  | 0 => SCInBoundS adv x out outB u
  | n.+1 => SCInBoundS adv x (ins 0) (insB 0) u &&
    @SCFunBounds E M 
      adv x n (fun x => ins (x.+1)) out (fun x => insB (x.+1)) outB u
  end.

Definition SCExiBoundCondition {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) 
  (c : @SemiCircuit E) : Prop :=
  forall u : nat -> 'F_FSize, forall i : |[length E]|,
  forall (ins : |[lnth E i]| -> 'F_FSize) (out : 'F_FSize),
  exiAdv adv i ins == Some out -> 
  SCFunBounds adv i ins out 
    (fun x => (exiFBoundsSC c i).1 x)
    (exiFBoundsSC c i).2 (MakeU ins u) == true.

Definition SCDenotation {E} {M : @Sigma11Model FSize}
  (c : SemiCircuit) : Prop :=
  exists (a : @SCAdvice E M),
    SCFormulaCondition a c /\
    SCIndCondition0 a c /\
    SCIndConditionS a c /\
    SCExiFCondition0 a c /\
    SCExiFConditionS a c /\
    SCFreeFCondition0 a c /\
    SCFreeFConditionS a c /\
    SCUniversalCondition a c /\
    SCExiBoundCondition a c.

End SemicircuitDef.

Section SemicircuitTranslation.

Variable (FSize : nat).

(* 
(*Convert constraint to one over context with additional function calls*)
Program Fixpoint PolyCallCastFree {IndC ExiC FreeC}
  {newC : nat -> nat}
  (p : @SCPoly IndC ExiC FreeC) :
  @SCPoly IndC ExiC (fun x => FreeC x + newC x) := 
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
  | PolyConsInd i => PolyConsInd i
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF i j
  end.
Next Obligation. qauto use: ltn_addr. Qed.

Program Fixpoint PolyCallCastExi {IndC ExiC FreeC}
  {newC : nat -> nat}
  (p : @SCPoly IndC ExiC FreeC) :
  @SCPoly IndC (fun x => ExiC x + newC x) FreeC := 
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
  | PolyConsInd i => PolyConsInd i
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF i j
  end.
Next Obligation. qauto use: ltn_addr. Qed.

Program Fixpoint PolyCallCastInd {IndC ExiC FreeC}
  {newC : nat}
  (p : @SCPoly IndC ExiC FreeC) :
  @SCPoly (IndC + newC) ExiC FreeC := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyCallCastInd p1 in
    let r2 := PolyCallCastInd p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyCallCastInd p1 in
    let r2 := PolyCallCastInd p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd i => PolyConsInd i
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF i j
  end.
Next Obligation. qauto use: ltn_addr. Qed. *)

(* Program Fixpoint PolyCallCast {E}
    (p : @SCPoly E) :
  @SCPoly E :=
  match p with
  | PolyConsUndef => PolyConsUndef
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
  | PolyConsInd i => PolyConsInd i
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF i j
  end. *)

(*Lift new polynomial args so names don't conflict with arguments from other polynomials *)
Program Fixpoint PolyCallLift {E}
    (newIC : nat)
    (newEC : nat -> nat)
    (newFC : nat -> nat)
    (p : @SCPoly E) :
  @SCPoly E :=
  match p with
  | PolyConsUndef => PolyConsUndef
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyCallLift newIC newEC newFC p1 in
    let r2 := PolyCallLift newIC newEC newFC p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyCallLift newIC newEC newFC p1 in
    let r2 := PolyCallLift newIC newEC newFC p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd i => PolyConsInd (newIC + i)
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i (newFC i + j)
  | PolyConsExiF i j => PolyConsExiF i (newEC i + j)
  end.

Program Fixpoint PropCallLift {E}
    (newIC : nat)
    (newEC : nat -> nat)
    (newFC : nat -> nat)
    (p : @SCProp E) :
  @SCProp E :=
  match p with
  | ZOConsNot x => ZOConsNot (PropCallLift newIC newEC newFC x)
  | ZOConsAnd x y => 
    ZOConsAnd (PropCallLift newIC newEC newFC x)
              (PropCallLift newIC newEC newFC y)
  | ZOConsOr x y => 
    ZOConsOr (PropCallLift newIC newEC newFC x)
             (PropCallLift newIC newEC newFC y)
  | ZOConsImp x y => 
    ZOConsImp (PropCallLift newIC newEC newFC x)
              (PropCallLift newIC newEC newFC y)
  | ZOConsEq x y => 
    ZOConsEq (PolyCallLift newIC newEC newFC x)
             (PolyCallLift newIC newEC newFC y)
  end.

Record SemiConversionData {E} : Type := 
  mkSemiConversionData {
    IndArgs : nat -> (@SCPoly E * @SCPoly E);
    ExiArgs : forall i, nat -> |[lnth E i]| -> @SCPoly E;
    FreeArgs : forall i a : nat, nat -> |[a]| -> @SCPoly E ;
  }.

Record SemiAdvice : Type :=
  mkSemiAdvice {
    IndCOut : nat -> (nat -> 'F_FSize) -> option 'F_FSize;
    ExiCOut : forall i j : nat, (nat -> 'F_FSize) -> option 'F_FSize;
    FreeCOut : forall i j : nat, (nat -> 'F_FSize) -> option 'F_FSize;
  }.

Definition SemiAdviceGenerator {E} := @Sigma11Model FSize -> PrenexAdvice FSize E -> SemiAdvice.

Definition EmptyGenerator {E} : @SemiAdviceGenerator E := fun _ _ =>
  {| IndCOut := fun _ _ => None; 
     ExiCOut := fun _ _ _ => None; 
     FreeCOut := fun _ _ _ => None; |}.

Definition SemiConversionEmptyData {E} : 
  @SemiConversionData E :=
  {| IndArgs := fun _ => (PolyConsUndef, PolyConsUndef); 
     ExiArgs := fun _ _ _ => PolyConsUndef; 
     FreeArgs := fun _ _ _ _ => PolyConsUndef; |}.

Definition SemiConversionDataBundle {E} :=
  (nat * (nat -> nat) * (nat -> nat) * @SemiConversionData E * @SemiAdviceGenerator E)%type.

Definition EmptyBundle {E} : @SemiConversionDataBundle E :=
  (0, fun _=> 0, fun _=> 0, @SemiConversionEmptyData E, @EmptyGenerator E).

Definition CombineGens {E} nic1 nefc1 nffc1 (g1 g2 : @SemiAdviceGenerator E) : @SemiAdviceGenerator E :=
  fun M A =>
  match g1 M A, g2 M A with
  | {| IndCOut := ico1; ExiCOut := eco1; FreeCOut := fco1 |}
  , {| IndCOut := ico2; ExiCOut := eco2; FreeCOut := fco2 |} =>
    {| IndCOut := fun x => if x < nic1 then ico1 x else ico2 (x - nic1); 
       ExiCOut := fun i x => if x < nefc1 i then eco1 i x else eco2 i (x - nefc1 i); 
       FreeCOut := fun i x => if x < nffc1 i then fco1 i x else fco2 i (x - nffc1 i);  |}
  end.

Definition SemiConversionCombineData {E}
  (d1 : @SemiConversionDataBundle E)
  (d2 : @SemiConversionDataBundle E) : 
  @SemiConversionDataBundle E :=
  match d1, d2 with
  | (nic1, nefc1, nffc1, {| FreeArgs := farg1; ExiArgs := earg1; IndArgs := iarg1 |}, gen1)
  , (nic2, nefc2, nffc2, {| FreeArgs := farg2; ExiArgs := earg2; IndArgs := iarg2 |}, gen2)
  => (nic1 + nic2, fun x => nefc1 x + nefc2 x, fun x => nffc1 x + nffc2 x, 
   {| FreeArgs := fun i a j => (
      if j < nffc1 i as b return j < nffc1 i = b -> |[a]| -> _
      then fun _ k => (farg1 i a j k)
      else fun _ k => PolyCallLift nic1 nefc1 nffc1 (farg2 i a (j - nffc1 i) k)
    ) (erefl _)
    ; ExiArgs := fun i j => (
      if j < nefc1 (` i) as b return j < nefc1 (` i) = b -> |[lnth E i]| -> _
      then fun _ k => (earg1 i j k)
      else fun _ k => PolyCallLift nic1 nefc1 nffc1 (earg2 i (j - nefc1 (` i)) k)
    ) (erefl _) 
    ; IndArgs := fun i => (
      if i < nic1 as b return i < nic1 = b -> _
      then fun _ => let (u, v) := iarg1 i in (u, v)
      else fun _ => let (u, v) := iarg2 (i - nic1) in 
                    (PolyCallLift nic1 nefc1 nffc1 u, PolyCallLift nic1 nefc1 nffc1 v) 
    ) (erefl _) 
  |}, CombineGens nic1 nefc1 nffc1 gen1 gen2)
  end.

Program Fixpoint SemiConversionCombineTup {E a}
  (ds : |[a]| -> @SemiConversionDataBundle E * @SCPoly E) :
  @SemiConversionDataBundle E * (|[a]| -> @SCPoly E) :=
match a with
| 0 => (EmptyBundle, emptyTuple)
| n.+1 => 
  let (bund, pols) := SemiConversionCombineTup (fSeqRest ds) in
  match (ds 0).1 with
  | (nic, nefc, nffc, dat, gen) =>
    (SemiConversionCombineData (ds 0).1 bund, ExtendAt0N (ds 0).2 (fun x => PolyCallLift nic nefc nffc (pols x)))
  end
end.

Fixpoint SemiConversionCombineSeq {E}
  (ds : seq (@SemiConversionDataBundle E * @SCPoly E)) :
  @SemiConversionDataBundle E * seq (@SCPoly E):=
match ds with
| [::] => (EmptyBundle, [::])
| ((nic, nefc, nffc, dat, gen), p) :: xs => 
  let (bund, polys) := SemiConversionCombineSeq xs in
  (SemiConversionCombineData (nic, nefc, nffc, dat, gen) bund, p :: map (PolyCallLift nic nefc nffc) polys)
end. 

Definition AddIndArg {E} n (p1 p2 : @SCPoly E) (d : SemiConversionData) : SemiConversionData :=
  match d with
  | {| IndArgs := iarg1; ExiArgs := earg1; FreeArgs := farg1 |} =>
    {| IndArgs := fun x => if x == n then (p1, p2) else iarg1 x
     ; ExiArgs := earg1; FreeArgs := farg1 |}
  end.

Definition AddIndCall {E} n v (d : @SemiAdviceGenerator E) : SemiAdviceGenerator :=
  fun M A =>
  match d M A with
  | {| IndCOut := ico1; ExiCOut := eco1; FreeCOut := fco1 |} =>
    {| IndCOut := fun x => if x == n then PolyVSDenotation _ M v A else ico1 x
     ; ExiCOut := eco1; FreeCOut := fco1 |}
  end.

Program Definition AddExiArg {E} i n (ps : |[lnth E i]| -> @SCPoly E) (d : @SemiConversionData E) : SemiConversionData :=
  match d with
  | {| IndArgs := iarg1; ExiArgs := earg1; FreeArgs := farg1 |} =>
    {| IndArgs := iarg1
     ; ExiArgs := fun i' =>
        (if i == i' as b return (i == i') = b -> nat -> |[lnth E i']| -> SCPoly
         then fun _ x => if x == n then ps else earg1 i' x
         else fun _ => earg1 i') (erefl _)
     ; FreeArgs := farg1 |}
  end.
Next Obligation.
  apply EEConvert in e; simpl in e; destruct e.
  by replace H0 with H1;[|apply eq_irrelevance].
Qed.
Next Obligation.
  apply EEConvert in e; simpl in e; destruct e.
  by replace H1 with H0;[|apply eq_irrelevance].
Qed.

Program Definition AddExiCall {E} i n (ps : @PolyTermVS E) (d : @SemiAdviceGenerator E) : SemiAdviceGenerator :=
  fun M A =>
  match d M A with
  | {| IndCOut := ico1; ExiCOut := eco1; FreeCOut := fco1 |} =>
    {| IndCOut := ico1
     ; ExiCOut := fun i' =>
        if i == i'
        then fun x => (if x == n then (PolyVSDenotation _ M ps A) else eco1 i' x)
        else eco1 i'
     ; FreeCOut := fco1 |}
  end.

Program Definition AddFreeArg {E a} i n (ps : |[a]| -> @SCPoly E) (d : @SemiConversionData E) : SemiConversionData :=
  match d with
  | {| IndArgs := iarg1; ExiArgs := earg1; FreeArgs := farg1 |} =>
    {| IndArgs := iarg1; ExiArgs := earg1
     ; FreeArgs := fun i' =>
        if i == i' 
        then fun a' =>
             (if a == a' as b return (a == a') = b -> nat -> |[a']| -> SCPoly
              then fun _ x => if x == n then ps else farg1 i' a' x
              else fun _ => farg1 i' a') (erefl _)
        else farg1 i'|}
  end.
Next Obligation. by apply EEConvert in e; destruct e. Qed.
Next Obligation. by apply EEConvert in e; destruct e. Qed.

Program Definition AddFreeCall {E} i n (ps : @PolyTermVS E) (d : @SemiAdviceGenerator E) : SemiAdviceGenerator :=
  fun M A =>
  match d M A with
  | {| IndCOut := ico1; ExiCOut := eco1; FreeCOut := fco1 |} =>
    {| IndCOut := ico1; ExiCOut := eco1
     ; FreeCOut := fun i' =>
        if i == i'
        then fun x => (if x == n then (PolyVSDenotation _ M ps A) else fco1 i' x)
        else fco1 i' |}
  end.

Fixpoint SemiPolyConvert {E} (r : @PolyTermVS E) :
  @SemiConversionDataBundle E * @SCPoly E := 
  match r with
  | UndefVS => (EmptyBundle, PolyConsUndef)
  | PolyFVarVS i => (EmptyBundle, PolyConsFreeV i)
  | PolyUVarVS i => (EmptyBundle, PolyConsUniV i)

  | PolyEFunVS i t => 
    let (bund, polys) := SemiConversionCombineTup (fun x => SemiPolyConvert (t x)) in
    match bund with
    | (nic, nefc, nffc, dat, gen) =>
      let nefc' x := if x == ` i then (nefc x).+1 else nefc x in
      let dat' := AddExiArg i (nefc (` i)) polys dat in
      let gen' := AddExiCall (` i) (nefc (` i)) (PolyEFunVS i t) gen in
      ((nic, nefc', nffc, dat', gen'), PolyConsExiF i (nefc (` i)))
    end

  | PolyFFunVS i a t => 
    let (bund, polys) := SemiConversionCombineTup (fun x => SemiPolyConvert (t x)) in
    match bund with
    | (nic, nefc, nffc, dat, gen) =>
      let nffc' x := if x == i then (nffc x).+1 else nffc x in
      let dat' := AddFreeArg i (nffc i) polys dat in
      let gen' := AddFreeCall i (nffc i) (PolyFFunVS i a t) gen in
      ((nic, nefc, nffc', dat', gen'), PolyConsFreeF i (nffc i))
    end

  | PolyMinusOneVS => (EmptyBundle, PolyConsMinusOne)
  | PolyPlusOneVS => (EmptyBundle, PolyConsPlusOne)
  | PolyZeroVS => (EmptyBundle, PolyConsZero)
  | PolyPlusVS p1 p2 =>
    match SemiPolyConvert p1, SemiPolyConvert p2 with
    | (bun1, poly1), (bun2, poly2) =>
      (SemiConversionCombineData bun1 bun2, PolyConsPlus poly1 (PolyCallLift bun1.1.1.1.1 bun1.1.1.1.2 bun1.1.1.2 poly2))
    end
  | PolyTimesVS p1 p2 => 
    match SemiPolyConvert p1, SemiPolyConvert p2 with
    | (bun1, poly1), (bun2, poly2) =>
      (SemiConversionCombineData bun1 bun2, PolyConsTimes poly1 (PolyCallLift bun1.1.1.1.1 bun1.1.1.1.2 bun1.1.1.2 poly2))
    end
  | PolyIndVS p1 p2 => 
    match SemiPolyConvert p1, SemiPolyConvert p2 with
    | ((nic1, nefc1, nffc1, dat1, gen1), poly1), (bun2, poly2) =>
      let bun1 := (nic1, nefc1, nffc1, dat1, gen1) in
      let poly2' := PolyCallLift nic1 nefc1 nffc1 poly2 in
      match SemiConversionCombineData bun1 bun2 with
      | (nic, nefc, nffc, dat, gen) => 
        ( (nic.+1, nefc, nffc, AddIndArg nic poly1 poly2' dat, AddIndCall nic (PolyIndVS p1 p2) gen)
        , PolyConsInd nic)
      end
    end
  end.

Fixpoint CallBounds {E} (nic : nat) (nefc : nat -> nat) (nffc : nat -> nat) 
  (p : @SCPoly E) : bool :=
  match p with
  | PolyConsUndef => true
  | PolyConsZero => true
  | PolyConsPlusOne => true
  | PolyConsMinusOne => true
  | PolyConsPlus p1 p2 => 
    CallBounds nic nefc nffc p1 && CallBounds nic nefc nffc p2
  | PolyConsTimes p1 p2 =>
    CallBounds nic nefc nffc p1 && CallBounds nic nefc nffc p2
  | PolyConsInd i => i < nic
  | PolyConsFreeV i => true
  | PolyConsUniV i => true
  | PolyConsExiF i j => j < nefc (` i)
  | PolyConsFreeF i j => j < nffc i
  end.

Theorem CallBounds_Left {E i j k l m n D} :
  CallBounds i j k n ->
  CallBounds (E := E)
             (SemiConversionCombineData (i, j, k, l, m) D).1.1.1.1
             (SemiConversionCombineData (i, j, k, l, m) D).1.1.1.2
             (SemiConversionCombineData (E := E) (i, j, k, l, m) D).1.1.2 
             n.
Proof.
  elim: n; try qauto.
  - move=> x IHx y IHy.
    destruct l, D, p, p, p, s0; simpl in *.
    destruct (CallBounds _ _ _ _), (CallBounds _ _ _ _); auto.
  - move=> x IHx y IHy.
    destruct l, D, p, p, p, s0; simpl in *.
    destruct (CallBounds _ _ _ _), (CallBounds _ _ _ _); auto.
  - move=> n.
    destruct l, D, p, p, p, s0; simpl.
    move: i; induction n;move=> i H;cbn in *; destruct i; try qauto.
  - move=> n i0.
    simpl.
    destruct l, D, p, p, p, s0; simpl.
    remember (k n) as kn; clear Heqkn.
    move: kn; induction i0;move=> kn H;cbn in *; destruct kn; try qauto.
  - move=> n j0.
    simpl.
    destruct l, D, p, p, p, s0; simpl.
    remember (j (` n)) as jn; clear Heqjn.
    move: jn; induction j0;move=> jn H;cbn in *; destruct jn; try qauto.
Qed.

Theorem CallBounds_Right {E i j k l m n D} :
  CallBounds i j k n ->
  CallBounds (E := E) (SemiConversionCombineData D (i, j, k, l, m)).1.1.1.1
    (SemiConversionCombineData D (i, j, k, l, m)).1.1.1.2
    (SemiConversionCombineData (E := E) D (i, j, k, l, m)).1.1.2 
    (PolyCallLift D.1.1.1.1 D.1.1.1.2 D.1.1.2 n).
Proof.
  elim: n; try qauto.
  - move=> x IHx y IHy.
    destruct l, D, p, p, p, s0; simpl in *.
    destruct (CallBounds _ _ _ _), (CallBounds _ _ _ _); auto.
  - move=> x IHx y IHy.
    destruct l, D, p, p, p, s0; simpl in *.
    destruct (CallBounds _ _ _ _), (CallBounds _ _ _ _); auto.
  - move=> n.
    destruct l, D, p, p, p, s0; simpl.
    by rewrite ltn_add2l.
  - move=> n i0.
    destruct l, D, p, p, p, s0; simpl.
    by rewrite ltn_add2l.
  - move=> n j0.
    destruct l, D, p, p, p, s0; simpl.
    by rewrite ltn_add2l.
Qed.

Theorem CallBounds_Correct {E} (r : @PolyTermVS E) :
  CallBounds (SemiPolyConvert r).1.1.1.1.1 (SemiPolyConvert r).1.1.1.1.2 (SemiPolyConvert r).1.1.1.2 (SemiPolyConvert r).2.
Proof.
  elim: r; try qauto.
  - move=> i a p IH.
    simpl.
    rewrite (surjective_pairing (SemiConversionCombineTup _))
            (surjective_pairing (SemiConversionCombineTup _).1)
            (surjective_pairing (SemiConversionCombineTup _).1.1)
            (surjective_pairing (SemiConversionCombineTup _).1.1.1)
            (surjective_pairing (SemiConversionCombineTup _).1.1.1.1); simpl.
    rewrite eq_refl.
    apply ltnSn.
  - move=> i p IH.
    simpl.
    rewrite (surjective_pairing (SemiConversionCombineTup _))
            (surjective_pairing (SemiConversionCombineTup _).1)
            (surjective_pairing (SemiConversionCombineTup _).1.1)
            (surjective_pairing (SemiConversionCombineTup _).1.1.1)
            (surjective_pairing (SemiConversionCombineTup _).1.1.1.1); simpl.
    rewrite eq_refl.
    apply ltnSn.
  - move=> x IHx y IHy.
    simpl.
    rewrite (surjective_pairing (SemiPolyConvert x))
            (surjective_pairing (SemiPolyConvert y)).
    simpl.
    destruct (SemiPolyConvert x) as [[[[[i j] k] l] m] n].
    rewrite CallBounds_Left; auto.
    destruct (SemiPolyConvert y) as [[[[[i0 j0] k0] l0] m0] n0].
    rewrite CallBounds_Right; auto.
  - move=> x IHx y IHy.
    simpl.
    rewrite (surjective_pairing (SemiPolyConvert x))
            (surjective_pairing (SemiPolyConvert y)).
    simpl.
    destruct (SemiPolyConvert x) as [[[[[i j] k] l] m] n].
    rewrite CallBounds_Left; auto.
    destruct (SemiPolyConvert y) as [[[[[i0 j0] k0] l0] m0] n0].
    rewrite CallBounds_Right; auto.
  - move=> x IHx y IHy.
    simpl.
    destruct (SemiPolyConvert x), s, p, p, p.
    destruct (SemiPolyConvert y), s1, s2, p, p, p, s2; simpl.
    apply ltnSn.
Qed.

Fixpoint SemiPropConvert {E} (r : @PropTermVS E) :
  @SemiConversionDataBundle E * @SCProp E := 
  match r with
  | ZONotVS x =>
    match SemiPropConvert x with
    | (bun1, prop1) => (bun1, ZOConsNot prop1)
    end
  | ZOAndVS x y => 
    match SemiPropConvert x, SemiPropConvert y with
    | (bun1, prop1), (bun2, prop2) =>
      (SemiConversionCombineData bun1 bun2, ZOConsAnd prop1 (PropCallLift bun1.1.1.1.1 bun1.1.1.1.2 bun1.1.1.2 prop2))
    end
  | ZOOrVS x y => 
    match SemiPropConvert x, SemiPropConvert y with
    | (bun1, prop1), (bun2, prop2) =>
      (SemiConversionCombineData bun1 bun2, ZOConsOr prop1 (PropCallLift bun1.1.1.1.1 bun1.1.1.1.2 bun1.1.1.2 prop2))
    end
  | ZOImpVS x y => 
    match SemiPropConvert x, SemiPropConvert y with
    | (bun1, prop1), (bun2, prop2) =>
      (SemiConversionCombineData bun1 bun2, ZOConsImp prop1 (PropCallLift bun1.1.1.1.1 bun1.1.1.1.2 bun1.1.1.2 prop2))
    end
  | ZOEqVS x y => 
    match SemiPolyConvert x, SemiPolyConvert y with
    | (bun1, poly1), (bun2, poly2) =>
      (SemiConversionCombineData bun1 bun2, ZOConsEq poly1 (PolyCallLift bun1.1.1.1.1 bun1.1.1.1.2 bun1.1.1.2 poly2))
    end
  end.

Definition ExiConv {E}
  (e : forall i, (|[lnth E i]| -> @PolyTermVS E) * @PolyTermVS E) :
  forall i, @SemiConversionDataBundle E * ((|[lnth E i]| -> @SCPoly E) * @SCPoly E) :=
fun i =>
  let (bs, y) := e i in
  let (bundbs, bs') := SemiConversionCombineTup (fun x => SemiPolyConvert (bs x)) in
  match bundbs with
  | (nic, nefc, nffc, dat, gen) => 
    let (bundy, y') := SemiPolyConvert y in
    (SemiConversionCombineData bundbs bundy, (bs', PolyCallLift nic nefc nffc y'))
  end.

Definition AdviceGenerator {E} := forall M : @Sigma11Model FSize, PrenexAdvice FSize E -> @SCAdvice FSize E M.

Definition Prenex_Semicircuit {E} (p : @Prenex E) : @SemiCircuit E  * @AdviceGenerator E :=
match p with
| {| uniBounds := ub; exiBounds := eb; formula := f |} =>
  let (ubund, upols) := SemiConversionCombineSeq (map SemiPolyConvert ub) in
  let (fbund, fprop) := SemiPropConvert f in
  let (ebund, epols) := unzip_dep (ExiConv eb) in
  match ubund with
  | (nicu, nefcu, nffcu, datu, genu) => 
  let bnd0 := SemiConversionCombineData ubund fbund in
  match bnd0 with
  | (nic0, nefc0, nffc0, dat0, gen0) => 
  ({| indArgs0 := IndArgs dat0;
      indArgsS := fun i => IndArgs (ebund i).1.2;
      exiArgs0 := ExiArgs dat0;
      exiArgsS := fun i => ExiArgs (ebund i).1.2;
      freeFArgs0 := FreeArgs dat0;
      freeFArgsS := fun i => FreeArgs (ebund i).1.2;
      uniVBoundsSC := upols;
      exiFBoundsSC := epols;
      formulaSC := PropCallLift nicu nefcu nffcu fprop
   |}, fun M A => 
   {| exiAdv := A;
      indCallOut0 := IndCOut (gen0 M A);
      indCallOutS := fun i => IndCOut ((ebund i).2 M A);
      exiCallOut0 := ExiCOut (gen0 M A);
      exiCallOutS := fun i => ExiCOut ((ebund i).2 M A);
      freeFCallOut0 := FreeCOut (gen0 M A);
      freeFCallOutS := fun i => FreeCOut ((ebund i).2 M A);
   |})
  end end
end.

Theorem SemiConversionCombineSeq_length {E ds} : length (@SemiConversionCombineSeq E ds).2 = length ds.
Proof.
  elim: ds; auto.
  intros.
  simpl.
  rewrite (surjective_pairing a)
          (surjective_pairing a.1)
          (surjective_pairing a.1.1)
          (surjective_pairing a.1.1.1)
          (surjective_pairing a.1.1.1.1)
          (surjective_pairing (SemiConversionCombineSeq l)); simpl.
  rewrite <- H; clear H.
  f_equal.
  by rewrite map_length.
Qed.

Fixpoint SCPolySemiDenotation {E} (M : @Sigma11Model FSize)
  (adv : SemiAdvice)
  (p : @SCPoly E) :
  (nat -> 'F_FSize) -> option 'F_FSize :=
  match p with
  | PolyConsUndef => fun _ => None
  | PolyConsZero => fun _ => Some 0%R
  | PolyConsPlusOne => fun _ => Some 1%R
  | PolyConsMinusOne => fun _ => Some (-1)%R
  | PolyConsPlus p1 p2 => fun u =>
    let r1 := SCPolySemiDenotation M adv p1 u in
    let r2 := SCPolySemiDenotation M adv p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) r2) r1
  | PolyConsTimes p1 p2 => fun u =>
    let r1 := SCPolySemiDenotation M adv p1 u in
    let r2 := SCPolySemiDenotation M adv p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) r2) r1
  | PolyConsInd i => IndCOut adv i
  | PolyConsFreeV i => fun _ => Some (V_F _ M i)
  | PolyConsUniV i => fun u => Some (u i)
  | PolyConsFreeF i j => FreeCOut adv i j
  | PolyConsExiF i j => ExiCOut adv (` i) j
  end.

Theorem CombineDenotationRight {E k j i f h Y D M A} :
  SCPolySemiDenotation M
    ((SemiConversionCombineData (E := E) (k, j, i, f, h) D).2 M A)
    (PolyCallLift k j i Y) =
  SCPolySemiDenotation (E := E) M (D.2 M A) Y.
Proof.
  elim: Y; try qauto.
  - move=> n.
    simpl.
    unfold IndCOut.
    destruct f, D, p, p, p, s0; simpl.
    unfold CombineGens.
    destruct (h M A); simpl.
    destruct (s M A); simpl.
    by rewrite LTPF kpmnken.
  - move=> i0 j0.
    simpl.
    unfold FreeCOut.
    destruct f, D, p, p, p, s0; simpl.
    unfold CombineGens.
    destruct (h M A); simpl.
    destruct (s M A); simpl.
    by rewrite LTPF kpmnken.
  - move=> i0 n.
    simpl.
    unfold ExiCOut.
    destruct f, D, p, p, p, s0; simpl.
    unfold CombineGens.
    destruct (h M A); simpl.
    destruct (s M A); simpl.
    by rewrite LTPF kpmnken.
Qed.

Theorem CombineDenotationLeft {E G Y D M A} :
  CallBounds G.1.1.1.1 G.1.1.1.2 G.1.1.2 Y ->
  SCPolySemiDenotation M
    ((SemiConversionCombineData (E := E) G D).2 M A) Y =
  SCPolySemiDenotation (E := E) M (G.2 M A) Y.
Proof.
  move: G.
  elim: Y; try qauto.
  - move=> x IHx y IHy G.
    simpl.
    intro.
    apply functional_extensionality=> u.
    f_equal.
    apply functional_extensionality=> r1; f_equal.
    rewrite IHy; auto.
    destruct (CallBounds _ _ _ _); auto.
    rewrite IHx; auto.
    destruct (CallBounds _ _ _ _); auto.
  - move=> x IHx y IHy G.
    simpl.
    intro.
    apply functional_extensionality=> u.
    f_equal.
    apply functional_extensionality=> r1; f_equal.
    rewrite IHy; auto.
    destruct (CallBounds _ _ _ _); auto.
    rewrite IHx; auto.
    destruct (CallBounds _ _ _ _); auto.
  - move=> n G.
    simpl.
    unfold IndCOut.
    destruct G, p, p, p, s0, D, p, p, p, s1; simpl.
    unfold CombineGens.
    destruct (s M A), (s0 M A); qauto.
  - move=> i j G.
    simpl.
    unfold FreeCOut.
    destruct G, p, p, p, s0, D, p, p, p, s1; simpl.
    unfold CombineGens.
    destruct (s M A), (s0 M A); qauto.
  - move=> i n G.
    simpl.
    unfold ExiCOut.
    destruct G, p, p, p, s0, D, p, p, p, s1; simpl.
    unfold CombineGens.
    destruct (s M A), (s0 M A); qauto.
Qed.

Theorem SemiPolyConvert_Correct {E M A} (r : @PolyTermVS E) :
  PolyVSDenotation FSize M r A = SCPolySemiDenotation M ((SemiPolyConvert r).1.2 M A) (SemiPolyConvert r).2.
Proof.
  elim: r; try qauto.
  - move=> i a p IH.
    apply functional_extensionality=> u.
    simpl SCPolySemiDenotation.
    rewrite (surjective_pairing (SemiConversionCombineTup _))
            (surjective_pairing (SemiConversionCombineTup _).1)
            (surjective_pairing (SemiConversionCombineTup _).1.1)
            (surjective_pairing (SemiConversionCombineTup _).1.1.1)
            (surjective_pairing (SemiConversionCombineTup _).1.1.1.1).
    rewrite <- surjective_pairing; simpl SCPolySemiDenotation.
    unfold FreeCOut.
    unfold AddFreeCall.
    remember ((SemiConversionCombineTup _).1.2 _ _) as SCCT.
    destruct SCCT.
    by do 2 rewrite eq_refl.
  - move=> i p IH.
    apply functional_extensionality=> u.
    simpl SCPolySemiDenotation.
    rewrite (surjective_pairing (SemiConversionCombineTup _))
            (surjective_pairing (SemiConversionCombineTup _).1)
            (surjective_pairing (SemiConversionCombineTup _).1.1)
            (surjective_pairing (SemiConversionCombineTup _).1.1.1)
            (surjective_pairing (SemiConversionCombineTup _).1.1.1.1).
    simpl SCPolySemiDenotation.
    unfold ExiCOut.
    unfold AddExiCall.
    remember ((SemiConversionCombineTup _).1.2 _ _) as SCCT.
    destruct SCCT.
    by do 2 rewrite eq_refl.
  - move=> x IHx y IHy.
    apply functional_extensionality=> u; simpl.
    rewrite (surjective_pairing (SemiPolyConvert x))
            (surjective_pairing (SemiPolyConvert y)); simpl.
    f_equal. 
    apply functional_extensionality=> r0; f_equal.
    destruct (SemiPolyConvert x) as [[[[[k j] i] f] h] x2].
    by rewrite IHy CombineDenotationRight.
    rewrite IHx CombineDenotationLeft; auto.
    apply CallBounds_Correct.
  - move=> x IHx y IHy.
    apply functional_extensionality=> u; simpl.
    rewrite (surjective_pairing (SemiPolyConvert x))
            (surjective_pairing (SemiPolyConvert y)); simpl.
    f_equal. 
    apply functional_extensionality=> r0; f_equal.
    destruct (SemiPolyConvert x) as [[[[[k j] i] f] h] x2].
    by rewrite IHy CombineDenotationRight.
    rewrite IHx CombineDenotationLeft; auto.
    apply CallBounds_Correct.
  - move=> x IHx y IHy.
    apply functional_extensionality=> u; simpl.
    destruct (SemiPolyConvert x), s, p, p, p.
    destruct (SemiPolyConvert y), s1, s2, p, p, p.
    destruct s2; simpl.
    unfold IndCOut, AddIndCall, CombineGens.
    destruct (s M A), (s1 M A).
    by rewrite eq_refl.
Qed.

Fixpoint SCPropSemiDenotation {E} (M : @Sigma11Model FSize)
  (adv : SemiAdvice)
  (p : @SCProp E) :
  (nat -> 'F_FSize) -> option bool :=
  match p with
  | ZOConsNot p => fun u => 
    let r := SCPropSemiDenotation M adv p u in
    obind (fun r => Some (negb r)) r
  | ZOConsAnd p1 p2 => fun u => 
    let r1 := SCPropSemiDenotation M adv p1 u in
    let r2 := SCPropSemiDenotation M adv p2 u in
    obind (fun r1 => obind (fun r2 => Some (r1 && r2)) r2) r1
  | ZOConsOr p1 p2 => fun u => 
    let r1 := SCPropSemiDenotation M adv p1 u in
    let r2 := SCPropSemiDenotation M adv p2 u in
    obind (fun r1 => obind (fun r2 => Some (r1 || r2)) r2) r1
  | ZOConsImp p1 p2 => fun u => 
    let r1 := SCPropSemiDenotation M adv p1 u in
    let r2 := SCPropSemiDenotation M adv p2 u in
    obind (fun r1 => obind (fun r2 => Some (r1 ==> r2)) r2) r1
  | ZOConsEq p1 p2 => fun u => 
    let r1 := SCPolySemiDenotation M adv p1 u in
    let r2 := SCPolySemiDenotation M adv p2 u in
    obind (fun r1 => obind (fun r2 => Some (r1 == r2)) r2) r1
  end.

Fixpoint CallBoundsP {E} (nic : nat) (nefc : nat -> nat) (nffc : nat -> nat) 
  (p : @SCProp E) : bool :=
  match p with
  | ZOConsNot p => CallBoundsP nic nefc nffc p
  | ZOConsAnd p1 p2 => 
    CallBoundsP nic nefc nffc p1 && CallBoundsP nic nefc nffc p2
  | ZOConsOr p1 p2 => 
    CallBoundsP nic nefc nffc p1 && CallBoundsP nic nefc nffc p2
  | ZOConsImp p1 p2 =>
    CallBoundsP nic nefc nffc p1 && CallBoundsP nic nefc nffc p2
  | ZOConsEq p1 p2 =>
    CallBounds nic nefc nffc p1 && CallBounds nic nefc nffc p2
  end.

Theorem CallBoundsP_Left {E i j k l m n D} :
  CallBoundsP i j k n ->
  CallBoundsP (E := E)
              (SemiConversionCombineData (i, j, k, l, m) D).1.1.1.1
              (SemiConversionCombineData (i, j, k, l, m) D).1.1.1.2
              (SemiConversionCombineData (E := E) (i, j, k, l, m) D).1.1.2 
              n.
Proof.
  elim: n; try qauto.
  - move=> x IHx y IHy.
    destruct l, D, p, p, p, s0; simpl in *.
    destruct (CallBoundsP _ _ _ _), (CallBoundsP _ _ _ _); auto.
  - move=> x IHx y IHy.
    destruct l, D, p, p, p, s0; simpl in *.
    destruct (CallBoundsP _ _ _ _), (CallBoundsP _ _ _ _); auto.
  - move=> x IHx y IHy.
    destruct l, D, p, p, p, s0; simpl in *.
    destruct (CallBoundsP _ _ _ _), (CallBoundsP _ _ _ _); auto.
  - move=> x y.
    simpl=> chk.
    rewrite CallBounds_Left.
    rewrite CallBounds_Left; auto.
    all: by destruct (CallBounds i j k x), (CallBounds i j k y).
Qed.

Theorem CallBoundsP_Right {E i j k l m n D} :
  CallBoundsP i j k n ->
  CallBoundsP (E := E) (SemiConversionCombineData D (i, j, k, l, m)).1.1.1.1
    (SemiConversionCombineData D (i, j, k, l, m)).1.1.1.2
    (SemiConversionCombineData (E := E) D (i, j, k, l, m)).1.1.2 
    (PropCallLift D.1.1.1.1 D.1.1.1.2 D.1.1.2 n).
Proof.
  elim: n; try qauto.
  - move=> x IHx y IHy.
    destruct l, D, p, p, p, s0; simpl in *.
    destruct (CallBoundsP _ _ _ _), (CallBoundsP _ _ _ _); auto.
  - move=> x IHx y IHy.
    destruct l, D, p, p, p, s0; simpl in *.
    destruct (CallBoundsP _ _ _ _), (CallBoundsP _ _ _ _); auto.
  - move=> x IHx y IHy.
    destruct l, D, p, p, p, s0; simpl in *.
    destruct (CallBoundsP _ _ _ _), (CallBoundsP _ _ _ _); auto.
  - move=> x y.
    simpl=> chk.
    rewrite CallBounds_Right.
    rewrite CallBounds_Right; auto.
    all: by destruct (CallBounds i j k x), (CallBounds i j k y).
Qed.

Theorem CallBoundsP_Correct {E} (r : @PropTermVS E) :
  CallBoundsP (SemiPropConvert r).1.1.1.1.1 (SemiPropConvert r).1.1.1.1.2 (SemiPropConvert r).1.1.1.2 (SemiPropConvert r).2.
Proof.
  elim: r; try qauto.
  - move=> x IHx y IHy.
    simpl.
    rewrite (surjective_pairing (SemiPropConvert x))
            (surjective_pairing (SemiPropConvert y)).
    simpl.
    destruct (SemiPropConvert x) as [[[[[i j] k] l] m] n].
    rewrite CallBoundsP_Left; auto.
    destruct (SemiPropConvert y) as [[[[[i0 j0] k0] l0] m0] n0].
    rewrite CallBoundsP_Right; auto.
  - move=> x IHx y IHy.
    simpl.
    rewrite (surjective_pairing (SemiPropConvert x))
            (surjective_pairing (SemiPropConvert y)).
    simpl.
    destruct (SemiPropConvert x) as [[[[[i j] k] l] m] n].
    rewrite CallBoundsP_Left; auto.
    destruct (SemiPropConvert y) as [[[[[i0 j0] k0] l0] m0] n0].
    rewrite CallBoundsP_Right; auto.
  - move=> x IHx y IHy.
    simpl.
    rewrite (surjective_pairing (SemiPropConvert x))
            (surjective_pairing (SemiPropConvert y)).
    simpl.
    destruct (SemiPropConvert x) as [[[[[i j] k] l] m] n].
    rewrite CallBoundsP_Left; auto.
    destruct (SemiPropConvert y) as [[[[[i0 j0] k0] l0] m0] n0].
    rewrite CallBoundsP_Right; auto.
  - move=> x y.
    simpl.
    rewrite (surjective_pairing (SemiPolyConvert x))
            (surjective_pairing (SemiPolyConvert y)); simpl.
    remember (CallBounds_Correct x) as H0; clear HeqH0.
    remember (CallBounds_Correct y) as H1; clear HeqH1.
    destruct (SemiPolyConvert x) as [[[[[i j] k] l] m] n].
    rewrite CallBounds_Left; auto.
    destruct (SemiPolyConvert y) as [[[[[i0 j0] k0] l0] m0] n0].
    rewrite CallBounds_Right; auto.
Qed.

Theorem CombineDenotationPropRight {E k j i f h Y D M A} :
  SCPropSemiDenotation M
    ((SemiConversionCombineData (E := E) (k, j, i, f, h) D).2 M A)
    (PropCallLift k j i Y) =
  SCPropSemiDenotation (E := E) M (D.2 M A) Y.
Proof.
  elim: Y; try qauto.
  move=> x y.
  simpl.
  by do 2 rewrite CombineDenotationRight.
Qed.

Theorem CombineDenotationPropLeft {E G Y D M A} :
  CallBoundsP G.1.1.1.1 G.1.1.1.2 G.1.1.2 Y ->
  SCPropSemiDenotation M
    ((SemiConversionCombineData (E := E) G D).2 M A) Y =
  SCPropSemiDenotation (E := E) M (G.2 M A) Y.
Proof.
  elim: Y; try qauto.
  - move=> x IHx y IHy.
    simpl.
    intro.
    apply functional_extensionality=> u.
    f_equal.
    apply functional_extensionality=> r1; f_equal.
    rewrite IHy; auto.
    destruct (CallBoundsP _ _ _ _); auto.
    rewrite IHx; auto.
    destruct (CallBoundsP _ _ _ _); auto.
  - move=> x IHx y IHy.
    simpl.
    intro.
    apply functional_extensionality=> u.
    f_equal.
    apply functional_extensionality=> r1; f_equal.
    rewrite IHy; auto.
    destruct (CallBoundsP _ _ _ _); auto.
    rewrite IHx; auto.
    destruct (CallBoundsP _ _ _ _); auto.
  - move=> x IHx y IHy.
    simpl.
    intro.
    apply functional_extensionality=> u.
    f_equal.
    apply functional_extensionality=> r1; f_equal.
    rewrite IHy; auto.
    destruct (CallBoundsP _ _ _ _); auto.
    rewrite IHx; auto.
    destruct (CallBoundsP _ _ _ _); auto.
  - move=> x y.
    simpl.
    move=> chk.
    apply functional_extensionality=> u.
    f_equal.
    apply functional_extensionality=> r1; f_equal.
    all: rewrite CombineDenotationLeft; auto;
         by destruct (CallBounds _ _ _ _).
Qed.

Theorem SemiPropConvert_Correct {E M A} (r : @PropTermVS E) :
  PropVSDenotation FSize M r A = SCPropSemiDenotation M ((SemiPropConvert r).1.2 M A) (SemiPropConvert r).2.
Proof.
  elim: r; try qauto.
  - move=> x IHx y IHy.
    apply functional_extensionality=> u; simpl.
    rewrite (surjective_pairing (SemiPropConvert x))
            (surjective_pairing (SemiPropConvert y)); simpl.
    f_equal. 
    apply functional_extensionality=> r0; f_equal.
    destruct (SemiPropConvert x) as [[[[[k j] i] f] h] x2].
    by rewrite IHy CombineDenotationPropRight.
    rewrite IHx CombineDenotationPropLeft; auto.
    apply CallBoundsP_Correct.
  - move=> x IHx y IHy.
    apply functional_extensionality=> u; simpl.
    rewrite (surjective_pairing (SemiPropConvert x))
            (surjective_pairing (SemiPropConvert y)); simpl.
    f_equal. 
    apply functional_extensionality=> r0; f_equal.
    destruct (SemiPropConvert x) as [[[[[k j] i] f] h] x2].
    by rewrite IHy CombineDenotationPropRight.
    rewrite IHx CombineDenotationPropLeft; auto.
    apply CallBoundsP_Correct.
  - move=> x IHx y IHy.
    apply functional_extensionality=> u; simpl.
    rewrite (surjective_pairing (SemiPropConvert x))
            (surjective_pairing (SemiPropConvert y)); simpl.
    f_equal. 
    apply functional_extensionality=> r0; f_equal.
    destruct (SemiPropConvert x) as [[[[[k j] i] f] h] x2].
    by rewrite IHy CombineDenotationPropRight.
    rewrite IHx CombineDenotationPropLeft; auto.
    apply CallBoundsP_Correct.
  - move=> x y.
    apply functional_extensionality=> u; simpl.
    rewrite (surjective_pairing (SemiPolyConvert x))
            (surjective_pairing (SemiPolyConvert y)); simpl.
    f_equal. 
    apply functional_extensionality=> r0; f_equal.
    destruct (SemiPolyConvert x) as [[[[[k j] i] f] h] x2].
    by rewrite CombineDenotationRight SemiPolyConvert_Correct.
    rewrite CombineDenotationLeft.
    by rewrite <- SemiPolyConvert_Correct.
    apply CallBounds_Correct.
Qed.

Theorem Prenex_Semicircuit_Correct {E M} (p : @Prenex E) :
  PrenexDenotation FSize M p <-> @SCDenotation _ _ M (Prenex_Semicircuit p).1.
Proof.
  split.
  - move=>[A [H0 [H1 H2]]]; exists ((Prenex_Semicircuit p).2 M A).
    remember (Prenex_Semicircuit p) as PSP.
    destruct p; simpl in HeqPSP.
    rewrite (surjective_pairing (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- uniBounds]))
            (surjective_pairing (SemiPropConvert formula))
            (surjective_pairing (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- uniBounds]).1)
            (surjective_pairing (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- uniBounds]).1.1)
            (surjective_pairing (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- uniBounds]).1.1.1)
            (surjective_pairing (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- uniBounds]).1.1.1.1)
            (surjective_pairing (SemiConversionCombineData _ _))
            (surjective_pairing (SemiConversionCombineData _ _).1)
            (surjective_pairing (SemiConversionCombineData _ _).1.1)
            (surjective_pairing (SemiConversionCombineData _ _).1.1.1) in HeqPSP.
    do 4 rewrite <- surjective_pairing in HeqPSP.
    split;[|split;[|split;[|split;[|split;[|split;[|split;[|split]]]]]]].
    + rewrite HeqPSP; clear HeqPSP PSP; simpl.
      unfold SCFormulaCondition.
      move=>[u ltu]; simpl in *.
      assert (length uniBounds = length (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- uniBounds]).2) as e;[by rewrite SemiConversionCombineSeq_length map_length|].

      .
      unfold SCU; simpl.
    simpl.
    
    unfold SCDenotation.
    

    rewrite (surjective_pairing _.1).
    Search ((_.1, _.2)).
    remember (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- uniBounds]) as sbnd.
    destruct sbnd; simpl.
    remember (SemiPropConvert formula) as fbnd.
    destruct fbnd; simpl.
    destruct s; destruct p0; p1, p2.

End SemicircuitTranslation.

