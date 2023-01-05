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
Inductive SCPoly {E : seq nat} {IndC : nat} {ExiC : |[length E]| -> nat} {FreeC : nat -> nat} : Type :=
| PolyConsUndef : SCPoly
| PolyConsZero : SCPoly
| PolyConsPlusOne : SCPoly
| PolyConsMinusOne : SCPoly
| PolyConsPlus : SCPoly -> SCPoly -> SCPoly
| PolyConsTimes : SCPoly -> SCPoly -> SCPoly
| PolyConsInd : |[IndC]| -> SCPoly
| PolyConsFreeV : nat -> SCPoly
| PolyConsUniV : nat -> SCPoly
| PolyConsFreeF : forall i, |[FreeC i]| -> SCPoly
| PolyConsExiF : forall i, |[ExiC i]| -> SCPoly.

(* <S> in the paper *)
Inductive SCProp {E IndC ExiC FreeC} : Type :=
| ZOConsNot : SCProp -> SCProp
| ZOConsAnd : SCProp -> SCProp -> SCProp
| ZOConsOr : SCProp -> SCProp -> SCProp
| ZOConsImp : SCProp -> SCProp -> SCProp
| ZOConsEq : @SCPoly E IndC ExiC FreeC -> @SCPoly E IndC ExiC FreeC -> SCProp.

Record SemiCircuit {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} : Type :=
  mkSemiCircuit {
    (* nu : {s : |[exiV ctx]| -> { m : nat | m <= uniV ctx } | forall i j : |[exiV ctx]|, (` i) <= (` j) -> (` (s j)) <= (` (s i))}; *)
    indArgs0 : |[IndC0]| -> (@SCPoly E IndC0 ExiC0 FreeC0 * @SCPoly E IndC0 ExiC0 FreeC0);
    indArgsS : forall x : |[length E]|, 
               |[IndCS x]| -> 
                   (@SCPoly E (IndCS x) (ExiCS x) (FreeCS x) 
                  * @SCPoly E (IndCS x) (ExiCS x) (FreeCS x));
    (* w in paper *)
    freeFArgs0 : forall i a : nat, |[FreeC0 i]| -> (|[a]| -> @SCPoly E IndC0 ExiC0 FreeC0);
    freeFArgsS : forall x : |[length E]|, 
                 forall i a : nat, |[FreeCS x i]| -> (|[a]| -> @SCPoly E (IndCS x) (ExiCS x) (FreeCS x));
    (* omega in paper *)
    exiArgs0 : forall i, |[ExiC0 i]| -> (|[lnth E i]| -> @SCPoly E IndC0 ExiC0 FreeC0);
    exiArgsS : forall x : |[length E]|, 
                 forall i, |[ExiCS x i]| -> (|[lnth E i]| -> @SCPoly E (IndCS x) (ExiCS x) (FreeCS x));
    (* V in paper *)
    uniVBounds : seq (@SCPoly E IndC0 ExiC0 FreeC0);
    (* S, G and B in paper *)
    exiFBounds : forall i, (|[lnth E i]| -> @SCPoly E (IndCS i) (ExiCS i) (FreeCS i)) 
                          * @SCPoly E (IndCS i) (ExiCS i) (FreeCS i);
    formula : @SCProp E IndC0 ExiC0 FreeC0
  }.

(* Record SCInstance {ctx} {R : RingData} {c : @SemicircuitCtx ctx} : Type :=
  mkSCInstance { 
    (* v in paper *)
    freeVInst : |[freeV ctx]| -> T R;
    (* f in paper *)
    freeFInst : forall i : |[freeF ctx]|, (|[freeFA ctx i]| -> T R) -> option 'F_FSize;
  }. *)

Record SCAdvice {E IndC0} {ExiC0 : |[length E]| -> nat} {FreeC0 : nat -> nat} 
                {IndCS : |[length E]| -> nat} 
                {ExiCS : |[length E]| -> |[length E]| -> nat}
                {FreeCS : |[length E]| -> nat -> nat} 
                {M : @Sigma11Model FSize} : Type :=
  mkSCAdvice { 
    (* s and g in paper *)
    exiAdv : forall i, (|[lnth E i]| -> 'F_FSize) -> option 'F_FSize;
    (* o in paper *)
    (*Arguments are: which bound, which function, which call*)
    freeFCallOut0 : forall i, |[FreeC0 i]| -> (nat -> 'F_FSize) -> option 'F_FSize;
    freeFCallOutS : forall x : |[length E]|, forall i,  |[FreeCS x i]| -> (nat -> 'F_FSize) -> option 'F_FSize;
    (* sigma in paper *)
    (*Arguments are: which bound, which function, which call*)
    exiCallOut0 : forall i, |[ExiC0 i]| -> (nat -> 'F_FSize) -> option 'F_FSize;
    exiCallOutS : forall x : |[length E]|, forall i, |[ExiCS x i]| -> (nat -> 'F_FSize) -> option 'F_FSize;
    (*Arguments are: which bound, which call*)
    indCallOut0 : |[IndC0]| -> (nat -> 'F_FSize) -> option 'F_FSize;
    indCallOutS : forall x : |[length E]|, |[IndCS x]| -> (nat -> 'F_FSize) -> option 'F_FSize;
  }.

Fixpoint SCPolyDenotation0 {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M)
  (p : @SCPoly E IndC0 ExiC0 FreeC0) :
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
  | PolyConsExiF i j => exiCallOut0 adv i j
  end.

Fixpoint SCPolyDenotationS {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M)
  x (p : @SCPoly E (IndCS x) (ExiCS x) (FreeCS x)) :
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
  | PolyConsExiF i j => exiCallOutS adv x i j
  end.

Fixpoint SCPropDenotation {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M)
  (p : @SCProp E IndC0 ExiC0 FreeC0) :
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
  let ev i := SCPolyDenotation inst adv (lnth (polyConstraints c) (uniVBounds c i)) in
  forall i, 
    match (ev i t) with
    | None => false
    | Some e => lt R (t i) e
    end.

Definition U {ctx} {R} {c}
             (inst : @SCInstance ctx R (Ctx c)) (adv : @SCAdvice ctx R (Ctx c)) : Type 
  := { t : |[uniV ctx]| -> T R | UProp inst adv t }. *)


Definition SCInBound0 {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M)
  (r : 'F_FSize)
  (b : SCPoly) 
  (t : nat -> 'F_FSize) : bool :=
  match SCPolyDenotation0 adv b t with
  | None => false
  | Some e => r < e
  end.

Definition SCInBoundS {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) x
  (r : 'F_FSize)
  (b : SCPoly) 
  (t : nat -> 'F_FSize) : bool :=
  match SCPolyDenotationS adv x b t with
  | None => false
  | Some e => r < e
  end.

(*A collection of universal variables within *)
Program Definition SCU {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) 
  (f : @SemiCircuit E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS) : Type 
  := { u : |[length (uniVBounds f)]| -> 'F_FSize | 
       forall j : |[length (uniVBounds f)]|,
       forall v : nat -> 'F_FSize, 
       SCInBound0 adv (u j) (lnth (uniVBounds f) j) (MakeU u v)
    }.

Program Definition SCFormulaCondition {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) (f : SemiCircuit) : Prop :=
  forall (u : SCU adv f), 
  SCPropDenotation adv (formula f) (MakeU u (fun _ => 0%R)) == Some true.

(* Program Definition SCB {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) 
  (f : @SemiCircuit E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS) (x : |[length E]|) : Type 
  := { u : |[lnth E x]| -> 'F_FSize | 
       forall j : |[lnth E x]|,
       forall v : nat -> 'F_FSize, 
       SCInBoundS adv x (u j) ((exiFBounds f x).1 j) (MakeU u v)
    }. *)

Program Definition SCIndCondition0 {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall u : SCU adv c, forall i : |[IndC0]|,
  let (a1, a2) := indArgs0 c i in
  let b1 : option 'F_FSize := SCPolyDenotation0 adv a1 (MakeU u v) in
  let b2 : option 'F_FSize := SCPolyDenotation0 adv a2 (MakeU u v) in
  obind (fun b1 => obind (fun b2 => Some (indFun b1 b2)) b2) b1
  = indCallOut0 adv i (MakeU u v).

Program Definition SCIndConditionS {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M)
  (c : @SemiCircuit E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS) : Prop :=
  forall v : nat -> 'F_FSize, forall x : |[length E]|, forall i : |[IndCS x]|,
  forall (ins : |[lnth E x]| -> 'F_FSize) (out : 'F_FSize),
  exiAdv adv x ins == Some out -> 
  let (a1, a2) := indArgsS c x i in
  let b1 : option 'F_FSize := SCPolyDenotationS adv x a1 (MakeU ins v) in
  let b2 : option 'F_FSize := SCPolyDenotationS adv x a2 (MakeU ins v) in
  obind (fun b1 => obind (fun b2 => Some (indFun b1 b2)) b2) b1
  = indCallOutS adv x i (MakeU ins v).

Program Definition SCExiFCondition0 {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall u : SCU adv c, forall (i : |[length E]|) (j : |[ExiC0 i]|),
  let t (a : |[lnth E i]|) : option 'F_FSize
      := SCPolyDenotation0 adv (exiArgs0 c i j a) (MakeU u v) in
  obind (fun t => exiAdv adv i t) (option_fun t)  
  = exiCallOut0 adv i j (MakeU u v).

Program Definition SCExiFConditionS {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M)
  (c : @SemiCircuit E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS) : Prop :=
  forall v : nat -> 'F_FSize, forall x, forall (i : |[length E]|) (j : |[ExiCS x i]|),
  forall (ins : |[lnth E x]| -> 'F_FSize) (out : 'F_FSize),
  exiAdv adv x ins == Some out -> 
  let t (a : |[lnth E i]|) : option 'F_FSize
      := SCPolyDenotationS adv x (exiArgsS c x i j a) (MakeU ins v) in
  obind (fun t => exiAdv adv i t) (option_fun t)  
  = exiCallOutS adv x i j (MakeU ins v).

Program Definition SCFreeFCondition0 {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall u : SCU adv c, forall (i : |[length E]|) (j : |[FreeC0 i]|),
  let t a : option 'F_FSize
      := SCPolyDenotation0 adv (freeFArgs0 c i (projT1 (F_S _ M i)) j a) (MakeU u v) in
  obind (fun t => projT2 (F_S _ M i) t) (option_fun t)
  = freeFCallOut0 adv i j (MakeU u v).

Program Definition SCFreeFConditionS {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) 
  (c : @SemiCircuit E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS) : Prop :=
  forall v : nat -> 'F_FSize, forall x, forall (i : |[length E]|) (j : |[FreeCS x i]|),
  forall (ins : |[lnth E x]| -> 'F_FSize) (out : 'F_FSize),
  exiAdv adv x ins == Some out -> 
  let t a : option 'F_FSize
      := SCPolyDenotationS adv x (freeFArgsS c x i (projT1 (F_S _ M i)) j a) (MakeU ins v) in
  obind (fun t => projT2 (F_S _ M i) t) (option_fun t)
  = freeFCallOutS adv x i j (MakeU ins v).

Program Definition SCUniversalCondition {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) 
  (c : @SemiCircuit E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS) : Prop :=
  forall (u : nat -> 'F_FSize) (i : |[length (uniVBounds c)]|),
    (forall j : |[i]|, SCInBound0 adv (u j) (lnth (uniVBounds c) j) u) ->
    exists o, SCPolyDenotation0 adv (lnth (uniVBounds c) i) u = Some o.
Next Obligation. strivial use: ltn_trans. Qed.

Program Fixpoint SCFunBounds {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) (x : |[length E]|) {a}
  (ins : |[a]| -> 'F_FSize) (out : 'F_FSize)
  (insB : |[a]| -> SCPoly) (outB : SCPoly) :
  (nat -> 'F_FSize) -> bool := fun u =>
  match a with
  | 0 => SCInBoundS adv x out outB u
  | n.+1 => SCInBoundS adv x (ins 0) (insB 0) u &&
    @SCFunBounds E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M 
      adv x n (fun x => ins (x.+1)) out (fun x => insB (x.+1)) outB u
  end.

Definition SCExiBoundCondition {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M) 
  (c : @SemiCircuit E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS) : Prop :=
  forall u : nat -> 'F_FSize, forall i : |[length E]|,
  forall (ins : |[lnth E i]| -> 'F_FSize) (out : 'F_FSize),
  exiAdv adv i ins == Some out -> 
  SCFunBounds adv i ins out 
    (fun x => (exiFBounds c i).1 x)
    (exiFBounds c i).2 (MakeU ins u) == true.

Definition SCDenotation {E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS} {M : @Sigma11Model FSize}
  (c : SemiCircuit) : Prop :=
  exists (a : @SCAdvice E IndC0 ExiC0 FreeC0 IndCS ExiCS FreeCS M),
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

Program Fixpoint PolyCallCast {E IndC ExiC FreeC}
    {newIC : nat}
    {newEC : |[length E]| -> nat}
    {newFC : nat -> nat}
    (p : @SCPoly E IndC ExiC FreeC) :
  @SCPoly E (IndC + newIC) (fun x => ExiC x + newEC x) (fun x => FreeC x + newFC x) :=
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
  end.
Solve All Obligations with qauto use: ltn_addr.

(*Lift new polynomial args so names don't conflict with arguments from other polynomials *)
Program Fixpoint PolyCallLift {E IndC ExiC FreeC}
    {newIC : nat}
    {newEC : |[length E]| -> nat}
    {newFC : nat -> nat}
    (p : @SCPoly E IndC ExiC FreeC) :
  @SCPoly E (newIC + IndC) (fun x => newEC x + ExiC x) (fun x => newFC x + FreeC x) :=
  match p with
  | PolyConsUndef => PolyConsUndef
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
  | PolyConsInd i => PolyConsInd (newIC + i)
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i (newFC i + j)
  | PolyConsExiF i j => PolyConsExiF i (newEC i + j)
  end.
Solve All Obligations with qauto use: ltn_add2l.

Record SemiConversionData {E} {IndC : nat} {ExiC : |[length E]| -> nat} {FreeC : nat -> nat} : Type := 
  mkPolyConvertData {
  IndArgs : |[IndC]| -> (@SCPoly E IndC ExiC FreeC 
                                 * @SCPoly E IndC ExiC FreeC);
  ExiArgs : forall i, |[ExiC i]| -> |[lnth E i]| -> @SCPoly E IndC ExiC FreeC ;
  FreeArgs : forall i a, |[FreeC i]| -> |[a]| -> @SCPoly E IndC ExiC FreeC ;
  }.

Definition SemiConversionEmptyData {E} : 
  @SemiConversionData E 0 (fun _ => 0) (fun _ => 0) :=
  {| IndArgs := emptyTuple; ExiArgs := fun x => emptyTuple; FreeArgs := fun _ _ => emptyTuple; |}.

Program Definition SemiConversionCombineData {E nic1 nefc1 nffc1 nic2 nefc2 nffc2}
  (d1 : @SemiConversionData E nic1 nefc1 nffc1)
  (d2 : @SemiConversionData E nic2 nefc2 nffc2) : 
  @SemiConversionData E (nic1 + nic2) (fun x => nefc1 x + nefc2 x) (fun x => nffc1 x + nffc2 x) :=
  match d1, d2 with
  | {| FreeArgs := farg1; ExiArgs := earg1; IndArgs := iarg1 |}
  , {| FreeArgs := farg2; ExiArgs := earg2; IndArgs := iarg2 |}
  => 
   let SCP := @SCPoly E (nic1 + nic2) (fun x => nefc1 x + nefc2 x) (fun x => nffc1 x + nffc2 x) in
   {| FreeArgs := fun i a j => (
      if j < nffc1 i as b return j < nffc1 i = b -> |[a]| -> SCP
      then fun _ k => PolyCallCast (farg1 i a j k)
      else fun _ k => PolyCallLift (farg2 i a (j - nffc1 i) k)
    ) (erefl _)
    ; ExiArgs := fun i j => (
      if j < nefc1 i as b return j < nefc1 i = b -> |[lnth E i]| -> SCP
      then fun _ k => PolyCallCast (earg1 i j k)
      else fun _ k => PolyCallLift (earg2 i (j - nefc1 i) k)
    ) (erefl _) 
    ; IndArgs := fun i => (
      if i < nic1 as b return i < nic1 = b -> SCP * SCP
      then fun _ => let (u, v) := iarg1 i in (PolyCallCast u, PolyCallCast v)
      else fun _ => let (u, v) := iarg2 (i - nic1) in (PolyCallLift u, PolyCallLift v) 
    ) (erefl _) 
  |}
  end.
Next Obligation.
  assert (nic1 <= i);[
  hauto use: contraFltn, contra_not_leq unfold: is_true|qauto use: ltn_subLR, contraFltn].
Qed.
Next Obligation.
  assert (~ (j < nefc1 (exist _ i H1)));[hauto|].
  assert (nefc1 (exist _ i H1) <= j);[by apply (contra_not_leq (P := j < nefc1 (exist _ i H1)))|].
  qauto use: ltn_subLR, ltn_addr.
Qed.
Next Obligation.
  assert (~ (j < nffc1 i));[hauto|].
  assert (nffc1 i <= j);[by apply (contra_not_leq (P := j < nffc1 i))|].
  qauto use: ltn_subLR, ltn_addr.
Qed.

Fixpoint SemiConversionCombineSeq {E}
  (ds : seq { nc & @SemiConversionData E nc.1 nc.2.1 nc.2.2}) :
  @SemiConversionData E 
    (sumn (map (fun x => (projT1 x).1) ds)) 
    (fun x => sumn (map (fun z => (projT1 z).2.1 x) ds)) 
    (fun x => sumn (map (fun z => (projT1 z).2.2 x) ds)) :=
match ds with
| [::] => SemiConversionEmptyData
| existT _ x :: xs => SemiConversionCombineData x (SemiConversionCombineSeq xs)
end.

Program Fixpoint PolyConvert {E} (r : @PolyTermVS E) :
  { nc & 
    prod (@SemiConversionData E nc.1 nc.2.1 nc.2.2)
         (@SCPoly E nc.1 nc.2.1 nc.2.2) } := 
  match r with
  | PolyFVar m => existT _ SemiConversionEmptyData (EmptyDataAdvice, PolyConsFreeV m)
  | PolyUVar m => existT _ SemiConversionEmptyData (EmptyDataAdvice, PolyConsUniV m)
  | PolyFFun i t => PolyConvertFreeCase i (fun x => PolyConvert (t x))
  | PolyEFun i t => PolyConvertExiCase i (fun x => PolyConvert (t x))
  | PolyMinusOne => existT _ SemiConversionEmptyData (EmptyDataAdvice, PolyConsMinusOne)
  | PolyPlusOne => existT _ SemiConversionEmptyData (EmptyDataAdvice, PolyConsPlusOne)
  | PolyZero => existT _ SemiConversionEmptyData (EmptyDataAdvice, PolyConsZero)
  | PolyPlus r1 r2 => 
    let (d1, D1) := PolyConvert r1 in let (ad1, p1) := D1 in
    let (d2, D2) := PolyConvert r2 in let (ad2, p2) := D2 in
    existT _ (SemiConversionCombineData d1 d2)
             (CombineDataDenotation ad1 ad2
             ,PolyConsPlus (PolyCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) (newIC := newIndCalls d2) p1) 
                           (PolyCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) (newIC := newIndCalls d1) p2))
  | PolyTimes r1 r2 => 
    let (d1, D1) := PolyConvert r1 in let (ad1, p1) := D1 in
    let (d2, D2) := PolyConvert r2 in let (ad2, p2) := D2 in
    existT _ (SemiConversionCombineData d1 d2)
             (CombineDataDenotation ad1 ad2
             ,PolyConsTimes (PolyCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) (newIC := newIndCalls d2) p1) 
                            (PolyCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) (newIC := newIndCalls d1) p2))
  | PolyInd r1 r2 => PolyConvertIndCase (PolyConvert r1) (PolyConvert r2)
  end.
Next Obligation. by destruct d1, d2; unfold SemiConversionDataCtx; f_equal; apply functional_extensionality;move=>[x ltx]. Qed.
Next Obligation. by destruct d1, d2; unfold SemiConversionDataCtx; f_equal; apply functional_extensionality;move=>[x ltx]. Qed.
Next Obligation. by destruct d1, d2; unfold SemiConversionDataCtx; f_equal; apply functional_extensionality;move=>[x ltx]. Qed.
Next Obligation. by destruct d1, d2; unfold SemiConversionDataCtx; f_equal; apply functional_extensionality;move=>[x ltx]. Qed.


(* 
Record SemiConversionData {E} : Type := mkPolyConvertData {
  newIndCalls : nat ;
  newExiFCalls : |[length E]| -> nat ;
  newFreeFCalls : nat -> nat ;
  newFreeArgs : forall i a, |[newFreeFCalls i]| -> |[a]| -> @SCPoly E newIndCalls newExiFCalls newFreeFCalls ;
  newExiArgs : forall i, |[newExiFCalls i]| -> |[lnth E i]| -> @SCPoly E newIndCalls newExiFCalls newFreeFCalls ;
  newIndArgs : |[newIndCalls]| -> (@SCPoly E newIndCalls newExiFCalls newFreeFCalls 
                                 * @SCPoly E newIndCalls newExiFCalls newFreeFCalls)
  }.

Definition PolyConversionEmptyData {E} : 
  @SemiConversionData E :=
  {| newFreeFCalls := fun _ => 0; newExiFCalls := fun _ => 0; newIndCalls := 0;
     newFreeArgs := fun _ _ => emptyTuple; newExiArgs := fun x => emptyTuple; newIndArgs := emptyTuple|}.

Program Definition SemiConversionCombineData {E}
  (d1 d2 : @SemiConversionData E) : @SemiConversionData E :=
  match d1, d2 with
  | {| newFreeFCalls := nffc1; newExiFCalls := nefc1; newIndCalls := nic1; newFreeArgs := farg1; newExiArgs := earg1; newIndArgs := iarg1 |}
  , {| newFreeFCalls := nffc2; newExiFCalls := nefc2; newIndCalls := nic2; newFreeArgs := farg2; newExiArgs := earg2; newIndArgs := iarg2 |}
  => 
   let SCP := @SCPoly E (nic1 + nic2) (fun x => nefc1 x + nefc2 x) (fun x => nffc1 x + nffc2 x) in
   {| newFreeFCalls := fun x => nffc1 x + nffc2 x
    ; newExiFCalls := fun x => nefc1 x + nefc2 x
    ; newIndCalls := nic1 + nic2
    ; newFreeArgs := fun i a j => (
      if j < nffc1 i as b return j < nffc1 i = b -> |[a]| -> SCP
      then fun _ k => PolyCallCast (farg1 i a j k)
      else fun _ k => PolyCallLift (farg2 i a (j - nffc1 i) k)
    ) (erefl _)
    ; newExiArgs := fun i j => (
      if j < nefc1 i as b return j < nefc1 i = b -> |[lnth E i]| -> SCP
      then fun _ k => PolyCallCast (earg1 i j k)
      else fun _ k => PolyCallLift (earg2 i (j - nefc1 i) k)
    ) (erefl _) 
    ; newIndArgs := fun i => (
      if i < nic1 as b return i < nic1 = b -> SCP * SCP
      then fun _ => let (u, v) := iarg1 i in (PolyCallCast u, PolyCallCast v)
      else fun _ => let (u, v) := iarg2 (i - nic1) in (PolyCallLift u, PolyCallLift v) 
    ) (erefl _) 
  |}
  end.
Next Obligation.
  assert (~ (j < nffc1 i));[hauto|].
  assert (nffc1 i <= j);[by apply (contra_not_leq (P := j < nffc1 i))|].
  qauto use: ltn_subLR, ltn_addr.
Qed.
Next Obligation.
  assert (~ (j < nefc1 (exist _ i H1)));[hauto|].
  assert (nefc1 (exist _ i H1) <= j);[by apply (contra_not_leq (P := j < nefc1 (exist _ i H1)))|].
  qauto use: ltn_subLR, ltn_addr.
Qed.
Next Obligation.
  assert (nic1 <= i);[
  hauto use: contraFltn, contra_not_leq unfold: is_true|qauto use: ltn_subLR, contraFltn].
Qed.

Definition SemiDenotation {E} := 
  (forall i, (|[E i]| -> 'F_FSize) -> option 'F_FSize) ->
  (nat -> 'F_FSize) ->
  (@Sigma11Model FSize) -> @SemiCircuitAdvice E.


Program Definition CombineDataDenotation {E} 
  {d1 d2 : @SemiConversionData E}
  (ad1 : SemiDenotation (@SemiConversionDataCtx c d1) i j k)
  (ad2 : SemiDenotation (@SemiConversionDataCtx c d2) i j k) :
  SemiDenotation (@SemiConversionDataCtx c (SemiConversionCombineData d1 d2)) i j k :=
  fun X Y M =>
  let data' := (SemiConversionCombineData d1 d2) in
  let ctx' := SemiConversionDataCtx data' in
  {| exiVAdv := exiVAdv (ad1 X Y M)
   ; exiFAdv := exiFAdv (ad1 X Y M)
   ; freeFCallOut := fun i j => (
     if j < newFreeFCalls d1 i as b return j < newFreeFCalls d1 i = b -> (|[uniV c]| -> T D) -> option (T D)
     then fun _ => freeFCallOut (ad1 X Y M) i j
     else fun _ => freeFCallOut (ad2 X Y M) i (j - newFreeFCalls d1 i)
   ) (erefl _)
   ; exiFCallOut := fun i j => (
     if j < newExiFCalls d1 i as b return j < newExiFCalls d1 i = b -> (|[uniV c]| -> T D) -> option (T D)
     then fun _ => exiFCallOut (ad1 X Y M) i j
     else fun _ => exiFCallOut (ad2 X Y M) i (j - newExiFCalls d1 i)
   ) (erefl _) 
   ; indCallOut := fun i => (
     if i < newIndCalls d1 as b return i < newIndCalls d1 = b -> (|[uniV c]| -> T D) -> option (T D)
     then fun _ => indCallOut (ad1 X Y M) i
     else fun _ => indCallOut (ad2 X Y M) (i - newIndCalls d1)
   ) (erefl _) 
  |}.
Next Obligation. *)