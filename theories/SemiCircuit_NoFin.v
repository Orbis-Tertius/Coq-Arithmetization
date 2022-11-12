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
    (* V in paper *)
    uniVBoundsSC : seq (@SCPoly E);
    (* S, G and B in paper *)
    exiFBoundsSC : forall i, (|[lnth E i]| -> @SCPoly E) * @SCPoly E;
    formulaSC : @SCProp E;
    (* nu : {s : |[exiV ctx]| -> { m : nat | m <= uniV ctx } | forall i j : |[exiV ctx]|, (` i) <= (` j) -> (` (s j)) <= (` (s i))}; *)
    indArgsF : nat -> (@SCPoly E * @SCPoly E);
    indArgsU : nat -> nat -> (@SCPoly E * @SCPoly E);
    indArgsE : forall x : |[length E]|, 
               nat -> (@SCPoly E * @SCPoly E );
    (* w in paper *)
    freeFArgsF : forall i a : nat, nat -> (|[a]| -> @SCPoly E);
    freeFArgsU : forall b i a : nat, nat -> (|[a]| -> @SCPoly E);
    freeFArgsE : forall x : |[length E]|, 
                 forall i a j: nat, (|[a]| -> @SCPoly E);
    (* omega in paper *)
    exiArgsF : forall i, nat -> (|[lnth E i]| -> @SCPoly E);
    exiArgsU : nat -> forall i, nat -> (|[lnth E i]| -> @SCPoly E);
    exiArgsE : forall x : |[length E]|, 
                 forall i, nat -> (|[lnth E i]| -> @SCPoly E);
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
    indCallOutF : nat -> (nat -> 'F_FSize) -> option 'F_FSize;
    indCallOutU : nat -> nat -> (nat -> 'F_FSize) -> option 'F_FSize;
    indCallOutE : forall x : |[length E]|, nat -> (nat -> 'F_FSize) -> option 'F_FSize;
    (* sigma in paper *)
    (*Arguments are: which bound, which function, which call*)
    exiCallOutF : forall i j : nat, (nat -> 'F_FSize) -> option 'F_FSize;
    exiCallOutU : forall b i j : nat, (nat -> 'F_FSize) -> option 'F_FSize;
    exiCallOutE : forall x : |[length E]|, forall i j : nat, (nat -> 'F_FSize) -> option 'F_FSize;
    (* o in paper *)
    (*Arguments are: which bound, which function, which call*)
    freeFCallOutF : forall i j : nat, (nat -> 'F_FSize) -> option 'F_FSize;
    freeFCallOutU : forall b i j : nat, (nat -> 'F_FSize) -> option 'F_FSize;
    freeFCallOutE : forall x : |[length E]|, forall i j : nat, (nat -> 'F_FSize) -> option 'F_FSize;
  }.

Fixpoint SCPolyDenotationF {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  (p : @SCPoly E) :
  (nat -> 'F_FSize) -> option 'F_FSize :=
  match p with
  | PolyConsUndef => fun _ => None
  | PolyConsZero => fun _ => Some 0%R
  | PolyConsPlusOne => fun _ => Some 1%R
  | PolyConsMinusOne => fun _ => Some (-1)%R
  | PolyConsPlus p1 p2 => fun u =>
    let r1 := SCPolyDenotationF adv p1 u in
    let r2 := SCPolyDenotationF adv p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) r2) r1
  | PolyConsTimes p1 p2 => fun u =>
    let r1 := SCPolyDenotationF adv p1 u in
    let r2 := SCPolyDenotationF adv p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) r2) r1
  | PolyConsInd i => indCallOutF adv i
  | PolyConsFreeV i => fun _ => Some (V_F _ M i)
  | PolyConsUniV i => fun u => Some (u i)
  | PolyConsFreeF i j => freeFCallOutF adv i j
  | PolyConsExiF i j => exiCallOutF adv (` i) j
  end.

Fixpoint SCPolyDenotationU {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  x (p : @SCPoly E) :
  (nat -> 'F_FSize) -> option 'F_FSize :=
  match p with
  | PolyConsUndef => fun _ => None
  | PolyConsZero => fun _ => Some 0%R
  | PolyConsPlusOne => fun _ => Some 1%R
  | PolyConsMinusOne => fun _ => Some (-1)%R
  | PolyConsPlus p1 p2 => fun u =>
    let r1 := SCPolyDenotationU adv x p1 u in
    let r2 := SCPolyDenotationU adv x p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) r2) r1
  | PolyConsTimes p1 p2 => fun u =>
    let r1 := SCPolyDenotationU adv x p1 u in
    let r2 := SCPolyDenotationU adv x p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) r2) r1
  | PolyConsInd i => indCallOutU adv x i
  | PolyConsFreeV i => fun _ => Some (V_F _ M i)
  | PolyConsUniV i => fun u => Some (u i)
  | PolyConsFreeF i j => freeFCallOutU adv x i j
  | PolyConsExiF i j => exiCallOutU adv x (` i) j
  end.

Fixpoint SCPolyDenotationE {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  x (p : @SCPoly E) :
  (nat -> 'F_FSize) -> option 'F_FSize :=
  match p with
  | PolyConsUndef => fun _ => None
  | PolyConsZero => fun _ => Some 0%R
  | PolyConsPlusOne => fun _ => Some 1%R
  | PolyConsMinusOne => fun _ => Some (-1)%R
  | PolyConsPlus p1 p2 => fun u =>
    let r1 := SCPolyDenotationE adv x p1 u in
    let r2 := SCPolyDenotationE adv x p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) r2) r1
  | PolyConsTimes p1 p2 => fun u =>
    let r1 := SCPolyDenotationE adv x p1 u in
    let r2 := SCPolyDenotationE adv x p2 u in 
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) r2) r1
  | PolyConsInd i => indCallOutE adv x i
  | PolyConsFreeV i => fun _ => Some (V_F _ M i)
  | PolyConsUniV i => fun u => Some (u i)
  | PolyConsFreeF i j => freeFCallOutE adv x i j
  | PolyConsExiF i j => exiCallOutE adv x (` i) j
  end.

Fixpoint SCPropDenotation {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  (p : @SCProp E) :
  (nat -> 'F_FSize) -> option bool :=
  match p with
  | ZOConsNot p => fun u => 
    let r := SCPropDenotation adv p u in
    obind (fun r => Some (negb r)) r
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
    let r1 := SCPolyDenotationF adv p1 u in
    let r2 := SCPolyDenotationF adv p2 u in
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


Definition SCInBoundF {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  (r : 'F_FSize)
  (b : SCPoly) 
  (t : nat -> 'F_FSize) : bool :=
  match SCPolyDenotationF adv b t with
  | None => false
  | Some e => r < e
  end.

Definition SCInBoundU {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  (r : 'F_FSize)
  x (b : SCPoly) 
  (t : nat -> 'F_FSize) : bool :=
  match SCPolyDenotationU adv x b t with
  | None => false
  | Some e => r < e
  end.

Definition SCInBoundE {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  (r : 'F_FSize)
  x (b : SCPoly) 
  (t : nat -> 'F_FSize) : bool :=
  match SCPolyDenotationE adv x b t with
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
       SCInBoundU adv (u j) j (lnth (uniVBoundsSC f) j) (MakeU u v)
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

Program Definition SCIndConditionF {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall i, forall u : SCU adv c, 
  let (a1, a2) := indArgsF c i in
  let b1 : option 'F_FSize := SCPolyDenotationF adv a1 (MakeU u v) in
  let b2 : option 'F_FSize := SCPolyDenotationF adv a2 (MakeU u v) in
  obind (fun b1 => obind (fun b2 => Some (indFun b1 b2)) b2) b1
  = indCallOutF adv i (MakeU u v).

Program Definition SCIndConditionU {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : SemiCircuit) : Prop :=
  forall (x : |[length (uniVBoundsSC c)]|) i, forall (u : nat -> 'F_FSize),
    (forall j : |[x]|, SCInBoundU adv (u j) j (lnth (uniVBoundsSC c) j) u) ->
  let (a1, a2) := indArgsU c x i in
  let b1 : option 'F_FSize := SCPolyDenotationU adv x a1 u in
  let b2 : option 'F_FSize := SCPolyDenotationU adv x a2 u in
  obind (fun b1 => obind (fun b2 => Some (indFun b1 b2)) b2) b1
  = indCallOutU adv x i u.
Next Obligation. by apply (ltn_trans H). Qed.

Program Definition SCIndConditionE {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  (c : @SemiCircuit E) : Prop :=
  forall v : nat -> 'F_FSize, forall x : |[length E]|, forall i,
  forall (ins : |[lnth E x]| -> 'F_FSize) (out : 'F_FSize),
  exiAdv adv x ins == Some out -> 
  let (a1, a2) := indArgsE c x i in
  let b1 : option 'F_FSize := SCPolyDenotationE adv x a1 (MakeU ins v) in
  let b2 : option 'F_FSize := SCPolyDenotationE adv x a2 (MakeU ins v) in
  obind (fun b1 => obind (fun b2 => Some (indFun b1 b2)) b2) b1
  = indCallOutE adv x i (MakeU ins v).

Program Definition SCExiFConditionF {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall u : SCU adv c, forall (i : |[length E]|) j,
  let t (a : |[lnth E i]|) : option 'F_FSize
      := SCPolyDenotationF adv (exiArgsF c i j a) (MakeU u v) in
  obind (fun t => exiAdv adv i t) (option_fun t)  
  = exiCallOutF adv i j (MakeU u v).

Program Definition SCExiFConditionU {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : SemiCircuit) : Prop :=
  forall (x : |[length (uniVBoundsSC c)]|) (i : |[length E]|) j,
  forall (u : nat -> 'F_FSize), (forall j : |[x]|, SCInBoundU adv (u j) j (lnth (uniVBoundsSC c) j) u) ->
  let t (a : |[lnth E i]|) : option 'F_FSize
      := SCPolyDenotationU adv x (exiArgsU c x i j a) u in
  obind (fun t => exiAdv adv i t) (option_fun t)  
  = exiCallOutU adv x i j u.
Next Obligation. by apply (ltn_trans H). Qed.

Program Definition SCExiFConditionE {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  (c : @SemiCircuit E) : Prop :=
  forall v : nat -> 'F_FSize, forall x, forall (i : |[length E]|) j,
  forall (ins : |[lnth E x]| -> 'F_FSize) (out : 'F_FSize),
  exiAdv adv x ins == Some out -> 
  let t (a : |[lnth E i]|) : option 'F_FSize
      := SCPolyDenotationE adv x (exiArgsE c x i j a) (MakeU ins v) in
  obind (fun t => exiAdv adv i t) (option_fun t)  
  = exiCallOutE adv x i j (MakeU ins v).

Program Definition SCFreeFConditionF {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall u : SCU adv c, forall (i : |[length E]|) j,
  let t a : option 'F_FSize
      := SCPolyDenotationF adv (freeFArgsF c i (projT1 (F_S _ M i)) j a) (MakeU u v) in
  obind (fun t => projT2 (F_S _ M i) t) (option_fun t)
  = freeFCallOutF adv i j (MakeU u v).

Program Definition SCFreeFConditionU {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : SemiCircuit) : Prop :=
  forall u : SCU adv c, forall (x : |[length (uniVBoundsSC c)]|) (i : |[length E]|) j,
  forall (u : nat -> 'F_FSize), (forall j : |[x]|, SCInBoundU adv (u j) j (lnth (uniVBoundsSC c) j) u) ->
  let t a : option 'F_FSize
      := SCPolyDenotationU adv x (freeFArgsU c x i (projT1 (F_S _ M i)) j a) u in
  obind (fun t => projT2 (F_S _ M i) t) (option_fun t)
  = freeFCallOutU adv x i j u.
Next Obligation. by apply (ltn_trans H). Qed.

Program Definition SCFreeFConditionE {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) 
  (c : @SemiCircuit E) : Prop :=
  forall v : nat -> 'F_FSize, forall x, forall (i : |[length E]|) j,
  forall (ins : |[lnth E x]| -> 'F_FSize) (out : 'F_FSize),
  exiAdv adv x ins == Some out -> 
  let t a : option 'F_FSize
      := SCPolyDenotationE adv x (freeFArgsE c x i (projT1 (F_S _ M i)) j a) (MakeU ins v) in
  obind (fun t => projT2 (F_S _ M i) t) (option_fun t)
  = freeFCallOutE adv x i j (MakeU ins v).

Program Definition SCUniversalCondition {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) 
  (c : @SemiCircuit E) : Prop :=
  forall (u : nat -> 'F_FSize) (i : |[length (uniVBoundsSC c)]|),
    (forall j : |[i]|, SCInBoundF adv (u j) (lnth (uniVBoundsSC c) j) u) ->
  exists o, SCPolyDenotationF adv (lnth (uniVBoundsSC c) i) u = Some o.
Next Obligation. strivial use: ltn_trans. Qed.

Program Fixpoint SCFunBounds {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (x : |[length E]|) {a}
  (ins : |[a]| -> 'F_FSize) (out : 'F_FSize)
  (insB : |[a]| -> SCPoly) (outB : SCPoly) :
  (nat -> 'F_FSize) -> bool := fun u =>
  match a with
  | 0 => SCInBoundE adv out x outB u
  | n.+1 => SCInBoundE adv (ins 0) x (insB 0) u &&
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
    SCIndConditionF a c /\
    SCIndConditionU a c /\
    SCIndConditionE a c /\
    SCExiFConditionF a c /\
    SCExiFConditionU a c /\
    SCExiFConditionE a c /\
    SCFreeFConditionF a c /\
    SCFreeFConditionU a c /\
    SCFreeFConditionE a c /\
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

Theorem SemiAdviceEta {A} : 
  {| IndCOut := IndCOut A; ExiCOut := ExiCOut A; FreeCOut := FreeCOut A |} = A.
Proof. by destruct A. Qed.

Theorem SemiAdviceMatch {X A} {F : _ -> _ -> _ -> X} :
  (match A with
   | {| IndCOut := iarg1; ExiCOut := earg1; FreeCOut := farg1 |} =>
      F iarg1 earg1 farg1
  end) = F (IndCOut A) (ExiCOut A) (FreeCOut A).
Proof. by destruct A. Qed.

Theorem SemiConversionDataEta {E A} : 
  {| IndArgs := IndArgs A; ExiArgs := ExiArgs A; FreeArgs := FreeArgs (E := E) A |} = A.
Proof. by destruct A. Qed.

Theorem SemiConversionDataMatch {X E A} {F : _ -> _ -> _ -> X} :
  (match A with
   | {| IndArgs := iarg1; ExiArgs := earg1; FreeArgs := farg1 |} =>
      F iarg1 earg1 farg1
  end) = F (IndArgs A) (ExiArgs A) (FreeArgs (E := E) A).
Proof. by destruct A. Qed.

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
 {| IndArgs := fun x => if x == n then (p1, p2) else IndArgs d x
 ; ExiArgs := ExiArgs d; FreeArgs := FreeArgs d |}.

Definition AddIndCall {E} n v (d : @SemiAdviceGenerator E) : SemiAdviceGenerator :=
  fun M A =>
  {| IndCOut := fun x => if x == n then PolyVSDenotation _ M v A else IndCOut (d M A) x
   ; ExiCOut := ExiCOut (d M A); FreeCOut := FreeCOut (d M A) |}.

Program Definition AddExiArg {E} i n (ps : |[lnth E i]| -> @SCPoly E) (d : @SemiConversionData E) : SemiConversionData :=
 {| IndArgs := IndArgs d
  ; ExiArgs := fun i' =>
    (if i == i' as b return (i == i') = b -> nat -> |[lnth E i']| -> SCPoly
      then fun _ x => if x == n then ps else ExiArgs d i' x
      else fun _ => ExiArgs d i') (erefl _)
  ; FreeArgs := FreeArgs d |}.
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
  {| IndCOut := IndCOut (d M A)
    ; ExiCOut := fun i' =>
      if i == i'
      then fun x => (if x == n then (PolyVSDenotation _ M ps A) else ExiCOut (d M A) i' x)
      else ExiCOut (d M A) i'
    ; FreeCOut := FreeCOut (d M A) |}.

Program Definition AddFreeArg {E a} i n (ps : |[a]| -> @SCPoly E) (d : @SemiConversionData E) : SemiConversionData :=
  {| IndArgs := IndArgs d; ExiArgs := ExiArgs d
  ; FreeArgs := fun i' =>
    if i == i' 
    then fun a' =>
          (if a == a' as b return (a == a') = b -> nat -> |[a']| -> SCPoly
          then fun _ x => if x == n then ps else FreeArgs d i' a' x
          else fun _ => FreeArgs d i' a') (erefl _)
    else FreeArgs d i'|}.
Next Obligation. by apply EEConvert in e; destruct e. Qed.
Next Obligation. by apply EEConvert in e; destruct e. Qed.

Program Definition AddFreeCall {E} i n (ps : @PolyTermVS E) (d : @SemiAdviceGenerator E) : SemiAdviceGenerator :=
  fun M A =>
  {| IndCOut := IndCOut (d M A); ExiCOut := ExiCOut (d M A)
    ; FreeCOut := fun i' =>
      if i == i'
      then fun x => (if x == n then (PolyVSDenotation _ M ps A) else FreeCOut (d M A) i' x)
      else FreeCOut (d M A) i' |}.

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

Theorem CallBounds_Left {E G n D} :
  CallBounds G.1.1.1.1 G.1.1.1.2 G.1.1.2 n ->
  CallBounds (E := E)
             (SemiConversionCombineData G D).1.1.1.1
             (SemiConversionCombineData G D).1.1.1.2
             (SemiConversionCombineData (E := E) G D).1.1.2 
             n.
Proof.
  elim: n; try qauto; destruct G as [[[[i j] k] l] m].
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

Theorem CallBounds_Left_Sum {E n0 n1 n2 a0 a1 a2 s} :
  CallBounds (E := E) n0 n1 n2 s ->
  CallBounds (n0 + a0)
    (fun x : nat => n1 x + a1 x)
    (fun x : nat => n2 x + a2 x) s.
Proof.
  elim: s; try qauto.
  - move=> x IHx y IHy H.
    simpl.
    simpl in H.
    rewrite IHx.
    rewrite IHy; auto.
    by destruct (CallBounds n0 n1 n2 x), (CallBounds n0 n1 n2 y).
    by destruct (CallBounds n0 n1 n2 x).
  - move=> x IHx y IHy H.
    simpl.
    simpl in H.
    rewrite IHx.
    rewrite IHy; auto.
    by destruct (CallBounds n0 n1 n2 x), (CallBounds n0 n1 n2 y).
    by destruct (CallBounds n0 n1 n2 x).
  - move=> n; apply ltn_addr.
  - move=> i j; apply ltn_addr.
  - move=> i j; apply ltn_addr.
Qed.

Theorem CallBounds_Right {E G n D} :
  CallBounds G.1.1.1.1 G.1.1.1.2 G.1.1.2 n ->
  CallBounds (E := E) (SemiConversionCombineData D G).1.1.1.1
    (SemiConversionCombineData D G).1.1.1.2
    (SemiConversionCombineData (E := E) D G).1.1.2 
    (PolyCallLift D.1.1.1.1 D.1.1.1.2 D.1.1.2 n).
Proof.
  elim: n; try qauto; destruct G as [[[[i j] k] l] m].
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

Theorem CallBounds_Right_Sum {E n0 n1 n2 a0 a1 a2 s} :
  CallBounds (E := E) n0 n1 n2 s ->
  CallBounds (a0 + n0)
    (fun x : nat => a1 x + n1 x)
    (fun x : nat => a2 x + n2 x) 
    (PolyCallLift a0 a1 a2 s).
Proof.
  elim: s; try qauto.
  - move=> x IHx y IHy H.
    simpl.
    simpl in H.
    rewrite IHx.
    rewrite IHy; auto.
    by destruct (CallBounds n0 n1 n2 x), (CallBounds n0 n1 n2 y).
    by destruct (CallBounds n0 n1 n2 x).
  - move=> x IHx y IHy H.
    simpl.
    simpl in H.
    rewrite IHx.
    rewrite IHy; auto.
    by destruct (CallBounds n0 n1 n2 x), (CallBounds n0 n1 n2 y).
    by destruct (CallBounds n0 n1 n2 x).
  - move=> n; simpl; by rewrite ltn_add2l.
  - move=> i j; simpl; by rewrite ltn_add2l.
  - move=> i j; simpl; by rewrite ltn_add2l.
Qed.

Theorem CallBounds_Correct {E} (r : @PolyTermVS E) :
  CallBounds (SemiPolyConvert r).1.1.1.1.1 (SemiPolyConvert r).1.1.1.1.2 (SemiPolyConvert r).1.1.1.2 (SemiPolyConvert r).2.
Proof.
  elim: r; try qauto.
  - move=> i a p IH.
    simpl.
    rewrite (P6Eta (SemiConversionCombineTup _)); simpl.
    rewrite eq_refl.
    apply ltnSn.
  - move=> i p IH.
    simpl.
    rewrite (P6Eta (SemiConversionCombineTup _)); simpl.
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
(* 
Definition UniConv {E}
  (e : forall i, @PolyTermVS E) :
  forall i, @SemiConversionDataBundle E * @SCPoly E) :=
fun i =>
  let (bs, y) := e i in
  let (bundbs, bs') := SemiConversionCombineTup (fun x => SemiPolyConvert (bs x)) in
  match bundbs with
  | (nic, nefc, nffc, dat, gen) => 
    let (bundy, y') := SemiPolyConvert y in
    (SemiConversionCombineData bundbs bundy, (bs', PolyCallLift nic nefc nffc y'))
  end. *)

Definition AdviceGenerator {E} := forall M : @Sigma11Model FSize, PrenexAdvice FSize E -> @SCAdvice FSize E M.
(* (nat * (nat -> nat) * (nat -> nat) * @SemiConversionData E * @SemiAdviceGenerator E)%type. *)

Definition defaultBund {E} : SemiConversionDataBundle (E := E)
  := (0, fun _=>0, fun _=>0, SemiConversionEmptyData, EmptyGenerator).

Definition Prenex_Semicircuit {E} (p : @Prenex E) : @SemiCircuit E  * @AdviceGenerator E :=
match p with
| {| uniBounds := ub; exiBounds := eb; formula := f |} =>
  let (ubund', upols) := unzipSeq (map SemiPolyConvert ub) in
  let ubund := nth defaultBund ubund' in
  let (fbund, fprop) := SemiPropConvert f in
  let (ebund, epols) := unzip_dep (ExiConv eb) in
  ({| indArgsF := IndArgs fbund.1.2;
      indArgsU := fun i => IndArgs (ubund i).1.2;
      indArgsE := fun i => IndArgs (ebund i).1.2;
      exiArgsF := ExiArgs fbund.1.2;
      exiArgsU := fun i => ExiArgs (ubund i).1.2;
      exiArgsE := fun i => ExiArgs (ebund i).1.2;
      freeFArgsF := FreeArgs fbund.1.2;
      freeFArgsU := fun i => FreeArgs (ubund i).1.2;
      freeFArgsE := fun i => FreeArgs (ebund i).1.2;
      uniVBoundsSC := upols;
      exiFBoundsSC := epols;
      formulaSC := fprop
   |}, fun M A => 
   {| exiAdv := A;
      indCallOutF := IndCOut (fbund.2 M A);
      indCallOutU := fun i => IndCOut ((ubund i).2 M A);
      indCallOutE := fun i => IndCOut ((ebund i).2 M A);
      exiCallOutF := ExiCOut (fbund.2 M A);
      exiCallOutU := fun i => ExiCOut ((ubund i).2 M A);
      exiCallOutE := fun i => ExiCOut ((ebund i).2 M A);
      freeFCallOutF := FreeCOut (fbund.2 M A);
      freeFCallOutU := fun i => FreeCOut ((ubund i).2 M A);
      freeFCallOutE := fun i => FreeCOut ((ebund i).2 M A);
   |})
end.

Theorem SemiConversionCombineSeq_length {E ds} : length (@SemiConversionCombineSeq E ds).2 = length ds.
Proof.
  elim: ds; auto.
  intros.
  simpl.
  rewrite (P6Eta a)
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

Theorem CombineDenotationRight {E G Y D M A} :
  SCPolySemiDenotation M
    ((SemiConversionCombineData (E := E) G D).2 M A)
    (PolyCallLift G.1.1.1.1 G.1.1.1.2 G.1.1.2 Y) =
  SCPolySemiDenotation (E := E) M (D.2 M A) Y.
Proof.
  elim: Y; try qauto.
  - move=> n.
    simpl.
    unfold IndCOut.
    destruct G as [[[[k i] j] f] h]; simpl.
    destruct f, D, p, p, p, s0; simpl.
    unfold CombineGens.
    destruct (h M A); simpl.
    destruct (s M A); simpl.
    by rewrite LTPF kpmnken.
  - move=> i0 j0.
    simpl.
    unfold FreeCOut.
    destruct G as [[[[k i] j] f] h]; simpl.
    destruct f, D, p, p, p, s0; simpl.
    unfold CombineGens.
    destruct (h M A); simpl.
    destruct (s M A); simpl.
    by rewrite LTPF kpmnken.
  - move=> i0 n.
    simpl.
    unfold ExiCOut.
    destruct G as [[[[k i] j] f] h]; simpl.
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

Theorem CallBoundsP_Left {E A n D} :
  CallBoundsP A.1.1.1.1 A.1.1.1.2 A.1.1.2 n ->
  CallBoundsP (E := E)
              (SemiConversionCombineData A D).1.1.1.1
              (SemiConversionCombineData A D).1.1.1.2
              (SemiConversionCombineData (E := E) A D).1.1.2 
              n.
Proof.
  elim: n; try qauto; destruct A as [[[[k j] i] l] h].
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
    rewrite <- (SemiConversionDataEta (A := l)).
    rewrite (P5Eta D).
    rewrite <- (SemiConversionDataEta (A := D.1.2)).
    simpl.
    rewrite CallBounds_Left_Sum.
    rewrite CallBounds_Left_Sum; auto.
    all: by destruct (CallBounds k j i x), (CallBounds k j i y).
Qed.

Theorem CallBoundsP_Right {E A n D} :
  CallBoundsP A.1.1.1.1 A.1.1.1.2 A.1.1.2 n ->
  CallBoundsP (E := E) (SemiConversionCombineData D A).1.1.1.1
    (SemiConversionCombineData D A).1.1.1.2
    (SemiConversionCombineData (E := E) D A).1.1.2 
    (PropCallLift D.1.1.1.1 D.1.1.1.2 D.1.1.2 n).
Proof.
  elim: n; try qauto; destruct A as [[[[k j] i] l] h].
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
    all: simpl; by destruct (CallBounds k j i x), (CallBounds k j i y).
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

Theorem CombineDenotationPropRight {E G Y D M A} :
  SCPropSemiDenotation M
    ((SemiConversionCombineData (E := E) G D).2 M A)
    (PropCallLift G.1.1.1.1 G.1.1.1.2 G.1.1.2 Y) =
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

Theorem DenotToSemiDenotePolyF {E M PCL adv} :
  SCPolyDenotationF FSize (E := E) (M := M) adv PCL =
  SCPolySemiDenotation M 
    {| IndCOut := indCallOutF _ adv; ExiCOut := exiCallOutF _ adv; FreeCOut := freeFCallOutF _ adv |} PCL.
Proof. elim PCL; try qauto. Qed.

Theorem DenotToSemiDenotePolyU {E M PCL adv x} :
  SCPolyDenotationU FSize (E := E) (M := M) adv x PCL =
  SCPolySemiDenotation M 
    {| IndCOut := indCallOutU _ adv x; ExiCOut := exiCallOutU _ adv x; FreeCOut := freeFCallOutU _ adv x |} PCL.
Proof. elim PCL; try qauto. Qed.

Theorem DenotToSemiDenotePolyE {E M PCL adv x} :
  SCPolyDenotationE FSize (E := E) (M := M) adv x PCL =
  SCPolySemiDenotation M 
    {| IndCOut := indCallOutE _ adv x; ExiCOut := exiCallOutE _ adv x; FreeCOut := freeFCallOutE _ adv x |} PCL.
Proof. elim PCL; try qauto. Qed.

Theorem DenotToSemiDenoteProp {E M PCL adv} :
  SCPropDenotation FSize (E := E) (M := M) adv PCL =
  SCPropSemiDenotation M
    {| IndCOut := indCallOutF _ adv; ExiCOut := exiCallOutF _ adv; FreeCOut := freeFCallOutF _ adv |} PCL.
Proof. 
  elim PCL; try qauto.
  move=> s IH.
  simpl.
  apply functional_extensionality=> u; f_equal.
  apply functional_extensionality=> x; f_equal.
  all: by rewrite DenotToSemiDenotePolyF.
Qed.

Definition SCInBound0 {E} (M : @Sigma11Model FSize)
  (adv : SemiAdvice)
  (r : 'F_FSize)
  (b : SCPoly) 
  (t : nat -> 'F_FSize) : bool :=
  match SCPolySemiDenotation (E := E) M adv b t with
  | None => false
  | Some e => r < e
  end.

Theorem SCInBound0_InBound {E M} a b u adv :
  InBound (E := E) FSize M adv a b u =
  SCInBound0 M ((SemiPolyConvert b).1.2 M adv) a (SemiPolyConvert b).2 u.
Proof.
  unfold SCInBound0, InBound.
  by rewrite SemiPolyConvert_Correct.
Qed.


Theorem SemiConversionCombineSeq_Part {E M A b j} ej1 ej2 :
  SCPolySemiDenotation M
    ((SemiConversionCombineSeq [seq SemiPolyConvert i | i <- b]).1.2 M A)
    (lnth (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- b]).2 (exist _ j ej1))
  = SCPolySemiDenotation (E := E) M 
      ((SemiPolyConvert (lnth b (exist _ j ej2))).1.2 M A)
      (SemiPolyConvert (lnth b (exist _ j ej2))).2.
Proof.
  move: j ej1 ej2 A.
  elim: b;[fcrush|].
  move=> a l IH j ej1 ej2 A.
  remember (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- a :: l]) as aaa.
  replace (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- a :: l])
    with (SemiConversionCombineData (SemiPolyConvert a).1 (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- l]).1
  ,(SemiPolyConvert a).2 :: map (PolyCallLift (SemiPolyConvert a).1.1.1.1.1 (SemiPolyConvert a).1.1.1.1.2 (SemiPolyConvert a).1.1.1.2) (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- l]).2)
    in Heqaaa;[
    | simpl;
      destruct (SemiPolyConvert a) as [[[[[i0 j0] k0] [l00 l01 l02]] m0] n0];
      by destruct (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- l]) as [[[[[i1 j1] k1] [l10 l11 l12]] m1] n1]].
  simpl.
  move: ej1; rewrite Heqaaa; clear Heqaaa aaa; simpl=> ej1.
  destruct j;[rewrite CombineDenotationLeft; auto; apply CallBounds_Correct|simpl].
  rewrite lnth_map CombineDenotationRight; simpl.
  remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as ee; clear Heqee; simpl in ee.
  by rewrite <- (IH j ee ej2).
Qed.

Theorem CallBoundsSeq {E l j ej1 ej2} :
  CallBounds (lnth l (exist _ j ej1)).1.1.1.1.1 
             (lnth l (exist _ j ej1)).1.1.1.1.2
             (lnth l (exist _ j ej1)).1.1.1.2 
             (lnth l (exist _ j ej1)).2 
  ->
  CallBounds (E := E)
    (SemiConversionCombineSeq l).1.1.1.1.1
    (SemiConversionCombineSeq l).1.1.1.1.2
    (SemiConversionCombineSeq l).1.1.1.2
    (lnth (SemiConversionCombineSeq l).2 (exist _ j ej2)).
Proof.
  move: j ej1 ej2; elim: l;[move=>j ej1;fcrush|].
  move=> a l IH j ej1 ej2 H.
  simpl.
  move: ej2.
  rewrite (P6Eta a); simpl;
  rewrite (P6Eta (SemiConversionCombineSeq l)); simpl;
  rewrite <- (SemiConversionDataEta (A := a.1.1.2)); simpl.
  move=> ltj.
  rewrite SemiConversionDataMatch.
  destruct j.
  by apply CallBounds_Left_Sum.
  rewrite lnth_map; simpl.
  apply CallBounds_Right_Sum.
  by apply (IH j ej1 _).
Qed.

Theorem add_lte_split {i j k} : i + j <= k -> (i <= k) /\ (j <= k).
Proof.
  move=> ltk.
  split.
  - move: i ltk; elim: k;[by destruct i, j|].
    destruct i; auto.
    move=> lt.
    by apply H.
  - move: j ltk; elim: k;[by destruct i, j|].
    destruct j; auto.
    move=> lt.
    apply H.
    by rewrite addnS in lt.
Qed.

(* Theorem IndCOut_SeqNone {E M A u v i} :
  (SemiConversionCombineSeq (E := E) u).1.1.1.1.1 <= i ->
  IndCOut ((SemiConversionCombineSeq (E := E) u).1.2 M A) i v = None.
Proof.
  move:i; elim:u;[(destruct i; auto)|].
  move=> a l IH i.
  simpl;
  rewrite (P6Eta a)
          (surjective_pairing (SemiConversionCombineSeq _))
          (P5Eta ((SemiConversionCombineSeq _).1));
  do 2 rewrite SemiConversionDataMatch; simpl=> lti.
  unfold CombineGens.
  do 2 rewrite SemiAdviceMatch; simpl.
  assert (i < a.1.1.1.1.1 = false).
    destruct a as [[[[[i0 n] m] l0] k] j];auto;simpl in *.
    clear j k l0 n m.
    move: i lti; elim: i0; destruct i; auto; apply H.
  rewrite H.
  rewrite IH; auto.
  remember ((SemiConversionCombineSeq _).1.1.1.1.1) as A0; clear HeqA0.
  destruct a as [[[[[i0 n] m] l0] k] j];auto;simpl in *.
  clear j k l0 n m H IH.
  move: i0 A0 lti; elim: i; destruct i0, A0; auto; by apply H.
Qed. *)
(* 
Theorem IndCOut_Seq {E M A u v i} :
  i < (SemiConversionCombineSeq (E := E) u).1.1.1.1.1 ->
  IndCOut ((SemiConversionCombineSeq (E := E) u).1.2 M A) i v = 
  nth None (map (fun x => IndCOut (x.1.2 M A) i v) u) i.
Proof.
  move:i; elim:u;[(destruct i; auto)|].
  move=> a l IH i.
  simpl;
  rewrite (P6Eta a)
          (surjective_pairing (SemiConversionCombineSeq _))
          (P5Eta ((SemiConversionCombineSeq _).1));
  do 2 rewrite SemiConversionDataMatch; simpl=> lti.
  unfold CombineGens.
  do 2 rewrite SemiAdviceMatch; simpl.
  destruct a as [[[[[i0 n] m] l0] k] j];auto;simpl in *.
  destruct (i < i0).
  assert (i < a.1.1.1.1.1 = false).
    destruct a as [[[[[i0 n] m] l0] k] j];auto;simpl in *.
    clear j k l0 n m.
    move: i lti; elim: i0; destruct i; auto; apply H.
  rewrite H.
  rewrite IH; auto.
  remember ((SemiConversionCombineSeq _).1.1.1.1.1) as A0; clear HeqA0.
  destruct a as [[[[[i0 n] m] l0] k] j];auto;simpl in *.
  clear j k l0 n m H IH.
  move: i0 A0 lti; elim: i; destruct i0, A0; auto; by apply H.
Qed. *)
(* 
Theorem ExiCOut_SeqNone {E M A u v i} :
  (forall x, (SemiConversionCombineSeq (E := E) u).1.1.1.1.2 x <= i x) ->
  forall x, ExiCOut ((SemiConversionCombineSeq (E := E) u).1.2 M A) x (i x) v = None.
Proof.
  move=> H x.
  remember (H x) as Hx; clear HeqHx H.
  remember (i x) as ix; clear Heqix i.
  move: ix Hx; elim:u;[(destruct ix; auto)|].
  move=> a l IH ix.
  simpl;
  rewrite (P6Eta a)
          (surjective_pairing (SemiConversionCombineSeq _))
          (P5Eta ((SemiConversionCombineSeq _).1));
  do 2 rewrite SemiConversionDataMatch; simpl=> lti.
  unfold CombineGens; do 2 rewrite SemiAdviceMatch; simpl.
  assert (ix < a.1.1.1.1.2 x = false).
    destruct a as [[[[[i0 n] m] l0] k] j];auto;simpl in *.
    remember (n x) as nx; clear Heqnx.
    move: ix lti; elim: nx; destruct ix; auto; apply H.
  rewrite H.
  rewrite IH; auto.
  remember ((SemiConversionCombineSeq _).1.1.1.1.2) as A0; clear HeqA0.
  destruct a as [[[[[i0 n] m] l0] k] j];auto;simpl in *.
  clear H.
  remember (n x) as nx; remember (A0 x) as Ax; clear Heqnx HeqAx IH x.
  move: ix lti; elim: nx; destruct ix, Ax; auto; by apply H.
Qed.

Theorem FreeCOut_SeqNone {E M A u v i} :
  (forall x, (SemiConversionCombineSeq (E := E) u).1.1.1.2 x <= i x) ->
  forall x, FreeCOut ((SemiConversionCombineSeq (E := E) u).1.2 M A) x (i x) v = None.
Proof.
  move=> H x.
  remember (H x) as Hx; clear HeqHx H.
  remember (i x) as ix; clear Heqix i.
  move: ix Hx; elim:u;[(destruct ix; auto)|].
  move=> a l IH ix.
  simpl;
  rewrite (P6Eta a)
          (surjective_pairing (SemiConversionCombineSeq _))
          (P5Eta ((SemiConversionCombineSeq _).1));
  do 2 rewrite SemiConversionDataMatch; simpl=> lti.
  unfold CombineGens; do 2 rewrite SemiAdviceMatch; simpl.
  assert (ix < a.1.1.1.2 x = false).
    destruct a as [[[[[i0 n] m] l0] k] j];auto;simpl in *.
    remember (m x) as mx; clear Heqmx.
    move: ix lti; elim: mx; destruct ix; auto; apply H.
  rewrite H.
  rewrite IH; auto.
  remember ((SemiConversionCombineSeq _).1.1.1.2) as A0; clear HeqA0.
  destruct a as [[[[[i0 n] m] l0] k] j];auto;simpl in *.
  clear H.
  remember (m x) as mx; remember (A0 x) as Ax; clear Heqmx HeqAx IH x.
  move: ix lti; elim: mx; destruct ix, Ax; auto; by apply H.
Qed. *)

Theorem IndCOut_Comb_Left {E M A g f v i} :
  i < g.1.1.1.1 ->
  IndCOut ((SemiConversionCombineData (E := E) g f).2 M A) i v = 
  IndCOut (g.2 M A) i v.
Proof.
  unfold SemiConversionCombineData.
  rewrite (P5Eta g) (P5Eta f).
  do 2 rewrite SemiConversionDataMatch.
  simpl.
  unfold CombineGens.
  do 2 rewrite SemiAdviceMatch; simpl=> lti.
  by rewrite lti.
Qed.

Theorem IndCOut_Comb_Right {E M A g f v i} :
  g.1.1.1.1 <= i ->
  IndCOut ((SemiConversionCombineData (E := E) g f).2 M A) i v = 
  IndCOut (f.2 M A) (i - g.1.1.1.1) v.
Proof.
  unfold SemiConversionCombineData.
  rewrite (P5Eta g) (P5Eta f).
  do 2 rewrite SemiConversionDataMatch.
  simpl.
  unfold CombineGens.
  do 2 rewrite SemiAdviceMatch; simpl=> lti.
  assert (i < g.1.1.1.1 = false).
    destruct g as [[[[n m] l0] k] j];auto;simpl in *.
    move: i lti; elim: n; destruct i; auto; apply H.
  by rewrite H.
Qed.

Theorem IndArgs_Comb_Left_1 {E M A g f v i} :
  CallBounds g.1.1.1.1 g.1.1.1.2 g.1.1.2 (IndArgs g.1.2 i).1 ->
  i < g.1.1.1.1 ->
  SCPolySemiDenotation M
    ((SemiConversionCombineData (E := E) g f).2 M A)
    (IndArgs (SemiConversionCombineData g f).1.2 i).1 v =
  SCPolySemiDenotation M (g.2 M A) (IndArgs g.1.2 i).1 v.
Proof.
  move=> H0.
  unfold SemiConversionCombineData.
  rewrite (P5Eta g) (P5Eta f).
  do 2 rewrite SemiConversionDataMatch.
  simpl.
  rewrite <- (CombineDenotationLeft (D := f)); auto.
  unfold SemiConversionCombineData.
  rewrite (P5Eta g) (P5Eta f).
  do 2 rewrite SemiConversionDataMatch.
  simpl.
  unfold CombineGens.
  do 2 rewrite SemiAdviceMatch; simpl=> lti.
  rewrite lti.
  by rewrite (surjective_pairing (IndArgs _ _)); simpl.
Qed.

Theorem IndArgs_Comb_Right_1 {E M A g f v i} :
  g.1.1.1.1 <= i ->
  SCPolySemiDenotation M
    ((SemiConversionCombineData (E := E) g f).2 M A)
    (IndArgs (SemiConversionCombineData g f).1.2 i).1 v =
  SCPolySemiDenotation M (f.2 M A) (IndArgs f.1.2 (i - g.1.1.1.1)).1 v.
Proof.
  unfold SemiConversionCombineData.
  rewrite (P5Eta g) (P5Eta f).
  do 2 rewrite SemiConversionDataMatch.
  simpl.
  rewrite <- (CombineDenotationRight (G := g)).
  unfold SemiConversionCombineData.
  rewrite (P5Eta g) (P5Eta f).
  do 2 rewrite SemiConversionDataMatch.
  simpl.
  unfold CombineGens.
  do 2 rewrite SemiAdviceMatch; simpl=> lti.
  assert (i < g.1.1.1.1 = false).
    destruct g as [[[[n m] l0] k] j];auto;simpl in *.
    move: i lti; elim: n; destruct i; auto; apply H.
  rewrite H; simpl.
  rewrite (surjective_pairing (IndArgs f.1.2 (i - g.1.1.1.1))); simpl.
  auto.
Qed.

Theorem IndArgs_Comb_Left_2 {E M A g f v i} :
  CallBounds g.1.1.1.1 g.1.1.1.2 g.1.1.2 (IndArgs g.1.2 i).2 ->
  i < g.1.1.1.1 ->
  SCPolySemiDenotation M
    ((SemiConversionCombineData (E := E) g f).2 M A)
    (IndArgs (SemiConversionCombineData g f).1.2 i).2 v =
  SCPolySemiDenotation M (g.2 M A) (IndArgs g.1.2 i).2 v.
Proof.
  move=> H0.
  unfold SemiConversionCombineData.
  rewrite (P5Eta g) (P5Eta f).
  do 2 rewrite SemiConversionDataMatch.
  simpl.
  rewrite <- (CombineDenotationLeft (D := f)); auto.
  unfold SemiConversionCombineData.
  rewrite (P5Eta g) (P5Eta f).
  do 2 rewrite SemiConversionDataMatch.
  simpl.
  unfold CombineGens.
  do 2 rewrite SemiAdviceMatch; simpl=> lti.
  rewrite lti.
  by rewrite (surjective_pairing (IndArgs _ _)); simpl.
Qed.

Theorem IndArgs_Comb_Right_2 {E M A g f v i} :
  g.1.1.1.1 <= i ->
  SCPolySemiDenotation M
    ((SemiConversionCombineData (E := E) g f).2 M A)
    (IndArgs (SemiConversionCombineData g f).1.2 i).2 v =
  SCPolySemiDenotation M (f.2 M A) (IndArgs f.1.2 (i - g.1.1.1.1)).2 v.
Proof.
  unfold SemiConversionCombineData.
  rewrite (P5Eta g) (P5Eta f).
  do 2 rewrite SemiConversionDataMatch.
  simpl.
  rewrite <- (CombineDenotationRight (G := g)).
  unfold SemiConversionCombineData.
  rewrite (P5Eta g) (P5Eta f).
  do 2 rewrite SemiConversionDataMatch.
  simpl.
  unfold CombineGens.
  do 2 rewrite SemiAdviceMatch; simpl=> lti.
  assert (i < g.1.1.1.1 = false).
    destruct g as [[[[n m] l0] k] j];auto;simpl in *.
    move: i lti; elim: n; destruct i; auto; apply H.
  rewrite H; simpl.
  rewrite (surjective_pairing (IndArgs f.1.2 (i - g.1.1.1.1))); simpl.
  auto.
Qed.

Theorem IndArgs_Right_1 {E G F i} :
  G.1.1.1.1 <= i ->
  (IndArgs (SemiConversionCombineData G F).1.2 i).1 = 
  PolyCallLift (E := E) G.1.1.1.1 G.1.1.1.2 G.1.1.2 (IndArgs F.1.2 (i - G.1.1.1.1)).1.
Proof.
  move=> lti.
  unfold SemiConversionCombineData.
  rewrite (P5Eta G) (P5Eta F).
  do 2 rewrite SemiConversionDataMatch.
  simpl.
  assert (i < G.1.1.1.1 = false).
    destruct G as [[[[n m] l0] k] j];auto;simpl in *.
    move: i lti; elim: n; destruct i; auto; apply H.
  rewrite H.
  by rewrite (surjective_pairing (IndArgs _ _)).
Qed.

Theorem IndArgs_Right_2 {E G F i} :
  G.1.1.1.1 <= i ->
  (IndArgs (SemiConversionCombineData G F).1.2 i).2 = 
  PolyCallLift (E := E) G.1.1.1.1 G.1.1.1.2 G.1.1.2 (IndArgs F.1.2 (i - G.1.1.1.1)).2.
Proof.
  move=> lti.
  unfold SemiConversionCombineData.
  rewrite (P5Eta G) (P5Eta F).
  do 2 rewrite SemiConversionDataMatch.
  simpl.
  assert (i < G.1.1.1.1 = false).
    destruct G as [[[[n m] l0] k] j];auto;simpl in *.
    move: i lti; elim: n; destruct i; auto; apply H.
  rewrite H.
  by rewrite (surjective_pairing (IndArgs _ _)).
Qed.

Theorem IndArgs_Left_1 {E G F i} :
  i < G.1.1.1.1 ->
  (IndArgs (SemiConversionCombineData (E := E) G F).1.2 i).1 = (IndArgs G.1.2 i).1.
Proof.
  move=> lti.
  unfold SemiConversionCombineData.
  rewrite (P5Eta G) (P5Eta F).
  do 2 rewrite SemiConversionDataMatch.
  simpl.
  rewrite lti.
  by rewrite (surjective_pairing (IndArgs _ _)).
Qed.

Theorem IndArgs_Left_2 {E G F i} :
  i < G.1.1.1.1 ->
  (IndArgs (SemiConversionCombineData (E := E) G F).1.2 i).2 = (IndArgs G.1.2 i).2.
Proof.
  move=> lti.
  unfold SemiConversionCombineData.
  rewrite (P5Eta G) (P5Eta F).
  do 2 rewrite SemiConversionDataMatch.
  simpl.
  rewrite lti.
  by rewrite (surjective_pairing (IndArgs _ _)).
Qed.

Theorem CallBounds_Poly_IndArgs_1 {E p i} :
  CallBounds (E := E)
    (SemiPolyConvert p).1.1.1.1.1 (SemiPolyConvert p).1.1.1.1.2 (SemiPolyConvert p).1.1.1.2 
    (IndArgs (SemiPolyConvert p).1.1.2 i).1.
Proof.
  move: i.
  elim: p; try qauto.
  move=> i a p IH j.
  simpl.
  rewrite (P6Eta (SemiConversionCombineTup _)); simpl.
Admitted.

Theorem CallBounds_Poly_IndArgs_2 {E p i} :
  CallBounds (E := E)
    (SemiPolyConvert p).1.1.1.1.1 (SemiPolyConvert p).1.1.1.1.2 (SemiPolyConvert p).1.1.1.2 
    (IndArgs (SemiPolyConvert p).1.1.2 i).2.
Proof.
  move: i.
  elim: p; try qauto.
  move=> i a p IH j.
  simpl.
  rewrite (P6Eta (SemiConversionCombineTup _)); simpl.
Admitted.

Theorem CallBounds_Prop_IndArgs_1 {E p i} :
  CallBounds (E := E)
    (SemiPropConvert p).1.1.1.1.1 (SemiPropConvert p).1.1.1.1.2 (SemiPropConvert p).1.1.1.2 
    (IndArgs (SemiPropConvert p).1.1.2 i).1.
Proof.
  move: i.
  elim: p.
  qauto.
  all: try 
    ( move=> p IHp q IHq i;
      simpl;
      rewrite (surjective_pairing (SemiPropConvert p))
              (surjective_pairing (SemiPropConvert q)); simpl;
      destruct ((SemiPropConvert p).1.1.1.1.1 <= i) eqn:lti;[
      (rewrite IndArgs_Right_1; auto;apply CallBounds_Right; auto)|
      (rewrite IndArgs_Left_1);[apply CallBounds_Left;auto|]];
      move: i lti; elim: (SemiPropConvert p).1.1.1.1.1; destruct i; auto; apply H
    ).
  simpl.
  move=> p q i.
  rewrite (surjective_pairing (SemiPolyConvert p))
          (surjective_pairing (SemiPolyConvert q)); simpl.
  destruct ((SemiPolyConvert p).1.1.1.1.1 <= i) eqn:lti.
  rewrite IndArgs_Right_1; auto;apply CallBounds_Right; auto.
  apply CallBounds_Poly_IndArgs_1.
  rewrite IndArgs_Left_1.
  apply CallBounds_Left; auto.
  apply CallBounds_Poly_IndArgs_1.
  move: i lti; elim: (SemiPolyConvert p).1.1.1.1.1; destruct i; auto; apply H.
Qed.

Theorem CallBounds_Prop_IndArgs_2 {E p i} :
  CallBounds (E := E)
    (SemiPropConvert p).1.1.1.1.1 (SemiPropConvert p).1.1.1.1.2 (SemiPropConvert p).1.1.1.2 
    (IndArgs (SemiPropConvert p).1.1.2 i).2.
Proof.
  move: i.
  elim: p.
  qauto.
  all: try 
    ( move=> p IHp q IHq i;
      simpl;
      rewrite (surjective_pairing (SemiPropConvert p))
              (surjective_pairing (SemiPropConvert q)); simpl;
      destruct ((SemiPropConvert p).1.1.1.1.1 <= i) eqn:lti;[
      (rewrite IndArgs_Right_2; auto;apply CallBounds_Right; auto)|
      (rewrite IndArgs_Left_2);[apply CallBounds_Left;auto|]];
      move: i lti; elim: (SemiPropConvert p).1.1.1.1.1; destruct i; auto; apply H
    ).
  simpl.
  move=> p q i.
  rewrite (surjective_pairing (SemiPolyConvert p))
          (surjective_pairing (SemiPolyConvert q)); simpl.
  destruct ((SemiPolyConvert p).1.1.1.1.1 <= i) eqn:lti.
  rewrite IndArgs_Right_2; auto;apply CallBounds_Right; auto.
  apply CallBounds_Poly_IndArgs_2.
  rewrite IndArgs_Left_2.
  apply CallBounds_Left; auto.
  apply CallBounds_Poly_IndArgs_2.
  move: i lti; elim: (SemiPolyConvert p).1.1.1.1.1; destruct i; auto; apply H.
Qed.

Theorem Prenex_Semicircuit_Correct_Lem_1_0 {E M A i v N o} {u : |[N]| -> 'F_FSize} {p} :
  PolyVSDenotation (E := E) FSize M p A (MakeU u (fun=> 0%R)) = Some o ->
  obind (fun b1 =>
    obind (fun b2 => Some (indFun b1 b2))
      (SCPolySemiDenotation M ((SemiPolyConvert p).1.2 M A)
          (IndArgs (SemiPolyConvert p).1.1.2 i).2 (MakeU u v)))
    (SCPolySemiDenotation M ((SemiPolyConvert p).1.2 M A)
      (IndArgs (SemiPolyConvert p).1.1.2 i).1 (MakeU u v)) =
  IndCOut ((SemiPolyConvert p).1.2 M A) i (MakeU u v).
Proof.
  move: i o.
  elim: p; try qauto.
  move=> i a p IH j o H.
  simpl.
  rewrite (P6Eta (SemiConversionCombineTup _)); simpl.
Admitted.

Theorem Prenex_Semicircuit_Correct_Lem_1_1 {E M A i u o} {p} :
  PolyVSDenotation (E := E) FSize M p A u = Some o ->
  obind (fun b1 =>
    obind (fun b2 => Some (indFun b1 b2))
      (SCPolySemiDenotation M ((SemiPolyConvert p).1.2 M A)
          (IndArgs (SemiPolyConvert p).1.1.2 i).2 u))
    (SCPolySemiDenotation M ((SemiPolyConvert p).1.2 M A)
      (IndArgs (SemiPolyConvert p).1.1.2 i).1 u) =
  IndCOut ((SemiPolyConvert p).1.2 M A) i u.
Proof.
  move: i o.
  elim: p; try qauto.
  move=> i a p IH j o H.
  simpl.
  rewrite (P6Eta (SemiConversionCombineTup _)); simpl.
Admitted.

Theorem Prenex_Semicircuit_Correct_Lem_1 {E M A i v a b} {u : |[a]| -> 'F_FSize} {f} :
  PropVSDenotation (E := E) FSize M f A (MakeU u (fun=> 0%R)) == Some b ->
  obind
    (fun b1 : 'F_FSize =>
    obind (fun b2 : 'F_FSize => Some (indFun b1 b2))
      (SCPolySemiDenotation M ((SemiPropConvert f).1.2 M A)
          (IndArgs (SemiPropConvert f).1.1.2 i).2 
          (MakeU u v)))
    (SCPolySemiDenotation M ((SemiPropConvert f).1.2 M A)
      (IndArgs (SemiPropConvert f).1.1.2 i).1 
      (MakeU u v)) =
  IndCOut ((SemiPropConvert f).1.2 M A) i (MakeU u v).
Proof.
  move: i b.
  elim: f.
  - move=> p IHp i b H.
    simpl.
    rewrite (surjective_pairing (SemiPropConvert p)); simpl.
    assert (PropVSDenotation FSize M p A (MakeU u (fun=> 0%R)) == Some (~~ b)).
    simpl in H.
    destruct (PropVSDenotation FSize M p A (MakeU u (fun=> 0%R))); auto.
    simpl in H.
    by destruct b0, b.
    by apply (IHp i (~~ b)).
  - move=> p IHp q IHq i b H.
    simpl.
    do 2 rewrite (surjective_pairing (SemiPropConvert _)); simpl.
    simpl in H.
    destruct (PropVSDenotation FSize M q A (MakeU u (fun=> 0%R))),
             (PropVSDenotation FSize M p A (MakeU u (fun=> 0%R))); simpl in H;[|fcrush|fcrush|fcrush].
    destruct ((SemiPropConvert p).1.1.1.1.1 <= i) eqn:lti.
    rewrite IndCOut_Comb_Right; auto.
    rewrite <- (IHq _ b0 (eq_refl _)).
    rewrite IndArgs_Comb_Right_1; auto.
    by rewrite IndArgs_Comb_Right_2.
    assert (i < (SemiPropConvert p).1.1.1.1.1).
      assert (~ ((SemiPropConvert p).1.1.1.1.1 <= i));[sauto|clear lti].
      remember (SemiPropConvert p).1.1.1.1.1 as AA; clear HeqAA.
      move:i H0; elim:AA; destruct i; try qauto.
    rewrite IndCOut_Comb_Left; auto.
    rewrite <- (IHp _ b1 (eq_refl _)).
    rewrite IndArgs_Comb_Left_1; auto;[|apply CallBounds_Prop_IndArgs_1].
    rewrite IndArgs_Comb_Left_2; auto;apply CallBounds_Prop_IndArgs_2.
  - move=> p IHp q IHq i b H.
    simpl.
    do 2 rewrite (surjective_pairing (SemiPropConvert _)); simpl.
    simpl in H.
    destruct (PropVSDenotation FSize M q A (MakeU u (fun=> 0%R))),
             (PropVSDenotation FSize M p A (MakeU u (fun=> 0%R))); simpl in H;[|fcrush|fcrush|fcrush].
    destruct ((SemiPropConvert p).1.1.1.1.1 <= i) eqn:lti.
    rewrite IndCOut_Comb_Right; auto.
    rewrite <- (IHq _ b0 (eq_refl _)).
    rewrite IndArgs_Comb_Right_1; auto.
    by rewrite IndArgs_Comb_Right_2.
    assert (i < (SemiPropConvert p).1.1.1.1.1).
      assert (~ ((SemiPropConvert p).1.1.1.1.1 <= i));[sauto|clear lti].
      remember (SemiPropConvert p).1.1.1.1.1 as AA; clear HeqAA.
      move:i H0; elim:AA; destruct i; try qauto.
    rewrite IndCOut_Comb_Left; auto.
    rewrite <- (IHp _ b1 (eq_refl _)).
    rewrite IndArgs_Comb_Left_1; auto;[|apply CallBounds_Prop_IndArgs_1].
    rewrite IndArgs_Comb_Left_2; auto;apply CallBounds_Prop_IndArgs_2.
  - move=> p IHp q IHq i b H.
    simpl.
    do 2 rewrite (surjective_pairing (SemiPropConvert _)); simpl.
    simpl in H.
    destruct (PropVSDenotation FSize M q A (MakeU u (fun=> 0%R))),
             (PropVSDenotation FSize M p A (MakeU u (fun=> 0%R))); simpl in H;[|fcrush|fcrush|fcrush].
    destruct ((SemiPropConvert p).1.1.1.1.1 <= i) eqn:lti.
    rewrite IndCOut_Comb_Right; auto.
    rewrite <- (IHq _ b0 (eq_refl _)).
    rewrite IndArgs_Comb_Right_1; auto.
    by rewrite IndArgs_Comb_Right_2.
    assert (i < (SemiPropConvert p).1.1.1.1.1).
      assert (~ ((SemiPropConvert p).1.1.1.1.1 <= i));[sauto|clear lti].
      remember (SemiPropConvert p).1.1.1.1.1 as AA; clear HeqAA.
      move:i H0; elim:AA; destruct i; try qauto.
    rewrite IndCOut_Comb_Left; auto.
    rewrite <- (IHp _ b1 (eq_refl _)).
    rewrite IndArgs_Comb_Left_1; auto;[|apply CallBounds_Prop_IndArgs_1].
    rewrite IndArgs_Comb_Left_2; auto;apply CallBounds_Prop_IndArgs_2.
  move=> p q i b H.
  simpl.
  do 2 rewrite (surjective_pairing (SemiPolyConvert _)); simpl in *.
  remember (PolyVSDenotation FSize M q A (MakeU u (fun=> 0%R))) as PCVq.
  remember (PolyVSDenotation FSize M p A (MakeU u (fun=> 0%R))) as PCVp.
  destruct PCVq, PCVp;[|fcrush|fcrush|fcrush].
  simpl in H.
  destruct ((SemiPolyConvert p).1.1.1.1.1 <= i) eqn:lti.
  rewrite IndCOut_Comb_Right; auto.
  rewrite IndArgs_Comb_Right_1; auto.
  rewrite IndArgs_Comb_Right_2; auto.
  rewrite (Prenex_Semicircuit_Correct_Lem_1_0 (o := o)); qauto.
  assert (i < (SemiPolyConvert p).1.1.1.1.1);[
    move:i lti; elim:(SemiPolyConvert p).1.1.1.1.1; destruct i; auto; apply H0|].
  rewrite IndCOut_Comb_Left; auto.
  rewrite IndArgs_Comb_Left_1; auto;[|apply CallBounds_Poly_IndArgs_1].
  rewrite IndArgs_Comb_Left_2; auto;[|apply CallBounds_Poly_IndArgs_2].
  rewrite (Prenex_Semicircuit_Correct_Lem_1_0 (o := o0)); qauto.
Qed.

Theorem Prenex_Semicircuit_Correct_Lem_2_in  {E M A N ins out insB outB v} :
FunBoundsVS FSize M A ins out insB outB (MakeU ins v) == true ->
forall (i : |[N]|),
exists o, PolyVSDenotation (E := E) FSize M (insB i) A (MakeU (n := N) ins v) = Some o.
Proof. Admitted.

Theorem Prenex_Semicircuit_Correct_Lem_2_out  {E M A N ins out insB outB v} :
FunBoundsVS FSize M A ins out insB outB (MakeU ins v) == true ->
exists o, PolyVSDenotation (E := E) FSize M outB A (MakeU (n := N) ins v) = Some o.
Proof. Admitted.

Theorem Prenex_Semicircuit_Correct {E M} (p : @Prenex E) :
  PrenexDenotation FSize M p <-> @SCDenotation _ _ M (Prenex_Semicircuit p).1.
Proof.
  split.
  - move=>[A [H0 [H1 H2]]]; exists ((Prenex_Semicircuit p).2 M A).
    remember (Prenex_Semicircuit p) as PSP.
    destruct p; simpl in HeqPSP.
    rewrite (surjective_pairing (unzipSeq _))
            (surjective_pairing (SemiPropConvert formula)) in HeqPSP.
    split;[|split;[|split;[|split;[|split;[|split;[|split;[|split;[|split;[|split;[|split]]]]]]]]]].
    + rewrite HeqPSP; clear HeqPSP PSP; simpl.
      unfold SCFormulaCondition.
      move=>[u ltu]; simpl in *.
      rewrite DenotToSemiDenoteProp; simpl.
      rewrite SemiAdviceEta.
      rewrite <- SemiPropConvert_Correct.
      assert (length (unzipSeq [seq SemiPolyConvert i | i <- uniBounds]).2 = length uniBounds) as H00;[
        by rewrite unzipSeqLengthRight map_length|].
      remember (eq_rect _ (fun x => |[x]| -> _) u _ H00) as u'; simpl in u'.
      assert (forall (j : |[length uniBounds]|) (v : nat -> 'F_FSize),
             InBound FSize M A (u' j) (lnth uniBounds j) (MakeU u' v)).
          move=> [j0 ltj] v.
          assert (j0 < length (unzipSeq [seq SemiPolyConvert i | i <- uniBounds]).2) as ltj';[qauto|].
          remember (ltu (exist _ j0 ltj') v) as ltu'; clear Heqltu' ltu.
          unfold InBound.
          rewrite SemiPolyConvert_Correct.
          unfold SCInBoundU in ltu'.
          rewrite DenotToSemiDenotePolyU SemiAdviceEta in ltu'; simpl in ltu'.
          replace (u' (exist _ j0 ltj)) with (u (exist _ j0 ltj')).
          replace (MakeU u' v) with (MakeU u v).
          remember (SCPolySemiDenotation _ _ _) as SCP.
          replace (SCPolySemiDenotation _ _ _) with SCP; auto.
          rewrite HeqSCP; clear ltu' HeqSCP SCP.
          rewrite unzipSeqLnthRight lnth_map.
          remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD; clear HeqDDD; simpl in DDD.
          move: DDD; rewrite projT1_eq_rect; simpl=> DDD.
          assert (ltj = DDD) as EE;[apply eq_irrelevance|destruct EE].
          remember (unzipSeq [seq SemiPolyConvert i | i <- uniBounds]).1.
          replace (unzipSeq [seq SemiPolyConvert i | i <- uniBounds]).1
             with [seq (SemiPolyConvert i).1 | i <- uniBounds] in Heql;[|by rewrite unzipSeqMapLeft].
          rewrite Heql; clear Heql l.
          change defaultBund with (SemiPolyConvert (E := E) UndefVS).1.
          rewrite (nth_map (f := fun x => (SemiPolyConvert x).1)).
          by rewrite (lnth_nth UndefVS); simpl.
          rewrite Hequ'; clear Hequ' u' ltu'.
          by destruct H00.
          rewrite Hequ'; clear Hequ' u' ltu'.
          rewrite eq_rect_ap_el; f_equal.
          by apply subset_eq; rewrite projT1_eq_rect.
      remember (H0 (exist _ u' H)) as H0'; clear HeqH0' H0; simpl in H0'; clear H.
      replace (MakeU u (fun=> 0%R)) with (MakeU u' (fun=> 0%R)); auto.
      rewrite Hequ'; clear Hequ' u' H0'.
      by destruct H00.
    + rewrite HeqPSP; clear HeqPSP PSP; simpl.
      unfold SCIndConditionF; simpl.
      move=> v0 i [u ltu]; simpl in *.
      rewrite (surjective_pairing (IndArgs _ _)).
      assert (length (unzipSeq [seq SemiPolyConvert i | i <- uniBounds]).2 = length uniBounds) as H00;[
              by rewrite unzipSeqLengthRight map_length|].
      remember (eq_rect _ (fun x => |[x]| -> _) u _ H00) as u'; simpl in u'.
      assert (forall (j : |[length uniBounds]|) (v : nat -> 'F_FSize),
             InBound FSize M A (u' j) (lnth uniBounds j) (MakeU u' v)).
          move=> [j0 ltj] v.
          assert (j0 < length (unzipSeq [seq SemiPolyConvert i | i <- uniBounds]).2) as ltj';[qauto|].
          remember (ltu (exist _ j0 ltj') v) as ltu'; clear Heqltu' ltu.
          unfold InBound.
          rewrite SemiPolyConvert_Correct.
          unfold SCInBoundU in ltu'.
          rewrite DenotToSemiDenotePolyU SemiAdviceEta in ltu'; simpl in ltu'.
          replace (u' (exist _ j0 ltj)) with (u (exist _ j0 ltj')).
          replace (MakeU u' v) with (MakeU u v).
          remember (SCPolySemiDenotation _ _ _) as SCP.
          replace (SCPolySemiDenotation _ _ _) with SCP; auto.
          rewrite HeqSCP; clear ltu' HeqSCP SCP.
          rewrite unzipSeqLnthRight lnth_map.
          remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD; clear HeqDDD; simpl in DDD.
          move: DDD; rewrite projT1_eq_rect; simpl=> DDD.
          assert (ltj = DDD) as EE;[apply eq_irrelevance|destruct EE].
          remember (unzipSeq [seq SemiPolyConvert i | i <- uniBounds]).1.
          replace (unzipSeq [seq SemiPolyConvert i | i <- uniBounds]).1
             with [seq (SemiPolyConvert i).1 | i <- uniBounds] in Heql;[|by rewrite unzipSeqMapLeft].
          rewrite Heql; clear Heql l.
          change defaultBund with (SemiPolyConvert (E := E) UndefVS).1.
          rewrite (nth_map (f := fun x => (SemiPolyConvert x).1)).
          by rewrite (lnth_nth UndefVS); simpl.
          rewrite Hequ'; clear Hequ' u' ltu'.
          by destruct H00.
          rewrite Hequ'; clear Hequ' u' ltu'.
          rewrite eq_rect_ap_el; f_equal.
          by apply subset_eq; rewrite projT1_eq_rect.
      clear ltu.
      unfold PrenexFormulaCondition in H0.
      remember (H0 (exist _ u' H)) as H0'; clear HeqH0' H0; simpl in H0'; clear H.
      do 2 rewrite DenotToSemiDenotePolyF; simpl.
      rewrite SemiAdviceEta.
      replace (MakeU u' (fun=> 0%R)) with (MakeU u (fun=> 0%R)) in H0';[|
        rewrite Hequ'; clear H0' Hequ' u'; by destruct H00].
      clear Hequ' u' H00 H2 H1.
      by apply (Prenex_Semicircuit_Correct_Lem_1 (b := true)).
    + rewrite HeqPSP; clear HeqPSP PSP; simpl.
      unfold SCIndConditionU; simpl.
      move=> [x ltx] i u H; simpl in *.
      remember (SCIndConditionU_obligation_1 _ _ _) as DDD; clear HeqDDD; simpl in DDD.
      unfold SCInBoundU in H.
      rewrite (surjective_pairing (IndArgs _ _)).
      do 2 rewrite DenotToSemiDenotePolyU; simpl.
      rewrite SemiAdviceEta.
      transitivity (
        obind (fun b1 => obind (fun b2 => Some (indFun b1 b2))
            (SCPolySemiDenotation M
                ((nth defaultBund
                    [seq (SemiPolyConvert i).1 | i <- uniBounds] x).2 M A)
                (IndArgs
                  (nth defaultBund
                      [seq (SemiPolyConvert i).1 | i <- uniBounds] x).1.2 i).2
                u))
          (SCPolySemiDenotation M
            ((nth defaultBund [seq (SemiPolyConvert i).1 | i <- uniBounds]
                x).2 M A)
            (IndArgs
                (nth defaultBund
                  [seq (SemiPolyConvert i).1 | i <- uniBounds] x).1.2 i).1
            u)
      ).
      f_equal;[|by rewrite unzipSeqMapLeft].
      apply functional_extensionality=>b1; do 2 f_equal; by rewrite unzipSeqMapLeft.
      change defaultBund with (SemiPolyConvert (E := E) UndefVS).1.
      transitivity (
        IndCOut
          ((nth (SemiPolyConvert UndefVS).1
              [seq (SemiPolyConvert i).1 | i <- uniBounds] x).2 M A) i u
      );[|by rewrite unzipSeqMapLeft].
      rewrite (nth_map (f := fun x => (SemiPolyConvert x).1)).
      assert (x < length uniBounds) as ltx2;[clear H u i; by rewrite unzipSeqMapRight map_length in ltx|].
      replace (nth UndefVS uniBounds x) with (lnth uniBounds (exist _ x ltx2));[|by rewrite (lnth_nth UndefVS)].
      clear H0 H2.
      unfold PrenexUniversalCondition in H1; simpl in H1.
      remember (H1 u (exist _ x ltx2)) as H1'; clear HeqH1' H1; simpl in H1'.
      remember (Prenex.PrenexUniversalCondition_obligation_1 _ _ _ _ _) as DDY; clear HeqDDY; simpl in DDY.
      assert (forall j, InBound FSize M A (u (` j)) (lnth uniBounds (exist _ (` j) (DDY j))) u).
            move=>[j ltj].
            remember (H (exist _ j ltj)) as H'; clear HeqH' H; simpl in *.
            unfold InBound.
            rewrite DenotToSemiDenotePolyU SemiAdviceEta in H'; simpl in H'.
            remember (SCPolySemiDenotation _ _ _) as PVD.
            replace (PolyVSDenotation _ _ _ _) with PVD; auto.
            rewrite HeqPVD; clear H1' H' HeqPVD PVD; auto.
            remember (DDD _) as DD; clear HeqDD DDD; simpl in DD.
            move: DD;
            rewrite (unzipSeqMapLeft SemiPolyConvert)
                    (unzipSeqMapRight SemiPolyConvert)=> D.
            assert (j < length [seq (SemiPolyConvert i0).1 | i0 <- uniBounds]) as ltj3;[by do 2 rewrite map_length in D *|].
            replace (nth defaultBund [seq (SemiPolyConvert i0).1 | i0 <- uniBounds] j)
              with (lnth [seq (SemiPolyConvert i0).1 | i0 <- uniBounds] (exist _ j ltj3));[|
              by rewrite (lnth_nth defaultBund)].
            do 2 rewrite lnth_map; simpl.
            remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDT; clear HeqDDT; simpl in DDT.
            remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDR; clear HeqDDR; simpl in DDR.
            (* assert (ltx2 = DDT) as EET;[by apply eq_irrelevance|destruct EET]. *)
            assert (DDT = DDR) as EER;[by apply eq_irrelevance|destruct EER].
            rewrite <- SemiPolyConvert_Correct.
            by assert (DDT = DDY (exist _ j ltj)) as EER;[by apply eq_irrelevance|destruct EER].
      remember (H1' H0) as H1; clear HeqH1 H1' H.
      destruct H1 as [o H1].
      by rewrite (Prenex_Semicircuit_Correct_Lem_1_1 H1).
    + rewrite HeqPSP; clear HeqPSP PSP; simpl.
      unfold SCIndConditionE; simpl.
      move=> v [x ltx] i ins out; simpl in *=> H.
      rewrite (surjective_pairing (IndArgs _ _)).
      do 2 rewrite DenotToSemiDenotePolyE; simpl.
      rewrite SemiAdviceEta.
      remember (H2 v (exist _ x ltx) ins out H) as H2'; clear HeqH2' H0 H1 H2 H; simpl in H2'.
      unfold ExiConv.
      rewrite (surjective_pairing (exiBounds _)).
      rewrite (P6Eta (SemiConversionCombineTup _));
      rewrite <- P5Eta;
      rewrite (surjective_pairing (SemiPolyConvert _));
      simpl.
      destruct ((SemiConversionCombineTup
                  (fun x0 => SemiPolyConvert 
                  ((exiBounds (exist _ x ltx)).1 x0))).1.1.1.1.1 <= i) eqn:ilim.
      rewrite IndArgs_Comb_Right_1; auto; rewrite IndArgs_Comb_Right_2; auto; rewrite IndCOut_Comb_Right; auto.
      remember (SemiConversionCombineTup _) as S; clear HeqS.
      apply Prenex_Semicircuit_Correct_Lem_2_out in H2'.
      destruct H2' as [o H2].
      by rewrite (Prenex_Semicircuit_Correct_Lem_1_1 (o := o)).
      assert (i < (SemiConversionCombineTup (fun x0 => SemiPolyConvert ((exiBounds (exist _ x ltx)).1 x0))).1.1.1.1.1);[
        move: i ilim; elim: (SemiConversionCombineTup _).1.1.1.1.1; auto; destruct i; auto; apply H|].
      rewrite IndArgs_Comb_Left_1; auto. 
      rewrite IndArgs_Comb_Left_2; auto. 
      rewrite IndCOut_Comb_Left; auto.


      unfold FunBoundsVS in H2'.
      rewrite Prenex_Semicircuit_Correct_Lem_1_1.
      Check Prenex_Semicircuit_Correct_Lem_1_1.
      rewrite (Prenex_Semicircuit_Correct_Lem_1_1).
      unfold FunBoundsVS in H2'.

      apply Prenex_Semicircuit_Correct_Lem_1_1 in H1.
      rewrite Prenex_Semicircuit_Correct_Lem_1_0.
      rewrite lnth_map; simpl.
      replace (nth UndefVS uniBounds x) with (lnth uniBounds (exist _ x ltx2));[|by rewrite (lnth_nth UndefVS)].
      
      transitivity (
        SCPolySemiDenotation M
          ((nth defaultBund [seq (SemiPolyConvert i).1 | i <- uniBounds] x).2
            M A)
          (lnth [seq (SemiPolyConvert i).2 | i <- uniBounds]
            (exist
                (fun n : nat =>
                n < length (unzipSeq [seq SemiPolyConvert i | i <- uniBounds]).2) j
                (DDD (exist (fun n : nat => n < x) j ltj))))
      ).
      replace (unzipSeq [seq SemiPolyConvert i | i <- uniBounds]).1
             with [seq (SemiPolyConvert i).1 | i <- uniBounds];[|by rewrite unzipSeqMapLeft].
      replace (nth UndefVS uniBounds x) with (lnth uniBounds (exist _ x ltx2)) in H';[|by rewrite (lnth_nth UndefVS)].
      
      rewrite unzipSeqMapLeft in H'.
      rewrite SemiAdviceEta.
      rewrite (lnth_nth UndefVS); simpl.

      by rewrite unzipSeqMapLeft.
      assert ((unzipSeq [seq SemiPolyConvert i | i <- uniBounds]).1 =
              [seq (SemiPolyConvert i).1 | i <- uniBounds]
              );[by rewrite unzipSeqMapLeft|].
      destruct H3.
      assert ([seq (SemiPolyConvert i).1 | i <- uniBounds] =
              (unzipSeq [seq SemiPolyConvert i | i <- uniBounds]).1);[by rewrite unzipSeqMapLeft|].
      destruct H3.
      replace (unzipSeq [seq SemiPolyConvert i | i <- uniBounds]).1
        with [seq (SemiPolyConvert i).1 | i <- uniBounds];[|by rewrite unzipSeqMapLeft].
          
      rewrite unzipSeqMapLeft.
      fold SemiPolyConvert.



      unfold SCIndConditionU_obligation_1.
      rewrite (surjective_pairing (IndArgs _ _)).
      assert (length (unzipSeq [seq SemiPolyConvert i | i <- uniBounds]).2 = length uniBounds) as H00;[
              by rewrite unzipSeqLengthRight map_length|].
      remember (eq_rect _ (fun x => |[x]| -> _) u _ H00) as u'; simpl in u'.

      move: H0'.
      clear exiBounds.


      elim: formula.
      2:{
      rewrite Hequ' in H0'




      destruct (i < (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- uniBounds]).1.1.1.1.1) eqn:T1.
      rewrite CombineDenotationLeft.
      rewrite CombineDenotationLeft.
      remember (SemiConversionCombineData _ _) as s.
      unfold SemiConversionCombineData in Heqs.
      rewrite (P5Eta (SemiConversionCombineSeq _).1)
              (P5Eta (SemiPropConvert formula).1)
              SemiConversionDataMatch SemiConversionDataMatch in Heqs;
      simpl in Heqs.
      rewrite Heqs; clear Heqs s; simpl.
      unfold CombineGens; simpl.
      do 2 rewrite SemiAdviceMatch.
      simpl; rewrite T1.
      rewrite (surjective_pairing (IndArgs _ _)); simpl.
      rewrite T1.

      simpl.
      destruct (i < (SemiConversionCombineSeq _).1.1.1.1.1) eqn:T1.
      rewrite (surjective_pairing (IndArgs _ i)); simpl.
      rewrite IndCOut_SeqNone.


      simpl.


      destruct (length uniBounds < i) eqn:ibnd.
      simpl.


      unfold IndCOut.
      rewrite <- (SemiAdviceEta (A := (SemiConversionCombineData
      (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- uniBounds]).1
      (SemiPropConvert formula).1).2 M A)).


      rewrite SemiConversionDataEta.
      simpl.

      by destruct H00.

      remember (Utils.lnth_map_obligation_1 _ _ _ _ (exist _ j0 ltj2)) as EE1.
 
      replace (Utils.lnth_map_obligation_1 PolyTermVS
              (nat * (nat -> nat) * (nat -> nat) * SemiConversionData *
               SemiAdviceGenerator * SCPoly) [eta SemiPolyConvert] uniBounds
              (exist
                 (fun n : nat =>
                  n < length [seq SemiPolyConvert i | i <- uniBounds]) j0
                 ltj2)) with ltj;[|apply eq_irrelevance].


      remember (H1 (MakeU u v0)) as H1'; clear HeqH1' H1; simpl in H1'.

      apply subset_eq in Heqj0'; rewrite projT1_eq_rect in Heqj0'; simpl in Heqj0'; symmetry in Heqj0'; destruct Heqj0'.
      by destruct j0.
      replace x with (` j0).
      rewrite Heqj0'; clear Heqj0' j0'.
      destruct 
      rewrite 
      destruct (esym H00).
    rewrite Hequ'; clear Hequ' u'.
    clear HeqSCCS ExiArgs0 FreeArgs0 IndArgs0 H0 H1 H2.
    destruct H00.
    rewrite <- (SemiAdviceEta (A := (SemiPropConvert formula).1.1.2)) in ltu'.
    rewrite SemiAdviceEta in ltu'.
            (surjective_pairing ((SemiPropConvert formula).1.1))
            (surjective_pairing ((SemiPropConvert formula).1.1.1))
            (surjective_pairing ((SemiPropConvert formula).1.1.1)) in ltu'.
            (surjective_pairing (SemiPropConvert formula))
            (surjective_pairing (SemiConversionCombineSeq _).1)
            (surjective_pairing (SemiConversionCombineSeq _).1.1)
            (surjective_pairing (SemiConversionCombineSeq _).1.1.1)
            (surjective_pairing (SemiConversionCombineSeq _).1.1.1.1)
            (surjective_pairing (SemiConversionCombineData _ _))
            (surjective_pairing (SemiConversionCombineData _ _).1)
            (surjective_pairing (SemiConversionCombineData _ _).1.1)
            (surjective_pairing (SemiConversionCombineData _ _).1.1.1) in HeqPSP.
      Check (lnth n j0').


      simpl in ltu.
    destruct H00.
      apply H0.

      2:{ rewrite HeqSCP; clear HeqSCP SCP.
          remember ((SemiConversionCombineData SCCS.1 (SemiPropConvert formula).1).2 M A) as GG.
          clear HeqGG HeqPCL ltu u HeqSCCS SCCS H2 H1 H0 formula uniBounds.




          elim PCL.
          unfold SCPropSemiDenotation.
          simpl.
      rewrite <- (CombineDenotationPropRight (k := (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- uniBounds]).1.1.1.1.1)
                                             (j := (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- uniBounds]).1.1.1.1.2)
                                             (i := (SemiConversionCombineSeq [seq SemiPolyConvert i | i <- uniBounds]).1.1.1.2)
                                             

Theorem CombineDenotationPropRight {E k j i f h Y D M A} :
  SCPropSemiDenotation M
    ((SemiConversionCombineData (E := E) (k, j, i, f, h) D).2 M A)
    (PropCallLift k j i Y) =
  SCPropSemiDenotation (E := E) M (D.2 M A) Y.

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

