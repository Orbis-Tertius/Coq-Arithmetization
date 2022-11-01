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
Inductive SCPoly : Type :=
| PolyConsZero : SCPoly
| PolyConsPlusOne : SCPoly
| PolyConsMinusOne : SCPoly
| PolyConsPlus : SCPoly -> SCPoly -> SCPoly
| PolyConsTimes : SCPoly -> SCPoly -> SCPoly
| PolyConsInd : nat -> SCPoly
| PolyConsFreeV : nat -> SCPoly
| PolyConsUniV : nat -> SCPoly
| PolyConsFreeF : nat -> nat -> SCPoly
| PolyConsExiF : nat -> nat -> SCPoly.

(* <S> in the paper *)
Inductive SCProp  : Type :=
| ZOConsNot : SCProp -> SCProp
| ZOConsAnd : SCProp -> SCProp -> SCProp
| ZOConsOr : SCProp -> SCProp -> SCProp
| ZOConsImp : SCProp -> SCProp -> SCProp
| ZOConsEq : SCPoly -> SCPoly -> SCProp.

Record SemiCircuit {E} : Type :=
  mkSemiCircuit {
    (* Ctx : @SemicircuitCtx ctx;
    freeFCalls := freeFC Ctx; (* r in paper *)
    exiFCalls := exiFC Ctx; (* q in paper *)
    indCalls := indC Ctx;  *)
    (* nu : {s : |[exiV ctx]| -> { m : nat | m <= uniV ctx } | forall i j : |[exiV ctx]|, (` i) <= (` j) -> (` (s j)) <= (` (s i))}; *)
    indArgs : nat -> seq (SCPoly * SCPoly);
    (* w in paper *)
    freeFArgs : nat -> forall i a : nat, seq (|[a]| -> SCPoly);
    (* omega in paper *)
    exiArgs : nat -> forall i, seq (|[lnth E i]| -> SCPoly);
    (* V in paper *)
    uniVBounds : seq SCPoly;
    (* S, G and B in paper *)
    exiFBounds : forall i, (|[lnth E i]| -> SCPoly) * SCPoly;
    formula : SCProp
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
    (* o in paper *)
    (*Arguments are: which bound, which function, which call*)
    freeFCallOut : nat -> nat -> nat -> (nat -> 'F_FSize) -> option 'F_FSize;
    (* sigma in paper *)
    (*Arguments are: which bound, which function, which call*)
    exiCallOut : nat -> nat -> nat -> (nat -> 'F_FSize) -> option 'F_FSize;
    (*Arguments are: which bound, which call*)
    indCallOut : nat -> nat -> (nat -> 'F_FSize) -> option 'F_FSize;
  }.

Fixpoint SCPolyDenotation {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  (p : SCPoly) :
  nat -> (nat -> 'F_FSize) -> option 'F_FSize :=
  match p with
  | PolyConsZero => fun _ _ => Some 0%R
  | PolyConsPlusOne => fun _ _ => Some 1%R
  | PolyConsMinusOne => fun _ _ => Some (-1)%R
  | PolyConsPlus p1 p2 => fun x u =>
    let r1 := SCPolyDenotation adv p1 x u in
    let r2 := SCPolyDenotation adv p2 x u in 
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) r2) r1
  | PolyConsTimes p1 p2 => fun x u =>
    let r1 := SCPolyDenotation adv p1 x u in
    let r2 := SCPolyDenotation adv p2 x u in 
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) r2) r1
  | PolyConsInd i => fun x => indCallOut adv x i
  | PolyConsFreeV i => fun _ _ => Some (V_F _ M i)
  | PolyConsUniV i => fun _ u => Some (u i)
  | PolyConsFreeF i j => fun x => freeFCallOut adv x i j
  | PolyConsExiF i j => fun x => exiCallOut adv x i j
  end.

Program Fixpoint SCPropDenotation {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  (p : SCProp) :
  nat -> (nat -> 'F_FSize) -> option bool :=
  match p with
  | ZOConsNot p => fun x u => 
    let r := SCPropDenotation adv p x u in
    obind (fun r1 => Some (negb r)) r
  | ZOConsAnd p1 p2 => fun x u => 
    let r1 := SCPropDenotation adv p1 x u in
    let r2 := SCPropDenotation adv p2 x u in
    obind (fun r1 => obind (fun r2 => Some (r1 && r2)) r2) r1
  | ZOConsOr p1 p2 => fun x u => 
    let r1 := SCPropDenotation adv p1 x u in
    let r2 := SCPropDenotation adv p2 x u in
    obind (fun r1 => obind (fun r2 => Some (r1 || r2)) r2) r1
  | ZOConsImp p1 p2 => fun x u => 
    let r1 := SCPropDenotation adv p1 x u in
    let r2 := SCPropDenotation adv p2 x u in
    obind (fun r1 => obind (fun r2 => Some (r1 ==> r2)) r2) r1
  | ZOConsEq p1 p2 => fun x u => 
    let r1 := SCPolyDenotation adv p1 x u in
    let r2 := SCPolyDenotation adv p2 x u in
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


Definition SCInBound {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M)
  (r : 'F_FSize)
  (b : SCPoly) 
  (x : nat) (t : nat -> 'F_FSize) : bool :=
  match SCPolyDenotation adv b x t with
  | None => false
  | Some e => r < e
  end.

(*A collection of universal variables within *)
Program Definition SCU {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (f : @SemiCircuit E) : Type 
  := { u : |[length (uniVBounds f)]| -> 'F_FSize | 
       forall j : |[length (uniVBounds f)]|,
       forall v : nat -> 'F_FSize, 
       SCInBound adv (u j) (lnth (uniVBounds f) j) 0 (MakeU u v)
    }.

Program Definition SCFormulaCondition {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (f : SemiCircuit) : Prop :=
  forall (u : SCU adv f), 
  SCPropDenotation adv (formula f) 0 (MakeU u (fun _ => 0%R)) == Some true.

Program Definition SCB {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (f : @SemiCircuit E) (x : |[length E]|) : Type 
  := { u : |[lnth E x]| -> 'F_FSize | 
       forall j : |[lnth E x]|,
       forall v : nat -> 'F_FSize, 
       SCInBound adv (u j) ((exiFBounds f x).1 j) x (MakeU u v)
    }.

Program Definition SCIndCondition0 {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall u : SCU adv c, forall i : nat,
  let (a1, a2) := nth (PolyConsZero, PolyConsZero) (indArgs c 0) i in
  let b1 : option 'F_FSize := SCPolyDenotation adv a1 0 (MakeU u v) in
  let b2 : option 'F_FSize := SCPolyDenotation adv a2 0 (MakeU u v) in
  obind (fun b1 => obind (fun b2 => Some (indFun b1 b2)) b2) b1
  = indCallOut adv i 0 (MakeU u v).

Program Definition SCIndConditionS {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall x : |[length E]|, forall u : SCB adv c x, forall i : nat,
  let (a1, a2) := nth (PolyConsZero, PolyConsZero) (indArgs c x) i in
  let b1 : option 'F_FSize := SCPolyDenotation adv a1 x.+1 (MakeU u v) in
  let b2 : option 'F_FSize := SCPolyDenotation adv a2 x.+1 (MakeU u v) in
  obind (fun b1 => obind (fun b2 => Some (indFun b1 b2)) b2) b1
  = indCallOut adv x.+1 i (MakeU u v).

Program Definition SCExiFCondition0 {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall u : SCU adv c, forall i j,
  let t (a : |[lnth E i]|) : option 'F_FSize
      := SCPolyDenotation adv (nth (fun _ => PolyConsZero) (exiArgs c 0 i) j a) 0 (MakeU u v) in
  obind (fun t => exiAdv adv i t) (option_fun t)  
  = exiCallOut adv 0 i j (MakeU u v).

Program Definition SCExiFConditionS {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall x : |[length E]|, forall u : SCB adv c x, forall i j,
  let t (a : |[lnth E i]|) : option 'F_FSize
      := SCPolyDenotation adv (nth (fun _ => PolyConsZero) (exiArgs c x.+1 i) j a) x.+1 (MakeU u v) in
  obind (fun t => exiAdv adv i t) (option_fun t)  
  = exiCallOut adv x.+1 i j (MakeU u v).

Program Definition SCFreeFCondition0 {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall u : SCU adv c, forall i j,
  let t a : option 'F_FSize
      := SCPolyDenotation adv (nth (fun _ => PolyConsZero) (freeFArgs c 0 i (projT1 (F_S _ M i))) j a) 0 (MakeU u v) in
  obind (fun t => projT2 (F_S _ M i) t) (option_fun t)
  = freeFCallOut adv 0 i j (MakeU u v).

Program Definition SCFreeFConditionS {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : SemiCircuit) : Prop :=
  forall v : nat -> 'F_FSize, forall x : |[length E]|, forall u : SCB adv c x, forall i j,
  let t a : option 'F_FSize
      := SCPolyDenotation adv (nth (fun _ => PolyConsZero) (freeFArgs c x.+1 i (projT1 (F_S _ M i))) j a) x.+1 (MakeU u v) in
  obind (fun t => projT2 (F_S _ M i) t) (option_fun t)
  = freeFCallOut adv x.+1 i j (MakeU u v).

Program Definition SCUniversalCondition {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : @SemiCircuit E) : Prop :=
  forall (u : nat -> 'F_FSize) (i : |[length (uniVBounds c)]|),
    (forall j : |[i]|, SCInBound adv (u j) (lnth (uniVBounds c) j) 0 u) ->
    exists o, SCPolyDenotation adv (lnth (uniVBounds c) i) 0 u = Some o.
Next Obligation. strivial use: ltn_trans. Qed.

Program Fixpoint SCFunBounds {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) {a}
  (ins : |[a]| -> 'F_FSize) (out : 'F_FSize)
  (insB : |[a]| -> SCPoly) (outB : SCPoly) (x : |[length E]|) :
  (nat -> 'F_FSize) -> bool := fun u =>
  match a with
  | 0 => SCInBound adv out outB x u
  | n.+1 => SCInBound adv (ins 0) (insB 0) x u &&
    @SCFunBounds E M adv n (fun x => ins (x.+1)) out (fun x => insB (x.+1)) outB x u
  end.

Definition SCExiBoundCondition {E} {M : @Sigma11Model FSize}
  (adv : @SCAdvice E M) (c : SemiCircuit) : Prop :=
  forall u : nat -> 'F_FSize, forall i : |[length E]|,
  forall (ins : |[lnth E i]| -> 'F_FSize) (out : 'F_FSize),
  exiAdv adv i ins == Some out -> 
  SCFunBounds adv ins out 
    (fun x => (exiFBounds c i).1 x)
    (exiFBounds c i).2 i (MakeU ins u) == true.

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
