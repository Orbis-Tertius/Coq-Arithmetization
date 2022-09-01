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

Notation "|[ v ]|" := {n : nat | n < v} : type_scope.

Inductive SemicircuitPolyConstraint (* <P> in the paper *)
  {freeV exiV uniV freeF exiF : nat} 
  {freeFA : (|[freeF]| -> nat)} 
  {exiFA : (|[exiF]| -> nat)} : Type :=
| RingConsZero : SemicircuitPolyConstraint
| RingConsPlusOne : SemicircuitPolyConstraint
| RingConsMinusOne : SemicircuitPolyConstraint
| RingConsPlus : SemicircuitPolyConstraint -> SemicircuitPolyConstraint -> SemicircuitPolyConstraint
| RingConsTimes : SemicircuitPolyConstraint -> SemicircuitPolyConstraint -> SemicircuitPolyConstraint
| RingConsInd : SemicircuitPolyConstraint -> SemicircuitPolyConstraint -> SemicircuitPolyConstraint
| RingConsFreeV : |[freeV]| -> SemicircuitPolyConstraint
| RingConsExiV : |[exiV]| -> SemicircuitPolyConstraint
| RingConsUniV : |[uniV]| -> SemicircuitPolyConstraint
| RingConsFreeF : forall x : |[freeF]|, |[freeFA x]| -> SemicircuitPolyConstraint
| RingConsUniF : forall x : |[exiF]|, |[exiFA x]| -> SemicircuitPolyConstraint.

Inductive SemicircuitPropConstraint (* <S> in the paper *)
  {freeV exiV uniV freeF exiF : nat} 
  {freeFA : (|[freeF]| -> nat)} 
  {exiFA : (|[exiF]| -> nat)} : Type :=
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
| ZOConsEq : @SemicircuitPolyConstraint freeV exiV uniV freeF exiF freeFA exiFA
          -> @SemicircuitPolyConstraint freeV exiV uniV freeF exiF freeFA exiFA
          -> SemicircuitPropConstraint.

Record SemiCircuit : Type :=
  mkSemiCircuit {
    freeVN : nat; (* n in paper *)
    freeFN : nat; (* Number of free functions *)
    freeFunArity : |[freeFN]| -> nat; (* a in paper *)
    exiVN : nat; (* m in paper *)
    exiFN : nat; (* Number of SO existential functions *)
    exiFArity : |[exiFN]| -> nat; (* b in paper *)
    uniVN : nat; (* u in paper *)
    nu : {s : |[exiVN]| -> nat | forall i j : |[exiVN]|, (` i) <= (` j) -> s i <= s j};
    freeFunCalls : |[freeFN]| -> nat; (* r in paper *)
    exiFCalls : |[exiFN]| -> nat; (* q in paper *)
    polyConstraints : seq (@SemicircuitPolyConstraint freeVN exiVN uniVN freeFN exiFN freeFunCalls exiFCalls);
    (* w in paper *)
    freeFunArgs : forall (i : |[freeFN]|), |[freeFunCalls i]| -> |[freeFunArity i]| -> |[length polyConstraints]|;
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
    formula : unit + @SemicircuitPropConstraint freeVN exiVN uniVN freeFN exiFN freeFunCalls exiFCalls
  }.

Record SemiCircuitInstance (c : SemiCircuit) (M : Sigma11Model) : Type :=
  mkSemiCircuitInstance { 
    freeVInst : |[freeVN c]| -> R M;
    freeFInst : forall i : |[freeFN c]|, (|[freeFunArity c i]| -> R M) -> option (R M);
  }.

Record SemiCircuitAdvice (c : SemiCircuit) (M : Sigma11Model) : Type :=
  mkSemiCircuitAdvice { 
    exiFInst : forall i : |[exiFN c]|, (|[exiFArity c i]| -> R M) -> option (R M);
    (* s in paper *)
    exiVInst : |[exiVN c]| -> (|[uniVN c]| -> R M) -> R M;
    (* o in paper *)
    freeFCallOut : forall i : |[freeFN c]|, |[freeFunCalls c i]| -> (|[uniVN c]| -> R M) -> R M;
    (* sigma in paper *)
    exiFCallOut : forall i : |[exiFN c]|, |[exiFCalls c i]| -> (|[uniVN c]| -> R M) -> R M;
  }.

Definition indFun (M : Sigma11Model) (x y : R M) : R M := if lt_dec M x y then 1%R else 0%R.

Fixpoint SemicircuitPolyDenotation
  (c : SemiCircuit) (M : Sigma11Model)
  (inst : SemiCircuitInstance c M)
  (adv : SemiCircuitAdvice c M)
  (p : @SemicircuitPolyConstraint (freeVN c) (exiVN c) (uniVN c) (freeFN c) (exiFN c) (freeFunCalls c) (exiFCalls c)) :
  (|[uniVN c]| -> R M) -> R M :=
  match p with
  | RingConsZero => fun _ => 0%R
  | RingConsPlusOne => fun _ => 1%R
  | RingConsMinusOne => fun _ => (-1)%R
  | RingConsPlus p1 p2 => fun u =>
    let r1 := SemicircuitPolyDenotation c M inst adv p1 u in
    let r2 := SemicircuitPolyDenotation c M inst adv p2 u in 
    (r1 + r2)%R
  | RingConsTimes p1 p2 => fun u =>
    let r1 := SemicircuitPolyDenotation c M inst adv p1 u in
    let r2 := SemicircuitPolyDenotation c M inst adv p2 u in 
    (r1 * r2)%R
  | RingConsInd p1 p2 => fun u => 
    let r1 := SemicircuitPolyDenotation c M inst adv p1 u in
    let r2 := SemicircuitPolyDenotation c M inst adv p2 u in
    indFun M r1 r2
  | RingConsFreeV i => fun _ => freeVInst _ _ inst i
  | RingConsExiV i => exiVInst _ _ adv i
  | RingConsUniV i => fun u => u i
  | RingConsFreeF i j => freeFCallOut _ _ adv i j
  | RingConsUniF i j => exiFCallOut _ _ adv i j
  end.

Program Fixpoint SemicircuitPropDenotation
  (c : SemiCircuit) (M : Sigma11Model)
  (inst : SemiCircuitInstance c M)
  (adv : SemiCircuitAdvice c M)
  (p : @SemicircuitPropConstraint (freeVN c) (exiVN c) (uniVN c) (freeFN c) (exiFN c) (freeFunCalls c) (exiFCalls c)) :
  (|[uniVN c]| -> R M) -> Prop :=
  match p with
  | ZOConsNot p => fun u => 
    let r := SemicircuitPropDenotation c M inst adv p u in
    not r
  | ZOConsAnd p1 p2 => fun u => 
    let r1 := SemicircuitPropDenotation c M inst adv p1 u in
    let r2 := SemicircuitPropDenotation c M inst adv p2 u in
    r1 /\ r2
  | ZOConsOr p1 p2 => fun u => 
    let r1 := SemicircuitPropDenotation c M inst adv p1 u in
    let r2 := SemicircuitPropDenotation c M inst adv p2 u in
    r1 \/ r2
  | ZOConsImp p1 p2 => fun u => 
    let r1 := SemicircuitPropDenotation c M inst adv p1 u in
    let r2 := SemicircuitPropDenotation c M inst adv p2 u in
    r1 -> r2
  | ZOConsEq p1 p2 => fun u => 
    let r1 := SemicircuitPolyDenotation c M inst adv p1 u in
    let r2 := SemicircuitPolyDenotation c M inst adv p2 u in
    r1 = r2
  end.

Definition UProp {c : SemiCircuit} {M : Sigma11Model}
                 (inst : SemiCircuitInstance c M) (adv : SemiCircuitAdvice c M) 
                 (t : |[uniVN c]| -> R M) : Prop :=
  let ev i := SemicircuitPolyDenotation c M inst adv (lnth (polyConstraints c) (uniVBounds c i)) in
  forall i, lt M (t i) (ev i t).

Definition U {c : SemiCircuit} {M : Sigma11Model}
             (inst : SemiCircuitInstance c M) (adv : SemiCircuitAdvice c M) : Type 
  := { t : |[uniVN c]| -> R M | UProp inst adv t }.

Definition SemiCircuitFormulaCondition
  (c : SemiCircuit) (M : Sigma11Model)
  (inst : SemiCircuitInstance c M)
  (adv : SemiCircuitAdvice c M) : Prop :=
  exists p, formula c = inr p /\ forall u, SemicircuitPropDenotation c M inst adv p u = true.

Definition SemiCircuitFreeFunCondition
  (c : SemiCircuit) (M : Sigma11Model)
  (inst : SemiCircuitInstance c M)
  (adv : SemiCircuitAdvice c M) : Prop :=
  forall u : U inst adv, forall i : |[freeFN c]|, forall j : |[freeFunCalls c i]|,
  let t (a : |[freeFunArity c i]|) : R M
      := SemicircuitPolyDenotation c M inst adv (lnth (polyConstraints c) (freeFunArgs c i j a)) (` u) in
  freeFInst _ _ inst i t = Some (freeFCallOut c M adv i j (` u)).

Definition SemiCircuitexiFCondition
  (c : SemiCircuit) (M : Sigma11Model)
  (inst : SemiCircuitInstance c M)
  (adv : SemiCircuitAdvice c M) : Prop :=
  forall u : U inst adv, forall i : |[exiFN c]|, forall j : |[exiFCalls c i]|,
  let t (a : |[exiFArity c i]|) : R M
      := SemicircuitPolyDenotation c M inst adv (lnth (polyConstraints c) (exiFArgs c i j a)) (` u) in
  exiFInst _ _ adv i t = Some (exiFCallOut c M adv i j (` u)).

Definition SemiCircuitFOBoundCondition
  (c : SemiCircuit) (M : Sigma11Model)
  (inst : SemiCircuitInstance c M)
  (adv : SemiCircuitAdvice c M) : Prop :=
  forall u : U inst adv, forall i : |[exiVN c]|,
  let B := SemicircuitPolyDenotation c M inst adv (lnth (polyConstraints c) (exiVBounds c i)) (` u) in
  lt M (exiVInst _ _ adv i (` u)) B.

(* Note: This covers both conditions 5 and 6 in the paper *)
Definition SemiCircuitSOBoundCondition
  (c : SemiCircuit) (M : Sigma11Model)
  (inst : SemiCircuitInstance c M)
  (adv : SemiCircuitAdvice c M) : Prop :=
  forall u : U inst adv, forall i : |[exiFN c]|,
  let B := SemicircuitPolyDenotation c M inst adv (lnth (polyConstraints c) (exiFOutputBounds c i)) (` u) in
  let G (j : |[exiFArity c i]|) := SemicircuitPolyDenotation c M inst adv (lnth (polyConstraints c) (exiFInputBounds c i j)) (` u) in
  forall (t : |[exiFArity c i]| -> R M) (out : R M),
  exiFInst _ _ adv i t = Some out ->
  (forall x, lt M (t x) (G x)) /\ lt M out B.

Program Fixpoint TupConcat {T} {a b} (m : |[a]| -> T) (n : |[b]| -> T) (i : |[a + b]|) : T :=
  (if i < a as b return i < a = b -> T
   then fun _ => m i
   else fun _ => n (i - a)
  ) (erefl _).
Next Obligation.
  assert (a <= i); [hecrush use: notF, contraFltn|hauto use: ltn_subLR ].
Qed.

Ltac SemiCircuitExiStratConditionScript c i H0 Heqa :=
  remember ((` (nu c)) (exist (fun n : nat => n < exiVN c) i H0)) as a; clear Heqa;
  remember (uniVN c) as b; clear H0;
  destruct (a < b) eqn:ltba;[
    assert (a < b);[sfirstorder|hauto use: ltnW, subnKC]
  | assert (b <= a);[hecrush use: notF, contraFltn|hauto use: leq_trans, ltn_addr]].

Program Definition SemiCircuitExiStratCondition
  (c : SemiCircuit) (M : Sigma11Model)
  (inst : SemiCircuitInstance c M)
  (adv : SemiCircuitAdvice c M) : Prop :=
  forall i : |[exiVN c]|, forall m : |[nu c i]| -> R M,
  forall n1 n2 : |[uniVN c - nu c i]| -> R M,
  forall H1 : UProp inst adv (TupConcat m n1),
  forall H2 : UProp inst adv (TupConcat m n2),
  exiVInst _ _ adv i (TupConcat m n1) = exiVInst _ _ adv i (TupConcat m n2).
Next Obligation. SemiCircuitExiStratConditionScript c i H0 Heqa. Qed.
Next Obligation. clear H1; SemiCircuitExiStratConditionScript c i H0 Heqa. Qed.
Next Obligation. clear H2 H1; SemiCircuitExiStratConditionScript c i H0 Heqa. Qed.
Next Obligation. clear H2 H1; SemiCircuitExiStratConditionScript c i H0 Heqa. Qed.

Definition SemiCircuitDenotation 
  (c : SemiCircuit) (M : Sigma11Model) (i : SemiCircuitInstance c M) : Prop :=
  exists (a : SemiCircuitAdvice c M),
    SemiCircuitFormulaCondition c M i a /\
    SemiCircuitFreeFunCondition c M i a /\
    SemiCircuitexiFCondition c M i a /\
    SemiCircuitFOBoundCondition c M i a /\
    SemiCircuitSOBoundCondition c M i a /\
    SemiCircuitExiStratCondition c M i a.

End SemicircuitDef.

Section SemicircuitTranslation.



End SemicircuitTranslation.
