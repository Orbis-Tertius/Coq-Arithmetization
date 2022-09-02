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

Inductive SemicircuitPolyConstraint (* <P> in the paper *)
  {freeV exiV uniV freeF exiF : nat} 
  {freeFA : (|[freeF]| -> nat)} 
  {exiFA : (|[exiF]| -> nat)} : Type :=
| PolyConsZero : SemicircuitPolyConstraint
| PolyConsPlusOne : SemicircuitPolyConstraint
| PolyConsMinusOne : SemicircuitPolyConstraint
| PolyConsPlus : SemicircuitPolyConstraint -> SemicircuitPolyConstraint -> SemicircuitPolyConstraint
| PolyConsTimes : SemicircuitPolyConstraint -> SemicircuitPolyConstraint -> SemicircuitPolyConstraint
| PolyConsInd : SemicircuitPolyConstraint -> SemicircuitPolyConstraint -> SemicircuitPolyConstraint
| PolyConsFreeV : |[freeV]| -> SemicircuitPolyConstraint
| PolyConsExiV : |[exiV]| -> SemicircuitPolyConstraint
| PolyConsUniV : |[uniV]| -> SemicircuitPolyConstraint
| PolyConsFreeF : forall x : |[freeF]|, |[freeFA x]| -> SemicircuitPolyConstraint
| PolyConsExiF : forall x : |[exiF]|, |[exiFA x]| -> SemicircuitPolyConstraint.

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
    freeFArity : |[freeFN]| -> nat; (* a in paper *)
    exiVN : nat; (* m in paper *)
    exiFN : nat; (* Number of SO existential functions *)
    exiFArity : |[exiFN]| -> nat; (* b in paper *)
    uniVN : nat; (* u in paper *)
    nu : {s : |[exiVN]| -> nat | forall i j : |[exiVN]|, (` i) <= (` j) -> s i <= s j};
    freeFCalls : |[freeFN]| -> nat; (* r in paper *)
    exiFCalls : |[exiFN]| -> nat; (* q in paper *)
    polyConstraints : seq (@SemicircuitPolyConstraint freeVN exiVN uniVN freeFN exiFN freeFCalls exiFCalls);
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
    formula : unit + @SemicircuitPropConstraint freeVN exiVN uniVN freeFN exiFN freeFCalls exiFCalls
  }.

Record SemiCircuitInstance (M : Sigma11Model) (c : SemiCircuit) : Type :=
  mkSemiCircuitInstance { 
    freeVInst : |[freeVN c]| -> R M;
    freeFInst : forall i : |[freeFN c]|, (|[freeFArity c i]| -> R M) -> option (R M);
  }.

Record SemiCircuitAdvice (M : Sigma11Model) (c : SemiCircuit) : Type :=
  mkSemiCircuitAdvice { 
    exiFInst : forall i : |[exiFN c]|, (|[exiFArity c i]| -> R M) -> option (R M);
    (* s in paper *)
    exiVInst : |[exiVN c]| -> (|[uniVN c]| -> R M) -> R M;
    (* o in paper *)
    freeFCallOut : forall i : |[freeFN c]|, |[freeFCalls c i]| -> (|[uniVN c]| -> R M) -> R M;
    (* sigma in paper *)
    exiFCallOut : forall i : |[exiFN c]|, |[exiFCalls c i]| -> (|[uniVN c]| -> R M) -> R M;
  }.

Definition indFun (M : Sigma11Model) (x y : R M) : R M := if lt_dec M x y then 1%R else 0%R.

Fixpoint SemicircuitPolyDenotation
  (M : Sigma11Model) (c : SemiCircuit)
  (inst : SemiCircuitInstance M c)
  (adv : SemiCircuitAdvice M c)
  (p : @SemicircuitPolyConstraint (freeVN c) (exiVN c) (uniVN c) (freeFN c) (exiFN c) (freeFCalls c) (exiFCalls c)) :
  (|[uniVN c]| -> R M) -> R M :=
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
  (M : Sigma11Model) (c : SemiCircuit)
  (inst : SemiCircuitInstance M c)
  (adv : SemiCircuitAdvice M c)
  (p : @SemicircuitPropConstraint (freeVN c) (exiVN c) (uniVN c) (freeFN c) (exiFN c) (freeFCalls c) (exiFCalls c)) :
  (|[uniVN c]| -> R M) -> Prop :=
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

Definition UProp {c : SemiCircuit} {M : Sigma11Model}
                 (inst : SemiCircuitInstance M c) (adv : SemiCircuitAdvice M c) 
                 (t : |[uniVN c]| -> R M) : Prop :=
  let ev i := SemicircuitPolyDenotation M c inst adv (lnth (polyConstraints c) (uniVBounds c i)) in
  forall i, lt M (t i) (ev i t).

Definition U {c : SemiCircuit} {M : Sigma11Model}
             (inst : SemiCircuitInstance M c) (adv : SemiCircuitAdvice M c) : Type 
  := { t : |[uniVN c]| -> R M | UProp inst adv t }.

Definition SemiCircuitFormulaCondition
  (M : Sigma11Model) (c : SemiCircuit)
  (inst : SemiCircuitInstance M c)
  (adv : SemiCircuitAdvice M c) : Prop :=
  exists p, formula c = inr p /\ forall u, SemicircuitPropDenotation M c inst adv p u = true.

Definition SemiCircuitFreeFunCondition
  (M : Sigma11Model) (c : SemiCircuit)
  (inst : SemiCircuitInstance M c)
  (adv : SemiCircuitAdvice M c) : Prop :=
  forall u : U inst adv, forall i : |[freeFN c]|, forall j : |[freeFCalls c i]|,
  let t (a : |[freeFArity c i]|) : R M
      := SemicircuitPolyDenotation M c inst adv (lnth (polyConstraints c) (freeFArgs c i j a)) (` u) in
  freeFInst _ _ inst i t = Some (freeFCallOut M c adv i j (` u)).

Definition SemiCircuitexiFCondition
  (M : Sigma11Model) (c : SemiCircuit)
  (inst : SemiCircuitInstance M c)
  (adv : SemiCircuitAdvice M c) : Prop :=
  forall u : U inst adv, forall i : |[exiFN c]|, forall j : |[exiFCalls c i]|,
  let t (a : |[exiFArity c i]|) : R M
      := SemicircuitPolyDenotation M c inst adv (lnth (polyConstraints c) (exiFArgs c i j a)) (` u) in
  exiFInst _ _ adv i t = Some (exiFCallOut M c adv i j (` u)).

Definition SemiCircuitFOBoundCondition
  (M : Sigma11Model) (c : SemiCircuit)
  (inst : SemiCircuitInstance M c)
  (adv : SemiCircuitAdvice M c) : Prop :=
  forall u : U inst adv, forall i : |[exiVN c]|,
  let B := SemicircuitPolyDenotation M c inst adv (lnth (polyConstraints c) (exiVBounds c i)) (` u) in
  lt M (exiVInst _ _ adv i (` u)) B.

(* Note: This covers both conditions 5 and 6 in the paper *)
Definition SemiCircuitSOBoundCondition
  (M : Sigma11Model) (c : SemiCircuit)
  (inst : SemiCircuitInstance M c)
  (adv : SemiCircuitAdvice M c) : Prop :=
  forall u : U inst adv, forall i : |[exiFN c]|,
  let B := SemicircuitPolyDenotation M c inst adv (lnth (polyConstraints c) (exiFOutputBounds c i)) (` u) in
  let G (j : |[exiFArity c i]|) := SemicircuitPolyDenotation M c inst adv (lnth (polyConstraints c) (exiFInputBounds c i j)) (` u) in
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
  (M : Sigma11Model) (c : SemiCircuit)
  (inst : SemiCircuitInstance M c)
  (adv : SemiCircuitAdvice M c) : Prop :=
  forall i : |[exiVN c]|, forall m : |[nu c i]| -> R M,
  forall n1 n2 : |[uniVN c - nu c i]| -> R M,
  forall H1 : UProp inst adv (TupConcat m n1),
  forall H2 : UProp inst adv (TupConcat m n2),
  exiVInst _ _ adv i (TupConcat m n1) = exiVInst _ _ adv i (TupConcat m n2).
Next Obligation. SemiCircuitExiStratConditionScript c i H0 Heqa. Qed.
Next Obligation. clear H1; SemiCircuitExiStratConditionScript c i H0 Heqa. Qed.
Next Obligation. clear H2 H1; SemiCircuitExiStratConditionScript c i H0 Heqa. Qed.
Next Obligation. clear H2 H1; SemiCircuitExiStratConditionScript c i H0 Heqa. Qed.

Definition SemiCircuitDenotation (M : Sigma11Model)
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

(*Extend exi functions with new one with no calls*)
Program Fixpoint SemicircuitPolyConstraint_ExiFunExtend_1
    (freeVN freeFN exiVN exiFN uniVN : nat)
    (freeFArity : |[freeFN]| -> nat)
    (exiFArity : |[exiFN]| -> nat)
    (freeFCalls : |[freeFN]| -> nat)
    (exiFCalls : |[exiFN]| -> nat)
    (p : @SemicircuitPolyConstraint freeVN exiVN uniVN freeFN exiFN freeFCalls exiFCalls) :
    @SemicircuitPolyConstraint freeVN exiVN uniVN freeFN (exiFN.+1) freeFCalls (fseqSnoc 0 exiFCalls) := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := SemicircuitPolyConstraint_ExiFunExtend_1 _ _ _ _ uniVN freeFArity exiFArity freeFCalls exiFCalls p1 in
    let r2 := SemicircuitPolyConstraint_ExiFunExtend_1 _ _ _ _ uniVN freeFArity exiFArity freeFCalls exiFCalls p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := SemicircuitPolyConstraint_ExiFunExtend_1 _ _ _ _ uniVN freeFArity exiFArity freeFCalls exiFCalls p1 in
    let r2 := SemicircuitPolyConstraint_ExiFunExtend_1 _ _ _ _ uniVN freeFArity exiFArity freeFCalls exiFCalls p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd p1 p2 =>
    let r1 := SemicircuitPolyConstraint_ExiFunExtend_1 _ _ _ _ uniVN freeFArity exiFArity freeFCalls exiFCalls p1 in
    let r2 := SemicircuitPolyConstraint_ExiFunExtend_1 _ _ _ _ uniVN freeFArity exiFArity freeFCalls exiFCalls p2 in 
    PolyConsInd r1 r2
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsExiV i => PolyConsExiV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF i j
  end.
Next Obligation. by unfold fseqSnoc; rewrite dep_if_case_true. Qed.

(*Extend exi functions with new one with no calls*)
Fixpoint SemicircuitPropConstraint_ExiFunExtend_1
    (freeVN freeFN exiVN exiFN uniVN : nat)
    (freeFArity : |[freeFN]| -> nat)
    (exiFArity : |[exiFN]| -> nat)
    (freeFCalls : |[freeFN]| -> nat)
    (exiFCalls : |[exiFN]| -> nat)
    (p : @SemicircuitPropConstraint freeVN exiVN uniVN freeFN exiFN freeFCalls exiFCalls) :
    @SemicircuitPropConstraint freeVN exiVN uniVN freeFN (exiFN.+1) freeFCalls (fseqSnoc 0 exiFCalls) := 
  match p with
  | ZOConsNot p =>
    let r := SemicircuitPropConstraint_ExiFunExtend_1 _ _ _ _ uniVN freeFArity exiFArity freeFCalls exiFCalls p in
    ZOConsNot r
  | ZOConsAnd p1 p2 =>
    let r1 := SemicircuitPropConstraint_ExiFunExtend_1 _ _ _ _ uniVN freeFArity exiFArity freeFCalls exiFCalls p1 in
    let r2 := SemicircuitPropConstraint_ExiFunExtend_1 _ _ _ _ uniVN freeFArity exiFArity freeFCalls exiFCalls p2 in
    ZOConsAnd r1 r2
  | ZOConsOr p1 p2 =>
    let r1 := SemicircuitPropConstraint_ExiFunExtend_1 _ _ _ _ uniVN freeFArity exiFArity freeFCalls exiFCalls p1 in
    let r2 := SemicircuitPropConstraint_ExiFunExtend_1 _ _ _ _ uniVN freeFArity exiFArity freeFCalls exiFCalls p2 in
    ZOConsOr r1 r2
  | ZOConsImp p1 p2 =>
    let r1 := SemicircuitPropConstraint_ExiFunExtend_1 _ _ _ _ uniVN freeFArity exiFArity freeFCalls exiFCalls p1 in
    let r2 := SemicircuitPropConstraint_ExiFunExtend_1 _ _ _ _ uniVN freeFArity exiFArity freeFCalls exiFCalls p2 in
    ZOConsImp r1 r2
  | ZOConsEq p1 p2 =>
    let r1 := SemicircuitPolyConstraint_ExiFunExtend_1 _ _ _ _ uniVN freeFArity exiFArity freeFCalls exiFCalls p1 in
    let r2 := SemicircuitPolyConstraint_ExiFunExtend_1 _ _ _ _ uniVN freeFArity exiFArity freeFCalls exiFCalls p2 in
    ZOConsEq r1 r2
  end.

(* Add new existential function assuming polynomial constraints have already been added *)
Program Definition SemiCircuit_ExiFunExtend_0
  (c : SemiCircuit)
  (arity : nat)
  (ocons : |[length (polyConstraints c)]|)
  (icons : |[arity]| -> |[length (polyConstraints c)]|) :
  SemiCircuit :=
  match c with
  | {| freeVN := freeVN
     ; freeFN := freeFN
     ; freeFArity := freeFArity
     ; exiVN := exiVN
     ; exiFN := exiFN
     ; exiFArity := exiFArity 
     ; uniVN := uniVN 
     ; nu := nu 
     ; freeFCalls := freeFCalls 
     ; exiFCalls := exiFCalls 
     ; polyConstraints := polyConstraints 
     ; freeFArgs := freeFArgs 
     ; exiFArgs := exiFArgs 
     ; uniVBounds := uniVBounds 
     ; exiVBounds := exiVBounds 
     ; exiFOutputBounds := exiFOutputBounds 
     ; exiFInputBounds := exiFInputBounds 
     ; formula := formula 
    |} => 
      {| freeVN := freeVN
       ; freeFN := freeFN
       ; freeFArity := freeFArity
       ; exiVN := exiVN
       ; exiFN := exiFN.+1
       ; exiFArity := fseqSnoc arity exiFArity
       ; uniVN := uniVN 
       ; nu := nu 
       ; freeFCalls := freeFCalls 
       ; exiFCalls := fseqSnoc 0 exiFCalls
       ; polyConstraints := map (SemicircuitPolyConstraint_ExiFunExtend_1 _ _ _ _ _ freeFArity exiFArity _ _) polyConstraints
       ; freeFArgs := freeFArgs
       ; exiFArgs := fun i =>
         (if i < exiFN as b return (i < exiFN) = b -> |[fseqSnoc 0 exiFCalls i]| -> |[fseqSnoc arity exiFArity i]| -> |[length polyConstraints]|
          then fun _ => exiFArgs i
          else fun _ => emptyTuple) (erefl _)
       ; uniVBounds := uniVBounds
       ; exiVBounds := exiVBounds
       ; exiFOutputBounds := fun i =>
         (if i < exiFN as b return (i < exiFN) = b -> |[length polyConstraints]|
          then fun _ => exiFOutputBounds i
          else fun _ => ocons) (erefl _)
       ; exiFInputBounds := fun i =>
         (if i < exiFN as b return (i < exiFN) = b -> |[fseqSnoc arity exiFArity i]| -> |[length polyConstraints]|
          then fun _ => exiFInputBounds i
          else fun _ => icons) (erefl _)
       ; formula := 
          match formula with
          | inl u => inl u
          | inr f => inr (SemicircuitPropConstraint_ExiFunExtend_1 _ _ _ _ _ freeFArity exiFArity _ _ f) 
          end
      |}
  end.
Next Obligation. by rewrite map_length; destruct (freeFArgs0 _ _ _). Qed.
Next Obligation. by unfold fseqSnoc in H; rewrite dep_if_case_true in H. Qed.
Next Obligation. by unfold fseqSnoc in H; rewrite dep_if_case_true in H. Qed.
Next Obligation. by unfold fseqSnoc in H; rewrite dep_if_case_false in H. Qed.
Next Obligation.
  dep_if_case (i < exiFN0).
  by destruct (exiFArgs0 _ _ _); rewrite map_length.
  by remember (SemiCircuit_ExiFunExtend_0_obligation_5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) as D5.
Qed.
Next Obligation. by rewrite map_length; destruct (uniVBounds0 _). Qed.
Next Obligation. by rewrite map_length; destruct (exiVBounds0 _). Qed.
Next Obligation.
  dep_if_case (i < exiFN0); auto.
  by destruct (exiFOutputBounds0 _); rewrite map_length.
  by rewrite map_length.
Qed.
Next Obligation. by unfold fseqSnoc in H; rewrite dep_if_case_true in H. Qed.
Next Obligation. by unfold fseqSnoc in H; rewrite dep_if_case_false in H. Qed.
Next Obligation. hauto. Qed.
Next Obligation. 
  dep_if_case (i < exiFN0).
  by destruct (exiFInputBounds0 _); rewrite map_length.
  by rewrite map_length; hauto.
Qed.

Program Fixpoint ZOSigma11_Semicircuit 
  (freeVN : nat) (exiVN : nat) (uniVN : nat)
  (freeFA : seq nat) (exiFA : seq nat)
  (f : @ZerothOrderFormula 
          {| freeFOctx := freeVN; exiFOctx := exiVN; uniFOctx := uniVN
          ; freeSOctx := freeFA; exiSOctx := exiFA |}) :
  SemiCircuit := Hole.

Program Fixpoint FOSigma11_Semicircuit 
  (freeVN : nat) (exiVN : nat) (uniVN : nat)
  (freeFA : seq nat) (exiFA : seq nat)
  (f : @FirstOrderFormula 
          {| freeFOctx := freeVN; exiFOctx := exiVN; uniFOctx := uniVN
          ; freeSOctx := freeFA; exiSOctx := exiFA |}) :
  SemiCircuit := Hole.

Program Fixpoint Sigma11_Semicircuit 
  (freeVN : nat) (exiVN : nat) (uniVN : nat)
  (freeFA : seq nat) (exiFA : seq nat)
  (f : @SecondOrderFormula 
          {| freeFOctx := freeVN; exiFOctx := exiVN; uniFOctx := uniVN
          ; freeSOctx := freeFA; exiSOctx := exiFA |}) :
  SemiCircuit := Hole.

End SemicircuitTranslation.
