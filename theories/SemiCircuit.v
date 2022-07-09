From Hammer Require Import Tactics Reflect Hints.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint seq choice.
From mathcomp Require Import fintype div intdiv tuple bigop prime finset fingroup.
From mathcomp Require Import ssralg poly polydiv morphism action finalg zmodp.
From mathcomp Require Import cyclic center pgroup abelian matrix mxpoly vector.
From mathcomp Require Import falgebra fieldext separable galois.
From mathcomp Require ssrnum ssrint.

Require Import CoqArith.Sigma_1_1_Stratified.

Section SemicircuitDef.


(* Some theorems justifying skolemization. *)
Theorem Cannon (phi : nat -> nat -> Prop) : 
  (exists (x : nat), forall (y : nat), phi x y) ->
  (forall (y : nat), exists (x : nat), phi x y).
Proof. sauto. Qed.

Theorem Cannon2 (phi : nat -> nat -> Prop) (f : nat -> nat) : 
  (exists n, forall x, f x = n) ->
  (forall (y : nat), phi (f y) y) -> (exists (x : nat), forall (y : nat), phi x y).
Proof. sauto. Qed.

Theorem Cannon3 (phi : nat -> nat -> Prop) : 
  forall (f : forall (y : nat), { x : nat & phi x y }),
  (exists n, forall i, projT1 (f i) = n) ->
  (exists (x : nat), forall (y : nat), phi x y).
Proof.
  move => f [n e].
  exists n.
  move=> y.
  assert (phi (projT1 (f y)) y);[exact (projT2 (f y))|hauto].
Qed.


(*Convert a sequence of bounds for universally quantified vars
  into the input type of a skolem function. *)
Definition QuantBoundType (M : SecondOrderFormulaModel) (l : seq nat) : Type :=
  forall (i : 'I_(length l)), { r : R M | lt M r (naturalRingElement (tnth (in_tuple l) i)) }.

Inductive RingConstraint {funs unis exis : nat} : Type :=
| RingConsFun : 'I_funs -> RingConstraint
| RingConsUni : 'I_unis -> RingConstraint
| RingConsExi : 'I_exis -> RingConstraint
| RingConsMinusOne : RingConstraint
| RingConsPlusOne : RingConstraint
| RingConsZero : RingConstraint
| RingConsPlus : RingConstraint -> RingConstraint -> RingConstraint
| RingConsTimes : RingConstraint -> RingConstraint -> RingConstraint.

Inductive ZerothOrderConstraint {eqidx : nat} : Type :=
| ZOConsTrue : ZerothOrderConstraint
| ZOConsFalse : ZerothOrderConstraint
| ZOConsNot : ZerothOrderConstraint -> ZerothOrderConstraint
| ZOConsAnd : ZerothOrderConstraint ->
          ZerothOrderConstraint ->
          ZerothOrderConstraint
| ZOConsOr : ZerothOrderConstraint ->
         ZerothOrderConstraint ->
         ZerothOrderConstraint
| ZOConsImp : ZerothOrderConstraint ->
          ZerothOrderConstraint ->
          ZerothOrderConstraint
| ZOConsEq : 'I_eqidx -> 'I_eqidx -> ZerothOrderConstraint.

Record SemiCircuit (M : SecondOrderFormulaModel) : Type :=
  mkSemiCircuit {
    InstanceFO : seq (R M);
    InstanceSO : seq {n : nat & 
                     {y : (R M) & 
                     {bs : n.-tuple (R M) & 
                     (forall i : 'I_n, {r : R M | lt M r (tnth bs i)}) -> {r : R M | lt M r y}}}};

    ExQuantSO : seq {n : nat & 
                  {y : (R M) & 
                  {bs : n.-tuple (R M) & 
                  (forall i : 'I_n, {r : R M | lt M r (tnth bs i)}) -> {r : R M | lt M r y}}}};
    
    UniQuantBnds : seq nat;

    (* States how many universal quantifiers appear prior to each existential quantifier *)
    ExQuantFO : seq (QuantBoundType M UniQuantBnds -> R M);

    (*Function calls with their inputs and outputs. *)
    FunCalls : seq (QuantBoundType M UniQuantBnds -> 
                    (R M * 
                    {i : 'I_(length (InstanceSO ++ ExQuantSO)) & 
                         (projT1 (tnth (in_tuple (InstanceSO ++ ExQuantSO)) i)).-tuple (R M)
                    }));

    (*The constraints defining the values at each function call. *)
    FunConst : forall (c : 'I_(length FunCalls))
                (unVals : QuantBoundType M UniQuantBnds),
                (projT1 (tnth (in_tuple (InstanceSO ++ ExQuantSO)) (projT1 (tnth (in_tuple FunCalls) c unVals).2))).-tuple
                (@RingConstraint (length FunCalls) (length UniQuantBnds) (length ExQuantFO));

    (*Equation value pairs*)
    Equs : seq (R M * R M);

    (*The constraints defininf the values at each equation entry.*)
    EquConst : 'I_(length Equs) -> QuantBoundType M UniQuantBnds ->
              (@RingConstraint (length FunCalls) (length UniQuantBnds) (length ExQuantFO))
              * (@RingConstraint (length FunCalls) (length UniQuantBnds) (length ExQuantFO));

    FormulaConst : QuantBoundType M UniQuantBnds -> @ZerothOrderConstraint (length Equs);

  }.


End SemicircuitDef.
