From Hammer Require Import Tactics Reflect Hints.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint seq choice.
From mathcomp Require Import fintype div intdiv tuple bigop prime finset fingroup.
From mathcomp Require Import ssralg poly polydiv morphism action finalg zmodp.
From mathcomp Require Import cyclic center pgroup abelian matrix mxpoly vector.
From mathcomp Require Import falgebra fieldext separable galois.
From mathcomp Require ssrnum ssrint.

Require Import CoqArith.Sigma_1_1_Stratified.

Section SemicircuitDef.

(*Convert a sequence of bounds for universally quantified vars
  into the input type of a skolem function. *)
Fixpoint QuantBoundType (M : SecondOrderFormulaModel) (l : seq nat) : Type :=
  match l with 
  | [::] => unit
  | x :: xs => { r : R M | lt M r (naturalRingElement x) } * QuantBoundType M xs
  end.

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




(*
Inductive RingTerm {soctx : SOctx} {foctx : FOctx} : Type :=
| RingVar : 'I_foctx -> RingTerm
| RingFun : forall (i : 'I_(length soctx)),
            ('I_(tnth (in_tuple soctx) i) -> RingTerm) ->
            RingTerm
| RingMinusOne : RingTerm
| RingPlusOne : RingTerm
| RingZero : RingTerm
| RingPlus : RingTerm -> RingTerm -> RingTerm
| RingTimes : RingTerm -> RingTerm -> RingTerm.
*)

(*
Record SemiCircuit (M : SecondOrderFormulaModel) : Type :=
  mkSemiCircuit {
    FreeFO : seq (R M);
    FreeSO : seq {n : nat & 
                 {y : (R M) & 
                 {bs : n.-tuple (R M) & 
                 (forall i : 'I_n, {r : R M | lt M r (tnth bs i)}) -> {r : R M | lt M r y}}}};

    QuantSO : seq {n : nat & 
                  {y : (R M) & 
                  {bs : n.-tuple (R M) & 
                  (forall i : 'I_n, {r : R M | lt M r (tnth bs i)}) -> {r : R M | lt M r y}}}};
    
    UniQuantBnds : seq nat;

    (* States how many universal quantifiers appear prior to each existential quantifier *)
    QuantFO : seq {i : 'I_(length UniQuantBnds) & QuantBoundType M (take i UniQuantBnds) -> R M }


  }.
*)


Record SemiCircuit (M : SecondOrderFormulaModel) : Type :=
  mkSemiCircuit {
    InstanceFO : seq (R M);
    InstanceSO : seq {n : nat & 
                     {y : (R M) & 
                     {bs : n.-tuple (R M) & 
                     (forall i : 'I_n, {r : R M | lt M r (tnth bs i)}) -> {r : R M | lt M r y}}}};

    QuantSO : seq {n : nat & 
                  {y : (R M) & 
                  {bs : n.-tuple (R M) & 
                  (forall i : 'I_n, {r : R M | lt M r (tnth bs i)}) -> {r : R M | lt M r y}}}};
    
    UniQuantBnds : seq nat;

    (* States how many universal quantifiers appear prior to each existential quantifier *)
    QuantFO : seq (QuantBoundType M UniQuantBnds -> R M);

    (*Function calls with their inputs an outputs. *)
    FunCalls : seq (QuantBoundType M UniQuantBnds -> 
                    (R M * 
                    {i : 'I_(length (InstanceSO ++ QuantSO)) & 
                      (projT1 (tnth (in_tuple (InstanceSO ++ QuantSO)) i)).-tuple (R M)
                    }));
  }.

End SemicircuitDef.
