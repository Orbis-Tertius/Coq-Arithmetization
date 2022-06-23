From Hammer Require Import Tactics Reflect Hints.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint seq choice.
From mathcomp Require Import fintype div intdiv tuple bigop prime finset fingroup.
From mathcomp Require Import ssralg poly polydiv morphism action finalg zmodp.
From mathcomp Require Import cyclic center pgroup abelian matrix mxpoly vector.
From mathcomp Require Import falgebra fieldext separable galois.
From mathcomp Require ssrnum ssrint.

Section CircuitDef.

Variable F : finFieldType.
(* Implicit Types (a b c x y z : F) (p q r d : {poly F}). *)

Variant ColumnType : Type :=
| Fixed
| Advice 
| Instance.

Variant EqualityType : Type :=
| Equality
| NonEquality.

Record PolyLim (d : nat) (Y : Type) :=
  mkPolyLim {
    polynomial : {poly F};
    pDegreeLim : size polynomial <= d + 1;
    formalVars : (size polynomial).-tuple Y
  }. 

Record Circuit : Type :=
  mkCircuit {
    FixedNum : nat;
    InstanceNum : nat;
    AdviceNum : nat;
    (* called "n" *)
    ColNum := FixedNum + (InstanceNum + AdviceNum);
    (* A single vector, denoted "c" *)
    columnEqualityTypes : ColNum.-tuple EqualityType;
    degree : nat; (* called "d" *)
    degreePos : degree > 0;
    (* called "p" of length "m" *)
    polynomials : seq (PolyLim degree ('I_ColNum * int));
    (* called "l" of length k × q *)
    lookup : seq {q : nat & q.-tuple (PolyLim degree ('I_ColNum * int) * 'I_ColNum)};
    RowNum' : nat; (* Note: must be positive to take modulus in Polynomial Constraint. *)
    RowNum := RowNum'.+1; (* called "r" *)
    (* called "e" of length "t" *)
    Equalities : seq (('I_ColNum * 'I_RowNum) * ('I_ColNum * 'I_RowNum));
    (* called "X" *)
    FixedColumns : 'M[F]_(FixedNum, RowNum) ;
  }.

Definition FixedConstraint (C : Circuit) (M : 'M[F]_(ColNum C, RowNum C)) : Prop :=
  usubmx M = FixedColumns C.

Definition PolynomialMultieval (p : {poly F}) (v : seq F) : F :=
  \sum_(i < size p) p`_i * v`_i ^+ i.

Definition PolynomialConstraint (C : Circuit) (M : 'M[F]_(ColNum C, RowNum C)) : Prop :=
  List.Forall (fun (p : PolyLim (degree C) ('I_(ColNum C) * int)) => 
    List.Forall (fun j =>
      let Xs : seq F := 
          map (fun nr => M nr.1 (inZp (absz (modz (intZmod.addz nr.2 (Posz j)) (RowNum C)))))
              (formalVars _ _ p)
      in PolynomialMultieval (polynomial _ _ p) Xs = 0%R
      ) (List.seq 0 (RowNum C - 1))
    ) (polynomials C).

Definition LookupConstraint (C : Circuit) (M : 'M[F]_(ColNum C, RowNum C)) : Prop :=
  List.Forall (fun l' : {q : nat & q.-tuple _} =>
  let (q, l) := l' in
  let p := List.split l
  in List.Forall (fun rho => 
    let y := map (fun xj => 
      let Xs := map (fun nr => M nr.1 (inZp (absz (modz (intZmod.addz nr.2 (Posz rho)) (RowNum C))))) 
                    (formalVars _ _ xj)
      in PolynomialMultieval (polynomial _ _ xj) Xs) p.1
    in exists l : 'I_(RowNum C),
       y = map (fun n => M n l) p.2
    ) (List.seq 0 (RowNum C - 1))
  ) (lookup C).

Definition EqualityConstraint (C : Circuit) (M : 'M[F]_(ColNum C, RowNum C)) : Prop :=
  List.Forall 
    (fun ab => uncurry M ab.1 = uncurry M ab.2) 
    (Equalities C).

Definition EqualityTypeCheck (C : Circuit) (M : 'M[F]_(ColNum C, RowNum C)) : Prop :=
  List.Forall 
    (fun ab : ('I_(ColNum C) * 'I_(RowNum C)) * ('I_(ColNum C) * 'I_(RowNum C)) => 
      let ca := ab.1.1 in
      let cb := ab.2.1 in
      and (tnth (columnEqualityTypes C) ca = Equality)
          (tnth (columnEqualityTypes C) cb = Equality)
    )
    (Equalities C).

(* Every circuit defines a predicate over n × r matrices. *)
Definition CircuitConstraint (C : Circuit) (M : 'M[F]_(ColNum C, RowNum C)) : Prop :=
  and (FixedConstraint C M) (
  and (PolynomialConstraint C M) (
  and (LookupConstraint C M) (
  and (EqualityConstraint C M) (
       EqualityTypeCheck C M
  )))).

Definition ArithmetizedRelation (C : Circuit) 
  (Y : 'M[F]_(InstanceNum C, RowNum C)) : Prop :=
  exists (Z : 'M[F]_(AdviceNum C, RowNum C)),
  CircuitConstraint C (col_mx (FixedColumns C) (col_mx Y Z)).

Definition ArithmetizedRelation_D (C : Circuit)
  (D : Type) (f : D -> 'M[F]_(InstanceNum C, RowNum C)) (d : D) : Prop :=
  exists (Z : 'M[F]_(AdviceNum C, RowNum C)),
  CircuitConstraint C (col_mx (FixedColumns C) (col_mx (f d) Z)).

