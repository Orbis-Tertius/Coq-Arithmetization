From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun zmodp ssrbool ssrnat ssralg seq fintype finalg tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import Program.

Section Sigma_1_1_Internal.

Inductive PolyTerm {A : nat -> nat} : Type :=
| PolyVar : nat -> PolyTerm
| PolyFun : forall i, (|[A i]| -> PolyTerm) -> PolyTerm
| PolyMinusOne : PolyTerm
| PolyPlusOne : PolyTerm
| PolyZero : PolyTerm
| PolyPlus : PolyTerm -> PolyTerm -> PolyTerm
| PolyTimes : PolyTerm -> PolyTerm -> PolyTerm
| PolyInd : PolyTerm -> PolyTerm -> PolyTerm.

Inductive ZerothOrderFormula {A} : Type :=
| ZONot : ZerothOrderFormula -> ZerothOrderFormula
| ZOAnd : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOOr : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOImp : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOEq : @PolyTerm A -> @PolyTerm A -> ZerothOrderFormula.

Inductive QuantifiedFormula {A} : Type :=
| ZO : @ZerothOrderFormula A
    -> QuantifiedFormula
| QExists : forall (bs : seq (@PolyTerm A))
                   (y : @PolyTerm A),
            @QuantifiedFormula (ExtendAt0 (length bs) A)
         -> QuantifiedFormula
| QForall : @PolyTerm A
         -> QuantifiedFormula
         -> QuantifiedFormula.

End Sigma_1_1_Internal.



Section Sigma_1_1_Denotation.

Variable (FSize : nat).

Record Sigma11Model : Type :=
  mkSigma11Model {
      V_F : nat -> 'F_FSize;
      F_S : nat -> { a & (|[a]| -> 'F_FSize) -> option 'F_FSize };
  }.


Definition indFun {p} (x y : 'F_p) : 'F_p := if (x < y) then 1%R else 0%R.

Theorem FinFieEq {p} {a b : 'F_p} (e : a == b = true) : a = b.
Proof.
  destruct a, b.
  apply EEConvert in e; simpl in e.
  destruct e.
  by replace i with i0;[|apply eq_irrelevance].
Qed.

Fixpoint Poly_Denote (M : Sigma11Model) 
  (r : @PolyTerm (fun x => projT1 (F_S M x))) : option ('F_FSize) :=
  match r with
  | PolyVar m => Some (V_F M m)
  | PolyFun i t => 
    let ds := option_fun (fun x => Poly_Denote M (t x)) in
    obind (projT2 (F_S M i)) ds
  | PolyMinusOne => Some (-1)%R
  | PolyPlusOne => Some 1%R
  | PolyZero => Some 0%R
  | PolyPlus r1 r2 => 
    let d1 := Poly_Denote M r1 in
    let d2 := Poly_Denote M r2 in
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) d2) d1
  | PolyTimes r1 r2 => 
    let d1 := Poly_Denote M r1 in
    let d2 := Poly_Denote M r2 in
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) d2) d1
  | PolyInd r1 r2 =>
    let r1 := Poly_Denote M r1 in
    let r2 := Poly_Denote M r2 in 
    obind (fun r1 => obind (fun r2 => Some (indFun r1 r2)) r2) r1
  end.

Fixpoint ZerothOrder_Denote (M : Sigma11Model)
  (f : @ZerothOrderFormula (fun x => projT1 (F_S M x))) : option bool :=
  match f with
  | ZONot f =>
    let d := ZerothOrder_Denote M f in
    obind (fun d => Some (negb d)) d
  | ZOAnd f1 f2 =>
    let d1 := ZerothOrder_Denote M f1 in
    let d2 := ZerothOrder_Denote M f2 in
    obind (fun r1 => obind (fun r2 => Some (r1 && r2)) d2) d1
  | ZOOr f1 f2 => 
    let d1 := ZerothOrder_Denote M f1 in
    let d2 := ZerothOrder_Denote M f2 in
    obind (fun r1 => obind (fun r2 => Some (r1 || r2)) d2) d1
  | ZOImp f1 f2 => 
    let d1 := ZerothOrder_Denote M f1 in
    let d2 := ZerothOrder_Denote M f2 in
    obind (fun r1 => obind (fun r2 => Some (r1 ==> r2)) d2) d1
  | ZOEq r1 r2 => 
    let d1 := Poly_Denote M r1 in
    let d2 := Poly_Denote M r2 in
    obind (fun r1 => obind (fun r2 => Some (r1 == r2)) d2) d1
  end.

Definition AddModelV (M : Sigma11Model) (r : 'F_FSize) : Sigma11Model :=
  {| V_F := ExtendAt0 r (V_F M); F_S := F_S M |}.

Definition AddModelF  (M : Sigma11Model) (f : { newA & (|[newA]| -> 'F_FSize) -> option ('F_FSize)})  :
  Sigma11Model := {| V_F := V_F M; F_S := ExtendAt0 f (F_S M) |}.

Program Fixpoint FunBounds 
  (M : Sigma11Model) {a}
  (ins : |[a]| -> 'F_FSize) (out : 'F_FSize)
  (insB : |[a]| -> @PolyTerm (fun x => projT1 (F_S M x))) (outB : @PolyTerm (fun x => projT1 (F_S M x))) : bool :=
  match a with
  | 0 => 
    match Poly_Denote M outB with
    | None => false
    | Some oB => out < oB
    end
  | n.+1 => 
    match Poly_Denote M (insB 0) with
    | None => false
    | Some iB => (ins 0 < iB) && @FunBounds (AddModelV M (ins 0)) n (fun x => ins (x.+1)) out (fun x => insB (x.+1)) outB
    end  
  end.

Definition Fun_Bound_Check 
  (M : Sigma11Model)
  {n : nat}
  (bs : |[n]| -> @PolyTerm (fun x => projT1 (F_S M x)))
  (y : @PolyTerm (fun x => projT1 (F_S M x)))
  (f : (|[n]| -> 'F_FSize) -> option ('F_FSize)) : Prop :=
forall (ins : |[n]| -> 'F_FSize) (out : 'F_FSize),
  f ins == Some out -> 
  FunBounds M ins out bs y == true.

Program Fixpoint QuantifiedFormula_Denote (M : Sigma11Model) (f : @QuantifiedFormula (fun x => projT1 (F_S M x))) : Prop :=
  match f with
  | ZO z => ZerothOrder_Denote M z == Some true
  | QExists bs y f => 
    exists (F : (|[length bs]| -> 'F_FSize) -> option ('F_FSize)), 
    Fun_Bound_Check M (lnth bs) y F /\ QuantifiedFormula_Denote (AddModelF M (existT _ (length bs) F)) f
  | QForall b f =>
    match Poly_Denote M b with
    | None => False
    | Some p' => forall (r : 'F_FSize), r < p' -> QuantifiedFormula_Denote (AddModelV M r) f
    end
  end.
Next Obligation.
  apply functional_extensionality;move=> [|x]; auto.
Qed.

End Sigma_1_1_Denotation.
