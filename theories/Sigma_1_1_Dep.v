From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun zmodp ssrbool ssrnat ssralg seq fintype finalg tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import Program.

Section Sigma_1_1_Internal.

Inductive PolyTerm : Type :=
| PolyVar : nat -> PolyTerm
| PolyFun : forall (i a : nat), ('I_a -> PolyTerm) -> PolyTerm
| PolyMinusOne : PolyTerm
| PolyPlusOne : PolyTerm
| PolyZero : PolyTerm
| PolyPlus : PolyTerm -> PolyTerm -> PolyTerm
| PolyTimes : PolyTerm -> PolyTerm -> PolyTerm
| PolyInd : PolyTerm -> PolyTerm -> PolyTerm.

Inductive ZerothOrderFormula : Type :=
| ZONot : ZerothOrderFormula -> ZerothOrderFormula
| ZOAnd : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOOr : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOImp : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOEq : PolyTerm -> PolyTerm -> ZerothOrderFormula.

Inductive QuantifiedFormula : Type :=
| ZO : ZerothOrderFormula
    -> QuantifiedFormula
| QExists : forall (bs : seq (PolyTerm))
                   (y : PolyTerm),
            QuantifiedFormula
         -> QuantifiedFormula
| QForall : PolyTerm
         -> QuantifiedFormula
         -> QuantifiedFormula.

End Sigma_1_1_Internal.



Section Sigma_1_1_Denotation.

Record Sigma11Model : Type :=
  mkSigma11Model {
      p : nat;
      V_F : nat -> 'F_p;
      F_S : nat -> { a & ('I_a -> 'F_p) -> option 'F_p };
  }.

Definition indFun {p} (x y : 'F_p) : 'F_p := if (x < y) then 1%R else 0%R.

Theorem FinFieEq {p} {a b : 'F_p} (e : a == b = true) : a = b.
Proof.
  destruct a, b.
  apply EEConvert in e; simpl in e.
  destruct e.
  by replace i with i0;[|apply eq_irrelevance].
Qed.

Program Fixpoint Poly_Denote (M : Sigma11Model) 
  (r : PolyTerm) : option ('F_(p M)) :=
  match r with
  | PolyVar m => Some (V_F M m)
  | PolyFun i a t => 
    (if a == projT1 (F_S M i) as b return ((a == projT1 (F_S M i)) = b -> option ('F_(p M)))
     then fun _ => (
          let ds := option_fun (fun x => Poly_Denote M (t x)) in
          obind (fun t : 'I_a -> 'F_(p M) => projT2 (F_S M i) t) ds)
      else fun _ => None) (erefl _)
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
Next Obligation. apply EEConvert in e; qauto. Qed.

Fixpoint ZerothOrder_Denote (M : Sigma11Model)
  (f : ZerothOrderFormula) : option bool :=
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
    obind (fun r1 => obind (fun r2 => Some (negb r1 || r2)) d2) d1
  | ZOEq r1 r2 => 
    let d1 := Poly_Denote M r1 in
    let d2 := Poly_Denote M r2 in
    obind (fun r1 => obind (fun r2 => Some (r1 == r2)) d2) d1
  end.

Definition AddModelV (M : Sigma11Model) (r : 'F_(p M)) : Sigma11Model :=
  {| V_F := ExtendAt0 r (V_F M); F_S := F_S M |}.

Definition AddModelExiF  (M : Sigma11Model) (f : { newA & (|[newA]| -> 'F_(p M)) -> option ('F_(p M))})  :
  Sigma11Model := {| V_F := V_F M; F_S := ExtendAt0 f (F_S M) |}.

Definition Hole {A} : A. Admitted.

Program Fixpoint FunBounds 
  (M : Sigma11Model) {a}
  (ins : |[a]| -> 'F_(p M)) (out : 'F_(p M))
  (insB : |[a]| -> PolyTerm) (outB : PolyTerm) : option Prop :=
  match a with
  | 0 => 
    let oB := Poly_Denote M outB in
    obind (fun oB : 'F_(p M) => Some ((out < oB) = true)) oB
  | n.+1 => 
    let iB := Poly_Denote M (insB 0) in
    let rB := FunBounds (AddModelV M (ins 0)) (fun x : |[n]| => ins (x.+1)) out (fun x : |[n]| => insB (x.+1)) outB in
    obind (fun rB => obind (fun iB : 'F_(p M) => Some ((ins 0 < iB) = true /\ rB)) iB) rB    
  end.

Definition Fun_Bound_Check 
  (M : Sigma11Model)
  {n : nat}
  (bs : |[n]| -> PolyTerm)
  (y : PolyTerm)
  (f : (|[n]| -> 'F_(p M)) -> option ('F_(p M))) : option Prop :=
forall (ins : |[n]| -> 'F_(p M)) (out : 'F_(p M)),
  f ins == Some out -> 
  FunBounds M ins out bs y == Some true.

Fixpoint QuantifiedFormula_Denote (M : Sigma11Model) (f : QuantifiedFormula) : option bool :=
  match f with
  | ZO z => ZerothOrder_Denote z M
  | QExists bs y f => 
    let BC := FunBounds M 

    let op := Poly_Denote p M in
    match op with
    | None => false
    | Some p' => exists (r : 'F_(p M)), lt D r p' /\ QuantifiedFormula_Denote f
    end
  | FOForall p f =>
    let op := Poly_Denote p M in
    match op with
    | None => true
    | Some p' => forall (r : 'F_(p M)),  lt D r p' -> QuantifiedFormula_Denote (AddModelV M r) f
    end
  end.

Definition SO_Bound_Check 
  (M : Sigma11Model)
  (n : nat)
  (y : 'F_(p M))
  (bs : |[n]| -> 'F_(p M))
  (f : (|[n]| -> 'F_(p M)) -> option ('F_(p M))) : Prop :=
forall (ins : |[n]| -> 'F_(p M)) (out : 'F_(p M)),
  f ins = Some out ->
  (forall x : |[n]|, lt D (ins x) (bs x)) /\ lt D out y.

Definition AddModelExiFA (f : forall newA, (|[newA]| -> 'F_(p M)) -> option ('F_(p M))) (M : Sigma11Model)  :
  Sigma11Model := {| V_F := V_F M; F_S := ExtendAt0 f (F_S M) |}.

Program Definition AddModelExiF (newA : nat) (f : (|[newA]| -> 'F_(p M)) -> option ('F_(p M))) (M : Sigma11Model)  :
  Sigma11Model :=
  AddModelExiFA (fun a => (
    if a == newA as b return ((a == newA) = b -> (|[a]| -> 'F_(p M)) -> option ('F_(p M)))
    then fun _ => f
    else fun _ _ => None
  ) (erefl _)) M.
Next Obligation. apply EEConvert in e; by destruct e. Qed.

Fixpoint SecondOrder_Denote (f : SecondOrderFormula) (M : Sigma11Model) : Prop :=
  match f with
  | FO f => FirstOrder_Denote f M
  | SOExists y bs f => 
    let y' : option ('F_(p M)) := Poly_Denote y M in
    let bs' : option (|[length bs]| -> 'F_(p M)) := 
        option_tuple (fun m => Poly_Denote (lnth bs m) M) in
    match y' with
    | None => false
    | Some y' =>
      match bs' with
      | None => false
      | Some bs' =>
        exists a : (|[length bs]| -> 'F_(p M)) -> option ('F_(p M)),
          SO_Bound_Check M (length bs) y' bs' a 
          /\ SecondOrder_Denote f (AddModelExiF (length bs) a M)
      end
    end
  end.

End Sigma_1_1_Denotation.
