From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun zmodp ssrbool ssrnat ssralg seq fintype finfun finalg tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import Program.

Section Sigma_1_1_Internal.

Inductive PolyTerm : Type :=
| PolyVar : nat -> PolyTerm
| PolyFun : nat -> seq PolyTerm -> PolyTerm
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
      F_S : nat -> { a & {ffun a.-tuple 'F_p -> option 'F_p }};
  }.

Definition indFun {p} (x y : 'F_p) : 'F_p := if (x < y) then 1%R else 0%R.

Theorem FinFieEq {p} {a b : 'F_p} (e : a == b = true) : a = b.
Proof.
  destruct a, b.
  apply EEConvert in e; simpl in e.
  destruct e.
  by replace i with i0;[|apply eq_irrelevance].
Qed.

Fixpoint option_seq {A} (s : seq (option A)) : option (seq A) :=
  match s with
  | [::] => Some [::]
  | (x :: xs) => 
    obind (fun x => obind (fun xs => Some (x :: xs)) (option_seq xs)) x
  end.

Fixpoint option_tuple {n A} : n.-tuple (option A) -> option (n.-tuple A) :=
  match n with
  | 0 => fun _ => Some (nil_tuple A)
  | n.+1 => fun t =>
    obind (fun x => obind (fun xs => Some (cons_tuple x xs)) (option_tuple (behead_tuple t))) (thead t)
  end.

Program Fixpoint PolyDepth (r : PolyTerm) : nat :=
  match r with
  | PolyVar m => 0
  | PolyFun i t => (List.list_max (map PolyDepth t)).+1
  | PolyMinusOne => 0
  | PolyPlusOne => 0
  | PolyZero => 0
  | PolyPlus r1 r2 => (max (PolyDepth r1) (PolyDepth r2)).+1
  | PolyTimes r1 r2 => (max (PolyDepth r1) (PolyDepth r2)).+1
  | PolyInd r1 r2 =>(max (PolyDepth r1) (PolyDepth r2)).+1
  end.

Program Fixpoint Poly_Denote_WF (M : Sigma11Model)
  (n : nat) (r : PolyTerm) : option ('F_(p M)) :=
  match n with
  | 0 => None
  | n.+1 => 
    match r with
    | PolyVar m => Some (V_F M m)
    | PolyFun i t => 
      let ds := option_tuple (map_tuple (Poly_Denote_WF M n) (in_tuple t)) in
      (if size t == projT1 (F_S M i) as b return (size t == projT1 (F_S M i) = b -> option ('F_(p M)))
      then fun e => (
            obind (fun u : (size t).-tuple 'F_(p M) => projT2 (F_S M i) u) ds)
      else fun _ => None) (erefl _)
    | PolyMinusOne => Some (-1)%R
    | PolyPlusOne => Some 1%R
    | PolyZero => Some 0%R
    | PolyPlus r1 r2 => 
      let d1 := Poly_Denote_WF M n r1 in
      let d2 := Poly_Denote_WF M n r2 in
      obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) d2) d1
    | PolyTimes r1 r2 => 
      let d1 := Poly_Denote_WF M n r1 in
      let d2 := Poly_Denote_WF M n r2 in
      obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) d2) d1
    | PolyInd r1 r2 =>
      let r1 := Poly_Denote_WF M n r1 in
      let r2 := Poly_Denote_WF M n r2 in 
      obind (fun r1 => obind (fun r2 => Some (indFun r1 r2)) r2) r1
    end
  end.
Next Obligation. by apply EEConvert in e. Qed.

Definition Poly_Denote M r := Poly_Denote_WF M (PolyDepth r).+1 r.

Fixpoint ZerothOrder_Denote (M : Sigma11Model)
  (f : ZerothOrderFormula) : option bool :=
  match f with
  | ZONot f =>
    let d := ZerothOrder_Denote M f in
    obind (fun d => Some (negb d)) d
  | ZOAnd f1 f2 =>
    let d1 := ZerothOrder_Denote M f1 in
    let d2 := ZerothOrder_Denote M f2 in
    obind (fun r1 => obind (fun r2 => Some (r1 || r2)) d2) d1
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

Definition AddModelExiF  (M : Sigma11Model) (f : { newA & {ffun (newA.-tuple 'F_(p M)) -> option ('F_(p M))}})  :
  Sigma11Model := {| V_F := V_F M; F_S := ExtendAt0 f (F_S M) |}.

(* Program Fixpoint FunBounds 
  (M : Sigma11Model) {a}
  (ins : a .-tuple 'F_(p M)) (out : 'F_(p M))
  (insB : a .-tuple PolyTerm) (outB : PolyTerm) : option bool :=
  match a with
  | 0 => 
    let oB := Poly_Denote M outB in
    obind (fun oB : 'F_(p M) => Some (out < oB)) oB
  | n.+1 => 
    let iB := Poly_Denote M (thead insB) in
    let rB := @FunBounds (AddModelV M (thead ins)) n (behead_tuple ins) out (behead_tuple insB) outB in
    obind (fun rB => obind (fun iB : 'F_(p M) => Some ((thead ins < iB) && rB)) iB) rB    
  end. *)

Program Fixpoint FunBounds 
  (M : Sigma11Model) {a}
  (ins : a .-tuple 'F_(p M)) (out : option 'F_(p M))
  (insB : a .-tuple PolyTerm) (outB : PolyTerm) : bool :=
  match a with
  | 0 => 
    match out with
    | None => true
    | Some out =>
      match Poly_Denote M outB with
      | None => false
      | Some oB => out < oB
      end
    end
  | n.+1 => 
    match Poly_Denote M (thead insB) with
    | None => false
    | Some iB => (thead ins < iB) && @FunBounds (AddModelV M (thead ins)) n (behead_tuple ins) out (behead_tuple insB) outB
    end  
  end.

Definition Hole {A} : A. Admitted.

(* Definition Fun_Bound_Check 
  (M : Sigma11Model)
  {n : nat}
  (bs : n .-tuple PolyTerm)
  (y : PolyTerm)
  (f : {ffun (n.-tuple 'F_(p M)) -> option ('F_(p M))}) :  option bool :=
let ips : seq (n .-tuple 'F_(p M) * 'F_(p M))
        := enum [pred x | f x.1 == Some x.2] in
obind (fun x => Some (all [pred x | x] x))
      (option_seq (map (fun x => FunBounds M x.1 x.2 bs y) ips)). *)

Definition Fun_Bound_Check
  (M : Sigma11Model)
  {n : nat}
  (bs : n .-tuple PolyTerm)
  (y : PolyTerm)
  (f : {ffun (n.-tuple 'F_(p M)) -> option ('F_(p M))}) : bool :=
all [pred x | FunBounds M (projT1 x) (projT2 x) bs y] (tfgraph f).

(*
Note: there's no way to get this to coherently return an undefined value. 
Consider the statement "exists F, P F" where "P F" may be undefined.
Because the outside is "exists" the overall expression must return a bool,
but because the "F" is bound by "exists", we can't take "P" outside of
"F"'s scope to see if "P F" would give an undefined value. So the potential
undefined value must be interpreted as a bool if it comes up in order to
evaluate the expression at all.

To handle this, I check that "P F == Some true" which will be false when
"P F" is undefined.
*)

Fixpoint QuantifiedFormula_Denote (M : Sigma11Model) (f : QuantifiedFormula) : option bool :=
  match f with
  | ZO z => ZerothOrder_Denote M z
  | QExists bs y f => Some
    [exists F, Fun_Bound_Check M (in_tuple bs) y F
            && (QuantifiedFormula_Denote (AddModelExiF M (existT _ (size bs) F)) f == Some true)] 
  | QForall B f => obind (fun B : 'F_(p M) => Some
    [forall r, ((r : 'F_(p M)) < B) ==> (QuantifiedFormula_Denote (AddModelV M r) f == Some true)]
  ) (Poly_Denote M B)
  end.

End Sigma_1_1_Denotation.
