From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import Program.

Section Sigma_1_1_Internal.

Inductive PolyTerm 
  {freeV freeF} {freeFA : |[freeF]| -> nat} 
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV} : Type :=
| PolyFVar : |[freeV]| -> PolyTerm
| PolyEVar : |[exiV]| -> PolyTerm
| PolyUVar : |[uniV]| -> PolyTerm
| PolyFFun : forall (i : |[freeF]|), (|[freeFA i]| -> PolyTerm) -> PolyTerm
| PolyEFun : forall (i : |[exiF]|), (|[exiFA i]| -> PolyTerm) -> PolyTerm
| PolyMinusOne : PolyTerm
| PolyPlusOne : PolyTerm
| PolyZero : PolyTerm
| PolyPlus : PolyTerm -> PolyTerm -> PolyTerm
| PolyTimes : PolyTerm -> PolyTerm -> PolyTerm
| PolyInd : PolyTerm -> PolyTerm -> PolyTerm.

Inductive ZerothOrderFormula
  {freeV freeF} {freeFA : |[freeF]| -> nat} 
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV} : Type :=
| ZONot : ZerothOrderFormula -> ZerothOrderFormula
| ZOAnd : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOOr : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOImp : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOEq : @PolyTerm freeV freeF freeFA exiV exiF exiFA uniV
      -> @PolyTerm freeV freeF freeFA exiV exiF exiFA uniV
      -> ZerothOrderFormula.

Inductive FirstOrderFormula 
  {freeV freeF} {freeFA : |[freeF]| -> nat} 
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV} : Type :=
| ZO : @ZerothOrderFormula freeV freeF freeFA exiV exiF exiFA uniV
    -> FirstOrderFormula
| FOExists : @PolyTerm freeV freeF freeFA exiV exiF exiFA uniV
          -> @FirstOrderFormula freeV freeF freeFA (exiV.+1) exiF exiFA uniV
          -> FirstOrderFormula
| FOForall : @PolyTerm freeV freeF freeFA exiV exiF exiFA uniV
          -> @FirstOrderFormula freeV freeF freeFA exiV exiF exiFA (uniV.+1)
          -> FirstOrderFormula.

Inductive SecondOrderFormula 
  {freeV freeF} {freeFA : |[freeF]| -> nat} 
  {exiF} {exiFA : |[exiF]| -> nat}: Type :=
| FO : @FirstOrderFormula freeV freeF freeFA 0 exiF exiFA 0
    -> SecondOrderFormula
| SOExists : 
  forall (y : @PolyTerm freeV freeF freeFA 0 exiF exiFA 0) 
         (bs : seq (@PolyTerm freeV freeF freeFA 0 exiF exiFA 0)), 
  @SecondOrderFormula freeV freeF freeFA (exiF.+1) (ExtendAt0N (length bs) exiFA) ->
  SecondOrderFormula.

End Sigma_1_1_Internal.



Section Sigma_1_1_Denotation.

Variable D : RingData.

Record Sigma11Model : Type :=
  mkSigma11Model {
      freeV_F : nat -> T D;
      freeF_S : forall i a : nat, (|[a]| -> (T D)) -> option (T D);
      exiV_F : nat -> (T D);
      exiF_S : forall i a : nat, (|[a]| -> (T D)) -> option (T D);
      uniV_F : nat -> (T D);
  }.

Definition indFun (x y : T D) : T D := if lt_dec D x y then 1%R else 0%R.

Fixpoint Poly_Denote
  {freeV freeF freeFA exiV exiF exiFA uniV}
  (r : @PolyTerm freeV freeF freeFA exiV exiF exiFA uniV) 
  (M : Sigma11Model) : option (T D) :=
  match r with
  | PolyFVar m => Some (freeV_F M (` m))
  | PolyEVar m => Some (exiV_F M (` m))
  | PolyUVar m => Some (uniV_F M (` m))
  | PolyFFun i t => 
    obind (fun t => freeF_S M (` i) (freeFA i) t) (option_tuple (fun x => Poly_Denote (t x) M))
  | PolyEFun i t => 
    obind (fun t => exiF_S M (` i) (exiFA i) t) (option_tuple (fun x => Poly_Denote (t x) M))
  | PolyMinusOne => Some (-1)%R
  | PolyPlusOne => Some 1%R
  | PolyZero => Some 0%R
  | PolyPlus r1 r2 => 
    let d1 := Poly_Denote r1 M in
    let d2 := Poly_Denote r2 M in
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) d2) d1
  | PolyTimes r1 r2 => 
    let d1 := Poly_Denote r1 M in
    let d2 := Poly_Denote r2 M in
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) d2) d1
  | PolyInd r1 r2 =>
    let r1 := Poly_Denote r1 M in
    let r2 := Poly_Denote r2 M in 
    obind (fun r1 => obind (fun r2 => Some (indFun r1 r2)) r2) r1
  end.

Fixpoint ZerothOrder_Denote
  {freeV freeF freeFA exiV exiF exiFA uniV}
  (f : @ZerothOrderFormula freeV freeF freeFA exiV exiF exiFA uniV)
  (M : Sigma11Model) : Prop :=
  match f with
  (* | ZOTrue => true
  | ZOFalse => false *)
  | ZONot f => not (ZerothOrder_Denote f M)
  | ZOAnd f1 f2 => (ZerothOrder_Denote f1 M) /\ (ZerothOrder_Denote f2 M)
  | ZOOr f1 f2 => (ZerothOrder_Denote f1 M) \/ (ZerothOrder_Denote f2 M)
  | ZOImp f1 f2 => (ZerothOrder_Denote f1 M) -> (ZerothOrder_Denote f2 M)
  | ZOEq r1 r2 => 
    match Poly_Denote r1 M with
    | None => false
    | Some r1 =>
      match Poly_Denote r2 M with
      | None => false
      | Some r2 => r1 = r2
      end
    end
  end.

Definition AddModelExi (M : Sigma11Model) (r : T D) : Sigma11Model :=
  {| freeV_F := freeV_F M; freeF_S := freeF_S M; exiV_F := ExtendAt0 r (exiV_F M); exiF_S := exiF_S M; uniV_F := uniV_F M |}.

Definition AddModelUni (M : Sigma11Model) (r : T D) : Sigma11Model :=
  {| freeV_F := freeV_F M; freeF_S := freeF_S M; exiV_F := exiV_F M; exiF_S := exiF_S M; uniV_F := ExtendAt0 r (uniV_F M) |}.

Fixpoint FirstOrder_Denote
  {freeV freeF freeFA exiV exiF exiFA uniV}
  (f : @FirstOrderFormula freeV freeF freeFA exiV exiF exiFA uniV)
  (M : Sigma11Model) : Prop :=
  match f with
  | ZO z => ZerothOrder_Denote z M
  | FOExists p f => 
    let op := Poly_Denote p M in
    match op with
    | None => False
    | Some p' => exists (r : T D), lt D r p' /\ FirstOrder_Denote f (AddModelExi M r)
    end
  | FOForall p f =>
    let op := Poly_Denote p M in
    match op with
    | None => False
    | Some p' => forall (r : T D),  lt D r p' -> FirstOrder_Denote f (AddModelUni M r)
    end
  end.

Definition SO_Bound_Check 
  (M : Sigma11Model)
  (n : nat)
  (y : T D)
  (bs : |[n]| -> T D)
  (f : (|[n]| -> T D) -> option (T D)) : Prop :=
forall (ins : |[n]| -> T D) (out : T D),
  f ins = Some out ->
  (forall x : |[n]|, lt D (ins x) (bs x)) /\ lt D out y.

Program Definition AddExiF (newA : nat) (f : (|[newA]| -> T D) -> option (T D)) 
  (e : nat -> forall a : nat, (|[a]| -> T D) -> option (T D)):
  forall i a : nat, (|[a]| -> T D) -> option (T D):=
  fun i a : nat => (
      if i == 0 as b return ((i == 0) = b -> (|[a]| -> T D) -> option (T D))
      then fun _ => (
        if a == newA as b return ((a == newA) = b -> (|[a]| -> T D) -> option (T D))
        then fun _ => f
        else fun _ _ => None
      ) (erefl _)
      else fun _ t => e (i.-1) a t
    ) (erefl _).
Next Obligation. by assert (a = newA);[rewrite <- EEConvert|rewrite H0]. Qed.

Program Definition AddModelExiF (newA : nat) (f : (|[newA]| -> T D) -> option (T D)) (M : Sigma11Model)  :
  Sigma11Model :=
  {| freeV_F := freeV_F M; freeF_S := freeF_S M; exiV_F := exiV_F M; exiF_S := AddExiF newA f (exiF_S M); uniV_F := uniV_F M |}.

Fixpoint SecondOrder_Denote
  {freeV freeF freeFA exiF exiFA}
  (f : @SecondOrderFormula freeV freeF freeFA exiF exiFA)
  (M : Sigma11Model) : Prop :=
  match f with
  | FO f => FirstOrder_Denote f M
  | SOExists y bs f => 
    let y' : option (T D) := Poly_Denote y M in
    let bs' : option (|[length bs]| -> T D) := 
        option_tuple (fun m => Poly_Denote (lnth bs m) M) in
    match y' with
    | None => false
    | Some y' =>
      match bs' with
      | None => false
      | Some bs' =>
        exists a : (|[length bs]| -> T D) -> option (T D),
          SO_Bound_Check M (length bs) y' bs' a 
          /\ SecondOrder_Denote f (AddModelExiF (length bs) a M)
      end
    end
  end.

End Sigma_1_1_Denotation.
