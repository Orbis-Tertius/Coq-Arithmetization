From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import Program.

Section Sigma_1_1_Internal.

Record Sigma11Ctx := mkSigma11Ctx
  { freeV : nat
  ; freeF : nat
  ; freeFA : |[freeF]| -> nat
  ; exiV : nat
  ; exiF : nat
  ; exiFA : |[exiF]| -> nat
  ; uniV : nat
  }.
Definition incExiV (ctx : Sigma11Ctx) : Sigma11Ctx := 
  match ctx with
  | {| freeV := a; freeF := b; freeFA := f; exiV := c;    exiF := d; exiFA := g; uniV := e |} =>
    {| freeV := a; freeF := b; freeFA := f; exiV := c.+1; exiF := d; exiFA := g; uniV := e |}
  end.
Definition incUniV (ctx : Sigma11Ctx) : Sigma11Ctx := 
  match ctx with
  | {| freeV := a; freeF := b; freeFA := f; exiV := c; exiF := d; exiFA := g; uniV := e |} =>
    {| freeV := a; freeF := b; freeFA := f; exiV := c; exiF := d; exiFA := g; uniV := e.+1 |}
  end.
Definition addExiF (newA : nat) (ctx : Sigma11Ctx) : Sigma11Ctx := 
  match ctx with
  | {| freeV := a; freeF := b; freeFA := f; exiV := c; exiF := d; exiFA := g; uniV := e |} =>
    {| freeV := a; freeF := b; freeFA := f; exiV := c; exiF := d.+1; exiFA := ExtendAt0N newA g; uniV := e |}
  end.

Inductive PolyTerm {ctx : Sigma11Ctx} : Type :=
| PolyFVar : |[freeV ctx]| -> PolyTerm
| PolyEVar : |[exiV ctx]| -> PolyTerm
| PolyUVar : |[uniV ctx]| -> PolyTerm
| PolyFFun : forall (i : |[freeF ctx]|), (|[freeFA ctx i]| -> PolyTerm) -> PolyTerm
| PolyEFun : forall (i : |[exiF ctx]|), (|[exiFA ctx i]| -> PolyTerm) -> PolyTerm
| PolyMinusOne : PolyTerm
| PolyPlusOne : PolyTerm
| PolyZero : PolyTerm
| PolyPlus : PolyTerm -> PolyTerm -> PolyTerm
| PolyTimes : PolyTerm -> PolyTerm -> PolyTerm
| PolyInd : PolyTerm -> PolyTerm -> PolyTerm.

Inductive ZerothOrderFormula {ctx : Sigma11Ctx} : Type :=
(* | ZOTrue : ZerothOrderFormula
| ZOFalse : ZerothOrderFormula *)
| ZONot : ZerothOrderFormula -> ZerothOrderFormula
| ZOAnd : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOOr : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOImp : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOEq : @PolyTerm ctx -> @PolyTerm ctx -> ZerothOrderFormula.

Inductive FirstOrderFormula {ctx : Sigma11Ctx} : Type :=
| ZO : @ZerothOrderFormula ctx -> FirstOrderFormula
| FOExists : @PolyTerm ctx -> FirstOrderFormula (ctx := incExiV ctx) -> FirstOrderFormula
| FOForall : @PolyTerm ctx -> FirstOrderFormula (ctx := incUniV ctx) -> FirstOrderFormula.

Inductive SecondOrderFormula {ctx : Sigma11Ctx} : Type :=
| FO : @FirstOrderFormula ctx -> SecondOrderFormula
| SOExists : forall (y : @PolyTerm ctx) (bs : seq (@PolyTerm ctx)), 
             SecondOrderFormula (ctx := addExiF (length bs) ctx) ->
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

Fixpoint Poly_Denote {ctx} (r : @PolyTerm ctx) (M : Sigma11Model) : option (T D) :=
  match r with
  | PolyFVar m => Some (freeV_F M (` m))
  | PolyEVar m => Some (exiV_F M (` m))
  | PolyUVar m => Some (uniV_F M (` m))
  | PolyFFun i t => 
    obind (fun t => freeF_S M (` i) (freeFA ctx i) t) (option_tuple (fun x => Poly_Denote (t x) M))
  | PolyEFun i t => 
    obind (fun t => exiF_S M (` i) (exiFA ctx i) t) (option_tuple (fun x => Poly_Denote (t x) M))
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
    let d1 := Poly_Denote r1 M in
    let d2 := Poly_Denote r2 M in
    (obind (fun r1 => obind (fun r2 => 
      match lt_total D r1 r2 with
      | inl _ => Some 1%R
      | inr _ => Some 0%R
      end) d2) d1)
  end.

Fixpoint ZerothOrder_Denote {ctx} (f : @ZerothOrderFormula ctx)  (M : Sigma11Model) : Prop :=
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

Fixpoint FirstOrder_Denote {ctx} (f : @FirstOrderFormula ctx) (M : Sigma11Model) : Prop :=
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

Fixpoint SecondOrder_Denote {ctx} (f : @SecondOrderFormula ctx) (M : Sigma11Model) : Prop :=
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
        exists a : ({m : nat | m < length bs} -> T D) -> option (T D),
          SO_Bound_Check M (length bs) y' bs' a 
          /\ SecondOrder_Denote f (AddModelExiF (length bs) a M)
      end
    end
  end.

End Sigma_1_1_Denotation.
