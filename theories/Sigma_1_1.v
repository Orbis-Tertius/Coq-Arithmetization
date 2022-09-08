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
Program Definition addExiF (newA : nat) (ctx : Sigma11Ctx) : Sigma11Ctx := 
  match ctx with
  | {| freeV := a; freeF := b; freeFA := f; exiV := c; exiF := d; exiFA := g; uniV := e |} =>
    let g' := fun x : |[d.+1]| => (if x == d as b return (x == d) = b -> nat then fun _ => newA else fun _ => g x) (erefl _) in
    {| freeV := a; freeF := b; freeFA := f; exiV := c; exiF := d.+1; exiFA := g'; uniV := e |}
  end.
Next Obligation.
  apply EEFConvert in e0; simpl in e0.
  by apply leq_neq_lt.
Qed.

Inductive RingTerm {ctx : Sigma11Ctx} : Type :=
| RingFVar : |[freeV ctx]| -> RingTerm
| RingEVar : |[exiV ctx]| -> RingTerm
| RingUVar : |[uniV ctx]| -> RingTerm
| RingFFun : forall (i : |[freeF ctx]|), (|[freeFA ctx i]| -> RingTerm) -> RingTerm
| RingEFun : forall (i : |[exiF ctx]|), (|[exiFA ctx i]| -> RingTerm) -> RingTerm
| RingMinusOne : RingTerm
| RingPlusOne : RingTerm
| RingZero : RingTerm
| RingPlus : RingTerm -> RingTerm -> RingTerm
| RingTimes : RingTerm -> RingTerm -> RingTerm
| RingInd : RingTerm -> RingTerm -> RingTerm.

Inductive ZerothOrderFormula {ctx : Sigma11Ctx} : Type :=
| ZOTrue : ZerothOrderFormula
| ZOFalse : ZerothOrderFormula
| ZONot : ZerothOrderFormula -> ZerothOrderFormula
| ZOAnd : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOOr : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOImp : ZerothOrderFormula -> ZerothOrderFormula -> ZerothOrderFormula
| ZOEq : @RingTerm ctx -> @RingTerm ctx -> ZerothOrderFormula.

Inductive FirstOrderFormula {ctx : Sigma11Ctx} : Type :=
| ZO : @ZerothOrderFormula ctx -> FirstOrderFormula
| FOExists : @RingTerm ctx -> FirstOrderFormula (ctx := incExiV ctx) -> FirstOrderFormula
| FOForall : @RingTerm ctx -> FirstOrderFormula (ctx := incUniV ctx) -> FirstOrderFormula.

Inductive SecondOrderFormula {ctx : Sigma11Ctx} : Type :=
| FO : @FirstOrderFormula ctx -> SecondOrderFormula
| SOExists : forall (y : @RingTerm ctx) (bs : seq (@RingTerm ctx)), 
             SecondOrderFormula (ctx := addExiF (length bs) ctx) ->
             SecondOrderFormula.

End Sigma_1_1_Internal.



Section Sigma_1_1_Denotation.

Program Fixpoint option_tuple {A} {l : nat} (t : |[l]| -> option A) : option (|[l]| -> A) := 
  match l with
  | 0 => Some emptyTuple
  | m.+1 =>
    let most : |[m]| -> option A := fun x => t x in
    let r : option (|[m]| -> A) := option_tuple most in
    let last : option A := t m in
    obind (fun last => obind (fun r => Some (
      fun x : {n : nat | n < m.+1} => 
      (if x < m as b return x < m = b -> A 
       then (fun _ => r (x : |[m]|) )
       else (fun _ => last)) (erefl _)
    )) r) last
  end.

Record RingData : Type :=
  mkRingData {
    T : ringType;
    (*lt should be a strict, total order with a least element*)
    lt : relation T;
    so : StrictOrder lt;
    lt_total : forall x y, (lt x y) + ((x==y) + (lt y x));
    lt_dec x y :=
      match lt_total x y with
      | inl _ => true
      | inr _ => false
      end;
    min : T;
    least_elem : forall x, lt min x;
  }.

Record Sigma11Model {ctx : Sigma11Ctx} : Type :=
  mkSigma11Model {
      D : RingData;
      R : ringType := T D;
      freeV_F : |[freeV ctx]| -> R;
      freeF_S : forall i : |[freeF ctx]|, (|[freeFA ctx i]| -> R) -> option R;
      exiV_F : |[exiV ctx]| -> R;
      exiF_S : forall i : |[exiF ctx]|, (|[exiFA ctx i]| -> R) -> option R;
      uniV_F : |[uniV ctx]| -> R;
    }.

Fixpoint Ring_Denote {ctx} (M : @Sigma11Model ctx) (r : @RingTerm ctx) : option (R M) :=
  match r with
  | RingFVar m => Some (freeV_F M m)
  | RingEVar m => Some (exiV_F M m)
  | RingUVar m => Some (uniV_F M m)
  | RingFFun i t => 
    obind (fun t => freeF_S M i t) (option_tuple (fun x => Ring_Denote M (t x)))
  | RingEFun i t => 
    obind (fun t => exiF_S M i t) (option_tuple (fun x => Ring_Denote M (t x)))
  | RingMinusOne => Some (-1)%R
  | RingPlusOne => Some 1%R
  | RingZero => Some 0%R
  | RingPlus r1 r2 => 
    let d1 := Ring_Denote M r1 in
    let d2 := Ring_Denote M r2 in
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) d2) d1
  | RingTimes r1 r2 => 
    let d1 := Ring_Denote M r1 in
    let d2 := Ring_Denote M r2 in
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) d2) d1
  | RingInd r1 r2 => 
    let d1 := Ring_Denote M r1 in
    let d2 := Ring_Denote M r2 in
    (obind (fun r1 => obind (fun r2 => 
      match lt_total (D M) r1 r2 with
      | inl _ => Some 1%R
      | inr _ => Some 0%R
      end) d2) d1)
  end.

Fixpoint ZerothOrder_Denote {ctx} (M : @Sigma11Model ctx) (f : @ZerothOrderFormula ctx) : Prop :=
  match f with
  | ZOTrue => true
  | ZOFalse => false
  | ZONot f => not (ZerothOrder_Denote M f)
  | ZOAnd f1 f2 => (ZerothOrder_Denote M f1) /\ (ZerothOrder_Denote M f2)
  | ZOOr f1 f2 => (ZerothOrder_Denote M f1) \/ (ZerothOrder_Denote M f2)
  | ZOImp f1 f2 => (ZerothOrder_Denote M f1) -> (ZerothOrder_Denote M f2)
  | ZOEq r1 r2 => 
    match Ring_Denote M r1 with
    | None => false
    | Some r1 =>
      match Ring_Denote M r2 with
      | None => false
      | Some r2 => r1 = r2
      end
    end
  end.

Definition AddModelExi {ctx} (M : @Sigma11Model ctx) (r : R M) : @Sigma11Model (incExiV ctx).
  destruct M.
  unfold R in r; simpl in r.
  assert (freeV_F' : |[freeV (incExiV ctx)]| -> R0).
  destruct ctx; exact freeV_F0.
  assert (uniV_F' : |[uniV (incExiV ctx)]| -> R0).
  destruct ctx; exact uniV_F0.
  assert (freeF_S' : forall i : |[freeF (incExiV ctx)]|, (|[freeFA (incExiV ctx) i]| -> R0) -> option R0).
  destruct ctx; exact freeF_S0.
  assert (exiF_S' : forall i : |[exiF (incExiV ctx)]|, (|[exiFA (incExiV ctx) i]| -> R0) -> option R0).
  destruct ctx; exact exiF_S0.
  assert (exiV_F' : |[exiV (incExiV ctx)]| -> R0).
  destruct ctx; simpl in *.
  move=> [x lt].
  destruct (x == exiV0) eqn:b.
  exact r.
  apply EEFConvert in b.
  assert (x < exiV0);[by apply leq_neq_lt|].
  exact (exiV_F0 (exist _ x H)).
  exact {| D := D0; freeV_F := freeV_F'; freeF_S := freeF_S'; exiV_F := exiV_F'; exiF_S := exiF_S'; uniV_F := uniV_F' |}.
Qed.

(*How to make this work???*)
(* Program Definition AddModelExi {ctx} (M : @Sigma11Model ctx) (r : R M) : @Sigma11Model (incExiV ctx) :=
  match M with
  | {| D := a; freeV_F := b; freeF_S := c; exiV_F := d; exiF_S := e; uniV_F := f |} =>
    let d' : |[exiV (incExiV ctx)]| -> R := fun x => (
      if x == d as b return ((x == d) = b -> R)
      then r
      else exiV_F x
    ) (erefl _) in
    {| D := a; freeV_F := b; freeF_S := c; exiV_F := d'; exiF_S := e; uniV_F := f |}
  end.   *)

Definition AddModelUni {ctx} (M : @Sigma11Model ctx) (r : R M) : @Sigma11Model (incUniV ctx).
  destruct M.
  unfold R in r; simpl in r.
  assert (freeV_F' : |[freeV (incUniV ctx)]| -> R0).
  destruct ctx; exact freeV_F0.
  assert (exiV_F' : |[exiV (incUniV ctx)]| -> R0).
  destruct ctx; exact exiV_F0.
  assert (freeF_S' : forall i : |[freeF (incUniV ctx)]|, (|[freeFA (incUniV ctx) i]| -> R0) -> option R0).
  destruct ctx; exact freeF_S0.
  assert (exiF_S' : forall i : |[exiF (incUniV ctx)]|, (|[exiFA (incUniV ctx) i]| -> R0) -> option R0).
  destruct ctx; exact exiF_S0.
  assert (uniV_F' : |[uniV (incUniV ctx)]| -> R0).
  destruct ctx; simpl in *.
  move=> [x lt].
  destruct (x == uniV0) eqn:b.
  exact r.
  apply EEFConvert in b.
  assert (x < uniV0);[by apply leq_neq_lt|].
  exact (uniV_F0 (exist _ x H)).
  exact {| D := D0; freeV_F := freeV_F'; freeF_S := freeF_S'; exiV_F := exiV_F'; exiF_S := exiF_S'; uniV_F := uniV_F' |}.
Qed.

Fixpoint FirstOrder_Denote {ctx} (M : @Sigma11Model ctx) (f : @FirstOrderFormula ctx) : Prop :=
  match f with
  | ZO z => ZerothOrder_Denote M z
  | FOExists p f => 
    let op := Ring_Denote M p in
    match op with
    | None => False
    | Some p' => exists (r : R M), lt (D M) r p' /\ FirstOrder_Denote (AddModelExi M r) f
    end
  | FOForall p f =>
    let op := Ring_Denote M p in
    match op with
    | None => False
    | Some p' => forall (r : R M),  lt (D M) r p' -> FirstOrder_Denote (AddModelUni M r) f
    end
  end.

Definition SO_Bound_Check {ctx} (M : @Sigma11Model ctx) 
  (n : nat)
  (y : R M)
  (bs : |[n]| -> R M)
  (f : (|[n]| -> R M) -> option (R M)) : Prop :=
forall (ins : |[n]| -> R M) (out : R M),
  f ins = Some out ->
  (forall x : |[n]|, lt (D M) (ins x) (bs x)) /\ lt (D M) out y.

Definition AddModelExiF {ctx} (M : @Sigma11Model ctx) (newA : nat) (f : (|[newA]| -> R M) -> option (R M)) : 
  @Sigma11Model (addExiF newA ctx).
  destruct M.
  unfold R in f; simpl in f.
  assert (freeV_F' : |[freeV (addExiF newA ctx)]| -> R0).
  destruct ctx; exact freeV_F0.
  assert (exiV_F' : |[exiV (addExiF newA ctx)]| -> R0).
  destruct ctx; exact exiV_F0.
  assert (uniV_F' : |[uniV (addExiF newA ctx)]| -> R0).
  destruct ctx; exact uniV_F0.
  assert (freeF_S' : forall i : |[freeF (addExiF newA ctx)]|, (|[freeFA (addExiF newA ctx) i]| -> R0) -> option R0).
  destruct ctx; exact freeF_S0.
  assert (exiF_S' : forall i : |[exiF (addExiF newA ctx)]|, (|[exiFA (addExiF newA ctx) i]| -> R0) -> option R0).
  destruct ctx; simpl in *.
  move=> [i lti].
  destruct (i == exiF0) eqn:b.
  - rewrite dep_if_case_true;[auto|].
    exact f.
  - rewrite dep_if_case_false.
    move=> t.
    apply: exiF_S0.
    exact t.
  exact {| D := D0; freeV_F := freeV_F'; freeF_S := freeF_S'; exiV_F := exiV_F'; exiF_S := exiF_S'; uniV_F := uniV_F' |}.
Qed.

Fixpoint SecondOrder_Denote {ctx} (M : @Sigma11Model ctx) (f : @SecondOrderFormula ctx) : Prop :=
  match f with
  | FO f => FirstOrder_Denote M f
  | SOExists y bs f => 
    let y' : option (R M) := Ring_Denote M y in
    let bs' : option (|[length bs]| -> R M) := 
        option_tuple (fun m => Ring_Denote M (lnth bs m)) in
    match y' with
    | None => false
    | Some y' =>
      match bs' with
      | None => false
      | Some bs' =>
        exists a : ({m : nat | m < length bs} -> R M) -> option (R M),
          SO_Bound_Check M (length bs) y' bs' a 
          /\ SecondOrder_Denote (AddModelExiF M (length bs) a) f
      end
    end
  end.

End Sigma_1_1_Denotation.
