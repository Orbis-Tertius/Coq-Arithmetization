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
    let g' := fun x : |[d.+1]| => (if x == 0 as b return (x == 0) = b -> nat then fun _ => newA else fun _ => g (x.-1)) (erefl _) in
    {| freeV := a; freeF := b; freeFA := f; exiV := c; exiF := d.+1; exiFA := g'; uniV := e |}
  end.
Next Obligation.
  apply EEFConvert in e0; simpl in e0.
  by destruct x.
Qed.

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

Fixpoint Poly_Denote {ctx} (M : @Sigma11Model ctx) (r : @PolyTerm ctx) : option (R M) :=
  match r with
  | PolyFVar m => Some (freeV_F M m)
  | PolyEVar m => Some (exiV_F M m)
  | PolyUVar m => Some (uniV_F M m)
  | PolyFFun i t => 
    obind (fun t => freeF_S M i t) (option_tuple (fun x => Poly_Denote M (t x)))
  | PolyEFun i t => 
    obind (fun t => exiF_S M i t) (option_tuple (fun x => Poly_Denote M (t x)))
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
    let d1 := Poly_Denote M r1 in
    let d2 := Poly_Denote M r2 in
    (obind (fun r1 => obind (fun r2 => 
      match lt_total (D M) r1 r2 with
      | inl _ => Some 1%R
      | inr _ => Some 0%R
      end) d2) d1)
  end.

Fixpoint ZerothOrder_Denote {ctx} (M : @Sigma11Model ctx) (f : @ZerothOrderFormula ctx) : Prop :=
  match f with
  (* | ZOTrue => true
  | ZOFalse => false *)
  | ZONot f => not (ZerothOrder_Denote M f)
  | ZOAnd f1 f2 => (ZerothOrder_Denote M f1) /\ (ZerothOrder_Denote M f2)
  | ZOOr f1 f2 => (ZerothOrder_Denote M f1) \/ (ZerothOrder_Denote M f2)
  | ZOImp f1 f2 => (ZerothOrder_Denote M f1) -> (ZerothOrder_Denote M f2)
  | ZOEq r1 r2 => 
    match Poly_Denote M r1 with
    | None => false
    | Some r1 =>
      match Poly_Denote M r2 with
      | None => false
      | Some r2 => r1 = r2
      end
    end
  end.

Program Definition AddModelExi {ctx} (M : @Sigma11Model ctx) (r : R M) : @Sigma11Model (incExiV ctx) :=
  let d' := fun x : |[exiV (incExiV ctx)]| => (
      if x == 0 as b return ((x == 0) = b -> R M)
      then fun _ => r
      else fun _ => exiV_F M (x.-1)
    ) (erefl _) 
  in {| D := D M; freeV_F := freeV_F M; freeF_S := freeF_S M; exiV_F := d'; exiF_S := exiF_S M; uniV_F := uniV_F M |}.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  destruct ctx; simpl in *.
  assert ((x == 0) = false);[auto|clear e].
  by destruct x;[fcrush|].
Qed.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. 
  destruct ctx; simpl in *.
  remember (AddModelExi_obligation_4 _ _ _ _) as A; clear HeqA.
  simpl in A.
  replace A with H0 in H;[auto|apply eq_irrelevance].
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation. 
  destruct ctx; simpl in *.
  remember (AddModelExi_obligation_6 _ _ _ _) as A; clear HeqA.
  simpl in A.
  replace A with H0 in H;[auto|apply eq_irrelevance].
Qed.
Next Obligation. by destruct ctx. Qed.

Program Definition AddModelUni {ctx} (M : @Sigma11Model ctx) (r : R M) : @Sigma11Model (incUniV ctx) :=
  let d' := fun x : |[uniV (incUniV ctx)]|=> (
      if x == 0 as b return ((x == 0) = b -> R M)
      then fun _ => r
      else fun _ => uniV_F M (x.-1)
    ) (erefl _) 
  in {| D := D M; freeV_F := freeV_F M; freeF_S := freeF_S M; exiV_F := exiV_F M; exiF_S := exiF_S M; uniV_F := d' |}.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  destruct ctx; simpl in *.
  assert ((x == 0) = false);[auto|clear e].
  by destruct x;[fcrush|].
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation. 
  destruct ctx; simpl in *.
  remember (AddModelUni_obligation_3 _ _ _ _) as A; clear HeqA.
  simpl in A.
  replace A with H0 in H;[auto|apply eq_irrelevance].
Qed.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. 
  destruct ctx; simpl in *.
  remember (AddModelUni_obligation_6 _ _ _ _) as A; clear HeqA.
  simpl in A.
  replace A with H0 in H;[auto|apply eq_irrelevance].
Qed.
Next Obligation. by destruct ctx. Qed. 

Fixpoint FirstOrder_Denote {ctx} (M : @Sigma11Model ctx) (f : @FirstOrderFormula ctx) : Prop :=
  match f with
  | ZO z => ZerothOrder_Denote M z
  | FOExists p f => 
    let op := Poly_Denote M p in
    match op with
    | None => False
    | Some p' => exists (r : R M), lt (D M) r p' /\ FirstOrder_Denote (AddModelExi M r) f
    end
  | FOForall p f =>
    let op := Poly_Denote M p in
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

Program Definition AddModelExiF {ctx} (M : @Sigma11Model ctx) (newA : nat) (f : (|[newA]| -> R M) -> option (R M)) : 
  @Sigma11Model (addExiF newA ctx) :=
  let d' := fun x : |[exiF (addExiF newA ctx)]| => (
      if x == 0 as b return ((x == 0) = b -> (|[exiFA (addExiF newA ctx) x]| -> R M) -> option (R M))
      then fun _ => f
      else fun _ t => exiF_S M (x.-1) t
    ) (erefl _) 
  in {| D := D M; freeV_F := freeV_F M; freeF_S := freeF_S M; exiV_F := exiV_F M; exiF_S := d'; uniV_F := uniV_F M |}.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx, x. Qed.
Next Obligation. 
  destruct ctx; simpl in *.
  rewrite dep_if_case_false.
  remember (AddModelExiF_obligation_2 _ _ _ _ _ _ _) as A; clear HeqA; simpl in A.
  remember (addExiF_obligation_2 _ _ _) as B; clear HeqB; simpl in B.
  replace B with A;[auto|apply eq_irrelevance].
Qed.
Next Obligation. 
  destruct ctx; simpl in *.
  rewrite dep_if_case_true; auto.
Qed.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation. 
  destruct ctx; simpl in *.
  remember (AddModelExiF_obligation_7 _ _ _ _ _) as A; clear HeqA.
  simpl in A.
  replace A with H0 in H;[auto|apply eq_irrelevance].
Qed.
Next Obligation. by destruct ctx. Qed.

Fixpoint SecondOrder_Denote {ctx} (M : @Sigma11Model ctx) (f : @SecondOrderFormula ctx) : Prop :=
  match f with
  | FO f => FirstOrder_Denote M f
  | SOExists y bs f => 
    let y' : option (R M) := Poly_Denote M y in
    let bs' : option (|[length bs]| -> R M) := 
        option_tuple (fun m => Poly_Denote M (lnth bs m)) in
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
