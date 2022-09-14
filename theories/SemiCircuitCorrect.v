From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.
Require Import Program.

Require Import CoqArith.Sigma_1_1.
Require Import CoqArith.SemiCircuit.
Require Import CoqArith.SemiCircuitTranslation.

Section SemicircuitCorrect.

Definition Hole {A} : A. Admitted.

Definition PolyConvertDenotation (D : RingData) {ctx}
  (o : { d : @PolyConversionData ctx &
    @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d; indC := newIndCalls d |}})
  (inst : SemiCircuitInstance D {| subCtx := ctx; freeFC := newFreeFCalls (projT1 o); exiFC := newExiFCalls (projT1 o); indC := newIndCalls (projT1 o) |})
  (adv : SemiCircuitAdvice D {| subCtx := ctx; freeFC := newFreeFCalls (projT1 o); exiFC := newExiFCalls (projT1 o); indC := newIndCalls (projT1 o) |}) :
  (|[uniV ctx]| -> T D) -> T D := SemicircuitPolyDenotation D _ inst adv (projT2 o).

Definition SemiData_to_Sigma11Model {D : RingData} {ctx}
  (inst : SemiCircuitInstance D ctx)
  (adv : SemiCircuitAdvice D ctx) 
  (u : (|[uniVS ctx]| -> T D)) :
  @Sigma11Model (subCtx ctx) :=
  {| D := D
   ; freeV_F := freeVInst D _ inst
   ; freeF_S := freeFInst D _ inst
   ; exiV_F := fun x => exiVAdv D _ adv x u
   ; exiF_S := exiFAdv D _ adv
   ; uniV_F := u
  |}.


Theorem PolyConvertCorrect {D : RingData} {ctx} (r : @PolyTerm ctx) 
  (inst : SemiCircuitInstance D {| subCtx := ctx; freeFC := newFreeFCalls (projT1 (PolyConvert r)); exiFC := newExiFCalls (projT1 (PolyConvert r)); indC := newIndCalls (projT1 (PolyConvert r)) |})
  (adv : SemiCircuitAdvice D {| subCtx := ctx; freeFC := newFreeFCalls (projT1 (PolyConvert r)); exiFC := newExiFCalls (projT1 (PolyConvert r)); indC := newIndCalls (projT1 (PolyConvert r)) |}) :
  forall u, Poly_Denote (SemiData_to_Sigma11Model inst adv u) r
          = Some (PolyConvertDenotation D (PolyConvert r) inst adv u).
Proof.
  move: adv inst; elim: r; auto.
  move=> i p IH adv inst u.
  simpl.
  unfold freeFInst.
  transitivity (Poly_Denote (SemiData_to_Sigma11Model inst adv u) (p s)).
  replace (PolyConvertFreeCase i (fun x => PolyConvert (p x)))
    with (fun x => PolyConvert (p i)).
  unfold PolyConvertFreeCase.
  pattern (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)] ).


  assert (forall (s : {n : nat | n < freeFA ctx i}),
                (SemiCircuitAdvice D
                          {|
                            subCtx := ctx;
                            freeFC := newFreeFCalls (projT1 (PolyConvert (p s)));
                            exiFC := newExiFCalls (projT1 (PolyConvert (p s)));
                            indC := newIndCalls (projT1 (PolyConvert (p s)))
                          |})) as adv2.
  destruct adv.
  intro.
  split.
  apply exiVAdv.
  apply exiFAdv.
  unfold freeFS, uniVS, subCtx, freeFC in freeFCallOut.
  unfold freeFS, uniVS, subCtx, freeFC.
  apply freeFCallOut.
  apply exiFCallOut.
  apply indCallOut.


  unfold exiVS, uniVS, subCtx.

  destruct inst, adv.
  replace (fun x : {n : nat | n < freeFA ctx i} =>
      Poly_Denote
        (SemiData_to_Sigma11Model
           {| freeVInst := freeVInst; freeFInst := freeFInst |}
           {|
             exiVAdv := exiVAdv;
             exiFAdv := exiFAdv;
             freeFCallOut := freeFCallOut;
             exiFCallOut := exiFCallOut;
             indCallOut := indCallOut
           |} u) (p x)) with
    (fun x : {n : nat | n < freeFA ctx i} =>
      Some (PolyConvertDenotation D (PolyConvert (p x)) {| freeVInst := freeVInst; freeFInst := freeFInst |} {|
             exiVAdv := exiVAdv;
             exiFAdv := exiFAdv;
             freeFCallOut := freeFCallOut;
             exiFCallOut := exiFCallOut;
             indCallOut := indCallOut
           |}  u)).
  assert (forall (s : {n : nat | n < freeFA ctx i}),
                (SemiCircuitAdvice D
                          {|
                            subCtx := ctx;
                            freeFC := newFreeFCalls (projT1 (PolyConvert (p s)));
                            exiFC := newExiFCalls (projT1 (PolyConvert (p s)));
                            indC := newIndCalls (projT1 (PolyConvert (p s)))
                          |})) as adv2.
  destruct adv.
  intro.
  split.
  unfold exiVS, uniVS, subCtx.

  simpl.


                  inst u => Poly_Denote (SemiData_to_Sigma11Model inst adv u) (p s))
     = (fun s adv inst u => Some (PolyConvertDenotation D (PolyConvert (p s)) inst adv u)))


  assert ((fun (s : {n : nat | n < freeFA ctx i})
                (adv : SemiCircuitAdvice D
                          {|
                            subCtx := ctx;
                            freeFC := newFreeFCalls (projT1 (PolyConvert (p s)));
                            exiFC := newExiFCalls (projT1 (PolyConvert (p s)));
                            indC := newIndCalls (projT1 (PolyConvert (p s)))
                          |})
                  inst u => Poly_Denote (SemiData_to_Sigma11Model inst adv u) (p s))
     = (fun s adv inst u => Some (PolyConvertDenotation D (PolyConvert (p s)) inst adv u))) as IH_FE.
  do 4 (apply functional_extensionality_dep; intro).
  by rewrite IH.
  transitivity (obind [eta (let (_, freeFInst) := inst in freeFInst) i]
  (option_tuple
     ((fun f x => f x adv inst u) (fun x (adv : SemiCircuitAdvice D
                          {|
                            subCtx := ctx;
                            freeFC := newFreeFCalls (projT1 (PolyConvert (p x)));
                            exiFC := newExiFCalls (projT1 (PolyConvert (p x)));
                            indC := newIndCalls (projT1 (PolyConvert (p x)))
                          |}) u => Poly_Denote (SemiData_to_Sigma11Model inst adv u) (p x))))); auto.

  pattern inst.
  rewrite IH_FE.

  apply (functional_extensionality _ (fun s => fun adv inst u => Some (PolyConvertDenotation D (PolyConvert (p s)) inst adv u))).

  apply functional_extensionality.
  do 3 (apply functional_extensionality; intro).
     

  apply functional_extensionality in IH.
  transitivity (obind [eta (let (_, freeFInst) := inst in freeFInst) i]
  (option_tuple
     ((fun f x => f x inst adv u) (fun x inst adv u => Poly_Denote (SemiData_to_Sigma11Model inst adv u) (p x))))); auto.
  remember (fun x : {n : nat | n < freeFA ctx i} =>
    Some (PolyConvertDenotation D (PolyConvert (p x)) inst adv u)) as FD2.
  assert (SemiCircuitInstance D
    {|
      subCtx := ctx;
      freeFC := newFreeFCalls (projT1 (PolyConvert (p x)));
      exiFC := newExiFCalls (projT1 (PolyConvert (p x)));
      indC := newIndCalls (projT1 (PolyConvert (p x)))
    |}) as inst2.
  remember (fun x => Some (PolyConvertDenotation D (PolyConvert (p x)) inst adv u)) as FD2.
  destruct adv, inst; simpl.
  unfold option_tuple.
  remember (fun x => Some (PolyConvertDenotation D (PolyConvert (p x)) inst adv u)) as FD2.
  setoid_rewrite <- IH in FD.


  setoid_rewrite <- IH.
  replace (fun x : {n : nat | n < freeFA ctx i} => Poly_Denote (SemiData_to_Sigma11Model inst adv u) (p x))
    with  (fun x : _ => Some (PolyConvertDenotation D (PolyConvert (p x)) inst adv u)).
  transitivity (Some
  (PolyConvertDenotation D
     (PolyConvertFreeCase i p inst adv
     u))
  destruct adv, inst; cbn.
  unfold PolyConvertFreeCase.
  unfold freeFC.
  remember (PolyCallSeqFuse
          [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)]) as D1.

  unfold PolyConvertDenotation.
  cbn.
  simpl.
  unfold PolyConvertFreeCase.
  move=> u.


  (r : @PolyTerm ctx)

PolyConvert {ctx} (r : @PolyTerm ctx) :
  { d : @PolyConversionData ctx &  
    @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d; indC := newIndCalls d |} }

SemicircuitPolyDenotation




End SemicircuitTranslation.
