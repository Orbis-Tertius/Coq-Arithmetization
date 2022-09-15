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

Fixpoint ConstraintEq {ctx} {d1 d2 : @PolyConversionData ctx}
  (p1 : @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d1; exiFC := newExiFCalls d1; indC := newIndCalls d1 |})
  (p2 : @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d2; exiFC := newExiFCalls d2; indC := newIndCalls d2 |}) : Prop :=
  match p1, p2 with
  | PolyConsZero, PolyConsZero => true
  | PolyConsPlusOne, PolyConsPlusOne => true
  | PolyConsMinusOne, PolyConsMinusOne => true
  | PolyConsPlus p11 p12, PolyConsPlus p21 p22 => ConstraintEq p11 p21 /\ ConstraintEq p12 p22
  | PolyConsTimes p11 p12, PolyConsTimes p21 p22 => ConstraintEq p11 p21 /\ ConstraintEq p12 p22
  | PolyConsInd i, PolyConsInd j => ` i = ` j
  | PolyConsExiV i, PolyConsExiV j => ` i = ` j
  | PolyConsUniV i, PolyConsUniV j => ` i = ` j
  | PolyConsFreeF i1 j1, PolyConsFreeF i2 j2 => ` i1 = ` i2 /\ ` j1 = ` j2
  | PolyConsExiF i1 j1, PolyConsFreeF i2 j2 => ` i1 = ` i2 /\ ` j1 = ` j2 
  | _, _ => false
  end.




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

Theorem dep_prod_split {A} {B} (p : { n : A & B n }) : p = existT _ (projT1 p) (projT2 p).
Proof. by destruct p. Qed.

Theorem dep_let_split {A C} {B} (p : { n : A & B n }) (f : forall n, B n -> C) :
  (let (x, y) := p in f x y) = f (projT1 p) (projT2 p).
Proof. by destruct p. Qed.

Theorem PolyConvertCorrect {D : RingData} {ctx} (r : @PolyTerm ctx) 
  (inst : SemiCircuitInstance D {| subCtx := ctx
                                 ; freeFC := newFreeFCalls (projT1 (PolyConvert r))
                                 ; exiFC := newExiFCalls (projT1 (PolyConvert r))
                                 ; indC := newIndCalls (projT1 (PolyConvert r)) |})
  (adv : SemiCircuitAdvice D {| subCtx := ctx
                              ; freeFC := newFreeFCalls (projT1 (PolyConvert r))
                              ; exiFC := newExiFCalls (projT1 (PolyConvert r))
                              ; indC := newIndCalls (projT1 (PolyConvert r)) |}) :
  forall u, Poly_Denote (SemiData_to_Sigma11Model inst adv u) r
          = Some (PolyConvertDenotation D (PolyConvert r) inst adv u).
Proof.
  move: adv inst; elim: r; auto.
  move=> i p IH adv inst u.
  simpl.
  unfold freeFInst.
  unfold PolyConvertFreeCase.
  unfold freeFC.
  unfold PolyConvertDenotation.
  simpl.
  unfold freeFCallOut.


  destruct adv.
  (exist _
        (newFreeFCalls
           (projT1 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])) i)
        (SemiCircuitTranslation.PolyConvertFreeCase_obligation_2 ctx i
           (fun x : {n : nat | n < freeFA ctx i} => PolyConvert (p x))))
  destruct (PolyCallSeqFuse _).
  remember (SemiCircuitTranslation.PolyConvertFreeCase_obligation_2 ctx i
              (fun x : {n : nat | n < freeFA ctx i} => PolyConvert (p x))) as Y0; clear HeqY0.
  simpl in Y0.

(PolyConvertDenotation D
     (existT (fun d : PolyConversionData => SemicircuitPolyConstraint)
        (FreeCallIncorp
           (projT1 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])) i
           (` (projT2 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])))
           (SemiCircuitTranslation.PolyConvertFreeCase_obligation_1 ctx i
              (fun x : {n : nat | n < freeFA ctx i} => PolyConvert (p x))))
        (PolyConsFreeF i
           (exist _
              (newFreeFCalls
                 (projT1 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])) i)
              Y0))) inst adv u)









  destruct ctx; simpl.
  remember (SemiCircuitTranslation.PolyConvertFreeCase_obligation_1 _ _ _) as Y1; clear HeqY1.
  destruct (PolyCallSeqFuse _).
  remember (SemiCircuitTranslation.PolyConvertFreeCase_obligation_1 _ _ _) as Y1; clear HeqY1.
  destruct (PolyCallSeqFuse _).
  destruct polys.
  transitivity (Some
  (PolyConvertDenotation D
     (
      existT (fun d : PolyConversionData => SemicircuitPolyConstraint)
        (FreeCallIncorp (projT1 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])) i (` (projT2 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])))
           (SemiCircuitTranslation.PolyConvertFreeCase_obligation_1 ctx i
              (fun x : {n : nat | n < freeFA ctx i} => PolyConvert (p x)) (projT1 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])) (projT2 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)]))))
        (PolyConsFreeF (ctx := {|
                            subCtx := ctx;
                            freeFC :=
                              @newFreeFCalls ctx
                                (@FreeCallIncorp ctx (projT1 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])) i (` (projT2 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])))
                                   (SemiCircuitTranslation.PolyConvertFreeCase_obligation_1 ctx i
                                      (fun x0 : {n : nat | n < freeFA ctx i} =>
                                       @PolyConvert ctx (p x0)) (projT1 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])) (projT2 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)]))));
                            exiFC :=
                              @newExiFCalls ctx
                                (@FreeCallIncorp ctx (projT1 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])) i (` (projT2 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])))
                                   (SemiCircuitTranslation.PolyConvertFreeCase_obligation_1 ctx i
                                      (fun x0 : {n : nat | n < freeFA ctx i} =>
                                       @PolyConvert ctx (p x0)) (projT1 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])) (projT2 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)]))));
                            indC :=
                              @newIndCalls ctx
                                (@FreeCallIncorp ctx (projT1 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])) i (` (projT2 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])))
                                   (SemiCircuitTranslation.PolyConvertFreeCase_obligation_1 ctx i
                                      (fun x0 : {n : nat | n < freeFA ctx i} =>
                                       @PolyConvert ctx (p x0)) (projT1 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])) (projT2 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)]))))
                          |}) i
           (exist
              _
              (newFreeFCalls (projT1 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])) i)
              (SemiCircuitTranslation.PolyConvertFreeCase_obligation_2 ctx i
                 (fun x : {n : nat | n < freeFA ctx i} => PolyConvert (p x)) (projT1 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])) (projT2 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])))))) inst adv
     u)
).

  remember (Some _) as RHS.
  destruct RHS;[|fcrush].
  injection HeqRHS;move=> RHS2; clear HeqRHS.
  remember (SemiCircuitTranslation.PolyConvertFreeCase_obligation_1 ctx i
                           (fun x : {n0 : nat | n0 < freeFA ctx i} => PolyConvert (p x))) as DDD. 
  rewrite dep_let_split in RHS2.
  remember (let (data, polys) := PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)] in
      existT (fun d : PolyConversionData => SemicircuitPolyConstraint)
        (FreeCallIncorp data i (` polys)
           (SemiCircuitTranslation.PolyConvertFreeCase_obligation_1 ctx i
              (fun x : {n : nat | n < freeFA ctx i} => PolyConvert (p x)) data polys))
        (PolyConsFreeF _
           _)) as DD.

  destruct (PolyCallSeqFuse [seq PolyConvert (p i) | i <- cRange 0 (freeFA ctx i)]) in HeqRHS.

  cbn in HeqRHS.
  transitivity RHS.
  2:{
  Set Printing Implicit.
  Check PolyConsFreeF.


  assert (length (` (projT2 (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)]))) = freeFA ctx i).
  destruct (projT2 _).
  simpl.
  rewrite e; clear e.
  by rewrite map_length (length_cRange (n := 0)).
  Check (SemiCircuitTranslation.PolyConvertFreeCase_obligation_2 ctx i
                 (fun x : {n : nat | n < freeFA ctx i} => PolyConvert (p x)) ).
  rewrite dep_let_split.

  rewrite (dep_prod_split (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)])).
  Search (_ = (projT1 _, _)).

  assert (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)] =
          (projT1) )
  remember (FreeCallIncorp data i _ _) as D0; clear HeqD0.
  remember (SemiCircuitTranslation.PolyConvertFreeCase_obligation_2 _ _ _) as D0; clear HeqD0.
  remember (SemiCircuitTranslation.PolyConvertFreeCase_obligation_1 _ _ _) as D0; clear HeqD0.
  destruct (PolyCallSeqFuse [seq PolyConvert (p i0) | i0 <- cRange 0 (freeFA ctx i)]).

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
