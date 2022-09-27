From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import CoqArith.Sigma_1_1_UnFree.
Require Import Program.

Section NoQuantDef.

Variables D : RingData.

Inductive PolyTermVS {exiV exiF uniV} {exiFA : |[exiF]| -> nat} : Type :=
| PolyFVarVS : nat -> PolyTermVS
| PolyEVarVS : |[exiV]| -> PolyTermVS
| PolyUVarVS : |[uniV]| -> PolyTermVS
| PolyFFunVS : forall (i a : nat), (|[a]| -> PolyTermVS) -> PolyTermVS
| PolyEFunVS : forall (i : |[exiF]|), (|[exiFA i]| -> PolyTermVS) -> PolyTermVS
| PolyMinusOneVS : PolyTermVS
| PolyPlusOneVS : PolyTermVS
| PolyZeroVS : PolyTermVS
| PolyPlusVS : PolyTermVS -> PolyTermVS -> PolyTermVS
| PolyTimesVS : PolyTermVS -> PolyTermVS -> PolyTermVS
| PolyIndVS : PolyTermVS -> PolyTermVS -> PolyTermVS.

Inductive ZerothOrderFormulaVS {exiV exiF uniV} {exiFA : |[exiF]| -> nat} : Type :=
| ZONotVS : ZerothOrderFormulaVS -> ZerothOrderFormulaVS
| ZOAndVS : ZerothOrderFormulaVS -> ZerothOrderFormulaVS -> ZerothOrderFormulaVS
| ZOOrVS : ZerothOrderFormulaVS -> ZerothOrderFormulaVS -> ZerothOrderFormulaVS
| ZOImpVS : ZerothOrderFormulaVS -> ZerothOrderFormulaVS -> ZerothOrderFormulaVS
| ZOEqVS : @PolyTermVS exiV exiF uniV exiFA
      -> @PolyTermVS exiV exiF uniV exiFA
      -> ZerothOrderFormulaVS.

Record NoQuant {exiV exiF uniV} {exiFA : |[exiF]| -> nat} : Type :=
  mkNoQuant {
    nu : {s : |[exiV]| -> { m : nat | m <= uniV } | forall i j : |[exiV]|, (` i) <= (` j) -> (` (s i)) <= (` (s j))};
    uniVBounds : |[uniV]| -> @PolyTermVS exiV exiF uniV exiFA;
    exiVBounds : |[exiV]| -> @PolyTermVS exiV exiF uniV exiFA;
    exiFOutputBounds : |[exiF]| -> @PolyTermVS exiV exiF uniV exiFA;
    exiFInputBounds : forall (i : |[exiF]|), |[exiFA i]| -> @PolyTermVS exiV exiF uniV exiFA;
    formula : @ZerothOrderFormulaVS exiV exiF uniV exiFA
  }.

Record NoQuantAdvice {exiV exiF uniV} {exiFA : |[exiF]| -> nat} : Type :=
  mkNoQuantAdvice { 
    exiVAdv : |[exiV]| -> (|[uniV]| -> T D) -> T D;
    exiFAdv : forall i : |[exiF]|, (|[exiFA i]| -> T D) -> option (T D);
  }.

Fixpoint PolyVSDenotation
  {exiV exiF uniV} {exiFA : |[exiF]| -> nat}
  (p : PolyTermVS)
  (M : Sigma11Model D)
  (adv : @NoQuantAdvice exiV exiF uniV exiFA) :
  (|[uniV]| -> T D) -> option (T D) :=
  match p with
  | PolyFVarVS i => fun _ => Some (V_F D M i)
  | PolyEVarVS i => fun u => Some (exiVAdv adv i u)
  | PolyUVarVS i =>  fun u => Some (u i)
  | PolyFFunVS i a t => fun u =>
    obind (fun t => F_S D M i a t) (option_tuple (fun x => PolyVSDenotation (t x) M adv u))
  | PolyEFunVS i t => fun u =>
    obind (fun t => exiFAdv adv i t) (option_tuple (fun x => PolyVSDenotation (t x) M adv u))
  | PolyMinusOneVS => fun _ => Some (-1)%R
  | PolyPlusOneVS => fun _ => Some 1%R
  | PolyZeroVS => fun _ => Some 0%R
  | PolyPlusVS p1 p2 => fun u =>
    let d1 := PolyVSDenotation p1 M adv u in
    let d2 := PolyVSDenotation p2 M adv u in
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) d2) d1
  | PolyTimesVS p1 p2 => fun u =>
    let r1 := PolyVSDenotation p1 M adv u in
    let r2 := PolyVSDenotation p2 M adv u in 
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) r2) r1
  | PolyIndVS p1 p2 => fun u =>
    let r1 := PolyVSDenotation p1 M adv u in
    let r2 := PolyVSDenotation p2 M adv u in 
    obind (fun r1 => obind (fun r2 => Some (indFun D r1 r2)) r2) r1
  end.

Program Fixpoint NoQuantZODenotation
  {exiV exiF uniV} {exiFA : |[exiF]| -> nat}
  (p : ZerothOrderFormulaVS)
  (M : Sigma11Model D)
  (adv : @NoQuantAdvice exiV exiF uniV exiFA) :
  (|[uniV]| -> T D) -> Prop :=
  match p with
  | ZONotVS p => fun u => 
    let r := NoQuantZODenotation p M adv u in
    not r
  | ZOAndVS p1 p2 => fun u => 
    let r1 := NoQuantZODenotation p1 M adv u in
    let r2 := NoQuantZODenotation p2 M adv u in
    r1 /\ r2
  | ZOOrVS p1 p2 => fun u => 
    let r1 := NoQuantZODenotation p1 M adv u in
    let r2 := NoQuantZODenotation p2 M adv u in
    r1 \/ r2
  | ZOImpVS p1 p2 => fun u => 
    let r1 := NoQuantZODenotation p1 M adv u in
    let r2 := NoQuantZODenotation p2 M adv u in
    r1 -> r2
  | ZOEqVS p1 p2 => fun u => 
    let r1 := PolyVSDenotation p1 M adv u in
    let r2 := PolyVSDenotation p2 M adv u in
    match r1 with
    | None => false
    | Some r1 =>
      match r2 with
      | None => false
      | Some r2 => r1 = r2
      end
    end
  end.

Definition InBound 
  {exiV exiF uniV} {exiFA : |[exiF]| -> nat}
  (M : Sigma11Model D) 
  (adv : @NoQuantAdvice exiV exiF uniV exiFA)
  (r : T D)
  (b : @PolyTermVS exiV exiF uniV exiFA) 
  (t : |[uniV]| -> T D) : Prop :=
  match PolyVSDenotation b M adv t with
  | None => False
  | Some e => lt D r e
  end.

Program Definition MakeU {A uniV} {n : {m : nat | m <= uniV}}
  (a : |[n]| -> A) 
  (b : |[uniV - n]| -> A) :
  |[uniV]| -> A := TupConcat a b.
Next Obligation.
  replace (n + (uniV - n)) with uniV; auto.
  sfirstorder use: subnKC.
Qed.

Program Definition U
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (f : @NoQuant exiV exiF uniV exiFA) 
  (M : Sigma11Model D) (adv : NoQuantAdvice) 
  (i : |[exiV]|) : Type 
  := { u : |[nu f i]| -> T D | 
       forall j : |[nu f i]|,
       forall v : |[uniV - nu f i]| -> T D, 
       InBound M adv (u j) (uniVBounds f j) (MakeU u v)
    }.
Next Obligation.
  destruct ((` (nu f)) _).
  simpl in *.
  strivial use: @NoFractions, leq_trans.
Qed.

Definition NoQuantFormulaCondition
  {exiV exiF uniV} {exiFA : |[exiF]| -> nat}
  (f : @NoQuant exiV exiF uniV exiFA) 
  (M : Sigma11Model D) (adv : NoQuantAdvice) : Prop :=
  forall u, NoQuantZODenotation (formula f) M adv u.

Program Definition NoQuantFOBoundCondition 
  {exiV exiF uniV} {exiFA : |[exiF]| -> nat}
  (f : @NoQuant exiV exiF uniV exiFA) 
  (M : Sigma11Model D) (adv : NoQuantAdvice) : Prop :=
  forall i : |[exiV]|,
  forall u : U f M adv i, 
  forall n : |[uniV - nu f i]| -> T D,
  InBound M adv (exiVAdv adv i (MakeU u n)) (exiVBounds f i) (MakeU u n).

(* Note: This covers both conditions 5 and 6 in the paper *)
Definition NoQuantSOBoundCondition
  {exiV exiF uniV} {exiFA : |[exiF]| -> nat}
  (f : @NoQuant exiV exiF uniV exiFA) 
  (M : Sigma11Model D) (adv : NoQuantAdvice) : Prop :=
  forall u : |[uniV]| -> T D, forall i : |[exiF]|,
  let B := PolyVSDenotation (exiFOutputBounds f i) M adv u in
  let G (j : |[exiFA i]|) := PolyVSDenotation (exiFInputBounds f i j) M adv u in
  forall (t : |[exiFA i]| -> T D) (out : T D),
  exiFAdv adv i t = Some out ->
  match B with
  | None => false
  | Some B => lt D out B /\ forall x,
    match G x with
    | None => false
    | Some Gx => lt D (t x) Gx
    end
  end.

Program Definition NoQuantExiStratCondition 
  {exiV exiF uniV} {exiFA : |[exiF]| -> nat}
  (f : @NoQuant exiV exiF uniV exiFA) 
  (M : Sigma11Model D)
  (adv : @NoQuantAdvice exiV exiF uniV exiFA) : Prop :=
  forall i : |[exiV]|, forall m : |[nu f i]| -> T D,
  exists C, forall n : |[uniV - nu f i]| -> T D,
  exiVAdv adv i (MakeU m n) = C.

Definition NoQuantDenotation
  {exiV exiF uniV} {exiFA : |[exiF]| -> nat}
  (f : @NoQuant exiV exiF uniV exiFA) 
  (i : Sigma11Model D): Prop :=
  exists (a : NoQuantAdvice),
    NoQuantFormulaCondition f i a /\
    NoQuantFOBoundCondition f i a /\
    NoQuantSOBoundCondition f i a /\
    NoQuantExiStratCondition f i a.

End NoQuantDef.

Section NoQuantTranslation.

Variables D : RingData.

Fixpoint PolyTerm_PolyTermVS (p : PolyTerm) : @PolyTermVS 0 0 0 emptyTuple :=
  match p with
  | PolyVar m => PolyFVarVS m
  | PolyFun i a t => PolyFFunVS i a (fun x => PolyTerm_PolyTermVS (t x))
  | PolyMinusOne => PolyMinusOneVS
  | PolyPlusOne => PolyPlusOneVS
  | PolyZero => PolyZeroVS
  | PolyPlus r1 r2 => PolyPlusVS (PolyTerm_PolyTermVS r1) (PolyTerm_PolyTermVS r2)
  | PolyTimes r1 r2 => PolyTimesVS (PolyTerm_PolyTermVS r1) (PolyTerm_PolyTermVS r2)
  | PolyInd r1 r2 => PolyIndVS (PolyTerm_PolyTermVS r1) (PolyTerm_PolyTermVS r2)
  end.

Definition EmptyAdvice : @NoQuantAdvice D 0 0 0 emptyTuple :=
  {| exiVAdv := emptyTuple
   ; exiFAdv := emptyTuple
  |}.

Theorem EmptyAdviceUnique : forall a, a = EmptyAdvice.
Proof.
  intros [a b].
  unfold EmptyAdvice.
  f_equal. 
  apply functional_extensionality;move=> [lti i]; fcrush.
  apply functional_extensionality_dep;move=> [lti i]; fcrush.
Qed.

Definition PolyVSDenotation0
  (p : @PolyTermVS 0 0 0 emptyTuple)
  (M : Sigma11Model D) : option (T D) :=
  PolyVSDenotation D p M EmptyAdvice emptyTuple.

Theorem PolyTerm_PolyTermVS_Correct (p : PolyTerm) :
  Poly_Denote D p = PolyVSDenotation0 (PolyTerm_PolyTermVS p).
Proof.
  induction p; auto; apply functional_extensionality; intro.
  - unfold PolyVSDenotation0; simpl.
    do 2 f_equal; apply functional_extensionality; qauto.
  all: unfold PolyVSDenotation0; simpl;
      f_equal;[|by rewrite IHp1];
      apply functional_extensionality; intro;
      f_equal; by rewrite IHp2.
Qed.

Fixpoint ZerothOrder_ZerothOrderVS (p : ZerothOrderFormula) : @ZerothOrderFormulaVS 0 0 0 emptyTuple :=
  match p with
  | ZONot m => ZONotVS (ZerothOrder_ZerothOrderVS m)
  | ZOAnd r1 r2 => ZOAndVS (ZerothOrder_ZerothOrderVS r1) (ZerothOrder_ZerothOrderVS r2)
  | ZOOr r1 r2 => ZOOrVS (ZerothOrder_ZerothOrderVS r1) (ZerothOrder_ZerothOrderVS r2)
  | ZOImp r1 r2 => ZOImpVS (ZerothOrder_ZerothOrderVS r1) (ZerothOrder_ZerothOrderVS r2)
  | ZOEq a b => ZOEqVS (PolyTerm_PolyTermVS a) (PolyTerm_PolyTermVS b)
  end.

Definition NoQuantZODenotation0
  (p : @ZerothOrderFormulaVS 0 0 0 emptyTuple)
  (M : Sigma11Model D) : Prop :=
  NoQuantZODenotation D p M EmptyAdvice emptyTuple.

Theorem ZerothOrder_ZerothOrderVS_Correct (p : ZerothOrderFormula) :
  ZerothOrder_Denote D p = NoQuantZODenotation0 (ZerothOrder_ZerothOrderVS p).
Proof.
  induction p; apply functional_extensionality; intro; try qauto.
  unfold NoQuantZODenotation0; simpl.
  do 2 rewrite PolyTerm_PolyTermVS_Correct.
  unfold PolyVSDenotation0.
  do 2 (destruct (PolyVSDenotation  _ _ _ _); auto).
Qed.

Program Definition ZO_NoQuant
  (f : ZerothOrderFormula) : @NoQuant 0 0 0 emptyTuple :=
  {| nu := emptyTuple
   ; uniVBounds := emptyTuple
   ; exiVBounds := emptyTuple
   ; exiFOutputBounds := emptyTuple
   ; exiFInputBounds := emptyTuple
   ; formula := ZerothOrder_ZerothOrderVS f
  |}.

Lemma ZO_NoQuant_Correct_NoQuantFormulaCondition
  (f : ZerothOrderFormula) (M : Sigma11Model D) :
  ZerothOrder_Denote D f M <-> 
  exists a, NoQuantFormulaCondition D (ZO_NoQuant f) M a.
Proof.
  rewrite ZerothOrder_ZerothOrderVS_Correct.
  split;move=> H.
  - exists EmptyAdvice.
    intro t; replace t with (@emptyTuple (fun _ => T D));auto.
    apply functional_extensionality;move=> [x ltx]; fcrush.
  - destruct H as [adv H].
    unfold NoQuantFormulaCondition in H.
    remember (H emptyTuple) as H'; clear HeqH' H.
    rewrite (EmptyAdviceUnique adv) in H'; auto.
Qed.

Lemma ZO_NoQuant_Correct_NoQuantFOBoundCondition
  (f : ZerothOrderFormula) (M : Sigma11Model D) :
  forall a, NoQuantFOBoundCondition D (ZO_NoQuant f) M a.
Proof. move=> a [u ltu]; fcrush. Qed.

Lemma ZO_NoQuant_Correct_NoQuantSOBoundCondition
  (f : ZerothOrderFormula) (M : Sigma11Model D) :
  forall a, NoQuantSOBoundCondition D (ZO_NoQuant f) M a.
Proof. move=> a u [i lti]; fcrush. Qed.

Lemma ZO_NoQuant_Correct_NoQuantExiStratCondition
  (f : ZerothOrderFormula) (M : Sigma11Model D) :
  forall a, NoQuantExiStratCondition D (ZO_NoQuant f) M a.
Proof. move=> a [i lti]; fcrush. Qed.

Theorem ZO_NoQuant_Correct (p : ZerothOrderFormula) (M : Sigma11Model D) :
  ZerothOrder_Denote D p M <-> NoQuantDenotation D (ZO_NoQuant p) M.
Proof.
  hauto use: ZO_NoQuant_Correct_NoQuantFormulaCondition
           , ZO_NoQuant_Correct_NoQuantFOBoundCondition
           , ZO_NoQuant_Correct_NoQuantSOBoundCondition
           , ZO_NoQuant_Correct_NoQuantExiStratCondition.
Qed.

Fixpoint FOUni (f : FirstOrderFormula) : nat :=
  match f with
  | ZO z => 0
  | FOExists p f => FOUni f
  | FOForall p f => (FOUni f).+1
  end.

Fixpoint FOExi (f : FirstOrderFormula) : nat :=
  match f with
  | ZO z => 0
  | FOExists p f => (FOExi f).+1
  | FOForall p f => FOExi f
  end.

Program Fixpoint PolyTermVSLiftExi
  {exiV uniV}
  (p : @PolyTermVS exiV 0 uniV emptyTuple):
  @PolyTermVS (exiV.+1) 0 uniV emptyTuple :=
  match p with
  | PolyFVarVS i => 
    if i == 0
    then PolyEVarVS 0
    else PolyFVarVS (i.-1)
  | PolyEVarVS i => PolyEVarVS (i.+1)
  | PolyUVarVS i => PolyUVarVS i
  | PolyFFunVS i a t => PolyFFunVS i a (fun x => PolyTermVSLiftExi (t x))
  | PolyEFunVS i t => emptyTuple i
  | PolyMinusOneVS => PolyMinusOneVS
  | PolyPlusOneVS => PolyPlusOneVS
  | PolyZeroVS => PolyZeroVS
  | PolyPlusVS p1 p2 => PolyPlusVS (PolyTermVSLiftExi p1) (PolyTermVSLiftExi p2)
  | PolyTimesVS p1 p2 => PolyTimesVS (PolyTermVSLiftExi p1) (PolyTermVSLiftExi p2)
  | PolyIndVS p1 p2 => PolyIndVS (PolyTermVSLiftExi p1) (PolyTermVSLiftExi p2)
  end.

Fixpoint PropTermVSLiftExi
  {exiV uniV}
  (f : @ZerothOrderFormulaVS exiV 0 uniV emptyTuple):
  @ZerothOrderFormulaVS (exiV.+1) 0 uniV emptyTuple :=
  match f with
  | ZONotVS f => ZONotVS (PropTermVSLiftExi f)
  | ZOAndVS f1 f2 => ZOAndVS (PropTermVSLiftExi f1) (PropTermVSLiftExi f2)
  | ZOOrVS f1 f2 => ZOOrVS (PropTermVSLiftExi f1) (PropTermVSLiftExi f2)
  | ZOImpVS f1 f2 => ZOImpVS (PropTermVSLiftExi f1) (PropTermVSLiftExi f2)
  | ZOEqVS r1 r2 => ZOEqVS (PolyTermVSLiftExi r1) (PolyTermVSLiftExi r2)
  end.

Program Fixpoint PolyTermVSLiftUni
  {exiV uniV}
  (p : @PolyTermVS exiV 0 uniV emptyTuple):
  @PolyTermVS exiV 0 (uniV.+1) emptyTuple :=
  match p with
  | PolyFVarVS i => 
    if i == 0
    then PolyUVarVS 0
    else PolyFVarVS (i.-1)
  | PolyEVarVS i => PolyEVarVS i
  | PolyUVarVS i => PolyUVarVS (i.+1)
  | PolyFFunVS i a t => PolyFFunVS i a (fun x => PolyTermVSLiftUni (t x))
  | PolyEFunVS i t => emptyTuple i
  | PolyMinusOneVS => PolyMinusOneVS
  | PolyPlusOneVS => PolyPlusOneVS
  | PolyZeroVS => PolyZeroVS
  | PolyPlusVS p1 p2 => PolyPlusVS (PolyTermVSLiftUni p1) (PolyTermVSLiftUni p2)
  | PolyTimesVS p1 p2 => PolyTimesVS (PolyTermVSLiftUni p1) (PolyTermVSLiftUni p2)
  | PolyIndVS p1 p2 => PolyIndVS (PolyTermVSLiftUni p1) (PolyTermVSLiftUni p2)
  end.

Fixpoint PropTermVSLiftUni
  {exiV uniV}
  (f : @ZerothOrderFormulaVS exiV 0 uniV emptyTuple):
  @ZerothOrderFormulaVS exiV 0 (uniV.+1) emptyTuple :=
  match f with
  | ZONotVS f => ZONotVS (PropTermVSLiftUni f)
  | ZOAndVS f1 f2 => ZOAndVS (PropTermVSLiftUni f1) (PropTermVSLiftUni f2)
  | ZOOrVS f1 f2 => ZOOrVS (PropTermVSLiftUni f1) (PropTermVSLiftUni f2)
  | ZOImpVS f1 f2 => ZOImpVS (PropTermVSLiftUni f1) (PropTermVSLiftUni f2)
  | ZOEqVS r1 r2 => ZOEqVS (PolyTermVSLiftUni r1) (PolyTermVSLiftUni r2)
  end.

Program Fixpoint PolyTermVSCastFO
  {exiV uniV}
  (p : @PolyTermVS 0 0 0 emptyTuple):
  @PolyTermVS exiV 0 uniV emptyTuple :=
  match p with
  | PolyFVarVS i => PolyFVarVS i
  | PolyEVarVS i => emptyTuple i
  | PolyUVarVS i => emptyTuple i
  | PolyFFunVS i a t => PolyFFunVS i a (fun x => PolyTermVSCastFO (t x))
  | PolyEFunVS i t => emptyTuple i
  | PolyMinusOneVS => PolyMinusOneVS
  | PolyPlusOneVS => PolyPlusOneVS
  | PolyZeroVS => PolyZeroVS
  | PolyPlusVS p1 p2 => PolyPlusVS (PolyTermVSCastFO p1) (PolyTermVSCastFO p2)
  | PolyTimesVS p1 p2 => PolyTimesVS (PolyTermVSCastFO p1) (PolyTermVSCastFO p2)
  | PolyIndVS p1 p2 => PolyIndVS (PolyTermVSCastFO p1) (PolyTermVSCastFO p2)
  end.

Program Definition NoQuantAddExi 
  {exiV uniV}
  (b : @PolyTermVS 0 0 0 emptyTuple)
  (q : @NoQuant exiV 0 uniV emptyTuple) :
  @NoQuant (exiV.+1) 0 uniV emptyTuple :=
  {| nu := ExtendAt0N 0 (nu q)
  ; uniVBounds := fun x => PolyTermVSLiftExi (uniVBounds q x)
  ; exiVBounds := 
    ExtendAt0N (PolyTermVSCastFO b)
               (fun x => PolyTermVSLiftExi (exiVBounds q x))
  ; exiFOutputBounds := emptyTuple
  ; exiFInputBounds := emptyTuple
  ; formula := PropTermVSLiftExi (formula q)
  |}.
Next Obligation.
  unfold ExtendAt0N.
  dep_if_case (x == 0); auto.
  by destruct ((` (nu q)) _).
Qed.
Next Obligation.
  destruct (nu q).
  unfold ExtendAt0N.
  dep_if_case (i == 0); auto.
  dep_if_case (j == 0); auto;[|apply i0]; by destruct i, j.
Qed.

Program Definition NoQuantAddUni 
  {exiV uniV}
  (b : @PolyTermVS 0 0 0 emptyTuple)
  (q : @NoQuant exiV 0 uniV emptyTuple) :
  @NoQuant exiV 0 (uniV.+1) emptyTuple :=
  {| nu := fun x => (nu q x).+1
  ; uniVBounds := 
    ExtendAt0N (PolyTermVSCastFO b)
               (fun x => PolyTermVSLiftUni (uniVBounds q x))
  ; exiVBounds := fun x => PolyTermVSLiftUni (exiVBounds q x)
  ; exiFOutputBounds := emptyTuple
  ; exiFInputBounds := emptyTuple
  ; formula := PropTermVSLiftUni (formula q)
  |}.
Next Obligation. by destruct ((` (nu q)) _). Qed.
Next Obligation.
  destruct (nu q).
  by apply i0.
Qed.

Fixpoint FO_NoQuant
  (f : FirstOrderFormula) : @NoQuant (FOExi f) 0 (FOUni f) emptyTuple :=
  match f with
  | ZO z => ZO_NoQuant z
  | FOExists p f => NoQuantAddExi (PolyTerm_PolyTermVS p) (FO_NoQuant f)
  | FOForall p f => NoQuantAddUni (PolyTerm_PolyTermVS p) (FO_NoQuant f)
  end.

Definition AdviceExiExtend {exiV uniV}
  (r : T D)
  (adv : @NoQuantAdvice D exiV 0 uniV emptyTuple) : 
  @NoQuantAdvice D (exiV.+1) 0 uniV emptyTuple :=
  {| exiVAdv := ExtendAt0N (fun _ => r) (exiVAdv D adv)
  ; exiFAdv := exiFAdv D adv
  |}.

Program Definition AdviceUniExtend {exiV uniV}
  (M : Sigma11Model D)
  (adv : @NoQuantAdvice D exiV 0 uniV emptyTuple) 
  (f : {f : |[exiV]| -> (|[uniV.+1]| -> T D) -> T D | forall i x, f i (ExtendAt0N (V_F D M 0) x) = exiVAdv D adv i x }): 
  @NoQuantAdvice D exiV 0 (uniV.+1) emptyTuple :=
  {| exiVAdv := f
  ; exiFAdv := exiFAdv D adv
  |}.

Lemma FO_NoQuant_Correct_Lem_0_0
  {exiV uniV}
  (p : @PolyTermVS exiV 0 uniV emptyTuple)
  (adv : @NoQuantAdvice D exiV 0 uniV emptyTuple) 
  (M : Sigma11Model D) (r : T D) :
  forall u,
  PolyVSDenotation D p (AddModelV D M r) adv u = 
  PolyVSDenotation D (PolyTermVSLiftExi p) M (AdviceExiExtend r adv) u.
Proof.
  elim: p; try qauto.
  - move=> n u.
    simpl.
    unfold ExtendAt0.
    dep_if_case (n == 0); auto.
    rewrite H.
    simpl.
    f_equal.
    by rewrite H.
  - move=> n u.
    simpl.
    f_equal.
    unfold ExtendAt0N; simpl.
    f_equal.
    by destruct n; apply subset_eq_compat.
  - move=> i a p IH u.
    simpl.
    do 2 f_equal.
    by apply functional_extensionality;move=> x.
  - move=> [i lti]; fcrush.
Qed.

Lemma FO_NoQuant_Correct_Lem_0 
  {exiV uniV}
  (f: @ZerothOrderFormulaVS exiV 0 uniV emptyTuple)
  (adv : @NoQuantAdvice D exiV 0 uniV emptyTuple) 
  (M : Sigma11Model D) (r : T D) :
  forall u,
  NoQuantZODenotation D f (AddModelV D M r) adv u <->
  NoQuantZODenotation D (PropTermVSLiftExi f) M (AdviceExiExtend r adv) u.
Proof.
  elim: f; try qauto.
  move=> p1 p2 u.
  simpl.
  by do 2 rewrite FO_NoQuant_Correct_Lem_0_0.
Qed.


Lemma FO_NoQuant_Correct_Lem_1
  {exiV uniV}
  (adv : @NoQuantAdvice D exiV 0 uniV emptyTuple)
  (p : @PolyTermVS 0 0 0 emptyTuple)
  (M : Sigma11Model D) :
  forall u, 
  PolyVSDenotation D (PolyTermVSCastFO p) M adv u
  = (PolyVSDenotation0 p M).
Proof.
  move=> u; elim p; try qauto.
  - move=> [n ltn]; fcrush.
  - move=> [n ltn]; fcrush.
  - move=> i a t IH.
    unfold PolyVSDenotation0; simpl.
    do 2 f_equal.
    apply functional_extensionality;move=> x.
    qauto.
  - move=> [i lti]; fcrush.
Qed.

(* Lemma FO_NoQuant_Correct_Lem_2
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model D) a r
  (t : {n : nat | n < FOUni f} -> T D) :
  UProp D (FO_NoQuant f) (AddModelV D M r) a t <->
  UProp D (FO_NoQuant (FOExists p f)) M (AdviceExiExtend r a) t.
Proof.
  unfold UProp; simpl; split=> H i.
  - rewrite <- FO_NoQuant_Correct_Lem_0_0.
    apply (H i).
  - rewrite FO_NoQuant_Correct_Lem_0_0.
    apply (H i).
Qed. *)

Lemma FO_NoQuant_Correct_NoQuantSOBoundCondition
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model D) a :
  NoQuantSOBoundCondition D (FO_NoQuant f) M a.
Proof. move=> u [i lti]; fcrush. Qed. 

Lemma FO_NoQuant_Correct_NoQuantFormulaCondition_Exi
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model D) a r :
  NoQuantFormulaCondition D (FO_NoQuant f) (AddModelV D M r) a <-> 
  NoQuantFormulaCondition D (FO_NoQuant (FOExists p f)) M (AdviceExiExtend r a).
Proof. split; move=> H u; by apply FO_NoQuant_Correct_Lem_0. Qed.

(* 
Lemma FO_NoQuant_Correct_NoQuantFOBoundCondition_Exi
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model D) a r :
  (NoQuantFOBoundCondition D (FO_NoQuant f) (AddModelV D M r) a) <->
  NoQuantFOBoundCondition D (FO_NoQuant (FOExists p f)) M (AdviceExiExtend r a).
Proof.
  split.
  - move=> H0 [i lti] u n0.
    destruct (i == 0) eqn:ei0.
    + simpl; unfold ExtendAt0N.
      do 2 (rewrite dep_if_case_true; auto).
      unfold NoQuantFOBoundCondition in H0.
       *)

Program Definition FO_NoQuant_Correct_Lem_2_0 {exiV uniV i}
  {lti lti2 : i < exiV}
  {nuF : {n : nat | n < exiV} -> {m : nat | m <= uniV}}
  (v : {n : nat | n < uniV - ` (nuF (exist _ i lti))} -> T D) :
  {n : nat | n < uniV - ` (nuF (exist _ i lti2))} -> T D := v.
Next Obligation.
  by replace lti with lti2;[|apply eq_irrelevance].
Qed.

Program Definition FO_NoQuant_Correct_Lem_2
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model D) a r i
  (lti : i.+1 < (FOExi f).+1)
  (t : {n : nat | n < FOUni f} -> T D)
  (u : U D (FO_NoQuant (FOExists p f)) M (AdviceExiExtend r a)
      (exist (fun n : nat => n < (FOExi f).+1) i.+1 lti)) :
  U D (FO_NoQuant f) (AddModelV D M r) a
      (exist (fun n : nat => n < FOExi f) i lti) := u.
Next Obligation.
  unfold ExtendAt0N; simpl.
  replace (` ((` (nu (FO_NoQuant f))) _)) 
     with (` ((` (nu (FO_NoQuant f))) (exist _ i lti))); auto.
  do 3 f_equal; apply proof_irrelevance.
Qed.
Next Obligation.
  destruct u as [u pu]; simpl in *.
  unfold ExtendAt0N in *; simpl in *.
  pose lti2 := (Utils.ExtendAt0N_obligation_2 (FOExi f) (exist _ i.+1 lti) (erefl _)).
  assert (lti2 = lti) as e;[apply proof_irrelevance|].
  assert (j < ` ((` (nu (FO_NoQuant f))) (exist _ i lti2))) as ltj;[by rewrite e|].
  remember (pu (exist _ j ltj) (FO_NoQuant_Correct_Lem_2_0 v)) as pu'; clear Heqpu' pu.
  remember (InBound _ _ _ _ _ _) as A1.
  replace (InBound _ _ _ _ _ _) with A1;[auto|].
  rewrite HeqA1; clear pu' HeqA1 A1.
  f_equal.
  unfold InBound; simpl.
  remember (U_obligation_1 _ _ _ _ _ _ _ _ _ _) as DD0; clear HeqDD0.
  remember (U_obligation_1 _ _ _ _ _ _ _ _ _ _) as DD1; clear HeqDD1.
  simpl in *.
  rewrite <- FO_NoQuant_Correct_Lem_0_0.
  remember (PolyVSDenotation _ _ _ _ _) as P1.
  remember (PolyVSDenotation D (uniVBounds (FO_NoQuant f) (exist _ j DD1)) _ a _) as P2.
  replace P1 with P2.
  destruct P2; simpl; auto.
  by do 2 f_equal; apply subset_eq_compat.
  rewrite HeqP1 HeqP2; clear HeqP1 HeqP2 P1 P2.
  f_equal.
  by f_equal; apply subset_eq_compat.
  unfold MakeU.
  apply functional_extensionality=> x.
  simpl.
  f_equal.
  unfold TupConcat.
  remember (Utils.ExtendAt0N_obligation_2 _ _ _ ) as DD2.
  
  destruct e. 
  reflexivity.
  f_equal.
  rewrite <- e.
  f_equal.
  replace (MakeU (fun x => u (exist _ (` x)
             (FO_NoQuant_Correct_Lem_2_obligation_1 p f i lti x))) v)
  with (MakeU u (FO_NoQuant_Correct_Lem_2_0 v)).
  replace DD0 with DD1;[|apply eq_irrelevance].
  remember (PolyVSDenotation _ _ _ _ _) as P1.
  remember (PolyVSDenotation D
    (uniVBounds (FO_NoQuant f) (exist (fun n : nat => n < FOUni f) j DD1))
    (AddModelV D M r) a (MakeU u (FO_NoQuant_Correct_Lem_2_0 v))) as P2.
  rewrite <- HeqP1.
  remember (PolyVSDenotation _ _ _ _ _) as P2. 
  rewrite PM.

PolyVSDenotation D
  (uniVBounds (FO_NoQuant f) (exist (fun n : nat => n < FOUni f) j DD1))
  (AddModelV D M r) a (MakeU u (FO_NoQuant_Correct_Lem_2_0 v))
PolyVSDenotation D
  (uniVBounds (FO_NoQuant f) (exist (fun n : nat => n < FOUni f) j DD1))
  (AddModelV D M r) a (MakeU u (FO_NoQuant_Correct_Lem_2_0 v))

  f_equal.
  simpl.
  unfold PolyTermVSLiftExi.
  destruct e.

  f_equal.
  unfold InBound in *.


Check (exist (fun n0 : nat => n0 < FOExi f) i lti).

Program Definition FO_NoQuant_Correct_Lem_2_0 {exiV} {uniV}
  {lti lti2 : i.+1 < eviV}
  (nuF : {n : nat | n < exiV} -> {m : nat | m <= uniV})
  (v : {n : nat | n < uniV - ` (nuF (exist _ i lti))} -> T D) :
  {n : nat | n < uniV - ` (nuF (exist _ i lti2))} -> T D := v.

  unfold InBound.
  remember (U_obligation_1 _ _ _ _ _ _ _ _ _ _) as DD0; clear HeqDD0.
  simpl.
  rewrite e in v.
  destruct v as [v ltv].
  rewrite e in H.


Lemma FO_NoQuant_Correct_NoQuantFOBoundCondition_Exi
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model D) a r :
  ((forall n, InBound D M (AdviceExiExtend r a) r (PolyTermVSCastFO (PolyTerm_PolyTermVS p)) n)
   /\ NoQuantFOBoundCondition D (FO_NoQuant f) (AddModelV D M r) a) <->
  NoQuantFOBoundCondition D (FO_NoQuant (FOExists p f)) M (AdviceExiExtend r a).
Proof.
  split.
  - move=> [H0 H1] [i lti] u n0.
    destruct (i == 0) eqn:ei0.
    + simpl; unfold ExtendAt0N.
      do 2 (rewrite dep_if_case_true; auto).
    + destruct i;[fcrush|clear ei0].
      simpl in n0; unfold ExtendAt0N in n0; simpl in n0.
      remember (H0 (MakeU (` u) n0)) as H0'; clear HeqH0' H0; simpl in H0'.
      unfold NoQuantFOBoundCondition in H1.
      remember (H1 (exist _ i lti)) as H1'; clear HeqH1' H1.
      simpl in lti.
      unfold U in u; simpl in u.
      unfold ExtendAt0N in *; simpl in *.
      assert (lti = (Utils.ExtendAt0N_obligation_2 (FOExi f) (exist _ i.+1 lti) (erefl
        (exist _ i.+1 lti == exist _ 0 is_true_true)))) as e;[apply eq_irrelevance|].
      clear H0'.
      rewrite e in u.
      destruct u as [u pu]; simpl in *.
      rewrite e in n0.
      unfold InBound in *.
      destruct u as [u pu]; simpl in *.
      unfold ExtendAt0N; simpl.
      change (exist _ ?x _ == exist _ ?y _) with (x == y) in *.
      rewrite FO_NoQuant_Correct_Lem_1 in H0'.
      rewrite <- FO_NoQuant_Correct_Lem_0_0.
      destruct (FO_NoQuant f); simpl.
      remember (Utils.ExtendAt0N_obligation_2 (FOExi f)
             (exist (fun n : nat => n < (FOExi f).+1) i.+1 lti)
             (erefl (i.+1 == 0))) as DD0.

      assert (lti = (Utils.ExtendAt0N_obligation_2 (FOExi f) (exist _ i.+1 lti) (erefl
        (exist _ i.+1 lti == exist _ 0 is_true_true)))) as e;[apply eq_irrelevance|].


(exist (fun n1 : nat => n1 < FOExi f) i
          (Utils.ExtendAt0N_obligation_2 (FOExi f)
             (exist (fun n : nat => n < (FOExi f).+1) i.+1 lti)
             (erefl (i.+1 == 0))))) (AddModelV D M r) a 
      destruct M; unfold AddModelV.
      unfold ExtendAt0.
      simpl.
      auto.
      apply
      simpl in n1.
      remember (` ((` (nu (FO_NoQuant f))) _)) as nn.
      assert (nn <= FOUni f);[by destruct ((` (nu (FO_NoQuant f))) _); rewrite Heqnn|].
      assert ({n : nat | n < FOUni f} -> T D) as n1.
        move=>[n ltn].
        destruct (n < FOUni f - nn) eqn:nlt2.
        apply n0.
        exists n.
        clear Heqnn u lti H0 H1; sfirstorder.
        exact 0%R.
      remember (H0 n1) as H0'. ; clear HeqH0' H0; simpl in H0'.
      
      remember (MakeU n0 (fun x => 0%R)) as n1.

      assert (forall n, n < FOUni f - nn -> n < FOUni f) as d.
        clear u; hecrush use: leq_trans, ltn_subrR, contraFltn unfold: is_true.
      assert ({n : nat | n < FOUni f} -> T D) as n1.
      move=> [n ltn].
      assert (n < FOUni f - nn).
    
      simpl; unfold ExtendAt0N; simpl.

      remember (fun x : {n : nat | n < FOUni f} => 
                )
        exists 0.
        unfold ExtendAt0N; simpl.
      cbn.
      auto.
      simpl in *.
      destruct u as [u ltu]; simpl in *.
      unfold ExtendAt0N in *; simpl in *.
      remember (exist (fun n1 : nat => n1 < FOExi f) i
        (Utils.ExtendAt0N_obligation_2 (FOExi f)
           (exist (fun n : nat => n < (FOExi f).+1) i.+1 lti)
           (erefl
              (exist (fun n : nat => n < (FOExi f).+1) i.+1 lti ==
               exist (fun x : nat => x < (FOExi f).+1) 0 is_true_true)))) as e1.

      unfold U in u; simpl in u.
      unfold ExtendAt0N in *; simpl in *.
      destruct ((` (nu (FO_NoQuant f)))
           (exist (fun n0 : nat => n0 < FOExi f) i
              (Utils.ExtendAt0N_obligation_2 (FOExi f)
                 (exist (fun n0 : nat => n0 < (FOExi f).+1) i.+1 lti)
                 (erefl
                    (exist (fun n0 : nat => n0 < (FOExi f).+1) i.+1 lti ==
                     exist (fun x : nat => x < (FOExi f).+1) 0 is_true_true)))))


      remember (Utils.ExtendAt0N_obligation_2 
                        (FOExi f)
                        (exist (fun n0 : nat => n0 < (FOExi f).+1) i.+1 lti)
                        (erefl
                           (exist (fun n0 : nat => n0 < (FOExi f).+1) i.+1
                              lti ==
                            exist (fun x : nat => x < (FOExi f).+1) 0
                              is_true_true))) as DDD.
      unfold InBound.
      simpl.
      unfold ExtendAt0N; rewrite dep_if_case_true; auto.
; rewrite FO_NoQuant_Correct_Lem_1.
      clear n u.
      destruct u as [u ltu]; simpl.
      destruct (FO_NoQuant f); simpl in *.
      unfold ExtendAt0N in ltu.
      change (exist _ ?x _ == exist _ ?y _) with (x == y) in *.
      rewrite FO_NoQuant_Correct_Lem_1.
      destruct u as [u ltu].
      simpl in *.

      assert i < 

      rewrite
    destruct n as [n ltn].
    rewrite dep_if_case_true; auto.

    move


Lemma FO_NoQuant_Correct_NoQuantExiStratCondition_Exi
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model D) a r :
  NoQuantExiStratCondition D (FO_NoQuant f) (AddModelV D M r) a <->
  NoQuantExiStratCondition D (FO_NoQuant (FOExists p f)) M (AdviceExiExtend r a).
Proof.
  split;move=> H.
  - unfold NoQuantExiStratCondition in *.
    move=> i m.
    destruct i as [i lti]; simpl.
    destruct (i == 0) eqn:ei0.
    + exists r;move=> n.
      unfold ExtendAt0N; simpl; rewrite dep_if_case_true; auto.
    + assert (i.-1 < FOExi f) as lti2. destruct i;[fcrush|auto].
      remember (H (exist _ (i.-1) lti2)) as H'; clear HeqH' H.
      assert (ExtendAt0N 0 (fun x => ` ((` (nu (FO_NoQuant f))) x)) (exist _ i lti) =
              ` ((` (nu (FO_NoQuant f))) (exist (fun n0 : nat => n0 < FOExi f) i.-1 lti2))) as e.
        unfold ExtendAt0N.
        rewrite dep_if_case_false.
        do 3 f_equal; apply eq_irrelevance.
      remember (H' (eq_rect _ (fun x => |[x]| -> T D) m _ e)) as H; clear HeqH H'.
      destruct H as [C H].
      exists C; move=> n.
      unfold ExtendAt0N; rewrite dep_if_case_false; auto; simpl.
      remember (H (eq_rect _ (fun x => |[FOUni f - x]| -> T D) n _ e)) as H'; clear HeqH' H.
      destruct a; simpl in *.
      change (exist _ ?x _ == exist _ ?y _) with (x == y) in *.
      remember (exiVAdv0 _ _) as A1.
      remember (exiVAdv0 (exist _ i.-1 (Utils.ExtendAt0N_obligation_2 _ (exist _ i lti) _)) _) as A2.
      replace A2 with A1; auto.
      rewrite HeqA1; rewrite HeqA2; clear HeqA1 HeqA2.
      f_equal;[f_equal; apply eq_irrelevance|].
      apply functional_extensionality;move=> x.
      remember (NoQuantExiStratCondition_obligation_1 _ _ _ _ _ _ _ _ _ _) as DD0; clear HeqDD0.
      remember (NoQuantExiStratCondition_obligation_1 _ _ _ _ _ _ _ _ _ _) as DD1; clear HeqDD1.
      destruct e.
      by f_equal; apply subset_eq_compat.
  - unfold NoQuantExiStratCondition in *.
    move=> i m.
    simpl in H.
    destruct i as [i lti].
    remember (H (exist _ (i.+1) lti)) as H'; clear HeqH' H.
    unfold ExtendAt0N in H'; simpl in H'.
    assert (lti = Utils.ExtendAt0N_obligation_2  (FOExi f) (exist _ i.+1 lti)
                      (erefl (exist _ i.+1 lti == exist _ 0 is_true_true))) as e;[apply eq_irrelevance|].
    remember (H' (eq_rect _ (fun x => |[ ` ((` (nu (FO_NoQuant f))) (exist _ i x))]| -> T D) m _ e)) as H; clear HeqH H'.
    destruct H as [C H].
    exists C; move=> n.
    remember (H (eq_rect _ (fun x => |[FOUni f - ` ((` (nu (FO_NoQuant f))) (exist _ i x))]| -> T D) n _ e)) as H'; clear HeqH' H.
    destruct a; simpl in *.
    remember (exiVAdv0 _ _) as A1.
    remember (exiVAdv0 (exist _ i lti) _) as A2.
    replace A2 with A1; auto.
    rewrite HeqA1; rewrite HeqA2; clear HeqA1 HeqA2.
    f_equal;[f_equal; apply eq_irrelevance|].
    apply functional_extensionality;move=> x.
    remember (NoQuantExiStratCondition_obligation_1 _ _ _ _ _ _ _ _ _ _) as DD0; clear HeqDD0.
    remember (NoQuantExiStratCondition_obligation_1 _ _ _ _ _ _ _ _ _ _) as DD1; clear HeqDD1.
    remember (exist _ (` x) DD0) as E0; destruct E0; apply EqdepFacts.eq_sig_fst in HeqE0.
    remember (exist _ (` x) DD1) as E1; destruct E1; apply EqdepFacts.eq_sig_fst in HeqE1.
    destruct HeqE0, HeqE1, e.
    by f_equal; apply subset_eq_compat.
Qed.


(* 
Lemma FO_NoQuant_Correct_NoQuantFormulaCondition_Uni
  (f : FirstOrderFormula) (M : Sigma11Model D) a r :
  NoQuantFormulaCondition D (FO_NoQuant f) (AddModelV D M r) a <->
  NoQuantFormulaCondition D (FO_NoQuant (FOForall p f)) M (AdviceExiExtend r a).

Lemma FO_NoQuant_Correct_NoQuantFOBoundCondition_Uni
  (f : FirstOrderFormula) (M : Sigma11Model D) a r :
  NoQuantFOBoundCondition D (FO_NoQuant f) (AddModelV D M r) a <->
  NoQuantFOBoundCondition D (FO_NoQuant (FOForall p f)) M (AdviceExiExtend r a).

Lemma FO_NoQuant_Correct_NoQuantSOBoundCondition_Uni
  (f : FirstOrderFormula) (M : Sigma11Model D) a r :
  NoQuantSOBoundCondition D (FO_NoQuant f) (AddModelV D M r) a <->
  NoQuantSOBoundCondition D (FO_NoQuant (FOForall p f)) M (AdviceExiExtend r a).

Lemma FO_NoQuant_Correct_NoQuantExiStratCondition_Uni
  (f : FirstOrderFormula) (M : Sigma11Model D) a r :
  NoQuantExiStratCondition D (FO_NoQuant f) (AddModelV D M r) a <->
  NoQuantExiStratCondition D (FO_NoQuant (FOForall p f)) M (AdviceExiExtend r a). *)

Lemma FO_NoQuant_Correct_Lem_3_0
  (f : ZerothOrderFormula) (M : Sigma11Model D) a
  (H0 : NoQuantFormulaCondition D (ZO_NoQuant f) M a)
  (H1 : NoQuantFOBoundCondition D (ZO_NoQuant f) M a)
  (H2 : NoQuantSOBoundCondition D (ZO_NoQuant f) M a)
  (H3 : NoQuantExiStratCondition D (ZO_NoQuant f) M a) :
  (exists (t : |[0]| -> T D), UProp D (ZO_NoQuant f) M a t) \/
  ZerothOrder_Denote D f M.
Proof.
  right.
  apply ZO_NoQuant_Correct.
  unfold NoQuantDenotation.
  exists a; auto.
Qed.

(* Lemma FO_NoQuant_Correct_Lem_3
  (f : FirstOrderFormula) (M : Sigma11Model D) a
  (H0 : NoQuantFormulaCondition D (FO_NoQuant f) M a)
  (H1 : NoQuantFOBoundCondition D (FO_NoQuant f) M a)
  (H2 : NoQuantSOBoundCondition D (FO_NoQuant f) M a)
  (H3 : NoQuantExiStratCondition D (FO_NoQuant f) M a) :
  (exists (t : |[FOUni f]| -> T D), UProp D (FO_NoQuant f) M a t) \/
  FirstOrder_Denote D f M.
Proof.
  induction f; simpl in *.
  - apply FO_NoQuant_Correct_Lem_3_0; auto.
  - left.

Admitted. *)

(* 

Lemma FO_NoQuant_Correct_Lem_3
  {exiV uniV}
  (p : @PolyTermVS 0 0 0 emptyTuple)
  (q : @NoQuant exiV 0 uniV emptyTuple)
  (i : nat) (H : (i == 0) = false) (lti : i < exiV.+1) (lti2 : i.-1 < exiV) :
  ` ((` (nu q)) (exist _ i.-1 lti2)) =
  ` ((` (nu (NoQuantAddExi p q))) (exist _ i lti)).
Proof.
  destruct q; simpl.
  unfold ExtendAt0N.
  rewrite dep_if_case_false.
  simpl.
  do 3 f_equal; apply eq_irrelevance.
Qed.

Lemma FO_NoQuant_Correct_Lem_4
  {exiV uniV}
  (q : @NoQuant exiV 0 uniV emptyTuple)
  (i : nat) (H : (i == 0) = false) (lti : i < exiV.+1) (lti2 : i.-1 < exiV) :
  uniV - ` ((` (nu q)) (exist _ i.-1 lti2)) =
  uniV - ExtendAt0N 0
          (fun x : {n0 : nat | n0 < exiV} => ` ((` (nu q)) x))
          (exist _ i lti).
Proof.
  unfold ExtendAt0N.
  rewrite dep_if_case_false; auto.
  simpl.
  remember (Utils.ExtendAt0N_obligation_2 _ _ _) as D0.
  simpl in D0.
  by replace D0 with lti2;[|apply eq_irrelevance].
Qed. *)

(*
n < uniV - ` ((` (nu q)) (exist _ i.-1 lti2))
uniV - ExtendAt0N 0
        (fun x : {n0 : nat | n0 < exiV} => ` ((` (nu q)) x))
        (exist _ i lti)
 *)


(* Lemma FO_NoQuant_Correct_Lem_1
  {exiV uniV}
  (b : @PolyTermVS 0 0 0 emptyTuple)
  (adv : @NoQuantAdvice D exiV 0 uniV emptyTuple) 
  (p : @NoQuant exiV 0 uniV emptyTuple)
  (M : Sigma11Model D) (r : T D) :
  forall u i, 
    PolyVSDenotation D
      (exiVBounds (NoQuantAddExi b p) i) M
      (AdviceExiExtend r adv) u =
    PolyVSDenotation D (exiVBounds p (fSeqRest i)) (AddModelV D M r) adv u. *)

Theorem FO_NoQuant_Correct (p : FirstOrderFormula) (M : Sigma11Model D) :
  FirstOrder_Denote D p M <-> NoQuantDenotation D (FO_NoQuant p) M.
Proof.
  move: M; elim: p.
  - apply ZO_NoQuant_Correct.
  - move=> p f IH M.
    split.
    + move=> H.
      simpl.
      unfold NoQuantDenotation.
      simpl in H.
      remember (Poly_Denote D p M) as PM.
      destruct PM;[|fcrush].
      destruct H as [r [ltrs fd]].
      apply ((IH (AddModelV D M r)).1) in fd; clear IH.
      unfold NoQuantDenotation in fd.
      destruct fd as [adv [H0 [H1 [H2 H3]]]].
      apply (FO_NoQuant_Correct_NoQuantFormulaCondition_Exi p) in H0.
      apply (FO_NoQuant_Correct_NoQuantSOBoundCondition_Exi p) in H2.
      apply (FO_NoQuant_Correct_NoQuantExiStratCondition_Exi p) in H3.
      exists (AdviceExiExtend r adv).
      split;[|split;[|split]];auto.
      * clear H0 H2 H3. 
        move=> u i.
        simpl.
        unfold ExtendAt0N.
        destruct i as [i lti].
        dep_if_case (i == 0); auto.
        ++ rewrite dep_if_case_true; simpl; auto.
           rewrite FO_NoQuant_Correct_Lem_1.
           rewrite <- PolyTerm_PolyTermVS_Correct.
           by rewrite <- HeqPM.
        ++ rewrite <- FO_NoQuant_Correct_Lem_0_0.
           rewrite dep_if_case_false; simpl.
           remember (exist (fun n0 : nat => n0 < FOExi f) i.-1 _) as i'.
           destruct u as [u uH]; simpl.
           apply FO_NoQuant_Correct_Lem_2 in uH.
           apply (H1 (exist _ u uH) i').
    + move=> H.
      destruct H as [adv [H0 [H1 [H2 H3]]]].
      (* remember (FO_NoQuant_Correct_Lem_3 _ M adv H0 H1 H2 H3) as DI; clear HeqDI.
      destruct DI; auto. *)
      simpl.
      remember (Poly_Denote D p M) as PM;destruct PM.
      simpl in *.
      unfold NoQuantExiStratCondition in H3.
      destruct (H3 (exist _ 0 (leq0n (FOExi f))) emptyTuple) as [X PX].
      exists X.
      split.
        clear H0 H2.
        unfold NoQuantAddExi in *; simpl in *.
        simpl in PX; unfold ExtendAt0N in PX; simpl in PX.
        unfold NoQuantFOBoundCondition in H1.
        assert (U D {|
                nu :=
                  exist (fun s => forall i j, ` i <= ` j -> ` (s i) <= ` (s j))
                    (fun x => exist _
                       (ExtendAt0N 0 (fun x0 => ` ((` (nu (FO_NoQuant f))) x0)) x)
                       (NoQuantAddExi_obligation_1 
                          (FOExi f) (FOUni f) (FO_NoQuant f) x))
                    (fun i j => [eta NoQuantAddExi_obligation_2 
                            (FOExi f) (FOUni f) (FO_NoQuant f) i j]);
                uniVBounds := fun x => PolyTermVSLiftExi (uniVBounds (FO_NoQuant f) x);
                exiVBounds :=
                  ExtendAt0N (PolyTermVSCastFO (PolyTerm_PolyTermVS p))
                    (fun x => PolyTermVSLiftExi (exiVBounds (FO_NoQuant f) x));
                exiFOutputBounds := emptyTuple;
                exiFInputBounds := emptyTuple;
                formula := PropTermVSLiftExi (formula (FO_NoQuant f))
              |} M adv) as u.
      2:{
        remember (H1 u) as H1'; clear HeqH1' H1.
        simpl in H1'.


 destruct H as [t ut]


      destruct HeqX.
      simpl in PXE.
      assert (ExtendAt0N 0 (fun x => ` ((` nu0) x)) (exist _ 0 (leq0n (FOExi f))) = 0) as D0.
      unfold ExtendAt0Nz
      exists ()

      simpl in H; unfold NoQuantDenotation in H.
      unfold NoQuantDenotation in *.
           simpl.

           destruct (FO_NoQuant f)
           remember (ExtendAt0N 0 (fun x0 => ` ((` nu0) x0)) (exist _ i lti)) as G.
           remember ((fun x0 => m
     (exist
        (fun n0 : nat =>
         n0 <
         ExtendAt0N 0
           (fun x1 : {n1 : nat | n1 < FOExi f} => ` ((` (nu (FO_NoQuant f))) x1))
           (exist (fun n1 : nat => n1 < (FOExi f).+1) i lti)) 
        (` x0)
        (FO_NoQuant_Correct_Lem_3 (PolyTerm_PolyTermVS p) 
           (FO_NoQuant f) i ei0 lti lti2 (` x0) (ssrfun.svalP x0))))) as m2.
           f_equal.
           f_equal.
           Check TupConcat.
           cbn.
           unfold TupConcat.
           f_equal.
           rewrite ei0.
           f_equal.
           rewrite HeqA2; clear HeqA2.
           unfold exiVAdv0.
           remember (Utils.ExtendAt0N_obligation_2 _ _).
           unfold exiVAdv.
           move: n.
           unfold ExtendAt0N.
           change (exist _ ?x _ == exist _ ?y _) with (x == y).
           rewrite dep_if_case_false.
           Check (fun x : {n : nat
            | n <
              `
              ((` (nu (FO_NoQuant f)))
                 (exist (fun n0 : nat => n0 < FOExi f) i.-1 lti2))}
          => m (exist _ (projT1 x) (FO_NoQuant_Correct_Lem_3 _ _ i lti lti2 (projT1 x) (projT2 x)))).
           apply le
           simpl in *.


unfold ExtendAt0N; simpl; rewrite dep_if_case_false; auto.
        destruct m.
        rewrite EEConvert in ei0.
        Check (FO_NoQuant_Correct_Lem_3 (n := FOExi f)
          (P := fun b n i m =>
            forall n : {n : nat | n < FOUni f - ` ((` (nu (FO_NoQuant f))) i)} -> T D,
                  exiVAdv D adv i
                    (fun x : {n0 : nat | n0 < FOUni f} =>
                      TupConcat m n
                        (exist
                          (fun n0 : nat =>
                            n0 <
                            ` ((` (nu (FO_NoQuant f))) i) +
                            (FOUni f - ` ((` (nu (FO_NoQuant f))) i))) 
                          (` x)
                          (NoQuantExiStratCondition_obligation_1 D (FOExi f) 0 emptyTuple
                              (FOUni f) (FO_NoQuant f) i m n x))) = b)
          r H3).
        Search (_ -> ex _).
        Search ex.
        remember (fun x y => ex_proj1 (H3 x y) : forall (i : {n : nat | n < FOExi f})
       (m : {n : nat | n < ` ((` (nu (FO_NoQuant f))) i)} -> T D), T D).
        Check (fun x y => exists_inhabited _ (H3 x y)).
        Check (FO_NoQuant_Correct_Lem_3 r (fun x y => ex_proj1 (H3 x y))).




        Check (ExtendAt0N 
                (fun _ => r) 
                (fun (i0 : {n : nat | n < FOExi f}) 
                     (m0 : {n : nat | n < ` ((` (nu (FO_NoQuant f))) i0)} -> T D) 
                => ` (H3 i0 m0)) i m).
        exists r.
        move=> n.
        simpl.
        unfold ExtendAt0N.
        destruct i as [i lti].
        dep_if_case (i == 0); auto.
        simpl.
        unfold exiVAdv.



          destruct u; simpl.

          assert (
          apply (H1 u i').
          apply H1.
          rewrite H.
PolyVSDenotation D (PolyTermVSCastFO (PolyTerm_PolyTermVS p)) M
    (AdviceExiExtend r adv) (` u) =
PolyVSDenotation D

        replace 
          (PolyVSDenotation D
            (exiVBounds (NoQuantAddExi (PolyTerm_PolyTermVS p) (FO_NoQuant f)) i) M
            (AdviceExiExtend r adv) (` u))
        with
          (PolyVSDenotation D (exiVBounds (FO_NoQuant f) i) (AddModelV D M r) adv (` u)).
        simpl.



        simpl.
        unfold U in u.
        rewrite <- FO_NoQuant_Correct_Lem_0_0.

        Set Printing Implicit.

        move: H0'; elim: formula0.
        intro z.
        move=> IH ca.
        simpl in ca.
        simpl.
        clear exiFInputBounds0.



      2:{

    cbn.














































Program Fixpoint LiftPolyExi 
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV} 
  (p : PolyTerm) : 
  @PolyTerm (exiV.+1) exiF exiFA uniV :=
  match p with
  | PolyFVar m => PolyFVar m
  | PolyEVar m => PolyEVar m.+1
  | PolyUVar m => PolyUVar m
  | PolyFFun i t => PolyFFun i (fun x => LiftPolyExi (t x))
  | PolyEFun i t => PolyEFun i (fun x => LiftPolyExi (t x))
  | PolyMinusOne => PolyMinusOne
  | PolyPlusOne => PolyPlusOne
  | PolyZero => PolyZero
  | PolyPlus r1 r2 => PolyPlus (LiftPolyExi r1) (LiftPolyExi r2)
  | PolyTimes r1 r2 => PolyTimes (LiftPolyExi r1) (LiftPolyExi r2)
  | PolyInd r1 r2 => PolyInd (LiftPolyExi r1) (LiftPolyExi r2)
  end.

Program Fixpoint LiftPolyUni 
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV} 
  (p : PolyTerm) : 
  @PolyTerm exiV exiF exiFA (uniV.+1) :=
  match p with
  | PolyFVar m => PolyFVar m
  | PolyEVar m => PolyEVar m
  | PolyUVar m => PolyUVar m.+1
  | PolyFFun i t => PolyFFun i (fun x => LiftPolyUni (t x))
  | PolyEFun i t => PolyEFun i (fun x => LiftPolyUni (t x))
  | PolyMinusOne => PolyMinusOne
  | PolyPlusOne => PolyPlusOne
  | PolyZero => PolyZero
  | PolyPlus r1 r2 => PolyPlus (LiftPolyUni r1) (LiftPolyUni r2)
  | PolyTimes r1 r2 => PolyTimes (LiftPolyUni r1) (LiftPolyUni r2)
  | PolyInd r1 r2 => PolyInd (LiftPolyUni r1) (LiftPolyUni r2)
  end.

Fixpoint LiftPropExi 
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (p : ZerothOrderFormula) : 
  @ZerothOrderFormula (exiV.+1) exiF exiFA uniV :=
  match p with
  | ZONot f => ZONot (LiftPropExi f)
  | ZOAnd f1 f2 => ZOAnd (LiftPropExi f1) (LiftPropExi f2)
  | ZOOr f1 f2 => ZOOr (LiftPropExi f1) (LiftPropExi f2)
  | ZOImp f1 f2 => ZOImp (LiftPropExi f1) (LiftPropExi f2)
  | ZOEq r1 r2 => ZOEq (LiftPolyExi r1) (LiftPolyExi r2)
  end.

Fixpoint LiftPropUni 
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (p : ZerothOrderFormula) : 
  @ZerothOrderFormula exiV exiF exiFA (uniV.+1) :=
  match p with
  | ZONot f => ZONot (LiftPropUni f)
  | ZOAnd f1 f2 => ZOAnd (LiftPropUni f1) (LiftPropUni f2)
  | ZOOr f1 f2 => ZOOr (LiftPropUni f1) (LiftPropUni f2)
  | ZOImp f1 f2 => ZOImp (LiftPropUni f1) (LiftPropUni f2)
  | ZOEq r1 r2 => ZOEq (LiftPolyUni r1) (LiftPolyUni r2)
  end.

Program Definition AddExiVBound 
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (p : PolyTerm)
  (n : @NoQuant exiV exiF uniV exiFA) : 
  @NoQuant (exiV.+1) exiF exiFA uniV :=
  {| nu := ExtendAt0N (uniV) (nu n)
   ; uniVBounds := fun x => LiftPolyExi (uniVBounds n x)
   ; exiVBounds := fun x => LiftPolyExi (ExtendAt0N p (exiVBounds n) x)
   ; exiFOutputBounds := fun x => LiftPolyExi (exiFOutputBounds n x)
   ; exiFInputBounds := fun x y => LiftPolyExi (exiFInputBounds n x y)
   ; formula := inrMap LiftPropExi (formula n)
  |}.
Next Obligation.
  unfold ExtendAt0N.
  dep_if_case (x == 0); auto.
  by destruct ((` (nu n)) _).
Qed.
Next Obligation.
  unfold ExtendAt0N.
  dep_if_case (j == 0); auto.
  rewrite dep_if_case_True; auto.
  destruct i;[auto|apply EEConvert.1 in H2;fcrush].
  dep_if_case (i == 0); auto.
  by destruct ((` (nu n)) _).
  by destruct (nu n); apply i0; destruct i, j.
Qed.

Program Definition AddUniVBound 
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (p : PolyTerm)
  (n : @NoQuant exiV exiF uniV exiFA) : 
  @NoQuant exiV exiF exiFA (uniV.+1) :=
  {| nu := nu n
   ; uniVBounds := fun x => LiftPolyUni (ExtendAt0N p (uniVBounds n) x)
   ; exiVBounds := fun x => LiftPolyUni (exiVBounds n x)
   ; exiFOutputBounds := fun x => LiftPolyUni (exiFOutputBounds n x)
   ; exiFInputBounds := fun x y => LiftPolyUni (exiFInputBounds n x y)
   ; formula := inrMap LiftPropUni (formula n)
  |}.
Next Obligation. by destruct (` (nu n)); auto. Qed.
Next Obligation. by destruct nu; apply i0. Qed.

Fixpoint FOExiMod 
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (f : @FirstOrderFormula exiV exiF uniV exiFA) : nat :=
  match f with
  | ZO z => exiV
  | FOExists p f => FOExiMod f
  | FOForall p f => FOExiMod f
  end.

Fixpoint FOUniMod 
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (f : @FirstOrderFormula exiV exiF uniV exiFA) : nat :=
  match f with
  | ZO z => uniV
  | FOExists p f => FOUniMod f
  | FOForall p f => FOUniMod f
  end.

Fixpoint FO_NoQuant 
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (f : @FirstOrderFormula exiV exiF uniV exiFA)
  (n : @NoQuant exiV exiF uniV exiFA) : 
  @NoQuant (FOExiMod f) exiF exiFA (FOUniMod f) :=
  match f with
  | ZO z => ZO_NoQuant z n
  | FOExists p f => FO_NoQuant f (AddExiVBound p n)
  | FOForall p f => FO_NoQuant f (AddUniVBound p n)
  end.

Program Fixpoint LiftPolyExiF 
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  {a} 
  (p : PolyTerm) : 
  @PolyTerm exiV (exiF.+1) (ExtendAt0N a exiFA) uniV :=
  match p with
  | PolyFVar m => PolyFVar m
  | PolyEVar m => PolyEVar m
  | PolyUVar m => PolyUVar m
  | PolyFFun i t => PolyFFun i (fun x => LiftPolyExiF (t x))
  | PolyEFun i t => PolyEFun i.+1 (fun x => LiftPolyExiF (t x))
  | PolyMinusOne => PolyMinusOne
  | PolyPlusOne => PolyPlusOne
  | PolyZero => PolyZero
  | PolyPlus r1 r2 => PolyPlus (LiftPolyExiF r1) (LiftPolyExiF r2)
  | PolyTimes r1 r2 => PolyTimes (LiftPolyExiF r1) (LiftPolyExiF r2)
  | PolyInd r1 r2 => PolyInd (LiftPolyExiF r1) (LiftPolyExiF r2)
  end.
Next Obligation.
  unfold ExtendAt0N in H; simpl in H.
  remember (Utils.ExtendAt0N_obligation_2 _ _ _) as P; clear HeqP; simpl in P.
  by replace H0 with P;[|apply eq_irrelevance].
Qed.

Fixpoint LiftPropExiF 
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  {a} 
  (p : ZerothOrderFormula) : 
  @ZerothOrderFormula exiV (exiF.+1) (ExtendAt0N a exiFA) uniV :=
  match p with
  | ZONot f => ZONot (LiftPropExiF f)
  | ZOAnd f1 f2 => ZOAnd (LiftPropExiF f1) (LiftPropExiF f2)
  | ZOOr f1 f2 => ZOOr (LiftPropExiF f1) (LiftPropExiF f2)
  | ZOImp f1 f2 => ZOImp (LiftPropExiF f1) (LiftPropExiF f2)
  | ZOEq r1 r2 => ZOEq (LiftPolyExiF r1) (LiftPolyExiF r2)
  end.

Program Definition AddExiFBound 
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  {uniV}
  (p : PolyTerm)
  (bs : seq (PolyTerm)) 
  (n : @NoQuant exiV exiF uniV exiFA) : 
  @NoQuant exiV (exiF.+1) (ExtendAt0N (length bs) exiFA) uniV :=
  {| nu := nu n
   ; uniVBounds := fun x => LiftPolyExiF (a := length bs) (uniVBounds n x)
   ; exiVBounds := fun x => LiftPolyExiF (a := length bs) (exiVBounds n x)
   ; exiFOutputBounds := fun x => LiftPolyExiF (a := length bs) (ExtendAt0N p (exiFOutputBounds n) x)
   ; exiFInputBounds := fun i =>
    (if i == 0 as b return (i == 0) = b -> |[ExtendAt0N (length bs) exiFA i]| -> PolyTerm
    then fun _ j => LiftPolyExiF (lnth bs j)
    else fun _ j => LiftPolyExiF (exiFInputBounds n (i.-1) j)) (erefl _)
(* fun x y => LiftPolyExiF (ExtendAt0N (lnth bs) (exiFInputBounds n) x y) *)
   ; formula := inrMap LiftPropExiF (formula n)
  |}.
Next Obligation. by destruct i. Qed.
Next Obligation.
  unfold ExtendAt0N in H.
  change (exist _ ?x _ == exist _ ?y _) with (x == y) in *.
  remember (AddExiFBound_obligation_2 _ _ _ _ _ _ _ _ _ _ _) as P; clear HeqP; simpl in P.
  rewrite dep_if_case_False in H; simpl in H.
  remember (Utils.ExtendAt0N_obligation_2 _ _ _) as Q; clear HeqQ; simpl in Q.
  by replace P with Q;[|apply eq_irrelevance].
Qed.
Next Obligation.
  unfold ExtendAt0N in H.
  by rewrite dep_if_case_True in H.
Qed.

Fixpoint SOExiFMod 
  {exiF} {exiFA : |[exiF]| -> nat}
  (f : @SecondOrderFormula exiF exiFA) : nat :=
  match f with
  | FO f => exiF
  | SOExists y bs f => SOExiFMod f
  end.

Fixpoint SOExiFAMod 
  {exiF} {exiFA : |[exiF]| -> nat}
  (f : @SecondOrderFormula exiF exiFA) : |[SOExiFMod f]| -> nat :=
  match f with
  | FO _ => exiFA
  | SOExists y bs f => SOExiFAMod f
  end.

Fixpoint SOExiMod 
  {exiF} {exiFA : |[exiF]| -> nat}
  (f : @SecondOrderFormula exiF exiFA) : nat :=
  match f with
  | FO f => FOExiMod f
  | SOExists y bs f => SOExiMod f
  end.

Fixpoint SOUniMod 
  {exiF} {exiFA : |[exiF]| -> nat}
  (f : @SecondOrderFormula exiF exiFA) : nat :=
  match f with
  | FO f => FOUniMod f
  | SOExists y bs f => SOUniMod f
  end.

Fixpoint SO_NoQuant 
  {exiF} {exiFA : |[exiF]| -> nat}
  (f : @SecondOrderFormula exiF exiFA) 
  (n : @NoQuant 0 exiF exiFA 0) : 
  @NoQuant (SOExiMod f) (SOExiFMod f) (SOExiFAMod f) (SOUniMod f) :=
  match f with
  | FO f => FO_NoQuant f n
  | SOExists y bs f => SO_NoQuant f (AddExiFBound y bs n)
  end.

End NoQuantTranslation.

Section NoQuantCorrect.

Variables D : RingData.

Program Definition ModelMance
  (M : @Sigma11Model D) : @NoQuantMance D :=
  {| freeVM := freeV_F D M
   ; freeFM := fun x => freeF_S D M x (freeFA x)
  |}.

Program Definition SONoQuant {exiF exiFA} 
  exiFOutputBounds exiFInputBounds: 
  @NoQuant 0 exiF exiFA 0 :=
  {| nu := emptyTuple
   ; uniVBounds := emptyTuple
   ; exiVBounds := emptyTuple
   ; exiFOutputBounds := exiFOutputBounds
   ; exiFInputBounds := exiFInputBounds
   ; formula := inl ()
  |}.


Fixpoint FOModelMod
  {exiV exiF} {exiFA : |[exiF]| -> nat}
  uniV
  (f : @FirstOrderFormula exiV exiF uniV exiFA) : Type :=
match f with
| ZO f => @Sigma11Model D
| FOExists p f => (|[uniV]| -> T D) -> FOModelMod uniV f
| FOForall p f => FOModelMod (uniV.+1) f
end.

Fixpoint SOModelMod 
  {exiF exiFA}
  (f : @SecondOrderFormula exiF exiFA) : Type :=
match f with
| FO f => FOModelMod 0 f
| SOExists y bs f => ((|[length bs]| -> T D) -> option (T D)) -> SOModelMod f
end.

Arguments SecondOrderFormula _ _ _ _ _ : clear implicits.
Arguments FirstOrderFormula _ _ _ _ _ _ _ : clear implicits.

Theorem SO_NOQuant_Sound 
  {exiF exiFA} 
  (M : @Sigma11Model D) 
  (f : @SecondOrderFormula exiF exiFA) ys bss :
  NoQuantDenotation D (SO_NoQuant f (SONoQuant ys bss)) (ModelMance M) ->
  SecondOrder_Denote D f M.
move: M.
induction f.
2:{
  intros M H.
  simpl in H.  
  simpl.
  remember (Poly_Denote D y M) as D1.
  destruct D1.
  remember (option_tuple
    (fun m : {n : nat | n < length bs} => Poly_Denote D (lnth bs m) M)) as D2.
  destruct D2.
  destruct H as [[exiVAdv exiFAdv] [H0 [H1 [H2 H3]]]].
  assert (0 < SOExiFMod f).
  2:{
  remember (exiFAdv (exist _ 0 H)) as f0.
  replace (length bs)
     with (SOExiFAMod f (exist (fun n0 : nat => n0 < SOExiFMod f) 0 H)) in f0.
  replace (SOExiFAMod f (exist (fun n0 : nat => n0 < SOExiFMod f) 0 H))
     with (length bs) in f0.
  Search sig.
  Unset Printing Notations.
  clear HeqD2 s0 HeqD1 s H3 H2 H1 H0 exiFAdv exiVAdv M IHf bss ys y D.
  induction f; auto.
  unfold SOExiMod.
  remember (exiFAdv 0) as Cool.
  remember (ex_proj1 H) as adv.
  destruct y.
  unfold AddExiFBound.
Admitted.

Program Definition EmptyNoQuant {freeV freeF freeFA} : @NoQuant 0 0 emptyTuple 0 :=
  {| nu := emptyTuple
   ; uniVBounds := emptyTuple
   ; exiVBounds := emptyTuple
   ; exiFOutputBounds := emptyTuple
   ; exiFInputBounds := emptyTuple
   ; formula := inl ()
  |}.

Theorem SO_NOQuant_Sound_E {freeV freeF freeFA} (M : @Sigma11Model D) 
  (f : @SecondOrderFormula 0 emptyTuple) :
  NoQuantDenotation D (SO_NoQuant f EmptyNoQuant) (ModelMance M) ->
  SecondOrder_Denote D f M.
Admitted.

Theorem SO_NOQuant_Complete_E {freeV freeF freeFA} (M : @Sigma11Model D) 
  (f : @SecondOrderFormula 0 emptyTuple) :
  SecondOrder_Denote D f M ->
  NoQuantDenotation D (SO_NoQuant f EmptyNoQuant) (ModelMance M).
Admitted.

Theorem SO_NOQuant_Correct {freeV freeF freeFA} (M : @Sigma11Model D) 
  (f : @SecondOrderFormula 0 emptyTuple) :
  SecondOrder_Denote D f M <->
  NoQuantDenotation D (SO_NoQuant f EmptyNoQuant) (ModelMance M).
Proof. qauto use: SO_NOQuant_Complete_E, SO_NOQuant_Sound_E. Qed.

End NoQuantCorrect.