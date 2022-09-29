From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.
From Coq Require Import ClassicalChoice.

Require Import CoqArith.Utils.

Require Import CoqArith.Sigma_1_1_UnFree.
Require Import Program.

Section NoQuantDef.

Variables D : RingData.

Inductive PolyTermVS {nu : seq nat} : Type :=
| PolyFVarVS : nat -> PolyTermVS
| PolyEVarVS : |[length nu]| -> PolyTermVS
| PolyUVarVS : nat -> PolyTermVS
| PolyFFunVS : forall (i a : nat), (|[a]| -> PolyTermVS) -> PolyTermVS
| PolyEFunVS : forall (i a : nat), (|[a]| -> PolyTermVS) -> PolyTermVS
| PolyMinusOneVS : PolyTermVS
| PolyPlusOneVS : PolyTermVS
| PolyZeroVS : PolyTermVS
| PolyPlusVS : PolyTermVS -> PolyTermVS -> PolyTermVS
| PolyTimesVS : PolyTermVS -> PolyTermVS -> PolyTermVS
| PolyIndVS : PolyTermVS -> PolyTermVS -> PolyTermVS.

Inductive ZerothOrderFormulaVS {nu} : Type :=
| ZONotVS : ZerothOrderFormulaVS -> ZerothOrderFormulaVS
| ZOAndVS : ZerothOrderFormulaVS -> ZerothOrderFormulaVS -> ZerothOrderFormulaVS
| ZOOrVS : ZerothOrderFormulaVS -> ZerothOrderFormulaVS -> ZerothOrderFormulaVS
| ZOImpVS : ZerothOrderFormulaVS -> ZerothOrderFormulaVS -> ZerothOrderFormulaVS
| ZOEqVS : @PolyTermVS nu -> @PolyTermVS nu -> ZerothOrderFormulaVS.

Record NoQuant : Type :=
  mkNoQuant {
    nu : seq nat;
    uniVBounds : seq (@PolyTermVS nu);
    exiVBounds : seq (@PolyTermVS nu);
    exiFOutputBounds : seq (@PolyTermVS nu);
    exiFInputBounds : seq (seq (@PolyTermVS nu));
    formula : @ZerothOrderFormulaVS nu
  }.

Record NoQuantAdvice (nu : seq nat) : Type :=
  mkNoQuantAdvice { 
    exiVAdv : forall i : |[length nu]|, (|[lnth nu i]| -> T D) -> T D;
    exiFAdv : forall i a : nat, (|[a]| -> T D) -> option (T D);
  }.

Program Fixpoint PolyVSDenotation {nu}
  (p : @PolyTermVS nu)
  (M : Sigma11Model D)
  (adv : NoQuantAdvice nu) :
  (nat -> T D) -> option (T D) :=
  match p with
  | PolyFVarVS i => fun _ => Some (V_F D M i)
  | PolyEVarVS i => fun u => Some (exiVAdv nu adv i u)
  | PolyUVarVS i => fun u => Some (u i)
  | PolyFFunVS i a t => fun u =>
    obind (fun t => F_S D M i a t) (option_tuple (fun x => PolyVSDenotation (t x) M adv u))
  | PolyEFunVS i a t => fun u =>
    obind (fun t => exiFAdv nu adv i a t) (option_tuple (fun x => PolyVSDenotation (t x) M adv u))
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

Fixpoint NoQuantZODenotation {nu}
  (p : @ZerothOrderFormulaVS nu)
  (M : Sigma11Model D)
  (adv : NoQuantAdvice nu) :
  (nat -> T D) -> Prop :=
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
  (M : Sigma11Model D) 
  {nu} (adv : NoQuantAdvice nu)
  (r : T D)
  (b : PolyTermVS) 
  (t : nat -> T D) : Prop :=
  match PolyVSDenotation b M adv t with
  | None => False
  | Some e => lt D r e
  end.

Program Definition MakeU {A} {n}
  (a : |[n]| -> A) 
  (b : nat -> A) :
  nat -> A := fun i => (
  if i < n as b return i < n = b -> A
  then fun _ => a i
  else fun _ => b (i - n)
  ) (erefl _).

Program Definition U
  (f : NoQuant)
  (M : Sigma11Model D) (adv : NoQuantAdvice (nu f)) 
  (i : nat) : Type 
  := { u : |[i]| -> T D | 
       forall j : |[i]|,
       forall v : nat -> T D, 
       InBound M adv (u j) (nth PolyZeroVS (uniVBounds f) j) (MakeU u v)
    }.

Program Definition NoQuantFormulaCondition
  (f : NoQuant) 
  (M : Sigma11Model D) (adv : NoQuantAdvice (nu f)) : Prop :=
  forall (u : U f M adv (length (uniVBounds f))), 
  NoQuantZODenotation (formula f) M adv (MakeU u (fun _ => 0%R)).

Program Definition NoQuantFOBoundCondition 
  (f : NoQuant) 
  (M : Sigma11Model D) (adv : NoQuantAdvice  (nu f)) : Prop :=
  forall i : |[length (nu f)]|, 
  forall u : U f M adv (nth 0 (nu f) i), 
  forall n : nat -> T D,
  InBound M adv (exiVAdv _ adv i u)
                (nth PolyZeroVS (exiVBounds f) i) (MakeU u n).
Next Obligation. by rewrite (lnth_nth 0) in H. Qed.

(* Note: This covers both conditions 5 and 6 in the paper *)
Program Definition NoQuantSOBoundCondition
  (f : NoQuant) (M : Sigma11Model D) (adv : NoQuantAdvice (nu f)) : Prop :=
  forall u : nat -> T D, forall i : |[length (exiFInputBounds f)]|,
  let B := PolyVSDenotation (nth (PolyPlusOneVS) (exiFOutputBounds f) i) M adv u in
  let GP := nth [::] (exiFInputBounds f) i in
  let G (j : nat) := 
    PolyVSDenotation (nth PolyPlusOneVS GP j)
                     M adv u in
  forall (t : nat -> T D) (out : T D),
  exiFAdv _ adv i (length GP) t = Some out ->
  match B with
  | None => False
  | Some B => lt D out B /\ forall x,
    match G x with
    | None => False
    | Some Gx => lt D (t x) Gx
    end
  end.

(* Program Definition NoQuantExiStratCondition 
  (f : NoQuant) 
  (M : Sigma11Model D)
  (adv : NoQuantAdvice (nu f)) : Prop :=
  forall i : |[length (nu f)]|, forall m : |[nth 0 (nu f) i]| -> T D,
  exists C, forall n : nat -> T D,
  exiVAdv _ adv i (MakeU m n) = C. *)

Definition NoQuantDenotation
  (f : NoQuant) 
  (i : Sigma11Model D): Prop :=
  exists (a : NoQuantAdvice (nu f)),
    NoQuantFormulaCondition f i a /\
    NoQuantFOBoundCondition f i a /\
    NoQuantSOBoundCondition f i a.

End NoQuantDef.

Section NoQuantTranslation.

Variables D : RingData.

Fixpoint PolyTerm_PolyTermVS (p : PolyTerm) : @PolyTermVS [::] :=
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

Definition EmptyAdvice : NoQuantAdvice D [::] :=
  {| exiVAdv := fun _ _ => 0%R
   ; exiFAdv := fun _ _ _ => None
  |}.

Definition PolyVSDenotation0
  (p : PolyTermVS)
  (M : Sigma11Model D) : option (T D) :=
  PolyVSDenotation D p M EmptyAdvice (fun _ => 0%R).

Definition PolyVSDenotation0Spec
  (p : PolyTerm) (M : Sigma11Model D) a t :
  PolyVSDenotation D (PolyTerm_PolyTermVS p) M a t =
  PolyVSDenotation0 (PolyTerm_PolyTermVS p) M.
Proof.
  unfold PolyVSDenotation0; induction p; auto; simpl.
  do 2 f_equal; by apply functional_extensionality.
  all: f_equal; auto;
       apply functional_extensionality=> x;
       f_equal; auto.
Qed.

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

Fixpoint ZerothOrder_ZerothOrderVS (p : ZerothOrderFormula) : ZerothOrderFormulaVS :=
  match p with
  | ZONot m => ZONotVS (ZerothOrder_ZerothOrderVS m)
  | ZOAnd r1 r2 => ZOAndVS (ZerothOrder_ZerothOrderVS r1) (ZerothOrder_ZerothOrderVS r2)
  | ZOOr r1 r2 => ZOOrVS (ZerothOrder_ZerothOrderVS r1) (ZerothOrder_ZerothOrderVS r2)
  | ZOImp r1 r2 => ZOImpVS (ZerothOrder_ZerothOrderVS r1) (ZerothOrder_ZerothOrderVS r2)
  | ZOEq a b => ZOEqVS (PolyTerm_PolyTermVS a) (PolyTerm_PolyTermVS b)
  end.

Definition NoQuantZODenotation0
  (p : ZerothOrderFormulaVS)
  (M : Sigma11Model D) : Prop :=
  NoQuantZODenotation D p M EmptyAdvice (fun _ => 0%R).

Definition NoQuantZODenotation0Spec
  (p : ZerothOrderFormula) (M : Sigma11Model D) a t :
  NoQuantZODenotation D (ZerothOrder_ZerothOrderVS p) M a t =
  NoQuantZODenotation0 (ZerothOrder_ZerothOrderVS p) M.
Proof.
  unfold NoQuantZODenotation0; induction p; try qauto; simpl.
  by do 2 rewrite PolyVSDenotation0Spec.
Qed.

Theorem ZerothOrder_ZerothOrderVS_Correct (p : ZerothOrderFormula) :
  ZerothOrder_Denote D p = NoQuantZODenotation0 (ZerothOrder_ZerothOrderVS p).
Proof.
  induction p; apply functional_extensionality; intro; try qauto.
  unfold NoQuantZODenotation0; simpl.
  do 2 rewrite PolyTerm_PolyTermVS_Correct.
  unfold PolyVSDenotation0.
  do 2 (destruct (PolyVSDenotation  _ _ _ _); auto).
Qed.

Program Definition ZO_NoQuant (f : ZerothOrderFormula) : NoQuant :=
  {| nu := [::]
   ; uniVBounds := [::]
   ; exiVBounds := [::]
   ; exiFOutputBounds := [::]
   ; exiFInputBounds := [::]
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
    intro t.
    by rewrite NoQuantZODenotation0Spec.
  - destruct H as [adv H].
    unfold NoQuantFormulaCondition in H.
    assert (U D (ZO_NoQuant f) M adv (length (uniVBounds (ZO_NoQuant f)))).
    unfold U.
    simpl.
    exists emptyTuple.
    move=> [j ltj]; fcrush.
    remember (H X) as H'; clear HeqH' H.
    by rewrite NoQuantZODenotation0Spec in H'.
Qed.

Lemma ZO_NoQuant_Correct_NoQuantFOBoundCondition
  (f : ZerothOrderFormula) (M : Sigma11Model D) :
  forall a, NoQuantFOBoundCondition D (ZO_NoQuant f) M a.
Proof. move=> a [i lti]; fcrush. Qed.

Lemma ZO_NoQuant_Correct_NoQuantSOBoundCondition
  (f : ZerothOrderFormula) (M : Sigma11Model D) :
  forall a, NoQuantSOBoundCondition D (ZO_NoQuant f) M a.
Proof. move=> a u [i lti]; fcrush. Qed.
(* 
Lemma ZO_NoQuant_Correct_NoQuantExiStratCondition
  (f : ZerothOrderFormula) (M : Sigma11Model D) :
  forall a, NoQuantExiStratCondition D (ZO_NoQuant f) M a.
Proof. move=> a [i lti]; fcrush. Qed. *)

Theorem ZO_NoQuant_Correct (p : ZerothOrderFormula) (M : Sigma11Model D) :
  ZerothOrder_Denote D p M <-> NoQuantDenotation D (ZO_NoQuant p) M.
Proof.
  hauto use: ZO_NoQuant_Correct_NoQuantFormulaCondition
           , ZO_NoQuant_Correct_NoQuantFOBoundCondition
           , ZO_NoQuant_Correct_NoQuantSOBoundCondition.
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

Program Fixpoint PolyTermVSLiftExi {nu}
  (p : @PolyTermVS nu):
  @PolyTermVS (0 :: nu) :=
  match p with
  | PolyFVarVS i => 
    if i == 0
    then PolyEVarVS 0
    else PolyFVarVS (i.-1)
  | PolyEVarVS i => PolyEVarVS (i.+1)
  | PolyUVarVS i => PolyUVarVS i
  | PolyFFunVS i a t => PolyFFunVS i a (fun x => PolyTermVSLiftExi (t x))
  | PolyEFunVS i a t => PolyEFunVS i a (fun x => PolyTermVSLiftExi (t x))
  | PolyMinusOneVS => PolyMinusOneVS
  | PolyPlusOneVS => PolyPlusOneVS
  | PolyZeroVS => PolyZeroVS
  | PolyPlusVS p1 p2 => PolyPlusVS (PolyTermVSLiftExi p1) (PolyTermVSLiftExi p2)
  | PolyTimesVS p1 p2 => PolyTimesVS (PolyTermVSLiftExi p1) (PolyTermVSLiftExi p2)
  | PolyIndVS p1 p2 => PolyIndVS (PolyTermVSLiftExi p1) (PolyTermVSLiftExi p2)
  end.

Fixpoint PropTermVSLiftExi {nu}
  (f : @ZerothOrderFormulaVS nu):
  @ZerothOrderFormulaVS (0 :: nu) :=
  match f with
  | ZONotVS f => ZONotVS (PropTermVSLiftExi f)
  | ZOAndVS f1 f2 => ZOAndVS (PropTermVSLiftExi f1) (PropTermVSLiftExi f2)
  | ZOOrVS f1 f2 => ZOOrVS (PropTermVSLiftExi f1) (PropTermVSLiftExi f2)
  | ZOImpVS f1 f2 => ZOImpVS (PropTermVSLiftExi f1) (PropTermVSLiftExi f2)
  | ZOEqVS r1 r2 => ZOEqVS (PolyTermVSLiftExi r1) (PolyTermVSLiftExi r2)
  end.

Program Fixpoint PolyTermVSLiftUni {nu}
  (p : @PolyTermVS nu):
  @PolyTermVS (map (fun x => x.+1) nu) :=
  match p with
  | PolyFVarVS i => 
    if i == 0
    then PolyUVarVS 0
    else PolyFVarVS (i.-1)
  | PolyEVarVS i => PolyEVarVS i
  | PolyUVarVS i => PolyUVarVS (i.+1)
  | PolyFFunVS i a t => PolyFFunVS i a (fun x => PolyTermVSLiftUni (t x))
  | PolyEFunVS i a t => PolyEFunVS i a (fun x => PolyTermVSLiftUni (t x))
  | PolyMinusOneVS => PolyMinusOneVS
  | PolyPlusOneVS => PolyPlusOneVS
  | PolyZeroVS => PolyZeroVS
  | PolyPlusVS p1 p2 => PolyPlusVS (PolyTermVSLiftUni p1) (PolyTermVSLiftUni p2)
  | PolyTimesVS p1 p2 => PolyTimesVS (PolyTermVSLiftUni p1) (PolyTermVSLiftUni p2)
  | PolyIndVS p1 p2 => PolyIndVS (PolyTermVSLiftUni p1) (PolyTermVSLiftUni p2)
  end.
Next Obligation. by rewrite map_length. Qed.

Fixpoint PropTermVSLiftUni {nu}
  (f : @ZerothOrderFormulaVS nu):
  @ZerothOrderFormulaVS (map (fun x => x.+1) nu) :=
  match f with
  | ZONotVS f => ZONotVS (PropTermVSLiftUni f)
  | ZOAndVS f1 f2 => ZOAndVS (PropTermVSLiftUni f1) (PropTermVSLiftUni f2)
  | ZOOrVS f1 f2 => ZOOrVS (PropTermVSLiftUni f1) (PropTermVSLiftUni f2)
  | ZOImpVS f1 f2 => ZOImpVS (PropTermVSLiftUni f1) (PropTermVSLiftUni f2)
  | ZOEqVS r1 r2 => ZOEqVS (PolyTermVSLiftUni r1) (PolyTermVSLiftUni r2)
  end.

Program Fixpoint PolyTermVSCastFO {nu}
  (p : @PolyTermVS [::]):
  @PolyTermVS nu :=
  match p with
  | PolyFVarVS i => PolyFVarVS i
  | PolyEVarVS i => emptyTuple i
  | PolyUVarVS i => PolyUVarVS i
  | PolyFFunVS i a t => PolyFFunVS i a (fun x => PolyTermVSCastFO (t x))
  | PolyEFunVS i a t => PolyEFunVS i a (fun x => PolyTermVSCastFO (t x))
  | PolyMinusOneVS => PolyMinusOneVS
  | PolyPlusOneVS => PolyPlusOneVS
  | PolyZeroVS => PolyZeroVS
  | PolyPlusVS p1 p2 => PolyPlusVS (PolyTermVSCastFO p1) (PolyTermVSCastFO p2)
  | PolyTimesVS p1 p2 => PolyTimesVS (PolyTermVSCastFO p1) (PolyTermVSCastFO p2)
  | PolyIndVS p1 p2 => PolyIndVS (PolyTermVSCastFO p1) (PolyTermVSCastFO p2)
  end.

Theorem PolyTermVSCastFOCastId {nu}
  (p : PolyTerm) (M : Sigma11Model D) a t :
  PolyVSDenotation D (PolyTermVSCastFO (nu := nu) (PolyTerm_PolyTermVS p)) M a t =
  PolyVSDenotation0 (PolyTerm_PolyTermVS p) M.
Proof.
  unfold PolyVSDenotation0; induction p; auto; simpl.
  do 2 f_equal; by apply functional_extensionality.
  all: f_equal; auto;
       apply functional_extensionality=> x;
       f_equal; auto.
Qed.

Definition NoQuantAddExi (b : @PolyTermVS [::]) (q : NoQuant) : NoQuant :=
  {| nu := 0 :: nu q
  ; uniVBounds := map PolyTermVSLiftExi (uniVBounds q)
  ; exiVBounds := PolyTermVSCastFO b :: map PolyTermVSLiftExi (exiVBounds q)
  ; exiFOutputBounds := map PolyTermVSLiftExi (exiFOutputBounds q)
  ; exiFInputBounds := map (map PolyTermVSLiftExi) (exiFInputBounds q)
  ; formula := PropTermVSLiftExi (formula q)
  |}.

Definition NoQuantAddUni (b : @PolyTermVS [::]) (q : NoQuant) : NoQuant :=
  {| nu := map (fun x => x.+1) (nu q)
  ; uniVBounds := PolyTermVSCastFO b :: map PolyTermVSLiftUni (uniVBounds q)
  ; exiVBounds := map PolyTermVSLiftUni (exiVBounds q)
  ; exiFOutputBounds := map PolyTermVSLiftUni (exiFOutputBounds q)
  ; exiFInputBounds := map (map PolyTermVSLiftUni) (exiFInputBounds q)
  ; formula := PropTermVSLiftUni (formula q)
  |}.

Fixpoint FO_NoQuant (f : FirstOrderFormula) : NoQuant :=
  match f with
  | ZO z => ZO_NoQuant z
  | FOExists p f => NoQuantAddExi (PolyTerm_PolyTermVS p) (FO_NoQuant f)
  | FOForall p f => NoQuantAddUni (PolyTerm_PolyTermVS p) (FO_NoQuant f)
  end.

Program Definition AdviceExiExtend
  (r : T D)
  {nu} (adv : NoQuantAdvice D nu) : 
  NoQuantAdvice D (0 :: nu) :=
  {| exiVAdv := fun i u => (
      if i == 0 as b return (i == 0) = b -> T D
      then fun _ => r
      else fun _ => exiVAdv D _ adv (i.-1) u) (erefl _)
   ; exiFAdv := exiFAdv D _ adv
  |}.
Next Obligation. destruct i; auto. Qed.

Program Definition AdviceUniExtend
  (M : Sigma11Model D)
  nu (adv : NoQuantAdvice D nu) 
  (f : forall i, (|[(lnth nu i).+1]| -> T D) -> T D)
  (H : forall i (t : |[lnth nu i]| -> T D), 
    f i (ExtendAt0N (V_F D M 0) t) = 
    exiVAdv D _ adv i t) :
  NoQuantAdvice D (map (fun x => x.+1) nu) :=
  {| exiVAdv := f
  ;  exiFAdv := exiFAdv D _ adv
  |}.
Next Obligation.
  destruct i;[fcrush|simpl in *].
  by rewrite (lnth_nth 0); rewrite (lnth_nth 0) in H.
Qed.
Next Obligation. by rewrite map_length in H0. Qed.
Next Obligation. 
  rewrite (lnth_nth 1); rewrite (lnth_nth 0) in H0; simpl in *.
  by rewrite nth_map.
Qed.

Lemma FO_NoQuant_Correct_Lem_0_0 {nu}
  (p : @PolyTermVS nu)
  (adv : NoQuantAdvice D nu) 
  (M : Sigma11Model D) (r : T D) :
  forall u,
  PolyVSDenotation D p (AddModelV D M r) adv u = 
  PolyVSDenotation D (PolyTermVSLiftExi p) M (AdviceExiExtend r adv) u.
Proof.
  elim: p; try qauto.
  - move=> n u.
    simpl.
    unfold ExtendAt0.
    dep_if_case (n == 0);try qauto.
  - move=> [s lts] u.
    simpl.
    remember (AdviceExiExtend_obligation_2 _ _ _ _) as DD0; clear HeqDD0; simpl in DD0.
    by replace DD0 with lts;[|apply eq_irrelevance].
  all: move=> i a p IH u; simpl; do 2 f_equal;
       by apply functional_extensionality.
Qed.

Lemma FO_NoQuant_Correct_Lem_0 {nu}
  (f: @ZerothOrderFormulaVS nu)
  (adv : NoQuantAdvice D nu) 
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

(* Lemma FO_NoQuant_Correct_Lem_1
  {exiV uniV}
  (adv : @NoQuantAdvice D exiV 0 uniV emptyTuple)
  (p : @PolyTermVS 0 0 0 emptyTuple)
  (M : Sigma11Model D) :
  forall u, 
  PolyVSDenotation D ( p) M adv u
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
Qed. *)

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


Lemma FO_NoQuant_Empty_InputBounds
  (f : FirstOrderFormula) :
  (exiFInputBounds (FO_NoQuant f)) = [::].
Proof. elim: f; try qauto. Qed.

Lemma FO_NoQuant_Empty_OutputBounds
  (f : FirstOrderFormula) :
  (exiFOutputBounds (FO_NoQuant f)) = [::].
Proof. elim: f; try qauto. Qed.

Lemma FO_NoQuant_Correct_NoQuantSOBoundCondition
  (f : FirstOrderFormula) (M : Sigma11Model D) a :
  NoQuantSOBoundCondition D (FO_NoQuant f) M a.
Proof.
  move=> u [i lti]; simpl.
  by rewrite FO_NoQuant_Empty_InputBounds in lti.
Qed.

Fixpoint FO_nu (f : FirstOrderFormula) : seq nat :=
  match f with
  | ZO z => [::]
  | FOExists p f => 0::FO_nu f
  | FOForall p f => map (fun x => x.+1) (FO_nu f)
  end.

Lemma FO_NoQuant_Correct_NoQuantFormulaCondition_Exi_Lem :
  forall f p,
  length (uniVBounds (FO_NoQuant (FOExists p f))) 
  = length (uniVBounds (FO_NoQuant f)).
Proof. cbn; by move=> f; rewrite map_length. Qed.

(* 
Lemma FO_NoQuant_Correct_NoQuantFormulaCondition_Exi_Lem2  {p f}:
  uniVBounds (NoQuantAddExi p f) = uniVBounds f. *)

Lemma FO_NoQuant_Correct_NoQuantFormulaCondition_Exi
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model D) r a :
  NoQuantFormulaCondition D (FO_NoQuant f) (AddModelV D M r) a <-> 
  NoQuantFormulaCondition D (FO_NoQuant (FOExists p f)) M (AdviceExiExtend r a).
Proof. 
  split; move=> H u; apply FO_NoQuant_Correct_Lem_0.
  - unfold NoQuantFormulaCondition in H.
    move: u.
    rewrite FO_NoQuant_Correct_NoQuantFormulaCondition_Exi_Lem.
    move=> u.
    destruct u as [u ltu]; simpl in *.
    assert (forall
    (j : {n : nat | n < length (uniVBounds (FO_NoQuant f))})
    (v : nat -> T D),
      InBound D (AddModelV D M r) a (u j)
        (nth PolyZeroVS (uniVBounds (FO_NoQuant f)) (` j))
        (MakeU u v)) as ltu2.
    move=> j v.
    remember (ltu j v); clear Heqi.
    change PolyZeroVS 
      with (PolyTermVSLiftExi (nu := nu (FO_NoQuant f)) PolyZeroVS) in i.
    rewrite nth_map in i.
    unfold InBound in *.
    by rewrite FO_NoQuant_Correct_Lem_0_0.
    exact (H (exist _ u ltu2)).
  - unfold NoQuantFormulaCondition in H.
    destruct u as [u ltu]; simpl in *.
    rewrite map_length in H.
    assert (forall
      (j : {n : nat | n < length (uniVBounds (FO_NoQuant f))})
      (v : nat -> T D),
        InBound D M (AdviceExiExtend r a) (u j)
          (nth PolyZeroVS
              (uniVBounds
                (NoQuantAddExi (PolyTerm_PolyTermVS p)
                    (FO_NoQuant f))) (` j)) (MakeU u v)) as ltu2;[
      |exact (H (exist _ u ltu2))].
    move=> j v.
    remember (ltu j v); clear Heqi.
    unfold InBound in *.
    auto.
    rewrite FO_NoQuant_Correct_Lem_0_0 in i.
    simpl in *.
    change PolyZeroVS 
      with (PolyTermVSLiftExi (nu := nu (FO_NoQuant f)) PolyZeroVS).
    by rewrite nth_map.
Qed.

(* Lemma URest_Lem {q j M t r a} :
  PolyVSDenotation D
    (nth PolyZeroVS (map PolyTermVSLiftExi (uniVBounds q)) j) M
    (AdviceExiExtend r a) t =
  PolyVSDenotation D (nth PolyZeroVS (uniVBounds q) j) 
    (AddModelV D M r) a t.
Proof.
  change PolyZeroVS with (PolyTermVSLiftExi PolyZeroVS).
  rewrite nth_map; simpl.
  by rewrite <- FO_NoQuant_Correct_Lem_0_0.
Qed. *)

(* Program Definition UCast1 {M b q a r i}
  (u : U D (NoQuantAddExi b q) M (AdviceExiExtend r a) (nth 0 (nu f) (i.+1))) :
  U D q (AddModelV D M r) a (nth 0 (nu f) i) := u.
Next Obligation.
  destruct u as [u pu]; simpl in *.
  remember (pu (exist _ j H) v) as pu'; clear Heqpu' pu; simpl in pu'.
  unfold InBound in *; simpl in *.
  change PolyZeroVS with (PolyTermVSLiftExi (nu := nu q) PolyZeroVS) in pu'.
  rewrite nth_map in pu'; simpl.
  by rewrite <- FO_NoQuant_Correct_Lem_0_0 in pu'.
Qed. *)

(* Program Definition UCast2 {M b q a r i}
  (u : U D q (AddModelV D M r) a i) :
  U D (NoQuantAddExi b q) M (AdviceExiExtend r a) i.+1 := u.
Next Obligation.
  destruct u as [u pu]; simpl in *.
  remember (pu (exist _ j H) v) as pu'; clear Heqpu' pu; simpl in pu'.
  unfold InBound in *; simpl in *.
  change PolyZeroVS with (PolyTermVSLiftExi (nu := nu q) PolyZeroVS).
  rewrite nth_map; simpl.
  by rewrite <- FO_NoQuant_Correct_Lem_0_0.
Qed. *)

Program Definition EmptyU {M b q a} : 
  U D (NoQuantAddExi b q) M a 0 := emptyTuple.

Lemma exiVAdvEqLem {nu a i j}
  {k : |[lnth nu i]| -> T D} 
  {l : |[lnth nu j]| -> T D}
  (e : i = j) :
  (forall x, k x = l (eq_rect _ (fun x => |[lnth nu x]|) x _ e)) ->
  exiVAdv D nu a i k = exiVAdv D nu a j l.
Proof. 
  destruct e=> e; f_equal.
  by apply functional_extensionality.
Qed.

Lemma match_lem {A B} {x y : option B} {f g} {k1 k2 : A} :
  x = y -> k1 = k2 -> f = g ->
  match x with
  | Some e => f e
  | None => k1
  end = 
  match y with
  | Some e => g e
  | None => k2
  end.
Proof. by intros [] [] []. Qed.

Lemma FO_NoQuant_Correct_NoQuantFOBoundCondition_Exi
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model D) a r :
  ((forall n, InBound D M (AdviceExiExtend r a) r (PolyTermVSCastFO (PolyTerm_PolyTermVS p)) n)
   /\ NoQuantFOBoundCondition D (FO_NoQuant f) (AddModelV D M r) a) <->
  NoQuantFOBoundCondition D (FO_NoQuant (FOExists p f)) M (AdviceExiExtend r a).
Proof.
  split.
  - move=> [H0 H1] [i lti] u n0.
    destruct i;auto;simpl in *.
    unfold NoQuantFOBoundCondition in H1.
    destruct u as [u ltu]; simpl in *.
    assert (forall (j : {n : nat | n < nth 0 (nu (FO_NoQuant f)) i})
        (v : nat -> T D),
      InBound D (AddModelV D M r) a (u j)
        (nth PolyZeroVS (uniVBounds (FO_NoQuant f)) (` j))
        (MakeU u v)) as ltu2.
      move=> j v; remember (ltu j v) as ltu'; clear Heqltu'.
      change PolyZeroVS 
      with (PolyTermVSLiftExi (nu := nu (FO_NoQuant f)) PolyZeroVS) in ltu'.
      rewrite nth_map in ltu'.
      unfold InBound in *.
      by rewrite FO_NoQuant_Correct_Lem_0_0.
    remember (H1 (exist _ i lti) (exist _ u ltu2) n0) as H1'; clear HeqH1' H1; simpl in H1'.
    simpl in *.
    unfold InBound in *.
    change PolyZeroVS 
    with (PolyTermVSLiftExi (nu := nu (FO_NoQuant f)) PolyZeroVS).
    rewrite nth_map.
    rewrite <- FO_NoQuant_Correct_Lem_0_0.
    destruct (PolyVSDenotation _ _ _ _); auto.
    remember (lt _ _ _) as H1B.
    replace (lt _ _ _) with H1B; auto.
    rewrite HeqH1B; clear HeqH1B H1' H1B.
    f_equal.
    assert (
      (exist (fun n : nat => n < length (nu (FO_NoQuant f))) i lti) = 
      (exist _ i
     (AdviceExiExtend_obligation_2 (nu (FO_NoQuant f))
        (exist _ i.+1 lti)
        (fun x=> u (exist _  (` x)
              (NoQuantFOBoundCondition_obligation_1 D
                 (NoQuantAddExi (PolyTerm_PolyTermVS p) (FO_NoQuant f)) M
                 (AdviceExiExtend r a)
                 (exist _ i.+1 lti)
                 (exist _ u ltu) x)))
        (erefl _)))) as e;[by apply subset_eq_compat|].
    apply (exiVAdvEqLem e); simpl=> x;
    f_equal;
    apply subset_eq_compat; destruct x; simpl;
    by rewrite projT1_eq_rect.
  - move=> H.
    split.
    + move=> n.
      simpl in H.
      unfold NoQuantFOBoundCondition in H.
      simpl in H.
      remember (H (exist _ 0 (ltn0Sn _)) EmptyU n) as H'; clear HeqH' H; simpl in H'.
      replace (MakeU emptyTuple n) with n in H'; auto.
      unfold MakeU in H'.
      apply functional_extensionality; move=> [|i]; auto.
    + move=> [i lti] u n; simpl in *.
      unfold NoQuantFOBoundCondition in H; simpl in H.
      destruct u as [u ltu]; simpl.
      assert (forall j v,
        InBound D M (AdviceExiExtend r a) (u j)
          (nth PolyZeroVS
              (uniVBounds
                (NoQuantAddExi (PolyTerm_PolyTermVS p)
                    (FO_NoQuant f))) (` j)) (MakeU u v)) as ltu2.
        move=> j v; remember (ltu j v) as ltu'; clear Heqltu'.
        unfold InBound in *; simpl in *.
        change PolyZeroVS 
        with (PolyTermVSLiftExi (nu := nu (FO_NoQuant f)) PolyZeroVS).
        rewrite nth_map.
        by rewrite FO_NoQuant_Correct_Lem_0_0 in ltu'.
      remember (H (exist _ (i.+1) lti) (exist _ u ltu2) n) as H'; clear HeqH' H; simpl in H'.
      remember (InBound _ _ _ _ _ _) as H1B.
      replace (InBound _ _ _ _ _ _) with H1B; auto.
      rewrite HeqH1B; clear HeqH1B H1B H'.
      unfold InBound.
      apply match_lem; auto.
      change (PolyZeroVS (nu := 0 :: nu (FO_NoQuant f))) 
        with (PolyTermVSLiftExi (nu := nu (FO_NoQuant f)) (PolyZeroVS));rewrite nth_map.
      by rewrite <- FO_NoQuant_Correct_Lem_0_0.
      f_equal.
      assert (
        (exist (fun n0 : nat => n0 < length (nu (FO_NoQuant f)))
     i
     (AdviceExiExtend_obligation_2 (nu (FO_NoQuant f))
        (exist _ i.+1 lti)
        (fun x => u (exist _
              (` x)
              (NoQuantFOBoundCondition_obligation_1 D
                 (NoQuantAddExi (PolyTerm_PolyTermVS p)
                    (FO_NoQuant f)) M
                 (AdviceExiExtend r a)
                 (exist _ i.+1 lti)
                 (exist _ u ltu2) x))) (erefl _)))
        = (exist (fun n : nat => n < length (nu (FO_NoQuant f))) i lti)) as e;[by apply subset_eq_compat|].
      apply (exiVAdvEqLem e); simpl=> x.
      f_equal.
      apply subset_eq_compat.
      by rewrite projT1_eq_rect.
Qed.

Lemma FO_NoQuant_Correct_NoQuantSOBoundCondition_Exi
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model D) a r :
  NoQuantSOBoundCondition D (FO_NoQuant f) (AddModelV D M r) a <->
  NoQuantSOBoundCondition D (FO_NoQuant (FOExists p f)) M (AdviceExiExtend r a).
Proof.
  split=> H;[|apply FO_NoQuant_Correct_NoQuantSOBoundCondition].
  move=> u [i lti]; simpl.
  by rewrite FO_NoQuant_Empty_InputBounds in lti.
Qed.

(* Lemma FO_NoQuant_Correct_NoQuantExiStratCondition_Exi
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model D) a r :
  NoQuantExiStratCondition D (FO_NoQuant f) (AddModelV D M r) a <->
  NoQuantExiStratCondition D (FO_NoQuant (FOExists p f)) M (AdviceExiExtend r a).
Proof.
  split;move=> H.
  - unfold NoQuantExiStratCondition in *.
    move=> [i lti] m; simpl.
    destruct i;[by exists r|simpl in *].
    remember (H (exist _ i lti) m) as H'; clear HeqH' H; simpl in H'.
    destruct H' as [C H].
    exists C.
    move=> n.
    remember (H n) as HB1; clear HeqHB1 H.
    remember (exiVAdv _ _ _ _ _) as HB2.
    rewrite <- HB1; rewrite HeqHB2; auto.
    assert ((exist (fun n0 : nat => n0 < length (nu (FO_NoQuant f))) i
      (AdviceExiExtend_obligation_2 (nu (FO_NoQuant f))
        (exist _ i.+1 lti) (fun x => MakeU m n (` x)) (erefl _))) = 
      (exist (fun n0 : nat => n0 < length (nu (FO_NoQuant f))) i lti)) as e;[by apply subset_eq_compat|].
    apply (exiVAdvEqLem e); simpl=> x.
    f_equal.
    by rewrite projT1_eq_rect.
  - unfold NoQuantExiStratCondition in *.
    move=> i m.
    simpl in H.
    destruct i as [i lti].
    remember (H (exist _ (i.+1) lti) m) as H'; clear HeqH' H.
    destruct H' as [C H].
    exists C.
    move=> n.
    remember (H n) as HB1; clear HeqHB1 H.
    remember (exiVAdv _ _ _ _ _) as HB2.
    rewrite <- HB1; rewrite HeqHB2; auto.
    assert ((exist (fun n0 : nat => n0 < length (nu (FO_NoQuant f))) i lti)
      = (exist (fun n0 : nat => n0 < length (nu (FO_NoQuant f))) i
      (AdviceExiExtend_obligation_2 (nu (FO_NoQuant f))
        (exist _ i.+1 lti) (fun x => MakeU m n (` x)) (erefl _)))) as e;[by apply subset_eq_compat|].
    apply (exiVAdvEqLem e); simpl=> x.
    f_equal.
    by rewrite projT1_eq_rect.
Qed. *)

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

Program Definition AdviceDropExi {nu}
  (adv : NoQuantAdvice D (0 :: nu)) :=
  {| exiVAdv := fun i => exiVAdv D _ adv (i.+1) 
   ; exiFAdv := exiFAdv D _ adv
  |}.

Theorem AdviceDropExi_Spec {nu}
  (adv : NoQuantAdvice D (0 :: nu)) :
  adv = 
  (AdviceExiExtend (exiVAdv D _ adv (exist _ 0 (ltn0Sn _)) emptyTuple)
                   (AdviceDropExi adv)).
Proof.
  replace adv with {| exiVAdv := exiVAdv _ _ adv;
                     exiFAdv := exiFAdv _ _ adv |};[|by destruct adv].
  unfold AdviceDropExi.
  unfold AdviceExiExtend.
  f_equal.
  apply functional_extensionality_dep=> x.
  apply functional_extensionality_dep=> u.
  destruct x as [x ltx].
  dep_if_case (x == 0); auto.
  - destruct x;[|fcrush].
    assert (
      exist (fun n : nat => n < length (0 :: nu)) 0 ltx =
      exist _ 0 (ltn0Sn
          ((fix length (l : seq nat) : nat :=
              match l with
              | [::] => 0
              | _ :: l' => (length l').+1
              end) nu))) as e;[by apply subset_eq_compat|].
    destruct adv; apply (exiVAdvEqLem e); simpl=> x.
    destruct x;fcrush.
  - destruct x;[fcrush|]; simpl.
    assert (
      exist (fun n : nat => n < (length nu).+1) x.+1 ltx =
      exist (fun n : nat => n < (length nu).+1) x.+1
     (AdviceExiExtend_obligation_2 (AdviceDropExi_obligation_1 nu)
        (exist (fun n : nat => n < (length nu).+1) x.+1 ltx) u H)) as e;[by apply subset_eq_compat|].
    apply (exiVAdvEqLem (a := adv) e).
    move=> [x0 ltx0].
    f_equal.
    apply subset_eq_compat.
    by rewrite (projT1_eq_rect (e := e)).
Qed.

Theorem lt_dec_true_true {a b}
  (e : lt_dec D a b = true) : lt D a b.
Proof.
  unfold lt_dec in e.
  by destruct (lt_total D a b) eqn:ltP.
Qed.

Theorem lt_dec_false_false {a b}
  (e : lt_dec D a b = false) : ~ (lt D a b).
Proof.
  unfold lt_dec in e.
  destruct (lt_total D a b) eqn:ltP;[fcrush|].
  destruct (so D).
  unfold Irreflexive, Reflexive, complement in StrictOrder_Irreflexive.
  unfold Transitive in StrictOrder_Transitive.
  destruct s;[qauto|].
  move=> l2.
  apply (StrictOrder_Irreflexive b); qauto.
Qed.

Program Definition Uni_Advice  {nu s}
  (H : {r : T D | lt D r s} ->
       forall i : |[length nu]|, (|[lnth nu i]| -> T D) -> T D)
  (i : |[length (map (fun x => x.+1) nu)]|)
  (t : |[lnth (map (fun x => x.+1) nu) i]| -> T D) : T D := (
if lt_dec D (t 0) s as b return lt_dec D (t 0) s = b -> T D
then fun p => H (exist _ (t 0) (lt_dec_true_true p)) i (fun x => t (x.+1))
else fun _ => 0%R) (erefl _).
Next Obligation. by rewrite (lnth_nth 1) nth_map. Qed.
Next Obligation. clear t p; by rewrite map_length in H0. Qed.
Next Obligation.
  rewrite (lnth_nth 1) nth_map; simpl.
  rewrite (lnth_nth 0) in H0; simpl in H0.
  sfirstorder.
Qed.

Theorem lt_ltdec {a b} :
  lt D a b -> lt_dec D a b = true.
Proof.
  move=> ltab.
  unfold lt_dec.
  destruct (lt_total D a b); auto.
  remember (so D).
  destruct s0.
  destruct s.
  destruct e.
  unfold Irreflexive, Reflexive, complement in StrictOrder_Irreflexive; qauto.
  unfold Irreflexive, Reflexive, complement in StrictOrder_Irreflexive; qauto.
Qed. 

Lemma FO_NoQuant_Correct_Lem_4_0
  nu p
  (M: Sigma11Model D)
  (s: T D)
  (adv: {r : T D | lt D r s} -> NoQuantAdvice D nu)
  (u: nat -> T D)
  (ltu0: lt D (u 0) s) :
PolyVSDenotation D p (AddModelV D M (u 0))
    (adv (exist ((lt D)^~ s) (u 0) ltu0)) (fun x : nat => u x.+1) =
PolyVSDenotation D (PolyTermVSLiftUni p) M
    {|
      exiVAdv := Uni_Advice (fun x => exiVAdv D nu (adv x));
      exiFAdv := exiFAdv D nu (adv (exist ((lt D)^~ s) (u 0) ltu0))
    |} u.
Proof.
  elim:p; try qauto.
  - move=> n; by destruct n.
  - move=> s'.
    simpl.
    f_equal.
    unfold Uni_Advice; simpl.
    rewrite dep_if_case_true.
    by apply lt_ltdec.
    move=> H0.
    replace ltu0 with (lt_dec_true_true H0);[|apply proof_irrelevance].
    assert (s' = (exist (fun n : nat => n < length nu) (` s')
      (Uni_Advice_obligation_2 nu s
          (exist (fun n : nat => n < length [seq x.+1 | x <- nu]) (` s')
            (PolyTermVSLiftUni_obligation_1 nu (PolyEVarVS s') s' (erefl (PolyEVarVS s'))))
          (fun x => u (` x)) H0))) as e;[destruct s'; by apply subset_eq_compat|].
    apply (exiVAdvEqLem e).
    move=> x; f_equal.
    by rewrite projT1_eq_rect.
  - move=> i a p IH.
    simpl.
    do 2 f_equal.
    apply functional_extensionality; auto.
  - move=> i a p IH.
    simpl.
    do 2 f_equal.
    apply functional_extensionality; auto.
Qed.

Lemma FO_NoQuant_Correct_Lem_4_0_1 {k} {e}
  nu p
  (M: Sigma11Model D)
  (s: T D)
  (adv: {r : T D | lt D r s} -> NoQuantAdvice D nu)
  (u: |[k.+1]| -> T D)
  (v: nat -> T D)
  (ltu0: lt D (u (exist _ 0 e)) s) :
PolyVSDenotation D p (AddModelV D M (u (exist _ 0 e)))
    (adv (exist ((lt D)^~ s) (u (exist _ 0 e)) ltu0)) (MakeU (fSeqRest u) v) =
PolyVSDenotation D (PolyTermVSLiftUni p) M
    {|
      exiVAdv := Uni_Advice (fun x => exiVAdv D nu (adv x));
      exiFAdv := exiFAdv D nu (adv (exist ((lt D)^~ s) (u (exist _ 0 e)) ltu0))
    |} (MakeU u v).
Proof.
  assert (u (exist _ 0 e) = MakeU u v 0).
    unfold MakeU; simpl.
    f_equal; by apply subset_eq_compat.
  elim:p; try qauto.
  - move=> n; destruct n; auto.
    simpl.
    f_equal.
    by rewrite <- H.
  - move=> s'.
    simpl.
    f_equal.
    unfold Uni_Advice; simpl.
    rewrite dep_if_case_true.
    rewrite <- H.
    by apply lt_ltdec.
    move=> H0.
    replace (adv (exist ((lt D)^~ s) (u (exist _ 0 e)) ltu0)) 
       with (adv (exist ((lt D)^~ s) (MakeU u v 0) (lt_dec_true_true H0))).
    assert (s' = (exist (fun n : nat => n < length nu) (` s')
     (Uni_Advice_obligation_2 nu s
        (exist _ (` s')
           (PolyTermVSLiftUni_obligation_1 nu (PolyEVarVS s') s'
              (erefl (PolyEVarVS s'))))
        (fun x => MakeU u v (` x)) H0))) as e2;[destruct s'; by apply subset_eq_compat|].
    apply (exiVAdvEqLem e2).
    move=> x; f_equal.
    by rewrite projT1_eq_rect.
    f_equal; by apply subset_eq_compat.
  - move=> i a p IH.
    simpl.
    do 2 f_equal.
    apply functional_extensionality; auto.
  - move=> i a p IH.
    simpl.
    do 2 f_equal.
    apply functional_extensionality; auto.
Qed.

Lemma FO_NoQuant_Correct_Lem_4
  nu f
  (M: Sigma11Model D)
  (s: T D)
  (adv: {r : T D | lt D r s} -> NoQuantAdvice D nu)
  (u: nat -> T D)
  (ltu0: lt D (u 0) s) :
NoQuantZODenotation D f (AddModelV D M (u 0))
  (adv (exist ((lt D)^~ s) (u 0) ltu0)) (fun x : nat => u x.+1) <->
NoQuantZODenotation D (PropTermVSLiftUni f) M
  {| exiVAdv := Uni_Advice (fun x => exiVAdv D nu (adv x));
     exiFAdv := exiFAdv D nu (adv (exist ((lt D)^~ s) (u 0) ltu0))
  |} u.
Proof.
  elim: f; try qauto.
  move=> p0 p1.
  simpl.
  by do 2 rewrite FO_NoQuant_Correct_Lem_4_0.
Qed.


Lemma FO_NoQuant_Correct_Lem_4_0_2 {k}
  nu p
  (M: Sigma11Model D)
  (s: T D)
  (adv: {r : T D | lt D r s} -> NoQuantAdvice D nu)
  (u: |[k.+1]| -> T D)
  (v: nat -> T D)
  (ltu0: lt D (u (exist _ 0 (ltn0Sn _))) s) :
NoQuantZODenotation D p (AddModelV D M (u (exist _ 0 (ltn0Sn _))))
    (adv (exist ((lt D)^~ s) (u (exist _ 0 (ltn0Sn _))) ltu0)) (MakeU (fSeqRest u) v) =
NoQuantZODenotation D (PropTermVSLiftUni p) M
    {|
      exiVAdv := Uni_Advice (fun x => exiVAdv D nu (adv x));
      exiFAdv := exiFAdv D nu (adv (exist ((lt D)^~ s) (u (exist _ 0 (ltn0Sn _))) ltu0))
    |} (MakeU u v).
Proof.
  elim: p; try qauto.
  move=> p0 p1.
  simpl.
  by do 2 rewrite FO_NoQuant_Correct_Lem_4_0_1.
Qed.

Lemma FO_NoQuant_Correct_Lem_5_1 {p M adv1 adv2 u} :
  PolyVSDenotation D (PolyTermVSLiftUni (PolyTerm_PolyTermVS p)) M adv1 u =
  PolyVSDenotation D (PolyTermVSLiftUni (PolyTerm_PolyTermVS p)) M adv2 u.
Proof.
  induction p; try qauto.
  simpl.
  do 2 f_equal.
  by apply functional_extensionality.
Qed.

(* Lemma FO_NoQuant_Correct_Lem_4_0_1
  nu p
  (M: Sigma11Model D)
  (s: T D)
  (adv: {r : T D | lt D r s} -> NoQuantAdvice D nu)
  (u: nat -> T D)
  (ltu0: lt D (u 0) s) :
PolyVSDenotation D (PolyTerm_PolyTermVS p) (AddModelV D M (u 0))
    (adv (exist ((lt D)^~ s) (u 0) ltu0)) (fun x : nat => u x.+1) =
PolyVSDenotation D (PolyTermVSLiftUni (PolyTerm_PolyTermVS p)) M
    {|
      exiVAdv := Uni_Advice (fun x => exiVAdv D nu (adv x));
      exiFAdv := fun=> (fun a : nat => fun=> None)
    |} u.
Proof. *)

Lemma FO_NoQuant_Correct_Lem_5_0 {z M adv1 adv2 u} :
  NoQuantZODenotation D (PropTermVSLiftUni (ZerothOrder_ZerothOrderVS z)) M adv1 u =
  NoQuantZODenotation D (PropTermVSLiftUni (ZerothOrder_ZerothOrderVS z)) M adv2 u.
Proof.
  induction z; try qauto.
  simpl.
  by do 2 rewrite (FO_NoQuant_Correct_Lem_5_1 (adv1 := adv1) (adv2 := adv2)).
Qed.

Lemma FO_NoQuant_Correct_Lem_5_3 {p M exiV exiF1 exiF2 u} :
  PolyVSDenotation D (PolyTermVSLiftExi (PolyTerm_PolyTermVS p)) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  PolyVSDenotation D (PolyTermVSLiftExi (PolyTerm_PolyTermVS p)) M
        {| exiVAdv := exiV; exiFAdv := exiF2 |} u.
Proof.
  induction p; try qauto.
  simpl.
  do 2 f_equal.
  by apply functional_extensionality.
Qed.

Lemma FO_NoQuant_Correct_Lem_5_2 {z M exiV exiF1 exiF2 u} :
  NoQuantZODenotation D (PropTermVSLiftExi (ZerothOrder_ZerothOrderVS z)) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  NoQuantZODenotation D (PropTermVSLiftExi (ZerothOrder_ZerothOrderVS z)) M
        {| exiVAdv := exiV; exiFAdv := exiF2 |} u.
Proof.
  induction z; try qauto.
  simpl.
  by do 2 rewrite (FO_NoQuant_Correct_Lem_5_3 (exiF1 := exiF1) (exiF2 := exiF2)).
Qed.

Lemma FO_NoQuant_Correct_Lem_6_0 {nu}
  (p : @PolyTermVS _)
  (adv : NoQuantAdvice D (0 :: nu))
  (M : Sigma11Model D) :
  forall u,
  PolyVSDenotation D p (AddModelV D M (exiVAdv D _ adv (exist _ 0 (ltn0Sn _)) (fun x => u (` x)))) (AdviceDropExi adv) u = 
  PolyVSDenotation D (PolyTermVSLiftExi p) M adv u.
Proof.
  elim: p; try qauto.
  - move=> n u.
    simpl.
    unfold ExtendAt0.
    dep_if_case (n == 0);try qauto.
    rewrite H; simpl.
    f_equal.
    unfold AdviceDropExi_obligation_1.
    remember (ltn0Sn _) as D0; clear HeqD0.
    remember (PolyTermVSLiftExi_obligation_1 nu) as D1; clear HeqD1.
    unfold length in D1.
    by replace D0 with D1;[|apply eq_irrelevance].
  - move=> i a p IH u.
    simpl.
    do 2 f_equal.
    by apply functional_extensionality.
  - move=> i a p IH u.
    simpl.
    do 2 f_equal.
    by apply functional_extensionality.
Qed.

Lemma FO_NoQuant_Correct_Lem_6 {nu}
  p
  (adv : NoQuantAdvice D (0 :: nu))
  (M : Sigma11Model D) :
  forall u,
  NoQuantZODenotation D p (AddModelV D M (exiVAdv D _ adv (exist _ 0 (ltn0Sn _)) (fun x => u (` x)))) (AdviceDropExi adv) u = 
  NoQuantZODenotation D (PropTermVSLiftExi p) M adv u.
Proof.
  elim: p; try qauto.
  move=> p1 p2 u.
  simpl.
  by do 2 rewrite FO_NoQuant_Correct_Lem_6_0.
Qed.

Program Definition AdviceDropUni {nu} r
  (adv : NoQuantAdvice D (map (fun x => x.+1) nu)) :
  NoQuantAdvice D nu :=
  {| exiVAdv := fun i t => exiVAdv D _ adv i (ExtendAt0N r t)
   ; exiFAdv := exiFAdv D _ adv
  |}.
Next Obligation. by rewrite map_length. Qed.
Next Obligation.
  rewrite (lnth_nth 1) nth_map in H.
  by rewrite (lnth_nth 0).
Qed.

Lemma FO_NoQuant_Correct_Lem_7_0 {nu}
  (p : @PolyTermVS _)
  (adv : NoQuantAdvice D (map (fun x => x.+1) nu))
  (M : Sigma11Model D) :
  forall u,
  PolyVSDenotation D p (AddModelV D M (u 0)) (AdviceDropUni (u 0) adv) (fun x => u (x.+1)) = 
  PolyVSDenotation D (PolyTermVSLiftUni p) M adv u.
Proof.
  elim: p; try qauto.
  - move=> n u.
    simpl.
    unfold ExtendAt0.
    dep_if_case (n == 0);try qauto.
  - move=> s u.
    simpl.
    f_equal.
    assert  
      (exist (fun n => n < length [seq x.+1 | x <- nu]) (` s)
        (AdviceDropUni_obligation_1 nu s (fun x => u (` x).+1)) =
      exist (fun n => n < length [seq x.+1 | x <- nu]) (` s)
        (PolyTermVSLiftUni_obligation_1 nu (PolyEVarVS s) s (erefl (PolyEVarVS s)))) as e;[by apply subset_eq_compat|].
    apply (exiVAdvEqLem e)=> x.
    unfold ExtendAt0N; simpl.
    destruct x; simpl.
    by destruct x;rewrite projT1_eq_rect.
  - move=> i a p IH u.
    simpl.
    do 2 f_equal.
    by apply functional_extensionality.
  - move=> i a p IH u.
    simpl.
    do 2 f_equal.
    by apply functional_extensionality.
Qed.

Lemma FO_NoQuant_Correct_Lem_7_0_A {nu r}
  p
  (adv : NoQuantAdvice D (map (fun x => x.+1) nu))
  (M : Sigma11Model D) :
  forall u,
  PolyVSDenotation D p (AddModelV D M r) (AdviceDropUni r adv) u = 
  PolyVSDenotation D (PolyTermVSLiftUni p) M adv (ExtendAt0 r u).
Proof.
  move=> u.
  remember (ExtendAt0 r u) as u'.
  replace u with (fun x => u' (x.+1));[|qauto].
  replace r with (u' 0);[|qauto].
  by rewrite FO_NoQuant_Correct_Lem_7_0.
Qed.

Lemma FO_NoQuant_Correct_Lem_7 {nu}
  p
  (adv : NoQuantAdvice D (map (fun x => x.+1) nu))
  (M : Sigma11Model D) :
  forall u,
  NoQuantZODenotation D p (AddModelV D M (u 0)) (AdviceDropUni (u 0) adv) (fun x => u (x.+1)) = 
  NoQuantZODenotation D (PropTermVSLiftUni p) M adv u.
Proof.
  elim: p; try qauto.
  move=> p1 p2 u.
  simpl.
  by do 2 rewrite FO_NoQuant_Correct_Lem_7_0.
Qed.

Lemma FO_NoQuant_Correct_Lem_7_A {nu r}
  p
  (adv : NoQuantAdvice D (map (fun x => x.+1) nu))
  (M : Sigma11Model D) :
  forall u,
  NoQuantZODenotation D p (AddModelV D M r) (AdviceDropUni r adv) u = 
  NoQuantZODenotation D (PropTermVSLiftUni p) M adv (ExtendAt0 r u).
Proof.
  move=> u.
  remember (ExtendAt0 r u) as u'.
  replace u with (fun x => u' (x.+1));[|qauto].
  replace r with (u' 0);[|qauto].
  by rewrite FO_NoQuant_Correct_Lem_7.
Qed.

Lemma FO_NoQuant_Correct_Lem_5 {f M exiV exiF1 u} :
  NoQuantZODenotation D (formula (FO_NoQuant f)) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  NoQuantZODenotation D (formula (FO_NoQuant f)) M
        {| exiVAdv := exiV; exiFAdv := fun=> (fun a : nat => fun=> None) |} u.
Proof.
  move: M u.
  induction f; simpl=> M u.
  - by do 2 rewrite NoQuantZODenotation0Spec.
  - do 2 rewrite <- (FO_NoQuant_Correct_Lem_6 (formula (FO_NoQuant f)) _ M).
    simpl; by rewrite IHf.
  - do 2 rewrite <- (FO_NoQuant_Correct_Lem_7 (formula (FO_NoQuant f)) _ M).
    simpl; by rewrite IHf.
Qed.

Lemma FO_NoQuant_Correct_Lem_5_5 {f M exiV exiF1 u} :
  NoQuantZODenotation D (PropTermVSLiftUni (formula (FO_NoQuant f))) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  NoQuantZODenotation D (PropTermVSLiftUni (formula (FO_NoQuant f))) M
        {| exiVAdv := exiV; exiFAdv := fun=> (fun a : nat => fun=> None) |} u.
Proof.
  do 2 rewrite <- (FO_NoQuant_Correct_Lem_7 (formula (FO_NoQuant f)) _ M).
  by do 2 rewrite FO_NoQuant_Correct_Lem_5.
Qed.

Lemma FO_NoQuant_Correct_Lem_8 {u f j M exV1 exF1 exF2} :
  PolyVSDenotation D (nth PolyZeroVS (uniVBounds (FO_NoQuant f)) j) M
    {| exiVAdv := exV1;
       exiFAdv := exF1
    |} u =
  PolyVSDenotation D (nth PolyZeroVS (uniVBounds (FO_NoQuant f)) j) M
    {| exiVAdv := exV1;
       exiFAdv := exF2
    |} u.
Proof.
  move: j u M; induction f.
  - by destruct j.
  - move=> j u M.
    simpl.
    change PolyZeroVS with (PolyTermVSLiftExi (nu := nu (FO_NoQuant f)) (PolyZeroVS)).
    rewrite nth_map.
    do 2 rewrite <- (FO_NoQuant_Correct_Lem_6_0 (nth PolyZeroVS (uniVBounds (FO_NoQuant f)) j)).
    apply IHf.
  - move=> j u M.
    simpl.
    destruct j; simpl.
    by do 2 rewrite PolyTermVSCastFOCastId.
    change PolyZeroVS with (PolyTermVSLiftUni (nu := nu (FO_NoQuant f)) PolyZeroVS).
    rewrite nth_map.
    do 2 rewrite <- (FO_NoQuant_Correct_Lem_7_0 (nth PolyZeroVS (uniVBounds (FO_NoQuant f)) j)).
    apply IHf.
Qed.

Lemma FO_NoQuant_Correct_Lem_10 {u f j M exV1 exF1 exF2} :
  PolyVSDenotation D (nth PolyZeroVS (exiVBounds (FO_NoQuant f)) j) M
    {| exiVAdv := exV1;
       exiFAdv := exF1
    |} u =
  PolyVSDenotation D (nth PolyZeroVS (exiVBounds (FO_NoQuant f)) j) M
    {| exiVAdv := exV1;
       exiFAdv := exF2
    |} u.
Proof.
  move: j u M; induction f.
  - by destruct j.
  - move=> j u M.
    simpl.
    destruct j; simpl.
    by do 2 rewrite PolyTermVSCastFOCastId.
    change PolyZeroVS with (PolyTermVSLiftExi (nu := nu (FO_NoQuant f)) (PolyZeroVS)).
    rewrite nth_map.
    do 2 rewrite <- (FO_NoQuant_Correct_Lem_6_0 (nth PolyZeroVS (exiVBounds (FO_NoQuant f)) j)).
    apply IHf.
  - move=> j u M.
    simpl.
    change PolyZeroVS with (PolyTermVSLiftUni (nu := nu (FO_NoQuant f)) PolyZeroVS).
    rewrite nth_map.
    do 2 rewrite <- (FO_NoQuant_Correct_Lem_7_0 (nth PolyZeroVS (exiVBounds (FO_NoQuant f)) j)).
    apply IHf.
Qed.

Lemma FO_NoQuant_Correct_Lem_8_5 {f M exiV exiF1 exiF2 j u} :
  PolyVSDenotation D (PolyTermVSLiftUni (nth PolyZeroVS (uniVBounds (FO_NoQuant f)) j)) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  PolyVSDenotation D (PolyTermVSLiftUni (nth PolyZeroVS (uniVBounds (FO_NoQuant f)) j)) M
        {| exiVAdv := exiV; exiFAdv := exiF2 |} u.
Proof.
  do 2 rewrite <- (FO_NoQuant_Correct_Lem_7_0 (nth PolyZeroVS (uniVBounds (FO_NoQuant f)) j)).
  apply FO_NoQuant_Correct_Lem_8.
Qed.


Lemma FO_NoQuant_Correct_Lem_10_5 {f M exiV exiF1 exiF2 j u} :
  PolyVSDenotation D (PolyTermVSLiftUni (nth PolyZeroVS (exiVBounds (FO_NoQuant f)) j)) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  PolyVSDenotation D (PolyTermVSLiftUni (nth PolyZeroVS (exiVBounds (FO_NoQuant f)) j)) M
        {| exiVAdv := exiV; exiFAdv := exiF2 |} u.
Proof.
  do 2 rewrite <- (FO_NoQuant_Correct_Lem_7_0 (nth PolyZeroVS (exiVBounds (FO_NoQuant f)) j)).
  apply FO_NoQuant_Correct_Lem_10.
Qed.

Program Definition FO_NoQuant_Correct_Lem_9 {A s i} (e : i < length s)
  (u : |[nth 0 [seq x.+1 | x <- s] i]| -> A) : |[(nth 0 s i).+1]| -> A := u.
Next Obligation.
  assert (i < length [seq x0.+1 | x0 <- s]);[by rewrite map_length|].
  replace (nth _ _ _) with (lnth [seq x0.+1 | x0 <- s] (exist _ i H0)).
  by rewrite lnth_map (lnth_nth 0).
  by rewrite (lnth_nth 0).
Qed.

Program Definition FO_NoQuant_Correct_Lem_9_0 {A s i} (e : i < length s)
  (u : |[(nth 0 s i).+1]| -> A) : |[nth 0 [seq x.+1 | x <- s] i]| -> A := u.
Next Obligation.
  assert (i < length [seq x0.+1 | x0 <- s]);[by rewrite map_length|].
  replace (nth _ _ _) with (lnth [seq x0.+1 | x0 <- s] (exist _ i H0)) in H.
  by rewrite lnth_map (lnth_nth 0) in H.
  by rewrite (lnth_nth 0).
Qed.

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
      destruct fd as [adv [H0 [H1 H2]]].
      exists (AdviceExiExtend r adv).
      split;[|split];auto.
      * by apply (FO_NoQuant_Correct_NoQuantFormulaCondition_Exi p).
      * apply (FO_NoQuant_Correct_NoQuantFOBoundCondition_Exi p).
        split; auto.
        move=> n.
        unfold InBound.
        rewrite PolyTermVSCastFOCastId; rewrite <- PolyTerm_PolyTermVS_Correct.
        by rewrite <- HeqPM.
      * by apply (FO_NoQuant_Correct_NoQuantSOBoundCondition_Exi p).
    + move=> [adv [H0 [H1 H2]]].
      simpl in adv.
      rewrite (AdviceDropExi_Spec adv) in H0, H1, H2.
      apply (FO_NoQuant_Correct_NoQuantFormulaCondition_Exi p) in H0.
      apply (FO_NoQuant_Correct_NoQuantFOBoundCondition_Exi p) in H1.
      apply (FO_NoQuant_Correct_NoQuantSOBoundCondition_Exi p) in H2.
      simpl.
      remember (Poly_Denote D p M) as PM; destruct PM.
      exists (exiVAdv D _ adv (exist _ 0 (ltn0Sn _)) emptyTuple).
      split;[|qauto].
        clear H2 H0; destruct H1 as [LT _].
        remember (LT (fun _ => 0%R)) as LT'; clear HeqLT' LT.
        unfold InBound in LT'.
        rewrite PolyTermVSCastFOCastId in LT'.
        rewrite <- PolyTerm_PolyTermVS_Correct in LT'.
        by rewrite <- HeqPM in LT'.
      clear H2 H0; destruct H1 as [LT _].
      remember (LT (fun _ => 0%R)) as LT'; clear HeqLT' LT.
      unfold InBound in LT'.
      rewrite PolyTermVSCastFOCastId in LT'.
      rewrite <- PolyTerm_PolyTermVS_Correct in LT'.
      by rewrite <- HeqPM in LT'.
  - move=> p f IH M.
    simpl.
    destruct (Poly_Denote D p M) eqn:PM; split; try qauto.
    + move=> FO.
      assert (
        forall r : T D,
          lt D r s ->
          NoQuantDenotation D (FO_NoQuant f) (AddModelV D M r)) as FO';[qauto|clear IH FO].
      unfold NoQuantDenotation in *.
      assert (
        forall r : {r : T D | lt D r s},
        exists a : NoQuantAdvice D (nu (FO_NoQuant f)),
          NoQuantFormulaCondition D (FO_NoQuant f) (AddModelV D M (` r)) a /\
          NoQuantFOBoundCondition D (FO_NoQuant f) (AddModelV D M (` r)) a /\
          NoQuantSOBoundCondition D (FO_NoQuant f) (AddModelV D M (` r)) a) as FO;[qauto|clear FO'].
      apply choice in FO.
      destruct FO as [adv H].
      exists {| exiVAdv :=  Uni_Advice (fun x => exiVAdv _ _ (adv x))
              ; exiFAdv := fun _ _ _ => None |}.
      split;[|split].
      * unfold NoQuantFormulaCondition.
        simpl; rewrite map_length; move=> [u ltu]; simpl.
        assert (lt D (u (exist _ 0 (ltn0Sn _))) s) as ltuE.
          remember (ltu (exist _ 0 (ltn0Sn _)) (fun=> 0%R)) as ltu'; clear Heqltu' ltu.
          simpl in ltu'.
          unfold InBound in ltu'.
          rewrite PolyTermVSCastFOCastId in ltu'.
          rewrite <- PolyTerm_PolyTermVS_Correct in ltu'.
          by rewrite PM in ltu'; simpl in ltu'.
        remember (H (exist _ (u (exist _ 0 (ltn0Sn _))) ltuE)) as H'; clear HeqH' H.
        destruct H' as [H _].
        unfold NoQuantFormulaCondition in H; simpl in H.
        assert (forall j v,
              InBound D M
                {|
                  exiVAdv := Uni_Advice (fun x => exiVAdv D (nu (FO_NoQuant f)) (adv x));
                  exiFAdv := exiFAdv D _ (adv (exist ((lt D)^~ s) (u (exist _ 0 (ltn0Sn _))) ltuE))
                |} (u j)
                (nth PolyZeroVS
                  (uniVBounds (NoQuantAddUni (PolyTerm_PolyTermVS p) (FO_NoQuant f)))
                  (` j)) (MakeU u v)) as ltuX.
              clear H ; move=> [j ltj] v; simpl in *.
              remember (ltu (exist _ j ltj) v) as ltu'; clear Heqltu'.
              unfold InBound in *; simpl in *.
              destruct j; simpl in *.
              by rewrite PolyTermVSCastFOCastId; rewrite PolyTermVSCastFOCastId in ltu'.
              change (PolyZeroVS (nu := [seq x.+1 | x <- nu (FO_NoQuant f)]))
              with (PolyTermVSLiftUni (nu := nu (FO_NoQuant f)) PolyZeroVS) in ltu'.
              change (PolyZeroVS (nu := [seq x.+1 | x <- nu (FO_NoQuant f)]))
              with (PolyTermVSLiftUni (nu := nu (FO_NoQuant f)) PolyZeroVS).
              rewrite nth_map; rewrite nth_map in ltu'.
              remember (PolyVSDenotation _ _ _ _ _) as PD0.
              replace (PolyVSDenotation _ _ _ _ _) with PD0.
              destruct PD0; auto; simpl in *.
              rewrite HeqPD0; clear HeqPD0 PD0 ltu'.
              do 2 rewrite <- (FO_NoQuant_Correct_Lem_7_0 (nth PolyZeroVS (uniVBounds (FO_NoQuant f)) j)).
              apply FO_NoQuant_Correct_Lem_8.
        assert (forall j v, InBound D (AddModelV D M (u (exist _ 0 (ltn0Sn _))))
               (adv (exist ((lt D)^~ s) (u (exist _ 0 (ltn0Sn _))) ltuE)) (fSeqRest u j)
               (nth PolyZeroVS (uniVBounds (FO_NoQuant f)) (` j)) (MakeU (fSeqRest u) v)) as ltu0.
              clear H ; move=> [j ltj] v; simpl in *.
              assert (j.+1 < (length (uniVBounds (FO_NoQuant f))).+1) as ltj2;[clear ltu ltuX ltuE PM adv v u s M p; sfirstorder|].
              remember (ltuX (exist _ (j.+1) ltj2) v) as ltu'; clear Heqltu'.
              unfold InBound in *; simpl in *.
              change (PolyZeroVS (nu := [seq x.+1 | x <- nu (FO_NoQuant f)]))
              with (PolyTermVSLiftUni (nu := nu (FO_NoQuant f)) PolyZeroVS) in ltu'.
              rewrite nth_map in ltu'.
              remember (PolyVSDenotation _ _ _ _ _) as PD0.
              replace (PolyVSDenotation _ _ _ _ _) with PD0.
              destruct PD0; auto; simpl in *.
              replace (fSeqRest u (exist _ j ltj))
                with (u (exist _ j.+1 ltj2)); auto.
              unfold fSeqRest; simpl; apply f_equal; by apply subset_eq_compat.
              rewrite HeqPD0; clear HeqPD0 PD0 ltu'.
              by rewrite <- FO_NoQuant_Correct_Lem_4_0_1.
        remember (H (exist _ (fSeqRest u) ltu0)) as H'; clear HeqH' H; simpl in H'.
        rewrite <- (FO_NoQuant_Correct_Lem_5_5 (exiF1 := exiFAdv D (nu (FO_NoQuant f))
          (adv (exist ((lt D)^~ s) (u (exist _ 0 (ltn0Sn _))) ltuE)))).
        by rewrite <- FO_NoQuant_Correct_Lem_4_0_2.
      * unfold NoQuantFOBoundCondition=> i [u ltu] n; simpl in *.
        destruct i as [i lti].
        assert (i < length (nu (FO_NoQuant f))) as lti2;[clear u ltu; by rewrite map_length in lti|].
        assert (nth 0 [seq x.+1 | x <- nu (FO_NoQuant f)] i 
                = (nth 0 (nu (FO_NoQuant f)) i).+1).
          transitivity (lnth [seq x.+1 | x <- nu (FO_NoQuant f)] (exist _ i lti));[by rewrite (lnth_nth 0)|].
          by rewrite lnth_map (lnth_nth 0); f_equal.
        remember (NoQuantFOBoundCondition_obligation_1 _ _ _ _ _ _) as DDD; clear HeqDDD.
        change PolyZeroVS with (PolyTermVSLiftUni (nu := nu (FO_NoQuant f)) PolyZeroVS); rewrite nth_map.
        assert (0 < nth 0 [seq x.+1 | x <- nu (FO_NoQuant f)] i) as lt0;[by rewrite H0|].
        assert (lt D (u (exist _ 0 lt0)) s) as ltuE.
          remember (ltu (exist _ 0 lt0) (fun=> 0%R)) as ltu'; clear Heqltu' ltu.
          simpl in ltu'.
          unfold InBound in ltu'.
          rewrite PolyTermVSCastFOCastId in ltu'.
          rewrite <- PolyTerm_PolyTermVS_Correct in ltu'.
          by rewrite PM in ltu'.
        remember (H (exist _ (u (exist _ 0 lt0)) ltuE)) as H'; clear HeqH' H.
        destruct H' as [_ [H _]]; simpl in H.
        unfold NoQuantFOBoundCondition in H.
        remember (FO_NoQuant_Correct_Lem_9 lti2 u) as u'.
        assert (lt D (u' (exist _ 0 (ltn0Sn (nth 0 (nu (FO_NoQuant f)) i)))) s) as ltuE2.
          rewrite Hequ'; unfold FO_NoQuant_Correct_Lem_9; simpl.
          remember (lt _ _ _) as L1; replace (lt _ _ _) with L1;auto;rewrite HeqL1.
          do 2 f_equal; by apply subset_eq_compat.
        assert (forall j v, InBound D (AddModelV D M (u (exist _ 0 lt0)))
                 (adv (exist ((lt D)^~ s) (u (exist _ 0 lt0)) ltuE)) (fSeqRest u' j)
                 (nth PolyZeroVS (uniVBounds (FO_NoQuant f)) (` j))
                 (MakeU (fSeqRest u') v)) as ltu2.
                move=> [j ltj] v.
                simpl.
                clear H DDD.
                simpl in *.
                assert (j.+1 < nth 0 [seq x.+1 | x <- nu (FO_NoQuant f)] i) as ltj2;[by rewrite H0|].
                remember (ltu (exist _ (j.+1) ltj2) v) as ltu'; clear Heqltu' ltu.
                unfold InBound in *.
                remember (PolyVSDenotation _ _ _ _ _) as P0.
                replace (PolyVSDenotation _ _ _ _ _) with P0.
                destruct P0; auto.
                replace (fSeqRest u' _) with (u (exist _ j.+1 ltj2)); auto.
                rewrite Hequ'.
                unfold FO_NoQuant_Correct_Lem_9, fSeqRest; simpl.
                f_equal; by apply subset_eq_compat.
                rewrite HeqP0; clear ltu' HeqP0 P0.
                simpl.
                change (PolyZeroVS (nu := [seq x.+1 | x <- nu (FO_NoQuant f)]))
                with (PolyTermVSLiftUni (nu := nu (FO_NoQuant f)) PolyZeroVS). 
                rewrite nth_map.
                remember (adv _) as adv'.
                assert (adv' = adv (exist ((lt D)^~ s) (u' (exist _ 0 (ltn0Sn _))) ltuE2)).
                  rewrite Heqadv'; f_equal; apply subset_eq_compat.
                  rewrite Hequ'; unfold FO_NoQuant_Correct_Lem_9; f_equal; by apply subset_eq_compat.
                transitivity (PolyVSDenotation D
                  (PolyTermVSLiftUni (nth PolyZeroVS (uniVBounds (FO_NoQuant f)) j)) M
                  {| exiVAdv := Uni_Advice (fun x => exiVAdv D (nu (FO_NoQuant f)) (adv x));
                    exiFAdv := exiFAdv _ _ (adv (exist ((lt D)^~ s) (u' (exist _ 0 (ltn0Sn _))) ltuE2))
                  |} (MakeU u v));[by apply FO_NoQuant_Correct_Lem_8_5|].
                replace (MakeU u v) with (MakeU u' v).
                rewrite <- FO_NoQuant_Correct_Lem_4_0_1.
                f_equal; auto.
                f_equal; rewrite Hequ'; unfold FO_NoQuant_Correct_Lem_9; f_equal; by apply subset_eq_compat.
                rewrite Hequ'.
                unfold FO_NoQuant_Correct_Lem_9.
                apply functional_extensionality=> x.
                unfold MakeU.
                dep_if_case (x < (nth 0 (nu (FO_NoQuant f)) i).+1); auto.
                rewrite dep_if_case_true;[by rewrite H0|]=> Hyp0.
                f_equal; by apply subset_eq_compat.
                by rewrite dep_if_case_false;rewrite H0.
        remember (H (exist _ i lti2) (exist _ _ ltu2) n) as H'; clear HeqH' H.
        unfold InBound in *; simpl in *.
        remember (PolyVSDenotation _ _ _ _ _) as P0; replace (PolyVSDenotation _ _ _ _ _) with P0.
        destruct P0; auto.
        unfold Uni_Advice; simpl.
        rewrite dep_if_case_true.
          apply lt_ltdec.
          clear H' HeqP0 s0 ltu2 Hequ' ltuE2 u'.
          replace (u _) with (u (exist _ 0 lt0)); auto.
          f_equal; by apply subset_eq_compat.
        move=> Hyp0.
        remember (exiVAdv _ _ _ _ _) as A1; replace (exiVAdv _ _ _ _ _) with A1; auto; rewrite HeqA1; auto.
        replace (adv (exist ((lt D)^~ s) (u (exist _ 0 (DDD (exist _ 0 _)))) (lt_dec_true_true Hyp0)))
        with ((adv (exist ((lt D)^~ s) (u (exist _ 0 lt0)) ltuE))).
        assert (exist (fun n0 : nat => n0 < length (nu (FO_NoQuant f))) i lti2 =
                exist _ i (Uni_Advice_obligation_2 (nu (FO_NoQuant f)) s (exist _ i lti) (fun x => u (exist _ (` x) (DDD x))) Hyp0))as e;[
        by apply subset_eq_compat|].
        apply (exiVAdvEqLem e)=> x.
        remember (NoQuantFOBoundCondition_obligation_1 _ _ _ _ _ _ _) as DDD0; clear HeqDDD0.
        unfold fSeqRest; rewrite Hequ'; unfold FO_NoQuant_Correct_Lem_9.
        f_equal; apply subset_eq_compat; simpl.
        by rewrite projT1_eq_rect.
        f_equal; apply subset_eq_compat; f_equal; by apply subset_eq_compat.
        rewrite HeqP0; clear H' HeqP0 P0.
        transitivity (PolyVSDenotation D
          (PolyTermVSLiftUni (nth PolyZeroVS (exiVBounds (FO_NoQuant f)) i)) M
          {| exiVAdv := Uni_Advice (fun x => exiVAdv D (nu (FO_NoQuant f)) (adv x));
             exiFAdv := exiFAdv _ _ (adv (exist ((lt D)^~ s) (u' (exist _ 0 (ltn0Sn _))) ltuE2))
          |} (MakeU u n)).
        replace (MakeU u n) with (MakeU u' n).
        rewrite <- FO_NoQuant_Correct_Lem_4_0_1.
        do 2 f_equal.
        rewrite Hequ'; unfold FO_NoQuant_Correct_Lem_9; f_equal; by apply subset_eq_compat.
        apply subset_eq_compat; rewrite Hequ'; unfold FO_NoQuant_Correct_Lem_9; f_equal; by apply subset_eq_compat.
        apply functional_extensionality=> x.
        rewrite Hequ'; unfold MakeU.
        dep_if_case (x < (nth 0 (nu (FO_NoQuant f)) i).+1); auto.
        rewrite dep_if_case_true;[by rewrite H0|]=> Hyp0.
        unfold FO_NoQuant_Correct_Lem_9; f_equal; by apply subset_eq_compat.
        by rewrite dep_if_case_false;rewrite H0.
        apply FO_NoQuant_Correct_Lem_10_5.
      * unfold NoQuantFOBoundCondition; simpl=> i u; simpl=> t out con; fcrush.
  - move=> [adv [H0 [H1 H2]]] r ltrs.
    apply IH; clear IH.
    unfold NoQuantDenotation.
    exists (AdviceDropUni r adv).
    split;[|split].
    + clear H1 H2.
      move=> [u ltu]; simpl.
      unfold NoQuantFormulaCondition in H0.
      unfold U in H0.
      simpl in H0.
      remember (ExtendAt0N r u) as u'.
      rewrite map_length in H0.
      assert (forall j v, InBound D M adv (u' j) (nth PolyZeroVS
                (PolyTermVSCastFO (PolyTerm_PolyTermVS p)
                  :: [seq PolyTermVSLiftUni i | i <- uniVBounds (FO_NoQuant f)]) 
                (` j)) (MakeU u' v)) as ltu'.
              move=> [j ltj] v.
              rewrite Hequ'; destruct j; unfold ExtendAt0N, MakeU; simpl; auto.
              unfold InBound.
              rewrite PolyTermVSCastFOCastId; rewrite <- PolyTerm_PolyTermVS_Correct.
              by rewrite PM.
              unfold InBound.
              change PolyZeroVS with (PolyTermVSLiftUni (nu := nu (FO_NoQuant f)) PolyZeroVS).
              rewrite nth_map.
              remember (ltu (exist _ j ltj) v) as ltu2; clear Heqltu2 ltu.
              simpl in ltu2.
              unfold InBound in ltu2.
              remember (PolyVSDenotation _ _ _ _ _) as PD0.
              replace (PolyVSDenotation _ _ _ _ _) with PD0.
              destruct PD0;auto.
              remember (Utils.ExtendAt0N_obligation_2  _ _ _) as DD0; simpl in DD0.
              by replace DD0 with ltj;[|apply eq_irrelevance].
              rewrite HeqPD0; clear HeqPD0 PD0 ltu2.
              rewrite FO_NoQuant_Correct_Lem_7_0_A.
              f_equal.
              unfold ExtendAt0; apply functional_extensionality=> x.
              destruct x; simpl; auto.
              unfold MakeU.
              dep_if_case (x < length (uniVBounds (FO_NoQuant f))); auto.
              rewrite dep_if_case_true; auto.
              f_equal; by apply subset_eq_compat.
              rewrite dep_if_case_false; auto.
      remember (H0 (exist _ u' ltu')) as H; clear HeqH H0; simpl in H.
      rewrite FO_NoQuant_Correct_Lem_7_A.
      rewrite Hequ' in H.
      replace (ExtendAt0 r (MakeU u (fun=> 0%R)))
         with (MakeU (ExtendAt0N r u) (fun=> 0%R)); auto.
      unfold MakeU, ExtendAt0; apply functional_extensionality=> x.
      destruct x; auto; simpl.
      dep_if_case (x < length (uniVBounds (FO_NoQuant f))); auto.
      unfold ExtendAt0N; simpl.
      rewrite dep_if_case_true; auto.
      f_equal; by apply subset_eq_compat.
      rewrite dep_if_case_false; auto.
    + clear H0 H2.
      move=> [i lti] [u ltu] n; simpl.
      remember (FO_NoQuant_Correct_Lem_9_0 lti (ExtendAt0N r u)) as u'.
      simpl in H1.
      assert (i < length [seq x.+1 | x <- nu (FO_NoQuant f)]) as lti2.
        by rewrite map_length.
      assert (nth 0 [seq x0.+1 | x0 <- nu (FO_NoQuant f)] i =
              (nth 0 (nu (FO_NoQuant f)) i).+1) as HH.
          replace (nth 0 [seq x.+1 | x <- nu (FO_NoQuant f)] i)
            with (lnth [seq x.+1 | x <- nu (FO_NoQuant f)] (exist _ i lti2)).
          by rewrite lnth_map (lnth_nth 0).
          by rewrite (lnth_nth 0).
      assert (forall (j : |[nth 0 [seq x.+1 | x <- nu (FO_NoQuant f)] i]|) v, InBound D M adv (u' j) (nth PolyZeroVS
              (PolyTermVSCastFO (PolyTerm_PolyTermVS p) :: [seq PolyTermVSLiftUni i
                          | i <- uniVBounds (FO_NoQuant f)]) 
                   (` j)) (MakeU u' v)) as ltu'.
              move=> [j ltj] v.
              rewrite Hequ'; destruct j; unfold ExtendAt0N, MakeU; simpl; auto.
              unfold InBound.
              rewrite PolyTermVSCastFOCastId; rewrite <- PolyTerm_PolyTermVS_Correct.
              by rewrite PM.
              unfold InBound.
              change PolyZeroVS with (PolyTermVSLiftUni (nu := nu (FO_NoQuant f)) PolyZeroVS).
              rewrite nth_map.
              simpl in ltu.
              assert (j < nth 0 (nu (FO_NoQuant f)) i) as ltj2;[by rewrite HH in ltj|].
              remember (ltu (exist _ j ltj2) v) as ltu2; clear Heqltu2 ltu.
              simpl in ltu2.
              unfold InBound in ltu2.
              remember (PolyVSDenotation _ _ _ _ _) as PD0.
              replace (PolyVSDenotation _ _ _ _ _) with PD0.
              destruct PD0;auto.
              replace (FO_NoQuant_Correct_Lem_9_0 _ _ _)
                 with (u (exist (fun n : nat => n < nth 0 (nu (FO_NoQuant f)) i) j ltj2)); auto.
              unfold FO_NoQuant_Correct_Lem_9_0; simpl.
              f_equal; by apply subset_eq_compat.
              rewrite HeqPD0; clear HeqPD0 PD0 ltu2.
              rewrite FO_NoQuant_Correct_Lem_7_0_A.
              f_equal.
              unfold ExtendAt0; apply functional_extensionality=> x.
              destruct x; simpl; auto.
              rewrite dep_if_case_true; auto; by rewrite HH.
              unfold MakeU.
              dep_if_case (x < nth 0 (nu (FO_NoQuant f)) i); auto.
              rewrite dep_if_case_true; auto;[by rewrite HH|].
              move=> Hyp.
              unfold FO_NoQuant_Correct_Lem_9_0; simpl.
              f_equal; by apply subset_eq_compat.
              rewrite dep_if_case_false; auto;by rewrite HH.
      remember (H1 (exist _ i lti2) (exist _ u' ltu') n) as H; clear HeqH H1; simpl in H.
      unfold InBound in *.
      rewrite FO_NoQuant_Correct_Lem_7_0_A.
      change PolyZeroVS with (PolyTermVSLiftUni (nu := nu (FO_NoQuant f)) PolyZeroVS) in H.
      rewrite nth_map in H.
      replace (MakeU u' n) with (ExtendAt0 r (MakeU u n)) in H.
      destruct (PolyVSDenotation _ _ _ _ _); auto.
      remember (exiVAdv _ _ _ _ _) as E.
      replace (exiVAdv _ _ _ _ _) with E; auto.
      rewrite HeqE; clear H HeqE E.
      assert (exist (fun n0 : nat => n0 < length [seq x.+1 | x <- nu (FO_NoQuant f)]) i lti2 
            = (exist _ i (AdviceDropUni_obligation_1 (nu (FO_NoQuant f)) (exist _ i lti)
              (fun x => u (exist _  (` x) (NoQuantFOBoundCondition_obligation_1 D 
              (FO_NoQuant f) (AddModelV D M r) (AdviceDropUni r adv)
              (exist _ i lti) (exist _ u ltu) x))))) ) as e;[by apply subset_eq_compat|].
      apply (exiVAdvEqLem e)=> x; destruct x; simpl.
      remember (exist _ x _) as DDD.
      rewrite Hequ' HeqDDD; clear HeqDDD DDD.
      unfold FO_NoQuant_Correct_Lem_9_0; simpl.
      remember (FO_NoQuant_Correct_Lem_9_0_obligation_1 _ _ _ _) as DDD; clear HeqDDD; simpl in DDD.
      unfold ExtendAt0N; destruct x; simpl;[rewrite dep_if_case_true|rewrite dep_if_case_false];auto;
        change (exist _ ?x _ == exist _ ?y _) with (x == y).
      by rewrite projT1_eq_rect.
      by rewrite projT1_eq_rect.
      simpl=> Hyp.
      f_equal; apply subset_eq_compat; by rewrite projT1_eq_rect.
      rewrite Hequ'; unfold MakeU, ExtendAt0, ExtendAt0N; apply functional_extensionality=>x.
      destruct x; simpl; auto.
      unfold FO_NoQuant_Correct_Lem_9_0; simpl.
      by rewrite HH.
      dep_if_case (x < nth 0 (nu (FO_NoQuant f)) i); auto.
      rewrite dep_if_case_true; auto;[by rewrite HH|].
      move=> Hyp.
      unfold FO_NoQuant_Correct_Lem_9_0; simpl.
      f_equal; by apply subset_eq_compat.
      rewrite dep_if_case_false; auto;by rewrite HH.
    + move => u [i lti].
      assert (length (exiFInputBounds (FO_NoQuant f)) = 0).
      clear adv H0 H1 H2 PM lti.
      elim: f; try qauto.
      move=> p0 f IH; simpl; by rewrite map_length.
      move=> p0 f IH; simpl; by rewrite map_length.
      assert (i < 0);[by rewrite H in lti|fcrush].
    + move=> _.
      unfold NoQuantDenotation.
      exists {| exiVAdv := fun x t => 0%R; exiFAdv := fun x a v => None |}.
      split;[|split].
      * move=> [u ltu]; simpl.
        simpl in ltu.
        remember (ltu (exist _ 0 (ltn0Sn _)) (fun _ => 0%R)) as ltu'; clear Heqltu' ltu.
        unfold InBound in ltu'; simpl in ltu'.
        rewrite PolyTermVSCastFOCastId in ltu'; rewrite <- PolyTerm_PolyTermVS_Correct in ltu'.
        by rewrite PM in ltu'.
      * move=> [i lti] [u ltu]; simpl; simpl in ltu.
        assert (0 < nth 0 [seq x.+1 | x <- nu (FO_NoQuant f)] i) as lt0.
        replace (nth 0 [seq x.+1 | x <- nu (FO_NoQuant f)] i)
            with (lnth [seq x.+1 | x <- nu (FO_NoQuant f)] (exist _ i lti)).
          by rewrite lnth_map (lnth_nth 0).
          by rewrite (lnth_nth 0).
        remember (ltu (exist _ 0 lt0) (fun _ => 0%R)) as ltu'; clear Heqltu' ltu.
        unfold InBound in ltu'; simpl in ltu'.
        rewrite PolyTermVSCastFOCastId in ltu'; rewrite <- PolyTerm_PolyTermVS_Correct in ltu'.
        by rewrite PM in ltu'.
      * move => u [i lti].
        assert (length (exiFInputBounds (FO_NoQuant f)) = 0).
        clear IH lti.
        elim: f; try qauto.
        move=> p0 f IH; simpl; by rewrite map_length.
        move=> p0 f IH; simpl; by rewrite map_length.
        simpl in lti.
        assert (i < 0);[by rewrite map_length H in lti|fcrush].
Qed.






































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
  (n : NoQuant) : 
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
  (n : NoQuant) : 
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
  (n : NoQuant) : 
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
  (n : NoQuant) : 
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