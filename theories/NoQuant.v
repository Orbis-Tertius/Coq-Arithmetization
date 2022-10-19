From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun zmodp ssrbool ssrnat ssralg seq fintype finalg tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.
From Coq Require Import ClassicalChoice.

Require Import CoqArith.Utils.

Require Import CoqArith.Sigma_1_1.
Require Import Program.

Section NoQuantDef.

Variable (FSize : nat).

Inductive PolyTermVS : Type :=
| PolyFVarVS : nat -> PolyTermVS
| PolyUVarVS : nat -> PolyTermVS
| PolyFFunVS : forall (i a : nat), (|[a]| -> PolyTermVS) -> PolyTermVS
| PolyEFunVS : forall (i a : nat), (|[a]| -> PolyTermVS) -> PolyTermVS
| PolyMinusOneVS : PolyTermVS
| PolyPlusOneVS : PolyTermVS
| PolyZeroVS : PolyTermVS
| PolyPlusVS : PolyTermVS -> PolyTermVS -> PolyTermVS
| PolyTimesVS : PolyTermVS -> PolyTermVS -> PolyTermVS
| PolyIndVS : PolyTermVS -> PolyTermVS -> PolyTermVS.

Inductive ZerothOrderFormulaVS : Type :=
| ZONotVS : ZerothOrderFormulaVS -> ZerothOrderFormulaVS
| ZOAndVS : ZerothOrderFormulaVS -> ZerothOrderFormulaVS -> ZerothOrderFormulaVS
| ZOOrVS : ZerothOrderFormulaVS -> ZerothOrderFormulaVS -> ZerothOrderFormulaVS
| ZOImpVS : ZerothOrderFormulaVS -> ZerothOrderFormulaVS -> ZerothOrderFormulaVS
| ZOEqVS : @PolyTermVS -> @PolyTermVS -> ZerothOrderFormulaVS.

Record NoQuant : Type :=
  mkNoQuant {
    uniBounds : seq PolyTermVS;
    exiBounds : seq (seq PolyTermVS * PolyTermVS);
    formula : ZerothOrderFormulaVS
  }.

Definition NoQuantAdvice a p : Type :=
  forall i : nat, (|[a i]| -> 'F_p) -> option 'F_p .

Program Fixpoint PolyVSDenotation (M : @Sigma11Model FSize)
  (p : PolyTermVS)
  {A} (adv : NoQuantAdvice A FSize) :
  (nat -> 'F_FSize) -> option ('F_FSize) :=
  match p with
  | PolyFVarVS i => fun _ => Some (V_F _ M i)
  | PolyUVarVS i => fun u => Some (u i)
  | PolyFFunVS i a t => fun u =>
    (if a == projT1 (F_S _ M i) as b return ((a == projT1 (F_S _ M i)) = b -> option ('F_FSize))
     then fun _ => (
          let ds := option_fun (fun x => PolyVSDenotation M (t x) adv u) in
          obind (fun t : |[a]| -> 'F_FSize => projT2 (F_S _ M i) t) ds)
      else fun _ => None) (erefl _)
  | PolyEFunVS i a t => fun u =>
    (if a == A i as b return ((a == A i) = b -> option ('F_FSize))
     then fun _ => (
          let ds := option_fun (fun x => PolyVSDenotation M (t x) adv u) in
          obind (fun t : |[a]| -> 'F_FSize => adv i t) ds)
      else fun _ => None) (erefl _)
  | PolyMinusOneVS => fun _ => Some (-1)%R
  | PolyPlusOneVS => fun _ => Some 1%R
  | PolyZeroVS => fun _ => Some 0%R
  | PolyPlusVS p1 p2 => fun u =>
    let d1 := PolyVSDenotation M p1 adv u in
    let d2 := PolyVSDenotation M p2 adv u in
    obind (fun r1 => obind (fun r2 => Some (r1 + r2)%R) d2) d1
  | PolyTimesVS p1 p2 => fun u =>
    let r1 := PolyVSDenotation M p1 adv u in
    let r2 := PolyVSDenotation M p2 adv u in 
    obind (fun r1 => obind (fun r2 => Some (r1 * r2)%R) r2) r1
  | PolyIndVS p1 p2 => fun u =>
    let r1 := PolyVSDenotation M p1 adv u in
    let r2 := PolyVSDenotation M p2 adv u in 
    obind (fun r1 => obind (fun r2 => Some (indFun r1 r2)) r2) r1
  end.
Next Obligation. apply EEConvert in e; qauto. Qed.
Next Obligation. apply EEConvert in e; qauto. Qed.

Fixpoint NoQuantZODenotation (M : @Sigma11Model FSize)
  (f : ZerothOrderFormulaVS)
  {A} (adv : NoQuantAdvice A FSize) :
  (nat -> 'F_FSize) -> option bool :=
  match f with
  | ZONotVS f => fun u => 
    let d := NoQuantZODenotation M f adv u in
    obind (fun d => Some (negb d)) d
  | ZOAndVS f1 f2 => fun u => 
    let d1 := NoQuantZODenotation M f1 adv u in
    let d2 := NoQuantZODenotation M f2 adv u in
    obind (fun r1 => obind (fun r2 => Some (r1 && r2)) d2) d1
  | ZOOrVS f1 f2 => fun u => 
    let d1 := NoQuantZODenotation M f1 adv u in
    let d2 := NoQuantZODenotation M f2 adv u in
    obind (fun r1 => obind (fun r2 => Some (r1 || r2)) d2) d1
  | ZOImpVS f1 f2 => fun u => 
    let d1 := NoQuantZODenotation M f1 adv u in
    let d2 := NoQuantZODenotation M f2 adv u in
    obind (fun r1 => obind (fun r2 => Some (r1 ==> r2)) d2) d1
  | ZOEqVS r1 r2 => fun u => 
    let d1 := PolyVSDenotation M r1 adv u in
    let d2 := PolyVSDenotation M r2 adv u in
    obind (fun r1 => obind (fun r2 => Some (r1 == r2)) d2) d1
  end.

Definition InBound (M : @Sigma11Model FSize)
  {A} (adv : NoQuantAdvice A FSize)
  (r : 'F_FSize)
  (b : PolyTermVS) 
  (t : nat -> 'F_FSize) : bool :=
  match PolyVSDenotation M b adv t with
  | None => false
  | Some e => r < e
  end.

Program Definition MakeU {A} {n}
  (a : |[n]| -> A) 
  (b : nat -> A) :
  nat -> A := fun i => (
  if i < n as b return i < n = b -> A
  then fun _ => a i
  else fun _ => b (i - n)
  ) (erefl _).

Definition NoQuantAdviceF 
  (f : NoQuant) : Type :=
  NoQuantAdvice (fun i => nth 0 (map (fun x => length x.1) (exiBounds f)) i) FSize.

Program Definition U (M : @Sigma11Model FSize)
  (f : NoQuant) (adv : NoQuantAdviceF f) : Type 
  := { u : |[length (uniBounds f)]| -> 'F_FSize | 
       forall j : |[length (uniBounds f)]|,
       forall v : nat -> 'F_FSize, 
       InBound M adv (u j) (lnth (uniBounds f) j) (MakeU u v)
    }.

Program Definition NoQuantFormulaCondition (M : @Sigma11Model FSize)
  (f : NoQuant) (adv : NoQuantAdviceF f) : Prop :=
  forall (u : U M f adv), 
  NoQuantZODenotation M (formula f) adv (MakeU u (fun _ => 0%R)) == Some true.

Program Definition NoQuantUniversalCondition (M : @Sigma11Model FSize)
  (f : NoQuant) (adv : NoQuantAdviceF f) : Prop :=
  forall (u : nat -> 'F_FSize) (i : |[length (uniBounds f)]|),
    (forall j : |[i]|, InBound M adv (u j) (lnth (uniBounds f) j) u) ->
    InBound M adv (u i) (lnth (uniBounds f) i) u.
Next Obligation. strivial use: ltn_trans. Qed.

Program Fixpoint FunBoundsVS (M : @Sigma11Model FSize)
  {A} (adv : NoQuantAdvice A FSize) {a}
  (ins : |[a]| -> 'F_FSize) (out : 'F_FSize)
  (insB : |[a]| -> PolyTermVS) (outB : PolyTermVS) :
  (nat -> 'F_FSize) -> bool := fun u =>
  match a with
  | 0 => 
    match PolyVSDenotation M outB adv u with
    | None => false
    | Some oB => out < oB
    end
  | n.+1 => 
    match PolyVSDenotation M (insB 0) adv u with
    | None => false
    | Some iB => (ins 0 < iB) && 
        @FunBoundsVS (AddModelV _ M (ins 0)) A adv n (fun x => ins (x.+1)) out (fun x => insB (x.+1)) outB u
    end
  end.

Program Definition NoQuantExiBoundCondition (M : @Sigma11Model FSize)
  (f : NoQuant) (adv : NoQuantAdviceF f) : Prop :=
  forall u : nat -> 'F_FSize, forall i : |[length (exiBounds f)]|,
  forall (ins : |[lnth (map (fun x => length x.1) (exiBounds f)) i]| -> 'F_FSize) (out : 'F_FSize),
  adv i ins == Some out -> 
  FunBoundsVS M adv ins out 
    (fun x => (lnth (lnth (map (fun x => x.1) (exiBounds f)) i) x))
    (lnth (map (fun x => x.2) (exiBounds f)) i) u == true.
Next Obligation. by rewrite map_length. Qed.
Next Obligation. 
  rewrite lnth_map; simpl.
  assert (i < length [seq length x.1 | x <- exiBounds f]);[by rewrite map_length|].
  replace (length _) with (lnth [seq length x.1 | x <- exiBounds f] (exist _ i H1));[|
    rewrite lnth_map; do 3 f_equal; by apply subset_eq_compat].
  by rewrite (lnth_nth 0).
Qed.
Next Obligation. by rewrite map_length. Qed.
Next Obligation.
  remember (NoQuantExiBoundCondition_obligation_3 _ _ _ _) as DD; clear HeqDD; simpl in DD. 
  rewrite lnth_map in H; simpl in H.
  rewrite lnth_map; simpl.
  remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DD0; clear HeqDD0; simpl in DD0. 
  remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DD1; clear HeqDD1; simpl in DD1. 
  by replace DD1 with DD0;[|apply eq_irrelevance].
Qed.
Next Obligation. by rewrite map_length. Qed.

Definition NoQuantDenotation (M : @Sigma11Model FSize)
  (f : NoQuant) : Prop :=
  exists (a : NoQuantAdviceF f),
    NoQuantFormulaCondition M f a /\
    NoQuantUniversalCondition M f a /\
    NoQuantExiBoundCondition M f a.

End NoQuantDef.

Section NoQuantTranslation.

Variable (FSize : nat).

Fixpoint PolyTerm_PolyTermVS (p : PolyTerm) : PolyTermVS :=
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

Theorem PolyTerm_PolyTermVS_Correct M p {A} (a : NoQuantAdvice A _) u :
  PolyVSDenotation FSize M (PolyTerm_PolyTermVS p) a u = Poly_Denote _ M p.
Proof.
  induction p; auto; simpl.
  - dep_if_case (a0 == projT1 (F_S _ M i)); auto;[rewrite dep_if_case_true|rewrite dep_if_case_false];auto.
    do 2 f_equal; auto; apply functional_extensionality=> t;[|apply H].
    f_equal; apply functional_extensionality=> x. 
    f_equal; by apply subset_eq_compat.
  all: f_equal;[|by rewrite IHp1];
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

Theorem ZerothOrder_ZerothOrderVS_Correct M p {A} (a : NoQuantAdvice A _) t :
  NoQuantZODenotation FSize M (ZerothOrder_ZerothOrderVS p) a t = ZerothOrder_Denote _ M p.
Proof.
  induction p; try qauto.
  by simpl; do 2 rewrite PolyTerm_PolyTermVS_Correct.
Qed.

Program Definition ZO_NoQuant (f : ZerothOrderFormula) : NoQuant :=
  {| uniBounds := [::]
   ; exiBounds := [::]
   ; formula := ZerothOrder_ZerothOrderVS f
  |}.

Lemma ZO_NoQuant_Correct_NoQuantFormulaCondition
  M f : ZerothOrder_Denote FSize M f == Some true <-> 
  exists a, NoQuantFormulaCondition _ M (ZO_NoQuant f) a.
Proof.
  split;move=> H.
  - exists (fun _ _ => None).
    unfold NoQuantFormulaCondition. 
    move=> u; by rewrite ZerothOrder_ZerothOrderVS_Correct.
  - destruct H as [adv H].
    unfold NoQuantFormulaCondition in H.
    assert (U _ M (ZO_NoQuant f) adv).
    unfold U.
    simpl.
    exists emptyTuple.
    move=> [j ltj]; fcrush.
    remember (H X) as H'; clear HeqH' H.
    by rewrite ZerothOrder_ZerothOrderVS_Correct in H'.
Qed.

Lemma ZO_NoQuant_Correct_NoQuantUniversalCondition
  M f : forall a, NoQuantUniversalCondition FSize M (ZO_NoQuant f) a.
Proof. move=> a u [i lti]; fcrush. Qed.

Lemma ZO_NoQuant_Correct_NoQuantExiBoundCondition
  M f : forall a, NoQuantExiBoundCondition FSize M (ZO_NoQuant f) a.
Proof. move=> a u [i lti]; fcrush. Qed.

Theorem ZO_NoQuant_Correct M p :
  ZerothOrder_Denote FSize M p == Some true <-> NoQuantDenotation _ M (ZO_NoQuant p).
Proof.
  qauto use: ZO_NoQuant_Correct_NoQuantFormulaCondition
           , ZO_NoQuant_Correct_NoQuantUniversalCondition
           , ZO_NoQuant_Correct_NoQuantExiBoundCondition.
Qed.

Program Fixpoint LiftPolyExi
  (p : PolyTermVS) :  PolyTermVS :=
  match p with
  | PolyFVarVS m => PolyFVarVS m
  | PolyUVarVS m => PolyUVarVS m
  | PolyFFunVS i a t => 
    if i == 0
    then PolyEFunVS 0 a (fun x => LiftPolyExi (t x))
    else PolyFFunVS (i.-1) a (fun x => LiftPolyExi (t x))
  | PolyEFunVS i a t => PolyEFunVS i.+1 a (fun x => LiftPolyExi (t x))
  | PolyMinusOneVS => PolyMinusOneVS
  | PolyPlusOneVS => PolyPlusOneVS
  | PolyZeroVS => PolyZeroVS
  | PolyPlusVS r1 r2 => PolyPlusVS (LiftPolyExi r1) (LiftPolyExi r2)
  | PolyTimesVS r1 r2 => PolyTimesVS (LiftPolyExi r1) (LiftPolyExi r2)
  | PolyIndVS r1 r2 => PolyIndVS (LiftPolyExi r1) (LiftPolyExi r2)
  end.

Fixpoint LiftPropExi (p : ZerothOrderFormulaVS) : ZerothOrderFormulaVS :=
  match p with
  | ZONotVS f => ZONotVS (LiftPropExi f)
  | ZOAndVS f1 f2 => ZOAndVS (LiftPropExi f1) (LiftPropExi f2)
  | ZOOrVS f1 f2 => ZOOrVS (LiftPropExi f1) (LiftPropExi f2)
  | ZOImpVS f1 f2 => ZOImpVS (LiftPropExi f1) (LiftPropExi f2)
  | ZOEqVS r1 r2 => ZOEqVS (LiftPolyExi r1) (LiftPolyExi r2)
  end.

Program Fixpoint LiftPolyUni (p : PolyTermVS): PolyTermVS :=
  match p with
  | PolyFVarVS i => 
    if i == 0
    then PolyUVarVS 0
    else PolyFVarVS (i.-1)
  | PolyUVarVS i => PolyUVarVS (i.+1)
  | PolyFFunVS i a t => PolyFFunVS i a (fun x => LiftPolyUni (t x))
  | PolyEFunVS i a t => 
    PolyEFunVS i a.+1 
    (fun x => 
      (if (x == 0) as b return (x == 0) = b -> PolyTermVS
       then fun _ => PolyUVarVS 0
       else fun _ => (t x.-1)) (erefl _)
    )
  | PolyMinusOneVS => PolyMinusOneVS
  | PolyPlusOneVS => PolyPlusOneVS
  | PolyZeroVS => PolyZeroVS
  | PolyPlusVS p1 p2 => PolyPlusVS (LiftPolyUni p1) (LiftPolyUni p2)
  | PolyTimesVS p1 p2 => PolyTimesVS (LiftPolyUni p1) (LiftPolyUni p2)
  | PolyIndVS p1 p2 => PolyIndVS (LiftPolyUni p1) (LiftPolyUni p2)
  end.
Next Obligation. destruct x;[fcrush|auto]. Qed.

Fixpoint LiftPropUni
  (f : ZerothOrderFormulaVS):
  ZerothOrderFormulaVS :=
  match f with
  | ZONotVS f => ZONotVS (LiftPropUni f)
  | ZOAndVS f1 f2 => ZOAndVS (LiftPropUni f1) (LiftPropUni f2)
  | ZOOrVS f1 f2 => ZOOrVS (LiftPropUni f1) (LiftPropUni f2)
  | ZOImpVS f1 f2 => ZOImpVS (LiftPropUni f1) (LiftPropUni f2)
  | ZOEqVS r1 r2 => ZOEqVS (LiftPolyUni r1) (LiftPolyUni r2)
  end.

Definition NoQuantAddExi (bs : seq PolyTermVS) (y : PolyTermVS) (q : NoQuant) : NoQuant :=
  {| uniBounds := map LiftPolyExi (uniBounds q)
   ; exiBounds := (bs, y) :: map (fun x => (map LiftPolyExi x.1, LiftPolyExi x.2)) (exiBounds q)
   ; formula := LiftPropExi (formula q)
  |}.

Definition NoQuantAddUni (b : PolyTermVS) (q : NoQuant) : NoQuant :=
  {| uniBounds := b :: map LiftPolyUni (uniBounds q)
   ; exiBounds := map (fun x => (map LiftPolyUni x.1, LiftPolyUni x.2)) (exiBounds q)
   ; formula := LiftPropUni (formula q)
  |}.

Fixpoint Q_NoQuant (f : QuantifiedFormula) : NoQuant :=
  match f with
  | ZO z => ZO_NoQuant z
  | QExists bs y f => NoQuantAddExi (map PolyTerm_PolyTermVS bs) (PolyTerm_PolyTermVS y) (Q_NoQuant f)
  | QForall p f => NoQuantAddUni (PolyTerm_PolyTermVS p) (Q_NoQuant f)
  end.

Program Definition AdviceExtend {B} {p}
  (f : (|[B]| -> 'F_p) -> option ('F_p))
  {A} (adv : NoQuantAdvice A p) : 
  NoQuantAdvice (ExtendAt0 B A) p := fun i => 
  (if i == 0 as b return (i == 0 = b -> ({n : nat | n < ExtendAt0 B A i} -> 'F_p) -> option 'F_p)
   then fun _ => f
   else fun _ => adv i.-1) (erefl _).
Next Obligation. destruct i; auto. Qed.
Next Obligation. destruct i; auto. Qed.

Program Definition AdviceExtendF {bs y p}
  (f : (|[length bs]| -> 'F_FSize) -> option ('F_FSize))
  (adv : NoQuantAdviceF FSize p) : 
  NoQuantAdviceF FSize (NoQuantAddExi bs y p) := AdviceExtend f adv.
Next Obligation.
  destruct x; auto. 
  unfold ExtendAt0 in H; simpl in *.
  replace [seq length x.1 | x <- exiBounds p]
    with [seq length x1.1
     | x1 <- [seq ([seq LiftPolyExi i | i <- x1.1], LiftPolyExi x1.2)
                | x1 <- exiBounds p]] in H; auto.
  clear H x0.
  induction (exiBounds p); auto; simpl.
  by rewrite IHl map_length.
Qed.

Lemma Q_NoQuant_Correct_Lem_0 {M u p a f A adv} :
  PolyVSDenotation FSize M (LiftPolyExi p) (AdviceExtend f adv) u
  = PolyVSDenotation _ (AddModelF _ M (existT _ a f)) p (A := A) adv u.
Proof.
  elim: p; try qauto.
  - move=> i a' p IH.
    simpl.
    destruct i; simpl;[
      unfold ExtendAt0; simpl; dep_if_case (a' == a);
      auto;[rewrite dep_if_case_true|rewrite dep_if_case_false];auto
    | dep_if_case (a' == projT1 (F_S _ M i));
      auto;[rewrite dep_if_case_true|rewrite dep_if_case_false];auto];
    (f_equal;[apply functional_extensionality=> x;unfold AdviceExtend; simpl;
              f_equal; apply functional_extensionality=> t; f_equal; by apply subset_eq_compat
            | f_equal; apply functional_extensionality=> x; by rewrite IH]). 
  - move=> i a' p IH.
    simpl.
    unfold ExtendAt0; simpl.
    dep_if_case (a' == A i);auto;[rewrite dep_if_case_true|rewrite dep_if_case_false];auto.
    do 2 f_equal; apply functional_extensionality=> x; auto.
    unfold AdviceExtend; simpl.
    f_equal; apply functional_extensionality=> y; f_equal; by apply subset_eq_compat.
Qed.

Lemma Q_NoQuant_Correct_Lem_1 {M u p a f A adv} :
  NoQuantZODenotation FSize M (LiftPropExi p) (AdviceExtend f adv) u
  = NoQuantZODenotation _ (AddModelF _ M (existT _ a f)) p (A := A) adv u.
Proof.
  elim: p; try qauto.
  move=> p1 p2.
  simpl.
  by do 2 rewrite Q_NoQuant_Correct_Lem_0.
Qed.

Theorem Q_NoQuant_Correct_Lem_2 (M: Sigma11Model FSize) 
  {A} (adv: NoQuantAdvice A FSize)
  ar u ins out insB outB a F :
FunBoundsVS FSize (AddModelF FSize M (existT _ a F)) adv ins out insB outB u = 
FunBoundsVS FSize M (AdviceExtend F adv) (a := ar) ins out (fun x => LiftPolyExi (insB x)) (LiftPolyExi outB) u.
Proof.
  move:M ins; induction ar=> M ins; simpl;[by rewrite <- Q_NoQuant_Correct_Lem_0|].
  remember (FunBoundsVS_obligation_4 _ _ _ adv _ _ _ _ _ _) as DD0; clear HeqDD0; simpl in DD0;
  remember (FunBoundsVS_obligation_5 _ _ _ adv _ _ _ _ _ _) as DD1; clear HeqDD1; simpl in DD1;
  remember (FunBoundsVS_obligation_4 _ _ _ _ _ _ _ _ _ _) as DD2; clear HeqDD2; simpl in DD2;
  remember (FunBoundsVS_obligation_5 _ _ _ _ _ _ _ _ _ _) as DD3; clear HeqDD3; simpl in DD3.
  assert (PolyVSDenotation FSize
    (AddModelF FSize M (existT _ a F))
    (insB (exist (fun n : nat => n < ar.+1) 0 is_true_true)) adv u =
    (PolyVSDenotation FSize M
    (LiftPolyExi (insB (exist (fun n : nat => n < ar.+1) 0 is_true_true)))
    (AdviceExtend F adv) u));[by rewrite Q_NoQuant_Correct_Lem_0|].
  destruct (PolyVSDenotation _ _ _ _ _);destruct (PolyVSDenotation _ _ _ _ _);[|fcrush|fcrush|auto].
  f_equal;[qauto|].
  rewrite <- IHar.
  f_equal; apply functional_extensionality=>x;f_equal;by apply subset_eq_compat.
Qed.

Theorem Q_NoQuant_Correct_Lem_3 (M: Sigma11Model FSize) 
  {A} (adv: NoQuantAdvice A FSize)
  (bs: seq PolyTerm) (y: PolyTerm) u ins out
  : FunBoundsVS FSize M adv ins out (lnth [seq PolyTerm_PolyTermVS i | i <- bs])
      (PolyTerm_PolyTermVS y) u =
    FunBounds FSize M
      (eq_rect _ (fun x => |[x]| -> 'F_FSize) ins _ (map_length PolyTerm_PolyTermVS bs)) out 
      (lnth bs) y.
Proof.
  move:M ins; induction bs=> M ins;[simpl; by rewrite PolyTerm_PolyTermVS_Correct|simpl].
  remember (FunBoundsVS_obligation_4 _ _ _ _ _ _ _ _ _ _) as DD0; clear HeqDD0; simpl in DD0;
  remember (FunBoundsVS_obligation_5 _ _ _ _ _ _ _ _ _ _) as DD1; clear HeqDD1; simpl in DD1;
  remember (Sigma_1_1.FunBounds_obligation_4 _ _ _ _ _ _ _) as DD2; clear HeqDD2; simpl in DD2;
  remember (Sigma_1_1.FunBounds_obligation_5 _ _ _ _ _ _ _) as DD3; clear HeqDD3; simpl in DD3.
  destruct (PolyVSDenotation _ _ _ _ _) eqn:PM;rewrite PolyTerm_PolyTermVS_Correct in PM;
    (destruct (Poly_Denote FSize M a));[assert (o0 = o) as e;[qauto|destruct e];clear PM|fcrush|fcrush|auto].
  f_equal; rewrite eq_rect_ap_el; do 4 f_equal;[apply subset_eq; by rewrite projT1_eq_rect|].
  replace (fun x => lnth [seq PolyTerm_PolyTermVS i | i <- bs] (exist _ (` x) (DD1 o0 (erefl _) x))) 
    with (lnth [seq PolyTerm_PolyTermVS i | i <- bs]).
  rewrite IHbs;f_equal.
  do 3 f_equal; apply subset_eq; by rewrite projT1_eq_rect.
  apply functional_extensionality; move=> [x ltx]; do 2 rewrite eq_rect_ap_el; f_equal;
    apply subset_eq; simpl; by do 2 rewrite projT1_eq_rect.
  all: apply functional_extensionality; move=> [x ltx]; f_equal; by apply subset_eq_compat.
Qed.

Theorem Q_NoQuant_Correct M p :
  QuantifiedFormula_Denote FSize M p <-> NoQuantDenotation _ M (Q_NoQuant p).
Proof.
  move: M; elim: p.
  - move=> z M; apply ZO_NoQuant_Correct.
  - move=> bs y q IH M.
    assert ((ExtendAt0 (length bs) [eta nth 0 [seq length x.1 | x <- exiBounds (Q_NoQuant q)]]) 
                  = [eta nth 0 [seq length x.1 | x <- exiBounds
                    (NoQuantAddExi [seq PolyTerm_PolyTermVS i | i <- bs]
                                  (PolyTerm_PolyTermVS y) (Q_NoQuant q))]]) as E1.
            apply functional_extensionality=> x.
            unfold ExtendAt0.
            destruct x; simpl;[by rewrite map_length|f_equal].
            induction (exiBounds (Q_NoQuant q));auto;simpl.
            by rewrite IHl map_length.
    split=> H.
    + simpl.
      destruct H as [F [FBC H]].
      apply IH in H; clear IH.
      destruct H as [adv [H0 [H1 H2]]].
      unfold NoQuantDenotation.
      unfold NoQuantDenotation, NoQuantAdviceF.
      exists (eq_rect _ (fun x => NoQuantAdvice x _) (AdviceExtend F adv) _ E1).
      split;[|split].
      * unfold NoQuantFormulaCondition in *.
        move=> [u ltu]; simpl.
        pose (eq_rect _ (fun x => |[x]| -> 'F_FSize) u _ (map_length _ _)) as u2.
        assert (forall v, MakeU u2 v = MakeU u v) as u2el.
              move=> v.
              unfold MakeU; simpl; apply functional_extensionality=> i.
              dep_if_case (i < length (uniBounds (Q_NoQuant q)));auto;[rewrite dep_if_case_true|rewrite dep_if_case_false];try (rewrite map_length; auto).
              move=> Hyp0; unfold u2; destruct (map_length _ _); simpl; f_equal; by apply subset_eq_compat.
        assert (forall j v,
              InBound FSize
                (AddModelF FSize M (existT _ (length bs) F)) adv (u2 j)
                (lnth (uniBounds (Q_NoQuant q)) j) 
                (MakeU u2 v)) as ltu2.
              move=> [j ltj] v.
              assert (j < length [seq LiftPolyExi i | i <- uniBounds (Q_NoQuant q)]) as ltj2;[by rewrite map_length|].
              remember (ltu (exist _ j ltj2) v) as ltu'; clear Heqltu'.
              unfold InBound in *.
              remember (PolyVSDenotation _ _ _ _ _) as P.
              replace (PolyVSDenotation _ _ _ _ _) with P.
              destruct P; auto.
              replace (u2 _) with (u (exist _ j ltj2)); auto.
              unfold u2; simpl.
              destruct (map_length _ _); simpl.
              f_equal; by apply subset_eq_compat.
              rewrite HeqP; clear HeqP.
              rewrite <- Q_NoQuant_Correct_Lem_0.
              simpl.
              rewrite lnth_map; simpl.
              remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as ltj'; clear Heqltj'; simpl in ltj'.
              replace ltj' with ltj;[|apply eq_irrelevance].
              rewrite u2el.
              remember (fun A x => PolyVSDenotation (A := A) FSize M (LiftPolyExi (lnth (uniBounds (Q_NoQuant q)) (exist _ j ltj))) x (MakeU u v)) as AA.
              transitivity (AA _ (eq_rect _ (NoQuantAdvice^~ FSize) (AdviceExtend F adv) _ E1)); qauto. (* ???Why does this work??? *)
        remember (H0 (exist _ u2 ltu2)) as H0'; clear HeqH0' H0; simpl in H0'.
        rewrite <- Q_NoQuant_Correct_Lem_1 in H0'.
        rewrite u2el in H0'.
        remember (fun A x => NoQuantZODenotation FSize M (LiftPropExi (formula (Q_NoQuant q))) (A := A) x (MakeU u (fun=> 0%R))  == Some true) as AA.
        replace (NoQuantZODenotation _ _ _ (eq_rect _ (NoQuantAdvice^~ FSize) (AdviceExtend F adv) _ E1) _ == Some true)
           with (AA _ (eq_rect _ (NoQuantAdvice^~ FSize) (AdviceExtend F adv) _ E1)); qauto.
      * unfold NoQuantUniversalCondition => u [i lti] bnds; simpl in *.
        assert (i < length (uniBounds (Q_NoQuant q))) as lti2;[clear bnds; by rewrite map_length in lti|].
        assert (forall j, InBound FSize
         (AddModelF FSize M (existT _  (length bs) F)) adv (u (` j))
         (lnth (uniBounds (Q_NoQuant q)) (exist _ (` j)
            (NoQuantUniversalCondition_obligation_1 FSize (Q_NoQuant q) u (exist _ i lti2) j))) u) as YY.
                move=> j; remember (bnds j) as bnds'; clear Heqbnds' bnds; simpl in *.
                unfold InBound in *.
                remember (PolyVSDenotation _ _ _ _ _) as P.
                replace (PolyVSDenotation _ _ _ _ _) with P.
                destruct P; auto.
                rewrite HeqP; clear HeqP.
                rewrite <- Q_NoQuant_Correct_Lem_0, lnth_map; simpl.
                remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DD0; clear HeqDD0; simpl in DD0.
                remember (NoQuantUniversalCondition_obligation_1 _ _ _ _ _) as DD1; clear HeqDD1; simpl in DD1.
                replace DD1 with DD0;[|apply eq_irrelevance].
                f_equal.
                remember (fun A x => PolyVSDenotation (A := A) FSize M (LiftPolyExi (lnth (uniBounds (Q_NoQuant q)) (exist _ (` j) DD0))) x u) as AA.
                replace (PolyVSDenotation _ _ _
                  (eq_rect _ (NoQuantAdvice^~ FSize) (AdviceExtend F adv) _ E1) u)
                with (AA _ (eq_rect _ (NoQuantAdvice^~ FSize) (AdviceExtend F adv) _ E1)); qauto.
        remember (H1 u (exist _ i lti2) YY) as H1'; clear HeqH1' H1; simpl in *.
        unfold InBound in *.
        remember (PolyVSDenotation _ _ _ _ _) as P.
        replace (PolyVSDenotation _ _ _ _ _) with P.
        destruct P; auto.
        rewrite HeqP; clear HeqP.
        rewrite <- Q_NoQuant_Correct_Lem_0, lnth_map; simpl.
        remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as lti'; clear Heqlti'; simpl in lti'.
        replace lti' with lti2;[|apply eq_irrelevance].
        remember (fun A x => PolyVSDenotation FSize M (LiftPolyExi (lnth (uniBounds (Q_NoQuant q)) (exist _ i lti2))) (A := A) x u) as AA.
        replace (PolyVSDenotation _ _ _ (eq_rect _ (NoQuantAdvice^~ FSize) (AdviceExtend F adv) _ E1) _)
           with (AA _ (eq_rect _ (NoQuantAdvice^~ FSize) (AdviceExtend F adv) _ E1)); qauto.
      * unfold NoQuantExiBoundCondition.
        move=> u [[|i] lti]; simpl in *=> ins out chk.
        --  unfold Fun_Bound_Check in FBC.
            assert (F (eq_rect _ (fun x : nat => |[x]| -> 'F_FSize) ins _ (map_length PolyTerm_PolyTermVS bs)) == Some out) as YY.
                clear FBC.
                replace (F _) 
                  with (eq_rect _ (NoQuantAdvice^~ FSize) (AdviceExtend F adv) _ E1 0
                            (fun x => ins (exist _ (` x)
                                  (NoQuantExiBoundCondition_obligation_2 FSize
                                    (NoQuantAddExi [seq PolyTerm_PolyTermVS i | i <- bs]
                                        (PolyTerm_PolyTermVS y) (Q_NoQuant q))
                                    (exist _ 0 lti) ins x)))); auto; clear chk; simpl.
                remember (eq_rect _ (NoQuantAdvice^~ FSize) _ _ _ 0) as F'.
                simpl in F'.
                replace F' with (eq_rect _ (fun x => (|[x]| -> 'F_FSize) -> option 'F_FSize) F _ (esym (map_length PolyTerm_PolyTermVS bs))).
                destruct (map_length _ _); simpl.
                f_equal; apply functional_extensionality;move=> [x ltx].
                f_equal; by apply subset_eq_compat.
                rewrite HeqF'; clear HeqF' F'.
                destruct (map_length _ _); simpl.
                rewrite eq_rect_ap.
                apply functional_extensionality=> x.
                rewrite eq_rect_ap_el.
                unfold AdviceExtend; simpl.
                f_equal; apply functional_extensionality;move=> [k ltk]; simpl.
                rewrite eq_rect_ap_el.
                f_equal.
                apply subset_eq; by rewrite projT1_eq_rect.
            remember (FBC (eq_rect _ (fun x => |[x]| -> 'F_FSize) ins _ (map_length PolyTerm_PolyTermVS _)) out YY) as FBC'; clear HeqFBC' FBC YY.
            replace (fun x => lnth _ _) with (lnth [seq PolyTerm_PolyTermVS i | i <- bs]);[
              by rewrite Q_NoQuant_Correct_Lem_3|].
            apply functional_extensionality; move=> [x ltx]; f_equal; by apply subset_eq_compat.
        --  assert (i < length (exiBounds (Q_NoQuant q))) as lti2;[clear chk ins; by rewrite map_length in lti|].
            assert (lnth [seq length x.1 | x <- [seq ([seq LiftPolyExi i | i <- x.1], LiftPolyExi x.2)
                                  | x <- exiBounds (Q_NoQuant q)]]
                    (exist _ i (NoQuantExiBoundCondition_obligation_1
                          (NoQuantAddExi [seq PolyTerm_PolyTermVS i | i <- bs]
                            (PolyTerm_PolyTermVS y) (Q_NoQuant q))
                          (exist _ i.+1 lti))) =
                    lnth [seq length x.1 | x <- exiBounds (Q_NoQuant q)]
                    (exist _ i (NoQuantExiBoundCondition_obligation_1 
                      (Q_NoQuant q) (exist _ i lti2)))) as E2.
                  do 3 rewrite lnth_map; simpl; rewrite map_length.
                  remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DD0; clear HeqDD0; simpl in DD0.
                  remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DD1; clear HeqDD1; simpl in DD1.
                  replace DD0 with DD1;[auto|apply eq_irrelevance].
                  f_equal.
            assert (adv i (fun x => eq_rect _ (fun x => |[x]| -> _) ins _ E2 (exist _ (` x)
                    (NoQuantExiBoundCondition_obligation_2 _ _ (exist _ i lti2) (eq_rect _ (fun x => |[x]| -> _) ins _ E2) x)))
                    == Some out) as YY.
                  remember (eq_rect _ (NoQuantAdvice^~ FSize) _ _ _ _ _) as LLL.
                  replace (adv _ _) with LLL; auto; rewrite HeqLLL; clear HeqLLL LLL chk.
                  rewrite eq_rect_ap eq_rect_ap_el; simpl.
                  unfold AdviceExtend; simpl.
                  f_equal.
                  apply functional_extensionality; move=>[x ltx]; simpl.
                  do 2 rewrite eq_rect_ap_el; simpl; f_equal;
                  apply subset_eq; simpl; by do 2 rewrite projT1_eq_rect.
            remember (H2 u (exist _ i lti2) (eq_rect _ (fun x => |[x]| -> _) ins _ E2) out YY) as H2'; clear YY chk HeqH2' H2; simpl in H2'.
            rewrite Q_NoQuant_Correct_Lem_2 in H2'.
            remember (FunBoundsVS _ _ _ _ _ _ _ _) as FB1.
            replace (FunBoundsVS _ _ _ _ _ _ _ _) with FB1; auto.
            rewrite HeqFB1; clear HeqFB1 FB1 H2'.
            remember (AdviceExtend F adv) as ADV1.
            remember (eq_rect _ (NoQuantAdvice^~ FSize) ADV1 _ E1) as ADV2.
            remember (eq_rect _ (fun x : nat => |[x]| -> 'F_FSize) ins _ E2) as ins1.
            remember (fun x => LiftPolyExi (lnth _ _)) as insB1.
            remember (fun x => lnth _ _) as insB2.
            remember (LiftPolyExi _) as outB1.
            remember (lnth _ (exist (fun n : nat => n < length
                      [seq x.2 | x <- [seq ([seq LiftPolyExi i | i <- x.1], LiftPolyExi x.2)
                      | x <- exiBounds (Q_NoQuant q)]]) i _)) as outB2.
            transitivity (FunBoundsVS FSize M ADV2 ins1 out insB1 outB1 u);[
              rewrite HeqADV2 HeqADV1; by destruct E1|clear HeqADV1 ADV1 HeqADV2].
            replace outB1 with outB2;[clear HeqoutB1 outB1 HeqoutB2 |
              rewrite HeqoutB1 HeqoutB2; do 3 rewrite lnth_map; simpl; do 3 f_equal; by apply subset_eq_compat].
            transitivity (FunBoundsVS FSize M ADV2 (eq_rect _ (fun x => |[x]| -> _) ins _ E2) out 
                                                   (eq_rect _ (fun x => |[x]| -> _) insB2 _ E2) outB2 u).
                f_equal.
                by rewrite Heqins1.
                rewrite HeqinsB1; clear HeqinsB1 insB1.
                apply functional_extensionality;move=>[x ltx]; simpl.
                rewrite eq_rect_ap_el.
                rewrite HeqinsB2; clear HeqinsB2.
                rewrite (lnth_nth PolyZeroVS); simpl.
                rewrite (lnth_nth ([::], PolyZeroVS).1).
                rewrite nth_map; simpl.
                rewrite (lnth_nth PolyZeroVS); simpl.
                rewrite projT1_eq_rect; simpl.
                do 2 rewrite lnth_map; simpl.
                change (PolyZeroVS) with (LiftPolyExi PolyZeroVS).
                rewrite nth_map; simpl. 
                do 2 f_equal.
                by rewrite (lnth_nth ([::], PolyZeroVS)).
            rewrite HeqinsB2; clear HeqinsB2 HeqinsB1 insB1 Heqins1 ins1.
            by destruct E2.
    + simpl.
      destruct H as [adv [H0 [H1 H2]]].
      simpl in adv.
      unfold NoQuantAdviceF in adv; simpl in adv.
      exists (eq_rect _ (fun x => (|[x]| -> _) -> _) (adv 0) _ (map_length PolyTerm_PolyTermVS _)).
      simpl; split.
      unfold Fun_Bound_Check=> ins out io.
      rewrite eq_rect_ap_el in io.
      remember (H2 (fun=> 0%R) (exist _ 0 (ltn0Sn _)) 
                   (eq_rect _ (fun x : nat => |[x]| -> 'F_FSize) ins _
                   (esym (map_length PolyTerm_PolyTermVS bs))) out) as H2'; clear HeqH2' H2; simpl in H2'.
      remember (NoQuantExiBoundCondition_obligation_2 _ (NoQuantAddExi _ _ _) (exist (fun n : nat => n < (length _).+1) 0 _) _) as DDD; clear HeqDDD; simpl in *.
      assert (adv 0 (fun x => eq_rect _ (fun x => |[x]| -> 'F_FSize) ins _
           (esym (map_length PolyTerm_PolyTermVS bs)) (exist _ (` x) (DDD x))) == Some out) as HH.
          replace (fun x => eq_rect _ (fun x => |[x]| -> 'F_FSize) ins _ _ _) 
            with (eq_rect _ (fun x => |[x]| -> 'F_FSize) ins _ (esym (map_length PolyTerm_PolyTermVS bs))); auto.
          apply functional_extensionality;move=>[x ltx]; simpl.
          do 2 rewrite eq_rect_ap_el; f_equal.
          destruct (esym (esym (map_length PolyTerm_PolyTermVS bs))); simpl; by apply subset_eq_compat.
      remember (H2' HH) as H2; clear HeqH2 H2' HH.
      assert (FunBoundsVS FSize M adv
       (eq_rect (length bs) (fun x : nat => {n : nat | n < x} -> 'F_FSize) ins
          (length [seq PolyTerm_PolyTermVS i | i <- bs])
          (esym (map_length PolyTerm_PolyTermVS bs))) out
       (lnth [seq PolyTerm_PolyTermVS i | i <- bs])
       (PolyTerm_PolyTermVS y) (fun=> 0%R) == true);[|clear H2].
          remember (FunBoundsVS _ _ _ _ _ _ _) as F1; replace (FunBoundsVS _ _ _ _ _ _ _) with F1; auto; rewrite HeqF1; f_equal.
          apply functional_extensionality; move=>[x ltx]; f_equal; by apply subset_eq_compat.      
      rewrite Q_NoQuant_Correct_Lem_3 in H.
      remember (FunBounds _ _ _ _ _ _) as F1; replace (FunBounds _ _ _ _ _ _) with F1; auto; rewrite HeqF1; f_equal.
      apply functional_extensionality;move=> [x ltx].
      do 2 rewrite eq_rect_ap_el.
      f_equal; apply subset_eq; by do 2 rewrite projT1_eq_rect.
      apply IH.
      unfold NoQuantDenotation.
      unfold NoQuantAdviceF.
      unfold NoQuantAdvice in adv.
      unfold NoQuantAdvice.
      assert ([seq length x0.1
               | x0 <- [seq ([seq LiftPolyExi i | i <- x0.1], LiftPolyExi x0.2)
                          | x0 <- exiBounds (Q_NoQuant q)]] = [seq length x.1 | x <- exiBounds (Q_NoQuant q)]) as E2.
          clear H0 H1 H2 adv E1.
          induction (exiBounds (Q_NoQuant q));[auto|simpl;rewrite IHl; simpl; by rewrite map_length].
      exists (fun i => (eq_rect _ (fun x => (|[nth 0 x i]| -> _) -> _) (adv (i.+1)) _ E2)).
      split;[|split].
      * move=>[u lti]; simpl.
        simpl in H0.
        remember (eq_rect _ (fun x => |[x]| -> _) u _ (esym (map_length LiftPolyExi _))) as u'.
        assert (forall
                (j : {n : nat | n < length (uniBounds (Q_NoQuant (QExists bs y q)))})
                (v : nat -> 'F_FSize),
              InBound FSize M adv (u' j)
                (lnth (uniBounds (Q_NoQuant (QExists bs y q))) j) 
                (MakeU u' v)) as ltu'.
              move=> [j ltj] v.
              assert (j < length (uniBounds (Q_NoQuant q))) as ltj2;[simpl in ltj; by rewrite map_length in ltj|].
              remember (lti (exist _ j ltj2) v) as lti2; clear lti Heqlti2.
              unfold InBound in *.
              rewrite <- Q_NoQuant_Correct_Lem_0 in lti2.
              remember (PolyVSDenotation _ _ _ _ _) as P; replace (PolyVSDenotation _ _ _ _ _) with P;[destruct P|rewrite HeqP];auto.
              rewrite Hequ'; clear HeqP Hequ'.
              rewrite eq_rect_ap_el.
              destruct (esym (esym (map_length LiftPolyExi (uniBounds (Q_NoQuant q))))); simpl.
              replace ltj with ltj2;[auto|apply eq_irrelevance].
              clear HeqP lti2.
              destruct (map_length PolyTerm_PolyTermVS bs); simpl.
              rewrite lnth_map; simpl.
              destruct E2; simpl.
              transitivity (PolyVSDenotation _ M (LiftPolyExi (lnth (uniBounds (Q_NoQuant q)) (exist _ j ltj2)))
                (eq_rect _ (fun x => NoQuantAdvice x _) adv _ (esym E1)) (MakeU u v)).
              f_equal.
              apply functional_extensionality_dep=>x.
              rewrite eq_rect_ap.
              apply functional_extensionality_dep=>u2.
              rewrite eq_rect_ap_el.
              destruct x.
              unfold AdviceExtend; simpl.
              f_equal.
              apply functional_extensionality=>z.
              rewrite eq_rect_ap_el.
              f_equal; apply subset_eq; by rewrite projT1_eq_rect.
              unfold AdviceExtend; simpl.
              f_equal; apply functional_extensionality=> z. 
              rewrite eq_rect_ap_el; f_equal.
              apply subset_eq; by rewrite projT1_eq_rect.
              destruct (esym E1); simpl.
              f_equal;[do 2 f_equal; by apply subset_eq|rewrite Hequ'; by destruct (esym _)].
        remember (H0 (exist _ u' ltu')) as H0'; clear H0 HeqH0'; simpl in H0'.
        rewrite <- Q_NoQuant_Correct_Lem_1.
        remember (NoQuantZODenotation _ _ _ _ _) as P; replace (NoQuantZODenotation _ _ _ _ _) with P;[destruct P|rewrite HeqP];auto.
        transitivity (NoQuantZODenotation _ M (LiftPropExi (formula (Q_NoQuant q)))
                (eq_rect _ (fun x => NoQuantAdvice x _) adv _ (esym E1)) (MakeU u (fun=> 0%R))).              
        destruct (esym E1); simpl; f_equal.
        rewrite Hequ'; clear H0' HeqP P ltu' Hequ' u' lti E2 E1 H1 H2 adv.
        apply functional_extensionality=> x.
        unfold MakeU.
        dep_if_case (x < length [seq LiftPolyExi i | i <- uniBounds (Q_NoQuant q)]); auto.
        rewrite dep_if_case_true.
        by rewrite map_length in H.
        move=> Hy.
        rewrite eq_rect_ap_el; f_equal.
        apply subset_eq; by rewrite projT1_eq_rect.
        rewrite dep_if_case_false;[by rewrite map_length in H|auto].
        f_equal.
        apply functional_extensionality_dep=>x.
        rewrite eq_rect_ap.
        apply functional_extensionality_dep=>u2.
        rewrite eq_rect_ap_el.
        destruct x.
        unfold AdviceExtend; simpl.
        rewrite eq_rect_ap_el.
        f_equal.
        apply functional_extensionality;move=>[x ltx].
        do 2 rewrite eq_rect_ap_el; f_equal.
        apply subset_eq; rewrite projT1_eq_rect; simpl; by rewrite projT1_eq_rect.
        unfold AdviceExtend; simpl.
        rewrite eq_rect_ap_el; f_equal.
        apply functional_extensionality_dep;move=>[z ltz].
        do 2 rewrite eq_rect_ap_el; f_equal.
        apply subset_eq; rewrite projT1_eq_rect; simpl; by rewrite projT1_eq_rect.
      * move=> u [i lti] bnd; simpl in *.
        assert (i < length (uniBounds (NoQuantAddExi
                      [seq PolyTerm_PolyTermVS i | i <- bs]
                      (PolyTerm_PolyTermVS y) 
                      (Q_NoQuant q)))) as lti2;[
              cbn; by rewrite map_length|].
        assert (forall j, InBound FSize M adv (u (` j))
         (lnth [seq LiftPolyExi i | i <- uniBounds (Q_NoQuant q)]
            (exist _ (` j) (NoQuantUniversalCondition_obligation_1
                  _ _ u (exist _ i lti2) j))) u) as YY.
              move=>j; remember (bnd j) as bnd'; clear bnd Heqbnd'.
              unfold InBound in *.
              rewrite <- Q_NoQuant_Correct_Lem_0 in bnd'.
              remember (PolyVSDenotation _ _ _ _ _) as P; replace (PolyVSDenotation _ _ _ _ _) with P;[destruct P|rewrite HeqP];auto.
              rewrite lnth_map; simpl.
              remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
              remember (NoQuantUniversalCondition_obligation_1 _ _ _ _ _) as DDD1; clear HeqDDD1; simpl in DDD1.
              clear HeqP bnd'.
              replace DDD1 with DDD0;[|apply eq_irrelevance].
              transitivity (PolyVSDenotation FSize M (LiftPolyExi (lnth (uniBounds (Q_NoQuant q)) (exist _ (` j) DDD0))) 
                    (eq_rect _ (fun x => NoQuantAdvice x _) adv _ (esym E1)) u).
              f_equal.
              apply functional_extensionality_dep=>x.
              rewrite eq_rect_ap.
              apply functional_extensionality_dep=>u2.
              rewrite eq_rect_ap_el.
              destruct x.
              unfold AdviceExtend; simpl.
              rewrite eq_rect_ap_el.
              f_equal.
              apply functional_extensionality;move=>[x ltx].
              do 2 rewrite eq_rect_ap_el; f_equal.
              apply subset_eq; simpl; rewrite projT1_eq_rect; simpl; by rewrite projT1_eq_rect.
              unfold AdviceExtend; simpl.
              rewrite eq_rect_ap_el; f_equal.
              apply functional_extensionality_dep;move=>[z ltz].
              do 2 rewrite eq_rect_ap_el; f_equal.
              apply subset_eq; simpl; rewrite projT1_eq_rect; simpl; by rewrite projT1_eq_rect.
              by destruct (esym E1).
        remember (H1 u (exist _ i lti2) YY) as H1'; clear H1 HeqH1' bnd YY; simpl in H1'.
        unfold InBound in *.
        rewrite <- Q_NoQuant_Correct_Lem_0.
        remember (PolyVSDenotation _ _ _ _ _) as P; replace (PolyVSDenotation _ _ _ _ _) with P;[destruct P|rewrite HeqP];auto.
        rewrite lnth_map; simpl.
        remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
        replace DDD0 with lti;[|apply eq_irrelevance]; clear DDD0.
        transitivity (PolyVSDenotation FSize M (LiftPolyExi (lnth (uniBounds (Q_NoQuant q)) (exist _ i lti)))
              (eq_rect _ (fun x => NoQuantAdvice x _) adv _ (esym E1)) u).
        by destruct (esym E1).
        f_equal.
        apply functional_extensionality_dep=>x.
        rewrite eq_rect_ap.
        apply functional_extensionality_dep=>u2.
        rewrite eq_rect_ap_el.
        destruct x.
        unfold AdviceExtend; simpl.
        rewrite eq_rect_ap_el.
        f_equal.
        apply functional_extensionality;move=>[x ltx].
        do 2 rewrite eq_rect_ap_el; f_equal.
        apply subset_eq; simpl; rewrite projT1_eq_rect; simpl; by rewrite projT1_eq_rect.
        unfold AdviceExtend; simpl.
        rewrite eq_rect_ap_el; f_equal.
        apply functional_extensionality_dep;move=>[z ltz].
        do 2 rewrite eq_rect_ap_el; f_equal.
        apply subset_eq; simpl; rewrite projT1_eq_rect; simpl; by rewrite projT1_eq_rect.
      * unfold NoQuantExiBoundCondition.
        move=> u [i lti] ins out io; simpl in *.
        assert (i.+1 < length (exiBounds (NoQuantAddExi [seq PolyTerm_PolyTermVS i | i <- bs]
                       (PolyTerm_PolyTermVS y)  (Q_NoQuant q)))) as lti2.
              simpl; by rewrite map_length.
        assert (lnth _ (exist _ i (NoQuantExiBoundCondition_obligation_1
                (Q_NoQuant q) (exist _ i lti))) = 
              lnth _ (exist _ i
                      (NoQuantExiBoundCondition_obligation_1
                         (NoQuantAddExi [seq PolyTerm_PolyTermVS i | i <- bs]
                           (PolyTerm_PolyTermVS y)
                           (Q_NoQuant q))
                         (exist _ i.+1 lti2)))) as E3.
                do 3 rewrite lnth_map; simpl.
                remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD0; clear HeqDDD0;
                remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD1; clear HeqDDD1; simpl in *.
                rewrite map_length.
                by replace DDD1 with DDD0;[|apply eq_irrelevance].
        remember (H2 u (exist _ i.+1 lti2) (eq_rect _ (fun x => |[x]| -> _) ins _ E3) out) as H2'; clear HeqH2' H2; simpl in H2'.
        rewrite eq_rect_ap_el in io.
        remember (adv i.+1 _) as A0.
        replace (adv i.+1 _) with A0 in io.
        remember (H2' io) as H2; clear H2' HeqH2 io.
        rewrite Q_NoQuant_Correct_Lem_2.
        remember (FunBoundsVS _ _ _ _ _ _ _) as P; replace (FunBoundsVS _ _ _ _ _ _ _) with P;[destruct P|rewrite HeqP];auto.
        clear H2 HeqP.
        remember (AdviceExtend _ _) as ADV1.
        remember (eq_rect _ (fun x : nat => |[x]| -> 'F_FSize) ins _ _) as ins1.
        remember (fun x => LiftPolyExi (lnth _ _)) as insB1.
        remember (fun x => lnth _ _) as insB2.
        remember (LiftPolyExi _) as outB1.
        remember (lnth _ (exist (fun n : nat => n < length
                  [seq x.2 | x <- [seq ([seq LiftPolyExi i | i <- x.1], LiftPolyExi x.2)
                  | x <- exiBounds (Q_NoQuant q)]]) i _)) as outB2.
        replace outB2 with outB1.
        transitivity (FunBoundsVS FSize M adv (eq_rect _ (fun x => |[x]| -> _) ins _ E3) out 
                                              (eq_rect _ (fun x => |[x]| -> _) insB1 _ E3) outB1).
        f_equal.
        rewrite Heqins1; clear Heqins1 ins1 HeqA0 HeqinsB2 HeqoutB2.
        apply functional_extensionality;move=>[x ltx].
        rewrite eq_rect_ap_el; f_equal.
        rewrite HeqinsB2; clear HeqA0 HeqinsB2 HeqoutB2.
        rewrite HeqinsB1; clear HeqinsB1 HeqoutB1.
        apply functional_extensionality;move=>[x ltx].
        rewrite eq_rect_ap_el; f_equal; simpl.
        rewrite (lnth_nth PolyZeroVS); simpl.
        rewrite (lnth_nth ([::], PolyZeroVS).1).
        rewrite nth_map; simpl.
        change ([::], PolyZeroVS) with
          ([seq LiftPolyExi i | i <- ([::] : seq PolyTermVS, PolyZeroVS).1], LiftPolyExi ([::] : seq PolyTermVS, PolyZeroVS).2).
        rewrite nth_map; simpl.
        change (nth PolyZeroVS) with (nth (LiftPolyExi PolyZeroVS)).
        rewrite nth_map; simpl.
        rewrite (lnth_nth PolyZeroVS); simpl.
        rewrite projT1_eq_rect; simpl.
        rewrite (lnth_nth ([::], PolyZeroVS).1).
        by rewrite nth_map; simpl.
        transitivity (FunBoundsVS _ M adv ins out insB1 outB1).
        clear HeqinsB1 HeqinsB2 HeqoutB2 HeqoutB1 HeqADV1 ADV1 P HeqA0 A0 Heqins1 ins1. 
        by destruct E3.
        transitivity (FunBoundsVS FSize M (eq_rect _ (fun x => NoQuantAdvice x _) adv _ (esym E1)) ins out insB1 outB1).
        by destruct (esym E1).
        f_equal.
        rewrite HeqADV1.
        apply functional_extensionality_dep=>x.
        rewrite eq_rect_ap.
        apply functional_extensionality_dep=>u2.
        rewrite eq_rect_ap_el.
        destruct x.
        unfold AdviceExtend; simpl.
        rewrite eq_rect_ap_el.
        f_equal.
        apply functional_extensionality;move=>[x ltx].
        do 2 rewrite eq_rect_ap_el; f_equal.
        apply subset_eq; simpl; rewrite projT1_eq_rect; simpl; by rewrite projT1_eq_rect.
        unfold AdviceExtend; simpl.
        rewrite eq_rect_ap_el; f_equal.
        apply functional_extensionality_dep;move=>[z ltz].
        do 2 rewrite eq_rect_ap_el; f_equal.
        apply subset_eq; simpl; rewrite projT1_eq_rect; simpl; by rewrite projT1_eq_rect.
        rewrite HeqoutB1 HeqoutB2.
        do 3 rewrite lnth_map; simpl.
        do 3 f_equal; by apply subset_eq_compat.
        rewrite HeqA0; f_equal.
        apply functional_extensionality;move=>[x ltx].
        do 2 rewrite eq_rect_ap_el; f_equal.
        apply subset_eq; simpl; rewrite projT1_eq_rect; simpl; by rewrite projT1_eq_rect.
  - 
      * 
        rewrite HeqADV1.

v        f_equal.
        destruct E3.
        remember (NoQuantExiBoundCondition_obligation_1 _ _) as DDD0; clear HeqDDD0.
        remember (NoQuantExiBoundCondition_obligation_3 _ _ _ _ _) as DDD1; clear HeqDDD1.

        simpl.
        f_equal.
        destruct E3.


        rewrite nth_map; simpl.
        do 2 rewrite lnth_map; simpl.
        change (PolyZeroVS) with (LiftPolyExi PolyZeroVS).
        rewrite nth_map; simpl. 
        do 2 f_equal.
        by rewrite (lnth_nth ([::], PolyZeroVS)).


        do 2 rewrite lnth_map; simpl.
        change (PolyZeroVS) with (LiftPolyExi PolyZeroVS).
        rewrite nth_map; simpl. 
        do 2 f_equal.
        by rewrite (lnth_nth ([::], PolyZeroVS)).
        remember (NoQuantExiBoundCondition_obligation_4 _ _ _ _ _) as DDD0; clear HeqDDD0.
        remember (NoQuantExiBoundCondition_obligation_3 _ _ _ _ _) as DDD1; clear HeqDDD1.
        rewrite lnth_map.
        remember (NoQuantExiBoundCondition_obligation_3 _ _ _ _) as DDD2; clear HeqDDD2.
        remember (NoQuantExiBoundCondition_obligation_5 _ _ _ _) as DDD2; clear HeqDDD2.
        rewrite lnth_map.
        do 2 rewrite eq_rect_ap_el; f_equal.
        destruct E3.
        transitivity (FunBoundsVS FSize M adv (eq_rect _ (fun x => |[x]| -> _) ins1 _ E3) out 
                                              (eq_rect _ (fun x => |[x]| -> _) insB2 _ E3) outB1 u).
            f_equal.
        remember (NoQuantExiBoundCondition_obligation_4 _ _ _ _) as DDD0; clear HeqDDD0.
        remember (NoQuantExiBoundCondition_obligation_3 _ _ _ _) as DDD1; clear HeqDDD1.
        remember (NoQuantExiBoundCondition_obligation_5 _ _ _ _) as DDD2; clear HeqDDD2.
        rewrite lnth_map; simpl.
        replace (FunBoundsVS FSize M adv) with
           (FunBoundsVS FSize M (eq_rect _ (fun x => NoQuantAdvice x _) adv _ (esym E1))).
        f_equal.
        remember (NoQuantExiBoundCondition_obligation_1 _ _) as DDD; clear HeqDDD.

        remember (NoQuantExiBoundCondition_obligation_2 _ _ _ _) as DDD; clear HeqDDD.

          destruct (lnth (exiBounds (Q_NoQuant q))
              (exist
                 (fun n : nat =>
                  n <
                  length
                    (exiBounds
                       (Q_NoQuant q))) i
                 DDD0));simpl.
          simpl in *.
          simpl.
          fold map.
          auto.
        remember (eq_rect _ (fun x => |[x]| -> _) ins _ (esym E2)).
        remember (eq_rect _ (fun x => |[x]| -> _) ins _ E1).
        rewrite eq_rect_ap_el.
        rewrite eq_rect_ap.

        rewrite eq_rect_ap_el.
        by destruct E2.
unfold NoQuantUniversalCondition.

        replace (fun x => u2 _) with u2.
        clear Hequ' u' ltj2 ltj P u.
        destruct (esym E1).
        destruct (esym E1).
        apply eq_rect_ap_el.
        destruct (esym E1).

        apply eq_rect_ap_el.
        unfold AdviceExtend.
        apply functional_extensionality=>x2.
        destruct (esym E1).
        
        replace (AdviceExtend (adv 0) (fun i : nat => adv i.+1)) with .
        destruct E1.
        f_equal.
        replace (Utils.lnth_map_obligation_1 PolyTermVS PolyTermVS LiftPolyExi
              (uniBounds (Q_NoQuant q))
              (exist
                 (fun n : nat =>
                  n < length [seq LiftPolyExi i | i <- uniBounds (Q_NoQuant q)]) j ltj)) with ltj2.
        f_equal.
      Search (_ <-> ` _ = _).
      rewrite eq_rect_ap_el.

rewrite <- Q_NoQuant_Correct_Lem_3.
      

    FunBoundsVS FSize M adv ins out (lnth [seq PolyTerm_PolyTermVS i | i <- bs])
      (PolyTerm_PolyTermVS y) u =
    FunBounds FSize M
      (eq_rect _ (fun x => |[x]| -> 'F_FSize) ins _ (map_length PolyTerm_PolyTermVS bs)) out 
      (lnth bs) y.


        simpl.
      simpl in H2.
      rewrite map_length in adv.
      unfold NoQuantDenotation in H.

            rewrite projT1_eq_rect; simpl.
            rewrite nth_map; simpl.
            remember (NoQuantExiBoundCondition_obligation_4 _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
            remember (NoQuantExiBoundCondition_obligation_3 _ _ _ _ _) as DDD1; clear HeqDDD1; simpl in DDD1.
            remember (NoQuantExiBoundCondition_obligation_4 _ _ _ _ _) as DDD3; clear HeqDDD3; simpl in DDD3.
            remember (NoQuantExiBoundCondition_obligation_3 _ _ _ _ _) as DDD2; clear HeqDDD2; simpl in DDD2.
            rewrite (lnth_nth PolyZeroVS); simpl.
            rewrite (lnth_nth ([::], PolyZeroVS).1).
            rewrite nth_map; simpl.
            rewrite (lnth_nth PolyZeroVS); simpl.
            rewrite (lnth_nth ([::], PolyZeroVS).1).
            rewrite nth_map; simpl.
            rewrite projT1_eq_rect; simpl.

LiftPolyExi
  (nth PolyZeroVS
     (nth ([::], PolyZeroVS).1 [seq x0.1 | x0 <- exiBounds (Q_NoQuant q)]
        (` (exist (fun n : nat => n < length [seq x0.1 | x0 <- exiBounds (Q_NoQuant q)]) i DDD1))) x)
LiftPolyExi
  (nth PolyZeroVS
     (nth ([::], PolyZeroVS) (exiBounds (Q_NoQuant q)) (` (exist (fun n : nat => n < length [seq x0.1 | x0 <- exiBounds (Q_NoQuant q)]) i DDD1))).1 x)

            rewrite nth_map.
Check exiBounds.
            rewrite (lnth_nth ((PolyZeroVS, [::]).1)).
            do 2 rewrite (lnth_nth PolyMinusOneVS); simpl.
            rewrite lnth_map.
            f_equal.
            destruct E2.
            2:{ f_equal. destruct E2.
            destruct E2.
                rewrite lnth_map; simpl.
                rewrite lnth_map; simpl.
            Set Printing Implicit.


  (lnth
     [seq x.2
        | x <- [seq ([seq LiftPolyExi i | i <- x.1], LiftPolyExi x.2)
                  | x <- exiBounds (Q_NoQuant q)]]
     (exist
        (fun n : nat =>
         n <
         length
           [seq x.2
              | x <- [seq ([seq LiftPolyExi i | i <- x.1], LiftPolyExi x.2)
                        | x <- exiBounds (Q_NoQuant q)]]) i
        (NoQuantExiBoundCondition_obligation_5 FSize
           (NoQuantAddExi [seq PolyTerm_PolyTermVS i | i <- bs]
              (PolyTerm_PolyTermVS y) (Q_NoQuant q))
           (exist
              (fun n : nat =>
               n <
               (length
                  [seq ([seq LiftPolyExi i | i <- x.1], LiftPolyExi x.2)
                     | x <- exiBounds (Q_NoQuant q)]).+1) i.+1 lt
            simpl in ADV2.
            replace (AdviceExtend F adv) with ADV2.

            replace ADV1 with ADV2.
            destruct E1.
            f_equal.
            replace (eq_rect
     (ExtendAt0 (length bs)
        [eta nth 0 [seq length x.1 | x <- exiBounds (Q_NoQuant q)]])
     (NoQuantAdvice^~ FSize) (AdviceExtend F adv)
     [eta nth 0
            (length [seq PolyTerm_PolyTermVS i0 | i0 <- bs]
             :: [seq length x.1
                   | x <- [seq ([seq LiftPolyExi i | i <- x.1],
                               LiftPolyExi x.2)
                             | x <- exiBounds (Q_NoQuant q)]])] E1) with  (AdviceExtend F adv).


Lemma Q_NoQuant_Correct_Lem_2 {M u p a f A adv} :
  NoQuantZODenotation FSize M (LiftPropExi p) (AdviceExtend f adv) u
  = FunBounds _ (AddModelF _ M (existT _ a f)) ar  u.
Proof.
  elim: p; try qauto.
  move=> p1 p2.
  simpl.
  by do 2 rewrite Q_NoQuant_Correct_Lem_0.
Qed.

            rewrite <- Q_NoQuant_Correct_Lem_0 in H2'.
            remember (FunBounds _ _ _ _ _ _) as FF.
            replace (FunBounds _ _ _ _ _ _) with FF; auto; rewrite HeqFF; clear HeqFF FF H2'.
            remember (eq_rect _ (fun x : nat => |[x]| -> 'F_FSize) ins _ E2) as ins2.
            remember (fun x : |[lnth [seq length x.1 | x <- exiBounds (Q_NoQuant q)]
                        (exist _ i
                            (NoQuantExiBoundCondition_obligation_1 
                              (Q_NoQuant q)
                              (exist
                                  (fun n0 : nat => n0 < length (exiBounds (Q_NoQuant q)))
                                  i lti2)))]| => _) as BS2.
            remember (fun x : |[lnth
             [seq length x.1
                | x <- [seq ([seq LiftPolyExi i | i <- x.1], LiftPolyExi x.2)
                          | x <- exiBounds (Q_NoQuant q)]]
             (exist _ i
                (NoQuantExiBoundCondition_obligation_1
                   (NoQuantAddExi [seq PolyTerm_PolyTermVS i | i <- bs]
                      (PolyTerm_PolyTermVS y) (Q_NoQuant q))
                   (exist
                      (fun n0 =>
                       n0 <
                       (length
                          [seq ([seq LiftPolyExi i | i <- x.1],
                               LiftPolyExi x.2)
                             | x <- exiBounds (Q_NoQuant q)]).+1) i.+1 lti)))]| => _) as BS1. 
            remember (PolyVSDenotation FSize 

            remember 

            destruct E2.
            cbn.
            rewrite <- Q_NoQuant_Correct_Lem_0.
            remember (NoQuantExiBoundCondition_obligation_1 _ _) as DD0.
\            rewrite eq_rect_ap_el.

            rewrite eq_rect_ap.
            simpl in *.
            unfold FunBounds.
            remember (lnth [seq length x.1 | x <- exiBounds (Q_NoQuant q)] _) as L0.
        clear FBC'; destruct (map_length _ _); qauto.
        rewrite lnth_map map_length.
        
        simpl.
        rewrite map_length.
        replace (fun x =>
   PolyVSDenotation FSize M
     (lnth [seq PolyTerm_PolyTermVS i | i <- bs]
        (exist
           (fun n : nat => n < length [seq PolyTerm_PolyTermVS i | i <- bs])
           (` x)
           (NoQuantExiBoundCondition_obligation_4 FSize
              (NoQuantAddExi [seq PolyTerm_PolyTermVS i | i <- bs]
                 (PolyTerm_PolyTermVS y) (Q_NoQuant q))
              (exist
                 (fun n : nat =>
                  n <
                  (length
                     [seq ([seq LiftPolyExi i | i <- x0.1], LiftPolyExi x0.2)
                        | x0 <- exiBounds (Q_NoQuant q)]).+1) 0 lti) ins x)))
     (eq_rect
        (ExtendAt0 (length bs)
           [eta nth 0 [seq length x0.1 | x0 <- exiBounds (Q_NoQuant q)]])
        (NoQuantAdvice^~ FSize) (AdviceExtend F adv)
        [eta nth 0
               (length [seq PolyTerm_PolyTermVS i | i <- bs]
                :: [seq length x1.1
                      | x1 <- [seq ([seq LiftPolyExi i | i <- x1.1],
                                   LiftPolyExi x1.2)
                                 | x1 <- exiBounds (Q_NoQuant q)]])] E1) u)
        with (fun x => lnth [seq Poly_Denote FSize M i | i <- bs] x).
        unfold FunBounds.
        rewrite <- lnth_map.
        PolyVSDenotation FSize M (PolyTerm_PolyTermVS
        unfold FunBounds.

        remember (H2 u) as H2'; clear HeqH2' H2; simpl in *.
    

FBC :  Fun_Bound_Check FSize M (lnth bs) y F
FunBounds FSize M ins out
  (fun x : {n : nat | n < length [seq PolyTerm_PolyTermVS i | i <- bs]} =>
   PolyVSDenotation FSize M
     (lnth [seq PolyTerm_PolyTermVS i | i <- bs]
        (exist
           (fun n : nat => n < length [seq PolyTerm_PolyTermVS i | i <- bs])
           (` x)
           (NoQuantExiBoundCondition_obligation_4 FSize
              (NoQuantAddExi [seq PolyTerm_PolyTermVS i | i <- bs]
                 (PolyTerm_PolyTermVS y) (Q_NoQuant q))
              (exist
                 (fun n : nat =>
                  n <
                  (length
                     [seq ([seq LiftPolyExi i | i <- x0.1], LiftPolyExi x0.2)
                        | x0 <- exiBounds (Q_NoQuant q)]).+1) 0 lti) ins x)))
     (eq_rect
        (ExtendAt0 (length bs)
           [eta nth 0 [seq length x0.1 | x0 <- exiBounds (Q_NoQuant q)]])
        (NoQuantAdvice^~ FSize) (AdviceExtend F adv)
        [eta nth 0
               (length [seq PolyTerm_PolyTermVS i | i <- bs]
                :: [seq length x1.1
                      | x1 <- [seq ([seq LiftPolyExi i | i <- x1.1],
                                   LiftPolyExi x1.2)
                                 | x1 <- exiBounds (Q_NoQuant q)]])] E1) u)
  (PolyVSDenotation FSize M (PolyTerm_PolyTermVS y)
     (eq_rect
        (ExtendAt0 (length bs)
           [eta nth 0 [seq length x.1 | x <- exiBounds (Q_NoQuant q)]])
        (NoQuantAdvice^~ FSize) (AdviceExtend F adv)
        [eta nth 0
               (length [seq PolyTerm_PolyTermVS i | i <- bs]
                :: [seq length x.1
                      | x <- [seq ([seq LiftPolyExi i | i <- x.1],
                                  LiftPolyExi x.2)
                                | x <- exiBounds (Q_NoQuant q)]])] E1) u)


        replace (NoQuantZODenotation FSize M (LiftPropExi (formula (Q_NoQuant q))) (A := ?A) ?x (MakeU u (fun=> 0%R)) == Some true)
          with (AA _ x).
        transitivity (AA _ (eq_rect _ (NoQuantAdvice^~ FSize) (AdviceExtend F adv) _ E1)); qauto. (* ???Why does this work??? *)
              
        qauto.




Lemma fEqLem {A B P} {i j : B} {F : forall b : B, (P b -> A) -> Type}
  {k : P i -> A} 
  {l : P j -> A}
  (e : i = j) :
  (forall x, k x = l (eq_rect _ P x _ e)) ->
  F i k = F j l.
Proof. 
  destruct e=> e; f_equal.
  by apply functional_extensionality.
Qed.



              replace a0 with a1.
              destruct E1.
              f_equal. 
              remember (eq_rect _ _ _ _ _).
              replace (eq_rect _ _ _ _ _ _) with (AdviceExtend F adv).
              f_equal. 
            simpl; 
        remember (H0 (exist _ u2 ltu2)) as H0'; clear HeqH0' H0. 
              
        unfold U in H0.


        destruct (Q_NoQuant q); simpl in *.
        by rewrite map_length.
        qauto.

        f_equal.
        rewrite map_flatten.
        Search (map (map _) _).
        
      replace (NoQuantAdviceF FSize
        (NoQuantAddExi [seq PolyTerm_PolyTermVS i | i <- bs]
           (PolyTerm_PolyTermVS y) (Q_NoQuant q)))
        with (NoQuantAdvice
     (ExtendAt0 (length bs)
        [eta nth 0 [seq length x.1 | x <- exiBounds (Q_NoQuant q)]]) FSize).
      replace [eta nth 0
               [seq length x.1
                  | x <- exiBounds
                           (NoQuantAddExi
                              [seq PolyTerm_PolyTermVS i | i <- bs]
                              (PolyTerm_PolyTermVS y) 
                              (Q_NoQuant q))]]
         with (ExtendAt0 (length bs)
        [eta nth 0 [seq length x.1 | x <- exiBounds (Q_NoQuant q)]]).
      simpl.
      unfold NoQuantAddExi.
      dest
      simpl in *.
      rewrite <- Q_NoQuant_Correct_Lem_0 in H.

      destruct IH.
      apply IH in H.

    simpl.


Lemma ZO_NoQuant_Correct_NoQuantFormulaCondition
  (f : ZerothOrderFormula) :
  ZerothOrder_Denote _ M f <-> 
  exists a, NoQuantFormulaCondition _ M (ZO_NoQuant f) a.



(* Program Definition AdviceUniExtend
  (M : Sigma11Model)
  nu (adv : NoQuantAdvice nu) 
  (f : forall i, (|[(lnth nu i).+1]| -> 'F_FSize) -> 'F_FSize)
  (H : forall i (t : |[lnth nu i]| -> 'F_FSize), 
    f i (ExtendAt0N (V_F M 0) t) = 
    exiVAdv _ adv i t) :
  NoQuantAdvice (map (fun x => x.+1) nu) :=
  {| exiVAdv := f
  ;  exiFAdv := exiFAdv _ adv
  |}.
Next Obligation.
  destruct i;[fcrush|simpl in *].
  by rewrite (lnth_nth 0); rewrite (lnth_nth 0) in H.
Qed.
Next Obligation. by rewrite map_length in H0. Qed.
Next Obligation. 
  rewrite (lnth_nth 1); rewrite (lnth_nth 0) in H0; simpl in *.
  by rewrite nth_map.
Qed. *)

Lemma FO_NoQuant_Correct_Lem_0_0 {nu}
  (p : PolyTermVS)
  (adv : NoQuantAdvice nu) 
  (M : Sigma11Model) (r : 'F_FSize) :
  forall u,
  PolyVSDenotation p (AddModelV M r) adv u = 
  PolyVSDenotation (LiftPolyExi p) M (AdviceExtend r adv) u.
Proof.
  elim: p; try qauto.
  - move=> n u.
    simpl.
    unfold ExtendAt0.
    dep_if_case (n == 0);try qauto.
  - move=> [s lts] u.
    simpl.
    remember (AdviceExtend_obligation_2 _ _ _ _) asD0; clear HeqDD0; simpl inD0.
    by replaceD0 with lts;[|apply eq_irrelevance].
  all: move=> i a p IH u; simpl; do 2 f_equal;
       by apply functional_extensionality.
Qed.

Lemma FO_NoQuant_Correct_Lem_0 {nu}
  (f: ZerothOrderFormulaVS)
  (adv : NoQuantAdvice nu) 
  (M : Sigma11Model) (r : 'F_FSize) :
  forall u,
  NoQuantZODenotation f (AddModelV M r) adv u <->
  NoQuantZODenotation (LiftPropExi f) M (AdviceExtend r adv) u.
Proof.
  elim: f; try qauto.
  move=> p1 p2 u.
  simpl.
  by do 2 rewrite FO_NoQuant_Correct_Lem_0_0.
Qed.

Lemma FO_NoQuant_Empty_InputBounds
  (f : FirstOrderFormula) :
  (exiFInputBounds (FO_NoQuant f)) = [::].
Proof. elim: f; try qauto. Qed.

Lemma FO_NoQuant_Empty_OutputBounds
  (f : FirstOrderFormula) :
  (exiFOutputBounds (FO_NoQuant f)) = [::].
Proof. elim: f; try qauto. Qed.

Lemma FO_NoQuant_Correct_NoQuantSOBoundCondition
  (f : FirstOrderFormula) (M : Sigma11Model) a :
  NoQuantSOBoundCondition (FO_NoQuant f) M a.
Proof.
  move=> u [i lti]; simpl.
  assert (i < 0);[|fcrush].
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
  length (uniBounds (FO_NoQuant (FOExists p f))) 
  = length (uniBounds (FO_NoQuant f)).
Proof. cbn; by move=> f; rewrite map_length. Qed.

(* 
Lemma FO_NoQuant_Correct_NoQuantFormulaCondition_Exi_Lem2  {p f}:
  uniBounds (NoQuantAddExi p f) = uniBounds f. *)

Lemma FO_NoQuant_Correct_NoQuantFormulaCondition_Exi
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model) r a :
  NoQuantFormulaCondition (FO_NoQuant f) (AddModelV M r) a <-> 
  NoQuantFormulaCondition (FO_NoQuant (FOExists p f)) M (AdviceExtend r a).
Proof. 
  split; move=> H u; apply FO_NoQuant_Correct_Lem_0.
  - unfold NoQuantFormulaCondition in H.
    move: u.
    rewrite FO_NoQuant_Correct_NoQuantFormulaCondition_Exi_Lem.
    move=> u.
    destruct u as [u ltu]; simpl in *.
    assert (forall
    (j : {n : nat | n < length (uniBounds (FO_NoQuant f))})
    (v : nat -> 'F_FSize),
      InBound (AddModelV M r) a (u j)
        (nth PolyZeroVS (uniBounds (FO_NoQuant f)) (` j))
        (MakeU u v)) as ltu2.
    move=> j v.
    remember (ltu j v); clear Heqi.
    change PolyZeroVS  with (LiftPolyExi (nu := nu (FO_NoQuant f)) PolyZeroVS) in i.
    rewrite nth_map in i.
    unfold InBound in *.
    by rewrite FO_NoQuant_Correct_Lem_0_0.
    exact (H (exist _ u ltu2)).
  - unfold NoQuantFormulaCondition in H.
    destruct u as [u ltu]; simpl in *.
    rewrite map_length in H.
    assert (forall
      (j : {n : nat | n < length (uniBounds (FO_NoQuant f))})
      (v : nat -> 'F_FSize),
        InBound M (AdviceExtend r a) (u j)
          (nth PolyZeroVS
              (uniBounds
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
      with (LiftPolyExi (nu := nu (FO_NoQuant f)) PolyZeroVS).
    by rewrite nth_map.
Qed.

Program Definition EmptyU {M b q a} : 
  U (NoQuantAddExi b q) M a 0 := emptyTuple.

Lemma exiVAdvEqLem {nu a i j}
  {k : |[lnth nu i]| -> 'F_FSize} 
  {l : |[lnth nu j]| -> 'F_FSize}
  (e : i = j) :
  (forall x, k x = l (eq_rect _ (fun x => |[lnth nu x]|) x _ e)) ->
  exiVAdv nu a i k = exiVAdv nu a j l.
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
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model) a r :
  ((forall n, InBound M (AdviceExtend r a) r (PolyTermVSCast (PolyTerm_PolyTermVS p)) n)
   /\ NoQuantFOBoundCondition (FO_NoQuant f) (AddModelV M r) a) <->
  NoQuantFOBoundCondition (FO_NoQuant (FOExists p f)) M (AdviceExtend r a).
Proof.
  split.
  - move=> [H0 H1] [i lti] u n0.
    destruct i;auto;simpl in *.
    unfold NoQuantFOBoundCondition in H1.
    destruct u as [u ltu]; simpl in *.
    assert (forall (j : {n : nat | n < nth 0 (nu (FO_NoQuant f)) i})
        (v : nat -> 'F_FSize),
      InBound (AddModelV M r) a (u j)
        (nth PolyZeroVS (uniBounds (FO_NoQuant f)) (` j))
        (MakeU u v)) as ltu2.
      move=> j v; remember (ltu j v) as ltu'; clear Heqltu'.
      change PolyZeroVS 
      with (LiftPolyExi (nu := nu (FO_NoQuant f)) PolyZeroVS) in ltu'.
      rewrite nth_map in ltu'.
      unfold InBound in *.
      by rewrite FO_NoQuant_Correct_Lem_0_0.
    remember (H1 (exist _ i lti) (exist _ u ltu2) n0) as H1'; clear HeqH1' H1; simpl in H1'.
    simpl in *.
    unfold InBound in *.
    change PolyZeroVS 
    with (LiftPolyExi (nu := nu (FO_NoQuant f)) PolyZeroVS).
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
     (AdviceExtend_obligation_2 (nu (FO_NoQuant f))
        (exist _ i.+1 lti)
        (fun x=> u (exist _  (` x)
              (NoQuantFOBoundCondition_obligation_1
                 (NoQuantAddExi (PolyTerm_PolyTermVS p) (FO_NoQuant f)) M
                 (AdviceExtend r a)
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
        InBound M (AdviceExtend r a) (u j)
          (nth PolyZeroVS
              (uniBounds
                (NoQuantAddExi (PolyTerm_PolyTermVS p)
                    (FO_NoQuant f))) (` j)) (MakeU u v)) as ltu2.
        move=> j v; remember (ltu j v) as ltu'; clear Heqltu'.
        unfold InBound in *; simpl in *.
        change PolyZeroVS 
        with (LiftPolyExi (nu := nu (FO_NoQuant f)) PolyZeroVS).
        rewrite nth_map.
        by rewrite FO_NoQuant_Correct_Lem_0_0 in ltu'.
      remember (H (exist _ (i.+1) lti) (exist _ u ltu2) n) as H'; clear HeqH' H; simpl in H'.
      remember (InBound _ _ _ _ _ _) as H1B.
      replace (InBound _ _ _ _ _ _) with H1B; auto.
      rewrite HeqH1B; clear HeqH1B H1B H'.
      unfold InBound.
      apply match_lem; auto.
      change (PolyZeroVS (nu := 0 :: nu (FO_NoQuant f))) 
        with (LiftPolyExi (nu := nu (FO_NoQuant f)) (PolyZeroVS));rewrite nth_map.
      by rewrite <- FO_NoQuant_Correct_Lem_0_0.
      f_equal.
      assert ((exist (fun n0 : nat => n0 < length (nu (FO_NoQuant f))) i
              (AdviceExtend_obligation_2 (nu (FO_NoQuant f))
                  (exist _ i.+1 lti)
                  (fun x => u (exist _
                        (` x)
                        (NoQuantFOBoundCondition_obligation_1
                          (NoQuantAddExi (PolyTerm_PolyTermVS p)
                              (FO_NoQuant f)) M
                          (AdviceExtend r a)
                          (exist _ i.+1 lti)
                          (exist _ u ltu2) x))) (erefl _)))
              = (exist (fun n : nat => n < length (nu (FO_NoQuant f))) i lti)) as e;[by apply subset_eq_compat|].
      apply (exiVAdvEqLem e); simpl=> x.
      f_equal.
      apply subset_eq_compat.
      by rewrite projT1_eq_rect.
Qed.

Lemma FO_NoQuant_Correct_NoQuantSOBoundCondition_Exi
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model) a r :
  NoQuantSOBoundCondition (FO_NoQuant f) (AddModelV M r) a <->
  NoQuantSOBoundCondition (FO_NoQuant (FOExists p f)) M (AdviceExtend r a).
Proof.
  split=> H;[|apply FO_NoQuant_Correct_NoQuantSOBoundCondition].
  move=> u [i lti]; simpl.
  assert (i < 0);[|fcrush].
  by rewrite FO_NoQuant_Empty_InputBounds in lti.
Qed.

Program Definition AdviceDropExi {nu}
  (adv : NoQuantAdvice (0 :: nu)) :=
  {| exiVAdv := fun i => exiVAdv _ adv (i.+1) 
   ; exiFAdv := exiFAdv _ adv
  |}.

Theorem AdviceDropExi_Spec {nu}
  (adv : NoQuantAdvice (0 :: nu)) :
  adv = 
  (AdviceExtend (exiVAdv _ adv (exist _ 0 (ltn0Sn _)) emptyTuple)
                   (AdviceDropExi adv)).
Proof.
  replace adv with {| exiVAdv := exiVAdv _ _ adv;
                     exiFAdv := exiFAdv _ _ adv |};[|by destruct adv].
  unfold AdviceDropExi.
  unfold AdviceExtend.
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
     (AdviceExtend_obligation_2 (AdviceDropExi_obligation_1 nu)
        (exist (fun n : nat => n < (length nu).+1) x.+1 ltx) u H)) as e;[by apply subset_eq_compat|].
    apply (exiVAdvEqLem (a := adv) e).
    move=> [x0 ltx0].
    f_equal.
    apply subset_eq_compat.
    by rewrite (projT1_eq_rect (e := e)).
Qed.

Theorem lt_dec_true_true {a b}
  (e : lt_dec a b = true) : lt a b.
Proof.
  unfold lt_dec in e.
  by destruct (lt_total a b) eqn:ltP.
Qed.

Theorem lt_dec_false_false {a b}
  (e : lt_dec a b = false) : ~ (lt a b).
Proof.
  unfold lt_dec in e.
  destruct (lt_total a b) eqn:ltP;[fcrush|].
  destruct (so).
  unfold Irreflexive, Reflexive, complement in StrictOrder_Irreflexive.
  unfold Transitive in StrictOrder_Transitive.
  destruct s;[qauto|].
  move=> l2.
  apply (StrictOrder_Irreflexive b); qauto.
Qed.

Program Definition Uni_Advice  {nu s}
  (H : {r : 'F_FSize | lt r s} ->
       forall i : |[length nu]|, (|[lnth nu i]| -> 'F_FSize) -> 'F_FSize)
  (i : |[length (map (fun x => x.+1) nu)]|)
  (t : |[lnth (map (fun x => x.+1) nu) i]| -> 'F_FSize) : 'F_FSize := (
if lt_dec (t 0) s as b return lt_dec (t 0) s = b -> 'F_FSize
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
  lt a b -> lt_dec a b = true.
Proof.
  move=> ltab.
  unfold lt_dec.
  destruct (lt_total a b); auto.
  remember (so).
  destruct s0.
  destruct s.
  destruct e.
  unfold Irreflexive, Reflexive, complement in StrictOrder_Irreflexive; qauto.
  unfold Irreflexive, Reflexive, complement in StrictOrder_Irreflexive; qauto.
Qed. 

Lemma FO_NoQuant_Correct_Lem_4_0
  nu p
  (M: Sigma11Model)
  (s: 'F_FSize)
  (adv: {r : 'F_FSize | lt r s} -> NoQuantAdvice nu)
  (u: nat -> 'F_FSize)
  (ltu0: lt (u 0) s) :
PolyVSDenotation p (AddModelV M (u 0))
    (adv (exist ((lt)^~ s) (u 0) ltu0)) (fun x : nat => u x.+1) =
PolyVSDenotation (LiftPolyUni p) M
    {|
      exiVAdv := Uni_Advice (fun x => exiVAdv nu (adv x));
      exiFAdv := exiFAdv nu (adv (exist ((lt)^~ s) (u 0) ltu0))
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
  (M: Sigma11Model)
  (s: 'F_FSize)
  (adv: {r : 'F_FSize | lt r s} -> NoQuantAdvice nu)
  (u: |[k.+1]| -> 'F_FSize)
  (v: nat -> 'F_FSize)
  (ltu0: lt (u (exist _ 0 e)) s) :
PolyVSDenotation p (AddModelV M (u (exist _ 0 e)))
    (adv (exist ((lt)^~ s) (u (exist _ 0 e)) ltu0)) (MakeU (fSeqRest u) v) =
PolyVSDenotation (LiftPolyUni p) M
    {|
      exiVAdv := Uni_Advice (fun x => exiVAdv nu (adv x));
      exiFAdv := exiFAdv nu (adv (exist ((lt)^~ s) (u (exist _ 0 e)) ltu0))
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
    replace (adv (exist ((lt)^~ s) (u (exist _ 0 e)) ltu0)) 
       with (adv (exist ((lt)^~ s) (MakeU u v 0) (lt_dec_true_true H0))).
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
  (M: Sigma11Model)
  (s: 'F_FSize)
  (adv: {r : 'F_FSize | lt r s} -> NoQuantAdvice nu)
  (u: nat -> 'F_FSize)
  (ltu0: lt (u 0) s) :
NoQuantZODenotation f (AddModelV M (u 0))
  (adv (exist ((lt)^~ s) (u 0) ltu0)) (fun x : nat => u x.+1) <->
NoQuantZODenotation (LiftPropUni f) M
  {| exiVAdv := Uni_Advice (fun x => exiVAdv nu (adv x));
     exiFAdv := exiFAdv nu (adv (exist ((lt)^~ s) (u 0) ltu0))
  |} u.
Proof.
  elim: f; try qauto.
  move=> p0 p1.
  simpl.
  by do 2 rewrite FO_NoQuant_Correct_Lem_4_0.
Qed.


Lemma FO_NoQuant_Correct_Lem_4_0_2 {k}
  nu p
  (M: Sigma11Model)
  (s: 'F_FSize)
  (adv: {r : 'F_FSize | lt r s} -> NoQuantAdvice nu)
  (u: |[k.+1]| -> 'F_FSize)
  (v: nat -> 'F_FSize)
  (ltu0: lt (u (exist _ 0 (ltn0Sn _))) s) :
NoQuantZODenotation p (AddModelV M (u (exist _ 0 (ltn0Sn _))))
    (adv (exist ((lt)^~ s) (u (exist _ 0 (ltn0Sn _))) ltu0)) (MakeU (fSeqRest u) v) =
NoQuantZODenotation (LiftPropUni p) M
    {|
      exiVAdv := Uni_Advice (fun x => exiVAdv nu (adv x));
      exiFAdv := exiFAdv nu (adv (exist ((lt)^~ s) (u (exist _ 0 (ltn0Sn _))) ltu0))
    |} (MakeU u v).
Proof.
  elim: p; try qauto.
  move=> p0 p1.
  simpl.
  by do 2 rewrite FO_NoQuant_Correct_Lem_4_0_1.
Qed.

Lemma FO_NoQuant_Correct_Lem_5_1 {p M adv1 adv2 u} :
  PolyVSDenotation (LiftPolyUni (PolyTerm_PolyTermVS p)) M adv1 u =
  PolyVSDenotation (LiftPolyUni (PolyTerm_PolyTermVS p)) M adv2 u.
Proof.
  induction p; try qauto.
  simpl.
  do 2 f_equal.
  by apply functional_extensionality.
Qed.

Lemma FO_NoQuant_Correct_Lem_5_0 {z M adv1 adv2 u} :
  NoQuantZODenotation (LiftPropUni (ZerothOrder_ZerothOrderVS z)) M adv1 u =
  NoQuantZODenotation (LiftPropUni (ZerothOrder_ZerothOrderVS z)) M adv2 u.
Proof.
  induction z; try qauto.
  simpl.
  by do 2 rewrite (FO_NoQuant_Correct_Lem_5_1 (adv1 := adv1) (adv2 := adv2)).
Qed.

Lemma FO_NoQuant_Correct_Lem_5_3 {p M exiV exiF1 exiF2 u} :
  PolyVSDenotation (LiftPolyExi (PolyTerm_PolyTermVS p)) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  PolyVSDenotation (LiftPolyExi (PolyTerm_PolyTermVS p)) M
        {| exiVAdv := exiV; exiFAdv := exiF2 |} u.
Proof.
  induction p; try qauto.
  simpl.
  do 2 f_equal.
  by apply functional_extensionality.
Qed.

Lemma FO_NoQuant_Correct_Lem_5_2 {z M exiV exiF1 exiF2 u} :
  NoQuantZODenotation (LiftPropExi (ZerothOrder_ZerothOrderVS z)) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  NoQuantZODenotation (LiftPropExi (ZerothOrder_ZerothOrderVS z)) M
        {| exiVAdv := exiV; exiFAdv := exiF2 |} u.
Proof.
  induction z; try qauto.
  simpl.
  by do 2 rewrite (FO_NoQuant_Correct_Lem_5_3 (exiF1 := exiF1) (exiF2 := exiF2)).
Qed.

Lemma FO_NoQuant_Correct_Lem_6_0 {nu}
  (p : @PolyTermVS _)
  (adv : NoQuantAdvice (0 :: nu))
  (M : Sigma11Model) :
  forall u,
  PolyVSDenotation p (AddModelV M (exiVAdv _ adv (exist _ 0 (ltn0Sn _)) (fun x => u (` x)))) (AdviceDropExi adv) u = 
  PolyVSDenotation (LiftPolyExi p) M adv u.
Proof.
  elim: p; try qauto.
  - move=> n u.
    simpl.
    unfold ExtendAt0.
    dep_if_case (n == 0);try qauto.
    rewrite H; simpl.
    f_equal.
    unfold AdviceDropExi_obligation_1.
    remember (ltn0Sn _) as0; clear HeqD0.
    remember (PolyTermVSLiftExi_obligation_1 nu) as1; clear HeqD1.
    unfold length in1.
    by replace0 with1;[|apply eq_irrelevance].
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
  (adv : NoQuantAdvice (0 :: nu))
  (M : Sigma11Model) :
  forall u,
  NoQuantZODenotation p (AddModelV M (exiVAdv _ adv (exist _ 0 (ltn0Sn _)) (fun x => u (` x)))) (AdviceDropExi adv) u = 
  NoQuantZODenotation (LiftPropExi p) M adv u.
Proof.
  elim: p; try qauto.
  move=> p1 p2 u.
  simpl.
  by do 2 rewrite FO_NoQuant_Correct_Lem_6_0.
Qed.

Program Definition AdviceDropUni {nu} r
  (adv : NoQuantAdvice (map (fun x => x.+1) nu)) :
  NoQuantAdvice nu :=
  {| exiVAdv := fun i t => exiVAdv _ adv i (ExtendAt0N r t)
   ; exiFAdv := exiFAdv _ adv
  |}.
Next Obligation. by rewrite map_length. Qed.
Next Obligation.
  rewrite (lnth_nth 1) nth_map in H.
  by rewrite (lnth_nth 0).
Qed.

Lemma FO_NoQuant_Correct_Lem_7_0 {nu}
  (p : @PolyTermVS _)
  (adv : NoQuantAdvice (map (fun x => x.+1) nu))
  (M : Sigma11Model) :
  forall u,
  PolyVSDenotation p (AddModelV M (u 0)) (AdviceDropUni (u 0) adv) (fun x => u (x.+1)) = 
  PolyVSDenotation (LiftPolyUni p) M adv u.
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
  (adv : NoQuantAdvice (map (fun x => x.+1) nu))
  (M : Sigma11Model) :
  forall u,
  PolyVSDenotation p (AddModelV M r) (AdviceDropUni r adv) u = 
  PolyVSDenotation (LiftPolyUni p) M adv (ExtendAt0 r u).
Proof.
  move=> u.
  remember (ExtendAt0 r u) as u'.
  replace u with (fun x => u' (x.+1));[|qauto].
  replace r with (u' 0);[|qauto].
  by rewrite FO_NoQuant_Correct_Lem_7_0.
Qed.

Lemma FO_NoQuant_Correct_Lem_7 {nu}
  p
  (adv : NoQuantAdvice (map (fun x => x.+1) nu))
  (M : Sigma11Model) :
  forall u,
  NoQuantZODenotation p (AddModelV M (u 0)) (AdviceDropUni (u 0) adv) (fun x => u (x.+1)) = 
  NoQuantZODenotation (LiftPropUni p) M adv u.
Proof.
  elim: p; try qauto.
  move=> p1 p2 u.
  simpl.
  by do 2 rewrite FO_NoQuant_Correct_Lem_7_0.
Qed.

Lemma FO_NoQuant_Correct_Lem_7_A {nu r}
  p
  (adv : NoQuantAdvice (map (fun x => x.+1) nu))
  (M : Sigma11Model) :
  forall u,
  NoQuantZODenotation p (AddModelV M r) (AdviceDropUni r adv) u = 
  NoQuantZODenotation (LiftPropUni p) M adv (ExtendAt0 r u).
Proof.
  move=> u.
  remember (ExtendAt0 r u) as u'.
  replace u with (fun x => u' (x.+1));[|qauto].
  replace r with (u' 0);[|qauto].
  by rewrite FO_NoQuant_Correct_Lem_7.
Qed.

Lemma FO_NoQuant_Correct_Lem_5 {f M exiV exiF1 u} :
  NoQuantZODenotation (formula (FO_NoQuant f)) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  NoQuantZODenotation (formula (FO_NoQuant f)) M
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
  NoQuantZODenotation (LiftPropUni (formula (FO_NoQuant f))) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  NoQuantZODenotation (LiftPropUni (formula (FO_NoQuant f))) M
        {| exiVAdv := exiV; exiFAdv := fun=> (fun a : nat => fun=> None) |} u.
Proof.
  do 2 rewrite <- (FO_NoQuant_Correct_Lem_7 (formula (FO_NoQuant f)) _ M).
  by do 2 rewrite FO_NoQuant_Correct_Lem_5.
Qed.

Lemma FO_NoQuant_Correct_Lem_8 {u f j M exV1 exF1 exF2} :
  PolyVSDenotation (nth PolyZeroVS (uniBounds (FO_NoQuant f)) j) M
    {| exiVAdv := exV1;
       exiFAdv := exF1
    |} u =
  PolyVSDenotation (nth PolyZeroVS (uniBounds (FO_NoQuant f)) j) M
    {| exiVAdv := exV1;
       exiFAdv := exF2
    |} u.
Proof.
  move: j u M; induction f.
  - by destruct j.
  - move=> j u M.
    simpl.
    change PolyZeroVS with (LiftPolyExi (nu := nu (FO_NoQuant f)) (PolyZeroVS)).
    rewrite nth_map.
    do 2 rewrite <- (FO_NoQuant_Correct_Lem_6_0 (nth PolyZeroVS (uniBounds (FO_NoQuant f)) j)).
    apply IHf.
  - move=> j u M.
    simpl.
    destruct j; simpl.
    by do 2 rewrite PolyTermVSCastCastId.
    change PolyZeroVS with (LiftPolyUni (nu := nu (FO_NoQuant f)) PolyZeroVS).
    rewrite nth_map.
    do 2 rewrite <- (FO_NoQuant_Correct_Lem_7_0 (nth PolyZeroVS (uniBounds (FO_NoQuant f)) j)).
    apply IHf.
Qed.

Lemma FO_NoQuant_Correct_Lem_10 {u f j M exV1 exF1 exF2} :
  PolyVSDenotation (nth PolyZeroVS (exiVBounds (FO_NoQuant f)) j) M
    {| exiVAdv := exV1;
       exiFAdv := exF1
    |} u =
  PolyVSDenotation (nth PolyZeroVS (exiVBounds (FO_NoQuant f)) j) M
    {| exiVAdv := exV1;
       exiFAdv := exF2
    |} u.
Proof.
  move: j u M; induction f.
  - by destruct j.
  - move=> j u M.
    simpl.
    destruct j; simpl.
    by do 2 rewrite PolyTermVSCastCastId.
    change PolyZeroVS with (LiftPolyExi (nu := nu (FO_NoQuant f)) (PolyZeroVS)).
    rewrite nth_map.
    do 2 rewrite <- (FO_NoQuant_Correct_Lem_6_0 (nth PolyZeroVS (exiVBounds (FO_NoQuant f)) j)).
    apply IHf.
  - move=> j u M.
    simpl.
    change PolyZeroVS with (LiftPolyUni (nu := nu (FO_NoQuant f)) PolyZeroVS).
    rewrite nth_map.
    do 2 rewrite <- (FO_NoQuant_Correct_Lem_7_0 (nth PolyZeroVS (exiVBounds (FO_NoQuant f)) j)).
    apply IHf.
Qed.

Lemma FO_NoQuant_Correct_Lem_8_5 {f M exiV exiF1 exiF2 j u} :
  PolyVSDenotation (LiftPolyUni (nth PolyZeroVS (uniBounds (FO_NoQuant f)) j)) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  PolyVSDenotation (LiftPolyUni (nth PolyZeroVS (uniBounds (FO_NoQuant f)) j)) M
        {| exiVAdv := exiV; exiFAdv := exiF2 |} u.
Proof.
  do 2 rewrite <- (FO_NoQuant_Correct_Lem_7_0 (nth PolyZeroVS (uniBounds (FO_NoQuant f)) j)).
  apply FO_NoQuant_Correct_Lem_8.
Qed.


Lemma FO_NoQuant_Correct_Lem_10_5 {f M exiV exiF1 exiF2 j u} :
  PolyVSDenotation (LiftPolyUni (nth PolyZeroVS (exiVBounds (FO_NoQuant f)) j)) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  PolyVSDenotation (LiftPolyUni (nth PolyZeroVS (exiVBounds (FO_NoQuant f)) j)) M
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

Theorem FO_NoQuant_Correct (p : FirstOrderFormula) (M : Sigma11Model) :
  FirstOrder_Denote p M <-> NoQuantDenotation (FO_NoQuant p) M.
Proof.
  move: M; elim: p.
  - apply ZO_NoQuant_Correct.
  - move=> p f IH M.
    split.
    + move=> H.
      simpl.
      unfold NoQuantDenotation.
      simpl in H.
      remember (Poly_Denote p M) as PM.
      destruct PM;[|fcrush].
      destruct H as [r [ltrs fd]].
      apply ((IH (AddModelV M r)).1) in fd; clear IH.
      unfold NoQuantDenotation in fd.
      destruct fd as [adv [H0 [H1 H2]]].
      exists (AdviceExtend r adv).
      split;[|split];auto.
      * by apply (FO_NoQuant_Correct_NoQuantFormulaCondition_Exi p).
      * apply (FO_NoQuant_Correct_NoQuantFOBoundCondition_Exi p).
        split; auto.
        move=> n.
        unfold InBound.
        rewrite PolyTermVSCastCastId; rewrite <- PolyTerm_PolyTermVS_Correct.
        by rewrite <- HeqPM.
      * by apply (FO_NoQuant_Correct_NoQuantSOBoundCondition_Exi p).
    + move=> [adv [H0 [H1 H2]]].
      simpl in adv.
      rewrite (AdviceDropExi_Spec adv) in H0, H1, H2.
      apply (FO_NoQuant_Correct_NoQuantFormulaCondition_Exi p) in H0.
      apply (FO_NoQuant_Correct_NoQuantFOBoundCondition_Exi p) in H1.
      apply (FO_NoQuant_Correct_NoQuantSOBoundCondition_Exi p) in H2.
      simpl.
      destruct (Poly_Denote p M) eqn:PM.
      exists (exiVAdv _ adv (exist _ 0 (ltn0Sn _)) emptyTuple).
      split;[|qauto].
        clear H2 H0; destruct H1 as [LT _].
        remember (LT (fun _ => 0%R)) as LT'; clear HeqLT' LT.
        unfold InBound in LT'.
        rewrite PolyTermVSCastCastId in LT'.
        rewrite <- PolyTerm_PolyTermVS_Correct in LT'.
        by rewrite PM in LT'.
      clear H2 H0; destruct H1 as [LT _].
      remember (LT (fun _ => 0%R)) as LT'; clear HeqLT' LT.
      unfold InBound in LT'.
      rewrite PolyTermVSCastCastId in LT'.
      rewrite <- PolyTerm_PolyTermVS_Correct in LT'.
      by rewrite PM in LT'.
  - move=> p f IH M.
    simpl.
    destruct (Poly_Denote p M) eqn:PM; split; try qauto.
    + move=> FO.
      assert (
        forall r : 'F_FSize,
          lt r s ->
          NoQuantDenotation (FO_NoQuant f) (AddModelV M r)) as FO';[qauto|clear IH FO].
      unfold NoQuantDenotation in *.
      assert (
        forall r : {r : 'F_FSize | lt r s},
        exists a : NoQuantAdvice (nu (FO_NoQuant f)),
          NoQuantFormulaCondition (FO_NoQuant f) (AddModelV M (` r)) a /\
          NoQuantFOBoundCondition (FO_NoQuant f) (AddModelV M (` r)) a /\
          NoQuantSOBoundCondition (FO_NoQuant f) (AddModelV M (` r)) a) as FO;[qauto|clear FO'].
      apply choice in FO.
      destruct FO as [adv H].
      exists {| exiVAdv :=  Uni_Advice (fun x => exiVAdv _ _ (adv x))
              ; exiFAdv := fun _ _ _ => None |}.
      split;[|split].
      * unfold NoQuantFormulaCondition.
        simpl; rewrite map_length; move=> [u ltu]; simpl.
        assert (lt (u (exist _ 0 (ltn0Sn _))) s) as ltuE.
          remember (ltu (exist _ 0 (ltn0Sn _)) (fun=> 0%R)) as ltu'; clear Heqltu' ltu.
          simpl in ltu'.
          unfold InBound in ltu'.
          rewrite PolyTermVSCastCastId in ltu'.
          rewrite <- PolyTerm_PolyTermVS_Correct in ltu'.
          by rewrite PM in ltu'; simpl in ltu'.
        remember (H (exist _ (u (exist _ 0 (ltn0Sn _))) ltuE)) as H'; clear HeqH' H.
        destruct H' as [H _].
        unfold NoQuantFormulaCondition in H; simpl in H.
        assert (forall j v,
              InBound M
                {|
                  exiVAdv := Uni_Advice (fun x => exiVAdv (nu (FO_NoQuant f)) (adv x));
                  exiFAdv := exiFAdv _ (adv (exist ((lt)^~ s) (u (exist _ 0 (ltn0Sn _))) ltuE))
                |} (u j)
                (nth PolyZeroVS
                  (uniBounds (NoQuantAddUni (PolyTerm_PolyTermVS p) (FO_NoQuant f)))
                  (` j)) (MakeU u v)) as ltuX.
              clear H ; move=> [j ltj] v; simpl in *.
              remember (ltu (exist _ j ltj) v) as ltu'; clear Heqltu'.
              unfold InBound in *; simpl in *.
              destruct j; simpl in *.
              by rewrite PolyTermVSCastCastId; rewrite PolyTermVSCastCastId in ltu'.
              change (PolyZeroVS (nu := [seq x.+1 | x <- nu (FO_NoQuant f)]))
              with (LiftPolyUni (nu := nu (FO_NoQuant f)) PolyZeroVS) in ltu'.
              change (PolyZeroVS (nu := [seq x.+1 | x <- nu (FO_NoQuant f)]))
              with (LiftPolyUni (nu := nu (FO_NoQuant f)) PolyZeroVS).
              rewrite nth_map; rewrite nth_map in ltu'.
              remember (PolyVSDenotation _ _ _ _ _) as PD0.
              replace (PolyVSDenotation _ _ _ _ _) with PD0.
              destruct PD0; auto; simpl in *.
              rewrite HeqPD0; clear HeqPD0 PD0 ltu'.
              do 2 rewrite <- (FO_NoQuant_Correct_Lem_7_0 (nth PolyZeroVS (uniBounds (FO_NoQuant f)) j)).
              apply FO_NoQuant_Correct_Lem_8.
        assert (forall j v, InBound (AddModelV M (u (exist _ 0 (ltn0Sn _))))
               (adv (exist ((lt)^~ s) (u (exist _ 0 (ltn0Sn _))) ltuE)) (fSeqRest u j)
               (nth PolyZeroVS (uniBounds (FO_NoQuant f)) (` j)) (MakeU (fSeqRest u) v)) as ltu0.
              clear H ; move=> [j ltj] v; simpl in *.
              assert (j.+1 < (length (uniBounds (FO_NoQuant f))).+1) as ltj2;[clear ltu ltuX ltuE PM adv v u s M p; sfirstorder|].
              remember (ltuX (exist _ (j.+1) ltj2) v) as ltu'; clear Heqltu'.
              unfold InBound in *; simpl in *.
              change (PolyZeroVS (nu := [seq x.+1 | x <- nu (FO_NoQuant f)]))
              with (LiftPolyUni (nu := nu (FO_NoQuant f)) PolyZeroVS) in ltu'.
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
        rewrite <- (FO_NoQuant_Correct_Lem_5_5 (exiF1 := exiFAdv (nu (FO_NoQuant f))
          (adv (exist ((lt)^~ s) (u (exist _ 0 (ltn0Sn _))) ltuE)))).
        by rewrite <- FO_NoQuant_Correct_Lem_4_0_2.
      * unfold NoQuantFOBoundCondition=> i [u ltu] n; simpl in *.
        destruct i as [i lti].
        assert (i < length (nu (FO_NoQuant f))) as lti2;[clear u ltu; by rewrite map_length in lti|].
        assert (nth 0 [seq x.+1 | x <- nu (FO_NoQuant f)] i 
                = (nth 0 (nu (FO_NoQuant f)) i).+1).
          transitivity (lnth [seq x.+1 | x <- nu (FO_NoQuant f)] (exist _ i lti));[by rewrite (lnth_nth 0)|].
          by rewrite lnth_map (lnth_nth 0); f_equal.
        remember (NoQuantFOBoundCondition_obligation_1 _ _ _ _ _ _) asDD; clear HeqDDD.
        change PolyZeroVS with (LiftPolyUni (nu := nu (FO_NoQuant f)) PolyZeroVS); rewrite nth_map.
        assert (0 < nth 0 [seq x.+1 | x <- nu (FO_NoQuant f)] i) as lt0;[by rewrite H0|].
        assert (lt (u (exist _ 0 lt0)) s) as ltuE.
          remember (ltu (exist _ 0 lt0) (fun=> 0%R)) as ltu'; clear Heqltu' ltu.
          simpl in ltu'.
          unfold InBound in ltu'.
          rewrite PolyTermVSCastCastId in ltu'.
          rewrite <- PolyTerm_PolyTermVS_Correct in ltu'.
          by rewrite PM in ltu'.
        remember (H (exist _ (u (exist _ 0 lt0)) ltuE)) as H'; clear HeqH' H.
        destruct H' as [_ [H _]]; simpl in H.
        unfold NoQuantFOBoundCondition in H.
        remember (FO_NoQuant_Correct_Lem_9 lti2 u) as u'.
        assert (lt (u' (exist _ 0 (ltn0Sn (nth 0 (nu (FO_NoQuant f)) i)))) s) as ltuE2.
          rewrite Hequ'; unfold FO_NoQuant_Correct_Lem_9; simpl.
          remember (lt _ _ _) as L1; replace (lt _ _ _) with L1;auto;rewrite HeqL1.
          do 2 f_equal; by apply subset_eq_compat.
        assert (forall j v, InBound (AddModelV M (u (exist _ 0 lt0)))
                 (adv (exist ((lt)^~ s) (u (exist _ 0 lt0)) ltuE)) (fSeqRest u' j)
                 (nth PolyZeroVS (uniBounds (FO_NoQuant f)) (` j))
                 (MakeU (fSeqRest u') v)) as ltu2.
                move=> [j ltj] v.
                simpl.
                clear HDD.
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
                with (LiftPolyUni (nu := nu (FO_NoQuant f)) PolyZeroVS). 
                rewrite nth_map.
                remember (adv _) as adv'.
                assert (adv' = adv (exist ((lt)^~ s) (u' (exist _ 0 (ltn0Sn _))) ltuE2)).
                  rewrite Heqadv'; f_equal; apply subset_eq_compat.
                  rewrite Hequ'; unfold FO_NoQuant_Correct_Lem_9; f_equal; by apply subset_eq_compat.
                transitivity (PolyVSDenotation
                  (LiftPolyUni (nth PolyZeroVS (uniBounds (FO_NoQuant f)) j)) M
                  {| exiVAdv := Uni_Advice (fun x => exiVAdv (nu (FO_NoQuant f)) (adv x));
                    exiFAdv := exiFAdv _ _ (adv (exist ((lt)^~ s) (u' (exist _ 0 (ltn0Sn _))) ltuE2))
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
        replace (adv (exist ((lt)^~ s) (u (exist _ 0 (DDD (exist _ 0 _)))) (lt_dec_true_true Hyp0)))
        with ((adv (exist ((lt)^~ s) (u (exist _ 0 lt0)) ltuE))).
        assert (exist (fun n0 : nat => n0 < length (nu (FO_NoQuant f))) i lti2 =
                exist _ i (Uni_Advice_obligation_2 (nu (FO_NoQuant f)) s (exist _ i lti) (fun x => u (exist _ (` x) (DDD x))) Hyp0))as e;[
        by apply subset_eq_compat|].
        apply (exiVAdvEqLem e)=> x.
        remember (NoQuantFOBoundCondition_obligation_1 _ _ _ _ _ _ _) asDD0; clear HeqDDD0.
        unfold fSeqRest; rewrite Hequ'; unfold FO_NoQuant_Correct_Lem_9.
        f_equal; apply subset_eq_compat; simpl.
        by rewrite projT1_eq_rect.
        f_equal; apply subset_eq_compat; f_equal; by apply subset_eq_compat.
        rewrite HeqP0; clear H' HeqP0 P0.
        transitivity (PolyVSDenotation
          (LiftPolyUni (nth PolyZeroVS (exiVBounds (FO_NoQuant f)) i)) M
          {| exiVAdv := Uni_Advice (fun x => exiVAdv (nu (FO_NoQuant f)) (adv x));
             exiFAdv := exiFAdv _ _ (adv (exist ((lt)^~ s) (u' (exist _ 0 (ltn0Sn _))) ltuE2))
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
      * unfold NoQuantFOBoundCondition; simpl=> u [i lti]; simpl.
        assert (i < 0);[|fcrush].
        assert (length (exiFInputBounds (FO_NoQuant f)) = 0) as LE0.
        clear adv H i lti.
        elim: f; try qauto.
        move=> p0 f IH; simpl; by rewrite map_length.
        move=> p0 f IH; simpl; by rewrite map_length.
        simpl in lti.
        rewrite map_length in lti.
        by rewrite LE0 in lti.
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
      assert (forall j v, InBound M adv (u' j) (nth PolyZeroVS
                (PolyTermVSCast (PolyTerm_PolyTermVS p)
                  :: [seq LiftPolyUni i | i <- uniBounds (FO_NoQuant f)]) 
                (` j)) (MakeU u' v)) as ltu'.
              move=> [j ltj] v.
              rewrite Hequ'; destruct j; unfold ExtendAt0N, MakeU; simpl; auto.
              unfold InBound.
              rewrite PolyTermVSCastCastId; rewrite <- PolyTerm_PolyTermVS_Correct.
              by rewrite PM.
              unfold InBound.
              change PolyZeroVS with (LiftPolyUni (nu := nu (FO_NoQuant f)) PolyZeroVS).
              rewrite nth_map.
              remember (ltu (exist _ j ltj) v) as ltu2; clear Heqltu2 ltu.
              simpl in ltu2.
              unfold InBound in ltu2.
              remember (PolyVSDenotation _ _ _ _ _) as PD0.
              replace (PolyVSDenotation _ _ _ _ _) with PD0.
              destruct PD0;auto.
              remember (Utils.ExtendAt0N_obligation_2  _ _ _) asD0; simpl inD0.
              by replaceD0 with ltj;[|apply eq_irrelevance].
              rewrite HeqPD0; clear HeqPD0 PD0 ltu2.
              rewrite FO_NoQuant_Correct_Lem_7_0_A.
              f_equal.
              unfold ExtendAt0; apply functional_extensionality=> x.
              destruct x; simpl; auto.
              unfold MakeU.
              dep_if_case (x < length (uniBounds (FO_NoQuant f))); auto.
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
      dep_if_case (x < length (uniBounds (FO_NoQuant f))); auto.
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
      assert (forall (j : |[nth 0 [seq x.+1 | x <- nu (FO_NoQuant f)] i]|) v, InBound M adv (u' j) (nth PolyZeroVS
              (PolyTermVSCast (PolyTerm_PolyTermVS p) :: [seq LiftPolyUni i
                          | i <- uniBounds (FO_NoQuant f)]) 
                   (` j)) (MakeU u' v)) as ltu'.
              move=> [j ltj] v.
              rewrite Hequ'; destruct j; unfold ExtendAt0N, MakeU; simpl; auto.
              unfold InBound.
              rewrite PolyTermVSCastCastId; rewrite <- PolyTerm_PolyTermVS_Correct.
              by rewrite PM.
              unfold InBound.
              change PolyZeroVS with (LiftPolyUni (nu := nu (FO_NoQuant f)) PolyZeroVS).
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
      change PolyZeroVS with (LiftPolyUni (nu := nu (FO_NoQuant f)) PolyZeroVS) in H.
      rewrite nth_map in H.
      replace (MakeU u' n) with (ExtendAt0 r (MakeU u n)) in H.
      destruct (PolyVSDenotation _ _ _ _ _); auto.
      remember (exiVAdv _ _ _ _ _) as E.
      replace (exiVAdv _ _ _ _ _) with E; auto.
      rewrite HeqE; clear H HeqE E.
      assert (exist (fun n0 : nat => n0 < length [seq x.+1 | x <- nu (FO_NoQuant f)]) i lti2 
            = (exist _ i (AdviceDropUni_obligation_1 (nu (FO_NoQuant f)) (exist _ i lti)
              (fun x => u (exist _  (` x) (NoQuantFOBoundCondition_obligation_1 
              (FO_NoQuant f) (AddModelV M r) (AdviceDropUni r adv)
              (exist _ i lti) (exist _ u ltu) x))))) ) as e;[by apply subset_eq_compat|].
      apply (exiVAdvEqLem e)=> x; destruct x; simpl.
      remember (exist _ x _) asDD.
      rewrite Hequ' HeqDDD; clear HeqDDDDD.
      unfold FO_NoQuant_Correct_Lem_9_0; simpl.
      remember (FO_NoQuant_Correct_Lem_9_0_obligation_1 _ _ _ _) asDD; clear HeqDDD; simpl inDD.
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
        rewrite PolyTermVSCastCastId in ltu'; rewrite <- PolyTerm_PolyTermVS_Correct in ltu'.
        by rewrite PM in ltu'.
      * move=> [i lti] [u ltu]; simpl; simpl in ltu.
        assert (0 < nth 0 [seq x.+1 | x <- nu (FO_NoQuant f)] i) as lt0.
        replace (nth 0 [seq x.+1 | x <- nu (FO_NoQuant f)] i)
            with (lnth [seq x.+1 | x <- nu (FO_NoQuant f)] (exist _ i lti)).
          by rewrite lnth_map (lnth_nth 0).
          by rewrite (lnth_nth 0).
        remember (ltu (exist _ 0 lt0) (fun _ => 0%R)) as ltu'; clear Heqltu' ltu.
        unfold InBound in ltu'; simpl in ltu'.
        rewrite PolyTermVSCastCastId in ltu'; rewrite <- PolyTerm_PolyTermVS_Correct in ltu'.
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

Program Fixpoint LiftPolyExi {nu}
  (p : PolyTermVS) :  PolyTermVS :=
  match p with
  | PolyFVarVS m => PolyFVarVS m
  | PolyEVarVS m => PolyEVarVS m
  | PolyUVarVS m => PolyUVarVS m
  | PolyFFunVS i a t => 
    if i == 0
    then PolyEFunVS 0 a (fun x => LiftPolyExi (t x))
    else PolyFFunVS (i.-1) a (fun x => LiftPolyExi (t x))
  | PolyEFunVS i a t => PolyEFunVS i.+1 a (fun x => LiftPolyExi (t x))
  | PolyMinusOneVS => PolyMinusOneVS
  | PolyPlusOneVS => PolyPlusOneVS
  | PolyZeroVS => PolyZeroVS
  | PolyPlusVS r1 r2 => PolyPlusVS (LiftPolyExi r1) (LiftPolyExi r2)
  | PolyTimesVS r1 r2 => PolyTimesVS (LiftPolyExi r1) (LiftPolyExi r2)
  | PolyIndVS r1 r2 => PolyIndVS (LiftPolyExi r1) (LiftPolyExi r2)
  end.

Fixpoint LiftPropExi {nu}
  (p : ZerothOrderFormulaVS) :  ZerothOrderFormulaVS :=
  match p with
  | ZONotVS f => ZONotVS (LiftPropExi f)
  | ZOAndVS f1 f2 => ZOAndVS (LiftPropExi f1) (LiftPropExi f2)
  | ZOOrVS f1 f2 => ZOOrVS (LiftPropExi f1) (LiftPropExi f2)
  | ZOImpVS f1 f2 => ZOImpVS (LiftPropExi f1) (LiftPropExi f2)
  | ZOEqVS r1 r2 => ZOEqVS (LiftPolyExi r1) (LiftPolyExi r2)
  end.

Definition AddExiFBound 
  (y : @PolyTermVS [::])
  (bs : seq (@PolyTermVS [::]))
  (n : NoQuant) : 
  NoQuant :=
  {| nu := nu n
   ; uniBounds := map LiftPolyExi (uniBounds n)
   ; exiVBounds := map LiftPolyExi (exiVBounds n)
   ; exiFOutputBounds := PolyTermVSCast y :: map LiftPolyExi (exiFOutputBounds n)
   ; exiFInputBounds := map PolyTermVSCast bs :: map (map LiftPolyExi) (exiFInputBounds n)
   ; formula := LiftPropExi (formula n)
  |}.

Fixpoint SO_NoQuant (f : SecondOrderFormula) : NoQuant :=
  match f with
  | FO f => FO_NoQuant f
  | SOExists y bs f => 
    AddExiFBound (PolyTerm_PolyTermVS y)
                 (map PolyTerm_PolyTermVS bs)
                 (SO_NoQuant f)
  end.

Program Definition AdviceExiFExtend {b}
  (f : (|[b]| -> 'F_FSize) -> option ('F_FSize))
  {nu} (adv : NoQuantAdvice nu) : 
  NoQuantAdvice nu :=
  {| exiVAdv := exiVAdv _ _ adv
   ; exiFAdv := fun i a => 
      if i == 0
      then (if a == b as B return (a == b = B -> (|[a]| -> 'F_FSize) -> option ('F_FSize))
            then fun _ => f
            else fun _ _ => None) (erefl _)
      else exiFAdv _ _ adv (i.-1) a
  |}.
Next Obligation. apply EEConvert in e; by destruct e. Qed.

Program Definition SO_NoQuant_Correct_Lem_1 {A B} {f : A -> B} {s : seq A}
  (u : |[length [seq f i | i <- s]]| -> 'F_FSize) : |[length s]| -> 'F_FSize := u.
Next Obligation. by rewrite map_length. Qed.

Lemma SO_NoQuant_Correct_Lem_2 {M nu u p a f adv} :
  PolyVSDenotation (nu := nu) _ (LiftPolyExi p) M (AdviceExiFExtend f adv) u
  = PolyVSDenotation _ p (AddModelExiF _ a f M) adv u.
Proof.
  move: M.
  elim: p; try qauto.
  - move=> i a' p IH M.
    simpl.
    destruct i; simpl.
    f_equal.
    apply functional_extensionality=> x.
    unfold AddExiF, ExtendAt0; simpl.
    dep_if_case (a' == a); auto.
    rewrite dep_if_case_true.
    f_equal; apply functional_extensionality=>y; f_equal; by apply subset_eq_compat.
    rewrite dep_if_case_false; auto.
    f_equal; apply functional_extensionality=> x; auto.
    do 2 f_equal; apply functional_extensionality=> x; auto.
  - move=> i a' p IH M.
    simpl.
    do 2 f_equal; apply functional_extensionality=> x; auto.
Qed.

Lemma SO_NoQuant_Correct_Lem_2_0 {M nu u p a f adv} :
  NoQuantZODenotation (nu := nu) _ (LiftPropExi p) M (AdviceExiFExtend f adv) u
  = NoQuantZODenotation _ p (AddModelExiF _ a f M) adv u.
Proof.
  elim: p; try qauto.
  move=> p0 p1.
  simpl.
  by do 2 rewrite SO_NoQuant_Correct_Lem_2.
Qed.

(* 
Lemma SO_NoQuant_Correct_NoQuantSOBoundCondition_Exi
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model) a f :
  ((forall n, InBound M (AdviceExiFExtend f a) r (PolyTermVSCast (PolyTerm_PolyTermVS y)) n) /\
   (forall n, InBound M (AdviceExiFExtend f a) r (PolyTermVSCast (PolyTerm_PolyTermVS p)) n)
   /\ NoQuantSOBoundCondition (SO_NoQuant f) (AddModelV M r) a) <->
  NoQuantSOBoundCondition (SO_NoQuant (SOExists y bs f)) M (AdviceExiFExtend f a).
Proof.
  split.
  - move=> [H0 H1] [i lti] u n0.
Qed. *)

(* Theorem SO_NoQuant_Correct_Lem_3 {y M a s} {f : (|[a]| -> 'F_FSize) -> option ('F_FSize)} :
  Poly_Denote y M = Some s ->
  exists s', Poly_Denote y (AddModelExiF a f M) = Some s'.
Proof.
  move: M.
  elim: y; try qauto.
  move=> i a2 p IH M e.
  destruct i; simpl.
  move=> e. *)

(* PolyVSDenotation (LiftPolyExi (PolyTermVSCast (PolyTerm_PolyTermVS y)))
    M (AdviceExiFExtend f adv) u



Theorem PolyTermVSCastCastId {nu}
  (p : PolyTerm) (M : Sigma11Model) a t :
  PolyVSDenotation (PolyTermVSCast (nu := nu) (PolyTerm_PolyTermVS p)) M a t =
  PolyVSDenotation0 (PolyTerm_PolyTermVS p) M. *)

Lemma SomeLem {A O a} {f : option A} {g h e} (t : Some a = f) :
  ((match f as b return b = f -> O with
   | Some k => g k
   | None => h
   end) e) = g a t.
Proof. destruct t. f_equal; apply proof_irrelevance. Qed.

Lemma SO_NoQuant_Correct_Lem_4 {A a b x ltx ltx2}
  (HH : a = b)
  (s1 : |[a]| -> A) :
  s1 (exist (fun n : nat => n < a) x ltx2) =
  eq_rect _ (fun x0 : nat => |[x0]| -> A) s1 _ HH
    (exist (fun n : nat => n < b) x ltx).
Proof. 
  destruct HH; simpl.
  f_equal; by apply subset_eq_compat.
Qed.

Lemma exiFAdvEqLem {nu a i a1 a2}
  {k : |[a1]| -> 'F_FSize} 
  {l : |[a2]| -> 'F_FSize}
  (e : a1 = a2) :
  (forall x, k x = l (eq_rect _ (fun x => |[x]|) x _ e)) ->
  exiFAdv nu a i a1 k = exiFAdv nu a i a2 l.
Proof. 
  destruct e=> e; f_equal.
  by apply functional_extensionality.
Qed.

Lemma lnthEqLem {A a1 a2}
  {k : |[length a1]|}
  {l : |[length a2]|}
  (e : a2 = a1) :
  (k = eq_rect _ (fun x => |[length x]|) l _ e) ->
  lnth ('F_FSize := A) a1 k = lnth a2 l.
Proof. 
  destruct e=> e; f_equal.
  destruct k, l.
  apply subset_eq_compat.
  apply subset_eq in e.
  by rewrite projT1_eq_rect in e.
Qed.

Definition AdviceExiFExtendA
  (f : forall b, (|[b]| -> 'F_FSize) -> option ('F_FSize))
  {nu} (adv : NoQuantAdvice nu) : 
  NoQuantAdvice nu :=
  {| exiVAdv := exiVAdv _ _ adv
   ; exiFAdv := fun i a => 
      if i == 0
      then f a
      else exiFAdv _ _ adv (i.-1) a
  |}.

Program Definition AdviceDropExiF {nu}
  (adv : NoQuantAdvice nu) :=
  {| exiVAdv := exiVAdv _ adv
   ; exiFAdv := fun i => exiFAdv _ adv (i.+1) 
  |}.

Theorem AdviceDropExiF_Spec_1 {nu}
  (adv : NoQuantAdvice nu) :
  adv = 
  (AdviceExiFExtendA (exiFAdv _ adv 0)
                     (AdviceDropExiF adv)).
Proof.
  destruct adv; f_equal; simpl.
  unfold AdviceDropExiF, AdviceExiFExtendA; simpl; f_equal.
  apply functional_extensionality;move=> [|i]; auto.
Qed.

Theorem AdviceDropExiF_Spec_2 {nu a f} 
  (adv : NoQuantAdvice nu) :
  adv = 
  (AdviceDropExiF (AdviceExiFExtend (b := a) f adv)).
Proof.
  destruct adv; f_equal; simpl.
  unfold AdviceDropExiF, AdviceExiFExtendA; simpl; f_equal.
Qed.

Lemma SO_NoQuant_Correct_Lem_2_A {M nu u p f adv} :
  PolyVSDenotation (nu := nu) _ (LiftPolyExi p) M (AdviceExiFExtendA f adv) u
  = PolyVSDenotation _ p (AddModelExiFA _ f M) adv u.
Proof.
  move: M.
  elim: p; try qauto.
  - move=> i a' p IH M.
    simpl.
    destruct i; simpl;
    do 2 f_equal; apply functional_extensionality; qauto.
  - move=> i a' p IH M.
    simpl.
    do 2 f_equal; apply functional_extensionality=> x; auto.
Qed.

Lemma SO_NoQuant_Correct_Lem_2_B {M nu u p adv} :
  PolyVSDenotation (nu := nu) _ (LiftPolyExi p) M adv u
  = PolyVSDenotation _ p (AddModelExiFA _ (exiFAdv _ adv 0) M) (AdviceDropExiF adv) u.
Proof.
  move: M.
  elim: p; try qauto.
  - move=> i a' p IH M.
    simpl.
    destruct i; simpl;
    do 2 f_equal; apply functional_extensionality; qauto.
  - move=> i a' p IH M.
    simpl.
    do 2 f_equal; apply functional_extensionality=> x; auto.
Qed.

Lemma SO_NoQuant_Correct_Lem_2_C {M nu u p adv d} :
  PolyVSDenotation (nu := nu) _ (LiftPolyExi p) M (AdviceExiFExtend (exiFAdv _ adv 0 d) (AdviceDropExiF adv)) u
  = PolyVSDenotation _ p (AddModelExiF _ d (exiFAdv _ adv 0 d) M) (AdviceDropExiF adv) u.
Proof.
  move: M.
  elim: p; try qauto.
  - move=> i a' p IH M.
    simpl.
    destruct i; simpl;
    do 2 f_equal; apply functional_extensionality; try qauto.
    unfold ExtendAt0; simpl.
    dep_if_case (a' == d); auto.
    assert (a' = d);[by apply EEConvert in H|].
    move=> x; rewrite dep_if_case_true; auto.
    f_equal; apply functional_extensionality=> X; f_equal; by apply subset_eq_compat.
    rewrite dep_if_case_false; auto.
  - move=> i a' p IH M.
    simpl.
    destruct i; simpl;
    do 2 f_equal; apply functional_extensionality; try qauto.
Qed.


(* Lemma SO_NoQuant_Correct_Lem_2_C {M nu u p adv d} :
  PolyVSDenotation (nu := nu) _ (LiftPolyExi p) M adv u
  = PolyVSDenotation _ p (AddModelExiF _ d (exiFAdv _ adv 0 d) M) (AdviceDropExiF adv) u.
Proof.
  move: M.
  elim: p; try qauto.
  - move=> i a' p IH M.
    simpl.
    destruct i; simpl;
    do 2 f_equal; apply functional_extensionality.
    move=> x.
    unfold ExtendAt0; simpl.
    dep_if_case (a' == d); auto.

 ; qauto.
  - move=> i a' p IH M.
    simpl.
    do 2 f_equal; apply functional_extensionality=> x; auto.
Qed. *)

(* 
Lemma SO_NoQuant_Correct_Lem_2_B {M nu u p adv} :
  PolyVSDenotation (nu := nu) _ (LiftPolyExi p) M adv u
  = PolyVSDenotation _ p (AddModelExiF _ (exiFAdv _ adv 0) M) (AdviceDropExiF adv) u.
Proof.
  move: M.
  elim: p; try qauto.
  - move=> i a' p IH M.
    simpl.
    destruct i; simpl;
    do 2 f_equal; apply functional_extensionality; qauto.
  - move=> i a' p IH M.
    simpl.
    do 2 f_equal; apply functional_extensionality=> x; auto.
Qed. *)

Theorem SO_NoQuant_Correct (p : SecondOrderFormula) (M : Sigma11Model) :
  SecondOrder_Denote p M <-> NoQuantDenotation (SO_NoQuant p) M.
Proof.
  move: M; elim: p;[apply FO_NoQuant_Correct|].
  move=> y bs s IH M.
  split.
  + move=> f.
    simpl in f.
    (*Note: This proof can be made shorter by replacing 
      Poly_Denote y M with its equal from H2 before destructing.*)
    destruct (Poly_Denote y M) eqn: PMy;[|fcrush].
    destruct (option_fun (fun m => Poly_Denote (lnth bs m) M)) eqn:PMbs;[|fcrush].
    - destruct f as [f [bnd H]].
      apply IH in H.
      unfold NoQuantDenotation.
      simpl.
      destruct H as [adv [H0 [H1 H2]]].
      exists (AdviceExiFExtend f adv).
      split;[|split].
      * clear H1 H2.
        unfold NoQuantFormulaCondition in *.
        move=> [u ltu]; simpl.
        unfold AddExiFBound in u; simpl in u.
        unfold AddExiFBound in ltu; simpl in ltu.
        remember (SO_NoQuant_Correct_Lem_1 u) as u'.
        assert (forall j v, InBound (AddModelExiF (length bs) f M) adv 
                  (u' j) (nth PolyZeroVS (uniBounds (SO_NoQuant s)) (` j))
                  (MakeU u' v)) as ltu'.
                move=> [j ltj] v.
                assert (j < length [seq LiftPolyExi i | i <- uniBounds (SO_NoQuant s)]) as ltj2;[by rewrite map_length|].
                remember (ltu (exist _ j ltj2) v) as ltu'; clear Heqltu' ltu; simpl in ltu'.
                unfold InBound in *; simpl in *.
                replace (MakeU u' v) with (MakeU u v).
                change PolyZeroVS  with (LiftPolyExi (nu := nu (SO_NoQuant s)) PolyZeroVS) in ltu'.
                rewrite nth_map in ltu'.
                rewrite <- SO_NoQuant_Correct_Lem_2.
                destruct (PolyVSDenotation _ _ _ _ _); auto.
                replace (u' _) with (u (exist _ j ltj2)); auto.
                rewrite Hequ'; unfold SO_NoQuant_Correct_Lem_1; f_equal; by apply subset_eq_compat.
                unfold MakeU.
                apply functional_extensionality=> x.
                dep_if_case (x < length (uniBounds (SO_NoQuant s))); auto.
                by rewrite map_length.
                move=> HHH; rewrite dep_if_case_true.
                rewrite Hequ'; unfold SO_NoQuant_Correct_Lem_1; f_equal; by apply subset_eq_compat.
                by rewrite map_length.
                rewrite dep_if_case_false; auto.
                by rewrite map_length.
        remember (H0 (exist _ u' ltu')) as H; clear H0 HeqH; simpl in H.
        rewrite SO_NoQuant_Correct_Lem_2_0.
        replace (MakeU u (fun=> 0%R)) with (MakeU u' (fun=> 0%R)); auto.
        rewrite Hequ'.
        unfold MakeU; apply functional_extensionality=> x.
        dep_if_case (x < length (uniBounds (SO_NoQuant s))); auto.
        rewrite dep_if_case_true;[by rewrite map_length|].
        move=> HHH; unfold SO_NoQuant_Correct_Lem_1; f_equal; by apply subset_eq_compat.
        rewrite dep_if_case_false; auto.
        by rewrite map_length.
      * clear H0 H2.
        unfold NoQuantFOBoundCondition in *.
        move=> [i lti] [u ltu] n; simpl in *.
        assert (forall j v, InBound (AddModelExiF (length bs) f M) adv 
                (u j) (nth PolyZeroVS (uniBounds (SO_NoQuant s)) (` j))
                (MakeU u v)) as ltu2.
            move=> j v; remember (ltu j v) as ltu'; clear Heqltu'.
            change PolyZeroVS  with (LiftPolyExi (nu := nu (SO_NoQuant s)) PolyZeroVS) in ltu'.
            rewrite nth_map in ltu'.
            unfold InBound in *.
            by rewrite <- SO_NoQuant_Correct_Lem_2.
        remember (H1 (exist _ i lti) (exist _ u ltu2) n) as H; clear HeqH H1; simpl in H.
        unfold InBound in *.
        change PolyZeroVS with (LiftPolyExi (nu := nu (SO_NoQuant s)) PolyZeroVS).
        rewrite nth_map.
        rewrite SO_NoQuant_Correct_Lem_2.
        destruct (PolyVSDenotation _ _ _ _); auto.
        remember (NoQuantFOBoundCondition_obligation_1 _ _ _ _ _ _) asD0; clear HeqDD0.
        remember (NoQuantFOBoundCondition_obligation_1 _ _ _ _ _ _) asD1; clear HeqDD1.
        simpl in *.
        replaceD1 withD0; auto.
        apply functional_extensionality_dep=>x; apply eq_irrelevance.
      * clear H0 H1.
        unfold NoQuantSOBoundCondition in *.
        move=> u [[|i] lti]; simpl in *;[clear H2|].
        rewrite PolyTermVSCastCastId; rewrite <- PolyTerm_PolyTermVS_Correct.
        rewrite PMy; simpl.
        assert (length bs = length [seq (PolyTermVSCast (nu := nu (SO_NoQuant s))) i | i <- [seq PolyTerm_PolyTermVS i | i <- bs]]) as HH;[by do 2 rewrite map_length|].
        replace (option_fun (fun j => PolyVSDenotation _ M (AdviceExiFExtend f adv) u))
           with (Some (eq_rect _ (fun x => |[x]| -> 'F_FSize) s1 _ HH)).
        move=> t out.
        rewrite dep_if_case_true;[by do 2 rewrite map_length; apply EEConvert|].
        move=> Hy BoundCon.
        unfold SO_Bound_Check in bnd.
        remember (fun x0 => t (exist _ (` x0) _)) as ins.
        remember (bnd ins out BoundCon) as bnd'; clear Heqbnd' bnd.
        destruct bnd' as [ibnd obnd].
        split; auto.
        move=> [x ltx].
        assert (x < length bs) as ltx2;[by rewrite HH|].
        remember (ibnd (exist _ x ltx2)) as ibnd'; clear Heqibnd' ibnd.
        replace (t _) with (ins (exist (fun n0 : nat => n0 < length bs) x ltx2)).
        replace (eq_rect _ (fun x0 => |[x0]| -> 'F_FSize) _ _ _ _) 
           with (s1 (exist (fun n0 : nat => n0 < length bs) x ltx2)); auto.
        apply SO_NoQuant_Correct_Lem_4.
        rewrite Heqins.
        f_equal; by apply subset_eq_compat.
        transitivity (
        option_fun
          (fun j => Poly_Denote
            (lnth bs (eq_rect _ (fun x => |[x]|) j _ (esym HH))) M)).
        transitivity (eq_rect _ (fun x => option (|[x]| -> 'F_FSize)) (Some s1) _ HH);[|rewrite <- PMbs];by destruct HH.
        f_equal; apply functional_extensionality=> x.
        do 2 rewrite lnth_map; rewrite PolyTermVSCastCastId; rewrite <- PolyTerm_PolyTermVS_Correct; do 3 f_equal.
        apply subset_eq; by rewrite projT1_eq_rect.
        change PolyPlusOneVS with (LiftPolyExi (nu := nu (SO_NoQuant s)) PolyPlusOneVS).
        rewrite nth_map.
        rewrite SO_NoQuant_Correct_Lem_2.
        assert (i < length (exiFInputBounds (SO_NoQuant s))) as lti2;[by rewrite map_length in lti|].
        remember (H2 u (exist _ i lti2)) as H; clear HeqH H2; simpl in H.
        destruct (PolyVSDenotation _ _ adv u); auto.
        assert (length (lnth (exiFInputBounds (SO_NoQuant s)) (exist _ i lti2))
          = length (lnth [seq [seq LiftPolyExi i | i <- i] | i <- exiFInputBounds (SO_NoQuant s)] (exist _ i lti))).
          rewrite lnth_map map_length; do 2 f_equal; by apply subset_eq_compat.
        remember (option_fun
        (fun j => PolyVSDenotation (lnth (lnth (exiFInputBounds (SO_NoQuant s))
          (exist _ i lti2)) j) (AddModelExiF (length bs) f M) adv u)) as o1.
        replace (option_fun _) with (eq_rect _ (fun x => option (|[x]| -> 'F_FSize)) o1 _ H0).
        destruct o1;[|fcrush].
        replace (eq_rect _ (fun x => option (|[x]| -> 'F_FSize)) _ _ _) with
                (Some (eq_rect _ (fun x => |[x]| -> 'F_FSize) s3 _ H0));[|by destruct H0].
        move=> t out odef.
        remember (H (eq_rect _ (fun x => |[x]| -> 'F_FSize) t _ (esym H0)) out) as H'; clear HeqH' H.
        remember (exiFAdv _ _ _ _ _ _) as e1.
        replace (exiFAdv _ _ _ _ _ _) with e1 in H'.
        remember (H' odef) as H; clear HeqH H'.
        split; destruct H as [H' HO]; auto.
        move=> [x ltx].
        assert (x < length (lnth (exiFInputBounds (SO_NoQuant s)) (exist _ i lti2))) as ltx2;[by rewrite H0|].
        remember (H' (exist _ x ltx2)) as H; clear HeqH H' HO.
        remember (lt _ _ _) as L1; replace (lt _ _ _) with L1; auto; rewrite HeqL1; clear HeqL1 L1 H.
        f_equal.
        transitivity (t (eq_rect _ (fun x0 : nat => |[x0]|) (exist _ x ltx2) _ H0)).
        remember (length (lnth _ (exist _ i lti))) as a; clear Heqa; by destruct H0.
        f_equal; apply subset_eq; by rewrite projT1_eq_rect.
        transitivity (s3 (eq_rect _ (fun x0 : nat => |[x0]|) (exist _ x ltx) _ (esym H0))).
        f_equal; apply subset_eq; by rewrite projT1_eq_rect.
        remember (length (lnth _ (exist _ i lti))) as a; clear Heqa; by destruct H0.
        rewrite Heqe1; clear Heqe1.
        apply (exiFAdvEqLem (esym H0)); move=> [x ltx].
        remember (length (lnth _ (exist _ i lti))) as a; clear Heqa; by destruct H0.
        rewrite Heqo1; clear H Heqo1 o1.
        transitivity (option_fun (fun j => PolyVSDenotation (lnth
                  (lnth (exiFInputBounds (SO_NoQuant s))
                      (exist _ i lti2)) (eq_rect _ (fun x : nat => |[x]|) j _ (esym H0))) 
                (AddModelExiF (length bs) f M) adv u)).
        remember (length (lnth _ (exist _ i lti))) as a; clear Heqa; by destruct H0.
        f_equal; apply functional_extensionality;move=> [x ltx].
        rewrite <- SO_NoQuant_Correct_Lem_2.
        f_equal. 
        pose ([seq LiftPolyExi i0
            | i0 <- lnth (exiFInputBounds (SO_NoQuant s))
                      (exist _ i 
                          (Utils.lnth_map_obligation_1 (seq PolyTermVS)
                            (seq PolyTermVS) [eta map [eta LiftPolyExi]]
                            (exiFInputBounds (SO_NoQuant s)) (exist _ i lti)))]) as L1.
        assert (x < length L1) as ltx3.
          rewrite lnth_map map_length in ltx.
          by rewrite map_length.
        transitivity (lnth L1 (exist _ x ltx3));[
          |do 2 rewrite (lnth_nth PolyZeroVS); f_equal; by rewrite lnth_map].
        transitivity (LiftPolyExi
          (lnth (lnth (exiFInputBounds (SO_NoQuant s))
          (exist _ i (Utils.lnth_map_obligation_1 _ _ _ _ (exist _ i lti))))
          (exist _ x (Utils.lnth_map_obligation_1 _ _ _ (lnth (exiFInputBounds (SO_NoQuant s))
          (exist _ i (Utils.lnth_map_obligation_1 _ _ _ _ (exist _ i lti))))
          (exist _ x ltx3)))));[|by rewrite lnth_map].
        f_equal.
        do 2 rewrite (lnth_nth PolyZeroVS); do 2 f_equal;[
          by apply subset_eq_compat|by rewrite projT1_eq_rect].
  + move=> H; simpl.
    destruct H as [adv [H0 [H1 H2]]].
    unfold NoQuantSOBoundCondition in H2.
    remember (H2 (fun _ => 0%R) (exist _ 0 (ltn0Sn _))) as H2_0; clear HeqH2_0; simpl in H2_0.
    rewrite PolyTermVSCastCastId in H2_0; rewrite <- PolyTerm_PolyTermVS_Correct in H2_0.
    destruct (Poly_Denote y M) eqn: PMy;[|fcrush].
    assert (length [seq PolyTermVSCast (nu := (nu (SO_NoQuant s))) i | i <- [seq PolyTerm_PolyTermVS i | i <- bs]]
            = length bs) as HH;[by do 2 rewrite map_length|].
    remember (option_fun _) as o1.
    replace (option_fun _) with (eq_rect _ (fun x => option (|[x]| -> 'F_FSize)) o1 _ HH).
    2:{   rewrite Heqo1.
          transitivity (option_fun (fun j => PolyVSDenotation
            (lnth [seq PolyTermVSCast i | i <- [seq PolyTerm_PolyTermVS i | i <- bs]] 
                (eq_rect _ (fun x => |[x]|) j _ (esym HH))) M adv
            (fun=> 0%R)));[by destruct HH|].
          f_equal; apply functional_extensionality;move=> [x ltx].
          do 2 rewrite lnth_map; simpl.
          rewrite PolyTermVSCastCastId; rewrite <- PolyTerm_PolyTermVS_Correct.
          do 2 f_equal.
          apply subset_eq_compat; by rewrite projT1_eq_rect. }
    destruct HH; simpl.
    rewrite Heqo1; rewrite Heqo1 in H2_0; clear Heqo1 o1.
    destruct (option_fun _);[|fcrush].
    exists (exiFAdv _ _ adv 0 _).
    split;[unfold SO_Bound_Check;qauto|].
    apply IH.
    unfold NoQuantDenotation.
    (* rewrite (AdviceDropExiF_Spec adv) in H0 H1 H2; clear H2_0. *)
    exists (AdviceDropExiF adv).
    split;[|split].
    + clear H1 H2. 
      unfold NoQuantFormulaCondition; unfold NoQuantFormulaCondition in H0.
      do 2 rewrite map_length; simpl in *.
      move=> [u ltu]; simpl.
      (* unfold U in H0. *)
      rewrite map_length in H0.
      assert (forall (j : {n : nat | n < length (uniBounds (SO_NoQuant s))})
               (v : nat -> 'F_FSize),
             InBound M adv (u j)
               (nth PolyZeroVS
                  (uniBounds
                     (AddExiFBound (PolyTerm_PolyTermVS y)
                        [seq PolyTerm_PolyTermVS i | i <- bs] 
                        (SO_NoQuant s))) (` j)) (MakeU u v)).
      move=> j v.
      remember (ltu j v) as ltu'; clear Heqltu' ltu.
      unfold InBound in *.
      change PolyZeroVS with (LiftPolyExi (nu := nu (SO_NoQuant s)) PolyZeroVS).
      rewrite nth_map.
      rewrite <- SO_NoQuant_Correct_Lem_2_C in ltu'.
      remember (PolyVSDenotation _ _ _ _ _) as P0.
      replace (PolyVSDenotation _ _ _ _ _) with P0; auto.
      rewrite HeqP0; clear ltu' HeqP0 P0.
      unfold AddModelExiF.
      f_equal.
      f_equal.
      apply functional_extensionality_dep=> x.
      dep_if_case (x == length bs); auto.
      apply functional_extensionality=> z.
      assert (length bs = x);[by apply EEConvert in H|].
      apply (exiFAdvEqLem H1);move=> [w ltw].
      f_equal.
      by apply subset_eq; rewrite projT1_eq_rect.
      Search (_ <-> ` _ = ` _).
      rewrite H1.


      f_equal.
      simpl.
      auto.
      f_equal.
      rewrite (AdviceDropExiF_Spec adv); rewrite SO_NoQuant_Correct_Lem_2_A.
      rewrite <- SO_NoQuant_Correct_Lem_2_A in ltu'.
    unfold SO_Bound_Check. qauto.
    move=> ins out hyp.
    remember (H2_0 ins out hyp).
    simpl.



    destruct (Poly_Denote y M) eqn: PMy.
    destruct (option_fun (fun m => Poly_Denote (lnth bs m) M)) eqn:PMbs.
    destruct H as [adv [H0 [H1 H2]]].
    exists (exiFAdv _ _ adv 0 (length bs)).
    unfold NoQuantDenotation in H.





End NoQuantCorrect.
