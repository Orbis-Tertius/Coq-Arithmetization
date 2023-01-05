From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun zmodp ssrbool ssrnat ssralg seq fintype finalg tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.
From Coq Require Import ClassicalChoice.

Require Import CoqArith.Utils.

Require Import CoqArith.Sigma_1_1.
Require Import Program.

Section PrenexDef.

Variable (FSize : nat).

Inductive PolyTermVS {E} : Type :=
| UndefVS : PolyTermVS
| PolyFVarVS : nat -> PolyTermVS
| PolyUVarVS : nat -> PolyTermVS
| PolyFFunVS : forall (i a : nat), (|[a]| -> PolyTermVS) -> PolyTermVS
| PolyEFunVS : forall i, (|[lnth E i]| -> PolyTermVS) -> PolyTermVS
| PolyMinusOneVS : PolyTermVS
| PolyPlusOneVS : PolyTermVS
| PolyZeroVS : PolyTermVS
| PolyPlusVS : PolyTermVS -> PolyTermVS -> PolyTermVS
| PolyTimesVS : PolyTermVS -> PolyTermVS -> PolyTermVS
| PolyIndVS : PolyTermVS -> PolyTermVS -> PolyTermVS.

Inductive PropTermVS {E} : Type :=
| ZONotVS : PropTermVS -> PropTermVS
| ZOAndVS : PropTermVS -> PropTermVS -> PropTermVS
| ZOOrVS : PropTermVS -> PropTermVS -> PropTermVS
| ZOImpVS : PropTermVS -> PropTermVS -> PropTermVS
| ZOEqVS : @PolyTermVS E -> @PolyTermVS E -> PropTermVS.

Record Prenex {E} : Type :=
  mkPrenex {
    uniBounds : seq (@PolyTermVS E);
    exiBounds : forall i, ((|[lnth E i]| -> (@PolyTermVS E)) * (@PolyTermVS E));
    formula : @PropTermVS E
  }.

Definition PrenexAdvice E : Type :=
  forall i, (|[lnth E i]| -> 'F_FSize) -> option 'F_FSize.

Program Fixpoint PolyVSDenotation {E} (M : @Sigma11Model FSize)
  (p : @PolyTermVS E) (adv : PrenexAdvice E) :
  (nat -> 'F_FSize) -> option ('F_FSize) :=
  match p with
  | UndefVS => fun _ => None
  | PolyFVarVS i => fun _ => Some (V_F _ M i)
  | PolyUVarVS i => fun u => Some (u i)
  | PolyFFunVS i a t => fun u =>
    (if a == projT1 (F_S _ M i) as b return ((a == projT1 (F_S _ M i)) = b -> option ('F_FSize))
     then fun _ => (
          let ds := option_fun (fun x => PolyVSDenotation M (t x) adv u) in
          obind (fun t : |[a]| -> 'F_FSize => projT2 (F_S _ M i) t) ds)
      else fun _ => None) (erefl _)
  | PolyEFunVS i t => fun u =>
    let ds := option_fun (fun x => PolyVSDenotation M (t x) adv u) in
    obind (fun t : |[lnth E i]| -> 'F_FSize => adv i t) ds
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

Fixpoint PropVSDenotation {E} (M : @Sigma11Model FSize)
  (f : @PropTermVS E)
  (adv : PrenexAdvice E) :
  (nat -> 'F_FSize) -> option bool :=
  match f with
  | ZONotVS f => fun u => 
    let d := PropVSDenotation M f adv u in
    obind (fun d => Some (~~ d)) d
  | ZOAndVS f1 f2 => fun u => 
    let d1 := PropVSDenotation M f1 adv u in
    let d2 := PropVSDenotation M f2 adv u in
    obind (fun r1 => obind (fun r2 => Some (r1 && r2)) d2) d1
  | ZOOrVS f1 f2 => fun u => 
    let d1 := PropVSDenotation M f1 adv u in
    let d2 := PropVSDenotation M f2 adv u in
    obind (fun r1 => obind (fun r2 => Some (r1 || r2)) d2) d1
  | ZOImpVS f1 f2 => fun u => 
    let d1 := PropVSDenotation M f1 adv u in
    let d2 := PropVSDenotation M f2 adv u in
    obind (fun r1 => obind (fun r2 => Some (r1 ==> r2)) d2) d1
  | ZOEqVS r1 r2 => fun u => 
    let d1 := PolyVSDenotation M r1 adv u in
    let d2 := PolyVSDenotation M r2 adv u in
    obind (fun r1 => obind (fun r2 => Some (r1 == r2)) d2) d1
  end.

Definition InBound (M : @Sigma11Model FSize)
  {E} (adv : PrenexAdvice E)
  (r : 'F_FSize)
  (b : @PolyTermVS E) 
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

Program Definition U {E} (M : @Sigma11Model FSize)
  (f : @Prenex E) (adv : PrenexAdvice E) : Type 
  := { u : |[length (uniBounds f)]| -> 'F_FSize | 
       forall j : |[length (uniBounds f)]|,
       forall v : nat -> 'F_FSize, 
       InBound M adv (u j) (lnth (uniBounds f) j) (MakeU u v)
    }.

Program Definition PrenexFormulaCondition {E} (M : @Sigma11Model FSize)
  (f : Prenex) (adv : PrenexAdvice E) : Prop :=
  forall (u : U M f adv), 
  PropVSDenotation M (formula f) adv (MakeU u (fun _ => 0%R)) == Some true.

Program Definition PrenexUniversalCondition {E} (M : @Sigma11Model FSize)
  (f : Prenex) (adv : PrenexAdvice E) : Prop :=
  forall (u : nat -> 'F_FSize) (i : |[length (uniBounds f)]|),
    (forall j : |[i]|, InBound M adv (u j) (lnth (uniBounds f) j) u) ->
    exists o, PolyVSDenotation M (lnth (uniBounds f) i) adv u = Some o.
Next Obligation. strivial use: ltn_trans. Qed.

Program Fixpoint FunBoundsVS {E} (M : @Sigma11Model FSize)
  (adv : PrenexAdvice E) {a}
  (ins : |[a]| -> 'F_FSize) (out : 'F_FSize)
  (insB : |[a]| -> PolyTermVS) (outB : PolyTermVS) :
  (nat -> 'F_FSize) -> bool := fun u =>
  match a with
  | 0 => InBound M adv out outB u
  | n.+1 => InBound M adv (ins 0) (insB 0) u &&
    @FunBoundsVS E M adv n (fun x => ins (x.+1)) out (fun x => insB (x.+1)) outB u
  end.

Definition PrenexExiBoundCondition {E} (M : @Sigma11Model FSize)
  (f : Prenex) (adv : PrenexAdvice E) : Prop :=
  forall u : nat -> 'F_FSize, forall i : |[length E]|,
  forall (ins : |[lnth E i]| -> 'F_FSize) (out : 'F_FSize),
  adv i ins == Some out -> 
  FunBoundsVS M adv ins out 
    (fun x => (exiBounds f i).1 x)
    (exiBounds f i).2 (MakeU ins u) == true.

Definition PrenexDenotation {E} (M : @Sigma11Model FSize)
  (f : Prenex) : Prop :=
  exists (a : PrenexAdvice E),
    PrenexFormulaCondition M f a /\
    PrenexUniversalCondition M f a /\
    PrenexExiBoundCondition M f a.

End PrenexDef.

Section PrenexTranslation.

Variable (FSize : nat).

Fixpoint PolyTerm_PolyTermVS {E} (n : nat) (p : PolyTerm) : @PolyTermVS E :=
  match p with
  | PolyVar m => 
    if m < n
    then PolyUVarVS (n.-1 - m)
    else PolyFVarVS (m - n)
  | PolyFun i a t => PolyFFunVS i a (fun x => PolyTerm_PolyTermVS n (t x))
  | PolyMinusOne => PolyMinusOneVS
  | PolyPlusOne => PolyPlusOneVS
  | PolyZero => PolyZeroVS
  | PolyPlus r1 r2 => PolyPlusVS (PolyTerm_PolyTermVS n r1) (PolyTerm_PolyTermVS n r2)
  | PolyTimes r1 r2 => PolyTimesVS (PolyTerm_PolyTermVS n r1) (PolyTerm_PolyTermVS n r2)
  | PolyInd r1 r2 => PolyIndVS (PolyTerm_PolyTermVS n r1) (PolyTerm_PolyTermVS n r2)
  end.

Theorem PolyTerm_PolyTermVS_Correct M p {A} (a : PrenexAdvice _ A) u :
  PolyVSDenotation FSize M (PolyTerm_PolyTermVS 0 p) a u = Poly_Denote _ M p.
Proof.
  induction p; auto; simpl.
  induction n; qauto.
  - dep_if_case (a0 == projT1 (F_S _ M i)); auto;[rewrite dep_if_case_true|rewrite dep_if_case_false];auto.
    do 2 f_equal; auto; apply functional_extensionality=> t;[|apply H].
    f_equal; apply functional_extensionality=> x. 
    f_equal; by apply subset_eq_compat.
  all: f_equal;[|by rewrite IHp1];
      apply functional_extensionality; intro;
      f_equal; by rewrite IHp2.
Qed.

Theorem PolyTerm_PolyTermVS_Correct_N_Rec M p n {A} (a : PrenexAdvice _ A) u :
  PolyVSDenotation FSize M (PolyTerm_PolyTermVS n.+1 p) a u = 
  PolyVSDenotation FSize (AddModelV _ M (u 0)) (PolyTerm_PolyTermVS n p) a (fun x => u x.+1).
Proof.
  induction p; auto; simpl.
  simpl.
  destruct (n0 < n) eqn:E1; simpl.
  replace (n0 < n.+1) with true; simpl.
  by rewrite <- subIn_addOut.
  symmetry.
  assert (n0 < n);[|apply ltnSE, ltnW in H];qauto lq: on.
  change (n0 < n.+1) with (n0 <= n).
  assert (n <= n0);[move: n0 E1; induction n; destruct n0; try (cbn; qauto)|clear E1].
  destruct (n0 == n) eqn:E2; simpl.
  apply EEConvert in E2.
  destruct E2.
  replace (n0 <= n0) with true.
  unfold ExtendAt0.
  replace (n0 - n0 == 0) with true.
  by rewrite n_sub_n.
  assert (n < n0);[move: n0 E2 H; induction n; destruct n0; try (cbn; qauto)|clear E2 H].
  assert (n0 <= n = false);[move: n H0; induction n0; destruct n; try (cbn in *; qauto)|].
  rewrite H.
  unfold ExtendAt0.
  change (n0 - n == 0) with (n0 <= n).
  rewrite H; simpl.
  by rewrite subOut_addIn_LR.
  - dep_if_case (a0 == projT1 (F_S _ M i)); auto;[rewrite dep_if_case_true|rewrite dep_if_case_false];auto.
    do 2 f_equal; auto; apply functional_extensionality=> t;[|apply H].
    f_equal; apply functional_extensionality=> x. 
    f_equal; by apply subset_eq_compat.
  all: f_equal;[|by rewrite IHp1];
      apply functional_extensionality; intro;
      f_equal; by rewrite IHp2.
Qed.

Theorem PolyTerm_PolyTermVS_Correct_N M p n {A} (a : PrenexAdvice _ A) u :
  PolyVSDenotation FSize M (PolyTerm_PolyTermVS n p) a u = 
  Poly_Denote _ {| V_F := fun x => if x < n then u (n.-1 - x) else V_F FSize M (x - n); F_S := F_S FSize M |} p.
Proof.
  move: M u; induction n=>M u.
  - rewrite PolyTerm_PolyTermVS_Correct.
    do 2 f_equal.
    destruct M; f_equal.
    apply functional_extensionality=> x.
    by rewrite ltn0 zero_sub.
  - rewrite PolyTerm_PolyTermVS_Correct_N_Rec.
    unfold AddModelV; simpl.
    rewrite IHn; clear IHn.
    do 2 f_equal.
    apply functional_extensionality=> x.
    unfold ExtendAt0; simpl.
    change (x - n == 0) with (x <= n).
    change (x < n.+1) with (x <= n).
    destruct (x < n) eqn:PM.
    replace (x <= n) with true.
    rewrite <- subIn_addOut; auto.
    move: x PM; induction n; destruct x; try (cbn; qauto); intro; by apply IHn.
    destruct (x == n) eqn:EM.
    apply EEConvert in EM; destruct EM.
    by rewrite n_sub_n leqnn.
    replace (x <= n) with false.
    assert (n < x);[move: x PM EM; induction n; destruct x; try (cbn; qauto)|clear PM EM].
    rewrite subOut_addIn_LR; auto.
    move: x PM EM; induction n; destruct x; try (cbn; qauto); intros; by apply IHn.
Qed.

Fixpoint ZerothOrder_ZerothOrderVS {E} (p : ZerothOrderFormula) : @PropTermVS E :=
  match p with
  | ZONot m => ZONotVS (ZerothOrder_ZerothOrderVS m)
  | ZOAnd r1 r2 => ZOAndVS (ZerothOrder_ZerothOrderVS r1) (ZerothOrder_ZerothOrderVS r2)
  | ZOOr r1 r2 => ZOOrVS (ZerothOrder_ZerothOrderVS r1) (ZerothOrder_ZerothOrderVS r2)
  | ZOImp r1 r2 => ZOImpVS (ZerothOrder_ZerothOrderVS r1) (ZerothOrder_ZerothOrderVS r2)
  | ZOEq a b => ZOEqVS (PolyTerm_PolyTermVS 0 a) (PolyTerm_PolyTermVS 0 b)
  end.

Theorem ZerothOrder_ZerothOrderVS_Correct M p {A} (a : PrenexAdvice _ A) t :
  PropVSDenotation FSize M (ZerothOrder_ZerothOrderVS p) a t = ZerothOrder_Denote _ M p.
Proof.
  induction p; try qauto.
  by simpl; do 2 rewrite PolyTerm_PolyTermVS_Correct.
Qed.

Program Definition ZO_Prenex (f : ZerothOrderFormula) : @Prenex [::] :=
  {| uniBounds := [::]
   ; exiBounds := emptyTuple
   ; formula := ZerothOrder_ZerothOrderVS f
  |}.

Lemma ZO_Prenex_Correct_PrenexFormulaCondition
  M f : ZerothOrder_Denote FSize M f == Some true <-> 
  exists a, PrenexFormulaCondition _ M (ZO_Prenex f) a.
Proof.
  split;move=> H.
  - exists (fun _ _ => None).
    unfold PrenexFormulaCondition. 
    move=> u; by rewrite ZerothOrder_ZerothOrderVS_Correct.
  - destruct H as [adv H].
    unfold PrenexFormulaCondition in H.
    assert (U _ M (ZO_Prenex f) adv).
    unfold U.
    simpl.
    exists emptyTuple.
    move=> [j ltj]; fcrush.
    remember (H X) as H'; clear HeqH' H.
    by rewrite ZerothOrder_ZerothOrderVS_Correct in H'.
Qed.

Lemma ZO_Prenex_Correct_PrenexUniversalCondition
  M f : forall a, PrenexUniversalCondition FSize M (ZO_Prenex f) a.
Proof. move=> a u [i lti]; fcrush. Qed.

Lemma ZO_Prenex_Correct_PrenexExiBoundCondition
  M f : forall a, PrenexExiBoundCondition FSize M (ZO_Prenex f) a.
Proof. move=> a u [i lti]; fcrush. Qed.

Theorem ZO_Prenex_Correct M p :
  ZerothOrder_Denote FSize M p == Some true <-> PrenexDenotation _ M (ZO_Prenex p).
Proof.
  qauto use: ZO_Prenex_Correct_PrenexFormulaCondition
           , ZO_Prenex_Correct_PrenexUniversalCondition
           , ZO_Prenex_Correct_PrenexExiBoundCondition.
Qed.

Program Fixpoint LiftPolyExi {a E}
  (p : @PolyTermVS E) : @PolyTermVS (a :: E) :=
  match p with
  | UndefVS => UndefVS
  | PolyFVarVS m => PolyFVarVS m
  | PolyUVarVS m => PolyUVarVS m
  | PolyFFunVS i a' t => 
    if i == 0
    then (
      if a' == a as B return a' == a = B -> @PolyTermVS (a :: E)
      then fun _ => PolyEFunVS 0 (fun x => LiftPolyExi (t x))
      else fun _ => UndefVS
      ) (erefl _)
    else PolyFFunVS (i.-1) a' (fun x => LiftPolyExi (t x))
  | PolyEFunVS i t => PolyEFunVS i.+1 (fun x => LiftPolyExi (t x))
  | PolyMinusOneVS => PolyMinusOneVS
  | PolyPlusOneVS => PolyPlusOneVS
  | PolyZeroVS => PolyZeroVS
  | PolyPlusVS r1 r2 => PolyPlusVS (LiftPolyExi r1) (LiftPolyExi r2)
  | PolyTimesVS r1 r2 => PolyTimesVS (LiftPolyExi r1) (LiftPolyExi r2)
  | PolyIndVS r1 r2 => PolyIndVS (LiftPolyExi r1) (LiftPolyExi r2)
  end.
Next Obligation. apply EEConvert in e; qauto. Qed.

Fixpoint LiftPropExi {a E}
  (p : @PropTermVS E) : @PropTermVS (a :: E) :=
  match p with
  | ZONotVS f => ZONotVS (LiftPropExi f)
  | ZOAndVS f1 f2 => ZOAndVS (LiftPropExi f1) (LiftPropExi f2)
  | ZOOrVS f1 f2 => ZOOrVS (LiftPropExi f1) (LiftPropExi f2)
  | ZOImpVS f1 f2 => ZOImpVS (LiftPropExi f1) (LiftPropExi f2)
  | ZOEqVS r1 r2 => ZOEqVS (LiftPolyExi r1) (LiftPolyExi r2)
  end.

Program Fixpoint LiftPolyUni {E} (p : @PolyTermVS E): @PolyTermVS (map (fun x => x.+1) E) :=
  match p with
  | UndefVS => UndefVS
  | PolyFVarVS i => 
    if i == 0
    then PolyUVarVS 0
    else PolyFVarVS (i.-1)
  | PolyUVarVS i => PolyUVarVS (i.+1)
  | PolyFFunVS i a t => PolyFFunVS i a (fun x => LiftPolyUni (t x))
  | PolyEFunVS i t => 
    PolyEFunVS i 
    (fun x => 
      (if (x == 0) as b return (x == 0) = b -> @PolyTermVS (map (fun x => x.+1) E)
       then fun _ => PolyUVarVS 0
       else fun _ => LiftPolyUni (t x.-1)) (erefl _)
    )
  | PolyMinusOneVS => PolyMinusOneVS
  | PolyPlusOneVS => PolyPlusOneVS
  | PolyZeroVS => PolyZeroVS
  | PolyPlusVS p1 p2 => PolyPlusVS (LiftPolyUni p1) (LiftPolyUni p2)
  | PolyTimesVS p1 p2 => PolyTimesVS (LiftPolyUni p1) (LiftPolyUni p2)
  | PolyIndVS p1 p2 => PolyIndVS (LiftPolyUni p1) (LiftPolyUni p2)
  end.
Next Obligation. by rewrite map_length. Qed.
Next Obligation. by rewrite lnth_map. Qed.
Next Obligation. 
  destruct x;[fcrush|clear e]; simpl. 
  rewrite lnth_map in H; simpl in H.
  remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
  by replace H0 with DDD0;[|apply eq_irrelevance].
Qed.

Fixpoint LiftPropUni {E}
  (f : @PropTermVS E):
  @PropTermVS (map (fun x => x.+1) E) :=
  match f with
  | ZONotVS f => ZONotVS (LiftPropUni f)
  | ZOAndVS f1 f2 => ZOAndVS (LiftPropUni f1) (LiftPropUni f2)
  | ZOOrVS f1 f2 => ZOOrVS (LiftPropUni f1) (LiftPropUni f2)
  | ZOImpVS f1 f2 => ZOImpVS (LiftPropUni f1) (LiftPropUni f2)
  | ZOEqVS r1 r2 => ZOEqVS (LiftPolyUni r1) (LiftPolyUni r2)
  end.

Fixpoint LiftArgs {E} n (bs : seq PolyTerm) : seq (@PolyTermVS E) :=
  match bs with
  | [::] => [::]
  | x :: xs => PolyTerm_PolyTermVS n x :: LiftArgs n.+1 xs
  end.

Theorem LiftArgs_length {E n bs} : length (@LiftArgs E n bs) = length bs.
Proof. move:n; induction bs; qauto. Qed.

Program Definition PrenexAddExi {E} 
  (bs : seq PolyTerm) (y : PolyTerm) (q : @Prenex E) : @Prenex (length bs :: E) :=
  {| uniBounds := map LiftPolyExi (uniBounds q)
   ; exiBounds := fun i => (
      if i == 0 as B return i == 0 = B -> (|[lnth (length bs :: E) i]| -> @PolyTermVS (length bs :: E)) * @PolyTermVS (length bs :: E)
      then fun _ => (lnth (LiftArgs 0 bs), PolyTerm_PolyTermVS (length bs) y)
      else fun _ => (fun x => LiftPolyExi ((exiBounds q (i.-1)).1 x), LiftPolyExi (exiBounds q (i.-1)).2)
   ) (erefl _)
   ; formula := LiftPropExi (formula q)
  |}.
Next Obligation. by destruct i;[fcrush|]. Qed.
Next Obligation. by destruct i;[fcrush|]. Qed.
Next Obligation. 
  destruct i;[fcrush|]; simpl in *.
  remember (PrenexAddExi_obligation_3 _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
  by replace DDD0 with H0;[|apply eq_irrelevance].
Qed.
Next Obligation. rewrite LiftArgs_length. by destruct i;[|fcrush]. Qed.

Program Definition PrenexAddUni {E} (b : PolyTerm) (q : @Prenex E) : @Prenex (map (fun x => x.+1) E) :=
  let b' := PolyTerm_PolyTermVS 0 b in
  {| uniBounds := b' :: map LiftPolyUni (uniBounds q)
   ; exiBounds := fun i => (fun x => (ExtendAt0N b' (fun y => LiftPolyUni (x.1 y)), LiftPolyUni x.2)) (exiBounds q i)
   ; formula := LiftPropUni (formula q)
  |}.
Next Obligation. by rewrite map_length in H. Qed.
Next Obligation. 
  rewrite lnth_map in H; simpl in H.
  remember (PrenexAddUni_obligation_1 _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
  remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD1; clear HeqDDD1; simpl in DDD1.
  by replace DDD0 with DDD1;[|apply eq_irrelevance].
Qed.

Fixpoint Q_Ar (f : QuantifiedFormula) : seq nat :=
  match f with
  | ZO z => [::]
  | QExists bs y f => length bs :: Q_Ar f
  | QForall b f => map (fun x => x.+1) (Q_Ar f)
  end.

Fixpoint Q_Prenex (f : QuantifiedFormula) : @Prenex (Q_Ar f) :=
  match f with
  | ZO z => ZO_Prenex z
  | QExists bs y f => PrenexAddExi bs y (Q_Prenex f)
  | QForall b f => PrenexAddUni b (Q_Prenex f)
  end.

Program Definition AdviceExtend {E B}
  (f : (|[B]| -> 'F_FSize) -> option ('F_FSize))
  (adv : PrenexAdvice _ E) : 
  PrenexAdvice _ (B :: E) := fun i => 
  (if i == 0 as b return (i == 0 = b -> (|[lnth (B :: E) i]| -> 'F_FSize) -> option 'F_FSize)
   then fun _ => f
   else fun _ => adv i.-1) (erefl _).
Next Obligation. destruct i; auto. Qed.
Next Obligation.
  destruct i;[fcrush|]; simpl in *.
  remember (AdviceExtend_obligation_2 _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
  by replace H0 with DDD0;[|apply eq_irrelevance].
Qed.
Next Obligation. by destruct i. Qed.

Program Definition AdviceDrop {E B}
  (adv : PrenexAdvice FSize (B :: E)) : 
  PrenexAdvice _ E := fun i => adv i.+1.

Program Definition Uni_AdviceF {s E}
  (H : {r : 'F_FSize | r < s} -> PrenexAdvice _ E) :
  PrenexAdvice _ (map (fun x => x.+1) E) := fun i t => (
    if (t 0) < s as B2 return (t 0) < s = B2 -> option 'F_FSize
    then fun p => H (exist _ (t 0) p) i (fun x => t (x.+1))
    else fun _ => None) (erefl _).
Next Obligation. by rewrite lnth_map. Qed.
Next Obligation. clear p t; by rewrite map_length in H0. Qed.
Next Obligation. 
  rewrite lnth_map; simpl.
  remember (Uni_AdviceF_obligation_2 _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
  remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD1; clear HeqDDD1; simpl in DDD1.
  by replace DDD1 with DDD0;[|apply eq_irrelevance].
Qed.

Program Definition Uni_Advice_Drop {E} r
  (adv : PrenexAdvice _ [seq x.+1 | x <- E]) : PrenexAdvice _ E :=
  fun i t => adv i (ExtendAt0N r t).
Next Obligation. by rewrite map_length. Qed.
Next Obligation. 
  rewrite lnth_map in H; simpl in *. 
  by replace (Utils.lnth_map_obligation_1 _ _ _ _ (exist _ i _)) with H0 in H;[|apply eq_irrelevance].
Qed.

Lemma Q_Prenex_Correct_Lem_0 {M u E p f adv} :
  PolyVSDenotation (E := E) _ (AddModelF _ M f) p adv u
  = PolyVSDenotation FSize M (LiftPolyExi p) (AdviceExtend (projT2 f) adv) u.
Proof.
  elim: p; try qauto.
  - move=> i a' p IH.
    simpl.
    destruct i; unfold ExtendAt0; simpl.
    dep_if_case (a' == projT1 f); auto.
    rewrite dep_if_case_true; auto; simpl.
    unfold LiftPolyExi_obligation_1.
    assert (a' = projT1 f);[by apply EEConvert in H|].
    unfold AdviceExtend at 1; simpl.
    remember (AdviceExtend_obligation_4 _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
    remember (PolyVSDenotation_obligation_1 _ _ _ _ _ _ _ _) as DDD1; clear HeqDDD1; simpl in DDD1.
    unfold ExtendAt0 in DDD1; simpl in DDD1.
    transitivity (obind
        (fun t => projT2 f (fun x => t (exist _ (` x) (DDD0 t x))))
        (option_fun (eq_rect _ (fun x => |[x]| -> _) (fun x => 
            PolyVSDenotation _ (AddModelF FSize M f) (p x) adv u) _ H0))).
    destruct H0; simpl.
    do 2 (f_equal; apply functional_extensionality; intro).
    f_equal; by apply subset_eq_compat.
    do 2 f_equal.
    apply functional_extensionality;move=> [x ltx].
    rewrite eq_rect_ap_el.
    rewrite IH.
    do 3 f_equal.
    destruct (esym H0); simpl.
    by apply subset_eq_compat.
    rewrite dep_if_case_false; auto; simpl.
    dep_if_case (a' == projT1 (F_S FSize M i)); auto.
    rewrite dep_if_case_true; auto; simpl.
    f_equal.
    apply functional_extensionality=> t.
    f_equal.
    apply functional_extensionality;move=>[x ltx].
    f_equal; by apply subset_eq_compat.
    f_equal;apply functional_extensionality;move=>[x ltx]; auto.
    rewrite dep_if_case_false; auto; simpl.
  - move=> [i lti] p IH.
    simpl.
    f_equal.
    apply functional_extensionality=> t.
    unfold AdviceExtend; simpl.
    assert (lti = AdviceExtend_obligation_2 E (projT1 f) (exist _ i.+1 lti) (erefl _)) as EE;[apply eq_irrelevance|].
    transitivity (adv (exist _ i _) (eq_rect _ (fun x => |[lnth E (exist (fun n0 : nat => n0 < length E) i x)]| -> _) t _ EE)).
    by destruct EE.
    f_equal.
    apply functional_extensionality;move=>[x ltx].
    rewrite eq_rect_ap_el.
    f_equal.
    apply subset_eq; simpl.
    by rewrite projT1_eq_rect.
    f_equal.
    apply functional_extensionality;move=>[x ltx].
    by rewrite IH.
Qed.

Lemma Q_Prenex_Correct_Lem_1 {M u E p f adv} :
  PropVSDenotation (E := E) _ (AddModelF _ M f) p adv u
  = PropVSDenotation FSize M (LiftPropExi p) (AdviceExtend (projT2 f) adv) u.
Proof.
  elim: p; try qauto.
  move=> p1 p2.
  simpl.
  by do 2 rewrite Q_Prenex_Correct_Lem_0.
Qed.

Lemma Q_Prenex_Correct_Lem_2 (M: Sigma11Model FSize) 
  {A} (adv: PrenexAdvice _ A)
  ar u ins out insB outB F :
FunBoundsVS FSize (AddModelF FSize M F) adv ins out insB outB u = 
FunBoundsVS FSize M (AdviceExtend (projT2 F) adv) (a := ar) ins out (fun x => LiftPolyExi (insB x)) (LiftPolyExi outB) u.
Proof.
  move:M ins; induction ar=> M ins; simpl;[by unfold InBound; rewrite <- Q_Prenex_Correct_Lem_0|].
  by f_equal;[unfold InBound; rewrite <- Q_Prenex_Correct_Lem_0|rewrite <- IHar].
Qed.

Lemma Q_Prenex_Correct_Lem_3_0 {n} (M: Sigma11Model FSize) 
  {A} (adv: PrenexAdvice _ A)
  (bs: seq PolyTerm) (y: PolyTerm) u (ins : |[n + length (LiftArgs n bs)]| -> _) out
  : FunBoundsVS FSize M adv (fSeqBack ins) out (lnth (LiftArgs n bs)) (PolyTerm_PolyTermVS (length bs + n) y) (MakeU ins u) = 
    FunBounds FSize {| V_F := fun x => if x < n then (MakeU ins u) (n.-1 - x) else V_F FSize M (x - n); F_S := F_S FSize M |} (fSeqBack ins) out (eq_rect _ (fun x => |[x]| -> _) (lnth bs) _ (esym LiftArgs_length)) y.
Proof.
  move: n M ins; induction bs=> n M ins;[
    simpl; unfold InBound; rewrite PolyTerm_PolyTermVS_Correct_N; by destruct (Poly_Denote _ _ _)|simpl].
  unfold InBound.
  remember (Sigma_1_1.FunBounds_obligation_4 _ _ _ _ _ _ _) as DD2; clear HeqDD2; simpl in DD2;
  remember (Sigma_1_1.FunBounds_obligation_5 _ _ _ _ _ _ _) as DD3; clear HeqDD3; simpl in DD3.
  remember (Poly_Denote FSize _ _) as P.
  rewrite eq_rect_ap_el dep_match_zero in HeqP;[by rewrite projT1_eq_rect|symmetry in HeqP; destruct HeqP].
  rewrite PolyTerm_PolyTermVS_Correct_N.
  destruct (Poly_Denote _ _ _); auto; f_equal; auto.
  replace (fun x : {n0 : nat | n0 < length (LiftArgs n.+1 bs)} =>
   lnth (LiftArgs n.+1 bs) (exist _ (` x) _)) with (lnth (@LiftArgs A n.+1 bs));[|
    apply functional_extensionality;move=>[x ltx];do 2 f_equal; apply eq_irrelevance].
  rewrite addSnnS.
  simpl in ins.
  remember (eq_rect _ (fun x => |[x]| -> _) ins _ (esym (addSnnS _ _))) as ins'.
  replace (MakeU ins u) with (MakeU ins' u);[|by rewrite Heqins'; clear ins' Heqins'; destruct (esym _)].
  replace (fun x => fSeqBack _ _) with (fSeqBack ins').
  rewrite IHbs; clear IHbs; rewrite Heqins'; clear ins' Heqins'; simpl.
  f_equal.
  unfold AddModelV, ExtendAt0, fSeqBack, MakeU; simpl.
  f_equal.
  destruct (esym _); simpl.
  apply functional_extensionality=>x.
  destruct (x == 0) eqn:x0.
  apply EEConvert in x0. 
  rewrite x0; simpl.
  rewrite dep_if_case_true.
  rewrite zero_sub.
  apply Utils.cRange_obligation_1.
  move=> Hyp.
  f_equal; apply subset_eq_compat.
  by rewrite zero_sub.
  destruct x;[fcrush|clear x0;simpl].
  change (x.+1 < n.+1) with (x < n).
  destruct (x < n) eqn:E;auto.
  rewrite subIn_addIn;auto.
  unfold fSeqBack; apply functional_extensionality;move=>[x ltx]; simpl.
  rewrite eq_rect_ap_el; f_equal.
  apply subset_eq; rewrite projT1_eq_rect; simpl; by rewrite addSnnS. 
  apply functional_extensionality;move=>[x ltx]; simpl.
  do 2 rewrite eq_rect_ap_el; f_equal.
  remember (Utils.lnth_obligation_1 _ _ _ _) as DDD; clear HeqDDD; simpl in DDD.
  remember (` _) as n'.
  rewrite projT1_eq_rect in Heqn'; simpl in Heqn'; symmetry in Heqn'; destruct Heqn'.
  f_equal.
  destruct (esym _); by apply subset_eq_compat.
  unfold fSeqBack; apply functional_extensionality;move=>[x ltx]; simpl.
  unfold fSeqBack; rewrite Heqins'; clear ins' Heqins'.
  rewrite eq_rect_ap_el; f_equal.
  apply subset_eq; rewrite projT1_eq_rect; simpl; by rewrite addSnnS.
Qed. 

Lemma Q_Prenex_Correct_Lem_3 (M: Sigma11Model FSize) 
  {A} (adv: PrenexAdvice _ A)
  (bs: seq PolyTerm) (y: PolyTerm) u ins out
  : FunBoundsVS FSize M adv ins out (lnth (LiftArgs 0 bs)) (PolyTerm_PolyTermVS (length bs) y) (MakeU ins u) = 
    FunBounds FSize M ins out (eq_rect _ (fun x => |[x]| -> _) (lnth bs) _ (esym LiftArgs_length)) y.
Proof.
  assert (ins = fSeqBack (ins : |[0 + _]| -> _)) as insb.
    unfold fSeqBack.
    apply functional_extensionality;move=> [x ltx].
    f_equal; apply subset_eq_compat; by rewrite ZeroCanc.
  replace ins with (fSeqBack (ins : |[0 + _]| -> _)) at 1.
  rewrite <- (@ZeroCanc (length bs)) at 1.
  rewrite Q_Prenex_Correct_Lem_3_0.
  destruct M; do 2 f_equal; auto.
  apply functional_extensionality=>x; by destruct x.
Qed.

Lemma Q_Prenex_Correct_Lem_4 
  {M E v o B} {u0 : 'F_FSize} {ltu : u0 < o}
  {adv : {r : 'F_FSize | r < o} -> PrenexAdvice _ E} :
  PolyVSDenotation FSize (AddModelV FSize M u0) B (adv (exist _ u0 ltu)) v
  = PolyVSDenotation FSize M (LiftPolyUni B) (Uni_AdviceF adv) (ExtendAt0 u0 v).
Proof.
  induction B; try qauto.
  - destruct n; qauto.
  - simpl.
    dep_if_case (a == projT1 (F_S FSize M i)); auto;
      [rewrite dep_if_case_true|rewrite dep_if_case_false]; auto.
    f_equal. 
    apply functional_extensionality=>t.
    f_equal.
    apply functional_extensionality;move=>[x ltx].
    f_equal; by apply subset_eq_compat.
    f_equal; apply functional_extensionality;move=>[x ltx]; qauto.
  - simpl.
    pose (lnth [seq x.+1 | x <- E]
          (exist (fun n0 : nat => n0 < length [seq x.+1 | x <- E]) 
             (` i)
             (LiftPolyUni_obligation_1 E (PolyEFunVS i p) i p
                (erefl (PolyEFunVS i p))))) as A.
    assert (A = (lnth E i).+1) as EE.
        unfold A; rewrite lnth_map; simpl; do 2 f_equal.
        destruct i; by apply subset_eq_compat.
    remember (fun x => PolyVSDenotation _ M _ _ _) as P1.
    remember [eta Uni_AdviceF adv _] as adv'.
    transitivity (obind (eq_rect _ (fun x => (|[x]| -> _) -> _) adv' _ EE) (option_fun (eq_rect _ (fun x => |[x]| -> _) P1 _ EE)));[|by destruct EE].
    simpl.
    rewrite eq_rect_ap_el.
    remember (P1 _) as P1'.
    rewrite HeqP1 in HeqP1'.
    rewrite dep_if_case_true in HeqP1';[cbn; by rewrite projT1_eq_rect|].
    rewrite HeqP1'; clear HeqP1' P1'.
    assert (PolyVSDenotation FSize M (PolyUVarVS 0) (Uni_AdviceF adv) (ExtendAt0 u0 v) = Some u0) as PM;[auto|rewrite PM;simpl].
    replace (option_fun (fun x => eq_rect _ (fun x => |[x]| -> _) P1 _ EE _)) 
       with (option_fun (fun x => PolyVSDenotation FSize (AddModelV FSize M u0) (p x) (adv (exist _ u0 ltu)) v)).
    destruct (option_fun _) eqn: PM2; simpl; auto.
    rewrite eq_rect_ap_el.
    rewrite Heqadv'; clear Heqadv' adv'.
    unfold Uni_AdviceF; change (?x == exist _ ?y _) with (` x == y);
    rewrite dep_if_case_true.
    by rewrite eq_rect_ap_el dep_if_case_true;[rewrite projT1_eq_rect|destruct u0].
    move=>Hyp; simpl.
    assert (i = (exist _ (` i) (Uni_AdviceF_obligation_2 o E _ _ Hyp))) as EE2;[
      destruct i; by apply subset_eq_compat|].
    transitivity (adv (exist (fun r : 'F_FSize => r < o) u0 ltu) (exist _ (` i) (Uni_AdviceF_obligation_2 o E _ _ Hyp)) 
                         (eq_rect _ (fun x => |[lnth E x]| -> _) o0 _ EE2));[by destruct EE2|f_equal].
    apply subset_eq_compat.
    by rewrite eq_rect_ap_el dep_if_case_true;[rewrite projT1_eq_rect|].
    apply functional_extensionality; move=> [x ltx]; simpl.
    do 2 rewrite eq_rect_ap_el; rewrite dep_if_case_false;[by rewrite projT1_eq_rect|]=> Hyp2.
    f_equal.
    apply subset_eq.
    by do 2 (rewrite projT1_eq_rect; simpl).
    f_equal.
    apply functional_extensionality; move=>[x ltx].
    rewrite H.
    rewrite HeqP1.
    rewrite eq_rect_ap_el; rewrite dep_if_case_false;[cbn; by rewrite projT1_eq_rect|]=> Hyp.
    do 3 f_equal; apply subset_eq_compat; by rewrite projT1_eq_rect.
Qed.

Lemma Q_Prenex_Correct_Lem_4_1
  {M E v B} {r : 'F_FSize}
  {adv : PrenexAdvice FSize [seq x.+1 | x <- E]} :
  PolyVSDenotation FSize (AddModelV FSize M r) B (Uni_Advice_Drop r adv) v
  = PolyVSDenotation FSize M (LiftPolyUni B) adv (ExtendAt0 r v).
Proof.
  induction B; try qauto.
  - destruct n; qauto.
  - simpl.
    dep_if_case (a == projT1 (F_S FSize M i)); auto;
      [rewrite dep_if_case_true|rewrite dep_if_case_false]; auto.
    f_equal. 
    apply functional_extensionality=>t.
    f_equal.
    apply functional_extensionality;move=>[x ltx].
    f_equal; by apply subset_eq_compat.
    f_equal; apply functional_extensionality;move=>[x ltx]; qauto.
  - simpl.
    pose (lnth [seq x.+1 | x <- E]
                (exist (fun n0 : nat => n0 < length [seq x.+1 | x <- E])
                   (` i)
                   (LiftPolyUni_obligation_1 E (PolyEFunVS i p) i p
                      (erefl (PolyEFunVS i p))))) as A.
    assert (A = (lnth E i).+1) as EE.
        unfold A; rewrite lnth_map; simpl; do 2 f_equal.
        destruct i; by apply subset_eq_compat.
    remember (fun x => PolyVSDenotation _ M _ _ _) as P1.
    remember [eta adv (exist _ (` i) _)] as adv'.
    transitivity (obind (eq_rect _ (fun x => (|[x]| -> _) -> _) adv' _ EE) (option_fun (eq_rect _ (fun x => |[x]| -> _) P1 _ EE)));[|by destruct EE].
    simpl.
    rewrite eq_rect_ap_el.
    remember (P1 _) as P1'.
    rewrite HeqP1 in HeqP1'.
    rewrite dep_if_case_true in HeqP1';[cbn; by rewrite projT1_eq_rect|].
    rewrite HeqP1'; clear HeqP1' P1'.
    assert (PolyVSDenotation FSize M (PolyUVarVS 0) adv (ExtendAt0 r v) = Some r) as PM;[auto|rewrite PM;simpl].
    replace (option_fun (fun x => eq_rect _ (fun x => |[x]| -> _) P1 _ EE _)) 
       with (option_fun (fun x => PolyVSDenotation FSize (AddModelV FSize M r) (p x) (Uni_Advice_Drop r adv) v));[|
        f_equal; apply functional_extensionality;move=>[x ltx];
        rewrite eq_rect_ap_el;
        rewrite HeqP1; clear HeqP1 P1; simpl;
        rewrite dep_if_case_false;[by cbn; rewrite projT1_eq_rect|intro Hyp];
        rewrite H;
        do 3 f_equal; apply subset_eq_compat; by rewrite projT1_eq_rect
       ].
    destruct (option_fun _) eqn: PM2; simpl; auto.
    rewrite Heqadv'; clear Heqadv' adv'.
    unfold Uni_Advice_Drop.
    change (?x == exist _ ?y _) with (` x == y).
    remember (Utils.option_fun_obligation_4 _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
    remember (Utils.option_fun_obligation_3 _ _ _ _ _) as DDD1; clear HeqDDD1; simpl in DDD1.
    clear HeqP1 P1.
    rewrite eq_rect_ap_el.
    remember (LiftPolyUni_obligation_1 E _ i p _) as DDD2; clear HeqDDD2; simpl in DDD2.
    assert (Uni_Advice_Drop_obligation_2 E i o =DDD2 ) as e;[apply eq_irrelevance|destruct e].
    f_equal.
    apply functional_extensionality;move=>[[|x] ltx]; simpl.
    unfold ExtendAt0N; simpl.
    rewrite eq_rect_ap_el.
    by rewrite dep_if_case_true;[rewrite projT1_eq_rect|].
    unfold ExtendAt0N; simpl.
    rewrite eq_rect_ap_el.
    rewrite dep_if_case_false;[by rewrite projT1_eq_rect|intro hyp].
    f_equal.
    apply subset_eq_compat.
    by rewrite projT1_eq_rect.
Qed.

Lemma Q_Prenex_Correct_Lem_5
  {M E v o B} {u0 : 'F_FSize} {ltu : u0 < o}
  {adv : {r : 'F_FSize | r < o} -> PrenexAdvice _ E} :
  PropVSDenotation FSize (AddModelV FSize M u0) B (adv (exist _ u0 ltu)) v
  = PropVSDenotation FSize M (LiftPropUni B) (Uni_AdviceF adv) (ExtendAt0 u0 v).
Proof.
  induction B; try qauto.
  simpl.
  f_equal;[|apply Q_Prenex_Correct_Lem_4].
  apply functional_extensionality=> r.
  f_equal;apply Q_Prenex_Correct_Lem_4.
Qed.

Lemma Q_Prenex_Correct_Lem_5_1
  {M E v B} {r : 'F_FSize}
  {adv : PrenexAdvice FSize [seq x.+1 | x <- E]} :
  PropVSDenotation FSize (AddModelV FSize M r) B (Uni_Advice_Drop r adv) v
  = PropVSDenotation FSize M (LiftPropUni B) adv (ExtendAt0 r v).
Proof.
  induction B; try qauto.
  simpl.
  f_equal;[|apply Q_Prenex_Correct_Lem_4_1].
  apply functional_extensionality=> x.
  f_equal;apply Q_Prenex_Correct_Lem_4_1.
Qed.

Lemma Q_Prenex_Correct_Lem_6
  {M E o u ar} {u0 : 'F_FSize} {ltu : u0 < o}
  {adv : {r : 'F_FSize | r < o} -> PrenexAdvice _ E}
  ins out insB outB :
  FunBoundsVS FSize (AddModelV FSize M u0)
    (adv (exist (fun r : 'F_FSize => r < o) u0 ltu)) ins out
    insB outB u =
  FunBoundsVS FSize M (Uni_AdviceF adv) ins out
    (fun x : |[ar]| => LiftPolyUni (insB x))
    (LiftPolyUni outB) (ExtendAt0 u0 u).
Proof.
  move:M ins; induction ar=> M ins.
  simpl.
  unfold InBound.
  by rewrite Q_Prenex_Correct_Lem_4.
  simpl.
  f_equal;[unfold InBound;by rewrite Q_Prenex_Correct_Lem_4|].
  by rewrite IHar.
Qed.

Lemma Q_Prenex_Correct_Lem_6_1
  {M E u ar r}
  {adv : PrenexAdvice FSize [seq x.+1 | x <- E]}
  ins out insB outB :
  FunBoundsVS FSize (AddModelV FSize M r)
    (Uni_Advice_Drop r adv) ins out
    insB outB u =
  FunBoundsVS FSize M adv ins out
    (fun x : |[ar]| => LiftPolyUni (insB x))
    (LiftPolyUni outB) (ExtendAt0 r u).
Proof.
  move:M ins; induction ar=> M ins.
  simpl.
  unfold InBound.
  by rewrite Q_Prenex_Correct_Lem_4_1.
  simpl.
  f_equal;[unfold InBound;by rewrite Q_Prenex_Correct_Lem_4_1|].
  by rewrite IHar.
Qed.

Theorem Q_Prenex_Correct M p :
  QuantifiedFormula_Denote FSize M p <-> PrenexDenotation _ M (Q_Prenex p).
Proof.
  move: M; elim: p.
  - move=> z M; apply ZO_Prenex_Correct.
  - move=> bs y q IH M.
    split=> H.
    + simpl.
      destruct H as [F [FBC H]].
      apply IH in H; clear IH.
      destruct H as [adv [H0 [H1 H2]]].
      exists (AdviceExtend F adv).
      split;[|split].
      * unfold PrenexFormulaCondition in *.
        move=> [u ltu]; simpl.
        pose (eq_rect _ (fun x => |[x]| -> 'F_FSize) u _ (map_length LiftPolyExi _)) as u2.
        assert (forall v, MakeU u2 v = MakeU u v) as u2el.
              move=> v.
              unfold MakeU; simpl; apply functional_extensionality=> i.
              dep_if_case (i < length (uniBounds (Q_Prenex q)));auto;[rewrite dep_if_case_true|rewrite dep_if_case_false];try (rewrite map_length; auto).
              move=> Hyp0; unfold u2; destruct (map_length _ _); simpl; f_equal; by apply subset_eq_compat.
        assert (forall j v,
              InBound FSize
                (AddModelF FSize M (existT _ (length bs) F)) adv (u2 j)
                (lnth (uniBounds (Q_Prenex q)) j) 
                (MakeU u2 v)) as ltu2.
              move=> [j ltj] v.
              assert (j < length [seq LiftPolyExi (a := length bs) (E := Q_Ar q) i | i <- uniBounds (Q_Prenex q)]) as ltj2;[by rewrite map_length|].
              remember (ltu (exist _ j ltj2) v) as ltu'; clear Heqltu'.
              rewrite u2el.
              unfold InBound in *.
              rewrite Q_Prenex_Correct_Lem_0; simpl.
              simpl in ltu'.
              rewrite lnth_map in ltu'; simpl in ltu'.
              remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as ltj'; clear Heqltj'; simpl in ltj'.
              replace ltj' with ltj in ltu';[|apply eq_irrelevance].
              destruct (PolyVSDenotation _ _ _ _ _); auto.
              replace (u2 _) with (u (exist _ j ltj2)); auto.
              unfold u2; simpl.
              destruct (map_length _ _); simpl.
              f_equal; by apply subset_eq_compat.
        remember (H0 (exist _ u2 ltu2)) as H0'; clear HeqH0' H0; simpl in H0'.
        rewrite Q_Prenex_Correct_Lem_1 in H0'.
        by rewrite u2el in H0'.
      * move=> u [i lti] bnds; simpl in *.
        assert (i < length (uniBounds (Q_Prenex q))) as lti2;[clear bnds; by rewrite map_length in lti|].
        assert (forall j, InBound FSize (AddModelF FSize M (existT _ (length bs) F))
            adv (u (` j)) (lnth (uniBounds (Q_Prenex q))
            (exist _ (` j) (PrenexUniversalCondition_obligation_1
            FSize (Q_Ar q) (Q_Prenex q) u (exist _ i lti2) j))) u) as YY.
                move=> j; remember (bnds j) as bnds'; clear Heqbnds' bnds; simpl in *.
                unfold InBound in *.
                rewrite Q_Prenex_Correct_Lem_0; simpl.
                rewrite lnth_map in bnds'; simpl in bnds'.
                remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DD0; clear HeqDD0; simpl in DD0.
                remember (PrenexUniversalCondition_obligation_1 _ _ _ _ _ _) as DD1; clear HeqDD1; simpl in DD1.
                replace DD1 with DD0;[|apply eq_irrelevance].
                destruct (PolyVSDenotation _ _ _ _ _); auto.
        remember (H1 u (exist _ i lti2) YY) as H1'; clear HeqH1' H1 YY; simpl in *.
        rewrite Q_Prenex_Correct_Lem_0 in H1'; simpl in H1'. 
        rewrite lnth_map; simpl.
        remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DD0; clear HeqDD0; simpl in DD0.
        by replace DD0 with lti2;[|apply eq_irrelevance].
      * move=> u [[|i] lti]; simpl in *=> ins out chk; unfold AdviceExtend in chk; simpl in chk.
        --  replace (fun x => ins _) with ins in chk;[
              |apply functional_extensionality;move=>[x ltx];f_equal; by apply subset_eq_compat].
            remember (FBC ins out chk) as FBC'; clear HeqFBC' FBC. 
            remember (eq_rect _ (fun x => |[x]| -> _) ins _ (esym (LiftArgs_length (n := 0) (E := length bs :: Q_Ar q)))) as ins'.
            replace (FunBoundsVS _ _ _ _ _ _ _ _) with
              (FunBoundsVS FSize M (AdviceExtend F adv) ins' out
                (lnth (LiftArgs (E := length bs :: Q_Ar q) 0 bs))
                (PolyTerm_PolyTermVS (length bs) y) (MakeU ins' u)).
            rewrite Q_Prenex_Correct_Lem_3 Heqins'; clear Heqins' ins'; by destruct (esym LiftArgs_length).
            remember (PrenexAddExi_obligation_5 _ _ _ _) as DDD; clear HeqDDD; simpl in DDD.
            replace (MakeU ins' u) with (MakeU ins u);[|
              rewrite Heqins'; clear Heqins' ins'; by destruct (esym LiftArgs_length)].
            transitivity (
              FunBoundsVS FSize M (AdviceExtend F adv)  
                ins' out
                (eq_rect _ (fun x => |[x]| -> _) ((fun x => lnth (LiftArgs 0 bs) (exist _ (` x) (DDD x)))) 
                _ (esym (LiftArgs_length (n := 0) (E := length bs :: Q_Ar q))))
                (PolyTerm_PolyTermVS (length bs) y)
                (MakeU ins u));[f_equal|rewrite Heqins'; clear Heqins' ins'; by destruct (esym (LiftArgs_length))].
            apply functional_extensionality;move=>[x ltx].
            rewrite eq_rect_ap_el; f_equal; apply subset_eq_compat; by rewrite projT1_eq_rect.
        --  replace (adv _ _) with (adv (exist _ i lti) ins) in chk.
            remember (H2 u (exist _ i lti) ins out chk) as H2'; clear HeqH2' H2.
            rewrite Q_Prenex_Correct_Lem_2 in H2'; simpl in H2'.
            remember (FunBoundsVS _ _ _ _ _ _ _ _) as FB1.
            replace (FunBoundsVS _ _ _ _ _ _ _ _) with FB1; auto.
            rewrite HeqFB1; clear HeqFB1 FB1 H2'.
            f_equal. 
            apply functional_extensionality;move=>[x ltx].
            f_equal; simpl.
            remember (PrenexAddExi_obligation_4 _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
            remember (PrenexAddExi_obligation_3 _ _ _ _ _) as DDD1; clear HeqDDD1; simpl in DDD1.
            assert (DDD1 = lti) as EE;[apply eq_irrelevance|destruct EE].
            f_equal; by apply subset_eq_compat.
            f_equal.
            remember (PrenexAddExi_obligation_2 _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
            by replace DDD0 with lti;[|apply eq_irrelevance].
            remember (AdviceExtend_obligation_3 _ _ _ _ _ _) as DDD1; clear HeqDDD1; simpl in DDD1.
            remember (AdviceExtend_obligation_2 _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
            assert (DDD0 = lti) as EE;[apply eq_irrelevance|destruct EE].           
            f_equal.
            apply functional_extensionality;move=>[x ltx]; simpl.
            f_equal; by apply subset_eq_compat.
    + simpl.
      destruct H as [adv [H0 [H1 H2]]].
      simpl in adv.
      exists (adv (exist _ 0 (ltn0Sn (length (Q_Ar q))))).
      simpl; split.
      --  unfold Fun_Bound_Check=> ins out io.
          remember (H2 (fun=> 0%R) (exist _ 0 (ltn0Sn (length (Q_Ar q)))) ins out io) as H; clear HeqH H2; simpl in H. 
          remember (eq_rect _ (fun x => |[x]| -> _) ins _ (esym (LiftArgs_length (n := 0) (E := length bs :: Q_Ar q)))) as ins'.
          replace (FunBoundsVS _ _ _ _ _ _ _ _) with
              (FunBoundsVS FSize M adv ins' out
                (lnth (LiftArgs (E := length bs :: Q_Ar q) 0 bs))
                (PolyTerm_PolyTermVS (length bs) y) (MakeU ins' (fun=> 0%R))) in H.
          rewrite Q_Prenex_Correct_Lem_3 Heqins' in H; clear Heqins' ins'; by destruct (esym LiftArgs_length).
          remember (PrenexAddExi_obligation_5 _ _ _ _) as DDD; clear HeqDDD; simpl in DDD.
          replace (MakeU ins' (fun=> 0%R)) with (MakeU ins (fun=> 0%R));[|
            rewrite Heqins'; clear Heqins' ins'; by destruct (esym LiftArgs_length)].
          transitivity (
            FunBoundsVS FSize M adv
              ins' out
              (eq_rect _ (fun x => |[x]| -> _) ((fun x => lnth (LiftArgs 0 bs) (exist _ (` x) (DDD x)))) 
              _ (esym (LiftArgs_length (n := 0) (E := length bs :: Q_Ar q))))
              (PolyTerm_PolyTermVS (length bs) y)
              (MakeU ins (fun=> 0%R)));[f_equal|rewrite Heqins'; clear Heqins' ins'; by destruct (esym (LiftArgs_length))].
          apply functional_extensionality;move=>[x ltx].
          rewrite eq_rect_ap_el; f_equal; apply subset_eq_compat; by rewrite projT1_eq_rect.
      apply IH.
      exists (AdviceDrop adv).
      assert (AdviceExtend (projT2
              (existT
                (fun newA : nat => ({n : nat | n < newA} -> 'F_FSize) -> option 'F_FSize)
                (length bs)
                (adv (exist _ 0 (ltn0Sn (length (Q_Ar q))))))) 
                (AdviceDrop adv) = adv) as AE.
            unfold AdviceExtend; simpl.
            apply functional_extensionality_dep;move=>[[|x] ltx]; apply functional_extensionality=>F; simpl.
            replace (ltn0Sn (length (Q_Ar q))) with ltx;[|apply eq_irrelevance].
            f_equal; apply functional_extensionality;move=>[z ltz]; simpl.
            f_equal; by apply subset_eq_compat.
            unfold AdviceDrop; simpl.
            remember (AdviceExtend_obligation_3 _ _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
            remember (AdviceExtend_obligation_2 _ _ _ _) as ltx2; clear Heqltx2; simpl in ltx2.
            assert (ltx = ltx2) as EE;[apply eq_irrelevance|destruct EE].
            f_equal; apply functional_extensionality;move=>[z ltz]; simpl.
            f_equal; by apply subset_eq_compat.
      split;[|split].
      * move=>[u ltu]; simpl.
        remember (eq_rect _ (fun x => |[x]| -> _) u _ (esym (map_length (LiftPolyExi (a := length bs)) _))) as u'; simpl in u'.
        assert (forall j v,
                  InBound FSize M adv (u' j)
                    (lnth [seq LiftPolyExi i | i <- uniBounds (Q_Prenex q)] j)
                    (MakeU u' v)) as ltu'.
              move=> [j ltj] v.
              assert (j < length (uniBounds (Q_Prenex q))) as ltj2;[simpl in ltj; by rewrite map_length in ltj|].
              remember (ltu (exist _ j ltj2) v) as ltu2; clear ltu Heqltu2.
              unfold InBound in *.
              rewrite Q_Prenex_Correct_Lem_0 in ltu2.
              rewrite lnth_map; simpl.
              remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
              replace DDD0 with ltj2;[|apply eq_irrelevance]; clear DDD0.
              replace (MakeU u' v) with (MakeU u v).
              rewrite AE in ltu2.
              destruct (PolyVSDenotation _ _ _ _ _); auto.
              rewrite Hequ' eq_rect_ap_el; clear Hequ'.
              destruct (esym (esym _)); simpl.
              replace ltj with ltj2;[auto|apply eq_irrelevance].
              apply functional_extensionality=> x; rewrite Hequ'; unfold MakeU; simpl.
              dep_if_case (x < length (uniBounds (Q_Prenex q)));auto;[rewrite dep_if_case_true|rewrite dep_if_case_false];try (qauto use:map_length).
              move=> Hyp.
              rewrite eq_rect_ap_el; f_equal.
              f_equal; apply subset_eq; by rewrite projT1_eq_rect.
        remember (H0 (exist _ u' ltu')) as H0'; clear H0 HeqH0'; simpl in H0'.
        rewrite Q_Prenex_Correct_Lem_1.
        rewrite AE.
        replace (MakeU u (fun=> 0%R)) with (MakeU u' (fun=> 0%R)); auto.
        apply functional_extensionality=> x; rewrite Hequ'; unfold MakeU; simpl.
        dep_if_case (x < length [seq LiftPolyExi (a := length bs) i | i <- uniBounds (Q_Prenex q)]);auto;[rewrite dep_if_case_true|rewrite dep_if_case_false]; auto.
        by rewrite map_length in H.
        move=> Hyp.
        rewrite eq_rect_ap_el; f_equal.
        f_equal; apply subset_eq; by rewrite projT1_eq_rect.
        by rewrite map_length in H.
      * move=> u [i lti] bnd; simpl in *.
        assert (i < length (uniBounds (PrenexAddExi bs y (Q_Prenex q)))) as lti2;[
              cbn; by rewrite map_length|].
        assert (forall j, InBound FSize M adv (u (` j))
                (lnth [seq LiftPolyExi i | i <- uniBounds (Q_Prenex q)]
                (exist _ (` j) (PrenexUniversalCondition_obligation_1 _ _ _ u
                (exist _ i lti2) j))) u) as YY.
              move=>j; remember (bnd j) as bnd'; clear bnd Heqbnd'.
              unfold InBound in *.
              rewrite Q_Prenex_Correct_Lem_0 in bnd'.
              rewrite AE in bnd'.
              rewrite lnth_map; simpl.
              remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
              remember (PrenexUniversalCondition_obligation_1 _ _ _ _ _ _) as DDD1; clear HeqDDD1; simpl in DDD1.
              by replace DDD0 with DDD1;[clear DDD0|apply eq_irrelevance].
        remember (H1 u (exist _ i lti2) YY) as H1'; clear H1 HeqH1' bnd YY; simpl in H1'.
        unfold InBound in *.
        rewrite Q_Prenex_Correct_Lem_0 AE.
        rewrite lnth_map in H1'; simpl in H1'.
        by replace (Utils.lnth_map_obligation_1 _ _ _ _ (exist _ i lti2)) with lti in H1';[
          |apply eq_irrelevance].
      * move=> u [i lti] ins out io; simpl in *.
        rewrite Q_Prenex_Correct_Lem_2 AE.
        unfold AdviceDrop in io; simpl in io.
        replace (fun x => ins _) with ins in io;[
          |apply functional_extensionality;move=>[x ltx];f_equal].
        remember (H2 u (exist _ i.+1 lti) ins out io) as H2'; clear HeqH2' H2; simpl in H2'.
        remember (FunBoundsVS _ _ _ _ _ _ _) as P; replace (FunBoundsVS _ _ _ _ _ _ _) with P;[destruct P|rewrite HeqP];auto.
        f_equal. 
        apply functional_extensionality;move=>[z ltz]; simpl; f_equal.
        remember (PrenexAddExi_obligation_4 _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
        remember (PrenexAddExi_obligation_3 _ _ _ _ _) as DDD3; clear HeqDDD3; simpl in DDD3.
        assert (DDD3 = lti) as EE;[apply eq_irrelevance|destruct EE].
        f_equal; by apply subset_eq_compat.
        f_equal.
        remember (PrenexAddExi_obligation_2 _ _ _ _) as DDD1; clear HeqDDD1; simpl in DDD1.
        by replace DDD1 with lti;[|apply eq_irrelevance].
  - move=> p q IH M.
    split=> H.
    simpl in H.
    + destruct (Poly_Denote FSize M p) eqn:PM;[|fcrush].
      simpl.
      assert (
        forall r : {r : 'F_FSize | r < o},
          PrenexDenotation FSize (AddModelV _ M (` r)) (Q_Prenex q)) as H';[qauto|clear IH H].
      apply choice in H'; destruct H' as [adv H].
      exists (Uni_AdviceF adv).
      split;[|split].
      * move=>[u ltu]; simpl.
        simpl in u.
        assert (u (exist _ 0 (ltn0Sn (length [seq LiftPolyUni i | i <- uniBounds (Q_Prenex q)]))) < o) as ltuo.
            remember (ltu (exist _ 0 (ltn0Sn _)) (fun _ => 0%R)) as ltu'; clear Heqltu'.
            unfold InBound in ltu'.
            simpl in ltu'.
            rewrite PolyTerm_PolyTermVS_Correct in ltu'.
            by rewrite PM in ltu'.
        destruct (H (exist _ (u (exist _ 0 (ltn0Sn _))) ltuo)) as [H0 _]; simpl in *.
        unfold PrenexFormulaCondition in H0.
        unfold U in H0; simpl in H0.
        remember (eq_rect _ (fun x => |[x]| -> _) (fSeqRest u) _ (map_length LiftPolyUni _)) as u'; simpl in u'.
        assert (forall j v, InBound FSize
                (AddModelV FSize M (u (exist _ 0 (ltn0Sn _))))
                (adv (exist (fun r : 'F_FSize => r < o) _ ltuo))
                (u' j) (lnth (uniBounds (Q_Prenex q)) j) 
                (MakeU u' v)) as ltu'.
            move=> [j ltj] v.
            assert (j.+1 < (length [seq LiftPolyUni i | i <- uniBounds (Q_Prenex q)]).+1) as ltj2;[by rewrite map_length|].
            remember (ltu (exist _ (j.+1) ltj2) v) as ltu'; clear Heqltu' ltu; simpl in *.
            unfold InBound in *.
            rewrite lnth_map in ltu'; simpl in ltu'.
            remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
            replace DDD0 with ltj in ltu';[|apply eq_irrelevance].
            rewrite Q_Prenex_Correct_Lem_4.
            replace (ExtendAt0 _ _) with (MakeU u v).
            destruct (PolyVSDenotation _ _ _ _ _); auto.
            rewrite Hequ'; clear Hequ' u'.
            destruct (map_length LiftPolyUni (uniBounds (Q_Prenex q))); simpl.
            unfold fSeqRest; simpl.
            by replace ltj with ltj2;[|apply eq_irrelevance].
            rewrite Hequ'; clear Hequ' u'.
            destruct (map_length LiftPolyUni (uniBounds (Q_Prenex q))); simpl.
            apply functional_extensionality=>x.
            unfold ExtendAt0; destruct x; auto; simpl.
            unfold MakeU; simpl.
            f_equal; by apply subset_eq_compat.
        remember (H0 (exist _ u' ltu')) as H0'; clear HeqH0' H0; simpl in H0'.
        rewrite Q_Prenex_Correct_Lem_5 in H0'.
        replace (ExtendAt0 _ _) with (MakeU u (fun=> 0%R)) in H0'; auto.
        rewrite Hequ'; clear H0' Hequ' ltu' u'.
        destruct (map_length LiftPolyUni (uniBounds (Q_Prenex q))); simpl.
        apply functional_extensionality;move=>[|i]; cbn; auto.
        f_equal; by apply subset_eq_compat.
      * move=> u [[|i] lti] chk; simpl in *.
        unfold InBound; rewrite PolyTerm_PolyTermVS_Correct PM.
        by exists o.
        rewrite lnth_map; simpl.
        remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as lti2; simpl in lti2;  clear Heqlti2.
        remember (chk (exist _ 0 (ltn0Sn _))) as chk0; clear Heqchk0; simpl in chk0.
        unfold InBound in chk0.
        rewrite PolyTerm_PolyTermVS_Correct PM in chk0.
        destruct (H (exist _ (u 0) chk0)) as [H0 [H1 H2]]; clear H; simpl in *.
        assert (forall j : {n : nat | n < i},
            InBound FSize (AddModelV FSize M (u 0))
              (adv (exist (fun r : 'F_FSize => r < o) (u 0) chk0)) 
              (u (` j).+1)
              (lnth (uniBounds (Q_Prenex q))
                  (exist (fun n : nat => n < length (uniBounds (Q_Prenex q))) 
                    (` j)
                    (PrenexUniversalCondition_obligation_1 FSize 
                        (Q_Ar q) (Q_Prenex q) (fun x : nat => u x.+1)
                        (exist (fun n : nat => n < length (uniBounds (Q_Prenex q)))
                          i lti2) j))) (fun x : nat => u x.+1)) as YY.
                move=>[j ltj].
                remember (chk (exist _ j.+1 ltj)) as chk'; clear Heqchk' chk; simpl in *.
                unfold InBound in *.
                rewrite Q_Prenex_Correct_Lem_4.
                rewrite lnth_map in chk'; simpl in *.
                remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD; clear HeqDDD; simpl in DDD.
                remember (PrenexUniversalCondition_obligation_1 _ _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
                replace DDD0 with DDD;[|apply eq_irrelevance].
                replace (ExtendAt0 (u 0) (fun x : nat => u x.+1)) with u;[auto|].
                apply functional_extensionality;move=>[|x];auto.
        destruct (H1 (fun x => u (x.+1)) (exist _ i lti2) YY) as [o0 H1']; clear H1 YY chk; simpl in H1'.
        exists o0.
        rewrite <- H1'; clear H1'.
        rewrite Q_Prenex_Correct_Lem_4.
        f_equal;apply functional_extensionality;move=>[|x];auto.
      * move=> u [i lti] ins out io.
        unfold Uni_AdviceF in io; simpl in io.
        pose (ins (exist _ 0 (Uni_AdviceF_obligation_1 (Q_Ar q) (exist _ i lti) ins))) as X.
        destruct (X < o) eqn:o0;[|rewrite dep_if_case_false in io;[exact o0|by cbn in io]].
        rewrite dep_if_case_true in io.
        destruct (H (exist _ X o0)) as [_ [_ H2]]; clear H.
        unfold PrenexExiBoundCondition in H2.
        assert (i < length (Q_Ar q)) as lti2;[clear io X o0 H2 ins; by rewrite map_length in lti|].
        assert (lnth [seq x.+1 | x <- Q_Ar q] (exist _ i lti) = (lnth (Q_Ar q) (exist _ i lti2)).+1) as EE;[
          rewrite lnth_map; simpl; do 2 f_equal; by apply subset_eq_compat|].
        assert (adv (exist _ X o0) (exist _ i lti2)
                  (fSeqRest (eq_rect _ (fun x : nat => |[x]| -> _) ins _ EE)) ==
                  Some out) as YY.
          clear H2.
          remember (adv _ _ _) as A1.
          replace (adv _ _ _) with A1; auto.
          rewrite HeqA1; clear io HeqA1 A1.
          unfold X in *; clear X; simpl in *.
          unfold fSeqRest.
          assert (exist (fun n : nat => n < length (Q_Ar q)) i (Uni_AdviceF_obligation_2 o (Q_Ar q) (exist _ i lti) ins o0) = exist _ i lti2);[
            by apply subset_eq_compat|].
          destruct H.
          f_equal.
          apply functional_extensionality;move=>[x ltx]; simpl.
          rewrite eq_rect_ap_el; f_equal.
          apply subset_eq; by rewrite projT1_eq_rect.          
        remember (H2 u (exist _ i lti2) (fSeqRest (eq_rect _ (fun x => |[x]| -> _) ins _ EE)) out YY) as H2'; clear HeqH2' H2 YY; simpl in H2'.
        rewrite Q_Prenex_Correct_Lem_6 in H2'.
        simpl in *.
        remember (eq_rect _ (fun x => |[x]| -> _) ins _ (lnth_map)) as ins'; simpl in ins'.
        remember (fun x => ExtendAt0N _ _ _) as insB.
        remember (eq_rect _ (fun x => |[x]| -> _) insB _ (lnth_map)) as insB'; simpl in insB'.
        remember (LiftPolyUni (exiBounds (Q_Prenex q) (exist _ i (PrenexAddUni_obligation_1 (Q_Ar q) (exist _ i lti)))).2) as outB.
        replace (FunBoundsVS _ _ _ _ _ _ _ _) 
          with (FunBoundsVS FSize M (Uni_AdviceF adv) ins' out insB' outB (MakeU ins u));[|
          remember (MakeU ins u) as u'; clear Hequ';
          remember (fun a ins insB => FunBoundsVS (a := a) FSize M (Uni_AdviceF adv) ins out insB outB u') as AA;
          transitivity (AA _ ins' insB');[by rewrite HeqAA|];
          transitivity (AA _ ins insB);[|by rewrite HeqAA];
          clear HeqAA;
          rewrite Heqins' HeqinsB'; clear Heqins' HeqinsB' ins' insB' HeqinsB H2' EE lti2 io o0 X HeqoutB H2';
          simpl;
          assert ((lnth (Q_Ar q) (exist _ i
                    (Utils.lnth_map_obligation_1 nat nat [eta succn] (Q_Ar q)
                      (exist _ i lti)))).+1 = lnth [seq x.+1 | x <- Q_Ar q]
                  (exist _ i lti)) as E;[by rewrite lnth_map|];
          remember lnth_map as E3; clear HeqE3;
          destruct E; f_equal;[
          apply functional_extensionality;move=>[x ltx]; rewrite eq_rect_ap_el; f_equal;
          apply subset_eq; by rewrite projT1_eq_rect|
          apply functional_extensionality;move=>[x ltx]; rewrite eq_rect_ap_el; f_equal;
          apply subset_eq; by rewrite projT1_eq_rect]].
        simpl.
        replace (InBound _ _ _ _ _ _) with true; simpl.
        remember (FunBoundsVS _ _ _ _ _ _ _ _) as FV; replace (FunBoundsVS _ _ _ _ _ _ _ _) with FV; auto.
        rewrite HeqFV; clear H2' HeqFV FV.
        remember (FunBoundsVS_obligation_4 _  _ _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
        remember (FunBoundsVS_obligation_3 _  _ _ _ _ _ _) as DDD1; clear HeqDDD1; simpl in DDD1.
        assert (Utils.lnth_map_obligation_1 nat nat
                  [eta succn] (Q_Ar q)
                  (exist
                      (fun n0 : nat =>
                      n0 < length [seq x.+1 | x <- Q_Ar q])
                      i lti) = lti2) as e;[apply eq_irrelevance|destruct e].
        f_equal.
        apply functional_extensionality;move=>[x ltx].
        rewrite Heqins'; clear Heqins' HeqinsB' HeqinsB ins' insB' insB; simpl.
        unfold fSeqRest; simpl.
        do 2 rewrite eq_rect_ap_el; f_equal.
        apply subset_eq; by do 2 rewrite projT1_eq_rect.
        apply functional_extensionality;move=>[x ltx].
        rewrite HeqinsB' HeqinsB; clear Heqins' HeqinsB' HeqinsB ins' insB' insB; simpl.
        rewrite eq_rect_ap_el.
        unfold ExtendAt0N; rewrite dep_if_case_false;[cbn; by rewrite projT1_eq_rect|intro Hyp].
        f_equal; simpl.
        remember (DDD0 _) as DDD3; clear HeqDDD3; simpl in DDD3; clear DDD0 DDD1.
        remember (Utils.ExtendAt0N_obligation_2 _ _ _) as DDD0; clear HeqDDD0 Hyp; simpl in DDD0.
        assert (Utils.lnth_map_obligation_1 nat nat [eta succn] (Q_Ar q) (exist _ i lti) 
                = PrenexAddUni_obligation_1 (Q_Ar q) (exist _ i lti)) as e;[apply eq_irrelevance|destruct e].
        f_equal.
        apply subset_eq_compat; by rewrite projT1_eq_rect.
        f_equal.
        clear Heqins' ins' HeqinsB' insB' HeqinsB insB.
        remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD3; clear HeqDDD3; simpl in DDD3.
        remember (PrenexAddUni_obligation_1  _ _) as DDD4; clear HeqDDD4 DDD1 DDD0 EE; simpl in DDD4.
        replace DDD3 with DDD4;[auto|apply eq_irrelevance].
        apply functional_extensionality;move=>[|x]; unfold ExtendAt0, MakeU; simpl.
        unfold X.
        rewrite dep_if_case_true;[by rewrite lnth_map|intro Hyp]; auto.
        f_equal; by apply subset_eq_compat.
        dep_if_case (x < lnth (Q_Ar q) (exist _ i
          (Utils.lnth_map_obligation_1 nat nat [eta succn]
              (Q_Ar q) (exist _ i lti)))); auto.
        rewrite dep_if_case_true;[by rewrite lnth_map|intro Hyp].
        unfold fSeqRest; simpl.
        rewrite eq_rect_ap_el.
        f_equal; apply subset_eq; by rewrite projT1_eq_rect.
        rewrite dep_if_case_false;[by rewrite lnth_map|].
        by rewrite lnth_map.
        simpl.
        unfold InBound.
        remember (PolyVSDenotation _ _ _ _ _) as P.
        replace P with (Some o).
        rewrite Heqins'; clear Heqins' ins'.
        rewrite eq_rect_ap_el.
        replace (ins _) with X; auto.
        unfold X; f_equal.
        apply subset_eq; by rewrite projT1_eq_rect.
        rewrite <- PM.
        rewrite HeqP; clear HeqP P.
        rewrite HeqinsB' HeqinsB; clear HeqinsB' insB' HeqinsB insB.
        rewrite eq_rect_ap_el.
        unfold ExtendAt0N at 1; simpl.
        change (exist _ ?x _ == exist _ ?y _) with (x == y).
        rewrite dep_if_case_true;[by rewrite projT1_eq_rect|].
        by rewrite PolyTerm_PolyTermVS_Correct.
    + simpl in *.
      destruct H as [adv [H0 [H1 H2]]].
      destruct (H1 (fun _ => 0%R) (exist _ 0 (ltn0Sn _)) emptyTuple) as [o PM].
      simpl in PM; rewrite PolyTerm_PolyTermVS_Correct in PM.
      rewrite PM=> r rb.
      apply IH; clear IH.
      exists (Uni_Advice_Drop r adv).
      split;[|split].
      * move=>[u ltu]; simpl.
        unfold PrenexFormulaCondition, U in H0; simpl in H0.
        remember (ExtendAt0N r (eq_rect _ (fun x => |[x]| -> _) u _ (esym (map_length _ _)) 
                  : |[length [seq LiftPolyUni i | i <- _]]| -> 'F_FSize)) as u'.
        assert (forall j v,
             InBound FSize M adv (u' j)
               (match ` j as n' return (n' = ` j -> PolyTermVS) with
                | 0 => fun=> PolyTerm_PolyTermVS 0 p
                | n.+1 =>
                    fun Heq_n : n.+1 = ` j =>
                    lnth [seq LiftPolyUni i | i <- uniBounds (Q_Prenex q)]
                      (exist _ n
                         (Utils.lnth_obligation_1 PolyTermVS
                            (PolyTerm_PolyTermVS 0 p)
                            [seq LiftPolyUni i | i <- uniBounds (Q_Prenex q)]
                            j n Heq_n))
                end (erefl (` j))) (MakeU u' v)) as ltu'.
              move=>[[|j] ltj] v; simpl.
              rewrite Hequ'; unfold ExtendAt0N at 1; simpl.
              unfold InBound.
              by rewrite PolyTerm_PolyTermVS_Correct PM.
              assert (j < length (uniBounds (Q_Prenex q))) as ltj2;[by rewrite map_length in ltj|].
              remember (ltu (exist _ j ltj2) v) as ltu'; clear Heqltu' ltu.
              unfold InBound in *.
              rewrite Q_Prenex_Correct_Lem_4_1 in ltu'.
              rewrite lnth_map; simpl.
              replace (Utils.lnth_map_obligation_1 _ _ _ _ (exist _ j ltj)) with ltj2;[|apply eq_irrelevance].
              replace (MakeU u' v) with (ExtendAt0 r (MakeU u v)).
              destruct (PolyVSDenotation _ _ _ _ _); auto.
              rewrite Hequ'; clear Hequ' u'.
              unfold ExtendAt0N; simpl.
              rewrite eq_rect_ap_el.
              destruct (esym _); simpl.
              by replace (Utils.ExtendAt0N_obligation_2 _ _
                    (erefl (exist (fun n0 : nat => n0 < (length [seq LiftPolyUni i | i <- uniBounds (Q_Prenex q)]).+1) j.+1 ltj ==
                            exist (fun x : nat => x < (length [seq LiftPolyUni i | i <- uniBounds (Q_Prenex q)]).+1)0 is_true_true))) with ltj2;[|apply eq_irrelevance].
              rewrite Hequ'; clear Hequ' u'.
              apply functional_extensionality;move=>[|x]; unfold MakeU, ExtendAt0, ExtendAt0N; simpl; auto.
              dep_if_case (x < length (uniBounds (Q_Prenex q))); auto;[rewrite dep_if_case_true|rewrite dep_if_case_false].
              by rewrite map_length.
              intro hyp.
              rewrite eq_rect_ap_el; f_equal.
              destruct (esym _); by apply subset_eq_compat.
              by rewrite map_length.
              by rewrite map_length.
        remember (H0 (exist _ u' ltu')) as H0'; clear H0 HeqH0'; simpl in H0'.
        rewrite Q_Prenex_Correct_Lem_5_1.
        replace (ExtendAt0 r (MakeU u (fun=> 0%R))) with (MakeU u' (fun=> 0%R)); auto.
        rewrite Hequ'; clear ltu' H0' Hequ' u'.
        apply functional_extensionality;move=>[|x]; unfold MakeU, ExtendAt0, ExtendAt0N; simpl; auto.
        dep_if_case (x.+1 < (length [seq LiftPolyUni i | i <- uniBounds (Q_Prenex q)]).+1); auto;[rewrite dep_if_case_true|rewrite dep_if_case_false]; auto.
        by rewrite map_length in H.
        intro hyp.
        rewrite eq_rect_ap_el; f_equal.
        destruct (esym _); by apply subset_eq_compat.
        by rewrite map_length in H.
      * move=> u [i lti] bnd; simpl in *.
        unfold PrenexUniversalCondition in H1.
        assert (i.+1 < length (uniBounds (PrenexAddUni p (Q_Prenex q)))) as lti2;[
              simpl; by rewrite map_length|].
        assert (forall j,
                    InBound FSize M adv (ExtendAt0 r u (` j))
                      (match ` j as n' return (n' = ` j -> PolyTermVS) with
                        | 0 => fun=> PolyTerm_PolyTermVS 0 p
                        | n.+1 =>
                            fun Heq_n : n.+1 = ` j =>
                            lnth [seq LiftPolyUni i | i <- uniBounds (Q_Prenex q)]
                              (exist _ n
                                (eq_ind n.+1
                                    (fun n0 : nat =>
                                    n0 <
                                    (length
                                        [seq LiftPolyUni i | i <- uniBounds (Q_Prenex q)]).+1 ->
                                    n <
                                    length
                                      [seq LiftPolyUni i | i <- uniBounds (Q_Prenex q)])
                                    id (` j) Heq_n
                                    (PrenexUniversalCondition_obligation_1 FSize
                                      [seq x.+1 | x <- Q_Ar q]
                                      (PrenexAddUni p (Q_Prenex q)) 
                                      (ExtendAt0 r u)
                                      (exist _ i.+1 lti2) j)))
                        end (erefl (` j))) (ExtendAt0 r u)) as YY.
              move=>[[|j] ltj].
              simpl.
              by unfold InBound; rewrite PolyTerm_PolyTermVS_Correct PM.
              unfold ExtendAt0 at 1; simpl.
              rewrite lnth_map; simpl.
              remember (bnd (exist _ j ltj)) as bnd'; clear bnd Heqbnd'; simpl in bnd'.
              unfold InBound in *.
              rewrite Q_Prenex_Correct_Lem_4_1 in bnd'.
              remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
              remember (PrenexUniversalCondition_obligation_1 _ _ _ _ _ _) as DDD1; clear HeqDDD1; simpl in DDD1.
              by replace DDD0 with DDD1;[clear DDD0|apply eq_irrelevance].
        destruct (H1 (ExtendAt0 r u) (exist _ i.+1 lti2) YY) as [o0 H1']; clear H1 bnd YY; simpl in H1'.
        exists o0.
        rewrite Q_Prenex_Correct_Lem_4_1.
        rewrite lnth_map in H1'; simpl in H1'.
        remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
        by replace DDD0 with lti in H1';[|apply eq_irrelevance].
      * move=> u [i lti] ins out io; simpl in *.
        unfold PrenexExiBoundCondition in H2.
        assert (i < length [seq x.+1 | x <- Q_Ar q]) as lti2;[by rewrite map_length|].
        assert ((lnth (Q_Ar q) (exist _ i lti)).+1
                = lnth [seq x.+1 | x <- Q_Ar q] (exist _ i lti2)) as E;[rewrite lnth_map;do 2 f_equal; by apply subset_eq_compat|].
        remember (eq_rect _ (fun x => |[x]| -> _) (ExtendAt0N r ins) _ E) as ins'.
        assert (adv (exist (fun n : nat => n < length [seq x.+1 | x <- Q_Ar q]) i lti2) ins' == Some out) as YY.
            rewrite Heqins'; clear Heqins' ins' H0 H1 H2.
            unfold Uni_Advice_Drop in io; simpl in io.
            assert ((Uni_Advice_Drop_obligation_2 (Q_Ar q)
             (exist (fun n : nat => n < length (Q_Ar q)) i lti) ins) = lti2) as e;[apply eq_irrelevance|destruct e].
            remember (adv _ _) as A1; replace (adv _ _) with A1; auto; rewrite HeqA1; clear io HeqA1 A1.
            f_equal.
            apply functional_extensionality;move=>[x ltx]; simpl; rewrite eq_rect_ap_el.
            f_equal.
            apply subset_eq; by rewrite projT1_eq_rect.
        remember (H2 u (exist _ i lti2) ins' out YY) as H2'; clear HeqH2' H2 YY io; simpl in H2'.
        rewrite Q_Prenex_Correct_Lem_6_1.
        replace (ExtendAt0 r (MakeU ins u)) with (MakeU ins' u).
        remember (FunBoundsVS _ _ _ _ _ _ _ _) as P; replace (FunBoundsVS _ _ _ _ _ _ _ _) with P;[auto|rewrite HeqP; clear HeqP P H2'];auto.
        simpl.
        remember (fun x => ExtendAt0N _ _ _) as insB'.
        transitivity (
          FunBoundsVS FSize M adv (eq_rect _ (fun x => |[x]| -> _) ins' _ (esym E)) out 
            (eq_rect _ (fun x => |[x]| -> _) insB' _ (esym E))            
            (LiftPolyUni
              (exiBounds (Q_Prenex q)
                  (exist (fun n : nat => n < length (Q_Ar q)) i
                    (PrenexAddUni_obligation_1 (Q_Ar q)
                        (exist (fun n : nat => n < length [seq x.+1 | x <- Q_Ar q]) i
                          lti2)))).2) (MakeU ins' u) );[by destruct (esym E)|].
        simpl.
        replace (InBound _ _ _ _ _ _) with true; simpl.
        assert (PrenexAddUni_obligation_1 (Q_Ar q) (exist _ i lti2) = lti) as e;[apply eq_irrelevance|destruct e].
        f_equal.
        apply functional_extensionality;move=>[x ltx]; simpl.
        rewrite eq_rect_ap_el.
        rewrite Heqins'; clear Heqins' ins'.
        unfold InBound.
        rewrite eq_rect_ap_el.
        destruct (esym (esym E)); simpl.
        unfold ExtendAt0N; rewrite dep_if_case_false.
        change (?x == exist _ ?y _) with (` x == y).
        by rewrite projT1_eq_rect.
        intro hyp.
        f_equal; apply subset_eq_compat.
        by rewrite projT1_eq_rect.
        apply functional_extensionality;move=>[x ltx]; simpl.
        rewrite eq_rect_ap_el.
        rewrite HeqinsB'; clear HeqinsB' insB'.
        unfold ExtendAt0N; rewrite dep_if_case_false.
        change (exist _ ?x _ == exist _ ?y _) with (x == y).
        by rewrite projT1_eq_rect.
        intro hyp.
        do 2 f_equal; simpl.
        apply subset_eq_compat.
        by rewrite projT1_eq_rect.
        unfold InBound.
        rewrite eq_rect_ap_el.
        rewrite HeqinsB'; clear HeqinsB' insB'.
        unfold ExtendAt0N; rewrite dep_if_case_true.
        change (exist _ ?x _ == exist _ ?y _) with (x == y).
        by rewrite projT1_eq_rect.
        rewrite PolyTerm_PolyTermVS_Correct PM.
        rewrite eq_rect_ap_el.
        rewrite Heqins'; clear Heqins' ins'.
        rewrite eq_rect_ap_el.
        unfold ExtendAt0N; rewrite dep_if_case_true; auto.
        change (?x == exist _ ?y _) with (` x == y).
        by do 2 rewrite projT1_eq_rect.
        rewrite Heqins'; clear H2' Heqins' ins'.
        unfold MakeU, ExtendAt0, ExtendAt0N.
        apply functional_extensionality;move=>[|x].
        rewrite dep_if_case_true;[by rewrite lnth_map|intro hyp; simpl].
        rewrite eq_rect_ap_el.
        rewrite dep_if_case_true; auto.
        change (?x == exist _ ?y _) with (` x == y).
        by rewrite projT1_eq_rect.
        dep_if_case (x.+1 < lnth [seq x0.+1 | x0 <- Q_Ar q] (exist _ i lti2));auto;[rewrite dep_if_case_true|rewrite dep_if_case_false].
        rewrite lnth_map in H; simpl in *.
        remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD; clear HeqDDD; simpl in DDD.
        replace lti with DDD;[auto|apply eq_irrelevance].
        intro hyp.
        rewrite eq_rect_ap_el.
        rewrite dep_if_case_false.
        change (?x == exist _ ?y _) with (` x == y).
        by rewrite projT1_eq_rect.
        intro hyp2.
        f_equal.
        apply subset_eq_compat.
        by rewrite projT1_eq_rect.
        rewrite lnth_map in H; simpl in *.
        remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DDD; clear HeqDDD; simpl in DDD.
        replace lti with DDD;[auto|apply eq_irrelevance].
        f_equal.
        rewrite lnth_map; simpl.
        by replace (Utils.lnth_map_obligation_1 _ _ _ _ (exist _ i lti2)) with lti;[|apply eq_irrelevance].
Qed.

End PrenexTranslation.
