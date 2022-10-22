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

Inductive ZerothOrderFormulaVS {E} : Type :=
| ZONotVS : ZerothOrderFormulaVS -> ZerothOrderFormulaVS
| ZOAndVS : ZerothOrderFormulaVS -> ZerothOrderFormulaVS -> ZerothOrderFormulaVS
| ZOOrVS : ZerothOrderFormulaVS -> ZerothOrderFormulaVS -> ZerothOrderFormulaVS
| ZOImpVS : ZerothOrderFormulaVS -> ZerothOrderFormulaVS -> ZerothOrderFormulaVS
| ZOEqVS : @PolyTermVS E -> @PolyTermVS E -> ZerothOrderFormulaVS.

Record Prenex {E} : Type :=
  mkPrenex {
    uniBounds : seq (@PolyTermVS E);
    exiBounds : forall i, ((|[lnth E i]| -> (@PolyTermVS E)) * (@PolyTermVS E));
    formula : @ZerothOrderFormulaVS E
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

Fixpoint PrenexZODenotation {E} (M : @Sigma11Model FSize)
  (f : @ZerothOrderFormulaVS E)
  (adv : PrenexAdvice E) :
  (nat -> 'F_FSize) -> option bool :=
  match f with
  | ZONotVS f => fun u => 
    let d := PrenexZODenotation M f adv u in
    obind (fun d => Some (negb d)) d
  | ZOAndVS f1 f2 => fun u => 
    let d1 := PrenexZODenotation M f1 adv u in
    let d2 := PrenexZODenotation M f2 adv u in
    obind (fun r1 => obind (fun r2 => Some (r1 && r2)) d2) d1
  | ZOOrVS f1 f2 => fun u => 
    let d1 := PrenexZODenotation M f1 adv u in
    let d2 := PrenexZODenotation M f2 adv u in
    obind (fun r1 => obind (fun r2 => Some (r1 || r2)) d2) d1
  | ZOImpVS f1 f2 => fun u => 
    let d1 := PrenexZODenotation M f1 adv u in
    let d2 := PrenexZODenotation M f2 adv u in
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
  PrenexZODenotation M (formula f) adv (MakeU u (fun _ => 0%R)) == Some true.

(* Program Definition PrenexUniversalCondition {E} (M : @Sigma11Model FSize)
  (f : Prenex) (adv : PrenexAdvice E) : Prop :=
  forall (u : nat -> 'F_FSize) (i : |[length (uniBounds f)]|),
    (forall j : |[i]|, InBound M adv (u j) (lnth (uniBounds f) j) u) ->
    InBound M adv (u i) (lnth (uniBounds f) i) u.
Next Obligation. strivial use: ltn_trans. Qed. *)

(* Program Fixpoint FunBoundsVS {E} (M : @Sigma11Model FSize)
  (adv : PrenexAdvice E) {a}
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
        @FunBoundsVS E M adv n (fun x => ins (x.+1)) out (fun x => insB (x.+1)) outB u
    end
  end. *)

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
    (* PrenexUniversalCondition M f a /\ *)
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

Fixpoint ZerothOrder_ZerothOrderVS {E} (p : ZerothOrderFormula) : @ZerothOrderFormulaVS E :=
  match p with
  | ZONot m => ZONotVS (ZerothOrder_ZerothOrderVS m)
  | ZOAnd r1 r2 => ZOAndVS (ZerothOrder_ZerothOrderVS r1) (ZerothOrder_ZerothOrderVS r2)
  | ZOOr r1 r2 => ZOOrVS (ZerothOrder_ZerothOrderVS r1) (ZerothOrder_ZerothOrderVS r2)
  | ZOImp r1 r2 => ZOImpVS (ZerothOrder_ZerothOrderVS r1) (ZerothOrder_ZerothOrderVS r2)
  | ZOEq a b => ZOEqVS (PolyTerm_PolyTermVS 0 a) (PolyTerm_PolyTermVS 0 b)
  end.

Theorem ZerothOrder_ZerothOrderVS_Correct M p {A} (a : PrenexAdvice _ A) t :
  PrenexZODenotation FSize M (ZerothOrder_ZerothOrderVS p) a t = ZerothOrder_Denote _ M p.
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

(* Lemma ZO_Prenex_Correct_PrenexUniversalCondition
  M f : forall a, PrenexUniversalCondition FSize M (ZO_Prenex f) a.
Proof. move=> a u [i lti]; fcrush. Qed. *)

Lemma ZO_Prenex_Correct_PrenexExiBoundCondition
  M f : forall a, PrenexExiBoundCondition FSize M (ZO_Prenex f) a.
Proof. move=> a u [i lti]; fcrush. Qed.

Theorem ZO_Prenex_Correct M p :
  ZerothOrder_Denote FSize M p == Some true <-> PrenexDenotation _ M (ZO_Prenex p).
Proof.
  qauto use: ZO_Prenex_Correct_PrenexFormulaCondition
           (* , ZO_Prenex_Correct_PrenexUniversalCondition *)
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
  (p : @ZerothOrderFormulaVS E) : @ZerothOrderFormulaVS (a :: E) :=
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
  (f : @ZerothOrderFormulaVS E):
  @ZerothOrderFormulaVS (map (fun x => x.+1) E) :=
  match f with
  | ZONotVS f => ZONotVS (LiftPropUni f)
  | ZOAndVS f1 f2 => ZOAndVS (LiftPropUni f1) (LiftPropUni f2)
  | ZOOrVS f1 f2 => ZOOrVS (LiftPropUni f1) (LiftPropUni f2)
  | ZOImpVS f1 f2 => ZOImpVS (LiftPropUni f1) (LiftPropUni f2)
  | ZOEqVS r1 r2 => ZOEqVS (LiftPolyUni r1) (LiftPolyUni r2)
  end.

Fixpoint LiftExiArgs {E} n (bs : seq PolyTerm) : seq (@PolyTermVS E) :=
  match bs with
  | [::] => [::]
  | x :: xs => PolyTerm_PolyTermVS n x :: LiftExiArgs n.+1 xs
  end.

Theorem LiftExiArgs_length {E n bs} : length (@LiftExiArgs E n bs) = length bs.
Proof. move:n; induction bs; qauto. Qed.

Program Definition PrenexAddExi {E} 
  (bs : seq PolyTerm) (y : PolyTerm) (q : @Prenex E) : @Prenex (length bs :: E) :=
  {| uniBounds := map LiftPolyExi (uniBounds q)
   ; exiBounds := fun i => (
      if i == 0 as B return i == 0 = B -> (|[lnth (length bs :: E) i]| -> @PolyTermVS (length bs :: E)) * @PolyTermVS (length bs :: E)
      then fun _ => (lnth (LiftExiArgs 0 bs), PolyTerm_PolyTermVS (length bs) y)
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
Next Obligation. rewrite LiftExiArgs_length. by destruct i;[|fcrush]. Qed.

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
  PrenexZODenotation (E := E) _ (AddModelF _ M f) p adv u
  = PrenexZODenotation FSize M (LiftPropExi p) (AdviceExtend (projT2 f) adv) u.
Proof.
  elim: p; try qauto.
  move=> p1 p2.
  simpl.
  by do 2 rewrite Q_Prenex_Correct_Lem_0.
Qed.

Theorem Q_Prenex_Correct_Lem_2 (M: Sigma11Model FSize) 
  {A} (adv: PrenexAdvice _ A)
  ar u ins out insB outB F :
FunBoundsVS FSize (AddModelF FSize M F) adv ins out insB outB u = 
FunBoundsVS FSize M (AdviceExtend (projT2 F) adv) (a := ar) ins out (fun x => LiftPolyExi (insB x)) (LiftPolyExi outB) u.
Proof.
  move:M ins; induction ar=> M ins; simpl;[by unfold InBound; rewrite <- Q_Prenex_Correct_Lem_0|].
  by f_equal;[unfold InBound; rewrite <- Q_Prenex_Correct_Lem_0|rewrite <- IHar].
Qed.

Theorem Q_Prenex_Correct_Lem_3_0 {n} (M: Sigma11Model FSize) 
  {A} (adv: PrenexAdvice _ A)
  (bs: seq PolyTerm) (y: PolyTerm) u (ins : |[n + length (LiftExiArgs n bs)]| -> _) out
  : FunBoundsVS FSize M adv (fSeqBack ins) out (lnth (LiftExiArgs n bs)) (PolyTerm_PolyTermVS (length bs + n) y) (MakeU ins u) = 
    FunBounds FSize {| V_F := fun x => if x < n then (MakeU ins u) (n.-1 - x) else V_F FSize M (x - n); F_S := F_S FSize M |} (fSeqBack ins) out (eq_rect _ (fun x => |[x]| -> _) (lnth bs) _ (esym LiftExiArgs_length)) y.
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
  replace (fun x : {n0 : nat | n0 < length (LiftExiArgs n.+1 bs)} =>
   lnth (LiftExiArgs n.+1 bs) (exist _ (` x) _)) with (lnth (@LiftExiArgs A n.+1 bs));[|
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

Theorem Q_Prenex_Correct_Lem_3 (M: Sigma11Model FSize) 
  {A} (adv: PrenexAdvice _ A)
  (bs: seq PolyTerm) (y: PolyTerm) u ins out
  : FunBoundsVS FSize M adv ins out (lnth (LiftExiArgs 0 bs)) (PolyTerm_PolyTermVS (length bs) y) (MakeU ins u) = 
    FunBounds FSize M ins out (eq_rect _ (fun x => |[x]| -> _) (lnth bs) _ (esym LiftExiArgs_length)) y.
Proof.
  remember (@Q_Prenex_Correct_Lem_3_0 0 M _ adv bs y u ins out) as L; clear HeqL.
  assert (ins = fSeqBack (ins : |[0 + _]| -> _)) as insb.
    unfold fSeqBack.
    apply functional_extensionality;move=> [x ltx].
    f_equal; apply subset_eq_compat; by rewrite ZeroCanc.
  replace ins with (fSeqBack (ins : |[0 + _]| -> _)) at 1.
  replace (PolyTerm_PolyTermVS (length bs) y) with (PolyTerm_PolyTermVS (E := A) (length bs + 0) y);[|by rewrite ZeroCanc].
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

Lemma Q_Prenex_Correct_Lem_5
  {M E v o B} {u0 : 'F_FSize} {ltu : u0 < o}
  {adv : {r : 'F_FSize | r < o} -> PrenexAdvice _ E} :
  PrenexZODenotation FSize (AddModelV FSize M u0) B (adv (exist _ u0 ltu)) v
  = PrenexZODenotation FSize M (LiftPropUni B) (Uni_AdviceF adv) (ExtendAt0 u0 v).
Proof.
  induction B; try qauto.
  simpl.
  f_equal;[|apply Q_Prenex_Correct_Lem_4].
  apply functional_extensionality=> r.
  f_equal;apply Q_Prenex_Correct_Lem_4.
Qed.

Theorem Q_Prenex_Correct_Lem_6
  {M E o p u ar b} {u0 : 'F_FSize} {ltu : u0 < o}
  {adv : {r : 'F_FSize | r < o} -> PrenexAdvice _ E}
  ins out insB outB :
PolyVSDenotation FSize M p (Uni_AdviceF adv) u = Some b ->
u0 < b ->
FunBoundsVS FSize (AddModelV FSize M u0) (adv (exist _ u0 ltu)) (a := ar) ins out insB outB u = 
FunBoundsVS FSize M (Uni_AdviceF adv) (ExtendAt0N u0 ins) out 
            (ExtendAt0N p (fun x => LiftPolyUni (insB x))) (LiftPolyUni outB) u.
Proof.
  simpl=> e bn.
  rewrite (dep_option_match_some b); auto.
  replace (ExtendAt0N u0 ins (exist (fun n : nat => n < ar.+1) 0 is_true_true) < b) with true; auto; simpl.
  unfold ExtendAt0N; simpl.
  clear e.
  move:M ins; induction ar=> M ins; simpl=> hyp.
  rewrite Q_Prenex_Correct_Lem_4.

PolyVSDenotation FSize (AddModelV FSize M u0) B adv u = 
PolyVSDenotation FSize M B adv (ExtendAt0 u0 u)

PolyVSDenotation FSize M (LiftPolyUni outB) (Uni_AdviceF adv) (ExtendAt0 u0 u)
PolyVSDenotation FSize (AddModelV FSize M u0) (LiftPolyUni outB) (Uni_AdviceF adv) u

PolyVSDenotation FSize (AddModelV FSize M u0) B (Uni_AdviceF adv) u
PolyVSDenotation FSize M B adv (ExtendAt0 u0 u)

  rewrite Q_Prenex_Correct_Lem_4.

  PolyVSDenotation FSize (AddModelV FSize M u0) B (adv (exist _ u0 ltu)) v
  = PolyVSDenotation FSize M (LiftPolyUni B) (Uni_AdviceF adv) (ExtendAt0 u0 v).

  r
  remember (Utils.ExtendAt0N_obligation_2 _ _ _) as DDD.
  destruct (PolyVSDenotation FSize M p (Uni_AdviceF adv) u);[simpl|fcrush].
  rewrite e.
  destruct e.
  intro e.
  rewrite Q_Prenex_Correct_Lem_4.
  
  unfold ExtendAt0N; simpl.
  remember (FunBoundsVS_obligation_4 _ _ _ adv _ _ _ _ _ _) as DD0; clear HeqDD0; simpl in DD0;
  remember (FunBoundsVS_obligation_5 _ _ _ adv _ _ _ _ _ _) as DD1; clear HeqDD1; simpl in DD1;
  remember (FunBoundsVS_obligation_4 _ _ _ _ _ _ _ _ _ _) as DD2; clear HeqDD2; simpl in DD2;
  remember (FunBoundsVS_obligation_5 _ _ _ _ _ _ _ _ _ _) as DD3; clear HeqDD3; simpl in DD3.
  assert (PolyVSDenotation FSize
    (AddModelF FSize M F)
    (insB (exist (fun n : nat => n < ar.+1) 0 is_true_true)) adv u =
    (PolyVSDenotation FSize M
    (LiftPolyExi (insB (exist (fun n : nat => n < ar.+1) 0 is_true_true)))
    (AdviceExtend (projT2 F) adv) u));[by rewrite Q_Prenex_Correct_Lem_0|].
  destruct (PolyVSDenotation _ _ _ _ _);destruct (PolyVSDenotation _ _ _ _ _);[|fcrush|fcrush|auto].
  f_equal;[qauto|].
  rewrite <- IHar.
  f_equal; apply functional_extensionality=>x;f_equal;by apply subset_eq_compat.


FunBoundsVS FSize (AddModelV FSize M X)
        (adv (exist (fun r : 'F_FSize => r < o) X o0))
        (fSeqRest
           (eq_rect
              (lnth [seq x.+1 | x <- Q_Ar q]
                 (exist (fun n : nat => n < length [seq x.+1 | x <- Q_Ar q])
                    i lti)) (fun x : nat => {n : nat | n < x} -> 'F_FSize)
              ins
              (lnth (Q_Ar q)
                 (exist (fun n : nat => n < length (Q_Ar q)) i lti2)).+1 EE))
        out [eta insB] outB u == is_true_true

FunBoundsVS FSize M (Uni_AdviceF adv) ins out
  (fun
     x : {n : nat
         | n <
           lnth [seq x.+1 | x <- Q_Ar q]
             (exist (fun n0 : nat => n0 < length [seq x.+1 | x <- Q_Ar q]) i
                lti)} =>
   ExtendAt0N (PolyTerm_PolyTermVS p)
     (fun
        y : {n0 : nat
            | n0 <
              lnth (Q_Ar q)
                (exist (fun n : nat => n < length (Q_Ar q)) i
                   (PrenexAddUni_obligation_1 (Q_Ar q)
                      (exist
                         (fun n : nat =>
                          n < length [seq x0.+1 | x0 <- Q_Ar q]) i lti)))} =>
      LiftPolyUni (insB2 y))
     (exist
        (fun n0 : nat =>
         n0 <
         (lnth (Q_Ar q)
            (exist (fun n : nat => n < length (Q_Ar q)) i
               (PrenexAddUni_obligation_1 (Q_Ar q)
                  (exist
                     (fun n : nat => n < length [seq x0.+1 | x0 <- Q_Ar q]) i
                     lti)))).+1) (` x)
        (PrenexAddUni_obligation_2 (Q_Ar q)
           (exist (fun n : nat => n < length [seq x0.+1 | x0 <- Q_Ar q]) i
              lti) x))) (LiftPolyUni outB2) u == true


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
      (* destruct H as [adv [H0 [H1 H2]]]. *)
      destruct H as [adv [H0 H2]].
      exists (AdviceExtend F adv).
      split.
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
      (* * move=> u [i lti] bnds; simpl in *.
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
        unfold InBound in *.
        rewrite Q_Prenex_Correct_Lem_0 in H1'; simpl in H1'. 
        rewrite lnth_map; simpl.
        remember (Utils.lnth_map_obligation_1 _ _ _ _ _) as DD0; clear HeqDD0; simpl in DD0.
        by replace DD0 with lti2;[|apply eq_irrelevance]. *)
      * move=> u [[|i] lti]; simpl in *=> ins out chk; unfold AdviceExtend in chk; simpl in chk.
        --  replace (fun x => ins _) with ins in chk;[
              |apply functional_extensionality;move=>[x ltx];f_equal; by apply subset_eq_compat].
            remember (FBC ins out chk) as FBC'; clear HeqFBC' FBC.
            replace (fun x => lnth _ _) with (fun x => PolyTerm_PolyTermVS (E := length bs :: Q_Ar q) (lnth bs x));[
              |apply functional_extensionality;move=>[x ltx];rewrite lnth_map;do 2 f_equal; by apply subset_eq_compat].
            by rewrite Q_Prenex_Correct_Lem_3.
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
      (* destruct H as [adv [H0 [H1 H2]]]. *)
      destruct H as [adv [H0 H2]].
      simpl in adv.
      exists (adv (exist _ 0 (ltn0Sn (length (Q_Ar q))))).
      simpl; split.
      --  unfold Fun_Bound_Check=> ins out io.
          remember (H2 (fun=> 0%R) (exist _ 0 (ltn0Sn (length (Q_Ar q)))) ins out io) as H; clear HeqH H2; simpl in H. 
          replace (fun x => lnth _ _) with (fun x => PolyTerm_PolyTermVS (E := length bs :: Q_Ar q) (lnth bs x)) in H;[
                  |apply functional_extensionality;move=>[x ltx];rewrite lnth_map;do 2 f_equal; by apply subset_eq_compat].
          by rewrite Q_Prenex_Correct_Lem_3 in H.
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
      split.
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
      (* * move=> u [i lti] bnd; simpl in *.
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
          |apply eq_irrelevance]. *)
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
    * destruct (Poly_Denote FSize M p) eqn:PM;[|fcrush].
      simpl.
      assert (
        forall r : {r : 'F_FSize | r < o},
          PrenexDenotation FSize (AddModelV _ M (` r)) (Q_Prenex q)) as H';[qauto|clear IH H].
      apply choice in H'; destruct H' as [adv H].
      exists (Uni_AdviceF adv).
      split.
      + move=>[u ltu]; simpl.
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
      (* + move=> u [[|i] lti] chk; simpl in *.
        unfold InBound; rewrite PolyTerm_PolyTermVS_Correct PM.
        clear chk. *)
      + move=> u [i lti] ins out io.
        unfold Uni_AdviceF in io; simpl in io.
        pose (ins (exist _ 0 (Uni_AdviceF_obligation_1 (Q_Ar q) (exist _ i lti) ins))) as X.
        destruct (X < o) eqn:o0;[|rewrite dep_if_case_false in io;[exact o0|by cbn in io]].
        rewrite dep_if_case_true in io.
        destruct (H (exist _ X o0)) as [_ H2]; clear H.
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
        remember (H2 u (exist _ i lti2) (fSeqRest (eq_rect _ (fun x => |[x]| -> _) ins _ EE)) out YY) as H2'; clear HeqH2' H2; simpl in H2'.
        simpl in *.
        remember (exiBounds (Q_Prenex q)
        (exist (fun n : nat => n < length (Q_Ar q)) i
           lti2)) as Y; destruct Y as [insB outB]; simpl in H2'.
        remember (exiBounds (Q_Prenex q)
                  (exist (fun n : nat => n < length (Q_Ar q)) i
                    (PrenexAddUni_obligation_1 (Q_Ar q)
                        (exist (fun n : nat => n < length [seq x.+1 | x <- Q_Ar q]) i
                          lti)))) as Y2; destruct Y2 as [insB2 outB2]; simpl.
        remember (fSeqRest _) as ins2.
        simpl.
        remember (exist
        (fun n0 : nat =>
         n0 <
         (lnth (Q_Ar q)
            (exist (fun n : nat => n < length (Q_Ar q)) i
               (PrenexAddUni_obligation_1 (Q_Ar q)
                  (exist
                     (fun n : nat => n < length [seq x0.+1 | x0 <- Q_Ar q]) i
                     lti)))).+1)) as i'.
        (PrenexAddUni_obligation_2 (Q_Ar q)
           (exist (fun n : nat => n < length [seq x0.+1 | x0 <- Q_Ar q]) i
              lti) x)) as i'.
        (exist (fun n : nat => n < length (Q_Ar q)) i
           lti2)) as Y.
        simpl in H2'.
        clear YY.
        (exist (fun n : nat => n < length (Q_Ar q)) i
           (PrenexAddUni_obligation_1 (Q_Ar q)
              (exist (fun n : nat => n < length [seq x.+1 | x <- Q_Ar q]) i
                 lti)))) as Y.
(PrenexAddUni_obligation_1 (Q_Ar q)
               (exist (fun n : nat => n < length [seq x.+1 | x <- Q_Ar q]) i
                  lti)).
          clear adv PM out M p.
          remember (length (Q_Ar q)) as n; clear Heqn q u o FSize.
          hammer.
          sfirstorder.
        apply EEConvert in io.
        fcrush.
        destruct o as [o].

        destruct i; simpl.
        

        

        assert (u 0 < o) as ltuo.
            remember (ltu (exist _ 0 (ltn0Sn _)) (fun _ => 0%R)) as ltu'; clear Heqltu'.
            unfold InBound in ltu'.
            simpl in ltu'.
            rewrite PolyTerm_PolyTermVS_Correct in ltu'.
            by rewrite PM in ltu'.
        destruct (H (exist _ (u (exist _ 0 (ltn0Sn _))) ltuo)) as [H0 _]; simpl in *.
        rewrite 
        unfold PrenexZODenotation in *.

      split;[|split].
      * unfold PrenexFormulaCondition.
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
        unfold PrenexFormulaCondition in H; simpl in H.
        assert (forall j v,
              InBound M
                {|
                  exiVAdv := Uni_Advice (fun x => exiVAdv (nu (FO_Prenex f)) (adv x));
                  exiFAdv := exiFAdv _ (adv (exist ((lt)^~ s) (u (exist _ 0 (ltn0Sn _))) ltuE))
                |} (u j)
                (nth PolyZeroVS
                  (uniBounds (PrenexAddUni (PolyTerm_PolyTermVS p) (FO_Prenex f)))
                  (` j)) (MakeU u v)) as ltuX.
              clear H ; move=> [j ltj] v; simpl in *.
              remember (ltu (exist _ j ltj) v) as ltu'; clear Heqltu'.
              unfold InBound in *; simpl in *.
              destruct j; simpl in *.
              by rewrite PolyTermVSCastCastId; rewrite PolyTermVSCastCastId in ltu'.
              change (PolyZeroVS (nu := [seq x.+1 | x <- nu (FO_Prenex f)]))
              with (LiftPolyUni (nu := nu (FO_Prenex f)) PolyZeroVS) in ltu'.
              change (PolyZeroVS (nu := [seq x.+1 | x <- nu (FO_Prenex f)]))
              with (LiftPolyUni (nu := nu (FO_Prenex f)) PolyZeroVS).
              rewrite nth_map; rewrite nth_map in ltu'.
              remember (PolyVSDenotation _ _ _ _ _) as PD0.
              replace (PolyVSDenotation _ _ _ _ _) with PD0.
              destruct PD0; auto; simpl in *.
              rewrite HeqPD0; clear HeqPD0 PD0 ltu'.
              do 2 rewrite <- (FO_Prenex_Correct_Lem_7_0 (nth PolyZeroVS (uniBounds (FO_Prenex f)) j)).
              apply FO_Prenex_Correct_Lem_8.
        assert (forall j v, InBound (AddModelV M (u (exist _ 0 (ltn0Sn _))))
               (adv (exist ((lt)^~ s) (u (exist _ 0 (ltn0Sn _))) ltuE)) (fSeqRest u j)
               (nth PolyZeroVS (uniBounds (FO_Prenex f)) (` j)) (MakeU (fSeqRest u) v)) as ltu0.
              clear H ; move=> [j ltj] v; simpl in *.
              assert (j.+1 < (length (uniBounds (FO_Prenex f))).+1) as ltj2;[clear ltu ltuX ltuE PM adv v u s M p; sfirstorder|].
              remember (ltuX (exist _ (j.+1) ltj2) v) as ltu'; clear Heqltu'.
              unfold InBound in *; simpl in *.
              change (PolyZeroVS (nu := [seq x.+1 | x <- nu (FO_Prenex f)]))
              with (LiftPolyUni (nu := nu (FO_Prenex f)) PolyZeroVS) in ltu'.
              rewrite nth_map in ltu'.
              remember (PolyVSDenotation _ _ _ _ _) as PD0.
              replace (PolyVSDenotation _ _ _ _ _) with PD0.
              destruct PD0; auto; simpl in *.
              replace (fSeqRest u (exist _ j ltj))
                with (u (exist _ j.+1 ltj2)); auto.
              unfold fSeqRest; simpl; apply f_equal; by apply subset_eq_compat.
              rewrite HeqPD0; clear HeqPD0 PD0 ltu'.
              by rewrite <- FO_Prenex_Correct_Lem_4_0_1.
        remember (H (exist _ (fSeqRest u) ltu0)) as H'; clear HeqH' H; simpl in H'.
        rewrite <- (FO_Prenex_Correct_Lem_5_5 (exiF1 := exiFAdv (nu (FO_Prenex f))
          (adv (exist ((lt)^~ s) (u (exist _ 0 (ltn0Sn _))) ltuE)))).
        by rewrite <- FO_Prenex_Correct_Lem_4_0_2.


        unfold PrenexDenotation.
        2:{ fcrush. auto.
        rewrite HeqADV1.

v        f_equal.
        destruct E3.
        remember (PrenexExiBoundCondition_obligation_1 _ _) as DDD0; clear HeqDDD0.
        remember (PrenexExiBoundCondition_obligation_3 _ _ _ _ _) as DDD1; clear HeqDDD1.

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
        remember (PrenexExiBoundCondition_obligation_4 _ _ _ _ _) as DDD0; clear HeqDDD0.
        remember (PrenexExiBoundCondition_obligation_3 _ _ _ _ _) as DDD1; clear HeqDDD1.
        rewrite lnth_map.
        remember (PrenexExiBoundCondition_obligation_3 _ _ _ _) as DDD2; clear HeqDDD2.
        remember (PrenexExiBoundCondition_obligation_5 _ _ _ _) as DDD2; clear HeqDDD2.
        rewrite lnth_map.
        do 2 rewrite eq_rect_ap_el; f_equal.
        destruct E3.
        transitivity (FunBoundsVS FSize M adv (eq_rect _ (fun x => |[x]| -> _) ins1 _ E3) out 
                                              (eq_rect _ (fun x => |[x]| -> _) insB2 _ E3) outB1 u).
            f_equal.
        remember (PrenexExiBoundCondition_obligation_4 _ _ _ _) as DDD0; clear HeqDDD0.
        remember (PrenexExiBoundCondition_obligation_3 _ _ _ _) as DDD1; clear HeqDDD1.
        remember (PrenexExiBoundCondition_obligation_5 _ _ _ _) as DDD2; clear HeqDDD2.
        rewrite lnth_map; simpl.
        replace (FunBoundsVS FSize M adv) with
           (FunBoundsVS FSize M (eq_rect _ (fun x => PrenexAdvice x _) adv _ (esym E1))).
        f_equal.
        remember (PrenexExiBoundCondition_obligation_1 _ _) as DDD; clear HeqDDD.

        remember (PrenexExiBoundCondition_obligation_2 _ _ _ _) as DDD; clear HeqDDD.

          destruct (lnth (exiBounds (Q_Prenex q))
              (exist
                 (fun n : nat =>
                  n <
                  length
                    (exiBounds
                       (Q_Prenex q))) i
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
unfold PrenexUniversalCondition.

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
              (uniBounds (Q_Prenex q))
              (exist
                 (fun n : nat =>
                  n < length [seq LiftPolyExi i | i <- uniBounds (Q_Prenex q)]) j ltj)) with ltj2.
        f_equal.
      Search (_ <-> ` _ = _).
      rewrite eq_rect_ap_el.

rewrite <- Q_Prenex_Correct_Lem_3.
      

    FunBoundsVS FSize M adv ins out (lnth [seq PolyTerm_PolyTermVS i | i <- bs])
      (PolyTerm_PolyTermVS y) u =
    FunBounds FSize M
      (eq_rect _ (fun x => |[x]| -> 'F_FSize) ins _ (map_length PolyTerm_PolyTermVS bs)) out 
      (lnth bs) y.


        simpl.
      simpl in H2.
      rewrite map_length in adv.
      unfold PrenexDenotation in H.

            rewrite projT1_eq_rect; simpl.
            rewrite nth_map; simpl.
            remember (PrenexExiBoundCondition_obligation_4 _ _ _ _ _) as DDD0; clear HeqDDD0; simpl in DDD0.
            remember (PrenexExiBoundCondition_obligation_3 _ _ _ _ _) as DDD1; clear HeqDDD1; simpl in DDD1.
            remember (PrenexExiBoundCondition_obligation_4 _ _ _ _ _) as DDD3; clear HeqDDD3; simpl in DDD3.
            remember (PrenexExiBoundCondition_obligation_3 _ _ _ _ _) as DDD2; clear HeqDDD2; simpl in DDD2.
            rewrite (lnth_nth PolyZeroVS); simpl.
            rewrite (lnth_nth ([::], PolyZeroVS).1).
            rewrite nth_map; simpl.
            rewrite (lnth_nth PolyZeroVS); simpl.
            rewrite (lnth_nth ([::], PolyZeroVS).1).
            rewrite nth_map; simpl.
            rewrite projT1_eq_rect; simpl.

LiftPolyExi
  (nth PolyZeroVS
     (nth ([::], PolyZeroVS).1 [seq x0.1 | x0 <- exiBounds (Q_Prenex q)]
        (` (exist (fun n : nat => n < length [seq x0.1 | x0 <- exiBounds (Q_Prenex q)]) i DDD1))) x)
LiftPolyExi
  (nth PolyZeroVS
     (nth ([::], PolyZeroVS) (exiBounds (Q_Prenex q)) (` (exist (fun n : nat => n < length [seq x0.1 | x0 <- exiBounds (Q_Prenex q)]) i DDD1))).1 x)

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
                  | x <- exiBounds (Q_Prenex q)]]
     (exist
        (fun n : nat =>
         n <
         length
           [seq x.2
              | x <- [seq ([seq LiftPolyExi i | i <- x.1], LiftPolyExi x.2)
                        | x <- exiBounds (Q_Prenex q)]]) i
        (PrenexExiBoundCondition_obligation_5 FSize
           (PrenexAddExi [seq PolyTerm_PolyTermVS i | i <- bs]
              (PolyTerm_PolyTermVS y) (Q_Prenex q))
           (exist
              (fun n : nat =>
               n <
               (length
                  [seq ([seq LiftPolyExi i | i <- x.1], LiftPolyExi x.2)
                     | x <- exiBounds (Q_Prenex q)]).+1) i.+1 lt
            simpl in ADV2.
            replace (AdviceExtend F adv) with ADV2.

            replace ADV1 with ADV2.
            destruct E1.
            f_equal.
            replace (eq_rect
     (ExtendAt0 (length bs)
        [eta nth 0 [seq length x.1 | x <- exiBounds (Q_Prenex q)]])
     (PrenexAdvice^~ FSize) (AdviceExtend F adv)
     [eta nth 0
            (length [seq PolyTerm_PolyTermVS i0 | i0 <- bs]
             :: [seq length x.1
                   | x <- [seq ([seq LiftPolyExi i | i <- x.1],
                               LiftPolyExi x.2)
                             | x <- exiBounds (Q_Prenex q)]])] E1) with  (AdviceExtend F adv).


Lemma Q_Prenex_Correct_Lem_2 {M u p a f A adv} :
  PrenexZODenotation FSize M (LiftPropExi p) (AdviceExtend f adv) u
  = FunBounds _ (AddModelF _ M (existT _ a f)) ar  u.
Proof.
  elim: p; try qauto.
  move=> p1 p2.
  simpl.
  by do 2 rewrite Q_Prenex_Correct_Lem_0.
Qed.

            rewrite <- Q_Prenex_Correct_Lem_0 in H2'.
            remember (FunBounds _ _ _ _ _ _) as FF.
            replace (FunBounds _ _ _ _ _ _) with FF; auto; rewrite HeqFF; clear HeqFF FF H2'.
            remember (eq_rect _ (fun x : nat => |[x]| -> 'F_FSize) ins _ E2) as ins2.
            remember (fun x : |[lnth [seq length x.1 | x <- exiBounds (Q_Prenex q)]
                        (exist _ i
                            (PrenexExiBoundCondition_obligation_1 
                              (Q_Prenex q)
                              (exist
                                  (fun n0 : nat => n0 < length (exiBounds (Q_Prenex q)))
                                  i lti2)))]| => _) as BS2.
            remember (fun x : |[lnth
             [seq length x.1
                | x <- [seq ([seq LiftPolyExi i | i <- x.1], LiftPolyExi x.2)
                          | x <- exiBounds (Q_Prenex q)]]
             (exist _ i
                (PrenexExiBoundCondition_obligation_1
                   (PrenexAddExi [seq PolyTerm_PolyTermVS i | i <- bs]
                      (PolyTerm_PolyTermVS y) (Q_Prenex q))
                   (exist
                      (fun n0 =>
                       n0 <
                       (length
                          [seq ([seq LiftPolyExi i | i <- x.1],
                               LiftPolyExi x.2)
                             | x <- exiBounds (Q_Prenex q)]).+1) i.+1 lti)))]| => _) as BS1. 
            remember (PolyVSDenotation FSize 

            remember 

            destruct E2.
            cbn.
            rewrite <- Q_Prenex_Correct_Lem_0.
            remember (PrenexExiBoundCondition_obligation_1 _ _) as DD0.
\            rewrite eq_rect_ap_el.

            rewrite eq_rect_ap.
            simpl in *.
            unfold FunBounds.
            remember (lnth [seq length x.1 | x <- exiBounds (Q_Prenex q)] _) as L0.
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
           (PrenexExiBoundCondition_obligation_4 FSize
              (PrenexAddExi [seq PolyTerm_PolyTermVS i | i <- bs]
                 (PolyTerm_PolyTermVS y) (Q_Prenex q))
              (exist
                 (fun n : nat =>
                  n <
                  (length
                     [seq ([seq LiftPolyExi i | i <- x0.1], LiftPolyExi x0.2)
                        | x0 <- exiBounds (Q_Prenex q)]).+1) 0 lti) ins x)))
     (eq_rect
        (ExtendAt0 (length bs)
           [eta nth 0 [seq length x0.1 | x0 <- exiBounds (Q_Prenex q)]])
        (PrenexAdvice^~ FSize) (AdviceExtend F adv)
        [eta nth 0
               (length [seq PolyTerm_PolyTermVS i | i <- bs]
                :: [seq length x1.1
                      | x1 <- [seq ([seq LiftPolyExi i | i <- x1.1],
                                   LiftPolyExi x1.2)
                                 | x1 <- exiBounds (Q_Prenex q)]])] E1) u)
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
           (PrenexExiBoundCondition_obligation_4 FSize
              (PrenexAddExi [seq PolyTerm_PolyTermVS i | i <- bs]
                 (PolyTerm_PolyTermVS y) (Q_Prenex q))
              (exist
                 (fun n : nat =>
                  n <
                  (length
                     [seq ([seq LiftPolyExi i | i <- x0.1], LiftPolyExi x0.2)
                        | x0 <- exiBounds (Q_Prenex q)]).+1) 0 lti) ins x)))
     (eq_rect
        (ExtendAt0 (length bs)
           [eta nth 0 [seq length x0.1 | x0 <- exiBounds (Q_Prenex q)]])
        (PrenexAdvice^~ FSize) (AdviceExtend F adv)
        [eta nth 0
               (length [seq PolyTerm_PolyTermVS i | i <- bs]
                :: [seq length x1.1
                      | x1 <- [seq ([seq LiftPolyExi i | i <- x1.1],
                                   LiftPolyExi x1.2)
                                 | x1 <- exiBounds (Q_Prenex q)]])] E1) u)
  (PolyVSDenotation FSize M (PolyTerm_PolyTermVS y)
     (eq_rect
        (ExtendAt0 (length bs)
           [eta nth 0 [seq length x.1 | x <- exiBounds (Q_Prenex q)]])
        (PrenexAdvice^~ FSize) (AdviceExtend F adv)
        [eta nth 0
               (length [seq PolyTerm_PolyTermVS i | i <- bs]
                :: [seq length x.1
                      | x <- [seq ([seq LiftPolyExi i | i <- x.1],
                                  LiftPolyExi x.2)
                                | x <- exiBounds (Q_Prenex q)]])] E1) u)


        replace (PrenexZODenotation FSize M (LiftPropExi (formula (Q_Prenex q))) (A := ?A) ?x (MakeU u (fun=> 0%R)) == Some true)
          with (AA _ x).
        transitivity (AA _ (eq_rect _ (PrenexAdvice^~ FSize) (AdviceExtend F adv) _ E1)); qauto. (* ???Why does this work??? *)
              
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


        destruct (Q_Prenex q); simpl in *.
        by rewrite map_length.
        qauto.

        f_equal.
        rewrite map_flatten.
        Search (map (map _) _).
        
      replace (PrenexAdvice FSize
        (PrenexAddExi [seq PolyTerm_PolyTermVS i | i <- bs]
           (PolyTerm_PolyTermVS y) (Q_Prenex q)))
        with (PrenexAdvice
     (ExtendAt0 (length bs)
        [eta nth 0 [seq length x.1 | x <- exiBounds (Q_Prenex q)]]) FSize).
      replace [eta nth 0
               [seq length x.1
                  | x <- exiBounds
                           (PrenexAddExi
                              [seq PolyTerm_PolyTermVS i | i <- bs]
                              (PolyTerm_PolyTermVS y) 
                              (Q_Prenex q))]]
         with (ExtendAt0 (length bs)
        [eta nth 0 [seq length x.1 | x <- exiBounds (Q_Prenex q)]]).
      simpl.
      unfold PrenexAddExi.
      dest
      simpl in *.
      rewrite <- Q_Prenex_Correct_Lem_0 in H.

      destruct IH.
      apply IH in H.

    simpl.


Lemma ZO_Prenex_Correct_PrenexFormulaCondition
  (f : ZerothOrderFormula) :
  ZerothOrder_Denote _ M f <-> 
  exists a, PrenexFormulaCondition _ M (ZO_Prenex f) a.



(* Program Definition AdviceUniExtend
  (M : Sigma11Model)
  nu (adv : PrenexAdvice nu) 
  (f : forall i, (|[(lnth nu i).+1]| -> 'F_FSize) -> 'F_FSize)
  (H : forall i (t : |[lnth nu i]| -> 'F_FSize), 
    f i (ExtendAt0N (V_F M 0) t) = 
    exiVAdv _ adv i t) :
  PrenexAdvice (map (fun x => x.+1) nu) :=
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

Lemma FO_Prenex_Correct_Lem_0_0 {nu}
  (p : PolyTermVS)
  (adv : PrenexAdvice nu) 
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

Lemma FO_Prenex_Correct_Lem_0 {nu}
  (f: ZerothOrderFormulaVS)
  (adv : PrenexAdvice nu) 
  (M : Sigma11Model) (r : 'F_FSize) :
  forall u,
  PrenexZODenotation f (AddModelV M r) adv u <->
  PrenexZODenotation (LiftPropExi f) M (AdviceExtend r adv) u.
Proof.
  elim: f; try qauto.
  move=> p1 p2 u.
  simpl.
  by do 2 rewrite FO_Prenex_Correct_Lem_0_0.
Qed.

Lemma FO_Prenex_Empty_InputBounds
  (f : FirstOrderFormula) :
  (exiFInputBounds (FO_Prenex f)) = [::].
Proof. elim: f; try qauto. Qed.

Lemma FO_Prenex_Empty_OutputBounds
  (f : FirstOrderFormula) :
  (exiFOutputBounds (FO_Prenex f)) = [::].
Proof. elim: f; try qauto. Qed.

Lemma FO_Prenex_Correct_PrenexSOBoundCondition
  (f : FirstOrderFormula) (M : Sigma11Model) a :
  PrenexSOBoundCondition (FO_Prenex f) M a.
Proof.
  move=> u [i lti]; simpl.
  assert (i < 0);[|fcrush].
  by rewrite FO_Prenex_Empty_InputBounds in lti.
Qed.

Fixpoint FO_nu (f : FirstOrderFormula) : seq nat :=
  match f with
  | ZO z => [::]
  | FOExists p f => 0::FO_nu f
  | FOForall p f => map (fun x => x.+1) (FO_nu f)
  end.

Lemma FO_Prenex_Correct_PrenexFormulaCondition_Exi_Lem :
  forall f p,
  length (uniBounds (FO_Prenex (FOExists p f))) 
  = length (uniBounds (FO_Prenex f)).
Proof. cbn; by move=> f; rewrite map_length. Qed.

(* 
Lemma FO_Prenex_Correct_PrenexFormulaCondition_Exi_Lem2  {p f}:
  uniBounds (PrenexAddExi p f) = uniBounds f. *)

Lemma FO_Prenex_Correct_PrenexFormulaCondition_Exi
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model) r a :
  PrenexFormulaCondition (FO_Prenex f) (AddModelV M r) a <-> 
  PrenexFormulaCondition (FO_Prenex (FOExists p f)) M (AdviceExtend r a).
Proof. 
  split; move=> H u; apply FO_Prenex_Correct_Lem_0.
  - unfold PrenexFormulaCondition in H.
    move: u.
    rewrite FO_Prenex_Correct_PrenexFormulaCondition_Exi_Lem.
    move=> u.
    destruct u as [u ltu]; simpl in *.
    assert (forall
    (j : {n : nat | n < length (uniBounds (FO_Prenex f))})
    (v : nat -> 'F_FSize),
      InBound (AddModelV M r) a (u j)
        (nth PolyZeroVS (uniBounds (FO_Prenex f)) (` j))
        (MakeU u v)) as ltu2.
    move=> j v.
    remember (ltu j v); clear Heqi.
    change PolyZeroVS  with (LiftPolyExi (nu := nu (FO_Prenex f)) PolyZeroVS) in i.
    rewrite nth_map in i.
    unfold InBound in *.
    by rewrite FO_Prenex_Correct_Lem_0_0.
    exact (H (exist _ u ltu2)).
  - unfold PrenexFormulaCondition in H.
    destruct u as [u ltu]; simpl in *.
    rewrite map_length in H.
    assert (forall
      (j : {n : nat | n < length (uniBounds (FO_Prenex f))})
      (v : nat -> 'F_FSize),
        InBound M (AdviceExtend r a) (u j)
          (nth PolyZeroVS
              (uniBounds
                (PrenexAddExi (PolyTerm_PolyTermVS p)
                    (FO_Prenex f))) (` j)) (MakeU u v)) as ltu2;[
      |exact (H (exist _ u ltu2))].
    move=> j v.
    remember (ltu j v); clear Heqi.
    unfold InBound in *.
    auto.
    rewrite FO_Prenex_Correct_Lem_0_0 in i.
    simpl in *.
    change PolyZeroVS 
      with (LiftPolyExi (nu := nu (FO_Prenex f)) PolyZeroVS).
    by rewrite nth_map.
Qed.

Program Definition EmptyU {M b q a} : 
  U (PrenexAddExi b q) M a 0 := emptyTuple.

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

Lemma FO_Prenex_Correct_PrenexFOBoundCondition_Exi
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model) a r :
  ((forall n, InBound M (AdviceExtend r a) r (PolyTermVSCast (PolyTerm_PolyTermVS p)) n)
   /\ PrenexFOBoundCondition (FO_Prenex f) (AddModelV M r) a) <->
  PrenexFOBoundCondition (FO_Prenex (FOExists p f)) M (AdviceExtend r a).
Proof.
  split.
  - move=> [H0 H1] [i lti] u n0.
    destruct i;auto;simpl in *.
    unfold PrenexFOBoundCondition in H1.
    destruct u as [u ltu]; simpl in *.
    assert (forall (j : {n : nat | n < nth 0 (nu (FO_Prenex f)) i})
        (v : nat -> 'F_FSize),
      InBound (AddModelV M r) a (u j)
        (nth PolyZeroVS (uniBounds (FO_Prenex f)) (` j))
        (MakeU u v)) as ltu2.
      move=> j v; remember (ltu j v) as ltu'; clear Heqltu'.
      change PolyZeroVS 
      with (LiftPolyExi (nu := nu (FO_Prenex f)) PolyZeroVS) in ltu'.
      rewrite nth_map in ltu'.
      unfold InBound in *.
      by rewrite FO_Prenex_Correct_Lem_0_0.
    remember (H1 (exist _ i lti) (exist _ u ltu2) n0) as H1'; clear HeqH1' H1; simpl in H1'.
    simpl in *.
    unfold InBound in *.
    change PolyZeroVS 
    with (LiftPolyExi (nu := nu (FO_Prenex f)) PolyZeroVS).
    rewrite nth_map.
    rewrite <- FO_Prenex_Correct_Lem_0_0.
    destruct (PolyVSDenotation _ _ _ _); auto.
    remember (lt _ _ _) as H1B.
    replace (lt _ _ _) with H1B; auto.
    rewrite HeqH1B; clear HeqH1B H1' H1B.
    f_equal.
    assert (
      (exist (fun n : nat => n < length (nu (FO_Prenex f))) i lti) = 
      (exist _ i
     (AdviceExtend_obligation_2 (nu (FO_Prenex f))
        (exist _ i.+1 lti)
        (fun x=> u (exist _  (` x)
              (PrenexFOBoundCondition_obligation_1
                 (PrenexAddExi (PolyTerm_PolyTermVS p) (FO_Prenex f)) M
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
      unfold PrenexFOBoundCondition in H.
      simpl in H.
      remember (H (exist _ 0 (ltn0Sn _)) EmptyU n) as H'; clear HeqH' H; simpl in H'.
      replace (MakeU emptyTuple n) with n in H'; auto.
      unfold MakeU in H'.
      apply functional_extensionality; move=> [|i]; auto.
    + move=> [i lti] u n; simpl in *.
      unfold PrenexFOBoundCondition in H; simpl in H.
      destruct u as [u ltu]; simpl.
      assert (forall j v,
        InBound M (AdviceExtend r a) (u j)
          (nth PolyZeroVS
              (uniBounds
                (PrenexAddExi (PolyTerm_PolyTermVS p)
                    (FO_Prenex f))) (` j)) (MakeU u v)) as ltu2.
        move=> j v; remember (ltu j v) as ltu'; clear Heqltu'.
        unfold InBound in *; simpl in *.
        change PolyZeroVS 
        with (LiftPolyExi (nu := nu (FO_Prenex f)) PolyZeroVS).
        rewrite nth_map.
        by rewrite FO_Prenex_Correct_Lem_0_0 in ltu'.
      remember (H (exist _ (i.+1) lti) (exist _ u ltu2) n) as H'; clear HeqH' H; simpl in H'.
      remember (InBound _ _ _ _ _ _) as H1B.
      replace (InBound _ _ _ _ _ _) with H1B; auto.
      rewrite HeqH1B; clear HeqH1B H1B H'.
      unfold InBound.
      apply match_lem; auto.
      change (PolyZeroVS (nu := 0 :: nu (FO_Prenex f))) 
        with (LiftPolyExi (nu := nu (FO_Prenex f)) (PolyZeroVS));rewrite nth_map.
      by rewrite <- FO_Prenex_Correct_Lem_0_0.
      f_equal.
      assert ((exist (fun n0 : nat => n0 < length (nu (FO_Prenex f))) i
              (AdviceExtend_obligation_2 (nu (FO_Prenex f))
                  (exist _ i.+1 lti)
                  (fun x => u (exist _
                        (` x)
                        (PrenexFOBoundCondition_obligation_1
                          (PrenexAddExi (PolyTerm_PolyTermVS p)
                              (FO_Prenex f)) M
                          (AdviceExtend r a)
                          (exist _ i.+1 lti)
                          (exist _ u ltu2) x))) (erefl _)))
              = (exist (fun n : nat => n < length (nu (FO_Prenex f))) i lti)) as e;[by apply subset_eq_compat|].
      apply (exiVAdvEqLem e); simpl=> x.
      f_equal.
      apply subset_eq_compat.
      by rewrite projT1_eq_rect.
Qed.

Lemma FO_Prenex_Correct_PrenexSOBoundCondition_Exi
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model) a r :
  PrenexSOBoundCondition (FO_Prenex f) (AddModelV M r) a <->
  PrenexSOBoundCondition (FO_Prenex (FOExists p f)) M (AdviceExtend r a).
Proof.
  split=> H;[|apply FO_Prenex_Correct_PrenexSOBoundCondition].
  move=> u [i lti]; simpl.
  assert (i < 0);[|fcrush].
  by rewrite FO_Prenex_Empty_InputBounds in lti.
Qed.

Program Definition AdviceDropExi {nu}
  (adv : PrenexAdvice (0 :: nu)) :=
  {| exiVAdv := fun i => exiVAdv _ adv (i.+1) 
   ; exiFAdv := exiFAdv _ adv
  |}.

Theorem AdviceDropExi_Spec {nu}
  (adv : PrenexAdvice (0 :: nu)) :
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

Lemma FO_Prenex_Correct_Lem_4_0
  nu p
  (M: Sigma11Model)
  (s: 'F_FSize)
  (adv: {r : 'F_FSize | lt r s} -> PrenexAdvice nu)
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

Lemma FO_Prenex_Correct_Lem_4_0_1 {k} {e}
  nu p
  (M: Sigma11Model)
  (s: 'F_FSize)
  (adv: {r : 'F_FSize | lt r s} -> PrenexAdvice nu)
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

Lemma FO_Prenex_Correct_Lem_4
  nu f
  (M: Sigma11Model)
  (s: 'F_FSize)
  (adv: {r : 'F_FSize | lt r s} -> PrenexAdvice nu)
  (u: nat -> 'F_FSize)
  (ltu0: lt (u 0) s) :
PrenexZODenotation f (AddModelV M (u 0))
  (adv (exist ((lt)^~ s) (u 0) ltu0)) (fun x : nat => u x.+1) <->
PrenexZODenotation (LiftPropUni f) M
  {| exiVAdv := Uni_Advice (fun x => exiVAdv nu (adv x));
     exiFAdv := exiFAdv nu (adv (exist ((lt)^~ s) (u 0) ltu0))
  |} u.
Proof.
  elim: f; try qauto.
  move=> p0 p1.
  simpl.
  by do 2 rewrite FO_Prenex_Correct_Lem_4_0.
Qed.


Lemma FO_Prenex_Correct_Lem_4_0_2 {k}
  nu p
  (M: Sigma11Model)
  (s: 'F_FSize)
  (adv: {r : 'F_FSize | lt r s} -> PrenexAdvice nu)
  (u: |[k.+1]| -> 'F_FSize)
  (v: nat -> 'F_FSize)
  (ltu0: lt (u (exist _ 0 (ltn0Sn _))) s) :
PrenexZODenotation p (AddModelV M (u (exist _ 0 (ltn0Sn _))))
    (adv (exist ((lt)^~ s) (u (exist _ 0 (ltn0Sn _))) ltu0)) (MakeU (fSeqRest u) v) =
PrenexZODenotation (LiftPropUni p) M
    {|
      exiVAdv := Uni_Advice (fun x => exiVAdv nu (adv x));
      exiFAdv := exiFAdv nu (adv (exist ((lt)^~ s) (u (exist _ 0 (ltn0Sn _))) ltu0))
    |} (MakeU u v).
Proof.
  elim: p; try qauto.
  move=> p0 p1.
  simpl.
  by do 2 rewrite FO_Prenex_Correct_Lem_4_0_1.
Qed.

Lemma FO_Prenex_Correct_Lem_5_1 {p M adv1 adv2 u} :
  PolyVSDenotation (LiftPolyUni (PolyTerm_PolyTermVS p)) M adv1 u =
  PolyVSDenotation (LiftPolyUni (PolyTerm_PolyTermVS p)) M adv2 u.
Proof.
  induction p; try qauto.
  simpl.
  do 2 f_equal.
  by apply functional_extensionality.
Qed.

Lemma FO_Prenex_Correct_Lem_5_0 {z M adv1 adv2 u} :
  PrenexZODenotation (LiftPropUni (ZerothOrder_ZerothOrderVS z)) M adv1 u =
  PrenexZODenotation (LiftPropUni (ZerothOrder_ZerothOrderVS z)) M adv2 u.
Proof.
  induction z; try qauto.
  simpl.
  by do 2 rewrite (FO_Prenex_Correct_Lem_5_1 (adv1 := adv1) (adv2 := adv2)).
Qed.

Lemma FO_Prenex_Correct_Lem_5_3 {p M exiV exiF1 exiF2 u} :
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

Lemma FO_Prenex_Correct_Lem_5_2 {z M exiV exiF1 exiF2 u} :
  PrenexZODenotation (LiftPropExi (ZerothOrder_ZerothOrderVS z)) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  PrenexZODenotation (LiftPropExi (ZerothOrder_ZerothOrderVS z)) M
        {| exiVAdv := exiV; exiFAdv := exiF2 |} u.
Proof.
  induction z; try qauto.
  simpl.
  by do 2 rewrite (FO_Prenex_Correct_Lem_5_3 (exiF1 := exiF1) (exiF2 := exiF2)).
Qed.

Lemma FO_Prenex_Correct_Lem_6_0 {nu}
  (p : @PolyTermVS _)
  (adv : PrenexAdvice (0 :: nu))
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

Lemma FO_Prenex_Correct_Lem_6 {nu}
  p
  (adv : PrenexAdvice (0 :: nu))
  (M : Sigma11Model) :
  forall u,
  PrenexZODenotation p (AddModelV M (exiVAdv _ adv (exist _ 0 (ltn0Sn _)) (fun x => u (` x)))) (AdviceDropExi adv) u = 
  PrenexZODenotation (LiftPropExi p) M adv u.
Proof.
  elim: p; try qauto.
  move=> p1 p2 u.
  simpl.
  by do 2 rewrite FO_Prenex_Correct_Lem_6_0.
Qed.

Program Definition AdviceDropUni {nu} r
  (adv : PrenexAdvice (map (fun x => x.+1) nu)) :
  PrenexAdvice nu :=
  {| exiVAdv := fun i t => exiVAdv _ adv i (ExtendAt0N r t)
   ; exiFAdv := exiFAdv _ adv
  |}.
Next Obligation. by rewrite map_length. Qed.
Next Obligation.
  rewrite (lnth_nth 1) nth_map in H.
  by rewrite (lnth_nth 0).
Qed.

Lemma FO_Prenex_Correct_Lem_7_0 {nu}
  (p : @PolyTermVS _)
  (adv : PrenexAdvice (map (fun x => x.+1) nu))
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

Lemma FO_Prenex_Correct_Lem_7_0_A {nu r}
  p
  (adv : PrenexAdvice (map (fun x => x.+1) nu))
  (M : Sigma11Model) :
  forall u,
  PolyVSDenotation p (AddModelV M r) (AdviceDropUni r adv) u = 
  PolyVSDenotation (LiftPolyUni p) M adv (ExtendAt0 r u).
Proof.
  move=> u.
  remember (ExtendAt0 r u) as u'.
  replace u with (fun x => u' (x.+1));[|qauto].
  replace r with (u' 0);[|qauto].
  by rewrite FO_Prenex_Correct_Lem_7_0.
Qed.

Lemma FO_Prenex_Correct_Lem_7 {nu}
  p
  (adv : PrenexAdvice (map (fun x => x.+1) nu))
  (M : Sigma11Model) :
  forall u,
  PrenexZODenotation p (AddModelV M (u 0)) (AdviceDropUni (u 0) adv) (fun x => u (x.+1)) = 
  PrenexZODenotation (LiftPropUni p) M adv u.
Proof.
  elim: p; try qauto.
  move=> p1 p2 u.
  simpl.
  by do 2 rewrite FO_Prenex_Correct_Lem_7_0.
Qed.

Lemma FO_Prenex_Correct_Lem_7_A {nu r}
  p
  (adv : PrenexAdvice (map (fun x => x.+1) nu))
  (M : Sigma11Model) :
  forall u,
  PrenexZODenotation p (AddModelV M r) (AdviceDropUni r adv) u = 
  PrenexZODenotation (LiftPropUni p) M adv (ExtendAt0 r u).
Proof.
  move=> u.
  remember (ExtendAt0 r u) as u'.
  replace u with (fun x => u' (x.+1));[|qauto].
  replace r with (u' 0);[|qauto].
  by rewrite FO_Prenex_Correct_Lem_7.
Qed.

Lemma FO_Prenex_Correct_Lem_5 {f M exiV exiF1 u} :
  PrenexZODenotation (formula (FO_Prenex f)) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  PrenexZODenotation (formula (FO_Prenex f)) M
        {| exiVAdv := exiV; exiFAdv := fun=> (fun a : nat => fun=> None) |} u.
Proof.
  move: M u.
  induction f; simpl=> M u.
  - by do 2 rewrite PrenexZODenotation0Spec.
  - do 2 rewrite <- (FO_Prenex_Correct_Lem_6 (formula (FO_Prenex f)) _ M).
    simpl; by rewrite IHf.
  - do 2 rewrite <- (FO_Prenex_Correct_Lem_7 (formula (FO_Prenex f)) _ M).
    simpl; by rewrite IHf.
Qed.

Lemma FO_Prenex_Correct_Lem_5_5 {f M exiV exiF1 u} :
  PrenexZODenotation (LiftPropUni (formula (FO_Prenex f))) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  PrenexZODenotation (LiftPropUni (formula (FO_Prenex f))) M
        {| exiVAdv := exiV; exiFAdv := fun=> (fun a : nat => fun=> None) |} u.
Proof.
  do 2 rewrite <- (FO_Prenex_Correct_Lem_7 (formula (FO_Prenex f)) _ M).
  by do 2 rewrite FO_Prenex_Correct_Lem_5.
Qed.

Lemma FO_Prenex_Correct_Lem_8 {u f j M exV1 exF1 exF2} :
  PolyVSDenotation (nth PolyZeroVS (uniBounds (FO_Prenex f)) j) M
    {| exiVAdv := exV1;
       exiFAdv := exF1
    |} u =
  PolyVSDenotation (nth PolyZeroVS (uniBounds (FO_Prenex f)) j) M
    {| exiVAdv := exV1;
       exiFAdv := exF2
    |} u.
Proof.
  move: j u M; induction f.
  - by destruct j.
  - move=> j u M.
    simpl.
    change PolyZeroVS with (LiftPolyExi (nu := nu (FO_Prenex f)) (PolyZeroVS)).
    rewrite nth_map.
    do 2 rewrite <- (FO_Prenex_Correct_Lem_6_0 (nth PolyZeroVS (uniBounds (FO_Prenex f)) j)).
    apply IHf.
  - move=> j u M.
    simpl.
    destruct j; simpl.
    by do 2 rewrite PolyTermVSCastCastId.
    change PolyZeroVS with (LiftPolyUni (nu := nu (FO_Prenex f)) PolyZeroVS).
    rewrite nth_map.
    do 2 rewrite <- (FO_Prenex_Correct_Lem_7_0 (nth PolyZeroVS (uniBounds (FO_Prenex f)) j)).
    apply IHf.
Qed.

Lemma FO_Prenex_Correct_Lem_10 {u f j M exV1 exF1 exF2} :
  PolyVSDenotation (nth PolyZeroVS (exiVBounds (FO_Prenex f)) j) M
    {| exiVAdv := exV1;
       exiFAdv := exF1
    |} u =
  PolyVSDenotation (nth PolyZeroVS (exiVBounds (FO_Prenex f)) j) M
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
    change PolyZeroVS with (LiftPolyExi (nu := nu (FO_Prenex f)) (PolyZeroVS)).
    rewrite nth_map.
    do 2 rewrite <- (FO_Prenex_Correct_Lem_6_0 (nth PolyZeroVS (exiVBounds (FO_Prenex f)) j)).
    apply IHf.
  - move=> j u M.
    simpl.
    change PolyZeroVS with (LiftPolyUni (nu := nu (FO_Prenex f)) PolyZeroVS).
    rewrite nth_map.
    do 2 rewrite <- (FO_Prenex_Correct_Lem_7_0 (nth PolyZeroVS (exiVBounds (FO_Prenex f)) j)).
    apply IHf.
Qed.

Lemma FO_Prenex_Correct_Lem_8_5 {f M exiV exiF1 exiF2 j u} :
  PolyVSDenotation (LiftPolyUni (nth PolyZeroVS (uniBounds (FO_Prenex f)) j)) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  PolyVSDenotation (LiftPolyUni (nth PolyZeroVS (uniBounds (FO_Prenex f)) j)) M
        {| exiVAdv := exiV; exiFAdv := exiF2 |} u.
Proof.
  do 2 rewrite <- (FO_Prenex_Correct_Lem_7_0 (nth PolyZeroVS (uniBounds (FO_Prenex f)) j)).
  apply FO_Prenex_Correct_Lem_8.
Qed.


Lemma FO_Prenex_Correct_Lem_10_5 {f M exiV exiF1 exiF2 j u} :
  PolyVSDenotation (LiftPolyUni (nth PolyZeroVS (exiVBounds (FO_Prenex f)) j)) M
        {| exiVAdv := exiV; exiFAdv := exiF1 |} u =
  PolyVSDenotation (LiftPolyUni (nth PolyZeroVS (exiVBounds (FO_Prenex f)) j)) M
        {| exiVAdv := exiV; exiFAdv := exiF2 |} u.
Proof.
  do 2 rewrite <- (FO_Prenex_Correct_Lem_7_0 (nth PolyZeroVS (exiVBounds (FO_Prenex f)) j)).
  apply FO_Prenex_Correct_Lem_10.
Qed.

Program Definition FO_Prenex_Correct_Lem_9 {A s i} (e : i < length s)
  (u : |[nth 0 [seq x.+1 | x <- s] i]| -> A) : |[(nth 0 s i).+1]| -> A := u.
Next Obligation.
  assert (i < length [seq x0.+1 | x0 <- s]);[by rewrite map_length|].
  replace (nth _ _ _) with (lnth [seq x0.+1 | x0 <- s] (exist _ i H0)).
  by rewrite lnth_map (lnth_nth 0).
  by rewrite (lnth_nth 0).
Qed.

Program Definition FO_Prenex_Correct_Lem_9_0 {A s i} (e : i < length s)
  (u : |[(nth 0 s i).+1]| -> A) : |[nth 0 [seq x.+1 | x <- s] i]| -> A := u.
Next Obligation.
  assert (i < length [seq x0.+1 | x0 <- s]);[by rewrite map_length|].
  replace (nth _ _ _) with (lnth [seq x0.+1 | x0 <- s] (exist _ i H0)) in H.
  by rewrite lnth_map (lnth_nth 0) in H.
  by rewrite (lnth_nth 0).
Qed.

Theorem FO_Prenex_Correct (p : FirstOrderFormula) (M : Sigma11Model) :
  FirstOrder_Denote p M <-> PrenexDenotation (FO_Prenex p) M.
Proof.
  move: M; elim: p.
  - apply ZO_Prenex_Correct.
  - move=> p f IH M.
    split.
    + move=> H.
      simpl.
      unfold PrenexDenotation.
      simpl in H.
      remember (Poly_Denote p M) as PM.
      destruct PM;[|fcrush].
      destruct H as [r [ltrs fd]].
      apply ((IH (AddModelV M r)).1) in fd; clear IH.
      unfold PrenexDenotation in fd.
      destruct fd as [adv [H0 [H1 H2]]].
      exists (AdviceExtend r adv).
      split;[|split];auto.
      * by apply (FO_Prenex_Correct_PrenexFormulaCondition_Exi p).
      * apply (FO_Prenex_Correct_PrenexFOBoundCondition_Exi p).
        split; auto.
        move=> n.
        unfold InBound.
        rewrite PolyTermVSCastCastId; rewrite <- PolyTerm_PolyTermVS_Correct.
        by rewrite <- HeqPM.
      * by apply (FO_Prenex_Correct_PrenexSOBoundCondition_Exi p).
    + move=> [adv [H0 [H1 H2]]].
      simpl in adv.
      rewrite (AdviceDropExi_Spec adv) in H0, H1, H2.
      apply (FO_Prenex_Correct_PrenexFormulaCondition_Exi p) in H0.
      apply (FO_Prenex_Correct_PrenexFOBoundCondition_Exi p) in H1.
      apply (FO_Prenex_Correct_PrenexSOBoundCondition_Exi p) in H2.
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
          PrenexDenotation (FO_Prenex f) (AddModelV M r)) as FO';[qauto|clear IH FO].
      unfold PrenexDenotation in *.
      assert (
        forall r : {r : 'F_FSize | lt r s},
        exists a : PrenexAdvice (nu (FO_Prenex f)),
          PrenexFormulaCondition (FO_Prenex f) (AddModelV M (` r)) a /\
          PrenexFOBoundCondition (FO_Prenex f) (AddModelV M (` r)) a /\
          PrenexSOBoundCondition (FO_Prenex f) (AddModelV M (` r)) a) as FO;[qauto|clear FO'].
      apply choice in FO.
      destruct FO as [adv H].
      exists {| exiVAdv :=  Uni_Advice (fun x => exiVAdv _ _ (adv x))
              ; exiFAdv := fun _ _ _ => None |}.
      split;[|split].
      * unfold PrenexFormulaCondition.
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
        unfold PrenexFormulaCondition in H; simpl in H.
        assert (forall j v,
              InBound M
                {|
                  exiVAdv := Uni_Advice (fun x => exiVAdv (nu (FO_Prenex f)) (adv x));
                  exiFAdv := exiFAdv _ (adv (exist ((lt)^~ s) (u (exist _ 0 (ltn0Sn _))) ltuE))
                |} (u j)
                (nth PolyZeroVS
                  (uniBounds (PrenexAddUni (PolyTerm_PolyTermVS p) (FO_Prenex f)))
                  (` j)) (MakeU u v)) as ltuX.
              clear H ; move=> [j ltj] v; simpl in *.
              remember (ltu (exist _ j ltj) v) as ltu'; clear Heqltu'.
              unfold InBound in *; simpl in *.
              destruct j; simpl in *.
              by rewrite PolyTermVSCastCastId; rewrite PolyTermVSCastCastId in ltu'.
              change (PolyZeroVS (nu := [seq x.+1 | x <- nu (FO_Prenex f)]))
              with (LiftPolyUni (nu := nu (FO_Prenex f)) PolyZeroVS) in ltu'.
              change (PolyZeroVS (nu := [seq x.+1 | x <- nu (FO_Prenex f)]))
              with (LiftPolyUni (nu := nu (FO_Prenex f)) PolyZeroVS).
              rewrite nth_map; rewrite nth_map in ltu'.
              remember (PolyVSDenotation _ _ _ _ _) as PD0.
              replace (PolyVSDenotation _ _ _ _ _) with PD0.
              destruct PD0; auto; simpl in *.
              rewrite HeqPD0; clear HeqPD0 PD0 ltu'.
              do 2 rewrite <- (FO_Prenex_Correct_Lem_7_0 (nth PolyZeroVS (uniBounds (FO_Prenex f)) j)).
              apply FO_Prenex_Correct_Lem_8.
        assert (forall j v, InBound (AddModelV M (u (exist _ 0 (ltn0Sn _))))
               (adv (exist ((lt)^~ s) (u (exist _ 0 (ltn0Sn _))) ltuE)) (fSeqRest u j)
               (nth PolyZeroVS (uniBounds (FO_Prenex f)) (` j)) (MakeU (fSeqRest u) v)) as ltu0.
              clear H ; move=> [j ltj] v; simpl in *.
              assert (j.+1 < (length (uniBounds (FO_Prenex f))).+1) as ltj2;[clear ltu ltuX ltuE PM adv v u s M p; sfirstorder|].
              remember (ltuX (exist _ (j.+1) ltj2) v) as ltu'; clear Heqltu'.
              unfold InBound in *; simpl in *.
              change (PolyZeroVS (nu := [seq x.+1 | x <- nu (FO_Prenex f)]))
              with (LiftPolyUni (nu := nu (FO_Prenex f)) PolyZeroVS) in ltu'.
              rewrite nth_map in ltu'.
              remember (PolyVSDenotation _ _ _ _ _) as PD0.
              replace (PolyVSDenotation _ _ _ _ _) with PD0.
              destruct PD0; auto; simpl in *.
              replace (fSeqRest u (exist _ j ltj))
                with (u (exist _ j.+1 ltj2)); auto.
              unfold fSeqRest; simpl; apply f_equal; by apply subset_eq_compat.
              rewrite HeqPD0; clear HeqPD0 PD0 ltu'.
              by rewrite <- FO_Prenex_Correct_Lem_4_0_1.
        remember (H (exist _ (fSeqRest u) ltu0)) as H'; clear HeqH' H; simpl in H'.
        rewrite <- (FO_Prenex_Correct_Lem_5_5 (exiF1 := exiFAdv (nu (FO_Prenex f))
          (adv (exist ((lt)^~ s) (u (exist _ 0 (ltn0Sn _))) ltuE)))).
        by rewrite <- FO_Prenex_Correct_Lem_4_0_2.
      * unfold PrenexFOBoundCondition=> i [u ltu] n; simpl in *.
        destruct i as [i lti].
        assert (i < length (nu (FO_Prenex f))) as lti2;[clear u ltu; by rewrite map_length in lti|].
        assert (nth 0 [seq x.+1 | x <- nu (FO_Prenex f)] i 
                = (nth 0 (nu (FO_Prenex f)) i).+1).
          transitivity (lnth [seq x.+1 | x <- nu (FO_Prenex f)] (exist _ i lti));[by rewrite (lnth_nth 0)|].
          by rewrite lnth_map (lnth_nth 0); f_equal.
        remember (PrenexFOBoundCondition_obligation_1 _ _ _ _ _ _) asDD; clear HeqDDD.
        change PolyZeroVS with (LiftPolyUni (nu := nu (FO_Prenex f)) PolyZeroVS); rewrite nth_map.
        assert (0 < nth 0 [seq x.+1 | x <- nu (FO_Prenex f)] i) as lt0;[by rewrite H0|].
        assert (lt (u (exist _ 0 lt0)) s) as ltuE.
          remember (ltu (exist _ 0 lt0) (fun=> 0%R)) as ltu'; clear Heqltu' ltu.
          simpl in ltu'.
          unfold InBound in ltu'.
          rewrite PolyTermVSCastCastId in ltu'.
          rewrite <- PolyTerm_PolyTermVS_Correct in ltu'.
          by rewrite PM in ltu'.
        remember (H (exist _ (u (exist _ 0 lt0)) ltuE)) as H'; clear HeqH' H.
        destruct H' as [_ [H _]]; simpl in H.
        unfold PrenexFOBoundCondition in H.
        remember (FO_Prenex_Correct_Lem_9 lti2 u) as u'.
        assert (lt (u' (exist _ 0 (ltn0Sn (nth 0 (nu (FO_Prenex f)) i)))) s) as ltuE2.
          rewrite Hequ'; unfold FO_Prenex_Correct_Lem_9; simpl.
          remember (lt _ _ _) as L1; replace (lt _ _ _) with L1;auto;rewrite HeqL1.
          do 2 f_equal; by apply subset_eq_compat.
        assert (forall j v, InBound (AddModelV M (u (exist _ 0 lt0)))
                 (adv (exist ((lt)^~ s) (u (exist _ 0 lt0)) ltuE)) (fSeqRest u' j)
                 (nth PolyZeroVS (uniBounds (FO_Prenex f)) (` j))
                 (MakeU (fSeqRest u') v)) as ltu2.
                move=> [j ltj] v.
                simpl.
                clear HDD.
                simpl in *.
                assert (j.+1 < nth 0 [seq x.+1 | x <- nu (FO_Prenex f)] i) as ltj2;[by rewrite H0|].
                remember (ltu (exist _ (j.+1) ltj2) v) as ltu'; clear Heqltu' ltu.
                unfold InBound in *.
                remember (PolyVSDenotation _ _ _ _ _) as P0.
                replace (PolyVSDenotation _ _ _ _ _) with P0.
                destruct P0; auto.
                replace (fSeqRest u' _) with (u (exist _ j.+1 ltj2)); auto.
                rewrite Hequ'.
                unfold FO_Prenex_Correct_Lem_9, fSeqRest; simpl.
                f_equal; by apply subset_eq_compat.
                rewrite HeqP0; clear ltu' HeqP0 P0.
                simpl.
                change (PolyZeroVS (nu := [seq x.+1 | x <- nu (FO_Prenex f)]))
                with (LiftPolyUni (nu := nu (FO_Prenex f)) PolyZeroVS). 
                rewrite nth_map.
                remember (adv _) as adv'.
                assert (adv' = adv (exist ((lt)^~ s) (u' (exist _ 0 (ltn0Sn _))) ltuE2)).
                  rewrite Heqadv'; f_equal; apply subset_eq_compat.
                  rewrite Hequ'; unfold FO_Prenex_Correct_Lem_9; f_equal; by apply subset_eq_compat.
                transitivity (PolyVSDenotation
                  (LiftPolyUni (nth PolyZeroVS (uniBounds (FO_Prenex f)) j)) M
                  {| exiVAdv := Uni_Advice (fun x => exiVAdv (nu (FO_Prenex f)) (adv x));
                    exiFAdv := exiFAdv _ _ (adv (exist ((lt)^~ s) (u' (exist _ 0 (ltn0Sn _))) ltuE2))
                  |} (MakeU u v));[by apply FO_Prenex_Correct_Lem_8_5|].
                replace (MakeU u v) with (MakeU u' v).
                rewrite <- FO_Prenex_Correct_Lem_4_0_1.
                f_equal; auto.
                f_equal; rewrite Hequ'; unfold FO_Prenex_Correct_Lem_9; f_equal; by apply subset_eq_compat.
                rewrite Hequ'.
                unfold FO_Prenex_Correct_Lem_9.
                apply functional_extensionality=> x.
                unfold MakeU.
                dep_if_case (x < (nth 0 (nu (FO_Prenex f)) i).+1); auto.
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
        assert (exist (fun n0 : nat => n0 < length (nu (FO_Prenex f))) i lti2 =
                exist _ i (Uni_Advice_obligation_2 (nu (FO_Prenex f)) s (exist _ i lti) (fun x => u (exist _ (` x) (DDD x))) Hyp0))as e;[
        by apply subset_eq_compat|].
        apply (exiVAdvEqLem e)=> x.
        remember (PrenexFOBoundCondition_obligation_1 _ _ _ _ _ _ _) asDD0; clear HeqDDD0.
        unfold fSeqRest; rewrite Hequ'; unfold FO_Prenex_Correct_Lem_9.
        f_equal; apply subset_eq_compat; simpl.
        by rewrite projT1_eq_rect.
        f_equal; apply subset_eq_compat; f_equal; by apply subset_eq_compat.
        rewrite HeqP0; clear H' HeqP0 P0.
        transitivity (PolyVSDenotation
          (LiftPolyUni (nth PolyZeroVS (exiVBounds (FO_Prenex f)) i)) M
          {| exiVAdv := Uni_Advice (fun x => exiVAdv (nu (FO_Prenex f)) (adv x));
             exiFAdv := exiFAdv _ _ (adv (exist ((lt)^~ s) (u' (exist _ 0 (ltn0Sn _))) ltuE2))
          |} (MakeU u n)).
        replace (MakeU u n) with (MakeU u' n).
        rewrite <- FO_Prenex_Correct_Lem_4_0_1.
        do 2 f_equal.
        rewrite Hequ'; unfold FO_Prenex_Correct_Lem_9; f_equal; by apply subset_eq_compat.
        apply subset_eq_compat; rewrite Hequ'; unfold FO_Prenex_Correct_Lem_9; f_equal; by apply subset_eq_compat.
        apply functional_extensionality=> x.
        rewrite Hequ'; unfold MakeU.
        dep_if_case (x < (nth 0 (nu (FO_Prenex f)) i).+1); auto.
        rewrite dep_if_case_true;[by rewrite H0|]=> Hyp0.
        unfold FO_Prenex_Correct_Lem_9; f_equal; by apply subset_eq_compat.
        by rewrite dep_if_case_false;rewrite H0.
        apply FO_Prenex_Correct_Lem_10_5.
      * unfold PrenexFOBoundCondition; simpl=> u [i lti]; simpl.
        assert (i < 0);[|fcrush].
        assert (length (exiFInputBounds (FO_Prenex f)) = 0) as LE0.
        clear adv H i lti.
        elim: f; try qauto.
        move=> p0 f IH; simpl; by rewrite map_length.
        move=> p0 f IH; simpl; by rewrite map_length.
        simpl in lti.
        rewrite map_length in lti.
        by rewrite LE0 in lti.
  - move=> [adv [H0 [H1 H2]]] r ltrs.
    apply IH; clear IH.
    unfold PrenexDenotation.
    exists (AdviceDropUni r adv).
    split;[|split].
    + clear H1 H2.
      move=> [u ltu]; simpl.
      unfold PrenexFormulaCondition in H0.
      unfold U in H0.
      simpl in H0.
      remember (ExtendAt0N r u) as u'.
      rewrite map_length in H0.
      assert (forall j v, InBound M adv (u' j) (nth PolyZeroVS
                (PolyTermVSCast (PolyTerm_PolyTermVS p)
                  :: [seq LiftPolyUni i | i <- uniBounds (FO_Prenex f)]) 
                (` j)) (MakeU u' v)) as ltu'.
              move=> [j ltj] v.
              rewrite Hequ'; destruct j; unfold ExtendAt0N, MakeU; simpl; auto.
              unfold InBound.
              rewrite PolyTermVSCastCastId; rewrite <- PolyTerm_PolyTermVS_Correct.
              by rewrite PM.
              unfold InBound.
              change PolyZeroVS with (LiftPolyUni (nu := nu (FO_Prenex f)) PolyZeroVS).
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
              rewrite FO_Prenex_Correct_Lem_7_0_A.
              f_equal.
              unfold ExtendAt0; apply functional_extensionality=> x.
              destruct x; simpl; auto.
              unfold MakeU.
              dep_if_case (x < length (uniBounds (FO_Prenex f))); auto.
              rewrite dep_if_case_true; auto.
              f_equal; by apply subset_eq_compat.
              rewrite dep_if_case_false; auto.
      remember (H0 (exist _ u' ltu')) as H; clear HeqH H0; simpl in H.
      rewrite FO_Prenex_Correct_Lem_7_A.
      rewrite Hequ' in H.
      replace (ExtendAt0 r (MakeU u (fun=> 0%R)))
         with (MakeU (ExtendAt0N r u) (fun=> 0%R)); auto.
      unfold MakeU, ExtendAt0; apply functional_extensionality=> x.
      destruct x; auto; simpl.
      dep_if_case (x < length (uniBounds (FO_Prenex f))); auto.
      unfold ExtendAt0N; simpl.
      rewrite dep_if_case_true; auto.
      f_equal; by apply subset_eq_compat.
      rewrite dep_if_case_false; auto.
    + clear H0 H2.
      move=> [i lti] [u ltu] n; simpl.
      remember (FO_Prenex_Correct_Lem_9_0 lti (ExtendAt0N r u)) as u'.
      simpl in H1.
      assert (i < length [seq x.+1 | x <- nu (FO_Prenex f)]) as lti2.
        by rewrite map_length.
      assert (nth 0 [seq x0.+1 | x0 <- nu (FO_Prenex f)] i =
              (nth 0 (nu (FO_Prenex f)) i).+1) as HH.
          replace (nth 0 [seq x.+1 | x <- nu (FO_Prenex f)] i)
            with (lnth [seq x.+1 | x <- nu (FO_Prenex f)] (exist _ i lti2)).
          by rewrite lnth_map (lnth_nth 0).
          by rewrite (lnth_nth 0).
      assert (forall (j : |[nth 0 [seq x.+1 | x <- nu (FO_Prenex f)] i]|) v, InBound M adv (u' j) (nth PolyZeroVS
              (PolyTermVSCast (PolyTerm_PolyTermVS p) :: [seq LiftPolyUni i
                          | i <- uniBounds (FO_Prenex f)]) 
                   (` j)) (MakeU u' v)) as ltu'.
              move=> [j ltj] v.
              rewrite Hequ'; destruct j; unfold ExtendAt0N, MakeU; simpl; auto.
              unfold InBound.
              rewrite PolyTermVSCastCastId; rewrite <- PolyTerm_PolyTermVS_Correct.
              by rewrite PM.
              unfold InBound.
              change PolyZeroVS with (LiftPolyUni (nu := nu (FO_Prenex f)) PolyZeroVS).
              rewrite nth_map.
              simpl in ltu.
              assert (j < nth 0 (nu (FO_Prenex f)) i) as ltj2;[by rewrite HH in ltj|].
              remember (ltu (exist _ j ltj2) v) as ltu2; clear Heqltu2 ltu.
              simpl in ltu2.
              unfold InBound in ltu2.
              remember (PolyVSDenotation _ _ _ _ _) as PD0.
              replace (PolyVSDenotation _ _ _ _ _) with PD0.
              destruct PD0;auto.
              replace (FO_Prenex_Correct_Lem_9_0 _ _ _)
                 with (u (exist (fun n : nat => n < nth 0 (nu (FO_Prenex f)) i) j ltj2)); auto.
              unfold FO_Prenex_Correct_Lem_9_0; simpl.
              f_equal; by apply subset_eq_compat.
              rewrite HeqPD0; clear HeqPD0 PD0 ltu2.
              rewrite FO_Prenex_Correct_Lem_7_0_A.
              f_equal.
              unfold ExtendAt0; apply functional_extensionality=> x.
              destruct x; simpl; auto.
              rewrite dep_if_case_true; auto; by rewrite HH.
              unfold MakeU.
              dep_if_case (x < nth 0 (nu (FO_Prenex f)) i); auto.
              rewrite dep_if_case_true; auto;[by rewrite HH|].
              move=> Hyp.
              unfold FO_Prenex_Correct_Lem_9_0; simpl.
              f_equal; by apply subset_eq_compat.
              rewrite dep_if_case_false; auto;by rewrite HH.
      remember (H1 (exist _ i lti2) (exist _ u' ltu') n) as H; clear HeqH H1; simpl in H.
      unfold InBound in *.
      rewrite FO_Prenex_Correct_Lem_7_0_A.
      change PolyZeroVS with (LiftPolyUni (nu := nu (FO_Prenex f)) PolyZeroVS) in H.
      rewrite nth_map in H.
      replace (MakeU u' n) with (ExtendAt0 r (MakeU u n)) in H.
      destruct (PolyVSDenotation _ _ _ _ _); auto.
      remember (exiVAdv _ _ _ _ _) as E.
      replace (exiVAdv _ _ _ _ _) with E; auto.
      rewrite HeqE; clear H HeqE E.
      assert (exist (fun n0 : nat => n0 < length [seq x.+1 | x <- nu (FO_Prenex f)]) i lti2 
            = (exist _ i (AdviceDropUni_obligation_1 (nu (FO_Prenex f)) (exist _ i lti)
              (fun x => u (exist _  (` x) (PrenexFOBoundCondition_obligation_1 
              (FO_Prenex f) (AddModelV M r) (AdviceDropUni r adv)
              (exist _ i lti) (exist _ u ltu) x))))) ) as e;[by apply subset_eq_compat|].
      apply (exiVAdvEqLem e)=> x; destruct x; simpl.
      remember (exist _ x _) asDD.
      rewrite Hequ' HeqDDD; clear HeqDDDDD.
      unfold FO_Prenex_Correct_Lem_9_0; simpl.
      remember (FO_Prenex_Correct_Lem_9_0_obligation_1 _ _ _ _) asDD; clear HeqDDD; simpl inDD.
      unfold ExtendAt0N; destruct x; simpl;[rewrite dep_if_case_true|rewrite dep_if_case_false];auto;
        change (exist _ ?x _ == exist _ ?y _) with (x == y).
      by rewrite projT1_eq_rect.
      by rewrite projT1_eq_rect.
      simpl=> Hyp.
      f_equal; apply subset_eq_compat; by rewrite projT1_eq_rect.
      rewrite Hequ'; unfold MakeU, ExtendAt0, ExtendAt0N; apply functional_extensionality=>x.
      destruct x; simpl; auto.
      unfold FO_Prenex_Correct_Lem_9_0; simpl.
      by rewrite HH.
      dep_if_case (x < nth 0 (nu (FO_Prenex f)) i); auto.
      rewrite dep_if_case_true; auto;[by rewrite HH|].
      move=> Hyp.
      unfold FO_Prenex_Correct_Lem_9_0; simpl.
      f_equal; by apply subset_eq_compat.
      rewrite dep_if_case_false; auto;by rewrite HH.
    + move => u [i lti].
      assert (length (exiFInputBounds (FO_Prenex f)) = 0).
      clear adv H0 H1 H2 PM lti.
      elim: f; try qauto.
      move=> p0 f IH; simpl; by rewrite map_length.
      move=> p0 f IH; simpl; by rewrite map_length.
      assert (i < 0);[by rewrite H in lti|fcrush].
    + move=> _.
      unfold PrenexDenotation.
      exists {| exiVAdv := fun x t => 0%R; exiFAdv := fun x a v => None |}.
      split;[|split].
      * move=> [u ltu]; simpl.
        simpl in ltu.
        remember (ltu (exist _ 0 (ltn0Sn _)) (fun _ => 0%R)) as ltu'; clear Heqltu' ltu.
        unfold InBound in ltu'; simpl in ltu'.
        rewrite PolyTermVSCastCastId in ltu'; rewrite <- PolyTerm_PolyTermVS_Correct in ltu'.
        by rewrite PM in ltu'.
      * move=> [i lti] [u ltu]; simpl; simpl in ltu.
        assert (0 < nth 0 [seq x.+1 | x <- nu (FO_Prenex f)] i) as lt0.
        replace (nth 0 [seq x.+1 | x <- nu (FO_Prenex f)] i)
            with (lnth [seq x.+1 | x <- nu (FO_Prenex f)] (exist _ i lti)).
          by rewrite lnth_map (lnth_nth 0).
          by rewrite (lnth_nth 0).
        remember (ltu (exist _ 0 lt0) (fun _ => 0%R)) as ltu'; clear Heqltu' ltu.
        unfold InBound in ltu'; simpl in ltu'.
        rewrite PolyTermVSCastCastId in ltu'; rewrite <- PolyTerm_PolyTermVS_Correct in ltu'.
        by rewrite PM in ltu'.
      * move => u [i lti].
        assert (length (exiFInputBounds (FO_Prenex f)) = 0).
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
  (n : Prenex) : 
  Prenex :=
  {| nu := nu n
   ; uniBounds := map LiftPolyExi (uniBounds n)
   ; exiVBounds := map LiftPolyExi (exiVBounds n)
   ; exiFOutputBounds := PolyTermVSCast y :: map LiftPolyExi (exiFOutputBounds n)
   ; exiFInputBounds := map PolyTermVSCast bs :: map (map LiftPolyExi) (exiFInputBounds n)
   ; formula := LiftPropExi (formula n)
  |}.

Fixpoint SO_Prenex (f : SecondOrderFormula) : Prenex :=
  match f with
  | FO f => FO_Prenex f
  | SOExists y bs f => 
    AddExiFBound (PolyTerm_PolyTermVS y)
                 (map PolyTerm_PolyTermVS bs)
                 (SO_Prenex f)
  end.

Program Definition AdviceExiFExtend {b}
  (f : (|[b]| -> 'F_FSize) -> option ('F_FSize))
  {nu} (adv : PrenexAdvice nu) : 
  PrenexAdvice nu :=
  {| exiVAdv := exiVAdv _ _ adv
   ; exiFAdv := fun i a => 
      if i == 0
      then (if a == b as B return (a == b = B -> (|[a]| -> 'F_FSize) -> option ('F_FSize))
            then fun _ => f
            else fun _ _ => None) (erefl _)
      else exiFAdv _ _ adv (i.-1) a
  |}.
Next Obligation. apply EEConvert in e; by destruct e. Qed.

Program Definition SO_Prenex_Correct_Lem_1 {A B} {f : A -> B} {s : seq A}
  (u : |[length [seq f i | i <- s]]| -> 'F_FSize) : |[length s]| -> 'F_FSize := u.
Next Obligation. by rewrite map_length. Qed.

Lemma SO_Prenex_Correct_Lem_2 {M nu u p a f adv} :
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

Lemma SO_Prenex_Correct_Lem_2_0 {M nu u p a f adv} :
  PrenexZODenotation (nu := nu) _ (LiftPropExi p) M (AdviceExiFExtend f adv) u
  = PrenexZODenotation _ p (AddModelExiF _ a f M) adv u.
Proof.
  elim: p; try qauto.
  move=> p0 p1.
  simpl.
  by do 2 rewrite SO_Prenex_Correct_Lem_2.
Qed.

(* 
Lemma SO_Prenex_Correct_PrenexSOBoundCondition_Exi
  (p : PolyTerm) (f : FirstOrderFormula) (M : Sigma11Model) a f :
  ((forall n, InBound M (AdviceExiFExtend f a) r (PolyTermVSCast (PolyTerm_PolyTermVS y)) n) /\
   (forall n, InBound M (AdviceExiFExtend f a) r (PolyTermVSCast (PolyTerm_PolyTermVS p)) n)
   /\ PrenexSOBoundCondition (SO_Prenex f) (AddModelV M r) a) <->
  PrenexSOBoundCondition (SO_Prenex (SOExists y bs f)) M (AdviceExiFExtend f a).
Proof.
  split.
  - move=> [H0 H1] [i lti] u n0.
Qed. *)

(* Theorem SO_Prenex_Correct_Lem_3 {y M a s} {f : (|[a]| -> 'F_FSize) -> option ('F_FSize)} :
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

Lemma SO_Prenex_Correct_Lem_4 {A a b x ltx ltx2}
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
  {nu} (adv : PrenexAdvice nu) : 
  PrenexAdvice nu :=
  {| exiVAdv := exiVAdv _ _ adv
   ; exiFAdv := fun i a => 
      if i == 0
      then f a
      else exiFAdv _ _ adv (i.-1) a
  |}.

Program Definition AdviceDropExiF {nu}
  (adv : PrenexAdvice nu) :=
  {| exiVAdv := exiVAdv _ adv
   ; exiFAdv := fun i => exiFAdv _ adv (i.+1) 
  |}.

Theorem AdviceDropExiF_Spec_1 {nu}
  (adv : PrenexAdvice nu) :
  adv = 
  (AdviceExiFExtendA (exiFAdv _ adv 0)
                     (AdviceDropExiF adv)).
Proof.
  destruct adv; f_equal; simpl.
  unfold AdviceDropExiF, AdviceExiFExtendA; simpl; f_equal.
  apply functional_extensionality;move=> [|i]; auto.
Qed.

Theorem AdviceDropExiF_Spec_2 {nu a f} 
  (adv : PrenexAdvice nu) :
  adv = 
  (AdviceDropExiF (AdviceExiFExtend (b := a) f adv)).
Proof.
  destruct adv; f_equal; simpl.
  unfold AdviceDropExiF, AdviceExiFExtendA; simpl; f_equal.
Qed.

Lemma SO_Prenex_Correct_Lem_2_A {M nu u p f adv} :
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

Lemma SO_Prenex_Correct_Lem_2_B {M nu u p adv} :
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

Lemma SO_Prenex_Correct_Lem_2_C {M nu u p adv d} :
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


(* Lemma SO_Prenex_Correct_Lem_2_C {M nu u p adv d} :
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
Lemma SO_Prenex_Correct_Lem_2_B {M nu u p adv} :
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

Theorem SO_Prenex_Correct (p : SecondOrderFormula) (M : Sigma11Model) :
  SecondOrder_Denote p M <-> PrenexDenotation (SO_Prenex p) M.
Proof.
  move: M; elim: p;[apply FO_Prenex_Correct|].
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
      unfold PrenexDenotation.
      simpl.
      destruct H as [adv [H0 [H1 H2]]].
      exists (AdviceExiFExtend f adv).
      split;[|split].
      * clear H1 H2.
        unfold PrenexFormulaCondition in *.
        move=> [u ltu]; simpl.
        unfold AddExiFBound in u; simpl in u.
        unfold AddExiFBound in ltu; simpl in ltu.
        remember (SO_Prenex_Correct_Lem_1 u) as u'.
        assert (forall j v, InBound (AddModelExiF (length bs) f M) adv 
                  (u' j) (nth PolyZeroVS (uniBounds (SO_Prenex s)) (` j))
                  (MakeU u' v)) as ltu'.
                move=> [j ltj] v.
                assert (j < length [seq LiftPolyExi i | i <- uniBounds (SO_Prenex s)]) as ltj2;[by rewrite map_length|].
                remember (ltu (exist _ j ltj2) v) as ltu'; clear Heqltu' ltu; simpl in ltu'.
                unfold InBound in *; simpl in *.
                replace (MakeU u' v) with (MakeU u v).
                change PolyZeroVS  with (LiftPolyExi (nu := nu (SO_Prenex s)) PolyZeroVS) in ltu'.
                rewrite nth_map in ltu'.
                rewrite <- SO_Prenex_Correct_Lem_2.
                destruct (PolyVSDenotation _ _ _ _ _); auto.
                replace (u' _) with (u (exist _ j ltj2)); auto.
                rewrite Hequ'; unfold SO_Prenex_Correct_Lem_1; f_equal; by apply subset_eq_compat.
                unfold MakeU.
                apply functional_extensionality=> x.
                dep_if_case (x < length (uniBounds (SO_Prenex s))); auto.
                by rewrite map_length.
                move=> HHH; rewrite dep_if_case_true.
                rewrite Hequ'; unfold SO_Prenex_Correct_Lem_1; f_equal; by apply subset_eq_compat.
                by rewrite map_length.
                rewrite dep_if_case_false; auto.
                by rewrite map_length.
        remember (H0 (exist _ u' ltu')) as H; clear H0 HeqH; simpl in H.
        rewrite SO_Prenex_Correct_Lem_2_0.
        replace (MakeU u (fun=> 0%R)) with (MakeU u' (fun=> 0%R)); auto.
        rewrite Hequ'.
        unfold MakeU; apply functional_extensionality=> x.
        dep_if_case (x < length (uniBounds (SO_Prenex s))); auto.
        rewrite dep_if_case_true;[by rewrite map_length|].
        move=> HHH; unfold SO_Prenex_Correct_Lem_1; f_equal; by apply subset_eq_compat.
        rewrite dep_if_case_false; auto.
        by rewrite map_length.
      * clear H0 H2.
        unfold PrenexFOBoundCondition in *.
        move=> [i lti] [u ltu] n; simpl in *.
        assert (forall j v, InBound (AddModelExiF (length bs) f M) adv 
                (u j) (nth PolyZeroVS (uniBounds (SO_Prenex s)) (` j))
                (MakeU u v)) as ltu2.
            move=> j v; remember (ltu j v) as ltu'; clear Heqltu'.
            change PolyZeroVS  with (LiftPolyExi (nu := nu (SO_Prenex s)) PolyZeroVS) in ltu'.
            rewrite nth_map in ltu'.
            unfold InBound in *.
            by rewrite <- SO_Prenex_Correct_Lem_2.
        remember (H1 (exist _ i lti) (exist _ u ltu2) n) as H; clear HeqH H1; simpl in H.
        unfold InBound in *.
        change PolyZeroVS with (LiftPolyExi (nu := nu (SO_Prenex s)) PolyZeroVS).
        rewrite nth_map.
        rewrite SO_Prenex_Correct_Lem_2.
        destruct (PolyVSDenotation _ _ _ _); auto.
        remember (PrenexFOBoundCondition_obligation_1 _ _ _ _ _ _) asD0; clear HeqDD0.
        remember (PrenexFOBoundCondition_obligation_1 _ _ _ _ _ _) asD1; clear HeqDD1.
        simpl in *.
        replaceD1 withD0; auto.
        apply functional_extensionality_dep=>x; apply eq_irrelevance.
      * clear H0 H1.
        unfold PrenexSOBoundCondition in *.
        move=> u [[|i] lti]; simpl in *;[clear H2|].
        rewrite PolyTermVSCastCastId; rewrite <- PolyTerm_PolyTermVS_Correct.
        rewrite PMy; simpl.
        assert (length bs = length [seq (PolyTermVSCast (nu := nu (SO_Prenex s))) i | i <- [seq PolyTerm_PolyTermVS i | i <- bs]]) as HH;[by do 2 rewrite map_length|].
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
        apply SO_Prenex_Correct_Lem_4.
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
        change PolyPlusOneVS with (LiftPolyExi (nu := nu (SO_Prenex s)) PolyPlusOneVS).
        rewrite nth_map.
        rewrite SO_Prenex_Correct_Lem_2.
        assert (i < length (exiFInputBounds (SO_Prenex s))) as lti2;[by rewrite map_length in lti|].
        remember (H2 u (exist _ i lti2)) as H; clear HeqH H2; simpl in H.
        destruct (PolyVSDenotation _ _ adv u); auto.
        assert (length (lnth (exiFInputBounds (SO_Prenex s)) (exist _ i lti2))
          = length (lnth [seq [seq LiftPolyExi i | i <- i] | i <- exiFInputBounds (SO_Prenex s)] (exist _ i lti))).
          rewrite lnth_map map_length; do 2 f_equal; by apply subset_eq_compat.
        remember (option_fun
        (fun j => PolyVSDenotation (lnth (lnth (exiFInputBounds (SO_Prenex s))
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
        assert (x < length (lnth (exiFInputBounds (SO_Prenex s)) (exist _ i lti2))) as ltx2;[by rewrite H0|].
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
                  (lnth (exiFInputBounds (SO_Prenex s))
                      (exist _ i lti2)) (eq_rect _ (fun x : nat => |[x]|) j _ (esym H0))) 
                (AddModelExiF (length bs) f M) adv u)).
        remember (length (lnth _ (exist _ i lti))) as a; clear Heqa; by destruct H0.
        f_equal; apply functional_extensionality;move=> [x ltx].
        rewrite <- SO_Prenex_Correct_Lem_2.
        f_equal. 
        pose ([seq LiftPolyExi i0
            | i0 <- lnth (exiFInputBounds (SO_Prenex s))
                      (exist _ i 
                          (Utils.lnth_map_obligation_1 (seq PolyTermVS)
                            (seq PolyTermVS) [eta map [eta LiftPolyExi]]
                            (exiFInputBounds (SO_Prenex s)) (exist _ i lti)))]) as L1.
        assert (x < length L1) as ltx3.
          rewrite lnth_map map_length in ltx.
          by rewrite map_length.
        transitivity (lnth L1 (exist _ x ltx3));[
          |do 2 rewrite (lnth_nth PolyZeroVS); f_equal; by rewrite lnth_map].
        transitivity (LiftPolyExi
          (lnth (lnth (exiFInputBounds (SO_Prenex s))
          (exist _ i (Utils.lnth_map_obligation_1 _ _ _ _ (exist _ i lti))))
          (exist _ x (Utils.lnth_map_obligation_1 _ _ _ (lnth (exiFInputBounds (SO_Prenex s))
          (exist _ i (Utils.lnth_map_obligation_1 _ _ _ _ (exist _ i lti))))
          (exist _ x ltx3)))));[|by rewrite lnth_map].
        f_equal.
        do 2 rewrite (lnth_nth PolyZeroVS); do 2 f_equal;[
          by apply subset_eq_compat|by rewrite projT1_eq_rect].
  + move=> H; simpl.
    destruct H as [adv [H0 [H1 H2]]].
    unfold PrenexSOBoundCondition in H2.
    remember (H2 (fun _ => 0%R) (exist _ 0 (ltn0Sn _))) as H2_0; clear HeqH2_0; simpl in H2_0.
    rewrite PolyTermVSCastCastId in H2_0; rewrite <- PolyTerm_PolyTermVS_Correct in H2_0.
    destruct (Poly_Denote y M) eqn: PMy;[|fcrush].
    assert (length [seq PolyTermVSCast (nu := (nu (SO_Prenex s))) i | i <- [seq PolyTerm_PolyTermVS i | i <- bs]]
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
    unfold PrenexDenotation.
    (* rewrite (AdviceDropExiF_Spec adv) in H0 H1 H2; clear H2_0. *)
    exists (AdviceDropExiF adv).
    split;[|split].
    + clear H1 H2. 
      unfold PrenexFormulaCondition; unfold PrenexFormulaCondition in H0.
      do 2 rewrite map_length; simpl in *.
      move=> [u ltu]; simpl.
      (* unfold U in H0. *)
      rewrite map_length in H0.
      assert (forall (j : {n : nat | n < length (uniBounds (SO_Prenex s))})
               (v : nat -> 'F_FSize),
             InBound M adv (u j)
               (nth PolyZeroVS
                  (uniBounds
                     (AddExiFBound (PolyTerm_PolyTermVS y)
                        [seq PolyTerm_PolyTermVS i | i <- bs] 
                        (SO_Prenex s))) (` j)) (MakeU u v)).
      move=> j v.
      remember (ltu j v) as ltu'; clear Heqltu' ltu.
      unfold InBound in *.
      change PolyZeroVS with (LiftPolyExi (nu := nu (SO_Prenex s)) PolyZeroVS).
      rewrite nth_map.
      rewrite <- SO_Prenex_Correct_Lem_2_C in ltu'.
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
      rewrite (AdviceDropExiF_Spec adv); rewrite SO_Prenex_Correct_Lem_2_A.
      rewrite <- SO_Prenex_Correct_Lem_2_A in ltu'.
    unfold SO_Bound_Check. qauto.
    move=> ins out hyp.
    remember (H2_0 ins out hyp).
    simpl.



    destruct (Poly_Denote y M) eqn: PMy.
    destruct (option_fun (fun m => Poly_Denote (lnth bs m) M)) eqn:PMbs.
    destruct H as [adv [H0 [H1 H2]]].
    exists (exiFAdv _ _ adv 0 (length bs)).
    unfold PrenexDenotation in H.





End PrenexCorrect.
