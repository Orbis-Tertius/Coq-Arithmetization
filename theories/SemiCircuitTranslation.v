From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import CoqArith.Sigma_1_1.
Require Import CoqArith.SemiCircuit.
Require Import Program.

Section SemicircuitTranslation.

(*Convert constraint to one over context with additional function calls*)
Program Fixpoint PolyCallCastFree {ctx}
  {newC : |[freeFS ctx]| -> nat}
  (p : @SemicircuitPolyConstraint ctx) :
  @SemicircuitPolyConstraint {| subCtx := subCtx ctx
                              ; freeFC := fun x => freeFC ctx x + newC x 
                              ; exiFC := exiFC ctx
                              ; indC := indC ctx
  |} := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyCallCastFree p1 in
    let r2 := PolyCallCastFree p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyCallCastFree p1 in
    let r2 := PolyCallCastFree p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd i => PolyConsInd i
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsExiV i => PolyConsExiV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF i j
  end.
Next Obligation. qauto use: ltn_addr. Qed.

Program Fixpoint PolyCallCastExi {ctx}
  {newC : |[exiFS ctx]| -> nat}
  (p : @SemicircuitPolyConstraint ctx) :
  @SemicircuitPolyConstraint {| subCtx := subCtx ctx
                              ; freeFC := freeFC ctx
                              ; exiFC := fun x => exiFC ctx x + newC x
                              ; indC := indC ctx
  |} := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyCallCastExi p1 in
    let r2 := PolyCallCastExi p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyCallCastExi p1 in
    let r2 := PolyCallCastExi p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd i => PolyConsInd i
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsExiV i => PolyConsExiV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF i j
  end.
Next Obligation. qauto use: ltn_addr. Qed.

Program Fixpoint PolyCallCastInd {ctx}
  {newC : nat}
  (p : @SemicircuitPolyConstraint ctx) :
  @SemicircuitPolyConstraint {| subCtx := subCtx ctx
                              ; freeFC := freeFC ctx
                              ; exiFC := exiFC ctx
                              ; indC := indC ctx + newC
  |} := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyCallCastInd p1 in
    let r2 := PolyCallCastInd p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyCallCastInd p1 in
    let r2 := PolyCallCastInd p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd i => PolyConsInd i
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsExiV i => PolyConsExiV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF i j
  end.
Next Obligation. qauto use: ltn_addr. Qed.

Program Fixpoint PolyCallCast {ctx}
    {newFC : |[freeFS ctx]| -> nat}
    {newEC : |[exiFS ctx]| -> nat}
    {newIC : nat}
    (p : @SemicircuitPolyConstraint ctx) :
  @SemicircuitPolyConstraint {| subCtx := subCtx ctx
                              ; freeFC := fun x => freeFC ctx x + newFC x
                              ; exiFC := fun x => exiFC ctx x + newEC x
                              ; indC := indC ctx + newIC
  |} := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyCallCast p1 in
    let r2 := PolyCallCast p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyCallCast p1 in
    let r2 := PolyCallCast p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd i => PolyConsInd i
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsExiV i => PolyConsExiV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF i j
  end.
Solve All Obligations with qauto use: ltn_addr.

(*Lift new polynomial args so names don't conflict with arguments from other polynomials *)
Program Fixpoint PolyCallLift {ctx}
    {newFC : |[freeFS ctx]| -> nat}
    {newEC : |[exiFS ctx]| -> nat}
    {newIC : nat}
    (p : @SemicircuitPolyConstraint ctx) :
  @SemicircuitPolyConstraint {| subCtx := subCtx ctx
                              ; freeFC := fun x => newFC x + freeFC ctx x
                              ; exiFC := fun x => newEC x +  exiFC ctx x
                              ; indC := newIC + indC ctx
  |} := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyCallLift p1 in
    let r2 := PolyCallLift p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyCallLift p1 in
    let r2 := PolyCallLift p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd i => PolyConsInd (newIC + i)
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsExiV i => PolyConsExiV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i (newFC i + j)
  | PolyConsExiF i j => PolyConsExiF i (newEC i + j)
  end.
Solve All Obligations with qauto use: ltn_add2l.

Record PolyConversionData {ctx : Sigma11Ctx} : Type := mkPolyConvertData {
  newFreeFCalls : |[freeF ctx]| -> nat ;
  newExiFCalls : |[exiF ctx]| -> nat ;
  newIndCalls : nat ;
  newPolys : seq (@SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls; exiFC := newExiFCalls; indC := newIndCalls |}) ;
  newFreeArgs : forall (i : |[freeF ctx]|), |[newFreeFCalls i]| -> |[freeFA ctx i]| -> |[length newPolys]| ;
  newExiArgs : forall (i : |[exiF ctx]|), |[newExiFCalls i]| -> |[exiFA ctx i]| -> |[length newPolys]| ;
  newIndArgs : |[newIndCalls]| -> (|[length newPolys]| * |[length newPolys]|)
  }.

Definition PolyConversionEmptyData {ctx}: 
  @PolyConversionData ctx :=
  {| newFreeFCalls := fun _ => 0; newExiFCalls := fun _ => 0; newIndCalls := 0; newPolys := [::]
   ; newFreeArgs := fun x => emptyTuple; newExiArgs := fun x => emptyTuple; newIndArgs := emptyTuple|}.

Program Definition PolyConversionCombineData {ctx}
  (d1 d2 : @PolyConversionData ctx) : @PolyConversionData ctx :=
  match d1, d2 with
  | {| newFreeFCalls := nffc1; newExiFCalls := nefc1; newIndCalls := nic1; newPolys := polys1; newFreeArgs := farg1; newExiArgs := earg1; newIndArgs := iarg1 |}
  , {| newFreeFCalls := nffc2; newExiFCalls := nefc2; newIndCalls := nic2; newPolys := polys2; newFreeArgs := farg2; newExiArgs := earg2; newIndArgs := iarg2 |}
  => let poly' := map PolyCallCast polys1 ++ map PolyCallLift polys2 in
   {| newFreeFCalls := fun x => nffc1 x + nffc2 x
    ; newExiFCalls := fun x => nefc1 x + nefc2 x
    ; newIndCalls := nic1 + nic2
    ; newPolys := poly'
    ; newFreeArgs := fun i j => (
      if j < nffc1 i as b return j < nffc1 i = b -> |[freeFA ctx i]| -> |[length poly']|
      then fun _ => farg1 i j
      else fun _ => farg2 i (j - nffc1 i)
    ) (erefl _)
    ; newExiArgs := fun i j => (
      if j < nefc1 i as b return j < nefc1 i = b -> |[exiFA ctx i]| -> |[length poly']|
      then fun _ => earg1 i j
      else fun _ => earg2 i (j - nefc1 i)
    ) (erefl _) 
    ; newIndArgs := fun i => (
      if i < nic1 as b return i < nic1 = b -> (|[length poly']| * |[length poly']|)
      then fun _ => iarg1 i
      else fun _ => iarg2 (i - nic1)
    ) (erefl _) 
  |}
  end.
Next Obligation.
  rewrite length_cat map_length map_length.
  by destruct (farg1 _); apply ltn_addr.
Qed.
Next Obligation.
  assert (~ (j < nffc1 (exist _ i H0)));[hauto|].
  assert (nffc1 (exist _ i H0) <= j);[by apply (contra_not_leq (P := j < nffc1 (exist _ i H0)))|].
  qauto use: ltn_subLR, ltn_addr.
Qed.
Next Obligation.
  rewrite length_cat map_length map_length.
  by destruct (farg2 _); apply ltn_addl.
Qed.
Next Obligation.
  rewrite length_cat map_length map_length.
  by destruct (earg1 _); apply ltn_addr.
Qed.
Next Obligation.
  assert (~ (j < nefc1 (exist _ i H0)));[hauto|].
  assert (nefc1 (exist _ i H0) <= j);[by apply (contra_not_leq (P := j < nefc1 (exist _ i H0)))|].
  qauto use: ltn_subLR, ltn_addr.
Qed.
Next Obligation.
  rewrite length_cat map_length map_length.
  by destruct (earg2 _); apply ltn_addl.
Qed.
Next Obligation.
  rewrite length_cat map_length map_length.
  by destruct ((iarg1 _).1); apply ltn_addr.
Qed.
Next Obligation.
  rewrite length_cat map_length map_length.
  by destruct ((iarg1 _).2); apply ltn_addr.
Qed.
Next Obligation.
  assert (nic1 <= i);[
  hauto use: contraFltn, contra_not_leq unfold: is_true|qauto use: ltn_subLR, contraFltn].
Qed.
Next Obligation.
  rewrite length_cat map_length map_length.
  by destruct ((iarg2 _).1); apply ltn_addl.
Qed.
Next Obligation.
  rewrite length_cat map_length map_length.
  by destruct ((iarg2 _).2); apply ltn_addl.
Qed.

Program Definition PolyFuseCoerce {ctx : Sigma11Ctx} {d1 d2 : @PolyConversionData ctx} 
  (s : @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := fun x => newFreeFCalls d1 x + newFreeFCalls d2 x
                                                  ; exiFC := fun x => newExiFCalls d1 x + newExiFCalls d2 x
                                                  ; indC := newIndCalls d1 + newIndCalls d2 |}) :
  @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls (PolyConversionCombineData d1 d2)
                                             ; exiFC := newExiFCalls (PolyConversionCombineData d1 d2)
                                             ; indC := newIndCalls (PolyConversionCombineData d1 d2) |} := s.
Next Obligation. by f_equal; destruct d1, d2. Qed.

(*Fuse sequence of poly conversion outputs into a single output. *)
Program Fixpoint PolyCallSeqFuse {ctx : Sigma11Ctx} 
  (s : seq { d : @PolyConversionData ctx &  
    @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d; indC := newIndCalls d |} }) :
  { d : @PolyConversionData ctx &
    {t : seq (@SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d; indC := newIndCalls d |}) | length t = length s} } :=
  match s with
  | [::] => existT _ PolyConversionEmptyData [::]
  | (existT b x) :: xs => 
    let (d, p) := PolyCallSeqFuse xs in
    let d0 := PolyConversionCombineData b d in
    let p0 := map PolyFuseCoerce (PolyCallCast x :: map PolyCallLift p) in
    existT _ d0 p0
  end.
Next Obligation. by rewrite map_length map_length. Qed.

(*Call for a single function*)
Definition SingleCall {FN} (i : |[FN]|) (j : |[FN]|) : nat :=
  (if j == i as b return (j == i) = b -> nat 
   then fun _ => 1
   else fun _ => 0) (erefl _).

(*Add new call to a function*)
Definition AddCall {FN} (FCalls : |[FN]| -> nat) (j : |[FN]|) : |[FN]| -> nat :=
  fun i => FCalls i + SingleCall j i.

(*Add polynomial addresses from a new to call function*)
Program Definition AddPolys {FN} {n} {m} (FCalls : |[FN]| -> nat) (FArity : |[FN]| -> nat)
  (j : |[FN]|) (k : |[FArity j]| -> |[m]|)
  (freeCalls : forall (i : |[FN]|), |[FCalls i]| -> |[FArity i]| -> |[n]|)
  (i : |[FN]|) : |[AddCall FCalls j i]| -> |[FArity i]| -> |[n + m]| := (
    if i == j as b return (i == j) = b -> |[AddCall FCalls j i]| -> |[FArity i]| -> |[n + m]| 
    then fun _ c => (
      (*If we're looking at the last call*)
      if c == FCalls i as b return (c == FCalls i) = b -> |[FArity i]| -> |[n + m]|
      then fun _ x => n + k x
      else fun _ => freeCalls i c
      ) (erefl _)
    else fun _ => freeCalls i
  ) (erefl _).
Next Obligation.
  unfold AddCall in H.
  unfold SingleCall in H.
  rewrite dep_if_case_false in H; auto.
  remember (FCalls _) as F; clear HeqF.
  replace (F + 0) with F in H; auto.
  clear k; hauto use: addSn, add1n, addSnnS, addn1 inv: nat.
Qed.
Next Obligation. destruct (freeCalls _); hauto use: ltn_addr. Qed.
Next Obligation.
  unfold AddCall, SingleCall.
  rewrite dep_if_case_true; auto.
  remember (FCalls _) as F; clear HeqF.
  replace (F + 1) with (F.+1);[sfirstorder|hauto use: addn1].
Qed.
Next Obligation.
  apply EEFConvert in e0; simpl in e0.
  unfold AddCall, SingleCall in H; rewrite dep_if_case_true in H; auto.
  remember (FCalls _) as F; clear HeqF.
  move: F e0 H;elim: c;[move=>[|F];hauto|]=>c IH [|F] e0 H;auto.
  apply IH; auto.
Qed.
Next Obligation. destruct (freeCalls _); hauto use: ltn_addr. Qed.
Next Obligation.
  clear e0; apply EEConvert, (subset_eq_compat _ (fun n : nat => n < FN) _ _ H1 H2) in e; hauto.
Qed.
Next Obligation. by destruct (k _); rewrite ltn_add2l. Qed.

(*Add a list of circuit constraints associated to a free fun call to data*)
Program Definition FreeCallIncorp {ctx}
  (d : @PolyConversionData ctx) (i : |[freeF ctx]|) :
  forall s : seq (@SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d; indC := newIndCalls d |}),
  length s = freeFA ctx i -> @PolyConversionData ctx :=
  match d with
  | {| newFreeFCalls := nffc; newExiFCalls := nefc; newIndCalls := nic; newPolys := plys; newFreeArgs := farg; newExiArgs := earg; newIndArgs := iarg |} =>
    fun ps ls =>
    {| newFreeFCalls := AddCall nffc i
    ;  newExiFCalls := nefc
    ;  newIndCalls := nic
    ;  newPolys := map (PolyCallCastFree (newC := SingleCall i)) (plys ++ ps)
    ;  newFreeArgs := AddPolys nffc (freeFA ctx) i (cRangeFun 0 (freeFA ctx i)) farg 
    ;  newExiArgs := earg
    ;  newIndArgs := iarg |}
  end.
Next Obligation.
  destruct (AddPolys _ _ _ _ _ _); simpl.
  rewrite map_length length_cat.
  by rewrite ls.
Qed.
Next Obligation.
  destruct (earg _ _ _); simpl.
  rewrite map_length length_cat.
  hauto use: ltnW, ltn_addr, ltnS.
Qed.
Next Obligation.
  destruct (iarg _); simpl.
  rewrite map_length length_cat.
  hauto use: ltnW, ltn_addr, ltnS.
Qed.
Next Obligation.
  destruct (iarg _); simpl.
  rewrite map_length length_cat.
  hauto use: ltnW, ltn_addr, ltnS.
Qed.

(*Add a list of circuit constraints associated to an exi fun call to data*)
Program Definition ExiCallIncorp {ctx}
  (d : @PolyConversionData ctx) (i : |[exiF ctx]|) :
  forall s : seq (@SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d; indC := newIndCalls d |}),
  length s = exiFA ctx i ->
  @PolyConversionData ctx :=
  match d with
  | {| newFreeFCalls := nffc; newExiFCalls := nefc; newIndCalls := nic; newPolys := plys; newFreeArgs := farg; newExiArgs := earg; newIndArgs := iarg |} =>
    fun ps ls =>
    {| newFreeFCalls := nffc
    ;  newExiFCalls := AddCall nefc i
    ;  newIndCalls := nic
    ;  newPolys := map (PolyCallCastExi (newC := SingleCall i)) (plys ++ ps)
    ;  newFreeArgs := farg 
    ;  newExiArgs := AddPolys nefc (exiFA ctx) i (cRangeFun 0 (exiFA ctx i)) earg
    ;  newIndArgs := iarg |}
  end.
Next Obligation.
  destruct (farg _ _ _); simpl.
  rewrite map_length length_cat.
  hauto use: ltnW, ltn_addr, ltnS.
Qed.
Next Obligation.
  destruct (AddPolys _ _ _ _ _ _); simpl.
  rewrite map_length length_cat.
  by rewrite ls.
Qed.
Next Obligation.
  destruct (iarg _); simpl.
  rewrite map_length length_cat.
  hauto use: ltnW, ltn_addr, ltnS.
Qed.
Next Obligation.
  destruct (iarg _); simpl.
  rewrite map_length length_cat.
  hauto use: ltnW, ltn_addr, ltnS.
Qed.

Program Definition PolyConvertFreeCase {ctx} 
  (i : |[freeF ctx]|) 
  (t : |[freeFA ctx i]| ->
    { d : @PolyConversionData ctx &  
    @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d; indC := newIndCalls d |} }) :
  { d : @PolyConversionData ctx &  
    @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d; indC := newIndCalls d |} } := 
  let (data, polys) := PolyCallSeqFuse [seq t i | i <- cRange 0 (freeFA ctx i) ] in
  let data2 : @PolyConversionData ctx := FreeCallIncorp data i polys _ in
  existT _ data2 (PolyConsFreeF i (newFreeFCalls data i)).
Next Obligation. by rewrite map_length (length_cRange (n := 0)) in H. Qed.
Next Obligation.
  destruct data; simpl.
  unfold AddCall.
  unfold SingleCall.
  rewrite dep_if_case_true;[by rewrite EEConvert|].
  hauto use: ltnSn, addn1, contra_ltn_leq.
Qed.

Program Definition PolyConvertExiCase {ctx} 
  (i : |[exiF ctx]|) 
  (t : |[exiFA ctx i]| ->
    { d : @PolyConversionData ctx &  
    @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d; indC := newIndCalls d |} }) :
  { d : @PolyConversionData ctx &  
    @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d; indC := newIndCalls d |} } :=
  let (data, polys) := PolyCallSeqFuse [seq t i | i <- cRange 0 (exiFA ctx i) ] in
  let data2 : @PolyConversionData ctx := ExiCallIncorp data i polys _ in
  existT _ data2 (PolyConsExiF i (newExiFCalls data i)).
Next Obligation. by rewrite map_length (length_cRange (n := 0)) in H. Qed.
Next Obligation.
  destruct data; simpl.
  unfold AddCall.
  unfold SingleCall.
  rewrite dep_if_case_true;[by rewrite EEConvert|].
  hauto use: ltnSn, addn1, contra_ltn_leq.
Qed.

(*Add a list of circuit constraints associated to an ind call to data*)
Program Definition IndCallIncorp {ctx}
  (d : @PolyConversionData ctx) :
  (@SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d; indC := newIndCalls d |}) ->
  (@SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d; indC := newIndCalls d |}) ->
  @PolyConversionData ctx :=
  match d with
  | {| newFreeFCalls := nffc; newExiFCalls := nefc; newIndCalls := nic; newPolys := plys; newFreeArgs := farg; newExiArgs := earg; newIndArgs := iarg |} =>
    fun p1 p2 =>
    let poly' := map (PolyCallCastInd (newC := 1)) (rcons (rcons plys p1) p2) in
    {| newFreeFCalls := nffc
    ;  newExiFCalls := nefc
    ;  newIndCalls := nic + 1
    ;  newPolys := poly'
    ;  newFreeArgs := farg 
    ;  newExiArgs := earg
    ;  newIndArgs := fun i => (
        if i == nic as b return (i == nic) = b -> (|[length poly']| * |[length poly']|)
        then fun _ => (length plys, (length plys).+1)
        else fun _ => iarg i
     ) (erefl _) |}
  end.
Next Obligation.
  destruct (farg _ _ _); simpl.
  rewrite map_length length_rcons length_rcons.
  hauto use: ltnW, ltn_addr, ltnS.
Qed.
Next Obligation.
  destruct (earg _ _ _); simpl.
  rewrite map_length length_rcons length_rcons.
  hauto use: ltnW, ltn_addr, ltnS.
Qed.
Next Obligation.
  hauto use: addn1, Utils.cRange_obligation_1.
Qed.
Next Obligation.
  assert (i <> nic);[by rewrite <- EEFConvert|].
  assert (i < nic.+1);[scongruence use: addn1, add1n|].
  by apply leq_neq_lt.
Qed.
Next Obligation.
  destruct (iarg _); simpl.
  rewrite map_length length_rcons length_rcons.
  hauto use: ltnW, ltn_addr, ltnS.
Qed.
Next Obligation.
  destruct (iarg _); simpl.
  rewrite map_length length_rcons length_rcons.
  hauto use: ltnW, ltn_addr, ltnS.
Qed.
Next Obligation.
  rewrite map_length length_rcons length_rcons.
  apply ltnSn.
Qed.
Next Obligation.
  rewrite map_length length_rcons length_rcons.
  apply ltnW, ltnSn.
Qed.

(*Construct a polynomial constraint, new calls within that constraint, simultanious with data to modify a semicircuit *)
Program Fixpoint PolyConvert {ctx} (r : @PolyTerm ctx) :
  { d : @PolyConversionData ctx &  
    @SemicircuitPolyConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d; indC := newIndCalls d |} } := 
  match r with
  | PolyFVar m => existT _ PolyConversionEmptyData (PolyConsFreeV m)
  | PolyEVar m => existT _ PolyConversionEmptyData (PolyConsExiV m)
  | PolyUVar m => existT _ PolyConversionEmptyData (PolyConsUniV m)
  | PolyFFun i t => PolyConvertFreeCase i (fun x => PolyConvert (t x))
  | PolyEFun i t => PolyConvertExiCase i (fun x => PolyConvert (t x))
  | PolyMinusOne => existT _ PolyConversionEmptyData PolyConsMinusOne
  | PolyPlusOne => existT _ PolyConversionEmptyData PolyConsPlusOne
  | PolyZero => existT _ PolyConversionEmptyData PolyConsZero
  | PolyPlus r1 r2 => 
    let (d1, p1) := PolyConvert r1 in
    let (d2, p2) := PolyConvert r2 in
    existT _ (PolyConversionCombineData d1 d2)
             (PolyConsPlus (PolyCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) (newIC := newIndCalls d2) p1) 
                           (PolyCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) (newIC := newIndCalls d1) p2))
  | PolyTimes r1 r2 => 
    let (d1, p1) := PolyConvert r1 in
    let (d2, p2) := PolyConvert r2 in
    existT _ (PolyConversionCombineData d1 d2)
             (PolyConsTimes (PolyCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) (newIC := newIndCalls d2) p1) 
                            (PolyCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) (newIC := newIndCalls d1) p2))
  | PolyInd r1 r2 => 
    let (d1, p1) := PolyConvert r1 in
    let (d2, p2) := PolyConvert r2 in
    let d3 := PolyConversionCombineData d1 d2 in
    let d4 := IndCallIncorp d3 
                (PolyCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) (newIC := newIndCalls d2) p1) 
                (PolyCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) (newIC := newIndCalls d1) p2) in
    existT _ d4 (PolyConsInd (newIndCalls d3))
  end.
Next Obligation. by f_equal; try apply functional_extensionality;try move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; try apply functional_extensionality;try move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; try apply functional_extensionality;try move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; try apply functional_extensionality;try move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; try apply functional_extensionality;try move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; try apply functional_extensionality;try move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. destruct d1, d2; apply Utils.cRange_obligation_1. Qed.

(*Convert constraint to one with new function with no calls*)
Fixpoint PropCallCast {ctx}
    {newFC : |[freeFS ctx]| -> nat}
    {newEC : |[exiFS ctx]| -> nat}
    {newIC : nat}
    (p : @SemicircuitPropConstraint ctx) :
    @SemicircuitPropConstraint {| subCtx := subCtx ctx
                               ; freeFC := fun x => freeFC ctx x + newFC x
                               ; exiFC := fun x => exiFC ctx x + newEC x
                               ; indC := indC ctx + newIC|} := 
  match p with
  | ZOConsNot p =>
    let r := PropCallCast p in
    ZOConsNot r
  | ZOConsAnd p1 p2 =>
    let r1 := PropCallCast p1 in
    let r2 := PropCallCast p2 in
    ZOConsAnd r1 r2
  | ZOConsOr p1 p2 =>
    let r1 := PropCallCast p1 in
    let r2 := PropCallCast p2 in
    ZOConsOr r1 r2
  | ZOConsImp p1 p2 =>
    let r1 := PropCallCast p1 in
    let r2 := PropCallCast p2 in
    ZOConsImp r1 r2
  | ZOConsEq p1 p2 =>
    let r1 := PolyCallCast p1 in
    let r2 := PolyCallCast p2 in
    ZOConsEq r1 r2
  end.

Fixpoint PropCallLift {ctx}
    {newFC : |[freeFS ctx]| -> nat}
    {newEC : |[exiFS ctx]| -> nat}
    {newIC : nat}
    (p : @SemicircuitPropConstraint ctx) :
    @SemicircuitPropConstraint {| subCtx := subCtx ctx
                               ; freeFC := fun x => newFC x + freeFC ctx x
                               ; exiFC := fun x => newEC x + exiFC ctx x
                               ; indC := newIC + indC ctx|} := 
  match p with
  | ZOConsNot p =>
    let r := PropCallLift p in
    ZOConsNot r
  | ZOConsAnd p1 p2 =>
    let r1 := PropCallLift p1 in
    let r2 := PropCallLift p2 in
    ZOConsAnd r1 r2
  | ZOConsOr p1 p2 =>
    let r1 := PropCallLift p1 in
    let r2 := PropCallLift p2 in
    ZOConsOr r1 r2
  | ZOConsImp p1 p2 =>
    let r1 := PropCallLift p1 in
    let r2 := PropCallLift p2 in
    ZOConsImp r1 r2
  | ZOConsEq p1 p2 =>
    let r1 := PolyCallLift p1 in
    let r2 := PolyCallLift p2 in
    ZOConsEq r1 r2
  end.

(*Construct a proposition constraint, new calls within that constraint, simultanious with data to modify a semicircuit *)
Program Fixpoint PropConvert {ctx} (r : @ZerothOrderFormula ctx) :
  { d : @PolyConversionData ctx &  
    @SemicircuitPropConstraint {| subCtx := ctx; freeFC := newFreeFCalls d; exiFC := newExiFCalls d; indC := newIndCalls d |} } := 
  match r with
  | ZONot f => 
    let (d, p) := PropConvert f in
    existT _ d (ZOConsNot p)
  | ZOAnd f1 f2 => 
    let (d1, p1) := PropConvert f1 in
    let (d2, p2) := PropConvert f2 in
    existT _ (PolyConversionCombineData d1 d2)
             (ZOConsAnd (PropCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) (newIC := newIndCalls d2) p1) 
                        (PropCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) (newIC := newIndCalls d1) p2))
  | ZOOr f1 f2 => 
    let (d1, p1) := PropConvert f1 in
    let (d2, p2) := PropConvert f2 in
    existT _ (PolyConversionCombineData d1 d2)
             (ZOConsOr (PropCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) (newIC := newIndCalls d2) p1) 
                       (PropCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) (newIC := newIndCalls d1) p2))
  | ZOImp f1 f2 => 
    let (d1, p1) := PropConvert f1 in
    let (d2, p2) := PropConvert f2 in
    existT _ (PolyConversionCombineData d1 d2)
             (ZOConsImp (PropCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) (newIC := newIndCalls d2) p1) 
                        (PropCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) (newIC := newIndCalls d1) p2))
  | ZOEq r1 r2 => 
    let (d1, p1) := PolyConvert r1 in
    let (d2, p2) := PolyConvert r2 in
    existT _ (PolyConversionCombineData d1 d2)
             (ZOConsEq (PolyCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) (newIC := newIndCalls d2) p1) 
                       (PolyCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) (newIC := newIndCalls d1) p2))
  end.
Next Obligation. by f_equal; try apply functional_extensionality;try move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; try apply functional_extensionality;try move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; try apply functional_extensionality;try move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; try apply functional_extensionality;try move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; try apply functional_extensionality;try move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; try apply functional_extensionality;try move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; try apply functional_extensionality;try move=>[x ltx];destruct d1, d2. Qed.
Next Obligation. by f_equal; try apply functional_extensionality;try move=>[x ltx];destruct d1, d2. Qed.

(*Integrate generated polynomial constraint data into a semicircuit*)
Program Definition IntegrateConversionData
  (c : SemiCircuit)
  (d : @PolyConversionData (subCtx (Ctx c))) : SemiCircuit :=
  let Ctx' := {| subCtx := subCtx (Ctx c) 
              ; freeFC := fun x => freeFCalls c x + newFreeFCalls d x
              ; exiFC := fun x => exiFCalls c x + newExiFCalls d x
              ; indC := indCalls c + newIndCalls d |} in
  let poly' := map (PolyCallCast) (polyConstraints c) ++ map PolyCallLift (newPolys d) in
  {| Ctx := Ctx'
   ; nu := nu c
   ; polyConstraints := poly'
   ; indArgs := fun i =>
     (if i < indCalls c as b return (i < indCalls c) = b -> (|[length poly']| * |[length poly']|)
      then fun _ => indArgs c i
      else fun _ => let (a, b) := newIndArgs d (i - indCalls c) in
        (length (polyConstraints c) + a, length (polyConstraints c) + b)) (erefl _)
   ; freeFArgs := fun i (j : |[freeFCalls c i + newFreeFCalls d i]|) =>
     (if j < freeFCalls c i as b return (j < freeFCalls c i) = b -> |[freeFArity c i]| -> |[length poly']|
     then fun _ => freeFArgs c i j
     else fun _ x => length (polyConstraints c) 
                   + newFreeArgs d i (j - freeFCalls c i) x) (erefl _)
   ; exiFArgs := fun i (j : |[exiFCalls c i + newExiFCalls d i]|) =>
     (if j < exiFCalls c i as b return (j < exiFCalls c i) = b -> |[exiFArity c i]| -> |[length poly']|
     then fun _ => exiFArgs c i j
     else fun _ x => length (polyConstraints c) 
                   + newExiArgs d i (j - exiFCalls c i) x) (erefl _)
   ; uniVBounds := uniVBounds c
   ; exiVBounds := exiVBounds c
   ; exiFOutputBounds := exiFOutputBounds c
   ; exiFInputBounds := exiFInputBounds c
   ; formula := inrMap PropCallCast (formula c)
  |}.
Next Obligation.
  destruct (indArgs _ _).
  rewrite length_cat map_length map_length.
  qauto use: leq_addl, ltn_addr, addSnnS.
Qed.
Next Obligation.
  destruct (indArgs _ _).
  rewrite length_cat map_length map_length.
  qauto use: leq_addl, ltn_addr, addSnnS.
Qed.
Next Obligation.
  remember (newIndCalls d) as n; clear Heqn.
  remember (indCalls c) as m; clear Heqm.
  assert (m <= i);[qauto use: contra_not_leq unfold: is_true|clear e].
  hauto use: ltn_subLR.
Qed.
Next Obligation.
  rewrite length_cat map_length map_length.
  remember (length (polyConstraints c)) as n; clear Heqn.
  remember (length (newPolys d)) as m; clear Heqm.
  scongruence use: ltn_add2l.
Qed.
Next Obligation.
  rewrite length_cat map_length map_length.
  remember (length (polyConstraints c)) as n; clear Heqn.
  remember (length (newPolys d)) as m; clear Heqm.
  scongruence use: ltn_add2l.
Qed.
Next Obligation.
  destruct (freeFArgs _ _).
  rewrite length_cat map_length map_length.
  qauto use: leq_addl, ltn_addr, addSnnS.
Qed.
Next Obligation.
  remember (freeFCalls _ _) as F; clear HeqF.
  by assert (~ (j < F));[ hauto
                        | assert (F <= j);[ apply (contra_not_leq (P := j < F))
                                          | qauto use: ltn_subLR]].
Qed.
Next Obligation.
  destruct (newFreeArgs _ _).
  rewrite length_cat map_length map_length.
  by rewrite ltn_add2l.
Qed.
Next Obligation.
  destruct (exiFArgs _ _).
  rewrite length_cat map_length map_length.
  by apply ltn_addr.
Qed.
Next Obligation.
  remember (exiFCalls _ _) as F; clear HeqF.
  by assert (~ (j < F));[ hauto
                        | assert (F <= j);[ apply (contra_not_leq (P := j < F))
                                          | qauto use: ltn_subLR]].
Qed.
Next Obligation.
  destruct (newExiArgs _ _).
  rewrite length_cat map_length map_length.
  simpl.
  by rewrite ltn_add2l.
Qed.
Next Obligation. 
  destruct (uniVBounds _ _).
  rewrite length_cat map_length map_length.
  by apply ltn_addr.
Qed.
Next Obligation. 
  destruct (exiVBounds _ _).
  rewrite length_cat map_length map_length.
  by apply ltn_addr.
Qed.
Next Obligation. 
  destruct (exiFOutputBounds _ _).
  rewrite length_cat map_length map_length.
  by apply ltn_addr.
Qed.
Next Obligation. 
  destruct (exiFInputBounds _ _).
  rewrite length_cat map_length map_length.
  by apply ltn_addr.
Qed.

Definition Translate_ZerothOrderFormula 
  (c : SemiCircuit)
  (f : @ZerothOrderFormula (subCtx (Ctx c))) : SemiCircuit :=
  let (d, p) := PropConvert f in
  let c0 := IntegrateConversionData c d in
  {| Ctx := Ctx c0
   ; nu := nu c0
   ; polyConstraints := polyConstraints c0
   ; indArgs := indArgs c0
   ; freeFArgs := freeFArgs c0
   ; exiFArgs := exiFArgs c0
   ; uniVBounds := uniVBounds c0
   ; exiVBounds := exiVBounds c0
   ; exiFOutputBounds := exiFOutputBounds c0
   ; exiFInputBounds := exiFInputBounds c0
   ; formula := inr (PropCallLift p)
  |}.

Program Fixpoint PolyLiftExiV {ctx}
  (p : @SemicircuitPolyConstraint ctx) :
    @SemicircuitPolyConstraint {| subCtx := incExiV (subCtx ctx)
                                ; freeFC := freeFC ctx
                                ; exiFC := exiFC ctx
                                ; indC := indC ctx|} := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyLiftExiV p1 in
    let r2 := PolyLiftExiV p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyLiftExiV p1 in
    let r2 := PolyLiftExiV p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd i => PolyConsInd i
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsExiV i => PolyConsExiV i.+1
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF i j
  end.
Next Obligation. by destruct (subCtx ctx). Qed. Next Obligation. by destruct (subCtx ctx). Qed.
Next Obligation. by unfold freeVS in *; simpl; destruct (subCtx ctx). Qed. 
Next Obligation. by unfold exiVS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation. by unfold uniVS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation. by clear H; unfold freeFS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation.
  remember (PolyLiftExiV_obligation_1 _ _) as P; clear HeqP; simpl in P.
  replace P with H0; auto.
  apply eq_irrelevance.
Qed.
Next Obligation. by clear H; unfold exiFS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation.
  remember (PolyLiftExiV_obligation_2 _ _) as P; clear HeqP; simpl in P.
  replace P with H0; auto.
  apply eq_irrelevance.
Qed.

Program Fixpoint PropLiftExiV {ctx}
  (p : @SemicircuitPropConstraint ctx) :
  @SemicircuitPropConstraint {| subCtx := incExiV (subCtx ctx)
                              ; freeFC := freeFC ctx
                              ; exiFC := exiFC ctx
                                ; indC := indC ctx|} := 
  match p with
  | ZOConsNot p =>
    let r := PropLiftExiV p in
    ZOConsNot r
  | ZOConsAnd p1 p2 =>
    let r1 := PropLiftExiV p1 in
    let r2 := PropLiftExiV p2 in
    ZOConsAnd r1 r2
  | ZOConsOr p1 p2 =>
    let r1 := PropLiftExiV p1 in
    let r2 := PropLiftExiV p2 in
    ZOConsOr r1 r2
  | ZOConsImp p1 p2 =>
    let r1 := PropLiftExiV p1 in
    let r2 := PropLiftExiV p2 in
    ZOConsImp r1 r2
  | ZOConsEq p1 p2 =>
    let r1 := PolyLiftExiV p1 in
    let r2 := PolyLiftExiV p2 in
    ZOConsEq r1 r2
  end.

Program Fixpoint PolyLiftUniV {ctx}
  (p : @SemicircuitPolyConstraint ctx) :
    @SemicircuitPolyConstraint {| subCtx := incUniV (subCtx ctx)
                                ; freeFC := freeFC ctx
                                ; exiFC := exiFC ctx
                                ; indC := indC ctx|} := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyLiftUniV p1 in
    let r2 := PolyLiftUniV p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyLiftUniV p1 in
    let r2 := PolyLiftUniV p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd i => PolyConsInd i
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsExiV i => PolyConsExiV i
  | PolyConsUniV i => PolyConsUniV i.+1
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF i j
  end.
Next Obligation. by destruct (subCtx ctx). Qed. Next Obligation. by destruct (subCtx ctx). Qed.
Next Obligation. by unfold freeVS in *; simpl; destruct (subCtx ctx). Qed. 
Next Obligation. by unfold exiVS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation. by unfold uniVS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation. by clear H; unfold freeFS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation.
  remember (PolyLiftUniV_obligation_1 _ _) as P; clear HeqP; simpl in P.
  replace P with H0; auto.
  apply eq_irrelevance.
Qed.
Next Obligation. by clear H; unfold exiFS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation.
  remember (PolyLiftUniV_obligation_2 _ _) as P; clear HeqP; simpl in P.
  replace P with H0; auto.
  apply eq_irrelevance.
Qed.

Program Fixpoint PropLiftUniV {ctx}
  (p : @SemicircuitPropConstraint ctx) :
  @SemicircuitPropConstraint {| subCtx := incUniV (subCtx ctx)
                              ; freeFC := freeFC ctx
                              ; exiFC := exiFC ctx
                              ; indC := indC ctx|} := 
  match p with
  | ZOConsNot p =>
    let r := PropLiftUniV p in
    ZOConsNot r
  | ZOConsAnd p1 p2 =>
    let r1 := PropLiftUniV p1 in
    let r2 := PropLiftUniV p2 in
    ZOConsAnd r1 r2
  | ZOConsOr p1 p2 =>
    let r1 := PropLiftUniV p1 in
    let r2 := PropLiftUniV p2 in
    ZOConsOr r1 r2
  | ZOConsImp p1 p2 =>
    let r1 := PropLiftUniV p1 in
    let r2 := PropLiftUniV p2 in
    ZOConsImp r1 r2
  | ZOConsEq p1 p2 =>
    let r1 := PolyLiftUniV p1 in
    let r2 := PolyLiftUniV p2 in
    ZOConsEq r1 r2
  end.

(*Add a new existentially quantified first order variable to semicircuit *)
Program Definition SemicircuitExiInc (c : SemiCircuit) (p : @SemicircuitPolyConstraint (Ctx c)): SemiCircuit :=
  {| Ctx := {| subCtx := incExiV (subCtx (Ctx c))
              ; freeFC := freeFC (Ctx c)
              ; exiFC := exiFC (Ctx c)
              ; indC := indC (Ctx c)|}
  ; nu := fun i =>
    (if i == 0 as b return (i == 0) = b -> nat
     then fun _ => uniV (subCtx (Ctx c))
     else fun _ => nu c (i.-1)) (erefl _)
  ; polyConstraints := map PolyLiftExiV (rcons (polyConstraints c) p)
  ; freeFArgs := freeFArgs c
  ; exiFArgs := exiFArgs c
  ; indArgs := indArgs c
  ; uniVBounds := uniVBounds c
  ; exiVBounds := fun i =>
    (if i == 0 as b return (i == 0) = b -> |[length (map PolyLiftExiV (rcons (polyConstraints c) p))]|
    then fun _ => length (polyConstraints c)
    else fun _ => exiVBounds c (i.-1)) (erefl _)
  ; exiFOutputBounds := exiFOutputBounds c
  ; exiFInputBounds := exiFInputBounds c
  ; formula := inrMap PropLiftExiV (formula c)
  |}.
Next Obligation.
  destruct (indArgs _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation.
  destruct (indArgs _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation.
  remember (PolyLiftExiV_obligation_1 _ _) as P; clear HeqP; simpl in P.
  destruct c, Ctx, subCtx; simpl in *.
  replace P with H1;auto.
  apply eq_irrelevance.
Qed.
Next Obligation.
  destruct (freeFArgs _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation.
  remember (PolyLiftExiV_obligation_2 _ _) as P; clear HeqP; simpl in P.
  destruct c, Ctx, subCtx; simpl in *.
  replace P with H1;auto.
  apply eq_irrelevance.
Qed.
Next Obligation.
  destruct (exiFArgs _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct c, Ctx, subCtx. Qed.
Next Obligation.
  destruct (uniVBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct c, Ctx, subCtx. Qed.
Next Obligation.
  destruct (exiFOutputBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct c, Ctx, subCtx. Qed.
Next Obligation.
  remember (SemicircuitExiInc_obligation_11 _ _ _) as P; clear HeqP; simpl in P.
  destruct c, Ctx, subCtx; simpl in *.
  replace P with H0;auto.
  apply eq_irrelevance.
Qed.
Next Obligation.
  destruct (exiFInputBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct c, Ctx, subCtx. Qed.
Next Obligation.
  assert ((i == 0) = false);[exact e|clear e].
  destruct c, Ctx, subCtx; simpl in *.
  unfold exiVS, exiVN, Ctx, exiVS, subCtx, Sigma_1_1.exiV in *.
  assert (i <> 0);[by rewrite <- EEFConvert|].
  by destruct i;[fcrush|].
Qed.
Next Obligation.
  change (exist _ ?x _ == exist _ ?y _) with (x == y).
  dep_if_case (i == 0); auto.
  by destruct (Ctx c), subCtx.
  destruct ((` (nu c)) _).
  clear H.
  by destruct c, Ctx, subCtx.
Qed.
Next Obligation.
  change (exist _ ?x _ == exist _ ?y _) with (x == y).
  dep_if_case (j == 0); auto.
  assert (j = 0);[by rewrite <- EEConvert|].
  assert (i = 0). rewrite H3 in H;destruct i;[auto|fcrush].
  rewrite <- EEConvert in H4.
  rewrite dep_if_case_true; auto.
  dep_if_case (i == 0); auto.
  destruct (` (nu c) _).
  by destruct c, Ctx, subCtx.
  destruct (nu c).
  simpl.
  apply i0.
  simpl.
  destruct i, j;auto.
Qed.
Next Obligation. by destruct (exiVS _);[fcrush|]. Qed.
Next Obligation. 
  assert ((i == 0) = false);[exact e|clear e].
  destruct c, Ctx, subCtx; simpl in *.
  unfold exiVS, exiVN, Ctx, exiVS, subCtx, Sigma_1_1.exiV in *.
  assert (i <> 0);[by rewrite <- EEFConvert|].
  by destruct i;[fcrush|].
Qed.
Next Obligation. 
  destruct (exiVBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. rewrite map_length length_rcons; sfirstorder. Qed.

(*Add a new universally quantified first order variable to semicircuit *)
Program Definition SemicircuitUniInc (c : SemiCircuit) (p : @SemicircuitPolyConstraint (Ctx c)): SemiCircuit :=
  {| Ctx := {| subCtx := incUniV (subCtx (Ctx c))
              ; freeFC := freeFC (Ctx c)
              ; exiFC := exiFC (Ctx c)
              ; indC := indC (Ctx c)|}
  ; nu := nu c
  ; polyConstraints := map PolyLiftUniV (rcons (polyConstraints c) p)
  ; freeFArgs := freeFArgs c
  ; exiFArgs := exiFArgs c
  ; indArgs := indArgs c
  ; uniVBounds := fun i =>
    (if i == 0 as b return (i == 0) = b -> |[length (map PolyLiftUniV (rcons (polyConstraints c) p))]|
    then fun _ => length (polyConstraints c)
    else fun _ => uniVBounds c (i.-1)) (erefl _)
  ; exiVBounds := exiVBounds c
  ; exiFOutputBounds := exiFOutputBounds c
  ; exiFInputBounds := exiFInputBounds c
  ; formula := inrMap PropLiftUniV (formula c)
  |}.
Next Obligation. by destruct c, Ctx, subCtx. Qed.
Next Obligation.
  destruct ((` (nu c)) _).
  clear H.  
  by destruct c, Ctx, subCtx; apply leqW.
Qed.
Next Obligation.
  destruct (nu c).
  by apply i0.
Qed.
Next Obligation.
  destruct (indArgs _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation.
  destruct (indArgs _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation.
  remember (PolyLiftUniV_obligation_1 _ _) as P; clear HeqP; simpl in P.
  destruct c, Ctx, subCtx; simpl in *.
  replace P with H1;auto.
  apply eq_irrelevance.
Qed.
Next Obligation.
  destruct (freeFArgs _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation.
  remember (PolyLiftUniV_obligation_2 _ _) as P; clear HeqP; simpl in P.
  destruct c, Ctx, subCtx; simpl in *.
  replace P with H1;auto.
  apply eq_irrelevance.
Qed.
Next Obligation.
  destruct (exiFArgs _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct c, Ctx, subCtx. Qed.
Next Obligation.
  destruct (exiVBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct c, Ctx, subCtx. Qed.
Next Obligation.
  destruct (exiFOutputBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct c, Ctx, subCtx. Qed.
Next Obligation.
  remember (SemicircuitUniInc_obligation_14 _ _ _) as P; clear HeqP; simpl in P.
  destruct c, Ctx, subCtx; simpl in *.
  replace P with H0;auto.
  apply eq_irrelevance.
Qed.
Next Obligation.
  destruct (exiFInputBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct c, Ctx, subCtx. Qed.
Next Obligation.
  assert ((i == 0) = false);[exact e|clear e].
  destruct c, Ctx, subCtx; simpl in *.
  unfold exiVS, exiVN, Ctx, exiVS, subCtx, Sigma_1_1.exiV in *.
  assert (i <> 0);[by rewrite <- EEFConvert|].
  by destruct i;[fcrush|].
Qed.
Next Obligation.
  destruct (uniVBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. rewrite map_length length_rcons; sfirstorder. Qed.

Fixpoint Translate_FirstOrderFormula 
  (c : SemiCircuit)
  (f : @FirstOrderFormula (subCtx (Ctx c))) : SemiCircuit :=
  match f with
  | ZO f => Translate_ZerothOrderFormula c f
  | FOExists b f =>
    let (da, bo) := PolyConvert b in
    let c0 := IntegrateConversionData c da in
    let c1 := SemicircuitExiInc c0 (PolyCallLift bo) in
    Translate_FirstOrderFormula c1 f
  | FOForall b f => 
    let (da, bo) := PolyConvert b in
    let c0 := IntegrateConversionData c da in
    let c1 := SemicircuitUniInc c0 (PolyCallLift bo) in
    Translate_FirstOrderFormula c1 f
  end.

Program Fixpoint PolyLiftAddExiF {ctx}
  (a : nat)
  (p : @SemicircuitPolyConstraint ctx) :
    @SemicircuitPolyConstraint {| subCtx := addExiF a (subCtx ctx)
                                ; freeFC := freeFC ctx
                                ; exiFC := fun i =>
          ( if i == 0 as b return (i == 0) = b -> nat
            then fun _ => 0
            else fun _ => exiFC ctx (i.-1) ) (erefl _)
                                ; indC := indC ctx
    |} := 
  match p with
  | PolyConsZero => PolyConsZero
  | PolyConsPlusOne => PolyConsPlusOne
  | PolyConsMinusOne => PolyConsMinusOne
  | PolyConsPlus p1 p2 =>
    let r1 := PolyLiftAddExiF a p1 in
    let r2 := PolyLiftAddExiF a p2 in 
    PolyConsPlus r1 r2
  | PolyConsTimes p1 p2 =>
    let r1 := PolyLiftAddExiF a p1 in
    let r2 := PolyLiftAddExiF a p2 in 
    PolyConsTimes r1 r2
  | PolyConsInd i => PolyConsInd i
  | PolyConsFreeV i => PolyConsFreeV i
  | PolyConsExiV i => PolyConsExiV i
  | PolyConsUniV i => PolyConsUniV i
  | PolyConsFreeF i j => PolyConsFreeF i j
  | PolyConsExiF i j => PolyConsExiF (i.+1) j
  end.
Next Obligation. by destruct (subCtx ctx). Qed.
Next Obligation. destruct (exiF (addExiF a (subCtx ctx)));[fcrush|auto]. Qed.
Next Obligation.
  assert (i <> 0);[by rewrite <- EEFConvert|clear e].
  destruct i;[fcrush|].
  simpl.
  by destruct (subCtx ctx).
Qed.
Next Obligation. by unfold freeVS in *; simpl; destruct (subCtx ctx). Qed. 
Next Obligation. by unfold exiVS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation. by unfold uniVS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation. by clear H; unfold freeFS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation.
  remember (PolyLiftAddExiF_obligation_1 _ _ _) as P; clear HeqP; simpl in P.
  replace P with H0; auto.
  apply eq_irrelevance.
Qed.
Next Obligation. by clear H; unfold exiFS in *; simpl; destruct (subCtx ctx). Qed.
Next Obligation.
  remember (PolyLiftAddExiF_obligation_3 _ _ _ _) as P; clear HeqP; simpl in P.
  replace P with H0; auto.
  apply eq_irrelevance.
Qed.

Program Fixpoint PropLiftAddExiF {ctx}
  (a : nat)
  (p : @SemicircuitPropConstraint ctx) :
    @SemicircuitPropConstraint {| subCtx := addExiF a (subCtx ctx)
                                ; freeFC := freeFC ctx
                                ; exiFC := fun i =>
          ( if i == 0 as b return (i == 0) = b -> nat
            then fun _ => 0
            else fun _ => exiFC ctx (i.-1) ) (erefl _)
                                ; indC := indC ctx
    |} := 
  match p with
  | ZOConsNot p =>
    let r := PropLiftAddExiF a p in
    ZOConsNot r
  | ZOConsAnd p1 p2 =>
    let r1 := PropLiftAddExiF a p1 in
    let r2 := PropLiftAddExiF a p2 in
    ZOConsAnd r1 r2
  | ZOConsOr p1 p2 =>
    let r1 := PropLiftAddExiF a p1 in
    let r2 := PropLiftAddExiF a p2 in
    ZOConsOr r1 r2
  | ZOConsImp p1 p2 =>
    let r1 := PropLiftAddExiF a p1 in
    let r2 := PropLiftAddExiF a p2 in
    ZOConsImp r1 r2
  | ZOConsEq p1 p2 =>
    let r1 := PolyLiftAddExiF a p1 in
    let r2 := PolyLiftAddExiF a p2 in
    ZOConsEq r1 r2
  end.

Program Definition SemicircuitExiFAdd 
  (c : SemiCircuit) 
  (y : @SemicircuitPolyConstraint (Ctx c))
  (bs : seq (@SemicircuitPolyConstraint (Ctx c))) : SemiCircuit :=
  let Ctx' := {| subCtx := addExiF (length bs) (subCtx (Ctx c))
              ; freeFC := freeFC (Ctx c)
              ; exiFC := fun i =>
              ( if i == 0 as b return (i == 0) = b -> nat
                then fun _ => 0
                else fun _ => exiFC (Ctx c) (i.-1) ) (erefl _)
              ; indC := indC (Ctx c)
              |} in
  let polyConstraints' := map (PolyLiftAddExiF (length bs)) (rcons (polyConstraints c ++ bs) y) in
  {| Ctx := Ctx'
  ; nu := nu c
  ; polyConstraints := polyConstraints'
  ; indArgs := indArgs c
  ; freeFArgs := freeFArgs c
  ; exiFArgs := fun i =>
    ( if i == 0 as b return (i == 0) = b -> |[exiFC Ctx' i]| -> |[exiFSA Ctx' i]| -> |[length polyConstraints']|
      then fun _ => emptyTuple
      else fun _ => exiFArgs c (i.-1) ) (erefl _)
  ; uniVBounds := uniVBounds c
  ; exiVBounds := exiVBounds c
  ; exiFOutputBounds := fun i =>
    (if i == 0 as b return (i == 0) = b -> |[length polyConstraints']|
    then fun _ => length (polyConstraints c) + length bs
    else fun _ => exiFOutputBounds c (i.-1)) (erefl _)
  ; exiFInputBounds := fun i =>
    (if i == 0 as b return (i == 0) = b -> |[exiFSA Ctx' i]| -> |[length polyConstraints']|
    then fun _ j => length (polyConstraints c) + j
    else fun _ => exiFInputBounds c (i.-1)) (erefl _)
  ; formula := inrMap (PropLiftAddExiF (length bs)) (formula c)
  |}.
Next Obligation. by destruct c, Ctx, subCtx. Qed.
Next Obligation.
  destruct ((` (nu c))_).
  clear H.
  by destruct c, Ctx, subCtx; simpl in *.
Qed.
Next Obligation.
  destruct (nu c); simpl.
  by apply i0.
Qed.
Next Obligation. 
  destruct ((indArgs _ _).1); simpl.
  rewrite map_length length_rcons length_cat.
  remember (length _) as a; clear Heqa.
  remember (length _) as b; clear Heqb.
  apply (ltn_trans i); clear i x0.
  scongruence use: addSn, Utils.cRange_obligation_1, addSnnS.
Qed.
Next Obligation.
  destruct ((indArgs _ _).2).
  rewrite map_length length_rcons length_cat.
  remember (length _) as a; clear Heqa.
  remember (length _) as b; clear Heqb.
  apply (ltn_trans i); clear i x0.
  scongruence use: addSn, Utils.cRange_obligation_1, addSnnS.
Qed.
Next Obligation. 
  remember (PolyLiftAddExiF_obligation_1 _ _ _) as P; clear HeqP; simpl in P.
  destruct c, Ctx, subCtx; simpl in *;
  replace P with H1;auto;apply eq_irrelevance.
Qed.
Next Obligation. 
  destruct (freeFArgs _ _); clear H H0 H1.
  rewrite map_length length_rcons length_cat.
  simpl.
  remember (length (polyConstraints c)) as a; clear Heqa.
  remember (length bs) as b; clear Heqb bs y c x x0 x1.
  hauto use: leq_addl, ltn_addr, addSnnS.
Qed.
Next Obligation. by destruct c, Ctx, subCtx. Qed.
Next Obligation. 
  destruct (uniVBounds _ _); clear H.
  rewrite map_length length_rcons length_cat.
  simpl.
  remember (length (polyConstraints c)) as a; clear Heqa.
  remember (length bs) as b; clear Heqb bs y c x.
  hauto use: leq_addl, ltn_addr, addSnnS.
Qed.
Next Obligation. by destruct c, Ctx, subCtx. Qed.
Next Obligation. 
  destruct (exiVBounds _ _); clear H.
  rewrite map_length length_rcons length_cat.
  simpl.
  remember (length (polyConstraints c)) as a; clear Heqa.
  remember (length bs) as b; clear Heqb bs y c x.
  hauto use: leq_addl, ltn_addr, addSnnS.
Qed.
Next Obligation. destruct (exiFS _); auto. Qed.
Next Obligation.
  assert (i <> 0);[by rewrite <- EEFConvert|clear e].
  destruct i;[fcrush|].
  by destruct c, Ctx, subCtx.
Qed.
Next Obligation.
  change (exist _ ?x _ == exist _ ?y _) with (x == y) in e.
  clear H0.
  destruct c, Ctx, subCtx; cbn; cbn in H.
  rewrite dep_if_case_false in H.
  remember (SemicircuitExiFAdd_obligation_13 _ _ _ _ _) as P; clear HeqP; simpl in P.
  cbn in P.
  replace (exist (fun n : nat => eqn (n.+1 - exiF)%Nrec 0) i.-1 P)
     with (exist (fun n : nat => eqn (n.+1 - exiF)%Nrec 0) i.-1
            (Sigma_1_1.addExiF_obligation_2 exiF
               (exist (fun n : nat => eqn (n - exiF)%Nrec 0) i H1) e)); auto.
  by apply subset_eq_compat.
Qed.
Next Obligation.
  change (exist _ ?x _ == exist _ ?y _) with (x == y) in e.
  destruct c, Ctx, subCtx; cbn in *.
  rewrite dep_if_case_false in H.
  remember (SemicircuitExiFAdd_obligation_13 _ _ _ _ _) as P; clear HeqP; simpl in P.
  replace (exist _ i.-1 _)
      with (exist (fun n : nat => eqn (n.+1 - exiF)%Nrec 0) i.-1 P) in H; auto.
  by apply subset_eq_compat.
Qed.
Next Obligation.
  destruct (exiFArgs _ _).
  clear H H0 e H1.
  rewrite map_length length_rcons length_cat.
  simpl.
  remember (length (polyConstraints c)) as a; clear Heqa.
  remember (length bs) as b; clear Heqb bs y c x.
  hauto use: leq_addl, ltn_addr, addSnnS.
Qed.
Next Obligation.
  destruct c, Ctx, subCtx; cbn in *.
  rewrite dep_if_case_true in H; auto.
Qed.
Next Obligation. by destruct c, Ctx, subCtx. Qed.
Next Obligation.
  destruct c, Ctx, subCtx; cbn in *.
  destruct i; auto.
Qed.
Next Obligation.
  destruct (exiFOutputBounds _ _).
  rewrite map_length length_rcons length_cat.
  simpl.
  remember (length (polyConstraints c)) as a; clear Heqa e.
  remember (length bs) as b; clear Heqb bs H.
  hauto use: leq_addl, ltn_addr, addSnnS.
Qed.
Next Obligation.
  rewrite map_length length_rcons length_cat.
  apply ltnSn.
Qed.
Next Obligation. by destruct c, Ctx, subCtx. Qed.
Next Obligation. 
  destruct c, Ctx, subCtx; cbn in *.
  destruct i; auto.
Qed.
Next Obligation. 
  destruct c, Ctx, subCtx; cbn in *.
  rewrite dep_if_case_false in H; auto.
  remember (SemicircuitExiFAdd_obligation_23 _ _ _ _ _) as P; clear HeqP; simpl in P.
  replace (exist _ i.-1 _)
      with (exist (fun n : nat => eqn (n.+1 - exiF)%Nrec 0) i.-1 P) in H; auto.
  by apply subset_eq_compat.
Qed.
Next Obligation.
  destruct (exiFInputBounds _ _).
  rewrite map_length length_rcons length_cat.
  simpl.
  remember (length (polyConstraints c)) as a; clear Heqa e.
  remember (length bs) as b; clear Heqb bs H.
  hauto use: leq_addl, ltn_addr, addSnnS.
Qed.
Next Obligation.
  rewrite map_length length_rcons length_cat.
  destruct c, Ctx, subCtx; cbn in *.
  rewrite dep_if_case_true in H; auto.
  assert (j < length bs);[auto|clear H].
  assert (length polyConstraints + j <= length polyConstraints + length bs);[|auto].
  rewrite leq_add2l.
  by apply ltnW.
Qed.

Program Fixpoint Translate_SecondOrderFormula 
  (c : SemiCircuit)
  (f : @SecondOrderFormula (subCtx (Ctx c))) : SemiCircuit :=
  match f with
  | FO f => Translate_FirstOrderFormula c f
  | SOExists y bs f => 
    let (day, poy) := PolyConvert y in
    let c0 := IntegrateConversionData c day in
    let poy0 : @SemicircuitPolyConstraint (Ctx c0) := PolyCallLift poy in
    let bs' := map PolyConvert bs in
    let (dabs, pobs) := PolyCallSeqFuse bs' in
    let c1 := IntegrateConversionData c0 dabs in
    let poy1 : @SemicircuitPolyConstraint (Ctx c1) := PolyCallCast poy0 in
    let pobs1 : seq (@SemicircuitPolyConstraint (Ctx c1)) := map PolyCallLift pobs in
    let c2 := SemicircuitExiFAdd c1 poy1 pobs1 in
    Translate_SecondOrderFormula c2 f
  end.
Next Obligation.
  do 2 rewrite map_length in H *.
  by rewrite H.
Qed.

End SemicircuitTranslation.
