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

Variable D : RingData.

Definition ModelInstance {ctx} {c} (M : Sigma11Model D) : @SemiCircuitInstance ctx D c :=
  {| freeVInst := fun n => freeV_F D M (` n)
   ; freeFInst := fun i t => freeF_S D M (` i) (freeFA ctx i) t
  |}.

Record SemiConversionData {ctx : Sigma11Ctx} : Type := mkPolyConvertData {
  newFreeFCalls : |[freeF ctx]| -> nat ;
  newExiFCalls : |[exiF ctx]| -> nat ;
  newIndCalls : nat ;
  newPolys : seq (@SCPoly _ {| freeFC := newFreeFCalls; exiFC := newExiFCalls; indC := newIndCalls |}) ;
  newFreeArgs : forall (i : |[freeF ctx]|), |[newFreeFCalls i]| -> |[freeFA ctx i]| -> |[length newPolys]| ;
  newExiArgs : forall (i : |[exiF ctx]|), |[newExiFCalls i]| -> |[exiFA ctx i]| -> |[length newPolys]| ;
  newIndArgs : |[newIndCalls]| -> (|[length newPolys]| * |[length newPolys]|)
  }.

Definition SemiConversionDataCtx {ctx} (data : @SemiConversionData ctx) : @SemicircuitCtx ctx :=
  {| freeFC := newFreeFCalls data 
   ; exiFC := newExiFCalls data
   ; indC := newIndCalls data
  |}.

Definition SemiDenotation {ctx} c exFN (exFA : |[exFN]| -> nat) exVN := 
  (forall i : |[exFN]|, (|[exFA i]| -> T D) -> option (T D)) ->
  (|[exVN]| -> T D) ->
  Sigma11Model D -> @SemiCircuitAdvice ctx D c.

Definition emptyCtx ctx : @SemicircuitCtx ctx := {| freeFC := fun _=> 0; exiFC := fun _=> 0; indC := 0|}.

Definition SemiConversionEmptyData {ctx} : 
  @SemiConversionData ctx :=
  {| newFreeFCalls := fun _ => 0; newExiFCalls := fun _ => 0; newIndCalls := 0; newPolys := [::]
   ; newFreeArgs := fun x => emptyTuple; newExiArgs := fun x => emptyTuple; newIndArgs := emptyTuple|}.

Program Definition EmptyDenotation {c i j k} : SemiDenotation (emptyCtx c) i j k :=
  fun _ _ M =>
  {| exiVAdv := fun n _ => exiV_F D M (` n)
   ; exiFAdv := fun i t => exiF_S D M (` i) (exiFA c i) t
   ; freeFCallOut := fun _ => emptyTuple
   ; exiFCallOut := fun _ => emptyTuple
   ; indCallOut := emptyTuple
  |}.

Definition EmptyDataAdvice {c i j k} : SemiDenotation (@SemiConversionDataCtx c SemiConversionEmptyData) i j k :=
  EmptyDenotation.

Program Definition SemiConversionCombineData {ctx}
  (d1 d2 : @SemiConversionData ctx) : @SemiConversionData ctx :=
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
      else fun _ k => length polys1 + farg2 i (j - nffc1 i) k
    ) (erefl _)
    ; newExiArgs := fun i j => (
      if j < nefc1 i as b return j < nefc1 i = b -> |[exiFA ctx i]| -> |[length poly']|
      then fun _ => earg1 i j
      else fun _ k => length polys1 + earg2 i (j - nefc1 i) k
    ) (erefl _) 
    ; newIndArgs := fun i => (
      if i < nic1 as b return i < nic1 = b -> (|[length poly']| * |[length poly']|)
      then fun _ => iarg1 i
      else fun _ => 
        let (u, v) := iarg2 (i - nic1)
        in (length polys1 + u, length polys1 + v)
    ) (erefl _) 
  |}
  end.
Next Obligation.
  rewrite length_cat map_length map_length.
  by destruct (farg1 _); apply ltn_addr.
Qed.
Next Obligation.
  assert (~ (j < nffc1 (exist _ i H1)));[hauto|].
  assert (nffc1 (exist _ i H1) <= j);[by apply (contra_not_leq (P := j < nffc1 (exist _ i H1)))|].
  qauto use: ltn_subLR, ltn_addr.
Qed.
Next Obligation.
  rewrite length_cat map_length map_length.
  by destruct (farg2 _); rewrite ltn_add2l.
Qed.
Next Obligation.
  rewrite length_cat map_length map_length.
  by destruct (earg1 _); apply ltn_addr.
Qed.
Next Obligation.
  assert (~ (j < nefc1 (exist _ i H1)));[hauto|].
  assert (nefc1 (exist _ i H1) <= j);[by apply (contra_not_leq (P := j < nefc1 (exist _ i H1)))|].
  qauto use: ltn_subLR, ltn_addr.
Qed.
Next Obligation.
  rewrite length_cat map_length map_length.
  by destruct (earg2 _); rewrite ltn_add2l.
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
  by rewrite ltn_add2l.
Qed.
Next Obligation.
  rewrite length_cat map_length map_length.
  by rewrite ltn_add2l.
Qed.

Program Definition CombineDataDenotation {c i j k} 
  {d1 d2 : @SemiConversionData c}
  (ad1 : SemiDenotation (@SemiConversionDataCtx c d1) i j k)
  (ad2 : SemiDenotation (@SemiConversionDataCtx c d2) i j k) :
  SemiDenotation (@SemiConversionDataCtx c (SemiConversionCombineData d1 d2)) i j k :=
  fun X Y M =>
  let data' := (SemiConversionCombineData d1 d2) in
  let ctx' := SemiConversionDataCtx data' in
  {| exiVAdv := exiVAdv (ad1 X Y M)
   ; exiFAdv := exiFAdv (ad1 X Y M)
   ; freeFCallOut := fun i j => (
     if j < newFreeFCalls d1 i as b return j < newFreeFCalls d1 i = b -> (|[uniV c]| -> T D) -> option (T D)
     then fun _ => freeFCallOut (ad1 X Y M) i j
     else fun _ => freeFCallOut (ad2 X Y M) i (j - newFreeFCalls d1 i)
   ) (erefl _)
   ; exiFCallOut := fun i j => (
     if j < newExiFCalls d1 i as b return j < newExiFCalls d1 i = b -> (|[uniV c]| -> T D) -> option (T D)
     then fun _ => exiFCallOut (ad1 X Y M) i j
     else fun _ => exiFCallOut (ad2 X Y M) i (j - newExiFCalls d1 i)
   ) (erefl _) 
   ; indCallOut := fun i => (
     if i < newIndCalls d1 as b return i < newIndCalls d1 = b -> (|[uniV c]| -> T D) -> option (T D)
     then fun _ => indCallOut (ad1 X Y M) i
     else fun _ => indCallOut (ad2 X Y M) (i - newIndCalls d1)
   ) (erefl _) 
  |}.
Next Obligation.
  destruct d1, d2, c; cbn in *;
  hecrush use: ltn_subLR, contraFltn, is_true_true unfold: is_true.
Qed.
Next Obligation.
  destruct d1, d2, c; cbn in *; hecrush use: ltn_subLR, contraFltn, is_true_true unfold: is_true.
Qed.
Next Obligation.
  destruct d1, d2, c; cbn in *; hecrush use: ltn_subLR, contraFltn, is_true_true unfold: is_true.
Qed.

Program Definition PolyFuseCoerce {ctx : Sigma11Ctx} {d1 d2 : @SemiConversionData ctx} 
  (s : @SCPoly ctx {| freeFC := fun x => newFreeFCalls d1 x + newFreeFCalls d2 x
                                                  ; exiFC := fun x => newExiFCalls d1 x + newExiFCalls d2 x
                                                  ; indC := newIndCalls d1 + newIndCalls d2 |}) :
  @SCPoly ctx {| freeFC := newFreeFCalls (SemiConversionCombineData d1 d2)
                                    ; exiFC := newExiFCalls (SemiConversionCombineData d1 d2)
                                    ; indC := newIndCalls (SemiConversionCombineData d1 d2) |} := s.
Next Obligation. by f_equal; destruct d1, d2. Qed.

(*Fuse sequence of poly conversion outputs into a single output. *)
Program Fixpoint PolyCallSeqFuse {ctx X Y Z} 
  (s : seq { d : @SemiConversionData ctx & 
    prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
         (@SCPoly _ (@SemiConversionDataCtx ctx d)) }) :
  { d : @SemiConversionData ctx & 
    prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
         {t : seq (@SCPoly _ (@SemiConversionDataCtx ctx d)) | length t = length s} } :=
  match s with
  | [::] => existT _ SemiConversionEmptyData (EmptyDataAdvice, [::])
  | (existT b (a, x)) :: xs => 
    let (d, D) := PolyCallSeqFuse xs in let (ad, p) := D in
    let d0 := SemiConversionCombineData b d in
    let ad0 := CombineDataDenotation a ad in
    let p0 := map PolyFuseCoerce (PolyCallCast x :: map PolyCallLift p) in
    existT _ d0 (ad0, p0)
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
  (d : @SemiConversionData ctx) (i : |[freeF ctx]|) :
  forall s : seq (@SCPoly _ (@SemiConversionDataCtx ctx d)),
  length s = freeFA ctx i -> @SemiConversionData ctx :=
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

Program Definition FreeCallIncorpDenotation {ctx X Y Z} 
  (d : @SemiConversionData ctx) {i} {s} {e}
  (ad : SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z) :
  SemiDenotation (@SemiConversionDataCtx ctx (FreeCallIncorp d i s e)) X Y Z :=
  fun X Y M =>
  let data' := FreeCallIncorp d i s e in
  let ctx' := SemiConversionDataCtx data' in
  {| exiVAdv := exiVAdv (ad X Y M)
   ; exiFAdv := exiFAdv (ad X Y M)
   ; freeFCallOut := fun j => (
     if j == i as b return j == i = b -> |[freeFC ctx' j]| -> (|[uniV ctx]| -> T D) -> option (T D)
     then fun _ c => (
      if c == newFreeFCalls d i as b return (c == newFreeFCalls d i) = b -> (|[uniV ctx]| -> T D) -> option (T D)
      then fun _ u => 
        let f0 := (fun x => SemicircuitPolyDenotation (ModelInstance M) (ad X Y M) (lnth s x) u) in 
        match obind (freeF_S D M i _) (OptionArgs (B := fun _ => _) f0) with
        | None => Some 0%R
        | Some r1 => Some r1
        end
      else fun _ => freeFCallOut (ad X Y M) j c
      ) (erefl _)
     else fun _ => freeFCallOut (ad X Y M) j
   ) (erefl _)
   ; exiFCallOut := exiFCallOut (ad X Y M)
   ; indCallOut := indCallOut (ad X Y M)
  |}.
Next Obligation.
  destruct d, ctx; cbn in *.
  unfold SingleCall in H.
  rewrite dep_if_case_false in H; auto.
  qauto use: addn1, addSnnS inv: nat.
Qed.
Next Obligation. by destruct d. Qed.
Next Obligation. by destruct d. Qed.
Next Obligation.
  clear H c.
  assert ((exist (fun n : nat => n < freeF ctx) j H0) = (exist (fun n : nat => n < freeF ctx) i H1)).
  by apply EEConvert.1 in e0; apply subset_eq_compat.
  destruct d, ctx; simpl; unfold AddCall, SingleCall; rewrite dep_if_case_true; auto; simpl.
  rewrite H; apply Utils.cRange_obligation_1.
Qed.
Next Obligation.
  change (exist _ ?x _ == exist _ ?y _) with (x == y) in *.
  destruct d, ctx; simpl in *.
  unfold AddCall, SemiConversionDataCtx, SingleCall in *;
  rewrite dep_if_case_true in H; auto.
  apply leq_neq_lt;[by rewrite addn1 in H|].
  simpl; rewrite <- EEFConvert.
  by replace (exist _ j H0) with (exist (fun n : nat => n < freeF) i H1);[
  |apply subset_eq_compat; apply EEConvert.1 in e0].
Qed.

(*Add a list of circuit constraints associated to an exi fun call to data*)
Program Definition ExiCallIncorp {ctx}
  (d : @SemiConversionData ctx) (i : |[exiF ctx]|) :
  forall s : seq (@SCPoly _ (@SemiConversionDataCtx ctx d)),
  length s = exiFA ctx i ->
  @SemiConversionData ctx :=
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

Program Definition ExiCallIncorpDenotation {ctx X Y Z} 
  (d : @SemiConversionData ctx) {i} {s} {e}
  (ad : SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z) :
  SemiDenotation (@SemiConversionDataCtx ctx (ExiCallIncorp d i s e)) X Y Z :=
  fun X Y M =>
  let data' := ExiCallIncorp d i s e in
  let ctx' := SemiConversionDataCtx data' in
  {| exiVAdv := exiVAdv (ad X Y M)
   ; exiFAdv := exiFAdv (ad X Y M)
   ; freeFCallOut := freeFCallOut (ad X Y M)
   ; exiFCallOut := fun j => (
     if j == i as b return j == i = b -> |[exiFC ctx' j]| -> (|[uniV ctx]| -> T D) -> option (T D)
     then fun _ c => (
      if c == newExiFCalls d i as b return (c == newExiFCalls d i) = b -> (|[uniV ctx]| -> T D) -> option (T D)
      then fun _ u => 
        let f0 := (fun x => SemicircuitPolyDenotation (ModelInstance M) (ad X Y M) (lnth s x) u) in 
        match obind (exiF_S D M i _) (OptionArgs (B := fun _ => _) f0) with
        | None => Some 0%R
        | Some r1 => Some r1
        end
      else fun _ => exiFCallOut (ad X Y M) j c
      ) (erefl _)
     else fun _ => exiFCallOut (ad X Y M) j
   ) (erefl _)
   ; indCallOut := indCallOut (ad X Y M)
  |}.
Next Obligation. by destruct d. Qed.
Next Obligation.
  destruct d, ctx; cbn in *.
  unfold SingleCall in H.
  rewrite dep_if_case_false in H; auto.
  qauto use: addn1, addSnnS inv: nat.
Qed.
Next Obligation. by destruct d. Qed.
Next Obligation.
  clear H c.
  assert ((exist (fun n : nat => n < exiF ctx) j H0) = (exist (fun n : nat => n < exiF ctx) i H1)).
  by apply EEConvert.1 in e0; apply subset_eq_compat.
  destruct d, ctx; simpl; unfold AddCall, SingleCall; rewrite dep_if_case_true; auto; simpl.
  rewrite H; apply Utils.cRange_obligation_1.
Qed.
Next Obligation.
  change (exist _ ?x _ == exist _ ?y _) with (x == y) in *.
  destruct d, ctx; simpl in *.
  unfold AddCall, SemiConversionDataCtx, SingleCall in *;
  rewrite dep_if_case_true in H; auto.
  apply leq_neq_lt;[by rewrite addn1 in H|].
  simpl; rewrite <- EEFConvert.
  by replace (exist _ j H0) with (exist (fun n : nat => n < exiF) i H1);[
  |apply subset_eq_compat; apply EEConvert.1 in e0].
Qed.

Program Definition PolyConvertFreeCase {ctx X Y Z} 
  (i : |[freeF ctx]|) 
  (t : |[freeFA ctx i]| ->
    { d : @SemiConversionData ctx &  
      prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
          (@SCPoly _ (@SemiConversionDataCtx ctx d)) }) :
  { d : @SemiConversionData ctx &  
    prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
         (@SCPoly _ (@SemiConversionDataCtx ctx d)) } := 
  let (data, D) := PolyCallSeqFuse [seq t i | i <- cRange 0 (freeFA ctx i) ] in let (ad, polys) := D in
  let data2 : @SemiConversionData ctx := FreeCallIncorp data i polys _ in
  existT _ data2 (FreeCallIncorpDenotation _ ad, PolyConsFreeF i (newFreeFCalls data i)).
Next Obligation. by rewrite map_length (length_cRange (n := 0)) in H. Qed.
Next Obligation.
  destruct data; simpl.
  unfold AddCall, SingleCall.
  rewrite dep_if_case_true;[by rewrite EEConvert|].
  apply Utils.cRange_obligation_1.
Qed.

Program Definition PolyConvertExiCase {ctx X Y Z} 
  (i : |[exiF ctx]|) 
  (t : |[exiFA ctx i]| ->
    { d : @SemiConversionData ctx &  
      prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
           (@SCPoly _ (@SemiConversionDataCtx ctx d)) }) :
  { d : @SemiConversionData ctx &  
    prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
         (@SCPoly _ (@SemiConversionDataCtx ctx d)) } :=
  let (data, D) := PolyCallSeqFuse [seq t i | i <- cRange 0 (exiFA ctx i) ] in let (ad, polys) := D in
  let data2 : @SemiConversionData ctx := ExiCallIncorp data i polys _ in
  existT _ data2 (ExiCallIncorpDenotation _ ad, PolyConsExiF i (newExiFCalls data i)).
Next Obligation. by rewrite map_length (length_cRange (n := 0)) in H. Qed.
Next Obligation.
  destruct data; simpl.
  unfold AddCall.
  unfold SingleCall.
  rewrite dep_if_case_true;[by rewrite EEConvert|].
  apply Utils.cRange_obligation_1.
Qed.

(*Add a list of circuit constraints associated to an ind call to data*)
Program Definition IndCallIncorp {ctx}
  (d : @SemiConversionData ctx) :
  (@SCPoly _ (@SemiConversionDataCtx ctx d)) ->
  (@SCPoly _ (@SemiConversionDataCtx ctx d)) ->
  @SemiConversionData ctx :=
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

Program Definition IndCallIncorpAdvice {c X Y Z} 
  (d : @SemiConversionData c) {x} {y}
  (ad : SemiDenotation (@SemiConversionDataCtx c d) X Y Z) :
  SemiDenotation (@SemiConversionDataCtx c (IndCallIncorp d x y)) X Y Z :=
  fun X Y M =>
  let data' := IndCallIncorp d x y in
  let ctx' := SemiConversionDataCtx data' in
  {| exiVAdv := exiVAdv (ad X Y M)
   ; exiFAdv := exiFAdv (ad X Y M)
   ; freeFCallOut := freeFCallOut (ad X Y M)
   ; exiFCallOut := exiFCallOut (ad X Y M)
   ; indCallOut := fun i => (
      if i == newIndCalls d as b return (i == newIndCalls d) = b -> (|[uniV c]| -> T D) -> option (T D)
      then fun _ u => 
        let x1 := SemicircuitPolyDenotation (ModelInstance M) (ad X Y M) x u in
        let y1 := SemicircuitPolyDenotation (ModelInstance M) (ad X Y M) y u in
        obind (fun x => obind (fun y => Some (indFun D x y)) y1) x1
      else fun _ => indCallOut (ad X Y M) i
   ) (erefl _)
  |}.
Next Obligation. by destruct d. Qed.
Next Obligation. by destruct d. Qed.
Next Obligation. destruct d; apply Utils.cRange_obligation_1. Qed.
Next Obligation.
  change (exist _ ?x _ == exist _ ?y _) with (x == y) in *.
  replace (newIndCalls (IndCallIncorp d x y))
     with ((newIndCalls d).+1) in H.
  by apply leq_neq_lt;[|rewrite <- EEFConvert].
  destruct d; unfold IndCallIncorp in H; simpl.
  hauto use: addn1.
Qed.

Program Definition PolyConvertIndCase {ctx X Y Z} 
  (x : { d : @SemiConversionData ctx &  
          prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
              (@SCPoly _ (@SemiConversionDataCtx ctx d)) })
  (y : { d : @SemiConversionData ctx &  
          prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
              (@SCPoly _ (@SemiConversionDataCtx ctx d)) }) :
  { d : @SemiConversionData ctx &  
    prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
         (@SCPoly _ (@SemiConversionDataCtx ctx d)) } :=
  let (data, D) := PolyCallSeqFuse (cons x (cons y nil)) in let (ad, polys) := D in
  let data2 : @SemiConversionData ctx := IndCallIncorp data (lnth polys 0) (lnth polys 1) in
  existT _ data2 (IndCallIncorpAdvice _ ad, PolyConsInd (newIndCalls data)).
Next Obligation. by rewrite H. Qed.
Next Obligation. by destruct data; apply Utils.cRange_obligation_1. Qed.

(*Construct a polynomial constraint, new calls within that constraint, simultanious with data to modify a semicircuit *)
Program Fixpoint PolyConvert {ctx X Y Z} (r : @PolyTerm ctx) :
  { d : @SemiConversionData ctx &  
    prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
         (@SCPoly _ (@SemiConversionDataCtx ctx d)) } := 
  match r with
  | PolyFVar m => existT _ SemiConversionEmptyData (EmptyDataAdvice, PolyConsFreeV m)
  | PolyEVar m => existT _ SemiConversionEmptyData (EmptyDataAdvice, PolyConsExiV m)
  | PolyUVar m => existT _ SemiConversionEmptyData (EmptyDataAdvice, PolyConsUniV m)
  | PolyFFun i t => PolyConvertFreeCase i (fun x => PolyConvert (t x))
  | PolyEFun i t => PolyConvertExiCase i (fun x => PolyConvert (t x))
  | PolyMinusOne => existT _ SemiConversionEmptyData (EmptyDataAdvice, PolyConsMinusOne)
  | PolyPlusOne => existT _ SemiConversionEmptyData (EmptyDataAdvice, PolyConsPlusOne)
  | PolyZero => existT _ SemiConversionEmptyData (EmptyDataAdvice, PolyConsZero)
  | PolyPlus r1 r2 => 
    let (d1, D1) := PolyConvert r1 in let (ad1, p1) := D1 in
    let (d2, D2) := PolyConvert r2 in let (ad2, p2) := D2 in
    existT _ (SemiConversionCombineData d1 d2)
             (CombineDataDenotation ad1 ad2
             ,PolyConsPlus (PolyCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) (newIC := newIndCalls d2) p1) 
                           (PolyCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) (newIC := newIndCalls d1) p2))
  | PolyTimes r1 r2 => 
    let (d1, D1) := PolyConvert r1 in let (ad1, p1) := D1 in
    let (d2, D2) := PolyConvert r2 in let (ad2, p2) := D2 in
    existT _ (SemiConversionCombineData d1 d2)
             (CombineDataDenotation ad1 ad2
             ,PolyConsTimes (PolyCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) (newIC := newIndCalls d2) p1) 
                            (PolyCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) (newIC := newIndCalls d1) p2))
  | PolyInd r1 r2 => PolyConvertIndCase (PolyConvert r1) (PolyConvert r2)
  end.
Next Obligation. by destruct d1, d2; unfold SemiConversionDataCtx; f_equal; apply functional_extensionality;move=>[x ltx]. Qed.
Next Obligation. by destruct d1, d2; unfold SemiConversionDataCtx; f_equal; apply functional_extensionality;move=>[x ltx]. Qed.
Next Obligation. by destruct d1, d2; unfold SemiConversionDataCtx; f_equal; apply functional_extensionality;move=>[x ltx]. Qed.
Next Obligation. by destruct d1, d2; unfold SemiConversionDataCtx; f_equal; apply functional_extensionality;move=>[x ltx]. Qed.

(*Convert constraint to one with new function with no calls*)
Fixpoint PropCallCast {ctx c}
    {newFC : |[freeF ctx]| -> nat}
    {newEC : |[exiF ctx]| -> nat}
    {newIC : nat}
    (p : @SemicircuitPropConstraint ctx c) :
    @SemicircuitPropConstraint _ {| freeFC := fun x => freeFC c x + newFC x
                               ; exiFC := fun x => exiFC c x + newEC x
                               ; indC := indC c + newIC|} := 
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

Fixpoint PropCallLift {ctx c}
    {newFC : |[freeF ctx]| -> nat}
    {newEC : |[exiF ctx]| -> nat}
    {newIC : nat}
    (p : @SemicircuitPropConstraint ctx c) :
    @SemicircuitPropConstraint _ {|freeFC := fun x => newFC x + freeFC c x
                               ; exiFC := fun x => newEC x + exiFC c x
                               ; indC := newIC + indC c|} := 
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
Program Fixpoint PropConvert {ctx X Y Z} (r : @ZerothOrderFormula ctx) :
  { d : @SemiConversionData ctx &  
        prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
             (@SemicircuitPropConstraint _ (@SemiConversionDataCtx ctx d)) } := 
  match r with
  | ZONot f => 
    let (d, D) := PropConvert f in let (ad, p) := D in
    existT _ d (ad, ZOConsNot p)
  | ZOAnd f1 f2 => 
    let (d1, D1) := PropConvert f1 in let (ad1, p1) := D1 in
    let (d2, D2) := PropConvert f2 in let (ad2, p2) := D2 in
    existT _ (SemiConversionCombineData d1 d2)
             (CombineDataDenotation ad1 ad2
             ,ZOConsAnd (PropCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) (newIC := newIndCalls d2) p1) 
                        (PropCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) (newIC := newIndCalls d1) p2))
  | ZOOr f1 f2 => 
    let (d1, D1) := PropConvert f1 in let (ad1, p1) := D1 in
    let (d2, D2) := PropConvert f2 in let (ad2, p2) := D2 in
    existT _ (SemiConversionCombineData d1 d2)
             (CombineDataDenotation ad1 ad2
             ,ZOConsOr (PropCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) (newIC := newIndCalls d2) p1) 
                       (PropCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) (newIC := newIndCalls d1) p2))
  | ZOImp f1 f2 => 
    let (d1, D1) := PropConvert f1 in let (ad1, p1) := D1 in
    let (d2, D2) := PropConvert f2 in let (ad2, p2) := D2 in
    existT _ (SemiConversionCombineData d1 d2)
             (CombineDataDenotation ad1 ad2
             ,ZOConsImp (PropCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) (newIC := newIndCalls d2) p1) 
                        (PropCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) (newIC := newIndCalls d1) p2))
  | ZOEq r1 r2 => 
    let (d1, D1) := PolyConvert r1 in let (ad1, p1) := D1 in
    let (d2, D2) := PolyConvert r2 in let (ad2, p2) := D2 in
    existT _ (SemiConversionCombineData d1 d2)
             (CombineDataDenotation ad1 ad2
             ,ZOConsEq (PolyCallCast (newFC := newFreeFCalls d2) (newEC := newExiFCalls d2) (newIC := newIndCalls d2) p1) 
                       (PolyCallLift (newFC := newFreeFCalls d1) (newEC := newExiFCalls d1) (newIC := newIndCalls d1) p2))
  end.
Next Obligation. by destruct d1, d2; unfold SemiConversionDataCtx; f_equal; apply functional_extensionality;move=>[x ltx]. Qed.
Next Obligation. by destruct d1, d2; unfold SemiConversionDataCtx; f_equal; apply functional_extensionality;move=>[x ltx]. Qed.
Next Obligation. by destruct d1, d2; unfold SemiConversionDataCtx; f_equal; apply functional_extensionality;move=>[x ltx]. Qed.
Next Obligation. by destruct d1, d2; unfold SemiConversionDataCtx; f_equal; apply functional_extensionality;move=>[x ltx]. Qed.
Next Obligation. by destruct d1, d2; unfold SemiConversionDataCtx; f_equal; apply functional_extensionality;move=>[x ltx]. Qed.
Next Obligation. by destruct d1, d2; unfold SemiConversionDataCtx; f_equal; apply functional_extensionality;move=>[x ltx]. Qed.
Next Obligation. by destruct d1, d2; unfold SemiConversionDataCtx; f_equal; apply functional_extensionality;move=>[x ltx]. Qed.
Next Obligation. by destruct d1, d2; unfold SemiConversionDataCtx; f_equal; apply functional_extensionality;move=>[x ltx]. Qed.

(*Integrate generated polynomial constraint data into a semicircuit*)
Program Definition IntegrateConversionDataC {ctx}
  (c : @SemiCircuit ctx)
  (d : @SemiConversionData ctx) : SemiCircuit :=
  let Ctx' := {|freeFC := fun x => freeFCalls c x + newFreeFCalls d x
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
     (if j < freeFCalls c i as b return (j < freeFCalls c i) = b -> |[freeFA ctx i]| -> |[length poly']|
     then fun _ => freeFArgs c i j
     else fun _ x => length (polyConstraints c) 
                   + newFreeArgs d i (j - freeFCalls c i) x) (erefl _)
   ; exiFArgs := fun i (j : |[exiFCalls c i + newExiFCalls d i]|) =>
     (if j < exiFCalls c i as b return (j < exiFCalls c i) = b -> |[exiFA ctx i]| -> |[length poly']|
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

Program Definition IntegrateConversionDataA {ctx X Y Z}
  {s} (ad1 : SemiDenotation (Ctx s) X Y Z)
  {d} (ad2 : SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z) :
  SemiDenotation (Ctx (IntegrateConversionDataC s d)) X Y Z :=
  fun X Y M =>
  let data' := IntegrateConversionDataC s d in
  let ctx' := Ctx data' in
  {| exiVAdv := exiVAdv (ad1 X Y M)
   ; exiFAdv := exiFAdv (ad1 X Y M)
   ; freeFCallOut := fun i j => (
     if j < freeFCalls s i as b return j < freeFCalls s i = b -> (|[uniV ctx]| -> T D) -> option (T D)
     then fun _ => freeFCallOut (ad1 X Y M) i j
     else fun _ => freeFCallOut (ad2 X Y M) i (j - freeFCalls s i)
    ) (erefl _)
   ; exiFCallOut := fun i j => (
     if j < exiFCalls s i as b return j < exiFCalls s i = b -> (|[uniV ctx]| -> T D) -> option (T D)
     then fun _ => exiFCallOut (ad1 X Y M) i j
     else fun _ => exiFCallOut (ad2 X Y M) i (j - exiFCalls s i)
      ) (erefl _)
   ; indCallOut := fun i => (
     if i < indCalls s as b return i < indCalls s = b -> (|[uniV ctx]| -> T D) -> option (T D)
     then fun _ => indCallOut (ad1 X Y M) i
     else fun _ => indCallOut (ad2 X Y M) (i - indCalls s)
      ) (erefl _)
  |}.
Next Obligation.
  remember (freeFCalls _ _) as a; clear Heqa.
  assert (a <= j);[hecrush use: contraFltn|qauto use: ltn_subLR].
Qed.
Next Obligation.
  remember (exiFCalls _ _) as a; clear Heqa.
  assert (a <= j);[hecrush use: contraFltn|qauto use: ltn_subLR].
Qed.
Next Obligation.
  assert (indCalls s <= i);[hecrush use: contraFltn|qauto use: ltn_subLR].
Qed.

Definition IntegrateConversionData {ctx X Y Z}
  (c : {s : @SemiCircuit ctx & SemiDenotation (Ctx s) X Y Z})
  (d : {d : @SemiConversionData ctx & 
            SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z}) : 
  {s : @SemiCircuit ctx & SemiDenotation (Ctx s) X Y Z} :=
  match c, d with
  | existT c adc, existT d add =>
    existT _ (IntegrateConversionDataC c d) (IntegrateConversionDataA adc add) 
  end.

Definition Translate_ZerothOrderFormula {ctx X Y Z}
  (s : { s : @SemiCircuit ctx & SemiDenotation (Ctx s) X Y Z})
  (f : @ZerothOrderFormula ctx) : 
  { s : @SemiCircuit ctx & SemiDenotation (Ctx s) X Y Z} :=
  match PropConvert f with
  | existT d (ad, p) => 
    let c0 := IntegrateConversionDataC (projT1 s) d in
    let c' := {| Ctx := Ctx c0
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
              |} in
    existT _ c' (IntegrateConversionDataA (projT2 s) ad)
  end.

Check PropConvert.

Definition PropInt {ctx X Y Z}
  (s : { s : @SemiCircuit ctx & SemiDenotation (Ctx s) X Y Z})

  (d : @SemiConversionData ctx)
  (ad : SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
  (p : @SemicircuitPropConstraint _ (@SemiConversionDataCtx ctx d)) :
  { s : @SemiCircuit ctx & SemiDenotation (Ctx s) X Y Z} :=
  let c0 := IntegrateConversionDataC (projT1 s) d in
  let c' := {| Ctx := Ctx c0
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
            |} in
  existT _ c' (IntegrateConversionDataA (projT2 s) ad).


Program Definition incExiCC {ctx} (c : @SemicircuitCtx ctx) : @SemicircuitCtx (incExiV ctx) :=
  {| freeFC := freeFC c
   ; exiFC := exiFC c
   ; indC := indC c
  |}.
Next Obligation. by destruct ctx. Qed.
Next Obligation. by destruct ctx. Qed.

Program Definition incExiAd {ctx} {X Y Z} {c}
  (ad : @SemiDenotation ctx c X Y Z) : SemiDenotation (incExiCC c) X Y (Z.+1) :=
  fun X Y M =>
  {| exiVAdv := ExtendAt0N
                  (fun _ => Y 0) 
                  (exiVAdv (ad X (fun y => Y (y.+1)) M))
    ; exiFAdv := exiFAdv (ad X (fun y => Y (y.+1)) M)
    ; freeFCallOut := freeFCallOut (ad X (fun y => Y (y.+1)) M)
    ; exiFCallOut := exiFCallOut (ad X (fun y => Y (y.+1)) M)
    ; indCallOut := indCallOut (ad X (fun y => Y (y.+1)) M)
   |}.
Next Obligation. by destruct ctx, c. Qed. Next Obligation. by destruct ctx, c. Qed.
Next Obligation. by destruct ctx, c. Qed.
Next Obligation. 
  remember (incExiAd_obligation_6 _ _ _ _ _ _ _) as P; clear HeqP; simpl in P.
  destruct ctx, c; replace H0 with P;[auto|apply eq_irrelevance].
Qed.
Next Obligation. by destruct ctx, c. Qed. Next Obligation. by destruct ctx, c. Qed.
Next Obligation. by destruct ctx, c. Qed.

Program Fixpoint PolyLiftExiV {ctx c}
  (p : @SCPoly ctx c) :
  @SCPoly _ (incExiCC c) := 
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
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed. 
Next Obligation.
  remember (incExiCC_obligation_1 _ _ _) as P; clear HeqP; simpl in P.
  replace P with H0;[auto|apply eq_irrelevance].
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  remember (incExiCC_obligation_2 _ _ _) as P; clear HeqP; simpl in P.
  replace P with H0;[auto|apply eq_irrelevance].
Qed.

Fixpoint PropLiftExiV {ctx c}
  (p : @SemicircuitPropConstraint ctx c) :
  @SemicircuitPropConstraint _ (incExiCC c) := 
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

Program Definition incUniCC {ctx} (c : @SemicircuitCtx ctx) : @SemicircuitCtx (incUniV ctx) :=
  {| freeFC := freeFC c
   ; exiFC := exiFC c
   ; indC := indC c
  |}.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.

Program Definition incUniAd {ctx c X Y Z}
  (ad : @SemiDenotation ctx c X Y Z) : SemiDenotation (incUniCC c) X Y Z :=
  fun X Y M =>
  {| exiVAdv := fun x t => exiVAdv (ad X Y M) x (fun y => t (y.+1))
   ; exiFAdv := exiFAdv (ad X Y M)
   ; freeFCallOut := fun i n t => freeFCallOut (ad X Y M) i n (fun y => t (y.+1))
   ; exiFCallOut := fun i n t => exiFCallOut (ad X Y M) i n (fun y => t (y.+1))
   ; indCallOut := fun n t => indCallOut (ad X Y M) n (fun y => t (y.+1))
  |}.
Next Obligation. destruct ctx, c; assumption. Qed.
Next Obligation. destruct ctx, c; assumption. Qed.
Next Obligation. destruct ctx, c; assumption. Qed.
Next Obligation.
  remember (incUniAd_obligation_3 _ _ _ _ _ _ _) as Q; clear HeqQ;
  destruct ctx, c;
  unfold incUniCC in *; cbn in *;
  replace Q with H0 in H;[auto|apply eq_irrelevance].
Qed.
Next Obligation. by destruct ctx, c. Qed.
Next Obligation. by destruct ctx, c. Qed.
Next Obligation. by destruct ctx, c. Qed.

Program Fixpoint PolyLiftUniV {ctx c}
  (p : @SCPoly ctx c) :
    @SCPoly _ (incUniCC c) := 
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
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation.
  remember (incUniCC_obligation_1 _ _ _) as P; clear HeqP; simpl in P.
  replace P with H0; auto.
  apply eq_irrelevance.
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  remember (incUniCC_obligation_2 _ _ _) as P; clear HeqP; simpl in P.
  replace P with H0; auto.
  apply eq_irrelevance.
Qed.

Fixpoint PropLiftUniV {ctx c}
  (p : @SemicircuitPropConstraint ctx c) :
  @SemicircuitPropConstraint _ (incUniCC c) := 
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
Program Definition SemicircuitExiInc {ctx} (c : @SemiCircuit ctx)
  (p : @SCPoly _ (Ctx c)): SemiCircuit :=
  {| Ctx := incExiCC (Ctx c)
  ; nu := ExtendAt0N (uniV ctx) (nu c)
  ; polyConstraints := map PolyLiftExiV (rcons (polyConstraints c) p)
  ; freeFArgs := freeFArgs c
  ; exiFArgs := exiFArgs c
  ; indArgs := indArgs c
  ; uniVBounds := uniVBounds c
  ; exiVBounds := ExtendAt0N (length (polyConstraints c)) (exiVBounds c)
  ; exiFOutputBounds := exiFOutputBounds c
  ; exiFInputBounds := exiFInputBounds c
  ; formula := inrMap PropLiftExiV (formula c)
  |}.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  unfold ExtendAt0N; dep_if_case (x == 0); auto.
  by destruct ctx.
  by destruct ((` (nu c)) _), ctx.
Qed.
Next Obligation. 
  unfold ExtendAt0N; dep_if_case (j == 0); auto.
  rewrite dep_if_case_true; auto.
  by destruct i, j.
  dep_if_case (i == 0); auto.
  by destruct ((` (nu c)) _), ctx. 
  destruct (nu c).
  apply i0.
  by destruct i, j.
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
  remember (incExiCC_obligation_1 _ _ _) as P; clear HeqP; simpl in P.
  destruct ctx; simpl in *.
  replace P with H1;[auto|apply eq_irrelevance].
Qed.
Next Obligation.
  destruct (freeFArgs _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation.
  remember (incExiCC_obligation_2 _ _ _) as P; clear HeqP; simpl in P.
  destruct ctx; simpl in *.
  replace P with H1;[auto|apply eq_irrelevance].
Qed.
Next Obligation.
  destruct (exiFArgs _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  destruct (uniVBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  unfold ExtendAt0N.
  dep_if_case (x == 0); auto.
  rewrite map_length length_rcons; sfirstorder.
  destruct (exiVBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  destruct (exiFOutputBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  remember (SemicircuitExiInc_obligation_16 _ _ _ _) as P; clear HeqP.
  destruct ctx; simpl in *.
  by replace P with H0;[|apply eq_irrelevance].
Qed.
Next Obligation.
  destruct (exiFInputBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.

Definition SemicircuitExiIncWA {ctx X Y Z}
  (c : {s : @SemiCircuit ctx & SemiDenotation (Ctx s) X Y Z}) :
  @SCPoly ctx (Ctx (projT1 c)) ->
  {s : SemiCircuit & SemiDenotation (Ctx s) X Y (Z.+1)} :=
match c with
| existT s ad => fun p => existT _ (SemicircuitExiInc s p) (incExiAd ad)
end.

(*What is going on? Why do these need to be separate functions?*)
Definition PolyIntExi {ctx X Y Z}
  (c : @SemiCircuit ctx)
  (adc : SemiDenotation (Ctx c) X Y Z)

  (d : @SemiConversionData ctx)
  (ad : SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
  (p : @SCPoly _ (@SemiConversionDataCtx ctx d)) :=

  SemicircuitExiIncWA (IntegrateConversionData (existT _ c adc) (existT _ d ad)) (PolyCallLift p).

Definition IntegrateNewPolyExi {ctx X Y Z}
  (s : {s' : @SemiCircuit ctx & SemiDenotation (Ctx s') X Y Z })

  (p : { d : @SemiConversionData ctx &  
        prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
            (@SCPoly _ (@SemiConversionDataCtx ctx d)) }) :
  {s0 : SemiCircuit & SemiDenotation (Ctx s0) X Y Z.+1} :=
  match s, p with
  | existT c adc, existT d (ad, p) => PolyIntExi c adc d ad p
  end.

(*Add a new universally quantified first order variable to semicircuit *)
Program Definition SemicircuitUniInc {ctx} (c : SemiCircuit) (p : @SCPoly ctx (Ctx c)): SemiCircuit :=
  {| Ctx := incUniCC (Ctx c)
  ; nu := nu c
  ; polyConstraints := map PolyLiftUniV (rcons (polyConstraints c) p)
  ; freeFArgs := freeFArgs c
  ; exiFArgs := exiFArgs c
  ; indArgs := indArgs c
  ; uniVBounds := ExtendAt0N (length (polyConstraints c)) (uniVBounds c)
  ; exiVBounds := exiVBounds c
  ; exiFOutputBounds := exiFOutputBounds c
  ; exiFInputBounds := exiFInputBounds c
  ; formula := inrMap PropLiftUniV (formula c)
  |}.
Next Obligation. by destruct ctx. Qed.
Next Obligation. by destruct ((` (nu c)) _), ctx; apply leqW. Qed.
Next Obligation. by destruct (nu c); apply i0. Qed.
Next Obligation.
  destruct (indArgs _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation.
  destruct (indArgs _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation.
  remember (incUniCC_obligation_1 _ _ _) as P; clear HeqP; simpl in P.
  destruct ctx; simpl in *.
  replace P with H1;auto.
  apply eq_irrelevance.
Qed.
Next Obligation.
  destruct (freeFArgs _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation.
  remember (incUniCC_obligation_2 _ _ _) as P; clear HeqP; simpl in P.
  destruct ctx; simpl in *.
  replace P with H1;auto.
  apply eq_irrelevance.
Qed.
Next Obligation.
  destruct (exiFArgs _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  unfold ExtendAt0N.
  dep_if_case (x == 0); auto.
  rewrite map_length length_rcons; sfirstorder.
  destruct (uniVBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  destruct (exiVBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  destruct (exiFOutputBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  remember (SemicircuitUniInc_obligation_16 _ _ _ _) as P; clear HeqP; simpl in P.
  destruct ctx; simpl in *.
  replace P with H0;auto.
  apply eq_irrelevance.
Qed.
Next Obligation.
  destruct (exiFInputBounds _ _).
  rewrite map_length length_rcons; sfirstorder.
Qed.

Definition SemicircuitUniIncWA {ctx} {X Y Z}
  (c : {s : @SemiCircuit ctx & SemiDenotation (Ctx s) X Y Z}) :
  @SCPoly _ (Ctx (projT1 c)) ->
  {s : SemiCircuit & SemiDenotation (Ctx s) X Y Z} :=
  match c with
  | existT s ad => fun p => existT _ (SemicircuitUniInc s p) (incUniAd ad)
  end.

(*What is going on? Why do these need to be separate functions?*)
Definition PolyIntUni {ctx X Y Z}
  (c : @SemiCircuit ctx)
  (adc : SemiDenotation (Ctx c) X Y Z)

  (d : @SemiConversionData ctx)
  (ad : SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
  (p : @SCPoly ctx (@SemiConversionDataCtx ctx d)) :=

  SemicircuitUniIncWA (IntegrateConversionData (existT _ c adc) (existT _ d ad)) (PolyCallLift p).

Definition IntegrateNewPolyUni {ctx X Y Z}
  (s : {s' : @SemiCircuit ctx & SemiDenotation (Ctx s') X Y Z })

  (p : { d : @SemiConversionData ctx &  
        prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
            (@SCPoly _ (@SemiConversionDataCtx ctx d)) }) :
  {s0 : SemiCircuit & SemiDenotation (Ctx s0) X Y Z} :=
  match s, p with
  | existT c adc, existT d (ad, p) => PolyIntUni c adc d ad p
  end.

Fixpoint newBounds {c} (f : @FirstOrderFormula c) : nat :=
  match f with
  | ZO f => 0
  | FOExists b f => (newBounds f).+1
  | FOForall b f => newBounds f
  end.

Fixpoint newCtx {c} (f : @FirstOrderFormula c) : Sigma11Ctx :=
  match f with
  | ZO f => c
  | FOExists b f => (newCtx f)
  | FOForall b f => (newCtx f)
  end.

Fixpoint Translate_FirstOrderFormula {ctx X Y Z}
  (s : {s' : @SemiCircuit ctx & SemiDenotation (Ctx s') X Y Z })
  (f : @FirstOrderFormula ctx) : 
  {s' : @SemiCircuit (newCtx f) & SemiDenotation (Ctx s') X Y (newBounds f + Z)} :=
  match f with
  | ZO f => Translate_ZerothOrderFormula s f
  | FOExists b f =>
    let c1 := IntegrateNewPolyExi s (PolyConvert b) in
    eq_rect _ (fun x => {s' : SemiCircuit & SemiDenotation (Ctx s') X Y x}) (Translate_FirstOrderFormula c1 f) _ (esym (addSnnS _ _))
  | FOForall b f =>
    let c1 := IntegrateNewPolyUni s (PolyConvert b) in
    Translate_FirstOrderFormula c1 f
  end.

Definition Hole {A} : A. Admitted.

Program Definition CtxAddExiF {ctx} (a : nat) (c : @SemicircuitCtx ctx) : @SemicircuitCtx (addExiF a ctx) :=
    {| freeFC := freeFC c
     ; exiFC := ExtendAt0N 0 (exiFC c)
     ; indC := indC c
    |}.
Next Obligation. by destruct ctx. Qed.
Next Obligation. by destruct ctx. Qed.

Program Fixpoint PolyLiftAddExiF {ctx c}
  (a : nat)
  (p : @SCPoly ctx c) :
    @SCPoly _ (CtxAddExiF a c) := 
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
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. by destruct i, ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. 
  remember (CtxAddExiF_obligation_1 _ _ _ _) as P; clear HeqP.
  by replace P with H0;[|apply eq_irrelevance].
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  unfold ExtendAt0N; simpl.
  remember (Utils.ExtendAt0N_obligation_2 _ _ _) as P; clear HeqP; simpl in P.
  by replace P with H0;[|apply eq_irrelevance].
Qed.

Program Fixpoint PropLiftAddExiF {ctx c}
  (a : nat)
  (p : @SemicircuitPropConstraint ctx c) :
  @SemicircuitPropConstraint _ (CtxAddExiF a c) := 
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

Program Definition SemicircuitExiFAdd {ctx}
  (c : SemiCircuit) 
  (y : @SCPoly ctx (Ctx c))
  (bs : seq (@SCPoly ctx (Ctx c))) : 
  @SemiCircuit (addExiF (length bs) ctx) :=
  let Ctx' := CtxAddExiF (length bs) (Ctx c) in
  let polyConstraints' := map (PolyLiftAddExiF (length bs)) (rcons (polyConstraints c ++ bs) y) in
  {| Ctx := Ctx'
  ; nu := nu c
  ; polyConstraints := polyConstraints'
  ; indArgs := indArgs c
  ; freeFArgs := freeFArgs c
  ; exiFArgs := fun i =>
    ( if i == 0 as b return (i == 0) = b -> |[exiFC Ctx' i]| -> |[exiFA (addExiF (length bs) ctx) i]| -> |[length polyConstraints']|
      then fun _ => emptyTuple
      else fun _ => exiFArgs c (i.-1) ) (erefl _)
  ; uniVBounds := uniVBounds c
  ; exiVBounds := exiVBounds c
  ; exiFOutputBounds := fun i =>
    (if i == 0 as b return (i == 0) = b -> |[length polyConstraints']|
    then fun _ => length (polyConstraints c) + length bs
    else fun _ => exiFOutputBounds c (i.-1)) (erefl _)
  ; exiFInputBounds := fun i =>
    (if i == 0 as b return (i == 0) = b -> |[exiFA (addExiF (length bs) ctx) i]| -> |[length polyConstraints']|
    then fun _ j => length (polyConstraints c) + j
    else fun _ => exiFInputBounds c (i.-1)) (erefl _)
  ; formula := inrMap (PropLiftAddExiF (length bs)) (formula c)
  |}.
Next Obligation. by destruct ctx. Qed.
Next Obligation.
  destruct ((` (nu c))_).
  clear H.
  by destruct ctx; simpl in *.
Qed.
Next Obligation.
  destruct (nu c); simpl.
  by apply i0.
Qed.
Next Obligation. 
  destruct ((indArgs _ _).1); simpl.
  rewrite map_length length_rcons length_cat. 
  apply (ltn_trans i); clear i x0.
  scongruence use: addSn, Utils.cRange_obligation_1, addSnnS.
Qed.
Next Obligation.
  destruct ((indArgs _ _).2).
  rewrite map_length length_rcons length_cat.
  apply (ltn_trans i); clear i x0.
  scongruence use: addSn, Utils.cRange_obligation_1, addSnnS.
Qed.
Next Obligation. 
  remember (CtxAddExiF_obligation_1 _ _ _ _) as P; clear HeqP; simpl in P.
  destruct ctx; simpl in *.
  by replace P with H1;[|apply eq_irrelevance].
Qed.
Next Obligation. 
  destruct (freeFArgs _ _); clear H H0 H1.
  rewrite map_length length_rcons length_cat.
  remember (length (polyConstraints c)) as a; clear Heqa.
  remember (length bs) as b; clear Heqb.
  hauto use: leq_addl, ltn_addr, addSnnS.
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation. 
  destruct (uniVBounds _ _); clear H.
  rewrite map_length length_rcons length_cat.
  simpl.
  remember (length (polyConstraints c)) as a; clear Heqa.
  remember (length bs) as b; clear Heqb bs y c x.
  hauto use: leq_addl, ltn_addr, addSnnS.
Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation. 
  destruct (exiVBounds _ _); clear H.
  rewrite map_length length_rcons length_cat.
  simpl.
  remember (length (polyConstraints c)) as a; clear Heqa.
  remember (length bs) as b; clear Heqb bs y c x.
  hauto use: leq_addl, ltn_addr, addSnnS.
Qed.
Next Obligation. by destruct (exiF _). Qed.
Next Obligation.
  assert (i <> 0);[by rewrite <- EEFConvert|clear e].
  destruct i;[fcrush|].
  by destruct ctx.
Qed.
Next Obligation.
  destruct (exiFOutputBounds _ _); simpl.
  rewrite map_length length_rcons length_cat.
  remember (length (polyConstraints c)) as a; clear Heqa e.
  remember (length bs) as b; clear Heqb.
  hauto use: leq_addl, ltn_addr, addSnnS.
Qed.
Next Obligation.
  rewrite map_length length_rcons length_cat; apply ltnSn.
Qed.
Next Obligation. by destruct (exiF _). Qed. Next Obligation. by destruct i, ctx. Qed.
Next Obligation.
  clear H0.
  remember (SemicircuitExiFAdd_obligation_17 _ _ _ _ _ _) as P; clear HeqP; simpl in P.
  destruct i, ctx;[fcrush|simpl in *].
  unfold ExtendAt0N in H; simpl in H.
  remember (Utils.ExtendAt0N_obligation_2 _ _ _) as Q; clear HeqQ; simpl in Q.
  by replace P with Q;[|apply eq_irrelevance].
Qed.
Next Obligation.
  unfold ExtendAt0N in H.
  rewrite dep_if_case_false in H; auto.
  remember (SemicircuitExiFAdd_obligation_17 _ _ _ _ _ _) as P; clear HeqP; simpl in P.
  remember (Utils.ExtendAt0N_obligation_2 _ _ _) as Q; clear HeqQ; simpl in Q.
  by replace P with Q;[|apply eq_irrelevance].
Qed.
Next Obligation.
  destruct (exiFArgs _ _ _).
  rewrite map_length length_rcons length_cat.
  clear H H H0 e H1.
  remember (length (polyConstraints c)) as a; clear Heqa.
  remember (length bs) as b; clear Heqb.
  apply (ltn_trans i0).
  scongruence use: addSn, ltnW, Utils.cRange_obligation_1, addSnnS.
Qed.
Next Obligation. 
  unfold ExtendAt0N in H.
  move: H; rewrite dep_if_case_true; auto.
Qed.
Next Obligation. by destruct (exiF _). Qed. Next Obligation. by destruct i, ctx. Qed.
Next Obligation.
  remember (SemicircuitExiFAdd_obligation_23 _ _ _ _ _ _) as P; clear HeqP; simpl in P.
  destruct i, ctx;[fcrush|simpl in *].
  unfold ExtendAt0N in H; simpl in H.
  remember (Utils.ExtendAt0N_obligation_2 _ _ _) as Q; clear HeqQ; simpl in Q.
  by replace P with Q;[|apply eq_irrelevance].
Qed.
Next Obligation. 
  destruct (exiFInputBounds _ _). 
  rewrite map_length length_rcons length_cat.
  remember (length (polyConstraints c)) as n; clear Heqn e;
  remember (length bs) as m; clear Heqm.
  apply (ltn_trans i0).
  scongruence use: addSn, ltnW, Utils.cRange_obligation_1, addSnnS.
Qed. 
Next Obligation.
  rewrite map_length length_rcons length_cat.
  destruct ctx; simpl in *.
  unfold ExtendAt0N in H; simpl in H.
  rewrite dep_if_case_true in H; auto.
  remember (length (polyConstraints c)) as n; clear Heqn e;
  remember (length bs) as m; clear Heqm.
  clear H0 bs y c uniV exiFA exiV exiF freeFA freeV freeF i.
  hauto use: ltnW, ltn_add2l unfold: is_true.
Qed.

Ltac incExiFAddAdScript H HeqP H0 := 
  unfold ExtendAt0N in H; simpl in H;
  remember (Utils.ExtendAt0N_obligation_2 _ _ _) as P; clear HeqP; simpl in P;
  by replace H0 with P;[|apply eq_irrelevance].

Program Definition incExiFAddAd {ctx} {exFN Y Z} {c} {a}
  (ad : @SemiDenotation ctx c exFN Y Z) : 
  SemiDenotation (CtxAddExiF a c) (exFN.+1) (ExtendAt0N a Y) Z :=
  fun X Y M =>
  {| exiVAdv := exiVAdv (ad (fun y => X (y.+1)) Y M)
   ; exiFAdv := fun x : |[exiF (addExiF a ctx)]| => (
      if x == 0 as b return ((x == 0) = b -> (|[exiFA (addExiF a ctx) x]| -> T D) -> option (T D))
      then fun _ => X 0
      else fun _ => exiFAdv (ad (fun y => X (y.+1)) Y M) (x.-1) 
    ) (erefl _)
   ; freeFCallOut := freeFCallOut (ad (fun y => X (y.+1)) Y M)
   ; exiFCallOut := fun x : |[exiF (addExiF a ctx)]| =>(
      if x == 0 as b return ((x == 0) = b -> |[exiFC (CtxAddExiF a c) x]| -> (|[uniV ctx]| -> T D) -> option (T D))
      then fun _ => emptyTuple
      else fun _ => exiFCallOut (ad (fun y => X (y.+1)) Y M) (x.-1) 
    ) (erefl _)
   ; indCallOut := indCallOut (ad (fun y => X (y.+1)) Y M)
  |}.
Next Obligation. incExiFAddAdScript H HeqP H0. Qed.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. incExiFAddAdScript H HeqP H0. Qed.
Next Obligation. by destruct ctx. Qed. Next Obligation. by destruct ctx. Qed.
Next Obligation. incExiFAddAdScript H HeqP H0. Qed.
Next Obligation. by destruct ctx. Qed.
Next Obligation. by destruct (exiF _). Qed.
Next Obligation. by destruct x, ctx. Qed.
Next Obligation.
  remember (incExiFAddAd_obligation_13 _ _ _ _ _ _ _ _ _) as P; clear HeqP; simpl in P.
  destruct x;[fcrush|].
  unfold ExtendAt0N in H; simpl in H.
  remember (Utils.ExtendAt0N_obligation_2 _ _ _) as Q; clear HeqQ; simpl in Q.
  by replace P with Q;[|apply eq_irrelevance].
Qed.
Next Obligation. incExiFAddAdScript H HeqP H0. Qed.
Next Obligation.
  unfold ExtendAt0N in H; simpl in H.
  move: H.
  rewrite dep_if_case_true; auto.
Qed.
Next Obligation. by destruct (exiF _). Qed.
Next Obligation. by destruct x, ctx. Qed.
Next Obligation.
  destruct x;[fcrush|]. 
  remember (incExiFAddAd_obligation_19 _ _ _ _ _ _ _ _ _) as P; clear HeqP; simpl in P.
  destruct ctx; cbn.
  remember (Utils.ExtendAt0N_obligation_2 _ _ _) as Q; clear HeqQ; simpl in Q.
  by replace Q with P;[|apply eq_irrelevance].
Qed.
Next Obligation. incExiFAddAdScript H HeqP H0. Qed.
Next Obligation.
  remember (incExiFAddAd_obligation_23 _ _ _ _ _) as P; clear HeqP; simpl in P.
  destruct ctx; simpl.
  unfold ExtendAt0N in *.
  move: H.
  rewrite dep_if_case_true; auto.
Qed.

(* 
Definition PolyIntExiF {ctx X Y Z}
  (c : @SemiCircuit ctx)
  (adc : SemiDenotation (Ctx c) X Y Z)

  (y : @SemiConversionData ctx)
  (ady : SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
  (poy : @SCPoly _ (@SemiConversionDataCtx ctx d))

  (bs : @SemiConversionData ctx)
  (adbs : SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
  (pobs : seq (@SCPoly _ (@SemiConversionDataCtx ctx d))) :=

  SemicircuitUniIncWA (IntegrateConversionData (existT _ c adc) (existT _ d ad)) (PolyCallLift p).

Definition IntegrateNewPolyExiF {ctx X Y Z}
  (s : {s' : @SemiCircuit ctx & SemiDenotation (Ctx s') X Y Z })

  (y : { d : @SemiConversionData ctx &  
        prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
             (@SCPoly _ (@SemiConversionDataCtx ctx d)) })

  (bs : seq 
      { d : @SemiConversionData ctx &  
        prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
             (@SCPoly _ (@SemiConversionDataCtx ctx d)) }) :

  {s0 : @SemiCircuit ctx & SemiDenotation (Ctx s0) X Y Z} :=
  match y with 
  | existT day (poy, ady) => 
    match PolyCallSeqFuse bs with
    | existT dabs (pobs, adbs) =>
      let c0 := IntegrateConversionData s (existT _ day ady) in
      let c1 := IntegrateConversionData c0 (existT _ dabs adbs) in
      Hole
    end
  end.

  let (day, poy, ad) := y in
  Hole.

(*What is going on? Why do these need to be separate functions?*)
Definition PolyIntExiF {ctx X Y Z}
  (c : @SemiCircuit ctx)
  (adc : SemiDenotation (Ctx c) X Y Z)

  (d : @SemiConversionData ctx)
  (ad : SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
  (p : @SCPoly _ (@SemiConversionDataCtx ctx d)) :=

  SemicircuitUniIncWA (IntegrateConversionData (existT _ c adc) (existT _ d ad)) (PolyCallLift p).

Definition IntegrateNewPolyExiF {ctx X Y Z}
  (s : {s' : @SemiCircuit ctx & SemiDenotation (Ctx s') X Y Z })

  (y : { d : @SemiConversionData ctx &  
        prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
             (@SCPoly _ (@SemiConversionDataCtx ctx d)) }) :

  (bs : seq 
      { d : @SemiConversionData ctx &  
        prod (SemiDenotation (@SemiConversionDataCtx ctx d) X Y Z)
             (@SCPoly _ (@SemiConversionDataCtx ctx d)) }) :

  {s0 : SemiCircuit & SemiDenotation (Ctx s0) X Y Z} :=
  match s, p with
  | existT c adc, existT d (ad, p) => PolyIntUni c adc d ad p
  end.


Fixpoint newCtx2 {c} (f : @SecondOrderFormula c) : Sigma11Ctx :=
  match f with
  | FO f => newCtx f
  | SOExists y bs f => (newCtx2 f)
  end.

Program Fixpoint Translate_SecondOrderFormula 
  (c : SemiCircuit)
  (f : @SecondOrderFormula ctx) : @SemiCircuit (newCtx2 f) :=
  match f with
  | FO f => Translate_FirstOrderFormula c f
  | SOExists y bs f => 
    let (day, poy) := PolyConvert y in
    let c0 := IntegrateConversionData c day in
    let poy0 : @SCPoly (Ctx c0) := PolyCallLift poy in
    let bs' := map PolyConvert bs in
    let (dabs, pobs) := PolyCallSeqFuse bs' in
    let c1 := IntegrateConversionData c0 dabs in
    let poy1 : @SCPoly (Ctx c1) := PolyCallCast poy0 in
    let pobs1 : seq (@SCPoly (Ctx c1)) := map PolyCallLift pobs in
    let c2 := SemicircuitExiFAdd c1 poy1 pobs1 in
    Translate_SecondOrderFormula c2 f
  end.
Next Obligation.
  do 2 rewrite map_length in H *.
  by rewrite H.
Qed. *)

End SemicircuitTranslation.
