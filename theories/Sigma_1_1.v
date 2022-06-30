From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Section Sigma_1_1_Internal.

Definition SOctx := seq (nat * seq nat).
Definition FOctx := seq nat.

Inductive RingTerm {soctx : SOctx} {foctx : FOctx} : Type :=
| RingVar : 'I_(length foctx) -> RingTerm
| RingFun : forall (i : 'I_(length soctx)),
            ('I_(length (snd (tnth (in_tuple soctx) i))) -> RingTerm) ->
            RingTerm
| RingMinusOne : RingTerm
| RingPlusOne : RingTerm
| RingZero : RingTerm
| RingPlus : RingTerm -> RingTerm -> RingTerm
| RingTimes : RingTerm -> RingTerm -> RingTerm.

Definition RingTermFOQuote {soctx} {foctx} {n} : 
  @RingTerm soctx foctx ->
  RingTerm (soctx := soctx) (foctx := n :: foctx).
  intro r.
  induction r.
  - apply RingVar.
    destruct o as [o lto].
    apply (Ordinal (m := o.+1)); auto.
  - apply (RingFun i).
    intro.
    exact (X X0).
  - exact RingMinusOne.
  - exact RingPlusOne.
  - exact RingZero.
  - exact (RingPlus IHr1 IHr2).
  - exact (RingTimes IHr1 IHr2).
Defined.

Theorem RingTermFOQuote_Fun_Step {soctx} {foctx} {n}
  (i : 'I_(length soctx))
  (t : 'I_(length (snd (tnth (in_tuple soctx) i))) -> RingTerm (foctx := foctx)) :
  RingTermFOQuote (n := n) (RingFun i t) =
  RingFun i (fun x => RingTermFOQuote (t x)).
Proof. reflexivity. Qed.

Definition RingTermSOQuote {soctx} {foctx} {n} {l} : 
  @RingTerm soctx foctx ->
  RingTerm (soctx := (n, l) :: soctx) (foctx := foctx).
  elim.
  - apply RingVar.
  - move=>[i lti] _ IH.
    assert (i.+1 < length ((n, l) :: soctx));[auto|].
    apply (RingFun (Ordinal (m := i.+1) H)).
    move=>[j ltj].
    apply: IH.
    apply (Ordinal (m := j)).
    by do 2 rewrite (tnth_nth (0, nil)) in ltj *.
  - exact RingMinusOne.
  - exact RingPlusOne.
  - exact RingZero.
  - intros r1 IHr1 r2 IHr2.
    exact (RingPlus IHr1 IHr2).
  - intros r1 IHr1 r2 IHr2.
    exact (RingTimes IHr1 IHr2).
Defined.

Theorem RingTermSOQuote_Fun_Step {soctx} {foctx} {n} {l}
  (i : nat) (lti : i < length soctx)
  (t : 'I_(length ((tnth (in_tuple soctx) (Ordinal lti)).2)) -> RingTerm (foctx := foctx)) :
  RingTermSOQuote (RingFun (Ordinal lti) t) = 
  RingFun (Ordinal (n:=length ((n, l) :: soctx)) (m:=i.+1) lti) 
          (fun x => RingTermSOQuote (t (eq_rect _ (fun x => 'I_(length x.2)) x _ (tnth_tuple_index (n, l) lti)))).
Proof.
  unfold RingTermSOQuote at 1.
  unfold RingTerm_rect.
  f_equal.
  apply functional_extensionality.
  move=>[x ltx].
  unfold RingTermSOQuote, RingTerm_rect.
  do 2 f_equal.
  apply ord_inj.
  destruct (tnth_tuple_index _ _); reflexivity.
Qed.

Definition RingTermFOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_(length foctx)),
  @RingTerm soctx (drop_index i foctx) ->
  @RingTerm soctx foctx ->
  @RingTerm soctx (drop_index i foctx).
  move=> [i lti] t s.
  induction s.
  - destruct o as [o lto].
    destruct (Nat.compare i o) eqn:comp.
    + exact t.
    + apply RingVar.
      rewrite drop_index_length;[|auto].
      assert (o-1 < length foctx - 1) as H;[|exact (Ordinal (m:=o-1) H)].
      rewrite <- Compare_dec.nat_compare_lt in comp.
      apply (introT (b := i < o) ltP) in comp.
      destruct o;[auto|].
      destruct (length foctx) as [|lf];[auto|];
      destruct lf as [|lf2];[auto|].
      hauto use: subn1, pred_Sn, ltn_predRL q: on.
    + rewrite <- Compare_dec.nat_compare_gt in comp.
      apply (introT (b := o < i) ltP) in comp.
      apply RingVar.
      rewrite drop_index_length;[|auto].
      apply (Ordinal (m:=o)).
      destruct i;[auto|].
      destruct (length foctx) as [|lf];[auto|];
      destruct lf as [|lf2];[auto|].
      hauto use: (leq_ltn_trans (n := i)), pred_Sn, subn1.
  - apply (RingFun i0).
    intro.
    exact (X X0).
  - exact RingMinusOne.
  - exact RingPlusOne.
  - exact RingZero.
  - exact (RingPlus IHs1 IHs2).
  - exact (RingTimes IHs1 IHs2).
Defined.

Theorem RingTermFOSubst_Fun_Step {soctx} {foctx}
  (i : 'I_(length foctx))
  (j : 'I_(length soctx))
  (r : @RingTerm soctx (drop_index i foctx))
  (t : 'I_(length (snd (tnth (in_tuple soctx) j))) -> RingTerm (foctx := foctx)) :
  RingTermFOSubst i r (RingFun j t) =
  RingFun j (fun x => RingTermFOSubst i r (t x)).
Proof. destruct i; reflexivity. Qed.

Theorem FOsubsts_unquote {soctx : SOctx} {foctx : FOctx} :
  forall n
         (x : @RingTerm soctx foctx)
         (e : @RingTerm soctx foctx)
         (H : 0 < length (n :: foctx)),
  RingTermFOSubst (Ordinal H) x (RingTermFOQuote (n := n) e) = e.
Proof.
  move=> n x; elim; try hauto q:on.
  - move=>[o lto] H.
    ssimpl; f_equal.
    apply ord_inj.
    assert (forall x, x.+1 - 1 = x);[hauto use: subn1, pred_Sn|].
    assert (length (drop_index 0 (n :: foctx)) = length (n :: foctx) - 1) as H3;[hauto|].
    rewrite (eq_irrelevance (drop_index_length _ _ _) H3).
    hauto.
  - move=> [i lti] t rH triv.
    rewrite RingTermFOQuote_Fun_Step RingTermFOSubst_Fun_Step.
    f_equal.
    apply functional_extensionality; move=> [j ltj].
    by rewrite rH.
Qed.

Definition RingTermSOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_(length soctx)),
  (('I_(length (snd (tnth (in_tuple soctx) i))) -> 
   RingTerm  (soctx := drop_index i soctx) (foctx := foctx)) -> 
   RingTerm (soctx := drop_index i soctx) (foctx := foctx)) ->
  @RingTerm soctx foctx ->
  RingTerm (soctx := drop_index i soctx) (foctx := foctx).
  move=> [i lti] f; elim.
  - apply RingVar.
  - move=> [j ltj].
    destruct (Nat.compare i j) eqn:comp.
    + apply Compare_dec.nat_compare_eq in comp.
      move: ltj; rewrite <- comp=> ltj.
      rewrite (eq_irrelevance ltj lti); clear comp j ltj=> t tH.
      exact (f tH).
    + clear f.
      rewrite <- Compare_dec.nat_compare_lt in comp.
      apply (introT (b := i < j) ltP) in comp.
      move=> _ tH.
      assert (j-1 < length (drop_index i soctx)) as H.
      { rewrite drop_index_length; auto.
        destruct j; auto; clear tH; destruct (length soctx); [auto|sauto q:on lazy:on]. }
      apply (RingFun (Ordinal (m := j-1) H)).
      move=> [o lto].
      apply: tH.
      apply (Ordinal (m:=o)).
      do 2 rewrite (tnth_nth (0, nil)) in lto *.
      simpl; simpl in lto.
      by rewrite drop_index_nth_high in lto.
    + clear f.
      rewrite <- Compare_dec.nat_compare_gt in comp.
      apply (introT (b := j < i) ltP) in comp.
      move=> _ tH.
      assert (j < length (drop_index i soctx)) as H.
      { rewrite drop_index_length; auto.
        clear tH; destruct (length soctx);[fcrush|].
        replace (n.+1 - 1) with n;[|sauto q:on lazy:on].
        hauto use: pred_Sn, ltn_predRL, leq_ltn_trans. }
      apply (RingFun (Ordinal (m := j) H)).
      move=>[o lto]; apply: tH.
      do 2 rewrite (tnth_nth (0, nil)) in lto *.
      simpl; simpl in lto.
      rewrite drop_index_nth_low in lto; sauto q:on.
  - exact RingMinusOne.
  - exact RingPlusOne.
  - exact RingZero.
  - intros r1 IHr1 r2 IHr2.
    exact (RingPlus IHr1 IHr2).
  - intros r1 IHr1 r2 IHr2.
    exact (RingTimes IHr1 IHr2).
Defined.

Lemma Lt_Compare_match {i} {j} {Q : comparison -> Type} 
  {a : Q Eq} {b : Q Lt} {c : Q Gt} 
  (comp : Lt = Nat.compare i j) :
  (match Nat.compare i j as c return (Q c) with
  | Eq => a
  | Lt => b
  | Gt => c
  end) = eq_rect _ Q b _ comp.
Proof. destruct comp; reflexivity. Qed.

Lemma Lt_Compare_match_fun {i} {j} {Q : comparison -> Type} {R : Type}
  {a : Q Eq -> R} {b : Q Lt -> R} {c : Q Gt -> R} 
  (v : Q (Nat.compare i j))
  (comp : Nat.compare i j = Lt) :
  match Nat.compare i j as c return (Q c -> R) with
  | Eq => a
  | Lt => b
  | Gt => c
  end v = b (eq_rect _ Q v _ comp).
Proof.
  rewrite (Lt_Compare_match (esym comp)).
  destruct comp; reflexivity.
Qed.

Theorem RingTermSOSubst_Fun_Step_Lt {soctx : SOctx} {foctx : FOctx}
  (i : nat) (lti : i < length soctx)
  (f : ('I_(length ((tnth (in_tuple soctx) (Ordinal lti)).2)) -> 
        RingTerm (soctx := drop_index i soctx) (foctx := foctx)) -> 
        RingTerm (soctx := drop_index i soctx) (foctx := foctx))
  (j : nat) (ltj : j < length soctx)
  (t : 'I_(length ((tnth (in_tuple soctx) (Ordinal ltj)).2)) -> 
        RingTerm  (soctx := soctx) (foctx := foctx))
  (ltij : i < j) :
  RingTermSOSubst (Ordinal lti) f (RingFun (Ordinal ltj) t) =
  RingFun (Ordinal (n:=length (drop_index (Ordinal lti) soctx)) (m:=j - 1) (index_low_decr ltij ltj))
          (fun x => RingTermSOSubst (Ordinal lti) f
                      (t (eq_rect _ (fun x => 'I_(length x.2)) x _ 
                         (decr_index_const ltj (index_low_decr ltij ltj) ltij)))).
Proof.
  assert (PeanoNat.Nat.compare i j = Lt) as comp_lt;[exact 
    (iffLR (Compare_dec.nat_compare_lt i j) (elimT (b := i < j) ltP ltij))|].
  unfold RingTermSOSubst at 1; unfold RingTerm_rect; rewrite (Lt_Compare_match_fun _ comp_lt);
  rewrite (eq_irrelevance (eq_ind_r (fun pv : nat => j - 1 < pv) _ _) (index_low_decr ltij ltj)).
  f_equal.
  apply functional_extensionality;move=>[x ltx].
  unfold RingTermSOSubst, RingTerm_rect; do 2 f_equal.
  remember (eq_ind_r
           (fun pv : nat * seq nat =>
            x < length pv.2 ->
            x < length (tnth (in_tuple soctx) (Ordinal (n:=length soctx) (m:=j) ltj)).2)
           _ _ _) as ltx2 eqn:dx; clear dx.
  destruct (decr_index_const _ _ _); by apply ord_inj.
Qed.

Lemma Gt_Compare_match {i} {j} {Q : comparison -> Type} 
  {a : Q Eq} {b : Q Lt} {c : Q Gt} 
  (comp : Gt = Nat.compare i j) :
  (match Nat.compare i j as c return (Q c) with
  | Eq => a
  | Lt => b
  | Gt => c
  end) = eq_rect _ Q c _ comp.
Proof. destruct comp; reflexivity. Qed.

Lemma Gt_Compare_match_fun {i} {j} {Q : comparison -> Type} {R : Type}
  {a : Q Eq -> R} {b : Q Lt -> R} {c : Q Gt -> R} 
  (v : Q (Nat.compare i j))
  (comp : Nat.compare i j = Gt) :
  match Nat.compare i j as c return (Q c -> R) with
  | Eq => a
  | Lt => b
  | Gt => c
  end v = c (eq_rect _ Q v _ comp).
Proof.
  rewrite (Gt_Compare_match (esym comp)).
  destruct comp; reflexivity.
Qed.

Theorem RingTermSOSubst_Fun_Step_Gt {soctx : SOctx} {foctx : FOctx}
  (i : nat) (lti : i < length soctx)
  (f : ('I_(length ((tnth (in_tuple soctx) (Ordinal lti)).2)) -> 
        RingTerm (soctx := drop_index i soctx) (foctx := foctx)) -> 
        RingTerm (soctx := drop_index i soctx) (foctx := foctx))
  (j : nat) (ltj : j < length soctx)
  (t : 'I_(length ((tnth (in_tuple soctx) (Ordinal ltj)).2)) -> 
        RingTerm  (soctx := soctx) (foctx := foctx))
  (ltij : j < i) :
  RingTermSOSubst (Ordinal lti) f (RingFun (Ordinal ltj) t) =
  RingFun (Ordinal (low_index_bound ltj ltij))
          (fun x => RingTermSOSubst (Ordinal lti) f 
                      (t (eq_rect _ (fun x => 'I_(length x.2)) x _ 
                         (low_index_const ltj (low_index_bound ltj ltij) ltij)))).
Proof.
  assert (PeanoNat.Nat.compare i j = Gt) as comp_gt;[exact 
    (iffLR (Compare_dec.nat_compare_gt i j) (elimT (b := j < i) ltP ltij))|].
  unfold RingTermSOSubst at 1; unfold RingTerm_rect; rewrite (Gt_Compare_match_fun _ comp_gt);
  rewrite (eq_irrelevance (eq_ind_r (fun pv : nat => j < pv) _ _) (low_index_bound ltj ltij)).
  f_equal.
  apply functional_extensionality;move=>[x ltx].
  unfold RingTermSOSubst, RingTerm_rect; do 2 f_equal.
  apply ord_inj.
  unfold eq_rect_r.
  rewrite (rew_map (fun x => x -> _) (fun v => x < length v.2)).
  destruct (low_index_const _ _ _); simpl.
  by destruct (f_equal _ _), (Logic.eq_sym _), (Logic.eq_sym _).
Qed.

Lemma Eq_Compare_match {i} {j} {Q : comparison -> Type} 
  {a : Q Eq} {b : Q Lt} {c : Q Gt} 
  (comp : Eq = Nat.compare i j) :
  (match Nat.compare i j as c return (Q c) with
  | Eq => a
  | Lt => b
  | Gt => c
  end) = eq_rect _ Q a _ comp.
Proof. destruct comp; reflexivity. Qed.

Lemma Eq_Compare_match_fun {i} {j} {Q : comparison -> Type} {R : Type}
  {a : Q Eq -> R} {b : Q Lt -> R} {c : Q Gt -> R} 
  (v : Q (Nat.compare i j))
  (comp : Nat.compare i j = Eq) :
  match Nat.compare i j as c return (Q c -> R) with
  | Eq => a
  | Lt => b
  | Gt => c
  end v = a (eq_rect _ Q v _ comp).
Proof.
  rewrite (Eq_Compare_match (esym comp)).
  destruct comp; reflexivity.
Qed.

Theorem RingTermSOSubst_Fun_Step_Eq {soctx : SOctx} {foctx : FOctx}
  (i : nat) (lti : i < length soctx)
  (f : ('I_(length ((tnth (in_tuple soctx) (Ordinal lti)).2)) -> 
        RingTerm (soctx := drop_index i soctx) (foctx := foctx)) -> 
        RingTerm (soctx := drop_index i soctx) (foctx := foctx))
  (t : 'I_(length ((tnth (in_tuple soctx) (Ordinal lti)).2)) -> 
        RingTerm  (soctx := soctx) (foctx := foctx)) :
  RingTermSOSubst (Ordinal lti) f (RingFun (Ordinal lti) t) =
  f (fun x => RingTermSOSubst (Ordinal lti) f (t x)).
Proof.
  unfold RingTermSOSubst at 1; unfold RingTerm_rect; rewrite (Eq_Compare_match_fun _ (PeanoNat.Nat.compare_refl i)).
  rewrite <- Eqdep.Eq_rect_eq.eq_rect_eq.
  unfold eq_rect_r.
  rewrite <- Eqdep.Eq_rect_eq.eq_rect_eq.
  reflexivity.
Qed.

(* A generalized version where i and j are merely assumed equal
Theorem RingTermSOSubst_Fun_Step_Eq {soctx : SOctx} {foctx : FOctx}
  (i : nat) (lti : i < length soctx)
  (f : ('I_(length ((tnth (in_tuple soctx) (Ordinal lti)).2)) -> 
        RingTerm (soctx := drop_index i soctx) (foctx := foctx)) -> 
        RingTerm (soctx := drop_index i soctx) (foctx := foctx))
  (j : nat) (ltj : j < length soctx)
  (t : 'I_(length ((tnth (in_tuple soctx) (Ordinal ltj)).2)) -> 
        RingTerm  (soctx := soctx) (foctx := foctx))
  (ltij : j = i) 
  (ltm : i < length (@drop_index (nat * seq nat) i soctx))
  (e : tnth (in_tuple soctx) (Ordinal lti) = 
       tnth (in_tuple soctx) (Ordinal ltj)) :
  RingTermSOSubst (Ordinal lti) f (RingFun (Ordinal ltj) t) =
  f (fun x => t (eq_rect _ (fun x => 'I_(length x.2)) x _ e)).
Proof.
*)

Lemma eq_rect_f_ap {T} {B} {Q : T -> Type} {a b : T} {e : a = b}
  (f : Q a -> B) :
  eq_rect _ (fun x => Q x -> B) f _ e
  = fun x => f (eq_rect _ Q x _ (esym e)).
Proof. by destruct e. Qed.

Theorem SOsubsts_unquote {soctx : SOctx} {foctx : FOctx} :
  forall n l
         (e : @RingTerm soctx foctx)
         (H : 0 < length ((n, l) :: soctx)) f,
  RingTermSOSubst (Ordinal H) f (RingTermSOQuote (n := n) (l := l) e) = e.
Proof.
  move=> n l; elim.
  - hauto.
  - move=> [i lti] t IHe H f.
    assert (forall i, i.+1 - 1 = i) as ipm;[hauto use: subn1, pred_Sn|].
    rewrite RingTermSOQuote_Fun_Step.
    rewrite RingTermSOSubst_Fun_Step_Lt.
    change (drop_index _ (_ :: soctx)) with soctx.
    assert (Ordinal (n:=length soctx) (m:=i) lti =
            Ordinal (n:=length soctx) (m:=i.+1 - 1)
                    (@index_low_decr 0 i.+1 _ ((n, l) :: soctx) H lti)) as H0;[apply ord_inj;hauto|].
    transitivity 
      (RingFun (Ordinal (n:=length soctx) (m:=i.+1 - 1) (@index_low_decr 0 i.+1 _ ((n, l) :: soctx) H lti)) 
      (eq_rect _ (fun x => 'I_(length (tnth _ x).2) -> _) t _ H0));[|destruct H0;reflexivity].
    f_equal.
    apply functional_extensionality.
    move=>[x ltx].
    rewrite IHe; clear IHe.
    rewrite eq_rect_f_ap.
    f_equal.
    apply ord_inj.
    rewrite (rew_map (fun x => 'I_(length x.2)) (tnth (in_tuple soctx))).
    do 3 rewrite <- (map_subst (P := (fun x => 'I_(length x.2))) (fun _ p => nat_of_ord p)).
    by do 3 rewrite rew_const.
  - hauto.
  - hauto.
  - hauto.
  - move=> r1 IHr1 r2 IHr2 h f.
    by rewrite <- IHr1 at 2; rewrite <- IHr2 at 2.
  - move=> r1 IHr1 r2 IHr2 h f.
    by rewrite <- IHr1 at 2; rewrite <- IHr2 at 2.
Qed.

Inductive FirstOrderFormula {soctx : SOctx} {foctx : FOctx} : Type :=
| FOTrue : FirstOrderFormula
| FOFalse : FirstOrderFormula
| FONot : FirstOrderFormula -> FirstOrderFormula
| FOAnd : FirstOrderFormula ->
          FirstOrderFormula ->
          FirstOrderFormula
| FOOr : FirstOrderFormula ->
         FirstOrderFormula ->
         FirstOrderFormula
| FOImp : FirstOrderFormula ->
          FirstOrderFormula ->
          FirstOrderFormula
| FOEq : @RingTerm soctx foctx -> 
         @RingTerm soctx foctx ->
         FirstOrderFormula
| FOExists : forall n, FirstOrderFormula (foctx := n :: foctx) ->
                       FirstOrderFormula
| FOForall : forall n, FirstOrderFormula (foctx := n :: foctx) ->
                       FirstOrderFormula. 

Definition FirstOrderFormulaFOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_(length foctx)),
  @RingTerm soctx (drop_index i foctx) ->
  @FirstOrderFormula soctx foctx ->
  @FirstOrderFormula soctx (drop_index i foctx).
  intros i t s.
  induction s.
  - exact FOTrue.
  - exact FOFalse.
  - exact (FONot (IHs i t)).
  - exact (FOAnd (IHs1 i t) (IHs2 i t)).
  - exact (FOOr (IHs1 i t) (IHs2 i t)).
  - exact (FOImp (IHs1 i t) (IHs2 i t)).
  - exact (FOEq (RingTermFOSubst i t r) (RingTermFOSubst i t r0)).
  - apply (FOExists n).
    destruct i as [i lti].
    assert (i.+1 < length (n :: foctx)) as H;[auto|].
    apply (IHs (Ordinal (m := i.+1) H)).
    apply RingTermFOQuote.
    exact t.
  - apply (FOForall n).
    destruct i as [i lti].
    assert (i.+1 < length (n :: foctx)) as H;[auto|].
    apply (IHs (Ordinal (m := i.+1) H)).
    apply RingTermFOQuote.
    exact t.
Defined.

Definition FirstOrderFormulaSOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_(length soctx)),
  (('I_(length (snd (tnth (in_tuple soctx) i))) -> 
   @RingTerm (drop_index i soctx) foctx) -> 
   @RingTerm (drop_index i soctx) foctx) ->
  @FirstOrderFormula soctx foctx ->
  @FirstOrderFormula (drop_index i soctx) foctx.
  intros i f s.
  induction s.
  - exact FOTrue.
  - exact FOFalse.
  - exact (FONot (IHs f)).
  - exact (FOAnd (IHs1 f) (IHs2 f)).
  - exact (FOOr (IHs1 f) (IHs2 f)).
  - exact (FOImp (IHs1 f) (IHs2 f)).
  - exact (FOEq (RingTermSOSubst i f r) (RingTermSOSubst i f r0)).
  - apply (FOExists n).
    apply IHs.
    intro t.
    assert (0 < length (n :: foctx)) as H;[auto|].
    apply (fun x => RingTermFOQuote (n := n) (f x)).
    exact (fun x => (RingTermFOSubst (Ordinal H) RingZero (t x))).
  - apply (FOForall n).
    apply IHs.
    intro t.
    assert (0 < length (n :: foctx)) as H;[auto|].
    apply (fun x => RingTermFOQuote (n := n) (f x)).
    exact (fun x => (RingTermFOSubst (Ordinal H) RingZero (t x))).
Defined.

Inductive Sigma11 {soctx : SOctx} : Type :=
| S11Exists : forall (y : nat) (bs : seq nat), 
              @Sigma11 ((y, bs) :: soctx) ->
              Sigma11
| FO : @FirstOrderFormula soctx nil -> 
       Sigma11.

Definition SecondOrderFormulaSOSubst {soctx : SOctx} :
  forall (i : 'I_(length soctx)),
  (('I_(length (snd (tnth (in_tuple soctx) i))) -> 
   @RingTerm (drop_index i soctx) nil) -> 
   @RingTerm (drop_index i soctx) nil) ->
  @Sigma11 soctx ->
  @Sigma11 (drop_index i soctx).
  move=> i f X;move: i f.
  induction X; move=>[i lti] f2.
  - apply (S11Exists y bs).
    assert (i.+1 < length ((y, bs) :: soctx)) as H;[auto|].
    apply (IHX (Ordinal (m := i.+1) H)).
    move=> t.
    apply RingTermSOQuote.
    apply: f2.
    move=> jo.
    replace (tnth (in_tuple ((y, bs) :: soctx))
             (Ordinal (n:=length ((y, bs) :: soctx)) (m:=i.+1) H))
       with (tnth (in_tuple soctx)
             (Ordinal (n:=length soctx) (m:=i) lti)) in t;
    [|by do 2 rewrite (tnth_nth (0, nil))].
    apply t in jo; clear t.
    assert (forall ctx, 0 < length ((y, bs) :: ctx)) as H0;[fcrush|].
    apply (RingTermSOSubst (Ordinal (H0 _)) (fun _ => RingZero)).
    exact jo.
  - exact (FO (FirstOrderFormulaSOSubst _ f2 f)).
Defined.

Example sigma11_1 : @Sigma11 nil.
  apply (S11Exists 5 [::2;3;4]).
  apply (S11Exists 3 [::1;2]).
  apply FO.
  apply (FOExists 7).
  apply (FOForall 6).
  apply (FOExists 5).
  apply FOOr.
  apply FOAnd.
  apply FOEq.
  apply RingPlusOne.
  apply (RingVar (foctx := [::_;_;_]) (inord 0)).
  apply FOEq.
  apply (RingFun (soctx := [::_;_]) (inord 0)).
  intros [i lt].
  destruct i;[apply RingPlusOne|].
  destruct i;[apply RingMinusOne|].
  unfold in_tuple, tnth, tval in lt.
  rewrite inordK in lt;[|auto]; cbn in lt; inversion lt.
  apply (RingFun (soctx := [::_;_]) (inord 1)).
  intros [i lt].
  destruct i;[apply RingPlusOne|].
  destruct i;[apply RingMinusOne|].
  destruct i;[apply RingZero|].
  unfold in_tuple, tnth, tval in lt.
  rewrite inordK in lt;[|auto];cbn in lt;inversion lt.
  apply FOTrue.
Defined.

Example sigma11_2 : @Sigma11 nil :=
  S11Exists 5 [:: 2; 3; 4] (S11Exists 3 [:: 1; 2]
	(FO (FOExists 7 (FOForall 6 (FOExists 5 (
  (FOOr
    (FOAnd 
      (FOEq RingPlusOne (RingVar (foctx := [:: _; _; _]) (inord 0)))
      (FOEq
        (RingFun (soctx := [:: _; _]) (inord 0)
          (fun X  =>
            match X with
            | @Ordinal _ i _ =>
                match i with
                | 0 => RingPlusOne
                | _.+1 => RingMinusOne
                end
            end))
        (RingFun (soctx := [:: _; _]) (inord 1)
          (fun X =>
            match X with
            | @Ordinal _ i _ =>
                match i with
                | 0 => RingPlusOne
                | 1 => RingMinusOne
                | _.+2 => RingZero
                end
            end))
      )) FOTrue))))))).

End Sigma_1_1_Internal.





Section Sigma_1_1_Denotation.

Record Sigma11Model : Type :=
    mkSigma11Model {
        R : ringType;
        (*lt should be a strict, total order with a least element*)
        lt : relation R;
        so : StrictOrder lt;
        lt_total : forall x y, lt x y \/ x==y \/ lt y x;
        min : R;
        least_elem : forall x, lt min x
      }.

Fixpoint naturalRingElement {R : ringType} (n : nat) : R := 
  match n with
  | 0 => 0
  | x.+1 => naturalRingElement x + 1
  end.

(* Coercion naturalRingElement : nat >-> ringType. *)

Definition RingTerm_Denotation (M : Sigma11Model) (r : @RingTerm nil nil) : R M.
  elim r.
  - fcrush.
  - destruct i; fcrush.
  - exact (-1)%R.
  - exact 1%R.
  - exact 0%R.
  - move=> _ r1 _ r2; exact (r1 + r2)%R.
  - move=> _ r1 _ r2; exact (r1 * r2)%R.
Defined.

Fixpoint FirstOrder_Measure {soctx} {foctx} (f : @FirstOrderFormula soctx foctx) : nat :=
  match f with
  | FOTrue => 0
  | FOFalse => 0
  | FONot f => (FirstOrder_Measure f).+1
  | FOAnd f1 f2 => (FirstOrder_Measure f1 + FirstOrder_Measure f2).+1
  | FOOr f1 f2 => (FirstOrder_Measure f1 + FirstOrder_Measure f2).+1
  | FOImp f1 f2 => (FirstOrder_Measure f1 + FirstOrder_Measure f2).+1
  | FOEq r1 r2 => 0
  | FOExists n f => (FirstOrder_Measure f).+1
  | FOForall n f => (FirstOrder_Measure f).+1
  end.

Lemma fo_subst_measure {soctx} {foctx}
  (f : @FirstOrderFormula soctx foctx)
  (i : 'I_(length foctx))
  (r : @RingTerm soctx (@drop_index nat i foctx)) :
  (FirstOrder_Measure (FirstOrderFormulaFOSubst i r f) =
   FirstOrder_Measure f)%coq_nat.
Proof.
  induction f; try hauto q:on; destruct i;
  simpl FirstOrderFormulaFOSubst; simpl FirstOrder_Measure;
  by rewrite <- (IHf (Ordinal (n:=(length foctx).+1) (m:=m.+1) i) (RingTermFOQuote r)).
Qed.

Require Import Program.

Program Fixpoint FirstOrder_Denotation
  (M : Sigma11Model) (f : @FirstOrderFormula nil nil) 
  {measure (FirstOrder_Measure f)} : Prop :=
  match f with
  | FOTrue => true
  | FOFalse => false
  | FONot f => not (FirstOrder_Denotation M f)
  | FOAnd f1 f2 => (FirstOrder_Denotation M f1) /\ (FirstOrder_Denotation M f2)
  | FOOr f1 f2 => (FirstOrder_Denotation M f1) \/ (FirstOrder_Denotation M f2)
  | FOImp f1 f2 => (FirstOrder_Denotation M f1) -> (FirstOrder_Denotation M f2)
  | FOEq r1 r2 => RingTerm_Denotation M r1 = RingTerm_Denotation M r2
  | FOExists n f => 
    exists (r : @RingTerm nil nil), 
    lt M (RingTerm_Denotation M r) (naturalRingElement n) /\
    FirstOrder_Denotation M 
      (FirstOrderFormulaFOSubst (Ordinal (n:=length [::n]) (ltn0Sn _)) r f)
  | FOForall n f =>
    forall (r : @RingTerm nil nil), 
    lt M (RingTerm_Denotation M r) (naturalRingElement n) ->
    FirstOrder_Denotation M 
      (FirstOrderFormulaFOSubst (Ordinal (n:=length [::n]) (ltn0Sn _)) r f)
  end.
Next Obligation.
  hauto db:arith q:on.
Qed.
Next Obligation.
  hauto db:arith q:on.
Qed.
Next Obligation.
  hauto db:arith q:on.
Qed.
Next Obligation.
  hauto db:arith q:on.
Qed.
Next Obligation.
  hauto db:arith q:on.
Qed.
Next Obligation.
  hauto db:arith q:on.
Qed.
Next Obligation.
  rewrite (fo_subst_measure f (Ordinal (ltn0Sn 0))).
  hauto.
Qed.
Next Obligation.
  rewrite (fo_subst_measure f (Ordinal (ltn0Sn 0))).
  hauto.
Qed.

Fixpoint SecondOrder_Measure {soctx} (f : @Sigma11 soctx) : nat :=
  match f with
  | S11Exists y bs f => (SecondOrder_Measure f).+1
  | FO f => 0
  end.

Lemma so_subst_measure {soctx}
  (f : @Sigma11 soctx)
  (i : 'I_(length soctx))
  (rf : ('I_(length (snd (tnth (in_tuple soctx) i))) -> 
   @RingTerm (drop_index i soctx) nil) -> 
   @RingTerm (drop_index i soctx) nil) :
  (SecondOrder_Measure (SecondOrderFormulaSOSubst i rf f) =
   SecondOrder_Measure f)%coq_nat.
Proof.
  induction f;[|hauto q:on].
  destruct i.
  simpl SecondOrderFormulaSOSubst; simpl SecondOrder_Measure;
  remember (fun _ => RingTermSOQuote _) as rf';
  by rewrite <- (IHf (Ordinal (n:=(length soctx).+1) (m:=m.+1) i) rf').
Qed.

Program Fixpoint SecondOrder_Denotation
  (M : Sigma11Model) (f : @Sigma11 nil) 
  {measure (SecondOrder_Measure f)} : Prop :=
  match f with
  | S11Exists y bs f => 
    exists (rf : ('I_(length bs) -> @RingTerm nil nil) -> @RingTerm nil nil),
    (forall (t : 'I_(length bs) -> @RingTerm nil nil),
     (forall x : 'I_(length bs), lt M (RingTerm_Denotation M (t x)) (naturalRingElement (tnth (in_tuple bs) x))) ->
     lt M (RingTerm_Denotation M (rf t)) (naturalRingElement y)) /\
    SecondOrder_Denotation M 
      (SecondOrderFormulaSOSubst (Ordinal (n:=length [::(y, bs)]) (ltn0Sn _)) rf f)
  | FO f => FirstOrder_Denotation M f
  end.
Next Obligation.
  rewrite (so_subst_measure f (Ordinal (ltn0Sn 0))).
  hauto.
Qed.

End Sigma_1_1_Denotation.