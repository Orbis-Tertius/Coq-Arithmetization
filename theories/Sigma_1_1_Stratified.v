From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssralg seq fintype tuple eqtype.

From Coq Require Import FunctionalExtensionality.
From Coq Require Import Relation_Definitions RelationClasses.

Require Import CoqArith.Utils.

Require Import Program.

Section Sigma_1_1_Internal.

Definition SOctx := seq nat.
Definition FOctx := nat.

Inductive RingTerm {soctx : SOctx} {foctx : FOctx} : Type :=
| RingVar : 'I_foctx -> RingTerm
| RingFun : forall (i : 'I_(length soctx)),
            ('I_(tnth (in_tuple soctx) i) -> RingTerm) ->
            RingTerm
| RingMinusOne : RingTerm
| RingPlusOne : RingTerm
| RingZero : RingTerm
| RingPlus : RingTerm -> RingTerm -> RingTerm
| RingTimes : RingTerm -> RingTerm -> RingTerm.

Definition RingTermFOQuote {soctx} {foctx} : 
  @RingTerm soctx foctx ->
  RingTerm (soctx := soctx) (foctx := foctx.+1).
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

Theorem RingTermFOQuote_Fun_Step {soctx} {foctx}
  (i : 'I_(length soctx))
  (t : 'I_(tnth (in_tuple soctx) i) -> RingTerm (foctx := foctx)) :
  RingTermFOQuote (RingFun i t) =
  RingFun i (fun x => RingTermFOQuote (t x)).
Proof. reflexivity. Qed.

Definition RingTermSOQuote {soctx} {foctx} {bs} : 
  @RingTerm soctx foctx ->
  RingTerm (soctx := bs :: soctx) (foctx := foctx).
  elim.
  - apply RingVar.
  - move=>[i lti] _ IH.
    assert (i.+1 < length (bs :: soctx));[auto|].
    apply (RingFun (Ordinal (m := i.+1) H)).
    move=>[j ltj].
    apply: IH.
    apply (Ordinal (m := j)).
    by do 2 rewrite (tnth_nth 0) in ltj *.
  - exact RingMinusOne.
  - exact RingPlusOne.
  - exact RingZero.
  - intros r1 IHr1 r2 IHr2.
    exact (RingPlus IHr1 IHr2).
  - intros r1 IHr1 r2 IHr2.
    exact (RingTimes IHr1 IHr2).
Defined.

Theorem RingTermSOQuote_Fun_Step {soctx} {foctx} {n}
  (i : nat) (lti : i < length soctx)
  (t : 'I_(tnth (in_tuple soctx) (Ordinal lti)) -> RingTerm (foctx := foctx)) :
  RingTermSOQuote (RingFun (Ordinal lti) t) = 
  RingFun (Ordinal (n:=length (n :: soctx)) (m:=i.+1) lti) 
          (fun x => RingTermSOQuote (t (eq_rect _ (fun x => 'I_x) x _ (tnth_tuple_index n lti)))).
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
  forall (i : 'I_foctx),
  @RingTerm soctx (foctx.-1) ->
  @RingTerm soctx foctx ->
  @RingTerm soctx (foctx.-1).
  move=> [i lti] t s.
  induction s.
  - destruct o as [o lto].
    destruct (Nat.compare i o) eqn:comp.
    + exact t.
    + rewrite <- Compare_dec.nat_compare_lt in comp.
      apply (introT (b := i < o) ltP) in comp.
      apply RingVar.
      apply (Ordinal (m:=o.-1)).
      sauto q: on.
    + rewrite <- Compare_dec.nat_compare_gt in comp.
      apply (introT (b := o < i) ltP) in comp.
      apply RingVar.
      apply (Ordinal (m:=o)).
      destruct i;[auto|].
      destruct foctx as [|[|foctx]];[auto|auto|].
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
  (i : 'I_foctx)
  (j : 'I_(length soctx))
  (r : @RingTerm soctx (foctx.-1))
  (t : 'I_(tnth (in_tuple soctx) j) -> RingTerm (foctx := foctx)) :
  RingTermFOSubst i r (RingFun j t) =
  RingFun j (fun x => RingTermFOSubst i r (t x)).
Proof. destruct i; reflexivity. Qed.

Theorem FOsubsts_unquote {soctx : SOctx} {foctx : FOctx} :
  forall (x : @RingTerm soctx foctx)
         (e : @RingTerm soctx foctx)
         (H : 0 < foctx.+1),
  RingTermFOSubst (Ordinal H) x (RingTermFOQuote e) = e.
Proof.
  move=> x; elim; try hauto q:on.
  - move=> [i lti] t rH triv.
    rewrite RingTermFOQuote_Fun_Step RingTermFOSubst_Fun_Step.
    f_equal.
    apply functional_extensionality; move=> [j ltj].
    by rewrite rH.
Qed.

Definition RingTermSOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_(length soctx)),
  (('I_(tnth (in_tuple soctx) i) -> 
   RingTerm (soctx := drop_index i soctx) (foctx := foctx)) -> 
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
      assert (j.-1 < length (drop_index i soctx)) as H.
      { rewrite drop_index_length; auto.
        destruct j; auto; clear tH; destruct (length soctx); [auto|sauto q:on lazy:on]. }
      apply (RingFun (Ordinal (m := j.-1) H)).
      move=> [o lto].
      apply: tH.
      apply (Ordinal (m:=o)).
      do 2 rewrite (tnth_nth 0) in lto *.
      simpl; simpl in lto.
      by rewrite drop_index_nth_high in lto.
    + clear f.
      rewrite <- Compare_dec.nat_compare_gt in comp.
      apply (introT (b := j < i) ltP) in comp.
      move=> _ tH.
      assert (j < length (drop_index i soctx)) as H.
      { hauto use: drop_index_length, pred_Sn, ltn_predRL, leq_ltn_trans. }
      apply (RingFun (Ordinal (m := j) H)).
      move=>[o lto]; apply: tH.
      do 2 rewrite (tnth_nth 0) in lto *.
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
  (f : ('I_(tnth (in_tuple soctx) (Ordinal lti)) -> 
        RingTerm (soctx := drop_index i soctx) (foctx := foctx)) -> 
        RingTerm (soctx := drop_index i soctx) (foctx := foctx))
  (j : nat) (ltj : j < length soctx)
  (t : 'I_(tnth (in_tuple soctx) (Ordinal ltj)) -> 
        RingTerm  (soctx := soctx) (foctx := foctx))
  (ltij : i < j) :
  RingTermSOSubst (Ordinal lti) f (RingFun (Ordinal ltj) t) =
  RingFun (Ordinal (n:=length (drop_index (Ordinal lti) soctx)) (m:=j.-1) (index_low_decr ltij ltj))
          (fun x => RingTermSOSubst (Ordinal lti) f
                      (t (eq_rect _ (fun x => 'I_x) x _ 
                         (decr_index_const ltj (index_low_decr ltij ltj) ltij)))).
Proof.
  assert (PeanoNat.Nat.compare i j = Lt) as comp_lt;[exact 
    (iffLR (Compare_dec.nat_compare_lt i j) (elimT (b := i < j) ltP ltij))|].
  unfold RingTermSOSubst at 1; unfold RingTerm_rect; rewrite (Lt_Compare_match_fun _ comp_lt);
  rewrite (eq_irrelevance (eq_ind_r (fun pv : nat => j.-1 < pv) _ _) (index_low_decr ltij ltj)).
  f_equal.
  apply functional_extensionality;move=>[x ltx].
  unfold RingTermSOSubst, RingTerm_rect; do 2 f_equal.
  remember (eq_ind_r (fun pv : nat => x < pv -> x < _) _ _ _) as ltx2 eqn:dx; clear dx.
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
  (f : ('I_(tnth (in_tuple soctx) (Ordinal lti)) -> 
        RingTerm (soctx := drop_index i soctx) (foctx := foctx)) -> 
        RingTerm (soctx := drop_index i soctx) (foctx := foctx))
  (j : nat) (ltj : j < length soctx)
  (t : 'I_(tnth (in_tuple soctx) (Ordinal ltj)) -> 
        RingTerm  (soctx := soctx) (foctx := foctx))
  (ltij : j < i) :
  RingTermSOSubst (Ordinal lti) f (RingFun (Ordinal ltj) t) =
  RingFun (Ordinal (low_index_bound ltj ltij))
          (fun x => RingTermSOSubst (Ordinal lti) f 
                      (t (eq_rect _ (fun x => 'I_x) x _ 
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
  rewrite (rew_map (fun x => x -> _) (fun v => x < v)).
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
  (f : ('I_(tnth (in_tuple soctx) (Ordinal lti)) -> 
        RingTerm (soctx := drop_index i soctx) (foctx := foctx)) -> 
        RingTerm (soctx := drop_index i soctx) (foctx := foctx))
  (t : 'I_(tnth (in_tuple soctx) (Ordinal lti)) -> 
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
  forall n
         (e : @RingTerm soctx foctx)
         (H : 0 < length (n :: soctx)) f,
  RingTermSOSubst (Ordinal H) f (RingTermSOQuote (bs := n) e) = e.
Proof.
  move=> n; elim.
  - hauto.
  - move=> [i lti] t IHe H f.
    rewrite RingTermSOQuote_Fun_Step.
    rewrite RingTermSOSubst_Fun_Step_Lt.
    change (drop_index _ (_ :: soctx)) with soctx.
    assert (Ordinal (n:=length soctx) (m:=i) lti =
            Ordinal (n:=length soctx) (m:=i.+1.-1)
                    (@index_low_decr 0 i.+1 _ (n :: soctx) H lti)) as H0;[apply ord_inj;hauto|].
    transitivity 
      (RingFun (Ordinal (n:=length soctx) (m:=i.+1.-1) (@index_low_decr 0 i.+1 _ (n :: soctx) H lti)) 
      (eq_rect _ (fun x => 'I_(tnth _ x) -> _) t _ H0));[|destruct H0;reflexivity].
    f_equal.
    apply functional_extensionality.
    move=>[x ltx].
    rewrite IHe; clear IHe.
    rewrite eq_rect_f_ap.
    f_equal.
    apply ord_inj.
    rewrite (rew_map (fun x => 'I_x) (tnth (in_tuple soctx))).
    do 3 rewrite <- (map_subst (P := (fun x => 'I_x)) (fun _ p => nat_of_ord p)).
    by do 3 rewrite rew_const.
  - hauto.
  - hauto.
  - hauto.
  - move=> r1 IHr1 r2 IHr2 h f.
    by rewrite <- IHr1 at 2; rewrite <- IHr2 at 2.
  - move=> r1 IHr1 r2 IHr2 h f.
    by rewrite <- IHr1 at 2; rewrite <- IHr2 at 2.
Qed.

Inductive ZerothOrderFormula {soctx : SOctx} {foctx : FOctx} : Type :=
| ZOTrue : ZerothOrderFormula
| ZOFalse : ZerothOrderFormula
| ZONot : ZerothOrderFormula -> ZerothOrderFormula
| ZOAnd : ZerothOrderFormula ->
          ZerothOrderFormula ->
          ZerothOrderFormula
| ZOOr : ZerothOrderFormula ->
         ZerothOrderFormula ->
         ZerothOrderFormula
| ZOImp : ZerothOrderFormula ->
          ZerothOrderFormula ->
          ZerothOrderFormula
| ZOEq : @RingTerm soctx foctx -> 
         @RingTerm soctx foctx ->
         ZerothOrderFormula.

Definition ZerothOrderFormulaFOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_foctx),
  @RingTerm soctx foctx.-1 ->
  @ZerothOrderFormula soctx foctx ->
  @ZerothOrderFormula soctx foctx.-1.
  intros i t s.
  induction s.
  - exact ZOTrue.
  - exact ZOFalse.
  - exact (ZONot IHs).
  - exact (ZOAnd IHs1 IHs2).
  - exact (ZOOr IHs1 IHs2).
  - exact (ZOImp IHs1 IHs2).
  - exact (ZOEq (RingTermFOSubst i t r) (RingTermFOSubst i t r0)).
Defined.

Definition ZerothOrderFormulaSOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_(length soctx)),
  (('I_(tnth (in_tuple soctx) i) -> 
   @RingTerm (drop_index i soctx) foctx) -> 
   @RingTerm (drop_index i soctx) foctx) ->
  @ZerothOrderFormula soctx foctx ->
  @ZerothOrderFormula (drop_index i soctx) foctx.
  intros i f s.
  induction s.
  - exact ZOTrue.
  - exact ZOFalse.
  - exact (ZONot IHs).
  - exact (ZOAnd IHs1 IHs2).
  - exact (ZOOr IHs1 IHs2).
  - exact (ZOImp IHs1 IHs2).
  - exact (ZOEq (RingTermSOSubst i f r) (RingTermSOSubst i f r0)).
Defined.

Inductive FirstOrderFormula {soctx : SOctx} {foctx : FOctx} : Type :=
| ZO : @ZerothOrderFormula soctx foctx -> FirstOrderFormula
| FOExists : nat -> FirstOrderFormula (foctx := foctx.+1) -> FirstOrderFormula
| FOForall : nat -> FirstOrderFormula (foctx := foctx.+1) -> FirstOrderFormula. 

Definition FirstOrderFormulaFOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_foctx),
  @RingTerm soctx foctx.-1 ->
  @FirstOrderFormula soctx foctx ->
  @FirstOrderFormula soctx foctx.-1.
  intros i t s.
  induction s.
  - exact (ZO (ZerothOrderFormulaFOSubst i t z)).
  - apply (FOExists n).
    destruct i as [i lti].
    assert (i.+1 < foctx.+1) as H;[auto|].
    destruct foctx;[fcrush|].
    apply (IHs (Ordinal (m := i.+1) H)).
    apply RingTermFOQuote.
    exact t.
  - apply (FOForall n).
    destruct i as [i lti].
    assert (i.+1 < foctx.+1) as H;[auto|].
    destruct foctx;[fcrush|].
    apply (IHs (Ordinal (m := i.+1) H)).
    apply RingTermFOQuote.
    exact t.
Defined.

Definition FirstOrderFormulaSOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_(length soctx)),
  (('I_(tnth (in_tuple soctx) i) -> 
   @RingTerm (drop_index i soctx) foctx) -> 
   @RingTerm (drop_index i soctx) foctx) ->
  @FirstOrderFormula soctx foctx ->
  @FirstOrderFormula (drop_index i soctx) foctx.
  intros i f s.
  induction s.
  - exact (ZO (ZerothOrderFormulaSOSubst i f z)).
  - apply (FOExists n).
    apply IHs.
    intro t.
    assert (0 < foctx.+1) as H;[auto|].
    apply (fun x => RingTermFOQuote (f x)).
    exact (fun x => (RingTermFOSubst (Ordinal H) RingZero (t x))).
  - apply (FOForall n).
    apply IHs.
    intro t.
    assert (0 < foctx.+1) as H;[auto|].
    apply (fun x => RingTermFOQuote (f x)).
    exact (fun x => (RingTermFOSubst (Ordinal H) RingZero (t x))).
Defined.

Inductive SecondOrderFormula {soctx : SOctx} {foctx : FOctx} : Type :=
| FO : @FirstOrderFormula soctx foctx -> 
       SecondOrderFormula
| SOExists : forall (y : nat) (bs : seq nat), 
              SecondOrderFormula (soctx := length bs :: soctx) ->
              SecondOrderFormula.

Definition SecondOrderFormulaFOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_foctx),
  @RingTerm soctx foctx.-1 ->
  @SecondOrderFormula soctx foctx ->
  @SecondOrderFormula soctx foctx.-1.
  intros i t s.
  induction s.
  - exact (FO (FirstOrderFormulaFOSubst i t f)).
  - apply (SOExists y bs).
    apply (IHs i).
    exact (RingTermSOQuote (bs := length bs) t).
Defined.

Definition SecondOrderFormulaSOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_(length soctx)),
  (('I_(tnth (in_tuple soctx) i) -> 
   @RingTerm (drop_index i soctx) foctx) -> 
   @RingTerm (drop_index i soctx) foctx) ->
  @SecondOrderFormula soctx foctx ->
  @SecondOrderFormula (drop_index i soctx) foctx.
  move=> i f X;move: i f.
  induction X; move=>[i lti] f2.
  - exact (FO (FirstOrderFormulaSOSubst _ f2 f)).
  - apply (SOExists y bs).
    assert (i.+1 < length (length bs :: soctx)) as H;[auto|].
    apply (IHX (Ordinal (m := i.+1) H)).
    move=> t.
    apply RingTermSOQuote.
    apply: f2.
    move=> jo.
    replace (tnth (in_tuple (length bs :: soctx))
             (Ordinal (n:=length (length bs :: soctx)) (m:=i.+1) H))
       with (tnth (in_tuple soctx)
             (Ordinal (n:=length soctx) (m:=i) lti)) in t;
    [|by do 2 rewrite (tnth_nth 0)].
    apply t in jo; clear t.
    assert (forall ctx, 0 < length (length bs :: ctx)) as H0;[fcrush|].
    apply (RingTermSOSubst (Ordinal (H0 _)) (fun _ => RingZero)).
    exact jo.
Defined.

Example sigma11_1 : @SecondOrderFormula nil 0.
  apply (SOExists 5 [::2;3;4]).
  apply (SOExists 3 [::1;2]).
  apply FO.
  apply (FOExists 7).
  apply (FOForall 6).
  apply (FOExists 5).
  apply ZO.
  apply ZOOr.
  apply ZOAnd.
  apply ZOEq.
  apply RingPlusOne.
  apply (RingVar (inord 0)).
  apply ZOEq.
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
  apply ZOTrue.
Defined.

Example sigma11_2 : @SecondOrderFormula nil 0 :=
  SOExists 5 [:: 2; 3; 4] (SOExists 3 [:: 1; 2]
	(FO (FOExists 7 (FOForall 6 (FOExists 5 (ZO
  (ZOOr
    (ZOAnd 
      (ZOEq RingPlusOne (RingVar (inord 0)))
      (ZOEq
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
      )) ZOTrue))))))).

End Sigma_1_1_Internal.





Section Sigma_1_1_Denotation.

Record SecondOrderFormulaModel : Type :=
    mkSecondOrderFormulaModel {
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

Definition RingTerm_Denotation (M : SecondOrderFormulaModel) (r : @RingTerm nil 0) : R M.
  elim r.
  - fcrush.
  - destruct i; fcrush.
  - exact (-1)%R.
  - exact 1%R.
  - exact 0%R.
  - move=> _ r1 _ r2; exact (r1 + r2)%R.
  - move=> _ r1 _ r2; exact (r1 * r2)%R.
Defined.

Fixpoint ZerothOrder_Denotation
  (M : SecondOrderFormulaModel) (f : @ZerothOrderFormula nil 0) : Prop :=
  match f with
  | ZOTrue => true
  | ZOFalse => false
  | ZONot f => not (ZerothOrder_Denotation M f)
  | ZOAnd f1 f2 => (ZerothOrder_Denotation M f1) /\ (ZerothOrder_Denotation M f2)
  | ZOOr f1 f2 => (ZerothOrder_Denotation M f1) \/ (ZerothOrder_Denotation M f2)
  | ZOImp f1 f2 => (ZerothOrder_Denotation M f1) -> (ZerothOrder_Denotation M f2)
  | ZOEq r1 r2 => RingTerm_Denotation M r1 = RingTerm_Denotation M r2
  end.

Fixpoint FirstOrder_Measure {soctx} {foctx} (f : @FirstOrderFormula soctx foctx) : nat :=
  match f with
  | ZO _ => 0
  | FOExists n f => (FirstOrder_Measure f).+1
  | FOForall n f => (FirstOrder_Measure f).+1
  end.

Lemma fo_subst_measure {soctx} {foctx}
  (f : @FirstOrderFormula soctx foctx)
  (i : 'I_foctx)
  (r : @RingTerm soctx (foctx.-1)) :
  (FirstOrder_Measure (FirstOrderFormulaFOSubst i r f) =
   FirstOrder_Measure f)%coq_nat.
Proof.
  induction f; try hauto q:on; destruct i;
  simpl FirstOrderFormulaFOSubst; simpl FirstOrder_Measure;
  by rewrite <- (IHf (Ordinal (n:=(length foctx).+1) (m:=m.+1) i) (RingTermFOQuote r)).
Qed.

Program Fixpoint FirstOrder_Denotation
  (M : SecondOrderFormulaModel) (f : @FirstOrderFormula nil 0) 
  {measure (FirstOrder_Measure f)} : Prop :=
  match f with
  | ZO z => ZerothOrder_Denotation M z
  | FOExists n f => 
    exists (r : @RingTerm nil 0), 
    lt M (RingTerm_Denotation M r) (naturalRingElement n) /\
    FirstOrder_Denotation M 
      (FirstOrderFormulaFOSubst (Ordinal (n:=length [::n]) (ltn0Sn _)) r f)
  | FOForall n f =>
    forall (r : @RingTerm nil 0), 
    lt M (RingTerm_Denotation M r) (naturalRingElement n) ->
    FirstOrder_Denotation M 
      (FirstOrderFormulaFOSubst (Ordinal (n:=length [::n]) (ltn0Sn _)) r f)
  end.
Next Obligation.
  rewrite (fo_subst_measure f (Ordinal (ltn0Sn 0))).
  hauto.
Qed.
Next Obligation.
  rewrite (fo_subst_measure f (Ordinal (ltn0Sn 0))).
  hauto.
Qed.

Fixpoint SecondOrder_Measure {soctx} {foctx} 
  (f : @SecondOrderFormula soctx foctx) : nat :=
  match f with
  | SOExists y bs f => (SecondOrder_Measure f).+1
  | FO f => 0
  end.

Lemma so_subst_measure {soctx} {foctx} 
  (f : @SecondOrderFormula soctx foctx)
  (i : 'I_(length soctx))
  (rf : ('I_(tnth (in_tuple soctx) i) -> 
   @RingTerm (drop_index i soctx) foctx) -> 
   @RingTerm (drop_index i soctx) foctx) :
  (SecondOrder_Measure (SecondOrderFormulaSOSubst i rf f) =
   SecondOrder_Measure f)%coq_nat.
Proof.
  induction f;[hauto q:on|].
  destruct i.
  simpl SecondOrderFormulaSOSubst; simpl SecondOrder_Measure;
  remember (fun _ => RingTermSOQuote _) as rf';
  by rewrite <- (IHf (Ordinal (n:=(length soctx).+1) (m:=m.+1) i) rf').
Qed.

Program Fixpoint SecondOrder_Denotation
  (M : SecondOrderFormulaModel) (f : @SecondOrderFormula nil 0) 
  {measure (SecondOrder_Measure f)} : Prop :=
  match f with
  | FO f => FirstOrder_Denotation M f
  | SOExists y bs f => 
    exists (rf : ('I_(length bs) -> @RingTerm nil 0) -> @RingTerm nil 0),
    (forall (t : 'I_(length bs) -> @RingTerm nil 0),
     (forall x : 'I_(length bs), lt M (RingTerm_Denotation M (t x)) (naturalRingElement (tnth (in_tuple bs) x))) ->
     lt M (RingTerm_Denotation M (rf t)) (naturalRingElement y)) /\
    SecondOrder_Denotation M 
      (SecondOrderFormulaSOSubst (Ordinal (n:=length [::(y, bs)]) (ltn0Sn _)) rf f)
  end.
Next Obligation.
  rewrite (so_subst_measure f (Ordinal (ltn0Sn 0))).
  hauto.
Qed.

Theorem map_length {A B} (f : A -> B) (s : seq A) : length [seq f i | i <- s] = length s.
Proof. move: s; elim; hauto q:on. Qed.

Theorem Ordinal_Rect n n2 m (i : m < n) (e : n = n2) :
  (eq_rect _ _ (Ordinal (n:=n) (m:=m) i) _ e) = Ordinal (eq_rect _ (fun x => m < x) i _ e).
Proof. by destruct e. Qed.

Theorem map_nth {A B} (f : A -> B) (s : seq A) (o : 'I_(length [seq f i | i <- s])) :
  tnth (in_tuple [seq f i | i <- s]) o = 
  f (tnth (in_tuple s) (eq_rect _ _ o _ (map_length _ _))).
Proof.
  move: s o; elim;[move=> [x xlt]; fcrush|].
  simpl.
  move=> a l IH o.
  destruct o.
  rewrite Ordinal_Rect.
  rewrite (tnth_nth (f a)).
  rewrite (tnth_nth a).
  destruct m;[reflexivity|].
  simpl.
  assert (m < length [seq f i | i <- l]) as H;[hauto|].
  transitivity (tnth (in_tuple [seq f i0 | i0 <- l]) (Ordinal H));[
  by rewrite (tnth_nth (f a))|].
  rewrite IH.
  rewrite Ordinal_Rect.
  by rewrite (tnth_nth a).
Qed.

Theorem map_nth_2 {A B} (f : A -> B) (s : seq A) (o : 'I_(length s)) :
  f (tnth (in_tuple s) o) 
  = tnth (in_tuple [seq f i | i <- s]) (eq_rect _ _ o _ (esym (map_length f _))).
Proof.
  move: s o; elim;[move=> [x xlt]; fcrush|].
  simpl.
  move=> a l IH o.
  destruct o.
  rewrite Ordinal_Rect.
  rewrite (tnth_nth (f a)).
  rewrite (tnth_nth a).
  destruct m;[reflexivity|].
  simpl.
  assert (m < length l) as H;[hauto|].
  transitivity (f (tnth (in_tuple l) (Ordinal H)));[
  by rewrite (tnth_nth a)|].
  rewrite IH.
  rewrite Ordinal_Rect.
  by rewrite (tnth_nth (f a)).
Qed.

Lemma map_nth_3_lem 
  {A T} {a b} (P Q : A -> Type) (tt : forall a, P a -> Q a -> T)
  (e : a = b) (pa : P a) (qb : Q b) :
  tt _ (eq_rect _ _ pa _ e) qb =
  tt _ pa (eq_rect _ _ qb _ (esym e)).
Proof. by destruct e. Qed.

Theorem map_nth_3 {A B} (f : A -> B) (s : seq A) (o : 'I_(length s)) :
  f (tnth (in_tuple s) o) 
  = tnth (eq_rect _ (fun i => i.-tuple B) (in_tuple [seq f i | i <- s])
         _ 
         (map_length f _)) o.
Proof.
  rewrite map_nth_2.
  by rewrite (map_nth_3_lem _ _ (fun x => @tnth x B) _ _ _).
Qed.

(*Interpreting a ring term with free variables as a function from ring elems. and functions. *)
Definition Ring_Denote (M : SecondOrderFormulaModel)
  (v1 : seq (R M))
  (v2 : seq {n : nat & 
            {y : (R M) & 
            {bs : n.-tuple (R M) & 
            {f : ('I_n -> R M) -> R M | 
            (forall (t : 'I_n -> R M), (forall x : 'I_n, lt M (t x) (tnth bs x)) -> lt M (f t) y)
            }}}})
  (s : @RingTerm [seq projT1 i | i <- v2] (length v1)) :
  R M.
  move:s; elim.
  - move=> idx; exact (tnth (in_tuple v1) idx).
  - move=> idx _ IH.
    rewrite map_nth in IH.
    destruct (tnth _ _) as [n[y[bs[f p]]]].
    exact (f IH).
  - exact (-1)%R.
  - exact 1%R.
  - exact 0%R.
  - move=> _ r1 _ r2; exact (r1 + r2)%R.
  - move=> _ r1 _ r2; exact (r1 * r2)%R.
Defined.

Fixpoint ZerothOrder_Denote (M : SecondOrderFormulaModel) 
  (v1 : seq (R M))
  (v2 : seq {n : nat & 
            {y : (R M) & 
            {bs : n.-tuple (R M) & 
            {f : ('I_n -> R M) -> R M | 
            (forall (t : 'I_n -> R M), (forall x : 'I_n, lt M (t x) (tnth bs x)) -> lt M (f t) y)
            }}}})
  (f : @ZerothOrderFormula [seq projT1 i | i <- v2] (length v1)) : Prop :=
  match f with
  | ZOTrue => true
  | ZOFalse => false
  | ZONot f => not (ZerothOrder_Denote M v1 v2 f)
  | ZOAnd f1 f2 => (ZerothOrder_Denote M v1 v2 f1) /\ (ZerothOrder_Denote M v1 v2 f2)
  | ZOOr f1 f2 => (ZerothOrder_Denote M v1 v2 f1) \/ (ZerothOrder_Denote M v1 v2 f2)
  | ZOImp f1 f2 => (ZerothOrder_Denote M v1 v2 f1) -> (ZerothOrder_Denote M v1 v2 f2)
  | ZOEq r1 r2 => Ring_Denote M v1 v2 r1 = Ring_Denote M v1 v2 r2
  end.

Fixpoint FirstOrder_Denote (M : SecondOrderFormulaModel) 
  (v1 : seq (R M))
  (v2 : seq {n : nat & 
            {y : (R M) & 
            {bs : n.-tuple (R M) & 
            {f : ('I_n -> R M) -> R M | 
            (forall (t : 'I_n -> R M), (forall x : 'I_n, lt M (t x) (tnth bs x)) -> lt M (f t) y)
            }}}})
  (f : @FirstOrderFormula [seq projT1 i | i <- v2] (length v1)) : Prop :=
  match f with
  | ZO z => ZerothOrder_Denote M v1 v2 z
  | FOExists n f => 
    exists (r : R M), 
      lt M r (naturalRingElement n) /\
      FirstOrder_Denote M (r :: v1) v2 f
  | FOForall n f =>
    forall (r : R M), 
      lt M r (naturalRingElement n) ->
      FirstOrder_Denote M (r :: v1) v2 f
  end.

(*Interpreting a ring term with free variables as a function from ring elems. and functions. *)
Program Fixpoint SecondOrder_Denote (M : SecondOrderFormulaModel) 
  (v1 : seq (R M))
  (v2 : seq {n : nat & 
            {y : (R M) & 
            {bs : n.-tuple (R M) & 
            {f : ('I_n -> R M) -> R M | 
            (forall (t : 'I_n -> R M), (forall x : 'I_n, lt M (t x) (tnth bs x)) -> lt M (f t) y)
            }}}})
  (f : @SecondOrderFormula [seq projT1 i | i <- v2] (length v1)) : Prop :=
  match f with
  | FO f => FirstOrder_Denote M v1 v2 f
  | SOExists y bs f => 
    exists (rf : ('I_(length bs) -> R M) -> R M)
    (p : forall (t : 'I_(length bs) -> R M),
          (forall x : 'I_(length bs), 
            lt M (t x) (naturalRingElement (tnth (in_tuple bs) x))) ->
            lt M (rf t) (naturalRingElement y)),
    SecondOrder_Denote M v1 
      (existT _ (length bs) 
      (existT _ (naturalRingElement y) 
      (existT _ (in_tuple (map naturalRingElement bs))
      (exist _ rf p))) :: v2) f
  end.
Next Obligation.
  by rewrite <- (map_length (@naturalRingElement (R M))).
Qed.
Next Obligation.
  rewrite map_nth_3.
  do 2 f_equal.
  apply proof_irrelevance.
Qed.

(*
Note: This is impossible. Consider if one of the bs bounds is 0; then it's impossible
      for any applied argument to type check. Bounds should be part of the proposition,
      not enforced on the type level.

Definition Sigma11_Pred (M : SecondOrderFormulaModel)
  (v1 : seq (R M))
  (v2 : seq {n : nat & 
            {y : (R M) & 
            {bs : n.-tuple (R M) & 
            ((forall o : 'I_n, {r : (R M) | lt M r (tnth bs o)}) -> {r : R M | lt M r y})}}})
  (s : @RingTerm [seq projT1 i | i <- v2] (length v1)) :
  R M := ...
*)

End Sigma_1_1_Denotation.
