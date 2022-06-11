From Hammer Require Import Tactics Reflect Hints.
From Hammer Require Import Hammer.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssrint seq choice.
From mathcomp Require Import fintype div intdiv tuple bigop prime finset fingroup.
From mathcomp Require Import ssralg poly polydiv morphism action finalg zmodp.
From mathcomp Require Import cyclic center pgroup abelian matrix mxpoly vector.
From mathcomp Require Import falgebra fieldext separable galois.
From mathcomp Require ssrnum ssrint.

From Coq Require Import FunctionalExtensionality.

Definition drop_index {T} (m : nat) (s : seq T) : seq T := 
  take m s ++ behead (drop m s).

Theorem drop_index_length {T} : forall (s : seq T) (m : nat),
  m < length s -> length (drop_index m s) = length s - 1.
Proof.
  elim;[auto|].
  unfold drop_index.
  simpl; move=> a l IH [|m] mlt;[sauto|].
  simpl; rewrite IH; auto.
  destruct (length l);[fcrush|sauto q: on].
Qed.

Theorem drop_index_nth_low {T} : forall i j (s : seq T) d,
  j < i ->
  nth d (drop_index i s) j = nth d s j.
Proof.
  elim;[fcrush|].
  move=> i iH j [|x s] d jtl;sauto.
Qed.

Theorem drop_index_nth_high {T} : forall i j (s : seq T) d,
  i < j ->
  nth d (drop_index i s) (j - 1) = nth d s j.
Proof.
  elim;destruct j;try fcrush.
  move=> [|x s] d jg;[sauto use: nth_nil|].
  replace (j.+1 - 1) with j;[|sauto q:on].
  simpl.
  symmetry; rewrite <- H; [|auto].
  destruct j;[fcrush|].
  by replace (j.+1 - 1) with j;[|sauto q:on].
Qed.

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
  RingTerm (soctx := soctx) (foctx := foctx) ->
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

Definition RingTermSOQuote {soctx} {foctx} {n} {l} : 
  RingTerm (soctx := soctx) (foctx := foctx) ->
  RingTerm (soctx := (n, l) :: soctx) (foctx := foctx).
  elim.
  - apply RingVar.
  - move=>[i lti] X0 X.
    assert (i.+1 < length ((n, l) :: soctx));[auto|].
    apply (RingFun (Ordinal (m := i.+1) H)).
    move=>[j ltj].
    apply: X.
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

Definition RingTermFOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_(length foctx)),
  RingTerm (soctx := soctx) (foctx := drop_index i foctx) ->
  RingTerm (soctx := soctx) (foctx := foctx) ->
  RingTerm (soctx := soctx) (foctx := drop_index i foctx).
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

Theorem FOsubsts_unquote {soctx : SOctx} {foctx : FOctx} :
  forall n
         (x : RingTerm (soctx := soctx) (foctx := foctx))
         (e : RingTerm (soctx := soctx) (foctx := foctx))
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
    unfold RingTermFOQuote, RingTermFOSubst, RingTerm_rect.
    f_equal.
    apply functional_extensionality; move=> [j ltj].
    rewrite <- (rH (Ordinal ltj)) at 2.
    reflexivity.
Qed.

Definition RingTermSOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_(length soctx)),
  (('I_(length (snd (tnth (in_tuple soctx) i))) -> 
   RingTerm  (soctx := drop_index i soctx) (foctx := foctx)) -> 
   RingTerm (soctx := drop_index i soctx) (foctx := foctx)) ->
  RingTerm (soctx := soctx) (foctx := foctx) ->
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
| FOEq : RingTerm (soctx := soctx) (foctx := foctx) -> 
         RingTerm (soctx := soctx) (foctx := foctx) ->
         FirstOrderFormula
| FOExists : forall n, FirstOrderFormula (foctx := n :: foctx) ->
                       FirstOrderFormula
| FOForall : forall n, FirstOrderFormula (foctx := n :: foctx) ->
                       FirstOrderFormula.

Definition FirstOrderFormulaFOSubst {soctx : SOctx} {foctx : FOctx} :
  forall (i : 'I_(length foctx)),
  RingTerm (soctx := soctx) (foctx := drop_index i foctx) ->
  FirstOrderFormula (soctx := soctx) (foctx := foctx) ->
  FirstOrderFormula (soctx := soctx) (foctx := drop_index i foctx).
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
   RingTerm  (soctx := drop_index i soctx) (foctx := foctx)) -> 
   RingTerm (soctx := drop_index i soctx) (foctx := foctx)) ->
  FirstOrderFormula (soctx := soctx) (foctx := foctx) ->
  FirstOrderFormula (soctx := drop_index i soctx) (foctx := foctx).
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



Inductive Sigma11 : SOctx -> Type :=
| S11Exists : forall {ctx : SOctx} (y : nat) (bs : seq nat), 
            Sigma11 ((y, bs) :: ctx) ->
            Sigma11 ctx
| FO : forall {ctx : SOctx}, FirstOrderFormula (soctx := ctx) (foctx := nil) -> 
                             Sigma11 ctx.

Example sigma11_1 : Sigma11 nil.
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

Example sigma11_2 : Sigma11 nil :=
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

Record Sigma11Model {soctx : SOctx} {foctx : FOctx} : Type :=
    mkSigma11Model {
        R : ringType;
        (*lt : stricttotalordering R;*)

      }.


End Sigma_1_1_Internal.