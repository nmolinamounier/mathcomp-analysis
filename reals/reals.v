(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)
(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets sup_inf contra set_interval.

(**md**************************************************************************)
(* # An axiomatization of real numbers $\mathbb{R}$                           *)
(*                                                                            *)
(* This file provides a classical axiomatization of real numbers as a         *)
(* discrete real archimedean field with in particular a theory of floor and   *)
(* ceil.                                                                      *)
(*                                                                            *)
(* ```                                                                        *)
(*     realType == type of real numbers                                       *)
(*                 The HB class is Real.                                      *)
(*        sup A == where A : set R with R : realType, the supremum of A when  *)
(*                 it exists, 0 otherwise                                     *)
(*        inf A := - sup (- A)                                                *)
(* ```                                                                        *)
(*                                                                            *)
(* The mixin corresponding to realType extends an archiFieldType with two     *)
(* properties:                                                                *)
(* - when sup A exists, it is an upper bound of A (lemma sup_upper_bound)     *)
(* - when sup A exists, there exists an element x in A such that              *)
(*   sup A - eps < x for any 0 < eps (lemma sup_adherent)                     *)
(*                                                                            *)
(* ```                                                                        *)
(*         Rint == the set of real numbers that can be written as z%:~R,      *)
(*                 i.e., as an integer                                        *)
(*     Rtoint r == r when r is an integer, 0 otherwise                        *)
(*  floor_set x := [set y | Rtoint y /\ y <= x]                               *)
(*     Rfloor x == the floor of x as a real number                            *)
(*     range1 x := [set y |x <= y < x + 1]                                    *)
(*      Rceil x == the ceil of x as a real number, i.e., - Rfloor (- x)       *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*     @rational R == set of rational numbers of type R : realType            *)
(*   @irrational R == the complement of rational R                            *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Declare Scope real_scope.

(* -------------------------------------------------------------------- *)
Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

(* -------------------------------------------------------------------- *)
Delimit Scope real_scope with real.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section subr_image.
Variable R : numDomainType.
Implicit Types (E : set R) (x : R).

Lemma has_lbound0 : has_lbound (@set0 R). Proof. by exists 0. Qed.

Lemma has_ubound0 : has_ubound (@set0 R). Proof. by exists 0. Qed.

Lemma ubound0 : ubound (@set0 R) = setT.
Proof. by rewrite predeqE => r; split => // _. Qed.

Lemma lboundT : lbound [set: R] = set0.
Proof.
rewrite predeqE => r; split => // /(_ (r - 1) Logic.I).
by rewrite addrC -subr_ge0 addrK ler0N1.
Qed.

End subr_image.

Section has_bound_lemmas.
Variable R : realDomainType.
Implicit Types E : set R.
Implicit Types x : R.

Lemma has_ub_image_norm E : has_ubound (Num.norm @` E) -> has_ubound E.
Proof.
case => M /ubP uM; exists M; apply/ubP => r rS.
by apply: (le_trans (ler_norm _)); apply: uM; exists r.
Qed.

Lemma has_lb_image_norm E : has_ubound (Num.norm @` E) -> has_lbound E.
Proof.
case=> /= M /ubP uM; exists (- M); apply/lbP => r rS.
by apply: lerNnormlW; apply: uM; exists r.
Qed.

Lemma has_inf_supN E : has_sup (-%R @` E) <-> has_inf E.
Proof. by rewrite /has_sup /has_inf -has_lb_ubN nonemptyN. Qed.

Lemma has_sup_infN E : has_inf (-%R @` E) <-> has_sup E.
Proof. by rewrite -has_inf_supN setNK. Qed.

End has_bound_lemmas.

(* -------------------------------------------------------------------- *)

HB.mixin Record DedekindPOrder_BaseAddUMagma_ZeroSupInf T 
    & DedekindPOrder ring_display T & Algebra.BaseAddUMagma T := {
  sup_out : forall (A : set T), ~ has_sup A -> sup A = 0 ;
  inf_out : forall (A : set T), ~ has_inf A -> inf A = 0  
}.

#[short(type=realType)]
HB.structure Definition Real := {R of 
  DedekindPOrder ring_display R & DedekindPOrder_BaseAddUMagma_ZeroSupInf R &
  Num.ArchiRealClosedField R}.

Bind Scope ring_scope with Real.sort.

(* -------------------------------------------------------------------- *)

Section IsInt.
Context {R : realFieldType}.

Definition Rint_pred := fun x : R => `[< exists z, x == z%:~R >].
Arguments Rint_pred _ /.
Definition Rint := [qualify a x | Rint_pred x].

Lemma Rint_def x : (x \is a Rint) = (`[< exists z, x == z%:~R >]).
Proof. by []. Qed.

Lemma RintP x : reflect (exists z, x = z%:~R) (x \in Rint).
Proof.
by apply/(iffP idP) => [/asboolP[z /eqP]|[z]] ->; [|apply/asboolP]; exists z.
Qed.

Lemma RintC z : z%:~R \is a Rint.
Proof. by apply/RintP; exists z. Qed.

Lemma Rint0 : 0 \is a Rint.
Proof. by rewrite -[0](mulr0z 1) RintC. Qed.

Lemma Rint1 : 1 \is a Rint.
Proof. by rewrite -[1]mulr1z RintC. Qed.

Hint Resolve Rint0 Rint1 RintC : core.

Lemma Rint_subring_closed : subring_closed Rint.
Proof.
split=> // _ _ /RintP[x ->] /RintP[y ->]; apply/RintP.
by exists (x - y); rewrite rmorphB. by exists (x * y); rewrite rmorphM.
Qed.

HB.instance Definition _ := GRing.isSubringClosed.Build R Rint_pred
  Rint_subring_closed.

Lemma Rint_ler_addr1 (x y : R) : x \is a Rint -> y \is a Rint ->
  (x + 1 <= y) = (x < y).
Proof.
move=> /RintP[xi ->] /RintP[yi ->]; rewrite -{2}[1]mulr1z.
by rewrite -intrD !(ltr_int, ler_int) lezD1.
Qed.

Lemma Rint_ltr_addr1 (x y : R) : x \is a Rint -> y \is a Rint ->
  (x < y + 1) = (x <= y).
Proof.
move=> /RintP[xi ->] /RintP[yi ->]; rewrite -{3}[1]mulr1z.
by rewrite -intrD !(ltr_int, ler_int) ltzD1.
Qed.

End IsInt.
Arguments Rint_pred _ _ /.

(* -------------------------------------------------------------------- *)
Section ToInt.
Context {R : realType}.

Implicit Types x y : R.

Definition Rtoint (x : R) : int :=
  if insub x : {? x | x \is a Rint} is Some Px then
    xchoose (asboolP _ (tagged Px))
  else 0.

Lemma RtointK (x : R): x \is a Rint -> (Rtoint x)%:~R = x.
Proof.
move=> Ix; rewrite /Rtoint insubT /= [RHS](eqP (xchooseP (asboolP _ Ix))).
by congr _%:~R; apply/eq_xchoose.
Qed.

Lemma Rtointz (z : int): Rtoint z%:~R = z.
Proof. by apply/eqP; rewrite -(@eqr_int R) RtointK ?rpred_int. Qed.

Lemma Rtointn (n : nat): Rtoint n%:R = n%:~R.
Proof. by rewrite -{1}mulrz_nat Rtointz. Qed.

Lemma inj_Rtoint : {in Rint &, injective Rtoint}.
Proof. by move=> x y Ix Iy /= /(congr1 (@intmul R 1)); rewrite !RtointK. Qed.

Lemma RtointN x : x \is a Rint -> Rtoint (- x) = - Rtoint x.
Proof.
move=> Ir; apply/eqP.
by rewrite -(@eqr_int R) RtointK // ?rpredN // mulrNz RtointK.
Qed.

End ToInt.

(* -------------------------------------------------------------------- *)

Section RealDerivedOps.
Variable R : realType.

Implicit Types x y : R.
Definition floor_set x := [set y : R | (y \is a Rint) && (y <= x)].

Definition Rfloor x : R := (Num.floor x)%:~R.

Definition range1 (x : R) := [set y | x <= y < x + 1].

Definition Rceil x : R := (Num.ceil x)%:~R.

End RealDerivedOps.

(*-------------------------------------------------------------------- *)

Section real_sup_inf.
Context {R : realType}.
Import Dedekind.Order.

Lemma sup0 : sup set0 = 0 :> R.
Proof. by apply: sup_out => -[[]]. Qed.

Lemma inf0 : inf set0 = 0 :> R.
Proof. by apply: inf_out => -[[]]. Qed.

Lemma sup_adherent (A : set R) (eps : R) :
  0 < eps -> A !=set0 -> exists2 a, A a & sup A - eps < a.
Proof. by move=> eps0 Ane; apply: lt_sup_ex => //; rewrite gtrBl. Qed.

Lemma inf_adherent (A : set R) (eps : R) :
  0 < eps -> A !=set0 -> exists2 a, A a & a < inf A + eps.
Proof. by move=> eps0 Ane; apply: gt_inf_ex => //; rewrite ltrDl. Qed.

Lemma supEN (A : set R) :
  sup A = - inf (-%R @` A).
Proof.
case: (EM (has_sup A)) => [|/[dup] nsA /has_sup_infN niA]; last first.
  by rewrite sup_out// inf_out// oppr0.
move=> [Ane /[dup] ubA /has_ub_lbN lbNA].
apply/(canRL opprK)/esym/inf_eq; first by apply/ub_lbN/ub_le_sup.
apply/ub_lbN => ? [x /[swap] <-] /lb_ubN.
by rewrite setNK opprK; apply: ge_sup.
Qed.

Lemma infEN (A : set R) :
  inf A = - sup (-%R @` A).
Proof. by rewrite supEN opprK setNK. Qed.

End real_sup_inf.

Section sup_inf_sum.
Context {R : realType}.

Import Dedekind.Order.

Lemma has_sup_sumE (A B : set R) :
  has_sup A -> has_sup B -> has_sup (A `+ B).
Proof.
case=> [[x Ax] [MA ubMA]] [[y Ay] [MB ubMB]].
split; first by exists (x+y); exists x => //; exists y.
exists (MA + MB) => ? [x' ? [y' ? <-]].
by apply: lerD; [ apply: ubMA | apply: ubMB ].
Qed.

Lemma has_inf_sumE (A B : set R) :
  has_inf A -> has_inf B -> has_inf (A `+ B).
Proof.
case=> [[x Ax] [MA lbMA]] [[y Ay] [MB lbMB]].
split; first by exists (x+y); exists x => //; exists y.
exists (MA + MB) => ? [x' ? [y' ? <-]].
by apply: lerD; [ apply: lbMA | apply: lbMB ].
Qed.

Lemma sup_sumE (A B : set R) :
  has_sup A -> has_sup B -> sup (A `+ B) = sup A + sup B.
Proof.
move=> [Ane ubA] [Bne ubB].
apply: sup_eq.
  by move=> ? [x Ax [y By <-]]; apply: lerD; apply: ub_le_sup.
move=> M ubAB; rewrite -lerBrDr.
apply: ge_sup => // => x Ax.
rewrite lerBrDl -lerBrDr; apply: ge_sup => // y By.
by rewrite lerBrDl; apply: ubAB; exists x => //; exists y.
Qed.

Lemma inf_sumE (A B : set R) :
  has_inf A -> has_inf B -> inf (A `+ B) = inf A + inf B.
Proof.
move=> [Ane lbA] [Bne lbB].
apply: inf_eq.
  by move=> ? [x Ax [y By <-]]; apply: lerD; apply: lb_ge_inf.
move=> M lbAB; rewrite -lerBlDr.
apply: le_inf => // => x Ax.
rewrite lerBlDr -lerBlDl; apply: le_inf => // y By.
by rewrite lerBlDl; apply: lbAB; exists x => //; exists y.
Qed.

End sup_inf_sum.

(* -------------------------------------------------------------------- *)
Section FloorTheory.
Variable R : realType.
Implicit Types (x y : R) (i : int).

Import Dedekind.Order.

Lemma isint_Rfloor x : Rfloor x \is a Rint.
Proof. by rewrite inE; exists (Num.floor x). Qed.

Lemma RfloorE x : Rfloor x = (Num.floor x)%:~R.
Proof. by []. Qed.

Lemma sup_floor_set_Rfloor x : sup (floor_set x) = Rfloor x.
Proof.
apply: sup_eq.
  by move=> _ /andP[/RintP[y ->]]; rewrite RfloorE ler_int floor_ge_int.
move=> y; apply.
by rewrite /floor_set/= isint_Rfloor/= /Rfloor floor_le.
Qed.

Lemma sup_in_floor_set x : (floor_set x) (sup (floor_set x)).
Proof. 
by rewrite sup_floor_set_Rfloor /floor_set /= isint_Rfloor /= floor_le. 
Qed.

Lemma mem_rg1_floor x : (range1 (Num.floor x)%:~R) x.
Proof. by rewrite /range1 /mkset -intrD1 floor_le floorD1_gt. Qed.

Lemma mem_rg1_Rfloor x : (range1 (Rfloor x)) x.
Proof. exact: mem_rg1_floor. Qed.

Lemma Rfloor_le x : Rfloor x <= x.
Proof. by case/andP: (mem_rg1_Rfloor x). Qed.

Lemma lt_succ_Rfloor x : x < Rfloor x + 1.
Proof. by case/andP: (mem_rg1_Rfloor x). Qed.

Lemma range1z_inj x i1 i2 : (range1 i1%:~R) x -> (range1 i2%:~R) x -> i1 = i2.
Proof.
move=> /andP[i1x x_i1] /andP[i2x x_i2].
wlog suffices: i1 i2 i1x {x_i1 i2x} x_i2 / (i1 <= i2).
  by move=> ih; apply/eqP; rewrite eq_le !ih.
rewrite -(lerD2r 1) lezD1 -(@ltr_int R) intrD.
exact/(le_lt_trans i1x).
Qed.

Lemma range1rr x : (range1 x) x.
Proof. by rewrite /range1/mkset lexx /= ltrDl ltr01. Qed.

Lemma range1zP i x : Rfloor x = i%:~R <-> (range1 i%:~R) x.
Proof.
split=> [<-|h]; first exact/mem_rg1_Rfloor.
by congr intmul; apply/floor_def; rewrite intrD1.
Qed.

Lemma Rfloor_natz i : Rfloor i%:~R = i%:~R :> R.
Proof. exact/range1zP/range1rr. Qed.

Lemma Rfloor0 : Rfloor 0 = 0 :> R. Proof. by rewrite /Rfloor floor0. Qed.

Lemma Rfloor1 : Rfloor 1 = 1 :> R. Proof. by rewrite /Rfloor floor1. Qed.

Lemma le_Rfloor : {homo (@Rfloor R) : x y / x <= y}.
Proof. by move=> x y /Num.Theory.le_floor; rewrite ler_int. Qed.

Lemma Rfloor_ge_int x (i : int) : (i%:~R <= x)= (i%:~R <= Rfloor x).
Proof. by rewrite ler_int floor_ge_int. Qed.

Lemma Rfloor_lt_int x (i : int) : (x < i%:~R) = (Rfloor x < i%:~R).
Proof. by rewrite ltr_int -floor_lt_int. Qed.

Lemma Rfloor_le0 x : x <= 0 -> Rfloor x <= 0.
Proof. by move=> ?; rewrite -Rfloor0 le_Rfloor. Qed.

Lemma Rfloor_lt0 x : x < 0 -> Rfloor x < 0.
Proof. by move=> x0; rewrite (le_lt_trans _ x0) // Rfloor_le. Qed.

Lemma ltr_add_invr y x : y < x -> exists k, y + k.+1%:R^-1 < x.
Proof.
move=> yx; exists (Num.truncn (x - y)^-1).
by rewrite -ltrBrDl invf_plt 1?posrE 1?subr_gt0// truncnS_gt.
Qed.

End FloorTheory.

Section CeilTheory.
Variable R : realType.

Implicit Types x y : R.

Lemma isint_Rceil x : Rceil x \is a Rint.
Proof. by rewrite /Rceil RintC. Qed.

Lemma Rceil0 : Rceil 0 = 0 :> R.
Proof. by rewrite /Rceil ceil0. Qed.

Lemma Rceil_ge x : x <= Rceil x.
Proof. by rewrite Num.Theory.ceil_ge ?num_real. Qed.

Lemma le_Rceil : {homo (@Rceil R) : x y / x <= y}.
Proof. by move=> x y ?; rewrite /Rceil ler_int le_ceil. Qed.

Lemma Rceil_ge0 x : 0 <= x -> 0 <= Rceil x.
Proof. by move=> x0; rewrite /Rceil ler0z -(ceil0 R) le_ceil. Qed.

Lemma RceilE x : Rceil x = (Num.ceil x)%:~R.
Proof. by []. Qed.

End CeilTheory.

(* -------------------------------------------------------------------- *)
Section Sup.
Context {R : realType}.
Implicit Types A B : set R.

Import Dedekind.Order.

Lemma lt_sup_imfset {T : Type} (F : T -> R) l :
  has_sup [set y | exists x, y = F x] ->
  l < sup [set y | exists x, y = F x] ->
  exists2 x, l < F x & F x <= sup [set y | exists x, y = F x].
Proof.
move=> [+ ubI] => /lt_sup_ex /[apply] - [? [x -> lFx]].
by exists x => //; apply: ub_le_sup => //; exists x.
Qed.

Lemma lt_inf_imfset {T : Type} (F : T -> R) l :
  has_inf [set y | exists x, y = F x] ->
  inf [set y | exists x, y = F x] < l ->
  exists2 x, F x < l & inf [set y | exists x, y = F x] <= F x.
Proof.
move=> [+ lbI] => /gt_inf_ex /[apply] - [? [x -> Fxl]].
by exists x => //; apply: lb_ge_inf => //; exists x.
Qed.

(** This is a specialization of the lemma `ub_le_sup` exploiting the fact
    that `sup` is 0 when there is no supremum. *)
Lemma sup_ge0 A : (forall x, A x -> 0 <= x) -> 0 <= sup A.
Proof.
move=> A0; have [->|/set0P[a Aa]] := eqVneq A set0; first by rewrite sup0.
have [[_ Aub]|supA] := pselect (has_sup A); last by rewrite sup_out.
by rewrite (le_trans (A0 _ Aa))// ub_le_sup.
Qed.

Lemma inf_ge0 A : (forall x, A x -> 0 <= x) -> 0 <= inf A.
Proof.
move=> BA; have [->|/set0P A0] := eqVneq A set0; first by rewrite inf0.
by apply: le_inf.
Qed.

Lemma has_ub_wpZl A (a : R) : 0 <= a -> has_ubound A ->
  has_ubound [set a * x | x in A].
Proof.
move=> a0 [b ub]; exists (a * b) => _ [y Ay <-].
by rewrite ler_wpM2l// ub.
Qed.

Lemma has_lb_wpZl A (a : R) : 0 <= a -> has_lbound A ->
  has_lbound [set a * x | x in A].
Proof.
move=> a0 [b lb]; exists (a * b) => _ [y Ay <-].
by rewrite ler_wpM2l// lb.
Qed.

Lemma has_sup_wpZl A (a : R) : 0 <= a -> has_sup A ->
  has_sup [set a * x | x in A].
Proof.
move=> a0 [[x Ax] ubA].
split; first by exists (a * x), x.
by apply: has_ub_wpZl.
Qed.

Lemma has_inf_wpZl A (a : R) : 0 <= a -> has_inf A ->
  has_inf [set a * x | x in A].
Proof.
move=> a0 [[x Ax] ubA].
split; first by exists (a * x), x.
by apply: has_lb_wpZl.
Qed.

Lemma gt0_has_supZl A (a : R) : 0 < a -> has_sup [set a * x | x in A ] ->
  has_sup A.
Proof.
move=> a0 [[_ [x Ax _]] [b ub]]; split; first by exists x.
by exists (b / a) => y Ay; rewrite ler_pdivlMr// mulrC ub//; exists y.
Qed.

Lemma gt0_has_infzl A (a : R) : 0 < a -> has_inf [set a * x | x in A] ->
  has_inf A.
Proof.
move=> a0 [[_ [x Ax _]] [b lb]]; split; first by exists x.
by exists (b / a) => y Ay; rewrite ler_pdivrMr// mulrC lb//; exists y.
Qed.

Lemma ge0_supZl A (a : R) : 0 <= a -> sup [set a * x | x in A] = a * sup A.
Proof.
rewrite le_eqVlt => /predU1P[<-|an0].
  under eq_imagel do rewrite mul0r.
  by rewrite set_cst mul0r; case: ifP => _; rewrite ?sup0 ?sup1.
have [->|/set0P A0] := eqVneq A set0; first by rewrite image_set0 sup0 mulr0.
have [[[x Ax] ubA]|not_ex_sup] := pselect (has_sup A); last first.
  rewrite !sup_out ?mulr0//.
  by apply: contra_not not_ex_sup; exact: gt0_has_supZl.
apply: sup_eq.
  by move=> _ [y Ay <-]; rewrite ler_pM2l// ub_le_sup.
case: ubA => M ubM y uby.
rewrite -ler_pdivlMl// ge_sup// => z Az.
by rewrite ler_pdivlMl// uby//; exists z.
Qed.

Lemma ge0_infZl A (a : R) : 0 <= a -> inf [set a * x | x in A] = a * inf A.
Proof.
move=> a0; rewrite !infEN mulrN -(ge0_supZl (-%R @` A) a0); congr (- sup _).
by rewrite !image_comp/=; apply: eq_imagel => //= ? _; rewrite mulrN.
Qed.

Import arithmetic_tactic.

Lemma inf_pos : inf [set r : R | 0 < r] = 0.
Proof.
apply: lt_inf_eq => [? /ltW //|x x0].
by exists (x / 2) => /=; lra.
Qed.

Lemma sup_neg : sup [set r : R | r < 0] = 0.
Proof.
apply: gt_sup_eq => [? /ltW //| x x0].
by exists (x / 2) => /=; lra.
Qed.

Lemma has_sup_Mn A n : has_sup A -> has_sup [set x *+n | x in A].
Proof.
move=> [[x Ax] [y Ay]]; split; first by exists (x *+ n), x.
by exists (y *+ n) => _ [y0 Ay0 <-]; rewrite lerMn2r Ay// orbT.
Qed.

Lemma has_inf_Mn A n : has_inf A -> has_inf [set x *+ n | x in A].
Proof.
move=> [[x Ax] [y Ay]]; split; first by exists (x *+ n), x.
by exists (y *+ n) => _ [y0 Ay0 <-]; rewrite lerMn2r Ay// orbT.
Qed.

Lemma sup_Mn A n : sup [set x *+n | x in A ] = sup A *+ n.
Proof.
rewrite -mulr_natl (_ : [set _ | _ in _] = [set n%:R * x | x in A]).
  by under eq_fun do rewrite -mulr_natl.
exact: ge0_supZl.
Qed.

Lemma inf_Mn A n : inf [set x *+n | x in A ] = inf A *+ n.
Proof.
rewrite -mulr_natl (_ : [set _ | _ in _] = [set n%:R * x | x in A]).
  by under eq_fun do rewrite -mulr_natl.
exact: ge0_infZl.
Qed.

End Sup.

Lemma int_lbound_has_minimum (B : set int) i : B !=set0 -> lbound B i ->
  exists j, B j /\ forall k, B k -> j <= k.
Proof.
move=> [i0 Bi0] lbBi; have [n i0in] : exists n, i0 - i = n%:Z.
  by exists `|i0 - i|%N; rewrite gez0_abs // subr_ge0; exact: lbBi.
elim: n i lbBi i0in => [i lbBi /eqP|n ih i lbBi i0in1].
  by rewrite subr_eq0 => /eqP i0i; exists i0; split =>// k Bk; rewrite i0i lbBi.
have i0i1n : i0 - (i + 1) = n by rewrite opprD addrA i0in1 -addn1 PoszD addrK.
have [?|/not_forallP] := pselect (lbound B (i + 1)); first exact: (ih (i + 1)).
move=> /contrapT[x /not_implyP[Bx i1x]]; exists x; split => // k Bk.
rewrite (le_trans _ (lbBi _ Bk)) //.
by move/negP : i1x; rewrite -ltNge ltzD1.
Qed.

Lemma nat_has_minimum (A : set nat) : A !=set0 ->
  exists j, A j /\ forall k, A k -> (j <= k)%N.
Proof.
move=> A0.
pose B : set int := [set x%:~R | x in A].
have B0 : B !=set0 by apply: image_nonempty.
have: lbound B 0 by move=> _ [b0 Bb0 <-]; rewrite ler0z.
move/(int_lbound_has_minimum B0) => [_ [[i Ai <-]]] Bi.
exists i; split=> // k Bk.
by have := Bi k%:~R; rewrite ler_int; apply; exists k.
Qed.

Section rat_in_itvoo.

Let bound_div (R : archiRealFieldType) (x y : R) : nat :=
  if y < 0 then 0%N else Num.bound (y / x).

Let archi_bound_divP (R : archiRealFieldType) (x y : R) :
  0 < x -> y < x *+ bound_div x y.
Proof.
move=> x0; have [y0|y0] := leP 0 y; last by rewrite /bound_div y0 mulr0n.
rewrite /bound_div (ltNge y 0) y0/= -mulr_natl -ltr_pdivrMr//.
by rewrite archi_boundP// (divr_ge0 _(ltW _)).
Qed.

Lemma rat_in_itvoo (R : archiRealFieldType) (x y : R) :
  x < y -> exists q, ratr q \in `]x, y[.
Proof.
move=> xy; move: (xy); rewrite -subr_gt0.
move=> /(archi_bound_divP 1); set n := bound_div _ _ => nyx.
have [m1 m1nx] : exists m1, m1.+1%:~R > x *+ n.
  have := archi_bound_divP (x *+ n) ltr01; set p := bound_div _ _ => nxp.
  have [x0|x0] := ltP 0 x.
    exists p.-1; rewrite prednK // lt0n; apply: contraPN nxp => /eqP ->.
    by apply/negP; rewrite -leNgt mulrn_wge0 // ltW.
  by exists 0%N; rewrite (le_lt_trans _ ltr01) // mulrn_wle0.
have [m2 m2nx] : exists m2, m2.+1%:~R > - x *+ n.
  have := archi_bound_divP (- x *+ n) ltr01; set p := bound_div _ _ => nxp.
  have [x0|x0] := ltP 0 x.
    by exists O; rewrite (le_lt_trans _ ltr01) // nmulrn_rle0// oppr_lt0.
  exists p.-1; rewrite prednK // -(ltr_nat R) (le_lt_trans _ nxp) //.
  by rewrite mulrn_wge0 // oppr_ge0.
have : exists m, -(m2.+1 : int) <= m <= m1.+1 /\ m%:~R - 1 <= x *+ n < m%:~R.
  have m2m1 : - (m2.+1 : int) < m1.+1.
    by rewrite -(ltr_int R) (lt_trans _ m1nx)// rmorphN /= ltrNl // -mulNrn.
  pose B := [set m : int | m%:~R > x *+ n].
  have m1B : B m1.+1 by [].
  have m2B : lbound B (- m2.+1%:~R).
    move=> i; rewrite /B /= -(opprK (x *+ n)) -ltrNl -mulNrn => nxi.
    rewrite -(mulN1r m2.+1%:~R) mulN1r -lerNl.
    by have := lt_trans nxi m2nx; rewrite intz -mulrNz ltr_int => /ltW.
  have [m [Bm infB]] := int_lbound_has_minimum (ex_intro _ _ m1B) m2B.
  have mN1B : ~ B (m - 1).
    by move=> /infB; apply/negP; rewrite -ltNge ltrBlDr ltzD1.
  exists m; (split; [apply/andP; split|apply/andP; split]) => //.
  - by move: m2B; rewrite /lbound /= => /(_ _ Bm); rewrite intz.
  - exact: infB.
  - by rewrite leNgt; apply/negP; rewrite /B /= intrD in mN1B.
move=> [m [/andP[m2m mm1] /andP[mnx nxm]]].
have [/andP[a b] c] : x *+ n < m%:~R <= 1 + x *+ n /\ 1 + x *+ n < y *+ n.
  (split; [apply/andP; split|]) => //; first by rewrite -lerBlDl.
  by move: nyx; rewrite mulrnDl -ltrBrDr mulNrn.
have n_gt0 : n != 0%N by apply: contraTN nyx => /eqP ->; rewrite mulr0n ltr10.
exists (m%:Q / n%:Q); rewrite in_itv /= fmorph_div/= ratr_nat ratr_int.
rewrite ltr_pdivlMr ?ltr_pdivrMr ?ltr0n ?lt0n// !mulr_natr nxm/=.
apply: (le_lt_trans b c).
Qed.

End rat_in_itvoo.

Section rational.
Context {R : realType}.

Definition rational : set R := ratr @` [set: rat].

Lemma rationalP (r : R) :
  rational r <-> exists (a : int) (b : nat), r = a%:~R / b%:R.
Proof.
split=> [[q _ <-{r}]|[a [b ->]]]; last first.
  by exists (a%:~R / b%:R); rewrite // fmorph_div/= ratr_nat ratr_int.
have [n d nd] := ratP q; exists n, d.+1.
by rewrite fmorph_div/= ratr_nat ratr_int.
Qed.

Definition irrational : set R := ~` rational.

Lemma irrationalE : irrational = \bigcap_(q : rat) ~` (ratr @` [set q]).
Proof.
apply/seteqP; split => [r/= rE q _/=|r/= rE [q] _ qr]; last first.
  by apply: (rE q Logic.I) => /=; exists q.
by apply: contra_not rE => -[_ -> <-{r}]; exists q.
Qed.

End rational.
