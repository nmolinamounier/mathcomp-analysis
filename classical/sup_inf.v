From HB Require Import structures.
From mathcomp Require Import boot order ssralg matrix finmap ssrnum.
From mathcomp Require Import ssrint rat interval.
From mathcomp Require Import boolp classical_sets.

Import Order.Def.

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope order_scope.
Open Scope classical_set_scope.

Section ubound_lbound.
Import Order.LTheory.
Context {d} {T : porderType d}.
Implicit Types (A : set T) (x y z : T).

Definition ubound A : set T := [set y | forall x, A x -> x <= y].
Definition lbound A : set T := [set y | forall x, A x -> y <= x].

Lemma ubP A x : (forall y, A y -> y <= x) <-> ubound A x.
Proof. by []. Qed.

Lemma lbP A x : (forall y, A y -> x <= y) <-> lbound A x.
Proof. by []. Qed.

Lemma ub_set0 : ubound set0 = [set: T].
Proof. by rewrite -subTset => ? _ ?. Qed.

Lemma lb_set0 : lbound set0 = [set: T].
Proof. by rewrite -subTset => ? _ ?. Qed.

Lemma ub_set1 x y : ubound [set x] y = (x <= y).
Proof. by rewrite propeqE; split => [/(_ x erefl)//|xy z ->]. Qed.

Lemma lb_set1 x y : lbound [set x] y = (x >= y).
Proof. by rewrite propeqE; split => [/(_ x erefl)//|xy z ->]. Qed.

Lemma lb_ub_set1 x y : lbound (ubound [set x]) y -> y <= x.
Proof. by move/(_ x); apply; rewrite ub_set1. Qed.

Lemma ub_lb_set1 x y : ubound (lbound [set x]) y -> x <= y.
Proof. by move/(_ x); apply; rewrite lb_set1. Qed.

Lemma lb_ub_refl x : lbound (ubound [set x]) x.
Proof. by move=> y; apply. Qed.

Lemma ub_lb_refl x : ubound (lbound [set x]) x.
Proof. by move=> y; apply. Qed.

Lemma ub_lb_ub A x y : ubound A y -> lbound (ubound A) x -> x <= y.
Proof. by move=> Ay; apply. Qed.

Lemma lb_ub_lb A x y : lbound A y -> ubound (lbound A) x -> y <= x.
Proof. by move=> Ey; apply. Qed.

(* down set (i.e., generated order ideal) *)
(* i.e. down A := { x | exists y, y \in A /\ x <= y} *)
Definition down A : set T := [set x | exists y, A y /\ x <= y].
Definition up A : set T := [set x | exists y, A y /\ y <= x].

Definition has_ubound A := ubound A !=set0.
Definition has_sup A := (A !=set0) /\ has_ubound A.
Definition has_lbound A := lbound A !=set0.
Definition has_inf A := (A !=set0) /\ has_lbound A.

Lemma has_ub_set1 x : has_ubound [set x].
Proof. by exists x; rewrite ub_set1. Qed.

Lemma has_inf0 : ~ has_inf (@set0 T).
Proof. by rewrite /has_inf not_andP; left; exact/nonemptyPn. Qed.

Lemma has_sup0 : ~ has_sup (@set0 T).
Proof. by rewrite /has_sup not_andP; left; exact/nonemptyPn. Qed.

Lemma has_sup1 x : has_sup [set x].
Proof. by split; [exists x | exists x => y ->]. Qed.

Lemma has_inf1 x : has_inf [set x].
Proof. by split; [exists x | exists x => y ->]. Qed.

Lemma subset_has_lbound A B : A `<=` B -> has_lbound B -> has_lbound A.
Proof. by move=> AB [l Bl]; exists l => a Aa; exact/Bl/AB. Qed.

Lemma subset_has_ubound A B : A `<=` B -> has_ubound B -> has_ubound A.
Proof. by move=> AB [l Bl]; exists l => a Aa; exact/Bl/AB. Qed.

Lemma downP A x : (exists2 y, A y & x <= y) <-> down A x.
Proof. by rewrite exists2E. Qed.

Lemma upP A x : (exists2 y, A y & y <= x) <-> up A x.
Proof. by rewrite exists2E. Qed.

Lemma subset_down A : A `<=` down A.
Proof. by move=> x ?; exists x. Qed.

Lemma subset_up A : A `<=` up A.
Proof. by move=> x ?; exists x. Qed.

Lemma downK A : down (down A) = down A.
Proof.
apply/seteqP; split; last exact: subset_down.
move=> x /downP[y /downP[z Az +]] => /[swap] /le_trans /[apply] xz.
by exists z.
Qed.

Lemma upK A : up (up A) = up A.
Proof.
apply/seteqP; split; last exact: subset_up.
move=> x /upP[y /upP[z Az +]] => /le_trans /[apply] zx.
by exists z.
Qed.

Lemma has_ubound_down A : has_ubound (down A) <-> has_ubound A.
Proof.
split; first by apply: subset_has_ubound; exact: subset_down.
by case=> M ubM; exists M => x /downP[y /ubM /[swap]]; exact: le_trans.
Qed.

Lemma has_lbound_up A : has_lbound (up A) <-> has_lbound A.
Proof.
split; first by apply: subset_has_lbound; exact: subset_up.
by case=> M lbM; exists M => x /upP[y /lbM]; exact: le_trans.
Qed.

Lemma has_sup_down A : has_sup (down A) <-> has_sup A.
Proof.
apply/propeqP; congr and; last by apply/propeqP/has_ubound_down.
apply/propeqP; split; last first. 
  by apply: subset_nonempty; exact: subset_down.
by move=> [? [y [? _]]]; exists y.
Qed.

Lemma has_inf_up A : has_inf (up A) <-> has_inf A.
Proof.
apply/propeqP; congr and; last by apply/propeqP/has_lbound_up.
apply/propeqP; split; last first. 
  by apply: subset_nonempty; exact: subset_up.
by move=> [? [y [? _]]]; exists y.
Qed.

Definition supremums A := ubound A `&` lbound (ubound A).

Lemma supremums1 x : supremums [set x] = [set x].
Proof.
rewrite /supremums predeqE => y; split => [[]|->{y}]; last first.
  by split; [rewrite ub_set1|exact: lb_ub_refl].
by rewrite ub_set1 => xy /lb_ub_set1 yx; apply/eqP; rewrite eq_le xy yx.
Qed.

Lemma is_subset1_supremums A : is_subset1 (supremums A).
Proof.
move=> x y [Ax xA] [Ay yA]; apply/eqP.
by rewrite eq_le (ub_lb_ub Ax yA) (ub_lb_ub Ay xA).
Qed.

Definition infimums A := lbound A `&` ubound (lbound A).

Lemma infimums1 x : infimums [set x] = [set x].
Proof.
rewrite /infimums predeqE => y; split => [[]|->{y}]; last first.
  by split; [rewrite lb_set1|apply ub_lb_refl].
by rewrite lb_set1 => xy /ub_lb_set1 yx; apply/eqP; rewrite eq_le xy yx.
Qed.

Lemma is_subset1_infimums A : is_subset1 (infimums A).
Proof.
move=> x y [Ax xA] [Ay yA]; apply/eqP.
by rewrite eq_le (lb_ub_lb Ax yA) (lb_ub_lb Ay xA).
Qed.

End ubound_lbound.
#[global] Hint Resolve subset_up subset_down : core.

Section total_ubound_lbound.
Import Order.TTheory.
Variables (d : Order.disp_t) (T : orderType d).
Implicit Types (A : set T) (x y z : T).

Lemma has_ubPn {A} : ~ has_ubound A <-> (forall x, exists2 y, A y & x < y).
Proof.
split; last first.
  move=> h [x] /ubP hle; case/(_ x): h => y /hle.
  by move=> /le_lt_trans /[apply]; rewrite ltxx.
move/forallNP => h x; have {h} := h x.
move=> /ubP /existsNP => -[y /not_implyP[Ey /negP]].
by rewrite -ltNge => ltx; exists y.
Qed.

Lemma has_lbPn E : ~ has_lbound E <-> (forall x, exists2 y, E y & y < x).
Proof.
split; last first.
  move=> h [x] /lbP hle; case/(_ x): h => y /hle.
  by move=> /le_lt_trans /[apply]; rewrite ltxx.
move/forallNP => h x; have {h} := h x.
move=> /lbP /existsNP => -[y /not_implyP[Ey /negP]].
by rewrite -ltNge => ltx; exists y.
Qed.

Lemma has_supPn {E} : E !=set0 ->
  ~ has_sup E <-> (forall x, exists2 y, E y & x < y).
Proof. by rewrite /has_sup => /propT ->; rewrite andB; exact: has_ubPn. Qed.

Lemma has_infPn {E} : E !=set0 ->
  ~ has_inf E <-> (forall x, exists2 y, E y & y < x).
Proof. by rewrite /has_inf => /propT ->; rewrite andB; exact: has_lbPn. Qed.

End total_ubound_lbound.

Lemma nat_supremums_neq0 (A : set nat) : ubound A !=set0 -> supremums A !=set0.
Proof.
case => /=; elim => [A0|n ih]; first by exists O.
case: (pselect (ubound A n)) => [/ih //|An {ih}] An1.
exists n.+1; split => // m Am; case/existsNP : An => k /not_implyP[Ak /negP].
rewrite -Order.TotalTheory.ltNge => kn.
by rewrite (Order.POrderTheory.le_trans _ (Am _ Ak)).
Qed.

HB.mixin Record POrder_isDedekindComplete d T & Order.POrder d T := {
  sup : set T -> T ;
  inf : set T -> T ;
  ub_le_sup_subproof : forall (A : set T), has_ubound A -> ubound A (sup A) ;
  sup_lub_subproof : forall (A : set T), 
    has_ubound A -> lbound (ubound A) !=set0 -> lbound (ubound A) (sup A) ;
  lb_ge_inf_subproof : forall (A : set T), has_lbound A -> lbound A (inf A) ;
  inf_glb_subproof : forall (A : set T), 
    has_lbound A -> ubound (lbound A) !=set0 -> ubound (lbound A) (inf A)
}.

#[short(type="dedekindPOrderType")]
HB.structure Definition DedekindPOrder d := 
  {T of Order.POrder d T & POrder_isDedekindComplete d T}.
#[short(type="dedekindTPOrderType")]
HB.structure Definition DedekindTPOrder d :=
  {T of Order.TPOrder d T & POrder_isDedekindComplete d T}.
#[short(type="dedekindBPOrderType")]
HB.structure Definition DedekindBPOrder d :=
  {T of Order.BPOrder d T & POrder_isDedekindComplete d T}.
#[short(type="dedekindTBPOrderType")]
HB.structure Definition DedekindTBPOrder d :=
  {T of Order.TBPOrder d T & POrder_isDedekindComplete d T}.

#[short(type="dedekindOrderType")]
HB.structure Definition DedekindOrder d := 
  {T of Order.Total d T & DedekindPOrder d T}.
#[short(type="dedekindTOrderType")]
HB.structure Definition DedekindTOrder d := 
  {T of Order.Total d T & DedekindTPOrder d T}.
#[short(type="dedekindBOrderType")]
HB.structure Definition DedekindBOrder d := 
  {T of Order.Total d T & DedekindBPOrder d T}.
#[short(type="dedekindTBOrderType")]
HB.structure Definition DedekindTBOrder d := 
  {T of Order.Total d T & DedekindTBPOrder d T}.

Section dedekind_dual.
Context {d} {T : dedekindPOrderType d}.

Let sup' : set T^d -> T := @inf _ T.
Let inf' : set T^d -> T := @sup _ T.

HB.instance Definition _ := @POrder_isDedekindComplete.Build _ T^d sup' inf' 
  lb_ge_inf_subproof inf_glb_subproof ub_le_sup_subproof sup_lub_subproof.

Lemma supEdual A : sup (A :> set T^d) = inf (A :> set T).
Proof. by []. Qed.

Lemma infEdual A : inf (A :> set T^d) = sup (A :> set T).
Proof. by []. Qed.

End dedekind_dual.

Module Dedekind.

Module Order.

Section dedekindPOrder.
Context {d} {T : dedekindPOrderType d}.
Implicit Types (A B : set T).

Import Order.LTheory.

Lemma ub_le_sup A : has_ubound A -> ubound A (sup A).
Proof. exact: ub_le_sup_subproof. Qed.

#[deprecated(since="analysis 1.20.0", use=ub_le_sup)]
Lemma sup_upper_bound A : has_sup A -> ubound A (sup A).
Proof. by move=> [_ +]; exact: ub_le_sup. Qed.

Lemma lb_ge_inf A : has_lbound A -> lbound A (inf A).
Proof. exact: lb_ge_inf_subproof. Qed.

Lemma sup_lub A : 
  has_ubound A -> lbound (ubound A) !=set0 -> lbound (ubound A) (sup A).
Proof. exact: sup_lub_subproof. Qed.

Lemma inf_glb A : 
  has_lbound A -> ubound (lbound A) !=set0 -> ubound (lbound A) (inf A).
Proof. exact: inf_glb_subproof. Qed.

Lemma le_sup A r : has_ubound A -> down A r -> r <= sup A.
Proof. by move=> ubA [x [Ax /le_trans]]; apply; apply: ub_le_sup. Qed.

Lemma ge_inf A r : has_lbound A -> up A r -> inf A <= r.
Proof. by move=> lbA [x [Ax]]; apply: le_trans; apply: lb_ge_inf. Qed.

Lemma ge_sup {A} r : A !=set0 -> ubound A r -> sup A <= r.
Proof.
move=> Ane ubr.
apply: sup_lub => //; first by exists r.
by apply: subset_nonempty Ane => x Ax ?; apply.
Qed.

Lemma le_inf {A} r : A !=set0 -> lbound A r -> r <= inf A.
Proof.
move=> Ane lbr.
apply: inf_glb => //; first by exists r.
by apply: subset_nonempty Ane => x Ax ?; apply.
Qed.

Lemma ge_supP {A} x : has_sup A -> sup A <= x <-> ubound A x.
Proof.
move=> [Ane ubA]; split; last by apply: ge_sup.
by move=> + ? ?; apply: le_trans; apply: ub_le_sup.
Qed.

Lemma le_infP {A} x : has_inf A -> x <= inf A <-> lbound A x.
Proof.
move=> [Ane lbA]; split; last by apply: le_inf.
by move=> /le_trans + ? ?; apply; apply: lb_ge_inf.
Qed.

Lemma gt_sup {A} x : has_ubound A -> sup A < x -> forall y, A y -> y < x.
Proof. by move=> hsA sAx y Ay; apply: le_lt_trans sAx; apply: ub_le_sup. Qed.

Lemma lt_inf {A} x : has_lbound A -> x < inf A -> forall y, A y -> x < y.
Proof. by move=> hsA /lt_le_trans + y Ay; apply; apply: lb_ge_inf. Qed.

Lemma sup_ub_strict {A} : has_ubound A ->
  ~ A (sup A) -> A `<=` [set r | r < sup A].
Proof.
move=> ubA AsupA r Ar /=; rewrite lt_neqAle ub_le_sup // andbT.
by apply/negP => /eqP supAr; move: AsupA; rewrite -supAr.
Qed.

Lemma inf_lb_strict {A} : has_lbound A ->
  ~ A (inf A) -> A `<=` [set r | inf A < r].
Proof.
move=> lbA AinfA r Ar /=; rewrite lt_neqAle lb_ge_inf // andbT.
by apply/negP => /eqP infAr; move: AinfA; rewrite infAr.
Qed.

Lemma sup_le A B : A !=set0 -> has_ubound B -> A `<=` down B -> sup A <= sup B.
Proof.
move=> Ane ubB AdB.
apply: ge_sup => // x Ax.
by apply: le_sup => //; apply: AdB.
Qed.

Lemma inf_le A B : A !=set0 -> has_lbound B -> A `<=` up B -> inf B <= inf A.
Proof.
move=> Ane lbB AuB.
apply: le_inf => // x Ax.
by apply: ge_inf => //; apply: AuB.
Qed.

Lemma supS {A B} : A !=set0 -> has_ubound B -> A `<=` B -> sup A <= sup B.
Proof. by move=> ? ? AB; apply: sup_le => //; apply: (subset_trans AB). Qed.

Lemma infS {A B} : A !=set0 -> has_lbound B -> A `<=` B -> inf B <= inf A.
Proof. by move=> ? ? AB; apply: inf_le => //; apply: (subset_trans AB). Qed.

Lemma sup_setU A B : has_sup B ->
  (forall a b, A a -> B b -> a <= b) -> sup (A `|` B) = sup B.
Proof.
move/[dup] => -[Bne ubB] [[b Bb] [M ubM]] A_le_B.
apply/le_anti/andP; split; last first.
  apply: supS => //; exists M => x [Ax|]; last exact: ubM.
  by apply: le_trans (ubM b Bb); apply: A_le_B.
apply: sup_le => //; first by exists b; right.
move=> x []; last exact: subset_down.
by move=> /A_le_B /(_ Bb) xb; exists b.
Qed.

Lemma inf_setU A B : has_inf A ->
  (forall a b, A a -> B b -> a <= b) -> inf (A `|` B) = inf A.
Proof.
move/[dup] => -[Ane ubA] [[a Aa] [M ubM]] A_le_B.
apply/le_anti/andP; split.
  apply: infS => //; exists M => x [|Bx]; first exact: ubM.
  by apply: (le_trans (ubM a Aa)); apply: A_le_B.
apply: inf_le => //; first by exists a; left.
move=> x []; first exact: subset_up.
by move=> /(A_le_B a _ Aa) ax; exists a.
Qed.

Lemma lt_sup A r : has_ubound A ->
  (exists2 x, A x & r < x) -> r < sup A.
Proof.
move=> ubA [x Ax] => /lt_le_trans; apply.
by apply: ub_le_sup.
Qed.

Lemma gt_inf A r : has_lbound A ->
  (exists2 x, A x & x < r) -> inf A < r.
Proof.
move=> lbA [x Ax]; apply: le_lt_trans.
by apply: lb_ge_inf.
Qed.

Lemma sup_eq A r :
  ubound A r -> lbound (ubound A) r ->
  sup A = r.
Proof.
move=> ubA lbubA.
apply/le_anti/andP; split. 
  by apply: sup_lub => //; exists r.
by apply: lbubA; apply: ub_le_sup; exists r.
Qed.

Lemma inf_eq A r :
  lbound A r -> ubound (lbound A) r ->
  inf A = r.
Proof.
move=> lbA ublbA.
apply/le_anti/andP; split; last first.
  by apply: inf_glb => //; exists r.
by apply: ublbA; apply: lb_ge_inf; exists r.
Qed.

Lemma sup_eq_sup A B : 
  has_ubound A ->
  A `<=` down B -> B `<=` down A ->
  sup A = sup B.
Proof.
case: (eqVneq A set0) => [-> _ _ Bd0|/set0P Ane Aub AdB BdA].
  suff : B `<=` set0 by rewrite subset0 => ->.
  by move=> ? /Bd0[? []].
have Bne : B !=set0.
  by case: Ane => x /AdB[b [? _]]; exists b.
have Bub : has_ubound B.
  case: Aub => M ubM; exists M => x.
  by case/BdA => a [/ubM /[swap]]; exact: le_trans.
by apply/le_anti/andP; split; apply: sup_le.
Qed.

Lemma inf_eq_inf A B :
  has_lbound A ->
  A `<=` up B -> B `<=` up A ->
  inf A = inf B.
Proof.
case: (eqVneq A set0) => [-> _ _ Bu0|/set0P Ane Alb AuB BuA].
  suff : B `<=` set0 by rewrite subset0 => ->.
  by move=> ? /Bu0[? []].
have Bne : B !=set0.
  by case: Ane => x /AuB[b [? _]]; exists b.
have Bub : has_lbound B.
  case: Alb => M ubM; exists M => x.
  by case/BuA => a [/ubM]; exact: le_trans.
by apply/le_anti/andP; split; apply: inf_le.
Qed.

Lemma sup_downE A : has_ubound A -> sup (down A) = sup A.
Proof.
by move=> ubA; apply: sup_eq_sup => //
  ; [ apply/has_ubound_down | rewrite downK ].
Qed.

Lemma inf_upE A : has_lbound A -> inf (up A) = inf A.
Proof.
by move=> ubA; apply: inf_eq_inf => //
  ; [ apply/has_lbound_up | rewrite upK ].
Qed.

Lemma sup1 (x : T) : sup [set x] = x.
Proof. by apply: sup_eq => [_ -> //|?]; apply. Qed.

Lemma inf1 (x : T) : inf [set x] = x.
Proof. by apply: inf_eq => [_ -> //|?]; apply. Qed.

Lemma sup_le_set (x : T) : sup [set y | y <= x] = x.
Proof. by apply: sup_eq => // ?; apply=> /=. Qed.

Lemma inf_ge_set (x : T) : inf [set y | x <= y] = x.
Proof. by apply: inf_eq => // ?; apply=> /=. Qed.

Lemma sup_interchange X Y (A : set X) (B : set Y) (f : X -> Y -> T) :
  has_ubound [set f x y | x in A & y in B] ->
  sup [set sup [set f x y | y in B] | x in A]
    = sup [set sup [set f x y | x in A] | y in B].
Proof.
move=> ubf.
set L := LHS; set R := RHS.
wlog suff : X Y A B f ubf @L @R / L <= R.
  move=> LRcase.
  apply/le_anti/andP; split; first by apply: LRcase.
  by apply: (LRcase _ _ _ _ (fun y x => f x y)); rewrite -image2_sym.
move: @L @R => /=.
case: (eqVneq A set0) => [->|/set0P Ane].
  rewrite image_set0; under eq_imagel do rewrite image_set0.
  by rewrite set_cst; case: ifP => // _; rewrite sup1.
case: (eqVneq B set0) => [->|/set0P Bne].
  rewrite image_set0; under eq_imagel do rewrite image_set0.
  by rewrite set_cst; case: ifP => // _; rewrite sup1.
apply: ge_sup; first by apply: image_nonempty.
move=> _ [x Ax <-].
apply: sup_le; first by apply: image_nonempty.
- case: ubf => M ubM. 
  exists M => ? [y By <-].
  apply: ge_sup; first by apply: image_nonempty.
  by move=> ? [x' ? <-]; apply: ubM; exists x' => //; exists y.
- move=> _ [y By <-]; apply/downP.
  exists (sup [set f x' y | x' in A]); first by exists y.
  apply: ub_le_sup.
    apply: subset_has_ubound ubf => _ [x' ? <-].
    by exists x' => //; exists y.
  by exists x.
Qed.

End dedekindPOrder.

Lemma inf_interchange {d} {T : dedekindPOrderType d} 
    X Y (A : set X) (B : set Y) (f : X -> Y -> T) :
  has_lbound [set f x y | x in A & y in B] ->
  inf [set inf [set f x y | y in B] | x in A]
    = inf [set inf [set f x y | x in A] | y in B].
Proof. exact: (@sup_interchange _ T^d _ _ A B f). Qed.

Section dedekindOrder.
Context {d} {T : dedekindOrderType d}.
Implicit Types (A B : set T).

Import Order.TTheory.

Lemma lt_sup_ex A r : A !=set0 ->
  r < sup A -> exists2 y, A y & r < y.
Proof.
move=> Ane; apply: contra_ltP => /forallPNP g.
by apply: ge_sup => // y /g /negP; rewrite -leNgt.
Qed.

Lemma gt_inf_ex A r : A !=set0 ->
  inf A < r -> exists2 y, A y & y < r.
Proof.
move=> Ane; apply: contra_ltP => /forallPNP g.
by apply: le_inf => // y /g /negP; rewrite -leNgt.
Qed.

Lemma lt_supP A r : has_sup A ->
  r < sup A <-> exists2 y, A y & r < y.
Proof. by move=> [Ane ubA]; split; [ apply: lt_sup_ex | apply: lt_sup ]. Qed.

Lemma gt_infP A r : has_inf A ->
  inf A < r <-> exists2 y, A y & y < r.
Proof. by move=> [Ane lbA]; split; [ apply: gt_inf_ex | apply: gt_inf ]. Qed.

Lemma gt_sup_eq A r : 
  ubound A r ->
  (forall x, x < r -> exists2 y, A y & x < y) -> 
  sup A = r.
Proof.
move=> ubAr adhA.
apply/le_anti/andP; split; last first.
  apply/le_gtP => /= x /adhA[y Ay] /lt_le_trans; apply.
  by apply: ub_le_sup => //; exists r.
apply: sup_lub => //; exists r => // x.
apply: contraPle => /adhA[y Ay xy] /(_ y Ay).
by apply/negP; rewrite -ltNge.
Qed.

Lemma lt_inf_eq A r : 
  lbound A r ->
  (forall x, r < x -> exists2 y, A y & y < x) -> 
  inf A = r.
Proof.
move=> lbAr adhA.
apply/le_anti/andP; split.
  apply/le_ltP => /= x /adhA[y Ay]; apply: le_lt_trans.
  by apply: lb_ge_inf => //; exists r.
apply: inf_glb => //; exists r => // x.
apply: contraPle => /adhA[y Ay xy] /(_ y Ay).
by apply/negP; rewrite -ltNge.
Qed.

Lemma sup_total {A} r : A !=set0 -> down A r \/ sup A <= r.
Proof.
move=> Ane.
case: (leP (sup A) r); first by right.
move=> /(lt_sup_ex Ane)[y Ay ry]; left.
by exists y; split=> //; apply: ltW.
Qed.

Lemma inf_total {A} r : A !=set0 -> up A r \/ r <= inf A.
Proof.
move=> Ane.
case: (leP r (inf A)); first by right.
move=> /(gt_inf_ex Ane)[y Ay yr]; left.
by exists y; split=> //; apply: ltW.
Qed.

End dedekindOrder.

End Order.

Module TOrder.
Import Order.

Section dedekindTPOrder.
Context {d} {T : dedekindTPOrderType d}.
Implicit Types (A B : set T).

Import Order.LTheory.

Lemma top_has_ubound A : has_ubound A.
Proof. by exists \top. Qed.
#[local] Hint Resolve top_has_ubound : core.

Lemma top_has_sup A : A !=set0 -> has_sup A.
Proof. by []. Qed.

Lemma inf0Etop : inf set0 = \top :> T.
Proof.
apply/le_anti; rewrite lex1 /=.
by apply: inf_glb => //; exists \top.
Qed.

Lemma ub_le_sup A : ubound A (sup A).
Proof. exact: ub_le_sup. Qed.

Lemma lb_ge_inf A : has_lbound A -> lbound A (inf A).
Proof. exact: lb_ge_inf. Qed.

Lemma sup_lub A : 
  lbound (ubound A) !=set0 -> lbound (ubound A) (sup A).
Proof. exact: sup_lub. Qed.

Lemma inf_glb A : 
  has_lbound A -> ubound (lbound A) (inf A).
Proof. by move=> ?; apply: inf_glb => //; exists \top. Qed.

Lemma le_sup A r : down A r -> r <= sup A.
Proof. exact: le_sup. Qed.

Lemma ge_inf A r : has_lbound A -> up A r -> inf A <= r.
Proof. exact: ge_inf. Qed.

Lemma ge_sup {A} r : A !=set0 -> ubound A r -> sup A <= r.
Proof. exact: ge_sup. Qed.

Lemma le_inf {A} r : lbound A r -> r <= inf A.
Proof. 
by case: (eqVneq A set0) => [-> _|/set0P]
  ; [ rewrite inf0Etop | exact: le_inf ].
Qed.

Lemma ge_supP {A} x : A !=set0 -> sup A <= x <-> ubound A x.
Proof. by move/top_has_sup; exact: ge_supP. Qed.

Lemma le_infP {A} x : has_lbound A -> x <= inf A <-> lbound A x.
Proof. 
case: (eqVneq A set0) => [-> _|/set0P Ane lbA]; last by apply: le_infP.
by rewrite inf0Etop lex1; split=> // _.
Qed.

Lemma gt_sup {A} x : sup A < x -> forall y, A y -> y < x.
Proof. exact: gt_sup. Qed.

Lemma lt_inf {A} x : has_lbound A -> x < inf A -> forall y, A y -> x < y.
Proof. exact: lt_inf. Qed.

Lemma sup_ub_strict {A} :
  ~ A (sup A) -> A `<=` [set r | r < sup A].
Proof. exact: sup_ub_strict. Qed.

Lemma inf_lb_strict {A} : has_lbound A ->
  ~ A (inf A) -> A `<=` [set r | inf A < r].
Proof. exact: inf_lb_strict. Qed.

Lemma sup_le A B : A !=set0 -> A `<=` down B -> sup A <= sup B.
Proof. by move=> ?; apply: sup_le. Qed.

Lemma inf_le A B : has_lbound B -> A `<=` up B -> inf B <= inf A.
Proof.
by case: (eqVneq A set0) => [->|/set0P Ane]; 
  [ rewrite inf0Etop | apply: inf_le ].
Qed.

Lemma supS {A B} : A !=set0 -> A `<=` B -> sup A <= sup B.
Proof. by move=> ?; apply: supS. Qed.

Lemma infS {A B} : has_lbound B -> A `<=` B -> inf B <= inf A.
Proof.
by case: (eqVneq A set0) => [->|/set0P ? ? AB]; 
  [ rewrite inf0Etop | apply: infS ].
Qed.

Lemma sup_setU A B : B !=set0 ->
  (forall a b, A a -> B b -> a <= b) -> sup (A `|` B) = sup B.
Proof. by move=> ?; apply: sup_setU. Qed.

Lemma inf_setU A B : has_inf A ->
  (forall a b, A a -> B b -> a <= b) -> inf (A `|` B) = inf A.
Proof. exact: inf_setU. Qed.

Lemma lt_sup A r : 
  (exists2 x, A x & r < x) -> r < sup A.
Proof. exact: lt_sup. Qed.

Lemma gt_inf A r : has_lbound A ->
  (exists2 x, A x & x < r) -> inf A < r.
Proof. exact: gt_inf. Qed.

Lemma sup_eq A r :
  ubound A r -> lbound (ubound A) r ->
  sup A = r.
Proof. exact: sup_eq. Qed.

Lemma inf_eq A r :
  lbound A r -> ubound (lbound A) r ->
  inf A = r.
Proof. exact: inf_eq. Qed.

Lemma sup_eq_sup A B :
  A `<=` down B -> B `<=` down A ->
  sup A = sup B.
Proof. exact: sup_eq_sup. Qed.

Lemma inf_eq_inf A B :
  has_lbound A ->
  A `<=` up B -> B `<=` up A ->
  inf A = inf B.
Proof. exact: inf_eq_inf. Qed.

Lemma sup_downE A : sup (down A) = sup A.
Proof. exact: sup_downE. Qed.

Lemma inf_upE A : has_lbound A -> inf (up A) = inf A.
Proof. exact: inf_upE. Qed.

Lemma sup1 (x : T) : sup [set x] = x.
Proof. exact: sup1. Qed.

Lemma inf1 (x : T) : inf [set x] = x.
Proof. exact: inf1. Qed.

Lemma sup_le_set (x : T) : sup [set y | y <= x] = x.
Proof. exact: sup_le_set. Qed.

Lemma inf_ge_set (x : T) : inf [set y | x <= y] = x.
Proof. exact: inf_ge_set. Qed.

Lemma sup_interchange X Y (A : set X) (B : set Y) (f : X -> Y -> T) :
  sup [set sup [set f x y | y in B] | x in A]
    = sup [set sup [set f x y | x in A] | y in B].
Proof. exact: sup_interchange. Qed.

Lemma inf_interchange X Y (A : set X) (B : set Y) (f : X -> Y -> T) :
  has_lbound [set f x y | x in A & y in B] ->
  inf [set inf [set f x y | y in B] | x in A]
    = inf [set inf [set f x y | x in A] | y in B].
Proof. exact: inf_interchange. Qed.

End dedekindTPOrder.
#[global] Hint Extern 0 (has_ubound _) => solve[apply: top_has_ubound] : core.

Section dedekindTOrder.
Context {d} {T : dedekindTOrderType d}.
Implicit Types (A B : set T).

Import Order.TTheory.

Lemma lt_sup_ex A r : A !=set0 ->
  r < sup A -> exists2 y, A y & r < y.
Proof. exact: lt_sup_ex. Qed.

Lemma gt_inf_ex A r : 
  inf A < r -> exists2 y, A y & y < r.
Proof. 
by case: (eqVneq A set0) => [->|/set0P Ane];
  [ rewrite inf0Etop lt1x | exact: gt_inf_ex ].
Qed.

Lemma lt_supP A r : A !=set0 ->
  r < sup A <-> exists2 y, A y & r < y.
Proof. by move=> ?; exact: lt_supP. Qed.

Lemma gt_infP A r : has_lbound A ->
  inf A < r <-> exists2 y, A y & y < r.
Proof.
case: (eqVneq A set0) => [-> _|/set0P ? ?]; last by apply: gt_infP.
by rewrite inf0Etop lt1x; split=> // - [].
Qed.

Lemma gt_sup_eq A r : 
  ubound A r ->
  (forall x, x < r -> exists2 y, A y & x < y) -> 
  sup A = r.
Proof. exact: gt_sup_eq. Qed.

Lemma lt_inf_eq A r : 
  lbound A r ->
  (forall x, r < x -> exists2 y, A y & y < x) -> 
  inf A = r.
Proof. exact: lt_inf_eq. Qed.

Lemma sup_total {A} r : A !=set0 -> down A r \/ sup A <= r.
Proof. exact: sup_total. Qed.

Lemma inf_total {A} r : up A r \/ r <= inf A.
Proof.
by case: (eqVneq A set0) => [->|/set0P]
  ; [ rewrite inf0Etop; right | exact: inf_total ].
Qed.

End dedekindTOrder.

End TOrder.

Module BOrder.
Import Order.

Section dedekindBPOrder.
Context {d} {T : dedekindBPOrderType d}.
Implicit Types (A B : set T).

Import Order.LTheory.

Lemma bot_has_lbound A : has_lbound A.
Proof. by exists \bot. Qed.
#[local] Hint Resolve bot_has_lbound : core.

Lemma bot_has_inf A : A !=set0 -> has_inf A.
Proof. by []. Qed.

Lemma sup0Ebot : sup set0 = \bot :> T.
Proof.
apply/le_anti; rewrite le0x andbT.
by apply: sup_lub => //; exists \bot.
Qed.

Lemma ub_le_sup A : has_ubound A -> ubound A (sup A).
Proof. exact: ub_le_sup. Qed.

Lemma lb_ge_inf A : lbound A (inf A).
Proof. exact: lb_ge_inf. Qed.

Lemma sup_lub A : 
  has_ubound A -> lbound (ubound A) (sup A).
Proof. by move=> ?; apply: sup_lub => //; exists \bot. Qed.

Lemma inf_glb A : 
  ubound (lbound A) !=set0 -> ubound (lbound A) (inf A).
Proof. exact: inf_glb. Qed.

Lemma le_sup A r : has_ubound A -> down A r -> r <= sup A.
Proof. exact: le_sup. Qed.

Lemma ge_inf A r : up A r -> inf A <= r.
Proof. exact: ge_inf. Qed.

Lemma ge_sup {A} r : ubound A r -> sup A <= r.
Proof.
by case: (eqVneq A set0) => [-> _|/set0P]
  ; [ rewrite sup0Ebot | exact: ge_sup ].
Qed.

Lemma le_inf {A} r : A !=set0 -> lbound A r -> r <= inf A.
Proof. exact: le_inf. Qed.

Lemma ge_supP {A} x : has_ubound A -> sup A <= x <-> ubound A x.
Proof.
case: (eqVneq A set0) => [-> _|/set0P Ane ubA]; last by apply: ge_supP.
by rewrite sup0Ebot le0x; split=> // _.
Qed.

Lemma le_infP {A} x : A !=set0 -> x <= inf A <-> lbound A x.
Proof. by move=> ?; exact: le_infP. Qed.

Lemma gt_sup {A} x : has_ubound A -> sup A < x -> forall y, A y -> y < x.
Proof. exact: gt_sup. Qed.

Lemma lt_inf {A} x : x < inf A -> forall y, A y -> x < y.
Proof. exact: lt_inf. Qed.

Lemma sup_ub_strict {A} : has_ubound A ->
  ~ A (sup A) -> A `<=` [set r | r < sup A].
Proof. exact: sup_ub_strict. Qed.

Lemma inf_lb_strict {A} : 
  ~ A (inf A) -> A `<=` [set r | inf A < r].
Proof. exact: inf_lb_strict. Qed.

Lemma sup_le A B : has_ubound B -> A `<=` down B -> sup A <= sup B.
Proof.
by case: (eqVneq A set0) => [->|/set0P Ane]; 
  [ rewrite sup0Ebot | apply: sup_le ].
Qed.

Lemma inf_le A B : A !=set0 -> A `<=` up B -> inf B <= inf A.
Proof. by move=> ?; apply: inf_le. Qed.

Lemma supS {A B} : has_ubound B -> A `<=` B -> sup A <= sup B.
Proof.
by case: (eqVneq A set0) => [->|/set0P ? ? AB]; 
  [ rewrite sup0Ebot | apply: supS ].
Qed.

Lemma infS {A B} : A !=set0 -> A `<=` B -> inf B <= inf A.
Proof. by move=> ?; apply: infS. Qed.

Lemma sup_setU A B : has_sup B ->
  (forall a b, A a -> B b -> a <= b) -> sup (A `|` B) = sup B.
Proof. exact: sup_setU. Qed.

Lemma inf_setU A B : A !=set0 ->
  (forall a b, A a -> B b -> a <= b) -> inf (A `|` B) = inf A.
Proof. by move=> ?; apply: inf_setU. Qed.

Lemma lt_sup A r : has_ubound A ->
  (exists2 x, A x & r < x) -> r < sup A.
Proof. exact: lt_sup. Qed.

Lemma gt_inf A r :
  (exists2 x, A x & x < r) -> inf A < r.
Proof. exact: gt_inf. Qed.

Lemma sup_eq A r :
  ubound A r -> lbound (ubound A) r ->
  sup A = r.
Proof. exact: sup_eq. Qed.

Lemma inf_eq A r :
  lbound A r -> ubound (lbound A) r ->
  inf A = r.
Proof. exact: inf_eq. Qed.

Lemma sup_eq_sup A B :
  has_ubound A ->
  A `<=` down B -> B `<=` down A ->
  sup A = sup B.
Proof. exact: sup_eq_sup. Qed.

Lemma inf_eq_inf A B :
  A `<=` up B -> B `<=` up A ->
  inf A = inf B.
Proof. exact: inf_eq_inf. Qed.

Lemma sup_downE A : has_ubound A -> sup (down A) = sup A.
Proof. exact: sup_downE. Qed.

Lemma inf_upE A : inf (up A) = inf A.
Proof. exact: inf_upE. Qed.

Lemma sup1 (x : T) : sup [set x] = x.
Proof. exact: sup1. Qed.

Lemma inf1 (x : T) : inf [set x] = x.
Proof. exact: inf1. Qed.

Lemma sup_le_set (x : T) : sup [set y | y <= x] = x.
Proof. exact: sup_le_set. Qed.

Lemma inf_ge_set (x : T) : inf [set y | x <= y] = x.
Proof. exact: inf_ge_set. Qed.

Lemma sup_interchange X Y (A : set X) (B : set Y) (f : X -> Y -> T) :
  has_ubound [set f x y | x in A & y in B] ->
  sup [set sup [set f x y | y in B] | x in A]
    = sup [set sup [set f x y | x in A] | y in B].
Proof. exact: sup_interchange. Qed.

Lemma inf_interchange X Y (A : set X) (B : set Y) (f : X -> Y -> T) :
  inf [set inf [set f x y | y in B] | x in A]
    = inf [set inf [set f x y | x in A] | y in B].
Proof. exact: inf_interchange. Qed.

End dedekindBPOrder.
#[global] Hint Extern 0 (has_lbound _) => solve[apply: bot_has_lbound] : core.

Section dedekindBOrder.
Context {d} {T : dedekindBOrderType d}.
Implicit Types (A B : set T).

Import Order.TTheory.

Lemma lt_sup_ex A r :
  r < sup A -> exists2 y, A y & r < y.
Proof. 
by case: (eqVneq A set0) => [->|/set0P Ane];
  [ rewrite sup0Ebot ltx0 | exact: lt_sup_ex ].
Qed.

Lemma gt_inf_ex A r : A !=set0 ->
  inf A < r -> exists2 y, A y & y < r.
Proof. exact: gt_inf_ex. Qed.

Lemma lt_supP A r : has_ubound A ->
  r < sup A <-> exists2 y, A y & r < y.
Proof.
case: (eqVneq A set0) => [-> _|/set0P ? ?]; last by apply: lt_supP.
by rewrite sup0Ebot ltx0; split=> // - [].
Qed.

Lemma gt_infP A r : A !=set0 ->
  inf A < r <-> exists2 y, A y & y < r.
Proof. by move=> ?; exact: gt_infP. Qed.

Lemma gt_sup_eq A r : 
  ubound A r ->
  (forall x, x < r -> exists2 y, A y & x < y) -> 
  sup A = r.
Proof. exact: gt_sup_eq. Qed.

Lemma lt_inf_eq A r : 
  lbound A r ->
  (forall x, r < x -> exists2 y, A y & y < x) -> 
  inf A = r.
Proof. exact: lt_inf_eq. Qed.

Lemma sup_total {A} r : down A r \/ sup A <= r.
Proof.
by case: (eqVneq A set0) => [->|/set0P]
  ; [ rewrite sup0Ebot; right | exact: sup_total ].
Qed.

Lemma inf_total {A} r : A !=set0 -> up A r \/ r <= inf A.
Proof. exact: inf_total. Qed.

End dedekindBOrder.

End BOrder.

Module TBOrder.
Import TOrder.
Import BOrder.

Section dedekindTBPOrder.
Context {d} {T : dedekindTBPOrderType d}.
Implicit Types (A B : set T).

Import Order.LTheory.

Lemma ub_le_sup A : ubound A (sup A).
Proof. exact: ub_le_sup. Qed.

Lemma lb_ge_inf A : lbound A (inf A).
Proof. exact: lb_ge_inf. Qed.

Lemma sup_lub A : lbound (ubound A) (sup A).
Proof. exact: sup_lub. Qed.

Lemma inf_glb A : ubound (lbound A) (inf A).
Proof. exact: TOrder.inf_glb. Qed.

Lemma le_sup A r : down A r -> r <= sup A.
Proof. exact: le_sup. Qed.

Lemma ge_inf A r : up A r -> inf A <= r.
Proof. exact: ge_inf. Qed.

Lemma ge_sup {A} r : ubound A r -> sup A <= r.
Proof. exact: ge_sup. Qed.

Lemma le_inf {A} r : lbound A r -> r <= inf A.
Proof. exact: TOrder.le_inf. Qed.

Lemma ge_supP {A} x : sup A <= x <-> ubound A x.
Proof. exact: ge_supP. Qed.

Lemma le_infP {A} x : x <= inf A <-> lbound A x.
Proof. exact: TOrder.le_infP. Qed.

Lemma gt_sup {A} x : sup A < x -> forall y, A y -> y < x.
Proof. exact: gt_sup. Qed.

Lemma lt_inf {A} x : x < inf A -> forall y, A y -> x < y.
Proof. exact: lt_inf. Qed.

Lemma sup_ub_strict {A} : 
  ~ A (sup A) -> A `<=` [set r | r < sup A].
Proof. exact: sup_ub_strict. Qed.

Lemma inf_lb_strict {A} : 
  ~ A (inf A) -> A `<=` [set r | inf A < r].
Proof. exact: inf_lb_strict. Qed.

Lemma sup_le A B : A `<=` down B -> sup A <= sup B.
Proof. exact: sup_le. Qed.

Lemma inf_le A B : A `<=` up B -> inf B <= inf A.
Proof. exact: TOrder.inf_le. Qed.

Lemma supS {A B} : A `<=` B -> sup A <= sup B.
Proof. exact: supS. Qed.

Lemma infS {A B} : A `<=` B -> inf B <= inf A.
Proof. exact: TOrder.infS. Qed.

Lemma sup_setU A B : B !=set0 ->
  (forall a b, A a -> B b -> a <= b) -> sup (A `|` B) = sup B.
Proof. by move=> ?; apply: sup_setU. Qed.

Lemma inf_setU A B : A !=set0 ->
  (forall a b, A a -> B b -> a <= b) -> inf (A `|` B) = inf A.
Proof. by move=> ?; apply: inf_setU. Qed.

Lemma lt_sup A r :
  (exists2 x, A x & r < x) -> r < sup A.
Proof. exact: lt_sup. Qed.

Lemma gt_inf A r :
  (exists2 x, A x & x < r) -> inf A < r.
Proof. exact: gt_inf. Qed.

Lemma sup_eq A r :
  ubound A r -> lbound (ubound A) r ->
  sup A = r.
Proof. exact: sup_eq. Qed.

Lemma inf_eq A r :
  lbound A r -> ubound (lbound A) r ->
  inf A = r.
Proof. exact: inf_eq. Qed.

Lemma sup_eq_sup A B :
  A `<=` down B -> B `<=` down A ->
  sup A = sup B.
Proof. exact: sup_eq_sup. Qed.

Lemma inf_eq_inf A B :
  A `<=` up B -> B `<=` up A ->
  inf A = inf B.
Proof. exact: inf_eq_inf. Qed.

Lemma sup_downE A : sup (down A) = sup A.
Proof. exact: sup_downE. Qed.

Lemma inf_upE A : inf (up A) = inf A.
Proof. exact: inf_upE. Qed.

Lemma sup1 (x : T) : sup [set x] = x.
Proof. exact: sup1. Qed.

Lemma inf1 (x : T) : inf [set x] = x.
Proof. exact: inf1. Qed.

Lemma sup_le_set (x : T) : sup [set y | y <= x] = x.
Proof. exact: sup_le_set. Qed.

Lemma inf_ge_set (x : T) : inf [set y | x <= y] = x.
Proof. exact: inf_ge_set. Qed.

Lemma sup_interchange X Y (A : set X) (B : set Y) (f : X -> Y -> T) :
  sup [set sup [set f x y | y in B] | x in A]
    = sup [set sup [set f x y | x in A] | y in B].
Proof. exact: sup_interchange. Qed.

Lemma inf_interchange X Y (A : set X) (B : set Y) (f : X -> Y -> T) :
  inf [set inf [set f x y | y in B] | x in A]
    = inf [set inf [set f x y | x in A] | y in B].
Proof. exact: inf_interchange. Qed.

End dedekindTBPOrder.

Section dedekindTBOrder.
Context {d} {T : dedekindTBOrderType d}.
Implicit Types (A B : set T).

Import Order.TTheory.

Lemma lt_sup_ex A r :
  r < sup A -> exists2 y, A y & r < y.
Proof. exact: lt_sup_ex. Qed.

Lemma gt_inf_ex A r : 
  inf A < r -> exists2 y, A y & y < r.
Proof. exact: TOrder.gt_inf_ex. Qed.

Lemma lt_supP A r : 
  r < sup A <-> exists2 y, A y & r < y.
Proof. exact: lt_supP. Qed.

Lemma gt_infP A r : 
  inf A < r <-> exists2 y, A y & y < r.
Proof. exact: TOrder.gt_infP. Qed.

Lemma gt_sup_eq A r : 
  ubound A r ->
  (forall x, x < r -> exists2 y, A y & x < y) -> 
  sup A = r.
Proof. exact: gt_sup_eq. Qed.

Lemma lt_inf_eq A r : 
  lbound A r ->
  (forall x, r < x -> exists2 y, A y & y < x) -> 
  inf A = r.
Proof. exact: lt_inf_eq. Qed.

Lemma sup_total {A} r : down A r \/ sup A <= r.
Proof. exact: sup_total. Qed.

Lemma inf_total {A} r : up A r \/ r <= inf A.
Proof. exact: TOrder.inf_total. Qed.

End dedekindTBOrder.

End TBOrder.

End Dedekind.

HB.mixin Record POrder_hasSup d T & Order.POrder d T := {
  sup : set T -> T ;
  ub_le_sup_subproof : forall (A : set T), has_ubound A -> ubound A (sup A) ;
  sup_lub_subproof : forall (A : set T), 
    has_ubound A -> lbound (ubound A) !=set0 -> lbound (ubound A) (sup A)
}.
HB.builders Context d T & POrder_hasSup d T.

Let inf A := sup (lbound A).

Let lb_ge_inf_subproof A : has_lbound A -> lbound A (inf A).
Proof.
move=> lbA x Ax.
apply: sup_lub_subproof; first by exists x => ?; apply.
- case: lbA => [m mlb].
  by exists m => ?; apply.
- by move=> ?; apply.
Qed.

Let inf_glb_subproof A : 
  has_lbound A -> ubound (lbound A) !=set0 -> ubound (lbound A) (inf A).
Proof.
by move=> [m lbm] ublb m' lbm'; apply: ub_le_sup_subproof.
Qed.

HB.instance Definition _ := 
  POrder_isDedekindComplete.Build d T 
    ub_le_sup_subproof sup_lub_subproof 
    lb_ge_inf_subproof inf_glb_subproof.

HB.end.

HB.mixin Record POrder_hasInf d T & Order.POrder d T := {
  inf : set T -> T ;
  lb_ge_inf_subproof : forall (A : set T), has_lbound A -> lbound A (inf A) ;
  inf_glb_subproof : forall (A : set T), 
    has_lbound A -> ubound (lbound A) !=set0 -> ubound (lbound A) (inf A)
}.
HB.builders Context d T & POrder_hasInf d T.

Let sup A := inf (ubound A).

Let ub_le_sup_subproof A : has_ubound A -> ubound A (sup A).
Proof.
move=> ubA x Ax.
apply: inf_glb_subproof; first by exists x => ?; apply.
- case: ubA => [M mub].
  by exists M => ?; apply.
- by move=> ?; apply.
Qed.

Let sup_lub_subproof A : 
  has_ubound A -> lbound (ubound A) !=set0 -> lbound (ubound A) (sup A).
Proof.
by move=> [M ubM] lbb M' ubM'; apply: lb_ge_inf_subproof.
Qed.

HB.instance Definition _ := 
  POrder_isDedekindComplete.Build d T 
    ub_le_sup_subproof sup_lub_subproof 
    lb_ge_inf_subproof inf_glb_subproof.

HB.end.

Section nat_dedekind.

Let inf_nat (A : set nat) :=
  if pselect (exists n, mem A n) is left A_ex
  then ex_minn A_ex
  else 0.

Let lb_ge_inf_subproof A :
  has_lbound A -> lbound A (inf_nat A).
Proof.
move=> [/= m lbm] n An; rewrite /inf_nat. 
case: pselect => [a|/forallNP/(_ n) //].
by case: ex_minnP => k _; apply; rewrite inE.
Qed.

Let inf_glb_subproof A :
  has_lbound A -> ubound (lbound A) !=set0 -> ubound (lbound A) (inf_nat A).
Proof.
move=> lbA [/= M ublb] n lbn.
have [x /mem_set Ax] : A !=set0.
  apply/set0P/eqP => A0; move: A0 ublb => -> /(_ M.+1 ltac:(done)).
  by rewrite leEnat ltnn.
rewrite /inf_nat; case: pselect => [hk|/forallNP /(_ x) //].
by case: ex_minnP => m /set_mem + _; exact: lbn.
Qed.

HB.instance Definition _ := 
  POrder_hasInf.Build _ nat lb_ge_inf_subproof inf_glb_subproof.

Import Dedekind.BOrder.

Lemma nat_inf_min (A : set nat) : A !=set0 -> A (inf A).
Proof.
move=> [x /mem_set Ax]; rewrite /inf/= /inf_nat.
case: pselect => [hk|/forallNP /(_ x) //].
by case: ex_minnP => m /set_mem.
Qed.

Lemma nat_sup_max (A : set nat) : has_sup A -> A (sup A).
Proof.
move=> [[x /mem_set Ax] [M ubM]].
have ex_memA : exists n, mem A n by exists x.
have ub_memA i : mem A i -> (i <= M)%N by move=> /set_mem; exact: ubM.
pose n := ex_maxn ex_memA ub_memA.
have : A n by rewrite /n; case: ex_maxnP => ? /set_mem.
congr A; rewrite /n; case: ex_maxnP => i /set_mem Ai /= i_max.
apply/esym; apply: sup_eq => [+ /mem_set|]; first exact: i_max.
by move=> ?; apply.
Qed.

End nat_dedekind.

Section int_dedekind.
Implicit Types (A : set int).
Import intZmod intOrdered Order.TTheory Num.Def Num.Theory.

Local Open Scope int_scope.
Local Open Scope ring_scope.

Let inf_int A : int :=
  min (- (sup [set absz i | i in A `&` [set` Num.npos]])%:R)
    (inf [set absz i | i in A `&` [set` Num.nneg]] :> int).
Let sup_int A : int :=
  max (- (inf [set absz i | i in A `&` [set` Num.npos]])%:R)
    (sup [set absz i | i in A `&` [set` Num.nneg]] :> int).

Let ub_le_sup_subproof A : has_ubound A -> ubound A (sup_int A).
Proof.
move=> [/= M ubM] i Ai.
rewrite /sup_int le_max; apply/orP.
case: (EM (A `&` [set` Num.npos] !=set0)) => [[x [/= Ax xnp]]|].
- left; rewrite lerNr.

 






HB.howto nat dedekindBOrderType. 