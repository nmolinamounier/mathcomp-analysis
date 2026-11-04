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
  sup_ubound_subproof : forall (A : set T), has_sup A -> ubound A (sup A) ;
  sup_lub_subproof : forall (A : set T), 
    has_sup A -> lbound (ubound A) (sup A) ;
  inf_lbound_subproof : forall (A : set T), has_inf A -> lbound A (inf A) ;
  inf_glb_subproof : forall (A : set T), 
    has_inf A -> ubound (lbound A) (inf A) ;
}.

#[short(type="dedekindPOrderType")]
HB.structure Definition DedekindPOrder d := 
  {T of Order.POrder d T & POrder_isDedekindComplete d T}.

HB.mixin Record DedekindPOrder_isDedekindTPOrder d T 
    & DedekindPOrder d T & Order.TPOrder d T := {
  inf0_top_subproof : inf set0 = \top%O :> T
}.
HB.mixin Record DedekindPOrder_isDedekindBPOrder d T 
    & DedekindPOrder d T & Order.BPOrder d T := {
  sup0_bot_subproof : sup set0 = \bot%O :> T
}.

HB.mixin Record DedekindPOrder_ZeroSupInf0 T 
    & DedekindPOrder _ T & Num.POrderNmodule T := {
  sup0_subproof : forall A, ~ has_inf A -> sup A = 0%R :> T ;
  inf0_subproof : forall A, ~ has_inf A -> inf A = 0%R :> T;
}.

#[short(type="dedekindTPOrderType")]
HB.structure Definition DedekindTPOrder d :=
  {T of Order.TPOrder d T & DedekindPOrder d T 
    & DedekindPOrder_isDedekindTPOrder d T}.
#[short(type="dedekindBPOrderType")]
HB.structure Definition DedekindBPOrder d :=
  {T of Order.BPOrder d T & DedekindPOrder d T 
    & DedekindPOrder_isDedekindBPOrder d T}.
#[short(type="dedekindTBPOrderType")]
HB.structure Definition DedekindTBPOrder d :=
  {T of DedekindBPOrder d T & DedekindTPOrder d T}.

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

Module Order.

Module LTheory.
Export Order.LTheory.

Section dedekindPOrder.
Context {d} {T : dedekindPOrderType d}.
Implicit Types (A B : set T).

Lemma ub_le_sup A : has_ubound A -> ubound A (sup A).
Proof.
move=> ubE; apply/ubP => x Ex; move: (x) (Ex).
by apply/ubP/sup_ubound_subproof => //; split; first by exists x.
Qed.

#[deprecated(since="analysis 1.20.0", use=ub_le_sup)]
Lemma sup_upper_bound A : has_sup A -> ubound A (sup A).
Proof. exact: sup_ubound_subproof. Qed.

Lemma lb_ge_inf A : has_lbound A -> lbound A (inf A).
Proof.
move=> lbE; apply/lbP => x Ex; move: (x) (Ex).
by apply/lbP/inf_lbound_subproof => //; split; first by exists x.
Qed.

Lemma le_sup A r : has_ubound A -> down A r -> r <= sup A.
Proof. by move=> ubA [x [Ax /le_trans]]; apply; apply: ub_le_sup. Qed.

Lemma ge_inf A r : has_lbound A -> up A r -> inf A <= r.
Proof. by move=> lbA [x [Ax]]; apply: le_trans; apply: lb_ge_inf. Qed.

Lemma ge_sup {A} r : A !=set0 -> ubound A r -> sup A <= r.
Proof.
move=> Ane ubr.
by apply: sup_lub_subproof => //; split=> //; exists r.
Qed.

Lemma le_inf {A} r : A !=set0 -> lbound A r -> r <= inf A.
Proof.
move=> Ane lbr.
by apply: inf_glb_subproof => //; split=> //; exists r.
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

Lemma eq_sup_sup A B : 
  has_sup A ->
  A `<=` down B -> B `<=` down A ->
  sup A = sup B.
Proof.
move=> [Ane Aub] AdB BdA.
have Bne : B !=set0.
  by case: Ane => x /AdB[b [? _]]; exists b.
have Bub : has_ubound B.
  case: Aub => M ubM; exists M => x.
  by case/BdA => a [/ubM /[swap]]; exact: le_trans.
by apply/le_anti/andP; split; apply: sup_le.
Qed.

Lemma eq_inf_inf A B :
  has_inf A ->
  A `<=` up B -> B `<=` up A ->
  inf A = inf B.
Proof.
move=> [Ane Alb] AuB BuA.
have Bne : B !=set0.
  by case: Ane => x /AuB[b [? _]]; exists b.
have Bub : has_lbound B.
  case: Alb => M ubM; exists M => x.
  by case/BuA => a [/ubM]; exact: le_trans.
by apply/le_anti/andP; split; apply: inf_le.
Qed.

Lemma sup_downE A : has_sup A -> sup (down A) = sup A.
Proof.
by move=> ubA; apply: eq_sup_sup => //; [ apply/has_sup_down | rewrite downK ].
Qed.

Lemma inf_upE A : has_inf A -> inf (up A) = inf A.
Proof.
by move=> ubA; apply: eq_inf_inf => //; [ apply/has_inf_up | rewrite upK ].
Qed.

Lemma sup1 (x : T) : sup [set x] = x.
Proof.
apply/le_anti/andP; split.
- by apply: ge_sup => [|_ -> //]; exists x.
- by apply: ub_le_sup => //; exists x => _ ->.
Qed.

Lemma inf1 (x : T) : inf [set x] = x.
Proof.
apply/le_anti/andP; split.
- by apply: lb_ge_inf => //; exists x => _ ->.
- by apply: le_inf => [|_ -> //]; exists x.
Qed.

Lemma sup_le_set (x : T) : sup [set y | y <= x] = x.
Proof.
suff -> : [set y | y <= x] = down [set x].
  rewrite sup_downE ?sup1//.
  split; first by exists x.
  by exists x => _ ->.
rewrite predeqP => y /=; split; first by exists x.
by move=> [? [->]].
Qed.

Lemma inf_ge_set (x : T) : inf [set y | x <= y] = x.
Proof.
suff -> : [set y | x <= y] = up [set x].
  rewrite inf_upE ?inf1//.
  split; first by exists x.
  by exists x => _ ->.
rewrite predeqP => y /=; split; first by exists x.
by move=> [? [->]].
Qed.

End dedekindPOrder.

Section dedekindTPOrder.
Context {d} {T : dedekindTPOrderType d}.
Implicit Types (A B : set T).

Lemma top_has_ubound A : has_ubound A.
Proof. by exists \top. Qed.
#[local] Hint Resolve top_has_ubound : core.

Lemma top_has_sup A : A !=set0 -> has_sup A.
Proof. by []. Qed.

Lemma inf0_top : inf set0 = \top :> T.
Proof. exact: inf0_top_subproof. Qed. 

Lemma top_le_inf {A} r : lbound A r -> r <= inf A.
Proof.
case: (eqVneq A set0) => [->|]; first by rewrite inf0_top.
by move/set0P; exact: le_inf.
Qed.

Lemma sup_ge_set (x : T) : sup [set y | x <= y] = \top.
Proof. by apply/eqP; rewrite -le1x; apply: ub_le_sup => /=. Qed.

End dedekindTPOrder.

Section dedekindBPOrder.
Context {d} {T : dedekindBPOrderType d}.
Implicit Types (A B : set T).

Lemma bot_has_lbound A : has_lbound A.
Proof. by exists \bot. Qed.
#[local] Hint Resolve bot_has_lbound : core.

Lemma bot_has_inf A : A !=set0 -> has_inf A.
Proof. by []. Qed.

Lemma sup0_bot : sup set0 = \bot :> T.
Proof. exact: sup0_bot_subproof. Qed. 

Lemma bot_ge_sup {A} r : ubound A r -> sup A <= r.
Proof.
case: (eqVneq A set0) => [->|]; first by rewrite sup0_bot.
by move/set0P; exact: ge_sup.
Qed.

Lemma inf_le_set (x : T) : inf [set y | y <= x] = \bot.
Proof. by apply/eqP; rewrite -lex0; apply: lb_ge_inf => /=. Qed.

End dedekindBPOrder.

Section dedekindTBPOrder.
Context {d} {T : dedekindTBPOrderType d}.
Implicit Types (A B : set T).


End dedekindTBPOrder.

End LTheory.

Module Theory.
Export Order.TTheory.
Export LTheory.

Section dedekindOrder.
Context {d} {T : dedekindOrderType d}.
Implicit Types (A B : set T).

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

Lemma sup_eq A r : A !=set0 -> ubound A r ->
  (forall x, x < r -> exists2 y, A y & x < y) -> 
  sup A = r.
Proof.
move=> Ane ubAr adhA.
apply/le_anti/andP; split; first by apply: ge_sup.
apply/le_gtP => /= x /adhA[y Ay] /lt_le_trans; apply.
by apply: ub_le_sup => //; exists r.
Qed.

Lemma inf_eq A r : A !=set0 -> lbound A r ->
  (forall x, r < x -> exists2 y, A y & y < x) -> 
  inf A = r.
Proof.
move=> Ane lbAr adhA.
apply/le_anti/andP; split; last by apply: le_inf.
apply/le_ltP => /= x /adhA[y Ay +]; apply: le_lt_trans.
by apply: lb_ge_inf => //; exists r.
Qed.

End dedekindOrder.

Section dedekindTOrder.
Context {d} {T : dedekindTOrderType d}.
Implicit Types (A B : set T).

End dedekindTOrder.

Section dedekindBOrder.
Context {d} {T : dedekindBOrderType d}.
Implicit Types (A B : set T).

End dedekindBOrder.

End Theory.

End Order.