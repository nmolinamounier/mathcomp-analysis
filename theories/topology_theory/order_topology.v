(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra finmap all_classical.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import topology_structure separation_axioms.
From mathcomp Require Import product_topology uniform_structure
  pseudometric_structure.

(**md**************************************************************************)
(* # Order topology                                                           *)
(*                                                                            *)
(* `POrderedNbhs`                                                             *)
(* : join of `Nbhs` and `isPOrder`                                            *)
(*                                                                            *)
(* `POrderedTopological`                                                      *)
(* : join of `Topological` and `isPOrder`                                     *)
(*                                                                            *)
(* `POrderedUniform`                                                          *)
(* : join of `Uniform` and `isPOrder`                                         *)
(*                                                                            *)
(* `POrderedPseudoMetric`                                                     *)
(* : join of `PseudoMetric` and `isPOrder`                                    *)
(*                                                                            *)
(* `POrderedPointedTopological`                                               *)
(* : join of `PointedTopological` and `isPOrder`                              *)
(*                                                                            *)
(* `orderTopologicalType`                                                     *)
(* : a topology built from intervals                                          *)
(*                                                                            *)
(* `order_topology T`                                                         *)
(* : the induced order topology on `T`                                        *)
(*                                                                            *)
(* `order_display T`                                                          *)
(* : display for `order_topology T`                                           *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.structure Definition POrderedNbhs td od :=
  { T of Nbhs td T & Order.isPOrder od T }.

HB.structure Definition POrderedTopological td od :=
  { T of Topological td T & Order.isPOrder od T }.

HB.structure Definition POrderedRegular td od :=
  { T of Regular td T & Order.isPOrder od T }.

HB.structure Definition POrderedUniform td od :=
  { T of Uniform td T & Order.isPOrder od T }.

HB.structure Definition POrderedPseudoMetric td od (R : numDomainType) :=
  {T of PseudoMetric td R T & Order.isPOrder od T}.

HB.structure Definition POrderedPointedTopological td od :=
  {T of PointedTopological td T & Order.isPOrder od T}.

(** TODO: generalize this to a preOrder once that's available *)
HB.mixin Record Order_isNbhs td od (T : Type) & Nbhs td T & Order.Total od T := {
  (** Note that just the intervals `]a, b[ doesn't work when the order has a
      top or bottom element, so we also need the rays `]-oo, b[ and ]a, +oo[ *)
  itv_nbhsE : forall x : T, nbhs x = filter_from
    (fun i => itv_open_ends i /\ x \in i)
    (fun i => [set` i])
}.

#[short(type="orderNbhsType")]
HB.structure Definition OrderNbhs td od :=
  { T of Nbhs td T & Order.Total od T & Order_isNbhs td od T }.

#[short(type="orderTopologicalType")]
HB.structure Definition OrderTopological td od :=
  { T of Hausdorff td T & Regular td T & Order.Total od T &
    Order_isNbhs td od T }.

#[short(type="orderUniformType")]
HB.structure Definition OrderUniform td od :=
  {T of Uniform td T & OrderTopological td od T}.

#[short(type="orderPseudoMetricType")]
HB.structure Definition OrderPseudoMetric td od (R : numDomainType) :=
  {T of PseudoMetric td R T & OrderTopological td od T}.

HB.factory Record Order_isTopological td od T
    & Topological td T & Order.Total od T := {
  itv_nbhsE : forall x : T, nbhs x = filter_from
    (fun i => itv_open_ends i /\ x \in i)
    (fun i => [set` i])
}.

HB.builders Context td od T & Order_isTopological td od T.

Local Open Scope order_scope.
Local Open Scope classical_set_scope.

Let order_hausdorffP : hausdorff_space T.
Proof.
move=> x y xy.
wlog xy : x y {xy} / x < y.
  move: xy => + hlt; rewrite neq_lt => /orP[xy|yx]; first by apply: hlt.
  have [B [A [Bn An]]] := hlt _ _ yx; rewrite disj_set_sym => dAB.
  by exists A, B.
case: (EM (exists2 z, x < z & z < y)) => [[/= z xz zy]|].
  exists `]-oo,z[, `]z,+oo[; split.
  - by rewrite itv_nbhsE /=; exists `]-oo,z[%O.
  - rewrite itv_nbhsE /=; exists `]z,+oo[%O => //; split=> //.
    by rewrite in_itv/= zy.
  - rewrite !set_itvE. 
    by apply/disj_setPLR => ? /lt_trans /[apply]; rewrite ltxx.
move/forallPNP => /= hgap.
exists `]-oo,y[, `]x,+oo[; split.
- by rewrite itv_nbhsE /=; exists `]-oo,y[%O.
- rewrite itv_nbhsE /=; exists `]x,+oo[%O => //; split=> //.
  by rewrite in_itv/= xy.
- by rewrite !set_itvE; apply/disj_setPLR => ? /= + /hgap.
Qed.

HB.instance Definition _ := Topological_isHausdorff.Build td T order_hausdorffP.

Let itv_basis : basis [set [set` i] | i in [set` @itv_open_ends _ T]].
Proof.
split.
  move=> _ [i iop <-]; rewrite openE => x /= xi.
  by rewrite /interior itv_nbhsE /=; exists i.
move=> /= x A; rewrite itv_nbhsE => -[/= i [iop xi siA]].
by exists [set` i] => //=; split=> //; exists i.
Qed.

Let open_ends_itv (i : interval T) :
  itv_open_ends i -> open [set` i].
Proof. by move=> oi; apply itv_basis; exists i. Qed.

Let open_itv (x y : T) : open `]x, y[.
Proof. exact: open_ends_itv. Qed.

Let open_rray (x : T) : open `]x, +oo[.
Proof. exact: open_ends_itv. Qed.

Let open_lray (x : T) : open `]-oo, x[.
Proof. exact: open_ends_itv. Qed.

Let closed_itv (x y : T) : closed `[x, y].
Proof. by rewrite -openC setCitv /=; apply: openU. Qed.

Let itv_closure (x y : T) (b b' : bool) :
  closure [set` Interval (BSide b x) (BSide b' y)] `<=` `[x, y].
Proof.
rewrite closureE => r; apply; split=> //.
by apply: subset_itvScc => /=; rewrite bnd_simp.
Qed.

Let closed_rray (x : T) : closed `[x, +oo[.
Proof. by rewrite -openC setCitvr. Qed.

Let closed_lray (x : T) : closed `]-oo, x].
Proof. by rewrite -openC setCitvl. Qed.

Let order_regularP : regular_space T.
Proof.
apply/closure_regularP => x U /[dup] -[oU Ux].
move/open_nbhs_nbhs; rewrite itv_nbhsE /=.
case=> [[a b] [op_ab xab] abU].
pose Il := [set` Interval a b] `&` [set y | y < x].
pose Ir := [set` Interval a b] `&` [set y | x < y].
case: (EM (Il !=set0)) (EM (Ir !=set0)) => /= [[u Ilu]|Il0] [[v Irv]|Ir0].
- case: Ilu Irv => [/= ui ux] [/= vi xv].
  exists `]u, v[.
    by split=> //=; rewrite in_itv /= ux xv.
  apply: subset_trans abU.
  apply: subset_trans; first exact: itv_closure.
  by move: ui vi => /andP[au _] /andP[_ vb]; apply: subset_itv.
- case: Ilu Ir0 => [/= uab ux] /nonemptyPn; rewrite -subset0 => Ir0.
  pose I := [set` Interval a b] `&` `]u,+oo[.
  have oI : open I by apply: openI => //; apply: open_ends_itv.
  exists I.
    by split=> //; rewrite /I set_itvE /=.
  have -> : I = `]u, x].
    rewrite /I !set_itvE; apply/seteqP; split=> z /=.
    + move=> [zi -> /=]; rewrite leNgt; apply/negP => xz.
      by apply: (Ir0 z).
    + move=> /andP[/[dup] uz -> zx]; split=> //.
      move: xab uab => /andP[_ xb] /andP[ua _].
      apply/andP; split.
      * by apply: (le_trans ua); rewrite bnd_simp ltW.
      * by apply: le_trans xb.
  apply: subset_trans; first exact: itv_closure.
  apply: subset_trans abU.
  by move: uab xab => /andP[au _] /andP[_ xb]; apply: subset_itv.
- case: Irv Il0 => [/= vab xv] /nonemptyPn; rewrite -subset0 => Il0.
  pose I := [set` Interval a b] `&` `]-oo,v[.
  have oI : open I by apply: openI => //; apply: open_ends_itv.
  exists I.
    by split=> //; rewrite /I set_itvE /=.
  have -> : I = `[x, v[.
    rewrite /I !set_itvE; apply/seteqP; split=> z /=.
    + move=> [zi ->]; rewrite andbT leNgt; apply/negP => zx.
      by apply: (Il0 z).
    + move=> /andP[xz /[dup] zv ->]; split=> //.
      move: xab vab => /andP[ax _] /andP[_ vb].
      apply/andP; split.
      * by apply: (le_trans ax).
      * by apply: le_trans vb; rewrite bnd_simp ltW.
  apply: subset_trans; first exact: itv_closure.
  apply: subset_trans abU.
  by move: xab vab => /andP[ax _] /andP[_ vb]; apply: subset_itv.
- suff ox : open [set x].
    exists [set x] => //.
    rewrite -(closure_id _).1; first exact: closed_set1.
    by rewrite sub1set inE.
  suff <- : [set` Interval a b] = [set x].
    by apply: open_ends_itv.
  apply/seteqP; split; last by rewrite sub1set inE.
  move=> /= y yab; apply: contrapT => /eqP.
  rewrite neq_lt => /orP[yx|xy].
  + by apply: Il0; exists y.
  + by apply: Ir0; exists y.
Qed.

HB.instance Definition _ :=
  Topological_isRegular.Build td T order_regularP.
HB.instance Definition _ :=
  Order_isNbhs.Build td od T itv_nbhsE.

HB.end.

Section order_topologies.
Local Open Scope order_scope.
Local Open Scope classical_set_scope.
Context {td od} {T : orderTopologicalType td od}.
Implicit Types x y : T.

Lemma rray_open x : @open _ T `]x, +oo[.
Proof.
rewrite openE /interior => z xoz; rewrite itv_nbhsE.
by exists `]x, +oo[%O => //; split => //; left.
Qed.
Hint Resolve rray_open : core.

Lemma lray_open x : @open _ T `]-oo, x[.
Proof.
rewrite openE /interior => z xoz; rewrite itv_nbhsE.
by exists (`]-oo, x[)%O => //; split => //; left.
Qed.
Hint Resolve lray_open : core.

Lemma itv_open x y : @open _ T `]x, y[.
Proof. by rewrite set_itv_splitI /=; apply: openI. Qed.
Hint Resolve itv_open : core.

Lemma itv_open_ends_open (i : interval T) : itv_open_ends i -> open [set` i].
Proof.
case: i; rewrite /itv_open_ends => [[[]t1|[]]] [[]t2|[]]// ?.
by rewrite set_itvE; exact: openT.
Qed.

Lemma rray_closed x : @closed _ T `[x, +oo[.
Proof. by rewrite -setCitvl closedC. Qed.
Hint Resolve rray_closed : core.

Lemma lray_closed x : @closed _ T `]-oo, x].
Proof. by rewrite -setCitvr closedC. Qed.
Hint Resolve lray_closed : core.

Lemma itv_closed x y : @closed _ T `[x, y].
Proof. by rewrite set_itv_splitI; apply: closedI => /=. Qed.
Hint Resolve itv_closed : core.

Lemma itv_closed_ends_closed (i : interval T) :
  itv_closed_ends i -> closed [set` i].
Proof. by case: i => [[[]t1|[]]] [[]t2|[]]. Qed.

Lemma itv_closure x y : closure `]x, y[ `<=` `[x, y].
Proof.
rewrite closureE => r; apply; split => //.
by apply: subset_itvScc => /=; rewrite bnd_simp.
Qed.

Lemma itv_closed_infimums (A : set T) : A !=set0 -> closed A ->
  infimums A `<=` A.
Proof.
move=> [a0 Aa0] + l [loL] hiL; rewrite closure_id => -> => U.
rewrite itv_nbhsE => -[[p q []]].
have [E|E] := eqVneq ([set` Interval (BSide true l) q] `&` A) set0; last first.
  case/set0P: E => a [lqa ?] ? lpq pqU; exists a; split => //.
  apply: pqU; move: lpq lqa; rewrite /= ?inE => lpq /le_trans; apply.
  by move: lpq => /andP [? ?]; exact/andP.
case: q E.
- move=> b q /[swap] /itv_open_ends_rside -> E lpq ; suff : lbound A q.
    move/hiL => + _; rewrite leNgt; apply: contraNP => _.
    by move: lpq; rewrite in_itv => /andP [].
  move=> a Aa; have : (~` (`[l, q[ `&` A)) a by rewrite E.
  rewrite setCI => -[|//]; rewrite setCitv /= ?in_itv/= ?andbT => -[|//].
  by rewrite ltNge (loL _ Aa).
- move=> b _ /itv_open_ends_rinfty -> lpo poU; exists a0; split => //.
  apply: poU; move: lpo; rewrite /= ?itv_boundlr /= => /andP[pl _]; apply/andP.
  by split => //; exact/(le_trans pl)/loL.
Qed.

Lemma itv_closed_supremums (A : set T) : A !=set0 -> closed A ->
  supremums A `<=` A.
Proof.
move=> [a0 Aa0] + l [upL] lbL; rewrite closure_id => -> => U.
rewrite itv_nbhsE => -[[p q[]]].
have [E|E] := eqVneq ([set` Interval p (BSide false l)] `&` A) set0; last first.
  case/set0P: E => a [lqa ?] ? lpq pqU; exists a; split => //.
  apply: pqU; move: lpq lqa; rewrite /= ?inE => lpq /le_trans; apply.
  by move: lpq => /andP [? ?]; exact/andP.
case: p E.
- move=> b p /[swap] /itv_open_ends_lside -> E lpq ; suff : ubound A p.
    move/lbL => + _; rewrite leNgt; apply: contraNP => _.
    by move: lpq; rewrite in_itv => /andP [].
  move=> a Aa; have : (~` (`]p, l] `&` A)) a by rewrite E.
  rewrite setCI => -[|//]; rewrite setCitv /= ?in_itv/= ?andbT => -[//|].
  by rewrite ltNge (upL _ Aa).
- move=> b _ /itv_open_ends_linfty -> lpo poU; exists a0; split => //.
  apply: poU; move: lpo; rewrite /= ?itv_boundrl /= => /andP[_ pl]; apply/andP.
  by split => //; exact/(le_trans _ pl)/upL.
Qed.

Let sub_open_mem x (U : set T) (i : interval T) :=
  [/\ [set` i] `<=` U, open [set` i] & x \in i].

Lemma clopen_bigcup_clopen x (U : set T) : clopen U -> U x ->
  clopen (\bigcup_(i in sub_open_mem x U) [set` i]).
Proof.
pose I := \bigcup_(i in sub_open_mem x U) [set` i].
move=> clU Ux; split; first by apply: bigcup_open => ? [].
have cIV : closure I `<=` U.
  rewrite closureE => z /(_ U); apply; split; first by case: clU.
  by move=> ? [? [+ _ _]]; exact.
apply/closure_id; rewrite eqEsubset; split; first exact: subset_closure.
move=> z cIi; have Uz : U z by exact: cIV.
case: clU => + _;  rewrite {1}openE => /(_ _ Uz).
rewrite /interior /= itv_nbhsE /= => -[i [/itv_open_ends_open oi iy] siU].
case/(_ [set` i]): cIi; first by move: oi; rewrite openE; exact.
move=> /= w [[j [jU oJ jy jw]]] wi; exists (i `|` j)%O; first last.
  exact/(le_trans iy)/leUl.
split; first by rewrite itv_setU ?{1}subUset //; exists w.
by rewrite itv_setU ?{1}subUset //; [exists w | exact: openU].
exact/(le_trans jy)/leUr.
Qed.

End order_topologies.
Hint Resolve lray_open : core.
Hint Resolve rray_open : core.
Hint Resolve itv_open : core.
Hint Resolve lray_closed : core.
Hint Resolve rray_closed : core.
Hint Resolve itv_closed : core.

Definition order_topology (T : Type) : Type := T.

Fact order_display (T : Type) : filter_display.
Proof. by []. Qed.

Section induced_order_topology.

Context {od} {T : orderType od}.

Local Notation oT := (order_topology T).

HB.instance Definition _ := isPointed.Build (interval T) (`]-oo,+oo[).

HB.instance Definition _ := Order.Total.on oT.
HB.instance Definition _ := @isSubBaseTopological.Build
  (order_display T) oT (interval T) (itv_is_open_unbounded) (fun i => [set` i]).

Lemma order_nbhs_itv (x : oT) : nbhs x = filter_from
    (fun i => itv_open_ends i /\ x \in i)
    (fun i => [set` i]).
Proof.
rewrite eqEsubset; split => U; first last.
  case=> /= i [ro xi /filterS]; apply; move: ro => /orP [rayi|].
    exists [set` i]; split => //=.
    exists [set [set` i]]; last by rewrite bigcup_set1.
    move=> A ->; exists (fset1 i); last by rewrite set_fset1 bigcap_set1.
    by move=> ?; rewrite !inE => /eqP ->.
  case: i xi => [][[]l|[]] [[]r|[]] xlr//= ?; exists `]l, r[%classic.
  split => //; exists [set `]l, r[%classic]; last by rewrite bigcup_set1.
  move=> ? ->; exists [fset `]-oo, r[ ; `]l, +oo[]%fset.
    by move=> ?; rewrite !inE => /orP[] /eqP ->.
  rewrite set_fsetU !set_fset1 bigcap_setU !bigcap_set1.
  by rewrite (@set_itv_splitI _ _ `]l, r[) /= setIC.
case=> ? [[ I Irp] <-] [?] /[dup] /(Irp _) [F rayF <-] IF Fix IU.
pose j := \big[Order.meet/`]-oo, +oo[]_(i <- F) i.
exists j; first split.
- rewrite /j (@eq_fbig_cond _ _ _ _ _ F _ (mem F) _ id)//.
    by move=> p /=; rewrite !inE/=; exact: andb_id2l.
  apply: (big_ind itv_open_ends) => //=; first exact: itv_open_endsI.
  by rewrite /itv_open_ends; move=> i /rayF /set_mem ->.
- pose f (i : interval T) : Prop := x \in i; suff : f j by [].
  rewrite /j (@eq_fbig_cond _ _ _ _ _ F _ (mem F) _ id)//=.
  + by move=> p /=; rewrite !inE/=; exact: andb_id2l.
  + by apply: big_ind => //=; rewrite /f /= => a ? xa ?; rewrite in_itvI xa.
- suff -> : [set` j] = \bigcap_(i in [set` F]) [set` i].
    by move=> i Fi; apply: IU; exists (\bigcap_(i in [set` F]) [set` i]).
  rewrite -bigsetI_fset_set ?set_fsetK//.
  pose f (i : interval T) (j : set T) : Prop := [set` i] = j.
  suff : f j (\big[setI/[set: T]]_(i <- F) [set` i]) by [].
  rewrite /j big_mkcond /=; apply: big_ind2; rewrite /f ?set_itvE//.
  by move=> ? ? ? ? <- <-; rewrite itv_setI.
Qed.

HB.instance Definition _ := Order_isTopological.Build _ _ oT order_nbhs_itv.
End induced_order_topology.

Lemma min_continuous {td od} {T : orderTopologicalType td od} :
  continuous (fun xy : T * T => Order.min xy.1 xy.2).
Proof.
case=> x y; have [<- U /=|]:= eqVneq x y.
  rewrite min_l// => Ux; exists (U, U) => //= -[a b [Ua Ub]].
  by have /orP[?|?]/= := le_total a b; [rewrite min_l|rewrite min_r].
wlog xy : x y / (x < y)%O.
  move=> WH /[dup] /lt_total/orP[|yx /eqP/nesym/eqP yNx]; first exact: WH.
  rewrite (_ : (fun _ => _)
      = (fun xy => Order.min xy.1 xy.2) \o @swap T T); last first.
    by apply: continuous_comp; [exact: swap_continuous|exact: WH].
  apply/funext => -[a b/=]; have /orP[ab|ba] := le_total a b.
  - by rewrite min_l // min_r.
  - by rewrite min_r // min_l.
move=> _ U /=; rewrite (min_l (ltW xy)) => Ux.
have [[z xzy]|/forallNP/= xNy] := pselect (exists z, x < z < y)%O.
  exists (U `&` `]-oo, z[, `]z, +oo[%classic) => /=.
    split; [apply: filterI =>//|]; apply: open_nbhs_nbhs.
    - by split; [exact: lray_open|rewrite set_itvE; case/andP: xzy].
    - by split; [exact: rray_open|rewrite set_itvE; case/andP: xzy].
  case=> a b /= [[Ua]]; rewrite !in_itv andbT /= => az zb.
  by rewrite min_l// (ltW (lt_trans az _)).
exists (U `&` `]-oo, y[, `]x, +oo[%classic) => /=.
  split; [apply: filterI => //|]; apply: open_nbhs_nbhs.
  - by split; [exact: lray_open|rewrite set_itvE].
  - by split; [exact: rray_open|rewrite set_itvE].
case=> a b /= [[Ua]]; rewrite !in_itv andbT /= => ay xb.
rewrite min_l// leNgt; apply: contra_notN (xNy b) => ba.
by rewrite xb (lt_trans ba).
Qed.

Lemma min_fun_continuous {td} {X : topologicalType td}
  {od} {T : orderTopologicalType td od} (f g : X -> T) :
  continuous f -> continuous g -> continuous (f \min g).
Proof.
move=> fc gc z; apply: continuous2_cvg; [|exact: fc|exact: gc].
by apply min_continuous.
Qed.

Lemma max_continuous {td od} {T : orderTopologicalType td od} :
  continuous (fun xy : T * T => Order.max xy.1 xy.2).
Proof.
case=> x y; have [<- U|] := eqVneq x y.
  rewrite /= max_r // => ux; exists (U, U) => //= -[a b] [/= Ua Ub].
  by have /orP[?|?]/= := le_total a b; [rewrite max_r|rewrite max_l].
wlog xy : x y / (x < y)%O.
  move=> WH /[dup] /lt_total/orP[|yx /eqP/nesym/eqP yNx]; first exact: WH.
  rewrite (_ : (fun _ => _)
      = (fun xy => Order.max xy.1 xy.2) \o @swap T T); last first.
    by apply: continuous_comp; [exact: swap_continuous|exact: WH].
  apply/funext => -[a b] /=; have /orP [ab|ba] := le_total a b.
  - by rewrite max_r // max_l.
  - by rewrite max_l // max_r.
move=> _ U /=; rewrite (max_r (ltW xy)) => Ux.
have [[z xzy]|/forallNP /= xNy] := pselect (exists z, x < z < y)%O.
  exists (`]-oo, z[%classic, U `&` `]z, +oo[) => /=.
    split; [|apply: filterI =>//]; apply: open_nbhs_nbhs.
    - by split; [exact: lray_open|rewrite set_itvE; case/andP: xzy].
    - by split; [exact: rray_open|rewrite set_itvE; case/andP: xzy].
  case=> a b /= [] + []; rewrite !in_itv andbT /= => az Ub zb.
  by rewrite (max_r (ltW (lt_trans az _))).
exists (`]-oo, y[%classic, U `&` `]x, +oo[) => /=.
  split; [|apply: filterI => //]; apply: open_nbhs_nbhs.
  - by split; [exact: lray_open|rewrite set_itvE].
  - by split; [exact: rray_open|rewrite set_itvE].
case=> a b /=; rewrite !in_itv /= andbT => [/=] [ay] [Ub] xb.
rewrite max_r// leNgt; apply: contra_notN (xNy b) => ba.
by rewrite xb (lt_trans ba).
Qed.

Lemma max_fun_continuous {td} {X : topologicalType td}
  {od} {T : orderTopologicalType td od} (f g : X -> T) :
  continuous f -> continuous g -> continuous (f \max g).
Proof.
move=> fc gc z; apply: continuous2_cvg; [|exact: fc|exact: gc].
by apply max_continuous.
Qed.
