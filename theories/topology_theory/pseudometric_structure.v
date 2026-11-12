(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra archimedean all_classical.
From mathcomp Require Import interval_inference reals topology_structure.
From mathcomp Require Import uniform_structure compact.

(**md**************************************************************************)
(* # PseudoMetric Spaces                                                      *)
(* This file provides pseudometric spaces, complete pseudometric spaces,      *)
(* and the corresponding theory. Note that a classic metric space is simply   *)
(* pseudometric + hausdorff. However we will make extensive use of the        *)
(* non-hausdorff case, such as in our proof of Urysohn's lemma.               *)
(*                                                                            *)
(* ## Mathematical structures                                                 *)
(* ### PseudoMetrics                                                          *)
(* ```                                                                        *)
(*                entourage_ ball == entourages defined using balls           *)
(*               pseudoMetricType == interface type for pseudo metric space   *)
(*                                   structure: a type equipped with balls    *)
(*                                   The HB class is PseudoMetric.            *)
(*              pseudoPMetricType == a pointed pseudoMetric space             *)
(*                       ball x e == ball of center x and radius e            *)
(*                nbhs_ball_ ball == nbhs defined using the given balls       *)
(*                      nbhs_ball == nbhs defined using balls in a            *)
(*                                   pseudometric space                       *)
(* ```                                                                        *)
(* ### Factories                                                              *)
(* ```                                                                        *)
(*            Nbhs_isPseudoMetric == factory to build a topological space     *)
(*                                   from a mixin for a pseudoMetric space    *)
(* ```                                                                        *)
(* ### Complete Pseudometrics                                                 *)
(* ```                                                                        *)
(*                        ball_ N == balls defined by the norm/absolute       *)
(*                                   value N                                  *)
(*       completePseudoMetricType == interface type for a complete            *)
(*                                   pseudometric space structure             *)
(*                                   The HB class is CompletePseudoMetric.    *)
(*                   cauchy_ex F <-> the set of sets F is a cauchy filter     *)
(*                                   (epsilon-delta definition)               *)
(*                 cauchy_ball F <-> the set of sets F is a cauchy filter     *)
(*                                   (using the near notations)               *)
(* ```                                                                        *)
(* ## Closed balls                                                            *)
(* ```                                                                        *)
(*             closed_ball_ norm x e := [set y | norm (x - y) <= e]           *)
(*                       closed_ball == closure of a ball                     *)
(* ```                                                                        *)
(* ## metrizability for uniform spaces                                        *)
(* ```                                                                        *)
(*  countable_uniform.type == endows a pseudoMetric on a uniform type whose   *)
(*                            entourage has a countable basis                 *)
(*        sup_pseudometric == the pseudometric induced for the supremum       *)
(*                            of countably many pseudoMetrics                 *)
(*                 gauge E == for an entourage E, gauge E is a filter which   *)
(*                            includes `iter n split_ent E`.                  *)
(*                            Critically, `gauge E` forms a uniform space     *)
(*                            with a countable uniformity.                    *)
(* ```                                                                        *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Making sure that [Program] does not automatically introduce *)
#[local]
Obligation Tactic := idtac.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition entourage_ {R : numDomainType} {T T'} (ball : T -> R -> set T') :=
  @filter_from R _ [set x | 0 < x] (fun e => [set xy | ball xy.1 e xy.2]).

Lemma entourage_E {R : numDomainType} {T T'} (ball : T -> R -> set T') :
  entourage_ ball =
  @filter_from R _ [set x | 0 < x] (fun e => [set xy | ball xy.1 e xy.2]).
Proof. by []. Qed.

HB.mixin Record Uniform_isPseudoMetric (R : numDomainType) M & Uniform M := {
  ball : M -> R -> M -> Prop ;
  ball_center_subproof : forall x (e : R), 0 < e -> ball x e x ;
  ball_sym_subproof : forall x y (e : R), ball x e y -> ball y e x ;
  ball_triangle_subproof :
    forall x y z e1 e2, ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z;
  entourageE_subproof : entourage = entourage_ ball
}.

#[short(type="pseudoMetricType")]
HB.structure Definition PseudoMetric (R : numDomainType) :=
  {T of Uniform T & Uniform_isPseudoMetric R T}.

#[short(type="pseudoPMetricType")]
HB.structure Definition PseudoPointedMetric (R : numDomainType) :=
  {T of Pointed T & Uniform T & Uniform_isPseudoMetric R T}.

(* was uniformityOfBallMixin *)
HB.factory Record Nbhs_isPseudoMetric (R : numFieldType) M & Nbhs M := {
  ent : set_system (M * M);
  nbhsE : nbhs = nbhs_ ent;
  ball : M -> R -> M -> Prop ;
  ball_center : forall x (e : R), 0 < e -> ball x e x ;
  ball_sym : forall x y (e : R), ball x e y -> ball y e x ;
  ball_triangle :
    forall x y z e1 e2, ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z;
  entourageE : ent = entourage_ ball
}.

HB.builders Context R M & Nbhs_isPseudoMetric R M.
Local Open Scope relation_scope.

Let ball_le x : {homo ball x : e1 e2 / e1 <= e2 >-> e1 `<=` e2}.
Proof.
move=> e1 e2 le12 y xe1_y.
move: le12; rewrite le_eqVlt => /orP [/eqP <- //|].
rewrite -subr_gt0 => lt12.
rewrite -[e2](subrK e1); apply: ball_triangle xe1_y.
suff : ball x (PosNum lt12)%:num x by [].
exact: ball_center.
Qed.

Let entourage_filter_subproof : Filter ent.
Proof.
rewrite entourageE; apply: filter_from_filter; first by exists 1 => /=.
move=> _ _ /posnumP[e1] /posnumP[e2]; exists (Num.min e1 e2)%:num => //=.
by rewrite subsetI; split=> ?; apply: ball_le;
   rewrite num_le// ge_min lexx ?orbT.
Qed.

Let ball_sym_subproof A : ent A -> diagonal `<=` A.
Proof.
rewrite entourageE; move=> [e egt0 sbeA] xy xey.
by apply: sbeA; rewrite /= xey; exact: ball_center.
Qed.

Let ball_triangle_subproof A : ent A -> ent A^-1.
Proof.
rewrite entourageE => - [e egt0 sbeA].
by exists e => // xy xye; apply: sbeA; exact: ball_sym.
Qed.

Let entourageE_subproof A : ent A -> exists2 B, ent B & B \; B `<=` A.
Proof.
rewrite entourageE; move=> [_/posnumP[e] sbeA].
exists [set xy | ball xy.1 (e%:num / 2) xy.2].
  by exists (e%:num / 2) => /=.
move=> xy [z xzhe zyhe]; apply: sbeA.
by rewrite [e%:num]splitr; exact: ball_triangle zyhe.
Qed.

HB.instance Definition _ := Nbhs_isUniform.Build M
  entourage_filter_subproof ball_sym_subproof ball_triangle_subproof
  entourageE_subproof nbhsE.

HB.instance Definition _ := Uniform_isPseudoMetric.Build R M
  ball_center ball_sym ball_triangle entourageE.

HB.end.

Lemma entourage_ballE {R : numDomainType} {M : pseudoMetricType R} :
  entourage_ (@ball R M) = entourage.
Proof. by rewrite entourageE_subproof. Qed.

Lemma entourage_from_ballE {R : numDomainType} {M : pseudoMetricType R} :
  @filter_from R _ [set x : R | 0 < x]
    (fun e => [set xy | @ball R M xy.1 e xy.2]) = entourage.
Proof. by rewrite -entourage_ballE. Qed.

Lemma entourage_ball {R : numDomainType} (M : pseudoMetricType R)
  (e : {posnum R}) : entourage [set xy : M * M | ball xy.1 e%:num xy.2].
Proof. by rewrite -entourage_ballE; exists e%:num => /=. Qed.
#[global] Hint Resolve entourage_ball : core.

Definition nbhs_ball_ {R : numDomainType} {T T'} (ball : T -> R -> set T')
  (x : T) := @filter_from R _ [set e | e > 0] (ball x).

Definition nbhs_ball {R : numDomainType} {M : pseudoMetricType R} :=
  nbhs_ball_ (@ball R M).

Lemma nbhs_ballE {R : numDomainType} {M : pseudoMetricType R} :
  @nbhs_ball R M = nbhs.
Proof.
rewrite predeq2E => x P; rewrite -nbhs_entourageE; split.
  move=> [_/posnumP[e] sbxeP]; exists [set xy | ball xy.1 e%:num xy.2] => //.
  by move=> y /xsectionP/sbxeP.
rewrite -entourage_ballE; move=> [A [e egt0 sbeA] sAP].
by exists e => // ? ?; exact/sAP/xsectionP/sbeA.
Qed.

Lemma filter_from_ballE {R : numDomainType} {M : pseudoMetricType R} x :
  @filter_from R _ [set x : R | 0 < x] (@ball R M x) = nbhs x.
Proof. by rewrite -nbhs_ballE. Qed.

Module Export NbhsBall.
Definition nbhs_simpl := (nbhs_simpl,@filter_from_ballE,@nbhs_ballE).
End NbhsBall.

Lemma nbhs_ballP {R : numDomainType} {M : pseudoMetricType R} (x : M) P :
  nbhs x P <-> nbhs_ball x P.
Proof. by rewrite nbhs_simpl. Qed.

Lemma ball_center {R : numDomainType} (M : pseudoMetricType R) (x : M)
  (e : {posnum R}) : ball x e%:num x.
Proof. exact: ball_center_subproof. Qed.
#[global] Hint Extern 0 (ball _ _ _) => solve[apply: ball_center] : core.

Section pseudoMetricType_numDomainType.
Context {R : numDomainType} {M : pseudoMetricType R}.
Implicit Types x y z : M.

Lemma ballxx x (e : R) : 0 < e -> ball x e x.
Proof. by move=> e_gt0; apply: ball_center (PosNum e_gt0). Qed.

Lemma ball_sym x y (e : R) : ball x e y -> ball y e x.
Proof. exact: ball_sym_subproof. Qed.

Lemma ball_symE x y (e : R) : ball x e y = ball y e x.
Proof. by rewrite propeqE; split; exact/ball_sym. Qed.

Lemma ball_triangle y x z (e1 e2 : R) :
  ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z.
Proof. exact: ball_triangle_subproof. Qed.

Lemma nbhsx_ballx x (eps : R) : 0 < eps -> nbhs x (ball x eps).
Proof. by move=> e0; apply/nbhs_ballP; exists eps. Qed.

Lemma open_nbhs_ball x (eps : {posnum R}) : open_nbhs x (ball x eps%:num)°.
Proof.
split; first exact: open_interior.
by apply: nbhs_singleton; apply: nbhs_interior; exact: nbhsx_ballx.
Qed.

Lemma le_ball x (e1 e2 : R) : e1 <= e2 -> ball x e1 `<=` ball x e2.
Proof.
move=> le12 y. case: comparableP le12 => [lte12 _|//|//|->//].
by rewrite -[e2](subrK e1); apply/ball_triangle/ballxx; rewrite subr_gt0.
Qed.

Lemma near_ball y (eps : R) : 0 < eps -> \forall y' \near y, ball y eps y'.
Proof. exact: nbhsx_ballx. Qed.

Lemma dnbhs_ball x (e : R) : (0 < e)%R -> x^' (ball x e `\ x).
Proof.
move: e => _/posnumP[e]; rewrite /dnbhs /within /=; near=> r => ra.
split => //=; last exact/eqP.
by near: r; rewrite near_simpl; exact: near_ball.
Unshelve. all: by end_near. Qed.

Lemma fcvg_ballP {F} {FF : Filter F} (y : M) :
  F --> y <-> forall eps : R, 0 < eps -> \forall y' \near F, ball y eps y'.
Proof. by rewrite -filter_fromP !nbhs_simpl /=. Qed.

Lemma fcvg_ball {F} {FF : Filter F} (y : M) :
  F --> y -> forall eps : R, 0 < eps -> \forall y' \near F, ball y eps y'.
Proof. by move/fcvg_ballP. Qed.

Lemma cvg_ballP {T} {F} {FF : Filter F} (f : T -> M) y :
  f @ F --> y <-> forall eps : R, 0 < eps -> \forall x \near F, ball y eps (f x).
Proof. exact: fcvg_ballP. Qed.

Lemma cvg_ball {T} {F} {FF : Filter F} (f : T -> M) y :
  f @ F --> y -> forall eps : R, 0 < eps -> \forall x \near F, ball y eps (f x).
Proof. exact: fcvg_ball. Qed.

Lemma cvgi_ballP T {F} {FF : Filter F} (f : T -> M -> Prop) y :
  f `@ F --> y <->
  forall eps : R, 0 < eps -> \forall x \near F, exists z, f x z /\ ball y eps z.
Proof.
split=> [Fy _/posnumP[eps] |Fy P] /=; first exact/Fy/nbhsx_ballx.
move=> /nbhs_ballP[_ /posnumP[eps] subP].
rewrite near_simpl near_mapi; near=> x.
have [//|z [fxz yz]] := near (Fy _ (gt0 eps)) x.
by exists z => //; split => //; apply: subP.
Unshelve. all: end_near. Qed.

Lemma cvgi_ball T {F} {FF : Filter F} (f : T -> M -> Prop) y :
  f `@ F --> y ->
  forall eps : R, 0 < eps -> F [set x | exists z, f x z /\ ball y eps z].
Proof. by move/cvgi_ballP. Qed.

End pseudoMetricType_numDomainType.

#[global] Hint Resolve nbhsx_ballx : core.

Global Instance entourage_proper_filter {R : numDomainType}
  {M : pseudoPMetricType R} : ProperFilter (@entourage M).
Proof.
apply: Build_ProperFilter_ex; rewrite -entourage_ballE => A [_/posnumP[e] sbeA].
by exists (point, point); apply: sbeA; apply: ballxx.
Qed.

Arguments nbhsx_ballx {R M} x eps.
Arguments near_ball {R M} y eps.

Section pseudoMetricType_numFieldType.
Context {R : numFieldType} {M : pseudoMetricType R}.
Implicit Types x y z p : M.

Lemma ball_split z x y (e : R) :
  ball x (e / 2) z -> ball z (e / 2) y -> ball x e y.
Proof. by move=> /ball_triangle h /h; rewrite -splitr. Qed.

Lemma ball_splitr z x y (e : R) :
  ball z (e / 2) x -> ball z (e / 2) y -> ball x e y.
Proof. by move=> /ball_sym /ball_split; apply. Qed.

Lemma ball_splitl z x y (e : R) :
  ball x (e / 2) z -> ball y (e / 2) z -> ball x e y.
Proof. by move=> bxz /ball_sym /(ball_split bxz). Qed.

End pseudoMetricType_numFieldType.

Lemma cvg_withinP {T : topologicalType} {R : archiRealFieldType}
  {M : pseudoMetricType R} (f : M -> T) (p : M) (l : T) (A : set M) :
  f @ within A (nbhs p) --> l <->
  (forall u : M^nat, (forall n, A (u n)) /\ u @ \oo --> p ->
    f (u n) @[n --> \oo] --> l).
Proof.
split=> [fpl u [Au up]|ful].
  move=> V Vnb.
  have := fpl _ Vnb; rewrite {1 2 4}/nbhs/= /within/= => Unb.
  have [N _ {}up] := up _ Unb.
  by exists N => // n /= Nn; exact: up.
apply: contrapT => fpl; move: ful; apply/existsNP.
suff: exists2 u : M^nat,
    (forall k, A (u k)) /\ u @ \oo --> p & ~ f (u n) @[n --> \oo] --> l.
  by move=> [x_] h; exists x_; exact/not_implyP.
have [V Vnb hV] : exists2 V : set T, nbhs l V & forall d : {posnum R},
    exists xn : M, [/\ A xn, ball xn d%:num p & ~ V (f xn)].
  apply: contrapT; apply: contra_not fpl => /forallPNP h.
  move=> V Vnb; have /existsNP[d] := h V Vnb; move/forallNP => {}h.
  rewrite nbhs_nearE near_map near_withinE; near=> t => At.
  have /not_and3P[//|bp|/contrapT //] := h t.
  exfalso; apply: bp.
  by rewrite ball_symE; near: t; apply: near_ball.
have invn n : 0 < n.+1%:R^-1 :> R by rewrite invr_gt0.
exists (fun n => sval (cid (hV (PosNum (invn n))))).
- split => [k|]; first by rewrite /sval/=; case: cid => x [].
  apply/cvg_ballP => r r0; near=> n.
  rewrite /sval/=; case: cid => x [Ax xpn _].
  rewrite ball_symE; apply: le_ball xpn.
  rewrite -(@invrK _ r) lef_pV2 ?posrE ?invr_gt0//.
  near: n; exists (Num.truncn r^-1) => // s /= rs.
  by apply/ltW; rewrite -truncn_le_nat.
- move=> /(_ V Vnb)[N _] /(_ _ (leqnn _)).
  by rewrite /sval/=; case: cid => // x [Ax xpN].
Unshelve. all: by end_near. Qed.

Lemma cvg_nbhsP {T : topologicalType} {R : archiRealFieldType}
  {M : pseudoMetricType R} (f : M -> T) (p : M) (l : T) :
  f @ p --> l <->
  (forall u : M^nat, u @ \oo --> p -> f (u n) @[n --> \oo] --> l).
Proof.
rewrite -(withinET (F := nbhs p)) cvg_withinP withinET.
apply/propeqP; apply: eq_forall => u; congr (_ -> _).
by apply/propeqP; split=> [[]|].
Qed.

Lemma compact_second_countable {R : realType} {T : pseudoPMetricType R} :
  compact [set: T] -> @second_countable T.
Proof.
have npos n : (0:R) < n.+1%:R^-1 by [].
pose f n (z : T): set T := (ball z (PosNum (npos n))%:num)°.
move=> cmpt; have h n : finite_subset_cover [set: T] (f n) [set: T].
  move: cmpt; rewrite compact_cover; apply.
  - by move=> z _; rewrite /f; exact: open_interior.
  - by move=> z _; exists z => //; rewrite /f /interior; exact: nbhsx_ballx.
pose h' n := cid (iffLR (exists2P _ _) (h n)).
pose h'' n := projT1 (h' n).
pose B := \bigcup_n (f n) @` [set` h'' n]; exists B;[|split].
- apply: bigcup_countable => // n _; apply: finite_set_countable.
  exact/finite_image/ finite_fset.
- by move => ? [? _ [? _ <-]]; exact: open_interior.
- move=> x V /nbhs_ballP [] _/posnumP[eps] ballsubV.
  have [//|N] := @ltr_add_invr R 0%R (eps%:num/2) _; rewrite add0r => deleps.
  have [w wh fx] : exists2 w : T, w \in h'' N & f N w x.
    by have [_ /(_ x) [// | w ? ?]] := projT2 (h' N); exists w.
  exists (f N w); first split => //; first (by exists N).
  apply: (subset_trans _ ballsubV) => z bz.
  rewrite [_%:num]splitr; apply: (@ball_triangle _ _ w).
    by apply: (le_ball (ltW deleps)); apply/ball_sym; apply: interior_subset.
  by apply: (le_ball (ltW deleps)); apply: interior_subset.
Qed.

Lemma clopen_surj {R : realType} {T : pseudoPMetricType R} :
  compact [set: T] -> $|{surjfun [set: nat] >-> @clopen T}|.
Proof.
move=> cmptT.
suff : @clopen T = set0 \/ $|{surjfun [set: nat] >-> @clopen T}|.
  by case => //; rewrite eqEsubset => -[/(_ _ clopenT)].
exact/pfcard_geP/clopen_countable/compact_second_countable.
Qed.

Section entourages.
Context {R : numDomainType}.

Lemma unif_continuousP (U V : pseudoMetricType R) (f : U -> V) :
  unif_continuous f <->
  forall e, e > 0 -> exists2 d, d > 0 &
    forall x, ball x.1 d x.2 -> ball (f x.1) e (f x.2).
Proof.
have fappF : Filter ((fun xy => (f xy.1, f xy.2)) @ entourage_ ball).
  by rewrite entourage_ballE; apply: fmap_filter.
by rewrite /unif_continuous -!entourage_ballE filter_fromP.
Qed.

End entourages.

Lemma countable_uniformity_metric {R : realType} {T : pseudoMetricType R} :
  countable_uniformity T.
Proof.
apply/countable_uniformityP.
exists (fun n => [set xy : T * T | ball xy.1 n.+1%:R^-1 xy.2]); last first.
  by move=> n; exact: (entourage_ball _ n.+1%:R^-1%:pos).
move=> E; rewrite -entourage_ballE => -[e e0 subE].
exists (Num.truncn e^-1); apply: subset_trans subE => xy; apply: le_ball.
by rewrite /= -[leRHS]invrK lef_pV2 ?posrE ?invr_gt0// ltW// truncnS_gt.
Qed.

(** Specific pseudoMetric spaces *)

HB.instance Definition _ (R : zmodType) := isPointed.Build R 0.

Definition ball_
  (R : numDomainType) (V : zmodType) (norm : V -> R) (x : V) (e : R) :=
  [set y | norm (x - y) < e].
Arguments ball_ {R} {V} norm x e%_R y /.

Lemma subset_ball_prop_in_itv (R : realDomainType) (x : R) e P :
  ball_ Num.Def.normr x e `<=` P <->
  {in `](x - e), (x + e)[, forall y, P y}.
Proof.
by split=> exP y /=; rewrite ?in_itv (ltr_distlC, =^~ltr_distlC); apply: exP.
Qed.

Lemma subset_ball_prop_in_itvcc (R : realDomainType) (x : R) e P : 0 < e ->
  ball_ Num.Def.normr x (2 * e) `<=` P ->
  {in `[(x - e), (x + e)], forall y, P y}.
Proof.
move=> e_gt0 PP y; rewrite in_itv/= -ler_distlC => ye; apply: PP => /=.
by rewrite (le_lt_trans ye)// ltr_pMl// ltr1n.
Qed.

Global Instance ball_filter (R : realDomainType) (t : R) : Filter
  [set P | exists2 i : R, 0 < i & ball_ Num.norm t i `<=` P].
Proof.
apply: Build_Filter; [by exists 1 | move=> P Q | move=> P Q PQ]; rewrite /mkset.
- move=> -[x x0 xP] [y ? yQ]; exists (Num.min x y); first by rewrite lt_min x0.
  move=> z tz; split.
    by apply: xP; rewrite /= (lt_le_trans tz) // ge_min lexx.
  by apply: yQ; rewrite /= (lt_le_trans tz) // ge_min lexx orbT.
- by move=> -[x ? xP]; exists x => //; apply: (subset_trans xP).
Qed.

#[global] Hint Extern 0 (Filter [set P | exists2 i, _ & ball_ _ _ i `<=` P]) =>
  (apply: ball_filter) : typeclass_instances.

Section pseudoMetric_of_normedDomain.
Context {K : numDomainType} {R : normedZmodType K}.

Lemma ball_norm_center (x : R) (e : K) : 0 < e -> ball_ Num.norm x e x.
Proof. by move=> ? /=; rewrite subrr normr0. Qed.

Lemma ball_norm_symmetric (x y : R) (e : K) :
  ball_ Num.norm x e y -> ball_ Num.norm y e x.
Proof. by rewrite /= distrC. Qed.

Lemma ball_norm_triangle (x y z : R) (e1 e2 : K) :
  ball_ Num.norm x e1 y -> ball_ Num.norm y e2 z -> ball_ Num.norm x (e1 + e2) z.
Proof.
by move=> /= ? ?; rewrite -(subrKA y) (le_lt_trans (ler_normD _ _)) // ltrD.
Qed.

Lemma nbhs_ball_normE :
  @nbhs_ball_ K R R (ball_ Num.norm) = nbhs_ (entourage_ (ball_ Num.norm)).
Proof.
rewrite /nbhs_ entourage_E predeq2E => x A; split.
  move=> [e egt0 sbeA].
  exists [set xy | ball_ Num.norm xy.1 e xy.2]; first by exists e.
  by move=> r /xsectionP; exact: sbeA.
by move=> [E [e egt0 sbeE] sEA]; exists e => // ? ?; exact/sEA/xsectionP/sbeE.
Qed.

End pseudoMetric_of_normedDomain.

HB.instance Definition _ (R : zmodType) := Pointed.on R^o.

#[short(type="completePseudoMetricType")]
HB.structure Definition CompletePseudoMetric R :=
  {T of Complete T & PseudoPointedMetric R T}.

Definition cauchy_ex {R : numDomainType} {T : pseudoMetricType R}
    (F : set_system T) :=
  forall eps : R, 0 < eps -> exists x, F (ball x eps).

Definition cauchy_ball {R : numDomainType} {T : pseudoMetricType R}
    (F : set_system T) :=
  forall e, e > 0 -> \forall x & y \near F, ball x e y.

Lemma cauchy_ballP (R : numDomainType) (T  : pseudoMetricType R)
    (F : set_system T) (FF : Filter F) :
  cauchy_ball F <-> cauchy F.
Proof.
split=> cauchyF; last first.
  by move=> _/posnumP[eps]; apply/cauchyF/entourage_ball.
move=> U; rewrite -entourage_ballE => - [_/posnumP[eps] xyepsU].
by near do apply: xyepsU; apply: cauchyF.
Unshelve. all: by end_near. Qed.
Arguments cauchy_ballP {R T} F {FF}.

Lemma cauchy_exP (R : numFieldType) (T : pseudoMetricType R)
    (F : set_system T) (FF : Filter F) :
  cauchy_ex F -> cauchy F.
Proof.
move=> Fc A; rewrite !nbhs_simpl /= -entourage_ballE => -[_/posnumP[e] sdeA].
have /Fc [z /= Fze] := [gt0 of e%:num / 2]; near=> x y; apply: sdeA => /=.
by apply: (@ball_splitr _ _ z); [near: x|near: y].
Unshelve. all: by end_near. Qed.
Arguments cauchy_exP {R T} F {FF}.

Lemma cauchyP (R : numFieldType) (T : pseudoMetricType R)
    (F : set_system T) (PF : ProperFilter F) :
  cauchy F <-> cauchy_ex F.
Proof.
split=> [Fcauchy _/posnumP[e] |/cauchy_exP//].
near F => x; exists x; near: x; apply: (@nearP_dep _ _ F F).
exact/Fcauchy/entourage_ball.
Unshelve. all: by end_near. Qed.
Arguments cauchyP {R T} F {PF}.

Definition closed_ball_ {R : numDomainType} {V : zmodType} (norm : V -> R)
  (x : V) (e : R) := [set y | norm (x - y) <= e].

Definition closed_ball {R : numDomainType} {V : pseudoMetricType R}
  (x : V) (e : R) := closure (ball x e).

Section closed_ball_lemmas.
Context {R : numDomainType} {V : pseudoMetricType R}.
Implicit Types (x : V) (r : R).

Lemma closure_ballE x r : closure (ball x r) = closed_ball x r.
Proof. by []. Qed.

Lemma closed_ballxx x r : 0 < r -> closed_ball x r x.
Proof. by move=> ?; exact/subset_closure/ballxx. Qed.

Lemma closed_ball_closed x r : closed (closed_ball x r).
Proof. exact: closed_closure. Qed.

Lemma subset_closed_ball x r : ball x r `<=` closed_ball x r.
Proof. exact: subset_closure. Qed.

Lemma le_closed_ball x r1 r2 : (r1 <= r2)%O ->
  closed_ball x r1 `<=` closed_ball x r2.
Proof. by rewrite /closed_ball => le; apply/closureS/le_ball. Qed.

End closed_ball_lemmas.
#[deprecated(since="mathcomp-analysis 1.14.0", note="renamed to `closure_ballE`")]
Notation closure_ball := closure_ballE (only parsing).

Lemma subset_closure_half {R : numFieldType} {V : pseudoMetricType R} (x : V)
  (r : R) : 0 < r -> closed_ball x (r / 2) `<=` ball x r.
Proof.
move:r => _/posnumP[r] z /(_ (ball z ((r%:num/2)%:pos)%:num)) [].
  exact: nbhsx_ballx.
by move=> y [+/ball_sym]; rewrite [t in ball x t z]splitr; apply: ball_triangle.
Qed.


(* This section proves that uniform spaces, with a countable base for their
   entourage, are metrizable. The definition of this metric is rather arcane,
   and the proof is tough. That's ok because the resulting metric is not
   intended to be used explicitly. Instead, this is typically used in
   applications that do not depend on the metric:
   - `metric spaces are T4`
   - `in metric spaces, compactness and sequential compactness agree`
   - infinite products of metric spaces are metrizable
*)
Module countable_uniform.
Section countable_uniform.
Local Open Scope relation_scope.
Context {R : realType} {T : uniformType}.

Hypothesis cnt_unif : @countable_uniformity T.

Let f_ := projT1 (cid2 (iffLR countable_uniformityP cnt_unif)).

Local Lemma countableBase : forall A, entourage A -> exists N, f_ N `<=` A.
Proof. by have [] := projT2 (cid2 (iffLR countable_uniformityP cnt_unif)). Qed.

Let entF : forall n, entourage (f_ n).
Proof. by have [] := projT2 (cid2 (iffLR countable_uniformityP cnt_unif)). Qed.

(* Step 1:
   We build a nicer base `g` for `entourage` with better assumptions than `f`
   - each (g_ n) is symmetric
   - the sets (g_ n) are nested downward
   - g_ n.+1 \o g_ n.+1 \o g_ n.+1 `<=` g_ n says the sets descend `quickly`
 *)

Local Fixpoint g_ n : set (T * T) :=
  if n is n.+1 then let W := split_ent (split_ent (g_ n)) `&` f_ n in W `&` W^-1
  else [set: T*T].

Let entG n : entourage (g_ n).
Proof.
elim: n => /=; first exact: entourageT.
by move=> n entg; apply/entourage_invI; exact: filterI.
Qed.

Local Lemma symG n : (g_ n)^-1 = g_ n.
Proof.
by case: n => // n; rewrite eqEsubset; split; case=> ? ?; rewrite /= andC.
Qed.

Local Lemma descendG1 n : g_ n.+1 `<=` g_ n.
Proof.
apply: subIset; left; apply: subIset; left; apply: subset_trans.
  by apply: split_ent_subset; exact: entourage_split_ent.
by apply: subset_trans; last exact: split_ent_subset.
Qed.

Local Lemma descendG n m : (m <= n)%N -> g_ n `<=` g_ m.
Proof.
elim: n; rewrite ?leqn0; first by move=>/eqP ->.
move=> n IH; rewrite leq_eqVlt ltnS => /orP [/eqP <- //|] /IH.
by apply: subset_trans; exact: descendG1.
Qed.

Local Lemma splitG3 n : g_ n.+1 \; g_ n.+1 \; g_ n.+1 `<=` g_ n.
Proof.
suff g2split : g_ n.+1 \; g_ n.+1 `<=` split_ent (g_ n).
  apply: subset_trans; last exact: subset_split_ent (entG n).
  apply: set_compose_subset (g2split); rewrite -[_ n.+1]set_compose_diag.
  apply: subset_trans g2split; apply: set_compose_subset => //.
  by move=> [_ _] [z _] [<- <-]; exact: entourage_refl.
apply: subset_trans; last exact: subset_split_ent.
by apply: set_compose_subset; apply: subIset; left; apply: subIset; left.
Qed.

Local Lemma gsubf n : g_ n.+1 `<=` f_ n.
Proof. by apply: subIset; left; apply: subIset; right. Qed.

Local Lemma countableBaseG A : entourage A -> exists N, g_ N `<=` A.
Proof.
move=> /countableBase [N] fnA; exists N.+1.
by apply: subset_trans fnA; exact: gsubf.
Qed.

(* Step 2.
   We build a sensible notion of balls for our metric.
   The naive attempt,
                     `ball x e y := g_ (distN e) (x,y))
   doesn't respect triangle inequality. We need to cook triangle inequality
   into the balls themselves. So we define balls in terms of steps:
      `ball x e y := there are n steps x_0 = x,...,x_i,..., x_n.+1 = y and
                     e_1,...,e_n such that
                           g_ (distN e_i) (x_i,x_i+1)
                                    and
                               sum (e_i) = e
*)

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Definition distN (e : R) : nat := Num.truncn e^-1.

Local Lemma distN0 : distN 0 = 0%N.
Proof. by rewrite /distN invr0 truncn0. Qed.

Local Lemma distN_nat (n : nat) : distN n%:R^-1 = n.
Proof.
by rewrite /distN invrK; apply/eqP; rewrite -(@eqr_nat R) -natrEtruncn.
Qed.

Local Lemma distN_le e1 e2 : e1 > 0 -> e1 <= e2 -> (distN e2 <= distN e1)%N.
Proof.
move=> e1pos e1e2; rewrite /distN le_truncn// lef_pV2// posrE.
by rewrite (lt_le_trans e1pos).
Qed.

Local Fixpoint n_step_ball n x e z :=
  if n is n.+1 then exists y d1 d2,
    [/\ n_step_ball n x d1 y,
        0 < d1,
        0 < d2,
        g_ (distN d2) (y, z) &
        d1 + d2 = e]
  else e > 0 /\ g_ (distN e) (x, z).

Local Definition step_ball x e z := exists i, (n_step_ball i x e z).

Local Lemma n_step_ball_pos n x e z : n_step_ball n x e z -> 0 < e.
Proof.
by case: n => [[]|] // n; case=> [?] [?] [?] [] ? ? ? ? <-; exact: addr_gt0.
Qed.

Local Lemma step_ball_pos x e z : step_ball x e z -> 0 < e.
Proof. by case => ?; exact: n_step_ball_pos. Qed.

Local Lemma entourage_nball e :
  0 < e -> entourage [set xy | step_ball xy.1 e xy.2].
Proof.
move=> epos; apply: (@filterS _ _ _ (g_ (distN e))) => // [[x y]] ?.
by exists 0%N.
Qed.

Local Lemma n_step_ball_center x e : 0 < e -> n_step_ball 0 x e x.
Proof. by move=> epos; split => //; exact: entourage_refl. Qed.

Local Lemma step_ball_center x e : 0 < e -> step_ball x e x.
Proof. by move=> epos; exists 0%N; apply: n_step_ball_center. Qed.

Local Lemma n_step_ball_triangle n m x y z d1 d2 :
  n_step_ball n x d1 y ->
  n_step_ball m y d2 z ->
  n_step_ball (n + m).+1 x (d1 + d2) z.
Proof.
move: n z d2; elim: m => [n z d2 Nxy [? ?]|n IH m z d2 Oxy].
  by exists y, d1, d2; split; rewrite ?addn0 // (n_step_ball_pos Nxy).
move=> [w] [e1] [e2] [Oyw ? ? ? <-].
exists w, (d1 + e1), e2; rewrite addnS addrA.
split => //; last by rewrite addr_gt0//; exact: n_step_ball_pos Oxy.
by case: (IH m w e1 Oxy Oyw) => t [e3] [e4] [] Oxt ? ? ? <-; exists t, e3, e4.
Qed.

Local Lemma step_ball_triangle x y z d1 d2 :
  step_ball x d1 y -> step_ball y d2 z -> step_ball x (d1 + d2) z.
Proof.
move=> [n Oxy] [m Oyz]; exists (n + m).+1.
exact: n_step_ball_triangle Oxy Oyz.
Qed.

Local Lemma n_step_ball_sym n x y e :
  n_step_ball n x e y -> n_step_ball n y e x.
Proof.
move: x y e; elim: n; first by move=> ? ? ?; rewrite /= -{1}symG.
move=> n IH x y e [t] [d1] [d2] [] /IH Oty ? ?.
rewrite addrC -symG -[n]add0n => gty <-; apply: (n_step_ball_triangle _ Oty).
by split => //; exact: gty.
Qed.

Local Lemma step_ball_sym x y e : step_ball x e y -> step_ball y e x.
Proof. by case=> n /n_step_ball_sym ?; exists n. Qed.

(* Step 3:
   We prove that step_ball respects the original entourage. This requires an
   induction on the length of the steps, which is pretty tricky. The central
   lemma is `split_n_step_ball`, which lets us break a list into parts three
   parts as: half + one_step + half. Then our we can break apart our n +1 path

                         nlong + one_step
   into
                  (half + one_step + half) + one_step
                                =
                  half + one_step + (half + one_step)

   and we can we can use our (strong) induction hypothesis.
   And lastly we finish with splitG3.
*)

Local Lemma n_step_ball_le n x e1 e2 :
  e1 <= e2 -> n_step_ball n x e1 `<=` n_step_ball n x e2.
Proof.
move: x e1 e2; elim: n.
  move=> x e1 e2 e1e2 y [?] gxy; split; first exact: (lt_le_trans _ e1e2).
  by apply: descendG; last (exact: gxy); exact: distN_le.
move=> n IH x e1 e2 e1e2 z [y] [d1] [d2] [] /IH P d1pos d2pos gyz d1d2e1.
exists y, (e2 - d2), d2; split => //.
- by apply: P; rewrite lerBrDr d1d2e1.
- by apply: lt_le_trans d1pos _; rewrite lerBrDr d1d2e1.
- by rewrite subrK.
Qed.

Local Lemma step_ball_le x e1 e2 :
  e1 <= e2 -> step_ball x e1 `<=` step_ball x e2.
Proof. by move=> e1e2 ? [n P]; exists n; exact: (n_step_ball_le e1e2). Qed.

Local Lemma distN_half (n : nat) : n.+1%:R^-1 / (2:R) <= n.+2%:R^-1.
Proof.
rewrite -invrM //; [exact: unitf_gt0 |exact: unitf_gt0|].
rewrite lef_pV2 ?posrE // -?natrM ?ler_nat -addn1 -addn1 -addnA mulnDr.
by rewrite muln1 leq_add2r leq_pmull.
Qed.

Local Lemma split_n_step_ball n x e1 e2 z :
  0 < e1 -> 0 < e2 -> n_step_ball n.+1 x (e1 + e2) z ->
    exists t1 t2 a b,
    [/\
      n_step_ball a x e1 t1,
      n_step_ball 0 t1 (e1 + e2) t2,
      n_step_ball b t2 e2 z &
      (a + b = n)%N
    ].
Proof.
move: e1 e2 x z; elim: n.
  move=> e1 e2 x z e1pos e2pos [y] [d1] [d2] [] Oxy ? ? gd2yz deE.
  case: (pselect (e1 <= d1)).
    move=> e1d1; exists x, y, 0%N, 0%N; split.
    - exact: n_step_ball_center.
    - apply: n_step_ball_le; last exact: Oxy.
      by rewrite -deE lerDl; apply: ltW.
    - by apply: (@n_step_ball_le _ _ d2); rewrite // -(lerD2l e1) -deE lerD.
    - by rewrite addn0.
  move=> /negP; rewrite -ltNge//.
  move=> e1d1; exists y, z, 0%N, 0%N; split.
  - by apply: n_step_ball_le; last (exact: Oxy); exact: ltW.
  - by apply: (@n_step_ball_le _ _ d2); rewrite // -deE lerDr ltW.
  - exact: n_step_ball_center.
  - by rewrite addn0.
move=> n IH e1 e2 x z e1pos e2pos [y] [d1] [d2] [] Od1xy d1pos d2pos gd2yz deE.
case: (pselect (e2 <= d2)).
  move=> e2d2; exists y, z, n.+1, 0%N; split.
  - by apply: (@n_step_ball_le _ _ d1); rewrite // -(lerD2r e2) -deE lerD.
  - by apply: (@n_step_ball_le _ _ d2); rewrite // -deE lerDr; exact: ltW.
  - exact: n_step_ball_center.
  - by rewrite addn0.
have d1E' : d1 = e1 + (e2 - d2) by rewrite addrA -deE addrK.
move=> /negP; rewrite -ltNge// => d2lee2.
  case: (IH e1 (e2 - d2) x y); rewrite ?subr_gt0 // -d1E' //.
  move=> t1 [t2] [c1] [c2] [] Oxy1 gt1t2 t2y <-.
  exists t1, t2, c1, c2.+1; split => //.
  - by apply: (@n_step_ball_le _ _ d1); rewrite -?deE // ?lerDl; exact: ltW.
  - by exists y, (e2 - d2), d2; rewrite // ?subr_gt0// subrK.
  - by rewrite addnS.
Qed.

Local Lemma n_step_ball_le_g x n :
  n_step_ball 0 x n%:R^-1 `<=` [set y | g_ n (x,y)].
Proof. by move=> y [] ?; rewrite distN_nat. Qed.

Local Lemma subset_n_step_ball n x N :
  n_step_ball n x N.+1%:R^-1 `<=` [set y | (g_ N) (x, y)].
Proof.
move: N x; elim: n {-2}n (leqnn n) => n.
  rewrite leqn0 => /eqP -> N x; apply: subset_trans.
    exact: n_step_ball_le_g.
  by move=> y ?; exact: descendG.
move=> IH1 + + N x1 x4; case.
  by move=> ? [?] P; apply: descendG _ P; rewrite distN_nat.
move=> l ln1 Ox1x4.
case: (@split_n_step_ball l x1 (N.+1%:R^-1/2) (N.+1%:R^-1/2) x4) => //.
  by rewrite -splitr.
move=> x2 [x3] [l1] [l2] [] P1 [? +] P3 l1l2; rewrite -splitr distN_nat => ?.
have l1n : (l1 <= n)%N by rewrite (leq_trans (leq_addr l2 l1))// l1l2 -ltnS.
have l2n : (l2 <= n)%N by rewrite (leq_trans (leq_addl l1 l2))// l1l2 -ltnS.
apply: splitG3; exists x3; [exists x2 => //|].
  by move/(n_step_ball_le (distN_half N))/(IH1 _ l1n) : P1.
by move/(n_step_ball_le (distN_half N))/(IH1 _ l2n) : P3.
Qed.

Local Lemma subset_step_ball x N :
  step_ball x N.+1%:R^-1 `<=` [set y | (g_ N) (x, y)].
Proof. by move=> y [] n; exact: subset_n_step_ball. Qed.

Local Lemma step_ball_entourage : entourage = entourage_ step_ball.
Proof.
rewrite predeqE => E; split; first last.
  by case=> e /= epos esubE; apply: (filterS esubE); exact: entourage_nball.
move=> entE; case: (countableBase entE) => N fN.
exists N.+2%:R^-1; first by rewrite /= invr_gt0.
apply: (subset_trans _ fN); apply: subset_trans; last apply: gsubf.
by case=> x y /= N1ball; apply: (@subset_step_ball x N.+1).
Qed.

Definition type : Type := let _ := countableBase in let _ := entF in T.

#[export] HB.instance Definition _ := Uniform.on type.
#[export] HB.instance Definition _ := Uniform_isPseudoMetric.Build R type
  step_ball_center step_ball_sym step_ball_triangle step_ball_entourage.
#[export] HB.instance Definition _ {q : Pointed T} :=
  Pointed.copy type (Pointed.Pack q).

Lemma countable_uniform_bounded (x y : T) : @ball _ type x 2 y.
Proof.
rewrite /ball; exists O%N; rewrite /n_step_ball; split; rewrite // /distN.
rewrite (_ : Num.truncn _ = 0)//.
by apply/eqP; rewrite truncn_eq// invr_ge0// ler0n/= invf_lt1// ltr1n.
Qed.

End countable_uniform.

Module Exports. HB.reexport. End Exports.
End countable_uniform.
Export countable_uniform.Exports.

Notation countable_uniform := countable_uniform.type.

Module gauge.
Section gauge.
Local Open Scope relation_scope.

Let split_sym {T : uniformType} (W : set (T * T)) :=
  (split_ent W) `&` (split_ent W)^-1.

Section entourage_gauge.
Context {T : uniformType} (E : set (T * T)) (entE : entourage E).

Definition gauge :=
  filter_from [set: nat] (fun n => iter n split_sym (E `&` E^-1)).

Lemma iter_split_ent j : entourage (iter j split_sym (E `&` E^-1)).
Proof. by elim: j => [|i IH]; exact: filterI. Qed.

Lemma gauge_ent A : gauge A -> entourage A.
Proof.
case=> n; elim: n A; first by move=> ? _ /filterS; apply; apply: filterI.
by move=> n ? A _ /filterS; apply; apply: filterI; have ? := iter_split_ent n.
Qed.

Lemma gauge_filter : Filter gauge.
Proof.
apply: filter_from_filter; first by exists 0%N.
move=> i j _ _; wlog ilej : i j / (i <= j)%N.
  by move=> WH; have [|/ltnW] := leqP i j;
    [|rewrite (setIC (iter _ _ _))]; exact: WH.
exists j => //; rewrite subsetI; split => //; elim: j i ilej => [i|j IH i].
  by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /predU1P[<-//|/ltnSE/IH]; apply: subset_trans.
by move=> x/= [jx _]; apply: split_ent_subset => //; exact: iter_split_ent.
Qed.

Lemma gauge_refl A : gauge A -> diagonal `<=` A.
Proof.
case=> n _; apply: subset_trans => -[_ a]/diagonalP ->.
by apply: entourage_refl; exact: iter_split_ent.
Qed.

Lemma gauge_inv A : gauge A -> gauge A^-1.
Proof.
case=> n _ EA; apply: (@filterS _ _ _ (iter n split_sym (E `&` E^-1))).
- exact: gauge_filter.
- by case: n EA; last move=> n; move=> EA [? ?] [/=] ? ?; exact: EA.
- by exists n .
Qed.

Lemma gauge_split A : gauge A -> exists2 B, gauge B & B \; B `<=` A.
Proof.
case => n _ EA; exists (iter n.+1 split_sym (E `&` E^-1)); first by exists n.+1.
apply: subset_trans EA; apply: subset_trans; first last.
  by apply: subset_split_ent; exact: iter_split_ent.
by case=> a c [b] [] ? ? [] ? ?; exists b.
Qed.

Let gauged : Type := T.

HB.instance Definition _ := Choice.on gauged.
HB.instance Definition _ :=
  @isUniform.Build gauged gauge gauge_filter gauge_refl gauge_inv gauge_split.

Lemma gauge_countable_uniformity : countable_uniformity gauged.
Proof.
exists [set iter n split_sym (E `&` E^-1) | n in [set: nat]].
split; [exact: card_image_le | by move=> W [n] _ <-; exists n|].
by move=> D [n _ ?]; exists (iter n split_sym (E `&` E^-1)).
Qed.

Definition type := countable_uniform.type gauge_countable_uniformity.
End entourage_gauge.

End gauge.
Module Exports. HB.reexport. End Exports.
End gauge.
Export gauge.Exports.