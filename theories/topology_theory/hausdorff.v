(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra interval_inference finmap.
From mathcomp Require Import boolp classical_sets functions wochoice contra.
From mathcomp Require Import cardinality fsbigop set_interval filter reals.
From mathcomp Require Import topology_structure connected compact.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section set_nbhs.
Context {T : topologicalType} (A : set T).

Definition set_nbhs := \bigcap_(x in A) nbhs x.

Global Instance set_nbhs_filter : Filter set_nbhs.
Proof.
split => P Q; first by exact: filterT.
  by move=> Px Qx x Ax; apply: filterI; [exact: Px | exact: Qx].
by move=> PQ + x Ax => /(_ _ Ax)/filterS; exact.
Qed.

Global Instance set_nbhs_pfilter : A !=set0 -> ProperFilter set_nbhs.
Proof.
case=> x Ax; split; last exact: set_nbhs_filter.
by move/(_ x Ax)/nbhs_singleton.
Qed.

Lemma set_nbhsP (B : set T) :
   set_nbhs B <-> (exists C, [/\ open C, A `<=` C & C `<=` B]).
Proof.
split; first last.
  by case=> V [? AV /filterS +] x /AV ?; apply; apply: open_nbhs_nbhs.
move=> snB; have Ux x : exists U, A x -> [/\ U x, open U & U `<=` B].
  have [/snB|?] := pselect (A x); last by exists point.
  by rewrite nbhsE => -[V [? ? ?]]; exists V.
exists (\bigcup_(x in A) (projT1 (cid (Ux x)))); split.
- by apply: bigcup_open => x Ax; have [] := projT2 (cid (Ux x)).
- by move=> x Ax; exists x => //; have [] := projT2 (cid (Ux x)).
- by move=> x [y Ay]; have [//| _ _] := projT2 (cid (Ux y)); exact.
Qed.

End set_nbhs.

Section point_separation_axioms.
Context {T : topologicalType}.

Definition is_kolmogorov_space := forall x y, x != y ->
  exists A : set T, (A \in nbhs x /\ y \in ~` A) \/ (A \in nbhs y /\ x \in ~` A).

Definition is_accessible_space := forall x y, x != y ->
  exists A : set T, [/\ open A, x \in A & y \in ~` A].

Definition is_hausdorff_space := forall p q : T, cluster (nbhs p) q -> p = q.

Definition is_urysohn_space := forall (x y : T), x != y -> 
  exists AB, [/\
    closed AB.1, closed AB.2, nbhs x AB.1, nbhs y AB.2 & [disjoint AB.1 & AB.2]
  ].

Definition is_regular_space :=
  forall (x : T) (F : set T), closed F -> (~ F x) ->
    exists (A B : set T), [/\
      nbhs x A , set_nbhs F B & [disjoint A & B]
    ].

Definition is_normal_space :=
  forall A : set T, closed A ->
    filter_from (set_nbhs A) closure `=>` set_nbhs A.

(* Definition is_completely_hausdorff_space := forall x y : T, x != y ->
  exists (f : T -> R), [/\ continuous f , f x = 0 & f y = 1 ].

Definition is_completely_regular_space := forall (x : T) (F : set T),
  closed F -> (~ F x) -> exists (f : T -> R), [/\
    continuous f, f x = 0 & (forall y, F y -> f y = 1)
  ].

Definition is_completely_normal_space :=
  forall A B : set T, separated A B -> 
    exists UV, [/\ set_nbhs A UV.1, set_nbhs B UV.2 & [disjoint UV.1 & UV.2]].

Definition is_perfectly_normal_space :=
  forall A B : set T, closed A -> closed B -> [disjoint A & B] ->
    exists f : T -> R, [/\ 
      continuous f, 
      A = f @^-1` [set 0] & B = f @^-1` [set 1]
    ]. *)

End point_separation_axioms.
Arguments is_kolmogorov_space : clear implicits.
Arguments is_accessible_space : clear implicits.
Arguments is_hausdorff_space : clear implicits.
Arguments is_urysohn_space : clear implicits.
Arguments is_regular_space : clear implicits.
Arguments is_normal_space : clear implicits.

Section separation_equivalences.
Context (R : realType) (T : topologicalType).

Lemma accessibleP : 
  is_accessible_space T  <-> (forall x : T, closed [set x]). 
Proof.
split=> [T1 x|cs1 x y xy].
  rewrite -[X in closed X]setCK; apply: open_closedC.
  rewrite openE => y /eqP /T1 [U [oU yU xU]].
  rewrite /interior nbhsE /=; exists U; last by rewrite subsetC1.
  by split=> //; exact: set_mem.
exists [set~ y]; split.
- by apply: closed_openC.
- by rewrite inE/=; apply/eqP.
- by rewrite inE/=.
Qed.

Lemma open_hausdorffP :
  is_hausdorff_space T <->
  (forall (x y : T), x != y -> exists2 AB, 
    (x \in AB.1 /\ y \in AB.2) &
    [/\ open AB.1, open AB.2 & [disjoint AB.1 & AB.2]]).
Proof.
split => [T_filterT2|T_openT2] x y.
  have := contra_not (T_filterT2 x y); move=> + /eqP => /[apply].
  move=> /existsNP[A] /existsNP[B] /not_implyP[xA] /not_implyP[yB].
  move=> /nonemptyPn AIB_eq0.
  move: xA yB; rewrite !nbhsE => -[oA [ooA oAx] oAA] [oB [ooB oBx] oBB].
  by exists (oA, oB); rewrite ?inE; split => //; apply: subsetI_eq0 AIB_eq0.
contra => /T_openT2[[A B] /= [/set_mem Ax /set_mem Bx] [oA oB AdB]].
exists A, B; last split; [ exact: open_nbhs_nbhs .. |].
by apply/disj_setPLR.
Qed.

Lemma closed_normalP :
  is_normal_space T <->
  forall (A B : set T), closed A -> closed B -> [disjoint A & B] ->
    exists UV, 
      [/\ set_nbhs A UV.1, set_nbhs B UV.2 & [disjoint UV.1 & UV.2]].
Proof.
split.
- move=> hN A B cA cB dAB.
  have nAcB : set_nbhs A (~` B).
    apply/set_nbhsP; exists (~` B); split=> //.
    + by apply: closed_openC.
    + by apply/disj_setPLR.
  have [U nAU /subsetCr +] := hN A cA _ nAcB.
  rewrite -interiorC => BicU.
  exists (U, (~` U)°); split=> //=.
  + apply/set_nbhsP; exists (~` U)°; split=> //.
    exact: open_interior.
  + by rewrite interiorC; apply/disj_setPCl; exact: subset_closure.
- move=> hN F cF U nFU.
  pose G := ~` U°.
  have cG : closed G.
    by apply: open_closedC; exact: open_interior.
  have dFG : [disjoint F & G].
    by apply/disj_setPCl; exact: nFU.
  have [[V W] /= [nFV nGW dVW]] := hN F G cF cG dFG.
  have VsciW : V `<=` ~` W°.
    move: dVW => /disj_setPLR /subset_trans; apply.
    apply: subsetC; exact: interior_subset.
  exists V => //.
  apply: (subset_trans (B := ~` W°)); last first.
    apply: subset_trans; last exact: interior_subset.
    by apply: subsetCl; exact: nGW. 
  move: VsciW => /closureS; congr subset.
  by apply/esym/closure_id; apply: open_closedC; exact: open_interior.
Qed.

Lemma open_normalP :
  is_normal_space T <->
  forall (G H : set T), open G -> open H -> G `|` H = [set: T] ->
    exists UV, [/\ 
      open UV.1 , open UV.2 ,
      UV.1 `|` G = [set: T] , 
      UV.2 `|` H = [set: T] & 
      [disjoint UV.1 & UV.2]
    ].
Proof.
rewrite closed_normalP; split.
- move=> hc G H oG oH GHT.
  have [] := hc (~` G) (~` H) (open_closedC oG) (open_closedC oH).
    by apply/eqP; rewrite -setCU; apply: (canLR setCK); rewrite setC0.
  move=> [U V] /= [ncGU ncHV /disj_setPS dUV].
  have dUVo : [disjoint U° & V°].
    apply/disj_setPS; apply: subset_trans dUV.
    by apply: setISS; exact: interior_subset.
  exists (U°, V°); split => //=; do ?exact: open_interior; by [
    rewrite -setC0; apply: (canRL setCK); rewrite setCU; 
    rewrite setIC; apply/subsets_disjoint
  ].
- move=> ho A B cA cB dAB.
  have [] := ho (~`A) (~`B) (closed_openC cA) (closed_openC cB).
    rewrite -setCI; apply: (canLR setCK); rewrite setCT.
    by apply/eqP.
  move=> [U V] /= [oU oV].
  rewrite -setC0 => /(canLR setCK) + /(canLR setCK) + dUV.
  rewrite !setCU !setCK !(setIC (~` _)).
  move => /subsets_disjoint + /subsets_disjoint +.
  have <- : U° = U by apply/interior_id.
  have <- : V° = V by apply/interior_id.
  by exists (U, V).
Qed.

End separation_equivalences.

HB.mixin Record Topological_isKolmogorov T & Topological T := {
  kolmogorov_space : is_kolmogorov_space T
}.

#[short(type="kolmogorovType")]
HB.structure Definition Kolmogorov := 
  {T of Topological T & Topological_isKolmogorov T}.

#[short(type="pkolmogorovType")]
HB.structure Definition PKolmogorov :=
  {T of Pointed T & Kolmogorov T}.

HB.mixin Record Kolmogorov_isAccessible T & Kolmogorov T := {
  accessible_space : is_accessible_space T
}.

#[short(type="accessibleType")]
HB.structure Definition Accessible :=
  {T of Kolmogorov T & Kolmogorov_isAccessible T}.

#[short(type="paccessibleType")]
HB.structure Definition PAccessible :=
  {T of Pointed T & Accessible T}.

HB.factory Record Topological_isAccessible T & Topological T := {
  accessible_space_subproof : is_accessible_space T
}.
HB.builders Context T & Topological_isAccessible T.

Let accessible_kolmogorov : is_kolmogorov_space T.
Proof.
move=> x y /accessible_space_subproof [A [oA xA yA]].
exists A; left; split=> //.
by rewrite nbhsE inE; exists A => //; rewrite inE in xA.
Qed.

HB.instance Definition _ := 
  Topological_isKolmogorov.Build T accessible_kolmogorov.
HB.instance Definition _ :=
  Kolmogorov_isAccessible.Build T accessible_space_subproof.

HB.end.

HB.factory Record FiniteClosed_isAccessible T & Topological T := {
  finite_closed_subproof : forall (A : set T), finite_set A -> closed A
}.
HB.builders Context T & FiniteClosed_isAccessible T.

Let finite_closed_accessible : is_accessible_space T.
Proof.
move=> x y xy.
by exists (~` [set y]); rewrite !inE/=; split;
  [rewrite openC; exact: finite_closed_subproof|exact/eqP|].
Qed.

HB.instance Definition _ := 
  Topological_isAccessible.Build T finite_closed_accessible.

HB.end.

Section accessible_theory.
Context (T : accessibleType).

Lemma closed_set1 (x : T) : closed [set x].
Proof.
rewrite -[X in closed X]setCK; apply: open_closedC.
rewrite openE => y /eqP /accessible_space [U [oU yU xU]].
rewrite /interior nbhsE /=; exists U; last by rewrite subsetC1.
by split=> //; exact: set_mem.
Qed.

Lemma finite_set_closed (A : set T) :
  finite_set A -> closed A.
Proof.
move=> fA; rewrite -(fsbig_setU_set1 fA) fsbig_finite//=.
by apply: bigsetU_closed => x xA; exact: closed_set1.
Qed.

Lemma limit_point_closed (A : set T) : closed (limit_point A).
Proof.
rewrite -openC openE/= => a.
rewrite /setC/= not_limit_pointE => -[X].
rewrite nbhsE/= => -[U oaU UX] XAa.
rewrite /interior nbhsE/=.
exists U => // x Ux /=.
rewrite not_limit_pointE.
have [xa|xneqa] := eqVneq x a.
  exists U; rewrite xa; first exact: open_nbhs_nbhs.
  by apply: subset_trans XAa; exact: setIS.
exists (U `&` [set~ a]).
  apply: open_nbhs_nbhs; split.
    apply: openI; first by case: oaU.
    by rewrite openC; exact: closed_set1.
  by split => //; exact/eqP.
apply: (@subset_trans _ (A `&` (X `&` [set~ a]))).
  by apply: setIS; exact: setSI.
apply: (@subset_trans _ ([set a] `&` [set~ a])).
  by rewrite setIA; exact: setSI.
by rewrite setICr.
Qed.
End accessible_theory.

HB.mixin Record Accessible_isHausdorff T & Accessible T := {
  hausdorff_space : is_hausdorff_space T
}.

#[short(type="hausdorffType")]
HB.structure Definition Hausdorff :=
  {T of Accessible T & Accessible_isHausdorff T}.

#[short(type="phausdorffType")]
HB.structure Definition PHausdorff :=
  {T of Pointed T & Hausdorff T}.

Section hausdorff_theory.
Context (T : hausdorffType).

Lemma compact_closed (A : set T) : compact A -> closed A.
Proof.
move=> Aco p clAp; have pA := [elaborate @withinT _ (nbhs p) A _].
have [q [Aq clsAp_q]] := [elaborate Aco _ _ pA]. 
rewrite (hausdorff_space p q) //.
by apply: cvg_cluster clsAp_q; apply: cvg_within.
Qed.

Lemma compact_cluster_set1 (x : T) F V :
  compact V -> nbhs x V -> 
  ProperFilter F -> F V -> cluster F = [set x] -> F --> x.
Proof.
move=> cptV nxV PF FV clFx1 U nbhsU; rewrite nbhs_simpl.
wlog oU : U nbhsU / open U.
  rewrite /= nbhsE in nbhsU; case: nbhsU => O oO OsubU /(_ O) WH.
  by apply: (filterS OsubU); apply: WH; [exact: open_nbhs_nbhs | by case: oO].
have /compact_near_coveringP : compact (V `\` U).
  apply: (subclosed_compact _ cptV) => //.
  by apply: closedI; [exact: compact_closed | exact: open_closedC].
move=> /(_ _ (powerset_filter_from F) (fun W x => ~ W x))[].
  move=> z [Vz ?]; have zE : x <> z by move/nbhs_singleton: nbhsU => /[swap] ->.
  have : ~ cluster F z by move: zE; apply: contra_not; rewrite clFx1 => ->.
  case/existsNP=> C /existsPNP [D] FC /existsNP [Dz] /nonemptyPn.
  rewrite setIC => /disjoints_subset CD0; exists (D, [set W | F W /\ W `<=` C]).
    by split; rewrite //= nbhs_simpl; exact: powerset_filter_fromP.
  by case => t W [Dt] [FW] /subsetCP; apply; apply: CD0.
move=> M [MF ME2 [W] MW /(_ _ MW) VUW].
apply: (@filterS _ _ _ (V `&` W)); last by apply: filterI => //; exact: MF.
by move=> t [Vt Wt]; apply: contrapT => Ut; exact: (VUW t).
Qed.

Lemma compact_precompact (A : set T) :
  compact A -> precompact A.
Proof.
by move=> c; rewrite precompactE -(closure_id _).1//; exact: compact_closed.
Qed.

Lemma open_hausdorff (x y : T) : x != y ->
    exists2 AB, (x \in AB.1 /\ y \in AB.2) &
                [/\ open AB.1, open AB.2 & AB.1 `&` AB.2 == set0].
Proof. by move: x y; apply/open_hausdorffP; exact: hausdorff_space. Qed.

End hausdorff_theory.

HB.factory Record Topological_isHausdorff T & Topological T := {
  hausdorff_space_subproof : is_hausdorff_space T
}.
HB.builders Context T & Topological_isHausdorff T.

Let hausdorff_accessible : is_accessible_space T.
Proof.
move: hausdorff_space_subproof => /open_hausdorffP + x y => /[apply].
move=> [[U V] [xU yV]] [/= ? ? /eqP].
rewrite setIC => /disjoints_subset VUc; exists U; repeat split => //.
by rewrite inE; apply: VUc; rewrite -inE.
Qed.

HB.instance Definition _ :=
  Topological_isAccessible.Build T hausdorff_accessible.
HB.instance Definition _ :=
  Accessible_isHausdorff.Build T hausdorff_space_subproof.

HB.end.

HB.factory Record Topological_isOpenHausdorff T & Topological T := {
  open_hausdorff_subproof : forall (x y : T), x != y ->
    exists2 AB, (x \in AB.1 /\ y \in AB.2) &
            [/\ open AB.1, open AB.2 & AB.1 `&` AB.2 == set0]
}.
HB.builders Context T & Topological_isOpenHausdorff T.

Let hausdorff : forall x y : T, cluster (nbhs x) y -> x = y.
Proof.
move=> x y.
apply: contraPP => /eqP /open_hausdorff_subproof[[/=A B]].
rewrite !inE => - [xA yB] [Aopen Bopen /eqP AIB_eq0].
move=> /(_ A B (open_nbhs_nbhs _) (open_nbhs_nbhs _)).
by rewrite -set0P => /(_ _ _)/negP; apply.
Qed.

HB.instance Definition _ := Topological_isHausdorff.Build T hausdorff.

HB.end.