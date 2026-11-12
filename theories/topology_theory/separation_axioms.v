(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot finmap all_classical.
From mathcomp Require Import topology_structure connected.

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.

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

Lemma set_nbhs_subsetP (B : set T) : set_nbhs B <-> (A `<=` B°).
Proof. by []. Qed.

Lemma open_set_nbhs (B : set T) : open B -> A `<=` B -> set_nbhs B.
Proof. by move=> /interior_id {1}<-. Qed.

End set_nbhs.

Section point_separation_axioms.
Implicit Type (T : topologicalType).

Definition kolmogorov_space T := forall x y, x != y ->
  exists A : set T, (nbhs x A /\ ~ A y) \/ (nbhs y A /\ ~ A x).

Definition accessible_space T := forall x y, x != y ->
  exists A : set T, [/\ open A, A x & ~ A y].

Definition hausdorff_space T := forall x y : T, x != y ->
  exists (A B : set T), [/\
    nbhs x A, nbhs y B & [disjoint A & B]
  ].

Definition regular_space T :=
  forall (x : T) (F : set T), closed F -> (~ F x) ->
    exists (A B : set T), [/\
      nbhs x A, set_nbhs F B & [disjoint A & B]
    ].

Definition normal_space T :=
  forall A : set T, closed A -> 
    forall U, set_nbhs A U ->
      exists2 V, set_nbhs A V & closure V `<=` U.

End point_separation_axioms.
Arguments kolmogorov_space : clear implicits.
Arguments accessible_space : clear implicits.
Arguments hausdorff_space : clear implicits.
Arguments regular_space : clear implicits.
Arguments normal_space : clear implicits.

Section separation_equivalences.
Context (T : topologicalType).

Lemma set1_accessibleP : 
  accessible_space T  <-> (forall x : T, closed [set x]). 
Proof.
split=> [T1 x|cs1 x y xy].
  rewrite -[X in closed X]setCK; apply: open_closedC.
  rewrite openE => y /eqP /T1 [U [oU yU xU]].
  rewrite /interior nbhsE /=; exists U => //.
  by apply: subsetCr => ? ->.
exists [set~ y]; split=> [||//=]; last by apply/eqP.
by apply: closed_openC.
Qed.

Lemma cluster_hausdorffP : 
  hausdorff_space T <->
  (forall x y : T, cluster (nbhs x) y -> x = y).
Proof.
split; last first.
  contra => -[x [y xy nsep]].
  by exists x, y => // A B /nsep /[apply] /set0P.
contra => -[x [y nsep xy]].
exists x, y => // A B /nsep /[apply].
by contra=> /disj_setPLR.
Qed.

Lemma open_hausdorffP :
  hausdorff_space T <->
  forall (x y : T), x != y -> exists (A B : set T), 
    [/\ open_nbhs x A, open_nbhs y B & [disjoint A & B]].
Proof.
split=> + x y => /[apply] -[A [B [An Bn dAB]]]; last first.
  by exists A, B; split=> //; apply: open_nbhs_nbhs.
exists A°, B°; split; [by split=> //; exact: open_interior .. |].
move: dAB; rewrite -!(rwP disj_setPS); apply: subset_trans.
by apply: setISS; exact: interior_subset.
Qed.

Lemma open_normalP :
  normal_space T <->
  forall (A : set T), closed A ->
    forall U, open U -> A `<=` U ->
      exists V, [/\ open V, A `<=` V & closure V `<=` U].
Proof.
apply/propeqP/eq_forall => A; apply/eq_forall => cA.
apply/propeqP; split=> [hnb U oU AU|ho U AU].
- have [|V AV cVU]:= hnb U; first by apply: open_set_nbhs.
  exists V°; split=> //; first exact: open_interior.
  by apply: subset_trans cVU; apply: closureS; exact: interior_subset.
- have [|V [oV AV cVUo]] := ho U° _ AU; first exact: open_interior.
  exists V; first by apply: open_set_nbhs.
  apply: (subset_trans cVUo); exact: interior_subset.
Qed.

Lemma closed_normalP :
  normal_space T <->
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

End separation_equivalences.

Section separation_implications.
Context (T : topologicalType).

Lemma accessible_kolmogorov : accessible_space T -> kolmogorov_space T.
Proof.
move=> + x y xy => /(_ _ _ xy)[A [oA xA yNA]].
exists A; left; split=> //.
by apply: open_nbhs_nbhs.
Qed.

Lemma hausdorff_accessible : hausdorff_space T -> accessible_space T.
Proof.
move=> /open_hausdorffP T2 x y xy.
have [A [B [[oA Ax] [oB By] dAB]]] := T2 x y xy.
by exists A; split=> //; apply/(disj_setPRL dAB).
Qed.

Lemma urysohn_hausdorff : urysohn_space T -> hausdorff_space T.
Proof.
move=> T2h; apply/open_hausdorffP => x y xy.
have [[A B] /= [cA cB An Bn dAB]] := T2h x y xy.
exists (A°, B°) => //=; split; [exact: open_interior..|].
move: dAB; rewrite !inE -!subset0; apply: subset_trans.
by apply: setISS; exact: interior_subset.
Qed.

Lemma regular_kolmogorov_hausdorff :
  regular_space T -> kolmogorov_space T -> hausdorff_space T.
Proof.
move=> Reg Kol; apply/open_hausdorffP => x y xy.
have [V hV] := Kol x y xy.
wlog [Vox nVy] : x y xy {hV} / nbhs x V /\ ~ V y.
  move=> lcase.
  case: hV => [/(lcase _ _ xy) //|/lcase].
  rewrite eq_sym => /(_ xy) [[X Y] /= [? ?] [? ? ?]].
  by exists (Y, X) => //=; split=> //; rewrite disj_set_sym.
have [|//|A [B [An Bn dAB]]] := Reg x (~` V°).
  by apply: open_closedC; exact: open_interior.
exists (A°, B°) => /=; split=> //; try exact: open_interior.
- by apply: Bn => /interior_subset /nVy.
- by rewrite inE -interiorI; move: dAB => /disj_set2P ->; rewrite interior0.
Qed.

Lemma regular_kolmogorov_urysohn :
  regular_space T -> kolmogorov_space T -> urysohn_space T.
Proof.
move=> /[dup] R /regular_kolmogorov_hausdorff /[apply] + x y xy.
move=> /open_hausdorffP/(_ _ _ xy)[[A B] /= [Ax By] [oA oB dAB]].
have [U [V [Un cAV dUV]]] := R x (~` A) (open_closedC oA) ltac:(done).
exists (closure U, closure B); split=> //=.
- exact: closed_closure.
- exact: closed_closure.
- apply: filterS Un; exact: subset_closure.
- by apply: (filterS (@subset_closure _ B)); apply: open_nbhs_nbhs.
apply/disj_setPRL; apply: (@subset_trans _ V°).
  apply: subset_trans cAV.
  have -> : ~` A = closure (~` A) by apply/closure_id/open_closedC.
  by apply/closureS/disj_setPRL.
by rewrite -interiorC; apply/interiorS/disj_setPRL.
Qed.

Lemma completely_normal_normal : 
  completely_normal_space T -> normal_space T.
Proof.
move=> CN. 
apply/closed_normalP => A B /closure_id cA /closure_id cB /disj_set2P dAB.
by apply: CN; rewrite /separated -cA -cB.
Qed.

Lemma perfectly_normal_completely_normal :
  perfectly_normal_space T -> completely_normal_space T.
Proof.
move=> [NT closed_Gd] A B [cAB0 AcB0].
gen have trim_cover : A {cAB0 AcB0} / forall U_ V_ : (set T)^nat,
    (forall n, open (U_ n)) -> A `<=` \bigcup_n U_ n ->
    (forall n, [disjoint closure (V_ n) & A]) ->
    A `<=` \bigcup_n (U_ n `\` closure (\bigcup_(m < n.+1) V_ m)).
  move=> U_ V_ oU AU dVA x /[dup] Ax /AU[n _ Unx]; exists n => //.
  rewrite setDE -interiorC setC_bigcup; split=> //.
  gen have : {Unx} / forall U : (set T)^nat, 
      \bigcap_(i < n.+1) (U i)° `<=` (\bigcap_(i < n.+1) U i)°.
    move=> U; rewrite -open_subsetE.
      by apply: bigcap_open => ?; exact: open_interior.
    by apply: subset_bigcap => ? _; exact: interior_subset.
  apply=> i i_n; rewrite interiorC.
  by apply/disj_setPRL; first exact: dVA.
wlog suff sep_cover : A B AcB0 cAB0 / exists (O : nat -> set T), [/\
      forall n, open (O n),
      forall n, [disjoint closure (O n) & B] &
      A `<=` \bigcup_n O n
    ].
  have [U [oU dUB AU]] := sep_cover A B AcB0 cAB0.
  have [||V [oV dVA BV]] := sep_cover B A; [by rewrite setIC ..|].
  eexists (_, _); split=> /=.
  - apply: open_set_nbhs (trim_cover A U V oU AU dVA).
    apply: bigcup_open => i _; apply: openI => //.
    by apply: closed_openC; exact: closed_closure.
  - apply: open_set_nbhs (trim_cover B V U oV BV dUB).
    apply: bigcup_open => i _; apply: openI => //.
    by apply: closed_openC; exact: closed_closure.
  rewrite inE setI_bigcup -bigcup_setX.
  apply: bigcup0 => [[i j] /= _].
  case: (leqP i j) => [ij|ji].
  - rewrite setDE setIA setIAC [X in X `&` _]setIAC.
    rewrite (_ : U i `&` _ = set0) ?set0I //.
    rewrite -[LHS]setDE setD_eq0.
    apply: subset_trans; last exact: subset_closure.
    by apply: bigcup_sup; rewrite /= ltnS.
  - rewrite !setDE (setIC (U i)) setIACA (_ : _ `&` V _ = set0) ?set0I //.
    rewrite setIC -setDE setD_eq0.
    apply: subset_trans; last exact: subset_closure.
    by apply: bigcup_sup; rewrite /= ltnS ltnW.
clear trim_cover.
have [U oU BU] := closed_Gd (closure B) (@closed_closure _ _).
have : forall i : nat, exists V, 
    [/\ open V, closure B `<=` V & closure V `<=` U i].
  move=> i.
  have [|V cBV cVU] := NT (closure B) (@closed_closure _ _) (U i).
    by apply: open_set_nbhs => //; rewrite BU; exact: bigcap_inf.
  exists V°; split=> //; first exact: open_interior.
  by apply: subset_trans cVU; apply: closureS; exact: interior_subset.
case/choice => [V_ /all_and3[oV cBV cOV]].
exists (fun i => ~` closure (V_ i)); split.
- by move=> ?; apply: closed_openC; exact: closed_closure.
- move=> n; rewrite closureC; apply/disj_setPCr.
  apply: subset_trans; first exact: subset_closure.
  apply: (subset_trans (cBV n)); rewrite -open_subsetE //.
  exact: subset_closure.
- move: AcB0 => /disj_set2P/disj_setPLR/subset_trans; apply.
  rewrite -setC_bigcap subsetCP BU.
  by apply: subset_bigcap.
Qed.

End separation_implications.

(* Kolmogorov spaces (T_0) *)
HB.mixin Record Topological_isKolmogorov T & Topological T := {
  kolmogorovP : kolmogorov_space T
}.

#[short(type="kolmogorovType")]
HB.structure Definition Kolmogorov := 
  {T of Topological T & Topological_isKolmogorov T}.

Hint Extern 0 (kolmogorov_space _) => solve [apply: kolmogorovP] : core.

(* Accessible spaces (Fréchet/T_1) *)
HB.mixin Record Kolmogorov_isAccessible T & Kolmogorov T := {
  accessibleP : accessible_space T
}.

#[short(type="accessibleType")]
HB.structure Definition Accessible :=
  {T of Kolmogorov T & Kolmogorov_isAccessible T}.

Hint Extern 0 (accessible_space _) => solve [apply: accessibleP] : core.

HB.factory Record Topological_isAccessible T & Topological T := {
  accessibleP_subproof : accessible_space T
}.
HB.builders Context T & Topological_isAccessible T.

HB.instance Definition _ := 
  Topological_isKolmogorov.Build T (accessible_kolmogorov accessibleP_subproof).
HB.instance Definition _ :=
  Kolmogorov_isAccessible.Build T accessibleP_subproof.

HB.end.

(* Hausdorff spaces (T_2) *)
HB.mixin Record Accessible_isHausdorff T & Accessible T := {
  hausdorffP : hausdorff_space T
}.

#[short(type="hausdorffType")]
HB.structure Definition Hausdorff :=
  {T of Accessible T & Accessible_isHausdorff T}.

#[short(type="phausdorffType")]
HB.structure Definition PHausdorff :=
  {T of Pointed T & Hausdorff T}.

Hint Extern 0 (hausdorff_space _) => solve [apply: hausdorffP] : core.

HB.factory Record Topological_isHausdorff T & Topological T := {
  hausdorffP_subproof : hausdorff_space T
}.
HB.builders Context T & Topological_isHausdorff T.

HB.instance Definition _ :=
  Topological_isAccessible.Build T (hausdorff_accessible hausdorffP_subproof).
HB.instance Definition _ :=
  Accessible_isHausdorff.Build T hausdorffP_subproof.

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

(* Urysohn spaces (T_2 1/2) *)
HB.mixin Record Hausdorff_isUrysohn T & Hausdorff T := {
  urysohnP : urysohn_space T
}.

#[short(type="urysohnType")]
HB.structure Definition Urysohn := 
  {T of Hausdorff T & Hausdorff_isUrysohn T}.

Hint Extern 0 (urysohn_space _) => solve [apply: urysohnP] : core.

HB.factory Record Topological_isUrysohn T & Topological T := {
  urysohnP_subproof : urysohn_space T
}.
HB.builders Context T & Topological_isUrysohn T.

HB.instance Definition _ := 
  Topological_isHausdorff.Build T (urysohn_hausdorff urysohnP_subproof).
HB.instance Definition _ := Hausdorff_isUrysohn.Build T urysohnP_subproof.

HB.end.

(* Regular and regular Hausdorff spaces (R and T_3) *)
HB.mixin Record Topological_isRegular T & Topological T := {
  regularP : regular_space T
}.

#[short(type="regularType")]
HB.structure Definition Regular := 
  {T of Topological T & Topological_isRegular T}.

#[short(type="regularHausdorffType")]
HB.structure Definition RegularHausdorff :=
  {T of Urysohn T & Regular T}.

Hint Extern 0 (regular_space _) => solve [apply: regularP] : core.

HB.factory Record Topological_isRegularHausdorff T & Topological T := {
  kolmogorovP_subproof : kolmogorov_space T ;
  regularP_subproof : regular_space T
}.
HB.builders Context T & Topological_isRegularHausdorff T.

Let urysohn := 
  regular_kolmogorov_urysohn regularP_subproof kolmogorovP_subproof.

HB.instance Definition _ := Topological_isRegular.Build T regularP_subproof.
HB.instance Definition _ := Topological_isUrysohn.Build T urysohn.

HB.end.

(* Uniform/Completely regular spaces *)
Local Open Scope relation_scope.

Definition nbhs_ {T T'} (ent : set_system (T * T')) (x : T) :=
  filter_from ent (fun A => xsection A x).

Lemma nbhs_E {T T'} (ent : set_system (T * T')) x :
  nbhs_ ent x = filter_from ent (fun A => xsection A x).
Proof. by []. Qed.

HB.mixin Record Regular_isUniform T & Regular T := {
  entourage : set_system (T * T);
  entourage_filter : Filter entourage;
  entourage_diagonal_subproof :
    forall A, entourage A -> diagonal `<=` A;
  entourage_inv_subproof : forall A, entourage A -> entourage A^-1;
  entourage_split_ex_subproof :
    forall A, entourage A -> exists2 B, entourage B & B \; B `<=` A;
  nbhsE_subproof : nbhs = nbhs_ entourage;
}.

#[short(type="uniformType")]
HB.structure Definition Uniform := 
  {T of Regular T & Regular_isUniform T}.

#[short(type="puniformType")]
HB.structure Definition PointedUniform := 
  {T of Pointed T & Uniform T}.

#[short(type="tychonoffType")]
HB.structure Definition Tychonoff := 
  {T of Uniform T & RegularHausdorff T}.

Lemma nbhs_entourageE {M : uniformType} : nbhs_ (@entourage M) = nbhs.
Proof. by rewrite -Regular_isUniform.nbhsE_subproof. Qed.

Section split_ent.
Context {M : uniformType}.

Lemma entourage_refl (A : set (M * M)) x : entourage A -> A (x, x).
Proof. by move=> entA; exact: entourage_diagonal_subproof entA _ _. Qed.

Lemma entourage_inv (A : set (M * M)) : entourage A -> entourage A^-1.
Proof. exact: entourage_inv_subproof. Qed.

Lemma entourage_split_ex (A : set (M * M)) :
  entourage A -> exists2 B, entourage B & B \; B `<=` A.
Proof. exact: entourage_split_ex_subproof. Qed.

Definition split_ent (A : set (M * M)) :=
  get (entourage `&` [set B | B \; B `<=` A]).

Lemma split_entP (A : set (M * M)) : entourage A ->
  entourage (split_ent A) /\ split_ent A \; split_ent A `<=` A.
Proof. by move/entourage_split_ex/exists2P/getPex. Qed.

Lemma entourage_split_ent (A : set (M * M)) : entourage A ->
  entourage (split_ent A).
Proof. by case/split_entP. Qed.

Lemma subset_split_ent (A : set (M * M)) : entourage A ->
  split_ent A \; split_ent A `<=` A.
Proof. by case/split_entP. Qed.

Lemma entourage_split (z x y : M) A : entourage A ->
  split_ent A (x, z) -> split_ent A (z, y) -> A (x, y).
Proof. by move=> /subset_split_ent sA ? ?; apply: sA; exists z. Qed.

Lemma split_ent_subset (E : set (M * M)) : entourage E -> split_ent E `<=` E.
Proof.
move=> entE; case=> x y splitxy; apply: subset_split_ent => //; exists y => //.
by apply: entourage_refl; exact: entourage_split_ent.
Qed.

End split_ent.

HB.factory Record Topological_isUniform T & Topological T := {
  entourage : set_system (T * T);
  entourage_filter : Filter entourage;
  entourage_diagonal :
    forall A, entourage A -> diagonal `<=` A;
  entourage_inv : forall A, entourage A -> entourage A^-1;
  entourage_split_ex :
    forall A, entourage A -> exists2 B, entourage B & B \; B `<=` A;
  nbhsE : nbhs = nbhs_ entourage
}.
HB.builders Context T & Topological_isUniform T.

Let regular : regular_space T.
Proof.
move=> x F /closed_openC + /[dup] nFx.
rewrite openE /interior {1}nbhsE/= => /[apply] -[U eU /subsetCPr FUx].
have [V eV VV] := entourage_split_ex eU.
exists (xsection V x), (\bigcup_(y in F) ysection V y); split.
- by rewrite nbhsE; exists V.
- move=> y Fy; rewrite nbhsE; exists V^-1; first by apply: entourage_inv.
  by apply: bigcup_sup.
- apply/disj_setPS => z [/set_mem Vxz [y /FUx nUxy /set_mem Uzy]] /=.
  apply: nUxy; rewrite /xsection /= inE; apply: VV.
  by exists z.
Qed.

HB.instance Definition _ := Topological_isRegular.Build T regular.
HB.instance Definition _ := Regular_isUniform.Build T
  entourage_filter entourage_diagonal entourage_inv entourage_split_ex nbhsE.

HB.end.

HB.factory Record Nbhs_isUniform_mixin T & Nbhs T := {
  entourage : set_system (T * T);
  entourage_filter : Filter entourage;
  entourage_diagonal_subproof :
    forall A, entourage A -> diagonal `<=` A;
  entourage_inv_subproof : forall A, entourage A -> entourage A^-1;
  entourage_split_ex_subproof :
    forall A, entourage A -> exists2 B, entourage B & B \; B `<=` A;
  nbhsE_subproof : nbhs = nbhs_ entourage;
}.
HB.builders Context T & Nbhs_isUniform_mixin T.

Local Instance ent_filter : Filter entourage.
Proof. exact: entourage_filter. Qed.

Let nbhs_filter (x : T) : ProperFilter (nbhs x).
Proof.
rewrite nbhsE_subproof.
apply: Build_ProperFilter_ex => [P [U eU UP]|].
  exists x; apply: UP; rewrite xsectionP.
  by apply: entourage_diagonal_subproof.
apply: filter_from_filter; first by exists setT; exact: filterT.
move=> U V eU eV; exists (U `&` V); first by apply: filterI.
by rewrite xsectionI.
Qed.

Let nbhs_singleton (x : T) A : nbhs x A -> A x.
Proof.
rewrite nbhsE_subproof => -[U /entourage_diagonal_subproof dU].
by apply; rewrite xsectionP; apply: dU.
Qed.
  
Let nbhs_nbhs (x : T) A : nbhs x A -> nbhs x (nbhs^~ A).
Proof.
rewrite !nbhsE_subproof => -[U eU UA].
have [V eV VV] := entourage_split_ex_subproof eU.
exists V => // y /xsectionP Vyx. 
exists V => // z /xsectionP Vyz.
by apply: UA; apply/xsectionP/VV; exists y.
Qed.

HB.instance Definition _ := Nbhs_isNbhsTopological.Build T
  nbhs_filter nbhs_singleton nbhs_nbhs.
HB.instance Definition _ := Topological_isUniform.Build T 
  entourage_filter entourage_diagonal_subproof entourage_inv_subproof
  entourage_split_ex_subproof nbhsE_subproof.

HB.end.

HB.factory Record isUniform T & Choice T := {
  entourage : set_system (T * T);
  entourage_filter : Filter entourage;
  entourage_diagonal : forall A, entourage A -> diagonal `<=` A;
  entourage_inv : forall A, entourage A -> entourage A^-1;
  entourage_split_ex :
    forall A, entourage A -> exists2 B, entourage B & B \; B `<=` A;
}.
HB.builders Context T & isUniform T.

HB.instance Definition _ := @hasNbhs.Build T (nbhs_ entourage).
HB.instance Definition _ := Nbhs_isUniform_mixin.Build T
  entourage_filter entourage_diagonal entourage_inv entourage_split_ex
  erefl.

HB.end.

HB.factory Record Uniform_isTychonoff T & Uniform T := {
  kolmogorovP : kolmogorov_space T
}.
HB.builders Context T & Uniform_isTychonoff T.

Let urysohn : urysohn_space T.
Proof.
move=> x y /kolmogorovP[X hX].
wlog [+ nXy] : x y {hX} / nbhs x X /\ ~ X y.
  case: hX => /[swap] /[apply] // -[[A B] /= [? ? ? ? ?]].
  by exists (B, A); split=> //=; rewrite disj_set_sym.
rewrite -nbhs_entourageE => -[/= U eU UX].
have [V eV V3] : exists2 V : set (T * T), 
    entourage V & (V \; V) \; (V \; V) `<=` U.
  exists (split_ent (split_ent U)); first by repeat apply: entourage_split_ent.
  apply: subset_trans; last exact: subset_split_ent.
  have esU : entourage (split_ent U) by apply: entourage_split_ent.
  by apply: set_compose_subset; apply: subset_split_ent.
exists (closure (xsection V x), closure (xsection V^-1 y)); split=> /=.
- exact: closed_closure.
- exact: closed_closure.
- exists V => //; exact: subset_closure.
- exists V^-1; first by apply: entourage_inv.
  exact: subset_closure.
apply/disj_setPS => z [].
have Vnz : nbhs z (xsection V z) by rewrite -nbhs_entourageE; exists V.
have V1nz : nbhs z (xsection V^-1 z).
  rewrite -nbhs_entourageE; exists V^-1 => //.
  by apply: entourage_inv.
move=> /(_ _ V1nz) [/= t [+ +]] /(_ _ Vnz) [/= u [+ +]].
rewrite !xsectionE /= => Vxt Vtz Vuy Vzu.
apply/nXy/UX/xsectionP/V3.
by exists z => /=; [exists t|exists u].
Qed.

HB.instance Definition _ := Topological_isUrysohn.Build T urysohn.

HB.end.

(* Normal/Normal Hausdorff spaces (N/T_4) *)
HB.mixin Record Topological_isNormal T & Topological T := {
  normalP : normal_space T
}.

#[short(type="normalType")]
HB.structure Definition Normal :=
  {T of Topological T & Topological_isNormal T}.

#[short(type="normalRegularType")]
HB.structure Definition NormalRegular :=
  {T of Normal T & Uniform T}.

#[short(type="normalHausdorffType")]
HB.structure Definition NormalHausdorff :=
  {T of NormalRegular T & Tychonoff T}.

Hint Extern 0 (normal_space _) => solve [apply: normalP] : core.

(* Normal & Regular => NormalRegular is deferred due to needing
   Urysohn's lemma *)

(* Completely normal/Completely normal Hausdorff spaces (CN/T_5) *)
HB.mixin Record Normal_isCompletelyNormal T & Normal T := {
  completely_normalP : completely_normal_space T
}.

#[short(type="completelyNormalType")]
HB.structure Definition CompletelyNormal :=
  {T of Normal T & Normal_isCompletelyNormal T}.

#[short(type="completelyNormalRegularType")]
HB.structure Definition CompletelyNormalRegular :=
  {T of CompletelyNormal T & NormalRegular T}.

#[short(type="completelyNormalHausdorffType")]
HB.structure Definition CompletelyNormalHausdorff :=
  {T of CompletelyNormal T & NormalHausdorff T}.

Hint Extern 0 (completely_normal_space _)
  => solve [apply: completely_normalP] : core.

HB.factory Record Topological_isCompletelyNormal T & Topological T := {
  completely_normalP : completely_normal_space T
}.
HB.builders Context T & Topological_isCompletelyNormal T.

HB.instance Definition _ := Topological_isNormal.Build T
  (completely_normal_normal completely_normalP).
HB.instance Definition _ := 
  Normal_isCompletelyNormal.Build T completely_normalP.

HB.end.

(* Perfectly normal/Perfectly normal Hausdorff spaces (PN/T_6) *)
HB.mixin Record CompletelyNormalRegular_isPerfectlyNormal T 
    & CompletelyNormalRegular T := {
  perfectly_normalP : perfectly_normal_space T
}.

#[short(type="perfectlyNormalType")]
HB.structure Definition PerfectlyNormal :=
  {T of CompletelyNormalRegular T 
    & CompletelyNormalRegular_isPerfectlyNormal T}.

#[short(type="perfectlyNormalHausdorffType")]
HB.structure Definition PerfectlyNormalHausdorff := 
  {T of PerfectlyNormal T & CompletelyNormalHausdorff T}.

Hint Extern 0 (perfectly_normal_space _)
  => solve [apply: perfectly_normalP] : core.

(* Topological_isPerfectlyNormal is also deferred due to needing to
   prove uniformizability *)

(* ---------------- *)

(* Theorem of Kolmogorov spaces *)

Section kolmogorov_ind.
Context (P : topologicalType -> Prop).
Hypothesis hKol : forall T : kolmogorovType, P T.

HB.declare Context (T : Type) & Topological T.
Hypothesis kT : kolmogorov_space T.

Lemma kolmogorov_ind_ : P T.
Proof.
pose T' : kolmogorovType := HB.pack T (Topological_isKolmogorov.Build T kT).
exact: (hKol T').
Qed.
 
End kolmogorov_ind.

Lemma kolmogorov_ind (P : topologicalType -> Prop) :
  (forall T : kolmogorovType, P T) ->
  forall T, kolmogorov_space T -> P T.
Proof. by move=> hKol [T []] >; apply: kolmogorov_ind_. Qed.

(* Theory of accessible spaces *)

Section accessible_theory.
Context (T : accessibleType).

Lemma closed_set1 (x : T) : closed [set x].
Proof.
rewrite -[X in closed X]setCK; apply: open_closedC.
rewrite openE => y /eqP /accessibleP[U [oU yU xU]].
rewrite /interior nbhsE /=; exists U; last by rewrite subsetC1 inE.
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

Section accessible_ind.
Context (P : topologicalType -> Prop).
Hypothesis hAcc : forall T : accessibleType, P T.

HB.declare Context (T : Type) & Topological T.
Hypothesis aT : accessible_space T.

Lemma accessible_ind_ : P T.
Proof.
pose T' : accessibleType := HB.pack T (Topological_isAccessible.Build T aT).
exact: (hAcc T').
Qed.
 
End accessible_ind.

Lemma accessible_ind (P : topologicalType -> Prop) :
  (forall T : accessibleType, P T) ->
  forall T, accessible_space T -> P T.
Proof. by move=> hAcc [T []] >; apply: accessible_ind_. Qed.

(* Theory of Hausdorff spaces *)

Section hausdorff_theory.
Context (T : hausdorffType).

Lemma open_hausdorff (x y : T) : x != y ->
    exists2 AB, (x \in AB.1 /\ y \in AB.2) &
                [/\ open AB.1, open AB.2 & AB.1 `&` AB.2 == set0].
Proof. 
move: (@hausdorffP T) => /open_hausdorffP /[apply] -[AB ABxy hAB].
by exists AB => //; rewrite !inE.
Qed.

Lemma open_separator_ex (x : T) : 
  exists (UV : (T -> set T) * (T -> set T)), forall y, y != x ->
    [/\ open_nbhs x (UV.1 y), open_nbhs y (UV.2 y) & 
      [disjoint UV.1 y & UV.2 y]].
Proof.
apply/(exists_pairfunP (fun f g => forall y, _ -> 
  [/\ _ _ (f y), _ _ (g y) & [disjoint f y & g y]]
)).
apply/ex_of_sigT/(cond_choice _ (fun y UV => 
  [/\ _ x UV.1, _ y UV.2 & [disjoint UV.1 & UV.2]])
) => y yx /=.
have /open_hausdorffP/(_ y x yx) := @hausdorffP T.
case=> [[/= U V] [Uy Vx] [oU oV dUV]].
by exists (V, U); split=> //=; rewrite disj_set_sym.
Qed.

Lemma nbhs_separator_ex (x : T) : 
  exists (UV : (T -> set T) * (T -> set T)), forall y, y != x ->
    [/\ nbhs x (UV.1 y), nbhs y (UV.2 y) & 
      [disjoint UV.1 y & UV.2 y]].
Proof.
have [UV hUV] := open_separator_ex x.
exists UV => y /hUV[Ux Vy dUV].
by split=> //; apply: open_nbhs_nbhs.
Qed.

End hausdorff_theory.

Definition close (T : topologicalType) (x y : T) : Prop := 
  forall M, open_nbhs y M -> closure M x.

Section close_theory.
Context (T : topologicalType).
Implicit Types x y : T.

Local Open Scope classical_set_scope.

Lemma closeEnbhs x : close x = cluster (nbhs x).
Proof.
transitivity (cluster (open_nbhs x)); last first.
  by rewrite /cluster; under eq_fun do rewrite -meets_openl.
rewrite clusterEonbhs /close funeqE => y /=; rewrite meetsC /meets.
apply/eq_forall => A; rewrite forall_swap.
by rewrite closureEonbhs/= meets_globallyl.
Qed.

Lemma closeEonbhs x : close x = [set y | open_nbhs x `#` open_nbhs y].
Proof.
by rewrite closeEnbhs; under eq_fun do rewrite -meets_openl -meets_openr.
Qed.

Lemma close_sym x y : close x y -> close y x.
Proof. by rewrite !closeEnbhs /cluster/= meetsC. Qed.

Lemma cvg_close {F} {FF : ProperFilter F} x y : F --> x -> F --> y -> close x y.
Proof.
by move=> /sub_meets sx /sx; rewrite closeEnbhs; apply; apply/proper_meetsxx.
Qed.

Lemma close_refl x : close x x.
Proof. exact: (@cvg_close (nbhs x)). Qed.
Hint Resolve close_refl : core.

Lemma cvgx_close x y : x --> y -> close x y.
Proof. exact: cvg_close. Qed.

Lemma cvgi_close T' {F} {FF : ProperFilter F} (f : T' -> set T) (l l' : T) :
  {near F, is_fun f} -> f `@ F --> l -> f `@ F --> l' -> close l l'.
Proof.
move=> f_prop fFl fFl'.
suff f_totalfun: {near F, is_totalfun f}.
  by apply: cvg_close fFl fFl'; exact: fmapi_proper_filter.
apply: filter_app f_prop; near do split=> //=.
have: (f `@ F) setT by apply: fFl; apply: filterT.
by rewrite fmapiE; apply: filterS => x [y []]; exists y.
Unshelve. all: by end_near. Qed.

End close_theory.

Section hausdorff_close.
Context (T : hausdorffType).
Implicit Types x y : T.

Lemma closeE x y : close x y = (x = y).
Proof.
rewrite propeqE; split; last by move=> ->; exact: close_refl.
by rewrite closeEnbhs; exact: hausdorffP.
Qed.

Lemma close_eq x y : close x y -> x = y.
Proof. by rewrite closeE. Qed.

Lemma cvg_unique {F} {FF : ProperFilter F} : is_subset1 [set x : T | F --> x].
Proof. move=> Fx Fy; rewrite -closeE //; exact: (@cvg_close _ F). Qed.

Lemma cvg_eq x y : x --> y -> x = y.
Proof. by rewrite -closeE //; apply: cvg_close. Qed.

Lemma cvgi_unique {U : Type} {F} {FF : ProperFilter F} (f : U -> set T) :
  {near F, is_fun f} -> is_subset1 [set x : T | f `@ F --> x].
Proof. by move=> ffun fx fy; rewrite -closeE //; exact: cvgi_close. Qed.

End hausdorff_close.

Lemma close_cvg (T : ptopologicalType) 
    (F1 F2 : set_system T) {FF2 : ProperFilter F2} :
  F1 --> F2 -> F2 --> F1 -> close (lim F1) (lim F2).
Proof.
move=> F12 F21.
have [/(cvg_trans F21) F2l|dvgF1] := pselect (cvg F1).
  by apply (@cvg_close _ F2) => //; apply: cvgP F2l.
have [/(cvg_trans F12)/cvgP//|dvgF2] := pselect (cvg F2).
rewrite dvgP // dvgP //; exact/close_refl.
Qed.
Arguments close_cvg {T} F1 F2 {FF2} _.

Section phausdorff_theory.
Context (T : phausdorffType).
Implicit Types x y : T.

Lemma cvg_lim {F} {FF : ProperFilter F} (l : T) :
  F --> l -> lim F = l.
Proof. by move=> /[dup] /cvgP /cvg_unique; apply. Qed.

Lemma lim_id x : lim (nbhs x) = x.
Proof. exact: cvg_lim. Qed.

Lemma lim_near_cst {U} {F} {FF : ProperFilter F} (l : T) (f : U -> T) :
   (\forall x \near F, f x = l) -> lim (f @ F) = l.
Proof. by move=> /cvg_near_cst/cvg_lim. Qed.

Lemma lim_cst {U} {F} {FF : ProperFilter F} (k : T) : lim (@cst U _ k @ F) = k.
Proof. exact: cvg_lim. Qed.

Lemma cvgi_lim {U} {F} {FF : ProperFilter F} (f : U -> T -> Prop) (l : T) :
  F (fun x : U => is_subset1 (f x)) ->
  f `@ F --> l -> lim (f `@ F) = l.
Proof.
by move=> f_prop fl; apply: get_unique =>// l' fl'; exact: cvgi_unique _ fl' fl.
Qed.

End phausdorff_theory.
#[global] Hint Resolve close_refl : core.

Section hausdorff_ind.
Context (P : topologicalType -> Prop).
Hypothesis hHau : forall T : hausdorffType, P T.

HB.declare Context (T : Type) & Topological T.
Hypothesis hT : hausdorff_space T.

Lemma hausdorff_ind_ : P T.
Proof.
pose T' : hausdorffType := HB.pack T (Topological_isHausdorff.Build T hT).
exact: (hHau T').
Qed.
 
End hausdorff_ind.

Lemma hausdorff_ind (P : topologicalType -> Prop) :
  (forall T : hausdorffType, P T) ->
  forall T, hausdorff_space T -> P T.
Proof. by move=> hHau [T []] >; apply: hausdorff_ind_. Qed.

(* Theory of Urysohn spaces *)

Section urysohn_theory.
Context (T : urysohnType).

Lemma closed_separator_ex (x : T) : 
  exists (UV : (T -> set T) * (T -> set T)), forall y, y != x ->
    [/\ closed (UV.1 y), closed (UV.2 y),
      nbhs x (UV.1 y), nbhs y (UV.2 y) &
      [disjoint UV.1 y & UV.2 y]].
Proof.
apply/(exists_pairfunP (fun f g => forall y, _ ->
  [/\ _ (f y), _ (g y), _ (f y), _ (g y) & [disjoint f y & g y]]
)).
apply/ex_of_sigT/(cond_choice _ (fun y UV => 
  [/\ _ UV.1, _ UV.2, _ UV.1, _ UV.2 & [disjoint UV.1 & UV.2]])
) => y yx /=.
have [[U V] /= [*]] := urysohnP y x yx.
by exists (V, U); split=> //=; rewrite disj_set_sym.
Qed.

End urysohn_theory.

Section urysohn_ind.
Context (P : topologicalType -> Prop).
Hypothesis hUry : forall T : urysohnType, P T.

HB.declare Context (T : Type) & Topological T.
Hypothesis uT : urysohn_space T.

Lemma urysohn_ind_ : P T.
Proof.
pose T' : urysohnType := HB.pack T (Topological_isUrysohn.Build T uT).
exact: (hUry T').
Qed.
 
End urysohn_ind.

Lemma urysohn_ind (P : topologicalType -> Prop) :
  (forall T : urysohnType, P T) ->
  forall T, urysohn_space T -> P T.
Proof. by move=> hUry [T []] >; apply: urysohn_ind_. Qed.

(* Theory of regular spaces *)

Section regular_theory.
Context (T : regularType).

Lemma regular_separator_ex (F : set T) : closed F ->
  exists (UV : (T -> set T) * (T -> set T)), forall x, ~ F x ->
    [/\ nbhs x (UV.1 x), set_nbhs F (UV.2 x) & [disjoint UV.1 x & UV.2 x]].
Proof.
move=> cF.
apply/(exists_pairfunP (fun f g => forall x, _ ->
  [/\ _ (f x), _ (g x) & [disjoint f x & g x]]
)).
apply/ex_of_sigT/(cond_choice _ (fun x UV => 
  [/\ _ UV.1, _ UV.2 & [disjoint UV.1 & UV.2]]
)) => /= x nFx.
by have /exists_existsP := regularP x F cF nFx.
Qed.

End regular_theory.

Section regular_ind.
Context (P : topologicalType -> Prop).
Hypothesis hReg : forall T : regularType, P T.

HB.declare Context (T : Type) & Topological T.
Hypothesis rT : regular_space T.

Lemma regular_ind_ : P T.
Proof.
pose T' : regularType := HB.pack T (Topological_isRegular.Build T rT).
exact: (hReg T').
Qed.
 
End regular_ind.

Lemma regular_ind (P : topologicalType -> Prop) :
  (forall T : regularType, P T) ->
  forall T, regular_space T -> P T.
Proof. by move=> hReg [T []] >; apply: regular_ind_. Qed.

(*
Section subspace_hausdorff.
Context (T : hausdorffType) (A : set T).

Let subspace_hausdorff : hausdorff_space (subspace A).
Proof.
have := @hausdorff_space T.
rewrite !open_hausdorffP => + x y xNy => /(_ x y xNy).
move=> [[P Q]] /= [Px Qx] /= [/open_subspaceW oP /open_subspaceW oQ].
by move=> ?; exists (P, Q); split => //=; [exact: oP | exact: oQ].
Qed.

HB.instance Definition _ := 
  Topological_isHausdorff.Build (subspace A) subspace_hausdorff.

End subspace_hausdorff.

(*
Lemma discrete_hausdorff {T : discreteTopologicalType} : hausdorff_space T.
Proof.
by move=> p q /(_ _ _ (discrete_set1 p) (discrete_set1 q)) [] // x [] -> ->.
Qed.

Lemma order_hausdorff {d} {T : orderTopologicalType d} : hausdorff_space T.
Proof.
rewrite open_hausdorff=> p q; wlog : p q / (p < q)%O.
  have /orP[] := le_total p q; rewrite le_eqVlt => /predU1P[->|].
  - by rewrite eqxx.
  - by move=> ?; exact.
  - by rewrite eqxx.
  - move=> qp WH; rewrite eq_sym => /(WH _ _ qp)[[P Q] [? ?] [? ? ?]].
    by exists (Q, P); split; rewrite // setIC.
move=> plq ?; have [[z /andP[pz zq]]|] := pselect (exists z, p < z < q)%O.
  exists (`]-oo,z[, `]z,+oo[)%classic.
    by split => //=; apply/mem_set; rewrite set_itvE.
  split => //= ; apply/eqP; rewrite -subset0 => r; rewrite set_itvE => -[/= rz].
  by apply/negP; rewrite in_itv/= andbT -leNgt (ltW rz).
move=> npzq; exists (`]-oo, q[, `]p, +oo[)%classic; split => //=.
- by apply /mem_set; rewrite set_itvE.
- by apply /mem_set; rewrite set_itvE.
- apply/eqP; rewrite -subset0 => r; rewrite !set_itvE => -[/= rz zr].
  by apply: npzq; exists r; rewrite rz zr.
Qed.

Section ball_hausdorff.
Variables (R : numDomainType) (T : pseudoMetricType R).

Lemma ball_hausdorff : hausdorff_space T =
  forall (a b : T), a != b ->
  exists r : {posnum R} * {posnum R},
    ball a r.1%:num `&` ball b r.2%:num == set0.
Proof.
rewrite propeqE open_hausdorff; split => T2T a b /T2T[[/=]].
  move=> A B; rewrite 2!inE => [[aA bB] [oA oB /eqP ABeq0]].
  have /nbhs_ballP[_/posnumP[r] rA]: nbhs a A by apply: open_nbhs_nbhs.
  have /nbhs_ballP[_/posnumP[s] rB]: nbhs b B by apply: open_nbhs_nbhs.
  by exists (r, s) => /=; rewrite (subsetI_eq0 _ _ ABeq0).
move=> r s /eqP brs_eq0; exists ((ball a r%:num)°, (ball b s%:num)°) => /=.
  split; by rewrite inE; apply: nbhs_singleton; apply: nbhs_interior;
            apply/nbhs_ballP; apply: in_filter_from => /=.
split; do ?by apply: open_interior.
by rewrite (subsetI_eq0 _ _ brs_eq0)//; exact: interior_subset.
Qed.
End ball_hausdorff.

Import numFieldTopology.Exports.
Lemma Rhausdorff (R : realFieldType) : hausdorff_space R.
Proof. exact: order_hausdorff. Qed.

Lemma one_point_compactification_hausdorff {X : topologicalType} :
   locally_compact [set: X] ->
   hausdorff_space X ->
   hausdorff_space (one_point_compactification X).
Proof.
move=> lcpt hsdfX [x|] [y|] //=.
- move=> clxy; congr Some; apply: hsdfX => U V Ux Vy.
  have [] := clxy (Some @` U) (Some @` V).
    by apply: filterS Ux; exact: preimage_image.
    by apply: filterS Vy; exact: preimage_image.
  by case=> [_|] [] /= [// p /[swap] -[] <- Up] [q /[swap] -[] -> Vp]; exists p.
- have [U] := lcpt x I; rewrite withinET => Ux [cU clU].
  case/(_ (Some @` U) (Some @` (~` U) `|` [set None])).
  + exact: one_point_compactification_some_nbhs.
  + by exists U.
  + by move=> [?|] [][]// z /[swap] -[] <- ? []//= [? /[swap] -[] ->].
- have [U] := lcpt y I; rewrite withinET => Uy [cU clU].
  case/(_ (Some @` (~` U) `|` [set None]) (Some @` U)); first by exists U.
    exact: one_point_compactification_some_nbhs.
  by case=> [?|] [] [] //= + [] ? // /[swap] -[] -> => -[? /[swap] -[] <-].
Qed.*)



Section close_uniform.
Implicit Types (U : uniformType).

Lemma entourage_close {U} (x y : U) :
  close x y = forall A, entourage A -> A (x, y).
Proof.
rewrite propeqE; split=> [cxy A entA|cxy].
  have /entourage_split_ent entsA := entA; rewrite closeEnbhs in cxy.
  have yl := nbhs_entourage _ (entourage_inv entsA).
  have yr := nbhs_entourage _ entsA.
  have [z [/xsectionP zx /xsectionP zy]] := cxy _ _ (yr x) (yl y).
  exact: (entourage_split z).
rewrite closeEnbhs => A B /nbhsP[E1 entE1 sE1A] /nbhsP[E2 entE2 sE2B].
exists y; split.
- by apply/sE1A/xsectionP; exact: cxy.
- by apply/sE2B/xsectionP; exact: entourage_refl.
Qed.

Lemma close_trans {U} (y x z : U) : close x y -> close y z -> close x z.
Proof.
rewrite !entourage_close => cxy cyz A entA.
exact: entourage_split (cxy _ _) (cyz _ _).
Qed.

Lemma close_cvgxx {U} (x y : U) : close x y -> x --> y.
Proof.
rewrite entourage_close => cxy P /= /nbhsP[A entA sAP].
apply/nbhsP; exists (split_ent A) => // z /xsectionP xz; apply: sAP.
apply/xsectionP; apply: (entourage_split x) => //.
by have := cxy _ (entourage_inv (entourage_split_ent entA)).
Qed.

Lemma cvg_closeP {U : puniformType} (F : set_system U) (l : U) :
    ProperFilter F ->
  F --> l <-> ([cvg F in U] /\ close (lim F) l).
Proof.
move=> FF; split=> [Fl|[cvF]Cl].
  by have /cvgP := Fl; split=> //; apply: (@cvg_close _ F).
by apply: cvg_trans (close_cvgxx Cl).
Qed.

Lemma ball_close {R : numFieldType} {M : pseudoMetricType R} (x y : M) :
  close x y = forall eps : {posnum R}, ball x eps%:num y.
Proof.
rewrite propeqE; split => [cxy eps|cxy].
  have := [elaborate cxy _ (open_nbhs_ball _ (eps%:num/2)%:pos)].
  rewrite closureEonbhs/= meetsC meets_globallyr.
  move/(_ _ (open_nbhs_ball _ (eps%:num/2)%:pos)) => [z [zx zy]].
  by apply: (@ball_splitl _ _ z); apply: interior_subset.
rewrite closeEnbhs => B A /nbhs_ballP[_/posnumP[e2 e2B]]
  /nbhs_ballP[_/posnumP[e1 e1A]].
by exists y; split; [apply/e2B|apply/e1A; exact: ballxx].
Qed.
End close_uniform.



Section set_separations.
Context {T : topologicalType}.

Definition normal_space :=
  forall A : set T, closed A ->
    filter_from (set_nbhs A) closure `=>` set_nbhs A.

Definition regular_space :=
  forall a : T, filter_from (nbhs a) closure --> a.

Lemma compact_regular (x : T) V : hausdorff_space T -> compact V ->
  nbhs x V -> {for x, regular_space}.
Proof.
move=> sep cptv Vx; apply: (@compact_cluster_set1 T x _ V) => //.
- apply: filter_from_proper => //; first last.
    by move=> ? /nbhs_singleton/subset_closure ?; exists x.
  apply: filter_from_filter; first by exists setT; exact: filterT.
  move=> P Q Px Qx; exists (P `&` Q); [exact: filterI | exact: closureI].
- by exists V => //; have /closure_id <- : closed V by exact: compact_closed.
rewrite eqEsubset; split; first last.
  move=> _ -> A B [C Cx CA /nbhs_singleton Bx]; exists x; split => //.
  by apply/CA/subset_closure; exact: nbhs_singleton.
move=> y /=; apply: contraPeq; move: sep; rewrite open_hausdorff => /[apply].
move=> [[B A]]/=; rewrite ?inE; case=> By Ax [oB oA BA0].
apply/existsNP; exists (closure A); apply/existsNP; exists B; apply/not_implyP.
split; first by exists A => //; exact: open_nbhs_nbhs.
apply/not_implyP; split; first exact: open_nbhs_nbhs.
apply/set0P/negP; rewrite negbK; apply/eqP/disjoints_subset.
have /closure_id -> : closed (~` B); first by exact: open_closedC.
by apply/closureS/disjoints_subset; rewrite setIC.
Qed.

Lemma compact_normal_local (K : set T) : hausdorff_space T -> compact K ->
  forall A : set T, A `<=` K° -> {for A, normal_space}.
Proof.
move=> hT cptV A AK clA B snAB; have /compact_near_coveringP cvA : compact A.
  apply/(subclosed_compact clA cptV)/(subset_trans AK).
  exact: interior_subset.
have snbC (U : set T) : Filter (filter_from (set_nbhs U) closure).
  apply: filter_from_filter; first by exists setT; apply: filterT.
  by move=> P Q sAP sAQ; exists (P `&` Q); [apply filterI|exact: closureI].
have [/(congr1 setC)|/set0P[b0 B0]] := eqVneq (~` B) set0.
  by rewrite setCK setC0 => ->; exact: filterT.
have PsnA : ProperFilter (filter_from (set_nbhs (~` B)) closure).
  apply: filter_from_proper => ? P.
  by exists b0; apply/subset_closure; apply: nbhs_singleton; exact: P.
pose F := powerset_filter_from (filter_from (set_nbhs (~` B)) closure).
have PF : Filter F by exact: powerset_filter_from_filter.
have cvP (x : T) : A x -> \forall x' \near x & i \near F, (~` i) x'.
  move=> Ax; case/set_nbhsP : snAB => C [oC AC CB].
  have [] := @compact_regular x _ hT cptV _ C; first exact: AK.
    by rewrite nbhsE /=; exists C => //; split => //; exact: AC.
  move=> D /nbhs_interior nD cDC.
  have snBD : filter_from (set_nbhs (~` B)) closure (closure (~` closure D)).
    exists (closure (~` closure D)) => [z|].
      move=> nBZ; apply: filterS; first exact: subset_closure.
      apply: open_nbhs_nbhs; split; first exact/closed_openC/closed_closure.
      exact/(subsetC _ nBZ)/(subset_trans cDC).
    by have := @closed_closure _ (~` closure D); rewrite closure_id => <-.
  near=> y U => /=; have Dy : D° y by exact: (near nD _).
  have UclD : U `<=` closure (~` closure D).
    exact: (near (small_set_sub snBD) U).
  move=> Uy; have [z [/= + Dz]] := UclD _ Uy _ Dy.
  by apply; exact: subset_closure.
case/(_ _ _ _ _ cvP) : cvA => R /= [RA Rmono [U RU] RBx].
have [V /set_nbhsP [W [oW cBW WV] clVU]] := RA _ RU; exists (~` W).
  apply/set_nbhsP; exists (~` closure W); split.
  - exact/closed_openC/closed_closure.
  - by move=> y /(RBx _ RU) + Wy; apply; exact/clVU/(closureS WV).
  - by apply: subsetC; exact/subset_closure.
have : closed (~` W) by exact: open_closedC.
by rewrite closure_id => <-; exact: subsetCl.
Unshelve. all: by end_near. Qed.

Lemma compact_normal : hausdorff_space T -> compact [set: T] -> normal_space.
Proof.
move=> ? /compact_normal_local + A clA; apply => //.
by move=> z ?; exact: filterT.
Qed.

End set_separations.

Arguments normal_space : clear implicits.
Arguments regular_space : clear implicits.

Local Open Scope relation_scope.
Lemma uniform_regular {T : uniformType} : @regular_space T.
Proof.
move=> x R /=; rewrite -{1}nbhs_entourageE => -[E entE ER].
pose E' := split_ent E; have eE' : entourage E' by exact: entourage_split_ent.
exists (xsection (E' `&` E'^-1) x).
  rewrite -nbhs_entourageE; exists (E' `&` E'^-1) => //.
  exact: filterI.
move=> z /= clEz; apply/ER/xsectionP; apply: subset_split_ent => //.
have [] := clEz (xsection (E' `&` E'^-1) z).
  rewrite -nbhs_entourageE; exists (E' `&` E'^-1) => //.
  exact: filterI.
by move=> y /= [/xsectionP[? ?] /xsectionP[? ?]]; exists y.
Qed.
Local Close Scope relation_scope.

#[global] Hint Resolve uniform_regular : core.

Section totally_disconnected.
Implicit Types T : topologicalType.

Definition totally_disconnected {T} (A : set T) :=
  forall x, A x -> connected_component A x = [set x].

Definition zero_dimensional T :=
  (forall x y, x != y -> exists U : set T, [/\ clopen U, U x & ~ U y]).

Lemma discrete_zero_dimension {T : discreteTopologicalType} : zero_dimensional T.
Proof.
move=> x y xny; exists [set x]; split => //; last exact/nesym/eqP.
by split; [exact: discrete_open | exact: discrete_closed].
Qed.

Lemma zero_dimension_totally_disconnected {T} :
  zero_dimensional T -> totally_disconnected [set: T].
Proof.
move=> zdA x _; rewrite eqEsubset.
split=> [z [R [Rx _ ctdR Rz]]|_ ->]; last exact: connected_component_refl.
apply: contrapT => /eqP znx; have [U [[oU cU] Uz Ux]] := zdA _ _  znx.
suff : R `&` U = R by move: Rx => /[swap] <- [].
by apply: ctdR; [exists z|exists U|exists U].
Qed.

Lemma zero_dimensional_cvg {T} (x : T) :
  hausdorff_space T -> zero_dimensional T -> compact [set: T] ->
  filter_from [set D : set T | D x /\ clopen D] id --> x.
Proof.
pose F := filter_from [set D : set T | D x /\ clopen D] id.
have FF : Filter F.
  apply: filter_from_filter; first by exists setT; split => //; exact: clopenT.
  by move=> A B [? ?] [? ?]; exists (A `&` B) => //; split=> //; exact: clopenI.
have PF : ProperFilter F by apply: filter_from_proper; move=> ? [? _]; exists x.
move=> hsdfT zdT cmpT U Ux; rewrite nbhs_simpl -/F.
wlog oU : U Ux / open U.
  move: Ux; rewrite /= nbhsE => -[] V [? ?] /filterS + /(_ V) P.
  by apply; apply: P => //; exists V.
have /(iffLR (compact_near_coveringP _)) : compact (~` U).
  by apply: (subclosed_compact _ cmpT) => //; exact: open_closedC.
move=> /(_ _ _ setC (powerset_filter_from_filter PF))[].
  move=> y nUy; have /zdT [C [[oC cC] Cx Cy]] : x != y.
    by apply: contra_notN nUy => /eqP <-; exact: nbhs_singleton.
  exists (~` C, [set U | U `<=` C]); first split.
  - by apply: open_nbhs_nbhs; split => //; exact: closed_openC.
  - apply/near_powerset_filter_fromP; first by move=> ? ?; exact: subset_trans.
    by exists C => //; exists C.
  - by case=> i j [? /subsetC]; apply.
by move=> D [DF _ [C DC]]/(_ _ DC)/subsetC2/filterS; apply; exact: DF.
Qed.

Lemma zero_dimensional_ray {d} {T : orderTopologicalType d} (x y : T) :
  (x < y)%O -> zero_dimensional T ->
  exists U, [/\ clopen U, U y , ~ U x & forall l r, U r -> ~ U l -> l < r]%O.
Proof.
move=> xy zt; have xNy : y != x by move: xy; rewrite lt_def => /andP[].
have [U [clU Uy nUx]] := zt y x xNy.
have := clopen_bigcup_clopen clU Uy; set I := (I in clopen I); case=> ? ?.
pose V := I `|` `[y, +oo[; have Iy : I y.
  case: clU => + _; rewrite openE => /(_ _ Uy).
  rewrite /interior /= itv_nbhsE /= => -[i [] iy yi iU].
  by exists i => //; split => //; exact: itv_open_ends_open.
have IU : I `<=` U by move=> ? [? [+ _ _]] => /subset_trans; exact.
exists V; split; first split.
- suff -> : V = I `|` `]y,+oo[ by exact: openU.
  have /mem_set := Iy; rewrite -sub1set => /setUidl <-.
  by rewrite -setUA setU1itv.
- by apply: closedU => //; exact: rray_closed.
- by left.
- by move=> [/IU //|]; rewrite set_itvE/= leNgt xy.
- move=> l r Vr Vl; rewrite ltNge; apply/negP; move: Vl; apply: contra_not.
  move=> rl; case: Vr; first last.
    by rewrite set_itvE => yr; right; rewrite set_itvE; exact: (le_trans yr).
  have /orP[|ly] := le_total y l; first by move=> + _; right; rewrite set_itvE.
  case=> i [iu oi /= yi ri]; left; exists i; first by split.
  move: iu oi => _ _; case: i yi ri => p q /= /andP [py yq] /andP[pr rq].
  apply/andP; split.
  + by rewrite (le_trans pr)// bnd_simp.
  + by rewrite (le_trans _ yq)// bnd_simp.
Qed.

End totally_disconnected.

Section perfect_sets.

Implicit Types (T : topologicalType).

Definition perfect_set {T} (A : set T) := closed A /\ limit_point A = A.

Lemma perfectP {T} (A : set T) :
  perfect_set A <-> closed A /\ isolated A = set0.
Proof.
split=> [[cA limA]|[cA isoA]]; have := closure_isolated_limit_point A.
- move=> /(congr1 (fun x => x `\` limit_point A)).
  rewrite setUDK.
    by apply/disj_setPS; rewrite disj_set_sym disjoint_isolated_limit_point.
  by rewrite limA -(closure_id A).1// setDv.
- by rewrite isoA set0U -(closure_id A).1.
Qed.

Lemma perfectTP {T} : perfect_set [set: T] <-> forall x : T, ~ open [set x].
Proof.
split.
  case=> _; rewrite eqEsubset; case=> _ + x Ox => /(_ x I [set x]).
  by (case; [by apply: open_nbhs_nbhs; split |]) => y [+ _] => /[swap] -> /eqP.
move=> NOx; split; [exact: closedT |]; rewrite eqEsubset; split => x // _.
move=> U; rewrite nbhsE; case=> V [] oV Vx VU.
have Vnx: V != [set x] by apply/eqP => M; apply: (NOx x); rewrite -M.
have /existsNP [y /existsNP [Vy Ynx]] : ~ forall y, V y -> y = x.
  move/negP: Vnx; apply: contra_not => Vxy; apply/eqP; rewrite eqEsubset.
  by split => // ? ->.
by exists y; split => //; [exact/eqP | exact: VU].
Qed.

Lemma perfectTP_ex {T} : perfect_set [set: T] <->
  forall (U : set T), open U -> U !=set0 ->
  exists x y, [/\ U x, U y & x != y] .
Proof.
apply: (iff_trans perfectTP); split.
  move=> nx1 U oU [] x Ux; exists x.
  have : U <> [set x] by move=> Ux1; apply: (nx1 x); rewrite -Ux1.
  apply: contra_notP => /not_existsP/contrapT=> Uyx; rewrite eqEsubset.
  by split => [y Uy|? ->//]; have /not_and3P[//|//|/negP/negPn/eqP] := Uyx y.
move=> Unxy x Ox; have [] := Unxy _ Ox; first by exists x.
by move=> y [] ? [->] -> /eqP.
Qed.

End perfect_sets.

Section sigT_separations.
Context {I : choiceType} {X : I -> topologicalType}.

Lemma sigT_hausdorff :
  (forall i, hausdorff_space (X i)) -> hausdorff_space {i & X i}.
Proof.
move=> hX [i x] [j y]; rewrite/cluster /= /nbhs /= 2!sigT_nbhsE /= => cl.
have [] := cl (existT X i @` [set: X i]) (existT X j @` [set: X j]);
  [by apply: existT_nbhs; exact: filterT..|].
move=> p [/= [_ _ <-] [_ _ [ji]]] _.
rewrite {}ji {j} in x y cl *.
congr existT; apply: hX => U V Ux Vy.
have [] := cl (existT X i @` U) (existT X i @` V); [exact: existT_nbhs..|].
move=> z [] [l Ul <-] [r Vr lr]; exists l; split => //.
by rewrite -(existT_inj2 lr).
Qed.

End sigT_separations.

*)