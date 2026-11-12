(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra finmap.
From mathcomp Require Import all_classical.
From mathcomp Require Import interval_inference reals topology_structure
  separation_axioms.

(**md**************************************************************************)
(* # Compactness                                                              *)
(* This file provides various formulations of compactness, and some theory.   *)
(*                                                                            *)
(* ```                                                                        *)
(*                  cluster F == set of cluster points of F                   *)
(*                    compact == set of compact sets w.r.t. the filter-based  *)
(*                               definition of compactness                    *)
(*              near_covering == a reformulation of covering compact better   *)
(*                               suited for use with `near`                   *)
(*       near_covering_within == equivalent definition of near_covering       *)
(*             compact_near F == the filter F contains a closed compact set   *)
(*               precompact A == A is contained in a closed compact set       *)
(*          locally_compact A == every point in A has a compact (and closed)  *)
(*                               neighborhood                                 *)
(*  finite_subset_cover D F A == the family of sets F is a cover of A         *)
(*                               for a finite number of indices in D          *)
(*              cover_compact == set of compact sets w.r.t. the open          *)
(*                               cover-based definition of compactness        *)
(*          open_fam_of A D f == the family of f indexed by D restricted to A *)
(*                               is a family of open sets                     *)
(*        closed_fam_of A D f == the family of f indexed by D restricted to A *)
(*                               is a family of closed sets                   *)
(*                                                                            *)
(* ```                                                                        *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* infer class to help typeclass inference on the fly *)
Class infer (P : Prop) := Infer : P.
#[export] Hint Mode infer ! : typeclass_instances.
#[export] Hint Extern 0 (infer _) => (exact) : typeclass_instances.
Lemma inferP (P : Prop) : P -> infer P. Proof. by []. Qed.

Section Compact.
Context {T : topologicalType}.

Definition compact A := forall (F : set_system T),
  ProperFilter F -> F A -> A `&` cluster F !=set0.

Lemma compact0 : compact set0.
Proof. by move=> F FF /filter_ex []. Qed.

Lemma subclosed_compact (A B : set T) :
  closed A -> compact B -> A `<=` B -> compact A.
Proof.
move=> Acl Bco sAB F Fproper FA.
have [|p [Bp Fp]] := Bco F; first exact: filterS FA.
by exists p; split=> //; apply: Acl=> C Cp; apply: Fp.
Qed.

Typeclasses Opaque within.
Global Instance within_nbhs_proper (A : set T) p :
  infer (closure A p) -> ProperFilter (within A (nbhs p)).
Proof.
move=> clAp; apply: Build_ProperFilter_ex => B.
by move=> /clAp [q [Aq AqsoBq]]; exists q; apply: AqsoBq.
Qed.

Lemma compact_set1 (x : T) : compact [set x].
Proof.
move=> F PF Fx; exists x; split; first by [].
move=> P B nbhsB; exists x; split; last exact: nbhs_singleton.
suff [y [Py <-//]] : P `&` [set x] !=set0.
by apply: filter_ex; [exact: PF| exact: filterI].
Qed.

Lemma compact_closedI (A B : set T) :
  compact A -> closed B -> compact (A `&` B).
Proof.
move=> cptA clB F PF FAB; have FA : F A by move: FAB; exact: filterS.
(have FB : F B by move: FAB; apply: filterS); have [x [Ax]] := cptA F PF FA.
move=> /[dup] clx; rewrite {1}clusterE => /(_ (closure B)); move: clB.
by rewrite closure_id => /[dup] + <- => <- /(_ FB) Bx; exists x.
Qed.
End Compact.

Section near_covering.
Context {X : topologicalType}.

Definition near_covering (K : set X) :=
  forall (I : Type) (F : set_system I) (P : I -> X -> Prop),
  Filter F ->
  (forall x, K x -> \forall x' \near x & i \near F, P i x') ->
  \forall i \near F, K `<=` P i.

Let near_covering_compact : near_covering `<=` compact.
Proof.
move=> K locK F PF FK; apply/set0P/eqP=> KclstF0; case: (PF) => + FF; apply.
rewrite -(setICr K); apply: filterI => //.
have /locK : forall x, K x ->
    \forall x' \near x & i \near powerset_filter_from F, (~` i) x'.
  move=> x Kx; have : ~ cluster F x.
    by apply: contraPnot KclstF0 => clstFx; apply/eqP/set0P; exists x.
  move=> /existsNP [U /existsNP [V /not_implyP [FU /not_implyP [nbhsV]]]] UV0.
  near=> x' W => //= => Wx'; apply: UV0; exists x'.
  by split; [exact: (near (small_set_sub FU) W) | exact: (near nbhsV x')].
case=> G [GF Gdown [U GU]] GP; apply: (@filterS _ _ _ U); last exact: GF.
by move=> y Uy Ky; exact: (GP _ GU y Ky).
Unshelve. all: end_near. Qed.

Let compact_near_covering : compact `<=` near_covering.
Proof.
move=> K cptK I F P FF cover.
pose badPoints := fun U => K `\` [set x | K x /\ U `<=` P ^~ x].
pose G := filter_from F badPoints.
have FG : Filter G.
  apply: filter_from_filter; first by exists setT; exact: filterT.
  move=> L R FL FR; exists (L `&` R); first exact: filterI.
  rewrite /badPoints /= !setDIr !setDv !set0U -setDUr; apply: setDS.
  by move=> ? [|] => + ? [? ?]; exact.
have [[V FV]|G0] := pselect (G set0).
  rewrite subset0 setD_eq0 => subK.
  by apply: (@filterS _ _ _ V) => // ? ? ? /subK [?]; exact.
have PG : ProperFilter G by [].
have GK : G K by exists setT; [exact: filterT | move=> ? []].
case: (cptK _ PG GK) => x [Kx].
have [[/= U1 U2] [U1x FU2 subP]] := cover x Kx.
have GP : G (badPoints (P ^~ x `&` U2)).
  apply: filterI => //; exists (P ^~ x `&` U2); last by move=> ? [].
  near=> i; split; last exact: (near FU2 i).
  by apply: (subP (x, i)); split; [exact: nbhs_singleton|exact: (near FU2 i)].
move=> /(_ _ _ GP U1x) => [[x'[]]][] Kx' /[swap] U1x'.
by case; split => // i [? ?]; exact: (subP (x', i)).
Unshelve. end_near. Qed.

Lemma compact_near_coveringP A : compact A <-> near_covering A.
Proof.
by split; [exact: compact_near_covering| exact: near_covering_compact].
Qed.

Definition near_covering_within (K : set X) :=
  forall (I : Type) (F : set_system I) (P : I -> X -> Prop),
  Filter F ->
  (forall x, K x -> \forall x' \near x & i \near F, K x' -> P i x') ->
  \forall i \near F, K `<=` P i.

Lemma near_covering_withinP (K : set X) :
  near_covering_within K <-> near_covering K.
Proof.
split => cvrW I F P FF cvr; near=> i;
    (suff: K `<=` fun q : X => K q -> P i q by move=> + k Kk; exact); near: i.
  by apply: cvrW => x /cvr; apply: filter_app; near=> j.
have := cvrW _ _ (fun i q => K q -> P i q) FF.
by apply => x /cvr; apply: filter_app; near=> j => + ?; apply.
Unshelve. all: by end_near. Qed.

End near_covering.

Lemma ultra_cvg_clusterE (T : topologicalType) (F : set_system T) :
  UltraFilter F -> cluster F = [set p | F --> p].
Proof.
move=> FU; rewrite predeqE => p; split.
  by rewrite cluster_cvgE => - [G GF [cvGp /max_filter <-]].
by move=> cvFp; rewrite cluster_cvgE; exists F; [apply: ultra_proper|split].
Qed.

Lemma compact_ultra (T : topologicalType) :
  compact = [set A | forall F : set_system T,
  UltraFilter F -> F A -> A `&` [set p | F --> p] !=set0].
Proof.
rewrite predeqE => A; split=> Aco F FF FA.
  by have /Aco [p [?]] := FA; rewrite ultra_cvg_clusterE; exists p.
have [G [GU sFG]] := ultraFilterLemma FF.
have /Aco [p [Ap]] : G A by apply: sFG.
rewrite /= -[_ --> p]/([set _ | _] p) -ultra_cvg_clusterE.
by move=> /(cvg_cluster sFG); exists p.
Qed.

Section Precompact.
Context {X : topologicalType}.

Lemma compactU : setU_closed (@compact X).
Proof.
move=> A B; rewrite compact_ultra => cptA cptB F UF FAB; rewrite setIUl.
have [/cptA[x AFx]|] := in_ultra_setVsetC A UF; first by exists x; left.
move=> /(filterI FAB); rewrite setIUl setICr set0U => FBA.
have /cptB[x BFx] : F B by apply: filterS FBA; exact: subIsetr.
by exists x; right.
Qed.

Lemma bigsetU_compact I (F : I -> set X) (s : seq I) (P : pred I) :
    (forall i, P i -> compact (F i)) ->
  compact (\big[setU/set0]_(i <- s | P i) F i).
Proof. by move=> ?; elim/big_ind : _ =>//; [exact:compact0|exact:compactU]. Qed.

(** The closed condition here is neccessary to make this definition work in a
    non-hausdorff setting. *)
Definition compact_near (F : set_system X) :=
  exists2 U, F U & compact U /\ closed U.

Definition precompact (C : set X) := compact_near (globally C).

Lemma precompactE (C : set X) : precompact C = compact (closure C).
Proof.
rewrite propeqE; split=> [[B CsubB [cptB cB]]|]; last first.
  move=> clC; exists (closure C) => //; first exact: subset_closure.
  by split => //; exact: closed_closure.
apply: (subclosed_compact _ cptB); first exact: closed_closure.
by move/closure_id: cB => ->; exact: closureS.
Qed.

Lemma precompact_subset (A B : set X) :
  A `<=` B -> precompact B -> precompact A.
Proof.
by move=> AsubB [B' B'subB cptB']; exists B' => // ? ?; exact/B'subB/AsubB.
Qed.

Lemma precompact_closed (A : set X) : closed A -> precompact A = compact A.
Proof.
move=> clA; rewrite propeqE; split=> [[B AsubB [ + _ ]]|].
  by move=> /subclosed_compact; exact.
by rewrite {1}(_ : A = closure A) ?precompactE// -closure_id.
Qed.

Definition locally_compact (A : set X) := [locally precompact A].

End Precompact.

Definition finite_subset_cover (I : choiceType) (D : set I)
    U (F : I -> set U) (A : set U) :=
  exists2 D' : {fset I}, {subset D' <= D} & A `<=` cover [set` D'] F.

Section Covers.
Variable T : topologicalType.

Definition cover_compact (A : set T) :=
  forall (I : choiceType) (D : set I) (f : I -> set T),
  (forall i, D i -> open (f i)) -> A `<=` cover D f ->
  finite_subset_cover D f A.

Definition open_fam_of (A : set T) I (D : set I) (f : I -> set T) :=
  exists2 g : I -> set T, (forall i, D i -> open (g i)) &
    forall i, D i -> f i = A `&` g i.

Lemma cover_compactE : cover_compact =
  [set A | forall (I : choiceType) (D : set I) (f : I -> set T),
    open_fam_of A D f ->
      A `<=` cover D f -> finite_subset_cover D f A].
Proof.
rewrite predeqE => A; split=> [Aco I D f [g gop feAg] fcov|Aco I D f fop fcov].
  have gcov : A `<=` \bigcup_(i in D) g i.
    by move=> p /fcov [i Di]; rewrite feAg // => - []; exists i.
  have [D' sD sgcov] := Aco _ _ _ gop gcov.
  exists D' => // p Ap; have /sgcov [i D'i gip] := Ap.
  by exists i => //; rewrite feAg //; have /sD := D'i; rewrite inE.
have Afcov : A `<=` \bigcup_(i in D) (A `&` f i).
  by move=> p Ap; have /fcov [i ??] := Ap; exists i.
have Afop : open_fam_of A D (fun i => A `&` f i) by exists f.
have [D' sD sAfcov] := Aco _ _ _ Afop Afcov.
by exists D' => // p /sAfcov [i ? []]; exists i.
Qed.

Definition closed_fam_of (A : set T) I (D : set I) (f : I -> set T) :=
  exists2 g : I -> set T, (forall i, D i -> closed (g i)) &
    forall i, D i -> f i = A `&` g i.

Lemma compact_In0 :
  compact = [set A | forall (I : choiceType) (D : set I) (f : I -> set T),
    closed_fam_of A D f -> finI D f -> \bigcap_(i in D) f i !=set0].
Proof.
rewrite predeqE => A; split=> [Aco I D f [g gcl feAg] finIf|Aco F FF FA].
  case: (pselectT T) => [/setF_eq0 h0|point].
    move: finIf => /(_ fset0 ltac:(done)).
    by rewrite set_fset0 bigcap_set0 h0 => -[?].
  case: (pselect (exists i, D i)) => [[i Di] | /asboolP]; last first.
    by rewrite asbool_neg => /forallp_asboolPn D0; exists point => ? /D0.
  have [|p [Ap clfinIfp]] := Aco _ (finI_filter finIf).
    by exists (f i); [exact: open_finI_from1|rewrite feAg // => ? []].
  exists p => j Dj; rewrite feAg //; split=> //; apply: gcl => // B.
  apply: clfinIfp.
  by exists (f j); [exact: open_finI_from1|rewrite feAg // => ? []].
have finIAclF : finI F (fun B => A `&` closure B).
  apply: (@filter_finI _ F) => B FB.
  by apply: filterI => //; apply: filterS FB; apply: subset_closure.
have [|p AclFIp] := Aco _ _ _ _ finIAclF.
  by exists closure=> //; move=> ? ?; exact: closed_closure.
exists p; split=> [|B C FB p_C]; first by have /AclFIp [] := FA.
by have /AclFIp [_] := FB; move=> /(_ _ p_C).
Qed.

Lemma compact_cover : compact = cover_compact.
Proof.
rewrite compact_In0 cover_compactE predeqE => A.
split=> [Aco I D f [g gop feAg] fcov|Aco I D f [g gcl feAg]].
  case: (pselect (exists i, D i)) => [[j Dj] | /asboolP]; last first.
    rewrite asbool_neg => /forallp_asboolPn D0.
    by exists fset0 => // ? /fcov [? /D0].
  apply/exists2P; apply: contrapT.
  move=> /asboolP; rewrite asbool_neg => /forallp_asboolPn sfncov.
  suff [p IAnfp] : \bigcap_(i in D) (A `\` f i) !=set0.
    by have /IAnfp [Ap _] := Dj; have /fcov [k /IAnfp [_]] := Ap.
  apply: Aco.
    exists (fun i => ~` g i) => i Di; first exact/open_closedC/gop.
    rewrite predeqE => p; split=> [[Ap nfip] | [Ap ngip]]; split=> //.
      by move=> gip; apply: nfip; rewrite feAg.
    by rewrite feAg // => - [].
  move=> D' sD.
  have /asboolP : ~ A `<=` cover [set` D'] f by move=> sAIf; exact: (sfncov D').
  rewrite asbool_neg => /existsp_asboolPn [p /asboolP].
  rewrite asbool_neg => /imply_asboolPn [Ap nUfp].
  by exists p => i D'i; split=> // fip; apply: nUfp; exists i.
case: (pselectT T) => [/setF_eq0 h0|point].
  move=> /(_ fset0 ltac:(done)).
  by rewrite set_fset0 bigcap_set0 h0 => -[?].
case: (pselect (exists i, D i)) => [[j Dj] | /asboolP]; last first.
  by rewrite asbool_neg => /forallp_asboolPn D0 => _; exists point => ? /D0.
apply: contraPP => /asboolP; rewrite asbool_neg => /forallp_asboolPn If0.
apply/asboolP; rewrite asbool_neg; apply/existsp_asboolPn.
have Anfcov : A `<=` \bigcup_(i in D) (A `\` f i).
  move=> p Ap; have /asboolP := If0 p; rewrite asbool_neg => /existsp_asboolPn.
  move=> [i /asboolP]; rewrite asbool_neg => /imply_asboolPn [Di nfip].
  by exists i.
have Anfop : open_fam_of A D (fun i => A `\` f i).
  exists (fun i => ~` g i) => i Di; first exact/closed_openC/gcl.
  rewrite predeqE => p; split=> [[Ap nfip] | [Ap ngip]]; split=> //.
    by move=> gip; apply: nfip; rewrite feAg.
  by rewrite feAg // => - [].
have [D' sD sAnfcov] := Aco _ _ _ Anfop Anfcov.
wlog [k D'k] : D' sD sAnfcov / exists i, i \in D'.
  move=> /(_ (D' `|` [fset j])%fset); apply.
  - by move=> k; rewrite !inE => /orP [/sD|/eqP->] //; rewrite inE.
  - by move=> p /sAnfcov [i D'i Anfip]; exists i => //=; rewrite !inE D'i.
  - by exists j; rewrite !inE orbC eq_refl.
exists D' => /(_ sD) [p Ifp].
have /Ifp := D'k; rewrite feAg; first by have /sD := D'k; rewrite inE.
by move=> [/sAnfcov [i D'i [_ nfip]] _]; have /Ifp := D'i.
Qed.

End Covers.

Lemma finite_compact {X : topologicalType} (A : set X) :
  finite_set A -> compact A.
Proof.
case/finite_setP=> n; elim: n A => [A|n ih A /eq_cardSP[x Ax /ih ?]].
  by rewrite II0 card_eq0 => /eqP ->; exact: compact0.
by rewrite -(setD1K Ax); apply: compactU => //; exact: compact_set1.
Qed.

Lemma clopen_countable {T : topologicalType}:
  compact [set: T] -> @second_countable T -> countable (@clopen T).
Proof.
move=> cmpT [B /fset_subset_countable cntB] [obase Bbase].
apply/(card_le_trans _ cntB)/pcard_surjP.
pose f := fun F : {fset set T} => \bigcup_(x in [set` F]) x; exists f.
move=> D [] oD cD /=; have cmpt : cover_compact D.
  by rewrite -compact_cover; exact: (subclosed_compact _ cmpT).
have h (x : T) : exists V : set T, D x -> [/\ B V, nbhs x V & V `<=` D].
  have [Dx|] := pselect (D x); last by move=> ?; exists set0.
  have [V [BV Vx VD]] := Bbase x D (open_nbhs_nbhs (conj oD Dx)).
  exists V => _; split => //; apply: open_nbhs_nbhs; split => //.
  exact: obase.
pose h' := fun z => projT1 (cid (h z)).
have [fs fsD DsubC] : finite_subset_cover D h' D.
  apply: cmpt.
  - by move=> z Dz; apply: obase; have [] := projT2 (cid (h z)) Dz.
  - move=> z Dz; exists z => //; apply: nbhs_singleton.
    by have [] := projT2 (cid (h z)) Dz.
exists [fset h' z | z in fs]%fset.
  move=> U/imfsetP [z /=] /fsD /set_mem Dz ->; rewrite inE.
  by have [] := projT2 (cid (h z)) Dz.
rewrite eqEsubset; split => z.
  case=> y /imfsetP [x /= /fsD/set_mem Dx ->]; move: z.
  by have [] := projT2 (cid (h x)) Dx.
move=> /DsubC /= [y /= yfs hyz]; exists (h' y) => //.
by rewrite set_imfset /=; exists y.
Qed.

Section compact_separation.

Section hausdorff.
Context (T : hausdorffType).

Lemma compact_closed (A : set T) : compact A -> closed A.
Proof.
move=> Aco p clAp; have pA := [elaborate @withinT _ (nbhs p) A _].
have [q [Aq clsAp_q]] := [elaborate Aco _ _ pA]. 
rewrite (hausdorffP p q) //.
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

Lemma compact_closed_separation (x : T) (F : set T) :
  compact F -> ~ F x -> exists (U V : set T), [/\
    nbhs x U, set_nbhs F V & [disjoint U & V]
  ].
Proof.
rewrite compact_cover => coF nFx.
have [[U_ V_] /= hUV] := open_separator_ex x.
have F_neq y : F y -> y != x by apply: contraPneq => ->.
have oV_ y : F y -> open (V_ y) by move=> /F_neq /hUV[_ []].
have Fcov : F `<=` cover F V_.
  move=> y Fy; exists y => //.
  apply: nbhs_singleton; apply: open_nbhs_nbhs.
  by apply hUV; apply: F_neq.
have [G GF FcV] := coF T F V_ oV_ Fcov.
exists (\bigcap_(y in [set` G]) U_ y).
exists (\bigcup_(y in [set` G]) V_ y) => /=; split.
- apply: filter_bigI => y /GF /set_mem Fy.
  by apply: open_nbhs_nbhs; apply hUV; apply: F_neq.
- apply: open_set_nbhs => //.
  by apply: bigcup_open => ? /GF /set_mem /oV_.
- apply/disj_setPRL => z [i Gi Vz] /(_ _ Gi).
  have : [disjoint U_ i & V_ i].
    by apply hUV; apply: F_neq; apply/set_mem; apply: GF.
  by move/disj_setPLR/[apply].
Qed.

Lemma hausdorff_compact_regular : 
  compact [set: T] -> regular_space T.
Proof.
move=> cT x F clF nFx.
apply: compact_closed_separation => //.
by apply: (subclosed_compact _ cT).
Qed.

Lemma hausdorff_compact_normal : 
  compact [set: T] -> normal_space T.
Proof.
move=> /[dup] /hausdorff_compact_regular.
apply: (@regular_ind (fun T => compact [set: T] -> normal_space T)).
clear T => T cT.
apply/closed_normalP => A B cA cB dAB.
have [[U_ V_] /= hUV] := regular_separator_ex cA.
have coB : cover_compact B.
  by rewrite -compact_cover; apply: (subclosed_compact _ cT).
have BcA : B `<=` ~` A by apply/disj_setPRL.
have [||] := coB T B (interior \o U_).
- by move=> ? ?; exact: open_interior.
- by move=> x /[dup] Bx /BcA /hUV[Un Vn dUV]; exists x.
move=> C CB Bcov.
exists (\bigcap_(i in [set` C]) V_ i, \bigcup_(i in [set` C]) U_ i); split=> /=.
- by apply: filter_bigI => i /CB /set_mem /BcA /hUV[].
- by apply/set_nbhs_subsetP; apply: (subset_trans Bcov); exact: interior_bigcup.
apply/disj_setPRL => x [i Ci Ux] /(_ i Ci).
by move: Ci => /CB /set_mem /BcA /hUV[_ _] /disj_setPRL /[apply].
Qed.

End hausdorff.

End compact_separation.