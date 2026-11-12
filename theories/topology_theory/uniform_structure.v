(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra all_classical.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import topology_structure compact separation_axioms.

(**md**************************************************************************)
(* # Uniform Spaces                                                           *)
(* This file provides uniform spaces, and their theory. It also includes      *)
(* complete spaces, which extends uniform in the hierarchy.                   *)
(*                                                                            *)
(* ## Mathematical structures                                                 *)
(* ### Uniform                                                                *)
(* ```                                                                        *)
(*                      nbhs_ ent == neighborhoods defined using entourages   *)
(*                    uniformType == interface type for uniform spaces: a     *)
(*                                   type equipped with entourages            *)
(*                                   The HB class is Uniform.                 *)
(*                   puniformType == a pointed and uniform space              *)
(*                      entourage == set of entourages in a uniform space     *)
(*                    split_ent E == when E is an entourage, split_ent E is   *)
(*                                   an entourage E' such that E' \o E' is    *)
(*                                   included in E when seen as a relation    *)
(*         countable_uniformity T == T's entourage has a countable base       *)
(*                                   This is equivalent to `T` being          *)
(*                                   metrizable.                              *)
(*              unif_continuous f == f is uniformly continuous                *)
(*                entourage_ ball == entourages defined using balls           *)
(* ```                                                                        *)
(* ## Factories                                                               *)
(* ```                                                                        *)
(*                 Nbhs_isUniform == factory to build a topological space     *)
(*                                   from a mixin for a uniform space         *)
(*                                                                            *)
(* ```                                                                        *)
(* ### Complete uniform spaces                                                *)
(* ```                                                                        *)
(*                      cauchy F <-> the set of sets F is a cauchy filter     *)
(*                                   (entourage definition)                   *)
(*                   completeType == interface type for a complete uniform    *)
(*                                   space structure                          *)
(*                                   The HB class is Complete.                *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Open Scope relation_scope.

HB.factory Record Nbhs_isUniform M & Nbhs M := {
  entourage : set_system (M * M);
  entourage_filter : Filter entourage;
  entourage_diagonal : forall A, entourage A -> diagonal `<=` A;
  entourage_inv : forall A, entourage A -> entourage A^-1;
  entourage_split_ex :
    forall A, entourage A -> exists2 B, entourage B & B \; B `<=` A;
  nbhsE : nbhs = nbhs_ entourage;
}.

HB.builders Context M & Nbhs_isUniform M.

HB.instance Definition _ := Nbhs_isUniform_mixin.Build M
  entourage_filter entourage_diagonal entourage_inv
  entourage_split_ex nbhsE.

HB.end.

Lemma entourage_sym {X Y : Type} E (x : X) (y : Y) :
  E (x, y) <-> (E ^-1)%relation (y, x).
Proof. by []. Qed.

Lemma filter_from_entourageE {M : uniformType} x :
  filter_from (@entourage M) (fun A => xsection A x) = nbhs x.
Proof. by rewrite -nbhs_entourageE. Qed.

Module Export NbhsEntourage.
Definition nbhs_simpl :=
  (nbhs_simpl,@filter_from_entourageE,@nbhs_entourageE).
End NbhsEntourage.

Lemma nbhsP {M : uniformType} (x : M) P : nbhs x P <-> nbhs_ entourage x P.
Proof. by rewrite nbhs_simpl. Qed.

Lemma filter_inv {T : Type} (F : set_system (T * T)) :
  Filter F -> Filter [set V^-1 | V in F]%relation.
Proof.
move=> FF; split => /=.
- by exists [set: T * T] => //; exact: filterT.
- by move=> P Q [R FR <-] [S FS <-]; exists (R `&` S) => //; exact: filterI.
- move=> P Q PQ [R FR RP]; exists Q^-1%relation => //; first last.
    by rewrite eqEsubset; split; case.
  by apply: filterS FR; case=> ? ? /= ?; apply: PQ; rewrite -RP.
Qed.

Section uniformType1.
Local Open Scope relation_scope.
Context {M : uniformType}.

Global Instance entourage_filter' : Filter (@entourage M).
Proof.
exact: entourage_filter.
Qed.

Lemma entourageT : entourage [set: M * M].
Proof. exact: filterT. Qed.

Lemma nbhs_entourage (x : M) A : entourage A -> nbhs x (xsection A x).
Proof. by move=> ?; apply/nbhsP; exists A. Qed.

Lemma cvg_entourageP F (FF : Filter F) (p : M) :
  F --> p <-> forall A, entourage A -> \forall q \near F, A (p, q).
Proof.
rewrite -filter_fromP [X in filter_from _ X](_ : _ = @xsection M M ^~ p)//.
  by apply/funext => E; apply/seteqP; split => [|] ? /xsectionP.
by rewrite filter_from_entourageE.
Qed.

Lemma cvg_entourage {F} {FF : Filter F} (x : M) :
  F --> x -> forall A, entourage A -> \forall y \near F, A (x, y).
Proof. by move/cvg_entourageP. Qed.

Lemma cvg_app_entourageP T (f : T -> M) F (FF : Filter F) p :
  f @ F --> p <-> forall A, entourage A -> \forall t \near F, A (p, f t).
Proof. exact: cvg_entourageP. Qed.

Lemma entourage_invI (E : set (M * M)) : entourage E -> entourage (E `&` E^-1).
Proof. by move=> ?; apply: filterI; last exact: entourage_inv. Qed.

End uniformType1.

Global Instance entourage_pfilter {M : puniformType} :
  ProperFilter (@entourage M).
Proof.
apply Build_ProperFilter_ex; last exact: entourage_filter.
by move=> A entA; exists (point, point); apply: entourage_refl.
Qed.

#[global]
Hint Extern 0 (entourage (split_ent _)) => exact: entourage_split_ent : core.
#[global]
Hint Extern 0 (entourage (get _)) => exact: entourage_split_ent : core.
#[global]
Hint Extern 0 (entourage (_^-1)%relation) => exact: entourage_inv : core.
Arguments entourage_split {M} z {x y A}.
#[global]
Hint Extern 0 (nbhs _ (xsection _ _)) => exact: nbhs_entourage : core.

Lemma ent_closure {M : uniformType} (x : M) E : entourage E ->
  closure (xsection (split_ent E) x) `<=` xsection E x.
Proof.
pose E' := (split_ent E) `&` (split_ent E)^-1%relation.
move=> entE z /(_ (xsection E' z))[].
  by rewrite -nbhs_entourageE; exists E' => //; exact: filterI.
move=> y; rewrite xsectionI => -[/xsectionP xy [_ /xsectionP yz]].
by apply/xsectionP; move: xy yz; exact: entourage_split.
Qed.

Lemma continuous_withinNx {U V : uniformType} (f : U -> V) x :
  {for x, continuous f} <-> f @ x^' --> f x.
Proof.
split=> - cfx P /= fxP.
  by rewrite !near_simpl; apply: cvg_within; apply: cfx.
rewrite !nbhs_nearE !near_map in fxP *; have /= := cfx P fxP.
rewrite !near_simpl near_withinE near_simpl => Pf; near=> y.
by have [->|] := eqVneq y x; [by apply: nbhs_singleton|near: y].
Unshelve. all: by end_near. Qed.

Lemma continuous_injective_withinNx
  (T U : topologicalType) (f : T -> U) (x : T) :
  {for x, continuous f} ->
  (forall y, f y = f x -> y = x) -> f @ x^' --> (f x)^'.
Proof.
move=> cf fI A; rewrite /nbhs /= /dnbhs !withinE/= => -[V Vfx AV].
exists (f @^-1` V); first exact: cf Vfx.
by apply/seteqP; split=> y/=;
  move/predeqP : AV => /(_ (f y))/= AV [AVfy yx];
  have /contra_neq /(_ yx) := fI y; tauto.
Qed.

(* This property is primarily useful for metrizability on uniform spaces *)
Definition countable_uniformity (T : uniformType) :=
  exists R : set_system (T * T), [/\
    countable R,
    R `<=` entourage &
    forall P, entourage P -> exists2 Q, R Q & Q `<=` P].

Lemma countable_uniformityP {T : uniformType} :
  countable_uniformity T <-> exists2 f : nat -> set (T * T),
    (forall A, entourage A -> exists N, f N `<=` A) &
    (forall n, entourage (f n)).
Proof.
split=> [[M []]|[f fsubE entf]].
  move=> /pfcard_geP[-> _ /(_ _ (@entourageT _))[]//|/unsquash f eM Msub].
  exists f; last by move=> n; apply: eM; exact: funS.
  by move=> ? /Msub [Q + ?] => /(@surj _ _ _ _ f)[n _ fQ]; exists n; rewrite fQ.
exists (range f); split; first exact: card_image_le.
  by move=> E [n _] <-; exact: entf.
by move=> E /fsubE [n fnA]; exists (f n) => //; exists n.
Qed.

Lemma open_nbhs_entourage (U : uniformType) (x : U) (A : set (U * U)) :
  entourage A -> open_nbhs x (xsection A x)°.
Proof.
move=> entA; split; first exact: open_interior.
by apply: nbhs_singleton; apply: nbhs_interior; exact: nbhs_entourage.
Qed.

Definition unif_continuous (U V : uniformType) (f : U -> V) :=
  (map_pair f) @ entourage --> entourage.

Lemma unif_continuous_continuous (U V : uniformType) (f : U -> V) :
  unif_continuous f -> continuous f.
Proof.
rewrite /unif_continuous /cvg_to !nbhs_simpl => ucf.
rewrite /cvg_to /= => u X; rewrite !nbhs_simpl /= -!nbhs_entourageE.
case => Y /ucf /=; set Y' := (Y' in entourage Y') => eY' YX.
exists Y' => //.
rewrite /Y' /=.
rewrite -image_sub => v [] u' /= Yfuu' <-.
exact: YX.
Qed.

Lemma unif_continuous_comp {U V W : uniformType} (f : U -> V) (g : V -> W) :
  unif_continuous f -> unif_continuous g -> unif_continuous (g \o f).
Proof. by move=> cf cg A /cg /cf; exact. Qed.

Definition entourage_set (U : uniformType) (A : set ((set U) * (set U))) :=
  exists2 B, entourage B & forall PQ, A PQ -> forall p q,
    PQ.1 p -> PQ.2 q -> B (p,q).

(** Complete uniform spaces *)

Definition cauchy {T : uniformType} (F : set_system T) := (F, F) --> entourage.

Lemma cvg_cauchy {T : puniformType} (F : set_system T) : Filter F ->
  [cvg F in T] -> cauchy F.
Proof.
move=> FF cvF A entA; have /entourage_split_ex [B entB sB2A] := entA.
exists (xsection (B^-1%relation) (lim F), xsection B (lim F)).
  split=> /=; apply: cvF; rewrite /= -nbhs_entourageE; last by exists B.
  by exists B^-1%relation => //; exact: entourage_inv.
move=> ab [/= /xsectionP Balima /xsectionP Blimb]; apply: sB2A.
by exists (lim F).
Qed.

HB.mixin Record Uniform_isComplete T & PointedUniform T := {
  cauchy_cvg :
    forall (F : set_system T), ProperFilter F -> cauchy F -> cvg F
}.

#[short(type="completeType")]
HB.structure Definition Complete :=
  {T of Uniform T & Uniform_isComplete T & isPointed T}.

Section completeType1.

Context {T : completeType}.

Lemma cauchy_cvgP (F : set_system T) (FF : ProperFilter F) : cauchy F <-> cvg F.
Proof. by split=> [/cauchy_cvg|/cvg_cauchy]. Qed.

End completeType1.
Arguments cauchy_cvg {T} F {FF} _ : rename.
Arguments cauchy_cvgP {T} F {FF}.

Lemma compact_cauchy_cvg {T : puniformType} (U : set T) (F : set_system T) :
  ProperFilter F -> cauchy F -> F U -> compact U -> cvg F.
Proof.
move=> PF cf FU /(_ F PF FU) [x [_ clFx]]; apply: (cvgP x).
apply/cvg_entourageP => E entE.
have : nbhs entourage (split_ent E) by rewrite nbhs_filterE.
move=> /(cf (split_ent E))[] [D1 D2]/= /[!nbhs_simpl] -[FD1 FD2 D1D2E].
have : nbhs x (xsection (split_ent E) x) by exact: nbhs_entourage.
move=> /(clFx _ (xsection (split_ent E) x) FD1)[z [Dz /xsectionP Exz]].
by near=> t; apply/(entourage_split z entE Exz)/D1D2E; split => //; near: t.
Unshelve. all: by end_near. Qed.