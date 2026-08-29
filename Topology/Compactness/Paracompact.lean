/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Yury Kudryashov
-/
module

public import Mathlib.Data.Option.Basic
public import Mathlib.Topology.Separation.Regular

/-!
# Paracompact topological spaces

A topological space `X` is said to be paracompact if every open covering of `X` admits a locally
finite refinement.

The definition requires that each set of the new covering is a subset of one of the sets of the
initial covering. However, one can ensure that each open covering `s : ι → Set X` admits a *precise*
locally finite refinement, i.e., an open covering `t : ι → Set X` with the same index set such that
`∀ i, t i ⊆ s i`, see lemma `precise_refinement`. We also provide a convenience lemma
`precise_refinement_set` that deals with open coverings of a closed subset of `X` instead of the
whole space.

We also prove the following facts.

* Every compact space is paracompact, see instance `paracompact_of_compact`.

* A locally compact sigma compact Hausdorff space is paracompact, see instance
  `paracompact_of_locallyCompact_sigmaCompact`. Moreover, we can choose a locally finite
  refinement with sets in a given collection of filter bases of `𝓝 x`, `x : X`, see
  `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis`. For example, in a proper metric space
  every open covering `⋃ i, s i` admits a refinement `⋃ i, Metric.ball (c i) (r i)`.

* Every paracompact Hausdorff space is normal. This statement is not an instance to avoid loops in
  the instance graph.

* Every `EMetricSpace` is a paracompact space, see instance `EMetric.instParacompactSpace` in
  `Topology/EMetricSpace/Paracompact`.

## TODO

Prove (some of) [Michael's theorems](https://ncatlab.org/nlab/show/Michael%27s+theorem).

## Tags

compact space, paracompact space, locally finite covering
-/

public section


open Set Filter Function

open Filter Topology

universe u v w

/--
Definition of `ParacompactSpace` / `ParacompactSpace` 的定义

English:
class ParacompactSpace
  parameters: (X : Type v) [TopologicalSpace X]
  axioms and operations (1):
    - locallyFinite_refinement : forall (α : Type v) (s : α -> Set X), (forall a, IsOpen (s a)) -> (⋃ a, s a = univ) -> exists (β : Type v) (t : β -> Set X), (forall b, IsOpen (t b)) ∧ (⋃ b, t b = univ) ∧ LocallyFinite t ∧ forall b, exists a, t b subseteq s a

中文:
类 仿紧空间
  参数: (X : 类型v) [拓扑空间 X]
  公理与运算 (1 个):
    - locallyFinite_refinement : 对任意 (α : 类型v) (s : α -> 集合 X), (对任意 a, 是开集 (s a)) -> (⋃ a, s a = univ) -> 存在 (β : 类型v) (t : β -> 集合 X), (对任意 b, 是开集 (t b)) ∧ (⋃ b, t b = univ) ∧ 局部有限 t ∧ 对任意 b, 存在 a, t b subseteq s a
-/
class ParacompactSpace (X : Type v) [TopologicalSpace X] : Prop where
  /-- Every open cover of a paracompact space assumes a locally finite refinement. -/
  locallyFinite_refinement :
    forall (α : Type v) (s : α -> Set X), (forall a, IsOpen (s a)) -> (⋃ a, s a = univ) ->
      exists (β : Type v) (t : β -> Set X),
        (forall b, IsOpen (t b)) ∧ (⋃ b, t b = univ) ∧ LocallyFinite t ∧ forall b, exists a, t b subseteq s a

variable {ι : Type u} {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/--
theorem `precise_refinement` / 定理 `precise_refinement`

English:
theorem precise_refinement
  statement: [ParacompactSpace X] (u : ι -> Set X) (uo : forall a, IsOpen (u a))
  proof: by
  -- Apply definition to `range u`, then turn existence quantifiers into functions using `choose`
  have := ParacompactSpace.locallyFinite_refinement (range u) (fun r => (r : Set X))
    (forall_subtype_range_iff.2 uo) (by rwa [← sUnion_range, Subtype.range_coe])
  simp only [exists_subtype_range_iff, iUnion_eq_univ_iff] at this
  choose α t hto hXt htf ind hind using this
  choose t_inv ht_inv using hXt
  choose U hxU hU using htf
  -- Send each `i` to the union of `t a` over `a ∈ ind ⁻¹' {i}`
  refine ⟨fun i => ⋃ (a : α) (_ : ind a = i), t a, ?_, ?_, ?_, ?_⟩
  · exact fun a => isOpen_iUnion fun a => isOpen_iUnion fun _ => hto a
  · simp only [eq_univ_iff_forall, mem_iUnion]
    exact fun x => ⟨ind (t_inv x), _, rfl, ht_inv _⟩
  · refine fun x => ⟨U x, hxU x, ((hU x).image ind).subset ?_⟩
    simp only [subset_def, mem_iUnion, mem_ofPred_eq, Set.Nonempty, mem_inter_iff]
    rintro i ⟨y, ⟨a, rfl, hya⟩, hyU⟩
    exact mem_image_of_mem _ ⟨y, hya, hyU⟩
  · simp only [subset_def, mem_iUnion]
    rintro i x ⟨a, rfl, hxa⟩
    exact hind _ hxa

中文:
定理 precise_refinement
  结论: [仿紧空间 X] (u : ι -> 集合 X) (uo : 对任意 a, 是开集 (u a))
  证明: by
  -- Apply definition to `range u`, then turn existence quantifiers into functions using `choose`
  have := ParacompactSpace.locallyFinite_refinement (range u) (fun r => (r : Set X))
    (forall_subtype_range_iff.2 uo) (by rwa [← sUnion_range, Subtype.range_coe])
  simp only [exists_subtype_range_iff, iUnion_eq_univ_iff] at this
  choose α t hto hXt htf ind hind using this
  choose t_inv ht_inv using hXt
  choose U hxU hU using htf
  -- Send each `i` to the union of `t a` over `a ∈ ind ⁻¹' {i}`
  refine ⟨fun i => ⋃ (a : α) (_ : ind a = i), t a, ?_, ?_, ?_, ?_⟩
  · exact fun a => isOpen_iUnion fun a => isOpen_iUnion fun _ => hto a
  · simp only [eq_univ_iff_forall, mem_iUnion]
    exact fun x => ⟨ind (t_inv x), _, rfl, ht_inv _⟩
  · refine fun x => ⟨U x, hxU x, ((hU x).image ind).subset ?_⟩
    simp only [subset_def, mem_iUnion, mem_ofPred_eq, Set.Nonempty, mem_inter_iff]
    rintro i ⟨y, ⟨a, rfl, hya⟩, hyU⟩
    exact mem_image_of_mem _ ⟨y, hya, hyU⟩
  · simp only [subset_def, mem_iUnion]
    rintro i x ⟨a, rfl, hxa⟩
    exact hind _ hxa
-/
theorem precise_refinement [ParacompactSpace X] (u : ι -> Set X) (uo : forall a, IsOpen (u a))
    (uc : ⋃ i, u i = univ) : exists v : ι -> Set X, (forall a, IsOpen (v a)) ∧ ⋃ i, v i = univ ∧
    LocallyFinite v ∧ forall a, v a subseteq u a := by
  -- Apply definition to `range u`, then turn existence quantifiers into functions using `choose`
  have := ParacompactSpace.locallyFinite_refinement (range u) (fun r => (r : Set X))
    (forall_subtype_range_iff.2 uo) (by rwa [← sUnion_range, Subtype.range_coe])
  simp only [exists_subtype_range_iff, iUnion_eq_univ_iff] at this
  choose α t hto hXt htf ind hind using this
  choose t_inv ht_inv using hXt
  choose U hxU hU using htf
  -- Send each `i` to the union of `t a` over `a ∈ ind ⁻¹' {i}`
  refine ⟨fun i => ⋃ (a : α) (_ : ind a = i), t a, ?_, ?_, ?_, ?_⟩
  · exact fun a => isOpen_iUnion fun a => isOpen_iUnion fun _ => hto a
  · simp only [eq_univ_iff_forall, mem_iUnion]
    exact fun x => ⟨ind (t_inv x), _, rfl, ht_inv _⟩
  · refine fun x => ⟨U x, hxU x, ((hU x).image ind).subset ?_⟩
    simp only [subset_def, mem_iUnion, mem_ofPred_eq, Set.Nonempty, mem_inter_iff]
    rintro i ⟨y, ⟨a, rfl, hya⟩, hyU⟩
    exact mem_image_of_mem _ ⟨y, hya, hyU⟩
  · simp only [subset_def, mem_iUnion]
    rintro i x ⟨a, rfl, hxa⟩
    exact hind _ hxa

/--
theorem `precise_refinement_set` / 定理 `precise_refinement_set`

English:
theorem precise_refinement_set
  statement: [ParacompactSpace X] {s : Set X} (hs : IsClosed s) (u : ι -> Set X)
  proof: by
  have uc : (iUnion fun i => Option.elim' sᶜ u i) = univ := by
    apply Subset.antisymm (subset_univ _)
    · simp_rw [← compl_union_self s, Option.elim', iUnion_option]
      apply union_subset_union_right sᶜ us
  rcases precise_refinement (Option.elim' sᶜ u) (Option.forall.2 ⟨isOpen_compl_iff.2 hs, uo⟩)
      uc with
    ⟨v, vo, vc, vf, vu⟩
  refine ⟨v ∘ some, fun i => vo _, ?_, vf.comp_injective (Option.some_injective _), fun i => vu _⟩
  · simp only [iUnion_option, ← compl_subset_iff_union] at vc
    exact Subset.trans (subset_compl_comm.1 <| vu Option.none) vc

中文:
定理 precise_refinement_set
  结论: [仿紧空间 X] {s : 集合 X} (hs : 是闭集 s) (u : ι -> 集合 X)
  证明: by
  have uc : (iUnion fun i => Option.elim' sᶜ u i) = univ := by
    apply Subset.antisymm (subset_univ _)
    · simp_rw [← compl_union_self s, Option.elim', iUnion_option]
      apply union_subset_union_right sᶜ us
  rcases precise_refinement (Option.elim' sᶜ u) (Option.forall.2 ⟨isOpen_compl_iff.2 hs, uo⟩)
      uc with
    ⟨v, vo, vc, vf, vu⟩
  refine ⟨v ∘ some, fun i => vo _, ?_, vf.comp_injective (Option.some_injective _), fun i => vu _⟩
  · simp only [iUnion_option, ← compl_subset_iff_union] at vc
    exact Subset.trans (subset_compl_comm.1 <| vu Option.none) vc

Depends on / 依赖: Option.elim, Option.forall, Option.some_injective, Subset, Subset.antisymm, Subset.trans, antisymm, comp_injective, compl_subset_iff_union, compl_union_self, iUnion, iUnion_option, isOpen_compl_iff, precise_refinement, simp_rw, some_injective, subset_univ, union_subset_union_right, vf.comp_injective
-/
theorem precise_refinement_set [ParacompactSpace X] {s : Set X} (hs : IsClosed s) (u : ι -> Set X)
    (uo : forall i, IsOpen (u i)) (us : s subseteq ⋃ i, u i) :
    exists v : ι -> Set X, (forall i, IsOpen (v i)) ∧ (s subseteq ⋃ i, v i) ∧ LocallyFinite v ∧ forall i, v i subseteq u i := by
  have uc : (iUnion fun i => Option.elim' sᶜ u i) = univ := by
    apply Subset.antisymm (subset_univ _)
    · simp_rw [← compl_union_self s, Option.elim', iUnion_option]
      apply union_subset_union_right sᶜ us
  rcases precise_refinement (Option.elim' sᶜ u) (Option.forall.2 ⟨isOpen_compl_iff.2 hs, uo⟩)
      uc with
    ⟨v, vo, vc, vf, vu⟩
  refine ⟨v ∘ some, fun i => vo _, ?_, vf.comp_injective (Option.some_injective _), fun i => vu _⟩
  · simp only [iUnion_option, ← compl_subset_iff_union] at vc
    exact Subset.trans (subset_compl_comm.1 <| vu Option.none) vc

/--
theorem `ParacompactSpace.of_hasBasis` / 定理 `ParacompactSpace.of_hasBasis`

English:
theorem ParacompactSpace.of_hasBasis
  statement: {ι : X -> Sort*} {p : forall x, ι x -> Prop} {s : forall x, ι x -> Set X}
  proof: by
    have := fun x => (iUnion_eq_univ_iff.1 hu x).imp fun a ha => (hb _).mem_iff.1 ((ho a).mem_nhds ha)
    choose a f hp hsub using this
    rcases h f hp with ⟨β, t, hto, ht, htf, hts⟩
    refine ⟨range t, Subtype.val, forall_subtype_range_iff.2 hto, ?_, htf.on_range,
      forall_subtype_range_iff.2 fun b => ?_⟩
    · rwa [iUnion_subtype, biUnion_range]
    · rcases hts b with ⟨x, hx⟩
      exact ⟨_, hx.trans (hsub _)⟩

中文:
定理 仿紧空间.of_hasBasis
  结论: {ι : X -> 类型层*} {p : 对任意 x, ι x -> 命题} {s : 对任意 x, ι x -> 集合 X}
  证明: by
    have := fun x => (iUnion_eq_univ_iff.1 hu x).imp fun a ha => (hb _).mem_iff.1 ((ho a).mem_nhds ha)
    choose a f hp hsub using this
    rcases h f hp with ⟨β, t, hto, ht, htf, hts⟩
    refine ⟨range t, Subtype.val, forall_subtype_range_iff.2 hto, ?_, htf.on_range,
      forall_subtype_range_iff.2 fun b => ?_⟩
    · rwa [iUnion_subtype, biUnion_range]
    · rcases hts b with ⟨x, hx⟩
      exact ⟨_, hx.trans (hsub _)⟩

Depends on / 依赖: Subtype, Subtype.val, biUnion_range, forall_subtype_range_iff, htf.on_range, hx.trans, iUnion_eq_univ_iff, iUnion_subtype, mem_iff, mem_nhds, on_range
-/
theorem ParacompactSpace.of_hasBasis {ι : X -> Sort*} {p : forall x, ι x -> Prop} {s : forall x, ι x -> Set X}
    (hb : forall x, (𝓝 x).HasBasis (p x) (s x))
    (h : forall f : (x : X) -> ι x, (forall x, p x (f x)) ->
      exists (β : Type u) (t : β -> Set X), (forall b, IsOpen (t b)) ∧ (⋃ b, t b) = univ ∧ LocallyFinite t ∧
        forall b, exists x, t b subseteq s x (f x)) : ParacompactSpace X where
  locallyFinite_refinement α S ho hu := by
    have := fun x => (iUnion_eq_univ_iff.1 hu x).imp fun a ha => (hb _).mem_iff.1 ((ho a).mem_nhds ha)
    choose a f hp hsub using this
    rcases h f hp with ⟨β, t, hto, ht, htf, hts⟩
    refine ⟨range t, Subtype.val, forall_subtype_range_iff.2 hto, ?_, htf.on_range,
      forall_subtype_range_iff.2 fun b => ?_⟩
    · rwa [iUnion_subtype, biUnion_range]
    · rcases hts b with ⟨x, hx⟩
      exact ⟨_, hx.trans (hsub _)⟩

/--
theorem `Topology.IsClosedEmbedding.paracompactSpace` / 定理 `Topology.IsClosedEmbedding.paracompactSpace`

English:
theorem Topology.IsClosedEmbedding.paracompactSpace
  statement: [ParacompactSpace Y] {e : X -> Y}
  proof: by
    choose U hUo hU using fun a => he.isOpen_iff.1 (ho a)
    simp only [← hU] at hu ⊢
    have heU : range e subseteq ⋃ i, U i := by
      simpa only [range_subset_iff, mem_iUnion, iUnion_eq_univ_iff] using! hu
    rcases precise_refinement_set he.isClosed_range U hUo heU with ⟨V, hVo, heV, hVf, hVU⟩
    refine ⟨α, fun a => e ⁻¹' (V a), fun a => (hVo a).preimage he.continuous, ?_,
      hVf.preimage_continuous he.continuous, fun a => ⟨a, preimage_mono (hVU a)⟩⟩
    simpa only [range_subset_iff, mem_iUnion, iUnion_eq_univ_iff] using! heV

中文:
定理 拓扑.是闭嵌入.paracompactSpace
  结论: [仿紧空间 Y] {e : X -> Y}
  证明: by
    choose U hUo hU using fun a => he.isOpen_iff.1 (ho a)
    simp only [← hU] at hu ⊢
    have heU : range e subseteq ⋃ i, U i := by
      simpa only [range_subset_iff, mem_iUnion, iUnion_eq_univ_iff] using! hu
    rcases precise_refinement_set he.isClosed_range U hUo heU with ⟨V, hVo, heV, hVf, hVU⟩
    refine ⟨α, fun a => e ⁻¹' (V a), fun a => (hVo a).preimage he.continuous, ?_,
      hVf.preimage_continuous he.continuous, fun a => ⟨a, preimage_mono (hVU a)⟩⟩
    simpa only [range_subset_iff, mem_iUnion, iUnion_eq_univ_iff] using! heV

Depends on / 依赖: continuous, hVf.preimage_continuous, he.continuous, he.isClosed_range, he.isOpen_iff, iUnion_eq_univ_iff, isClosed_range, isOpen_iff, mem_iUnion, precise_refinement_set, preimage, preimage_continuous, preimage_mono, range_subset_iff, subseteq
-/
theorem Topology.IsClosedEmbedding.paracompactSpace [ParacompactSpace Y] {e : X -> Y}
    (he : IsClosedEmbedding e) : ParacompactSpace X where
  locallyFinite_refinement α s ho hu := by
    choose U hUo hU using fun a => he.isOpen_iff.1 (ho a)
    simp only [← hU] at hu ⊢
    have heU : range e subseteq ⋃ i, U i := by
      simpa only [range_subset_iff, mem_iUnion, iUnion_eq_univ_iff] using! hu
    rcases precise_refinement_set he.isClosed_range U hUo heU with ⟨V, hVo, heV, hVf, hVU⟩
    refine ⟨α, fun a => e ⁻¹' (V a), fun a => (hVo a).preimage he.continuous, ?_,
      hVf.preimage_continuous he.continuous, fun a => ⟨a, preimage_mono (hVU a)⟩⟩
    simpa only [range_subset_iff, mem_iUnion, iUnion_eq_univ_iff] using! heV

/--
theorem `Homeomorph.paracompactSpace_iff` / 定理 `Homeomorph.paracompactSpace_iff`

English:
theorem Homeomorph.paracompactSpace_iff
  given: (e : X ≃ₜ Y)
  statement: ParacompactSpace X ↔ ParacompactSpace Y
  proof: ⟨fun _ => e.symm.isClosedEmbedding.paracompactSpace, fun _ => e.isClosedEmbedding.paracompactSpace⟩

中文:
定理 同胚.paracompactSpace_iff
  条件: (e : X ≃ₜ Y)
  结论: 仿紧空间 X ↔ 仿紧空间 Y
  证明: ⟨fun _ => e.symm.isClosedEmbedding.paracompactSpace, fun _ => e.isClosedEmbedding.paracompactSpace⟩

Depends on / 依赖: e.isClosedEmbedding.paracompactSpace, e.symm.isClosedEmbedding.paracompactSpace, isClosedEmbedding, paracompactSpace
-/
theorem Homeomorph.paracompactSpace_iff (e : X ≃ₜ Y) : ParacompactSpace X ↔ ParacompactSpace Y :=
  ⟨fun _ => e.symm.isClosedEmbedding.paracompactSpace, fun _ => e.isClosedEmbedding.paracompactSpace⟩

/-- The product of a compact space and a paracompact space is a paracompact space. The formalization
is based on https://dantopology.wordpress.com/2009/10/24/compact-x-paracompact-is-paracompact/
with some minor modifications.

This version assumes that `X` in `X × Y` is compact and `Y` is paracompact, see next lemma for the
other case. -/
instance (priority := 200) [CompactSpace X] [ParacompactSpace Y] : ParacompactSpace (X × Y) where
  locallyFinite_refinement α s ho hu := by
    have : forall (x : X) (y : Y), exists (a : α) (U : Set X) (V : Set Y),
        IsOpen U ∧ IsOpen V ∧ x in U ∧ y in V ∧ U ×ˢ V subseteq s a := fun x y =>
      (iUnion_eq_univ_iff.1 hu (x, y)).imp fun a ha => isOpen_prod_iff.1 (ho a) x y ha
    choose a U V hUo hVo hxU hyV hUV using this
    choose T hT using fun y => CompactSpace.elim_nhds_subcover (U · y) fun x =>
      (hUo x y).mem_nhds (hxU x y)
    set W : Y -> Set Y := fun y => ⋂ x in T y, V x y
    have hWo : forall y, IsOpen (W y) := fun y => isOpen_biInter_finset fun _ _ => hVo _ _
    have hW : forall y, y in W y := fun _ => mem_iInter₂.2 fun _ _ => hyV _ _
    rcases precise_refinement W hWo (iUnion_eq_univ_iff.2 fun y => ⟨y, hW y⟩)
      with ⟨E, hEo, hE, hEf, hEA⟩
    refine ⟨Σ y, T y, fun z => U z.2.1 z.1 ×ˢ E z.1, fun _ => (hUo _ _).prod (hEo _),
      iUnion_eq_univ_iff.2 fun (x, y) => ?_, fun (x, y) => ?_, fun ⟨y, x, hx⟩ => ?_⟩
    · rcases iUnion_eq_univ_iff.1 hE y with ⟨b, hb⟩
      rcases iUnion₂_eq_univ_iff.1 (hT b) x with ⟨a, ha, hx⟩
      exact ⟨⟨b, a, ha⟩, hx, hb⟩
    · rcases hEf y with ⟨t, ht, htf⟩
      refine ⟨univ ×ˢ t, prod_mem_nhds univ_mem ht, ?_⟩
      refine (htf.biUnion fun y _ => finite_range (Sigma.mk y)).subset ?_
      rintro ⟨b, a, ha⟩ ⟨⟨c, d⟩, ⟨-, hd : d in E b⟩, -, hdt : d in t⟩
      exact mem_iUnion₂.2 ⟨b, ⟨d, hd, hdt⟩, mem_range_self _⟩
    · refine ⟨a x y, (Set.prod_mono Subset.rfl ?_).trans (hUV x y)⟩
      exact (hEA _).trans (iInter₂_subset x hx)

instance (priority := 200) [ParacompactSpace X] [CompactSpace Y] : ParacompactSpace (X × Y) :=
  (Homeomorph.prodComm X Y).paracompactSpace_iff.2 inferInstance

-- See note [lower instance priority]
/-- A compact space is paracompact. -/
instance (priority := 100) paracompact_of_compact [CompactSpace X] : ParacompactSpace X := by
  -- the proof is trivial: we choose a finite subcover using compactness, and use it
  refine ⟨fun ι s ho hu => ?_⟩
  rcases isCompact_univ.elim_finite_subcover _ ho hu.ge with ⟨T, hT⟩
  refine ⟨(T : Set ι), fun t => s t, fun t => ho _, ?_, locallyFinite_of_finite _,
    fun t => ⟨t, Subset.rfl⟩⟩
  simpa only [iUnion_coe_set, ← univ_subset_iff]

/--
theorem `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set` / 定理 `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set`

English:
theorem refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set
  statement: [WeaklyLocallyCompactSpace X]
  proof: by
  -- For technical reasons we prepend two empty sets to the sequence `CompactExhaustion.choice X`
  set K' : CompactExhaustion X := CompactExhaustion.choice X
  set K : CompactExhaustion X := K'.shiftr.shiftr
  set Kdiff := fun n => K (n + 1) \ interior (K n)
  -- Now we restate some properties of `CompactExhaustion` for `K`/`Kdiff`
  have hKcov : forall x, x in Kdiff (K'.find x + 1) := fun x => by
    simpa only [K'.find_shiftr] using
      sdiff_subset_sdiff_right interior_subset (K'.shiftr.mem_sdiff_shiftr_find x)
  have Kdiffc : forall n, IsCompact (Kdiff n inter s) :=
    fun n => ((K.isCompact _).diff isOpen_interior).inter_right hs
  -- Next we choose a finite covering `B (c n i) (r n i)` of each
  -- `Kdiff (n + 1) ∩ s` such that `B (c n i) (r n i) ∩ s` is disjoint with `K n`
  have : forall (n) (x : ↑(Kdiff (n + 1) inter s)), (K n)ᶜ in 𝓝 (x : X) :=
fun n x => (K.isClosed n).compl_mem_nhds fun hx' => x.2.1.2 K.subset_interior_succ _ hx'
  choose! r hrp hr using fun n (x : ↑(Kdiff (n + 1) inter s)) => (hB x x.2.2).mem_iff.1 (this n x)
  have hxr : forall (n x) (hx : x in Kdiff (n + 1) inter s), B x (r n ⟨x, hx⟩) in 𝓝 x := fun n x hx =>
    (hB x hx.2).mem_of_mem (hrp _ ⟨x, hx⟩)
  choose T hT using fun n => (Kdiffc (n + 1)).elim_nhds_subcover' _ (hxr n)
  set T' : forall n, Set ↑(Kdiff (n + 1) inter s) := fun n => T n
  -- Finally, we take the union of all these coverings
  refine ⟨Σ n, T' n, fun a => a.2, fun a => r a.1 a.2, ?_, ?_, ?_⟩
  · rintro ⟨n, x, hx⟩
    exact ⟨x.2.2, hrp _ _⟩
  · refine fun x hx => mem_iUnion.2 ?_
    rcases mem_iUnion₂.1 (hT _ ⟨hKcov x, hx⟩) with ⟨⟨c, hc⟩, hcT, hcx⟩
    exact ⟨⟨_, ⟨c, hc⟩, hcT⟩, hcx⟩
  · intro x
    refine
      ⟨interior (K (K'.find x + 3)),
        IsOpen.mem_nhds isOpen_interior (K.subset_interior_succ _ (hKcov x).1), ?_⟩
    have : (⋃ k <= K'.find x + 2, range (Sigma.mk k) : Set (Σ n, T' n)).Finite :=
      (finite_le_nat _).biUnion fun k _ => finite_range _
    apply this.subset
    rintro ⟨k, c, hc⟩
    simp only [mem_iUnion, mem_ofPred_eq, Subtype.coe_mk]
    rintro ⟨x, hxB : x in B c (r k c), hxK⟩
    refine ⟨k, ?_, ⟨c, hc⟩, rfl⟩
    have := (mem_compl_iff _ _).1 (hr k c hxB)
    contrapose! this with hnk
    exact K.subset hnk (interior_subset hxK)

中文:
定理 refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set
  结论: [WeaklyLocallyCompact空间 X]
  证明: by
  -- For technical reasons we prepend two empty sets to the sequence `CompactExhaustion.choice X`
  set K' : CompactExhaustion X := CompactExhaustion.choice X
  set K : CompactExhaustion X := K'.shiftr.shiftr
  set Kdiff := fun n => K (n + 1) \ interior (K n)
  -- Now we restate some properties of `CompactExhaustion` for `K`/`Kdiff`
  have hKcov : forall x, x in Kdiff (K'.find x + 1) := fun x => by
    simpa only [K'.find_shiftr] using
      sdiff_subset_sdiff_right interior_subset (K'.shiftr.mem_sdiff_shiftr_find x)
  have Kdiffc : forall n, IsCompact (Kdiff n inter s) :=
    fun n => ((K.isCompact _).diff isOpen_interior).inter_right hs
  -- Next we choose a finite covering `B (c n i) (r n i)` of each
  -- `Kdiff (n + 1) ∩ s` such that `B (c n i) (r n i) ∩ s` is disjoint with `K n`
  have : forall (n) (x : ↑(Kdiff (n + 1) inter s)), (K n)ᶜ in 𝓝 (x : X) :=
fun n x => (K.isClosed n).compl_mem_nhds fun hx' => x.2.1.2 K.subset_interior_succ _ hx'
  choose! r hrp hr using fun n (x : ↑(Kdiff (n + 1) inter s)) => (hB x x.2.2).mem_iff.1 (this n x)
  have hxr : forall (n x) (hx : x in Kdiff (n + 1) inter s), B x (r n ⟨x, hx⟩) in 𝓝 x := fun n x hx =>
    (hB x hx.2).mem_of_mem (hrp _ ⟨x, hx⟩)
  choose T hT using fun n => (Kdiffc (n + 1)).elim_nhds_subcover' _ (hxr n)
  set T' : forall n, Set ↑(Kdiff (n + 1) inter s) := fun n => T n
  -- Finally, we take the union of all these coverings
  refine ⟨Σ n, T' n, fun a => a.2, fun a => r a.1 a.2, ?_, ?_, ?_⟩
  · rintro ⟨n, x, hx⟩
    exact ⟨x.2.2, hrp _ _⟩
  · refine fun x hx => mem_iUnion.2 ?_
    rcases mem_iUnion₂.1 (hT _ ⟨hKcov x, hx⟩) with ⟨⟨c, hc⟩, hcT, hcx⟩
    exact ⟨⟨_, ⟨c, hc⟩, hcT⟩, hcx⟩
  · intro x
    refine
      ⟨interior (K (K'.find x + 3)),
        IsOpen.mem_nhds isOpen_interior (K.subset_interior_succ _ (hKcov x).1), ?_⟩
    have : (⋃ k <= K'.find x + 2, range (Sigma.mk k) : Set (Σ n, T' n)).Finite :=
      (finite_le_nat _).biUnion fun k _ => finite_range _
    apply this.subset
    rintro ⟨k, c, hc⟩
    simp only [mem_iUnion, mem_ofPred_eq, Subtype.coe_mk]
    rintro ⟨x, hxB : x in B c (r k c), hxK⟩
    refine ⟨k, ?_, ⟨c, hc⟩, rfl⟩
    have := (mem_compl_iff _ _).1 (hr k c hxB)
    contrapose! this with hnk
    exact K.subset hnk (interior_subset hxK)
-/
theorem refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] [T2Space X] {ι : X -> Type u} {p : forall x, ι x -> Prop} {B : forall x, ι x -> Set X}
    {s : Set X} (hs : IsClosed s) (hB : forall x in s, (𝓝 x).HasBasis (p x) (B x)) :
    exists (α : Type v) (c : α -> X) (r : forall a, ι (c a)),
      (forall a, c a in s ∧ p (c a) (r a)) ∧
        (s subseteq ⋃ a, B (c a) (r a)) ∧ LocallyFinite fun a => B (c a) (r a) := by
  -- For technical reasons we prepend two empty sets to the sequence `CompactExhaustion.choice X`
  set K' : CompactExhaustion X := CompactExhaustion.choice X
  set K : CompactExhaustion X := K'.shiftr.shiftr
  set Kdiff := fun n => K (n + 1) \ interior (K n)
  -- Now we restate some properties of `CompactExhaustion` for `K`/`Kdiff`
  have hKcov : forall x, x in Kdiff (K'.find x + 1) := fun x => by
    simpa only [K'.find_shiftr] using
      sdiff_subset_sdiff_right interior_subset (K'.shiftr.mem_sdiff_shiftr_find x)
  have Kdiffc : forall n, IsCompact (Kdiff n inter s) :=
    fun n => ((K.isCompact _).diff isOpen_interior).inter_right hs
  -- Next we choose a finite covering `B (c n i) (r n i)` of each
  -- `Kdiff (n + 1) ∩ s` such that `B (c n i) (r n i) ∩ s` is disjoint with `K n`
  have : forall (n) (x : ↑(Kdiff (n + 1) inter s)), (K n)ᶜ in 𝓝 (x : X) :=
fun n x => (K.isClosed n).compl_mem_nhds fun hx' => x.2.1.2 K.subset_interior_succ _ hx'
  choose! r hrp hr using fun n (x : ↑(Kdiff (n + 1) inter s)) => (hB x x.2.2).mem_iff.1 (this n x)
  have hxr : forall (n x) (hx : x in Kdiff (n + 1) inter s), B x (r n ⟨x, hx⟩) in 𝓝 x := fun n x hx =>
    (hB x hx.2).mem_of_mem (hrp _ ⟨x, hx⟩)
  choose T hT using fun n => (Kdiffc (n + 1)).elim_nhds_subcover' _ (hxr n)
  set T' : forall n, Set ↑(Kdiff (n + 1) inter s) := fun n => T n
  -- Finally, we take the union of all these coverings
  refine ⟨Σ n, T' n, fun a => a.2, fun a => r a.1 a.2, ?_, ?_, ?_⟩
  · rintro ⟨n, x, hx⟩
    exact ⟨x.2.2, hrp _ _⟩
  · refine fun x hx => mem_iUnion.2 ?_
    rcases mem_iUnion₂.1 (hT _ ⟨hKcov x, hx⟩) with ⟨⟨c, hc⟩, hcT, hcx⟩
    exact ⟨⟨_, ⟨c, hc⟩, hcT⟩, hcx⟩
  · intro x
    refine
      ⟨interior (K (K'.find x + 3)),
        IsOpen.mem_nhds isOpen_interior (K.subset_interior_succ _ (hKcov x).1), ?_⟩
    have : (⋃ k <= K'.find x + 2, range (Sigma.mk k) : Set (Σ n, T' n)).Finite :=
      (finite_le_nat _).biUnion fun k _ => finite_range _
    apply this.subset
    rintro ⟨k, c, hc⟩
    simp only [mem_iUnion, mem_ofPred_eq, Subtype.coe_mk]
    rintro ⟨x, hxB : x in B c (r k c), hxK⟩
    refine ⟨k, ?_, ⟨c, hc⟩, rfl⟩
    have := (mem_compl_iff _ _).1 (hr k c hxB)
    contrapose! this with hnk
    exact K.subset hnk (interior_subset hxK)

/--
theorem `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis` / 定理 `refinement_of_locallyCompact_sigmaCompact_of_nhds_basis`

English:
theorem refinement_of_locallyCompact_sigmaCompact_of_nhds_basis
  statement: [WeaklyLocallyCompactSpace X]
  proof: let ⟨α, c, r, hp, hU, hfin⟩ :=
    refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set isClosed_univ fun x _ => hB x
  ⟨α, c, r, fun a => (hp a).2, univ_subset_iff.1 hU, hfin⟩

中文:
定理 refinement_of_locallyCompact_sigmaCompact_of_nhds_basis
  结论: [WeaklyLocallyCompact空间 X]
  证明: let ⟨α, c, r, hp, hU, hfin⟩ :=
    refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set isClosed_univ fun x _ => hB x
  ⟨α, c, r, fun a => (hp a).2, univ_subset_iff.1 hU, hfin⟩

Depends on / 依赖: isClosed_univ, refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set, univ_subset_iff
-/
theorem refinement_of_locallyCompact_sigmaCompact_of_nhds_basis [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] [T2Space X] {ι : X -> Type u} {p : forall x, ι x -> Prop} {B : forall x, ι x -> Set X}
    (hB : forall x, (𝓝 x).HasBasis (p x) (B x)) :
    exists (α : Type v) (c : α -> X) (r : forall a, ι (c a)),
      (forall a, p (c a) (r a)) ∧ ⋃ a, B (c a) (r a) = univ ∧ LocallyFinite fun a => B (c a) (r a) :=
  let ⟨α, c, r, hp, hU, hfin⟩ :=
    refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set isClosed_univ fun x _ => hB x
  ⟨α, c, r, fun a => (hp a).2, univ_subset_iff.1 hU, hfin⟩

-- See note [lower instance priority]
/-- A locally compact sigma compact Hausdorff space is paracompact. See also
`refinement_of_locallyCompact_sigmaCompact_of_nhds_basis` for a more precise statement. -/
instance (priority := 100) paracompact_of_locallyCompact_sigmaCompact [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] [T2Space X] : ParacompactSpace X := by
  refine ⟨fun α s ho hc => ?_⟩
  choose i hi using iUnion_eq_univ_iff.1 hc
  have : forall x : X, (𝓝 x).HasBasis (fun t : Set X => (x in t ∧ IsOpen t) ∧ t subseteq s (i x)) id :=
    fun x : X => (nhds_basis_opens x).restrict_subset (IsOpen.mem_nhds (ho (i x)) (hi x))
  rcases refinement_of_locallyCompact_sigmaCompact_of_nhds_basis this with
    ⟨β, c, t, hto, htc, htf⟩
exact ⟨β, t, fun x => (hto x).1.2, htc, htf, fun b => ⟨i c b, (hto b).2⟩⟩

/-- **Dieudonné's theorem**: a paracompact R₁ space is normal.
Formalization is based on the proof
at [ncatlab](https://ncatlab.org/nlab/show/paracompact+Hausdorff+spaces+are+normal). -/
instance (priority := 100) NormalSpace.of_paracompactSpace_r1Space
    [R1Space X] [ParacompactSpace X] : NormalSpace X := by
  -- First we show how to go from points to a set on one side.
  have : forall s t : Set X, IsClosed s ->
      (forall x in s, exists u v, IsOpen u ∧ IsOpen v ∧ x in u ∧ t subseteq v ∧ Disjoint u v) ->
      exists u v, IsOpen u ∧ IsOpen v ∧ s subseteq u ∧ t subseteq v ∧ Disjoint u v := fun s t hs H => by
    /- For each `x ∈ s` we choose open disjoint `u x ∋ x` and `v x ⊇ t`. The sets `u x` form an
        open covering of `s`. We choose a locally finite refinement `u' : s → Set X`, then
        `⋃ i, u' i` and `(closure (⋃ i, u' i))ᶜ` are disjoint open neighborhoods of `s` and `t`. -/
    choose u v hu hv hxu htv huv using SetCoe.forall'.1 H
    rcases precise_refinement_set hs u hu fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxu _⟩ with
      ⟨u', hu'o, hcov', hu'fin, hsub⟩
    refine ⟨⋃ i, u' i, (closure (⋃ i, u' i))ᶜ, isOpen_iUnion hu'o, isClosed_closure.isOpen_compl,
      hcov', ?_, disjoint_compl_right.mono le_rfl (compl_le_compl subset_closure)⟩
    rw [hu'fin.closure_iUnion]; rw [compl_iUnion]; rw [subset_iInter_iff]
    refine fun i x hxt hxu =>
      absurd (htv i hxt) (closure_minimal ?_ (isClosed_compl_iff.2 <| hv _) hxu)
    exact fun y hyu hyv => (huv i).le_bot ⟨hsub _ hyu, hyv⟩
  -- Now we apply the lemma twice: first to `s` and `t`, then to `t` and each point of `s`.
  refine { normal := fun s t hs ht hst => this s t hs fun x hx => ?_ }
  rcases this t {x} ht fun y hy => (by
    simp_rw [singleton_subset_iff]
exact r1_separation ht.not_inseparable hy hst.notMem_of_mem_left hx)
    with ⟨v, u, hv, hu, htv, hxu, huv⟩
  exact ⟨u, v, hu, hv, singleton_subset_iff.1 hxu, htv, huv.symm⟩
