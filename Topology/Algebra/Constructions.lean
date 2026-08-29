/-
Copyright (c) 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Topological space structure on the opposite monoid and on the units group

In this file we define `TopologicalSpace` structure on `Mᵐᵒᵖ`, `Mᵃᵒᵖ`, `Mˣ`, and `AddUnits M`.
This file does not import definitions of a topological monoid and/or a continuous multiplicative
action, so we postpone the proofs of `ContinuousMul Mᵐᵒᵖ` etc. till we have these definitions.

## Tags

topological space, opposite monoid, units
-/

@[expose] public section


variable {M N X : Type*}

open Filter Topology

namespace MulOpposite

/-- Put the same topological space structure on the opposite monoid as on the original space. -/
@[to_additive /-- Put the same topological space structure on the opposite monoid as on the original
space. -/]
/--
Instance `instTopologicalSpaceMulOpposite` / 实例 `instTopologicalSpaceMulOpposite`

English:
instance instTopologicalSpaceMulOpposite
  signature: [TopologicalSpace M]
  body: TopologicalSpace.induced (unop : Mᵐᵒᵖ -> M) ‹_›

中文:
实例 instTopologicalSpaceMulOpposite
  签名: [拓扑空间 M]
  定义体: TopologicalSpace.induced (unop : Mᵐᵒᵖ -> M) ‹_›

Depends on / 依赖: TopologicalSpace, TopologicalSpace.induced, induced
-/
instance instTopologicalSpaceMulOpposite [TopologicalSpace M] : TopologicalSpace Mᵐᵒᵖ :=
  TopologicalSpace.induced (unop : Mᵐᵒᵖ -> M) ‹_›

variable [TopologicalSpace M]

@[to_additive (attr := continuity, fun_prop)]
/--
theorem `continuous_unop` / 定理 `continuous_unop`

English:
theorem continuous_unop
  statement: Continuous (unop : Mᵐᵒᵖ -> M)
  proof: continuous_induced_dom

@[to_additive (attr := continuity, fun_prop)]

中文:
定理 continuous_unop
  结论: 连续 (unop : Mᵐᵒᵖ -> M)
  证明: continuous_induced_dom

@[to_additive (attr := continuity, fun_prop)]

Depends on / 依赖: continuous_induced_dom
-/
theorem continuous_unop : Continuous (unop : Mᵐᵒᵖ -> M) :=
  continuous_induced_dom

@[to_additive (attr := continuity, fun_prop)]
/--
theorem `continuous_op` / 定理 `continuous_op`

English:
theorem continuous_op
  statement: Continuous (op : M -> Mᵐᵒᵖ)
  proof: continuous_induced_rng.2 continuous_id

中文:
定理 continuous_op
  结论: 连续 (op : M -> Mᵐᵒᵖ)
  证明: continuous_induced_rng.2 continuous_id

Depends on / 依赖: continuous_id, continuous_induced_rng
-/
theorem continuous_op : Continuous (op : M -> Mᵐᵒᵖ) :=
  continuous_induced_rng.2 continuous_id

/-- `MulOpposite.op` as a homeomorphism. -/
@[to_additive (attr := simps!) /-- `AddOpposite.op` as a homeomorphism. -/]
/--
Definition of `opHomeomorph` / `opHomeomorph` 的定义

English:
definition opHomeomorph
  signature: : M ≃ₜ Mᵐᵒᵖ where
  body: opEquiv

@[to_additive]

中文:
定义 opHomeomorph
  签名: : M ≃ₜ Mᵐᵒᵖ where
  定义体: opEquiv

@[to_additive]

Depends on / 依赖: opEquiv
-/
def opHomeomorph : M ≃ₜ Mᵐᵒᵖ where
  toEquiv := opEquiv

@[to_additive]
/--
Instance `instT2Space` / 实例 `instT2Space`

English:
instance instT2Space
  signature: [T2Space M]
  body: opHomeomorph.t2Space

@[to_additive]

中文:
实例 instT2Space
  签名: [T2空间 M]
  定义体: opHomeomorph.t2Space

@[to_additive]

Depends on / 依赖: opHomeomorph, opHomeomorph.t2Space, t2Space
-/
instance instT2Space [T2Space M] : T2Space Mᵐᵒᵖ := opHomeomorph.t2Space

@[to_additive]
/--
Instance `instDiscreteTopology` / 实例 `instDiscreteTopology`

English:
instance instDiscreteTopology
  signature: [DiscreteTopology M]
  body: opHomeomorph.symm.isEmbedding.discreteTopology

@[to_additive]

中文:
实例 instDiscreteTopology
  签名: [离散拓扑 M]
  定义体: opHomeomorph.symm.isEmbedding.discreteTopology

@[to_additive]

Depends on / 依赖: discreteTopology, isEmbedding, opHomeomorph, opHomeomorph.symm.isEmbedding.discreteTopology
-/
instance instDiscreteTopology [DiscreteTopology M] : DiscreteTopology Mᵐᵒᵖ :=
  opHomeomorph.symm.isEmbedding.discreteTopology

@[to_additive]
/--
Instance `instCompactSpace` / 实例 `instCompactSpace`

English:
instance instCompactSpace
  signature: [CompactSpace M]
  body: opHomeomorph.compactSpace

@[to_additive]

中文:
实例 instCompactSpace
  签名: [紧空间 M]
  定义体: opHomeomorph.compactSpace

@[to_additive]

Depends on / 依赖: compactSpace, opHomeomorph, opHomeomorph.compactSpace
-/
instance instCompactSpace [CompactSpace M] : CompactSpace Mᵐᵒᵖ :=
  opHomeomorph.compactSpace

@[to_additive]
/--
Instance `instWeaklyLocallyCompactSpace` / 实例 `instWeaklyLocallyCompactSpace`

English:
instance instWeaklyLocallyCompactSpace
  signature: [WeaklyLocallyCompactSpace M]
  body: opHomeomorph.symm.isClosedEmbedding.weaklyLocallyCompactSpace

@[to_additive]

中文:
实例 instWeaklyLocallyCompactSpace
  签名: [WeaklyLocallyCompact空间 M]
  定义体: opHomeomorph.symm.isClosedEmbedding.weaklyLocallyCompactSpace

@[to_additive]

Depends on / 依赖: isClosedEmbedding, opHomeomorph, opHomeomorph.symm.isClosedEmbedding.weaklyLocallyCompactSpace, weaklyLocallyCompactSpace
-/
instance instWeaklyLocallyCompactSpace [WeaklyLocallyCompactSpace M] :
    WeaklyLocallyCompactSpace Mᵐᵒᵖ :=
  opHomeomorph.symm.isClosedEmbedding.weaklyLocallyCompactSpace

@[to_additive]
/--
Instance `instLocallyCompactSpace` / 实例 `instLocallyCompactSpace`

English:
instance instLocallyCompactSpace
  signature: [LocallyCompactSpace M]
  body: opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace

@[to_additive (attr := simp)]

中文:
实例 instLocallyCompactSpace
  签名: [局部紧空间 M]
  定义体: opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace

@[to_additive (attr := simp)]

Depends on / 依赖: isClosedEmbedding, locallyCompactSpace, opHomeomorph, opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
-/
instance instLocallyCompactSpace [LocallyCompactSpace M] :
    LocallyCompactSpace Mᵐᵒᵖ :=
  opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace

@[to_additive (attr := simp)]
/--
theorem `map_op_nhds` / 定理 `map_op_nhds`

English:
theorem map_op_nhds
  given: (x : M)
  statement: map (op : M -> Mᵐᵒᵖ) (𝓝 x) = 𝓝 (op x)
  proof: opHomeomorph.map_nhds_eq x

@[to_additive (attr := simp)]

中文:
定理 map_op_nhds
  条件: (x : M)
  结论: map (op : M -> Mᵐᵒᵖ) (𝓝 x) = 𝓝 (op x)
  证明: opHomeomorph.map_nhds_eq x

@[to_additive (attr := simp)]

Depends on / 依赖: map_nhds_eq, opHomeomorph, opHomeomorph.map_nhds_eq
-/
theorem map_op_nhds (x : M) : map (op : M -> Mᵐᵒᵖ) (𝓝 x) = 𝓝 (op x) :=
  opHomeomorph.map_nhds_eq x

@[to_additive (attr := simp)]
/--
theorem `map_unop_nhds` / 定理 `map_unop_nhds`

English:
theorem map_unop_nhds
  given: (x : Mᵐᵒᵖ)
  statement: map (unop : Mᵐᵒᵖ -> M) (𝓝 x) = 𝓝 (unop x)
  proof: opHomeomorph.symm.map_nhds_eq x

@[to_additive (attr := simp)]

中文:
定理 map_unop_nhds
  条件: (x : Mᵐᵒᵖ)
  结论: map (unop : Mᵐᵒᵖ -> M) (𝓝 x) = 𝓝 (unop x)
  证明: opHomeomorph.symm.map_nhds_eq x

@[to_additive (attr := simp)]

Depends on / 依赖: map_nhds_eq, opHomeomorph, opHomeomorph.symm.map_nhds_eq
-/
theorem map_unop_nhds (x : Mᵐᵒᵖ) : map (unop : Mᵐᵒᵖ -> M) (𝓝 x) = 𝓝 (unop x) :=
  opHomeomorph.symm.map_nhds_eq x

@[to_additive (attr := simp)]
/--
theorem `comap_op_nhds` / 定理 `comap_op_nhds`

English:
theorem comap_op_nhds
  given: (x : Mᵐᵒᵖ)
  statement: comap (op : M -> Mᵐᵒᵖ) (𝓝 x) = 𝓝 (unop x)
  proof: opHomeomorph.comap_nhds_eq x

@[to_additive (attr := simp)]

中文:
定理 comap_op_nhds
  条件: (x : Mᵐᵒᵖ)
  结论: comap (op : M -> Mᵐᵒᵖ) (𝓝 x) = 𝓝 (unop x)
  证明: opHomeomorph.comap_nhds_eq x

@[to_additive (attr := simp)]

Depends on / 依赖: comap_nhds_eq, opHomeomorph, opHomeomorph.comap_nhds_eq
-/
theorem comap_op_nhds (x : Mᵐᵒᵖ) : comap (op : M -> Mᵐᵒᵖ) (𝓝 x) = 𝓝 (unop x) :=
  opHomeomorph.comap_nhds_eq x

@[to_additive (attr := simp)]
/--
theorem `comap_unop_nhds` / 定理 `comap_unop_nhds`

English:
theorem comap_unop_nhds
  given: (x : M)
  statement: comap (unop : Mᵐᵒᵖ -> M) (𝓝 x) = 𝓝 (op x)
  proof: opHomeomorph.symm.comap_nhds_eq x

中文:
定理 comap_unop_nhds
  条件: (x : M)
  结论: comap (unop : Mᵐᵒᵖ -> M) (𝓝 x) = 𝓝 (op x)
  证明: opHomeomorph.symm.comap_nhds_eq x

Depends on / 依赖: comap_nhds_eq, opHomeomorph, opHomeomorph.symm.comap_nhds_eq
-/
theorem comap_unop_nhds (x : M) : comap (unop : Mᵐᵒᵖ -> M) (𝓝 x) = 𝓝 (op x) :=
  opHomeomorph.symm.comap_nhds_eq x

end MulOpposite

namespace Units

open MulOpposite

variable [TopologicalSpace M] [Monoid M] [TopologicalSpace N] [Monoid N] [TopologicalSpace X]

/-- The units of a monoid are equipped with a topology, via the embedding into `M × M`. -/
@[to_additive
/-- The additive units of a monoid are equipped with a topology, via the embedding into `M × M`. -/]
/--
Instance `instTopologicalSpaceUnits` / 实例 `instTopologicalSpaceUnits`

English:
instance instTopologicalSpaceUnits
  signature: : TopologicalSpace Mˣ
  body: TopologicalSpace.induced (embedProduct M) inferInstance

@[to_additive]

中文:
实例 instTopologicalSpaceUnits
  签名: : 拓扑空间 Mˣ
  定义体: TopologicalSpace.induced (embedProduct M) inferInstance

@[to_additive]

Depends on / 依赖: TopologicalSpace, TopologicalSpace.induced, embedProduct, induced
-/
instance instTopologicalSpaceUnits : TopologicalSpace Mˣ :=
  TopologicalSpace.induced (embedProduct M) inferInstance

@[to_additive]
/--
theorem `isInducing_embedProduct` / 定理 `isInducing_embedProduct`

English:
theorem isInducing_embedProduct
  statement: IsInducing (embedProduct M)
  proof: ⟨rfl⟩

@[to_additive]

中文:
定理 isInducing_embedProduct
  结论: 是Inducing (embedProduct M)
  证明: ⟨rfl⟩

@[to_additive]
-/
theorem isInducing_embedProduct : IsInducing (embedProduct M) := ⟨rfl⟩

@[to_additive]
/--
theorem `isEmbedding_embedProduct` / 定理 `isEmbedding_embedProduct`

English:
theorem isEmbedding_embedProduct
  statement: IsEmbedding (embedProduct M)
  proof: ⟨isInducing_embedProduct, embedProduct_injective M⟩

@[to_additive]

中文:
定理 isEmbedding_embedProduct
  结论: 是嵌入 (embedProduct M)
  证明: ⟨isInducing_embedProduct, embedProduct_injective M⟩

@[to_additive]

Depends on / 依赖: embedProduct_injective, isInducing_embedProduct
-/
theorem isEmbedding_embedProduct : IsEmbedding (embedProduct M) :=
  ⟨isInducing_embedProduct, embedProduct_injective M⟩

@[to_additive]
/--
Instance `instT2Space` / 实例 `instT2Space`

English:
instance instT2Space
  signature: [T2Space M]
  body: isEmbedding_embedProduct.t2Space

@[to_additive]

中文:
实例 instT2Space
  签名: [T2空间 M]
  定义体: isEmbedding_embedProduct.t2Space

@[to_additive]

Depends on / 依赖: isEmbedding_embedProduct, isEmbedding_embedProduct.t2Space, t2Space
-/
instance instT2Space [T2Space M] : T2Space Mˣ := isEmbedding_embedProduct.t2Space

@[to_additive]
/--
Instance `instDiscreteTopology` / 实例 `instDiscreteTopology`

English:
instance instDiscreteTopology
  signature: [DiscreteTopology M]
  body: isEmbedding_embedProduct.discreteTopology

中文:
实例 instDiscreteTopology
  签名: [离散拓扑 M]
  定义体: isEmbedding_embedProduct.discreteTopology

Depends on / 依赖: discreteTopology, isEmbedding_embedProduct, isEmbedding_embedProduct.discreteTopology
-/
instance instDiscreteTopology [DiscreteTopology M] : DiscreteTopology Mˣ :=
  isEmbedding_embedProduct.discreteTopology

/--
lemma `topology_eq_inf` / 引理 `topology_eq_inf`

English:
lemma topology_eq_inf
  proof: by
  simp only [isInducing_embedProduct.1, instTopologicalSpaceProd, induced_inf,
    instTopologicalSpaceMulOpposite, induced_compose]; rfl

中文:
引理 topology_eq_inf
  证明: by
  simp only [isInducing_embedProduct.1, instTopologicalSpaceProd, induced_inf,
    instTopologicalSpaceMulOpposite, induced_compose]; rfl
-/
@[to_additive] lemma topology_eq_inf :
    instTopologicalSpaceUnits =
      .induced (val : Mˣ -> M) ‹_› ⊓ .induced (fun u => ↑u⁻¹ : Mˣ -> M) ‹_› := by
  simp only [isInducing_embedProduct.1, instTopologicalSpaceProd, induced_inf,
    instTopologicalSpaceMulOpposite, induced_compose]; rfl

/-- An auxiliary lemma that can be used to prove that coercion `Mˣ → M` is a topological embedding.
Use `Units.isEmbedding_val₀`, `Units.isEmbedding_val`, or `toUnits_homeomorph` instead. -/
@[to_additive /-- An auxiliary lemma that can be used to prove that coercion `AddUnits M → M` is a
topological embedding. Use `AddUnits.isEmbedding_val` or `toAddUnits_homeomorph` instead. -/]
/--
lemma `isEmbedding_val_mk'` / 引理 `isEmbedding_val_mk'`

English:
lemma isEmbedding_val_mk'
  statement: {M : Type*} [Monoid M] [TopologicalSpace M] {f : M -> M}
  proof: by
  refine ⟨⟨?_⟩, val_injective⟩
  rw [topology_eq_inf]; rw [inf_eq_left]; rw [← continuous_iff_le_induced]; rw [@continuous_iff_continuousAt _ _ (.induced _ _)]
  intro u s hs
  simp only [← hf, nhds_induced, Filter.mem_map] at hs ⊢
  exact ⟨_, mem_inf_principal.1 (hc u u.isUnit hs), fun u' hu' =>

中文:
引理 isEmbedding_val_mk'
  结论: {M : 类型} [幺半群 M] [拓扑空间 M] {f : M -> M}
  证明: by
  refine ⟨⟨?_⟩, val_injective⟩
  rw [topology_eq_inf]; rw [inf_eq_left]; rw [← continuous_iff_le_induced]; rw [@continuous_iff_continuousAt _ _ (.induced _ _)]
  intro u s hs
  simp only [← hf, nhds_induced, Filter.mem_map] at hs ⊢
  exact ⟨_, mem_inf_principal.1 (hc u u.isUnit hs), fun u' hu' =>

Depends on / 依赖: Filter, Filter.mem_map, continuous_iff_continuousAt, continuous_iff_le_induced, induced, inf_eq_left, isUnit, mem_inf_principal, mem_map, nhds_induced, topology_eq_inf, u.isUnit, val_injective
-/
lemma isEmbedding_val_mk' {M : Type*} [Monoid M] [TopologicalSpace M] {f : M -> M}
    (hc : ContinuousOn f {x : M | IsUnit x}) (hf : forall u : Mˣ, f u.1 = ↑u⁻¹) :
    IsEmbedding (val : Mˣ -> M) := by
  refine ⟨⟨?_⟩, val_injective⟩
  rw [topology_eq_inf]; rw [inf_eq_left]; rw [← continuous_iff_le_induced]; rw [@continuous_iff_continuousAt _ _ (.induced _ _)]
  intro u s hs
  simp only [← hf, nhds_induced, Filter.mem_map] at hs ⊢
  exact ⟨_, mem_inf_principal.1 (hc u u.isUnit hs), fun u' hu' => hu' u'.isUnit⟩

/-- An auxiliary lemma that can be used to prove that coercion `Mˣ → M` is a topological embedding.
Use `Units.isEmbedding_val₀`, `Units.isEmbedding_val`, or `toUnits_homeomorph` instead. -/
@[to_additive /-- An auxiliary lemma that can be used to prove that coercion `AddUnits M → M` is a
topological embedding. Use `AddUnits.isEmbedding_val` or `toAddUnits_homeomorph` instead. -/]
/--
lemma `embedding_val_mk` / 引理 `embedding_val_mk`

English:
lemma embedding_val_mk
  statement: {M : Type*} [DivisionMonoid M] [TopologicalSpace M]
  proof: isEmbedding_val_mk' h fun u => (val_inv_eq_inv_val u).symm

@[to_additive]

中文:
引理 embedding_val_mk
  结论: {M : 类型} [Division幺半群 M] [拓扑空间 M]
  证明: isEmbedding_val_mk' h fun u => (val_inv_eq_inv_val u).symm

@[to_additive]

Depends on / 依赖: isEmbedding_val_mk, val_inv_eq_inv_val
-/
lemma embedding_val_mk {M : Type*} [DivisionMonoid M] [TopologicalSpace M]
    (h : ContinuousOn Inv.inv {x : M | IsUnit x}) : IsEmbedding (val : Mˣ -> M) :=
  isEmbedding_val_mk' h fun u => (val_inv_eq_inv_val u).symm

@[to_additive]
/--
theorem `continuous_embedProduct` / 定理 `continuous_embedProduct`

English:
theorem continuous_embedProduct
  statement: Continuous (embedProduct M)
  proof: continuous_induced_dom

@[to_additive (attr := fun_prop)]

中文:
定理 continuous_embedProduct
  结论: 连续 (embedProduct M)
  证明: continuous_induced_dom

@[to_additive (attr := fun_prop)]

Depends on / 依赖: continuous_induced_dom
-/
theorem continuous_embedProduct : Continuous (embedProduct M) :=
  continuous_induced_dom

@[to_additive (attr := fun_prop)]
/--
theorem `continuous_val` / 定理 `continuous_val`

English:
theorem continuous_val
  statement: Continuous ((↑) : Mˣ -> M)
  proof: (@continuous_embedProduct M _ _).fst

@[to_additive]

中文:
定理 continuous_val
  结论: 连续 ((↑) : Mˣ -> M)
  证明: (@continuous_embedProduct M _ _).fst

@[to_additive]

Depends on / 依赖: continuous_embedProduct
-/
theorem continuous_val : Continuous ((↑) : Mˣ -> M) :=
  (@continuous_embedProduct M _ _).fst

@[to_additive]
/--
theorem `continuous_iff` / 定理 `continuous_iff`

English:
theorem continuous_iff
  given: {f : X -> Mˣ}
  proof: by
  simp only [isInducing_embedProduct.continuous_iff, embedProduct_apply, Function.comp_def,
    continuous_prodMk, opHomeomorph.symm.isInducing.continuous_iff, opHomeomorph_symm_apply,
    unop_op]

@[to_additive (attr := fun_prop)]

中文:
定理 continuous_iff
  条件: {f : X -> Mˣ}
  证明: by
  simp only [isInducing_embedProduct.continuous_iff, embedProduct_apply, Function.comp_def,
    continuous_prodMk, opHomeomorph.symm.isInducing.continuous_iff, opHomeomorph_symm_apply,
    unop_op]

@[to_additive (attr := fun_prop)]
-/
protected theorem continuous_iff {f : X -> Mˣ} :
    Continuous f ↔ Continuous (val ∘ f) ∧ Continuous (fun x => ↑(f x)⁻¹ : X -> M) := by
  simp only [isInducing_embedProduct.continuous_iff, embedProduct_apply, Function.comp_def,
    continuous_prodMk, opHomeomorph.symm.isInducing.continuous_iff, opHomeomorph_symm_apply,
    unop_op]

@[to_additive (attr := fun_prop)]
/--
theorem `continuous_coe_inv` / 定理 `continuous_coe_inv`

English:
theorem continuous_coe_inv
  statement: Continuous (fun u => ↑u⁻¹ : Mˣ -> M)
  proof: (Units.continuous_iff.1 continuous_id).2

@[to_additive]

中文:
定理 continuous_coe_inv
  结论: 连续 (fun u => ↑u⁻¹ : Mˣ -> M)
  证明: (Units.continuous_iff.1 continuous_id).2

@[to_additive]

Depends on / 依赖: Units.continuous_iff, continuous_id, continuous_iff
-/
theorem continuous_coe_inv : Continuous (fun u => ↑u⁻¹ : Mˣ -> M) :=
  (Units.continuous_iff.1 continuous_id).2

@[to_additive]
/--
lemma `continuous_map` / 引理 `continuous_map`

English:
lemma continuous_map
  given: {f : M ->* N} (hf : Continuous f)
  statement: Continuous (map f)
  proof: Units.continuous_iff.mpr ⟨hf.comp continuous_val, hf.comp continuous_coe_inv⟩

@[to_additive]

中文:
引理 continuous_map
  条件: {f : M ->* N} (hf : 连续 f)
  结论: 连续 (map f)
  证明: Units.continuous_iff.mpr ⟨hf.comp continuous_val, hf.comp continuous_coe_inv⟩

@[to_additive]

Depends on / 依赖: Units.continuous_iff.mpr, continuous_coe_inv, continuous_iff, continuous_val, hf.comp
-/
lemma continuous_map {f : M ->* N} (hf : Continuous f) : Continuous (map f) :=
  Units.continuous_iff.mpr ⟨hf.comp continuous_val, hf.comp continuous_coe_inv⟩

@[to_additive]
/--
lemma `isOpenMap_map` / 引理 `isOpenMap_map`

English:
lemma isOpenMap_map
  given: {f : M ->* N} (hf_inj : Function.Injective f) (hf : IsOpenMap f)
  proof: by
  rintro _ ⟨U, hU, rfl⟩
have hg_openMap := hf.prodMap opHomeomorph.isOpenMap.comp (hf.comp opHomeomorph.symm.isOpenMap)
  refine ⟨_, hg_openMap U hU, Set.ext fun y => ?_⟩
  simp only [embedProduct, OneHom.coe_mk, Set.mem_preimage, Set.mem_image, Prod.mk.injEq,
    Prod.map, Prod.exists, MulOpposi

中文:
引理 isOpenMap_map
  条件: {f : M ->* N} (hf_inj : 函数.单射 f) (hf : 是开映射 f)
  证明: by
  rintro _ ⟨U, hU, rfl⟩
have hg_openMap := hf.prodMap opHomeomorph.isOpenMap.comp (hf.comp opHomeomorph.symm.isOpenMap)
  refine ⟨_, hg_openMap U hU, Set.ext fun y => ?_⟩
  simp only [embedProduct, OneHom.coe_mk, Set.mem_preimage, Set.mem_image, Prod.mk.injEq,
    Prod.map, Prod.exists, MulOpposi

Depends on / 依赖: MonoidHom, MonoidHom.coe_mk, MulOpposite, MulOpposite.exists, OneHom, OneHom.coe_mk, Prod.exists, Prod.map, Prod.mk.injEq, Set.ext, Set.mem_image, Set.mem_preimage, all_goals, coe_mk, embedProduct, hf.comp, hf.prodMap, hf_inj, hg_openMap, isOpenMap
-/
lemma isOpenMap_map {f : M ->* N} (hf_inj : Function.Injective f) (hf : IsOpenMap f) :
    IsOpenMap (map f) := by
  rintro _ ⟨U, hU, rfl⟩
have hg_openMap := hf.prodMap opHomeomorph.isOpenMap.comp (hf.comp opHomeomorph.symm.isOpenMap)
  refine ⟨_, hg_openMap U hU, Set.ext fun y => ?_⟩
  simp only [embedProduct, OneHom.coe_mk, Set.mem_preimage, Set.mem_image, Prod.mk.injEq,
    Prod.map, Prod.exists, MulOpposite.exists, MonoidHom.coe_mk]
  refine ⟨fun ⟨a, b, h, ha, hb⟩ => ⟨⟨a, b, hf_inj ?_, hf_inj ?_⟩, ?_⟩,
    fun ⟨x, hxV, hx⟩ => ⟨x, x.inv, by simp [hxV, ← hx]⟩⟩
  all_goals simp_all

@[to_additive]
/--
lemma `_root_.Topology.IsInducing.units_map` / 引理 `_root_.Topology.IsInducing.units_map`

English:
lemma _root_.Topology.IsInducing.units_map
  given: {f : M ->* N} (hf : IsInducing f)
  proof: by
  refine .of_comp (continuous_map hf.continuous) continuous_embedProduct ?_
  exact hf.prodMap (opHomeomorph.isInducing.comp <| hf.comp opHomeomorph.symm.isInducing)
.comp isInducing_embedProduct

@[to_additive]

中文:
引理 _root_.拓扑.是Inducing.units_map
  条件: {f : M ->* N} (hf : 是Inducing f)
  证明: by
  refine .of_comp (continuous_map hf.continuous) continuous_embedProduct ?_
  exact hf.prodMap (opHomeomorph.isInducing.comp <| hf.comp opHomeomorph.symm.isInducing)
.comp isInducing_embedProduct

@[to_additive]

Depends on / 依赖: continuous, continuous_embedProduct, continuous_map, hf.comp, hf.continuous, hf.prodMap, isInducing, isInducing_embedProduct, of_comp, opHomeomorph, opHomeomorph.isInducing.comp, opHomeomorph.symm.isInducing, prodMap
-/
lemma _root_.Topology.IsInducing.units_map {f : M ->* N} (hf : IsInducing f) :
    IsInducing (map f) := by
  refine .of_comp (continuous_map hf.continuous) continuous_embedProduct ?_
  exact hf.prodMap (opHomeomorph.isInducing.comp <| hf.comp opHomeomorph.symm.isInducing)
.comp isInducing_embedProduct

@[to_additive]
/--
lemma `_root_.Topology.IsEmbedding.units_map` / 引理 `_root_.Topology.IsEmbedding.units_map`

English:
lemma _root_.Topology.IsEmbedding.units_map
  given: {f : M ->* N} (hf : IsEmbedding f)
  proof: by
  refine .of_comp (continuous_map hf.continuous) continuous_embedProduct ?_
  exact hf.prodMap (opHomeomorph.isEmbedding.comp <| hf.comp opHomeomorph.symm.isEmbedding)
.comp isEmbedding_embedProduct

中文:
引理 _root_.拓扑.是嵌入.units_map
  条件: {f : M ->* N} (hf : 是嵌入 f)
  证明: by
  refine .of_comp (continuous_map hf.continuous) continuous_embedProduct ?_
  exact hf.prodMap (opHomeomorph.isEmbedding.comp <| hf.comp opHomeomorph.symm.isEmbedding)
.comp isEmbedding_embedProduct

Depends on / 依赖: continuous, continuous_embedProduct, continuous_map, hf.comp, hf.continuous, hf.prodMap, isEmbedding, isEmbedding_embedProduct, of_comp, opHomeomorph, opHomeomorph.isEmbedding.comp, opHomeomorph.symm.isEmbedding, prodMap
-/
lemma _root_.Topology.IsEmbedding.units_map {f : M ->* N} (hf : IsEmbedding f) :
    IsEmbedding (map f) := by
  refine .of_comp (continuous_map hf.continuous) continuous_embedProduct ?_
  exact hf.prodMap (opHomeomorph.isEmbedding.comp <| hf.comp opHomeomorph.symm.isEmbedding)
.comp isEmbedding_embedProduct

end Units
