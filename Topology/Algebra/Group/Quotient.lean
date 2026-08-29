/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Maps.OpenQuotient

/-!
# Topology on the quotient group

In this file we define topology on `G ⧸ N`, where `N` is a subgroup of `G`,
and prove basic properties of this topology.
-/

public section

assert_not_exists Cardinal

open Topology
open scoped Pointwise

variable {G : Type*} [TopologicalSpace G] [Group G]

namespace QuotientGroup

@[to_additive]
/--
Instance `instTopologicalSpace` / 实例 `instTopologicalSpace`

English:
instance instTopologicalSpace
  signature: (N : Subgroup G)
  body: instTopologicalSpaceQuotient

@[to_additive]

中文:
实例 instTopologicalSpace
  签名: (N : 子群 G)
  定义体: instTopologicalSpaceQuotient

@[to_additive]

Depends on / 依赖: instTopologicalSpaceQuotient
-/
instance instTopologicalSpace (N : Subgroup G) : TopologicalSpace (G ⧸ N) :=
  instTopologicalSpaceQuotient

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: G] (N
  body: Quotient.compactSpace

@[to_additive]

中文:
实例 [紧空间
  签名: G] (N
  定义体: Quotient.compactSpace

@[to_additive]

Depends on / 依赖: Quotient, Quotient.compactSpace, compactSpace
-/
instance [CompactSpace G] (N : Subgroup G) : CompactSpace (G ⧸ N) :=
  Quotient.compactSpace

@[to_additive]
/--
theorem `isQuotientMap_mk` / 定理 `isQuotientMap_mk`

English:
theorem isQuotientMap_mk
  given: (N : Subgroup G)
  statement: IsQuotientMap (mk : G -> G ⧸ N)
  proof: isQuotientMap_quot_mk

@[to_additive (attr := continuity, fun_prop)]

中文:
定理 isQuotientMap_mk
  条件: (N : 子群 G)
  结论: 是商映射 (mk : G -> G ⧸ N)
  证明: isQuotientMap_quot_mk

@[to_additive (attr := continuity, fun_prop)]

Depends on / 依赖: isQuotientMap_quot_mk
-/
theorem isQuotientMap_mk (N : Subgroup G) : IsQuotientMap (mk : G -> G ⧸ N) :=
  isQuotientMap_quot_mk

@[to_additive (attr := continuity, fun_prop)]
/--
theorem `continuous_mk` / 定理 `continuous_mk`

English:
theorem continuous_mk
  given: {N : Subgroup G}
  statement: Continuous (mk : G -> G ⧸ N)
  proof: continuous_quot_mk

中文:
定理 continuous_mk
  条件: {N : 子群 G}
  结论: 连续 (mk : G -> G ⧸ N)
  证明: continuous_quot_mk

Depends on / 依赖: continuous_quot_mk
-/
theorem continuous_mk {N : Subgroup G} : Continuous (mk : G -> G ⧸ N) :=
  continuous_quot_mk

section ContinuousMul

variable [SeparatelyContinuousMul G] {N : Subgroup G}

@[to_additive]
/--
theorem `isOpenMap_coe` / 定理 `isOpenMap_coe`

English:
theorem isOpenMap_coe
  statement: IsOpenMap ((↑) : G -> G ⧸ N)
  proof: isOpenMap_quotient_mk'_mul

@[to_additive]

中文:
定理 isOpenMap_coe
  结论: 是开映射 ((↑) : G -> G ⧸ N)
  证明: isOpenMap_quotient_mk'_mul

@[to_additive]

Depends on / 依赖: _mul, isOpenMap_quotient_mk
-/
theorem isOpenMap_coe : IsOpenMap ((↑) : G -> G ⧸ N) := isOpenMap_quotient_mk'_mul

@[to_additive]
/--
theorem `isOpenQuotientMap_mk` / 定理 `isOpenQuotientMap_mk`

English:
theorem isOpenQuotientMap_mk
  statement: IsOpenQuotientMap (mk : G -> G ⧸ N)
  proof: MulAction.isOpenQuotientMap_quotientMk

@[to_additive (attr := simp)]

中文:
定理 isOpenQuotientMap_mk
  结论: 是OpenQuotient映射 (mk : G -> G ⧸ N)
  证明: MulAction.isOpenQuotientMap_quotientMk

@[to_additive (attr := simp)]

Depends on / 依赖: MulAction, MulAction.isOpenQuotientMap_quotientMk, isOpenQuotientMap_quotientMk
-/
theorem isOpenQuotientMap_mk : IsOpenQuotientMap (mk : G -> G ⧸ N) :=
  MulAction.isOpenQuotientMap_quotientMk

@[to_additive (attr := simp)]
/--
theorem `dense_preimage_mk` / 定理 `dense_preimage_mk`

English:
theorem dense_preimage_mk
  given: {s : Set (G ⧸ N)}
  statement: Dense ((↑) ⁻¹' s : Set G) ↔ Dense s
  proof: isOpenQuotientMap_mk.dense_preimage_iff

@[to_additive]

中文:
定理 dense_preimage_mk
  条件: {s : 集合 (G ⧸ N)}
  结论: 稠密 ((↑) ⁻¹' s : 集合 G) ↔ 稠密 s
  证明: isOpenQuotientMap_mk.dense_preimage_iff

@[to_additive]

Depends on / 依赖: dense_preimage_iff, isOpenQuotientMap_mk, isOpenQuotientMap_mk.dense_preimage_iff
-/
theorem dense_preimage_mk {s : Set (G ⧸ N)} : Dense ((↑) ⁻¹' s : Set G) ↔ Dense s :=
  isOpenQuotientMap_mk.dense_preimage_iff

@[to_additive]
/--
theorem `dense_image_mk` / 定理 `dense_image_mk`

English:
theorem dense_image_mk
  given: {s : Set G}
  proof: by
  rw [← dense_preimage_mk]; rw [preimage_image_mk_eq_mul]

@[to_additive]

中文:
定理 dense_image_mk
  条件: {s : 集合 G}
  证明: by
  rw [← dense_preimage_mk]; rw [preimage_image_mk_eq_mul]

@[to_additive]

Depends on / 依赖: dense_preimage_mk, preimage_image_mk_eq_mul
-/
theorem dense_image_mk {s : Set G} :
    Dense (mk '' s : Set (G ⧸ N)) ↔ Dense (s * (N : Set G)) := by
  rw [← dense_preimage_mk]; rw [preimage_image_mk_eq_mul]

@[to_additive]
/--
Instance `instContinuousSMul` / 实例 `instContinuousSMul`

English:
instance instContinuousSMul
  signature: {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
  body: by
    rw [← (IsOpenQuotientMap.id.prodMap isOpenQuotientMap_mk).continuous_comp_iff]
    exact continuous_mk.comp continuous_mul

@[to_additive]

中文:
实例 instContinuousSMul
  签名: {G : 类型} [群 G] [拓扑空间 G] [连续乘法 G]
  定义体: by
    rw [← (IsOpenQuotientMap.id.prodMap isOpenQuotientMap_mk).continuous_comp_iff]
    exact continuous_mk.comp continuous_mul

@[to_additive]

Depends on / 依赖: IsOpenQuotientMap, IsOpenQuotientMap.id.prodMap, continuous_comp_iff, continuous_mk, continuous_mk.comp, continuous_mul, isOpenQuotientMap_mk, prodMap
-/
instance instContinuousSMul {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    {N : Subgroup G} : ContinuousSMul G (G ⧸ N) where
  continuous_smul := by
    rw [← (IsOpenQuotientMap.id.prodMap isOpenQuotientMap_mk).continuous_comp_iff]
    exact continuous_mk.comp continuous_mul

@[to_additive]
/--
Instance `instContinuousConstSMul` / 实例 `instContinuousConstSMul`

English:
instance instContinuousConstSMul
  signature: : ContinuousConstSMul G (G ⧸ N) where
  body: by
    rw [← isOpenQuotientMap_mk.continuous_comp_iff]
exact continuous_mk.comp continuous_const_smul γ

@[to_additive]

中文:
实例 instContinuousConstSMul
  签名: : 连续常数标量乘法 G (G ⧸ N) where
  定义体: by
    rw [← isOpenQuotientMap_mk.continuous_comp_iff]
exact continuous_mk.comp continuous_const_smul γ

@[to_additive]

Depends on / 依赖: continuous_comp_iff, continuous_const_smul, continuous_mk, continuous_mk.comp, isOpenQuotientMap_mk, isOpenQuotientMap_mk.continuous_comp_iff
-/
instance instContinuousConstSMul : ContinuousConstSMul G (G ⧸ N) where
  continuous_const_smul γ := by
    rw [← isOpenQuotientMap_mk.continuous_comp_iff]
exact continuous_mk.comp continuous_const_smul γ

@[to_additive]
/--
theorem `t1Space_iff` / 定理 `t1Space_iff`

English:
theorem t1Space_iff
  proof: by
  rw [← QuotientGroup.preimage_mk_one]; rw [MulAction.IsPretransitive.t1Space_iff G (mk 1)]; rw [isClosed_coinduced]
  rfl

@[to_additive]

中文:
定理 t1Space_iff
  证明: by
  rw [← QuotientGroup.preimage_mk_one]; rw [MulAction.IsPretransitive.t1Space_iff G (mk 1)]; rw [isClosed_coinduced]
  rfl

@[to_additive]

Depends on / 依赖: IsPretransitive, MulAction, MulAction.IsPretransitive.t1Space_iff, QuotientGroup, QuotientGroup.preimage_mk_one, isClosed_coinduced, preimage_mk_one, t1Space_iff
-/
theorem t1Space_iff :
    T1Space (G ⧸ N) ↔ IsClosed (N : Set G) := by
  rw [← QuotientGroup.preimage_mk_one]; rw [MulAction.IsPretransitive.t1Space_iff G (mk 1)]; rw [isClosed_coinduced]
  rfl

@[to_additive]
/--
theorem `discreteTopology_iff` / 定理 `discreteTopology_iff`

English:
theorem discreteTopology_iff
  proof: by
  rw [← QuotientGroup.preimage_mk_one]; rw [MulAction.IsPretransitive.discreteTopology_iff G (mk 1)]; rw [isOpen_coinduced]
  rfl

中文:
定理 discreteTopology_iff
  证明: by
  rw [← QuotientGroup.preimage_mk_one]; rw [MulAction.IsPretransitive.discreteTopology_iff G (mk 1)]; rw [isOpen_coinduced]
  rfl

Depends on / 依赖: IsPretransitive, MulAction, MulAction.IsPretransitive.discreteTopology_iff, QuotientGroup, QuotientGroup.preimage_mk_one, discreteTopology_iff, isOpen_coinduced, preimage_mk_one
-/
theorem discreteTopology_iff :
    DiscreteTopology (G ⧸ N) ↔ IsOpen (N : Set G) := by
  rw [← QuotientGroup.preimage_mk_one]; rw [MulAction.IsPretransitive.discreteTopology_iff G (mk 1)]; rw [isOpen_coinduced]
  rfl

/-- The quotient of a topological group `G` by a closed subgroup `N` is T1.

When `G` is normal, this implies (because `G ⧸ N` is a topological group) that the quotient is T3
(see `QuotientGroup.instT3Space`).

Back to the general case, we will show later that the quotient is in fact T2
since `N` acts on `G` properly. -/
@[to_additive
/-- The quotient of a topological additive group `G` by a closed subgroup `N` is T1.

When `G` is normal, this implies (because `G ⧸ N` is a topological additive group) that the
quotient is T3 (see `QuotientAddGroup.instT3Space`).

Back to the general case, we will show later that the quotient is in fact T2
since `N` acts on `G` properly. -/]
/--
Instance `instT1Space` / 实例 `instT1Space`

English:
instance instT1Space
  signature: [hN : IsClosed (N : Set G)]
  body: t1Space_iff.mpr hN

中文:
实例 instT1Space
  签名: [hN : 是闭集 (N : 集合 G)]
  定义体: t1Space_iff.mpr hN

Depends on / 依赖: t1Space_iff, t1Space_iff.mpr
-/
instance instT1Space [hN : IsClosed (N : Set G)] :
    T1Space (G ⧸ N) :=
  t1Space_iff.mpr hN

-- TODO: `IsOpen` should be a class and this should be an instance
@[to_additive]
/--
theorem `discreteTopology` / 定理 `discreteTopology`

English:
theorem discreteTopology
  given: (hN : IsOpen (N : Set G))
  proof: discreteTopology_iff.mpr hN

中文:
定理 discreteTopology
  条件: (hN : 是开集 (N : 集合 G))
  证明: discreteTopology_iff.mpr hN

Depends on / 依赖: discreteTopology_iff, discreteTopology_iff.mpr
-/
theorem discreteTopology (hN : IsOpen (N : Set G)) :
    DiscreteTopology (G ⧸ N) :=
  discreteTopology_iff.mpr hN

/-- A quotient of a locally compact group is locally compact. -/
@[to_additive]
/--
Instance `instLocallyCompactSpace` / 实例 `instLocallyCompactSpace`

English:
instance instLocallyCompactSpace
  signature: [LocallyCompactSpace G] (N : Subgroup G)
  body: QuotientGroup.isOpenQuotientMap_mk.locallyCompactSpace

中文:
实例 instLocallyCompactSpace
  签名: [局部紧空间 G] (N : 子群 G)
  定义体: QuotientGroup.isOpenQuotientMap_mk.locallyCompactSpace

Depends on / 依赖: QuotientGroup, QuotientGroup.isOpenQuotientMap_mk.locallyCompactSpace, isOpenQuotientMap_mk, locallyCompactSpace
-/
instance instLocallyCompactSpace [LocallyCompactSpace G] (N : Subgroup G) :
    LocallyCompactSpace (G ⧸ N) :=
  QuotientGroup.isOpenQuotientMap_mk.locallyCompactSpace

variable (N)

/-- Neighborhoods in the quotient are precisely the map of neighborhoods in the prequotient. -/
@[to_additive
  /-- Neighborhoods in the quotient are precisely the map of neighborhoods in the prequotient. -/]
/--
theorem `nhds_eq` / 定理 `nhds_eq`

English:
theorem nhds_eq
  given: (x : G)
  statement: 𝓝 (x : G ⧸ N) = Filter.map (↑) (𝓝 x)
  proof: (isOpenQuotientMap_mk.map_nhds_eq _).symm

@[to_additive]

中文:
定理 nhds_eq
  条件: (x : G)
  结论: 𝓝 (x : G ⧸ N) = 滤子.map (↑) (𝓝 x)
  证明: (isOpenQuotientMap_mk.map_nhds_eq _).symm

@[to_additive]

Depends on / 依赖: isOpenQuotientMap_mk, isOpenQuotientMap_mk.map_nhds_eq, map_nhds_eq
-/
theorem nhds_eq (x : G) : 𝓝 (x : G ⧸ N) = Filter.map (↑) (𝓝 x) :=
  (isOpenQuotientMap_mk.map_nhds_eq _).symm

@[to_additive]
/--
Instance `instFirstCountableTopology` / 实例 `instFirstCountableTopology`

English:
instance instFirstCountableTopology
  signature: [FirstCountableTopology G]
  body: mk_surjective.forall.2 fun x => nhds_eq N x ▸ inferInstance

中文:
实例 instFirstCountableTopology
  签名: [第一可数拓扑 G]
  定义体: mk_surjective.forall.2 fun x => nhds_eq N x ▸ inferInstance

Depends on / 依赖: mk_surjective, mk_surjective.forall, nhds_eq
-/
instance instFirstCountableTopology [FirstCountableTopology G] :
    FirstCountableTopology (G ⧸ N) where
  nhds_generated_countable := mk_surjective.forall.2 fun x => nhds_eq N x ▸ inferInstance

/-- The quotient of a second countable topological group by a subgroup is second countable. -/
@[to_additive
  /-- The quotient of a second countable additive topological group by a subgroup is second
  countable. -/]
/--
Instance `instSecondCountableTopology` / 实例 `instSecondCountableTopology`

English:
instance instSecondCountableTopology
  signature: [SecondCountableTopology G]
  body: ContinuousConstSMul.secondCountableTopology

中文:
实例 instSecondCountableTopology
  签名: [第二可数拓扑 G]
  定义体: ContinuousConstSMul.secondCountableTopology

Depends on / 依赖: ContinuousConstSMul, ContinuousConstSMul.secondCountableTopology, secondCountableTopology
-/
instance instSecondCountableTopology [SecondCountableTopology G] :
    SecondCountableTopology (G ⧸ N) :=
  ContinuousConstSMul.secondCountableTopology

end ContinuousMul

variable [IsTopologicalGroup G] (N : Subgroup G)

@[to_additive]
/--
Instance `instIsTopologicalGroup` / 实例 `instIsTopologicalGroup`

English:
instance instIsTopologicalGroup
  signature: [N.Normal]
  body: by
    rw [← (isOpenQuotientMap_mk.prodMap isOpenQuotientMap_mk).continuous_comp_iff]
    exact continuous_mk.comp continuous_mul
  continuous_inv := continuous_inv.quotient_map' _

@[to_additive]

中文:
实例 instIsTopologicalGroup
  签名: [N.正规]
  定义体: by
    rw [← (isOpenQuotientMap_mk.prodMap isOpenQuotientMap_mk).continuous_comp_iff]
    exact continuous_mk.comp continuous_mul
  continuous_inv := continuous_inv.quotient_map' _

@[to_additive]

Depends on / 依赖: continuous_comp_iff, continuous_inv, continuous_inv.quotient_map, continuous_mk, continuous_mk.comp, continuous_mul, isOpenQuotientMap_mk, isOpenQuotientMap_mk.prodMap, prodMap, quotient_map
-/
instance instIsTopologicalGroup [N.Normal] : IsTopologicalGroup (G ⧸ N) where
  continuous_mul := by
    rw [← (isOpenQuotientMap_mk.prodMap isOpenQuotientMap_mk).continuous_comp_iff]
    exact continuous_mk.comp continuous_mul
  continuous_inv := continuous_inv.quotient_map' _

@[to_additive]
/--
theorem `isClosedMap_coe` / 定理 `isClosedMap_coe`

English:
theorem isClosedMap_coe
  given: {H : Subgroup G} (hH : IsCompact (H : Set G))
  proof: by
  intro t ht
  rw [← (isQuotientMap_mk H).isClosed_preimage]; rw [preimage_image_mk_eq_mul]
  exact ht.mul_right_of_isCompact hH

@[to_additive]

中文:
定理 isClosedMap_coe
  条件: {H : 子群 G} (hH : 是紧集 (H : 集合 G))
  证明: by
  intro t ht
  rw [← (isQuotientMap_mk H).isClosed_preimage]; rw [preimage_image_mk_eq_mul]
  exact ht.mul_right_of_isCompact hH

@[to_additive]

Depends on / 依赖: ht.mul_right_of_isCompact, isClosed_preimage, isQuotientMap_mk, mul_right_of_isCompact, preimage_image_mk_eq_mul
-/
theorem isClosedMap_coe {H : Subgroup G} (hH : IsCompact (H : Set G)) :
    IsClosedMap ((↑) : G -> G ⧸ H) := by
  intro t ht
  rw [← (isQuotientMap_mk H).isClosed_preimage]; rw [preimage_image_mk_eq_mul]
  exact ht.mul_right_of_isCompact hH

@[to_additive]
/--
Instance `instT3Space` / 实例 `instT3Space`

English:
instance instT3Space
  signature: [N.Normal] [hN : IsClosed (N : Set G)]
  body: by
  infer_instance

中文:
实例 instT3Space
  签名: [N.正规] [hN : 是闭集 (N : 集合 G)]
  定义体: by
  infer_instance

Depends on / 依赖: infer_instance
-/
instance instT3Space [N.Normal] [hN : IsClosed (N : Set G)] : T3Space (G ⧸ N) := by
  infer_instance

end QuotientGroup
