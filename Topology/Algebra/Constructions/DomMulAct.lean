/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Topological space structure on `Mᵈᵐᵃ` and `Mᵈᵃᵃ`

In this file we define `TopologicalSpace` structure on `Mᵈᵐᵃ` and `Mᵈᵃᵃ`
and prove basic theorems about these topologies.
The topologies on `Mᵈᵐᵃ` and `Mᵈᵃᵃ` are the same as the topology on `M`.
Formally, they are induced by `DomMulAct.mk.symm` and `DomAddAct.mk.symm`,
since the types aren't definitionally equal.

## Tags

topological space, group action, domain action
-/

@[expose] public section

open Filter TopologicalSpace Topology

namespace DomMulAct

variable {M : Type*} [TopologicalSpace M]

/-- Put the same topological space structure on `Mᵈᵐᵃ` as on the original space. -/
@[to_additive /-- Put the same topological space structure on `Mᵈᵃᵃ` as on the original space. -/]
/--
Instance `instTopologicalSpace` / 实例 `instTopologicalSpace`

English:
instance instTopologicalSpace
  signature: : TopologicalSpace Mᵈᵐᵃ
  body: .induced mk.symm ‹_›

@[to_additive (attr := continuity, fun_prop)]

中文:
实例 instTopologicalSpace
  签名: : 拓扑空间 Mᵈᵐᵃ
  定义体: .induced mk.symm ‹_›

@[to_additive (attr := continuity, fun_prop)]

Depends on / 依赖: induced, mk.symm
-/
instance instTopologicalSpace : TopologicalSpace Mᵈᵐᵃ := .induced mk.symm ‹_›

@[to_additive (attr := continuity, fun_prop)]
/--
theorem `continuous_mk` / 定理 `continuous_mk`

English:
theorem continuous_mk
  statement: Continuous (@mk M)
  proof: continuous_induced_rng.2 continuous_id

@[to_additive (attr := continuity, fun_prop)]

中文:
定理 continuous_mk
  结论: 连续 (@mk M)
  证明: continuous_induced_rng.2 continuous_id

@[to_additive (attr := continuity, fun_prop)]

Depends on / 依赖: continuous_id, continuous_induced_rng
-/
theorem continuous_mk : Continuous (@mk M) := continuous_induced_rng.2 continuous_id

@[to_additive (attr := continuity, fun_prop)]
/--
theorem `continuous_mk_symm` / 定理 `continuous_mk_symm`

English:
theorem continuous_mk_symm
  statement: Continuous (@mk M).symm
  proof: continuous_induced_dom

中文:
定理 continuous_mk_symm
  结论: 连续 (@mk M).symm
  证明: continuous_induced_dom

Depends on / 依赖: continuous_induced_dom
-/
theorem continuous_mk_symm : Continuous (@mk M).symm := continuous_induced_dom

/-- `DomMulAct.mk` as a homeomorphism. -/
@[to_additive (attr := simps toEquiv) /-- `DomAddAct.mk` as a homeomorphism. -/]
/--
Definition of `mkHomeomorph` / `mkHomeomorph` 的定义

English:
definition mkHomeomorph
  signature: : M ≃ₜ Mᵈᵐᵃ where
  body: mk

中文:
定义 mkHomeomorph
  签名: : M ≃ₜ Mᵈᵐᵃ where
  定义体: mk
-/
def mkHomeomorph : M ≃ₜ Mᵈᵐᵃ where
  toEquiv := mk

/--
theorem `coe_mkHomeomorph` / 定理 `coe_mkHomeomorph`

English:
theorem coe_mkHomeomorph
  statement: ⇑(mkHomeomorph : M ≃ₜ Mᵈᵐᵃ) = mk
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coe_mkHomeomorph
  结论: ⇑(mkHomeomorph : M ≃ₜ Mᵈᵐᵃ) = mk
  证明: rfl

@[to_additive (attr := simp)]
-/
@[to_additive (attr := simp)] theorem coe_mkHomeomorph : ⇑(mkHomeomorph : M ≃ₜ Mᵈᵐᵃ) = mk := rfl

@[to_additive (attr := simp)]
/--
theorem `coe_mkHomeomorph_symm` / 定理 `coe_mkHomeomorph_symm`

English:
theorem coe_mkHomeomorph_symm
  statement: ⇑(mkHomeomorph : M ≃ₜ Mᵈᵐᵃ).symm = mk.symm
  proof: rfl

中文:
定理 coe_mkHomeomorph_symm
  结论: ⇑(mkHomeomorph : M ≃ₜ Mᵈᵐᵃ).symm = mk.symm
  证明: rfl
-/
theorem coe_mkHomeomorph_symm : ⇑(mkHomeomorph : M ≃ₜ Mᵈᵐᵃ).symm = mk.symm := rfl

/--
theorem `isInducing_mk` / 定理 `isInducing_mk`

English:
theorem isInducing_mk
  statement: IsInducing (@mk M)
  proof: mkHomeomorph.isInducing

中文:
定理 isInducing_mk
  结论: 是Inducing (@mk M)
  证明: mkHomeomorph.isInducing
-/
@[to_additive] theorem isInducing_mk : IsInducing (@mk M) := mkHomeomorph.isInducing
/--
theorem `isEmbedding_mk` / 定理 `isEmbedding_mk`

English:
theorem isEmbedding_mk
  statement: IsEmbedding (@mk M)
  proof: mkHomeomorph.isEmbedding

中文:
定理 isEmbedding_mk
  结论: 是嵌入 (@mk M)
  证明: mkHomeomorph.isEmbedding
-/
@[to_additive] theorem isEmbedding_mk : IsEmbedding (@mk M) := mkHomeomorph.isEmbedding
/--
theorem `isOpenEmbedding_mk` / 定理 `isOpenEmbedding_mk`

English:
theorem isOpenEmbedding_mk
  statement: IsOpenEmbedding (@mk M)
  proof: mkHomeomorph.isOpenEmbedding

中文:
定理 isOpenEmbedding_mk
  结论: 是开嵌入 (@mk M)
  证明: mkHomeomorph.isOpenEmbedding
-/
@[to_additive] theorem isOpenEmbedding_mk : IsOpenEmbedding (@mk M) := mkHomeomorph.isOpenEmbedding
/--
theorem `isClosedEmbedding_mk` / 定理 `isClosedEmbedding_mk`

English:
theorem isClosedEmbedding_mk
  statement: IsClosedEmbedding (@mk M)
  proof: mkHomeomorph.isClosedEmbedding

中文:
定理 isClosedEmbedding_mk
  结论: 是闭嵌入 (@mk M)
  证明: mkHomeomorph.isClosedEmbedding
-/
@[to_additive] theorem isClosedEmbedding_mk : IsClosedEmbedding (@mk M) :=
  mkHomeomorph.isClosedEmbedding
/--
theorem `isQuotientMap_mk` / 定理 `isQuotientMap_mk`

English:
theorem isQuotientMap_mk
  statement: IsQuotientMap (@mk M)
  proof: mkHomeomorph.isQuotientMap

中文:
定理 isQuotientMap_mk
  结论: 是商映射 (@mk M)
  证明: mkHomeomorph.isQuotientMap
-/
@[to_additive] theorem isQuotientMap_mk : IsQuotientMap (@mk M) := mkHomeomorph.isQuotientMap

/--
theorem `isInducing_mk_symm` / 定理 `isInducing_mk_symm`

English:
theorem isInducing_mk_symm
  statement: IsInducing (@mk M).symm
  proof: mkHomeomorph.symm.isInducing

中文:
定理 isInducing_mk_symm
  结论: 是Inducing (@mk M).symm
  证明: mkHomeomorph.symm.isInducing
-/
@[to_additive] theorem isInducing_mk_symm : IsInducing (@mk M).symm := mkHomeomorph.symm.isInducing
/--
theorem `isEmbedding_mk_symm` / 定理 `isEmbedding_mk_symm`

English:
theorem isEmbedding_mk_symm
  statement: IsEmbedding (@mk M).symm
  proof: mkHomeomorph.symm.isEmbedding

@[to_additive]

中文:
定理 isEmbedding_mk_symm
  结论: 是嵌入 (@mk M).symm
  证明: mkHomeomorph.symm.isEmbedding

@[to_additive]
-/
@[to_additive] theorem isEmbedding_mk_symm : IsEmbedding (@mk M).symm :=
  mkHomeomorph.symm.isEmbedding

@[to_additive]
/--
theorem `isOpenEmbedding_mk_symm` / 定理 `isOpenEmbedding_mk_symm`

English:
theorem isOpenEmbedding_mk_symm
  statement: IsOpenEmbedding (@mk M).symm
  proof: mkHomeomorph.symm.isOpenEmbedding

@[to_additive]

中文:
定理 isOpenEmbedding_mk_symm
  结论: 是开嵌入 (@mk M).symm
  证明: mkHomeomorph.symm.isOpenEmbedding

@[to_additive]

Depends on / 依赖: isOpenEmbedding, mkHomeomorph, mkHomeomorph.symm.isOpenEmbedding
-/
theorem isOpenEmbedding_mk_symm : IsOpenEmbedding (@mk M).symm := mkHomeomorph.symm.isOpenEmbedding

@[to_additive]
/--
theorem `isClosedEmbedding_mk_symm` / 定理 `isClosedEmbedding_mk_symm`

English:
theorem isClosedEmbedding_mk_symm
  statement: IsClosedEmbedding (@mk M).symm
  proof: mkHomeomorph.symm.isClosedEmbedding

@[to_additive]

中文:
定理 isClosedEmbedding_mk_symm
  结论: 是闭嵌入 (@mk M).symm
  证明: mkHomeomorph.symm.isClosedEmbedding

@[to_additive]

Depends on / 依赖: isClosedEmbedding, mkHomeomorph, mkHomeomorph.symm.isClosedEmbedding
-/
theorem isClosedEmbedding_mk_symm : IsClosedEmbedding (@mk M).symm :=
  mkHomeomorph.symm.isClosedEmbedding

@[to_additive]
/--
theorem `isQuotientMap_mk_symm` / 定理 `isQuotientMap_mk_symm`

English:
theorem isQuotientMap_mk_symm
  statement: IsQuotientMap (@mk M).symm
  proof: mkHomeomorph.symm.isQuotientMap

中文:
定理 isQuotientMap_mk_symm
  结论: 是商映射 (@mk M).symm
  证明: mkHomeomorph.symm.isQuotientMap

Depends on / 依赖: isQuotientMap, mkHomeomorph, mkHomeomorph.symm.isQuotientMap
-/
theorem isQuotientMap_mk_symm : IsQuotientMap (@mk M).symm := mkHomeomorph.symm.isQuotientMap

/--
Instance `instT0Space` / 实例 `instT0Space`

English:
instance instT0Space
  signature: [T0Space M]
  body: mkHomeomorph.t0Space

中文:
实例 instT0Space
  签名: [T0空间 M]
  定义体: mkHomeomorph.t0Space
-/
@[to_additive] instance instT0Space [T0Space M] : T0Space Mᵈᵐᵃ := mkHomeomorph.t0Space
/--
Instance `instT1Space` / 实例 `instT1Space`

English:
instance instT1Space
  signature: [T1Space M]
  body: mkHomeomorph.t1Space

中文:
实例 instT1Space
  签名: [T1空间 M]
  定义体: mkHomeomorph.t1Space
-/
@[to_additive] instance instT1Space [T1Space M] : T1Space Mᵈᵐᵃ := mkHomeomorph.t1Space
/--
Instance `instT2Space` / 实例 `instT2Space`

English:
instance instT2Space
  signature: [T2Space M]
  body: mkHomeomorph.t2Space

中文:
实例 instT2Space
  签名: [T2空间 M]
  定义体: mkHomeomorph.t2Space
-/
@[to_additive] instance instT2Space [T2Space M] : T2Space Mᵈᵐᵃ := mkHomeomorph.t2Space
/--
Instance `instT25Space` / 实例 `instT25Space`

English:
instance instT25Space
  signature: [T25Space M]
  body: mkHomeomorph.t25Space

中文:
实例 instT25Space
  签名: [T25空间 M]
  定义体: mkHomeomorph.t25Space
-/
@[to_additive] instance instT25Space [T25Space M] : T25Space Mᵈᵐᵃ := mkHomeomorph.t25Space
/--
Instance `instT3Space` / 实例 `instT3Space`

English:
instance instT3Space
  signature: [T3Space M]
  body: mkHomeomorph.t3Space

中文:
实例 instT3Space
  签名: [T3空间 M]
  定义体: mkHomeomorph.t3Space
-/
@[to_additive] instance instT3Space [T3Space M] : T3Space Mᵈᵐᵃ := mkHomeomorph.t3Space
/--
Instance `instT4Space` / 实例 `instT4Space`

English:
instance instT4Space
  signature: [T4Space M]
  body: mkHomeomorph.t4Space

中文:
实例 instT4Space
  签名: [T4空间 M]
  定义体: mkHomeomorph.t4Space
-/
@[to_additive] instance instT4Space [T4Space M] : T4Space Mᵈᵐᵃ := mkHomeomorph.t4Space
/--
Instance `instT5Space` / 实例 `instT5Space`

English:
instance instT5Space
  signature: [T5Space M]
  body: mkHomeomorph.t5Space

中文:
实例 instT5Space
  签名: [T5空间 M]
  定义体: mkHomeomorph.t5Space
-/
@[to_additive] instance instT5Space [T5Space M] : T5Space Mᵈᵐᵃ := mkHomeomorph.t5Space

/--
Instance `instR0Space` / 实例 `instR0Space`

English:
instance instR0Space
  signature: [R0Space M]
  body: isEmbedding_mk_symm.r0Space

中文:
实例 instR0Space
  签名: [R0空间 M]
  定义体: isEmbedding_mk_symm.r0Space
-/
@[to_additive] instance instR0Space [R0Space M] : R0Space Mᵈᵐᵃ := isEmbedding_mk_symm.r0Space
/--
Instance `instR1Space` / 实例 `instR1Space`

English:
instance instR1Space
  signature: [R1Space M]
  body: isEmbedding_mk_symm.r1Space

@[to_additive]

中文:
实例 instR1Space
  签名: [R1空间 M]
  定义体: isEmbedding_mk_symm.r1Space

@[to_additive]
-/
@[to_additive] instance instR1Space [R1Space M] : R1Space Mᵈᵐᵃ := isEmbedding_mk_symm.r1Space

@[to_additive]
/--
Instance `instRegularSpace` / 实例 `instRegularSpace`

English:
instance instRegularSpace
  signature: [RegularSpace M]
  body: isEmbedding_mk_symm.regularSpace

@[to_additive]

中文:
实例 instRegularSpace
  签名: [正则空间 M]
  定义体: isEmbedding_mk_symm.regularSpace

@[to_additive]

Depends on / 依赖: isEmbedding_mk_symm, isEmbedding_mk_symm.regularSpace, regularSpace
-/
instance instRegularSpace [RegularSpace M] : RegularSpace Mᵈᵐᵃ := isEmbedding_mk_symm.regularSpace

@[to_additive]
/--
Instance `instNormalSpace` / 实例 `instNormalSpace`

English:
instance instNormalSpace
  signature: [NormalSpace M]
  body: mkHomeomorph.normalSpace

@[to_additive]

中文:
实例 instNormalSpace
  签名: [正规空间 M]
  定义体: mkHomeomorph.normalSpace

@[to_additive]

Depends on / 依赖: mkHomeomorph, mkHomeomorph.normalSpace, normalSpace
-/
instance instNormalSpace [NormalSpace M] : NormalSpace Mᵈᵐᵃ := mkHomeomorph.normalSpace

@[to_additive]
/--
Instance `instCompletelyNormalSpace` / 实例 `instCompletelyNormalSpace`

English:
instance instCompletelyNormalSpace
  signature: [CompletelyNormalSpace M]
  body: isEmbedding_mk_symm.completelyNormalSpace

@[to_additive]

中文:
实例 instCompletelyNormalSpace
  签名: [余mpletelyNormal空间 M]
  定义体: isEmbedding_mk_symm.completelyNormalSpace

@[to_additive]

Depends on / 依赖: completelyNormalSpace, isEmbedding_mk_symm, isEmbedding_mk_symm.completelyNormalSpace
-/
instance instCompletelyNormalSpace [CompletelyNormalSpace M] : CompletelyNormalSpace Mᵈᵐᵃ :=
  isEmbedding_mk_symm.completelyNormalSpace

@[to_additive]
/--
Instance `instDiscreteTopology` / 实例 `instDiscreteTopology`

English:
instance instDiscreteTopology
  signature: [DiscreteTopology M]
  body: isEmbedding_mk_symm.discreteTopology

@[to_additive]

中文:
实例 instDiscreteTopology
  签名: [离散拓扑 M]
  定义体: isEmbedding_mk_symm.discreteTopology

@[to_additive]

Depends on / 依赖: discreteTopology, isEmbedding_mk_symm, isEmbedding_mk_symm.discreteTopology
-/
instance instDiscreteTopology [DiscreteTopology M] : DiscreteTopology Mᵈᵐᵃ :=
  isEmbedding_mk_symm.discreteTopology

@[to_additive]
/--
Instance `instSeparableSpace` / 实例 `instSeparableSpace`

English:
instance instSeparableSpace
  signature: [SeparableSpace M]
  body: isQuotientMap_mk.separableSpace

@[to_additive]

中文:
实例 instSeparableSpace
  签名: [可分空间 M]
  定义体: isQuotientMap_mk.separableSpace

@[to_additive]

Depends on / 依赖: isQuotientMap_mk, isQuotientMap_mk.separableSpace, separableSpace
-/
instance instSeparableSpace [SeparableSpace M] : SeparableSpace Mᵈᵐᵃ :=
  isQuotientMap_mk.separableSpace

@[to_additive]
/--
Instance `instFirstCountableTopology` / 实例 `instFirstCountableTopology`

English:
instance instFirstCountableTopology
  signature: [FirstCountableTopology M]
  body: isInducing_mk_symm.firstCountableTopology

@[to_additive]

中文:
实例 instFirstCountableTopology
  签名: [第一可数拓扑 M]
  定义体: isInducing_mk_symm.firstCountableTopology

@[to_additive]

Depends on / 依赖: firstCountableTopology, isInducing_mk_symm, isInducing_mk_symm.firstCountableTopology
-/
instance instFirstCountableTopology [FirstCountableTopology M] : FirstCountableTopology Mᵈᵐᵃ :=
  isInducing_mk_symm.firstCountableTopology

@[to_additive]
/--
Instance `instSecondCountableTopology` / 实例 `instSecondCountableTopology`

English:
instance instSecondCountableTopology
  signature: [SecondCountableTopology M]
  body: isInducing_mk_symm.secondCountableTopology

@[to_additive]

中文:
实例 instSecondCountableTopology
  签名: [第二可数拓扑 M]
  定义体: isInducing_mk_symm.secondCountableTopology

@[to_additive]

Depends on / 依赖: isInducing_mk_symm, isInducing_mk_symm.secondCountableTopology, secondCountableTopology
-/
instance instSecondCountableTopology [SecondCountableTopology M] : SecondCountableTopology Mᵈᵐᵃ :=
  isInducing_mk_symm.secondCountableTopology

@[to_additive]
/--
Instance `instCompactSpace` / 实例 `instCompactSpace`

English:
instance instCompactSpace
  signature: [CompactSpace M]
  body: mkHomeomorph.compactSpace

@[to_additive]

中文:
实例 instCompactSpace
  签名: [紧空间 M]
  定义体: mkHomeomorph.compactSpace

@[to_additive]

Depends on / 依赖: compactSpace, mkHomeomorph, mkHomeomorph.compactSpace
-/
instance instCompactSpace [CompactSpace M] : CompactSpace Mᵈᵐᵃ :=
  mkHomeomorph.compactSpace

@[to_additive]
/--
Instance `instLocallyCompactSpace` / 实例 `instLocallyCompactSpace`

English:
instance instLocallyCompactSpace
  signature: [LocallyCompactSpace M]
  body: isOpenEmbedding_mk_symm.locallyCompactSpace

@[to_additive]

中文:
实例 instLocallyCompactSpace
  签名: [局部紧空间 M]
  定义体: isOpenEmbedding_mk_symm.locallyCompactSpace

@[to_additive]

Depends on / 依赖: isOpenEmbedding_mk_symm, isOpenEmbedding_mk_symm.locallyCompactSpace, locallyCompactSpace
-/
instance instLocallyCompactSpace [LocallyCompactSpace M] : LocallyCompactSpace Mᵈᵐᵃ :=
  isOpenEmbedding_mk_symm.locallyCompactSpace

@[to_additive]
/--
Instance `instWeaklyLocallyCompactSpace` / 实例 `instWeaklyLocallyCompactSpace`

English:
instance instWeaklyLocallyCompactSpace
  signature: [WeaklyLocallyCompactSpace M]
  body: isClosedEmbedding_mk_symm.weaklyLocallyCompactSpace

@[to_additive (attr := simp)]

中文:
实例 instWeaklyLocallyCompactSpace
  签名: [WeaklyLocallyCompact空间 M]
  定义体: isClosedEmbedding_mk_symm.weaklyLocallyCompactSpace

@[to_additive (attr := simp)]

Depends on / 依赖: isClosedEmbedding_mk_symm, isClosedEmbedding_mk_symm.weaklyLocallyCompactSpace, weaklyLocallyCompactSpace
-/
instance instWeaklyLocallyCompactSpace [WeaklyLocallyCompactSpace M] :
    WeaklyLocallyCompactSpace Mᵈᵐᵃ :=
  isClosedEmbedding_mk_symm.weaklyLocallyCompactSpace

@[to_additive (attr := simp)]
/--
theorem `map_mk_nhds` / 定理 `map_mk_nhds`

English:
theorem map_mk_nhds
  given: (x : M)
  statement: map (mk : M -> Mᵈᵐᵃ) (𝓝 x) = 𝓝 (mk x)
  proof: mkHomeomorph.map_nhds_eq x

@[to_additive (attr := simp)]

中文:
定理 map_mk_nhds
  条件: (x : M)
  结论: map (mk : M -> Mᵈᵐᵃ) (𝓝 x) = 𝓝 (mk x)
  证明: mkHomeomorph.map_nhds_eq x

@[to_additive (attr := simp)]

Depends on / 依赖: map_nhds_eq, mkHomeomorph, mkHomeomorph.map_nhds_eq
-/
theorem map_mk_nhds (x : M) : map (mk : M -> Mᵈᵐᵃ) (𝓝 x) = 𝓝 (mk x) :=
  mkHomeomorph.map_nhds_eq x

@[to_additive (attr := simp)]
/--
theorem `map_mk_symm_nhds` / 定理 `map_mk_symm_nhds`

English:
theorem map_mk_symm_nhds
  given: (x : Mᵈᵐᵃ)
  statement: map (mk.symm : Mᵈᵐᵃ -> M) (𝓝 x) = 𝓝 (mk.symm x)
  proof: mkHomeomorph.symm.map_nhds_eq x

@[to_additive (attr := simp)]

中文:
定理 map_mk_symm_nhds
  条件: (x : Mᵈᵐᵃ)
  结论: map (mk.symm : Mᵈᵐᵃ -> M) (𝓝 x) = 𝓝 (mk.symm x)
  证明: mkHomeomorph.symm.map_nhds_eq x

@[to_additive (attr := simp)]

Depends on / 依赖: map_nhds_eq, mkHomeomorph, mkHomeomorph.symm.map_nhds_eq
-/
theorem map_mk_symm_nhds (x : Mᵈᵐᵃ) : map (mk.symm : Mᵈᵐᵃ -> M) (𝓝 x) = 𝓝 (mk.symm x) :=
  mkHomeomorph.symm.map_nhds_eq x

@[to_additive (attr := simp)]
/--
theorem `comap_mk_nhds` / 定理 `comap_mk_nhds`

English:
theorem comap_mk_nhds
  given: (x : Mᵈᵐᵃ)
  statement: comap (mk : M -> Mᵈᵐᵃ) (𝓝 x) = 𝓝 (mk.symm x)
  proof: mkHomeomorph.comap_nhds_eq x

@[to_additive (attr := simp)]

中文:
定理 comap_mk_nhds
  条件: (x : Mᵈᵐᵃ)
  结论: comap (mk : M -> Mᵈᵐᵃ) (𝓝 x) = 𝓝 (mk.symm x)
  证明: mkHomeomorph.comap_nhds_eq x

@[to_additive (attr := simp)]

Depends on / 依赖: comap_nhds_eq, mkHomeomorph, mkHomeomorph.comap_nhds_eq
-/
theorem comap_mk_nhds (x : Mᵈᵐᵃ) : comap (mk : M -> Mᵈᵐᵃ) (𝓝 x) = 𝓝 (mk.symm x) :=
  mkHomeomorph.comap_nhds_eq x

@[to_additive (attr := simp)]
/--
theorem `comap_mk.symm_nhds` / 定理 `comap_mk.symm_nhds`

English:
theorem comap_mk.symm_nhds
  given: (x : M)
  statement: comap (mk.symm : Mᵈᵐᵃ -> M) (𝓝 x) = 𝓝 (mk x)
  proof: mkHomeomorph.symm.comap_nhds_eq x

中文:
定理 comap_mk.symm_nhds
  条件: (x : M)
  结论: comap (mk.symm : Mᵈᵐᵃ -> M) (𝓝 x) = 𝓝 (mk x)
  证明: mkHomeomorph.symm.comap_nhds_eq x

Depends on / 依赖: comap_nhds_eq, mkHomeomorph, mkHomeomorph.symm.comap_nhds_eq
-/
theorem comap_mk.symm_nhds (x : M) : comap (mk.symm : Mᵈᵐᵃ -> M) (𝓝 x) = 𝓝 (mk x) :=
  mkHomeomorph.symm.comap_nhds_eq x

end DomMulAct
