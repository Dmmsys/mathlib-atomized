/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Metrizable.Urysohn

/-!
# Metrizability of a σ-compact manifold

In this file we show that a σ-compact Hausdorff topological manifold over a finite-dimensional real
vector space is metrizable.
-/

public section


open TopologicalSpace

/-- A σ-compact Hausdorff topological manifold over a finite-dimensional real vector space is
metrizable. -/
/-
**Manifold.metrizableSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Manifold.metrizableSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace R
eal E] [FiniteDimensional Real E] {H : Type*} [TopologicalSpace H] (I : ModelWit
hCorners Real E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [SigmaCom
pactSpace M] [T2Space M] : MetrizableSpace M
参数：I : ModelWithCorners Real E H；M : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.locallyCompactSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {H : Type u_…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `ChartedSpace.locallyCompactSpace`：ChartedSpace.locallyCompactSpace [Loca
llyCompactSpace H] : LocallyCompactSpace M
· 使用定理 `ModelWithCorners.secondCountableTopology`：∀ {𝕜 : Type u_1} [inst : Nontr
iviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `ChartedSpace.secondCountable_of_sigmaCompact`：ChartedSpace.secondCountab
le_of_sigmaCompact [SecondCountableTopology H] [SigmaCompactSpace M] : SecondCou
ntableTopology M
· 使用定理 `TopologicalSpace.metrizableSpace_of_t3_secondCountable`：∀ (X : Type u_1)
 [inst : TopologicalSpace X] [T3Space X] [SecondCountableTopology X], Topologica
lSpace.MetrizableSpace X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `NormalSpace.of_paracompactSpace_r1Space`：∀ {X : Type v} [inst : Topologi
calSpace X] [R1Space X] [ParacompactSpace X], NormalSpace X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `paracompact_of_locallyCompact_sigmaCompact`：∀ {X : Type v} [inst : Topol
ogicalSpace X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X] [T2Space X], 
  ParacompactSpace X
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X

--- 原说明 ---
A σ-compact Hausdorff topological manifold over a finite-dimensional real vector
 space is
metrizable.
-/
theorem Manifold.metrizableSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [SigmaCompactSpace M] [T2Space M] :
    MetrizableSpace M := by
  have := I.locallyCompactSpace; have := ChartedSpace.locallyCompactSpace H M
  have := I.secondCountableTopology
  have := ChartedSpace.secondCountable_of_sigmaCompact H M
  exact metrizableSpace_of_t3_secondCountable M
