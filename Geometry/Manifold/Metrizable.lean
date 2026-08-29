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

/--
theorem `Manifold.metrizableSpace` / 定理 `Manifold.metrizableSpace`

English:
theorem Manifold.metrizableSpace
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  have := I.locallyCompactSpace; have := ChartedSpace.locallyCompactSpace H M
  have := I.secondCountableTopology
  have := ChartedSpace.secondCountable_of_sigmaCompact H M
  exact metrizableSpace_of_t3_secondCountable M

中文:
定理 流形.metrizableSpace
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  have := I.locallyCompactSpace; have := ChartedSpace.locallyCompactSpace H M
  have := I.secondCountableTopology
  have := ChartedSpace.secondCountable_of_sigmaCompact H M
  exact metrizableSpace_of_t3_secondCountable M

Depends on / 依赖: ChartedSpace, ChartedSpace.locallyCompactSpace, ChartedSpace.secondCountable_of_sigmaCompact, I.locallyCompactSpace, I.secondCountableTopology, locallyCompactSpace, metrizableSpace_of_t3_secondCountable, secondCountableTopology, secondCountable_of_sigmaCompact
-/
theorem Manifold.metrizableSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners Real E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [SigmaCompactSpace M] [T2Space M] :
    MetrizableSpace M := by
  have := I.locallyCompactSpace; have := ChartedSpace.locallyCompactSpace H M
  have := I.secondCountableTopology
  have := ChartedSpace.secondCountable_of_sigmaCompact H M
  exact metrizableSpace_of_t3_secondCountable M
