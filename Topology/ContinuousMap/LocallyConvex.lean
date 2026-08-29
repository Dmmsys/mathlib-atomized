/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# The space of continuous maps is a locally convex space

In this file we prove that the space of continuous maps from a topological space
to a locally convex topological vector space is a locally convex topological vector space.
-/

public section

open scoped Topology

/--
Instance `ContinuousMap.instLocallyConvexSpace` / 实例 `ContinuousMap.instLocallyConvexSpace`

English:
instance ContinuousMap.instLocallyConvexSpace
  signature: {X 𝕜 E : Type*}
  body: .ofBasisZero _ _ _ _ (LocallyConvexSpace.convex_basis_zero 𝕜 E).nhds_continuousMapConst by
    rintro ⟨K, U⟩ ⟨hK, hU₀, hUc⟩ f hf g hg a b ha hb hab x hx
    exact hUc (hf hx) (hg hx) ha hb hab

中文:
实例 ContinuousMap.instLocallyConvexSpace
  签名: {X 𝕜 E : 类型}
  定义体: .ofBasisZero _ _ _ _ (LocallyConvexSpace.convex_basis_zero 𝕜 E).nhds_continuousMapConst by
    rintro ⟨K, U⟩ ⟨hK, hU₀, hUc⟩ f hf g hg a b ha hb hab x hx
    exact hUc (hf hx) (hg hx) ha hb hab

Depends on / 依赖: LocallyConvexSpace, LocallyConvexSpace.convex_basis_zero, convex_basis_zero, nhds_continuousMapConst, ofBasisZero
-/
instance ContinuousMap.instLocallyConvexSpace {X 𝕜 E : Type*}
    [TopologicalSpace X]
    [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [LocallyConvexSpace 𝕜 E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] :
    LocallyConvexSpace 𝕜 C(X, E) :=
.ofBasisZero _ _ _ _ (LocallyConvexSpace.convex_basis_zero 𝕜 E).nhds_continuousMapConst by
    rintro ⟨K, U⟩ ⟨hK, hU₀, hUc⟩ f hf g hg a b ha hb hab x hx
    exact hUc (hf hx) (hg hx) ha hb hab
