/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.ContinuousLinearEquiv
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# (Strict) convexity and linear isometries

In this file we prove some basic lemmas about (strict) convexity and linear isometries.
-/

public section

open Function Set Metric
open scoped Convex

section SeminormedAddCommGroup

variable {𝕜 E F : Type*}
  [NormedField 𝕜] [PartialOrder 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

@[simp]
/--
lemma `LinearIsometryEquiv.strictConvex_preimage` / 引理 `LinearIsometryEquiv.strictConvex_preimage`

English:
lemma LinearIsometryEquiv.strictConvex_preimage
  given: {s : Set F} (e : E ≃ₗᵢ[𝕜] F)
  proof: e.toContinuousLinearEquiv.strictConvex_preimage

@[simp]

中文:
引理 线性等距等价.strictConvex_preimage
  条件: {s : 集合 F} (e : E ≃ₗᵢ[𝕜] F)
  证明: e.toContinuousLinearEquiv.strictConvex_preimage

@[simp]

Depends on / 依赖: e.toContinuousLinearEquiv.strictConvex_preimage, strictConvex_preimage, toContinuousLinearEquiv
-/
lemma LinearIsometryEquiv.strictConvex_preimage {s : Set F} (e : E ≃ₗᵢ[𝕜] F) :
    StrictConvex 𝕜 (e ⁻¹' s) ↔ StrictConvex 𝕜 s :=
  e.toContinuousLinearEquiv.strictConvex_preimage

@[simp]
/--
lemma `LinearIsometryEquiv.strictConvex_image` / 引理 `LinearIsometryEquiv.strictConvex_image`

English:
lemma LinearIsometryEquiv.strictConvex_image
  given: {s : Set E} (e : E ≃ₗᵢ[𝕜] F)
  proof: e.toContinuousLinearEquiv.strictConvex_image

中文:
引理 线性等距等价.strictConvex_image
  条件: {s : 集合 E} (e : E ≃ₗᵢ[𝕜] F)
  证明: e.toContinuousLinearEquiv.strictConvex_image

Depends on / 依赖: e.toContinuousLinearEquiv.strictConvex_image, strictConvex_image, toContinuousLinearEquiv
-/
lemma LinearIsometryEquiv.strictConvex_image {s : Set E} (e : E ≃ₗᵢ[𝕜] F) :
    StrictConvex 𝕜 (e '' s) ↔ StrictConvex 𝕜 s :=
  e.toContinuousLinearEquiv.strictConvex_image

end SeminormedAddCommGroup

variable {𝕜 E F : Type*} [NormedField 𝕜] [PartialOrder 𝕜]

/--
lemma `StrictConvex.linearIsometry_preimage` / 引理 `StrictConvex.linearIsometry_preimage`

English:
lemma StrictConvex.linearIsometry_preimage
  statement: [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  proof: hs.linear_preimage _ e.continuous e.injective

中文:
引理 严格凸.linearIsometry_preimage
  结论: [赋范交换加群 E] [赋范空间 𝕜 E]
  证明: hs.linear_preimage _ e.continuous e.injective

Depends on / 依赖: continuous, e.continuous, e.injective, hs.linear_preimage, injective, linear_preimage
-/
lemma StrictConvex.linearIsometry_preimage [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set F}
    (hs : StrictConvex 𝕜 s) (e : E ->ₗᵢ[𝕜] F) : StrictConvex 𝕜 (e ⁻¹' s) :=
  hs.linear_preimage _ e.continuous e.injective

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/--
lemma `LinearIsometryEquiv.strictConvexSpace_iff` / 引理 `LinearIsometryEquiv.strictConvexSpace_iff`

English:
lemma LinearIsometryEquiv.strictConvexSpace_iff
  given: (e : E ≃ₗᵢ[𝕜] F)
  proof: by
  simp only [strictConvexSpace_iff, ← map_zero e, ← e.image_closedBall, e.strictConvex_image]

中文:
引理 线性等距等价.strictConvexSpace_iff
  条件: (e : E ≃ₗᵢ[𝕜] F)
  证明: by
  simp only [strictConvexSpace_iff, ← map_zero e, ← e.image_closedBall, e.strictConvex_image]
-/
protected lemma LinearIsometryEquiv.strictConvexSpace_iff (e : E ≃ₗᵢ[𝕜] F) :
    StrictConvexSpace 𝕜 E ↔ StrictConvexSpace 𝕜 F := by
  simp only [strictConvexSpace_iff, ← map_zero e, ← e.image_closedBall, e.strictConvex_image]

/--
lemma `LinearIsometry.strictConvexSpace_range_iff` / 引理 `LinearIsometry.strictConvexSpace_range_iff`

English:
lemma LinearIsometry.strictConvexSpace_range_iff
  given: (e : E ->ₗᵢ[𝕜] F)
  proof: e.equivRange.strictConvexSpace_iff.symm

中文:
引理 线性等距.strictConvexSpace_range_iff
  条件: (e : E ->ₗᵢ[𝕜] F)
  证明: e.equivRange.strictConvexSpace_iff.symm

Depends on / 依赖: e.equivRange.strictConvexSpace_iff.symm, equivRange, strictConvexSpace_iff
-/
lemma LinearIsometry.strictConvexSpace_range_iff (e : E ->ₗᵢ[𝕜] F) :
    StrictConvexSpace 𝕜 (e : E ->ₗ[𝕜] F).range ↔ StrictConvexSpace 𝕜 E :=
  e.equivRange.strictConvexSpace_iff.symm

/--
Instance `LinearIsometry.strictConvexSpace_range` / 实例 `LinearIsometry.strictConvexSpace_range`

English:
instance LinearIsometry.strictConvexSpace_range
  signature: [StrictConvexSpace 𝕜 E] (e : E ->ₗᵢ[𝕜] F)
  body: e.strictConvexSpace_range_iff.mpr ‹_›

中文:
实例 线性等距.strictConvexSpace_range
  签名: [严格凸空间 𝕜 E] (e : E ->ₗᵢ[𝕜] F)
  定义体: e.strictConvexSpace_range_iff.mpr ‹_›

Depends on / 依赖: e.strictConvexSpace_range_iff.mpr, strictConvexSpace_range_iff
-/
instance LinearIsometry.strictConvexSpace_range [StrictConvexSpace 𝕜 E] (e : E ->ₗᵢ[𝕜] F) :
    StrictConvexSpace 𝕜 (e : E ->ₗ[𝕜] F).range :=
  e.strictConvexSpace_range_iff.mpr ‹_›

/--
lemma `LinearIsometry.strictConvexSpace` / 引理 `LinearIsometry.strictConvexSpace`

English:
lemma LinearIsometry.strictConvexSpace
  given: [StrictConvexSpace 𝕜 F] (f : E ->ₗᵢ[𝕜] F)
  proof: by
    rw [← f.isometry.preimage_closedBall]
    exact (strictConvex_closedBall _ _ _).linearIsometry_preimage _

中文:
引理 线性等距.strictConvexSpace
  条件: [严格凸空间 𝕜 F] (f : E ->ₗᵢ[𝕜] F)
  证明: by
    rw [← f.isometry.preimage_closedBall]
    exact (strictConvex_closedBall _ _ _).linearIsometry_preimage _

Depends on / 依赖: f.isometry.preimage_closedBall, isometry, linearIsometry_preimage, preimage_closedBall, strictConvex_closedBall
-/
lemma LinearIsometry.strictConvexSpace [StrictConvexSpace 𝕜 F] (f : E ->ₗᵢ[𝕜] F) :
    StrictConvexSpace 𝕜 E where
  strictConvex_closedBall r hr := by
    rw [← f.isometry.preimage_closedBall]
    exact (strictConvex_closedBall _ _ _).linearIsometry_preimage _

/-- A vector subspace of a strict convex space is a strict convex space.

This instance has priority 900
to make sure that instances like `LinearIsometry.strictConvexSpace_range`
are tried before this one. -/
instance (priority := 900) Submodule.instStrictConvexSpace [StrictConvexSpace 𝕜 E]
    (p : Submodule 𝕜 E) : StrictConvexSpace 𝕜 p :=
  p.subtypeₗᵢ.strictConvexSpace
