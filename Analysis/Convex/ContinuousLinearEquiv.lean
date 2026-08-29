/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Strict
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# (Pre)images of strict convex sets under continuous linear equivalences

In this file we prove that the (pre)image of a strict convex set
under a continuous linear equivalence is a strict convex set.
-/

public section

variable {𝕜 E F : Type*}
  [Field 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

namespace ContinuousLinearEquiv

@[simp]
/--
lemma `strictConvex_preimage` / 引理 `strictConvex_preimage`

English:
lemma strictConvex_preimage
  given: {s : Set F} (e : E ≃L[𝕜] F)
  proof: ⟨fun h => Function.LeftInverse.preimage_preimage e.right_inv s ▸
    h.linear_preimage e.symm.toLinearMap e.symm.continuous e.symm.injective,
    fun h => h.linear_preimage e.toLinearMap e.continuous e.injective⟩

@[simp]

中文:
引理 strictConvex_preimage
  条件: {s : 集合 F} (e : E ≃L[𝕜] F)
  证明: ⟨fun h => Function.LeftInverse.preimage_preimage e.right_inv s ▸
    h.linear_preimage e.symm.toLinearMap e.symm.continuous e.symm.injective,
    fun h => h.linear_preimage e.toLinearMap e.continuous e.injective⟩

@[simp]

Depends on / 依赖: Function, Function.LeftInverse.preimage_preimage, LeftInverse, continuous, e.continuous, e.injective, e.right_inv, e.symm.continuous, e.symm.injective, e.symm.toLinearMap, e.toLinearMap, h.linear_preimage, injective, linear_preimage, preimage_preimage, right_inv, toLinearMap
-/
lemma strictConvex_preimage {s : Set F} (e : E ≃L[𝕜] F) :
    StrictConvex 𝕜 (e ⁻¹' s) ↔ StrictConvex 𝕜 s :=
  ⟨fun h => Function.LeftInverse.preimage_preimage e.right_inv s ▸
    h.linear_preimage e.symm.toLinearMap e.symm.continuous e.symm.injective,
    fun h => h.linear_preimage e.toLinearMap e.continuous e.injective⟩

@[simp]
/--
lemma `strictConvex_image` / 引理 `strictConvex_image`

English:
lemma strictConvex_image
  given: {s : Set E} (e : E ≃L[𝕜] F)
  proof: by
  rw [e.image_eq_preimage_symm]; rw [e.symm.strictConvex_preimage]

中文:
引理 strictConvex_image
  条件: {s : 集合 E} (e : E ≃L[𝕜] F)
  证明: by
  rw [e.image_eq_preimage_symm]; rw [e.symm.strictConvex_preimage]

Depends on / 依赖: e.image_eq_preimage_symm, e.symm.strictConvex_preimage, image_eq_preimage_symm, strictConvex_preimage
-/
lemma strictConvex_image {s : Set E} (e : E ≃L[𝕜] F) :
    StrictConvex 𝕜 (e '' s) ↔ StrictConvex 𝕜 s := by
  rw [e.image_eq_preimage_symm]; rw [e.symm.strictConvex_preimage]

end ContinuousLinearEquiv
