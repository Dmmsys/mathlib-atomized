/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Analysis.Normed.Group.AddTorsor

/-!
# Smooth affine maps

This file contains results about smoothness of affine maps.

## Main results

* `ContinuousAffineMap.contDiff`: a continuous affine map is smooth.
* `AffineMap.contDiff_lineMap_uncurry`: `AffineMap.lineMap` is smooth in its three arguments,
  jointly and pointwise.

-/

public section
namespace ContinuousAffineMap

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/--
theorem `contDiff` / 定理 `contDiff`

English:
theorem contDiff
  given: {n : WithTop Nat∞} (f : V ->ᴬ[𝕜] W)
  statement: ContDiff 𝕜 n f
  proof: by
  rw [f.decomp]
  apply f.contLinear.contDiff.add
  exact contDiff_const

中文:
定理 contDiff
  条件: {n : WithTop 自然数∞} (f : V ->ᴬ[𝕜] W)
  结论: 连续可微 𝕜 n f
  证明: by
  rw [f.decomp]
  apply f.contLinear.contDiff.add
  exact contDiff_const

Depends on / 依赖: contDiff, contDiff_const, contLinear, decomp, f.contLinear.contDiff.add, f.decomp
-/
theorem contDiff {n : WithTop Nat∞} (f : V ->ᴬ[𝕜] W) : ContDiff 𝕜 n f := by
  rw [f.decomp]
  apply f.contLinear.contDiff.add
  exact contDiff_const

end ContinuousAffineMap

namespace AffineMap

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]

set_option backward.isDefEq.respectTransparency.types false in
/-- `AffineMap.lineMap` is smooth in all three arguments. -/
@[fun_prop]
/--
theorem `contDiff_lineMap_uncurry` / 定理 `contDiff_lineMap_uncurry`

English:
theorem contDiff_lineMap_uncurry
  given: {n : WithTop Nat∞}
  proof: by
  simp only [AffineMap.lineMap_apply_module]
  fun_prop

中文:
定理 contDiff_lineMap_uncurry
  条件: {n : WithTop 自然数∞}
  证明: by
  simp only [AffineMap.lineMap_apply_module]
  fun_prop

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply_module, fun_prop, lineMap_apply_module
-/
theorem contDiff_lineMap_uncurry {n : WithTop Nat∞} :
    ContDiff 𝕜 n (fun pqc : V × V × 𝕜 => AffineMap.lineMap pqc.1 pqc.2.1 pqc.2.2) := by
  simp only [AffineMap.lineMap_apply_module]
  fun_prop

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `contDiff_lineMap` / 定理 `contDiff_lineMap`

English:
theorem contDiff_lineMap
  given: (p₀ p₁ : V) {n : WithTop Nat∞}
  proof: by
  fun_prop

中文:
定理 contDiff_lineMap
  条件: (p₀ p₁ : V) {n : WithTop 自然数∞}
  证明: by
  fun_prop

Depends on / 依赖: fun_prop
-/
theorem contDiff_lineMap (p₀ p₁ : V) {n : WithTop Nat∞} :
    ContDiff 𝕜 n (AffineMap.lineMap p₀ p₁ : 𝕜 -> V) := by
  fun_prop

end AffineMap

section LineMapComp

variable {𝕜 V E : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f₁ f₂ : E -> V} {g : E -> 𝕜} {s : Set E} {x : E} {n : WithTop Nat∞}

set_option backward.isDefEq.respectTransparency.types false in
@[fun_prop]
/--
theorem `ContDiffWithinAt.lineMap` / 定理 `ContDiffWithinAt.lineMap`

English:
theorem ContDiffWithinAt.lineMap
  statement: (h₁ : ContDiffWithinAt 𝕜 n f₁ s x)
  proof: by
  simp only [AffineMap.lineMap_apply_module]
  fun_prop

中文:
定理 ContDiffWithinAt.lineMap
  结论: (h₁ : ContDiffWithinAt 𝕜 n f₁ s x)
  证明: by
  simp only [AffineMap.lineMap_apply_module]
  fun_prop

Depends on / 依赖: AffineMap, AffineMap.lineMap_apply_module, fun_prop, lineMap_apply_module
-/
theorem ContDiffWithinAt.lineMap (h₁ : ContDiffWithinAt 𝕜 n f₁ s x)
    (h₂ : ContDiffWithinAt 𝕜 n f₂ s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    ContDiffWithinAt 𝕜 n (fun x => AffineMap.lineMap (f₁ x) (f₂ x) (g x)) s x := by
  simp only [AffineMap.lineMap_apply_module]
  fun_prop

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `ContDiffAt.lineMap` / 定理 `ContDiffAt.lineMap`

English:
theorem ContDiffAt.lineMap
  statement: (h₁ : ContDiffAt 𝕜 n f₁ x)
  proof: by
  fun_prop

中文:
定理 ContDiffAt.lineMap
  结论: (h₁ : ContDiffAt 𝕜 n f₁ x)
  证明: by
  fun_prop

Depends on / 依赖: fun_prop
-/
theorem ContDiffAt.lineMap (h₁ : ContDiffAt 𝕜 n f₁ x)
    (h₂ : ContDiffAt 𝕜 n f₂ x) (hg : ContDiffAt 𝕜 n g x) :
    ContDiffAt 𝕜 n (fun x => AffineMap.lineMap (f₁ x) (f₂ x) (g x)) x := by
  fun_prop

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `ContDiffOn.lineMap` / 定理 `ContDiffOn.lineMap`

English:
theorem ContDiffOn.lineMap
  statement: (h₁ : ContDiffOn 𝕜 n f₁ s)
  proof: by
  fun_prop

中文:
定理 ContDiffOn.lineMap
  结论: (h₁ : ContDiffOn 𝕜 n f₁ s)
  证明: by
  fun_prop

Depends on / 依赖: fun_prop
-/
theorem ContDiffOn.lineMap (h₁ : ContDiffOn 𝕜 n f₁ s)
    (h₂ : ContDiffOn 𝕜 n f₂ s) (hg : ContDiffOn 𝕜 n g s) :
    ContDiffOn 𝕜 n (fun x => AffineMap.lineMap (f₁ x) (f₂ x) (g x)) s := by
  fun_prop

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `ContDiff.lineMap` / 定理 `ContDiff.lineMap`

English:
theorem ContDiff.lineMap
  statement: (h₁ : ContDiff 𝕜 n f₁)
  proof: by
  fun_prop

中文:
定理 连续可微.lineMap
  结论: (h₁ : 连续可微 𝕜 n f₁)
  证明: by
  fun_prop

Depends on / 依赖: fun_prop
-/
theorem ContDiff.lineMap (h₁ : ContDiff 𝕜 n f₁)
    (h₂ : ContDiff 𝕜 n f₂) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun x => AffineMap.lineMap (f₁ x) (f₂ x) (g x)) := by
  fun_prop

end LineMapComp
