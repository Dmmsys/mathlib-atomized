/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivative of `x ↦ f (cx)`

In this file we prove that the derivative of `fun x ↦ f (c * x)`
equals `c` times the derivative of `f` evaluated at `c * x`.

Since Mathlib uses `0` as the fallback value for the derivatives whenever they are undefined,
the theorems in this file require neither differentiability of `f`,
nor assumptions like `UniqueDiffWithinAt 𝕜 s x`.
-/

public section

open Set
open scoped Pointwise

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {c : 𝕜} {f : 𝕜 -> E} {f' : E} {s : Set 𝕜} {x : 𝕜}

/--
theorem `hasDerivWithinAt_comp_mul_left_smul_iff` / 定理 `hasDerivWithinAt_comp_mul_left_smul_iff`

English:
theorem hasDerivWithinAt_comp_mul_left_smul_iff
  proof: by
  simp only [hasDerivWithinAt_iff_hasFDerivWithinAt, ← smul_eq_mul,
    ← hasFDerivWithinAt_comp_smul_smul_iff, ContinuousLinearMap.toSpanSingleton_smul]

中文:
定理 hasDerivWithinAt_comp_mul_left_smul_iff
  证明: by
  simp only [hasDerivWithinAt_iff_hasFDerivWithinAt, ← smul_eq_mul,
    ← hasFDerivWithinAt_comp_smul_smul_iff, ContinuousLinearMap.toSpanSingleton_smul]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.toSpanSingleton_smul, hasDerivWithinAt_iff_hasFDerivWithinAt, hasFDerivWithinAt_comp_smul_smul_iff, smul_eq_mul, toSpanSingleton_smul
-/
theorem hasDerivWithinAt_comp_mul_left_smul_iff :
    HasDerivWithinAt (f <| c * ·) (c • f') s x ↔ HasDerivWithinAt f f' (c • s) (c * x) := by
  simp only [hasDerivWithinAt_iff_hasFDerivWithinAt, ← smul_eq_mul,
    ← hasFDerivWithinAt_comp_smul_smul_iff, ContinuousLinearMap.toSpanSingleton_smul]

variable (c f s x) in
/--
theorem `derivWithin_comp_mul_left` / 定理 `derivWithin_comp_mul_left`

English:
theorem derivWithin_comp_mul_left
  proof: by
  simp only [← smul_eq_mul]
  rw [← derivWithin_const_smul_field]; rw [derivWithin]; rw [derivWithin]; rw [fderivWithin_comp_smul_eq_fderivWithin_smul]; rw [Pi.smul_def]

中文:
定理 derivWithin_comp_mul_left
  证明: by
  simp only [← smul_eq_mul]
  rw [← derivWithin_const_smul_field]; rw [derivWithin]; rw [derivWithin]; rw [fderivWithin_comp_smul_eq_fderivWithin_smul]; rw [Pi.smul_def]

Depends on / 依赖: Pi.smul_def, derivWithin, derivWithin_const_smul_field, fderivWithin_comp_smul_eq_fderivWithin_smul, smul_def, smul_eq_mul
-/
theorem derivWithin_comp_mul_left :
    derivWithin (f <| c * ·) s x = c • derivWithin f (c • s) (c * x) := by
  simp only [← smul_eq_mul]
  rw [← derivWithin_const_smul_field]; rw [derivWithin]; rw [derivWithin]; rw [fderivWithin_comp_smul_eq_fderivWithin_smul]; rw [Pi.smul_def]

variable (c f x) in
/--
theorem `deriv_comp_mul_left` / 定理 `deriv_comp_mul_left`

English:
theorem deriv_comp_mul_left
  statement: deriv (f <| c * ·) x = c • deriv f (c * x)
  proof: by
  simp only [← smul_eq_mul, deriv, fderiv_comp_smul, smul_apply]

中文:
定理 deriv_comp_mul_left
  结论: deriv (f <| c * ·) x = c • deriv f (c * x)
  证明: by
  simp only [← smul_eq_mul, deriv, fderiv_comp_smul, smul_apply]

Depends on / 依赖: fderiv_comp_smul, smul_apply, smul_eq_mul
-/
theorem deriv_comp_mul_left : deriv (f <| c * ·) x = c • deriv f (c * x) := by
  simp only [← smul_eq_mul, deriv, fderiv_comp_smul, smul_apply]
