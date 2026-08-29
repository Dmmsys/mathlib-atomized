/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Analytic.Inverse
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Analyticity of local inverses
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {f : 𝕜 -> 𝕜} {x : 𝕜}
  [CompleteSpace 𝕜] [CharZero 𝕜]

namespace AnalyticAt

/--
lemma `analyticAt_localInverse` / 引理 `analyticAt_localInverse`

English:
lemma analyticAt_localInverse
  given: (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x != 0)
  proof: by
  let i : 𝕜 ≃L[𝕜] 𝕜 := .unitsEquivAut 𝕜 (.mk0 _ hf') -- multiplication by `deriv f a` as equiv
  have hfd : HasStrictFDerivAt f i.toContinuousLinearMap x := hf.hasStrictDerivAt
  let R : OpenPartialHomeomorph 𝕜 𝕜 := hfd.toOpenPartialHomeomorph _
  have hx : x in R.source := HasStrictFDerivAt.mem_

中文:
引理 analyticAt_localInverse
  条件: (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x != 0)
  证明: by
  let i : 𝕜 ≃L[𝕜] 𝕜 := .unitsEquivAut 𝕜 (.mk0 _ hf') -- multiplication by `deriv f a` as equiv
  have hfd : HasStrictFDerivAt f i.toContinuousLinearMap x := hf.hasStrictDerivAt
  let R : OpenPartialHomeomorph 𝕜 𝕜 := hfd.toOpenPartialHomeomorph _
  have hx : x in R.source := HasStrictFDerivAt.mem_

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source, OpenPartialHomeomorph, R.hasFPowerSeriesAt_symm, R.source, analyticAt, hasFPowerSeriesAt, hasFPowerSeriesAt_symm, hasStrictDerivAt, hf.hasFPowerSeriesAt, hf.hasStrictDerivAt, hfd.toOpenPartialHomeomorph, i.toContinuousLinearMap, mem_toOpenPartialHomeomorph_source, multiplication, source, toContinuousLinearMap, toOpenPartialHomeomorph, unitsEquivAut
-/
lemma analyticAt_localInverse (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x != 0) :
    AnalyticAt 𝕜 (hf.hasStrictDerivAt.localInverse _ _ _ hf') (f x) := by
  let i : 𝕜 ≃L[𝕜] 𝕜 := .unitsEquivAut 𝕜 (.mk0 _ hf') -- multiplication by `deriv f a` as equiv
  have hfd : HasStrictFDerivAt f i.toContinuousLinearMap x := hf.hasStrictDerivAt
  let R : OpenPartialHomeomorph 𝕜 𝕜 := hfd.toOpenPartialHomeomorph _
  have hx : x in R.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
.analyticAt refine R.hasFPowerSeriesAt_symm hx hf.hasFPowerSeriesAt (i := i) ?_
  ext
  simp [i]

end AnalyticAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {g : 𝕜 -> E}

/--
lemma `analyticAt_comp_iff_of_deriv_ne_zero` / 引理 `analyticAt_comp_iff_of_deriv_ne_zero`

English:
lemma analyticAt_comp_iff_of_deriv_ne_zero
  given: (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x != 0)
  proof: by
  refine ⟨fun hg => ?_, (AnalyticAt.comp · hf)⟩
  let r := hf.hasStrictDerivAt.localInverse _ _ _ hf'
  have hra : AnalyticAt 𝕜 r (f x) := hf.analyticAt_localInverse hf'
  have : r (f x) = x := HasStrictFDerivAt.localInverse_apply_image ..
  rw [← this] at hg
exact (hg.comp hra).congr .fun_comp (

中文:
引理 analyticAt_comp_iff_of_deriv_ne_zero
  条件: (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x != 0)
  证明: by
  refine ⟨fun hg => ?_, (AnalyticAt.comp · hf)⟩
  let r := hf.hasStrictDerivAt.localInverse _ _ _ hf'
  have hra : AnalyticAt 𝕜 r (f x) := hf.analyticAt_localInverse hf'
  have : r (f x) = x := HasStrictFDerivAt.localInverse_apply_image ..
  rw [← this] at hg
exact (hg.comp hra).congr .fun_comp (

Depends on / 依赖: AnalyticAt, AnalyticAt.comp, HasStrictDerivAt, HasStrictDerivAt.eventually_right_inverse, HasStrictFDerivAt, HasStrictFDerivAt.localInverse_apply_image, analyticAt_localInverse, eventually_right_inverse, fun_comp, hasStrictDerivAt, hf.analyticAt_localInverse, hf.hasStrictDerivAt.localInverse, hg.comp, localInverse, localInverse_apply_image
-/
lemma analyticAt_comp_iff_of_deriv_ne_zero (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x != 0) :
    AnalyticAt 𝕜 (g ∘ f) x ↔ AnalyticAt 𝕜 g (f x) := by
  refine ⟨fun hg => ?_, (AnalyticAt.comp · hf)⟩
  let r := hf.hasStrictDerivAt.localInverse _ _ _ hf'
  have hra : AnalyticAt 𝕜 r (f x) := hf.analyticAt_localInverse hf'
  have : r (f x) = x := HasStrictFDerivAt.localInverse_apply_image ..
  rw [← this] at hg
exact (hg.comp hra).congr .fun_comp (HasStrictDerivAt.eventually_right_inverse ..) g

end
