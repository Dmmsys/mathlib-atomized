/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv

/-!
# Derivatives of the `tan` and `arctan` functions.

Continuity and derivatives of the tangent and arctangent functions.
-/

public section


noncomputable section

namespace Real

open Set Filter

open scoped Topology Real

/--
theorem `hasStrictDerivAt_tan` / 定理 `hasStrictDerivAt_tan`

English:
theorem hasStrictDerivAt_tan
  given: {x : Real} (h : cos x != 0)
  statement: HasStrictDerivAt tan (1 / cos x ^ 2) x
  proof: mod_cast (Complex.hasStrictDerivAt_tan (by exact mod_cast h)).real_of_complex

中文:
定理 hasStrictDerivAt_tan
  条件: {x : 实数} (h : cos x != 0)
  结论: HasStrictDerivAt tan (1 / cos x ^ 2) x
  证明: mod_cast (Complex.hasStrictDerivAt_tan (by exact mod_cast h)).real_of_complex

Depends on / 依赖: Complex.hasStrictDerivAt_tan, hasStrictDerivAt_tan, mod_cast, real_of_complex
-/
theorem hasStrictDerivAt_tan {x : Real} (h : cos x != 0) : HasStrictDerivAt tan (1 / cos x ^ 2) x :=
  mod_cast (Complex.hasStrictDerivAt_tan (by exact mod_cast h)).real_of_complex

/--
theorem `hasDerivAt_tan` / 定理 `hasDerivAt_tan`

English:
theorem hasDerivAt_tan
  given: {x : Real} (h : cos x != 0)
  statement: HasDerivAt tan (1 / cos x ^ 2) x
  proof: mod_cast (Complex.hasDerivAt_tan (by exact mod_cast h)).real_of_complex

中文:
定理 hasDerivAt_tan
  条件: {x : 实数} (h : cos x != 0)
  结论: 在点处可导 tan (1 / cos x ^ 2) x
  证明: mod_cast (Complex.hasDerivAt_tan (by exact mod_cast h)).real_of_complex

Depends on / 依赖: Complex.hasDerivAt_tan, hasDerivAt_tan, mod_cast, real_of_complex
-/
theorem hasDerivAt_tan {x : Real} (h : cos x != 0) : HasDerivAt tan (1 / cos x ^ 2) x :=
  mod_cast (Complex.hasDerivAt_tan (by exact mod_cast h)).real_of_complex

/--
theorem `tendsto_abs_tan_of_cos_eq_zero` / 定理 `tendsto_abs_tan_of_cos_eq_zero`

English:
theorem tendsto_abs_tan_of_cos_eq_zero
  given: {x : Real} (hx : cos x = 0)
  proof: by
  have hx : Complex.cos x = 0 := mod_cast hx
  simp only [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_tan]
  refine (Complex.tendsto_norm_tan_of_cos_eq_zero hx).comp ?_
  refine Tendsto.inf Complex.continuous_ofReal.continuousAt ?_
  exact tendsto_principal_principal.2 fun y => mt Complex.ofReal_inj.1

中文:
定理 tendsto_abs_tan_of_cos_eq_zero
  条件: {x : 实数} (hx : cos x = 0)
  证明: by
  have hx : Complex.cos x = 0 := mod_cast hx
  simp only [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_tan]
  refine (Complex.tendsto_norm_tan_of_cos_eq_zero hx).comp ?_
  refine Tendsto.inf Complex.continuous_ofReal.continuousAt ?_
  exact tendsto_principal_principal.2 fun y => mt Complex.ofReal_inj.1

Depends on / 依赖: Complex.continuous_ofReal.continuousAt, Complex.cos, Complex.norm_real, Complex.ofReal_inj, Complex.ofReal_tan, Complex.tendsto_norm_tan_of_cos_eq_zero, Real.norm_eq_abs, Tendsto, Tendsto.inf, continuousAt, continuous_ofReal, mod_cast, norm_eq_abs, norm_real, ofReal_inj, ofReal_tan, tendsto_norm_tan_of_cos_eq_zero, tendsto_principal_principal
-/
theorem tendsto_abs_tan_of_cos_eq_zero {x : Real} (hx : cos x = 0) :
    Tendsto (fun x => abs (tan x)) (𝓝[!=] x) atTop := by
  have hx : Complex.cos x = 0 := mod_cast hx
  simp only [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_tan]
  refine (Complex.tendsto_norm_tan_of_cos_eq_zero hx).comp ?_
  refine Tendsto.inf Complex.continuous_ofReal.continuousAt ?_
  exact tendsto_principal_principal.2 fun y => mt Complex.ofReal_inj.1

/--
theorem `tendsto_abs_tan_atTop` / 定理 `tendsto_abs_tan_atTop`

English:
theorem tendsto_abs_tan_atTop
  given: (k : Int)
  proof: tendsto_abs_tan_of_cos_eq_zero cos_eq_zero_iff.2 ⟨k, rfl⟩

中文:
定理 tendsto_abs_tan_atTop
  条件: (k : 整数)
  证明: tendsto_abs_tan_of_cos_eq_zero cos_eq_zero_iff.2 ⟨k, rfl⟩

Depends on / 依赖: cos_eq_zero_iff, tendsto_abs_tan_of_cos_eq_zero
-/
theorem tendsto_abs_tan_atTop (k : Int) :
    Tendsto (fun x => abs (tan x)) (𝓝[!=] ((2 * k + 1) * π / 2)) atTop :=
tendsto_abs_tan_of_cos_eq_zero cos_eq_zero_iff.2 ⟨k, rfl⟩

/--
theorem `continuousAt_tan` / 定理 `continuousAt_tan`

English:
theorem continuousAt_tan
  given: {x : Real}
  statement: ContinuousAt tan x ↔ cos x != 0
  proof: by
  refine ⟨fun hc h₀ => ?_, fun h => (hasDerivAt_tan h).continuousAt⟩
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_abs_tan_of_cos_eq_zero h₀) _
    (hc.norm.tendsto.mono_left inf_le_left)

中文:
定理 continuousAt_tan
  条件: {x : 实数}
  结论: ContinuousAt tan x ↔ cos x != 0
  证明: by
  refine ⟨fun hc h₀ => ?_, fun h => (hasDerivAt_tan h).continuousAt⟩
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_abs_tan_of_cos_eq_zero h₀) _
    (hc.norm.tendsto.mono_left inf_le_left)

Depends on / 依赖: continuousAt, hasDerivAt_tan, hc.norm.tendsto.mono_left, inf_le_left, mono_left, not_tendsto_nhds_of_tendsto_atTop, tendsto, tendsto_abs_tan_of_cos_eq_zero
-/
theorem continuousAt_tan {x : Real} : ContinuousAt tan x ↔ cos x != 0 := by
  refine ⟨fun hc h₀ => ?_, fun h => (hasDerivAt_tan h).continuousAt⟩
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_abs_tan_of_cos_eq_zero h₀) _
    (hc.norm.tendsto.mono_left inf_le_left)

/--
theorem `differentiableAt_tan` / 定理 `differentiableAt_tan`

English:
theorem differentiableAt_tan
  given: {x : Real}
  statement: DifferentiableAt Real tan x ↔ cos x != 0
  proof: ⟨fun h => continuousAt_tan.1 h.continuousAt, fun h => (hasDerivAt_tan h).differentiableAt⟩

@[simp]

中文:
定理 differentiableAt_tan
  条件: {x : 实数}
  结论: DifferentiableAt 实数 tan x ↔ cos x != 0
  证明: ⟨fun h => continuousAt_tan.1 h.continuousAt, fun h => (hasDerivAt_tan h).differentiableAt⟩

@[simp]

Depends on / 依赖: continuousAt, continuousAt_tan, differentiableAt, h.continuousAt, hasDerivAt_tan
-/
theorem differentiableAt_tan {x : Real} : DifferentiableAt Real tan x ↔ cos x != 0 :=
  ⟨fun h => continuousAt_tan.1 h.continuousAt, fun h => (hasDerivAt_tan h).differentiableAt⟩

@[simp]
/--
theorem `deriv_tan` / 定理 `deriv_tan`

English:
theorem deriv_tan
  given: (x : Real)
  statement: deriv tan x = 1 / cos x ^ 2
  proof: if h : cos x = 0 then by
    have : ¬DifferentiableAt Real tan x := mt differentiableAt_tan.1 (Classical.not_not.2 h)
    simp [deriv_zero_of_not_differentiableAt this, h, sq]
  else (hasDerivAt_tan h).deriv

@[simp]

中文:
定理 deriv_tan
  条件: (x : 实数)
  结论: deriv tan x = 1 / cos x ^ 2
  证明: if h : cos x = 0 then by
    have : ¬DifferentiableAt Real tan x := mt differentiableAt_tan.1 (Classical.not_not.2 h)
    simp [deriv_zero_of_not_differentiableAt this, h, sq]
  else (hasDerivAt_tan h).deriv

@[simp]

Depends on / 依赖: Classical, Classical.not_not, DifferentiableAt, deriv_zero_of_not_differentiableAt, differentiableAt_tan, hasDerivAt_tan, not_not
-/
theorem deriv_tan (x : Real) : deriv tan x = 1 / cos x ^ 2 :=
  if h : cos x = 0 then by
    have : ¬DifferentiableAt Real tan x := mt differentiableAt_tan.1 (Classical.not_not.2 h)
    simp [deriv_zero_of_not_differentiableAt this, h, sq]
  else (hasDerivAt_tan h).deriv

@[simp]
/--
theorem `contDiffAt_tan` / 定理 `contDiffAt_tan`

English:
theorem contDiffAt_tan
  given: {n : WithTop Nat∞} {x : Real}
  statement: ContDiffAt Real n tan x ↔ cos x != 0
  proof: ⟨fun h => continuousAt_tan.1 h.continuousAt, fun h =>
    (Complex.contDiffAt_tan.2 <| mod_cast h).real_of_complex⟩

中文:
定理 contDiffAt_tan
  条件: {n : WithTop 自然数∞} {x : 实数}
  结论: ContDiffAt 实数 n tan x ↔ cos x != 0
  证明: ⟨fun h => continuousAt_tan.1 h.continuousAt, fun h =>
    (Complex.contDiffAt_tan.2 <| mod_cast h).real_of_complex⟩

Depends on / 依赖: Complex.contDiffAt_tan, contDiffAt_tan, continuousAt, continuousAt_tan, h.continuousAt, mod_cast, real_of_complex
-/
theorem contDiffAt_tan {n : WithTop Nat∞} {x : Real} : ContDiffAt Real n tan x ↔ cos x != 0 :=
  ⟨fun h => continuousAt_tan.1 h.continuousAt, fun h =>
    (Complex.contDiffAt_tan.2 <| mod_cast h).real_of_complex⟩

/--
theorem `hasDerivAt_tan_of_mem_Ioo` / 定理 `hasDerivAt_tan_of_mem_Ioo`

English:
theorem hasDerivAt_tan_of_mem_Ioo
  given: {x : Real} (h : x in Ioo (-(π / 2) : Real) (π / 2))
  proof: hasDerivAt_tan (cos_pos_of_mem_Ioo h).ne'

中文:
定理 hasDerivAt_tan_of_mem_Ioo
  条件: {x : 实数} (h : x in 开区间 (-(π / 2) : 实数) (π / 2))
  证明: hasDerivAt_tan (cos_pos_of_mem_Ioo h).ne'

Depends on / 依赖: cos_pos_of_mem_Ioo, hasDerivAt_tan
-/
theorem hasDerivAt_tan_of_mem_Ioo {x : Real} (h : x in Ioo (-(π / 2) : Real) (π / 2)) :
    HasDerivAt tan (1 / cos x ^ 2) x :=
  hasDerivAt_tan (cos_pos_of_mem_Ioo h).ne'

/--
theorem `differentiableAt_tan_of_mem_Ioo` / 定理 `differentiableAt_tan_of_mem_Ioo`

English:
theorem differentiableAt_tan_of_mem_Ioo
  given: {x : Real} (h : x in Ioo (-(π / 2) : Real) (π / 2))
  proof: (hasDerivAt_tan_of_mem_Ioo h).differentiableAt

中文:
定理 differentiableAt_tan_of_mem_Ioo
  条件: {x : 实数} (h : x in 开区间 (-(π / 2) : 实数) (π / 2))
  证明: (hasDerivAt_tan_of_mem_Ioo h).differentiableAt

Depends on / 依赖: differentiableAt, hasDerivAt_tan_of_mem_Ioo
-/
theorem differentiableAt_tan_of_mem_Ioo {x : Real} (h : x in Ioo (-(π / 2) : Real) (π / 2)) :
    DifferentiableAt Real tan x :=
  (hasDerivAt_tan_of_mem_Ioo h).differentiableAt

/--
theorem `hasStrictDerivAt_arctan` / 定理 `hasStrictDerivAt_arctan`

English:
theorem hasStrictDerivAt_arctan
  given: (x : Real)
  statement: HasStrictDerivAt arctan (1 / (1 + x ^ 2)) x
  proof: by
  have A : cos (arctan x) != 0 := (cos_arctan_pos x).ne'
  simpa [cos_sq_arctan] using
    tanPartialHomeomorph.hasStrictDerivAt_symm trivial (by simpa) (hasStrictDerivAt_tan A)

中文:
定理 hasStrictDerivAt_arctan
  条件: (x : 实数)
  结论: HasStrictDerivAt arctan (1 / (1 + x ^ 2)) x
  证明: by
  have A : cos (arctan x) != 0 := (cos_arctan_pos x).ne'
  simpa [cos_sq_arctan] using
    tanPartialHomeomorph.hasStrictDerivAt_symm trivial (by simpa) (hasStrictDerivAt_tan A)

Depends on / 依赖: arctan, cos_arctan_pos, cos_sq_arctan, hasStrictDerivAt_symm, hasStrictDerivAt_tan, tanPartialHomeomorph, tanPartialHomeomorph.hasStrictDerivAt_symm
-/
theorem hasStrictDerivAt_arctan (x : Real) : HasStrictDerivAt arctan (1 / (1 + x ^ 2)) x := by
  have A : cos (arctan x) != 0 := (cos_arctan_pos x).ne'
  simpa [cos_sq_arctan] using
    tanPartialHomeomorph.hasStrictDerivAt_symm trivial (by simpa) (hasStrictDerivAt_tan A)

/--
theorem `hasDerivAt_arctan` / 定理 `hasDerivAt_arctan`

English:
theorem hasDerivAt_arctan
  given: (x : Real)
  statement: HasDerivAt arctan (1 / (1 + x ^ 2)) x
  proof: (hasStrictDerivAt_arctan x).hasDerivAt

中文:
定理 hasDerivAt_arctan
  条件: (x : 实数)
  结论: 在点处可导 arctan (1 / (1 + x ^ 2)) x
  证明: (hasStrictDerivAt_arctan x).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_arctan
-/
theorem hasDerivAt_arctan (x : Real) : HasDerivAt arctan (1 / (1 + x ^ 2)) x :=
  (hasStrictDerivAt_arctan x).hasDerivAt

/--
theorem `hasDerivAt_arctan'` / 定理 `hasDerivAt_arctan'`

English:
theorem hasDerivAt_arctan'
  given: (x : Real)
  statement: HasDerivAt arctan (1 + x ^ 2)⁻¹ x
  proof: one_div (1 + x ^ 2) ▸ hasDerivAt_arctan x

中文:
定理 hasDerivAt_arctan'
  条件: (x : 实数)
  结论: 在点处可导 arctan (1 + x ^ 2)⁻¹ x
  证明: one_div (1 + x ^ 2) ▸ hasDerivAt_arctan x

Depends on / 依赖: hasDerivAt_arctan, one_div
-/
theorem hasDerivAt_arctan' (x : Real) : HasDerivAt arctan (1 + x ^ 2)⁻¹ x :=
  one_div (1 + x ^ 2) ▸ hasDerivAt_arctan x

/--
theorem `differentiableAt_arctan` / 定理 `differentiableAt_arctan`

English:
theorem differentiableAt_arctan
  given: (x : Real)
  statement: DifferentiableAt Real arctan x
  proof: (hasDerivAt_arctan x).differentiableAt

中文:
定理 differentiableAt_arctan
  条件: (x : 实数)
  结论: DifferentiableAt 实数 arctan x
  证明: (hasDerivAt_arctan x).differentiableAt

Depends on / 依赖: differentiableAt, hasDerivAt_arctan
-/
theorem differentiableAt_arctan (x : Real) : DifferentiableAt Real arctan x :=
  (hasDerivAt_arctan x).differentiableAt

/--
theorem `differentiable_arctan` / 定理 `differentiable_arctan`

English:
theorem differentiable_arctan
  statement: Differentiable Real arctan
  proof: differentiableAt_arctan

@[simp]

中文:
定理 differentiable_arctan
  结论: 可微 实数 arctan
  证明: differentiableAt_arctan

@[simp]

Depends on / 依赖: differentiableAt_arctan
-/
theorem differentiable_arctan : Differentiable Real arctan :=
  differentiableAt_arctan

@[simp]
/--
theorem `deriv_arctan` / 定理 `deriv_arctan`

English:
theorem deriv_arctan
  statement: deriv arctan = fun (x : Real) => 1 / (1 + x ^ 2)
  proof: funext fun x => (hasDerivAt_arctan x).deriv

中文:
定理 deriv_arctan
  结论: deriv arctan = fun (x : 实数) => 1 / (1 + x ^ 2)
  证明: funext fun x => (hasDerivAt_arctan x).deriv

Depends on / 依赖: hasDerivAt_arctan
-/
theorem deriv_arctan : deriv arctan = fun (x : Real) => 1 / (1 + x ^ 2) :=
  funext fun x => (hasDerivAt_arctan x).deriv

/--
theorem `contDiff_arctan` / 定理 `contDiff_arctan`

English:
theorem contDiff_arctan
  given: {n : WithTop Nat∞}
  statement: ContDiff Real n arctan
  proof: contDiff_iff_contDiffAt.2 fun x =>
    have : cos (arctan x) != 0 := (cos_arctan_pos x).ne'
    tanPartialHomeomorph.contDiffAt_symm_deriv (by simpa) trivial (hasDerivAt_tan this)
      (contDiffAt_tan.2 this)

中文:
定理 contDiff_arctan
  条件: {n : WithTop 自然数∞}
  结论: 连续可微 实数 n arctan
  证明: contDiff_iff_contDiffAt.2 fun x =>
    have : cos (arctan x) != 0 := (cos_arctan_pos x).ne'
    tanPartialHomeomorph.contDiffAt_symm_deriv (by simpa) trivial (hasDerivAt_tan this)
      (contDiffAt_tan.2 this)

Depends on / 依赖: arctan, contDiffAt_symm_deriv, contDiffAt_tan, contDiff_iff_contDiffAt, cos_arctan_pos, hasDerivAt_tan, tanPartialHomeomorph, tanPartialHomeomorph.contDiffAt_symm_deriv
-/
theorem contDiff_arctan {n : WithTop Nat∞} : ContDiff Real n arctan :=
  contDiff_iff_contDiffAt.2 fun x =>
    have : cos (arctan x) != 0 := (cos_arctan_pos x).ne'
    tanPartialHomeomorph.contDiffAt_symm_deriv (by simpa) trivial (hasDerivAt_tan this)
      (contDiffAt_tan.2 this)

end Real

section

/-!
### Lemmas for derivatives of the composition of `Real.arctan` with a differentiable function

In this section we register lemmas for the derivatives of the composition of `Real.arctan` with a
differentiable function, for standalone use and use with `simp`. -/


open Real

section deriv

variable {f : Real -> Real} {f' x : Real} {s : Set Real}

/--
theorem `HasStrictDerivAt.arctan` / 定理 `HasStrictDerivAt.arctan`

English:
theorem HasStrictDerivAt.arctan
  given: (hf : HasStrictDerivAt f f' x)
  proof: (Real.hasStrictDerivAt_arctan (f x)).comp x hf

中文:
定理 HasStrictDerivAt.arctan
  条件: (hf : HasStrictDerivAt f f' x)
  证明: (Real.hasStrictDerivAt_arctan (f x)).comp x hf

Depends on / 依赖: Real.hasStrictDerivAt_arctan, hasStrictDerivAt_arctan
-/
theorem HasStrictDerivAt.arctan (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => arctan (f x)) (1 / (1 + f x ^ 2) * f') x :=
  (Real.hasStrictDerivAt_arctan (f x)).comp x hf

/--
theorem `HasDerivAt.arctan` / 定理 `HasDerivAt.arctan`

English:
theorem HasDerivAt.arctan
  given: (hf : HasDerivAt f f' x)
  proof: (Real.hasDerivAt_arctan (f x)).comp x hf

中文:
定理 在点处可导.arctan
  条件: (hf : 在点处可导 f f' x)
  证明: (Real.hasDerivAt_arctan (f x)).comp x hf

Depends on / 依赖: Real.hasDerivAt_arctan, hasDerivAt_arctan
-/
theorem HasDerivAt.arctan (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => arctan (f x)) (1 / (1 + f x ^ 2) * f') x :=
  (Real.hasDerivAt_arctan (f x)).comp x hf

/--
theorem `HasDerivWithinAt.arctan` / 定理 `HasDerivWithinAt.arctan`

English:
theorem HasDerivWithinAt.arctan
  given: (hf : HasDerivWithinAt f f' s x)
  proof: (Real.hasDerivAt_arctan (f x)).comp_hasDerivWithinAt x hf

中文:
定理 HasDerivWithinAt.arctan
  条件: (hf : HasDerivWithinAt f f' s x)
  证明: (Real.hasDerivAt_arctan (f x)).comp_hasDerivWithinAt x hf

Depends on / 依赖: Real.hasDerivAt_arctan, comp_hasDerivWithinAt, hasDerivAt_arctan
-/
theorem HasDerivWithinAt.arctan (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => arctan (f x)) (1 / (1 + f x ^ 2) * f') s x :=
  (Real.hasDerivAt_arctan (f x)).comp_hasDerivWithinAt x hf

/--
theorem `derivWithin_arctan` / 定理 `derivWithin_arctan`

English:
theorem derivWithin_arctan
  given: (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x)
  proof: hf.hasDerivWithinAt.arctan.derivWithin hxs

@[simp]

中文:
定理 derivWithin_arctan
  条件: (hf : DifferentiableWithinAt 实数 f s x) (hxs : UniqueDiffWithinAt 实数 s x)
  证明: hf.hasDerivWithinAt.arctan.derivWithin hxs

@[simp]

Depends on / 依赖: arctan, derivWithin, hasDerivWithinAt, hf.hasDerivWithinAt.arctan.derivWithin
-/
theorem derivWithin_arctan (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x) :
    derivWithin (fun x => arctan (f x)) s x = 1 / (1 + f x ^ 2) * derivWithin f s x :=
  hf.hasDerivWithinAt.arctan.derivWithin hxs

@[simp]
/--
theorem `deriv_arctan` / 定理 `deriv_arctan`

English:
theorem deriv_arctan
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasDerivAt.arctan.deriv

中文:
定理 deriv_arctan
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasDerivAt.arctan.deriv

Depends on / 依赖: arctan, hasDerivAt, hc.hasDerivAt.arctan.deriv
-/
theorem deriv_arctan (hc : DifferentiableAt Real f x) :
    deriv (fun x => arctan (f x)) x = 1 / (1 + f x ^ 2) * deriv f x :=
  hc.hasDerivAt.arctan.deriv

end deriv

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f : E -> Real} {f' : StrongDual Real E}
  {x : E} {s : Set E} {n : Nat∞}

/--
theorem `HasStrictFDerivAt.arctan` / 定理 `HasStrictFDerivAt.arctan`

English:
theorem HasStrictFDerivAt.arctan
  given: (hf : HasStrictFDerivAt f f' x)
  proof: (hasStrictDerivAt_arctan (f x)).comp_hasStrictFDerivAt x hf

中文:
定理 HasStrictFDerivAt.arctan
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: (hasStrictDerivAt_arctan (f x)).comp_hasStrictFDerivAt x hf

Depends on / 依赖: comp_hasStrictFDerivAt, hasStrictDerivAt_arctan
-/
theorem HasStrictFDerivAt.arctan (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => arctan (f x)) ((1 / (1 + f x ^ 2)) • f') x :=
  (hasStrictDerivAt_arctan (f x)).comp_hasStrictFDerivAt x hf

/--
theorem `HasFDerivAt.arctan` / 定理 `HasFDerivAt.arctan`

English:
theorem HasFDerivAt.arctan
  given: (hf : HasFDerivAt f f' x)
  proof: (hasDerivAt_arctan (f x)).comp_hasFDerivAt x hf

中文:
定理 在点处Fréchet可导.arctan
  条件: (hf : 在点处Fréchet可导 f f' x)
  证明: (hasDerivAt_arctan (f x)).comp_hasFDerivAt x hf

Depends on / 依赖: comp_hasFDerivAt, hasDerivAt_arctan
-/
theorem HasFDerivAt.arctan (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => arctan (f x)) ((1 / (1 + f x ^ 2)) • f') x :=
  (hasDerivAt_arctan (f x)).comp_hasFDerivAt x hf

/--
theorem `HasFDerivWithinAt.arctan` / 定理 `HasFDerivWithinAt.arctan`

English:
theorem HasFDerivWithinAt.arctan
  given: (hf : HasFDerivWithinAt f f' s x)
  proof: (hasDerivAt_arctan (f x)).comp_hasFDerivWithinAt x hf

中文:
定理 HasFDerivWithinAt.arctan
  条件: (hf : HasFDerivWithinAt f f' s x)
  证明: (hasDerivAt_arctan (f x)).comp_hasFDerivWithinAt x hf

Depends on / 依赖: comp_hasFDerivWithinAt, hasDerivAt_arctan
-/
theorem HasFDerivWithinAt.arctan (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => arctan (f x)) ((1 / (1 + f x ^ 2)) • f') s x :=
  (hasDerivAt_arctan (f x)).comp_hasFDerivWithinAt x hf

/--
theorem `fderivWithin_arctan` / 定理 `fderivWithin_arctan`

English:
theorem fderivWithin_arctan
  given: (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x)
  proof: hf.hasFDerivWithinAt.arctan.fderivWithin hxs

@[simp]

中文:
定理 fderivWithin_arctan
  条件: (hf : DifferentiableWithinAt 实数 f s x) (hxs : UniqueDiffWithinAt 实数 s x)
  证明: hf.hasFDerivWithinAt.arctan.fderivWithin hxs

@[simp]

Depends on / 依赖: arctan, fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.arctan.fderivWithin
-/
theorem fderivWithin_arctan (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x) :
    fderivWithin Real (fun x => arctan (f x)) s x = (1 / (1 + f x ^ 2)) • fderivWithin Real f s x :=
  hf.hasFDerivWithinAt.arctan.fderivWithin hxs

@[simp]
/--
theorem `fderiv_arctan` / 定理 `fderiv_arctan`

English:
theorem fderiv_arctan
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasFDerivAt.arctan.fderiv

中文:
定理 fderiv_arctan
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasFDerivAt.arctan.fderiv

Depends on / 依赖: arctan, fderiv, hasFDerivAt, hc.hasFDerivAt.arctan.fderiv
-/
theorem fderiv_arctan (hc : DifferentiableAt Real f x) :
    fderiv Real (fun x => arctan (f x)) x = (1 / (1 + f x ^ 2)) • fderiv Real f x :=
  hc.hasFDerivAt.arctan.fderiv

/--
theorem `DifferentiableWithinAt.arctan` / 定理 `DifferentiableWithinAt.arctan`

English:
theorem DifferentiableWithinAt.arctan
  given: (hf : DifferentiableWithinAt Real f s x)
  proof: hf.hasFDerivWithinAt.arctan.differentiableWithinAt

@[simp]

中文:
定理 DifferentiableWithinAt.arctan
  条件: (hf : DifferentiableWithinAt 实数 f s x)
  证明: hf.hasFDerivWithinAt.arctan.differentiableWithinAt

@[simp]

Depends on / 依赖: arctan, differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.arctan.differentiableWithinAt
-/
theorem DifferentiableWithinAt.arctan (hf : DifferentiableWithinAt Real f s x) :
    DifferentiableWithinAt Real (fun x => Real.arctan (f x)) s x :=
  hf.hasFDerivWithinAt.arctan.differentiableWithinAt

@[simp]
/--
theorem `DifferentiableAt.arctan` / 定理 `DifferentiableAt.arctan`

English:
theorem DifferentiableAt.arctan
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasFDerivAt.arctan.differentiableAt

中文:
定理 DifferentiableAt.arctan
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasFDerivAt.arctan.differentiableAt

Depends on / 依赖: arctan, differentiableAt, hasFDerivAt, hc.hasFDerivAt.arctan.differentiableAt
-/
theorem DifferentiableAt.arctan (hc : DifferentiableAt Real f x) :
    DifferentiableAt Real (fun x => arctan (f x)) x :=
  hc.hasFDerivAt.arctan.differentiableAt

/--
theorem `DifferentiableOn.arctan` / 定理 `DifferentiableOn.arctan`

English:
theorem DifferentiableOn.arctan
  given: (hc : DifferentiableOn Real f s)
  proof: fun x h => (hc x h).arctan

@[simp]

中文:
定理 DifferentiableOn.arctan
  条件: (hc : DifferentiableOn 实数 f s)
  证明: fun x h => (hc x h).arctan

@[simp]

Depends on / 依赖: arctan
-/
theorem DifferentiableOn.arctan (hc : DifferentiableOn Real f s) :
    DifferentiableOn Real (fun x => arctan (f x)) s := fun x h => (hc x h).arctan

@[simp]
/--
theorem `Differentiable.arctan` / 定理 `Differentiable.arctan`

English:
theorem Differentiable.arctan
  given: (hc : Differentiable Real f)
  statement: Differentiable Real fun x => arctan (f x)
  proof: fun x => (hc x).arctan

中文:
定理 可微.arctan
  条件: (hc : 可微 实数 f)
  结论: 可微 实数 fun x => arctan (f x)
  证明: fun x => (hc x).arctan

Depends on / 依赖: arctan
-/
theorem Differentiable.arctan (hc : Differentiable Real f) : Differentiable Real fun x => arctan (f x) :=
  fun x => (hc x).arctan

/--
theorem `ContDiffAt.arctan` / 定理 `ContDiffAt.arctan`

English:
theorem ContDiffAt.arctan
  given: (h : ContDiffAt Real n f x)
  statement: ContDiffAt Real n (fun x => arctan (f x)) x
  proof: contDiff_arctan.contDiffAt.comp x h

中文:
定理 ContDiffAt.arctan
  条件: (h : ContDiffAt 实数 n f x)
  结论: ContDiffAt 实数 n (fun x => arctan (f x)) x
  证明: contDiff_arctan.contDiffAt.comp x h

Depends on / 依赖: contDiffAt, contDiff_arctan, contDiff_arctan.contDiffAt.comp
-/
theorem ContDiffAt.arctan (h : ContDiffAt Real n f x) : ContDiffAt Real n (fun x => arctan (f x)) x :=
  contDiff_arctan.contDiffAt.comp x h

/--
theorem `ContDiff.arctan` / 定理 `ContDiff.arctan`

English:
theorem ContDiff.arctan
  given: (h : ContDiff Real n f)
  statement: ContDiff Real n fun x => arctan (f x)
  proof: contDiff_arctan.comp h

中文:
定理 连续可微.arctan
  条件: (h : 连续可微 实数 n f)
  结论: 连续可微 实数 n fun x => arctan (f x)
  证明: contDiff_arctan.comp h

Depends on / 依赖: contDiff_arctan, contDiff_arctan.comp
-/
theorem ContDiff.arctan (h : ContDiff Real n f) : ContDiff Real n fun x => arctan (f x) :=
  contDiff_arctan.comp h

/--
theorem `ContDiffWithinAt.arctan` / 定理 `ContDiffWithinAt.arctan`

English:
theorem ContDiffWithinAt.arctan
  given: (h : ContDiffWithinAt Real n f s x)
  proof: contDiff_arctan.comp_contDiffWithinAt h

中文:
定理 ContDiffWithinAt.arctan
  条件: (h : ContDiffWithinAt 实数 n f s x)
  证明: contDiff_arctan.comp_contDiffWithinAt h

Depends on / 依赖: comp_contDiffWithinAt, contDiff_arctan, contDiff_arctan.comp_contDiffWithinAt
-/
theorem ContDiffWithinAt.arctan (h : ContDiffWithinAt Real n f s x) :
    ContDiffWithinAt Real n (fun x => arctan (f x)) s x :=
  contDiff_arctan.comp_contDiffWithinAt h

/--
theorem `ContDiffOn.arctan` / 定理 `ContDiffOn.arctan`

English:
theorem ContDiffOn.arctan
  given: (h : ContDiffOn Real n f s)
  statement: ContDiffOn Real n (fun x => arctan (f x)) s
  proof: contDiff_arctan.comp_contDiffOn h

中文:
定理 ContDiffOn.arctan
  条件: (h : ContDiffOn 实数 n f s)
  结论: ContDiffOn 实数 n (fun x => arctan (f x)) s
  证明: contDiff_arctan.comp_contDiffOn h

Depends on / 依赖: comp_contDiffOn, contDiff_arctan, contDiff_arctan.comp_contDiffOn
-/
theorem ContDiffOn.arctan (h : ContDiffOn Real n f s) : ContDiffOn Real n (fun x => arctan (f x)) s :=
  contDiff_arctan.comp_contDiffOn h

end fderiv

end
