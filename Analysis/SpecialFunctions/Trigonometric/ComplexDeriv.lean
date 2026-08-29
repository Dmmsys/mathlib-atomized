/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Complex trigonometric functions

Basic facts and derivatives for the complex trigonometric functions.
-/

public section


noncomputable section

namespace Complex

open Set Filter

open scoped Real

/--
theorem `hasStrictDerivAt_tan` / 定理 `hasStrictDerivAt_tan`

English:
theorem hasStrictDerivAt_tan
  given: {x : Complex} (h : cos x != 0)
  statement: HasStrictDerivAt tan (1 / cos x ^ 2) x
  proof: by
  convert! (hasStrictDerivAt_sin x).div (hasStrictDerivAt_cos x) h using 1
  rw_mod_cast [← sin_sq_add_cos_sq x]
  ring

中文:
定理 hasStrictDerivAt_tan
  条件: {x : 复形} (h : cos x != 0)
  结论: HasStrictDerivAt tan (1 / cos x ^ 2) x
  证明: by
  convert! (hasStrictDerivAt_sin x).div (hasStrictDerivAt_cos x) h using 1
  rw_mod_cast [← sin_sq_add_cos_sq x]
  ring

Depends on / 依赖: convert, hasStrictDerivAt_cos, hasStrictDerivAt_sin, rw_mod_cast, sin_sq_add_cos_sq
-/
theorem hasStrictDerivAt_tan {x : Complex} (h : cos x != 0) : HasStrictDerivAt tan (1 / cos x ^ 2) x := by
  convert! (hasStrictDerivAt_sin x).div (hasStrictDerivAt_cos x) h using 1
  rw_mod_cast [← sin_sq_add_cos_sq x]
  ring

/--
theorem `hasDerivAt_tan` / 定理 `hasDerivAt_tan`

English:
theorem hasDerivAt_tan
  given: {x : Complex} (h : cos x != 0)
  statement: HasDerivAt tan (1 / cos x ^ 2) x
  proof: (hasStrictDerivAt_tan h).hasDerivAt

中文:
定理 hasDerivAt_tan
  条件: {x : 复形} (h : cos x != 0)
  结论: 在点处可导 tan (1 / cos x ^ 2) x
  证明: (hasStrictDerivAt_tan h).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_tan
-/
theorem hasDerivAt_tan {x : Complex} (h : cos x != 0) : HasDerivAt tan (1 / cos x ^ 2) x :=
  (hasStrictDerivAt_tan h).hasDerivAt

open scoped Topology

/--
theorem `tendsto_norm_tan_of_cos_eq_zero` / 定理 `tendsto_norm_tan_of_cos_eq_zero`

English:
theorem tendsto_norm_tan_of_cos_eq_zero
  given: {x : Complex} (hx : cos x = 0)
  proof: by
  simp only [tan_eq_sin_div_cos, norm_div]
  have A : sin x != 0 := fun h => by simpa [*, sq] using sin_sq_add_cos_sq x
  have B : Tendsto cos (𝓝[!=] x) (𝓝[!=] 0) :=
    hx ▸ (hasDerivAt_cos x).tendsto_nhdsNE (neg_ne_zero.2 A)
  exact continuous_sin.continuousWithinAt.norm.pos_mul_atTop (norm_pos_iff.2 A)
    (tendsto_norm_nhdsNE_zero.comp B).inv_tendsto_nhdsGT_zero

中文:
定理 tendsto_norm_tan_of_cos_eq_zero
  条件: {x : 复形} (hx : cos x = 0)
  证明: by
  simp only [tan_eq_sin_div_cos, norm_div]
  have A : sin x != 0 := fun h => by simpa [*, sq] using sin_sq_add_cos_sq x
  have B : Tendsto cos (𝓝[!=] x) (𝓝[!=] 0) :=
    hx ▸ (hasDerivAt_cos x).tendsto_nhdsNE (neg_ne_zero.2 A)
  exact continuous_sin.continuousWithinAt.norm.pos_mul_atTop (norm_pos_iff.2 A)
    (tendsto_norm_nhdsNE_zero.comp B).inv_tendsto_nhdsGT_zero

Depends on / 依赖: Tendsto, continuousWithinAt, continuous_sin, continuous_sin.continuousWithinAt.norm.pos_mul_atTop, hasDerivAt_cos, inv_tendsto_nhdsGT_zero, neg_ne_zero, norm_div, norm_pos_iff, pos_mul_atTop, sin_sq_add_cos_sq, tan_eq_sin_div_cos, tendsto_nhdsNE, tendsto_norm_nhdsNE_zero, tendsto_norm_nhdsNE_zero.comp
-/
theorem tendsto_norm_tan_of_cos_eq_zero {x : Complex} (hx : cos x = 0) :
    Tendsto (fun x => ‖tan x‖) (𝓝[!=] x) atTop := by
  simp only [tan_eq_sin_div_cos, norm_div]
  have A : sin x != 0 := fun h => by simpa [*, sq] using sin_sq_add_cos_sq x
  have B : Tendsto cos (𝓝[!=] x) (𝓝[!=] 0) :=
    hx ▸ (hasDerivAt_cos x).tendsto_nhdsNE (neg_ne_zero.2 A)
  exact continuous_sin.continuousWithinAt.norm.pos_mul_atTop (norm_pos_iff.2 A)
    (tendsto_norm_nhdsNE_zero.comp B).inv_tendsto_nhdsGT_zero

/--
theorem `tendsto_norm_tan_atTop` / 定理 `tendsto_norm_tan_atTop`

English:
theorem tendsto_norm_tan_atTop
  given: (k : Int)
  proof: tendsto_norm_tan_of_cos_eq_zero cos_eq_zero_iff.2 ⟨k, rfl⟩

@[simp]

中文:
定理 tendsto_norm_tan_atTop
  条件: (k : 整数)
  证明: tendsto_norm_tan_of_cos_eq_zero cos_eq_zero_iff.2 ⟨k, rfl⟩

@[simp]

Depends on / 依赖: cos_eq_zero_iff, tendsto_norm_tan_of_cos_eq_zero
-/
theorem tendsto_norm_tan_atTop (k : Int) :
    Tendsto (fun x => ‖tan x‖) (𝓝[!=] ((2 * k + 1) * π / 2 : Complex)) atTop :=
tendsto_norm_tan_of_cos_eq_zero cos_eq_zero_iff.2 ⟨k, rfl⟩

@[simp]
/--
theorem `continuousAt_tan` / 定理 `continuousAt_tan`

English:
theorem continuousAt_tan
  given: {x : Complex}
  statement: ContinuousAt tan x ↔ cos x != 0
  proof: by
  refine ⟨fun hc h₀ => ?_, fun h => (hasDerivAt_tan h).continuousAt⟩
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_norm_tan_of_cos_eq_zero h₀) _
    (hc.norm.tendsto.mono_left inf_le_left)

@[simp]

中文:
定理 continuousAt_tan
  条件: {x : 复形}
  结论: ContinuousAt tan x ↔ cos x != 0
  证明: by
  refine ⟨fun hc h₀ => ?_, fun h => (hasDerivAt_tan h).continuousAt⟩
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_norm_tan_of_cos_eq_zero h₀) _
    (hc.norm.tendsto.mono_left inf_le_left)

@[simp]

Depends on / 依赖: continuousAt, hasDerivAt_tan, hc.norm.tendsto.mono_left, inf_le_left, mono_left, not_tendsto_nhds_of_tendsto_atTop, tendsto, tendsto_norm_tan_of_cos_eq_zero
-/
theorem continuousAt_tan {x : Complex} : ContinuousAt tan x ↔ cos x != 0 := by
  refine ⟨fun hc h₀ => ?_, fun h => (hasDerivAt_tan h).continuousAt⟩
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_norm_tan_of_cos_eq_zero h₀) _
    (hc.norm.tendsto.mono_left inf_le_left)

@[simp]
/--
theorem `differentiableAt_tan` / 定理 `differentiableAt_tan`

English:
theorem differentiableAt_tan
  given: {x : Complex}
  statement: DifferentiableAt Complex tan x ↔ cos x != 0
  proof: ⟨fun h => continuousAt_tan.1 h.continuousAt, fun h => (hasDerivAt_tan h).differentiableAt⟩

@[simp]

中文:
定理 differentiableAt_tan
  条件: {x : 复形}
  结论: DifferentiableAt 复形 tan x ↔ cos x != 0
  证明: ⟨fun h => continuousAt_tan.1 h.continuousAt, fun h => (hasDerivAt_tan h).differentiableAt⟩

@[simp]

Depends on / 依赖: continuousAt, continuousAt_tan, differentiableAt, h.continuousAt, hasDerivAt_tan
-/
theorem differentiableAt_tan {x : Complex} : DifferentiableAt Complex tan x ↔ cos x != 0 :=
  ⟨fun h => continuousAt_tan.1 h.continuousAt, fun h => (hasDerivAt_tan h).differentiableAt⟩

@[simp]
/--
theorem `deriv_tan` / 定理 `deriv_tan`

English:
theorem deriv_tan
  given: (x : Complex)
  statement: deriv tan x = 1 / cos x ^ 2
  proof: if h : cos x = 0 then by
    have : ¬DifferentiableAt Complex tan x := mt differentiableAt_tan.1 (Classical.not_not.2 h)
    simp [deriv_zero_of_not_differentiableAt this, h, sq]
  else (hasDerivAt_tan h).deriv

@[simp]

中文:
定理 deriv_tan
  条件: (x : 复形)
  结论: deriv tan x = 1 / cos x ^ 2
  证明: if h : cos x = 0 then by
    have : ¬DifferentiableAt Complex tan x := mt differentiableAt_tan.1 (Classical.not_not.2 h)
    simp [deriv_zero_of_not_differentiableAt this, h, sq]
  else (hasDerivAt_tan h).deriv

@[simp]

Depends on / 依赖: Classical, Classical.not_not, DifferentiableAt, app.hom, app.hom_inv_id_assoc, cancel_epi, comp_id, deriv_zero_of_not_differentiableAt, differentiableAt_tan, hasDerivAt_tan, hom_inv_id, hom_inv_id_assoc, not_not, reassoc_of
-/
theorem deriv_tan (x : Complex) : deriv tan x = 1 / cos x ^ 2 :=
  if h : cos x = 0 then by
    have : ¬DifferentiableAt Complex tan x := mt differentiableAt_tan.1 (Classical.not_not.2 h)
    simp [deriv_zero_of_not_differentiableAt this, h, sq]
  else (hasDerivAt_tan h).deriv

@[simp]
/--
theorem `contDiffAt_tan` / 定理 `contDiffAt_tan`

English:
theorem contDiffAt_tan
  given: {x : Complex} {n : WithTop Nat∞}
  statement: ContDiffAt Complex n tan x ↔ cos x != 0
  proof: ⟨fun h => continuousAt_tan.1 h.continuousAt, contDiff_sin.contDiffAt.div contDiff_cos.contDiffAt⟩

中文:
定理 contDiffAt_tan
  条件: {x : 复形} {n : WithTop 自然数∞}
  结论: ContDiffAt 复形 n tan x ↔ cos x != 0
  证明: ⟨fun h => continuousAt_tan.1 h.continuousAt, contDiff_sin.contDiffAt.div contDiff_cos.contDiffAt⟩

Depends on / 依赖: contDiffAt, contDiff_cos, contDiff_cos.contDiffAt, contDiff_sin, contDiff_sin.contDiffAt.div, continuousAt, continuousAt_tan, h.continuousAt
-/
theorem contDiffAt_tan {x : Complex} {n : WithTop Nat∞} : ContDiffAt Complex n tan x ↔ cos x != 0 :=
  ⟨fun h => continuousAt_tan.1 h.continuousAt, contDiff_sin.contDiffAt.div contDiff_cos.contDiffAt⟩

end Complex
