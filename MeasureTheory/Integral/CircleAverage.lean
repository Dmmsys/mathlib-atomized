/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Integral.IntervalAverage

/-!
# Circle Averages

For a function `f` on the complex plane, this file introduces the definition
`Real.circleAverage f c R` as a shorthand for the average of `f` on the circle with center `c` and
radius `R`, equipped with the rotation-invariant measure of total volume one. Like
`IntervalAverage`, this notion exists as a convenience. It avoids notationally inconvenient
compositions of `f` with `circleMap` and avoids the need to manually eliminate `2 * π` every time
an average is computed.

Note: Like the interval average defined in `Mathlib/MeasureTheory/Integral/IntervalAverage.lean`,
the `circleAverage` defined here is a purely measure-theoretic average. It should not be confused
with `circleIntegral`, which is the path integral over the circle path. The relevant integrability
property `circleAverage` is `CircleIntegrable`, as defined in
`Mathlib/MeasureTheory/Integral/CircleIntegral.lean`.

Implementation Note: Like `circleMap`, `circleAverage`s are defined for negative radii. The theorem
`circleAverage_congr_negRadius` shows that the average is independent of the radius' sign.
-/

@[expose] public section

open Complex Filter Metric Real Set Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
  {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E] [SMulCommClass Real 𝕜 E]
  {f f₁ f₂ : Complex -> E} {c : Complex} {R : Real} {a : 𝕜}

namespace Real

/-!
### Definition
-/

variable (f c R) in
/--
Definition of `circleAverage` / `circleAverage` 的定义

English:
definition circleAverage
  signature: : E
  body: (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ)

中文:
定义 circleAverage
  签名: : E
  定义体: (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ)

Depends on / 依赖: circleMap
-/
noncomputable def circleAverage : E :=
  (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ)

/--
lemma `circleAverage_def` / 引理 `circleAverage_def`

English:
lemma circleAverage_def
  proof: rfl

中文:
引理 circleAverage_def
  证明: rfl
-/
lemma circleAverage_def :
    circleAverage f c R = (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ) := rfl

/--
theorem `circleAverage.integral_undef` / 定理 `circleAverage.integral_undef`

English:
theorem circleAverage.integral_undef
  given: (hf : ¬CircleIntegrable f c R)
  proof: by
  simp_all [circleAverage, CircleIntegrable, intervalIntegral.integral_undef]

中文:
定理 circleAverage.integral_undef
  条件: (hf : ¬Circle整数egrable f c R)
  证明: by
  simp_all [circleAverage, CircleIntegrable, intervalIntegral.integral_undef]

Depends on / 依赖: CircleIntegrable, circleAverage, integral_undef, intervalIntegral, intervalIntegral.integral_undef
-/
theorem circleAverage.integral_undef (hf : ¬CircleIntegrable f c R) :
    circleAverage f c R = 0 := by
  simp_all [circleAverage, CircleIntegrable, intervalIntegral.integral_undef]

/--
lemma `circleAverage_eq_intervalAverage` / 引理 `circleAverage_eq_intervalAverage`

English:
lemma circleAverage_eq_intervalAverage
  proof: by
  simp [circleAverage, interval_average_eq]

中文:
引理 circleAverage_eq_intervalAverage
  证明: by
  simp [circleAverage, interval_average_eq]

Depends on / 依赖: circleAverage, interval_average_eq
-/
lemma circleAverage_eq_intervalAverage :
    circleAverage f c R = ⨍ θ in 0..2 * π, f (circleMap c R θ) := by
  simp [circleAverage, interval_average_eq]

/--
lemma `circleAverage_zero` / 引理 `circleAverage_zero`

English:
lemma circleAverage_zero
  given: [CompleteSpace E]
  proof: by
  rw [circleAverage]
  simp only [circleMap_zero_radius, Function.const_apply,
    intervalIntegral.integral_const, sub_zero,
    ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero pi_ne_zero),
    one_smul]

中文:
引理 circleAverage_zero
  条件: [CompleteSpace E]
  证明: by
  rw [circleAverage]
  simp only [circleMap_zero_radius, Function.const_apply,
    intervalIntegral.integral_const, sub_zero,
    ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero pi_ne_zero),
    one_smul]
-/
@[simp] lemma circleAverage_zero [CompleteSpace E] :
    circleAverage f c 0 = f c := by
  rw [circleAverage]
  simp only [circleMap_zero_radius, Function.const_apply,
    intervalIntegral.integral_const, sub_zero,
    ← smul_assoc, smul_eq_mul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero pi_ne_zero),
    one_smul]

/--
lemma `circleAverage_map_add_const` / 引理 `circleAverage_map_add_const`

English:
lemma circleAverage_map_add_const
  proof: by
  unfold circleAverage circleMap
  congr
  ext θ
  simp only [zero_add]
  congr 1
  ring

中文:
引理 circleAverage_map_add_const
  证明: by
  unfold circleAverage circleMap
  congr
  ext θ
  simp only [zero_add]
  congr 1
  ring

Depends on / 依赖: circleAverage, circleMap, zero_add
-/
lemma circleAverage_map_add_const :
    circleAverage (fun z => f (z + c)) 0 R = circleAverage f c R := by
  unfold circleAverage circleMap
  congr
  ext θ
  simp only [zero_add]
  congr 1
  ring

/--
theorem `circleAverage_eq_circleIntegral` / 定理 `circleAverage_eq_circleIntegral`

English:
theorem circleAverage_eq_circleIntegral
  statement: {F : Type*} [NormedAddCommGroup F] [NormedSpace Complex F]
  proof: by
  calc circleAverage f c R
  _ = (↑(2 * π) : Complex)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ) := by
    simp [circleAverage, ← coe_smul]
  _ = (2 * π * I)⁻¹ • ∫ θ in 0..2 * π, I • f (circleMap c R θ) := by
    rw [intervalIntegral.integral_smul]; rw [mul_inv_rev]; rw [smul_smul]
    match_scalar

中文:
定理 circleAverage_eq_circleIntegral
  结论: {F : 类型} [NormedAddCommGroup F] [NormedSpace Complex F]
  证明: by
  calc circleAverage f c R
  _ = (↑(2 * π) : Complex)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ) := by
    simp [circleAverage, ← coe_smul]
  _ = (2 * π * I)⁻¹ • ∫ θ in 0..2 * π, I • f (circleMap c R θ) := by
    rw [intervalIntegral.integral_smul]; rw [mul_inv_rev]; rw [smul_smul]
    match_scalar

Depends on / 依赖: circleAverage, circleIntegral, circleMap, circleMap_ne_center, circleMap_sub_center, coe_smul, deriv_circleMap, integral_smul, intervalIntegral, intervalIntegral.integral_smul, match_scalars, mul_inv_rev, smul_smul
-/
theorem circleAverage_eq_circleIntegral {F : Type*} [NormedAddCommGroup F] [NormedSpace Complex F]
    {f : Complex -> F} (h : R != 0) :
    circleAverage f c R = (2 * π * I)⁻¹ • (∮ z in C(c, R), (z - c)⁻¹ • f z) := by
  calc circleAverage f c R
  _ = (↑(2 * π) : Complex)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R θ) := by
    simp [circleAverage, ← coe_smul]
  _ = (2 * π * I)⁻¹ • ∫ θ in 0..2 * π, I • f (circleMap c R θ) := by
    rw [intervalIntegral.integral_smul]; rw [mul_inv_rev]; rw [smul_smul]
    match_scalars
    field
  _ = (2 * π * I)⁻¹ • (∮ z in C(c, R), (z - c)⁻¹ • f z) := by
    unfold circleIntegral
    congr with θ
    simp [deriv_circleMap, circleMap_sub_center, smul_smul]
    field_simp [circleMap_ne_center h]

/-!
## Congruence Lemmata
-/

/--
lemma `circleAverage_eq_integral_add` / 引理 `circleAverage_eq_integral_add`

English:
lemma circleAverage_eq_integral_add
  given: (η : Real)
  proof: by
  rw [intervalIntegral.integral_comp_add_right (fun θ => f (circleMap c R θ))]
  have t₀ : (fun θ => f (circleMap c R θ)).Periodic (2 * π) :=
    fun x => by simp [periodic_circleMap c R x]
  have := t₀.intervalIntegral_add_eq 0 η
  rw [zero_add]; rw [add_comm] at this
  rw [zero_add]
  simp only

中文:
引理 circleAverage_eq_integral_add
  条件: (η : 实数)
  证明: by
  rw [intervalIntegral.integral_comp_add_right (fun θ => f (circleMap c R θ))]
  have t₀ : (fun θ => f (circleMap c R θ)).Periodic (2 * π) :=
    fun x => by simp [periodic_circleMap c R x]
  have := t₀.intervalIntegral_add_eq 0 η
  rw [zero_add]; rw [add_comm] at this
  rw [zero_add]
  simp only

Depends on / 依赖: Periodic, add_comm, circleAverage, circleMap, integral_comp_add_right, intervalIntegral, intervalIntegral.integral_comp_add_right, intervalIntegral_add_eq, mul_inv_rev, periodic_circleMap, zero_add
-/
lemma circleAverage_eq_integral_add (η : Real) :
    circleAverage f c R = (2 * π)⁻¹ • ∫ θ in 0..2 * π, f (circleMap c R (θ + η)) := by
  rw [intervalIntegral.integral_comp_add_right (fun θ => f (circleMap c R θ))]
  have t₀ : (fun θ => f (circleMap c R θ)).Periodic (2 * π) :=
    fun x => by simp [periodic_circleMap c R x]
  have := t₀.intervalIntegral_add_eq 0 η
  rw [zero_add]; rw [add_comm] at this
  rw [zero_add]
  simp only [circleAverage, mul_inv_rev]
  congr

/--
theorem `circleAverage_neg_radius` / 定理 `circleAverage_neg_radius`

English:
theorem circleAverage_neg_radius
  proof: by
  unfold circleAverage
  simp_rw [circleMap_neg_radius, ← circleAverage_def, circleAverage_eq_integral_add π]

中文:
定理 circleAverage_neg_radius
  证明: by
  unfold circleAverage
  simp_rw [circleMap_neg_radius, ← circleAverage_def, circleAverage_eq_integral_add π]
-/
@[simp] theorem circleAverage_neg_radius :
    circleAverage f c (-R) = circleAverage f c R := by
  unfold circleAverage
  simp_rw [circleMap_neg_radius, ← circleAverage_def, circleAverage_eq_integral_add π]

/--
theorem `circleAverage_abs_radius` / 定理 `circleAverage_abs_radius`

English:
theorem circleAverage_abs_radius
  proof: by
  by_cases! hR : 0 <= R
  · rw [abs_of_nonneg hR]
  · rw [abs_of_neg hR, circleAverage_neg_radius]

中文:
定理 circleAverage_abs_radius
  证明: by
  by_cases! hR : 0 <= R
  · rw [abs_of_nonneg hR]
  · rw [abs_of_neg hR, circleAverage_neg_radius]
-/
@[simp] theorem circleAverage_abs_radius :
    circleAverage f c |R| = circleAverage f c R := by
  by_cases! hR : 0 <= R
  · rw [abs_of_nonneg hR]
  · rw [abs_of_neg hR, circleAverage_neg_radius]

/--
theorem `circleAverage_congr_codiscreteWithin` / 定理 `circleAverage_congr_codiscreteWithin`

English:
theorem circleAverage_congr_codiscreteWithin
  proof: by
  unfold circleAverage
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  apply codiscreteWithin_mono (by tauto) (circleMap_preimage_codiscrete hR hf)

中文:
定理 circleAverage_congr_codiscreteWithin
  证明: by
  unfold circleAverage
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  apply codiscreteWithin_mono (by tauto) (circleMap_preimage_codiscrete hR hf)

Depends on / 依赖: ae_restrict_le_codiscreteWithin, circleAverage, circleMap_preimage_codiscrete, codiscreteWithin_mono, integral_congr_ae_restrict, intervalIntegral, intervalIntegral.integral_congr_ae_restrict, measurableSet_uIoc
-/
theorem circleAverage_congr_codiscreteWithin
    (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hR : R != 0) :
    circleAverage f₁ c R = circleAverage f₂ c R := by
  unfold circleAverage
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  apply codiscreteWithin_mono (by tauto) (circleMap_preimage_codiscrete hR hf)

/--
theorem `circleAverage_congr_sphere` / 定理 `circleAverage_congr_sphere`

English:
theorem circleAverage_congr_sphere
  given: {f₁ f₂ : Complex -> E} (hf : Set.EqOn f₁ f₂ (sphere c |R|))
  proof: by
  unfold circleAverage
  congr 1
  exact intervalIntegral.integral_congr (fun x => by simp [hf (circleMap_mem_sphere' c R x)])

中文:
定理 circleAverage_congr_sphere
  条件: {f₁ f₂ : Complex -> E} (hf : Set.EqOn f₁ f₂ (sphere c |R|))
  证明: by
  unfold circleAverage
  congr 1
  exact intervalIntegral.integral_congr (fun x => by simp [hf (circleMap_mem_sphere' c R x)])

Depends on / 依赖: circleAverage, circleMap_mem_sphere, integral_congr, intervalIntegral, intervalIntegral.integral_congr
-/
theorem circleAverage_congr_sphere {f₁ f₂ : Complex -> E} (hf : Set.EqOn f₁ f₂ (sphere c |R|)) :
    circleAverage f₁ c R = circleAverage f₂ c R := by
  unfold circleAverage
  congr 1
  exact intervalIntegral.integral_congr (fun x => by simp [hf (circleMap_mem_sphere' c R x)])

/--
theorem `circleAverage_eq_circleAverage_zero_one` / 定理 `circleAverage_eq_circleAverage_zero_one`

English:
theorem circleAverage_eq_circleAverage_zero_one
  proof: by
  unfold circleAverage circleMap
  congr with θ
  ring_nf
  simp

中文:
定理 circleAverage_eq_circleAverage_zero_one
  证明: by
  unfold circleAverage circleMap
  congr with θ
  ring_nf
  simp

Depends on / 依赖: circleAverage, circleMap, ring_nf
-/
theorem circleAverage_eq_circleAverage_zero_one :
    circleAverage f c R = (circleAverage (fun z => f (R * z + c)) 0 1) := by
  unfold circleAverage circleMap
  congr with θ
  ring_nf
  simp

/--
The circle average of a function `f` on the unit sphere equals the circle average of the function
`z ↦ f z⁻¹`.
-/
@[simp]
/--
theorem `circleAverage_zero_one_congr_inv` / 定理 `circleAverage_zero_one_congr_inv`

English:
theorem circleAverage_zero_one_congr_inv
  given: {f : Complex -> E}
  proof: by
  unfold circleAverage
  congr 1
  calc ∫ θ in 0..2 * π, f (circleMap 0 1 θ)⁻¹
  _ = ∫ θ in 0..2 * π, f (circleMap 0 1 (-θ)) := by
    simp [circleMap_zero_inv]
  _ = ∫ θ in 0..2 * π, f (circleMap 0 1 θ) := by
    rw [intervalIntegral.integral_comp_neg (fun w => f (circleMap 0 1 w))]
    have t₀ 

中文:
定理 circleAverage_zero_one_congr_inv
  条件: {f : Complex -> E}
  证明: by
  unfold circleAverage
  congr 1
  calc ∫ θ in 0..2 * π, f (circleMap 0 1 θ)⁻¹
  _ = ∫ θ in 0..2 * π, f (circleMap 0 1 (-θ)) := by
    simp [circleMap_zero_inv]
  _ = ∫ θ in 0..2 * π, f (circleMap 0 1 θ) := by
    rw [intervalIntegral.integral_comp_neg (fun w => f (circleMap 0 1 w))]
    have t₀ 

Depends on / 依赖: Function, Function.Periodic, Periodic, circleAverage, circleMap, circleMap_zero_inv, integral_comp_neg, intervalIntegral, intervalIntegral.integral_comp_neg, intervalIntegral_add_eq, periodic_circleMap
-/
theorem circleAverage_zero_one_congr_inv {f : Complex -> E} :
    circleAverage (f ·⁻¹) 0 1 = circleAverage f 0 1 := by
  unfold circleAverage
  congr 1
  calc ∫ θ in 0..2 * π, f (circleMap 0 1 θ)⁻¹
  _ = ∫ θ in 0..2 * π, f (circleMap 0 1 (-θ)) := by
    simp [circleMap_zero_inv]
  _ = ∫ θ in 0..2 * π, f (circleMap 0 1 θ) := by
    rw [intervalIntegral.integral_comp_neg (fun w => f (circleMap 0 1 w))]
    have t₀ : Function.Periodic (fun w => f (circleMap 0 1 w)) (2 * π) :=
      fun x => by simp [periodic_circleMap 0 1 x]
    simpa using (t₀.intervalIntegral_add_eq (-(2 * π)) 0)

/-!
## Continuity
-/

/--
lemma `circleMap.continuous` / 引理 `circleMap.continuous`

English:
lemma circleMap.continuous
  given: {c : Complex}
  proof: by
  fun_prop [circleMap]

中文:
引理 circleMap.continuous
  条件: {c : Complex}
  证明: by
  fun_prop [circleMap]
-/
@[fun_prop] lemma circleMap.continuous {c : Complex} :
    Continuous (fun (x : Real × Real) => circleMap c x.1 x.2) := by
  fun_prop [circleMap]

/--
theorem `ContinuousOn.circleAverage` / 定理 `ContinuousOn.circleAverage`

English:
theorem ContinuousOn.circleAverage
  statement: {f : Complex -> E} {s : Set Real} {c : Complex}
  proof: by
  rw [continuousOn_iff_continuous_domRestrict] at *
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ _ _).const_smul
  have (x : s × Real) : circleMap c x.1 x.2 in {z | ‖z - c‖ in s} := by
    simp [abs_of_nonneg (hs x.1 (Subtype.coe_prop x.1))]
  apply hf.comp (f

中文:
定理 ContinuousOn.circleAverage
  结论: {f : Complex -> E} {s : Set 实数} {c : Complex}
  证明: by
  rw [continuousOn_iff_continuous_domRestrict] at *
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ _ _).const_smul
  have (x : s × Real) : circleMap c x.1 x.2 in {z | ‖z - c‖ in s} := by
    simp [abs_of_nonneg (hs x.1 (Subtype.coe_prop x.1))]
  apply hf.comp (f

Depends on / 依赖: Subtype, Subtype.coe_prop, abs_of_nonneg, circleMap, coe_prop, const_smul, continuousOn_iff_continuous_domRestrict, continuous_parametric_intervalIntegral_of_continuous, fun_prop, hf.comp, intervalIntegral, intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
-/
theorem ContinuousOn.circleAverage {f : Complex -> E} {s : Set Real} {c : Complex}
    (hf : ContinuousOn f {z : Complex | ‖z - c‖ in s})
    (hs : forall r in s, 0 <= r) :
    ContinuousOn (circleAverage f c) s := by
  rw [continuousOn_iff_continuous_domRestrict] at *
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ _ _).const_smul
  have (x : s × Real) : circleMap c x.1 x.2 in {z | ‖z - c‖ in s} := by
    simp [abs_of_nonneg (hs x.1 (Subtype.coe_prop x.1))]
  apply hf.comp (f := (fun x => ⟨circleMap c x.1 x.2, this x⟩))
  fun_prop

/--
theorem `Continuous.circleAverage` / 定理 `Continuous.circleAverage`

English:
theorem Continuous.circleAverage
  given: {f : Complex -> E} (hf : Continuous f)
  proof: by
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ _ _).const_smul
  fun_prop

中文:
定理 Continuous.circleAverage
  条件: {f : Complex -> E} (hf : Continuous f)
  证明: by
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ _ _).const_smul
  fun_prop

Depends on / 依赖: IsAtomic
-/
@[fun_prop] theorem Continuous.circleAverage {f : Complex -> E} (hf : Continuous f) :
    Continuous (Real.circleAverage f c) := by
  apply (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ _ _).const_smul
  fun_prop

/--
lemma `ContinuousOn.eq_of_eqOn_Ioo` / 引理 `ContinuousOn.eq_of_eqOn_Ioo`

English:
lemma ContinuousOn.eq_of_eqOn_Ioo
  statement: {f : Real -> Real} {c r R : Real}
  proof: by
  have : Filter.Tendsto f (𝓝[Iio R] R) (𝓝 (f R)) := by
    apply (h₁f R (right_mem_Ioc.mpr hR)).mono_left
    rw [nhdsWithin_le_iff]; rw [mem_nhdsLT_iff_exists_Ioo_subset]
    use r
    simp_all [Ioo_subset_Ioc_self]
  apply tendsto_nhds_unique this (tendsto_const_nhds.congr' _)
  apply Filter.ev

中文:
引理 ContinuousOn.eq_of_eqOn_Ioo
  结论: {f : 实数 -> 实数} {c r R : 实数}
  证明: by
  have : Filter.Tendsto f (𝓝[Iio R] R) (𝓝 (f R)) := by
    apply (h₁f R (right_mem_Ioc.mpr hR)).mono_left
    rw [nhdsWithin_le_iff]; rw [mem_nhdsLT_iff_exists_Ioo_subset]
    use r
    simp_all [Ioo_subset_Ioc_self]
  apply tendsto_nhds_unique this (tendsto_const_nhds.congr' _)
  apply Filter.ev

Depends on / 依赖: Filter, Filter.Tendsto, Filter.eventuallyEq_of_mem, Ioo_mem_nhdsLT, Ioo_subset_Ioc_self, Tendsto, eventuallyEq_of_mem, mem_nhdsLT_iff_exists_Ioo_subset, mono_left, nhdsWithin_le_iff, right_mem_Ioc, right_mem_Ioc.mpr, tendsto_const_nhds, tendsto_const_nhds.congr, tendsto_nhds_unique
-/
lemma ContinuousOn.eq_of_eqOn_Ioo {f : Real -> Real} {c r R : Real}
    (h₁f : ContinuousOn f (Ioc r R)) (hR : r < R)
    (h₂f : EqOn f (fun _ => c) (Ioo r R)) :
    f R = c := by
  have : Filter.Tendsto f (𝓝[Iio R] R) (𝓝 (f R)) := by
    apply (h₁f R (right_mem_Ioc.mpr hR)).mono_left
    rw [nhdsWithin_le_iff]; rw [mem_nhdsLT_iff_exists_Ioo_subset]
    use r
    simp_all [Ioo_subset_Ioc_self]
  apply tendsto_nhds_unique this (tendsto_const_nhds.congr' _)
  apply Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT hR) (fun _ hx => (h₂f hx).symm)

/-!
## Constant Functions
-/

/--
theorem `circleAverage_const` / 定理 `circleAverage_const`

English:
theorem circleAverage_const
  given: [CompleteSpace E] (a : E) (c : Complex) (R : Real)
  proof: by
  simp only [circleAverage, intervalIntegral.integral_const, ← smul_assoc, sub_zero, smul_eq_mul]
  ring_nf
  simp

中文:
定理 circleAverage_const
  条件: [CompleteSpace E] (a : E) (c : Complex) (R : 实数)
  证明: by
  simp only [circleAverage, intervalIntegral.integral_const, ← smul_assoc, sub_zero, smul_eq_mul]
  ring_nf
  simp

Depends on / 依赖: circleAverage, integral_const, intervalIntegral, intervalIntegral.integral_const, ring_nf, smul_assoc, smul_eq_mul, sub_zero
-/
theorem circleAverage_const [CompleteSpace E] (a : E) (c : Complex) (R : Real) :
    circleAverage (fun _ => a) c R = a := by
  simp only [circleAverage, intervalIntegral.integral_const, ← smul_assoc, sub_zero, smul_eq_mul]
  ring_nf
  simp

/--
theorem `circleAverage_const_on_circle` / 定理 `circleAverage_const_on_circle`

English:
theorem circleAverage_const_on_circle
  statement: [CompleteSpace E] {a : E}
  proof: by
  rw [circleAverage]
  conv =>
    left; arg 2; arg 1
    intro θ
    rw [hf (circleMap c R θ) (circleMap_mem_sphere' c R θ)]
  apply circleAverage_const a c R

中文:
定理 circleAverage_const_on_circle
  结论: [CompleteSpace E] {a : E}
  证明: by
  rw [circleAverage]
  conv =>
    left; arg 2; arg 1
    intro θ
    rw [hf (circleMap c R θ) (circleMap_mem_sphere' c R θ)]
  apply circleAverage_const a c R

Depends on / 依赖: circleAverage, circleAverage_const, circleMap, circleMap_mem_sphere
-/
theorem circleAverage_const_on_circle [CompleteSpace E] {a : E}
    (hf : forall x in Metric.sphere c |R|, f x = a) :
    circleAverage f c R = a := by
  rw [circleAverage]
  conv =>
    left; arg 2; arg 1
    intro θ
    rw [hf (circleMap c R θ) (circleMap_mem_sphere' c R θ)]
  apply circleAverage_const a c R

/-!
## Inequalities
-/

/--
Circle averages respect the `≤` relation.
-/
@[gcongr]
/--
theorem `circleAverage_mono` / 定理 `circleAverage_mono`

English:
theorem circleAverage_mono
  statement: {c : Complex} {R : Real} {f₁ f₂ : Complex -> Real} (hf₁ : CircleIntegrable f₁ c R)
  proof: by
  apply (mul_le_mul_iff_of_pos_left (by simp [pi_pos])).2
  apply intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt two_pi_pos) hf₁ hf₂
  exact fun x _ => by simp [h (circleMap c R x)]

中文:
定理 circleAverage_mono
  结论: {c : Complex} {R : 实数} {f₁ f₂ : Complex -> 实数} (hf₁ : Circle整数egrable f₁ c R)
  证明: by
  apply (mul_le_mul_iff_of_pos_left (by simp [pi_pos])).2
  apply intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt two_pi_pos) hf₁ hf₂
  exact fun x _ => by simp [h (circleMap c R x)]

Depends on / 依赖: circleMap, integral_mono_on_of_le_Ioo, intervalIntegral, intervalIntegral.integral_mono_on_of_le_Ioo, le_of_lt, mul_le_mul_iff_of_pos_left, pi_pos, two_pi_pos
-/
theorem circleAverage_mono {c : Complex} {R : Real} {f₁ f₂ : Complex -> Real} (hf₁ : CircleIntegrable f₁ c R)
    (hf₂ : CircleIntegrable f₂ c R) (h : forall x in Metric.sphere c |R|, f₁ x <= f₂ x) :
    circleAverage f₁ c R <= circleAverage f₂ c R := by
  apply (mul_le_mul_iff_of_pos_left (by simp [pi_pos])).2
  apply intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt two_pi_pos) hf₁ hf₂
  exact fun x _ => by simp [h (circleMap c R x)]

/--
theorem `circleAverage_mono_on_of_le_circle` / 定理 `circleAverage_mono_on_of_le_circle`

English:
theorem circleAverage_mono_on_of_le_circle
  statement: {f : Complex -> Real} {a : Real} (hf : CircleIntegrable f c R)
  proof: by
  rw [← circleAverage_const a c |R|]; rw [circleAverage]; rw [circleAverage]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_le_mul_iff_of_pos_left (inv_pos.2 two_pi_pos)]
  exact intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt two_pi_pos) hf
    intervalIntegrable_const (fun θ _ => h₂f (circl

中文:
定理 circleAverage_mono_on_of_le_circle
  结论: {f : Complex -> 实数} {a : 实数} (hf : Circle整数egrable f c R)
  证明: by
  rw [← circleAverage_const a c |R|]; rw [circleAverage]; rw [circleAverage]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_le_mul_iff_of_pos_left (inv_pos.2 two_pi_pos)]
  exact intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt two_pi_pos) hf
    intervalIntegrable_const (fun θ _ => h₂f (circl

Depends on / 依赖: circleAverage, circleAverage_const, circleMap, circleMap_mem_sphere, integral_mono_on_of_le_Ioo, intervalIntegrable_const, intervalIntegral, intervalIntegral.integral_mono_on_of_le_Ioo, inv_pos, le_of_lt, mul_le_mul_iff_of_pos_left, smul_eq_mul, two_pi_pos
-/
theorem circleAverage_mono_on_of_le_circle {f : Complex -> Real} {a : Real} (hf : CircleIntegrable f c R)
    (h₂f : forall x in Metric.sphere c |R|, f x <= a) :
    circleAverage f c R <= a := by
  rw [← circleAverage_const a c |R|]; rw [circleAverage]; rw [circleAverage]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_le_mul_iff_of_pos_left (inv_pos.2 two_pi_pos)]
  exact intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt two_pi_pos) hf
    intervalIntegrable_const (fun θ _ => h₂f (circleMap c R θ) (circleMap_mem_sphere' c R θ))

/--
theorem `abs_circleAverage_le_circleAverage_abs` / 定理 `abs_circleAverage_le_circleAverage_abs`

English:
theorem abs_circleAverage_le_circleAverage_abs
  given: {f : Complex -> Real}
  proof: by
  rw [circleAverage]; rw [circleAverage]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [abs_mul]; rw [abs_of_pos (inv_pos.2 two_pi_pos)]; rw [mul_le_mul_iff_of_pos_left (inv_pos.2 two_pi_pos)]
  exact intervalIntegral.abs_integral_le_integral_abs (le_of_lt two_pi_pos)

中文:
定理 abs_circleAverage_le_circleAverage_abs
  条件: {f : Complex -> 实数}
  证明: by
  rw [circleAverage]; rw [circleAverage]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [abs_mul]; rw [abs_of_pos (inv_pos.2 two_pi_pos)]; rw [mul_le_mul_iff_of_pos_left (inv_pos.2 two_pi_pos)]
  exact intervalIntegral.abs_integral_le_integral_abs (le_of_lt two_pi_pos)

Depends on / 依赖: IsCoatomic, abs_integral_le_integral_abs, abs_mul, abs_of_pos, circleAverage, intervalIntegral, intervalIntegral.abs_integral_le_integral_abs, inv_pos, le_of_lt, mul_le_mul_iff_of_pos_left, smul_eq_mul, two_pi_pos
-/
theorem abs_circleAverage_le_circleAverage_abs {f : Complex -> Real} :
    |circleAverage f c R| <= circleAverage |f| c R := by
  rw [circleAverage]; rw [circleAverage]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [abs_mul]; rw [abs_of_pos (inv_pos.2 two_pi_pos)]; rw [mul_le_mul_iff_of_pos_left (inv_pos.2 two_pi_pos)]
  exact intervalIntegral.abs_integral_le_integral_abs (le_of_lt two_pi_pos)

/--
theorem `circleAverage_nonneg_of_nonneg` / 定理 `circleAverage_nonneg_of_nonneg`

English:
theorem circleAverage_nonneg_of_nonneg
  statement: {c : Complex} {R : Real} {f : Complex -> Real}
  proof: by
  by_cases hf : CircleIntegrable f c R
  · rw [← circleAverage_const 0 c |R|, circleAverage, circleAverage, smul_eq_mul, smul_eq_mul,
      mul_le_mul_iff_of_pos_left (inv_pos.2 two_pi_pos)]
    apply intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt two_pi_pos)
      intervalIntegrable_const

中文:
定理 circleAverage_nonneg_of_nonneg
  结论: {c : Complex} {R : 实数} {f : Complex -> 实数}
  证明: by
  by_cases hf : CircleIntegrable f c R
  · rw [← circleAverage_const 0 c |R|, circleAverage, circleAverage, smul_eq_mul, smul_eq_mul,
      mul_le_mul_iff_of_pos_left (inv_pos.2 two_pi_pos)]
    apply intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt two_pi_pos)
      intervalIntegrable_const

Depends on / 依赖: CircleIntegrable, circleAverage, circleAverage.integral_undef, circleAverage_const, circleMap, circleMap_mem_sphere, integral_mono_on_of_le_Ioo, integral_undef, intervalIntegrable_const, intervalIntegral, intervalIntegral.integral_mono_on_of_le_Ioo, inv_pos, le_of_lt, mul_le_mul_iff_of_pos_left, smul_eq_mul, two_pi_pos
-/
theorem circleAverage_nonneg_of_nonneg {c : Complex} {R : Real} {f : Complex -> Real}
    (h₂f : forall x in Metric.sphere c |R|, 0 <= f x) :
    0 <= circleAverage f c R := by
  by_cases hf : CircleIntegrable f c R
  · rw [← circleAverage_const 0 c |R|, circleAverage, circleAverage, smul_eq_mul, smul_eq_mul,
      mul_le_mul_iff_of_pos_left (inv_pos.2 two_pi_pos)]
    apply intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt two_pi_pos)
      intervalIntegrable_const hf (fun θ _ => h₂f (circleMap c R θ) (circleMap_mem_sphere' c R θ))
  · rw [circleAverage.integral_undef hf]

/-!
## Commutativity with Linear Maps
-/

/--
theorem `_root_.ContinuousLinearMap.circleAverage_comp_comm` / 定理 `_root_.ContinuousLinearMap.circleAverage_comp_comm`

English:
theorem _root_.ContinuousLinearMap.circleAverage_comp_comm
  statement: [CompleteSpace E] (L : E ->L[Real] F)
  proof: by
  unfold circleAverage
  rw [map_smul]
  congr
  exact L.intervalIntegral_comp_comm hf

中文:
定理 _root_.ContinuousLinearMap.circleAverage_comp_comm
  结论: [CompleteSpace E] (L : E ->L[实数] F)
  证明: by
  unfold circleAverage
  rw [map_smul]
  congr
  exact L.intervalIntegral_comp_comm hf

Depends on / 依赖: L.intervalIntegral_comp_comm, circleAverage, intervalIntegral_comp_comm, map_smul
-/
theorem _root_.ContinuousLinearMap.circleAverage_comp_comm [CompleteSpace E] (L : E ->L[Real] F)
    {f : Complex -> E} (hf : CircleIntegrable f c R) :
    circleAverage (L ∘ f) c R = L (circleAverage f c R) := by
  unfold circleAverage
  rw [map_smul]
  congr
  exact L.intervalIntegral_comp_comm hf

/-!
## Behaviour with Respect to Arithmetic Operations
-/

/--
theorem `circleAverage_smul` / 定理 `circleAverage_smul`

English:
theorem circleAverage_smul
  proof: by
  unfold circleAverage
  have := SMulCommClass.symm Real 𝕜 E
  rw [smul_comm]
  simp [intervalIntegral.integral_smul]

中文:
定理 circleAverage_smul
  证明: by
  unfold circleAverage
  have := SMulCommClass.symm Real 𝕜 E
  rw [smul_comm]
  simp [intervalIntegral.integral_smul]

Depends on / 依赖: SMulCommClass, SMulCommClass.symm, circleAverage, integral_smul, intervalIntegral, intervalIntegral.integral_smul, smul_comm
-/
theorem circleAverage_smul :
    circleAverage (a • f) c R = a • circleAverage f c R := by
  unfold circleAverage
  have := SMulCommClass.symm Real 𝕜 E
  rw [smul_comm]
  simp [intervalIntegral.integral_smul]

/--
theorem `circleAverage_fun_smul` / 定理 `circleAverage_fun_smul`

English:
theorem circleAverage_fun_smul
  proof: circleAverage_smul

中文:
定理 circleAverage_fun_smul
  证明: circleAverage_smul

Depends on / 依赖: circleAverage_smul
-/
theorem circleAverage_fun_smul :
    circleAverage (fun z => a • f z) c R = a • circleAverage f c R :=
  circleAverage_smul

/--
theorem `circleAverage_add` / 定理 `circleAverage_add`

English:
theorem circleAverage_add
  given: (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R)
  proof: by
  rw [circleAverage]; rw [circleAverage]; rw [circleAverage]; rw [← smul_add]
  congr
  apply intervalIntegral.integral_add hf₁ hf₂

中文:
定理 circleAverage_add
  条件: (hf₁ : Circle整数egrable f₁ c R) (hf₂ : Circle整数egrable f₂ c R)
  证明: by
  rw [circleAverage]; rw [circleAverage]; rw [circleAverage]; rw [← smul_add]
  congr
  apply intervalIntegral.integral_add hf₁ hf₂

Depends on / 依赖: CompleteLattice, CompleteLattice.isAtomistic_iff, IsAtom, circleAverage, iInf_iSup_eq, iInf_le, iSup_bool_eq, iSup_le_iff, inf_le_rig, inhabit, integral_add, intervalIntegral, intervalIntegral.integral_add, isAtomistic_iff, le_antisymm, le_iSup, le_sSup, le_trans, lt_of_lt_of_le, sSup_le
-/
theorem circleAverage_add (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R) :
    circleAverage (f₁ + f₂) c R = circleAverage f₁ c R + circleAverage f₂ c R := by
  rw [circleAverage]; rw [circleAverage]; rw [circleAverage]; rw [← smul_add]
  congr
  apply intervalIntegral.integral_add hf₁ hf₂

/--
theorem `circleAverage_fun_add` / 定理 `circleAverage_fun_add`

English:
theorem circleAverage_fun_add
  statement: {c : Complex} {R : Real} {f₁ f₂ : Complex -> E} (hf₁ : CircleIntegrable f₁ c R)
  proof: circleAverage_add hf₁ hf₂

中文:
定理 circleAverage_fun_add
  结论: {c : Complex} {R : 实数} {f₁ f₂ : Complex -> E} (hf₁ : Circle整数egrable f₁ c R)
  证明: circleAverage_add hf₁ hf₂

Depends on / 依赖: circleAverage_add, isAtomistic_dual_iff_isCoatomistic
-/
theorem circleAverage_fun_add {c : Complex} {R : Real} {f₁ f₂ : Complex -> E} (hf₁ : CircleIntegrable f₁ c R)
    (hf₂ : CircleIntegrable f₂ c R) :
    circleAverage (fun z => f₁ z + f₂ z) c R = circleAverage f₁ c R + circleAverage f₂ c R :=
  circleAverage_add hf₁ hf₂

/--
theorem `circleAverage_sum` / 定理 `circleAverage_sum`

English:
theorem circleAverage_sum
  statement: {ι : Type*} {s : Finset ι} {f : ι -> Complex -> E}
  proof: by
  unfold circleAverage
  simp [← Finset.smul_sum, intervalIntegral.integral_finsetSum h]

中文:
定理 circleAverage_sum
  结论: {ι : 类型} {s : Finset ι} {f : ι -> Complex -> E}
  证明: by
  unfold circleAverage
  simp [← Finset.smul_sum, intervalIntegral.integral_finsetSum h]

Depends on / 依赖: Finset, Finset.smul_sum, circleAverage, integral_finsetSum, intervalIntegral, intervalIntegral.integral_finsetSum, smul_sum
-/
theorem circleAverage_sum {ι : Type*} {s : Finset ι} {f : ι -> Complex -> E}
    (h : forall i in s, CircleIntegrable (f i) c R) :
    circleAverage (∑ i in s, f i) c R = ∑ i in s, circleAverage (f i) c R := by
  unfold circleAverage
  simp [← Finset.smul_sum, intervalIntegral.integral_finsetSum h]

/--
theorem `circleAverage_fun_sum` / 定理 `circleAverage_fun_sum`

English:
theorem circleAverage_fun_sum
  statement: {ι : Type*} {s : Finset ι} {f : ι -> Complex -> E}
  proof: by
  convert! circleAverage_sum h
  simp

中文:
定理 circleAverage_fun_sum
  结论: {ι : 类型} {s : Finset ι} {f : ι -> Complex -> E}
  证明: by
  convert! circleAverage_sum h
  simp

Depends on / 依赖: circleAverage_sum, convert
-/
theorem circleAverage_fun_sum {ι : Type*} {s : Finset ι} {f : ι -> Complex -> E}
    (h : forall i in s, CircleIntegrable (f i) c R) :
    circleAverage (fun z => ∑ i in s, f i z) c R = ∑ i in s, circleAverage (f i) c R := by
  convert! circleAverage_sum h
  simp

/--
theorem `circleAverage_sub` / 定理 `circleAverage_sub`

English:
theorem circleAverage_sub
  given: (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R)
  proof: by
  rw [circleAverage]; rw [circleAverage]; rw [circleAverage]; rw [← smul_sub]
  congr
  apply intervalIntegral.integral_sub hf₁ hf₂

中文:
定理 circleAverage_sub
  条件: (hf₁ : Circle整数egrable f₁ c R) (hf₂ : Circle整数egrable f₂ c R)
  证明: by
  rw [circleAverage]; rw [circleAverage]; rw [circleAverage]; rw [← smul_sub]
  congr
  apply intervalIntegral.integral_sub hf₁ hf₂

Depends on / 依赖: circleAverage, integral_sub, intervalIntegral, intervalIntegral.integral_sub, smul_sub
-/
theorem circleAverage_sub (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R) :
    circleAverage (f₁ - f₂) c R = circleAverage f₁ c R - circleAverage f₂ c R := by
  rw [circleAverage]; rw [circleAverage]; rw [circleAverage]; rw [← smul_sub]
  congr
  apply intervalIntegral.integral_sub hf₁ hf₂

/--
theorem `circleAverage_fun_sub` / 定理 `circleAverage_fun_sub`

English:
theorem circleAverage_fun_sub
  given: (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R)
  proof: circleAverage_sub hf₁ hf₂

中文:
定理 circleAverage_fun_sub
  条件: (hf₁ : Circle整数egrable f₁ c R) (hf₂ : Circle整数egrable f₂ c R)
  证明: circleAverage_sub hf₁ hf₂

Depends on / 依赖: circleAverage_sub
-/
theorem circleAverage_fun_sub (hf₁ : CircleIntegrable f₁ c R) (hf₂ : CircleIntegrable f₂ c R) :
    circleAverage (fun z => f₁ z - f₂ z) c R = circleAverage f₁ c R - circleAverage f₂ c R :=
  circleAverage_sub hf₁ hf₂

end Real
