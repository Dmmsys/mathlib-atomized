/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Covering.OneDim
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Lebesgue Differentiation Theorem (Interval Version)

This file proves the interval version of the Lebesgue Differentiation Theorem. There are two
versions in this file.

* `LocallyIntegrable.ae_hasDerivAt_integral` is the global version. It states that if `f : ℝ → E`
  is locally integrable (`E` a Banach space), then for almost every `x`, for any `c : ℝ`, the
  derivative of `∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`.

* `IntervalIntegrable.ae_hasDerivAt_integral` is the local version. It states that if `f : ℝ → E`
  is interval integrable on `a..b`, then for almost every `x ∈ uIcc a b`, for any `c ∈ uIcc a b`,
  the derivative of `∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`.
-/

public section

open MeasureTheory Set Filter Function IsUnifLocDoublingMeasure

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/--
theorem `LocallyIntegrable.ae_hasDerivAt_integral` / 定理 `LocallyIntegrable.ae_hasDerivAt_integral`

English:
theorem LocallyIntegrable.ae_hasDerivAt_integral
  given: {f : Real -> E} (hf : LocallyIntegrable f volume)
  proof: by
  have hg (x y : Real) : IntervalIntegrable f volume x y :=
intervalIntegrable_iff.mpr
      (hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have LDT := (vitaliFamily volume 1).ae_tendsto_average hf
  have h {a b : Real} : ∫ (t : Real) in Ioc a b, f t = ∫ (t : Real) in Icc 

中文:
定理 Locally整数egrable.ae_hasDerivAt_integral
  条件: {f : 实数 -> E} (hf : Locally整数egrable f volume)
  证明: by
  have hg (x y : Real) : IntervalIntegrable f volume x y :=
intervalIntegrable_iff.mpr
      (hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have LDT := (vitaliFamily volume 1).ae_tendsto_average hf
  have h {a b : Real} : ∫ (t : Real) in Ioc a b, f t = ∫ (t : Real) in Icc 

Depends on / 依赖: IntervalIntegrable, ae_tendsto_average, filter_upwards, hasDerivAt_iff_tendsto_slope_left_right, hf.integrableOn_isCompact, hx.comp, integrableOn_isCompact, integral_Icc_eq_integral_Ioc, intervalIntegrable_iff, intervalIntegrable_iff.mpr, isCompact_uIcc, mono_set, tendsto_Icc_vitaliFamil, uIoc_subset_uIcc, vitaliFamily, volume, x.tendsto_Icc_vitaliFamil
-/
theorem LocallyIntegrable.ae_hasDerivAt_integral {f : Real -> E} (hf : LocallyIntegrable f volume) :
    forallᵐ x, forall c, HasDerivAt (fun x => ∫ (t : Real) in c..x, f t) (f x) x := by
  have hg (x y : Real) : IntervalIntegrable f volume x y :=
intervalIntegrable_iff.mpr
      (hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have LDT := (vitaliFamily volume 1).ae_tendsto_average hf
  have h {a b : Real} : ∫ (t : Real) in Ioc a b, f t = ∫ (t : Real) in Icc a b, f t :=
.symm integral_Icc_eq_integral_Ioc (x := a) (y := b) (X := Real)
  filter_upwards [LDT] with x hx
  intro c
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
.mpr (hx.comp x.tendsto_Icc_vitaliFamily_left) · refine Filter.tendsto_congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : y <= x := hy.le
    suffices -((y - x)⁻¹ • ∫ (t : Real) in Icc y x, f t) = (x - y)⁻¹ • ∫ (t : Real) in Icc y x, f t by
      simpa [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_ge, hy, h]
    rw [← neg_smul]; rw [neg_inv]; rw [neg_sub]
.mpr (hx.comp x.tendsto_Icc_vitaliFamily_right) · refine Filter.tendsto_congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : x <= y := hy.le
    simp [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_le, hy, h]

/--
theorem `IntervalIntegrable.ae_hasDerivAt_integral` / 定理 `IntervalIntegrable.ae_hasDerivAt_integral`

English:
theorem IntervalIntegrable.ae_hasDerivAt_integral
  statement: {f : Real -> E} {a b : Real}
  proof: by
  wlog hab : a <= b
  · exact uIcc_comm b a ▸ this hf.symm (by linarith)
  rw [uIcc_of_le hab]
  have h₁ : forallᵐ x, x != a := by simp [ae_iff, measure_singleton]
  have h₂ : forallᵐ x, x != b := by simp [ae_iff, measure_singleton]
  let g (x : Real) := if x in Ioc a b then f x else 0
  have hg 

中文:
定理 整数erval整数egrable.ae_hasDerivAt_integral
  结论: {f : 实数 -> E} {a b : 实数}
  证明: by
  wlog hab : a <= b
  · exact uIcc_comm b a ▸ this hf.symm (by linarith)
  rw [uIcc_of_le hab]
  have h₁ : forallᵐ x, x != a := by simp [ae_iff, measure_singleton]
  have h₂ : forallᵐ x, x != b := by simp [ae_iff, measure_singleton]
  let g (x : Real) := if x in Ioc a b then f x else 0
  have hg 

Depends on / 依赖: LocallyIntegrable, LocallyIntegrable.ae_hasDerivAt_int, ae_hasDerivAt_int, ae_iff, filter_upwards, hf.left, hf.symm, integrableOn_congr_fun, integrable_of_forall_notMem_eq_zero, locallyIntegrable, measure_singleton, uIcc_comm, uIcc_of_le, volume
-/
theorem IntervalIntegrable.ae_hasDerivAt_integral {f : Real -> E} {a b : Real}
    (hf : IntervalIntegrable f volume a b) :
    forallᵐ x, x in uIcc a b -> forall c in uIcc a b, HasDerivAt (fun x => ∫ (t : Real) in c..x, f t) (f x) x := by
  wlog hab : a <= b
  · exact uIcc_comm b a ▸ this hf.symm (by linarith)
  rw [uIcc_of_le hab]
  have h₁ : forallᵐ x, x != a := by simp [ae_iff, measure_singleton]
  have h₂ : forallᵐ x, x != b := by simp [ae_iff, measure_singleton]
  let g (x : Real) := if x in Ioc a b then f x else 0
  have hg : LocallyIntegrable g volume :=
.mpr hf.left integrableOn_congr_fun (by grind [EqOn]) (by simp)
.locallyIntegrable .integrable_of_forall_notMem_eq_zero (by grind)
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg, h₁, h₂] with x hx _ _ _
  intro c hc
refine HasDerivWithinAt.hasDerivAt (s := Ioo a b) ?_
    Ioo_mem_nhds (by grind) (by grind)
  rw [show f x = g x by grind]
  refine (hx c).hasDerivWithinAt.congr (fun y hy => ?_) ?_
  all_goals apply intervalIntegral.integral_congr_ae' <;> filter_upwards <;> grind
