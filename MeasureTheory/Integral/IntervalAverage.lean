/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Louis (Yiyang) Liu
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integral average over an interval

In this file we introduce notation `⨍ x in a..b, f x` for the average `⨍ x in Ι a b, f x` of `f`
over the interval `Ι a b = Set.Ioc (min a b) (max a b)` w.r.t. the Lebesgue measure, then prove
formulas for this average:

* `interval_average_eq`: `⨍ x in a..b, f x = (b - a)⁻¹ • ∫ x in a..b, f x`;
* `interval_average_eq_div`: `⨍ x in a..b, f x = (∫ x in a..b, f x) / (b - a)`;
* `exists_eq_interval_average_of_measure`:
    `∃ c ∈ Ι a b, f c = ⨍ x in Ι a b, f x ∂μ`.
* `exists_eq_interval_average_of_nullSingletonClass`:
    `∃ c ∈ uIoo a b, f c = ⨍ x in Ι a b, f x ∂μ`.
* `exists_eq_interval_average`:
    `∃ c ∈ uIoo a b, f c = ⨍ x in a..b, f x`.

We also prove that `⨍ x in a..b, f x = ⨍ x in b..a, f x`, see `interval_average_symm`.

## Notation

`⨍ x in a..b, f x`: average of `f` over the interval `Ι a b` w.r.t. the Lebesgue measure.

-/

public section


open MeasureTheory Set intervalIntegral

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/-- `⨍ x in a..b, f x` is the average of `f` over the interval `Ι a b` w.r.t. the Lebesgue
measure. -/
notation3 "⨍ "(...)" in "a".."b",
  "r:60:(scoped f => average (Measure.restrict volume (uIoc a b)) f) => r

/--
theorem `interval_average_symm` / 定理 `interval_average_symm`

English:
theorem interval_average_symm
  given: (f : Real -> E) (a b : Real)
  statement: (⨍ x in a..b, f x) = ⨍ x in b..a, f x
  proof: by
  rw [setAverage_eq]; rw [setAverage_eq]; rw [uIoc_comm]

中文:
定理 interval_average_symm
  条件: (f : 实数 -> E) (a b : 实数)
  结论: (⨍ x in a..b, f x) = ⨍ x in b..a, f x
  证明: by
  rw [setAverage_eq]; rw [setAverage_eq]; rw [uIoc_comm]

Depends on / 依赖: setAverage_eq, uIoc_comm
-/
theorem interval_average_symm (f : Real -> E) (a b : Real) : (⨍ x in a..b, f x) = ⨍ x in b..a, f x := by
  rw [setAverage_eq]; rw [setAverage_eq]; rw [uIoc_comm]

/--
theorem `interval_average_eq` / 定理 `interval_average_eq`

English:
theorem interval_average_eq
  given: (f : Real -> E) (a b : Real)
  proof: by
  rcases le_or_gt a b with h | h
  · rw [setAverage_eq, uIoc_of_le h, Real.volume_real_Ioc_of_le h, integral_of_le h]
  · rw [setAverage_eq, uIoc_of_ge h.le, Real.volume_real_Ioc_of_le h.le, integral_of_ge h.le,
      smul_neg, ← neg_smul, ← inv_neg, neg_sub]

中文:
定理 interval_average_eq
  条件: (f : 实数 -> E) (a b : 实数)
  证明: by
  rcases le_or_gt a b with h | h
  · rw [setAverage_eq, uIoc_of_le h, Real.volume_real_Ioc_of_le h, integral_of_le h]
  · rw [setAverage_eq, uIoc_of_ge h.le, Real.volume_real_Ioc_of_le h.le, integral_of_ge h.le,
      smul_neg, ← neg_smul, ← inv_neg, neg_sub]

Depends on / 依赖: Real.volume_real_Ioc_of_le, h.le, integral_of_ge, integral_of_le, inv_neg, le_or_gt, neg_smul, neg_sub, setAverage_eq, smul_neg, uIoc_of_ge, uIoc_of_le, volume_real_Ioc_of_le
-/
theorem interval_average_eq (f : Real -> E) (a b : Real) :
    (⨍ x in a..b, f x) = (b - a)⁻¹ • ∫ x in a..b, f x := by
  rcases le_or_gt a b with h | h
  · rw [setAverage_eq, uIoc_of_le h, Real.volume_real_Ioc_of_le h, integral_of_le h]
  · rw [setAverage_eq, uIoc_of_ge h.le, Real.volume_real_Ioc_of_le h.le, integral_of_ge h.le,
      smul_neg, ← neg_smul, ← inv_neg, neg_sub]

/--
theorem `interval_average_eq_div` / 定理 `interval_average_eq_div`

English:
theorem interval_average_eq_div
  given: (f : Real -> Real) (a b : Real)
  proof: by
  rw [interval_average_eq]; rw [smul_eq_mul]; rw [div_eq_inv_mul]

中文:
定理 interval_average_eq_div
  条件: (f : 实数 -> 实数) (a b : 实数)
  证明: by
  rw [interval_average_eq]; rw [smul_eq_mul]; rw [div_eq_inv_mul]

Depends on / 依赖: div_eq_inv_mul, interval_average_eq, smul_eq_mul
-/
theorem interval_average_eq_div (f : Real -> Real) (a b : Real) :
    (⨍ x in a..b, f x) = (∫ x in a..b, f x) / (b - a) := by
  rw [interval_average_eq]; rw [smul_eq_mul]; rw [div_eq_inv_mul]

/--
theorem `intervalAverage_congr_codiscreteWithin` / 定理 `intervalAverage_congr_codiscreteWithin`

English:
theorem intervalAverage_congr_codiscreteWithin
  statement: {a b : Real} {f₁ f₂ : Real -> Real}
  proof: by
  rw [interval_average_eq]; rw [integral_congr_codiscreteWithin hf]; rw [← interval_average_eq]

中文:
定理 intervalAverage_congr_codiscreteWithin
  结论: {a b : 实数} {f₁ f₂ : 实数 -> 实数}
  证明: by
  rw [interval_average_eq]; rw [integral_congr_codiscreteWithin hf]; rw [← interval_average_eq]

Depends on / 依赖: integral_congr_codiscreteWithin, interval_average_eq
-/
theorem intervalAverage_congr_codiscreteWithin {a b : Real} {f₁ f₂ : Real -> Real}
    (hf : f₁ =ᶠ[Filter.codiscreteWithin (Ι a b)] f₂) :
    ⨍ (x : Real) in a..b, f₁ x = ⨍ (x : Real) in a..b, f₂ x := by
  rw [interval_average_eq]; rw [integral_congr_codiscreteWithin hf]; rw [← interval_average_eq]

variable {f : Real -> Real} {a b : Real} {μ : Measure Real}

/--
theorem `exists_eq_interval_average_of_measure` / 定理 `exists_eq_interval_average_of_measure`

English:
theorem exists_eq_interval_average_of_measure
  proof: exists_eq_setAverage ⟨nonempty_of_measure_ne_zero hμ0, isPreconnected_Ioc⟩
    (hf.mono uIoc_subset_uIcc) (hf.integrableOn_of_subset_isCompact
    isCompact_uIcc measurableSet_uIoc uIoc_subset_uIcc hμfin) hμfin hμ0

中文:
定理 exists_eq_interval_average_of_measure
  证明: exists_eq_setAverage ⟨nonempty_of_measure_ne_zero hμ0, isPreconnected_Ioc⟩
    (hf.mono uIoc_subset_uIcc) (hf.integrableOn_of_subset_isCompact
    isCompact_uIcc measurableSet_uIoc uIoc_subset_uIcc hμfin) hμfin hμ0

Depends on / 依赖: exists_eq_setAverage, hf.integrableOn_of_subset_isCompact, hf.mono, integrableOn_of_subset_isCompact, isCompact_uIcc, isPreconnected_Ioc, measurableSet_uIoc, nonempty_of_measure_ne_zero, uIoc_subset_uIcc
-/
theorem exists_eq_interval_average_of_measure
    (hf : ContinuousOn f (uIcc a b)) (hμfin : μ (Ι a b) != ⊤) (hμ0 : μ (Ι a b) != 0) :
    exists c in Ι a b, f c = ⨍ x in Ι a b, f x ∂μ :=
  exists_eq_setAverage ⟨nonempty_of_measure_ne_zero hμ0, isPreconnected_Ioc⟩
    (hf.mono uIoc_subset_uIcc) (hf.integrableOn_of_subset_isCompact
    isCompact_uIcc measurableSet_uIoc uIoc_subset_uIcc hμfin) hμfin hμ0

/--
theorem `exists_eq_interval_average_of_nullSingletonClass` / 定理 `exists_eq_interval_average_of_nullSingletonClass`

English:
theorem exists_eq_interval_average_of_nullSingletonClass
  proof: by
  have hint : IntegrableOn f (Ι a b) μ := hf.integrableOn_of_subset_isCompact
    isCompact_uIcc measurableSet_uIoc uIoc_subset_uIcc hμfin
  have h : a != b := by intro hab; simp [hab] at hμ0
  let s := uIoo a b
  have hs' : s subseteq Ι a b := by intro x hx; rcases hx with ⟨h1, h2⟩; grind
  have

中文:
定理 exists_eq_interval_average_of_nullSingletonClass
  证明: by
  have hint : IntegrableOn f (Ι a b) μ := hf.integrableOn_of_subset_isCompact
    isCompact_uIcc measurableSet_uIoc uIoc_subset_uIcc hμfin
  have h : a != b := by intro hab; simp [hab] at hμ0
  let s := uIoo a b
  have hs' : s subseteq Ι a b := by intro x hx; rcases hx with ⟨h1, h2⟩; grind
  have

Depends on / 依赖: IntegrableOn, Ioo_ae_eq_Ioc, exists_eq_setAverage, hf.integrableOn_of_subset_isCompact, hs_ev, integrableOn_of_subset_isCompact, isCompact_uIcc, isConnected_uIoo, measurableSet_uIoc, measure_congr, subseteq, uIoc_subset_uIcc
-/
theorem exists_eq_interval_average_of_nullSingletonClass
    [NullSingletonClass μ] (hf : ContinuousOn f (uIcc a b)) (hμfin : μ (Ι a b) != ⊤)
    (hμ0 : μ (Ι a b) != 0) : exists c in uIoo a b, f c = ⨍ x in Ι a b, f x ∂μ := by
  have hint : IntegrableOn f (Ι a b) μ := hf.integrableOn_of_subset_isCompact
    isCompact_uIcc measurableSet_uIoc uIoc_subset_uIcc hμfin
  have h : a != b := by intro hab; simp [hab] at hμ0
  let s := uIoo a b
  have hs' : s subseteq Ι a b := by intro x hx; rcases hx with ⟨h1, h2⟩; grind
  have hs_ev : s =ᵐ[μ] Ι a b := by simpa using! Ioo_ae_eq_Ioc
  have hμ0' : μ s != 0 := by
    have hμ : μ s = μ (Ι a b) := by rw [measure_congr hs_ev]
    rwa [hμ]
  obtain ⟨c, hc, heq⟩ := exists_eq_setAverage (isConnected_uIoo h) (hf.mono uIoo_subset_uIcc_self)
    (hint.mono_set hs') (measure_ne_top_of_subset hs' hμfin) hμ0'
  exact ⟨c, hc, by rwa [← setAverage_congr hs_ev]⟩

@[deprecated (since := "2026-06-09")]
alias exists_eq_interval_average_of_noAtoms := exists_eq_interval_average_of_nullSingletonClass

/--
theorem `exists_eq_interval_average` / 定理 `exists_eq_interval_average`

English:
theorem exists_eq_interval_average
  proof: exists_eq_interval_average_of_nullSingletonClass hf (by simp)
    (by simpa using sub_ne_zero.mpr hab.symm)

中文:
定理 exists_eq_interval_average
  证明: exists_eq_interval_average_of_nullSingletonClass hf (by simp)
    (by simpa using sub_ne_zero.mpr hab.symm)

Depends on / 依赖: exists_eq_interval_average_of_nullSingletonClass, hab.symm, sub_ne_zero, sub_ne_zero.mpr
-/
theorem exists_eq_interval_average
    (hab : a != b) (hf : ContinuousOn f (uIcc a b)) :
    exists c in uIoo a b, f c = ⨍ x in a..b, f x :=
  exists_eq_interval_average_of_nullSingletonClass hf (by simp)
    (by simpa using sub_ne_zero.mpr hab.symm)
