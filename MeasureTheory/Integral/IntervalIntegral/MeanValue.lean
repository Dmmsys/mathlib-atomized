/-
Copyright (c) 2025 Louis (Yiyang) Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis (Yiyang) Liu
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.MeanValue

/-!
# First mean value theorem for interval integrals

We prove versions of the first mean value theorem for interval integrals.

## Main results

* `exists_eq_const_mul_intervalIntegral_of_ae_nonneg` (a.e. nonnegativity of `g` on `s`):
    `∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ)`.
* `exists_eq_const_mul_intervalIntegral_of_nonneg` (pointwise nonnegativity of `g` on `s`):
    `∃ c ∈ uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ)`.

## References

* [V. A. Zorich, *Mathematical Analysis I*][zorich2016],
    Thm. 5 (First mean-value theorem for the integral).
* <https://proofwiki.org/wiki/Mean_Value_Theorem_for_Integrals/Generalization>

## Tags

mean value theorem, interval integral
-/

public section

open MeasureTheory Set intervalIntegral

open scoped Interval

variable {a b : Real} {f g : Real -> Real} {μ : Measure Real}

/--
theorem `exists_eq_const_mul_intervalIntegral_of_ae_nonneg` / 定理 `exists_eq_const_mul_intervalIntegral_of_ae_nonneg`

English:
theorem exists_eq_const_mul_intervalIntegral_of_ae_nonneg
  proof: by
  by_cases h : a = b
  · subst h
    exact ⟨a, by simp, by simp⟩
  wlog hab : a < b generalizing a b
  · simp only [not_lt] at hab
    obtain ⟨c, c_in_uIcc, that⟩ :=
      this (by rwa [uIcc_comm]) hg.symm (by rwa [uIoc_comm]) (by lia) (lt_of_le_of_ne' hab h)
    exact ⟨c, by rwa [uIcc_comm], by 

中文:
定理 存在_eq_const_mul_interval整数egral_of_ae_nonneg
  证明: by
  by_cases h : a = b
  · subst h
    exact ⟨a, by simp, by simp⟩
  wlog hab : a < b generalizing a b
  · simp only [not_lt] at hab
    obtain ⟨c, c_in_uIcc, that⟩ :=
      this (by rwa [uIcc_comm]) hg.symm (by rwa [uIoc_comm]) (by lia) (lt_of_le_of_ne' hab h)
    exact ⟨c, by rwa [uIcc_comm], by 

Depends on / 依赖: Integra, IsConnected, c_in_uIcc, generalizing, hab.le, hg.symm, hs_conn, integral_symm, isConnected_Ioc, lt_of_le_of_ne, not_lt, subseteq, uIcc_comm, uIoc_comm, uIoc_of_le, uIoc_subset_uIcc
-/
theorem exists_eq_const_mul_intervalIntegral_of_ae_nonneg
    (hf : ContinuousOn f (uIcc a b)) (hg : IntervalIntegrable g μ a b)
    (hg0 : forallᵐ x ∂(μ.restrict (Ι a b)), 0 <= g x) :
    exists c in uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ) := by
  by_cases h : a = b
  · subst h
    exact ⟨a, by simp, by simp⟩
  wlog hab : a < b generalizing a b
  · simp only [not_lt] at hab
    obtain ⟨c, c_in_uIcc, that⟩ :=
      this (by rwa [uIcc_comm]) hg.symm (by rwa [uIoc_comm]) (by lia) (lt_of_le_of_ne' hab h)
    exact ⟨c, by rwa [uIcc_comm], by simpa [integral_symm b a]⟩
  let s := Ι a b
  have hs : s = Ioc a b := uIoc_of_le hab.le
  have hs' : s subseteq [[a, b]] := uIoc_subset_uIcc
  have hs_conn : IsConnected s := by simpa [hs] using isConnected_Ioc hab
  have hfg : IntegrableOn (fun x => f x * g x) s μ := by
    rw [← intervalIntegrable_iff]
    exact hg.continuousOn_smul hf
  obtain ⟨c, hc, h⟩ := exists_eq_const_mul_setIntegral_of_ae_nonneg
    hs_conn measurableSet_uIoc (hf.mono hs') (by rwa [← intervalIntegrable_iff]) hfg hg0
  have h' : ∫ (x : Real) in a..b, f x * g x ∂μ = f c * ∫ (x : Real) in a..b, g x ∂μ := by
    simpa [intervalIntegral.integral_of_le hab.le, hs] using h
  exact ⟨c, mem_of_subset_of_mem hs' hc, h'⟩

/--
theorem `exists_eq_const_mul_intervalIntegral_of_nonneg` / 定理 `exists_eq_const_mul_intervalIntegral_of_nonneg`

English:
theorem exists_eq_const_mul_intervalIntegral_of_nonneg
  proof: by
  have hg0_ae : forallᵐ x ∂(μ.restrict (Ι a b)), 0 <= g x := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    exact ae_of_all μ hg0
  exact exists_eq_const_mul_intervalIntegral_of_ae_nonneg hf hg hg0_ae

中文:
定理 存在_eq_const_mul_interval整数egral_of_nonneg
  证明: by
  have hg0_ae : forallᵐ x ∂(μ.restrict (Ι a b)), 0 <= g x := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    exact ae_of_all μ hg0
  exact exists_eq_const_mul_intervalIntegral_of_ae_nonneg hf hg hg0_ae

Depends on / 依赖: ae_of_all, ae_restrict_iff, exists_eq_const_mul_intervalIntegral_of_ae_nonneg, hg0_ae, measurableSet_uIoc, restrict
-/
theorem exists_eq_const_mul_intervalIntegral_of_nonneg
    (hf : ContinuousOn f (uIcc a b)) (hg : IntervalIntegrable g μ a b)
    (hg0 : forall x in Ι a b, 0 <= g x) :
    exists c in uIcc a b, (∫ x in a..b, f x * g x ∂μ) = f c * (∫ x in a..b, g x ∂μ) := by
  have hg0_ae : forallᵐ x ∂(μ.restrict (Ι a b)), 0 <= g x := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    exact ae_of_all μ hg0
  exact exists_eq_const_mul_intervalIntegral_of_ae_nonneg hf hg hg0_ae
