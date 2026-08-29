/-
Copyright (c) 2025 Louis (Yiyang) Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis (Yiyang) Liu
-/
module

public import Mathlib.MeasureTheory.Integral.Average

/-!
# First mean value theorem for set integrals

We prove versions of the first mean value theorem for set integrals.

## Main results

* `exists_eq_const_mul_setIntegral_of_ae_nonneg` (a.e. nonnegativity of `g` on `s`):
    `∃ c ∈ s, (∫ x in s, f x * g x ∂μ) = f c * (∫ x in s, g x ∂μ)`.
* `exists_eq_const_mul_setIntegral_of_nonneg` (pointwise nonnegativity of `g` on `s`):
    `∃ c ∈ s, (∫ x in s, f x * g x ∂μ) = f c * (∫ x in s, g x ∂μ)`.

## Tags

first mean value theorem, set integral
-/

public section

open MeasureTheory

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
  {s : Set α} {f g : α -> Real} {μ : Measure α}

/--
theorem `exists_eq_const_mul_setIntegral_of_ae_nonneg` / 定理 `exists_eq_const_mul_setIntegral_of_ae_nonneg`

English:
theorem exists_eq_const_mul_setIntegral_of_ae_nonneg
  proof: by
  let ρ := fun x => ENNReal.ofReal (g x)
  let ν := μ.withDensity ρ
  have hρ_ae : AEMeasurable ρ (μ.restrict s) := by
    apply AEMeasurable.ennreal_ofReal
    exact hg.aestronglyMeasurable.aemeasurable
  have hρ_top : forallᵐ x ∂μ.restrict s, ρ x < ⊤ := by simp [ρ]
  have h_toReal_ae : (fun x =

中文:
定理 exists_eq_const_mul_setIntegral_of_ae_nonneg
  证明: by
  let ρ := fun x => ENNReal.ofReal (g x)
  let ν := μ.withDensity ρ
  have hρ_ae : AEMeasurable ρ (μ.restrict s) := by
    apply AEMeasurable.ennreal_ofReal
    exact hg.aestronglyMeasurable.aemeasurable
  have hρ_top : forallᵐ x ∂μ.restrict s, ρ x < ⊤ := by simp [ρ]
  have h_toReal_ae : (fun x =

Depends on / 依赖: AEMeasurable, AEMeasurable.ennreal_ofReal, ENNReal, ENNReal.ofReal, MeasureTheory, MeasureTheory.integral_congr_, aemeasurable, aestronglyMeasurable, ennreal_ofReal, h_toReal_ae, hg.aestronglyMeasurable.aemeasurable, hg0.mono, integral_congr_, ofReal, restrict, toReal, withDensity
-/
theorem exists_eq_const_mul_setIntegral_of_ae_nonneg
    (hs_conn : IsConnected s) (hs_meas : MeasurableSet s) (hf : ContinuousOn f s)
    (hg : IntegrableOn g s μ) (hfg : IntegrableOn (fun x => f x * g x) s μ)
    (hg0 : forallᵐ x ∂(μ.restrict s), 0 <= g x) :
    exists c in s, (∫ x in s, f x * g x ∂μ) = f c * (∫ x in s, g x ∂μ) := by
  let ρ := fun x => ENNReal.ofReal (g x)
  let ν := μ.withDensity ρ
  have hρ_ae : AEMeasurable ρ (μ.restrict s) := by
    apply AEMeasurable.ennreal_ofReal
    exact hg.aestronglyMeasurable.aemeasurable
  have hρ_top : forallᵐ x ∂μ.restrict s, ρ x < ⊤ := by simp [ρ]
  have h_toReal_ae : (fun x => (ρ x).toReal) =ᵐ[μ.restrict s] g := by
    apply hg0.mono
    intro x hx
    simpa [ρ]
  have heq : ∫ x in s, f x * g x ∂μ = ∫ x in s, f x ∂ν := by
    calc
      _ = ∫ x in s, (ρ x).toReal * f x ∂μ := by
        apply MeasureTheory.integral_congr_ae
        apply h_toReal_ae.mono
        intro x hx
        simp [hx, mul_comm]
      _ = _ := by
        have h := setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hρ_ae hρ_top f hs_meas
        simp [ν, h]
  have hg1 : ∫ x in s, g x ∂μ = ∫ x in s, (1 : Real) ∂ν := by
    have h := setIntegral_withDensity_eq_setIntegral_toReal_smul₀
      hρ_ae hρ_top (fun _ => (1 : Real)) hs_meas
    calc
      _ = ∫ x in s, (ρ x).toReal ∂μ := by rw [integral_congr_ae h_toReal_ae]
      _ = _ := by simp [ν, h]
  by_cases hν0 : ∫ x in s, (1 : Real) ∂ν = 0
  · rcases hs_conn.nonempty with ⟨c, hc⟩
    refine ⟨c, hc, ?_⟩
    calc
      _ = ∫ x in s, f x ∂ν := heq
      _ = 0 := by
        rw [hν0]; rw [setIntegral_eq_zero_iff_of_nonneg_ae hg0 hg] at hg1
        have heq_zero : ∫ x in s, f x * g x ∂μ = 0 := by
          have heq_ae : (fun x => f x * g x) =ᵐ[μ.restrict s] 0 := by
            apply hg1.mono
            intro x hx
            simp [hx]
          simpa using! integral_congr_ae heq_ae
        rw [← heq]; rw [heq_zero]
      _ = _ := by simp [hν0, hg1]
  · have hν0' : (ν s).toReal != 0 := by simpa using! hν0
    have hνfin : ν s != ⊤ := by intro this; apply hν0'; simp [this]
    have hν0'' : ν s != 0 := by intro this; apply hν0'; simp [this]
    have hint : IntegrableOn f s ν := by
      have hmul_ae : (fun x => (ρ x).toReal * f x) =ᵐ[μ.restrict s] (fun x => f x * g x) := by
        apply h_toReal_ae.mono
        intro x hx
        simp [hx, mul_comm]
      have h_IntOn : IntegrableOn (fun x => (ρ x).toReal * f x) s μ := by
        rwa [integrableOn_congr_fun_ae hmul_ae]
      have h_Int : Integrable f ((μ.restrict s).withDensity ρ) := by
        rwa [integrable_withDensity_iff_integrable_smul₀' hρ_ae hρ_top, ← IntegrableOn]
      have hνrs : ν.restrict s = (μ.restrict s).withDensity ρ := by
        ext t ht
        simp [ht, ν, hs_meas]
      simpa [IntegrableOn, hνrs] using! h_Int
    obtain ⟨c, hc, h_ave⟩ := exists_eq_setAverage hs_conn hf hint hνfin hν0''
    refine ⟨c, hc, ?_⟩
    calc
      _ = ∫ x in s, f x ∂ν := heq
      _ = f c * ∫ x in s, (1 : Real) ∂ν := by
        rw [h_ave]
        simp only [setAverage_eq, smul_eq_mul, integral_const, MeasurableSet.univ,
          measureReal_restrict_apply, Set.univ_inter, mul_one]
        rw [measureReal_def]
        field_simp
      _ = _ := by simp [hg1]

/--
theorem `exists_eq_const_mul_setIntegral_of_nonneg` / 定理 `exists_eq_const_mul_setIntegral_of_nonneg`

English:
theorem exists_eq_const_mul_setIntegral_of_nonneg
  proof: by
  have hg0_ae : forallᵐ x ∂(μ.restrict s), 0 <= g x := by
    rw [ae_restrict_iff' hs_meas]
    exact ae_of_all μ hg0
  exact exists_eq_const_mul_setIntegral_of_ae_nonneg hs_conn hs_meas hf hg hfg hg0_ae

中文:
定理 exists_eq_const_mul_setIntegral_of_nonneg
  证明: by
  have hg0_ae : forallᵐ x ∂(μ.restrict s), 0 <= g x := by
    rw [ae_restrict_iff' hs_meas]
    exact ae_of_all μ hg0
  exact exists_eq_const_mul_setIntegral_of_ae_nonneg hs_conn hs_meas hf hg hfg hg0_ae

Depends on / 依赖: ae_of_all, ae_restrict_iff, exists_eq_const_mul_setIntegral_of_ae_nonneg, hg0_ae, hs_conn, hs_meas, restrict
-/
theorem exists_eq_const_mul_setIntegral_of_nonneg
    (hs_conn : IsConnected s) (hs_meas : MeasurableSet s) (hf : ContinuousOn f s)
    (hg : IntegrableOn g s μ) (hfg : IntegrableOn (fun x => f x * g x) s μ)
    (hg0 : forall x in s, 0 <= g x) :
    exists c in s, (∫ x in s, f x * g x ∂μ) = f c * (∫ x in s, g x ∂μ) := by
  have hg0_ae : forallᵐ x ∂(μ.restrict s), 0 <= g x := by
    rw [ae_restrict_iff' hs_meas]
    exact ae_of_all μ hg0
  exact exists_eq_const_mul_setIntegral_of_ae_nonneg hs_conn hs_meas hf hg hfg hg0_ae
