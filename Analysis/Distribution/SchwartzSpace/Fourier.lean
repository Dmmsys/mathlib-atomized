/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion

/-!
# Fourier transform on Schwartz functions

This file constructs the Fourier transform as a continuous linear map acting on Schwartz
functions, in `fourierTransformCLM`. It is also given as a continuous linear equiv, in
`fourierTransformCLE`.

## Main statements
* `SchwartzMap.fderivCLM_fourier_eq`: The derivative of the Fourier transform is given by the
  Fourier transform of the multiplication with `-(2 * π * Complex.I) • innerSL ℝ`.
* `SchwartzMap.lineDerivOp_fourier_eq`: The line derivative of the Fourier transform is given by the
  Fourier transform of the multiplication with `-(2 * π * Complex.I) • (inner ℝ · m)`.
* `SchwartzMap.integral_bilin_fourier_eq`: The Fourier transform is self-adjoint.
* `SchwartzMap.integral_inner_fourier_fourier`: Plancherel's theorem for Schwartz functions.

-/

@[expose] public section

open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace

noncomputable section

namespace SchwartzMap

variable
  (𝕜 : Type*) [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E] [NormedSpace 𝕜 E] [SMulCommClass Complex 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V]

section definition

/--
Definition of `fourierTransformCLM` / `fourierTransformCLM` 的定义

English:
definition fourierTransformCLM
  signature: : 𝓢(V, E) ->L[𝕜] 𝓢(V, E)
  body: by
  refine mkCLM ((𝓕 : (V -> E) -> (V -> E)) ·) ?_ ?_ ?_ ?_
  · intro f g
    simp [fourier_eq, integral_add ((fourierIntegral_convergent_iff _).mpr f.integrable)
      ((fourierIntegral_convergent_iff _).mpr g.integrable)]
  · simp [fourier_eq, smul_comm, integral_smul]
  · exact fun f => contDiff_fourier (fun n _ => integrable_pow_mul volume f n)
  · rintro ⟨k, n⟩
    refine ⟨Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1),
      (2 * π) ^ n * (2 * n + 2) ^ k * (Finset.range (n + 1) ×ˢ Finset.range (k + 1)).card *
        2 ^ integrablePower (volume : Measure V) *
        (∫ x : V, (1 + ‖x‖) ^ (- integrablePower (volume : Measure V) : Real)) * 2, by positivity,
      fun f x => ?_⟩
    apply (pow_mul_norm_iteratedFDeriv_fourier_le (f.smooth ⊤)
      (fun k n _hk _hn => integrable_pow_mul_iteratedFDeriv _ f k n) le_top le_top x).trans
    simp only [mul_assoc]
    gcongr
    calc
    _ <= ∑ _ in Finset.range (n + 1) ×ˢ Finset.range (k + 1),
        2 ^ integrablePower (volume : Measure V) *
          (∫ x : V, (1 + ‖x‖) ^ (- integrablePower (volume : Measure V) : Real)) * 2 *
          (Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1)).sup
          (schwartzSeminormFamily 𝕜 V E) f := by
      gcongr with p
      apply (f.integral_pow_mul_iteratedFDeriv_le 𝕜 ..).trans
      simp only [mul_assoc, two_mul]
      gcongr
      · have : (0, p.2) in Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ
            Finset.range (k + 1) := by simp_all
        apply Seminorm.le_def.mp (Finset.le_sup (f := fun p => SchwartzMap.seminorm 𝕜 p.1 p.2) this)
      · have : (p.1 + integrablePower (volume : Measure V), p.2) in Finset.range
            (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1) := by simp_all
        apply Seminorm.le_def.mp (Finset.le_sup (f := fun p => SchwartzMap.seminorm 𝕜 p.1 p.2) this)
    _ = _ := by simp [mul_assoc]

中文:
定义 fourierTransformCLM
  签名: : 𝓢(V, E) ->L[𝕜] 𝓢(V, E)
  定义体: by
  refine mkCLM ((𝓕 : (V -> E) -> (V -> E)) ·) ?_ ?_ ?_ ?_
  · intro f g
    simp [fourier_eq, integral_add ((fourierIntegral_convergent_iff _).mpr f.integrable)
      ((fourierIntegral_convergent_iff _).mpr g.integrable)]
  · simp [fourier_eq, smul_comm, integral_smul]
  · exact fun f => contDiff_fourier (fun n _ => integrable_pow_mul volume f n)
  · rintro ⟨k, n⟩
    refine ⟨Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1),
      (2 * π) ^ n * (2 * n + 2) ^ k * (Finset.range (n + 1) ×ˢ Finset.range (k + 1)).card *
        2 ^ integrablePower (volume : Measure V) *
        (∫ x : V, (1 + ‖x‖) ^ (- integrablePower (volume : Measure V) : Real)) * 2, by positivity,
      fun f x => ?_⟩
    apply (pow_mul_norm_iteratedFDeriv_fourier_le (f.smooth ⊤)
      (fun k n _hk _hn => integrable_pow_mul_iteratedFDeriv _ f k n) le_top le_top x).trans
    simp only [mul_assoc]
    gcongr
    calc
    _ <= ∑ _ in Finset.range (n + 1) ×ˢ Finset.range (k + 1),
        2 ^ integrablePower (volume : Measure V) *
          (∫ x : V, (1 + ‖x‖) ^ (- integrablePower (volume : Measure V) : Real)) * 2 *
          (Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1)).sup
          (schwartzSeminormFamily 𝕜 V E) f := by
      gcongr with p
      apply (f.integral_pow_mul_iteratedFDeriv_le 𝕜 ..).trans
      simp only [mul_assoc, two_mul]
      gcongr
      · have : (0, p.2) in Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ
            Finset.range (k + 1) := by simp_all
        apply Seminorm.le_def.mp (Finset.le_sup (f := fun p => SchwartzMap.seminorm 𝕜 p.1 p.2) this)
      · have : (p.1 + integrablePower (volume : Measure V), p.2) in Finset.range
            (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1) := by simp_all
        apply Seminorm.le_def.mp (Finset.le_sup (f := fun p => SchwartzMap.seminorm 𝕜 p.1 p.2) this)
    _ = _ := by simp [mul_assoc]

Depends on / 依赖: Finset, Finset.range, Measure, contDiff_fourier, f.integrable, fourierIntegral_convergent_iff, fourier_eq, g.integrable, integrable, integrablePower, integrable_pow_mul, integral_add, integral_smul, smul_comm, volume
-/
def fourierTransformCLM : 𝓢(V, E) ->L[𝕜] 𝓢(V, E) := by
  refine mkCLM ((𝓕 : (V -> E) -> (V -> E)) ·) ?_ ?_ ?_ ?_
  · intro f g
    simp [fourier_eq, integral_add ((fourierIntegral_convergent_iff _).mpr f.integrable)
      ((fourierIntegral_convergent_iff _).mpr g.integrable)]
  · simp [fourier_eq, smul_comm, integral_smul]
  · exact fun f => contDiff_fourier (fun n _ => integrable_pow_mul volume f n)
  · rintro ⟨k, n⟩
    refine ⟨Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1),
      (2 * π) ^ n * (2 * n + 2) ^ k * (Finset.range (n + 1) ×ˢ Finset.range (k + 1)).card *
        2 ^ integrablePower (volume : Measure V) *
        (∫ x : V, (1 + ‖x‖) ^ (- integrablePower (volume : Measure V) : Real)) * 2, by positivity,
      fun f x => ?_⟩
    apply (pow_mul_norm_iteratedFDeriv_fourier_le (f.smooth ⊤)
      (fun k n _hk _hn => integrable_pow_mul_iteratedFDeriv _ f k n) le_top le_top x).trans
    simp only [mul_assoc]
    gcongr
    calc
    _ <= ∑ _ in Finset.range (n + 1) ×ˢ Finset.range (k + 1),
        2 ^ integrablePower (volume : Measure V) *
          (∫ x : V, (1 + ‖x‖) ^ (- integrablePower (volume : Measure V) : Real)) * 2 *
          (Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1)).sup
          (schwartzSeminormFamily 𝕜 V E) f := by
      gcongr with p
      apply (f.integral_pow_mul_iteratedFDeriv_le 𝕜 ..).trans
      simp only [mul_assoc, two_mul]
      gcongr
      · have : (0, p.2) in Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ
            Finset.range (k + 1) := by simp_all
        apply Seminorm.le_def.mp (Finset.le_sup (f := fun p => SchwartzMap.seminorm 𝕜 p.1 p.2) this)
      · have : (p.1 + integrablePower (volume : Measure V), p.2) in Finset.range
            (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1) := by simp_all
        apply Seminorm.le_def.mp (Finset.le_sup (f := fun p => SchwartzMap.seminorm 𝕜 p.1 p.2) this)
    _ = _ := by simp [mul_assoc]

/--
Instance `instFourierTransform` / 实例 `instFourierTransform`

English:
instance instFourierTransform
  signature: : FourierTransform 𝓢(V, E) 𝓢(V, E) where
  body: fourierTransformCLM Complex f

中文:
实例 instFourierTransform
  签名: : Fourier变换 𝓢(V, E) 𝓢(V, E) where
  定义体: fourierTransformCLM Complex f

Depends on / 依赖: fourierTransformCLM
-/
instance instFourierTransform : FourierTransform 𝓢(V, E) 𝓢(V, E) where
  fourier f := fourierTransformCLM Complex f

/--
Instance `instFourierAdd` / 实例 `instFourierAdd`

English:
instance instFourierAdd
  signature: : FourierAdd 𝓢(V, E) 𝓢(V, E) where
  body: ContinuousLinearMap.map_add _

中文:
实例 instFourierAdd
  签名: : FourierAdd 𝓢(V, E) 𝓢(V, E) where
  定义体: ContinuousLinearMap.map_add _

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.map_add, map_add
-/
instance instFourierAdd : FourierAdd 𝓢(V, E) 𝓢(V, E) where
  fourier_add := ContinuousLinearMap.map_add _

/--
Instance `instFourierSMul` / 实例 `instFourierSMul`

English:
instance instFourierSMul
  signature: : FourierSMul 𝕜 𝓢(V, E) 𝓢(V, E) where
  body: (fourierTransformCLM 𝕜).map_smul

中文:
实例 instFourierSMul
  签名: : FourierSMul 𝕜 𝓢(V, E) 𝓢(V, E) where
  定义体: (fourierTransformCLM 𝕜).map_smul

Depends on / 依赖: fourierTransformCLM, map_smul
-/
instance instFourierSMul : FourierSMul 𝕜 𝓢(V, E) 𝓢(V, E) where
  fourier_smul := (fourierTransformCLM 𝕜).map_smul

/--
Instance `instContinuousFourier` / 实例 `instContinuousFourier`

English:
instance instContinuousFourier
  signature: : ContinuousFourier 𝓢(V, E) 𝓢(V, E) where
  body: ContinuousLinearMap.continuous _

中文:
实例 instContinuousFourier
  签名: : 余ntinuousFourier 𝓢(V, E) 𝓢(V, E) where
  定义体: ContinuousLinearMap.continuous _

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.continuous, continuous
-/
instance instContinuousFourier : ContinuousFourier 𝓢(V, E) 𝓢(V, E) where
  continuous_fourier := ContinuousLinearMap.continuous _

/--
lemma `fourier_coe` / 引理 `fourier_coe`

English:
lemma fourier_coe
  given: (f : 𝓢(V, E))
  statement: 𝓕 f = 𝓕 (f : V -> E)
  proof: rfl

@[simp]

中文:
引理 fourier_coe
  条件: (f : 𝓢(V, E))
  结论: 𝓕 f = 𝓕 (f : V -> E)
  证明: rfl

@[simp]
-/
lemma fourier_coe (f : 𝓢(V, E)) : 𝓕 f = 𝓕 (f : V -> E) := rfl

@[simp]
/--
theorem `fourierTransformCLM_apply` / 定理 `fourierTransformCLM_apply`

English:
theorem fourierTransformCLM_apply
  given: (f : 𝓢(V, E))
  proof: rfl

中文:
定理 fourierTransformCLM_apply
  条件: (f : 𝓢(V, E))
  证明: rfl
-/
theorem fourierTransformCLM_apply (f : 𝓢(V, E)) :
    fourierTransformCLM 𝕜 f = 𝓕 f := rfl

/--
Instance `instFourierTransformInv` / 实例 `instFourierTransformInv`

English:
instance instFourierTransformInv
  signature: : FourierTransformInv 𝓢(V, E) 𝓢(V, E) where
  body: (compCLMOfContinuousLinearEquiv Complex (LinearIsometryEquiv.neg Real (E := V)))
      ∘L (fourierTransformCLM Complex)

中文:
实例 instFourierTransformInv
  签名: : FourierTransformInv 𝓢(V, E) 𝓢(V, E) where
  定义体: (compCLMOfContinuousLinearEquiv Complex (LinearIsometryEquiv.neg Real (E := V)))
      ∘L (fourierTransformCLM Complex)

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.neg, compCLMOfContinuousLinearEquiv
-/
instance instFourierTransformInv : FourierTransformInv 𝓢(V, E) 𝓢(V, E) where
  fourierInv := (compCLMOfContinuousLinearEquiv Complex (LinearIsometryEquiv.neg Real (E := V)))
      ∘L (fourierTransformCLM Complex)

/--
Instance `instFourierInvAdd` / 实例 `instFourierInvAdd`

English:
instance instFourierInvAdd
  signature: : FourierInvAdd 𝓢(V, E) 𝓢(V, E) where
  body: ContinuousLinearMap.map_add _

中文:
实例 instFourierInvAdd
  签名: : FourierInvAdd 𝓢(V, E) 𝓢(V, E) where
  定义体: ContinuousLinearMap.map_add _

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.map_add, map_add
-/
instance instFourierInvAdd : FourierInvAdd 𝓢(V, E) 𝓢(V, E) where
  fourierInv_add := ContinuousLinearMap.map_add _

/--
Instance `instFourierInvSMul` / 实例 `instFourierInvSMul`

English:
instance instFourierInvSMul
  signature: : FourierInvSMul 𝕜 𝓢(V, E) 𝓢(V, E) where
  body: ((compCLMOfContinuousLinearEquiv 𝕜 (D := V) (E := V) (F := E)
    (LinearIsometryEquiv.neg Real (E := V))) ∘L (fourierTransformCLM 𝕜)).map_smul

中文:
实例 instFourierInvSMul
  签名: : FourierInvSMul 𝕜 𝓢(V, E) 𝓢(V, E) where
  定义体: ((compCLMOfContinuousLinearEquiv 𝕜 (D := V) (E := V) (F := E)
    (LinearIsometryEquiv.neg Real (E := V))) ∘L (fourierTransformCLM 𝕜)).map_smul

Depends on / 依赖: compCLMOfContinuousLinearEquiv
-/
instance instFourierInvSMul : FourierInvSMul 𝕜 𝓢(V, E) 𝓢(V, E) where
  fourierInv_smul := ((compCLMOfContinuousLinearEquiv 𝕜 (D := V) (E := V) (F := E)
    (LinearIsometryEquiv.neg Real (E := V))) ∘L (fourierTransformCLM 𝕜)).map_smul

/--
Instance `instContinuousFourierInv` / 实例 `instContinuousFourierInv`

English:
instance instContinuousFourierInv
  signature: : ContinuousFourierInv 𝓢(V, E) 𝓢(V, E) where
  body: ContinuousLinearMap.continuous _

中文:
实例 instContinuousFourierInv
  签名: : 余ntinuousFourierInv 𝓢(V, E) 𝓢(V, E) where
  定义体: ContinuousLinearMap.continuous _

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.continuous, continuous
-/
instance instContinuousFourierInv : ContinuousFourierInv 𝓢(V, E) 𝓢(V, E) where
  continuous_fourierInv := ContinuousLinearMap.continuous _

/--
lemma `fourierInv_coe` / 引理 `fourierInv_coe`

English:
lemma fourierInv_coe
  given: (f : 𝓢(V, E))
  statement: 𝓕⁻ f = 𝓕⁻ (f : V -> E)
  proof: by
  ext x
  exact (fourierInv_eq_fourier_neg f x).symm

中文:
引理 fourierInv_coe
  条件: (f : 𝓢(V, E))
  结论: 𝓕⁻ f = 𝓕⁻ (f : V -> E)
  证明: by
  ext x
  exact (fourierInv_eq_fourier_neg f x).symm

Depends on / 依赖: fourierInv_eq_fourier_neg
-/
lemma fourierInv_coe (f : 𝓢(V, E)) : 𝓕⁻ f = 𝓕⁻ (f : V -> E) := by
  ext x
  exact (fourierInv_eq_fourier_neg f x).symm

/--
lemma `fourierInv_apply_eq` / 引理 `fourierInv_apply_eq`

English:
lemma fourierInv_apply_eq
  given: (f : 𝓢(V, E))
  proof: by
  rfl

中文:
引理 fourierInv_apply_eq
  条件: (f : 𝓢(V, E))
  证明: by
  rfl
-/
lemma fourierInv_apply_eq (f : 𝓢(V, E)) :
    𝓕⁻ f = (compCLMOfContinuousLinearEquiv Complex (LinearIsometryEquiv.neg Real (E := V))) (𝓕 f) := by
  rfl

variable [CompleteSpace E]

/--
Instance `instFourierPair` / 实例 `instFourierPair`

English:
instance instFourierPair
  signature: : FourierPair 𝓢(V, E) 𝓢(V, E) where
  body: by
    intro f
    ext x
    rw [fourierInv_coe]; rw [fourier_coe]; rw [f.continuous.fourierInv_fourier_eq f.integrable
      (𝓕 f).integrable]

中文:
实例 instFourierPair
  签名: : FourierPair 𝓢(V, E) 𝓢(V, E) where
  定义体: by
    intro f
    ext x
    rw [fourierInv_coe]; rw [fourier_coe]; rw [f.continuous.fourierInv_fourier_eq f.integrable
      (𝓕 f).integrable]

Depends on / 依赖: continuous, f.continuous.fourierInv_fourier_eq, f.integrable, fourierInv_coe, fourierInv_fourier_eq, fourier_coe, integrable
-/
instance instFourierPair : FourierPair 𝓢(V, E) 𝓢(V, E) where
  fourierInv_fourier_eq := by
    intro f
    ext x
    rw [fourierInv_coe]; rw [fourier_coe]; rw [f.continuous.fourierInv_fourier_eq f.integrable
      (𝓕 f).integrable]

/--
Instance `instFourierInvPair` / 实例 `instFourierInvPair`

English:
instance instFourierInvPair
  signature: : FourierInvPair 𝓢(V, E) 𝓢(V, E) where
  body: by
    intro f
    ext x
    rw [fourier_coe]; rw [fourierInv_coe]; rw [f.continuous.fourier_fourierInv_eq f.integrable
      (𝓕 f).integrable]

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLE := FourierTransform.fourierCLE

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLE_apply := FourierTransform.fourierCLE_apply

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLE_symm_apply := FourierTransform.fourierCLE_symm_apply

中文:
实例 instFourierInvPair
  签名: : FourierInvPair 𝓢(V, E) 𝓢(V, E) where
  定义体: by
    intro f
    ext x
    rw [fourier_coe]; rw [fourierInv_coe]; rw [f.continuous.fourier_fourierInv_eq f.integrable
      (𝓕 f).integrable]

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLE := FourierTransform.fourierCLE

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLE_apply := FourierTransform.fourierCLE_apply

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLE_symm_apply := FourierTransform.fourierCLE_symm_apply

Depends on / 依赖: continuous, f.continuous.fourier_fourierInv_eq, f.integrable, fourierInv_coe, fourier_coe, fourier_fourierInv_eq, integrable
-/
instance instFourierInvPair : FourierInvPair 𝓢(V, E) 𝓢(V, E) where
  fourier_fourierInv_eq := by
    intro f
    ext x
    rw [fourier_coe]; rw [fourierInv_coe]; rw [f.continuous.fourier_fourierInv_eq f.integrable
      (𝓕 f).integrable]

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLE := FourierTransform.fourierCLE

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLE_apply := FourierTransform.fourierCLE_apply

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLE_symm_apply := FourierTransform.fourierCLE_symm_apply

end definition

section eval

variable {𝕜' : Type*} [NormedField 𝕜']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace Complex G] [NormedSpace 𝕜' G] [SMulCommClass Real 𝕜' G]

variable (𝕜') in
/--
theorem `fourier_evalCLM_eq` / 定理 `fourier_evalCLM_eq`

English:
theorem fourier_evalCLM_eq
  given: (f : 𝓢(V, F ->L[Real] G)) (m : F)
  proof: by
  ext x
  exact (fourier_continuousLinearMap_apply f.integrable).symm

中文:
定理 fourier_evalCLM_eq
  条件: (f : 𝓢(V, F ->L[实数] G)) (m : F)
  证明: by
  ext x
  exact (fourier_continuousLinearMap_apply f.integrable).symm

Depends on / 依赖: f.integrable, fourier_continuousLinearMap_apply, integrable
-/
theorem fourier_evalCLM_eq (f : 𝓢(V, F ->L[Real] G)) (m : F) :
    𝓕 (SchwartzMap.evalCLM 𝕜' V G m f) = SchwartzMap.evalCLM 𝕜' V G m (𝓕 f) := by
  ext x
  exact (fourier_continuousLinearMap_apply f.integrable).symm

end eval

section deriv

/--
theorem `fderivCLM_fourier_eq` / 定理 `fderivCLM_fourier_eq`

English:
theorem fderivCLM_fourier_eq
  given: (f : 𝓢(V, E))
  proof: by
  ext1 x
  change fderiv Real (𝓕 ⇑f) x = 𝓕 (VectorFourier.fourierSMulRight (innerSL Real) f) x
  rw [fderiv_fourier f.integrable]
  simpa using f.integrable_pow_mul volume 1

中文:
定理 fderivCLM_fourier_eq
  条件: (f : 𝓢(V, E))
  证明: by
  ext1 x
  change fderiv Real (𝓕 ⇑f) x = 𝓕 (VectorFourier.fourierSMulRight (innerSL Real) f) x
  rw [fderiv_fourier f.integrable]
  simpa using f.integrable_pow_mul volume 1

Depends on / 依赖: VectorFourier, VectorFourier.fourierSMulRight, f.integrable, f.integrable_pow_mul, fderiv, fderiv_fourier, fourierSMulRight, innerSL, integrable, integrable_pow_mul, volume
-/
theorem fderivCLM_fourier_eq (f : 𝓢(V, E)) :
    fderivCLM 𝕜 V E (𝓕 f) = 𝓕 (-(2 * π * Complex.I) • smulRightCLM Complex E (innerSL Real) f) := by
  ext1 x
  change fderiv Real (𝓕 ⇑f) x = 𝓕 (VectorFourier.fourierSMulRight (innerSL Real) f) x
  rw [fderiv_fourier f.integrable]
  simpa using f.integrable_pow_mul volume 1

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fourier_fderivCLM_eq` / 定理 `fourier_fderivCLM_eq`

English:
theorem fourier_fderivCLM_eq
  given: (f : 𝓢(V, E))
  proof: by
  ext x m
  change 𝓕 (fderiv Real ⇑f) x m = _
  simp [fourier_fderiv f.integrable f.differentiable (fderivCLM Real V E f).integrable,
    innerSL_apply_apply Real, fourier_coe]

中文:
定理 fourier_fderivCLM_eq
  条件: (f : 𝓢(V, E))
  证明: by
  ext x m
  change 𝓕 (fderiv Real ⇑f) x m = _
  simp [fourier_fderiv f.integrable f.differentiable (fderivCLM Real V E f).integrable,
    innerSL_apply_apply Real, fourier_coe]

Depends on / 依赖: differentiable, f.differentiable, f.integrable, fderiv, fderivCLM, fourier_coe, fourier_fderiv, innerSL_apply_apply, integrable
-/
theorem fourier_fderivCLM_eq (f : 𝓢(V, E)) :
    𝓕 (fderivCLM 𝕜 V E f) = (2 * π * Complex.I) • smulRightCLM Complex E (innerSL Real) (𝓕 f) := by
  ext x m
  change 𝓕 (fderiv Real ⇑f) x m = _
  simp [fourier_fderiv f.integrable f.differentiable (fderivCLM Real V E f).integrable,
    innerSL_apply_apply Real, fourier_coe]

open LineDeriv

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineDerivOp_fourier_eq` / 定理 `lineDerivOp_fourier_eq`

English:
theorem lineDerivOp_fourier_eq
  given: (f : 𝓢(V, E)) (m : V)
  proof: by
  change SchwartzMap.evalCLM Real V E m (fderivCLM Real V E (𝓕 f)) = _
  rw [fderivCLM_fourier_eq]; rw [← fourier_evalCLM_eq]
  congr
  ext
  have : (inner Real · m).HasTemperateGrowth := ((innerSL Real).flip m).hasTemperateGrowth
  simp [this, innerSL_apply_apply Real]

中文:
定理 lineDerivOp_fourier_eq
  条件: (f : 𝓢(V, E)) (m : V)
  证明: by
  change SchwartzMap.evalCLM Real V E m (fderivCLM Real V E (𝓕 f)) = _
  rw [fderivCLM_fourier_eq]; rw [← fourier_evalCLM_eq]
  congr
  ext
  have : (inner Real · m).HasTemperateGrowth := ((innerSL Real).flip m).hasTemperateGrowth
  simp [this, innerSL_apply_apply Real]

Depends on / 依赖: HasTemperateGrowth, SchwartzMap, SchwartzMap.evalCLM, evalCLM, fderivCLM, fderivCLM_fourier_eq, fourier_evalCLM_eq, hasTemperateGrowth, innerSL, innerSL_apply_apply
-/
theorem lineDerivOp_fourier_eq (f : 𝓢(V, E)) (m : V) :
    ∂_{m} (𝓕 f) = 𝓕 (-(2 * π * Complex.I) • smulLeftCLM E (inner Real · m) f) := by
  change SchwartzMap.evalCLM Real V E m (fderivCLM Real V E (𝓕 f)) = _
  rw [fderivCLM_fourier_eq]; rw [← fourier_evalCLM_eq]
  congr
  ext
  have : (inner Real · m).HasTemperateGrowth := ((innerSL Real).flip m).hasTemperateGrowth
  simp [this, innerSL_apply_apply Real]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fourier_lineDerivOp_eq` / 定理 `fourier_lineDerivOp_eq`

English:
theorem fourier_lineDerivOp_eq
  given: (f : 𝓢(V, E)) (m : V)
  proof: by
  change 𝓕 (SchwartzMap.evalCLM Real V E m (fderivCLM Real V E f)) = _
  ext
  have : (inner Real · m).HasTemperateGrowth := ((innerSL Real).flip m).hasTemperateGrowth
  simp [fourier_evalCLM_eq Real, fourier_fderivCLM_eq, this, innerSL_apply_apply Real]

中文:
定理 fourier_lineDerivOp_eq
  条件: (f : 𝓢(V, E)) (m : V)
  证明: by
  change 𝓕 (SchwartzMap.evalCLM Real V E m (fderivCLM Real V E f)) = _
  ext
  have : (inner Real · m).HasTemperateGrowth := ((innerSL Real).flip m).hasTemperateGrowth
  simp [fourier_evalCLM_eq Real, fourier_fderivCLM_eq, this, innerSL_apply_apply Real]

Depends on / 依赖: HasTemperateGrowth, SchwartzMap, SchwartzMap.evalCLM, evalCLM, fderivCLM, fourier_evalCLM_eq, fourier_fderivCLM_eq, hasTemperateGrowth, innerSL, innerSL_apply_apply
-/
theorem fourier_lineDerivOp_eq (f : 𝓢(V, E)) (m : V) :
    𝓕 (∂_{m} f) = (2 * π * Complex.I) • smulLeftCLM E (inner Real · m) (𝓕 f) := by
  change 𝓕 (SchwartzMap.evalCLM Real V E m (fderivCLM Real V E f)) = _
  ext
  have : (inner Real · m).HasTemperateGrowth := ((innerSL Real).flip m).hasTemperateGrowth
  simp [fourier_evalCLM_eq Real, fourier_fderivCLM_eq, this, innerSL_apply_apply Real]

/--
theorem `lineDerivOp_fourierInv_eq` / 定理 `lineDerivOp_fourierInv_eq`

English:
theorem lineDerivOp_fourierInv_eq
  given: (f : 𝓢(V, E)) (m : V)
  proof: by
  simp [fourierInv_apply_eq, lineDerivOp_compCLMOfContinuousLinearEquiv, lineDerivOp_fourier_eq]

中文:
定理 lineDerivOp_fourierInv_eq
  条件: (f : 𝓢(V, E)) (m : V)
  证明: by
  simp [fourierInv_apply_eq, lineDerivOp_compCLMOfContinuousLinearEquiv, lineDerivOp_fourier_eq]

Depends on / 依赖: fourierInv_apply_eq, lineDerivOp_compCLMOfContinuousLinearEquiv, lineDerivOp_fourier_eq
-/
theorem lineDerivOp_fourierInv_eq (f : 𝓢(V, E)) (m : V) :
    ∂_{m} (𝓕⁻ f) = 𝓕⁻ ((2 * π * Complex.I) • smulLeftCLM E (inner Real · m) f) := by
  simp [fourierInv_apply_eq, lineDerivOp_compCLMOfContinuousLinearEquiv, lineDerivOp_fourier_eq]

/--
theorem `fourierInv_lineDerivOp_eq` / 定理 `fourierInv_lineDerivOp_eq`

English:
theorem fourierInv_lineDerivOp_eq
  given: (f : 𝓢(V, E)) (m : V)
  proof: by
  have : (inner Real · m).HasTemperateGrowth := by fun_prop
  simp [fourierInv_apply_eq, fourier_lineDerivOp_eq,
    smulLeftCLM_compCLMOfContinuousLinearEquiv Complex this, Function.comp_def, smulLeftCLM_fun_neg this]

中文:
定理 fourierInv_lineDerivOp_eq
  条件: (f : 𝓢(V, E)) (m : V)
  证明: by
  have : (inner Real · m).HasTemperateGrowth := by fun_prop
  simp [fourierInv_apply_eq, fourier_lineDerivOp_eq,
    smulLeftCLM_compCLMOfContinuousLinearEquiv Complex this, Function.comp_def, smulLeftCLM_fun_neg this]

Depends on / 依赖: Function, Function.comp_def, HasTemperateGrowth, comp_def, fourierInv_apply_eq, fourier_lineDerivOp_eq, fun_prop, smulLeftCLM_compCLMOfContinuousLinearEquiv, smulLeftCLM_fun_neg
-/
theorem fourierInv_lineDerivOp_eq (f : 𝓢(V, E)) (m : V) :
    𝓕⁻ (∂_{m} f) = -(2 * π * Complex.I) • smulLeftCLM E (inner Real · m) (𝓕⁻ f) := by
  have : (inner Real · m).HasTemperateGrowth := by fun_prop
  simp [fourierInv_apply_eq, fourier_lineDerivOp_eq,
    smulLeftCLM_compCLMOfContinuousLinearEquiv Complex this, Function.comp_def, smulLeftCLM_fun_neg this]

end deriv

section fubini

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Complex F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace Complex G]

variable [CompleteSpace E] [CompleteSpace F]

/--
theorem `integral_bilin_fourier_eq` / 定理 `integral_bilin_fourier_eq`

English:
theorem integral_bilin_fourier_eq
  given: (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L[Complex] F ->L[Complex] G)
  proof: by
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip M (L := innerₗ V)
    continuous_fourierChar continuous_inner f.integrable g.integrable

中文:
定理 integral_bilin_fourier_eq
  条件: (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L[复形] F ->L[复形] G)
  证明: by
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip M (L := innerₗ V)
    continuous_fourierChar continuous_inner f.integrable g.integrable

Depends on / 依赖: VectorFourier, VectorFourier.integral_bilin_fourierIntegral_eq_flip, continuous_fourierChar, continuous_inner, f.integrable, g.integrable, integrable, integral_bilin_fourierIntegral_eq_flip
-/
theorem integral_bilin_fourier_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L[Complex] F ->L[Complex] G) :
    ∫ ξ, M (𝓕 f ξ) (g ξ) = ∫ x, M (f x) (𝓕 g x) := by
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip M (L := innerₗ V)
    continuous_fourierChar continuous_inner f.integrable g.integrable

/--
theorem `integral_fourier_smul_eq` / 定理 `integral_fourier_smul_eq`

English:
theorem integral_fourier_smul_eq
  given: (f : 𝓢(V, Complex)) (g : 𝓢(V, F))
  proof: integral_bilin_fourier_eq f g (.lsmul Complex Complex)

中文:
定理 integral_fourier_smul_eq
  条件: (f : 𝓢(V, 复形)) (g : 𝓢(V, F))
  证明: integral_bilin_fourier_eq f g (.lsmul Complex Complex)

Depends on / 依赖: integral_bilin_fourier_eq
-/
theorem integral_fourier_smul_eq (f : 𝓢(V, Complex)) (g : 𝓢(V, F)) :
    ∫ ξ, 𝓕 f ξ • g ξ = ∫ x, f x • 𝓕 g x :=
  integral_bilin_fourier_eq f g (.lsmul Complex Complex)

/--
theorem `integral_fourier_mul_eq` / 定理 `integral_fourier_mul_eq`

English:
theorem integral_fourier_mul_eq
  given: (f : 𝓢(V, Complex)) (g : 𝓢(V, Complex))
  proof: integral_bilin_fourier_eq f g (.mul Complex Complex)

中文:
定理 integral_fourier_mul_eq
  条件: (f : 𝓢(V, 复形)) (g : 𝓢(V, 复形))
  证明: integral_bilin_fourier_eq f g (.mul Complex Complex)

Depends on / 依赖: integral_bilin_fourier_eq
-/
theorem integral_fourier_mul_eq (f : 𝓢(V, Complex)) (g : 𝓢(V, Complex)) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x :=
  integral_bilin_fourier_eq f g (.mul Complex Complex)

/--
theorem `integral_bilin_fourierInv_eq` / 定理 `integral_bilin_fourierInv_eq`

English:
theorem integral_bilin_fourierInv_eq
  given: (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L[Complex] F ->L[Complex] G)
  proof: by
  convert! (integral_bilin_fourier_eq (𝓕⁻ f) (𝓕⁻ g) M).symm
  · exact (FourierTransform.fourier_fourierInv_eq g).symm
  · exact (FourierTransform.fourier_fourierInv_eq f).symm

中文:
定理 integral_bilin_fourierInv_eq
  条件: (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L[复形] F ->L[复形] G)
  证明: by
  convert! (integral_bilin_fourier_eq (𝓕⁻ f) (𝓕⁻ g) M).symm
  · exact (FourierTransform.fourier_fourierInv_eq g).symm
  · exact (FourierTransform.fourier_fourierInv_eq f).symm

Depends on / 依赖: FourierTransform, FourierTransform.fourier_fourierInv_eq, convert, fourier_fourierInv_eq, integral_bilin_fourier_eq
-/
theorem integral_bilin_fourierInv_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L[Complex] F ->L[Complex] G) :
    ∫ ξ, M (𝓕⁻ f ξ) (g ξ) = ∫ x, M (f x) (𝓕⁻ g x) := by
  convert! (integral_bilin_fourier_eq (𝓕⁻ f) (𝓕⁻ g) M).symm
  · exact (FourierTransform.fourier_fourierInv_eq g).symm
  · exact (FourierTransform.fourier_fourierInv_eq f).symm

/--
theorem `integral_fourierInv_smul_eq` / 定理 `integral_fourierInv_smul_eq`

English:
theorem integral_fourierInv_smul_eq
  given: (f : 𝓢(V, Complex)) (g : 𝓢(V, F))
  proof: integral_bilin_fourierInv_eq f g (.lsmul Complex Complex)

中文:
定理 integral_fourierInv_smul_eq
  条件: (f : 𝓢(V, 复形)) (g : 𝓢(V, F))
  证明: integral_bilin_fourierInv_eq f g (.lsmul Complex Complex)

Depends on / 依赖: integral_bilin_fourierInv_eq
-/
theorem integral_fourierInv_smul_eq (f : 𝓢(V, Complex)) (g : 𝓢(V, F)) :
    ∫ ξ, 𝓕⁻ f ξ • g ξ = ∫ x, f x • 𝓕⁻ g x :=
  integral_bilin_fourierInv_eq f g (.lsmul Complex Complex)

/--
theorem `integral_fourierInv_mul_eq` / 定理 `integral_fourierInv_mul_eq`

English:
theorem integral_fourierInv_mul_eq
  given: (f : 𝓢(V, Complex)) (g : 𝓢(V, Complex))
  proof: integral_bilin_fourierInv_eq f g (.mul Complex Complex)

中文:
定理 integral_fourierInv_mul_eq
  条件: (f : 𝓢(V, 复形)) (g : 𝓢(V, 复形))
  证明: integral_bilin_fourierInv_eq f g (.mul Complex Complex)

Depends on / 依赖: integral_bilin_fourierInv_eq
-/
theorem integral_fourierInv_mul_eq (f : 𝓢(V, Complex)) (g : 𝓢(V, Complex)) :
    ∫ ξ, 𝓕⁻ f ξ * g ξ = ∫ x, f x * 𝓕⁻ g x :=
  integral_bilin_fourierInv_eq f g (.mul Complex Complex)

/--
theorem `integral_sesq_fourier_eq` / 定理 `integral_sesq_fourier_eq`

English:
theorem integral_sesq_fourier_eq
  given: (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L⋆[Complex] F ->L[Complex] G)
  proof: by
  simpa [fourierInv_coe] using! VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip M
    (L := innerₗ V) continuous_fourierChar continuous_inner f.integrable g.integrable

中文:
定理 integral_sesq_fourier_eq
  条件: (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L⋆[复形] F ->L[复形] G)
  证明: by
  simpa [fourierInv_coe] using! VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip M
    (L := innerₗ V) continuous_fourierChar continuous_inner f.integrable g.integrable

Depends on / 依赖: VectorFourier, VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip, continuous_fourierChar, continuous_inner, f.integrable, fourierInv_coe, g.integrable, integrable, integral_sesq_fourierIntegral_eq_neg_flip
-/
theorem integral_sesq_fourier_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L⋆[Complex] F ->L[Complex] G) :
    ∫ ξ, M (𝓕 f ξ) (g ξ) = ∫ x, M (f x) (𝓕⁻ g x) := by
  simpa [fourierInv_coe] using! VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip M
    (L := innerₗ V) continuous_fourierChar continuous_inner f.integrable g.integrable

/--
theorem `integral_sesq_fourier_fourier` / 定理 `integral_sesq_fourier_fourier`

English:
theorem integral_sesq_fourier_fourier
  given: (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L⋆[Complex] F ->L[Complex] G)
  proof: by
  simpa using integral_sesq_fourier_eq f (𝓕 g) M

中文:
定理 integral_sesq_fourier_fourier
  条件: (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L⋆[复形] F ->L[复形] G)
  证明: by
  simpa using integral_sesq_fourier_eq f (𝓕 g) M

Depends on / 依赖: integral_sesq_fourier_eq
-/
theorem integral_sesq_fourier_fourier (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E ->L⋆[Complex] F ->L[Complex] G) :
    ∫ ξ, M (𝓕 f ξ) (𝓕 g ξ) = ∫ x, M (f x) (g x) := by
  simpa using integral_sesq_fourier_eq f (𝓕 g) M

end fubini

section L1

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Complex F]

/--
theorem `norm_fourier_apply_le_toLp_one` / 定理 `norm_fourier_apply_le_toLp_one`

English:
theorem norm_fourier_apply_le_toLp_one
  given: (f : 𝓢(V, F)) (x : V)
  proof: calc
  _ = ‖∫ (v : V), 𝐞 (-inner Real v x) • f v‖ := by rw [fourier_coe, Real.fourier_eq]
  _ <= ∫ (v : V), ‖𝐞 (-inner Real v x) • f v‖ := norm_integral_le_integral_norm _
  _ = _ := by simp [norm_toLp_one]

中文:
定理 norm_fourier_apply_le_toLp_one
  条件: (f : 𝓢(V, F)) (x : V)
  证明: calc
  _ = ‖∫ (v : V), 𝐞 (-inner Real v x) • f v‖ := by rw [fourier_coe, Real.fourier_eq]
  _ <= ∫ (v : V), ‖𝐞 (-inner Real v x) • f v‖ := norm_integral_le_integral_norm _
  _ = _ := by simp [norm_toLp_one]
-/
theorem norm_fourier_apply_le_toLp_one (f : 𝓢(V, F)) (x : V) :
    ‖𝓕 f x‖ <= ‖f.toLp 1‖ := calc
  _ = ‖∫ (v : V), 𝐞 (-inner Real v x) • f v‖ := by rw [fourier_coe, Real.fourier_eq]
  _ <= ∫ (v : V), ‖𝐞 (-inner Real v x) • f v‖ := norm_integral_le_integral_norm _
  _ = _ := by simp [norm_toLp_one]

/--
theorem `norm_fourier_toBoundedContinuousFunction_le_toLp_one` / 定理 `norm_fourier_toBoundedContinuousFunction_le_toLp_one`

English:
theorem norm_fourier_toBoundedContinuousFunction_le_toLp_one
  given: (f : 𝓢(V, F))
  proof: by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  simpa using norm_fourier_apply_le_toLp_one f

中文:
定理 norm_fourier_toBoundedContinuousFunction_le_toLp_one
  条件: (f : 𝓢(V, F))
  证明: by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  simpa using norm_fourier_apply_le_toLp_one f

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.norm_le, norm_fourier_apply_le_toLp_one, norm_le
-/
theorem norm_fourier_toBoundedContinuousFunction_le_toLp_one (f : 𝓢(V, F)) :
    ‖(𝓕 f).toBoundedContinuousFunction‖ <= ‖f.toLp 1‖ := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  simpa using norm_fourier_apply_le_toLp_one f

/--
theorem `norm_fourier_Lp_top_leq_toLp_one` / 定理 `norm_fourier_Lp_top_leq_toLp_one`

English:
theorem norm_fourier_Lp_top_leq_toLp_one
  given: (f : 𝓢(V, F))
  proof: norm_toLp_top_le.trans (seminorm_le_bound Real 0 0 _ (by positivity)
    (by simpa using norm_fourier_apply_le_toLp_one f))

中文:
定理 norm_fourier_Lp_top_leq_toLp_one
  条件: (f : 𝓢(V, F))
  证明: norm_toLp_top_le.trans (seminorm_le_bound Real 0 0 _ (by positivity)
    (by simpa using norm_fourier_apply_le_toLp_one f))

Depends on / 依赖: norm_fourier_apply_le_toLp_one, norm_toLp_top_le, norm_toLp_top_le.trans, seminorm_le_bound
-/
theorem norm_fourier_Lp_top_leq_toLp_one (f : 𝓢(V, F)) :
    ‖(𝓕 f).toLp ⊤‖ <= ‖f.toLp 1‖ :=
  norm_toLp_top_le.trans (seminorm_le_bound Real 0 0 _ (by positivity)
    (by simpa using norm_fourier_apply_le_toLp_one f))

end L1

section L2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H] [CompleteSpace H]

/--
theorem `integral_inner_fourier_fourier` / 定理 `integral_inner_fourier_fourier`

English:
theorem integral_inner_fourier_fourier
  given: (f g : 𝓢(V, H))
  proof: integral_sesq_fourier_fourier f g (innerSL Complex)

中文:
定理 integral_inner_fourier_fourier
  条件: (f g : 𝓢(V, H))
  证明: integral_sesq_fourier_fourier f g (innerSL Complex)
-/
@[simp] theorem integral_inner_fourier_fourier (f g : 𝓢(V, H)) :
    ∫ ξ, ⟪𝓕 f ξ, 𝓕 g ξ⟫ = ∫ x, ⟪f x, g x⟫ :=
  integral_sesq_fourier_fourier f g (innerSL Complex)

/--
theorem `integral_norm_sq_fourier` / 定理 `integral_norm_sq_fourier`

English:
theorem integral_norm_sq_fourier
  given: (f : 𝓢(V, H))
  proof: by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    integral_inner_fourier_fourier f f

中文:
定理 integral_norm_sq_fourier
  条件: (f : 𝓢(V, H))
  证明: by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    integral_inner_fourier_fourier f f

Depends on / 依赖: Complex.ofRealLI.injective, LinearIsometry, LinearIsometry.integral_comp_comm, injective, inner_self_eq_norm_sq_to_K, integral_comp_comm, integral_inner_fourier_fourier, ofRealLI
-/
theorem integral_norm_sq_fourier (f : 𝓢(V, H)) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    integral_inner_fourier_fourier f f

/--
theorem `inner_fourier_toL2_eq` / 定理 `inner_fourier_toL2_eq`

English:
theorem inner_fourier_toL2_eq
  given: (f g : 𝓢(V, H))
  proof: by simp

中文:
定理 inner_fourier_toL2_eq
  条件: (f g : 𝓢(V, H))
  证明: by simp
-/
theorem inner_fourier_toL2_eq (f g : 𝓢(V, H)) :
    ⟪(𝓕 f).toLp 2, (𝓕 g).toLp 2⟫ = ⟪f.toLp 2, g.toLp 2⟫ := by simp

/--
theorem `norm_fourier_toL2_eq` / 定理 `norm_fourier_toL2_eq`

English:
theorem norm_fourier_toL2_eq
  given: (f : 𝓢(V, H))
  proof: by
  simp_rw [norm_eq_sqrt_re_inner (𝕜 := Complex), inner_fourier_toL2_eq]

中文:
定理 norm_fourier_toL2_eq
  条件: (f : 𝓢(V, H))
  证明: by
  simp_rw [norm_eq_sqrt_re_inner (𝕜 := Complex), inner_fourier_toL2_eq]
-/
@[simp] theorem norm_fourier_toL2_eq (f : 𝓢(V, H)) :
    ‖(𝓕 f).toLp 2‖ = ‖f.toLp 2‖ := by
  simp_rw [norm_eq_sqrt_re_inner (𝕜 := Complex), inner_fourier_toL2_eq]

end L2

end SchwartzMap
