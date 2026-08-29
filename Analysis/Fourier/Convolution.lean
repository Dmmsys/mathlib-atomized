/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # The Fourier transform of the convolution

In this file we calculate the Fourier transform of a convolution.

## Main definitions
* `SchwartzMap.convolution`: The convolution on Schwartz functions is defined via the Fourier
  transform.

## Main statements
* `Real.fourier_bilin_convolution_eq`: The Fourier transform of a convolution is the bilinear map
  applied to the Fourier transform of the functions.
* `Real.fourier_smul_convolution_eq`: Variant for scalar multiplication.
* `Real.fourier_mul_convolution_eq`: Variant for multiplication.
* `SchwartzMap.fourier_convolution`: The Fourier transform of the Schwartz convolution is given by
  the pairing of the Fourier transformed Schwartz functions.
* `SchwartzMap.convolution_apply`: The Schwartz function convolution coincides with the convolution
  for functions.

-/

@[expose] public section

variable {𝕜 R E F F₁ F₂ F₃ : Type*}

namespace Real

open MeasureTheory Convolution

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F₁] [NormedAddCommGroup F₂] [NormedAddCommGroup F₃]
  [InnerProductSpace Real E] [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace 𝕜 F₁] [NormedSpace 𝕜 F₂] [NormedSpace 𝕜 F₃]

/--
theorem `integrable_prod_sub` / 定理 `integrable_prod_sub`

English:
theorem integrable_prod_sub
  statement: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {f₁ : E -> F₁} {f₂ : E -> F₂}
  proof: by
  simpa [mul_comm] using (hf₂.norm.convolution_integrand (.mul Real Real) hf₁.norm).const_mul ‖B‖

中文:
定理 integrable_prod_sub
  结论: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {f₁ : E -> F₁} {f₂ : E -> F₂}
  证明: by
  simpa [mul_comm] using (hf₂.norm.convolution_integrand (.mul Real Real) hf₁.norm).const_mul ‖B‖

Depends on / 依赖: const_mul, convolution_integrand, mul_comm, norm.convolution_integrand
-/
theorem integrable_prod_sub (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {f₁ : E -> F₁} {f₂ : E -> F₂}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) :
    Integrable (fun (p : E × E) => ‖B‖ * (‖f₁ (p.1 - p.2)‖ * ‖f₂ p.2‖)) (volume.prod volume) := by
  simpa [mul_comm] using (hf₂.norm.convolution_integrand (.mul Real Real) hf₁.norm).const_mul ‖B‖

open FourierTransform

variable [NormedSpace Complex F₃]

/--
theorem `fourier_bilin_convolution_eq_integral` / 定理 `fourier_bilin_convolution_eq_integral`

English:
theorem fourier_bilin_convolution_eq_integral
  statement: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {f₁ : E -> F₁} {f₂ : E -> F₂}
  proof: calc
  _ = 𝓕 (f₂ ⋆[B.flip] f₁) ξ := by
    rw [convolution_flip]
  _ = ∫ x, 𝐞 (-inner Real x ξ) • ∫ y, B (f₁ (x - y)) (f₂ y) := by rfl
  _ = ∫ x, ∫ y, 𝐞 (-inner Real x ξ) • B (f₁ (x - y)) (f₂ y) := by
    congr
    ext x
    simp_rw [Circle.smul_def, integral_smul]
  _ = ∫ y, ∫ x, 𝐞 (-inner Real x ξ) • B (f₁ (x - y)) (f₂ y) := by
    refine integral_integral_swap ?_
    have hB := hf₂.convolution_integrand B.flip hf₁
    refine hB.mono ?_ ?_
.aestronglyMeasurable.smul · exact continuous_fourierChar.comp (by fun_prop)
        hB.aestronglyMeasurable
    · filter_upwards with ⟨x, y⟩ using by simp
  _ = ∫ y, ∫ x, 𝐞 (-inner Real (y + x) ξ) • B (f₁ x) (f₂ y) := by
    congr
    ext y
    -- Linear change of variables
    convert! integral_sub_right_eq_self _ y (μ := volume)
    congr
    simp

中文:
定理 fourier_bilin_convolution_eq_integral
  结论: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {f₁ : E -> F₁} {f₂ : E -> F₂}
  证明: calc
  _ = 𝓕 (f₂ ⋆[B.flip] f₁) ξ := by
    rw [convolution_flip]
  _ = ∫ x, 𝐞 (-inner Real x ξ) • ∫ y, B (f₁ (x - y)) (f₂ y) := by rfl
  _ = ∫ x, ∫ y, 𝐞 (-inner Real x ξ) • B (f₁ (x - y)) (f₂ y) := by
    congr
    ext x
    simp_rw [Circle.smul_def, integral_smul]
  _ = ∫ y, ∫ x, 𝐞 (-inner Real x ξ) • B (f₁ (x - y)) (f₂ y) := by
    refine integral_integral_swap ?_
    have hB := hf₂.convolution_integrand B.flip hf₁
    refine hB.mono ?_ ?_
.aestronglyMeasurable.smul · exact continuous_fourierChar.comp (by fun_prop)
        hB.aestronglyMeasurable
    · filter_upwards with ⟨x, y⟩ using by simp
  _ = ∫ y, ∫ x, 𝐞 (-inner Real (y + x) ξ) • B (f₁ x) (f₂ y) := by
    congr
    ext y
    -- Linear change of variables
    convert! integral_sub_right_eq_self _ y (μ := volume)
    congr
    simp
-/
theorem fourier_bilin_convolution_eq_integral (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) {f₁ : E -> F₁} {f₂ : E -> F₂}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (ξ : E) :
    𝓕 (f₁ ⋆[B] f₂) ξ = ∫ y, ∫ x, 𝐞 (-inner Real (y + x) ξ) • B (f₁ x) (f₂ y) := calc
  _ = 𝓕 (f₂ ⋆[B.flip] f₁) ξ := by
    rw [convolution_flip]
  _ = ∫ x, 𝐞 (-inner Real x ξ) • ∫ y, B (f₁ (x - y)) (f₂ y) := by rfl
  _ = ∫ x, ∫ y, 𝐞 (-inner Real x ξ) • B (f₁ (x - y)) (f₂ y) := by
    congr
    ext x
    simp_rw [Circle.smul_def, integral_smul]
  _ = ∫ y, ∫ x, 𝐞 (-inner Real x ξ) • B (f₁ (x - y)) (f₂ y) := by
    refine integral_integral_swap ?_
    have hB := hf₂.convolution_integrand B.flip hf₁
    refine hB.mono ?_ ?_
.aestronglyMeasurable.smul · exact continuous_fourierChar.comp (by fun_prop)
        hB.aestronglyMeasurable
    · filter_upwards with ⟨x, y⟩ using by simp
  _ = ∫ y, ∫ x, 𝐞 (-inner Real (y + x) ξ) • B (f₁ x) (f₂ y) := by
    congr
    ext y
    -- Linear change of variables
    convert! integral_sub_right_eq_self _ y (μ := volume)
    congr
    simp

variable [CompleteSpace F₁] [CompleteSpace F₂] [CompleteSpace F₃]
  [NormedSpace Complex F₁] [NormedSpace Complex F₂]

open ContinuousLinearMap

/--
theorem `fourier_bilin_convolution_eq` / 定理 `fourier_bilin_convolution_eq`

English:
theorem fourier_bilin_convolution_eq
  statement: (B : F₁ ->L[Complex] F₂ ->L[Complex] F₃) {f₁ : E -> F₁} {f₂ : E -> F₂}
  proof: calc
  _ = ∫ y, ∫ x, 𝐞 (-inner Real (y + x) ξ) • B (f₁ x) (f₂ y) :=
    fourier_bilin_convolution_eq_integral B hf₁ hf₂ _
  _ = ∫ y, ∫ x, 𝐞 (-inner Real y ξ) • 𝐞 (-inner Real x ξ) • B (f₁ x) (f₂ y) := by
    simp_rw [inner_add_left, neg_add, AddChar.map_add_eq_mul, smul_smul]
  _ = ∫ y, (∫ x, B (𝐞 (-inner Real x ξ) • f₁ x)) (𝐞 (-inner Real y ξ) • f₂ y) := by
    congr with y
    have : Integrable (fun x => (𝐞 (-inner Real x ξ) : Complex) • B (f₁ x)) volume := by
      simpa [Circle.smul_def] using
        (Real.fourierIntegral_convergent_iff ξ).2 (B.integrable_comp hf₁)
    simp [Circle.smul_def, MeasureTheory.integral_smul, integral_apply this (f₂ y)]
  _ = B (∫ x, 𝐞 (-inner Real x ξ) • f₁ x) (∫ y, 𝐞 (-inner Real y ξ) • f₂ y) := by
    rw [← integral_comp_comm _ (by simpa using hf₂)]; rw [← integral_comp_comm _ (by simpa using hf₁)]

中文:
定理 fourier_bilin_convolution_eq
  结论: (B : F₁ ->L[复形] F₂ ->L[复形] F₃) {f₁ : E -> F₁} {f₂ : E -> F₂}
  证明: calc
  _ = ∫ y, ∫ x, 𝐞 (-inner Real (y + x) ξ) • B (f₁ x) (f₂ y) :=
    fourier_bilin_convolution_eq_integral B hf₁ hf₂ _
  _ = ∫ y, ∫ x, 𝐞 (-inner Real y ξ) • 𝐞 (-inner Real x ξ) • B (f₁ x) (f₂ y) := by
    simp_rw [inner_add_left, neg_add, AddChar.map_add_eq_mul, smul_smul]
  _ = ∫ y, (∫ x, B (𝐞 (-inner Real x ξ) • f₁ x)) (𝐞 (-inner Real y ξ) • f₂ y) := by
    congr with y
    have : Integrable (fun x => (𝐞 (-inner Real x ξ) : Complex) • B (f₁ x)) volume := by
      simpa [Circle.smul_def] using
        (Real.fourierIntegral_convergent_iff ξ).2 (B.integrable_comp hf₁)
    simp [Circle.smul_def, MeasureTheory.integral_smul, integral_apply this (f₂ y)]
  _ = B (∫ x, 𝐞 (-inner Real x ξ) • f₁ x) (∫ y, 𝐞 (-inner Real y ξ) • f₂ y) := by
    rw [← integral_comp_comm _ (by simpa using hf₂)]; rw [← integral_comp_comm _ (by simpa using hf₁)]
-/
theorem fourier_bilin_convolution_eq (B : F₁ ->L[Complex] F₂ ->L[Complex] F₃) {f₁ : E -> F₁} {f₂ : E -> F₂}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (ξ : E) :
    𝓕 (f₁ ⋆[B] f₂) ξ = B (𝓕 f₁ ξ) (𝓕 f₂ ξ) := calc
  _ = ∫ y, ∫ x, 𝐞 (-inner Real (y + x) ξ) • B (f₁ x) (f₂ y) :=
    fourier_bilin_convolution_eq_integral B hf₁ hf₂ _
  _ = ∫ y, ∫ x, 𝐞 (-inner Real y ξ) • 𝐞 (-inner Real x ξ) • B (f₁ x) (f₂ y) := by
    simp_rw [inner_add_left, neg_add, AddChar.map_add_eq_mul, smul_smul]
  _ = ∫ y, (∫ x, B (𝐞 (-inner Real x ξ) • f₁ x)) (𝐞 (-inner Real y ξ) • f₂ y) := by
    congr with y
    have : Integrable (fun x => (𝐞 (-inner Real x ξ) : Complex) • B (f₁ x)) volume := by
      simpa [Circle.smul_def] using
        (Real.fourierIntegral_convergent_iff ξ).2 (B.integrable_comp hf₁)
    simp [Circle.smul_def, MeasureTheory.integral_smul, integral_apply this (f₂ y)]
  _ = B (∫ x, 𝐞 (-inner Real x ξ) • f₁ x) (∫ y, 𝐞 (-inner Real y ξ) • f₂ y) := by
    rw [← integral_comp_comm _ (by simpa using hf₂)]; rw [← integral_comp_comm _ (by simpa using hf₁)]

/--
theorem `fourier_smul_convolution_eq` / 定理 `fourier_smul_convolution_eq`

English:
theorem fourier_smul_convolution_eq
  statement: {f₁ : E -> Complex} {f₂ : E -> F₁}
  proof: fourier_bilin_convolution_eq (lsmul Complex Complex) hf₁ hf₂ ξ

中文:
定理 fourier_smul_convolution_eq
  结论: {f₁ : E -> 复形} {f₂ : E -> F₁}
  证明: fourier_bilin_convolution_eq (lsmul Complex Complex) hf₁ hf₂ ξ

Depends on / 依赖: fourier_bilin_convolution_eq
-/
theorem fourier_smul_convolution_eq {f₁ : E -> Complex} {f₂ : E -> F₁}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (ξ : E) :
    𝓕 (f₁ ⋆[lsmul Complex Complex] f₂) ξ = (𝓕 f₁ ξ) • (𝓕 f₂ ξ) :=
  fourier_bilin_convolution_eq (lsmul Complex Complex) hf₁ hf₂ ξ

variable [NormedRing R] [NormedSpace Complex R] [IsScalarTower Complex R R] [SMulCommClass Complex R R]
  [CompleteSpace R]

/--
theorem `fourier_mul_convolution_eq` / 定理 `fourier_mul_convolution_eq`

English:
theorem fourier_mul_convolution_eq
  statement: {f₁ : E -> R} {f₂ : E -> R}
  proof: fourier_bilin_convolution_eq (mul Complex R) hf₁ hf₂ ξ

中文:
定理 fourier_mul_convolution_eq
  结论: {f₁ : E -> R} {f₂ : E -> R}
  证明: fourier_bilin_convolution_eq (mul Complex R) hf₁ hf₂ ξ

Depends on / 依赖: fourier_bilin_convolution_eq
-/
theorem fourier_mul_convolution_eq {f₁ : E -> R} {f₂ : E -> R}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (ξ : E) :
    𝓕 (f₁ ⋆[mul Complex R] f₂) ξ = (𝓕 f₁ ξ) * (𝓕 f₂ ξ) :=
  fourier_bilin_convolution_eq (mul Complex R) hf₁ hf₂ ξ

end Real

namespace SchwartzMap

variable [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E] [MeasurableSpace E]
  [BorelSpace E]
  [NormedAddCommGroup F₁] [NormedSpace Complex F₁] [NormedSpace 𝕜 F₁] [SMulCommClass Complex 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace Complex F₂] [NormedSpace 𝕜 F₂] [SMulCommClass Complex 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace Complex F₃] [NormedSpace 𝕜 F₃] [SMulCommClass Complex 𝕜 F₃]

open FourierTransform Convolution

/-- The bilinear convolution of Schwartz functions.

The continuity in the left argument is provided in `SchwartzMap.convolution_continuous_left`. -/
noncomputable
/--
Definition of `convolution` / `convolution` 的定义

English:
definition convolution
  signature: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃)
  body: fourierInvCLM 𝕜 𝓢(E, F₃) ∘L pairing B (𝓕 f) ∘L fourierCLM 𝕜 𝓢(E, F₂)
  map_add' := by simp [FourierTransform.fourier_add]
  map_smul' := by simp [FourierTransform.fourier_smul]

@[simp]

中文:
定义 convolution
  签名: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃)
  定义体: fourierInvCLM 𝕜 𝓢(E, F₃) ∘L pairing B (𝓕 f) ∘L fourierCLM 𝕜 𝓢(E, F₂)
  map_add' := by simp [FourierTransform.fourier_add]
  map_smul' := by simp [FourierTransform.fourier_smul]

@[simp]

Depends on / 依赖: fourierCLM, fourierInvCLM, pairing
-/
def convolution (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) : 𝓢(E, F₁) ->ₗ[𝕜] 𝓢(E, F₂) ->L[𝕜] 𝓢(E, F₃) where
  toFun f := fourierInvCLM 𝕜 𝓢(E, F₃) ∘L pairing B (𝓕 f) ∘L fourierCLM 𝕜 𝓢(E, F₂)
  map_add' := by simp [FourierTransform.fourier_add]
  map_smul' := by simp [FourierTransform.fourier_smul]

@[simp]
/--
theorem `convolution_flip` / 定理 `convolution_flip`

English:
theorem convolution_flip
  given: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂))
  proof: rfl

中文:
定理 convolution_flip
  条件: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂))
  证明: rfl
-/
theorem convolution_flip (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) :
    convolution B.flip g f = convolution B f g := rfl

/-- The convolution is continuous in the left argument.

Note that since `𝓢(E, F)` is not a normed space, uncurried and curried continuity do not
coincide. -/
@[fun_prop]
/--
theorem `convolution_continuous_left` / 定理 `convolution_continuous_left`

English:
theorem convolution_continuous_left
  given: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (g : 𝓢(E, F₂))
  proof: (convolution B.flip g).continuous

中文:
定理 convolution_continuous_left
  条件: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (g : 𝓢(E, F₂))
  证明: (convolution B.flip g).continuous

Depends on / 依赖: B.flip, continuous, convolution
-/
theorem convolution_continuous_left (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (g : 𝓢(E, F₂)) :
    Continuous (convolution B · g) := (convolution B.flip g).continuous

variable [CompleteSpace F₃]

/--
theorem `fourier_convolution` / 定理 `fourier_convolution`

English:
theorem fourier_convolution
  given: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂))
  proof: by simp [convolution]

中文:
定理 fourier_convolution
  条件: (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂))
  证明: by simp [convolution]

Depends on / 依赖: SeminormedGroup, convolution, seminormedGroup
-/
theorem fourier_convolution (B : F₁ ->L[𝕜] F₂ ->L[𝕜] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) :
    𝓕 (convolution B f g) = pairing B (𝓕 f) (𝓕 g) := by simp [convolution]

variable [CompleteSpace F₁] [CompleteSpace F₂]

open MeasureTheory

/--
theorem `fourier_convolution_apply` / 定理 `fourier_convolution_apply`

English:
theorem fourier_convolution_apply
  given: (B : F₁ ->L[Complex] F₂ ->L[Complex] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) (x : E)
  proof: by
  simp [fourier_convolution, fourier_coe,
    Real.fourier_bilin_convolution_eq B f.integrable g.integrable]

中文:
定理 fourier_convolution_apply
  条件: (B : F₁ ->L[复形] F₂ ->L[复形] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) (x : E)
  证明: by
  simp [fourier_convolution, fourier_coe,
    Real.fourier_bilin_convolution_eq B f.integrable g.integrable]

Depends on / 依赖: Real.fourier_bilin_convolution_eq, f.integrable, fourier_bilin_convolution_eq, fourier_coe, fourier_convolution, g.integrable, integrable
-/
theorem fourier_convolution_apply (B : F₁ ->L[Complex] F₂ ->L[Complex] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) (x : E) :
    𝓕 (convolution B f g) x = 𝓕 (f ⋆[B] g) x := by
  simp [fourier_convolution, fourier_coe,
    Real.fourier_bilin_convolution_eq B f.integrable g.integrable]

/--
theorem `convolution_apply` / 定理 `convolution_apply`

English:
theorem convolution_apply
  given: (B : F₁ ->L[Complex] F₂ ->L[Complex] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) (x : E)
  proof: calc
  _ = 𝓕⁻ (𝓕 (convolution B f g)) x := by simp
  _ = 𝓕⁻ (fun y => 𝓕 (f ⋆[B] g) y) x := by
    rw [fourierInv_coe]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [fourier_convolution_apply]
  _ = _ := by
    rw [Continuous.fourierInv_fourier_eq]
    · refine BddAbove.continuous_convolution_right_of_integrable B ?_ f.integrable g.continuous
      exact ⟨SchwartzMap.seminorm Real 0 0 g, fun x ⟨y, hy⟩ => hy ▸ norm_le_seminorm Real g y⟩
    · exact f.integrable.integrable_convolution B g.integrable
    · have : Integrable (fun ξ => B (𝓕 f ξ) (𝓕 g ξ)) volume := (pairing B (𝓕 f) (𝓕 g)).integrable
      convert! this
      rw [← fourier_convolution_apply B f g]; rw [fourier_convolution]; rw [pairing_apply_apply]

中文:
定理 convolution_apply
  条件: (B : F₁ ->L[复形] F₂ ->L[复形] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) (x : E)
  证明: calc
  _ = 𝓕⁻ (𝓕 (convolution B f g)) x := by simp
  _ = 𝓕⁻ (fun y => 𝓕 (f ⋆[B] g) y) x := by
    rw [fourierInv_coe]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [fourier_convolution_apply]
  _ = _ := by
    rw [Continuous.fourierInv_fourier_eq]
    · refine BddAbove.continuous_convolution_right_of_integrable B ?_ f.integrable g.continuous
      exact ⟨SchwartzMap.seminorm Real 0 0 g, fun x ⟨y, hy⟩ => hy ▸ norm_le_seminorm Real g y⟩
    · exact f.integrable.integrable_convolution B g.integrable
    · have : Integrable (fun ξ => B (𝓕 f ξ) (𝓕 g ξ)) volume := (pairing B (𝓕 f) (𝓕 g)).integrable
      convert! this
      rw [← fourier_convolution_apply B f g]; rw [fourier_convolution]; rw [pairing_apply_apply]

Depends on / 依赖: SeminormedCommGroup, SetLike, seminormedCommGroup
-/
theorem convolution_apply (B : F₁ ->L[Complex] F₂ ->L[Complex] F₃) (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂)) (x : E) :
    convolution B f g x = (f ⋆[B] g) x := calc
  _ = 𝓕⁻ (𝓕 (convolution B f g)) x := by simp
  _ = 𝓕⁻ (fun y => 𝓕 (f ⋆[B] g) y) x := by
    rw [fourierInv_coe]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [fourier_convolution_apply]
  _ = _ := by
    rw [Continuous.fourierInv_fourier_eq]
    · refine BddAbove.continuous_convolution_right_of_integrable B ?_ f.integrable g.continuous
      exact ⟨SchwartzMap.seminorm Real 0 0 g, fun x ⟨y, hy⟩ => hy ▸ norm_le_seminorm Real g y⟩
    · exact f.integrable.integrable_convolution B g.integrable
    · have : Integrable (fun ξ => B (𝓕 f ξ) (𝓕 g ξ)) volume := (pairing B (𝓕 f) (𝓕 g)).integrable
      convert! this
      rw [← fourier_convolution_apply B f g]; rw [fourier_convolution]; rw [pairing_apply_apply]


end SchwartzMap
