/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Normed.Operator.Extend

/-!

# The Fourier transform on $L^p$

In this file we define the Fourier transform on $L^2$ as a linear isometry equivalence.

## Main definitions

* `MeasureTheory.Lp.fourierTransformₗᵢ`: The Fourier transform on $L^2$ as a linear isometry
  equivalence.

## Main statements

* `SchwartzMap.toLp_fourier_eq`: The Fourier transform on `𝓢(E, F)` agrees with the Fourier
  transform on $L^2$.
* `MeasureTheory.Lp.fourier_toTemperedDistribution_eq`: The Fourier transform on $L^2$ agrees with
  the Fourier transform on `𝓢'(E, F)`.

-/

@[expose] public section

noncomputable section

section FourierTransform

variable {E F : Type*}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace Complex F] [CompleteSpace F]

open SchwartzMap MeasureTheory FourierTransform ComplexInnerProductSpace

variable [InnerProductSpace Real E] [FiniteDimensional Real E]

namespace MeasureTheory.Lp

variable (E F) in
/-- The Fourier transform on `L2` as a linear isometry equivalence. -/
@[wikidata Q6520159]
/--
Definition of `fourierTransformₗᵢ` / `fourierTransformₗᵢ` 的定义

English:
definition fourierTransformₗᵢ
  signature: : (Lp (α := E) F 2) ≃ₗᵢ[Complex] (Lp (α := E) F 2)
  body: (fourierEquiv Complex 𝓢(E, F)).extendOfIsometry
    (toLpCLM Complex (E := E) F 2 volume) (toLpCLM Complex (E := E) F 2 volume)
    -- Not explicitly stating the measure as being the volume causes time-outs in the proofs below
    (denseRange_toLpCLM ENNReal.ofNat_ne_top) (denseRange_toLpCLM ENNReal

中文:
定义 fourierTransformₗᵢ
  签名: : (Lp (α := E) F 2) ≃ₗᵢ[复形] (Lp (α := E) F 2)
  定义体: (fourierEquiv Complex 𝓢(E, F)).extendOfIsometry
    (toLpCLM Complex (E := E) F 2 volume) (toLpCLM Complex (E := E) F 2 volume)
    -- Not explicitly stating the measure as being the volume causes time-outs in the proofs below
    (denseRange_toLpCLM ENNReal.ofNat_ne_top) (denseRange_toLpCLM ENNReal
-/
def fourierTransformₗᵢ : (Lp (α := E) F 2) ≃ₗᵢ[Complex] (Lp (α := E) F 2) :=
  (fourierEquiv Complex 𝓢(E, F)).extendOfIsometry
    (toLpCLM Complex (E := E) F 2 volume) (toLpCLM Complex (E := E) F 2 volume)
    -- Not explicitly stating the measure as being the volume causes time-outs in the proofs below
    (denseRange_toLpCLM ENNReal.ofNat_ne_top) (denseRange_toLpCLM ENNReal.ofNat_ne_top)
    norm_fourier_toL2_eq

/--
Instance `instFourierTransform` / 实例 `instFourierTransform`

English:
instance instFourierTransform
  signature: : FourierTransform (Lp (α := E) F 2) (Lp (α := E) F 2) where
  body: fourierTransformₗᵢ E F

中文:
实例 instFourierTransform
  签名: : Fourier变换 (Lp (α := E) F 2) (Lp (α := E) F 2) where
  定义体: fourierTransformₗᵢ E F
-/
instance instFourierTransform : FourierTransform (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourier := fourierTransformₗᵢ E F

/--
Instance `instFourierAdd` / 实例 `instFourierAdd`

English:
instance instFourierAdd
  signature: : FourierAdd (Lp (α := E) F 2) (Lp (α := E) F 2) where
  body: (fourierTransformₗᵢ E F).map_add

中文:
实例 instFourierAdd
  签名: : FourierAdd (Lp (α := E) F 2) (Lp (α := E) F 2) where
  定义体: (fourierTransformₗᵢ E F).map_add
-/
instance instFourierAdd : FourierAdd (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourier_add := (fourierTransformₗᵢ E F).map_add

/--
Instance `instFourierSMul` / 实例 `instFourierSMul`

English:
instance instFourierSMul
  signature: : FourierSMul Complex (Lp (α := E) F 2) (Lp (α := E) F 2) where
  body: (fourierTransformₗᵢ E F).map_smul

中文:
实例 instFourierSMul
  签名: : FourierSMul 复形 (Lp (α := E) F 2) (Lp (α := E) F 2) where
  定义体: (fourierTransformₗᵢ E F).map_smul
-/
instance instFourierSMul : FourierSMul Complex (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourier_smul := (fourierTransformₗᵢ E F).map_smul

/--
Instance `instContinuousFourier` / 实例 `instContinuousFourier`

English:
instance instContinuousFourier
  signature: : ContinuousFourier (Lp (α := E) F 2) (Lp (α := E) F 2) where
  body: (fourierTransformₗᵢ E F).continuous

中文:
实例 instContinuousFourier
  签名: : 余ntinuousFourier (Lp (α := E) F 2) (Lp (α := E) F 2) where
  定义体: (fourierTransformₗᵢ E F).continuous
-/
instance instContinuousFourier : ContinuousFourier (Lp (α := E) F 2) (Lp (α := E) F 2) where
  continuous_fourier := (fourierTransformₗᵢ E F).continuous

/--
Instance `instFourierTransformInv` / 实例 `instFourierTransformInv`

English:
instance instFourierTransformInv
  signature: : FourierTransformInv (Lp (α := E) F 2) (Lp (α := E) F 2) where
  body: (fourierTransformₗᵢ E F).symm

中文:
实例 instFourierTransformInv
  签名: : FourierTransformInv (Lp (α := E) F 2) (Lp (α := E) F 2) where
  定义体: (fourierTransformₗᵢ E F).symm
-/
instance instFourierTransformInv : FourierTransformInv (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourierInv := (fourierTransformₗᵢ E F).symm

/--
Instance `instFourierInvAdd` / 实例 `instFourierInvAdd`

English:
instance instFourierInvAdd
  signature: : FourierInvAdd (Lp (α := E) F 2) (Lp (α := E) F 2) where
  body: (fourierTransformₗᵢ E F).symm.map_add

中文:
实例 instFourierInvAdd
  签名: : FourierInvAdd (Lp (α := E) F 2) (Lp (α := E) F 2) where
  定义体: (fourierTransformₗᵢ E F).symm.map_add
-/
instance instFourierInvAdd : FourierInvAdd (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourierInv_add := (fourierTransformₗᵢ E F).symm.map_add

/--
Instance `instFourierInvSMul` / 实例 `instFourierInvSMul`

English:
instance instFourierInvSMul
  signature: : FourierInvSMul Complex (Lp (α := E) F 2) (Lp (α := E) F 2) where
  body: (fourierTransformₗᵢ E F).symm.map_smul

中文:
实例 instFourierInvSMul
  签名: : FourierInvSMul 复形 (Lp (α := E) F 2) (Lp (α := E) F 2) where
  定义体: (fourierTransformₗᵢ E F).symm.map_smul
-/
instance instFourierInvSMul : FourierInvSMul Complex (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourierInv_smul := (fourierTransformₗᵢ E F).symm.map_smul

/--
Instance `instContinuousFourierInv` / 实例 `instContinuousFourierInv`

English:
instance instContinuousFourierInv
  signature: : ContinuousFourierInv (Lp (α := E) F 2) (Lp (α := E) F 2) where
  body: (fourierTransformₗᵢ E F).symm.continuous

中文:
实例 instContinuousFourierInv
  签名: : 余ntinuousFourierInv (Lp (α := E) F 2) (Lp (α := E) F 2) where
  定义体: (fourierTransformₗᵢ E F).symm.continuous
-/
instance instContinuousFourierInv : ContinuousFourierInv (Lp (α := E) F 2) (Lp (α := E) F 2) where
  continuous_fourierInv := (fourierTransformₗᵢ E F).symm.continuous

/--
Instance `instFourierPair` / 实例 `instFourierPair`

English:
instance instFourierPair
  signature: : FourierPair (Lp (α := E) F 2) (Lp (α := E) F 2) where
  body: (Lp.fourierTransformₗᵢ E F).symm_apply_apply

中文:
实例 instFourierPair
  签名: : FourierPair (Lp (α := E) F 2) (Lp (α := E) F 2) where
  定义体: (Lp.fourierTransformₗᵢ E F).symm_apply_apply
-/
instance instFourierPair : FourierPair (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourierInv_fourier_eq := (Lp.fourierTransformₗᵢ E F).symm_apply_apply

/--
Instance `instFourierPairInv` / 实例 `instFourierPairInv`

English:
instance instFourierPairInv
  signature: : FourierInvPair (Lp (α := E) F 2) (Lp (α := E) F 2) where
  body: (Lp.fourierTransformₗᵢ E F).apply_symm_apply

中文:
实例 instFourierPairInv
  签名: : FourierInvPair (Lp (α := E) F 2) (Lp (α := E) F 2) where
  定义体: (Lp.fourierTransformₗᵢ E F).apply_symm_apply
-/
instance instFourierPairInv : FourierInvPair (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourier_fourierInv_eq := (Lp.fourierTransformₗᵢ E F).apply_symm_apply

/-- Plancherel's theorem for `L2` functions. -/
@[simp]
/--
theorem `norm_fourier_eq` / 定理 `norm_fourier_eq`

English:
theorem norm_fourier_eq
  given: (f : Lp (α := E) F 2)
  statement: ‖𝓕 f‖ = ‖f‖
  proof: (Lp.fourierTransformₗᵢ E F).norm_map f

@[simp]

中文:
定理 norm_fourier_eq
  条件: (f : Lp (α := E) F 2)
  结论: ‖𝓕 f‖ = ‖f‖
  证明: (Lp.fourierTransformₗᵢ E F).norm_map f

@[simp]
-/
theorem norm_fourier_eq (f : Lp (α := E) F 2) : ‖𝓕 f‖ = ‖f‖ :=
  (Lp.fourierTransformₗᵢ E F).norm_map f

@[simp]
/--
theorem `inner_fourier_eq` / 定理 `inner_fourier_eq`

English:
theorem inner_fourier_eq
  given: (f g : Lp (α := E) F 2)
  statement: ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫
  proof: (Lp.fourierTransformₗᵢ E F).inner_map_map f g

中文:
定理 inner_fourier_eq
  条件: (f g : Lp (α := E) F 2)
  结论: ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫
  证明: (Lp.fourierTransformₗᵢ E F).inner_map_map f g
-/
theorem inner_fourier_eq (f g : Lp (α := E) F 2) : ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫ :=
  (Lp.fourierTransformₗᵢ E F).inner_map_map f g

end MeasureTheory.Lp

@[simp]
/--
theorem `SchwartzMap.toLp_fourier_eq` / 定理 `SchwartzMap.toLp_fourier_eq`

English:
theorem SchwartzMap.toLp_fourier_eq
  given: (f : 𝓢(E, F))
  statement: 𝓕 (f.toLp 2) = (𝓕 f).toLp 2
  proof: by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  use 1
  intro f
  rw [one_mul]
  exact (norm_fourier_toL2_eq f).le

@[simp]

中文:
定理 Schwartz映射.toLp_fourier_eq
  条件: (f : 𝓢(E, F))
  结论: 𝓕 (f.toLp 2) = (𝓕 f).toLp 2
  证明: by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  use 1
  intro f
  rw [one_mul]
  exact (norm_fourier_toL2_eq f).le

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofNat_ne_top, LinearMap, LinearMap.extendOfNorm_eq, SchwartzMap, SchwartzMap.denseRange_toLpCLM, denseRange_toLpCLM, extendOfNorm_eq, norm_fourier_toL2_eq, ofNat_ne_top, one_mul
-/
theorem SchwartzMap.toLp_fourier_eq (f : 𝓢(E, F)) : 𝓕 (f.toLp 2) = (𝓕 f).toLp 2 := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  use 1
  intro f
  rw [one_mul]
  exact (norm_fourier_toL2_eq f).le

@[simp]
/--
theorem `SchwartzMap.toLp_fourierInv_eq` / 定理 `SchwartzMap.toLp_fourierInv_eq`

English:
theorem SchwartzMap.toLp_fourierInv_eq
  given: (f : 𝓢(E, F))
  statement: 𝓕⁻ (f.toLp 2) = (𝓕⁻ f).toLp 2
  proof: by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  use 1
  intro f
  rw [one_mul]
  convert! (norm_fourier_toL2_eq (𝓕⁻ f)).symm.le
  simp

中文:
定理 Schwartz映射.toLp_fourierInv_eq
  条件: (f : 𝓢(E, F))
  结论: 𝓕⁻ (f.toLp 2) = (𝓕⁻ f).toLp 2
  证明: by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  use 1
  intro f
  rw [one_mul]
  convert! (norm_fourier_toL2_eq (𝓕⁻ f)).symm.le
  simp

Depends on / 依赖: ENNReal, ENNReal.ofNat_ne_top, LinearMap, LinearMap.extendOfNorm_eq, SchwartzMap, SchwartzMap.denseRange_toLpCLM, convert, denseRange_toLpCLM, extendOfNorm_eq, norm_fourier_toL2_eq, ofNat_ne_top, one_mul, symm.le
-/
theorem SchwartzMap.toLp_fourierInv_eq (f : 𝓢(E, F)) : 𝓕⁻ (f.toLp 2) = (𝓕⁻ f).toLp 2 := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  use 1
  intro f
  rw [one_mul]
  convert! (norm_fourier_toL2_eq (𝓕⁻ f)).symm.le
  simp

namespace MeasureTheory.Lp

/--
theorem `fourier_toTemperedDistribution_eq` / 定理 `fourier_toTemperedDistribution_eq`

English:
theorem fourier_toTemperedDistribution_eq
  given: (f : Lp (α := E) F 2)
  proof: by
  set p := fun f : Lp (α := E) F 2 => 𝓕 (f : 𝓢'(E, F)) = (𝓕 f : Lp (α := E) F 2)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (fourierCLM Complex 𝓢'(E, F) ∘L toTemperedDistributionCLM F volume 2).co

中文:
定理 fourier_toTemperedDistribution_eq
  条件: (f : Lp (α := E) F 2)
  证明: by
  set p := fun f : Lp (α := E) F 2 => 𝓕 (f : 𝓢'(E, F)) = (𝓕 f : Lp (α := E) F 2)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (fourierCLM Complex 𝓢'(E, F) ∘L toTemperedDistributionCLM F volume 2).co
-/
theorem fourier_toTemperedDistribution_eq (f : Lp (α := E) F 2) :
    𝓕 (f : 𝓢'(E, F)) = (𝓕 f : Lp (α := E) F 2) := by
  set p := fun f : Lp (α := E) F 2 => 𝓕 (f : 𝓢'(E, F)) = (𝓕 f : Lp (α := E) F 2)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (fourierCLM Complex 𝓢'(E, F) ∘L toTemperedDistributionCLM F volume 2).continuous
    · exact (toTemperedDistributionCLM F volume 2 ∘L fourierCLM Complex (Lp (α := E) F 2)).continuous
  intro f
  simp [p, TemperedDistribution.fourier_toTemperedDistributionCLM_eq]

/--
theorem `fourierInv_toTemperedDistribution_eq` / 定理 `fourierInv_toTemperedDistribution_eq`

English:
theorem fourierInv_toTemperedDistribution_eq
  given: (f : Lp (α := E) F 2)
  proof: calc
  _ = 𝓕⁻ (Lp.toTemperedDistribution (𝓕 (𝓕⁻ f))) := by
    congr; exact (fourier_fourierInv_eq f).symm
  _ = 𝓕⁻ (𝓕 (Lp.toTemperedDistribution (𝓕⁻ f))) := by
    rw [fourier_toTemperedDistribution_eq]
  _ = _ := fourierInv_fourier_eq _

中文:
定理 fourierInv_toTemperedDistribution_eq
  条件: (f : Lp (α := E) F 2)
  证明: calc
  _ = 𝓕⁻ (Lp.toTemperedDistribution (𝓕 (𝓕⁻ f))) := by
    congr; exact (fourier_fourierInv_eq f).symm
  _ = 𝓕⁻ (𝓕 (Lp.toTemperedDistribution (𝓕⁻ f))) := by
    rw [fourier_toTemperedDistribution_eq]
  _ = _ := fourierInv_fourier_eq _
-/
theorem fourierInv_toTemperedDistribution_eq (f : Lp (α := E) F 2) :
    𝓕⁻ (f : 𝓢'(E, F)) = (𝓕⁻ f : Lp (α := E) F 2) := calc
  _ = 𝓕⁻ (Lp.toTemperedDistribution (𝓕 (𝓕⁻ f))) := by
    congr; exact (fourier_fourierInv_eq f).symm
  _ = 𝓕⁻ (𝓕 (Lp.toTemperedDistribution (𝓕⁻ f))) := by
    rw [fourier_toTemperedDistribution_eq]
  _ = _ := fourierInv_fourier_eq _

end MeasureTheory.Lp

end FourierTransform
