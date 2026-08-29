/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-! # Fourier multiplier on Schwartz functions and tempered distributions

We define a Fourier multiplier as continuous linear maps on Schwartz functions and tempered
distributions. The multiplier function is throughout assumed to have temperate growth.

## Main definitions
* `SchwartzMap.fourierMultiplierCLM`: Fourier multiplier on Schwartz functions
* `TemperedDistribution.fourierMultiplierCLM`: Fourier multiplier on tempered distribution

## Main statements
* `SchwartzMap.lineDeriv_eq_fourierMultiplierCLM`: the directional derivative is equal to the
  Fourier multiplier with `inner ℝ . m`.
* `SchwartzMap.laplacian_eq_fourierMultiplierCLM`: the Laplacian is equal to the Fourier multiplier
  with `‖·‖`.
* `TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM`: the distributional directional
  derivative is equal to the Fourier multiplier with `inner ℝ . m`.
* `TemperedDistribution.laplacian_eq_fourierMultiplierCLM`: the distributional Laplacian is equal to
  the Fourier multiplier with `‖·‖`.

-/

@[expose] public noncomputable section

variable {ι 𝕜 E F F₁ F₂ : Type*}

namespace SchwartzMap

/-! ## Schwartz functions -/

open scoped SchwartzMap

variable [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace Real E] [NormedSpace Complex F] [NormedSpace 𝕜 F] [SMulCommClass Complex 𝕜 F]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform

variable (F) in
/--
Definition of `fourierMultiplierCLM` / `fourierMultiplierCLM` 的定义

English:
definition fourierMultiplierCLM
  signature: (g : E -> 𝕜)
  body: fourierInvCLM 𝕜 𝓢(E, F) ∘L (smulLeftCLM F g) ∘L fourierCLM 𝕜 𝓢(E, F)

中文:
定义 fourierMultiplierCLM
  签名: (g : E -> 𝕜)
  定义体: fourierInvCLM 𝕜 𝓢(E, F) ∘L (smulLeftCLM F g) ∘L fourierCLM 𝕜 𝓢(E, F)

Depends on / 依赖: fourierCLM, fourierInvCLM, smulLeftCLM
-/
def fourierMultiplierCLM (g : E -> 𝕜) : 𝓢(E, F) ->L[𝕜] 𝓢(E, F) :=
  fourierInvCLM 𝕜 𝓢(E, F) ∘L (smulLeftCLM F g) ∘L fourierCLM 𝕜 𝓢(E, F)

/--
theorem `fourierMultiplierCLM_apply` / 定理 `fourierMultiplierCLM_apply`

English:
theorem fourierMultiplierCLM_apply
  given: (g : E -> 𝕜) (f : 𝓢(E, F))
  proof: by
  rfl

中文:
定理 fourierMultiplierCLM_apply
  条件: (g : E -> 𝕜) (f : 𝓢(E, F))
  证明: by
  rfl
-/
theorem fourierMultiplierCLM_apply (g : E -> 𝕜) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f)) := by
  rfl

variable (𝕜) in
/--
theorem `fourierMultiplierCLM_ofReal` / 定理 `fourierMultiplierCLM_ofReal`

English:
theorem fourierMultiplierCLM_ofReal
  given: {g : E -> Real} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F))
  proof: by
  simp_rw [fourierMultiplierCLM_apply]
  congr 1
  exact smulLeftCLM_ofReal 𝕜 hg (𝓕 f)

中文:
定理 fourierMultiplierCLM_ofReal
  条件: {g : E -> 实数} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F))
  证明: by
  simp_rw [fourierMultiplierCLM_apply]
  congr 1
  exact smulLeftCLM_ofReal 𝕜 hg (𝓕 f)
-/
theorem fourierMultiplierCLM_ofReal {g : E -> Real} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F (fun x => RCLike.ofReal (K := 𝕜) (g x)) f =
    fourierMultiplierCLM F g f := by
  simp_rw [fourierMultiplierCLM_apply]
  congr 1
  exact smulLeftCLM_ofReal 𝕜 hg (𝓕 f)

/--
theorem `fourierMultiplierCLM_smul` / 定理 `fourierMultiplierCLM_smul`

English:
theorem fourierMultiplierCLM_smul
  given: {g : E -> 𝕜} (hg : g.HasTemperateGrowth) (c : 𝕜)
  proof: by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smul hg]

中文:
定理 fourierMultiplierCLM_smul
  条件: {g : E -> 𝕜} (hg : g.HasTemperateGrowth) (c : 𝕜)
  证明: by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smul hg]

Depends on / 依赖: fourierMultiplierCLM_apply, smulLeftCLM_smul
-/
theorem fourierMultiplierCLM_smul {g : E -> 𝕜} (hg : g.HasTemperateGrowth) (c : 𝕜) :
    fourierMultiplierCLM F (c • g) = c • fourierMultiplierCLM F g := by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smul hg]

variable (F) in
/--
theorem `fourierMultiplierCLM_sum` / 定理 `fourierMultiplierCLM_sum`

English:
theorem fourierMultiplierCLM_sum
  statement: {g : ι -> E -> 𝕜} {s : Finset ι}
  proof: by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_sum hg]

中文:
定理 fourierMultiplierCLM_sum
  结论: {g : ι -> E -> 𝕜} {s : Finset ι}
  证明: by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_sum hg]

Depends on / 依赖: fourierMultiplierCLM_apply, smulLeftCLM_sum
-/
theorem fourierMultiplierCLM_sum {g : ι -> E -> 𝕜} {s : Finset ι}
    (hg : forall i in s, (g i).HasTemperateGrowth) :
    fourierMultiplierCLM F (∑ i in s, g i ·) = ∑ i in s, fourierMultiplierCLM F (g i) := by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_sum hg]

variable [CompleteSpace F]

@[simp]
/--
theorem `fourierMultiplierCLM_const` / 定理 `fourierMultiplierCLM_const`

English:
theorem fourierMultiplierCLM_const
  given: (c : 𝕜)
  proof: by
  ext f x
  simp [fourierMultiplierCLM_apply]

中文:
定理 fourierMultiplierCLM_const
  条件: (c : 𝕜)
  证明: by
  ext f x
  simp [fourierMultiplierCLM_apply]

Depends on / 依赖: fourierMultiplierCLM_apply
-/
theorem fourierMultiplierCLM_const (c : 𝕜) :
    fourierMultiplierCLM F (fun (_ : E) => c) = c • ContinuousLinearMap.id _ _ := by
  ext f x
  simp [fourierMultiplierCLM_apply]

/--
theorem `fourierMultiplierCLM_fourierMultiplierCLM_apply` / 定理 `fourierMultiplierCLM_fourierMultiplierCLM_apply`

English:
theorem fourierMultiplierCLM_fourierMultiplierCLM_apply
  statement: {g₁ g₂ : E -> 𝕜}
  proof: by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smulLeftCLM_apply hg₁ hg₂]

中文:
定理 fourierMultiplierCLM_fourierMultiplierCLM_apply
  结论: {g₁ g₂ : E -> 𝕜}
  证明: by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smulLeftCLM_apply hg₁ hg₂]

Depends on / 依赖: fourierMultiplierCLM_apply, smulLeftCLM_smulLeftCLM_apply
-/
theorem fourierMultiplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E -> 𝕜}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g₁ (fourierMultiplierCLM F g₂ f) =
    fourierMultiplierCLM F (g₁ * g₂) f := by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smulLeftCLM_apply hg₁ hg₂]

/--
theorem `fourierMultiplierCLM_compL_fourierMultiplierCLM` / 定理 `fourierMultiplierCLM_compL_fourierMultiplierCLM`

English:
theorem fourierMultiplierCLM_compL_fourierMultiplierCLM
  statement: {g₁ g₂ : E -> 𝕜}
  proof: by
  ext1 f
  simp [fourierMultiplierCLM_fourierMultiplierCLM_apply hg₁ hg₂]

中文:
定理 fourierMultiplierCLM_compL_fourierMultiplierCLM
  结论: {g₁ g₂ : E -> 𝕜}
  证明: by
  ext1 f
  simp [fourierMultiplierCLM_fourierMultiplierCLM_apply hg₁ hg₂]

Depends on / 依赖: fourierMultiplierCLM_fourierMultiplierCLM_apply
-/
theorem fourierMultiplierCLM_compL_fourierMultiplierCLM {g₁ g₂ : E -> 𝕜}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F g₁ ∘L fourierMultiplierCLM F g₂ =
    fourierMultiplierCLM F (g₁ * g₂) := by
  ext1 f
  simp [fourierMultiplierCLM_fourierMultiplierCLM_apply hg₁ hg₂]

open LineDeriv Real

/--
theorem `lineDeriv_eq_fourierMultiplierCLM` / 定理 `lineDeriv_eq_fourierMultiplierCLM`

English:
theorem lineDeriv_eq_fourierMultiplierCLM
  given: (m : E) (f : 𝓢(E, F))
  proof: by
  rw [fourierMultiplierCLM_apply]; rw [← FourierTransform.fourierInv_smul]; rw [← fourier_lineDerivOp_eq]; rw [FourierTransform.fourierInv_fourier_eq]

中文:
定理 lineDeriv_eq_fourierMultiplierCLM
  条件: (m : E) (f : 𝓢(E, F))
  证明: by
  rw [fourierMultiplierCLM_apply]; rw [← FourierTransform.fourierInv_smul]; rw [← fourier_lineDerivOp_eq]; rw [FourierTransform.fourierInv_fourier_eq]

Depends on / 依赖: FourierTransform, FourierTransform.fourierInv_fourier_eq, FourierTransform.fourierInv_smul, fourierInv_fourier_eq, fourierInv_smul, fourierMultiplierCLM_apply, fourier_lineDerivOp_eq
-/
theorem lineDeriv_eq_fourierMultiplierCLM (m : E) (f : 𝓢(E, F)) :
    ∂_{m} f = (2 * π * Complex.I) • fourierMultiplierCLM F (inner Real · m) f := by
  rw [fourierMultiplierCLM_apply]; rw [← FourierTransform.fourierInv_smul]; rw [← fourier_lineDerivOp_eq]; rw [FourierTransform.fourierInv_fourier_eq]

open Laplacian

/--
theorem `laplacian_eq_fourierMultiplierCLM` / 定理 `laplacian_eq_fourierMultiplierCLM`

English:
theorem laplacian_eq_fourierMultiplierCLM
  given: (f : 𝓢(E, F))
  proof: by
  let ι := Fin (Module.finrank Real E)
  let b := stdOrthonormalBasis Real E
  have : forall i (hi : i in Finset.univ), (inner Real · (b i) ^ 2).HasTemperateGrowth := by
    fun_prop
  simp_rw [laplacian_eq_sum b, ← b.sum_sq_inner_left, fourierMultiplierCLM_sum F this,
    _root_.sum_apply, Finse

中文:
定理 laplacian_eq_fourierMultiplierCLM
  条件: (f : 𝓢(E, F))
  证明: by
  let ι := Fin (Module.finrank Real E)
  let b := stdOrthonormalBasis Real E
  have : forall i (hi : i in Finset.univ), (inner Real · (b i) ^ 2).HasTemperateGrowth := by
    fun_prop
  simp_rw [laplacian_eq_sum b, ← b.sum_sq_inner_left, fourierMultiplierCLM_sum F this,
    _root_.sum_apply, Finse

Depends on / 依赖: Finset, Finset.smul_sum, Finset.univ, HasTemperateGrowth, Module, Module.finrank, _root_, _root_.sum_apply, b.sum_sq_inner_left, finrank, fourierMultiplierCLM_ofReal, fourierMultiplierCLM_sum, fun_prop, laplacian_eq_sum, lineDeriv_eq_fourierMultiplierCLM, map_smul, ring_nf, simp_rw, smul_apply, smul_smul
-/
theorem laplacian_eq_fourierMultiplierCLM (f : 𝓢(E, F)) :
    Δ f = -(2 * π) ^ 2 • fourierMultiplierCLM F (‖·‖ ^ 2) f := by
  let ι := Fin (Module.finrank Real E)
  let b := stdOrthonormalBasis Real E
  have : forall i (hi : i in Finset.univ), (inner Real · (b i) ^ 2).HasTemperateGrowth := by
    fun_prop
  simp_rw [laplacian_eq_sum b, ← b.sum_sq_inner_left, fourierMultiplierCLM_sum F this,
    _root_.sum_apply, Finset.smul_sum]
  congr 1
  ext i x
  simp_rw [smul_apply, lineDeriv_eq_fourierMultiplierCLM]
  rw [← fourierMultiplierCLM_ofReal Complex (by fun_prop)]
  simp_rw [map_smul, smul_apply, smul_smul]
  congr 1
  · ring_nf
    simp
  · rw [fourierMultiplierCLM_ofReal Complex (by fun_prop),
      fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
    simp [sq, Pi.mul_def]

end SchwartzMap

namespace TemperedDistribution

/-! ## Tempered distributions -/

open scoped SchwartzMap

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace Real E] [NormedSpace Complex F]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform

variable (F) in
/--
Definition of `fourierMultiplierCLM` / `fourierMultiplierCLM` 的定义

English:
definition fourierMultiplierCLM
  signature: (g : E -> Complex)
  body: fourierInvCLM Complex 𝓢'(E, F) ∘L (smulLeftCLM F g) ∘L fourierCLM Complex 𝓢'(E, F)

中文:
定义 fourierMultiplierCLM
  签名: (g : E -> Complex)
  定义体: fourierInvCLM Complex 𝓢'(E, F) ∘L (smulLeftCLM F g) ∘L fourierCLM Complex 𝓢'(E, F)

Depends on / 依赖: fourierCLM, fourierInvCLM, smulLeftCLM
-/
def fourierMultiplierCLM (g : E -> Complex) : 𝓢'(E, F) ->L[Complex] 𝓢'(E, F) :=
  fourierInvCLM Complex 𝓢'(E, F) ∘L (smulLeftCLM F g) ∘L fourierCLM Complex 𝓢'(E, F)

/--
theorem `fourierMultiplierCLM_apply` / 定理 `fourierMultiplierCLM_apply`

English:
theorem fourierMultiplierCLM_apply
  given: (g : E -> Complex) (f : 𝓢'(E, F))
  proof: by
  rfl

@[simp]

中文:
定理 fourierMultiplierCLM_apply
  条件: (g : E -> Complex) (f : 𝓢'(E, F))
  证明: by
  rfl

@[simp]
-/
theorem fourierMultiplierCLM_apply (g : E -> Complex) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f)) := by
  rfl

@[simp]
/--
theorem `fourierMultiplierCLM_apply_apply` / 定理 `fourierMultiplierCLM_apply_apply`

English:
theorem fourierMultiplierCLM_apply_apply
  given: (g : E -> Complex) (f : 𝓢'(E, F)) (u : 𝓢(E, Complex))
  proof: by
  rfl

@[simp]

中文:
定理 fourierMultiplierCLM_apply_apply
  条件: (g : E -> Complex) (f : 𝓢'(E, F)) (u : 𝓢(E, Complex))
  证明: by
  rfl

@[simp]
-/
theorem fourierMultiplierCLM_apply_apply (g : E -> Complex) (f : 𝓢'(E, F)) (u : 𝓢(E, Complex)) :
    fourierMultiplierCLM F g f u = f (𝓕 (SchwartzMap.smulLeftCLM Complex g (𝓕⁻ u))) := by
  rfl

@[simp]
/--
theorem `fourierMultiplierCLM_const` / 定理 `fourierMultiplierCLM_const`

English:
theorem fourierMultiplierCLM_const
  given: (c : Complex)
  proof: by
  ext
  simp

中文:
定理 fourierMultiplierCLM_const
  条件: (c : Complex)
  证明: by
  ext
  simp
-/
theorem fourierMultiplierCLM_const (c : Complex) :
    fourierMultiplierCLM F (fun (_ : E) => c) = c • ContinuousLinearMap.id _ _ := by
  ext
  simp

/--
theorem `fourierMultiplierCLM_fourierMultiplierCLM_apply` / 定理 `fourierMultiplierCLM_fourierMultiplierCLM_apply`

English:
theorem fourierMultiplierCLM_fourierMultiplierCLM_apply
  statement: {g₁ g₂ : E -> Complex}
  proof: by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smulLeftCLM_apply hg₁ hg₂]

中文:
定理 fourierMultiplierCLM_fourierMultiplierCLM_apply
  结论: {g₁ g₂ : E -> Complex}
  证明: by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smulLeftCLM_apply hg₁ hg₂]

Depends on / 依赖: fourierMultiplierCLM_apply, smulLeftCLM_smulLeftCLM_apply
-/
theorem fourierMultiplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E -> Complex}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F g₂ (fourierMultiplierCLM F g₁ f) =
    fourierMultiplierCLM F (g₁ * g₂) f := by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smulLeftCLM_apply hg₁ hg₂]

/--
theorem `fourierMultiplierCLM_compL_fourierMultiplierCLM` / 定理 `fourierMultiplierCLM_compL_fourierMultiplierCLM`

English:
theorem fourierMultiplierCLM_compL_fourierMultiplierCLM
  statement: {g₁ g₂ : E -> Complex}
  proof: by
  ext1 f
  simp [fourierMultiplierCLM_fourierMultiplierCLM_apply hg₁ hg₂]

中文:
定理 fourierMultiplierCLM_compL_fourierMultiplierCLM
  结论: {g₁ g₂ : E -> Complex}
  证明: by
  ext1 f
  simp [fourierMultiplierCLM_fourierMultiplierCLM_apply hg₁ hg₂]

Depends on / 依赖: fourierMultiplierCLM_fourierMultiplierCLM_apply
-/
theorem fourierMultiplierCLM_compL_fourierMultiplierCLM {g₁ g₂ : E -> Complex}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F g₂ ∘L fourierMultiplierCLM F g₁ =
    fourierMultiplierCLM F (g₁ * g₂) := by
  ext1 f
  simp [fourierMultiplierCLM_fourierMultiplierCLM_apply hg₁ hg₂]

/--
theorem `fourierMultiplierCLM_smul` / 定理 `fourierMultiplierCLM_smul`

English:
theorem fourierMultiplierCLM_smul
  given: {g : E -> Complex} (hg : g.HasTemperateGrowth) (c : Complex)
  proof: by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smul hg]

中文:
定理 fourierMultiplierCLM_smul
  条件: {g : E -> Complex} (hg : g.HasTemperateGrowth) (c : Complex)
  证明: by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smul hg]

Depends on / 依赖: fourierMultiplierCLM_apply, smulLeftCLM_smul
-/
theorem fourierMultiplierCLM_smul {g : E -> Complex} (hg : g.HasTemperateGrowth) (c : Complex) :
    fourierMultiplierCLM F (c • g) = c • fourierMultiplierCLM F g := by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smul hg]

variable (F) in
/--
theorem `fourierMultiplierCLM_sum` / 定理 `fourierMultiplierCLM_sum`

English:
theorem fourierMultiplierCLM_sum
  statement: {g : ι -> E -> Complex} {s : Finset ι}
  proof: by
  ext f u
  simp [SchwartzMap.smulLeftCLM_sum hg]

中文:
定理 fourierMultiplierCLM_sum
  结论: {g : ι -> E -> Complex} {s : Finset ι}
  证明: by
  ext f u
  simp [SchwartzMap.smulLeftCLM_sum hg]

Depends on / 依赖: SchwartzMap, SchwartzMap.smulLeftCLM_sum, smulLeftCLM_sum
-/
theorem fourierMultiplierCLM_sum {g : ι -> E -> Complex} {s : Finset ι}
    (hg : forall i in s, (g i).HasTemperateGrowth) :
    fourierMultiplierCLM F (∑ i in s, g i ·) = ∑ i in s, fourierMultiplierCLM F (g i) := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_sum hg]

section embedding

variable [CompleteSpace F]

/--
theorem `fourierMultiplierCLM_toTemperedDistributionCLM_eq` / 定理 `fourierMultiplierCLM_toTemperedDistributionCLM_eq`

English:
theorem fourierMultiplierCLM_toTemperedDistributionCLM_eq
  statement: {g : E -> Complex}
  proof: by
  ext u
  simp [SchwartzMap.integral_fourier_smul_eq, SchwartzMap.fourierMultiplierCLM_apply g f,
    ← SchwartzMap.integral_fourierInv_smul_eq, hg, smul_smul, mul_comm]

中文:
定理 fourierMultiplierCLM_toTemperedDistributionCLM_eq
  结论: {g : E -> Complex}
  证明: by
  ext u
  simp [SchwartzMap.integral_fourier_smul_eq, SchwartzMap.fourierMultiplierCLM_apply g f,
    ← SchwartzMap.integral_fourierInv_smul_eq, hg, smul_smul, mul_comm]

Depends on / 依赖: SchwartzMap, SchwartzMap.fourierMultiplierCLM_apply, SchwartzMap.integral_fourierInv_smul_eq, SchwartzMap.integral_fourier_smul_eq, fourierMultiplierCLM_apply, integral_fourierInv_smul_eq, integral_fourier_smul_eq, mul_comm, smul_smul
-/
theorem fourierMultiplierCLM_toTemperedDistributionCLM_eq {g : E -> Complex}
    (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g (f : 𝓢'(E, F)) = SchwartzMap.fourierMultiplierCLM F g f := by
  ext u
  simp [SchwartzMap.integral_fourier_smul_eq, SchwartzMap.fourierMultiplierCLM_apply g f,
    ← SchwartzMap.integral_fourierInv_smul_eq, hg, smul_smul, mul_comm]

end embedding

open LineDeriv Real

/--
theorem `lineDeriv_eq_fourierMultiplierCLM` / 定理 `lineDeriv_eq_fourierMultiplierCLM`

English:
theorem lineDeriv_eq_fourierMultiplierCLM
  given: (m : E) (f : 𝓢'(E, F))
  proof: by
  rw [fourierMultiplierCLM_apply]; rw [← FourierTransform.fourierInv_smul]; rw [← fourier_lineDerivOp_eq]; rw [FourierTransform.fourierInv_fourier_eq]

中文:
定理 lineDeriv_eq_fourierMultiplierCLM
  条件: (m : E) (f : 𝓢'(E, F))
  证明: by
  rw [fourierMultiplierCLM_apply]; rw [← FourierTransform.fourierInv_smul]; rw [← fourier_lineDerivOp_eq]; rw [FourierTransform.fourierInv_fourier_eq]

Depends on / 依赖: FourierTransform, FourierTransform.fourierInv_fourier_eq, FourierTransform.fourierInv_smul, fourierInv_fourier_eq, fourierInv_smul, fourierMultiplierCLM_apply, fourier_lineDerivOp_eq
-/
theorem lineDeriv_eq_fourierMultiplierCLM (m : E) (f : 𝓢'(E, F)) :
    ∂_{m} f = (2 * π * Complex.I) • fourierMultiplierCLM F (inner Real · m) f := by
  rw [fourierMultiplierCLM_apply]; rw [← FourierTransform.fourierInv_smul]; rw [← fourier_lineDerivOp_eq]; rw [FourierTransform.fourierInv_fourier_eq]

open Laplacian

/--
theorem `laplacian_eq_fourierMultiplierCLM` / 定理 `laplacian_eq_fourierMultiplierCLM`

English:
theorem laplacian_eq_fourierMultiplierCLM
  given: (f : 𝓢'(E, F))
  proof: by
  let ι := Fin (Module.finrank Real E)
  let b := stdOrthonormalBasis Real E
  have : forall i (hi : i in Finset.univ),
      (fun x => Complex.ofReal (inner Real x (b i)) ^ 2).HasTemperateGrowth := by
    fun_prop
  simp_rw [laplacian_eq_sum b, ← b.sum_sq_inner_left, Complex.ofReal_sum, Complex.

中文:
定理 laplacian_eq_fourierMultiplierCLM
  条件: (f : 𝓢'(E, F))
  证明: by
  let ι := Fin (Module.finrank Real E)
  let b := stdOrthonormalBasis Real E
  have : forall i (hi : i in Finset.univ),
      (fun x => Complex.ofReal (inner Real x (b i)) ^ 2).HasTemperateGrowth := by
    fun_prop
  simp_rw [laplacian_eq_sum b, ← b.sum_sq_inner_left, Complex.ofReal_sum, Complex.

Depends on / 依赖: Complex.ofReal, Complex.ofReal_pow, Complex.ofReal_sum, Finset, Finset.smul_sum, Finset.univ, HasTemperateGrowth, Module, Module.finrank, b.sum_sq_inner_left, finrank, fourierMultiplierCLM_fourierMultiplierCLM_apply, fourierMultiplierCLM_sum, fun_prop, laplacian_eq_sum, lineDeriv_eq_fourierMultiplierCLM, map_smul, ofReal, ofReal_pow, ofReal_sum
-/
theorem laplacian_eq_fourierMultiplierCLM (f : 𝓢'(E, F)) :
    Δ f = -(2 * π) ^ 2 • fourierMultiplierCLM F (fun x => Complex.ofReal (‖x‖ ^ 2)) f := by
  let ι := Fin (Module.finrank Real E)
  let b := stdOrthonormalBasis Real E
  have : forall i (hi : i in Finset.univ),
      (fun x => Complex.ofReal (inner Real x (b i)) ^ 2).HasTemperateGrowth := by
    fun_prop
  simp_rw [laplacian_eq_sum b, ← b.sum_sq_inner_left, Complex.ofReal_sum, Complex.ofReal_pow,
    fourierMultiplierCLM_sum F this, sum_apply, Finset.smul_sum]
  congr 1
  ext i x
  simp_rw [lineDeriv_eq_fourierMultiplierCLM, map_smul, smul_smul]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]; rw [← Complex.coe_smul (-(2 * π) ^ 2)]
  congr 4
  · ring_nf
    simp
  · simp [sq, Pi.mul_def]

end TemperedDistribution
