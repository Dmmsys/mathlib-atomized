/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# TemperedDistribution

## Main definitions

* `TemperedDistribution E F`: The space `𝓢(E, ℂ) →L[ℂ] F` equipped with the pointwise
  convergence topology.
* `MeasureTheory.Measure.toTemperedDistribution`: Every measure of temperate growth is a tempered
  distribution.
* `Function.HasTemperateGrowth.toTemperedDistribution`: Every function of temperate growth is a
  tempered distribution.
* `SchwartzMap.toTemperedDistributionCLM`: The canonical map from `𝓢` to `𝓢'` as a continuous linear
  map.
* `MeasureTheory.Lp.toTemperedDistribution`: Every `Lp` function is a tempered distribution.
* `TemperedDistribution.mulLeftCLM`: Multiplication with temperate growth function as a continuous
  linear map.
* `TemperedDistribution.instLineDeriv`: The directional derivative on tempered distributions.
* `TemperedDistribution.fourierTransformCLM`: The Fourier transform on tempered distributions.

## Notation
* `𝓢'(E, F)`: The space of tempered distributions `TemperedDistribution E F` scoped in
  `SchwartzMap`
-/

@[expose] public noncomputable section

open SchwartzMap ContinuousLinearMap MeasureTheory MeasureTheory.Measure

open scoped Nat NNReal ContDiff

variable {ι 𝕜 E F F₁ F₂ : Type*}

section definition

variable [NormedAddCommGroup E] [NormedSpace Real E]
  [TopologicalSpace F] [AddCommGroup F] [Module Complex F]

variable (E F) in
/--
Definition of `TemperedDistribution` / `TemperedDistribution` 的定义

English:
abbreviation TemperedDistribution
  body: 𝓢(E, Complex) ->Lₚₜ[Complex] F

中文:
缩写 TemperedDistribution
  定义体: 𝓢(E, Complex) ->Lₚₜ[Complex] F
-/
abbrev TemperedDistribution := 𝓢(E, Complex) ->Lₚₜ[Complex] F
/- Since mathlib is missing quite a few results that show that continuity of linear maps and
convergence of sequences can be checked for strong duals of Fréchet-Montel spaces pointwise, we
use the pointwise topology for now and not the strong topology. The pointwise topology is
conventionally used in PDE texts, but has the downside that it is not barrelled, hence the uniform
boundedness principle does not hold. -/

@[inherit_doc]
scoped[SchwartzMap] notation "𝓢'(" E ", " F ")" => TemperedDistribution E F

end definition

/-! ### Embeddings into tempered distributions -/

section Embeddings

variable [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Complex F]

namespace MeasureTheory.Measure

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]

set_option backward.privateInPublic true in
/--
Definition of `toTemperedDistribution` / `toTemperedDistribution` 的定义

English:
definition toTemperedDistribution
  signature: : 𝓢'(E, Complex)
  body: toPointwiseConvergenceCLM _ _ _ _ (integralCLM Complex μ)

中文:
定义 toTemperedDistribution
  签名: : 𝓢'(E, Complex)
  定义体: toPointwiseConvergenceCLM _ _ _ _ (integralCLM Complex μ)

Depends on / 依赖: integralCLM, toPointwiseConvergenceCLM
-/
def toTemperedDistribution : 𝓢'(E, Complex) :=
  toPointwiseConvergenceCLM _ _ _ _ (integralCLM Complex μ)

set_option backward.privateInPublic true in
@[simp]
/--
theorem `toTemperedDistribution_apply` / 定理 `toTemperedDistribution_apply`

English:
theorem toTemperedDistribution_apply
  given: (g : 𝓢(E, Complex))
  proof: by
  rfl

中文:
定理 toTemperedDistribution_apply
  条件: (g : 𝓢(E, Complex))
  证明: by
  rfl
-/
theorem toTemperedDistribution_apply (g : 𝓢(E, Complex)) :
    μ.toTemperedDistribution g = ∫ (x : E), g x ∂μ := by
  rfl

end MeasureTheory.Measure

namespace Function.HasTemperateGrowth

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]

set_option backward.privateInPublic true in
/--
Definition of `toTemperedDistribution` / `toTemperedDistribution` 的定义

English:
definition toTemperedDistribution
  signature: {f : E -> F} (hf : f.HasTemperateGrowth)
  body: toPointwiseConvergenceCLM _ _ _ _ ((integralCLM Complex μ) ∘L (bilinLeftCLM (lsmul Complex Complex) hf))

中文:
定义 toTemperedDistribution
  签名: {f : E -> F} (hf : f.HasTemperateGrowth)
  定义体: toPointwiseConvergenceCLM _ _ _ _ ((integralCLM Complex μ) ∘L (bilinLeftCLM (lsmul Complex Complex) hf))

Depends on / 依赖: bilinLeftCLM, integralCLM, toPointwiseConvergenceCLM
-/
def toTemperedDistribution {f : E -> F} (hf : f.HasTemperateGrowth) : 𝓢'(E, F) :=
  toPointwiseConvergenceCLM _ _ _ _ ((integralCLM Complex μ) ∘L (bilinLeftCLM (lsmul Complex Complex) hf))

set_option backward.privateInPublic true in
@[simp]
/--
theorem `toTemperedDistribution_apply` / 定理 `toTemperedDistribution_apply`

English:
theorem toTemperedDistribution_apply
  given: {f : E -> F} (hf : f.HasTemperateGrowth) (g : 𝓢(E, Complex))
  proof: rfl

中文:
定理 toTemperedDistribution_apply
  条件: {f : E -> F} (hf : f.HasTemperateGrowth) (g : 𝓢(E, Complex))
  证明: rfl
-/
theorem toTemperedDistribution_apply {f : E -> F} (hf : f.HasTemperateGrowth) (g : 𝓢(E, Complex)) :
    toTemperedDistribution μ hf g = ∫ (x : E), g x • f x ∂μ := rfl

end Function.HasTemperateGrowth

namespace SchwartzMap

section MeasurableSpace

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

set_option backward.isDefEq.respectTransparency false in
variable (E F) in
/--
Definition of `toTemperedDistributionCLM` / `toTemperedDistributionCLM` 的定义

English:
definition toTemperedDistributionCLM
  signature: (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]
  body: toPointwiseConvergenceCLM _ _ _ _ integralCLM Complex μ ∘L pairing (lsmul Complex Complex).flip f
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  cont := PointwiseConvergenceCLM.continuous_of_continuous_eval
fun g => (integralCLM Complex μ).cont.comp pairing_continuous_left (lsmul Complex Com

中文:
定义 toTemperedDistributionCLM
  签名: (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]
  定义体: toPointwiseConvergenceCLM _ _ _ _ integralCLM Complex μ ∘L pairing (lsmul Complex Complex).flip f
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  cont := PointwiseConvergenceCLM.continuous_of_continuous_eval
fun g => (integralCLM Complex μ).cont.comp pairing_continuous_left (lsmul Complex Com

Depends on / 依赖: HasTemperateGrowth, PointwiseConvergenceCLM, PointwiseConvergenceCLM.continuous_of_continuous_eval, cont.comp, continuous_of_continuous_eval, integralCLM, map_add, map_smul, pairing, pairing_continuous_left, toPointwiseConvergenceCLM, volume_tac
-/
def toTemperedDistributionCLM (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth] :
    𝓢(E, F) ->L[Complex] 𝓢'(E, F) where
toFun f := toPointwiseConvergenceCLM _ _ _ _ integralCLM Complex μ ∘L pairing (lsmul Complex Complex).flip f
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  cont := PointwiseConvergenceCLM.continuous_of_continuous_eval
fun g => (integralCLM Complex μ).cont.comp pairing_continuous_left (lsmul Complex Complex).flip g

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toTemperedDistributionCLM_apply_apply` / 定理 `toTemperedDistributionCLM_apply_apply`

English:
theorem toTemperedDistributionCLM_apply_apply
  statement: (μ : Measure E := by volume_tac)
  proof: by
  simp [toTemperedDistributionCLM, comp_apply _]

中文:
定理 toTemperedDistributionCLM_apply_apply
  结论: (μ : Measure E := by volume_tac)
  证明: by
  simp [toTemperedDistributionCLM, comp_apply _]

Depends on / 依赖: HasTemperateGrowth, comp_apply, toTemperedDistributionCLM, volume_tac
-/
theorem toTemperedDistributionCLM_apply_apply (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] (f : 𝓢(E, F)) (g : 𝓢(E, Complex)) :
    toTemperedDistributionCLM E F μ f g = ∫ (x : E), g x • f x ∂μ := by
  simp [toTemperedDistributionCLM, comp_apply _]

end MeasurableSpace

section MeasureSpace

variable [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
  [(volume (α := E)).HasTemperateGrowth]

/--
Instance `instCoeToTemperedDistribution` / 实例 `instCoeToTemperedDistribution`

English:
instance instCoeToTemperedDistribution
  signature: :
  body: toTemperedDistributionCLM E F volume

中文:
实例 instCoeToTemperedDistribution
  签名: :
  定义体: toTemperedDistributionCLM E F volume

Depends on / 依赖: toTemperedDistributionCLM, volume
-/
instance instCoeToTemperedDistribution :
    Coe 𝓢(E, F) 𝓢'(E, F) where
  coe := toTemperedDistributionCLM E F volume

/--
theorem `coe_apply` / 定理 `coe_apply`

English:
theorem coe_apply
  given: (f : 𝓢(E, F)) (g : 𝓢(E, Complex))
  proof: toTemperedDistributionCLM_apply_apply volume f g

中文:
定理 coe_apply
  条件: (f : 𝓢(E, F)) (g : 𝓢(E, Complex))
  证明: toTemperedDistributionCLM_apply_apply volume f g

Depends on / 依赖: toTemperedDistributionCLM_apply_apply, volume
-/
theorem coe_apply (f : 𝓢(E, F)) (g : 𝓢(E, Complex)) :
    (f : 𝓢'(E, F)) g = ∫ (x : E), g x • f x :=
  toTemperedDistributionCLM_apply_apply volume f g

end MeasureSpace

end SchwartzMap

namespace MeasureTheory.Lp

open scoped ENNReal

variable [CompleteSpace F]

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [hμ : μ.HasTemperateGrowth]

/--
Definition of `toTemperedDistribution` / `toTemperedDistribution` 的定义

English:
definition toTemperedDistribution
  signature: {p : Real>=0∞}
  body: haveI := ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
  haveI : Fact (1 <= (1 - p⁻¹)⁻¹) := by simp [fact_iff]
toPointwiseConvergenceCLM _ _ _ _
    (lsmul Complex Complex).flip.lpPairing μ p (1 - p⁻¹)⁻¹ f ∘L toLpCLM Complex Complex (1 - p⁻¹)⁻¹ μ

中文:
定义 toTemperedDistribution
  签名: {p : 实数>=0∞}
  定义体: haveI := ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
  haveI : Fact (1 <= (1 - p⁻¹)⁻¹) := by simp [fact_iff]
toPointwiseConvergenceCLM _ _ _ _
    (lsmul Complex Complex).flip.lpPairing μ p (1 - p⁻¹)⁻¹ f ∘L toLpCLM Complex Complex (1 - p⁻¹)⁻¹ μ

Depends on / 依赖: ENNReal, ENNReal.HolderConjugate.inv_one_sub_inv, HolderConjugate, fact_iff, flip.lpPairing, hp.out, inv_one_sub_inv, lpPairing, toLpCLM, toPointwiseConvergenceCLM
-/
def toTemperedDistribution {p : Real>=0∞}
    [hp : Fact (1 <= p)] (f : Lp F p μ) : 𝓢'(E, F) :=
  haveI := ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
  haveI : Fact (1 <= (1 - p⁻¹)⁻¹) := by simp [fact_iff]
toPointwiseConvergenceCLM _ _ _ _
    (lsmul Complex Complex).flip.lpPairing μ p (1 - p⁻¹)⁻¹ f ∘L toLpCLM Complex Complex (1 - p⁻¹)⁻¹ μ

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toTemperedDistribution_apply` / 定理 `toTemperedDistribution_apply`

English:
theorem toTemperedDistribution_apply
  statement: {p : Real>=0∞} [hp : Fact (1 <= p)] (f : Lp F p μ)
  proof: by
  simp only [toTemperedDistribution, toPointwiseConvergenceCLM_apply, comp_apply _, toLpCLM_apply,
    lpPairing_eq_integral, lsmul_flip_apply, toSpanSingleton_apply]
  apply integral_congr_ae
  filter_upwards [g.coeFn_toLp (1 - p⁻¹)⁻¹ μ] with x hg
  rw [hg]

中文:
定理 toTemperedDistribution_apply
  结论: {p : 实数>=0∞} [hp : Fact (1 <= p)] (f : Lp F p μ)
  证明: by
  simp only [toTemperedDistribution, toPointwiseConvergenceCLM_apply, comp_apply _, toLpCLM_apply,
    lpPairing_eq_integral, lsmul_flip_apply, toSpanSingleton_apply]
  apply integral_congr_ae
  filter_upwards [g.coeFn_toLp (1 - p⁻¹)⁻¹ μ] with x hg
  rw [hg]

Depends on / 依赖: coeFn_toLp, comp_apply, filter_upwards, g.coeFn_toLp, integral_congr_ae, lpPairing_eq_integral, lsmul_flip_apply, toLpCLM_apply, toPointwiseConvergenceCLM_apply, toSpanSingleton_apply, toTemperedDistribution
-/
theorem toTemperedDistribution_apply {p : Real>=0∞} [hp : Fact (1 <= p)] (f : Lp F p μ)
    (g : 𝓢(E, Complex)) :
    toTemperedDistribution f g = ∫ (x : E), g x • f x ∂μ := by
  simp only [toTemperedDistribution, toPointwiseConvergenceCLM_apply, comp_apply _, toLpCLM_apply,
    lpPairing_eq_integral, lsmul_flip_apply, toSpanSingleton_apply]
  apply integral_congr_ae
  filter_upwards [g.coeFn_toLp (1 - p⁻¹)⁻¹ μ] with x hg
  rw [hg]

/--
Instance `instCoeToTemperedDistribution` / 实例 `instCoeToTemperedDistribution`

English:
instance instCoeToTemperedDistribution
  signature: {p : Real>=0∞} [hp : Fact (1 <= p)]
  body: toTemperedDistribution

@[simp]

中文:
实例 instCoeToTemperedDistribution
  签名: {p : 实数>=0∞} [hp : Fact (1 <= p)]
  定义体: toTemperedDistribution

@[simp]

Depends on / 依赖: toTemperedDistribution
-/
instance instCoeToTemperedDistribution {p : Real>=0∞} [hp : Fact (1 <= p)] :
    CoeHead (Lp F p μ) 𝓢'(E, F) where
  coe := toTemperedDistribution

@[simp]
/--
theorem `toTemperedDistribution_toLp_eq` / 定理 `toTemperedDistribution_toLp_eq`

English:
theorem toTemperedDistribution_toLp_eq
  statement: [SecondCountableTopology E] {p : Real>=0∞} [hp : Fact (1 <= p)]
  proof: by
  ext g
  simp only [Lp.toTemperedDistribution_apply, toTemperedDistributionCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp p μ] with x hf
  rw [hf]

中文:
定理 toTemperedDistribution_toLp_eq
  结论: [SecondCountableTopology E] {p : 实数>=0∞} [hp : Fact (1 <= p)]
  证明: by
  ext g
  simp only [Lp.toTemperedDistribution_apply, toTemperedDistributionCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp p μ] with x hf
  rw [hf]

Depends on / 依赖: Lp.toTemperedDistribution_apply, coeFn_toLp, f.coeFn_toLp, filter_upwards, integral_congr_ae, toTemperedDistributionCLM_apply_apply, toTemperedDistribution_apply
-/
theorem toTemperedDistribution_toLp_eq [SecondCountableTopology E] {p : Real>=0∞} [hp : Fact (1 <= p)]
    (f : 𝓢(E, F)) : ((f : Lp F p μ) : 𝓢'(E, F)) = f.toTemperedDistributionCLM E F μ := by
  ext g
  simp only [Lp.toTemperedDistribution_apply, toTemperedDistributionCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp p μ] with x hf
  rw [hf]

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/--
Definition of `toTemperedDistributionCLM` / `toTemperedDistributionCLM` 的定义

English:
definition toTemperedDistributionCLM
  signature: (μ : Measure E := by volume_tac) [μ.HasTemperateGrowth]
  body: toTemperedDistribution
  map_add' f g := by simp [Lp.toTemperedDistribution]
  map_smul' a f := by simp [Lp.toTemperedDistribution]
  cont := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro g
    have : Fact (1 <= (1 - p⁻¹)⁻¹) := by simp [fact_iff]
    have hpq : ENNReal

中文:
定义 toTemperedDistributionCLM
  签名: (μ : Measure E := by volume_tac) [μ.HasTemperateGrowth]
  定义体: toTemperedDistribution
  map_add' f g := by simp [Lp.toTemperedDistribution]
  map_smul' a f := by simp [Lp.toTemperedDistribution]
  cont := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro g
    have : Fact (1 <= (1 - p⁻¹)⁻¹) := by simp [fact_iff]
    have hpq : ENNReal

Depends on / 依赖: ENNReal, ENNReal.HolderConjugate, ENNReal.HolderConjugate.inv_one_sub_inv, HasTemperateGrowth, HolderConjugate, Lp.toTemperedDistribution, PointwiseConvergenceCLM, PointwiseConvergenceCLM.continuous_of_continuous_eval, continuous_of_continuous_eval, fact_iff, hp.out, inv_one_sub_inv, map_add, map_smul, toTemperedDistribution, volume_tac
-/
def toTemperedDistributionCLM (μ : Measure E := by volume_tac) [μ.HasTemperateGrowth]
    (p : Real>=0∞) [hp : Fact (1 <= p)] :
    Lp F p μ ->L[Complex] 𝓢'(E, F) where
  toFun := toTemperedDistribution
  map_add' f g := by simp [Lp.toTemperedDistribution]
  map_smul' a f := by simp [Lp.toTemperedDistribution]
  cont := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro g
    have : Fact (1 <= (1 - p⁻¹)⁻¹) := by simp [fact_iff]
    have hpq : ENNReal.HolderConjugate p (1 - p⁻¹)⁻¹ :=
      ENNReal.HolderConjugate.inv_one_sub_inv' hp.out
    exact (((lsmul Complex Complex (E := F)).flip.lpPairing μ p (1 - p⁻¹)⁻¹).flip (g.toLp (1 - p⁻¹)⁻¹ μ)).cont

@[simp]
/--
theorem `toTemperedDistributionCLM_apply` / 定理 `toTemperedDistributionCLM_apply`

English:
theorem toTemperedDistributionCLM_apply
  given: {p : Real>=0∞} [hp : Fact (1 <= p)] (f : Lp F p μ)
  proof: rfl

中文:
定理 toTemperedDistributionCLM_apply
  条件: {p : 实数>=0∞} [hp : Fact (1 <= p)] (f : Lp F p μ)
  证明: rfl
-/
theorem toTemperedDistributionCLM_apply {p : Real>=0∞} [hp : Fact (1 <= p)] (f : Lp F p μ) :
    toTemperedDistributionCLM F μ p f = f := rfl

variable [FiniteDimensional Real E] [IsLocallyFiniteMeasure μ]

/--
theorem `ker_toTemperedDistributionCLM_eq_bot` / 定理 `ker_toTemperedDistributionCLM_eq_bot`

English:
theorem ker_toTemperedDistributionCLM_eq_bot
  given: {p : Real>=0∞} [hp : Fact (1 <= p)]
  proof: by
  rw [LinearMap.ker_eq_bot']; rw [ContinuousLinearMap.coe_coe]
  intro f hf
  rw [eq_zero_iff_ae_eq_zero]
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
  · exact (Lp.memLp f).locallyIntegrable hp.elim
  · intro g g_smooth g_cpt
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_

中文:
定理 ker_toTemperedDistributionCLM_eq_bot
  条件: {p : 实数>=0∞} [hp : Fact (1 <= p)]
  证明: by
  rw [LinearMap.ker_eq_bot']; rw [ContinuousLinearMap.coe_coe]
  intro f hf
  rw [eq_zero_iff_ae_eq_zero]
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
  · exact (Lp.memLp f).locallyIntegrable hp.elim
  · intro g g_smooth g_cpt
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_

Depends on / 依赖: Complex.ofRealCLM, ContDiff, ContinuousLinearMap, ContinuousLinearMap.coe_coe, HasCompactSupport, LinearMap, LinearMap.ker_eq_bot, Lp.memLp, ae_eq_zero_of_integral_contDiff_smul_eq_zero, coe_coe, comp_left, eq_zero_iff_ae_eq_zero, fun_prop, g_cpt, g_cpt.comp_left, g_smooth, hp.elim, ker_eq_bot, locallyIntegrable, ofRealCLM
-/
theorem ker_toTemperedDistributionCLM_eq_bot {p : Real>=0∞} [hp : Fact (1 <= p)] :
    (MeasureTheory.Lp.toTemperedDistributionCLM F μ p).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot']; rw [ContinuousLinearMap.coe_coe]
  intro f hf
  rw [eq_zero_iff_ae_eq_zero]
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
  · exact (Lp.memLp f).locallyIntegrable hp.elim
  · intro g g_smooth g_cpt
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hg₂ : ContDiff Real ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
    calc
      _ = toTemperedDistributionCLM F μ p f (hg₁.toSchwartzMap hg₂) := by simp
      _ = _ := by simp [hf]

end MeasureTheory.Lp

end Embeddings

namespace TemperedDistribution

/-! ### Scalar multiplication with temperate growth functions -/

section Multiplication

variable [NormedAddCommGroup E] [NormedSpace Real E]

section TVS

variable [AddCommGroup F] [Module Complex F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul Complex F]

variable (F) in
/--
Definition of `smulLeftCLM` / `smulLeftCLM` 的定义

English:
definition smulLeftCLM
  signature: (g : E -> Complex)
  body: PointwiseConvergenceCLM.precomp _ (SchwartzMap.smulLeftCLM Complex g)

@[simp]

中文:
定义 smulLeftCLM
  签名: (g : E -> Complex)
  定义体: PointwiseConvergenceCLM.precomp _ (SchwartzMap.smulLeftCLM Complex g)

@[simp]

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.precomp, SchwartzMap, SchwartzMap.smulLeftCLM, precomp, smulLeftCLM
-/
def smulLeftCLM (g : E -> Complex) : 𝓢'(E, F) ->L[Complex] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp _ (SchwartzMap.smulLeftCLM Complex g)

@[simp]
/--
theorem `smulLeftCLM_apply_apply` / 定理 `smulLeftCLM_apply_apply`

English:
theorem smulLeftCLM_apply_apply
  given: (g : E -> Complex) (f : 𝓢'(E, F)) (f' : 𝓢(E, Complex))
  proof: by
  rfl

@[simp]

中文:
定理 smulLeftCLM_apply_apply
  条件: (g : E -> Complex) (f : 𝓢'(E, F)) (f' : 𝓢(E, Complex))
  证明: by
  rfl

@[simp]
-/
theorem smulLeftCLM_apply_apply (g : E -> Complex) (f : 𝓢'(E, F)) (f' : 𝓢(E, Complex)) :
    smulLeftCLM F g f f' = f (SchwartzMap.smulLeftCLM Complex g f') := by
  rfl

@[simp]
/--
theorem `smulLeftCLM_const` / 定理 `smulLeftCLM_const`

English:
theorem smulLeftCLM_const
  given: (c : Complex) (f : 𝓢'(E, F))
  statement: smulLeftCLM F (fun _ : E => c) f = c • f
  proof: by
  ext1; simp

@[simp]

中文:
定理 smulLeftCLM_const
  条件: (c : Complex) (f : 𝓢'(E, F))
  结论: smulLeftCLM F (fun _ : E => c) f = c • f
  证明: by
  ext1; simp

@[simp]
-/
theorem smulLeftCLM_const (c : Complex) (f : 𝓢'(E, F)) : smulLeftCLM F (fun _ : E => c) f = c • f := by
  ext1; simp

@[simp]
/--
theorem `smulLeftCLM_smulLeftCLM_apply` / 定理 `smulLeftCLM_smulLeftCLM_apply`

English:
theorem smulLeftCLM_smulLeftCLM_apply
  statement: {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth)
  proof: by
  ext; simp [hg₁, hg₂]

中文:
定理 smulLeftCLM_smulLeftCLM_apply
  结论: {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth)
  证明: by
  ext; simp [hg₁, hg₂]
-/
theorem smulLeftCLM_smulLeftCLM_apply {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E, F)) :
    smulLeftCLM F g₂ (smulLeftCLM F g₁ f) = smulLeftCLM F (g₁ * g₂) f := by
  ext; simp [hg₁, hg₂]

/--
theorem `smulLeftCLM_compL_smulLeftCLM` / 定理 `smulLeftCLM_compL_smulLeftCLM`

English:
theorem smulLeftCLM_compL_smulLeftCLM
  statement: {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth)
  proof: by
  ext1 f
  simp [hg₁, hg₂]

中文:
定理 smulLeftCLM_compL_smulLeftCLM
  结论: {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth)
  证明: by
  ext1 f
  simp [hg₁, hg₂]
-/
theorem smulLeftCLM_compL_smulLeftCLM {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F g₂ ∘L smulLeftCLM F g₁ = smulLeftCLM F (g₁ * g₂) := by
  ext1 f
  simp [hg₁, hg₂]

/--
theorem `smulLeftCLM_smul` / 定理 `smulLeftCLM_smul`

English:
theorem smulLeftCLM_smul
  given: {g : E -> Complex} (hg : g.HasTemperateGrowth) (c : Complex)
  proof: by
  ext f u
  simp [SchwartzMap.smulLeftCLM_smul hg]

中文:
定理 smulLeftCLM_smul
  条件: {g : E -> Complex} (hg : g.HasTemperateGrowth) (c : Complex)
  证明: by
  ext f u
  simp [SchwartzMap.smulLeftCLM_smul hg]

Depends on / 依赖: SchwartzMap, SchwartzMap.smulLeftCLM_smul, smulLeftCLM_smul
-/
theorem smulLeftCLM_smul {g : E -> Complex} (hg : g.HasTemperateGrowth) (c : Complex) :
    smulLeftCLM F (c • g) = c • smulLeftCLM F g := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_smul hg]

/--
theorem `smulLeftCLM_add` / 定理 `smulLeftCLM_add`

English:
theorem smulLeftCLM_add
  statement: {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth)
  proof: by
  ext f u
  simp [SchwartzMap.smulLeftCLM_add hg₁ hg₂]

中文:
定理 smulLeftCLM_add
  结论: {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth)
  证明: by
  ext f u
  simp [SchwartzMap.smulLeftCLM_add hg₁ hg₂]

Depends on / 依赖: SchwartzMap, SchwartzMap.smulLeftCLM_add, smulLeftCLM_add
-/
theorem smulLeftCLM_add {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F (g₁ + g₂) = smulLeftCLM F g₁ + smulLeftCLM F g₂ := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_add hg₁ hg₂]

/--
theorem `smulLeftCLM_sub` / 定理 `smulLeftCLM_sub`

English:
theorem smulLeftCLM_sub
  statement: {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth)
  proof: by
  ext f u
  simp [SchwartzMap.smulLeftCLM_sub hg₁ hg₂]

中文:
定理 smulLeftCLM_sub
  结论: {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth)
  证明: by
  ext f u
  simp [SchwartzMap.smulLeftCLM_sub hg₁ hg₂]

Depends on / 依赖: SchwartzMap, SchwartzMap.smulLeftCLM_sub, smulLeftCLM_sub
-/
theorem smulLeftCLM_sub {g₁ g₂ : E -> Complex} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F (g₁ - g₂) = smulLeftCLM F g₁ - smulLeftCLM F g₂ := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_sub hg₁ hg₂]

/--
theorem `smulLeftCLM_neg` / 定理 `smulLeftCLM_neg`

English:
theorem smulLeftCLM_neg
  given: {g : E -> Complex} (hg : g.HasTemperateGrowth)
  proof: by
  ext f u
  simp [SchwartzMap.smulLeftCLM_neg hg]

中文:
定理 smulLeftCLM_neg
  条件: {g : E -> Complex} (hg : g.HasTemperateGrowth)
  证明: by
  ext f u
  simp [SchwartzMap.smulLeftCLM_neg hg]

Depends on / 依赖: SchwartzMap, SchwartzMap.smulLeftCLM_neg, smulLeftCLM_neg
-/
theorem smulLeftCLM_neg {g : E -> Complex} (hg : g.HasTemperateGrowth) :
    smulLeftCLM F (-g) = -smulLeftCLM F g := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_neg hg]

/--
theorem `smulLeftCLM_sum` / 定理 `smulLeftCLM_sum`

English:
theorem smulLeftCLM_sum
  given: {g : ι -> E -> Complex} {s : Finset ι} (hg : forall i in s, (g i).HasTemperateGrowth)
  proof: by
  ext f u
  simp [SchwartzMap.smulLeftCLM_sum hg]

中文:
定理 smulLeftCLM_sum
  条件: {g : ι -> E -> Complex} {s : Finset ι} (hg : 对任意 i in s, (g i).HasTemperateGrowth)
  证明: by
  ext f u
  simp [SchwartzMap.smulLeftCLM_sum hg]

Depends on / 依赖: SchwartzMap, SchwartzMap.smulLeftCLM_sum, smulLeftCLM_sum
-/
theorem smulLeftCLM_sum {g : ι -> E -> Complex} {s : Finset ι} (hg : forall i in s, (g i).HasTemperateGrowth) :
    smulLeftCLM F (fun x => ∑ i in s, g i x) = ∑ i in s, smulLeftCLM F (g i) := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_sum hg]

end TVS

open ENNReal MeasureTheory

variable [NormedAddCommGroup F] [NormedSpace Complex F] [CompleteSpace F]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [hμ : μ.HasTemperateGrowth]

/--
theorem `_root_.MeasureTheory.Lp.toTemperedDistribution_smul_eq` / 定理 `_root_.MeasureTheory.Lp.toTemperedDistribution_smul_eq`

English:
theorem _root_.MeasureTheory.Lp.toTemperedDistribution_smul_eq
  statement: {p q r : Real>=0∞} [p.HolderTriple q r]
  proof: by
  ext u
  simp only [Lp.toTemperedDistribution_apply, smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_lpSMul (r := r) (hg₂.toLp _) f, hg₂.coeFn_toLp] with x hg hg'
  simp [hg, hg', hg₁, smul_smul, mul_comm]

中文:
定理 _root_.MeasureTheory.Lp.toTemperedDistribution_smul_eq
  结论: {p q r : 实数>=0∞} [p.HolderTriple q r]
  证明: by
  ext u
  simp only [Lp.toTemperedDistribution_apply, smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_lpSMul (r := r) (hg₂.toLp _) f, hg₂.coeFn_toLp] with x hg hg'
  simp [hg, hg', hg₁, smul_smul, mul_comm]

Depends on / 依赖: Lp.coeFn_lpSMul, Lp.toTemperedDistribution_apply, coeFn_lpSMul, coeFn_toLp, filter_upwards, integral_congr_ae, mul_comm, smulLeftCLM_apply_apply, smul_smul, toTemperedDistribution_apply
-/
theorem _root_.MeasureTheory.Lp.toTemperedDistribution_smul_eq {p q r : Real>=0∞} [p.HolderTriple q r]
    [Fact (1 <= q)] [Fact (1 <= r)] {g : E -> Complex} (hg₁ : g.HasTemperateGrowth) (hg₂ : MemLp g p μ)
    (f : Lp F q μ) :
    ((hg₂.toLp _) • f : Lp F r μ) = smulLeftCLM F g f := by
  ext u
  simp only [Lp.toTemperedDistribution_apply, smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_lpSMul (r := r) (hg₂.toLp _) f, hg₂.coeFn_toLp] with x hg hg'
  simp [hg, hg', hg₁, smul_smul, mul_comm]

end Multiplication

/-! ### Derivatives -/

section deriv

section TVS

variable [AddCommGroup F] [Module Complex F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul Complex F]

variable (F) in
/--
Definition of `derivCLM` / `derivCLM` 的定义

English:
definition derivCLM
  signature: : 𝓢'(Real, F) ->L[Complex] 𝓢'(Real, F)
  body: PointwiseConvergenceCLM.precomp F (-SchwartzMap.derivCLM Complex Complex)

@[simp]

中文:
定义 derivCLM
  签名: : 𝓢'(实数, F) ->L[Complex] 𝓢'(实数, F)
  定义体: PointwiseConvergenceCLM.precomp F (-SchwartzMap.derivCLM Complex Complex)

@[simp]

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.precomp, SchwartzMap, SchwartzMap.derivCLM, derivCLM, precomp
-/
def derivCLM : 𝓢'(Real, F) ->L[Complex] 𝓢'(Real, F) :=
  PointwiseConvergenceCLM.precomp F (-SchwartzMap.derivCLM Complex Complex)

@[simp]
/--
theorem `derivCLM_apply_apply` / 定理 `derivCLM_apply_apply`

English:
theorem derivCLM_apply_apply
  given: (f : 𝓢'(Real, F)) (g : 𝓢(Real, Complex))
  proof: rfl

中文:
定理 derivCLM_apply_apply
  条件: (f : 𝓢'(实数, F)) (g : 𝓢(实数, Complex))
  证明: rfl
-/
theorem derivCLM_apply_apply (f : 𝓢'(Real, F)) (g : 𝓢(Real, Complex)) :
    derivCLM F f g = f (-SchwartzMap.derivCLM Complex Complex g) := rfl

end TVS

variable [RCLike 𝕜] [NormedAddCommGroup F] [NormedSpace Complex F] [NormedSpace 𝕜 F]

variable (𝕜) in
/--
theorem `derivCLM_toTemperedDistributionCLM_eq` / 定理 `derivCLM_toTemperedDistributionCLM_eq`

English:
theorem derivCLM_toTemperedDistributionCLM_eq
  given: (f : 𝓢(Real, F))
  proof: by
  ext1 g
  simp [integral_smul_deriv_right_eq_neg_left, integral_neg]

中文:
定理 derivCLM_toTemperedDistributionCLM_eq
  条件: (f : 𝓢(实数, F))
  证明: by
  ext1 g
  simp [integral_smul_deriv_right_eq_neg_left, integral_neg]

Depends on / 依赖: integral_neg, integral_smul_deriv_right_eq_neg_left
-/
theorem derivCLM_toTemperedDistributionCLM_eq (f : 𝓢(Real, F)) :
    derivCLM F (f : 𝓢'(Real, F)) = SchwartzMap.derivCLM 𝕜 F f := by
  ext1 g
  simp [integral_smul_deriv_right_eq_neg_left, integral_neg]

end deriv

section lineDeriv

open LineDeriv

variable [NormedAddCommGroup E] [NormedSpace Real E]

section TVS

variable [AddCommGroup F] [Module Complex F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul Complex F]

/--
Instance `instLineDeriv` / 实例 `instLineDeriv`

English:
instance instLineDeriv
  signature: : LineDeriv E 𝓢'(E, F) 𝓢'(E, F) where
  body: PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m)

@[simp]

中文:
实例 instLineDeriv
  签名: : LineDeriv E 𝓢'(E, F) 𝓢'(E, F) where
  定义体: PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m)

@[simp]

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.precomp, lineDerivOpCLM, precomp
-/
instance instLineDeriv : LineDeriv E 𝓢'(E, F) 𝓢'(E, F) where
  lineDerivOp m := PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m)

@[simp]
/--
theorem `lineDerivOp_apply_apply` / 定理 `lineDerivOp_apply_apply`

English:
theorem lineDerivOp_apply_apply
  given: (f : 𝓢'(E, F)) (g : 𝓢(E, Complex)) (m : E)
  proof: rfl

中文:
定理 lineDerivOp_apply_apply
  条件: (f : 𝓢'(E, F)) (g : 𝓢(E, Complex)) (m : E)
  证明: rfl
-/
theorem lineDerivOp_apply_apply (f : 𝓢'(E, F)) (g : 𝓢(E, Complex)) (m : E) :
    ∂_{m} f g = f (- ∂_{m} g) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LineDerivAdd E 𝓢'(E, F) 𝓢'(E, F)
  body: (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m)).map_add
  lineDerivOp_left_add x y f := by
    ext u
    simp [lineDerivOp_left_add, add_comm]

中文:
实例 :
  签名: LineDerivAdd E 𝓢'(E, F) 𝓢'(E, F)
  定义体: (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m)).map_add
  lineDerivOp_left_add x y f := by
    ext u
    simp [lineDerivOp_left_add, add_comm]

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.precomp, lineDerivOpCLM, map_add, precomp
-/
instance : LineDerivAdd E 𝓢'(E, F) 𝓢'(E, F) where
  lineDerivOp_add m := (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m)).map_add
  lineDerivOp_left_add x y f := by
    ext u
    simp [lineDerivOp_left_add, add_comm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LineDerivSMul Complex E 𝓢'(E, F) 𝓢'(E, F)
  body: (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m)).map_smul

中文:
实例 :
  签名: LineDerivSMul Complex E 𝓢'(E, F) 𝓢'(E, F)
  定义体: (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m)).map_smul

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.precomp, lineDerivOpCLM, map_smul, precomp
-/
instance : LineDerivSMul Complex E 𝓢'(E, F) 𝓢'(E, F) where
  lineDerivOp_smul m := (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m)).map_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LineDerivSMul Real E 𝓢'(E, F) 𝓢'(E, F)
  body: (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m)).map_smul_of_tower

中文:
实例 :
  签名: LineDerivSMul 实数 E 𝓢'(E, F) 𝓢'(E, F)
  定义体: (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m)).map_smul_of_tower

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.precomp, lineDerivOpCLM, map_smul_of_tower, precomp
-/
instance : LineDerivSMul Real E 𝓢'(E, F) 𝓢'(E, F) where
  lineDerivOp_smul m :=
    (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m)).map_smul_of_tower

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousLineDeriv E 𝓢'(E, F) 𝓢'(E, F)
  body: (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m)).continuous

中文:
实例 :
  签名: ContinuousLineDeriv E 𝓢'(E, F) 𝓢'(E, F)
  定义体: (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m)).continuous

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.precomp, continuous, lineDerivOpCLM, precomp
-/
instance : ContinuousLineDeriv E 𝓢'(E, F) 𝓢'(E, F) where
  continuous_lineDerivOp m :=
    (PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m)).continuous

/--
theorem `lineDerivOpCLM_eq` / 定理 `lineDerivOpCLM_eq`

English:
theorem lineDerivOpCLM_eq
  given: (m : E)
  statement: lineDerivOpCLM Complex 𝓢'(E, F) m =
  proof: rfl

中文:
定理 lineDerivOpCLM_eq
  条件: (m : E)
  结论: lineDerivOpCLM Complex 𝓢'(E, F) m =
  证明: rfl
-/
theorem lineDerivOpCLM_eq (m : E) : lineDerivOpCLM Complex 𝓢'(E, F) m =
  PointwiseConvergenceCLM.precomp F (-lineDerivOpCLM Complex 𝓢(E, Complex) m) := rfl

end TVS

variable [NormedAddCommGroup F] [NormedSpace Complex F]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LineDerivLeftSMul Real E 𝓢'(E, F) 𝓢'(E, F)
  body: by
    ext u
    simp [lineDerivOp_left_smul, map_smul_of_tower f]

中文:
实例 :
  签名: LineDerivLeftSMul 实数 E 𝓢'(E, F) 𝓢'(E, F)
  定义体: by
    ext u
    simp [lineDerivOp_left_smul, map_smul_of_tower f]

Depends on / 依赖: lineDerivOp_left_smul, map_smul_of_tower
-/
instance : LineDerivLeftSMul Real E 𝓢'(E, F) 𝓢'(E, F) where
  lineDerivOp_left_smul r x f := by
    ext u
    simp [lineDerivOp_left_smul, map_smul_of_tower f]

variable
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional Real E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/--
theorem `lineDerivOp_toTemperedDistributionCLM_eq` / 定理 `lineDerivOp_toTemperedDistributionCLM_eq`

English:
theorem lineDerivOp_toTemperedDistributionCLM_eq
  given: (f : 𝓢(E, F)) (m : E)
  proof: by
  ext1 g
  simp [integral_smul_lineDerivOp_right_eq_neg_left g f, integral_neg]

中文:
定理 lineDerivOp_toTemperedDistributionCLM_eq
  条件: (f : 𝓢(E, F)) (m : E)
  证明: by
  ext1 g
  simp [integral_smul_lineDerivOp_right_eq_neg_left g f, integral_neg]

Depends on / 依赖: integral_neg, integral_smul_lineDerivOp_right_eq_neg_left
-/
theorem lineDerivOp_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) (m : E) :
    ∂_{m} (toTemperedDistributionCLM E F μ f) = toTemperedDistributionCLM E F μ (∂_{m} f) := by
  ext1 g
  simp [integral_smul_lineDerivOp_right_eq_neg_left g f, integral_neg]

end lineDeriv

/-! ### Laplacian-/

section Laplacian

open Laplacian LineDeriv
open scoped SchwartzMap

variable [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]

section TVS

variable [AddCommGroup F] [Module Complex F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul Complex F]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Laplacian 𝓢'(E, F) 𝓢'(E, F)
  body: LineDeriv.laplacianCLM Real E 𝓢'(E, F)

@[simp]

中文:
实例 :
  签名: Laplacian 𝓢'(E, F) 𝓢'(E, F)
  定义体: LineDeriv.laplacianCLM Real E 𝓢'(E, F)

@[simp]

Depends on / 依赖: LineDeriv, LineDeriv.laplacianCLM, laplacianCLM
-/
instance : Laplacian 𝓢'(E, F) 𝓢'(E, F) where
  laplacian := LineDeriv.laplacianCLM Real E 𝓢'(E, F)

@[simp]
/--
theorem `laplacianCLM_apply` / 定理 `laplacianCLM_apply`

English:
theorem laplacianCLM_apply
  given: (f : 𝓢'(E, F))
  statement: laplacianCLM Complex E 𝓢'(E, F) f = Δ f
  proof: by
  simp [laplacianCLM, laplacian]

中文:
定理 laplacianCLM_apply
  条件: (f : 𝓢'(E, F))
  结论: laplacianCLM Complex E 𝓢'(E, F) f = Δ f
  证明: by
  simp [laplacianCLM, laplacian]

Depends on / 依赖: laplacian, laplacianCLM
-/
theorem laplacianCLM_apply (f : 𝓢'(E, F)) : laplacianCLM Complex E 𝓢'(E, F) f = Δ f := by
  simp [laplacianCLM, laplacian]

end TVS

variable [NormedAddCommGroup F] [NormedSpace Complex F]

/--
theorem `laplacian_eq_sum` / 定理 `laplacian_eq_sum`

English:
theorem laplacian_eq_sum
  given: [Fintype ι] (b : OrthonormalBasis ι Real E) (f : 𝓢'(E, F))
  proof: LineDeriv.laplacianCLM_eq_sum b f

@[simp]

中文:
定理 laplacian_eq_sum
  条件: [Fintype ι] (b : OrthonormalBasis ι 实数 E) (f : 𝓢'(E, F))
  证明: LineDeriv.laplacianCLM_eq_sum b f

@[simp]

Depends on / 依赖: LineDeriv, LineDeriv.laplacianCLM_eq_sum, laplacianCLM_eq_sum
-/
theorem laplacian_eq_sum [Fintype ι] (b : OrthonormalBasis ι Real E) (f : 𝓢'(E, F)) :
    Δ f = ∑ i, ∂_{b i} (∂_{b i} f) := LineDeriv.laplacianCLM_eq_sum b f

@[simp]
/--
theorem `laplacian_apply_apply` / 定理 `laplacian_apply_apply`

English:
theorem laplacian_apply_apply
  given: (f : 𝓢'(E, F)) (u : 𝓢(E, Complex))
  statement: (Δ f) u = f (Δ u)
  proof: by
  simp [laplacian_eq_sum (stdOrthonormalBasis Real E),
    SchwartzMap.laplacian_eq_sum (stdOrthonormalBasis Real E), map_neg, neg_neg]

中文:
定理 laplacian_apply_apply
  条件: (f : 𝓢'(E, F)) (u : 𝓢(E, Complex))
  结论: (Δ f) u = f (Δ u)
  证明: by
  simp [laplacian_eq_sum (stdOrthonormalBasis Real E),
    SchwartzMap.laplacian_eq_sum (stdOrthonormalBasis Real E), map_neg, neg_neg]

Depends on / 依赖: SchwartzMap, SchwartzMap.laplacian_eq_sum, laplacian_eq_sum, map_neg, neg_neg, stdOrthonormalBasis
-/
theorem laplacian_apply_apply (f : 𝓢'(E, F)) (u : 𝓢(E, Complex)) : (Δ f) u = f (Δ u) := by
  simp [laplacian_eq_sum (stdOrthonormalBasis Real E),
    SchwartzMap.laplacian_eq_sum (stdOrthonormalBasis Real E), map_neg, neg_neg]

variable [MeasurableSpace E] [BorelSpace E]

/-- The distributional Laplacian and the classical Laplacian coincide on `𝓢(E, F)`. -/
@[simp]
/--
theorem `laplacian_toTemperedDistributionCLM_eq` / 定理 `laplacian_toTemperedDistributionCLM_eq`

English:
theorem laplacian_toTemperedDistributionCLM_eq
  given: (f : 𝓢(E, F))
  proof: by
  ext u
  simp [SchwartzMap.integral_smul_laplacian_right_eq_left]

中文:
定理 laplacian_toTemperedDistributionCLM_eq
  条件: (f : 𝓢(E, F))
  证明: by
  ext u
  simp [SchwartzMap.integral_smul_laplacian_right_eq_left]

Depends on / 依赖: SchwartzMap, SchwartzMap.integral_smul_laplacian_right_eq_left, integral_smul_laplacian_right_eq_left
-/
theorem laplacian_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) :
    Δ (f : 𝓢'(E, F)) = Δ f := by
  ext u
  simp [SchwartzMap.integral_smul_laplacian_right_eq_left]

end Laplacian

/-! ### Fourier transform -/

section Fourier

open FourierTransform

variable [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

section TVS

variable [AddCommGroup F] [Module Complex F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul Complex F]

/--
Instance `instFourierTransform` / 实例 `instFourierTransform`

English:
instance instFourierTransform
  signature: : FourierTransform 𝓢'(E, F) 𝓢'(E, F) where
  body: PointwiseConvergenceCLM.precomp F (fourierCLM Complex 𝓢(E, Complex))

中文:
实例 instFourierTransform
  签名: : FourierTransform 𝓢'(E, F) 𝓢'(E, F) where
  定义体: PointwiseConvergenceCLM.precomp F (fourierCLM Complex 𝓢(E, Complex))

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.precomp, fourierCLM, precomp
-/
instance instFourierTransform : FourierTransform 𝓢'(E, F) 𝓢'(E, F) where
  fourier := PointwiseConvergenceCLM.precomp F (fourierCLM Complex 𝓢(E, Complex))

/--
Instance `instFourierAdd` / 实例 `instFourierAdd`

English:
instance instFourierAdd
  signature: : FourierAdd 𝓢'(E, F) 𝓢'(E, F) where
  body: (PointwiseConvergenceCLM.precomp F (fourierCLM Complex 𝓢(E, Complex))).map_add

中文:
实例 instFourierAdd
  签名: : FourierAdd 𝓢'(E, F) 𝓢'(E, F) where
  定义体: (PointwiseConvergenceCLM.precomp F (fourierCLM Complex 𝓢(E, Complex))).map_add

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.precomp, fourierCLM, map_add, precomp
-/
instance instFourierAdd : FourierAdd 𝓢'(E, F) 𝓢'(E, F) where
  fourier_add := (PointwiseConvergenceCLM.precomp F (fourierCLM Complex 𝓢(E, Complex))).map_add

/--
Instance `instFourierSMul` / 实例 `instFourierSMul`

English:
instance instFourierSMul
  signature: : FourierSMul Complex 𝓢'(E, F) 𝓢'(E, F) where
  body: (PointwiseConvergenceCLM.precomp F (fourierCLM Complex 𝓢(E, Complex))).map_smul

中文:
实例 instFourierSMul
  签名: : FourierSMul Complex 𝓢'(E, F) 𝓢'(E, F) where
  定义体: (PointwiseConvergenceCLM.precomp F (fourierCLM Complex 𝓢(E, Complex))).map_smul

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.precomp, fourierCLM, map_smul, precomp
-/
instance instFourierSMul : FourierSMul Complex 𝓢'(E, F) 𝓢'(E, F) where
  fourier_smul := (PointwiseConvergenceCLM.precomp F (fourierCLM Complex 𝓢(E, Complex))).map_smul

/--
Instance `instContinuousFourier` / 实例 `instContinuousFourier`

English:
instance instContinuousFourier
  signature: : ContinuousFourier 𝓢'(E, F) 𝓢'(E, F) where
  body: (PointwiseConvergenceCLM.precomp F (fourierCLM Complex 𝓢(E, Complex))).cont

@[simp]

中文:
实例 instContinuousFourier
  签名: : ContinuousFourier 𝓢'(E, F) 𝓢'(E, F) where
  定义体: (PointwiseConvergenceCLM.precomp F (fourierCLM Complex 𝓢(E, Complex))).cont

@[simp]

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.precomp, fourierCLM, precomp
-/
instance instContinuousFourier : ContinuousFourier 𝓢'(E, F) 𝓢'(E, F) where
  continuous_fourier := (PointwiseConvergenceCLM.precomp F (fourierCLM Complex 𝓢(E, Complex))).cont

@[simp]
/--
theorem `fourier_apply` / 定理 `fourier_apply`

English:
theorem fourier_apply
  given: (f : 𝓢'(E, F)) (g : 𝓢(E, Complex))
  statement: 𝓕 f g = f (𝓕 g)
  proof: rfl

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLM := FourierTransform.fourierCLM

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLM_apply := FourierTransform.fourierCLM_apply

@[deprecated (since := "2026-01-06")]
alias fourierTransform_apply := fourier_apply

中文:
定理 fourier_apply
  条件: (f : 𝓢'(E, F)) (g : 𝓢(E, Complex))
  结论: 𝓕 f g = f (𝓕 g)
  证明: rfl

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLM := FourierTransform.fourierCLM

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLM_apply := FourierTransform.fourierCLM_apply

@[deprecated (since := "2026-01-06")]
alias fourierTransform_apply := fourier_apply
-/
theorem fourier_apply (f : 𝓢'(E, F)) (g : 𝓢(E, Complex)) : 𝓕 f g = f (𝓕 g) := rfl

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLM := FourierTransform.fourierCLM

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLM_apply := FourierTransform.fourierCLM_apply

@[deprecated (since := "2026-01-06")]
alias fourierTransform_apply := fourier_apply

/--
Instance `instFourierTransformInv` / 实例 `instFourierTransformInv`

English:
instance instFourierTransformInv
  signature: : FourierTransformInv 𝓢'(E, F) 𝓢'(E, F) where
  body: PointwiseConvergenceCLM.precomp F (fourierInvCLM Complex 𝓢(E, Complex))

中文:
实例 instFourierTransformInv
  签名: : FourierTransformInv 𝓢'(E, F) 𝓢'(E, F) where
  定义体: PointwiseConvergenceCLM.precomp F (fourierInvCLM Complex 𝓢(E, Complex))

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.precomp, fourierInvCLM, precomp
-/
instance instFourierTransformInv : FourierTransformInv 𝓢'(E, F) 𝓢'(E, F) where
  fourierInv := PointwiseConvergenceCLM.precomp F (fourierInvCLM Complex 𝓢(E, Complex))

/--
Instance `instFourierInvAdd` / 实例 `instFourierInvAdd`

English:
instance instFourierInvAdd
  signature: : FourierInvAdd 𝓢'(E, F) 𝓢'(E, F) where
  body: (PointwiseConvergenceCLM.precomp F (fourierInvCLM Complex 𝓢(E, Complex))).map_add

中文:
实例 instFourierInvAdd
  签名: : FourierInvAdd 𝓢'(E, F) 𝓢'(E, F) where
  定义体: (PointwiseConvergenceCLM.precomp F (fourierInvCLM Complex 𝓢(E, Complex))).map_add

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.precomp, fourierInvCLM, map_add, precomp
-/
instance instFourierInvAdd : FourierInvAdd 𝓢'(E, F) 𝓢'(E, F) where
  fourierInv_add := (PointwiseConvergenceCLM.precomp F (fourierInvCLM Complex 𝓢(E, Complex))).map_add

/--
Instance `instFourierInvSMul` / 实例 `instFourierInvSMul`

English:
instance instFourierInvSMul
  signature: : FourierInvSMul Complex 𝓢'(E, F) 𝓢'(E, F) where
  body: (PointwiseConvergenceCLM.precomp F (fourierInvCLM Complex 𝓢(E, Complex))).map_smul

中文:
实例 instFourierInvSMul
  签名: : FourierInvSMul Complex 𝓢'(E, F) 𝓢'(E, F) where
  定义体: (PointwiseConvergenceCLM.precomp F (fourierInvCLM Complex 𝓢(E, Complex))).map_smul

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.precomp, fourierInvCLM, map_smul, precomp
-/
instance instFourierInvSMul : FourierInvSMul Complex 𝓢'(E, F) 𝓢'(E, F) where
  fourierInv_smul := (PointwiseConvergenceCLM.precomp F (fourierInvCLM Complex 𝓢(E, Complex))).map_smul

/--
Instance `instContinuousFourierInv` / 实例 `instContinuousFourierInv`

English:
instance instContinuousFourierInv
  signature: : ContinuousFourierInv 𝓢'(E, F) 𝓢'(E, F) where
  body: (PointwiseConvergenceCLM.precomp F (fourierInvCLM Complex 𝓢(E, Complex))).cont

@[simp]

中文:
实例 instContinuousFourierInv
  签名: : ContinuousFourierInv 𝓢'(E, F) 𝓢'(E, F) where
  定义体: (PointwiseConvergenceCLM.precomp F (fourierInvCLM Complex 𝓢(E, Complex))).cont

@[simp]

Depends on / 依赖: PointwiseConvergenceCLM, PointwiseConvergenceCLM.precomp, fourierInvCLM, precomp
-/
instance instContinuousFourierInv : ContinuousFourierInv 𝓢'(E, F) 𝓢'(E, F) where
  continuous_fourierInv := (PointwiseConvergenceCLM.precomp F (fourierInvCLM Complex 𝓢(E, Complex))).cont

@[simp]
/--
theorem `fourierInv_apply` / 定理 `fourierInv_apply`

English:
theorem fourierInv_apply
  given: (f : 𝓢'(E, F)) (g : 𝓢(E, Complex))
  statement: 𝓕⁻ f g = f (𝓕⁻ g)
  proof: rfl

@[deprecated (since := "2026-01-06")]
alias fourierTransformInvCLM := FourierTransform.fourierInvCLM

@[deprecated (since := "2026-01-06")]
alias fourierTransformInvCLM_apply := FourierTransform.fourierInvCLM_apply

@[deprecated (since := "2026-01-06")]
alias fourierTransformInv_apply := fourie

中文:
定理 fourierInv_apply
  条件: (f : 𝓢'(E, F)) (g : 𝓢(E, Complex))
  结论: 𝓕⁻ f g = f (𝓕⁻ g)
  证明: rfl

@[deprecated (since := "2026-01-06")]
alias fourierTransformInvCLM := FourierTransform.fourierInvCLM

@[deprecated (since := "2026-01-06")]
alias fourierTransformInvCLM_apply := FourierTransform.fourierInvCLM_apply

@[deprecated (since := "2026-01-06")]
alias fourierTransformInv_apply := fourie
-/
theorem fourierInv_apply (f : 𝓢'(E, F)) (g : 𝓢(E, Complex)) : 𝓕⁻ f g = f (𝓕⁻ g) := rfl

@[deprecated (since := "2026-01-06")]
alias fourierTransformInvCLM := FourierTransform.fourierInvCLM

@[deprecated (since := "2026-01-06")]
alias fourierTransformInvCLM_apply := FourierTransform.fourierInvCLM_apply

@[deprecated (since := "2026-01-06")]
alias fourierTransformInv_apply := fourierInv_apply

/--
Instance `instFourierPair` / 实例 `instFourierPair`

English:
instance instFourierPair
  signature: : FourierPair 𝓢'(E, F) 𝓢'(E, F) where
  body: by ext; simp

中文:
实例 instFourierPair
  签名: : FourierPair 𝓢'(E, F) 𝓢'(E, F) where
  定义体: by ext; simp
-/
instance instFourierPair : FourierPair 𝓢'(E, F) 𝓢'(E, F) where
  fourierInv_fourier_eq f := by ext; simp

/--
Instance `instFourierPairInv` / 实例 `instFourierPairInv`

English:
instance instFourierPairInv
  signature: : FourierInvPair 𝓢'(E, F) 𝓢'(E, F) where
  body: by ext; simp

中文:
实例 instFourierPairInv
  签名: : FourierInvPair 𝓢'(E, F) 𝓢'(E, F) where
  定义体: by ext; simp
-/
instance instFourierPairInv : FourierInvPair 𝓢'(E, F) 𝓢'(E, F) where
  fourier_fourierInv_eq f := by ext; simp

end TVS

section embedding

variable [NormedAddCommGroup F] [NormedSpace Complex F] [CompleteSpace F]

/--
theorem `fourier_toTemperedDistributionCLM_eq` / 定理 `fourier_toTemperedDistributionCLM_eq`

English:
theorem fourier_toTemperedDistributionCLM_eq
  given: (f : 𝓢(E, F))
  proof: by
  ext g
  simpa using integral_fourier_smul_eq g f

@[deprecated (since := "2026-01-14")]
alias fourierTransform_toTemperedDistributionCLM_eq := fourier_toTemperedDistributionCLM_eq

中文:
定理 fourier_toTemperedDistributionCLM_eq
  条件: (f : 𝓢(E, F))
  证明: by
  ext g
  simpa using integral_fourier_smul_eq g f

@[deprecated (since := "2026-01-14")]
alias fourierTransform_toTemperedDistributionCLM_eq := fourier_toTemperedDistributionCLM_eq

Depends on / 依赖: integral_fourier_smul_eq
-/
theorem fourier_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) :
    𝓕 (f : 𝓢'(E, F)) = 𝓕 f := by
  ext g
  simpa using integral_fourier_smul_eq g f

@[deprecated (since := "2026-01-14")]
alias fourierTransform_toTemperedDistributionCLM_eq := fourier_toTemperedDistributionCLM_eq

/--
theorem `fourierInv_toTemperedDistributionCLM_eq` / 定理 `fourierInv_toTemperedDistributionCLM_eq`

English:
theorem fourierInv_toTemperedDistributionCLM_eq
  given: (f : 𝓢(E, F))
  proof: calc
  _ = 𝓕⁻ (toTemperedDistributionCLM E F volume (𝓕 (𝓕⁻ f))) := by
    congr; exact (fourier_fourierInv_eq f).symm
  _ = 𝓕⁻ (𝓕 (toTemperedDistributionCLM E F volume (𝓕⁻ f))) := by
    rw [fourier_toTemperedDistributionCLM_eq]
  _ = _ := fourierInv_fourier_eq _

@[deprecated (since := "2026-01-14"

中文:
定理 fourierInv_toTemperedDistributionCLM_eq
  条件: (f : 𝓢(E, F))
  证明: calc
  _ = 𝓕⁻ (toTemperedDistributionCLM E F volume (𝓕 (𝓕⁻ f))) := by
    congr; exact (fourier_fourierInv_eq f).symm
  _ = 𝓕⁻ (𝓕 (toTemperedDistributionCLM E F volume (𝓕⁻ f))) := by
    rw [fourier_toTemperedDistributionCLM_eq]
  _ = _ := fourierInv_fourier_eq _

@[deprecated (since := "2026-01-14"
-/
theorem fourierInv_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) :
    𝓕⁻ (f : 𝓢'(E, F)) = 𝓕⁻ f := calc
  _ = 𝓕⁻ (toTemperedDistributionCLM E F volume (𝓕 (𝓕⁻ f))) := by
    congr; exact (fourier_fourierInv_eq f).symm
  _ = 𝓕⁻ (𝓕 (toTemperedDistributionCLM E F volume (𝓕⁻ f))) := by
    rw [fourier_toTemperedDistributionCLM_eq]
  _ = _ := fourierInv_fourier_eq _

@[deprecated (since := "2026-01-14")]
alias fourierTransformInv_toTemperedDistributionCLM_eq := fourierInv_toTemperedDistributionCLM_eq

end embedding

open LineDeriv Real

variable [NormedAddCommGroup F] [NormedSpace Complex F]

/--
theorem `lineDerivOp_fourier_eq` / 定理 `lineDerivOp_fourier_eq`

English:
theorem lineDerivOp_fourier_eq
  given: (f : 𝓢'(E, F)) (m : E)
  proof: by
  ext u
  have : (inner Real · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.fourier_lineDerivOp_eq, ← smulLeftCLM_ofReal Complex this]

中文:
定理 lineDerivOp_fourier_eq
  条件: (f : 𝓢'(E, F)) (m : E)
  证明: by
  ext u
  have : (inner Real · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.fourier_lineDerivOp_eq, ← smulLeftCLM_ofReal Complex this]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, HasTemperateGrowth, SchwartzMap, SchwartzMap.fourier_lineDerivOp_eq, SemiNormedGrp, fourier_lineDerivOp_eq, fun_prop, smulLeftCLM_ofReal
-/
theorem lineDerivOp_fourier_eq (f : 𝓢'(E, F)) (m : E) :
    ∂_{m} (𝓕 f) = 𝓕 (- (2 * π * Complex.I) • smulLeftCLM F (inner Real · m) f) := by
  ext u
  have : (inner Real · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.fourier_lineDerivOp_eq, ← smulLeftCLM_ofReal Complex this]

/--
theorem `fourier_lineDerivOp_eq` / 定理 `fourier_lineDerivOp_eq`

English:
theorem fourier_lineDerivOp_eq
  given: (f : 𝓢'(E, F)) (m : E)
  proof: by
  ext u
  have : (inner Real · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.lineDerivOp_fourier_eq, ← smulLeftCLM_ofReal Complex this]

中文:
定理 fourier_lineDerivOp_eq
  条件: (f : 𝓢'(E, F)) (m : E)
  证明: by
  ext u
  have : (inner Real · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.lineDerivOp_fourier_eq, ← smulLeftCLM_ofReal Complex this]

Depends on / 依赖: HasTemperateGrowth, SchwartzMap, SchwartzMap.lineDerivOp_fourier_eq, fun_prop, lineDerivOp_fourier_eq, smulLeftCLM_ofReal
-/
theorem fourier_lineDerivOp_eq (f : 𝓢'(E, F)) (m : E) :
    𝓕 (∂_{m} f) = (2 * π * Complex.I) • smulLeftCLM F (inner Real · m) (𝓕 f) := by
  ext u
  have : (inner Real · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.lineDerivOp_fourier_eq, ← smulLeftCLM_ofReal Complex this]

/--
theorem `lineDerivOp_fourierInv_eq` / 定理 `lineDerivOp_fourierInv_eq`

English:
theorem lineDerivOp_fourierInv_eq
  given: (f : 𝓢'(E, F)) (m : E)
  proof: by
  ext u
  have : (inner Real · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.fourierInv_lineDerivOp_eq, ← smulLeftCLM_ofReal Complex this]

中文:
定理 lineDerivOp_fourierInv_eq
  条件: (f : 𝓢'(E, F)) (m : E)
  证明: by
  ext u
  have : (inner Real · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.fourierInv_lineDerivOp_eq, ← smulLeftCLM_ofReal Complex this]

Depends on / 依赖: HasTemperateGrowth, SchwartzMap, SchwartzMap.fourierInv_lineDerivOp_eq, f.hom, fourierInv_lineDerivOp_eq, fun_prop, smulLeftCLM_ofReal
-/
theorem lineDerivOp_fourierInv_eq (f : 𝓢'(E, F)) (m : E) :
    ∂_{m} (𝓕⁻ f) = 𝓕⁻ ((2 * π * Complex.I) • smulLeftCLM F (inner Real · m) f) := by
  ext u
  have : (inner Real · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.fourierInv_lineDerivOp_eq, ← smulLeftCLM_ofReal Complex this]

/--
theorem `fourierInv_lineDerivOp_eq` / 定理 `fourierInv_lineDerivOp_eq`

English:
theorem fourierInv_lineDerivOp_eq
  given: (f : 𝓢'(E, F)) (m : E)
  proof: by
  ext u
  have : (inner Real · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.lineDerivOp_fourierInv_eq, ← smulLeftCLM_ofReal Complex this]

中文:
定理 fourierInv_lineDerivOp_eq
  条件: (f : 𝓢'(E, F)) (m : E)
  证明: by
  ext u
  have : (inner Real · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.lineDerivOp_fourierInv_eq, ← smulLeftCLM_ofReal Complex this]

Depends on / 依赖: HasTemperateGrowth, SchwartzMap, SchwartzMap.lineDerivOp_fourierInv_eq, fun_prop, lineDerivOp_fourierInv_eq, smulLeftCLM_ofReal
-/
theorem fourierInv_lineDerivOp_eq (f : 𝓢'(E, F)) (m : E) :
    𝓕⁻ (∂_{m} f) = -(2 * π * Complex.I) • smulLeftCLM F (inner Real · m) (𝓕⁻ f) := by
  ext u
  have : (inner Real · m).HasTemperateGrowth := by fun_prop
  simp [SchwartzMap.lineDerivOp_fourierInv_eq, ← smulLeftCLM_ofReal Complex this]

end Fourier

section DiracDelta

variable [NormedAddCommGroup E]

section definition

variable [NormedSpace Real E]

/--
Definition of `delta` / `delta` 的定义

English:
definition delta
  signature: (x : E)
  body: toPointwiseConvergenceCLM _ _ _ _
    (BoundedContinuousFunction.evalCLM Complex x).comp (toBoundedContinuousFunctionCLM Complex E Complex)

@[simp]

中文:
定义 delta
  签名: (x : E)
  定义体: toPointwiseConvergenceCLM _ _ _ _
    (BoundedContinuousFunction.evalCLM Complex x).comp (toBoundedContinuousFunctionCLM Complex E Complex)

@[simp]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.evalCLM, evalCLM, toBoundedContinuousFunctionCLM, toPointwiseConvergenceCLM
-/
def delta (x : E) : 𝓢'(E, Complex) :=
toPointwiseConvergenceCLM _ _ _ _
    (BoundedContinuousFunction.evalCLM Complex x).comp (toBoundedContinuousFunctionCLM Complex E Complex)

@[simp]
/--
theorem `delta_apply` / 定理 `delta_apply`

English:
theorem delta_apply
  given: (x : E) (f : 𝓢(E, Complex))
  statement: delta x f = f x
  proof: rfl

中文:
定理 delta_apply
  条件: (x : E) (f : 𝓢(E, Complex))
  结论: delta x f = f x
  证明: rfl
-/
theorem delta_apply (x : E) (f : 𝓢(E, Complex)) : delta x f = f x :=
  rfl

open MeasureTheory MeasureTheory.Measure

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Dirac measure considered as a tempered distribution is the delta distribution. -/
@[simp]
/--
theorem `toTemperedDistribution_dirac_eq_delta` / 定理 `toTemperedDistribution_dirac_eq_delta`

English:
theorem toTemperedDistribution_dirac_eq_delta
  given: (x : E)
  proof: by aesop

中文:
定理 toTemperedDistribution_dirac_eq_delta
  条件: (x : E)
  证明: by aesop
-/
theorem toTemperedDistribution_dirac_eq_delta (x : E) :
  (dirac x).toTemperedDistribution = delta x := by aesop

end definition

variable [InnerProductSpace Real E] [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform

/--
theorem `fourier_delta_zero` / 定理 `fourier_delta_zero`

English:
theorem fourier_delta_zero
  statement: 𝓕 (delta (0 : E)) = volume.toTemperedDistribution
  proof: by
  ext f
  simp [SchwartzMap.fourier_coe, Real.fourier_eq]

中文:
定理 fourier_delta_zero
  结论: 𝓕 (delta (0 : E)) = volume.toTemperedDistribution
  证明: by
  ext f
  simp [SchwartzMap.fourier_coe, Real.fourier_eq]

Depends on / 依赖: Real.fourier_eq, SchwartzMap, SchwartzMap.fourier_coe, fourier_coe, fourier_eq
-/
theorem fourier_delta_zero : 𝓕 (delta (0 : E)) = volume.toTemperedDistribution := by
  ext f
  simp [SchwartzMap.fourier_coe, Real.fourier_eq]

end DiracDelta

end TemperedDistribution
