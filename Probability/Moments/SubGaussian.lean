/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Condexp
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.Tilted

/-!
# Sub-Gaussian random variables

This presentation of sub-Gaussian random variables is inspired by section 2.5 of
[vershynin2018high]. Let `X` be a random variable. Consider the following five properties, in which
`Kᵢ` are positive reals,
* (i) for all `t ≥ 0`, `ℙ(|X| ≥ t) ≤ 2 * exp(-t^2 / K₁^2)`,
* (ii) for all `p : ℕ` with `1 ≤ p`, `𝔼[|X|^p]^(1/p) ≤ K₂ sqrt(p)`,
* (iii) for all `|t| ≤ 1/K₃`, `𝔼[exp (t^2 * X^2)] ≤ exp (K₃^2 * t^2)`,
* (iv) `𝔼[exp(X^2 / K₄)] ≤ 2`,
* (v) for all `t : ℝ`, `𝔼[exp (t * X)] ≤ exp (K₅ * t^2 / 2)`.

Properties (i) to (iv) are equivalent, in the sense that there exists a constant `C` such that
if `X` satisfies one of those properties with constant `K`, then it satisfies any other one with
constant at most `CK`.

If `𝔼[X] = 0` then properties (i)-(iv) are equivalent to (v) in that same sense.
Property (v) implies that `X` has expectation zero.

The name sub-Gaussian is used by various authors to refer to any one of (i)-(v). We will say that a
random variable has sub-Gaussian moment-generating function (mgf) with constant `K₅` to mean that
property (v) holds with that constant. The function `exp (K₅ * t^2 / 2)` which appears in
property (v) is the mgf of a Gaussian with variance `K₅`.
That property (v) is the most convenient one to work with if one wants to prove concentration
inequalities using Chernoff's method.

TODO: implement definitions for (i)-(iv) when it makes sense. For example the maximal constant `K₄`
such that (iv) is true is an Orlicz norm. Prove relations between those properties.

### Conditionally sub-Gaussian random variables and kernels

A related notion to sub-Gaussian random variables is that of conditionally sub-Gaussian random
variables. A random variable `X` is conditionally sub-Gaussian in the sense of (v) with respect to
a sigma-algebra `m` and a measure `μ` if for all `t : ℝ`, `exp (t * X)` is `μ`-integrable and
the conditional mgf of `X` conditioned on `m` is almost surely bounded by `exp (c * t^2 / 2)`
for some constant `c`.

As in other parts of Mathlib's probability library (notably the independence and conditional
independence definitions), we express both sub-Gaussian and conditionally sub-Gaussian properties
as special cases of a notion of sub-Gaussianity with respect to a kernel and a measure.

## Main definitions

* `Kernel.HasSubgaussianMGF`: a random variable `X` has a sub-Gaussian moment-generating function
  with parameter `c` with respect to a kernel `κ` and a measure `ν` if for `ν`-almost all `ω'`,
  for all `t : ℝ`, the moment-generating function of `X` with respect to `κ ω'` is bounded by
  `exp (c * t ^ 2 / 2)`.
* `HasCondSubgaussianMGF`: a random variable `X` has a conditionally sub-Gaussian moment-generating
  function with parameter `c` with respect to a sigma-algebra `m` and a measure `μ` if for all
  `t : ℝ`, `exp (t * X)` is `μ`-integrable and the moment-generating function of `X` conditioned
  on `m` is almost surely bounded by `exp (c * t ^ 2 / 2)` for all `t : ℝ`.
  The actual definition uses `Kernel.HasSubgaussianMGF`: `HasCondSubgaussianMGF` is defined as
  sub-Gaussian with respect to the conditional expectation kernel for `m` and the restriction of `μ`
  to the sigma-algebra `m`.
* `HasSubgaussianMGF`: a random variable `X` has a sub-Gaussian moment-generating function
  with parameter `c` with respect to a measure `μ` if for all `t : ℝ`, `exp (t * X)`
  is `μ`-integrable and the moment-generating function of `X` is bounded by `exp (c * t ^ 2 / 2)`
  for all `t : ℝ`.
  This is equivalent to `Kernel.HasSubgaussianMGF` with a constant kernel.
  See `HasSubgaussianMGF_iff_kernel`.

## Main statements

* `measure_sum_ge_le_of_iIndepFun`: Hoeffding's inequality for sums of independent sub-Gaussian
  random variables.
* `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`: Hoeffding's lemma for random variables with
  expectation zero.
* `measure_sum_ge_le_of_HasCondSubgaussianMGF`: the Azuma-Hoeffding inequality for sub-Gaussian
  random variables.

## Implementation notes

### Definition of `Kernel.HasSubgaussianMGF`

The definition of sub-Gaussian with respect to a kernel and a measure is the following:
```
structure Kernel.HasSubgaussianMGF (X : Ω → ℝ) (c : ℝ≥0)
    (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν)
  mgf_le : ∀ᵐ ω' ∂ν, ∀ t, mgf X (κ ω') t ≤ exp (c * t ^ 2 / 2)
```
An interesting point is that the integrability condition is not integrability of `exp (t * X)`
with respect to `κ ω'` for `ν`-almost all `ω'`, but integrability with respect to `κ ∘ₘ ν`.
This is a stronger condition, as the weaker one did not allow to prove interesting results about
the sum of two sub-Gaussian random variables.

For the conditional case, that integrability condition reduces to integrability of `exp (t * X)`
with respect to `μ`.

### Definition of `HasCondSubgaussianMGF`

We define `HasCondSubgaussianMGF` as a special case of `Kernel.HasSubgaussianMGF` with the
conditional expectation kernel for `m`, `condExpKernel μ m`, and the restriction of `μ` to `m`,
`μ.trim hm` (where `hm` states that `m` is a sub-sigma-algebra).
Note that `condExpKernel μ m ∘ₘ μ.trim hm = μ`. The definition is equivalent to the two
conditions
* for all `t`, `exp (t * X)` is `μ`-integrable,
* for `μ.trim hm`-almost all `ω`, for all `t`, the mgf with respect to the conditional
  distribution `condExpKernel μ m ω` is bounded by `exp (c * t ^ 2 / 2)`.

For any `t`, we can write the mgf of `X` with respect to the conditional expectation kernel as
a conditional expectation, `(μ.trim hm)`-almost surely:
`mgf X (condExpKernel μ m ·) t =ᵐ[μ.trim hm] μ[fun ω' ↦ exp (t * X ω') | m]`.

## References

* [R. Vershynin, *High-dimensional probability: An introduction with applications in data
  science*][vershynin2018high]

-/

@[expose] public section

open MeasureTheory Real

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

section Kernel

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {ν : Measure Ω'} {κ : Kernel Ω' Ω} {X : Ω -> Real} {c : Real>=0}

/-! ### Sub-Gaussian with respect to a kernel and a measure -/

/--
Definition of `Kernel.HasSubgaussianMGF` / `Kernel.HasSubgaussianMGF` 的定义

English:
structure Kernel.HasSubgaussianMGF
  parameters: (X : Ω -> Real) (c : Real>=0)
  axioms and operations (2):
    - integrable_exp_mul : forall t, Integrable (fun ω => exp (t * X ω)) (κ ∘ₘ ν)
    - mgf_le : forallᵐ ω' ∂ν, forall t, mgf X (κ ω') t <= exp (c * t ^ 2 / 2)

中文:
结构 Kernel.HasSubgaussianMGF
  参数: (X : Ω -> 实数) (c : 实数>=0)
  公理与运算 (2 个):
    - integrable_exp_mul : 对任意 t, 整数egrable (fun ω => exp (t * X ω)) (κ ∘ₘ ν)
    - mgf_le : 对任意ᵐ ω' ∂ν, 对任意 t, mgf X (κ ω') t <= exp (c * t ^ 2 / 2)
-/
structure Kernel.HasSubgaussianMGF (X : Ω -> Real) (c : Real>=0)
    (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  integrable_exp_mul : forall t, Integrable (fun ω => exp (t * X ω)) (κ ∘ₘ ν)
  mgf_le : forallᵐ ω' ∂ν, forall t, mgf X (κ ω') t <= exp (c * t ^ 2 / 2)

namespace Kernel.HasSubgaussianMGF

section BasicProperties

/--
lemma `aestronglyMeasurable` / 引理 `aestronglyMeasurable`

English:
lemma aestronglyMeasurable
  given: (h : HasSubgaussianMGF X c κ ν)
  proof: by
  have h_int := h.integrable_exp_mul 1
  simpa using (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

中文:
引理 aestronglyMeasurable
  条件: (h : HasSubgaussianMGF X c κ ν)
  证明: by
  have h_int := h.integrable_exp_mul 1
  simpa using (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

Depends on / 依赖: aemeasurable, aemeasurable_of_aemeasurable_exp, aestronglyMeasurable, h.integrable_exp_mul, h_int, integrable_exp_mul
-/
lemma aestronglyMeasurable (h : HasSubgaussianMGF X c κ ν) :
    AEStronglyMeasurable X (κ ∘ₘ ν) := by
  have h_int := h.integrable_exp_mul 1
  simpa using (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

/--
lemma `ae_integrable_exp_mul` / 引理 `ae_integrable_exp_mul`

English:
lemma ae_integrable_exp_mul
  given: (h : HasSubgaussianMGF X c κ ν) (t : Real)
  proof: Measure.ae_integrable_of_integrable_comp (h.integrable_exp_mul t)

中文:
引理 ae_integrable_exp_mul
  条件: (h : HasSubgaussianMGF X c κ ν) (t : 实数)
  证明: Measure.ae_integrable_of_integrable_comp (h.integrable_exp_mul t)

Depends on / 依赖: Measure, Measure.ae_integrable_of_integrable_comp, ae_integrable_of_integrable_comp, h.integrable_exp_mul, integrable_exp_mul
-/
lemma ae_integrable_exp_mul (h : HasSubgaussianMGF X c κ ν) (t : Real) :
    forallᵐ ω' ∂ν, Integrable (fun y => exp (t * X y)) (κ ω') :=
  Measure.ae_integrable_of_integrable_comp (h.integrable_exp_mul t)

/--
lemma `ae_aestronglyMeasurable` / 引理 `ae_aestronglyMeasurable`

English:
lemma ae_aestronglyMeasurable
  given: (h : HasSubgaussianMGF X c κ ν)
  proof: by
  have h_int := h.ae_integrable_exp_mul 1
  filter_upwards [h_int] with ω h_int
  simpa using (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

中文:
引理 ae_aestronglyMeasurable
  条件: (h : HasSubgaussianMGF X c κ ν)
  证明: by
  have h_int := h.ae_integrable_exp_mul 1
  filter_upwards [h_int] with ω h_int
  simpa using (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

Depends on / 依赖: ae_integrable_exp_mul, aemeasurable, aemeasurable_of_aemeasurable_exp, aestronglyMeasurable, filter_upwards, h.ae_integrable_exp_mul, h_int
-/
lemma ae_aestronglyMeasurable (h : HasSubgaussianMGF X c κ ν) :
    forallᵐ ω' ∂ν, AEStronglyMeasurable X (κ ω') := by
  have h_int := h.ae_integrable_exp_mul 1
  filter_upwards [h_int] with ω h_int
  simpa using (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

/--
lemma `ae_forall_integrable_exp_mul` / 引理 `ae_forall_integrable_exp_mul`

English:
lemma ae_forall_integrable_exp_mul
  given: (h : HasSubgaussianMGF X c κ ν)
  proof: by
  have h_int (n : Int) : forallᵐ ω' ∂ν, Integrable (fun ω => exp (n * X ω)) (κ ω') :=
    h.ae_integrable_exp_mul _
  rw [← ae_all_iff] at h_int
  filter_upwards [h_int] with ω' h_int t
  exact integrable_exp_mul_of_le_of_le (h_int _) (h_int _) (Int.floor_le t) (Int.le_ceil t)

中文:
引理 ae_forall_integrable_exp_mul
  条件: (h : HasSubgaussianMGF X c κ ν)
  证明: by
  have h_int (n : Int) : forallᵐ ω' ∂ν, Integrable (fun ω => exp (n * X ω)) (κ ω') :=
    h.ae_integrable_exp_mul _
  rw [← ae_all_iff] at h_int
  filter_upwards [h_int] with ω' h_int t
  exact integrable_exp_mul_of_le_of_le (h_int _) (h_int _) (Int.floor_le t) (Int.le_ceil t)

Depends on / 依赖: Int.floor_le, Int.le_ceil, Integrable, ae_all_iff, ae_integrable_exp_mul, filter_upwards, floor_le, h.ae_integrable_exp_mul, h_int, integrable_exp_mul_of_le_of_le, le_ceil
-/
lemma ae_forall_integrable_exp_mul (h : HasSubgaussianMGF X c κ ν) :
    forallᵐ ω' ∂ν, forall t, Integrable (fun ω => exp (t * X ω)) (κ ω') := by
  have h_int (n : Int) : forallᵐ ω' ∂ν, Integrable (fun ω => exp (n * X ω)) (κ ω') :=
    h.ae_integrable_exp_mul _
  rw [← ae_all_iff] at h_int
  filter_upwards [h_int] with ω' h_int t
  exact integrable_exp_mul_of_le_of_le (h_int _) (h_int _) (Int.floor_le t) (Int.le_ceil t)

/--
lemma `ae_forall_memLp_exp_mul` / 引理 `ae_forall_memLp_exp_mul`

English:
lemma ae_forall_memLp_exp_mul
  given: (h : HasSubgaussianMGF X c κ ν) (p : Real>=0)
  proof: by
  filter_upwards [h.ae_forall_integrable_exp_mul] with ω' hi t
  constructor
  · exact (hi t).1
  · by_cases hp : p = 0
    · simp [hp]
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp) (by simp)]; rw [ENNReal.coe_toReal]
    have hf := (hi (p * t)).lintegral_lt_top
    convert

中文:
引理 ae_forall_memLp_exp_mul
  条件: (h : HasSubgaussianMGF X c κ ν) (p : 实数>=0)
  证明: by
  filter_upwards [h.ae_forall_integrable_exp_mul] with ω' hi t
  constructor
  · exact (hi t).1
  · by_cases hp : p = 0
    · simp [hp]
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp) (by simp)]; rw [ENNReal.coe_toReal]
    have hf := (hi (p * t)).lintegral_lt_top
    convert

Depends on / 依赖: ENNReal, ENNReal.coe_toReal, ENNReal.ofReal_rpow_of_nonneg, ae_forall_integrable_exp_mul, coe_toReal, convert, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top, enorm_eq_ofReal, exp_mul, filter_upwards, h.ae_forall_integrable_exp_mul, lintegral_lt_top, mod_cast, mul_assoc, mul_comm, ofReal_rpow_of_nonneg
-/
lemma ae_forall_memLp_exp_mul (h : HasSubgaussianMGF X c κ ν) (p : Real>=0) :
    forallᵐ ω' ∂ν, forall t, MemLp (fun ω => exp (t * X ω)) p (κ ω') := by
  filter_upwards [h.ae_forall_integrable_exp_mul] with ω' hi t
  constructor
  · exact (hi t).1
  · by_cases hp : p = 0
    · simp [hp]
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp) (by simp)]; rw [ENNReal.coe_toReal]
    have hf := (hi (p * t)).lintegral_lt_top
    convert! hf using 3 with ω
    rw [enorm_eq_ofReal (by positivity)]; rw [ENNReal.ofReal_rpow_of_nonneg (by positivity)]; rw [← exp_mul]; rw [mul_comm]; rw [← mul_assoc]
    positivity

/--
lemma `memLp_exp_mul` / 引理 `memLp_exp_mul`

English:
lemma memLp_exp_mul
  given: (h : HasSubgaussianMGF X c κ ν) (t : Real) (p : Real>=0)
  proof: by
  by_cases hp0 : p = 0
  · simpa [hp0] using (h.integrable_exp_mul t).1
  constructor
  · exact (h.integrable_exp_mul t).1
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp0) (by simp)]
    simp only [ENNReal.coe_toReal]
    have h' := (h.integrable_exp_mul (p * t)).2
    rw [ha

中文:
引理 memLp_exp_mul
  条件: (h : HasSubgaussianMGF X c κ ν) (t : 实数) (p : 实数>=0)
  证明: by
  by_cases hp0 : p = 0
  · simpa [hp0] using (h.integrable_exp_mul t).1
  constructor
  · exact (h.integrable_exp_mul t).1
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp0) (by simp)]
    simp only [ENNReal.coe_toReal]
    have h' := (h.integrable_exp_mul (p * t)).2
    rw [ha

Depends on / 依赖: ENNReal, ENNReal.coe_toReal, ENNReal.ofReal_rpow_of_nonneg, coe_toReal, convert, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top, enorm_eq_ofReal, exp_mul, h.integrable_exp_mul, hasFiniteIntegral_def, integrable_exp_mul, mod_cast, mul_comm, ofReal_rpow_of_nonneg
-/
lemma memLp_exp_mul (h : HasSubgaussianMGF X c κ ν) (t : Real) (p : Real>=0) :
    MemLp (fun ω => exp (t * X ω)) p (κ ∘ₘ ν) := by
  by_cases hp0 : p = 0
  · simpa [hp0] using (h.integrable_exp_mul t).1
  constructor
  · exact (h.integrable_exp_mul t).1
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp0) (by simp)]
    simp only [ENNReal.coe_toReal]
    have h' := (h.integrable_exp_mul (p * t)).2
    rw [hasFiniteIntegral_def] at h'
    convert! h' using 3 with ω
    rw [enorm_eq_ofReal (by positivity)]; rw [enorm_eq_ofReal (by positivity)]; rw [ENNReal.ofReal_rpow_of_nonneg (by positivity)]; rw [← exp_mul]; rw [mul_comm]; rw [← mul_assoc]
    positivity

/--
lemma `cgf_le` / 引理 `cgf_le`

English:
lemma cgf_le
  given: (h : HasSubgaussianMGF X c κ ν)
  proof: by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul] with ω' h h_int t
  calc cgf X (κ ω') t
  _ = log (mgf X (κ ω') t) := rfl
  _ <= log (exp (c * t ^ 2 / 2)) := by
    by_cases h0 : κ ω' = 0
    · simpa [h0] using by positivity
    gcongr
    · exact mgf_pos' h0 (h_int t)
    · exact h t

中文:
引理 cgf_le
  条件: (h : HasSubgaussianMGF X c κ ν)
  证明: by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul] with ω' h h_int t
  calc cgf X (κ ω') t
  _ = log (mgf X (κ ω') t) := rfl
  _ <= log (exp (c * t ^ 2 / 2)) := by
    by_cases h0 : κ ω' = 0
    · simpa [h0] using by positivity
    gcongr
    · exact mgf_pos' h0 (h_int t)
    · exact h t

Depends on / 依赖: ae_forall_integrable_exp_mul, filter_upwards, h.ae_forall_integrable_exp_mul, h.mgf_le, h_int, log_exp, mgf_le, mgf_pos
-/
lemma cgf_le (h : HasSubgaussianMGF X c κ ν) :
    forallᵐ ω' ∂ν, forall t, cgf X (κ ω') t <= c * t ^ 2 / 2 := by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul] with ω' h h_int t
  calc cgf X (κ ω') t
  _ = log (mgf X (κ ω') t) := rfl
  _ <= log (exp (c * t ^ 2 / 2)) := by
    by_cases h0 : κ ω' = 0
    · simpa [h0] using by positivity
    gcongr
    · exact mgf_pos' h0 (h_int t)
    · exact h t
  _ <= c * t ^ 2 / 2 := by rw [log_exp]

/--
lemma `isFiniteMeasure` / 引理 `isFiniteMeasure`

English:
lemma isFiniteMeasure
  given: (h : HasSubgaussianMGF X c κ ν)
  proof: by
  filter_upwards [h.ae_integrable_exp_mul 0, h.mgf_le] with ω' h h_mgf
  simpa [integrable_const_iff] using h

中文:
引理 isFiniteMeasure
  条件: (h : HasSubgaussianMGF X c κ ν)
  证明: by
  filter_upwards [h.ae_integrable_exp_mul 0, h.mgf_le] with ω' h h_mgf
  simpa [integrable_const_iff] using h

Depends on / 依赖: ae_integrable_exp_mul, filter_upwards, h.ae_integrable_exp_mul, h.mgf_le, h_mgf, integrable_const_iff, mgf_le
-/
lemma isFiniteMeasure (h : HasSubgaussianMGF X c κ ν) :
    forallᵐ ω' ∂ν, IsFiniteMeasure (κ ω') := by
  filter_upwards [h.ae_integrable_exp_mul 0, h.mgf_le] with ω' h h_mgf
  simpa [integrable_const_iff] using h

/--
lemma `measure_univ_le_one` / 引理 `measure_univ_le_one`

English:
lemma measure_univ_le_one
  given: (h : HasSubgaussianMGF X c κ ν)
  proof: by
  filter_upwards [h.isFiniteMeasure, h.mgf_le] with ω' h h_mgf
  suffices (κ ω').real Set.univ <= 1 by
    rwa [← ENNReal.ofReal_one, ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) zero_le_one]
  simpa [mgf] using h_mgf 0

中文:
引理 measure_univ_le_one
  条件: (h : HasSubgaussianMGF X c κ ν)
  证明: by
  filter_upwards [h.isFiniteMeasure, h.mgf_le] with ω' h h_mgf
  suffices (κ ω').real Set.univ <= 1 by
    rwa [← ENNReal.ofReal_one, ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) zero_le_one]
  simpa [mgf] using h_mgf 0

Depends on / 依赖: ENNReal, ENNReal.le_ofReal_iff_toReal_le, ENNReal.ofReal_one, Set.univ, filter_upwards, h.isFiniteMeasure, h.mgf_le, h_mgf, isFiniteMeasure, le_ofReal_iff_toReal_le, measure_ne_top, mgf_le, ofReal_one, zero_le_one
-/
lemma measure_univ_le_one (h : HasSubgaussianMGF X c κ ν) :
    forallᵐ ω' ∂ν, κ ω' Set.univ <= 1 := by
  filter_upwards [h.isFiniteMeasure, h.mgf_le] with ω' h h_mgf
  suffices (κ ω').real Set.univ <= 1 by
    rwa [← ENNReal.ofReal_one, ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) zero_le_one]
  simpa [mgf] using h_mgf 0

end BasicProperties

/--
lemma `of_rat` / 引理 `of_rat`

English:
lemma of_rat
  statement: (h_int : forall t : Real, Integrable (fun ω => exp (t * X ω)) (κ ∘ₘ ν))
  proof: h_int
  mgf_le := by
    rw [← ae_all_iff] at h_mgf
    have h_int : forallᵐ ω' ∂ν, forall t, Integrable (fun ω => exp (t * X ω)) (κ ω') := by
      have h_int' (n : Int) := Measure.ae_integrable_of_integrable_comp (h_int n)
      rw [← ae_all_iff] at h_int'
      filter_upwards [h_int'] with ω' h_i

中文:
引理 of_rat
  结论: (h_int : 对任意 t : 实数, 整数egrable (fun ω => exp (t * X ω)) (κ ∘ₘ ν))
  证明: h_int
  mgf_le := by
    rw [← ae_all_iff] at h_mgf
    have h_int : forallᵐ ω' ∂ν, forall t, Integrable (fun ω => exp (t * X ω)) (κ ω') := by
      have h_int' (n : Int) := Measure.ae_integrable_of_integrable_comp (h_int n)
      rw [← ae_all_iff] at h_int'
      filter_upwards [h_int'] with ω' h_i
-/
protected lemma of_rat (h_int : forall t : Real, Integrable (fun ω => exp (t * X ω)) (κ ∘ₘ ν))
    (h_mgf : forall q : Rat, forallᵐ ω' ∂ν, mgf X (κ ω') q <= exp (c * q ^ 2 / 2)) :
    Kernel.HasSubgaussianMGF X c κ ν where
  integrable_exp_mul := h_int
  mgf_le := by
    rw [← ae_all_iff] at h_mgf
    have h_int : forallᵐ ω' ∂ν, forall t, Integrable (fun ω => exp (t * X ω)) (κ ω') := by
      have h_int' (n : Int) := Measure.ae_integrable_of_integrable_comp (h_int n)
      rw [← ae_all_iff] at h_int'
      filter_upwards [h_int'] with ω' h_int t
      exact integrable_exp_mul_of_le_of_le (h_int _) (h_int _) (Int.floor_le t) (Int.le_ceil t)
    filter_upwards [h_mgf, h_int] with ω' h_mgf h_int t
    refine Rat.denseRange_cast.induction_on t ?_ h_mgf
    exact isClosed_le (continuous_mgf h_int) (by fun_prop)

@[simp]
/--
lemma `fun_zero` / 引理 `fun_zero`

English:
lemma fun_zero
  given: [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ]
  proof: by simp
  mgf_le := by simp

@[simp]

中文:
引理 fun_zero
  条件: [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ]
  证明: by simp
  mgf_le := by simp

@[simp]

Depends on / 依赖: mgf_le
-/
lemma fun_zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] :
    HasSubgaussianMGF (fun _ => 0) 0 κ ν where
  integrable_exp_mul := by simp
  mgf_le := by simp

@[simp]
/--
lemma `zero` / 引理 `zero`

English:
lemma zero
  given: [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ]
  statement: HasSubgaussianMGF 0 0 κ ν
  proof: fun_zero

@[simp]

中文:
引理 zero
  条件: [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ]
  结论: HasSubgaussianMGF 0 0 κ ν
  证明: fun_zero

@[simp]

Depends on / 依赖: fun_zero
-/
lemma zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] : HasSubgaussianMGF 0 0 κ ν := fun_zero

@[simp]
/--
lemma `zero_kernel` / 引理 `zero_kernel`

English:
lemma zero_kernel
  statement: HasSubgaussianMGF X c (0 : Kernel Ω' Ω) ν
  proof: by
  constructor
  · simp [FunLike.coe_zero]
  · simp [exp_nonneg]

@[simp]

中文:
引理 zero_kernel
  结论: HasSubgaussianMGF X c (0 : Kernel Ω' Ω) ν
  证明: by
  constructor
  · simp [FunLike.coe_zero]
  · simp [exp_nonneg]

@[simp]

Depends on / 依赖: FunLike, FunLike.coe_zero, coe_zero, exp_nonneg
-/
lemma zero_kernel : HasSubgaussianMGF X c (0 : Kernel Ω' Ω) ν := by
  constructor
  · simp [FunLike.coe_zero]
  · simp [exp_nonneg]

@[simp]
/--
lemma `zero_measure` / 引理 `zero_measure`

English:
lemma zero_measure
  statement: HasSubgaussianMGF X c κ (0 : Measure Ω')
  proof: ⟨by simp, by simp⟩

中文:
引理 zero_measure
  结论: HasSubgaussianMGF X c κ (0 : Measure Ω')
  证明: ⟨by simp, by simp⟩
-/
lemma zero_measure : HasSubgaussianMGF X c κ (0 : Measure Ω') := ⟨by simp, by simp⟩

/--
lemma `neg` / 引理 `neg`

English:
lemma neg
  given: {c : Real>=0} (h : HasSubgaussianMGF X c κ ν)
  statement: HasSubgaussianMGF (-X) c κ ν where
  proof: by simpa using h.integrable_exp_mul (-t)
  mgf_le := by filter_upwards [h.mgf_le] with ω' hm t using by simpa [mgf] using hm (-t)

中文:
引理 neg
  条件: {c : 实数>=0} (h : HasSubgaussianMGF X c κ ν)
  结论: HasSubgaussianMGF (-X) c κ ν where
  证明: by simpa using h.integrable_exp_mul (-t)
  mgf_le := by filter_upwards [h.mgf_le] with ω' hm t using by simpa [mgf] using hm (-t)

Depends on / 依赖: filter_upwards, h.integrable_exp_mul, h.mgf_le, integrable_exp_mul, mgf_le
-/
lemma neg {c : Real>=0} (h : HasSubgaussianMGF X c κ ν) : HasSubgaussianMGF (-X) c κ ν where
  integrable_exp_mul t := by simpa using h.integrable_exp_mul (-t)
  mgf_le := by filter_upwards [h.mgf_le] with ω' hm t using by simpa [mgf] using hm (-t)

/--
lemma `congr` / 引理 `congr`

English:
lemma congr
  given: {Y : Ω -> Real} (h : HasSubgaussianMGF X c κ ν) (h' : X =ᵐ[κ ∘ₘ ν] Y)
  proof: by
    refine (integrable_congr ?_).mpr (h.integrable_exp_mul t)
    filter_upwards [h'] with ω hω using by rw [hω]
  mgf_le := by
    have h'' := Measure.ae_ae_of_ae_comp h'
    filter_upwards [h.mgf_le, h''] with ω' h_mgf h' t
    rw [mgf_congr (Filter.EventuallyEq.symm h')]
    exact h_mgf t

中文:
引理 congr
  条件: {Y : Ω -> 实数} (h : HasSubgaussianMGF X c κ ν) (h' : X =ᵐ[κ ∘ₘ ν] Y)
  证明: by
    refine (integrable_congr ?_).mpr (h.integrable_exp_mul t)
    filter_upwards [h'] with ω hω using by rw [hω]
  mgf_le := by
    have h'' := Measure.ae_ae_of_ae_comp h'
    filter_upwards [h.mgf_le, h''] with ω' h_mgf h' t
    rw [mgf_congr (Filter.EventuallyEq.symm h')]
    exact h_mgf t

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.symm, Measure, Measure.ae_ae_of_ae_comp, ae_ae_of_ae_comp, filter_upwards, h.integrable_exp_mul, h.mgf_le, h_mgf, integrable_congr, integrable_exp_mul, mgf_congr, mgf_le
-/
lemma congr {Y : Ω -> Real} (h : HasSubgaussianMGF X c κ ν) (h' : X =ᵐ[κ ∘ₘ ν] Y) :
    HasSubgaussianMGF Y c κ ν where
  integrable_exp_mul t := by
    refine (integrable_congr ?_).mpr (h.integrable_exp_mul t)
    filter_upwards [h'] with ω hω using by rw [hω]
  mgf_le := by
    have h'' := Measure.ae_ae_of_ae_comp h'
    filter_upwards [h.mgf_le, h''] with ω' h_mgf h' t
    rw [mgf_congr (Filter.EventuallyEq.symm h')]
    exact h_mgf t

/--
lemma `_root_.ProbabilityTheory.Kernel.HasSubgaussianMGF_congr` / 引理 `_root_.ProbabilityTheory.Kernel.HasSubgaussianMGF_congr`

English:
lemma _root_.ProbabilityTheory.Kernel.HasSubgaussianMGF_congr
  given: {Y : Ω -> Real} (h : X =ᵐ[κ ∘ₘ ν] Y)
  proof: ⟨fun hX => congr hX h, fun hY => congr hY (ae_eq_symm h)⟩

中文:
引理 _root_.ProbabilityTheory.Kernel.HasSubgaussianMGF_congr
  条件: {Y : Ω -> 实数} (h : X =ᵐ[κ ∘ₘ ν] Y)
  证明: ⟨fun hX => congr hX h, fun hY => congr hY (ae_eq_symm h)⟩

Depends on / 依赖: ae_eq_symm
-/
lemma _root_.ProbabilityTheory.Kernel.HasSubgaussianMGF_congr {Y : Ω -> Real} (h : X =ᵐ[κ ∘ₘ ν] Y) :
    HasSubgaussianMGF X c κ ν ↔ HasSubgaussianMGF Y c κ ν :=
  ⟨fun hX => congr hX h, fun hY => congr hY (ae_eq_symm h)⟩

/--
lemma `of_map` / 引理 `of_map`

English:
lemma of_map
  statement: {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {κ : Kernel Ω' Ω''}
  proof: by
    have h1 := h.integrable_exp_mul t
    rwa [← Measure.map_comp _ _ hY, integrable_map_measure h1.aestronglyMeasurable (by fun_prop)]
      at h1
  mgf_le := by
    filter_upwards [h.ae_forall_integrable_exp_mul, h.mgf_le] with ω' h_int h_mgf t
    convert! h_mgf t
    ext t
    rw [map_apply _

中文:
引理 of_map
  结论: {Ω'' : 类型} {mΩ'' : MeasurableSpace Ω''} {κ : Kernel Ω' Ω''}
  证明: by
    have h1 := h.integrable_exp_mul t
    rwa [← Measure.map_comp _ _ hY, integrable_map_measure h1.aestronglyMeasurable (by fun_prop)]
      at h1
  mgf_le := by
    filter_upwards [h.ae_forall_integrable_exp_mul, h.mgf_le] with ω' h_int h_mgf t
    convert! h_mgf t
    ext t
    rw [map_apply _

Depends on / 依赖: Measure, Measure.map_comp, ae_forall_integrable_exp_mul, aemeasurable, aestronglyMeasurable, convert, filter_upwards, fun_prop, h.ae_forall_integrable_exp_mul, h.integrable_exp_mul, h.mgf_le, h1.aestronglyMeasurable, hY.aemeasurable, h_int, h_mgf, integrable_exp_mul, integrable_map_measure, map_apply, map_comp, mgf_le
-/
lemma of_map {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {κ : Kernel Ω' Ω''}
    {Y : Ω'' -> Ω} {X : Ω -> Real} (hY : Measurable Y) (h : HasSubgaussianMGF X c (κ.map Y) ν) :
    HasSubgaussianMGF (X ∘ Y) c κ ν where
  integrable_exp_mul t := by
    have h1 := h.integrable_exp_mul t
    rwa [← Measure.map_comp _ _ hY, integrable_map_measure h1.aestronglyMeasurable (by fun_prop)]
      at h1
  mgf_le := by
    filter_upwards [h.ae_forall_integrable_exp_mul, h.mgf_le] with ω' h_int h_mgf t
    convert! h_mgf t
    ext t
    rw [map_apply _ hY]; rw [mgf_map hY.aemeasurable]
    convert! (h_int t).1
    rw [map_apply _ hY]

/--
lemma `id_map_iff` / 引理 `id_map_iff`

English:
lemma id_map_iff
  given: (hX : Measurable X)
  proof: by
  refine ⟨fun h => ?_, fun h => ⟨fun t => ?_, ?_⟩⟩
  · change HasSubgaussianMGF (id ∘ X) c κ ν
    exact .of_map hX h
  · rw [← Kernel.deterministic_comp_eq_map hX, ← Measure.comp_assoc,
      Measure.deterministic_comp_eq_map, integrable_map_measure (by fun_prop) hX.aemeasurable]
    exact h.int

中文:
引理 id_map_iff
  条件: (hX : Measurable X)
  证明: by
  refine ⟨fun h => ?_, fun h => ⟨fun t => ?_, ?_⟩⟩
  · change HasSubgaussianMGF (id ∘ X) c κ ν
    exact .of_map hX h
  · rw [← Kernel.deterministic_comp_eq_map hX, ← Measure.comp_assoc,
      Measure.deterministic_comp_eq_map, integrable_map_measure (by fun_prop) hX.aemeasurable]
    exact h.int

Depends on / 依赖: HasSubgaussianMGF, Kernel, Kernel.deterministic_comp_eq_map, Kernel.map_apply, Measure, Measure.comp_assoc, Measure.deterministic_comp_eq_map, aemeasurable, comp_assoc, deterministic_comp_eq_map, fun_prop, h.integrable_exp_mul, h.mgf_le, hX.aemeasurable, integrable_exp_mul, integrable_map_measure, map_apply, mgf_id_map, mgf_le, of_map
-/
lemma id_map_iff (hX : Measurable X) :
    HasSubgaussianMGF id c (κ.map X) ν ↔ HasSubgaussianMGF X c κ ν := by
  refine ⟨fun h => ?_, fun h => ⟨fun t => ?_, ?_⟩⟩
  · change HasSubgaussianMGF (id ∘ X) c κ ν
    exact .of_map hX h
  · rw [← Kernel.deterministic_comp_eq_map hX, ← Measure.comp_assoc,
      Measure.deterministic_comp_eq_map, integrable_map_measure (by fun_prop) hX.aemeasurable]
    exact h.integrable_exp_mul t
  · simpa [Kernel.map_apply _ hX, mgf_id_map hX.aemeasurable] using h.mgf_le

/--
lemma `const_mul` / 引理 `const_mul`

English:
lemma const_mul
  given: (h : HasSubgaussianMGF X c κ ν) (r : Real)
  proof: by
    simp_rw [← mul_assoc]
    exact h.integrable_exp_mul (t * r)
  mgf_le := by
    filter_upwards [h.mgf_le] with ω hω t
    rw [mgf_const_mul]; rw [mul_comm]
    refine (hω (t * r)).trans_eq ?_
    congr 1
    simp only [NNReal.coe_mul, NNReal.coe_mk]
    ring

中文:
引理 const_mul
  条件: (h : HasSubgaussianMGF X c κ ν) (r : 实数)
  证明: by
    simp_rw [← mul_assoc]
    exact h.integrable_exp_mul (t * r)
  mgf_le := by
    filter_upwards [h.mgf_le] with ω hω t
    rw [mgf_const_mul]; rw [mul_comm]
    refine (hω (t * r)).trans_eq ?_
    congr 1
    simp only [NNReal.coe_mul, NNReal.coe_mk]
    ring
-/
protected lemma const_mul (h : HasSubgaussianMGF X c κ ν) (r : Real) :
    HasSubgaussianMGF (fun ω => r * X ω) (.mk (r ^ 2) (sq_nonneg r) * c) κ ν where
  integrable_exp_mul t := by
    simp_rw [← mul_assoc]
    exact h.integrable_exp_mul (t * r)
  mgf_le := by
    filter_upwards [h.mgf_le] with ω hω t
    rw [mgf_const_mul]; rw [mul_comm]
    refine (hω (t * r)).trans_eq ?_
    congr 1
    simp only [NNReal.coe_mul, NNReal.coe_mk]
    ring

section ChernoffBound

/--
lemma `measure_ge_le_exp_add` / 引理 `measure_ge_le_exp_add`

English:
lemma measure_ge_le_exp_add
  given: (h : HasSubgaussianMGF X c κ ν) (ε : Real)
  proof: by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul, h.isFiniteMeasure] with ω' h1 h2 _ t ht
  calc (κ ω').real {ω | ε <= X ω}
  _ <= exp (-t * ε) * mgf X (κ ω') t := measure_ge_le_exp_mul_mgf ε ht (h2 t)
  _ <= exp (-t * ε + c * t ^ 2 / 2) := by
    rw [exp_add]
    gcongr
    exact h1 t

中文:
引理 measure_ge_le_exp_add
  条件: (h : HasSubgaussianMGF X c κ ν) (ε : 实数)
  证明: by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul, h.isFiniteMeasure] with ω' h1 h2 _ t ht
  calc (κ ω').real {ω | ε <= X ω}
  _ <= exp (-t * ε) * mgf X (κ ω') t := measure_ge_le_exp_mul_mgf ε ht (h2 t)
  _ <= exp (-t * ε + c * t ^ 2 / 2) := by
    rw [exp_add]
    gcongr
    exact h1 t

Depends on / 依赖: ae_forall_integrable_exp_mul, exp_add, filter_upwards, h.ae_forall_integrable_exp_mul, h.isFiniteMeasure, h.mgf_le, isFiniteMeasure, measure_ge_le_exp_mul_mgf, mgf_le
-/
lemma measure_ge_le_exp_add (h : HasSubgaussianMGF X c κ ν) (ε : Real) :
    forallᵐ ω' ∂ν, forall t, 0 <= t -> (κ ω').real {ω | ε <= X ω} <= exp (-t * ε + c * t ^ 2 / 2) := by
  filter_upwards [h.mgf_le, h.ae_forall_integrable_exp_mul, h.isFiniteMeasure] with ω' h1 h2 _ t ht
  calc (κ ω').real {ω | ε <= X ω}
  _ <= exp (-t * ε) * mgf X (κ ω') t := measure_ge_le_exp_mul_mgf ε ht (h2 t)
  _ <= exp (-t * ε + c * t ^ 2 / 2) := by
    rw [exp_add]
    gcongr
    exact h1 t

/--
lemma `measure_ge_le` / 引理 `measure_ge_le`

English:
lemma measure_ge_le
  given: (h : HasSubgaussianMGF X c κ ν) {ε : Real} (hε : 0 <= ε)
  proof: by
  by_cases hc0 : c = 0
  · filter_upwards [h.measure_univ_le_one] with ω' h
    simp only [hc0, NNReal.coe_zero, mul_zero, div_zero, exp_zero]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp only [ENNReal.ofReal_one]
    exact (measure_mono (Set.subset_univ _)).trans h
  filter_

中文:
引理 measure_ge_le
  条件: (h : HasSubgaussianMGF X c κ ν) {ε : 实数} (hε : 0 <= ε)
  证明: by
  by_cases hc0 : c = 0
  · filter_upwards [h.measure_univ_le_one] with ω' h
    simp only [hc0, NNReal.coe_zero, mul_zero, div_zero, exp_zero]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp only [ENNReal.ofReal_one]
    exact (measure_mono (Set.subset_univ _)).trans h
  filter_

Depends on / 依赖: ENNReal, ENNReal.ofReal_one, ENNReal.toReal_le_of_le_ofReal, NNReal, NNReal.coe_zero, Set.subset_univ, coe_zero, div_zero, exp_zero, filter_upwards, h.measure_univ_le_one, measure_ge_le_exp_add, measure_mono, measure_univ_le_one, mul_zero, ofReal_one, subset_univ, toReal_le_of_le_ofReal, zero_le_one
-/
lemma measure_ge_le (h : HasSubgaussianMGF X c κ ν) {ε : Real} (hε : 0 <= ε) :
    forallᵐ ω' ∂ν, (κ ω').real {ω | ε <= X ω} <= exp (-ε ^ 2 / (2 * c)) := by
  by_cases hc0 : c = 0
  · filter_upwards [h.measure_univ_le_one] with ω' h
    simp only [hc0, NNReal.coe_zero, mul_zero, div_zero, exp_zero]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp only [ENNReal.ofReal_one]
    exact (measure_mono (Set.subset_univ _)).trans h
  filter_upwards [measure_ge_le_exp_add h ε] with ω' h
  calc (κ ω').real {ω | ε <= X ω}
  -- choose the minimizer of the r.h.s. of `h` for `t ≥ 0`. That is, `t = ε / c`.
  _ <= exp (-(ε / c) * ε + c * (ε / c) ^ 2 / 2) := h (ε / c) (by positivity)
  _ = exp (- ε ^ 2 / (2 * c)) := by congr; field

end ChernoffBound

section Zero

/--
lemma `measure_pos_eq_zero_of_hasSubGaussianMGF_zero` / 引理 `measure_pos_eq_zero_of_hasSubGaussianMGF_zero`

English:
lemma measure_pos_eq_zero_of_hasSubGaussianMGF_zero
  given: (h : HasSubgaussianMGF X 0 κ ν)
  proof: by
  have hs : {ω | 0 < X ω} = ⋃ ε : {ε : Rat // 0 < ε}, {ω | ε <= X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Subtype.exists, exists_prop]
    constructor
    · intro hp
      obtain ⟨q, h1, h2⟩ := exists_rat_btwn hp
      exact ⟨q, (q.cast_pos.1 h1), h2.le⟩
    · intro ⟨

中文:
引理 measure_pos_eq_zero_of_hasSubGaussianMGF_zero
  条件: (h : HasSubgaussianMGF X 0 κ ν)
  证明: by
  have hs : {ω | 0 < X ω} = ⋃ ε : {ε : Rat // 0 < ε}, {ω | ε <= X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Subtype.exists, exists_prop]
    constructor
    · intro hp
      obtain ⟨q, h1, h2⟩ := exists_rat_btwn hp
      exact ⟨q, (q.cast_pos.1 h1), h2.le⟩
    · intro ⟨

Depends on / 依赖: NNReal, Set.mem_iUnion, Set.mem_ofPred_eq, Subtype, Subtype.exists, cast_pos, exists_prop, exists_rat_btwn, filter_upwards, h.isFiniteMeasure, h.measure_ge_le_exp_add, h2.le, isFiniteMeasure, lt_of_lt_of_le, measure_ge_le_exp_add, mem_iUnion, mem_ofPred_eq, neg_mul, q.cast_pos
-/
lemma measure_pos_eq_zero_of_hasSubGaussianMGF_zero (h : HasSubgaussianMGF X 0 κ ν) :
    forallᵐ ω' ∂ν, (κ ω') {ω | 0 < X ω} = 0 := by
  have hs : {ω | 0 < X ω} = ⋃ ε : {ε : Rat // 0 < ε}, {ω | ε <= X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Subtype.exists, exists_prop]
    constructor
    · intro hp
      obtain ⟨q, h1, h2⟩ := exists_rat_btwn hp
      exact ⟨q, (q.cast_pos.1 h1), h2.le⟩
    · intro ⟨q, h1, h2⟩
      exact lt_of_lt_of_le (q.cast_pos.2 h1) h2
  have hb (ε : Rat) : forallᵐ ω' ∂ν, 0 < ε -> (κ ω') {ω | ε <= X ω} = 0 := by
    filter_upwards [h.measure_ge_le_exp_add ε, h.isFiniteMeasure] with ω' hm _ hε
    simp only [neg_mul, NNReal.coe_zero, zero_mul, zero_div, add_zero] at hm
    suffices (κ ω').real {ω | ε <= X ω} = 0 by simpa [Measure.real, ENNReal.toReal_eq_zero_iff]
    have hl : Filter.Tendsto (fun t => rexp (-(t * ε))) Filter.atTop (𝓝 0) := by
      apply tendsto_exp_neg_atTop_nhds_zero.comp
      exact Filter.Tendsto.atTop_mul_const (ε.cast_pos.2 hε) (fun _ a => a)
    apply le_antisymm
    · exact ge_of_tendsto hl (Filter.eventually_atTop.2 ⟨0, hm⟩)
    · exact measureReal_nonneg
  /- `ν`-almost everywhere, `{ω | 0 < X ω}` is a countable union of `κ ω'`-null sets. -/
  filter_upwards [ae_all_iff.2 hb] with ω' hn
  simp only [hs, measure_iUnion_null_iff, Subtype.forall]
  exact fun _ => hn _

/--
lemma `ae_eq_zero_of_hasSubgaussianMGF_zero` / 引理 `ae_eq_zero_of_hasSubgaussianMGF_zero`

English:
lemma ae_eq_zero_of_hasSubgaussianMGF_zero
  given: (h : HasSubgaussianMGF X 0 κ ν)
  proof: by
  filter_upwards [(h.neg).measure_pos_eq_zero_of_hasSubGaussianMGF_zero,
    h.measure_pos_eq_zero_of_hasSubGaussianMGF_zero]
  intro ω' h1 h2
  simp_rw [Pi.neg_apply, Left.neg_pos_iff] at h1
  apply nonpos_iff_eq_zero.1
  calc (κ ω') {ω | X ω != 0}
  _ = (κ ω') {ω | X ω < 0 ∨ 0 < X ω} := by simp

中文:
引理 ae_eq_zero_of_hasSubgaussianMGF_zero
  条件: (h : HasSubgaussianMGF X 0 κ ν)
  证明: by
  filter_upwards [(h.neg).measure_pos_eq_zero_of_hasSubGaussianMGF_zero,
    h.measure_pos_eq_zero_of_hasSubGaussianMGF_zero]
  intro ω' h1 h2
  simp_rw [Pi.neg_apply, Left.neg_pos_iff] at h1
  apply nonpos_iff_eq_zero.1
  calc (κ ω') {ω | X ω != 0}
  _ = (κ ω') {ω | X ω < 0 ∨ 0 < X ω} := by simp

Depends on / 依赖: Left.neg_pos_iff, Pi.neg_apply, filter_upwards, h.measure_pos_eq_zero_of_hasSubGaussianMGF_zero, h.neg, measure_pos_eq_zero_of_hasSubGaussianMGF_zero, measure_union_le, ne_iff_lt_or_gt, neg_apply, neg_pos_iff, nonpos_iff_eq_zero, simp_rw
-/
lemma ae_eq_zero_of_hasSubgaussianMGF_zero (h : HasSubgaussianMGF X 0 κ ν) :
    forallᵐ ω' ∂ν, X =ᵐ[κ ω'] 0 := by
  filter_upwards [(h.neg).measure_pos_eq_zero_of_hasSubGaussianMGF_zero,
    h.measure_pos_eq_zero_of_hasSubGaussianMGF_zero]
  intro ω' h1 h2
  simp_rw [Pi.neg_apply, Left.neg_pos_iff] at h1
  apply nonpos_iff_eq_zero.1
  calc (κ ω') {ω | X ω != 0}
  _ = (κ ω') {ω | X ω < 0 ∨ 0 < X ω} := by simp_rw [ne_iff_lt_or_gt]
  _ <= (κ ω') {ω | X ω < 0} + (κ ω') {ω | 0 < X ω} := measure_union_le _ _
  _ = 0 := by simp [h1, h2]

/--
lemma `ae_eq_zero_of_hasSubgaussianMGF_zero_of_measurable` / 引理 `ae_eq_zero_of_hasSubgaussianMGF_zero_of_measurable`

English:
lemma ae_eq_zero_of_hasSubgaussianMGF_zero_of_measurable
  proof: by
  rw [Filter.EventuallyEq]; rw [Measure.ae_comp_iff (measurableSet_eq_fun hX (by fun_prop))]
  exact h.ae_eq_zero_of_hasSubgaussianMGF_zero

中文:
引理 ae_eq_zero_of_hasSubgaussianMGF_zero_of_measurable
  证明: by
  rw [Filter.EventuallyEq]; rw [Measure.ae_comp_iff (measurableSet_eq_fun hX (by fun_prop))]
  exact h.ae_eq_zero_of_hasSubgaussianMGF_zero

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq, Measure, Measure.ae_comp_iff, ae_comp_iff, ae_eq_zero_of_hasSubgaussianMGF_zero, fun_prop, h.ae_eq_zero_of_hasSubgaussianMGF_zero, measurableSet_eq_fun
-/
lemma ae_eq_zero_of_hasSubgaussianMGF_zero_of_measurable
    (hX : Measurable X) (h : HasSubgaussianMGF X 0 κ ν) :
    X =ᵐ[κ ∘ₘ ν] 0 := by
  rw [Filter.EventuallyEq]; rw [Measure.ae_comp_iff (measurableSet_eq_fun hX (by fun_prop))]
  exact h.ae_eq_zero_of_hasSubgaussianMGF_zero

/--
lemma `ae_eq_zero_of_hasSubgaussianMGF_zero'` / 引理 `ae_eq_zero_of_hasSubgaussianMGF_zero'`

English:
lemma ae_eq_zero_of_hasSubgaussianMGF_zero'
  given: (h : HasSubgaussianMGF X 0 κ ν)
  proof: by
  have hX := h.aestronglyMeasurable
  have h' : HasSubgaussianMGF (hX.mk X) 0 κ ν := h.congr hX.ae_eq_mk
  exact hX.ae_eq_mk.trans (ae_eq_zero_of_hasSubgaussianMGF_zero_of_measurable hX.measurable_mk h')

中文:
引理 ae_eq_zero_of_hasSubgaussianMGF_zero'
  条件: (h : HasSubgaussianMGF X 0 κ ν)
  证明: by
  have hX := h.aestronglyMeasurable
  have h' : HasSubgaussianMGF (hX.mk X) 0 κ ν := h.congr hX.ae_eq_mk
  exact hX.ae_eq_mk.trans (ae_eq_zero_of_hasSubgaussianMGF_zero_of_measurable hX.measurable_mk h')

Depends on / 依赖: HasSubgaussianMGF, ae_eq_mk, ae_eq_zero_of_hasSubgaussianMGF_zero_of_measurable, aestronglyMeasurable, h.aestronglyMeasurable, h.congr, hX.ae_eq_mk, hX.ae_eq_mk.trans, hX.measurable_mk, hX.mk, measurable_mk
-/
lemma ae_eq_zero_of_hasSubgaussianMGF_zero' (h : HasSubgaussianMGF X 0 κ ν) :
    X =ᵐ[κ ∘ₘ ν] 0 := by
  have hX := h.aestronglyMeasurable
  have h' : HasSubgaussianMGF (hX.mk X) 0 κ ν := h.congr hX.ae_eq_mk
  exact hX.ae_eq_mk.trans (ae_eq_zero_of_hasSubgaussianMGF_zero_of_measurable hX.measurable_mk h')

end Zero

section Add

/--
lemma `add` / 引理 `add`

English:
lemma add
  statement: {Y : Ω -> Real} {cX cY : Real>=0} (hX : HasSubgaussianMGF X cX κ ν)
  proof: by
  by_cases hX0 : cX = 0
  · simp only [hX0, NNReal.sqrt_zero, zero_add, NNReal.sq_sqrt] at hX ⊢
    refine hY.congr ?_
    filter_upwards [ae_eq_zero_of_hasSubgaussianMGF_zero' hX] with ω hX0 using by simp [hX0]
  by_cases hY0 : cY = 0
  · simp only [hY0, NNReal.sqrt_zero, add_zero, NNReal.sq_sqr

中文:
引理 add
  结论: {Y : Ω -> 实数} {cX cY : 实数>=0} (hX : HasSubgaussianMGF X cX κ ν)
  证明: by
  by_cases hX0 : cX = 0
  · simp only [hX0, NNReal.sqrt_zero, zero_add, NNReal.sq_sqrt] at hX ⊢
    refine hY.congr ?_
    filter_upwards [ae_eq_zero_of_hasSubgaussianMGF_zero' hX] with ω hX0 using by simp [hX0]
  by_cases hY0 : cY = 0
  · simp only [hY0, NNReal.sqrt_zero, add_zero, NNReal.sq_sqr

Depends on / 依赖: MemLp.integrable_mul, NNReal, NNReal.sq_sqrt, NNReal.sqrt_zero, add_zero, ae_eq_zero_of_hasSubgaussianMGF_zero, convert, exp_add, filter_upwards, hX.congr, hX.m, hY.congr, integrable_exp_mul, integrable_mul, mul_add, simp_rw, sq_sqrt, sqrt_zero, zero_add
-/
lemma add {Y : Ω -> Real} {cX cY : Real>=0} (hX : HasSubgaussianMGF X cX κ ν)
    (hY : HasSubgaussianMGF Y cY κ ν) :
    HasSubgaussianMGF (fun ω => X ω + Y ω) ((cX.sqrt + cY.sqrt) ^ 2) κ ν := by
  by_cases hX0 : cX = 0
  · simp only [hX0, NNReal.sqrt_zero, zero_add, NNReal.sq_sqrt] at hX ⊢
    refine hY.congr ?_
    filter_upwards [ae_eq_zero_of_hasSubgaussianMGF_zero' hX] with ω hX0 using by simp [hX0]
  by_cases hY0 : cY = 0
  · simp only [hY0, NNReal.sqrt_zero, add_zero, NNReal.sq_sqrt] at hY ⊢
    refine hX.congr ?_
    filter_upwards [ae_eq_zero_of_hasSubgaussianMGF_zero' hY] with ω hY0 using by simp [hY0]
  exact
  { integrable_exp_mul t := by
      simp_rw [mul_add, exp_add]
      convert! MemLp.integrable_mul (hX.memLp_exp_mul t 2) (hY.memLp_exp_mul t 2)
      norm_cast
      infer_instance
    mgf_le := by
      let p := (cX.sqrt + cY.sqrt) / cX.sqrt
      let q := (cX.sqrt + cY.sqrt) / cY.sqrt
      filter_upwards [hX.mgf_le, hY.mgf_le, hX.ae_forall_memLp_exp_mul p,
        hY.ae_forall_memLp_exp_mul q] with ω' hmX hmY hlX hlY t
      calc (κ ω')[fun ω => exp (t * (X ω + Y ω))]
      _ <= (κ ω')[fun ω => exp (t * X ω) ^ (p : Real)] ^ (1 / (p : Real)) *
          (κ ω')[fun ω => exp (t * Y ω) ^ (q : Real)] ^ (1 / (q : Real)) := by
        simp_rw [mul_add, exp_add]
        apply integral_mul_le_Lp_mul_Lq_of_nonneg
        · exact ⟨by simp [field, p, q], by positivity, by positivity⟩
        · exact ae_of_all _ fun _ => exp_nonneg _
        · exact ae_of_all _ fun _ => exp_nonneg _
        · simpa using (hlX t)
        · simpa using (hlY t)
      _ <= exp (cX * (t * p) ^ 2 / 2) ^ (1 / (p : Real)) *
          exp (cY * (t * q) ^ 2 / 2) ^ (1 / (q : Real)) := by
        simp_rw [← exp_mul _ p, ← exp_mul _ q, mul_right_comm t _ p, mul_right_comm t _ q]
        gcongr
        · exact hmX (t * p)
        · exact hmY (t * q)
      _ = exp ((cX.sqrt + cY.sqrt) ^ 2 * t ^ 2 / 2) := by
        simp_rw [← exp_mul, ← exp_add]
        simp only [NNReal.coe_div, NNReal.coe_add, coe_sqrt, one_div, inv_div, exp_eq_exp, p, q]
        field_simp
        linear_combination t ^ 2 * (-√↑cY * Real.sq_sqrt cX.coe_nonneg
            -√↑cX * Real.sq_sqrt cY.coe_nonneg) }

variable {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {Y : Ω'' -> Real} {cY : Real>=0}

/--
lemma `prodMkLeft_compProd` / 引理 `prodMkLeft_compProd`

English:
lemma prodMkLeft_compProd
  given: {η : Kernel Ω Ω''} (h : HasSubgaussianMGF Y cY η (κ ∘ₘ ν))
  proof: by
  by_cases hν : SFinite ν
  swap; · simp [hν]
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  constructor
  · simpa using h.integrable_exp_mul
  · have h2 := h.mgf_le
    rw [← Measure.snd_compProd]; rw [Measure.snd] at h2
    exact ae_of_ae_map (by fun_prop) h2

中文:
引理 prodMkLeft_compProd
  条件: {η : Kernel Ω Ω''} (h : HasSubgaussianMGF Y cY η (κ ∘ₘ ν))
  证明: by
  by_cases hν : SFinite ν
  swap; · simp [hν]
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  constructor
  · simpa using h.integrable_exp_mul
  · have h2 := h.mgf_le
    rw [← Measure.snd_compProd]; rw [Measure.snd] at h2
    exact ae_of_ae_map (by fun_prop) h2

Depends on / 依赖: IsSFiniteKernel, Measure, Measure.snd, Measure.snd_compProd, SFinite, ae_of_ae_map, fun_prop, h.integrable_exp_mul, h.mgf_le, integrable_exp_mul, mgf_le, snd_compProd
-/
lemma prodMkLeft_compProd {η : Kernel Ω Ω''} (h : HasSubgaussianMGF Y cY η (κ ∘ₘ ν)) :
    HasSubgaussianMGF Y cY (prodMkLeft Ω' η) (ν otimesₘ κ) := by
  by_cases hν : SFinite ν
  swap; · simp [hν]
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  constructor
  · simpa using h.integrable_exp_mul
  · have h2 := h.mgf_le
    rw [← Measure.snd_compProd]; rw [Measure.snd] at h2
    exact ae_of_ae_map (by fun_prop) h2

variable [SFinite ν]

/--
lemma `integrable_exp_add_compProd` / 引理 `integrable_exp_add_compProd`

English:
lemma integrable_exp_add_compProd
  statement: {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η]
  proof: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [FunLike.coe_zero, hκ]
  rcases eq_zero_or_isMarkovKernel η with rfl | hη
  · simp [FunLike.coe_zero]
  simp_rw [mul_add, exp_add]
  refine MemLp.integrable_mul (p := 2) (q := 2) ?_ ?_
  · have h := hX.memLp_exp_mul t 2
    simp only [ENNReal.coe_o

中文:
引理 integrable_exp_add_compProd
  结论: {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η]
  证明: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [FunLike.coe_zero, hκ]
  rcases eq_zero_or_isMarkovKernel η with rfl | hη
  · simp [FunLike.coe_zero]
  simp_rw [mul_add, exp_add]
  refine MemLp.integrable_mul (p := 2) (q := 2) ?_ ?_
  · have h := hX.memLp_exp_mul t 2
    simp only [ENNReal.coe_o

Depends on / 依赖: ENNReal, ENNReal.coe_ofNat, FunLike, FunLike.coe_zero, IsSFiniteKernel, Measure, Measure.map_comp, MemLp.integrable_mul, Prod.fst, aemeasurable, coe_ofNat, coe_zero, eq_zero_or_isMarkovKernel, exp_add, fst_compProd, fst_eq, hX.memLp_exp_mul, integrable_mul, map_comp, measurable_fst
-/
lemma integrable_exp_add_compProd {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η]
    (hX : HasSubgaussianMGF X c κ ν) (hY : HasSubgaussianMGF Y cY η (ν otimesₘ κ)) (t : Real) :
    Integrable (fun ω => exp (t * (X ω.1 + Y ω.2))) ((κ otimesₖ η) ∘ₘ ν) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [FunLike.coe_zero, hκ]
  rcases eq_zero_or_isMarkovKernel η with rfl | hη
  · simp [FunLike.coe_zero]
  simp_rw [mul_add, exp_add]
  refine MemLp.integrable_mul (p := 2) (q := 2) ?_ ?_
  · have h := hX.memLp_exp_mul t 2
    simp only [ENNReal.coe_ofNat] at h
    have : κ ∘ₘ ν = ((κ otimesₖ η) ∘ₘ ν).map Prod.fst := by
      rw [Measure.map_comp _ _ measurable_fst]; rw [← fst_eq]; rw [fst_compProd]
    rwa [this, memLp_map_measure_iff h.1 measurable_fst.aemeasurable] at h
  · have h := hY.memLp_exp_mul t 2
    rwa [ENNReal.coe_ofNat, Measure.comp_compProd_comm, Measure.snd,
      memLp_map_measure_iff h.1 measurable_snd.aemeasurable] at h

/--
lemma `add_compProd` / 引理 `add_compProd`

English:
lemma add_compProd
  statement: {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η]
  proof: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  refine .of_rat (integrable_exp_add_compProd hX hY) fun q => ?_
  filter_upwards [hX.mgf_le, hX.ae_integrable_exp_mul q, Measure.ae_ae_of_ae_compProd hY.mgf_le,
Measure.ae_integrable_of_integrable_comp integrable_exp_add_compProd hX hY q]
   

中文:
引理 add_compProd
  结论: {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η]
  证明: by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  refine .of_rat (integrable_exp_add_compProd hX hY) fun q => ?_
  filter_upwards [hX.mgf_le, hX.ae_integrable_exp_mul q, Measure.ae_ae_of_ae_compProd hY.mgf_le,
Measure.ae_integrable_of_integrable_comp integrable_exp_add_compProd hX hY q]
   

Depends on / 依赖: IsSFiniteKernel, Measure, Measure.ae_ae_of_ae_compProd, Measure.ae_integrable_of_integrable_comp, ae_ae_of_ae_compProd, ae_integrable_exp_mul, ae_integrable_of_integrable_comp, exp_add, filter_upwards, hX.ae_integrable_exp_mul, hX.mgf_le, hX_int, hX_mgf, hY.mgf_le, hY_mgf, h_int_mul, integrable_exp_add_compProd, mgf_le, mul_add, of_rat
-/
lemma add_compProd {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η]
    (hX : HasSubgaussianMGF X c κ ν) (hY : HasSubgaussianMGF Y cY η (ν otimesₘ κ)) :
    HasSubgaussianMGF (fun p => X p.1 + Y p.2) (c + cY) (κ otimesₖ η) ν := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  refine .of_rat (integrable_exp_add_compProd hX hY) fun q => ?_
  filter_upwards [hX.mgf_le, hX.ae_integrable_exp_mul q, Measure.ae_ae_of_ae_compProd hY.mgf_le,
Measure.ae_integrable_of_integrable_comp integrable_exp_add_compProd hX hY q]
    with ω' hX_mgf hX_int hY_mgf h_int_mul
  calc mgf (fun p => X p.1 + Y p.2) ((κ otimesₖ η) ω') q
  _ = ∫ x, exp (q * X x) * ∫ y, exp (q * Y y) ∂(η (ω', x)) ∂(κ ω') := by
    simp_rw [mgf, mul_add, exp_add] at h_int_mul ⊢
    simp_rw [integral_compProd h_int_mul, integral_const_mul]
  _ <= ∫ x, exp (q * X x) * exp (cY * q ^ 2 / 2) ∂(κ ω') := by
    refine integral_mono_of_nonneg ?_ (hX_int.mul_const _) ?_
    · exact ae_of_all _ fun ω => mul_nonneg (by positivity)
        (integral_nonneg (fun _ => by positivity))
    · filter_upwards [all_ae_of hY_mgf q] with ω hY_mgf
      gcongr
      exact hY_mgf
  _ <= exp (↑(c + cY) * q ^ 2 / 2) := by
    rw [integral_mul_const]; rw [NNReal.coe_add]; rw [add_mul]; rw [add_div]; rw [exp_add]
    gcongr
    exact hX_mgf q

/--
lemma `add_comp` / 引理 `add_comp`

English:
lemma add_comp
  statement: {η : Kernel Ω Ω''} [IsZeroOrMarkovKernel η]
  proof: hX.add_compProd hY.prodMkLeft_compProd

中文:
引理 add_comp
  结论: {η : Kernel Ω Ω''} [IsZeroOrMarkovKernel η]
  证明: hX.add_compProd hY.prodMkLeft_compProd

Depends on / 依赖: add_compProd, hX.add_compProd, hY.prodMkLeft_compProd, prodMkLeft_compProd
-/
lemma add_comp {η : Kernel Ω Ω''} [IsZeroOrMarkovKernel η]
    (hX : HasSubgaussianMGF X c κ ν) (hY : HasSubgaussianMGF Y cY η (κ ∘ₘ ν)) :
    HasSubgaussianMGF (fun p => X p.1 + Y p.2) (c + cY) (κ otimesₖ prodMkLeft Ω' η) ν :=
  hX.add_compProd hY.prodMkLeft_compProd

end Add

end Kernel.HasSubgaussianMGF

end Kernel

section Conditional

/-! ### Conditionally sub-Gaussian moment-generating function -/

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {hm : m <= mΩ} [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω -> Real} {c : Real>=0}

variable (m) (hm) in
/--
Definition of `HasCondSubgaussianMGF` / `HasCondSubgaussianMGF` 的定义

English:
definition HasCondSubgaussianMGF
  signature: (X : Ω -> Real) (c : Real>=0)
  body: Kernel.HasSubgaussianMGF X c (condExpKernel μ m) (μ.trim hm)

中文:
定义 HasCondSubgaussianMGF
  签名: (X : Ω -> 实数) (c : 实数>=0)
  定义体: Kernel.HasSubgaussianMGF X c (condExpKernel μ m) (μ.trim hm)

Depends on / 依赖: HasSubgaussianMGF, IsFiniteMeasure, Kernel, Kernel.HasSubgaussianMGF, condExpKernel, volume_tac
-/
def HasCondSubgaussianMGF (X : Ω -> Real) (c : Real>=0)
    (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Kernel.HasSubgaussianMGF X c (condExpKernel μ m) (μ.trim hm)

namespace HasCondSubgaussianMGF

/--
lemma `mgf_le` / 引理 `mgf_le`

English:
lemma mgf_le
  given: (h : HasCondSubgaussianMGF m hm X c μ)
  proof: Kernel.HasSubgaussianMGF.mgf_le h

中文:
引理 mgf_le
  条件: (h : HasCondSubgaussianMGF m hm X c μ)
  证明: Kernel.HasSubgaussianMGF.mgf_le h

Depends on / 依赖: HasSubgaussianMGF, Kernel, Kernel.HasSubgaussianMGF.mgf_le, mgf_le
-/
lemma mgf_le (h : HasCondSubgaussianMGF m hm X c μ) :
    forallᵐ ω' ∂(μ.trim hm), forall t, mgf X (condExpKernel μ m ω') t <= exp (c * t ^ 2 / 2) :=
  Kernel.HasSubgaussianMGF.mgf_le h

/--
lemma `cgf_le` / 引理 `cgf_le`

English:
lemma cgf_le
  given: (h : HasCondSubgaussianMGF m hm X c μ)
  proof: Kernel.HasSubgaussianMGF.cgf_le h

中文:
引理 cgf_le
  条件: (h : HasCondSubgaussianMGF m hm X c μ)
  证明: Kernel.HasSubgaussianMGF.cgf_le h

Depends on / 依赖: HasSubgaussianMGF, Kernel, Kernel.HasSubgaussianMGF.cgf_le, cgf_le
-/
lemma cgf_le (h : HasCondSubgaussianMGF m hm X c μ) :
    forallᵐ ω' ∂(μ.trim hm), forall t, cgf X (condExpKernel μ m ω') t <= c * t ^ 2 / 2 :=
  Kernel.HasSubgaussianMGF.cgf_le h

/--
lemma `ae_trim_condExp_le` / 引理 `ae_trim_condExp_le`

English:
lemma ae_trim_condExp_le
  given: (h : HasCondSubgaussianMGF m hm X c μ) (t : Real)
  proof: by
  have h_eq := condExp_ae_eq_trim_integral_condExpKernel hm (h.integrable_exp_mul t)
  simp_rw [condExpKernel_comp_trim] at h_eq
  filter_upwards [h.mgf_le, h_eq] with ω' h_mgf h_eq
  rw [h_eq]
  exact h_mgf t

中文:
引理 ae_trim_condExp_le
  条件: (h : HasCondSubgaussianMGF m hm X c μ) (t : 实数)
  证明: by
  have h_eq := condExp_ae_eq_trim_integral_condExpKernel hm (h.integrable_exp_mul t)
  simp_rw [condExpKernel_comp_trim] at h_eq
  filter_upwards [h.mgf_le, h_eq] with ω' h_mgf h_eq
  rw [h_eq]
  exact h_mgf t

Depends on / 依赖: condExpKernel_comp_trim, condExp_ae_eq_trim_integral_condExpKernel, filter_upwards, h.integrable_exp_mul, h.mgf_le, h_eq, h_mgf, integrable_exp_mul, mgf_le, simp_rw
-/
lemma ae_trim_condExp_le (h : HasCondSubgaussianMGF m hm X c μ) (t : Real) :
    forallᵐ ω' ∂(μ.trim hm), (μ[fun ω => exp (t * X ω) | m]) ω' <= exp (c * t ^ 2 / 2) := by
  have h_eq := condExp_ae_eq_trim_integral_condExpKernel hm (h.integrable_exp_mul t)
  simp_rw [condExpKernel_comp_trim] at h_eq
  filter_upwards [h.mgf_le, h_eq] with ω' h_mgf h_eq
  rw [h_eq]
  exact h_mgf t

/--
lemma `ae_condExp_le` / 引理 `ae_condExp_le`

English:
lemma ae_condExp_le
  given: (h : HasCondSubgaussianMGF m hm X c μ) (t : Real)
  proof: ae_of_ae_trim hm (h.ae_trim_condExp_le t)

@[simp]

中文:
引理 ae_condExp_le
  条件: (h : HasCondSubgaussianMGF m hm X c μ) (t : 实数)
  证明: ae_of_ae_trim hm (h.ae_trim_condExp_le t)

@[simp]

Depends on / 依赖: ae_of_ae_trim, ae_trim_condExp_le, h.ae_trim_condExp_le
-/
lemma ae_condExp_le (h : HasCondSubgaussianMGF m hm X c μ) (t : Real) :
    forallᵐ ω' ∂μ, (μ[fun ω => exp (t * X ω) | m]) ω' <= exp (c * t ^ 2 / 2) :=
  ae_of_ae_trim hm (h.ae_trim_condExp_le t)

@[simp]
/--
lemma `fun_zero` / 引理 `fun_zero`

English:
lemma fun_zero
  statement: HasCondSubgaussianMGF m hm (fun _ => 0) 0 μ
  proof: Kernel.HasSubgaussianMGF.fun_zero

@[simp]

中文:
引理 fun_zero
  结论: HasCondSubgaussianMGF m hm (fun _ => 0) 0 μ
  证明: Kernel.HasSubgaussianMGF.fun_zero

@[simp]

Depends on / 依赖: HasSubgaussianMGF, Kernel, Kernel.HasSubgaussianMGF.fun_zero, fun_zero
-/
lemma fun_zero : HasCondSubgaussianMGF m hm (fun _ => 0) 0 μ := Kernel.HasSubgaussianMGF.fun_zero

@[simp]
/--
lemma `zero` / 引理 `zero`

English:
lemma zero
  statement: HasCondSubgaussianMGF m hm 0 0 μ
  proof: Kernel.HasSubgaussianMGF.zero

中文:
引理 zero
  结论: HasCondSubgaussianMGF m hm 0 0 μ
  证明: Kernel.HasSubgaussianMGF.zero

Depends on / 依赖: HasSubgaussianMGF, Kernel, Kernel.HasSubgaussianMGF.zero
-/
lemma zero : HasCondSubgaussianMGF m hm 0 0 μ := Kernel.HasSubgaussianMGF.zero

/--
lemma `memLp_exp_mul` / 引理 `memLp_exp_mul`

English:
lemma memLp_exp_mul
  given: (h : HasCondSubgaussianMGF m hm X c μ) (t : Real) (p : Real>=0)
  proof: condExpKernel_comp_trim (μ := μ) hm ▸ Kernel.HasSubgaussianMGF.memLp_exp_mul h t p

中文:
引理 memLp_exp_mul
  条件: (h : HasCondSubgaussianMGF m hm X c μ) (t : 实数) (p : 实数>=0)
  证明: condExpKernel_comp_trim (μ := μ) hm ▸ Kernel.HasSubgaussianMGF.memLp_exp_mul h t p

Depends on / 依赖: HasSubgaussianMGF, Kernel, Kernel.HasSubgaussianMGF.memLp_exp_mul, condExpKernel_comp_trim, memLp_exp_mul
-/
lemma memLp_exp_mul (h : HasCondSubgaussianMGF m hm X c μ) (t : Real) (p : Real>=0) :
    MemLp (fun ω => exp (t * X ω)) p μ :=
  condExpKernel_comp_trim (μ := μ) hm ▸ Kernel.HasSubgaussianMGF.memLp_exp_mul h t p

/--
lemma `integrable_exp_mul` / 引理 `integrable_exp_mul`

English:
lemma integrable_exp_mul
  given: (h : HasCondSubgaussianMGF m hm X c μ) (t : Real)
  proof: condExpKernel_comp_trim (μ := μ) hm ▸ Kernel.HasSubgaussianMGF.integrable_exp_mul h t

中文:
引理 integrable_exp_mul
  条件: (h : HasCondSubgaussianMGF m hm X c μ) (t : 实数)
  证明: condExpKernel_comp_trim (μ := μ) hm ▸ Kernel.HasSubgaussianMGF.integrable_exp_mul h t

Depends on / 依赖: HasSubgaussianMGF, Kernel, Kernel.HasSubgaussianMGF.integrable_exp_mul, condExpKernel_comp_trim, integrable_exp_mul
-/
lemma integrable_exp_mul (h : HasCondSubgaussianMGF m hm X c μ) (t : Real) :
    Integrable (fun ω => exp (t * X ω)) μ :=
  condExpKernel_comp_trim (μ := μ) hm ▸ Kernel.HasSubgaussianMGF.integrable_exp_mul h t

end HasCondSubgaussianMGF

end Conditional

/-! ### Sub-Gaussian moment-generating function -/

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω -> Real} {c : Real>=0}

/--
Definition of `HasSubgaussianMGF` / `HasSubgaussianMGF` 的定义

English:
structure HasSubgaussianMGF
  parameters: (X : Ω -> Real) (c : Real>=0) (μ : Measure Ω := by volume_tac)
  axioms and operations (2):
    - integrable_exp_mul : forall t : Real, Integrable (fun ω => exp (t * X ω)) μ
    - mgf_le : forall t : Real, mgf X μ t <= exp (c * t ^ 2 / 2)

中文:
结构 HasSubgaussianMGF
  参数: (X : Ω -> 实数) (c : 实数>=0) (μ : Measure Ω := by volume_tac)
  公理与运算 (2 个):
    - integrable_exp_mul : 对任意 t : 实数, 整数egrable (fun ω => exp (t * X ω)) μ
    - mgf_le : 对任意 t : 实数, mgf X μ t <= exp (c * t ^ 2 / 2)

Depends on / 依赖: Integrable, integrable_exp_mul, mgf_le, volume_tac
-/
structure HasSubgaussianMGF (X : Ω -> Real) (c : Real>=0) (μ : Measure Ω := by volume_tac) : Prop where
  integrable_exp_mul : forall t : Real, Integrable (fun ω => exp (t * X ω)) μ
  mgf_le : forall t : Real, mgf X μ t <= exp (c * t ^ 2 / 2)

/--
lemma `HasSubgaussianMGF_iff_kernel` / 引理 `HasSubgaussianMGF_iff_kernel`

English:
lemma HasSubgaussianMGF_iff_kernel
  proof: ⟨fun ⟨h1, h2⟩ => ⟨by simpa, by simpa⟩, fun ⟨h1, h2⟩ => ⟨by simpa using h1, by simpa using h2⟩⟩

中文:
引理 HasSubgaussianMGF_iff_kernel
  证明: ⟨fun ⟨h1, h2⟩ => ⟨by simpa, by simpa⟩, fun ⟨h1, h2⟩ => ⟨by simpa using h1, by simpa using h2⟩⟩
-/
lemma HasSubgaussianMGF_iff_kernel :
    HasSubgaussianMGF X c μ
      ↔ Kernel.HasSubgaussianMGF X c (Kernel.const Unit μ) (Measure.dirac ()) :=
  ⟨fun ⟨h1, h2⟩ => ⟨by simpa, by simpa⟩, fun ⟨h1, h2⟩ => ⟨by simpa using h1, by simpa using h2⟩⟩

namespace HasSubgaussianMGF

/--
lemma `aestronglyMeasurable` / 引理 `aestronglyMeasurable`

English:
lemma aestronglyMeasurable
  given: (h : HasSubgaussianMGF X c μ)
  statement: AEStronglyMeasurable X μ
  proof: by
  have h_int := h.integrable_exp_mul 1
  simpa using (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

中文:
引理 aestronglyMeasurable
  条件: (h : HasSubgaussianMGF X c μ)
  结论: AEStronglyMeasurable X μ
  证明: by
  have h_int := h.integrable_exp_mul 1
  simpa using (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

Depends on / 依赖: aemeasurable, aemeasurable_of_aemeasurable_exp, aestronglyMeasurable, h.integrable_exp_mul, h_int, integrable_exp_mul
-/
lemma aestronglyMeasurable (h : HasSubgaussianMGF X c μ) : AEStronglyMeasurable X μ := by
  have h_int := h.integrable_exp_mul 1
  simpa using (aemeasurable_of_aemeasurable_exp h_int.1.aemeasurable).aestronglyMeasurable

/--
lemma `aemeasurable` / 引理 `aemeasurable`

English:
lemma aemeasurable
  given: (h : HasSubgaussianMGF X c μ)
  statement: AEMeasurable X μ
  proof: h.aestronglyMeasurable.aemeasurable

中文:
引理 aemeasurable
  条件: (h : HasSubgaussianMGF X c μ)
  结论: AEMeasurable X μ
  证明: h.aestronglyMeasurable.aemeasurable

Depends on / 依赖: aemeasurable, aestronglyMeasurable, h.aestronglyMeasurable.aemeasurable
-/
lemma aemeasurable (h : HasSubgaussianMGF X c μ) : AEMeasurable X μ :=
  h.aestronglyMeasurable.aemeasurable

/--
lemma `congr` / 引理 `congr`

English:
lemma congr
  given: (h : HasSubgaussianMGF X c μ) {Y : Ω -> Real} (h' : X =ᵐ[μ] Y)
  proof: by
  rw [HasSubgaussianMGF_iff_kernel] at h ⊢
  apply h.congr
  simpa

中文:
引理 congr
  条件: (h : HasSubgaussianMGF X c μ) {Y : Ω -> 实数} (h' : X =ᵐ[μ] Y)
  证明: by
  rw [HasSubgaussianMGF_iff_kernel] at h ⊢
  apply h.congr
  simpa

Depends on / 依赖: HasSubgaussianMGF_iff_kernel, h.congr
-/
lemma congr (h : HasSubgaussianMGF X c μ) {Y : Ω -> Real} (h' : X =ᵐ[μ] Y) :
    HasSubgaussianMGF Y c μ := by
  rw [HasSubgaussianMGF_iff_kernel] at h ⊢
  apply h.congr
  simpa

/--
lemma `memLp_exp_mul` / 引理 `memLp_exp_mul`

English:
lemma memLp_exp_mul
  given: (h : HasSubgaussianMGF X c μ) (t : Real) (p : Real>=0)
  proof: by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using h.memLp_exp_mul t p

中文:
引理 memLp_exp_mul
  条件: (h : HasSubgaussianMGF X c μ) (t : 实数) (p : 实数>=0)
  证明: by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using h.memLp_exp_mul t p

Depends on / 依赖: HasSubgaussianMGF_iff_kernel, h.memLp_exp_mul, memLp_exp_mul
-/
lemma memLp_exp_mul (h : HasSubgaussianMGF X c μ) (t : Real) (p : Real>=0) :
    MemLp (fun ω => exp (t * X ω)) p μ := by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using h.memLp_exp_mul t p

/--
lemma `cgf_le` / 引理 `cgf_le`

English:
lemma cgf_le
  given: (h : HasSubgaussianMGF X c μ) (t : Real)
  statement: cgf X μ t <= c * t ^ 2 / 2
  proof: by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using (all_ae_of h.cgf_le t)

@[simp]

中文:
引理 cgf_le
  条件: (h : HasSubgaussianMGF X c μ) (t : 实数)
  结论: cgf X μ t <= c * t ^ 2 / 2
  证明: by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using (all_ae_of h.cgf_le t)

@[simp]

Depends on / 依赖: HasSubgaussianMGF_iff_kernel, all_ae_of, cgf_le, h.cgf_le
-/
lemma cgf_le (h : HasSubgaussianMGF X c μ) (t : Real) : cgf X μ t <= c * t ^ 2 / 2 := by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using (all_ae_of h.cgf_le t)

@[simp]
/--
lemma `fun_zero` / 引理 `fun_zero`

English:
lemma fun_zero
  given: [IsZeroOrProbabilityMeasure μ]
  statement: HasSubgaussianMGF (fun _ => 0) 0 μ
  proof: by
  simp [HasSubgaussianMGF_iff_kernel]

@[simp]

中文:
引理 fun_zero
  条件: [IsZeroOrProbabilityMeasure μ]
  结论: HasSubgaussianMGF (fun _ => 0) 0 μ
  证明: by
  simp [HasSubgaussianMGF_iff_kernel]

@[simp]

Depends on / 依赖: HasSubgaussianMGF_iff_kernel
-/
lemma fun_zero [IsZeroOrProbabilityMeasure μ] : HasSubgaussianMGF (fun _ => 0) 0 μ := by
  simp [HasSubgaussianMGF_iff_kernel]

@[simp]
/--
lemma `zero` / 引理 `zero`

English:
lemma zero
  given: [IsZeroOrProbabilityMeasure μ]
  statement: HasSubgaussianMGF 0 0 μ
  proof: fun_zero

中文:
引理 zero
  条件: [IsZeroOrProbabilityMeasure μ]
  结论: HasSubgaussianMGF 0 0 μ
  证明: fun_zero

Depends on / 依赖: fun_zero
-/
lemma zero [IsZeroOrProbabilityMeasure μ] : HasSubgaussianMGF 0 0 μ := fun_zero

/--
lemma `neg` / 引理 `neg`

English:
lemma neg
  given: {c : Real>=0} (h : HasSubgaussianMGF X c μ)
  statement: HasSubgaussianMGF (-X) c μ
  proof: by
  simpa [HasSubgaussianMGF_iff_kernel] using (HasSubgaussianMGF_iff_kernel.1 h).neg

中文:
引理 neg
  条件: {c : 实数>=0} (h : HasSubgaussianMGF X c μ)
  结论: HasSubgaussianMGF (-X) c μ
  证明: by
  simpa [HasSubgaussianMGF_iff_kernel] using (HasSubgaussianMGF_iff_kernel.1 h).neg

Depends on / 依赖: HasSubgaussianMGF_iff_kernel
-/
lemma neg {c : Real>=0} (h : HasSubgaussianMGF X c μ) : HasSubgaussianMGF (-X) c μ := by
  simpa [HasSubgaussianMGF_iff_kernel] using (HasSubgaussianMGF_iff_kernel.1 h).neg

/--
lemma `of_map` / 引理 `of_map`

English:
lemma of_map
  statement: {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
  proof: by
    have h1 := h.integrable_exp_mul t
    rwa [integrable_map_measure h1.aestronglyMeasurable (by fun_prop)] at h1
  mgf_le t := by
    convert! h.mgf_le t using 1
    rw [mgf_map hY (h.integrable_exp_mul t).1]

中文:
引理 of_map
  结论: {Ω' : 类型} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
  证明: by
    have h1 := h.integrable_exp_mul t
    rwa [integrable_map_measure h1.aestronglyMeasurable (by fun_prop)] at h1
  mgf_le t := by
    convert! h.mgf_le t using 1
    rw [mgf_map hY (h.integrable_exp_mul t).1]

Depends on / 依赖: aestronglyMeasurable, convert, fun_prop, h.integrable_exp_mul, h.mgf_le, h1.aestronglyMeasurable, integrable_exp_mul, integrable_map_measure, mgf_le, mgf_map
-/
lemma of_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {Y : Ω' -> Ω} {X : Ω -> Real} (hY : AEMeasurable Y μ) (h : HasSubgaussianMGF X c (μ.map Y)) :
    HasSubgaussianMGF (X ∘ Y) c μ where
  integrable_exp_mul t := by
    have h1 := h.integrable_exp_mul t
    rwa [integrable_map_measure h1.aestronglyMeasurable (by fun_prop)] at h1
  mgf_le t := by
    convert! h.mgf_le t using 1
    rw [mgf_map hY (h.integrable_exp_mul t).1]

/--
lemma `id_map_iff` / 引理 `id_map_iff`

English:
lemma id_map_iff
  given: (hX : AEMeasurable X μ)
  proof: by
  refine ⟨fun h => ?_, fun h => ⟨fun t => ?_, fun t => ?_⟩⟩
  · rw [← Function.id_comp X]
    exact .of_map hX h
  · rw [integrable_map_measure (by fun_prop) hX]
    exact h.integrable_exp_mul t
  · rw [mgf_id_map hX]
    exact h.mgf_le t

中文:
引理 id_map_iff
  条件: (hX : AEMeasurable X μ)
  证明: by
  refine ⟨fun h => ?_, fun h => ⟨fun t => ?_, fun t => ?_⟩⟩
  · rw [← Function.id_comp X]
    exact .of_map hX h
  · rw [integrable_map_measure (by fun_prop) hX]
    exact h.integrable_exp_mul t
  · rw [mgf_id_map hX]
    exact h.mgf_le t

Depends on / 依赖: Function, Function.id_comp, fun_prop, h.integrable_exp_mul, h.mgf_le, id_comp, integrable_exp_mul, integrable_map_measure, mgf_id_map, mgf_le, of_map
-/
lemma id_map_iff (hX : AEMeasurable X μ) :
    HasSubgaussianMGF id c (μ.map X) ↔ HasSubgaussianMGF X c μ := by
  refine ⟨fun h => ?_, fun h => ⟨fun t => ?_, fun t => ?_⟩⟩
  · rw [← Function.id_comp X]
    exact .of_map hX h
  · rw [integrable_map_measure (by fun_prop) hX]
    exact h.integrable_exp_mul t
  · rw [mgf_id_map hX]
    exact h.mgf_le t

/--
lemma `congr_identDistrib` / 引理 `congr_identDistrib`

English:
lemma congr_identDistrib
  statement: {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
  proof: by
  rw [← id_map_iff hXY.aemeasurable_fst] at hX
  rwa [← id_map_iff hXY.aemeasurable_snd, ← hXY.map_eq]

中文:
引理 congr_identDistrib
  结论: {Ω' : 类型} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
  证明: by
  rw [← id_map_iff hXY.aemeasurable_fst] at hX
  rwa [← id_map_iff hXY.aemeasurable_snd, ← hXY.map_eq]

Depends on / 依赖: aemeasurable_fst, aemeasurable_snd, hXY.aemeasurable_fst, hXY.aemeasurable_snd, hXY.map_eq, id_map_iff, map_eq
-/
lemma congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {Y : Ω' -> Real} (hX : HasSubgaussianMGF X c μ) (hXY : IdentDistrib X Y μ μ') :
    HasSubgaussianMGF Y c μ' := by
  rw [← id_map_iff hXY.aemeasurable_fst] at hX
  rwa [← id_map_iff hXY.aemeasurable_snd, ← hXY.map_eq]

/--
lemma `trim` / 引理 `trim`

English:
lemma trim
  given: (hm : m <= mΩ) (hXm : Measurable[m] X) (hX : HasSubgaussianMGF X c μ)
  proof: by
    refine (hX.integrable_exp_mul t).trim hm ?_
exact Measurable.stronglyMeasurable by fun_prop
  mgf_le t := by
    rw [mgf]; rw [← integral_trim]
    · exact hX.mgf_le t
· exact Measurable.stronglyMeasurable by fun_prop

中文:
引理 trim
  条件: (hm : m <= mΩ) (hXm : Measurable[m] X) (hX : HasSubgaussianMGF X c μ)
  证明: by
    refine (hX.integrable_exp_mul t).trim hm ?_
exact Measurable.stronglyMeasurable by fun_prop
  mgf_le t := by
    rw [mgf]; rw [← integral_trim]
    · exact hX.mgf_le t
· exact Measurable.stronglyMeasurable by fun_prop

Depends on / 依赖: Measurable, Measurable.stronglyMeasurable, fun_prop, hX.integrable_exp_mul, hX.mgf_le, integrable_exp_mul, integral_trim, mgf_le, stronglyMeasurable
-/
lemma trim (hm : m <= mΩ) (hXm : Measurable[m] X) (hX : HasSubgaussianMGF X c μ) :
    HasSubgaussianMGF X c (μ.trim hm) where
  integrable_exp_mul t := by
    refine (hX.integrable_exp_mul t).trim hm ?_
exact Measurable.stronglyMeasurable by fun_prop
  mgf_le t := by
    rw [mgf]; rw [← integral_trim]
    · exact hX.mgf_le t
· exact Measurable.stronglyMeasurable by fun_prop

/--
lemma `const_mul` / 引理 `const_mul`

English:
lemma const_mul
  given: (h : HasSubgaussianMGF X c μ) (r : Real)
  proof: by
  rw [HasSubgaussianMGF_iff_kernel] at h ⊢
  exact Kernel.HasSubgaussianMGF.const_mul h r

中文:
引理 const_mul
  条件: (h : HasSubgaussianMGF X c μ) (r : 实数)
  证明: by
  rw [HasSubgaussianMGF_iff_kernel] at h ⊢
  exact Kernel.HasSubgaussianMGF.const_mul h r
-/
protected lemma const_mul (h : HasSubgaussianMGF X c μ) (r : Real) :
    HasSubgaussianMGF (fun ω => r * X ω) (⟨r ^ 2, sq_nonneg r⟩ * c) μ := by
  rw [HasSubgaussianMGF_iff_kernel] at h ⊢
  exact Kernel.HasSubgaussianMGF.const_mul h r

/--
lemma `integrableExpSet_eq_univ` / 引理 `integrableExpSet_eq_univ`

English:
lemma integrableExpSet_eq_univ
  given: (hX : HasSubgaussianMGF X c μ)
  proof: by
  ext t
  simpa using! hX.integrable_exp_mul t

中文:
引理 integrableExpSet_eq_univ
  条件: (hX : HasSubgaussianMGF X c μ)
  证明: by
  ext t
  simpa using! hX.integrable_exp_mul t

Depends on / 依赖: hX.integrable_exp_mul, integrable_exp_mul
-/
lemma integrableExpSet_eq_univ (hX : HasSubgaussianMGF X c μ) :
    integrableExpSet X μ = Set.univ := by
  ext t
  simpa using! hX.integrable_exp_mul t

/--
lemma `memLp` / 引理 `memLp`

English:
lemma memLp
  given: (hX : HasSubgaussianMGF X c μ) (p : Real>=0)
  statement: MemLp X p μ
  proof: memLp_of_mem_interior_integrableExpSet (by simp [integrableExpSet_eq_univ hX]) p

中文:
引理 memLp
  条件: (hX : HasSubgaussianMGF X c μ) (p : 实数>=0)
  结论: MemLp X p μ
  证明: memLp_of_mem_interior_integrableExpSet (by simp [integrableExpSet_eq_univ hX]) p

Depends on / 依赖: integrableExpSet_eq_univ, memLp_of_mem_interior_integrableExpSet
-/
lemma memLp (hX : HasSubgaussianMGF X c μ) (p : Real>=0) : MemLp X p μ :=
  memLp_of_mem_interior_integrableExpSet (by simp [integrableExpSet_eq_univ hX]) p

/--
lemma `integrable` / 引理 `integrable`

English:
lemma integrable
  given: (hX : HasSubgaussianMGF X c μ)
  statement: Integrable X μ
  proof: integrable_of_mem_interior_integrableExpSet (by simp [integrableExpSet_eq_univ hX])

中文:
引理 integrable
  条件: (hX : HasSubgaussianMGF X c μ)
  结论: 整数egrable X μ
  证明: integrable_of_mem_interior_integrableExpSet (by simp [integrableExpSet_eq_univ hX])

Depends on / 依赖: integrableExpSet_eq_univ, integrable_of_mem_interior_integrableExpSet
-/
lemma integrable (hX : HasSubgaussianMGF X c μ) : Integrable X μ :=
  integrable_of_mem_interior_integrableExpSet (by simp [integrableExpSet_eq_univ hX])

section ChernoffBound

/--
lemma `measure_ge_le` / 引理 `measure_ge_le`

English:
lemma measure_ge_le
  given: (h : HasSubgaussianMGF X c μ) {ε : Real} (hε : 0 <= ε)
  proof: by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using h.measure_ge_le hε

中文:
引理 measure_ge_le
  条件: (h : HasSubgaussianMGF X c μ) {ε : 实数} (hε : 0 <= ε)
  证明: by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using h.measure_ge_le hε

Depends on / 依赖: HasSubgaussianMGF_iff_kernel, h.measure_ge_le, measure_ge_le
-/
lemma measure_ge_le (h : HasSubgaussianMGF X c μ) {ε : Real} (hε : 0 <= ε) :
    μ.real {ω | ε <= X ω} <= exp (-ε ^ 2 / (2 * c)) := by
  rw [HasSubgaussianMGF_iff_kernel] at h
  simpa using h.measure_ge_le hε

end ChernoffBound

section Zero

/--
lemma `ae_eq_zero_of_hasSubgaussianMGF_zero` / 引理 `ae_eq_zero_of_hasSubgaussianMGF_zero`

English:
lemma ae_eq_zero_of_hasSubgaussianMGF_zero
  given: (h : HasSubgaussianMGF X 0 μ)
  statement: X =ᵐ[μ] 0
  proof: by
  simpa using (HasSubgaussianMGF_iff_kernel.1 h).ae_eq_zero_of_hasSubgaussianMGF_zero

中文:
引理 ae_eq_zero_of_hasSubgaussianMGF_zero
  条件: (h : HasSubgaussianMGF X 0 μ)
  结论: X =ᵐ[μ] 0
  证明: by
  simpa using (HasSubgaussianMGF_iff_kernel.1 h).ae_eq_zero_of_hasSubgaussianMGF_zero

Depends on / 依赖: HasSubgaussianMGF_iff_kernel, ae_eq_zero_of_hasSubgaussianMGF_zero
-/
lemma ae_eq_zero_of_hasSubgaussianMGF_zero (h : HasSubgaussianMGF X 0 μ) : X =ᵐ[μ] 0 := by
  simpa using (HasSubgaussianMGF_iff_kernel.1 h).ae_eq_zero_of_hasSubgaussianMGF_zero

end Zero

section Add

/--
lemma `add` / 引理 `add`

English:
lemma add
  statement: {Y : Ω -> Real} {cX cY : Real>=0} (hX : HasSubgaussianMGF X cX μ)
  proof: by
  have := (HasSubgaussianMGF_iff_kernel.1 hX).add (HasSubgaussianMGF_iff_kernel.1 hY)
  simpa [HasSubgaussianMGF_iff_kernel] using this

中文:
引理 add
  结论: {Y : Ω -> 实数} {cX cY : 实数>=0} (hX : HasSubgaussianMGF X cX μ)
  证明: by
  have := (HasSubgaussianMGF_iff_kernel.1 hX).add (HasSubgaussianMGF_iff_kernel.1 hY)
  simpa [HasSubgaussianMGF_iff_kernel] using this

Depends on / 依赖: HasSubgaussianMGF_iff_kernel
-/
lemma add {Y : Ω -> Real} {cX cY : Real>=0} (hX : HasSubgaussianMGF X cX μ)
    (hY : HasSubgaussianMGF Y cY μ) :
    HasSubgaussianMGF (fun ω => X ω + Y ω) ((cX.sqrt + cY.sqrt) ^ 2) μ := by
  have := (HasSubgaussianMGF_iff_kernel.1 hX).add (HasSubgaussianMGF_iff_kernel.1 hY)
  simpa [HasSubgaussianMGF_iff_kernel] using this

/--
lemma `add_of_indepFun` / 引理 `add_of_indepFun`

English:
lemma add_of_indepFun
  statement: {Y : Ω -> Real} {cX cY : Real>=0} (hX : HasSubgaussianMGF X cX μ)
  proof: by
    simp_rw [mul_add, exp_add]
    convert! MemLp.integrable_mul (hX.memLp_exp_mul t 2) (hY.memLp_exp_mul t 2)
    norm_cast
    infer_instance
  mgf_le t := by
    calc mgf (X + Y) μ t
    _ = mgf X μ t * mgf Y μ t :=
      hindep.mgf_add (hX.integrable_exp_mul t).1 (hY.integrable_exp_mul t).1
 

中文:
引理 add_of_indepFun
  结论: {Y : Ω -> 实数} {cX cY : 实数>=0} (hX : HasSubgaussianMGF X cX μ)
  证明: by
    simp_rw [mul_add, exp_add]
    convert! MemLp.integrable_mul (hX.memLp_exp_mul t 2) (hY.memLp_exp_mul t 2)
    norm_cast
    infer_instance
  mgf_le t := by
    calc mgf (X + Y) μ t
    _ = mgf X μ t * mgf Y μ t :=
      hindep.mgf_add (hX.integrable_exp_mul t).1 (hY.integrable_exp_mul t).1
 

Depends on / 依赖: MemLp.integrable_mul, convert, exp_add, hX.integrable_exp_mul, hX.memLp_exp_mul, hX.mgf_le, hY.integrable_exp_mul, hY.memLp_exp_mul, hY.mgf_le, hindep, hindep.mgf_add, infer_instance, integrable_exp_mul, integrable_mul, memLp_exp_mul, mgf_add, mgf_le, mgf_nonneg, mul_add, simp_rw
-/
lemma add_of_indepFun {Y : Ω -> Real} {cX cY : Real>=0} (hX : HasSubgaussianMGF X cX μ)
    (hY : HasSubgaussianMGF Y cY μ) (hindep : X ⟂ᵢ[μ] Y) :
    HasSubgaussianMGF (fun ω => X ω + Y ω) (cX + cY) μ where
  integrable_exp_mul t := by
    simp_rw [mul_add, exp_add]
    convert! MemLp.integrable_mul (hX.memLp_exp_mul t 2) (hY.memLp_exp_mul t 2)
    norm_cast
    infer_instance
  mgf_le t := by
    calc mgf (X + Y) μ t
    _ = mgf X μ t * mgf Y μ t :=
      hindep.mgf_add (hX.integrable_exp_mul t).1 (hY.integrable_exp_mul t).1
    _ <= exp (cX * t ^ 2 / 2) * exp (cY * t ^ 2 / 2) := by
      gcongr
      · exact mgf_nonneg
      · exact hX.mgf_le t
      · exact hY.mgf_le t
    _ = exp ((cX + cY) * t ^ 2 / 2) := by rw [← exp_add]; congr; ring

/--
lemma `sub_of_indepFun` / 引理 `sub_of_indepFun`

English:
lemma sub_of_indepFun
  statement: {Y : Ω -> Real} {cX cY : Real>=0} (hX : HasSubgaussianMGF X cX μ)
  proof: by
  simp_rw [sub_eq_add_neg]
  exact hX.add_of_indepFun hY.neg hindep.neg_right

中文:
引理 sub_of_indepFun
  结论: {Y : Ω -> 实数} {cX cY : 实数>=0} (hX : HasSubgaussianMGF X cX μ)
  证明: by
  simp_rw [sub_eq_add_neg]
  exact hX.add_of_indepFun hY.neg hindep.neg_right

Depends on / 依赖: add_of_indepFun, hX.add_of_indepFun, hY.neg, hindep, hindep.neg_right, neg_right, simp_rw, sub_eq_add_neg
-/
lemma sub_of_indepFun {Y : Ω -> Real} {cX cY : Real>=0} (hX : HasSubgaussianMGF X cX μ)
    (hY : HasSubgaussianMGF Y cY μ) (hindep : X ⟂ᵢ[μ] Y) :
    HasSubgaussianMGF (fun ω => X ω - Y ω) (cX + cY) μ := by
  simp_rw [sub_eq_add_neg]
  exact hX.add_of_indepFun hY.neg hindep.neg_right

/--
lemma `sum_of_iIndepFun_of_forall_aemeasurable` / 引理 `sum_of_iIndepFun_of_forall_aemeasurable`

English:
lemma sum_of_iIndepFun_of_forall_aemeasurable
  proof: by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his h =>
    simp_rw [← Finset.sum_apply, Finset.sum_insert his, Pi.add_apply, Finset.sum_apply]
    have h_indep' := (h_indep.indepFun_finsetS

中文:
引理 sum_of_iIndepFun_of_forall_aemeasurable
  证明: by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his h =>
    simp_rw [← Finset.sum_apply, Finset.sum_insert his, Pi.add_apply, Finset.sum_apply]
    have h_indep' := (h_indep.indepFun_finsetS
-/
private lemma sum_of_iIndepFun_of_forall_aemeasurable
    {ι : Type*} {X : ι -> Ω -> Real} (h_indep : iIndepFun X μ) {c : ι -> Real>=0}
    (h_meas : forall i, AEMeasurable (X i) μ)
    {s : Finset ι} (h_subG : forall i in s, HasSubgaussianMGF (X i) (c i) μ) :
    HasSubgaussianMGF (fun ω => ∑ i in s, X i ω) (∑ i in s, c i) μ := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his h =>
    simp_rw [← Finset.sum_apply, Finset.sum_insert his, Pi.add_apply, Finset.sum_apply]
    have h_indep' := (h_indep.indepFun_finsetSum_of_notMem₀ h_meas his).symm
    refine add_of_indepFun (h_subG _ (Finset.mem_insert_self _ _)) (h ?_) ?_
    · exact fun i hi => h_subG _ (Finset.mem_insert_of_mem hi)
    · convert! h_indep'
      rw [Finset.sum_apply]

/--
lemma `sum_of_iIndepFun` / 引理 `sum_of_iIndepFun`

English:
lemma sum_of_iIndepFun
  statement: {ι : Type*} {X : ι -> Ω -> Real} (h_indep : iIndepFun X μ) {c : ι -> Real>=0}
  proof: by
  have : HasSubgaussianMGF (fun ω => ∑ (i : s), X i ω) (∑ (i : s), c i) μ := by
    apply sum_of_iIndepFun_of_forall_aemeasurable
    · exact h_indep.precomp Subtype.val_injective
    · exact fun i => (h_subG i i.2).aemeasurable
    · exact fun i _ => h_subG i i.2
  rw [Finset.sum_coe_sort] at th

中文:
引理 sum_of_iIndepFun
  结论: {ι : 类型} {X : ι -> Ω -> 实数} (h_indep : iIndepFun X μ) {c : ι -> 实数>=0}
  证明: by
  have : HasSubgaussianMGF (fun ω => ∑ (i : s), X i ω) (∑ (i : s), c i) μ := by
    apply sum_of_iIndepFun_of_forall_aemeasurable
    · exact h_indep.precomp Subtype.val_injective
    · exact fun i => (h_subG i i.2).aemeasurable
    · exact fun i _ => h_subG i i.2
  rw [Finset.sum_coe_sort] at th

Depends on / 依赖: Finset, Finset.sum_attach, Finset.sum_coe_sort, HasSubgaussianMGF, Subtype, Subtype.val_injective, ae_of_all, aemeasurable, h_indep, h_indep.precomp, h_subG, precomp, sum_attach, sum_coe_sort, sum_of_iIndepFun_of_forall_aemeasurable, this.congr, val_injective
-/
lemma sum_of_iIndepFun {ι : Type*} {X : ι -> Ω -> Real} (h_indep : iIndepFun X μ) {c : ι -> Real>=0}
    {s : Finset ι} (h_subG : forall i in s, HasSubgaussianMGF (X i) (c i) μ) :
    HasSubgaussianMGF (fun ω => ∑ i in s, X i ω) (∑ i in s, c i) μ := by
  have : HasSubgaussianMGF (fun ω => ∑ (i : s), X i ω) (∑ (i : s), c i) μ := by
    apply sum_of_iIndepFun_of_forall_aemeasurable
    · exact h_indep.precomp Subtype.val_injective
    · exact fun i => (h_subG i i.2).aemeasurable
    · exact fun i _ => h_subG i i.2
  rw [Finset.sum_coe_sort] at this
  exact this.congr (ae_of_all _ fun ω => Finset.sum_attach s (fun i => X i ω))

/--
lemma `measure_sum_ge_le_of_iIndepFun` / 引理 `measure_sum_ge_le_of_iIndepFun`

English:
lemma measure_sum_ge_le_of_iIndepFun
  statement: {ι : Type*} {X : ι -> Ω -> Real} (h_indep : iIndepFun X μ)
  proof: (sum_of_iIndepFun h_indep h_subG).measure_ge_le hε

中文:
引理 measure_sum_ge_le_of_iIndepFun
  结论: {ι : 类型} {X : ι -> Ω -> 实数} (h_indep : iIndepFun X μ)
  证明: (sum_of_iIndepFun h_indep h_subG).measure_ge_le hε

Depends on / 依赖: h_indep, h_subG, measure_ge_le, sum_of_iIndepFun
-/
lemma measure_sum_ge_le_of_iIndepFun {ι : Type*} {X : ι -> Ω -> Real} (h_indep : iIndepFun X μ)
    {c : ι -> Real>=0}
    {s : Finset ι} (h_subG : forall i in s, HasSubgaussianMGF (X i) (c i) μ) {ε : Real} (hε : 0 <= ε) :
    μ.real {ω | ε <= ∑ i in s, X i ω} <= exp (-ε ^ 2 / (2 * ∑ i in s, c i)) :=
  (sum_of_iIndepFun h_indep h_subG).measure_ge_le hε

/--
lemma `measure_sum_range_ge_le_of_iIndepFun` / 引理 `measure_sum_range_ge_le_of_iIndepFun`

English:
lemma measure_sum_range_ge_le_of_iIndepFun
  statement: {X : Nat -> Ω -> Real} (h_indep : iIndepFun X μ) {c : Real>=0}
  proof: by
  have h := (sum_of_iIndepFun h_indep (c := fun _ => c)
    (s := Finset.range n) (by simpa)).measure_ge_le hε
  simpa [← mul_assoc] using h

中文:
引理 measure_sum_range_ge_le_of_iIndepFun
  结论: {X : 自然数 -> Ω -> 实数} (h_indep : iIndepFun X μ) {c : 实数>=0}
  证明: by
  have h := (sum_of_iIndepFun h_indep (c := fun _ => c)
    (s := Finset.range n) (by simpa)).measure_ge_le hε
  simpa [← mul_assoc] using h

Depends on / 依赖: Finset, Finset.range, h_indep, measure_ge_le, mul_assoc, sum_of_iIndepFun
-/
lemma measure_sum_range_ge_le_of_iIndepFun {X : Nat -> Ω -> Real} (h_indep : iIndepFun X μ) {c : Real>=0}
    {n : Nat} (h_subG : forall i < n, HasSubgaussianMGF (X i) c μ) {ε : Real} (hε : 0 <= ε) :
    μ.real {ω | ε <= ∑ i in Finset.range n, X i ω} <= exp (-ε ^ 2 / (2 * n * c)) := by
  have h := (sum_of_iIndepFun h_indep (c := fun _ => c)
    (s := Finset.range n) (by simpa)).measure_ge_le hε
  simpa [← mul_assoc] using h

/--
lemma `measureReal_le_le_exp` / 引理 `measureReal_le_le_exp`

English:
lemma measureReal_le_le_exp
  statement: {Y : Ω -> Real} {cX cY : Real>=0}
  proof: by
  calc μ.real {ω | X ω <= Y ω}
  _ = μ.real {ω | (μ[X] - μ[Y]) <= (Y ω - μ[Y]) - (X ω - μ[X])} := by
    congr with ω
    grind
  _ <= Real.exp (- (μ[Y] - μ[X]) ^ 2 / (2 * (cX + cY))) := by
    refine (measure_ge_le (X := fun ω => (Y ω - μ[Y]) - (X ω - μ[X])) (c := cX + cY) ?_ ?_).trans_eq
      

中文:
引理 measureReal_le_le_exp
  结论: {Y : Ω -> 实数} {cX cY : 实数>=0}
  证明: by
  calc μ.real {ω | X ω <= Y ω}
  _ = μ.real {ω | (μ[X] - μ[Y]) <= (Y ω - μ[Y]) - (X ω - μ[X])} := by
    congr with ω
    grind
  _ <= Real.exp (- (μ[Y] - μ[X]) ^ 2 / (2 * (cX + cY))) := by
    refine (measure_ge_le (X := fun ω => (Y ω - μ[Y]) - (X ω - μ[X])) (c := cX + cY) ?_ ?_).trans_eq
      

Depends on / 依赖: Real.exp, add_comm, fun_prop, hindep, hindep.symm.comp, measure_ge_le, sub_of_indepFun, trans_eq
-/
lemma measureReal_le_le_exp {Y : Ω -> Real} {cX cY : Real>=0}
    (hX : HasSubgaussianMGF (fun ω => X ω - μ[X]) cX μ)
    (hY : HasSubgaussianMGF (fun ω => Y ω - μ[Y]) cY μ)
    (hindep : IndepFun X Y μ) (h_le : μ[Y] <= μ[X]) :
    μ.real {ω | X ω <= Y ω} <= Real.exp (- (μ[Y] - μ[X]) ^ 2 / (2 * (cX + cY))) := by
  calc μ.real {ω | X ω <= Y ω}
  _ = μ.real {ω | (μ[X] - μ[Y]) <= (Y ω - μ[Y]) - (X ω - μ[X])} := by
    congr with ω
    grind
  _ <= Real.exp (- (μ[Y] - μ[X]) ^ 2 / (2 * (cX + cY))) := by
    refine (measure_ge_le (X := fun ω => (Y ω - μ[Y]) - (X ω - μ[X])) (c := cX + cY) ?_ ?_).trans_eq
      ?_
    · rw [add_comm cX]
      refine sub_of_indepFun hY hX ?_
      exact hindep.symm.comp (φ := fun x => x - μ[Y]) (ψ := fun x => x - μ[X])
        (by fun_prop) (by fun_prop)
    · grind
    · congr 2
      grind

end Add

end HasSubgaussianMGF

section HoeffdingLemma

/--
lemma `mgf_le_of_mem_Icc_of_integral_eq_zero` / 引理 `mgf_le_of_mem_Icc_of_integral_eq_zero`

English:
lemma mgf_le_of_mem_Icc_of_integral_eq_zero
  statement: [IsProbabilityMeasure μ] {a b t : Real}
  proof: by
  have hi (u : Real) : Integrable (fun ω => exp (u * X ω)) μ := integrable_exp_mul_of_mem_Icc hm hb
  have hs : Set.Icc 0 t subseteq interior (integrableExpSet X μ) := by simp [hi, integrableExpSet]
  obtain ⟨u, h1, h2⟩ := exists_cgf_eq_iteratedDeriv_two_cgf_mul ht hc hs
  rw [← exp_cgf (hi t)]; 

中文:
引理 mgf_le_of_mem_Icc_of_integral_eq_zero
  结论: [IsProbabilityMeasure μ] {a b t : 实数}
  证明: by
  have hi (u : Real) : Integrable (fun ω => exp (u * X ω)) μ := integrable_exp_mul_of_mem_Icc hm hb
  have hs : Set.Icc 0 t subseteq interior (integrableExpSet X μ) := by simp [hi, integrableExpSet]
  obtain ⟨u, h1, h2⟩ := exists_cgf_eq_iteratedDeriv_two_cgf_mul ht hc hs
  rw [← exp_cgf (hi t)]; 
-/
protected lemma mgf_le_of_mem_Icc_of_integral_eq_zero [IsProbabilityMeasure μ] {a b t : Real}
    (hm : AEMeasurable X μ) (hb : forallᵐ ω ∂μ, X ω in Set.Icc a b) (hc : μ[X] = 0) (ht : 0 < t) :
    mgf X μ t <= exp ((‖b - a‖₊ / 2) ^ 2 * t ^ 2 / 2) := by
  have hi (u : Real) : Integrable (fun ω => exp (u * X ω)) μ := integrable_exp_mul_of_mem_Icc hm hb
  have hs : Set.Icc 0 t subseteq interior (integrableExpSet X μ) := by simp [hi, integrableExpSet]
  obtain ⟨u, h1, h2⟩ := exists_cgf_eq_iteratedDeriv_two_cgf_mul ht hc hs
  rw [← exp_cgf (hi t)]; rw [exp_le_exp]; rw [h2]
  gcongr
  calc
  _ = Var[X; μ.tilted (u * X ·)] := by
    rw [← variance_tilted_mul (hs (Set.mem_Icc_of_Ioo h1))]
  _ <= ((b - a) / 2) ^ 2 := by
    convert! variance_le_sq_of_bounded ((tilted_absolutelyContinuous μ (u * X ·)) hb) _
    · exact isProbabilityMeasure_tilted (hi u)
    · exact hm.mono_ac (tilted_absolutelyContinuous μ (u * X ·))
  _ = (‖b - a‖₊ / 2) ^ 2 := by simp [field]

/--
lemma `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` / 引理 `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`

English:
lemma hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
  statement: [IsProbabilityMeasure μ] {a b : Real}
  proof: integrable_exp_mul_of_mem_Icc hm hb
  mgf_le t := by
    obtain ht | ht | ht := lt_trichotomy 0 t
    · exact ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero hm hb hc ht
    · simp [← ht]
    calc
    _ = mgf (-X) μ (-t) := by simp [mgf]
    _ <= exp ((‖-a - -b‖₊ / 2) ^ 2 * (-t) ^ 2 / 2) := 

中文:
引理 hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
  结论: [IsProbabilityMeasure μ] {a b : 实数}
  证明: integrable_exp_mul_of_mem_Icc hm hb
  mgf_le t := by
    obtain ht | ht | ht := lt_trichotomy 0 t
    · exact ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero hm hb hc ht
    · simp [← ht]
    calc
    _ = mgf (-X) μ (-t) := by simp [mgf]
    _ <= exp ((‖-a - -b‖₊ / 2) ^ 2 * (-t) ^ 2 / 2) := 

Depends on / 依赖: integrable_exp_mul_of_mem_Icc
-/
lemma hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero [IsProbabilityMeasure μ] {a b : Real}
    (hm : AEMeasurable X μ) (hb : forallᵐ ω ∂μ, X ω in Set.Icc a b) (hc : μ[X] = 0) :
    HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2) μ where
  integrable_exp_mul t := integrable_exp_mul_of_mem_Icc hm hb
  mgf_le t := by
    obtain ht | ht | ht := lt_trichotomy 0 t
    · exact ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero hm hb hc ht
    · simp [← ht]
    calc
    _ = mgf (-X) μ (-t) := by simp [mgf]
    _ <= exp ((‖-a - -b‖₊ / 2) ^ 2 * (-t) ^ 2 / 2) := by
      apply ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero (hm.neg)
      · filter_upwards [hb] with ω ⟨hl, hr⟩ using ⟨neg_le_neg_iff.2 hr, neg_le_neg_iff.2 hl⟩
      · simp only [Pi.neg_apply]; rw [integral_neg, hc, neg_zero]
      · rwa [Left.neg_pos_iff]
    _ = exp (((‖b - a‖₊ / 2) ^ 2) * t ^ 2 / 2) := by ring_nf

/--
lemma `hasSubgaussianMGF_of_mem_Icc` / 引理 `hasSubgaussianMGF_of_mem_Icc`

English:
lemma hasSubgaussianMGF_of_mem_Icc
  statement: [IsProbabilityMeasure μ] {a b : Real} (hm : AEMeasurable X μ)
  proof: by
  rw [← sub_sub_sub_cancel_right b a μ[X]]
  apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hm.sub_const _)
  · filter_upwards [hb] with ω hab using by simpa using hab
  · simp [integral_sub (Integrable.of_mem_Icc a b hm hb) (integrable_const _)]

中文:
引理 hasSubgaussianMGF_of_mem_Icc
  结论: [IsProbabilityMeasure μ] {a b : 实数} (hm : AEMeasurable X μ)
  证明: by
  rw [← sub_sub_sub_cancel_right b a μ[X]]
  apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hm.sub_const _)
  · filter_upwards [hb] with ω hab using by simpa using hab
  · simp [integral_sub (Integrable.of_mem_Icc a b hm hb) (integrable_const _)]

Depends on / 依赖: Integrable, Integrable.of_mem_Icc, filter_upwards, hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero, hm.sub_const, integrable_const, integral_sub, of_mem_Icc, sub_const, sub_sub_sub_cancel_right
-/
lemma hasSubgaussianMGF_of_mem_Icc [IsProbabilityMeasure μ] {a b : Real} (hm : AEMeasurable X μ)
    (hb : forallᵐ ω ∂μ, X ω in Set.Icc a b) :
    HasSubgaussianMGF (fun ω => X ω - μ[X]) ((‖b - a‖₊ / 2) ^ 2) μ := by
  rw [← sub_sub_sub_cancel_right b a μ[X]]
  apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hm.sub_const _)
  · filter_upwards [hb] with ω hab using by simpa using hab
  · simp [integral_sub (Integrable.of_mem_Icc a b hm hb) (integrable_const _)]

end HoeffdingLemma

section Martingale

variable [StandardBorelSpace Ω]

/--
lemma `HasSubgaussianMGF.add_of_hasCondSubgaussianMGF` / 引理 `HasSubgaussianMGF.add_of_hasCondSubgaussianMGF`

English:
lemma HasSubgaussianMGF.add_of_hasCondSubgaussianMGF
  statement: [IsFiniteMeasure μ]
  proof: by
  suffices HasSubgaussianMGF (fun p => X p.1 + Y p.2) (cX + cY)
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ) by
    have h_eq : X + Y = (fun p => X p.1 + Y p.2) ∘ Function.diag := rfl
    rw [h_eq]
    refine HasSubgaussianMGF.of_map ?_ this
    exact @Measurable.aemeasurable _ _

中文:
引理 HasSubgaussianMGF.add_of_hasCondSubgaussianMGF
  结论: [IsFiniteMeasure μ]
  证明: by
  suffices HasSubgaussianMGF (fun p => X p.1 + Y p.2) (cX + cY)
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ) by
    have h_eq : X + Y = (fun p => X p.1 + Y p.2) ∘ Function.diag := rfl
    rw [h_eq]
    refine HasSubgaussianMGF.of_map ?_ this
    exact @Measurable.aemeasurable _ _

Depends on / 依赖: Function, Function.diag, HasSubgaussianMGF, HasSubgaussianMGF.of_map, HasSubgaussianMGF_iff_kernel, Kernel, Kernel.HasSubgaussianMGF, Kernel.const, Measurable, Measurable.aemeasurable, Measure, Measure.dirac, Measure.map, aemeasurable, condExpKernel, h_eq, m.prod, measurable_id, of_map, prodMk
-/
lemma HasSubgaussianMGF.add_of_hasCondSubgaussianMGF [IsFiniteMeasure μ]
    {Y : Ω -> Real} {cX cY : Real>=0} (hm : m <= mΩ)
    (hX : HasSubgaussianMGF X cX (μ.trim hm)) (hY : HasCondSubgaussianMGF m hm Y cY μ) :
    HasSubgaussianMGF (X + Y) (cX + cY) μ := by
  suffices HasSubgaussianMGF (fun p => X p.1 + Y p.2) (cX + cY)
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ) by
    have h_eq : X + Y = (fun p => X p.1 + Y p.2) ∘ Function.diag := rfl
    rw [h_eq]
    refine HasSubgaussianMGF.of_map ?_ this
    exact @Measurable.aemeasurable _ _ _ (m.prod mΩ) _ _
      ((measurable_id'' hm).prodMk measurable_id)
  rw [HasSubgaussianMGF_iff_kernel] at hX ⊢
  have hY' : Kernel.HasSubgaussianMGF Y cY (condExpKernel μ m)
      (Kernel.const Unit (μ.trim hm) ∘ₘ Measure.dirac ()) := by simpa
  convert! hX.add_comp hY'
  ext
  rw [Kernel.const_apply]; rw [← Measure.compProd]; rw [compProd_trim_condExpKernel]

@[deprecated (since := "2026-01-27")]
alias HasSubgaussianMGF_add_of_HasCondSubgaussianMGF :=
  HasSubgaussianMGF.add_of_hasCondSubgaussianMGF

variable {Y : Nat -> Ω -> Real} {cY : Nat -> Real>=0} {ℱ : Filtration Nat mΩ}

/--
lemma `HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF` / 引理 `HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF`

English:
lemma HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF
  statement: [IsZeroOrProbabilityMeasure μ]
  proof: by
  induction n with
  | zero => simp
  | succ n hn =>
    induction n with
    | zero => simp [h0]
    | succ n =>
      specialize hn fun i hi => h_subG i (by lia)
      simp_rw [Finset.sum_range_succ _ (n + 1)]
      refine HasSubgaussianMGF.add_of_hasCondSubgaussianMGF (ℱ.le n) ?_ (h_subG n (by

中文:
引理 HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF
  结论: [IsZeroOrProbabilityMeasure μ]
  证明: by
  induction n with
  | zero => simp
  | succ n hn =>
    induction n with
    | zero => simp [h0]
    | succ n =>
      specialize hn fun i hi => h_subG i (by lia)
      simp_rw [Finset.sum_range_succ _ (n + 1)]
      refine HasSubgaussianMGF.add_of_hasCondSubgaussianMGF (ℱ.le n) ?_ (h_subG n (by

Depends on / 依赖: Finset, Finset.measurable_fun_sum, Finset.mem_range, Finset.range, Finset.sum_range_succ, HasSubgaussianMGF, HasSubgaussianMGF.add_of_hasCondSubgaussianMGF, HasSubgaussianMGF.trim, add_of_hasCondSubgaussianMGF, h_adapted, h_subG, measurable, measurable_fun_sum, mem_range, simp_rw, specialize, sum_range_succ
-/
lemma HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF [IsZeroOrProbabilityMeasure μ]
    (h_adapted : StronglyAdapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ) (n : Nat)
    (h_subG : forall i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ) :
    HasSubgaussianMGF (fun ω => ∑ i in Finset.range n, Y i ω) (∑ i in Finset.range n, cY i) μ := by
  induction n with
  | zero => simp
  | succ n hn =>
    induction n with
    | zero => simp [h0]
    | succ n =>
      specialize hn fun i hi => h_subG i (by lia)
      simp_rw [Finset.sum_range_succ _ (n + 1)]
      refine HasSubgaussianMGF.add_of_hasCondSubgaussianMGF (ℱ.le n) ?_ (h_subG n (by lia))
      refine HasSubgaussianMGF.trim (ℱ.le n) ?_ hn
      refine Finset.measurable_fun_sum (Finset.range (n + 1)) fun m hm =>
        ((h_adapted m).mono (ℱ.mono ?_)).measurable
      simp only [Finset.mem_range] at hm
      lia

@[deprecated (since := "2026-01-27")]
alias HasSubgaussianMGF_sum_of_HasCondSubgaussianMGF :=
  HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF

/--
lemma `measure_sum_ge_le_of_hasCondSubgaussianMGF` / 引理 `measure_sum_ge_le_of_hasCondSubgaussianMGF`

English:
lemma measure_sum_ge_le_of_hasCondSubgaussianMGF
  statement: [IsZeroOrProbabilityMeasure μ]
  proof: (HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF h_adapted h0 n h_subG).measure_ge_le hε

@[deprecated (since := "2026-01-27")]
alias measure_sum_ge_le_of_HasCondSubgaussianMGF := measure_sum_ge_le_of_hasCondSubgaussianMGF

中文:
引理 measure_sum_ge_le_of_hasCondSubgaussianMGF
  结论: [IsZeroOrProbabilityMeasure μ]
  证明: (HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF h_adapted h0 n h_subG).measure_ge_le hε

@[deprecated (since := "2026-01-27")]
alias measure_sum_ge_le_of_HasCondSubgaussianMGF := measure_sum_ge_le_of_hasCondSubgaussianMGF

Depends on / 依赖: HasSubgaussianMGF, HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF, h_adapted, h_subG, measure_ge_le, sum_of_hasCondSubgaussianMGF
-/
lemma measure_sum_ge_le_of_hasCondSubgaussianMGF [IsZeroOrProbabilityMeasure μ]
    (h_adapted : StronglyAdapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ) (n : Nat)
    (h_subG : forall i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ)
    {ε : Real} (hε : 0 <= ε) :
    μ.real {ω | ε <= ∑ i in Finset.range n, Y i ω}
      <= exp (-ε ^ 2 / (2 * ∑ i in Finset.range n, cY i)) :=
  (HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF h_adapted h0 n h_subG).measure_ge_le hε

@[deprecated (since := "2026-01-27")]
alias measure_sum_ge_le_of_HasCondSubgaussianMGF := measure_sum_ge_le_of_hasCondSubgaussianMGF

end Martingale

end ProbabilityTheory
