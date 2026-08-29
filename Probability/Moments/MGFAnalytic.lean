/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Calculus.Taylor

/-!
# The moment-generating function is analytic

The moment-generating function `mgf X μ` of a random variable `X` with respect to a measure `μ`
is analytic on the interior of `integrableExpSet X μ`, the interval on which it is defined.

## Main results

* `analyticOn_mgf`: the moment-generating function is analytic on the interior of the interval
  on which it is defined.
* `iteratedDeriv_mgf`: the n-th derivative of the mgf at `t` is `μ[X ^ n * exp (t * X)]`.

* `analyticOn_cgf`: the cumulant-generating function is analytic on the interior of the interval
  `integrableExpSet X μ`.

-/

public section


open MeasureTheory Filter Finset Real

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology Nat

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω -> Real} {μ : Measure Ω} {t u v : Real}

/--
lemma `hasDerivAt_integral_pow_mul_exp_real` / 引理 `hasDerivAt_integral_pow_mul_exp_real`

English:
lemma hasDerivAt_integral_pow_mul_exp_real
  given: (ht : t in interior (integrableExpSet X μ)) (n : Nat)
  proof: by
  have h_re_of_mem n t (ht' : t in interior (integrableExpSet X μ)) :
      (∫ ω, X ω ^ n * Complex.exp (t * X ω) ∂μ).re = ∫ ω, X ω ^ n * exp (t * X ω) ∂μ := by
    rw [← RCLike.re_eq_complex_re]; rw [← integral_re]
    · norm_cast
    · refine integrable_pow_mul_cexp_of_re_mem_interior_integrabl

中文:
引理 hasDerivAt_integral_pow_mul_exp_real
  条件: (ht : t in interior (integrableExpSet X μ)) (n : 自然数)
  证明: by
  have h_re_of_mem n t (ht' : t in interior (integrableExpSet X μ)) :
      (∫ ω, X ω ^ n * Complex.exp (t * X ω) ∂μ).re = ∫ ω, X ω ^ n * exp (t * X ω) ∂μ := by
    rw [← RCLike.re_eq_complex_re]; rw [← integral_re]
    · norm_cast
    · refine integrable_pow_mul_cexp_of_re_mem_interior_integrabl

Depends on / 依赖: Complex.exp, RCLike, RCLike.re_eq_complex_re, eventually_mem, filter_upwards, h_re, h_re_of_mem, integrableExpSet, integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet, integral_re, interior, isOpen_interior, isOpen_interior.eventually_mem, re_eq_complex_re
-/
lemma hasDerivAt_integral_pow_mul_exp_real (ht : t in interior (integrableExpSet X μ)) (n : Nat) :
    HasDerivAt (fun t => μ[fun ω => X ω ^ n * exp (t * X ω)])
      μ[fun ω => X ω ^ (n + 1) * exp (t * X ω)] t := by
  have h_re_of_mem n t (ht' : t in interior (integrableExpSet X μ)) :
      (∫ ω, X ω ^ n * Complex.exp (t * X ω) ∂μ).re = ∫ ω, X ω ^ n * exp (t * X ω) ∂μ := by
    rw [← RCLike.re_eq_complex_re]; rw [← integral_re]
    · norm_cast
    · refine integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet ?_ n
      simpa using ht'
  have h_re n : forallᶠ t' : Real in 𝓝 t, (∫ ω, X ω ^ n * Complex.exp (t' * X ω) ∂μ).re
      = ∫ ω, X ω ^ n * exp (t' * X ω) ∂μ := by
    filter_upwards [isOpen_interior.eventually_mem ht] with t ht' using h_re_of_mem n t ht'
  rw [← EventuallyEq.hasDerivAt_iff (h_re _)]; rw [← h_re_of_mem _ t ht]
  exact (hasDerivAt_integral_pow_mul_exp (by simp [ht]) n).real_of_complex

section DerivMGF

/--
lemma `hasDerivAt_mgf` / 引理 `hasDerivAt_mgf`

English:
lemma hasDerivAt_mgf
  given: (h : t in interior (integrableExpSet X μ))
  proof: by
  convert! hasDerivAt_integral_pow_mul_exp_real h 0
  · simp [mgf]
  · simp

中文:
引理 hasDerivAt_mgf
  条件: (h : t in interior (integrableExpSet X μ))
  证明: by
  convert! hasDerivAt_integral_pow_mul_exp_real h 0
  · simp [mgf]
  · simp

Depends on / 依赖: convert, hasDerivAt_integral_pow_mul_exp_real
-/
lemma hasDerivAt_mgf (h : t in interior (integrableExpSet X μ)) :
    HasDerivAt (mgf X μ) (μ[fun ω => X ω * exp (t * X ω)]) t := by
  convert! hasDerivAt_integral_pow_mul_exp_real h 0
  · simp [mgf]
  · simp

/--
lemma `hasDerivAt_iteratedDeriv_mgf` / 引理 `hasDerivAt_iteratedDeriv_mgf`

English:
lemma hasDerivAt_iteratedDeriv_mgf
  given: (ht : t in interior (integrableExpSet X μ)) (n : Nat)
  proof: by
  induction n generalizing t with
  | zero => simp [hasDerivAt_mgf ht]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    have : deriv (iteratedDeriv n (mgf X μ))
        =ᶠ[𝓝 t] fun t => μ[fun ω => X ω ^ (n + 1) * exp (t * X ω)] := by
      have h_mem : forallᶠ y in 𝓝 t, y in interior (integrableE

中文:
引理 hasDerivAt_iteratedDeriv_mgf
  条件: (ht : t in interior (integrableExpSet X μ)) (n : 自然数)
  证明: by
  induction n generalizing t with
  | zero => simp [hasDerivAt_mgf ht]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    have : deriv (iteratedDeriv n (mgf X μ))
        =ᶠ[𝓝 t] fun t => μ[fun ω => X ω ^ (n + 1) * exp (t * X ω)] := by
      have h_mem : forallᶠ y in 𝓝 t, y in interior (integrableE

Depends on / 依赖: EventuallyEq, EventuallyEq.hasDerivAt_iff, HasDerivAt, HasDerivAt.deriv, eventually_mem, filter_upwards, generalizing, h_mem, hasDerivAt_iff, hasDerivAt_integral_pow_mul_exp_real, hasDerivAt_mgf, integrableExpSet, interior, isOpen_interior, isOpen_interior.eventually_mem, iteratedDeriv, iteratedDeriv_succ
-/
lemma hasDerivAt_iteratedDeriv_mgf (ht : t in interior (integrableExpSet X μ)) (n : Nat) :
    HasDerivAt (iteratedDeriv n (mgf X μ)) μ[fun ω => X ω ^ (n + 1) * exp (t * X ω)] t := by
  induction n generalizing t with
  | zero => simp [hasDerivAt_mgf ht]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    have : deriv (iteratedDeriv n (mgf X μ))
        =ᶠ[𝓝 t] fun t => μ[fun ω => X ω ^ (n + 1) * exp (t * X ω)] := by
      have h_mem : forallᶠ y in 𝓝 t, y in interior (integrableExpSet X μ) :=
        isOpen_interior.eventually_mem ht
      filter_upwards [h_mem] with y hy using HasDerivAt.deriv (hn hy)
    rw [EventuallyEq.hasDerivAt_iff this]
    exact hasDerivAt_integral_pow_mul_exp_real ht (n + 1)

/--
lemma `iteratedDeriv_mgf` / 引理 `iteratedDeriv_mgf`

English:
lemma iteratedDeriv_mgf
  given: (ht : t in interior (integrableExpSet X μ)) (n : Nat)
  proof: by
  induction n generalizing t with
  | zero => simp [mgf]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    exact (hasDerivAt_iteratedDeriv_mgf ht n).deriv

中文:
引理 iteratedDeriv_mgf
  条件: (ht : t in interior (integrableExpSet X μ)) (n : 自然数)
  证明: by
  induction n generalizing t with
  | zero => simp [mgf]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    exact (hasDerivAt_iteratedDeriv_mgf ht n).deriv

Depends on / 依赖: generalizing, hasDerivAt_iteratedDeriv_mgf, iteratedDeriv_succ
-/
lemma iteratedDeriv_mgf (ht : t in interior (integrableExpSet X μ)) (n : Nat) :
    iteratedDeriv n (mgf X μ) t = μ[fun ω => X ω ^ n * exp (t * X ω)] := by
  induction n generalizing t with
  | zero => simp [mgf]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    exact (hasDerivAt_iteratedDeriv_mgf ht n).deriv

/--
lemma `iteratedDeriv_mgf_zero` / 引理 `iteratedDeriv_mgf_zero`

English:
lemma iteratedDeriv_mgf_zero
  given: (h : 0 in interior (integrableExpSet X μ)) (n : Nat)
  proof: by
  simp [iteratedDeriv_mgf h n]

中文:
引理 iteratedDeriv_mgf_zero
  条件: (h : 0 in interior (integrableExpSet X μ)) (n : 自然数)
  证明: by
  simp [iteratedDeriv_mgf h n]

Depends on / 依赖: iteratedDeriv_mgf
-/
lemma iteratedDeriv_mgf_zero (h : 0 in interior (integrableExpSet X μ)) (n : Nat) :
    iteratedDeriv n (mgf X μ) 0 = μ[X ^ n] := by
  simp [iteratedDeriv_mgf h n]

/--
lemma `deriv_mgf` / 引理 `deriv_mgf`

English:
lemma deriv_mgf
  given: (h : t in interior (integrableExpSet X μ))
  proof: (hasDerivAt_mgf h).deriv

中文:
引理 deriv_mgf
  条件: (h : t in interior (integrableExpSet X μ))
  证明: (hasDerivAt_mgf h).deriv

Depends on / 依赖: hasDerivAt_mgf
-/
lemma deriv_mgf (h : t in interior (integrableExpSet X μ)) :
    deriv (mgf X μ) t = μ[fun ω => X ω * exp (t * X ω)] :=
  (hasDerivAt_mgf h).deriv

/--
lemma `deriv_mgf_zero` / 引理 `deriv_mgf_zero`

English:
lemma deriv_mgf_zero
  given: (h : 0 in interior (integrableExpSet X μ))
  statement: deriv (mgf X μ) 0 = μ[X]
  proof: by
  simp [deriv_mgf h]

中文:
引理 deriv_mgf_zero
  条件: (h : 0 in interior (integrableExpSet X μ))
  结论: deriv (mgf X μ) 0 = μ[X]
  证明: by
  simp [deriv_mgf h]

Depends on / 依赖: deriv_mgf
-/
lemma deriv_mgf_zero (h : 0 in interior (integrableExpSet X μ)) : deriv (mgf X μ) 0 = μ[X] := by
  simp [deriv_mgf h]

end DerivMGF

section AnalyticMGF

/--
lemma `analyticAt_mgf` / 引理 `analyticAt_mgf`

English:
lemma analyticAt_mgf
  given: (ht : t in interior (integrableExpSet X μ))
  proof: by
  rw [← re_complexMGF_ofReal']
  exact (analyticAt_complexMGF (by simp [ht])).re_ofReal

中文:
引理 analyticAt_mgf
  条件: (ht : t in interior (integrableExpSet X μ))
  证明: by
  rw [← re_complexMGF_ofReal']
  exact (analyticAt_complexMGF (by simp [ht])).re_ofReal

Depends on / 依赖: analyticAt_complexMGF, re_complexMGF_ofReal, re_ofReal
-/
lemma analyticAt_mgf (ht : t in interior (integrableExpSet X μ)) :
    AnalyticAt Real (mgf X μ) t := by
  rw [← re_complexMGF_ofReal']
  exact (analyticAt_complexMGF (by simp [ht])).re_ofReal

/--
lemma `analyticOnNhd_mgf` / 引理 `analyticOnNhd_mgf`

English:
lemma analyticOnNhd_mgf
  statement: AnalyticOnNhd Real (mgf X μ) (interior (integrableExpSet X μ))
  proof: fun _ hx => analyticAt_mgf hx

中文:
引理 analyticOnNhd_mgf
  结论: AnalyticOnNhd 实数 (mgf X μ) (interior (integrableExpSet X μ))
  证明: fun _ hx => analyticAt_mgf hx

Depends on / 依赖: analyticAt_mgf
-/
lemma analyticOnNhd_mgf : AnalyticOnNhd Real (mgf X μ) (interior (integrableExpSet X μ)) :=
  fun _ hx => analyticAt_mgf hx

/--
lemma `analyticOn_mgf` / 引理 `analyticOn_mgf`

English:
lemma analyticOn_mgf
  statement: AnalyticOn Real (mgf X μ) (interior (integrableExpSet X μ))
  proof: analyticOnNhd_mgf.analyticOn

中文:
引理 analyticOn_mgf
  结论: AnalyticOn 实数 (mgf X μ) (interior (integrableExpSet X μ))
  证明: analyticOnNhd_mgf.analyticOn

Depends on / 依赖: P.asIdeal, analyticOn, analyticOnNhd_mgf, analyticOnNhd_mgf.analyticOn, asIdeal
-/
lemma analyticOn_mgf : AnalyticOn Real (mgf X μ) (interior (integrableExpSet X μ)) :=
  analyticOnNhd_mgf.analyticOn

/--
lemma `hasFPowerSeriesAt_mgf` / 引理 `hasFPowerSeriesAt_mgf`

English:
lemma hasFPowerSeriesAt_mgf
  given: (hv : v in interior (integrableExpSet X μ))
  proof: by
  convert! (analyticAt_mgf hv).hasFPowerSeriesAt
  rw [iteratedDeriv_mgf hv]

中文:
引理 hasFPowerSeriesAt_mgf
  条件: (hv : v in interior (integrableExpSet X μ))
  证明: by
  convert! (analyticAt_mgf hv).hasFPowerSeriesAt
  rw [iteratedDeriv_mgf hv]

Depends on / 依赖: analyticAt_mgf, convert, hasFPowerSeriesAt, iteratedDeriv_mgf
-/
lemma hasFPowerSeriesAt_mgf (hv : v in interior (integrableExpSet X μ)) :
    HasFPowerSeriesAt (mgf X μ)
      (FormalMultilinearSeries.ofScalars Real
        (fun n => (μ[fun ω => X ω ^ n * exp (v * X ω)] : Real) / n !)) v := by
  convert! (analyticAt_mgf hv).hasFPowerSeriesAt
  rw [iteratedDeriv_mgf hv]

/--
lemma `differentiableAt_mgf` / 引理 `differentiableAt_mgf`

English:
lemma differentiableAt_mgf
  given: (ht : t in interior (integrableExpSet X μ))
  proof: (analyticAt_mgf ht).differentiableAt

中文:
引理 differentiableAt_mgf
  条件: (ht : t in interior (integrableExpSet X μ))
  证明: (analyticAt_mgf ht).differentiableAt

Depends on / 依赖: analyticAt_mgf, differentiableAt
-/
lemma differentiableAt_mgf (ht : t in interior (integrableExpSet X μ)) :
    DifferentiableAt Real (mgf X μ) t := (analyticAt_mgf ht).differentiableAt

/--
lemma `differentiableOn_mgf` / 引理 `differentiableOn_mgf`

English:
lemma differentiableOn_mgf
  statement: DifferentiableOn Real (mgf X μ) (interior (integrableExpSet X μ))
  proof: fun _ hx => (differentiableAt_mgf hx).differentiableWithinAt

中文:
引理 differentiableOn_mgf
  结论: DifferentiableOn 实数 (mgf X μ) (interior (integrableExpSet X μ))
  证明: fun _ hx => (differentiableAt_mgf hx).differentiableWithinAt

Depends on / 依赖: differentiableAt_mgf, differentiableWithinAt
-/
lemma differentiableOn_mgf : DifferentiableOn Real (mgf X μ) (interior (integrableExpSet X μ)) :=
  fun _ hx => (differentiableAt_mgf hx).differentiableWithinAt

-- todo: this should be extended to `integrableExpSet X μ`, not only its interior
/--
lemma `continuousOn_mgf` / 引理 `continuousOn_mgf`

English:
lemma continuousOn_mgf
  statement: ContinuousOn (mgf X μ) (interior (integrableExpSet X μ))
  proof: differentiableOn_mgf.continuousOn

中文:
引理 continuousOn_mgf
  结论: ContinuousOn (mgf X μ) (interior (integrableExpSet X μ))
  证明: differentiableOn_mgf.continuousOn

Depends on / 依赖: continuousOn, differentiableOn_mgf, differentiableOn_mgf.continuousOn
-/
lemma continuousOn_mgf : ContinuousOn (mgf X μ) (interior (integrableExpSet X μ)) :=
  differentiableOn_mgf.continuousOn

/--
lemma `continuous_mgf` / 引理 `continuous_mgf`

English:
lemma continuous_mgf
  given: (h : forall t, Integrable (fun ω => exp (t * X ω)) μ)
  proof: by
  rw [← continuousOn_univ]
  convert! continuousOn_mgf
  symm
  rw [interior_eq_univ]
  ext t
  simpa using! h t

中文:
引理 continuous_mgf
  条件: (h : 对任意 t, 整数egrable (fun ω => exp (t * X ω)) μ)
  证明: by
  rw [← continuousOn_univ]
  convert! continuousOn_mgf
  symm
  rw [interior_eq_univ]
  ext t
  simpa using! h t

Depends on / 依赖: continuousOn_mgf, continuousOn_univ, convert, interior_eq_univ
-/
lemma continuous_mgf (h : forall t, Integrable (fun ω => exp (t * X ω)) μ) :
    Continuous (mgf X μ) := by
  rw [← continuousOn_univ]
  convert! continuousOn_mgf
  symm
  rw [interior_eq_univ]
  ext t
  simpa using! h t

/--
lemma `analyticOnNhd_iteratedDeriv_mgf` / 引理 `analyticOnNhd_iteratedDeriv_mgf`

English:
lemma analyticOnNhd_iteratedDeriv_mgf
  given: (n : Nat)
  proof: by
  rw [iteratedDeriv_eq_iterate]
  exact analyticOnNhd_mgf.iterated_deriv n

中文:
引理 analyticOnNhd_iteratedDeriv_mgf
  条件: (n : 自然数)
  证明: by
  rw [iteratedDeriv_eq_iterate]
  exact analyticOnNhd_mgf.iterated_deriv n

Depends on / 依赖: analyticOnNhd_mgf, analyticOnNhd_mgf.iterated_deriv, iteratedDeriv_eq_iterate, iterated_deriv
-/
lemma analyticOnNhd_iteratedDeriv_mgf (n : Nat) :
    AnalyticOnNhd Real (iteratedDeriv n (mgf X μ)) (interior (integrableExpSet X μ)) := by
  rw [iteratedDeriv_eq_iterate]
  exact analyticOnNhd_mgf.iterated_deriv n

/--
lemma `analyticOn_iteratedDeriv_mgf` / 引理 `analyticOn_iteratedDeriv_mgf`

English:
lemma analyticOn_iteratedDeriv_mgf
  given: (n : Nat)
  proof: (analyticOnNhd_iteratedDeriv_mgf n).analyticOn

中文:
引理 analyticOn_iteratedDeriv_mgf
  条件: (n : 自然数)
  证明: (analyticOnNhd_iteratedDeriv_mgf n).analyticOn

Depends on / 依赖: analyticOn, analyticOnNhd_iteratedDeriv_mgf
-/
lemma analyticOn_iteratedDeriv_mgf (n : Nat) :
    AnalyticOn Real (iteratedDeriv n (mgf X μ)) (interior (integrableExpSet X μ)) :=
  (analyticOnNhd_iteratedDeriv_mgf n).analyticOn

/--
lemma `analyticAt_iteratedDeriv_mgf` / 引理 `analyticAt_iteratedDeriv_mgf`

English:
lemma analyticAt_iteratedDeriv_mgf
  given: (hv : v in interior (integrableExpSet X μ)) (n : Nat)
  proof: analyticOnNhd_iteratedDeriv_mgf n v hv

中文:
引理 analyticAt_iteratedDeriv_mgf
  条件: (hv : v in interior (integrableExpSet X μ)) (n : 自然数)
  证明: analyticOnNhd_iteratedDeriv_mgf n v hv

Depends on / 依赖: analyticOnNhd_iteratedDeriv_mgf
-/
lemma analyticAt_iteratedDeriv_mgf (hv : v in interior (integrableExpSet X μ)) (n : Nat) :
    AnalyticAt Real (iteratedDeriv n (mgf X μ)) v :=
  analyticOnNhd_iteratedDeriv_mgf n v hv

/--
lemma `differentiableAt_iteratedDeriv_mgf` / 引理 `differentiableAt_iteratedDeriv_mgf`

English:
lemma differentiableAt_iteratedDeriv_mgf
  given: (hv : v in interior (integrableExpSet X μ)) (n : Nat)
  proof: (analyticAt_iteratedDeriv_mgf hv n).differentiableAt

中文:
引理 differentiableAt_iteratedDeriv_mgf
  条件: (hv : v in interior (integrableExpSet X μ)) (n : 自然数)
  证明: (analyticAt_iteratedDeriv_mgf hv n).differentiableAt

Depends on / 依赖: analyticAt_iteratedDeriv_mgf, differentiableAt
-/
lemma differentiableAt_iteratedDeriv_mgf (hv : v in interior (integrableExpSet X μ)) (n : Nat) :
    DifferentiableAt Real (iteratedDeriv n (mgf X μ)) v :=
  (analyticAt_iteratedDeriv_mgf hv n).differentiableAt

end AnalyticMGF

section AnalyticCGF

/--
lemma `analyticAt_cgf` / 引理 `analyticAt_cgf`

English:
lemma analyticAt_cgf
  given: (h : v in interior (integrableExpSet X μ))
  statement: AnalyticAt Real (cgf X μ) v
  proof: by
  by_cases hμ : μ = 0
  · simp only [hμ, cgf_zero_measure]
    exact analyticAt_const
· exact (analyticAt_mgf h).log mgf_pos' hμ (interior_subset (s := integrableExpSet X μ) h)

中文:
引理 analyticAt_cgf
  条件: (h : v in interior (integrableExpSet X μ))
  结论: AnalyticAt 实数 (cgf X μ) v
  证明: by
  by_cases hμ : μ = 0
  · simp only [hμ, cgf_zero_measure]
    exact analyticAt_const
· exact (analyticAt_mgf h).log mgf_pos' hμ (interior_subset (s := integrableExpSet X μ) h)

Depends on / 依赖: analyticAt_const, analyticAt_mgf, cgf_zero_measure, integrableExpSet, interior_subset, mgf_pos
-/
lemma analyticAt_cgf (h : v in interior (integrableExpSet X μ)) : AnalyticAt Real (cgf X μ) v := by
  by_cases hμ : μ = 0
  · simp only [hμ, cgf_zero_measure]
    exact analyticAt_const
· exact (analyticAt_mgf h).log mgf_pos' hμ (interior_subset (s := integrableExpSet X μ) h)

/--
lemma `analyticOnNhd_cgf` / 引理 `analyticOnNhd_cgf`

English:
lemma analyticOnNhd_cgf
  statement: AnalyticOnNhd Real (cgf X μ) (interior (integrableExpSet X μ))
  proof: fun _ hx => analyticAt_cgf hx

中文:
引理 analyticOnNhd_cgf
  结论: AnalyticOnNhd 实数 (cgf X μ) (interior (integrableExpSet X μ))
  证明: fun _ hx => analyticAt_cgf hx

Depends on / 依赖: analyticAt_cgf
-/
lemma analyticOnNhd_cgf : AnalyticOnNhd Real (cgf X μ) (interior (integrableExpSet X μ)) :=
  fun _ hx => analyticAt_cgf hx

/--
lemma `analyticOn_cgf` / 引理 `analyticOn_cgf`

English:
lemma analyticOn_cgf
  statement: AnalyticOn Real (cgf X μ) (interior (integrableExpSet X μ))
  proof: analyticOnNhd_cgf.analyticOn

中文:
引理 analyticOn_cgf
  结论: AnalyticOn 实数 (cgf X μ) (interior (integrableExpSet X μ))
  证明: analyticOnNhd_cgf.analyticOn

Depends on / 依赖: analyticOn, analyticOnNhd_cgf, analyticOnNhd_cgf.analyticOn
-/
lemma analyticOn_cgf : AnalyticOn Real (cgf X μ) (interior (integrableExpSet X μ)) :=
  analyticOnNhd_cgf.analyticOn

end AnalyticCGF

section DerivCGF

/--
lemma `deriv_cgf` / 引理 `deriv_cgf`

English:
lemma deriv_cgf
  given: (h : v in interior (integrableExpSet X μ))
  proof: by
  by_cases hμ : μ = 0
  · simp only [hμ, cgf_zero_measure, integral_zero_measure, mgf_zero_measure, div_zero,
      Pi.zero_apply]
    exact deriv_const v 0
  have hv : Integrable (fun ω => exp (v * X ω)) μ := interior_subset (s := integrableExpSet X μ) h
  calc deriv (fun x => log (mgf X μ x)) v

中文:
引理 deriv_cgf
  条件: (h : v in interior (integrableExpSet X μ))
  证明: by
  by_cases hμ : μ = 0
  · simp only [hμ, cgf_zero_measure, integral_zero_measure, mgf_zero_measure, div_zero,
      Pi.zero_apply]
    exact deriv_const v 0
  have hv : Integrable (fun ω => exp (v * X ω)) μ := interior_subset (s := integrableExpSet X μ) h
  calc deriv (fun x => log (mgf X μ x)) v

Depends on / 依赖: Integrable, Pi.zero_apply, cgf_zero_measure, deriv.log, deriv_const, deriv_mgf, differentiableAt_mgf, div_zero, integrableExpSet, integral_zero_measure, interior_subset, mgf_pos, mgf_zero_measure, zero_apply
-/
lemma deriv_cgf (h : v in interior (integrableExpSet X μ)) :
    deriv (cgf X μ) v = μ[fun ω => X ω * exp (v * X ω)] / mgf X μ v := by
  by_cases hμ : μ = 0
  · simp only [hμ, cgf_zero_measure, integral_zero_measure, mgf_zero_measure, div_zero,
      Pi.zero_apply]
    exact deriv_const v 0
  have hv : Integrable (fun ω => exp (v * X ω)) μ := interior_subset (s := integrableExpSet X μ) h
  calc deriv (fun x => log (mgf X μ x)) v
  _ = deriv (mgf X μ) v / mgf X μ v := by
    rw [deriv.log (differentiableAt_mgf h) ((mgf_pos' hμ hv).ne')]
  _ = μ[fun ω => X ω * exp (v * X ω)] / mgf X μ v := by rw [deriv_mgf h]

/--
lemma `deriv_cgf_zero` / 引理 `deriv_cgf_zero`

English:
lemma deriv_cgf_zero
  given: (h : 0 in interior (integrableExpSet X μ))
  proof: by simp [deriv_cgf h]

中文:
引理 deriv_cgf_zero
  条件: (h : 0 in interior (integrableExpSet X μ))
  证明: by simp [deriv_cgf h]

Depends on / 依赖: deriv_cgf
-/
lemma deriv_cgf_zero (h : 0 in interior (integrableExpSet X μ)) :
    deriv (cgf X μ) 0 = μ[X] / μ.real Set.univ := by simp [deriv_cgf h]

/--
lemma `iteratedDeriv_two_cgf` / 引理 `iteratedDeriv_two_cgf`

English:
lemma iteratedDeriv_two_cgf
  given: (h : v in interior (integrableExpSet X μ))
  proof: by
  rw [iteratedDeriv_succ]; rw [iteratedDeriv_one]
  by_cases hμ : μ = 0
  · simp [hμ]
  have h_mem : forallᶠ y in 𝓝 v, y in interior (integrableExpSet X μ) :=
    isOpen_interior.eventually_mem h
  have h_d_cgf : deriv (cgf X μ) =ᶠ[𝓝 v] fun u => μ[fun ω => X ω * exp (u * X ω)] / mgf X μ u := by
 

中文:
引理 iteratedDeriv_two_cgf
  条件: (h : v in interior (integrableExpSet X μ))
  证明: by
  rw [iteratedDeriv_succ]; rw [iteratedDeriv_one]
  by_cases hμ : μ = 0
  · simp [hμ]
  have h_mem : forallᶠ y in 𝓝 v, y in interior (integrableExpSet X μ) :=
    isOpen_interior.eventually_mem h
  have h_d_cgf : deriv (cgf X μ) =ᶠ[𝓝 v] fun u => μ[fun ω => X ω * exp (u * X ω)] / mgf X μ u := by
 

Depends on / 依赖: deriv_cgf, deriv_eq, deriv_mgf, eventually_mem, filter_upwards, h_d_cgf, h_d_cgf.deriv_eq, h_d_mgf, h_mem, integrableExpSet, interior, isOpen_interior, isOpen_interior.eventually_mem, iteratedDeriv_one, iteratedDeriv_succ
-/
lemma iteratedDeriv_two_cgf (h : v in interior (integrableExpSet X μ)) :
    iteratedDeriv 2 (cgf X μ) v
      = μ[fun ω => (X ω) ^ 2 * exp (v * X ω)] / mgf X μ v - deriv (cgf X μ) v ^ 2 := by
  rw [iteratedDeriv_succ]; rw [iteratedDeriv_one]
  by_cases hμ : μ = 0
  · simp [hμ]
  have h_mem : forallᶠ y in 𝓝 v, y in interior (integrableExpSet X μ) :=
    isOpen_interior.eventually_mem h
  have h_d_cgf : deriv (cgf X μ) =ᶠ[𝓝 v] fun u => μ[fun ω => X ω * exp (u * X ω)] / mgf X μ u := by
    filter_upwards [h_mem] with u hu using deriv_cgf hu
  have h_d_mgf : deriv (mgf X μ) =ᶠ[𝓝 v] fun u => μ[fun ω => X ω * exp (u * X ω)] := by
    filter_upwards [h_mem] with u hu using deriv_mgf hu
  rw [h_d_cgf.deriv_eq]
  calc deriv (fun u => (∫ ω, X ω * exp (u * X ω) ∂μ) / mgf X μ u) v
  _ = (deriv (fun u => ∫ ω, X ω * exp (u * X ω) ∂μ) v * mgf X μ v -
      (∫ ω, X ω * exp (v * X ω) ∂μ) * deriv (mgf X μ) v) / mgf X μ v ^ 2 := by
    rw [deriv_fun_div]
    · rw [h_d_mgf.symm.differentiableAt_iff, ← iteratedDeriv_one]
      exact differentiableAt_iteratedDeriv_mgf h 1
    · exact differentiableAt_mgf h
    · exact (mgf_pos' hμ (interior_subset (s := integrableExpSet X μ) h)).ne'
  _ = (deriv (fun u => ∫ ω, X ω * exp (u * X ω) ∂μ) v * mgf X μ v -
      (∫ ω, X ω * exp (v * X ω) ∂μ) * ∫ ω, X ω * exp (v * X ω) ∂μ) / mgf X μ v ^ 2 := by
    rw [deriv_mgf h]
  _ = deriv (fun u => ∫ ω, X ω * exp (u * X ω) ∂μ) v / mgf X μ v - deriv (cgf X μ) v ^ 2 := by
    rw [sub_div]
    congr 1
    · rw [pow_two, div_mul_eq_div_div, mul_div_assoc, div_self, mul_one]
      exact (mgf_pos' hμ (interior_subset (s := integrableExpSet X μ) h)).ne'
    · rw [deriv_cgf h]
      ring
  _ = (∫ ω, (X ω) ^ 2 * exp (v * X ω) ∂μ) / mgf X μ v - deriv (cgf X μ) v ^ 2 := by
    congr
    convert! (hasDerivAt_integral_pow_mul_exp_real h 1).deriv using 1
    simp

/--
lemma `iteratedDeriv_two_cgf_eq_integral` / 引理 `iteratedDeriv_two_cgf_eq_integral`

English:
lemma iteratedDeriv_two_cgf_eq_integral
  given: (h : v in interior (integrableExpSet X μ))
  proof: by
  by_cases hμ : μ = 0
  · simp [hμ]
  rw [iteratedDeriv_two_cgf h]
  calc (∫ ω, (X ω) ^ 2 * exp (v * X ω) ∂μ) / mgf X μ v - deriv (cgf X μ) v ^ 2
  _ = (∫ ω, (X ω) ^ 2 * exp (v * X ω) ∂μ - 2 * (∫ ω, X ω * exp (v * X ω) ∂μ) * deriv (cgf X μ) v
      + deriv (cgf X μ) v ^ 2 * mgf X μ v) / mgf X μ v

中文:
引理 iteratedDeriv_two_cgf_eq_integral
  条件: (h : v in interior (integrableExpSet X μ))
  证明: by
  by_cases hμ : μ = 0
  · simp [hμ]
  rw [iteratedDeriv_two_cgf h]
  calc (∫ ω, (X ω) ^ 2 * exp (v * X ω) ∂μ) / mgf X μ v - deriv (cgf X μ) v ^ 2
  _ = (∫ ω, (X ω) ^ 2 * exp (v * X ω) ∂μ - 2 * (∫ ω, X ω * exp (v * X ω) ∂μ) * deriv (cgf X μ) v
      + deriv (cgf X μ) v ^ 2 * mgf X μ v) / mgf X μ v

Depends on / 依赖: add_div, deriv_cgf, integrableExpSet, interior_subset, iteratedDeriv_two_cgf, mgf_pos, sub_add, sub_div
-/
lemma iteratedDeriv_two_cgf_eq_integral (h : v in interior (integrableExpSet X μ)) :
    iteratedDeriv 2 (cgf X μ) v
      = μ[fun ω => (X ω - deriv (cgf X μ) v) ^ 2 * exp (v * X ω)] / mgf X μ v := by
  by_cases hμ : μ = 0
  · simp [hμ]
  rw [iteratedDeriv_two_cgf h]
  calc (∫ ω, (X ω) ^ 2 * exp (v * X ω) ∂μ) / mgf X μ v - deriv (cgf X μ) v ^ 2
  _ = (∫ ω, (X ω) ^ 2 * exp (v * X ω) ∂μ - 2 * (∫ ω, X ω * exp (v * X ω) ∂μ) * deriv (cgf X μ) v
      + deriv (cgf X μ) v ^ 2 * mgf X μ v) / mgf X μ v := by
    rw [add_div]; rw [sub_div]; rw [sub_add]
    congr 1
    rw [mul_div_cancel_right₀]; rw [deriv_cgf h]
    · ring
    · exact (mgf_pos' hμ (interior_subset (s := integrableExpSet X μ) h)).ne'
  _ = (∫ ω, ((X ω) ^ 2 - 2 * X ω * deriv (cgf X μ) v + deriv (cgf X μ) v ^ 2) * exp (v * X ω) ∂μ)
      / mgf X μ v := by
    congr 1
    simp_rw [add_mul, sub_mul]
    have h_int : Integrable (fun ω => 2 * X ω * deriv (cgf X μ) v * exp (v * X ω)) μ := by
      simp_rw [mul_assoc, mul_comm (deriv (cgf X μ) v)]
      refine Integrable.const_mul ?_ _
      simp_rw [← mul_assoc]
      refine Integrable.mul_const ?_ _
      convert! integrable_pow_mul_exp_of_mem_interior_integrableExpSet h 1
      simp
    rw [integral_add]
    rotate_left
    · exact (integrable_pow_mul_exp_of_mem_interior_integrableExpSet h 2).sub h_int
    · exact (interior_subset (s := integrableExpSet X μ) h).const_mul _
    rw [integral_sub (integrable_pow_mul_exp_of_mem_interior_integrableExpSet h 2) h_int]
    congr
    · rw [← integral_const_mul, ← integral_mul_const]
      congr with ω
      ring
    · rw [integral_const_mul, mgf]
  _ = (∫ ω, (X ω - deriv (cgf X μ) v) ^ 2 * exp (v * X ω) ∂μ) / mgf X μ v := by
    congr with ω
    ring

/--
lemma `exists_cgf_eq_iteratedDeriv_two_cgf_mul` / 引理 `exists_cgf_eq_iteratedDeriv_two_cgf_mul`

English:
lemma exists_cgf_eq_iteratedDeriv_two_cgf_mul
  statement: [IsZeroOrProbabilityMeasure μ] (ht : 0 < t)
  proof: by
  have hu : UniqueDiffOn Real (Set.Icc 0 t) := uniqueDiffOn_Icc ht
  rw [← sub_zero (cgf X μ t)]
  nth_rw 3 [← sub_zero t]
  rw [← Set.uIoo_of_lt ht]
  convert! taylor_mean_remainder_lagrange_iteratedDeriv ht.ne ?_
  · have hd : derivWithin (cgf X μ) (Set.Icc 0 t) 0 = 0 := by
      convert! (anal

中文:
引理 exists_cgf_eq_iteratedDeriv_two_cgf_mul
  结论: [IsZeroOrProbabilityMeasure μ] (ht : 0 < t)
  证明: by
  have hu : UniqueDiffOn Real (Set.Icc 0 t) := uniqueDiffOn_Icc ht
  rw [← sub_zero (cgf X μ t)]
  nth_rw 3 [← sub_zero t]
  rw [← Set.uIoo_of_lt ht]
  convert! taylor_mean_remainder_lagrange_iteratedDeriv ht.ne ?_
  · have hd : derivWithin (cgf X μ) (Set.Icc 0 t) 0 = 0 := by
      convert! (anal

Depends on / 依赖: Set.Icc, Set.uIcc_of_lt, Set.uIoo_of_lt, UniqueDiffOn, analyticAt_cgf, convert, derivWithin, deriv_cgf_zero, differentiableAt, differentiableAt.derivWithin, ht.ne, le_of_lt, le_refl, nth_rw, sub_zero, taylor_mean_remainder_lagrange_iteratedDeriv, uIcc_of_lt, uIoo_of_lt, uniqueDiffOn_Icc
-/
lemma exists_cgf_eq_iteratedDeriv_two_cgf_mul [IsZeroOrProbabilityMeasure μ] (ht : 0 < t)
    (hc : μ[X] = 0) (hs : Set.Icc 0 t subseteq interior (integrableExpSet X μ)) :
    exists u in Set.Ioo 0 t, cgf X μ t = (iteratedDeriv 2 (cgf X μ) u) * t ^ 2 / 2 := by
  have hu : UniqueDiffOn Real (Set.Icc 0 t) := uniqueDiffOn_Icc ht
  rw [← sub_zero (cgf X μ t)]
  nth_rw 3 [← sub_zero t]
  rw [← Set.uIoo_of_lt ht]
  convert! taylor_mean_remainder_lagrange_iteratedDeriv ht.ne ?_
  · have hd : derivWithin (cgf X μ) (Set.Icc 0 t) 0 = 0 := by
      convert! (analyticAt_cgf (hs ⟨le_refl 0, le_of_lt ht⟩)).differentiableAt.derivWithin _
      · simpa [hc] using (deriv_cgf_zero (hs ⟨le_refl 0, le_of_lt ht⟩)).symm
      · exact hu 0 ⟨le_refl 0, le_of_lt ht⟩
    simp [hd, Set.uIcc_of_lt ht]
  · rw [Set.uIcc_of_lt ht]
    exact (analyticOn_cgf.mono hs).contDiffOn hu

end DerivCGF

end ProbabilityTheory
