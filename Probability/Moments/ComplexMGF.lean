/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# The complex-valued moment-generating function

The moment-generating function (mgf) is `t : ℝ ↦ μ[fun ω ↦ rexp (t * X ω)]`. It can be extended to
a complex function `z : ℂ ↦ μ[fun ω ↦ cexp (z * X ω)]`, which we call `complexMGF X μ`.
That function is holomorphic on the vertical strip with base the interior of the interval
of definition of the mgf.
On the vertical line that goes through 0, `complexMGF X μ` is equal to the characteristic function.
This allows us to link properties of the characteristic function and the mgf (mostly deducing
properties of the mgf from those of the characteristic function).

## Main definitions

* `complexMGF X μ`: the function `z : ℂ ↦ μ[fun ω ↦ cexp (z * X ω)]`.

## Main results

* `complexMGF_ofReal`: for `x : ℝ`, `complexMGF X μ x = mgf X μ x`.

* `hasDerivAt_complexMGF`: for all `z : ℂ` such that the real part `z.re` belongs to the interior
  of the interval of definition of the mgf, `complexMGF X μ` is differentiable at `z`
  with derivative `μ[X * exp (z * X)]`.
* `differentiableOn_complexMGF`: `complexMGF X μ` is holomorphic on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`.
* `analyticOn_complexMGF`: `complexMGF X μ` is analytic on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`.

* `eqOn_complexMGF_of_mgf`: if two random variables have the same moment-generating function,
  then they have the same `complexMGF` on the vertical strip
  `{z | z.re ∈ interior (integrableExpSet X μ)}`.
  Once we know that equal `mgf` implies equal distributions, we will be able to show that
  the `complexMGF` are equal everywhere, not only on the strip.
  This lemma will be used in the proof of the equality of distributions.

* `ext_of_complexMGF_eq`: If the complex moment-generating functions of two random variables `X`
  and `Y` with respect to the finite measures `μ`, `μ'`, respectively, coincide, then
  `μ.map X = μ'.map Y`. In other words, complex moment-generating functions separate the
  distributions of random variables.

## TODO

* Prove that if two random variables have the same `mgf`, then the have the same `complexMGF`.

-/

@[expose] public section


open MeasureTheory Filter Finset Real Complex

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω -> Real} {μ : Measure Ω} {t u v : Real} {z ε : Complex}

/-- Complex extension of the moment-generating function. -/
noncomputable
/--
Definition of `complexMGF` / `complexMGF` 的定义

English:
definition complexMGF
  signature: (X : Ω -> Real) (μ : Measure Ω) (z : Complex)
  body: ∫ ω, cexp (z * X ω) ∂μ

中文:
定义 complexMGF
  签名: (X : Ω -> 实数) (μ : 测度 Ω) (z : 复形)
  定义体: ∫ ω, cexp (z * X ω) ∂μ
-/
def complexMGF (X : Ω -> Real) (μ : Measure Ω) (z : Complex) : Complex := ∫ ω, cexp (z * X ω) ∂μ

/--
lemma `complexMGF_undef` / 引理 `complexMGF_undef`

English:
lemma complexMGF_undef
  given: (hX : AEMeasurable X μ) (h : ¬ Integrable (fun ω => rexp (z.re * X ω)) μ)
  proof: by
  rw [complexMGF]; rw [integral_undef]
  rw [← integrable_norm_iff (by fun_prop)]
  simpa [Complex.norm_exp] using h

中文:
引理 complexMGF_undef
  条件: (hX : 几乎处处可测 X μ) (h : ¬ 可积 (fun ω => rexp (z.re * X ω)) μ)
  证明: by
  rw [complexMGF]; rw [integral_undef]
  rw [← integrable_norm_iff (by fun_prop)]
  simpa [Complex.norm_exp] using h

Depends on / 依赖: Complex.norm_exp, complexMGF, fun_prop, integrable_norm_iff, integral_undef, norm_exp
-/
lemma complexMGF_undef (hX : AEMeasurable X μ) (h : ¬ Integrable (fun ω => rexp (z.re * X ω)) μ) :
    complexMGF X μ z = 0 := by
  rw [complexMGF]; rw [integral_undef]
  rw [← integrable_norm_iff (by fun_prop)]
  simpa [Complex.norm_exp] using h

/--
lemma `complexMGF_id_map` / 引理 `complexMGF_id_map`

English:
lemma complexMGF_id_map
  given: (hX : AEMeasurable X μ)
  statement: complexMGF id (μ.map X) = complexMGF X μ
  proof: by
  ext t
  rw [complexMGF]; rw [integral_map hX]
  · rfl
  · fun_prop

中文:
引理 complexMGF_id_map
  条件: (hX : 几乎处处可测 X μ)
  结论: complexMGF id (μ.map X) = complexMGF X μ
  证明: by
  ext t
  rw [complexMGF]; rw [integral_map hX]
  · rfl
  · fun_prop

Depends on / 依赖: complexMGF, fun_prop, integral_map
-/
lemma complexMGF_id_map (hX : AEMeasurable X μ) : complexMGF id (μ.map X) = complexMGF X μ := by
  ext t
  rw [complexMGF]; rw [integral_map hX]
  · rfl
  · fun_prop

/--
lemma `complexMGF_congr_identDistrib` / 引理 `complexMGF_congr_identDistrib`

English:
lemma complexMGF_congr_identDistrib
  statement: {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
  proof: by
  rw [← complexMGF_id_map h.aemeasurable_fst]; rw [← complexMGF_id_map h.aemeasurable_snd]; rw [h.map_eq]

中文:
引理 complexMGF_congr_identDistrib
  结论: {Ω' : 类型} {mΩ' : 可测空间 Ω'} {μ' : 测度 Ω'}
  证明: by
  rw [← complexMGF_id_map h.aemeasurable_fst]; rw [← complexMGF_id_map h.aemeasurable_snd]; rw [h.map_eq]

Depends on / 依赖: aemeasurable_fst, aemeasurable_snd, complexMGF_id_map, h.aemeasurable_fst, h.aemeasurable_snd, h.map_eq, map_eq
-/
lemma complexMGF_congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {Y : Ω' -> Real} (h : IdentDistrib X Y μ μ') :
    complexMGF X μ = complexMGF Y μ' := by
  rw [← complexMGF_id_map h.aemeasurable_fst]; rw [← complexMGF_id_map h.aemeasurable_snd]; rw [h.map_eq]

/--
lemma `norm_complexMGF_le_mgf` / 引理 `norm_complexMGF_le_mgf`

English:
lemma norm_complexMGF_le_mgf
  statement: ‖complexMGF X μ z‖ <= mgf X μ z.re
  proof: by
  rw [complexMGF]; rw [← re_add_im z]
  simp_rw [add_mul, Complex.exp_add, re_add_im]
  calc ‖∫ ω, cexp (z.re * X ω) * cexp (z.im * I * X ω) ∂μ‖
  _ <= ∫ ω, ‖cexp (z.re * X ω) * cexp (z.im * I * X ω)‖ ∂μ := norm_integral_le_integral_norm _
  _ = ∫ ω, rexp (z.re * X ω) ∂μ := by simp [Complex.norm_exp]

中文:
引理 norm_complexMGF_le_mgf
  结论: ‖complexMGF X μ z‖ <= mgf X μ z.re
  证明: by
  rw [complexMGF]; rw [← re_add_im z]
  simp_rw [add_mul, Complex.exp_add, re_add_im]
  calc ‖∫ ω, cexp (z.re * X ω) * cexp (z.im * I * X ω) ∂μ‖
  _ <= ∫ ω, ‖cexp (z.re * X ω) * cexp (z.im * I * X ω)‖ ∂μ := norm_integral_le_integral_norm _
  _ = ∫ ω, rexp (z.re * X ω) ∂μ := by simp [Complex.norm_exp]

Depends on / 依赖: Complex.exp_add, Complex.norm_exp, add_mul, complexMGF, exp_add, norm_exp, norm_integral_le_integral_norm, re_add_im, simp_rw, z.im, z.re
-/
lemma norm_complexMGF_le_mgf : ‖complexMGF X μ z‖ <= mgf X μ z.re := by
  rw [complexMGF]; rw [← re_add_im z]
  simp_rw [add_mul, Complex.exp_add, re_add_im]
  calc ‖∫ ω, cexp (z.re * X ω) * cexp (z.im * I * X ω) ∂μ‖
  _ <= ∫ ω, ‖cexp (z.re * X ω) * cexp (z.im * I * X ω)‖ ∂μ := norm_integral_le_integral_norm _
  _ = ∫ ω, rexp (z.re * X ω) ∂μ := by simp [Complex.norm_exp]

/--
lemma `complexMGF_ofReal` / 引理 `complexMGF_ofReal`

English:
lemma complexMGF_ofReal
  given: (x : Real)
  statement: complexMGF X μ x = mgf X μ x
  proof: by
  rw [complexMGF]; rw [mgf]
  norm_cast

中文:
引理 complexMGF_of实数
  条件: (x : 实数)
  结论: complexMGF X μ x = mgf X μ x
  证明: by
  rw [complexMGF]; rw [mgf]
  norm_cast

Depends on / 依赖: complexMGF
-/
lemma complexMGF_ofReal (x : Real) : complexMGF X μ x = mgf X μ x := by
  rw [complexMGF]; rw [mgf]
  norm_cast

/--
lemma `re_complexMGF_ofReal` / 引理 `re_complexMGF_ofReal`

English:
lemma re_complexMGF_ofReal
  given: (x : Real)
  statement: (complexMGF X μ x).re = mgf X μ x
  proof: by
  simp [complexMGF_ofReal]

中文:
引理 re_complexMGF_of实数
  条件: (x : 实数)
  结论: (complexMGF X μ x).re = mgf X μ x
  证明: by
  simp [complexMGF_ofReal]

Depends on / 依赖: complexMGF_ofReal
-/
lemma re_complexMGF_ofReal (x : Real) : (complexMGF X μ x).re = mgf X μ x := by
  simp [complexMGF_ofReal]

/--
lemma `re_complexMGF_ofReal'` / 引理 `re_complexMGF_ofReal'`

English:
lemma re_complexMGF_ofReal'
  statement: (fun x : Real => (complexMGF X μ x).re) = mgf X μ
  proof: by
  ext x
  exact re_complexMGF_ofReal x

中文:
引理 re_complexMGF_of实数'
  结论: (fun x : 实数 => (complexMGF X μ x).re) = mgf X μ
  证明: by
  ext x
  exact re_complexMGF_ofReal x

Depends on / 依赖: re_complexMGF_ofReal
-/
lemma re_complexMGF_ofReal' : (fun x : Real => (complexMGF X μ x).re) = mgf X μ := by
  ext x
  exact re_complexMGF_ofReal x

/--
lemma `complexMGF_id_mul_I` / 引理 `complexMGF_id_mul_I`

English:
lemma complexMGF_id_mul_I
  given: {μ : Measure Real} (t : Real)
  proof: by
  simp only [complexMGF, id_eq, charFun, RCLike.inner_apply, conj_trivial, ofReal_mul]
  congr with x
  ring_nf

中文:
引理 complexMGF_id_mul_I
  条件: {μ : 测度 实数} (t : 实数)
  证明: by
  simp only [complexMGF, id_eq, charFun, RCLike.inner_apply, conj_trivial, ofReal_mul]
  congr with x
  ring_nf

Depends on / 依赖: RCLike, RCLike.inner_apply, charFun, complexMGF, conj_trivial, id_eq, inner_apply, ofReal_mul, ring_nf
-/
lemma complexMGF_id_mul_I {μ : Measure Real} (t : Real) :
    complexMGF id μ (t * I) = charFun μ t := by
  simp only [complexMGF, id_eq, charFun, RCLike.inner_apply, conj_trivial, ofReal_mul]
  congr with x
  ring_nf

/--
lemma `complexMGF_mul_I` / 引理 `complexMGF_mul_I`

English:
lemma complexMGF_mul_I
  given: (hX : AEMeasurable X μ) (t : Real)
  proof: by
  rw [← complexMGF_id_map hX]; rw [complexMGF_id_mul_I]

中文:
引理 complexMGF_mul_I
  条件: (hX : 几乎处处可测 X μ) (t : 实数)
  证明: by
  rw [← complexMGF_id_map hX]; rw [complexMGF_id_mul_I]

Depends on / 依赖: complexMGF_id_map, complexMGF_id_mul_I
-/
lemma complexMGF_mul_I (hX : AEMeasurable X μ) (t : Real) :
    complexMGF X μ (t * I) = charFun (μ.map X) t := by
  rw [← complexMGF_id_map hX]; rw [complexMGF_id_mul_I]

section Analytic

/--
lemma `hasDerivAt_integral_pow_mul_exp` / 引理 `hasDerivAt_integral_pow_mul_exp`

English:
lemma hasDerivAt_integral_pow_mul_exp
  given: (hz : z.re in interior (integrableExpSet X μ)) (n : Nat)
  proof: by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  have hz' := hz
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hz'
  obtain ⟨l, u, hlu, h_subset⟩ := hz'
  let t := ((z.re - l) ⊓ (u - z.re)) / 2
  have h_pos : 0 < (z.re - l) ⊓ (u - z.re) := by simp [hlu.1, hlu.2]
  have ht : 0 < t := half_pos h_pos
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun ω => |X ω| ^ (n + 1) * rexp (z.re * X ω + t / 2 * |X ω|))
    (F := fun z ω => X ω ^ n * cexp (z * X ω))
    (F' := fun z ω => X ω ^ (n + 1) * cexp (z * X ω)) (Metric.ball_mem_nhds _ (half_pos ht))
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact .of_forall fun z => by fun_prop
  · exact integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet hz n
  · fun_prop
  · refine ae_of_all _ fun ω ε hε => ?_
    simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs]
    rw [Complex.norm_exp]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    gcongr
    have : ε = z + (ε - z) := by simp
    rw [this]; rw [add_re]; rw [add_mul]
    gcongr _ + ?_
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    gcongr
    refine (abs_re_le_norm _).trans ?_
    simp only [Metric.mem_ball, dist_eq_norm] at hε
    exact hε.le
  · refine integrable_pow_abs_mul_exp_add_of_integrable_exp_mul ?_ ?_ ?_ ?_ (t := t) (n + 1)
    · exact h_subset (add_half_inf_sub_mem_Ioo hlu)
    · exact h_subset (sub_half_inf_sub_mem_Ioo hlu)
    · positivity
    · exact lt_of_lt_of_le (by simp [ht]) (le_abs_self _)
  · refine ae_of_all _ fun ω ε hε => ?_
    simp_rw [pow_succ, mul_assoc]
    refine HasDerivAt.const_mul _ ?_
    simp_rw [← smul_eq_mul, Complex.exp_eq_exp_Complex]
    convert! hasDerivAt_exp_smul_const (X ω : Complex) ε using 1
    rw [smul_eq_mul]; rw [mul_comm]

中文:
引理 hasDerivAt_integral_pow_mul_exp
  条件: (hz : z.re in interior (integrableExpSet X μ)) (n : 自然数)
  证明: by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  have hz' := hz
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hz'
  obtain ⟨l, u, hlu, h_subset⟩ := hz'
  let t := ((z.re - l) ⊓ (u - z.re)) / 2
  have h_pos : 0 < (z.re - l) ⊓ (u - z.re) := by simp [hlu.1, hlu.2]
  have ht : 0 < t := half_pos h_pos
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun ω => |X ω| ^ (n + 1) * rexp (z.re * X ω + t / 2 * |X ω|))
    (F := fun z ω => X ω ^ n * cexp (z * X ω))
    (F' := fun z ω => X ω ^ (n + 1) * cexp (z * X ω)) (Metric.ball_mem_nhds _ (half_pos ht))
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact .of_forall fun z => by fun_prop
  · exact integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet hz n
  · fun_prop
  · refine ae_of_all _ fun ω ε hε => ?_
    simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs]
    rw [Complex.norm_exp]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    gcongr
    have : ε = z + (ε - z) := by simp
    rw [this]; rw [add_re]; rw [add_mul]
    gcongr _ + ?_
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    gcongr
    refine (abs_re_le_norm _).trans ?_
    simp only [Metric.mem_ball, dist_eq_norm] at hε
    exact hε.le
  · refine integrable_pow_abs_mul_exp_add_of_integrable_exp_mul ?_ ?_ ?_ ?_ (t := t) (n + 1)
    · exact h_subset (add_half_inf_sub_mem_Ioo hlu)
    · exact h_subset (sub_half_inf_sub_mem_Ioo hlu)
    · positivity
    · exact lt_of_lt_of_le (by simp [ht]) (le_abs_self _)
  · refine ae_of_all _ fun ω ε hε => ?_
    simp_rw [pow_succ, mul_assoc]
    refine HasDerivAt.const_mul _ ?_
    simp_rw [← smul_eq_mul, Complex.exp_eq_exp_Complex]
    convert! hasDerivAt_exp_smul_const (X ω : Complex) ε using 1
    rw [smul_eq_mul]; rw [mul_comm]

Depends on / 依赖: AEMeasurable, aemeasurable_of_mem_interior_integrableExpSet, h_pos, h_subset, half_pos, hasDerivAt_integral_of_dominated_loc_of_deriv_le, mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset, z.re
-/
lemma hasDerivAt_integral_pow_mul_exp (hz : z.re in interior (integrableExpSet X μ)) (n : Nat) :
    HasDerivAt (fun z => μ[fun ω => X ω ^ n * cexp (z * X ω)])
        μ[fun ω => X ω ^ (n + 1) * cexp (z * X ω)] z := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  have hz' := hz
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hz'
  obtain ⟨l, u, hlu, h_subset⟩ := hz'
  let t := ((z.re - l) ⊓ (u - z.re)) / 2
  have h_pos : 0 < (z.re - l) ⊓ (u - z.re) := by simp [hlu.1, hlu.2]
  have ht : 0 < t := half_pos h_pos
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun ω => |X ω| ^ (n + 1) * rexp (z.re * X ω + t / 2 * |X ω|))
    (F := fun z ω => X ω ^ n * cexp (z * X ω))
    (F' := fun z ω => X ω ^ (n + 1) * cexp (z * X ω)) (Metric.ball_mem_nhds _ (half_pos ht))
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact .of_forall fun z => by fun_prop
  · exact integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet hz n
  · fun_prop
  · refine ae_of_all _ fun ω ε hε => ?_
    simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs]
    rw [Complex.norm_exp]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    gcongr
    have : ε = z + (ε - z) := by simp
    rw [this]; rw [add_re]; rw [add_mul]
    gcongr _ + ?_
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    gcongr
    refine (abs_re_le_norm _).trans ?_
    simp only [Metric.mem_ball, dist_eq_norm] at hε
    exact hε.le
  · refine integrable_pow_abs_mul_exp_add_of_integrable_exp_mul ?_ ?_ ?_ ?_ (t := t) (n + 1)
    · exact h_subset (add_half_inf_sub_mem_Ioo hlu)
    · exact h_subset (sub_half_inf_sub_mem_Ioo hlu)
    · positivity
    · exact lt_of_lt_of_le (by simp [ht]) (le_abs_self _)
  · refine ae_of_all _ fun ω ε hε => ?_
    simp_rw [pow_succ, mul_assoc]
    refine HasDerivAt.const_mul _ ?_
    simp_rw [← smul_eq_mul, Complex.exp_eq_exp_Complex]
    convert! hasDerivAt_exp_smul_const (X ω : Complex) ε using 1
    rw [smul_eq_mul]; rw [mul_comm]

/--
theorem `hasDerivAt_complexMGF` / 定理 `hasDerivAt_complexMGF`

English:
theorem hasDerivAt_complexMGF
  given: (hz : z.re in interior (integrableExpSet X μ))
  proof: by
  convert! hasDerivAt_integral_pow_mul_exp hz 0
  · simp [complexMGF]
  · simp

中文:
定理 hasDerivAt_complexMGF
  条件: (hz : z.re in interior (integrableExpSet X μ))
  证明: by
  convert! hasDerivAt_integral_pow_mul_exp hz 0
  · simp [complexMGF]
  · simp

Depends on / 依赖: complexMGF, convert, hasDerivAt_integral_pow_mul_exp
-/
theorem hasDerivAt_complexMGF (hz : z.re in interior (integrableExpSet X μ)) :
    HasDerivAt (complexMGF X μ) μ[fun ω => X ω * cexp (z * X ω)] z := by
  convert! hasDerivAt_integral_pow_mul_exp hz 0
  · simp [complexMGF]
  · simp

/--
theorem `differentiableOn_complexMGF` / 定理 `differentiableOn_complexMGF`

English:
theorem differentiableOn_complexMGF
  proof: by
  intro z hz
  have h := hasDerivAt_complexMGF hz
  rw [hasDerivAt_iff_hasFDerivAt] at h
  exact h.hasFDerivWithinAt.differentiableWithinAt

中文:
定理 differentiableOn_complexMGF
  证明: by
  intro z hz
  have h := hasDerivAt_complexMGF hz
  rw [hasDerivAt_iff_hasFDerivAt] at h
  exact h.hasFDerivWithinAt.differentiableWithinAt

Depends on / 依赖: differentiableWithinAt, h.hasFDerivWithinAt.differentiableWithinAt, hasDerivAt_complexMGF, hasDerivAt_iff_hasFDerivAt, hasFDerivWithinAt
-/
theorem differentiableOn_complexMGF :
    DifferentiableOn Complex (complexMGF X μ) {z | z.re in interior (integrableExpSet X μ)} := by
  intro z hz
  have h := hasDerivAt_complexMGF hz
  rw [hasDerivAt_iff_hasFDerivAt] at h
  exact h.hasFDerivWithinAt.differentiableWithinAt

/--
theorem `analyticOnNhd_complexMGF` / 定理 `analyticOnNhd_complexMGF`

English:
theorem analyticOnNhd_complexMGF
  proof: differentiableOn_complexMGF.analyticOnNhd (isOpen_interior.preimage Complex.continuous_re)

中文:
定理 analyticOnNhd_complexMGF
  证明: differentiableOn_complexMGF.analyticOnNhd (isOpen_interior.preimage Complex.continuous_re)

Depends on / 依赖: Complex.continuous_re, analyticOnNhd, continuous_re, differentiableOn_complexMGF, differentiableOn_complexMGF.analyticOnNhd, isOpen_interior, isOpen_interior.preimage, preimage
-/
theorem analyticOnNhd_complexMGF :
    AnalyticOnNhd Complex (complexMGF X μ) {z | z.re in interior (integrableExpSet X μ)} :=
  differentiableOn_complexMGF.analyticOnNhd (isOpen_interior.preimage Complex.continuous_re)

/--
theorem `analyticOn_complexMGF` / 定理 `analyticOn_complexMGF`

English:
theorem analyticOn_complexMGF
  proof: analyticOnNhd_complexMGF.analyticOn

中文:
定理 analyticOn_complexMGF
  证明: analyticOnNhd_complexMGF.analyticOn

Depends on / 依赖: analyticOn, analyticOnNhd_complexMGF, analyticOnNhd_complexMGF.analyticOn
-/
theorem analyticOn_complexMGF :
    AnalyticOn Complex (complexMGF X μ) {z | z.re in interior (integrableExpSet X μ)} :=
  analyticOnNhd_complexMGF.analyticOn

/--
lemma `analyticAt_complexMGF` / 引理 `analyticAt_complexMGF`

English:
lemma analyticAt_complexMGF
  given: (hz : z.re in interior (integrableExpSet X μ))
  proof: analyticOnNhd_complexMGF z hz

中文:
引理 analyticAt_complexMGF
  条件: (hz : z.re in interior (integrableExpSet X μ))
  证明: analyticOnNhd_complexMGF z hz

Depends on / 依赖: analyticOnNhd_complexMGF
-/
lemma analyticAt_complexMGF (hz : z.re in interior (integrableExpSet X μ)) :
    AnalyticAt Complex (complexMGF X μ) z :=
  analyticOnNhd_complexMGF z hz

end Analytic

section Deriv


/--
lemma `hasDerivAt_iteratedDeriv_complexMGF` / 引理 `hasDerivAt_iteratedDeriv_complexMGF`

English:
lemma hasDerivAt_iteratedDeriv_complexMGF
  given: (hz : z.re in interior (integrableExpSet X μ)) (n : Nat)
  proof: by
  induction n generalizing z with
  | zero => simp [hasDerivAt_complexMGF hz]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    have : deriv (iteratedDeriv n (complexMGF X μ))
        =ᶠ[𝓝 z] fun z => μ[fun ω => X ω ^ (n + 1) * cexp (z * X ω)] := by
      have h_mem : forallᶠ y in 𝓝 z, y.re in interior (integrableExpSet X μ) := by
        refine IsOpen.eventually_mem ?_ hz
        exact isOpen_interior.preimage Complex.continuous_re
      filter_upwards [h_mem] with y hy using HasDerivAt.deriv (hn hy)
    rw [EventuallyEq.hasDerivAt_iff this]
    exact hasDerivAt_integral_pow_mul_exp hz (n + 1)

中文:
引理 hasDerivAt_iteratedDeriv_complexMGF
  条件: (hz : z.re in interior (integrableExpSet X μ)) (n : 自然数)
  证明: by
  induction n generalizing z with
  | zero => simp [hasDerivAt_complexMGF hz]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    have : deriv (iteratedDeriv n (complexMGF X μ))
        =ᶠ[𝓝 z] fun z => μ[fun ω => X ω ^ (n + 1) * cexp (z * X ω)] := by
      have h_mem : forallᶠ y in 𝓝 z, y.re in interior (integrableExpSet X μ) := by
        refine IsOpen.eventually_mem ?_ hz
        exact isOpen_interior.preimage Complex.continuous_re
      filter_upwards [h_mem] with y hy using HasDerivAt.deriv (hn hy)
    rw [EventuallyEq.hasDerivAt_iff this]
    exact hasDerivAt_integral_pow_mul_exp hz (n + 1)

Depends on / 依赖: Complex.continuous_re, EventuallyEq, EventuallyEq.hasDerivAt_iff, HasDerivAt, HasDerivAt.deriv, IsOpen, IsOpen.eventually_mem, complexMGF, continuous_re, eventually_mem, filter_upwards, generalizing, h_mem, hasDerivAt_complexMGF, hasDerivAt_iff, integrableExpSet, interior, isOpen_interior, isOpen_interior.preimage, iteratedDeriv
-/
lemma hasDerivAt_iteratedDeriv_complexMGF (hz : z.re in interior (integrableExpSet X μ)) (n : Nat) :
    HasDerivAt (iteratedDeriv n (complexMGF X μ)) μ[fun ω => X ω ^ (n + 1) * cexp (z * X ω)] z := by
  induction n generalizing z with
  | zero => simp [hasDerivAt_complexMGF hz]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    have : deriv (iteratedDeriv n (complexMGF X μ))
        =ᶠ[𝓝 z] fun z => μ[fun ω => X ω ^ (n + 1) * cexp (z * X ω)] := by
      have h_mem : forallᶠ y in 𝓝 z, y.re in interior (integrableExpSet X μ) := by
        refine IsOpen.eventually_mem ?_ hz
        exact isOpen_interior.preimage Complex.continuous_re
      filter_upwards [h_mem] with y hy using HasDerivAt.deriv (hn hy)
    rw [EventuallyEq.hasDerivAt_iff this]
    exact hasDerivAt_integral_pow_mul_exp hz (n + 1)

/--
lemma `iteratedDeriv_complexMGF` / 引理 `iteratedDeriv_complexMGF`

English:
lemma iteratedDeriv_complexMGF
  given: (hz : z.re in interior (integrableExpSet X μ)) (n : Nat)
  proof: by
  induction n generalizing z with
  | zero => simp [complexMGF]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    exact (hasDerivAt_iteratedDeriv_complexMGF hz n).deriv

中文:
引理 iteratedDeriv_complexMGF
  条件: (hz : z.re in interior (integrableExpSet X μ)) (n : 自然数)
  证明: by
  induction n generalizing z with
  | zero => simp [complexMGF]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    exact (hasDerivAt_iteratedDeriv_complexMGF hz n).deriv

Depends on / 依赖: complexMGF, generalizing, hasDerivAt_iteratedDeriv_complexMGF, iteratedDeriv_succ
-/
lemma iteratedDeriv_complexMGF (hz : z.re in interior (integrableExpSet X μ)) (n : Nat) :
    iteratedDeriv n (complexMGF X μ) z = μ[fun ω => X ω ^ n * cexp (z * X ω)] := by
  induction n generalizing z with
  | zero => simp [complexMGF]
  | succ n hn =>
    rw [iteratedDeriv_succ]
    exact (hasDerivAt_iteratedDeriv_complexMGF hz n).deriv

end Deriv

section EqOfMGF

/-! We prove that if two random variables have the same `mgf`, then
they also have the same `complexMGF`. -/

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {Y : Ω' -> Real} {μ' : Measure Ω'}

/--
lemma `integrableExpSet_eq_of_mgf'` / 引理 `integrableExpSet_eq_of_mgf'`

English:
lemma integrableExpSet_eq_of_mgf'
  given: (hXY : mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' = 0)
  proof: by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq]
  by_cases hμ : μ = 0
  · simp [hμ, hμμ'.mp hμ]
  have : NeZero μ := ⟨hμ⟩
  have : NeZero μ' := ⟨(not_iff_not.mpr hμμ').mp hμ⟩
  rw [← mgf_pos_iff]; rw [← mgf_pos_iff]; rw [hXY]

中文:
引理 integrableExpSet_eq_of_mgf'
  条件: (hXY : mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' = 0)
  证明: by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq]
  by_cases hμ : μ = 0
  · simp [hμ, hμμ'.mp hμ]
  have : NeZero μ := ⟨hμ⟩
  have : NeZero μ' := ⟨(not_iff_not.mpr hμμ').mp hμ⟩
  rw [← mgf_pos_iff]; rw [← mgf_pos_iff]; rw [hXY]

Depends on / 依赖: NeZero, Set.mem_ofPred_eq, integrableExpSet, mem_ofPred_eq, mgf_pos_iff, not_iff_not, not_iff_not.mpr
-/
lemma integrableExpSet_eq_of_mgf' (hXY : mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' = 0) :
    integrableExpSet X μ = integrableExpSet Y μ' := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq]
  by_cases hμ : μ = 0
  · simp [hμ, hμμ'.mp hμ]
  have : NeZero μ := ⟨hμ⟩
  have : NeZero μ' := ⟨(not_iff_not.mpr hμμ').mp hμ⟩
  rw [← mgf_pos_iff]; rw [← mgf_pos_iff]; rw [hXY]

/--
lemma `integrableExpSet_eq_of_mgf` / 引理 `integrableExpSet_eq_of_mgf`

English:
lemma integrableExpSet_eq_of_mgf
  statement: [IsProbabilityMeasure μ]
  proof: by
  refine integrableExpSet_eq_of_mgf' hXY ?_
  simp only [IsProbabilityMeasure.ne_zero, false_iff]
  suffices mgf Y μ' 0 != 0 by
    intro h_contra
    simp [h_contra] at this
  rw [← hXY]
  exact (mgf_pos (by simp)).ne'

中文:
引理 integrableExpSet_eq_of_mgf
  结论: [是概率测度 μ]
  证明: by
  refine integrableExpSet_eq_of_mgf' hXY ?_
  simp only [IsProbabilityMeasure.ne_zero, false_iff]
  suffices mgf Y μ' 0 != 0 by
    intro h_contra
    simp [h_contra] at this
  rw [← hXY]
  exact (mgf_pos (by simp)).ne'

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.ne_zero, false_iff, h_contra, integrableExpSet_eq_of_mgf, mgf_pos, ne_zero
-/
lemma integrableExpSet_eq_of_mgf [IsProbabilityMeasure μ]
    (hXY : mgf X μ = mgf Y μ') :
    integrableExpSet X μ = integrableExpSet Y μ' := by
  refine integrableExpSet_eq_of_mgf' hXY ?_
  simp only [IsProbabilityMeasure.ne_zero, false_iff]
  suffices mgf Y μ' 0 != 0 by
    intro h_contra
    simp [h_contra] at this
  rw [← hXY]
  exact (mgf_pos (by simp)).ne'

/--
lemma `eqOn_complexMGF_of_mgf'` / 引理 `eqOn_complexMGF_of_mgf'`

English:
lemma eqOn_complexMGF_of_mgf'
  given: (hXY : mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' = 0)
  proof: by
  by_cases h_empty : interior (integrableExpSet X μ) = ∅
  · simp [h_empty]
  rw [← ne_eq]; rw [← Set.nonempty_iff_ne_empty] at h_empty
  obtain ⟨t, ht⟩ := h_empty
  have hX : AnalyticOnNhd Complex (complexMGF X μ) {z | z.re in interior (integrableExpSet X μ)} :=
    analyticOnNhd_complexMGF
  have hY : AnalyticOnNhd Complex (complexMGF Y μ') {z | z.re in interior (integrableExpSet Y μ')} :=
    analyticOnNhd_complexMGF
  rw [integrableExpSet_eq_of_mgf' hXY hμμ'] at hX ht ⊢
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hX hY
    (convex_integrableExpSet.interior.linear_preimage reLm).isPreconnected
    (z₀ := (t : Complex)) (by simp [ht]) ?_
  have h_real : existsᶠ (x : Real) in 𝓝[!=] t, complexMGF X μ x = complexMGF Y μ' x := by
    refine .of_forall fun y => ?_
    rw [complexMGF_ofReal]; rw [complexMGF_ofReal]; rw [hXY]
  rw [frequently_iff_seq_forall] at h_real ⊢
  obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
  refine ⟨fun n => xs n, ?_, fun n => ?_⟩
  · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    constructor
    · rw [tendsto_ofReal_iff]
      exact hx_tendsto.1
    · simpa using hx_tendsto.2
  · simp [hx_eq]

中文:
引理 eqOn_complexMGF_of_mgf'
  条件: (hXY : mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' = 0)
  证明: by
  by_cases h_empty : interior (integrableExpSet X μ) = ∅
  · simp [h_empty]
  rw [← ne_eq]; rw [← Set.nonempty_iff_ne_empty] at h_empty
  obtain ⟨t, ht⟩ := h_empty
  have hX : AnalyticOnNhd Complex (complexMGF X μ) {z | z.re in interior (integrableExpSet X μ)} :=
    analyticOnNhd_complexMGF
  have hY : AnalyticOnNhd Complex (complexMGF Y μ') {z | z.re in interior (integrableExpSet Y μ')} :=
    analyticOnNhd_complexMGF
  rw [integrableExpSet_eq_of_mgf' hXY hμμ'] at hX ht ⊢
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hX hY
    (convex_integrableExpSet.interior.linear_preimage reLm).isPreconnected
    (z₀ := (t : Complex)) (by simp [ht]) ?_
  have h_real : existsᶠ (x : Real) in 𝓝[!=] t, complexMGF X μ x = complexMGF Y μ' x := by
    refine .of_forall fun y => ?_
    rw [complexMGF_ofReal]; rw [complexMGF_ofReal]; rw [hXY]
  rw [frequently_iff_seq_forall] at h_real ⊢
  obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
  refine ⟨fun n => xs n, ?_, fun n => ?_⟩
  · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    constructor
    · rw [tendsto_ofReal_iff]
      exact hx_tendsto.1
    · simpa using hx_tendsto.2
  · simp [hx_eq]

Depends on / 依赖: AnalyticOnNhd, AnalyticOnNhd.eqOn_of_preconnecte, Set.nonempty_iff_ne_empty, analyticOnNhd_complexMGF, complexMGF, eqOn_of_preconnecte, h_empty, integrableExpSet, integrableExpSet_eq_of_mgf, interior, ne_eq, nonempty_iff_ne_empty, z.re
-/
lemma eqOn_complexMGF_of_mgf' (hXY : mgf X μ = mgf Y μ') (hμμ' : μ = 0 ↔ μ' = 0) :
    Set.EqOn (complexMGF X μ) (complexMGF Y μ') {z | z.re in interior (integrableExpSet X μ)} := by
  by_cases h_empty : interior (integrableExpSet X μ) = ∅
  · simp [h_empty]
  rw [← ne_eq]; rw [← Set.nonempty_iff_ne_empty] at h_empty
  obtain ⟨t, ht⟩ := h_empty
  have hX : AnalyticOnNhd Complex (complexMGF X μ) {z | z.re in interior (integrableExpSet X μ)} :=
    analyticOnNhd_complexMGF
  have hY : AnalyticOnNhd Complex (complexMGF Y μ') {z | z.re in interior (integrableExpSet Y μ')} :=
    analyticOnNhd_complexMGF
  rw [integrableExpSet_eq_of_mgf' hXY hμμ'] at hX ht ⊢
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hX hY
    (convex_integrableExpSet.interior.linear_preimage reLm).isPreconnected
    (z₀ := (t : Complex)) (by simp [ht]) ?_
  have h_real : existsᶠ (x : Real) in 𝓝[!=] t, complexMGF X μ x = complexMGF Y μ' x := by
    refine .of_forall fun y => ?_
    rw [complexMGF_ofReal]; rw [complexMGF_ofReal]; rw [hXY]
  rw [frequently_iff_seq_forall] at h_real ⊢
  obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
  refine ⟨fun n => xs n, ?_, fun n => ?_⟩
  · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    constructor
    · rw [tendsto_ofReal_iff]
      exact hx_tendsto.1
    · simpa using hx_tendsto.2
  · simp [hx_eq]

/--
lemma `eqOn_complexMGF_of_mgf` / 引理 `eqOn_complexMGF_of_mgf`

English:
lemma eqOn_complexMGF_of_mgf
  statement: [IsProbabilityMeasure μ]
  proof: by
  refine eqOn_complexMGF_of_mgf' hXY ?_
  simp only [IsProbabilityMeasure.ne_zero, false_iff]
  suffices mgf Y μ' 0 != 0 by
    intro h_contra
    simp [h_contra] at this
  rw [← hXY]
  exact (mgf_pos (by simp)).ne'

中文:
引理 eqOn_complexMGF_of_mgf
  结论: [是概率测度 μ]
  证明: by
  refine eqOn_complexMGF_of_mgf' hXY ?_
  simp only [IsProbabilityMeasure.ne_zero, false_iff]
  suffices mgf Y μ' 0 != 0 by
    intro h_contra
    simp [h_contra] at this
  rw [← hXY]
  exact (mgf_pos (by simp)).ne'

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.ne_zero, eqOn_complexMGF_of_mgf, false_iff, h_contra, mgf_pos, ne_zero
-/
lemma eqOn_complexMGF_of_mgf [IsProbabilityMeasure μ]
    (hXY : mgf X μ = mgf Y μ') :
    Set.EqOn (complexMGF X μ) (complexMGF Y μ') {z | z.re in interior (integrableExpSet X μ)} := by
  refine eqOn_complexMGF_of_mgf' hXY ?_
  simp only [IsProbabilityMeasure.ne_zero, false_iff]
  suffices mgf Y μ' 0 != 0 by
    intro h_contra
    simp [h_contra] at this
  rw [← hXY]
  exact (mgf_pos (by simp)).ne'

end EqOfMGF

section ext

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {Y : Ω' -> Real} {μ' : Measure Ω'}

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `_root_.MeasureTheory.Measure.ext_of_complexMGF_eq` / 定理 `_root_.MeasureTheory.Measure.ext_of_complexMGF_eq`

English:
theorem _root_.MeasureTheory.Measure.ext_of_complexMGF_eq
  statement: [IsFiniteMeasure μ]
  proof: by
  have inner_ne_zero (x : Real) (h : x != 0) : innerₗ Real x != 0 :=
    DFunLike.ne_iff.mpr ⟨x, inner_self_ne_zero.mpr h⟩
  apply MeasureTheory.ext_of_integral_char_eq continuous_probChar probChar_ne_one inner_ne_zero
    continuous_inner (fun w => ?_)
  rw [funext_iff] at h
  specialize h (Multiplicative.toAdd w * I)
  simp_rw [complexMGF, mul_assoc, mul_comm I, ← mul_assoc] at h
  simp only [BoundedContinuousFunction.char_apply, innerₗ_apply_apply,
    RCLike.inner_apply, conj_trivial, probChar_apply, ofReal_mul]
  rwa [integral_map hX (by fun_prop), integral_map hY (by fun_prop)]

中文:
定理 _root_.测度论.测度.ext_of_complexMGF_eq
  结论: [是有限测度 μ]
  证明: by
  have inner_ne_zero (x : Real) (h : x != 0) : innerₗ Real x != 0 :=
    DFunLike.ne_iff.mpr ⟨x, inner_self_ne_zero.mpr h⟩
  apply MeasureTheory.ext_of_integral_char_eq continuous_probChar probChar_ne_one inner_ne_zero
    continuous_inner (fun w => ?_)
  rw [funext_iff] at h
  specialize h (Multiplicative.toAdd w * I)
  simp_rw [complexMGF, mul_assoc, mul_comm I, ← mul_assoc] at h
  simp only [BoundedContinuousFunction.char_apply, innerₗ_apply_apply,
    RCLike.inner_apply, conj_trivial, probChar_apply, ofReal_mul]
  rwa [integral_map hX (by fun_prop), integral_map hY (by fun_prop)]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.char_apply, DFunLike, DFunLike.ne_iff.mpr, MeasureTheory, MeasureTheory.ext_of_integral_char_eq, Multiplicative, Multiplicative.toAdd, RCLike, RCLike.inner_apply, char_apply, complexMGF, conj_trivial, continuous_inner, continuous_probChar, ext_of_integral_char_eq, funext_iff, inner_apply, inner_ne_zero, inner_self_ne_zero
-/
theorem _root_.MeasureTheory.Measure.ext_of_complexMGF_eq [IsFiniteMeasure μ]
    [IsFiniteMeasure μ'] (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ')
    (h : complexMGF X μ = complexMGF Y μ') :
    μ.map X = μ'.map Y := by
  have inner_ne_zero (x : Real) (h : x != 0) : innerₗ Real x != 0 :=
    DFunLike.ne_iff.mpr ⟨x, inner_self_ne_zero.mpr h⟩
  apply MeasureTheory.ext_of_integral_char_eq continuous_probChar probChar_ne_one inner_ne_zero
    continuous_inner (fun w => ?_)
  rw [funext_iff] at h
  specialize h (Multiplicative.toAdd w * I)
  simp_rw [complexMGF, mul_assoc, mul_comm I, ← mul_assoc] at h
  simp only [BoundedContinuousFunction.char_apply, innerₗ_apply_apply,
    RCLike.inner_apply, conj_trivial, probChar_apply, ofReal_mul]
  rwa [integral_map hX (by fun_prop), integral_map hY (by fun_prop)]

/--
lemma `_root_.MeasureTheory.Measure.ext_of_complexMGF_id_eq` / 引理 `_root_.MeasureTheory.Measure.ext_of_complexMGF_id_eq`

English:
lemma _root_.MeasureTheory.Measure.ext_of_complexMGF_id_eq
  proof: by
  simpa using Measure.ext_of_complexMGF_eq aemeasurable_id aemeasurable_id h

中文:
引理 _root_.测度论.测度.ext_of_complexMGF_id_eq
  证明: by
  simpa using Measure.ext_of_complexMGF_eq aemeasurable_id aemeasurable_id h

Depends on / 依赖: Measure, Measure.ext_of_complexMGF_eq, aemeasurable_id, ext_of_complexMGF_eq
-/
lemma _root_.MeasureTheory.Measure.ext_of_complexMGF_id_eq
    {μ μ' : Measure Real} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (h : complexMGF id μ = complexMGF id μ') :
    μ = μ' := by
  simpa using Measure.ext_of_complexMGF_eq aemeasurable_id aemeasurable_id h

end ext

end ProbabilityTheory
