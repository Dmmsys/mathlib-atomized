/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# Fernique's theorem for Gaussian measures

We show that the product of two identical Gaussian measures is invariant under rotation.
We then deduce Fernique's theorem, which states that for a Gaussian measure `μ`, there exists
`C > 0` such that the function `x ↦ exp (C * ‖x‖ ^ 2)` is integrable with respect to `μ`.
As a consequence, a Gaussian measure has finite moments of all orders.

## Main statements

* `IsGaussian.exists_integrable_exp_sq`: **Fernique's theorem**. For a Gaussian measure on a
  second-countable normed space, there exists `C > 0` such that the function
  `x ↦ exp (C * ‖x‖ ^ 2)` is integrable.
* `IsGaussian.memLp_id`: a Gaussian measure in a second-countable Banach space has finite moments
  of all orders.

## References

* [Martin Hairer, *An introduction to stochastic PDEs*][hairer2009introduction]

-/

public section

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal Real Topology

namespace ProbabilityTheory.IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsGaussian μ]

section Rotation

/--
lemma `charFunDual_eq_of_forall_strongDual_eq_zero` / 引理 `charFunDual_eq_of_forall_strongDual_eq_zero`

English:
lemma charFunDual_eq_of_forall_strongDual_eq_zero
  statement: (hμ : forall L : StrongDual Real E, μ[L] = 0)
  proof: by
  simp [charFunDual_eq L, integral_complex_ofReal, hμ L, neg_div]

中文:
引理 charFunDual_eq_of_forall_strongDual_eq_zero
  结论: (hμ : 对任意 L : StrongDual 实数 E, μ[L] = 0)
  证明: by
  simp [charFunDual_eq L, integral_complex_ofReal, hμ L, neg_div]

Depends on / 依赖: charFunDual_eq, integral_complex_ofReal, neg_div
-/
lemma charFunDual_eq_of_forall_strongDual_eq_zero (hμ : forall L : StrongDual Real E, μ[L] = 0)
    (L : StrongDual Real E) :
    charFunDual μ L = exp (- Var[L; μ] / 2) := by
  simp [charFunDual_eq L, integral_complex_ofReal, hμ L, neg_div]

/--
lemma `map_rotation_eq_self_of_forall_strongDual_eq_zero` / 引理 `map_rotation_eq_self_of_forall_strongDual_eq_zero`

English:
lemma map_rotation_eq_self_of_forall_strongDual_eq_zero
  proof: by
  refine Measure.ext_of_charFunDual ?_
  ext L
  simp_rw [charFunDual_map, charFunDual_prod, charFunDual_eq_of_forall_strongDual_eq_zero hμ,
    ← Complex.exp_add]
  rw [← add_div]; rw [← add_div]; rw [← neg_add]; rw [← neg_add]
  congr 3
  norm_cast
  have h1 : (L.comp (.rotation θ)).comp (.inl 

中文:
引理 map_rotation_eq_self_of_forall_strongDual_eq_zero
  证明: by
  refine Measure.ext_of_charFunDual ?_
  ext L
  simp_rw [charFunDual_map, charFunDual_prod, charFunDual_eq_of_forall_strongDual_eq_zero hμ,
    ← Complex.exp_add]
  rw [← add_div]; rw [← add_div]; rw [← neg_add]; rw [← neg_add]
  congr 3
  norm_cast
  have h1 : (L.comp (.rotation θ)).comp (.inl 

Depends on / 依赖: Complex.exp_add, ContinuousLinearMap, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.rotation_apply, L.comp, Measure, Measure.ext_of_charFunDual, Real.cos, Real.sin, add_div, charFunDual_eq_of_forall_strongDual_eq_zero, charFunDual_map, charFunDual_prod, comp_apply, exp_add, ext_of_charFunDual, inl_apply, neg_add, rotation
-/
lemma map_rotation_eq_self_of_forall_strongDual_eq_zero
    [SecondCountableTopology E] [CompleteSpace E]
    (hμ : forall L : StrongDual Real E, μ[L] = 0) (θ : Real) :
    (μ.prod μ).map (ContinuousLinearMap.rotation θ) = μ.prod μ := by
  refine Measure.ext_of_charFunDual ?_
  ext L
  simp_rw [charFunDual_map, charFunDual_prod, charFunDual_eq_of_forall_strongDual_eq_zero hμ,
    ← Complex.exp_add]
  rw [← add_div]; rw [← add_div]; rw [← neg_add]; rw [← neg_add]
  congr 3
  norm_cast
  have h1 : (L.comp (.rotation θ)).comp (.inl Real E E)
      = Real.cos θ • L.comp (.inl Real E E) - Real.sin θ • L.comp (.inr Real E E) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.rotation_apply, smul_zero, add_zero]
    rw [← L.comp_inl_add_comp_inr]
    simp [-neg_smul, sub_eq_add_neg]
  have h2 : (L.comp (.rotation θ)).comp (.inr Real E E)
      = Real.sin θ • L.comp (.inl Real E E) + Real.cos θ • L.comp (.inr Real E E) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.rotation_apply, smul_zero, zero_add, add_apply, smul_apply,
      ContinuousLinearMap.inl_apply, smul_eq_mul]
    rw [← L.comp_inl_add_comp_inr]
    simp
  rw [h1]; rw [h2]
  simp only [FunLike.coe_sub, FunLike.coe_smul,
    FunLike.coe_add]
  rw [variance_sub]; rw [variance_smul]; rw [variance_add]; rw [variance_smul]; rw [variance_smul]; rw [covariance_smul_left]; rw [covariance_smul_right]; rw [variance_smul]; rw [covariance_smul_left]; rw [covariance_smul_right]
  · have h := Real.cos_sq_add_sin_sq θ
    grind
  all_goals exact (memLp_dual _ _ _ (by simp)).const_smul _

end Rotation

section Fernique

variable [SecondCountableTopology E]

/--
lemma `integral_dual_conv_map_neg_eq_zero` / 引理 `integral_dual_conv_map_neg_eq_zero`

English:
lemma integral_dual_conv_map_neg_eq_zero
  given: (L : StrongDual Real E)
  proof: by
  rw [integral_conv (by fun_prop)]
  simp only [map_add]
  calc ∫ x, ∫ y, L x + L y ∂μ.map (ContinuousLinearEquiv.neg Real) ∂μ
  _ = ∫ x, L x + ∫ y, L y ∂μ.map (ContinuousLinearEquiv.neg Real) ∂μ := by
    congr with x
    rw [integral_add (by fun_prop) (by fun_prop)]
    simp [-ContinuousLinearE

中文:
引理 integral_dual_conv_map_neg_eq_zero
  条件: (L : StrongDual 实数 E)
  证明: by
  rw [integral_conv (by fun_prop)]
  simp only [map_add]
  calc ∫ x, ∫ y, L x + L y ∂μ.map (ContinuousLinearEquiv.neg Real) ∂μ
  _ = ∫ x, L x + ∫ y, L y ∂μ.map (ContinuousLinearEquiv.neg Real) ∂μ := by
    congr with x
    rw [integral_add (by fun_prop) (by fun_prop)]
    simp [-ContinuousLinearE

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.coe_neg, ContinuousLinearEquiv.neg, coe_neg, fun_pr, fun_prop, integral_add, integral_const, integral_conv, integral_map, map_add, smul_eq_mul
-/
lemma integral_dual_conv_map_neg_eq_zero (L : StrongDual Real E) :
    (μ ∗ (μ.map (ContinuousLinearEquiv.neg Real)))[L] = 0 := by
  rw [integral_conv (by fun_prop)]
  simp only [map_add]
  calc ∫ x, ∫ y, L x + L y ∂μ.map (ContinuousLinearEquiv.neg Real) ∂μ
  _ = ∫ x, L x + ∫ y, L y ∂μ.map (ContinuousLinearEquiv.neg Real) ∂μ := by
    congr with x
    rw [integral_add (by fun_prop) (by fun_prop)]
    simp [-ContinuousLinearEquiv.coe_neg, integral_const, smul_eq_mul]
  _ = ∫ x, L x ∂μ + ∫ y, L y ∂μ.map (ContinuousLinearEquiv.neg Real) := by
    rw [integral_add (by fun_prop) (by fun_prop)]
    simp
  _ = 0 := by
    rw [integral_map (by fun_prop) (by fun_prop)]
    simp [integral_neg]

/--
lemma `integrable_exp_sq_of_conv_neg` / 引理 `integrable_exp_sq_of_conv_neg`

English:
lemma integrable_exp_sq_of_conv_neg
  statement: (μ : Measure E) [IsGaussian μ] {C C' : Real}
  proof: by
  have h_int : forallᵐ y ∂μ, Integrable (fun x => rexp (C * ‖x - y‖ ^ 2)) μ := by
    rw [integrable_conv_iff (by fun_prop)] at hint
    replace hC := hint.1
    simp only [ContinuousLinearEquiv.coe_neg] at hC
    filter_upwards [hC] with y hy
    rw [integrable_map_measure (by fun_prop) (by fun_

中文:
引理 integrable_exp_sq_of_conv_neg
  结论: (μ : Measure E) [IsGaussian μ] {C C' : 实数}
  证明: by
  have h_int : forallᵐ y ∂μ, Integrable (fun x => rexp (C * ‖x - y‖ ^ 2)) μ := by
    rw [integrable_conv_iff (by fun_prop)] at hint
    replace hC := hint.1
    simp only [ContinuousLinearEquiv.coe_neg] at hC
    filter_upwards [hC] with y hy
    rw [integrable_map_measure (by fun_prop) (by fun_

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.coe_neg, Function, Function.comp_apply, Integrable, OfNat.ofNat_ne_zero, Pi.neg_apply, Real.exp_eq_exp, coe_neg, comp_apply, convert, exp_eq_exp, filter_upwards, fun_prop, h_int, id_eq, integrable_conv_iff, integrable_map_measure, mul_eq_mul_left_iff, ne_eq
-/
lemma integrable_exp_sq_of_conv_neg (μ : Measure E) [IsGaussian μ] {C C' : Real}
    (hint : Integrable (fun x => rexp (C * ‖x‖ ^ 2))
      (μ ∗ (μ.map (ContinuousLinearEquiv.neg Real))))
    (hC'_pos : 0 < C') (hC'_lt : C' < C) :
    Integrable (fun x => rexp (C' * ‖x‖ ^ 2)) μ := by
  have h_int : forallᵐ y ∂μ, Integrable (fun x => rexp (C * ‖x - y‖ ^ 2)) μ := by
    rw [integrable_conv_iff (by fun_prop)] at hint
    replace hC := hint.1
    simp only [ContinuousLinearEquiv.coe_neg] at hC
    filter_upwards [hC] with y hy
    rw [integrable_map_measure (by fun_prop) (by fun_prop)] at hy
    convert! hy with x
    simp only [Function.comp_apply, Pi.neg_apply, id_eq, Real.exp_eq_exp, mul_eq_mul_left_iff,
      norm_nonneg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_left_inj₀]
    left
    simp_rw [← sub_eq_add_neg, norm_sub_rev]
  obtain ⟨y, hy⟩ : exists y, Integrable (fun x => rexp (C * ‖x - y‖ ^ 2)) μ := h_int.exists
  let ε := (C - C') / C'
  have hε : 0 < ε := div_pos (by rwa [sub_pos]) (by positivity)
  suffices forall x, rexp (C' * ‖x‖ ^ 2) <= rexp (C / ε * ‖y‖ ^ 2) * rexp (C * ‖x - y‖ ^ 2) by
    refine integrable_of_le_of_le (g₁ := 0)
      (g₂ := fun x => rexp (C / ε * ‖y‖ ^ 2) * rexp (C * ‖x - y‖ ^ 2)) (by fun_prop) ?_ ?_
      (integrable_const _) (hy.const_mul _)
    · exact ae_of_all _ fun _ => by positivity
    · exact ae_of_all _ this
  intro x
  rw [← Real.exp_add]
  gcongr -- `⊢ C' * ‖x‖ ^ 2 ≤ C / ε * ‖y‖ ^ 2 + C * ‖x - y‖ ^ 2` with `ε = (C - C') / C'`
  have h_le : ‖x‖ ^ 2 <= (1 + ε) * ‖x - y‖ ^ 2 + (1 + 1 / ε) * ‖y‖ ^ 2 := by
    calc ‖x‖ ^ 2
    _ = ‖x - y + y‖ ^ 2 := by simp
    _ <= (‖x - y‖ + ‖y‖) ^ 2 := by grw [norm_add_le (x - y) y]
    _ = ‖x - y‖ ^ 2 + ‖y‖ ^ 2 + 2 * ‖x - y‖ * ‖y‖ := by ring
    _ <= ‖x - y‖ ^ 2 + ‖y‖ ^ 2 + ε * ‖x - y‖ ^ 2 + ε⁻¹ * ‖y‖ ^ 2 := by
      simp_rw [add_assoc]
      gcongr
      exact two_mul_le_add_mul_sq (by positivity)
    _ = (1 + ε) * ‖x - y‖ ^ 2 + (1 + 1 / ε) * ‖y‖ ^ 2 := by ring
  calc C' * ‖x‖ ^ 2
  _ <= C' * ((1 + ε) * ‖x - y‖ ^ 2 + (1 + 1 / ε) * ‖y‖ ^ 2) := by gcongr
  _ = C / ε * ‖y‖ ^ 2 + C * ‖x - y‖ ^ 2 := by grind

/--
theorem `exists_integrable_exp_sq` / 定理 `exists_integrable_exp_sq`

English:
theorem exists_integrable_exp_sq
  given: [CompleteSpace E] (μ : Measure E) [IsGaussian μ]
  proof: by
  -- Since `μ ∗ μ.map (ContinuousLinearEquiv.neg ℝ)` is a centered Gaussian measure, it is invariant
  -- under rotation. We can thus apply a version of Fernique's theorem to it.
  obtain ⟨C, hC_pos, hC⟩ : exists C, 0 < C
      ∧ Integrable (fun x => rexp (C * ‖x‖ ^ 2)) (μ ∗ μ.map (ContinuousLine

中文:
定理 exists_integrable_exp_sq
  条件: [CompleteSpace E] (μ : Measure E) [IsGaussian μ]
  证明: by
  -- Since `μ ∗ μ.map (ContinuousLinearEquiv.neg ℝ)` is a centered Gaussian measure, it is invariant
  -- under rotation. We can thus apply a version of Fernique's theorem to it.
  obtain ⟨C, hC_pos, hC⟩ : exists C, 0 < C
      ∧ Integrable (fun x => rexp (C * ‖x‖ ^ 2)) (μ ∗ μ.map (ContinuousLine
-/
theorem exists_integrable_exp_sq [CompleteSpace E] (μ : Measure E) [IsGaussian μ] :
    exists C, 0 < C ∧ Integrable (fun x => rexp (C * ‖x‖ ^ 2)) μ := by
  -- Since `μ ∗ μ.map (ContinuousLinearEquiv.neg ℝ)` is a centered Gaussian measure, it is invariant
  -- under rotation. We can thus apply a version of Fernique's theorem to it.
  obtain ⟨C, hC_pos, hC⟩ : exists C, 0 < C
      ∧ Integrable (fun x => rexp (C * ‖x‖ ^ 2)) (μ ∗ μ.map (ContinuousLinearEquiv.neg Real)) :=
    exists_integrable_exp_sq_of_map_rotation_eq_self
      (map_rotation_eq_self_of_forall_strongDual_eq_zero
        (integral_dual_conv_map_neg_eq_zero (μ := μ)) _)
  -- We must now prove that the integrability with respect to
  -- `μ ∗ μ.map (ContinuousLinearEquiv.neg ℝ)` implies integrability with respect to `μ` for
  -- another constant `C' < C`.
  refine ⟨C / 2, by positivity, ?_⟩
  exact integrable_exp_sq_of_conv_neg μ hC (by positivity) (by simp [hC_pos])

end Fernique

section FiniteMoments

variable [CompleteSpace E] [SecondCountableTopology E]

/--
lemma `memLp_id` / 引理 `memLp_id`

English:
lemma memLp_id
  given: (μ : Measure E) [IsGaussian μ] (p : Real>=0∞) (hp : p != ∞)
  statement: MemLp id p μ
  proof: by
  suffices MemLp (fun x => ‖x‖ ^ 2) (p / 2) μ by
    rw [← memLp_norm_rpow_iff (q := 2) (by fun_prop) (by simp) (by simp)]
    simpa using this
  lift p to Real>=0 using hp
  convert! memLp_of_mem_interior_integrableExpSet ?_ (p / 2)
  · simp
  obtain ⟨C, hC_pos, hC⟩ := exists_integrable_exp_sq μ

中文:
引理 memLp_id
  条件: (μ : Measure E) [IsGaussian μ] (p : 实数>=0∞) (hp : p != ∞)
  结论: MemLp id p μ
  证明: by
  suffices MemLp (fun x => ‖x‖ ^ 2) (p / 2) μ by
    rw [← memLp_norm_rpow_iff (q := 2) (by fun_prop) (by simp) (by simp)]
    simpa using this
  lift p to Real>=0 using hp
  convert! memLp_of_mem_interior_integrableExpSet ?_ (p / 2)
  · simp
  obtain ⟨C, hC_pos, hC⟩ := exists_integrable_exp_sq μ

Depends on / 依赖: Integrable, ae_of_all, convert, exists_integrable_exp_sq, fun_prop, hC_neg, hC_pos, integrable_const, integrable_of_le_of_le, memLp_norm_rpow_iff, memLp_of_mem_interior_integrableExpSet, negative
-/
lemma memLp_id (μ : Measure E) [IsGaussian μ] (p : Real>=0∞) (hp : p != ∞) : MemLp id p μ := by
  suffices MemLp (fun x => ‖x‖ ^ 2) (p / 2) μ by
    rw [← memLp_norm_rpow_iff (q := 2) (by fun_prop) (by simp) (by simp)]
    simpa using this
  lift p to Real>=0 using hp
  convert! memLp_of_mem_interior_integrableExpSet ?_ (p / 2)
  · simp
  obtain ⟨C, hC_pos, hC⟩ := exists_integrable_exp_sq μ
  have hC_neg : Integrable (fun x => rexp (-C * ‖x‖ ^ 2)) μ := by -- `-C` could be any negative
    refine integrable_of_le_of_le (g₁ := 0) (g₂ := 1) (by fun_prop)
      (ae_of_all _ fun _ => by positivity) ?_ (integrable_const _) (integrable_const _)
    filter_upwards with x
    simp only [neg_mul, Pi.one_apply, Real.exp_le_one_iff, Left.neg_nonpos_iff]
    positivity
  have h_subset : Set.Ioo (-C) C subseteq interior (integrableExpSet (fun x => ‖x‖ ^ 2) μ) := by
    rw [IsOpen.subset_interior_iff isOpen_Ioo]
    exact fun x hx => integrable_exp_mul_of_le_of_le hC_neg hC hx.1.le hx.2.le
  exact h_subset ⟨by simp [hC_pos], hC_pos⟩

@[to_fun integrable_fun_id]
/--
lemma `integrable_id` / 引理 `integrable_id`

English:
lemma integrable_id
  statement: Integrable id μ
  proof: memLp_one_iff_integrable.1 memLp_id μ 1 (by norm_num)

@[to_fun memLp_two_fun_id]

中文:
引理 integrable_id
  结论: 整数egrable id μ
  证明: memLp_one_iff_integrable.1 memLp_id μ 1 (by norm_num)

@[to_fun memLp_two_fun_id]

Depends on / 依赖: memLp_id, memLp_one_iff_integrable
-/
lemma integrable_id : Integrable id μ :=
memLp_one_iff_integrable.1 memLp_id μ 1 (by norm_num)

@[to_fun memLp_two_fun_id]
/--
lemma `memLp_two_id` / 引理 `memLp_two_id`

English:
lemma memLp_two_id
  statement: MemLp id 2 μ
  proof: memLp_id μ 2 (by norm_num)

中文:
引理 memLp_two_id
  结论: MemLp id 2 μ
  证明: memLp_id μ 2 (by norm_num)

Depends on / 依赖: memLp_id
-/
lemma memLp_two_id : MemLp id 2 μ := memLp_id μ 2 (by norm_num)

/--
lemma `integral_dual` / 引理 `integral_dual`

English:
lemma integral_dual
  given: (L : StrongDual Real E)
  statement: μ[L] = L (∫ x, x ∂μ)
  proof: L.integral_comp_comm ((memLp_id μ 1 (by simp)).integrable le_rfl)

中文:
引理 integral_dual
  条件: (L : StrongDual 实数 E)
  结论: μ[L] = L (∫ x, x ∂μ)
  证明: L.integral_comp_comm ((memLp_id μ 1 (by simp)).integrable le_rfl)

Depends on / 依赖: L.integral_comp_comm, integrable, integral_comp_comm, le_rfl, memLp_id
-/
lemma integral_dual (L : StrongDual Real E) : μ[L] = L (∫ x, x ∂μ) :=
  L.integral_comp_comm ((memLp_id μ 1 (by simp)).integrable le_rfl)

/--
lemma `eq_dirac_of_variance_eq_zero` / 引理 `eq_dirac_of_variance_eq_zero`

English:
lemma eq_dirac_of_variance_eq_zero
  given: (h : forall L : StrongDual Real E, Var[L; μ] = 0)
  proof: by
  refine Measure.ext_of_charFunDual ?_
  ext L
  rw [charFunDual_dirac]; rw [charFunDual_eq L]; rw [h L]; rw [integral_complex_ofReal]; rw [integral_dual L]
  simp

中文:
引理 eq_dirac_of_variance_eq_zero
  条件: (h : 对任意 L : StrongDual 实数 E, Var[L; μ] = 0)
  证明: by
  refine Measure.ext_of_charFunDual ?_
  ext L
  rw [charFunDual_dirac]; rw [charFunDual_eq L]; rw [h L]; rw [integral_complex_ofReal]; rw [integral_dual L]
  simp

Depends on / 依赖: Measure, Measure.ext_of_charFunDual, charFunDual_dirac, charFunDual_eq, ext_of_charFunDual, integral_complex_ofReal, integral_dual
-/
lemma eq_dirac_of_variance_eq_zero (h : forall L : StrongDual Real E, Var[L; μ] = 0) :
    μ = Measure.dirac (∫ x, x ∂μ) := by
  refine Measure.ext_of_charFunDual ?_
  ext L
  rw [charFunDual_dirac]; rw [charFunDual_eq L]; rw [h L]; rw [integral_complex_ofReal]; rw [integral_dual L]
  simp

/--
lemma `nullSingletonClass` / 引理 `nullSingletonClass`

English:
lemma nullSingletonClass
  given: (h : forall x, μ != Measure.dirac x)
  statement: NullSingletonClass μ where
  proof: by
    obtain ⟨L, hL⟩ : exists L : StrongDual Real E, Var[L; μ] != 0 := by
      contrapose! h
      exact ⟨_, eq_dirac_of_variance_eq_zero h⟩
    have hL_zero : μ.map L {L x} = 0 := by
      have : NullSingletonClass (μ.map L) := by
        rw [map_eq_gaussianReal L]
        refine nullSingletonCla

中文:
引理 nullSingletonClass
  条件: (h : 对任意 x, μ != Measure.dirac x)
  结论: NullSingletonClass μ where
  证明: by
    obtain ⟨L, hL⟩ : exists L : StrongDual Real E, Var[L; μ] != 0 := by
      contrapose! h
      exact ⟨_, eq_dirac_of_variance_eq_zero h⟩
    have hL_zero : μ.map L {L x} = 0 := by
      have : NullSingletonClass (μ.map L) := by
        rw [map_eq_gaussianReal L]
        refine nullSingletonCla

Depends on / 依赖: Measure, Measure.map_apply, NullSingletonClass, Real.toNNReal_eq_zero, StrongDual, contrapose, eq_dirac_of_variance_eq_zero, fun_prop, hL.symm, hL_zero, lt_of_le_of_ne, map_apply, map_eq_gaussianReal, measurableSet_singleton, measure_mono_null, measure_singleton, ne_eq, not_le, nullSingletonClass_gaussianReal, toNNReal_eq_zero
-/
lemma nullSingletonClass (h : forall x, μ != Measure.dirac x) : NullSingletonClass μ where
  measure_singleton x := by
    obtain ⟨L, hL⟩ : exists L : StrongDual Real E, Var[L; μ] != 0 := by
      contrapose! h
      exact ⟨_, eq_dirac_of_variance_eq_zero h⟩
    have hL_zero : μ.map L {L x} = 0 := by
      have : NullSingletonClass (μ.map L) := by
        rw [map_eq_gaussianReal L]
        refine nullSingletonClass_gaussianReal ?_
        simp only [ne_eq, Real.toNNReal_eq_zero, not_le]
        exact lt_of_le_of_ne (variance_nonneg _ _) hL.symm
      rw [measure_singleton]
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at hL_zero
    refine measure_mono_null ?_ hL_zero
    exact fun ⦃a⦄ => congrArg ⇑L

@[deprecated (since := "2026-06-09")]
alias noAtoms := nullSingletonClass

/--
lemma `charFunDual_eq_of_integral_eq_zero` / 引理 `charFunDual_eq_of_integral_eq_zero`

English:
lemma charFunDual_eq_of_integral_eq_zero
  given: (hμ : μ[id] = 0) (L : StrongDual Real E)
  proof: by
  refine charFunDual_eq_of_forall_strongDual_eq_zero (fun L => ?_) L
  simp only [id_eq] at hμ
  simp [integral_dual, hμ]

中文:
引理 charFunDual_eq_of_integral_eq_zero
  条件: (hμ : μ[id] = 0) (L : StrongDual 实数 E)
  证明: by
  refine charFunDual_eq_of_forall_strongDual_eq_zero (fun L => ?_) L
  simp only [id_eq] at hμ
  simp [integral_dual, hμ]

Depends on / 依赖: charFunDual_eq_of_forall_strongDual_eq_zero, id_eq, integral_dual
-/
lemma charFunDual_eq_of_integral_eq_zero (hμ : μ[id] = 0) (L : StrongDual Real E) :
    charFunDual μ L = exp (- Var[L; μ] / 2) := by
  refine charFunDual_eq_of_forall_strongDual_eq_zero (fun L => ?_) L
  simp only [id_eq] at hμ
  simp [integral_dual, hμ]

/--
lemma `map_rotation_eq_self` / 引理 `map_rotation_eq_self`

English:
lemma map_rotation_eq_self
  given: (hμ : μ[id] = 0) (θ : Real)
  proof: by
  refine map_rotation_eq_self_of_forall_strongDual_eq_zero (fun L => ?_) θ
  simp only [id_eq] at hμ
  simp [integral_dual, hμ]

中文:
引理 map_rotation_eq_self
  条件: (hμ : μ[id] = 0) (θ : 实数)
  证明: by
  refine map_rotation_eq_self_of_forall_strongDual_eq_zero (fun L => ?_) θ
  simp only [id_eq] at hμ
  simp [integral_dual, hμ]

Depends on / 依赖: id_eq, integral_dual, map_rotation_eq_self_of_forall_strongDual_eq_zero
-/
lemma map_rotation_eq_self (hμ : μ[id] = 0) (θ : Real) :
    (μ.prod μ).map (ContinuousLinearMap.rotation θ) = μ.prod μ := by
  refine map_rotation_eq_self_of_forall_strongDual_eq_zero (fun L => ?_) θ
  simp only [id_eq] at hμ
  simp [integral_dual, hμ]

end FiniteMoments

end ProbabilityTheory.IsGaussian
