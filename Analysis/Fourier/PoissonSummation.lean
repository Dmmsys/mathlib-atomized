/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Topology.ContinuousMap.Periodic

/-!
# Poisson's summation formula

We prove Poisson's summation formula `∑ (n : ℤ), f n = ∑ (n : ℤ), 𝓕 f n`, where `𝓕 f` is the
Fourier transform of `f`, under the following hypotheses:
* `f` is a continuous function `ℝ → ℂ`.
* The sum `∑ (n : ℤ), 𝓕 f n` is convergent.
* For all compacts `K ⊂ ℝ`, the sum `∑ (n : ℤ), ‖f(x + n)‖` is uniformly convergent on `K`.
  See `Real.tsum_eq_tsum_fourier` for this formulation.

These hypotheses are potentially a little awkward to apply, so we also provide the less general but
easier-to-use result `Real.tsum_eq_tsum_fourierIntegral_of_rpow_decay`, in which we assume `f` and
`𝓕 f` both decay as `|x| ^ (-b)` for some `b > 1`, and the even more specific result
`SchwartzMap.tsum_eq_tsum_fourierIntegral`, where we assume that `f` is a Schwartz function. -/

public section


noncomputable section

open Function hiding comp_apply

open Set hiding restrict_apply

open Complex

open Real

open TopologicalSpace Filter MeasureTheory Asymptotics

open scoped Real Filter FourierTransform

open ContinuousMap

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Real.fourierCoeff_tsum_comp_add` / 定理 `Real.fourierCoeff_tsum_comp_add`

English:
theorem Real.fourierCoeff_tsum_comp_add
  statement: {f : C(Real, Complex)}
  proof: by
  -- NB: This proof can be shortened somewhat by telescoping together some of the steps in the calc
  -- block, but I think it's more legible this way. We start with preliminaries about the integrand.
  let e : C(Real, Complex) := (fourier (-m)).comp ⟨((↑) : Real -> UnitAddCircle), continuous_quo

中文:
定理 Real.fourierCoeff_tsum_comp_add
  结论: {f : C(实数, Complex)}
  证明: by
  -- NB: This proof can be shortened somewhat by telescoping together some of the steps in the calc
  -- block, but I think it's more legible this way. We start with preliminaries about the integrand.
  let e : C(Real, Complex) := (fourier (-m)).comp ⟨((↑) : Real -> UnitAddCircle), continuous_quo
-/
theorem Real.fourierCoeff_tsum_comp_add {f : C(Real, Complex)}
    (hf : forall K : Compacts Real, Summable fun n : Int => ‖(f.comp (ContinuousMap.addRight n)).restrict K‖)
    (m : Int) : fourierCoeff (Periodic.lift <| f.periodic_tsum_comp_add_zsmul 1) m =
      𝓕 (f : Real -> Complex) m := by
  -- NB: This proof can be shortened somewhat by telescoping together some of the steps in the calc
  -- block, but I think it's more legible this way. We start with preliminaries about the integrand.
  let e : C(Real, Complex) := (fourier (-m)).comp ⟨((↑) : Real -> UnitAddCircle), continuous_quotient_mk'⟩
  have neK : forall (K : Compacts Real) (g : C(Real, Complex)), ‖(e * g).restrict K‖ = ‖g.restrict K‖ := by
    have (x : Real) : ‖e x‖ = 1 := (AddCircle.toCircle (-m • x)).norm_coe
    intro K g
    simp_rw [norm_eq_iSup_norm, restrict_apply, mul_apply, norm_mul, this, one_mul]
  have eadd : forall (n : Int), e.comp (ContinuousMap.addRight n) = e := by
    intro n; ext1 x
    have : Periodic e 1 := Periodic.comp (fun x => AddCircle.coe_add_period 1 x) (fourier (-m))
    simpa only [mul_one] using! this.int_mul n x
  -- Now the main argument. First unwind some definitions.
  calc
    fourierCoeff (Periodic.lift <| f.periodic_tsum_comp_add_zsmul 1) m =
        ∫ x in (0 : Real)..1, e x * (∑' n : Int, f.comp (ContinuousMap.addRight n)) x := by
      simp_rw [fourierCoeff_eq_intervalIntegral _ m 0, div_one, one_smul, zero_add, e, comp_apply,
        coe_mk, Periodic.lift_coe, zsmul_one, smul_eq_mul]
    -- Transform sum in C(ℝ, ℂ) evaluated at x into pointwise sum of values.
    _ = ∫ x in (0 : Real)..1, ∑' n : Int, (e * f.comp (ContinuousMap.addRight n)) x := by
      simp_rw [coe_mul, Pi.mul_apply,
        ← ContinuousMap.tsum_apply (summable_of_locally_summable_norm hf), tsum_mul_left]
    -- Swap sum and integral.
    _ = ∑' n : Int, ∫ x in (0 : Real)..1, (e * f.comp (ContinuousMap.addRight n)) x := by
      refine (intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm ?_).symm
      convert! hf ⟨uIcc 0 1, isCompact_uIcc⟩ using 1
      exact funext fun n => neK _ _
    _ = ∑' n : Int, ∫ x in (0 : Real)..1, (e * f).comp (ContinuousMap.addRight n) x := by
      simp only [mul_comp] at eadd ⊢
      simp_rw [eadd]
    -- Rearrange sum of interval integrals into an integral over `ℝ`.
    _ = ∫ x, e x * f x := by
      suffices Integrable (e * f) from this.hasSum_intervalIntegral_comp_add_int.tsum_eq
      apply integrable_of_summable_norm_Icc
      convert! hf ⟨Icc 0 1, isCompact_Icc⟩ using 1
      simp_rw [mul_comp] at eadd ⊢
      simp_rw [eadd]
      exact funext fun n => neK ⟨Icc 0 1, isCompact_Icc⟩ _
    -- Minor tidying to finish
    _ = 𝓕 (f : Real -> Complex) m := by
      rw [fourier_real_eq_integral_exp_smul]
      congr 1 with x : 1
      rw [smul_eq_mul]; rw [comp_apply]; rw [coe_mk]; rw [coe_mk]; rw [ContinuousMap.toFun_eq_coe]; rw [fourier_coe_apply]
      congr 2
      push_cast
      ring

/--
theorem `Real.tsum_eq_tsum_fourier` / 定理 `Real.tsum_eq_tsum_fourier`

English:
theorem Real.tsum_eq_tsum_fourier
  statement: {f : C(Real, Complex)}
  proof: by
  let F : C(UnitAddCircle, Complex) :=
    ⟨(f.periodic_tsum_comp_add_zsmul 1).lift, continuous_coinduced_dom.mpr (map_continuous _)⟩
  have : Summable (fourierCoeff F) := by
    convert! h_sum
    exact Real.fourierCoeff_tsum_comp_add h_norm _
  convert! (has_pointwise_sum_fourier_series_of_summ

中文:
定理 Real.tsum_eq_tsum_fourier
  结论: {f : C(实数, Complex)}
  证明: by
  let F : C(UnitAddCircle, Complex) :=
    ⟨(f.periodic_tsum_comp_add_zsmul 1).lift, continuous_coinduced_dom.mpr (map_continuous _)⟩
  have : Summable (fourierCoeff F) := by
    convert! h_sum
    exact Real.fourierCoeff_tsum_comp_add h_norm _
  convert! (has_pointwise_sum_fourier_series_of_summ

Depends on / 依赖: Periodic, Periodic.lift_coe, QuotientAddGroup, QuotientAddGroup.mk_zero, Real.fourierCoeff_tsum_comp_add, Summable, UnitAddCircle, coe_addRight, coe_mk, comp_apply, continuous_coinduced_dom, continuous_coinduced_dom.mpr, convert, f.periodic_tsum_comp_add_zsmul, fourierCoeff, fourierCoeff_tsum_comp_add, h_norm, h_sum, hasSum_apply, has_pointwise_sum_fourier_series_of_summable
-/
theorem Real.tsum_eq_tsum_fourier {f : C(Real, Complex)}
    (h_norm :
      forall K : Compacts Real, Summable fun n : Int => ‖(f.comp <| ContinuousMap.addRight n).restrict K‖)
    (h_sum : Summable fun n : Int => 𝓕 (f : Real -> Complex) n) (x : Real) :
    ∑' n : Int, f (x + n) = ∑' n : Int, 𝓕 (f : Real -> Complex) n * fourier n (x : UnitAddCircle) := by
  let F : C(UnitAddCircle, Complex) :=
    ⟨(f.periodic_tsum_comp_add_zsmul 1).lift, continuous_coinduced_dom.mpr (map_continuous _)⟩
  have : Summable (fourierCoeff F) := by
    convert! h_sum
    exact Real.fourierCoeff_tsum_comp_add h_norm _
  convert! (has_pointwise_sum_fourier_series_of_summable this x).tsum_eq.symm using 1
  · simpa only [F, coe_mk, ← QuotientAddGroup.mk_zero, Periodic.lift_coe, zsmul_one, comp_apply,
      coe_addRight, zero_add]
       using (hasSum_apply (summable_of_locally_summable_norm h_norm).hasSum x).tsum_eq
  · simp_rw [← Real.fourierCoeff_tsum_comp_add h_norm, smul_eq_mul, F, coe_mk]

section RpowDecay

variable {E : Type*} [NormedAddCommGroup E]

/--
theorem `isBigO_norm_Icc_restrict_atTop` / 定理 `isBigO_norm_Icc_restrict_atTop`

English:
theorem isBigO_norm_Icc_restrict_atTop
  statement: {f : C(Real, E)} {b : Real} (hb : 0 < b)
  proof: by
  -- First establish an explicit estimate on decay of inverse powers.
  -- This is logically independent of the rest of the proof, but of no mathematical interest in
  -- itself, so it is proved in-line rather than being formulated as a separate lemma.
  have claim : forall x : Real, max 0 (-2 * 

中文:
定理 isBigO_norm_Icc_restrict_atTop
  结论: {f : C(实数, E)} {b : 实数} (hb : 0 < b)
  证明: by
  -- First establish an explicit estimate on decay of inverse powers.
  -- This is logically independent of the rest of the proof, but of no mathematical interest in
  -- itself, so it is proved in-line rather than being formulated as a separate lemma.
  have claim : forall x : Real, max 0 (-2 * 
-/
theorem isBigO_norm_Icc_restrict_atTop {f : C(Real, E)} {b : Real} (hb : 0 < b)
    (hf : f =O[atTop] fun x : Real => |x| ^ (-b)) (R S : Real) :
    (fun x : Real => ‖f.restrict (Icc (x + R) (x + S))‖) =O[atTop] fun x : Real => |x| ^ (-b) := by
  -- First establish an explicit estimate on decay of inverse powers.
  -- This is logically independent of the rest of the proof, but of no mathematical interest in
  -- itself, so it is proved in-line rather than being formulated as a separate lemma.
  have claim : forall x : Real, max 0 (-2 * R) < x -> forall y : Real, x + R <= y ->
      y ^ (-b) <= (1 / 2) ^ (-b) * x ^ (-b) := fun x hx y hy => by
    rw [max_lt_iff] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [← mul_rpow] <;> try positivity
    apply rpow_le_rpow_of_nonpos <;> linarith
  -- Now the main proof.
  obtain ⟨c, hc, hc'⟩ := hf.exists_pos
  simp only [IsBigO, IsBigOWith, eventually_atTop] at hc' ⊢
  obtain ⟨d, hd⟩ := hc'
  refine ⟨c * (1 / 2) ^ (-b), ⟨max (1 + max 0 (-2 * R)) (d - R), fun x hx => ?_⟩⟩
  rw [max_le_iff] at hx
  have hx' : max 0 (-2 * R) < x := by linarith
  rw [max_lt_iff] at hx'
  rw [norm_norm]; rw [ContinuousMap.norm_le _ (by positivity)]
  refine fun y => (hd y.1 (by linarith [hx.1, y.2.1])).trans ?_
  have A : forall x : Real, 0 <= |x| ^ (-b) := fun x => by positivity
  rw [mul_assoc]; rw [mul_le_mul_iff_right₀ hc]; rw [norm_of_nonneg (A _)]; rw [norm_of_nonneg (A _)]
  convert! claim x (by linarith only [hx.1]) y.1 y.2.1
  · apply abs_of_nonneg; linarith [y.2.1]
  · exact abs_of_pos hx'.1

/--
theorem `isBigO_norm_Icc_restrict_atBot` / 定理 `isBigO_norm_Icc_restrict_atBot`

English:
theorem isBigO_norm_Icc_restrict_atBot
  statement: {f : C(Real, E)} {b : Real} (hb : 0 < b)
  proof: by
  have h1 : (f.comp (ContinuousMap.mk _ continuous_neg)) =O[atTop] fun x : Real => |x| ^ (-b) := by
    convert! hf.comp_tendsto tendsto_neg_atTop_atBot using 1
    ext1 x; simp only [Function.comp_apply, abs_neg]
  have h2 := (isBigO_norm_Icc_restrict_atTop hb h1 (-S) (-R)).comp_tendsto tendsto_

中文:
定理 isBigO_norm_Icc_restrict_atBot
  结论: {f : C(实数, E)} {b : 实数} (hb : 0 < b)
  证明: by
  have h1 : (f.comp (ContinuousMap.mk _ continuous_neg)) =O[atTop] fun x : Real => |x| ^ (-b) := by
    convert! hf.comp_tendsto tendsto_neg_atTop_atBot using 1
    ext1 x; simp only [Function.comp_apply, abs_neg]
  have h2 := (isBigO_norm_Icc_restrict_atTop hb h1 (-S) (-R)).comp_tendsto tendsto_

Depends on / 依赖: ContinuousMap, ContinuousMap.mk, Function, Function.comp_apply, Neg.neg, abs_neg, comp_apply, comp_tendsto, continuous_neg, convert, f.comp, hf.comp_tendsto, isBigO_norm_Icc_restrict_atTop, isBigO_of_le, tendsto_neg_atBot_atTop, tendsto_neg_atTop_atBot
-/
theorem isBigO_norm_Icc_restrict_atBot {f : C(Real, E)} {b : Real} (hb : 0 < b)
    (hf : f =O[atBot] fun x : Real => |x| ^ (-b)) (R S : Real) :
    (fun x : Real => ‖f.restrict (Icc (x + R) (x + S))‖) =O[atBot] fun x : Real => |x| ^ (-b) := by
  have h1 : (f.comp (ContinuousMap.mk _ continuous_neg)) =O[atTop] fun x : Real => |x| ^ (-b) := by
    convert! hf.comp_tendsto tendsto_neg_atTop_atBot using 1
    ext1 x; simp only [Function.comp_apply, abs_neg]
  have h2 := (isBigO_norm_Icc_restrict_atTop hb h1 (-S) (-R)).comp_tendsto tendsto_neg_atBot_atTop
  have : (fun x : Real => |x| ^ (-b)) ∘ Neg.neg = fun x : Real => |x| ^ (-b) := by
    ext1 x; simp only [Function.comp_apply, abs_neg]
  rw [this] at h2
  refine (isBigO_of_le _ fun x => ?_).trans h2
  -- equality holds, but less work to prove `≤` alone
  rw [norm_norm]; rw [Function.comp_apply]; rw [norm_norm]; rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  rintro ⟨x, hx⟩
  rw [ContinuousMap.restrict_apply_mk]
  refine (le_of_eq ?_).trans (ContinuousMap.norm_coe_le_norm _ ⟨-x, ?_⟩)
  · rw [ContinuousMap.restrict_apply_mk, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      ContinuousMap.coe_mk, neg_neg]
  · exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

/--
theorem `isBigO_norm_restrict_cocompact` / 定理 `isBigO_norm_restrict_cocompact`

English:
theorem isBigO_norm_restrict_cocompact
  statement: (f : C(Real, E)) {b : Real} (hb : 0 < b)
  proof: by
  obtain ⟨r, hr⟩ := K.isCompact.isBounded.subset_closedBall 0
  rw [closedBall_eq_Icc]; rw [zero_add]; rw [zero_sub] at hr
  have : forall x : Real,
      ‖(f.comp (ContinuousMap.addRight x)).restrict K‖ <= ‖f.restrict (Icc (x - r) (x + r))‖ := by
    intro x
    rw [ContinuousMap.norm_le _ (norm

中文:
定理 isBigO_norm_restrict_cocompact
  结论: (f : C(实数, E)) {b : 实数} (hb : 0 < b)
  证明: by
  obtain ⟨r, hr⟩ := K.isCompact.isBounded.subset_closedBall 0
  rw [closedBall_eq_Icc]; rw [zero_add]; rw [zero_sub] at hr
  have : forall x : Real,
      ‖(f.comp (ContinuousMap.addRight x)).restrict K‖ <= ‖f.restrict (Icc (x - r) (x + r))‖ := by
    intro x
    rw [ContinuousMap.norm_le _ (norm

Depends on / 依赖: ContinuousMap, ContinuousMap.addRight, ContinuousMap.coe_addRight, ContinuousMap.comp_apply, ContinuousMap.norm_coe_le_norm, ContinuousMap.norm_le, ContinuousMap.restrict_apply, K.isCompact.isBounded.subset_closedBall, addRight, closedBall_eq_Icc, coe_addRight, comp_apply, f.comp, f.restrict, isBounded, isCompact, le_of_eq, norm_coe_le_norm, norm_le, norm_nonneg
-/
theorem isBigO_norm_restrict_cocompact (f : C(Real, E)) {b : Real} (hb : 0 < b)
    (hf : f =O[cocompact Real] fun x : Real => |x| ^ (-b)) (K : Compacts Real) :
    (fun x => ‖(f.comp (ContinuousMap.addRight x)).restrict K‖) =O[cocompact Real] (|·| ^ (-b)) := by
  obtain ⟨r, hr⟩ := K.isCompact.isBounded.subset_closedBall 0
  rw [closedBall_eq_Icc]; rw [zero_add]; rw [zero_sub] at hr
  have : forall x : Real,
      ‖(f.comp (ContinuousMap.addRight x)).restrict K‖ <= ‖f.restrict (Icc (x - r) (x + r))‖ := by
    intro x
    rw [ContinuousMap.norm_le _ (norm_nonneg _)]
    rintro ⟨y, hy⟩
    refine (le_of_eq ?_).trans (ContinuousMap.norm_coe_le_norm _ ⟨y + x, ?_⟩)
    · simp_rw [ContinuousMap.restrict_apply, ContinuousMap.comp_apply, ContinuousMap.coe_addRight]
    · exact ⟨by linarith [(hr hy).1], by linarith [(hr hy).2]⟩
  simp_rw [cocompact_eq_atBot_atTop, isBigO_sup] at hf ⊢
  constructor
  · refine (isBigO_of_le atBot ?_).trans (isBigO_norm_Icc_restrict_atBot hb hf.1 (-r) r)
    simp_rw [norm_norm]; exact this
  · refine (isBigO_of_le atTop ?_).trans (isBigO_norm_Icc_restrict_atTop hb hf.2 (-r) r)
    simp_rw [norm_norm]; exact this

/--
theorem `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable` / 定理 `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`

English:
theorem Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
  statement: {f : Real -> Complex} (hc : Continuous f)
  proof: Real.tsum_eq_tsum_fourier (fun K => summable_of_isBigO (Real.summable_abs_int_rpow hb)
    ((isBigO_norm_restrict_cocompact ⟨_, hc⟩ (zero_lt_one.trans hb) hf K).comp_tendsto
    Int.tendsto_coe_cofinite)) hFf x

中文:
定理 Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable
  结论: {f : 实数 -> Complex} (hc : Continuous f)
  证明: Real.tsum_eq_tsum_fourier (fun K => summable_of_isBigO (Real.summable_abs_int_rpow hb)
    ((isBigO_norm_restrict_cocompact ⟨_, hc⟩ (zero_lt_one.trans hb) hf K).comp_tendsto
    Int.tendsto_coe_cofinite)) hFf x

Depends on / 依赖: Int.tendsto_coe_cofinite, Real.summable_abs_int_rpow, Real.tsum_eq_tsum_fourier, comp_tendsto, isBigO_norm_restrict_cocompact, summable_abs_int_rpow, summable_of_isBigO, tendsto_coe_cofinite, tsum_eq_tsum_fourier, zero_lt_one, zero_lt_one.trans
-/
theorem Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable {f : Real -> Complex} (hc : Continuous f)
    {b : Real} (hb : 1 < b) (hf : IsBigO (cocompact Real) f fun x : Real => |x| ^ (-b))
    (hFf : Summable fun n : Int => 𝓕 f n) (x : Real) :
    ∑' n : Int, f (x + n) = ∑' n : Int, 𝓕 f n * fourier n (x : UnitAddCircle) :=
  Real.tsum_eq_tsum_fourier (fun K => summable_of_isBigO (Real.summable_abs_int_rpow hb)
    ((isBigO_norm_restrict_cocompact ⟨_, hc⟩ (zero_lt_one.trans hb) hf K).comp_tendsto
    Int.tendsto_coe_cofinite)) hFf x

/--
theorem `Real.tsum_eq_tsum_fourier_of_rpow_decay` / 定理 `Real.tsum_eq_tsum_fourier_of_rpow_decay`

English:
theorem Real.tsum_eq_tsum_fourier_of_rpow_decay
  statement: {f : Real -> Complex} (hc : Continuous f) {b : Real}
  proof: Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc hb hf (summable_of_isBigO
    (Real.summable_abs_int_rpow hb) (hFf.comp_tendsto Int.tendsto_coe_cofinite)) x

中文:
定理 Real.tsum_eq_tsum_fourier_of_rpow_decay
  结论: {f : 实数 -> Complex} (hc : Continuous f) {b : 实数}
  证明: Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc hb hf (summable_of_isBigO
    (Real.summable_abs_int_rpow hb) (hFf.comp_tendsto Int.tendsto_coe_cofinite)) x

Depends on / 依赖: Int.tendsto_coe_cofinite, Real.summable_abs_int_rpow, Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable, comp_tendsto, hFf.comp_tendsto, summable_abs_int_rpow, summable_of_isBigO, tendsto_coe_cofinite, tsum_eq_tsum_fourier_of_rpow_decay_of_summable
-/
theorem Real.tsum_eq_tsum_fourier_of_rpow_decay {f : Real -> Complex} (hc : Continuous f) {b : Real}
    (hb : 1 < b) (hf : f =O[cocompact Real] (|·| ^ (-b)))
    (hFf : (𝓕 f) =O[cocompact Real] (|·| ^ (-b))) (x : Real) :
    ∑' n : Int, f (x + n) = ∑' n : Int, 𝓕 f n * fourier n (x : UnitAddCircle) :=
  Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc hb hf (summable_of_isBigO
    (Real.summable_abs_int_rpow hb) (hFf.comp_tendsto Int.tendsto_coe_cofinite)) x

end RpowDecay

section Schwartz

open scoped SchwartzMap

/--
theorem `SchwartzMap.tsum_eq_tsum_fourier` / 定理 `SchwartzMap.tsum_eq_tsum_fourier`

English:
theorem SchwartzMap.tsum_eq_tsum_fourier
  given: (f : 𝓢(Real, Complex)) (x : Real)
  proof: by
  -- We know that Schwartz functions are `O(‖x ^ (-b)‖)` for *every* `b`; for this argument we take
  -- `b = 2` and work with that.
  apply Real.tsum_eq_tsum_fourier_of_rpow_decay f.continuous one_lt_two
    (f.isBigO_cocompact_rpow (-2)) ((𝓕 f).isBigO_cocompact_rpow (-2))

中文:
定理 SchwartzMap.tsum_eq_tsum_fourier
  条件: (f : 𝓢(实数, Complex)) (x : 实数)
  证明: by
  -- We know that Schwartz functions are `O(‖x ^ (-b)‖)` for *every* `b`; for this argument we take
  -- `b = 2` and work with that.
  apply Real.tsum_eq_tsum_fourier_of_rpow_decay f.continuous one_lt_two
    (f.isBigO_cocompact_rpow (-2)) ((𝓕 f).isBigO_cocompact_rpow (-2))
-/
theorem SchwartzMap.tsum_eq_tsum_fourier (f : 𝓢(Real, Complex)) (x : Real) :
    ∑' n : Int, f (x + n) = ∑' n : Int, 𝓕 f n * fourier n (x : UnitAddCircle) := by
  -- We know that Schwartz functions are `O(‖x ^ (-b)‖)` for *every* `b`; for this argument we take
  -- `b = 2` and work with that.
  apply Real.tsum_eq_tsum_fourier_of_rpow_decay f.continuous one_lt_two
    (f.isBigO_cocompact_rpow (-2)) ((𝓕 f).isBigO_cocompact_rpow (-2))

end Schwartz
