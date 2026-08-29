/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder

/-!
# Integral representations of `rpow`

This file contains an integral representation of the `rpow` function between 0 and 1: we show
that there exists a measure on ℝ such that `x ^ p = ∫ t, rpowIntegrand₀₁ p t x ∂μ` for
the integrand `rpowIntegrand₀₁ p t x := t ^ p * (t⁻¹ - (t + x)⁻¹)`.

This representation is useful for showing that `rpow` is operator monotone and operator concave
in this range; that is, `cfc rpow` is monotone/concave. The integrand can be shown to be
operator monotone and concave through direct means, and this integral lifts these properties
to `rpow`. These results can be found in
`Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order`.

## Notes

Here we only compute the integral up to a constant, even though the actual constant can be
computed via contour integration. We chose to avoid this, as the constant is seldom if ever
relevant in applications, and would needlessly complicate the proof.

## Main declarations

+ `rpowIntegrand₀₁ p t x := t ^ p * (t⁻¹ - (t + x)⁻¹)`
+ `rpowIntegrand₁₂ p t x := t ^ (p - 1) * (x * t⁻¹ + t * (t + x)⁻¹ - 1)`
+ `exists_measure_rpow_eq_integral_rpowIntegrand₀₁` and
  `exists_measure_rpow_eq_integral_rpowIntegrand₁₂`: there exists a measure on `ℝ` such that
  `x ^ p = ∫ t, rpowIntegrand₀₁ p t x ∂μ` (resp `x ^ p = ∫ t, rpowIntegrand₁₂ p t x ∂μ`)
+ `CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁` and
  `CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂`: the corresponding statements where
  `x ^ p` is defined via the CFC.

## TODO

+ Give analogous representations for the range `Ioo (-1) 0`.

## References

+ [carlen2010] Eric A. Carlen, "Trace inequalities and quantum entropies: An introductory course"
  (see Lemma 2.8)
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace Real

/--
Definition of `rpowIntegrand₀₁` / `rpowIntegrand₀₁` 的定义

English:
definition rpowIntegrand₀₁
  signature: (p t x : Real)
  body: t ^ p * (t⁻¹ - (t + x)⁻¹)

中文:
定义 rpow整数egrand₀₁
  签名: (p t x : 实数)
  定义体: t ^ p * (t⁻¹ - (t + x)⁻¹)
-/
noncomputable def rpowIntegrand₀₁ (p t x : Real) : Real := t ^ p * (t⁻¹ - (t + x)⁻¹)

/--
Definition of `rpowIntegrand₁₂` / `rpowIntegrand₁₂` 的定义

English:
definition rpowIntegrand₁₂
  signature: (p t x : Real)
  body: t ^ (p - 1) * (t⁻¹ * x + t * (t + x)⁻¹ - 1)

中文:
定义 rpow整数egrand₁₂
  签名: (p t x : 实数)
  定义体: t ^ (p - 1) * (t⁻¹ * x + t * (t + x)⁻¹ - 1)
-/
noncomputable def rpowIntegrand₁₂ (p t x : Real) : Real := t ^ (p - 1) * (t⁻¹ * x + t * (t + x)⁻¹ - 1)

section ZeroOne
/-
## `p ∈ (0,1)`
-/

variable {p t x : Real}

@[simp]
/--
lemma `rpowIntegrand₀₁_zero_right` / 引理 `rpowIntegrand₀₁_zero_right`

English:
lemma rpowIntegrand₀₁_zero_right
  statement: rpowIntegrand₀₁ p t 0 = 0
  proof: by simp [rpowIntegrand₀₁]

中文:
引理 rpow整数egrand₀₁_zero_right
  结论: rpow整数egrand₀₁ p t 0 = 0
  证明: by simp [rpowIntegrand₀₁]
-/
lemma rpowIntegrand₀₁_zero_right : rpowIntegrand₀₁ p t 0 = 0 := by simp [rpowIntegrand₀₁]

/--
lemma `rpowIntegrand₀₁_zero_left` / 引理 `rpowIntegrand₀₁_zero_left`

English:
lemma rpowIntegrand₀₁_zero_left
  given: (hp : 0 < p)
  statement: rpowIntegrand₀₁ p 0 x = 0
  proof: by
  simp [rpowIntegrand₀₁, Real.zero_rpow hp.ne']

中文:
引理 rpow整数egrand₀₁_zero_left
  条件: (hp : 0 < p)
  结论: rpow整数egrand₀₁ p 0 x = 0
  证明: by
  simp [rpowIntegrand₀₁, Real.zero_rpow hp.ne']

Depends on / 依赖: Real.zero_rpow, hp.ne, zero_rpow
-/
lemma rpowIntegrand₀₁_zero_left (hp : 0 < p) : rpowIntegrand₀₁ p 0 x = 0 := by
  simp [rpowIntegrand₀₁, Real.zero_rpow hp.ne']

/--
lemma `rpowIntegrand₀₁_eq_sub` / 引理 `rpowIntegrand₀₁_eq_sub`

English:
lemma rpowIntegrand₀₁_eq_sub
  given: {p t : Real} (hp : p != 1) (ht : 0 < t)
  proof: by
  unfold rpowIntegrand₀₁
  ext x
  rw [mul_sub]; rw [← rpow_neg_one]; rw [← rpow_add' (by grind) (by grind)]
  grind only

中文:
引理 rpow整数egrand₀₁_eq_sub
  条件: {p t : 实数} (hp : p != 1) (ht : 0 < t)
  证明: by
  unfold rpowIntegrand₀₁
  ext x
  rw [mul_sub]; rw [← rpow_neg_one]; rw [← rpow_add' (by grind) (by grind)]
  grind only

Depends on / 依赖: ShortComplex, ShortComplex.Splitting.ofHasBinaryBiproduct, Splitting, mul_sub, ofHasBinaryBiproduct, rpow_add, rpow_neg_one, shortExact, shortExact.hasProjectiveDimensionLT_X
-/
lemma rpowIntegrand₀₁_eq_sub {p t : Real} (hp : p != 1) (ht : 0 < t) :
    rpowIntegrand₀₁ p t = fun x => t ^ (p - 1) - t ^ p * (t + x)⁻¹ := by
  unfold rpowIntegrand₀₁
  ext x
  rw [mul_sub]; rw [← rpow_neg_one]; rw [← rpow_add' (by grind) (by grind)]
  grind only

/--
lemma `rpowIntegrand₀₁_nonneg` / 引理 `rpowIntegrand₀₁_nonneg`

English:
lemma rpowIntegrand₀₁_nonneg
  given: (hp : 0 < p) (ht : 0 <= t) (hx : 0 <= x)
  proof: by
  unfold rpowIntegrand₀₁
  cases eq_or_lt_of_le' ht with
  | inl ht_zero => simp [ht_zero, Real.zero_rpow (ne_of_gt hp)]
  | inr ht_pos =>
    refine mul_nonneg (by positivity) ?_
    rw [sub_nonneg]
    gcongr
    linarith

中文:
引理 rpow整数egrand₀₁_nonneg
  条件: (hp : 0 < p) (ht : 0 <= t) (hx : 0 <= x)
  证明: by
  unfold rpowIntegrand₀₁
  cases eq_or_lt_of_le' ht with
  | inl ht_zero => simp [ht_zero, Real.zero_rpow (ne_of_gt hp)]
  | inr ht_pos =>
    refine mul_nonneg (by positivity) ?_
    rw [sub_nonneg]
    gcongr
    linarith

Depends on / 依赖: Real.zero_rpow, eq_or_lt_of_le, ht_pos, ht_zero, mul_nonneg, ne_of_gt, sub_nonneg, zero_rpow
-/
lemma rpowIntegrand₀₁_nonneg (hp : 0 < p) (ht : 0 <= t) (hx : 0 <= x) :
    0 <= rpowIntegrand₀₁ p t x := by
  unfold rpowIntegrand₀₁
  cases eq_or_lt_of_le' ht with
  | inl ht_zero => simp [ht_zero, Real.zero_rpow (ne_of_gt hp)]
  | inr ht_pos =>
    refine mul_nonneg (by positivity) ?_
    rw [sub_nonneg]
    gcongr
    linarith

/--
lemma `rpowIntegrand₀₁_eq_pow_div` / 引理 `rpowIntegrand₀₁_eq_pow_div`

English:
lemma rpowIntegrand₀₁_eq_pow_div
  given: (hp : p in Ioo 0 1) (ht : 0 <= t) (hx : 0 <= x)
  proof: by
  by_cases ht' : t = 0
  case neg =>
    have hxt : t + x != 0 := by positivity
    calc _ = (t : Real) ^ p * (t⁻¹ - (t + x)⁻¹) := rfl
      _ = (t : Real) ^ p * ((t + x - t) / (t * (t + x))) := by
          simp only [inv_eq_one_div]
          rw [div_sub_div _ _ (by lia) (by lia)]
          simp
      _ = t ^ p / t * x / (t + x) := by simp [field]
      _ = t ^ (p - 1) * x / (t + x) := by congr; exact (Real.rpow_sub_one ht' p).symm
  case pos =>
    push _ in _ at hp
    have hp₂ : p - 1 != 0 := by linarith
    simp [rpowIntegrand₀₁, ht', hp.1.ne', hp₂]

中文:
引理 rpow整数egrand₀₁_eq_pow_div
  条件: (hp : p in 开区间 0 1) (ht : 0 <= t) (hx : 0 <= x)
  证明: by
  by_cases ht' : t = 0
  case neg =>
    have hxt : t + x != 0 := by positivity
    calc _ = (t : Real) ^ p * (t⁻¹ - (t + x)⁻¹) := rfl
      _ = (t : Real) ^ p * ((t + x - t) / (t * (t + x))) := by
          simp only [inv_eq_one_div]
          rw [div_sub_div _ _ (by lia) (by lia)]
          simp
      _ = t ^ p / t * x / (t + x) := by simp [field]
      _ = t ^ (p - 1) * x / (t + x) := by congr; exact (Real.rpow_sub_one ht' p).symm
  case pos =>
    push _ in _ at hp
    have hp₂ : p - 1 != 0 := by linarith
    simp [rpowIntegrand₀₁, ht', hp.1.ne', hp₂]

Depends on / 依赖: Real.rpow_sub_one, div_sub_div, inv_eq_one_div, rpow_sub_one
-/
lemma rpowIntegrand₀₁_eq_pow_div (hp : p in Ioo 0 1) (ht : 0 <= t) (hx : 0 <= x) :
    rpowIntegrand₀₁ p t x = t ^ (p - 1) * x / (t + x) := by
  by_cases ht' : t = 0
  case neg =>
    have hxt : t + x != 0 := by positivity
    calc _ = (t : Real) ^ p * (t⁻¹ - (t + x)⁻¹) := rfl
      _ = (t : Real) ^ p * ((t + x - t) / (t * (t + x))) := by
          simp only [inv_eq_one_div]
          rw [div_sub_div _ _ (by lia) (by lia)]
          simp
      _ = t ^ p / t * x / (t + x) := by simp [field]
      _ = t ^ (p - 1) * x / (t + x) := by congr; exact (Real.rpow_sub_one ht' p).symm
  case pos =>
    push _ in _ at hp
    have hp₂ : p - 1 != 0 := by linarith
    simp [rpowIntegrand₀₁, ht', hp.1.ne', hp₂]

/--
lemma `rpowIntegrand₀₁_eqOn_pow_div` / 引理 `rpowIntegrand₀₁_eqOn_pow_div`

English:
lemma rpowIntegrand₀₁_eqOn_pow_div
  given: (hp : p in Ioo 0 1) (hx : 0 <= x)
  proof: by
  intro t ht
  simp [rpowIntegrand₀₁_eq_pow_div hp (le_of_lt ht) hx]

中文:
引理 rpow整数egrand₀₁_eqOn_pow_div
  条件: (hp : p in 开区间 0 1) (hx : 0 <= x)
  证明: by
  intro t ht
  simp [rpowIntegrand₀₁_eq_pow_div hp (le_of_lt ht) hx]

Depends on / 依赖: le_of_lt
-/
lemma rpowIntegrand₀₁_eqOn_pow_div (hp : p in Ioo 0 1) (hx : 0 <= x) :
    Set.EqOn (rpowIntegrand₀₁ p · x) (fun t => t ^ (p - 1) * x / (t + x)) (Ioi 0) := by
  intro t ht
  simp [rpowIntegrand₀₁_eq_pow_div hp (le_of_lt ht) hx]

/--
lemma `rpowIntegrand₀₁_apply_mul` / 引理 `rpowIntegrand₀₁_apply_mul`

English:
lemma rpowIntegrand₀₁_apply_mul
  given: (hp : p in Ioo 0 1) (ht : 0 <= t) (hx : 0 <= x)
  proof: by
  have hxt : 0 <= x * t := by positivity
  rw [rpowIntegrand₀₁_eq_pow_div hp hxt hx]; rw [rpowIntegrand₀₁_eq_pow_div hp ht zero_le_one]
  by_cases hx_zero : x = 0
  case neg =>
    calc _ = x ^ (p - 1) * (t ^ (p - 1) * (x / (x * t + x))) := by
              rw [← mul_assoc]; rw [mul_div_assoc]; rw [Real.mul_rpow hx ht]
      _ = x ^ (p - 1) * (t ^ (p - 1) * 1 / (t + 1)) := by
              have : x * t + x = x * (t + 1) := by ring
              rw [mul_div_assoc]; rw [this]; rw [div_mul_eq_div_mul_one_div]; rw [div_self hx_zero]; rw [one_mul]
      _ = t ^ (p - 1) * 1 / (t + 1) * x ^ (p - 1) := by rw [mul_comm]
  case pos =>
    rw [mem_Ioo] at hp
    simp [hx_zero, Real.zero_rpow (by linarith : p - 1 != 0)]

中文:
引理 rpow整数egrand₀₁_apply_mul
  条件: (hp : p in 开区间 0 1) (ht : 0 <= t) (hx : 0 <= x)
  证明: by
  have hxt : 0 <= x * t := by positivity
  rw [rpowIntegrand₀₁_eq_pow_div hp hxt hx]; rw [rpowIntegrand₀₁_eq_pow_div hp ht zero_le_one]
  by_cases hx_zero : x = 0
  case neg =>
    calc _ = x ^ (p - 1) * (t ^ (p - 1) * (x / (x * t + x))) := by
              rw [← mul_assoc]; rw [mul_div_assoc]; rw [Real.mul_rpow hx ht]
      _ = x ^ (p - 1) * (t ^ (p - 1) * 1 / (t + 1)) := by
              have : x * t + x = x * (t + 1) := by ring
              rw [mul_div_assoc]; rw [this]; rw [div_mul_eq_div_mul_one_div]; rw [div_self hx_zero]; rw [one_mul]
      _ = t ^ (p - 1) * 1 / (t + 1) * x ^ (p - 1) := by rw [mul_comm]
  case pos =>
    rw [mem_Ioo] at hp
    simp [hx_zero, Real.zero_rpow (by linarith : p - 1 != 0)]

Depends on / 依赖: Real.mul_rpow, div_mul_eq_div_mul_one_div, div_self, hx_zero, mul_assoc, mul_div_assoc, mul_rpow, one_mul, zero_le_one
-/
lemma rpowIntegrand₀₁_apply_mul (hp : p in Ioo 0 1) (ht : 0 <= t) (hx : 0 <= x) :
    rpowIntegrand₀₁ p (x * t) x = (rpowIntegrand₀₁ p t 1) * x ^ (p - 1) := by
  have hxt : 0 <= x * t := by positivity
  rw [rpowIntegrand₀₁_eq_pow_div hp hxt hx]; rw [rpowIntegrand₀₁_eq_pow_div hp ht zero_le_one]
  by_cases hx_zero : x = 0
  case neg =>
    calc _ = x ^ (p - 1) * (t ^ (p - 1) * (x / (x * t + x))) := by
              rw [← mul_assoc]; rw [mul_div_assoc]; rw [Real.mul_rpow hx ht]
      _ = x ^ (p - 1) * (t ^ (p - 1) * 1 / (t + 1)) := by
              have : x * t + x = x * (t + 1) := by ring
              rw [mul_div_assoc]; rw [this]; rw [div_mul_eq_div_mul_one_div]; rw [div_self hx_zero]; rw [one_mul]
      _ = t ^ (p - 1) * 1 / (t + 1) * x ^ (p - 1) := by rw [mul_comm]
  case pos =>
    rw [mem_Ioo] at hp
    simp [hx_zero, Real.zero_rpow (by linarith : p - 1 != 0)]

/--
lemma `rpowIntegrand₀₁_apply_mul'` / 引理 `rpowIntegrand₀₁_apply_mul'`

English:
lemma rpowIntegrand₀₁_apply_mul'
  given: (hp : p in Ioo 0 1) (ht : 0 <= t) (hx : 0 <= x)
  proof: by
  simp only [rpowIntegrand₀₁_apply_mul hp ht hx, mul_assoc]
  congr
simpa using Eq.symm Real.rpow_add' hx (by aesop : (p - 1) + 1 != 0)

中文:
引理 rpow整数egrand₀₁_apply_mul'
  条件: (hp : p in 开区间 0 1) (ht : 0 <= t) (hx : 0 <= x)
  证明: by
  simp only [rpowIntegrand₀₁_apply_mul hp ht hx, mul_assoc]
  congr
simpa using Eq.symm Real.rpow_add' hx (by aesop : (p - 1) + 1 != 0)

Depends on / 依赖: Eq.symm, Real.rpow_add, mul_assoc, rpow_add
-/
lemma rpowIntegrand₀₁_apply_mul' (hp : p in Ioo 0 1) (ht : 0 <= t) (hx : 0 <= x) :
    rpowIntegrand₀₁ p (x * t) x * x = (rpowIntegrand₀₁ p t 1) * x ^ p := by
  simp only [rpowIntegrand₀₁_apply_mul hp ht hx, mul_assoc]
  congr
simpa using Eq.symm Real.rpow_add' hx (by aesop : (p - 1) + 1 != 0)

/--
lemma `rpowIntegrand₀₁_apply_mul_eqOn_Ici` / 引理 `rpowIntegrand₀₁_apply_mul_eqOn_Ici`

English:
lemma rpowIntegrand₀₁_apply_mul_eqOn_Ici
  given: (hp : p in Ioo 0 1) (hx : 0 <= x)
  proof: fun _ ht => rpowIntegrand₀₁_apply_mul' hp ht hx

中文:
引理 rpow整数egrand₀₁_apply_mul_eqOn_Ici
  条件: (hp : p in 开区间 0 1) (hx : 0 <= x)
  证明: fun _ ht => rpowIntegrand₀₁_apply_mul' hp ht hx
-/
lemma rpowIntegrand₀₁_apply_mul_eqOn_Ici (hp : p in Ioo 0 1) (hx : 0 <= x) :
    (Ici 0).EqOn (fun t => rpowIntegrand₀₁ p (x * t) x * x)
      (fun t => (rpowIntegrand₀₁ p t 1) * x ^ p) :=
  fun _ ht => rpowIntegrand₀₁_apply_mul' hp ht hx

/--
lemma `continuousOn_rpowIntegrand₀₁` / 引理 `continuousOn_rpowIntegrand₀₁`

English:
lemma continuousOn_rpowIntegrand₀₁
  given: (hp : p in Ioo 0 1) (hx : 0 <= x)
  proof: by
refine ContinuousOn.congr ?_ rpowIntegrand₀₁_eqOn_pow_div hp hx
have h₀ : ContinuousOn (· ^ (p - 1) : Real -> Real) (Ioi 0) := .rpow_const (by fun_prop)
    fun t ht => .inl ht.ne'
  fun_prop (disch := grind -abstractProof)

中文:
引理 continuousOn_rpow整数egrand₀₁
  条件: (hp : p in 开区间 0 1) (hx : 0 <= x)
  证明: by
refine ContinuousOn.congr ?_ rpowIntegrand₀₁_eqOn_pow_div hp hx
have h₀ : ContinuousOn (· ^ (p - 1) : Real -> Real) (Ioi 0) := .rpow_const (by fun_prop)
    fun t ht => .inl ht.ne'
  fun_prop (disch := grind -abstractProof)

Depends on / 依赖: ContinuousOn, ContinuousOn.congr, abstractProof, fun_prop, ht.ne, rpow_const
-/
lemma continuousOn_rpowIntegrand₀₁ (hp : p in Ioo 0 1) (hx : 0 <= x) :
    ContinuousOn (rpowIntegrand₀₁ p · x) (Ioi 0) := by
refine ContinuousOn.congr ?_ rpowIntegrand₀₁_eqOn_pow_div hp hx
have h₀ : ContinuousOn (· ^ (p - 1) : Real -> Real) (Ioi 0) := .rpow_const (by fun_prop)
    fun t ht => .inl ht.ne'
  fun_prop (disch := grind -abstractProof)

/--
lemma `aestronglyMeasurable_rpowIntegrand₀₁` / 引理 `aestronglyMeasurable_rpowIntegrand₀₁`

English:
lemma aestronglyMeasurable_rpowIntegrand₀₁
  given: (hp : p in Ioo 0 1) (hx : 0 <= x)
  proof: (continuousOn_rpowIntegrand₀₁ hp hx).aestronglyMeasurable measurableSet_Ioi

中文:
引理 aestronglyMeasurable_rpow整数egrand₀₁
  条件: (hp : p in 开区间 0 1) (hx : 0 <= x)
  证明: (continuousOn_rpowIntegrand₀₁ hp hx).aestronglyMeasurable measurableSet_Ioi

Depends on / 依赖: aestronglyMeasurable, measurableSet_Ioi
-/
lemma aestronglyMeasurable_rpowIntegrand₀₁ (hp : p in Ioo 0 1) (hx : 0 <= x) :
    AEStronglyMeasurable (rpowIntegrand₀₁ p · x) (volume.restrict (Ioi 0)) :=
  (continuousOn_rpowIntegrand₀₁ hp hx).aestronglyMeasurable measurableSet_Ioi

/--
lemma `rpowIntegrand₀₁_monotoneOn` / 引理 `rpowIntegrand₀₁_monotoneOn`

English:
lemma rpowIntegrand₀₁_monotoneOn
  given: (hp : p in Ioo 0 1) (ht : 0 <= t)
  proof: by
  intro x hx y hy hxy
  by_cases h : x = 0
  case pos => simpa [h, rpowIntegrand₀₁] using rpowIntegrand₀₁_nonneg hp.1 ht hy
  case neg =>
    simp only [rpowIntegrand₀₁, mem_Ici] at hx h ⊢
    gcongr

中文:
引理 rpow整数egrand₀₁_monotoneOn
  条件: (hp : p in 开区间 0 1) (ht : 0 <= t)
  证明: by
  intro x hx y hy hxy
  by_cases h : x = 0
  case pos => simpa [h, rpowIntegrand₀₁] using rpowIntegrand₀₁_nonneg hp.1 ht hy
  case neg =>
    simp only [rpowIntegrand₀₁, mem_Ici] at hx h ⊢
    gcongr

Depends on / 依赖: mem_Ici
-/
lemma rpowIntegrand₀₁_monotoneOn (hp : p in Ioo 0 1) (ht : 0 <= t) :
    MonotoneOn (rpowIntegrand₀₁ p t) (Ici 0) := by
  intro x hx y hy hxy
  by_cases h : x = 0
  case pos => simpa [h, rpowIntegrand₀₁] using rpowIntegrand₀₁_nonneg hp.1 ht hy
  case neg =>
    simp only [rpowIntegrand₀₁, mem_Ici] at hx h ⊢
    gcongr

/--
lemma `continuousOn_rpowIntegrand₀₁_uncurry` / 引理 `continuousOn_rpowIntegrand₀₁_uncurry`

English:
lemma continuousOn_rpowIntegrand₀₁_uncurry
  given: (hp : p in Ioo 0 1) (s : Set Real) (hs : s subseteq Ici 0)
  proof: by
  let g : Real × Real -> Real := fun q => q.1 ^ (p - 1) * q.2 / (q.1 + q.2)
  refine ContinuousOn.congr (f := g) ?_ fun q => ?_
  · simp only [g]
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.mul ?_ (by fun_prop)
      exact ContinuousOn.rpow_const (by fun_prop) (by grind)
    · exact ContinuousOn.inv₀ (by fun_prop) (by grind)
  · intro hq
    simp [Function.uncurry, g, rpowIntegrand₀₁_eq_pow_div hp (le_of_lt hq.1) (hs hq.2)]

中文:
引理 continuousOn_rpow整数egrand₀₁_uncurry
  条件: (hp : p in 开区间 0 1) (s : 集合 实数) (hs : s subseteq 左闭右无界区间 0)
  证明: by
  let g : Real × Real -> Real := fun q => q.1 ^ (p - 1) * q.2 / (q.1 + q.2)
  refine ContinuousOn.congr (f := g) ?_ fun q => ?_
  · simp only [g]
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.mul ?_ (by fun_prop)
      exact ContinuousOn.rpow_const (by fun_prop) (by grind)
    · exact ContinuousOn.inv₀ (by fun_prop) (by grind)
  · intro hq
    simp [Function.uncurry, g, rpowIntegrand₀₁_eq_pow_div hp (le_of_lt hq.1) (hs hq.2)]

Depends on / 依赖: ContinuousOn, ContinuousOn.congr, ContinuousOn.inv, ContinuousOn.mul, ContinuousOn.rpow_const, Function, Function.uncurry, fun_prop, le_of_lt, rpow_const, uncurry
-/
lemma continuousOn_rpowIntegrand₀₁_uncurry (hp : p in Ioo 0 1) (s : Set Real) (hs : s subseteq Ici 0) :
    ContinuousOn (rpowIntegrand₀₁ p).uncurry (Ioi 0 ×ˢ s) := by
  let g : Real × Real -> Real := fun q => q.1 ^ (p - 1) * q.2 / (q.1 + q.2)
  refine ContinuousOn.congr (f := g) ?_ fun q => ?_
  · simp only [g]
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.mul ?_ (by fun_prop)
      exact ContinuousOn.rpow_const (by fun_prop) (by grind)
    · exact ContinuousOn.inv₀ (by fun_prop) (by grind)
  · intro hq
    simp [Function.uncurry, g, rpowIntegrand₀₁_eq_pow_div hp (le_of_lt hq.1) (hs hq.2)]

/--
lemma `continuousOn_rpowIntegrand₀₁_Ici` / 引理 `continuousOn_rpowIntegrand₀₁_Ici`

English:
lemma continuousOn_rpowIntegrand₀₁_Ici
  given: (hp : p in Ioo 0 1) (ht : 0 < t)
  proof: (continuousOn_rpowIntegrand₀₁_uncurry hp _ fun _ a => a).uncurry_left _ ht

中文:
引理 continuousOn_rpow整数egrand₀₁_Ici
  条件: (hp : p in 开区间 0 1) (ht : 0 < t)
  证明: (continuousOn_rpowIntegrand₀₁_uncurry hp _ fun _ a => a).uncurry_left _ ht

Depends on / 依赖: uncurry_left
-/
lemma continuousOn_rpowIntegrand₀₁_Ici (hp : p in Ioo 0 1) (ht : 0 < t) :
    ContinuousOn (rpowIntegrand₀₁ p t) (Ici 0) :=
  (continuousOn_rpowIntegrand₀₁_uncurry hp _ fun _ a => a).uncurry_left _ ht

/--
lemma `rpowIntegrand₀₁_le_rpow_sub_two_mul_self` / 引理 `rpowIntegrand₀₁_le_rpow_sub_two_mul_self`

English:
lemma rpowIntegrand₀₁_le_rpow_sub_two_mul_self
  given: (hp : p in Ioo 0 1) (ht : 0 < t) (hx : 0 <= x)
  proof: calc
  _ = t ^ (p - 1) * x / (t + x) := by rw [rpowIntegrand₀₁_eq_pow_div hp (le_of_lt ht) hx]
  _ <= t ^ (p - 1) * x / t := by gcongr; linarith
  _ = t ^ (p - 1) / t * x := by ring
  _ = t ^ (p - 2) * x := by
    congr
    rw [← Real.rpow_sub_one (by positivity)]
    congr 1
    ring

中文:
引理 rpow整数egrand₀₁_le_rpow_sub_two_mul_self
  条件: (hp : p in 开区间 0 1) (ht : 0 < t) (hx : 0 <= x)
  证明: calc
  _ = t ^ (p - 1) * x / (t + x) := by rw [rpowIntegrand₀₁_eq_pow_div hp (le_of_lt ht) hx]
  _ <= t ^ (p - 1) * x / t := by gcongr; linarith
  _ = t ^ (p - 1) / t * x := by ring
  _ = t ^ (p - 2) * x := by
    congr
    rw [← Real.rpow_sub_one (by positivity)]
    congr 1
    ring
-/
lemma rpowIntegrand₀₁_le_rpow_sub_two_mul_self (hp : p in Ioo 0 1) (ht : 0 < t) (hx : 0 <= x) :
    rpowIntegrand₀₁ p t x <= t ^ (p - 2) * x := calc
  _ = t ^ (p - 1) * x / (t + x) := by rw [rpowIntegrand₀₁_eq_pow_div hp (le_of_lt ht) hx]
  _ <= t ^ (p - 1) * x / t := by gcongr; linarith
  _ = t ^ (p - 1) / t * x := by ring
  _ = t ^ (p - 2) * x := by
    congr
    rw [← Real.rpow_sub_one (by positivity)]
    congr 1
    ring

/--
lemma `rpowIntegrand₀₁_le_rpow_sub_one` / 引理 `rpowIntegrand₀₁_le_rpow_sub_one`

English:
lemma rpowIntegrand₀₁_le_rpow_sub_one
  given: (hp : p in Ioo 0 1) (ht : 0 <= t) (hx : 0 <= x)
  proof: by
  by_cases hx_zero : x = 0
  case pos =>
    simp only [rpowIntegrand₀₁, hx_zero, add_zero, sub_self, mul_zero]
    positivity
  case neg =>
    calc
    _ = t ^ (p - 1) * x / (t + x) := by rw [rpowIntegrand₀₁_eq_pow_div hp ht hx]
    _ <= t ^ (p - 1) * x / x := by gcongr; linarith
    _ = t ^ (p - 1) * (x / x) := by ring
    _ = t ^ (p - 1) * 1 := by congr; exact (div_eq_one_iff_eq hx_zero).mpr rfl
    _ = _ := by simp

中文:
引理 rpow整数egrand₀₁_le_rpow_sub_one
  条件: (hp : p in 开区间 0 1) (ht : 0 <= t) (hx : 0 <= x)
  证明: by
  by_cases hx_zero : x = 0
  case pos =>
    simp only [rpowIntegrand₀₁, hx_zero, add_zero, sub_self, mul_zero]
    positivity
  case neg =>
    calc
    _ = t ^ (p - 1) * x / (t + x) := by rw [rpowIntegrand₀₁_eq_pow_div hp ht hx]
    _ <= t ^ (p - 1) * x / x := by gcongr; linarith
    _ = t ^ (p - 1) * (x / x) := by ring
    _ = t ^ (p - 1) * 1 := by congr; exact (div_eq_one_iff_eq hx_zero).mpr rfl
    _ = _ := by simp

Depends on / 依赖: add_zero, div_eq_one_iff_eq, hx_zero, mul_zero, sub_self
-/
lemma rpowIntegrand₀₁_le_rpow_sub_one (hp : p in Ioo 0 1) (ht : 0 <= t) (hx : 0 <= x) :
    rpowIntegrand₀₁ p t x <= t ^ (p - 1) := by
  by_cases hx_zero : x = 0
  case pos =>
    simp only [rpowIntegrand₀₁, hx_zero, add_zero, sub_self, mul_zero]
    positivity
  case neg =>
    calc
    _ = t ^ (p - 1) * x / (t + x) := by rw [rpowIntegrand₀₁_eq_pow_div hp ht hx]
    _ <= t ^ (p - 1) * x / x := by gcongr; linarith
    _ = t ^ (p - 1) * (x / x) := by ring
    _ = t ^ (p - 1) * 1 := by congr; exact (div_eq_one_iff_eq hx_zero).mpr rfl
    _ = _ := by simp

/--
lemma `rpowIntegrand₀₁_one_ge_rpow_sub_two` / 引理 `rpowIntegrand₀₁_one_ge_rpow_sub_two`

English:
lemma rpowIntegrand₀₁_one_ge_rpow_sub_two
  given: (hp : p in Ioo 0 1) (ht : 1 <= t)
  proof: calc
  _ = t ^ (p - 1) * (1 / 2 * 1 / t) := by
            have : p - 2 = p - 1 - 1 := by ring
            rw [this]; rw [Real.rpow_sub (by linarith)]; rw [Real.rpow_one]
            ring
  _ <= t ^ (p - 1) * (1 / (t + 1)) := by
            gcongr t ^ (p - 1) * ?_
            rw [mul_div_assoc]; rw [one_div_mul_one_div]; rw [one_div_le_one_div (by positivity) (by positivity)]
            linarith
  _ = rpowIntegrand₀₁ p t 1 := by
            rw [rpowIntegrand₀₁_eq_pow_div hp (by linarith) zero_le_one]; rw [mul_div_assoc]

中文:
引理 rpow整数egrand₀₁_one_ge_rpow_sub_two
  条件: (hp : p in 开区间 0 1) (ht : 1 <= t)
  证明: calc
  _ = t ^ (p - 1) * (1 / 2 * 1 / t) := by
            have : p - 2 = p - 1 - 1 := by ring
            rw [this]; rw [Real.rpow_sub (by linarith)]; rw [Real.rpow_one]
            ring
  _ <= t ^ (p - 1) * (1 / (t + 1)) := by
            gcongr t ^ (p - 1) * ?_
            rw [mul_div_assoc]; rw [one_div_mul_one_div]; rw [one_div_le_one_div (by positivity) (by positivity)]
            linarith
  _ = rpowIntegrand₀₁ p t 1 := by
            rw [rpowIntegrand₀₁_eq_pow_div hp (by linarith) zero_le_one]; rw [mul_div_assoc]
-/
lemma rpowIntegrand₀₁_one_ge_rpow_sub_two (hp : p in Ioo 0 1) (ht : 1 <= t) :
    (1 : Real) / 2 * t ^ (p - 2) <= rpowIntegrand₀₁ p t 1 := calc
  _ = t ^ (p - 1) * (1 / 2 * 1 / t) := by
            have : p - 2 = p - 1 - 1 := by ring
            rw [this]; rw [Real.rpow_sub (by linarith)]; rw [Real.rpow_one]
            ring
  _ <= t ^ (p - 1) * (1 / (t + 1)) := by
            gcongr t ^ (p - 1) * ?_
            rw [mul_div_assoc]; rw [one_div_mul_one_div]; rw [one_div_le_one_div (by positivity) (by positivity)]
            linarith
  _ = rpowIntegrand₀₁ p t 1 := by
            rw [rpowIntegrand₀₁_eq_pow_div hp (by linarith) zero_le_one]; rw [mul_div_assoc]

/--
lemma `rpowIntegrand₀₁_eqOn_mul_rpowIntegrand₀₁_one` / 引理 `rpowIntegrand₀₁_eqOn_mul_rpowIntegrand₀₁_one`

English:
lemma rpowIntegrand₀₁_eqOn_mul_rpowIntegrand₀₁_one
  given: (ht : 0 < t)
  proof: by
  intro x hx
  calc _ = t ^ p * (t⁻¹ - t⁻¹ * (1 + x * t⁻¹)⁻¹) := by simp [field, rpowIntegrand₀₁]
    _ = t ^ (p - 1) * (1 - (1 + x * t⁻¹)⁻¹) := by
          rw [Real.rpow_sub_one ht.ne']
          ring
    _ = _ := by simp [mul_comm, smul_eq_mul, rpowIntegrand₀₁]

中文:
引理 rpow整数egrand₀₁_eqOn_mul_rpow整数egrand₀₁_one
  条件: (ht : 0 < t)
  证明: by
  intro x hx
  calc _ = t ^ p * (t⁻¹ - t⁻¹ * (1 + x * t⁻¹)⁻¹) := by simp [field, rpowIntegrand₀₁]
    _ = t ^ (p - 1) * (1 - (1 + x * t⁻¹)⁻¹) := by
          rw [Real.rpow_sub_one ht.ne']
          ring
    _ = _ := by simp [mul_comm, smul_eq_mul, rpowIntegrand₀₁]

Depends on / 依赖: Real.rpow_sub_one, ht.ne, mul_comm, rpow_sub_one, smul_eq_mul
-/
lemma rpowIntegrand₀₁_eqOn_mul_rpowIntegrand₀₁_one (ht : 0 < t) :
    (Ici 0).EqOn (rpowIntegrand₀₁ p t)
      (fun x => t ^ (p - 1) * (rpowIntegrand₀₁ p 1 (t⁻¹ • x))) := by
  intro x hx
  calc _ = t ^ p * (t⁻¹ - t⁻¹ * (1 + x * t⁻¹)⁻¹) := by simp [field, rpowIntegrand₀₁]
    _ = t ^ (p - 1) * (1 - (1 + x * t⁻¹)⁻¹) := by
          rw [Real.rpow_sub_one ht.ne']
          ring
    _ = _ := by simp [mul_comm, smul_eq_mul, rpowIntegrand₀₁]

/--
lemma `integrableOn_rpowIntegrand₀₁_Ioc` / 引理 `integrableOn_rpowIntegrand₀₁_Ioc`

English:
lemma integrableOn_rpowIntegrand₀₁_Ioc
  given: (hp : p in Ioo 0 1) (hx : 0 <= x)
  proof: by
  refine IntegrableOn.congr_set_ae (t := Ioo 0 1) ?_ (Filter.EventuallyEq.symm Ioo_ae_eq_Ioc)
  refine ⟨?meas, ?finite⟩
  case meas =>
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    exact ContinuousOn.mono (continuousOn_rpowIntegrand₀₁ hp hx) Ioo_subset_Ioi_self
  case finite =>
    refine HasFiniteIntegral.mono' (g := fun t => t ^ (p - 1)) ?finitebound ?ae_le
    case finitebound =>
      apply Integrable.hasFiniteIntegral
      rw [Set.mem_Ioo] at hp
      rw [← IntegrableOn]; rw [intervalIntegral.integrableOn_Ioo_rpow_iff]
      · linarith
      · exact zero_lt_one
    case ae_le =>
      refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_
      rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg hp.1 (le_of_lt ht.1) hx)]
      exact rpowIntegrand₀₁_le_rpow_sub_one hp (le_of_lt ht.1) hx

中文:
引理 integrableOn_rpow整数egrand₀₁_Ioc
  条件: (hp : p in 开区间 0 1) (hx : 0 <= x)
  证明: by
  refine IntegrableOn.congr_set_ae (t := Ioo 0 1) ?_ (Filter.EventuallyEq.symm Ioo_ae_eq_Ioc)
  refine ⟨?meas, ?finite⟩
  case meas =>
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    exact ContinuousOn.mono (continuousOn_rpowIntegrand₀₁ hp hx) Ioo_subset_Ioi_self
  case finite =>
    refine HasFiniteIntegral.mono' (g := fun t => t ^ (p - 1)) ?finitebound ?ae_le
    case finitebound =>
      apply Integrable.hasFiniteIntegral
      rw [Set.mem_Ioo] at hp
      rw [← IntegrableOn]; rw [intervalIntegral.integrableOn_Ioo_rpow_iff]
      · linarith
      · exact zero_lt_one
    case ae_le =>
      refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_
      rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg hp.1 (le_of_lt ht.1) hx)]
      exact rpowIntegrand₀₁_le_rpow_sub_one hp (le_of_lt ht.1) hx
-/
private lemma integrableOn_rpowIntegrand₀₁_Ioc (hp : p in Ioo 0 1) (hx : 0 <= x) :
    IntegrableOn (rpowIntegrand₀₁ p · x) (Ioc 0 1) := by
  refine IntegrableOn.congr_set_ae (t := Ioo 0 1) ?_ (Filter.EventuallyEq.symm Ioo_ae_eq_Ioc)
  refine ⟨?meas, ?finite⟩
  case meas =>
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    exact ContinuousOn.mono (continuousOn_rpowIntegrand₀₁ hp hx) Ioo_subset_Ioi_self
  case finite =>
    refine HasFiniteIntegral.mono' (g := fun t => t ^ (p - 1)) ?finitebound ?ae_le
    case finitebound =>
      apply Integrable.hasFiniteIntegral
      rw [Set.mem_Ioo] at hp
      rw [← IntegrableOn]; rw [intervalIntegral.integrableOn_Ioo_rpow_iff]
      · linarith
      · exact zero_lt_one
    case ae_le =>
      refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => ?_
      rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg hp.1 (le_of_lt ht.1) hx)]
      exact rpowIntegrand₀₁_le_rpow_sub_one hp (le_of_lt ht.1) hx

/--
lemma `integrableOn_rpowIntegrand₀₁_Ioi_one` / 引理 `integrableOn_rpowIntegrand₀₁_Ioi_one`

English:
lemma integrableOn_rpowIntegrand₀₁_Ioi_one
  given: (hp : p in Ioo 0 1) (hx : 0 <= x)
  proof: by
  refine ⟨?meas, ?finite⟩
  case meas =>
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
.mono (Set.Ioi_subset_Ioi zero_le_one) exact continuousOn_rpowIntegrand₀₁ hp hx
  case finite =>
    refine HasFiniteIntegral.mono' (g := fun t => t ^ (p - 2) * x) ?finitebound ?ae_le
    case finitebound =>
      refine HasFiniteIntegral.mul_const ?_ _
      apply Integrable.hasFiniteIntegral
      rw [Set.mem_Ioo] at hp
      refine integrableOn_Ioi_rpow_of_lt ?_ zero_lt_one
      linarith
    case ae_le =>
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 1 < t) => ?_
      rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg hp.1 (by positivity) hx)]
      exact rpowIntegrand₀₁_le_rpow_sub_two_mul_self hp (by positivity) hx

中文:
引理 integrableOn_rpow整数egrand₀₁_Ioi_one
  条件: (hp : p in 开区间 0 1) (hx : 0 <= x)
  证明: by
  refine ⟨?meas, ?finite⟩
  case meas =>
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
.mono (Set.Ioi_subset_Ioi zero_le_one) exact continuousOn_rpowIntegrand₀₁ hp hx
  case finite =>
    refine HasFiniteIntegral.mono' (g := fun t => t ^ (p - 2) * x) ?finitebound ?ae_le
    case finitebound =>
      refine HasFiniteIntegral.mul_const ?_ _
      apply Integrable.hasFiniteIntegral
      rw [Set.mem_Ioo] at hp
      refine integrableOn_Ioi_rpow_of_lt ?_ zero_lt_one
      linarith
    case ae_le =>
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 1 < t) => ?_
      rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg hp.1 (by positivity) hx)]
      exact rpowIntegrand₀₁_le_rpow_sub_two_mul_self hp (by positivity) hx
-/
private lemma integrableOn_rpowIntegrand₀₁_Ioi_one (hp : p in Ioo 0 1) (hx : 0 <= x) :
    IntegrableOn (rpowIntegrand₀₁ p · x) (Ioi 1) := by
  refine ⟨?meas, ?finite⟩
  case meas =>
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
.mono (Set.Ioi_subset_Ioi zero_le_one) exact continuousOn_rpowIntegrand₀₁ hp hx
  case finite =>
    refine HasFiniteIntegral.mono' (g := fun t => t ^ (p - 2) * x) ?finitebound ?ae_le
    case finitebound =>
      refine HasFiniteIntegral.mul_const ?_ _
      apply Integrable.hasFiniteIntegral
      rw [Set.mem_Ioo] at hp
      refine integrableOn_Ioi_rpow_of_lt ?_ zero_lt_one
      linarith
    case ae_le =>
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 1 < t) => ?_
      rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg hp.1 (by positivity) hx)]
      exact rpowIntegrand₀₁_le_rpow_sub_two_mul_self hp (by positivity) hx

/--
lemma `integrableOn_rpowIntegrand₀₁_Ioi` / 引理 `integrableOn_rpowIntegrand₀₁_Ioi`

English:
lemma integrableOn_rpowIntegrand₀₁_Ioi
  given: (hp : p in Ioo 0 1) (hx : 0 <= x)
  proof: by
  /- The integral converges because it is `O(t ^ (p-1))` at the origin and `O(t ^ (p-2))` at
  infinity. Hence we break the integral into two parts. -/
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact IntegrableOn.union (integrableOn_rpowIntegrand₀₁_Ioc hp hx)
    (integrableOn_rpowIntegrand₀₁_Ioi_one hp hx)

中文:
引理 integrableOn_rpow整数egrand₀₁_Ioi
  条件: (hp : p in 开区间 0 1) (hx : 0 <= x)
  证明: by
  /- The integral converges because it is `O(t ^ (p-1))` at the origin and `O(t ^ (p-2))` at
  infinity. Hence we break the integral into two parts. -/
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact IntegrableOn.union (integrableOn_rpowIntegrand₀₁_Ioc hp hx)
    (integrableOn_rpowIntegrand₀₁_Ioi_one hp hx)
-/
lemma integrableOn_rpowIntegrand₀₁_Ioi (hp : p in Ioo 0 1) (hx : 0 <= x) :
    IntegrableOn (rpowIntegrand₀₁ p · x) (Ioi 0) := by
  /- The integral converges because it is `O(t ^ (p-1))` at the origin and `O(t ^ (p-2))` at
  infinity. Hence we break the integral into two parts. -/
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact IntegrableOn.union (integrableOn_rpowIntegrand₀₁_Ioc hp hx)
    (integrableOn_rpowIntegrand₀₁_Ioi_one hp hx)

/--
lemma `integrableOn_rpowIntegrand₀₁_Ici` / 引理 `integrableOn_rpowIntegrand₀₁_Ici`

English:
lemma integrableOn_rpowIntegrand₀₁_Ici
  given: (hp : p in Ioo 0 1) (hx : 0 <= x)
  proof: .congr_set_ae Ioi_ae_eq_Ici.symm integrableOn_rpowIntegrand₀₁_Ioi hp hx

中文:
引理 integrableOn_rpow整数egrand₀₁_Ici
  条件: (hp : p in 开区间 0 1) (hx : 0 <= x)
  证明: .congr_set_ae Ioi_ae_eq_Ici.symm integrableOn_rpowIntegrand₀₁_Ioi hp hx

Depends on / 依赖: Ioi_ae_eq_Ici, Ioi_ae_eq_Ici.symm, congr_set_ae
-/
lemma integrableOn_rpowIntegrand₀₁_Ici (hp : p in Ioo 0 1) (hx : 0 <= x) :
    IntegrableOn (rpowIntegrand₀₁ p · x) (Ici 0) :=
.congr_set_ae Ioi_ae_eq_Ici.symm integrableOn_rpowIntegrand₀₁_Ioi hp hx

/--
lemma `integral_rpowIntegrand₀₁_eq_rpow_mul_const` / 引理 `integral_rpowIntegrand₀₁_eq_rpow_mul_const`

English:
lemma integral_rpowIntegrand₀₁_eq_rpow_mul_const
  given: (hp : p in Ioo 0 1) (hx : 0 <= x)
  proof: by
  -- We use the change of variables formula with `f t = x * t`. Here `g = rpowIntegrand₀₁ p · x`.
  obtain (rfl | hx) := hx.eq_or_lt
  · simp [rpowIntegrand₀₁, Real.zero_rpow hp.1.ne']
  suffices ∫ t in Ioi 0, ((rpowIntegrand₀₁ p · x) ∘ (x * ·)) t * x =
      x ^ p * (∫ t in Ioi 0, rpowIntegrand₀₁ p t 1) by
    rwa [integral_comp_mul_deriv_Ioi (by fun_prop), mul_zero] at this
    · exact tendsto_id.const_mul_atTop hx
.const_mul x · simpa using fun t _ => hasDerivWithinAt_id t (Ioi t)
    · simpa [Set.image_mul_left_Ioi hx] using continuousOn_rpowIntegrand₀₁ hp hx.le
    · simpa [Set.image_mul_left_Ici hx] using integrableOn_rpowIntegrand₀₁_Ici hp hx.le
    · simp only [Function.comp]
      rw [integrableOn_congr_fun (rpowIntegrand₀₁_apply_mul_eqOn_Ici hp hx.le) measurableSet_Ici]
      exact Integrable.mul_const (integrableOn_rpowIntegrand₀₁_Ici hp zero_le_one) _
  have heqOn : EqOn (fun t => rpowIntegrand₀₁ p (x * t) x * x)
      (fun t => (rpowIntegrand₀₁ p t 1) * x ^ p) (Ioi 0) :=
    EqOn.mono Ioi_subset_Ici_self (rpowIntegrand₀₁_apply_mul_eqOn_Ici hp hx.le)
  simp only [Function.comp, setIntegral_congr_fun measurableSet_Ioi heqOn,
    ← smul_eq_mul (b := x ^ p), integral_smul_const]
  rw [smul_eq_mul]; rw [mul_comm]

中文:
引理 integral_rpow整数egrand₀₁_eq_rpow_mul_const
  条件: (hp : p in 开区间 0 1) (hx : 0 <= x)
  证明: by
  -- We use the change of variables formula with `f t = x * t`. Here `g = rpowIntegrand₀₁ p · x`.
  obtain (rfl | hx) := hx.eq_or_lt
  · simp [rpowIntegrand₀₁, Real.zero_rpow hp.1.ne']
  suffices ∫ t in Ioi 0, ((rpowIntegrand₀₁ p · x) ∘ (x * ·)) t * x =
      x ^ p * (∫ t in Ioi 0, rpowIntegrand₀₁ p t 1) by
    rwa [integral_comp_mul_deriv_Ioi (by fun_prop), mul_zero] at this
    · exact tendsto_id.const_mul_atTop hx
.const_mul x · simpa using fun t _ => hasDerivWithinAt_id t (Ioi t)
    · simpa [Set.image_mul_left_Ioi hx] using continuousOn_rpowIntegrand₀₁ hp hx.le
    · simpa [Set.image_mul_left_Ici hx] using integrableOn_rpowIntegrand₀₁_Ici hp hx.le
    · simp only [Function.comp]
      rw [integrableOn_congr_fun (rpowIntegrand₀₁_apply_mul_eqOn_Ici hp hx.le) measurableSet_Ici]
      exact Integrable.mul_const (integrableOn_rpowIntegrand₀₁_Ici hp zero_le_one) _
  have heqOn : EqOn (fun t => rpowIntegrand₀₁ p (x * t) x * x)
      (fun t => (rpowIntegrand₀₁ p t 1) * x ^ p) (Ioi 0) :=
    EqOn.mono Ioi_subset_Ici_self (rpowIntegrand₀₁_apply_mul_eqOn_Ici hp hx.le)
  simp only [Function.comp, setIntegral_congr_fun measurableSet_Ioi heqOn,
    ← smul_eq_mul (b := x ^ p), integral_smul_const]
  rw [smul_eq_mul]; rw [mul_comm]
-/
lemma integral_rpowIntegrand₀₁_eq_rpow_mul_const (hp : p in Ioo 0 1) (hx : 0 <= x) :
    (∫ t in Ioi 0, rpowIntegrand₀₁ p t x) = x ^ p * (∫ t in Ioi 0, rpowIntegrand₀₁ p t 1) := by
  -- We use the change of variables formula with `f t = x * t`. Here `g = rpowIntegrand₀₁ p · x`.
  obtain (rfl | hx) := hx.eq_or_lt
  · simp [rpowIntegrand₀₁, Real.zero_rpow hp.1.ne']
  suffices ∫ t in Ioi 0, ((rpowIntegrand₀₁ p · x) ∘ (x * ·)) t * x =
      x ^ p * (∫ t in Ioi 0, rpowIntegrand₀₁ p t 1) by
    rwa [integral_comp_mul_deriv_Ioi (by fun_prop), mul_zero] at this
    · exact tendsto_id.const_mul_atTop hx
.const_mul x · simpa using fun t _ => hasDerivWithinAt_id t (Ioi t)
    · simpa [Set.image_mul_left_Ioi hx] using continuousOn_rpowIntegrand₀₁ hp hx.le
    · simpa [Set.image_mul_left_Ici hx] using integrableOn_rpowIntegrand₀₁_Ici hp hx.le
    · simp only [Function.comp]
      rw [integrableOn_congr_fun (rpowIntegrand₀₁_apply_mul_eqOn_Ici hp hx.le) measurableSet_Ici]
      exact Integrable.mul_const (integrableOn_rpowIntegrand₀₁_Ici hp zero_le_one) _
  have heqOn : EqOn (fun t => rpowIntegrand₀₁ p (x * t) x * x)
      (fun t => (rpowIntegrand₀₁ p t 1) * x ^ p) (Ioi 0) :=
    EqOn.mono Ioi_subset_Ici_self (rpowIntegrand₀₁_apply_mul_eqOn_Ici hp hx.le)
  simp only [Function.comp, setIntegral_congr_fun measurableSet_Ioi heqOn,
    ← smul_eq_mul (b := x ^ p), integral_smul_const]
  rw [smul_eq_mul]; rw [mul_comm]

/--
lemma `le_integral_rpowIntegrand₀₁_one` / 引理 `le_integral_rpowIntegrand₀₁_one`

English:
lemma le_integral_rpowIntegrand₀₁_one
  given: (hp : p in Ioo 0 1)
  proof: calc
  _ = (1 / 2) * -((1 : Real) ^ (p - 1)) / (p - 1) := by rw [← div_div]; simp [neg_div]
  _ = ∫ t in Ioi 1, (1 / 2) * t ^ (p - 2) := by
        push _ in _ at hp
        rw [integral_const_mul]; rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
        ring_nf -- ring alone succeeds but gives a warning
  _ <= ∫ t in Ioi 1, rpowIntegrand₀₁ p t 1 := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi ?_
        · refine Integrable.const_mul ?_ _
          push _ in _ at hp
          exact integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
        · exact integrableOn_rpowIntegrand₀₁_Ioi_one hp zero_le_one
        · exact fun t ht => rpowIntegrand₀₁_one_ge_rpow_sub_two hp (le_of_lt ht)
  _ <= ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 := by
        refine setIntegral_mono_set (integrableOn_rpowIntegrand₀₁_Ioi hp zero_le_one) ?_ ?_
        · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
          exact rpowIntegrand₀₁_nonneg hp.1 (le_of_lt ht) zero_le_one
· exact .of_forall Set.Ioi_subset_Ioi zero_le_one

中文:
引理 le_integral_rpow整数egrand₀₁_one
  条件: (hp : p in 开区间 0 1)
  证明: calc
  _ = (1 / 2) * -((1 : Real) ^ (p - 1)) / (p - 1) := by rw [← div_div]; simp [neg_div]
  _ = ∫ t in Ioi 1, (1 / 2) * t ^ (p - 2) := by
        push _ in _ at hp
        rw [integral_const_mul]; rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
        ring_nf -- ring alone succeeds but gives a warning
  _ <= ∫ t in Ioi 1, rpowIntegrand₀₁ p t 1 := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi ?_
        · refine Integrable.const_mul ?_ _
          push _ in _ at hp
          exact integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
        · exact integrableOn_rpowIntegrand₀₁_Ioi_one hp zero_le_one
        · exact fun t ht => rpowIntegrand₀₁_one_ge_rpow_sub_two hp (le_of_lt ht)
  _ <= ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 := by
        refine setIntegral_mono_set (integrableOn_rpowIntegrand₀₁_Ioi hp zero_le_one) ?_ ?_
        · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
          exact rpowIntegrand₀₁_nonneg hp.1 (le_of_lt ht) zero_le_one
· exact .of_forall Set.Ioi_subset_Ioi zero_le_one
-/
lemma le_integral_rpowIntegrand₀₁_one (hp : p in Ioo 0 1) :
    -1 / (2 * (p - 1)) <= ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 := calc
  _ = (1 / 2) * -((1 : Real) ^ (p - 1)) / (p - 1) := by rw [← div_div]; simp [neg_div]
  _ = ∫ t in Ioi 1, (1 / 2) * t ^ (p - 2) := by
        push _ in _ at hp
        rw [integral_const_mul]; rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
        ring_nf -- ring alone succeeds but gives a warning
  _ <= ∫ t in Ioi 1, rpowIntegrand₀₁ p t 1 := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi ?_
        · refine Integrable.const_mul ?_ _
          push _ in _ at hp
          exact integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
        · exact integrableOn_rpowIntegrand₀₁_Ioi_one hp zero_le_one
        · exact fun t ht => rpowIntegrand₀₁_one_ge_rpow_sub_two hp (le_of_lt ht)
  _ <= ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 := by
        refine setIntegral_mono_set (integrableOn_rpowIntegrand₀₁_Ioi hp zero_le_one) ?_ ?_
        · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
          exact rpowIntegrand₀₁_nonneg hp.1 (le_of_lt ht) zero_le_one
· exact .of_forall Set.Ioi_subset_Ioi zero_le_one

/--
lemma `integral_rpowIntegrand₀₁_one_pos` / 引理 `integral_rpowIntegrand₀₁_one_pos`

English:
lemma integral_rpowIntegrand₀₁_one_pos
  given: (hp : p in Ioo 0 1)
  proof: calc
  0 < -1 / (2 * (p - 1)) := by
      rw [neg_div]; rw [neg_pos]; rw [one_div_neg]
      push _ in _ at hp
      linarith
  _ <= ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 := le_integral_rpowIntegrand₀₁_one hp

中文:
引理 integral_rpow整数egrand₀₁_one_pos
  条件: (hp : p in 开区间 0 1)
  证明: calc
  0 < -1 / (2 * (p - 1)) := by
      rw [neg_div]; rw [neg_pos]; rw [one_div_neg]
      push _ in _ at hp
      linarith
  _ <= ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 := le_integral_rpowIntegrand₀₁_one hp
-/
lemma integral_rpowIntegrand₀₁_one_pos (hp : p in Ioo 0 1) :
    0 < ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 := calc
  0 < -1 / (2 * (p - 1)) := by
      rw [neg_div]; rw [neg_pos]; rw [one_div_neg]
      push _ in _ at hp
      linarith
  _ <= ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 := le_integral_rpowIntegrand₀₁_one hp

/--
lemma `rpow_eq_const_mul_integral` / 引理 `rpow_eq_const_mul_integral`

English:
lemma rpow_eq_const_mul_integral
  given: (hp : p in Ioo 0 1) (hx : 0 <= x)
  proof: by
  rcases eq_or_lt_of_le' hx with hx_zero | _
  case inl =>
    push _ in _ at hp
    simp [hx_zero, Real.zero_rpow (by linarith)]
  case inr =>
    have : ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 != 0 :=
ne_of_gt integral_rpowIntegrand₀₁_one_pos hp
    rw [integral_rpowIntegrand₀₁_eq_rpow_mul_const hp hx]; rw [mul_comm]; rw [mul_assoc]; rw [mul_inv_cancel₀
      this]; rw [mul_one]

中文:
引理 rpow_eq_const_mul_integral
  条件: (hp : p in 开区间 0 1) (hx : 0 <= x)
  证明: by
  rcases eq_or_lt_of_le' hx with hx_zero | _
  case inl =>
    push _ in _ at hp
    simp [hx_zero, Real.zero_rpow (by linarith)]
  case inr =>
    have : ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 != 0 :=
ne_of_gt integral_rpowIntegrand₀₁_one_pos hp
    rw [integral_rpowIntegrand₀₁_eq_rpow_mul_const hp hx]; rw [mul_comm]; rw [mul_assoc]; rw [mul_inv_cancel₀
      this]; rw [mul_one]

Depends on / 依赖: Real.zero_rpow, eq_or_lt_of_le, hx_zero, mul_assoc, mul_comm, mul_one, ne_of_gt, zero_rpow
-/
lemma rpow_eq_const_mul_integral (hp : p in Ioo 0 1) (hx : 0 <= x) :
    x ^ p = (∫ t in Ioi 0, rpowIntegrand₀₁ p t 1)⁻¹ * ∫ t in Ioi 0, rpowIntegrand₀₁ p t x := by
  rcases eq_or_lt_of_le' hx with hx_zero | _
  case inl =>
    push _ in _ at hp
    simp [hx_zero, Real.zero_rpow (by linarith)]
  case inr =>
    have : ∫ t in Ioi 0, rpowIntegrand₀₁ p t 1 != 0 :=
ne_of_gt integral_rpowIntegrand₀₁_one_pos hp
    rw [integral_rpowIntegrand₀₁_eq_rpow_mul_const hp hx]; rw [mul_comm]; rw [mul_assoc]; rw [mul_inv_cancel₀
      this]; rw [mul_one]

/--
lemma `exists_measure_rpow_eq_integral_rpowIntegrand₀₁` / 引理 `exists_measure_rpow_eq_integral_rpowIntegrand₀₁`

English:
lemma exists_measure_rpow_eq_integral_rpowIntegrand₀₁
  given: (hp : p in Ioo 0 1)
  proof: by
  let C : Real>=0 := .mk (∫ t in Ioi 0, rpowIntegrand₀₁ p t 1)⁻¹
    (by rw [inv_nonneg]; exact le_of_lt <| integral_rpowIntegrand₀₁_one_pos hp)
  refine ⟨C • volume, fun x hx => ⟨?_, ?_⟩⟩
  · unfold IntegrableOn
    rw [Measure.restrict_smul]
exact Integrable.smul_measure_nnreal integrableOn_rpowIntegrand₀₁_Ioi hp hx
  · simp_rw [Measure.restrict_smul, integral_smul_nnreal_measure, rpow_eq_const_mul_integral hp hx,
      NNReal.smul_def, C, NNReal.coe_mk, smul_eq_mul]

@[deprecated (since := "2026-04-03")]
alias exists_measure_rpow_eq_integral := exists_measure_rpow_eq_integral_rpowIntegrand₀₁

中文:
引理 存在_measure_rpow_eq_integral_rpow整数egrand₀₁
  条件: (hp : p in 开区间 0 1)
  证明: by
  let C : Real>=0 := .mk (∫ t in Ioi 0, rpowIntegrand₀₁ p t 1)⁻¹
    (by rw [inv_nonneg]; exact le_of_lt <| integral_rpowIntegrand₀₁_one_pos hp)
  refine ⟨C • volume, fun x hx => ⟨?_, ?_⟩⟩
  · unfold IntegrableOn
    rw [Measure.restrict_smul]
exact Integrable.smul_measure_nnreal integrableOn_rpowIntegrand₀₁_Ioi hp hx
  · simp_rw [Measure.restrict_smul, integral_smul_nnreal_measure, rpow_eq_const_mul_integral hp hx,
      NNReal.smul_def, C, NNReal.coe_mk, smul_eq_mul]

@[deprecated (since := "2026-04-03")]
alias exists_measure_rpow_eq_integral := exists_measure_rpow_eq_integral_rpowIntegrand₀₁

Depends on / 依赖: Integrable, Integrable.smul_measure_nnreal, IntegrableOn, Measure, Measure.restrict_smul, NNReal, NNReal.coe_mk, NNReal.smul_def, coe_mk, integral_smul_nnreal_measure, inv_nonneg, le_of_lt, restrict_smul, rpow_eq_const_mul_integral, simp_rw, smul_def, smul_eq_mul, smul_measure_nnreal, volume
-/
lemma exists_measure_rpow_eq_integral_rpowIntegrand₀₁ (hp : p in Ioo 0 1) :
    exists μ : Measure Real, forall x in Ici 0,
      (IntegrableOn (fun t => rpowIntegrand₀₁ p t x) (Ioi 0) μ)
      ∧ x ^ p = ∫ t in Ioi 0, rpowIntegrand₀₁ p t x ∂μ := by
  let C : Real>=0 := .mk (∫ t in Ioi 0, rpowIntegrand₀₁ p t 1)⁻¹
    (by rw [inv_nonneg]; exact le_of_lt <| integral_rpowIntegrand₀₁_one_pos hp)
  refine ⟨C • volume, fun x hx => ⟨?_, ?_⟩⟩
  · unfold IntegrableOn
    rw [Measure.restrict_smul]
exact Integrable.smul_measure_nnreal integrableOn_rpowIntegrand₀₁_Ioi hp hx
  · simp_rw [Measure.restrict_smul, integral_smul_nnreal_measure, rpow_eq_const_mul_integral hp hx,
      NNReal.smul_def, C, NNReal.coe_mk, smul_eq_mul]

@[deprecated (since := "2026-04-03")]
alias exists_measure_rpow_eq_integral := exists_measure_rpow_eq_integral_rpowIntegrand₀₁

end ZeroOne

section OneTwo
/-
## `p ∈ (1,2)`
-/
variable {p t x : Real}

/--
lemma `rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁` / 引理 `rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁`

English:
lemma rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁
  given: (hx : 0 <= x) (ht : 0 < t)
  proof: by
  grind [rpowIntegrand₁₂, rpowIntegrand₀₁]

中文:
引理 rpow整数egrand₁₂_eq_mul_rpow整数egrand₀₁
  条件: (hx : 0 <= x) (ht : 0 < t)
  证明: by
  grind [rpowIntegrand₁₂, rpowIntegrand₀₁]
-/
lemma rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ (hx : 0 <= x) (ht : 0 < t) :
    rpowIntegrand₁₂ p t x = x * rpowIntegrand₀₁ (p - 1) t x := by
  grind [rpowIntegrand₁₂, rpowIntegrand₀₁]

/--
lemma `rpowIntegrand₁₂_nonneg` / 引理 `rpowIntegrand₁₂_nonneg`

English:
lemma rpowIntegrand₁₂_nonneg
  given: (hp : 1 < p) (ht : 0 <= t) (hx : 0 <= x)
  proof: by
  by_cases ht' : 0 < t
  · rw [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hx ht']
    refine mul_nonneg hx ?_
    exact rpowIntegrand₀₁_nonneg (by grind) (by grind) hx
  · have ht' : t = 0 := by grind
    simp [rpowIntegrand₁₂, ht', zero_rpow (by grind : p - 1 != 0)]

中文:
引理 rpow整数egrand₁₂_nonneg
  条件: (hp : 1 < p) (ht : 0 <= t) (hx : 0 <= x)
  证明: by
  by_cases ht' : 0 < t
  · rw [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hx ht']
    refine mul_nonneg hx ?_
    exact rpowIntegrand₀₁_nonneg (by grind) (by grind) hx
  · have ht' : t = 0 := by grind
    simp [rpowIntegrand₁₂, ht', zero_rpow (by grind : p - 1 != 0)]

Depends on / 依赖: mul_nonneg, zero_rpow
-/
lemma rpowIntegrand₁₂_nonneg (hp : 1 < p) (ht : 0 <= t) (hx : 0 <= x) :
    0 <= rpowIntegrand₁₂ p t x := by
  by_cases ht' : 0 < t
  · rw [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hx ht']
    refine mul_nonneg hx ?_
    exact rpowIntegrand₀₁_nonneg (by grind) (by grind) hx
  · have ht' : t = 0 := by grind
    simp [rpowIntegrand₁₂, ht', zero_rpow (by grind : p - 1 != 0)]

/--
lemma `rpowIntegrand₁₂_zero` / 引理 `rpowIntegrand₁₂_zero`

English:
lemma rpowIntegrand₁₂_zero
  given: (ht : 0 < t)
  proof: by grind [rpowIntegrand₁₂]

@[fun_prop]

中文:
引理 rpow整数egrand₁₂_zero
  条件: (ht : 0 < t)
  证明: by grind [rpowIntegrand₁₂]

@[fun_prop]
-/
lemma rpowIntegrand₁₂_zero (ht : 0 < t) :
    rpowIntegrand₁₂ p t 0 = 0 := by grind [rpowIntegrand₁₂]

@[fun_prop]
/--
lemma `continuousOn_rpowIntegrand₁₂_uncurry` / 引理 `continuousOn_rpowIntegrand₁₂_uncurry`

English:
lemma continuousOn_rpowIntegrand₁₂_uncurry
  given: (hp : p in Ioi 1) (s : Set Real) (hs : s subseteq Ici 0)
  proof: by
  unfold rpowIntegrand₁₂
  fun_prop (disch := grind)

中文:
引理 continuousOn_rpow整数egrand₁₂_uncurry
  条件: (hp : p in 左开右无界区间 1) (s : 集合 实数) (hs : s subseteq 左闭右无界区间 0)
  证明: by
  unfold rpowIntegrand₁₂
  fun_prop (disch := grind)

Depends on / 依赖: fun_prop
-/
lemma continuousOn_rpowIntegrand₁₂_uncurry (hp : p in Ioi 1) (s : Set Real) (hs : s subseteq Ici 0) :
    ContinuousOn (rpowIntegrand₁₂ p).uncurry (Ioi 0 ×ˢ s) := by
  unfold rpowIntegrand₁₂
  fun_prop (disch := grind)

/--
lemma `monotoneOn_rpowIntegrand₁₂` / 引理 `monotoneOn_rpowIntegrand₁₂`

English:
lemma monotoneOn_rpowIntegrand₁₂
  given: (hp : p in Ioo 1 2) (ht : 0 < t)
  proof: by
  refine MonotoneOn.congr ?_ fun x hx => (rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hx ht).symm
  apply monotoneOn_id.mul <;> grind [rpowIntegrand₀₁_monotoneOn, rpowIntegrand₀₁_nonneg]

中文:
引理 monotoneOn_rpow整数egrand₁₂
  条件: (hp : p in 开区间 1 2) (ht : 0 < t)
  证明: by
  refine MonotoneOn.congr ?_ fun x hx => (rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hx ht).symm
  apply monotoneOn_id.mul <;> grind [rpowIntegrand₀₁_monotoneOn, rpowIntegrand₀₁_nonneg]

Depends on / 依赖: MonotoneOn, MonotoneOn.congr, monotoneOn_id, monotoneOn_id.mul
-/
lemma monotoneOn_rpowIntegrand₁₂ (hp : p in Ioo 1 2) (ht : 0 < t) :
    MonotoneOn (rpowIntegrand₁₂ p t) (Ici 0) := by
  refine MonotoneOn.congr ?_ fun x hx => (rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hx ht).symm
  apply monotoneOn_id.mul <;> grind [rpowIntegrand₀₁_monotoneOn, rpowIntegrand₀₁_nonneg]

/--
lemma `integrableOn_rpowIntegrand₁₂` / 引理 `integrableOn_rpowIntegrand₁₂`

English:
lemma integrableOn_rpowIntegrand₁₂
  given: (hp : p in Ioo 1 2) (hx : 0 <= x)
  proof: by
  have hmain : (rpowIntegrand₁₂ p · x)
      =ᵐ[volume.restrict (Ioi 0)] (x * rpowIntegrand₀₁ (p-1) · x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    rw [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hx ha]
  rw [integrableOn_congr_fun_ae hmain]
  refine Integrable.const_mul ?_ _
  exact integrableOn_rpowIntegrand₀₁_Ioi (by grind) hx

中文:
引理 integrableOn_rpow整数egrand₁₂
  条件: (hp : p in 开区间 1 2) (hx : 0 <= x)
  证明: by
  have hmain : (rpowIntegrand₁₂ p · x)
      =ᵐ[volume.restrict (Ioi 0)] (x * rpowIntegrand₀₁ (p-1) · x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    rw [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hx ha]
  rw [integrableOn_congr_fun_ae hmain]
  refine Integrable.const_mul ?_ _
  exact integrableOn_rpowIntegrand₀₁_Ioi (by grind) hx

Depends on / 依赖: Integrable, Integrable.const_mul, ae_restrict_mem, const_mul, filter_upwards, integrableOn_congr_fun_ae, measurableSet_Ioi, restrict, volume, volume.restrict
-/
lemma integrableOn_rpowIntegrand₁₂ (hp : p in Ioo 1 2) (hx : 0 <= x) :
    IntegrableOn (rpowIntegrand₁₂ p · x) (Ioi 0) := by
  have hmain : (rpowIntegrand₁₂ p · x)
      =ᵐ[volume.restrict (Ioi 0)] (x * rpowIntegrand₀₁ (p-1) · x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    rw [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hx ha]
  rw [integrableOn_congr_fun_ae hmain]
  refine Integrable.const_mul ?_ _
  exact integrableOn_rpowIntegrand₀₁_Ioi (by grind) hx

/--
lemma `rpow_eq_const_mul_integral_rpowIntegrand₁₂` / 引理 `rpow_eq_const_mul_integral_rpowIntegrand₁₂`

English:
lemma rpow_eq_const_mul_integral_rpowIntegrand₁₂
  given: (hp : p in Ioo 1 2) (hx : 0 <= x)
  proof: by
  have hmain : (rpowIntegrand₁₂ p · x)
      =ᵐ[volume.restrict (Ioi 0)] (x * rpowIntegrand₀₁ (p-1) · x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    rw [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hx ha]
  rw [integral_congr_ae hmain]; rw [integral_const_mul_of_integrable
      (integrableOn_rpowIntegrand₀₁_Ioi (by grind) hx)]
  have h₁ : x ^ p = x * x ^ (p - 1) := by
    rw [mul_comm]; rw [← rpow_add_one' hx (by grind)]
    simp
  rw [h₁]; rw [rpow_eq_const_mul_integral (by grind) hx]
  grind

中文:
引理 rpow_eq_const_mul_integral_rpow整数egrand₁₂
  条件: (hp : p in 开区间 1 2) (hx : 0 <= x)
  证明: by
  have hmain : (rpowIntegrand₁₂ p · x)
      =ᵐ[volume.restrict (Ioi 0)] (x * rpowIntegrand₀₁ (p-1) · x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    rw [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hx ha]
  rw [integral_congr_ae hmain]; rw [integral_const_mul_of_integrable
      (integrableOn_rpowIntegrand₀₁_Ioi (by grind) hx)]
  have h₁ : x ^ p = x * x ^ (p - 1) := by
    rw [mul_comm]; rw [← rpow_add_one' hx (by grind)]
    simp
  rw [h₁]; rw [rpow_eq_const_mul_integral (by grind) hx]
  grind

Depends on / 依赖: ae_restrict_mem, filter_upwards, integral_congr_ae, integral_const_mul_of_integrable, measurableSet_Ioi, mul_comm, restrict, rpow_add_one, rpow_eq_const_mul_integral, volume, volume.restrict
-/
lemma rpow_eq_const_mul_integral_rpowIntegrand₁₂ (hp : p in Ioo 1 2) (hx : 0 <= x) :
    x ^ p
      = (∫ t in Ioi 0, rpowIntegrand₀₁ (p - 1) t 1)⁻¹ * ∫ t in Ioi 0, rpowIntegrand₁₂ p t x := by
  have hmain : (rpowIntegrand₁₂ p · x)
      =ᵐ[volume.restrict (Ioi 0)] (x * rpowIntegrand₀₁ (p-1) · x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    rw [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ hx ha]
  rw [integral_congr_ae hmain]; rw [integral_const_mul_of_integrable
      (integrableOn_rpowIntegrand₀₁_Ioi (by grind) hx)]
  have h₁ : x ^ p = x * x ^ (p - 1) := by
    rw [mul_comm]; rw [← rpow_add_one' hx (by grind)]
    simp
  rw [h₁]; rw [rpow_eq_const_mul_integral (by grind) hx]
  grind

/--
lemma `exists_measure_rpow_eq_integral_rpowIntegrand₁₂` / 引理 `exists_measure_rpow_eq_integral_rpowIntegrand₁₂`

English:
lemma exists_measure_rpow_eq_integral_rpowIntegrand₁₂
  given: (hp : p in Ioo 1 2)
  proof: by
  let C : Real>=0 := .mk
(∫ t in Ioi 0, rpowIntegrand₀₁ (p - 1) t 1)⁻¹ by
      rw [inv_nonneg]
exact le_of_lt integral_rpowIntegrand₀₁_one_pos (by grind)
  let μ : Measure Real := C • volume
  refine ⟨μ, fun x hx => ⟨?_, ?_⟩⟩
  · unfold μ IntegrableOn
    rw [Measure.restrict_smul]
exact Integrable.smul_measure_nnreal integrableOn_rpowIntegrand₁₂ hp hx
  · rw [Measure.restrict_smul, integral_smul_nnreal_measure,
      rpow_eq_const_mul_integral_rpowIntegrand₁₂ hp hx]
    simp [C, NNReal.smul_def]

中文:
引理 存在_measure_rpow_eq_integral_rpow整数egrand₁₂
  条件: (hp : p in 开区间 1 2)
  证明: by
  let C : Real>=0 := .mk
(∫ t in Ioi 0, rpowIntegrand₀₁ (p - 1) t 1)⁻¹ by
      rw [inv_nonneg]
exact le_of_lt integral_rpowIntegrand₀₁_one_pos (by grind)
  let μ : Measure Real := C • volume
  refine ⟨μ, fun x hx => ⟨?_, ?_⟩⟩
  · unfold μ IntegrableOn
    rw [Measure.restrict_smul]
exact Integrable.smul_measure_nnreal integrableOn_rpowIntegrand₁₂ hp hx
  · rw [Measure.restrict_smul, integral_smul_nnreal_measure,
      rpow_eq_const_mul_integral_rpowIntegrand₁₂ hp hx]
    simp [C, NNReal.smul_def]

Depends on / 依赖: Integrable, Integrable.smul_measure_nnreal, IntegrableOn, Measure, Measure.restrict_smul, NNReal, NNReal.smul_def, integral_smul_nnreal_measure, inv_nonneg, le_of_lt, restrict_smul, smul_def, smul_measure_nnreal, volume
-/
lemma exists_measure_rpow_eq_integral_rpowIntegrand₁₂ (hp : p in Ioo 1 2) :
    exists μ : Measure Real, forall x in Ici 0,
      (IntegrableOn (fun t => rpowIntegrand₁₂ p t x) (Ioi 0) μ)
      ∧ x ^ p = ∫ t in Ioi 0, rpowIntegrand₁₂ p t x ∂μ := by
  let C : Real>=0 := .mk
(∫ t in Ioi 0, rpowIntegrand₀₁ (p - 1) t 1)⁻¹ by
      rw [inv_nonneg]
exact le_of_lt integral_rpowIntegrand₀₁_one_pos (by grind)
  let μ : Measure Real := C • volume
  refine ⟨μ, fun x hx => ⟨?_, ?_⟩⟩
  · unfold μ IntegrableOn
    rw [Measure.restrict_smul]
exact Integrable.smul_measure_nnreal integrableOn_rpowIntegrand₁₂ hp hx
  · rw [Measure.restrict_smul, integral_smul_nnreal_measure,
      rpow_eq_const_mul_integral_rpowIntegrand₁₂ hp hx]
    simp [C, NNReal.smul_def]

end OneTwo

end Real

namespace CFC
open Real

section NonUnitalCFC

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace Real A] [SMulCommClass Real A A]
  [IsScalarTower Real A A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A]
  [NonUnitalContinuousFunctionalCalculus Real A IsSelfAdjoint]

/--
lemma `cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one` / 引理 `cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one`

English:
lemma cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one
  statement: {p t : Real} (hp : p in Ioo 0 1) (ht : 0 < t)
  proof: by
  have hspec : quasispectrum Real a subseteq Ici 0 := by grind
  have h_mapsTo : MapsTo (t⁻¹ • · : Real -> Real) (Ici 0) (Ici 0) := by
    intro x hx
    simp only [mem_Ici, smul_eq_mul] at hx ⊢
    positivity
  calc _ = cfcₙ (fun x => t ^ ((p : Real) - 1) * (rpowIntegrand₀₁ p 1 (t⁻¹ • x))) a := by
          refine cfcₙ_congr ?_
          refine Set.EqOn.mono hspec (rpowIntegrand₀₁_eqOn_mul_rpowIntegrand₀₁_one ht)
    _ = t ^ ((p : Real) - 1) • cfcₙ (fun x => rpowIntegrand₀₁ p 1 (t⁻¹ • x)) a := by
          refine cfcₙ_smul (R := Real) (t ^ ((p : Real) - 1)) _ a ?_
          refine ContinuousOn.mono ?_ hspec
          have := continuousOn_rpowIntegrand₀₁_Ici hp zero_lt_one
          fun_prop
    _ = t ^ ((p : Real) - 1) • cfcₙ (rpowIntegrand₀₁ p 1) (t⁻¹ • a) := by
          congr! 1
          refine cfcₙ_comp_smul (R := Real) t⁻¹ (fun x => rpowIntegrand₀₁ p 1 x) a ?_
.mono exact continuousOn_rpowIntegrand₀₁_Ici hp zero_lt_one
            (h_mapsTo.mono_left hspec).image_subset

中文:
引理 cfcₙ_rpow整数egrand₀₁_eq_cfcₙ_rpow整数egrand₀₁_one
  结论: {p t : 实数} (hp : p in 开区间 0 1) (ht : 0 < t)
  证明: by
  have hspec : quasispectrum Real a subseteq Ici 0 := by grind
  have h_mapsTo : MapsTo (t⁻¹ • · : Real -> Real) (Ici 0) (Ici 0) := by
    intro x hx
    simp only [mem_Ici, smul_eq_mul] at hx ⊢
    positivity
  calc _ = cfcₙ (fun x => t ^ ((p : Real) - 1) * (rpowIntegrand₀₁ p 1 (t⁻¹ • x))) a := by
          refine cfcₙ_congr ?_
          refine Set.EqOn.mono hspec (rpowIntegrand₀₁_eqOn_mul_rpowIntegrand₀₁_one ht)
    _ = t ^ ((p : Real) - 1) • cfcₙ (fun x => rpowIntegrand₀₁ p 1 (t⁻¹ • x)) a := by
          refine cfcₙ_smul (R := Real) (t ^ ((p : Real) - 1)) _ a ?_
          refine ContinuousOn.mono ?_ hspec
          have := continuousOn_rpowIntegrand₀₁_Ici hp zero_lt_one
          fun_prop
    _ = t ^ ((p : Real) - 1) • cfcₙ (rpowIntegrand₀₁ p 1) (t⁻¹ • a) := by
          congr! 1
          refine cfcₙ_comp_smul (R := Real) t⁻¹ (fun x => rpowIntegrand₀₁ p 1 x) a ?_
.mono exact continuousOn_rpowIntegrand₀₁_Ici hp zero_lt_one
            (h_mapsTo.mono_left hspec).image_subset

Depends on / 依赖: MapsTo, Set.EqOn.mono, h_mapsTo, mem_Ici, quasispectrum, smul_eq_mul, subseteq
-/
lemma cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one {p t : Real} (hp : p in Ioo 0 1) (ht : 0 < t)
    (a : A) (ha : 0 <= a) :
    cfcₙ (rpowIntegrand₀₁ p t) a = t ^ (p - 1) • cfcₙ (rpowIntegrand₀₁ p 1) (t⁻¹ • a) := by
  have hspec : quasispectrum Real a subseteq Ici 0 := by grind
  have h_mapsTo : MapsTo (t⁻¹ • · : Real -> Real) (Ici 0) (Ici 0) := by
    intro x hx
    simp only [mem_Ici, smul_eq_mul] at hx ⊢
    positivity
  calc _ = cfcₙ (fun x => t ^ ((p : Real) - 1) * (rpowIntegrand₀₁ p 1 (t⁻¹ • x))) a := by
          refine cfcₙ_congr ?_
          refine Set.EqOn.mono hspec (rpowIntegrand₀₁_eqOn_mul_rpowIntegrand₀₁_one ht)
    _ = t ^ ((p : Real) - 1) • cfcₙ (fun x => rpowIntegrand₀₁ p 1 (t⁻¹ • x)) a := by
          refine cfcₙ_smul (R := Real) (t ^ ((p : Real) - 1)) _ a ?_
          refine ContinuousOn.mono ?_ hspec
          have := continuousOn_rpowIntegrand₀₁_Ici hp zero_lt_one
          fun_prop
    _ = t ^ ((p : Real) - 1) • cfcₙ (rpowIntegrand₀₁ p 1) (t⁻¹ • a) := by
          congr! 1
          refine cfcₙ_comp_smul (R := Real) t⁻¹ (fun x => rpowIntegrand₀₁ p 1 x) a ?_
.mono exact continuousOn_rpowIntegrand₀₁_Ici hp zero_lt_one
            (h_mapsTo.mono_left hspec).image_subset

variable (A) in
/--
lemma `exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁` / 引理 `exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁`

English:
lemma exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁
  statement: [CompleteSpace A] {p : Real>=0}
  proof: by
  obtain ⟨μ, hμ⟩ := exists_measure_rpow_eq_integral_rpowIntegrand₀₁ hp
  refine ⟨μ, fun a (ha : 0 <= a) => ?_⟩
  nontriviality A
  have p_pos : 0 < (p : Real) := by exact_mod_cast hp.1
  let f t := rpowIntegrand₀₁ p t
  let maxr := sSup (quasispectrum Real a)
  have maxr_nonneg : 0 <= maxr :=
    le_csSup_of_le (b := 0) (IsCompact.bddAbove (by grind)) (by simp) (by simp)
  let bound (t : Real) := ‖f t maxr‖
  have hf : ContinuousOn (Function.uncurry f) (Ioi (0 : Real) ×ˢ quasispectrum Real a) := by
    refine continuousOn_rpowIntegrand₀₁_uncurry hp (quasispectrum Real a) ?_
    grind
  have hbound : forallᵐ t ∂μ.restrict (Ioi 0), forall z in quasispectrum Real a, ‖f t z‖ <= bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have hz' : 0 <= z := by grind
    unfold bound f
    rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg p_pos (le_of_lt ht) hz')]; rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg p_pos (le_of_lt ht) maxr_nonneg)]
    refine rpowIntegrand₀₁_monotoneOn hp (le_of_lt ht) hz' maxr_nonneg ?_
    exact le_csSup (IsCompact.bddAbove (quasispectrum.isCompact _)) hz
  have hbound_finite_integral : HasFiniteIntegral bound (μ.restrict (Ioi 0)) := by
    rw [hasFiniteIntegral_norm_iff]
    exact (hμ maxr maxr_nonneg).1.2
  have hmapzero : forallᵐ (x : Real) ∂μ.restrict (Ioi 0), rpowIntegrand₀₁ p x 0 = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
    simp
  refine ⟨?integrable, ?integral⟩
  case integrable =>
    exact integrableOn_cfcₙ measurableSet_Ioi _ bound a hf hmapzero hbound hbound_finite_integral
  case integral => calc
    a ^ p = cfcₙ (fun r => ∫ t in Ioi 0, rpowIntegrand₀₁ p t r ∂μ) a := by
      rw [nnrpow_eq_cfcₙ_real _ _]
      exact cfcₙ_congr fun r _ => (hμ r (by grind)).2
    _ = _ := cfcₙ_setIntegral measurableSet_Ioi _ bound a hf hmapzero hbound
                hbound_finite_integral ha.isSelfAdjoint

中文:
引理 存在_measure_nnrpow_eq_integral_cfcₙ_rpow整数egrand₀₁
  结论: [完备空间 A] {p : 实数>=0}
  证明: by
  obtain ⟨μ, hμ⟩ := exists_measure_rpow_eq_integral_rpowIntegrand₀₁ hp
  refine ⟨μ, fun a (ha : 0 <= a) => ?_⟩
  nontriviality A
  have p_pos : 0 < (p : Real) := by exact_mod_cast hp.1
  let f t := rpowIntegrand₀₁ p t
  let maxr := sSup (quasispectrum Real a)
  have maxr_nonneg : 0 <= maxr :=
    le_csSup_of_le (b := 0) (IsCompact.bddAbove (by grind)) (by simp) (by simp)
  let bound (t : Real) := ‖f t maxr‖
  have hf : ContinuousOn (Function.uncurry f) (Ioi (0 : Real) ×ˢ quasispectrum Real a) := by
    refine continuousOn_rpowIntegrand₀₁_uncurry hp (quasispectrum Real a) ?_
    grind
  have hbound : forallᵐ t ∂μ.restrict (Ioi 0), forall z in quasispectrum Real a, ‖f t z‖ <= bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have hz' : 0 <= z := by grind
    unfold bound f
    rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg p_pos (le_of_lt ht) hz')]; rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg p_pos (le_of_lt ht) maxr_nonneg)]
    refine rpowIntegrand₀₁_monotoneOn hp (le_of_lt ht) hz' maxr_nonneg ?_
    exact le_csSup (IsCompact.bddAbove (quasispectrum.isCompact _)) hz
  have hbound_finite_integral : HasFiniteIntegral bound (μ.restrict (Ioi 0)) := by
    rw [hasFiniteIntegral_norm_iff]
    exact (hμ maxr maxr_nonneg).1.2
  have hmapzero : forallᵐ (x : Real) ∂μ.restrict (Ioi 0), rpowIntegrand₀₁ p x 0 = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
    simp
  refine ⟨?integrable, ?integral⟩
  case integrable =>
    exact integrableOn_cfcₙ measurableSet_Ioi _ bound a hf hmapzero hbound hbound_finite_integral
  case integral => calc
    a ^ p = cfcₙ (fun r => ∫ t in Ioi 0, rpowIntegrand₀₁ p t r ∂μ) a := by
      rw [nnrpow_eq_cfcₙ_real _ _]
      exact cfcₙ_congr fun r _ => (hμ r (by grind)).2
    _ = _ := cfcₙ_setIntegral measurableSet_Ioi _ bound a hf hmapzero hbound
                hbound_finite_integral ha.isSelfAdjoint

Depends on / 依赖: ContinuousOn, Function, Function.uncurry, IsCompact, IsCompact.bddAbove, bddAbove, continuo, le_csSup_of_le, maxr_nonneg, nontriviality, p_pos, quasispectrum, uncurry
-/
lemma exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ [CompleteSpace A] {p : Real>=0}
    (hp : p in Ioo 0 1) :
    exists μ : Measure Real, forall a in Ici (0 : A),
      (IntegrableOn (fun t => cfcₙ (rpowIntegrand₀₁ p t) a) (Ioi 0) μ)
      ∧ a ^ p = ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) a ∂μ := by
  obtain ⟨μ, hμ⟩ := exists_measure_rpow_eq_integral_rpowIntegrand₀₁ hp
  refine ⟨μ, fun a (ha : 0 <= a) => ?_⟩
  nontriviality A
  have p_pos : 0 < (p : Real) := by exact_mod_cast hp.1
  let f t := rpowIntegrand₀₁ p t
  let maxr := sSup (quasispectrum Real a)
  have maxr_nonneg : 0 <= maxr :=
    le_csSup_of_le (b := 0) (IsCompact.bddAbove (by grind)) (by simp) (by simp)
  let bound (t : Real) := ‖f t maxr‖
  have hf : ContinuousOn (Function.uncurry f) (Ioi (0 : Real) ×ˢ quasispectrum Real a) := by
    refine continuousOn_rpowIntegrand₀₁_uncurry hp (quasispectrum Real a) ?_
    grind
  have hbound : forallᵐ t ∂μ.restrict (Ioi 0), forall z in quasispectrum Real a, ‖f t z‖ <= bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have hz' : 0 <= z := by grind
    unfold bound f
    rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg p_pos (le_of_lt ht) hz')]; rw [Real.norm_of_nonneg (rpowIntegrand₀₁_nonneg p_pos (le_of_lt ht) maxr_nonneg)]
    refine rpowIntegrand₀₁_monotoneOn hp (le_of_lt ht) hz' maxr_nonneg ?_
    exact le_csSup (IsCompact.bddAbove (quasispectrum.isCompact _)) hz
  have hbound_finite_integral : HasFiniteIntegral bound (μ.restrict (Ioi 0)) := by
    rw [hasFiniteIntegral_norm_iff]
    exact (hμ maxr maxr_nonneg).1.2
  have hmapzero : forallᵐ (x : Real) ∂μ.restrict (Ioi 0), rpowIntegrand₀₁ p x 0 = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi]
    simp
  refine ⟨?integrable, ?integral⟩
  case integrable =>
    exact integrableOn_cfcₙ measurableSet_Ioi _ bound a hf hmapzero hbound hbound_finite_integral
  case integral => calc
    a ^ p = cfcₙ (fun r => ∫ t in Ioi 0, rpowIntegrand₀₁ p t r ∂μ) a := by
      rw [nnrpow_eq_cfcₙ_real _ _]
      exact cfcₙ_congr fun r _ => (hμ r (by grind)).2
    _ = _ := cfcₙ_setIntegral measurableSet_Ioi _ bound a hf hmapzero hbound
                hbound_finite_integral ha.isSelfAdjoint

variable (A) in
/--
lemma `exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂` / 引理 `exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂`

English:
lemma exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂
  statement: [CompleteSpace A] {p : Real>=0}
  proof: by
  obtain ⟨μ, hμ⟩ := exists_measure_rpow_eq_integral_rpowIntegrand₁₂ hp
  refine ⟨μ, fun a (ha : 0 <= a) => ?_⟩
  have hpcoe : (p : Real) in Ioo 1 2 := by exact_mod_cast hp
  let f t := rpowIntegrand₁₂ p t
  let maxr := sSup (quasispectrum Real a)
  have maxr_nonneg : 0 <= maxr :=
    le_csSup_of_le (b := 0) (IsCompact.bddAbove (quasispectrum.isCompact _)) (by simp) le_rfl
  let bound (t : Real) := ‖f t maxr‖
  have hf : ContinuousOn (Function.uncurry f) (Ioi (0 : Real) ×ˢ quasispectrum Real a) :=
    continuousOn_rpowIntegrand₁₂_uncurry hpcoe.1 (quasispectrum Real a) (by grind)
  have hbound : forallᵐ t ∂μ.restrict (Ioi 0), forall z in quasispectrum Real a, ‖f t z‖ <= bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have hz' : 0 <= z := by grind
    unfold bound f
    rw [Real.norm_of_nonneg (rpowIntegrand₁₂_nonneg (by grind) (by grind) hz')]; rw [Real.norm_of_nonneg (rpowIntegrand₁₂_nonneg (by grind) (by grind) maxr_nonneg)]
    refine monotoneOn_rpowIntegrand₁₂ (by grind) (by grind) hz' maxr_nonneg ?_
    exact le_csSup (IsCompact.bddAbove (quasispectrum.isCompact _)) hz
  have hbound_finite_integral : HasFiniteIntegral bound (μ.restrict (Ioi 0)) := by
    rw [hasFiniteIntegral_norm_iff]
    exact (hμ maxr maxr_nonneg).1.2
  have hmapzero : forallᵐ (x : Real) ∂μ.restrict (Ioi 0), rpowIntegrand₁₂ p x 0 = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp [rpowIntegrand₁₂_zero ht]
  refine ⟨?integrable, ?integral⟩
  case integrable =>
    exact integrableOn_cfcₙ measurableSet_Ioi _ bound a hf hmapzero hbound hbound_finite_integral
  case integral => calc
      a ^ p = cfcₙ (fun x => NNReal.nnrpow x p) a := by
        rw [CFC.nnrpow_def]
      _ = cfcₙ (fun r => ∫ t in Ioi 0, rpowIntegrand₁₂ p t r ∂μ) a := by
        rw [cfcₙ_nnreal_eq_real ..]
        refine cfcₙ_congr fun r hr => ?_
        have hr' : 0 <= r := by grind
        simp only [sup_of_le_left hr', NNReal.nnrpow_def, NNReal.coe_rpow, coe_toNNReal']
        exact (hμ r hr').2
      _ = ∫ t in Ioi 0, cfcₙ (rpowIntegrand₁₂ p t) a ∂μ :=
        cfcₙ_setIntegral measurableSet_Ioi _ bound a hf hmapzero hbound
          hbound_finite_integral ha.isSelfAdjoint

中文:
引理 存在_measure_nnrpow_eq_integral_cfcₙ_rpow整数egrand₁₂
  结论: [完备空间 A] {p : 实数>=0}
  证明: by
  obtain ⟨μ, hμ⟩ := exists_measure_rpow_eq_integral_rpowIntegrand₁₂ hp
  refine ⟨μ, fun a (ha : 0 <= a) => ?_⟩
  have hpcoe : (p : Real) in Ioo 1 2 := by exact_mod_cast hp
  let f t := rpowIntegrand₁₂ p t
  let maxr := sSup (quasispectrum Real a)
  have maxr_nonneg : 0 <= maxr :=
    le_csSup_of_le (b := 0) (IsCompact.bddAbove (quasispectrum.isCompact _)) (by simp) le_rfl
  let bound (t : Real) := ‖f t maxr‖
  have hf : ContinuousOn (Function.uncurry f) (Ioi (0 : Real) ×ˢ quasispectrum Real a) :=
    continuousOn_rpowIntegrand₁₂_uncurry hpcoe.1 (quasispectrum Real a) (by grind)
  have hbound : forallᵐ t ∂μ.restrict (Ioi 0), forall z in quasispectrum Real a, ‖f t z‖ <= bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have hz' : 0 <= z := by grind
    unfold bound f
    rw [Real.norm_of_nonneg (rpowIntegrand₁₂_nonneg (by grind) (by grind) hz')]; rw [Real.norm_of_nonneg (rpowIntegrand₁₂_nonneg (by grind) (by grind) maxr_nonneg)]
    refine monotoneOn_rpowIntegrand₁₂ (by grind) (by grind) hz' maxr_nonneg ?_
    exact le_csSup (IsCompact.bddAbove (quasispectrum.isCompact _)) hz
  have hbound_finite_integral : HasFiniteIntegral bound (μ.restrict (Ioi 0)) := by
    rw [hasFiniteIntegral_norm_iff]
    exact (hμ maxr maxr_nonneg).1.2
  have hmapzero : forallᵐ (x : Real) ∂μ.restrict (Ioi 0), rpowIntegrand₁₂ p x 0 = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp [rpowIntegrand₁₂_zero ht]
  refine ⟨?integrable, ?integral⟩
  case integrable =>
    exact integrableOn_cfcₙ measurableSet_Ioi _ bound a hf hmapzero hbound hbound_finite_integral
  case integral => calc
      a ^ p = cfcₙ (fun x => NNReal.nnrpow x p) a := by
        rw [CFC.nnrpow_def]
      _ = cfcₙ (fun r => ∫ t in Ioi 0, rpowIntegrand₁₂ p t r ∂μ) a := by
        rw [cfcₙ_nnreal_eq_real ..]
        refine cfcₙ_congr fun r hr => ?_
        have hr' : 0 <= r := by grind
        simp only [sup_of_le_left hr', NNReal.nnrpow_def, NNReal.coe_rpow, coe_toNNReal']
        exact (hμ r hr').2
      _ = ∫ t in Ioi 0, cfcₙ (rpowIntegrand₁₂ p t) a ∂μ :=
        cfcₙ_setIntegral measurableSet_Ioi _ bound a hf hmapzero hbound
          hbound_finite_integral ha.isSelfAdjoint

Depends on / 依赖: ContinuousOn, Function, Function.uncurry, IsCompact, IsCompact.bddAbove, bddAbove, continuousOn_rp, isCompact, le_csSup_of_le, le_rfl, maxr_nonneg, quasispectrum, quasispectrum.isCompact, uncurry
-/
lemma exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂ [CompleteSpace A] {p : Real>=0}
    (hp : p in Ioo 1 2) :
    exists μ : Measure Real, forall a in Ici (0 : A),
      (IntegrableOn (fun t => cfcₙ (rpowIntegrand₁₂ p t) a) (Ioi 0) μ)
      ∧ a ^ p = ∫ t in Ioi 0, cfcₙ (rpowIntegrand₁₂ p t) a ∂μ := by
  obtain ⟨μ, hμ⟩ := exists_measure_rpow_eq_integral_rpowIntegrand₁₂ hp
  refine ⟨μ, fun a (ha : 0 <= a) => ?_⟩
  have hpcoe : (p : Real) in Ioo 1 2 := by exact_mod_cast hp
  let f t := rpowIntegrand₁₂ p t
  let maxr := sSup (quasispectrum Real a)
  have maxr_nonneg : 0 <= maxr :=
    le_csSup_of_le (b := 0) (IsCompact.bddAbove (quasispectrum.isCompact _)) (by simp) le_rfl
  let bound (t : Real) := ‖f t maxr‖
  have hf : ContinuousOn (Function.uncurry f) (Ioi (0 : Real) ×ˢ quasispectrum Real a) :=
    continuousOn_rpowIntegrand₁₂_uncurry hpcoe.1 (quasispectrum Real a) (by grind)
  have hbound : forallᵐ t ∂μ.restrict (Ioi 0), forall z in quasispectrum Real a, ‖f t z‖ <= bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have hz' : 0 <= z := by grind
    unfold bound f
    rw [Real.norm_of_nonneg (rpowIntegrand₁₂_nonneg (by grind) (by grind) hz')]; rw [Real.norm_of_nonneg (rpowIntegrand₁₂_nonneg (by grind) (by grind) maxr_nonneg)]
    refine monotoneOn_rpowIntegrand₁₂ (by grind) (by grind) hz' maxr_nonneg ?_
    exact le_csSup (IsCompact.bddAbove (quasispectrum.isCompact _)) hz
  have hbound_finite_integral : HasFiniteIntegral bound (μ.restrict (Ioi 0)) := by
    rw [hasFiniteIntegral_norm_iff]
    exact (hμ maxr maxr_nonneg).1.2
  have hmapzero : forallᵐ (x : Real) ∂μ.restrict (Ioi 0), rpowIntegrand₁₂ p x 0 = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp [rpowIntegrand₁₂_zero ht]
  refine ⟨?integrable, ?integral⟩
  case integrable =>
    exact integrableOn_cfcₙ measurableSet_Ioi _ bound a hf hmapzero hbound hbound_finite_integral
  case integral => calc
      a ^ p = cfcₙ (fun x => NNReal.nnrpow x p) a := by
        rw [CFC.nnrpow_def]
      _ = cfcₙ (fun r => ∫ t in Ioi 0, rpowIntegrand₁₂ p t r ∂μ) a := by
        rw [cfcₙ_nnreal_eq_real ..]
        refine cfcₙ_congr fun r hr => ?_
        have hr' : 0 <= r := by grind
        simp only [sup_of_le_left hr', NNReal.nnrpow_def, NNReal.coe_rpow, coe_toNNReal']
        exact (hμ r hr').2
      _ = ∫ t in Ioi 0, cfcₙ (rpowIntegrand₁₂ p t) a ∂μ :=
        cfcₙ_setIntegral measurableSet_Ioi _ bound a hf hmapzero hbound
          hbound_finite_integral ha.isSelfAdjoint

end NonUnitalCFC

section UnitalCStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/--
lemma `concaveOn_cfc_rpowIntegrand₀₁` / 引理 `concaveOn_cfc_rpowIntegrand₀₁`

English:
lemma concaveOn_cfc_rpowIntegrand₀₁
  given: {p t : Real} (hp : p in Ioo 0 1) (ht : 0 < t)
  proof: by
  have h₁ : (Ici (0 : A)).EqOn (cfc (rpowIntegrand₀₁ p t))
      (fun x : A =>
        algebraMap Real A (t ^ (p - 1)) - t ^ p • Ring.inverse (algebraMap Real A t + x)) := by
    intro x hx
    rw [rpowIntegrand₀₁_eq_sub (by grind) ht]
    have hg : ContinuousOn (fun z : Real => (t + z)⁻¹) (spectrum Real x) := by
      fun_prop (disch := grind -abstractProof)
    have hf : ContinuousOn (fun z : Real => (1 + z)) (spectrum Real x) := by fun_prop
    have hspectrum : forall r in spectrum Real x, t + r != 0 := by grind
    have := cfc_sub (fun _ : Real => t ^ (p - 1)) (fun z : Real => t ^ p * (t + z)⁻¹) x
    rw [this]; rw [cfc_const ..]; rw [cfc_const_mul ..]; rw [cfc_inv _ _ hspectrum ..]; rw [cfc_const_add ..]; rw [cfc_id' ..]
  refine ConcaveOn.congr ?_ h₁.symm
  refine ConcaveOn.sub (concaveOn_const _ (convex_Ici 0)) ?_
exact ConvexOn.smul (by positivity) CStarAlgebra.convexOn_ringInverse_algebraMap_add ht

中文:
引理 concaveOn_cfc_rpow整数egrand₀₁
  条件: {p t : 实数} (hp : p in 开区间 0 1) (ht : 0 < t)
  证明: by
  have h₁ : (Ici (0 : A)).EqOn (cfc (rpowIntegrand₀₁ p t))
      (fun x : A =>
        algebraMap Real A (t ^ (p - 1)) - t ^ p • Ring.inverse (algebraMap Real A t + x)) := by
    intro x hx
    rw [rpowIntegrand₀₁_eq_sub (by grind) ht]
    have hg : ContinuousOn (fun z : Real => (t + z)⁻¹) (spectrum Real x) := by
      fun_prop (disch := grind -abstractProof)
    have hf : ContinuousOn (fun z : Real => (1 + z)) (spectrum Real x) := by fun_prop
    have hspectrum : forall r in spectrum Real x, t + r != 0 := by grind
    have := cfc_sub (fun _ : Real => t ^ (p - 1)) (fun z : Real => t ^ p * (t + z)⁻¹) x
    rw [this]; rw [cfc_const ..]; rw [cfc_const_mul ..]; rw [cfc_inv _ _ hspectrum ..]; rw [cfc_const_add ..]; rw [cfc_id' ..]
  refine ConcaveOn.congr ?_ h₁.symm
  refine ConcaveOn.sub (concaveOn_const _ (convex_Ici 0)) ?_
exact ConvexOn.smul (by positivity) CStarAlgebra.convexOn_ringInverse_algebraMap_add ht

Depends on / 依赖: ContinuousOn, Ring.inverse, abstractProof, algebraMap, cfc_sub, fun_prop, hspectrum, inverse, spectrum
-/
lemma concaveOn_cfc_rpowIntegrand₀₁ {p t : Real} (hp : p in Ioo 0 1) (ht : 0 < t) :
    ConcaveOn Real (Ici (0 : A)) (cfc (rpowIntegrand₀₁ p t)) := by
  have h₁ : (Ici (0 : A)).EqOn (cfc (rpowIntegrand₀₁ p t))
      (fun x : A =>
        algebraMap Real A (t ^ (p - 1)) - t ^ p • Ring.inverse (algebraMap Real A t + x)) := by
    intro x hx
    rw [rpowIntegrand₀₁_eq_sub (by grind) ht]
    have hg : ContinuousOn (fun z : Real => (t + z)⁻¹) (spectrum Real x) := by
      fun_prop (disch := grind -abstractProof)
    have hf : ContinuousOn (fun z : Real => (1 + z)) (spectrum Real x) := by fun_prop
    have hspectrum : forall r in spectrum Real x, t + r != 0 := by grind
    have := cfc_sub (fun _ : Real => t ^ (p - 1)) (fun z : Real => t ^ p * (t + z)⁻¹) x
    rw [this]; rw [cfc_const ..]; rw [cfc_const_mul ..]; rw [cfc_inv _ _ hspectrum ..]; rw [cfc_const_add ..]; rw [cfc_id' ..]
  refine ConcaveOn.congr ?_ h₁.symm
  refine ConcaveOn.sub (concaveOn_const _ (convex_Ici 0)) ?_
exact ConvexOn.smul (by positivity) CStarAlgebra.convexOn_ringInverse_algebraMap_add ht

end UnitalCStarAlgebra

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/--
lemma `monotoneOn_cfcₙ_rpowIntegrand₀₁` / 引理 `monotoneOn_cfcₙ_rpowIntegrand₀₁`

English:
lemma monotoneOn_cfcₙ_rpowIntegrand₀₁
  given: {p : Real} {t : Real} (hp : p in Ioo 0 1) (ht : 0 < t)
  proof: by
  intro a (ha : 0 <= a) b (hb : 0 <= b) hab
  calc
    _ = t ^ ((p : Real) - 1) • cfcₙ (rpowIntegrand₀₁ p 1) (t⁻¹ • a) := by
      rw [cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one hp ht a ha]
    _ <= t ^ ((p : Real) - 1) • cfcₙ (rpowIntegrand₀₁ p 1) (t⁻¹ • b) := by
      gcongr
      unfold rpowIntegrand₀₁
      simp only [Real.one_rpow, one_mul, inv_one]
      refine CFC.monotoneOn_one_sub_one_add_inv_real
        (?_ : 0 <= t⁻¹ • a) (?_ : 0 <= t⁻¹ • b) (by gcongr)
      all_goals positivity
    _ = cfcₙ (rpowIntegrand₀₁ p t) b := by
      rw [cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one hp ht b hb]

中文:
引理 monotoneOn_cfcₙ_rpow整数egrand₀₁
  条件: {p : 实数} {t : 实数} (hp : p in 开区间 0 1) (ht : 0 < t)
  证明: by
  intro a (ha : 0 <= a) b (hb : 0 <= b) hab
  calc
    _ = t ^ ((p : Real) - 1) • cfcₙ (rpowIntegrand₀₁ p 1) (t⁻¹ • a) := by
      rw [cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one hp ht a ha]
    _ <= t ^ ((p : Real) - 1) • cfcₙ (rpowIntegrand₀₁ p 1) (t⁻¹ • b) := by
      gcongr
      unfold rpowIntegrand₀₁
      simp only [Real.one_rpow, one_mul, inv_one]
      refine CFC.monotoneOn_one_sub_one_add_inv_real
        (?_ : 0 <= t⁻¹ • a) (?_ : 0 <= t⁻¹ • b) (by gcongr)
      all_goals positivity
    _ = cfcₙ (rpowIntegrand₀₁ p t) b := by
      rw [cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one hp ht b hb]

Depends on / 依赖: CFC.monotoneOn_one_sub_one_add_inv_real, Real.one_rpow, all_goals, inv_one, monotoneOn_one_sub_one_add_inv_real, one_mul, one_rpow
-/
lemma monotoneOn_cfcₙ_rpowIntegrand₀₁ {p : Real} {t : Real} (hp : p in Ioo 0 1) (ht : 0 < t) :
    MonotoneOn (cfcₙ (rpowIntegrand₀₁ p t)) (Ici (0 : A)) := by
  intro a (ha : 0 <= a) b (hb : 0 <= b) hab
  calc
    _ = t ^ ((p : Real) - 1) • cfcₙ (rpowIntegrand₀₁ p 1) (t⁻¹ • a) := by
      rw [cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one hp ht a ha]
    _ <= t ^ ((p : Real) - 1) • cfcₙ (rpowIntegrand₀₁ p 1) (t⁻¹ • b) := by
      gcongr
      unfold rpowIntegrand₀₁
      simp only [Real.one_rpow, one_mul, inv_one]
      refine CFC.monotoneOn_one_sub_one_add_inv_real
        (?_ : 0 <= t⁻¹ • a) (?_ : 0 <= t⁻¹ • b) (by gcongr)
      all_goals positivity
    _ = cfcₙ (rpowIntegrand₀₁ p t) b := by
      rw [cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one hp ht b hb]

open CStarAlgebra in
/--
lemma `concaveOn_cfcₙ_rpowIntegrand₀₁` / 引理 `concaveOn_cfcₙ_rpowIntegrand₀₁`

English:
lemma concaveOn_cfcₙ_rpowIntegrand₀₁
  given: {p : Real} {t : Real} (hp : p in Ioo 0 1) (ht : 0 < t)
  proof: by
  apply concaveOn_cfcₙ_of_concaveOn_cfc
  refine ConcaveOn.subset (concaveOn_cfc_rpowIntegrand₀₁ hp ht) inr_map_Ici_zero ?_
  exact Convex.linear_image (convex_Ici _) (Unitization.inrHom Real Complex A)

中文:
引理 concaveOn_cfcₙ_rpow整数egrand₀₁
  条件: {p : 实数} {t : 实数} (hp : p in 开区间 0 1) (ht : 0 < t)
  证明: by
  apply concaveOn_cfcₙ_of_concaveOn_cfc
  refine ConcaveOn.subset (concaveOn_cfc_rpowIntegrand₀₁ hp ht) inr_map_Ici_zero ?_
  exact Convex.linear_image (convex_Ici _) (Unitization.inrHom Real Complex A)

Depends on / 依赖: CochainComplex, CochainComplex.isZero_of_isStrictlyLE, ConcaveOn, ConcaveOn.subset, Convex, Convex.linear_image, Int.exists_eq_neg_ofNat, IsZero, IsZero.projective, Projective, Projective.of_iso, R.cochainComplexXIso, Unitization, Unitization.inrHom, cochainComplexXIso, convex_Ici, exists_eq_neg_ofNat, inrHom, inr_map_Ici_zero, isZero_of_isStrictlyLE
-/
lemma concaveOn_cfcₙ_rpowIntegrand₀₁ {p : Real} {t : Real} (hp : p in Ioo 0 1) (ht : 0 < t) :
    ConcaveOn Real (Ici (0 : A)) (cfcₙ (rpowIntegrand₀₁ p t)) := by
  apply concaveOn_cfcₙ_of_concaveOn_cfc
  refine ConcaveOn.subset (concaveOn_cfc_rpowIntegrand₀₁ hp ht) inr_map_Ici_zero ?_
  exact Convex.linear_image (convex_Ici _) (Unitization.inrHom Real Complex A)

end NonUnitalCStarAlgebra

end CFC
