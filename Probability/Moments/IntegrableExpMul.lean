/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Domain of the moment-generating function

For `X` a real random variable and `μ` a finite measure, the set
`{t | Integrable (fun ω ↦ exp (t * X ω)) μ}` is an interval containing zero. This is the set of
points for which the moment-generating function `mgf X μ t` is well defined.
We denote that set by `integrableExpSet X μ`.

We prove the integrability of other functions for `t` in the interior of that interval.

## Main definitions

* `ProbabilityTheory.IntegrableExpSet`: the interval of reals for which `exp (t * X)` is integrable.

## Main results

* `ProbabilityTheory.integrable_exp_mul_of_le_of_le`: if `exp (u * X)` is integrable for `u = a` and
  `u = b` then it is integrable on `[a, b]`.
* `ProbabilityTheory.convex_integrableExpSet`: `integrableExpSet X μ` is a convex set.
* `ProbabilityTheory.integrable_exp_mul_of_nonpos_of_ge`: if `exp (u * X)` is integrable for `u ≤ 0`
  then it is integrable on `[u, 0]`.
* `ProbabilityTheory.integrable_rpow_abs_mul_exp_of_mem_interior`: for `v` in the interior of the
  interval in which `exp (t * X)` is integrable, for all nonnegative `p : ℝ`,
  `|X| ^ p * exp (v * X)` is integrable.
* `ProbabilityTheory.memLp_of_mem_interior_integrableExpSet`: if 0 belongs to the interior of
  `integrableExpSet X μ`, then `X` is in `ℒp` for all finite `p`.

-/

@[expose] public section


open MeasureTheory Filter Finset Real

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω -> Real} {μ : Measure Ω} {t u v : Real}

section Interval

/--
lemma `integrable_exp_mul_of_le_of_le` / 引理 `integrable_exp_mul_of_le_of_le`

English:
lemma integrable_exp_mul_of_le_of_le
  statement: {a b : Real}
  proof: by
  refine Integrable.mono (ha.add hb) ?_ (ae_of_all _ fun ω => ?_)
  · by_cases hab : a = b
    · have ha_eq_t : a = t := le_antisymm hat (hab ▸ htb)
      rw [← ha_eq_t]
      exact ha.1
    · refine AEMeasurable.aestronglyMeasurable ?_
      refine measurable_exp.comp_aemeasurable (AEMeasurable.const_mul ?_ _)
      by_cases ha_zero : a = 0
      · refine aemeasurable_of_aemeasurable_exp_mul ?_ hb.1.aemeasurable
        rw [ha_zero] at hab
        exact Ne.symm hab
      · exact aemeasurable_of_aemeasurable_exp_mul ha_zero ha.1.aemeasurable
  · simp only [norm_eq_abs, abs_exp, Pi.add_apply]
    conv_rhs => rw [abs_of_nonneg (by positivity)]
    rcases le_total 0 (X ω) with h | h
    · calc exp (t * X ω)
      _ <= exp (b * X ω) := exp_le_exp.mpr (mul_le_mul_of_nonneg_right htb h)
      _ <= exp (a * X ω) + exp (b * X ω) := le_add_of_nonneg_left (exp_nonneg _)
    · calc exp (t * X ω)
      _ <= exp (a * X ω) := exp_le_exp.mpr (mul_le_mul_of_nonpos_right hat h)
      _ <= exp (a * X ω) + exp (b * X ω) := le_add_of_nonneg_right (exp_nonneg _)

中文:
引理 integrable_exp_mul_of_le_of_le
  结论: {a b : 实数}
  证明: by
  refine Integrable.mono (ha.add hb) ?_ (ae_of_all _ fun ω => ?_)
  · by_cases hab : a = b
    · have ha_eq_t : a = t := le_antisymm hat (hab ▸ htb)
      rw [← ha_eq_t]
      exact ha.1
    · refine AEMeasurable.aestronglyMeasurable ?_
      refine measurable_exp.comp_aemeasurable (AEMeasurable.const_mul ?_ _)
      by_cases ha_zero : a = 0
      · refine aemeasurable_of_aemeasurable_exp_mul ?_ hb.1.aemeasurable
        rw [ha_zero] at hab
        exact Ne.symm hab
      · exact aemeasurable_of_aemeasurable_exp_mul ha_zero ha.1.aemeasurable
  · simp only [norm_eq_abs, abs_exp, Pi.add_apply]
    conv_rhs => rw [abs_of_nonneg (by positivity)]
    rcases le_total 0 (X ω) with h | h
    · calc exp (t * X ω)
      _ <= exp (b * X ω) := exp_le_exp.mpr (mul_le_mul_of_nonneg_right htb h)
      _ <= exp (a * X ω) + exp (b * X ω) := le_add_of_nonneg_left (exp_nonneg _)
    · calc exp (t * X ω)
      _ <= exp (a * X ω) := exp_le_exp.mpr (mul_le_mul_of_nonpos_right hat h)
      _ <= exp (a * X ω) + exp (b * X ω) := le_add_of_nonneg_right (exp_nonneg _)

Depends on / 依赖: AEMeasurable, AEMeasurable.aestronglyMeasurable, AEMeasurable.const_mul, Integrable, Integrable.mono, Ne.symm, ae_of_all, aemeasurable, aemeasurable_of_aemeasurable_exp_mul, aestronglyMeasurable, comp_aemeasurable, const_mul, ha.add, ha_eq_t, ha_zero, le_antisymm, measurable_exp, measurable_exp.comp_aemeasurable
-/
lemma integrable_exp_mul_of_le_of_le {a b : Real}
    (ha : Integrable (fun ω => exp (a * X ω)) μ) (hb : Integrable (fun ω => exp (b * X ω)) μ)
    (hat : a <= t) (htb : t <= b) :
    Integrable (fun ω => exp (t * X ω)) μ := by
  refine Integrable.mono (ha.add hb) ?_ (ae_of_all _ fun ω => ?_)
  · by_cases hab : a = b
    · have ha_eq_t : a = t := le_antisymm hat (hab ▸ htb)
      rw [← ha_eq_t]
      exact ha.1
    · refine AEMeasurable.aestronglyMeasurable ?_
      refine measurable_exp.comp_aemeasurable (AEMeasurable.const_mul ?_ _)
      by_cases ha_zero : a = 0
      · refine aemeasurable_of_aemeasurable_exp_mul ?_ hb.1.aemeasurable
        rw [ha_zero] at hab
        exact Ne.symm hab
      · exact aemeasurable_of_aemeasurable_exp_mul ha_zero ha.1.aemeasurable
  · simp only [norm_eq_abs, abs_exp, Pi.add_apply]
    conv_rhs => rw [abs_of_nonneg (by positivity)]
    rcases le_total 0 (X ω) with h | h
    · calc exp (t * X ω)
      _ <= exp (b * X ω) := exp_le_exp.mpr (mul_le_mul_of_nonneg_right htb h)
      _ <= exp (a * X ω) + exp (b * X ω) := le_add_of_nonneg_left (exp_nonneg _)
    · calc exp (t * X ω)
      _ <= exp (a * X ω) := exp_le_exp.mpr (mul_le_mul_of_nonpos_right hat h)
      _ <= exp (a * X ω) + exp (b * X ω) := le_add_of_nonneg_right (exp_nonneg _)

/--
lemma `integrable_exp_mul_of_abs_le` / 引理 `integrable_exp_mul_of_abs_le`

English:
lemma integrable_exp_mul_of_abs_le
  proof: by
  refine integrable_exp_mul_of_le_of_le (a := -|u|) (b := |u|) ?_ ?_ ?_ ?_
  · rcases le_total 0 u with hu | hu
    · rwa [abs_of_nonneg hu]
    · simpa [abs_of_nonpos hu]
  · rcases le_total 0 u with hu | hu
    · rwa [abs_of_nonneg hu]
    · rwa [abs_of_nonpos hu]
  · rw [neg_le]
    exact (neg_le_abs t).trans htu
  · exact (le_abs_self t).trans htu

中文:
引理 integrable_exp_mul_of_abs_le
  证明: by
  refine integrable_exp_mul_of_le_of_le (a := -|u|) (b := |u|) ?_ ?_ ?_ ?_
  · rcases le_total 0 u with hu | hu
    · rwa [abs_of_nonneg hu]
    · simpa [abs_of_nonpos hu]
  · rcases le_total 0 u with hu | hu
    · rwa [abs_of_nonneg hu]
    · rwa [abs_of_nonpos hu]
  · rw [neg_le]
    exact (neg_le_abs t).trans htu
  · exact (le_abs_self t).trans htu

Depends on / 依赖: abs_of_nonneg, abs_of_nonpos, integrable_exp_mul_of_le_of_le, le_abs_self, le_total, neg_le, neg_le_abs
-/
lemma integrable_exp_mul_of_abs_le
    (hu_int_pos : Integrable (fun ω => exp (u * X ω)) μ)
    (hu_int_neg : Integrable (fun ω => exp (-u * X ω)) μ)
    (htu : |t| <= |u|) :
    Integrable (fun ω => exp (t * X ω)) μ := by
  refine integrable_exp_mul_of_le_of_le (a := -|u|) (b := |u|) ?_ ?_ ?_ ?_
  · rcases le_total 0 u with hu | hu
    · rwa [abs_of_nonneg hu]
    · simpa [abs_of_nonpos hu]
  · rcases le_total 0 u with hu | hu
    · rwa [abs_of_nonneg hu]
    · rwa [abs_of_nonpos hu]
  · rw [neg_le]
    exact (neg_le_abs t).trans htu
  · exact (le_abs_self t).trans htu

/--
lemma `integrable_exp_mul_of_nonneg_of_le` / 引理 `integrable_exp_mul_of_nonneg_of_le`

English:
lemma integrable_exp_mul_of_nonneg_of_le
  statement: [IsFiniteMeasure μ]
  proof: integrable_exp_mul_of_le_of_le (by simp) hu h_nonneg htu

中文:
引理 integrable_exp_mul_of_nonneg_of_le
  结论: [是有限测度 μ]
  证明: integrable_exp_mul_of_le_of_le (by simp) hu h_nonneg htu

Depends on / 依赖: h_nonneg, integrable_exp_mul_of_le_of_le
-/
lemma integrable_exp_mul_of_nonneg_of_le [IsFiniteMeasure μ]
    (hu : Integrable (fun ω => exp (u * X ω)) μ) (h_nonneg : 0 <= t) (htu : t <= u) :
    Integrable (fun ω => exp (t * X ω)) μ :=
  integrable_exp_mul_of_le_of_le (by simp) hu h_nonneg htu

/--
lemma `integrable_exp_mul_of_nonpos_of_ge` / 引理 `integrable_exp_mul_of_nonpos_of_ge`

English:
lemma integrable_exp_mul_of_nonpos_of_ge
  statement: [IsFiniteMeasure μ]
  proof: integrable_exp_mul_of_le_of_le hu (by simp) htu h_nonpos

中文:
引理 integrable_exp_mul_of_nonpos_of_ge
  结论: [是有限测度 μ]
  证明: integrable_exp_mul_of_le_of_le hu (by simp) htu h_nonpos

Depends on / 依赖: h_nonpos, integrable_exp_mul_of_le_of_le
-/
lemma integrable_exp_mul_of_nonpos_of_ge [IsFiniteMeasure μ]
    (hu : Integrable (fun ω => exp (u * X ω)) μ) (h_nonpos : t <= 0) (htu : u <= t) :
    Integrable (fun ω => exp (t * X ω)) μ :=
  integrable_exp_mul_of_le_of_le hu (by simp) htu h_nonpos

end Interval

section IntegrableExpSet

/--
Definition of `integrableExpSet` / `integrableExpSet` 的定义

English:
definition integrableExpSet
  signature: (X : Ω -> Real) (μ : Measure Ω)
  body: {t | Integrable (fun ω => exp (t * X ω)) μ}

中文:
定义 integrableExpSet
  签名: (X : Ω -> 实数) (μ : 测度 Ω)
  定义体: {t | Integrable (fun ω => exp (t * X ω)) μ}

Depends on / 依赖: Integrable
-/
def integrableExpSet (X : Ω -> Real) (μ : Measure Ω) : Set Real :=
  {t | Integrable (fun ω => exp (t * X ω)) μ}

/--
lemma `integrable_of_mem_integrableExpSet` / 引理 `integrable_of_mem_integrableExpSet`

English:
lemma integrable_of_mem_integrableExpSet
  given: (h : t in integrableExpSet X μ)
  proof: h

中文:
引理 integrable_of_mem_integrableExpSet
  条件: (h : t in integrableExpSet X μ)
  证明: h
-/
lemma integrable_of_mem_integrableExpSet (h : t in integrableExpSet X μ) :
    Integrable (fun ω => exp (t * X ω)) μ := h

/--
lemma `convex_integrableExpSet` / 引理 `convex_integrableExpSet`

English:
lemma convex_integrableExpSet
  statement: Convex Real (integrableExpSet X μ)
  proof: by
  rintro t₁ ht₁ t₂ ht₂ a b ha hb hab
  wlog! h_le : t₁ <= t₂
  · rw [add_comm] at hab ⊢
    exact this ht₂ ht₁ hb ha hab h_le.le
  refine integrable_exp_mul_of_le_of_le ht₁ ht₂ ?_ ?_
  · simp only [smul_eq_mul]
    calc t₁
    _ = a * t₁ + b * t₁ := by rw [← add_mul, hab, one_mul]
    _ <= a * t₁ + b * t₂ := by gcongr
  · simp only [smul_eq_mul]
    calc a * t₁ + b * t₂
    _ <= a * t₂ + b * t₂ := by gcongr
    _ = t₂ := by rw [← add_mul, hab, one_mul]

中文:
引理 convex_integrableExpSet
  结论: 凸 实数 (integrableExpSet X μ)
  证明: by
  rintro t₁ ht₁ t₂ ht₂ a b ha hb hab
  wlog! h_le : t₁ <= t₂
  · rw [add_comm] at hab ⊢
    exact this ht₂ ht₁ hb ha hab h_le.le
  refine integrable_exp_mul_of_le_of_le ht₁ ht₂ ?_ ?_
  · simp only [smul_eq_mul]
    calc t₁
    _ = a * t₁ + b * t₁ := by rw [← add_mul, hab, one_mul]
    _ <= a * t₁ + b * t₂ := by gcongr
  · simp only [smul_eq_mul]
    calc a * t₁ + b * t₂
    _ <= a * t₂ + b * t₂ := by gcongr
    _ = t₂ := by rw [← add_mul, hab, one_mul]

Depends on / 依赖: add_comm, add_mul, h_le, h_le.le, integrable_exp_mul_of_le_of_le, one_mul, smul_eq_mul
-/
lemma convex_integrableExpSet : Convex Real (integrableExpSet X μ) := by
  rintro t₁ ht₁ t₂ ht₂ a b ha hb hab
  wlog! h_le : t₁ <= t₂
  · rw [add_comm] at hab ⊢
    exact this ht₂ ht₁ hb ha hab h_le.le
  refine integrable_exp_mul_of_le_of_le ht₁ ht₂ ?_ ?_
  · simp only [smul_eq_mul]
    calc t₁
    _ = a * t₁ + b * t₁ := by rw [← add_mul, hab, one_mul]
    _ <= a * t₁ + b * t₂ := by gcongr
  · simp only [smul_eq_mul]
    calc a * t₁ + b * t₂
    _ <= a * t₂ + b * t₂ := by gcongr
    _ = t₂ := by rw [← add_mul, hab, one_mul]

end IntegrableExpSet

section FiniteMoments

/--
lemma `aemeasurable_of_integrable_exp_mul` / 引理 `aemeasurable_of_integrable_exp_mul`

English:
lemma aemeasurable_of_integrable_exp_mul
  statement: (huv : u != v)
  proof: by
  by_cases hu : u = 0
  · have hv : v != 0 := ne_of_ne_of_eq huv.symm hu
    exact aemeasurable_of_aemeasurable_exp_mul hv hv_int.aemeasurable
  · exact aemeasurable_of_aemeasurable_exp_mul hu hu_int.aemeasurable

中文:
引理 aemeasurable_of_integrable_exp_mul
  结论: (huv : u != v)
  证明: by
  by_cases hu : u = 0
  · have hv : v != 0 := ne_of_ne_of_eq huv.symm hu
    exact aemeasurable_of_aemeasurable_exp_mul hv hv_int.aemeasurable
  · exact aemeasurable_of_aemeasurable_exp_mul hu hu_int.aemeasurable

Depends on / 依赖: aemeasurable, aemeasurable_of_aemeasurable_exp_mul, hu_int, hu_int.aemeasurable, huv.symm, hv_int, hv_int.aemeasurable, ne_of_ne_of_eq
-/
lemma aemeasurable_of_integrable_exp_mul (huv : u != v)
    (hu_int : Integrable (fun ω => exp (u * X ω)) μ)
    (hv_int : Integrable (fun ω => exp (v * X ω)) μ) :
    AEMeasurable X μ := by
  by_cases hu : u = 0
  · have hv : v != 0 := ne_of_ne_of_eq huv.symm hu
    exact aemeasurable_of_aemeasurable_exp_mul hv hv_int.aemeasurable
  · exact aemeasurable_of_aemeasurable_exp_mul hu hu_int.aemeasurable

/--
lemma `integrable_exp_mul_abs_add` / 引理 `integrable_exp_mul_abs_add`

English:
lemma integrable_exp_mul_abs_add
  statement: (ht_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ)
  proof: by
  have h_int_add : Integrable (fun a => exp ((v + t) * X a) + exp ((v - t) * X a)) μ :=
ht_int_pos.add by simpa using ht_int_neg
  refine Integrable.mono h_int_add ?_ (ae_of_all _ fun ω => ?_)
  · by_cases ht : t = 0
    · simp only [ht, zero_mul, zero_add, add_zero] at ht_int_pos ⊢
      exact ht_int_pos.1
    have hX : AEMeasurable X μ := aemeasurable_of_integrable_exp_mul ?_ ht_int_pos ht_int_neg
    · fun_prop
    · rw [← sub_ne_zero]
      simp [ht]
  · simp only [norm_eq_abs, abs_exp]
    conv_rhs => rw [abs_of_nonneg (by positivity)]
    -- ⊢ exp (t * |X ω| + v * X ω) ≤ exp ((v + t) * X ω) + exp ((v - t) * X ω)
    rcases le_total 0 (X ω) with h_nonneg | h_nonpos
    · rw [abs_of_nonneg h_nonneg, ← add_mul, add_comm, le_add_iff_nonneg_right]
      positivity
    · rw [abs_of_nonpos h_nonpos, mul_neg, mul_comm, ← mul_neg, mul_comm, ← add_mul, add_comm,
        ← sub_eq_add_neg, le_add_iff_nonneg_left]
      positivity

中文:
引理 integrable_exp_mul_abs_add
  结论: (ht_int_pos : 可积 (fun ω => exp ((v + t) * X ω)) μ)
  证明: by
  have h_int_add : Integrable (fun a => exp ((v + t) * X a) + exp ((v - t) * X a)) μ :=
ht_int_pos.add by simpa using ht_int_neg
  refine Integrable.mono h_int_add ?_ (ae_of_all _ fun ω => ?_)
  · by_cases ht : t = 0
    · simp only [ht, zero_mul, zero_add, add_zero] at ht_int_pos ⊢
      exact ht_int_pos.1
    have hX : AEMeasurable X μ := aemeasurable_of_integrable_exp_mul ?_ ht_int_pos ht_int_neg
    · fun_prop
    · rw [← sub_ne_zero]
      simp [ht]
  · simp only [norm_eq_abs, abs_exp]
    conv_rhs => rw [abs_of_nonneg (by positivity)]
    -- ⊢ exp (t * |X ω| + v * X ω) ≤ exp ((v + t) * X ω) + exp ((v - t) * X ω)
    rcases le_total 0 (X ω) with h_nonneg | h_nonpos
    · rw [abs_of_nonneg h_nonneg, ← add_mul, add_comm, le_add_iff_nonneg_right]
      positivity
    · rw [abs_of_nonpos h_nonpos, mul_neg, mul_comm, ← mul_neg, mul_comm, ← add_mul, add_comm,
        ← sub_eq_add_neg, le_add_iff_nonneg_left]
      positivity

Depends on / 依赖: AEMeasurable, Integrable, Integrable.mono, IsStandardSmooth, Subsingleton, abs_exp, abs_of_nonneg, add_zero, ae_of_all, aemeasurable_of_integrable_exp_mul, conv_rhs, fun_prop, h_int_add, ht_int_neg, ht_int_pos, ht_int_pos.add, norm_eq_abs, sub_ne_zero, zero_add, zero_mul
-/
lemma integrable_exp_mul_abs_add (ht_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω => exp ((v - t) * X ω)) μ) :
    Integrable (fun ω => exp (t * |X ω| + v * X ω)) μ := by
  have h_int_add : Integrable (fun a => exp ((v + t) * X a) + exp ((v - t) * X a)) μ :=
ht_int_pos.add by simpa using ht_int_neg
  refine Integrable.mono h_int_add ?_ (ae_of_all _ fun ω => ?_)
  · by_cases ht : t = 0
    · simp only [ht, zero_mul, zero_add, add_zero] at ht_int_pos ⊢
      exact ht_int_pos.1
    have hX : AEMeasurable X μ := aemeasurable_of_integrable_exp_mul ?_ ht_int_pos ht_int_neg
    · fun_prop
    · rw [← sub_ne_zero]
      simp [ht]
  · simp only [norm_eq_abs, abs_exp]
    conv_rhs => rw [abs_of_nonneg (by positivity)]
    -- ⊢ exp (t * |X ω| + v * X ω) ≤ exp ((v + t) * X ω) + exp ((v - t) * X ω)
    rcases le_total 0 (X ω) with h_nonneg | h_nonpos
    · rw [abs_of_nonneg h_nonneg, ← add_mul, add_comm, le_add_iff_nonneg_right]
      positivity
    · rw [abs_of_nonpos h_nonpos, mul_neg, mul_comm, ← mul_neg, mul_comm, ← add_mul, add_comm,
        ← sub_eq_add_neg, le_add_iff_nonneg_left]
      positivity

/--
lemma `integrable_exp_mul_abs` / 引理 `integrable_exp_mul_abs`

English:
lemma integrable_exp_mul_abs
  statement: (ht_int_pos : Integrable (fun ω => exp (t * X ω)) μ)
  proof: by
  have h := integrable_exp_mul_abs_add (t := t) (μ := μ) (X := X) (v := 0) ?_ ?_
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

中文:
引理 integrable_exp_mul_abs
  结论: (ht_int_pos : 可积 (fun ω => exp (t * X ω)) μ)
  证明: by
  have h := integrable_exp_mul_abs_add (t := t) (μ := μ) (X := X) (v := 0) ?_ ?_
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

Depends on / 依赖: IsStandardSmoothOfRelativeDimension, Subsingleton, ht_int_neg, ht_int_pos, integrable_exp_mul_abs_add
-/
lemma integrable_exp_mul_abs (ht_int_pos : Integrable (fun ω => exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω => exp (-t * X ω)) μ) :
    Integrable (fun ω => exp (t * |X ω|)) μ := by
  have h := integrable_exp_mul_abs_add (t := t) (μ := μ) (X := X) (v := 0) ?_ ?_
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

/--
lemma `integrable_exp_abs_mul_abs_add` / 引理 `integrable_exp_abs_mul_abs_add`

English:
lemma integrable_exp_abs_mul_abs_add
  statement: (ht_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ)
  proof: by
  rcases le_total 0 t with ht_nonneg | ht_nonpos
  · simp_rw [abs_of_nonneg ht_nonneg]
    exact integrable_exp_mul_abs_add ht_int_pos ht_int_neg
  · simp_rw [abs_of_nonpos ht_nonpos]
    exact integrable_exp_mul_abs_add ht_int_neg (by simpa using ht_int_pos)

中文:
引理 integrable_exp_abs_mul_abs_add
  结论: (ht_int_pos : 可积 (fun ω => exp ((v + t) * X ω)) μ)
  证明: by
  rcases le_total 0 t with ht_nonneg | ht_nonpos
  · simp_rw [abs_of_nonneg ht_nonneg]
    exact integrable_exp_mul_abs_add ht_int_pos ht_int_neg
  · simp_rw [abs_of_nonpos ht_nonpos]
    exact integrable_exp_mul_abs_add ht_int_neg (by simpa using ht_int_pos)

Depends on / 依赖: abs_of_nonneg, abs_of_nonpos, ht_int_neg, ht_int_pos, ht_nonneg, ht_nonpos, integrable_exp_mul_abs_add, le_total, simp_rw
-/
lemma integrable_exp_abs_mul_abs_add (ht_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω => exp ((v - t) * X ω)) μ) :
    Integrable (fun ω => exp (|t| * |X ω| + v * X ω)) μ := by
  rcases le_total 0 t with ht_nonneg | ht_nonpos
  · simp_rw [abs_of_nonneg ht_nonneg]
    exact integrable_exp_mul_abs_add ht_int_pos ht_int_neg
  · simp_rw [abs_of_nonpos ht_nonpos]
    exact integrable_exp_mul_abs_add ht_int_neg (by simpa using ht_int_pos)

/--
lemma `integrable_exp_abs_mul_abs` / 引理 `integrable_exp_abs_mul_abs`

English:
lemma integrable_exp_abs_mul_abs
  statement: (ht_int_pos : Integrable (fun ω => exp (t * X ω)) μ)
  proof: by
  rcases le_total 0 t with ht_nonneg | ht_nonpos
  · simp_rw [abs_of_nonneg ht_nonneg]
    exact integrable_exp_mul_abs ht_int_pos ht_int_neg
  · simp_rw [abs_of_nonpos ht_nonpos]
    exact integrable_exp_mul_abs ht_int_neg (by simpa using ht_int_pos)

中文:
引理 integrable_exp_abs_mul_abs
  结论: (ht_int_pos : 可积 (fun ω => exp (t * X ω)) μ)
  证明: by
  rcases le_total 0 t with ht_nonneg | ht_nonpos
  · simp_rw [abs_of_nonneg ht_nonneg]
    exact integrable_exp_mul_abs ht_int_pos ht_int_neg
  · simp_rw [abs_of_nonpos ht_nonpos]
    exact integrable_exp_mul_abs ht_int_neg (by simpa using ht_int_pos)

Depends on / 依赖: abs_of_nonneg, abs_of_nonpos, ht_int_neg, ht_int_pos, ht_nonneg, ht_nonpos, integrable_exp_mul_abs, le_total, simp_rw
-/
lemma integrable_exp_abs_mul_abs (ht_int_pos : Integrable (fun ω => exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω => exp (-t * X ω)) μ) :
    Integrable (fun ω => exp (|t| * |X ω|)) μ := by
  rcases le_total 0 t with ht_nonneg | ht_nonpos
  · simp_rw [abs_of_nonneg ht_nonneg]
    exact integrable_exp_mul_abs ht_int_pos ht_int_neg
  · simp_rw [abs_of_nonpos ht_nonpos]
    exact integrable_exp_mul_abs ht_int_neg (by simpa using ht_int_pos)

/--
lemma `rpow_abs_le_mul_max_exp_of_pos` / 引理 `rpow_abs_le_mul_max_exp_of_pos`

English:
lemma rpow_abs_le_mul_max_exp_of_pos
  given: (x : Real) {t p : Real} (hp : 0 <= p) (ht : 0 < t)
  proof: by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, rpow_zero, zero_div, neg_mul, one_mul, le_sup_iff, one_le_exp_iff,
      Left.nonneg_neg_iff]
    exact le_total 0 (t * x)
  have h_x_le c (hc : 0 < c) : x <= c⁻¹ * exp (c * x) := le_inv_mul_exp x hc
  have h_neg_x_le c (hc : 0 < c) : -x <= c⁻¹ * exp (-c * x) := by simpa using le_inv_mul_exp (-x) hc
  have h_abs_le c (hc : 0 < c) : |x| <= c⁻¹ * max (exp (c * x)) (exp (-c * x)) := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · rw [neg_le]
      refine (h_neg_x_le c hc).trans ?_
      gcongr
      exact le_max_right _ _
    · refine (h_x_le c hc).trans ?_
      gcongr
      exact le_max_left _ _
  calc |x| ^ p
  _ <= ((t / p)⁻¹ * max (exp (t / p * x)) (exp (-t / p * x))) ^ p := by
    gcongr
    convert! h_abs_le (t / p) (div_pos ht (hp.lt_of_ne' hp_zero)) using 5
    rw [neg_div]
  _ = (p / t) ^ p * max (exp (t * x)) (exp (-t * x)) := by
    rw [mul_rpow (by positivity) (by positivity)]
    congr
    · simp
    · rw [rpow_max (by positivity) (by positivity) hp, ← exp_mul, ← exp_mul]
      ring_nf
      congr <;> rw [mul_assoc, mul_inv_cancel₀ hp_zero, mul_one]

中文:
引理 rpow_abs_le_mul_max_exp_of_pos
  条件: (x : 实数) {t p : 实数} (hp : 0 <= p) (ht : 0 < t)
  证明: by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, rpow_zero, zero_div, neg_mul, one_mul, le_sup_iff, one_le_exp_iff,
      Left.nonneg_neg_iff]
    exact le_total 0 (t * x)
  have h_x_le c (hc : 0 < c) : x <= c⁻¹ * exp (c * x) := le_inv_mul_exp x hc
  have h_neg_x_le c (hc : 0 < c) : -x <= c⁻¹ * exp (-c * x) := by simpa using le_inv_mul_exp (-x) hc
  have h_abs_le c (hc : 0 < c) : |x| <= c⁻¹ * max (exp (c * x)) (exp (-c * x)) := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · rw [neg_le]
      refine (h_neg_x_le c hc).trans ?_
      gcongr
      exact le_max_right _ _
    · refine (h_x_le c hc).trans ?_
      gcongr
      exact le_max_left _ _
  calc |x| ^ p
  _ <= ((t / p)⁻¹ * max (exp (t / p * x)) (exp (-t / p * x))) ^ p := by
    gcongr
    convert! h_abs_le (t / p) (div_pos ht (hp.lt_of_ne' hp_zero)) using 5
    rw [neg_div]
  _ = (p / t) ^ p * max (exp (t * x)) (exp (-t * x)) := by
    rw [mul_rpow (by positivity) (by positivity)]
    congr
    · simp
    · rw [rpow_max (by positivity) (by positivity) hp, ← exp_mul, ← exp_mul]
      ring_nf
      congr <;> rw [mul_assoc, mul_inv_cancel₀ hp_zero, mul_one]

Depends on / 依赖: Left.nonneg_neg_iff, abs_le, abs_le.mpr, h_abs_le, h_neg_x_le, h_x_le, hp_zero, le_inv_mul_exp, le_sup_iff, le_total, neg_le, neg_mul, nonneg_neg_iff, one_le_exp_iff, one_mul, rpow_zero, zero_div
-/
lemma rpow_abs_le_mul_max_exp_of_pos (x : Real) {t p : Real} (hp : 0 <= p) (ht : 0 < t) :
    |x| ^ p <= (p / t) ^ p * max (exp (t * x)) (exp (-t * x)) := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, rpow_zero, zero_div, neg_mul, one_mul, le_sup_iff, one_le_exp_iff,
      Left.nonneg_neg_iff]
    exact le_total 0 (t * x)
  have h_x_le c (hc : 0 < c) : x <= c⁻¹ * exp (c * x) := le_inv_mul_exp x hc
  have h_neg_x_le c (hc : 0 < c) : -x <= c⁻¹ * exp (-c * x) := by simpa using le_inv_mul_exp (-x) hc
  have h_abs_le c (hc : 0 < c) : |x| <= c⁻¹ * max (exp (c * x)) (exp (-c * x)) := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · rw [neg_le]
      refine (h_neg_x_le c hc).trans ?_
      gcongr
      exact le_max_right _ _
    · refine (h_x_le c hc).trans ?_
      gcongr
      exact le_max_left _ _
  calc |x| ^ p
  _ <= ((t / p)⁻¹ * max (exp (t / p * x)) (exp (-t / p * x))) ^ p := by
    gcongr
    convert! h_abs_le (t / p) (div_pos ht (hp.lt_of_ne' hp_zero)) using 5
    rw [neg_div]
  _ = (p / t) ^ p * max (exp (t * x)) (exp (-t * x)) := by
    rw [mul_rpow (by positivity) (by positivity)]
    congr
    · simp
    · rw [rpow_max (by positivity) (by positivity) hp, ← exp_mul, ← exp_mul]
      ring_nf
      congr <;> rw [mul_assoc, mul_inv_cancel₀ hp_zero, mul_one]

/--
lemma `rpow_abs_le_mul_max_exp` / 引理 `rpow_abs_le_mul_max_exp`

English:
lemma rpow_abs_le_mul_max_exp
  given: (x : Real) {t p : Real} (hp : 0 <= p) (ht : t != 0)
  proof: by
  rcases lt_or_gt_of_ne ht with ht_neg | ht_pos
  · rw [abs_of_nonpos ht_neg.le, sup_comm]
    convert! rpow_abs_le_mul_max_exp_of_pos x hp (t := -t) (by simp [ht_neg])
    simp
  · rw [abs_of_nonneg ht_pos.le]
    exact rpow_abs_le_mul_max_exp_of_pos x hp ht_pos

中文:
引理 rpow_abs_le_mul_max_exp
  条件: (x : 实数) {t p : 实数} (hp : 0 <= p) (ht : t != 0)
  证明: by
  rcases lt_or_gt_of_ne ht with ht_neg | ht_pos
  · rw [abs_of_nonpos ht_neg.le, sup_comm]
    convert! rpow_abs_le_mul_max_exp_of_pos x hp (t := -t) (by simp [ht_neg])
    simp
  · rw [abs_of_nonneg ht_pos.le]
    exact rpow_abs_le_mul_max_exp_of_pos x hp ht_pos

Depends on / 依赖: abs_of_nonneg, abs_of_nonpos, convert, ht_neg, ht_neg.le, ht_pos, ht_pos.le, lt_or_gt_of_ne, rpow_abs_le_mul_max_exp_of_pos, sup_comm
-/
lemma rpow_abs_le_mul_max_exp (x : Real) {t p : Real} (hp : 0 <= p) (ht : t != 0) :
    |x| ^ p <= (p / |t|) ^ p * max (exp (t * x)) (exp (-t * x)) := by
  rcases lt_or_gt_of_ne ht with ht_neg | ht_pos
  · rw [abs_of_nonpos ht_neg.le, sup_comm]
    convert! rpow_abs_le_mul_max_exp_of_pos x hp (t := -t) (by simp [ht_neg])
    simp
  · rw [abs_of_nonneg ht_pos.le]
    exact rpow_abs_le_mul_max_exp_of_pos x hp ht_pos

/--
lemma `rpow_abs_le_mul_exp_abs` / 引理 `rpow_abs_le_mul_exp_abs`

English:
lemma rpow_abs_le_mul_exp_abs
  given: (x : Real) {t p : Real} (hp : 0 <= p) (ht : t != 0)
  proof: by
  refine (rpow_abs_le_mul_max_exp_of_pos x hp (t := |t|) ?_).trans_eq ?_
  · simp [ht]
  · congr
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      simp only [neg_mul, sup_eq_left, exp_le_exp, neg_le_self_iff]
      positivity
    · rw [abs_of_nonpos hx]
      simp only [neg_mul, mul_neg, sup_eq_right, exp_le_exp, le_neg_self_iff]
      exact mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) hx

中文:
引理 rpow_abs_le_mul_exp_abs
  条件: (x : 实数) {t p : 实数} (hp : 0 <= p) (ht : t != 0)
  证明: by
  refine (rpow_abs_le_mul_max_exp_of_pos x hp (t := |t|) ?_).trans_eq ?_
  · simp [ht]
  · congr
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      simp only [neg_mul, sup_eq_left, exp_le_exp, neg_le_self_iff]
      positivity
    · rw [abs_of_nonpos hx]
      simp only [neg_mul, mul_neg, sup_eq_right, exp_le_exp, le_neg_self_iff]
      exact mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) hx

Depends on / 依赖: abs_nonneg, abs_of_nonneg, abs_of_nonpos, exp_le_exp, le_neg_self_iff, le_total, mul_neg, mul_nonpos_of_nonneg_of_nonpos, neg_le_self_iff, neg_mul, rpow_abs_le_mul_max_exp_of_pos, sup_eq_left, sup_eq_right, trans_eq
-/
lemma rpow_abs_le_mul_exp_abs (x : Real) {t p : Real} (hp : 0 <= p) (ht : t != 0) :
    |x| ^ p <= (p / |t|) ^ p * exp (|t| * |x|) := by
  refine (rpow_abs_le_mul_max_exp_of_pos x hp (t := |t|) ?_).trans_eq ?_
  · simp [ht]
  · congr
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      simp only [neg_mul, sup_eq_left, exp_le_exp, neg_le_self_iff]
      positivity
    · rw [abs_of_nonpos hx]
      simp only [neg_mul, mul_neg, sup_eq_right, exp_le_exp, le_neg_self_iff]
      exact mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) hx

/--
lemma `integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul` / 引理 `integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul`

English:
lemma integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul
  statement: {x : Real}
  proof: by
  have ht : t != 0 := by
    suffices |t| != 0 by simpa
    exact (h_nonneg.trans_lt hx).ne'
  have hX : AEMeasurable X μ := aemeasurable_of_integrable_exp_mul ?_ h_int_pos h_int_neg
  swap; · rw [← sub_ne_zero]; simp [ht]
  rw [← integrable_norm_iff]
  swap; · fun_prop
  simp only [norm_mul, norm_eq_abs, abs_exp]
  have h_le a : |X a| ^ p * exp (v * X a + x * |X a|)
      <= (p / (|t| - x)) ^ p * exp (v * X a + |t| * |X a|) := by
    simp_rw [exp_add, mul_comm (exp (v * X a)), ← mul_assoc]
    gcongr ?_ * _
    have : |t| = |t| - x + x := by simp
    nth_rw 2 [this]
    rw [add_mul]; rw [exp_add]; rw [← mul_assoc]
    gcongr ?_ * _
    convert! rpow_abs_le_mul_exp_abs (X a) hp (t := |t| - x) _ using 4
    · nth_rw 2 [abs_of_nonneg]
      simp [hx.le]
    · nth_rw 2 [abs_of_nonneg]
      simp [hx.le]
    · rw [sub_ne_zero]
      exact hx.ne'
  refine Integrable.mono (g := fun a => (p / (|t| - x)) ^ p * exp (v * X a + |t| * |X a|))
?_ ?_ ae_of_all _ fun ω => ?_
  · refine Integrable.const_mul ?_ _
    simp_rw [add_comm (v * X _)]
    exact integrable_exp_abs_mul_abs_add h_int_pos h_int_neg
  · fun_prop
  · simp only [norm_mul, norm_eq_abs, abs_exp]
    simp_rw [abs_rpow_of_nonneg (abs_nonneg _), abs_abs]
    refine (h_le ω).trans_eq ?_
    congr
    symm
    simp only [abs_eq_self]
    positivity [sub_nonneg_of_le hx.le]

中文:
引理 integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul
  结论: {x : 实数}
  证明: by
  have ht : t != 0 := by
    suffices |t| != 0 by simpa
    exact (h_nonneg.trans_lt hx).ne'
  have hX : AEMeasurable X μ := aemeasurable_of_integrable_exp_mul ?_ h_int_pos h_int_neg
  swap; · rw [← sub_ne_zero]; simp [ht]
  rw [← integrable_norm_iff]
  swap; · fun_prop
  simp only [norm_mul, norm_eq_abs, abs_exp]
  have h_le a : |X a| ^ p * exp (v * X a + x * |X a|)
      <= (p / (|t| - x)) ^ p * exp (v * X a + |t| * |X a|) := by
    simp_rw [exp_add, mul_comm (exp (v * X a)), ← mul_assoc]
    gcongr ?_ * _
    have : |t| = |t| - x + x := by simp
    nth_rw 2 [this]
    rw [add_mul]; rw [exp_add]; rw [← mul_assoc]
    gcongr ?_ * _
    convert! rpow_abs_le_mul_exp_abs (X a) hp (t := |t| - x) _ using 4
    · nth_rw 2 [abs_of_nonneg]
      simp [hx.le]
    · nth_rw 2 [abs_of_nonneg]
      simp [hx.le]
    · rw [sub_ne_zero]
      exact hx.ne'
  refine Integrable.mono (g := fun a => (p / (|t| - x)) ^ p * exp (v * X a + |t| * |X a|))
?_ ?_ ae_of_all _ fun ω => ?_
  · refine Integrable.const_mul ?_ _
    simp_rw [add_comm (v * X _)]
    exact integrable_exp_abs_mul_abs_add h_int_pos h_int_neg
  · fun_prop
  · simp only [norm_mul, norm_eq_abs, abs_exp]
    simp_rw [abs_rpow_of_nonneg (abs_nonneg _), abs_abs]
    refine (h_le ω).trans_eq ?_
    congr
    symm
    simp only [abs_eq_self]
    positivity [sub_nonneg_of_le hx.le]

Depends on / 依赖: AEMeasurable, abs_exp, aemeasurable_of_integrable_exp_mul, exp_add, fun_prop, h_int_neg, h_int_pos, h_le, h_nonneg, h_nonneg.trans_lt, integrable_norm_iff, mul_assoc, mul_comm, norm_eq_abs, norm_mul, simp_rw, sub_ne_zero, trans_lt
-/
lemma integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul {x : Real}
    (h_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ)
    (h_int_neg : Integrable (fun ω => exp ((v - t) * X ω)) μ) (h_nonneg : 0 <= x) (hx : x < |t|)
    {p : Real} (hp : 0 <= p) :
    Integrable (fun a => |X a| ^ p * exp (v * X a + x * |X a|)) μ := by
  have ht : t != 0 := by
    suffices |t| != 0 by simpa
    exact (h_nonneg.trans_lt hx).ne'
  have hX : AEMeasurable X μ := aemeasurable_of_integrable_exp_mul ?_ h_int_pos h_int_neg
  swap; · rw [← sub_ne_zero]; simp [ht]
  rw [← integrable_norm_iff]
  swap; · fun_prop
  simp only [norm_mul, norm_eq_abs, abs_exp]
  have h_le a : |X a| ^ p * exp (v * X a + x * |X a|)
      <= (p / (|t| - x)) ^ p * exp (v * X a + |t| * |X a|) := by
    simp_rw [exp_add, mul_comm (exp (v * X a)), ← mul_assoc]
    gcongr ?_ * _
    have : |t| = |t| - x + x := by simp
    nth_rw 2 [this]
    rw [add_mul]; rw [exp_add]; rw [← mul_assoc]
    gcongr ?_ * _
    convert! rpow_abs_le_mul_exp_abs (X a) hp (t := |t| - x) _ using 4
    · nth_rw 2 [abs_of_nonneg]
      simp [hx.le]
    · nth_rw 2 [abs_of_nonneg]
      simp [hx.le]
    · rw [sub_ne_zero]
      exact hx.ne'
  refine Integrable.mono (g := fun a => (p / (|t| - x)) ^ p * exp (v * X a + |t| * |X a|))
?_ ?_ ae_of_all _ fun ω => ?_
  · refine Integrable.const_mul ?_ _
    simp_rw [add_comm (v * X _)]
    exact integrable_exp_abs_mul_abs_add h_int_pos h_int_neg
  · fun_prop
  · simp only [norm_mul, norm_eq_abs, abs_exp]
    simp_rw [abs_rpow_of_nonneg (abs_nonneg _), abs_abs]
    refine (h_le ω).trans_eq ?_
    congr
    symm
    simp only [abs_eq_self]
    positivity [sub_nonneg_of_le hx.le]

/--
lemma `integrable_pow_abs_mul_exp_add_of_integrable_exp_mul` / 引理 `integrable_pow_abs_mul_exp_add_of_integrable_exp_mul`

English:
lemma integrable_pow_abs_mul_exp_add_of_integrable_exp_mul
  statement: {x : Real}
  proof: by
  convert!
    integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul h_int_pos h_int_neg h_nonneg hx
      n.cast_nonneg
  simp

中文:
引理 integrable_pow_abs_mul_exp_add_of_integrable_exp_mul
  结论: {x : 实数}
  证明: by
  convert!
    integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul h_int_pos h_int_neg h_nonneg hx
      n.cast_nonneg
  simp

Depends on / 依赖: cast_nonneg, convert, h_int_neg, h_int_pos, h_nonneg, integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul, n.cast_nonneg
-/
lemma integrable_pow_abs_mul_exp_add_of_integrable_exp_mul {x : Real}
    (h_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ)
    (h_int_neg : Integrable (fun ω => exp ((v - t) * X ω)) μ) (h_nonneg : 0 <= x) (hx : x < |t|)
    (n : Nat) :
    Integrable (fun a => |X a| ^ n * exp (v * X a + x * |X a|)) μ := by
  convert!
    integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul h_int_pos h_int_neg h_nonneg hx
      n.cast_nonneg
  simp

/--
lemma `integrable_rpow_abs_mul_exp_of_integrable_exp_mul` / 引理 `integrable_rpow_abs_mul_exp_of_integrable_exp_mul`

English:
lemma integrable_rpow_abs_mul_exp_of_integrable_exp_mul
  statement: (ht : t != 0)
  proof: by
  convert!
    integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul ht_int_pos ht_int_neg le_rfl _ hp using 4
  · simp
  · simp [ht]

中文:
引理 integrable_rpow_abs_mul_exp_of_integrable_exp_mul
  结论: (ht : t != 0)
  证明: by
  convert!
    integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul ht_int_pos ht_int_neg le_rfl _ hp using 4
  · simp
  · simp [ht]

Depends on / 依赖: convert, ht_int_neg, ht_int_pos, integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul, le_rfl
-/
lemma integrable_rpow_abs_mul_exp_of_integrable_exp_mul (ht : t != 0)
    (ht_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω => exp ((v - t) * X ω)) μ) {p : Real} (hp : 0 <= p) :
    Integrable (fun ω => |X ω| ^ p * exp (v * X ω)) μ := by
  convert!
    integrable_rpow_abs_mul_exp_add_of_integrable_exp_mul ht_int_pos ht_int_neg le_rfl _ hp using 4
  · simp
  · simp [ht]

/--
lemma `integrable_pow_abs_mul_exp_of_integrable_exp_mul` / 引理 `integrable_pow_abs_mul_exp_of_integrable_exp_mul`

English:
lemma integrable_pow_abs_mul_exp_of_integrable_exp_mul
  statement: (ht : t != 0)
  proof: by
  convert!
    integrable_rpow_abs_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg
      (by positivity : 0 <= (n : Real)) with
    ω
  simp

中文:
引理 integrable_pow_abs_mul_exp_of_integrable_exp_mul
  结论: (ht : t != 0)
  证明: by
  convert!
    integrable_rpow_abs_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg
      (by positivity : 0 <= (n : Real)) with
    ω
  simp

Depends on / 依赖: convert, ht_int_neg, ht_int_pos, integrable_rpow_abs_mul_exp_of_integrable_exp_mul
-/
lemma integrable_pow_abs_mul_exp_of_integrable_exp_mul (ht : t != 0)
    (ht_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω => exp ((v - t) * X ω)) μ) (n : Nat) :
    Integrable (fun ω => |X ω| ^ n * exp (v * X ω)) μ := by
  convert!
    integrable_rpow_abs_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg
      (by positivity : 0 <= (n : Real)) with
    ω
  simp

/--
lemma `integrable_rpow_mul_exp_of_integrable_exp_mul` / 引理 `integrable_rpow_mul_exp_of_integrable_exp_mul`

English:
lemma integrable_rpow_mul_exp_of_integrable_exp_mul
  statement: (ht : t != 0)
  proof: by
  have hX : AEMeasurable X μ := aemeasurable_of_integrable_exp_mul ?_ ht_int_pos ht_int_neg
  swap; · rw [← sub_ne_zero]; simp [ht]
  rw [← integrable_norm_iff]
  · simp_rw [norm_eq_abs, abs_mul, abs_exp]
    have h := integrable_rpow_abs_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg hp
    refine h.mono' ?_ ?_
    · fun_prop
    · refine ae_of_all _ fun ω => ?_
      simp only [norm_mul, norm_eq_abs, abs_abs, abs_exp]
      gcongr
      exact abs_rpow_le_abs_rpow _ _
  · fun_prop

中文:
引理 integrable_rpow_mul_exp_of_integrable_exp_mul
  结论: (ht : t != 0)
  证明: by
  have hX : AEMeasurable X μ := aemeasurable_of_integrable_exp_mul ?_ ht_int_pos ht_int_neg
  swap; · rw [← sub_ne_zero]; simp [ht]
  rw [← integrable_norm_iff]
  · simp_rw [norm_eq_abs, abs_mul, abs_exp]
    have h := integrable_rpow_abs_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg hp
    refine h.mono' ?_ ?_
    · fun_prop
    · refine ae_of_all _ fun ω => ?_
      simp only [norm_mul, norm_eq_abs, abs_abs, abs_exp]
      gcongr
      exact abs_rpow_le_abs_rpow _ _
  · fun_prop

Depends on / 依赖: AEMeasurable, abs_abs, abs_exp, abs_mul, abs_rpow_le_abs_rpow, ae_of_all, aemeasurable_of_integrable_exp_mul, fun_prop, h.mono, ht_int_neg, ht_int_pos, integrable_norm_iff, integrable_rpow_abs_mul_exp_of_integrable_exp_mul, norm_eq_abs, norm_mul, simp_rw, sub_ne_zero
-/
lemma integrable_rpow_mul_exp_of_integrable_exp_mul (ht : t != 0)
    (ht_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω => exp ((v - t) * X ω)) μ) {p : Real} (hp : 0 <= p) :
    Integrable (fun ω => X ω ^ p * exp (v * X ω)) μ := by
  have hX : AEMeasurable X μ := aemeasurable_of_integrable_exp_mul ?_ ht_int_pos ht_int_neg
  swap; · rw [← sub_ne_zero]; simp [ht]
  rw [← integrable_norm_iff]
  · simp_rw [norm_eq_abs, abs_mul, abs_exp]
    have h := integrable_rpow_abs_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg hp
    refine h.mono' ?_ ?_
    · fun_prop
    · refine ae_of_all _ fun ω => ?_
      simp only [norm_mul, norm_eq_abs, abs_abs, abs_exp]
      gcongr
      exact abs_rpow_le_abs_rpow _ _
  · fun_prop

/--
lemma `integrable_pow_mul_exp_of_integrable_exp_mul` / 引理 `integrable_pow_mul_exp_of_integrable_exp_mul`

English:
lemma integrable_pow_mul_exp_of_integrable_exp_mul
  statement: (ht : t != 0)
  proof: by
  convert!
    integrable_rpow_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg
      (by positivity : 0 <= (n : Real)) with
    ω
  simp

中文:
引理 integrable_pow_mul_exp_of_integrable_exp_mul
  结论: (ht : t != 0)
  证明: by
  convert!
    integrable_rpow_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg
      (by positivity : 0 <= (n : Real)) with
    ω
  simp

Depends on / 依赖: convert, ht_int_neg, ht_int_pos, integrable_rpow_mul_exp_of_integrable_exp_mul
-/
lemma integrable_pow_mul_exp_of_integrable_exp_mul (ht : t != 0)
    (ht_int_pos : Integrable (fun ω => exp ((v + t) * X ω)) μ)
    (ht_int_neg : Integrable (fun ω => exp ((v - t) * X ω)) μ) (n : Nat) :
    Integrable (fun ω => X ω ^ n * exp (v * X ω)) μ := by
  convert!
    integrable_rpow_mul_exp_of_integrable_exp_mul ht ht_int_pos ht_int_neg
      (by positivity : 0 <= (n : Real)) with
    ω
  simp

/--
lemma `integrable_rpow_abs_of_integrable_exp_mul` / 引理 `integrable_rpow_abs_of_integrable_exp_mul`

English:
lemma integrable_rpow_abs_of_integrable_exp_mul
  statement: (ht : t != 0)
  proof: by
  have h := integrable_rpow_abs_mul_exp_of_integrable_exp_mul (μ := μ) (X := X) ht (v := 0) ?_ ?_ hp
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

中文:
引理 integrable_rpow_abs_of_integrable_exp_mul
  结论: (ht : t != 0)
  证明: by
  have h := integrable_rpow_abs_mul_exp_of_integrable_exp_mul (μ := μ) (X := X) ht (v := 0) ?_ ?_ hp
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

Depends on / 依赖: ht_int_neg, ht_int_pos, integrable_rpow_abs_mul_exp_of_integrable_exp_mul
-/
lemma integrable_rpow_abs_of_integrable_exp_mul (ht : t != 0)
    (ht_int_pos : Integrable (fun ω => exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω => exp (-t * X ω)) μ) {p : Real} (hp : 0 <= p) :
    Integrable (fun ω => |X ω| ^ p) μ := by
  have h := integrable_rpow_abs_mul_exp_of_integrable_exp_mul (μ := μ) (X := X) ht (v := 0) ?_ ?_ hp
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

/--
lemma `integrable_pow_abs_of_integrable_exp_mul` / 引理 `integrable_pow_abs_of_integrable_exp_mul`

English:
lemma integrable_pow_abs_of_integrable_exp_mul
  statement: (ht : t != 0)
  proof: by
  convert!
    integrable_rpow_abs_of_integrable_exp_mul ht ht_int_pos ht_int_neg
      (by positivity : 0 <= (n : Real)) with
    ω
  simp

中文:
引理 integrable_pow_abs_of_integrable_exp_mul
  结论: (ht : t != 0)
  证明: by
  convert!
    integrable_rpow_abs_of_integrable_exp_mul ht ht_int_pos ht_int_neg
      (by positivity : 0 <= (n : Real)) with
    ω
  simp

Depends on / 依赖: convert, ht_int_neg, ht_int_pos, integrable_rpow_abs_of_integrable_exp_mul
-/
lemma integrable_pow_abs_of_integrable_exp_mul (ht : t != 0)
    (ht_int_pos : Integrable (fun ω => exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω => exp (-t * X ω)) μ) (n : Nat) :
    Integrable (fun ω => |X ω| ^ n) μ := by
  convert!
    integrable_rpow_abs_of_integrable_exp_mul ht ht_int_pos ht_int_neg
      (by positivity : 0 <= (n : Real)) with
    ω
  simp

/--
lemma `integrable_rpow_of_integrable_exp_mul` / 引理 `integrable_rpow_of_integrable_exp_mul`

English:
lemma integrable_rpow_of_integrable_exp_mul
  statement: (ht : t != 0)
  proof: by
  have h := integrable_rpow_mul_exp_of_integrable_exp_mul (μ := μ) (X := X) ht (v := 0) ?_ ?_ hp
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

中文:
引理 integrable_rpow_of_integrable_exp_mul
  结论: (ht : t != 0)
  证明: by
  have h := integrable_rpow_mul_exp_of_integrable_exp_mul (μ := μ) (X := X) ht (v := 0) ?_ ?_ hp
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

Depends on / 依赖: ht_int_neg, ht_int_pos, integrable_rpow_mul_exp_of_integrable_exp_mul
-/
lemma integrable_rpow_of_integrable_exp_mul (ht : t != 0)
    (ht_int_pos : Integrable (fun ω => exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω => exp (-t * X ω)) μ) {p : Real} (hp : 0 <= p) :
    Integrable (fun ω => X ω ^ p) μ := by
  have h := integrable_rpow_mul_exp_of_integrable_exp_mul (μ := μ) (X := X) ht (v := 0) ?_ ?_ hp
  · simpa using h
  · simpa using ht_int_pos
  · simpa using ht_int_neg

/--
lemma `integrable_pow_of_integrable_exp_mul` / 引理 `integrable_pow_of_integrable_exp_mul`

English:
lemma integrable_pow_of_integrable_exp_mul
  statement: (ht : t != 0)
  proof: by
  convert!
    integrable_rpow_of_integrable_exp_mul ht ht_int_pos ht_int_neg
      (by positivity : 0 <= (n : Real)) with
    ω
  simp

中文:
引理 integrable_pow_of_integrable_exp_mul
  结论: (ht : t != 0)
  证明: by
  convert!
    integrable_rpow_of_integrable_exp_mul ht ht_int_pos ht_int_neg
      (by positivity : 0 <= (n : Real)) with
    ω
  simp

Depends on / 依赖: convert, ht_int_neg, ht_int_pos, integrable_rpow_of_integrable_exp_mul
-/
lemma integrable_pow_of_integrable_exp_mul (ht : t != 0)
    (ht_int_pos : Integrable (fun ω => exp (t * X ω)) μ)
    (ht_int_neg : Integrable (fun ω => exp (-t * X ω)) μ) (n : Nat) :
    Integrable (fun ω => X ω ^ n) μ := by
  convert!
    integrable_rpow_of_integrable_exp_mul ht ht_int_pos ht_int_neg
      (by positivity : 0 <= (n : Real)) with
    ω
  simp

section IntegrableExpSet

/--
lemma `add_half_inf_sub_mem_Ioo` / 引理 `add_half_inf_sub_mem_Ioo`

English:
lemma add_half_inf_sub_mem_Ioo
  given: {l u v : Real} (hv : v in Set.Ioo l u)
  proof: by
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hv.1, hv.2]
  constructor
  · calc l < v := hv.1
    _ <= v + ((v - l) ⊓ (u - v)) / 2 := le_add_of_nonneg_right (by positivity)
  · calc v + ((v - l) ⊓ (u - v)) / 2
    _ < v + ((v - l) ⊓ (u - v)) := by gcongr; exact half_lt_self (by positivity)
    _ <= v + (u - v) := by gcongr; exact inf_le_right
    _ = u := by abel

中文:
引理 add_half_inf_sub_mem_Ioo
  条件: {l u v : 实数} (hv : v in 集合.开区间 l u)
  证明: by
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hv.1, hv.2]
  constructor
  · calc l < v := hv.1
    _ <= v + ((v - l) ⊓ (u - v)) / 2 := le_add_of_nonneg_right (by positivity)
  · calc v + ((v - l) ⊓ (u - v)) / 2
    _ < v + ((v - l) ⊓ (u - v)) := by gcongr; exact half_lt_self (by positivity)
    _ <= v + (u - v) := by gcongr; exact inf_le_right
    _ = u := by abel

Depends on / 依赖: h_pos, half_lt_self, inf_le_right, le_add_of_nonneg_right
-/
lemma add_half_inf_sub_mem_Ioo {l u v : Real} (hv : v in Set.Ioo l u) :
    v + ((v - l) ⊓ (u - v)) / 2 in Set.Ioo l u := by
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hv.1, hv.2]
  constructor
  · calc l < v := hv.1
    _ <= v + ((v - l) ⊓ (u - v)) / 2 := le_add_of_nonneg_right (by positivity)
  · calc v + ((v - l) ⊓ (u - v)) / 2
    _ < v + ((v - l) ⊓ (u - v)) := by gcongr; exact half_lt_self (by positivity)
    _ <= v + (u - v) := by gcongr; exact inf_le_right
    _ = u := by abel

/--
lemma `sub_half_inf_sub_mem_Ioo` / 引理 `sub_half_inf_sub_mem_Ioo`

English:
lemma sub_half_inf_sub_mem_Ioo
  given: {l u v : Real} (hv : v in Set.Ioo l u)
  proof: by
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hv.1, hv.2]
  constructor
  · calc l = v - (v - l) := by abel
    _ <= v - ((v - l) ⊓ (u - v)) := by gcongr; exact inf_le_left
    _ < v - ((v - l) ⊓ (u - v)) / 2 := by gcongr; exact half_lt_self (by positivity)
  · calc v - ((v - l) ⊓ (u - v)) / 2
    _ <= v := by
      rw [sub_le_iff_le_add]
      exact le_add_of_nonneg_right (by positivity)
    _ < u := hv.2

中文:
引理 sub_half_inf_sub_mem_Ioo
  条件: {l u v : 实数} (hv : v in 集合.开区间 l u)
  证明: by
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hv.1, hv.2]
  constructor
  · calc l = v - (v - l) := by abel
    _ <= v - ((v - l) ⊓ (u - v)) := by gcongr; exact inf_le_left
    _ < v - ((v - l) ⊓ (u - v)) / 2 := by gcongr; exact half_lt_self (by positivity)
  · calc v - ((v - l) ⊓ (u - v)) / 2
    _ <= v := by
      rw [sub_le_iff_le_add]
      exact le_add_of_nonneg_right (by positivity)
    _ < u := hv.2

Depends on / 依赖: h_pos, half_lt_self, inf_le_left, le_add_of_nonneg_right, sub_le_iff_le_add
-/
lemma sub_half_inf_sub_mem_Ioo {l u v : Real} (hv : v in Set.Ioo l u) :
    v - ((v - l) ⊓ (u - v)) / 2 in Set.Ioo l u := by
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hv.1, hv.2]
  constructor
  · calc l = v - (v - l) := by abel
    _ <= v - ((v - l) ⊓ (u - v)) := by gcongr; exact inf_le_left
    _ < v - ((v - l) ⊓ (u - v)) / 2 := by gcongr; exact half_lt_self (by positivity)
  · calc v - ((v - l) ⊓ (u - v)) / 2
    _ <= v := by
      rw [sub_le_iff_le_add]
      exact le_add_of_nonneg_right (by positivity)
    _ < u := hv.2

/--
lemma `aemeasurable_of_mem_interior_integrableExpSet` / 引理 `aemeasurable_of_mem_interior_integrableExpSet`

English:
lemma aemeasurable_of_mem_interior_integrableExpSet
  given: (hv : v in interior (integrableExpSet X μ))
  proof: by
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hv
  obtain ⟨l, u, hvlu, h_subset⟩ := hv
  let t := ((v - l) ⊓ (u - v)) / 2
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hvlu.1, hvlu.2]
  have ht : 0 < t := half_pos h_pos
  by_cases hvt : v + t = 0
  · have hvt' : v - t != 0 := by
      rw [sub_ne_zero]
      refine fun h_eq => ht.ne' ?_
      simpa [h_eq] using hvt
    exact aemeasurable_of_aemeasurable_exp_mul hvt'
      (h_subset (sub_half_inf_sub_mem_Ioo hvlu)).aemeasurable
  · exact aemeasurable_of_aemeasurable_exp_mul hvt
      (h_subset (add_half_inf_sub_mem_Ioo hvlu)).aemeasurable

中文:
引理 aemeasurable_of_mem_interior_integrableExpSet
  条件: (hv : v in interior (integrableExpSet X μ))
  证明: by
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hv
  obtain ⟨l, u, hvlu, h_subset⟩ := hv
  let t := ((v - l) ⊓ (u - v)) / 2
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hvlu.1, hvlu.2]
  have ht : 0 < t := half_pos h_pos
  by_cases hvt : v + t = 0
  · have hvt' : v - t != 0 := by
      rw [sub_ne_zero]
      refine fun h_eq => ht.ne' ?_
      simpa [h_eq] using hvt
    exact aemeasurable_of_aemeasurable_exp_mul hvt'
      (h_subset (sub_half_inf_sub_mem_Ioo hvlu)).aemeasurable
  · exact aemeasurable_of_aemeasurable_exp_mul hvt
      (h_subset (add_half_inf_sub_mem_Ioo hvlu)).aemeasurable

Depends on / 依赖: aemeasurable, aemeasurable_of_aeme, aemeasurable_of_aemeasurable_exp_mul, h_eq, h_pos, h_subset, half_pos, ht.ne, mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset, sub_half_inf_sub_mem_Ioo, sub_ne_zero
-/
lemma aemeasurable_of_mem_interior_integrableExpSet (hv : v in interior (integrableExpSet X μ)) :
    AEMeasurable X μ := by
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hv
  obtain ⟨l, u, hvlu, h_subset⟩ := hv
  let t := ((v - l) ⊓ (u - v)) / 2
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hvlu.1, hvlu.2]
  have ht : 0 < t := half_pos h_pos
  by_cases hvt : v + t = 0
  · have hvt' : v - t != 0 := by
      rw [sub_ne_zero]
      refine fun h_eq => ht.ne' ?_
      simpa [h_eq] using hvt
    exact aemeasurable_of_aemeasurable_exp_mul hvt'
      (h_subset (sub_half_inf_sub_mem_Ioo hvlu)).aemeasurable
  · exact aemeasurable_of_aemeasurable_exp_mul hvt
      (h_subset (add_half_inf_sub_mem_Ioo hvlu)).aemeasurable

/--
lemma `integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet` / 引理 `integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet`

English:
lemma integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet
  proof: by
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hv
  obtain ⟨l, u, hvlu, h_subset⟩ := hv
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hvlu.1, hvlu.2]
  refine integrable_rpow_abs_mul_exp_of_integrable_exp_mul
    (t := min (v - l) (u - v) / 2) ?_ ?_ ?_ hp
  · positivity
  · exact h_subset (add_half_inf_sub_mem_Ioo hvlu)
  · exact h_subset (sub_half_inf_sub_mem_Ioo hvlu)

中文:
引理 integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet
  证明: by
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hv
  obtain ⟨l, u, hvlu, h_subset⟩ := hv
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hvlu.1, hvlu.2]
  refine integrable_rpow_abs_mul_exp_of_integrable_exp_mul
    (t := min (v - l) (u - v) / 2) ?_ ?_ ?_ hp
  · positivity
  · exact h_subset (add_half_inf_sub_mem_Ioo hvlu)
  · exact h_subset (sub_half_inf_sub_mem_Ioo hvlu)

Depends on / 依赖: add_half_inf_sub_mem_Ioo, h_pos, h_subset, integrable_rpow_abs_mul_exp_of_integrable_exp_mul, mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset, sub_half_inf_sub_mem_Ioo
-/
lemma integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet
    (hv : v in interior (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) :
    Integrable (fun ω => |X ω| ^ p * exp (v * X ω)) μ := by
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hv
  obtain ⟨l, u, hvlu, h_subset⟩ := hv
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hvlu.1, hvlu.2]
  refine integrable_rpow_abs_mul_exp_of_integrable_exp_mul
    (t := min (v - l) (u - v) / 2) ?_ ?_ ?_ hp
  · positivity
  · exact h_subset (add_half_inf_sub_mem_Ioo hvlu)
  · exact h_subset (sub_half_inf_sub_mem_Ioo hvlu)

/--
lemma `integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet` / 引理 `integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet`

English:
lemma integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet
  proof: by
  convert!
    integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet hv
      (by positivity : 0 <= (n : Real)) with
    ω
  simp

中文:
引理 integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet
  证明: by
  convert!
    integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet hv
      (by positivity : 0 <= (n : Real)) with
    ω
  simp

Depends on / 依赖: convert, integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet
-/
lemma integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet
    (hv : v in interior (integrableExpSet X μ)) (n : Nat) :
    Integrable (fun ω => |X ω| ^ n * exp (v * X ω)) μ := by
  convert!
    integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet hv
      (by positivity : 0 <= (n : Real)) with
    ω
  simp

/--
lemma `integrable_rpow_mul_exp_of_mem_interior_integrableExpSet` / 引理 `integrable_rpow_mul_exp_of_mem_interior_integrableExpSet`

English:
lemma integrable_rpow_mul_exp_of_mem_interior_integrableExpSet
  proof: by
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hv
  obtain ⟨l, u, hvlu, h_subset⟩ := hv
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hvlu.1, hvlu.2]
  refine integrable_rpow_mul_exp_of_integrable_exp_mul
    (t := min (v - l) (u - v) / 2) ?_ ?_ ?_ hp
  · positivity
  · exact h_subset (add_half_inf_sub_mem_Ioo hvlu)
  · exact h_subset (sub_half_inf_sub_mem_Ioo hvlu)

中文:
引理 integrable_rpow_mul_exp_of_mem_interior_integrableExpSet
  证明: by
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hv
  obtain ⟨l, u, hvlu, h_subset⟩ := hv
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hvlu.1, hvlu.2]
  refine integrable_rpow_mul_exp_of_integrable_exp_mul
    (t := min (v - l) (u - v) / 2) ?_ ?_ ?_ hp
  · positivity
  · exact h_subset (add_half_inf_sub_mem_Ioo hvlu)
  · exact h_subset (sub_half_inf_sub_mem_Ioo hvlu)

Depends on / 依赖: add_half_inf_sub_mem_Ioo, h_pos, h_subset, integrable_rpow_mul_exp_of_integrable_exp_mul, mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset, sub_half_inf_sub_mem_Ioo
-/
lemma integrable_rpow_mul_exp_of_mem_interior_integrableExpSet
    (hv : v in interior (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) :
    Integrable (fun ω => X ω ^ p * exp (v * X ω)) μ := by
  rw [mem_interior_iff_mem_nhds]; rw [mem_nhds_iff_exists_Ioo_subset] at hv
  obtain ⟨l, u, hvlu, h_subset⟩ := hv
  have h_pos : 0 < (v - l) ⊓ (u - v) := by simp [hvlu.1, hvlu.2]
  refine integrable_rpow_mul_exp_of_integrable_exp_mul
    (t := min (v - l) (u - v) / 2) ?_ ?_ ?_ hp
  · positivity
  · exact h_subset (add_half_inf_sub_mem_Ioo hvlu)
  · exact h_subset (sub_half_inf_sub_mem_Ioo hvlu)

/--
lemma `integrable_pow_mul_exp_of_mem_interior_integrableExpSet` / 引理 `integrable_pow_mul_exp_of_mem_interior_integrableExpSet`

English:
lemma integrable_pow_mul_exp_of_mem_interior_integrableExpSet
  proof: by
  convert!
    integrable_rpow_mul_exp_of_mem_interior_integrableExpSet hv (by positivity : 0 <= (n : Real)) with ω
  simp

中文:
引理 integrable_pow_mul_exp_of_mem_interior_integrableExpSet
  证明: by
  convert!
    integrable_rpow_mul_exp_of_mem_interior_integrableExpSet hv (by positivity : 0 <= (n : Real)) with ω
  simp

Depends on / 依赖: convert, integrable_rpow_mul_exp_of_mem_interior_integrableExpSet
-/
lemma integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (hv : v in interior (integrableExpSet X μ)) (n : Nat) :
    Integrable (fun ω => X ω ^ n * exp (v * X ω)) μ := by
  convert!
    integrable_rpow_mul_exp_of_mem_interior_integrableExpSet hv (by positivity : 0 <= (n : Real)) with ω
  simp

/--
lemma `integrable_rpow_abs_of_mem_interior_integrableExpSet` / 引理 `integrable_rpow_abs_of_mem_interior_integrableExpSet`

English:
lemma integrable_rpow_abs_of_mem_interior_integrableExpSet
  proof: by
  convert! integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet h hp using 1
  simp

中文:
引理 integrable_rpow_abs_of_mem_interior_integrableExpSet
  证明: by
  convert! integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet h hp using 1
  simp

Depends on / 依赖: convert, integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet
-/
lemma integrable_rpow_abs_of_mem_interior_integrableExpSet
    (h : 0 in interior (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) :
    Integrable (fun ω => |X ω| ^ p) μ := by
  convert! integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet h hp using 1
  simp

/--
lemma `integrable_pow_abs_of_mem_interior_integrableExpSet` / 引理 `integrable_pow_abs_of_mem_interior_integrableExpSet`

English:
lemma integrable_pow_abs_of_mem_interior_integrableExpSet
  proof: by
  convert! integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet h n
  simp

中文:
引理 integrable_pow_abs_of_mem_interior_integrableExpSet
  证明: by
  convert! integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet h n
  simp

Depends on / 依赖: convert, integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet
-/
lemma integrable_pow_abs_of_mem_interior_integrableExpSet
    (h : 0 in interior (integrableExpSet X μ)) (n : Nat) :
    Integrable (fun ω => |X ω| ^ n) μ := by
  convert! integrable_pow_abs_mul_exp_of_mem_interior_integrableExpSet h n
  simp

/--
lemma `integrable_rpow_of_mem_interior_integrableExpSet` / 引理 `integrable_rpow_of_mem_interior_integrableExpSet`

English:
lemma integrable_rpow_of_mem_interior_integrableExpSet
  proof: by
  convert! integrable_rpow_mul_exp_of_mem_interior_integrableExpSet h hp using 1
  simp

中文:
引理 integrable_rpow_of_mem_interior_integrableExpSet
  证明: by
  convert! integrable_rpow_mul_exp_of_mem_interior_integrableExpSet h hp using 1
  simp

Depends on / 依赖: convert, integrable_rpow_mul_exp_of_mem_interior_integrableExpSet
-/
lemma integrable_rpow_of_mem_interior_integrableExpSet
    (h : 0 in interior (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) :
    Integrable (fun ω => X ω ^ p) μ := by
  convert! integrable_rpow_mul_exp_of_mem_interior_integrableExpSet h hp using 1
  simp

/--
lemma `integrable_pow_of_mem_interior_integrableExpSet` / 引理 `integrable_pow_of_mem_interior_integrableExpSet`

English:
lemma integrable_pow_of_mem_interior_integrableExpSet
  proof: by
  convert! integrable_pow_mul_exp_of_mem_interior_integrableExpSet h n
  simp

中文:
引理 integrable_pow_of_mem_interior_integrableExpSet
  证明: by
  convert! integrable_pow_mul_exp_of_mem_interior_integrableExpSet h n
  simp

Depends on / 依赖: convert, integrable_pow_mul_exp_of_mem_interior_integrableExpSet
-/
lemma integrable_pow_of_mem_interior_integrableExpSet
    (h : 0 in interior (integrableExpSet X μ)) (n : Nat) :
    Integrable (fun ω => X ω ^ n) μ := by
  convert! integrable_pow_mul_exp_of_mem_interior_integrableExpSet h n
  simp

/--
lemma `memLp_of_mem_interior_integrableExpSet` / 引理 `memLp_of_mem_interior_integrableExpSet`

English:
lemma memLp_of_mem_interior_integrableExpSet
  given: (h : 0 in interior (integrableExpSet X μ)) (p : Real>=0)
  proof: by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet h
  by_cases hp_zero : p = 0
  · simp only [hp_zero, ENNReal.coe_zero, memLp_zero_iff_aestronglyMeasurable]
    exact hX.aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hX.aestronglyMeasurable (mod_cast hp_zero) (by simp)]
  simp only [norm_eq_abs, ENNReal.coe_toReal]
  exact integrable_rpow_abs_of_mem_interior_integrableExpSet h p.2

中文:
引理 memLp_of_mem_interior_integrableExpSet
  条件: (h : 0 in interior (integrableExpSet X μ)) (p : 实数>=0)
  证明: by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet h
  by_cases hp_zero : p = 0
  · simp only [hp_zero, ENNReal.coe_zero, memLp_zero_iff_aestronglyMeasurable]
    exact hX.aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hX.aestronglyMeasurable (mod_cast hp_zero) (by simp)]
  simp only [norm_eq_abs, ENNReal.coe_toReal]
  exact integrable_rpow_abs_of_mem_interior_integrableExpSet h p.2

Depends on / 依赖: AEMeasurable, ENNReal, ENNReal.coe_toReal, ENNReal.coe_zero, aemeasurable_of_mem_interior_integrableExpSet, aestronglyMeasurable, coe_toReal, coe_zero, hX.aestronglyMeasurable, hp_zero, integrable_norm_rpow_iff, integrable_rpow_abs_of_mem_interior_integrableExpSet, memLp_zero_iff_aestronglyMeasurable, mod_cast, norm_eq_abs
-/
lemma memLp_of_mem_interior_integrableExpSet (h : 0 in interior (integrableExpSet X μ)) (p : Real>=0) :
    MemLp X p μ := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet h
  by_cases hp_zero : p = 0
  · simp only [hp_zero, ENNReal.coe_zero, memLp_zero_iff_aestronglyMeasurable]
    exact hX.aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hX.aestronglyMeasurable (mod_cast hp_zero) (by simp)]
  simp only [norm_eq_abs, ENNReal.coe_toReal]
  exact integrable_rpow_abs_of_mem_interior_integrableExpSet h p.2

/--
lemma `integrable_of_mem_interior_integrableExpSet` / 引理 `integrable_of_mem_interior_integrableExpSet`

English:
lemma integrable_of_mem_interior_integrableExpSet
  given: (h : 0 in interior (integrableExpSet X μ))
  proof: by
  simpa using integrable_pow_of_mem_interior_integrableExpSet h 1

中文:
引理 integrable_of_mem_interior_integrableExpSet
  条件: (h : 0 in interior (integrableExpSet X μ))
  证明: by
  simpa using integrable_pow_of_mem_interior_integrableExpSet h 1

Depends on / 依赖: integrable_pow_of_mem_interior_integrableExpSet
-/
lemma integrable_of_mem_interior_integrableExpSet (h : 0 in interior (integrableExpSet X μ)) :
    Integrable X μ := by
  simpa using integrable_pow_of_mem_interior_integrableExpSet h 1

section Complex

open Complex

variable {z : Complex}

/--
lemma `integrable_cexp_mul_of_re_mem_integrableExpSet` / 引理 `integrable_cexp_mul_of_re_mem_integrableExpSet`

English:
lemma integrable_cexp_mul_of_re_mem_integrableExpSet
  statement: (hX : AEMeasurable X μ)
  proof: by
  rw [← integrable_norm_iff]
  · simpa [Complex.norm_exp] using! hz
  · fun_prop

中文:
引理 integrable_cexp_mul_of_re_mem_integrableExpSet
  结论: (hX : 几乎处处可测 X μ)
  证明: by
  rw [← integrable_norm_iff]
  · simpa [Complex.norm_exp] using! hz
  · fun_prop

Depends on / 依赖: Complex.norm_exp, fun_prop, integrable_norm_iff, norm_exp
-/
lemma integrable_cexp_mul_of_re_mem_integrableExpSet (hX : AEMeasurable X μ)
    (hz : z.re in integrableExpSet X μ) :
    Integrable (fun ω => cexp (z * X ω)) μ := by
  rw [← integrable_norm_iff]
  · simpa [Complex.norm_exp] using! hz
  · fun_prop

/--
lemma `integrable_cexp_mul_of_re_mem_interior_integrableExpSet` / 引理 `integrable_cexp_mul_of_re_mem_interior_integrableExpSet`

English:
lemma integrable_cexp_mul_of_re_mem_interior_integrableExpSet
  proof: integrable_cexp_mul_of_re_mem_integrableExpSet
    (aemeasurable_of_mem_interior_integrableExpSet hz) (interior_subset hz)

中文:
引理 integrable_cexp_mul_of_re_mem_interior_integrableExpSet
  证明: integrable_cexp_mul_of_re_mem_integrableExpSet
    (aemeasurable_of_mem_interior_integrableExpSet hz) (interior_subset hz)

Depends on / 依赖: aemeasurable_of_mem_interior_integrableExpSet, integrable_cexp_mul_of_re_mem_integrableExpSet, interior_subset
-/
lemma integrable_cexp_mul_of_re_mem_interior_integrableExpSet
    (hz : z.re in interior (integrableExpSet X μ)) :
    Integrable (fun ω => cexp (z * X ω)) μ :=
  integrable_cexp_mul_of_re_mem_integrableExpSet
    (aemeasurable_of_mem_interior_integrableExpSet hz) (interior_subset hz)

/--
lemma `integrable_rpow_abs_mul_cexp_of_re_mem_interior_integrableExpSet` / 引理 `integrable_rpow_abs_mul_cexp_of_re_mem_interior_integrableExpSet`

English:
lemma integrable_rpow_abs_mul_cexp_of_re_mem_interior_integrableExpSet
  proof: by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  rw [← integrable_norm_iff]
  swap; · fun_prop
  simpa [abs_rpow_of_nonneg (abs_nonneg _), Complex.norm_exp]
    using integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet hz hp

中文:
引理 integrable_rpow_abs_mul_cexp_of_re_mem_interior_integrableExpSet
  证明: by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  rw [← integrable_norm_iff]
  swap; · fun_prop
  simpa [abs_rpow_of_nonneg (abs_nonneg _), Complex.norm_exp]
    using integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet hz hp

Depends on / 依赖: AEMeasurable, Complex.norm_exp, IsStandardSmooth, Smooth, abs_nonneg, abs_rpow_of_nonneg, aemeasurable_of_mem_interior_integrableExpSet, fun_prop, integrable_norm_iff, integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet, norm_exp
-/
lemma integrable_rpow_abs_mul_cexp_of_re_mem_interior_integrableExpSet
    (hz : z.re in interior (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) :
    Integrable (fun ω => (|X ω| ^ p : Real) * cexp (z * X ω)) μ := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  rw [← integrable_norm_iff]
  swap; · fun_prop
  simpa [abs_rpow_of_nonneg (abs_nonneg _), Complex.norm_exp]
    using integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet hz hp

/--
lemma `integrable_pow_abs_mul_cexp_of_re_mem_interior_integrableExpSet` / 引理 `integrable_pow_abs_mul_cexp_of_re_mem_interior_integrableExpSet`

English:
lemma integrable_pow_abs_mul_cexp_of_re_mem_interior_integrableExpSet
  proof: by
  convert! integrable_rpow_abs_mul_cexp_of_re_mem_interior_integrableExpSet hz (Nat.cast_nonneg n)
  simp

中文:
引理 integrable_pow_abs_mul_cexp_of_re_mem_interior_integrableExpSet
  证明: by
  convert! integrable_rpow_abs_mul_cexp_of_re_mem_interior_integrableExpSet hz (Nat.cast_nonneg n)
  simp

Depends on / 依赖: IsStandardSmoothOfRelativeDimension, Nat.cast_nonneg, cast_nonneg, convert, integrable_rpow_abs_mul_cexp_of_re_mem_interior_integrableExpSet
-/
lemma integrable_pow_abs_mul_cexp_of_re_mem_interior_integrableExpSet
    (hz : z.re in interior (integrableExpSet X μ)) (n : Nat) :
    Integrable (fun ω => |X ω| ^ n * cexp (z * X ω)) μ := by
  convert! integrable_rpow_abs_mul_cexp_of_re_mem_interior_integrableExpSet hz (Nat.cast_nonneg n)
  simp

/--
lemma `integrable_rpow_mul_cexp_of_re_mem_interior_integrableExpSet` / 引理 `integrable_rpow_mul_cexp_of_re_mem_interior_integrableExpSet`

English:
lemma integrable_rpow_mul_cexp_of_re_mem_interior_integrableExpSet
  proof: by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  rw [← integrable_norm_iff]
  swap; · fun_prop
  simp only [norm_mul, norm_real, Complex.norm_exp, mul_re, ofReal_re,
    ofReal_im, mul_zero, sub_zero]
  refine (integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet hz hp).mono ?_ ?_
  · fun_prop
  refine ae_of_all _ fun ω => ?_
  simp only [norm_mul, Real.norm_eq_abs, Real.abs_exp]
  gcongr
  exact abs_rpow_le_abs_rpow _ _

中文:
引理 integrable_rpow_mul_cexp_of_re_mem_interior_integrableExpSet
  证明: by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  rw [← integrable_norm_iff]
  swap; · fun_prop
  simp only [norm_mul, norm_real, Complex.norm_exp, mul_re, ofReal_re,
    ofReal_im, mul_zero, sub_zero]
  refine (integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet hz hp).mono ?_ ?_
  · fun_prop
  refine ae_of_all _ fun ω => ?_
  simp only [norm_mul, Real.norm_eq_abs, Real.abs_exp]
  gcongr
  exact abs_rpow_le_abs_rpow _ _

Depends on / 依赖: AEMeasurable, Complex.norm_exp, Real.abs_exp, Real.norm_eq_abs, abs_exp, abs_rpow_le_abs_rpow, ae_of_all, aemeasurable_of_mem_interior_integrableExpSet, fun_prop, integrable_norm_iff, integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet, mul_re, mul_zero, norm_eq_abs, norm_exp, norm_mul, norm_real, ofReal_im, ofReal_re, sub_zero
-/
lemma integrable_rpow_mul_cexp_of_re_mem_interior_integrableExpSet
    (hz : z.re in interior (integrableExpSet X μ)) {p : Real} (hp : 0 <= p) :
    Integrable (fun ω => (X ω ^ p : Real) * cexp (z * X ω)) μ := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrableExpSet hz
  rw [← integrable_norm_iff]
  swap; · fun_prop
  simp only [norm_mul, norm_real, Complex.norm_exp, mul_re, ofReal_re,
    ofReal_im, mul_zero, sub_zero]
  refine (integrable_rpow_abs_mul_exp_of_mem_interior_integrableExpSet hz hp).mono ?_ ?_
  · fun_prop
  refine ae_of_all _ fun ω => ?_
  simp only [norm_mul, Real.norm_eq_abs, Real.abs_exp]
  gcongr
  exact abs_rpow_le_abs_rpow _ _

/--
lemma `integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet` / 引理 `integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet`

English:
lemma integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
  proof: by
  convert! integrable_rpow_mul_cexp_of_re_mem_interior_integrableExpSet hz (Nat.cast_nonneg n)
  simp

中文:
引理 integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
  证明: by
  convert! integrable_rpow_mul_cexp_of_re_mem_interior_integrableExpSet hz (Nat.cast_nonneg n)
  simp

Depends on / 依赖: Nat.cast_nonneg, cast_nonneg, convert, integrable_rpow_mul_cexp_of_re_mem_interior_integrableExpSet
-/
lemma integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
    (hz : z.re in interior (integrableExpSet X μ)) (n : Nat) :
    Integrable (fun ω => X ω ^ n * cexp (z * X ω)) μ := by
  convert! integrable_rpow_mul_cexp_of_re_mem_interior_integrableExpSet hz (Nat.cast_nonneg n)
  simp

end Complex

end IntegrableExpSet

end FiniteMoments

end ProbabilityTheory
