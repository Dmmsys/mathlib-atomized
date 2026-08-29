/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies, Louis (Yiyang) Liu
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integral average of a function

In this file we define `MeasureTheory.average μ f` (notation: `⨍ x, f x ∂μ`) to be the average
value of `f` with respect to measure `μ`. It is defined as `∫ x, f x ∂((μ univ)⁻¹ • μ)`, so it
is equal to zero if `f` is not integrable or if `μ` is an infinite measure. If `μ` is a probability
measure, then the average of any function is equal to its integral.

For the average on a set, we use `⨍ x in s, f x ∂μ` (notation for `⨍ x, f x ∂(μ.restrict s)`). For
average w.r.t. the volume, one can omit `∂volume`.

Both have a version for the Lebesgue integral rather than Bochner.

We prove several versions of the first moment method: An integrable function is below/above its
average on a set of positive measure:
* `measure_le_setLAverage_pos` for the Lebesgue integral
* `measure_le_setAverage_pos` for the Bochner integral

## Implementation notes

The average is defined as an integral over `(μ univ)⁻¹ • μ` so that all theorems about Bochner
integrals work for the average without modifications. For theorems that require integrability of a
function, we provide a convenience lemma `MeasureTheory.Integrable.to_average`.

## Tags

integral, center mass, average value, set average
-/

@[expose] public section


open ENNReal MeasureTheory MeasureTheory.Measure Metric Set Filter TopologicalSpace Function

open scoped Topology ENNReal Convex

variable {α E F : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] {μ ν : Measure α}
  {s t : Set α}

/-!
### Average value of a function w.r.t. a measure

The (Bochner, Lebesgue) average value of a function `f` w.r.t. a measure `μ` (notation:
`⨍ x, f x ∂μ`, `⨍⁻ x, f x ∂μ`) is defined as the (Bochner, Lebesgue) integral divided by the total
measure, so it is equal to zero if `μ` is an infinite measure, and (typically) equal to infinity if
`f` is not integrable. If `μ` is a probability measure, then the average of any function is equal to
its integral.
-/

namespace MeasureTheory
section ENNReal
variable (μ) {f g : α -> Real>=0∞}

/--
Definition of `laverage` / `laverage` 的定义

English:
definition laverage
  signature: (f : α -> Real>=0∞)
  body: ∫⁻ x, f x ∂(μ univ)⁻¹ • μ

中文:
定义 laverage
  签名: (f : α -> 实数>=0∞)
  定义体: ∫⁻ x, f x ∂(μ univ)⁻¹ • μ
-/
noncomputable def laverage (f : α -> Real>=0∞) := ∫⁻ x, f x ∂(μ univ)⁻¹ • μ

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. a measure `μ`.

It is equal to `(μ univ)⁻¹ * ∫⁻ x, f x ∂μ`, so it takes value zero if `μ` is an infinite measure. If
`μ` is a probability measure, then the average of any function is equal to its integral.

For the average on a set, use `⨍⁻ x in s, f x ∂μ`, defined as `⨍⁻ x, f x ∂(μ.restrict s)`. For the
average w.r.t. the volume, one can omit `∂volume`. -/
notation3 "⨍⁻ " (...) ", " r:60:(scoped f => f) " ∂" μ:70 => laverage μ r

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. the standard measure.

It is equal to `(volume univ)⁻¹ * ∫⁻ x, f x`, so it takes value zero if the space has infinite
measure. In a probability space, the average of any function is equal to its integral.

For the average on a set, use `⨍⁻ x in s, f x`, defined as `⨍⁻ x, f x ∂(volume.restrict s)`. -/
notation3 "⨍⁻ " (...) ", " r:60:(scoped f => laverage volume f) => r

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. a measure `μ` on a set `s`.

It is equal to `(μ s)⁻¹ * ∫⁻ x, f x ∂μ`, so it takes value zero if `s` has infinite measure. If `s`
has measure `1`, then the average of any function is equal to its integral.

For the average w.r.t. the volume, one can omit `∂volume`. -/
notation3 "⨍⁻ " (...) " in " s ", " r:60:(scoped f => f) " ∂" μ:70 =>
  laverage (Measure.restrict μ s) r

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. the standard measure on a set `s`.

It is equal to `(volume s)⁻¹ * ∫⁻ x, f x`, so it takes value zero if `s` has infinite measure. If
`s` has measure `1`, then the average of any function is equal to its integral. -/
notation3 (prettyPrint := false)
  "⨍⁻ " (...) " in " s ", " r:60:(scoped f => laverage Measure.restrict volume s f) => r

@[simp]
/--
theorem `laverage_zero` / 定理 `laverage_zero`

English:
theorem laverage_zero
  statement: ⨍⁻ _x, (0 : Real>=0∞) ∂μ = 0
  proof: by rw [laverage, lintegral_zero]

@[simp]

中文:
定理 laverage_zero
  结论: ⨍⁻ _x, (0 : 实数>=0∞) ∂μ = 0
  证明: by rw [laverage, lintegral_zero]

@[simp]

Depends on / 依赖: laverage, lintegral_zero
-/
theorem laverage_zero : ⨍⁻ _x, (0 : Real>=0∞) ∂μ = 0 := by rw [laverage, lintegral_zero]

@[simp]
/--
theorem `laverage_zero_measure` / 定理 `laverage_zero_measure`

English:
theorem laverage_zero_measure
  given: (f : α -> Real>=0∞)
  statement: ⨍⁻ x, f x ∂(0 : Measure α) = 0
  proof: by simp [laverage]

中文:
定理 laverage_zero_measure
  条件: (f : α -> 实数>=0∞)
  结论: ⨍⁻ x, f x ∂(0 : 测度 α) = 0
  证明: by simp [laverage]

Depends on / 依赖: laverage
-/
theorem laverage_zero_measure (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂(0 : Measure α) = 0 := by simp [laverage]

/--
theorem `laverage_eq'` / 定理 `laverage_eq'`

English:
theorem laverage_eq'
  given: (f : α -> Real>=0∞)
  statement: ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂(μ univ)⁻¹ • μ
  proof: rfl

中文:
定理 laverage_eq'
  条件: (f : α -> 实数>=0∞)
  结论: ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂(μ univ)⁻¹ • μ
  证明: rfl
-/
theorem laverage_eq' (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂(μ univ)⁻¹ • μ := rfl

/--
theorem `laverage_eq` / 定理 `laverage_eq`

English:
theorem laverage_eq
  given: (f : α -> Real>=0∞)
  statement: ⨍⁻ x, f x ∂μ = (∫⁻ x, f x ∂μ) / μ univ
  proof: by
  rw [laverage_eq']; rw [lintegral_smul_measure]; rw [ENNReal.div_eq_inv_mul]; rw [smul_eq_mul]

中文:
定理 laverage_eq
  条件: (f : α -> 实数>=0∞)
  结论: ⨍⁻ x, f x ∂μ = (∫⁻ x, f x ∂μ) / μ univ
  证明: by
  rw [laverage_eq']; rw [lintegral_smul_measure]; rw [ENNReal.div_eq_inv_mul]; rw [smul_eq_mul]

Depends on / 依赖: ENNReal, ENNReal.div_eq_inv_mul, div_eq_inv_mul, laverage_eq, lintegral_smul_measure, smul_eq_mul
-/
theorem laverage_eq (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂μ = (∫⁻ x, f x ∂μ) / μ univ := by
  rw [laverage_eq']; rw [lintegral_smul_measure]; rw [ENNReal.div_eq_inv_mul]; rw [smul_eq_mul]

/--
theorem `laverage_eq_lintegral` / 定理 `laverage_eq_lintegral`

English:
theorem laverage_eq_lintegral
  given: [IsProbabilityMeasure μ] (f : α -> Real>=0∞)
  proof: by rw [laverage, measure_univ, inv_one, one_smul]

@[simp]

中文:
定理 laverage_eq_lintegral
  条件: [是概率测度 μ] (f : α -> 实数>=0∞)
  证明: by rw [laverage, measure_univ, inv_one, one_smul]

@[simp]

Depends on / 依赖: inv_one, laverage, measure_univ, one_smul
-/
theorem laverage_eq_lintegral [IsProbabilityMeasure μ] (f : α -> Real>=0∞) :
    ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ := by rw [laverage, measure_univ, inv_one, one_smul]

@[simp]
/--
theorem `measure_mul_laverage` / 定理 `measure_mul_laverage`

English:
theorem measure_mul_laverage
  given: [IsFiniteMeasure μ] (f : α -> Real>=0∞)
  proof: by
  rcases eq_or_ne μ 0 with hμ | hμ
  · rw [hμ, lintegral_zero_measure, laverage_zero_measure, mul_zero]
  · rw [laverage_eq, ENNReal.mul_div_cancel (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)]

中文:
定理 measure_mul_laverage
  条件: [是有限测度 μ] (f : α -> 实数>=0∞)
  证明: by
  rcases eq_or_ne μ 0 with hμ | hμ
  · rw [hμ, lintegral_zero_measure, laverage_zero_measure, mul_zero]
  · rw [laverage_eq, ENNReal.mul_div_cancel (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)]

Depends on / 依赖: ENNReal, ENNReal.mul_div_cancel, eq_or_ne, laverage_eq, laverage_zero_measure, lintegral_zero_measure, measure_ne_top, measure_univ_ne_zero, mul_div_cancel, mul_zero
-/
theorem measure_mul_laverage [IsFiniteMeasure μ] (f : α -> Real>=0∞) :
    μ univ * ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ := by
  rcases eq_or_ne μ 0 with hμ | hμ
  · rw [hμ, lintegral_zero_measure, laverage_zero_measure, mul_zero]
  · rw [laverage_eq, ENNReal.mul_div_cancel (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)]

/--
theorem `setLAverage_eq` / 定理 `setLAverage_eq`

English:
theorem setLAverage_eq
  given: (f : α -> Real>=0∞) (s : Set α)
  proof: by rw [laverage_eq, restrict_apply_univ]

中文:
定理 setLAverage_eq
  条件: (f : α -> 实数>=0∞) (s : 集合 α)
  证明: by rw [laverage_eq, restrict_apply_univ]

Depends on / 依赖: laverage_eq, restrict_apply_univ
-/
theorem setLAverage_eq (f : α -> Real>=0∞) (s : Set α) :
    ⨍⁻ x in s, f x ∂μ = (∫⁻ x in s, f x ∂μ) / μ s := by rw [laverage_eq, restrict_apply_univ]

/--
theorem `setLAverage_eq'` / 定理 `setLAverage_eq'`

English:
theorem setLAverage_eq'
  given: (f : α -> Real>=0∞) (s : Set α)
  proof: by
  simp only [laverage_eq', restrict_apply_univ]

中文:
定理 setLAverage_eq'
  条件: (f : α -> 实数>=0∞) (s : 集合 α)
  证明: by
  simp only [laverage_eq', restrict_apply_univ]

Depends on / 依赖: laverage_eq, restrict_apply_univ
-/
theorem setLAverage_eq' (f : α -> Real>=0∞) (s : Set α) :
    ⨍⁻ x in s, f x ∂μ = ∫⁻ x, f x ∂(μ s)⁻¹ • μ.restrict s := by
  simp only [laverage_eq', restrict_apply_univ]

variable {μ}

/--
theorem `laverage_congr` / 定理 `laverage_congr`

English:
theorem laverage_congr
  given: {f g : α -> Real>=0∞} (h : f =ᵐ[μ] g)
  statement: ⨍⁻ x, f x ∂μ = ⨍⁻ x, g x ∂μ
  proof: by
  simp only [laverage_eq, lintegral_congr_ae h]

中文:
定理 laverage_congr
  条件: {f g : α -> 实数>=0∞} (h : f =ᵐ[μ] g)
  结论: ⨍⁻ x, f x ∂μ = ⨍⁻ x, g x ∂μ
  证明: by
  simp only [laverage_eq, lintegral_congr_ae h]

Depends on / 依赖: laverage_eq, lintegral_congr_ae
-/
theorem laverage_congr {f g : α -> Real>=0∞} (h : f =ᵐ[μ] g) : ⨍⁻ x, f x ∂μ = ⨍⁻ x, g x ∂μ := by
  simp only [laverage_eq, lintegral_congr_ae h]

/--
theorem `setLAverage_congr` / 定理 `setLAverage_congr`

English:
theorem setLAverage_congr
  given: (h : s =ᵐ[μ] t)
  statement: ⨍⁻ x in s, f x ∂μ = ⨍⁻ x in t, f x ∂μ
  proof: by
  simp only [setLAverage_eq, setLIntegral_congr h, measure_congr h]

中文:
定理 setLAverage_congr
  条件: (h : s =ᵐ[μ] t)
  结论: ⨍⁻ x in s, f x ∂μ = ⨍⁻ x in t, f x ∂μ
  证明: by
  simp only [setLAverage_eq, setLIntegral_congr h, measure_congr h]

Depends on / 依赖: measure_congr, setLAverage_eq, setLIntegral_congr
-/
theorem setLAverage_congr (h : s =ᵐ[μ] t) : ⨍⁻ x in s, f x ∂μ = ⨍⁻ x in t, f x ∂μ := by
  simp only [setLAverage_eq, setLIntegral_congr h, measure_congr h]

/--
theorem `setLAverage_congr_fun_ae` / 定理 `setLAverage_congr_fun_ae`

English:
theorem setLAverage_congr_fun_ae
  given: (hs : MeasurableSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x)
  proof: by
  simp only [laverage_eq, setLIntegral_congr_fun_ae hs h]

中文:
定理 setLAverage_congr_fun_ae
  条件: (hs : 可测集 s) (h : 对任意ᵐ x ∂μ, x in s -> f x = g x)
  证明: by
  simp only [laverage_eq, setLIntegral_congr_fun_ae hs h]

Depends on / 依赖: laverage_eq, setLIntegral_congr_fun_ae
-/
theorem setLAverage_congr_fun_ae (hs : MeasurableSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) :
    ⨍⁻ x in s, f x ∂μ = ⨍⁻ x in s, g x ∂μ := by
  simp only [laverage_eq, setLIntegral_congr_fun_ae hs h]

/--
theorem `setLAverage_congr_fun` / 定理 `setLAverage_congr_fun`

English:
theorem setLAverage_congr_fun
  given: (hs : MeasurableSet s) (h : EqOn f g s)
  proof: by
  simp only [laverage_eq, setLIntegral_congr_fun hs h]

中文:
定理 setLAverage_congr_fun
  条件: (hs : 可测集 s) (h : EqOn f g s)
  证明: by
  simp only [laverage_eq, setLIntegral_congr_fun hs h]

Depends on / 依赖: laverage_eq, setLIntegral_congr_fun
-/
theorem setLAverage_congr_fun (hs : MeasurableSet s) (h : EqOn f g s) :
    ⨍⁻ x in s, f x ∂μ = ⨍⁻ x in s, g x ∂μ := by
  simp only [laverage_eq, setLIntegral_congr_fun hs h]

/--
theorem `laverage_lt_top` / 定理 `laverage_lt_top`

English:
theorem laverage_lt_top
  given: (hf : ∫⁻ x, f x ∂μ != ∞)
  statement: ⨍⁻ x, f x ∂μ < ∞
  proof: by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [laverage_eq]
    finiteness [measure_univ_ne_zero.2 hμ]

中文:
定理 laverage_lt_top
  条件: (hf : ∫⁻ x, f x ∂μ != ∞)
  结论: ⨍⁻ x, f x ∂μ < ∞
  证明: by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [laverage_eq]
    finiteness [measure_univ_ne_zero.2 hμ]

Depends on / 依赖: eq_or_ne, finiteness, laverage_eq, measure_univ_ne_zero
-/
theorem laverage_lt_top (hf : ∫⁻ x, f x ∂μ != ∞) : ⨍⁻ x, f x ∂μ < ∞ := by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [laverage_eq]
    finiteness [measure_univ_ne_zero.2 hμ]

/--
theorem `setLAverage_lt_top` / 定理 `setLAverage_lt_top`

English:
theorem setLAverage_lt_top
  statement: ∫⁻ x in s, f x ∂μ != ∞ -> ⨍⁻ x in s, f x ∂μ < ∞
  proof: laverage_lt_top

中文:
定理 setLAverage_lt_top
  结论: ∫⁻ x in s, f x ∂μ != ∞ -> ⨍⁻ x in s, f x ∂μ < ∞
  证明: laverage_lt_top

Depends on / 依赖: laverage_lt_top
-/
theorem setLAverage_lt_top : ∫⁻ x in s, f x ∂μ != ∞ -> ⨍⁻ x in s, f x ∂μ < ∞ :=
  laverage_lt_top

/--
theorem `laverage_add_measure` / 定理 `laverage_add_measure`

English:
theorem laverage_add_measure
  proof: by
  by_cases hμ : IsFiniteMeasure μ; swap
  · rw [not_isFiniteMeasure_iff] at hμ
    simp [laverage_eq, hμ]
  by_cases hν : IsFiniteMeasure ν; swap
  · rw [not_isFiniteMeasure_iff] at hν
    simp [laverage_eq, hν]
  simp only [← ENNReal.mul_div_right_comm, measure_mul_laverage, ← ENNReal.add_div,
    ← lintegral_add_measure, ← Measure.add_apply, ← laverage_eq]

中文:
定理 laverage_add_measure
  证明: by
  by_cases hμ : IsFiniteMeasure μ; swap
  · rw [not_isFiniteMeasure_iff] at hμ
    simp [laverage_eq, hμ]
  by_cases hν : IsFiniteMeasure ν; swap
  · rw [not_isFiniteMeasure_iff] at hν
    simp [laverage_eq, hν]
  simp only [← ENNReal.mul_div_right_comm, measure_mul_laverage, ← ENNReal.add_div,
    ← lintegral_add_measure, ← Measure.add_apply, ← laverage_eq]

Depends on / 依赖: ENNReal, ENNReal.add_div, ENNReal.mul_div_right_comm, IsFiniteMeasure, Measure, Measure.add_apply, add_apply, add_div, laverage_eq, lintegral_add_measure, measure_mul_laverage, mul_div_right_comm, not_isFiniteMeasure_iff
-/
theorem laverage_add_measure :
    ⨍⁻ x, f x ∂(μ + ν) =
      μ univ / (μ univ + ν univ) * ⨍⁻ x, f x ∂μ + ν univ / (μ univ + ν univ) * ⨍⁻ x, f x ∂ν := by
  by_cases hμ : IsFiniteMeasure μ; swap
  · rw [not_isFiniteMeasure_iff] at hμ
    simp [laverage_eq, hμ]
  by_cases hν : IsFiniteMeasure ν; swap
  · rw [not_isFiniteMeasure_iff] at hν
    simp [laverage_eq, hν]
  simp only [← ENNReal.mul_div_right_comm, measure_mul_laverage, ← ENNReal.add_div,
    ← lintegral_add_measure, ← Measure.add_apply, ← laverage_eq]

/--
theorem `measure_mul_setLAverage` / 定理 `measure_mul_setLAverage`

English:
theorem measure_mul_setLAverage
  given: (f : α -> Real>=0∞) (h : μ s != ∞)
  proof: by
  have := Fact.mk h.lt_top
  rw [← measure_mul_laverage]; rw [restrict_apply_univ]

中文:
定理 measure_mul_setLAverage
  条件: (f : α -> 实数>=0∞) (h : μ s != ∞)
  证明: by
  have := Fact.mk h.lt_top
  rw [← measure_mul_laverage]; rw [restrict_apply_univ]

Depends on / 依赖: Fact.mk, h.lt_top, lt_top, measure_mul_laverage, restrict_apply_univ
-/
theorem measure_mul_setLAverage (f : α -> Real>=0∞) (h : μ s != ∞) :
    μ s * ⨍⁻ x in s, f x ∂μ = ∫⁻ x in s, f x ∂μ := by
  have := Fact.mk h.lt_top
  rw [← measure_mul_laverage]; rw [restrict_apply_univ]

/--
theorem `laverage_union` / 定理 `laverage_union`

English:
theorem laverage_union
  given: (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
  proof: by
  rw [restrict_union₀ hd ht]; rw [laverage_add_measure]; rw [restrict_apply_univ]; rw [restrict_apply_univ]

中文:
定理 laverage_union
  条件: (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
  证明: by
  rw [restrict_union₀ hd ht]; rw [laverage_add_measure]; rw [restrict_apply_univ]; rw [restrict_apply_univ]

Depends on / 依赖: laverage_add_measure, restrict_apply_univ
-/
theorem laverage_union (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ) :
    ⨍⁻ x in s union t, f x ∂μ =
      μ s / (μ s + μ t) * ⨍⁻ x in s, f x ∂μ + μ t / (μ s + μ t) * ⨍⁻ x in t, f x ∂μ := by
  rw [restrict_union₀ hd ht]; rw [laverage_add_measure]; rw [restrict_apply_univ]; rw [restrict_apply_univ]

/--
theorem `laverage_union_mem_openSegment` / 定理 `laverage_union_mem_openSegment`

English:
theorem laverage_union_mem_openSegment
  statement: (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
  proof: by
  refine
⟨μ s / (μ s + μ t), μ t / (μ s + μ t), ENNReal.div_pos hs₀ add_ne_top.2 ⟨hsμ, htμ⟩,
ENNReal.div_pos ht₀ add_ne_top.2 ⟨hsμ, htμ⟩, ?_, (laverage_union hd ht).symm⟩
  rw [← ENNReal.add_div]; rw [ENNReal.div_self (add_eq_zero.not.2 fun h => hs₀ h.1) (add_ne_top.2 ⟨hsμ]; rw [htμ⟩)]

中文:
定理 laverage_union_mem_openSegment
  结论: (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
  证明: by
  refine
⟨μ s / (μ s + μ t), μ t / (μ s + μ t), ENNReal.div_pos hs₀ add_ne_top.2 ⟨hsμ, htμ⟩,
ENNReal.div_pos ht₀ add_ne_top.2 ⟨hsμ, htμ⟩, ?_, (laverage_union hd ht).symm⟩
  rw [← ENNReal.add_div]; rw [ENNReal.div_self (add_eq_zero.not.2 fun h => hs₀ h.1) (add_ne_top.2 ⟨hsμ]; rw [htμ⟩)]

Depends on / 依赖: ENNReal, ENNReal.add_div, ENNReal.div_pos, ENNReal.div_self, add_div, add_eq_zero, add_eq_zero.not, add_ne_top, div_pos, div_self, laverage_union
-/
theorem laverage_union_mem_openSegment (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hs₀ : μ s != 0) (ht₀ : μ t != 0) (hsμ : μ s != ∞) (htμ : μ t != ∞) :
    ⨍⁻ x in s union t, f x ∂μ in openSegment Real>=0∞ (⨍⁻ x in s, f x ∂μ) (⨍⁻ x in t, f x ∂μ) := by
  refine
⟨μ s / (μ s + μ t), μ t / (μ s + μ t), ENNReal.div_pos hs₀ add_ne_top.2 ⟨hsμ, htμ⟩,
ENNReal.div_pos ht₀ add_ne_top.2 ⟨hsμ, htμ⟩, ?_, (laverage_union hd ht).symm⟩
  rw [← ENNReal.add_div]; rw [ENNReal.div_self (add_eq_zero.not.2 fun h => hs₀ h.1) (add_ne_top.2 ⟨hsμ]; rw [htμ⟩)]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `laverage_union_mem_segment` / 定理 `laverage_union_mem_segment`

English:
theorem laverage_union_mem_segment
  statement: (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
  proof: by
  by_cases hs₀ : μ s = 0
  · rw [← ae_eq_empty] at hs₀
    rw [restrict_congr_set (hs₀.union EventuallyEq.rfl)]; rw [empty_union]
    exact right_mem_segment _ _ _
  · refine
      ⟨μ s / (μ s + μ t), μ t / (μ s + μ t), zero_le, zero_le, ?_, (laverage_union hd ht).symm⟩
    rw [← ENNReal.add_div]; rw [ENNReal.div_self (add_eq_zero.not.2 fun h => hs₀ h.1) (add_ne_top.2 ⟨hsμ]; rw [htμ⟩)]

中文:
定理 laverage_union_mem_segment
  结论: (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
  证明: by
  by_cases hs₀ : μ s = 0
  · rw [← ae_eq_empty] at hs₀
    rw [restrict_congr_set (hs₀.union EventuallyEq.rfl)]; rw [empty_union]
    exact right_mem_segment _ _ _
  · refine
      ⟨μ s / (μ s + μ t), μ t / (μ s + μ t), zero_le, zero_le, ?_, (laverage_union hd ht).symm⟩
    rw [← ENNReal.add_div]; rw [ENNReal.div_self (add_eq_zero.not.2 fun h => hs₀ h.1) (add_ne_top.2 ⟨hsμ]; rw [htμ⟩)]

Depends on / 依赖: ENNReal, ENNReal.add_div, ENNReal.div_self, EventuallyEq, EventuallyEq.rfl, add_div, add_eq_zero, add_eq_zero.not, add_ne_top, ae_eq_empty, div_self, empty_union, laverage_union, restrict_congr_set, right_mem_segment, zero_le
-/
theorem laverage_union_mem_segment (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hsμ : μ s != ∞) (htμ : μ t != ∞) :
    ⨍⁻ x in s union t, f x ∂μ in [⨍⁻ x in s, f x ∂μ -[Real>=0∞] ⨍⁻ x in t, f x ∂μ] := by
  by_cases hs₀ : μ s = 0
  · rw [← ae_eq_empty] at hs₀
    rw [restrict_congr_set (hs₀.union EventuallyEq.rfl)]; rw [empty_union]
    exact right_mem_segment _ _ _
  · refine
      ⟨μ s / (μ s + μ t), μ t / (μ s + μ t), zero_le, zero_le, ?_, (laverage_union hd ht).symm⟩
    rw [← ENNReal.add_div]; rw [ENNReal.div_self (add_eq_zero.not.2 fun h => hs₀ h.1) (add_ne_top.2 ⟨hsμ]; rw [htμ⟩)]

/--
theorem `laverage_mem_openSegment_compl_self` / 定理 `laverage_mem_openSegment_compl_self`

English:
theorem laverage_mem_openSegment_compl_self
  statement: [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ)
  proof: by
  simpa only [union_compl_self, restrict_univ] using
    laverage_union_mem_openSegment aedisjoint_compl_right hs.compl hs₀ hsc₀ (measure_ne_top _ _)
      (measure_ne_top _ _)

@[simp]

中文:
定理 laverage_mem_openSegment_compl_self
  结论: [是有限测度 μ] (hs : NullMeasurableSet s μ)
  证明: by
  simpa only [union_compl_self, restrict_univ] using
    laverage_union_mem_openSegment aedisjoint_compl_right hs.compl hs₀ hsc₀ (measure_ne_top _ _)
      (measure_ne_top _ _)

@[simp]

Depends on / 依赖: aedisjoint_compl_right, hs.compl, laverage_union_mem_openSegment, measure_ne_top, restrict_univ, union_compl_self
-/
theorem laverage_mem_openSegment_compl_self [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ)
    (hs₀ : μ s != 0) (hsc₀ : μ sᶜ != 0) :
    ⨍⁻ x, f x ∂μ in openSegment Real>=0∞ (⨍⁻ x in s, f x ∂μ) (⨍⁻ x in sᶜ, f x ∂μ) := by
  simpa only [union_compl_self, restrict_univ] using
    laverage_union_mem_openSegment aedisjoint_compl_right hs.compl hs₀ hsc₀ (measure_ne_top _ _)
      (measure_ne_top _ _)

@[simp]
/--
theorem `laverage_const` / 定理 `laverage_const`

English:
theorem laverage_const
  given: (μ : Measure α) [IsFiniteMeasure μ] [h : NeZero μ] (c : Real>=0∞)
  proof: by
  simp only [laverage, lintegral_const, measure_univ, mul_one]

中文:
定理 laverage_const
  条件: (μ : 测度 α) [是有限测度 μ] [h : NeZero μ] (c : 实数>=0∞)
  证明: by
  simp only [laverage, lintegral_const, measure_univ, mul_one]

Depends on / 依赖: laverage, lintegral_const, measure_univ, mul_one
-/
theorem laverage_const (μ : Measure α) [IsFiniteMeasure μ] [h : NeZero μ] (c : Real>=0∞) :
    ⨍⁻ _x, c ∂μ = c := by
  simp only [laverage, lintegral_const, measure_univ, mul_one]

/--
theorem `setLAverage_const` / 定理 `setLAverage_const`

English:
theorem setLAverage_const
  given: (hs₀ : μ s != 0) (hs : μ s != ∞) (c : Real>=0∞)
  statement: ⨍⁻ _x in s, c ∂μ = c
  proof: by
  simp only [setLAverage_eq, lintegral_const, Measure.restrict_apply, MeasurableSet.univ,
    univ_inter, div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hs₀ hs, mul_one]

中文:
定理 setLAverage_const
  条件: (hs₀ : μ s != 0) (hs : μ s != ∞) (c : 实数>=0∞)
  结论: ⨍⁻ _x in s, c ∂μ = c
  证明: by
  simp only [setLAverage_eq, lintegral_const, Measure.restrict_apply, MeasurableSet.univ,
    univ_inter, div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hs₀ hs, mul_one]

Depends on / 依赖: ENNReal, ENNReal.mul_inv_cancel, MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_apply, div_eq_mul_inv, lintegral_const, mul_assoc, mul_inv_cancel, mul_one, restrict_apply, setLAverage_eq, univ_inter
-/
theorem setLAverage_const (hs₀ : μ s != 0) (hs : μ s != ∞) (c : Real>=0∞) : ⨍⁻ _x in s, c ∂μ = c := by
  simp only [setLAverage_eq, lintegral_const, Measure.restrict_apply, MeasurableSet.univ,
    univ_inter, div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hs₀ hs, mul_one]

/--
theorem `laverage_one` / 定理 `laverage_one`

English:
theorem laverage_one
  given: [IsFiniteMeasure μ] [NeZero μ]
  statement: ⨍⁻ _x, (1 : Real>=0∞) ∂μ = 1
  proof: laverage_const _ _

中文:
定理 laverage_one
  条件: [是有限测度 μ] [NeZero μ]
  结论: ⨍⁻ _x, (1 : 实数>=0∞) ∂μ = 1
  证明: laverage_const _ _

Depends on / 依赖: laverage_const
-/
theorem laverage_one [IsFiniteMeasure μ] [NeZero μ] : ⨍⁻ _x, (1 : Real>=0∞) ∂μ = 1 :=
  laverage_const _ _

/--
theorem `setLAverage_one` / 定理 `setLAverage_one`

English:
theorem setLAverage_one
  given: (hs₀ : μ s != 0) (hs : μ s != ∞)
  statement: ⨍⁻ _x in s, (1 : Real>=0∞) ∂μ = 1
  proof: setLAverage_const hs₀ hs _

@[simp]

中文:
定理 setLAverage_one
  条件: (hs₀ : μ s != 0) (hs : μ s != ∞)
  结论: ⨍⁻ _x in s, (1 : 实数>=0∞) ∂μ = 1
  证明: setLAverage_const hs₀ hs _

@[simp]

Depends on / 依赖: setLAverage_const
-/
theorem setLAverage_one (hs₀ : μ s != 0) (hs : μ s != ∞) : ⨍⁻ _x in s, (1 : Real>=0∞) ∂μ = 1 :=
  setLAverage_const hs₀ hs _

@[simp]
/--
theorem `laverage_mul_measure_univ` / 定理 `laverage_mul_measure_univ`

English:
theorem laverage_mul_measure_univ
  given: (μ : Measure α) [IsFiniteMeasure μ] (f : α -> Real>=0∞)
  proof: by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [laverage_eq, ENNReal.div_mul_cancel (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)]

中文:
定理 laverage_mul_measure_univ
  条件: (μ : 测度 α) [是有限测度 μ] (f : α -> 实数>=0∞)
  证明: by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [laverage_eq, ENNReal.div_mul_cancel (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)]

Depends on / 依赖: ENNReal, ENNReal.div_mul_cancel, div_mul_cancel, eq_or_ne, laverage_eq, measure_ne_top, measure_univ_ne_zero
-/
theorem laverage_mul_measure_univ (μ : Measure α) [IsFiniteMeasure μ] (f : α -> Real>=0∞) :
    (⨍⁻ (a : α), f a ∂μ) * μ univ = ∫⁻ x, f x ∂μ := by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [laverage_eq, ENNReal.div_mul_cancel (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)]

/--
theorem `lintegral_laverage` / 定理 `lintegral_laverage`

English:
theorem lintegral_laverage
  given: (μ : Measure α) [IsFiniteMeasure μ] (f : α -> Real>=0∞)
  proof: by
  simp

中文:
定理 lintegral_laverage
  条件: (μ : 测度 α) [是有限测度 μ] (f : α -> 实数>=0∞)
  证明: by
  simp
-/
theorem lintegral_laverage (μ : Measure α) [IsFiniteMeasure μ] (f : α -> Real>=0∞) :
    ∫⁻ _x, ⨍⁻ a, f a ∂μ ∂μ = ∫⁻ x, f x ∂μ := by
  simp

/--
theorem `setLIntegral_setLAverage` / 定理 `setLIntegral_setLAverage`

English:
theorem setLIntegral_setLAverage
  given: (μ : Measure α) [IsFiniteMeasure μ] (f : α -> Real>=0∞) (s : Set α)
  proof: lintegral_laverage _ _

@[gcongr]

中文:
定理 setL整数egral_setLAverage
  条件: (μ : 测度 α) [是有限测度 μ] (f : α -> 实数>=0∞) (s : 集合 α)
  证明: lintegral_laverage _ _

@[gcongr]

Depends on / 依赖: lintegral_laverage
-/
theorem setLIntegral_setLAverage (μ : Measure α) [IsFiniteMeasure μ] (f : α -> Real>=0∞) (s : Set α) :
    ∫⁻ _x in s, ⨍⁻ a in s, f a ∂μ ∂μ = ∫⁻ x in s, f x ∂μ :=
  lintegral_laverage _ _

@[gcongr]
/--
theorem `laverage_mono_ae` / 定理 `laverage_mono_ae`

English:
theorem laverage_mono_ae
  given: (h : f <=ᶠ[ae μ] g)
  proof: lintegral_mono_ae h.filter_mono Measure.ae_mono' Measure.smul_absolutelyContinuous

@[gcongr]

中文:
定理 laverage_mono_ae
  条件: (h : f <=ᶠ[ae μ] g)
  证明: lintegral_mono_ae h.filter_mono Measure.ae_mono' Measure.smul_absolutelyContinuous

@[gcongr]

Depends on / 依赖: Measure, Measure.ae_mono, Measure.smul_absolutelyContinuous, ae_mono, filter_mono, h.filter_mono, lintegral_mono_ae, smul_absolutelyContinuous
-/
theorem laverage_mono_ae (h : f <=ᶠ[ae μ] g) :
    ⨍⁻ a, f a ∂μ <= ⨍⁻ a, g a ∂μ :=
lintegral_mono_ae h.filter_mono Measure.ae_mono' Measure.smul_absolutelyContinuous

@[gcongr]
/--
theorem `setLAverage_mono_ae` / 定理 `setLAverage_mono_ae`

English:
theorem setLAverage_mono_ae
  given: (s : Set α) (h : f <=ᶠ[ae μ] g)
  proof: laverage_mono_ae h.filter_mono ae_mono Measure.restrict_le_self

中文:
定理 setLAverage_mono_ae
  条件: (s : 集合 α) (h : f <=ᶠ[ae μ] g)
  证明: laverage_mono_ae h.filter_mono ae_mono Measure.restrict_le_self

Depends on / 依赖: Measure, Measure.restrict_le_self, ae_mono, filter_mono, h.filter_mono, laverage_mono_ae, restrict_le_self
-/
theorem setLAverage_mono_ae (s : Set α) (h : f <=ᶠ[ae μ] g) :
    ⨍⁻ a in s, f a ∂μ <= ⨍⁻ a in s, g a ∂μ :=
laverage_mono_ae h.filter_mono ae_mono Measure.restrict_le_self

/--
theorem `setLAverage_le_essSup` / 定理 `setLAverage_le_essSup`

English:
theorem setLAverage_le_essSup
  given: (s : Set α) (f : α -> Real>=0∞)
  statement: ⨍⁻ x in s, f x ∂μ <= essSup f μ
  proof: by
  by_cases hμ : IsFiniteMeasure (μ.restrict s); swap
  · simp [laverage, not_isFiniteMeasure_iff.mp hμ]
  by_cases hμ0 : μ s = 0
  · rw [laverage, ← setLIntegral_univ]
    exact le_of_eq_of_le (setLIntegral_measure_zero univ f <| by simp [hμ0]) zero_le
  apply le_of_le_of_eq (laverage_mono_ae <| Eventually.filter_mono ae_restrict_le ae_le_essSup)
  have : NeZero (μ.restrict s) :=
    have : NeZero (μ s) := { out := hμ0 }
    restrict.neZero
  exact laverage_const (μ.restrict s) _

中文:
定理 setLAverage_le_essSup
  条件: (s : 集合 α) (f : α -> 实数>=0∞)
  结论: ⨍⁻ x in s, f x ∂μ <= essSup f μ
  证明: by
  by_cases hμ : IsFiniteMeasure (μ.restrict s); swap
  · simp [laverage, not_isFiniteMeasure_iff.mp hμ]
  by_cases hμ0 : μ s = 0
  · rw [laverage, ← setLIntegral_univ]
    exact le_of_eq_of_le (setLIntegral_measure_zero univ f <| by simp [hμ0]) zero_le
  apply le_of_le_of_eq (laverage_mono_ae <| Eventually.filter_mono ae_restrict_le ae_le_essSup)
  have : NeZero (μ.restrict s) :=
    have : NeZero (μ s) := { out := hμ0 }
    restrict.neZero
  exact laverage_const (μ.restrict s) _

Depends on / 依赖: Eventually, Eventually.filter_mono, IsFiniteMeasure, NeZero, ae_le_essSup, ae_restrict_le, filter_mono, laverage, laverage_const, laverage_mono_ae, le_of_eq_of_le, le_of_le_of_eq, neZero, not_isFiniteMeasure_iff, not_isFiniteMeasure_iff.mp, restrict, restrict.neZero, setLIntegral_measure_zero, setLIntegral_univ, zero_le
-/
theorem setLAverage_le_essSup (s : Set α) (f : α -> Real>=0∞) : ⨍⁻ x in s, f x ∂μ <= essSup f μ := by
  by_cases hμ : IsFiniteMeasure (μ.restrict s); swap
  · simp [laverage, not_isFiniteMeasure_iff.mp hμ]
  by_cases hμ0 : μ s = 0
  · rw [laverage, ← setLIntegral_univ]
    exact le_of_eq_of_le (setLIntegral_measure_zero univ f <| by simp [hμ0]) zero_le
  apply le_of_le_of_eq (laverage_mono_ae <| Eventually.filter_mono ae_restrict_le ae_le_essSup)
  have : NeZero (μ.restrict s) :=
    have : NeZero (μ s) := { out := hμ0 }
    restrict.neZero
  exact laverage_const (μ.restrict s) _

/--
theorem `laverage_le_essSup` / 定理 `laverage_le_essSup`

English:
theorem laverage_le_essSup
  given: (f : α -> Real>=0∞)
  statement: ⨍⁻ x, f x ∂μ <= essSup f μ
  proof: by
  simpa using setLAverage_le_essSup univ f

中文:
定理 laverage_le_essSup
  条件: (f : α -> 实数>=0∞)
  结论: ⨍⁻ x, f x ∂μ <= essSup f μ
  证明: by
  simpa using setLAverage_le_essSup univ f

Depends on / 依赖: setLAverage_le_essSup
-/
theorem laverage_le_essSup (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂μ <= essSup f μ := by
  simpa using setLAverage_le_essSup univ f

end ENNReal

section NormedAddCommGroup

variable (μ)
variable {f g : α -> E}

/--
Definition of `average` / `average` 的定义

English:
definition average
  signature: (f : α -> E)
  body: ∫ x, f x ∂(μ univ)⁻¹ • μ

中文:
定义 average
  签名: (f : α -> E)
  定义体: ∫ x, f x ∂(μ univ)⁻¹ • μ
-/
noncomputable def average (f : α -> E) :=
  ∫ x, f x ∂(μ univ)⁻¹ • μ

/-- Average value of a function `f` w.r.t. a measure `μ`.

It is equal to `(μ.real univ)⁻¹ • ∫ x, f x ∂μ`, so it takes value zero if `f` is not integrable or
if `μ` is an infinite measure. If `μ` is a probability measure, then the average of any function is
equal to its integral.

For the average on a set, use `⨍ x in s, f x ∂μ`, defined as `⨍ x, f x ∂(μ.restrict s)`. For the
average w.r.t. the volume, one can omit `∂volume`. -/
notation3 "⨍ " (...) ", " r:60:(scoped f => f) " ∂" μ:70 => average μ r

/-- Average value of a function `f` w.r.t. the standard measure.

It is equal to `(volume.real univ)⁻¹ * ∫ x, f x`, so it takes value zero if `f` is not integrable
or if the space has infinite measure. In a probability space, the average of any function is equal
to its integral.

For the average on a set, use `⨍ x in s, f x`, defined as `⨍ x, f x ∂(volume.restrict s)`. -/
notation3 "⨍ " (...) ", " r:60:(scoped f => average volume f) => r

/-- Average value of a function `f` w.r.t. a measure `μ` on a set `s`.

It is equal to `(μ.real s)⁻¹ * ∫ x, f x ∂μ`, so it takes value zero if `f` is not integrable on
`s` or if `s` has infinite measure. If `s` has measure `1`, then the average of any function is
equal to its integral.

For the average w.r.t. the volume, one can omit `∂volume`. -/
notation3 "⨍ " (...) " in " s ", " r:60:(scoped f => f) " ∂" μ:70 =>
  average (Measure.restrict μ s) r

/-- Average value of a function `f` w.r.t. the standard measure on a set `s`.

It is equal to `(volume.real s)⁻¹ * ∫ x, f x`, so it takes value zero `f` is not integrable on `s`
or if `s` has infinite measure. If `s` has measure `1`, then the average of any function is equal to
its integral. -/
notation3 "⨍ " (...) " in " s ", " r:60:(scoped f => average (Measure.restrict volume s) f) => r

@[simp]
/--
theorem `average_zero` / 定理 `average_zero`

English:
theorem average_zero
  statement: ⨍ _, (0 : E) ∂μ = 0
  proof: by rw [average, integral_zero]

@[simp]

中文:
定理 average_zero
  结论: ⨍ _, (0 : E) ∂μ = 0
  证明: by rw [average, integral_zero]

@[simp]

Depends on / 依赖: average, integral_zero
-/
theorem average_zero : ⨍ _, (0 : E) ∂μ = 0 := by rw [average, integral_zero]

@[simp]
/--
theorem `average_zero_measure` / 定理 `average_zero_measure`

English:
theorem average_zero_measure
  given: (f : α -> E)
  statement: ⨍ x, f x ∂(0 : Measure α) = 0
  proof: by
  rw [average]; rw [smul_zero]; rw [integral_zero_measure]

@[simp]

中文:
定理 average_zero_measure
  条件: (f : α -> E)
  结论: ⨍ x, f x ∂(0 : 测度 α) = 0
  证明: by
  rw [average]; rw [smul_zero]; rw [integral_zero_measure]

@[simp]

Depends on / 依赖: average, integral_zero_measure, smul_zero
-/
theorem average_zero_measure (f : α -> E) : ⨍ x, f x ∂(0 : Measure α) = 0 := by
  rw [average]; rw [smul_zero]; rw [integral_zero_measure]

@[simp]
/--
theorem `average_neg` / 定理 `average_neg`

English:
theorem average_neg
  given: (f : α -> E)
  statement: ⨍ x, -f x ∂μ = -⨍ x, f x ∂μ
  proof: integral_neg f

中文:
定理 average_neg
  条件: (f : α -> E)
  结论: ⨍ x, -f x ∂μ = -⨍ x, f x ∂μ
  证明: integral_neg f

Depends on / 依赖: integral_neg
-/
theorem average_neg (f : α -> E) : ⨍ x, -f x ∂μ = -⨍ x, f x ∂μ :=
  integral_neg f

/--
theorem `average_eq'` / 定理 `average_eq'`

English:
theorem average_eq'
  given: (f : α -> E)
  statement: ⨍ x, f x ∂μ = ∫ x, f x ∂(μ univ)⁻¹ • μ
  proof: rfl

中文:
定理 average_eq'
  条件: (f : α -> E)
  结论: ⨍ x, f x ∂μ = ∫ x, f x ∂(μ univ)⁻¹ • μ
  证明: rfl
-/
theorem average_eq' (f : α -> E) : ⨍ x, f x ∂μ = ∫ x, f x ∂(μ univ)⁻¹ • μ :=
  rfl

/--
theorem `average_eq` / 定理 `average_eq`

English:
theorem average_eq
  given: (f : α -> E)
  statement: ⨍ x, f x ∂μ = (μ.real univ)⁻¹ • ∫ x, f x ∂μ
  proof: by
  rw [average_eq']; rw [integral_smul_measure]; rw [ENNReal.toReal_inv]; rw [measureReal_def]

中文:
定理 average_eq
  条件: (f : α -> E)
  结论: ⨍ x, f x ∂μ = (μ.real univ)⁻¹ • ∫ x, f x ∂μ
  证明: by
  rw [average_eq']; rw [integral_smul_measure]; rw [ENNReal.toReal_inv]; rw [measureReal_def]

Depends on / 依赖: ENNReal, ENNReal.toReal_inv, average_eq, integral_smul_measure, measureReal_def, toReal_inv
-/
theorem average_eq (f : α -> E) : ⨍ x, f x ∂μ = (μ.real univ)⁻¹ • ∫ x, f x ∂μ := by
  rw [average_eq']; rw [integral_smul_measure]; rw [ENNReal.toReal_inv]; rw [measureReal_def]

/--
theorem `average_eq_integral` / 定理 `average_eq_integral`

English:
theorem average_eq_integral
  given: [IsProbabilityMeasure μ] (f : α -> E)
  statement: ⨍ x, f x ∂μ = ∫ x, f x ∂μ
  proof: by
  rw [average]; rw [measure_univ]; rw [inv_one]; rw [one_smul]

@[simp]

中文:
定理 average_eq_integral
  条件: [是概率测度 μ] (f : α -> E)
  结论: ⨍ x, f x ∂μ = ∫ x, f x ∂μ
  证明: by
  rw [average]; rw [measure_univ]; rw [inv_one]; rw [one_smul]

@[simp]

Depends on / 依赖: average, inv_one, measure_univ, one_smul
-/
theorem average_eq_integral [IsProbabilityMeasure μ] (f : α -> E) : ⨍ x, f x ∂μ = ∫ x, f x ∂μ := by
  rw [average]; rw [measure_univ]; rw [inv_one]; rw [one_smul]

@[simp]
/--
theorem `measure_smul_average` / 定理 `measure_smul_average`

English:
theorem measure_smul_average
  given: [IsFiniteMeasure μ] (f : α -> E)
  proof: by
  rcases eq_or_ne μ 0 with hμ | hμ
  · rw [hμ, integral_zero_measure, average_zero_measure, smul_zero]
  · rw [average_eq, smul_inv_smul₀]
    refine (ENNReal.toReal_pos ?_ <| measure_ne_top _ _).ne'
    rwa [Ne, measure_univ_eq_zero]

中文:
定理 measure_smul_average
  条件: [是有限测度 μ] (f : α -> E)
  证明: by
  rcases eq_or_ne μ 0 with hμ | hμ
  · rw [hμ, integral_zero_measure, average_zero_measure, smul_zero]
  · rw [average_eq, smul_inv_smul₀]
    refine (ENNReal.toReal_pos ?_ <| measure_ne_top _ _).ne'
    rwa [Ne, measure_univ_eq_zero]

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, average_eq, average_zero_measure, eq_or_ne, integral_zero_measure, measure_ne_top, measure_univ_eq_zero, smul_zero, toReal_pos
-/
theorem measure_smul_average [IsFiniteMeasure μ] (f : α -> E) :
    μ.real univ • ⨍ x, f x ∂μ = ∫ x, f x ∂μ := by
  rcases eq_or_ne μ 0 with hμ | hμ
  · rw [hμ, integral_zero_measure, average_zero_measure, smul_zero]
  · rw [average_eq, smul_inv_smul₀]
    refine (ENNReal.toReal_pos ?_ <| measure_ne_top _ _).ne'
    rwa [Ne, measure_univ_eq_zero]

/--
theorem `setAverage_eq` / 定理 `setAverage_eq`

English:
theorem setAverage_eq
  given: (f : α -> E) (s : Set α)
  proof: by
  rw [average_eq]; rw [measureReal_restrict_apply_univ]

中文:
定理 setAverage_eq
  条件: (f : α -> E) (s : 集合 α)
  证明: by
  rw [average_eq]; rw [measureReal_restrict_apply_univ]

Depends on / 依赖: average_eq, measureReal_restrict_apply_univ
-/
theorem setAverage_eq (f : α -> E) (s : Set α) :
    ⨍ x in s, f x ∂μ = (μ.real s)⁻¹ • ∫ x in s, f x ∂μ := by
  rw [average_eq]; rw [measureReal_restrict_apply_univ]

/--
theorem `setAverage_eq'` / 定理 `setAverage_eq'`

English:
theorem setAverage_eq'
  given: (f : α -> E) (s : Set α)
  proof: by
  simp only [average_eq', restrict_apply_univ]

中文:
定理 setAverage_eq'
  条件: (f : α -> E) (s : 集合 α)
  证明: by
  simp only [average_eq', restrict_apply_univ]

Depends on / 依赖: average_eq, restrict_apply_univ
-/
theorem setAverage_eq' (f : α -> E) (s : Set α) :
    ⨍ x in s, f x ∂μ = ∫ x, f x ∂(μ s)⁻¹ • μ.restrict s := by
  simp only [average_eq', restrict_apply_univ]

variable {μ}

/--
theorem `average_congr` / 定理 `average_congr`

English:
theorem average_congr
  given: {f g : α -> E} (h : f =ᵐ[μ] g)
  statement: ⨍ x, f x ∂μ = ⨍ x, g x ∂μ
  proof: by
  simp only [average_eq, integral_congr_ae h]

中文:
定理 average_congr
  条件: {f g : α -> E} (h : f =ᵐ[μ] g)
  结论: ⨍ x, f x ∂μ = ⨍ x, g x ∂μ
  证明: by
  simp only [average_eq, integral_congr_ae h]

Depends on / 依赖: average_eq, integral_congr_ae
-/
theorem average_congr {f g : α -> E} (h : f =ᵐ[μ] g) : ⨍ x, f x ∂μ = ⨍ x, g x ∂μ := by
  simp only [average_eq, integral_congr_ae h]

/--
theorem `setAverage_congr` / 定理 `setAverage_congr`

English:
theorem setAverage_congr
  given: (h : s =ᵐ[μ] t)
  statement: ⨍ x in s, f x ∂μ = ⨍ x in t, f x ∂μ
  proof: by
  simp only [setAverage_eq, setIntegral_congr_set h, measureReal_congr h]

中文:
定理 setAverage_congr
  条件: (h : s =ᵐ[μ] t)
  结论: ⨍ x in s, f x ∂μ = ⨍ x in t, f x ∂μ
  证明: by
  simp only [setAverage_eq, setIntegral_congr_set h, measureReal_congr h]

Depends on / 依赖: measureReal_congr, setAverage_eq, setIntegral_congr_set
-/
theorem setAverage_congr (h : s =ᵐ[μ] t) : ⨍ x in s, f x ∂μ = ⨍ x in t, f x ∂μ := by
  simp only [setAverage_eq, setIntegral_congr_set h, measureReal_congr h]

/--
theorem `setAverage_congr_fun` / 定理 `setAverage_congr_fun`

English:
theorem setAverage_congr_fun
  given: (hs : MeasurableSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x)
  proof: by simp only [average_eq, setIntegral_congr_ae hs h]

中文:
定理 setAverage_congr_fun
  条件: (hs : 可测集 s) (h : 对任意ᵐ x ∂μ, x in s -> f x = g x)
  证明: by simp only [average_eq, setIntegral_congr_ae hs h]

Depends on / 依赖: average_eq, setIntegral_congr_ae
-/
theorem setAverage_congr_fun (hs : MeasurableSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) :
    ⨍ x in s, f x ∂μ = ⨍ x in s, g x ∂μ := by simp only [average_eq, setIntegral_congr_ae hs h]

/--
theorem `average_add_measure` / 定理 `average_add_measure`

English:
theorem average_add_measure
  statement: [IsFiniteMeasure μ] {ν : Measure α} [IsFiniteMeasure ν] {f : α -> E}
  proof: by
  simp only [div_eq_inv_mul, mul_smul, measure_smul_average, ← smul_add,
    ← integral_add_measure hμ hν]
  rw [average_eq]; rw [measureReal_add_apply]

中文:
定理 average_add_measure
  结论: [是有限测度 μ] {ν : 测度 α} [是有限测度 ν] {f : α -> E}
  证明: by
  simp only [div_eq_inv_mul, mul_smul, measure_smul_average, ← smul_add,
    ← integral_add_measure hμ hν]
  rw [average_eq]; rw [measureReal_add_apply]

Depends on / 依赖: average_eq, div_eq_inv_mul, integral_add_measure, measureReal_add_apply, measure_smul_average, mul_smul, smul_add
-/
theorem average_add_measure [IsFiniteMeasure μ] {ν : Measure α} [IsFiniteMeasure ν] {f : α -> E}
    (hμ : Integrable f μ) (hν : Integrable f ν) :
    ⨍ x, f x ∂(μ + ν) =
      (μ.real univ / (μ.real univ + ν.real univ)) • ⨍ x, f x ∂μ +
        (ν.real univ / (μ.real univ + ν.real univ)) • ⨍ x, f x ∂ν := by
  simp only [div_eq_inv_mul, mul_smul, measure_smul_average, ← smul_add,
    ← integral_add_measure hμ hν]
  rw [average_eq]; rw [measureReal_add_apply]

/--
theorem `average_pair` / 定理 `average_pair`

English:
theorem average_pair
  statement: [CompleteSpace E]
  proof: integral_pair hfi.to_average hgi.to_average

中文:
定理 average_pair
  结论: [完备空间 E]
  证明: integral_pair hfi.to_average hgi.to_average

Depends on / 依赖: hfi.to_average, hgi.to_average, integral_pair, to_average
-/
theorem average_pair [CompleteSpace E]
    {f : α -> E} {g : α -> F} (hfi : Integrable f μ) (hgi : Integrable g μ) :
    ⨍ x, (f x, g x) ∂μ = (⨍ x, f x ∂μ, ⨍ x, g x ∂μ) :=
  integral_pair hfi.to_average hgi.to_average

/--
theorem `measure_smul_setAverage` / 定理 `measure_smul_setAverage`

English:
theorem measure_smul_setAverage
  given: (f : α -> E) {s : Set α} (h : μ s != ∞)
  proof: by
  have := Fact.mk h.lt_top
  rw [← measure_smul_average]; rw [measureReal_restrict_apply_univ]

中文:
定理 measure_smul_setAverage
  条件: (f : α -> E) {s : 集合 α} (h : μ s != ∞)
  证明: by
  have := Fact.mk h.lt_top
  rw [← measure_smul_average]; rw [measureReal_restrict_apply_univ]

Depends on / 依赖: Fact.mk, h.lt_top, lt_top, measureReal_restrict_apply_univ, measure_smul_average
-/
theorem measure_smul_setAverage (f : α -> E) {s : Set α} (h : μ s != ∞) :
    μ.real s • ⨍ x in s, f x ∂μ = ∫ x in s, f x ∂μ := by
  have := Fact.mk h.lt_top
  rw [← measure_smul_average]; rw [measureReal_restrict_apply_univ]

/--
theorem `average_union` / 定理 `average_union`

English:
theorem average_union
  statement: {f : α -> E} {s t : Set α} (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
  proof: by
  have := Fact.mk hsμ.lt_top; have := Fact.mk htμ.lt_top
  rw [restrict_union₀ hd ht]; rw [average_add_measure hfs hft]; rw [measureReal_restrict_apply_univ]; rw [measureReal_restrict_apply_univ]

中文:
定理 average_union
  结论: {f : α -> E} {s t : 集合 α} (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
  证明: by
  have := Fact.mk hsμ.lt_top; have := Fact.mk htμ.lt_top
  rw [restrict_union₀ hd ht]; rw [average_add_measure hfs hft]; rw [measureReal_restrict_apply_univ]; rw [measureReal_restrict_apply_univ]

Depends on / 依赖: Fact.mk, average_add_measure, lt_top, measureReal_restrict_apply_univ
-/
theorem average_union {f : α -> E} {s t : Set α} (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hsμ : μ s != ∞) (htμ : μ t != ∞) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    ⨍ x in s union t, f x ∂μ =
      (μ.real s / (μ.real s + μ.real t)) • ⨍ x in s, f x ∂μ +
        (μ.real t / (μ.real s + μ.real t)) • ⨍ x in t, f x ∂μ := by
  have := Fact.mk hsμ.lt_top; have := Fact.mk htμ.lt_top
  rw [restrict_union₀ hd ht]; rw [average_add_measure hfs hft]; rw [measureReal_restrict_apply_univ]; rw [measureReal_restrict_apply_univ]

/--
theorem `average_union_mem_openSegment` / 定理 `average_union_mem_openSegment`

English:
theorem average_union_mem_openSegment
  statement: {f : α -> E} {s t : Set α} (hd : AEDisjoint μ s t)
  proof: by
  replace hs₀ : 0 < μ.real s := ENNReal.toReal_pos hs₀ hsμ
  replace ht₀ : 0 < μ.real t := ENNReal.toReal_pos ht₀ htμ
  exact mem_openSegment_iff_div.mpr
    ⟨μ.real s, μ.real t, hs₀, ht₀, (average_union hd ht hsμ htμ hfs hft).symm⟩

中文:
定理 average_union_mem_openSegment
  结论: {f : α -> E} {s t : 集合 α} (hd : AEDisjoint μ s t)
  证明: by
  replace hs₀ : 0 < μ.real s := ENNReal.toReal_pos hs₀ hsμ
  replace ht₀ : 0 < μ.real t := ENNReal.toReal_pos ht₀ htμ
  exact mem_openSegment_iff_div.mpr
    ⟨μ.real s, μ.real t, hs₀, ht₀, (average_union hd ht hsμ htμ hfs hft).symm⟩

Depends on / 依赖: ENNReal, ENNReal.toReal_pos, average_union, mem_openSegment_iff_div, mem_openSegment_iff_div.mpr, replace, toReal_pos
-/
theorem average_union_mem_openSegment {f : α -> E} {s t : Set α} (hd : AEDisjoint μ s t)
    (ht : NullMeasurableSet t μ) (hs₀ : μ s != 0) (ht₀ : μ t != 0) (hsμ : μ s != ∞) (htμ : μ t != ∞)
    (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    ⨍ x in s union t, f x ∂μ in openSegment Real (⨍ x in s, f x ∂μ) (⨍ x in t, f x ∂μ) := by
  replace hs₀ : 0 < μ.real s := ENNReal.toReal_pos hs₀ hsμ
  replace ht₀ : 0 < μ.real t := ENNReal.toReal_pos ht₀ htμ
  exact mem_openSegment_iff_div.mpr
    ⟨μ.real s, μ.real t, hs₀, ht₀, (average_union hd ht hsμ htμ hfs hft).symm⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `average_union_mem_segment` / 定理 `average_union_mem_segment`

English:
theorem average_union_mem_segment
  statement: {f : α -> E} {s t : Set α} (hd : AEDisjoint μ s t)
  proof: by
  by_cases hse : μ s = 0
  · rw [← ae_eq_empty] at hse
    rw [restrict_congr_set (hse.union EventuallyEq.rfl)]; rw [empty_union]
    exact right_mem_segment _ _ _
  · refine
      mem_segment_iff_div.mpr
        ⟨μ.real s, μ.real t, ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, ?_,
          (average_union hd ht hsμ htμ hfs hft).symm⟩
    calc
      0 < μ.real s := ENNReal.toReal_pos hse hsμ
      _ <= _ := le_add_of_nonneg_right ENNReal.toReal_nonneg

中文:
定理 average_union_mem_segment
  结论: {f : α -> E} {s t : 集合 α} (hd : AEDisjoint μ s t)
  证明: by
  by_cases hse : μ s = 0
  · rw [← ae_eq_empty] at hse
    rw [restrict_congr_set (hse.union EventuallyEq.rfl)]; rw [empty_union]
    exact right_mem_segment _ _ _
  · refine
      mem_segment_iff_div.mpr
        ⟨μ.real s, μ.real t, ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, ?_,
          (average_union hd ht hsμ htμ hfs hft).symm⟩
    calc
      0 < μ.real s := ENNReal.toReal_pos hse hsμ
      _ <= _ := le_add_of_nonneg_right ENNReal.toReal_nonneg

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, ENNReal.toReal_pos, EventuallyEq, EventuallyEq.rfl, ae_eq_empty, average_union, empty_union, hse.union, le_add_of_nonneg_right, mem_segment_iff_div, mem_segment_iff_div.mpr, restrict_congr_set, right_mem_segment, toReal_nonneg, toReal_pos
-/
theorem average_union_mem_segment {f : α -> E} {s t : Set α} (hd : AEDisjoint μ s t)
    (ht : NullMeasurableSet t μ) (hsμ : μ s != ∞) (htμ : μ t != ∞) (hfs : IntegrableOn f s μ)
    (hft : IntegrableOn f t μ) :
    ⨍ x in s union t, f x ∂μ in [⨍ x in s, f x ∂μ -[Real] ⨍ x in t, f x ∂μ] := by
  by_cases hse : μ s = 0
  · rw [← ae_eq_empty] at hse
    rw [restrict_congr_set (hse.union EventuallyEq.rfl)]; rw [empty_union]
    exact right_mem_segment _ _ _
  · refine
      mem_segment_iff_div.mpr
        ⟨μ.real s, μ.real t, ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, ?_,
          (average_union hd ht hsμ htμ hfs hft).symm⟩
    calc
      0 < μ.real s := ENNReal.toReal_pos hse hsμ
      _ <= _ := le_add_of_nonneg_right ENNReal.toReal_nonneg

/--
theorem `average_mem_openSegment_compl_self` / 定理 `average_mem_openSegment_compl_self`

English:
theorem average_mem_openSegment_compl_self
  statement: [IsFiniteMeasure μ] {f : α -> E} {s : Set α}
  proof: by
  simpa only [union_compl_self, restrict_univ] using
    average_union_mem_openSegment aedisjoint_compl_right hs.compl hs₀ hsc₀ (measure_ne_top _ _)
      (measure_ne_top _ _) hfi.integrableOn hfi.integrableOn

中文:
定理 average_mem_openSegment_compl_self
  结论: [是有限测度 μ] {f : α -> E} {s : 集合 α}
  证明: by
  simpa only [union_compl_self, restrict_univ] using
    average_union_mem_openSegment aedisjoint_compl_right hs.compl hs₀ hsc₀ (measure_ne_top _ _)
      (measure_ne_top _ _) hfi.integrableOn hfi.integrableOn

Depends on / 依赖: aedisjoint_compl_right, average_union_mem_openSegment, hfi.integrableOn, hs.compl, integrableOn, measure_ne_top, restrict_univ, union_compl_self
-/
theorem average_mem_openSegment_compl_self [IsFiniteMeasure μ] {f : α -> E} {s : Set α}
    (hs : NullMeasurableSet s μ) (hs₀ : μ s != 0) (hsc₀ : μ sᶜ != 0) (hfi : Integrable f μ) :
    ⨍ x, f x ∂μ in openSegment Real (⨍ x in s, f x ∂μ) (⨍ x in sᶜ, f x ∂μ) := by
  simpa only [union_compl_self, restrict_univ] using
    average_union_mem_openSegment aedisjoint_compl_right hs.compl hs₀ hsc₀ (measure_ne_top _ _)
      (measure_ne_top _ _) hfi.integrableOn hfi.integrableOn

variable [CompleteSpace E]

@[simp]
/--
theorem `average_const` / 定理 `average_const`

English:
theorem average_const
  given: (μ : Measure α) [IsFiniteMeasure μ] [h : NeZero μ] (c : E)
  proof: by
  rw [average]; rw [integral_const]; rw [measureReal_def]; rw [measure_univ]; rw [ENNReal.toReal_one]; rw [one_smul]

中文:
定理 average_const
  条件: (μ : 测度 α) [是有限测度 μ] [h : NeZero μ] (c : E)
  证明: by
  rw [average]; rw [integral_const]; rw [measureReal_def]; rw [measure_univ]; rw [ENNReal.toReal_one]; rw [one_smul]

Depends on / 依赖: ENNReal, ENNReal.toReal_one, average, integral_const, measureReal_def, measure_univ, one_smul, toReal_one
-/
theorem average_const (μ : Measure α) [IsFiniteMeasure μ] [h : NeZero μ] (c : E) :
    ⨍ _x, c ∂μ = c := by
  rw [average]; rw [integral_const]; rw [measureReal_def]; rw [measure_univ]; rw [ENNReal.toReal_one]; rw [one_smul]

/--
theorem `setAverage_const` / 定理 `setAverage_const`

English:
theorem setAverage_const
  given: {s : Set α} (hs₀ : μ s != 0) (hs : μ s != ∞) (c : E)
  proof: have := NeZero.mk hs₀; have := Fact.mk hs.lt_top; average_const _ _

中文:
定理 setAverage_const
  条件: {s : 集合 α} (hs₀ : μ s != 0) (hs : μ s != ∞) (c : E)
  证明: have := NeZero.mk hs₀; have := Fact.mk hs.lt_top; average_const _ _

Depends on / 依赖: Fact.mk, NeZero, NeZero.mk, average_const, hs.lt_top, lt_top
-/
theorem setAverage_const {s : Set α} (hs₀ : μ s != 0) (hs : μ s != ∞) (c : E) :
    ⨍ _ in s, c ∂μ = c :=
  have := NeZero.mk hs₀; have := Fact.mk hs.lt_top; average_const _ _

/--
theorem `integral_average` / 定理 `integral_average`

English:
theorem integral_average
  given: (μ : Measure α) [IsFiniteMeasure μ] (f : α -> E)
  proof: by simp

中文:
定理 integral_average
  条件: (μ : 测度 α) [是有限测度 μ] (f : α -> E)
  证明: by simp
-/
theorem integral_average (μ : Measure α) [IsFiniteMeasure μ] (f : α -> E) :
    ∫ _, ⨍ a, f a ∂μ ∂μ = ∫ x, f x ∂μ := by simp

/--
theorem `setIntegral_setAverage` / 定理 `setIntegral_setAverage`

English:
theorem setIntegral_setAverage
  given: (μ : Measure α) [IsFiniteMeasure μ] (f : α -> E) (s : Set α)
  proof: integral_average _ _

中文:
定理 set整数egral_setAverage
  条件: (μ : 测度 α) [是有限测度 μ] (f : α -> E) (s : 集合 α)
  证明: integral_average _ _

Depends on / 依赖: integral_average
-/
theorem setIntegral_setAverage (μ : Measure α) [IsFiniteMeasure μ] (f : α -> E) (s : Set α) :
    ∫ _ in s, ⨍ a in s, f a ∂μ ∂μ = ∫ x in s, f x ∂μ :=
  integral_average _ _

/--
theorem `integral_sub_average` / 定理 `integral_sub_average`

English:
theorem integral_sub_average
  given: (μ : Measure α) [IsFiniteMeasure μ] (f : α -> E)
  proof: by
  by_cases hf : Integrable f μ
  · rw [integral_sub hf (integrable_const _), integral_average, sub_self]
  refine integral_undef fun h => hf ?_
  convert! h.add (integrable_const (⨍ a, f a ∂μ))
  exact (sub_add_cancel _ _).symm

中文:
定理 integral_sub_average
  条件: (μ : 测度 α) [是有限测度 μ] (f : α -> E)
  证明: by
  by_cases hf : Integrable f μ
  · rw [integral_sub hf (integrable_const _), integral_average, sub_self]
  refine integral_undef fun h => hf ?_
  convert! h.add (integrable_const (⨍ a, f a ∂μ))
  exact (sub_add_cancel _ _).symm

Depends on / 依赖: Integrable, convert, h.add, integrable_const, integral_average, integral_sub, integral_undef, sub_add_cancel, sub_self
-/
theorem integral_sub_average (μ : Measure α) [IsFiniteMeasure μ] (f : α -> E) :
    ∫ x, f x - ⨍ a, f a ∂μ ∂μ = 0 := by
  by_cases hf : Integrable f μ
  · rw [integral_sub hf (integrable_const _), integral_average, sub_self]
  refine integral_undef fun h => hf ?_
  convert! h.add (integrable_const (⨍ a, f a ∂μ))
  exact (sub_add_cancel _ _).symm

/--
theorem `setAverage_sub_setAverage` / 定理 `setAverage_sub_setAverage`

English:
theorem setAverage_sub_setAverage
  given: (hs : μ s != ∞) (f : α -> E)
  proof: haveI : Fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩
  integral_sub_average _ _

中文:
定理 setAverage_sub_setAverage
  条件: (hs : μ s != ∞) (f : α -> E)
  证明: haveI : Fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩
  integral_sub_average _ _

Depends on / 依赖: integral_sub_average, lt_top_iff_ne_top
-/
theorem setAverage_sub_setAverage (hs : μ s != ∞) (f : α -> E) :
    ∫ x in s, f x - ⨍ a in s, f a ∂μ ∂μ = 0 :=
  haveI : Fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩
  integral_sub_average _ _

/--
theorem `integral_average_sub` / 定理 `integral_average_sub`

English:
theorem integral_average_sub
  given: [IsFiniteMeasure μ] (hf : Integrable f μ)
  proof: by
  rw [integral_sub (integrable_const _) hf]; rw [integral_average]; rw [sub_self]

中文:
定理 integral_average_sub
  条件: [是有限测度 μ] (hf : 可积 f μ)
  证明: by
  rw [integral_sub (integrable_const _) hf]; rw [integral_average]; rw [sub_self]

Depends on / 依赖: integrable_const, integral_average, integral_sub, sub_self
-/
theorem integral_average_sub [IsFiniteMeasure μ] (hf : Integrable f μ) :
    ∫ x, ⨍ a, f a ∂μ - f x ∂μ = 0 := by
  rw [integral_sub (integrable_const _) hf]; rw [integral_average]; rw [sub_self]

/--
theorem `setIntegral_setAverage_sub` / 定理 `setIntegral_setAverage_sub`

English:
theorem setIntegral_setAverage_sub
  given: (hs : μ s != ∞) (hf : IntegrableOn f s μ)
  proof: haveI : Fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩
  integral_average_sub hf

中文:
定理 set整数egral_setAverage_sub
  条件: (hs : μ s != ∞) (hf : 整数egrableOn f s μ)
  证明: haveI : Fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩
  integral_average_sub hf

Depends on / 依赖: integral_average_sub, lt_top_iff_ne_top
-/
theorem setIntegral_setAverage_sub (hs : μ s != ∞) (hf : IntegrableOn f s μ) :
    ∫ x in s, ⨍ a in s, f a ∂μ - f x ∂μ = 0 :=
  haveI : Fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩
  integral_average_sub hf

end NormedAddCommGroup

/--
theorem `ofReal_average` / 定理 `ofReal_average`

English:
theorem ofReal_average
  given: {f : α -> Real} (hf : Integrable f μ) (hf₀ : 0 <=ᵐ[μ] f)
  proof: by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [average_eq, smul_eq_mul, measureReal_def, ← toReal_inv, ofReal_mul toReal_nonneg,
      ofReal_toReal (inv_ne_top.2 <| measure_univ_ne_zero.2 hμ),
      ofReal_integral_eq_lintegral_ofReal hf hf₀, ENNReal.div_eq_inv_mul]

中文:
定理 of实数_average
  条件: {f : α -> 实数} (hf : 可积 f μ) (hf₀ : 0 <=ᵐ[μ] f)
  证明: by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [average_eq, smul_eq_mul, measureReal_def, ← toReal_inv, ofReal_mul toReal_nonneg,
      ofReal_toReal (inv_ne_top.2 <| measure_univ_ne_zero.2 hμ),
      ofReal_integral_eq_lintegral_ofReal hf hf₀, ENNReal.div_eq_inv_mul]

Depends on / 依赖: ENNReal, ENNReal.div_eq_inv_mul, average_eq, div_eq_inv_mul, eq_or_ne, inv_ne_top, measureReal_def, measure_univ_ne_zero, ofReal_integral_eq_lintegral_ofReal, ofReal_mul, ofReal_toReal, smul_eq_mul, toReal_inv, toReal_nonneg
-/
theorem ofReal_average {f : α -> Real} (hf : Integrable f μ) (hf₀ : 0 <=ᵐ[μ] f) :
    ENNReal.ofReal (⨍ x, f x ∂μ) = (∫⁻ x, ENNReal.ofReal (f x) ∂μ) / μ univ := by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [average_eq, smul_eq_mul, measureReal_def, ← toReal_inv, ofReal_mul toReal_nonneg,
      ofReal_toReal (inv_ne_top.2 <| measure_univ_ne_zero.2 hμ),
      ofReal_integral_eq_lintegral_ofReal hf hf₀, ENNReal.div_eq_inv_mul]

/--
theorem `ofReal_setAverage` / 定理 `ofReal_setAverage`

English:
theorem ofReal_setAverage
  given: {f : α -> Real} (hf : IntegrableOn f s μ) (hf₀ : 0 <=ᵐ[μ.restrict s] f)
  proof: by
  simpa using ofReal_average hf hf₀

中文:
定理 of实数_setAverage
  条件: {f : α -> 实数} (hf : 整数egrableOn f s μ) (hf₀ : 0 <=ᵐ[μ.restrict s] f)
  证明: by
  simpa using ofReal_average hf hf₀

Depends on / 依赖: ofReal_average
-/
theorem ofReal_setAverage {f : α -> Real} (hf : IntegrableOn f s μ) (hf₀ : 0 <=ᵐ[μ.restrict s] f) :
    ENNReal.ofReal (⨍ x in s, f x ∂μ) = (∫⁻ x in s, ENNReal.ofReal (f x) ∂μ) / μ s := by
  simpa using ofReal_average hf hf₀

/--
theorem `toReal_laverage` / 定理 `toReal_laverage`

English:
theorem toReal_laverage
  given: {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (hf' : forallᵐ x ∂μ, f x != ∞)
  proof: by
    rw [average_eq]; rw [laverage_eq]; rw [smul_eq_mul]; rw [toReal_div]; rw [div_eq_inv_mul]; rw [←
      integral_toReal hf (hf'.mono fun _ => lt_top_iff_ne_top.2)]; rw [measureReal_def]

中文:
定理 to实数_laverage
  条件: {f : α -> 实数>=0∞} (hf : 几乎处处可测 f μ) (hf' : 对任意ᵐ x ∂μ, f x != ∞)
  证明: by
    rw [average_eq]; rw [laverage_eq]; rw [smul_eq_mul]; rw [toReal_div]; rw [div_eq_inv_mul]; rw [←
      integral_toReal hf (hf'.mono fun _ => lt_top_iff_ne_top.2)]; rw [measureReal_def]

Depends on / 依赖: average_eq, div_eq_inv_mul, integral_toReal, laverage_eq, lt_top_iff_ne_top, measureReal_def, smul_eq_mul, toReal_div
-/
theorem toReal_laverage {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (hf' : forallᵐ x ∂μ, f x != ∞) :
    (⨍⁻ x, f x ∂μ).toReal = ⨍ x, (f x).toReal ∂μ := by
    rw [average_eq]; rw [laverage_eq]; rw [smul_eq_mul]; rw [toReal_div]; rw [div_eq_inv_mul]; rw [←
      integral_toReal hf (hf'.mono fun _ => lt_top_iff_ne_top.2)]; rw [measureReal_def]

/--
theorem `toReal_setLAverage` / 定理 `toReal_setLAverage`

English:
theorem toReal_setLAverage
  statement: {f : α -> Real>=0∞} (hf : AEMeasurable f (μ.restrict s))
  proof: by
  simpa [laverage_eq] using toReal_laverage hf hf'

中文:
定理 to实数_setLAverage
  结论: {f : α -> 实数>=0∞} (hf : 几乎处处可测 f (μ.restrict s))
  证明: by
  simpa [laverage_eq] using toReal_laverage hf hf'

Depends on / 依赖: laverage_eq, toReal_laverage
-/
theorem toReal_setLAverage {f : α -> Real>=0∞} (hf : AEMeasurable f (μ.restrict s))
    (hf' : forallᵐ x ∂μ.restrict s, f x != ∞) :
    (⨍⁻ x in s, f x ∂μ).toReal = ⨍ x in s, (f x).toReal ∂μ := by
  simpa [laverage_eq] using toReal_laverage hf hf'

/-! ### First moment method -/

section FirstMomentReal
variable {N : Set α} {f : α -> Real}

/--
theorem `measure_le_setAverage_pos` / 定理 `measure_le_setAverage_pos`

English:
theorem measure_le_setAverage_pos
  given: (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ)
  proof: by
  refine pos_iff_ne_zero.2 fun H => ?_
  replace H : (μ.restrict s) {x | f x <= ⨍ a in s, f a ∂μ} = 0 := by
    rwa [restrict_apply₀, inter_comm]
    exact AEStronglyMeasurable.nullMeasurableSet_le hf.1 aestronglyMeasurable_const
  have := Fact.mk hμ₁.lt_top
  refine (integral_sub_average (μ.restrict s) f).not_gt ?_
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ ?_).2 ?_
  · refine measure_mono_null (fun x hx => ?_) H
    simp only [Pi.zero_apply, sub_nonneg, mem_compl_iff, mem_ofPred_eq, not_le] at hx
    exact hx.le
  · exact hf.sub (integrableOn_const hμ₁)
  · rwa [pos_iff_ne_zero, inter_comm, ← sdiff_compl, ← sdiff_inter_self_eq_sdiff,
      measure_sdiff_null]
    refine measure_mono_null ?_ (measure_inter_eq_zero_of_restrict H)
    exact inter_subset_inter_left _ fun a ha => (sub_eq_zero.1 <| of_not_not ha).le

中文:
定理 measure_le_setAverage_pos
  条件: (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : 整数egrableOn f s μ)
  证明: by
  refine pos_iff_ne_zero.2 fun H => ?_
  replace H : (μ.restrict s) {x | f x <= ⨍ a in s, f a ∂μ} = 0 := by
    rwa [restrict_apply₀, inter_comm]
    exact AEStronglyMeasurable.nullMeasurableSet_le hf.1 aestronglyMeasurable_const
  have := Fact.mk hμ₁.lt_top
  refine (integral_sub_average (μ.restrict s) f).not_gt ?_
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ ?_).2 ?_
  · refine measure_mono_null (fun x hx => ?_) H
    simp only [Pi.zero_apply, sub_nonneg, mem_compl_iff, mem_ofPred_eq, not_le] at hx
    exact hx.le
  · exact hf.sub (integrableOn_const hμ₁)
  · rwa [pos_iff_ne_zero, inter_comm, ← sdiff_compl, ← sdiff_inter_self_eq_sdiff,
      measure_sdiff_null]
    refine measure_mono_null ?_ (measure_inter_eq_zero_of_restrict H)
    exact inter_subset_inter_left _ fun a ha => (sub_eq_zero.1 <| of_not_not ha).le

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.nullMeasurableSet_le, Fact.mk, Pi.zero_apply, aestronglyMeasurable_const, integral_sub_average, inter_comm, lt_top, measure_mono_null, mem_compl_iff, mem_ofPred_eq, not_gt, not_le, nullMeasurableSet_le, pos_iff_ne_zero, replace, restrict, setIntegral_pos_iff_support_of_nonneg_ae, sub_nonneg, zero_apply
-/
theorem measure_le_setAverage_pos (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ) :
    0 < μ ({x in s | f x <= ⨍ a in s, f a ∂μ}) := by
  refine pos_iff_ne_zero.2 fun H => ?_
  replace H : (μ.restrict s) {x | f x <= ⨍ a in s, f a ∂μ} = 0 := by
    rwa [restrict_apply₀, inter_comm]
    exact AEStronglyMeasurable.nullMeasurableSet_le hf.1 aestronglyMeasurable_const
  have := Fact.mk hμ₁.lt_top
  refine (integral_sub_average (μ.restrict s) f).not_gt ?_
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ ?_).2 ?_
  · refine measure_mono_null (fun x hx => ?_) H
    simp only [Pi.zero_apply, sub_nonneg, mem_compl_iff, mem_ofPred_eq, not_le] at hx
    exact hx.le
  · exact hf.sub (integrableOn_const hμ₁)
  · rwa [pos_iff_ne_zero, inter_comm, ← sdiff_compl, ← sdiff_inter_self_eq_sdiff,
      measure_sdiff_null]
    refine measure_mono_null ?_ (measure_inter_eq_zero_of_restrict H)
    exact inter_subset_inter_left _ fun a ha => (sub_eq_zero.1 <| of_not_not ha).le

/--
theorem `measure_setAverage_le_pos` / 定理 `measure_setAverage_le_pos`

English:
theorem measure_setAverage_le_pos
  given: (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ)
  proof: by
  simpa [integral_neg, neg_div] using measure_le_setAverage_pos hμ hμ₁ hf.neg

中文:
定理 measure_setAverage_le_pos
  条件: (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : 整数egrableOn f s μ)
  证明: by
  simpa [integral_neg, neg_div] using measure_le_setAverage_pos hμ hμ₁ hf.neg

Depends on / 依赖: hf.neg, integral_neg, measure_le_setAverage_pos, neg_div
-/
theorem measure_setAverage_le_pos (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ) :
    0 < μ ({x in s | ⨍ a in s, f a ∂μ <= f x}) := by
  simpa [integral_neg, neg_div] using measure_le_setAverage_pos hμ hμ₁ hf.neg

/--
theorem `exists_le_setAverage` / 定理 `exists_le_setAverage`

English:
theorem exists_le_setAverage
  given: (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ)
  proof: let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_setAverage_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩

中文:
定理 存在_le_setAverage
  条件: (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : 整数egrableOn f s μ)
  证明: let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_setAverage_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩

Depends on / 依赖: measure_le_setAverage_pos, nonempty_of_measure_ne_zero
-/
theorem exists_le_setAverage (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ) :
    exists x in s, f x <= ⨍ a in s, f a ∂μ :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_setAverage_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩

/--
theorem `exists_setAverage_le` / 定理 `exists_setAverage_le`

English:
theorem exists_setAverage_le
  given: (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ)
  proof: let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_setAverage_le_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩

中文:
定理 存在_setAverage_le
  条件: (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : 整数egrableOn f s μ)
  证明: let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_setAverage_le_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩

Depends on / 依赖: measure_setAverage_le_pos, nonempty_of_measure_ne_zero
-/
theorem exists_setAverage_le (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ) :
    exists x in s, ⨍ a in s, f a ∂μ <= f x :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_setAverage_le_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩

section FiniteMeasure

variable [IsFiniteMeasure μ]

/--
theorem `measure_le_average_pos` / 定理 `measure_le_average_pos`

English:
theorem measure_le_average_pos
  given: (hμ : μ != 0) (hf : Integrable f μ)
  proof: by
  simpa using measure_le_setAverage_pos (Measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
    hf.integrableOn

中文:
定理 measure_le_average_pos
  条件: (hμ : μ != 0) (hf : 可积 f μ)
  证明: by
  simpa using measure_le_setAverage_pos (Measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
    hf.integrableOn

Depends on / 依赖: Measure, Measure.measure_univ_ne_zero, hf.integrableOn, integrableOn, measure_le_setAverage_pos, measure_ne_top, measure_univ_ne_zero
-/
theorem measure_le_average_pos (hμ : μ != 0) (hf : Integrable f μ) :
    0 < μ {x | f x <= ⨍ a, f a ∂μ} := by
  simpa using measure_le_setAverage_pos (Measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
    hf.integrableOn

/--
theorem `measure_average_le_pos` / 定理 `measure_average_le_pos`

English:
theorem measure_average_le_pos
  given: (hμ : μ != 0) (hf : Integrable f μ)
  proof: by
  simpa using measure_setAverage_le_pos (Measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
    hf.integrableOn

中文:
定理 measure_average_le_pos
  条件: (hμ : μ != 0) (hf : 可积 f μ)
  证明: by
  simpa using measure_setAverage_le_pos (Measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
    hf.integrableOn

Depends on / 依赖: Measure, Measure.measure_univ_ne_zero, hf.integrableOn, integrableOn, measure_ne_top, measure_setAverage_le_pos, measure_univ_ne_zero
-/
theorem measure_average_le_pos (hμ : μ != 0) (hf : Integrable f μ) :
    0 < μ {x | ⨍ a, f a ∂μ <= f x} := by
  simpa using measure_setAverage_le_pos (Measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
    hf.integrableOn

/--
theorem `exists_le_average` / 定理 `exists_le_average`

English:
theorem exists_le_average
  given: (hμ : μ != 0) (hf : Integrable f μ)
  statement: exists x, f x <= ⨍ a, f a ∂μ
  proof: let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_average_pos hμ hf).ne'
  ⟨x, hx⟩

中文:
定理 存在_le_average
  条件: (hμ : μ != 0) (hf : 可积 f μ)
  结论: 存在 x, f x <= ⨍ a, f a ∂μ
  证明: let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_average_pos hμ hf).ne'
  ⟨x, hx⟩

Depends on / 依赖: measure_le_average_pos, nonempty_of_measure_ne_zero
-/
theorem exists_le_average (hμ : μ != 0) (hf : Integrable f μ) : exists x, f x <= ⨍ a, f a ∂μ :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_average_pos hμ hf).ne'
  ⟨x, hx⟩

/--
theorem `exists_average_le` / 定理 `exists_average_le`

English:
theorem exists_average_le
  given: (hμ : μ != 0) (hf : Integrable f μ)
  statement: exists x, ⨍ a, f a ∂μ <= f x
  proof: let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_average_le_pos hμ hf).ne'
  ⟨x, hx⟩

中文:
定理 存在_average_le
  条件: (hμ : μ != 0) (hf : 可积 f μ)
  结论: 存在 x, ⨍ a, f a ∂μ <= f x
  证明: let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_average_le_pos hμ hf).ne'
  ⟨x, hx⟩

Depends on / 依赖: measure_average_le_pos, nonempty_of_measure_ne_zero
-/
theorem exists_average_le (hμ : μ != 0) (hf : Integrable f μ) : exists x, ⨍ a, f a ∂μ <= f x :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_average_le_pos hμ hf).ne'
  ⟨x, hx⟩

/--
theorem `exists_notMem_null_le_average` / 定理 `exists_notMem_null_le_average`

English:
theorem exists_notMem_null_le_average
  given: (hμ : μ != 0) (hf : Integrable f μ) (hN : μ N = 0)
  proof: by
  have := measure_le_average_pos hμ hf
  rw [← measure_sdiff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩

中文:
定理 存在_notMem_null_le_average
  条件: (hμ : μ != 0) (hf : 可积 f μ) (hN : μ N = 0)
  证明: by
  have := measure_le_average_pos hμ hf
  rw [← measure_sdiff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩

Depends on / 依赖: measure_le_average_pos, measure_sdiff_null, nonempty_of_measure_ne_zero, this.ne
-/
theorem exists_notMem_null_le_average (hμ : μ != 0) (hf : Integrable f μ) (hN : μ N = 0) :
    exists x, x ∉ N ∧ f x <= ⨍ a, f a ∂μ := by
  have := measure_le_average_pos hμ hf
  rw [← measure_sdiff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩

/--
theorem `exists_notMem_null_average_le` / 定理 `exists_notMem_null_average_le`

English:
theorem exists_notMem_null_average_le
  given: (hμ : μ != 0) (hf : Integrable f μ) (hN : μ N = 0)
  proof: by
  simpa [integral_neg, neg_div] using exists_notMem_null_le_average hμ hf.neg hN

中文:
定理 存在_notMem_null_average_le
  条件: (hμ : μ != 0) (hf : 可积 f μ) (hN : μ N = 0)
  证明: by
  simpa [integral_neg, neg_div] using exists_notMem_null_le_average hμ hf.neg hN

Depends on / 依赖: exists_notMem_null_le_average, hf.neg, integral_neg, neg_div
-/
theorem exists_notMem_null_average_le (hμ : μ != 0) (hf : Integrable f μ) (hN : μ N = 0) :
    exists x, x ∉ N ∧ ⨍ a, f a ∂μ <= f x := by
  simpa [integral_neg, neg_div] using exists_notMem_null_le_average hμ hf.neg hN

end FiniteMeasure

section ProbabilityMeasure

variable [IsProbabilityMeasure μ]

/--
theorem `measure_le_integral_pos` / 定理 `measure_le_integral_pos`

English:
theorem measure_le_integral_pos
  given: (hf : Integrable f μ)
  statement: 0 < μ {x | f x <= ∫ a, f a ∂μ}
  proof: by
  simpa only [average_eq_integral] using
    measure_le_average_pos (IsProbabilityMeasure.ne_zero μ) hf

中文:
定理 measure_le_integral_pos
  条件: (hf : 可积 f μ)
  结论: 0 < μ {x | f x <= ∫ a, f a ∂μ}
  证明: by
  simpa only [average_eq_integral] using
    measure_le_average_pos (IsProbabilityMeasure.ne_zero μ) hf

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.ne_zero, average_eq_integral, measure_le_average_pos, ne_zero
-/
theorem measure_le_integral_pos (hf : Integrable f μ) : 0 < μ {x | f x <= ∫ a, f a ∂μ} := by
  simpa only [average_eq_integral] using
    measure_le_average_pos (IsProbabilityMeasure.ne_zero μ) hf

/--
theorem `measure_integral_le_pos` / 定理 `measure_integral_le_pos`

English:
theorem measure_integral_le_pos
  given: (hf : Integrable f μ)
  statement: 0 < μ {x | ∫ a, f a ∂μ <= f x}
  proof: by
  simpa only [average_eq_integral] using
    measure_average_le_pos (IsProbabilityMeasure.ne_zero μ) hf

中文:
定理 measure_integral_le_pos
  条件: (hf : 可积 f μ)
  结论: 0 < μ {x | ∫ a, f a ∂μ <= f x}
  证明: by
  simpa only [average_eq_integral] using
    measure_average_le_pos (IsProbabilityMeasure.ne_zero μ) hf

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.ne_zero, average_eq_integral, measure_average_le_pos, ne_zero
-/
theorem measure_integral_le_pos (hf : Integrable f μ) : 0 < μ {x | ∫ a, f a ∂μ <= f x} := by
  simpa only [average_eq_integral] using
    measure_average_le_pos (IsProbabilityMeasure.ne_zero μ) hf

/--
theorem `exists_le_integral` / 定理 `exists_le_integral`

English:
theorem exists_le_integral
  given: (hf : Integrable f μ)
  statement: exists x, f x <= ∫ a, f a ∂μ
  proof: by
  simpa only [average_eq_integral] using exists_le_average (IsProbabilityMeasure.ne_zero μ) hf

中文:
定理 存在_le_integral
  条件: (hf : 可积 f μ)
  结论: 存在 x, f x <= ∫ a, f a ∂μ
  证明: by
  simpa only [average_eq_integral] using exists_le_average (IsProbabilityMeasure.ne_zero μ) hf

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.ne_zero, average_eq_integral, exists_le_average, ne_zero
-/
theorem exists_le_integral (hf : Integrable f μ) : exists x, f x <= ∫ a, f a ∂μ := by
  simpa only [average_eq_integral] using exists_le_average (IsProbabilityMeasure.ne_zero μ) hf

/--
theorem `exists_integral_le` / 定理 `exists_integral_le`

English:
theorem exists_integral_le
  given: (hf : Integrable f μ)
  statement: exists x, ∫ a, f a ∂μ <= f x
  proof: by
  simpa only [average_eq_integral] using exists_average_le (IsProbabilityMeasure.ne_zero μ) hf

中文:
定理 存在_integral_le
  条件: (hf : 可积 f μ)
  结论: 存在 x, ∫ a, f a ∂μ <= f x
  证明: by
  simpa only [average_eq_integral] using exists_average_le (IsProbabilityMeasure.ne_zero μ) hf

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.ne_zero, average_eq_integral, exists_average_le, ne_zero
-/
theorem exists_integral_le (hf : Integrable f μ) : exists x, ∫ a, f a ∂μ <= f x := by
  simpa only [average_eq_integral] using exists_average_le (IsProbabilityMeasure.ne_zero μ) hf

/--
theorem `exists_notMem_null_le_integral` / 定理 `exists_notMem_null_le_integral`

English:
theorem exists_notMem_null_le_integral
  given: (hf : Integrable f μ) (hN : μ N = 0)
  proof: by
  simpa only [average_eq_integral] using
    exists_notMem_null_le_average (IsProbabilityMeasure.ne_zero μ) hf hN

中文:
定理 存在_notMem_null_le_integral
  条件: (hf : 可积 f μ) (hN : μ N = 0)
  证明: by
  simpa only [average_eq_integral] using
    exists_notMem_null_le_average (IsProbabilityMeasure.ne_zero μ) hf hN

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.ne_zero, average_eq_integral, exists_notMem_null_le_average, ne_zero
-/
theorem exists_notMem_null_le_integral (hf : Integrable f μ) (hN : μ N = 0) :
    exists x, x ∉ N ∧ f x <= ∫ a, f a ∂μ := by
  simpa only [average_eq_integral] using
    exists_notMem_null_le_average (IsProbabilityMeasure.ne_zero μ) hf hN

/--
theorem `exists_notMem_null_integral_le` / 定理 `exists_notMem_null_integral_le`

English:
theorem exists_notMem_null_integral_le
  given: (hf : Integrable f μ) (hN : μ N = 0)
  proof: by
  simpa only [average_eq_integral] using
    exists_notMem_null_average_le (IsProbabilityMeasure.ne_zero μ) hf hN

中文:
定理 存在_notMem_null_integral_le
  条件: (hf : 可积 f μ) (hN : μ N = 0)
  证明: by
  simpa only [average_eq_integral] using
    exists_notMem_null_average_le (IsProbabilityMeasure.ne_zero μ) hf hN

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.ne_zero, average_eq_integral, exists_notMem_null_average_le, ne_zero
-/
theorem exists_notMem_null_integral_le (hf : Integrable f μ) (hN : μ N = 0) :
    exists x, x ∉ N ∧ ∫ a, f a ∂μ <= f x := by
  simpa only [average_eq_integral] using
    exists_notMem_null_average_le (IsProbabilityMeasure.ne_zero μ) hf hN

end ProbabilityMeasure
end FirstMomentReal

section FirstMomentENNReal
variable {N : Set α} {f : α -> Real>=0∞}

/--
theorem `measure_le_setLAverage_pos` / 定理 `measure_le_setLAverage_pos`

English:
theorem measure_le_setLAverage_pos
  statement: (hμ : μ s != 0) (hμ₁ : μ s != ∞)
  proof: by
  obtain h | h := eq_or_ne (∫⁻ a in s, f a ∂μ) ∞
  · simpa [mul_top, hμ₁, laverage, h, top_div_of_ne_top hμ₁, pos_iff_ne_zero] using hμ
  have := measure_le_setAverage_pos hμ hμ₁ (integrable_toReal_of_lintegral_ne_top hf h)
  rw [← ofPred_inter_eq_sep]; rw [← Measure.restrict_apply₀
    (hf.aestronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const)]
  rw [← ofPred_inter_eq_sep]; rw [← Measure.restrict_apply₀
    (hf.ennreal_toReal.aestronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const)]; rw [← measure_sdiff_null (measure_eq_top_of_lintegral_ne_top hf h)] at this
  refine this.trans_le (measure_mono ?_)
  rintro x ⟨hfx, hx⟩
  dsimp at hfx
  rwa [← toReal_laverage hf, toReal_le_toReal hx (setLAverage_lt_top h).ne] at hfx
  simp_rw [ae_iff, not_ne_iff]
  exact measure_eq_top_of_lintegral_ne_top hf h

中文:
定理 measure_le_setLAverage_pos
  结论: (hμ : μ s != 0) (hμ₁ : μ s != ∞)
  证明: by
  obtain h | h := eq_or_ne (∫⁻ a in s, f a ∂μ) ∞
  · simpa [mul_top, hμ₁, laverage, h, top_div_of_ne_top hμ₁, pos_iff_ne_zero] using hμ
  have := measure_le_setAverage_pos hμ hμ₁ (integrable_toReal_of_lintegral_ne_top hf h)
  rw [← ofPred_inter_eq_sep]; rw [← Measure.restrict_apply₀
    (hf.aestronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const)]
  rw [← ofPred_inter_eq_sep]; rw [← Measure.restrict_apply₀
    (hf.ennreal_toReal.aestronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const)]; rw [← measure_sdiff_null (measure_eq_top_of_lintegral_ne_top hf h)] at this
  refine this.trans_le (measure_mono ?_)
  rintro x ⟨hfx, hx⟩
  dsimp at hfx
  rwa [← toReal_laverage hf, toReal_le_toReal hx (setLAverage_lt_top h).ne] at hfx
  simp_rw [ae_iff, not_ne_iff]
  exact measure_eq_top_of_lintegral_ne_top hf h

Depends on / 依赖: Measure, Measure.restrict_apply, aestronglyMeasurable, aestronglyMeasurable_const, ennreal_toReal, eq_or_ne, hf.aestronglyMeasurable.nullMeasurableSet_le, hf.ennreal_toReal.aestronglyMeasurable.nullMeasurableSet_le, integrable_toReal_of_lintegral_ne_top, laverage, measure_le_setAverage_pos, mul_top, nullMeasurableSet_le, ofPred_inter_eq_sep, pos_iff_ne_zero, top_div_of_ne_top
-/
theorem measure_le_setLAverage_pos (hμ : μ s != 0) (hμ₁ : μ s != ∞)
    (hf : AEMeasurable f (μ.restrict s)) : 0 < μ {x in s | f x <= ⨍⁻ a in s, f a ∂μ} := by
  obtain h | h := eq_or_ne (∫⁻ a in s, f a ∂μ) ∞
  · simpa [mul_top, hμ₁, laverage, h, top_div_of_ne_top hμ₁, pos_iff_ne_zero] using hμ
  have := measure_le_setAverage_pos hμ hμ₁ (integrable_toReal_of_lintegral_ne_top hf h)
  rw [← ofPred_inter_eq_sep]; rw [← Measure.restrict_apply₀
    (hf.aestronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const)]
  rw [← ofPred_inter_eq_sep]; rw [← Measure.restrict_apply₀
    (hf.ennreal_toReal.aestronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const)]; rw [← measure_sdiff_null (measure_eq_top_of_lintegral_ne_top hf h)] at this
  refine this.trans_le (measure_mono ?_)
  rintro x ⟨hfx, hx⟩
  dsimp at hfx
  rwa [← toReal_laverage hf, toReal_le_toReal hx (setLAverage_lt_top h).ne] at hfx
  simp_rw [ae_iff, not_ne_iff]
  exact measure_eq_top_of_lintegral_ne_top hf h

/--
theorem `measure_setLAverage_le_pos` / 定理 `measure_setLAverage_le_pos`

English:
theorem measure_setLAverage_le_pos
  statement: (hμ : μ s != 0) (hs : NullMeasurableSet s μ)
  proof: by
  obtain hμ₁ | hμ₁ := eq_or_ne (μ s) ∞
  · simp [setLAverage_eq, hμ₁]
  obtain ⟨g, hg, hgf, hfg⟩ := exists_measurable_le_lintegral_eq (μ.restrict s) f
  have hfg' : ⨍⁻ a in s, f a ∂μ = ⨍⁻ a in s, g a ∂μ := by simp_rw [laverage_eq, hfg]
  rw [hfg] at hint
  have :=
    measure_setAverage_le_pos hμ hμ₁ (integrable_toReal_of_lintegral_ne_top hg.aemeasurable hint)
  simp_rw [← ofPred_inter_eq_sep, ← Measure.restrict_apply₀' hs, hfg']
  rw [← ofPred_inter_eq_sep]; rw [← Measure.restrict_apply₀' hs]; rw [←
    measure_sdiff_null (measure_eq_top_of_lintegral_ne_top hg.aemeasurable hint)] at this
  refine this.trans_le (measure_mono ?_)
  rintro x ⟨hfx, hx⟩
  dsimp at hfx
  rw [← toReal_laverage hg.aemeasurable]; rw [toReal_le_toReal (setLAverage_lt_top hint).ne hx] at hfx
  · exact hfx.trans (hgf _)
  · simp_rw [ae_iff, not_ne_iff]
    exact measure_eq_top_of_lintegral_ne_top hg.aemeasurable hint

中文:
定理 measure_setLAverage_le_pos
  结论: (hμ : μ s != 0) (hs : NullMeasurableSet s μ)
  证明: by
  obtain hμ₁ | hμ₁ := eq_or_ne (μ s) ∞
  · simp [setLAverage_eq, hμ₁]
  obtain ⟨g, hg, hgf, hfg⟩ := exists_measurable_le_lintegral_eq (μ.restrict s) f
  have hfg' : ⨍⁻ a in s, f a ∂μ = ⨍⁻ a in s, g a ∂μ := by simp_rw [laverage_eq, hfg]
  rw [hfg] at hint
  have :=
    measure_setAverage_le_pos hμ hμ₁ (integrable_toReal_of_lintegral_ne_top hg.aemeasurable hint)
  simp_rw [← ofPred_inter_eq_sep, ← Measure.restrict_apply₀' hs, hfg']
  rw [← ofPred_inter_eq_sep]; rw [← Measure.restrict_apply₀' hs]; rw [←
    measure_sdiff_null (measure_eq_top_of_lintegral_ne_top hg.aemeasurable hint)] at this
  refine this.trans_le (measure_mono ?_)
  rintro x ⟨hfx, hx⟩
  dsimp at hfx
  rw [← toReal_laverage hg.aemeasurable]; rw [toReal_le_toReal (setLAverage_lt_top hint).ne hx] at hfx
  · exact hfx.trans (hgf _)
  · simp_rw [ae_iff, not_ne_iff]
    exact measure_eq_top_of_lintegral_ne_top hg.aemeasurable hint

Depends on / 依赖: Measure, Measure.restrict_apply, aemeasurable, eq_or_ne, exists_measurable_le_lintegral_eq, hg.aemeasurable, integrable_toReal_of_lintegral_ne_top, laverage_eq, measure_sdi, measure_setAverage_le_pos, ofPred_inter_eq_sep, restrict, setLAverage_eq, simp_rw
-/
theorem measure_setLAverage_le_pos (hμ : μ s != 0) (hs : NullMeasurableSet s μ)
    (hint : ∫⁻ a in s, f a ∂μ != ∞) : 0 < μ {x in s | ⨍⁻ a in s, f a ∂μ <= f x} := by
  obtain hμ₁ | hμ₁ := eq_or_ne (μ s) ∞
  · simp [setLAverage_eq, hμ₁]
  obtain ⟨g, hg, hgf, hfg⟩ := exists_measurable_le_lintegral_eq (μ.restrict s) f
  have hfg' : ⨍⁻ a in s, f a ∂μ = ⨍⁻ a in s, g a ∂μ := by simp_rw [laverage_eq, hfg]
  rw [hfg] at hint
  have :=
    measure_setAverage_le_pos hμ hμ₁ (integrable_toReal_of_lintegral_ne_top hg.aemeasurable hint)
  simp_rw [← ofPred_inter_eq_sep, ← Measure.restrict_apply₀' hs, hfg']
  rw [← ofPred_inter_eq_sep]; rw [← Measure.restrict_apply₀' hs]; rw [←
    measure_sdiff_null (measure_eq_top_of_lintegral_ne_top hg.aemeasurable hint)] at this
  refine this.trans_le (measure_mono ?_)
  rintro x ⟨hfx, hx⟩
  dsimp at hfx
  rw [← toReal_laverage hg.aemeasurable]; rw [toReal_le_toReal (setLAverage_lt_top hint).ne hx] at hfx
  · exact hfx.trans (hgf _)
  · simp_rw [ae_iff, not_ne_iff]
    exact measure_eq_top_of_lintegral_ne_top hg.aemeasurable hint

/--
theorem `exists_le_setLAverage` / 定理 `exists_le_setLAverage`

English:
theorem exists_le_setLAverage
  given: (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : AEMeasurable f (μ.restrict s))
  proof: let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_setLAverage_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩

中文:
定理 存在_le_setLAverage
  条件: (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : 几乎处处可测 f (μ.restrict s))
  证明: let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_setLAverage_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩

Depends on / 依赖: measure_le_setLAverage_pos, nonempty_of_measure_ne_zero
-/
theorem exists_le_setLAverage (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : AEMeasurable f (μ.restrict s)) :
    exists x in s, f x <= ⨍⁻ a in s, f a ∂μ :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_setLAverage_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩

/--
theorem `exists_setLAverage_le` / 定理 `exists_setLAverage_le`

English:
theorem exists_setLAverage_le
  statement: (hμ : μ s != 0) (hs : NullMeasurableSet s μ)
  proof: let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_setLAverage_le_pos hμ hs hint).ne'
  ⟨x, hx, h⟩

中文:
定理 存在_setLAverage_le
  结论: (hμ : μ s != 0) (hs : NullMeasurableSet s μ)
  证明: let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_setLAverage_le_pos hμ hs hint).ne'
  ⟨x, hx, h⟩

Depends on / 依赖: measure_setLAverage_le_pos, nonempty_of_measure_ne_zero
-/
theorem exists_setLAverage_le (hμ : μ s != 0) (hs : NullMeasurableSet s μ)
    (hint : ∫⁻ a in s, f a ∂μ != ∞) : exists x in s, ⨍⁻ a in s, f a ∂μ <= f x :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_setLAverage_le_pos hμ hs hint).ne'
  ⟨x, hx, h⟩

/--
theorem `measure_laverage_le_pos` / 定理 `measure_laverage_le_pos`

English:
theorem measure_laverage_le_pos
  given: (hμ : μ != 0) (hint : ∫⁻ a, f a ∂μ != ∞)
  proof: by
  simpa [hint] using
    @measure_setLAverage_le_pos _ _ _ _ f (measure_univ_ne_zero.2 hμ) nullMeasurableSet_univ

中文:
定理 measure_laverage_le_pos
  条件: (hμ : μ != 0) (hint : ∫⁻ a, f a ∂μ != ∞)
  证明: by
  simpa [hint] using
    @measure_setLAverage_le_pos _ _ _ _ f (measure_univ_ne_zero.2 hμ) nullMeasurableSet_univ

Depends on / 依赖: measure_setLAverage_le_pos, measure_univ_ne_zero, nullMeasurableSet_univ
-/
theorem measure_laverage_le_pos (hμ : μ != 0) (hint : ∫⁻ a, f a ∂μ != ∞) :
    0 < μ {x | ⨍⁻ a, f a ∂μ <= f x} := by
  simpa [hint] using
    @measure_setLAverage_le_pos _ _ _ _ f (measure_univ_ne_zero.2 hμ) nullMeasurableSet_univ

/--
theorem `exists_laverage_le` / 定理 `exists_laverage_le`

English:
theorem exists_laverage_le
  given: (hμ : μ != 0) (hint : ∫⁻ a, f a ∂μ != ∞)
  statement: exists x, ⨍⁻ a, f a ∂μ <= f x
  proof: let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_laverage_le_pos hμ hint).ne'
  ⟨x, hx⟩

中文:
定理 存在_laverage_le
  条件: (hμ : μ != 0) (hint : ∫⁻ a, f a ∂μ != ∞)
  结论: 存在 x, ⨍⁻ a, f a ∂μ <= f x
  证明: let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_laverage_le_pos hμ hint).ne'
  ⟨x, hx⟩

Depends on / 依赖: measure_laverage_le_pos, nonempty_of_measure_ne_zero
-/
theorem exists_laverage_le (hμ : μ != 0) (hint : ∫⁻ a, f a ∂μ != ∞) : exists x, ⨍⁻ a, f a ∂μ <= f x :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_laverage_le_pos hμ hint).ne'
  ⟨x, hx⟩

/--
theorem `exists_notMem_null_laverage_le` / 定理 `exists_notMem_null_laverage_le`

English:
theorem exists_notMem_null_laverage_le
  given: (hμ : μ != 0) (hint : ∫⁻ a : α, f a ∂μ != ∞) (hN : μ N = 0)
  proof: by
  have := measure_laverage_le_pos hμ hint
  rw [← measure_sdiff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩

中文:
定理 存在_notMem_null_laverage_le
  条件: (hμ : μ != 0) (hint : ∫⁻ a : α, f a ∂μ != ∞) (hN : μ N = 0)
  证明: by
  have := measure_laverage_le_pos hμ hint
  rw [← measure_sdiff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩

Depends on / 依赖: measure_laverage_le_pos, measure_sdiff_null, nonempty_of_measure_ne_zero, this.ne
-/
theorem exists_notMem_null_laverage_le (hμ : μ != 0) (hint : ∫⁻ a : α, f a ∂μ != ∞) (hN : μ N = 0) :
    exists x, x ∉ N ∧ ⨍⁻ a, f a ∂μ <= f x := by
  have := measure_laverage_le_pos hμ hint
  rw [← measure_sdiff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩

section FiniteMeasure
variable [IsFiniteMeasure μ]

/--
theorem `measure_le_laverage_pos` / 定理 `measure_le_laverage_pos`

English:
theorem measure_le_laverage_pos
  given: (hμ : μ != 0) (hf : AEMeasurable f μ)
  proof: by
  simpa using
    measure_le_setLAverage_pos (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _) hf.restrict

中文:
定理 measure_le_laverage_pos
  条件: (hμ : μ != 0) (hf : 几乎处处可测 f μ)
  证明: by
  simpa using
    measure_le_setLAverage_pos (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _) hf.restrict

Depends on / 依赖: hf.restrict, measure_le_setLAverage_pos, measure_ne_top, measure_univ_ne_zero, restrict
-/
theorem measure_le_laverage_pos (hμ : μ != 0) (hf : AEMeasurable f μ) :
    0 < μ {x | f x <= ⨍⁻ a, f a ∂μ} := by
  simpa using
    measure_le_setLAverage_pos (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _) hf.restrict

/--
theorem `exists_le_laverage` / 定理 `exists_le_laverage`

English:
theorem exists_le_laverage
  given: (hμ : μ != 0) (hf : AEMeasurable f μ)
  statement: exists x, f x <= ⨍⁻ a, f a ∂μ
  proof: let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_laverage_pos hμ hf).ne'
  ⟨x, hx⟩

中文:
定理 存在_le_laverage
  条件: (hμ : μ != 0) (hf : 几乎处处可测 f μ)
  结论: 存在 x, f x <= ⨍⁻ a, f a ∂μ
  证明: let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_laverage_pos hμ hf).ne'
  ⟨x, hx⟩

Depends on / 依赖: measure_le_laverage_pos, nonempty_of_measure_ne_zero
-/
theorem exists_le_laverage (hμ : μ != 0) (hf : AEMeasurable f μ) : exists x, f x <= ⨍⁻ a, f a ∂μ :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_laverage_pos hμ hf).ne'
  ⟨x, hx⟩

/--
theorem `exists_notMem_null_le_laverage` / 定理 `exists_notMem_null_le_laverage`

English:
theorem exists_notMem_null_le_laverage
  given: (hμ : μ != 0) (hf : AEMeasurable f μ) (hN : μ N = 0)
  proof: by
  have := measure_le_laverage_pos hμ hf
  rw [← measure_sdiff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩

中文:
定理 存在_notMem_null_le_laverage
  条件: (hμ : μ != 0) (hf : 几乎处处可测 f μ) (hN : μ N = 0)
  证明: by
  have := measure_le_laverage_pos hμ hf
  rw [← measure_sdiff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩

Depends on / 依赖: measure_le_laverage_pos, measure_sdiff_null, nonempty_of_measure_ne_zero, this.ne
-/
theorem exists_notMem_null_le_laverage (hμ : μ != 0) (hf : AEMeasurable f μ) (hN : μ N = 0) :
    exists x, x ∉ N ∧ f x <= ⨍⁻ a, f a ∂μ := by
  have := measure_le_laverage_pos hμ hf
  rw [← measure_sdiff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩

end FiniteMeasure

section ProbabilityMeasure

variable [IsProbabilityMeasure μ]

/--
theorem `measure_le_lintegral_pos` / 定理 `measure_le_lintegral_pos`

English:
theorem measure_le_lintegral_pos
  given: (hf : AEMeasurable f μ)
  statement: 0 < μ {x | f x <= ∫⁻ a, f a ∂μ}
  proof: by
  simpa only [laverage_eq_lintegral] using
    measure_le_laverage_pos (IsProbabilityMeasure.ne_zero μ) hf

中文:
定理 measure_le_lintegral_pos
  条件: (hf : 几乎处处可测 f μ)
  结论: 0 < μ {x | f x <= ∫⁻ a, f a ∂μ}
  证明: by
  simpa only [laverage_eq_lintegral] using
    measure_le_laverage_pos (IsProbabilityMeasure.ne_zero μ) hf

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.ne_zero, laverage_eq_lintegral, measure_le_laverage_pos, ne_zero
-/
theorem measure_le_lintegral_pos (hf : AEMeasurable f μ) : 0 < μ {x | f x <= ∫⁻ a, f a ∂μ} := by
  simpa only [laverage_eq_lintegral] using
    measure_le_laverage_pos (IsProbabilityMeasure.ne_zero μ) hf

/--
theorem `measure_lintegral_le_pos` / 定理 `measure_lintegral_le_pos`

English:
theorem measure_lintegral_le_pos
  given: (hint : ∫⁻ a, f a ∂μ != ∞)
  statement: 0 < μ {x | ∫⁻ a, f a ∂μ <= f x}
  proof: by
  simpa only [laverage_eq_lintegral] using
    measure_laverage_le_pos (IsProbabilityMeasure.ne_zero μ) hint

中文:
定理 measure_lintegral_le_pos
  条件: (hint : ∫⁻ a, f a ∂μ != ∞)
  结论: 0 < μ {x | ∫⁻ a, f a ∂μ <= f x}
  证明: by
  simpa only [laverage_eq_lintegral] using
    measure_laverage_le_pos (IsProbabilityMeasure.ne_zero μ) hint

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.ne_zero, laverage_eq_lintegral, measure_laverage_le_pos, ne_zero
-/
theorem measure_lintegral_le_pos (hint : ∫⁻ a, f a ∂μ != ∞) : 0 < μ {x | ∫⁻ a, f a ∂μ <= f x} := by
  simpa only [laverage_eq_lintegral] using
    measure_laverage_le_pos (IsProbabilityMeasure.ne_zero μ) hint

/--
theorem `exists_le_lintegral` / 定理 `exists_le_lintegral`

English:
theorem exists_le_lintegral
  given: (hf : AEMeasurable f μ)
  statement: exists x, f x <= ∫⁻ a, f a ∂μ
  proof: by
  simpa only [laverage_eq_lintegral] using exists_le_laverage (IsProbabilityMeasure.ne_zero μ) hf

中文:
定理 存在_le_lintegral
  条件: (hf : 几乎处处可测 f μ)
  结论: 存在 x, f x <= ∫⁻ a, f a ∂μ
  证明: by
  simpa only [laverage_eq_lintegral] using exists_le_laverage (IsProbabilityMeasure.ne_zero μ) hf

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.ne_zero, exists_le_laverage, laverage_eq_lintegral, ne_zero
-/
theorem exists_le_lintegral (hf : AEMeasurable f μ) : exists x, f x <= ∫⁻ a, f a ∂μ := by
  simpa only [laverage_eq_lintegral] using exists_le_laverage (IsProbabilityMeasure.ne_zero μ) hf

/--
theorem `exists_lintegral_le` / 定理 `exists_lintegral_le`

English:
theorem exists_lintegral_le
  given: (hint : ∫⁻ a, f a ∂μ != ∞)
  statement: exists x, ∫⁻ a, f a ∂μ <= f x
  proof: by
  simpa only [laverage_eq_lintegral] using
    exists_laverage_le (IsProbabilityMeasure.ne_zero μ) hint

中文:
定理 存在_lintegral_le
  条件: (hint : ∫⁻ a, f a ∂μ != ∞)
  结论: 存在 x, ∫⁻ a, f a ∂μ <= f x
  证明: by
  simpa only [laverage_eq_lintegral] using
    exists_laverage_le (IsProbabilityMeasure.ne_zero μ) hint

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.ne_zero, exists_laverage_le, laverage_eq_lintegral, ne_zero
-/
theorem exists_lintegral_le (hint : ∫⁻ a, f a ∂μ != ∞) : exists x, ∫⁻ a, f a ∂μ <= f x := by
  simpa only [laverage_eq_lintegral] using
    exists_laverage_le (IsProbabilityMeasure.ne_zero μ) hint

/--
theorem `exists_notMem_null_le_lintegral` / 定理 `exists_notMem_null_le_lintegral`

English:
theorem exists_notMem_null_le_lintegral
  given: (hf : AEMeasurable f μ) (hN : μ N = 0)
  proof: by
  simpa only [laverage_eq_lintegral] using
    exists_notMem_null_le_laverage (IsProbabilityMeasure.ne_zero μ) hf hN

中文:
定理 存在_notMem_null_le_lintegral
  条件: (hf : 几乎处处可测 f μ) (hN : μ N = 0)
  证明: by
  simpa only [laverage_eq_lintegral] using
    exists_notMem_null_le_laverage (IsProbabilityMeasure.ne_zero μ) hf hN

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.ne_zero, exists_notMem_null_le_laverage, laverage_eq_lintegral, ne_zero
-/
theorem exists_notMem_null_le_lintegral (hf : AEMeasurable f μ) (hN : μ N = 0) :
    exists x, x ∉ N ∧ f x <= ∫⁻ a, f a ∂μ := by
  simpa only [laverage_eq_lintegral] using
    exists_notMem_null_le_laverage (IsProbabilityMeasure.ne_zero μ) hf hN

/--
theorem `exists_notMem_null_lintegral_le` / 定理 `exists_notMem_null_lintegral_le`

English:
theorem exists_notMem_null_lintegral_le
  given: (hint : ∫⁻ a, f a ∂μ != ∞) (hN : μ N = 0)
  proof: by
  simpa only [laverage_eq_lintegral] using
    exists_notMem_null_laverage_le (IsProbabilityMeasure.ne_zero μ) hint hN

中文:
定理 存在_notMem_null_lintegral_le
  条件: (hint : ∫⁻ a, f a ∂μ != ∞) (hN : μ N = 0)
  证明: by
  simpa only [laverage_eq_lintegral] using
    exists_notMem_null_laverage_le (IsProbabilityMeasure.ne_zero μ) hint hN

Depends on / 依赖: IsProbabilityMeasure, IsProbabilityMeasure.ne_zero, exists_notMem_null_laverage_le, laverage_eq_lintegral, ne_zero
-/
theorem exists_notMem_null_lintegral_le (hint : ∫⁻ a, f a ∂μ != ∞) (hN : μ N = 0) :
    exists x, x ∉ N ∧ ∫⁻ a, f a ∂μ <= f x := by
  simpa only [laverage_eq_lintegral] using
    exists_notMem_null_laverage_le (IsProbabilityMeasure.ne_zero μ) hint hN

end ProbabilityMeasure
end FirstMomentENNReal

/--
theorem `tendsto_integral_smul_of_tendsto_average_norm_sub` / 定理 `tendsto_integral_smul_of_tendsto_average_norm_sub`

English:
theorem tendsto_integral_smul_of_tendsto_average_norm_sub
  proof: by
  have g_int : forallᶠ i in l, Integrable (g i) μ := by
    filter_upwards [(tendsto_order.1 hg).1 _ zero_lt_one] with i hi
    contrapose hi
    simp only [integral_undef hi, lt_self_iff_false, not_false_eq_true]
  have I : forallᶠ i in l, ∫ y, g i y • (f y - c) ∂μ + (∫ y, g i y ∂μ) • c = ∫ y, g i y • f y ∂μ := by
    filter_upwards [f_int, g_int, g_supp, g_bound] with i hif hig hisupp hibound
    rw [← integral_smul_const]; rw [← integral_add]
    · simp only [smul_sub, sub_add_cancel]
    · simp_rw [smul_sub]
      apply Integrable.sub _ (hig.smul_const _)
      have A : Function.support (fun y => g i y • f y) subseteq a i := by
        apply Subset.trans _ hisupp
        exact Function.support_smul_subset_left _ _
      rw [← integrableOn_iff_integrable_of_support_subset A]
      apply Integrable.smul_of_top_right hif
      exact memLp_top_of_bound hig.aestronglyMeasurable.restrict
        (K / μ.real (a i)) (Eventually.of_forall hibound)
    · exact hig.smul_const _
  have L0 : Tendsto (fun i => ∫ y, g i y • (f y - c) ∂μ) l (𝓝 0) := by
    have := hf.const_mul K
    simp only [mul_zero] at this
    refine squeeze_zero_norm' ?_ this
    filter_upwards [g_supp, g_bound, f_int, (tendsto_order.1 hg).1 _ zero_lt_one]
      with i hi h'i h''i hi_int
    have mu_ai : μ (a i) < ∞ := by
      rw [lt_top_iff_ne_top]
      intro h
      simp only [h, ENNReal.toReal_top, _root_.div_zero, abs_nonpos_iff, measureReal_def] at h'i
      have : ∫ (y : α), g i y ∂μ = ∫ (y : α), 0 ∂μ := by congr; ext y; exact h'i y
      simp [this] at hi_int
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [average_eq, smul_eq_mul, ← integral_const_mul, norm_smul, ← mul_assoc,
      ← div_eq_mul_inv]
    have : forall x, x ∉ a i -> ‖g i x‖ * ‖(f x - c)‖ = 0 := by
      intro x hx
      have : g i x = 0 := by rw [← Function.notMem_support]; exact fun h => hx (hi h)
      simp [this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero this (μ := μ)]
    refine integral_mono_of_nonneg (Eventually.of_forall (fun x => by positivity)) ?_
      (Eventually.of_forall (fun x => ?_))
    · apply (Integrable.sub h''i _).norm.const_mul
      change IntegrableOn (fun _ => c) (a i) μ
      simp [mu_ai]
    · dsimp; gcongr; simpa using h'i x
  have := L0.add (hg.smul_const c)
  simp only [one_smul, zero_add] at this
  exact Tendsto.congr' I this

中文:
定理 tendsto_integral_smul_of_tendsto_average_norm_sub
  证明: by
  have g_int : forallᶠ i in l, Integrable (g i) μ := by
    filter_upwards [(tendsto_order.1 hg).1 _ zero_lt_one] with i hi
    contrapose hi
    simp only [integral_undef hi, lt_self_iff_false, not_false_eq_true]
  have I : forallᶠ i in l, ∫ y, g i y • (f y - c) ∂μ + (∫ y, g i y ∂μ) • c = ∫ y, g i y • f y ∂μ := by
    filter_upwards [f_int, g_int, g_supp, g_bound] with i hif hig hisupp hibound
    rw [← integral_smul_const]; rw [← integral_add]
    · simp only [smul_sub, sub_add_cancel]
    · simp_rw [smul_sub]
      apply Integrable.sub _ (hig.smul_const _)
      have A : Function.support (fun y => g i y • f y) subseteq a i := by
        apply Subset.trans _ hisupp
        exact Function.support_smul_subset_left _ _
      rw [← integrableOn_iff_integrable_of_support_subset A]
      apply Integrable.smul_of_top_right hif
      exact memLp_top_of_bound hig.aestronglyMeasurable.restrict
        (K / μ.real (a i)) (Eventually.of_forall hibound)
    · exact hig.smul_const _
  have L0 : Tendsto (fun i => ∫ y, g i y • (f y - c) ∂μ) l (𝓝 0) := by
    have := hf.const_mul K
    simp only [mul_zero] at this
    refine squeeze_zero_norm' ?_ this
    filter_upwards [g_supp, g_bound, f_int, (tendsto_order.1 hg).1 _ zero_lt_one]
      with i hi h'i h''i hi_int
    have mu_ai : μ (a i) < ∞ := by
      rw [lt_top_iff_ne_top]
      intro h
      simp only [h, ENNReal.toReal_top, _root_.div_zero, abs_nonpos_iff, measureReal_def] at h'i
      have : ∫ (y : α), g i y ∂μ = ∫ (y : α), 0 ∂μ := by congr; ext y; exact h'i y
      simp [this] at hi_int
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [average_eq, smul_eq_mul, ← integral_const_mul, norm_smul, ← mul_assoc,
      ← div_eq_mul_inv]
    have : forall x, x ∉ a i -> ‖g i x‖ * ‖(f x - c)‖ = 0 := by
      intro x hx
      have : g i x = 0 := by rw [← Function.notMem_support]; exact fun h => hx (hi h)
      simp [this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero this (μ := μ)]
    refine integral_mono_of_nonneg (Eventually.of_forall (fun x => by positivity)) ?_
      (Eventually.of_forall (fun x => ?_))
    · apply (Integrable.sub h''i _).norm.const_mul
      change IntegrableOn (fun _ => c) (a i) μ
      simp [mu_ai]
    · dsimp; gcongr; simpa using h'i x
  have := L0.add (hg.smul_const c)
  simp only [one_smul, zero_add] at this
  exact Tendsto.congr' I this

Depends on / 依赖: Integrable, contrapose, f_int, filter_upwards, g_bound, g_int, g_supp, hibound, hisupp, integral_add, integral_smul_const, integral_undef, lt_self_iff_false, not_false_eq_true, simp_rw, smul_sub, sub_add_cancel, tendsto_order, zero_lt_one
-/
theorem tendsto_integral_smul_of_tendsto_average_norm_sub
    [CompleteSpace E]
    {ι : Type*} {a : ι -> Set α} {l : Filter ι} {f : α -> E} {c : E} {g : ι -> α -> Real} (K : Real)
    (hf : Tendsto (fun i => ⨍ y in a i, ‖f y - c‖ ∂μ) l (𝓝 0))
    (f_int : forallᶠ i in l, IntegrableOn f (a i) μ)
    (hg : Tendsto (fun i => ∫ y, g i y ∂μ) l (𝓝 1))
    (g_supp : forallᶠ i in l, Function.support (g i) subseteq a i)
    (g_bound : forallᶠ i in l, forall x, |g i x| <= K / μ.real (a i)) :
    Tendsto (fun i => ∫ y, g i y • f y ∂μ) l (𝓝 c) := by
  have g_int : forallᶠ i in l, Integrable (g i) μ := by
    filter_upwards [(tendsto_order.1 hg).1 _ zero_lt_one] with i hi
    contrapose hi
    simp only [integral_undef hi, lt_self_iff_false, not_false_eq_true]
  have I : forallᶠ i in l, ∫ y, g i y • (f y - c) ∂μ + (∫ y, g i y ∂μ) • c = ∫ y, g i y • f y ∂μ := by
    filter_upwards [f_int, g_int, g_supp, g_bound] with i hif hig hisupp hibound
    rw [← integral_smul_const]; rw [← integral_add]
    · simp only [smul_sub, sub_add_cancel]
    · simp_rw [smul_sub]
      apply Integrable.sub _ (hig.smul_const _)
      have A : Function.support (fun y => g i y • f y) subseteq a i := by
        apply Subset.trans _ hisupp
        exact Function.support_smul_subset_left _ _
      rw [← integrableOn_iff_integrable_of_support_subset A]
      apply Integrable.smul_of_top_right hif
      exact memLp_top_of_bound hig.aestronglyMeasurable.restrict
        (K / μ.real (a i)) (Eventually.of_forall hibound)
    · exact hig.smul_const _
  have L0 : Tendsto (fun i => ∫ y, g i y • (f y - c) ∂μ) l (𝓝 0) := by
    have := hf.const_mul K
    simp only [mul_zero] at this
    refine squeeze_zero_norm' ?_ this
    filter_upwards [g_supp, g_bound, f_int, (tendsto_order.1 hg).1 _ zero_lt_one]
      with i hi h'i h''i hi_int
    have mu_ai : μ (a i) < ∞ := by
      rw [lt_top_iff_ne_top]
      intro h
      simp only [h, ENNReal.toReal_top, _root_.div_zero, abs_nonpos_iff, measureReal_def] at h'i
      have : ∫ (y : α), g i y ∂μ = ∫ (y : α), 0 ∂μ := by congr; ext y; exact h'i y
      simp [this] at hi_int
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [average_eq, smul_eq_mul, ← integral_const_mul, norm_smul, ← mul_assoc,
      ← div_eq_mul_inv]
    have : forall x, x ∉ a i -> ‖g i x‖ * ‖(f x - c)‖ = 0 := by
      intro x hx
      have : g i x = 0 := by rw [← Function.notMem_support]; exact fun h => hx (hi h)
      simp [this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero this (μ := μ)]
    refine integral_mono_of_nonneg (Eventually.of_forall (fun x => by positivity)) ?_
      (Eventually.of_forall (fun x => ?_))
    · apply (Integrable.sub h''i _).norm.const_mul
      change IntegrableOn (fun _ => c) (a i) μ
      simp [mu_ai]
    · dsimp; gcongr; simpa using h'i x
  have := L0.add (hg.smul_const c)
  simp only [one_smul, zero_add] at this
  exact Tendsto.congr' I this

/--
theorem `exists_eq_setAverage` / 定理 `exists_eq_setAverage`

English:
theorem exists_eq_setAverage
  proof: by
  let ave := ⨍ x in s, f x ∂μ
  let S₁ : Set α := {x | x in s ∧ f x <= ave}
  let S₂ : Set α := {x | x in s ∧ ave <= f x}
  have hS₁ : 0 < μ S₁ := measure_le_setAverage_pos hμ0 hμfin hint
  have hS₂ : 0 < μ S₂ := measure_setAverage_le_pos hμ0 hμfin hint
  rcases nonempty_of_measure_ne_zero hS₁.ne' with ⟨c₁, hc₁⟩
  rcases nonempty_of_measure_ne_zero hS₂.ne' with ⟨c₂, hc₂⟩
  apply hs.isPreconnected.intermediate_value hc₁.1 hc₂.1 hf
  grind

中文:
定理 存在_eq_setAverage
  证明: by
  let ave := ⨍ x in s, f x ∂μ
  let S₁ : Set α := {x | x in s ∧ f x <= ave}
  let S₂ : Set α := {x | x in s ∧ ave <= f x}
  have hS₁ : 0 < μ S₁ := measure_le_setAverage_pos hμ0 hμfin hint
  have hS₂ : 0 < μ S₂ := measure_setAverage_le_pos hμ0 hμfin hint
  rcases nonempty_of_measure_ne_zero hS₁.ne' with ⟨c₁, hc₁⟩
  rcases nonempty_of_measure_ne_zero hS₂.ne' with ⟨c₂, hc₂⟩
  apply hs.isPreconnected.intermediate_value hc₁.1 hc₂.1 hf
  grind

Depends on / 依赖: hs.isPreconnected.intermediate_value, intermediate_value, isPreconnected, measure_le_setAverage_pos, measure_setAverage_le_pos, nonempty_of_measure_ne_zero
-/
theorem exists_eq_setAverage
    [TopologicalSpace α] {f : α -> Real} (hs : IsConnected s) (hf : ContinuousOn f s)
    (hint : IntegrableOn f s μ) (hμfin : μ s != ⊤) (hμ0 : μ s != 0) :
    exists c in s, f c = ⨍ x in s, f x ∂μ := by
  let ave := ⨍ x in s, f x ∂μ
  let S₁ : Set α := {x | x in s ∧ f x <= ave}
  let S₂ : Set α := {x | x in s ∧ ave <= f x}
  have hS₁ : 0 < μ S₁ := measure_le_setAverage_pos hμ0 hμfin hint
  have hS₂ : 0 < μ S₂ := measure_setAverage_le_pos hμ0 hμfin hint
  rcases nonempty_of_measure_ne_zero hS₁.ne' with ⟨c₁, hc₁⟩
  rcases nonempty_of_measure_ne_zero hS₂.ne' with ⟨c₂, hc₂⟩
  apply hs.isPreconnected.intermediate_value hc₁.1 hc₂.1 hf
  grind

end MeasureTheory
