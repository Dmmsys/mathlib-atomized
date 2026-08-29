/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Integrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.FloorPow
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The strong law of large numbers

We prove the strong law of large numbers, in `ProbabilityTheory.strong_law_ae`:
If `X n` is a sequence of independent identically distributed integrable random
variables, then `∑ i ∈ range n, X i / n` converges almost surely to `𝔼[X 0]`.
We give here the strong version, due to Etemadi, that only requires pairwise independence.

This file also contains the Lᵖ version of the strong law of large numbers provided by
`ProbabilityTheory.strong_law_Lp` which shows `∑ i ∈ range n, X i / n` converges in Lᵖ to
`𝔼[X 0]` provided `X n` is independent identically distributed and is Lᵖ.

## Implementation

The main point is to prove the result for real-valued random variables, as the general case
of Banach-space-valued random variables follows from this case and approximation by simple
functions. The real version is given in `ProbabilityTheory.strong_law_ae_real`.

We follow the proof by Etemadi
[Etemadi, *An elementary proof of the strong law of large numbers*][etemadi_strong_law],
which goes as follows.

It suffices to prove the result for nonnegative `X`, as one can prove the general result by
splitting a general `X` into its positive part and negative part.
Consider `Xₙ` a sequence of nonnegative integrable identically distributed pairwise independent
random variables. Let `Yₙ` be the truncation of `Xₙ` up to `n`. We claim that
* Almost surely, `Xₙ = Yₙ` for all but finitely many indices. Indeed, `∑ ℙ (Xₙ ≠ Yₙ)` is bounded by
  `1 + 𝔼[X]` (see `sum_prob_mem_Ioc_le` and `tsum_prob_mem_Ioi_lt_top`).
* Let `c > 1`. Along the sequence `n = c ^ k`, then `(∑_{i=0}^{n-1} Yᵢ - 𝔼[Yᵢ])/n` converges almost
  surely to `0`. This follows from a variance control, as
  ```
  ∑_k ℙ (|∑_{i=0}^{c^k - 1} Yᵢ - 𝔼[Yᵢ]| > c^k ε)
    ≤ ∑_k (c^k ε)^{-2} ∑_{i=0}^{c^k - 1} Var[Yᵢ] (by Markov inequality)
    ≤ ∑_i (C/i^2) Var[Yᵢ] (as ∑_{c^k > i} 1/(c^k)^2 ≤ C/i^2)
    ≤ ∑_i (C/i^2) 𝔼[Yᵢ^2]
    ≤ 2C 𝔼[X^2] (see `sum_variance_truncation_le`)
  ```
* As `𝔼[Yᵢ]` converges to `𝔼[X]`, it follows from the two previous items and Cesàro that, along
  the sequence `n = c^k`, one has `(∑_{i=0}^{n-1} Xᵢ) / n → 𝔼[X]` almost surely.
* To generalize it to all indices, we use the fact that `∑_{i=0}^{n-1} Xᵢ` is nondecreasing and
  that, if `c` is close enough to `1`, the gap between `c^k` and `c^(k+1)` is small.
-/

@[expose] public section


noncomputable section

open MeasureTheory Filter Finset Asymptotics

open Set (indicator)

open scoped Topology MeasureTheory ProbabilityTheory ENNReal NNReal

open scoped Function -- required for scoped `on` notation

namespace ProbabilityTheory

/-! ### Prerequisites on truncations -/


section Truncation

variable {α : Type*}

/--
Definition of `truncation` / `truncation` 的定义

English:
definition truncation
  signature: (f : α -> Real) (A : Real)
  body: indicator (Set.Ioc (-A) A) id ∘ f

中文:
定义 truncation
  签名: (f : α -> 实数) (A : 实数)
  定义体: indicator (Set.Ioc (-A) A) id ∘ f

Depends on / 依赖: Set.Ioc, indicator
-/
def truncation (f : α -> Real) (A : Real) :=
  indicator (Set.Ioc (-A) A) id ∘ f

variable {m : MeasurableSpace α} {μ : Measure α} {f : α -> Real}

/--
theorem `_root_.MeasureTheory.AEStronglyMeasurable.truncation` / 定理 `_root_.MeasureTheory.AEStronglyMeasurable.truncation`

English:
theorem _root_.MeasureTheory.AEStronglyMeasurable.truncation
  statement: (hf : AEStronglyMeasurable f μ)
  proof: by
  apply AEStronglyMeasurable.comp_aemeasurable _ hf.aemeasurable
  exact (stronglyMeasurable_id.indicator measurableSet_Ioc).aestronglyMeasurable

中文:
定理 _root_.测度论.AEStronglyMeasurable.truncation
  结论: (hf : AEStronglyMeasurable f μ)
  证明: by
  apply AEStronglyMeasurable.comp_aemeasurable _ hf.aemeasurable
  exact (stronglyMeasurable_id.indicator measurableSet_Ioc).aestronglyMeasurable

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.comp_aemeasurable, aemeasurable, aestronglyMeasurable, comp_aemeasurable, hf.aemeasurable, indicator, measurableSet_Ioc, stronglyMeasurable_id, stronglyMeasurable_id.indicator
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.truncation (hf : AEStronglyMeasurable f μ)
    {A : Real} : AEStronglyMeasurable (truncation f A) μ := by
  apply AEStronglyMeasurable.comp_aemeasurable _ hf.aemeasurable
  exact (stronglyMeasurable_id.indicator measurableSet_Ioc).aestronglyMeasurable

/--
theorem `abs_truncation_le_bound` / 定理 `abs_truncation_le_bound`

English:
theorem abs_truncation_le_bound
  given: (f : α -> Real) (A : Real) (x : α)
  statement: |truncation f A x| <= |A|
  proof: by
  simp only [truncation, Set.indicator, id, Function.comp_apply]
  split_ifs with h
  · exact abs_le_abs h.2 (neg_le.2 h.1.le)
  · simp [abs_nonneg]

@[simp]

中文:
定理 abs_truncation_le_bound
  条件: (f : α -> 实数) (A : 实数) (x : α)
  结论: |truncation f A x| <= |A|
  证明: by
  simp only [truncation, Set.indicator, id, Function.comp_apply]
  split_ifs with h
  · exact abs_le_abs h.2 (neg_le.2 h.1.le)
  · simp [abs_nonneg]

@[simp]

Depends on / 依赖: Function, Function.comp_apply, Set.indicator, abs_le_abs, abs_nonneg, comp_apply, indicator, neg_le, split_ifs, truncation
-/
theorem abs_truncation_le_bound (f : α -> Real) (A : Real) (x : α) : |truncation f A x| <= |A| := by
  simp only [truncation, Set.indicator, id, Function.comp_apply]
  split_ifs with h
  · exact abs_le_abs h.2 (neg_le.2 h.1.le)
  · simp [abs_nonneg]

@[simp]
/--
theorem `truncation_zero` / 定理 `truncation_zero`

English:
theorem truncation_zero
  given: (f : α -> Real)
  statement: truncation f 0 = 0
  proof: by simp [truncation]; rfl

中文:
定理 truncation_zero
  条件: (f : α -> 实数)
  结论: truncation f 0 = 0
  证明: by simp [truncation]; rfl

Depends on / 依赖: truncation
-/
theorem truncation_zero (f : α -> Real) : truncation f 0 = 0 := by simp [truncation]; rfl

/--
theorem `abs_truncation_le_abs_self` / 定理 `abs_truncation_le_abs_self`

English:
theorem abs_truncation_le_abs_self
  given: (f : α -> Real) (A : Real) (x : α)
  statement: |truncation f A x| <= |f x|
  proof: by
  simp only [truncation, indicator, id, Function.comp_apply]
  split_ifs
  · exact le_rfl
  · simp [abs_nonneg]

中文:
定理 abs_truncation_le_abs_self
  条件: (f : α -> 实数) (A : 实数) (x : α)
  结论: |truncation f A x| <= |f x|
  证明: by
  simp only [truncation, indicator, id, Function.comp_apply]
  split_ifs
  · exact le_rfl
  · simp [abs_nonneg]

Depends on / 依赖: Function, Function.comp_apply, abs_nonneg, comp_apply, indicator, le_rfl, split_ifs, truncation
-/
theorem abs_truncation_le_abs_self (f : α -> Real) (A : Real) (x : α) : |truncation f A x| <= |f x| := by
  simp only [truncation, indicator, id, Function.comp_apply]
  split_ifs
  · exact le_rfl
  · simp [abs_nonneg]

/--
theorem `truncation_eq_self` / 定理 `truncation_eq_self`

English:
theorem truncation_eq_self
  given: {f : α -> Real} {A : Real} {x : α} (h : |f x| < A)
  proof: by
  simp only [truncation, indicator, id, Function.comp_apply, ite_eq_left_iff]
  intro H
  apply H.elim
  simp [(abs_lt.1 h).1, (abs_lt.1 h).2.le]

中文:
定理 truncation_eq_self
  条件: {f : α -> 实数} {A : 实数} {x : α} (h : |f x| < A)
  证明: by
  simp only [truncation, indicator, id, Function.comp_apply, ite_eq_left_iff]
  intro H
  apply H.elim
  simp [(abs_lt.1 h).1, (abs_lt.1 h).2.le]

Depends on / 依赖: Function, Function.comp_apply, H.elim, abs_lt, comp_apply, indicator, ite_eq_left_iff, truncation
-/
theorem truncation_eq_self {f : α -> Real} {A : Real} {x : α} (h : |f x| < A) :
    truncation f A x = f x := by
  simp only [truncation, indicator, id, Function.comp_apply, ite_eq_left_iff]
  intro H
  apply H.elim
  simp [(abs_lt.1 h).1, (abs_lt.1 h).2.le]

/--
theorem `truncation_eq_of_nonneg` / 定理 `truncation_eq_of_nonneg`

English:
theorem truncation_eq_of_nonneg
  given: {f : α -> Real} {A : Real} (h : forall x, 0 <= f x)
  proof: by
  ext x
  rcases (h x).lt_or_eq with (hx | hx)
  · simp only [truncation, indicator, hx, Set.mem_Ioc, id, Function.comp_apply]
    by_cases h'x : f x <= A
    · have : -A < f x := by linarith [h x]
      simp only [this, true_and]
    · simp only [h'x, and_false]
  · simp only [truncation, indica

中文:
定理 truncation_eq_of_nonneg
  条件: {f : α -> 实数} {A : 实数} (h : 对任意 x, 0 <= f x)
  证明: by
  ext x
  rcases (h x).lt_or_eq with (hx | hx)
  · simp only [truncation, indicator, hx, Set.mem_Ioc, id, Function.comp_apply]
    by_cases h'x : f x <= A
    · have : -A < f x := by linarith [h x]
      simp only [this, true_and]
    · simp only [h'x, and_false]
  · simp only [truncation, indica

Depends on / 依赖: Function, Function.comp_apply, Set.mem_Ioc, and_false, comp_apply, indicator, ite_self, lt_or_eq, mem_Ioc, true_and, truncation
-/
theorem truncation_eq_of_nonneg {f : α -> Real} {A : Real} (h : forall x, 0 <= f x) :
    truncation f A = indicator (Set.Ioc 0 A) id ∘ f := by
  ext x
  rcases (h x).lt_or_eq with (hx | hx)
  · simp only [truncation, indicator, hx, Set.mem_Ioc, id, Function.comp_apply]
    by_cases h'x : f x <= A
    · have : -A < f x := by linarith [h x]
      simp only [this, true_and]
    · simp only [h'x, and_false]
  · simp only [truncation, indicator, hx, id, Function.comp_apply, ite_self]

/--
theorem `truncation_nonneg` / 定理 `truncation_nonneg`

English:
theorem truncation_nonneg
  given: {f : α -> Real} (A : Real) {x : α} (h : 0 <= f x)
  statement: 0 <= truncation f A x
  proof: Set.indicator_apply_nonneg fun _ => h

中文:
定理 truncation_nonneg
  条件: {f : α -> 实数} (A : 实数) {x : α} (h : 0 <= f x)
  结论: 0 <= truncation f A x
  证明: Set.indicator_apply_nonneg fun _ => h

Depends on / 依赖: Set.indicator_apply_nonneg, indicator_apply_nonneg
-/
theorem truncation_nonneg {f : α -> Real} (A : Real) {x : α} (h : 0 <= f x) : 0 <= truncation f A x :=
  Set.indicator_apply_nonneg fun _ => h

/--
theorem `_root_.MeasureTheory.AEStronglyMeasurable.memLp_truncation` / 定理 `_root_.MeasureTheory.AEStronglyMeasurable.memLp_truncation`

English:
theorem _root_.MeasureTheory.AEStronglyMeasurable.memLp_truncation
  statement: [IsFiniteMeasure μ]
  proof: MemLp.of_bound hf.truncation |A| (Eventually.of_forall fun _ => abs_truncation_le_bound _ _ _)

中文:
定理 _root_.测度论.AEStronglyMeasurable.memLp_truncation
  结论: [是有限测度 μ]
  证明: MemLp.of_bound hf.truncation |A| (Eventually.of_forall fun _ => abs_truncation_le_bound _ _ _)

Depends on / 依赖: Eventually, Eventually.of_forall, MemLp.of_bound, abs_truncation_le_bound, hf.truncation, of_bound, of_forall, truncation
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.memLp_truncation [IsFiniteMeasure μ]
    (hf : AEStronglyMeasurable f μ) {A : Real} {p : Real>=0∞} : MemLp (truncation f A) p μ :=
  MemLp.of_bound hf.truncation |A| (Eventually.of_forall fun _ => abs_truncation_le_bound _ _ _)

/--
theorem `_root_.MeasureTheory.AEStronglyMeasurable.integrable_truncation` / 定理 `_root_.MeasureTheory.AEStronglyMeasurable.integrable_truncation`

English:
theorem _root_.MeasureTheory.AEStronglyMeasurable.integrable_truncation
  statement: [IsFiniteMeasure μ]
  proof: by
  rw [← memLp_one_iff_integrable]; exact hf.memLp_truncation

中文:
定理 _root_.测度论.AEStronglyMeasurable.integrable_truncation
  结论: [是有限测度 μ]
  证明: by
  rw [← memLp_one_iff_integrable]; exact hf.memLp_truncation

Depends on / 依赖: hf.memLp_truncation, memLp_one_iff_integrable, memLp_truncation
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.integrable_truncation [IsFiniteMeasure μ]
    (hf : AEStronglyMeasurable f μ) {A : Real} : Integrable (truncation f A) μ := by
  rw [← memLp_one_iff_integrable]; exact hf.memLp_truncation

/--
theorem `moment_truncation_eq_intervalIntegral` / 定理 `moment_truncation_eq_intervalIntegral`

English:
theorem moment_truncation_eq_intervalIntegral
  statement: (hf : AEStronglyMeasurable f μ) {A : Real} (hA : 0 <= A)
  proof: by
  have M : MeasurableSet (Set.Ioc (-A) A) := measurableSet_Ioc
  change ∫ x, (fun z => indicator (Set.Ioc (-A) A) id z ^ n) (f x) ∂μ = _
  rw [← integral_map (f := fun z => _ ^ n) hf.aemeasurable]; rw [intervalIntegral.integral_of_le]; rw [← integral_indicator M]
  · simp only [indicator, zero_po

中文:
定理 moment_truncation_eq_interval整数egral
  结论: (hf : AEStronglyMeasurable f μ) {A : 实数} (hA : 0 <= A)
  证明: by
  have M : MeasurableSet (Set.Ioc (-A) A) := measurableSet_Ioc
  change ∫ x, (fun z => indicator (Set.Ioc (-A) A) id z ^ n) (f x) ∂μ = _
  rw [← integral_map (f := fun z => _ ^ n) hf.aemeasurable]; rw [intervalIntegral.integral_of_le]; rw [← integral_indicator M]
  · simp only [indicator, zero_po

Depends on / 依赖: MeasurableSet, Set.Ioc, aemeasurable, aestronglyMeasurable, hf.aemeasurable, indicator, integral_indicator, integral_map, integral_of_le, intervalIntegral, intervalIntegral.integral_of_le, ite_pow, measurableSet_Ioc, measurable_id, measurable_id.indicator, pow_const, zero_pow
-/
theorem moment_truncation_eq_intervalIntegral (hf : AEStronglyMeasurable f μ) {A : Real} (hA : 0 <= A)
    {n : Nat} (hn : n != 0) : ∫ x, truncation f A x ^ n ∂μ = ∫ y in -A..A, y ^ n ∂Measure.map f μ := by
  have M : MeasurableSet (Set.Ioc (-A) A) := measurableSet_Ioc
  change ∫ x, (fun z => indicator (Set.Ioc (-A) A) id z ^ n) (f x) ∂μ = _
  rw [← integral_map (f := fun z => _ ^ n) hf.aemeasurable]; rw [intervalIntegral.integral_of_le]; rw [← integral_indicator M]
  · simp only [indicator, zero_pow hn, id, ite_pow]
  · linarith
  · exact ((measurable_id.indicator M).pow_const n).aestronglyMeasurable

/--
theorem `moment_truncation_eq_intervalIntegral_of_nonneg` / 定理 `moment_truncation_eq_intervalIntegral_of_nonneg`

English:
theorem moment_truncation_eq_intervalIntegral_of_nonneg
  statement: (hf : AEStronglyMeasurable f μ) {A : Real}
  proof: by
  have M : MeasurableSet (Set.Ioc 0 A) := measurableSet_Ioc
  have M' : MeasurableSet (Set.Ioc A 0) := measurableSet_Ioc
  rw [truncation_eq_of_nonneg h'f]
  change ∫ x, (fun z => indicator (Set.Ioc 0 A) id z ^ n) (f x) ∂μ = _
  rcases le_or_gt 0 A with (hA | hA)
  · rw [← integral_map (f := fun 

中文:
定理 moment_truncation_eq_interval整数egral_of_nonneg
  结论: (hf : AEStronglyMeasurable f μ) {A : 实数}
  证明: by
  have M : MeasurableSet (Set.Ioc 0 A) := measurableSet_Ioc
  have M' : MeasurableSet (Set.Ioc A 0) := measurableSet_Ioc
  rw [truncation_eq_of_nonneg h'f]
  change ∫ x, (fun z => indicator (Set.Ioc 0 A) id z ^ n) (f x) ∂μ = _
  rcases le_or_gt 0 A with (hA | hA)
  · rw [← integral_map (f := fun 

Depends on / 依赖: MeasurableSet, Set.Ioc, aemeasurable, aestronglyMeasurable, hf.aemeasurable, indicator, integral_indicator, integral_map, integral_of_le, intervalIntegral, intervalIntegral.integral_of_le, ite_pow, le_or_gt, measurableSet_Ioc, measurable_id, measurable_id.indicator, pow_const, truncation_eq_of_nonneg, zero_pow
-/
theorem moment_truncation_eq_intervalIntegral_of_nonneg (hf : AEStronglyMeasurable f μ) {A : Real}
    {n : Nat} (hn : n != 0) (h'f : 0 <= f) :
    ∫ x, truncation f A x ^ n ∂μ = ∫ y in 0..A, y ^ n ∂Measure.map f μ := by
  have M : MeasurableSet (Set.Ioc 0 A) := measurableSet_Ioc
  have M' : MeasurableSet (Set.Ioc A 0) := measurableSet_Ioc
  rw [truncation_eq_of_nonneg h'f]
  change ∫ x, (fun z => indicator (Set.Ioc 0 A) id z ^ n) (f x) ∂μ = _
  rcases le_or_gt 0 A with (hA | hA)
  · rw [← integral_map (f := fun z => _ ^ n) hf.aemeasurable, intervalIntegral.integral_of_le hA,
      ← integral_indicator M]
    · simp only [indicator, zero_pow hn, id, ite_pow]
    · exact ((measurable_id.indicator M).pow_const n).aestronglyMeasurable
  · rw [← integral_map (f := fun z => _ ^ n) hf.aemeasurable, intervalIntegral.integral_of_ge hA.le,
      ← integral_indicator M']
    · simp only [Set.Ioc_eq_empty_of_le hA.le, zero_pow hn, Set.indicator_empty, integral_zero,
        zero_eq_neg]
      apply integral_eq_zero_of_ae
      have : forallᵐ x ∂Measure.map f μ, (0 : Real) <= x :=
        (ae_map_iff hf.aemeasurable measurableSet_Ici).2 (Eventually.of_forall h'f)
      filter_upwards [this] with x hx
      simp only [indicator, Set.mem_Ioc, Pi.zero_apply, ite_eq_right_iff, and_imp]
      intro _ h''x
      have : x = 0 := by linarith
      simp [this, zero_pow hn]
    · exact ((measurable_id.indicator M).pow_const n).aestronglyMeasurable

/--
theorem `integral_truncation_eq_intervalIntegral` / 定理 `integral_truncation_eq_intervalIntegral`

English:
theorem integral_truncation_eq_intervalIntegral
  statement: (hf : AEStronglyMeasurable f μ) {A : Real}
  proof: by
  simpa using moment_truncation_eq_intervalIntegral hf hA one_ne_zero

中文:
定理 integral_truncation_eq_interval整数egral
  结论: (hf : AEStronglyMeasurable f μ) {A : 实数}
  证明: by
  simpa using moment_truncation_eq_intervalIntegral hf hA one_ne_zero

Depends on / 依赖: moment_truncation_eq_intervalIntegral, one_ne_zero
-/
theorem integral_truncation_eq_intervalIntegral (hf : AEStronglyMeasurable f μ) {A : Real}
    (hA : 0 <= A) : ∫ x, truncation f A x ∂μ = ∫ y in -A..A, y ∂Measure.map f μ := by
  simpa using moment_truncation_eq_intervalIntegral hf hA one_ne_zero

/--
theorem `integral_truncation_eq_intervalIntegral_of_nonneg` / 定理 `integral_truncation_eq_intervalIntegral_of_nonneg`

English:
theorem integral_truncation_eq_intervalIntegral_of_nonneg
  statement: (hf : AEStronglyMeasurable f μ) {A : Real}
  proof: by
  simpa using moment_truncation_eq_intervalIntegral_of_nonneg hf one_ne_zero h'f

中文:
定理 integral_truncation_eq_interval整数egral_of_nonneg
  结论: (hf : AEStronglyMeasurable f μ) {A : 实数}
  证明: by
  simpa using moment_truncation_eq_intervalIntegral_of_nonneg hf one_ne_zero h'f

Depends on / 依赖: moment_truncation_eq_intervalIntegral_of_nonneg, one_ne_zero
-/
theorem integral_truncation_eq_intervalIntegral_of_nonneg (hf : AEStronglyMeasurable f μ) {A : Real}
    (h'f : 0 <= f) : ∫ x, truncation f A x ∂μ = ∫ y in 0..A, y ∂Measure.map f μ := by
  simpa using moment_truncation_eq_intervalIntegral_of_nonneg hf one_ne_zero h'f

/--
theorem `integral_truncation_le_integral_of_nonneg` / 定理 `integral_truncation_le_integral_of_nonneg`

English:
theorem integral_truncation_le_integral_of_nonneg
  given: (hf : Integrable f μ) (h'f : 0 <= f) {A : Real}
  proof: by
  apply integral_mono_of_nonneg
    (Eventually.of_forall fun x => ?_) hf (Eventually.of_forall fun x => ?_)
  · exact truncation_nonneg _ (h'f x)
  · calc
      truncation f A x <= |truncation f A x| := le_abs_self _
      _ <= |f x| := abs_truncation_le_abs_self _ _ _
      _ = f x := abs_of_no

中文:
定理 integral_truncation_le_integral_of_nonneg
  条件: (hf : 可积 f μ) (h'f : 0 <= f) {A : 实数}
  证明: by
  apply integral_mono_of_nonneg
    (Eventually.of_forall fun x => ?_) hf (Eventually.of_forall fun x => ?_)
  · exact truncation_nonneg _ (h'f x)
  · calc
      truncation f A x <= |truncation f A x| := le_abs_self _
      _ <= |f x| := abs_truncation_le_abs_self _ _ _
      _ = f x := abs_of_no

Depends on / 依赖: Eventually, Eventually.of_forall, abs_of_nonneg, abs_truncation_le_abs_self, integral_mono_of_nonneg, le_abs_self, of_forall, truncation, truncation_nonneg
-/
theorem integral_truncation_le_integral_of_nonneg (hf : Integrable f μ) (h'f : 0 <= f) {A : Real} :
    ∫ x, truncation f A x ∂μ <= ∫ x, f x ∂μ := by
  apply integral_mono_of_nonneg
    (Eventually.of_forall fun x => ?_) hf (Eventually.of_forall fun x => ?_)
  · exact truncation_nonneg _ (h'f x)
  · calc
      truncation f A x <= |truncation f A x| := le_abs_self _
      _ <= |f x| := abs_truncation_le_abs_self _ _ _
      _ = f x := abs_of_nonneg (h'f x)

/--
theorem `tendsto_integral_truncation` / 定理 `tendsto_integral_truncation`

English:
theorem tendsto_integral_truncation
  given: {f : α -> Real} (hf : Integrable f μ)
  proof: by
  refine tendsto_integral_filter_of_dominated_convergence (fun x => abs (f x)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun A => hf.aestronglyMeasurable.truncation
  · filter_upwards with A
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact abs_truncation_le_abs_self _ _ _
  · exact 

中文:
定理 tendsto_integral_truncation
  条件: {f : α -> 实数} (hf : 可积 f μ)
  证明: by
  refine tendsto_integral_filter_of_dominated_convergence (fun x => abs (f x)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun A => hf.aestronglyMeasurable.truncation
  · filter_upwards with A
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact abs_truncation_le_abs_self _ _ _
  · exact 

Depends on / 依赖: Eventually, Eventually.of_forall, Ioi_mem_atTop, Real.norm_eq_abs, abs_truncation_le_abs_self, aestronglyMeasurable, filter_upwards, hf.abs, hf.aestronglyMeasurable.truncation, norm_eq_abs, of_forall, tendsto_const_nhds, tendsto_const_nhds.congr, tendsto_integral_filter_of_dominated_convergence, truncation, truncation_eq_self
-/
theorem tendsto_integral_truncation {f : α -> Real} (hf : Integrable f μ) :
    Tendsto (fun A => ∫ x, truncation f A x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x => abs (f x)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun A => hf.aestronglyMeasurable.truncation
  · filter_upwards with A
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact abs_truncation_le_abs_self _ _ _
  · exact hf.abs
  · filter_upwards with x
    apply tendsto_const_nhds.congr' _
    filter_upwards [Ioi_mem_atTop (abs (f x))] with A hA
    exact (truncation_eq_self hA).symm

/--
theorem `IdentDistrib.truncation` / 定理 `IdentDistrib.truncation`

English:
theorem IdentDistrib.truncation
  statement: {β : Type*} [MeasurableSpace β] {ν : Measure β} {f : α -> Real}
  proof: h.comp (measurable_id.indicator measurableSet_Ioc)

中文:
定理 同分布.truncation
  结论: {β : 类型} [可测空间 β] {ν : 测度 β} {f : α -> 实数}
  证明: h.comp (measurable_id.indicator measurableSet_Ioc)

Depends on / 依赖: h.comp, indicator, measurableSet_Ioc, measurable_id, measurable_id.indicator
-/
theorem IdentDistrib.truncation {β : Type*} [MeasurableSpace β] {ν : Measure β} {f : α -> Real}
    {g : β -> Real} (h : IdentDistrib f g μ ν) {A : Real} :
    IdentDistrib (truncation f A) (truncation g A) μ ν :=
  h.comp (measurable_id.indicator measurableSet_Ioc)

end Truncation

section StrongLawAeReal

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

section MomentEstimates

/--
theorem `sum_prob_mem_Ioc_le` / 定理 `sum_prob_mem_Ioc_le`

English:
theorem sum_prob_mem_Ioc_le
  statement: {X : Ω -> Real} (hint : Integrable X) (hnonneg : 0 <= X) {K : Nat} {N : Nat}
  proof: by
  let ρ : Measure Real := Measure.map X ℙ
  have : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hint.aemeasurable
  have A : ∑ j in range K, ∫ _ in j..N, (1 : Real) ∂ρ <= 𝔼[X] + 1 :=
    calc
      ∑ j in range K, ∫ _ in j..N, (1 : Real) ∂ρ =
          ∑ j in range K, ∑ i in Ico j N

中文:
定理 sum_prob_mem_Ioc_le
  结论: {X : Ω -> 实数} (hint : 可积 X) (hnonneg : 0 <= X) {K : 自然数} {N : 自然数}
  证明: by
  let ρ : Measure Real := Measure.map X ℙ
  have : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hint.aemeasurable
  have A : ∑ j in range K, ∫ _ in j..N, (1 : Real) ∂ρ <= 𝔼[X] + 1 :=
    calc
      ∑ j in range K, ∫ _ in j..N, (1 : Real) ∂ρ =
          ∑ j in range K, ∑ i in Ico j N

Depends on / 依赖: IsProbabilityMeasure, Measure, Measure.isProbabilityMeasure_map, Measure.map, aemeasurable, continuous_const, continuous_const.intervalIntegrable, hint.aemeasurable, intervalIntegrable, intervalIntegral, intervalIntegral.sum_integral_adjacent_intervals_Ico, isProbabilityMeasure_map, le.trans, mem_range, sum_congr, sum_integral_adjacent_intervals_Ico
-/
theorem sum_prob_mem_Ioc_le {X : Ω -> Real} (hint : Integrable X) (hnonneg : 0 <= X) {K : Nat} {N : Nat}
    (hKN : K <= N) :
    ∑ j in range K, ℙ {ω | X ω in Set.Ioc (j : Real) N} <= ENNReal.ofReal (𝔼[X] + 1) := by
  let ρ : Measure Real := Measure.map X ℙ
  have : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hint.aemeasurable
  have A : ∑ j in range K, ∫ _ in j..N, (1 : Real) ∂ρ <= 𝔼[X] + 1 :=
    calc
      ∑ j in range K, ∫ _ in j..N, (1 : Real) ∂ρ =
          ∑ j in range K, ∑ i in Ico j N, ∫ _ in i..(i + 1 : Nat), (1 : Real) ∂ρ := by
        apply sum_congr rfl fun j hj => ?_
        rw [intervalIntegral.sum_integral_adjacent_intervals_Ico ((mem_range.1 hj).le.trans hKN)]
        intro k _
        exact continuous_const.intervalIntegrable _ _
      _ = ∑ i in range N, ∑ j in range (min (i + 1) K), ∫ _ in i..(i + 1 : Nat), (1 : Real) ∂ρ := by
        simp_rw [sum_sigma']
        refine sum_nbij' (fun p => ⟨p.2, p.1⟩) (fun p => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_ <;>
          aesop (add simp Nat.lt_succ_iff)
      _ <= ∑ i in range N, (i + 1) * ∫ _ in i..(i + 1 : Nat), (1 : Real) ∂ρ := by
        gcongr with i
        simp only [Nat.cast_add, Nat.cast_one, sum_const, card_range, nsmul_eq_mul, Nat.cast_min]
        refine mul_le_mul_of_nonneg_right (min_le_left _ _) ?_
        apply intervalIntegral.integral_nonneg
        · simp only [le_add_iff_nonneg_right, zero_le_one]
        · simp only [zero_le_one, imp_true_iff]
      _ <= ∑ i in range N, ∫ x in i..(i + 1 : Nat), x + 1 ∂ρ := by
        gcongr with i
        have I : (i : Real) <= (i + 1 : Nat) := by
          simp only [Nat.cast_add, Nat.cast_one, le_add_iff_nonneg_right, zero_le_one]
        simp_rw [intervalIntegral.integral_of_le I, ← integral_const_mul]
        apply setIntegral_mono_on
        · exact continuous_const.integrableOn_Ioc
        · exact (continuous_id.add continuous_const).integrableOn_Ioc
        · exact measurableSet_Ioc
        · intro x hx
          simp only [Nat.cast_add, Nat.cast_one, Set.mem_Ioc] at hx
          simp [hx.1.le]
      _ = ∫ x in 0..N, x + 1 ∂ρ := by
        rw [intervalIntegral.sum_integral_adjacent_intervals fun k _ => ?_]
        · norm_cast
        · exact (continuous_id.add continuous_const).intervalIntegrable _ _
      _ = ∫ x in 0..N, x ∂ρ + ∫ x in 0..N, 1 ∂ρ := by
        rw [intervalIntegral.integral_add]
        · exact continuous_id.intervalIntegrable _ _
        · exact continuous_const.intervalIntegrable _ _
      _ = 𝔼[truncation X N] + ∫ x in 0..N, 1 ∂ρ := by
        rw [integral_truncation_eq_intervalIntegral_of_nonneg hint.1 hnonneg]
      _ <= 𝔼[X] + ∫ x in 0..N, 1 ∂ρ := by
        grw [integral_truncation_le_integral_of_nonneg hint hnonneg]
      _ <= 𝔼[X] + 1 := by
        gcongr
        rw [intervalIntegral.integral_of_le (Nat.cast_nonneg _)]
        simp only [integral_const, measureReal_restrict_apply', measurableSet_Ioc, Set.univ_inter,
          smul_eq_mul, mul_one]
        rw [← ENNReal.toReal_one]
        exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  have B : forall a b, ℙ {ω | X ω in Set.Ioc a b} = ENNReal.ofReal (∫ _ in Set.Ioc a b, (1 : Real) ∂ρ) := by
    intro a b
    rw [ofReal_setIntegral_one ρ _]; rw [Measure.map_apply_of_aemeasurable hint.aemeasurable measurableSet_Ioc]
    rfl
  calc
    ∑ j in range K, ℙ {ω | X ω in Set.Ioc (j : Real) N} =
        ∑ j in range K, ENNReal.ofReal (∫ _ in Set.Ioc (j : Real) N, (1 : Real) ∂ρ) := by simp_rw [B]
    _ = ENNReal.ofReal (∑ j in range K, ∫ _ in Set.Ioc (j : Real) N, (1 : Real) ∂ρ) := by
      simp [ENNReal.ofReal_sum_of_nonneg]
    _ = ENNReal.ofReal (∑ j in range K, ∫ _ in (j : Real)..N, (1 : Real) ∂ρ) := by
      congr 1
      refine sum_congr rfl fun j hj => ?_
      rw [intervalIntegral.integral_of_le (Nat.cast_le.2 ((mem_range.1 hj).le.trans hKN))]
    _ <= ENNReal.ofReal (𝔼[X] + 1) := ENNReal.ofReal_le_ofReal A

/--
theorem `tsum_prob_mem_Ioi_lt_top` / 定理 `tsum_prob_mem_Ioi_lt_top`

English:
theorem tsum_prob_mem_Ioi_lt_top
  given: {X : Ω -> Real} (hint : Integrable X) (hnonneg : 0 <= X)
  proof: by
  suffices forall K : Nat, ∑ j in range K, ℙ {ω | X ω in Set.Ioi (j : Real)} <= ENNReal.ofReal (𝔼[X] + 1) from
    (le_of_tendsto_of_tendsto (ENNReal.tendsto_nat_tsum _) tendsto_const_nhds
      (Eventually.of_forall this)).trans_lt ENNReal.ofReal_lt_top
  intro K
  have A : Tendsto (fun N : Nat 

中文:
定理 tsum_prob_mem_Ioi_lt_top
  条件: {X : Ω -> 实数} (hint : 可积 X) (hnonneg : 0 <= X)
  证明: by
  suffices forall K : Nat, ∑ j in range K, ℙ {ω | X ω in Set.Ioi (j : Real)} <= ENNReal.ofReal (𝔼[X] + 1) from
    (le_of_tendsto_of_tendsto (ENNReal.tendsto_nat_tsum _) tendsto_const_nhds
      (Eventually.of_forall this)).trans_lt ENNReal.ofReal_lt_top
  intro K
  have A : Tendsto (fun N : Nat 

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.ofReal_lt_top, ENNReal.tendsto_nat_tsum, Eventually, Eventually.of_forall, Set.Ioc, Set.Ioi, Tendsto, le_of_tendsto_of_tendsto, ofReal, ofReal_lt_top, of_forall, tendsto_const_nhds, tendsto_finsetSum, tendsto_nat_tsum, trans_lt
-/
theorem tsum_prob_mem_Ioi_lt_top {X : Ω -> Real} (hint : Integrable X) (hnonneg : 0 <= X) :
    (∑' j : Nat, ℙ {ω | X ω in Set.Ioi (j : Real)}) < ∞ := by
  suffices forall K : Nat, ∑ j in range K, ℙ {ω | X ω in Set.Ioi (j : Real)} <= ENNReal.ofReal (𝔼[X] + 1) from
    (le_of_tendsto_of_tendsto (ENNReal.tendsto_nat_tsum _) tendsto_const_nhds
      (Eventually.of_forall this)).trans_lt ENNReal.ofReal_lt_top
  intro K
  have A : Tendsto (fun N : Nat => ∑ j in range K, ℙ {ω | X ω in Set.Ioc (j : Real) N}) atTop
      (𝓝 (∑ j in range K, ℙ {ω | X ω in Set.Ioi (j : Real)})) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    have : {ω | X ω in Set.Ioi (i : Real)} = ⋃ N : Nat, {ω | X ω in Set.Ioc (i : Real) N} := by
      apply Set.Subset.antisymm _ _
      · intro ω hω
        obtain ⟨N, hN⟩ : exists N : Nat, X ω <= N := exists_nat_ge (X ω)
        exact Set.mem_iUnion.2 ⟨N, hω, hN⟩
      · simp +contextual only [Set.mem_Ioc, Set.mem_Ioi,
          Set.iUnion_subset_iff, Set.ofPred_subset_ofPred, imp_true_iff]
    rw [this]
    apply tendsto_measure_iUnion_atTop
    intro m n hmn x hx
    exact ⟨hx.1, hx.2.trans (Nat.cast_le.2 hmn)⟩
  apply le_of_tendsto_of_tendsto A tendsto_const_nhds
  filter_upwards [Ici_mem_atTop K] with N hN
  exact sum_prob_mem_Ioc_le hint hnonneg hN

/--
theorem `sum_variance_truncation_le` / 定理 `sum_variance_truncation_le`

English:
theorem sum_variance_truncation_le
  given: {X : Ω -> Real} (hint : Integrable X) (hnonneg : 0 <= X) (K : Nat)
  proof: by
  set Y := fun n : Nat => truncation X n
  let ρ : Measure Real := Measure.map X ℙ
  have Y2 : forall n, 𝔼[Y n ^ 2] = ∫ x in 0..n, x ^ 2 ∂ρ := by
    intro n
    change 𝔼[fun x => Y n x ^ 2] = _
    rw [moment_truncation_eq_intervalIntegral_of_nonneg hint.1 two_ne_zero hnonneg]
  calc
    ∑ j in 

中文:
定理 sum_variance_truncation_le
  条件: {X : Ω -> 实数} (hint : 可积 X) (hnonneg : 0 <= X) (K : 自然数)
  证明: by
  set Y := fun n : Nat => truncation X n
  let ρ : Measure Real := Measure.map X ℙ
  have Y2 : forall n, 𝔼[Y n ^ 2] = ∫ x in 0..n, x ^ 2 ∂ρ := by
    intro n
    change 𝔼[fun x => Y n x ^ 2] = _
    rw [moment_truncation_eq_intervalIntegral_of_nonneg hint.1 two_ne_zero hnonneg]
  calc
    ∑ j in 

Depends on / 依赖: Measure, Measure.map, hnonneg, moment_truncation_eq_intervalIntegral_of_nonneg, simp_rw, truncation, two_ne_zero
-/
theorem sum_variance_truncation_le {X : Ω -> Real} (hint : Integrable X) (hnonneg : 0 <= X) (K : Nat) :
    ∑ j in range K, ((j : Real) ^ 2)⁻¹ * 𝔼[truncation X j ^ 2] <= 2 * 𝔼[X] := by
  set Y := fun n : Nat => truncation X n
  let ρ : Measure Real := Measure.map X ℙ
  have Y2 : forall n, 𝔼[Y n ^ 2] = ∫ x in 0..n, x ^ 2 ∂ρ := by
    intro n
    change 𝔼[fun x => Y n x ^ 2] = _
    rw [moment_truncation_eq_intervalIntegral_of_nonneg hint.1 two_ne_zero hnonneg]
  calc
    ∑ j in range K, ((j : Real) ^ 2)⁻¹ * 𝔼[Y j ^ 2] =
        ∑ j in range K, ((j : Real) ^ 2)⁻¹ * ∫ x in 0..j, x ^ 2 ∂ρ := by simp_rw [Y2]
    _ = ∑ j in range K, ((j : Real) ^ 2)⁻¹ * ∑ k in range j, ∫ x in k..(k + 1 : Nat), x ^ 2 ∂ρ := by
      congr 1 with j
      congr 1
      rw [intervalIntegral.sum_integral_adjacent_intervals]
      · norm_cast
      intro k _
      exact (continuous_id.pow _).intervalIntegrable _ _
    _ = ∑ k in range K, (∑ j in Ioo k K, ((j : Real) ^ 2)⁻¹) * ∫ x in k..(k + 1 : Nat), x ^ 2 ∂ρ := by
      simp_rw [mul_sum, sum_mul, sum_sigma']
      refine sum_nbij' (fun p => ⟨p.2, p.1⟩) (fun p => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_ <;>
        aesop (add unsafe lt_trans)
    _ <= ∑ k in range K, 2 / (k + 1 : Real) * ∫ x in k..(k + 1 : Nat), x ^ 2 ∂ρ := by
      gcongr with k
      · refine intervalIntegral.integral_nonneg_of_forall ?_ fun u => sq_nonneg _
        simp
      · apply sum_Ioo_inv_sq_le
    _ <= ∑ k in range K, ∫ x in k..(k + 1 : Nat), 2 * x ∂ρ := by
      gcongr with k
      have Ik : (k : Real) <= (k + 1 : Nat) := by simp
      rw [← intervalIntegral.integral_const_mul]; rw [intervalIntegral.integral_of_le Ik]; rw [intervalIntegral.integral_of_le Ik]
      refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun x hx => ?_
      · apply Continuous.integrableOn_Ioc (by fun_prop)
      · apply Continuous.integrableOn_Ioc (by fun_prop)
      · calc
          2 / (↑k + 1) * x ^ 2 = x / (k + 1) * (2 * x) := by ring
          _ <= 1 * (2 * x) := by
              have : 0 < x := k.cast_nonneg.trans_lt hx.1
              gcongr
exact (div_le_one <| by positivity).2 mod_cast hx.2
          _ = 2 * x := by rw [one_mul]
    _ = 2 * ∫ x in (0 : Real)..K, x ∂ρ := by
      rw [intervalIntegral.sum_integral_adjacent_intervals fun k _ => ?_]
      swap; · exact (continuous_const.mul continuous_id').intervalIntegrable _ _
      rw [intervalIntegral.integral_const_mul]
      norm_cast
    _ <= 2 * 𝔼[X] := mul_le_mul_of_nonneg_left (by
      rw [← integral_truncation_eq_intervalIntegral_of_nonneg hint.1 hnonneg]
      exact integral_truncation_le_integral_of_nonneg hint hnonneg) zero_le_two

end MomentEstimates

/-! Proof of the strong law of large numbers (almost sure version, assuming only
pairwise independence) for nonnegative random variables, following Etemadi's proof. -/
section StrongLawNonneg

variable (X : Nat -> Ω -> Real) (hint : Integrable (X 0))
  (hindep : Pairwise (IndepFun on X)) (hident : forall i, IdentDistrib (X i) (X 0))
  (hnonneg : forall i ω, 0 <= X i ω)

include hint hindep hident hnonneg in
/--
theorem `strong_law_aux1` / 定理 `strong_law_aux1`

English:
theorem strong_law_aux1
  given: {c : Real} (c_one : 1 < c) {ε : Real} (εpos : 0 < ε)
  statement: forallᵐ ω, forallᶠ n : Nat in atTop,
  proof: by
  /- Let `S n = ∑ i ∈ range n, Y i` where `Y i = truncation (X i) i`. We should show that
    `|S k - 𝔼[S k]| / k ≤ ε` along the sequence of powers of `c`. For this, we apply Borel-Cantelli:
    it suffices to show that the converse probabilities are summable. From Chebyshev inequality,
    this 

中文:
定理 strong_law_aux1
  条件: {c : 实数} (c_one : 1 < c) {ε : 实数} (εpos : 0 < ε)
  结论: 对任意ᵐ ω, 对任意ᶠ n : 自然数 in atTop,
  证明: by
  /- Let `S n = ∑ i ∈ range n, Y i` where `Y i = truncation (X i) i`. We should show that
    `|S k - 𝔼[S k]| / k ≤ ε` along the sequence of powers of `c`. For this, we apply Borel-Cantelli:
    it suffices to show that the converse probabilities are summable. From Chebyshev inequality,
    this 
-/
theorem strong_law_aux1 {c : Real} (c_one : 1 < c) {ε : Real} (εpos : 0 < ε) : forallᵐ ω, forallᶠ n : Nat in atTop,
    |∑ i in range ⌊c ^ n⌋₊, truncation (X i) i ω - 𝔼[∑ i in range ⌊c ^ n⌋₊, truncation (X i) i]| <
    ε * ⌊c ^ n⌋₊ := by
  /- Let `S n = ∑ i ∈ range n, Y i` where `Y i = truncation (X i) i`. We should show that
    `|S k - 𝔼[S k]| / k ≤ ε` along the sequence of powers of `c`. For this, we apply Borel-Cantelli:
    it suffices to show that the converse probabilities are summable. From Chebyshev inequality,
    this will follow from a variance control `∑' Var[S (c^i)] / (c^i)^2 < ∞`. This is checked in
    `I2` using pairwise independence to expand the variance of the sum as the sum of the variances,
    and then a straightforward but tedious computation (essentially boiling down to the fact that
    the sum of `1/(c ^ i)^2` beyond a threshold `j` is comparable to `1/j^2`).
    Note that we have written `c^i` in the above proof sketch, but rigorously one should put integer
    parts everywhere, making things more painful. We write `u i = ⌊c^i⌋₊` for brevity. -/
  have c_pos : 0 < c := zero_lt_one.trans c_one
  have hX : forall i, AEStronglyMeasurable (X i) ℙ := fun i =>
    (hident i).symm.aestronglyMeasurable_snd hint.1
  have A : forall i, StronglyMeasurable (indicator (Set.Ioc (-i : Real) i) id) := fun i =>
    stronglyMeasurable_id.indicator measurableSet_Ioc
  set Y := fun n : Nat => truncation (X n) n
  set S := fun n => ∑ i in range n, Y i with hS
  let u : Nat -> Nat := fun n => ⌊c ^ n⌋₊
  have u_mono : Monotone u := fun i j hij => Nat.floor_mono (pow_right_mono₀ c_one.le hij)
  have I1 : forall K, ∑ j in range K, ((j : Real) ^ 2)⁻¹ * Var[Y j] <= 2 * 𝔼[X 0] := by
    intro K
    calc
      ∑ j in range K, ((j : Real) ^ 2)⁻¹ * Var[Y j] <=
          ∑ j in range K, ((j : Real) ^ 2)⁻¹ * 𝔼[truncation (X 0) j ^ 2] := by
        gcongr with j
        rw [(hident j).truncation.variance_eq]
        exact variance_le_expectation_sq (hX 0).truncation
      _ <= 2 * 𝔼[X 0] := sum_variance_truncation_le hint (hnonneg 0) K
  let C := c ^ 5 * (c - 1)⁻¹ ^ 3 * (2 * 𝔼[X 0])
  have I2 : forall N, ∑ i in range N, ((u i : Real) ^ 2)⁻¹ * Var[S (u i)] <= C := by
    intro N
    calc
      ∑ i in range N, ((u i : Real) ^ 2)⁻¹ * Var[S (u i)] =
          ∑ i in range N, ((u i : Real) ^ 2)⁻¹ * ∑ j in range (u i), Var[Y j] := by
        congr 1 with i
        congr 1
        rw [hS]; rw [IndepFun.variance_sum]
        · intro j _
          exact (hident j).aestronglyMeasurable_fst.memLp_truncation
        · intro k _ l _ hkl
          exact (hindep hkl).comp (A k).measurable (A l).measurable
      _ = ∑ j in range (u (N - 1)), (∑ i in range N with j < u i, ((u i : Real) ^ 2)⁻¹) * Var[Y j] := by
        simp_rw [mul_sum, sum_mul, sum_sigma']
        refine sum_nbij' (fun p => ⟨p.2, p.1⟩) (fun p => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
        · simp only [mem_sigma, mem_range, mem_filter, and_imp,
            Sigma.forall]
exact fun a b haN hb => ⟨hb.trans_le u_mono Nat.le_pred_of_lt haN, haN, hb⟩
        all_goals simp
      _ <= ∑ j in range (u (N - 1)), c ^ 5 * (c - 1)⁻¹ ^ 3 / ↑j ^ 2 * Var[Y j] := by
        gcongr ∑ _ in _, ?_ with j
        rcases eq_zero_or_pos j with (rfl | hj)
        · simp only [Nat.cast_zero]
          simp only [Y, Nat.cast_zero, truncation_zero, variance_zero, mul_zero, le_rfl]
        apply mul_le_mul_of_nonneg_right _ (variance_nonneg _ _)
        convert! sum_div_nat_floor_pow_sq_le_div_sq N (Nat.cast_pos.2 hj) c_one using 2
        · simp only [u, Nat.cast_lt]
        · simp only [u, one_div]
      _ = c ^ 5 * (c - 1)⁻¹ ^ 3 * ∑ j in range (u (N - 1)), ((j : Real) ^ 2)⁻¹ * Var[Y j] := by
        simp_rw [mul_sum, div_eq_mul_inv, mul_assoc]
      _ <= c ^ 5 * (c - 1)⁻¹ ^ 3 * (2 * 𝔼[X 0]) := by
        apply mul_le_mul_of_nonneg_left (I1 _)
        apply mul_nonneg (pow_nonneg c_pos.le _)
        exact pow_nonneg (inv_nonneg.2 (sub_nonneg.2 c_one.le)) _
  have I3 : forall N, ∑ i in range N, ℙ {ω | (u i * ε : Real) <= |S (u i) ω - 𝔼[S (u i)]|} <=
      ENNReal.ofReal (ε⁻¹ ^ 2 * C) := by
    intro N
    calc
      ∑ i in range N, ℙ {ω | (u i * ε : Real) <= |S (u i) ω - 𝔼[S (u i)]|} <=
          ∑ i in range N, ENNReal.ofReal (Var[S (u i)] / (u i * ε) ^ 2) := by
        gcongr with i _
        apply meas_ge_le_variance_div_sq
        · exact memLp_finsetSum' _ fun j _ => (hident j).aestronglyMeasurable_fst.memLp_truncation
        · apply mul_pos (Nat.cast_pos.2 _) εpos
          refine zero_lt_one.trans_le ?_
          apply Nat.le_floor
          rw [Nat.cast_one]
          apply one_le_pow₀ c_one.le
      _ = ENNReal.ofReal (∑ i in range N, Var[S (u i)] / (u i * ε) ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => ?_]
        exact div_nonneg (variance_nonneg _ _) (sq_nonneg _)
      _ <= ENNReal.ofReal (ε⁻¹ ^ 2 * C) := by
        apply ENNReal.ofReal_le_ofReal
        simp_rw [div_eq_inv_mul, ← inv_pow, mul_inv, mul_comm _ (ε⁻¹), mul_pow, mul_assoc,
          ← mul_sum]
        gcongr
        simpa only [inv_pow] using I2 N
  have I4 : (∑' i, ℙ {ω | (u i * ε : Real) <= |S (u i) ω - 𝔼[S (u i)]|}) < ∞ :=
    (le_of_tendsto_of_tendsto' (ENNReal.tendsto_nat_tsum _) tendsto_const_nhds I3).trans_lt
      ENNReal.ofReal_lt_top
  filter_upwards [ae_eventually_notMem I4.ne] with ω hω
  simp_rw [S, not_le, mul_comm, Finset.sum_apply] at hω
  convert! hω; simp only [Y, u, Finset.sum_apply]

include hint hindep hident hnonneg in
/--
theorem `strong_law_aux2` / 定理 `strong_law_aux2`

English:
theorem strong_law_aux2
  given: {c : Real} (c_one : 1 < c)
  proof: by
  obtain ⟨v, -, v_pos, v_lim⟩ :
      exists v : Nat -> Real, StrictAnti v ∧ (forall n : Nat, 0 < v n) ∧ Tendsto v atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : Real)
  have := fun i => strong_law_aux1 X hint hindep hident hnonneg c_one (v_pos i)
  filter_upwards [ae_all_iff.2 this] with 

中文:
定理 strong_law_aux2
  条件: {c : 实数} (c_one : 1 < c)
  证明: by
  obtain ⟨v, -, v_pos, v_lim⟩ :
      exists v : Nat -> Real, StrictAnti v ∧ (forall n : Nat, 0 < v n) ∧ Tendsto v atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : Real)
  have := fun i => strong_law_aux1 X hint hindep hident hnonneg c_one (v_pos i)
  filter_upwards [ae_all_iff.2 this] with 

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_iff, Nat.abs_cast, Real.norm_eq_abs, StrictAnti, Tendsto, abs_cast, ae_all_iff, c_one, exists_seq_strictAnti_tendsto, filter_upwards, hident, hindep, hnonneg, isLittleO_iff, norm_eq_abs, strong_law_aux1, tendsto_order, v_lim, v_pos
-/
theorem strong_law_aux2 {c : Real} (c_one : 1 < c) :
    forallᵐ ω, (fun n : Nat => ∑ i in range ⌊c ^ n⌋₊, truncation (X i) i ω -
      𝔼[∑ i in range ⌊c ^ n⌋₊, truncation (X i) i]) =o[atTop] fun n : Nat => (⌊c ^ n⌋₊ : Real) := by
  obtain ⟨v, -, v_pos, v_lim⟩ :
      exists v : Nat -> Real, StrictAnti v ∧ (forall n : Nat, 0 < v n) ∧ Tendsto v atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : Real)
  have := fun i => strong_law_aux1 X hint hindep hident hnonneg c_one (v_pos i)
  filter_upwards [ae_all_iff.2 this] with ω hω
  apply Asymptotics.isLittleO_iff.2 fun ε εpos => ?_
  obtain ⟨i, hi⟩ : exists i, v i < ε := ((tendsto_order.1 v_lim).2 ε εpos).exists
  filter_upwards [hω i] with n hn
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  exact hn.le.trans (mul_le_mul_of_nonneg_right hi.le (Nat.cast_nonneg _))

include hint hident in
/--
theorem `strong_law_aux3` / 定理 `strong_law_aux3`

English:
theorem strong_law_aux3
  proof: by
  have A : Tendsto (fun i => 𝔼[truncation (X i) i]) atTop (𝓝 𝔼[X 0]) := by
    convert! (tendsto_integral_truncation hint).comp tendsto_natCast_atTop_atTop using 1
    ext i
    exact (hident i).truncation.integral_eq
  convert! Asymptotics.isLittleO_sum_range_of_tendsto_zero (tendsto_sub_nhds_ze

中文:
定理 strong_law_aux3
  证明: by
  have A : Tendsto (fun i => 𝔼[truncation (X i) i]) atTop (𝓝 𝔼[X 0]) := by
    convert! (tendsto_integral_truncation hint).comp tendsto_natCast_atTop_atTop using 1
    ext i
    exact (hident i).truncation.integral_eq
  convert! Asymptotics.isLittleO_sum_range_of_tendsto_zero (tendsto_sub_nhds_ze

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_sum_range_of_tendsto_zero, Finset, Finset.sum_apply, Tendsto, card_range, convert, hident, integr, integrable_snd, integral_eq, integral_finsetSum, isLittleO_sum_range_of_tendsto_zero, nsmul_eq_mul, sub_left_inj, sum_apply, sum_const, sum_sub_distrib, symm.integrable_snd, tendsto_integral_truncation
-/
theorem strong_law_aux3 :
    (fun n => 𝔼[∑ i in range n, truncation (X i) i] - n * 𝔼[X 0]) =o[atTop] ((↑) : Nat -> Real) := by
  have A : Tendsto (fun i => 𝔼[truncation (X i) i]) atTop (𝓝 𝔼[X 0]) := by
    convert! (tendsto_integral_truncation hint).comp tendsto_natCast_atTop_atTop using 1
    ext i
    exact (hident i).truncation.integral_eq
  convert! Asymptotics.isLittleO_sum_range_of_tendsto_zero (tendsto_sub_nhds_zero_iff.2 A) using 1
  ext1 n
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, Finset.sum_apply, sub_left_inj]
  rw [integral_finsetSum _ fun i _ => ?_]
  exact ((hident i).symm.integrable_snd hint).1.integrable_truncation

include hint hindep hident hnonneg in
/--
theorem `strong_law_aux4` / 定理 `strong_law_aux4`

English:
theorem strong_law_aux4
  given: {c : Real} (c_one : 1 < c)
  proof: by
  filter_upwards [strong_law_aux2 X hint hindep hident hnonneg c_one] with ω hω
  have A : Tendsto (fun n : Nat => ⌊c ^ n⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt c_one)
  convert! hω.add ((strong_law_aux3 X hint hident).comp_tendsto A) using 1
  ext1 

中文:
定理 strong_law_aux4
  条件: {c : 实数} (c_one : 1 < c)
  证明: by
  filter_upwards [strong_law_aux2 X hint hindep hident hnonneg c_one] with ω hω
  have A : Tendsto (fun n : Nat => ⌊c ^ n⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt c_one)
  convert! hω.add ((strong_law_aux3 X hint hident).comp_tendsto A) using 1
  ext1 

Depends on / 依赖: Tendsto, c_one, comp_tendsto, convert, filter_upwards, hident, hindep, hnonneg, strong_law_aux2, strong_law_aux3, tendsto_nat_floor_atTop, tendsto_nat_floor_atTop.comp, tendsto_pow_atTop_atTop_of_one_lt
-/
theorem strong_law_aux4 {c : Real} (c_one : 1 < c) :
    forallᵐ ω, (fun n : Nat => ∑ i in range ⌊c ^ n⌋₊, truncation (X i) i ω - ⌊c ^ n⌋₊ * 𝔼[X 0]) =o[atTop]
    fun n : Nat => (⌊c ^ n⌋₊ : Real) := by
  filter_upwards [strong_law_aux2 X hint hindep hident hnonneg c_one] with ω hω
  have A : Tendsto (fun n : Nat => ⌊c ^ n⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt c_one)
  convert! hω.add ((strong_law_aux3 X hint hident).comp_tendsto A) using 1
  ext1 n
  simp

include hint hident hnonneg in
/--
theorem `strong_law_aux5` / 定理 `strong_law_aux5`

English:
theorem strong_law_aux5
  proof: by
  have A : (∑' j : Nat, ℙ {ω | X j ω in Set.Ioi (j : Real)}) < ∞ := by
    convert! tsum_prob_mem_Ioi_lt_top hint (hnonneg 0) using 2
    ext1 j
    exact (hident j).measure_mem_eq measurableSet_Ioi
  have B : forallᵐ ω, Tendsto (fun n : Nat => truncation (X n) n ω - X n ω) atTop (𝓝 0) := by
    

中文:
定理 strong_law_aux5
  证明: by
  have A : (∑' j : Nat, ℙ {ω | X j ω in Set.Ioi (j : Real)}) < ∞ := by
    convert! tsum_prob_mem_Ioi_lt_top hint (hnonneg 0) using 2
    ext1 j
    exact (hident j).measure_mem_eq measurableSet_Ioi
  have B : forallᵐ ω, Tendsto (fun n : Nat => truncation (X n) n ω - X n ω) atTop (𝓝 0) := by
    

Depends on / 依赖: A.ne, Function, Function.comp_apply, Ioi_mem_atTop, Set.Ioi, Set.mem_Ioc, Tendsto, ae_eventually_notMem, comp_apply, convert, filter_upwards, hident, hnonneg, indicator, measurableSet_Ioi, measure_mem_eq, mem_Ioc, split_ifs, tendsto_const_nhds, tendsto_const_nhds.congr
-/
theorem strong_law_aux5 :
    forallᵐ ω, (fun n : Nat => ∑ i in range n, truncation (X i) i ω - ∑ i in range n, X i ω) =o[atTop]
    fun n : Nat => (n : Real) := by
  have A : (∑' j : Nat, ℙ {ω | X j ω in Set.Ioi (j : Real)}) < ∞ := by
    convert! tsum_prob_mem_Ioi_lt_top hint (hnonneg 0) using 2
    ext1 j
    exact (hident j).measure_mem_eq measurableSet_Ioi
  have B : forallᵐ ω, Tendsto (fun n : Nat => truncation (X n) n ω - X n ω) atTop (𝓝 0) := by
    filter_upwards [ae_eventually_notMem A.ne] with ω hω
    apply tendsto_const_nhds.congr' _
    filter_upwards [hω, Ioi_mem_atTop 0] with n hn npos
    simp only [truncation, indicator, Set.mem_Ioc, id, Function.comp_apply]
    split_ifs with h
    · exact (sub_self _).symm
    · have : -(n : Real) < X n ω := by
        apply lt_of_lt_of_le _ (hnonneg n ω)
        simpa only [Right.neg_neg_iff, Nat.cast_pos] using! npos
      simp only [this, true_and, not_le] at h
      exact (hn h).elim
  filter_upwards [B] with ω hω
  convert! isLittleO_sum_range_of_tendsto_zero hω using 1
  ext n
  rw [sum_sub_distrib]

include hint hindep hident hnonneg in
/--
theorem `strong_law_aux6` / 定理 `strong_law_aux6`

English:
theorem strong_law_aux6
  given: {c : Real} (c_one : 1 < c)
  proof: by
  have H : forall n : Nat, (0 : Real) < ⌊c ^ n⌋₊ := by
    intro n
    refine zero_lt_one.trans_le ?_
    simp only [Nat.one_le_cast, Nat.one_le_floor_iff, one_le_pow₀ c_one.le]
  filter_upwards [strong_law_aux4 X hint hindep hident hnonneg c_one,
    strong_law_aux5 X hint hident hnonneg] with ω

中文:
定理 strong_law_aux6
  条件: {c : 实数} (c_one : 1 < c)
  证明: by
  have H : forall n : Nat, (0 : Real) < ⌊c ^ n⌋₊ := by
    intro n
    refine zero_lt_one.trans_le ?_
    simp only [Nat.one_le_cast, Nat.one_le_floor_iff, one_le_pow₀ c_one.le]
  filter_upwards [strong_law_aux4 X hint hindep hident hnonneg c_one,
    strong_law_aux5 X hint hident hnonneg] with ω

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_one_iff, Nat.one_le_cast, Nat.one_le_floor_iff, Tendsto, c_one, c_one.le, filter_upwards, hident, hindep, hnonneg, isLittleO_one_iff, one_le_cast, one_le_floor_iff, strong_law_aux4, strong_law_aux5, tendsto_sub_nhds_zero_iff, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem strong_law_aux6 {c : Real} (c_one : 1 < c) :
    forallᵐ ω, Tendsto (fun n : Nat => (∑ i in range ⌊c ^ n⌋₊, X i ω) / ⌊c ^ n⌋₊) atTop (𝓝 𝔼[X 0]) := by
  have H : forall n : Nat, (0 : Real) < ⌊c ^ n⌋₊ := by
    intro n
    refine zero_lt_one.trans_le ?_
    simp only [Nat.one_le_cast, Nat.one_le_floor_iff, one_le_pow₀ c_one.le]
  filter_upwards [strong_law_aux4 X hint hindep hident hnonneg c_one,
    strong_law_aux5 X hint hident hnonneg] with ω hω h'ω
  rw [← tendsto_sub_nhds_zero_iff]; rw [← Asymptotics.isLittleO_one_iff Real]
  have L : (fun n : Nat => ∑ i in range ⌊c ^ n⌋₊, X i ω - ⌊c ^ n⌋₊ * 𝔼[X 0]) =o[atTop] fun n =>
      (⌊c ^ n⌋₊ : Real) := by
    have A : Tendsto (fun n : Nat => ⌊c ^ n⌋₊) atTop atTop :=
      tendsto_nat_floor_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt c_one)
    convert! hω.sub (h'ω.comp_tendsto A) using 1
    ext1 n
    simp only [Function.comp_apply, sub_sub_sub_cancel_left]
  convert! L.mul_isBigO (isBigO_refl (fun n : Nat => (⌊c ^ n⌋₊ : Real)⁻¹) atTop) using 1 <;>
  (ext1 n; field [(H n).ne'])

include hint hindep hident hnonneg in
/--
theorem `strong_law_aux7` / 定理 `strong_law_aux7`

English:
theorem strong_law_aux7
  proof: by
  obtain ⟨c, -, cone, clim⟩ :
      exists c : Nat -> Real, StrictAnti c ∧ (forall n : Nat, 1 < c n) ∧ Tendsto c atTop (𝓝 1) :=
    exists_seq_strictAnti_tendsto (1 : Real)
  have : forall k, forallᵐ ω,
      Tendsto (fun n : Nat => (∑ i in range ⌊c k ^ n⌋₊, X i ω) / ⌊c k ^ n⌋₊) atTop (𝓝 𝔼[X 0]) 

中文:
定理 strong_law_aux7
  证明: by
  obtain ⟨c, -, cone, clim⟩ :
      exists c : Nat -> Real, StrictAnti c ∧ (forall n : Nat, 1 < c n) ∧ Tendsto c atTop (𝓝 1) :=
    exists_seq_strictAnti_tendsto (1 : Real)
  have : forall k, forallᵐ ω,
      Tendsto (fun n : Nat => (∑ i in range ⌊c k ^ n⌋₊, X i ω) / ⌊c k ^ n⌋₊) atTop (𝓝 𝔼[X 0]) 

Depends on / 依赖: StrictAnti, Tendsto, ae_all_iff, exists_seq_strictAnti_tendsto, filter_upwards, hident, hindep, hnonneg, strong_law_aux6, sum_le_sum_o, tendsto_div_of_monotone_of_tendsto_div_floor_pow
-/
theorem strong_law_aux7 :
    forallᵐ ω, Tendsto (fun n : Nat => (∑ i in range n, X i ω) / n) atTop (𝓝 𝔼[X 0]) := by
  obtain ⟨c, -, cone, clim⟩ :
      exists c : Nat -> Real, StrictAnti c ∧ (forall n : Nat, 1 < c n) ∧ Tendsto c atTop (𝓝 1) :=
    exists_seq_strictAnti_tendsto (1 : Real)
  have : forall k, forallᵐ ω,
      Tendsto (fun n : Nat => (∑ i in range ⌊c k ^ n⌋₊, X i ω) / ⌊c k ^ n⌋₊) atTop (𝓝 𝔼[X 0]) :=
    fun k => strong_law_aux6 X hint hindep hident hnonneg (cone k)
  filter_upwards [ae_all_iff.2 this] with ω hω
  apply tendsto_div_of_monotone_of_tendsto_div_floor_pow _ _ _ c cone clim _
  · intro m n hmn
    exact sum_le_sum_of_subset_of_nonneg (range_mono hmn) fun i _ _ => hnonneg i ω
  · exact hω

end StrongLawNonneg

/--
theorem `strong_law_ae_real` / 定理 `strong_law_ae_real`

English:
theorem strong_law_ae_real
  statement: {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  proof: by
  let mΩ : MeasureSpace Ω := ⟨μ⟩
  -- first get rid of the trivial case where the space is not a probability space
  by_cases h : forallᵐ ω, X 0 ω = 0
  · have I : forallᵐ ω, forall i, X i ω = 0 := by
      rw [ae_all_iff]
      intro i
      exact (hident i).symm.ae_snd (p := fun x => x = 0) mea

中文:
定理 strong_law_ae_real
  结论: {Ω : 类型} {m : 可测空间 Ω} {μ : 测度 Ω}
  证明: by
  let mΩ : MeasureSpace Ω := ⟨μ⟩
  -- first get rid of the trivial case where the space is not a probability space
  by_cases h : forallᵐ ω, X 0 ω = 0
  · have I : forallᵐ ω, forall i, X i ω = 0 := by
      rw [ae_all_iff]
      intro i
      exact (hident i).symm.ae_snd (p := fun x => x = 0) mea

Depends on / 依赖: MeasureSpace
-/
theorem strong_law_ae_real {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    (X : Nat -> Ω -> Real) (hint : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : forall i, IdentDistrib (X i) (X 0) μ μ) :
    forallᵐ ω ∂μ, Tendsto (fun n : Nat => (∑ i in range n, X i ω) / n) atTop (𝓝 μ[X 0]) := by
  let mΩ : MeasureSpace Ω := ⟨μ⟩
  -- first get rid of the trivial case where the space is not a probability space
  by_cases h : forallᵐ ω, X 0 ω = 0
  · have I : forallᵐ ω, forall i, X i ω = 0 := by
      rw [ae_all_iff]
      intro i
      exact (hident i).symm.ae_snd (p := fun x => x = 0) measurableSet_eq h
    filter_upwards [I] with ω hω
    simpa [hω] using! (integral_eq_zero_of_ae h).symm
  have : IsProbabilityMeasure μ :=
    hint.isProbabilityMeasure_of_indepFun (X 0) (X 1) h (hindep zero_ne_one)
  -- then consider separately the positive and the negative part, and apply the result
  -- for nonnegative functions to them.
  let pos : Real -> Real := fun x => max x 0
  let neg : Real -> Real := fun x => max (-x) 0
  have posm : Measurable pos := measurable_id'.max measurable_const
  have negm : Measurable neg := measurable_id'.neg.max measurable_const
  have A : forallᵐ ω, Tendsto (fun n : Nat => (∑ i in range n, (pos ∘ X i) ω) / n) atTop (𝓝 𝔼[pos ∘ X 0]) :=
    strong_law_aux7 _ hint.pos_part (fun i j hij => (hindep hij).comp posm posm)
      (fun i => (hident i).comp posm) fun i ω => le_max_right _ _
  have B : forallᵐ ω, Tendsto (fun n : Nat => (∑ i in range n, (neg ∘ X i) ω) / n) atTop (𝓝 𝔼[neg ∘ X 0]) :=
    strong_law_aux7 _ hint.neg_part (fun i j hij => (hindep hij).comp negm negm)
      (fun i => (hident i).comp negm) fun i ω => le_max_right _ _
  filter_upwards [A, B] with ω hωpos hωneg
  convert! hωpos.sub hωneg using 2
  · simp only [pos, neg, ← sub_div, ← sum_sub_distrib, max_zero_sub_max_neg_zero_eq_self,
      Function.comp_apply]
  · simp +instances only [pos, neg, ← integral_sub hint.pos_part hint.neg_part,
      max_zero_sub_max_neg_zero_eq_self, Function.comp_apply, mΩ]

end StrongLawAeReal

section StrongLawVectorSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
  [MeasurableSpace E]

open Set TopologicalSpace

/--
lemma `strong_law_ae_simpleFunc_comp` / 引理 `strong_law_ae_simpleFunc_comp`

English:
lemma strong_law_ae_simpleFunc_comp
  statement: (X : Nat -> Ω -> E) (h' : Measurable (X 0))
  proof: by
  -- this follows from the one-dimensional version when `φ` takes a single value, and is then
  -- extended to the general case by linearity.
  refine SimpleFunc.induction (motive := fun ψ => forallᵐ ω ∂μ,
    Tendsto (fun n : Nat => (n : Real)⁻¹ • (∑ i in range n, ψ (X i ω))) atTop (𝓝 μ[ψ ∘ (X 0

中文:
引理 strong_law_ae_simpleFunc_comp
  结论: (X : 自然数 -> Ω -> E) (h' : 可测 (X 0))
  证明: by
  -- this follows from the one-dimensional version when `φ` takes a single value, and is then
  -- extended to the general case by linearity.
  refine SimpleFunc.induction (motive := fun ψ => forallᵐ ω ∂μ,
    Tendsto (fun n : Nat => (n : Real)⁻¹ • (∑ i in range n, ψ (X i ω))) atTop (𝓝 μ[ψ ∘ (X 0
-/
lemma strong_law_ae_simpleFunc_comp (X : Nat -> Ω -> E) (h' : Measurable (X 0))
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : forall i, IdentDistrib (X i) (X 0) μ μ) (φ : SimpleFunc E E) :
    forallᵐ ω ∂μ,
      Tendsto (fun n : Nat => (n : Real)⁻¹ • (∑ i in range n, φ (X i ω))) atTop (𝓝 μ[φ ∘ (X 0)]) := by
  -- this follows from the one-dimensional version when `φ` takes a single value, and is then
  -- extended to the general case by linearity.
  refine SimpleFunc.induction (motive := fun ψ => forallᵐ ω ∂μ,
    Tendsto (fun n : Nat => (n : Real)⁻¹ • (∑ i in range n, ψ (X i ω))) atTop (𝓝 μ[ψ ∘ (X 0)])) ?_ ?_ φ
  · intro c s hs
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, piecewise_eq_indicator, Function.comp_apply]
    let F : E -> Real := indicator s 1
    have F_meas : Measurable F := (measurable_indicator_const_iff 1).2 hs
    let Y : Nat -> Ω -> Real := fun n => F ∘ (X n)
    have : forallᵐ (ω : Ω) ∂μ, Tendsto (fun (n : Nat) => (n : Real)⁻¹ • ∑ i in Finset.range n, Y i ω)
        atTop (𝓝 μ[Y 0]) := by
      simp only [smul_eq_mul, ← div_eq_inv_mul]
      apply strong_law_ae_real
      · exact SimpleFunc.integrable_of_isFiniteMeasure
          ((SimpleFunc.piecewise s hs (SimpleFunc.const _ (1 : Real))
            (SimpleFunc.const _ (0 : Real))).comp (X 0) h')
      · exact fun i j hij => IndepFun.comp (hindep hij) F_meas F_meas
      · exact fun i => (hident i).comp F_meas
    filter_upwards [this] with ω hω
    have I : indicator s (Function.const E c) = (fun x => (indicator s (1 : E -> Real) x) • c) := by
      ext
      rw [← indicator_smul_const_apply]
      congr! 1
      ext
      simp
    simp only [I, integral_smul_const]
    convert! Tendsto.smul_const hω c using 1
    simp [F, Y, ← sum_smul, smul_smul]
  · rintro φ ψ - hφ hψ
    filter_upwards [hφ, hψ] with ω hωφ hωψ
    convert! hωφ.add hωψ using 1
    · simp [sum_add_distrib]
    · congr 1
      rw [← integral_add]
      · rfl
      · exact (φ.comp (X 0) h').integrable_of_isFiniteMeasure
      · exact (ψ.comp (X 0) h').integrable_of_isFiniteMeasure

variable [BorelSpace E]

/--
lemma `strong_law_ae_of_measurable` / 引理 `strong_law_ae_of_measurable`

English:
lemma strong_law_ae_of_measurable
  proof: by
  /- Choose a simple function `φ` such that `φ (X 0)` approximates well enough `X 0` -- this is
  possible as `X 0` is strongly measurable. Then `φ (X n)` approximates well `X n`.
  Then the strong law for `φ (X n)` implies the strong law for `X n`, up to a small
  error controlled by `n⁻¹ ∑_{i=0

中文:
引理 strong_law_ae_of_measurable
  证明: by
  /- Choose a simple function `φ` such that `φ (X 0)` approximates well enough `X 0` -- this is
  possible as `X 0` is strongly measurable. Then `φ (X n)` approximates well `X n`.
  Then the strong law for `φ (X n)` implies the strong law for `X n`, up to a small
  error controlled by `n⁻¹ ∑_{i=0
-/
lemma strong_law_ae_of_measurable
    (X : Nat -> Ω -> E) (hint : Integrable (X 0) μ) (h' : StronglyMeasurable (X 0))
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : forall i, IdentDistrib (X i) (X 0) μ μ) :
    forallᵐ ω ∂μ, Tendsto (fun n : Nat => (n : Real)⁻¹ • (∑ i in range n, X i ω)) atTop (𝓝 μ[X 0]) := by
  /- Choose a simple function `φ` such that `φ (X 0)` approximates well enough `X 0` -- this is
  possible as `X 0` is strongly measurable. Then `φ (X n)` approximates well `X n`.
  Then the strong law for `φ (X n)` implies the strong law for `X n`, up to a small
  error controlled by `n⁻¹ ∑_{i=0}^{n-1} ‖X i - φ (X i)‖`. This one is also controlled thanks
  to the one-dimensional law of large numbers: it converges ae to `𝔼[‖X 0 - φ (X 0)‖]`, which
  is arbitrarily small for well-chosen `φ`. -/
  let s : Set E := Set.range (X 0) union {0}
  have zero_s : 0 in s := by simp [s]
  have : SeparableSpace s := h'.separableSpace_range_union_singleton
  have : Nonempty s := ⟨0, zero_s⟩
  -- sequence of approximating simple functions.
  let φ : Nat -> SimpleFunc E E :=
    SimpleFunc.nearestPt (fun k => Nat.casesOn k 0 ((↑) ∘ denseSeq s) : Nat -> E)
  let Y : Nat -> Nat -> Ω -> E := fun k i => (φ k) ∘ (X i)
  -- strong law for `φ (X n)`
  have A : forallᵐ ω ∂μ, forall k,
      Tendsto (fun n : Nat => (n : Real)⁻¹ • (∑ i in range n, Y k i ω)) atTop (𝓝 μ[Y k 0]) :=
    ae_all_iff.2 (fun k => strong_law_ae_simpleFunc_comp X h'.measurable hindep hident (φ k))
  -- strong law for the error `‖X i - φ (X i)‖`
  have B : forallᵐ ω ∂μ, forall k, Tendsto (fun n : Nat => (∑ i in range n, ‖(X i - Y k i) ω‖) / n)
        atTop (𝓝 μ[(fun ω => ‖(X 0 - Y k 0) ω‖)]) := by
    apply ae_all_iff.2 (fun k => ?_)
    let G : Nat -> E -> Real := fun k x => ‖x - φ k x‖
    have G_meas : forall k, Measurable (G k) :=
      fun k => (measurable_id.sub_stronglyMeasurable (φ k).stronglyMeasurable).norm
    have I : forall k i, (fun ω => ‖(X i - Y k i) ω‖) = (G k) ∘ (X i) := fun k i => rfl
    apply strong_law_ae_real (fun i ω => ‖(X i - Y k i) ω‖)
    · exact (hint.sub ((φ k).comp (X 0) h'.measurable).integrable_of_isFiniteMeasure).norm
    · unfold Function.onFun
      simp_rw [I]
      intro i j hij
      exact (hindep hij).comp (G_meas k) (G_meas k)
    · intro i
      simp_rw [I]
      apply (hident i).comp (G_meas k)
  -- check that, when both convergences above hold, then the strong law is satisfied
  filter_upwards [A, B] with ω hω h'ω
  rw [tendsto_iff_norm_sub_tendsto_zero]; rw [tendsto_order]
  refine ⟨fun c hc => Eventually.of_forall (fun n => hc.trans_le (norm_nonneg _)), ?_⟩
  -- start with some positive `ε` (the desired precision), and fix `δ` with `3 δ < ε`.
  intro ε (εpos : 0 < ε)
  obtain ⟨δ, δpos, hδ⟩ : exists δ, 0 < δ ∧ δ + δ + δ < ε := ⟨ε/4, by positivity, by linarith⟩
  -- choose `k` large enough so that `φₖ (X 0)` approximates well enough `X 0`, up to the
  -- precision `δ`.
  obtain ⟨k, hk⟩ : exists k, ∫ ω, ‖(X 0 - Y k 0) ω‖ ∂μ < δ := by
    simp_rw [Pi.sub_apply, norm_sub_rev (X 0 _)]
    exact ((tendsto_order.1 (tendsto_integral_norm_approxOn_sub h'.measurable hint)).2 δ
      δpos).exists
  have : ‖μ[Y k 0] - μ[X 0]‖ < δ := by
    rw [norm_sub_rev]; rw [← integral_sub hint]
    · exact (norm_integral_le_integral_norm _).trans_lt hk
    · exact ((φ k).comp (X 0) h'.measurable).integrable_of_isFiniteMeasure
  -- consider `n` large enough for which the above convergences have taken place within `δ`.
  have I : forallᶠ n in atTop, (∑ i in range n, ‖(X i - Y k i) ω‖) / n < δ :=
    (tendsto_order.1 (h'ω k)).2 δ hk
  have J : forallᶠ (n : Nat) in atTop, ‖(n : Real)⁻¹ • (∑ i in range n, Y k i ω) - μ[Y k 0]‖ < δ := by
    specialize hω k
    rw [tendsto_iff_norm_sub_tendsto_zero] at hω
    exact (tendsto_order.1 hω).2 δ δpos
  filter_upwards [I, J] with n hn h'n
  -- at such an `n`, the strong law is realized up to `ε`.
  calc
  ‖(n : Real)⁻¹ • ∑ i in Finset.range n, X i ω - μ[X 0]‖
    = ‖(n : Real)⁻¹ • ∑ i in Finset.range n, (X i ω - Y k i ω) +
        ((n : Real)⁻¹ • ∑ i in Finset.range n, Y k i ω - μ[Y k 0]) + (μ[Y k 0] - μ[X 0])‖ := by
      congr
      simp only [sum_sub_distrib, smul_sub]
      abel
  _ <= ‖(n : Real)⁻¹ • ∑ i in Finset.range n, (X i ω - Y k i ω)‖ +
        ‖(n : Real)⁻¹ • ∑ i in Finset.range n, Y k i ω - μ[Y k 0]‖ + ‖μ[Y k 0] - μ[X 0]‖ :=
      norm_add₃_le
  _ <= (∑ i in Finset.range n, ‖X i ω - Y k i ω‖) / n + δ + δ := by
      gcongr
      simp only [norm_smul, norm_inv, RCLike.norm_natCast,
        div_eq_inv_mul]
      gcongr
      exact norm_sum_le _ _
  _ <= δ + δ + δ := by
      gcongr
      exact hn.le
  _ < ε := hδ

omit [IsProbabilityMeasure μ] in
/--
theorem `strong_law_ae` / 定理 `strong_law_ae`

English:
theorem strong_law_ae
  statement: (X : Nat -> Ω -> E) (hint : Integrable (X 0) μ)
  proof: by
  -- First exclude the trivial case where the space is not a probability space
  by_cases h : forallᵐ ω ∂μ, X 0 ω = 0
  · have I : forallᵐ ω ∂μ, forall i, X i ω = 0 := by
      rw [ae_all_iff]
      intro i
      exact (hident i).symm.ae_snd (p := fun x => x = 0) measurableSet_eq h
    filter_upw

中文:
定理 strong_law_ae
  结论: (X : 自然数 -> Ω -> E) (hint : 可积 (X 0) μ)
  证明: by
  -- First exclude the trivial case where the space is not a probability space
  by_cases h : forallᵐ ω ∂μ, X 0 ω = 0
  · have I : forallᵐ ω ∂μ, forall i, X i ω = 0 := by
      rw [ae_all_iff]
      intro i
      exact (hident i).symm.ae_snd (p := fun x => x = 0) measurableSet_eq h
    filter_upw
-/
theorem strong_law_ae (X : Nat -> Ω -> E) (hint : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : forall i, IdentDistrib (X i) (X 0) μ μ) :
    forallᵐ ω ∂μ, Tendsto (fun n : Nat => (n : Real)⁻¹ • (∑ i in range n, X i ω)) atTop (𝓝 μ[X 0]) := by
  -- First exclude the trivial case where the space is not a probability space
  by_cases h : forallᵐ ω ∂μ, X 0 ω = 0
  · have I : forallᵐ ω ∂μ, forall i, X i ω = 0 := by
      rw [ae_all_iff]
      intro i
      exact (hident i).symm.ae_snd (p := fun x => x = 0) measurableSet_eq h
    filter_upwards [I] with ω hω
    simpa [hω] using (integral_eq_zero_of_ae h).symm
  have : IsProbabilityMeasure μ :=
    hint.isProbabilityMeasure_of_indepFun (X 0) (X 1) h (hindep zero_ne_one)
  -- we reduce to the case of strongly measurable random variables, by using `Y i` which is strongly
  -- measurable and ae equal to `X i`.
  have A : forall i, Integrable (X i) μ := fun i => (hident i).integrable_iff.2 hint
  let Y : Nat -> Ω -> E := fun i => (A i).1.mk (X i)
  have B : forallᵐ ω ∂μ, forall n, X n ω = Y n ω :=
    ae_all_iff.2 (fun i => AEStronglyMeasurable.ae_eq_mk (A i).1)
  have Yint : Integrable (Y 0) μ := Integrable.congr hint (AEStronglyMeasurable.ae_eq_mk (A 0).1)
  have C : forallᵐ ω ∂μ,
      Tendsto (fun n : Nat => (n : Real)⁻¹ • (∑ i in range n, Y i ω)) atTop (𝓝 μ[Y 0]) := by
    apply strong_law_ae_of_measurable Y Yint ((A 0).1.stronglyMeasurable_mk)
      (fun i j hij => IndepFun.congr (hindep hij) (A i).1.ae_eq_mk (A j).1.ae_eq_mk)
      (fun i => ((A i).1.identDistrib_mk.symm.trans (hident i)).trans (A 0).1.identDistrib_mk)
  filter_upwards [B, C] with ω h₁ h₂
  have : μ[X 0] = μ[Y 0] := integral_congr_ae (AEStronglyMeasurable.ae_eq_mk (A 0).1)
  rw [this]
  apply Tendsto.congr (fun n => ?_) h₂
  congr with i
  exact (h₁ i).symm

end StrongLawVectorSpace

section StrongLawLp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/--
theorem `strong_law_Lp` / 定理 `strong_law_Lp`

English:
theorem strong_law_Lp
  statement: {p : Real>=0∞} (hp : 1 <= p) (hp' : p != ∞) (X : Nat -> Ω -> E)
  proof: by
  -- First exclude the trivial case where the space is not a probability space
  by_cases h : forallᵐ ω ∂μ, X 0 ω = 0
  · have I : forallᵐ ω ∂μ, forall i, X i ω = 0 := by
      rw [ae_all_iff]
      intro i
      exact (hident i).symm.ae_snd (p := fun x => x = 0) measurableSet_eq h
    have A (n 

中文:
定理 strong_law_Lp
  结论: {p : 实数>=0∞} (hp : 1 <= p) (hp' : p != ∞) (X : 自然数 -> Ω -> E)
  证明: by
  -- First exclude the trivial case where the space is not a probability space
  by_cases h : forallᵐ ω ∂μ, X 0 ω = 0
  · have I : forallᵐ ω ∂μ, forall i, X i ω = 0 := by
      rw [ae_all_iff]
      intro i
      exact (hident i).symm.ae_snd (p := fun x => x = 0) measurableSet_eq h
    have A (n 
-/
theorem strong_law_Lp {p : Real>=0∞} (hp : 1 <= p) (hp' : p != ∞) (X : Nat -> Ω -> E)
    (hℒp : MemLp (X 0) p μ) (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : forall i, IdentDistrib (X i) (X 0) μ μ) :
    Tendsto (fun (n : Nat) => eLpNorm (fun ω => (n : Real)⁻¹ • (∑ i in range n, X i ω) - μ[X 0]) p μ)
      atTop (𝓝 0) := by
  -- First exclude the trivial case where the space is not a probability space
  by_cases h : forallᵐ ω ∂μ, X 0 ω = 0
  · have I : forallᵐ ω ∂μ, forall i, X i ω = 0 := by
      rw [ae_all_iff]
      intro i
      exact (hident i).symm.ae_snd (p := fun x => x = 0) measurableSet_eq h
    have A (n : Nat) : eLpNorm (fun ω => (n : Real)⁻¹ • (∑ i in range n, X i ω) - μ[X 0]) p μ = 0 := by
      simp only [integral_eq_zero_of_ae h, sub_zero]
      apply eLpNorm_eq_zero_of_ae_zero
      filter_upwards [I] with ω hω
      simp [hω]
    simp [A]
  -- Then use ae convergence and uniform integrability
  have : IsProbabilityMeasure μ := MemLp.isProbabilityMeasure_of_indepFun
    (X 0) (X 1) (zero_lt_one.trans_le hp).ne' hp' hℒp h (hindep zero_ne_one)
  have hmeas : forall i, AEStronglyMeasurable (X i) μ := fun i =>
    (hident i).aestronglyMeasurable_iff.2 hℒp.1
  have hint : Integrable (X 0) μ := hℒp.integrable hp
  have havg (n : Nat) :
      AEStronglyMeasurable (fun ω => (n : Real)⁻¹ • (∑ i in range n, X i ω)) μ :=
    AEStronglyMeasurable.const_smul (aestronglyMeasurable_fun_sum _ fun i _ => hmeas i) _
  refine tendsto_Lp_finite_of_tendstoInMeasure hp hp' havg (memLp_const _) ?_
    (tendstoInMeasure_of_tendsto_ae havg (strong_law_ae _ hint hindep hident))
  rw [(_ : (fun (n : Nat) ω => (n : Real)⁻¹ • (∑ i in range n]; rw [X i ω))
            = fun (n : Nat) => (n : Real)⁻¹ • (∑ i in range n]; rw [X i))]
  · apply UniformIntegrable.unifIntegrable
    apply uniformIntegrable_average hp
    exact MemLp.uniformIntegrable_of_identDistrib hp hp' hℒp hident
  · ext n ω
    simp only [Pi.smul_apply, Finset.sum_apply]

end StrongLawLp

end ProbabilityTheory
