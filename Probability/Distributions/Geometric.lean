/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Geometric distributions

We define the geometric distributions over natural numbers. For `0 < p ≤ 1`, `geometricMeasure p`
is the measure which to `{n}` associates `(1 - p) ^ n * n`.

As the parameter `p` needs to lie between `0` and `1`, we define `geometricMeasure p` with
`p : unitInterval`.

Imagine a certain experience which has success probability `p`. If you repeat this experience
infinitely many times and independently, the number of failures before the first success
follows a geometric distribution with parameter `p`.

## Main definition

* `geometricMeasure p`: a geometric measure on a semiring `R`,
  parametrized by its success probability `p`.

## Implementation note

To avoid having to carry around a hypothesis `p ≠ 0`, we define
`geometricMeasure 0 := Measure.dirac 0`. That way `IsProbabilityMeasure (geometricMeasure p)`
can be automatically inferred.

## Tags

geometric distribution
-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

variable {p : unitInterval}

/--
Definition of `geometricMeasure` / `geometricMeasure` 的定义

English:
definition geometricMeasure
  signature: (p : unitInterval)
  body: if p != 0
  then
    Measure.sum (fun n => ENNReal.ofReal ((1 - p) ^ n * p) • .dirac n)
  else
    .dirac 0

中文:
定义 geometricMeasure
  签名: (p : unit整数erval)
  定义体: if p != 0
  then
    Measure.sum (fun n => ENNReal.ofReal ((1 - p) ^ n * p) • .dirac n)
  else
    .dirac 0
-/
noncomputable def geometricMeasure (p : unitInterval) : Measure Nat := if p != 0
  then
    Measure.sum (fun n => ENNReal.ofReal ((1 - p) ^ n * p) • .dirac n)
  else
    .dirac 0

/--
lemma `geometricMeasure_eq` / 引理 `geometricMeasure_eq`

English:
lemma geometricMeasure_eq
  given: (hp : p != 0)
  proof: if_pos hp

中文:
引理 geometricMeasure_eq
  条件: (hp : p != 0)
  证明: if_pos hp

Depends on / 依赖: if_pos
-/
lemma geometricMeasure_eq (hp : p != 0) :
    geometricMeasure p =
      Measure.sum (fun n => ENNReal.ofReal ((1 - p) ^ n * p) • .dirac n) :=
  if_pos hp

/--
lemma `geometricMeasure_nonneg` / 引理 `geometricMeasure_nonneg`

English:
lemma geometricMeasure_nonneg
  given: (p : unitInterval) n
  proof: mul_nonneg (pow_nonneg (by grind) n) p.2.1

中文:
引理 geometricMeasure_nonneg
  条件: (p : unit整数erval) n
  证明: mul_nonneg (pow_nonneg (by grind) n) p.2.1

Depends on / 依赖: mul_nonneg, pow_nonneg
-/
lemma geometricMeasure_nonneg (p : unitInterval) n :
    0 <= (1 - p : Real) ^ n * p := mul_nonneg (pow_nonneg (by grind) n) p.2.1

/--
lemma `geometricMeasure_pos` / 引理 `geometricMeasure_pos`

English:
lemma geometricMeasure_pos
  given: (h1 : p != 0) (h2 : p != 1) n
  proof: mul_pos (pow_pos (by grind) n) (by grind)

中文:
引理 geometricMeasure_pos
  条件: (h1 : p != 0) (h2 : p != 1) n
  证明: mul_pos (pow_pos (by grind) n) (by grind)

Depends on / 依赖: mul_pos, pow_pos
-/
lemma geometricMeasure_pos (h1 : p != 0) (h2 : p != 1) n :
    0 < (1 - p : Real) ^ n * p := mul_pos (pow_pos (by grind) n) (by grind)

/--
lemma `geometricMeasure_singleton` / 引理 `geometricMeasure_singleton`

English:
lemma geometricMeasure_singleton
  given: (hp : p != 0) n
  proof: by
  rw [geometricMeasure_eq hp]; rw [Measure.sum_smul_dirac_singleton]

中文:
引理 geometricMeasure_singleton
  条件: (hp : p != 0) n
  证明: by
  rw [geometricMeasure_eq hp]; rw [Measure.sum_smul_dirac_singleton]

Depends on / 依赖: Measure, Measure.sum_smul_dirac_singleton, geometricMeasure_eq, sum_smul_dirac_singleton
-/
lemma geometricMeasure_singleton (hp : p != 0) n :
    geometricMeasure p {n} = ENNReal.ofReal ((1 - p) ^ n * p) := by
  rw [geometricMeasure_eq hp]; rw [Measure.sum_smul_dirac_singleton]

/--
lemma `geometricMeasure_real_singleton` / 引理 `geometricMeasure_real_singleton`

English:
lemma geometricMeasure_real_singleton
  given: (hp : p != 0) n
  proof: by
  rw [measureReal_def]; rw [geometricMeasure_singleton hp]; rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

中文:
引理 geometricMeasure_real_singleton
  条件: (hp : p != 0) n
  证明: by
  rw [measureReal_def]; rw [geometricMeasure_singleton hp]; rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, geometricMeasure_nonneg, geometricMeasure_singleton, measureReal_def, toReal_ofReal
-/
lemma geometricMeasure_real_singleton (hp : p != 0) n :
    (geometricMeasure p).real {n} = (1 - p) ^ n * p := by
  rw [measureReal_def]; rw [geometricMeasure_singleton hp]; rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

/--
lemma `geometricMeasure_real_singleton_pos` / 引理 `geometricMeasure_real_singleton_pos`

English:
lemma geometricMeasure_real_singleton_pos
  given: (h1 : p != 0) (h2 : p != 1) n
  proof: by
  rw [geometricMeasure_real_singleton h1]
  exact geometricMeasure_pos h1 h2 n

中文:
引理 geometricMeasure_real_singleton_pos
  条件: (h1 : p != 0) (h2 : p != 1) n
  证明: by
  rw [geometricMeasure_real_singleton h1]
  exact geometricMeasure_pos h1 h2 n

Depends on / 依赖: geometricMeasure_pos, geometricMeasure_real_singleton
-/
lemma geometricMeasure_real_singleton_pos (h1 : p != 0) (h2 : p != 1) n :
    0 < (geometricMeasure p).real {n} := by
  rw [geometricMeasure_real_singleton h1]
  exact geometricMeasure_pos h1 h2 n

/--
lemma `hasSum_one_geometricMeasure` / 引理 `hasSum_one_geometricMeasure`

English:
lemma hasSum_one_geometricMeasure
  given: (hp : p != 0)
  proof: by
  convert! (hasSum_geometric_of_lt_one (r := 1 - p) (by grind) (by grind)).mul_right (p : Real)
  grind

中文:
引理 hasSum_one_geometricMeasure
  条件: (hp : p != 0)
  证明: by
  convert! (hasSum_geometric_of_lt_one (r := 1 - p) (by grind) (by grind)).mul_right (p : Real)
  grind

Depends on / 依赖: convert, hasSum_geometric_of_lt_one, mul_right
-/
lemma hasSum_one_geometricMeasure (hp : p != 0) :
    HasSum (fun n => (1 - p : Real) ^ n * p) 1 := by
  convert! (hasSum_geometric_of_lt_one (r := 1 - p) (by grind) (by grind)).mul_right (p : Real)
  grind

/--
Instance `isProbabilityMeasure_geometricMeasure` / 实例 `isProbabilityMeasure_geometricMeasure`

English:
instance isProbabilityMeasure_geometricMeasure
  signature: :
  body: by
  rw [geometricMeasure]
  split_ifs with h
  · exact (hasSum_one_geometricMeasure h).isProbabilityMeasure_sum_dirac
      (geometricMeasure_nonneg p)
  · infer_instance

中文:
实例 isProbabilityMeasure_geometricMeasure
  签名: :
  定义体: by
  rw [geometricMeasure]
  split_ifs with h
  · exact (hasSum_one_geometricMeasure h).isProbabilityMeasure_sum_dirac
      (geometricMeasure_nonneg p)
  · infer_instance

Depends on / 依赖: geometricMeasure, geometricMeasure_nonneg, hasSum_one_geometricMeasure, infer_instance, isProbabilityMeasure_sum_dirac, split_ifs
-/
instance isProbabilityMeasure_geometricMeasure :
    IsProbabilityMeasure (geometricMeasure p) := by
  rw [geometricMeasure]
  split_ifs with h
  · exact (hasSum_one_geometricMeasure h).isProbabilityMeasure_sum_dirac
      (geometricMeasure_nonneg p)
  · infer_instance

section Integral

variable {E : Type*} [NormedAddCommGroup E] {f : Nat -> E}

/--
lemma `integrable_geometricMeasure_iff` / 引理 `integrable_geometricMeasure_iff`

English:
lemma integrable_geometricMeasure_iff
  given: (hp : p != 0)
  proof: by
  rw [geometricMeasure_eq hp]; rw [integrable_sum_dirac_iff (by simp)]
  congrm Summable (fun n => ?_ * _)
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

中文:
引理 integrable_geometricMeasure_iff
  条件: (hp : p != 0)
  证明: by
  rw [geometricMeasure_eq hp]; rw [integrable_sum_dirac_iff (by simp)]
  congrm Summable (fun n => ?_ * _)
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, Summable, congrm, geometricMeasure_eq, geometricMeasure_nonneg, integrable_sum_dirac_iff, toReal_ofReal
-/
lemma integrable_geometricMeasure_iff (hp : p != 0) :
    Integrable f (geometricMeasure p) ↔ Summable (fun n => (1 - p : Real) ^ n * p * ‖f n‖) := by
  rw [geometricMeasure_eq hp]; rw [integrable_sum_dirac_iff (by simp)]
  congrm Summable (fun n => ?_ * _)
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

variable [NormedSpace Real E]

/--
lemma `hasSum_integral_geometricMeasure` / 引理 `hasSum_integral_geometricMeasure`

English:
lemma hasSum_integral_geometricMeasure
  statement: [CompleteSpace E]
  proof: by
  have : (fun n => ((1 - p : Real) ^ n * p) • f n) =
      fun n => (ENNReal.ofReal ((1 - p) ^ n * p)).toReal • f n := by
    ext n; rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]
  rw [this]; rw [geometricMeasure_eq hp]
  apply hasSum_integral_sum_dirac (by simp)
  convert! (integrable

中文:
引理 hasSum_integral_geometricMeasure
  结论: [完备空间 E]
  证明: by
  have : (fun n => ((1 - p : Real) ^ n * p) • f n) =
      fun n => (ENNReal.ofReal ((1 - p) ^ n * p)).toReal • f n := by
    ext n; rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]
  rw [this]; rw [geometricMeasure_eq hp]
  apply hasSum_integral_sum_dirac (by simp)
  convert! (integrable

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.toReal_ofReal, convert, geometricMeasure_eq, geometricMeasure_nonneg, hasSum_integral_sum_dirac, integrable_geometricMeasure_iff, ofReal, toReal, toReal_ofReal
-/
lemma hasSum_integral_geometricMeasure [CompleteSpace E]
    (hp : p != 0) (hf : Integrable f (geometricMeasure p)) :
    HasSum (fun n => ((1 - p : Real) ^ n * p) • f n) (∫ n, f n ∂geometricMeasure p) := by
  have : (fun n => ((1 - p : Real) ^ n * p) • f n) =
      fun n => (ENNReal.ofReal ((1 - p) ^ n * p)).toReal • f n := by
    ext n; rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]
  rw [this]; rw [geometricMeasure_eq hp]
  apply hasSum_integral_sum_dirac (by simp)
  convert! (integrable_geometricMeasure_iff hp).1 hf with n
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

/--
lemma `integral_geometricMeasure'` / 引理 `integral_geometricMeasure'`

English:
lemma integral_geometricMeasure'
  statement: [CompleteSpace E] (hp : p != 0)
  proof: (hasSum_integral_geometricMeasure hp hf).tsum_eq.symm

中文:
引理 integral_geometricMeasure'
  结论: [完备空间 E] (hp : p != 0)
  证明: (hasSum_integral_geometricMeasure hp hf).tsum_eq.symm

Depends on / 依赖: hasSum_integral_geometricMeasure, tsum_eq, tsum_eq.symm
-/
lemma integral_geometricMeasure' [CompleteSpace E] (hp : p != 0)
    (hf : Integrable f (geometricMeasure p)) :
    ∫ n, f n ∂geometricMeasure p = ∑' n : Nat, ((1 - p : Real) ^ n * p) • f n :=
  (hasSum_integral_geometricMeasure hp hf).tsum_eq.symm

/--
lemma `integral_geometricMeasure` / 引理 `integral_geometricMeasure`

English:
lemma integral_geometricMeasure
  given: [FiniteDimensional Real E] (hp : p != 0) (f : Nat -> E)
  proof: by
  rw [geometricMeasure_eq hp]; rw [integral_sum_dirac (by simp)]
  congr with n
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

中文:
引理 integral_geometricMeasure
  条件: [有限维 实数 E] (hp : p != 0) (f : 自然数 -> E)
  证明: by
  rw [geometricMeasure_eq hp]; rw [integral_sum_dirac (by simp)]
  congr with n
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, geometricMeasure_eq, geometricMeasure_nonneg, integral_sum_dirac, toReal_ofReal
-/
lemma integral_geometricMeasure [FiniteDimensional Real E] (hp : p != 0) (f : Nat -> E) :
    ∫ n, f n ∂geometricMeasure p = ∑' n : Nat, ((1 - p : Real) ^ n * p) • f n := by
  rw [geometricMeasure_eq hp]; rw [integral_sum_dirac (by simp)]
  congr with n
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

end Integral

section GeometricPMF

variable {p : Real}

/-- The pmf of the geometric distribution depending on its success probability. -/
@[deprecated geometricMeasure (since := "2026-03-08")]
noncomputable
/--
Definition of `geometricPMFReal` / `geometricPMFReal` 的定义

English:
definition geometricPMFReal
  signature: (p : Real) (n : Nat)
  body: (1 - p) ^ n * p

@[deprecated hasSum_one_geometricMeasure (since := "2026-03-08")]

中文:
定义 geometricPMF实数
  签名: (p : 实数) (n : 自然数)
  定义体: (1 - p) ^ n * p

@[deprecated hasSum_one_geometricMeasure (since := "2026-03-08")]
-/
def geometricPMFReal (p : Real) (n : Nat) : Real := (1 - p) ^ n * p

@[deprecated hasSum_one_geometricMeasure (since := "2026-03-08")]
/--
lemma `geometricPMFRealSum` / 引理 `geometricPMFRealSum`

English:
lemma geometricPMFRealSum
  given: (hp_pos : 0 < p) (hp_le_one : p <= 1)
  proof: by
  unfold geometricPMFReal
  have := hasSum_geometric_of_lt_one (sub_nonneg.mpr hp_le_one) (sub_lt_self 1 hp_pos)
  apply (hasSum_mul_right_iff (hp_pos.ne')).mpr at this
  simp only [sub_sub_cancel] at this
  rw [inv_mul_eq_div]; rw [div_self hp_pos.ne'] at this
  exact this

@[deprecated geometri

中文:
引理 geometricPMF实数Sum
  条件: (hp_pos : 0 < p) (hp_le_one : p <= 1)
  证明: by
  unfold geometricPMFReal
  have := hasSum_geometric_of_lt_one (sub_nonneg.mpr hp_le_one) (sub_lt_self 1 hp_pos)
  apply (hasSum_mul_right_iff (hp_pos.ne')).mpr at this
  simp only [sub_sub_cancel] at this
  rw [inv_mul_eq_div]; rw [div_self hp_pos.ne'] at this
  exact this

@[deprecated geometri

Depends on / 依赖: div_self, geometricPMFReal, hasSum_geometric_of_lt_one, hasSum_mul_right_iff, hp_le_one, hp_pos, hp_pos.ne, inv_mul_eq_div, sub_lt_self, sub_nonneg, sub_nonneg.mpr, sub_sub_cancel
-/
lemma geometricPMFRealSum (hp_pos : 0 < p) (hp_le_one : p <= 1) :
    HasSum (fun n => geometricPMFReal p n) 1 := by
  unfold geometricPMFReal
  have := hasSum_geometric_of_lt_one (sub_nonneg.mpr hp_le_one) (sub_lt_self 1 hp_pos)
  apply (hasSum_mul_right_iff (hp_pos.ne')).mpr at this
  simp only [sub_sub_cancel] at this
  rw [inv_mul_eq_div]; rw [div_self hp_pos.ne'] at this
  exact this

@[deprecated geometricMeasure_real_singleton_pos (since := "2026-03-08")]
/--
lemma `geometricPMFReal_pos` / 引理 `geometricPMFReal_pos`

English:
lemma geometricPMFReal_pos
  given: {n : Nat} (hp_pos : 0 < p) (hp_lt_one : p < 1)
  proof: by
  rw [geometricPMFReal]
  positivity [sub_pos.mpr hp_lt_one]

@[deprecated measureReal_nonneg (since := "2026-03-08")]

中文:
引理 geometricPMF实数_pos
  条件: {n : 自然数} (hp_pos : 0 < p) (hp_lt_one : p < 1)
  证明: by
  rw [geometricPMFReal]
  positivity [sub_pos.mpr hp_lt_one]

@[deprecated measureReal_nonneg (since := "2026-03-08")]

Depends on / 依赖: geometricPMFReal, hp_lt_one, sub_pos, sub_pos.mpr
-/
lemma geometricPMFReal_pos {n : Nat} (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    0 < geometricPMFReal p n := by
  rw [geometricPMFReal]
  positivity [sub_pos.mpr hp_lt_one]

@[deprecated measureReal_nonneg (since := "2026-03-08")]
/--
lemma `geometricPMFReal_nonneg` / 引理 `geometricPMFReal_nonneg`

English:
lemma geometricPMFReal_nonneg
  given: {n : Nat} (hp_pos : 0 < p) (hp_le_one : p <= 1)
  proof: by
  rw [geometricPMFReal]
  positivity [sub_nonneg.mpr hp_le_one]

中文:
引理 geometricPMF实数_nonneg
  条件: {n : 自然数} (hp_pos : 0 < p) (hp_le_one : p <= 1)
  证明: by
  rw [geometricPMFReal]
  positivity [sub_nonneg.mpr hp_le_one]

Depends on / 依赖: geometricPMFReal, hp_le_one, sub_nonneg, sub_nonneg.mpr
-/
lemma geometricPMFReal_nonneg {n : Nat} (hp_pos : 0 < p) (hp_le_one : p <= 1) :
    0 <= geometricPMFReal p n := by
  rw [geometricPMFReal]
  positivity [sub_nonneg.mpr hp_le_one]

/-- Geometric distribution with success probability `p`. -/
@[deprecated geometricMeasure (since := "2026-03-08")]
noncomputable
/--
Definition of `geometricPMF` / `geometricPMF` 的定义

English:
definition geometricPMF
  signature: (hp_pos : 0 < p) (hp_le_one : p <= 1)
  body: ⟨fun n => ENNReal.ofReal (geometricPMFReal p n), by
    apply ENNReal.hasSum_coe.mpr
    rw [← toNNReal_one]
    exact (geometricPMFRealSum hp_pos hp_le_one).toNNReal
      (fun n => geometricPMFReal_nonneg hp_pos hp_le_one)⟩

@[deprecated Measurable.of_discrete (since := "2026-03-08")]

中文:
定义 geometricPMF
  签名: (hp_pos : 0 < p) (hp_le_one : p <= 1)
  定义体: ⟨fun n => ENNReal.ofReal (geometricPMFReal p n), by
    apply ENNReal.hasSum_coe.mpr
    rw [← toNNReal_one]
    exact (geometricPMFRealSum hp_pos hp_le_one).toNNReal
      (fun n => geometricPMFReal_nonneg hp_pos hp_le_one)⟩

@[deprecated Measurable.of_discrete (since := "2026-03-08")]

Depends on / 依赖: ENNReal, ENNReal.hasSum_coe.mpr, ENNReal.ofReal, geometricPMFReal, geometricPMFRealSum, geometricPMFReal_nonneg, hasSum_coe, hp_le_one, hp_pos, ofReal, toNNReal, toNNReal_one
-/
def geometricPMF (hp_pos : 0 < p) (hp_le_one : p <= 1) : PMF Nat :=
  ⟨fun n => ENNReal.ofReal (geometricPMFReal p n), by
    apply ENNReal.hasSum_coe.mpr
    rw [← toNNReal_one]
    exact (geometricPMFRealSum hp_pos hp_le_one).toNNReal
      (fun n => geometricPMFReal_nonneg hp_pos hp_le_one)⟩

@[deprecated Measurable.of_discrete (since := "2026-03-08")]
/--
lemma `measurable_geometricPMFReal` / 引理 `measurable_geometricPMFReal`

English:
lemma measurable_geometricPMFReal
  statement: Measurable (geometricPMFReal p)
  proof: by
  fun_prop

@[deprecated StronglyMeasurable.of_discrete (since := "2026-03-08")]

中文:
引理 measurable_geometricPMF实数
  结论: 可测 (geometricPMF实数 p)
  证明: by
  fun_prop

@[deprecated StronglyMeasurable.of_discrete (since := "2026-03-08")]

Depends on / 依赖: fun_prop
-/
lemma measurable_geometricPMFReal : Measurable (geometricPMFReal p) := by
  fun_prop

@[deprecated StronglyMeasurable.of_discrete (since := "2026-03-08")]
/--
lemma `stronglyMeasurable_geometricPMFReal` / 引理 `stronglyMeasurable_geometricPMFReal`

English:
lemma stronglyMeasurable_geometricPMFReal
  statement: StronglyMeasurable (geometricPMFReal p)
  proof: stronglyMeasurable_iff_measurable.mpr measurable_geometricPMFReal

中文:
引理 stronglyMeasurable_geometricPMF实数
  结论: StronglyMeasurable (geometricPMF实数 p)
  证明: stronglyMeasurable_iff_measurable.mpr measurable_geometricPMFReal

Depends on / 依赖: measurable_geometricPMFReal, stronglyMeasurable_iff_measurable, stronglyMeasurable_iff_measurable.mpr
-/
lemma stronglyMeasurable_geometricPMFReal : StronglyMeasurable (geometricPMFReal p) :=
  stronglyMeasurable_iff_measurable.mpr measurable_geometricPMFReal

end GeometricPMF

end ProbabilityTheory
