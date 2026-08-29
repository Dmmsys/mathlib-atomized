/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson, Alastair Irving
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Set.Function

import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Comparing sums and integrals

## Summary

It is often the case that error terms in analysis can be computed by comparing
an infinite sum to the improper integral of an antitone function.

It contains several lemmas in this direction, for antitone or monotone functions
(or products of antitone and monotone functions), formulated for sums on `range i` or `Ico a b`.
These are used to prove a version of the integral test for antitone functions.

## Main Results

* `AntitoneOn.integral_le_sum`: The integral of an antitone function is at most the sum of its
  values at integer steps aligning with the left-hand side of the interval.
* `AntitoneOn.sum_le_integral`: The sum of an antitone function along integer steps aligning with
  the right-hand side of the interval is at most the integral of the function along that interval
* `MonotoneOn.integral_le_sum`: The integral of a monotone function is at most the sum of its
  values at integer steps aligning with the right-hand side of the interval.
* `MonotoneOn.sum_le_integral`: The sum of a monotone function along integer steps aligning with
  the left-hand side of the interval is at most the integral of the function along that interval
* `sum_mul_Ico_le_integral_of_monotone_antitone`: the sum of `f i * g i` on an interval is bounded
  by the integral of `f x * g (x - 1)` if `f` is monotone and `g` is antitone.
* `integral_le_sum_mul_Ico_of_antitone_monotone`: the sum of `f i * g i` on an interval is bounded
  below by the integral of `f x * g (x - 1)` if `f` is antitone and `g` is monotone.
* `AntitoneOn.summable_of_integrableOn_Ioi_zero` and `AntitoneOn.tsum_le_integral`, the
  integral test for antitone functions.
* `AntitoneOn.abs_tsum_sub_sum_range_le_integral`: an error estimate for the difference
  between a sum and its partial sums in terms of an integral.
* `AntitoneOn.integrableOn_Ioi_zero_of_summable` and `AntitoneOn.integral_le_tsum`, the converse to
  the integral test.
## Tags

analysis, comparison, asymptotics
-/

public section

open Set MeasureTheory MeasureSpace intervalIntegral

variable {x₀ : Real} {a b : Nat} {f g : Real -> Real}

/--
lemma `sum_Ico_le_integral_of_le` / 引理 `sum_Ico_le_integral_of_le`

English:
lemma sum_Ico_le_integral_of_le
  statement: (hab : a <= b)
  proof: by
  have A i (hi : i in Finset.Ico a b) : IntervalIntegrable g volume i ↑(i + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Ico_of_le (by simp)]
    simp only [Finset.mem_Ico, ← Nat.add_one_le_iff] at hi
    rify at hi
    exact hg.mono (by grind) le_rfl
  calc
  _ = ∑ i in .Ico a b, (∫ x in

中文:
引理 sum_Ico_le_integral_of_le
  结论: (hab : a <= b)
  证明: by
  have A i (hi : i in Finset.Ico a b) : IntervalIntegrable g volume i ↑(i + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Ico_of_le (by simp)]
    simp only [Finset.mem_Ico, ← Nat.add_one_le_iff] at hi
    rify at hi
    exact hg.mono (by grind) le_rfl
  calc
  _ = ∑ i in .Ico a b, (∫ x in

Depends on / 依赖: Finset, Finset.Ico, Finset.mem_Ico, IntervalIntegrable, Nat.add_one_le_iff, add_one_le_iff, hg.mono, integral_mono_on_of_le_Ioo, intervalIntegrable_iff_integrableOn_Ico_of_le, le_rfl, mem_Ico, volume
-/
lemma sum_Ico_le_integral_of_le (hab : a <= b)
    (h : forall i in Ico a b, forall x in Ico (i : Real) ↑(i + 1), f i <= g x)
    (hg : IntegrableOn g (Ico a b)) : ∑ i in .Ico a b, f i <= ∫ x in a..b, g x := by
  have A i (hi : i in Finset.Ico a b) : IntervalIntegrable g volume i ↑(i + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Ico_of_le (by simp)]
    simp only [Finset.mem_Ico, ← Nat.add_one_le_iff] at hi
    rify at hi
    exact hg.mono (by grind) le_rfl
  calc
  _ = ∑ i in .Ico a b, (∫ x in (i : Real)..↑(i + 1), f i) := by simp
  _ <= ∑ i in .Ico a b, (∫ x in (i : Real)..↑(i + 1), g x) := by
    gcongr with i hi
    apply integral_mono_on_of_le_Ioo (by simp) (by simp) (A _ hi) (fun x hx => ?_)
    exact h _ (by simpa using hi) _ (Ioo_subset_Ico_self hx)
  _ = _ := by rw [sum_integral_adjacent_intervals_Ico (a := (↑·)) hab]; grind

/--
lemma `integral_le_sum_Ico_of_le` / 引理 `integral_le_sum_Ico_of_le`

English:
lemma integral_le_sum_Ico_of_le
  statement: (hab : a <= b)
  proof: by
  convert! neg_le_neg (sum_Ico_le_integral_of_le (f := -f) (g := -g) hab
    (fun i hi x hx => neg_le_neg (h i hi x hx)) hg.neg) <;> simp

中文:
引理 integral_le_sum_Ico_of_le
  结论: (hab : a <= b)
  证明: by
  convert! neg_le_neg (sum_Ico_le_integral_of_le (f := -f) (g := -g) hab
    (fun i hi x hx => neg_le_neg (h i hi x hx)) hg.neg) <;> simp

Depends on / 依赖: convert, hg.neg, neg_le_neg, sum_Ico_le_integral_of_le
-/
lemma integral_le_sum_Ico_of_le (hab : a <= b)
    (h : forall i in Ico a b, forall x in Ico (i : Real) ↑(i + 1), g x <= f i)
    (hg : IntegrableOn g (Ico a b)) : ∫ x in a..b, g x <= ∑ i in .Ico a b, f i := by
  convert! neg_le_neg (sum_Ico_le_integral_of_le (f := -f) (g := -g) hab
    (fun i hi x hx => neg_le_neg (h i hi x hx)) hg.neg) <;> simp

/--
theorem `AntitoneOn.intervalIntegrable_subset` / 定理 `AntitoneOn.intervalIntegrable_subset`

English:
theorem AntitoneOn.intervalIntegrable_subset
  statement: (hf : AntitoneOn f (Icc x₀ (x₀ + a)))
  proof: by
  refine (hf.mono ?_).intervalIntegrable
  rw [uIcc_of_le (by simp)]
  apply Icc_subset_Icc <;> simp [-Nat.cast_add, hk]

中文:
定理 AntitoneOn.interval整数egrable_subset
  结论: (hf : AntitoneOn f (闭区间 x₀ (x₀ + a)))
  证明: by
  refine (hf.mono ?_).intervalIntegrable
  rw [uIcc_of_le (by simp)]
  apply Icc_subset_Icc <;> simp [-Nat.cast_add, hk]
-/
private theorem AntitoneOn.intervalIntegrable_subset (hf : AntitoneOn f (Icc x₀ (x₀ + a)))
    (k : Nat) (hk : k + 1 <= a) : IntervalIntegrable f volume (x₀ + k) (x₀ + ↑(k + 1)) := by
  refine (hf.mono ?_).intervalIntegrable
  rw [uIcc_of_le (by simp)]
  apply Icc_subset_Icc <;> simp [-Nat.cast_add, hk]

/--
theorem `AntitoneOn.integral_le_sum` / 定理 `AntitoneOn.integral_le_sum`

English:
theorem AntitoneOn.integral_le_sum
  given: (hf : AntitoneOn f (Icc x₀ (x₀ + a)))
  proof: calc
  _ = ∑ i in .range a, ∫ x in x₀ + i..x₀ + ↑(i + 1), f x := by
    convert! (sum_integral_adjacent_intervals hf.intervalIntegrable_subset).symm
    simp
  _ <= ∑ i in .range a, ∫ _ in x₀ + i..x₀ + ↑(i + 1), f (x₀ + i) := by
    gcongr with i hi
    rw [Finset.mem_range]; rw [← Nat.add_one_le_if

中文:
定理 AntitoneOn.integral_le_sum
  条件: (hf : AntitoneOn f (闭区间 x₀ (x₀ + a)))
  证明: calc
  _ = ∑ i in .range a, ∫ x in x₀ + i..x₀ + ↑(i + 1), f x := by
    convert! (sum_integral_adjacent_intervals hf.intervalIntegrable_subset).symm
    simp
  _ <= ∑ i in .range a, ∫ _ in x₀ + i..x₀ + ↑(i + 1), f (x₀ + i) := by
    gcongr with i hi
    rw [Finset.mem_range]; rw [← Nat.add_one_le_if
-/
theorem AntitoneOn.integral_le_sum (hf : AntitoneOn f (Icc x₀ (x₀ + a))) :
    ∫ x in x₀..x₀ + a, f x <= ∑ i in .range a, f (x₀ + i) := calc
  _ = ∑ i in .range a, ∫ x in x₀ + i..x₀ + ↑(i + 1), f x := by
    convert! (sum_integral_adjacent_intervals hf.intervalIntegrable_subset).symm
    simp
  _ <= ∑ i in .range a, ∫ _ in x₀ + i..x₀ + ↑(i + 1), f (x₀ + i) := by
    gcongr with i hi
    rw [Finset.mem_range]; rw [← Nat.add_one_le_iff] at hi
    have := hf.intervalIntegrable_subset _ hi
    rify at hi this ⊢
    refine integral_mono_on (by simp) this (by simp) fun _ _ => by apply hf <;> grind
  _ = _ := by simp

/--
theorem `AntitoneOn.integral_le_sum_Ico` / 定理 `AntitoneOn.integral_le_sum_Ico`

English:
theorem AntitoneOn.integral_le_sum_Ico
  given: (hab : a <= b) (hf : AntitoneOn f (Set.Icc a b))
  proof: by
  suffices ∫ x in a..a + ↑(b - a), f x <= ∑ x in .Ico (0 + a) (b - a + a), f x by simp_all
  rw [← Finset.sum_Ico_add]; rw [Nat.Ico_zero_eq_range]
  suffices ∫ x in a..a + ↑(b - a), f x <= ∑ x in .range (b - a), f (a + x) by simp_all
  exact AntitoneOn.integral_le_sum (by simp only [hf, hab, Nat.

中文:
定理 AntitoneOn.integral_le_sum_Ico
  条件: (hab : a <= b) (hf : AntitoneOn f (集合.闭区间 a b))
  证明: by
  suffices ∫ x in a..a + ↑(b - a), f x <= ∑ x in .Ico (0 + a) (b - a + a), f x by simp_all
  rw [← Finset.sum_Ico_add]; rw [Nat.Ico_zero_eq_range]
  suffices ∫ x in a..a + ↑(b - a), f x <= ∑ x in .range (b - a), f (a + x) by simp_all
  exact AntitoneOn.integral_le_sum (by simp only [hf, hab, Nat.

Depends on / 依赖: AntitoneOn, AntitoneOn.integral_le_sum, Finset, Finset.sum_Ico_add, Ico_zero_eq_range, Nat.Ico_zero_eq_range, Nat.cast_sub, add_sub_cancel, cast_sub, integral_le_sum, sum_Ico_add
-/
theorem AntitoneOn.integral_le_sum_Ico (hab : a <= b) (hf : AntitoneOn f (Set.Icc a b)) :
    ∫ x in a..b, f x <= ∑ x in .Ico a b, f x := by
  suffices ∫ x in a..a + ↑(b - a), f x <= ∑ x in .Ico (0 + a) (b - a + a), f x by simp_all
  rw [← Finset.sum_Ico_add]; rw [Nat.Ico_zero_eq_range]
  suffices ∫ x in a..a + ↑(b - a), f x <= ∑ x in .range (b - a), f (a + x) by simp_all
  exact AntitoneOn.integral_le_sum (by simp only [hf, hab, Nat.cast_sub, add_sub_cancel])

/--
theorem `AntitoneOn.sum_le_integral` / 定理 `AntitoneOn.sum_le_integral`

English:
theorem AntitoneOn.sum_le_integral
  given: (hf : AntitoneOn f (Icc x₀ (x₀ + a)))
  proof: calc
  _ = ∑ i in .range a, ∫ _ in x₀ + i..x₀ + ↑(i + 1), f (x₀ + ↑(i + 1)) := by simp
  _ <= ∑ i in .range a, ∫ x in x₀ + i..x₀ + ↑(i + 1), f x := by
    gcongr with i hi
    rw [Finset.mem_range]; rw [← Nat.add_one_le_iff] at hi
    have := hf.intervalIntegrable_subset _ hi
    rify at hi this ⊢
 

中文:
定理 AntitoneOn.sum_le_integral
  条件: (hf : AntitoneOn f (闭区间 x₀ (x₀ + a)))
  证明: calc
  _ = ∑ i in .range a, ∫ _ in x₀ + i..x₀ + ↑(i + 1), f (x₀ + ↑(i + 1)) := by simp
  _ <= ∑ i in .range a, ∫ x in x₀ + i..x₀ + ↑(i + 1), f x := by
    gcongr with i hi
    rw [Finset.mem_range]; rw [← Nat.add_one_le_iff] at hi
    have := hf.intervalIntegrable_subset _ hi
    rify at hi this ⊢
 
-/
theorem AntitoneOn.sum_le_integral (hf : AntitoneOn f (Icc x₀ (x₀ + a))) :
    ∑ i in .range a, f (x₀ + ↑(i + 1)) <= ∫ x in x₀..x₀ + a, f x := calc
  _ = ∑ i in .range a, ∫ _ in x₀ + i..x₀ + ↑(i + 1), f (x₀ + ↑(i + 1)) := by simp
  _ <= ∑ i in .range a, ∫ x in x₀ + i..x₀ + ↑(i + 1), f x := by
    gcongr with i hi
    rw [Finset.mem_range]; rw [← Nat.add_one_le_iff] at hi
    have := hf.intervalIntegrable_subset _ hi
    rify at hi this ⊢
    exact integral_mono_on (by simp) (by simp) this fun _ _ => by apply hf <;> grind
  _ = _ := by
    convert! sum_integral_adjacent_intervals hf.intervalIntegrable_subset
    simp [-Nat.cast_add]

/--
theorem `AntitoneOn.sum_le_integral_Ico` / 定理 `AntitoneOn.sum_le_integral_Ico`

English:
theorem AntitoneOn.sum_le_integral_Ico
  given: (hab : a <= b) (hf : AntitoneOn f (Icc a b))
  proof: by
  suffices ∑ i in .Ico (0 + a) (b - a + a), f ↑(i + 1) <= ∫ x in a..a + ↑(b - a), f x by simp_all
  simp_rw [← Finset.sum_Ico_add, Nat.Ico_zero_eq_range, add_assoc]
  suffices ∑ x in .range (b - a), f (a + ↑(x + 1)) <= ∫ x in a..a + ↑(b - a), f x by simp_all
  exact AntitoneOn.sum_le_integral (by

中文:
定理 AntitoneOn.sum_le_integral_Ico
  条件: (hab : a <= b) (hf : AntitoneOn f (闭区间 a b))
  证明: by
  suffices ∑ i in .Ico (0 + a) (b - a + a), f ↑(i + 1) <= ∫ x in a..a + ↑(b - a), f x by simp_all
  simp_rw [← Finset.sum_Ico_add, Nat.Ico_zero_eq_range, add_assoc]
  suffices ∑ x in .range (b - a), f (a + ↑(x + 1)) <= ∫ x in a..a + ↑(b - a), f x by simp_all
  exact AntitoneOn.sum_le_integral (by

Depends on / 依赖: AntitoneOn, AntitoneOn.sum_le_integral, Finset, Finset.sum_Ico_add, Ico_zero_eq_range, Nat.Ico_zero_eq_range, add_assoc, simp_rw, sum_Ico_add, sum_le_integral
-/
theorem AntitoneOn.sum_le_integral_Ico (hab : a <= b) (hf : AntitoneOn f (Icc a b)) :
    ∑ i in .Ico a b, f ↑(i + 1) <= ∫ x in a..b, f x := by
  suffices ∑ i in .Ico (0 + a) (b - a + a), f ↑(i + 1) <= ∫ x in a..a + ↑(b - a), f x by simp_all
  simp_rw [← Finset.sum_Ico_add, Nat.Ico_zero_eq_range, add_assoc]
  suffices ∑ x in .range (b - a), f (a + ↑(x + 1)) <= ∫ x in a..a + ↑(b - a), f x by simp_all
  exact AntitoneOn.sum_le_integral (by simp [hf, hab])

/--
theorem `MonotoneOn.sum_le_integral` / 定理 `MonotoneOn.sum_le_integral`

English:
theorem MonotoneOn.sum_le_integral
  given: (hf : MonotoneOn f (Icc x₀ (x₀ + a)))
  proof: by
  rw [← neg_le_neg_iff]; rw [← Finset.sum_neg_distrib]; rw [← intervalIntegral.integral_neg]
  exact hf.neg.integral_le_sum

中文:
定理 MonotoneOn.sum_le_integral
  条件: (hf : MonotoneOn f (闭区间 x₀ (x₀ + a)))
  证明: by
  rw [← neg_le_neg_iff]; rw [← Finset.sum_neg_distrib]; rw [← intervalIntegral.integral_neg]
  exact hf.neg.integral_le_sum

Depends on / 依赖: Finset, Finset.sum_neg_distrib, hf.neg.integral_le_sum, integral_le_sum, integral_neg, intervalIntegral, intervalIntegral.integral_neg, neg_le_neg_iff, sum_neg_distrib
-/
theorem MonotoneOn.sum_le_integral (hf : MonotoneOn f (Icc x₀ (x₀ + a))) :
    ∑ i in .range a, f (x₀ + i) <= ∫ x in x₀..x₀ + a, f x := by
  rw [← neg_le_neg_iff]; rw [← Finset.sum_neg_distrib]; rw [← intervalIntegral.integral_neg]
  exact hf.neg.integral_le_sum

/--
theorem `MonotoneOn.sum_le_integral_Ico` / 定理 `MonotoneOn.sum_le_integral_Ico`

English:
theorem MonotoneOn.sum_le_integral_Ico
  given: (hab : a <= b) (hf : MonotoneOn f (Set.Icc a b))
  proof: by
  rw [← neg_le_neg_iff]; rw [← Finset.sum_neg_distrib]; rw [← intervalIntegral.integral_neg]
  exact hf.neg.integral_le_sum_Ico hab

中文:
定理 MonotoneOn.sum_le_integral_Ico
  条件: (hab : a <= b) (hf : MonotoneOn f (集合.闭区间 a b))
  证明: by
  rw [← neg_le_neg_iff]; rw [← Finset.sum_neg_distrib]; rw [← intervalIntegral.integral_neg]
  exact hf.neg.integral_le_sum_Ico hab

Depends on / 依赖: Finset, Finset.sum_neg_distrib, HasTerminal, IsFiltered, hf.neg.integral_le_sum_Ico, integral_le_sum_Ico, integral_neg, intervalIntegral, intervalIntegral.integral_neg, neg_le_neg_iff, of_hasTerminal, sum_neg_distrib
-/
theorem MonotoneOn.sum_le_integral_Ico (hab : a <= b) (hf : MonotoneOn f (Set.Icc a b)) :
    ∑ x in .Ico a b, f x <= ∫ x in a..b, f x := by
  rw [← neg_le_neg_iff]; rw [← Finset.sum_neg_distrib]; rw [← intervalIntegral.integral_neg]
  exact hf.neg.integral_le_sum_Ico hab

/--
theorem `MonotoneOn.integral_le_sum` / 定理 `MonotoneOn.integral_le_sum`

English:
theorem MonotoneOn.integral_le_sum
  given: (hf : MonotoneOn f (Icc x₀ (x₀ + a)))
  proof: by
  rw [← neg_le_neg_iff]; rw [← Finset.sum_neg_distrib]; rw [← intervalIntegral.integral_neg]
  exact hf.neg.sum_le_integral

中文:
定理 MonotoneOn.integral_le_sum
  条件: (hf : MonotoneOn f (闭区间 x₀ (x₀ + a)))
  证明: by
  rw [← neg_le_neg_iff]; rw [← Finset.sum_neg_distrib]; rw [← intervalIntegral.integral_neg]
  exact hf.neg.sum_le_integral

Depends on / 依赖: Finset, Finset.sum_neg_distrib, hf.neg.sum_le_integral, integral_neg, intervalIntegral, intervalIntegral.integral_neg, neg_le_neg_iff, sum_le_integral, sum_neg_distrib
-/
theorem MonotoneOn.integral_le_sum (hf : MonotoneOn f (Icc x₀ (x₀ + a))) :
    ∫ x in x₀..x₀ + a, f x <= ∑ i in .range a, f (x₀ + ↑(i + 1)) := by
  rw [← neg_le_neg_iff]; rw [← Finset.sum_neg_distrib]; rw [← intervalIntegral.integral_neg]
  exact hf.neg.sum_le_integral

/--
theorem `MonotoneOn.integral_le_sum_Ico` / 定理 `MonotoneOn.integral_le_sum_Ico`

English:
theorem MonotoneOn.integral_le_sum_Ico
  given: (hab : a <= b) (hf : MonotoneOn f (Set.Icc a b))
  proof: by
  rw [← neg_le_neg_iff]; rw [← Finset.sum_neg_distrib]; rw [← intervalIntegral.integral_neg]
  exact hf.neg.sum_le_integral_Ico hab

中文:
定理 MonotoneOn.integral_le_sum_Ico
  条件: (hab : a <= b) (hf : MonotoneOn f (集合.闭区间 a b))
  证明: by
  rw [← neg_le_neg_iff]; rw [← Finset.sum_neg_distrib]; rw [← intervalIntegral.integral_neg]
  exact hf.neg.sum_le_integral_Ico hab

Depends on / 依赖: Finset, Finset.sum_neg_distrib, hf.neg.sum_le_integral_Ico, integral_neg, intervalIntegral, intervalIntegral.integral_neg, neg_le_neg_iff, sum_le_integral_Ico, sum_neg_distrib
-/
theorem MonotoneOn.integral_le_sum_Ico (hab : a <= b) (hf : MonotoneOn f (Set.Icc a b)) :
    ∫ x in a..b, f x <= ∑ i in .Ico a b, f ↑(i + 1) := by
  rw [← neg_le_neg_iff]; rw [← Finset.sum_neg_distrib]; rw [← intervalIntegral.integral_neg]
  exact hf.neg.sum_le_integral_Ico hab

/--
lemma `sum_mul_Ico_le_integral_of_monotone_antitone` / 引理 `sum_mul_Ico_le_integral_of_monotone_antitone`

English:
lemma sum_mul_Ico_le_integral_of_monotone_antitone
  proof: by
  apply sum_Ico_le_integral_of_le (f := fun x => f x * g x) hab
  · intro i hi x hx
    simp only [Nat.cast_add, Nat.cast_one, mem_Ico, ← Nat.add_one_le_iff] at hx hi
    rify at hi
    gcongr
    · grw [gpos]; apply hg <;> grind
    · grw [fpos]; apply hf <;> grind
    · apply hf <;> grind
    ·

中文:
引理 sum_mul_Ico_le_integral_of_monotone_antitone
  证明: by
  apply sum_Ico_le_integral_of_le (f := fun x => f x * g x) hab
  · intro i hi x hx
    simp only [Nat.cast_add, Nat.cast_one, mem_Ico, ← Nat.add_one_le_iff] at hx hi
    rify at hi
    gcongr
    · grw [gpos]; apply hg <;> grind
    · grw [fpos]; apply hf <;> grind
    · apply hf <;> grind
    ·

Depends on / 依赖: AntitoneOn, AntitoneOn.memLp_isCompact, Ico_subset_Icc_self, Integrable, Integrable.mono_measure, Nat.add_one_le_iff, Nat.cast_add, Nat.cast_one, add_one_le_iff, cast_add, cast_one, hf.integrableOn_isCompact, integrableOn_isCompact, isCompact_Icc, memLp_isCompact, mem_Ico, mono_measure, mul_of_top_left, restrict_mono_set, sum_Ico_le_integral_of_le
-/
lemma sum_mul_Ico_le_integral_of_monotone_antitone
    (hab : a <= b) (hf : MonotoneOn f (Icc a b)) (hg : AntitoneOn g (Icc (a - 1) (b - 1)))
    (fpos : 0 <= f a) (gpos : 0 <= g (b - 1)) :
    ∑ i in .Ico a b, f i * g i <= ∫ x in a..b, f x * g (x - 1) := by
  apply sum_Ico_le_integral_of_le (f := fun x => f x * g x) hab
  · intro i hi x hx
    simp only [Nat.cast_add, Nat.cast_one, mem_Ico, ← Nat.add_one_le_iff] at hx hi
    rify at hi
    gcongr
    · grw [gpos]; apply hg <;> grind
    · grw [fpos]; apply hf <;> grind
    · apply hf <;> grind
    · apply hg <;> grind
  · apply Integrable.mono_measure _ (volume.restrict_mono_set Ico_subset_Icc_self)
    apply (hf.integrableOn_isCompact isCompact_Icc).mul_of_top_left
    apply AntitoneOn.memLp_isCompact isCompact_Icc
    intro _ _ _ _ _
    apply hg <;> grind

/--
lemma `integral_le_sum_mul_Ico_of_antitone_monotone` / 引理 `integral_le_sum_mul_Ico_of_antitone_monotone`

English:
lemma integral_le_sum_mul_Ico_of_antitone_monotone
  proof: by
  apply integral_le_sum_Ico_of_le (f := fun x => f x * g x) hab
  · intro i hi x hx
    simp only [Nat.cast_add, Nat.cast_one, mem_Ico, ← Nat.add_one_le_iff] at hx hi
    rify at hi
    gcongr
    · grw [gpos]; apply hg <;> grind
    · grw [fpos]; apply hf <;> grind
    · apply hf <;> grind
    ·

中文:
引理 integral_le_sum_mul_Ico_of_antitone_monotone
  证明: by
  apply integral_le_sum_Ico_of_le (f := fun x => f x * g x) hab
  · intro i hi x hx
    simp only [Nat.cast_add, Nat.cast_one, mem_Ico, ← Nat.add_one_le_iff] at hx hi
    rify at hi
    gcongr
    · grw [gpos]; apply hg <;> grind
    · grw [fpos]; apply hf <;> grind
    · apply hf <;> grind
    ·

Depends on / 依赖: Ico_subset_Icc_self, Integrable, Integrable.mono_measure, MonotoneOn, MonotoneOn.memLp_isCompact, Nat.add_one_le_iff, Nat.cast_add, Nat.cast_one, add_one_le_iff, cast_add, cast_one, hf.integrableOn_isCompact, integrableOn_isCompact, integral_le_sum_Ico_of_le, isCompact_Icc, memLp_isCompact, mem_Ico, mono_measure, mul_of_top_left, restrict_mono_set
-/
lemma integral_le_sum_mul_Ico_of_antitone_monotone
    (hab : a <= b) (hf : AntitoneOn f (Icc a b)) (hg : MonotoneOn g (Icc (a - 1) (b - 1)))
    (fpos : 0 <= f b) (gpos : 0 <= g (a - 1)) :
    ∫ x in a..b, f x * g (x - 1) <= ∑ i in .Ico a b, f i * g i := by
  apply integral_le_sum_Ico_of_le (f := fun x => f x * g x) hab
  · intro i hi x hx
    simp only [Nat.cast_add, Nat.cast_one, mem_Ico, ← Nat.add_one_le_iff] at hx hi
    rify at hi
    gcongr
    · grw [gpos]; apply hg <;> grind
    · grw [fpos]; apply hf <;> grind
    · apply hf <;> grind
    · apply hg <;> grind
  · apply Integrable.mono_measure _ (volume.restrict_mono_set Ico_subset_Icc_self)
    apply (hf.integrableOn_isCompact isCompact_Icc).mul_of_top_left
    apply MonotoneOn.memLp_isCompact isCompact_Icc
    intro _ _ _ _ _
    apply hg <;> grind

/-! ## Comparison of infinite sums and integrals -/

/--
lemma `AntitoneOn.sum_Ico_le_integral` / 引理 `AntitoneOn.sum_Ico_le_integral`

English:
lemma AntitoneOn.sum_Ico_le_integral
  statement: {a b : Nat} (anti : AntitoneOn f (Icc a b))
  proof: by
  by_cases! hab : b < a
  · simpa [Finset.Ico_eq_empty_of_le hab.le] using setIntegral_nonneg measurableSet_Ioi nonneg
  grw [anti.sum_le_integral_Ico hab, integral_of_le (mod_cast hab)]
  apply setIntegral_mono_set integrable _ (Ioc_subset_Ioi_self.eventuallyLE)
  exact ae_restrict_of_forall_mem

中文:
引理 AntitoneOn.sum_Ico_le_integral
  结论: {a b : 自然数} (anti : AntitoneOn f (闭区间 a b))
  证明: by
  by_cases! hab : b < a
  · simpa [Finset.Ico_eq_empty_of_le hab.le] using setIntegral_nonneg measurableSet_Ioi nonneg
  grw [anti.sum_le_integral_Ico hab, integral_of_le (mod_cast hab)]
  apply setIntegral_mono_set integrable _ (Ioc_subset_Ioi_self.eventuallyLE)
  exact ae_restrict_of_forall_mem

Depends on / 依赖: Finset, Finset.Ico_eq_empty_of_le, Ico_eq_empty_of_le, Ioc_subset_Ioi_self, Ioc_subset_Ioi_self.eventuallyLE, ae_restrict_of_forall_mem, anti.sum_le_integral_Ico, eventuallyLE, hab.le, integrable, integral_of_le, measurableSet_Ioi, mod_cast, nonneg, setIntegral_mono_set, setIntegral_nonneg, sum_le_integral_Ico
-/
lemma AntitoneOn.sum_Ico_le_integral {a b : Nat} (anti : AntitoneOn f (Icc a b))
    (integrable : IntegrableOn f (Ioi a)) (nonneg : forall t in Ioi (a : Real), 0 <= f t) :
    ∑ n in .Ico a b, f ↑(n + 1) <= ∫ x in Ioi (a : Real), f x := by
  by_cases! hab : b < a
  · simpa [Finset.Ico_eq_empty_of_le hab.le] using setIntegral_nonneg measurableSet_Ioi nonneg
  grw [anti.sum_le_integral_Ico hab, integral_of_le (mod_cast hab)]
  apply setIntegral_mono_set integrable _ (Ioc_subset_Ioi_self.eventuallyLE)
  exact ae_restrict_of_forall_mem measurableSet_Ioi nonneg

/--
lemma `AntitoneOn.sum_range_le_integral` / 引理 `AntitoneOn.sum_range_le_integral`

English:
lemma AntitoneOn.sum_range_le_integral
  statement: {N : Nat} (anti : AntitoneOn f (Icc 0 (N : Real)))
  proof: by
  rw [Finset.range_eq_Ico]
  exact_mod_cast AntitoneOn.sum_Ico_le_integral (a := 0) (mod_cast anti)
    (mod_cast integrable) (mod_cast nonneg)

中文:
引理 AntitoneOn.sum_range_le_integral
  结论: {N : 自然数} (anti : AntitoneOn f (闭区间 0 (N : 实数)))
  证明: by
  rw [Finset.range_eq_Ico]
  exact_mod_cast AntitoneOn.sum_Ico_le_integral (a := 0) (mod_cast anti)
    (mod_cast integrable) (mod_cast nonneg)

Depends on / 依赖: AntitoneOn, AntitoneOn.sum_Ico_le_integral, Finset, Finset.range_eq_Ico, integrable, mod_cast, nonneg, range_eq_Ico, sum_Ico_le_integral
-/
lemma AntitoneOn.sum_range_le_integral {N : Nat} (anti : AntitoneOn f (Icc 0 (N : Real)))
    (integrable : IntegrableOn f (Ioi 0)) (nonneg : forall t in Ioi 0, 0 <= f t) :
    ∑ n in Finset.range N, f ((n + 1 : Nat)) <= ∫ x in Ioi 0, f x := by
  rw [Finset.range_eq_Ico]
  exact_mod_cast AntitoneOn.sum_Ico_le_integral (a := 0) (mod_cast anti)
    (mod_cast integrable) (mod_cast nonneg)

/--
theorem `AntitoneOn.summable_of_integrableOn_Ioi` / 定理 `AntitoneOn.summable_of_integrableOn_Ioi`

English:
theorem AntitoneOn.summable_of_integrableOn_Ioi
  statement: {N : Nat} (anti : AntitoneOn f (Ici (N : Real)))
  proof: by
  rw [← summable_nat_add_iff (N + 1)]
  refine summable_of_sum_range_le (c := ∫ t in Ioi (N : Real), f t) (by grind) fun M => ?_
  calc
    _ = ∑ n in Finset.Ico N (N + M), f (n + 1 : Nat) := by rw [Finset.sum_Ico_eq_sum_range]; grind
    _ <= _ := (anti.mono Icc_subset_Ici_self).sum_Ico_le_integ

中文:
定理 AntitoneOn.summable_of_integrableOn_Ioi
  结论: {N : 自然数} (anti : AntitoneOn f (左闭右无界区间 (N : 实数)))
  证明: by
  rw [← summable_nat_add_iff (N + 1)]
  refine summable_of_sum_range_le (c := ∫ t in Ioi (N : Real), f t) (by grind) fun M => ?_
  calc
    _ = ∑ n in Finset.Ico N (N + M), f (n + 1 : Nat) := by rw [Finset.sum_Ico_eq_sum_range]; grind
    _ <= _ := (anti.mono Icc_subset_Ici_self).sum_Ico_le_integ

Depends on / 依赖: Finset, Finset.Ico, Finset.sum_Ico_eq_sum_range, Icc_subset_Ici_self, anti.mono, integrable, nonneg, sum_Ico_eq_sum_range, sum_Ico_le_integral, summable_nat_add_iff, summable_of_sum_range_le
-/
theorem AntitoneOn.summable_of_integrableOn_Ioi {N : Nat} (anti : AntitoneOn f (Ici (N : Real)))
    (integrable : IntegrableOn f (Ioi (N : Real))) (nonneg : forall t in Ioi (N : Real), 0 <= f t) :
    Summable (fun (n : Nat) => f n) := by
  rw [← summable_nat_add_iff (N + 1)]
  refine summable_of_sum_range_le (c := ∫ t in Ioi (N : Real), f t) (by grind) fun M => ?_
  calc
    _ = ∑ n in Finset.Ico N (N + M), f (n + 1 : Nat) := by rw [Finset.sum_Ico_eq_sum_range]; grind
    _ <= _ := (anti.mono Icc_subset_Ici_self).sum_Ico_le_integral integrable nonneg

/--
theorem `AntitoneOn.summable_of_integrableOn_Ioi_zero` / 定理 `AntitoneOn.summable_of_integrableOn_Ioi_zero`

English:
theorem AntitoneOn.summable_of_integrableOn_Ioi_zero
  statement: (anti : AntitoneOn f (Ici 0))
  proof: summable_of_integrableOn_Ioi (N := 0) (mod_cast anti) (mod_cast integrable) (mod_cast nonneg)

中文:
定理 AntitoneOn.summable_of_integrableOn_Ioi_zero
  结论: (anti : AntitoneOn f (左闭右无界区间 0))
  证明: summable_of_integrableOn_Ioi (N := 0) (mod_cast anti) (mod_cast integrable) (mod_cast nonneg)

Depends on / 依赖: integrable, mod_cast, nonneg, summable_of_integrableOn_Ioi
-/
theorem AntitoneOn.summable_of_integrableOn_Ioi_zero (anti : AntitoneOn f (Ici 0))
    (integrable : IntegrableOn f (Ioi 0)) (nonneg : forall t in Ioi 0, 0 <= f t) :
    Summable (fun (n : Nat) => f n) :=
  summable_of_integrableOn_Ioi (N := 0) (mod_cast anti) (mod_cast integrable) (mod_cast nonneg)

open Filter Finset in
/--
theorem `AntitoneOn.tsum_comp_add_le_integral` / 定理 `AntitoneOn.tsum_comp_add_le_integral`

English:
theorem AntitoneOn.tsum_comp_add_le_integral
  statement: (N : Nat) (anti : AntitoneOn f (Ici (N : Real)))
  proof: by
  refine tsum_le_of_sum_le' (integral_nonneg_of_ae ?_) fun s => ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] using nonneg
.exists · obtain ⟨t, ht⟩ := tendsto_finset_range.eventually (Ici_mem_atTop s)
    calc
      ∑ i in s, f ↑(i + N + 1) <= ∑ i in range t, f ↑(i + N + 1) :=
sum_le_

中文:
定理 AntitoneOn.tsum_comp_add_le_integral
  结论: (N : 自然数) (anti : AntitoneOn f (左闭右无界区间 (N : 实数)))
  证明: by
  refine tsum_le_of_sum_le' (integral_nonneg_of_ae ?_) fun s => ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] using nonneg
.exists · obtain ⟨t, ht⟩ := tendsto_finset_range.eventually (Ici_mem_atTop s)
    calc
      ∑ i in s, f ↑(i + N + 1) <= ∑ i in range t, f ↑(i + N + 1) :=
sum_le_

Depends on / 依赖: Finset, Finset.sum_Ico_eq_sum_range, Ici_mem_atTop, Set.Ioi, ae_restrict_mem, anti.mono, eventually, filter_upwards, integral_nonneg_of_ae, measurableSet_Ioi, nonneg, sum_Ico_eq_sum_range, sum_Ico_le_integral, sum_le_sum_of_subset_of_nonneg, tendsto_finset_range, tendsto_finset_range.eventually, tsum_le_of_sum_le
-/
theorem AntitoneOn.tsum_comp_add_le_integral (N : Nat) (anti : AntitoneOn f (Ici (N : Real)))
    (integrable : IntegrableOn f (Ioi (N : Real))) (nonneg : forall t in Ioi (N : Real), 0 <= f t) :
    ∑' (n : Nat), f (n + N + 1 : Nat) <= ∫ x in Ioi (N : Real), f x := by
  refine tsum_le_of_sum_le' (integral_nonneg_of_ae ?_) fun s => ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] using nonneg
.exists · obtain ⟨t, ht⟩ := tendsto_finset_range.eventually (Ici_mem_atTop s)
    calc
      ∑ i in s, f ↑(i + N + 1) <= ∑ i in range t, f ↑(i + N + 1) :=
sum_le_sum_of_subset_of_nonneg ht by grind
      _ = ∑ i in Ico N (N + t), f ↑(i + 1) := by rw [Finset.sum_Ico_eq_sum_range]; grind
      _ <= ∫ (x : Real) in Set.Ioi (N : Real), f x :=
        (anti.mono <| by grind).sum_Ico_le_integral integrable nonneg

/--
theorem `AntitoneOn.tsum_add_one_le_integral` / 定理 `AntitoneOn.tsum_add_one_le_integral`

English:
theorem AntitoneOn.tsum_add_one_le_integral
  statement: (anti : AntitoneOn f (Ici 0))
  proof: by
  exact_mod_cast AntitoneOn.tsum_comp_add_le_integral 0 (mod_cast anti) (mod_cast integrable)
    (mod_cast nonneg)

中文:
定理 AntitoneOn.tsum_add_one_le_integral
  结论: (anti : AntitoneOn f (左闭右无界区间 0))
  证明: by
  exact_mod_cast AntitoneOn.tsum_comp_add_le_integral 0 (mod_cast anti) (mod_cast integrable)
    (mod_cast nonneg)

Depends on / 依赖: AntitoneOn, AntitoneOn.tsum_comp_add_le_integral, integrable, mod_cast, nonneg, tsum_comp_add_le_integral
-/
theorem AntitoneOn.tsum_add_one_le_integral (anti : AntitoneOn f (Ici 0))
    (integrable : IntegrableOn f (Ioi 0)) (nonneg : forall t in Ioi 0, 0 <= f t) :
    ∑' (n : Nat), f (n + 1 : Nat) <= ∫ x in Ioi 0, f x := by
  exact_mod_cast AntitoneOn.tsum_comp_add_le_integral 0 (mod_cast anti) (mod_cast integrable)
    (mod_cast nonneg)

/--
theorem `AntitoneOn.tsum_le_integral` / 定理 `AntitoneOn.tsum_le_integral`

English:
theorem AntitoneOn.tsum_le_integral
  statement: (anti : AntitoneOn f (Ici 0))
  proof: by
  grind [(anti.summable_of_integrableOn_Ioi_zero integrable nonneg).tsum_eq_zero_add,
    anti.tsum_add_one_le_integral integrable nonneg]

中文:
定理 AntitoneOn.tsum_le_integral
  结论: (anti : AntitoneOn f (左闭右无界区间 0))
  证明: by
  grind [(anti.summable_of_integrableOn_Ioi_zero integrable nonneg).tsum_eq_zero_add,
    anti.tsum_add_one_le_integral integrable nonneg]

Depends on / 依赖: anti.summable_of_integrableOn_Ioi_zero, anti.tsum_add_one_le_integral, integrable, nonneg, summable_of_integrableOn_Ioi_zero, tsum_add_one_le_integral, tsum_eq_zero_add
-/
theorem AntitoneOn.tsum_le_integral (anti : AntitoneOn f (Ici 0))
    (integrable : IntegrableOn f (Ioi 0)) (nonneg : forall t in Ioi 0, 0 <= f t) :
    ∑' (n : Nat), f n <= f 0 + ∫ x in Ioi 0, f x := by
  grind [(anti.summable_of_integrableOn_Ioi_zero integrable nonneg).tsum_eq_zero_add,
    anti.tsum_add_one_le_integral integrable nonneg]

/--
theorem `AntitoneOn.abs_tsum_sub_sum_range_le_integral` / 定理 `AntitoneOn.abs_tsum_sub_sum_range_le_integral`

English:
theorem AntitoneOn.abs_tsum_sub_sum_range_le_integral
  statement: {N : Nat} (hN : 1 <= N)
  proof: by
  rw [← (AntitoneOn.summable_of_integrableOn_Ioi (mod_cast anti) (mod_cast integrable)
    (mod_cast nonneg)).sum_add_tsum_nat_add N]; rw [add_sub_cancel_left]; rw [abs_of_nonneg (tsum_nonneg <| by grind)]
  convert! AntitoneOn.tsum_comp_add_le_integral (N - 1) (mod_cast anti) (mod_cast integrabl

中文:
定理 AntitoneOn.abs_tsum_sub_sum_range_le_integral
  结论: {N : 自然数} (hN : 1 <= N)
  证明: by
  rw [← (AntitoneOn.summable_of_integrableOn_Ioi (mod_cast anti) (mod_cast integrable)
    (mod_cast nonneg)).sum_add_tsum_nat_add N]; rw [add_sub_cancel_left]; rw [abs_of_nonneg (tsum_nonneg <| by grind)]
  convert! AntitoneOn.tsum_comp_add_le_integral (N - 1) (mod_cast anti) (mod_cast integrabl

Depends on / 依赖: AntitoneOn, AntitoneOn.summable_of_integrableOn_Ioi, AntitoneOn.tsum_comp_add_le_integral, abs_of_nonneg, add_sub_cancel_left, convert, integrable, mod_cast, nonneg, sum_add_tsum_nat_add, summable_of_integrableOn_Ioi, tsum_comp_add_le_integral, tsum_nonneg
-/
theorem AntitoneOn.abs_tsum_sub_sum_range_le_integral {N : Nat} (hN : 1 <= N)
    (anti : AntitoneOn f (Ici (N - 1 : Real)))
    (integrable : IntegrableOn f (Ioi (N - 1 : Real))) (nonneg : forall t in Ioi (N - 1 : Real), 0 <= f t) :
    |(∑' (n : Nat), f n) - ∑ n in Finset.range N, f n| <= ∫ x in Ioi (N - 1 : Real), f x := by
  rw [← (AntitoneOn.summable_of_integrableOn_Ioi (mod_cast anti) (mod_cast integrable)
    (mod_cast nonneg)).sum_add_tsum_nat_add N]; rw [add_sub_cancel_left]; rw [abs_of_nonneg (tsum_nonneg <| by grind)]
  convert! AntitoneOn.tsum_comp_add_le_integral (N - 1) (mod_cast anti) (mod_cast integrable)
      (mod_cast nonneg) using 1
  · congr; ext; congr 2; grind
  · norm_cast

open Filter in
/--
theorem `AntitoneOn.integrableOn_Ioi_of_summable_comp_add` / 定理 `AntitoneOn.integrableOn_Ioi_of_summable_comp_add`

English:
theorem AntitoneOn.integrableOn_Ioi_of_summable_comp_add
  statement: {N : Nat} (anti : AntitoneOn f (Ici (N : Real)))
  proof: by
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (∑' (n : Nat), f (n + N : Nat)) _ ?_
    (tendsto_atTop_add_const_right atTop (N : Real) tendsto_natCast_atTop_atTop) ?_
  · intro n
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by grind)]
    exact (anti.mono <| by grind [uIc

中文:
定理 AntitoneOn.integrableOn_Ioi_of_summable_comp_add
  结论: {N : 自然数} (anti : AntitoneOn f (左闭右无界区间 (N : 实数)))
  证明: by
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (∑' (n : Nat), f (n + N : Nat)) _ ?_
    (tendsto_atTop_add_const_right atTop (N : Real) tendsto_natCast_atTop_atTop) ?_
  · intro n
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by grind)]
    exact (anti.mono <| by grind [uIc

Depends on / 依赖: Real.norm_of_nonneg, anti.mono, eventually_gt_atTop, filter_upwards, integrableOn_Ioi_of_intervalIntegral_norm_bounded, integral_congr_uIoo, intervalIntegrable, intervalIntegrable_iff_integrableOn_Ioc_of_le, intervalIntegral, intervalIntegral.integral_congr_uIoo, norm_of_nonneg, tendsto_atTop_add_const_right, tendsto_natCast_atTop_atTop, uIcc_of_le, uIoo_of_le
-/
theorem AntitoneOn.integrableOn_Ioi_of_summable_comp_add {N : Nat} (anti : AntitoneOn f (Ici (N : Real)))
    (summable : Summable (fun n => f (n + N : Nat))) (nonneg : forall t in Ioi (N : Real), 0 <= f t) :
    IntegrableOn f (Ioi (N : Real)) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (∑' (n : Nat), f (n + N : Nat)) _ ?_
    (tendsto_atTop_add_const_right atTop (N : Real) tendsto_natCast_atTop_atTop) ?_
  · intro n
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by grind)]
    exact (anti.mono <| by grind [uIcc_of_le]).intervalIntegrable
  · filter_upwards [eventually_gt_atTop 0] with M hM
    calc
      _ = ∫ x in N..M+N, f x := by
        refine intervalIntegral.integral_congr_uIoo fun x => ?_
        grind [Real.norm_of_nonneg, uIoo_of_le]
      _ <= ∑ n in Finset.range M, f (n + N : Nat) := by
        convert! AntitoneOn.integral_le_sum (anti.mono _) using 2 <;> grind
      _ <= _ := by grind [summable.sum_le_tsum, Nat.cast_pos]

/--
theorem `AntitoneOn.integrableOn_Ioi_zero_of_summable` / 定理 `AntitoneOn.integrableOn_Ioi_zero_of_summable`

English:
theorem AntitoneOn.integrableOn_Ioi_zero_of_summable
  statement: (anti : AntitoneOn f (Ici 0))
  proof: mod_cast AntitoneOn.integrableOn_Ioi_of_summable_comp_add (N := 0) (mod_cast anti) summable
    (mod_cast nonneg)

中文:
定理 AntitoneOn.integrableOn_Ioi_zero_of_summable
  结论: (anti : AntitoneOn f (左闭右无界区间 0))
  证明: mod_cast AntitoneOn.integrableOn_Ioi_of_summable_comp_add (N := 0) (mod_cast anti) summable
    (mod_cast nonneg)

Depends on / 依赖: AntitoneOn, AntitoneOn.integrableOn_Ioi_of_summable_comp_add, integrableOn_Ioi_of_summable_comp_add, mod_cast, nonneg, summable
-/
theorem AntitoneOn.integrableOn_Ioi_zero_of_summable (anti : AntitoneOn f (Ici 0))
    (summable : Summable (fun (n : Nat) => f n)) (nonneg : forall t in Ioi 0, 0 <= f t) :
    IntegrableOn f (Ioi 0) :=
  mod_cast AntitoneOn.integrableOn_Ioi_of_summable_comp_add (N := 0) (mod_cast anti) summable
    (mod_cast nonneg)

open Filter in
/--
theorem `AntitoneOn.integral_le_tsum_comp_add` / 定理 `AntitoneOn.integral_le_tsum_comp_add`

English:
theorem AntitoneOn.integral_le_tsum_comp_add
  statement: (N : Nat) (anti : AntitoneOn f (Ici (N : Real)))
  proof: by
  rw [← summable_nat_add_iff N] at summable
  have lim := summable.tendsto_sum_tsum_nat
  have := tendsto_atTop_add_const_right atTop (N : Real) tendsto_natCast_atTop_atTop
  have integrable := anti.integrableOn_Ioi_of_summable_comp_add summable nonneg
  refine le_of_tendsto_of_tendsto (intervalI

中文:
定理 AntitoneOn.integral_le_tsum_comp_add
  结论: (N : 自然数) (anti : AntitoneOn f (左闭右无界区间 (N : 实数)))
  证明: by
  rw [← summable_nat_add_iff N] at summable
  have lim := summable.tendsto_sum_tsum_nat
  have := tendsto_atTop_add_const_right atTop (N : Real) tendsto_natCast_atTop_atTop
  have integrable := anti.integrableOn_Ioi_of_summable_comp_add summable nonneg
  refine le_of_tendsto_of_tendsto (intervalI

Depends on / 依赖: AntitoneOn, AntitoneOn.integral_le_sum_Ico, Finset, Finset.Ico, anti.integrableOn_Ioi_of_summable_comp_add, anti.mono, convert, filter_upwards, integrable, integrableOn_Ioi_of_summable_comp_add, integral_le_sum_Ico, intervalIntegral_tendsto_integral_Ioi, le_of_tendsto_of_tendsto, nonneg, summable, summable.tendsto_sum_tsum_nat, summable_nat_add_iff, tendsto_atTop_add_const_right, tendsto_natCast_atTop_atTop, tendsto_sum_tsum_nat
-/
theorem AntitoneOn.integral_le_tsum_comp_add (N : Nat) (anti : AntitoneOn f (Ici (N : Real)))
    (summable : Summable (fun (n : Nat) => f n)) (nonneg : forall t in Ioi (N : Real), 0 <= f t) :
    ∫ x in Ioi (N : Real), f x <= ∑' (n : Nat), f (n + N : Nat) := by
  rw [← summable_nat_add_iff N] at summable
  have lim := summable.tendsto_sum_tsum_nat
  have := tendsto_atTop_add_const_right atTop (N : Real) tendsto_natCast_atTop_atTop
  have integrable := anti.integrableOn_Ioi_of_summable_comp_add summable nonneg
  refine le_of_tendsto_of_tendsto (intervalIntegral_tendsto_integral_Ioi N integrable this) lim ?_
  filter_upwards with M
  calc
    _ <= ∑ n in Finset.Ico N (N + M), f n := by
      convert! AntitoneOn.integral_le_sum_Ico _ _ using 2 <;> grind [anti.mono]
    _ = _ := by
      rw [Finset.sum_Ico_eq_sum_range]
      grind

/--
theorem `AntitoneOn.integral_le_tsum` / 定理 `AntitoneOn.integral_le_tsum`

English:
theorem AntitoneOn.integral_le_tsum
  statement: (anti : AntitoneOn f (Ici 0))
  proof: mod_cast AntitoneOn.integral_le_tsum_comp_add 0 (mod_cast anti) summable (mod_cast nonneg)

中文:
定理 AntitoneOn.integral_le_tsum
  结论: (anti : AntitoneOn f (左闭右无界区间 0))
  证明: mod_cast AntitoneOn.integral_le_tsum_comp_add 0 (mod_cast anti) summable (mod_cast nonneg)

Depends on / 依赖: AntitoneOn, AntitoneOn.integral_le_tsum_comp_add, integral_le_tsum_comp_add, mod_cast, nonneg, summable
-/
theorem AntitoneOn.integral_le_tsum (anti : AntitoneOn f (Ici 0))
    (summable : Summable (fun (n : Nat) => f n)) (nonneg : forall t in Ioi 0, 0 <= f t) :
    ∫ x in Ioi 0, f x <= ∑' (n : Nat), f n :=
  mod_cast AntitoneOn.integral_le_tsum_comp_add 0 (mod_cast anti) summable (mod_cast nonneg)
