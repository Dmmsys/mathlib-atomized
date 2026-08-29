/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SumOverResidueClass

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Convergence of `p`-series

In this file we prove that the series `∑' k in ℕ, 1 / k ^ p` converges if and only if `p > 1`.
The proof is based on the
[Cauchy condensation test](https://en.wikipedia.org/wiki/Cauchy_condensation_test): `∑ k, f k`
converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. We prove this test in
`NNReal.summable_condensed_iff` and `summable_condensed_iff_of_nonneg`, then use it to prove
`summable_one_div_rpow`. After this transformation, a `p`-series turns into a geometric series.

## Tags

p-series, Cauchy condensation test
-/

@[expose] public section

/-!
### Schlömilch's generalization of the Cauchy condensation test

In this section we prove the Schlömilch's generalization of the Cauchy condensation test:
for a strictly increasing `u : ℕ → ℕ` with ratio of successive differences bounded and an
antitone `f : ℕ → ℝ≥0` or `f : ℕ → ℝ`, `∑ k, f k` converges if and only if
so does `∑ k, (u (k + 1) - u k) * f (u k)`. Instead of giving a monolithic proof, we split it
into a series of lemmas with explicit estimates of partial sums of each series in terms of the
partial sums of the other series.
-/

/--
Definition of `SuccDiffBounded` / `SuccDiffBounded` 的定义

English:
definition SuccDiffBounded
  signature: (C : Nat) (u : Nat -> Nat)
  body: forall n : Nat, u (n + 2) - u (n + 1) <= C • (u (n + 1) - u n)

中文:
定义 SuccDiffBounded
  签名: (C : 自然数) (u : 自然数 -> 自然数)
  定义体: forall n : Nat, u (n + 2) - u (n + 1) <= C • (u (n + 1) - u n)
-/
def SuccDiffBounded (C : Nat) (u : Nat -> Nat) : Prop :=
  forall n : Nat, u (n + 2) - u (n + 1) <= C • (u (n + 1) - u n)

namespace Finset

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  {f : Nat -> M} {u : Nat -> Nat}

/--
theorem `le_sum_schlomilch'` / 定理 `le_sum_schlomilch'`

English:
theorem le_sum_schlomilch'
  statement: (hf : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) (h_pos : forall n, 0 < u n)
  proof: by
  induction n with
  | zero => simp
  | succ n ihn =>
    suffices (∑ k in Ico (u n) (u (n + 1)), f k) <= (u (n + 1) - u n) • f (u n) by
      rw [sum_range_succ]; rw [← sum_Ico_consecutive]
      · exact add_le_add ihn this
      exacts [hu n.zero_le, hu n.le_succ]
    have : forall k in Ico (u 

中文:
定理 le_sum_schlomilch'
  结论: (hf : 对任意 ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) (h_pos : 对任意 n, 0 < u n)
  证明: by
  induction n with
  | zero => simp
  | succ n ihn =>
    suffices (∑ k in Ico (u n) (u (n + 1)), f k) <= (u (n + 1) - u n) • f (u n) by
      rw [sum_range_succ]; rw [← sum_Ico_consecutive]
      · exact add_le_add ihn this
      exacts [hu n.zero_le, hu n.le_succ]
    have : forall k in Ico (u 

Depends on / 依赖: Nat.succ_le_of_lt, add_le_add, convert, exacts, h_pos, le_succ, mem_Ico, mem_Ico.mp, n.le_succ, n.zero_le, succ_le_of_lt, sum_Ico_consecutive, sum_le_sum, sum_range_succ, zero_le
-/
theorem le_sum_schlomilch' (hf : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) (h_pos : forall n, 0 < u n)
    (hu : Monotone u) (n : Nat) :
    (∑ k in Ico (u 0) (u n), f k) <= ∑ k in range n, (u (k + 1) - u k) • f (u k) := by
  induction n with
  | zero => simp
  | succ n ihn =>
    suffices (∑ k in Ico (u n) (u (n + 1)), f k) <= (u (n + 1) - u n) • f (u n) by
      rw [sum_range_succ]; rw [← sum_Ico_consecutive]
      · exact add_le_add ihn this
      exacts [hu n.zero_le, hu n.le_succ]
    have : forall k in Ico (u n) (u (n + 1)), f k <= f (u n) := fun k hk =>
      hf (Nat.succ_le_of_lt (h_pos n)) (mem_Ico.mp hk).1
    convert! sum_le_sum this
    simp

/--
theorem `le_sum_condensed'` / 定理 `le_sum_condensed'`

English:
theorem le_sum_condensed'
  given: (hf : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) (n : Nat)
  proof: by
  convert!
    le_sum_schlomilch' hf (fun n => pow_pos zero_lt_two n)
      (fun m n hm => pow_right_mono₀ one_le_two hm) n using 2
  simp [pow_succ, mul_two]

中文:
定理 le_sum_condensed'
  条件: (hf : 对任意 ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) (n : 自然数)
  证明: by
  convert!
    le_sum_schlomilch' hf (fun n => pow_pos zero_lt_two n)
      (fun m n hm => pow_right_mono₀ one_le_two hm) n using 2
  simp [pow_succ, mul_two]

Depends on / 依赖: convert, le_sum_schlomilch, mul_two, one_le_two, pow_pos, pow_succ, zero_lt_two
-/
theorem le_sum_condensed' (hf : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) (n : Nat) :
    (∑ k in Ico 1 (2 ^ n), f k) <= ∑ k in range n, 2 ^ k • f (2 ^ k) := by
  convert!
    le_sum_schlomilch' hf (fun n => pow_pos zero_lt_two n)
      (fun m n hm => pow_right_mono₀ one_le_two hm) n using 2
  simp [pow_succ, mul_two]

/--
theorem `le_sum_schlomilch` / 定理 `le_sum_schlomilch`

English:
theorem le_sum_schlomilch
  statement: (hf : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) (h_pos : forall n, 0 < u n)
  proof: by
  grw [← le_sum_schlomilch' hf h_pos hu n, ← sum_range_add_sum_Ico _ (hu n.zero_le)]

中文:
定理 le_sum_schlomilch
  结论: (hf : 对任意 ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) (h_pos : 对任意 n, 0 < u n)
  证明: by
  grw [← le_sum_schlomilch' hf h_pos hu n, ← sum_range_add_sum_Ico _ (hu n.zero_le)]

Depends on / 依赖: h_pos, le_sum_schlomilch, n.zero_le, sum_range_add_sum_Ico, zero_le
-/
theorem le_sum_schlomilch (hf : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) (h_pos : forall n, 0 < u n)
    (hu : Monotone u) (n : Nat) :
    (∑ k in range (u n), f k) <=
      ∑ k in range (u 0), f k + ∑ k in range n, (u (k + 1) - u k) • f (u k) := by
  grw [← le_sum_schlomilch' hf h_pos hu n, ← sum_range_add_sum_Ico _ (hu n.zero_le)]

/--
theorem `le_sum_condensed` / 定理 `le_sum_condensed`

English:
theorem le_sum_condensed
  given: (hf : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) (n : Nat)
  proof: by
  grw [← le_sum_condensed' hf n, ← sum_range_add_sum_Ico _ n.one_le_two_pow, sum_range_succ,
    sum_range_zero, zero_add]

中文:
定理 le_sum_condensed
  条件: (hf : 对任意 ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) (n : 自然数)
  证明: by
  grw [← le_sum_condensed' hf n, ← sum_range_add_sum_Ico _ n.one_le_two_pow, sum_range_succ,
    sum_range_zero, zero_add]

Depends on / 依赖: le_sum_condensed, n.one_le_two_pow, one_le_two_pow, sum_range_add_sum_Ico, sum_range_succ, sum_range_zero, zero_add
-/
theorem le_sum_condensed (hf : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) (n : Nat) :
    (∑ k in range (2 ^ n), f k) <= f 0 + ∑ k in range n, 2 ^ k • f (2 ^ k) := by
  grw [← le_sum_condensed' hf n, ← sum_range_add_sum_Ico _ n.one_le_two_pow, sum_range_succ,
    sum_range_zero, zero_add]

/--
theorem `sum_schlomilch_le'` / 定理 `sum_schlomilch_le'`

English:
theorem sum_schlomilch_le'
  statement: (hf : forall ⦃m n⦄, 1 < m -> m <= n -> f n <= f m) (h_pos : forall n, 0 < u n)
  proof: by
  induction n with
  | zero => simp
  | succ n ihn =>
    suffices (u (n + 1) - u n) • f (u (n + 1)) <= ∑ k in Ico (u n + 1) (u (n + 1) + 1), f k by
      rw [sum_range_succ]; rw [← sum_Ico_consecutive]
      exacts [add_le_add ihn this,
        (add_le_add_left (hu n.zero_le) _ : u 0 + 1 <= u n 

中文:
定理 sum_schlomilch_le'
  结论: (hf : 对任意 ⦃m n⦄, 1 < m -> m <= n -> f n <= f m) (h_pos : 对任意 n, 0 < u n)
  证明: by
  induction n with
  | zero => simp
  | succ n ihn =>
    suffices (u (n + 1) - u n) • f (u (n + 1)) <= ∑ k in Ico (u n + 1) (u (n + 1) + 1), f k by
      rw [sum_range_succ]; rw [← sum_Ico_consecutive]
      exacts [add_le_add ihn this,
        (add_le_add_left (hu n.zero_le) _ : u 0 + 1 <= u n 

Depends on / 依赖: EssentiallySmall, EssentiallySmall.mk, Nat.lt_of_le_of_lt, Nat.lt_succ_of_le, Nat.succ_le_of_lt, add_le_add, add_le_add_left, equivSmallModel, exacts, h_pos, le_rfl, le_succ, lt_of_le_of_lt, lt_succ_of_le, mem_Ico, mem_Ico.mp, n.le_succ, n.zero_le, succ_le_of_lt, sum_Ico_consecutive
-/
theorem sum_schlomilch_le' (hf : forall ⦃m n⦄, 1 < m -> m <= n -> f n <= f m) (h_pos : forall n, 0 < u n)
    (hu : Monotone u) (n : Nat) :
    (∑ k in range n, (u (k + 1) - u k) • f (u (k + 1))) <= ∑ k in Ico (u 0 + 1) (u n + 1), f k := by
  induction n with
  | zero => simp
  | succ n ihn =>
    suffices (u (n + 1) - u n) • f (u (n + 1)) <= ∑ k in Ico (u n + 1) (u (n + 1) + 1), f k by
      rw [sum_range_succ]; rw [← sum_Ico_consecutive]
      exacts [add_le_add ihn this,
        (add_le_add_left (hu n.zero_le) _ : u 0 + 1 <= u n + 1),
        add_le_add_left (hu n.le_succ) _]
    have : forall k in Ico (u n + 1) (u (n + 1) + 1), f (u (n + 1)) <= f k := fun k hk =>
      hf (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt (h_pos n)) <| (Nat.lt_succ_of_le le_rfl).trans_le
(mem_Ico.mp hk).1) (Nat.le_of_lt_succ (mem_Ico.mp hk).2)
    convert! sum_le_sum this
    simp

/--
theorem `sum_condensed_le'` / 定理 `sum_condensed_le'`

English:
theorem sum_condensed_le'
  given: (hf : forall ⦃m n⦄, 1 < m -> m <= n -> f n <= f m) (n : Nat)
  proof: by
  convert!
    sum_schlomilch_le' hf (fun n => pow_pos zero_lt_two n)
      (fun m n hm => pow_right_mono₀ one_le_two hm) n using 2
  simp [pow_succ, mul_two]

中文:
定理 sum_condensed_le'
  条件: (hf : 对任意 ⦃m n⦄, 1 < m -> m <= n -> f n <= f m) (n : 自然数)
  证明: by
  convert!
    sum_schlomilch_le' hf (fun n => pow_pos zero_lt_two n)
      (fun m n hm => pow_right_mono₀ one_le_two hm) n using 2
  simp [pow_succ, mul_two]

Depends on / 依赖: convert, mul_two, one_le_two, pow_pos, pow_succ, sum_schlomilch_le, zero_lt_two
-/
theorem sum_condensed_le' (hf : forall ⦃m n⦄, 1 < m -> m <= n -> f n <= f m) (n : Nat) :
    (∑ k in range n, 2 ^ k • f (2 ^ (k + 1))) <= ∑ k in Ico 2 (2 ^ n + 1), f k := by
  convert!
    sum_schlomilch_le' hf (fun n => pow_pos zero_lt_two n)
      (fun m n hm => pow_right_mono₀ one_le_two hm) n using 2
  simp [pow_succ, mul_two]

/--
theorem `sum_schlomilch_le` / 定理 `sum_schlomilch_le`

English:
theorem sum_schlomilch_le
  statement: {C : Nat} (hf : forall ⦃m n⦄, 1 < m -> m <= n -> f n <= f m) (h_pos : forall n, 0 < u n)
  proof: by
  rw [sum_range_succ']; rw [add_comm]
  gcongr
  suffices ∑ k in range n, (u (k + 2) - u (k + 1)) • f (u (k + 1)) <=
  C • ∑ k in range n, ((u (k + 1) - u k) • f (u (k + 1))) by
    refine this.trans (nsmul_le_nsmul_right ?_ _)
    exact sum_schlomilch_le' hf h_pos hu n
  have : forall k in range

中文:
定理 sum_schlomilch_le
  结论: {C : 自然数} (hf : 对任意 ⦃m n⦄, 1 < m -> m <= n -> f n <= f m) (h_pos : 对任意 n, 0 < u n)
  证明: by
  rw [sum_range_succ']; rw [add_comm]
  gcongr
  suffices ∑ k in range n, (u (k + 2) - u (k + 1)) • f (u (k + 1)) <=
  C • ∑ k in range n, ((u (k + 1) - u k) • f (u (k + 1))) by
    refine this.trans (nsmul_le_nsmul_right ?_ _)
    exact sum_schlomilch_le' hf h_pos hu n
  have : forall k in range

Depends on / 依赖: add_comm, convert, h_nonneg, h_pos, h_succ_diff, mod_cast, nsmul_le_nsmul_right, smul_smul, sum_le_sum, sum_range_succ, sum_schlomilch_le, this.trans
-/
theorem sum_schlomilch_le {C : Nat} (hf : forall ⦃m n⦄, 1 < m -> m <= n -> f n <= f m) (h_pos : forall n, 0 < u n)
    (h_nonneg : forall n, 0 <= f n) (hu : Monotone u) (h_succ_diff : SuccDiffBounded C u) (n : Nat) :
    ∑ k in range (n + 1), (u (k + 1) - u k) • f (u k) <=
    (u 1 - u 0) • f (u 0) + C • ∑ k in Ico (u 0 + 1) (u n + 1), f k := by
  rw [sum_range_succ']; rw [add_comm]
  gcongr
  suffices ∑ k in range n, (u (k + 2) - u (k + 1)) • f (u (k + 1)) <=
  C • ∑ k in range n, ((u (k + 1) - u k) • f (u (k + 1))) by
    refine this.trans (nsmul_le_nsmul_right ?_ _)
    exact sum_schlomilch_le' hf h_pos hu n
  have : forall k in range n, (u (k + 2) - u (k + 1)) • f (u (k + 1)) <=
    C • ((u (k + 1) - u k) • f (u (k + 1))) := by
    intro k _
    rw [smul_smul]
    gcongr
    · exact h_nonneg (u (k + 1))
    exact mod_cast h_succ_diff k
  convert! sum_le_sum this
  simp [smul_sum]

/--
theorem `sum_condensed_le` / 定理 `sum_condensed_le`

English:
theorem sum_condensed_le
  given: (hf : forall ⦃m n⦄, 1 < m -> m <= n -> f n <= f m) (n : Nat)
  proof: by
  grw [← sum_condensed_le' hf n]
  simp [sum_range_succ', add_comm, pow_succ', mul_nsmul', sum_nsmul]

中文:
定理 sum_condensed_le
  条件: (hf : 对任意 ⦃m n⦄, 1 < m -> m <= n -> f n <= f m) (n : 自然数)
  证明: by
  grw [← sum_condensed_le' hf n]
  simp [sum_range_succ', add_comm, pow_succ', mul_nsmul', sum_nsmul]

Depends on / 依赖: add_comm, mul_nsmul, pow_succ, sum_condensed_le, sum_nsmul, sum_range_succ
-/
theorem sum_condensed_le (hf : forall ⦃m n⦄, 1 < m -> m <= n -> f n <= f m) (n : Nat) :
    (∑ k in range (n + 1), 2 ^ k • f (2 ^ k)) <= f 1 + 2 • ∑ k in Ico 2 (2 ^ n + 1), f k := by
  grw [← sum_condensed_le' hf n]
  simp [sum_range_succ', add_comm, pow_succ', mul_nsmul', sum_nsmul]

end Finset

namespace ENNReal

open Filter Finset

variable {u : Nat -> Nat} {f : Nat -> Real>=0∞}

open NNReal in
/--
theorem `le_tsum_schlomilch` / 定理 `le_tsum_schlomilch`

English:
theorem le_tsum_schlomilch
  statement: (hf : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) (h_pos : forall n, 0 < u n)
  proof: by
  rw [ENNReal.tsum_eq_iSup_nat' hu.tendsto_atTop]
  refine iSup_le fun n => ?_
  grw [Finset.le_sum_schlomilch hf h_pos hu.monotone n]
  gcongr
  have (k : Nat) : (u (k + 1) - u k : Real>=0∞) = (u (k + 1) - (u k : Nat) : Nat) := by simp
  simp only [nsmul_eq_mul, this]
  apply ENNReal.sum_le_tsum

中文:
定理 le_tsum_schlomilch
  结论: (hf : 对任意 ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) (h_pos : 对任意 n, 0 < u n)
  证明: by
  rw [ENNReal.tsum_eq_iSup_nat' hu.tendsto_atTop]
  refine iSup_le fun n => ?_
  grw [Finset.le_sum_schlomilch hf h_pos hu.monotone n]
  gcongr
  have (k : Nat) : (u (k + 1) - u k : Real>=0∞) = (u (k + 1) - (u k : Nat) : Nat) := by simp
  simp only [nsmul_eq_mul, this]
  apply ENNReal.sum_le_tsum

Depends on / 依赖: ENNReal, ENNReal.sum_le_tsum, ENNReal.tsum_eq_iSup_nat, Finset, Finset.le_sum_schlomilch, h_pos, hu.monotone, hu.tendsto_atTop, iSup_le, le_sum_schlomilch, monotone, nsmul_eq_mul, sum_le_tsum, tendsto_atTop, tsum_eq_iSup_nat
-/
theorem le_tsum_schlomilch (hf : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) (h_pos : forall n, 0 < u n)
    (hu : StrictMono u) :
    ∑' k, f k <= ∑ k in range (u 0), f k + ∑' k : Nat, (u (k + 1) - u k) * f (u k) := by
  rw [ENNReal.tsum_eq_iSup_nat' hu.tendsto_atTop]
  refine iSup_le fun n => ?_
  grw [Finset.le_sum_schlomilch hf h_pos hu.monotone n]
  gcongr
  have (k : Nat) : (u (k + 1) - u k : Real>=0∞) = (u (k + 1) - (u k : Nat) : Nat) := by simp
  simp only [nsmul_eq_mul, this]
  apply ENNReal.sum_le_tsum

/--
theorem `le_tsum_condensed` / 定理 `le_tsum_condensed`

English:
theorem le_tsum_condensed
  given: (hf : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m)
  proof: by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_pow_atTop_atTop_of_one_lt _root_.one_lt_two)]
  refine iSup_le fun n => (Finset.le_sum_condensed hf n).trans ?_
  simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_two]
  grw [ENNReal.sum_le_tsum]

中文:
定理 le_tsum_condensed
  条件: (hf : 对任意 ⦃m n⦄, 0 < m -> m <= n -> f n <= f m)
  证明: by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_pow_atTop_atTop_of_one_lt _root_.one_lt_two)]
  refine iSup_le fun n => (Finset.le_sum_condensed hf n).trans ?_
  simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_two]
  grw [ENNReal.sum_le_tsum]

Depends on / 依赖: ENNReal, ENNReal.sum_le_tsum, ENNReal.tsum_eq_iSup_nat, Finset, Finset.le_sum_condensed, LocallySmall, LocallySmall.hom_small, Nat.cast_pow, Nat.cast_two, _root_, _root_.one_lt_two, cast_pow, cast_two, hom_small, iSup_le, le_sum_condensed, nsmul_eq_mul, one_lt_two, sum_le_tsum, tendsto_pow_atTop_atTop_of_one_lt
-/
theorem le_tsum_condensed (hf : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) :
    ∑' k, f k <= f 0 + ∑' k : Nat, 2 ^ k * f (2 ^ k) := by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_pow_atTop_atTop_of_one_lt _root_.one_lt_two)]
  refine iSup_le fun n => (Finset.le_sum_condensed hf n).trans ?_
  simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_two]
  grw [ENNReal.sum_le_tsum]

/--
theorem `tsum_schlomilch_le` / 定理 `tsum_schlomilch_le`

English:
theorem tsum_schlomilch_le
  statement: {C : Nat} (hf : forall ⦃m n⦄, 1 < m -> m <= n -> f n <= f m) (h_pos : forall n, 0 < u n)
  proof: by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_atTop_mono Nat.le_succ tendsto_id)]
  refine iSup_le fun n => ?_
  grw [← ENNReal.sum_le_tsum <| Finset.Ico (u 0 + 1) (u n + 1)]
  simpa using Finset.sum_schlomilch_le hf h_pos h_nonneg hu h_succ_diff n

中文:
定理 tsum_schlomilch_le
  结论: {C : 自然数} (hf : 对任意 ⦃m n⦄, 1 < m -> m <= n -> f n <= f m) (h_pos : 对任意 n, 0 < u n)
  证明: by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_atTop_mono Nat.le_succ tendsto_id)]
  refine iSup_le fun n => ?_
  grw [← ENNReal.sum_le_tsum <| Finset.Ico (u 0 + 1) (u n + 1)]
  simpa using Finset.sum_schlomilch_le hf h_pos h_nonneg hu h_succ_diff n

Depends on / 依赖: ENNReal, ENNReal.sum_le_tsum, ENNReal.tsum_eq_iSup_nat, Finset, Finset.Ico, Finset.sum_schlomilch_le, Nat.le_succ, h_nonneg, h_pos, h_succ_diff, iSup_le, injective, le_succ, opEquiv, small_of_injective, sum_le_tsum, sum_schlomilch_le, tendsto_atTop_mono, tendsto_id, tsum_eq_iSup_nat
-/
theorem tsum_schlomilch_le {C : Nat} (hf : forall ⦃m n⦄, 1 < m -> m <= n -> f n <= f m) (h_pos : forall n, 0 < u n)
    (h_nonneg : forall n, 0 <= f n) (hu : Monotone u) (h_succ_diff : SuccDiffBounded C u) :
    ∑' k : Nat, (u (k + 1) - u k) * f (u k) <= (u 1 - u 0) * f (u 0) + C * ∑' k, f k := by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_atTop_mono Nat.le_succ tendsto_id)]
  refine iSup_le fun n => ?_
  grw [← ENNReal.sum_le_tsum <| Finset.Ico (u 0 + 1) (u n + 1)]
  simpa using Finset.sum_schlomilch_le hf h_pos h_nonneg hu h_succ_diff n

/--
theorem `tsum_condensed_le` / 定理 `tsum_condensed_le`

English:
theorem tsum_condensed_le
  given: (hf : forall ⦃m n⦄, 1 < m -> m <= n -> f n <= f m)
  proof: by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_atTop_mono Nat.le_succ tendsto_id)]; rw [two_mul]; rw [← two_nsmul]
  refine iSup_le fun n => ?_
  grw [← ENNReal.sum_le_tsum <| Finset.Ico 2 (2 ^ n + 1)]
  simpa using Finset.sum_condensed_le hf n

中文:
定理 tsum_condensed_le
  条件: (hf : 对任意 ⦃m n⦄, 1 < m -> m <= n -> f n <= f m)
  证明: by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_atTop_mono Nat.le_succ tendsto_id)]; rw [two_mul]; rw [← two_nsmul]
  refine iSup_le fun n => ?_
  grw [← ENNReal.sum_le_tsum <| Finset.Ico 2 (2 ^ n + 1)]
  simpa using Finset.sum_condensed_le hf n

Depends on / 依赖: ENNReal, ENNReal.sum_le_tsum, ENNReal.tsum_eq_iSup_nat, Finset, Finset.Ico, Finset.sum_condensed_le, Nat.le_succ, iSup_le, le_succ, sum_condensed_le, sum_le_tsum, tendsto_atTop_mono, tendsto_id, tsum_eq_iSup_nat, two_mul, two_nsmul
-/
theorem tsum_condensed_le (hf : forall ⦃m n⦄, 1 < m -> m <= n -> f n <= f m) :
    (∑' k : Nat, 2 ^ k * f (2 ^ k)) <= f 1 + 2 * ∑' k, f k := by
  rw [ENNReal.tsum_eq_iSup_nat' (tendsto_atTop_mono Nat.le_succ tendsto_id)]; rw [two_mul]; rw [← two_nsmul]
  refine iSup_le fun n => ?_
  grw [← ENNReal.sum_le_tsum <| Finset.Ico 2 (2 ^ n + 1)]
  simpa using Finset.sum_condensed_le hf n

end ENNReal

namespace NNReal

open Finset

open ENNReal in
/--
theorem `summable_schlomilch_iff` / 定理 `summable_schlomilch_iff`

English:
theorem summable_schlomilch_iff
  statement: {C : Nat} {u : Nat -> Nat} {f : Nat -> Real>=0}
  proof: by
  simp only [← tsum_coe_ne_top_iff_summable, Ne, not_iff_not, ENNReal.coe_mul]
  constructor <;> intro h
  · replace hf : forall m n, 1 < m -> m <= n -> (f n : Real>=0∞) <= f m := fun m n hm hmn =>
      ENNReal.coe_le_coe.2 (hf (zero_lt_one.trans hm) hmn)
    have h_nonneg : forall n, 0 <= (f n 

中文:
定理 summable_schlomilch_iff
  结论: {C : 自然数} {u : 自然数 -> 自然数} {f : 自然数 -> 实数>=0}
  证明: by
  simp only [← tsum_coe_ne_top_iff_summable, Ne, not_iff_not, ENNReal.coe_mul]
  constructor <;> intro h
  · replace hf : forall m n, 1 < m -> m <= n -> (f n : Real>=0∞) <= f m := fun m n hm hmn =>
      ENNReal.coe_le_coe.2 (hf (zero_lt_one.trans hm) hmn)
    have h_nonneg : forall n, 0 <= (f n 

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.coe_mul, add_eq_top, coe_le_coe, coe_mul, eq_top_mono, hC_nonzero, h_nonneg, h_pos, h_succ_diff, hu_strict, hu_strict.monotone, monotone, mul_eq_top, mul_ne_top, not_iff_not, replace, tsum_coe_ne_top_iff_summable, tsum_schlomilch_le
-/
theorem summable_schlomilch_iff {C : Nat} {u : Nat -> Nat} {f : Nat -> Real>=0}
    (hf : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m)
    (h_pos : forall n, 0 < u n) (hu_strict : StrictMono u)
    (hC_nonzero : C != 0) (h_succ_diff : SuccDiffBounded C u) :
    (Summable fun k : Nat => (u (k + 1) - (u k : Real>=0)) * f (u k)) ↔ Summable f := by
  simp only [← tsum_coe_ne_top_iff_summable, Ne, not_iff_not, ENNReal.coe_mul]
  constructor <;> intro h
  · replace hf : forall m n, 1 < m -> m <= n -> (f n : Real>=0∞) <= f m := fun m n hm hmn =>
      ENNReal.coe_le_coe.2 (hf (zero_lt_one.trans hm) hmn)
    have h_nonneg : forall n, 0 <= (f n : Real>=0∞) := fun n =>
      ENNReal.coe_le_coe.2 (f n).2
    obtain hC := tsum_schlomilch_le hf h_pos h_nonneg hu_strict.monotone h_succ_diff
    simpa [add_eq_top, mul_ne_top, mul_eq_top, hC_nonzero] using eq_top_mono hC h
  · replace hf : forall m n, 0 < m -> m <= n -> (f n : Real>=0∞) <= f m := fun m n hm hmn =>
      ENNReal.coe_le_coe.2 (hf hm hmn)
    have : ∑ k in range (u 0), (f k : Real>=0∞) != ∞ := sum_ne_top.2 fun a _ => coe_ne_top
    simpa [h, add_eq_top, this] using le_tsum_schlomilch hf h_pos hu_strict

open ENNReal in
/--
theorem `summable_condensed_iff` / 定理 `summable_condensed_iff`

English:
theorem summable_condensed_iff
  given: {f : Nat -> Real>=0} (hf : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m)
  proof: by
  have h_succ_diff : SuccDiffBounded 2 (2 ^ ·) := by
    intro n
    simp [pow_succ, mul_two, two_mul]
  convert!
    summable_schlomilch_iff hf (pow_pos zero_lt_two) (pow_right_strictMono₀ _root_.one_lt_two)
      two_ne_zero h_succ_diff
  simp [pow_succ, mul_two]

中文:
定理 summable_condensed_iff
  条件: {f : 自然数 -> 实数>=0} (hf : 对任意 ⦃m n⦄, 0 < m -> m <= n -> f n <= f m)
  证明: by
  have h_succ_diff : SuccDiffBounded 2 (2 ^ ·) := by
    intro n
    simp [pow_succ, mul_two, two_mul]
  convert!
    summable_schlomilch_iff hf (pow_pos zero_lt_two) (pow_right_strictMono₀ _root_.one_lt_two)
      two_ne_zero h_succ_diff
  simp [pow_succ, mul_two]

Depends on / 依赖: SuccDiffBounded, _root_, _root_.one_lt_two, convert, equivSmallModel, h_succ_diff, locallySmall_congr, mul_two, one_lt_two, pow_pos, pow_succ, summable_schlomilch_iff, two_mul, two_ne_zero, zero_lt_two
-/
theorem summable_condensed_iff {f : Nat -> Real>=0} (hf : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) :
    (Summable fun k : Nat => (2 : Real>=0) ^ k * f (2 ^ k)) ↔ Summable f := by
  have h_succ_diff : SuccDiffBounded 2 (2 ^ ·) := by
    intro n
    simp [pow_succ, mul_two, two_mul]
  convert!
    summable_schlomilch_iff hf (pow_pos zero_lt_two) (pow_right_strictMono₀ _root_.one_lt_two)
      two_ne_zero h_succ_diff
  simp [pow_succ, mul_two]

end NNReal

open NNReal in
/--
theorem `summable_schlomilch_iff_of_nonneg` / 定理 `summable_schlomilch_iff_of_nonneg`

English:
theorem summable_schlomilch_iff_of_nonneg
  statement: {C : Nat} {u : Nat -> Nat} {f : Nat -> Real} (h_nonneg : forall n, 0 <= f n)
  proof: by
  lift f to Nat -> Real>=0 using h_nonneg
  simp only [NNReal.coe_le_coe] at *
  have (k : Nat) : (u (k + 1) - (u k : Real)) = ((u (k + 1) : Real>=0) - (u k : Real>=0) : Real>=0) := by
have := Nat.cast_le (α := Real>=0).mpr (hu_strict k.lt_succ_self).le
    simp [NNReal.coe_sub this]
  simp_rw [t

中文:
定理 summable_schlomilch_iff_of_nonneg
  结论: {C : 自然数} {u : 自然数 -> 自然数} {f : 自然数 -> 实数} (h_nonneg : 对任意 n, 0 <= f n)
  证明: by
  lift f to Nat -> Real>=0 using h_nonneg
  simp only [NNReal.coe_le_coe] at *
  have (k : Nat) : (u (k + 1) - (u k : Real)) = ((u (k + 1) : Real>=0) - (u k : Real>=0) : Real>=0) := by
have := Nat.cast_le (α := Real>=0).mpr (hu_strict k.lt_succ_self).le
    simp [NNReal.coe_sub this]
  simp_rw [t

Depends on / 依赖: Category, NNReal, NNReal.coe_le_coe, NNReal.coe_sub, NNReal.summable_schlomilch_iff, Nat.cast_le, cast_le, coe_le_coe, coe_sub, hC_nonzero, h_nonneg, h_pos, h_succ_diff, hu_strict, k.lt_succ_self, locallySmall_self, lt_succ_self, simp_rw, summable_schlomilch_iff
-/
theorem summable_schlomilch_iff_of_nonneg {C : Nat} {u : Nat -> Nat} {f : Nat -> Real} (h_nonneg : forall n, 0 <= f n)
    (hf : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) (h_pos : forall n, 0 < u n)
    (hu_strict : StrictMono u) (hC_nonzero : C != 0) (h_succ_diff : SuccDiffBounded C u) :
    (Summable fun k : Nat => (u (k + 1) - (u k : Real)) * f (u k)) ↔ Summable f := by
  lift f to Nat -> Real>=0 using h_nonneg
  simp only [NNReal.coe_le_coe] at *
  have (k : Nat) : (u (k + 1) - (u k : Real)) = ((u (k + 1) : Real>=0) - (u k : Real>=0) : Real>=0) := by
have := Nat.cast_le (α := Real>=0).mpr (hu_strict k.lt_succ_self).le
    simp [NNReal.coe_sub this]
  simp_rw [this]
  exact_mod_cast NNReal.summable_schlomilch_iff hf h_pos hu_strict hC_nonzero h_succ_diff

/--
theorem `summable_condensed_iff_of_nonneg` / 定理 `summable_condensed_iff_of_nonneg`

English:
theorem summable_condensed_iff_of_nonneg
  statement: {f : Nat -> Real} (h_nonneg : forall n, 0 <= f n)
  proof: by
  have h_succ_diff : SuccDiffBounded 2 (2 ^ ·) := by
    intro n
    simp [pow_succ, mul_two, two_mul]
  convert!
    summable_schlomilch_iff_of_nonneg h_nonneg h_mono (pow_pos zero_lt_two)
      (pow_right_strictMono₀ one_lt_two) two_ne_zero h_succ_diff
  simp [pow_succ, mul_two]

中文:
定理 summable_condensed_iff_of_nonneg
  结论: {f : 自然数 -> 实数} (h_nonneg : 对任意 n, 0 <= f n)
  证明: by
  have h_succ_diff : SuccDiffBounded 2 (2 ^ ·) := by
    intro n
    simp [pow_succ, mul_two, two_mul]
  convert!
    summable_schlomilch_iff_of_nonneg h_nonneg h_mono (pow_pos zero_lt_two)
      (pow_right_strictMono₀ one_lt_two) two_ne_zero h_succ_diff
  simp [pow_succ, mul_two]

Depends on / 依赖: Category, SuccDiffBounded, UnivLE, convert, h_mono, h_nonneg, h_succ_diff, locallySmall_of_univLE, mul_two, one_lt_two, pow_pos, pow_succ, summable_schlomilch_iff_of_nonneg, two_mul, two_ne_zero, zero_lt_two
-/
theorem summable_condensed_iff_of_nonneg {f : Nat -> Real} (h_nonneg : forall n, 0 <= f n)
    (h_mono : forall ⦃m n⦄, 0 < m -> m <= n -> f n <= f m) :
    (Summable fun k : Nat => (2 : Real) ^ k * f (2 ^ k)) ↔ Summable f := by
  have h_succ_diff : SuccDiffBounded 2 (2 ^ ·) := by
    intro n
    simp [pow_succ, mul_two, two_mul]
  convert!
    summable_schlomilch_iff_of_nonneg h_nonneg h_mono (pow_pos zero_lt_two)
      (pow_right_strictMono₀ one_lt_two) two_ne_zero h_succ_diff
  simp [pow_succ, mul_two]

/--
theorem `summable_condensed_iff_of_eventually_nonneg` / 定理 `summable_condensed_iff_of_eventually_nonneg`

English:
theorem summable_condensed_iff_of_eventually_nonneg
  statement: {f : Nat -> Real} (h_nonneg : 0 <=ᶠ[Filter.atTop] f)
  proof: by
  rw [Filter.EventuallyLE]; rw [Filter.eventually_atTop] at h_nonneg
  rw [Filter.eventually_atTop] at h_mono
  rcases h_nonneg with ⟨n, hn⟩
  rcases h_mono with ⟨m, hm⟩
  convert! summable_condensed_iff_of_nonneg (f := fun k => f (max k (n + m))) _ _ using 1
  · rw [summable_congr_atTop]
    hav

中文:
定理 summable_condensed_iff_of_eventually_nonneg
  结论: {f : 自然数 -> 实数} (h_nonneg : 0 <=ᶠ[滤子.atTop] f)
  证明: by
  rw [Filter.EventuallyLE]; rw [Filter.eventually_atTop] at h_nonneg
  rw [Filter.eventually_atTop] at h_mono
  rcases h_nonneg with ⟨n, hn⟩
  rcases h_mono with ⟨m, hm⟩
  convert! summable_condensed_iff_of_nonneg (f := fun k => f (max k (n + m))) _ _ using 1
  · rw [summable_congr_atTop]
    hav

Depends on / 依赖: EventuallyLE, Filter, Filter.EventuallyLE, Filter.eventuall, Filter.eventually_atTop, convert, eventuall, eventually_atTop, eventually_ge_atTop, filter_upwards, h_mono, h_nonneg, h_pow, h_pow.eventually_ge_atTop, max_eq_left, summable_condensed_iff_of_nonneg, summable_congr_atTop, tendsto_pow_atTop_atTop_of_one_lt
-/
theorem summable_condensed_iff_of_eventually_nonneg {f : Nat -> Real} (h_nonneg : 0 <=ᶠ[Filter.atTop] f)
    (h_mono : forallᶠ k in Filter.atTop, f (k + 1) <= f k) :
    (Summable fun k : Nat => (2 : Real) ^ k * f (2 ^ k)) ↔ Summable f := by
  rw [Filter.EventuallyLE]; rw [Filter.eventually_atTop] at h_nonneg
  rw [Filter.eventually_atTop] at h_mono
  rcases h_nonneg with ⟨n, hn⟩
  rcases h_mono with ⟨m, hm⟩
  convert! summable_condensed_iff_of_nonneg (f := fun k => f (max k (n + m))) _ _ using 1
  · rw [summable_congr_atTop]
    have h_pow := tendsto_pow_atTop_atTop_of_one_lt (r := 2) (by simp)
    filter_upwards [h_pow.eventually_ge_atTop (n + m)] with _ hk using by simp [max_eq_left hk]
  · rw [summable_congr_atTop]
    filter_upwards [Filter.eventually_ge_atTop (n + m)] with _ hk using by simp [max_eq_left hk]
  · simp_all
  · intro _ _ _ _
    exact antitoneOn_nat_Ici_of_succ_le (k := n + m) (by grind) (by simp) (by simp) (by grind)

section p_series

/-!
### Convergence of the `p`-series

In this section we prove that for a real number `p`, the series `∑' n : ℕ, 1 / (n ^ p)` converges if
and only if `1 < p`. There are many different proofs of this fact. The proof in this file uses the
Cauchy condensation test we formalized above. This test implies that `∑ n, 1 / (n ^ p)` converges if
and only if `∑ n, 2 ^ n / ((2 ^ n) ^ p)` converges, and the latter series is a geometric series with
common ratio `2 ^ {1 - p}`. -/

namespace Real

open Filter

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
@[simp]
/--
theorem `summable_nat_rpow_inv` / 定理 `summable_nat_rpow_inv`

English:
theorem summable_nat_rpow_inv
  given: {p : Real}
  proof: by
  rcases le_or_gt 0 p with hp | hp
  /- Cauchy condensation test applies only to antitone sequences, so we consider the
    cases `0 ≤ p` and `p < 0` separately. -/
  · rw [← summable_condensed_iff_of_nonneg]
    · simp_rw [Nat.cast_pow, Nat.cast_two, ← rpow_natCast, ← rpow_mul zero_lt_two.le, mu

中文:
定理 summable_nat_rpow_inv
  条件: {p : 实数}
  证明: by
  rcases le_or_gt 0 p with hp | hp
  /- Cauchy condensation test applies only to antitone sequences, so we consider the
    cases `0 ≤ p` and `p < 0` separately. -/
  · rw [← summable_condensed_iff_of_nonneg]
    · simp_rw [Nat.cast_pow, Nat.cast_two, ← rpow_natCast, ← rpow_mul zero_lt_two.le, mu

Depends on / 依赖: Category, le_or_gt, locallySmall_of_essentiallySmall
-/
theorem summable_nat_rpow_inv {p : Real} :
    Summable (fun n => ((n : Real) ^ p)⁻¹ : Nat -> Real) ↔ 1 < p := by
  rcases le_or_gt 0 p with hp | hp
  /- Cauchy condensation test applies only to antitone sequences, so we consider the
    cases `0 ≤ p` and `p < 0` separately. -/
  · rw [← summable_condensed_iff_of_nonneg]
    · simp_rw [Nat.cast_pow, Nat.cast_two, ← rpow_natCast, ← rpow_mul zero_lt_two.le, mul_comm _ p,
        rpow_mul zero_lt_two.le, rpow_natCast, ← inv_pow, ← mul_pow,
        summable_geometric_iff_norm_lt_one]
      nth_rw 1 [← rpow_one 2]
      rw [← division_def]; rw [← rpow_sub zero_lt_two]; rw [norm_eq_abs]; rw [abs_of_pos (rpow_pos_of_pos zero_lt_two _)]; rw [rpow_lt_one_iff zero_lt_two.le]
      simp
    · intro n
      positivity
    · intro m n hm hmn
      gcongr
  -- If `p < 0`, then `1 / n ^ p` tends to infinity, thus the series diverges.
  · suffices ¬Summable (fun n => ((n : Real) ^ p)⁻¹ : Nat -> Real) by
      have : ¬1 < p := fun hp₁ => hp.not_ge (zero_le_one.trans hp₁.le)
      simpa only [this, iff_false]
    intro h
    obtain ⟨k : Nat, hk₁ : ((k : Real) ^ p)⁻¹ < 1, hk₀ : k != 0⟩ :=
      ((h.tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)).and
          (eventually_cofinite_ne 0)).exists
    apply hk₀
    rw [← pos_iff_ne_zero]; rw [← @Nat.cast_pos Real] at hk₀
    simpa [inv_lt_one₀ (rpow_pos_of_pos hk₀ _), one_lt_rpow_iff_of_pos hk₀, hp,
      hp.not_gt, hk₀] using hk₁

@[simp]
/--
theorem `summable_nat_rpow` / 定理 `summable_nat_rpow`

English:
theorem summable_nat_rpow
  given: {p : Real}
  statement: Summable (fun n => (n : Real) ^ p : Nat -> Real) ↔ p < -1
  proof: by
  rcases neg_surjective p with ⟨p, rfl⟩
  simp [rpow_neg]

中文:
定理 summable_nat_rpow
  条件: {p : 实数}
  结论: Summable (fun n => (n : 实数) ^ p : 自然数 -> 实数) ↔ p < -1
  证明: by
  rcases neg_surjective p with ⟨p, rfl⟩
  simp [rpow_neg]

Depends on / 依赖: neg_surjective, rpow_neg
-/
theorem summable_nat_rpow {p : Real} : Summable (fun n => (n : Real) ^ p : Nat -> Real) ↔ p < -1 := by
  rcases neg_surjective p with ⟨p, rfl⟩
  simp [rpow_neg]

/--
theorem `summable_one_div_nat_rpow` / 定理 `summable_one_div_nat_rpow`

English:
theorem summable_one_div_nat_rpow
  given: {p : Real}
  proof: by
  simp

中文:
定理 summable_one_div_nat_rpow
  条件: {p : 实数}
  证明: by
  simp
-/
theorem summable_one_div_nat_rpow {p : Real} :
    Summable (fun n => 1 / (n : Real) ^ p : Nat -> Real) ↔ 1 < p := by
  simp

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
@[simp]
/--
theorem `summable_nat_pow_inv` / 定理 `summable_nat_pow_inv`

English:
theorem summable_nat_pow_inv
  given: {p : Nat}
  proof: by
  simp only [← rpow_natCast, summable_nat_rpow_inv, Nat.one_lt_cast]

中文:
定理 summable_nat_pow_inv
  条件: {p : 自然数}
  证明: by
  simp only [← rpow_natCast, summable_nat_rpow_inv, Nat.one_lt_cast]

Depends on / 依赖: Nat.one_lt_cast, one_lt_cast, rpow_natCast, summable_nat_rpow_inv
-/
theorem summable_nat_pow_inv {p : Nat} :
    Summable (fun n => ((n : Real) ^ p)⁻¹ : Nat -> Real) ↔ 1 < p := by
  simp only [← rpow_natCast, summable_nat_rpow_inv, Nat.one_lt_cast]

/--
theorem `summable_one_div_nat_pow` / 定理 `summable_one_div_nat_pow`

English:
theorem summable_one_div_nat_pow
  given: {p : Nat}
  proof: by
  simp only [one_div, Real.summable_nat_pow_inv]

中文:
定理 summable_one_div_nat_pow
  条件: {p : 自然数}
  证明: by
  simp only [one_div, Real.summable_nat_pow_inv]

Depends on / 依赖: Real.summable_nat_pow_inv, one_div, summable_nat_pow_inv
-/
theorem summable_one_div_nat_pow {p : Nat} :
    Summable (fun n => 1 / (n : Real) ^ p : Nat -> Real) ↔ 1 < p := by
  simp only [one_div, Real.summable_nat_pow_inv]

/--
theorem `summable_one_div_int_pow` / 定理 `summable_one_div_int_pow`

English:
theorem summable_one_div_int_pow
  given: {p : Nat}
  proof: by
  refine ⟨fun h => summable_one_div_nat_pow.mp (h.comp_injective Nat.cast_injective),
    fun h => .of_nat_of_neg (summable_one_div_nat_pow.mpr h)
      (((summable_one_div_nat_pow.mpr h).mul_left <| 1 / (-1 : Real) ^ p).congr fun n => ?_)⟩
  rw [Int.cast_neg]; rw [Int.cast_natCast]; rw [neg_eq_n

中文:
定理 summable_one_div_int_pow
  条件: {p : 自然数}
  证明: by
  refine ⟨fun h => summable_one_div_nat_pow.mp (h.comp_injective Nat.cast_injective),
    fun h => .of_nat_of_neg (summable_one_div_nat_pow.mpr h)
      (((summable_one_div_nat_pow.mpr h).mul_left <| 1 / (-1 : Real) ^ p).congr fun n => ?_)⟩
  rw [Int.cast_neg]; rw [Int.cast_natCast]; rw [neg_eq_n

Depends on / 依赖: Int.cast_natCast, Int.cast_neg, Nat.cast_injective, cast_injective, cast_natCast, cast_neg, comp_injective, div_div, h.comp_injective, mul_left, mul_one_div, mul_pow, neg_eq_neg_one_mul, of_nat_of_neg, summable_one_div_nat_pow, summable_one_div_nat_pow.mp, summable_one_div_nat_pow.mpr
-/
theorem summable_one_div_int_pow {p : Nat} :
    (Summable fun n : Int => 1 / (n : Real) ^ p) ↔ 1 < p := by
  refine ⟨fun h => summable_one_div_nat_pow.mp (h.comp_injective Nat.cast_injective),
    fun h => .of_nat_of_neg (summable_one_div_nat_pow.mpr h)
      (((summable_one_div_nat_pow.mpr h).mul_left <| 1 / (-1 : Real) ^ p).congr fun n => ?_)⟩
  rw [Int.cast_neg]; rw [Int.cast_natCast]; rw [neg_eq_neg_one_mul (n : Real)]; rw [mul_pow]; rw [mul_one_div]; rw [div_div]

/--
theorem `summable_abs_int_rpow` / 定理 `summable_abs_int_rpow`

English:
theorem summable_abs_int_rpow
  given: {b : Real} (hb : 1 < b)
  proof: by
  apply Summable.of_nat_of_neg
  on_goal 2 => simp_rw [Int.cast_neg, abs_neg]
  all_goals
    simp_rw [Int.cast_natCast, fun n : Nat => abs_of_nonneg (n.cast_nonneg : 0 <= (n : Real))]
    rwa [summable_nat_rpow, neg_lt_neg_iff]

中文:
定理 summable_abs_int_rpow
  条件: {b : 实数} (hb : 1 < b)
  证明: by
  apply Summable.of_nat_of_neg
  on_goal 2 => simp_rw [Int.cast_neg, abs_neg]
  all_goals
    simp_rw [Int.cast_natCast, fun n : Nat => abs_of_nonneg (n.cast_nonneg : 0 <= (n : Real))]
    rwa [summable_nat_rpow, neg_lt_neg_iff]

Depends on / 依赖: Int.cast_natCast, Int.cast_neg, Summable, Summable.of_nat_of_neg, abs_neg, abs_of_nonneg, all_goals, cast_natCast, cast_neg, cast_nonneg, n.cast_nonneg, neg_lt_neg_iff, of_nat_of_neg, on_goal, simp_rw, summable_nat_rpow
-/
theorem summable_abs_int_rpow {b : Real} (hb : 1 < b) :
    Summable fun n : Int => |(n : Real)| ^ (-b) := by
  apply Summable.of_nat_of_neg
  on_goal 2 => simp_rw [Int.cast_neg, abs_neg]
  all_goals
    simp_rw [Int.cast_natCast, fun n : Nat => abs_of_nonneg (n.cast_nonneg : 0 <= (n : Real))]
    rwa [summable_nat_rpow, neg_lt_neg_iff]

/--
theorem `not_summable_natCast_inv` / 定理 `not_summable_natCast_inv`

English:
theorem not_summable_natCast_inv
  statement: ¬Summable (fun n => n⁻¹ : Nat -> Real)
  proof: by
  have : ¬Summable (fun n => ((n : Real) ^ 1)⁻¹ : Nat -> Real) :=
    mt (summable_nat_pow_inv (p := 1)).1 (lt_irrefl 1)
  simpa

中文:
定理 not_summable_natCast_inv
  结论: ¬Summable (fun n => n⁻¹ : 自然数 -> 实数)
  证明: by
  have : ¬Summable (fun n => ((n : Real) ^ 1)⁻¹ : Nat -> Real) :=
    mt (summable_nat_pow_inv (p := 1)).1 (lt_irrefl 1)
  simpa

Depends on / 依赖: Summable, lt_irrefl, summable_nat_pow_inv
-/
theorem not_summable_natCast_inv : ¬Summable (fun n => n⁻¹ : Nat -> Real) := by
  have : ¬Summable (fun n => ((n : Real) ^ 1)⁻¹ : Nat -> Real) :=
    mt (summable_nat_pow_inv (p := 1)).1 (lt_irrefl 1)
  simpa

/--
theorem `not_summable_one_div_natCast` / 定理 `not_summable_one_div_natCast`

English:
theorem not_summable_one_div_natCast
  statement: ¬Summable (fun n => 1 / n : Nat -> Real)
  proof: by
  simpa only [inv_eq_one_div] using not_summable_natCast_inv

中文:
定理 not_summable_one_div_natCast
  结论: ¬Summable (fun n => 1 / n : 自然数 -> 实数)
  证明: by
  simpa only [inv_eq_one_div] using not_summable_natCast_inv

Depends on / 依赖: inv_eq_one_div, not_summable_natCast_inv
-/
theorem not_summable_one_div_natCast : ¬Summable (fun n => 1 / n : Nat -> Real) := by
  simpa only [inv_eq_one_div] using not_summable_natCast_inv

/--
theorem `tendsto_sum_range_one_div_nat_succ_atTop` / 定理 `tendsto_sum_range_one_div_nat_succ_atTop`

English:
theorem tendsto_sum_range_one_div_nat_succ_atTop
  proof: by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg]
  · exact_mod_cast mt (_root_.summable_nat_add_iff 1).1 not_summable_one_div_natCast
  · exact fun i => by positivity

中文:
定理 tendsto_sum_range_one_div_nat_succ_atTop
  证明: by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg]
  · exact_mod_cast mt (_root_.summable_nat_add_iff 1).1 not_summable_one_div_natCast
  · exact fun i => by positivity

Depends on / 依赖: _root_, _root_.summable_nat_add_iff, not_summable_iff_tendsto_nat_atTop_of_nonneg, not_summable_one_div_natCast, summable_nat_add_iff
-/
theorem tendsto_sum_range_one_div_nat_succ_atTop :
    Tendsto (fun n => ∑ i in Finset.range n, (1 / (i + 1) : Real)) atTop atTop := by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg]
  · exact_mod_cast mt (_root_.summable_nat_add_iff 1).1 not_summable_one_div_natCast
  · exact fun i => by positivity

end Real

namespace NNReal

@[simp]
/--
theorem `summable_rpow_inv` / 定理 `summable_rpow_inv`

English:
theorem summable_rpow_inv
  given: {p : Real}
  proof: by
  simp [← NNReal.summable_coe]

@[simp]

中文:
定理 summable_rpow_inv
  条件: {p : 实数}
  证明: by
  simp [← NNReal.summable_coe]

@[simp]

Depends on / 依赖: NNReal, NNReal.summable_coe, summable_coe
-/
theorem summable_rpow_inv {p : Real} :
    Summable (fun n => ((n : Real>=0) ^ p)⁻¹ : Nat -> Real>=0) ↔ 1 < p := by
  simp [← NNReal.summable_coe]

@[simp]
/--
theorem `summable_rpow` / 定理 `summable_rpow`

English:
theorem summable_rpow
  given: {p : Real}
  statement: Summable (fun n => (n : Real>=0) ^ p : Nat -> Real>=0) ↔ p < -1
  proof: by
  simp [← NNReal.summable_coe]

中文:
定理 summable_rpow
  条件: {p : 实数}
  结论: Summable (fun n => (n : 实数>=0) ^ p : 自然数 -> 实数>=0) ↔ p < -1
  证明: by
  simp [← NNReal.summable_coe]

Depends on / 依赖: NNReal, NNReal.summable_coe, summable_coe
-/
theorem summable_rpow {p : Real} : Summable (fun n => (n : Real>=0) ^ p : Nat -> Real>=0) ↔ p < -1 := by
  simp [← NNReal.summable_coe]

/--
theorem `summable_one_div_rpow` / 定理 `summable_one_div_rpow`

English:
theorem summable_one_div_rpow
  given: {p : Real}
  proof: by
  simp

中文:
定理 summable_one_div_rpow
  条件: {p : 实数}
  证明: by
  simp

Depends on / 依赖: ShrinkHoms, ShrinkHoms.toShrinkHoms, toShrinkHoms
-/
theorem summable_one_div_rpow {p : Real} :
    Summable (fun n => 1 / (n : Real>=0) ^ p : Nat -> Real>=0) ↔ 1 < p := by
  simp

end NNReal

end p_series

section

open Finset

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/--
theorem `sum_Ioc_inv_sq_le_sub` / 定理 `sum_Ioc_inv_sq_le_sub`

English:
theorem sum_Ioc_inv_sq_le_sub
  given: {k n : Nat} (hk : k != 0) (h : k <= n)
  proof: by
  refine Nat.le_induction ?_ ?_ n h
  · simp only [Ioc_self, sum_empty, sub_self, le_refl]
  intro n hn IH
  rw [sum_Ioc_succ_top hn]
  grw [IH]
  push_cast
  have A : 0 < (n : α) := by simpa using hk.bot_lt.trans_le hn
  field_simp
  linarith

中文:
定理 sum_Ioc_inv_sq_le_sub
  条件: {k n : 自然数} (hk : k != 0) (h : k <= n)
  证明: by
  refine Nat.le_induction ?_ ?_ n h
  · simp only [Ioc_self, sum_empty, sub_self, le_refl]
  intro n hn IH
  rw [sum_Ioc_succ_top hn]
  grw [IH]
  push_cast
  have A : 0 < (n : α) := by simpa using hk.bot_lt.trans_le hn
  field_simp
  linarith

Depends on / 依赖: Ioc_self, Nat.le_induction, Shrink, Shrink.ext, Subsingleton, Subsingleton.elim, bot_lt, hk.bot_lt.trans_le, le_induction, le_refl, sub_self, sum_Ioc_succ_top, sum_empty, trans_le
-/
theorem sum_Ioc_inv_sq_le_sub {k n : Nat} (hk : k != 0) (h : k <= n) :
    (∑ i in Ioc k n, ((i : α) ^ 2)⁻¹) <= (k : α)⁻¹ - (n : α)⁻¹ := by
  refine Nat.le_induction ?_ ?_ n h
  · simp only [Ioc_self, sum_empty, sub_self, le_refl]
  intro n hn IH
  rw [sum_Ioc_succ_top hn]
  grw [IH]
  push_cast
  have A : 0 < (n : α) := by simpa using hk.bot_lt.trans_le hn
  field_simp
  linarith

/--
theorem `sum_Ioo_inv_sq_le` / 定理 `sum_Ioo_inv_sq_le`

English:
theorem sum_Ioo_inv_sq_le
  given: (k n : Nat)
  statement: (∑ i in Ioo k n, (i ^ 2 : α)⁻¹) <= 2 / (k + 1)
  proof: calc
    (∑ i in Ioo k n, ((i : α) ^ 2)⁻¹) <= ∑ i in Ioc k (max (k + 1) n), ((i : α) ^ 2)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [mem_Ioo] at hx
        simp only [hx, hx.2.le, mem_Ioc, le_max_iff, or_true, and_self_iff]
      · intro i _hi _hident
  

中文:
定理 sum_Ioo_inv_sq_le
  条件: (k n : 自然数)
  结论: (∑ i in 开区间 k n, (i ^ 2 : α)⁻¹) <= 2 / (k + 1)
  证明: calc
    (∑ i in Ioo k n, ((i : α) ^ 2)⁻¹) <= ∑ i in Ioc k (max (k + 1) n), ((i : α) ^ 2)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [mem_Ioo] at hx
        simp only [hx, hx.2.le, mem_Ioc, le_max_iff, or_true, and_self_iff]
      · intro i _hi _hident
  

Depends on / 依赖: Icc_add_one_left_eq_Ioc, Ico_add_one_right_eq_Icc, Nat.lt_succ_self, Nat.succ_lt_succ, _hident, and_self_iff, k.succ, le_max_iff, lt_succ_self, mem_Ioc, mem_Ioo, or_true, succ_lt_succ, sum_eq_sum_Ico_succ_bot, sum_le_sum_of_subset_of_nonneg
-/
theorem sum_Ioo_inv_sq_le (k n : Nat) : (∑ i in Ioo k n, (i ^ 2 : α)⁻¹) <= 2 / (k + 1) :=
  calc
    (∑ i in Ioo k n, ((i : α) ^ 2)⁻¹) <= ∑ i in Ioc k (max (k + 1) n), ((i : α) ^ 2)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [mem_Ioo] at hx
        simp only [hx, hx.2.le, mem_Ioc, le_max_iff, or_true, and_self_iff]
      · intro i _hi _hident
        positivity
    _ <= ((k + 1 : α) ^ 2)⁻¹ + ∑ i in Ioc k.succ (max (k + 1) n), ((i : α) ^ 2)⁻¹ := by
      rw [← Icc_add_one_left_eq_Ioc]; rw [← Ico_add_one_right_eq_Icc]; rw [sum_eq_sum_Ico_succ_bot]
      swap; · exact Nat.succ_lt_succ ((Nat.lt_succ_self k).trans_le (le_max_left _ _))
      rw [Ico_add_one_right_eq_Icc]; rw [Icc_add_one_left_eq_Ioc]
      norm_cast
    _ <= ((k + 1 : α) ^ 2)⁻¹ + (k + 1 : α)⁻¹ := by
      refine add_le_add le_rfl ((sum_Ioc_inv_sq_le_sub ?_ (le_max_left _ _)).trans ?_)
      · simp only [Ne, Nat.succ_ne_zero, not_false_iff]
      · simp only [Nat.cast_succ, sub_le_self_iff, inv_nonneg, Nat.cast_nonneg]
    _ <= 1 / (k + 1) + 1 / (k + 1) := by
      have A : (1 : α) <= k + 1 := by simp only [le_add_iff_nonneg_left, Nat.cast_nonneg]
      simp_rw [← one_div]
      gcongr
      simpa using pow_right_mono₀ A one_le_two
    _ = 2 / (k + 1) := by ring

end

open Set Nat in
/--
lemma `Real.not_summable_indicator_one_div_natCast` / 引理 `Real.not_summable_indicator_one_div_natCast`

English:
lemma Real.not_summable_indicator_one_div_natCast
  given: {m : Nat} (hm : m != 0) (k : ZMod m)
  proof: by
  have : NeZero m := ⟨hm⟩ -- instance is needed below
  rw [← summable_nat_add_iff 1] -- shift by one to avoid non-monotonicity at zero
  have h (n : Nat) : {n : Nat | (n : ZMod m) = k - 1}.indicator (fun n : Nat => (1 / (n + 1 :) : Real)) n =
      if (n : ZMod m) = k - 1 then (1 / (n + 1) : Rea

中文:
引理 实数.not_summable_indicator_one_div_natCast
  条件: {m : 自然数} (hm : m != 0) (k : ZMod m)
  证明: by
  have : NeZero m := ⟨hm⟩ -- instance is needed below
  rw [← summable_nat_add_iff 1] -- shift by one to avoid non-monotonicity at zero
  have h (n : Nat) : {n : Nat | (n : ZMod m) = k - 1}.indicator (fun n : Nat => (1 / (n + 1 :) : Real)) n =
      if (n : ZMod m) = k - 1 then (1 / (n + 1) : Rea

Depends on / 依赖: NeZero, cast_add, cast_one, eq_sub_iff_add_eq, indicator, indicator_apply, instance, mem_ofPred, mem_ofPred_eq, monotonicity, needed, simp_rw, summable_indicator_mod_iff, summable_nat_add_iff
-/
lemma Real.not_summable_indicator_one_div_natCast {m : Nat} (hm : m != 0) (k : ZMod m) :
    ¬ Summable ({n : Nat | (n : ZMod m) = k}.indicator fun n : Nat => (1 / n : Real)) := by
  have : NeZero m := ⟨hm⟩ -- instance is needed below
  rw [← summable_nat_add_iff 1] -- shift by one to avoid non-monotonicity at zero
  have h (n : Nat) : {n : Nat | (n : ZMod m) = k - 1}.indicator (fun n : Nat => (1 / (n + 1 :) : Real)) n =
      if (n : ZMod m) = k - 1 then (1 / (n + 1) : Real) else (0 : Real) := by
    simp only [indicator_apply, mem_ofPred_eq, cast_add, cast_one]
  simp_rw [indicator_apply, mem_ofPred, cast_add, cast_one, ← eq_sub_iff_add_eq, ← h]
  rw [summable_indicator_mod_iff (fun n₁ n₂ h => by gcongr) (k - 1)]
  exact mt (summable_nat_add_iff (f := fun n : Nat => 1 / (n : Real)) 1).mp not_summable_one_div_natCast

/-!
## Translating the `p`-series by a real number
-/
section shifted

open Filter Asymptotics Topology

/--
lemma `Real.summable_one_div_nat_add_rpow` / 引理 `Real.summable_one_div_nat_add_rpow`

English:
lemma Real.summable_one_div_nat_add_rpow
  given: (a : Real) (s : Real)
  proof: by
  have hnorm : Tendsto (fun n : Nat => ‖(n : Real)‖) atTop atTop :=
    tendsto_natCast_atTop_atTop.congr' (by simp)
  have h_abs : (fun n : Nat => |n + a|) ~[atTop] (·) := by
    apply (IsEquivalent.refl.add_const_of_norm_tendsto_atTop hnorm).congr_left
    · filter_upwards [eventually_gt_atTop 

中文:
引理 实数.summable_one_div_nat_add_rpow
  条件: (a : 实数) (s : 实数)
  证明: by
  have hnorm : Tendsto (fun n : Nat => ‖(n : Real)‖) atTop atTop :=
    tendsto_natCast_atTop_atTop.congr' (by simp)
  have h_abs : (fun n : Nat => |n + a|) ~[atTop] (·) := by
    apply (IsEquivalent.refl.add_const_of_norm_tendsto_atTop hnorm).congr_left
    · filter_upwards [eventually_gt_atTop 

Depends on / 依赖: Asymptotics, Asymptotics.IsEquivalent.summable_iff_nat, IsEquivalent, IsEquivalent.refl.add_const_of_norm_tendsto_atTop, Nat.ceil, Nat.lt_of_ceil_lt, Tendsto, abs_neg, abs_of_pos, add_const_of_norm_tendsto_atTop, congr_left, eventually_gt_atTop, filter_upwards, h_abs, lt_of_abs_lt, lt_of_ceil_lt, one_div, summable_iff_nat, summable_one_div_nat_rpow, tendsto_natCast_atTop_atTop
-/
lemma Real.summable_one_div_nat_add_rpow (a : Real) (s : Real) :
    Summable (fun n : Nat => 1 / |n + a| ^ s) ↔ 1 < s := by
  have hnorm : Tendsto (fun n : Nat => ‖(n : Real)‖) atTop atTop :=
    tendsto_natCast_atTop_atTop.congr' (by simp)
  have h_abs : (fun n : Nat => |n + a|) ~[atTop] (·) := by
    apply (IsEquivalent.refl.add_const_of_norm_tendsto_atTop hnorm).congr_left
    · filter_upwards [eventually_gt_atTop (Nat.ceil |a|)] with _ hn
      rw [abs_of_pos]
      linarith [lt_of_abs_lt ((abs_neg a).symm ▸ Nat.lt_of_ceil_lt hn)]
  rw [← summable_one_div_nat_rpow]; rw [Asymptotics.IsEquivalent.summable_iff_nat]
  simpa [one_div] using! (IsEquivalent.rpow (fun n => by positivity) h_abs).inv

/--
lemma `Real.summable_one_div_int_add_rpow` / 引理 `Real.summable_one_div_int_add_rpow`

English:
lemma Real.summable_one_div_int_add_rpow
  given: (a : Real) (s : Real)
  proof: by
  simp_rw [summable_int_iff_summable_nat_and_neg, ← abs_neg (↑(-_ : Int) + a), neg_add,
    Int.cast_neg, neg_neg, Int.cast_natCast, summable_one_div_nat_add_rpow, and_self]

中文:
引理 实数.summable_one_div_int_add_rpow
  条件: (a : 实数) (s : 实数)
  证明: by
  simp_rw [summable_int_iff_summable_nat_and_neg, ← abs_neg (↑(-_ : Int) + a), neg_add,
    Int.cast_neg, neg_neg, Int.cast_natCast, summable_one_div_nat_add_rpow, and_self]

Depends on / 依赖: Int.cast_natCast, Int.cast_neg, abs_neg, and_self, cast_natCast, cast_neg, neg_add, neg_neg, simp_rw, summable_int_iff_summable_nat_and_neg, summable_one_div_nat_add_rpow
-/
lemma Real.summable_one_div_int_add_rpow (a : Real) (s : Real) :
    Summable (fun n : Int => 1 / |n + a| ^ s) ↔ 1 < s := by
  simp_rw [summable_int_iff_summable_nat_and_neg, ← abs_neg (↑(-_ : Int) + a), neg_add,
    Int.cast_neg, neg_neg, Int.cast_natCast, summable_one_div_nat_add_rpow, and_self]

/--
theorem `summable_pow_div_add` / 定理 `summable_pow_div_add`

English:
theorem summable_pow_div_add
  given: {α : Type*} (x : α) [RCLike α] (q k : Nat) (hq : 1 < q)
  proof: by
  simp_rw [norm_div]
  apply Summable.const_div
  simpa [hq, Nat.cast_add, one_div, norm_inv, norm_pow, RCLike.norm_natCast,
    Real.summable_nat_pow_inv, iff_true]
      using summable_nat_add_iff (f := fun x => ‖1 / (x ^ q : α)‖) k

中文:
定理 summable_pow_div_add
  条件: {α : 类型} (x : α) [RCLike α] (q k : 自然数) (hq : 1 < q)
  证明: by
  simp_rw [norm_div]
  apply Summable.const_div
  simpa [hq, Nat.cast_add, one_div, norm_inv, norm_pow, RCLike.norm_natCast,
    Real.summable_nat_pow_inv, iff_true]
      using summable_nat_add_iff (f := fun x => ‖1 / (x ^ q : α)‖) k

Depends on / 依赖: Nat.cast_add, RCLike, RCLike.norm_natCast, Real.summable_nat_pow_inv, Summable, Summable.const_div, cast_add, const_div, iff_true, norm_div, norm_inv, norm_natCast, norm_pow, one_div, simp_rw, summable_nat_add_iff, summable_nat_pow_inv
-/
theorem summable_pow_div_add {α : Type*} (x : α) [RCLike α] (q k : Nat) (hq : 1 < q) :
    Summable fun n : Nat => ‖(x / (↑n + k) ^ q)‖ := by
  simp_rw [norm_div]
  apply Summable.const_div
  simpa [hq, Nat.cast_add, one_div, norm_inv, norm_pow, RCLike.norm_natCast,
    Real.summable_nat_pow_inv, iff_true]
      using summable_nat_add_iff (f := fun x => ‖1 / (x ^ q : α)‖) k

end shifted
