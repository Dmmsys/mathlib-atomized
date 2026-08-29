/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.SmoothNumbers

/-!
# The sum of the reciprocals of the primes diverges

We show that the sum of `1/p`, where `p` runs through the prime numbers, diverges.
We follow the elementary proof by Erdős that is reproduced in "Proofs from THE BOOK".
There are two versions of the main result: `not_summable_one_div_on_primes`, which
expresses the sum as a sub-sum of the harmonic series, and `Nat.Primes.not_summable_one_div`,
which writes it as a sum over `Nat.Primes`. We also show that the sum of `p^r` for `r : ℝ`
converges if and only if `r < -1`; see `Nat.Primes.summable_rpow`.

## References

See the sixth proof for the infinity of primes in Chapter 1 of [aigner1999proofs].
The proof is due to Erdős.
-/

public section

open Set Nat
open scoped Topology

section PrimeSums

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] (f : Nat -> M)

omit [TopologicalSpace M] in
@[to_additive]
/--
lemma `ite_prime_eq_mulIndicator` / 引理 `ite_prime_eq_mulIndicator`

English:
lemma ite_prime_eq_mulIndicator
  proof: by
  ext; simp [Set.mulIndicator_apply]

中文:
引理 ite_prime_eq_mulIndicator
  证明: by
  ext; simp [Set.mulIndicator_apply]
-/
private lemma ite_prime_eq_mulIndicator :
    (fun n : Nat => if n.Prime then f n else 1) = {n | n.Prime}.mulIndicator f := by
  ext; simp [Set.mulIndicator_apply]

/-- Reindex a product over `Nat.Primes` as a product over `ℕ`, extending `f` by `1`. -/
@[to_additive /-- Reindex a sum over `Nat.Primes` as a sum over `ℕ`, extending `f` by `0`. -/]
/--
theorem `Nat.Primes.tprod_eq_tprod_ite` / 定理 `Nat.Primes.tprod_eq_tprod_ite`

English:
theorem Nat.Primes.tprod_eq_tprod_ite
  proof: by
  rw [ite_prime_eq_mulIndicator]; exact tprod_subtype {n | n.Prime} f

中文:
定理 自然数.Primes.tprod_eq_tprod_ite
  证明: by
  rw [ite_prime_eq_mulIndicator]; exact tprod_subtype {n | n.Prime} f

Depends on / 依赖: ite_prime_eq_mulIndicator, n.Prime, tprod_subtype
-/
theorem Nat.Primes.tprod_eq_tprod_ite :
    ∏' p : Primes, f p = ∏' n : Nat, if n.Prime then f n else 1 := by
  rw [ite_prime_eq_mulIndicator]; exact tprod_subtype {n | n.Prime} f

/-- `Multipliable` over `Nat.Primes` iff over `ℕ` extending `f` by `1`. -/
@[to_additive /-- `Summable` over `Nat.Primes` iff over `ℕ` extending `f` by `0`. -/]
/--
theorem `Nat.Primes.multipliable_iff_multipliable_ite` / 定理 `Nat.Primes.multipliable_iff_multipliable_ite`

English:
theorem Nat.Primes.multipliable_iff_multipliable_ite
  proof: by
  rw [ite_prime_eq_mulIndicator]; exact multipliable_subtype_iff_mulIndicator

中文:
定理 自然数.Primes.multipliable_iff_multipliable_ite
  证明: by
  rw [ite_prime_eq_mulIndicator]; exact multipliable_subtype_iff_mulIndicator

Depends on / 依赖: ite_prime_eq_mulIndicator, multipliable_subtype_iff_mulIndicator
-/
theorem Nat.Primes.multipliable_iff_multipliable_ite :
    Multipliable (fun p : Primes => f p) ↔ Multipliable fun n : Nat => if n.Prime then f n else 1 := by
  rw [ite_prime_eq_mulIndicator]; exact multipliable_subtype_iff_mulIndicator

/-- `HasProd` over `Nat.Primes` iff over `ℕ` extending `f` by `1`. -/
@[to_additive /-- `HasSum` over `Nat.Primes` iff over `ℕ` extending `f` by `0`. -/]
/--
theorem `Nat.Primes.hasProd_iff_hasProd_ite` / 定理 `Nat.Primes.hasProd_iff_hasProd_ite`

English:
theorem Nat.Primes.hasProd_iff_hasProd_ite
  given: {a : M}
  proof: by
  rw [ite_prime_eq_mulIndicator]; exact hasProd_subtype_iff_mulIndicator

中文:
定理 自然数.Primes.hasProd_iff_hasProd_ite
  条件: {a : M}
  证明: by
  rw [ite_prime_eq_mulIndicator]; exact hasProd_subtype_iff_mulIndicator

Depends on / 依赖: hasProd_subtype_iff_mulIndicator, ite_prime_eq_mulIndicator
-/
theorem Nat.Primes.hasProd_iff_hasProd_ite {a : M} :
    HasProd (fun p : Primes => f p) a ↔ HasProd (fun n : Nat => if n.Prime then f n else 1) a := by
  rw [ite_prime_eq_mulIndicator]; exact hasProd_subtype_iff_mulIndicator

end PrimeSums

-- This needs `Mathlib/Analysis/RCLike/Basic.lean`, so we put it here
-- instead of in `Mathlib/NumberTheory/SmoothNumbers.lean`.
/--
lemma `Nat.roughNumbersUpTo_card_le'` / 引理 `Nat.roughNumbersUpTo_card_le'`

English:
lemma Nat.roughNumbersUpTo_card_le'
  given: (N k : Nat)
  proof: by
  simp_rw [Finset.mul_sum, mul_one_div]
exact (Nat.cast_le.mpr <| roughNumbersUpTo_card_le N k).trans
    cast_sum (R := Real) .. ▸ Finset.sum_le_sum fun n _ => cast_div_le

中文:
引理 自然数.roughNumbersUpTo_card_le'
  条件: (N k : 自然数)
  证明: by
  simp_rw [Finset.mul_sum, mul_one_div]
exact (Nat.cast_le.mpr <| roughNumbersUpTo_card_le N k).trans
    cast_sum (R := Real) .. ▸ Finset.sum_le_sum fun n _ => cast_div_le

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_le_sum, Nat.cast_le.mpr, cast_div_le, cast_le, cast_sum, mul_one_div, mul_sum, roughNumbersUpTo_card_le, simp_rw, sum_le_sum
-/
lemma Nat.roughNumbersUpTo_card_le' (N k : Nat) :
    (roughNumbersUpTo N k).card <=
      N * (N.succ.primesBelow \ k.primesBelow).sum (fun p => (1 : Real) / p) := by
  simp_rw [Finset.mul_sum, mul_one_div]
exact (Nat.cast_le.mpr <| roughNumbersUpTo_card_le N k).trans
    cast_sum (R := Real) .. ▸ Finset.sum_le_sum fun n _ => cast_div_le

/--
lemma `one_half_le_sum_primes_ge_one_div` / 引理 `one_half_le_sum_primes_ge_one_div`

English:
lemma one_half_le_sum_primes_ge_one_div
  given: (k : Nat)
  proof: by
  set m : Nat := 2 ^ k.primesBelow.card
  set N₀ : Nat := 2 * m ^ 2 with hN₀
  let S : Real := ((2 * N₀).succ.primesBelow \ k.primesBelow).sum (fun p => (1 / p : Real))
  suffices 1 / 2 <= S by
    convert! this using 5
    rw [show 4 = 2 ^ 2 by simp]; rw [pow_right_comm]
    ring
  suffices 2 * 

中文:
引理 one_half_le_sum_primes_ge_one_div
  条件: (k : 自然数)
  证明: by
  set m : Nat := 2 ^ k.primesBelow.card
  set N₀ : Nat := 2 * m ^ 2 with hN₀
  let S : Real := ((2 * N₀).succ.primesBelow \ k.primesBelow).sum (fun p => (1 / p : Real))
  suffices 1 / 2 <= S by
    convert! this using 5
    rw [show 4 = 2 ^ 2 by simp]; rw [pow_right_comm]
    ring
  suffices 2 * 

Depends on / 依赖: cast_mul, cast_pow, cast_two, convert, k.primesBelow, k.primesBelow.card, mul_assoc, mul_pow, pow_right_comm, pow_two, primesBelow, sqrt_eq, sub_le_iff_le_add, succ.primesBelow
-/
lemma one_half_le_sum_primes_ge_one_div (k : Nat) :
    1 / 2 <= ∑ p in (4 ^ (k.primesBelow.card + 1)).succ.primesBelow \ k.primesBelow,
      (1 / p : Real) := by
  set m : Nat := 2 ^ k.primesBelow.card
  set N₀ : Nat := 2 * m ^ 2 with hN₀
  let S : Real := ((2 * N₀).succ.primesBelow \ k.primesBelow).sum (fun p => (1 / p : Real))
  suffices 1 / 2 <= S by
    convert! this using 5
    rw [show 4 = 2 ^ 2 by simp]; rw [pow_right_comm]
    ring
  suffices 2 * N₀ <= m * (2 * N₀).sqrt + 2 * N₀ * S by
    rwa [hN₀, ← mul_assoc, ← pow_two 2, ← mul_pow, sqrt_eq', ← sub_le_iff_le_add',
      cast_mul, cast_mul, cast_pow, cast_two,
      show (2 * (2 * m ^ 2) - m * (2 * m) : Real) = 2 * (2 * m ^ 2) * (1 / 2) by ring,
mul_le_mul_iff_right₀ by positivity] at this
  calc (2 * N₀ : Real)
    _ = ((2 * N₀).smoothNumbersUpTo k).card + ((2 * N₀).roughNumbersUpTo k).card := by
        exact_mod_cast ((2 * N₀).smoothNumbersUpTo_card_add_roughNumbersUpTo_card k).symm
    _ <= m * (2 * N₀).sqrt + ((2 * N₀).roughNumbersUpTo k).card := by
        exact_mod_cast Nat.add_le_add_right ((2 * N₀).smoothNumbersUpTo_card_le k) _
    _ <= m * (2 * N₀).sqrt + 2 * N₀ * S := by grw [roughNumbersUpTo_card_le']; norm_cast

/--
theorem `not_summable_one_div_on_primes` / 定理 `not_summable_one_div_on_primes`

English:
theorem not_summable_one_div_on_primes
  proof: by
  intro h
  obtain ⟨k, hk⟩ := h.nat_tsum_vanishing (Iio_mem_nhds one_half_pos : Iio (1 / 2 : Real) in 𝓝 0)
  specialize hk ({p | Nat.Prime p} inter {p | k <= p}) inter_subset_right
  rw [tsum_subtype]; rw [indicator_indicator]; rw [inter_eq_left.mpr fun n hn => hn.1]; rw [mem_Iio] at hk
  have h'

中文:
定理 not_summable_one_div_on_primes
  证明: by
  intro h
  obtain ⟨k, hk⟩ := h.nat_tsum_vanishing (Iio_mem_nhds one_half_pos : Iio (1 / 2 : Real) in 𝓝 0)
  specialize hk ({p | Nat.Prime p} inter {p | k <= p}) inter_subset_right
  rw [tsum_subtype]; rw [indicator_indicator]; rw [inter_eq_left.mpr fun n hn => hn.1]; rw [mem_Iio] at hk
  have h'

Depends on / 依赖: Iio_mem_nhds, Nat.Prime, Summable, convert, h.indicator, h.nat_tsum_vanishing, indicator, indicator_indicator, inter_comm, inter_eq_left, inter_eq_left.mpr, inter_subset_right, mem_Iio, nat_tsum_vanishing, one_half_le_sum_, one_half_pos, specialize, tsum_subtype
-/
theorem not_summable_one_div_on_primes :
    ¬ Summable (indicator {p | p.Prime} (fun n : Nat => (1 : Real) / n)) := by
  intro h
  obtain ⟨k, hk⟩ := h.nat_tsum_vanishing (Iio_mem_nhds one_half_pos : Iio (1 / 2 : Real) in 𝓝 0)
  specialize hk ({p | Nat.Prime p} inter {p | k <= p}) inter_subset_right
  rw [tsum_subtype]; rw [indicator_indicator]; rw [inter_eq_left.mpr fun n hn => hn.1]; rw [mem_Iio] at hk
  have h' : Summable (indicator ({p | Nat.Prime p} inter {p | k <= p}) fun n => (1 : Real) / n) := by
    convert! h.indicator {n : Nat | k <= n} using 1
    simp only [indicator_indicator, inter_comm]
  refine ((one_half_le_sum_primes_ge_one_div k).trans_lt <| LE.le.trans_lt ?_ hk).false
  convert!
    Summable.sum_le_tsum (primesBelow ((4 ^ (k.primesBelow.card + 1)).succ) \ primesBelow k)
      (fun n _ => indicator_nonneg (fun p _ => by positivity) _) h' using
    2 with p hp
  obtain ⟨hp₁, hp₂⟩ := mem_ofPred_eq ▸ Finset.mem_sdiff.mp hp
  have hpp := prime_of_mem_primesBelow hp₁
  refine (indicator_of_mem ?_ fun n : Nat => (1 / n : Real)).symm
  exact ⟨hpp, by simpa [primesBelow, hpp] using hp₂⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Nat.Primes.not_summable_one_div` / 定理 `Nat.Primes.not_summable_one_div`

English:
theorem Nat.Primes.not_summable_one_div
  statement: ¬ Summable (fun p : Nat.Primes => (1 / p : Real))
  proof: by
  convert! summable_subtype_iff_indicator.mp.mt not_summable_one_div_on_primes

中文:
定理 自然数.Primes.not_summable_one_div
  结论: ¬ Summable (fun p : 自然数.Primes => (1 / p : 实数))
  证明: by
  convert! summable_subtype_iff_indicator.mp.mt not_summable_one_div_on_primes

Depends on / 依赖: convert, not_summable_one_div_on_primes, summable_subtype_iff_indicator, summable_subtype_iff_indicator.mp.mt
-/
theorem Nat.Primes.not_summable_one_div : ¬ Summable (fun p : Nat.Primes => (1 / p : Real)) := by
  convert! summable_subtype_iff_indicator.mp.mt not_summable_one_div_on_primes

/--
theorem `Nat.Primes.summable_rpow` / 定理 `Nat.Primes.summable_rpow`

English:
theorem Nat.Primes.summable_rpow
  given: {r : Real}
  proof: by
  by_cases h : r < -1
  · -- case `r < -1`
    simp only [h, iff_true]
    exact (Real.summable_nat_rpow.mpr h).subtype _
  · -- case `-1 ≤ r`
    simp only [h, iff_false]
refine fun H => Nat.Primes.not_summable_one_div H.of_nonneg_of_le (fun _ => by positivity) ?_
    intro p
    rw [one_div]; r

中文:
定理 自然数.Primes.summable_rpow
  条件: {r : 实数}
  证明: by
  by_cases h : r < -1
  · -- case `r < -1`
    simp only [h, iff_true]
    exact (Real.summable_nat_rpow.mpr h).subtype _
  · -- case `-1 ≤ r`
    simp only [h, iff_false]
refine fun H => Nat.Primes.not_summable_one_div H.of_nonneg_of_le (fun _ => by positivity) ?_
    intro p
    rw [one_div]; r

Depends on / 依赖: H.of_nonneg_of_le, Nat.Primes.not_summable_one_div, Primes, Real.rpow_le_rpow_of_exponent_le, Real.rpow_neg_one, Real.summable_nat_rpow.mpr, iff_false, iff_true, not_lt, not_lt.mp, not_summable_one_div, of_nonneg_of_le, one_div, one_lt, p.prop.one_lt.le, rpow_le_rpow_of_exponent_le, rpow_neg_one, subtype, summable_nat_rpow
-/
theorem Nat.Primes.summable_rpow {r : Real} :
    Summable (fun p : Nat.Primes => (p : Real) ^ r) ↔ r < -1 := by
  by_cases h : r < -1
  · -- case `r < -1`
    simp only [h, iff_true]
    exact (Real.summable_nat_rpow.mpr h).subtype _
  · -- case `-1 ≤ r`
    simp only [h, iff_false]
refine fun H => Nat.Primes.not_summable_one_div H.of_nonneg_of_le (fun _ => by positivity) ?_
    intro p
    rw [one_div]; rw [← Real.rpow_neg_one]
exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.prop.one_lt.le) not_lt.mp h
