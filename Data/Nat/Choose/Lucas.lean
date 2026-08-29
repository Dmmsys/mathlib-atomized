/-
Copyright (c) 2023 Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gareth Ma
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Polynomial.Basic
meta import Mathlib.Tactic.GRewrite

/-!
# Lucas's theorem

This file contains a proof of [Lucas's theorem](https://en.wikipedia.org/wiki/Lucas's_theorem) about
binomial coefficients, which says that for primes `p`, `n` choose `k` is congruent to product of
`n_i` choose `k_i` modulo `p`, where `n_i` and `k_i` are the base-`p` digits of `n` and `k`,
respectively.

## Main statements

* `lucas_theorem`: the binomial coefficient `n choose k` is congruent to the product of `n_i choose
  k_i` modulo `p`, where `n_i` and `k_i` are the base-`p` digits of `n` and `k`, respectively.
-/

public section

open Finset hiding choose

open Nat Polynomial

namespace Choose

variable {n k a b p : Nat} [Fact p.Prime]

/--
theorem `choose_modEq_choose_mod_mul_choose_div` / 定理 `choose_modEq_choose_mod_mul_choose_div`

English:
theorem choose_modEq_choose_mod_mul_choose_div
  proof: by
  have decompose : ((X : (ZMod p)[X]) + 1) ^ n = (X + 1) ^ (n % p) * (X ^ p + 1) ^ (n / p) := by
    simpa using add_pow_eq_mul_pow_add_pow_div_char (X : (ZMod p)[X]) 1 p _
  simp only [← ZMod.intCast_eq_intCast_iff,
    ← coeff_X_add_one_pow _ n k, ← eq_intCast (Int.castRingHom (ZMod p)), ← coef

中文:
定理 choose_modEq_choose_mod_mul_choose_div
  证明: by
  have decompose : ((X : (ZMod p)[X]) + 1) ^ n = (X + 1) ^ (n % p) * (X ^ p + 1) ^ (n / p) := by
    simpa using add_pow_eq_mul_pow_add_pow_div_char (X : (ZMod p)[X]) 1 p _
  simp only [← ZMod.intCast_eq_intCast_iff,
    ← coeff_X_add_one_pow _ n k, ← eq_intCast (Int.castRingHom (ZMod p)), ← coef

Depends on / 依赖: Int.castRingHom, Polynomial, Polynomial.map_add, Polynomial.map_one, Polynomial.map_pow, ZMod.intCast_eq_intCast_iff, add_pow, add_pow_eq_mul_pow_add_pow_div_char, castRingHom, coeff_X_add_one_pow, coeff_map, conv_lhs, decompose, eq_intCast, intCast_eq_intCast_iff, map_X, map_add, map_one, map_pow, mul_assoc
-/
theorem choose_modEq_choose_mod_mul_choose_div :
    choose n k ≡ choose (n % p) (k % p) * choose (n / p) (k / p) [ZMOD p] := by
  have decompose : ((X : (ZMod p)[X]) + 1) ^ n = (X + 1) ^ (n % p) * (X ^ p + 1) ^ (n / p) := by
    simpa using add_pow_eq_mul_pow_add_pow_div_char (X : (ZMod p)[X]) 1 p _
  simp only [← ZMod.intCast_eq_intCast_iff,
    ← coeff_X_add_one_pow _ n k, ← eq_intCast (Int.castRingHom (ZMod p)), ← coeff_map,
    Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, map_X, decompose]
  simp only [add_pow, one_pow, mul_one, ← pow_mul, sum_mul_sum]
  conv_lhs =>
    enter [1, 2, k, 2, k']
    rw [← mul_assoc]; rw [mul_right_comm _ _ (X ^ (p * k'))]; rw [← pow_add]; rw [mul_assoc]; rw [← cast_mul]
  have h_iff : forall x in range (n % p + 1) ×ˢ range (n / p + 1),
      k = x.1 + p * x.2 ↔ (k % p, k / p) = x := by
    intro ⟨x₁, x₂⟩ hx
    rw [Prod.mk.injEq]
    constructor <;> intro h
    · simp only [mem_product, mem_range] at hx
have h' : x₁ < p := lt_of_lt_of_le hx.left mod_lt _ Fin.pos'
      rw [h]; rw [add_mul_mod_self_left]; rw [add_mul_div_left _ _ Fin.pos']; rw [eq_comm (b := x₂)]
      exact ⟨mod_eq_of_lt h', right_eq_add.mpr (div_eq_of_lt h')⟩
    · rw [← h.left, ← h.right, mod_add_div]
  simp only [finsetSum_coeff, coeff_mul_natCast, coeff_X_pow, ite_mul, zero_mul, ← cast_mul]
  rw [← sum_product']; rw [sum_congr rfl (fun a ha => if_congr (h_iff a ha) rfl rfl)]; rw [sum_ite_eq]
  split_ifs with h
  · simp
  · rw [mem_product, mem_range, mem_range, not_and_or, Nat.lt_succ_iff, not_le, not_lt] at h
    cases h <;> simp [choose_eq_zero_of_lt (by tauto)]

/--
theorem `choose_modEq_choose_mod_mul_choose_div_nat` / 定理 `choose_modEq_choose_mod_mul_choose_div_nat`

English:
theorem choose_modEq_choose_mod_mul_choose_div_nat
  proof: by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_modEq_choose_mod_mul_choose_div

中文:
定理 choose_modEq_choose_mod_mul_choose_div_nat
  证明: by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_modEq_choose_mod_mul_choose_div

Depends on / 依赖: Int.natCast_modEq_iff, choose_modEq_choose_mod_mul_choose_div, natCast_modEq_iff
-/
theorem choose_modEq_choose_mod_mul_choose_div_nat :
    choose n k ≡ choose (n % p) (k % p) * choose (n / p) (k / p) [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_modEq_choose_mod_mul_choose_div

/--
theorem `choose_modEq_choose_mul_prod_range_choose` / 定理 `choose_modEq_choose_mul_prod_range_choose`

English:
theorem choose_modEq_choose_mul_prod_range_choose
  given: (a : Nat)
  proof: match a with
  | Nat.zero => by simp
| Nat.succ a => (choose_modEq_choose_mul_prod_range_choose a).trans by
    rw [prod_range_succ]; rw [cast_mul]; rw [← mul_assoc]; rw [mul_right_comm]
    gcongr
    apply choose_modEq_choose_mod_mul_choose_div.trans
    simp_rw [pow_succ, Nat.div_div_eq_div_mul, 

中文:
定理 choose_modEq_choose_mul_prod_range_choose
  条件: (a : 自然数)
  证明: match a with
  | Nat.zero => by simp
| Nat.succ a => (choose_modEq_choose_mul_prod_range_choose a).trans by
    rw [prod_range_succ]; rw [cast_mul]; rw [← mul_assoc]; rw [mul_right_comm]
    gcongr
    apply choose_modEq_choose_mod_mul_choose_div.trans
    simp_rw [pow_succ, Nat.div_div_eq_div_mul, 

Depends on / 依赖: Int.ModEq.refl, Nat.div_div_eq_div_mul, Nat.succ, Nat.zero, cast_mul, choose_modEq_choose_mod_mul_choose_div, choose_modEq_choose_mod_mul_choose_div.trans, choose_modEq_choose_mul_prod_range_choose, div_div_eq_div_mul, mul_assoc, mul_comm, mul_right_comm, pow_succ, prod_range_succ, simp_rw
-/
theorem choose_modEq_choose_mul_prod_range_choose (a : Nat) :
    choose n k ≡ choose (n / p ^ a) (k / p ^ a) *
      ∏ i in range a, choose (n / p ^ i % p) (k / p ^ i % p) [ZMOD p] :=
  match a with
  | Nat.zero => by simp
| Nat.succ a => (choose_modEq_choose_mul_prod_range_choose a).trans by
    rw [prod_range_succ]; rw [cast_mul]; rw [← mul_assoc]; rw [mul_right_comm]
    gcongr
    apply choose_modEq_choose_mod_mul_choose_div.trans
    simp_rw [pow_succ, Nat.div_div_eq_div_mul, mul_comm, Int.ModEq.refl]

/--
theorem `choose_modEq_prod_range_choose` / 定理 `choose_modEq_prod_range_choose`

English:
theorem choose_modEq_prod_range_choose
  given: {a : Nat} (ha₁ : n < p ^ a) (ha₂ : k < p ^ a)
  proof: by
  apply (choose_modEq_choose_mul_prod_range_choose a).trans
  simp_rw [Nat.div_eq_of_lt ha₁, Nat.div_eq_of_lt ha₂, choose, cast_one, one_mul, cast_prod,
    Int.ModEq.refl]

中文:
定理 choose_modEq_prod_range_choose
  条件: {a : 自然数} (ha₁ : n < p ^ a) (ha₂ : k < p ^ a)
  证明: by
  apply (choose_modEq_choose_mul_prod_range_choose a).trans
  simp_rw [Nat.div_eq_of_lt ha₁, Nat.div_eq_of_lt ha₂, choose, cast_one, one_mul, cast_prod,
    Int.ModEq.refl]

Depends on / 依赖: Int.ModEq.refl, Nat.div_eq_of_lt, cast_one, cast_prod, choose_modEq_choose_mul_prod_range_choose, div_eq_of_lt, one_mul, simp_rw
-/
theorem choose_modEq_prod_range_choose {a : Nat} (ha₁ : n < p ^ a) (ha₂ : k < p ^ a) :
    choose n k ≡ ∏ i in range a, choose (n / p ^ i % p) (k / p ^ i % p) [ZMOD p] := by
  apply (choose_modEq_choose_mul_prod_range_choose a).trans
  simp_rw [Nat.div_eq_of_lt ha₁, Nat.div_eq_of_lt ha₂, choose, cast_one, one_mul, cast_prod,
    Int.ModEq.refl]

/--
theorem `choose_modEq_prod_range_choose_nat` / 定理 `choose_modEq_prod_range_choose_nat`

English:
theorem choose_modEq_prod_range_choose_nat
  given: {a : Nat} (ha₁ : n < p ^ a) (ha₂ : k < p ^ a)
  proof: by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_modEq_prod_range_choose ha₁ ha₂

alias lucas_theorem := choose_modEq_prod_range_choose
alias lucas_theorem_nat := choose_modEq_prod_range_choose_nat

中文:
定理 choose_modEq_prod_range_choose_nat
  条件: {a : 自然数} (ha₁ : n < p ^ a) (ha₂ : k < p ^ a)
  证明: by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_modEq_prod_range_choose ha₁ ha₂

alias lucas_theorem := choose_modEq_prod_range_choose
alias lucas_theorem_nat := choose_modEq_prod_range_choose_nat

Depends on / 依赖: Int.natCast_modEq_iff, choose_modEq_prod_range_choose, natCast_modEq_iff
-/
theorem choose_modEq_prod_range_choose_nat {a : Nat} (ha₁ : n < p ^ a) (ha₂ : k < p ^ a) :
    choose n k ≡ ∏ i in range a, choose (n / p ^ i % p) (k / p ^ i % p) [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_modEq_prod_range_choose ha₁ ha₂

alias lucas_theorem := choose_modEq_prod_range_choose
alias lucas_theorem_nat := choose_modEq_prod_range_choose_nat

/--
theorem `choose_mul_mul_modEq_choose` / 定理 `choose_mul_mul_modEq_choose`

English:
theorem choose_mul_mul_modEq_choose
  proof: by
  grw [choose_modEq_choose_mod_mul_choose_div]
  simp [NeZero.pos, Int.ModEq.refl]

中文:
定理 choose_mul_mul_modEq_choose
  证明: by
  grw [choose_modEq_choose_mod_mul_choose_div]
  simp [NeZero.pos, Int.ModEq.refl]

Depends on / 依赖: Int.ModEq.refl, NeZero, NeZero.pos, choose_modEq_choose_mod_mul_choose_div
-/
theorem choose_mul_mul_modEq_choose :
    choose (p * a) (p * b) ≡ choose a b [ZMOD p] := by
  grw [choose_modEq_choose_mod_mul_choose_div]
  simp [NeZero.pos, Int.ModEq.refl]

/--
theorem `choose_mul_mul_modEq_choose_nat` / 定理 `choose_mul_mul_modEq_choose_nat`

English:
theorem choose_mul_mul_modEq_choose_nat
  proof: by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_mul_mul_modEq_choose

中文:
定理 choose_mul_mul_modEq_choose_nat
  证明: by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_mul_mul_modEq_choose

Depends on / 依赖: Int.natCast_modEq_iff, choose_mul_mul_modEq_choose, natCast_modEq_iff
-/
theorem choose_mul_mul_modEq_choose_nat :
    choose (p * a) (p * b) ≡ choose a b [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_mul_mul_modEq_choose

/--
theorem `choose_pow_mul_pow_mul_modEq_choose` / 定理 `choose_pow_mul_pow_mul_modEq_choose`

English:
theorem choose_pow_mul_pow_mul_modEq_choose
  proof: by
  induction k with
  | zero => simp [Int.ModEq.refl]
  | succ k ih =>
    grw [Nat.pow_succ', mul_assoc, mul_assoc, choose_mul_mul_modEq_choose, ih]

中文:
定理 choose_pow_mul_pow_mul_modEq_choose
  证明: by
  induction k with
  | zero => simp [Int.ModEq.refl]
  | succ k ih =>
    grw [Nat.pow_succ', mul_assoc, mul_assoc, choose_mul_mul_modEq_choose, ih]

Depends on / 依赖: Int.ModEq.refl, Nat.pow_succ, choose_mul_mul_modEq_choose, mul_assoc, pow_succ
-/
theorem choose_pow_mul_pow_mul_modEq_choose :
    choose (p ^ k * a) (p ^ k * b) ≡ choose a b [ZMOD p] := by
  induction k with
  | zero => simp [Int.ModEq.refl]
  | succ k ih =>
    grw [Nat.pow_succ', mul_assoc, mul_assoc, choose_mul_mul_modEq_choose, ih]

/--
theorem `choose_pow_mul_pow_mul_modEq_choose_nat` / 定理 `choose_pow_mul_pow_mul_modEq_choose_nat`

English:
theorem choose_pow_mul_pow_mul_modEq_choose_nat
  proof: by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_pow_mul_pow_mul_modEq_choose

中文:
定理 choose_pow_mul_pow_mul_modEq_choose_nat
  证明: by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_pow_mul_pow_mul_modEq_choose

Depends on / 依赖: Int.natCast_modEq_iff, choose_pow_mul_pow_mul_modEq_choose, natCast_modEq_iff
-/
theorem choose_pow_mul_pow_mul_modEq_choose_nat :
    choose (p ^ k * a) (p ^ k * b) ≡ choose a b [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_pow_mul_pow_mul_modEq_choose

/--
theorem `eq_pow_multiplicity_of_choose_modEq_zero` / 定理 `eq_pow_multiplicity_of_choose_modEq_zero`

English:
theorem eq_pow_multiplicity_of_choose_modEq_zero
  statement: (hn : 0 < n)
  proof: by
  rename_i hp
  by_contra! hn₀
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd p n
  specialize h (p ^ multiplicity p n) (by grind [le_of_dvd hn (pow_multiplicity_dvd p n)])
  nth_grw 1 [← mul_one (p ^ _), hm, choose_pow_mul_pow_mul_modEq_choose, choose_one_right] at h
  suffices multiplicity p n + 1 <=

中文:
定理 eq_pow_multiplicity_of_choose_modEq_zero
  结论: (hn : 0 < n)
  证明: by
  rename_i hp
  by_contra! hn₀
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd p n
  specialize h (p ^ multiplicity p n) (by grind [le_of_dvd hn (pow_multiplicity_dvd p n)])
  nth_grw 1 [← mul_one (p ^ _), hm, choose_pow_mul_pow_mul_modEq_choose, choose_one_right] at h
  suffices multiplicity p n + 1 <=

Depends on / 依赖: FiniteMultiplicity, FiniteMultiplicity.pow_dvd_iff_le_multiplicity, Nat.mul_dvd_mul_left, choose_one_right, choose_pow_mul_pow_mul_modEq_choose, dvd_iff_mod_eq_zero, dvd_iff_mod_eq_zero.mpr, finiteMultiplici, le_of_dvd, mul_dvd_mul_left, mul_one, multiplicity, nth_grw, nth_rw, pow_add, pow_dvd_iff_le_multiplicity, pow_multiplicity_dvd, rename_i, specialize
-/
theorem eq_pow_multiplicity_of_choose_modEq_zero (hn : 0 < n)
    (h : forall i in Icc 1 (n - 1), n.choose i ≡ 0 [ZMOD p]) : n = p ^ multiplicity p n := by
  rename_i hp
  by_contra! hn₀
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd p n
  specialize h (p ^ multiplicity p n) (by grind [le_of_dvd hn (pow_multiplicity_dvd p n)])
  nth_grw 1 [← mul_one (p ^ _), hm, choose_pow_mul_pow_mul_modEq_choose, choose_one_right] at h
  suffices multiplicity p n + 1 <= multiplicity p n by lia
  rw [← FiniteMultiplicity.pow_dvd_iff_le_multiplicity]
  · nth_rw 2 [hm]
    simpa [pow_add] using Nat.mul_dvd_mul_left _ (dvd_iff_mod_eq_zero.mpr (by exact_mod_cast h))
  · exact finiteMultiplicity_iff.mpr ⟨hp.out.ne_one, hn⟩

/--
theorem `eq_pow_multiplicity_of_choose_modEq_zero_nat` / 定理 `eq_pow_multiplicity_of_choose_modEq_zero_nat`

English:
theorem eq_pow_multiplicity_of_choose_modEq_zero_nat
  statement: (hn : 0 < n)
  proof: eq_pow_multiplicity_of_choose_modEq_zero hn (by exact_mod_cast h)

中文:
定理 eq_pow_multiplicity_of_choose_modEq_zero_nat
  结论: (hn : 0 < n)
  证明: eq_pow_multiplicity_of_choose_modEq_zero hn (by exact_mod_cast h)

Depends on / 依赖: eq_pow_multiplicity_of_choose_modEq_zero
-/
theorem eq_pow_multiplicity_of_choose_modEq_zero_nat (hn : 0 < n)
    (h : forall i in Icc 1 (n - 1), n.choose i ≡ 0 [MOD p]) : n = p ^ multiplicity p n :=
  eq_pow_multiplicity_of_choose_modEq_zero hn (by exact_mod_cast h)

/--
theorem `minFac_dvd_gcd_choose_of_isPrimePow` / 定理 `minFac_dvd_gcd_choose_of_isPrimePow`

English:
theorem minFac_dvd_gcd_choose_of_isPrimePow
  given: (h : IsPrimePow n)
  proof: by
  obtain ⟨k, _, _, hn₁⟩ := (isPrimePow_nat_iff_bounded_log_minFac _).mp h
  exact dvd_gcd_iff.mpr fun i hi => by
    nth_rw 2 [hn₁]
    exact Prime.dvd_choose_pow (minFac_prime_iff.mpr h.ne_one) (by grind) (by grind)

中文:
定理 minFac_dvd_gcd_choose_of_isPrimePow
  条件: (h : IsPrimePow n)
  证明: by
  obtain ⟨k, _, _, hn₁⟩ := (isPrimePow_nat_iff_bounded_log_minFac _).mp h
  exact dvd_gcd_iff.mpr fun i hi => by
    nth_rw 2 [hn₁]
    exact Prime.dvd_choose_pow (minFac_prime_iff.mpr h.ne_one) (by grind) (by grind)

Depends on / 依赖: Prime.dvd_choose_pow, dvd_choose_pow, dvd_gcd_iff, dvd_gcd_iff.mpr, h.ne_one, isPrimePow_nat_iff_bounded_log_minFac, minFac_prime_iff, minFac_prime_iff.mpr, ne_one, nth_rw
-/
theorem minFac_dvd_gcd_choose_of_isPrimePow (h : IsPrimePow n) :
    n.minFac ∣ (Icc 1 (n - 1)).gcd n.choose := by
  obtain ⟨k, _, _, hn₁⟩ := (isPrimePow_nat_iff_bounded_log_minFac _).mp h
  exact dvd_gcd_iff.mpr fun i hi => by
    nth_rw 2 [hn₁]
    exact Prime.dvd_choose_pow (minFac_prime_iff.mpr h.ne_one) (by grind) (by grind)

/--
lemma `minFac_sq_ndvd_gcd_choose_of_isPrimePow` / 引理 `minFac_sq_ndvd_gcd_choose_of_isPrimePow`

English:
lemma minFac_sq_ndvd_gcd_choose_of_isPrimePow
  given: (h : IsPrimePow n)
  proof: by
  obtain ⟨k, _, k_pos, hn₁⟩ := (isPrimePow_nat_iff_bounded_log_minFac _).mp h
  have isPrime := minFac_prime_iff.mpr (IsPrimePow.ne_one h)
  refine mt Finset.dvd_gcd_iff.mp ?_
  simp only [mem_Icc, not_forall]
  have : n.minFac ^ (k - 1) <= n.minFac ^ k := Nat.pow_le_pow_right (minFac_pos n) (sub

中文:
引理 minFac_sq_ndvd_gcd_choose_of_isPrimePow
  条件: (h : IsPrimePow n)
  证明: by
  obtain ⟨k, _, k_pos, hn₁⟩ := (isPrimePow_nat_iff_bounded_log_minFac _).mp h
  have isPrime := minFac_prime_iff.mpr (IsPrimePow.ne_one h)
  refine mt Finset.dvd_gcd_iff.mp ?_
  simp only [mem_Icc, not_forall]
  have : n.minFac ^ (k - 1) <= n.minFac ^ k := Nat.pow_le_pow_right (minFac_pos n) (sub

Depends on / 依赖: Finset, Finset.dvd_gcd_iff.mp, IsPrimePow, IsPrimePow.ne_one, Nat.pow_le_pow_right, Nat.pow_lt_pow_of_lt, Prime.one_lt, dvd_gcd_iff, isPrime, isPrimePow_nat_iff_bounded_log_minFac, k_pos, le_sub_one_of_lt, mem_Icc, minFac, minFac_pos, minFac_prime_iff, minFac_prime_iff.mpr, n.minFac, ne_one, not_forall
-/
lemma minFac_sq_ndvd_gcd_choose_of_isPrimePow (h : IsPrimePow n) :
    ¬ n.minFac ^ 2 ∣ (Icc 1 (n - 1)).gcd n.choose := by
  obtain ⟨k, _, k_pos, hn₁⟩ := (isPrimePow_nat_iff_bounded_log_minFac _).mp h
  have isPrime := minFac_prime_iff.mpr (IsPrimePow.ne_one h)
  refine mt Finset.dvd_gcd_iff.mp ?_
  simp only [mem_Icc, not_forall]
  have : n.minFac ^ (k - 1) <= n.minFac ^ k := Nat.pow_le_pow_right (minFac_pos n) (sub_le k 1)
  refine ⟨n.minFac ^ (k - 1), ⟨one_le_pow _ _ (minFac_pos n), ?_⟩, ?_⟩
  · refine le_sub_one_of_lt ?_
    nth_rw 2 [hn₁]
    exact Nat.pow_lt_pow_of_lt (Prime.one_lt isPrime) (sub_one_lt_of_lt k_pos)
  · refine emultiplicity_lt_iff_not_dvd.mp ?_
    nth_rw 2 [hn₁]
    rw [Nat.Prime.emultiplicity_choose_prime_pow isPrime this (pow_ne_zero _
      (Nat.Prime.ne_zero isPrime))]; rw [multiplicity_pow_self_of_prime (prime_iff.mp isPrime)]
    norm_cast
    grind

/--
lemma `primeFactors_gcd_choose_of_isPrimePow` / 引理 `primeFactors_gcd_choose_of_isPrimePow`

English:
lemma primeFactors_gcd_choose_of_isPrimePow
  given: (h : IsPrimePow n)
  proof: by
  have ne_zero : (Icc 1 (n - 1)).gcd n.choose != 0 :=
    gcd_ne_zero_iff.mpr ⟨1, by simp; grind [IsPrimePow.two_le h]⟩
  have isPrime := minFac_prime_iff.mpr (IsPrimePow.ne_one h)
  refine eq_singleton_iff_unique_mem.mpr ⟨isPrime.mem_primeFactors
    (minFac_dvd_gcd_choose_of_isPrimePow h) ne_ze

中文:
引理 primeFactors_gcd_choose_of_isPrimePow
  条件: (h : IsPrimePow n)
  证明: by
  have ne_zero : (Icc 1 (n - 1)).gcd n.choose != 0 :=
    gcd_ne_zero_iff.mpr ⟨1, by simp; grind [IsPrimePow.two_le h]⟩
  have isPrime := minFac_prime_iff.mpr (IsPrimePow.ne_one h)
  refine eq_singleton_iff_unique_mem.mpr ⟨isPrime.mem_primeFactors
    (minFac_dvd_gcd_choose_of_isPrimePow h) ne_ze

Depends on / 依赖: Finset, Finset.dvd_gcd_iff, IsPrimePow, IsPrimePow.ne_one, IsPrimePow.two_le, Nat.Prime, dvd_gcd_iff, eq_pow_multiplicity_of_, eq_singleton_iff_unique_mem, eq_singleton_iff_unique_mem.mpr, gcd_ne_zero_iff, gcd_ne_zero_iff.mpr, isPrime, isPrime.mem_primeFactors, mem_primeFactors, minFac_dvd_gcd_choose_of_isPrimePow, minFac_prime_iff, minFac_prime_iff.mpr, modEq_zero_iff_dvd, n.choose
-/
lemma primeFactors_gcd_choose_of_isPrimePow (h : IsPrimePow n) :
    ((Icc 1 (n - 1)).gcd n.choose).primeFactors = {n.minFac} := by
  have ne_zero : (Icc 1 (n - 1)).gcd n.choose != 0 :=
    gcd_ne_zero_iff.mpr ⟨1, by simp; grind [IsPrimePow.two_le h]⟩
  have isPrime := minFac_prime_iff.mpr (IsPrimePow.ne_one h)
  refine eq_singleton_iff_unique_mem.mpr ⟨isPrime.mem_primeFactors
    (minFac_dvd_gcd_choose_of_isPrimePow h) ne_zero, ?_⟩
  intro p hp
  simp only [mem_primeFactors, ne_eq] at hp
  obtain ⟨hp₁, hp₂, hp₃⟩ := hp
  have : Fact (Nat.Prime p) := ⟨hp₁⟩
  simp_rw [Finset.dvd_gcd_iff, ← modEq_zero_iff_dvd] at hp₂
  have := eq_pow_multiplicity_of_choose_modEq_zero_nat h.pos hp₂
  have dvd_pow : n.minFac ∣ p ^ multiplicity p n := this ▸ minFac_dvd _
.symm exact (Nat.prime_dvd_prime_iff_eq isPrime hp₁).mp (isPrime.dvd_of_dvd_pow dvd_pow)

/--
theorem `gcd_choose_eq_minFac_of_isPrimePow` / 定理 `gcd_choose_eq_minFac_of_isPrimePow`

English:
theorem gcd_choose_eq_minFac_of_isPrimePow
  given: (h : IsPrimePow n)
  proof: by
  have ne_zero : (Icc 1 (n - 1)).gcd n.choose != 0 :=
    gcd_ne_zero_iff.mpr ⟨1, by simp; grind [IsPrimePow.two_le h]⟩
  have isPrime := minFac_prime_iff.mpr (IsPrimePow.ne_one h)
  have : multiplicity n.minFac ((Icc 1 (n - 1)).gcd n.choose) = 1 := by
    refine multiplicity_eq_of_dvd_of_not_dvd

中文:
定理 gcd_choose_eq_minFac_of_isPrimePow
  条件: (h : IsPrimePow n)
  证明: by
  have ne_zero : (Icc 1 (n - 1)).gcd n.choose != 0 :=
    gcd_ne_zero_iff.mpr ⟨1, by simp; grind [IsPrimePow.two_le h]⟩
  have isPrime := minFac_prime_iff.mpr (IsPrimePow.ne_one h)
  have : multiplicity n.minFac ((Icc 1 (n - 1)).gcd n.choose) = 1 := by
    refine multiplicity_eq_of_dvd_of_not_dvd

Depends on / 依赖: IsPrimePow, IsPrimePow.ne_one, IsPrimePow.two_le, Nat.m, Nat.prod_primeFactors_coe_pow_factorization, gcd_ne_zero_iff, gcd_ne_zero_iff.mpr, isPrime, minFac, minFac_dvd_gcd_choose_of_isPrimePow, minFac_prime_iff, minFac_prime_iff.mpr, minFac_sq_ndvd_gcd_choose_of_isPrimePow, multiplicity, multiplicity_eq_of_dvd_of_not_dvd, n.choose, n.minFac, ne_one, ne_zero, primeFactors_gcd_choose_of_isPrimePow
-/
theorem gcd_choose_eq_minFac_of_isPrimePow (h : IsPrimePow n) :
    (Icc 1 (n - 1)).gcd n.choose = n.minFac := by
  have ne_zero : (Icc 1 (n - 1)).gcd n.choose != 0 :=
    gcd_ne_zero_iff.mpr ⟨1, by simp; grind [IsPrimePow.two_le h]⟩
  have isPrime := minFac_prime_iff.mpr (IsPrimePow.ne_one h)
  have : multiplicity n.minFac ((Icc 1 (n - 1)).gcd n.choose) = 1 := by
    refine multiplicity_eq_of_dvd_of_not_dvd ?_ (minFac_sq_ndvd_gcd_choose_of_isPrimePow h)
    simpa using minFac_dvd_gcd_choose_of_isPrimePow h
  rw [Nat.prod_primeFactors_coe_pow_factorization ne_zero]; rw [primeFactors_gcd_choose_of_isPrimePow h]
  simp [← Nat.multiplicity_eq_factorization isPrime ne_zero, this]

/--
theorem `gcd_choose_eq_one_of_not_isPrimePow` / 定理 `gcd_choose_eq_one_of_not_isPrimePow`

English:
theorem gcd_choose_eq_one_of_not_isPrimePow
  given: (hn : 1 < n) (hpn : ¬ IsPrimePow n)
  proof: by
  contrapose! hpn
  obtain ⟨q, hq, h⟩ := Nat.exists_prime_and_dvd hpn
  simp_rw [Finset.dvd_gcd_iff, ← modEq_zero_iff_dvd] at h
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have := eq_pow_multiplicity_of_choose_modEq_zero_nat (zero_lt_of_lt hn) h
  refine (isPrimePow_nat_iff n).mpr ⟨q, _, hq, Dvd.multip

中文:
定理 gcd_choose_eq_one_of_not_isPrimePow
  条件: (hn : 1 < n) (hpn : ¬ IsPrimePow n)
  证明: by
  contrapose! hpn
  obtain ⟨q, hq, h⟩ := Nat.exists_prime_and_dvd hpn
  simp_rw [Finset.dvd_gcd_iff, ← modEq_zero_iff_dvd] at h
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have := eq_pow_multiplicity_of_choose_modEq_zero_nat (zero_lt_of_lt hn) h
  refine (isPrimePow_nat_iff n).mpr ⟨q, _, hq, Dvd.multip

Depends on / 依赖: Dvd.multiplicity_pos, Finset, Finset.dvd_gcd_iff, Nat.Prime, Nat.exists_prime_and_dvd, choose_one_right, contrapose, dvd_gcd_iff, eq_pow_multiplicity_of_choose_modEq_zero_nat, exists_prime_and_dvd, isPrimePow_nat_iff, modEq_zero_iff_dvd, multiplicity_pos, simp_rw, specialize, this.symm, zero_lt_of_lt
-/
theorem gcd_choose_eq_one_of_not_isPrimePow (hn : 1 < n) (hpn : ¬ IsPrimePow n) :
    (Icc 1 (n - 1)).gcd n.choose = 1 := by
  contrapose! hpn
  obtain ⟨q, hq, h⟩ := Nat.exists_prime_and_dvd hpn
  simp_rw [Finset.dvd_gcd_iff, ← modEq_zero_iff_dvd] at h
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have := eq_pow_multiplicity_of_choose_modEq_zero_nat (zero_lt_of_lt hn) h
  refine (isPrimePow_nat_iff n).mpr ⟨q, _, hq, Dvd.multiplicity_pos ?_, this.symm⟩
  specialize h 1 (by grind)
  rw [choose_one_right]; rw [modEq_zero_iff_dvd] at h
  exact h

end Choose
