/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
/-!
# The Möbius function and Möbius inversion

## Main Definitions

* `μ` is the Möbius function (spelled `moebius` in code; the notation `μ` is available by opening
  the namespace `ArithmeticFunction.Moebius`).

## Main Results

* Several forms of Möbius inversion:
* `sum_eq_iff_sum_mul_moebius_eq` for functions to a `CommRing`
* `sum_eq_iff_sum_smul_moebius_eq` for functions to an `AddCommGroup`
* `prod_eq_iff_prod_pow_moebius_eq` for functions to a `CommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_of_nonzero` for functions to a `CommGroupWithZero`
* And variants that apply when the equalities only hold on a set `S : Set ℕ` such that
  `m ∣ n → n ∈ S → m ∈ S`:
* `sum_eq_iff_sum_mul_moebius_eq_on` for functions to a `CommRing`
* `sum_eq_iff_sum_smul_moebius_eq_on` for functions to an `AddCommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_on` for functions to a `CommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero` for functions to a `CommGroupWithZero`

## Tags

arithmetic functions, dirichlet convolution, divisors

-/

@[expose] public section

open Finset Nat

variable {R : Type*}

namespace ArithmeticFunction

open scoped zeta

/--
Definition of `moebius` / `moebius` 的定义

English:
definition moebius
  signature: : ArithmeticFunction Int
  body: ⟨fun n => if Squarefree n then (-1) ^ cardFactors n else 0, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.Moebius] notation "μ" => ArithmeticFunction.moebius

中文:
定义 moebius
  签名: : ArithmeticFunction 整数
  定义体: ⟨fun n => if Squarefree n then (-1) ^ cardFactors n else 0, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.Moebius] notation "μ" => ArithmeticFunction.moebius

Depends on / 依赖: Squarefree, cardFactors
-/
def moebius : ArithmeticFunction Int :=
  ⟨fun n => if Squarefree n then (-1) ^ cardFactors n else 0, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.Moebius] notation "μ" => ArithmeticFunction.moebius

open scoped Moebius

@[simp]
/--
theorem `moebius_apply_of_squarefree` / 定理 `moebius_apply_of_squarefree`

English:
theorem moebius_apply_of_squarefree
  given: {n : Nat} (h : Squarefree n)
  statement: μ n = (-1) ^ cardFactors n
  proof: if_pos h

@[simp]

中文:
定理 moebius_apply_of_squarefree
  条件: {n : 自然数} (h : Squarefree n)
  结论: μ n = (-1) ^ cardFactors n
  证明: if_pos h

@[simp]

Depends on / 依赖: if_pos
-/
theorem moebius_apply_of_squarefree {n : Nat} (h : Squarefree n) : μ n = (-1) ^ cardFactors n :=
  if_pos h

@[simp]
/--
theorem `moebius_eq_zero_of_not_squarefree` / 定理 `moebius_eq_zero_of_not_squarefree`

English:
theorem moebius_eq_zero_of_not_squarefree
  given: {n : Nat} (h : ¬Squarefree n)
  statement: μ n = 0
  proof: if_neg h

中文:
定理 moebius_eq_zero_of_not_squarefree
  条件: {n : 自然数} (h : ¬Squarefree n)
  结论: μ n = 0
  证明: if_neg h

Depends on / 依赖: if_neg
-/
theorem moebius_eq_zero_of_not_squarefree {n : Nat} (h : ¬Squarefree n) : μ n = 0 :=
  if_neg h

/--
theorem `moebius_apply_one` / 定理 `moebius_apply_one`

English:
theorem moebius_apply_one
  statement: μ 1 = 1
  proof: by simp

中文:
定理 moebius_apply_one
  结论: μ 1 = 1
  证明: by simp
-/
theorem moebius_apply_one : μ 1 = 1 := by simp

/--
theorem `moebius_ne_zero_iff_squarefree` / 定理 `moebius_ne_zero_iff_squarefree`

English:
theorem moebius_ne_zero_iff_squarefree
  given: {n : Nat}
  statement: μ n != 0 ↔ Squarefree n
  proof: by
  constructor <;> intro h
  · contrapose h
    simp [h]
  · simp [h]

中文:
定理 moebius_ne_zero_iff_squarefree
  条件: {n : 自然数}
  结论: μ n != 0 ↔ Squarefree n
  证明: by
  constructor <;> intro h
  · contrapose h
    simp [h]
  · simp [h]

Depends on / 依赖: contrapose
-/
theorem moebius_ne_zero_iff_squarefree {n : Nat} : μ n != 0 ↔ Squarefree n := by
  constructor <;> intro h
  · contrapose h
    simp [h]
  · simp [h]

/--
theorem `moebius_eq_or` / 定理 `moebius_eq_or`

English:
theorem moebius_eq_or
  given: (n : Nat)
  statement: μ n = 0 ∨ μ n = 1 ∨ μ n = -1
  proof: by
  simp only [moebius, coe_mk]
  split_ifs
  · right
    exact neg_one_pow_eq_or ..
  · left
    rfl

中文:
定理 moebius_eq_or
  条件: (n : 自然数)
  结论: μ n = 0 ∨ μ n = 1 ∨ μ n = -1
  证明: by
  simp only [moebius, coe_mk]
  split_ifs
  · right
    exact neg_one_pow_eq_or ..
  · left
    rfl

Depends on / 依赖: coe_mk, moebius, neg_one_pow_eq_or, split_ifs
-/
theorem moebius_eq_or (n : Nat) : μ n = 0 ∨ μ n = 1 ∨ μ n = -1 := by
  simp only [moebius, coe_mk]
  split_ifs
  · right
    exact neg_one_pow_eq_or ..
  · left
    rfl

/--
theorem `moebius_ne_zero_iff_eq_or` / 定理 `moebius_ne_zero_iff_eq_or`

English:
theorem moebius_ne_zero_iff_eq_or
  given: {n : Nat}
  statement: μ n != 0 ↔ μ n = 1 ∨ μ n = -1
  proof: by
  have := moebius_eq_or n
  lia

中文:
定理 moebius_ne_zero_iff_eq_or
  条件: {n : 自然数}
  结论: μ n != 0 ↔ μ n = 1 ∨ μ n = -1
  证明: by
  have := moebius_eq_or n
  lia

Depends on / 依赖: moebius_eq_or
-/
theorem moebius_ne_zero_iff_eq_or {n : Nat} : μ n != 0 ↔ μ n = 1 ∨ μ n = -1 := by
  have := moebius_eq_or n
  lia

/--
theorem `moebius_sq_eq_one_of_squarefree` / 定理 `moebius_sq_eq_one_of_squarefree`

English:
theorem moebius_sq_eq_one_of_squarefree
  given: {l : Nat} (hl : Squarefree l)
  statement: μ l ^ 2 = 1
  proof: by
  rw [moebius_apply_of_squarefree hl]; rw [← pow_mul]; rw [mul_comm]; rw [pow_mul]; rw [neg_one_sq]; rw [one_pow]

中文:
定理 moebius_sq_eq_one_of_squarefree
  条件: {l : 自然数} (hl : Squarefree l)
  结论: μ l ^ 2 = 1
  证明: by
  rw [moebius_apply_of_squarefree hl]; rw [← pow_mul]; rw [mul_comm]; rw [pow_mul]; rw [neg_one_sq]; rw [one_pow]

Depends on / 依赖: moebius_apply_of_squarefree, mul_comm, neg_one_sq, one_pow, pow_mul
-/
theorem moebius_sq_eq_one_of_squarefree {l : Nat} (hl : Squarefree l) : μ l ^ 2 = 1 := by
  rw [moebius_apply_of_squarefree hl]; rw [← pow_mul]; rw [mul_comm]; rw [pow_mul]; rw [neg_one_sq]; rw [one_pow]

/--
theorem `abs_moebius_eq_one_of_squarefree` / 定理 `abs_moebius_eq_one_of_squarefree`

English:
theorem abs_moebius_eq_one_of_squarefree
  given: {l : Nat} (hl : Squarefree l)
  statement: |μ l| = 1
  proof: by
  simp only [moebius_apply_of_squarefree hl, abs_pow, abs_neg, abs_one, one_pow]

中文:
定理 abs_moebius_eq_one_of_squarefree
  条件: {l : 自然数} (hl : Squarefree l)
  结论: |μ l| = 1
  证明: by
  simp only [moebius_apply_of_squarefree hl, abs_pow, abs_neg, abs_one, one_pow]

Depends on / 依赖: abs_neg, abs_one, abs_pow, moebius_apply_of_squarefree, one_pow
-/
theorem abs_moebius_eq_one_of_squarefree {l : Nat} (hl : Squarefree l) : |μ l| = 1 := by
  simp only [moebius_apply_of_squarefree hl, abs_pow, abs_neg, abs_one, one_pow]

/--
theorem `moebius_sq` / 定理 `moebius_sq`

English:
theorem moebius_sq
  given: {n : Nat}
  proof: by
  split_ifs with h
  · exact moebius_sq_eq_one_of_squarefree h
  · simp only [moebius_eq_zero_of_not_squarefree h, zero_pow (show 2 != 0 by simp)]

中文:
定理 moebius_sq
  条件: {n : 自然数}
  证明: by
  split_ifs with h
  · exact moebius_sq_eq_one_of_squarefree h
  · simp only [moebius_eq_zero_of_not_squarefree h, zero_pow (show 2 != 0 by simp)]

Depends on / 依赖: moebius_eq_zero_of_not_squarefree, moebius_sq_eq_one_of_squarefree, split_ifs, zero_pow
-/
theorem moebius_sq {n : Nat} :
    μ n ^ 2 = if Squarefree n then 1 else 0 := by
  split_ifs with h
  · exact moebius_sq_eq_one_of_squarefree h
  · simp only [moebius_eq_zero_of_not_squarefree h, zero_pow (show 2 != 0 by simp)]

/--
theorem `abs_moebius` / 定理 `abs_moebius`

English:
theorem abs_moebius
  given: {n : Nat}
  proof: by
  split_ifs with h
  · exact abs_moebius_eq_one_of_squarefree h
  · simp only [moebius_eq_zero_of_not_squarefree h, abs_zero]

中文:
定理 abs_moebius
  条件: {n : 自然数}
  证明: by
  split_ifs with h
  · exact abs_moebius_eq_one_of_squarefree h
  · simp only [moebius_eq_zero_of_not_squarefree h, abs_zero]

Depends on / 依赖: abs_moebius_eq_one_of_squarefree, abs_zero, moebius_eq_zero_of_not_squarefree, split_ifs
-/
theorem abs_moebius {n : Nat} :
    |μ n| = if Squarefree n then 1 else 0 := by
  split_ifs with h
  · exact abs_moebius_eq_one_of_squarefree h
  · simp only [moebius_eq_zero_of_not_squarefree h, abs_zero]

/--
theorem `abs_moebius_le_one` / 定理 `abs_moebius_le_one`

English:
theorem abs_moebius_le_one
  given: {n : Nat}
  statement: |μ n| <= 1
  proof: by
  rw [abs_moebius]; rw [apply_ite (· <= 1)]
  simp

中文:
定理 abs_moebius_le_one
  条件: {n : 自然数}
  结论: |μ n| <= 1
  证明: by
  rw [abs_moebius]; rw [apply_ite (· <= 1)]
  simp

Depends on / 依赖: abs_moebius, apply_ite
-/
theorem abs_moebius_le_one {n : Nat} : |μ n| <= 1 := by
  rw [abs_moebius]; rw [apply_ite (· <= 1)]
  simp

/--
theorem `moebius_apply_prime` / 定理 `moebius_apply_prime`

English:
theorem moebius_apply_prime
  given: {p : Nat} (hp : p.Prime)
  statement: μ p = -1
  proof: by
  rw [moebius_apply_of_squarefree hp.squarefree]; rw [cardFactors_apply_prime hp]; rw [pow_one]

中文:
定理 moebius_apply_prime
  条件: {p : 自然数} (hp : p.素)
  结论: μ p = -1
  证明: by
  rw [moebius_apply_of_squarefree hp.squarefree]; rw [cardFactors_apply_prime hp]; rw [pow_one]

Depends on / 依赖: cardFactors_apply_prime, hp.squarefree, moebius_apply_of_squarefree, pow_one, squarefree
-/
theorem moebius_apply_prime {p : Nat} (hp : p.Prime) : μ p = -1 := by
  rw [moebius_apply_of_squarefree hp.squarefree]; rw [cardFactors_apply_prime hp]; rw [pow_one]

/--
theorem `moebius_apply_prime_pow` / 定理 `moebius_apply_prime_pow`

English:
theorem moebius_apply_prime_pow
  given: {p k : Nat} (hp : p.Prime) (hk : k != 0)
  proof: by
  split_ifs with h
  · rw [h, pow_one, moebius_apply_prime hp]
  rw [moebius_eq_zero_of_not_squarefree]
  rw [squarefree_pow_iff hp.ne_one hk]; rw [not_and_or]
  exact Or.inr h

中文:
定理 moebius_apply_prime_pow
  条件: {p k : 自然数} (hp : p.素) (hk : k != 0)
  证明: by
  split_ifs with h
  · rw [h, pow_one, moebius_apply_prime hp]
  rw [moebius_eq_zero_of_not_squarefree]
  rw [squarefree_pow_iff hp.ne_one hk]; rw [not_and_or]
  exact Or.inr h

Depends on / 依赖: Or.inr, hp.ne_one, moebius_apply_prime, moebius_eq_zero_of_not_squarefree, ne_one, not_and_or, pow_one, split_ifs, squarefree_pow_iff
-/
theorem moebius_apply_prime_pow {p k : Nat} (hp : p.Prime) (hk : k != 0) :
    μ (p ^ k) = if k = 1 then -1 else 0 := by
  split_ifs with h
  · rw [h, pow_one, moebius_apply_prime hp]
  rw [moebius_eq_zero_of_not_squarefree]
  rw [squarefree_pow_iff hp.ne_one hk]; rw [not_and_or]
  exact Or.inr h

/--
theorem `moebius_apply_isPrimePow_not_prime` / 定理 `moebius_apply_isPrimePow_not_prime`

English:
theorem moebius_apply_isPrimePow_not_prime
  given: {n : Nat} (hn : IsPrimePow n) (hn' : ¬n.Prime)
  proof: by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  rw [moebius_apply_prime_pow hp hk.ne']; rw [if_neg]
  rintro rfl
  exact hn' (by simpa)

@[arith_mult]

中文:
定理 moebius_apply_isPrimePow_not_prime
  条件: {n : 自然数} (hn : IsPrimePow n) (hn' : ¬n.素)
  证明: by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  rw [moebius_apply_prime_pow hp hk.ne']; rw [if_neg]
  rintro rfl
  exact hn' (by simpa)

@[arith_mult]

Depends on / 依赖: hk.ne, if_neg, isPrimePow_nat_iff, moebius_apply_prime_pow
-/
theorem moebius_apply_isPrimePow_not_prime {n : Nat} (hn : IsPrimePow n) (hn' : ¬n.Prime) :
    μ n = 0 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  rw [moebius_apply_prime_pow hp hk.ne']; rw [if_neg]
  rintro rfl
  exact hn' (by simpa)

@[arith_mult]
/--
theorem `isMultiplicative_moebius` / 定理 `isMultiplicative_moebius`

English:
theorem isMultiplicative_moebius
  statement: IsMultiplicative μ
  proof: by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp, fun {n m} hn hm hnm => ?_⟩
  simp only [moebius, coe_mk, squarefree_mul hnm, ite_zero_mul_ite_zero, cardFactors_mul hn hm,
    pow_add]

中文:
定理 isMultiplicative_moebius
  结论: 是Multiplicative μ
  证明: by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp, fun {n m} hn hm hnm => ?_⟩
  simp only [moebius, coe_mk, squarefree_mul hnm, ite_zero_mul_ite_zero, cardFactors_mul hn hm,
    pow_add]

Depends on / 依赖: IsMultiplicative, IsMultiplicative.iff_ne_zero, cardFactors_mul, coe_mk, iff_ne_zero, ite_zero_mul_ite_zero, moebius, pow_add, squarefree_mul
-/
theorem isMultiplicative_moebius : IsMultiplicative μ := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp, fun {n m} hn hm hnm => ?_⟩
  simp only [moebius, coe_mk, squarefree_mul hnm, ite_zero_mul_ite_zero, cardFactors_mul hn hm,
    pow_add]

/--
theorem `IsMultiplicative.prodPrimeFactors_one_add_of_squarefree` / 定理 `IsMultiplicative.prodPrimeFactors_one_add_of_squarefree`

English:
theorem IsMultiplicative.prodPrimeFactors_one_add_of_squarefree
  statement: [CommSemiring R]
  proof: by
  trans (∏ᵖ p ∣ n, ((ζ : ArithmeticFunction R) + f) p)
  · simp_rw [prodPrimeFactors_apply hn.ne_zero, add_apply, natCoe_apply]
    apply prod_congr rfl; intro p hp
    rw [zeta_apply_ne (prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp).ne_zero]; rw [cast_one]
  rw [isMultiplicative_zeta

中文:
定理 是Multiplicative.prodPrimeFactors_one_add_of_squarefree
  结论: [交换半环 R]
  证明: by
  trans (∏ᵖ p ∣ n, ((ζ : ArithmeticFunction R) + f) p)
  · simp_rw [prodPrimeFactors_apply hn.ne_zero, add_apply, natCoe_apply]
    apply prod_congr rfl; intro p hp
    rw [zeta_apply_ne (prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp).ne_zero]; rw [cast_one]
  rw [isMultiplicative_zeta

Depends on / 依赖: ArithmeticFunction, List.mem_toFinset.mp, add_apply, cast_one, coe_zeta_mul_apply, h_mult, hn.ne_zero, isMultiplicative_zeta, isMultiplicative_zeta.natCast.prodPrimeFactors_add_of_squarefree, mem_toFinset, natCast, natCoe_apply, ne_zero, prime_of_mem_primeFactorsList, prodPrimeFactors_add_of_squarefree, prodPrimeFactors_apply, prod_congr, simp_rw, zeta_apply_ne
-/
theorem IsMultiplicative.prodPrimeFactors_one_add_of_squarefree [CommSemiring R]
    {f : ArithmeticFunction R} (h_mult : f.IsMultiplicative) {n : Nat} (hn : Squarefree n) :
    ∏ p in n.primeFactors, (1 + f p) = ∑ d in n.divisors, f d := by
  trans (∏ᵖ p ∣ n, ((ζ : ArithmeticFunction R) + f) p)
  · simp_rw [prodPrimeFactors_apply hn.ne_zero, add_apply, natCoe_apply]
    apply prod_congr rfl; intro p hp
    rw [zeta_apply_ne (prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp).ne_zero]; rw [cast_one]
  rw [isMultiplicative_zeta.natCast.prodPrimeFactors_add_of_squarefree h_mult hn]; rw [coe_zeta_mul_apply]

/--
theorem `IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree` / 定理 `IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree`

English:
theorem IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
  statement: [CommRing R]
  proof: by
  trans (∏ p in n.primeFactors, (1 + (ArithmeticFunction.pmul (μ : ArithmeticFunction R) f) p))
  · apply prod_congr rfl; intro p hp
    rw [pmul_apply]; rw [intCoe_apply]; rw [ArithmeticFunction.moebius_apply_prime
        (prime_of_mem_primeFactorsList (List.mem_toFinset.mp hp))]
    ring
  · r

中文:
定理 是Multiplicative.prodPrimeFactors_one_sub_of_squarefree
  结论: [交换环 R]
  证明: by
  trans (∏ p in n.primeFactors, (1 + (ArithmeticFunction.pmul (μ : ArithmeticFunction R) f) p))
  · apply prod_congr rfl; intro p hp
    rw [pmul_apply]; rw [intCoe_apply]; rw [ArithmeticFunction.moebius_apply_prime
        (prime_of_mem_primeFactorsList (List.mem_toFinset.mp hp))]
    ring
  · r

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.moebius_apply_prime, ArithmeticFunction.pmul, List.mem_toFinset.mp, intCast, intCoe_apply, isMultiplicative_moebius, isMultiplicative_moebius.intCast.pmul, mem_toFinset, moebius_apply_prime, n.primeFactors, pmul_apply, primeFactors, prime_of_mem_primeFactorsList, prodPrimeFactors_one_add_of_squarefree, prod_congr, simp_rw
-/
theorem IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree [CommRing R]
    (f : ArithmeticFunction R) (hf : f.IsMultiplicative) {n : Nat} (hn : Squarefree n) :
    ∏ p in n.primeFactors, (1 - f p) = ∑ d in n.divisors, μ d * f d := by
  trans (∏ p in n.primeFactors, (1 + (ArithmeticFunction.pmul (μ : ArithmeticFunction R) f) p))
  · apply prod_congr rfl; intro p hp
    rw [pmul_apply]; rw [intCoe_apply]; rw [ArithmeticFunction.moebius_apply_prime
        (prime_of_mem_primeFactorsList (List.mem_toFinset.mp hp))]
    ring
  · rw [(isMultiplicative_moebius.intCast.pmul hf).prodPrimeFactors_one_add_of_squarefree hn]
    simp_rw [pmul_apply, intCoe_apply]

open UniqueFactorizationMonoid

@[simp]
/--
theorem `moebius_mul_coe_zeta` / 定理 `moebius_mul_coe_zeta`

English:
theorem moebius_mul_coe_zeta
  statement: (μ * ζ : ArithmeticFunction Int) = 1
  proof: by
  ext n
  induction n using recOnPosPrimePosCoprime with
  | zero => rw [map_zero, map_zero]
  | one => simp
  | prime_pow p n hp hn =>
    rw [coe_mul_zeta_apply]; rw [sum_divisors_prime_pow hp]; rw [sum_range_succ']
    simp [moebius_apply_prime_pow, hp.ne_one, hn.ne', hp, hn]
  | coprime a b _

中文:
定理 moebius_mul_coe_zeta
  结论: (μ * ζ : ArithmeticFunction 整数) = 1
  证明: by
  ext n
  induction n using recOnPosPrimePosCoprime with
  | zero => rw [map_zero, map_zero]
  | one => simp
  | prime_pow p n hp hn =>
    rw [coe_mul_zeta_apply]; rw [sum_divisors_prime_pow hp]; rw [sum_range_succ']
    simp [moebius_apply_prime_pow, hp.ne_one, hn.ne', hp, hn]
  | coprime a b _

Depends on / 依赖: IsMultiplicative, IsMultiplicative.map_mul_of_coprime, coe_mul_zeta_apply, coprime, hn.ne, hp.ne_one, isMultiplicative_moebius, isMultiplicative_moebius.mul, isMultiplicative_one, isMultiplicative_zeta, isMultiplicative_zeta.natCast, map_mul_of_coprime, map_zero, moebius_apply_prime_pow, natCast, ne_one, prime_pow, recOnPosPrimePosCoprime, sum_divisors_prime_pow, sum_range_succ
-/
theorem moebius_mul_coe_zeta : (μ * ζ : ArithmeticFunction Int) = 1 := by
  ext n
  induction n using recOnPosPrimePosCoprime with
  | zero => rw [map_zero, map_zero]
  | one => simp
  | prime_pow p n hp hn =>
    rw [coe_mul_zeta_apply]; rw [sum_divisors_prime_pow hp]; rw [sum_range_succ']
    simp [moebius_apply_prime_pow, hp.ne_one, hn.ne', hp, hn]
  | coprime a b _ha _hb hab ha' hb' =>
    rw [IsMultiplicative.map_mul_of_coprime _ hab]; rw [ha']; rw [hb']; rw [IsMultiplicative.map_mul_of_coprime isMultiplicative_one hab]
    exact isMultiplicative_moebius.mul isMultiplicative_zeta.natCast

@[simp]
/--
theorem `coe_zeta_mul_moebius` / 定理 `coe_zeta_mul_moebius`

English:
theorem coe_zeta_mul_moebius
  statement: (ζ * μ : ArithmeticFunction Int) = 1
  proof: by
  rw [mul_comm]; rw [moebius_mul_coe_zeta]

@[simp]

中文:
定理 coe_zeta_mul_moebius
  结论: (ζ * μ : ArithmeticFunction 整数) = 1
  证明: by
  rw [mul_comm]; rw [moebius_mul_coe_zeta]

@[simp]

Depends on / 依赖: moebius_mul_coe_zeta, mul_comm
-/
theorem coe_zeta_mul_moebius : (ζ * μ : ArithmeticFunction Int) = 1 := by
  rw [mul_comm]; rw [moebius_mul_coe_zeta]

@[simp]
/--
theorem `coe_moebius_mul_coe_zeta` / 定理 `coe_moebius_mul_coe_zeta`

English:
theorem coe_moebius_mul_coe_zeta
  given: [Ring R]
  statement: (μ * ζ : ArithmeticFunction R) = 1
  proof: by
  rw [← coe_coe]; rw [← intCoe_mul]; rw [moebius_mul_coe_zeta]; rw [intCoe_one]

@[simp]

中文:
定理 coe_moebius_mul_coe_zeta
  条件: [环 R]
  结论: (μ * ζ : ArithmeticFunction R) = 1
  证明: by
  rw [← coe_coe]; rw [← intCoe_mul]; rw [moebius_mul_coe_zeta]; rw [intCoe_one]

@[simp]

Depends on / 依赖: coe_coe, intCoe_mul, intCoe_one, moebius_mul_coe_zeta
-/
theorem coe_moebius_mul_coe_zeta [Ring R] : (μ * ζ : ArithmeticFunction R) = 1 := by
  rw [← coe_coe]; rw [← intCoe_mul]; rw [moebius_mul_coe_zeta]; rw [intCoe_one]

@[simp]
/--
theorem `coe_zeta_mul_coe_moebius` / 定理 `coe_zeta_mul_coe_moebius`

English:
theorem coe_zeta_mul_coe_moebius
  given: [Ring R]
  statement: (ζ * μ : ArithmeticFunction R) = 1
  proof: by
  rw [← coe_coe]; rw [← intCoe_mul]; rw [coe_zeta_mul_moebius]; rw [intCoe_one]

中文:
定理 coe_zeta_mul_coe_moebius
  条件: [环 R]
  结论: (ζ * μ : ArithmeticFunction R) = 1
  证明: by
  rw [← coe_coe]; rw [← intCoe_mul]; rw [coe_zeta_mul_moebius]; rw [intCoe_one]

Depends on / 依赖: coe_coe, coe_zeta_mul_moebius, intCoe_mul, intCoe_one
-/
theorem coe_zeta_mul_coe_moebius [Ring R] : (ζ * μ : ArithmeticFunction R) = 1 := by
  rw [← coe_coe]; rw [← intCoe_mul]; rw [coe_zeta_mul_moebius]; rw [intCoe_one]

section CommRing

variable [CommRing R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Invertible (ζ : ArithmeticFunction R)
  body: μ
  invOf_mul_self := coe_moebius_mul_coe_zeta
  mul_invOf_self := coe_zeta_mul_coe_moebius

中文:
实例 :
  签名: 可逆 (ζ : ArithmeticFunction R)
  定义体: μ
  invOf_mul_self := coe_moebius_mul_coe_zeta
  mul_invOf_self := coe_zeta_mul_coe_moebius
-/
instance : Invertible (ζ : ArithmeticFunction R) where
  invOf := μ
  invOf_mul_self := coe_moebius_mul_coe_zeta
  mul_invOf_self := coe_zeta_mul_coe_moebius

/--
Definition of `zetaUnit` / `zetaUnit` 的定义

English:
definition zetaUnit
  signature: : (ArithmeticFunction R)ˣ
  body: ⟨ζ, μ, coe_zeta_mul_coe_moebius, coe_moebius_mul_coe_zeta⟩

@[simp]

中文:
定义 zetaUnit
  签名: : (ArithmeticFunction R)ˣ
  定义体: ⟨ζ, μ, coe_zeta_mul_coe_moebius, coe_moebius_mul_coe_zeta⟩

@[simp]

Depends on / 依赖: coe_moebius_mul_coe_zeta, coe_zeta_mul_coe_moebius
-/
def zetaUnit : (ArithmeticFunction R)ˣ :=
  ⟨ζ, μ, coe_zeta_mul_coe_moebius, coe_moebius_mul_coe_zeta⟩

@[simp]
/--
theorem `coe_zetaUnit` / 定理 `coe_zetaUnit`

English:
theorem coe_zetaUnit
  statement: ((zetaUnit : (ArithmeticFunction R)ˣ) : ArithmeticFunction R) = ζ
  proof: rfl

@[simp]

中文:
定理 coe_zetaUnit
  结论: ((zetaUnit : (ArithmeticFunction R)ˣ) : ArithmeticFunction R) = ζ
  证明: rfl

@[simp]
-/
theorem coe_zetaUnit : ((zetaUnit : (ArithmeticFunction R)ˣ) : ArithmeticFunction R) = ζ :=
  rfl

@[simp]
/--
theorem `inv_zetaUnit` / 定理 `inv_zetaUnit`

English:
theorem inv_zetaUnit
  statement: ((zetaUnit⁻¹ : (ArithmeticFunction R)ˣ) : ArithmeticFunction R) = μ
  proof: rfl

中文:
定理 inv_zetaUnit
  结论: ((zetaUnit⁻¹ : (ArithmeticFunction R)ˣ) : ArithmeticFunction R) = μ
  证明: rfl
-/
theorem inv_zetaUnit : ((zetaUnit⁻¹ : (ArithmeticFunction R)ˣ) : ArithmeticFunction R) = μ :=
  rfl

end CommRing

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sum_eq_iff_sum_smul_moebius_eq` / 定理 `sum_eq_iff_sum_smul_moebius_eq`

English:
theorem sum_eq_iff_sum_smul_moebius_eq
  given: [AddCommGroup R] {f g : Nat -> R}
  proof: by
  let f' : ArithmeticFunction R := ⟨fun x => if x = 0 then 0 else f x, if_pos rfl⟩
  let g' : ArithmeticFunction R := ⟨fun x => if x = 0 then 0 else g x, if_pos rfl⟩
  trans (ζ : ArithmeticFunction Int) • f' = g'
  · rw [ArithmeticFunction.ext_iff]
    apply forall_congr'
    intro n
    cases n 

中文:
定理 sum_eq_iff_sum_smul_moebius_eq
  条件: [加法交换群 R] {f g : 自然数 -> R}
  证明: by
  let f' : ArithmeticFunction R := ⟨fun x => if x = 0 then 0 else f x, if_pos rfl⟩
  let g' : ArithmeticFunction R := ⟨fun x => if x = 0 then 0 else g x, if_pos rfl⟩
  trans (ζ : ArithmeticFunction Int) • f' = g'
  · rw [ArithmeticFunction.ext_iff]
    apply forall_congr'
    intro n
    cases n 

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.ext_iff, coe_mk, coe_zeta_smul_apply, ext_iff, forall_congr, forall_prop_of_true, if_neg, if_pos, ite_false, pos_of_mem_divisors, succ_ne_zero, succ_pos, sum_congr
-/
theorem sum_eq_iff_sum_smul_moebius_eq [AddCommGroup R] {f g : Nat -> R} :
    (forall n > 0, ∑ i in n.divisors, f i = g n) ↔
      forall n > 0, ∑ x in n.divisorsAntidiagonal, μ x.fst • g x.snd = f n := by
  let f' : ArithmeticFunction R := ⟨fun x => if x = 0 then 0 else f x, if_pos rfl⟩
  let g' : ArithmeticFunction R := ⟨fun x => if x = 0 then 0 else g x, if_pos rfl⟩
  trans (ζ : ArithmeticFunction Int) • f' = g'
  · rw [ArithmeticFunction.ext_iff]
    apply forall_congr'
    intro n
    cases n with
    | zero => simp
    | succ n =>
      rw [coe_zeta_smul_apply]
      simp only [forall_prop_of_true, succ_pos', f', g', coe_mk, succ_ne_zero, ite_false]
      rw [sum_congr rfl fun x hx => if_neg (pos_of_mem_divisors hx).ne']
  trans μ • g' = f'
  · constructor <;> intro h <;>
      simp only [← h, ← mul_smul, moebius_mul_coe_zeta, coe_zeta_mul_moebius, one_smul]
  · rw [ArithmeticFunction.ext_iff]
    apply forall_congr'
    intro n
    cases n with
    | zero => simp
    | succ n =>
      simp only [forall_prop_of_true, succ_pos', smul_apply, f', g', coe_mk, succ_ne_zero,
        ite_false]
      rw [sum_congr rfl fun x hx => ?_]
      rw [if_neg (pos_of_mem_divisors (snd_mem_divisors_of_mem_antidiagonal hx)).ne']

/--
theorem `sum_eq_iff_sum_mul_moebius_eq` / 定理 `sum_eq_iff_sum_mul_moebius_eq`

English:
theorem sum_eq_iff_sum_mul_moebius_eq
  given: [NonAssocRing R] {f g : Nat -> R}
  proof: by
  rw [sum_eq_iff_sum_smul_moebius_eq]
  apply forall_congr'
  refine fun a => imp_congr_right fun _ => (sum_congr rfl fun x _hx => ?_).congr_left
  rw [zsmul_eq_mul]

中文:
定理 sum_eq_iff_sum_mul_moebius_eq
  条件: [非结合环 R] {f g : 自然数 -> R}
  证明: by
  rw [sum_eq_iff_sum_smul_moebius_eq]
  apply forall_congr'
  refine fun a => imp_congr_right fun _ => (sum_congr rfl fun x _hx => ?_).congr_left
  rw [zsmul_eq_mul]

Depends on / 依赖: congr_left, forall_congr, imp_congr_right, sum_congr, sum_eq_iff_sum_smul_moebius_eq, zsmul_eq_mul
-/
theorem sum_eq_iff_sum_mul_moebius_eq [NonAssocRing R] {f g : Nat -> R} :
    (forall n > 0, ∑ i in n.divisors, f i = g n) ↔
      forall n > 0, ∑ x in n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd = f n := by
  rw [sum_eq_iff_sum_smul_moebius_eq]
  apply forall_congr'
  refine fun a => imp_congr_right fun _ => (sum_congr rfl fun x _hx => ?_).congr_left
  rw [zsmul_eq_mul]

/--
theorem `prod_eq_iff_prod_pow_moebius_eq` / 定理 `prod_eq_iff_prod_pow_moebius_eq`

English:
theorem prod_eq_iff_prod_pow_moebius_eq
  given: [CommGroup R] {f g : Nat -> R}
  proof: @sum_eq_iff_sum_smul_moebius_eq (Additive R) _ _ _

中文:
定理 prod_eq_iff_prod_pow_moebius_eq
  条件: [交换群 R] {f g : 自然数 -> R}
  证明: @sum_eq_iff_sum_smul_moebius_eq (Additive R) _ _ _

Depends on / 依赖: Additive, sum_eq_iff_sum_smul_moebius_eq
-/
theorem prod_eq_iff_prod_pow_moebius_eq [CommGroup R] {f g : Nat -> R} :
    (forall n > 0, ∏ i in n.divisors, f i = g n) ↔
      forall n > 0, ∏ x in n.divisorsAntidiagonal, g x.snd ^ μ x.fst = f n :=
  @sum_eq_iff_sum_smul_moebius_eq (Additive R) _ _ _

/--
theorem `prod_eq_iff_prod_pow_moebius_eq_of_nonzero` / 定理 `prod_eq_iff_prod_pow_moebius_eq_of_nonzero`

English:
theorem prod_eq_iff_prod_pow_moebius_eq_of_nonzero
  statement: [CommGroupWithZero R] {f g : Nat -> R}
  proof: by
  refine
      Iff.trans
        (Iff.trans (forall_congr' fun n => ?_)
          (@prod_eq_iff_prod_pow_moebius_eq Rˣ _
            (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1) fun n =>
            if h : 0 < n then Units.mk0 (g n) (hg n h) else 1))
        (forall_congr' fun n =

中文:
定理 prod_eq_iff_prod_pow_moebius_eq_of_nonzero
  结论: [带零交换群 R] {f g : 自然数 -> R}
  证明: by
  refine
      Iff.trans
        (Iff.trans (forall_congr' fun n => ?_)
          (@prod_eq_iff_prod_pow_moebius_eq Rˣ _
            (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1) fun n =>
            if h : 0 < n then Units.mk0 (g n) (hg n h) else 1))
        (forall_congr' fun n =

Depends on / 依赖: Iff.trans, Units.coeHom_apply, Units.mk0, Units.val_inj, Units.val_mk0, coeHom_apply, dif_pos, forall_congr, imp_congr_right, map_prod, pos_of_mem_divisors, prod_congr, prod_eq_iff_prod_pow_moebius_eq, val_inj, val_mk0
-/
theorem prod_eq_iff_prod_pow_moebius_eq_of_nonzero [CommGroupWithZero R] {f g : Nat -> R}
    (hf : forall n : Nat, 0 < n -> f n != 0) (hg : forall n : Nat, 0 < n -> g n != 0) :
    (forall n > 0, ∏ i in n.divisors, f i = g n) ↔
      forall n > 0, ∏ x in n.divisorsAntidiagonal, g x.snd ^ μ x.fst = f n := by
  refine
      Iff.trans
        (Iff.trans (forall_congr' fun n => ?_)
          (@prod_eq_iff_prod_pow_moebius_eq Rˣ _
            (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1) fun n =>
            if h : 0 < n then Units.mk0 (g n) (hg n h) else 1))
        (forall_congr' fun n => ?_) <;>
    refine imp_congr_right fun hn => ?_
  · rw [dif_pos hn, ← Units.val_inj, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (pos_of_mem_divisors hx)]; rw [Units.coeHom_apply]; rw [Units.val_mk0]
  · rw [dif_pos hn, ← Units.val_inj, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (pos_of_mem_divisors (snd_mem_divisors_of_mem_antidiagonal hx))]; rw [Units.coeHom_apply]; rw [Units.val_zpow_eq_zpow_val]; rw [Units.val_mk0]

/--
theorem `sum_eq_iff_sum_smul_moebius_eq_on` / 定理 `sum_eq_iff_sum_smul_moebius_eq_on`

English:
theorem sum_eq_iff_sum_smul_moebius_eq_on
  statement: [AddCommGroup R] {f g : Nat -> R}
  proof: by
  constructor
  · intro h
    let G := fun (n : Nat) => (∑ i in n.divisors, f i)
    intro n hn hnP
    suffices ∑ d in n.divisors, μ (n / d) • G d = f n by
      rw [sum_divisorsAntidiagonal' (f := fun x y => μ x • g y)]; rw [← this]; rw [sum_congr rfl]
      intro d hd
      rw [← h d (pos_of_m

中文:
定理 sum_eq_iff_sum_smul_moebius_eq_on
  结论: [加法交换群 R] {f g : 自然数 -> R}
  证明: by
  constructor
  · intro h
    let G := fun (n : Nat) => (∑ i in n.divisors, f i)
    intro n hn hnP
    suffices ∑ d in n.divisors, μ (n / d) • G d = f n by
      rw [sum_divisorsAntidiagonal' (f := fun x y => μ x • g y)]; rw [← this]; rw [sum_congr rfl]
      intro d hd
      rw [← h d (pos_of_m

Depends on / 依赖: divisors, divisorsAn, dvd_of_mem_divisors, n.divisors, n.divisorsAn, pos_of_mem_divisors, sum_congr, sum_divisorsAntidiagonal, sum_eq_iff_sum_smul_moebius_eq, sum_eq_iff_sum_smul_moebius_eq.mp
-/
theorem sum_eq_iff_sum_smul_moebius_eq_on [AddCommGroup R] {f g : Nat -> R}
    (s : Set Nat) (hs : forall m n, m ∣ n -> n in s -> m in s) :
    (forall n > 0, n in s -> (∑ i in n.divisors, f i) = g n) ↔
      forall n > 0, n in s -> (∑ x in n.divisorsAntidiagonal, μ x.fst • g x.snd) = f n := by
  constructor
  · intro h
    let G := fun (n : Nat) => (∑ i in n.divisors, f i)
    intro n hn hnP
    suffices ∑ d in n.divisors, μ (n / d) • G d = f n by
      rw [sum_divisorsAntidiagonal' (f := fun x y => μ x • g y)]; rw [← this]; rw [sum_congr rfl]
      intro d hd
      rw [← h d (pos_of_mem_divisors hd) <| hs d n (dvd_of_mem_divisors hd) hnP]
    rw [← sum_divisorsAntidiagonal' (f := fun x y => μ x • G y)]
    apply sum_eq_iff_sum_smul_moebius_eq.mp _ n hn
    intro _ _; rfl
  · intro h
    let F := fun (n : Nat) => ∑ x in n.divisorsAntidiagonal, μ x.fst • g x.snd
    intro n hn hnP
    suffices ∑ d in n.divisors, F d = g n by
      rw [← this]; rw [sum_congr rfl]
      intro d hd
      rw [← h d (pos_of_mem_divisors hd) <| hs d n (dvd_of_mem_divisors hd) hnP]
    apply sum_eq_iff_sum_smul_moebius_eq.mpr _ n hn
    intro _ _; rfl

/--
theorem `sum_eq_iff_sum_smul_moebius_eq_on'` / 定理 `sum_eq_iff_sum_smul_moebius_eq_on'`

English:
theorem sum_eq_iff_sum_smul_moebius_eq_on'
  statement: [AddCommGroup R] {f g : Nat -> R}
  proof: by
  have : forall P : Nat -> Prop, ((forall n in s, P n) ↔ (forall n > 0, n in s -> P n)) := fun P => by
    refine forall_congr' (fun n => ⟨fun h _ => h, fun h hn => h ?_ hn⟩)
    contrapose! hs₀
    simpa [nonpos_iff_eq_zero.mp hs₀] using hn
  simpa only [this] using sum_eq_iff_sum_smul_moebius_e

中文:
定理 sum_eq_iff_sum_smul_moebius_eq_on'
  结论: [加法交换群 R] {f g : 自然数 -> R}
  证明: by
  have : forall P : Nat -> Prop, ((forall n in s, P n) ↔ (forall n > 0, n in s -> P n)) := fun P => by
    refine forall_congr' (fun n => ⟨fun h _ => h, fun h hn => h ?_ hn⟩)
    contrapose! hs₀
    simpa [nonpos_iff_eq_zero.mp hs₀] using hn
  simpa only [this] using sum_eq_iff_sum_smul_moebius_e

Depends on / 依赖: contrapose, forall_congr, nonpos_iff_eq_zero, nonpos_iff_eq_zero.mp, sum_eq_iff_sum_smul_moebius_eq_on
-/
theorem sum_eq_iff_sum_smul_moebius_eq_on' [AddCommGroup R] {f g : Nat -> R}
    (s : Set Nat) (hs : forall m n, m ∣ n -> n in s -> m in s) (hs₀ : 0 ∉ s) :
    (forall n in s, (∑ i in n.divisors, f i) = g n) ↔
     forall n in s, (∑ x in n.divisorsAntidiagonal, μ x.fst • g x.snd) = f n := by
  have : forall P : Nat -> Prop, ((forall n in s, P n) ↔ (forall n > 0, n in s -> P n)) := fun P => by
    refine forall_congr' (fun n => ⟨fun h _ => h, fun h hn => h ?_ hn⟩)
    contrapose! hs₀
    simpa [nonpos_iff_eq_zero.mp hs₀] using hn
  simpa only [this] using sum_eq_iff_sum_smul_moebius_eq_on s hs

/--
theorem `sum_eq_iff_sum_mul_moebius_eq_on` / 定理 `sum_eq_iff_sum_mul_moebius_eq_on`

English:
theorem sum_eq_iff_sum_mul_moebius_eq_on
  statement: [NonAssocRing R] {f g : Nat -> R}
  proof: by
  rw [sum_eq_iff_sum_smul_moebius_eq_on s hs]
  apply forall_congr'
  intro a; refine imp_congr_right ?_
  refine fun _ => imp_congr_right fun _ => (sum_congr rfl fun x _hx => ?_).congr_left
  rw [zsmul_eq_mul]

中文:
定理 sum_eq_iff_sum_mul_moebius_eq_on
  结论: [非结合环 R] {f g : 自然数 -> R}
  证明: by
  rw [sum_eq_iff_sum_smul_moebius_eq_on s hs]
  apply forall_congr'
  intro a; refine imp_congr_right ?_
  refine fun _ => imp_congr_right fun _ => (sum_congr rfl fun x _hx => ?_).congr_left
  rw [zsmul_eq_mul]

Depends on / 依赖: congr_left, forall_congr, imp_congr_right, sum_congr, sum_eq_iff_sum_smul_moebius_eq_on, zsmul_eq_mul
-/
theorem sum_eq_iff_sum_mul_moebius_eq_on [NonAssocRing R] {f g : Nat -> R}
    (s : Set Nat) (hs : forall m n, m ∣ n -> n in s -> m in s) :
    (forall n > 0, n in s -> (∑ i in n.divisors, f i) = g n) ↔
      forall n > 0, n in s ->
        (∑ x in n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd) = f n := by
  rw [sum_eq_iff_sum_smul_moebius_eq_on s hs]
  apply forall_congr'
  intro a; refine imp_congr_right ?_
  refine fun _ => imp_congr_right fun _ => (sum_congr rfl fun x _hx => ?_).congr_left
  rw [zsmul_eq_mul]

/--
theorem `prod_eq_iff_prod_pow_moebius_eq_on` / 定理 `prod_eq_iff_prod_pow_moebius_eq_on`

English:
theorem prod_eq_iff_prod_pow_moebius_eq_on
  statement: [CommGroup R] {f g : Nat -> R}
  proof: @sum_eq_iff_sum_smul_moebius_eq_on (Additive R) _ _ _ s hs

中文:
定理 prod_eq_iff_prod_pow_moebius_eq_on
  结论: [交换群 R] {f g : 自然数 -> R}
  证明: @sum_eq_iff_sum_smul_moebius_eq_on (Additive R) _ _ _ s hs

Depends on / 依赖: Additive, sum_eq_iff_sum_smul_moebius_eq_on
-/
theorem prod_eq_iff_prod_pow_moebius_eq_on [CommGroup R] {f g : Nat -> R}
    (s : Set Nat) (hs : forall m n, m ∣ n -> n in s -> m in s) :
    (forall n > 0, n in s -> (∏ i in n.divisors, f i) = g n) ↔
      forall n > 0, n in s -> (∏ x in n.divisorsAntidiagonal, g x.snd ^ μ x.fst) = f n :=
  @sum_eq_iff_sum_smul_moebius_eq_on (Additive R) _ _ _ s hs

/--
theorem `prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero` / 定理 `prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero`

English:
theorem prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero
  statement: [CommGroupWithZero R]
  proof: by
  refine
      Iff.trans
        (Iff.trans (forall_congr' fun n => ?_)
          (@prod_eq_iff_prod_pow_moebius_eq_on Rˣ _
            (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1)
            (fun n => if h : 0 < n then Units.mk0 (g n) (hg n h) else 1)
            s hs))
        

中文:
定理 prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero
  结论: [带零交换群 R]
  证明: by
  refine
      Iff.trans
        (Iff.trans (forall_congr' fun n => ?_)
          (@prod_eq_iff_prod_pow_moebius_eq_on Rˣ _
            (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1)
            (fun n => if h : 0 < n then Units.mk0 (g n) (hg n h) else 1)
            s hs))
        

Depends on / 依赖: Iff.trans, Units.coeHom_apply, Units.mk0, Units.val_inj, Units.val_mk0, coeHom_apply, dif_pos, forall_congr, imp_congr_right, map_prod, pos_of_mem_divisors, prod_congr, prod_eq_iff_prod_pow_moebius_eq_on, val_inj, val_mk0
-/
theorem prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero [CommGroupWithZero R]
    (s : Set Nat) (hs : forall m n, m ∣ n -> n in s -> m in s) {f g : Nat -> R}
    (hf : forall n > 0, f n != 0) (hg : forall n > 0, g n != 0) :
    (forall n > 0, n in s -> (∏ i in n.divisors, f i) = g n) ↔
      forall n > 0, n in s -> (∏ x in n.divisorsAntidiagonal, g x.snd ^ μ x.fst) = f n := by
  refine
      Iff.trans
        (Iff.trans (forall_congr' fun n => ?_)
          (@prod_eq_iff_prod_pow_moebius_eq_on Rˣ _
            (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1)
            (fun n => if h : 0 < n then Units.mk0 (g n) (hg n h) else 1)
            s hs))
        (forall_congr' fun n => ?_) <;>
    refine imp_congr_right fun hn => ?_
  · rw [dif_pos hn, ← Units.val_inj, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (pos_of_mem_divisors hx)]; rw [Units.coeHom_apply]; rw [Units.val_mk0]
  · rw [dif_pos hn, ← Units.val_inj, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (pos_of_mem_divisors (snd_mem_divisors_of_mem_antidiagonal hx))]; rw [Units.coeHom_apply]; rw [Units.val_zpow_eq_zpow_val]; rw [Units.val_mk0]

end ArithmeticFunction
