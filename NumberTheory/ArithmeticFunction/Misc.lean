/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.Data.Nat.Factorization.PrimePow
/-!
# Miscellaneous arithmetic Functions

This file defines some simple examples of arithmetic functions (functions `ℕ → R` vanishing at
`0`, considered as a ring under Dirichlet convolution). Note that the Von Mangoldt and Möbius
functions are in separate files.

## Main Definitions

* `σ k` is the arithmetic function such that `σ k x = ∑ y ∈ divisors x, y ^ k` for `0 < x`.
* `pow k` is the arithmetic function such that `pow k x = x ^ k` for `0 < x`.
* `id` is the identity arithmetic function on `ℕ`.
* `ω n` is the number of distinct prime factors of `n`.
* `Ω n` is the number of prime factors of `n` counted with multiplicity.

## Notation

The arithmetic functions `σ`, `ω` and `Ω` have Greek letter names.
This notation is scoped to the separate locales `ArithmeticFunction.sigma` for `σ`,
`ArithmeticFunction.omega` for `ω` and `ArithmeticFunction.Omega` for `Ω`, to allow for selective
access.

## Tags

arithmetic functions, dirichlet convolution, divisors

-/

@[expose] public section

open Finset Nat

variable {R : Type*}

namespace ArithmeticFunction

section SpecialFunctions

open scoped zeta

section ProdPrimeFactors

/--
Definition of `prodPrimeFactors` / `prodPrimeFactors` 的定义

English:
definition prodPrimeFactors
  signature: [CommMonoidWithZero R] (f : Nat -> R)
  body: if d = 0 then 0 else ∏ p in d.primeFactors, f p
  map_zero' := if_pos rfl

中文:
定义 prodPrimeFactors
  签名: [带零交换幺半群 R] (f : 自然数 -> R)
  定义体: if d = 0 then 0 else ∏ p in d.primeFactors, f p
  map_zero' := if_pos rfl

Depends on / 依赖: d.primeFactors, primeFactors
-/
def prodPrimeFactors [CommMonoidWithZero R] (f : Nat -> R) : ArithmeticFunction R where
  toFun d := if d = 0 then 0 else ∏ p in d.primeFactors, f p
  map_zero' := if_pos rfl

open Batteries.ExtendedBinder

/-- `∏ᵖ p ∣ n, f p` is custom notation for `prodPrimeFactors f n` -/
scoped syntax (name := bigproddvd) "∏ᵖ " extBinder " ∣ " term ", " term:67 : term
scoped macro_rules (kind := bigproddvd)
  | `(∏ᵖ $x:ident ∣ $n, $r) => `(prodPrimeFactors (fun $x => $r) $n)

@[simp]
/--
theorem `prodPrimeFactors_apply` / 定理 `prodPrimeFactors_apply`

English:
theorem prodPrimeFactors_apply
  given: [CommMonoidWithZero R] {f : Nat -> R} {n : Nat} (hn : n != 0)
  proof: if_neg hn

中文:
定理 prodPrimeFactors_apply
  条件: [带零交换幺半群 R] {f : 自然数 -> R} {n : 自然数} (hn : n != 0)
  证明: if_neg hn

Depends on / 依赖: if_neg
-/
theorem prodPrimeFactors_apply [CommMonoidWithZero R] {f : Nat -> R} {n : Nat} (hn : n != 0) :
    ∏ᵖ p ∣ n, f p = ∏ p in n.primeFactors, f p :=
  if_neg hn

namespace IsMultiplicative

@[arith_mult]
/--
theorem `prodPrimeFactors` / 定理 `prodPrimeFactors`

English:
theorem prodPrimeFactors
  given: [CommMonoidWithZero R] (f : Nat -> R)
  proof: by
  rw [iff_ne_zero]
  simp only [ne_eq, one_ne_zero, not_false_eq_true, prodPrimeFactors_apply, primeFactors_one,
    prod_empty, true_and]
  intro x y hx hy hxy
  have hxy₀ : x * y != 0 := mul_ne_zero hx hy
  rw [prodPrimeFactors_apply hxy₀]; rw [prodPrimeFactors_apply hx]; rw [prodPrimeFactors_a

中文:
定理 prodPrimeFactors
  条件: [带零交换幺半群 R] (f : 自然数 -> R)
  证明: by
  rw [iff_ne_zero]
  simp only [ne_eq, one_ne_zero, not_false_eq_true, prodPrimeFactors_apply, primeFactors_one,
    prod_empty, true_and]
  intro x y hx hy hxy
  have hxy₀ : x * y != 0 := mul_ne_zero hx hy
  rw [prodPrimeFactors_apply hxy₀]; rw [prodPrimeFactors_apply hx]; rw [prodPrimeFactors_a

Depends on / 依赖: disjoint_primeFactors, hxy.disjoint_primeFactors, iff_ne_zero, mul_ne_zero, ne_eq, not_false_eq_true, one_ne_zero, primeFactors_mul, primeFactors_one, prodPrimeFactors_apply, prod_empty, prod_union, true_and
-/
theorem prodPrimeFactors [CommMonoidWithZero R] (f : Nat -> R) :
    IsMultiplicative (prodPrimeFactors f) := by
  rw [iff_ne_zero]
  simp only [ne_eq, one_ne_zero, not_false_eq_true, prodPrimeFactors_apply, primeFactors_one,
    prod_empty, true_and]
  intro x y hx hy hxy
  have hxy₀ : x * y != 0 := mul_ne_zero hx hy
  rw [prodPrimeFactors_apply hxy₀]; rw [prodPrimeFactors_apply hx]; rw [prodPrimeFactors_apply hy]; rw [primeFactors_mul hx hy]; rw [← prod_union hxy.disjoint_primeFactors]

/--
theorem `prodPrimeFactors_add_of_squarefree` / 定理 `prodPrimeFactors_add_of_squarefree`

English:
theorem prodPrimeFactors_add_of_squarefree
  statement: [CommSemiring R] {f g : ArithmeticFunction R}
  proof: by
  rw [prodPrimeFactors_apply hn.ne_zero]
  simp_rw [add_apply (f := f) (g := g)]
  rw [prod_add]; rw [mul_apply]; rw [sum_divisorsAntidiagonal (f · * g ·)]; rw [← divisors_filter_squarefree_of_squarefree hn]; rw [sum_divisors_filter_squarefree hn.ne_zero]; rw [factors_eq]
  apply sum_congr rfl
  

中文:
定理 prodPrimeFactors_add_of_squarefree
  结论: [交换半环 R] {f g : ArithmeticFunction R}
  证明: by
  rw [prodPrimeFactors_apply hn.ne_zero]
  simp_rw [add_apply (f := f) (g := g)]
  rw [prod_add]; rw [mul_apply]; rw [sum_divisorsAntidiagonal (f · * g ·)]; rw [← divisors_filter_squarefree_of_squarefree hn]; rw [sum_divisors_filter_squarefree hn.ne_zero]; rw [factors_eq]
  apply sum_congr rfl
  

Depends on / 依赖: Function, Function.id_def, add_apply, divisors_filter_squarefree_of_squarefree, factors_eq, hf.map_prod_of_subset_primeFactors, hg.map_prod_of_sub, hn.ne_zero, id_def, map_prod_of_sub, map_prod_of_subset_primeFactors, mem_powerset, mem_powerset.mp, mul_apply, ne_zero, prodPrimeFactors_apply, prod_add, prod_primeFactors_sdiff_of_squarefree, prod_val, simp_rw
-/
theorem prodPrimeFactors_add_of_squarefree [CommSemiring R] {f g : ArithmeticFunction R}
    (hf : IsMultiplicative f) (hg : IsMultiplicative g) {n : Nat} (hn : Squarefree n) :
    ∏ᵖ p ∣ n, (f + g) p = (f * g) n := by
  rw [prodPrimeFactors_apply hn.ne_zero]
  simp_rw [add_apply (f := f) (g := g)]
  rw [prod_add]; rw [mul_apply]; rw [sum_divisorsAntidiagonal (f · * g ·)]; rw [← divisors_filter_squarefree_of_squarefree hn]; rw [sum_divisors_filter_squarefree hn.ne_zero]; rw [factors_eq]
  apply sum_congr rfl
  intro t ht
  rw [t.prod_val]; rw [Function.id_def]; rw [← prod_primeFactors_sdiff_of_squarefree hn (mem_powerset.mp ht)]; rw [hf.map_prod_of_subset_primeFactors n t (mem_powerset.mp ht)]; rw [← hg.map_prod_of_subset_primeFactors n (_ \ t) sdiff_subset]

end IsMultiplicative

end ProdPrimeFactors

section Id

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : ArithmeticFunction Nat
  body: ⟨id, rfl⟩

@[simp]

中文:
定义 id
  签名: : ArithmeticFunction 自然数
  定义体: ⟨id, rfl⟩

@[simp]
-/
protected def id : ArithmeticFunction Nat :=
  ⟨id, rfl⟩

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: {x : Nat}
  statement: ArithmeticFunction.id x = x
  proof: rfl

@[arith_mult]

中文:
定理 id_apply
  条件: {x : 自然数}
  结论: ArithmeticFunction.id x = x
  证明: rfl

@[arith_mult]
-/
theorem id_apply {x : Nat} : ArithmeticFunction.id x = x :=
  rfl

@[arith_mult]
/--
theorem `isMultiplicative_id` / 定理 `isMultiplicative_id`

English:
theorem isMultiplicative_id
  statement: IsMultiplicative .id
  proof: ⟨rfl, fun _ => rfl⟩

中文:
定理 isMultiplicative_id
  结论: 是Multiplicative .id
  证明: ⟨rfl, fun _ => rfl⟩
-/
theorem isMultiplicative_id : IsMultiplicative .id :=
  ⟨rfl, fun _ => rfl⟩

end Id

section Pow

/--
Definition of `pow` / `pow` 的定义

English:
definition pow
  signature: (k : Nat)
  body: ArithmeticFunction.id.ppow k

@[simp]

中文:
定义 pow
  签名: (k : 自然数)
  定义体: ArithmeticFunction.id.ppow k

@[simp]

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.id.ppow
-/
def pow (k : Nat) : ArithmeticFunction Nat :=
  ArithmeticFunction.id.ppow k

@[simp]
/--
theorem `pow_apply` / 定理 `pow_apply`

English:
theorem pow_apply
  given: {k n : Nat}
  statement: pow k n = if k = 0 ∧ n = 0 then 0 else n ^ k
  proof: by
  cases k <;> simp [pow]

中文:
定理 pow_apply
  条件: {k n : 自然数}
  结论: pow k n = if k = 0 ∧ n = 0 then 0 else n ^ k
  证明: by
  cases k <;> simp [pow]
-/
theorem pow_apply {k n : Nat} : pow k n = if k = 0 ∧ n = 0 then 0 else n ^ k := by
  cases k <;> simp [pow]

/--
theorem `pow_zero_eq_zeta` / 定理 `pow_zero_eq_zeta`

English:
theorem pow_zero_eq_zeta
  statement: pow 0 = ζ
  proof: by
  ext n
  simp

中文:
定理 pow_zero_eq_zeta
  结论: pow 0 = ζ
  证明: by
  ext n
  simp
-/
theorem pow_zero_eq_zeta : pow 0 = ζ := by
  ext n
  simp

/--
theorem `pow_one_eq_id` / 定理 `pow_one_eq_id`

English:
theorem pow_one_eq_id
  statement: pow 1 = .id
  proof: by
  ext n
  simp

@[arith_mult]

中文:
定理 pow_one_eq_id
  结论: pow 1 = .id
  证明: by
  ext n
  simp

@[arith_mult]
-/
theorem pow_one_eq_id : pow 1 = .id := by
  ext n
  simp

@[arith_mult]
/--
theorem `isMultiplicative_pow` / 定理 `isMultiplicative_pow`

English:
theorem isMultiplicative_pow
  given: {k : Nat}
  statement: IsMultiplicative (pow k)
  proof: isMultiplicative_id.ppow

中文:
定理 isMultiplicative_pow
  条件: {k : 自然数}
  结论: 是Multiplicative (pow k)
  证明: isMultiplicative_id.ppow

Depends on / 依赖: isMultiplicative_id, isMultiplicative_id.ppow
-/
theorem isMultiplicative_pow {k : Nat} : IsMultiplicative (pow k) :=
  isMultiplicative_id.ppow
end Pow

section Sigma

/--
Definition of `sigma` / `sigma` 的定义

English:
definition sigma
  signature: (k : Nat)
  body: ⟨fun n => ∑ d in divisors n, d ^ k, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.sigma] notation "σ" => ArithmeticFunction.sigma

中文:
定义 sigma
  签名: (k : 自然数)
  定义体: ⟨fun n => ∑ d in divisors n, d ^ k, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.sigma] notation "σ" => ArithmeticFunction.sigma

Depends on / 依赖: divisors
-/
def sigma (k : Nat) : ArithmeticFunction Nat :=
  ⟨fun n => ∑ d in divisors n, d ^ k, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.sigma] notation "σ" => ArithmeticFunction.sigma

open scoped sigma

/--
theorem `sigma_apply` / 定理 `sigma_apply`

English:
theorem sigma_apply
  given: {k n : Nat}
  statement: σ k n = ∑ d in divisors n, d ^ k
  proof: rfl

@[simp]

中文:
定理 sigma_apply
  条件: {k n : 自然数}
  结论: σ k n = ∑ d in divisors n, d ^ k
  证明: rfl

@[simp]
-/
theorem sigma_apply {k n : Nat} : σ k n = ∑ d in divisors n, d ^ k :=
  rfl

@[simp]
/--
theorem `sigma_eq_zero` / 定理 `sigma_eq_zero`

English:
theorem sigma_eq_zero
  given: {k n : Nat}
  statement: σ k n = 0 ↔ n = 0
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [ArithmeticFunction.sigma_apply]
    aesop

@[simp]

中文:
定理 sigma_eq_zero
  条件: {k n : 自然数}
  结论: σ k n = 0 ↔ n = 0
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [ArithmeticFunction.sigma_apply]
    aesop

@[simp]

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.sigma_apply, eq_or_ne, sigma_apply
-/
theorem sigma_eq_zero {k n : Nat} : σ k n = 0 ↔ n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [ArithmeticFunction.sigma_apply]
    aesop

@[simp]
/--
theorem `sigma_pos_iff` / 定理 `sigma_pos_iff`

English:
theorem sigma_pos_iff
  given: {k n}
  statement: 0 < σ k n ↔ 0 < n
  proof: by
  simp [pos_iff_ne_zero]

中文:
定理 sigma_pos_iff
  条件: {k n}
  结论: 0 < σ k n ↔ 0 < n
  证明: by
  simp [pos_iff_ne_zero]

Depends on / 依赖: pos_iff_ne_zero
-/
theorem sigma_pos_iff {k n} : 0 < σ k n ↔ 0 < n := by
  simp [pos_iff_ne_zero]

/--
theorem `sigma_apply_prime_pow` / 定理 `sigma_apply_prime_pow`

English:
theorem sigma_apply_prime_pow
  given: {k p i : Nat} (hp : p.Prime)
  proof: by
  simp [sigma_apply, divisors_prime_pow hp, pow_mul]

中文:
定理 sigma_apply_prime_pow
  条件: {k p i : 自然数} (hp : p.素)
  证明: by
  simp [sigma_apply, divisors_prime_pow hp, pow_mul]

Depends on / 依赖: divisors_prime_pow, pow_mul, sigma_apply
-/
theorem sigma_apply_prime_pow {k p i : Nat} (hp : p.Prime) :
    σ k (p ^ i) = ∑ j in .range (i + 1), p ^ (j * k) := by
  simp [sigma_apply, divisors_prime_pow hp, pow_mul]

/--
theorem `sigma_one_apply` / 定理 `sigma_one_apply`

English:
theorem sigma_one_apply
  given: (n : Nat)
  statement: σ 1 n = ∑ d in divisors n, d
  proof: by simp [sigma_apply]

中文:
定理 sigma_one_apply
  条件: (n : 自然数)
  结论: σ 1 n = ∑ d in divisors n, d
  证明: by simp [sigma_apply]

Depends on / 依赖: sigma_apply
-/
theorem sigma_one_apply (n : Nat) : σ 1 n = ∑ d in divisors n, d := by simp [sigma_apply]

/--
theorem `sigma_one_apply_prime_pow` / 定理 `sigma_one_apply_prime_pow`

English:
theorem sigma_one_apply_prime_pow
  given: {p i : Nat} (hp : p.Prime)
  proof: by
  simp [sigma_apply_prime_pow hp]

中文:
定理 sigma_one_apply_prime_pow
  条件: {p i : 自然数} (hp : p.素)
  证明: by
  simp [sigma_apply_prime_pow hp]

Depends on / 依赖: sigma_apply_prime_pow
-/
theorem sigma_one_apply_prime_pow {p i : Nat} (hp : p.Prime) :
    σ 1 (p ^ i) = ∑ k in .range (i + 1), p ^ k := by
  simp [sigma_apply_prime_pow hp]

/--
theorem `sigma_eq_sum_div` / 定理 `sigma_eq_sum_div`

English:
theorem sigma_eq_sum_div
  given: (k n : Nat)
  statement: sigma k n = ∑ d in divisors n, (n / d) ^ k
  proof: by
  rw [sigma_apply]; rw [← sum_div_divisors]

中文:
定理 sigma_eq_sum_div
  条件: (k n : 自然数)
  结论: sigma k n = ∑ d in divisors n, (n / d) ^ k
  证明: by
  rw [sigma_apply]; rw [← sum_div_divisors]

Depends on / 依赖: sigma_apply, sum_div_divisors
-/
theorem sigma_eq_sum_div (k n : Nat) : sigma k n = ∑ d in divisors n, (n / d) ^ k := by
  rw [sigma_apply]; rw [← sum_div_divisors]

/--
theorem `sigma_zero_apply` / 定理 `sigma_zero_apply`

English:
theorem sigma_zero_apply
  given: (n : Nat)
  statement: σ 0 n = #n.divisors
  proof: by simp [sigma_apply]

中文:
定理 sigma_zero_apply
  条件: (n : 自然数)
  结论: σ 0 n = #n.divisors
  证明: by simp [sigma_apply]

Depends on / 依赖: sigma_apply
-/
theorem sigma_zero_apply (n : Nat) : σ 0 n = #n.divisors := by simp [sigma_apply]

/--
theorem `sigma_zero_apply_prime_pow` / 定理 `sigma_zero_apply_prime_pow`

English:
theorem sigma_zero_apply_prime_pow
  given: {p i : Nat} (hp : p.Prime)
  statement: σ 0 (p ^ i) = i + 1
  proof: by
  simp [sigma_apply_prime_pow hp]

@[simp]

中文:
定理 sigma_zero_apply_prime_pow
  条件: {p i : 自然数} (hp : p.素)
  结论: σ 0 (p ^ i) = i + 1
  证明: by
  simp [sigma_apply_prime_pow hp]

@[simp]

Depends on / 依赖: sigma_apply_prime_pow
-/
theorem sigma_zero_apply_prime_pow {p i : Nat} (hp : p.Prime) : σ 0 (p ^ i) = i + 1 := by
  simp [sigma_apply_prime_pow hp]

@[simp]
/--
theorem `sigma_one` / 定理 `sigma_one`

English:
theorem sigma_one
  given: (k : Nat)
  statement: σ k 1 = 1
  proof: by
  simp only [sigma_apply, divisors_one, sum_singleton, one_pow]

中文:
定理 sigma_one
  条件: (k : 自然数)
  结论: σ k 1 = 1
  证明: by
  simp only [sigma_apply, divisors_one, sum_singleton, one_pow]

Depends on / 依赖: divisors_one, one_pow, sigma_apply, sum_singleton
-/
theorem sigma_one (k : Nat) : σ k 1 = 1 := by
  simp only [sigma_apply, divisors_one, sum_singleton, one_pow]

/--
theorem `sigma_pos` / 定理 `sigma_pos`

English:
theorem sigma_pos
  given: (k n : Nat) (hn0 : n != 0)
  statement: 0 < σ k n
  proof: by
  rwa [sigma_pos_iff, pos_iff_ne_zero]

中文:
定理 sigma_pos
  条件: (k n : 自然数) (hn0 : n != 0)
  结论: 0 < σ k n
  证明: by
  rwa [sigma_pos_iff, pos_iff_ne_zero]

Depends on / 依赖: pos_iff_ne_zero, sigma_pos_iff
-/
theorem sigma_pos (k n : Nat) (hn0 : n != 0) : 0 < σ k n := by
  rwa [sigma_pos_iff, pos_iff_ne_zero]

/--
theorem `sigma_mono` / 定理 `sigma_mono`

English:
theorem sigma_mono
  given: (k k' n : Nat) (hk : k <= k')
  statement: σ k n <= σ k' n
  proof: by
  simp_rw [sigma_apply]
  gcongr with d hd
  exact pos_of_mem_divisors hd

中文:
定理 sigma_mono
  条件: (k k' n : 自然数) (hk : k <= k')
  结论: σ k n <= σ k' n
  证明: by
  simp_rw [sigma_apply]
  gcongr with d hd
  exact pos_of_mem_divisors hd

Depends on / 依赖: pos_of_mem_divisors, sigma_apply, simp_rw
-/
theorem sigma_mono (k k' n : Nat) (hk : k <= k') : σ k n <= σ k' n := by
  simp_rw [sigma_apply]
  gcongr with d hd
  exact pos_of_mem_divisors hd

/--
theorem `zeta_mul_pow_eq_sigma` / 定理 `zeta_mul_pow_eq_sigma`

English:
theorem zeta_mul_pow_eq_sigma
  given: {k : Nat}
  statement: ζ * pow k = σ k
  proof: by
  ext
  rw [sigma]; rw [zeta_mul_apply]
  apply sum_congr rfl
  aesop

@[arith_mult]

中文:
定理 zeta_mul_pow_eq_sigma
  条件: {k : 自然数}
  结论: ζ * pow k = σ k
  证明: by
  ext
  rw [sigma]; rw [zeta_mul_apply]
  apply sum_congr rfl
  aesop

@[arith_mult]

Depends on / 依赖: sum_congr, zeta_mul_apply
-/
theorem zeta_mul_pow_eq_sigma {k : Nat} : ζ * pow k = σ k := by
  ext
  rw [sigma]; rw [zeta_mul_apply]
  apply sum_congr rfl
  aesop

@[arith_mult]
/--
theorem `isMultiplicative_sigma` / 定理 `isMultiplicative_sigma`

English:
theorem isMultiplicative_sigma
  given: {k : Nat}
  statement: IsMultiplicative (σ k)
  proof: by
  rw [← zeta_mul_pow_eq_sigma]
  apply isMultiplicative_zeta.mul isMultiplicative_pow

中文:
定理 isMultiplicative_sigma
  条件: {k : 自然数}
  结论: 是Multiplicative (σ k)
  证明: by
  rw [← zeta_mul_pow_eq_sigma]
  apply isMultiplicative_zeta.mul isMultiplicative_pow

Depends on / 依赖: isMultiplicative_pow, isMultiplicative_zeta, isMultiplicative_zeta.mul, zeta_mul_pow_eq_sigma
-/
theorem isMultiplicative_sigma {k : Nat} : IsMultiplicative (σ k) := by
  rw [← zeta_mul_pow_eq_sigma]
  apply isMultiplicative_zeta.mul isMultiplicative_pow

/--
theorem `sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul` / 定理 `sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul`

English:
theorem sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
  given: {k n : Nat} (hn : n != 0)
  proof: by
  rw [isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h =>
sigma_apply_prime_pow prime_of_mem_primeFactors h

中文:
定理 sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
  条件: {k n : 自然数} (hn : n != 0)
  证明: by
  rw [isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h =>
sigma_apply_prime_pow prime_of_mem_primeFactors h

Depends on / 依赖: isMultiplicative_sigma, isMultiplicative_sigma.multiplicative_factorization, multiplicative_factorization, n.support_factorization, prime_of_mem_primeFactors, prod_congr, sigma_apply_prime_pow, support_factorization
-/
theorem sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul {k n : Nat} (hn : n != 0) :
    σ k n = ∏ p in n.primeFactors, ∑ i in .range (n.factorization p + 1), p ^ (i * k) := by
  rw [isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h =>
sigma_apply_prime_pow prime_of_mem_primeFactors h

/--
theorem `sigma_le_pow_succ` / 定理 `sigma_le_pow_succ`

English:
theorem sigma_le_pow_succ
  given: (k n : Nat)
  statement: σ k n <= n ^ (k + 1)
  proof: by
  simp only [sigma_apply, pow_succ']
  refine (Finset.sum_le_sum fun d hd => Nat.pow_le_pow_left (Nat.divisor_le hd) k).trans ?_
  simpa [Finset.sum_const] using Nat.mul_le_mul_right (n ^ k) (Nat.card_divisors_le_self n)

中文:
定理 sigma_le_pow_succ
  条件: (k n : 自然数)
  结论: σ k n <= n ^ (k + 1)
  证明: by
  simp only [sigma_apply, pow_succ']
  refine (Finset.sum_le_sum fun d hd => Nat.pow_le_pow_left (Nat.divisor_le hd) k).trans ?_
  simpa [Finset.sum_const] using Nat.mul_le_mul_right (n ^ k) (Nat.card_divisors_le_self n)

Depends on / 依赖: Finset, Finset.sum_const, Finset.sum_le_sum, Nat.card_divisors_le_self, Nat.divisor_le, Nat.mul_le_mul_right, Nat.pow_le_pow_left, card_divisors_le_self, divisor_le, mul_le_mul_right, pow_le_pow_left, pow_succ, sigma_apply, sum_const, sum_le_sum
-/
theorem sigma_le_pow_succ (k n : Nat) : σ k n <= n ^ (k + 1) := by
  simp only [sigma_apply, pow_succ']
  refine (Finset.sum_le_sum fun d hd => Nat.pow_le_pow_left (Nat.divisor_le hd) k).trans ?_
  simpa [Finset.sum_const] using Nat.mul_le_mul_right (n ^ k) (Nat.card_divisors_le_self n)

end Sigma

open scoped sigma

/--
theorem `_root_.Nat.card_divisors` / 定理 `_root_.Nat.card_divisors`

English:
theorem _root_.Nat.card_divisors
  given: {n : Nat} (hn : n != 0)
  proof: by
  rw [← sigma_zero_apply]; rw [isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h =>
sigma_zero_apply_prime_pow prime_of_mem_primeFactors h

@[simp]

中文:
定理 _root_.自然数.card_divisors
  条件: {n : 自然数} (hn : n != 0)
  证明: by
  rw [← sigma_zero_apply]; rw [isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h =>
sigma_zero_apply_prime_pow prime_of_mem_primeFactors h

@[simp]

Depends on / 依赖: isMultiplicative_sigma, isMultiplicative_sigma.multiplicative_factorization, multiplicative_factorization, n.support_factorization, prime_of_mem_primeFactors, prod_congr, sigma_zero_apply, sigma_zero_apply_prime_pow, support_factorization
-/
theorem _root_.Nat.card_divisors {n : Nat} (hn : n != 0) :
    #n.divisors = n.primeFactors.prod (n.factorization · + 1) := by
  rw [← sigma_zero_apply]; rw [isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h =>
sigma_zero_apply_prime_pow prime_of_mem_primeFactors h

@[simp]
/--
theorem `_root_.Nat.divisors_card_eq_one_iff` / 定理 `_root_.Nat.divisors_card_eq_one_iff`

English:
theorem _root_.Nat.divisors_card_eq_one_iff
  given: (n : Nat)
  statement: #n.divisors = 1 ↔ n = 1
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · refine ⟨fun h => ?_, fun h => by simp [h]⟩
    exact (card_le_one.mp h.le 1 (one_mem_divisors.mpr hn) n (n.mem_divisors_self hn)).symm

中文:
定理 _root_.自然数.divisors_card_eq_one_iff
  条件: (n : 自然数)
  结论: #n.divisors = 1 ↔ n = 1
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · refine ⟨fun h => ?_, fun h => by simp [h]⟩
    exact (card_le_one.mp h.le 1 (one_mem_divisors.mpr hn) n (n.mem_divisors_self hn)).symm

Depends on / 依赖: card_le_one, card_le_one.mp, eq_or_ne, h.le, mem_divisors_self, n.mem_divisors_self, one_mem_divisors, one_mem_divisors.mpr
-/
theorem _root_.Nat.divisors_card_eq_one_iff (n : Nat) : #n.divisors = 1 ↔ n = 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · refine ⟨fun h => ?_, fun h => by simp [h]⟩
    exact (card_le_one.mp h.le 1 (one_mem_divisors.mpr hn) n (n.mem_divisors_self hn)).symm

/--
theorem `sigma_zero_eq_one_iff` / 定理 `sigma_zero_eq_one_iff`

English:
theorem sigma_zero_eq_one_iff
  given: (n : Nat)
  statement: σ 0 n = 1 ↔ n = 1
  proof: by
  simp [sigma_zero_apply]

@[simp]

中文:
定理 sigma_zero_eq_one_iff
  条件: (n : 自然数)
  结论: σ 0 n = 1 ↔ n = 1
  证明: by
  simp [sigma_zero_apply]

@[simp]
-/
private theorem sigma_zero_eq_one_iff (n : Nat) : σ 0 n = 1 ↔ n = 1 := by
  simp [sigma_zero_apply]

@[simp]
/--
theorem `sigma_eq_one_iff` / 定理 `sigma_eq_one_iff`

English:
theorem sigma_eq_one_iff
  given: (k n : Nat)
  statement: σ k n = 1 ↔ n = 1
  proof: by
  by_cases hn0 : n = 0
  · aesop
  constructor
  · intro h
    rw [← sigma_zero_eq_one_iff]
    have zero_lt_sigma := sigma_pos 0 n hn0
    have sigma_zero_le_sigma := sigma_mono 0 k n k.zero_le
    lia
  · simp +contextual

中文:
定理 sigma_eq_one_iff
  条件: (k n : 自然数)
  结论: σ k n = 1 ↔ n = 1
  证明: by
  by_cases hn0 : n = 0
  · aesop
  constructor
  · intro h
    rw [← sigma_zero_eq_one_iff]
    have zero_lt_sigma := sigma_pos 0 n hn0
    have sigma_zero_le_sigma := sigma_mono 0 k n k.zero_le
    lia
  · simp +contextual

Depends on / 依赖: contextual, k.zero_le, sigma_mono, sigma_pos, sigma_zero_eq_one_iff, sigma_zero_le_sigma, zero_le, zero_lt_sigma
-/
theorem sigma_eq_one_iff (k n : Nat) : σ k n = 1 ↔ n = 1 := by
  by_cases hn0 : n = 0
  · aesop
  constructor
  · intro h
    rw [← sigma_zero_eq_one_iff]
    have zero_lt_sigma := sigma_pos 0 n hn0
    have sigma_zero_le_sigma := sigma_mono 0 k n k.zero_le
    lia
  · simp +contextual

/--
theorem `_root_.Nat.sum_divisors` / 定理 `_root_.Nat.sum_divisors`

English:
theorem _root_.Nat.sum_divisors
  given: {n : Nat} (hn : n != 0)
  proof: by
  rw [← sigma_one_apply]; rw [isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h =>
sigma_one_apply_prime_pow prime_of_mem_primeFactors h

中文:
定理 _root_.自然数.sum_divisors
  条件: {n : 自然数} (hn : n != 0)
  证明: by
  rw [← sigma_one_apply]; rw [isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h =>
sigma_one_apply_prime_pow prime_of_mem_primeFactors h

Depends on / 依赖: isMultiplicative_sigma, isMultiplicative_sigma.multiplicative_factorization, multiplicative_factorization, n.support_factorization, prime_of_mem_primeFactors, prod_congr, sigma_one_apply, sigma_one_apply_prime_pow, support_factorization
-/
theorem _root_.Nat.sum_divisors {n : Nat} (hn : n != 0) :
    ∑ d in n.divisors, d = ∏ p in n.primeFactors, ∑ k in .range (n.factorization p + 1), p ^ k := by
  rw [← sigma_one_apply]; rw [isMultiplicative_sigma.multiplicative_factorization _ hn]
  exact prod_congr n.support_factorization fun _ h =>
sigma_one_apply_prime_pow prime_of_mem_primeFactors h

/--
Definition of `cardFactors` / `cardFactors` 的定义

English:
definition cardFactors
  signature: : ArithmeticFunction Nat
  body: ⟨fun n => n.primeFactorsList.length, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.Omega] notation "Ω" => ArithmeticFunction.cardFactors

中文:
定义 cardFactors
  签名: : ArithmeticFunction 自然数
  定义体: ⟨fun n => n.primeFactorsList.length, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.Omega] notation "Ω" => ArithmeticFunction.cardFactors

Depends on / 依赖: length, n.primeFactorsList.length, primeFactorsList
-/
def cardFactors : ArithmeticFunction Nat :=
  ⟨fun n => n.primeFactorsList.length, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.Omega] notation "Ω" => ArithmeticFunction.cardFactors

open scoped Omega

/--
theorem `cardFactors_apply` / 定理 `cardFactors_apply`

English:
theorem cardFactors_apply
  given: {n : Nat}
  statement: Ω n = n.primeFactorsList.length
  proof: rfl

中文:
定理 cardFactors_apply
  条件: {n : 自然数}
  结论: Ω n = n.primeFactorsList.length
  证明: rfl
-/
theorem cardFactors_apply {n : Nat} : Ω n = n.primeFactorsList.length :=
  rfl

/--
lemma `cardFactors_zero` / 引理 `cardFactors_zero`

English:
lemma cardFactors_zero
  statement: Ω 0 = 0
  proof: by simp

中文:
引理 cardFactors_zero
  结论: Ω 0 = 0
  证明: by simp
-/
lemma cardFactors_zero : Ω 0 = 0 := by simp

/--
theorem `cardFactors_one` / 定理 `cardFactors_one`

English:
theorem cardFactors_one
  statement: Ω 1 = 0
  proof: by simp [cardFactors_apply]

@[simp]

中文:
定理 cardFactors_one
  结论: Ω 1 = 0
  证明: by simp [cardFactors_apply]

@[simp]
-/
@[simp] theorem cardFactors_one : Ω 1 = 0 := by simp [cardFactors_apply]

@[simp]
/--
theorem `cardFactors_eq_zero_iff_eq_zero_or_one` / 定理 `cardFactors_eq_zero_iff_eq_zero_or_one`

English:
theorem cardFactors_eq_zero_iff_eq_zero_or_one
  given: {n : Nat}
  statement: Ω n = 0 ↔ n = 0 ∨ n = 1
  proof: by
  rw [cardFactors_apply]; rw [List.length_eq_zero_iff]; rw [primeFactorsList_eq_nil]

@[simp]

中文:
定理 cardFactors_eq_zero_iff_eq_zero_or_one
  条件: {n : 自然数}
  结论: Ω n = 0 ↔ n = 0 ∨ n = 1
  证明: by
  rw [cardFactors_apply]; rw [List.length_eq_zero_iff]; rw [primeFactorsList_eq_nil]

@[simp]

Depends on / 依赖: List.length_eq_zero_iff, cardFactors_apply, length_eq_zero_iff, primeFactorsList_eq_nil
-/
theorem cardFactors_eq_zero_iff_eq_zero_or_one {n : Nat} : Ω n = 0 ↔ n = 0 ∨ n = 1 := by
  rw [cardFactors_apply]; rw [List.length_eq_zero_iff]; rw [primeFactorsList_eq_nil]

@[simp]
/--
theorem `cardFactors_pos_iff_one_lt` / 定理 `cardFactors_pos_iff_one_lt`

English:
theorem cardFactors_pos_iff_one_lt
  given: {n : Nat}
  statement: 0 < Ω n ↔ 1 < n
  proof: by
  rw [cardFactors_apply]; rw [List.length_pos_iff]; rw [primeFactorsList_ne_nil]

@[simp]

中文:
定理 cardFactors_pos_iff_one_lt
  条件: {n : 自然数}
  结论: 0 < Ω n ↔ 1 < n
  证明: by
  rw [cardFactors_apply]; rw [List.length_pos_iff]; rw [primeFactorsList_ne_nil]

@[simp]

Depends on / 依赖: List.length_pos_iff, cardFactors_apply, length_pos_iff, primeFactorsList_ne_nil
-/
theorem cardFactors_pos_iff_one_lt {n : Nat} : 0 < Ω n ↔ 1 < n := by
  rw [cardFactors_apply]; rw [List.length_pos_iff]; rw [primeFactorsList_ne_nil]

@[simp]
/--
theorem `cardFactors_eq_one_iff_prime` / 定理 `cardFactors_eq_one_iff_prime`

English:
theorem cardFactors_eq_one_iff_prime
  given: {n : Nat}
  statement: Ω n = 1 ↔ n.Prime
  proof: by
  refine ⟨fun h => ?_, fun h => List.length_eq_one_iff.2 ⟨n, primeFactorsList_prime h⟩⟩
  cases n with | zero => simp at h | succ n =>
  rcases List.length_eq_one_iff.1 h with ⟨x, hx⟩
  rw [← prod_primeFactorsList n.add_one_ne_zero]; rw [hx]; rw [List.prod_singleton]
  apply prime_of_mem_primeFac

中文:
定理 cardFactors_eq_one_iff_prime
  条件: {n : 自然数}
  结论: Ω n = 1 ↔ n.素
  证明: by
  refine ⟨fun h => ?_, fun h => List.length_eq_one_iff.2 ⟨n, primeFactorsList_prime h⟩⟩
  cases n with | zero => simp at h | succ n =>
  rcases List.length_eq_one_iff.1 h with ⟨x, hx⟩
  rw [← prod_primeFactorsList n.add_one_ne_zero]; rw [hx]; rw [List.prod_singleton]
  apply prime_of_mem_primeFac

Depends on / 依赖: List.length_eq_one_iff, List.mem_singleton, List.prod_singleton, add_one_ne_zero, length_eq_one_iff, mem_singleton, n.add_one_ne_zero, primeFactorsList_prime, prime_of_mem_primeFactorsList, prod_primeFactorsList, prod_singleton
-/
theorem cardFactors_eq_one_iff_prime {n : Nat} : Ω n = 1 ↔ n.Prime := by
  refine ⟨fun h => ?_, fun h => List.length_eq_one_iff.2 ⟨n, primeFactorsList_prime h⟩⟩
  cases n with | zero => simp at h | succ n =>
  rcases List.length_eq_one_iff.1 h with ⟨x, hx⟩
  rw [← prod_primeFactorsList n.add_one_ne_zero]; rw [hx]; rw [List.prod_singleton]
  apply prime_of_mem_primeFactorsList
  rw [hx]; rw [List.mem_singleton]

/--
theorem `cardFactors_mul` / 定理 `cardFactors_mul`

English:
theorem cardFactors_mul
  given: {m n : Nat} (m0 : m != 0) (n0 : n != 0)
  statement: Ω (m * n) = Ω m + Ω n
  proof: by
  rw [cardFactors_apply]; rw [cardFactors_apply]; rw [cardFactors_apply]; rw [← Multiset.coe_card]; rw [← factors_eq]; rw [UniqueFactorizationMonoid.normalizedFactors_mul m0 n0]; rw [factors_eq]; rw [factors_eq]; rw [Multiset.card_add]; rw [Multiset.coe_card]; rw [Multiset.coe_card]

中文:
定理 cardFactors_mul
  条件: {m n : 自然数} (m0 : m != 0) (n0 : n != 0)
  结论: Ω (m * n) = Ω m + Ω n
  证明: by
  rw [cardFactors_apply]; rw [cardFactors_apply]; rw [cardFactors_apply]; rw [← Multiset.coe_card]; rw [← factors_eq]; rw [UniqueFactorizationMonoid.normalizedFactors_mul m0 n0]; rw [factors_eq]; rw [factors_eq]; rw [Multiset.card_add]; rw [Multiset.coe_card]; rw [Multiset.coe_card]

Depends on / 依赖: Multiset, Multiset.card_add, Multiset.coe_card, UniqueFactorizationMonoid, UniqueFactorizationMonoid.normalizedFactors_mul, cardFactors_apply, card_add, coe_card, factors_eq, normalizedFactors_mul
-/
theorem cardFactors_mul {m n : Nat} (m0 : m != 0) (n0 : n != 0) : Ω (m * n) = Ω m + Ω n := by
  rw [cardFactors_apply]; rw [cardFactors_apply]; rw [cardFactors_apply]; rw [← Multiset.coe_card]; rw [← factors_eq]; rw [UniqueFactorizationMonoid.normalizedFactors_mul m0 n0]; rw [factors_eq]; rw [factors_eq]; rw [Multiset.card_add]; rw [Multiset.coe_card]; rw [Multiset.coe_card]

/--
theorem `cardFactors_multiset_prod` / 定理 `cardFactors_multiset_prod`

English:
theorem cardFactors_multiset_prod
  given: {s : Multiset Nat} (h0 : s.prod != 0)
  proof: by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons ih => simp_all [cardFactors_mul, not_or]

@[simp]

中文:
定理 cardFactors_multiset_prod
  条件: {s : Multiset 自然数} (h0 : s.乘积 != 0)
  证明: by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons ih => simp_all [cardFactors_mul, not_or]

@[simp]

Depends on / 依赖: Multiset, Multiset.induction_on, cardFactors_mul, induction_on, not_or
-/
theorem cardFactors_multiset_prod {s : Multiset Nat} (h0 : s.prod != 0) :
    Ω s.prod = (Multiset.map Ω s).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons ih => simp_all [cardFactors_mul, not_or]

@[simp]
/--
theorem `cardFactors_apply_prime` / 定理 `cardFactors_apply_prime`

English:
theorem cardFactors_apply_prime
  given: {p : Nat} (hp : p.Prime)
  statement: Ω p = 1
  proof: cardFactors_eq_one_iff_prime.2 hp

中文:
定理 cardFactors_apply_prime
  条件: {p : 自然数} (hp : p.素)
  结论: Ω p = 1
  证明: cardFactors_eq_one_iff_prime.2 hp

Depends on / 依赖: cardFactors_eq_one_iff_prime
-/
theorem cardFactors_apply_prime {p : Nat} (hp : p.Prime) : Ω p = 1 :=
  cardFactors_eq_one_iff_prime.2 hp

/--
lemma `cardFactors_pow` / 引理 `cardFactors_pow`

English:
lemma cardFactors_pow
  given: {m k : Nat}
  statement: Ω (m ^ k) = k * Ω m
  proof: by
  by_cases hm : m = 0
  · cases k <;> aesop
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]; rw [cardFactors_mul (pow_ne_zero n hm) hm]; rw [ih]
    ring

@[simp]

中文:
引理 cardFactors_pow
  条件: {m k : 自然数}
  结论: Ω (m ^ k) = k * Ω m
  证明: by
  by_cases hm : m = 0
  · cases k <;> aesop
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]; rw [cardFactors_mul (pow_ne_zero n hm) hm]; rw [ih]
    ring

@[simp]

Depends on / 依赖: cardFactors_mul, pow_ne_zero, pow_succ
-/
lemma cardFactors_pow {m k : Nat} : Ω (m ^ k) = k * Ω m := by
  by_cases hm : m = 0
  · cases k <;> aesop
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]; rw [cardFactors_mul (pow_ne_zero n hm) hm]; rw [ih]
    ring

@[simp]
/--
theorem `cardFactors_apply_prime_pow` / 定理 `cardFactors_apply_prime_pow`

English:
theorem cardFactors_apply_prime_pow
  given: {p k : Nat} (hp : p.Prime)
  statement: Ω (p ^ k) = k
  proof: by
  simp [cardFactors_pow, hp]

中文:
定理 cardFactors_apply_prime_pow
  条件: {p k : 自然数} (hp : p.素)
  结论: Ω (p ^ k) = k
  证明: by
  simp [cardFactors_pow, hp]

Depends on / 依赖: cardFactors_pow
-/
theorem cardFactors_apply_prime_pow {p k : Nat} (hp : p.Prime) : Ω (p ^ k) = k := by
  simp [cardFactors_pow, hp]

/--
theorem `cardFactors_eq_sum_factorization` / 定理 `cardFactors_eq_sum_factorization`

English:
theorem cardFactors_eq_sum_factorization
  given: {n : Nat}
  proof: by
  simp [cardFactors_apply, ← List.sum_toFinset_count_eq_length, Finsupp.sum]

中文:
定理 cardFactors_eq_sum_factorization
  条件: {n : 自然数}
  证明: by
  simp [cardFactors_apply, ← List.sum_toFinset_count_eq_length, Finsupp.sum]

Depends on / 依赖: Finsupp, Finsupp.sum, List.sum_toFinset_count_eq_length, cardFactors_apply, sum_toFinset_count_eq_length
-/
theorem cardFactors_eq_sum_factorization {n : Nat} :
    Ω n = n.factorization.sum fun _ k => k := by
  simp [cardFactors_apply, ← List.sum_toFinset_count_eq_length, Finsupp.sum]

/--
Definition of `cardDistinctFactors` / `cardDistinctFactors` 的定义

English:
definition cardDistinctFactors
  signature: : ArithmeticFunction Nat
  body: ⟨fun n => n.primeFactorsList.dedup.length, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.omega] notation "ω" => ArithmeticFunction.cardDistinctFactors

中文:
定义 cardDistinctFactors
  签名: : ArithmeticFunction 自然数
  定义体: ⟨fun n => n.primeFactorsList.dedup.length, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.omega] notation "ω" => ArithmeticFunction.cardDistinctFactors

Depends on / 依赖: length, n.primeFactorsList.dedup.length, primeFactorsList
-/
def cardDistinctFactors : ArithmeticFunction Nat :=
  ⟨fun n => n.primeFactorsList.dedup.length, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.omega] notation "ω" => ArithmeticFunction.cardDistinctFactors

open scoped omega

/--
theorem `cardDistinctFactors_zero` / 定理 `cardDistinctFactors_zero`

English:
theorem cardDistinctFactors_zero
  statement: ω 0 = 0
  proof: by simp

@[simp]

中文:
定理 cardDistinctFactors_zero
  结论: ω 0 = 0
  证明: by simp

@[simp]
-/
theorem cardDistinctFactors_zero : ω 0 = 0 := by simp

@[simp]
/--
theorem `cardDistinctFactors_one` / 定理 `cardDistinctFactors_one`

English:
theorem cardDistinctFactors_one
  statement: ω 1 = 0
  proof: by simp [cardDistinctFactors]

中文:
定理 cardDistinctFactors_one
  结论: ω 1 = 0
  证明: by simp [cardDistinctFactors]

Depends on / 依赖: cardDistinctFactors
-/
theorem cardDistinctFactors_one : ω 1 = 0 := by simp [cardDistinctFactors]

/--
theorem `cardDistinctFactors_apply` / 定理 `cardDistinctFactors_apply`

English:
theorem cardDistinctFactors_apply
  given: {n : Nat}
  statement: ω n = n.primeFactorsList.dedup.length
  proof: rfl

@[simp]

中文:
定理 cardDistinctFactors_apply
  条件: {n : 自然数}
  结论: ω n = n.primeFactorsList.dedup.length
  证明: rfl

@[simp]
-/
theorem cardDistinctFactors_apply {n : Nat} : ω n = n.primeFactorsList.dedup.length :=
  rfl

@[simp]
/--
theorem `cardDistinctFactors_eq_zero` / 定理 `cardDistinctFactors_eq_zero`

English:
theorem cardDistinctFactors_eq_zero
  given: {n : Nat}
  statement: ω n = 0 ↔ n <= 1
  proof: by
  simp [cardDistinctFactors_apply, le_one_iff_eq_zero_or_eq_one]

@[simp]

中文:
定理 cardDistinctFactors_eq_zero
  条件: {n : 自然数}
  结论: ω n = 0 ↔ n <= 1
  证明: by
  simp [cardDistinctFactors_apply, le_one_iff_eq_zero_or_eq_one]

@[simp]

Depends on / 依赖: cardDistinctFactors_apply, le_one_iff_eq_zero_or_eq_one
-/
theorem cardDistinctFactors_eq_zero {n : Nat} : ω n = 0 ↔ n <= 1 := by
  simp [cardDistinctFactors_apply, le_one_iff_eq_zero_or_eq_one]

@[simp]
/--
theorem `cardDistinctFactors_pos` / 定理 `cardDistinctFactors_pos`

English:
theorem cardDistinctFactors_pos
  given: {n : Nat}
  statement: 0 < ω n ↔ 1 < n
  proof: by simp [pos_iff_ne_zero]

中文:
定理 cardDistinctFactors_pos
  条件: {n : 自然数}
  结论: 0 < ω n ↔ 1 < n
  证明: by simp [pos_iff_ne_zero]

Depends on / 依赖: pos_iff_ne_zero
-/
theorem cardDistinctFactors_pos {n : Nat} : 0 < ω n ↔ 1 < n := by simp [pos_iff_ne_zero]

/--
theorem `cardDistinctFactors_eq_cardFactors_iff_squarefree` / 定理 `cardDistinctFactors_eq_cardFactors_iff_squarefree`

English:
theorem cardDistinctFactors_eq_cardFactors_iff_squarefree
  given: {n : Nat} (h0 : n != 0)
  proof: by
  rw [squarefree_iff_nodup_primeFactorsList h0]; rw [cardDistinctFactors_apply]
  constructor <;> intro h
  · rw [← n.primeFactorsList.dedup_sublist.eq_of_length h]
    apply List.nodup_dedup
  · simp [h.dedup, cardFactors]

中文:
定理 cardDistinctFactors_eq_cardFactors_iff_squarefree
  条件: {n : 自然数} (h0 : n != 0)
  证明: by
  rw [squarefree_iff_nodup_primeFactorsList h0]; rw [cardDistinctFactors_apply]
  constructor <;> intro h
  · rw [← n.primeFactorsList.dedup_sublist.eq_of_length h]
    apply List.nodup_dedup
  · simp [h.dedup, cardFactors]

Depends on / 依赖: List.nodup_dedup, cardDistinctFactors_apply, cardFactors, dedup_sublist, eq_of_length, h.dedup, n.primeFactorsList.dedup_sublist.eq_of_length, nodup_dedup, primeFactorsList, squarefree_iff_nodup_primeFactorsList
-/
theorem cardDistinctFactors_eq_cardFactors_iff_squarefree {n : Nat} (h0 : n != 0) :
    ω n = Ω n ↔ Squarefree n := by
  rw [squarefree_iff_nodup_primeFactorsList h0]; rw [cardDistinctFactors_apply]
  constructor <;> intro h
  · rw [← n.primeFactorsList.dedup_sublist.eq_of_length h]
    apply List.nodup_dedup
  · simp [h.dedup, cardFactors]

/--
theorem `cardDistinctFactors_eq_one_iff` / 定理 `cardDistinctFactors_eq_one_iff`

English:
theorem cardDistinctFactors_eq_one_iff
  given: {n : Nat}
  statement: ω n = 1 ↔ IsPrimePow n
  proof: by
  rw [ArithmeticFunction.cardDistinctFactors_apply]; rw [isPrimePow_iff_card_primeFactors_eq_one]; rw [← toFinset_factors]; rw [List.card_toFinset]

@[simp]

中文:
定理 cardDistinctFactors_eq_one_iff
  条件: {n : 自然数}
  结论: ω n = 1 ↔ IsPrimePow n
  证明: by
  rw [ArithmeticFunction.cardDistinctFactors_apply]; rw [isPrimePow_iff_card_primeFactors_eq_one]; rw [← toFinset_factors]; rw [List.card_toFinset]

@[simp]

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.cardDistinctFactors_apply, List.card_toFinset, cardDistinctFactors_apply, card_toFinset, isPrimePow_iff_card_primeFactors_eq_one, toFinset_factors
-/
theorem cardDistinctFactors_eq_one_iff {n : Nat} : ω n = 1 ↔ IsPrimePow n := by
  rw [ArithmeticFunction.cardDistinctFactors_apply]; rw [isPrimePow_iff_card_primeFactors_eq_one]; rw [← toFinset_factors]; rw [List.card_toFinset]

@[simp]
/--
theorem `cardDistinctFactors_apply_prime_pow` / 定理 `cardDistinctFactors_apply_prime_pow`

English:
theorem cardDistinctFactors_apply_prime_pow
  given: {p k : Nat} (hp : p.Prime) (hk : k != 0)
  proof: cardDistinctFactors_eq_one_iff.mpr hp.isPrimePow.pow hk

@[simp]

中文:
定理 cardDistinctFactors_apply_prime_pow
  条件: {p k : 自然数} (hp : p.素) (hk : k != 0)
  证明: cardDistinctFactors_eq_one_iff.mpr hp.isPrimePow.pow hk

@[simp]

Depends on / 依赖: cardDistinctFactors_eq_one_iff, cardDistinctFactors_eq_one_iff.mpr, hp.isPrimePow.pow, isPrimePow
-/
theorem cardDistinctFactors_apply_prime_pow {p k : Nat} (hp : p.Prime) (hk : k != 0) :
    ω (p ^ k) = 1 :=
cardDistinctFactors_eq_one_iff.mpr hp.isPrimePow.pow hk

@[simp]
/--
theorem `cardDistinctFactors_apply_prime` / 定理 `cardDistinctFactors_apply_prime`

English:
theorem cardDistinctFactors_apply_prime
  given: {p : Nat} (hp : p.Prime)
  statement: ω p = 1
  proof: by
  rw [← pow_one p]; rw [cardDistinctFactors_apply_prime_pow hp one_ne_zero]

中文:
定理 cardDistinctFactors_apply_prime
  条件: {p : 自然数} (hp : p.素)
  结论: ω p = 1
  证明: by
  rw [← pow_one p]; rw [cardDistinctFactors_apply_prime_pow hp one_ne_zero]

Depends on / 依赖: cardDistinctFactors_apply_prime_pow, one_ne_zero, pow_one
-/
theorem cardDistinctFactors_apply_prime {p : Nat} (hp : p.Prime) : ω p = 1 := by
  rw [← pow_one p]; rw [cardDistinctFactors_apply_prime_pow hp one_ne_zero]

/--
theorem `cardDistinctFactors_mul` / 定理 `cardDistinctFactors_mul`

English:
theorem cardDistinctFactors_mul
  given: {m n : Nat} (h : m.Coprime n)
  statement: ω (m * n) = ω m + ω n
  proof: by
  simp [cardDistinctFactors_apply, perm_primeFactorsList_mul_of_coprime h |>.dedup |>.length_eq,
.dedup_append] coprime_primeFactorsList_disjoint h

中文:
定理 cardDistinctFactors_mul
  条件: {m n : 自然数} (h : m.Coprime n)
  结论: ω (m * n) = ω m + ω n
  证明: by
  simp [cardDistinctFactors_apply, perm_primeFactorsList_mul_of_coprime h |>.dedup |>.length_eq,
.dedup_append] coprime_primeFactorsList_disjoint h

Depends on / 依赖: cardDistinctFactors_apply, coprime_primeFactorsList_disjoint, dedup_append, length_eq, perm_primeFactorsList_mul_of_coprime
-/
theorem cardDistinctFactors_mul {m n : Nat} (h : m.Coprime n) : ω (m * n) = ω m + ω n := by
  simp [cardDistinctFactors_apply, perm_primeFactorsList_mul_of_coprime h |>.dedup |>.length_eq,
.dedup_append] coprime_primeFactorsList_disjoint h

open scoped Function in
/--
theorem `cardDistinctFactors_prod` / 定理 `cardDistinctFactors_prod`

English:
theorem cardDistinctFactors_prod
  statement: {ι : Type*} {s : Finset ι} {f : ι -> Nat}
  proof: by
  induction s using cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
    rw [prod_cons]; rw [sum_cons]; rw [cardDistinctFactors_mul]; rw [ih]
    · exact fun x hx y hy hxy => h (by simp [hx]) (by simp [hy]) hxy
    · exact Coprime.prod_right fun i hi =>
        h (by simp) (by simp 

中文:
定理 cardDistinctFactors_prod
  结论: {ι : 类型} {s : 有限集 ι} {f : ι -> 自然数}
  证明: by
  induction s using cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
    rw [prod_cons]; rw [sum_cons]; rw [cardDistinctFactors_mul]; rw [ih]
    · exact fun x hx y hy hxy => h (by simp [hx]) (by simp [hy]) hxy
    · exact Coprime.prod_right fun i hi =>
        h (by simp) (by simp 

Depends on / 依赖: Coprime, Coprime.prod_right, cardDistinctFactors_mul, cons_induction_on, ne_of_mem_of_not_mem, prod_cons, prod_right, sum_cons
-/
theorem cardDistinctFactors_prod {ι : Type*} {s : Finset ι} {f : ι -> Nat}
    (h : (s : Set ι).Pairwise (Coprime on f)) : ω (∏ i in s, f i) = ∑ i in s, ω (f i) := by
  induction s using cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
    rw [prod_cons]; rw [sum_cons]; rw [cardDistinctFactors_mul]; rw [ih]
    · exact fun x hx y hy hxy => h (by simp [hx]) (by simp [hy]) hxy
    · exact Coprime.prod_right fun i hi =>
        h (by simp) (by simp [hi]) (ne_of_mem_of_not_mem hi ha).symm

end SpecialFunctions

section Sum

/--
theorem `sum_Ioc_zeta` / 定理 `sum_Ioc_zeta`

English:
theorem sum_Ioc_zeta
  given: (N : Nat)
  statement: ∑ n in Ioc 0 N, zeta n = N
  proof: by
  simp only [zeta_apply, sum_ite, sum_const_zero, sum_const, smul_eq_mul, mul_one, zero_add]
  rw [show {x in Ioc 0 N | ¬x = 0} = Ioc 0 N by ext; simp; lia]
  simp

中文:
定理 sum_Ioc_zeta
  条件: (N : 自然数)
  结论: ∑ n in 左开右闭区间 0 N, zeta n = N
  证明: by
  simp only [zeta_apply, sum_ite, sum_const_zero, sum_const, smul_eq_mul, mul_one, zero_add]
  rw [show {x in Ioc 0 N | ¬x = 0} = Ioc 0 N by ext; simp; lia]
  simp

Depends on / 依赖: mul_one, smul_eq_mul, sum_const, sum_const_zero, sum_ite, zero_add, zeta_apply
-/
theorem sum_Ioc_zeta (N : Nat) : ∑ n in Ioc 0 N, zeta n = N := by
  simp only [zeta_apply, sum_ite, sum_const_zero, sum_const, smul_eq_mul, mul_one, zero_add]
  rw [show {x in Ioc 0 N | ¬x = 0} = Ioc 0 N by ext; simp; lia]
  simp

variable {R : Type*} [Semiring R]

/--
theorem `sum_Ioc_mul_eq_sum_prod_filter` / 定理 `sum_Ioc_mul_eq_sum_prod_filter`

English:
theorem sum_Ioc_mul_eq_sum_prod_filter
  given: (f g : ArithmeticFunction R) (N : Nat)
  proof: by
  simp only [mul_apply]
  trans ∑ n in Ioc 0 N, ∑ x in Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = n, f x.1 * g x.2
  · refine sum_congr rfl fun n hn => ?_
    simp only [mem_Ioc] at hn
    rw [divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]
  · simp_rw [sum_filter]
    rw [sum_comm]
    exact s

中文:
定理 sum_Ioc_mul_eq_sum_prod_filter
  条件: (f g : ArithmeticFunction R) (N : 自然数)
  证明: by
  simp only [mul_apply]
  trans ∑ n in Ioc 0 N, ∑ x in Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = n, f x.1 * g x.2
  · refine sum_congr rfl fun n hn => ?_
    simp only [mem_Ioc] at hn
    rw [divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]
  · simp_rw [sum_filter]
    rw [sum_comm]
    exact s

Depends on / 依赖: divisorsAntidiagonal_eq_prod_filter_of_le, mem_Ioc, mul_apply, simp_rw, sum_comm, sum_congr, sum_filter
-/
theorem sum_Ioc_mul_eq_sum_prod_filter (f g : ArithmeticFunction R) (N : Nat) :
    ∑ n in Ioc 0 N, (f * g) n = ∑ x in Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 <= N, f x.1 * g x.2 := by
  simp only [mul_apply]
  trans ∑ n in Ioc 0 N, ∑ x in Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = n, f x.1 * g x.2
  · refine sum_congr rfl fun n hn => ?_
    simp only [mem_Ioc] at hn
    rw [divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]
  · simp_rw [sum_filter]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => (by simp_all)

/--
theorem `sum_Ioc_mul_eq_sum_sum` / 定理 `sum_Ioc_mul_eq_sum_sum`

English:
theorem sum_Ioc_mul_eq_sum_sum
  given: (f g : ArithmeticFunction R) (N : Nat)
  proof: by
  rw [sum_Ioc_mul_eq_sum_prod_filter]; rw [sum_filter]; rw [sum_product]
  refine sum_congr rfl fun n hn => ?_
  simp only [sum_ite, not_le, sum_const_zero, add_zero, mul_sum]
  congr
  ext
  simp only [mem_filter, mem_Ioc, and_assoc, and_congr_right_iff] at hn ⊢
  intro _
  constructor
  · intro

中文:
定理 sum_Ioc_mul_eq_sum_sum
  条件: (f g : ArithmeticFunction R) (N : 自然数)
  证明: by
  rw [sum_Ioc_mul_eq_sum_prod_filter]; rw [sum_filter]; rw [sum_product]
  refine sum_congr rfl fun n hn => ?_
  simp only [sum_ite, not_le, sum_const_zero, add_zero, mul_sum]
  congr
  ext
  simp only [mem_filter, mem_Ioc, and_assoc, and_congr_right_iff] at hn ⊢
  intro _
  constructor
  · intro

Depends on / 依赖: Nat.mul_div_cancel_left, add_zero, and_assoc, and_congr_right_iff, div_le_self, mem_Ioc, mem_filter, mul_div_cancel_left, mul_div_le, mul_sum, not_le, sum_Ioc_mul_eq_sum_prod_filter, sum_congr, sum_const_zero, sum_filter, sum_ite, sum_product
-/
theorem sum_Ioc_mul_eq_sum_sum (f g : ArithmeticFunction R) (N : Nat) :
    ∑ n in Ioc 0 N, (f * g) n = ∑ n in Ioc 0 N, f n * ∑ m in Ioc 0 (N / n), g m := by
  rw [sum_Ioc_mul_eq_sum_prod_filter]; rw [sum_filter]; rw [sum_product]
  refine sum_congr rfl fun n hn => ?_
  simp only [sum_ite, not_le, sum_const_zero, add_zero, mul_sum]
  congr
  ext
  simp only [mem_filter, mem_Ioc, and_assoc, and_congr_right_iff] at hn ⊢
  intro _
  constructor
  · intro ⟨_, h⟩
    grw [← h, Nat.mul_div_cancel_left _ (by lia)]
  · intro hm
    grw [hm]
    simp [mul_div_le, div_le_self]

/--
theorem `sum_Ioc_mul_zeta_eq_sum` / 定理 `sum_Ioc_mul_zeta_eq_sum`

English:
theorem sum_Ioc_mul_zeta_eq_sum
  given: (f : ArithmeticFunction R) (N : Nat)
  proof: by
  rw [sum_Ioc_mul_eq_sum_sum]
  refine sum_congr rfl fun n hn => ?_
  simp_rw [natCoe_apply]
  rw_mod_cast [sum_Ioc_zeta]

中文:
定理 sum_Ioc_mul_zeta_eq_sum
  条件: (f : ArithmeticFunction R) (N : 自然数)
  证明: by
  rw [sum_Ioc_mul_eq_sum_sum]
  refine sum_congr rfl fun n hn => ?_
  simp_rw [natCoe_apply]
  rw_mod_cast [sum_Ioc_zeta]

Depends on / 依赖: natCoe_apply, rw_mod_cast, simp_rw, sum_Ioc_mul_eq_sum_sum, sum_Ioc_zeta, sum_congr
-/
theorem sum_Ioc_mul_zeta_eq_sum (f : ArithmeticFunction R) (N : Nat) :
    ∑ n in Ioc 0 N, (f * zeta) n = ∑ n in Ioc 0 N, f n * ↑(N / n) := by
  rw [sum_Ioc_mul_eq_sum_sum]
  refine sum_congr rfl fun n hn => ?_
  simp_rw [natCoe_apply]
  rw_mod_cast [sum_Ioc_zeta]

--TODO: Dirichlet hyperbola method to get sums of length `sqrt N`
/--
theorem `sum_Ioc_sigma0_eq_sum_div` / 定理 `sum_Ioc_sigma0_eq_sum_div`

English:
theorem sum_Ioc_sigma0_eq_sum_div
  given: (N : Nat)
  proof: by
  rw [← zeta_mul_pow_eq_sigma]; rw [pow_zero_eq_zeta]
  convert! sum_Ioc_mul_zeta_eq_sum zeta N using 1
  simpa using sum_congr rfl (by grind)

中文:
定理 sum_Ioc_sigma0_eq_sum_div
  条件: (N : 自然数)
  证明: by
  rw [← zeta_mul_pow_eq_sigma]; rw [pow_zero_eq_zeta]
  convert! sum_Ioc_mul_zeta_eq_sum zeta N using 1
  simpa using sum_congr rfl (by grind)

Depends on / 依赖: convert, pow_zero_eq_zeta, sum_Ioc_mul_zeta_eq_sum, sum_congr, zeta_mul_pow_eq_sigma
-/
theorem sum_Ioc_sigma0_eq_sum_div (N : Nat) :
    ∑ n in Ioc 0 N, sigma 0 n = ∑ n in Ioc 0 N, (N / n) := by
  rw [← zeta_mul_pow_eq_sigma]; rw [pow_zero_eq_zeta]
  convert! sum_Ioc_mul_zeta_eq_sum zeta N using 1
  simpa using sum_congr rfl (by grind)

end Sum

end ArithmeticFunction

namespace Nat.Coprime

open ArithmeticFunction

/--
theorem `card_divisors_mul` / 定理 `card_divisors_mul`

English:
theorem card_divisors_mul
  given: {m n : Nat} (hmn : m.Coprime n)
  proof: by
  simp only [← sigma_zero_apply, isMultiplicative_sigma.map_mul_of_coprime hmn]

中文:
定理 card_divisors_mul
  条件: {m n : 自然数} (hmn : m.Coprime n)
  证明: by
  simp only [← sigma_zero_apply, isMultiplicative_sigma.map_mul_of_coprime hmn]

Depends on / 依赖: isMultiplicative_sigma, isMultiplicative_sigma.map_mul_of_coprime, map_mul_of_coprime, sigma_zero_apply
-/
theorem card_divisors_mul {m n : Nat} (hmn : m.Coprime n) :
    #(m * n).divisors = #m.divisors * #n.divisors := by
  simp only [← sigma_zero_apply, isMultiplicative_sigma.map_mul_of_coprime hmn]

/--
theorem `sum_divisors_mul` / 定理 `sum_divisors_mul`

English:
theorem sum_divisors_mul
  given: {m n : Nat} (hmn : m.Coprime n)
  proof: by
  simp only [← sigma_one_apply, isMultiplicative_sigma.map_mul_of_coprime hmn]

中文:
定理 sum_divisors_mul
  条件: {m n : 自然数} (hmn : m.Coprime n)
  证明: by
  simp only [← sigma_one_apply, isMultiplicative_sigma.map_mul_of_coprime hmn]

Depends on / 依赖: isMultiplicative_sigma, isMultiplicative_sigma.map_mul_of_coprime, map_mul_of_coprime, sigma_one_apply
-/
theorem sum_divisors_mul {m n : Nat} (hmn : m.Coprime n) :
    ∑ d in (m * n).divisors, d = (∑ d in m.divisors, d) * ∑ d in n.divisors, d := by
  simp only [← sigma_one_apply, isMultiplicative_sigma.map_mul_of_coprime hmn]

end Nat.Coprime

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for `ArithmeticFunction.sigma`. -/
@[positivity ArithmeticFunction.sigma _ _]
meta def evalArithmeticFunctionSigma : PositivityExt where eval {u α} z p? e :=
  match p? with | none => throwError "no PartialOrder instance" | some p => do
  match u, α, e with
  | 0, ~q(Nat), ~q(ArithmeticFunction.sigma $k $n) =>
    assumeInstancesCommute
    let rn ← core z p n
    match rn with
    | .positive pn => return .positive q(Iff.mpr ArithmeticFunction.sigma_pos_iff $pn)
    | _ => return .nonnegative q(Nat.zero_le _)
  | _, _, _ => throwError "not ArithmeticFunction.sigma"


end Mathlib.Meta.Positivity
