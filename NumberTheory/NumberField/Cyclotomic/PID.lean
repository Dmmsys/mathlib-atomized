/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

/-!
# Cyclotomic fields whose ring of integers is a PID.

We prove that `ℤ [ζₚ]` is a PID for specific values of `p`. The result holds for `p ≤ 19`,
but the proof is more and more involved.

## Main results
* `three_pid`: If `IsCyclotomicExtension {3} ℚ K` then `𝓞 K` is a principal ideal domain.
* `five_pid`: If `IsCyclotomicExtension {5} ℚ K` then `𝓞 K` is a principal ideal domain.
-/

public section

universe u

namespace IsCyclotomicExtension.Rat

open NumberField Polynomial InfinitePlace Nat Real cyclotomic

variable (K : Type u) [Field K] [NumberField K]

/-- If `IsCyclotomicExtension {3} ℚ K` then `𝓞 K` is a principal ideal domain. -/
/-
**IsCyclotomicExtension.Rat.three_pid** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclotomicExt
ension.Rat`。
形式化陈述：three_pid [IsCyclotomicExtension {3} Rat K] : IsPrincipalIdealRing (𝓞 K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`：isPrincipalIdealRin
g_of_abs_discr_lt (h : |discr K| < (2 * (π / 4) ^ nrComplexPlaces K * ((finrank 
Rat K) ^ (finrank Rat K) / (finrank Rat K…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsCyclotomicExtension.Rat.discr_prime`：discr_prime [IsCyclotomicExtensio
n {p} Rat K] : haveI : NumberField K
· 使用定理 `IsCyclotomicExtension.finrank`：finrank (hirr : Irreducible (cyclotomic n
 K)) : finrank K L = n.totient
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.cyclotomic.irreducible_rat`：∀ {n : ℕ}, 0 < n → Irreducible (P
olynomial.cyclotomic n ℚ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two`：nrComplexP
laces_eq_totient_div_two [h : IsCyclotomicExtension {n} Rat K] : haveI
· 使用定理 `Nat.totient_prime`：totient_prime {p : Nat} (hp : p.Prime) : φ p = p - 1
· 使用定理 `Nat.prime_three`：prime_three : Prime 3
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.succ_sub_succ_eq_sub`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Nat.div_self`：∀ {n : ℕ}, 0 < n → n / n = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
If `IsCyclotomicExtension {3} ℚ K` then `𝓞 K` is a principal ideal domain.
-/
theorem three_pid [IsCyclotomicExtension {3} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [discr_prime 3 K, IsCyclotomicExtension.finrank (n := 3) K
    (irreducible_rat (by simp)), nrComplexPlaces_eq_totient_div_two 3, totient_prime
      Nat.prime_three]
  simp only [Int.reduceNeg, succ_sub_succ_eq_sub, tsub_zero, zero_lt_two, Nat.div_self, pow_one,
    cast_ofNat, neg_mul, one_mul, abs_neg, Int.cast_abs, Int.cast_ofNat,
    abs_of_pos (zero_lt_three' ℝ), factorial_two]
  suffices (2 * (3 / 4) * (2 ^ 2 / 2)) ^ 2 < (2 * (π / 4) * (2 ^ 2 / 2)) ^ 2 from
    lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three

/-- If `IsCyclotomicExtension {5} ℚ K` then `𝓞 K` is a principal ideal domain. -/
/-
**IsCyclotomicExtension.Rat.five_pid** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclotomicExte
nsion.Rat`。
形式化陈述：five_pid [IsCyclotomicExtension {5} Rat K] : IsPrincipalIdealRing (𝓞 K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.prime_five`：prime_five : Prime 5
· 使用定理 `RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt`：isPrincipalIdealRin
g_of_abs_discr_lt (h : |discr K| < (2 * (π / 4) ^ nrComplexPlaces K * ((finrank 
Rat K) ^ (finrank Rat K) / (finrank Rat K…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsCyclotomicExtension.Rat.discr_prime`：discr_prime [IsCyclotomicExtensio
n {p} Rat K] : haveI : NumberField K
· 使用定理 `IsCyclotomicExtension.finrank`：finrank (hirr : Irreducible (cyclotomic n
 K)) : finrank K L = n.totient
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.cyclotomic.irreducible_rat`：∀ {n : ℕ}, 0 < n → Irreducible (P
olynomial.cyclotomic n ℚ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two`：nrComplexP
laces_eq_totient_div_two [h : IsCyclotomicExtension {n} Rat K] : haveI
· 使用定理 `Nat.totient_prime`：totient_prime {p : Nat} (hp : p.Prime) : φ p = p - 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.succ_sub_succ_eq_sub`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
If `IsCyclotomicExtension {5} ℚ K` then `𝓞 K` is a principal ideal domain.
-/
theorem five_pid [IsCyclotomicExtension {5} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [discr_prime 5 K, IsCyclotomicExtension.finrank (n := 5) K
    (irreducible_rat (by simp)), nrComplexPlaces_eq_totient_div_two 5,
    totient_prime Nat.prime_five]
  simp only [Int.reduceNeg, succ_sub_succ_eq_sub, tsub_zero, reduceDiv, even_two, Even.neg_pow,
    one_pow, cast_ofNat, Int.reducePow, one_mul, Int.cast_abs, Int.cast_ofNat,
    abs_of_pos (show (0 : ℝ) < 125 by simp), div_pow, show 4! = 24 by rfl]
  suffices (2 * (3 ^ 2 / 4 ^ 2) * (4 ^ 4 / 24)) ^ 2 < (2 * (π ^ 2 / 4 ^ 2) * (4 ^ 4 / 24)) ^ 2 from
    lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three

end IsCyclotomicExtension.Rat

