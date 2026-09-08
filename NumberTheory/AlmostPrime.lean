/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Almost prime numbers

This file defines `Nat.IsAlmostPrime k n`, the predicate that `n` has exactly `k`
prime factors counted with multiplicity. We also define `Nat.IsAtMostAlmostPrime`,
the corresponding predicate with at most `k` prime factors, and `Nat.IsSemiprime`,
the special case of `2`-almost-prime numbers.

Both definitions use the arithmetic function `ArithmeticFunction.cardFactors`, written `Ω`.

The terminology follows the standard definition of an
[almost prime](https://en.wikipedia.org/wiki/Almost_prime).

## Main statements

* `Nat.IsAlmostPrime.mul`: the product of a `k`-almost-prime number and an
  `l`-almost-prime number is `(k + l)`-almost-prime.
* `Nat.IsAtMostAlmostPrime.mul`: the analogous statement for at most `k` prime factors.

-/

@[expose] public section

open scoped ArithmeticFunction.Omega

namespace Nat

/-- `IsAlmostPrime k n` means that `n` is `k`-almost prime: it has exactly `k`
prime factors, counted with multiplicity. The side condition excludes `0`, so `1` is
`0`-almost prime. -/
/-
**Nat.IsAlmostPrime** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：IsAlmostPrime (k n : Nat) : Prop
参数：k n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsAlmostPrime k n` means that `n` is `k`-almost prime: it has exactly `k`
prime factors, counted with multiplicity. The side condition excludes `0`, so `1
` is
`0`-almost prime.
-/
def IsAlmostPrime (k n : ℕ) : Prop :=
  n ≠ 0 ∧ Ω n = k

/-- `IsAtMostAlmostPrime k n` means that `n` has at most `k` prime factors,
counted with multiplicity. -/
/-
**Nat.IsAtMostAlmostPrime** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：IsAtMostAlmostPrime (k n : Nat) : Prop
参数：k n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsAtMostAlmostPrime k n` means that `n` has at most `k` prime factors,
counted with multiplicity.
-/
def IsAtMostAlmostPrime (k n : ℕ) : Prop :=
  n ≠ 0 ∧ Ω n ≤ k

/-- A semiprime is a `2`-almost-prime number. -/
/-
**Nat.IsSemiprime** 是 Mathlib 中的一个缩写定义，位于命名空间 `Nat`。
形式化陈述：IsSemiprime (n : Nat) : Prop
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A semiprime is a `2`-almost-prime number.
-/
abbrev IsSemiprime (n : ℕ) : Prop :=
  IsAlmostPrime 2 n

variable {k l m n p q : ℕ}

@[simp]
/-
**Nat.isAlmostPrime_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：isAlmostPrime_zero_iff : IsAlmostPrime 0 n ↔ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.IsAlmostPrime.eq_1`：∀ (k n : ℕ), k.IsAlmostPrime n = (n ≠ 0 ∧ Arithm
eticFunction.cardFactors n = k)
· 使用定理 `ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one`：cardFactors_e
q_zero_iff_eq_zero_or_one {n : Nat} : Ω n = 0 ↔ n = 0 ∨ n = 1
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem isAlmostPrime_zero_iff : IsAlmostPrime 0 n ↔ n = 1 := by
  rw [IsAlmostPrime, ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one]
  exact ⟨fun h ↦ h.2.resolve_left h.1, fun h ↦ by simp [h]⟩

@[simp]
/-
**Nat.isAlmostPrime_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：isAlmostPrime_one_iff : IsAlmostPrime 1 n ↔ n.Prime
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ArithmeticFunction.cardFactors_eq_one_iff_prime`：cardFactors_eq_one_iff_
prime {n : Nat} : Ω n = 1 ↔ n.Prime
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem isAlmostPrime_one_iff : IsAlmostPrime 1 n ↔ n.Prime := by
  constructor
  · exact fun h ↦ ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h.2
  · exact fun h ↦ ⟨h.ne_zero, ArithmeticFunction.cardFactors_eq_one_iff_prime.mpr h⟩
/-
**Nat.Prime.isAlmostPrime_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → Nat.IsAlmostPrime 1 p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.isAlmostPrime_one_iff`：isAlmostPrime_one_iff : IsAlmostPrime 1 n ↔ n
.Prime
-/
theorem Prime.isAlmostPrime_one (hp : p.Prime) : IsAlmostPrime 1 p := by
  simpa using isAlmostPrime_one_iff.mpr hp
/-
**Nat.IsAlmostPrime.mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat.IsAlmostPrime`。
形式化陈述：∀ {k l m n : ℕ}, k.IsAlmostPrime m → l.IsAlmostPrime n → (k + l).IsAlmostP
rime (m * n)
参数：k + l；m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.cardFactors_mul`：cardFactors_mul {m n : Nat} (m0 : m 
!= 0) (n0 : n != 0) : Ω (m * n) = Ω m + Ω n
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsAlmostPrime.mul (hm : IsAlmostPrime k m) (hn : IsAlmostPrime l n) :
    IsAlmostPrime (k + l) (m * n) := by
  refine ⟨mul_ne_zero hm.1 hn.1, ?_⟩
  rw [ArithmeticFunction.cardFactors_mul hm.1 hn.1, hm.2, hn.2]
/-
**Nat.IsAtMostAlmostPrime.mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat.IsAtMostAlmostPrime
`。
形式化陈述：∀ {k l m n : ℕ}, k.IsAtMostAlmostPrime m → l.IsAtMostAlmostPrime n → (k + 
l).IsAtMostAlmostPrime (m * n)
参数：k + l；m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.cardFactors_mul`：cardFactors_mul {m n : Nat} (m0 : m 
!= 0) (n0 : n != 0) : Ω (m * n) = Ω m + Ω n
· 使用定理 `Nat.add_le_add`：∀ {a b c d : ℕ}, a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsAtMostAlmostPrime.mul (hm : IsAtMostAlmostPrime k m) (hn : IsAtMostAlmostPrime l n) :
    IsAtMostAlmostPrime (k + l) (m * n) := by
  refine ⟨mul_ne_zero hm.1 hn.1, ?_⟩
  rw [ArithmeticFunction.cardFactors_mul hm.1 hn.1]
  exact add_le_add hm.2 hn.2
/-
**Nat.IsAlmostPrime.isAtMost** 是 Mathlib 中的一个定理，位于命名空间 `Nat.IsAlmostPrime`。
形式化陈述：∀ {k l n : ℕ}, k.IsAlmostPrime n → k ≤ l → l.IsAtMostAlmostPrime n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsAlmostPrime.isAtMost (hn : IsAlmostPrime k n) (hkl : k ≤ l) :
    IsAtMostAlmostPrime l n :=
  ⟨hn.1, hn.2 ▸ hkl⟩
/-
**Nat.Prime.mul_isAlmostPrime_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p q : ℕ}, Nat.Prime p → Nat.Prime q → Nat.IsAlmostPrime 2 (p * q)
参数：p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.IsAlmostPrime.mul`：∀ {k l m n : ℕ}, k.IsAlmostPrime m → l.IsAlmostPr
ime n → (k + l).IsAlmostPrime (m * n)
· 使用定理 `Nat.Prime.isAlmostPrime_one`：∀ {p : ℕ}, Nat.Prime p → Nat.IsAlmostPrime 
1 p
-/
theorem Prime.mul_isAlmostPrime_two (hp : p.Prime) (hq : q.Prime) :
    IsAlmostPrime 2 (p * q) := by
  simpa using hp.isAlmostPrime_one.mul hq.isAlmostPrime_one
/-
**Nat.Prime.sq_isAlmostPrime_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → Nat.IsAlmostPrime 2 (p ^ 2)
参数：p ^ 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Nat.Prime.mul_isAlmostPrime_two`：∀ {p q : ℕ}, Nat.Prime p → Nat.Prime q 
→ Nat.IsAlmostPrime 2 (p * q)
-/
theorem Prime.sq_isAlmostPrime_two (hp : p.Prime) : IsAlmostPrime 2 (p ^ 2) := by
  simpa [pow_two] using hp.mul_isAlmostPrime_two hp

end Nat

