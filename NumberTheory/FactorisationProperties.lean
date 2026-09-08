/-
Copyright (c) 2024 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum

/-!
# Factorisation properties of natural numbers

This file defines abundant, pseudoperfect, deficient, and weird numbers and formalizes their
relations with prime and perfect numbers.

## Main Definitions

* `Nat.Abundant`: a natural number `n` is _abundant_ if the sum of its proper divisors is greater
  than `n`
* `Nat.Pseudoperfect`: a natural number `n` is _pseudoperfect_ if the sum of a subset of its proper
  divisors equals `n`
* `Nat.Deficient`: a natural number `n` is _deficient_ if the sum of its proper divisors is less
  than `n`
* `Nat.Weird`: a natural number is _weird_ if it is abundant but not pseudoperfect

## Main Results

* `Nat.deficient_or_perfect_or_abundant`: A positive natural number is either deficient,
  perfect, or abundant.
* `Nat.Prime.deficient`: All prime natural numbers are deficient.
* `Nat.infinite_deficient`: There are infinitely many deficient numbers.
* `Nat.Prime.deficient_pow`: Any natural number power of a prime is deficient.

## Implementation Notes
* Zero is not included in any of the definitions and these definitions only apply to natural
  numbers greater than zero.

## References
* [R. W. Prielipp, *PERFECT NUMBERS, ABUNDANT NUMBERS, AND DEFICIENT NUMBERS*][Prielipp1970]

## Tags

abundant, deficient, weird, pseudoperfect
-/

@[expose] public section

open Finset

namespace Nat

variable {n m p : ℕ}

/-- `n : ℕ` is _abundant_ if the sum of the proper divisors of `n` is greater than `n`. -/
/-
**Nat.Abundant** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：Abundant (n : Nat) : Prop
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`n : ℕ` is _abundant_ if the sum of the proper divisors of `n` is greater than `
n`.
-/
def Abundant (n : ℕ) : Prop := n < ∑ i ∈ properDivisors n, i
deriving Decidable

/-- `n : ℕ` is _deficient_ if the sum of the proper divisors of `n` is less than `n`. -/
/-
**Nat.Deficient** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：Deficient (n : Nat) : Prop
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`n : ℕ` is _deficient_ if the sum of the proper divisors of `n` is less than `n`
.
-/
def Deficient (n : ℕ) : Prop := ∑ i ∈ properDivisors n, i < n
deriving Decidable

/-- A positive natural number `n` is _pseudoperfect_ if there exists a subset of the proper
  divisors of `n` such that the sum of that subset is equal to `n`. -/
/-
**Nat.Pseudoperfect** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：Pseudoperfect (n : Nat) : Prop
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A positive natural number `n` is _pseudoperfect_ if there exists a subset of the
 proper
  divisors of `n` such that the sum of that subset is equal to `n`.
-/
def Pseudoperfect (n : ℕ) : Prop :=
  0 < n ∧ ∃ s ⊆ properDivisors n, ∑ i ∈ s, i = n
deriving Decidable

/-- `n : ℕ` is a _weird_ number if and only if it is abundant but not pseudoperfect. -/
/-
**Nat.Weird** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：Weird (n : Nat) : Prop
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`n : ℕ` is a _weird_ number if and only if it is abundant but not pseudoperfect.
-/
def Weird (n : ℕ) : Prop := Abundant n ∧ ¬ Pseudoperfect n
deriving Decidable

/-- `abundancyIndex n` is the sum of the divisors of `n` divided by `n`. -/
/-
**Nat.abundancyIndex** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：abundancyIndex (n : Nat) : Rat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`abundancyIndex n` is the sum of the divisors of `n` divided by `n`.
-/
def abundancyIndex (n : ℕ) : ℚ := (∑ i ∈ n.divisors, i) / (n : ℚ)
/-
**Nat.not_pseudoperfect_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_pseudoperfect_iff_forall : ¬ Pseudoperfect n ↔ n = 0 ∨ forall s subset
eq properDivisors n, ∑ i in s, i != n
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_pseudoperfect_iff_forall :
    ¬ Pseudoperfect n ↔ n = 0 ∨ ∀ s ⊆ properDivisors n, ∑ i ∈ s, i ≠ n := by
  grind [Pseudoperfect]
/-
**Nat.not_deficient_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_deficient_zero : ¬ Deficient 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem not_deficient_zero : ¬ Deficient 0 := by
  decide
/-
**Nat.deficient_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：deficient_one : Deficient 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem deficient_one : Deficient 1 := by
  decide
/-
**Nat.deficient_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：deficient_two : Deficient 2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem deficient_two : Deficient 2 := by
  decide
/-
**Nat.deficient_three** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：deficient_three : Deficient 3
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem deficient_three : Deficient 3 := by
  decide
/-
**Nat.not_abundant_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_abundant_zero : ¬ Abundant 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem not_abundant_zero : ¬ Abundant 0 := by
  decide
/-
**Nat.abundant_twelve** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：abundant_twelve : Abundant 12
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem abundant_twelve : Abundant 12 := by
  decide
/-
**Nat.not_weird_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_weird_zero : ¬ Weird 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem not_weird_zero : ¬ Weird 0 := by
  decide
/-
**Nat.weird_seventy** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：weird_seventy : Weird 70
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem weird_seventy : Weird 70 := by
  decide +kernel
/-
**Nat.Deficient.pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Deficient`。
形式化陈述：∀ {n : ℕ}, n.Deficient → 0 < n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Deficient.pos (h : Deficient n) : 0 < n := by
  grind only [not_deficient_zero]
/-
**Nat.Abundant.pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Abundant`。
形式化陈述：∀ {n : ℕ}, n.Abundant → 0 < n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Abundant.pos (h : Abundant n) : 0 < n := by
  grind only [not_abundant_zero]
/-
**Nat.Weird.pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Weird`。
形式化陈述：∀ {n : ℕ}, n.Weird → 0 < n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Weird.pos (h : Weird n) : 0 < n := by
  grind only [not_weird_zero]
/-
**Nat.deficient_iff_not_abundant_and_not_perfect** 是 Mathlib 中的一个引理，位于命名空间 `Nat`
。
形式化陈述：deficient_iff_not_abundant_and_not_perfect (hn : n != 0) : Deficient n ↔ ¬
 Abundant n ∧ ¬ Perfect n
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma deficient_iff_not_abundant_and_not_perfect (hn : n ≠ 0) :
    Deficient n ↔ ¬ Abundant n ∧ ¬ Perfect n := by
  grind [Perfect, Abundant, Deficient]
/-
**Nat.perfect_iff_not_abundant_and_not_deficient** 是 Mathlib 中的一个引理，位于命名空间 `Nat`
。
形式化陈述：perfect_iff_not_abundant_and_not_deficient (hn : 0 != n) : Perfect n ↔ ¬ A
bundant n ∧ ¬ Deficient n
参数：hn : 0 != n。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma perfect_iff_not_abundant_and_not_deficient (hn : 0 ≠ n) :
    Perfect n ↔ ¬ Abundant n ∧ ¬ Deficient n := by
  grind [Perfect, Abundant, Deficient]
/-
**Nat.abundant_iff_not_perfect_and_not_deficient** 是 Mathlib 中的一个引理，位于命名空间 `Nat`
。
形式化陈述：abundant_iff_not_perfect_and_not_deficient (hn : 0 != n) : Abundant n ↔ ¬ 
Perfect n ∧ ¬ Deficient n
参数：hn : 0 != n。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma abundant_iff_not_perfect_and_not_deficient (hn : 0 ≠ n) :
    Abundant n ↔ ¬ Perfect n ∧ ¬ Deficient n := by
  grind [Perfect, Abundant, Deficient]

/-- A positive natural number is either deficient, perfect, or abundant -/
/-
**Nat.deficient_or_perfect_or_abundant** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：deficient_or_perfect_or_abundant (hn : 0 != n) : Deficient n ∨ Abundant n 
∨ Perfect n
参数：hn : 0 != n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A positive natural number is either deficient, perfect, or abundant
-/
theorem deficient_or_perfect_or_abundant (hn : 0 ≠ n) :
    Deficient n ∨ Abundant n ∨ Perfect n := by
  grind [Perfect, Abundant, Deficient]
/-
**Nat.Perfect.pseudoperfect** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Perfect`。
形式化陈述：∀ {n : ℕ}, n.Perfect → n.Pseudoperfect
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Perfect.pseudoperfect (h : Perfect n) : Pseudoperfect n :=
  ⟨h.2, ⟨properDivisors n, ⟨fun _ a ↦ a, h.1⟩⟩⟩
/-
**Nat.Prime.not_abundant** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {n : ℕ}, Nat.Prime n → ¬n.Abundant
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.sum_properDivisors_eq_one_iff_prime`：sum_properDivisors_eq_one_iff_p
rime : ∑ x in n.properDivisors, x = 1 ↔ n.Prime
-/
theorem Prime.not_abundant (h : Prime n) : ¬ Abundant n :=
  fun h1 ↦ (h.one_lt.trans h1).ne' (sum_properDivisors_eq_one_iff_prime.mpr h)
/-
**Nat.Prime.not_weird** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {n : ℕ}, Nat.Prime n → ¬n.Weird
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Prime.not_weird (h : Prime n) : ¬ Weird n := by
  grind [Weird, h.not_abundant]
/-
**Nat.Prime.not_pseudoperfect** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → ¬p.Pseudoperfect
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.not_pseudoperfect_iff_forall`：not_pseudoperfect_iff_forall : ¬ Pseud
operfect n ↔ n = 0 ∨ forall s subseteq properDivisors n, ∑ i in s, i != n
· 使用定理 `Nat.ne_of_lt`：∀ {a b : ℕ}, a < b → a ≠ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Finset.sum_le_sum_of_subset`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] {f : ι → M}   {s t
 : Finset ι}, s ⊆…
· 使用定理 `Nat.Prime.properDivisors`：∀ {p : ℕ}, Nat.Prime p → p.properDivisors = {1
}
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
-/
theorem Prime.not_pseudoperfect (h : Prime p) : ¬ Pseudoperfect p := by
  rw [not_pseudoperfect_iff_forall]
  refine Or.inr fun s hs ↦ ne_of_lt (lt_of_le_of_lt ?_ h.one_lt)
  rw [Prime.properDivisors h] at hs
  simpa using Finset.sum_le_sum_of_subset hs
/-
**Nat.Prime.not_perfect** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → ¬p.Perfect
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.not_pseudoperfect`：∀ {p : ℕ}, Nat.Prime p → ¬p.Pseudoperfect
· 使用定理 `Nat.Perfect.pseudoperfect`：∀ {n : ℕ}, n.Perfect → n.Pseudoperfect
-/
theorem Prime.not_perfect (h : Prime p) : ¬ Perfect p :=
  fun hp ↦ h.not_pseudoperfect hp.pseudoperfect

/-- Any natural number power of a prime is deficient -/
/-
**Nat.Prime.deficient_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {n m : ℕ}, Nat.Prime n → (n ^ m).Deficient
参数：n ^ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.deficient_one`：deficient_one : Deficient 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Deficient.eq_1`：∀ (n : ℕ), n.Deficient = (∑ i ∈ n.properDivisors, i 
< n)
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Nat.properDivisors_prime_pow`：properDivisors_prime_pow {p : Nat} (pp : p
.Prime) (k : Nat) : properDivisors (p ^ k) = (Finset.range k).map ⟨(p ^ ·), Nat.
pow_right_injectiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Nat.geomSum_eq`：geomSum_eq (hm : 2 <= m) (n : Nat) : ∑ k in range n, m ^
 k = (m ^ n - 1) / (m - 1)
· 使用定理 `Nat.div_le_self`：∀ (n k : ℕ), n / k ≤ n
· 使用定理 `Nat.sub_lt`：∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p

--- 原说明 ---
Any natural number power of a prime is deficient
-/
theorem Prime.deficient_pow (h : Prime n) : Deficient (n ^ m) := by
  rcases Nat.eq_zero_or_pos m with (rfl | _)
  · simpa using deficient_one
  · rw [Deficient, properDivisors_prime_pow h]
    calc
      ∑ x ∈ Finset.map ⟨(n ^ ·), Nat.pow_right_injective h.two_le⟩ (range m), x
        = ∑ i ∈ range m, n ^ i := by simp
      _ = (n ^ m - 1) / (n - 1) := (Nat.geomSum_eq (Prime.two_le h) _)
      _ ≤ (n ^ m - 1) := Nat.div_le_self (n ^ m - 1) (n - 1)
      _ < n ^ m := sub_lt (pow_pos (Prime.pos h) m) (Nat.one_pos)
/-
**Nat._root_.IsPrimePow.deficient** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsPrimePow.deficient (h : IsPrimePow n) : Deficient n := by
  obtain ⟨p, k, hp, -, rfl⟩ := h
  exact hp.nat_prime.deficient_pow
/-
**Nat.Prime.deficient** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {n : ℕ}, Nat.Prime n → n.Deficient
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.deficient_pow`：∀ {n m : ℕ}, Nat.Prime n → (n ^ m).Deficient
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem Prime.deficient (h : Prime n) : Deficient n :=
  (pow_one n) ▸ h.deficient_pow

/-- There exists infinitely many deficient numbers -/
/-
**Nat.infinite_deficient** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：infinite_deficient : {n : Nat | n.Deficient}.Infinite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.infinite_iff_exists_gt`：∀ {α : Type u_2} [inst : LinearOrder α] [Loc
allyFiniteOrderBot α] {s : Set α} [Nonempty α],   s.Infinite ↔ ∀ (a : α), ∃ b ∈ 
s, a < b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.exists_infinite_primes`：exists_infinite_primes (n : Nat) : exists p,
 n <= p ∧ Prime p
· 使用定理 `Nat.Prime.deficient`：∀ {n : ℕ}, Nat.Prime n → n.Deficient

--- 原说明 ---
There exists infinitely many deficient numbers
-/
theorem infinite_deficient : {n : ℕ | n.Deficient}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro a
  obtain ⟨b, h1, h2⟩ := exists_infinite_primes a.succ
  exact ⟨b, h2.deficient, h1⟩
/-
**Nat.infinite_even_deficient** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：infinite_even_deficient : {n : Nat | Even n ∧ n.Deficient}.Infinite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.infinite_iff_exists_gt`：∀ {α : Type u_2} [inst : LinearOrder α] [Loc
allyFiniteOrderBot α] {s : Set α} [Nonempty α],   s.Infinite ↔ ∀ (a : α), ∃ b ∈ 
s, a < b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `Nat.Prime.deficient_pow`：∀ {n m : ℕ}, Nat.Prime n → (n ^ m).Deficient
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.lt_two_pow_self`：∀ {n : ℕ}, n < 2 ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pow_lt_pow_iff_right`：∀ {a n m : ℕ}, 1 < a → (a ^ n < a ^ m ↔ n < m)
· 使用定理 `Nat.one_lt_two`：1 < 2
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem infinite_even_deficient : {n : ℕ | Even n ∧ n.Deficient}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  use 2 ^ (n + 1)
  constructor
  · exact ⟨⟨2 ^ n, by rw [pow_succ, mul_two]⟩, prime_two.deficient_pow⟩
  · calc
      n ≤ 2 ^ n := Nat.le_of_lt n.lt_two_pow_self
      _ < 2 ^ (n + 1) := (Nat.pow_lt_pow_iff_right (Nat.one_lt_two)).mpr (lt_add_one n)
/-
**Nat.infinite_odd_deficient** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：infinite_odd_deficient : {n : Nat | Odd n ∧ n.Deficient}.Infinite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.infinite_iff_exists_gt`：∀ {α : Type u_2} [inst : LinearOrder α] [Loc
allyFiniteOrderBot α] {s : Set α} [Nonempty α],   s.Infinite ↔ ∀ (a : α), ∃ b ∈ 
s, a < b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.exists_infinite_primes`：exists_infinite_primes (n : Nat) : exists p,
 n <= p ∧ Prime p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Nat.Prime.odd_of_ne_two`：∀ {p : ℕ}, Nat.Prime p → p ≠ 2 → Odd p
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.ne_of_lt`：∀ {a b : ℕ}, a < b → a ≠ b
· 使用定理 `Nat.Prime.deficient`：∀ {n : ℕ}, Nat.Prime n → n.Deficient
-/
theorem infinite_odd_deficient : {n : ℕ | Odd n ∧ n.Deficient}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨p, ⟨_, h2⟩⟩ := exists_infinite_primes (max (n + 1) 3)
  exact ⟨p, Set.mem_ofPred.mpr ⟨Prime.odd_of_ne_two h2 (Ne.symm (ne_of_lt (by grind))),
    Prime.deficient h2⟩, by grind⟩
/-
**Nat.abundant_iff_sum_divisors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：abundant_iff_sum_divisors : Abundant n ↔ 2 * n < ∑ i in n.divisors, i
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem abundant_iff_sum_divisors : Abundant n ↔ 2 * n < ∑ i ∈ n.divisors, i := by
  grind [Abundant, sum_divisors_eq_sum_properDivisors_add_self]
/-
**Nat.abundant_iff_two_lt_abundancyIndex** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：abundant_iff_two_lt_abundancyIndex : Abundant n ↔ 2 < n.abundancyIndex
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.properDivisors_zero`：properDivisors_zero : properDivisors 0 = ∅
· 使用定理 `Nat.divisors_zero`：divisors_zero : divisors 0 = ∅
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.abundant_iff_sum_divisors`：abundant_iff_sum_divisors : Abundant n ↔ 
2 * n < ∑ i in n.divisors, i
· 使用定理 `Nat.abundancyIndex.eq_1`：∀ (n : ℕ), n.abundancyIndex = ↑(∑ i ∈ n.divisor
s, i) / ↑n
· 使用引理 `lt_div_iff₀`：lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem abundant_iff_two_lt_abundancyIndex : Abundant n ↔ 2 < n.abundancyIndex := by
  by_cases h : n = 0
  · simp [h, Abundant, abundancyIndex]
  · rw [abundant_iff_sum_divisors, abundancyIndex, lt_div_iff₀ (by positivity)]
    norm_cast
/-
**Nat.abundancyIndex_le_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：abundancyIndex_le_of_dvd (hn : n != 0) (hd : m ∣ n) : m.abundancyIndex <= 
n.abundancyIndex
参数：hn : n != 0；hd : m ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.abundancyIndex.eq_1`：∀ (n : ℕ), n.abundancyIndex = ↑(∑ i ∈ n.divisor
s, i) / ↑n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `div_mul_eq_div_div_swap`：div_mul_eq_div_div_swap : a / (b * c) = a / c /
 b
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Finset.sum_image`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst :
 AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ →
 ι}, S…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `mul_left_injective₀`：mul_left_injective₀ (hb : b != 0) : Function.Inject
ive fun a => a * b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Finset.sum_le_sum_of_subset`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] {f : ι → M}   {s t
 : Finset ι}, s ⊆…
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem abundancyIndex_le_of_dvd (hn : n ≠ 0) (hd : m ∣ n) :
    m.abundancyIndex ≤ n.abundancyIndex := by
  obtain ⟨k, hk⟩ := hd
  have hk0 : k ≠ 0 := by grind
  rw [abundancyIndex, abundancyIndex, hk, cast_mul, div_mul_eq_div_div_swap]
  refine div_le_div_of_nonneg_right ?_ m.cast_nonneg
  rw [le_div_iff₀ (by grind [cast_pos]), ← cast_mul, cast_le, sum_mul]
  exact (sum_image (f := fun i ↦ i) (mul_left_injective₀ hk0).injOn).symm.trans_le
    (sum_le_sum_of_subset (by grind [mul_dvd_mul_iff_right hk0]))
/-
**Nat.Abundant.of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Abundant`。
形式化陈述：∀ {n m : ℕ}, m.Abundant → m ∣ n → n ≠ 0 → n.Abundant
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.abundancyIndex_le_of_dvd`：abundancyIndex_le_of_dvd (hn : n != 0) (hd
 : m ∣ n) : m.abundancyIndex <= n.abundancyIndex
-/
theorem Abundant.of_dvd (h : Abundant m) (hd : m ∣ n) (hn : n ≠ 0) : Abundant n := by
  have := abundancyIndex_le_of_dvd hn hd
  grind [abundant_iff_two_lt_abundancyIndex]
/-
**Nat.Abundant.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Abundant`。
形式化陈述：∀ {n m : ℕ}, n.Abundant → m ≠ 0 → (m * n).Abundant
参数：m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.Abundant.of_dvd`：∀ {n m : ℕ}, m.Abundant → m ∣ n → n ≠ 0 → n.Abundan
t
· 使用定理 `Nat.dvd_mul_left`：∀ (a b : ℕ), a ∣ b * a
-/
theorem Abundant.mul_left (h : Abundant n) (hm : m ≠ 0) : Abundant (m * n) := by
  have hn : n ≠ 0 := by grind [not_abundant_zero]
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  exact Abundant.of_dvd h (Nat.dvd_mul_left n m) hmn
/-
**Nat.infinite_even_abundant** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：infinite_even_abundant : {n : Nat | Even n ∧ n.Abundant}.Infinite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.infinite_iff_exists_gt`：∀ {α : Type u_2} [inst : LinearOrder α] [Loc
allyFiniteOrderBot α] {s : Set α} [Nonempty α],   s.Infinite ↔ ∀ (a : α), ∃ b ∈ 
s, a < b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem infinite_even_abundant : {n : ℕ | Even n ∧ n.Abundant}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro a
  have ha : Abundant 12 := by decide
  use (2 * (a + 1)) * 12
  grind [Abundant.mul_left ha (show 2 * (a + 1) ≠ 0 by grind)]
/-
**Nat.infinite_odd_abundant** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：infinite_odd_abundant : {n : Nat | Odd n ∧ n.Abundant}.Infinite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.infinite_iff_exists_gt`：∀ {α : Type u_2} [inst : LinearOrder α] [Loc
allyFiniteOrderBot α] {s : Set α} [Nonempty α],   s.Infinite ↔ ∀ (a : α), ∃ b ∈ 
s, a < b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem infinite_odd_abundant : {n : ℕ | Odd n ∧ n.Abundant}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro a
  have ha : Abundant 945 := by decide +kernel
  use (2 * a + 1) * 945
  grind [Abundant.mul_left ha (show 2 * a + 1 ≠ 0 by grind)]

end Nat

