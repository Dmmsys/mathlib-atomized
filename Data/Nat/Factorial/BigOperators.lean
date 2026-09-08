/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Zify

/-!
# Factorial with big operators

This file contains some lemmas on factorials in combination with big operators.

While in terms of semantics they could be in the `Basic.lean` file, importing
`Algebra.BigOperators.Group.Finset` leads to a cyclic import.

-/

public section


open Finset Nat

namespace Nat

/-
**Nat.monotone_factorial** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：monotone_factorial : Monotone factorial
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.factorial_le`：factorial_le {m n} (h : m <= n) : m ! <= n !
-/
lemma monotone_factorial : Monotone factorial := fun _ _ => factorial_le

variable {α : Type*} (s : Finset α) (f : α → ℕ)
/-
**Nat.prod_factorial_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_factorial_pos : 0 < ∏ i in s, (f i)!
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
-/
theorem prod_factorial_pos : 0 < ∏ i ∈ s, (f i)! := prod_pos fun _ _ ↦ factorial_pos _
/-
**Nat.prod_factorial_dvd_factorial_sum** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_factorial_dvd_factorial_sum : (∏ i in s, (f i)!) ∣ (∑ i in s, f i)!
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用定理 `Nat.factorial_mul_factorial_dvd_factorial_add`：factorial_mul_factorial_d
vd_factorial_add (i j : Nat) : i ! * j ! ∣ (i + j)!
-/
theorem prod_factorial_dvd_factorial_sum : (∏ i ∈ s, (f i)!) ∣ (∑ i ∈ s, f i)! := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s has ih =>
    rw [prod_cons, Finset.sum_cons]
    exact (mul_dvd_mul_left _ ih).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
/-
**Nat.factorial_eq_prod_range_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), n.factorial = ∏ i ∈ Finset.range n, (i + 1)
参数：n : ℕ；i + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem factorial_eq_prod_range_add_one : ∀ n, (n)! = ∏ i ∈ range n, (i + 1)
  | 0 => rfl
  | n + 1 => by rw [factorial, prod_range_succ_comm, factorial_eq_prod_range_add_one n]

@[simp]
/-
**Nat._root_.Finset.prod_range_add_one_eq_factorial** 是 Mathlib 中的一个定理，位于命名空间 `N
at`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.prod_range_add_one_eq_factorial (n : ℕ) : ∏ i ∈ range n, (i + 1) = (n)! :=
  factorial_eq_prod_range_add_one _ |>.symm
/-
**Nat.ascFactorial_eq_prod_range** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n k : ℕ), n.ascFactorial k = ∏ i ∈ Finset.range k, (n + i)
参数：n k : ℕ；n + i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ascFactorial_eq_prod_range (n : ℕ) : ∀ k, n.ascFactorial k = ∏ i ∈ range k, (n + i)
  | 0 => rfl
  | k + 1 => by rw [ascFactorial, prod_range_succ_comm, ascFactorial_eq_prod_range n k]
/-
**Nat.descFactorial_eq_prod_range** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n k : ℕ), n.descFactorial k = ∏ i ∈ Finset.range k, (n - i)
参数：n k : ℕ；n - i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem descFactorial_eq_prod_range (n : ℕ) : ∀ k, n.descFactorial k = ∏ i ∈ range k, (n - i)
  | 0 => rfl
  | k + 1 => by rw [descFactorial, prod_range_succ_comm, descFactorial_eq_prod_range n k]

/-- `k!` divides the product of any `k` consecutive integers. -/
/-
**Nat.factorial_coe_dvd_prod** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：factorial_coe_dvd_prod (k : Nat) (n : Int) : (k ! : Int) ∣ ∏ i in range k,
 (n + i)
参数：k : Nat；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.dvd_iff_emod_eq_zero`：∀ {a b : ℤ}, a ∣ b ↔ b % a = 0
· 使用定理 `Finset.prod_int_mod`：prod_int_mod (s : Finset ι) (n : Int) (f : ι -> Int
) : (∏ i in s, f i) % n = (∏ i in s, f i % n) % n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.emod_add_emod`：∀ (m n k : ℤ), (m % n + k) % n = (m + k) % n
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Int.eq_ofNat_of_zero_le`：∀ {a : ℤ}, 0 ≤ a → ∃ n, a = ↑n
· 使用定理 `Nat.factorial_dvd_ascFactorial`：factorial_dvd_ascFactorial (n k : Nat) :
 k ! ∣ n.ascFactorial k
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.ascFactorial_eq_prod_range`：∀ (n k : ℕ), n.ascFactorial k = ∏ i ∈ Fi
nset.range k, (n + i)
· 使用定理 `Finset.prod_natCast`：prod_natCast (s : Finset ι) (f : ι -> Nat) : ↑(∏ i 
in s, f i : Nat) = ∏ i in s, (f i : R)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n

--- 原说明 ---
`k!` divides the product of any `k` consecutive integers.
-/
lemma factorial_coe_dvd_prod (k : ℕ) (n : ℤ) : (k ! : ℤ) ∣ ∏ i ∈ range k, (n + i) := by
  rw [Int.dvd_iff_emod_eq_zero, Finset.prod_int_mod]
  simp_rw [← Int.emod_add_emod n]
  have hn : 0 ≤ n % k ! := Int.emod_nonneg n <| Int.natCast_ne_zero.mpr k.factorial_ne_zero
  obtain ⟨x, hx⟩ := Int.eq_ofNat_of_zero_le hn
  have hdivk := x.factorial_dvd_ascFactorial k
  zify [x.ascFactorial_eq_prod_range k] at hdivk
  rwa [← Finset.prod_int_mod, ← Int.dvd_iff_emod_eq_zero, hx]

end Nat

