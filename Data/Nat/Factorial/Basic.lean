/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes, Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# Factorial and variants

This file defines the factorial, along with the ascending and descending variants.
For the proof that the factorial of `n` counts the permutations of an `n`-element set,
see `Fintype.card_perm`.

## Main declarations

* `Nat.factorial`: The factorial.
* `Nat.ascFactorial`: The ascending factorial. It is the product of natural numbers from `n` to
  `n + k - 1`.
* `Nat.descFactorial`: The descending factorial. It is the product of natural numbers from
  `n - k + 1` to `n`.
-/

@[expose] public section


namespace Nat

/-- `Nat.factorial n` is the factorial of `n`. -/
@[wikidata Q120976]
/-
**Nat.factorial** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Nat.factorial n` is the factorial of `n`.
-/
def factorial : ℕ → ℕ
  | 0 => 1
  | succ n => succ n * factorial n

/-- factorial notation `(n)!` for `Nat.factorial n`.
In Lean, names can end with exclamation marks (e.g. `List.get!`), so you cannot write
`n!` in Lean, but must write `(n)!` or `n !` instead. The former is preferred, since
Lean can confuse the `!` in `n !` as the (prefix) Boolean negation operation in some
cases.
For numerals the parentheses are not required, so e.g. `0!` or `1!` work fine. -/
scoped notation:10000 n "!" => Nat.factorial n

section Factorial

variable {m n : ℕ}

/-
**Nat.factorial_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.factorial 0 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem factorial_zero : 0! = 1 :=
  rfl
/-
**Nat.factorial_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem factorial_succ (n : ℕ) : (n + 1)! = (n + 1) * n ! :=
  rfl
/-
**Nat.factorial_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.factorial 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem factorial_one : 1! = 1 :=
  rfl
/-
**Nat.factorial_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.factorial 2 = 2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem factorial_two : 2! = 2 :=
  rfl
/-
**Nat.mul_factorial_pred** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mul_factorial_pred (hn : n != 0) : n * (n - 1)! = n !
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
theorem mul_factorial_pred (hn : n ≠ 0) : n * (n - 1)! = n ! :=
  Nat.sub_add_cancel (one_le_iff_ne_zero.mpr hn) ▸ rfl
/-
**Nat.factorial_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), 0 < n.factorial
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem factorial_pos : ∀ n, 0 < n !
  | 0 => Nat.zero_lt_one
  | succ n => Nat.mul_pos (succ_pos _) (factorial_pos n)
/-
**Nat.factorial_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorial_ne_zero (n : Nat) : n ! != 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
-/
theorem factorial_ne_zero (n : ℕ) : n ! ≠ 0 :=
  ne_of_gt (factorial_pos _)

@[gcongr]
/-
**Nat.factorial_dvd_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorial_dvd_factorial {m n} (h : m <= n) : m ! ∣ n !
参数：h : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_refl`：∀ (a : ℕ), a ∣ a
· 使用定理 `Nat.dvd_trans`：∀ {a b c : ℕ}, a ∣ b → b ∣ c → a ∣ c
· 使用定理 `Nat.dvd_mul_left`：∀ (a b : ℕ), a ∣ b * a
-/
theorem factorial_dvd_factorial {m n} (h : m ≤ n) : m ! ∣ n ! := by
  induction h with
  | refl => exact Nat.dvd_refl _
  | step _ ih => exact Nat.dvd_trans ih (Nat.dvd_mul_left _ _)
/-
**Nat.dvd_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m n : ℕ}, 0 < m → m ≤ n → m ∣ n.factorial
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_trans`：∀ {a b c : ℕ}, a ∣ b → b ∣ c → a ∣ c
· 使用定理 `Nat.dvd_mul_right`：∀ (a b : ℕ), a ∣ a * b
· 使用定理 `Nat.factorial_dvd_factorial`：factorial_dvd_factorial {m n} (h : m <= n) 
: m ! ∣ n !
-/
theorem dvd_factorial : ∀ {m n}, 0 < m → m ≤ n → m ∣ n !
  | succ _, _, _, h => Nat.dvd_trans (Nat.dvd_mul_right _ _) (factorial_dvd_factorial h)

@[mono, gcongr]
/-
**Nat.factorial_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorial_le {m n} (h : m <= n) : m ! <= n !
参数：h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `Nat.factorial_dvd_factorial`：factorial_dvd_factorial {m n} (h : m <= n) 
: m ! ∣ n !
-/
theorem factorial_le {m n} (h : m ≤ n) : m ! ≤ n ! :=
  le_of_dvd (factorial_pos _) (factorial_dvd_factorial h)
/-
**Nat.factorial_mul_pow_le_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m n : ℕ}, m.factorial * (m + 1) ^ n ≤ (m + n).factorial
参数：m + 1；m + n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem factorial_mul_pow_le_factorial : ∀ {m n : ℕ}, m ! * (m + 1) ^ n ≤ (m + n)!
  | m, 0 => by simp
  | m, n + 1 => by
    rw [← Nat.add_assoc, factorial_succ, Nat.mul_comm (_ + 1), Nat.pow_succ, ← Nat.mul_assoc]
    exact Nat.mul_le_mul factorial_mul_pow_le_factorial (succ_le_succ (le_add_right _ _))
/-
**Nat.factorial_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorial_lt (hn : 0 < n) : n ! < m ! ↔ n < m
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Nat.not_le_of_gt`：∀ {n m : ℕ}, n > m → ¬n ≤ m
· 使用定理 `Nat.factorial_le`：factorial_le {m n} (h : m <= n) : m ! <= n !
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用定理 `Nat.lt_add_left_iff_pos`：∀ {n k : ℕ}, n < k + n ↔ 0 < k
· 使用定理 `Nat.mul_pos`：∀ {n m : ℕ}, 0 < n → 0 < m → 0 < n * m
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Nat.lt_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n < m
-/
theorem factorial_lt (hn : 0 < n) : n ! < m ! ↔ n < m := by
  refine ⟨fun h => not_le.mp fun hmn => Nat.not_le_of_gt h (factorial_le hmn), fun h => ?_⟩
  have : ∀ {n}, 0 < n → n ! < (n + 1)! := by
    intro k hk
    rw [factorial_succ, succ_mul, Nat.lt_add_left_iff_pos]
    exact Nat.mul_pos hk k.factorial_pos
  induction h generalizing hn with
  | refl => exact this hn
  | step hnk ih => exact lt_trans (ih hn) <| this <| lt_trans hn <| lt_of_succ_le hnk

@[gcongr]
/-
**Nat.factorial_lt_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：factorial_lt_of_lt {m n : Nat} (hn : 0 < n) (h : n < m) : n ! < m !
参数：hn : 0 < n；h : n < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.factorial_lt`：factorial_lt (hn : 0 < n) : n ! < m ! ↔ n < m
-/
lemma factorial_lt_of_lt {m n : ℕ} (hn : 0 < n) (h : n < m) : n ! < m ! := (factorial_lt hn).mpr h
/-
**Nat.one_lt_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, 1 < n.factorial ↔ 1 < n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.factorial_lt`：factorial_lt (hn : 0 < n) : n ! < m ! ↔ n < m
-/
@[simp] lemma one_lt_factorial : 1 < n ! ↔ 1 < n := factorial_lt Nat.one_pos

@[simp]
/-
**Nat.factorial_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorial_eq_one : n ! = 1 ↔ n <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.one_lt_factorial`：∀ {n : ℕ}, 1 < n.factorial ↔ 1 < n
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem factorial_eq_one : n ! = 1 ↔ n ≤ 1 := by
  constructor
  · intro h
    rw [← not_lt, ← one_lt_factorial, h]
    apply lt_irrefl
  · rintro (_ | _ | _) <;> rfl
/-
**Nat.factorial_inj** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorial_inj (hn : 1 < n) : n ! = m ! ↔ n = m
参数：hn : 1 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.factorial_lt`：factorial_lt (hn : 0 < n) : n ! < m ! ↔ n < m
· 使用定理 `Nat.lt_of_succ_lt`：∀ {n m : ℕ}, n.succ < m → n < m
· 使用定理 `Nat.one_lt_factorial`：∀ {n : ℕ}, 1 < n.factorial ↔ 1 < n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem factorial_inj (hn : 1 < n) : n ! = m ! ↔ n = m := by
  refine ⟨fun h => ?_, congr_arg _⟩
  obtain hnm | rfl | hnm := lt_trichotomy n m
  · rw [← factorial_lt <| lt_of_succ_lt hn, h] at hnm
    cases lt_irrefl _ hnm
  · rfl
  rw [← one_lt_factorial, h, one_lt_factorial] at hn
  rw [← factorial_lt <| lt_of_succ_lt hn, h] at hnm
  cases lt_irrefl _ hnm
/-
**Nat.factorial_inj'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorial_inj' (h : 1 < n ∨ 1 < m) : n ! = m ! ↔ n = m
参数：h : 1 < n ∨ 1 < m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.factorial_inj`：factorial_inj (hn : 1 < n) : n ! = m ! ↔ n = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem factorial_inj' (h : 1 < n ∨ 1 < m) : n ! = m ! ↔ n = m := by
  obtain hn | hm := h
  · exact factorial_inj hn
  · rw [eq_comm, factorial_inj hm, eq_comm]
/-
**Nat.self_le_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), n ≤ n.factorial
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.le_mul_of_pos_right`：∀ {m : ℕ} (n : ℕ), 0 < m → n ≤ n * m
· 使用定理 `Nat.one_le_of_lt`：∀ {a b : ℕ}, a < b → 1 ≤ b
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
-/
theorem self_le_factorial : ∀ n : ℕ, n ≤ n !
  | 0 => Nat.zero_le _
  | k + 1 => Nat.le_mul_of_pos_right _ (Nat.one_le_of_lt k.factorial_pos)
/-
**Nat.lt_factorial_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_factorial_self {n : Nat} (hi : 3 <= n) : n < n !
参数：hi : 3 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_pred_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m.pred
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_mul_iff_one_lt_right`：∀ {a b : ℕ}, 0 < a → (a < a * b ↔ 1 < b)
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Nat.self_le_factorial`：∀ (n : ℕ), n ≤ n.factorial
-/
theorem lt_factorial_self {n : ℕ} (hi : 3 ≤ n) : n < n ! := by
  have : 0 < n := by lia
  have hn : 1 < pred n := le_pred_of_lt (succ_le_iff.mp hi)
  rw [← succ_pred_eq_of_pos ‹0 < n›, factorial_succ]
  exact (Nat.lt_mul_iff_one_lt_right (pred n).succ_pos).2
    ((Nat.lt_of_lt_of_le hn (self_le_factorial _)))
/-
**Nat.add_factorial_succ_lt_factorial_add_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_factorial_succ_lt_factorial_add_succ {i : Nat} (n : Nat) (hi : 2 <= i)
 : i + (n + 1)! < (i + n + 1)!
参数：n : Nat；hi : 2 <= i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `Nat.add_mul`：∀ (n m k : ℕ), (n + m) * k = n * k + m * k
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `Nat.self_le_factorial`：∀ (n : ℕ), n ≤ n.factorial
· 使用定理 `Nat.add_lt_add_of_lt_of_le`：∀ {a b c d : ℕ}, a < b → c ≤ d → a + c < b +
 d
· 使用定理 `Nat.lt_of_le_of_lt`：∀ {n m k : ℕ}, n ≤ m → m < k → n < k
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_mul_iff_one_lt_right`：∀ {a b : ℕ}, 0 < a → (a < a * b ↔ 1 < b)
· 使用定理 `Nat.factorial_le`：factorial_le {m n} (h : m <= n) : m ! <= n !
-/
theorem add_factorial_succ_lt_factorial_add_succ {i : ℕ} (n : ℕ) (hi : 2 ≤ i) :
    i + (n + 1)! < (i + n + 1)! := by
  rw [factorial_succ (i + _), Nat.add_mul, Nat.one_mul]
  have := (i + n).self_le_factorial
  refine Nat.add_lt_add_of_lt_of_le (Nat.lt_of_le_of_lt ?_ ((Nat.lt_mul_iff_one_lt_right ?_).2 ?_))
    (factorial_le ?_) <;> lia
/-
**Nat.add_factorial_lt_factorial_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_factorial_lt_factorial_add {i n : Nat} (hi : 2 <= i) (hn : 1 <= n) : i
 + n ! < (i + n)!
参数：hi : 2 <= i；hn : 1 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorial_one`：Nat.factorial 1 = 1
· 使用定理 `Nat.lt_factorial_self`：lt_factorial_self {n : Nat} (hi : 3 <= n) : n < n
 !
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_factorial_succ_lt_factorial_add_succ`：add_factorial_succ_lt_fact
orial_add_succ {i : Nat} (n : Nat) (hi : 2 <= i) : i + (n + 1)! < (i + n + 1)!
-/
theorem add_factorial_lt_factorial_add {i n : ℕ} (hi : 2 ≤ i) (hn : 1 ≤ n) :
    i + n ! < (i + n)! := by
  cases hn
  · rw [factorial_one]
    exact lt_factorial_self (succ_le_succ hi)
  exact add_factorial_succ_lt_factorial_add_succ _ hi
/-
**Nat.add_factorial_succ_le_factorial_add_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_factorial_succ_le_factorial_add_succ (i : Nat) (n : Nat) : i + (n + 1)
! <= (i + (n + 1))!
参数：i : Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.add_factorial_succ_lt_factorial_add_succ`：add_factorial_succ_lt_fact
orial_add_succ {i : Nat} (n : Nat) (hi : 2 <= i) : i + (n + 1)! < (i + n + 1)!
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `Nat.add_mul`：∀ (n m k : ℕ), (n + m) * k = n * k + m * k
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Nat.add_le_add_iff_right`：∀ {m k n : ℕ}, m + n ≤ k + n ↔ m ≤ k
· 使用定理 `Nat.mul_pos`：∀ {n m : ℕ}, 0 < n → 0 < m → 0 < n * m
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem add_factorial_succ_le_factorial_add_succ (i : ℕ) (n : ℕ) :
    i + (n + 1)! ≤ (i + (n + 1))! := by
  cases (le_or_gt (2 : ℕ) i)
  · rw [← Nat.add_assoc]
    apply Nat.le_of_lt
    apply add_factorial_succ_lt_factorial_add_succ
    assumption
  · match i with
    | 0 => simp
    | 1 =>
      rw [← Nat.add_assoc, factorial_succ (1 + n), Nat.add_mul, Nat.one_mul, Nat.add_comm 1 n,
        Nat.add_le_add_iff_right]
      exact Nat.mul_pos n.succ_pos n.succ.factorial_pos
    | succ (succ n) => contradiction
/-
**Nat.add_factorial_le_factorial_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_factorial_le_factorial_add (i : Nat) {n : Nat} (n1 : 1 <= n) : i + n !
 <= (i + n)!
参数：i : Nat；n1 : 1 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.self_le_factorial`：∀ (n : ℕ), n ≤ n.factorial
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_factorial_succ_le_factorial_add_succ`：add_factorial_succ_le_fact
orial_add_succ (i : Nat) (n : Nat) : i + (n + 1)! <= (i + (n + 1))!
-/
theorem add_factorial_le_factorial_add (i : ℕ) {n : ℕ} (n1 : 1 ≤ n) : i + n ! ≤ (i + n)! := by
  rcases n1 with - | @h
  · exact self_le_factorial _
  exact add_factorial_succ_le_factorial_add_succ i h
/-
**Nat.factorial_mul_pow_sub_le_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorial_mul_pow_sub_le_factorial {n m : Nat} (hnm : n <= m) : n ! * n ^ 
(m - n) <= m !
参数：hnm : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `Nat.pow_le_pow_left`：∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
· 使用定理 `Nat.factorial_mul_pow_le_factorial`：∀ {m n : ℕ}, m.factorial * (m + 1) ^
 n ≤ (m + n).factorial
-/
theorem factorial_mul_pow_sub_le_factorial {n m : ℕ} (hnm : n ≤ m) : n ! * n ^ (m - n) ≤ m ! := by
  calc
    _ ≤ n ! * (n + 1) ^ (m - n) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left n.le_succ _)
    _ ≤ _ := by simpa [hnm] using @Nat.factorial_mul_pow_le_factorial n (m - n)
/-
**Nat.factorial_le_pow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：factorial_le_pow : forall n, n ! <= n ^ n | 0 => le_refl _ | n + 1 => calc
 _ <= (n + 1) * n ^ n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma factorial_le_pow : ∀ n, n ! ≤ n ^ n
  | 0 => le_refl _
  | n + 1 =>
    calc
      _ ≤ (n + 1) * n ^ n := Nat.mul_le_mul_left _ n.factorial_le_pow
      _ ≤ (n + 1) * (n + 1) ^ n := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left n.le_succ _)
      _ = _ := by rw [pow_succ']

end Factorial

/-! ### Ascending and descending factorials -/


section AscFactorial

/-- `n.ascFactorial k = n (n + 1) ⋯ (n + k - 1)`. This is closely related to `ascPochhammer`, but
much less general. -/
/-
**Nat.ascFactorial** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`n.ascFactorial k = n (n + 1) ⋯ (n + k - 1)`. This is closely related to `ascPoc
hhammer`, but
much less general.
-/
def ascFactorial (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (n + k) * ascFactorial n k

@[simp]
/-
**Nat.ascFactorial_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ascFactorial_zero (n : Nat) : n.ascFactorial 0 = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ascFactorial_zero (n : ℕ) : n.ascFactorial 0 = 1 :=
  rfl
/-
**Nat.ascFactorial_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ascFactorial_succ {n k : Nat} : n.ascFactorial k.succ = (n + k) * n.ascFac
torial k
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ascFactorial_succ {n k : ℕ} : n.ascFactorial k.succ = (n + k) * n.ascFactorial k :=
  rfl
/-
**Nat.zero_ascFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (k : ℕ), Nat.ascFactorial 0 k.succ = 0
参数：k : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_ascFactorial : ∀ (k : ℕ), (0 : ℕ).ascFactorial k.succ = 0
  | 0 => by
    rw [ascFactorial_succ, ascFactorial_zero, Nat.zero_add, Nat.zero_mul]
  | (k + 1) => by
    rw [ascFactorial_succ, zero_ascFactorial k, Nat.mul_zero]

@[simp]
/-
**Nat.one_ascFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (k : ℕ), Nat.ascFactorial 1 k = k.factorial
参数：k : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_ascFactorial : ∀ (k : ℕ), (1 : ℕ).ascFactorial k = k.factorial
  | 0 => ascFactorial_zero 1
  | (k + 1) => by
    rw [ascFactorial_succ, one_ascFactorial k, Nat.add_comm, factorial_succ]
/-
**Nat.succ_ascFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n k : ℕ), n * n.succ.ascFactorial k = (n + k) * n.ascFactorial k
参数：n k : ℕ；n + k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem succ_ascFactorial (n : ℕ) :
    ∀ k, n * n.succ.ascFactorial k = (n + k) * n.ascFactorial k
  | 0 => by rw [Nat.add_zero, ascFactorial_zero, ascFactorial_zero]
  | k + 1 => by rw [ascFactorial, Nat.mul_left_comm, succ_ascFactorial n k, ascFactorial, succ_add,
    ← Nat.add_assoc]

/-- `(n + 1).ascFactorial k = (n + k) ! / n !` but without ℕ-division. See
`Nat.ascFactorial_eq_div` for the version with ℕ-division. -/
/-
**Nat.factorial_mul_ascFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n k : ℕ), n.factorial * (n + 1).ascFactorial k = (n + k).factorial
参数：n k : ℕ；n + 1；n + k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(n + 1).ascFactorial k = (n + k) ! / n !` but without ℕ-division. See
`Nat.ascFactorial_eq_div` for the version with ℕ-division.
-/
theorem factorial_mul_ascFactorial (n : ℕ) : ∀ k, n ! * (n + 1).ascFactorial k = (n + k)!
  | 0 => by rw [ascFactorial_zero, Nat.add_zero, Nat.mul_one]
  | k + 1 => by
    rw [ascFactorial_succ, ← Nat.add_assoc, factorial_succ, Nat.mul_comm (n + 1 + k),
      ← Nat.mul_assoc, factorial_mul_ascFactorial n k, Nat.mul_comm, Nat.add_right_comm]

/-- `n.ascFactorial k = (n + k - 1)! / (n - 1)!` for `n > 0` but without ℕ-division. See
`Nat.ascFactorial_eq_div` for the version with ℕ-division. Consider using
`factorial_mul_ascFactorial` to avoid complications of ℕ-subtraction. -/
/-
**Nat.factorial_mul_ascFactorial'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorial_mul_ascFactorial' (n k : Nat) (h : 0 < n) : (n - 1)! * n.ascFact
orial k = (n + k - 1)!
参数：n k : Nat；h : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_add_comm`：∀ {n m k : ℕ}, k ≤ n → n + m - k = n - k + m
· 使用定理 `Nat.sub_one`：∀ (n : ℕ), n - 1 = n.pred
· 使用定理 `Nat.eq_add_of_sub_eq`：∀ {a b c : ℕ}, b ≤ a → a - b = c → a = c + b
· 使用定理 `Nat.factorial_mul_ascFactorial`：∀ (n k : ℕ), n.factorial * (n + 1).ascFa
ctorial k = (n + k).factorial

--- 原说明 ---
`n.ascFactorial k = (n + k - 1)! / (n - 1)!` for `n > 0` but without ℕ-division.
 See
`Nat.ascFactorial_eq_div` for the version with ℕ-division. Consider using
`factorial_mul_ascFactorial` to avoid complications of ℕ-subtraction.
-/
theorem factorial_mul_ascFactorial' (n k : ℕ) (h : 0 < n) :
    (n - 1)! * n.ascFactorial k = (n + k - 1)! := by
  rw [Nat.sub_add_comm h, Nat.sub_one]
  nth_rw 2 [Nat.eq_add_of_sub_eq h rfl]
  rw [Nat.sub_one, factorial_mul_ascFactorial]
/-
**Nat.ascFactorial_mul_ascFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ascFactorial_mul_ascFactorial (n l k : Nat) : n.ascFactorial l * (n + l).a
scFactorial k = n.ascFactorial (l + k)
参数：n l k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_ascFactorial`：∀ (k : ℕ), Nat.ascFactorial 0 k.succ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_mul`：∀ (n : ℕ), 0 * n = 0
· 使用定理 `Nat.add_right_comm`：∀ (n m k : ℕ), n + m + k = n + k + m
· 使用定理 `Nat.mul_left_cancel`：∀ {n m k : ℕ}, 0 < n → n * m = n * k → m = k
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `Nat.factorial_mul_ascFactorial`：∀ (n k : ℕ), n.factorial * (n + 1).ascFa
ctorial k = (n + k).factorial
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
-/
theorem ascFactorial_mul_ascFactorial (n l k : ℕ) :
    n.ascFactorial l * (n + l).ascFactorial k = n.ascFactorial (l + k) := by
  cases n with
  | zero =>
    cases l
    · simp only [ascFactorial_zero, Nat.add_zero, Nat.one_mul, Nat.zero_add]
    · simp only [Nat.add_right_comm, zero_ascFactorial, Nat.zero_add, Nat.zero_mul]
  | succ n' =>
    apply Nat.mul_left_cancel (factorial_pos n')
    simp only [Nat.add_assoc, ← Nat.mul_assoc, factorial_mul_ascFactorial]
    rw [Nat.add_comm 1 l, ← Nat.add_assoc, factorial_mul_ascFactorial, Nat.add_assoc]

/-- Avoid in favor of `Nat.factorial_mul_ascFactorial` if you can. ℕ-division isn't worth it. -/
/-
**Nat.ascFactorial_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ascFactorial_eq_div (n k : Nat) : (n + 1).ascFactorial k = (n + k)! / n !
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_div_of_mul_eq_right`：∀ {c a b : ℕ}, c ≠ 0 → c * a = b → a = b / c
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Nat.factorial_mul_ascFactorial`：∀ (n k : ℕ), n.factorial * (n + 1).ascFa
ctorial k = (n + k).factorial

--- 原说明 ---
Avoid in favor of `Nat.factorial_mul_ascFactorial` if you can. ℕ-division isn't 
worth it.
-/
theorem ascFactorial_eq_div (n k : ℕ) : (n + 1).ascFactorial k = (n + k)! / n ! :=
  Nat.eq_div_of_mul_eq_right n.factorial_ne_zero (factorial_mul_ascFactorial _ _)

/-- Avoid in favor of `Nat.factorial_mul_ascFactorial'` if you can. ℕ-division isn't worth it. -/
/-
**Nat.ascFactorial_eq_div'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ascFactorial_eq_div' (n k : Nat) (h : 0 < n) : n.ascFactorial k = (n + k -
 1)! / (n - 1)!
参数：n k : Nat；h : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_div_of_mul_eq_right`：∀ {c a b : ℕ}, c ≠ 0 → c * a = b → a = b / c
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Nat.factorial_mul_ascFactorial'`：factorial_mul_ascFactorial' (n k : Nat)
 (h : 0 < n) : (n - 1)! * n.ascFactorial k = (n + k - 1)!

--- 原说明 ---
Avoid in favor of `Nat.factorial_mul_ascFactorial'` if you can. ℕ-division isn't
 worth it.
-/
theorem ascFactorial_eq_div' (n k : ℕ) (h : 0 < n) :
    n.ascFactorial k = (n + k - 1)! / (n - 1)! :=
  Nat.eq_div_of_mul_eq_right (n - 1).factorial_ne_zero (factorial_mul_ascFactorial' _ _ h)
/-
**Nat.ascFactorial_of_sub** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ascFactorial_of_sub {n k : Nat} : (n - k) * (n - k + 1).ascFactorial k = (
n - k).ascFactorial (k + 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.succ_ascFactorial`：∀ (n k : ℕ), n * n.succ.ascFactorial k = (n + k) 
* n.ascFactorial k
· 使用定理 `Nat.ascFactorial_succ`：ascFactorial_succ {n k : Nat} : n.ascFactorial k.
succ = (n + k) * n.ascFactorial k
-/
theorem ascFactorial_of_sub {n k : ℕ} :
    (n - k) * (n - k + 1).ascFactorial k = (n - k).ascFactorial (k + 1) := by
  rw [succ_ascFactorial, ascFactorial_succ]

@[gcongr]
/-
**Nat.ascFactorial_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ascFactorial_le (k : Nat) {n m : Nat} (h : n <= m) : n.ascFactorial k <= m
.ascFactorial k
参数：k : Nat；h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.mul_le_mul`：∀ {n₁ m₁ n₂ m₂ : ℕ}, n₁ ≤ n₂ → m₁ ≤ m₂ → n₁ * m₁ ≤ n₂ * 
m₂
-/
theorem ascFactorial_le (k : ℕ) {n m : ℕ} (h : n ≤ m) :
    n.ascFactorial k ≤ m.ascFactorial k := by
  induction k with
  | zero => rfl
  | succ k ih => exact Nat.mul_le_mul (by lia) ih
/-
**Nat.pow_succ_le_ascFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n k : ℕ), n ^ k ≤ n.ascFactorial k
参数：n k : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_succ_le_ascFactorial (n : ℕ) : ∀ k : ℕ, n ^ k ≤ n.ascFactorial k
  | 0 => by rw [ascFactorial_zero, Nat.pow_zero]
  | k + 1 => by
    rw [Nat.pow_succ, Nat.mul_comm, ascFactorial_succ, ← succ_ascFactorial]
    exact Nat.mul_le_mul (Nat.le_refl n)
      (Nat.le_trans (Nat.pow_le_pow_left (le_succ n) k) (pow_succ_le_ascFactorial n.succ k))
/-
**Nat.pow_lt_ascFactorial'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pow_lt_ascFactorial' (n k : Nat) : (n + 1) ^ (k + 2) < (n + 1).ascFactoria
l (k + 2)
参数：n k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_succ`：∀ (n m : ℕ), n ^ m.succ = n ^ m * n
· 使用定理 `Nat.ascFactorial.eq_2`：∀ (n n_1 : ℕ), n.ascFactorial n_1.succ = (n + n_1
) * n.ascFactorial n_1
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Nat.mul_lt_mul_of_lt_of_le'`：∀ {a c b d : ℕ}, a < c → b ≤ d → 0 < b → a 
* b < c * d
· 使用定理 `Nat.lt_add_of_pos_right`：∀ {k n : ℕ}, 0 < k → n < n + k
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.pow_succ_le_ascFactorial`：∀ (n k : ℕ), n ^ k ≤ n.ascFactorial k
· 使用定理 `Nat.pow_pos`：∀ {a n : ℕ}, 0 < a → 0 < a ^ n
-/
theorem pow_lt_ascFactorial' (n k : ℕ) : (n + 1) ^ (k + 2) < (n + 1).ascFactorial (k + 2) := by
  rw [Nat.pow_succ, ascFactorial, Nat.mul_comm]
  exact Nat.mul_lt_mul_of_lt_of_le' (Nat.lt_add_of_pos_right k.succ_pos)
    (pow_succ_le_ascFactorial n.succ _) (Nat.pow_pos n.succ_pos)
/-
**Nat.pow_lt_ascFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ) {k : ℕ}, 2 ≤ k → (n + 1) ^ k < (n + 1).ascFactorial k
参数：n : ℕ；n + 1；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `Nat.pow_lt_ascFactorial'`：pow_lt_ascFactorial' (n k : Nat) : (n + 1) ^ (
k + 2) < (n + 1).ascFactorial (k + 2)
-/
theorem pow_lt_ascFactorial (n : ℕ) : ∀ {k : ℕ}, 2 ≤ k → (n + 1) ^ k < (n + 1).ascFactorial k
  | 0 => by rintro ⟨⟩
  | 1 => by intro; contradiction
  | k + 2 => fun _ => pow_lt_ascFactorial' n k
/-
**Nat.ascFactorial_le_pow_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n k : ℕ), (n + 1).ascFactorial k ≤ (n + k) ^ k
参数：n k : ℕ；n + 1；n + k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ascFactorial_le_pow_add (n : ℕ) : ∀ k : ℕ, (n + 1).ascFactorial k ≤ (n + k) ^ k
  | 0 => by rw [ascFactorial_zero, Nat.pow_zero]
  | k + 1 => by
    rw [ascFactorial_succ, Nat.pow_succ, Nat.mul_comm, ← Nat.add_assoc, Nat.add_right_comm n 1 k]
    exact Nat.mul_le_mul_right _
      (Nat.le_trans (ascFactorial_le_pow_add _ k) (Nat.pow_le_pow_left (le_succ _) _))
/-
**Nat.ascFactorial_le_factorial_mul_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ascFactorial_le_factorial_mul_pow (n k : Nat) : n.ascFactorial k <= k ! * 
n ^ k
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ascFactorial_le_factorial_mul_pow (n k : ℕ) : n.ascFactorial k ≤ k ! * n ^ k :=
  match k with
  | 0 => by simp
  | j + 1 => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [zero_ascFactorial]
    rw [ascFactorial_succ, factorial_succ, pow_succ',
      Nat.mul_assoc (j + 1), Nat.mul_left_comm j !, ← Nat.mul_assoc (j + 1)]
    refine Nat.mul_le_mul ?_ (ascFactorial_le_factorial_mul_pow n j)
    rw [add_one_mul, Nat.add_comm, Nat.add_le_add_iff_right]
    exact Nat.le_mul_of_pos_right j hn
/-
**Nat.ascFactorial_lt_pow_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ) {k : ℕ}, 2 ≤ k → (n + 1).ascFactorial k < (n + k) ^ k
参数：n : ℕ；n + 1；n + k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_succ`：∀ (n m : ℕ), n ^ m.succ = n ^ m * n
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Nat.ascFactorial_succ`：ascFactorial_succ {n k : Nat} : n.ascFactorial k.
succ = (n + k) * n.ascFactorial k
· 使用定理 `Nat.succ_add_eq_add_succ`：∀ (a b : ℕ), a.succ + b = a + b.succ
· 使用定理 `Nat.mul_lt_mul_of_le_of_lt`：∀ {a c b d : ℕ}, a ≤ c → b < d → 0 < c → a *
 b < c * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.lt_of_le_of_lt`：∀ {n m k : ℕ}, n ≤ m → m < k → n < k
· 使用定理 `Nat.ascFactorial_le_pow_add`：∀ (n k : ℕ), (n + 1).ascFactorial k ≤ (n + 
k) ^ k
· 使用定理 `Nat.pow_lt_pow_left`：∀ {a b n : ℕ}, a < b → n ≠ 0 → a ^ n < b ^ n
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
theorem ascFactorial_lt_pow_add (n : ℕ) : ∀ {k : ℕ}, 2 ≤ k → (n + 1).ascFactorial k < (n + k) ^ k
  | 0 => by rintro ⟨⟩
  | 1 => by intro; contradiction
  | k + 2 => fun _ => by
    rw [Nat.pow_succ, Nat.mul_comm, ascFactorial_succ, succ_add_eq_add_succ n (k + 1)]
    exact Nat.mul_lt_mul_of_le_of_lt (le_refl _) (Nat.lt_of_le_of_lt (ascFactorial_le_pow_add n _)
      (Nat.pow_lt_pow_left (Nat.lt_succ_self _) k.succ_ne_zero)) (succ_pos _)
/-
**Nat.ascFactorial_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ascFactorial_pos (n k : Nat) : 0 < (n + 1).ascFactorial k
参数：n k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Nat.pow_pos`：∀ {a n : ℕ}, 0 < a → 0 < a ^ n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.pow_succ_le_ascFactorial`：∀ (n k : ℕ), n ^ k ≤ n.ascFactorial k
-/
theorem ascFactorial_pos (n k : ℕ) : 0 < (n + 1).ascFactorial k :=
  Nat.lt_of_lt_of_le (Nat.pow_pos n.succ_pos) (pow_succ_le_ascFactorial (n + 1) k)

end AscFactorial

section DescFactorial

/-- `n.descFactorial k = n! / (n - k)!` (as seen in `Nat.descFactorial_eq_div`), but
implemented recursively to allow for "quick" computation when using `norm_num`. This is closely
related to `descPochhammer`, but much less general. -/
/-
**Nat.descFactorial** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`n.descFactorial k = n! / (n - k)!` (as seen in `Nat.descFactorial_eq_div`), but
implemented recursively to allow for "quick" computation when using `norm_num`. 
This is closely
related to `descPochhammer`, but much less general.
-/
def descFactorial (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => (n - k) * descFactorial n k

@[simp]
/-
**Nat.descFactorial_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：descFactorial_zero (n : Nat) : n.descFactorial 0 = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem descFactorial_zero (n : ℕ) : n.descFactorial 0 = 1 :=
  rfl

@[simp]
/-
**Nat.descFactorial_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：descFactorial_succ (n k : Nat) : n.descFactorial (k + 1) = (n - k) * n.des
cFactorial k
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem descFactorial_succ (n k : ℕ) : n.descFactorial (k + 1) = (n - k) * n.descFactorial k :=
  rfl
/-
**Nat.zero_descFactorial_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：zero_descFactorial_succ (k : Nat) : (0 : Nat).descFactorial (k + 1) = 0
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.descFactorial_succ`：descFactorial_succ (n k : Nat) : n.descFactorial
 (k + 1) = (n - k) * n.descFactorial k
· 使用定理 `Nat.zero_sub`：∀ (n : ℕ), 0 - n = 0
· 使用定理 `Nat.zero_mul`：∀ (n : ℕ), 0 * n = 0
-/
theorem zero_descFactorial_succ (k : ℕ) : (0 : ℕ).descFactorial (k + 1) = 0 := by
  rw [descFactorial_succ, Nat.zero_sub, Nat.zero_mul]
/-
**Nat.descFactorial_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：descFactorial_one (n : Nat) : n.descFactorial 1 = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem descFactorial_one (n : ℕ) : n.descFactorial 1 = n := by simp
/-
**Nat.succ_descFactorial_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n k : ℕ), (n + 1).descFactorial (k + 1) = (n + 1) * n.descFactorial k
参数：n k : ℕ；n + 1；k + 1；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem succ_descFactorial_succ (n : ℕ) :
    ∀ k : ℕ, (n + 1).descFactorial (k + 1) = (n + 1) * n.descFactorial k
  | 0 => by rw [descFactorial_zero, descFactorial_one, Nat.mul_one]
  | succ k => by
    rw [descFactorial_succ, succ_descFactorial_succ _ k, descFactorial_succ, succ_sub_succ,
      Nat.mul_left_comm]
/-
**Nat.succ_descFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n k : ℕ), (n + 1 - k) * (n + 1).descFactorial k = (n + 1) * n.descFacto
rial k
参数：n k : ℕ；n + 1 - k；n + 1；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem succ_descFactorial (n : ℕ) :
    ∀ k, (n + 1 - k) * (n + 1).descFactorial k = (n + 1) * n.descFactorial k
  | 0 => by rw [Nat.sub_zero, descFactorial_zero, descFactorial_zero]
  | k + 1 => by
    rw [descFactorial, succ_descFactorial _ k, descFactorial_succ, succ_sub_succ, Nat.mul_left_comm]
/-
**Nat.descFactorial_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), n.descFactorial n = n.factorial
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem descFactorial_self : ∀ n : ℕ, n.descFactorial n = n !
  | 0 => by rw [descFactorial_zero, factorial_zero]
  | succ n => by rw [succ_descFactorial_succ, descFactorial_self n, factorial_succ]

@[simp]
/-
**Nat.descFactorial_eq_zero_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n k : ℕ}, n.descFactorial k = 0 ↔ n < k
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem descFactorial_eq_zero_iff_lt {n : ℕ} : ∀ {k : ℕ}, n.descFactorial k = 0 ↔ n < k
  | 0 => by simp only [descFactorial_zero, Nat.one_ne_zero, Nat.not_lt_zero]
  | succ k => by
    rw [descFactorial_succ, mul_eq_zero, descFactorial_eq_zero_iff_lt, Nat.lt_succ_iff,
      Nat.sub_eq_zero_iff_le, Nat.lt_iff_le_and_ne, or_iff_left_iff_imp, and_imp]
    exact fun h _ => h

@[simp]
/-
**Nat.descFactorial_pos** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：descFactorial_pos {n k : Nat} : 0 < n.descFactorial k ↔ k <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma descFactorial_pos {n k : ℕ} : 0 < n.descFactorial k ↔ k ≤ n := by simp [Nat.pos_iff_ne_zero]

alias ⟨_, descFactorial_of_lt⟩ := descFactorial_eq_zero_iff_lt
/-
**Nat.add_descFactorial_eq_ascFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n k : ℕ), (n + k).descFactorial k = (n + 1).ascFactorial k
参数：n k : ℕ；n + k；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_descFactorial_eq_ascFactorial (n : ℕ) : ∀ k : ℕ,
    (n + k).descFactorial k = (n + 1).ascFactorial k
  | 0 => by rw [ascFactorial_zero, descFactorial_zero]
  | succ k => by
    rw [Nat.add_succ, succ_descFactorial_succ, ascFactorial_succ,
      add_descFactorial_eq_ascFactorial _ k, Nat.add_right_comm]
/-
**Nat.add_descFactorial_eq_ascFactorial'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n k : ℕ), (n + k - 1).descFactorial k = n.ascFactorial k
参数：n k : ℕ；n + k - 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_descFactorial_eq_ascFactorial' (n : ℕ) :
    ∀ k : ℕ, (n + k - 1).descFactorial k = n.ascFactorial k
  | 0 => by rw [ascFactorial_zero, descFactorial_zero]
  | succ k => by
    rw [descFactorial_succ, ascFactorial_succ, ← succ_add_eq_add_succ,
      add_descFactorial_eq_ascFactorial' _ k, ← succ_ascFactorial, succ_add_sub_one,
      Nat.add_sub_cancel]

/-- `n.descFactorial k = n! / (n - k)!` but without ℕ-division. See `Nat.descFactorial_eq_div`
for the version using ℕ-division. -/
/-
**Nat.factorial_mul_descFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n k : ℕ}, k ≤ n → (n - k).factorial * n.descFactorial k = n.factorial
参数：n - k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`n.descFactorial k = n! / (n - k)!` but without ℕ-division. See `Nat.descFactori
al_eq_div`
for the version using ℕ-division.
-/
theorem factorial_mul_descFactorial : ∀ {n k : ℕ}, k ≤ n → (n - k)! * n.descFactorial k = n !
  | n, 0 => fun _ => by rw [descFactorial_zero, Nat.mul_one, Nat.sub_zero]
  | 0, succ k => fun h => by
    exfalso
    exact not_succ_le_zero k h
  | succ n, succ k => fun h => by
    rw [succ_descFactorial_succ, succ_sub_succ, ← Nat.mul_assoc, Nat.mul_comm (n - k)!,
      Nat.mul_assoc, factorial_mul_descFactorial (Nat.succ_le_succ_iff.1 h), factorial_succ]
/-
**Nat.descFactorial_mul_descFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：descFactorial_mul_descFactorial {k m n : Nat} (hkm : k <= m) : (n - k).des
cFactorial (m - k) * n.descFactorial k = n.descFactorial m
参数：hkm : k <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_left_cancel`：∀ {n m k : ℕ}, 0 < n → n * m = n * k → m = k
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorial_mul_descFactorial`：∀ {n k : ℕ}, k ≤ n → (n - k).factorial 
* n.descFactorial k = n.factorial
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_assoc`：∀ (n m k : ℕ), n * m * k = n * (m * k)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.descFactorial_eq_zero_iff_lt`：∀ {n k : ℕ}, n.descFactorial k = 0 ↔ n
 < k
· 使用定理 `Nat.zero_mul`：∀ (n : ℕ), 0 * n = 0
· 使用定理 `Nat.mul_zero`：∀ (n : ℕ), n * 0 = 0
-/
theorem descFactorial_mul_descFactorial {k m n : ℕ} (hkm : k ≤ m) :
    (n - k).descFactorial (m - k) * n.descFactorial k = n.descFactorial m := by
  by_cases hmn : m ≤ n
  · apply Nat.mul_left_cancel (n - m).factorial_pos
    rw [factorial_mul_descFactorial hmn, show n - m = (n - k) - (m - k) by lia, ← Nat.mul_assoc,
      factorial_mul_descFactorial (show m - k ≤ n - k by lia),
      factorial_mul_descFactorial (le_trans hkm hmn)]
  · rw [descFactorial_eq_zero_iff_lt.mpr (show n < m by lia)]
    by_cases hkn : k ≤ n
    · rw [descFactorial_eq_zero_iff_lt.mpr (show n - k < m - k by lia), Nat.zero_mul]
    · rw [descFactorial_eq_zero_iff_lt.mpr (show n < k by lia), Nat.mul_zero]

/-- Avoid in favor of `Nat.factorial_mul_descFactorial` if you can. ℕ-division isn't worth it. -/
/-
**Nat.descFactorial_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：descFactorial_eq_div {n k : Nat} (h : k <= n) : n.descFactorial k = n ! / 
(n - k)!
参数：h : k <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_left_cancel`：∀ {n m k : ℕ}, 0 < n → n * m = n * k → m = k
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorial_mul_descFactorial`：∀ {n k : ℕ}, k ≤ n → (n - k).factorial 
* n.descFactorial k = n.factorial
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Nat.factorial_dvd_factorial`：factorial_dvd_factorial {m n} (h : m <= n) 
: m ! ∣ n !
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n

--- 原说明 ---
Avoid in favor of `Nat.factorial_mul_descFactorial` if you can. ℕ-division isn't
 worth it.
-/
theorem descFactorial_eq_div {n k : ℕ} (h : k ≤ n) : n.descFactorial k = n ! / (n - k)! := by
  apply Nat.mul_left_cancel (n - k).factorial_pos
  rw [factorial_mul_descFactorial h]
  exact (Nat.mul_div_cancel' <| factorial_dvd_factorial <| Nat.sub_le n k).symm

@[gcongr]
/-
**Nat.descFactorial_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：descFactorial_le (n : Nat) {k m : Nat} (h : k <= m) : k.descFactorial n <=
 m.descFactorial n
参数：n : Nat；h : k <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.descFactorial_succ`：descFactorial_succ (n k : Nat) : n.descFactorial
 (k + 1) = (n - k) * n.descFactorial k
· 使用定理 `Nat.mul_le_mul`：∀ {n₁ m₁ n₂ m₂ : ℕ}, n₁ ≤ n₂ → m₁ ≤ m₂ → n₁ * m₁ ≤ n₂ * 
m₂
· 使用定理 `Nat.sub_le_sub_right`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), n - k ≤ m - k
-/
theorem descFactorial_le (n : ℕ) {k m : ℕ} (h : k ≤ m) :
    k.descFactorial n ≤ m.descFactorial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [descFactorial_succ, descFactorial_succ]
    exact Nat.mul_le_mul (Nat.sub_le_sub_right h n) ih
/-
**Nat.pow_sub_le_descFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n k : ℕ), (n + 1 - k) ^ k ≤ n.descFactorial k
参数：n k : ℕ；n + 1 - k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_sub_le_descFactorial (n : ℕ) : ∀ k : ℕ, (n + 1 - k) ^ k ≤ n.descFactorial k
  | 0 => by rw [descFactorial_zero, Nat.pow_zero]
  | k + 1 => by
    rw [descFactorial_succ, Nat.pow_succ, succ_sub_succ, Nat.mul_comm]
    apply Nat.mul_le_mul_left
    exact (le_trans (Nat.pow_le_pow_left (Nat.sub_le_sub_right n.le_succ _) k)
      (pow_sub_le_descFactorial n k))
/-
**Nat.pow_sub_lt_descFactorial'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n k : ℕ}, k + 2 ≤ n → (n - (k + 1)) ^ (k + 2) < n.descFactorial (k + 2)
参数：n - (k + 1)；k + 2；k + 2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_sub_lt_descFactorial' {n : ℕ} :
    ∀ {k : ℕ}, k + 2 ≤ n → (n - (k + 1)) ^ (k + 2) < n.descFactorial (k + 2)
  | 0, h => by
    rw [descFactorial_succ, Nat.pow_succ, Nat.pow_one, descFactorial_one]
    exact Nat.mul_lt_mul_of_pos_left (by lia) (Nat.sub_pos_of_lt h)
  | k + 1, h => by
    rw [descFactorial_succ, Nat.pow_succ, Nat.mul_comm]
    refine Nat.mul_lt_mul_of_pos_left ?_ (Nat.sub_pos_of_lt h)
    refine Nat.lt_of_le_of_lt (Nat.pow_le_pow_left (Nat.sub_le_sub_right n.le_succ _) _) ?_
    rw [succ_sub_succ]
    exact pow_sub_lt_descFactorial' (Nat.le_trans (le_succ _) h)
/-
**Nat.pow_sub_lt_descFactorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n k : ℕ}, 2 ≤ k → k ≤ n → (n + 1 - k) ^ k < n.descFactorial k
参数：n + 1 - k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.succ_sub_succ`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `Nat.pow_sub_lt_descFactorial'`：∀ {n k : ℕ}, k + 2 ≤ n → (n - (k + 1)) ^ 
(k + 2) < n.descFactorial (k + 2)
-/
theorem pow_sub_lt_descFactorial {n : ℕ} :
    ∀ {k : ℕ}, 2 ≤ k → k ≤ n → (n + 1 - k) ^ k < n.descFactorial k
  | 0 => by rintro ⟨⟩
  | 1 => by intro; contradiction
  | k + 2 => fun _ h => by
    rw [succ_sub_succ]
    exact pow_sub_lt_descFactorial' h
/-
**Nat.descFactorial_le_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n k : ℕ), n.descFactorial k ≤ n ^ k
参数：n k : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem descFactorial_le_pow (n : ℕ) : ∀ k : ℕ, n.descFactorial k ≤ n ^ k
  | 0 => by rw [descFactorial_zero, Nat.pow_zero]
  | k + 1 => by
    rw [descFactorial_succ, Nat.pow_succ, Nat.mul_comm _ n]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (descFactorial_le_pow _ k)
/-
**Nat.descFactorial_lt_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → ∀ {k : ℕ}, 2 ≤ k → n.descFactorial k < n ^ k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.descFactorial_succ`：descFactorial_succ (n k : Nat) : n.descFactorial
 (k + 1) = (n - k) * n.descFactorial k
· 使用定理 `Nat.pow_succ'`：∀ {m n : ℕ}, m ^ n.succ = m * m ^ n
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Nat.mul_lt_mul_of_le_of_lt`：∀ {a c b d : ℕ}, a ≤ c → b < d → 0 < c → a *
 b < c * d
· 使用定理 `Nat.descFactorial_le_pow`：∀ (n k : ℕ), n.descFactorial k ≤ n ^ k
· 使用定理 `Nat.pow_pos`：∀ {a n : ℕ}, 0 < a → 0 < a ^ n
-/
theorem descFactorial_lt_pow {n : ℕ} (hn : n ≠ 0) : ∀ {k : ℕ}, 2 ≤ k → n.descFactorial k < n ^ k
  | 0 => by rintro ⟨⟩
  | 1 => by intro; contradiction
  | k + 2 => fun _ => by
    rw [descFactorial_succ, pow_succ', Nat.mul_comm, Nat.mul_comm n]
    exact Nat.mul_lt_mul_of_le_of_lt (descFactorial_le_pow _ _) (by lia) (Nat.pow_pos <| by lia)

end DescFactorial

/-
**Nat.factorial_two_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：factorial_two_mul_le (n : Nat) : (2 * n)! <= (2 * n) ^ n * n !
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.two_mul`：∀ (n : ℕ), 2 * n = n + n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.factorial_mul_ascFactorial`：∀ (n k : ℕ), n.factorial * (n + 1).ascFa
ctorial k = (n + k).factorial
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
· 使用定理 `Nat.ascFactorial_le_pow_add`：∀ (n k : ℕ), (n + 1).ascFactorial k ≤ (n + 
k) ^ k
-/
lemma factorial_two_mul_le (n : ℕ) : (2 * n)! ≤ (2 * n) ^ n * n ! := by
  rw [Nat.two_mul, ← factorial_mul_ascFactorial, Nat.mul_comm]
  exact Nat.mul_le_mul_right _ (ascFactorial_le_pow_add _ _)
/-
**Nat.two_pow_mul_factorial_le_factorial_two_mul** 是 Mathlib 中的一个引理，位于命名空间 `Nat`
。
形式化陈述：two_pow_mul_factorial_le_factorial_two_mul (n : Nat) : 2 ^ n * n ! <= (2 *
 n)!
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Nat.two_mul`：∀ (n : ℕ), 2 * n = n + n
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `Nat.pow_le_pow_left`：∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Nat.factorial_mul_pow_le_factorial`：∀ {m n : ℕ}, m.factorial * (m + 1) ^
 n ≤ (m + n).factorial
-/
lemma two_pow_mul_factorial_le_factorial_two_mul (n : ℕ) : 2 ^ n * n ! ≤ (2 * n)! := by
  obtain _ | n := n
  · simp
  rw [Nat.mul_comm, Nat.two_mul]
  calc
    _ ≤ (n + 1)! * (n + 2) ^ (n + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (le_add_left _ _) _)
    _ ≤ _ := Nat.factorial_mul_pow_le_factorial


/-!
### Factorial via binary splitting.

We prove this is equal to the standard factorial and mark it `@[csimp]`.

We could proceed further, with either Legendre or Luschny methods.
-/

/-!
This is the highest factorial I can `#eval` using the naive implementation without a stack overflow:
```
/-- info: 114716 -/
#guard_msgs in
#eval 9718 ! |>.log2
```

Similarly, evaluation of `ascFactorial 100 15000` fails with the naive implementation
but works with the binary recursion.

We could implement a tail-recursive version (or just use `Nat.fold`),
but instead let's jump straight to binary splitting.
-/

/-- `ascFactorial` implemented using binary splitting.

While this still performs the same number of multiplications,
the big-integer operands to each are much smaller. -/
/-
**Nat.ascFactorialBinary** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ascFactorialBinary (n k : Nat) : Nat
参数：n k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ascFactorial` implemented using binary splitting.

While this still performs the same number of multiplications,
the big-integer operands to each are much smaller.
-/
def ascFactorialBinary (n k : ℕ) : ℕ :=
  match k with
  | 0 => 1
  | 1 => n
  | k@(_ + 2) => ascFactorialBinary n (k / 2) * ascFactorialBinary (n + k / 2) ((k + 1) / 2)

@[csimp]
/-
**Nat.ascFactorial_eq_ascFactorialBinary** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：ascFactorial_eq_ascFactorialBinary : ascFactorial = ascFactorialBinary
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.ascFactorialBinary.induct_unfolding`：∀ (motive : ℕ → ℕ → ℕ → Prop), 
  (∀ (n : ℕ), motive n 0 1) →     (∀ (n : ℕ), motive n 1 n) →       (∀ (n n_1 : 
ℕ),           motive n ((n_1 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n
-/
lemma ascFactorial_eq_ascFactorialBinary : ascFactorial = ascFactorialBinary := by
  ext n k
  fun_induction ascFactorialBinary with
  | case1 => simp
  | case2 => simp [ascFactorial]
  | case3 n k ih₁ ih₂ => grind [ascFactorial_mul_ascFactorial]

/-- Factorial implemented using binary splitting.

While this still performs the same number of multiplications,
the big-integer operands to each are much smaller. -/
/-
**Nat.factorialBinarySplitting** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：factorialBinarySplitting (n : Nat) : Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Factorial implemented using binary splitting.

While this still performs the same number of multiplications,
the big-integer operands to each are much smaller.
-/
def factorialBinarySplitting (n : ℕ) : ℕ :=
  ascFactorialBinary 1 n

@[csimp]
/-
**Nat.factorial_eq_factorialBinarySplitting** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorial_eq_factorialBinarySplitting : @factorial = @factorialBinarySplit
ting
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.one_ascFactorial`：∀ (k : ℕ), Nat.ascFactorial 1 k = k.factorial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorial_eq_factorialBinarySplitting : @factorial = @factorialBinarySplitting := by
  ext n
  simp [factorialBinarySplitting, ← ascFactorial_eq_ascFactorialBinary]

/-- `descFactorial` implemented using binary splitting. -/
/-
**Nat.descFactorialBinary** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：descFactorialBinary (n k : Nat) : Nat
参数：n k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`descFactorial` implemented using binary splitting.
-/
def descFactorialBinary (n k : ℕ) : ℕ :=
  if n < k then 0
  else ascFactorialBinary (n - k + 1) k

@[csimp]
/-
**Nat.descFactorial_eq_descFactorialBinary** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：descFactorial_eq_descFactorialBinary : descFactorial = descFactorialBinary
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.descFactorialBinary.eq_1`：∀ (n k : ℕ), n.descFactorialBinary k = if 
n < k then 0 else (n - k + 1).ascFactorialBinary k
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.descFactorial_of_lt`：∀ {n k : ℕ}, n < k → n.descFactorial k = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.ascFactorial_eq_ascFactorialBinary`：ascFactorial_eq_ascFactorialBina
ry : ascFactorial = ascFactorialBinary
· 使用定理 `Nat.add_descFactorial_eq_ascFactorial'`：∀ (n k : ℕ), (n + k - 1).descFac
torial k = n.ascFactorial k
-/
theorem descFactorial_eq_descFactorialBinary : descFactorial = descFactorialBinary := by
  ext n k
  rw [descFactorialBinary]
  split_ifs with h
  · rw [descFactorial_of_lt h]
  · rw [← ascFactorial_eq_ascFactorialBinary, ← add_descFactorial_eq_ascFactorial']
    grind

/-!
We are now limited by time, not stack space,
and this is much faster than even the tail-recursive version.

```
#time -- Less than 1s. (Tail-recursive version takes longer for `(10^5) !`.)
#eval (10^6) ! |>.log2
```
-/


end Nat

