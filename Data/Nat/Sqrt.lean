/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Basic

/-!
# Properties of the natural number square root function.
-/

public section

namespace Nat

/- We don't want to import the algebraic hierarchy in this file. -/
assert_not_exists Monoid

variable {m n a : ℕ}

/-!
### `sqrt`

See [Wikipedia, *Methods of computing square roots*]
(https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Binary_numeral_system_(base_2)).
-/

/-
**Nat.sqrt_le'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_le' (n : Nat) : sqrt n ^ 2 <= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_two`：∀ (a : ℕ), a ^ 2 = a * a
· 使用定理 `Nat.sqrt_le`：∀ (n : ℕ), n.sqrt * n.sqrt ≤ n

--- 原说明 ---
### `sqrt`

See [Wikipedia, *Methods of computing square roots*]
(https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Binary_numeral_
system_(base_2)).
-/
lemma sqrt_le' (n : ℕ) : sqrt n ^ 2 ≤ n := by simpa [Nat.pow_two] using sqrt_le n
/-
**Nat.lt_succ_sqrt'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：lt_succ_sqrt' (n : Nat) : n < succ (sqrt n) ^ 2
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_two`：∀ (a : ℕ), a ^ 2 = a * a
· 使用定理 `Nat.lt_succ_sqrt`：∀ (n : ℕ), n < n.sqrt.succ * n.sqrt.succ
-/
lemma lt_succ_sqrt' (n : ℕ) : n < succ (sqrt n) ^ 2 := by simpa [Nat.pow_two] using lt_succ_sqrt n
/-
**Nat.sqrt_le_add** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_le_add (n : Nat) : n <= sqrt n * sqrt n + sqrt n + sqrt n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Nat.lt_succ_sqrt`：∀ (n : ℕ), n < n.sqrt.succ * n.sqrt.succ
-/
lemma sqrt_le_add (n : ℕ) : n ≤ sqrt n * sqrt n + sqrt n + sqrt n := by
  rw [← succ_mul]; exact le_of_lt_succ (lt_succ_sqrt n)
/-
**Nat.le_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：le_sqrt : m <= sqrt n ↔ m * m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.mul_self_le_mul_self`：∀ {m n : ℕ}, m ≤ n → m * m ≤ n * n
· 使用定理 `Nat.sqrt_le`：∀ (n : ℕ), n.sqrt * n.sqrt ≤ n
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mul_self_lt_mul_self_iff`：∀ {m n : ℕ}, m * m < n * n ↔ m < n
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.lt_succ_sqrt`：∀ (n : ℕ), n < n.sqrt.succ * n.sqrt.succ
-/
lemma le_sqrt : m ≤ sqrt n ↔ m * m ≤ n :=
  ⟨fun h ↦ le_trans (mul_self_le_mul_self h) (sqrt_le n),
    fun h ↦ le_of_lt_succ <| Nat.mul_self_lt_mul_self_iff.1 <| lt_of_le_of_lt h (lt_succ_sqrt n)⟩
/-
**Nat.le_sqrt'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：le_sqrt' : m <= sqrt n ↔ m ^ 2 <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.pow_two`：∀ (a : ℕ), a ^ 2 = a * a
· 使用引理 `Nat.le_sqrt`：le_sqrt : m <= sqrt n ↔ m * m <= n
-/
lemma le_sqrt' : m ≤ sqrt n ↔ m ^ 2 ≤ n := by simpa only [Nat.pow_two] using le_sqrt
/-
**Nat.sqrt_lt** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_lt : sqrt m < n ↔ m < n * n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sqrt_lt : sqrt m < n ↔ m < n * n := by simp only [← not_le, le_sqrt]
/-
**Nat.sqrt_lt'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_lt' : sqrt m < n ↔ m < n ^ 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sqrt_lt' : sqrt m < n ↔ m < n ^ 2 := by simp only [← not_le, le_sqrt']
/-
**Nat.sqrt_le_self** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_le_self (n : Nat) : sqrt n <= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.le_mul_self`：∀ (n : ℕ), n ≤ n * n
· 使用定理 `Nat.sqrt_le`：∀ (n : ℕ), n.sqrt * n.sqrt ≤ n
-/
lemma sqrt_le_self (n : ℕ) : sqrt n ≤ n := le_trans (le_mul_self _) (sqrt_le n)

@[gcongr]
/-
**Nat.sqrt_le_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_le_sqrt (h : m <= n) : sqrt m <= sqrt n
参数：h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.le_sqrt`：le_sqrt : m <= sqrt n ↔ m * m <= n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.sqrt_le`：∀ (n : ℕ), n.sqrt * n.sqrt ≤ n
-/
lemma sqrt_le_sqrt (h : m ≤ n) : sqrt m ≤ sqrt n := le_sqrt.2 (le_trans (sqrt_le _) h)
/-
**Nat.eq_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：eq_sqrt : a = sqrt n ↔ a * a <= n ∧ n < (a + 1) * (a + 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sqrt_le`：∀ (n : ℕ), n.sqrt * n.sqrt ≤ n
· 使用定理 `Nat.lt_succ_sqrt`：∀ (n : ℕ), n < n.sqrt.succ * n.sqrt.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.le_sqrt`：le_sqrt : m <= sqrt n ↔ m * m <= n
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用引理 `Nat.sqrt_lt`：sqrt_lt : sqrt m < n ↔ m < n * n
-/
lemma eq_sqrt : a = sqrt n ↔ a * a ≤ n ∧ n < (a + 1) * (a + 1) :=
  ⟨fun e ↦ e.symm ▸ ⟨sqrt_le n, lt_succ_sqrt n⟩,
   fun ⟨h₁, h₂⟩ ↦ le_antisymm (le_sqrt.2 h₁) (le_of_lt_succ <| sqrt_lt.2 h₂)⟩
/-
**Nat.eq_sqrt'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：eq_sqrt' : a = sqrt n ↔ a ^ 2 <= n ∧ n < (a + 1) ^ 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.pow_two`：∀ (a : ℕ), a ^ 2 = a * a
· 使用引理 `Nat.eq_sqrt`：eq_sqrt : a = sqrt n ↔ a * a <= n ∧ n < (a + 1) * (a + 1)
-/
lemma eq_sqrt' : a = sqrt n ↔ a ^ 2 ≤ n ∧ n < (a + 1) ^ 2 := by
  simpa only [Nat.pow_two] using eq_sqrt
/-
**Nat.le_three_of_sqrt_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：le_three_of_sqrt_eq_one (h : sqrt n = 1) : n <= 3
参数：h : sqrt n = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.sqrt_lt`：sqrt_lt : sqrt m < n ↔ m < n * n
-/
lemma le_three_of_sqrt_eq_one (h : sqrt n = 1) : n ≤ 3 :=
  le_of_lt_succ <| (@sqrt_lt n 2).1 <| by grind
/-
**Nat.sqrt_lt_self** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_lt_self (h : 1 < n) : sqrt n < n
参数：h : 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.sqrt_lt`：sqrt_lt : sqrt m < n ↔ m < n * n
· 使用定理 `Nat.mul_lt_mul_of_pos_left`：∀ {n m k : ℕ}, n < m → k > 0 → k * n < k * m
· 使用定理 `Nat.lt_of_succ_lt`：∀ {n m : ℕ}, n.succ < m → n < m
-/
lemma sqrt_lt_self (h : 1 < n) : sqrt n < n :=
  sqrt_lt.2 <| by have := Nat.mul_lt_mul_of_pos_left h (lt_of_succ_lt h); grind

@[grind =]
/-
**Nat.sqrt_pos** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_pos : 0 < sqrt n ↔ 0 < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_sqrt`：le_sqrt : m <= sqrt n ↔ m * m <= n
-/
lemma sqrt_pos : 0 < sqrt n ↔ 0 < n :=
  le_sqrt
/-
**Nat.sqrt_add_eq** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_add_eq (n : Nat) (h : a <= n + n) : sqrt (n * n + a) = n
参数：n : Nat；h : a <= n + n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.sqrt_lt`：sqrt_lt : sqrt m < n ↔ m < n * n
· 使用引理 `Nat.le_sqrt`：le_sqrt : m <= sqrt n ↔ m * m <= n
-/
lemma sqrt_add_eq (n : ℕ) (h : a ≤ n + n) : sqrt (n * n + a) = n :=
  le_antisymm
    (le_of_lt_succ <| sqrt_lt.2 <| by grind)
    (le_sqrt.2 <| by grind)
/-
**Nat.sqrt_add_eq'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_add_eq' (n : Nat) (h : a <= n + n) : sqrt (n ^ 2 + a) = n
参数：n : Nat；h : a <= n + n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_two`：∀ (a : ℕ), a ^ 2 = a * a
· 使用引理 `Nat.sqrt_add_eq`：sqrt_add_eq (n : Nat) (h : a <= n + n) : sqrt (n * n + 
a) = n
-/
lemma sqrt_add_eq' (n : ℕ) (h : a ≤ n + n) : sqrt (n ^ 2 + a) = n := by
  simpa [Nat.pow_two] using sqrt_add_eq n h

@[simp]
/-
**Nat.sqrt_eq** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_eq (n : Nat) : sqrt (n * n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.sqrt_add_eq`：sqrt_add_eq (n : Nat) (h : a <= n + n) : sqrt (n * n + 
a) = n
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
lemma sqrt_eq (n : ℕ) : sqrt (n * n) = n := sqrt_add_eq n (zero_le _)

@[simp]
/-
**Nat.sqrt_eq'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_eq' (n : Nat) : sqrt (n ^ 2) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.sqrt_add_eq'`：sqrt_add_eq' (n : Nat) (h : a <= n + n) : sqrt (n ^ 2 
+ a) = n
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
lemma sqrt_eq' (n : ℕ) : sqrt (n ^ 2) = n := sqrt_add_eq' n (zero_le _)
/-
**Nat.sqrt_succ_le_succ_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_succ_le_succ_sqrt (n : Nat) : sqrt n.succ <= n.sqrt.succ
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.sqrt_lt`：sqrt_lt : sqrt m < n ↔ m < n * n
· 使用引理 `Nat.sqrt_le_add`：sqrt_le_add (n : Nat) : n <= sqrt n * sqrt n + sqrt n +
 sqrt n
-/
lemma sqrt_succ_le_succ_sqrt (n : ℕ) : sqrt n.succ ≤ n.sqrt.succ :=
  le_of_lt_succ <| sqrt_lt.2 <| (have := sqrt_le_add n; by grind)

@[simp]
/-
**Nat.log2_two** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：log2_two : (2 : Nat).log2 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log2_def`：∀ (n : ℕ), n.log2 = if 2 ≤ n then (n / 2).log2 + 1 else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `Nat.div_self`：∀ {n : ℕ}, 0 < n → n / n = 1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma log2_two : (2 : ℕ).log2 = 1 := by simp [log2_def]
/-
**Nat.sqrt_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.sqrt 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp, grind =] lemma sqrt_zero : sqrt 0 = 0 :=
  eq_comm.1 (by simp [eq_sqrt])
/-
**Nat.sqrt_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.sqrt 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp, grind =] lemma sqrt_one : sqrt 1 = 1 :=
  eq_comm.1 (by simp [eq_sqrt])
/-
**Nat.sqrt_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_eq_zero : sqrt n = 0 ↔ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.sqrt_lt`：sqrt_lt : sqrt m < n ↔ m < n * n
-/
lemma sqrt_eq_zero : sqrt n = 0 ↔ n = 0 :=
  ⟨fun h ↦ have := @sqrt_lt n 1; by grind, by grind⟩

@[simp]
/-
**Nat.sqrt_two** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_two : sqrt 2 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma sqrt_two : sqrt 2 = 1 :=
  eq_comm.1 (by simp [eq_sqrt])
/-
**Nat.add_one_sqrt_le_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：add_one_sqrt_le_of_ne_zero {n : Nat} (hn : n != 0) : (n + 1).sqrt <= n
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用引理 `Nat.sqrt_two`：sqrt_two : sqrt 2 = 1
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `Nat.sqrt_succ_le_succ_sqrt`：sqrt_succ_le_succ_sqrt (n : Nat) : sqrt n.su
cc <= n.sqrt.succ
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
-/
lemma add_one_sqrt_le_of_ne_zero {n : ℕ} (hn : n ≠ 0) : (n + 1).sqrt ≤ n :=
  le_induction (by simp) (fun n _ ih ↦ le_trans n.succ.sqrt_succ_le_succ_sqrt (succ_le_succ ih)) n
    (Nat.pos_of_ne_zero hn)
/-
**Nat.exists_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：exists_mul_self (x : Nat) : (exists n, n * n = x) ↔ sqrt x * sqrt x = x
参数：x : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.sqrt_eq`：sqrt_eq (n : Nat) : sqrt (n * n) = n
-/
lemma exists_mul_self (x : ℕ) : (∃ n, n * n = x) ↔ sqrt x * sqrt x = x :=
  ⟨fun ⟨n, hn⟩ ↦ by rw [← hn, sqrt_eq], fun h ↦ ⟨sqrt x, h⟩⟩
/-
**Nat.exists_mul_self'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：exists_mul_self' (x : Nat) : (exists n, n ^ 2 = x) ↔ sqrt x ^ 2 = x
参数：x : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.pow_two`：∀ (a : ℕ), a ^ 2 = a * a
· 使用引理 `Nat.exists_mul_self`：exists_mul_self (x : Nat) : (exists n, n * n = x) ↔
 sqrt x * sqrt x = x
-/
lemma exists_mul_self' (x : ℕ) : (∃ n, n ^ 2 = x) ↔ sqrt x ^ 2 = x := by
  simpa only [Nat.pow_two] using exists_mul_self x
/-
**Nat.sqrt_mul_sqrt_lt_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_mul_sqrt_lt_succ (n : Nat) : sqrt n * sqrt n < n + 1
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Nat.sqrt_le`：∀ (n : ℕ), n.sqrt * n.sqrt ≤ n
-/
lemma sqrt_mul_sqrt_lt_succ (n : ℕ) : sqrt n * sqrt n < n + 1 :=
  Nat.lt_succ_iff.mpr (sqrt_le _)
/-
**Nat.sqrt_mul_sqrt_lt_succ'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：sqrt_mul_sqrt_lt_succ' (n : Nat) : sqrt n ^ 2 < n + 1
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用引理 `Nat.sqrt_le'`：sqrt_le' (n : Nat) : sqrt n ^ 2 <= n
-/
lemma sqrt_mul_sqrt_lt_succ' (n : ℕ) : sqrt n ^ 2 < n + 1 :=
  Nat.lt_succ_iff.mpr (sqrt_le' _)
/-
**Nat.succ_le_succ_sqrt** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：succ_le_succ_sqrt (n : Nat) : n + 1 <= (sqrt n + 1) * (sqrt n + 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_pred_lt`：∀ {n : ℕ} {m : ℕ}, m.pred < n → m ≤ n
· 使用定理 `Nat.lt_succ_sqrt`：∀ (n : ℕ), n < n.sqrt.succ * n.sqrt.succ
-/
lemma succ_le_succ_sqrt (n : ℕ) : n + 1 ≤ (sqrt n + 1) * (sqrt n + 1) :=
  le_of_pred_lt (lt_succ_sqrt _)
/-
**Nat.succ_le_succ_sqrt'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：succ_le_succ_sqrt' (n : Nat) : n + 1 <= (sqrt n + 1) ^ 2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_pred_lt`：∀ {n : ℕ} {m : ℕ}, m.pred < n → m ≤ n
· 使用引理 `Nat.lt_succ_sqrt'`：lt_succ_sqrt' (n : Nat) : n < succ (sqrt n) ^ 2
-/
lemma succ_le_succ_sqrt' (n : ℕ) : n + 1 ≤ (sqrt n + 1) ^ 2 :=
  le_of_pred_lt (lt_succ_sqrt' _)

/-- There are no perfect squares strictly between m² and (m+1)² -/
/-
**Nat.not_exists_sq** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：not_exists_sq (hl : m * m < n) (hr : n < (m + 1) * (m + 1)) : ¬exists t, t
 * t = n
参数：hl : m * m < n；hr : n < (m + 1) * (m + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mul_self_lt_mul_self_iff`：∀ {m n : ℕ}, m * m < n * n ↔ m < n

--- 原说明 ---
There are no perfect squares strictly between m² and (m+1)²
-/
lemma not_exists_sq (hl : m * m < n) (hr : n < (m + 1) * (m + 1)) : ¬∃ t, t * t = n := by
  rintro ⟨t, rfl⟩
  have h1 : m < t := Nat.mul_self_lt_mul_self_iff.1 hl
  have h2 : t < m + 1 := Nat.mul_self_lt_mul_self_iff.1 hr
  grind
/-
**Nat.not_exists_sq'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：not_exists_sq' : m ^ 2 < n -> n < (m + 1) ^ 2 -> ¬exists t, t ^ 2 = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pow_two`：∀ (a : ℕ), a ^ 2 = a * a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Nat.not_exists_sq`：not_exists_sq (hl : m * m < n) (hr : n < (m + 1) * (m
 + 1)) : ¬exists t, t * t = n
-/
lemma not_exists_sq' : m ^ 2 < n → n < (m + 1) ^ 2 → ¬∃ t, t ^ 2 = n := by
  simpa only [Nat.pow_two] using not_exists_sq
/-
**Nat.le_sqrt_of_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：le_sqrt_of_eq_mul {a b c : Nat} (h : a = b * c) : b <= a.sqrt ∨ c <= a.sqr
t
参数：h : a = b * c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.le_sqrt`：le_sqrt : m <= sqrt n ↔ m * m <= n
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
-/
lemma le_sqrt_of_eq_mul {a b c : ℕ} (h : a = b * c) : b ≤ a.sqrt ∨ c ≤ a.sqrt := by
  rcases le_total b c with bc | cb
  · exact Or.inl <| le_sqrt.mpr <| h ▸ mul_le_mul_left b bc
  · exact Or.inr <| le_sqrt.mpr <| h ▸ mul_le_mul_right c cb

end Nat

