/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Bits

/-! Lemmas about `size`. -/

public section

namespace Nat

/-! ### `shiftLeft` and `shiftRight` -/

/-
**Nat.shiftLeft_eq_mul_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：shiftLeft_eq_mul_pow (m) : forall n, m <<< n = m * 2 ^ n
参数：m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.shiftLeft_eq`：∀ (a b : ℕ), a <<< b = a * 2 ^ b

--- 原说明 ---
### `shiftLeft` and `shiftRight`
-/
theorem shiftLeft_eq_mul_pow (m) : ∀ n, m <<< n = m * 2 ^ n := shiftLeft_eq _
/-
**Nat.shiftLeft'_true_eq_mul_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (m n : ℕ), Nat.shiftLeft' true m n + 1 = (m + 1) * 2 ^ n
参数：m n : ℕ；m + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.shiftLeft'`：shiftLeft'_false : forall n, shiftLeft' false m n = m <<
< n | 0 => rfl | n + 1 => by have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m
-/
theorem shiftLeft'_true_eq_mul_pow (m) : ∀ n, shiftLeft' true m n + 1 = (m + 1) * 2 ^ n
  | 0 => by simp [shiftLeft', Nat.pow_zero]
  | k + 1 => by
    rw [shiftLeft', bit_val, Bool.toNat_true, Nat.add_assoc, ← Nat.mul_add_one,
      shiftLeft'_true_eq_mul_pow m k, Nat.mul_left_comm, Nat.mul_comm 2, Nat.pow_succ]

@[deprecated (since := "2026-03-22")] alias shiftLeft'_tt_eq_mul_pow := shiftLeft'_true_eq_mul_pow
/-
**Nat.shiftLeft'_ne_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (b : Bool) {m : ℕ}, m ≠ 0 → ∀ (n : ℕ), Nat.shiftLeft' b m n ≠ 0
参数：b : Bool；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.shiftLeft'`：shiftLeft'_false : forall n, shiftLeft' false m n = m <<
< n | 0 => rfl | n + 1 => by have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem shiftLeft'_ne_zero_left (b) {m} (h : m ≠ 0) (n) : shiftLeft' b m n ≠ 0 := by
  induction n <;> simp [shiftLeft', *]
/-
**Nat.shiftLeft'_true_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (m : ℕ) {n : ℕ}, n ≠ 0 → Nat.shiftLeft' true m n ≠ 0
参数：m : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.shiftLeft'`：shiftLeft'_false : forall n, shiftLeft' false m n = m <<
< n | 0 => rfl | n + 1 => by have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem shiftLeft'_true_ne_zero (m) : ∀ {n}, (n ≠ 0) → shiftLeft' true m n ≠ 0
  | 0, h => absurd rfl h
  | succ _, _ => by simp [shiftLeft', bit]

@[deprecated (since := "2026-03-22")] alias shiftLeft'_tt_ne_zero := shiftLeft'_true_ne_zero

/-! ### `size` -/


@[simp]
/-
**Nat.size_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：size_zero : size 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `size`
-/
theorem size_zero : size 0 = 0 := rfl

@[simp]
/-
**Nat.size_bit** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：size_bit {b n} (h : bit b n != 0) : size (bit b n) = succ (size n)
参数：h : bit b n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.binaryRec_eq`：binaryRec_eq {zero : motive 0} {bit : forall b n, moti
ve n -> motive (bit b n)} (b n) (h : bit false 0 zero = zero ∨ (n = 0 -> b = tru
e)) : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.bit_ne_zero_iff`：bit_ne_zero_iff {n : Nat} {b : Bool} : n.bit b != 0
 ↔ n = 0 -> b = true
-/
theorem size_bit {b n} (h : bit b n ≠ 0) : size (bit b n) = succ (size n) :=
  Nat.binaryRec_eq _ _ (.inr <| Nat.bit_ne_zero_iff.mp h)

@[simp]
/-
**Nat.size_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：size_one : size 1 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem size_one : size 1 = 1 := rfl

@[simp]
/-
**Nat.size_shiftLeft'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：size_shiftLeft' {b m n} (h : shiftLeft' b m n != 0) : size (shiftLeft' b m
 n) = size m + n
参数：h : shiftLeft' b m n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.shiftLeft'`：shiftLeft'_false : forall n, shiftLeft' false m n = m <<
< n | 0 => rfl | n + 1 => by have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.size_bit`：size_bit {b n} (h : bit b n != 0) : size (bit b n) = succ 
(size n)
· 使用定理 `Nat.add_succ`：∀ (n m : ℕ), n + m.succ = (n + m).succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Nat.add_zero`：∀ (n : ℕ), n + 0 = n
· 使用定理 `Nat.succ.inj`：∀ {m n : ℕ}, m.succ = n.succ → m = n
· 使用定理 `Nat.eq_one_of_dvd_one`：∀ {n : ℕ}, n ∣ 1 → n = 1
· 使用定理 `Nat.shiftLeft'_true_eq_mul_pow`：∀ (m n : ℕ), Nat.shiftLeft' true m n + 1
 = (m + 1) * 2 ^ n
-/
theorem size_shiftLeft' {b m n} (h : shiftLeft' b m n ≠ 0) :
    size (shiftLeft' b m n) = size m + n := by
  induction n with
  | zero => simp [shiftLeft']
  | succ n IH =>
    simp only [shiftLeft', ne_eq] at h ⊢
    rw [size_bit h, Nat.add_succ]
    by_cases s0 : shiftLeft' b m n = 0
    case neg => rw [IH s0]
    rw [s0] at h ⊢
    cases b; · exact absurd rfl h
    have : shiftLeft' true m n + 1 = 1 := congr_arg (· + 1) s0
    rw [shiftLeft'_true_eq_mul_pow] at this
    obtain rfl := succ.inj (eq_one_of_dvd_one ⟨_, this.symm⟩)
    simp only [Nat.zero_add, Nat.one_mul, Nat.pow_eq_one, succ_ne_self, false_or] at this
    rw [this, Nat.add_zero]

@[simp]
/-
**Nat.size_shiftLeft** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：size_shiftLeft {m} (h : m != 0) (n) : size (m <<< n) = size m + n
参数：h : m != 0；n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.shiftLeft'`：shiftLeft'_false : forall n, shiftLeft' false m n = m <<
< n | 0 => rfl | n + 1 => by have : 2 * (m * 2 ^ n) = 2 ^ (n + 1) * m
· 使用定理 `Nat.size_shiftLeft'`：size_shiftLeft' {b m n} (h : shiftLeft' b m n != 0)
 : size (shiftLeft' b m n) = size m + n
· 使用定理 `Nat.shiftLeft'_ne_zero_left`：∀ (b : Bool) {m : ℕ}, m ≠ 0 → ∀ (n : ℕ), Na
t.shiftLeft' b m n ≠ 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem size_shiftLeft {m} (h : m ≠ 0) (n) : size (m <<< n) = size m + n := by
  simp only [size_shiftLeft' (shiftLeft'_ne_zero_left _ h _), ← shiftLeft'_false]
/-
**Nat.lt_size_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_size_self (n : Nat) : n < 2 ^ size n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.size_bit`：size_bit {b n} (h : bit b n != 0) : size (bit b n) = succ 
(size n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.bit_ne_zero_iff`：bit_ne_zero_iff {n : Nat} {b : Bool} : n.bit b != 0
 ↔ n = 0 -> b = true
· 使用定理 `Nat.bit_lt_two_pow_succ_iff`：∀ {b : Bool} {x n : ℕ}, Nat.bit b x < 2 ^ (
n + 1) ↔ x < 2 ^ n
-/
theorem lt_size_self (n : ℕ) : n < 2 ^ size n := by
  induction n using binaryRec' with
  | zero => simp
  | bit b n h IH =>
    rw [← Nat.bit_ne_zero_iff] at h
    rwa [size_bit h, bit_lt_two_pow_succ_iff]
/-
**Nat.size_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：size_le {m n : Nat} : size m <= n ↔ m < 2 ^ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Nat.lt_size_self`：lt_size_self (n : Nat) : n < 2 ^ size n
· 使用定理 `Nat.pow_le_pow_right`：∀ {n : ℕ}, n > 0 → ∀ {i j : ℕ}, i ≤ j → n ^ i ≤ n 
^ j
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.size_bit`：size_bit {b n} (h : bit b n != 0) : size (bit b n) = succ 
(size n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.bit_ne_zero_iff`：bit_ne_zero_iff {n : Nat} {b : Bool} : n.bit b != 0
 ↔ n = 0 -> b = true
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `Nat.bit_lt_two_pow_succ_iff`：∀ {b : Bool} {x n : ℕ}, Nat.bit b x < 2 ^ (
n + 1) ↔ x < 2 ^ n
-/
theorem size_le {m n : ℕ} : size m ≤ n ↔ m < 2 ^ n :=
  ⟨fun h => Nat.lt_of_lt_of_le (lt_size_self _) (Nat.pow_le_pow_right (by decide) h), fun h ↦ by
    induction m using binaryRec' generalizing n with
    | zero => simp
    | bit b m e IH =>
      rw [← Nat.bit_ne_zero_iff] at e
      rw [size_bit e]
      cases n with
      | zero => exact (e (Nat.lt_one_iff.mp h)).elim
      | succ n => exact succ_le_succ (IH (bit_lt_two_pow_succ_iff.mp h))⟩
/-
**Nat.lt_size** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_size {m n : Nat} : m < size n ↔ 2 ^ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.not_lt`：∀ {a b : ℕ}, ¬a < b ↔ b ≤ a
· 使用定理 `Decidable.iff_not_comm`：∀ {a b : Prop} [Decidable a] [Decidable b], (a ↔
 ¬b) ↔ (b ↔ ¬a)
· 使用定理 `Nat.size_le`：size_le {m n : Nat} : size m <= n ↔ m < 2 ^ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_size {m n : ℕ} : m < size n ↔ 2 ^ m ≤ n := by
  rw [← Nat.not_lt, Decidable.iff_not_comm, Nat.not_lt, size_le]
/-
**Nat.size_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：size_pos {n : Nat} : 0 < size n ↔ 0 < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_size`：lt_size {m n : Nat} : m < size n ↔ 2 ^ m <= n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem size_pos {n : ℕ} : 0 < size n ↔ 0 < n := by rw [lt_size]; rfl
/-
**Nat.size_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：size_eq_zero {n : Nat} : size n = 0 ↔ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.size_pos`：size_pos {n : Nat} : 0 < size n ↔ 0 < n
-/
theorem size_eq_zero {n : ℕ} : size n = 0 ↔ n = 0 := by
  simpa [Nat.pos_iff_ne_zero, Decidable.not_iff_not] using size_pos
/-
**Nat.size_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：size_pow {n : Nat} : size (2 ^ n) = n + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.shiftLeft_eq`：∀ (a b : ℕ), a <<< b = a * 2 ^ b
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Nat.size_shiftLeft`：size_shiftLeft {m} (h : m != 0) (n) : size (m <<< n)
 = size m + n
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem size_pow {n : ℕ} : size (2 ^ n) = n + 1 := by
  simpa [shiftLeft_eq, Nat.add_comm] using size_shiftLeft (m := 1) (by decide) n
/-
**Nat.size_le_size** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：size_le_size {m n : Nat} (h : m <= n) : size m <= size n
参数：h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.size_le`：size_le {m n : Nat} : size m <= n ↔ m < 2 ^ n
· 使用定理 `Nat.lt_of_le_of_lt`：∀ {n m k : ℕ}, n ≤ m → m < k → n < k
· 使用定理 `Nat.lt_size_self`：lt_size_self (n : Nat) : n < 2 ^ size n
-/
theorem size_le_size {m n : ℕ} (h : m ≤ n) : size m ≤ size n :=
  size_le.2 <| Nat.lt_of_le_of_lt h (lt_size_self _)
/-
**Nat.size_eq_bits_len** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：size_eq_bits_len (n : Nat) : n.bits.length = n.size
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_bits`：zero_bits : bits 0 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.size_bit`：size_bit {b n} (h : bit b n != 0) : size (bit b n) = succ 
(size n)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Bool.not_eq_false`：∀ (b : Bool), (¬b = false) = (b = true)
· 使用定理 `Nat.bits_append_bit`：bits_append_bit (n : Nat) (b : Bool) (hn : n = 0 ->
 b = true) : (bit b n).bits = b :: n.bits
-/
theorem size_eq_bits_len (n : ℕ) : n.bits.length = n.size := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit _ _ h ih =>
    rw [size_bit, bits_append_bit _ _ h]
    · simp [ih]
    · simpa [bit_eq_zero_iff]

end Nat

