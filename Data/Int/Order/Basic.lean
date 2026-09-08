/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Tactic.ByCases

/-!
# The order relation on the integers
-/

public section

open Nat

namespace Int

variable {a b : ℤ}

/-
**Int.le.elim** 是 Mathlib 中的一个定理，位于命名空间 `Int.le`。
形式化陈述：∀ {a b : ℤ}, a ≤ b → ∀ {P : Prop}, (∀ (n : ℕ), a + ↑n = b → P) → P
参数：∀ (n : ℕ), a + ↑n = b → P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Int.le.dest`：∀ {a b : ℤ}, a ≤ b → ∃ n, a + ↑n = b
-/
theorem le.elim (h : a ≤ b) {P : Prop} (h' : ∀ n : ℕ, a + ↑n = b → P) : P :=
  Exists.elim (le.dest h) h'

alias ⟨le_of_ofNat_le_ofNat, ofNat_le_ofNat_of_le⟩ := ofNat_le
/-
**Int.lt.elim** 是 Mathlib 中的一个定理，位于命名空间 `Int.lt`。
形式化陈述：∀ {a b : ℤ}, a < b → ∀ {P : Prop}, (∀ (n : ℕ), a + ↑n.succ = b → P) → P
参数：∀ (n : ℕ), a + ↑n.succ = b → P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Int.lt.dest`：∀ {a b : ℤ}, a < b → ∃ n, a + ↑n.succ = b
-/
theorem lt.elim (h : a < b) {P : Prop} (h' : ∀ n : ℕ, a + ↑(Nat.succ n) = b → P) : P :=
  Exists.elim (lt.dest h) h'

alias ⟨lt_of_ofNat_lt_ofNat, ofNat_lt_ofNat_of_lt⟩ := ofNat_lt
/-
**Int.instLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instLinearOrder : LinearOrder Int where le_refl
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.le_refl`：∀ (a : ℤ), a ≤ a
· 使用定理 `Int.le_trans`：∀ {a b c : ℤ}, a ≤ b → b ≤ c → a ≤ c
· 使用定理 `Int.lt_iff_le_and_not_ge`：∀ {a b : ℤ}, a < b ↔ a ≤ b ∧ ¬b ≤ a
· 使用定理 `Int.le_antisymm`：∀ {a b : ℤ}, a ≤ b → b ≤ a → a = b
· 使用定理 `Int.le_total`：∀ (a b : ℤ), a ≤ b ∨ b ≤ a
-/
instance instLinearOrder : LinearOrder ℤ where
  le_refl := Int.le_refl
  le_trans := @Int.le_trans
  le_antisymm := @Int.le_antisymm
  lt_iff_le_not_ge := @Int.lt_iff_le_and_not_ge
  le_total := Int.le_total
  toDecidableEq := instDecidableEq
  toDecidableLE := decLe
  toDecidableLT := decLt

protected alias ⟨eq_zero_or_eq_zero_of_mul_eq_zero, _⟩ := Int.mul_eq_zero
/-
**Int.nonneg_or_nonpos_of_mul_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：nonneg_or_nonpos_of_mul_nonneg : 0 <= a * b -> 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ 
b <= 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonneg_or_nonpos_of_mul_nonneg : 0 ≤ a * b → 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  grind [Int.mul_comm, Int.mul_nonneg_iff_of_pos_right]
/-
**Int.mul_nonneg_of_nonneg_or_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：mul_nonneg_of_nonneg_or_nonpos : 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0 -> 0 <=
 a * b | .inl ⟨ha, hb⟩ => Int.mul_nonneg ha hb | .inr ⟨ha, hb⟩ => Int.mul_nonneg
_of_nonpos_of_nonpos ha hb  protected theorem mul_nonneg_iff : 0 <= a * b ↔ 0 <=
 a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.mul_nonneg`：∀ {a b : ℤ}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `Int.mul_nonneg_of_nonpos_of_nonpos`：∀ {a b : ℤ}, a ≤ 0 → b ≤ 0 → 0 ≤ a *
 b
-/
theorem mul_nonneg_of_nonneg_or_nonpos : 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 → 0 ≤ a * b
  | .inl ⟨ha, hb⟩ => Int.mul_nonneg ha hb
  | .inr ⟨ha, hb⟩ => Int.mul_nonneg_of_nonpos_of_nonpos ha hb
/-
**Int.mul_nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {a b : ℤ}, 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.nonneg_or_nonpos_of_mul_nonneg`：nonneg_or_nonpos_of_mul_nonneg : 0 <
= a * b -> 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
· 使用定理 `Int.mul_nonneg_of_nonneg_or_nonpos`：mul_nonneg_of_nonneg_or_nonpos : 0 <
= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0 -> 0 <= a * b | .inl ⟨ha, hb⟩ => Int.mul_nonneg h
a hb | .inr ⟨ha, hb⟩ => …
-/
protected theorem mul_nonneg_iff : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
  ⟨nonneg_or_nonpos_of_mul_nonneg, mul_nonneg_of_nonneg_or_nonpos⟩
/-
**Int.mul_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {a b : ℤ}, 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.lt_iff_le_and_ne`：∀ {a b : ℤ}, a < b ↔ a ≤ b ∧ a ≠ b
· 使用定理 `Int.mul_nonneg_iff`：∀ {a b : ℤ}, 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤
 0
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用定理 `Int.mul_ne_zero_iff`：∀ {a b : ℤ}, a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0
-/
protected theorem mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rw [Int.lt_iff_le_and_ne, Int.mul_nonneg_iff, ne_comm, Int.mul_ne_zero_iff]
  lia
/-
**Int.mul_nonpos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {a b : ℤ}, a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Int.mul_pos_iff`：∀ {a b : ℤ}, 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0
-/
protected theorem mul_nonpos_iff : a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  rw [← not_iff_not, not_le, Int.mul_pos_iff]
  lia
/-
**Int.mul_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {a b : ℤ}, a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Int.mul_nonneg_iff`：∀ {a b : ℤ}, 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤
 0
-/
protected theorem mul_neg_iff : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  rw [← not_iff_not, not_lt, Int.mul_nonneg_iff]
  lia

end Int

