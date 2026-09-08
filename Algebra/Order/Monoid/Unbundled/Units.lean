/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Lemmas for units in an ordered monoid
-/

public section

variable {M : Type*} [Monoid M] [LE M]

namespace Units

section MulLeftMono
variable [MulLeftMono M] (u : Mˣ) {a b : M}

/-
**Units.mulLECancellable_val** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mulLECancellable_val : MulLECancellable (↑u : M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.inv_mul_cancel_left`：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ 
: α) * (a * b) = b
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
-/
theorem mulLECancellable_val : MulLECancellable (↑u : M) := fun _ _ h ↦ by
  simpa using mul_le_mul_right h ↑u⁻¹
/-
**Units.mul_le_mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_le_mul_iff_left : u * a ≤ u * b ↔ a ≤ b :=
  u.mulLECancellable_val.mul_le_mul_iff_left
/-
**Units.inv_mul_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：inv_mul_le_iff : u⁻¹ * a <= b ↔ a <= u * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Algebra.Order.Monoid.Unbundled.Units.0.Units.mul_le_mul
_iff_left`：∀ {M : Type u_1} [inst : Monoid M] [inst_1 : LE M] [MulLeftMono M] (u
 : Mˣ) {a b : M}, ↑u * a ≤ ↑u * b ↔ a ≤ b
· 使用定理 `Units.mul_inv_cancel_left`：mul_inv_cancel_left (a : αˣ) (b : α) : (a : α
) * (↑a⁻¹ * b) = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_mul_le_iff : u⁻¹ * a ≤ b ↔ a ≤ u * b := by
  rw [← u.mul_le_mul_iff_left, mul_inv_cancel_left]
/-
**Units.le_inv_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：le_inv_mul_iff : a <= u⁻¹ * b ↔ u * a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Algebra.Order.Monoid.Unbundled.Units.0.Units.mul_le_mul
_iff_left`：∀ {M : Type u_1} [inst : Monoid M] [inst_1 : LE M] [MulLeftMono M] (u
 : Mˣ) {a b : M}, ↑u * a ≤ ↑u * b ↔ a ≤ b
· 使用定理 `Units.mul_inv_cancel_left`：mul_inv_cancel_left (a : αˣ) (b : α) : (a : α
) * (↑a⁻¹ * b) = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_inv_mul_iff : a ≤ u⁻¹ * b ↔ u * a ≤ b := by
  rw [← u.mul_le_mul_iff_left, mul_inv_cancel_left]
/-
**Units.one_le_inv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] [inst_1 : LE M] [MulLeftMono M] (u : Mˣ
), 1 ≤ ↑u⁻¹ ↔ ↑u ≤ 1
参数：u : Mˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Algebra.Order.Monoid.Unbundled.Units.0.Units.mul_le_mul
_iff_left`：∀ {M : Type u_1} [inst : Monoid M] [inst_1 : LE M] [MulLeftMono M] (u
 : Mˣ) {a b : M}, ↑u * a ≤ ↑u * b ↔ a ≤ b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem one_le_inv : (1 : M) ≤ u⁻¹ ↔ (u : M) ≤ 1 := by
  rw [← u.mul_le_mul_iff_left, mul_one, mul_inv]
/-
**Units.inv_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] [inst_1 : LE M] [MulLeftMono M] (u : Mˣ
), ↑u⁻¹ ≤ 1 ↔ 1 ≤ ↑u
参数：u : Mˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Algebra.Order.Monoid.Unbundled.Units.0.Units.mul_le_mul
_iff_left`：∀ {M : Type u_1} [inst : Monoid M] [inst_1 : LE M] [MulLeftMono M] (u
 : Mˣ) {a b : M}, ↑u * a ≤ ↑u * b ↔ a ≤ b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem inv_le_one : u⁻¹ ≤ (1 : M) ↔ (1 : M) ≤ u := by
  rw [← u.mul_le_mul_iff_left, mul_one, mul_inv]
/-
**Units.one_le_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：one_le_inv_mul : 1 <= u⁻¹ * a ↔ u <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.le_inv_mul_iff`：le_inv_mul_iff : a <= u⁻¹ * b ↔ u * a <= b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_le_inv_mul : 1 ≤ u⁻¹ * a ↔ u ≤ a := by
  rw [u.le_inv_mul_iff, mul_one]
/-
**Units.inv_mul_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：inv_mul_le_one : u⁻¹ * a <= 1 ↔ a <= u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.inv_mul_le_iff`：inv_mul_le_iff : u⁻¹ * a <= b ↔ a <= u * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_mul_le_one : u⁻¹ * a ≤ 1 ↔ a ≤ u := by
  rw [u.inv_mul_le_iff, mul_one]

alias ⟨le_mul_of_inv_mul_le, inv_mul_le_of_le_mul⟩ := inv_mul_le_iff
alias ⟨mul_le_of_le_inv_mul, le_inv_mul_of_mul_le⟩ := le_inv_mul_iff
alias ⟨le_of_one_le_inv, one_le_inv_of_le⟩ := one_le_inv
alias ⟨le_of_inv_le_one, inv_le_one_of_le⟩ := inv_le_one
alias ⟨le_of_one_le_inv_mul, one_le_inv_mul_of_le⟩ := one_le_inv_mul
alias ⟨le_of_inv_mul_le_one, inv_mul_le_one_of_le⟩ := inv_mul_le_one

end MulLeftMono

section MulRightMono
variable [MulRightMono M] {a b : M} (u : Mˣ)

/-
**Units.mul_le_mul_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_le_mul_iff_right : a * u ≤ b * u ↔ a ≤ b :=
  ⟨(by simpa using mul_le_mul_left · ↑u⁻¹), (mul_le_mul_left · _)⟩
/-
**Units.mul_inv_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_inv_le_iff : a * u⁻¹ <= b ↔ a <= b * u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Algebra.Order.Monoid.Unbundled.Units.0.Units.mul_le_mul
_iff_right`：∀ {M : Type u_1} [inst : Monoid M] [inst_1 : LE M] [MulRightMono M] 
{a b : M} (u : Mˣ), a * ↑u ≤ b * ↑u ↔ a ≤ b
· 使用定理 `Units.inv_mul_cancel_right`：inv_mul_cancel_right (a : α) (b : αˣ) : a * 
↑b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_le_iff : a * u⁻¹ ≤ b ↔ a ≤ b * u := by
  rw [← u.mul_le_mul_iff_right, u.inv_mul_cancel_right]
/-
**Units.le_mul_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：le_mul_inv_iff : a <= b * u⁻¹ ↔ a * u <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Algebra.Order.Monoid.Unbundled.Units.0.Units.mul_le_mul
_iff_right`：∀ {M : Type u_1} [inst : Monoid M] [inst_1 : LE M] [MulRightMono M] 
{a b : M} (u : Mˣ), a * ↑u ≤ b * ↑u ↔ a ≤ b
· 使用定理 `Units.inv_mul_cancel_right`：inv_mul_cancel_right (a : α) (b : αˣ) : a * 
↑b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_mul_inv_iff : a ≤ b * u⁻¹ ↔ a * u ≤ b := by
  rw [← u.mul_le_mul_iff_right, inv_mul_cancel_right]
/-
**Units.one_le_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：one_le_mul_inv : 1 <= a * u⁻¹ ↔ u <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.le_mul_inv_iff`：le_mul_inv_iff : a <= b * u⁻¹ ↔ a * u <= b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_le_mul_inv : 1 ≤ a * u⁻¹ ↔ u ≤ a := by
  rw [u.le_mul_inv_iff, one_mul]
/-
**Units.mul_inv_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_inv_le_one : a * u⁻¹ <= 1 ↔ a <= u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.mul_inv_le_iff`：mul_inv_le_iff : a * u⁻¹ <= b ↔ a <= b * u
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_le_one : a * u⁻¹ ≤ 1 ↔ a ≤ u := by
  rw [u.mul_inv_le_iff, one_mul]

alias ⟨le_mul_of_mul_inv_le, mul_inv_le_of_le_mul⟩ := mul_inv_le_iff
alias ⟨mul_le_of_le_mul_inv, le_mul_inv_of_mul_le⟩ := le_mul_inv_iff
alias ⟨le_of_one_le_mul_inv, one_le_mul_inv_of_le⟩ := one_le_mul_inv
alias ⟨le_of_mul_inv_le_one, mul_inv_le_one_of_le⟩ := mul_inv_le_one

end MulRightMono

end Units

namespace IsUnit

section MulLeftMono
variable [MulLeftMono M] {a b c : M} (ha : IsUnit a)

include ha

/-
**IsUnit.mulLECancellable** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：mulLECancellable : MulLECancellable a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mulLECancellable_val`：mulLECancellable_val : MulLECancellable (↑u 
: M)
-/
theorem mulLECancellable : MulLECancellable a :=
  ha.unit.mulLECancellable_val
/-
**IsUnit.mul_le_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：mul_le_mul_left : a * b <= a * c ↔ b <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.Order.Monoid.Unbundled.Units.0.Units.mul_le_mul
_iff_left`：∀ {M : Type u_1} [inst : Monoid M] [inst_1 : LE M] [MulLeftMono M] (u
 : Mˣ) {a b : M}, ↑u * a ≤ ↑u * b ↔ a ≤ b
-/
theorem mul_le_mul_left : a * b ≤ a * c ↔ b ≤ c :=
  ha.unit.mul_le_mul_iff_left

alias ⟨le_of_mul_le_mul_left, _⟩ := mul_le_mul_left

end MulLeftMono

section MulRightMono
variable [MulRightMono M] {a b c : M} (hc : IsUnit c)

include hc

/-
**IsUnit.mul_le_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：mul_le_mul_right : a * c <= b * c ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.Order.Monoid.Unbundled.Units.0.Units.mul_le_mul
_iff_right`：∀ {M : Type u_1} [inst : Monoid M] [inst_1 : LE M] [MulRightMono M] 
{a b : M} (u : Mˣ), a * ↑u ≤ b * ↑u ↔ a ≤ b
-/
theorem mul_le_mul_right : a * c ≤ b * c ↔ a ≤ b :=
  hc.unit.mul_le_mul_iff_right

alias ⟨le_of_mul_le_mul_right, _⟩ := mul_le_mul_right

end MulRightMono

end IsUnit

