/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Sub.Defs

/-!
# Ordered groups

This file develops the basics of unbundled ordered groups.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/

public section

assert_not_exists IsOrderedMonoid

open Function

universe u

variable {α : Type u}

section Group

variable [Group α]

section MulLeftMono

variable [LE α] [MulLeftMono α] {a b c : α}

/-- Uses `left` co(ntra)variant. -/
@[to_additive (attr := simp) /-- Uses `left` co(ntra)variant. -/]
/-
**Left.inv_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.inv_le_one_iff : a⁻¹ <= 1 ↔ 1 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_left`：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflect
LE α] (a : α) {b c : α} : a * b <= a * c ↔ b <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Uses `left` co(ntra)variant.
-/
theorem Left.inv_le_one_iff : a⁻¹ ≤ 1 ↔ 1 ≤ a := by
  rw [← mul_le_mul_iff_left a]
  simp

/-- Uses `left` co(ntra)variant. -/
@[to_additive (attr := simp) /-- Uses `left` co(ntra)variant. -/]
/-
**Left.one_le_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.one_le_inv_iff : 1 <= a⁻¹ ↔ a <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_left`：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflect
LE α] (a : α) {b c : α} : a * b <= a * c ↔ b <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Uses `left` co(ntra)variant.
-/
theorem Left.one_le_inv_iff : 1 ≤ a⁻¹ ↔ a ≤ 1 := by
  rw [← mul_le_mul_iff_left a]
  simp

@[to_additive (attr := simp)]
/-
**le_inv_mul_iff_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_inv_mul_iff_mul_le : b <= a⁻¹ * c ↔ a * b <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_left`：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflect
LE α] (a : α) {b c : α} : a * b <= a * c ↔ b <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_inv_mul_iff_mul_le : b ≤ a⁻¹ * c ↔ a * b ≤ c := by
  rw [← mul_le_mul_iff_left a]
  simp

@[to_additive (attr := simp)]
/-
**inv_mul_le_iff_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_le_iff_le_mul : b⁻¹ * a <= c ↔ a <= b * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_left`：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflect
LE α] (a : α) {b c : α} : a * b <= a * c ↔ b <= c
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_mul_le_iff_le_mul : b⁻¹ * a ≤ c ↔ a ≤ b * c := by
  rw [← mul_le_mul_iff_left b, mul_inv_cancel_left]

@[to_additive neg_le_iff_add_nonneg']
/-
**inv_le_iff_one_le_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_le_iff_one_le_mul' : a⁻¹ <= b ↔ 1 <= a * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_le_mul_iff_left`：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflect
LE α] (a : α) {b c : α} : a * b <= a * c ↔ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_le_iff_one_le_mul' : a⁻¹ ≤ b ↔ 1 ≤ a * b :=
  (mul_le_mul_iff_left a).symm.trans <| by rw [mul_inv_cancel]

@[to_additive]
/-
**le_inv_iff_mul_le_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_inv_iff_mul_le_one_left : a <= b⁻¹ ↔ b * a <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_le_mul_iff_left`：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflect
LE α] (a : α) {b c : α} : a * b <= a * c ↔ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_inv_iff_mul_le_one_left : a ≤ b⁻¹ ↔ b * a ≤ 1 :=
  (mul_le_mul_iff_left b).symm.trans <| by rw [mul_inv_cancel]

@[to_additive]
/-
**le_inv_mul_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_inv_mul_iff_le : 1 <= b⁻¹ * a ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_left`：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflect
LE α] (a : α) {b c : α} : a * b <= a * c ↔ b <= c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_inv_mul_iff_le : 1 ≤ b⁻¹ * a ↔ b ≤ a := by
  rw [← mul_le_mul_iff_left b, mul_one, mul_inv_cancel_left]

@[to_additive]
/-
**inv_mul_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_le_one_iff : a⁻¹ * b <= 1 ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `inv_mul_le_iff_le_mul`：inv_mul_le_iff_le_mul : b⁻¹ * a <= c ↔ a <= b * c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_mul_le_one_iff : a⁻¹ * b ≤ 1 ↔ b ≤ a :=
  inv_mul_le_iff_le_mul.trans <| by rw [mul_one]

end MulLeftMono

section MulLeftStrictMono

variable [LT α] [MulLeftStrictMono α] {a b c : α}

/-- Uses `left` co(ntra)variant. -/
@[to_additive (attr := simp) Left.neg_pos_iff /-- Uses `left` co(ntra)variant. -/]
/-
**Left.one_lt_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_left`：mul_lt_mul_iff_left [MulLeftStrictMono α] [MulLeftR
eflectLT α] (a : α) {b c : α} : a * b < a * c ↔ b < c
· 使用定理 `Group.covconv`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N] [Cov
ariantClass N N (fun x1 x2 => x1 * x2) r],   ContravariantClass N N (fun x1 x2 =
> x…
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Uses `left` co(ntra)variant.
-/
theorem Left.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1 := by
  rw [← mul_lt_mul_iff_left a, mul_inv_cancel, mul_one]

/-- Uses `left` co(ntra)variant. -/
@[to_additive (attr := simp) /-- Uses `left` co(ntra)variant. -/]
/-
**Left.inv_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.inv_lt_one_iff : a⁻¹ < 1 ↔ 1 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_left`：mul_lt_mul_iff_left [MulLeftStrictMono α] [MulLeftR
eflectLT α] (a : α) {b c : α} : a * b < a * c ↔ b < c
· 使用定理 `Group.covconv`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N] [Cov
ariantClass N N (fun x1 x2 => x1 * x2) r],   ContravariantClass N N (fun x1 x2 =
> x…
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Uses `left` co(ntra)variant.
-/
theorem Left.inv_lt_one_iff : a⁻¹ < 1 ↔ 1 < a := by
  rw [← mul_lt_mul_iff_left a, mul_inv_cancel, mul_one]

@[to_additive (attr := simp)]
/-
**lt_inv_mul_iff_mul_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_inv_mul_iff_mul_lt : b < a⁻¹ * c ↔ a * b < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_left`：mul_lt_mul_iff_left [MulLeftStrictMono α] [MulLeftR
eflectLT α] (a : α) {b c : α} : a * b < a * c ↔ b < c
· 使用定理 `Group.covconv`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N] [Cov
ariantClass N N (fun x1 x2 => x1 * x2) r],   ContravariantClass N N (fun x1 x2 =
> x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_inv_mul_iff_mul_lt : b < a⁻¹ * c ↔ a * b < c := by
  rw [← mul_lt_mul_iff_left a]
  simp

@[to_additive (attr := simp)]
/-
**inv_mul_lt_iff_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_lt_iff_lt_mul : b⁻¹ * a < c ↔ a < b * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_left`：mul_lt_mul_iff_left [MulLeftStrictMono α] [MulLeftR
eflectLT α] (a : α) {b c : α} : a * b < a * c ↔ b < c
· 使用定理 `Group.covconv`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N] [Cov
ariantClass N N (fun x1 x2 => x1 * x2) r],   ContravariantClass N N (fun x1 x2 =
> x…
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_mul_lt_iff_lt_mul : b⁻¹ * a < c ↔ a < b * c := by
  rw [← mul_lt_mul_iff_left b, mul_inv_cancel_left]

@[to_additive]
/-
**inv_lt_iff_one_lt_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_lt_iff_one_lt_mul' : a⁻¹ < b ↔ 1 < a * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_lt_mul_iff_left`：mul_lt_mul_iff_left [MulLeftStrictMono α] [MulLeftR
eflectLT α] (a : α) {b c : α} : a * b < a * c ↔ b < c
· 使用定理 `Group.covconv`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N] [Cov
ariantClass N N (fun x1 x2 => x1 * x2) r],   ContravariantClass N N (fun x1 x2 =
> x…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_lt_iff_one_lt_mul' : a⁻¹ < b ↔ 1 < a * b :=
  (mul_lt_mul_iff_left a).symm.trans <| by rw [mul_inv_cancel]

@[to_additive]
/-
**lt_inv_iff_mul_lt_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_inv_iff_mul_lt_one' : a < b⁻¹ ↔ b * a < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_lt_mul_iff_left`：mul_lt_mul_iff_left [MulLeftStrictMono α] [MulLeftR
eflectLT α] (a : α) {b c : α} : a * b < a * c ↔ b < c
· 使用定理 `Group.covconv`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N] [Cov
ariantClass N N (fun x1 x2 => x1 * x2) r],   ContravariantClass N N (fun x1 x2 =
> x…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_inv_iff_mul_lt_one' : a < b⁻¹ ↔ b * a < 1 :=
  (mul_lt_mul_iff_left b).symm.trans <| by rw [mul_inv_cancel]

@[to_additive]
/-
**lt_inv_mul_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_inv_mul_iff_lt : 1 < b⁻¹ * a ↔ b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_left`：mul_lt_mul_iff_left [MulLeftStrictMono α] [MulLeftR
eflectLT α] (a : α) {b c : α} : a * b < a * c ↔ b < c
· 使用定理 `Group.covconv`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N] [Cov
ariantClass N N (fun x1 x2 => x1 * x2) r],   ContravariantClass N N (fun x1 x2 =
> x…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_inv_mul_iff_lt : 1 < b⁻¹ * a ↔ b < a := by
  rw [← mul_lt_mul_iff_left b, mul_one, mul_inv_cancel_left]

@[to_additive]
/-
**inv_mul_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_lt_one_iff : a⁻¹ * b < 1 ↔ b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `inv_mul_lt_iff_lt_mul`：inv_mul_lt_iff_lt_mul : b⁻¹ * a < c ↔ a < b * c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_mul_lt_one_iff : a⁻¹ * b < 1 ↔ b < a :=
  _root_.trans inv_mul_lt_iff_lt_mul <| by rw [mul_one]

end MulLeftStrictMono

section MulRightMono

variable [LE α] [MulRightMono α] {a b c : α}

/-- Uses `right` co(ntra)variant. -/
@[to_additive (attr := simp) /-- Uses `right` co(ntra)variant. -/]
/-
**Right.inv_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.inv_le_one_iff : a⁻¹ <= 1 ↔ 1 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Uses `right` co(ntra)variant.
-/
theorem Right.inv_le_one_iff : a⁻¹ ≤ 1 ↔ 1 ≤ a := by
  rw [← mul_le_mul_iff_right a]
  simp

/-- Uses `right` co(ntra)variant. -/
@[to_additive (attr := simp) /-- Uses `right` co(ntra)variant. -/]
/-
**Right.one_le_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.one_le_inv_iff : 1 <= a⁻¹ ↔ a <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Uses `right` co(ntra)variant.
-/
theorem Right.one_le_inv_iff : 1 ≤ a⁻¹ ↔ a ≤ 1 := by
  rw [← mul_le_mul_iff_right a]
  simp

@[to_additive neg_le_iff_add_nonneg]
/-
**inv_le_iff_one_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_le_iff_one_le_mul : a⁻¹ <= b ↔ 1 <= b * a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_le_iff_one_le_mul : a⁻¹ ≤ b ↔ 1 ≤ b * a :=
  (mul_le_mul_iff_right a).symm.trans <| by rw [inv_mul_cancel]

@[to_additive]
/-
**le_inv_iff_mul_le_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_inv_iff_mul_le_one_right : a <= b⁻¹ ↔ a * b <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_inv_iff_mul_le_one_right : a ≤ b⁻¹ ↔ a * b ≤ 1 :=
  (mul_le_mul_iff_right b).symm.trans <| by rw [inv_mul_cancel]

@[to_additive (attr := simp)]
/-
**mul_inv_le_iff_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_le_iff_le_mul : a * b⁻¹ <= c ↔ a <= c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_le_iff_le_mul : a * b⁻¹ ≤ c ↔ a ≤ c * b :=
  (mul_le_mul_iff_right b).symm.trans <| by rw [inv_mul_cancel_right]

@[to_additive (attr := simp)]
/-
**le_mul_inv_iff_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_inv_iff_mul_le : c <= a * b⁻¹ ↔ c * b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_mul_inv_iff_mul_le : c ≤ a * b⁻¹ ↔ c * b ≤ a :=
  (mul_le_mul_iff_right b).symm.trans <| by rw [inv_mul_cancel_right]

@[to_additive]
/-
**mul_inv_le_one_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_le_one_iff_le : a * b⁻¹ <= 1 ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mul_inv_le_iff_le_mul`：mul_inv_le_iff_le_mul : a * b⁻¹ <= c ↔ a <= c * b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_le_one_iff_le : a * b⁻¹ ≤ 1 ↔ a ≤ b :=
  mul_inv_le_iff_le_mul.trans <| by rw [one_mul]

@[to_additive]
/-
**le_mul_inv_iff_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_inv_iff_le : 1 <= a * b⁻¹ ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_mul_inv_iff_le : 1 ≤ a * b⁻¹ ↔ b ≤ a := by
  rw [← mul_le_mul_iff_right b, one_mul, inv_mul_cancel_right]

@[to_additive]
/-
**mul_inv_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_le_one_iff : b * a⁻¹ <= 1 ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `mul_inv_le_iff_le_mul`：mul_inv_le_iff_le_mul : a * b⁻¹ <= c ↔ a <= c * b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_le_one_iff : b * a⁻¹ ≤ 1 ↔ b ≤ a :=
  _root_.trans mul_inv_le_iff_le_mul <| by rw [one_mul]

end MulRightMono

section MulRightStrictMono

variable [LT α] [MulRightStrictMono α] {a b c : α}

/-- Uses `right` co(ntra)variant. -/
@[to_additive (attr := simp) /-- Uses `right` co(ntra)variant. -/]
/-
**Right.inv_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.inv_lt_one_iff : a⁻¹ < 1 ↔ 1 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Uses `right` co(ntra)variant.
-/
theorem Right.inv_lt_one_iff : a⁻¹ < 1 ↔ 1 < a := by
  rw [← mul_lt_mul_iff_right a, inv_mul_cancel, one_mul]

/-- Uses `right` co(ntra)variant. -/
@[to_additive (attr := simp) Right.neg_pos_iff /-- Uses `right` co(ntra)variant. -/]
/-
**Right.one_lt_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Uses `right` co(ntra)variant.
-/
theorem Right.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1 := by
  rw [← mul_lt_mul_iff_right a, inv_mul_cancel, one_mul]

@[to_additive]
/-
**inv_lt_iff_one_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_lt_iff_one_lt_mul : a⁻¹ < b ↔ 1 < b * a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_lt_iff_one_lt_mul : a⁻¹ < b ↔ 1 < b * a :=
  (mul_lt_mul_iff_right a).symm.trans <| by rw [inv_mul_cancel]

@[to_additive]
/-
**lt_inv_iff_mul_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_inv_iff_mul_lt_one : a < b⁻¹ ↔ a * b < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_inv_iff_mul_lt_one : a < b⁻¹ ↔ a * b < 1 :=
  (mul_lt_mul_iff_right b).symm.trans <| by rw [inv_mul_cancel]

@[to_additive (attr := simp)]
/-
**mul_inv_lt_iff_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_lt_iff_lt_mul : a * b⁻¹ < c ↔ a < c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_lt_iff_lt_mul : a * b⁻¹ < c ↔ a < c * b := by
  rw [← mul_lt_mul_iff_right b, inv_mul_cancel_right]

@[to_additive (attr := simp)]
/-
**lt_mul_inv_iff_mul_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_inv_iff_mul_lt : c < a * b⁻¹ ↔ c * b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_mul_inv_iff_mul_lt : c < a * b⁻¹ ↔ c * b < a :=
  (mul_lt_mul_iff_right b).symm.trans <| by rw [inv_mul_cancel_right]

@[to_additive]
/-
**inv_mul_lt_one_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_lt_one_iff_lt : a * b⁻¹ < 1 ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_mul_lt_one_iff_lt : a * b⁻¹ < 1 ↔ a < b := by
  rw [← mul_lt_mul_iff_right b, inv_mul_cancel_right, one_mul]

@[to_additive]
/-
**lt_mul_inv_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_inv_iff_lt : 1 < a * b⁻¹ ↔ b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_mul_inv_iff_lt : 1 < a * b⁻¹ ↔ b < a := by
  rw [← mul_lt_mul_iff_right b, one_mul, inv_mul_cancel_right]

@[to_additive]
/-
**mul_inv_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_lt_one_iff : b * a⁻¹ < 1 ↔ b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `mul_inv_lt_iff_lt_mul`：mul_inv_lt_iff_lt_mul : a * b⁻¹ < c ↔ a < c * b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_lt_one_iff : b * a⁻¹ < 1 ↔ b < a :=
  _root_.trans mul_inv_lt_iff_lt_mul <| by rw [one_mul]

end MulRightStrictMono

section MulLeftMono_MulRightMono

variable [LE α] [MulLeftMono α] {a b c d : α}

@[to_additive (attr := simp)]
/-
**div_le_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_self_iff (a : α) {b : α} : a / b <= a ↔ 1 <= b
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem div_le_self_iff (a : α) {b : α} : a / b ≤ a ↔ 1 ≤ b := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/-
**le_div_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_div_self_iff (a : α) {b : α} : a <= a / b ↔ b <= 1
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_div_self_iff (a : α) {b : α} : a ≤ a / b ↔ b ≤ 1 := by
  simp [div_eq_mul_inv]

alias ⟨_, sub_le_self⟩ := sub_le_self_iff

variable [MulRightMono α]

@[to_additive (attr := simp)]
/-
**inv_le_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_le_inv_iff : a⁻¹ <= b⁻¹ ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_left`：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflect
LE α] (a : α) {b c : α} : a * b <= a * c ↔ b <= c
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inv_le_inv_iff : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := by
  rw [← mul_le_mul_iff_left a, ← mul_le_mul_iff_right b]
  simp

alias ⟨le_of_neg_le_neg, _⟩ := neg_le_neg_iff

@[to_additive]
/-
**mul_inv_le_inv_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_le_inv_mul_iff : a * b⁻¹ <= d⁻¹ * c ↔ d * a <= c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_left`：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflect
LE α] (a : α) {b c : α} : a * b <= a * c ↔ b <= c
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_le_inv_mul_iff : a * b⁻¹ ≤ d⁻¹ * c ↔ d * a ≤ c * b := by
  rw [← mul_le_mul_iff_left d, ← mul_le_mul_iff_right b, mul_inv_cancel_left, mul_assoc,
    inv_mul_cancel_right]

end MulLeftMono_MulRightMono

section MulLeftStrictMono_MulRightStrictMono

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

@[to_additive (attr := simp)]
/-
**div_lt_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_lt_self_iff (a : α) {b : α} : a / b < a ↔ 1 < b
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Group.covconv`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N] [Cov
ariantClass N N (fun x1 x2 => x1 * x2) r],   ContravariantClass N N (fun x1 x2 =
> x…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem div_lt_self_iff (a : α) {b : α} : a / b < a ↔ 1 < b := by
  simp [div_eq_mul_inv]

alias ⟨_, sub_lt_self⟩ := sub_lt_self_iff

variable [MulRightStrictMono α]

@[to_additive (attr := simp)]
/-
**inv_lt_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_left`：mul_lt_mul_iff_left [MulLeftStrictMono α] [MulLeftR
eflectLT α] (a : α) {b c : α} : a * b < a * c ↔ b < c
· 使用定理 `Group.covconv`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N] [Cov
ariantClass N N (fun x1 x2 => x1 * x2) r],   ContravariantClass N N (fun x1 x2 =
> x…
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a := by
  rw [← mul_lt_mul_iff_left a, ← mul_lt_mul_iff_right b]
  simp

@[to_additive neg_lt]
/-
**inv_lt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_lt' : a⁻¹ < b ↔ b⁻¹ < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_lt_inv_iff`：inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_lt' : a⁻¹ < b ↔ b⁻¹ < a := by rw [← inv_lt_inv_iff, inv_inv]

@[to_additive lt_neg]
/-
**lt_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_inv' : a < b⁻¹ ↔ b < a⁻¹
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_lt_inv_iff`：inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_inv' : a < b⁻¹ ↔ b < a⁻¹ := by rw [← inv_lt_inv_iff, inv_inv]

alias ⟨lt_inv_of_lt_inv, _⟩ := lt_inv'

attribute [to_additive] lt_inv_of_lt_inv

alias ⟨inv_lt_of_inv_lt', _⟩ := inv_lt'

attribute [to_additive neg_lt_of_neg_lt] inv_lt_of_inv_lt'

@[to_additive]
/-
**mul_inv_lt_inv_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_lt_inv_mul_iff : a * b⁻¹ < d⁻¹ * c ↔ d * a < c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_left`：mul_lt_mul_iff_left [MulLeftStrictMono α] [MulLeftR
eflectLT α] (a : α) {b c : α} : a * b < a * c ↔ b < c
· 使用定理 `Group.covconv`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N] [Cov
ariantClass N N (fun x1 x2 => x1 * x2) r],   ContravariantClass N N (fun x1 x2 =
> x…
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_lt_inv_mul_iff : a * b⁻¹ < d⁻¹ * c ↔ d * a < c * b := by
  rw [← mul_lt_mul_iff_left d, ← mul_lt_mul_iff_right b, mul_inv_cancel_left, mul_assoc,
    inv_mul_cancel_right]

end MulLeftStrictMono_MulRightStrictMono

section Preorder

variable [Preorder α]

section LeftLE

variable [MulLeftMono α] {a : α}

@[to_additive]
/-
**Left.inv_le_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.inv_le_self (h : 1 <= a) : a⁻¹ <= a
参数：h : 1 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.inv_le_one_iff`：Left.inv_le_one_iff : a⁻¹ <= 1 ↔ 1 <= a
-/
theorem Left.inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a :=
  le_trans (Left.inv_le_one_iff.mpr h) h

alias neg_le_self := Left.neg_le_self

@[to_additive]
/-
**Left.self_le_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.self_le_inv (h : a <= 1) : a <= a⁻¹
参数：h : a <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.one_le_inv_iff`：Left.one_le_inv_iff : 1 <= a⁻¹ ↔ a <= 1
-/
theorem Left.self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ :=
  le_trans h (Left.one_le_inv_iff.mpr h)

end LeftLE

section LeftLT

variable [MulLeftStrictMono α] {a : α}

@[to_additive]
/-
**Left.inv_lt_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.inv_lt_self (h : 1 < a) : a⁻¹ < a
参数：h : 1 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.inv_lt_one_iff`：Left.inv_lt_one_iff : a⁻¹ < 1 ↔ 1 < a
-/
theorem Left.inv_lt_self (h : 1 < a) : a⁻¹ < a :=
  (Left.inv_lt_one_iff.mpr h).trans h

alias neg_lt_self := Left.neg_lt_self

@[to_additive]
/-
**Left.self_lt_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Left.self_lt_inv (h : a < 1) : a < a⁻¹
参数：h : a < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.one_lt_inv_iff`：Left.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1
-/
theorem Left.self_lt_inv (h : a < 1) : a < a⁻¹ :=
  lt_trans h (Left.one_lt_inv_iff.mpr h)

end LeftLT

section RightLE

variable [MulRightMono α] {a : α}

@[to_additive]
/-
**Right.inv_le_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.inv_le_self (h : 1 <= a) : a⁻¹ <= a
参数：h : 1 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Right.inv_le_one_iff`：Right.inv_le_one_iff : a⁻¹ <= 1 ↔ 1 <= a
-/
theorem Right.inv_le_self (h : 1 ≤ a) : a⁻¹ ≤ a :=
  le_trans (Right.inv_le_one_iff.mpr h) h

@[to_additive]
/-
**Right.self_le_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.self_le_inv (h : a <= 1) : a <= a⁻¹
参数：h : a <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Right.one_le_inv_iff`：Right.one_le_inv_iff : 1 <= a⁻¹ ↔ a <= 1
-/
theorem Right.self_le_inv (h : a ≤ 1) : a ≤ a⁻¹ :=
  le_trans h (Right.one_le_inv_iff.mpr h)

end RightLE

section RightLT

variable [MulRightStrictMono α] {a : α}

@[to_additive]
/-
**Right.inv_lt_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.inv_lt_self (h : 1 < a) : a⁻¹ < a
参数：h : 1 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Right.inv_lt_one_iff`：Right.inv_lt_one_iff : a⁻¹ < 1 ↔ 1 < a
-/
theorem Right.inv_lt_self (h : 1 < a) : a⁻¹ < a :=
  (Right.inv_lt_one_iff.mpr h).trans h

@[to_additive]
/-
**Right.self_lt_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Right.self_lt_inv (h : a < 1) : a < a⁻¹
参数：h : a < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Right.one_lt_inv_iff`：Right.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1
-/
theorem Right.self_lt_inv (h : a < 1) : a < a⁻¹ :=
  lt_trans h (Right.one_lt_inv_iff.mpr h)

end RightLT

end Preorder

end Group

section CommGroup

variable [CommGroup α]

section LE

variable [LE α] [MulLeftMono α] {a b c d : α}

@[to_additive]
/-
**inv_mul_le_iff_le_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_le_iff_le_mul' : c⁻¹ * a <= b ↔ a <= b * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_le_iff_le_mul`：inv_mul_le_iff_le_mul : b⁻¹ * a <= c ↔ a <= b * c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_mul_le_iff_le_mul' : c⁻¹ * a ≤ b ↔ a ≤ b * c := by rw [inv_mul_le_iff_le_mul, mul_comm]

@[to_additive]
/-
**mul_inv_le_iff_le_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_le_iff_le_mul' : a * b⁻¹ <= c ↔ a <= b * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_le_iff_le_mul`：inv_mul_le_iff_le_mul : b⁻¹ * a <= c ↔ a <= b * c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_le_iff_le_mul' : a * b⁻¹ ≤ c ↔ a ≤ b * c := by
  rw [← inv_mul_le_iff_le_mul, mul_comm]

@[to_additive add_neg_le_add_neg_iff]
/-
**mul_inv_le_mul_inv_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_le_mul_inv_iff' : a * b⁻¹ <= c * d⁻¹ ↔ a * d <= c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_inv_le_inv_mul_iff`：mul_inv_le_inv_mul_iff : a * b⁻¹ <= d⁻¹ * c ↔ d 
* a <= c * b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_le_mul_inv_iff' : a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b := by
  rw [mul_comm c, mul_inv_le_inv_mul_iff, mul_comm]

end LE

section LT

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

@[to_additive]
/-
**inv_mul_lt_iff_lt_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_mul_lt_iff_lt_mul' : c⁻¹ * a < b ↔ a < b * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_lt_iff_lt_mul`：inv_mul_lt_iff_lt_mul : b⁻¹ * a < c ↔ a < b * c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_mul_lt_iff_lt_mul' : c⁻¹ * a < b ↔ a < b * c := by rw [inv_mul_lt_iff_lt_mul, mul_comm]

@[to_additive]
/-
**mul_inv_lt_iff_le_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_lt_iff_le_mul' : a * b⁻¹ < c ↔ a < b * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_lt_iff_lt_mul`：inv_mul_lt_iff_lt_mul : b⁻¹ * a < c ↔ a < b * c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_lt_iff_le_mul' : a * b⁻¹ < c ↔ a < b * c := by
  rw [← inv_mul_lt_iff_lt_mul, mul_comm]

@[to_additive add_neg_lt_add_neg_iff]
/-
**mul_inv_lt_mul_inv_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_lt_mul_inv_iff' : a * b⁻¹ < c * d⁻¹ ↔ a * d < c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_inv_lt_inv_mul_iff`：mul_inv_lt_inv_mul_iff : a * b⁻¹ < d⁻¹ * c ↔ d *
 a < c * b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_lt_mul_inv_iff' : a * b⁻¹ < c * d⁻¹ ↔ a * d < c * b := by
  rw [mul_comm c, mul_inv_lt_inv_mul_iff, mul_comm]

end LT

end CommGroup

alias ⟨one_le_of_inv_le_one, _⟩ := Left.inv_le_one_iff

attribute [to_additive] one_le_of_inv_le_one

alias ⟨le_one_of_one_le_inv, _⟩ := Left.one_le_inv_iff

attribute [to_additive nonpos_of_neg_nonneg] le_one_of_one_le_inv

alias ⟨lt_of_inv_lt_inv, _⟩ := inv_lt_inv_iff

attribute [to_additive] lt_of_inv_lt_inv

alias ⟨one_lt_of_inv_lt_one, _⟩ := Left.inv_lt_one_iff

attribute [to_additive] one_lt_of_inv_lt_one

alias inv_lt_one_iff_one_lt := Left.inv_lt_one_iff

attribute [to_additive] inv_lt_one_iff_one_lt

alias inv_lt_one' := Left.inv_lt_one_iff

attribute [to_additive neg_lt_zero] inv_lt_one'

alias ⟨inv_of_one_lt_inv, _⟩ := Left.one_lt_inv_iff

attribute [to_additive neg_of_neg_pos] inv_of_one_lt_inv

alias ⟨_, one_lt_inv_of_inv⟩ := Left.one_lt_inv_iff

attribute [to_additive neg_pos_of_neg] one_lt_inv_of_inv

alias ⟨mul_le_of_le_inv_mul, _⟩ := le_inv_mul_iff_mul_le

attribute [to_additive] mul_le_of_le_inv_mul

alias ⟨_, le_inv_mul_of_mul_le⟩ := le_inv_mul_iff_mul_le

attribute [to_additive] le_inv_mul_of_mul_le

alias ⟨_, inv_mul_le_of_le_mul⟩ := inv_mul_le_iff_le_mul

attribute [to_additive] inv_mul_le_of_le_mul

alias ⟨mul_lt_of_lt_inv_mul, _⟩ := lt_inv_mul_iff_mul_lt

attribute [to_additive] mul_lt_of_lt_inv_mul

alias ⟨_, lt_inv_mul_of_mul_lt⟩ := lt_inv_mul_iff_mul_lt

attribute [to_additive] lt_inv_mul_of_mul_lt

alias ⟨lt_mul_of_inv_mul_lt, inv_mul_lt_of_lt_mul⟩ := inv_mul_lt_iff_lt_mul

attribute [to_additive] lt_mul_of_inv_mul_lt

attribute [to_additive] inv_mul_lt_of_lt_mul

alias lt_mul_of_inv_mul_lt_left := lt_mul_of_inv_mul_lt

attribute [to_additive] lt_mul_of_inv_mul_lt_left

alias inv_le_one' := Left.inv_le_one_iff

attribute [to_additive neg_nonpos] inv_le_one'

alias one_le_inv' := Left.one_le_inv_iff

attribute [to_additive neg_nonneg] one_le_inv'

alias one_lt_inv' := Left.one_lt_inv_iff

attribute [to_additive neg_pos] one_lt_inv'

--  Most of the lemmas that are primed in this section appear in ordered_field.
--  I (DT) did not try to minimise the assumptions.
section Group

variable [Group α] [LE α]

section Right

variable [MulRightMono α] {a b c : α}

@[to_additive]
/-
**div_le_div_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_div_iff_right (c : α) : a / c <= b / c ↔ a <= b
参数：c : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
-/
theorem div_le_div_iff_right (c : α) : a / c ≤ b / c ↔ a ≤ b := by
  simpa only [div_eq_mul_inv] using mul_le_mul_iff_right _

@[to_additive (attr := gcongr) sub_le_sub_right]
/-
**div_le_div_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_div_right' (h : a <= b) (c : α) : a / c <= b / c
参数：h : a <= b；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_le_div_iff_right`：div_le_div_iff_right (c : α) : a / c <= b / c ↔ a 
<= b
-/
theorem div_le_div_right' (h : a ≤ b) (c : α) : a / c ≤ b / c :=
  (div_le_div_iff_right c).2 h

@[to_additive (attr := simp) sub_nonneg]
/-
**one_le_div'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_le_div' : 1 <= a / b ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_le_div' : 1 ≤ a / b ↔ b ≤ a := by
  rw [← mul_le_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias ⟨le_of_sub_nonneg, sub_nonneg_of_le⟩ := sub_nonneg

@[to_additive sub_nonpos]
/-
**div_le_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_one' : a / b <= 1 ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_le_one' : a / b ≤ 1 ↔ a ≤ b := by
  rw [← mul_le_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias ⟨le_of_sub_nonpos, sub_nonpos_of_le⟩ := sub_nonpos

@[to_additive]
/-
**le_div_iff_mul_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_div_iff_mul_le : a <= c / b ↔ a * b <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_div_iff_mul_le : a ≤ c / b ↔ a * b ≤ c := by
  rw [← mul_le_mul_iff_right b, div_eq_mul_inv, inv_mul_cancel_right]

alias ⟨add_le_of_le_sub_right, le_sub_right_of_add_le⟩ := le_sub_iff_add_le

@[to_additive]
/-
**div_le_iff_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_iff_le_mul : a / c <= b ↔ a <= b * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_right`：mul_le_mul_iff_right [MulRightMono α] [MulRightRef
lectLE α] (a : α) {b c : α} : b * a <= c * a ↔ b <= c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_le_iff_le_mul : a / c ≤ b ↔ a ≤ b * c := by
  rw [← mul_le_mul_iff_right c, div_eq_mul_inv, inv_mul_cancel_right]

-- Note: we intentionally don't have `@[simp]` for the additive version,
-- since the LHS simplifies with `tsub_le_iff_right`
attribute [simp] div_le_iff_le_mul

-- TODO: Should we get rid of `sub_le_iff_le_add` in favor of
-- (a renamed version of) `tsub_le_iff_right`?
-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) AddGroup.toOrderedSub {α : Type*} [AddGroup α] [LE α]
    [AddRightMono α] : OrderedSub α :=
  ⟨fun _ _ _ => sub_le_iff_le_add⟩

end Right

section Left

variable [MulLeftMono α] [MulRightMono α] {a b c : α}

@[to_additive]
/-
**div_le_div_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_div_iff_left (a : α) : a / b <= a / c ↔ c <= b
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_left`：mul_le_mul_iff_left [MulLeftMono α] [MulLeftReflect
LE α] (a : α) {b c : α} : a * b <= a * c ↔ b <= c
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `inv_le_inv_iff`：inv_le_inv_iff : a⁻¹ <= b⁻¹ ↔ b <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_le_div_iff_left (a : α) : a / b ≤ a / c ↔ c ≤ b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_le_mul_iff_left a⁻¹, inv_mul_cancel_left,
    inv_mul_cancel_left, inv_le_inv_iff]

@[to_additive (attr := gcongr) sub_le_sub_left]
/-
**div_le_div_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_div_left' (h : a <= b) (c : α) : c / b <= c / a
参数：h : a <= b；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_le_div_iff_left`：div_le_div_iff_left (a : α) : a / b <= a / c ↔ c <=
 b
-/
theorem div_le_div_left' (h : a ≤ b) (c : α) : c / b ≤ c / a :=
  (div_le_div_iff_left c).2 h

end Left

end Group

section CommGroup

variable [CommGroup α]

section LE

variable [LE α] [MulLeftMono α] {a b c d : α}

/-- See also `div_le_div_iff` for a version that works for `LinearOrderedSemifield` with
additional assumptions. -/
@[to_additive sub_le_sub_iff]
/-
**div_le_div_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_div_iff' : a / b <= c / d ↔ a * d <= c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_le_mul_inv_iff'`：mul_inv_le_mul_inv_iff' : a * b⁻¹ <= c * d⁻¹ ↔ 
a * d <= c * b

--- 原说明 ---
See also `div_le_div_iff` for a version that works for `LinearOrderedSemifield` 
with
additional assumptions.
-/
theorem div_le_div_iff' : a / b ≤ c / d ↔ a * d ≤ c * b := by
  simpa only [div_eq_mul_inv] using mul_inv_le_mul_inv_iff'

@[to_additive]
/-
**le_div_iff_mul_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_div_iff_mul_le' : b <= c / a ↔ a * b <= c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_div_iff_mul_le`：le_div_iff_mul_le : a <= c / b ↔ a * b <= c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_div_iff_mul_le' : b ≤ c / a ↔ a * b ≤ c := by rw [le_div_iff_mul_le, mul_comm]

alias ⟨add_le_of_le_sub_left, le_sub_left_of_add_le⟩ := le_sub_iff_add_le'

@[to_additive]
/-
**div_le_iff_le_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_iff_le_mul' : a / b <= c ↔ a <= b * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_le_iff_le_mul`：div_le_iff_le_mul : a / c <= b ↔ a <= b * c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_le_iff_le_mul' : a / b ≤ c ↔ a ≤ b * c := by rw [div_le_iff_le_mul, mul_comm]

alias ⟨le_add_of_sub_left_le, sub_left_le_of_le_add⟩ := sub_le_iff_le_add'

@[to_additive (attr := simp)]
/-
**inv_le_div_iff_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_le_div_iff_le_mul : b⁻¹ <= a / c ↔ c <= a * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `le_div_iff_mul_le`：le_div_iff_mul_le : a <= c / b ↔ a * b <= c
· 使用定理 `inv_mul_le_iff_le_mul'`：inv_mul_le_iff_le_mul' : c⁻¹ * a <= b ↔ a <= b *
 c
-/
theorem inv_le_div_iff_le_mul : b⁻¹ ≤ a / c ↔ c ≤ a * b :=
  le_div_iff_mul_le.trans inv_mul_le_iff_le_mul'

@[to_additive]
/-
**inv_le_div_iff_le_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_le_div_iff_le_mul' : a⁻¹ <= b / c ↔ c <= a * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_le_div_iff_le_mul`：inv_le_div_iff_le_mul : b⁻¹ <= a / c ↔ c <= a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_le_div_iff_le_mul' : a⁻¹ ≤ b / c ↔ c ≤ a * b := by rw [inv_le_div_iff_le_mul, mul_comm]

@[to_additive]
/-
**div_le_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_comm : a / b <= c ↔ a / c <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `div_le_iff_le_mul'`：div_le_iff_le_mul' : a / b <= c ↔ a <= b * c
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `div_le_iff_le_mul`：div_le_iff_le_mul : a / c <= b ↔ a <= b * c
-/
theorem div_le_comm : a / b ≤ c ↔ a / c ≤ b :=
  div_le_iff_le_mul'.trans div_le_iff_le_mul.symm

@[to_additive]
/-
**le_div_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_div_comm : a <= b / c ↔ c <= b / a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `le_div_iff_mul_le'`：le_div_iff_mul_le' : b <= c / a ↔ a * b <= c
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `le_div_iff_mul_le`：le_div_iff_mul_le : a <= c / b ↔ a * b <= c
-/
theorem le_div_comm : a ≤ b / c ↔ c ≤ b / a :=
  le_div_iff_mul_le'.trans le_div_iff_mul_le.symm

end LE

section Preorder

variable [Preorder α] [MulLeftMono α] {a b c d : α}

@[to_additive (attr := gcongr) sub_le_sub]
/-
**div_le_div''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_div'' (hab : a <= b) (hcd : c <= d) : a / d <= b / c
参数：hab : a <= b；hcd : c <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_inv_le_inv_mul_iff`：mul_inv_le_inv_mul_iff : a * b⁻¹ <= d⁻¹ * c ↔ d 
* a <= c * b
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
-/
theorem div_le_div'' (hab : a ≤ b) (hcd : c ≤ d) : a / d ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm b, mul_inv_le_inv_mul_iff, mul_comm]
  exact mul_le_mul' hab hcd

end Preorder

end CommGroup

--  Most of the lemmas that are primed in this section appear in ordered_field.
--  I (DT) did not try to minimise the assumptions.
section Group

variable [Group α] [LT α]

section Right

variable [MulRightStrictMono α] {a b c : α}

@[to_additive (attr := simp)]
/-
**div_lt_div_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_lt_div_iff_right (c : α) : a / c < b / c ↔ a < b
参数：c : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
-/
theorem div_lt_div_iff_right (c : α) : a / c < b / c ↔ a < b := by
  simpa only [div_eq_mul_inv] using mul_lt_mul_iff_right _

@[to_additive (attr := gcongr) sub_lt_sub_right]
/-
**div_lt_div_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_lt_div_right' (h : a < b) (c : α) : a / c < b / c
参数：h : a < b；c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_lt_div_iff_right`：div_lt_div_iff_right (c : α) : a / c < b / c ↔ a <
 b
-/
theorem div_lt_div_right' (h : a < b) (c : α) : a / c < b / c :=
  (div_lt_div_iff_right c).2 h

@[to_additive (attr := simp) sub_pos]
/-
**one_lt_div'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_lt_div' : 1 < a / b ↔ b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_lt_div' : 1 < a / b ↔ b < a := by
  rw [← mul_lt_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias ⟨lt_of_sub_pos, sub_pos_of_lt⟩ := sub_pos

@[to_additive (attr := simp) sub_neg /-- For `a - -b = a + b`, see `sub_neg_eq_add`. -/]
/-
**div_lt_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_lt_one' : a / b < 1 ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_lt_one' : a / b < 1 ↔ a < b := by
  rw [← mul_lt_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

alias ⟨lt_of_sub_neg, sub_neg_of_lt⟩ := sub_neg

alias sub_lt_zero := sub_neg

@[to_additive]
/-
**lt_div_iff_mul_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_div_iff_mul_lt : a < c / b ↔ a * b < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_div_iff_mul_lt : a < c / b ↔ a * b < c := by
  rw [← mul_lt_mul_iff_right b, div_eq_mul_inv, inv_mul_cancel_right]

alias ⟨add_lt_of_lt_sub_right, lt_sub_right_of_add_lt⟩ := lt_sub_iff_add_lt

@[to_additive]
/-
**div_lt_iff_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_lt_iff_lt_mul : a / c < b ↔ a < b * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_right`：mul_lt_mul_iff_right [MulRightStrictMono α] [MulRi
ghtReflectLT α] (a : α) {b c : α} : b * a < c * a ↔ b < c
· 使用定理 `Group.covconv_swap`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N]
 [CovariantClass N N (Function.swap fun x1 x2 => x1 * x2) r],   ContravariantCla
ss N N (…
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_lt_iff_lt_mul : a / c < b ↔ a < b * c := by
  rw [← mul_lt_mul_iff_right c, div_eq_mul_inv, inv_mul_cancel_right]

alias ⟨lt_add_of_sub_right_lt, sub_right_lt_of_lt_add⟩ := sub_lt_iff_lt_add

end Right

section Left

variable [MulLeftStrictMono α] [MulRightStrictMono α]
  {a b c : α}

@[to_additive (attr := simp)]
/-
**div_lt_div_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_lt_div_iff_left (a : α) : a / b < a / c ↔ c < b
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_iff_left`：mul_lt_mul_iff_left [MulLeftStrictMono α] [MulLeftR
eflectLT α] (a : α) {b c : α} : a * b < a * c ↔ b < c
· 使用定理 `Group.covconv`：∀ {N : Type u_2} {r : N → N → Prop} [inst : Group N] [Cov
ariantClass N N (fun x1 x2 => x1 * x2) r],   ContravariantClass N N (fun x1 x2 =
> x…
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `inv_lt_inv_iff`：inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_lt_div_iff_left (a : α) : a / b < a / c ↔ c < b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_lt_mul_iff_left a⁻¹, inv_mul_cancel_left,
    inv_mul_cancel_left, inv_lt_inv_iff]

@[to_additive (attr := simp)]
/-
**inv_lt_div_iff_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_lt_div_iff_lt_mul : a⁻¹ < b / c ↔ c < a * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `lt_mul_inv_iff_mul_lt`：lt_mul_inv_iff_mul_lt : c < a * b⁻¹ ↔ c * b < a
· 使用定理 `inv_mul_lt_iff_lt_mul`：inv_mul_lt_iff_lt_mul : b⁻¹ * a < c ↔ a < b * c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_lt_div_iff_lt_mul : a⁻¹ < b / c ↔ c < a * b := by
  rw [div_eq_mul_inv, lt_mul_inv_iff_mul_lt, inv_mul_lt_iff_lt_mul]

@[to_additive (attr := gcongr) sub_lt_sub_left]
/-
**div_lt_div_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_lt_div_left' (h : a < b) (c : α) : c / b < c / a
参数：h : a < b；c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_lt_div_iff_left`：div_lt_div_iff_left (a : α) : a / b < a / c ↔ c < b
-/
theorem div_lt_div_left' (h : a < b) (c : α) : c / b < c / a :=
  (div_lt_div_iff_left c).2 h

end Left

end Group

section CommGroup

variable [CommGroup α]

section LT

variable [LT α] [MulLeftStrictMono α] {a b c d : α}

@[to_additive sub_lt_sub_iff]
/-
**div_lt_div_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_lt_div_iff' : a / b < c / d ↔ a * d < c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_lt_mul_inv_iff'`：mul_inv_lt_mul_inv_iff' : a * b⁻¹ < c * d⁻¹ ↔ a
 * d < c * b
-/
theorem div_lt_div_iff' : a / b < c / d ↔ a * d < c * b := by
  simpa only [div_eq_mul_inv] using mul_inv_lt_mul_inv_iff'

@[to_additive]
/-
**lt_div_iff_mul_lt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_div_iff_mul_lt' : b < c / a ↔ a * b < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_div_iff_mul_lt`：lt_div_iff_mul_lt : a < c / b ↔ a * b < c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_div_iff_mul_lt' : b < c / a ↔ a * b < c := by rw [lt_div_iff_mul_lt, mul_comm]

alias ⟨add_lt_of_lt_sub_left, lt_sub_left_of_add_lt⟩ := lt_sub_iff_add_lt'

@[to_additive]
/-
**div_lt_iff_lt_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_lt_iff_lt_mul' : a / b < c ↔ a < b * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_lt_iff_lt_mul`：div_lt_iff_lt_mul : a / c < b ↔ a < b * c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem div_lt_iff_lt_mul' : a / b < c ↔ a < b * c := by rw [div_lt_iff_lt_mul, mul_comm]

alias ⟨lt_add_of_sub_left_lt, sub_left_lt_of_lt_add⟩ := sub_lt_iff_lt_add'

@[to_additive]
/-
**inv_lt_div_iff_lt_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_lt_div_iff_lt_mul' : b⁻¹ < a / c ↔ c < a * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `lt_div_iff_mul_lt`：lt_div_iff_mul_lt : a < c / b ↔ a * b < c
· 使用定理 `inv_mul_lt_iff_lt_mul'`：inv_mul_lt_iff_lt_mul' : c⁻¹ * a < b ↔ a < b * c
-/
theorem inv_lt_div_iff_lt_mul' : b⁻¹ < a / c ↔ c < a * b :=
  lt_div_iff_mul_lt.trans inv_mul_lt_iff_lt_mul'

@[to_additive]
/-
**div_lt_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_lt_comm : a / b < c ↔ a / c < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `div_lt_iff_lt_mul'`：div_lt_iff_lt_mul' : a / b < c ↔ a < b * c
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `div_lt_iff_lt_mul`：div_lt_iff_lt_mul : a / c < b ↔ a < b * c
-/
theorem div_lt_comm : a / b < c ↔ a / c < b :=
  div_lt_iff_lt_mul'.trans div_lt_iff_lt_mul.symm

@[to_additive]
/-
**lt_div_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_div_comm : a < b / c ↔ c < b / a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `lt_div_iff_mul_lt'`：lt_div_iff_mul_lt' : b < c / a ↔ a * b < c
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `lt_div_iff_mul_lt`：lt_div_iff_mul_lt : a < c / b ↔ a * b < c
-/
theorem lt_div_comm : a < b / c ↔ c < b / a :=
  lt_div_iff_mul_lt'.trans lt_div_iff_mul_lt.symm

end LT

section Preorder

variable [Preorder α] [MulLeftStrictMono α] {a b c d : α}

@[to_additive (attr := gcongr) sub_lt_sub]
/-
**div_lt_div''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_lt_div'' (hab : a < b) (hcd : c < d) : a / d < b / c
参数：hab : a < b；hcd : c < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_inv_lt_inv_mul_iff`：mul_inv_lt_inv_mul_iff : a * b⁻¹ < d⁻¹ * c ↔ d *
 a < c * b
· 使用定理 `mul_lt_mul_of_lt_of_lt`：mul_lt_mul_of_lt_of_lt [MulLeftStrictMono α] [Mu
lRightStrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d
-/
theorem div_lt_div'' (hab : a < b) (hcd : c < d) : a / d < b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm b, mul_inv_lt_inv_mul_iff, mul_comm]
  exact mul_lt_mul_of_lt_of_lt hab hcd

end Preorder

section LinearOrder
variable [LinearOrder α] [MulLeftMono α] {a b c d : α}

/-
**lt_or_lt_of_div_lt_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : CommGroup α] [inst_1 : LinearOrder α] [MulLeftMono 
α] {a b c d : α},   a / d < b / c → a < b ∨ c < d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_le_div''`：div_le_div'' (hab : a <= b) (hcd : c <= d) : a / d <= b / 
c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
@[to_additive] lemma lt_or_lt_of_div_lt_div : a / d < b / c → a < b ∨ c < d := by
  contrapose!; exact fun h ↦ div_le_div'' h.1 h.2

end LinearOrder
end CommGroup

section LinearOrder

variable [Group α] [LinearOrder α]

@[to_additive (attr := simp) cmp_sub_zero]
/-
**cmp_div_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_div_one' [MulRightMono α] (a b : α) : cmp (a / b) 1 = cmp a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `cmp_mul_right'`：cmp_mul_right' {α : Type*} [Mul α] [LinearOrder α] [MulR
ightStrictMono α] (a b c : α) : cmp (a * c) (b * c) = cmp a b
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
-/
theorem cmp_div_one' [MulRightMono α] (a b : α) :
    cmp (a / b) 1 = cmp a b := by rw [← cmp_mul_right' _ _ b, one_mul, div_mul_cancel]

variable [MulLeftMono α]

section VariableNames

variable {a b : α}

@[to_additive]
/-
**le_of_forall_one_lt_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_forall_one_lt_lt_mul (h : forall ε : α, 1 < ε -> a < b * ε) : a <= b
参数：h : forall ε : α, 1 < ε -> a < b * ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_inv_mul_iff_lt`：lt_inv_mul_iff_lt : 1 < b⁻¹ * a ↔ b < a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
-/
theorem le_of_forall_one_lt_lt_mul (h : ∀ ε : α, 1 < ε → a < b * ε) : a ≤ b :=
  le_of_not_gt fun h₁ => lt_irrefl a (by simpa using h _ (lt_inv_mul_iff_lt.mpr h₁))

@[to_additive]
/-
**le_iff_forall_one_lt_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_forall_one_lt_lt_mul : a <= b ↔ forall ε, 1 < ε -> a < b * ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_mul_of_le_of_one_lt`：lt_mul_of_le_of_one_lt [MulLeftStrictMono α] {a 
b c : α} (hbc : b <= c) (ha : 1 < a) : b < c * a
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `le_of_forall_one_lt_lt_mul`：le_of_forall_one_lt_lt_mul (h : forall ε : α
, 1 < ε -> a < b * ε) : a <= b
-/
theorem le_iff_forall_one_lt_lt_mul : a ≤ b ↔ ∀ ε, 1 < ε → a < b * ε :=
  ⟨fun h _ => lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul⟩

/- I (DT) introduced this lemma to prove (the additive version `sub_le_sub_flip` of)
`div_le_div_flip` below.  Now I wonder what is the point of either of these lemmas... -/
@[to_additive]
/-
**div_le_inv_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_inv_mul_iff [MulRightMono α] : a / b <= a⁻¹ * b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_le_inv_mul_iff`：mul_inv_le_inv_mul_iff : a * b⁻¹ <= d⁻¹ * c ↔ d 
* a <= c * b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_lt_mul_of_lt_of_lt`：mul_lt_mul_of_lt_of_lt [MulLeftStrictMono α] [Mu
lRightStrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d

--- 原说明 ---
I (DT) introduced this lemma to prove (the additive version `sub_le_sub_flip` of
)
`div_le_div_flip` below.  Now I wonder what is the point of either of these lemm
as...
-/
theorem div_le_inv_mul_iff [MulRightMono α] :
    a / b ≤ a⁻¹ * b ↔ a ≤ b := by
  rw [div_eq_mul_inv, mul_inv_le_inv_mul_iff]
  exact
    ⟨fun h => not_lt.mp fun k => not_lt.mpr h (mul_lt_mul_of_lt_of_lt k k), fun h =>
      mul_le_mul' h h⟩

-- What is the point of this lemma?  See comment about `div_le_inv_mul_iff` above.
-- Note: we intentionally don't have `@[simp]` for the additive version,
-- since the LHS simplifies with `tsub_le_iff_right`
@[to_additive]
/-
**div_le_div_flip** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_le_div_flip {α : Type*} [CommGroup α] [LinearOrder α] [MulLeftMono α] 
{a b : α} : a / b <= b / a ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_le_inv_mul_iff`：div_le_inv_mul_iff [MulRightMono α] : a / b <= a⁻¹ *
 b ↔ a <= b
-/
theorem div_le_div_flip {α : Type*} [CommGroup α] [LinearOrder α]
    [MulLeftMono α] {a b : α} : a / b ≤ b / a ↔ a ≤ b := by
  rw [div_eq_mul_inv b, mul_comm]
  exact div_le_inv_mul_iff

end VariableNames

end LinearOrder

section

variable {β : Type*} [Group α] [Preorder α] [MulLeftMono α]
  [MulRightMono α] [Preorder β] {f : β → α} {s : Set β}

@[to_additive]
/-
**Monotone.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.inv (hf : Monotone f) : Antitone fun x => (f x)⁻¹
参数：hf : Monotone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_le_inv_iff`：inv_le_inv_iff : a⁻¹ <= b⁻¹ ↔ b <= a
-/
theorem Monotone.inv (hf : Monotone f) : Antitone fun x => (f x)⁻¹ := fun _ _ hxy =>
  inv_le_inv_iff.2 (hf hxy)

@[to_additive]
/-
**Antitone.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.inv (hf : Antitone f) : Monotone fun x => (f x)⁻¹
参数：hf : Antitone f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_le_inv_iff`：inv_le_inv_iff : a⁻¹ <= b⁻¹ ↔ b <= a
-/
theorem Antitone.inv (hf : Antitone f) : Monotone fun x => (f x)⁻¹ := fun _ _ hxy =>
  inv_le_inv_iff.2 (hf hxy)

@[to_additive]
/-
**MonotoneOn.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.inv (hf : MonotoneOn f s) : AntitoneOn (fun x => (f x)⁻¹) s
参数：hf : MonotoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_le_inv_iff`：inv_le_inv_iff : a⁻¹ <= b⁻¹ ↔ b <= a
-/
theorem MonotoneOn.inv (hf : MonotoneOn f s) : AntitoneOn (fun x => (f x)⁻¹) s :=
  fun _ hx _ hy hxy => inv_le_inv_iff.2 (hf hx hy hxy)

@[to_additive]
/-
**AntitoneOn.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.inv (hf : AntitoneOn f s) : MonotoneOn (fun x => (f x)⁻¹) s
参数：hf : AntitoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_le_inv_iff`：inv_le_inv_iff : a⁻¹ <= b⁻¹ ↔ b <= a
-/
theorem AntitoneOn.inv (hf : AntitoneOn f s) : MonotoneOn (fun x => (f x)⁻¹) s :=
  fun _ hx _ hy hxy => inv_le_inv_iff.2 (hf hx hy hxy)

end

section

variable {β : Type*} [Group α] [Preorder α] [MulLeftStrictMono α]
  [MulRightStrictMono α] [Preorder β] {f : β → α} {s : Set β}

@[to_additive]
/-
**StrictMono.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.inv (hf : StrictMono f) : StrictAnti fun x => (f x)⁻¹
参数：hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_lt_inv_iff`：inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a
-/
theorem StrictMono.inv (hf : StrictMono f) : StrictAnti fun x => (f x)⁻¹ := fun _ _ hxy =>
  inv_lt_inv_iff.2 (hf hxy)

@[to_additive]
/-
**StrictAnti.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.inv (hf : StrictAnti f) : StrictMono fun x => (f x)⁻¹
参数：hf : StrictAnti f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_lt_inv_iff`：inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a
-/
theorem StrictAnti.inv (hf : StrictAnti f) : StrictMono fun x => (f x)⁻¹ := fun _ _ hxy =>
  inv_lt_inv_iff.2 (hf hxy)

@[to_additive]
/-
**StrictMonoOn.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMonoOn.inv (hf : StrictMonoOn f s) : StrictAntiOn (fun x => (f x)⁻¹)
 s
参数：hf : StrictMonoOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_lt_inv_iff`：inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a
-/
theorem StrictMonoOn.inv (hf : StrictMonoOn f s) : StrictAntiOn (fun x => (f x)⁻¹) s :=
  fun _ hx _ hy hxy => inv_lt_inv_iff.2 (hf hx hy hxy)

@[to_additive]
/-
**StrictAntiOn.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAntiOn.inv (hf : StrictAntiOn f s) : StrictMonoOn (fun x => (f x)⁻¹)
 s
参数：hf : StrictAntiOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_lt_inv_iff`：inv_lt_inv_iff : a⁻¹ < b⁻¹ ↔ b < a
-/
theorem StrictAntiOn.inv (hf : StrictAntiOn f s) : StrictMonoOn (fun x => (f x)⁻¹) s :=
  fun _ hx _ hy hxy => inv_lt_inv_iff.2 (hf hx hy hxy)

end

