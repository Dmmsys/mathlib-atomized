/-
Copyright (c) 2017 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johannes Hölzl, Chris Hughes, Jens Wagemaker, Jon Eugster
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Logic.Unique
public import Mathlib.Tactic.Lift
public import Mathlib.Tactic.Subsingleton
public import Mathlib.Tactic.Attr.Core

import Mathlib.Tactic.Attr.Register

/-!
# Units (i.e., invertible elements) of a monoid

An element of a `Monoid` is a unit if it has a two-sided inverse.
This file contains the basic lemmas on units in a monoid, especially focusing on singleton types
and unique types.

## TODO

The results here should be used to golf the basic `Group` lemmas.
-/

public section

assert_not_exists Multiplicative MonoidWithZero DenselyOrdered

open Function

universe u

variable {α : Type u}

section HasElem

@[to_additive]
/-
**unique_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：unique_one {α : Type*} [Unique α] [One α] : default = (1 : α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.default_eq`：default_eq (a : α) : default = a
-/
theorem unique_one {α : Type*} [Unique α] [One α] : default = (1 : α) :=
  Unique.default_eq 1

end HasElem

namespace Units
section Monoid
variable [Monoid α]

variable (b c : αˣ) {u : αˣ}

@[to_additive (attr := simp)]
/-
**Units.mul_inv_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_inv_cancel_right (a : α) (b : αˣ) : a * b * ↑b⁻¹ = a
参数：a : α；b : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_inv_cancel_right (a : α) (b : αˣ) : a * b * ↑b⁻¹ = a := by
  rw [mul_assoc, mul_inv, mul_one]

@[to_additive (attr := simp)]
/-
**Units.inv_mul_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：inv_mul_cancel_right (a : α) (b : αˣ) : a * ↑b⁻¹ * b = a
参数：a : α；b : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem inv_mul_cancel_right (a : α) (b : αˣ) : a * ↑b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul, mul_one]

@[to_additive (attr := simp)]
/-
**Units.mul_right_inj** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_right_inj (a : αˣ) {b c : α} : (a : α) * b = a * c ↔ b = c
参数：a : αˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.inv_mul_cancel_left`：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ 
: α) * (a * b) = b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem mul_right_inj (a : αˣ) {b c : α} : (a : α) * b = a * c ↔ b = c :=
  ⟨fun h => by simpa only [inv_mul_cancel_left] using congr_arg (fun x : α => ↑(a⁻¹ : αˣ) * x) h,
    congr_arg _⟩

@[to_additive (attr := simp)]
/-
**Units.mul_left_inj** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b = c
参数：a : αˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.mul_inv_cancel_right`：mul_inv_cancel_right (a : α) (b : αˣ) : a * 
b * ↑b⁻¹ = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b = c :=
  ⟨fun h => by simpa only [mul_inv_cancel_right] using congr_arg (fun x : α => x * ↑(a⁻¹ : αˣ)) h,
    congr_arg (· * a.val)⟩

@[to_additive]
/-
**Units.eq_mul_inv_iff_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：eq_mul_inv_iff_mul_eq {a b : α} : a = b * ↑c⁻¹ ↔ a * c = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.inv_mul_cancel_right`：inv_mul_cancel_right (a : α) (b : αˣ) : a * 
↑b⁻¹ * b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.mul_inv_cancel_right`：mul_inv_cancel_right (a : α) (b : αˣ) : a * 
b * ↑b⁻¹ = a
-/
theorem eq_mul_inv_iff_mul_eq {a b : α} : a = b * ↑c⁻¹ ↔ a * c = b :=
  ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩

@[to_additive]
/-
**Units.eq_inv_mul_iff_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：eq_inv_mul_iff_mul_eq {a c : α} : a = ↑b⁻¹ * c ↔ ↑b * a = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.mul_inv_cancel_left`：mul_inv_cancel_left (a : αˣ) (b : α) : (a : α
) * (↑a⁻¹ * b) = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.inv_mul_cancel_left`：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ 
: α) * (a * b) = b
-/
theorem eq_inv_mul_iff_mul_eq {a c : α} : a = ↑b⁻¹ * c ↔ ↑b * a = c :=
  ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩

@[to_additive]
/-
**Units.mul_inv_eq_iff_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ = c ↔ a = c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.inv_mul_cancel_right`：inv_mul_cancel_right (a : α) (b : αˣ) : a * 
↑b⁻¹ * b = a
· 使用定理 `Units.mul_inv_cancel_right`：mul_inv_cancel_right (a : α) (b : αˣ) : a * 
b * ↑b⁻¹ = a
-/
theorem mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ = c ↔ a = c * b :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩

@[to_additive]
/-
**Units.inv_eq_of_mul_eq_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {α : Type u} [inst : Monoid α] {u : αˣ} {a : α}, a * ↑u = 1 → ↑u⁻¹ = a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.mul_inv_cancel_right`：mul_inv_cancel_right (a : α) (b : αˣ) : a * 
b * ↑b⁻¹ = a
-/
protected theorem inv_eq_of_mul_eq_one_left {a : α} (h : a * u = 1) : ↑u⁻¹ = a :=
  calc
    ↑u⁻¹ = 1 * ↑u⁻¹ := by rw [one_mul]
    _ = a := by rw [← h, mul_inv_cancel_right]

@[to_additive]
/-
**Units.inv_eq_of_mul_eq_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {α : Type u} [inst : Monoid α] {u : αˣ} {a : α}, ↑u * a = 1 → ↑u⁻¹ = a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.inv_mul_cancel_left`：inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ 
: α) * (a * b) = b
-/
protected theorem inv_eq_of_mul_eq_one_right {a : α} (h : ↑u * a = 1) : ↑u⁻¹ = a :=
  calc
    ↑u⁻¹ = ↑u⁻¹ * 1 := by rw [mul_one]
    _ = a := by rw [← h, inv_mul_cancel_left]

@[to_additive]
/-
**Units.eq_inv_of_mul_eq_one_left** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {α : Type u} [inst : Monoid α] {u : αˣ} {a : α}, ↑u * a = 1 → a = ↑u⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.inv_eq_of_mul_eq_one_right`：∀ {α : Type u} [inst : Monoid α] {u : 
αˣ} {a : α}, ↑u * a = 1 → ↑u⁻¹ = a
-/
protected theorem eq_inv_of_mul_eq_one_left {a : α} (h : ↑u * a = 1) : a = ↑u⁻¹ :=
  (Units.inv_eq_of_mul_eq_one_right h).symm

@[to_additive]
/-
**Units.eq_inv_of_mul_eq_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {α : Type u} [inst : Monoid α] {u : αˣ} {a : α}, a * ↑u = 1 → a = ↑u⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.inv_eq_of_mul_eq_one_left`：∀ {α : Type u} [inst : Monoid α] {u : α
ˣ} {a : α}, a * ↑u = 1 → ↑u⁻¹ = a
-/
protected theorem eq_inv_of_mul_eq_one_right {a : α} (h : a * u = 1) : a = ↑u⁻¹ :=
  (Units.inv_eq_of_mul_eq_one_left h).symm

@[to_additive (attr := simp)]
/-
**Units.mul_inv_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_inv_eq_one {a : α} : a * ↑u⁻¹ = 1 ↔ a = u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.eq_inv_of_mul_eq_one_right`：∀ {α : Type u} [inst : Monoid α] {u : 
αˣ} {a : α}, a * ↑u = 1 → a = ↑u⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Units.mul_inv_of_eq`：mul_inv_of_eq {a : α} (h : ↑u = a) : a * ↑u⁻¹ = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mul_inv_eq_one {a : α} : a * ↑u⁻¹ = 1 ↔ a = u :=
  ⟨inv_inv u ▸ Units.eq_inv_of_mul_eq_one_right, fun h => mul_inv_of_eq h.symm⟩

@[to_additive (attr := simp)]
/-
**Units.inv_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：inv_mul_eq_one {a : α} : ↑u⁻¹ * a = 1 ↔ ↑u = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.inv_eq_of_mul_eq_one_right`：∀ {α : Type u} [inst : Monoid α] {u : 
αˣ} {a : α}, ↑u * a = 1 → ↑u⁻¹ = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Units.inv_mul_of_eq`：inv_mul_of_eq {a : α} (h : ↑u = a) : ↑u⁻¹ * a = 1
-/
theorem inv_mul_eq_one {a : α} : ↑u⁻¹ * a = 1 ↔ ↑u = a :=
  ⟨inv_inv u ▸ Units.inv_eq_of_mul_eq_one_right, inv_mul_of_eq⟩

@[to_additive]
/-
**Units.mul_eq_one_iff_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_eq_one_iff_eq_inv {a : α} : a * u = 1 ↔ a = ↑u⁻¹
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.mul_inv_eq_one`：mul_inv_eq_one {a : α} : a * ↑u⁻¹ = 1 ↔ a = u
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_eq_one_iff_eq_inv {a : α} : a * u = 1 ↔ a = ↑u⁻¹ := by rw [← mul_inv_eq_one, inv_inv]

@[to_additive]
/-
**Units.mul_eq_one_iff_inv_eq** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_eq_one_iff_inv_eq {a : α} : ↑u * a = 1 ↔ ↑u⁻¹ = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.inv_mul_eq_one`：inv_mul_eq_one {a : α} : ↑u⁻¹ * a = 1 ↔ ↑u = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_eq_one_iff_inv_eq {a : α} : ↑u * a = 1 ↔ ↑u⁻¹ = a := by rw [← inv_mul_eq_one, inv_inv]

@[to_additive]
/-
**Units.inv_unique** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：inv_unique {u₁ u₂ : αˣ} (h : (↑u₁ : α) = ↑u₂) : (↑u₁⁻¹ : α) = ↑u₂⁻¹
参数：h : (↑u₁ : α) = ↑u₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.inv_eq_of_mul_eq_one_right`：∀ {α : Type u} [inst : Monoid α] {u : 
αˣ} {a : α}, ↑u * a = 1 → ↑u⁻¹ = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
theorem inv_unique {u₁ u₂ : αˣ} (h : (↑u₁ : α) = ↑u₂) : (↑u₁⁻¹ : α) = ↑u₂⁻¹ :=
  Units.inv_eq_of_mul_eq_one_right <| by rw [h, u₂.mul_inv]

@[to_additive (attr := simp)]
/-
**Units.val_inv_inj** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：val_inv_inj {u₁ u₂ : αˣ} : ((u₁⁻¹ : αˣ) : α) = u₂⁻¹ ↔ (u₁ : α) = u₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
-/
theorem val_inv_inj {u₁ u₂ : αˣ} : ((u₁⁻¹ : αˣ) : α) = u₂⁻¹ ↔ (u₁ : α) = u₂ :=
  Units.ext_iff.symm.trans <| inv_inj.trans Units.ext_iff

end Monoid

section CommMonoid

variable [CommMonoid α] (a c : α) (b d : αˣ)

@[to_additive]
/-
**Units.mul_inv_eq_mul_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：mul_inv_eq_mul_inv_iff : a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Units.mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ 
= c ↔ a = c * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Units.eq_inv_mul_iff_mul_eq`：eq_inv_mul_iff_mul_eq {a c : α} : a = ↑b⁻¹ 
* c ↔ ↑b * a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_inv_eq_mul_inv_iff : a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [mul_comm c, Units.mul_inv_eq_iff_eq_mul, mul_assoc, Units.eq_inv_mul_iff_mul_eq, mul_comm]

@[to_additive]
/-
**Units.inv_mul_eq_inv_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：inv_mul_eq_inv_mul_iff : b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Units.mul_inv_eq_mul_inv_iff`：mul_inv_eq_mul_inv_iff : a * b⁻¹ = c * d⁻¹
 ↔ a * d = c * b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_mul_eq_inv_mul_iff : b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b := by
  rw [mul_comm, mul_comm _ c, mul_inv_eq_mul_inv_iff]

end CommMonoid

end Units

section Monoid

variable [Monoid α]

@[simp]
/-
**divp_left_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：divp_left_inj (u : αˣ) {a b : α} : a /ₚ u = b /ₚ u ↔ a = b
参数：u : αˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_left_inj`：mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b 
= c
-/
theorem divp_left_inj (u : αˣ) {a b : α} : a /ₚ u = b /ₚ u ↔ a = b :=
  Units.mul_left_inj _
/-
**divp_eq_iff_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：divp_eq_iff_mul_eq {x : α} {u : αˣ} {y : α} : x /ₚ u = y ↔ y * u = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Units.mul_left_inj`：mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b 
= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `divp_mul_cancel`：divp_mul_cancel (a : α) (u : αˣ) : a /ₚ u * u = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem divp_eq_iff_mul_eq {x : α} {u : αˣ} {y : α} : x /ₚ u = y ↔ y * u = x :=
  u.mul_left_inj.symm.trans <| by rw [divp_mul_cancel]; exact ⟨Eq.symm, Eq.symm⟩
/-
**eq_divp_iff_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_divp_iff_mul_eq {x : α} {u : αˣ} {y : α} : x = y /ₚ u ↔ x * u = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `divp_eq_iff_mul_eq`：divp_eq_iff_mul_eq {x : α} {u : αˣ} {y : α} : x /ₚ u
 = y ↔ y * u = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_divp_iff_mul_eq {x : α} {u : αˣ} {y : α} : x = y /ₚ u ↔ x * u = y := by
  rw [eq_comm, divp_eq_iff_mul_eq]
/-
**divp_eq_one_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：divp_eq_one_iff_eq {a : α} {u : αˣ} : a /ₚ u = 1 ↔ a = u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Units.mul_left_inj`：mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b 
= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `divp_mul_cancel`：divp_mul_cancel (a : α) (u : αˣ) : a /ₚ u * u = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem divp_eq_one_iff_eq {a : α} {u : αˣ} : a /ₚ u = 1 ↔ a = u :=
  (Units.mul_left_inj u).symm.trans <| by rw [divp_mul_cancel, one_mul]
/-
**inv_eq_one_divp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_eq_one_divp' (u : αˣ) : ((1 / u : αˣ) : α) = 1 /ₚ u
参数：u : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `one_divp`：one_divp (u : αˣ) : 1 /ₚ u = ↑u⁻¹
-/
theorem inv_eq_one_divp' (u : αˣ) : ((1 / u : αˣ) : α) = 1 /ₚ u := by
  rw [one_div, one_divp]

end Monoid

namespace LeftCancelMonoid

variable [LeftCancelMonoid α] [Subsingleton αˣ] {a b : α}

@[to_additive]
/-
**LeftCancelMonoid.eq_one_of_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `LeftCancelMono
id`。
形式化陈述：∀ {α : Type u} [inst : LeftCancelMonoid α] [Subsingleton αˣ] {a b : α}, a 
* b = 1 → a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_left_cancel_iff`：mul_left_cancel_iff : a * b = a * c ↔ b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
protected theorem eq_one_of_mul_right (h : a * b = 1) : a = 1 :=
  congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ (by
    rw [← mul_left_cancel_iff (a := a), ← mul_assoc, h, one_mul, mul_one]) h) 1

@[to_additive]
/-
**LeftCancelMonoid.eq_one_of_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `LeftCancelMonoi
d`。
形式化陈述：∀ {α : Type u} [inst : LeftCancelMonoid α] [Subsingleton αˣ] {a b : α}, a 
* b = 1 → b = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LeftCancelMonoid.eq_one_of_mul_right`：∀ {α : Type u} [inst : LeftCancelM
onoid α] [Subsingleton αˣ] {a b : α}, a * b = 1 → a = 1
-/
protected theorem eq_one_of_mul_left (h : a * b = 1) : b = 1 := by
  rwa [LeftCancelMonoid.eq_one_of_mul_right h, one_mul] at h

@[to_additive (attr := simp)]
/-
**LeftCancelMonoid.mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `LeftCancelMonoid`。
形式化陈述：∀ {α : Type u} [inst : LeftCancelMonoid α] [Subsingleton αˣ] {a b : α}, a 
* b = 1 ↔ a = 1 ∧ b = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LeftCancelMonoid.eq_one_of_mul_right`：∀ {α : Type u} [inst : LeftCancelM
onoid α] [Subsingleton αˣ] {a b : α}, a * b = 1 → a = 1
· 使用定理 `LeftCancelMonoid.eq_one_of_mul_left`：∀ {α : Type u} [inst : LeftCancelMo
noid α] [Subsingleton αˣ] {a b : α}, a * b = 1 → b = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  ⟨fun h => ⟨LeftCancelMonoid.eq_one_of_mul_right h, LeftCancelMonoid.eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

@[to_additive]
/-
**LeftCancelMonoid.mul_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `LeftCancelMonoid`。
形式化陈述：∀ {α : Type u} [inst : LeftCancelMonoid α] [Subsingleton αˣ] {a b : α}, a 
* b ≠ 1 ↔ a ≠ 1 ∨ b ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem mul_ne_one : a * b ≠ 1 ↔ a ≠ 1 ∨ b ≠ 1 := by rw [not_iff_comm]; simp

end LeftCancelMonoid

namespace RightCancelMonoid

variable [RightCancelMonoid α] [Subsingleton αˣ] {a b : α}

@[to_additive]
/-
**RightCancelMonoid.eq_one_of_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `RightCancelMo
noid`。
形式化陈述：∀ {α : Type u} [inst : RightCancelMonoid α] [Subsingleton αˣ] {a b : α}, a
 * b = 1 → a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_cancel_iff`：mul_right_cancel_iff : b * a = c * a ↔ b = c
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
protected theorem eq_one_of_mul_right (h : a * b = 1) : a = 1 :=
  congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ (by
    rw [← mul_right_cancel_iff (a := b), mul_assoc, h, one_mul, mul_one]) h) 1

@[to_additive]
/-
**RightCancelMonoid.eq_one_of_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `RightCancelMon
oid`。
形式化陈述：∀ {α : Type u} [inst : RightCancelMonoid α] [Subsingleton αˣ] {a b : α}, a
 * b = 1 → b = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `RightCancelMonoid.eq_one_of_mul_right`：∀ {α : Type u} [inst : RightCance
lMonoid α] [Subsingleton αˣ] {a b : α}, a * b = 1 → a = 1
-/
protected theorem eq_one_of_mul_left (h : a * b = 1) : b = 1 := by
  rwa [RightCancelMonoid.eq_one_of_mul_right h, one_mul] at h

@[to_additive (attr := simp)]
/-
**RightCancelMonoid.mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `RightCancelMonoid`。
形式化陈述：∀ {α : Type u} [inst : RightCancelMonoid α] [Subsingleton αˣ] {a b : α}, a
 * b = 1 ↔ a = 1 ∧ b = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RightCancelMonoid.eq_one_of_mul_right`：∀ {α : Type u} [inst : RightCance
lMonoid α] [Subsingleton αˣ] {a b : α}, a * b = 1 → a = 1
· 使用定理 `RightCancelMonoid.eq_one_of_mul_left`：∀ {α : Type u} [inst : RightCancel
Monoid α] [Subsingleton αˣ] {a b : α}, a * b = 1 → b = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  ⟨fun h => ⟨RightCancelMonoid.eq_one_of_mul_right h, RightCancelMonoid.eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

@[to_additive]
/-
**RightCancelMonoid.mul_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `RightCancelMonoid`。
形式化陈述：∀ {α : Type u} [inst : RightCancelMonoid α] [Subsingleton αˣ] {a b : α}, a
 * b ≠ 1 ↔ a ≠ 1 ∨ b ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem mul_ne_one : a * b ≠ 1 ↔ a ≠ 1 ∨ b ≠ 1 := by rw [not_iff_comm]; simp

end RightCancelMonoid

section CancelMonoid

variable [CancelMonoid α] [Subsingleton αˣ] {a b : α}

@[to_additive]
/-
**eq_one_of_mul_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_one_of_mul_right' (h : a * b = 1) : a = 1
参数：h : a * b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LeftCancelMonoid.eq_one_of_mul_right`：∀ {α : Type u} [inst : LeftCancelM
onoid α] [Subsingleton αˣ] {a b : α}, a * b = 1 → a = 1
-/
theorem eq_one_of_mul_right' (h : a * b = 1) : a = 1 := LeftCancelMonoid.eq_one_of_mul_right h

@[to_additive]
/-
**eq_one_of_mul_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_one_of_mul_left' (h : a * b = 1) : b = 1
参数：h : a * b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LeftCancelMonoid.eq_one_of_mul_left`：∀ {α : Type u} [inst : LeftCancelMo
noid α] [Subsingleton αˣ] {a b : α}, a * b = 1 → b = 1
-/
theorem eq_one_of_mul_left' (h : a * b = 1) : b = 1 := LeftCancelMonoid.eq_one_of_mul_left h

@[to_additive]
/-
**mul_eq_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_one' : a * b = 1 ↔ a = 1 ∧ b = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LeftCancelMonoid.mul_eq_one`：∀ {α : Type u} [inst : LeftCancelMonoid α] 
[Subsingleton αˣ] {a b : α}, a * b = 1 ↔ a = 1 ∧ b = 1
-/
theorem mul_eq_one' : a * b = 1 ↔ a = 1 ∧ b = 1 := LeftCancelMonoid.mul_eq_one

@[to_additive]
/-
**mul_ne_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_ne_one' : a * b != 1 ↔ a != 1 ∨ b != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LeftCancelMonoid.mul_ne_one`：∀ {α : Type u} [inst : LeftCancelMonoid α] 
[Subsingleton αˣ] {a b : α}, a * b ≠ 1 ↔ a ≠ 1 ∨ b ≠ 1
-/
theorem mul_ne_one' : a * b ≠ 1 ↔ a ≠ 1 ∨ b ≠ 1 := LeftCancelMonoid.mul_ne_one

end CancelMonoid

section CommMonoid

variable [CommMonoid α]

/-
**divp_mul_eq_mul_divp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：divp_mul_eq_mul_divp (x y : α) (u : αˣ) : x /ₚ u * y = x * y /ₚ u
参数：x y : α；u : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `divp.eq_1`：∀ {α : Type u} [inst : Monoid α] (a : α) (u : αˣ), a /ₚ u = a
 * ↑u⁻¹
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
-/
theorem divp_mul_eq_mul_divp (x y : α) (u : αˣ) : x /ₚ u * y = x * y /ₚ u := by
  rw [divp, divp, mul_right_comm]
/-
**divp_eq_divp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：divp_eq_divp_iff {x y : α} {ux uy : αˣ} : x /ₚ ux = y /ₚ uy ↔ x * uy = y *
 ux
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `divp_eq_iff_mul_eq`：divp_eq_iff_mul_eq {x : α} {u : αˣ} {y : α} : x /ₚ u
 = y ↔ y * u = x
· 使用定理 `divp_mul_eq_mul_divp`：divp_mul_eq_mul_divp (x y : α) (u : αˣ) : x /ₚ u *
 y = x * y /ₚ u
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem divp_eq_divp_iff {x y : α} {ux uy : αˣ} : x /ₚ ux = y /ₚ uy ↔ x * uy = y * ux := by
  rw [divp_eq_iff_mul_eq, divp_mul_eq_mul_divp, divp_eq_iff_mul_eq]
/-
**divp_mul_divp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：divp_mul_divp (x y : α) (ux uy : αˣ) : x /ₚ ux * (y /ₚ uy) = x * y /ₚ (ux 
* uy)
参数：x y : α；ux uy : αˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `divp_mul_eq_mul_divp`：divp_mul_eq_mul_divp (x y : α) (u : αˣ) : x /ₚ u *
 y = x * y /ₚ u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `divp_assoc`：divp_assoc (a b : α) (u : αˣ) : a * b /ₚ u = a * (b /ₚ u)
· 使用定理 `divp_divp_eq_divp_mul`：divp_divp_eq_divp_mul (x : α) (u₁ u₂ : αˣ) : x /ₚ
 u₁ /ₚ u₂ = x /ₚ (u₂ * u₁)
-/
theorem divp_mul_divp (x y : α) (ux uy : αˣ) : x /ₚ ux * (y /ₚ uy) = x * y /ₚ (ux * uy) := by
  rw [divp_mul_eq_mul_divp, ← divp_assoc, divp_divp_eq_divp_mul]

variable [Subsingleton αˣ] {a b : α}

@[to_additive]
/-
**eq_one_of_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_one_of_mul_right (h : a * b = 1) : a = 1
参数：h : a * b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem eq_one_of_mul_right (h : a * b = 1) : a = 1 :=
  congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ (by rwa [mul_comm]) h) 1

@[to_additive]
/-
**eq_one_of_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_one_of_mul_left (h : a * b = 1) : b = 1
参数：h : a * b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem eq_one_of_mul_left (h : a * b = 1) : b = 1 :=
  congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ h <| by rwa [mul_comm]) 1

@[to_additive (attr := simp)]
/-
**mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_one_of_mul_right`：eq_one_of_mul_right (h : a * b = 1) : a = 1
· 使用定理 `eq_one_of_mul_left`：eq_one_of_mul_left (h : a * b = 1) : b = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  ⟨fun h => ⟨eq_one_of_mul_right h, eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩
/-
**mul_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : CommMonoid α] [Subsingleton αˣ] {a b : α}, a * b ≠ 
1 ↔ a ≠ 1 ∨ b ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive] theorem mul_ne_one : a * b ≠ 1 ↔ a ≠ 1 ∨ b ≠ 1 := by rw [not_iff_comm]; simp

end CommMonoid

/-!
### `IsUnit` predicate
-/


section IsUnit

variable {M : Type*}

@[to_additive (attr := nontriviality)]
/-
**isUnit_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_of_subsingleton [Monoid M] [Subsingleton M] (a : M) : IsUnit a
参数：a : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem isUnit_of_subsingleton [Monoid M] [Subsingleton M] (a : M) : IsUnit a :=
  ⟨⟨a, a, by subsingleton, by subsingleton⟩, rfl⟩

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid M] : CanLift M Mˣ Units.val IsUnit :=
  { prf := fun _ ↦ id }

/-- A subsingleton `Monoid` has a unique unit. -/
@[to_additive /-- A subsingleton `AddMonoid` has a unique additive unit. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subsingleton `Monoid` has a unique unit.
-/
instance [Monoid M] [Subsingleton M] : Unique Mˣ where
  uniq _ := Units.val_eq_one.mp (by subsingleton)

namespace IsUnit

section Monoid

variable [Monoid M] {a b c : M}

@[to_additive]
/-
**IsUnit.mul_left_inj** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
参数：h : IsUnit a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_left_inj`：mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b 
= c
-/
theorem mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_left_inj

@[to_additive]
/-
**IsUnit.mul_right_inj** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b = c
参数：h : IsUnit a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_right_inj`：mul_right_inj (a : αˣ) {b c : α} : (a : α) * b = a 
* c ↔ b = c
-/
theorem mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_right_inj

@[to_additive]
/-
**IsUnit.mul_left_cancel** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {a b c : M}, IsUnit a → a * b = a * c →
 b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUnit.mul_right_inj`：mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b =
 c
-/
protected theorem mul_left_cancel (h : IsUnit a) : a * b = a * c → b = c :=
  h.mul_right_inj.1

@[to_additive]
/-
**IsUnit.mul_right_cancel** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {a b c : M}, IsUnit b → a * b = c * b →
 a = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
-/
protected theorem mul_right_cancel (h : IsUnit b) : a * b = c * b → a = c :=
  h.mul_left_inj.1

@[to_additive]
/-
**IsUnit.mul_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：mul_eq_right (h : IsUnit b) : a * b = b ↔ a = 1
参数：h : IsUnit b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
-/
theorem mul_eq_right (h : IsUnit b) : a * b = b ↔ a = 1 := calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 := by rw [h.mul_left_inj]

@[to_additive]
/-
**IsUnit.mul_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：mul_eq_left (h : IsUnit a) : a * b = a ↔ b = 1
参数：h : IsUnit a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsUnit.mul_right_inj`：mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b =
 c
-/
theorem mul_eq_left (h : IsUnit a) : a * b = a ↔ b = 1 := calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 := by rw [h.mul_right_inj]

@[to_additive]
/-
**IsUnit.mul_right_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {a : M}, IsUnit a → Function.Injective 
fun x => a * x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.mul_left_cancel`：∀ {M : Type u_1} [inst : Monoid M] {a b c : M}, 
IsUnit a → a * b = a * c → b = c
-/
protected theorem mul_right_injective (h : IsUnit a) : Injective (a * ·) :=
  fun _ _ => h.mul_left_cancel

@[to_additive]
/-
**IsUnit.mul_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {b : M}, IsUnit b → Function.Injective 
fun x => x * b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.mul_right_cancel`：∀ {M : Type u_1} [inst : Monoid M] {a b c : M},
 IsUnit b → a * b = c * b → a = c
-/
protected theorem mul_left_injective (h : IsUnit b) : Injective (· * b) :=
  fun _ _ => h.mul_right_cancel

@[to_additive]
/-
**IsUnit.isUnit_iff_mulLeft_bijective** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：isUnit_iff_mulLeft_bijective {a : M} : IsUnit a ↔ Function.Bijective (a * 
·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.mul_right_injective`：∀ {M : Type u_1} [inst : Monoid M] {a : M}, 
IsUnit a → Function.Injective fun x => a * x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem isUnit_iff_mulLeft_bijective {a : M} :
    IsUnit a ↔ Function.Bijective (a * ·) :=
  ⟨fun h ↦ ⟨h.mul_right_injective, fun y ↦ ⟨h.unit⁻¹ * y, by simp [← mul_assoc]⟩⟩, fun h ↦
    ⟨⟨a, _, (h.2 1).choose_spec, h.1
      (by simpa [mul_assoc] using congr_arg (· * a) (h.2 1).choose_spec)⟩, rfl⟩⟩

@[to_additive]
/-
**IsUnit.isUnit_iff_mulRight_bijective** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：isUnit_iff_mulRight_bijective {a : M} : IsUnit a ↔ Function.Bijective (· *
 a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.mul_left_injective`：∀ {M : Type u_1} [inst : Monoid M] {b : M}, I
sUnit b → Function.Injective fun x => x * b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem isUnit_iff_mulRight_bijective {a : M} :
    IsUnit a ↔ Function.Bijective (· * a) :=
  ⟨fun h ↦ ⟨h.mul_left_injective, fun y ↦ ⟨y * h.unit⁻¹, by simp [mul_assoc]⟩⟩,
    fun h ↦ ⟨⟨a, _, h.1 (by simpa [mul_assoc] using congr_arg (a * ·) (h.2 1).choose_spec),
      (h.2 1).choose_spec⟩, rfl⟩⟩

end Monoid

section DivisionMonoid
variable [DivisionMonoid α] {a b c : α}

@[to_additive (attr := simp)]
/-
**IsUnit.mul_inv_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {b : α}, IsUnit b → ∀ (a : α), a 
* b * b⁻¹ = a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_inv_cancel_right`：mul_inv_cancel_right (a : α) (b : αˣ) : a * 
b * ↑b⁻¹ = a
-/
protected lemma mul_inv_cancel_right (h : IsUnit b) (a : α) : a * b * b⁻¹ = a :=
  h.unit'.mul_inv_cancel_right _

@[to_additive (attr := simp)]
/-
**IsUnit.inv_mul_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {b : α}, IsUnit b → ∀ (a : α), a 
* b⁻¹ * b = a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.inv_mul_cancel_right`：inv_mul_cancel_right (a : α) (b : αˣ) : a * 
↑b⁻¹ * b = a
-/
protected lemma inv_mul_cancel_right (h : IsUnit b) (a : α) : a * b⁻¹ * b = a :=
  h.unit'.inv_mul_cancel_right _

@[to_additive]
/-
**IsUnit.eq_mul_inv_iff_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a b c : α}, IsUnit c → (a = b * 
c⁻¹ ↔ a * c = b)
参数：a = b * c⁻¹ ↔ a * c = b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.eq_mul_inv_iff_mul_eq`：eq_mul_inv_iff_mul_eq {a b : α} : a = b * ↑
c⁻¹ ↔ a * c = b
-/
protected lemma eq_mul_inv_iff_mul_eq (h : IsUnit c) : a = b * c⁻¹ ↔ a * c = b :=
  h.unit'.eq_mul_inv_iff_mul_eq

@[to_additive]
/-
**IsUnit.eq_inv_mul_iff_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a b c : α}, IsUnit b → (a = b⁻¹ 
* c ↔ b * a = c)
参数：a = b⁻¹ * c ↔ b * a = c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.eq_inv_mul_iff_mul_eq`：eq_inv_mul_iff_mul_eq {a c : α} : a = ↑b⁻¹ 
* c ↔ ↑b * a = c
-/
protected lemma eq_inv_mul_iff_mul_eq (h : IsUnit b) : a = b⁻¹ * c ↔ b * a = c :=
  h.unit'.eq_inv_mul_iff_mul_eq

@[to_additive]
/-
**IsUnit.inv_mul_eq_iff_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a b c : α}, IsUnit a → (a⁻¹ * b 
= c ↔ b = a * c)
参数：a⁻¹ * b = c ↔ b = a * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.inv_mul_eq_iff_eq_mul`：inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b 
= c ↔ b = a * c
-/
protected lemma inv_mul_eq_iff_eq_mul (h : IsUnit a) : a⁻¹ * b = c ↔ b = a * c :=
  h.unit'.inv_mul_eq_iff_eq_mul

@[to_additive]
/-
**IsUnit.mul_inv_eq_iff_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a b c : α}, IsUnit b → (a * b⁻¹ 
= c ↔ a = c * b)
参数：a * b⁻¹ = c ↔ a = c * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ 
= c ↔ a = c * b
-/
protected lemma mul_inv_eq_iff_eq_mul (h : IsUnit b) : a * b⁻¹ = c ↔ a = c * b :=
  h.unit'.mul_inv_eq_iff_eq_mul

@[to_additive]
/-
**IsUnit.mul_inv_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a b : α}, IsUnit b → (a * b⁻¹ = 
1 ↔ a = b)
参数：a * b⁻¹ = 1 ↔ a = b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_inv_eq_one`：mul_inv_eq_one {a : α} : a * ↑u⁻¹ = 1 ↔ a = u
-/
protected lemma mul_inv_eq_one (h : IsUnit b) : a * b⁻¹ = 1 ↔ a = b :=
  @Units.mul_inv_eq_one _ _ h.unit' _

@[to_additive]
/-
**IsUnit.inv_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a b : α}, IsUnit a → (a⁻¹ * b = 
1 ↔ a = b)
参数：a⁻¹ * b = 1 ↔ a = b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.inv_mul_eq_one`：inv_mul_eq_one {a : α} : ↑u⁻¹ * a = 1 ↔ ↑u = a
-/
protected lemma inv_mul_eq_one (h : IsUnit a) : a⁻¹ * b = 1 ↔ a = b :=
  @Units.inv_mul_eq_one _ _ h.unit' _

@[to_additive]
/-
**IsUnit.mul_eq_one_iff_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a b : α}, IsUnit b → (a * b = 1 
↔ a = b⁻¹)
参数：a * b = 1 ↔ a = b⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_eq_one_iff_eq_inv`：mul_eq_one_iff_eq_inv {a : α} : a * u = 1 ↔
 a = ↑u⁻¹
-/
protected lemma mul_eq_one_iff_eq_inv (h : IsUnit b) : a * b = 1 ↔ a = b⁻¹ :=
  @Units.mul_eq_one_iff_eq_inv _ _ h.unit' _

@[to_additive]
/-
**IsUnit.mul_eq_one_iff_inv_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a b : α}, IsUnit a → (a * b = 1 
↔ a⁻¹ = b)
参数：a * b = 1 ↔ a⁻¹ = b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.mul_eq_one_iff_inv_eq`：mul_eq_one_iff_inv_eq {a : α} : ↑u * a = 1 
↔ ↑u⁻¹ = a
-/
protected lemma mul_eq_one_iff_inv_eq (h : IsUnit a) : a * b = 1 ↔ a⁻¹ = b :=
  @Units.mul_eq_one_iff_inv_eq _ _ h.unit' _

@[to_additive (attr := simp)]
/-
**IsUnit.div_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {b : α}, IsUnit b → ∀ (a : α), a 
/ b * b = a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IsUnit.inv_mul_cancel_right`：∀ {α : Type u} [inst : DivisionMonoid α] {b
 : α}, IsUnit b → ∀ (a : α), a * b⁻¹ * b = a
-/
protected lemma div_mul_cancel (h : IsUnit b) (a : α) : a / b * b = a := by
  rw [div_eq_mul_inv, h.inv_mul_cancel_right]

@[to_additive (attr := simp)]
/-
**IsUnit.mul_div_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {b : α}, IsUnit b → ∀ (a : α), a 
* b / b = a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IsUnit.mul_inv_cancel_right`：∀ {α : Type u} [inst : DivisionMonoid α] {b
 : α}, IsUnit b → ∀ (a : α), a * b * b⁻¹ = a
-/
protected lemma mul_div_cancel_right (h : IsUnit b) (a : α) : a * b / b = a := by
  rw [div_eq_mul_inv, h.mul_inv_cancel_right]

@[to_additive]
/-
**IsUnit.mul_one_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a : α}, IsUnit a → a * (1 / a) =
 1
参数：1 / a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `IsUnit.mul_inv_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {a : α},
 IsUnit a → a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma mul_one_div_cancel (h : IsUnit a) : a * (1 / a) = 1 := by simp [h]

@[to_additive]
/-
**IsUnit.one_div_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a : α}, IsUnit a → 1 / a * a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `IsUnit.inv_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {a : α},
 IsUnit a → a⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma one_div_mul_cancel (h : IsUnit a) : 1 / a * a = 1 := by simp [h]

@[to_additive]
/-
**IsUnit.div_left_inj** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a b c : α}, IsUnit c → (a / c = 
b / c ↔ a = b)
参数：a / c = b / c ↔ a = b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Units.mul_left_inj`：mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b 
= c
· 使用引理 `IsUnit.inv`：inv (h : IsUnit a) : IsUnit a⁻¹
-/
protected lemma div_left_inj (h : IsUnit c) : a / c = b / c ↔ a = b := by
  simp only [div_eq_mul_inv]
  exact Units.mul_left_inj h.inv.unit'

@[to_additive]
/-
**IsUnit.div_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a b c : α}, IsUnit b → (a / b = 
c ↔ a = c * b)
参数：a / b = c ↔ a = c * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IsUnit.mul_inv_eq_iff_eq_mul`：∀ {α : Type u} [inst : DivisionMonoid α] {
a b c : α}, IsUnit b → (a * b⁻¹ = c ↔ a = c * b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma div_eq_iff (h : IsUnit b) : a / b = c ↔ a = c * b := by
  rw [div_eq_mul_inv, h.mul_inv_eq_iff_eq_mul]

@[to_additive]
/-
**IsUnit.eq_div_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a b c : α}, IsUnit c → (a = b / 
c ↔ a * c = b)
参数：a = b / c ↔ a * c = b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IsUnit.eq_mul_inv_iff_mul_eq`：∀ {α : Type u} [inst : DivisionMonoid α] {
a b c : α}, IsUnit c → (a = b * c⁻¹ ↔ a * c = b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma eq_div_iff (h : IsUnit c) : a = b / c ↔ a * c = b := by
  rw [div_eq_mul_inv, h.eq_mul_inv_iff_mul_eq]

@[to_additive]
/-
**IsUnit.div_eq_of_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a b c : α}, IsUnit b → a = c * b
 → a / b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsUnit.div_eq_iff`：∀ {α : Type u} [inst : DivisionMonoid α] {a b c : α},
 IsUnit b → (a / b = c ↔ a = c * b)
-/
protected lemma div_eq_of_eq_mul (h : IsUnit b) : a = c * b → a / b = c :=
  h.div_eq_iff.2

@[to_additive]
/-
**IsUnit.eq_div_of_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a b c : α}, IsUnit c → a * c = b
 → a = b / c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsUnit.eq_div_iff`：∀ {α : Type u} [inst : DivisionMonoid α] {a b c : α},
 IsUnit c → (a = b / c ↔ a * c = b)
-/
protected lemma eq_div_of_mul_eq (h : IsUnit c) : a * c = b → a = b / c :=
  h.eq_div_iff.2

@[to_additive]
/-
**IsUnit.div_eq_one_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a b : α}, IsUnit b → (a / b = 1 
↔ a = b)
参数：a / b = 1 ↔ a = b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_div_eq_one`：eq_of_div_eq_one (h : a / b = 1) : a = b
· 使用定理 `IsUnit.div_self`：∀ {α : Type u} [inst : DivisionMonoid α] {a : α}, IsUni
t a → a / a = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected lemma div_eq_one_iff_eq (h : IsUnit b) : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun hab => hab.symm ▸ h.div_self⟩

@[to_additive]
/-
**IsUnit.div_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {a b : α}, IsUnit b → b / (a * b)
 = 1 / a
参数：a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.div_mul_cancel_right`：∀ {α : Type u} [inst : DivisionMonoid α] {b
 : α}, IsUnit b → ∀ (a : α), b / (a * b) = a⁻¹
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
protected lemma div_mul_left (h : IsUnit b) : b / (a * b) = 1 / a := by
  rw [h.div_mul_cancel_right, one_div]

@[to_additive]
/-
**IsUnit.mul_mul_div** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionMonoid α] {b : α} (a : α), IsUnit b → a * b
 * (1 / b) = a
参数：a : α；1 / b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `IsUnit.mul_inv_cancel_right`：∀ {α : Type u} [inst : DivisionMonoid α] {b
 : α}, IsUnit b → ∀ (a : α), a * b * b⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma mul_mul_div (a : α) (h : IsUnit b) : a * b * (1 / b) = a := by simp [h]

end DivisionMonoid

section DivisionCommMonoid
variable [DivisionCommMonoid α] {a b c d : α}

@[to_additive]
/-
**IsUnit.div_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionCommMonoid α] {a : α}, IsUnit a → ∀ (b : α)
, a / (a * b) = 1 / b
参数：b : α；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsUnit.div_mul_left`：∀ {α : Type u} [inst : DivisionMonoid α] {a b : α},
 IsUnit b → b / (a * b) = 1 / a
-/
protected lemma div_mul_right (h : IsUnit a) (b : α) : a / (a * b) = 1 / b := by
  rw [mul_comm, h.div_mul_left]

@[to_additive]
/-
**IsUnit.mul_div_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionCommMonoid α] {a : α}, IsUnit a → ∀ (b : α)
, a * b / a = b
参数：b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsUnit.mul_div_cancel_right`：∀ {α : Type u} [inst : DivisionMonoid α] {b
 : α}, IsUnit b → ∀ (a : α), a * b / b = a
-/
protected lemma mul_div_cancel_left (h : IsUnit a) (b : α) : a * b / a = b := by
  rw [mul_comm, h.mul_div_cancel_right]

@[to_additive]
/-
**IsUnit.mul_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionCommMonoid α] {a : α}, IsUnit a → ∀ (b : α)
, a * (b / a) = b
参数：b : α；b / a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
-/
protected lemma mul_div_cancel (h : IsUnit a) (b : α) : a * (b / a) = b := by
  rw [mul_comm, h.div_mul_cancel]

@[to_additive]
/-
**IsUnit.mul_eq_mul_of_div_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionCommMonoid α] {b d : α}, IsUnit b → IsUnit 
d → ∀ (a c : α), a / b = c / d → a * d = c * b
参数：a c : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsUnit.div_self`：∀ {α : Type u} [inst : DivisionMonoid α] {a : α}, IsUni
t a → a / a = 1
· 使用定理 `mul_comm_div`：mul_comm_div : a / b * c = a * (c / b)
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
-/
protected lemma mul_eq_mul_of_div_eq_div (hb : IsUnit b) (hd : IsUnit d)
    (a c : α) (h : a / b = c / d) : a * d = c * b := by
  rw [← mul_one a, ← hb.div_self, ← mul_comm_div, h, div_mul_eq_mul_div, hd.div_mul_cancel]

@[to_additive]
/-
**IsUnit.div_eq_div_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionCommMonoid α] {a b c d : α}, IsUnit b → IsU
nit d → (a / b = c / d ↔ a * d = c * b)
参数：a / b = c / d ↔ a * d = c * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma div_eq_div_iff (hb : IsUnit b) (hd : IsUnit d) :
    a / b = c / d ↔ a * d = c * b := by
  rw [← (hb.mul hd).mul_left_inj, ← mul_assoc, hb.div_mul_cancel, ← mul_assoc, mul_right_comm,
    hd.div_mul_cancel]

@[to_additive]
/-
**IsUnit.mul_inv_eq_mul_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionCommMonoid α] {a b c d : α}, IsUnit b → IsU
nit d → (a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b)
参数：a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `IsUnit.div_eq_div_iff`：∀ {α : Type u} [inst : DivisionCommMonoid α] {a b
 c d : α}, IsUnit b → IsUnit d → (a / b = c / d ↔ a * d = c * b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma mul_inv_eq_mul_inv_iff (hb : IsUnit b) (hd : IsUnit d) :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, hb.div_eq_div_iff hd]

@[to_additive]
/-
**IsUnit.inv_mul_eq_inv_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionCommMonoid α] {a b c d : α}, IsUnit b → IsU
nit d → (b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b)
参数：b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `IsUnit.div_eq_div_iff`：∀ {α : Type u} [inst : DivisionCommMonoid α] {a b
 c d : α}, IsUnit b → IsUnit d → (a / b = c / d ↔ a * d = c * b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma inv_mul_eq_inv_mul_iff (hb : IsUnit b) (hd : IsUnit d) :
    b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b := by
  rw [← div_eq_inv_mul, ← div_eq_inv_mul, hb.div_eq_div_iff hd]

@[to_additive]
/-
**IsUnit.div_div_cancel** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionCommMonoid α] {a b : α}, IsUnit a → a / (a 
/ b) = b
参数：a / b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_div_eq_mul_div`：div_div_eq_mul_div : a / (b / c) = a * c / b
· 使用定理 `IsUnit.mul_div_cancel_left`：∀ {α : Type u} [inst : DivisionCommMonoid α]
 {a : α}, IsUnit a → ∀ (b : α), a * b / a = b
-/
protected lemma div_div_cancel (h : IsUnit a) : a / (a / b) = b := by
  rw [div_div_eq_mul_div, h.mul_div_cancel_left]

@[to_additive]
/-
**IsUnit.div_div_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：∀ {α : Type u} [inst : DivisionCommMonoid α] {a b : α}, IsUnit a → a / b /
 a = b⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `IsUnit.mul_inv_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {a : α},
 IsUnit a → a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
protected lemma div_div_cancel_left (h : IsUnit a) : a / b / a = b⁻¹ := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm, h.mul_inv_cancel, one_mul]

end DivisionCommMonoid
end IsUnit

-- namespace
end IsUnit

