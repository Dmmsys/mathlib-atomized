/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson, Re'em Melamed-Katz
-/
module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Tactic.Common
public import Batteries.Tactic.SeqFocus

/-!
# Divisibility

This file defines the basics of the divisibility relation in the context of `(Comm)` `Monoid`s.

## Main definitions

* `semigroupDvd`

## Implementation notes

The divisibility relation is defined for all monoids, and as such, depends on the order of
  multiplication if the monoid is not commutative. There are two possible conventions for
  divisibility in the noncommutative context, and this relation follows the convention for ordinals,
  so `a | b` is defined as `∃ c, b = a * c`.

## Tags

divisibility, divides
-/

@[expose] public section


variable {α : Type*}

section Semigroup

variable [Semigroup α] {a b c : α}

/-- There are two possible conventions for divisibility, which coincide in a `CommMonoid`.
This matches the convention for ordinals. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There are two possible conventions for divisibility, which coincide in a `CommMo
noid`.
This matches the convention for ordinals.
-/
instance (priority := 100) semigroupDvd : Dvd α :=
  Dvd.mk fun a b => ∃ c, b = a * c

-- TODO: this used to not have `c` explicit, but that seems to be important
--       for use with tactics, similar to `Exists.intro`
/-
**Dvd.intro** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
参数：c : α；h : a * c = b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Dvd.intro (c : α) (h : a * c = b) : a ∣ b :=
  Exists.intro c h.symm

alias dvd_of_mul_right_eq := Dvd.intro
/-
**exists_eq_mul_right_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_eq_mul_right_of_dvd (h : a ∣ b) : exists c, b = a * c
参数：h : a ∣ b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_eq_mul_right_of_dvd (h : a ∣ b) : ∃ c, b = a * c :=
  h
/-
**dvd_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_def : a ∣ b ↔ exists c, b = a * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dvd_def : a ∣ b ↔ ∃ c, b = a * c :=
  Iff.rfl

alias dvd_iff_exists_eq_mul_right := dvd_def
/-
**Dvd.elim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : forall c, b = a * c -> P)
 : P
参数：H₁ : a ∣ b；H₂ : forall c, b = a * c -> P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
-/
theorem Dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : ∀ c, b = a * c → P) : P :=
  Exists.elim H₁ H₂

attribute [local simp] mul_assoc mul_comm mul_left_comm

@[trans]
/-
**dvd_trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d * e, h₁ ▸ h₂.
trans mul_assoc a d e⟩  alias Dvd.dvd.trans
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem dvd_trans : a ∣ b → b ∣ c → a ∣ c
  | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d * e, h₁ ▸ h₂.trans <| mul_assoc a d e⟩

alias Dvd.dvd.trans := dvd_trans

/-- Transitivity of `|` for use in `calc` blocks. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transitivity of `|` for use in `calc` blocks.
-/
instance : IsTrans α Dvd.dvd :=
  ⟨fun _ _ _ => dvd_trans⟩

@[simp]
/-
**dvd_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_mul_right (a b : α) : a ∣ a * b
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
-/
theorem dvd_mul_right (a b : α) : a ∣ a * b :=
  Dvd.intro b rfl
/-
**dvd_mul_of_dvd_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
参数：h : a ∣ b；c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c :=
  h.trans (dvd_mul_right b c)

alias Dvd.dvd.mul_right := dvd_mul_of_dvd_left
/-
**dvd_of_mul_right_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_of_mul_right_dvd (h : a * b ∣ c) : a ∣ c
参数：h : a * b ∣ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem dvd_of_mul_right_dvd (h : a * b ∣ c) : a ∣ c :=
  (dvd_mul_right a b).trans h

/-- An element `a` in a semigroup is primal if whenever `a` is a divisor of `b * c`, it can be
factored as the product of a divisor of `b` and a divisor of `c`. -/
/-
**IsPrimal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsPrimal (a : α) : Prop
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element `a` in a semigroup is primal if whenever `a` is a divisor of `b * c`,
 it can be
factored as the product of a divisor of `b` and a divisor of `c`.
-/
def IsPrimal (a : α) : Prop := ∀ ⦃b c⦄, a ∣ b * c → ∃ a₁ a₂, a₁ ∣ b ∧ a₂ ∣ c ∧ a = a₁ * a₂

variable (α) in
/-- A monoid is a decomposition monoid if every element is primal. An integral domain whose
multiplicative monoid is a decomposition monoid, is called a pre-Schreier domain; it is a
Schreier domain if it is moreover integrally closed. -/
/-
**DecompositionMonoid** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [Semigroup α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoid is a decomposition monoid if every element is primal. An integral domai
n whose
multiplicative monoid is a decomposition monoid, is called a pre-Schreier domain
; it is a
Schreier domain if it is moreover integrally closed.
-/
@[mk_iff] class DecompositionMonoid : Prop where
  primal (a : α) : IsPrimal a
/-
**exists_dvd_and_dvd_of_dvd_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_dvd_and_dvd_of_dvd_mul [DecompositionMonoid α] {b c a : α} (H : a ∣
 b * c) : exists a₁ a₂, a₁ ∣ b ∧ a₂ ∣ c ∧ a = a₁ * a₂
参数：H : a ∣ b * c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DecompositionMonoid.primal`：∀ {α : Type u_1} {inst : Semigroup α} [self 
: DecompositionMonoid α] (a : α), IsPrimal a
-/
theorem exists_dvd_and_dvd_of_dvd_mul [DecompositionMonoid α] {b c a : α} (H : a ∣ b * c) :
    ∃ a₁ a₂, a₁ ∣ b ∧ a₂ ∣ c ∧ a = a₁ * a₂ := DecompositionMonoid.primal a H

@[gcongr]
/-
**mul_dvd_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
参数：a : α；h : b ∣ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c := by
  obtain ⟨d, rfl⟩ := h
  use d
  rw [mul_assoc]
/-
**IsLeftRegular.dvd_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeftRegular.dvd_cancel_left (h : IsLeftRegular a) : a * b ∣ a * c ↔ b ∣ 
c
参数：h : IsLeftRegular a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
-/
theorem IsLeftRegular.dvd_cancel_left (h : IsLeftRegular a) : a * b ∣ a * c ↔ b ∣ c :=
  ⟨fun dvd ↦ have ⟨d, eq⟩ := dvd; ⟨d, h (eq.trans <| mul_assoc ..)⟩, mul_dvd_mul_left a⟩

/-- Right divisibility relation. `RightDvd a b` means `a` right-divides `b`,
i.e., `∃ c, b = c * a`. -/
/-
**RightDvd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RightDvd (a b : α) : Prop
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right divisibility relation. `RightDvd a b` means `a` right-divides `b`,
i.e., `∃ c, b = c * a`.
-/
def RightDvd (a b : α) : Prop := ∃ c, b = c * a

@[inherit_doc]
infix:50 " ∣ᵣ " => RightDvd

@[trans]
/-
**RightDvd.trans** 是 Mathlib 中的一个定理，位于命名空间 `RightDvd`。
形式化陈述：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ᵣ b → b ∣ᵣ c → a ∣ᵣ 
c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
protected theorem RightDvd.trans : a ∣ᵣ b → b ∣ᵣ c → a ∣ᵣ c
  | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨e * d, h₁ ▸ h₂.trans <| (mul_assoc e d a).symm⟩

/-- Transitivity of `RightDvd` for use in `calc` blocks. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transitivity of `RightDvd` for use in `calc` blocks.
-/
instance : IsTrans α RightDvd :=
  ⟨fun _ _ _ => RightDvd.trans⟩

@[simp]
/-
**RightDvd.mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RightDvd.mul_self (a b : α) : a ∣ᵣ b * a
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RightDvd.mul_self (a b : α) : a ∣ᵣ b * a :=
  ⟨b, rfl⟩
/-
**RightDvd.mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RightDvd.mul_left (h : a ∣ᵣ b) (c : α) : a ∣ᵣ c * b
参数：h : a ∣ᵣ b；c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RightDvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ᵣ 
b → b ∣ᵣ c → a ∣ᵣ c
· 使用定理 `RightDvd.mul_self`：RightDvd.mul_self (a b : α) : a ∣ᵣ b * a
-/
theorem RightDvd.mul_left (h : a ∣ᵣ b) (c : α) : a ∣ᵣ c * b :=
  h.trans (RightDvd.mul_self b c)
/-
**RightDvd.of_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RightDvd.of_mul_left (h : b * a ∣ᵣ c) : a ∣ᵣ c
参数：h : b * a ∣ᵣ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RightDvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ᵣ 
b → b ∣ᵣ c → a ∣ᵣ c
· 使用定理 `RightDvd.mul_self`：RightDvd.mul_self (a b : α) : a ∣ᵣ b * a
-/
theorem RightDvd.of_mul_left (h : b * a ∣ᵣ c) : a ∣ᵣ c :=
  (RightDvd.mul_self a b).trans h

@[gcongr]
/-
**RightDvd.mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RightDvd.mul_const (a : α) (h : b ∣ᵣ c) : b * a ∣ᵣ c * a
参数：a : α；h : b ∣ᵣ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem RightDvd.mul_const (a : α) (h : b ∣ᵣ c) : b * a ∣ᵣ c * a := by
  obtain ⟨d, rfl⟩ := h
  use d
  rw [mul_assoc]
/-
**IsRightRegular.rightDvd_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRightRegular.rightDvd_cancel_right (h : IsRightRegular a) : b * a ∣ᵣ c *
 a ↔ b ∣ᵣ c
参数：h : IsRightRegular a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `RightDvd.mul_const`：RightDvd.mul_const (a : α) (h : b ∣ᵣ c) : b * a ∣ᵣ c
 * a
-/
theorem IsRightRegular.rightDvd_cancel_right (h : IsRightRegular a) :
    b * a ∣ᵣ c * a ↔ b ∣ᵣ c :=
  ⟨fun dvd ↦ have ⟨d, eq⟩ := dvd
    ⟨d, h (eq.trans <| (mul_assoc ..).symm)⟩, RightDvd.mul_const a⟩
/-
**rightDvd_iff_op_dvd_op** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rightDvd_iff_op_dvd_op : a ∣ᵣ b ↔ MulOpposite.op a ∣ MulOpposite.op b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightDvd_iff_op_dvd_op : a ∣ᵣ b ↔ MulOpposite.op a ∣ MulOpposite.op b :=
  ⟨fun ⟨c, hc⟩ => ⟨MulOpposite.op c, by simp [hc]⟩,
   fun ⟨c, hc⟩ => ⟨MulOpposite.unop c, by simpa using congrArg MulOpposite.unop hc⟩⟩

end Semigroup

section RightCancelSemigroup

variable [RightCancelSemigroup α] {a b c : α}

@[simp]
/-
**mul_rightDvd_mul_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_rightDvd_mul_iff_left : b * a ∣ᵣ c * a ↔ b ∣ᵣ c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_right_cancel`：mul_right_cancel : a * b = c * b -> a = c
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `RightDvd.mul_const`：RightDvd.mul_const (a : α) (h : b ∣ᵣ c) : b * a ∣ᵣ c
 * a
-/
theorem mul_rightDvd_mul_iff_left : b * a ∣ᵣ c * a ↔ b ∣ᵣ c :=
  ⟨fun ⟨d, eq⟩ ↦ ⟨d, mul_right_cancel (eq.trans (mul_assoc ..).symm)⟩, RightDvd.mul_const a⟩

end RightCancelSemigroup

section Monoid
variable [Monoid α] {a b c : α} {m n : ℕ}

@[refl, simp]
/-
**dvd_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_refl (a : α) : a ∣ a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem dvd_refl (a : α) : a ∣ a :=
  Dvd.intro 1 (mul_one a)
/-
**dvd_rfl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_rfl : forall {a : α}, a ∣ a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
theorem dvd_rfl : ∀ {a : α}, a ∣ a := fun {a} => dvd_refl a
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Refl α (· ∣ ·) :=
  ⟨dvd_refl⟩
/-
**one_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_dvd (a : α) : 1 ∣ a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem one_dvd (a : α) : 1 ∣ a :=
  Dvd.intro a (one_mul a)
/-
**dvd_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_of_eq (h : a = b) : a ∣ b
参数：h : a = b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
theorem dvd_of_eq (h : a = b) : a ∣ b := by rw [h]

alias Eq.dvd := dvd_of_eq

@[gcongr]
/-
**pow_dvd_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
参数：a : α；h : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
-/
lemma pow_dvd_pow (a : α) (h : m ≤ n) : a ^ m ∣ a ^ n :=
  ⟨a ^ (n - m), by rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]⟩
/-
**dvd_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dvd_pow (hab : a ∣ b) : forall {n : Nat} (_ : n != 0), a ∣ b ^ n | 0, hn =
> (hn rfl).elim | n + 1, _ => by rw [pow_succ']; exact hab.mul_right _  alias Dv
d.dvd.pow
参数：hab : a ∣ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Dvd.dvd.mul_right`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α}, a ∣ 
b → ∀ (c : α), a ∣ b * c
-/
lemma dvd_pow (hab : a ∣ b) : ∀ {n : ℕ} (_ : n ≠ 0), a ∣ b ^ n
  | 0, hn => (hn rfl).elim
  | n + 1, _ => by rw [pow_succ']; exact hab.mul_right _

alias Dvd.dvd.pow := dvd_pow
/-
**dvd_pow_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n
参数：a : α；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.pow`：∀ {α : Type u_1} [inst : Monoid α] {a b : α}, a ∣ b → ∀ {n 
: ℕ}, n ≠ 0 → a ∣ b ^ n
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
lemma dvd_pow_self (a : α) {n : ℕ} (hn : n ≠ 0) : a ∣ a ^ n := dvd_rfl.pow hn

@[refl, simp]
/-
**RightDvd.refl** 是 Mathlib 中的一个定理，位于命名空间 `RightDvd`。
形式化陈述：∀ {α : Type u_1} [inst : Monoid α] (a : α), a ∣ᵣ a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
protected theorem RightDvd.refl (a : α) : a ∣ᵣ a :=
  ⟨1, (one_mul a).symm⟩
/-
**RightDvd.rfl** 是 Mathlib 中的一个定理，位于命名空间 `RightDvd`。
形式化陈述：∀ {α : Type u_1} [inst : Monoid α] {a : α}, a ∣ᵣ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RightDvd.refl`：∀ {α : Type u_1} [inst : Monoid α] (a : α), a ∣ᵣ a
-/
protected theorem RightDvd.rfl {a : α} : a ∣ᵣ a := .refl _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPreorder α RightDvd where
  refl := .refl
/-
**RightDvd.of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RightDvd.of_eq (h : a = b) : a ∣ᵣ b
参数：h : a = b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RightDvd.refl`：∀ {α : Type u_1} [inst : Monoid α] (a : α), a ∣ᵣ a
-/
theorem RightDvd.of_eq (h : a = b) : a ∣ᵣ b := by rw [h]

alias Eq.rightDvd := RightDvd.of_eq

end Monoid

section CommSemigroup

variable [CommSemigroup α] {a b c : α}

/-
**Dvd.intro_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b
参数：c : α；h : c * a = b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b :=
  Dvd.intro c (by rw [mul_comm] at h; apply h)

alias dvd_of_mul_left_eq := Dvd.intro_left
/-
**exists_eq_mul_left_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_eq_mul_left_of_dvd (h : a ∣ b) : exists c, b = c * a
参数：h : a ∣ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.elim`：Dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : forall c, b =
 a * c -> P) : P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem exists_eq_mul_left_of_dvd (h : a ∣ b) : ∃ c, b = c * a :=
  Dvd.elim h fun c => fun H1 : b = a * c => Exists.intro c (Eq.trans H1 (mul_comm a c))
/-
**dvd_iff_exists_eq_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_iff_exists_eq_mul_left : a ∣ b ↔ exists c, b = c * a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_eq_mul_left_of_dvd`：exists_eq_mul_left_of_dvd (h : a ∣ b) : exist
s c, b = c * a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dvd_iff_exists_eq_mul_left : a ∣ b ↔ ∃ c, b = c * a :=
  ⟨exists_eq_mul_left_of_dvd, by
    rintro ⟨c, rfl⟩
    exact ⟨c, mul_comm _ _⟩⟩
/-
**Dvd.elim_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dvd.elim_left {P : Prop} (h₁ : a ∣ b) (h₂ : forall c, b = c * a -> P) : P
参数：h₁ : a ∣ b；h₂ : forall c, b = c * a -> P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `exists_eq_mul_left_of_dvd`：exists_eq_mul_left_of_dvd (h : a ∣ b) : exist
s c, b = c * a
-/
theorem Dvd.elim_left {P : Prop} (h₁ : a ∣ b) (h₂ : ∀ c, b = c * a → P) : P :=
  Exists.elim (exists_eq_mul_left_of_dvd h₁) fun c => fun h₃ : b = c * a => h₂ c h₃

@[simp]
/-
**dvd_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_mul_left (a b : α) : a ∣ b * a
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem dvd_mul_left (a b : α) : a ∣ b * a :=
  Dvd.intro b (mul_comm a b)
/-
**dvd_mul_of_dvd_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c * b
参数：h : a ∣ b；c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Dvd.dvd.mul_right`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α}, a ∣ 
b → ∀ (c : α), a ∣ b * c
-/
theorem dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c * b := by
  rw [mul_comm]; exact h.mul_right _

alias Dvd.dvd.mul_left := dvd_mul_of_dvd_right

attribute [local simp] mul_assoc mul_comm mul_left_comm

@[gcongr]
/-
**mul_dvd_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a ∣ b → c ∣ d → a
 * c ∣ b * d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_dvd_mul : ∀ {a b c d : α}, a ∣ b → c ∣ d → a * c ∣ b * d
  | a, _, c, _, ⟨e, rfl⟩, ⟨f, rfl⟩ => ⟨e * f, by simp⟩
/-
**dvd_of_mul_left_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c
参数：h : a * b ∣ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.elim`：Dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : forall c, b =
 a * c -> P) : P
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c :=
  Dvd.elim h fun d ceq => Dvd.intro (a * d) (by simp [ceq])
/-
**dvd_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_mul [DecompositionMonoid α] {k m n : α} : k ∣ m * n ↔ exists d₁ d₂, d₁
 ∣ m ∧ d₂ ∣ n ∧ k = d₁ * d₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_dvd_and_dvd_of_dvd_mul`：exists_dvd_and_dvd_of_dvd_mul [Decomposit
ionMonoid α] {b c a : α} (H : a ∣ b * c) : exists a₁ a₂, a₁ ∣ b ∧ a₂ ∣ c ∧ a = a
₁ * a₂
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dvd_mul [DecompositionMonoid α] {k m n : α} :
    k ∣ m * n ↔ ∃ d₁ d₂, d₁ ∣ m ∧ d₂ ∣ n ∧ k = d₁ * d₂ := by
  refine ⟨exists_dvd_and_dvd_of_dvd_mul, ?_⟩
  rintro ⟨d₁, d₂, hy, hz, rfl⟩
  gcongr

@[simp]
/-
**rightDvd_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rightDvd_iff_dvd : a ∣ᵣ b ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rightDvd_iff_dvd : a ∣ᵣ b ↔ a ∣ b :=
  exists_congr fun c ↦ by rw [mul_comm]

end CommSemigroup

section CommMonoid

variable [CommMonoid α] {a b : α}

/-
**mul_dvd_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c
参数：h : a ∣ b；c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
theorem mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c := by
  gcongr
/-
**pow_dvd_pow_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_dvd_pow_of_dvd (h : a ∣ b) (n : Nat) : a ^ n ∣ b ^ n
参数：h : a ∣ b；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
-/
theorem pow_dvd_pow_of_dvd (h : a ∣ b) (n : ℕ) : a ^ n ∣ b ^ n := by
  induction n with
  | zero => simp
  | succ =>
    rw [pow_succ, pow_succ]
    gcongr

@[gcongr]
/-
**pow_dvd_pow_of_dvd_of_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_dvd_pow_of_dvd_of_le {m n : Nat} (hab : a ∣ b) (hmn : m <= n) : a ^ m 
∣ b ^ n
参数：hab : a ∣ b；hmn : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransDvd`：∀ {α : Type u_1} [inst : Semigroup α], IsTrans α Dvd.dvd
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `pow_dvd_pow_of_dvd`：pow_dvd_pow_of_dvd (h : a ∣ b) (n : Nat) : a ^ n ∣ b
 ^ n
-/
lemma pow_dvd_pow_of_dvd_of_le {m n : ℕ} (hab : a ∣ b) (hmn : m ≤ n) : a ^ m ∣ b ^ n := by
  trans (a ^ n) <;> [gcongr; apply_rules [pow_dvd_pow_of_dvd]]

end CommMonoid

