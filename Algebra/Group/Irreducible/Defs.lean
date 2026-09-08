/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Logic.Basic

/-!
# Irreducible elements in a monoid

This file defines irreducible elements of a monoid (`Irreducible`), as non-units that can't be
written as the product of two non-units. This generalises irreducible elements of a ring.
We also define the additive variant (`AddIrreducible`).

In decomposition monoids (e.g., `ℕ`, `ℤ`), this predicate is equivalent to `Prime`
(see `irreducible_iff_prime`), however this is not true in general.
-/

public section

assert_not_exists MonoidWithZero IsOrderedMonoid Multiset

variable {M : Type*}

/-- `AddIrreducible p` states that `p` is not an additive unit and cannot be written as a sum of
additive non-units. -/
/-
**AddIrreducible** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{M : Type u_1} → [AddMonoid M] → M → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddIrreducible p` states that `p` is not an additive unit and cannot be written
 as a sum of
additive non-units.
-/
structure AddIrreducible [AddMonoid M] (p : M) : Prop where
  /-- An irreducible element is not an additive unit. -/
  not_isAddUnit : ¬IsAddUnit p
  /-- If an irreducible element can be written as a sum, then one term is an additive unit. -/
  isAddUnit_or_isAddUnit ⦃a b⦄ : p = a + b → IsAddUnit a ∨ IsAddUnit b

section Monoid
variable [Monoid M] {p q a b : M}

/-- `Irreducible p` states that `p` is non-unit and only factors into units.

We explicitly avoid stating that `p` is non-zero, this would require a semiring. Assuming only a
monoid allows us to reuse irreducible for associated elements. -/
@[to_additive (attr := wikidata Q2989575)]
/-
**Irreducible** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{M : Type u_1} → [Monoid M] → M → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Irreducible p` states that `p` is non-unit and only factors into units.

We explicitly avoid stating that `p` is non-zero, this would require a semiring.
 Assuming only a
monoid allows us to reuse irreducible for associated elements.
-/
structure Irreducible (p : M) : Prop where
  /-- An irreducible element is not a unit. -/
  not_isUnit : ¬IsUnit p
  /-- If an irreducible element factors, then one factor is a unit. -/
  isUnit_or_isUnit ⦃a b : M⦄ : p = a * b → IsUnit a ∨ IsUnit b
/-
**irreducible_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irreducible p ↔ ¬IsUnit p ∧ ∀ 
⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
@[to_additive] lemma irreducible_iff :
    Irreducible p ↔ ¬IsUnit p ∧ ∀ ⦃a b⦄, p = a * b → IsUnit a ∨ IsUnit b where
  mp hp := ⟨hp.not_isUnit, hp.isUnit_or_isUnit⟩
  mpr hp := ⟨hp.1, hp.2⟩

@[to_additive (attr := simp)]
/-
**not_irreducible_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_irreducible_one : ¬Irreducible (1 : M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma not_irreducible_one : ¬Irreducible (1 : M) := by simp [irreducible_iff]

@[to_additive]
/-
**Irreducible.ne_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Irreducible.ne_one (hp : Irreducible p) : p != 1
参数：hp : Irreducible p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `not_irreducible_one`：not_irreducible_one : ¬Irreducible (1 : M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Irreducible.ne_one (hp : Irreducible p) : p ≠ 1 := by rintro rfl; exact not_irreducible_one hp

@[to_additive]
/-
**of_irreducible_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Irreducible (a * b) → IsUnit
 a ∨ IsUnit b
参数：a * b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_irreducible_mul : Irreducible (a * b) → IsUnit a ∨ IsUnit b | ⟨_, h⟩ => h rfl

@[to_additive]
/-
**irreducible_or_factor** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：irreducible_or_factor (hp : ¬IsUnit p) : Irreducible p ∨ exists a b, ¬IsUn
it a ∧ ¬IsUnit b ∧ p = a * b
参数：hp : ¬IsUnit p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
lemma irreducible_or_factor (hp : ¬IsUnit p) :
    Irreducible p ∨ ∃ a b, ¬IsUnit a ∧ ¬IsUnit b ∧ p = a * b := by
  simpa [irreducible_iff, hp, and_rotate] using em (∀ a b, p = a * b → IsUnit a ∨ IsUnit b)

@[to_additive]
/-
**Irreducible.eq_one_or_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Irreducible.eq_one_or_eq_one [Subsingleton Mˣ] (hab : Irreducible (a * b))
 : a = 1 ∨ b = 1
参数：hab : Irreducible (a * b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
-/
lemma Irreducible.eq_one_or_eq_one [Subsingleton Mˣ] (hab : Irreducible (a * b)) :
    a = 1 ∨ b = 1 := by simpa using hab.isUnit_or_isUnit rfl

end Monoid

