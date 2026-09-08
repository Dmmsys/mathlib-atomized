/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Data.Option.NAry

/-!
# Adjoining a zero/one to semigroups and mapping
-/

@[expose] public section

variable {α β γ : Type*}

namespace WithOne

/-- Lift a map `f : α → β` to `WithOne α → WithOne β`. Implemented using `Option.map`.

Note: the definition previously known as `WithOne.map` is now called `WithOne.mapMulHom`. -/
@[to_additive
/-- Lift a map `f : α → β` to `WithZero α → WithZero β`. Implemented using `Option.map`.

Note: the definition previously known as `WithZero.map` is now called `WithZero.mapAddHom`. -/]
/-
**WithOne.map** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
形式化陈述：map (f : α -> β) : WithOne α -> WithOne β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map (f : α → β) : WithOne α → WithOne β := Option.map f

@[to_additive (attr := simp)]
/-
**WithOne.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：map_bot (f : α -> β) : map f 1 = 1
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_bot (f : α → β) : map f 1 = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**WithOne.map_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：map_coe (f : α -> β) (a : α) : map f a = f a
参数：f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl

/-- The image of a binary function `f : α → β → γ` as a function
`WithOne α → WithOne β → WithOne γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
@[to_additive
/-- The image of a binary function `f : α → β → γ` as a function
`WithZero α → WithZero β → WithZero γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/]
/-
**WithOne.map** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
形式化陈述：map (f : α -> β) : WithOne α -> WithOne β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map₂ : (α → β → γ) → WithOne α → WithOne β → WithOne γ := Option.map₂

@[to_additive]
/-
**WithOne.map** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
形式化陈述：map (f : α -> β) : WithOne α -> WithOne β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : map₂ f a b = f a b := rfl
@[to_additive (attr := simp)]
/-
**WithOne.map** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
形式化陈述：map (f : α -> β) : WithOne α -> WithOne β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_bot_left (f : α → β → γ) (b) : map₂ f 1 b = 1 := rfl
@[to_additive (attr := simp)]
/-
**WithOne.map** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
形式化陈述：map (f : α -> β) : WithOne α -> WithOne β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_bot_right (f : α → β → γ) (a) : map₂ f a 1 = 1 := by cases a <;> rfl
@[to_additive (attr := simp)]
/-
**WithOne.map** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
形式化陈述：map (f : α -> β) : WithOne α -> WithOne β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_coe_left (f : α → β → γ) (a : α) (b) : map₂ f a b = b.map fun b ↦ f a b := rfl
@[to_additive (attr := simp)]
/-
**WithOne.map** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
形式化陈述：map (f : α -> β) : WithOne α -> WithOne β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_coe_right (f : α → β → γ) (a) (b : β) : map₂ f a b = a.map (f · b) := by
  cases a <;> rfl

@[to_additive (attr := simp)]
/-
**WithOne.map** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
形式化陈述：map (f : α -> β) : WithOne α -> WithOne β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₂_eq_bot_iff {f : α → β → γ} {a : WithOne α} {b : WithOne β} :
    map₂ f a b = 1 ↔ a = 1 ∨ b = 1 := Option.map₂_eq_none_iff

end WithOne

