/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Fintype.Card

/-!
# `Finite`, `Infinite` and `Fintype` are preserved by `Additive` and `Multiplicative`.
-/

public section

assert_not_exists MonoidWithZero MulAction

universe u

variable {α : Type u}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite α] : Finite (Additive α) :=
  Finite.of_equiv α (by rfl)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite α] : Finite (Multiplicative α) :=
  Finite.of_equiv α (by rfl)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : Infinite α] : Infinite (Additive α) := h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : Infinite α] : Infinite (Multiplicative α) := h
/-
**Additive.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.fintype : forall [Fintype α], Fintype (Additive α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.fintype : ∀ [Fintype α], Fintype (Additive α) :=
  Fintype.ofEquiv α Additive.ofMul
/-
**Multiplicative.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.fintype : forall [Fintype α], Fintype (Multiplicative α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.fintype : ∀ [Fintype α], Fintype (Multiplicative α) :=
  Fintype.ofEquiv α Multiplicative.ofAdd
/-
**Fintype.card_multiplicative** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ (α : Type u_1) [inst : Fintype α], Fintype.card (Multiplicative α) = Fin
type.card α
参数：α : Type u_1；Multiplicative α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
@[simp] lemma Fintype.card_multiplicative (α : Type*) [Fintype α] :
    card (Multiplicative α) = card α := Finset.card_map _
/-
**Fintype.card_additive** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ (α : Type u_1) [inst : Fintype α], Fintype.card (Additive α) = Fintype.c
ard α
参数：α : Type u_1；Additive α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
@[simp] lemma Fintype.card_additive (α : Type*) [Fintype α] : card (Additive α) = card α :=
  Finset.card_map _
