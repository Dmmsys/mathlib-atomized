/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Countable.Small
public import Mathlib.Data.Fintype.EquivFin

/-!
# Fintype instance for `Shrink`
-/

public section

universe u v
variable {α : Type u} [Fintype α]

/-
**Shrink.instFintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Shrink.instFintype : Fintype (Shrink.{v} α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance Shrink.instFintype : Fintype (Shrink.{v} α) := .ofEquiv _ (equivShrink _)
/-
**Shrink.instFinite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Shrink.instFinite {α : Type u} [Finite α] : Finite (Shrink.{v} α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Countable.toSmall`：∀ (α : Type v) [Countable α], Small.{w, v} α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
-/
instance Shrink.instFinite {α : Type u} [Finite α] : Finite (Shrink.{v} α) :=
  .of_equiv _ (equivShrink _)
/-
**Fintype.card_shrink** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {α : Type u} [inst : Fintype α] [inst_1 : Fintype (Shrink.{v, u} α)], Fi
ntype.card (Shrink.{v, u} α) = Fintype.card α
参数：Shrink.{v, u} α；Shrink.{v, u} α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Countable.toSmall`：∀ (α : Type v) [Countable α], Small.{w, v} α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma Fintype.card_shrink [Fintype (Shrink.{v} α)] : card (Shrink.{v} α) = card α :=
  card_congr (equivShrink _).symm
