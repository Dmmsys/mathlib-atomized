/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Data.Complex.Basic

/-!
# The cardinality of the complex numbers

This file shows that the complex numbers have cardinality continuum, i.e. `#ℂ = 𝔠`.
-/

public section

open Cardinal Set

open Cardinal

/-- The cardinality of the complex numbers, as a type. -/
@[simp]
/-
**Cardinal.mk_complex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Cardinal.mk_complex : #Complex = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Cardinal.mk_prod`：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v
, u} #α * lift.{u, v} #β
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.mk_real`：mk_real : #Real = 𝔠
· 使用定理 `Cardinal.continuum_mul_self`：continuum_mul_self : 𝔠 * 𝔠 = 𝔠

--- 原说明 ---
The cardinality of the complex numbers, as a type.
-/
theorem Cardinal.mk_complex : #ℂ = 𝔠 := by
  rw [mk_congr Complex.equivRealProd, mk_prod, lift_id, mk_real, continuum_mul_self]

/-- The cardinality of the complex numbers, as a set. -/
/-
**Cardinal.mk_univ_complex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Cardinal.mk_univ_complex : #(Set.univ : Set Complex) = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_univ`：mk_univ {α : Type u} : #(@univ α) = #α
· 使用定理 `Cardinal.mk_complex`：Cardinal.mk_complex : #Complex = 𝔠

--- 原说明 ---
The cardinality of the complex numbers, as a set.
-/
theorem Cardinal.mk_univ_complex : #(Set.univ : Set ℂ) = 𝔠 := by rw [mk_univ, mk_complex]

/-- The complex numbers are not countable. -/
/-
**not_countable_complex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_countable_complex : ¬(Set.univ : Set Complex).Countable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.le_aleph0_iff_set_countable`：le_aleph0_iff_set_countable {s : S
et α} : #s <= ℵ₀ ↔ s.Countable
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Cardinal.mk_univ_complex`：Cardinal.mk_univ_complex : #(Set.univ : Set Co
mplex) = 𝔠
· 使用定理 `Cardinal.cantor`：cantor (a : Cardinal.{u}) : a < 2 ^ a

--- 原说明 ---
The complex numbers are not countable.
-/
theorem not_countable_complex : ¬(Set.univ : Set ℂ).Countable := by
  rw [← le_aleph0_iff_set_countable, not_le, Cardinal.mk_univ_complex]
  apply cantor
