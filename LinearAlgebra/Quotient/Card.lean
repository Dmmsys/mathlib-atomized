/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
module

public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Coset.Basic

/-! Results about the cardinality of a quotient module. -/

public section

namespace Submodule

open LinearMap QuotientAddGroup

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-
**Submodule.card_eq_card_quotient_mul_card** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：card_eq_card_quotient_mul_card (S : Submodule R M) : Nat.card M = Nat.card
 S * Nat.card (M ⧸ S)
参数：S : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem card_eq_card_quotient_mul_card (S : Submodule R M) :
    Nat.card M = Nat.card S * Nat.card (M ⧸ S) := by
  rw [mul_comm, ← Nat.card_prod]
  exact Nat.card_congr AddSubgroup.addGroupEquivQuotientProdAddSubgroup

end Submodule

