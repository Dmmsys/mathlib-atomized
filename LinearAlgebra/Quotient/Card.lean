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

/--
theorem `card_eq_card_quotient_mul_card` / 定理 `card_eq_card_quotient_mul_card`

English:
theorem card_eq_card_quotient_mul_card
  given: (S : Submodule R M)
  proof: by
  rw [mul_comm]; rw [← Nat.card_prod]
  exact Nat.card_congr AddSubgroup.addGroupEquivQuotientProdAddSubgroup

中文:
定理 card_eq_card_quotient_mul_card
  条件: (S : Submodule R M)
  证明: by
  rw [mul_comm]; rw [← Nat.card_prod]
  exact Nat.card_congr AddSubgroup.addGroupEquivQuotientProdAddSubgroup

Depends on / 依赖: AddSubgroup, AddSubgroup.addGroupEquivQuotientProdAddSubgroup, Nat.card_congr, Nat.card_prod, addGroupEquivQuotientProdAddSubgroup, card_congr, card_prod, mul_comm
-/
theorem card_eq_card_quotient_mul_card (S : Submodule R M) :
    Nat.card M = Nat.card S * Nat.card (M ⧸ S) := by
  rw [mul_comm]; rw [← Nat.card_prod]
  exact Nat.card_congr AddSubgroup.addGroupEquivQuotientProdAddSubgroup

end Submodule
