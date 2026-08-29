/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Algebra.Group.Subsemigroup.Operations
public import Mathlib.GroupTheory.Subsemigroup.Center

/-!
# Lemmas about subsemigroups

This file collects various lemmas about subsemigroups.
-/

public section

variable {M N : Type*} [Mul M] [Mul N]

namespace Subsemigroup

@[to_additive]
/--
theorem `center_prod` / 定理 `center_prod`

English:
theorem center_prod
  statement: center (M × N) = prod (center M) (center N)
  proof: SetLike.coe_injective Set.center_prod

中文:
定理 center_prod
  结论: center (M × N) = 乘积 (center M) (center N)
  证明: SetLike.coe_injective Set.center_prod

Depends on / 依赖: Equiv.swap_injective_of_left, Function, Function.Injective.nontrivial, Injective, Nontrivial, Nontrivial.to_nonempty, classical, nontrivial, swap_injective_of_left, to_nonempty
-/
protected theorem center_prod : center (M × N) = prod (center M) (center N) :=
  SetLike.coe_injective Set.center_prod

end Subsemigroup
