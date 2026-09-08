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
/-
**Subsemigroup.center_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : Mul M] [inst_1 : Mul N],   Subsemi
group.center (M × N) = (Subsemigroup.center M).prod (Subsemigroup.center N)
参数：M × N；Subsemigroup.center M；Subsemigroup.center N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_prod`：∀ {M : Type u_1} [inst : Mul M] {N : Type u_2} [inst_1 
: Mul N], Set.center (M × N) = Set.center M ×ˢ Set.center N
-/
protected theorem center_prod : center (M × N) = prod (center M) (center N) :=
  SetLike.coe_injective Set.center_prod

end Subsemigroup

