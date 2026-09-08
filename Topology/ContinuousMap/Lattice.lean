/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Nicolò Cavalleri
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Order.Group.Lattice
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Ordered

/-!
# Continuous maps as a lattice ordered group
-/

public section


/-!
We now provide formulas for `f ⊓ g` and `f ⊔ g`, where `f g : C(α, β)`,
in terms of `ContinuousMap.abs`.
-/

namespace ContinuousMap

variable {α : Type*} [TopologicalSpace α]
variable {β : Type*} [TopologicalSpace β]

section Lattice

/-! `C(α, β)` is a lattice ordered group. -/

@[to_additive]
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`C(α, β)` is a lattice ordered group.
-/
instance [PartialOrder β] [CommMonoid β] [IsOrderedMonoid β] [ContinuousMul β] :
    IsOrderedMonoid C(α, β) where
  mul_le_mul_left _ _ hfg c x := mul_le_mul_left (hfg x) (c x)

variable [Group β] [IsTopologicalGroup β] [Lattice β] [TopologicalLattice β]

@[to_additive (attr := simp, norm_cast)]
/-
**ContinuousMap.coe_mabs** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：coe_mabs (f : C(α, β)) : ⇑|f|ₘ = |⇑f|ₘ
参数：f : C(α, β)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mabs (f : C(α, β)) : ⇑|f|ₘ = |⇑f|ₘ := rfl

@[to_additive (attr := simp)]
/-
**ContinuousMap.mabs_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：mabs_apply (f : C(α, β)) (x : α) : |f|ₘ x = |f x|ₘ
参数：f : C(α, β)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mabs_apply (f : C(α, β)) (x : α) : |f|ₘ x = |f x|ₘ := rfl

end Lattice

end ContinuousMap

