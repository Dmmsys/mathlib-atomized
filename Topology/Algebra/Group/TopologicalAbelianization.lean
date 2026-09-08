/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# The topological abelianization of a group.

This file defines the topological abelianization of a topological group.

## Main definitions

* `TopologicalAbelianization`: defines the topological abelianization of a group `G` as the quotient
  of `G` by the topological closure of its commutator subgroup..

## Main results
- `instNormalCommutatorClosure` : the topological closure of the commutator of a topological group
  `G` is a normal subgroup.

## Tags
group, topological abelianization

-/

public section

open scoped commutatorElement

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-
**instNormalCommutatorClosure** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instNormalCommutatorClosure : (commutator G).topologicalClosure.Normal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.is_normal_topologicalClosure`：Subgroup.is_normal_topologicalClo
sure {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] (N : Subg
roup G) [N.Normal] : (Subgr…
· 使用定理 `instNormalCommutator`：∀ (G : Type u_1) [inst : Group G], (commutator G).
Normal
-/
instance instNormalCommutatorClosure : (commutator G).topologicalClosure.Normal :=
  Subgroup.is_normal_topologicalClosure (commutator G)

/-- The topological abelianization of `absoluteGaloisGroup`, that is, the quotient of
  `absoluteGaloisGroup` by the topological closure of its commutator subgroup. -/
/-
**TopologicalAbelianization** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：TopologicalAbelianization
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topological abelianization of `absoluteGaloisGroup`, that is, the quotient o
f
  `absoluteGaloisGroup` by the topological closure of its commutator subgroup.
-/
abbrev TopologicalAbelianization := G ⧸ Subgroup.topologicalClosure (commutator G)

local notation "G_ab" => TopologicalAbelianization

namespace TopologicalAbelianization

/-
**TopologicalAbelianization.commGroup** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalAbel
ianization`。
形式化陈述：commGroup : CommGroup (G_ab G) where mul_comm
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commGroup : CommGroup (G_ab G) where
  mul_comm := fun x y =>
    Quotient.inductionOn₂' x y fun a b =>
      Quotient.sound' <|
        QuotientGroup.leftRel_apply.mpr <| by
          have h : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by group
          rw [h]
          exact Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator
            (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹))
  __ : Group (G_ab G) := inferInstance

end TopologicalAbelianization

