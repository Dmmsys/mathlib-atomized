/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Closed subgroups of a topological group

This file builds the frame of closed subgroups in a topological group `G`,
and its additive version `ClosedAddSubgroup`.

## Main definitions and results

* `normalCore_isClosed`: The `normalCore` of a closed subgroup is closed.

* `finindex_closedSubgroup_isOpen`: A closed subgroup with finite index is open.

## TODO

Actually provide the `Order.Frame (ClosedSubgroup G)` instance.
-/

public section

section

universe u v

/-- The type of closed subgroups of a topological group. -/
@[ext]
/--
Definition of `ClosedSubgroup` / `ClosedSubgroup` 的定义

English:
structure ClosedSubgroup
  parameters: (G : Type u) [Group G] [TopologicalSpace G]
  extends: Subgroup G
  axioms and operations (1):
    - isClosed' : IsClosed carrier

中文:
结构 ClosedSubgroup
  参数: (G : 类型u) [Group G] [TopologicalSpace G]
  继承: Subgroup G
  公理与运算 (1 个):
    - isClosed' : IsClosed carrier
-/
structure ClosedSubgroup (G : Type u) [Group G] [TopologicalSpace G] extends Subgroup G where
  isClosed' : IsClosed carrier

/-- The type of closed subgroups of an additive topological group. -/
@[ext]
/--
Definition of `ClosedAddSubgroup` / `ClosedAddSubgroup` 的定义

English:
structure ClosedAddSubgroup
  parameters: (G : Type u) [AddGroup G] [TopologicalSpace G]
  axioms and operations (1):
    - isClosed' : IsClosed carrier

中文:
结构 ClosedAddSubgroup
  参数: (G : 类型u) [AddGroup G] [TopologicalSpace G]
  公理与运算 (1 个):
    - isClosed' : IsClosed carrier
-/
structure ClosedAddSubgroup (G : Type u) [AddGroup G] [TopologicalSpace G] extends
    AddSubgroup G where
  isClosed' : IsClosed carrier

attribute [to_additive] ClosedSubgroup

attribute [coe] ClosedSubgroup.toSubgroup ClosedAddSubgroup.toAddSubgroup

namespace ClosedSubgroup

variable (G : Type u) [Group G] [TopologicalSpace G]

variable {G} in
@[to_additive]
/--
theorem `toSubgroup_injective` / 定理 `toSubgroup_injective`

English:
theorem toSubgroup_injective
  statement: Function.Injective
  proof: fun A B h => by
  ext
  rw [h]

@[to_additive]

中文:
定理 toSubgroup_injective
  结论: Function.Injective
  证明: fun A B h => by
  ext
  rw [h]

@[to_additive]
-/
theorem toSubgroup_injective : Function.Injective
    (ClosedSubgroup.toSubgroup : ClosedSubgroup G -> Subgroup G) :=
  fun A B h => by
  ext
  rw [h]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (ClosedSubgroup G) G
  body: U.1
coe_injective _ _ h := toSubgroup_injective SetLike.ext' h

中文:
实例 :
  签名: SetLike (ClosedSubgroup G) G
  定义体: U.1
coe_injective _ _ h := toSubgroup_injective SetLike.ext' h
-/
instance : SetLike (ClosedSubgroup G) G where
  coe U := U.1
coe_injective _ _ h := toSubgroup_injective SetLike.ext' h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (ClosedSubgroup G)
  body: .ofSetLike (ClosedSubgroup G) G

@[to_additive]

中文:
实例 :
  签名: PartialOrder (ClosedSubgroup G)
  定义体: .ofSetLike (ClosedSubgroup G) G

@[to_additive]
-/
@[to_additive] instance : PartialOrder (ClosedSubgroup G) := .ofSetLike (ClosedSubgroup G) G

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubgroupClass (ClosedSubgroup G) G
  body: Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]

中文:
实例 :
  签名: SubgroupClass (ClosedSubgroup G) G
  定义体: Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]

Depends on / 依赖: Subsemigroup, Subsemigroup.mul_mem, mul_mem
-/
instance : SubgroupClass (ClosedSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (ClosedSubgroup G) (Subgroup G)
  body: toSubgroup

@[to_additive]

中文:
实例 :
  签名: Coe (ClosedSubgroup G) (Subgroup G)
  定义体: toSubgroup

@[to_additive]

Depends on / 依赖: toSubgroup
-/
instance : Coe (ClosedSubgroup G) (Subgroup G) where
  coe := toSubgroup

@[to_additive]
/--
Instance `instInfClosedSubgroup` / 实例 `instInfClosedSubgroup`

English:
instance instInfClosedSubgroup
  signature: : Min (ClosedSubgroup G)
  body: ⟨fun U V => ⟨U ⊓ V, U.isClosed'.inter V.isClosed'⟩⟩

@[to_additive]

中文:
实例 instInfClosedSubgroup
  签名: : Min (ClosedSubgroup G)
  定义体: ⟨fun U V => ⟨U ⊓ V, U.isClosed'.inter V.isClosed'⟩⟩

@[to_additive]

Depends on / 依赖: U.isClosed, V.isClosed, isClosed
-/
instance instInfClosedSubgroup : Min (ClosedSubgroup G) :=
  ⟨fun U V => ⟨U ⊓ V, U.isClosed'.inter V.isClosed'⟩⟩

@[to_additive]
/--
Instance `instSemilatticeInfClosedSubgroup` / 实例 `instSemilatticeInfClosedSubgroup`

English:
instance instSemilatticeInfClosedSubgroup
  signature: : SemilatticeInf (ClosedSubgroup G)
  body: SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[to_additive]

中文:
实例 instSemilatticeInfClosedSubgroup
  签名: : SemilatticeInf (ClosedSubgroup G)
  定义体: SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[to_additive]

Depends on / 依赖: SetLike, SetLike.coe_injective.semilatticeInf, coe_injective, semilatticeInf
-/
instance instSemilatticeInfClosedSubgroup : SemilatticeInf (ClosedSubgroup G) :=
  SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: G] (H
  body: isCompact_iff_compactSpace.mp (IsClosed.isCompact H.isClosed')

中文:
实例 [CompactSpace
  签名: G] (H
  定义体: isCompact_iff_compactSpace.mp (IsClosed.isCompact H.isClosed')

Depends on / 依赖: H.isClosed, IsClosed, IsClosed.isCompact, isClosed, isCompact, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp
-/
instance [CompactSpace G] (H : ClosedSubgroup G) : CompactSpace H :=
  isCompact_iff_compactSpace.mp (IsClosed.isCompact H.isClosed')

end ClosedSubgroup

open scoped Pointwise

namespace Subgroup

variable {G : Type u} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

@[to_additive]
/--
lemma `normalCore_isClosed` / 引理 `normalCore_isClosed`

English:
lemma normalCore_isClosed
  given: (H : Subgroup G) (h : IsClosed (H : Set G))
  proof: by
  rw [normalCore_eq_iInf_comap_conj]
  push_cast
  apply isClosed_iInter
  intro g
  exact h.preimage (IsTopologicalGroup.continuous_conj g)

@[to_additive]

中文:
引理 normalCore_isClosed
  条件: (H : Subgroup G) (h : IsClosed (H : Set G))
  证明: by
  rw [normalCore_eq_iInf_comap_conj]
  push_cast
  apply isClosed_iInter
  intro g
  exact h.preimage (IsTopologicalGroup.continuous_conj g)

@[to_additive]

Depends on / 依赖: IsTopologicalGroup, IsTopologicalGroup.continuous_conj, continuous_conj, h.preimage, isClosed_iInter, normalCore_eq_iInf_comap_conj, preimage
-/
lemma normalCore_isClosed (H : Subgroup G) (h : IsClosed (H : Set G)) :
    IsClosed (H.normalCore : Set G) := by
  rw [normalCore_eq_iInf_comap_conj]
  push_cast
  apply isClosed_iInter
  intro g
  exact h.preimage (IsTopologicalGroup.continuous_conj g)

@[to_additive]
/--
lemma `isOpen_of_isClosed_of_finiteIndex` / 引理 `isOpen_of_isClosed_of_finiteIndex`

English:
lemma isOpen_of_isClosed_of_finiteIndex
  statement: (H : Subgroup G) [H.FiniteIndex]
  proof: by
  rw [← QuotientGroup.t1Space_iff] at h
  rw [← QuotientGroup.discreteTopology_iff]
  infer_instance

中文:
引理 isOpen_of_isClosed_of_finiteIndex
  结论: (H : Subgroup G) [H.FiniteIndex]
  证明: by
  rw [← QuotientGroup.t1Space_iff] at h
  rw [← QuotientGroup.discreteTopology_iff]
  infer_instance

Depends on / 依赖: QuotientGroup, QuotientGroup.discreteTopology_iff, QuotientGroup.t1Space_iff, discreteTopology_iff, infer_instance, t1Space_iff
-/
lemma isOpen_of_isClosed_of_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (h : IsClosed (H : Set G)) : IsOpen (H : Set G) := by
  rw [← QuotientGroup.t1Space_iff] at h
  rw [← QuotientGroup.discreteTopology_iff]
  infer_instance

end Subgroup

end
