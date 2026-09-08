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
/-
**ClosedSubgroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u) → [Group G] → [TopologicalSpace G] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of closed subgroups of a topological group.
-/
structure ClosedSubgroup (G : Type u) [Group G] [TopologicalSpace G] extends Subgroup G where
  isClosed' : IsClosed carrier

/-- The type of closed subgroups of an additive topological group. -/
@[ext]
/-
**ClosedAddSubgroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u) → [AddGroup G] → [TopologicalSpace G] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of closed subgroups of an additive topological group.
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
/-
**ClosedSubgroup.toSubgroup_injective** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubgroup`
。
形式化陈述：toSubgroup_injective : Function.Injective (ClosedSubgroup.toSubgroup : Clo
sedSubgroup G -> Subgroup G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubgroup.ext`：∀ {G : Type u} {inst : Group G} {inst_1 : Topologica
lSpace G} {x y : ClosedSubgroup G},   (↑x).carrier = (↑y).carrier → x = y
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubgroup_injective : Function.Injective
    (ClosedSubgroup.toSubgroup : ClosedSubgroup G → Subgroup G) :=
  fun A B h ↦ by
  ext
  rw [h]

@[to_additive]
/-
**ClosedSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (ClosedSubgroup G) G where
  coe U := U.1
  coe_injective _ _ h := toSubgroup_injective <| SetLike.ext' h
/-
**ClosedSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : PartialOrder (ClosedSubgroup G) := .ofSetLike (ClosedSubgroup G) G

@[to_additive]
/-
**ClosedSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubgroupClass (ClosedSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]
/-
**ClosedSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (ClosedSubgroup G) (Subgroup G) where
  coe := toSubgroup

@[to_additive]
/-
**ClosedSubgroup.instInfClosedSubgroup** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubgroup
`。
形式化陈述：instInfClosedSubgroup : Min (ClosedSubgroup G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInfClosedSubgroup : Min (ClosedSubgroup G) :=
  ⟨fun U V ↦ ⟨U ⊓ V, U.isClosed'.inter V.isClosed'⟩⟩

@[to_additive]
/-
**ClosedSubgroup.instSemilatticeInfClosedSubgroup** 是 Mathlib 中的一个实例，位于命名空间 `Clo
sedSubgroup`。
形式化陈述：instSemilatticeInfClosedSubgroup : SemilatticeInf (ClosedSubgroup G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeInfClosedSubgroup : SemilatticeInf (ClosedSubgroup G) :=
  SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl

@[to_additive]
/-
**ClosedSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace G] (H : ClosedSubgroup G) : CompactSpace H :=
  isCompact_iff_compactSpace.mp (IsClosed.isCompact H.isClosed')

end ClosedSubgroup

open scoped Pointwise

namespace Subgroup

variable {G : Type u} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

@[to_additive]
/-
**Subgroup.normalCore_isClosed** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：normalCore_isClosed (H : Subgroup G) (h : IsClosed (H : Set G)) : IsClosed
 (H.normalCore : Set G)
参数：H : Subgroup G；h : IsClosed (H : Set G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.normalCore_eq_iInf_comap_conj`：normalCore_eq_iInf_comap_conj (H
 : Subgroup G) : H.normalCore = ⨅ g : G, H.comap (MulAut.conj g)
· 使用定理 `Subgroup.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> Subgroup G} : (↑(⨅ i, 
S i) : Set G) = ⋂ i, S i
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `IsTopologicalGroup.continuous_conj`：IsTopologicalGroup.continuous_conj [
SeparatelyContinuousMul G] (g : G) : Continuous fun h : G => g * h * g⁻¹
-/
lemma normalCore_isClosed (H : Subgroup G) (h : IsClosed (H : Set G)) :
    IsClosed (H.normalCore : Set G) := by
  rw [normalCore_eq_iInf_comap_conj]
  push_cast
  apply isClosed_iInter
  intro g
  exact h.preimage (IsTopologicalGroup.continuous_conj g)

@[to_additive]
/-
**Subgroup.isOpen_of_isClosed_of_finiteIndex** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup
`。
形式化陈述：isOpen_of_isClosed_of_finiteIndex (H : Subgroup G) [H.FiniteIndex] (h : Is
Closed (H : Set G)) : IsOpen (H : Set G)
参数：H : Subgroup G；h : IsClosed (H : Set G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientGroup.discreteTopology_iff`：discreteTopology_iff : DiscreteTopol
ogy (G ⧸ N) ↔ IsOpen (N : Set G)
· 使用定理 `QuotientGroup.t1Space_iff`：t1Space_iff : T1Space (G ⧸ N) ↔ IsClosed (N :
 Set G)
-/
lemma isOpen_of_isClosed_of_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (h : IsClosed (H : Set G)) : IsOpen (H : Set G) := by
  rw [← QuotientGroup.t1Space_iff] at h
  rw [← QuotientGroup.discreteTopology_iff]
  infer_instance

end Subgroup

end

