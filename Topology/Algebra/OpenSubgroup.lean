/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Nailin Guan, Yi Song, Xuchun Li
-/
module

public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Sets.Opens

/-!
# Open subgroups of a topological group

This file builds the lattice `OpenSubgroup G` of open subgroups in a topological group `G`,
and its additive version `OpenAddSubgroup`. This lattice has a top element, the subgroup of all
elements, but no bottom element in general. The trivial subgroup which is the natural candidate
bottom has no reason to be open (this happens only in discrete groups).

Note that this notion is especially relevant in a non-archimedean context, for instance for
`p`-adic groups.

## Main declarations

* `OpenSubgroup.isClosed`: An open subgroup is automatically closed.
* `Subgroup.isOpen_mono`: A subgroup containing an open subgroup is open.
                           There are also versions for additive groups, submodules and ideals.
* `OpenSubgroup.comap`: Open subgroups can be pulled back by a continuous group morphism.

## TODO
* Prove that the identity component of a locally path connected group is an open subgroup.
  Up to now this file is really geared towards non-archimedean algebra, not Lie groups.
-/

@[expose] public section


open TopologicalSpace Topology Function

/-- The type of open subgroups of a topological additive group. -/
/-
**OpenAddSubgroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → [AddGroup G] → [TopologicalSpace G] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of open subgroups of a topological additive group.
-/
structure OpenAddSubgroup (G : Type*) [AddGroup G] [TopologicalSpace G] extends AddSubgroup G where
  isOpen' : IsOpen carrier

/-- The type of open subgroups of a topological group. -/
@[to_additive]
/-
**OpenSubgroup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → [Group G] → [TopologicalSpace G] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of open subgroups of a topological group.
-/
structure OpenSubgroup (G : Type*) [Group G] [TopologicalSpace G] extends Subgroup G where
  isOpen' : IsOpen carrier

/-- Reinterpret an `OpenSubgroup` as a `Subgroup`. -/
add_decl_doc OpenSubgroup.toSubgroup

/-- Reinterpret an `OpenAddSubgroup` as an `AddSubgroup`. -/
add_decl_doc OpenAddSubgroup.toAddSubgroup

attribute [coe] OpenSubgroup.toSubgroup OpenAddSubgroup.toAddSubgroup

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {U V : OpenSubgroup G} {g : G}

@[to_additive]
/-
**OpenSubgroup.hasCoeSubgroup** 是 Mathlib 中的一个实例，位于命名空间 `OpenSubgroup`。
形式化陈述：hasCoeSubgroup : CoeTC (OpenSubgroup G) (Subgroup G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeSubgroup : CoeTC (OpenSubgroup G) (Subgroup G) :=
  ⟨toSubgroup⟩

@[to_additive]
/-
**OpenSubgroup.toSubgroup_injective** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G], Function.
Injective OpenSubgroup.toSubgroup
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubgroup_injective : Injective ((↑) : OpenSubgroup G → Subgroup G)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[to_additive]
/-
**OpenSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `OpenSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (OpenSubgroup G) G where
  coe U := U.1
  coe_injective _ _ h := toSubgroup_injective <| SetLike.ext' h
/-
**OpenSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `OpenSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : PartialOrder (OpenSubgroup G) := .ofSetLike (OpenSubgroup G) G

@[to_additive]
/-
**OpenSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `OpenSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubgroupClass (OpenSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

/-- Coercion from `OpenSubgroup G` to `Opens G`. -/
@[to_additive (attr := coe) /-- Coercion from `OpenAddSubgroup G` to `Opens G`. -/]
/-
**OpenSubgroup.toOpens** 是 Mathlib 中的一个定义，位于命名空间 `OpenSubgroup`。
形式化陈述：toOpens (U : OpenSubgroup G) : Opens G
参数：U : OpenSubgroup G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OpenSubgroup.isOpen'`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Topolo
gicalSpace G] (self : OpenSubgroup G), IsOpen (↑self).carrier

--- 原说明 ---
Coercion from `OpenSubgroup G` to `Opens G`.
-/
def toOpens (U : OpenSubgroup G) : Opens G := ⟨U, U.isOpen'⟩

@[to_additive]
/-
**OpenSubgroup.hasCoeOpens** 是 Mathlib 中的一个实例，位于命名空间 `OpenSubgroup`。
形式化陈述：hasCoeOpens : CoeTC (OpenSubgroup G) (Opens G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeOpens : CoeTC (OpenSubgroup G) (Opens G) := ⟨toOpens⟩

@[to_additive (attr := simp, norm_cast)]
/-
**OpenSubgroup.coe_toOpens** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：coe_toOpens : ((U : Opens G) : Set G) = U
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toOpens : ((U : Opens G) : Set G) = U :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**OpenSubgroup.coe_toSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：coe_toSubgroup : ((U : Subgroup G) : Set G) = U
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubgroup : ((U : Subgroup G) : Set G) = U := rfl

@[to_additive (attr := simp, norm_cast)]
/-
**OpenSubgroup.mem_toOpens** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：mem_toOpens : g in (U : Opens G) ↔ g in U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toOpens : g ∈ (U : Opens G) ↔ g ∈ U := Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/-
**OpenSubgroup.mem_toSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：mem_toSubgroup : g in (U : Subgroup G) ↔ g in U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubgroup : g ∈ (U : Subgroup G) ↔ g ∈ U := Iff.rfl

@[to_additive (attr := ext)]
/-
**OpenSubgroup.ext** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：ext (h : forall x, x in U ↔ x in V) : U = V
参数：h : forall x, x in U ↔ x in V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext (h : ∀ x, x ∈ U ↔ x ∈ V) : U = V :=
  SetLike.ext h

variable (U)

@[to_additive]
/-
**OpenSubgroup.isOpen** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G] (U : OpenS
ubgroup G), IsOpen ↑U
参数：U : OpenSubgroup G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenSubgroup.isOpen'`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Topolo
gicalSpace G] (self : OpenSubgroup G), IsOpen (↑self).carrier
-/
protected theorem isOpen : IsOpen (U : Set G) :=
  U.isOpen'

@[to_additive]
/-
**OpenSubgroup.mem_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：mem_nhds_one : (U : Set G) in 𝓝 (1 : G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenSubgroup.isOpen`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Topolog
icalSpace G] (U : OpenSubgroup G), IsOpen ↑U
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
-/
theorem mem_nhds_one : (U : Set G) ∈ 𝓝 (1 : G) :=
  U.isOpen.mem_nhds U.one_mem

variable {U}
/-
**OpenSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `OpenSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : Top (OpenSubgroup G) := ⟨⟨⊤, isOpen_univ⟩⟩

@[to_additive (attr := simp)]
/-
**OpenSubgroup.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：mem_top (x : G) : x in (⊤ : OpenSubgroup G)
参数：x : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem mem_top (x : G) : x ∈ (⊤ : OpenSubgroup G) :=
  trivial

@[to_additive (attr := simp, norm_cast)]
/-
**OpenSubgroup.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：coe_top : ((⊤ : OpenSubgroup G) : Set G) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ((⊤ : OpenSubgroup G) : Set G) = Set.univ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**OpenSubgroup.toSubgroup_top** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：toSubgroup_top : ((⊤ : OpenSubgroup G) : Subgroup G) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubgroup_top : ((⊤ : OpenSubgroup G) : Subgroup G) = ⊤ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**OpenSubgroup.toOpens_top** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：toOpens_top : ((⊤ : OpenSubgroup G) : Opens G) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOpens_top : ((⊤ : OpenSubgroup G) : Opens G) = ⊤ :=
  rfl

@[to_additive]
/-
**OpenSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `OpenSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (OpenSubgroup G) :=
  ⟨⊤⟩

@[to_additive]
/-
**OpenSubgroup.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：isClosed [SeparatelyContinuousMul G] (U : OpenSubgroup G) : IsClosed (U : 
Set G)
参数：U : OpenSubgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.discreteTopology`：discreteTopology (hN : IsOpen (N : Set G
)) : DiscreteTopology (G ⧸ N)
· 使用定理 `OpenSubgroup.isOpen`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Topolog
icalSpace G] (U : OpenSubgroup G), IsOpen ↑U
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `QuotientGroup.t1Space_iff`：t1Space_iff : T1Space (G ⧸ N) ↔ IsClosed (N :
 Set G)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X
-/
theorem isClosed [SeparatelyContinuousMul G] (U : OpenSubgroup G) : IsClosed (U : Set G) := by
  have := QuotientGroup.discreteTopology U.isOpen
  exact QuotientGroup.t1Space_iff.mp inferInstance

@[to_additive]
/-
**OpenSubgroup.isClopen** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：isClopen [SeparatelyContinuousMul G] (U : OpenSubgroup G) : IsClopen (U : 
Set G)
参数：U : OpenSubgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenSubgroup.isClosed`：isClosed [SeparatelyContinuousMul G] (U : OpenSub
group G) : IsClosed (U : Set G)
· 使用定理 `OpenSubgroup.isOpen`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Topolog
icalSpace G] (U : OpenSubgroup G), IsOpen ↑U
-/
theorem isClopen [SeparatelyContinuousMul G] (U : OpenSubgroup G) : IsClopen (U : Set G) :=
  ⟨U.isClosed, U.isOpen⟩

section

variable {H : Type*} [Group H] [TopologicalSpace H]

/-- The product of two open subgroups as an open subgroup of the product group. -/
@[to_additive prod
/-- The product of two open subgroups as an open subgroup of the product group. -/]
/-
**OpenSubgroup.prod** 是 Mathlib 中的一个定义，位于命名空间 `OpenSubgroup`。
形式化陈述：prod (U : OpenSubgroup G) (V : OpenSubgroup H) : OpenSubgroup (G × H)
参数：U : OpenSubgroup G；V : OpenSubgroup H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prod (U : OpenSubgroup G) (V : OpenSubgroup H) : OpenSubgroup (G × H) :=
  ⟨.prod U V, U.isOpen.prod V.isOpen⟩

@[to_additive (attr := simp, norm_cast) coe_prod]
/-
**OpenSubgroup.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：coe_prod (U : OpenSubgroup G) (V : OpenSubgroup H) : (U.prod V : Set (G × 
H)) = (U : Set G) ×ˢ (V : Set H)
参数：U : OpenSubgroup G；V : OpenSubgroup H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (U : OpenSubgroup G) (V : OpenSubgroup H) :
    (U.prod V : Set (G × H)) = (U : Set G) ×ˢ (V : Set H) :=
  rfl

@[to_additive (attr := simp, norm_cast) toAddSubgroup_prod]
/-
**OpenSubgroup.toSubgroup_prod** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：toSubgroup_prod (U : OpenSubgroup G) (V : OpenSubgroup H) : (U.prod V : Su
bgroup (G × H)) = (U : Subgroup G).prod V
参数：U : OpenSubgroup G；V : OpenSubgroup H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubgroup_prod (U : OpenSubgroup G) (V : OpenSubgroup H) :
    (U.prod V : Subgroup (G × H)) = (U : Subgroup G).prod V :=
  rfl

end

@[to_additive]
/-
**OpenSubgroup.instInfOpenSubgroup** 是 Mathlib 中的一个实例，位于命名空间 `OpenSubgroup`。
形式化陈述：instInfOpenSubgroup : Min (OpenSubgroup G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInfOpenSubgroup : Min (OpenSubgroup G) :=
  ⟨fun U V ↦ ⟨U ⊓ V, U.isOpen.inter V.isOpen⟩⟩

@[to_additive (attr := simp, norm_cast)]
/-
**OpenSubgroup.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：coe_inf : (↑(U ⊓ V) : Set G) = (U : Set G) inter V
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf : (↑(U ⊓ V) : Set G) = (U : Set G) ∩ V :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**OpenSubgroup.toSubgroup_inf** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：toSubgroup_inf : (↑(U ⊓ V) : Subgroup G) = ↑U ⊓ ↑V
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubgroup_inf : (↑(U ⊓ V) : Subgroup G) = ↑U ⊓ ↑V :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**OpenSubgroup.toOpens_inf** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：toOpens_inf : (↑(U ⊓ V) : Opens G) = ↑U ⊓ ↑V
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOpens_inf : (↑(U ⊓ V) : Opens G) = ↑U ⊓ ↑V :=
  rfl

@[to_additive (attr := simp)]
/-
**OpenSubgroup.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：mem_inf {x} : x in U ⊓ V ↔ x in U ∧ x in V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf {x} : x ∈ U ⊓ V ↔ x ∈ U ∧ x ∈ V :=
  Iff.rfl

@[to_additive]
/-
**OpenSubgroup.instPartialOrderOpenSubgroup** 是 Mathlib 中的一个实例，位于命名空间 `OpenSubgr
oup`。
形式化陈述：instPartialOrderOpenSubgroup : PartialOrder (OpenSubgroup G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrderOpenSubgroup : PartialOrder (OpenSubgroup G) := inferInstance

-- We override `toPartialorder` to get better `le`
@[to_additive]
/-
**OpenSubgroup.instSemilatticeInfOpenSubgroup** 是 Mathlib 中的一个实例，位于命名空间 `OpenSub
group`。
形式化陈述：instSemilatticeInfOpenSubgroup : SemilatticeInf (OpenSubgroup G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeInfOpenSubgroup : SemilatticeInf (OpenSubgroup G) :=
  SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl

@[to_additive]
/-
**OpenSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `OpenSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTop (OpenSubgroup G) where
  le_top _ := Set.subset_univ _

@[to_additive (attr := simp, norm_cast)]
/-
**OpenSubgroup.toSubgroup_le** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：toSubgroup_le : (U : Subgroup G) <= (V : Subgroup G) ↔ U <= V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubgroup_le : (U : Subgroup G) ≤ (V : Subgroup G) ↔ U ≤ V :=
  Iff.rfl

variable {N : Type*} [Group N] [TopologicalSpace N]

/-- The preimage of an `OpenSubgroup` along a continuous `Monoid` homomorphism
  is an `OpenSubgroup`. -/
@[to_additive /-- The preimage of an `OpenAddSubgroup` along a continuous `AddMonoid` homomorphism
is an `OpenAddSubgroup`. -/]
/-
**OpenSubgroup.comap** 是 Mathlib 中的一个定义，位于命名空间 `OpenSubgroup`。
形式化陈述：comap (f : G ->* N) (hf : Continuous f) (H : OpenSubgroup N) : OpenSubgrou
p G
参数：f : G ->* N；hf : Continuous f；H : OpenSubgroup N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def comap (f : G →* N) (hf : Continuous f) (H : OpenSubgroup N) : OpenSubgroup G :=
  ⟨.comap f H, H.isOpen.preimage hf⟩

@[to_additive (attr := simp, norm_cast)]
/-
**OpenSubgroup.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：coe_comap (H : OpenSubgroup N) (f : G ->* N) (hf : Continuous f) : (H.coma
p f hf : Set G) = f ⁻¹' H
参数：H : OpenSubgroup N；f : G ->* N；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap (H : OpenSubgroup N) (f : G →* N) (hf : Continuous f) :
    (H.comap f hf : Set G) = f ⁻¹' H :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**OpenSubgroup.toSubgroup_comap** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：toSubgroup_comap (H : OpenSubgroup N) (f : G ->* N) (hf : Continuous f) : 
(H.comap f hf : Subgroup G) = (H : Subgroup N).comap f
参数：H : OpenSubgroup N；f : G ->* N；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubgroup_comap (H : OpenSubgroup N) (f : G →* N) (hf : Continuous f) :
    (H.comap f hf : Subgroup G) = (H : Subgroup N).comap f :=
  rfl

@[to_additive (attr := simp)]
/-
**OpenSubgroup.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：mem_comap {H : OpenSubgroup N} {f : G ->* N} {hf : Continuous f} {x : G} :
 x in H.comap f hf ↔ f x in H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {H : OpenSubgroup N} {f : G →* N} {hf : Continuous f} {x : G} :
    x ∈ H.comap f hf ↔ f x ∈ H :=
  Iff.rfl

@[to_additive]
/-
**OpenSubgroup.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：comap_comap {P : Type*} [Group P] [TopologicalSpace P] (K : OpenSubgroup P
) (f₂ : N ->* P) (hf₂ : Continuous f₂) (f₁ : G ->* N) (hf₁ : Continuous f₁) : (K
.comap f₂ hf₂).comap f₁ hf₁ = K.comap (f₂.comp f₁) (hf₂.comp hf₁)
参数：K : OpenSubgroup P；f₂ : N ->* P；hf₂ : Continuous f₂；f₁ : G ->* N；hf₁ : Contin
uous f₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comap {P : Type*} [Group P] [TopologicalSpace P] (K : OpenSubgroup P) (f₂ : N →* P)
    (hf₂ : Continuous f₂) (f₁ : G →* N) (hf₁ : Continuous f₁) :
    (K.comap f₂ hf₂).comap f₁ hf₁ = K.comap (f₂.comp f₁) (hf₂.comp hf₁) :=
  rfl

end OpenSubgroup
namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

@[to_additive]
/-
**Subgroup.isOpen_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：isOpen_of_mem_nhds [SeparatelyContinuousMul G] (H : Subgroup G) {g : G} (h
g : (H : Set G) in 𝓝 g) : IsOpen (H : Set G)
参数：H : Subgroup G；hg : (H : Set G) in 𝓝 g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.mul_const`：Continuous.mul_const (hf : Continuous f) (b : M) :
 Continuous (f · * b)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subgroup.mul_mem_cancel_right`：∀ {G : Type u_1} [inst : Group G] (H : Su
bgroup G) {x y : G}, x ∈ H → (y * x ∈ H ↔ y ∈ H)
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
-/
theorem isOpen_of_mem_nhds [SeparatelyContinuousMul G] (H : Subgroup G) {g : G}
    (hg : (H : Set G) ∈ 𝓝 g) : IsOpen (H : Set G) := by
  refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
  have hg' : g ∈ H := SetLike.mem_coe.1 (mem_of_mem_nhds hg)
  have : Filter.Tendsto (fun y ↦ y * (x⁻¹ * g)) (𝓝 x) (𝓝 g) :=
    (continuous_id.mul_const _).tendsto' _ _ (mul_inv_cancel_left _ _)
  simpa only [SetLike.mem_coe, Filter.mem_map',
    H.mul_mem_cancel_right (H.mul_mem (H.inv_mem hx) hg')] using! this hg

@[to_additive]
/-
**Subgroup.isOpen_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：isOpen_mono [SeparatelyContinuousMul G] {H₁ H₂ : Subgroup G} (h : H₁ <= H₂
) (h₁ : IsOpen (H₁ : Set G)) : IsOpen (H₂ : Set G)
参数：h : H₁ <= H₂；h₁ : IsOpen (H₁ : Set G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.isOpen_of_mem_nhds`：isOpen_of_mem_nhds [SeparatelyContinuousMul
 G] (H : Subgroup G) {g : G} (hg : (H : Set G) in 𝓝 g) : IsOpen (H : Set G)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem isOpen_mono [SeparatelyContinuousMul G] {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂)
    (h₁ : IsOpen (H₁ : Set G)) : IsOpen (H₂ : Set G) :=
  isOpen_of_mem_nhds _ <| Filter.mem_of_superset (h₁.mem_nhds <| one_mem H₁) h

@[to_additive]
/-
**Subgroup.isOpen_of_openSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：isOpen_of_openSubgroup [SeparatelyContinuousMul G] (H : Subgroup G) {U : O
penSubgroup G} (h : ↑U <= H) : IsOpen (H : Set G)
参数：H : Subgroup G；h : ↑U <= H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.isOpen_mono`：isOpen_mono [SeparatelyContinuousMul G] {H₁ H₂ : S
ubgroup G} (h : H₁ <= H₂) (h₁ : IsOpen (H₁ : Set G)) : IsOpen (H₂ : Set G)
· 使用定理 `OpenSubgroup.isOpen`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Topolog
icalSpace G] (U : OpenSubgroup G), IsOpen ↑U
-/
theorem isOpen_of_openSubgroup
    [SeparatelyContinuousMul G] (H : Subgroup G) {U : OpenSubgroup G} (h : ↑U ≤ H) :
    IsOpen (H : Set G) :=
  isOpen_mono h U.isOpen

/-- If a subgroup of a topological group has `1` in its interior, then it is open. -/
@[to_additive /-- If a subgroup of an additive topological group has `0` in its interior, then it is
open. -/]
/-
**Subgroup.isOpen_of_one_mem_interior** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：isOpen_of_one_mem_interior [SeparatelyContinuousMul G] (H : Subgroup G) (h
_1_int : (1 : G) in interior (H : Set G)) : IsOpen (H : Set G)
参数：H : Subgroup G；h_1_int : (1 : G) in interior (H : Set G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.isOpen_of_mem_nhds`：isOpen_of_mem_nhds [SeparatelyContinuousMul
 G] (H : Subgroup G) {g : G} (hg : (H : Set G) in 𝓝 g) : IsOpen (H : Set G)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
-/
theorem isOpen_of_one_mem_interior [SeparatelyContinuousMul G] (H : Subgroup G)
    (h_1_int : (1 : G) ∈ interior (H : Set G)) : IsOpen (H : Set G) :=
  isOpen_of_mem_nhds H <| mem_interior_iff_mem_nhds.1 h_1_int

@[to_additive]
/-
**Subgroup.isClosed_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：isClosed_of_isOpen [SeparatelyContinuousMul G] (U : Subgroup G) (h : IsOpe
n (U : Set G)) : IsClosed (U : Set G)
参数：U : Subgroup G；h : IsOpen (U : Set G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenSubgroup.isClosed`：isClosed [SeparatelyContinuousMul G] (U : OpenSub
group G) : IsClosed (U : Set G)
-/
lemma isClosed_of_isOpen [SeparatelyContinuousMul G] (U : Subgroup G) (h : IsOpen (U : Set G)) :
    IsClosed (U : Set G) :=
  OpenSubgroup.isClosed ⟨U, h⟩

@[to_additive]
/-
**Subgroup.subgroupOf_isOpen** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：subgroupOf_isOpen (U K : Subgroup G) (h : IsOpen (K : Set G)) : IsOpen (K.
subgroupOf U : Set U)
参数：U K : Subgroup G；h : IsOpen (K : Set G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_le_induced`：continuous_iff_le_induced {t₁ : TopologicalSp
ace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ t₁ <= induced f t₂
-/
lemma subgroupOf_isOpen (U K : Subgroup G) (h : IsOpen (K : Set G)) :
    IsOpen (K.subgroupOf U : Set U) :=
  Continuous.isOpen_preimage (continuous_iff_le_induced.mpr fun _ ↦ id) _ h

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SeparatelyContinuousMul G] (U : OpenSubgroup G) : DiscreteTopology (G ⧸ U.toSubgroup) :=
  QuotientGroup.discreteTopology U.isOpen

@[to_additive]
/-
**Subgroup.quotient_finite_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：quotient_finite_of_isOpen [SeparatelyContinuousMul G] [CompactSpace G] (U 
: Subgroup G) (h : IsOpen (U : Set G)) : Finite (G ⧸ U)
参数：U : Subgroup G；h : IsOpen (U : Set G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.discreteTopology`：discreteTopology (hN : IsOpen (N : Set G
)) : DiscreteTopology (G ⧸ N)
· 使用定理 `finite_of_compact_of_discrete`：finite_of_compact_of_discrete [CompactSpa
ce X] [DiscreteTopology X] : Finite X
· 使用定理 `QuotientGroup.instCompactSpaceQuotientSubgroup`：∀ {G : Type u_1} [inst :
 TopologicalSpace G] [inst_1 : Group G] [CompactSpace G] (N : Subgroup G), Compa
ctSpace (G ⧸ N)
-/
lemma quotient_finite_of_isOpen [SeparatelyContinuousMul G] [CompactSpace G] (U : Subgroup G)
    (h : IsOpen (U : Set G)) : Finite (G ⧸ U) :=
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology h
  finite_of_compact_of_discrete

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SeparatelyContinuousMul G] [CompactSpace G] (U : OpenSubgroup G) :
    Finite (G ⧸ U.toSubgroup) :=
  quotient_finite_of_isOpen U.toSubgroup U.isOpen

@[to_additive]
/-
**Subgroup.quotient_finite_of_isOpen'** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：quotient_finite_of_isOpen' [IsTopologicalGroup G] [CompactSpace G] (U : Su
bgroup G) (K : Subgroup U) (hUopen : IsOpen (U : Set G)) (hKopen : IsOpen (K : S
et U)) : Finite (U ⧸ K)
参数：U : Subgroup G；K : Subgroup U；hUopen : IsOpen (U : Set G)；hKopen : IsOpen (K 
: Set U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用引理 `Subgroup.isClosed_of_isOpen`：isClosed_of_isOpen [SeparatelyContinuousMul
 G] (U : Subgroup G) (h : IsOpen (U : Set G)) : IsClosed (U : Set G)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用引理 `Subgroup.quotient_finite_of_isOpen`：quotient_finite_of_isOpen [Separatel
yContinuousMul G] [CompactSpace G] (U : Subgroup G) (h : IsOpen (U : Set G)) : F
inite (G ⧸ U)
· 使用定理 `Subgroup.instIsTopologicalGroupSubtypeMem`：∀ {G : Type w} [inst : Topolo
gicalSpace G] [inst_1 : Group G] [IsTopologicalGroup G] (S : Subgroup G),   IsTo
pologicalGroup ↥S
-/
lemma quotient_finite_of_isOpen' [IsTopologicalGroup G] [CompactSpace G] (U : Subgroup G)
    (K : Subgroup U) (hUopen : IsOpen (U : Set G)) (hKopen : IsOpen (K : Set U)) :
    Finite (U ⧸ K) :=
  have : CompactSpace U := isCompact_iff_compactSpace.mp <| IsClosed.isCompact <|
    U.isClosed_of_isOpen hUopen
  K.quotient_finite_of_isOpen hKopen

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTopologicalGroup G] [CompactSpace G] (U : OpenSubgroup G) (K : OpenSubgroup U) :
    Finite (U ⧸ K.toSubgroup) :=
  quotient_finite_of_isOpen' U.toSubgroup K.toSubgroup U.isOpen K.isOpen

end Subgroup

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

@[to_additive]
/-
**OpenSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `OpenSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (OpenSubgroup G) :=
  ⟨fun U V ↦ ⟨U ⊔ V, Subgroup.isOpen_mono (le_sup_left : U.1 ≤ U.1 ⊔ V.1) U.isOpen⟩⟩

@[to_additive (attr := simp, norm_cast)]
/-
**OpenSubgroup.toSubgroup_sup** 是 Mathlib 中的一个定理，位于命名空间 `OpenSubgroup`。
形式化陈述：toSubgroup_sup (U V : OpenSubgroup G) : (↑(U ⊔ V) : Subgroup G) = ↑U ⊔ ↑V
参数：U V : OpenSubgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubgroup_sup (U V : OpenSubgroup G) : (↑(U ⊔ V) : Subgroup G) = ↑U ⊔ ↑V := rfl

@[to_additive]
/-
**OpenSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `OpenSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Lattice (OpenSubgroup G) where
  __ := toSubgroup_injective.semilatticeSup _ .rfl .rfl fun _ _ ↦ rfl
  __ := instSemilatticeInfOpenSubgroup

end OpenSubgroup

namespace Submodule

open OpenAddSubgroup

variable {R : Type*} {M : Type*} [CommRing R]
variable [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [Module R M]

/-
**Submodule.isOpen_mono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isOpen_mono {U P : Submodule R M} (h : U <= P) (hU : IsOpen (U : Set M)) :
 IsOpen (P : Set M)
参数：h : U <= P；hU : IsOpen (U : Set M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.isOpen_mono`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1 : 
TopologicalSpace G] [SeparatelyContinuousAdd G] {H₁ H₂ : AddSubgroup G},   H₁ ≤ 
H₂ → IsOpen ↑…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem isOpen_mono {U P : Submodule R M} (h : U ≤ P) (hU : IsOpen (U : Set M)) :
    IsOpen (P : Set M) :=
  @AddSubgroup.isOpen_mono M _ _ _ U.toAddSubgroup P.toAddSubgroup h hU

end Submodule

namespace Ideal

variable {R : Type*} [CommRing R]
variable [TopologicalSpace R] [IsTopologicalRing R]

/-
**Ideal.isOpen_of_isOpen_subideal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isOpen_of_isOpen_subideal {U I : Ideal R} (h : U <= I) (hU : IsOpen (U : S
et R)) : IsOpen (I : Set R)
参数：h : U <= I；hU : IsOpen (U : Set R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.isOpen_mono`：isOpen_mono {U P : Submodule R M} (h : U <= P) (h
U : IsOpen (U : Set M)) : IsOpen (P : Set M)
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
-/
theorem isOpen_of_isOpen_subideal {U I : Ideal R} (h : U ≤ I) (hU : IsOpen (U : Set R)) :
    IsOpen (I : Set R) :=
  @Submodule.isOpen_mono R R _ _ _ _ Semiring.toModule _ _ h hU

end Ideal

/-!
### Open normal subgroups of a topological group

This section builds the lattice `OpenNormalSubgroup G` of open subgroups in a topological group `G`,
and its additive version `OpenNormalAddSubgroup`.

-/

section

universe u

/-- The type of open normal subgroups of a topological group. -/
@[ext]
/-
**OpenNormalSubgroup** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：OpenNormalSubgroup (G : Type u) [Group G] [TopologicalSpace G] extends Ope
nSubgroup G where isNormal' : toSubgroup.Normal
参数：G : Type u。
继承自：OpenSubgroup G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of open normal subgroups of a topological group.
-/
structure OpenNormalSubgroup (G : Type u) [Group G] [TopologicalSpace G]
  extends OpenSubgroup G where
  isNormal' : toSubgroup.Normal := by infer_instance

/-- The type of open normal subgroups of a topological additive group. -/
@[ext]
/-
**OpenNormalAddSubgroup** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：OpenNormalAddSubgroup (G : Type u) [AddGroup G] [TopologicalSpace G] exten
ds OpenAddSubgroup G where isNormal' : toAddSubgroup.Normal
参数：G : Type u。
继承自：OpenAddSubgroup G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of open normal subgroups of a topological additive group.
-/
structure OpenNormalAddSubgroup (G : Type u) [AddGroup G] [TopologicalSpace G]
  extends OpenAddSubgroup G where
  isNormal' : toAddSubgroup.Normal := by infer_instance

attribute [to_additive] OpenNormalSubgroup

namespace OpenNormalSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G]

@[to_additive]
/-
**OpenNormalSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `OpenNormalSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (H : OpenNormalSubgroup G) : H.toSubgroup.Normal := H.isNormal'

@[to_additive]
/-
**OpenNormalSubgroup.toSubgroup_injective** 是 Mathlib 中的一个定理，位于命名空间 `OpenNormalS
ubgroup`。
形式化陈述：toSubgroup_injective : Function.Injective (fun H => H.toOpenSubgroup.toSub
group : OpenNormalSubgroup G -> Subgroup G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenNormalSubgroup.ext`：∀ {G : Type u} {inst : Group G} {inst_1 : Topolo
gicalSpace G} {x y : OpenNormalSubgroup G},   (↑x.toOpenSubgroup).carrier = (↑y.
toOpenSubgro…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubgroup_injective : Function.Injective
    (fun H ↦ H.toOpenSubgroup.toSubgroup : OpenNormalSubgroup G → Subgroup G) :=
  fun A B h ↦ by
  ext
  dsimp at h
  rw [h]

@[to_additive]
/-
**OpenNormalSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `OpenNormalSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (OpenNormalSubgroup G) G where
  coe U := U.1
  coe_injective _ _ h := toSubgroup_injective <| SetLike.ext' h
/-
**OpenNormalSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `OpenNormalSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : PartialOrder (OpenNormalSubgroup G) := .ofSetLike (OpenNormalSubgroup G) G

@[to_additive]
/-
**OpenNormalSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `OpenNormalSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubgroupClass (OpenNormalSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]
/-
**OpenNormalSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `OpenNormalSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (OpenNormalSubgroup G) (Subgroup G) where
  coe H := H.toOpenSubgroup.toSubgroup

@[to_additive]
/-
**OpenNormalSubgroup.instPartialOrderOpenNormalSubgroup** 是 Mathlib 中的一个实例，位于命名空
间 `OpenNormalSubgroup`。
形式化陈述：instPartialOrderOpenNormalSubgroup : PartialOrder (OpenNormalSubgroup G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrderOpenNormalSubgroup : PartialOrder (OpenNormalSubgroup G) := inferInstance

@[to_additive]
/-
**OpenNormalSubgroup.instInfOpenNormalSubgroup** 是 Mathlib 中的一个实例，位于命名空间 `OpenNo
rmalSubgroup`。
形式化陈述：instInfOpenNormalSubgroup : Min (OpenNormalSubgroup G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInfOpenNormalSubgroup : Min (OpenNormalSubgroup G) :=
  ⟨fun U V ↦ ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup,
    Subgroup.normal_inf_normal U.toSubgroup V.toSubgroup⟩⟩

@[to_additive]
/-
**OpenNormalSubgroup.instSemilatticeInfOpenNormalSubgroup** 是 Mathlib 中的一个实例，位于命
名空间 `OpenNormalSubgroup`。
形式化陈述：instSemilatticeInfOpenNormalSubgroup : SemilatticeInf (OpenNormalSubgroup 
G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeInfOpenNormalSubgroup : SemilatticeInf (OpenNormalSubgroup G) :=
  SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl

@[to_additive]
/-
**OpenNormalSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `OpenNormalSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SeparatelyContinuousMul G] : Max (OpenNormalSubgroup G) :=
  ⟨fun U V ↦ ⟨U.toOpenSubgroup ⊔ V.toOpenSubgroup,
    Subgroup.sup_normal U.toOpenSubgroup.1 V.toOpenSubgroup.1⟩⟩

@[to_additive]
/-
**OpenNormalSubgroup.instSemilatticeSupOpenNormalSubgroup** 是 Mathlib 中的一个实例，位于命
名空间 `OpenNormalSubgroup`。
形式化陈述：instSemilatticeSupOpenNormalSubgroup [SeparatelyContinuousMul G] : Semilat
ticeSup (OpenNormalSubgroup G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenNormalSubgroup.toSubgroup_injective`：toSubgroup_injective : Function
.Injective (fun H => H.toOpenSubgroup.toSubgroup : OpenNormalSubgroup G -> Subgr
oup G)
-/
instance instSemilatticeSupOpenNormalSubgroup [SeparatelyContinuousMul G] :
    SemilatticeSup (OpenNormalSubgroup G) :=
  toSubgroup_injective.semilatticeSup _ .rfl .rfl fun _ _ ↦ rfl

@[to_additive]
/-
**OpenNormalSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `OpenNormalSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SeparatelyContinuousMul G] : Lattice (OpenNormalSubgroup G) where

end OpenNormalSubgroup

end

/-!
### Existence of an open subgroup in any clopen neighborhood of the neutral element

This section proves the lemma `IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one`, which
states that in a compact topological group, for any clopen neighborhood of 1,
there exists an open subgroup contained within it.
-/

open scoped Pointwise

variable {G : Type*} [TopologicalSpace G]

/-- For a set `W`, `T` is a neighborhood of `0` which is open, stable under negation and satisfies
`T + W ⊆ W`. -/
/-
**IsTopologicalAddGroup.addNegClosureNhd** 是 Mathlib 中的一个归纳类型，位于命名空间 `IsTopologi
calAddGroup`。
形式化陈述：{G : Type u_1} → [TopologicalSpace G] → Set G → Set G → [AddGroup G] → Pro
p
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a set `W`, `T` is a neighborhood of `0` which is open, stable under negation
 and satisfies
`T + W ⊆ W`.
-/
structure IsTopologicalAddGroup.addNegClosureNhd (T W : Set G) [AddGroup G] : Prop where
  nhds : T ∈ 𝓝 0
  neg : -T = T
  isOpen : IsOpen T
  add : W + T ⊆ W

/-- For a set `W`, `T` is a neighborhood of `1` which is open, stable under inverse and satisfies
`T * W ⊆ W`. -/
@[to_additive]
/-
**IsTopologicalGroup.mulInvClosureNhd** 是 Mathlib 中的一个归纳类型，位于命名空间 `IsTopological
Group`。
形式化陈述：{G : Type u_1} → [TopologicalSpace G] → Set G → Set G → [Group G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a set `W`, `T` is a neighborhood of `1` which is open, stable under inverse 
and satisfies
`T * W ⊆ W`.
-/
structure IsTopologicalGroup.mulInvClosureNhd (T W : Set G) [Group G] : Prop where
  nhds : T ∈ 𝓝 1
  inv : T⁻¹ = T
  isOpen : IsOpen T
  mul : W * T ⊆ W

namespace IsTopologicalGroup

variable [Group G] [IsTopologicalGroup G] [CompactSpace G]

open Set Filter

@[to_additive]
/-
**IsTopologicalGroup.exist_mul_closure_nhds** 是 Mathlib 中的一个引理，位于命名空间 `IsTopolog
icalGroup`。
形式化陈述：exist_mul_closure_nhds {W : Set G} (WClopen : IsClopen W) : exists T in 𝓝 
(1 : G), W * T subseteq W
参数：WClopen : IsClopen W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.induction_on`：IsCompact.induction_on (hs : IsCompact s) {p : S
et X -> Prop} (he : p ∅) (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hun
ion : forall…
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `IsClopen.isClosed`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X
}, IsClopen s → IsClosed s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.empty_mul`：empty_mul : ∅ * s = ∅
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mul_subset_mul_right`：mul_subset_mul_right : s₁ subseteq s₂ -> s₁ * 
t subseteq s₂ * t
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Set.union_mul`：union_mul : (s₁ union s₂) * t = s₁ * t union s₂ * t
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Set.mul_subset_mul_left`：mul_subset_mul_left : t₁ subseteq t₂ -> s * t₁ 
subseteq s * t₂
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isOpen_prod_iff`：isOpen_prod_iff {s : Set (X × Y)} : IsOpen s ↔ forall a
 b, (a, b) in s -> exists u v, IsOpen u ∧ IsOpen v ∧ a in u ∧ b in v ∧ u ×ˢ v su
bsete…
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mul_subset_iff`：mul_subset_iff : s * t subseteq u ↔ forall x in s, f
orall y in t, x * y in u
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
lemma exist_mul_closure_nhds {W : Set G} (WClopen : IsClopen W) : ∃ T ∈ 𝓝 (1 : G), W * T ⊆ W := by
  apply WClopen.isClosed.isCompact.induction_on (p := fun S ↦ ∃ T ∈ 𝓝 (1 : G), S * T ⊆ W)
    ⟨Set.univ, by simp only [univ_mem, empty_mul, empty_subset, and_self]⟩
    (fun _ _ huv ⟨T, hT, mem⟩ ↦ ⟨T, hT, (mul_subset_mul_right huv).trans mem⟩)
    fun U V ⟨T₁, hT₁, mem1⟩ ⟨T₂, hT₂, mem2⟩ ↦ ⟨T₁ ∩ T₂, inter_mem hT₁ hT₂, by
      rw [union_mul]
      exact union_subset (mul_subset_mul_left inter_subset_left |>.trans mem1)
        (mul_subset_mul_left inter_subset_right |>.trans mem2) ⟩
  intro x memW
  have : (x, 1) ∈ (fun p ↦ p.1 * p.2) ⁻¹' W := by simp [memW]
  rcases isOpen_prod_iff.mp (continuous_mul.isOpen_preimage W <| WClopen.2) x 1 this with
    ⟨U, V, Uopen, Vopen, xmemU, onememV, prodsub⟩
  have h6 : U * V ⊆ W := mul_subset_iff.mpr (fun _ hx _ hy ↦ prodsub (mk_mem_prod hx hy))
  exact ⟨U ∩ W, ⟨U, Uopen.mem_nhds xmemU, W, fun _ a ↦ a, rfl⟩,
    V, IsOpen.mem_nhds Vopen onememV, fun _ a ↦ h6 ((mul_subset_mul_right inter_subset_left) a)⟩

@[to_additive]
/-
**IsTopologicalGroup.exists_mulInvClosureNhd** 是 Mathlib 中的一个引理，位于命名空间 `IsTopolo
gicalGroup`。
形式化陈述：exists_mulInvClosureNhd {W : Set G} (WClopen : IsClopen W) : exists T, mul
InvClosureNhd T W
参数：WClopen : IsClopen W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsTopologicalGroup.exist_mul_closure_nhds`：exist_mul_closure_nhds {W : S
et G} (WClopen : IsClopen W) : exists T in 𝓝 (1 : G), W * T subseteq W
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_inv`：inter_inv : (s inter t)⁻¹ = s⁻¹ inter t⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `IsOpen.inv`：IsOpen.inv (hs : IsOpen s) : IsOpen s⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `Set.mul_subset_mul_left`：mul_subset_mul_left : t₁ subseteq t₂ -> s * t₁ 
subseteq s * t₂
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
lemma exists_mulInvClosureNhd {W : Set G} (WClopen : IsClopen W) :
    ∃ T, mulInvClosureNhd T W := by
  rcases exist_mul_closure_nhds WClopen with ⟨S, Smemnhds, mulclose⟩
  rcases mem_nhds_iff.mp Smemnhds with ⟨U, UsubS, Uopen, onememU⟩
  use U ∩ U⁻¹
  constructor
  · simp [Uopen.mem_nhds onememU, inv_mem_nhds_one]
  · simp [inter_comm]
  · exact Uopen.inter Uopen.inv
  · exact fun a ha ↦ mulclose (mul_subset_mul_left UsubS (mul_subset_mul_left inter_subset_left ha))

@[to_additive]
/-
**IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one** 是 Mathlib 中的一个定
理，位于命名空间 `IsTopologicalGroup`。
形式化陈述：exist_openSubgroup_sub_clopen_nhds_of_one {G : Type*} [Group G] [Topologic
alSpace G] [IsTopologicalGroup G] [CompactSpace G] {W : Set G} (WClopen : IsClop
en W) (einW : 1 in W) : exists H : OpenSubgroup G, (H : Set G) subseteq W
参数：WClopen : IsClopen W；einW : 1 in W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsTopologicalGroup.exists_mulInvClosureNhd`：exists_mulInvClosureNhd {W :
 Set G} (WClopen : IsClopen W) : exists T, mulInvClosureNhd T W
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Set.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `IsTopologicalGroup.mulInvClosureNhd.nhds`：∀ {G : Type u_1} [inst : Topol
ogicalSpace G] {T W : Set G} [inst_1 : Group G],   IsTopologicalGroup.mulInvClos
ureNhd T W → T ∈ nhds 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsTopologicalGroup.mulInvClosureNhd.inv`：∀ {G : Type u_1} [inst : Topolo
gicalSpace G] {T W : Set G} [inst_1 : Group G],   IsTopologicalGroup.mulInvClosu
reNhd T W → T⁻¹ = T
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `IsOpen.mul_left`：IsOpen.mul_left : IsOpen t -> IsOpen (s * t)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `IsTopologicalGroup.mulInvClosureNhd.isOpen`：∀ {G : Type u_1} [inst : Top
ologicalSpace G] {T W : Set G} [inst_1 : Group G],   IsTopologicalGroup.mulInvCl
osureNhd T W → IsOpen T
· 使用定理 `IsTopologicalGroup.mulInvClosureNhd.mul`：∀ {G : Type u_1} [inst : Topolo
gicalSpace G] {T W : Set G} [inst_1 : Group G],   IsTopologicalGroup.mulInvClosu
reNhd T W → W * T ⊆ W
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mul_subset_mul_right`：mul_subset_mul_right : s₁ subseteq s₂ -> s₁ * 
t subseteq s₂ * t
（共 33 条，此处仅展示前 30 条）
-/
theorem exist_openSubgroup_sub_clopen_nhds_of_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    ∃ H : OpenSubgroup G, (H : Set G) ⊆ W := by
  rcases exists_mulInvClosureNhd WClopen with ⟨V, hV⟩
  let S : Subgroup G := {
    carrier := ⋃ n, V ^ (n + 1)
    mul_mem' := fun ha hb ↦ by
      rcases mem_iUnion.mp ha with ⟨k, hk⟩
      rcases mem_iUnion.mp hb with ⟨l, hl⟩
      apply mem_iUnion.mpr
      use k + 1 + l
      rw [add_assoc, pow_add]
      exact Set.mul_mem_mul hk hl
    one_mem' := by
      apply mem_iUnion.mpr
      use 0
      simp [mem_of_mem_nhds hV.nhds]
    inv_mem' := fun ha ↦ by
      rcases mem_iUnion.mp ha with ⟨k, hk⟩
      apply mem_iUnion.mpr
      use k
      rw [← hV.inv]
      simpa only [inv_pow, Set.mem_inv, inv_inv] using hk }
  have : IsOpen (⋃ n, V ^ (n + 1)) := by
    refine isOpen_iUnion (fun n ↦ ?_)
    rw [pow_succ]
    exact hV.isOpen.mul_left
  use ⟨S, this⟩
  have mulVpow (n : ℕ) : W * V ^ (n + 1) ⊆ W := by
    induction n with
    | zero => simp [hV.mul]
    | succ n ih =>
      rw [pow_succ, ← mul_assoc]
      exact (Set.mul_subset_mul_right ih).trans hV.mul
  have (n : ℕ) : V ^ (n + 1) ⊆ W * V ^ (n + 1) := by
    intro x xin
    rw [Set.mem_mul]
    use 1, einW, x, xin
    rw [one_mul]
  apply iUnion_subset fun i _ a ↦ mulVpow i (this i a)

end IsTopologicalGroup

