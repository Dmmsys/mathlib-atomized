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

/--
Definition of `OpenAddSubgroup` / `OpenAddSubgroup` 的定义

English:
structure OpenAddSubgroup
  parameters: (G : Type*) [AddGroup G] [TopologicalSpace G]
  extends: AddSubgroup G
  axioms and operations (1):
    - isOpen' : IsOpen carrier

中文:
结构 OpenAddSubgroup
  参数: (G : 类型) [AddGroup G] [TopologicalSpace G]
  继承: AddSubgroup G
  公理与运算 (1 个):
    - isOpen' : IsOpen carrier
-/
structure OpenAddSubgroup (G : Type*) [AddGroup G] [TopologicalSpace G] extends AddSubgroup G where
  isOpen' : IsOpen carrier

/-- The type of open subgroups of a topological group. -/
@[to_additive]
/--
Definition of `OpenSubgroup` / `OpenSubgroup` 的定义

English:
structure OpenSubgroup
  parameters: (G : Type*) [Group G] [TopologicalSpace G]
  extends: Subgroup G
  axioms and operations (1):
    - isOpen' : IsOpen carrier

中文:
结构 OpenSubgroup
  参数: (G : 类型) [Group G] [TopologicalSpace G]
  继承: Subgroup G
  公理与运算 (1 个):
    - isOpen' : IsOpen carrier
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
/--
Instance `hasCoeSubgroup` / 实例 `hasCoeSubgroup`

English:
instance hasCoeSubgroup
  signature: : CoeTC (OpenSubgroup G) (Subgroup G)
  body: ⟨toSubgroup⟩

@[to_additive]

中文:
实例 hasCoeSubgroup
  签名: : CoeTC (OpenSubgroup G) (Subgroup G)
  定义体: ⟨toSubgroup⟩

@[to_additive]

Depends on / 依赖: toSubgroup
-/
instance hasCoeSubgroup : CoeTC (OpenSubgroup G) (Subgroup G) :=
  ⟨toSubgroup⟩

@[to_additive]
/--
theorem `toSubgroup_injective` / 定理 `toSubgroup_injective`

English:
theorem toSubgroup_injective
  statement: Injective ((↑) : OpenSubgroup G -> Subgroup G)

中文:
定理 toSubgroup_injective
  结论: Injective ((↑) : OpenSubgroup G -> Subgroup G)
-/
theorem toSubgroup_injective : Injective ((↑) : OpenSubgroup G -> Subgroup G)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (OpenSubgroup G) G
  body: U.1
coe_injective _ _ h := toSubgroup_injective SetLike.ext' h

中文:
实例 :
  签名: SetLike (OpenSubgroup G) G
  定义体: U.1
coe_injective _ _ h := toSubgroup_injective SetLike.ext' h
-/
instance : SetLike (OpenSubgroup G) G where
  coe U := U.1
coe_injective _ _ h := toSubgroup_injective SetLike.ext' h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (OpenSubgroup G)
  body: .ofSetLike (OpenSubgroup G) G

@[to_additive]

中文:
实例 :
  签名: PartialOrder (OpenSubgroup G)
  定义体: .ofSetLike (OpenSubgroup G) G

@[to_additive]
-/
@[to_additive] instance : PartialOrder (OpenSubgroup G) := .ofSetLike (OpenSubgroup G) G

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubgroupClass (OpenSubgroup G) G
  body: Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

中文:
实例 :
  签名: SubgroupClass (OpenSubgroup G) G
  定义体: Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

Depends on / 依赖: Subsemigroup, Subsemigroup.mul_mem, mul_mem
-/
instance : SubgroupClass (OpenSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

/-- Coercion from `OpenSubgroup G` to `Opens G`. -/
@[to_additive (attr := coe) /-- Coercion from `OpenAddSubgroup G` to `Opens G`. -/]
/--
Definition of `toOpens` / `toOpens` 的定义

English:
definition toOpens
  signature: (U : OpenSubgroup G)
  body: ⟨U, U.isOpen'⟩

@[to_additive]

中文:
定义 toOpens
  签名: (U : OpenSubgroup G)
  定义体: ⟨U, U.isOpen'⟩

@[to_additive]

Depends on / 依赖: U.isOpen, isOpen
-/
def toOpens (U : OpenSubgroup G) : Opens G := ⟨U, U.isOpen'⟩

@[to_additive]
/--
Instance `hasCoeOpens` / 实例 `hasCoeOpens`

English:
instance hasCoeOpens
  signature: : CoeTC (OpenSubgroup G) (Opens G)
  body: ⟨toOpens⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 hasCoeOpens
  签名: : CoeTC (OpenSubgroup G) (Opens G)
  定义体: ⟨toOpens⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: toOpens
-/
instance hasCoeOpens : CoeTC (OpenSubgroup G) (Opens G) := ⟨toOpens⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_toOpens` / 定理 `coe_toOpens`

English:
theorem coe_toOpens
  statement: ((U : Opens G) : Set G) = U
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_toOpens
  结论: ((U : Opens G) : Set G) = U
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_toOpens : ((U : Opens G) : Set G) = U :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_toSubgroup` / 定理 `coe_toSubgroup`

English:
theorem coe_toSubgroup
  statement: ((U : Subgroup G) : Set G) = U
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_toSubgroup
  结论: ((U : Subgroup G) : Set G) = U
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_toSubgroup : ((U : Subgroup G) : Set G) = U := rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `mem_toOpens` / 定理 `mem_toOpens`

English:
theorem mem_toOpens
  statement: g in (U : Opens G) ↔ g in U
  proof: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 mem_toOpens
  结论: g in (U : Opens G) ↔ g in U
  证明: Iff.rfl

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toOpens : g in (U : Opens G) ↔ g in U := Iff.rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `mem_toSubgroup` / 定理 `mem_toSubgroup`

English:
theorem mem_toSubgroup
  statement: g in (U : Subgroup G) ↔ g in U
  proof: Iff.rfl

@[to_additive (attr := ext)]

中文:
定理 mem_toSubgroup
  结论: g in (U : Subgroup G) ↔ g in U
  证明: Iff.rfl

@[to_additive (attr := ext)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubgroup : g in (U : Subgroup G) ↔ g in U := Iff.rfl

@[to_additive (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall x, x in U ↔ x in V)
  statement: U = V
  proof: SetLike.ext h

中文:
定理 ext
  条件: (h : 对任意 x, x in U ↔ x in V)
  结论: U = V
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext (h : forall x, x in U ↔ x in V) : U = V :=
  SetLike.ext h

variable (U)

@[to_additive]
/--
theorem `isOpen` / 定理 `isOpen`

English:
theorem isOpen
  statement: IsOpen (U : Set G)
  proof: U.isOpen'

@[to_additive]

中文:
定理 isOpen
  结论: IsOpen (U : Set G)
  证明: U.isOpen'

@[to_additive]
-/
protected theorem isOpen : IsOpen (U : Set G) :=
  U.isOpen'

@[to_additive]
/--
theorem `mem_nhds_one` / 定理 `mem_nhds_one`

English:
theorem mem_nhds_one
  statement: (U : Set G) in 𝓝 (1 : G)
  proof: U.isOpen.mem_nhds U.one_mem

中文:
定理 mem_nhds_one
  结论: (U : Set G) in 𝓝 (1 : G)
  证明: U.isOpen.mem_nhds U.one_mem

Depends on / 依赖: U.isOpen.mem_nhds, U.one_mem, isOpen, mem_nhds, one_mem
-/
theorem mem_nhds_one : (U : Set G) in 𝓝 (1 : G) :=
  U.isOpen.mem_nhds U.one_mem

variable {U}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (OpenSubgroup G)
  body: ⟨⟨⊤, isOpen_univ⟩⟩

@[to_additive (attr := simp)]

中文:
实例 :
  签名: Top (OpenSubgroup G)
  定义体: ⟨⟨⊤, isOpen_univ⟩⟩

@[to_additive (attr := simp)]
-/
@[to_additive] instance : Top (OpenSubgroup G) := ⟨⟨⊤, isOpen_univ⟩⟩

@[to_additive (attr := simp)]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: (x : G)
  statement: x in (⊤ : OpenSubgroup G)
  proof: trivial

@[to_additive (attr := simp, norm_cast)]

中文:
定理 mem_top
  条件: (x : G)
  结论: x in (⊤ : OpenSubgroup G)
  证明: trivial

@[to_additive (attr := simp, norm_cast)]
-/
theorem mem_top (x : G) : x in (⊤ : OpenSubgroup G) :=
  trivial

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : OpenSubgroup G) : Set G) = Set.univ
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_top
  结论: ((⊤ : OpenSubgroup G) : Set G) = Set.univ
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_top : ((⊤ : OpenSubgroup G) : Set G) = Set.univ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `toSubgroup_top` / 定理 `toSubgroup_top`

English:
theorem toSubgroup_top
  statement: ((⊤ : OpenSubgroup G) : Subgroup G) = ⊤
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 toSubgroup_top
  结论: ((⊤ : OpenSubgroup G) : Subgroup G) = ⊤
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem toSubgroup_top : ((⊤ : OpenSubgroup G) : Subgroup G) = ⊤ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `toOpens_top` / 定理 `toOpens_top`

English:
theorem toOpens_top
  statement: ((⊤ : OpenSubgroup G) : Opens G) = ⊤
  proof: rfl

@[to_additive]

中文:
定理 toOpens_top
  结论: ((⊤ : OpenSubgroup G) : Opens G) = ⊤
  证明: rfl

@[to_additive]
-/
theorem toOpens_top : ((⊤ : OpenSubgroup G) : Opens G) = ⊤ :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (OpenSubgroup G)
  body: ⟨⊤⟩

@[to_additive]

中文:
实例 :
  签名: Inhabited (OpenSubgroup G)
  定义体: ⟨⊤⟩

@[to_additive]
-/
instance : Inhabited (OpenSubgroup G) :=
  ⟨⊤⟩

@[to_additive]
/--
theorem `isClosed` / 定理 `isClosed`

English:
theorem isClosed
  given: [SeparatelyContinuousMul G] (U : OpenSubgroup G)
  statement: IsClosed (U : Set G)
  proof: by
  have := QuotientGroup.discreteTopology U.isOpen
  exact QuotientGroup.t1Space_iff.mp inferInstance

@[to_additive]

中文:
定理 isClosed
  条件: [SeparatelyContinuousMul G] (U : OpenSubgroup G)
  结论: IsClosed (U : Set G)
  证明: by
  have := QuotientGroup.discreteTopology U.isOpen
  exact QuotientGroup.t1Space_iff.mp inferInstance

@[to_additive]

Depends on / 依赖: QuotientGroup, QuotientGroup.discreteTopology, QuotientGroup.t1Space_iff.mp, U.isOpen, discreteTopology, isOpen, t1Space_iff
-/
theorem isClosed [SeparatelyContinuousMul G] (U : OpenSubgroup G) : IsClosed (U : Set G) := by
  have := QuotientGroup.discreteTopology U.isOpen
  exact QuotientGroup.t1Space_iff.mp inferInstance

@[to_additive]
/--
theorem `isClopen` / 定理 `isClopen`

English:
theorem isClopen
  given: [SeparatelyContinuousMul G] (U : OpenSubgroup G)
  statement: IsClopen (U : Set G)
  proof: ⟨U.isClosed, U.isOpen⟩

中文:
定理 isClopen
  条件: [SeparatelyContinuousMul G] (U : OpenSubgroup G)
  结论: IsClopen (U : Set G)
  证明: ⟨U.isClosed, U.isOpen⟩

Depends on / 依赖: U.isClosed, U.isOpen, isClosed, isOpen
-/
theorem isClopen [SeparatelyContinuousMul G] (U : OpenSubgroup G) : IsClopen (U : Set G) :=
  ⟨U.isClosed, U.isOpen⟩

section

variable {H : Type*} [Group H] [TopologicalSpace H]

/-- The product of two open subgroups as an open subgroup of the product group. -/
@[to_additive prod
/-- The product of two open subgroups as an open subgroup of the product group. -/]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (U : OpenSubgroup G) (V : OpenSubgroup H)
  body: ⟨.prod U V, U.isOpen.prod V.isOpen⟩

@[to_additive (attr := simp, norm_cast) coe_prod]

中文:
定义 prod
  签名: (U : OpenSubgroup G) (V : OpenSubgroup H)
  定义体: ⟨.prod U V, U.isOpen.prod V.isOpen⟩

@[to_additive (attr := simp, norm_cast) coe_prod]

Depends on / 依赖: U.isOpen.prod, V.isOpen, isOpen
-/
def prod (U : OpenSubgroup G) (V : OpenSubgroup H) : OpenSubgroup (G × H) :=
  ⟨.prod U V, U.isOpen.prod V.isOpen⟩

@[to_additive (attr := simp, norm_cast) coe_prod]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (U : OpenSubgroup G) (V : OpenSubgroup H)
  proof: rfl

@[to_additive (attr := simp, norm_cast) toAddSubgroup_prod]

中文:
定理 coe_prod
  条件: (U : OpenSubgroup G) (V : OpenSubgroup H)
  证明: rfl

@[to_additive (attr := simp, norm_cast) toAddSubgroup_prod]
-/
theorem coe_prod (U : OpenSubgroup G) (V : OpenSubgroup H) :
    (U.prod V : Set (G × H)) = (U : Set G) ×ˢ (V : Set H) :=
  rfl

@[to_additive (attr := simp, norm_cast) toAddSubgroup_prod]
/--
theorem `toSubgroup_prod` / 定理 `toSubgroup_prod`

English:
theorem toSubgroup_prod
  given: (U : OpenSubgroup G) (V : OpenSubgroup H)
  proof: rfl

中文:
定理 toSubgroup_prod
  条件: (U : OpenSubgroup G) (V : OpenSubgroup H)
  证明: rfl
-/
theorem toSubgroup_prod (U : OpenSubgroup G) (V : OpenSubgroup H) :
    (U.prod V : Subgroup (G × H)) = (U : Subgroup G).prod V :=
  rfl

end

@[to_additive]
/--
Instance `instInfOpenSubgroup` / 实例 `instInfOpenSubgroup`

English:
instance instInfOpenSubgroup
  signature: : Min (OpenSubgroup G)
  body: ⟨fun U V => ⟨U ⊓ V, U.isOpen.inter V.isOpen⟩⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 instInfOpenSubgroup
  签名: : Min (OpenSubgroup G)
  定义体: ⟨fun U V => ⟨U ⊓ V, U.isOpen.inter V.isOpen⟩⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: U.isOpen.inter, V.isOpen, isOpen
-/
instance instInfOpenSubgroup : Min (OpenSubgroup G) :=
  ⟨fun U V => ⟨U ⊓ V, U.isOpen.inter V.isOpen⟩⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  statement: (↑(U ⊓ V) : Set G) = (U : Set G) inter V
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_inf
  结论: (↑(U ⊓ V) : Set G) = (U : Set G) inter V
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_inf : (↑(U ⊓ V) : Set G) = (U : Set G) inter V :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `toSubgroup_inf` / 定理 `toSubgroup_inf`

English:
theorem toSubgroup_inf
  statement: (↑(U ⊓ V) : Subgroup G) = ↑U ⊓ ↑V
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 toSubgroup_inf
  结论: (↑(U ⊓ V) : Subgroup G) = ↑U ⊓ ↑V
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem toSubgroup_inf : (↑(U ⊓ V) : Subgroup G) = ↑U ⊓ ↑V :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `toOpens_inf` / 定理 `toOpens_inf`

English:
theorem toOpens_inf
  statement: (↑(U ⊓ V) : Opens G) = ↑U ⊓ ↑V
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toOpens_inf
  结论: (↑(U ⊓ V) : Opens G) = ↑U ⊓ ↑V
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toOpens_inf : (↑(U ⊓ V) : Opens G) = ↑U ⊓ ↑V :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {x}
  statement: x in U ⊓ V ↔ x in U ∧ x in V
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_inf
  条件: {x}
  结论: x in U ⊓ V ↔ x in U ∧ x in V
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf {x} : x in U ⊓ V ↔ x in U ∧ x in V :=
  Iff.rfl

@[to_additive]
/--
Instance `instPartialOrderOpenSubgroup` / 实例 `instPartialOrderOpenSubgroup`

English:
instance instPartialOrderOpenSubgroup
  signature: : PartialOrder (OpenSubgroup G)
  body: inferInstance

中文:
实例 instPartialOrderOpenSubgroup
  签名: : PartialOrder (OpenSubgroup G)
  定义体: inferInstance
-/
instance instPartialOrderOpenSubgroup : PartialOrder (OpenSubgroup G) := inferInstance

-- We override `toPartialorder` to get better `le`
@[to_additive]
/--
Instance `instSemilatticeInfOpenSubgroup` / 实例 `instSemilatticeInfOpenSubgroup`

English:
instance instSemilatticeInfOpenSubgroup
  signature: : SemilatticeInf (OpenSubgroup G)
  body: SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[to_additive]

中文:
实例 instSemilatticeInfOpenSubgroup
  签名: : SemilatticeInf (OpenSubgroup G)
  定义体: SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[to_additive]

Depends on / 依赖: SetLike, SetLike.coe_injective.semilatticeInf, coe_injective, semilatticeInf
-/
instance instSemilatticeInfOpenSubgroup : SemilatticeInf (OpenSubgroup G) :=
  SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTop (OpenSubgroup G)
  body: Set.subset_univ _

@[to_additive (attr := simp, norm_cast)]

中文:
实例 :
  签名: OrderTop (OpenSubgroup G)
  定义体: Set.subset_univ _

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Set.subset_univ, subset_univ
-/
instance : OrderTop (OpenSubgroup G) where
  le_top _ := Set.subset_univ _

@[to_additive (attr := simp, norm_cast)]
/--
theorem `toSubgroup_le` / 定理 `toSubgroup_le`

English:
theorem toSubgroup_le
  statement: (U : Subgroup G) <= (V : Subgroup G) ↔ U <= V
  proof: Iff.rfl

中文:
定理 toSubgroup_le
  结论: (U : Subgroup G) <= (V : Subgroup G) ↔ U <= V
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem toSubgroup_le : (U : Subgroup G) <= (V : Subgroup G) ↔ U <= V :=
  Iff.rfl

variable {N : Type*} [Group N] [TopologicalSpace N]

/-- The preimage of an `OpenSubgroup` along a continuous `Monoid` homomorphism
  is an `OpenSubgroup`. -/
@[to_additive /-- The preimage of an `OpenAddSubgroup` along a continuous `AddMonoid` homomorphism
is an `OpenAddSubgroup`. -/]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : G ->* N) (hf : Continuous f) (H : OpenSubgroup N)
  body: ⟨.comap f H, H.isOpen.preimage hf⟩

@[to_additive (attr := simp, norm_cast)]

中文:
定义 comap
  签名: (f : G ->* N) (hf : Continuous f) (H : OpenSubgroup N)
  定义体: ⟨.comap f H, H.isOpen.preimage hf⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: H.isOpen.preimage, isOpen, preimage
-/
def comap (f : G ->* N) (hf : Continuous f) (H : OpenSubgroup N) : OpenSubgroup G :=
  ⟨.comap f H, H.isOpen.preimage hf⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (H : OpenSubgroup N) (f : G ->* N) (hf : Continuous f)
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_comap
  条件: (H : OpenSubgroup N) (f : G ->* N) (hf : Continuous f)
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_comap (H : OpenSubgroup N) (f : G ->* N) (hf : Continuous f) :
    (H.comap f hf : Set G) = f ⁻¹' H :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `toSubgroup_comap` / 定理 `toSubgroup_comap`

English:
theorem toSubgroup_comap
  given: (H : OpenSubgroup N) (f : G ->* N) (hf : Continuous f)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toSubgroup_comap
  条件: (H : OpenSubgroup N) (f : G ->* N) (hf : Continuous f)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toSubgroup_comap (H : OpenSubgroup N) (f : G ->* N) (hf : Continuous f) :
    (H.comap f hf : Subgroup G) = (H : Subgroup N).comap f :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {H : OpenSubgroup N} {f : G ->* N} {hf : Continuous f} {x : G}
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_comap
  条件: {H : OpenSubgroup N} {f : G ->* N} {hf : Continuous f} {x : G}
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap {H : OpenSubgroup N} {f : G ->* N} {hf : Continuous f} {x : G} :
    x in H.comap f hf ↔ f x in H :=
  Iff.rfl

@[to_additive]
/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  statement: {P : Type*} [Group P] [TopologicalSpace P] (K : OpenSubgroup P) (f₂ : N ->* P)
  proof: rfl

中文:
定理 comap_comap
  结论: {P : 类型} [Group P] [TopologicalSpace P] (K : OpenSubgroup P) (f₂ : N ->* P)
  证明: rfl
-/
theorem comap_comap {P : Type*} [Group P] [TopologicalSpace P] (K : OpenSubgroup P) (f₂ : N ->* P)
    (hf₂ : Continuous f₂) (f₁ : G ->* N) (hf₁ : Continuous f₁) :
    (K.comap f₂ hf₂).comap f₁ hf₁ = K.comap (f₂.comp f₁) (hf₂.comp hf₁) :=
  rfl

end OpenSubgroup
namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

@[to_additive]
/--
theorem `isOpen_of_mem_nhds` / 定理 `isOpen_of_mem_nhds`

English:
theorem isOpen_of_mem_nhds
  statement: [SeparatelyContinuousMul G] (H : Subgroup G) {g : G}
  proof: by
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  have hg' : g in H := SetLike.mem_coe.1 (mem_of_mem_nhds hg)
  have : Filter.Tendsto (fun y => y * (x⁻¹ * g)) (𝓝 x) (𝓝 g) :=
    (continuous_id.mul_const _).tendsto' _ _ (mul_inv_cancel_left _ _)
  simpa only [SetLike.mem_coe, Filter.mem_map',
    H.

中文:
定理 isOpen_of_mem_nhds
  结论: [SeparatelyContinuousMul G] (H : Subgroup G) {g : G}
  证明: by
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  have hg' : g in H := SetLike.mem_coe.1 (mem_of_mem_nhds hg)
  have : Filter.Tendsto (fun y => y * (x⁻¹ * g)) (𝓝 x) (𝓝 g) :=
    (continuous_id.mul_const _).tendsto' _ _ (mul_inv_cancel_left _ _)
  simpa only [SetLike.mem_coe, Filter.mem_map',
    H.

Depends on / 依赖: Filter, Filter.Tendsto, Filter.mem_map, H.inv_mem, H.mul_mem, H.mul_mem_cancel_right, SetLike, SetLike.mem_coe, Tendsto, continuous_id, continuous_id.mul_const, inv_mem, isOpen_iff_mem_nhds, mem_coe, mem_map, mem_of_mem_nhds, mul_const, mul_inv_cancel_left, mul_mem, mul_mem_cancel_right
-/
theorem isOpen_of_mem_nhds [SeparatelyContinuousMul G] (H : Subgroup G) {g : G}
    (hg : (H : Set G) in 𝓝 g) : IsOpen (H : Set G) := by
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  have hg' : g in H := SetLike.mem_coe.1 (mem_of_mem_nhds hg)
  have : Filter.Tendsto (fun y => y * (x⁻¹ * g)) (𝓝 x) (𝓝 g) :=
    (continuous_id.mul_const _).tendsto' _ _ (mul_inv_cancel_left _ _)
  simpa only [SetLike.mem_coe, Filter.mem_map',
    H.mul_mem_cancel_right (H.mul_mem (H.inv_mem hx) hg')] using! this hg

@[to_additive]
/--
theorem `isOpen_mono` / 定理 `isOpen_mono`

English:
theorem isOpen_mono
  statement: [SeparatelyContinuousMul G] {H₁ H₂ : Subgroup G} (h : H₁ <= H₂)
  proof: isOpen_of_mem_nhds _ Filter.mem_of_superset (h₁.mem_nhds <| one_mem H₁) h

@[to_additive]

中文:
定理 isOpen_mono
  结论: [SeparatelyContinuousMul G] {H₁ H₂ : Subgroup G} (h : H₁ <= H₂)
  证明: isOpen_of_mem_nhds _ Filter.mem_of_superset (h₁.mem_nhds <| one_mem H₁) h

@[to_additive]

Depends on / 依赖: Filter, Filter.mem_of_superset, isOpen_of_mem_nhds, mem_nhds, mem_of_superset, one_mem
-/
theorem isOpen_mono [SeparatelyContinuousMul G] {H₁ H₂ : Subgroup G} (h : H₁ <= H₂)
    (h₁ : IsOpen (H₁ : Set G)) : IsOpen (H₂ : Set G) :=
isOpen_of_mem_nhds _ Filter.mem_of_superset (h₁.mem_nhds <| one_mem H₁) h

@[to_additive]
/--
theorem `isOpen_of_openSubgroup` / 定理 `isOpen_of_openSubgroup`

English:
theorem isOpen_of_openSubgroup
  proof: isOpen_mono h U.isOpen

中文:
定理 isOpen_of_openSubgroup
  证明: isOpen_mono h U.isOpen

Depends on / 依赖: U.isOpen, isOpen, isOpen_mono
-/
theorem isOpen_of_openSubgroup
    [SeparatelyContinuousMul G] (H : Subgroup G) {U : OpenSubgroup G} (h : ↑U <= H) :
    IsOpen (H : Set G) :=
  isOpen_mono h U.isOpen

/-- If a subgroup of a topological group has `1` in its interior, then it is open. -/
@[to_additive /-- If a subgroup of an additive topological group has `0` in its interior, then it is
open. -/]
/--
theorem `isOpen_of_one_mem_interior` / 定理 `isOpen_of_one_mem_interior`

English:
theorem isOpen_of_one_mem_interior
  statement: [SeparatelyContinuousMul G] (H : Subgroup G)
  proof: isOpen_of_mem_nhds H mem_interior_iff_mem_nhds.1 h_1_int

@[to_additive]

中文:
定理 isOpen_of_one_mem_interior
  结论: [SeparatelyContinuousMul G] (H : Subgroup G)
  证明: isOpen_of_mem_nhds H mem_interior_iff_mem_nhds.1 h_1_int

@[to_additive]

Depends on / 依赖: h_1_int, isOpen_of_mem_nhds, mem_interior_iff_mem_nhds
-/
theorem isOpen_of_one_mem_interior [SeparatelyContinuousMul G] (H : Subgroup G)
    (h_1_int : (1 : G) in interior (H : Set G)) : IsOpen (H : Set G) :=
isOpen_of_mem_nhds H mem_interior_iff_mem_nhds.1 h_1_int

@[to_additive]
/--
lemma `isClosed_of_isOpen` / 引理 `isClosed_of_isOpen`

English:
lemma isClosed_of_isOpen
  given: [SeparatelyContinuousMul G] (U : Subgroup G) (h : IsOpen (U : Set G))
  proof: OpenSubgroup.isClosed ⟨U, h⟩

@[to_additive]

中文:
引理 isClosed_of_isOpen
  条件: [SeparatelyContinuousMul G] (U : Subgroup G) (h : IsOpen (U : Set G))
  证明: OpenSubgroup.isClosed ⟨U, h⟩

@[to_additive]

Depends on / 依赖: OpenSubgroup, OpenSubgroup.isClosed, isClosed
-/
lemma isClosed_of_isOpen [SeparatelyContinuousMul G] (U : Subgroup G) (h : IsOpen (U : Set G)) :
    IsClosed (U : Set G) :=
  OpenSubgroup.isClosed ⟨U, h⟩

@[to_additive]
/--
lemma `subgroupOf_isOpen` / 引理 `subgroupOf_isOpen`

English:
lemma subgroupOf_isOpen
  given: (U K : Subgroup G) (h : IsOpen (K : Set G))
  proof: Continuous.isOpen_preimage (continuous_iff_le_induced.mpr fun _ => id) _ h

@[to_additive]

中文:
引理 subgroupOf_isOpen
  条件: (U K : Subgroup G) (h : IsOpen (K : Set G))
  证明: Continuous.isOpen_preimage (continuous_iff_le_induced.mpr fun _ => id) _ h

@[to_additive]

Depends on / 依赖: Continuous, Continuous.isOpen_preimage, continuous_iff_le_induced, continuous_iff_le_induced.mpr, isOpen_preimage
-/
lemma subgroupOf_isOpen (U K : Subgroup G) (h : IsOpen (K : Set G)) :
    IsOpen (K.subgroupOf U : Set U) :=
  Continuous.isOpen_preimage (continuous_iff_le_induced.mpr fun _ => id) _ h

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SeparatelyContinuousMul
  signature: G] (U
  body: QuotientGroup.discreteTopology U.isOpen

@[to_additive]

中文:
实例 [SeparatelyContinuousMul
  签名: G] (U
  定义体: QuotientGroup.discreteTopology U.isOpen

@[to_additive]

Depends on / 依赖: QuotientGroup, QuotientGroup.discreteTopology, U.isOpen, discreteTopology, isOpen
-/
instance [SeparatelyContinuousMul G] (U : OpenSubgroup G) : DiscreteTopology (G ⧸ U.toSubgroup) :=
  QuotientGroup.discreteTopology U.isOpen

@[to_additive]
/--
lemma `quotient_finite_of_isOpen` / 引理 `quotient_finite_of_isOpen`

English:
lemma quotient_finite_of_isOpen
  statement: [SeparatelyContinuousMul G] [CompactSpace G] (U : Subgroup G)
  proof: have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology h
  finite_of_compact_of_discrete

@[to_additive]

中文:
引理 quotient_finite_of_isOpen
  结论: [SeparatelyContinuousMul G] [CompactSpace G] (U : Subgroup G)
  证明: have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology h
  finite_of_compact_of_discrete

@[to_additive]

Depends on / 依赖: DiscreteTopology, QuotientGroup, QuotientGroup.discreteTopology, discreteTopology, finite_of_compact_of_discrete
-/
lemma quotient_finite_of_isOpen [SeparatelyContinuousMul G] [CompactSpace G] (U : Subgroup G)
    (h : IsOpen (U : Set G)) : Finite (G ⧸ U) :=
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology h
  finite_of_compact_of_discrete

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SeparatelyContinuousMul
  signature: G] [CompactSpace G] (U
  body: quotient_finite_of_isOpen U.toSubgroup U.isOpen

@[to_additive]

中文:
实例 [SeparatelyContinuousMul
  签名: G] [CompactSpace G] (U
  定义体: quotient_finite_of_isOpen U.toSubgroup U.isOpen

@[to_additive]

Depends on / 依赖: U.isOpen, U.toSubgroup, isOpen, quotient_finite_of_isOpen, toSubgroup
-/
instance [SeparatelyContinuousMul G] [CompactSpace G] (U : OpenSubgroup G) :
    Finite (G ⧸ U.toSubgroup) :=
  quotient_finite_of_isOpen U.toSubgroup U.isOpen

@[to_additive]
/--
lemma `quotient_finite_of_isOpen'` / 引理 `quotient_finite_of_isOpen'`

English:
lemma quotient_finite_of_isOpen'
  statement: [IsTopologicalGroup G] [CompactSpace G] (U : Subgroup G)
  proof: have : CompactSpace U := isCompact_iff_compactSpace.mp IsClosed.isCompact
    U.isClosed_of_isOpen hUopen
  K.quotient_finite_of_isOpen hKopen

@[to_additive]

中文:
引理 quotient_finite_of_isOpen'
  结论: [IsTopologicalGroup G] [CompactSpace G] (U : Subgroup G)
  证明: have : CompactSpace U := isCompact_iff_compactSpace.mp IsClosed.isCompact
    U.isClosed_of_isOpen hUopen
  K.quotient_finite_of_isOpen hKopen

@[to_additive]

Depends on / 依赖: CompactSpace, IsClosed, IsClosed.isCompact, K.quotient_finite_of_isOpen, U.isClosed_of_isOpen, hKopen, hUopen, isClosed_of_isOpen, isCompact, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, quotient_finite_of_isOpen
-/
lemma quotient_finite_of_isOpen' [IsTopologicalGroup G] [CompactSpace G] (U : Subgroup G)
    (K : Subgroup U) (hUopen : IsOpen (U : Set G)) (hKopen : IsOpen (K : Set U)) :
    Finite (U ⧸ K) :=
have : CompactSpace U := isCompact_iff_compactSpace.mp IsClosed.isCompact
    U.isClosed_of_isOpen hUopen
  K.quotient_finite_of_isOpen hKopen

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTopologicalGroup
  signature: G] [CompactSpace G] (U
  body: quotient_finite_of_isOpen' U.toSubgroup K.toSubgroup U.isOpen K.isOpen

中文:
实例 [IsTopologicalGroup
  签名: G] [CompactSpace G] (U
  定义体: quotient_finite_of_isOpen' U.toSubgroup K.toSubgroup U.isOpen K.isOpen

Depends on / 依赖: K.isOpen, K.toSubgroup, U.isOpen, U.toSubgroup, isOpen, quotient_finite_of_isOpen, toSubgroup
-/
instance [IsTopologicalGroup G] [CompactSpace G] (U : OpenSubgroup G) (K : OpenSubgroup U) :
    Finite (U ⧸ K.toSubgroup) :=
  quotient_finite_of_isOpen' U.toSubgroup K.toSubgroup U.isOpen K.isOpen

end Subgroup

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (OpenSubgroup G)
  body: ⟨fun U V => ⟨U ⊔ V, Subgroup.isOpen_mono (le_sup_left : U.1 <= U.1 ⊔ V.1) U.isOpen⟩⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 :
  签名: Max (OpenSubgroup G)
  定义体: ⟨fun U V => ⟨U ⊔ V, Subgroup.isOpen_mono (le_sup_left : U.1 <= U.1 ⊔ V.1) U.isOpen⟩⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Subgroup, Subgroup.isOpen_mono, U.isOpen, isOpen, isOpen_mono, le_sup_left
-/
instance : Max (OpenSubgroup G) :=
  ⟨fun U V => ⟨U ⊔ V, Subgroup.isOpen_mono (le_sup_left : U.1 <= U.1 ⊔ V.1) U.isOpen⟩⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `toSubgroup_sup` / 定理 `toSubgroup_sup`

English:
theorem toSubgroup_sup
  given: (U V : OpenSubgroup G)
  statement: (↑(U ⊔ V) : Subgroup G) = ↑U ⊔ ↑V
  proof: rfl

@[to_additive]

中文:
定理 toSubgroup_sup
  条件: (U V : OpenSubgroup G)
  结论: (↑(U ⊔ V) : Subgroup G) = ↑U ⊔ ↑V
  证明: rfl

@[to_additive]
-/
theorem toSubgroup_sup (U V : OpenSubgroup G) : (↑(U ⊔ V) : Subgroup G) = ↑U ⊔ ↑V := rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lattice (OpenSubgroup G)
  body: toSubgroup_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl
  __ := instSemilatticeInfOpenSubgroup

中文:
实例 :
  签名: Lattice (OpenSubgroup G)
  定义体: toSubgroup_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl
  __ := instSemilatticeInfOpenSubgroup

Depends on / 依赖: semilatticeSup, toSubgroup_injective, toSubgroup_injective.semilatticeSup
-/
instance : Lattice (OpenSubgroup G) where
  __ := toSubgroup_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl
  __ := instSemilatticeInfOpenSubgroup

end OpenSubgroup

namespace Submodule

open OpenAddSubgroup

variable {R : Type*} {M : Type*} [CommRing R]
variable [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [Module R M]

/--
theorem `isOpen_mono` / 定理 `isOpen_mono`

English:
theorem isOpen_mono
  given: {U P : Submodule R M} (h : U <= P) (hU : IsOpen (U : Set M))
  proof: @AddSubgroup.isOpen_mono M _ _ _ U.toAddSubgroup P.toAddSubgroup h hU

中文:
定理 isOpen_mono
  条件: {U P : Submodule R M} (h : U <= P) (hU : IsOpen (U : Set M))
  证明: @AddSubgroup.isOpen_mono M _ _ _ U.toAddSubgroup P.toAddSubgroup h hU

Depends on / 依赖: AddSubgroup, AddSubgroup.isOpen_mono, P.toAddSubgroup, U.toAddSubgroup, isOpen_mono, toAddSubgroup
-/
theorem isOpen_mono {U P : Submodule R M} (h : U <= P) (hU : IsOpen (U : Set M)) :
    IsOpen (P : Set M) :=
  @AddSubgroup.isOpen_mono M _ _ _ U.toAddSubgroup P.toAddSubgroup h hU

end Submodule

namespace Ideal

variable {R : Type*} [CommRing R]
variable [TopologicalSpace R] [IsTopologicalRing R]

/--
theorem `isOpen_of_isOpen_subideal` / 定理 `isOpen_of_isOpen_subideal`

English:
theorem isOpen_of_isOpen_subideal
  given: {U I : Ideal R} (h : U <= I) (hU : IsOpen (U : Set R))
  proof: @Submodule.isOpen_mono R R _ _ _ _ Semiring.toModule _ _ h hU

中文:
定理 isOpen_of_isOpen_subideal
  条件: {U I : Ideal R} (h : U <= I) (hU : IsOpen (U : Set R))
  证明: @Submodule.isOpen_mono R R _ _ _ _ Semiring.toModule _ _ h hU

Depends on / 依赖: Semiring, Semiring.toModule, Submodule, Submodule.isOpen_mono, isOpen_mono, toModule
-/
theorem isOpen_of_isOpen_subideal {U I : Ideal R} (h : U <= I) (hU : IsOpen (U : Set R)) :
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
/--
Definition of `OpenNormalSubgroup` / `OpenNormalSubgroup` 的定义

English:
structure OpenNormalSubgroup
  parameters: (G : Type u) [Group G] [TopologicalSpace G]
  extends: OpenSubgroup G
  axioms and operations (1):
    - isNormal' : toSubgroup.Normal  [default: by infer_instance]

中文:
结构 OpenNormalSubgroup
  参数: (G : 类型u) [Group G] [TopologicalSpace G]
  继承: OpenSubgroup G
  公理与运算 (1 个):
    - isNormal' : toSubgroup.Normal  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
structure OpenNormalSubgroup (G : Type u) [Group G] [TopologicalSpace G]
  extends OpenSubgroup G where
  isNormal' : toSubgroup.Normal := by infer_instance

/-- The type of open normal subgroups of a topological additive group. -/
@[ext]
/--
Definition of `OpenNormalAddSubgroup` / `OpenNormalAddSubgroup` 的定义

English:
structure OpenNormalAddSubgroup
  parameters: (G : Type u) [AddGroup G] [TopologicalSpace G]
  extends: OpenAddSubgroup G
  axioms and operations (1):
    - isNormal' : toAddSubgroup.Normal  [default: by infer_instance]

中文:
结构 OpenNormalAddSubgroup
  参数: (G : 类型u) [AddGroup G] [TopologicalSpace G]
  继承: OpenAddSubgroup G
  公理与运算 (1 个):
    - isNormal' : toAddSubgroup.Normal  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
structure OpenNormalAddSubgroup (G : Type u) [AddGroup G] [TopologicalSpace G]
  extends OpenAddSubgroup G where
  isNormal' : toAddSubgroup.Normal := by infer_instance

attribute [to_additive] OpenNormalSubgroup

namespace OpenNormalSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G]

@[to_additive]
instance (H : OpenNormalSubgroup G) : H.toSubgroup.Normal := H.isNormal'

@[to_additive]
/--
theorem `toSubgroup_injective` / 定理 `toSubgroup_injective`

English:
theorem toSubgroup_injective
  statement: Function.Injective
  proof: fun A B h => by
  ext
  dsimp at h
  rw [h]

@[to_additive]

中文:
定理 toSubgroup_injective
  结论: Function.Injective
  证明: fun A B h => by
  ext
  dsimp at h
  rw [h]

@[to_additive]
-/
theorem toSubgroup_injective : Function.Injective
    (fun H => H.toOpenSubgroup.toSubgroup : OpenNormalSubgroup G -> Subgroup G) :=
  fun A B h => by
  ext
  dsimp at h
  rw [h]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (OpenNormalSubgroup G) G
  body: U.1
coe_injective _ _ h := toSubgroup_injective SetLike.ext' h

中文:
实例 :
  签名: SetLike (OpenNormalSubgroup G) G
  定义体: U.1
coe_injective _ _ h := toSubgroup_injective SetLike.ext' h
-/
instance : SetLike (OpenNormalSubgroup G) G where
  coe U := U.1
coe_injective _ _ h := toSubgroup_injective SetLike.ext' h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (OpenNormalSubgroup G)
  body: .ofSetLike (OpenNormalSubgroup G) G

@[to_additive]

中文:
实例 :
  签名: PartialOrder (OpenNormalSubgroup G)
  定义体: .ofSetLike (OpenNormalSubgroup G) G

@[to_additive]
-/
@[to_additive] instance : PartialOrder (OpenNormalSubgroup G) := .ofSetLike (OpenNormalSubgroup G) G

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubgroupClass (OpenNormalSubgroup G) G
  body: Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]

中文:
实例 :
  签名: SubgroupClass (OpenNormalSubgroup G) G
  定义体: Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]

Depends on / 依赖: Subsemigroup, Subsemigroup.mul_mem, mul_mem
-/
instance : SubgroupClass (OpenNormalSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (OpenNormalSubgroup G) (Subgroup G)
  body: H.toOpenSubgroup.toSubgroup

@[to_additive]

中文:
实例 :
  签名: Coe (OpenNormalSubgroup G) (Subgroup G)
  定义体: H.toOpenSubgroup.toSubgroup

@[to_additive]

Depends on / 依赖: H.toOpenSubgroup.toSubgroup, toOpenSubgroup, toSubgroup
-/
instance : Coe (OpenNormalSubgroup G) (Subgroup G) where
  coe H := H.toOpenSubgroup.toSubgroup

@[to_additive]
/--
Instance `instPartialOrderOpenNormalSubgroup` / 实例 `instPartialOrderOpenNormalSubgroup`

English:
instance instPartialOrderOpenNormalSubgroup
  signature: : PartialOrder (OpenNormalSubgroup G)
  body: inferInstance

@[to_additive]

中文:
实例 instPartialOrderOpenNormalSubgroup
  签名: : PartialOrder (OpenNormalSubgroup G)
  定义体: inferInstance

@[to_additive]
-/
instance instPartialOrderOpenNormalSubgroup : PartialOrder (OpenNormalSubgroup G) := inferInstance

@[to_additive]
/--
Instance `instInfOpenNormalSubgroup` / 实例 `instInfOpenNormalSubgroup`

English:
instance instInfOpenNormalSubgroup
  signature: : Min (OpenNormalSubgroup G)
  body: ⟨fun U V => ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup,
    Subgroup.normal_inf_normal U.toSubgroup V.toSubgroup⟩⟩

@[to_additive]

中文:
实例 instInfOpenNormalSubgroup
  签名: : Min (OpenNormalSubgroup G)
  定义体: ⟨fun U V => ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup,
    Subgroup.normal_inf_normal U.toSubgroup V.toSubgroup⟩⟩

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.normal_inf_normal, U.toOpenSubgroup, U.toSubgroup, V.toOpenSubgroup, V.toSubgroup, normal_inf_normal, toOpenSubgroup, toSubgroup
-/
instance instInfOpenNormalSubgroup : Min (OpenNormalSubgroup G) :=
  ⟨fun U V => ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup,
    Subgroup.normal_inf_normal U.toSubgroup V.toSubgroup⟩⟩

@[to_additive]
/--
Instance `instSemilatticeInfOpenNormalSubgroup` / 实例 `instSemilatticeInfOpenNormalSubgroup`

English:
instance instSemilatticeInfOpenNormalSubgroup
  signature: : SemilatticeInf (OpenNormalSubgroup G)
  body: SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[to_additive]

中文:
实例 instSemilatticeInfOpenNormalSubgroup
  签名: : SemilatticeInf (OpenNormalSubgroup G)
  定义体: SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[to_additive]

Depends on / 依赖: SetLike, SetLike.coe_injective.semilatticeInf, coe_injective, semilatticeInf
-/
instance instSemilatticeInfOpenNormalSubgroup : SemilatticeInf (OpenNormalSubgroup G) :=
  SetLike.coe_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SeparatelyContinuousMul
  signature: G] : Max (OpenNormalSubgroup G)
  body: ⟨fun U V => ⟨U.toOpenSubgroup ⊔ V.toOpenSubgroup,
    Subgroup.sup_normal U.toOpenSubgroup.1 V.toOpenSubgroup.1⟩⟩

@[to_additive]

中文:
实例 [SeparatelyContinuousMul
  签名: G] : Max (OpenNormalSubgroup G)
  定义体: ⟨fun U V => ⟨U.toOpenSubgroup ⊔ V.toOpenSubgroup,
    Subgroup.sup_normal U.toOpenSubgroup.1 V.toOpenSubgroup.1⟩⟩

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.sup_normal, U.toOpenSubgroup, V.toOpenSubgroup, sup_normal, toOpenSubgroup
-/
instance [SeparatelyContinuousMul G] : Max (OpenNormalSubgroup G) :=
  ⟨fun U V => ⟨U.toOpenSubgroup ⊔ V.toOpenSubgroup,
    Subgroup.sup_normal U.toOpenSubgroup.1 V.toOpenSubgroup.1⟩⟩

@[to_additive]
/--
Instance `instSemilatticeSupOpenNormalSubgroup` / 实例 `instSemilatticeSupOpenNormalSubgroup`

English:
instance instSemilatticeSupOpenNormalSubgroup
  signature: [SeparatelyContinuousMul G]
  body: toSubgroup_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[to_additive]

中文:
实例 instSemilatticeSupOpenNormalSubgroup
  签名: [SeparatelyContinuousMul G]
  定义体: toSubgroup_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[to_additive]

Depends on / 依赖: semilatticeSup, toSubgroup_injective, toSubgroup_injective.semilatticeSup
-/
instance instSemilatticeSupOpenNormalSubgroup [SeparatelyContinuousMul G] :
    SemilatticeSup (OpenNormalSubgroup G) :=
  toSubgroup_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SeparatelyContinuousMul
  signature: G] : Lattice (OpenNormalSubgroup G) where

中文:
实例 [SeparatelyContinuousMul
  签名: G] : Lattice (OpenNormalSubgroup G) where
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

/--
Definition of `IsTopologicalAddGroup.addNegClosureNhd` / `IsTopologicalAddGroup.addNegClosureNhd` 的定义

English:
structure IsTopologicalAddGroup.addNegClosureNhd
  parameters: (T W : Set G) [AddGroup G]
  axioms and operations (4):
    - nhds : T in 𝓝 0
    - neg : -T = T
    - isOpen : IsOpen T
    - add : W + T subseteq W

中文:
结构 IsTopologicalAddGroup.addNegClosureNhd
  参数: (T W : Set G) [AddGroup G]
  公理与运算 (4 个):
    - nhds : T in 𝓝 0
    - neg : -T = T
    - isOpen : IsOpen T
    - add : W + T subseteq W
-/
structure IsTopologicalAddGroup.addNegClosureNhd (T W : Set G) [AddGroup G] : Prop where
  nhds : T in 𝓝 0
  neg : -T = T
  isOpen : IsOpen T
  add : W + T subseteq W

/-- For a set `W`, `T` is a neighborhood of `1` which is open, stable under inverse and satisfies
`T * W ⊆ W`. -/
@[to_additive]
/--
Definition of `IsTopologicalGroup.mulInvClosureNhd` / `IsTopologicalGroup.mulInvClosureNhd` 的定义

English:
structure IsTopologicalGroup.mulInvClosureNhd
  parameters: (T W : Set G) [Group G]
  axioms and operations (4):
    - nhds : T in 𝓝 1
    - inv : T⁻¹ = T
    - isOpen : IsOpen T
    - mul : W * T subseteq W

中文:
结构 IsTopologicalGroup.mulInvClosureNhd
  参数: (T W : Set G) [Group G]
  公理与运算 (4 个):
    - nhds : T in 𝓝 1
    - inv : T⁻¹ = T
    - isOpen : IsOpen T
    - mul : W * T subseteq W
-/
structure IsTopologicalGroup.mulInvClosureNhd (T W : Set G) [Group G] : Prop where
  nhds : T in 𝓝 1
  inv : T⁻¹ = T
  isOpen : IsOpen T
  mul : W * T subseteq W

namespace IsTopologicalGroup

variable [Group G] [IsTopologicalGroup G] [CompactSpace G]

open Set Filter

@[to_additive]
/--
lemma `exist_mul_closure_nhds` / 引理 `exist_mul_closure_nhds`

English:
lemma exist_mul_closure_nhds
  given: {W : Set G} (WClopen : IsClopen W)
  statement: exists T in 𝓝 (1 : G), W * T subseteq W
  proof: by
  apply WClopen.isClosed.isCompact.induction_on (p := fun S => exists T in 𝓝 (1 : G), S * T subseteq W)
    ⟨Set.univ, by simp only [univ_mem, empty_mul, empty_subset, and_self]⟩
    (fun _ _ huv ⟨T, hT, mem⟩ => ⟨T, hT, (mul_subset_mul_right huv).trans mem⟩)
    fun U V ⟨T₁, hT₁, mem1⟩ ⟨T₂, hT₂, 

中文:
引理 exist_mul_closure_nhds
  条件: {W : Set G} (WClopen : IsClopen W)
  结论: 存在 T in 𝓝 (1 : G), W * T subseteq W
  证明: by
  apply WClopen.isClosed.isCompact.induction_on (p := fun S => exists T in 𝓝 (1 : G), S * T subseteq W)
    ⟨Set.univ, by simp only [univ_mem, empty_mul, empty_subset, and_self]⟩
    (fun _ _ huv ⟨T, hT, mem⟩ => ⟨T, hT, (mul_subset_mul_right huv).trans mem⟩)
    fun U V ⟨T₁, hT₁, mem1⟩ ⟨T₂, hT₂, 

Depends on / 依赖: Set.univ, WClopen, WClopen.isClosed.isCompact.induction_on, and_self, empty_mul, empty_subset, induction_on, inter_mem, inter_subset_left, inter_subset_right, isClosed, isCompact, mul_subset_mul_left, mul_subset_mul_right, subseteq, union_mul, union_subset, univ_mem
-/
lemma exist_mul_closure_nhds {W : Set G} (WClopen : IsClopen W) : exists T in 𝓝 (1 : G), W * T subseteq W := by
  apply WClopen.isClosed.isCompact.induction_on (p := fun S => exists T in 𝓝 (1 : G), S * T subseteq W)
    ⟨Set.univ, by simp only [univ_mem, empty_mul, empty_subset, and_self]⟩
    (fun _ _ huv ⟨T, hT, mem⟩ => ⟨T, hT, (mul_subset_mul_right huv).trans mem⟩)
    fun U V ⟨T₁, hT₁, mem1⟩ ⟨T₂, hT₂, mem2⟩ => ⟨T₁ inter T₂, inter_mem hT₁ hT₂, by
      rw [union_mul]
      exact union_subset (mul_subset_mul_left inter_subset_left |>.trans mem1)
        (mul_subset_mul_left inter_subset_right |>.trans mem2) ⟩
  intro x memW
  have : (x, 1) in (fun p => p.1 * p.2) ⁻¹' W := by simp [memW]
  rcases isOpen_prod_iff.mp (continuous_mul.isOpen_preimage W <| WClopen.2) x 1 this with
    ⟨U, V, Uopen, Vopen, xmemU, onememV, prodsub⟩
  have h6 : U * V subseteq W := mul_subset_iff.mpr (fun _ hx _ hy => prodsub (mk_mem_prod hx hy))
  exact ⟨U inter W, ⟨U, Uopen.mem_nhds xmemU, W, fun _ a => a, rfl⟩,
    V, IsOpen.mem_nhds Vopen onememV, fun _ a => h6 ((mul_subset_mul_right inter_subset_left) a)⟩

@[to_additive]
/--
lemma `exists_mulInvClosureNhd` / 引理 `exists_mulInvClosureNhd`

English:
lemma exists_mulInvClosureNhd
  given: {W : Set G} (WClopen : IsClopen W)
  proof: by
  rcases exist_mul_closure_nhds WClopen with ⟨S, Smemnhds, mulclose⟩
  rcases mem_nhds_iff.mp Smemnhds with ⟨U, UsubS, Uopen, onememU⟩
  use U inter U⁻¹
  constructor
  · simp [Uopen.mem_nhds onememU, inv_mem_nhds_one]
  · simp [inter_comm]
  · exact Uopen.inter Uopen.inv
  · exact fun a ha => mu

中文:
引理 exists_mulInvClosureNhd
  条件: {W : Set G} (WClopen : IsClopen W)
  证明: by
  rcases exist_mul_closure_nhds WClopen with ⟨S, Smemnhds, mulclose⟩
  rcases mem_nhds_iff.mp Smemnhds with ⟨U, UsubS, Uopen, onememU⟩
  use U inter U⁻¹
  constructor
  · simp [Uopen.mem_nhds onememU, inv_mem_nhds_one]
  · simp [inter_comm]
  · exact Uopen.inter Uopen.inv
  · exact fun a ha => mu

Depends on / 依赖: Smemnhds, Uopen.inter, Uopen.inv, Uopen.mem_nhds, WClopen, exist_mul_closure_nhds, inter_comm, inter_subset_left, inv_mem_nhds_one, mem_nhds, mem_nhds_iff, mem_nhds_iff.mp, mul_subset_mul_left, mulclose, onememU
-/
lemma exists_mulInvClosureNhd {W : Set G} (WClopen : IsClopen W) :
    exists T, mulInvClosureNhd T W := by
  rcases exist_mul_closure_nhds WClopen with ⟨S, Smemnhds, mulclose⟩
  rcases mem_nhds_iff.mp Smemnhds with ⟨U, UsubS, Uopen, onememU⟩
  use U inter U⁻¹
  constructor
  · simp [Uopen.mem_nhds onememU, inv_mem_nhds_one]
  · simp [inter_comm]
  · exact Uopen.inter Uopen.inv
  · exact fun a ha => mulclose (mul_subset_mul_left UsubS (mul_subset_mul_left inter_subset_left ha))

@[to_additive]
/--
theorem `exist_openSubgroup_sub_clopen_nhds_of_one` / 定理 `exist_openSubgroup_sub_clopen_nhds_of_one`

English:
theorem exist_openSubgroup_sub_clopen_nhds_of_one
  statement: {G : Type*} [Group G] [TopologicalSpace G]
  proof: by
  rcases exists_mulInvClosureNhd WClopen with ⟨V, hV⟩
  let S : Subgroup G := {
    carrier := ⋃ n, V ^ (n + 1)
    mul_mem' := fun ha hb => by
      rcases mem_iUnion.mp ha with ⟨k, hk⟩
      rcases mem_iUnion.mp hb with ⟨l, hl⟩
      apply mem_iUnion.mpr
      use k + 1 + l
      rw [add_assoc]

中文:
定理 exist_openSubgroup_sub_clopen_nhds_of_one
  结论: {G : 类型} [Group G] [TopologicalSpace G]
  证明: by
  rcases exists_mulInvClosureNhd WClopen with ⟨V, hV⟩
  let S : Subgroup G := {
    carrier := ⋃ n, V ^ (n + 1)
    mul_mem' := fun ha hb => by
      rcases mem_iUnion.mp ha with ⟨k, hk⟩
      rcases mem_iUnion.mp hb with ⟨l, hl⟩
      apply mem_iUnion.mpr
      use k + 1 + l
      rw [add_assoc]

Depends on / 依赖: Set.mul_mem_mul, Subgroup, WClopen, add_assoc, carrier, exists_mulInvClosureNhd, hV.inv, hV.nhds, inv_mem, inv_pow, mem_iUnion, mem_iUnion.mp, mem_iUnion.mpr, mem_of_mem_nhds, mul_mem, mul_mem_mul, one_mem, pow_add
-/
theorem exist_openSubgroup_sub_clopen_nhds_of_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 in W) :
    exists H : OpenSubgroup G, (H : Set G) subseteq W := by
  rcases exists_mulInvClosureNhd WClopen with ⟨V, hV⟩
  let S : Subgroup G := {
    carrier := ⋃ n, V ^ (n + 1)
    mul_mem' := fun ha hb => by
      rcases mem_iUnion.mp ha with ⟨k, hk⟩
      rcases mem_iUnion.mp hb with ⟨l, hl⟩
      apply mem_iUnion.mpr
      use k + 1 + l
      rw [add_assoc]; rw [pow_add]
      exact Set.mul_mem_mul hk hl
    one_mem' := by
      apply mem_iUnion.mpr
      use 0
      simp [mem_of_mem_nhds hV.nhds]
    inv_mem' := fun ha => by
      rcases mem_iUnion.mp ha with ⟨k, hk⟩
      apply mem_iUnion.mpr
      use k
      rw [← hV.inv]
      simpa only [inv_pow, Set.mem_inv, inv_inv] using hk }
  have : IsOpen (⋃ n, V ^ (n + 1)) := by
    refine isOpen_iUnion (fun n => ?_)
    rw [pow_succ]
    exact hV.isOpen.mul_left
  use ⟨S, this⟩
  have mulVpow (n : Nat) : W * V ^ (n + 1) subseteq W := by
    induction n with
    | zero => simp [hV.mul]
    | succ n ih =>
      rw [pow_succ]; rw [← mul_assoc]
      exact (Set.mul_subset_mul_right ih).trans hV.mul
  have (n : Nat) : V ^ (n + 1) subseteq W * V ^ (n + 1) := by
    intro x xin
    rw [Set.mem_mul]
    use 1, einW, x, xin
    rw [one_mul]
  apply iUnion_subset fun i _ a => mulVpow i (this i a)

end IsTopologicalGroup
