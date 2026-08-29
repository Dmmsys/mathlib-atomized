/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Group.Basic

/-!
### Lattice of group topologies

We define a type class `GroupTopology α` which endows a group `α` with a topology such that all
group operations are continuous.

Group topologies on a fixed group `α` are ordered, by reverse inclusion. They form a complete
lattice, with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : α → β` induces `coinduced f : TopologicalSpace α → GroupTopology β`.

The additive version `AddGroupTopology α` and corresponding results are provided as well.
-/

@[expose] public section

open Set Filter TopologicalSpace Function Topology Pointwise MulOpposite

universe u v w x

variable {G : Type w} {H : Type x} {α : Type u} {β : Type v}

/--
Definition of `GroupTopology` / `GroupTopology` 的定义

English:
structure GroupTopology
  parameters: (α : Type u) [Group α]
  extends: TopologicalSpace α, IsTopologicalGroup α
  (no additional axioms)

中文:
结构 GroupTopology
  参数: (α : 类型u) [Group α]
  继承: TopologicalSpace α, IsTopologicalGroup α
  (无附加公理)
-/
structure GroupTopology (α : Type u) [Group α] : Type u
  extends TopologicalSpace α, IsTopologicalGroup α

/--
Definition of `AddGroupTopology` / `AddGroupTopology` 的定义

English:
structure AddGroupTopology
  parameters: (α : Type u) [AddGroup α]
  extends: TopologicalSpace α, IsTopologicalAddGroup α
  (no additional axioms)

中文:
结构 AddGroupTopology
  参数: (α : 类型u) [AddGroup α]
  继承: TopologicalSpace α, IsTopologicalAddGroup α
  (无附加公理)
-/
structure AddGroupTopology (α : Type u) [AddGroup α] : Type u
  extends TopologicalSpace α, IsTopologicalAddGroup α

attribute [to_additive] GroupTopology

namespace GroupTopology

variable [Group α]

/-- A version of the global `continuous_mul` suitable for dot notation. -/
@[to_additive /-- A version of the global `continuous_add` suitable for dot notation. -/]
/--
theorem `continuous_mul'` / 定理 `continuous_mul'`

English:
theorem continuous_mul'
  given: (g : GroupTopology α)
  proof: g.toTopologicalSpace
    Continuous fun p : α × α => p.1 * p.2 := by
  let := g.toTopologicalSpace
  have := g.toIsTopologicalGroup
  exact continuous_mul

中文:
定理 continuous_mul'
  条件: (g : GroupTopology α)
  证明: g.toTopologicalSpace
    Continuous fun p : α × α => p.1 * p.2 := by
  let := g.toTopologicalSpace
  have := g.toIsTopologicalGroup
  exact continuous_mul

Depends on / 依赖: g.toTopologicalSpace, toTopologicalSpace
-/
theorem continuous_mul' (g : GroupTopology α) :
    haveI := g.toTopologicalSpace
    Continuous fun p : α × α => p.1 * p.2 := by
  let := g.toTopologicalSpace
  have := g.toIsTopologicalGroup
  exact continuous_mul

/-- A version of the global `continuous_inv` suitable for dot notation. -/
@[to_additive /-- A version of the global `continuous_neg` suitable for dot notation. -/]
/--
theorem `continuous_inv'` / 定理 `continuous_inv'`

English:
theorem continuous_inv'
  given: (g : GroupTopology α)
  proof: g.toTopologicalSpace
    Continuous (Inv.inv : α -> α) := by
  let := g.toTopologicalSpace
  have := g.toIsTopologicalGroup
  exact continuous_inv

@[to_additive]

中文:
定理 continuous_inv'
  条件: (g : GroupTopology α)
  证明: g.toTopologicalSpace
    Continuous (Inv.inv : α -> α) := by
  let := g.toTopologicalSpace
  have := g.toIsTopologicalGroup
  exact continuous_inv

@[to_additive]

Depends on / 依赖: g.toTopologicalSpace, toTopologicalSpace
-/
theorem continuous_inv' (g : GroupTopology α) :
    haveI := g.toTopologicalSpace
    Continuous (Inv.inv : α -> α) := by
  let := g.toTopologicalSpace
  have := g.toIsTopologicalGroup
  exact continuous_inv

@[to_additive]
/--
theorem `toTopologicalSpace_injective` / 定理 `toTopologicalSpace_injective`

English:
theorem toTopologicalSpace_injective
  proof: fun f g h => by
    cases f
    cases g
    congr

@[to_additive (attr := ext)]

中文:
定理 toTopologicalSpace_injective
  证明: fun f g h => by
    cases f
    cases g
    congr

@[to_additive (attr := ext)]
-/
theorem toTopologicalSpace_injective :
    Function.Injective (toTopologicalSpace : GroupTopology α -> TopologicalSpace α) :=
  fun f g h => by
    cases f
    cases g
    congr

@[to_additive (attr := ext)]
/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: {f g : GroupTopology α} (h : f.IsOpen = g.IsOpen)
  statement: f = g
  proof: toTopologicalSpace_injective TopologicalSpace.ext h

中文:
定理 ext'
  条件: {f g : GroupTopology α} (h : f.IsOpen = g.IsOpen)
  结论: f = g
  证明: toTopologicalSpace_injective TopologicalSpace.ext h

Depends on / 依赖: TopologicalSpace, TopologicalSpace.ext, toTopologicalSpace_injective
-/
theorem ext' {f g : GroupTopology α} (h : f.IsOpen = g.IsOpen) : f = g :=
toTopologicalSpace_injective TopologicalSpace.ext h

/-- The ordering on group topologies on the group `γ`. `t ≤ s` if every set open in `s` is also open
in `t` (`t` is finer than `s`). -/
@[to_additive
  /-- The ordering on group topologies on the group `γ`. `t ≤ s` if every set open in `s`
  is also open in `t` (`t` is finer than `s`). -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (GroupTopology α)
  body: PartialOrder.lift toTopologicalSpace toTopologicalSpace_injective

@[to_additive (attr := simp)]

中文:
实例 :
  签名: PartialOrder (GroupTopology α)
  定义体: PartialOrder.lift toTopologicalSpace toTopologicalSpace_injective

@[to_additive (attr := simp)]

Depends on / 依赖: PartialOrder, PartialOrder.lift, toTopologicalSpace, toTopologicalSpace_injective
-/
instance : PartialOrder (GroupTopology α) :=
  PartialOrder.lift toTopologicalSpace toTopologicalSpace_injective

@[to_additive (attr := simp)]
/--
theorem `toTopologicalSpace_le` / 定理 `toTopologicalSpace_le`

English:
theorem toTopologicalSpace_le
  given: {x y : GroupTopology α}
  proof: Iff.rfl

@[to_additive]

中文:
定理 toTopologicalSpace_le
  条件: {x y : GroupTopology α}
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem toTopologicalSpace_le {x y : GroupTopology α} :
    x.toTopologicalSpace <= y.toTopologicalSpace ↔ x <= y :=
  Iff.rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (GroupTopology α)
  body: let _t : TopologicalSpace α := ⊤
  ⟨{ continuous_mul := continuous_top
      continuous_inv := continuous_top }⟩

@[to_additive (attr := simp)]

中文:
实例 :
  签名: Top (GroupTopology α)
  定义体: let _t : TopologicalSpace α := ⊤
  ⟨{ continuous_mul := continuous_top
      continuous_inv := continuous_top }⟩

@[to_additive (attr := simp)]

Depends on / 依赖: TopologicalSpace, continuous_inv, continuous_mul, continuous_top
-/
instance : Top (GroupTopology α) :=
  let _t : TopologicalSpace α := ⊤
  ⟨{ continuous_mul := continuous_top
      continuous_inv := continuous_top }⟩

@[to_additive (attr := simp)]
/--
theorem `toTopologicalSpace_top` / 定理 `toTopologicalSpace_top`

English:
theorem toTopologicalSpace_top
  statement: (⊤ : GroupTopology α).toTopologicalSpace = ⊤
  proof: rfl

@[to_additive]

中文:
定理 toTopologicalSpace_top
  结论: (⊤ : GroupTopology α).toTopologicalSpace = ⊤
  证明: rfl

@[to_additive]
-/
theorem toTopologicalSpace_top : (⊤ : GroupTopology α).toTopologicalSpace = ⊤ :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (GroupTopology α)
  body: let _t : TopologicalSpace α := ⊥
  ⟨{ continuous_mul := by
        have := discreteTopology_bot α
        fun_prop
      continuous_inv := continuous_bot }⟩

@[to_additive (attr := simp)]

中文:
实例 :
  签名: Bot (GroupTopology α)
  定义体: let _t : TopologicalSpace α := ⊥
  ⟨{ continuous_mul := by
        have := discreteTopology_bot α
        fun_prop
      continuous_inv := continuous_bot }⟩

@[to_additive (attr := simp)]

Depends on / 依赖: TopologicalSpace, continuous_bot, continuous_inv, continuous_mul, discreteTopology_bot, fun_prop
-/
instance : Bot (GroupTopology α) :=
  let _t : TopologicalSpace α := ⊥
  ⟨{ continuous_mul := by
        have := discreteTopology_bot α
        fun_prop
      continuous_inv := continuous_bot }⟩

@[to_additive (attr := simp)]
/--
theorem `toTopologicalSpace_bot` / 定理 `toTopologicalSpace_bot`

English:
theorem toTopologicalSpace_bot
  statement: (⊥ : GroupTopology α).toTopologicalSpace = ⊥
  proof: rfl

@[to_additive]

中文:
定理 toTopologicalSpace_bot
  结论: (⊥ : GroupTopology α).toTopologicalSpace = ⊥
  证明: rfl

@[to_additive]
-/
theorem toTopologicalSpace_bot : (⊥ : GroupTopology α).toTopologicalSpace = ⊥ :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedOrder (GroupTopology α)
  body: show x.toTopologicalSpace <= ⊤ from le_top
  bot_le x := show ⊥ <= x.toTopologicalSpace from bot_le

@[to_additive]

中文:
实例 :
  签名: BoundedOrder (GroupTopology α)
  定义体: show x.toTopologicalSpace <= ⊤ from le_top
  bot_le x := show ⊥ <= x.toTopologicalSpace from bot_le

@[to_additive]

Depends on / 依赖: le_top, toTopologicalSpace, x.toTopologicalSpace
-/
instance : BoundedOrder (GroupTopology α) where
  le_top x := show x.toTopologicalSpace <= ⊤ from le_top
  bot_le x := show ⊥ <= x.toTopologicalSpace from bot_le

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (GroupTopology α)
  body: ⟨x.1 ⊓ y.1, topologicalGroup_inf x.2 y.2⟩

@[to_additive (attr := simp)]

中文:
实例 :
  签名: Min (GroupTopology α)
  定义体: ⟨x.1 ⊓ y.1, topologicalGroup_inf x.2 y.2⟩

@[to_additive (attr := simp)]

Depends on / 依赖: topologicalGroup_inf
-/
instance : Min (GroupTopology α) where min x y := ⟨x.1 ⊓ y.1, topologicalGroup_inf x.2 y.2⟩

@[to_additive (attr := simp)]
/--
theorem `toTopologicalSpace_inf` / 定理 `toTopologicalSpace_inf`

English:
theorem toTopologicalSpace_inf
  given: (x y : GroupTopology α)
  proof: rfl

@[to_additive]

中文:
定理 toTopologicalSpace_inf
  条件: (x y : GroupTopology α)
  证明: rfl

@[to_additive]
-/
theorem toTopologicalSpace_inf (x y : GroupTopology α) :
    (x ⊓ y).toTopologicalSpace = x.toTopologicalSpace ⊓ y.toTopologicalSpace :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeInf (GroupTopology α)
  body: toTopologicalSpace_injective.semilatticeInf _ .rfl .rfl toTopologicalSpace_inf

@[to_additive]

中文:
实例 :
  签名: SemilatticeInf (GroupTopology α)
  定义体: toTopologicalSpace_injective.semilatticeInf _ .rfl .rfl toTopologicalSpace_inf

@[to_additive]

Depends on / 依赖: semilatticeInf, toTopologicalSpace_inf, toTopologicalSpace_injective, toTopologicalSpace_injective.semilatticeInf
-/
instance : SemilatticeInf (GroupTopology α) :=
  toTopologicalSpace_injective.semilatticeInf _ .rfl .rfl toTopologicalSpace_inf

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (GroupTopology α)
  body: ⟨⊤⟩

中文:
实例 :
  签名: Inhabited (GroupTopology α)
  定义体: ⟨⊤⟩
-/
instance : Inhabited (GroupTopology α) :=
  ⟨⊤⟩

/-- Infimum of a collection of group topologies. -/
@[to_additive /-- Infimum of a collection of additive group topologies -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (GroupTopology α)
  body: ⟨sInf (toTopologicalSpace '' S), topologicalGroup_sInf forall_mem_image.2 fun t _ => t.2⟩

@[to_additive (attr := simp)]

中文:
实例 :
  签名: InfSet (GroupTopology α)
  定义体: ⟨sInf (toTopologicalSpace '' S), topologicalGroup_sInf forall_mem_image.2 fun t _ => t.2⟩

@[to_additive (attr := simp)]

Depends on / 依赖: forall_mem_image, toTopologicalSpace, topologicalGroup_sInf
-/
instance : InfSet (GroupTopology α) where
  sInf S :=
⟨sInf (toTopologicalSpace '' S), topologicalGroup_sInf forall_mem_image.2 fun t _ => t.2⟩

@[to_additive (attr := simp)]
/--
theorem `toTopologicalSpace_sInf` / 定理 `toTopologicalSpace_sInf`

English:
theorem toTopologicalSpace_sInf
  given: (s : Set (GroupTopology α))
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toTopologicalSpace_sInf
  条件: (s : Set (GroupTopology α))
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toTopologicalSpace_sInf (s : Set (GroupTopology α)) :
    (sInf s).toTopologicalSpace = sInf (toTopologicalSpace '' s) := rfl

@[to_additive (attr := simp)]
/--
theorem `toTopologicalSpace_iInf` / 定理 `toTopologicalSpace_iInf`

English:
theorem toTopologicalSpace_iInf
  given: {ι} (s : ι -> GroupTopology α)
  proof: congr_arg sInf (range_comp _ _).symm

中文:
定理 toTopologicalSpace_iInf
  条件: {ι} (s : ι -> GroupTopology α)
  证明: congr_arg sInf (range_comp _ _).symm

Depends on / 依赖: congr_arg, range_comp
-/
theorem toTopologicalSpace_iInf {ι} (s : ι -> GroupTopology α) :
    (⨅ i, s i).toTopologicalSpace = ⨅ i, (s i).toTopologicalSpace :=
  congr_arg sInf (range_comp _ _).symm

/-- Group topologies on `γ` form a complete lattice, with `⊥` the discrete topology and `⊤` the
indiscrete topology.

The infimum of a collection of group topologies is the topology generated by all their open sets
(which is a group topology).

The supremum of two group topologies `s` and `t` is the infimum of the family of all group
topologies contained in the intersection of `s` and `t`. -/
@[to_additive
  /-- Group topologies on `γ` form a complete lattice, with `⊥` the discrete topology and
  `⊤` the indiscrete topology.

  The infimum of a collection of group topologies is the topology generated by all their open sets
  (which is a group topology).

  The supremum of two group topologies `s` and `t` is the infimum of the family of all group
  topologies contained in the intersection of `s` and `t`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSemilatticeInf (GroupTopology α)
  body: { (inferInstance : InfSet (GroupTopology α)),
    (inferInstance : PartialOrder (GroupTopology α)) with
    isGLB_sInf _ := .of_image toTopologicalSpace_le (isGLB_sInf _) }

@[to_additive]

中文:
实例 :
  签名: CompleteSemilatticeInf (GroupTopology α)
  定义体: { (inferInstance : InfSet (GroupTopology α)),
    (inferInstance : PartialOrder (GroupTopology α)) with
    isGLB_sInf _ := .of_image toTopologicalSpace_le (isGLB_sInf _) }

@[to_additive]

Depends on / 依赖: GroupTopology, InfSet, PartialOrder, isGLB_sInf, of_image, toTopologicalSpace_le
-/
instance : CompleteSemilatticeInf (GroupTopology α) :=
  { (inferInstance : InfSet (GroupTopology α)),
    (inferInstance : PartialOrder (GroupTopology α)) with
    isGLB_sInf _ := .of_image toTopologicalSpace_le (isGLB_sInf _) }

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (GroupTopology α)
  body: { (inferInstance : BoundedOrder (GroupTopology α)),
    (inferInstance : SemilatticeInf (GroupTopology α)),
    completeLatticeOfCompleteSemilatticeInf _ with
    inf := (· ⊓ ·) }

中文:
实例 :
  签名: CompleteLattice (GroupTopology α)
  定义体: { (inferInstance : BoundedOrder (GroupTopology α)),
    (inferInstance : SemilatticeInf (GroupTopology α)),
    completeLatticeOfCompleteSemilatticeInf _ with
    inf := (· ⊓ ·) }

Depends on / 依赖: BoundedOrder, GroupTopology, SemilatticeInf, completeLatticeOfCompleteSemilatticeInf
-/
instance : CompleteLattice (GroupTopology α) :=
  { (inferInstance : BoundedOrder (GroupTopology α)),
    (inferInstance : SemilatticeInf (GroupTopology α)),
    completeLatticeOfCompleteSemilatticeInf _ with
    inf := (· ⊓ ·) }

/-- Given `f : α → β` and a topology on `α`, the coinduced group topology on `β` is the finest
topology such that `f` is continuous and `β` is a topological group. -/
@[to_additive
  /-- Given `f : α → β` and a topology on `α`, the coinduced additive group topology on `β`
  is the finest topology such that `f` is continuous and `β` is a topological additive group. -/]
/--
Definition of `coinduced` / `coinduced` 的定义

English:
definition coinduced
  signature: {α β : Type*} [t : TopologicalSpace α] [Group β] (f : α -> β)
  body: sInf { b : GroupTopology β | TopologicalSpace.coinduced f t <= b.toTopologicalSpace }

中文:
定义 coinduced
  签名: {α β : 类型} [t : TopologicalSpace α] [Group β] (f : α -> β)
  定义体: sInf { b : GroupTopology β | TopologicalSpace.coinduced f t <= b.toTopologicalSpace }

Depends on / 依赖: GroupTopology, TopologicalSpace, TopologicalSpace.coinduced, b.toTopologicalSpace, coinduced, toTopologicalSpace
-/
def coinduced {α β : Type*} [t : TopologicalSpace α] [Group β] (f : α -> β) : GroupTopology β :=
  sInf { b : GroupTopology β | TopologicalSpace.coinduced f t <= b.toTopologicalSpace }

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `coinduced_continuous` / 定理 `coinduced_continuous`

English:
theorem coinduced_continuous
  given: {α β : Type*} [t : TopologicalSpace α] [Group β] (f : α -> β)
  proof: by
  rw [continuous_sInf_rng]
  rintro _ ⟨t', ht', rfl⟩
  exact continuous_iff_coinduced_le.2 ht'

中文:
定理 coinduced_continuous
  条件: {α β : 类型} [t : TopologicalSpace α] [Group β] (f : α -> β)
  证明: by
  rw [continuous_sInf_rng]
  rintro _ ⟨t', ht', rfl⟩
  exact continuous_iff_coinduced_le.2 ht'

Depends on / 依赖: continuous_iff_coinduced_le, continuous_sInf_rng
-/
theorem coinduced_continuous {α β : Type*} [t : TopologicalSpace α] [Group β] (f : α -> β) :
    Continuous[t, (coinduced f).toTopologicalSpace] f := by
  rw [continuous_sInf_rng]
  rintro _ ⟨t', ht', rfl⟩
  exact continuous_iff_coinduced_le.2 ht'

end GroupTopology
