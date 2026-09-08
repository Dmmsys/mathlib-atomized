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

/-- A group topology on a group `α` is a topology for which multiplication and inversion
are continuous. -/
/-
**GroupTopology** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [Group α] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A group topology on a group `α` is a topology for which multiplication and inver
sion
are continuous.
-/
structure GroupTopology (α : Type u) [Group α] : Type u
  extends TopologicalSpace α, IsTopologicalGroup α

/-- An additive group topology on an additive group `α` is a topology for which addition and
negation are continuous. -/
/-
**AddGroupTopology** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → [AddGroup α] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive group topology on an additive group `α` is a topology for which addi
tion and
negation are continuous.
-/
structure AddGroupTopology (α : Type u) [AddGroup α] : Type u
  extends TopologicalSpace α, IsTopologicalAddGroup α

attribute [to_additive] GroupTopology

namespace GroupTopology

variable [Group α]

/-- A version of the global `continuous_mul` suitable for dot notation. -/
@[to_additive /-- A version of the global `continuous_add` suitable for dot notation. -/]
/-
**GroupTopology.continuous_mul'** 是 Mathlib 中的一个定理，位于命名空间 `GroupTopology`。
形式化陈述：continuous_mul' (g : GroupTopology α) : haveI
参数：g : GroupTopology α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupTopology.toIsTopologicalGroup`：∀ {α : Type u} [inst : Group α] (sel
f : GroupTopology α), IsTopologicalGroup α
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G

--- 原说明 ---
A version of the global `continuous_mul` suitable for dot notation.
-/
theorem continuous_mul' (g : GroupTopology α) :
    haveI := g.toTopologicalSpace
    Continuous fun p : α × α => p.1 * p.2 := by
  let := g.toTopologicalSpace
  have := g.toIsTopologicalGroup
  exact continuous_mul

/-- A version of the global `continuous_inv` suitable for dot notation. -/
@[to_additive /-- A version of the global `continuous_neg` suitable for dot notation. -/]
/-
**GroupTopology.continuous_inv'** 是 Mathlib 中的一个定理，位于命名空间 `GroupTopology`。
形式化陈述：continuous_inv' (g : GroupTopology α) : haveI
参数：g : GroupTopology α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupTopology.toIsTopologicalGroup`：∀ {α : Type u} [inst : Group α] (sel
f : GroupTopology α), IsTopologicalGroup α
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G

--- 原说明 ---
A version of the global `continuous_inv` suitable for dot notation.
-/
theorem continuous_inv' (g : GroupTopology α) :
    haveI := g.toTopologicalSpace
    Continuous (Inv.inv : α → α) := by
  let := g.toTopologicalSpace
  have := g.toIsTopologicalGroup
  exact continuous_inv

@[to_additive]
/-
**GroupTopology.toTopologicalSpace_injective** 是 Mathlib 中的一个定理，位于命名空间 `GroupTop
ology`。
形式化陈述：toTopologicalSpace_injective : Function.Injective (toTopologicalSpace : Gr
oupTopology α -> TopologicalSpace α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toTopologicalSpace_injective :
    Function.Injective (toTopologicalSpace : GroupTopology α → TopologicalSpace α) :=
  fun f g h => by
    cases f
    cases g
    congr

@[to_additive (attr := ext)]
/-
**GroupTopology.ext'** 是 Mathlib 中的一个定理，位于命名空间 `GroupTopology`。
形式化陈述：ext' {f g : GroupTopology α} (h : f.IsOpen = g.IsOpen) : f = g
参数：h : f.IsOpen = g.IsOpen。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupTopology.toTopologicalSpace_injective`：toTopologicalSpace_injective
 : Function.Injective (toTopologicalSpace : GroupTopology α -> TopologicalSpace 
α)
· 使用定理 `TopologicalSpace.ext`：∀ {X : Type u} {f g : TopologicalSpace X}, IsOpen 
= IsOpen → f = g
-/
theorem ext' {f g : GroupTopology α} (h : f.IsOpen = g.IsOpen) : f = g :=
  toTopologicalSpace_injective <| TopologicalSpace.ext h

/-- The ordering on group topologies on the group `γ`. `t ≤ s` if every set open in `s` is also open
in `t` (`t` is finer than `s`). -/
@[to_additive
  /-- The ordering on group topologies on the group `γ`. `t ≤ s` if every set open in `s`
  is also open in `t` (`t` is finer than `s`). -/]
/-
**GroupTopology.** 是 Mathlib 中的一个实例，位于命名空间 `GroupTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (GroupTopology α) :=
  PartialOrder.lift toTopologicalSpace toTopologicalSpace_injective

@[to_additive (attr := simp)]
/-
**GroupTopology.toTopologicalSpace_le** 是 Mathlib 中的一个定理，位于命名空间 `GroupTopology`。
形式化陈述：toTopologicalSpace_le {x y : GroupTopology α} : x.toTopologicalSpace <= y.
toTopologicalSpace ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toTopologicalSpace_le {x y : GroupTopology α} :
    x.toTopologicalSpace ≤ y.toTopologicalSpace ↔ x ≤ y :=
  Iff.rfl

@[to_additive]
/-
**GroupTopology.** 是 Mathlib 中的一个实例，位于命名空间 `GroupTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (GroupTopology α) :=
  let _t : TopologicalSpace α := ⊤
  ⟨{  continuous_mul := continuous_top
      continuous_inv := continuous_top }⟩

@[to_additive (attr := simp)]
/-
**GroupTopology.toTopologicalSpace_top** 是 Mathlib 中的一个定理，位于命名空间 `GroupTopology`
。
形式化陈述：toTopologicalSpace_top : (⊤ : GroupTopology α).toTopologicalSpace = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toTopologicalSpace_top : (⊤ : GroupTopology α).toTopologicalSpace = ⊤ :=
  rfl

@[to_additive]
/-
**GroupTopology.** 是 Mathlib 中的一个实例，位于命名空间 `GroupTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (GroupTopology α) :=
  let _t : TopologicalSpace α := ⊥
  ⟨{  continuous_mul := by
        have := discreteTopology_bot α
        fun_prop
      continuous_inv := continuous_bot }⟩

@[to_additive (attr := simp)]
/-
**GroupTopology.toTopologicalSpace_bot** 是 Mathlib 中的一个定理，位于命名空间 `GroupTopology`
。
形式化陈述：toTopologicalSpace_bot : (⊥ : GroupTopology α).toTopologicalSpace = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toTopologicalSpace_bot : (⊥ : GroupTopology α).toTopologicalSpace = ⊥ :=
  rfl

@[to_additive]
/-
**GroupTopology.** 是 Mathlib 中的一个实例，位于命名空间 `GroupTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedOrder (GroupTopology α) where
  le_top x := show x.toTopologicalSpace ≤ ⊤ from le_top
  bot_le x := show ⊥ ≤ x.toTopologicalSpace from bot_le

@[to_additive]
/-
**GroupTopology.** 是 Mathlib 中的一个实例，位于命名空间 `GroupTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (GroupTopology α) where min x y := ⟨x.1 ⊓ y.1, topologicalGroup_inf x.2 y.2⟩

@[to_additive (attr := simp)]
/-
**GroupTopology.toTopologicalSpace_inf** 是 Mathlib 中的一个定理，位于命名空间 `GroupTopology`
。
形式化陈述：toTopologicalSpace_inf (x y : GroupTopology α) : (x ⊓ y).toTopologicalSpac
e = x.toTopologicalSpace ⊓ y.toTopologicalSpace
参数：x y : GroupTopology α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toTopologicalSpace_inf (x y : GroupTopology α) :
    (x ⊓ y).toTopologicalSpace = x.toTopologicalSpace ⊓ y.toTopologicalSpace :=
  rfl

@[to_additive]
/-
**GroupTopology.** 是 Mathlib 中的一个实例，位于命名空间 `GroupTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeInf (GroupTopology α) :=
  toTopologicalSpace_injective.semilatticeInf _ .rfl .rfl toTopologicalSpace_inf

@[to_additive]
/-
**GroupTopology.** 是 Mathlib 中的一个实例，位于命名空间 `GroupTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (GroupTopology α) :=
  ⟨⊤⟩

/-- Infimum of a collection of group topologies. -/
@[to_additive /-- Infimum of a collection of additive group topologies -/]
/-
**GroupTopology.** 是 Mathlib 中的一个实例，位于命名空间 `GroupTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Infimum of a collection of group topologies.
-/
instance : InfSet (GroupTopology α) where
  sInf S :=
    ⟨sInf (toTopologicalSpace '' S), topologicalGroup_sInf <| forall_mem_image.2 fun t _ => t.2⟩

@[to_additive (attr := simp)]
/-
**GroupTopology.toTopologicalSpace_sInf** 是 Mathlib 中的一个定理，位于命名空间 `GroupTopology
`。
形式化陈述：toTopologicalSpace_sInf (s : Set (GroupTopology α)) : (sInf s).toTopologic
alSpace = sInf (toTopologicalSpace '' s)
参数：s : Set (GroupTopology α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toTopologicalSpace_sInf (s : Set (GroupTopology α)) :
    (sInf s).toTopologicalSpace = sInf (toTopologicalSpace '' s) := rfl

@[to_additive (attr := simp)]
/-
**GroupTopology.toTopologicalSpace_iInf** 是 Mathlib 中的一个定理，位于命名空间 `GroupTopology
`。
形式化陈述：toTopologicalSpace_iInf {ι} (s : ι -> GroupTopology α) : (⨅ i, s i).toTopo
logicalSpace = ⨅ i, (s i).toTopologicalSpace
参数：s : ι -> GroupTopology α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
-/
theorem toTopologicalSpace_iInf {ι} (s : ι → GroupTopology α) :
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
/-
**GroupTopology.** 是 Mathlib 中的一个实例，位于命名空间 `GroupTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteSemilatticeInf (GroupTopology α) :=
  { (inferInstance : InfSet (GroupTopology α)),
    (inferInstance : PartialOrder (GroupTopology α)) with
    isGLB_sInf _ := .of_image toTopologicalSpace_le (isGLB_sInf _) }

@[to_additive]
/-
**GroupTopology.** 是 Mathlib 中的一个实例，位于命名空间 `GroupTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**GroupTopology.coinduced** 是 Mathlib 中的一个定义，位于命名空间 `GroupTopology`。
形式化陈述：coinduced {α β : Type*} [t : TopologicalSpace α] [Group β] (f : α -> β) : 
GroupTopology β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coinduced {α β : Type*} [t : TopologicalSpace α] [Group β] (f : α → β) : GroupTopology β :=
  sInf { b : GroupTopology β | TopologicalSpace.coinduced f t ≤ b.toTopologicalSpace }

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**GroupTopology.coinduced_continuous** 是 Mathlib 中的一个定理，位于命名空间 `GroupTopology`。
形式化陈述：coinduced_continuous {α β : Type*} [t : TopologicalSpace α] [Group β] (f :
 α -> β) : Continuous[t, (coinduced f).toTopologicalSpace] f
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_sInf_rng`：continuous_sInf_rng {t₁ : TopologicalSpace α} {T : 
Set (TopologicalSpace β)} : Continuous[t₁, sInf T] f ↔ forall t in T, Continuous
[t₁, t] f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_coinduced_le`：continuous_iff_coinduced_le {t₁ : Topologic
alSpace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ coinduced f t₁ <= 
t₂
-/
theorem coinduced_continuous {α β : Type*} [t : TopologicalSpace α] [Group β] (f : α → β) :
    Continuous[t, (coinduced f).toTopologicalSpace] f := by
  rw [continuous_sInf_rng]
  rintro _ ⟨t', ht', rfl⟩
  exact continuous_iff_coinduced_le.2 ht'

end GroupTopology

