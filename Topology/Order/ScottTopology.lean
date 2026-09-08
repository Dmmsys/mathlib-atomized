/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Order.DirSupClosed
public import Mathlib.Order.ScottContinuity
public import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Scott topology

This file introduces the Scott topology on a preorder.

## Main definitions

- `Topology.scottHausdorff`: the Scott-Hausdorff topology is the topology whose closed sets are
  `DirSupClosed`, i.e. closed under directed suprema.
- `Topology.scott` - the Scott topology is defined as the join of the topology of upper sets and the
  Scott-Hausdorff topology (the topological space where a set `u` is open if, when the least upper
  bound of a directed set `d` lies in `u` then there is a tail of `d` which is a subset of `u`).

## Main statements

- `Topology.IsScott.isUpperSet_of_isOpen`: Scott open sets are upper.
- `Topology.IsScott.isLowerSet_of_isClosed`: Scott closed sets are lower.
- `Topology.IsScott.monotone_of_continuous`: Functions continuous w.r.t. the Scott topology are
  monotone.
- `Topology.IsScott.scottContinuousOn_iff_continuous` - a function is Scott continuous (preserves
  least upper bounds of directed sets) if and only if it is continuous w.r.t. the Scott topology.
- `Topology.IsScott.instT0Space` - the Scott topology on a partial order is T₀.

## Implementation notes

A type synonym `WithScott` is introduced and for a preorder `α`, `WithScott α` is made an instance
of `TopologicalSpace` by the `scott` topology.

We define a mixin class `IsScott` for the class of types which are both a preorder and a
topology and where the topology is the `scott` topology. It is shown that `WithScott α` is an
instance of `IsScott`.

A class `Scott` is defined in `Topology/OmegaCompletePartialOrder` and made an instance of a
topological space by defining the open sets to be those which have characteristic functions which
are monotone and preserve limits of countable chains (`OmegaCompletePartialOrder.Continuous'`).
A Scott continuous function between `OmegaCompletePartialOrder`s is always
`OmegaCompletePartialOrder.Continuous'` (`OmegaCompletePartialOrder.ScottContinuous.continuous'`).
The converse is true in some special cases, but not in general
([Domain Theory, 2.2.4][abramsky_gabbay_maibaum_1994]).

## References

* [Abramsky and Jung, *Domain Theory*][abramsky_gabbay_maibaum_1994]
* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
* [Karner, *Continuous monoids and semirings*][Karner2004]

## Tags

Scott topology, preorder
-/

@[expose] public section

open Set

variable {α β : Type*}

namespace Topology

/-! ### Scott-Hausdorff topology -/

/-- The Scott-Hausdorff topology.

A set `u` is open in the Scott-Hausdorff topology iff when the least upper bound of a directed set
`d` lies in `u` then there is a tail of `d` which is a subset of `u`.

For mild conditions on `D`, this is equivalent to saying that open sets are `DirSupInaccOn D`,
and closed sets are `DirSupClosedOn D`. -/
@[instance_reducible]
/-
**Topology.scottHausdorff** 是 Mathlib 中的一个定义，位于命名空间 `Topology`。
形式化陈述：scottHausdorff (α : Type*) (D : Set (Set α)) [Preorder α] : TopologicalSpa
ce α where IsOpen u
参数：α : Type*；D : Set (Set α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Scott-Hausdorff topology.

A set `u` is open in the Scott-Hausdorff topology iff when the least upper bound
 of a directed set
`d` lies in `u` then there is a tail of `d` which is a subset of `u`.

For mild conditions on `D`, this is equivalent to saying that open sets are `Dir
SupInaccOn D`,
and closed sets are `DirSupClosedOn D`.
-/
def scottHausdorff (α : Type*) (D : Set (Set α)) [Preorder α] : TopologicalSpace α where
  IsOpen u := ∀ ⦃d : Set α⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a : α⦄, IsLUB d a →
    a ∈ u → ∃ b ∈ d, Ici b ∩ d ⊆ u
  isOpen_univ := fun d _ ⟨b, hb⟩ _ _ _ _ ↦ ⟨b, hb, (Ici b ∩ d).subset_univ⟩
  isOpen_inter s t hs ht d hd₀ hd₁ hd₂ a hd₃ ha := by
    obtain ⟨b₁, hb₁d, hb₁ds⟩ := hs hd₀ hd₁ hd₂ hd₃ ha.1
    obtain ⟨b₂, hb₂d, hb₂dt⟩ := ht hd₀ hd₁ hd₂ hd₃ ha.2
    obtain ⟨c, hcd, hc⟩ := hd₂ b₁ hb₁d b₂ hb₂d
    exact ⟨c, hcd, fun e ⟨hce, hed⟩ ↦ ⟨hb₁ds ⟨hc.1.trans hce, hed⟩, hb₂dt ⟨hc.2.trans hce, hed⟩⟩⟩
  isOpen_sUnion := fun s h d hd₀ hd₁ hd₂ a hd₃ ⟨s₀, hs₀s, has₀⟩ ↦ by
    obtain ⟨b, hbd, hbds₀⟩ := h s₀ hs₀s hd₀ hd₁ hd₂ hd₃ has₀
    exact ⟨b, hbd, Set.subset_sUnion_of_subset s s₀ hbds₀ hs₀s⟩

/-- Predicate for an ordered topological space to be equipped with its Scott-Hausdorff topology.

A set `u` is open in the Scott-Hausdorff topology iff when the least upper bound of a directed set
`d` lies in `u` then there is a tail of `d` which is a subset of `u`.

For mild conditions on `D`, this is equivalent to saying that open sets are `DirSupInaccOn D`,
and closed sets are `DirSupClosedOn D`. -/
/-
**Topology.IsScottHausdorff** 是 Mathlib 中的一个归纳类型，位于命名空间 `Topology`。
形式化陈述：(α : Type u_3) → Set (Set α) → [Preorder α] → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate for an ordered topological space to be equipped with its Scott-Hausdor
ff topology.

A set `u` is open in the Scott-Hausdorff topology iff when the least upper bound
 of a directed set
`d` lies in `u` then there is a tail of `d` which is a subset of `u`.

For mild conditions on `D`, this is equivalent to saying that open sets are `Dir
SupInaccOn D`,
and closed sets are `DirSupClosedOn D`.
-/
class IsScottHausdorff (α) (D : Set (Set α)) [Preorder α] [TopologicalSpace α] : Prop where
  topology_eq_scottHausdorff : ‹TopologicalSpace α› = scottHausdorff α D
/-
**Topology.** 是 Mathlib 中的一个实例，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α) (D : Set (Set α)) [Preorder α] : @IsScottHausdorff α D _ (scottHausdorff α D) :=
  @IsScottHausdorff.mk _ _ _ (scottHausdorff α D) rfl

namespace IsScottHausdorff

variable {s : Set α} {D : Set (Set α)} [Preorder α] [t : TopologicalSpace α]

section General

variable [IsScottHausdorff α D]

variable (α D) in
/-
**Topology.IsScottHausdorff.topology_eq** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsSc
ottHausdorff`。
形式化陈述：topology_eq : ‹_› = scottHausdorff α D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsScottHausdorff.topology_eq_scottHausdorff`：∀ {α : Type u_3} {
D : Set (Set α)} {inst : Preorder α} {inst_1 : TopologicalSpace α}   [self : Top
ology.IsScottHausdorff α D], inst_1 = Topo…
-/
lemma topology_eq : ‹_› = scottHausdorff α D := topology_eq_scottHausdorff
/-
**Topology.IsScottHausdorff.isOpen_iff** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsSco
ttHausdorff`。
形式化陈述：isOpen_iff : IsOpen s ↔ forall ⦃d : Set α⦄, d in D -> d.Nonempty -> Direct
edOn (· <= ·) d -> forall ⦃a : α⦄, IsLUB d a -> a in s -> exists b in d, Ici b i
nter d subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsScottHausdorff.topology_eq_scottHausdorff`：∀ {α : Type u_3} {
D : Set (Set α)} {inst : Preorder α} {inst_1 : TopologicalSpace α}   [self : Top
ology.IsScottHausdorff α D], inst_1 = Topo…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isOpen_iff :
    IsOpen s ↔ ∀ ⦃d : Set α⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a : α⦄, IsLUB d a →
      a ∈ s → ∃ b ∈ d, Ici b ∩ d ⊆ s := by
  simp +instances [topology_eq_scottHausdorff (α := α) (D := D), IsOpen, scottHausdorff]
/-
**Topology.IsScottHausdorff.dirSupInaccOn_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 `T
opology.IsScottHausdorff`。
形式化陈述：dirSupInaccOn_of_isOpen (h : IsOpen s) : DirSupInaccOn D s
参数：h : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirSupInaccOn.of_inter_subset`：DirSupInaccOn.of_inter_subset (h : forall
 ⦃d : Set α⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a : α⦄, I
sLUB d a -> a in s …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Topology.IsScottHausdorff.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall ⦃d 
: Set α⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a : α⦄, IsLUB
 d a -> a in s -> exists b…
-/
lemma dirSupInaccOn_of_isOpen (h : IsOpen s) : DirSupInaccOn D s :=
  .of_inter_subset (isOpen_iff.1 h)
/-
**Topology.IsScottHausdorff.dirSupClosedOn_of_isClosed** 是 Mathlib 中的一个引理，位于命名空间
 `Topology.IsScottHausdorff`。
形式化陈述：dirSupClosedOn_of_isClosed (h : IsClosed s) : DirSupClosedOn D s
参数：h : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirSupClosedOn.of_compl`：∀ {α : Type u_1} {s : Set α} {D : Set (Set α)} 
[inst : Preorder α], DirSupInaccOn D sᶜ → DirSupClosedOn D s
· 使用引理 `Topology.IsScottHausdorff.dirSupInaccOn_of_isOpen`：dirSupInaccOn_of_isOp
en (h : IsOpen s) : DirSupInaccOn D s
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
-/
lemma dirSupClosedOn_of_isClosed (h : IsClosed s) : DirSupClosedOn D s :=
  .of_compl (dirSupInaccOn_of_isOpen h.isOpen_compl)
/-
**Topology.IsScottHausdorff.isOpen_iff_dirSupInaccOn** 是 Mathlib 中的一个定理，位于命名空间 `
Topology.IsScottHausdorff`。
形式化陈述：isOpen_iff_dirSupInaccOn (hDL : IsLowerSet D) : IsOpen s ↔ DirSupInaccOn D
 s
参数：hDL : IsLowerSet D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsScottHausdorff.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall ⦃d 
: Set α⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a : α⦄, IsLUB
 d a -> a in s -> exists b…
· 使用定理 `dirSupInaccOn_iff_inter_subset`：dirSupInaccOn_iff_inter_subset (hDL : Is
LowerSet D) : DirSupInaccOn D s ↔ forall ⦃d : Set α⦄, d in D -> d.Nonempty -> Di
rectedOn (· <= ·) d …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_iff_dirSupInaccOn (hDL : IsLowerSet D) : IsOpen s ↔ DirSupInaccOn D s := by
  rw [isOpen_iff (D := D), dirSupInaccOn_iff_inter_subset hDL]
/-
**Topology.IsScottHausdorff.isClosed_iff_dirSupClosedOn** 是 Mathlib 中的一个定理，位于命名空
间 `Topology.IsScottHausdorff`。
形式化陈述：isClosed_iff_dirSupClosedOn (hDL : IsLowerSet D) : IsClosed s ↔ DirSupClos
edOn D s
参数：hDL : IsLowerSet D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Topology.IsScottHausdorff.isOpen_iff_dirSupInaccOn`：isOpen_iff_dirSupIna
ccOn (hDL : IsLowerSet D) : IsOpen s ↔ DirSupInaccOn D s
· 使用引理 `dirSupInaccOn_compl`：dirSupInaccOn_compl : DirSupInaccOn D sᶜ ↔ DirSupCl
osedOn D s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isClosed_iff_dirSupClosedOn (hDL : IsLowerSet D) : IsClosed s ↔ DirSupClosedOn D s := by
  rw [← isOpen_compl_iff, isOpen_iff_dirSupInaccOn hDL, dirSupInaccOn_compl]
/-
**Topology.IsScottHausdorff.isOpen_of_isLowerSet** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logy.IsScottHausdorff`。
形式化陈述：isOpen_of_isLowerSet (hDL : IsLowerSet D) (h : IsLowerSet s) : IsOpen s
参数：hDL : IsLowerSet D；h : IsLowerSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.IsScottHausdorff.isOpen_iff_dirSupInaccOn`：isOpen_iff_dirSupIna
ccOn (hDL : IsLowerSet D) : IsOpen s ↔ DirSupInaccOn D s
· 使用引理 `IsLowerSet.dirSupInaccOn`：IsLowerSet.dirSupInaccOn (hs : IsLowerSet s) :
 DirSupInaccOn D s
-/
theorem isOpen_of_isLowerSet (hDL : IsLowerSet D) (h : IsLowerSet s) : IsOpen s :=
  (isOpen_iff_dirSupInaccOn hDL).2 h.dirSupInaccOn
/-
**Topology.IsScottHausdorff.isClosed_of_isUpperSet** 是 Mathlib 中的一个定理，位于命名空间 `To
pology.IsScottHausdorff`。
形式化陈述：isClosed_of_isUpperSet (hDL : IsLowerSet D) (h : IsUpperSet s) : IsClosed 
s
参数：hDL : IsLowerSet D；h : IsUpperSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.IsScottHausdorff.isClosed_iff_dirSupClosedOn`：isClosed_iff_dirS
upClosedOn (hDL : IsLowerSet D) : IsClosed s ↔ DirSupClosedOn D s
· 使用引理 `IsUpperSet.dirSupClosedOn`：IsUpperSet.dirSupClosedOn (hs : IsUpperSet s)
 : DirSupClosedOn D s
-/
theorem isClosed_of_isUpperSet (hDL : IsLowerSet D) (h : IsUpperSet s) : IsClosed s :=
  (isClosed_iff_dirSupClosedOn hDL).2 h.dirSupClosedOn

end General

section univ

variable [IsScottHausdorff α univ]

/-
**Topology.IsScottHausdorff.isOpen_iff_dirSupInacc** 是 Mathlib 中的一个定理，位于命名空间 `To
pology.IsScottHausdorff`。
形式化陈述：isOpen_iff_dirSupInacc : IsOpen s ↔ DirSupInacc s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsScottHausdorff.isOpen_iff_dirSupInaccOn`：isOpen_iff_dirSupIna
ccOn (hDL : IsLowerSet D) : IsOpen s ↔ DirSupInaccOn D s
· 使用定理 `isLowerSet_univ`：∀ {α : Type u_1} [inst : LE α], IsLowerSet Set.univ
· 使用定理 `dirSupInaccOn_univ`：∀ {α : Type u_1} {s : Set α} [inst : Preorder α], Di
rSupInaccOn Set.univ s ↔ DirSupInacc s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_iff_dirSupInacc : IsOpen s ↔ DirSupInacc s := by
  rw [isOpen_iff_dirSupInaccOn isLowerSet_univ, dirSupInaccOn_univ]
/-
**Topology.IsScottHausdorff.isClosed_iff_dirSupClosed** 是 Mathlib 中的一个定理，位于命名空间 
`Topology.IsScottHausdorff`。
形式化陈述：isClosed_iff_dirSupClosed : IsClosed s ↔ DirSupClosed s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsScottHausdorff.isClosed_iff_dirSupClosedOn`：isClosed_iff_dirS
upClosedOn (hDL : IsLowerSet D) : IsClosed s ↔ DirSupClosedOn D s
· 使用定理 `isLowerSet_univ`：∀ {α : Type u_1} [inst : LE α], IsLowerSet Set.univ
· 使用定理 `dirSupClosedOn_univ`：∀ {α : Type u_1} {s : Set α} [inst : Preorder α], D
irSupClosedOn Set.univ s ↔ DirSupClosed s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isClosed_iff_dirSupClosed : IsClosed s ↔ DirSupClosed s := by
  rw [isClosed_iff_dirSupClosedOn isLowerSet_univ, dirSupClosedOn_univ]

end univ
end IsScottHausdorff

/-! ### Scott topology -/

section Scott
section Preorder

/-- The Scott topology.

It is defined as the join of the topology of upper sets and the Scott-Hausdorff topology. -/
@[instance_reducible]
/-
**Topology.scott** 是 Mathlib 中的一个定义，位于命名空间 `Topology`。
形式化陈述：scott (α : Type*) (D : Set (Set α)) [Preorder α] : TopologicalSpace α
参数：α : Type*；D : Set (Set α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Scott topology.

It is defined as the join of the topology of upper sets and the Scott-Hausdorff 
topology.
-/
def scott (α : Type*) (D : Set (Set α)) [Preorder α] : TopologicalSpace α :=
  upperSet α ⊔ scottHausdorff α D
/-
**Topology.upperSet_le_scott** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：upperSet_le_scott [Preorder α] : upperSet α <= scott α univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
lemma upperSet_le_scott [Preorder α] : upperSet α ≤ scott α univ := le_sup_left
/-
**Topology.scottHausdorff_le_scott** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：scottHausdorff_le_scott [Preorder α] : scottHausdorff α univ <= scott α un
iv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma scottHausdorff_le_scott [Preorder α] : scottHausdorff α univ ≤ scott α univ := le_sup_right

variable (α) (D) [Preorder α] [TopologicalSpace α]

/-- Predicate for an ordered topological space to be equipped with its Scott topology.

The Scott topology is defined as the join of the topology of upper sets and the Scott Hausdorff
topology. -/
/-
**Topology.IsScott** 是 Mathlib 中的一个归纳类型，位于命名空间 `Topology`。
形式化陈述：(α : Type u_1) → Set (Set α) → [Preorder α] → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate for an ordered topological space to be equipped with its Scott topolog
y.

The Scott topology is defined as the join of the topology of upper sets and the 
Scott Hausdorff
topology.
-/
class IsScott : Prop where
  topology_eq_scott : ‹TopologicalSpace α› = scott α D

end Preorder

namespace IsScott
section Preorder
variable (α) (D) [Preorder α] [TopologicalSpace α]

/-
**Topology.IsScott.topology_eq** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsScott`。
形式化陈述：topology_eq [IsScott α D] : ‹_› = scott α D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsScott.topology_eq_scott`：∀ {α : Type u_1} {D : Set (Set α)} {
inst : Preorder α} {inst_1 : TopologicalSpace α} [self : Topology.IsScott α D], 
  inst_1 = Topology.scot…
-/
lemma topology_eq [IsScott α D] : ‹_› = scott α D := topology_eq_scott

variable {α} {D} {s : Set α} {a : α}
/-
**Topology.IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open** 是 Mathlib 中的一
个引理，位于命名空间 `Topology.IsScott`。
形式化陈述：isOpen_iff_isUpperSet_and_scottHausdorff_open [IsScott α D] : IsOpen s ↔ I
sUpperSet s ∧ IsOpen[scottHausdorff α D] s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsScott.topology_eq`：topology_eq [IsScott α D] : ‹_› = scott α 
D
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isOpen_iff_isUpperSet_and_scottHausdorff_open [IsScott α D] :
    IsOpen s ↔ IsUpperSet s ∧ IsOpen[scottHausdorff α D] s := by rw [topology_eq α D]; rfl
/-
**Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn** 是 Mathlib 中的一个引理，位于
命名空间 `Topology.IsScott`。
形式化陈述：isOpen_iff_isUpperSet_and_dirSupInaccOn [IsScott α D] : IsOpen s ↔ IsUpper
Set s ∧ DirSupInaccOn D s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open`：isOpen_i
ff_isUpperSet_and_scottHausdorff_open [IsScott α D] : IsOpen s ↔ IsUpperSet s ∧ 
IsOpen[scottHausdorff α D] s
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用引理 `Topology.IsScottHausdorff.dirSupInaccOn_of_isOpen`：dirSupInaccOn_of_isOp
en (h : IsOpen s) : DirSupInaccOn D s
· 使用定理 `Topology.instIsScottHausdorff`：∀ (α : Type u_3) (D : Set (Set α)) [inst 
: Preorder α], Topology.IsScottHausdorff α D
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `IsUpperSet.Ici_subset`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α},
 IsUpperSet s → ∀ ⦃a : α⦄, a ∈ s → Set.Ici a ⊆ s
-/
lemma isOpen_iff_isUpperSet_and_dirSupInaccOn [IsScott α D] :
    IsOpen s ↔ IsUpperSet s ∧ DirSupInaccOn D s := by
  rw [isOpen_iff_isUpperSet_and_scottHausdorff_open (D := D)]
  refine and_congr_right fun h ↦
    ⟨IsScottHausdorff.dirSupInaccOn_of_isOpen (t := scottHausdorff α D),
      fun h' d d₀ d₁ d₂ _ d₃ ha ↦ ?_⟩
  obtain ⟨b, hbd, hbu⟩ := h' d₀ d₁ d₂ d₃ ha
  exact ⟨b, hbd, Subset.trans inter_subset_left (h.Ici_subset hbu)⟩
/-
**Topology.IsScott.isClosed_iff_isLowerSet_and_dirSupClosed** 是 Mathlib 中的一个引理，位
于命名空间 `Topology.IsScott`。
形式化陈述：isClosed_iff_isLowerSet_and_dirSupClosed [IsScott α univ] : IsClosed s ↔ I
sLowerSet s ∧ DirSupClosed s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用引理 `Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn`：isOpen_iff_isU
pperSet_and_dirSupInaccOn [IsScott α D] : IsOpen s ↔ IsUpperSet s ∧ DirSupInaccO
n D s
· 使用定理 `isUpperSet_compl`：isUpperSet_compl : IsUpperSet sᶜ ↔ IsLowerSet s
· 使用定理 `dirSupInaccOn_univ`：∀ {α : Type u_1} {s : Set α} [inst : Preorder α], Di
rSupInaccOn Set.univ s ↔ DirSupInacc s
· 使用引理 `dirSupInacc_compl`：dirSupInacc_compl : DirSupInacc sᶜ ↔ DirSupClosed s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isClosed_iff_isLowerSet_and_dirSupClosed [IsScott α univ] :
    IsClosed s ↔ IsLowerSet s ∧ DirSupClosed s := by
  rw [← isOpen_compl_iff, isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ), isUpperSet_compl,
    dirSupInaccOn_univ, dirSupInacc_compl]
/-
**Topology.IsScott.isUpperSet_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsSc
ott`。
形式化陈述：isUpperSet_of_isOpen [IsScott α D] : IsOpen s -> IsUpperSet s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Topology.IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open`：isOpen_i
ff_isUpperSet_and_scottHausdorff_open [IsScott α D] : IsOpen s ↔ IsUpperSet s ∧ 
IsOpen[scottHausdorff α D] s
-/
lemma isUpperSet_of_isOpen [IsScott α D] : IsOpen s → IsUpperSet s := fun h ↦
  (isOpen_iff_isUpperSet_and_scottHausdorff_open (D := D).mp h).left
/-
**Topology.IsScott.isLowerSet_of_isClosed** 是 Mathlib 中的一个引理，位于命名空间 `Topology.Is
Scott`。
形式化陈述：isLowerSet_of_isClosed [IsScott α univ] : IsClosed s -> IsLowerSet s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Topology.IsScott.isClosed_iff_isLowerSet_and_dirSupClosed`：isClosed_iff_
isLowerSet_and_dirSupClosed [IsScott α univ] : IsClosed s ↔ IsLowerSet s ∧ DirSu
pClosed s
-/
lemma isLowerSet_of_isClosed [IsScott α univ] : IsClosed s → IsLowerSet s := fun h ↦
  (isClosed_iff_isLowerSet_and_dirSupClosed.mp h).left
/-
**Topology.IsScott.dirSupClosed_of_isClosed** 是 Mathlib 中的一个引理，位于命名空间 `Topology.
IsScott`。
形式化陈述：dirSupClosed_of_isClosed [IsScott α univ] : IsClosed s -> DirSupClosed s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Topology.IsScott.isClosed_iff_isLowerSet_and_dirSupClosed`：isClosed_iff_
isLowerSet_and_dirSupClosed [IsScott α univ] : IsClosed s ↔ IsLowerSet s ∧ DirSu
pClosed s
-/
lemma dirSupClosed_of_isClosed [IsScott α univ] : IsClosed s → DirSupClosed s := fun h ↦
  (isClosed_iff_isLowerSet_and_dirSupClosed.mp h).right
/-
**Topology.IsScott.lowerClosure_subset_closure** 是 Mathlib 中的一个引理，位于命名空间 `Topolo
gy.IsScott`。
形式化陈述：lowerClosure_subset_closure [IsScott α univ] : ↑(lowerClosure s) subseteq 
closure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsUpperSet.closure_eq_lowerClosure`：closure_eq_lowerClosure {s 
: Set α} : closure s = lowerClosure s
· 使用定理 `Topology.instIsUpperSet`：∀ {α : Type u_1} [inst : Preorder α], Topology.
IsUpperSet α
· 使用引理 `Topology.IsScott.topology_eq`：topology_eq [IsScott α D] : ‹_› = scott α 
D
· 使用定理 `closure.mono`：closure.mono (h : t₁ <= t₂) : closure[t₁] s subseteq closu
re[t₂] s
· 使用引理 `Topology.upperSet_le_scott`：upperSet_le_scott [Preorder α] : upperSet α 
<= scott α univ
-/
lemma lowerClosure_subset_closure [IsScott α univ] : ↑(lowerClosure s) ⊆ closure s := by
  convert! closure.mono (@upperSet_le_scott α _)
  · rw [@IsUpperSet.closure_eq_lowerClosure α _ (upperSet α) ?_ s]
    infer_instance
  · exact topology_eq α univ
/-
**Topology.IsScott.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.IsScott`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsScott α univ] : ClosedIicTopology α where
  isClosed_Iic _ :=
    isClosed_iff_isLowerSet_and_dirSupClosed.2 ⟨isLowerSet_Iic _, dirSupClosed_Iic _⟩

/--
The closure of a singleton `{a}` in the Scott topology is the right-closed left-infinite interval
`(-∞,a]`.
-/
/-
**Topology.IsScott.closure_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsScott
`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : TopologicalSpace α] {a : α}
 [Topology.IsScott α Set.univ],   closure {a} = Set.Iic a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iic
 b ↔ x ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `Topology.IsScott.instClosedIicTopologyOfUnivSet`：∀ {α : Type u_1} [inst 
: Preorder α] [inst_1 : TopologicalSpace α] [Topology.IsScott α Set.univ], Close
dIicTopology α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LowerSet.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] (a : α), ↑(LowerS
et.Iic a) = Set.Iic a
· 使用定理 `lowerClosure_singleton`：∀ {α : Type u_1} [inst : Preorder α] (a : α), lo
werClosure {a} = LowerSet.Iic a
· 使用引理 `Topology.IsScott.lowerClosure_subset_closure`：lowerClosure_subset_closur
e [IsScott α univ] : ↑(lowerClosure s) subseteq closure s

--- 原说明 ---
The closure of a singleton `{a}` in the Scott topology is the right-closed left-
infinite interval
`(-∞,a]`.
-/
@[simp] lemma closure_singleton [IsScott α univ] : closure {a} = Iic a := le_antisymm
  (closure_minimal (by rw [singleton_subset_iff, mem_Iic]) isClosed_Iic) <| by
    rw [← LowerSet.coe_Iic, ← lowerClosure_singleton]
    apply lowerClosure_subset_closure

variable [Preorder β] [TopologicalSpace β] [IsScott β univ] {f : α → β}
/-
**Topology.IsScott.monotone_of_continuous** 是 Mathlib 中的一个引理，位于命名空间 `Topology.Is
Scott`。
形式化陈述：monotone_of_continuous [IsScott α D] (hf : Continuous f) : Monotone f
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsScott.isUpperSet_of_isOpen`：isUpperSet_of_isOpen [IsScott α D
] : IsOpen s -> IsUpperSet s
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `Topology.IsScott.instClosedIicTopologyOfUnivSet`：∀ {α : Type u_1} [inst 
: Preorder α] [inst_1 : TopologicalSpace α] [Topology.IsScott α Set.univ], Close
dIicTopology α
-/
lemma monotone_of_continuous [IsScott α D] (hf : Continuous f) : Monotone f := fun _ b hab ↦ by
  by_contra h
  simpa only [mem_compl_iff, mem_preimage, mem_Iic, le_refl, not_true]
    using isUpperSet_of_isOpen (D := D) ((isOpen_compl_iff.2 isClosed_Iic).preimage hf) hab h
/-
**Topology.IsScott.scottContinuousOn_iff_continuous** 是 Mathlib 中的一个定理，位于命名空间 `T
opology.IsScott`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : TopologicalS
pace α] [inst_2 : Preorder β]   [inst_3 : TopologicalSpace β] [Topology.IsScott 
β Set.univ] {f : α → β} {D : Set (Set α)} [Topology.IsScott α D],   (∀ (a b : α)
, a ≤ b → {a, b} ∈ D) → (ScottContinuousOn D f ↔ Continuous f)
参数：Set α；∀ (a b : α), a ≤ b → {a, b} ∈ D；ScottContinuousOn D f ↔ Continuous f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn`：isOpen_iff_isU
pperSet_and_dirSupInaccOn [IsScott α D] : IsOpen s ↔ IsUpperSet s ∧ DirSupInaccO
n D s
· 使用定理 `IsUpperSet.preimage`：IsUpperSet.preimage (hs : IsUpperSet s) {f : β -> α
} (hf : Monotone f) : IsUpperSet (f ⁻¹' s : Set β)
· 使用引理 `Topology.IsScott.isUpperSet_of_isOpen`：isUpperSet_of_isOpen [IsScott α D
] : IsOpen s -> IsUpperSet s
· 使用定理 `ScottContinuousOn.monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : Preo
rder α] [inst_1 : Preorder β] {f : α → β} (D : Set (Set α)),   (∀ (a b : α), a ≤
 b → {a, b} ∈ D)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image_inter_nonempty_iff`：image_inter_nonempty_iff {f : α -> β} {s :
 Set α} {t : Set β} : (f '' s inter t).Nonempty ↔ (s inter f ⁻¹' t).Nonempty
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `trivial`：True
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `directedOn_image`：directedOn_image {s : Set β} {f : β -> α} : DirectedOn
 r (f '' s) ↔ DirectedOn (f ⁻¹'o r) s
· 使用定理 `DirectedOn.mono`：DirectedOn.mono {s : Set α} (h : DirectedOn r s) (H : f
orall ⦃a b⦄, r a b -> r' a b) : DirectedOn r' s
· 使用定理 `Monotone.mem_upperBounds_image`：mem_upperBounds_image (Ha : a in upperBo
unds s) : f a in upperBounds (f '' s)
· 使用引理 `Topology.IsScott.monotone_of_continuous`：monotone_of_continuous [IsScott
 α D] (hf : Continuous f) : Monotone f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `Topology.IsScott.instClosedIicTopologyOfUnivSet`：∀ {α : Type u_1} [inst 
: Preorder α] [inst_1 : TopologicalSpace α] [Topology.IsScott α Set.univ], Close
dIicTopology α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
@[simp] lemma scottContinuousOn_iff_continuous {D : Set (Set α)} [Topology.IsScott α D]
    (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D) : ScottContinuousOn D f ↔ Continuous f := by
  refine ⟨fun h ↦ continuous_def.2 fun u hu ↦ ?_, ?_⟩
  · rw [isOpen_iff_isUpperSet_and_dirSupInaccOn (D := D)]
    exact ⟨(isUpperSet_of_isOpen (D := univ) hu).preimage (h.monotone D hD),
      fun t h₀ hd₁ hd₂ a hd₃ ha ↦ image_inter_nonempty_iff.mp <|
        (isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ).mp hu).2 trivial (Nonempty.image f hd₁)
        (directedOn_image.mpr (hd₂.mono @(h.monotone D hD))) (h h₀ hd₁ hd₂ hd₃) ha⟩
  · refine fun hf t h₀ d₁ d₂ a d₃ ↦
      ⟨(monotone_of_continuous (D := D) hf).mem_upperBounds_image d₃.1,
      fun b hb ↦ ?_⟩
    by_contra h
    let u := (Iic b)ᶜ
    have hu : IsOpen (f ⁻¹' u) := isClosed_Iic.isOpen_compl.preimage hf
    rw [isOpen_iff_isUpperSet_and_dirSupInaccOn (D := D)] at hu
    obtain ⟨c, hcd, hfcb⟩ := hu.2 h₀ d₁ d₂ d₃ h
    simp only [upperBounds, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      mem_ofPred] at hb
    exact hfcb <| hb _ hcd

end Preorder

section PartialOrder
variable [PartialOrder α] [TopologicalSpace α] [IsScott α univ]

/--
The Scott topology on a partial order is T₀.
-/
-- see Note [lower instance priority]
/-
**Topology.IsScott.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.IsScott`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 90) : T0Space α :=
  (t0Space_iff_inseparable α).2 fun x y h ↦ Iic_injective <| by
    simpa only [inseparable_iff_closure_eq, IsScott.closure_singleton] using h

end PartialOrder

section CompleteLinearOrder

variable [CompleteLinearOrder α]

/-
**Topology.IsScott.isOpen_iff_Iic_compl_or_univ** 是 Mathlib 中的一个引理，位于命名空间 `Topol
ogy.IsScott`。
形式化陈述：isOpen_iff_Iic_compl_or_univ [TopologicalSpace α] [Topology.IsScott α univ
] (U : Set α) : IsOpen U ↔ U = univ ∨ exists a, (Iic a)ᶜ = U
参数：U : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.compl_empty_iff`：compl_empty_iff {s : Set α} : sᶜ = ∅ ↔ s = univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_eq_comm`：compl_eq_comm : xᶜ = y ↔ yᶜ = x
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `IsLowerSet.Iic_subset`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α},
 IsLowerSet s → ∀ ⦃a : α⦄, a ∈ s → Set.Iic a ⊆ s
· 使用引理 `Topology.IsScott.isLowerSet_of_isClosed`：isLowerSet_of_isClosed [IsScott
 α univ] : IsClosed s -> IsLowerSet s
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用引理 `dirSupClosed_iff_forall_sSup`：dirSupClosed_iff_forall_sSup : DirSupClose
d s ↔ forall ⦃d⦄, d subseteq s -> d.Nonempty -> DirectedOn (· <= ·) d -> sSup d 
in s
· 使用引理 `Topology.IsScott.dirSupClosed_of_isClosed`：dirSupClosed_of_isClosed [IsS
cott α univ] : IsClosed s -> DirSupClosed s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用定理 `isChain_of_trichotomous`：isChain_of_trichotomous [Std.Trichotomous r] (s
 : Set α) : IsChain r s
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `Topology.IsScott.instClosedIicTopologyOfUnivSet`：∀ {α : Type u_1} [inst 
: Preorder α] [inst_1 : TopologicalSpace α] [Topology.IsScott α Set.univ], Close
dIicTopology α
-/
lemma isOpen_iff_Iic_compl_or_univ [TopologicalSpace α] [Topology.IsScott α univ] (U : Set α) :
    IsOpen U ↔ U = univ ∨ ∃ a, (Iic a)ᶜ = U := by
  constructor
  · intro hU
    rcases eq_empty_or_nonempty Uᶜ with eUc | neUc
    · exact Or.inl (compl_empty_iff.mp eUc)
    · apply Or.inr
      use sSup Uᶜ
      rw [compl_eq_comm, le_antisymm_iff]
      refine ⟨fun _ ha ↦ le_sSup ha, (isLowerSet_of_isClosed hU.isClosed_compl).Iic_subset ?_⟩
      exact dirSupClosed_iff_forall_sSup.mp (dirSupClosed_of_isClosed hU.isClosed_compl) le_rfl neUc
        (isChain_of_trichotomous Uᶜ).directedOn
  · rintro (rfl | ⟨a, rfl⟩)
    · exact isOpen_univ
    · exact isClosed_Iic.isOpen_compl

-- N.B. A number of conditions equivalent to `scott α = upper α` are given in Gierz _et al_,
-- Chapter III, Exercise 3.23.
/-
**Topology.IsScott.scott_eq_upper_of_completeLinearOrder** 是 Mathlib 中的一个引理，位于命名
空间 `Topology.IsScott`。
形式化陈述：scott_eq_upper_of_completeLinearOrder : scott α univ = upper α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.ext`：∀ {X : Type u} {f g : TopologicalSpace X}, IsOpen 
= IsOpen → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsUpper.isTopologicalSpace_basis`：isTopologicalSpace_basis (U :
 Set α) : IsOpen U ↔ U = univ ∨ exists a, (Iic a)ᶜ = U
· 使用引理 `Topology.IsScott.isOpen_iff_Iic_compl_or_univ`：isOpen_iff_Iic_compl_or_u
niv [TopologicalSpace α] [Topology.IsScott α univ] (U : Set α) : IsOpen U ↔ U = 
univ ∨ exists a, (Iic a)ᶜ = U
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma scott_eq_upper_of_completeLinearOrder : scott α univ = upper α := by
  let := upper α
  ext U
  rw [@Topology.IsUpper.isTopologicalSpace_basis _ _ (upper α)
    ({ topology_eq_upperTopology := rfl }) U]
  let := scott α univ
  rw [@isOpen_iff_Iic_compl_or_univ _ _ (scott α univ) ({ topology_eq_scott := rfl }) U]

/-- The upper topology on a complete linear order is the Scott topology -/
/-
**Topology.IsScott.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.IsScott`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The upper topology on a complete linear order is the Scott topology
-/
instance [TopologicalSpace α] [IsUpper α] : IsScott α univ where
  topology_eq_scott := by
    rw [scott_eq_upper_of_completeLinearOrder]
    exact IsUpper.topology_eq α

end CompleteLinearOrder

/-
**Topology.IsScott.isOpen_iff_scottContinuous_mem** 是 Mathlib 中的一个引理，位于命名空间 `Top
ology.IsScott`。
形式化陈述：isOpen_iff_scottContinuous_mem [Preorder α] {s : Set α} [TopologicalSpace 
α] [IsScott α univ] : IsOpen s ↔ ScottContinuous fun x => x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `scottContinuousOn_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder
 α] [inst_1 : Preorder β] {f : α → β},   ScottContinuousOn Set.univ f ↔ ScottCon
tinuous f
· 使用定理 `Topology.IsScott.scottContinuousOn_iff_continuous`：∀ {α : Type u_1} {β :
 Type u_2} [inst : Preorder α] [inst_1 : TopologicalSpace α] [inst_2 : Preorder 
β]   [inst_3 : TopologicalSpace β] [Top…
· 使用定理 `Topology.IsScott.instUnivSetOfIsUpper`：∀ {α : Type u_1} [inst : Complete
LinearOrder α] [inst_1 : TopologicalSpace α] [Topology.IsUpper α],   Topology.Is
Scott α Set.univ
· 使用定理 `instIsUpperProp`：Topology.IsUpper Prop
· 使用定理 `isOpen_iff_continuous_mem`：isOpen_iff_continuous_mem {s : Set α} : IsOpe
n s ↔ Continuous (· in s)
-/
lemma isOpen_iff_scottContinuous_mem [Preorder α] {s : Set α} [TopologicalSpace α]
    [IsScott α univ] : IsOpen s ↔ ScottContinuous fun x ↦ x ∈ s := by
  rw [← scottContinuousOn_univ, scottContinuousOn_iff_continuous (fun _ _ _ ↦ by trivial)]
  exact isOpen_iff_continuous_mem

end IsScott

/--
Type synonym for a preorder equipped with the Scott topology
-/
/-
**Topology.WithScott** 是 Mathlib 中的一个定义，位于命名空间 `Topology`。
形式化陈述：WithScott (α : Type*)
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type synonym for a preorder equipped with the Scott topology
-/
def WithScott (α : Type*) := α

namespace WithScott

/-- `toScott` is the identity function to the `WithScott` of a type. -/
/-
**Topology.WithScott.toScott** 是 Mathlib 中的一个定义，位于命名空间 `Topology.WithScott`。
形式化陈述：{α : Type u_1} → α ≃ Topology.WithScott α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`toScott` is the identity function to the `WithScott` of a type.
-/
@[match_pattern] def toScott : α ≃ WithScott α := Equiv.refl _

/-- `ofScott` is the identity function from the `WithScott` of a type. -/
/-
**Topology.WithScott.ofScott** 是 Mathlib 中的一个定义，位于命名空间 `Topology.WithScott`。
形式化陈述：{α : Type u_1} → Topology.WithScott α ≃ α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`ofScott` is the identity function from the `WithScott` of a type.
-/
@[match_pattern] def ofScott : WithScott α ≃ α := Equiv.refl _
/-
**Topology.WithScott.toScott_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Topology.WithSco
tt`。
形式化陈述：∀ {α : Type u_1}, Topology.WithScott.toScott.symm = Topology.WithScott.ofS
cott
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`ofScott` is the identity function from the `WithScott` of a type.
-/
@[simp] lemma toScott_symm_eq : (@toScott α).symm = ofScott := rfl
/-
**Topology.WithScott.ofScott_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Topology.WithSco
tt`。
形式化陈述：∀ {α : Type u_1}, Topology.WithScott.ofScott.symm = Topology.WithScott.toS
cott
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`ofScott` is the identity function from the `WithScott` of a type.
-/
@[simp] lemma ofScott_symm_eq : (@ofScott α).symm = toScott := rfl
/-
**Topology.WithScott.toScott_ofScott** 是 Mathlib 中的一个定理，位于命名空间 `Topology.WithSco
tt`。
形式化陈述：∀ {α : Type u_1} (a : Topology.WithScott α), Topology.WithScott.toScott (T
opology.WithScott.ofScott a) = a
参数：a : Topology.WithScott α；Topology.WithScott.ofScott a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofScott` is the identity function from the `WithScott` of a type.
-/
@[simp] lemma toScott_ofScott (a : WithScott α) : toScott (ofScott a) = a := rfl
/-
**Topology.WithScott.ofScott_toScott** 是 Mathlib 中的一个定理，位于命名空间 `Topology.WithSco
tt`。
形式化陈述：∀ {α : Type u_1} (a : α), Topology.WithScott.ofScott (Topology.WithScott.t
oScott a) = a
参数：a : α；Topology.WithScott.toScott a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofScott` is the identity function from the `WithScott` of a type.
-/
@[simp] lemma ofScott_toScott (a : α) : ofScott (toScott a) = a := rfl
/-
**Topology.WithScott.toScott_inj** 是 Mathlib 中的一个引理，位于命名空间 `Topology.WithScott`。
形式化陈述：toScott_inj {a b : α} : toScott a = toScott b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`ofScott` is the identity function from the `WithScott` of a type.
-/
lemma toScott_inj {a b : α} : toScott a = toScott b ↔ a = b := Iff.rfl
/-
**Topology.WithScott.ofScott_inj** 是 Mathlib 中的一个引理，位于命名空间 `Topology.WithScott`。
形式化陈述：ofScott_inj {a b : WithScott α} : ofScott a = ofScott b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ofScott_inj {a b : WithScott α} : ofScott a = ofScott b ↔ a = b := Iff.rfl
/-- A recursor for `WithScott`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**Topology.WithScott.rec** 是 Mathlib 中的一个定义，位于命名空间 `Topology.WithScott`。
形式化陈述：{α : Type u_1} →   {β : Topology.WithScott α → Sort u_3} →     ((a : α) → 
β (Topology.WithScott.toScott a)) → (a : Topology.WithScott α) → β a
参数：(a : α) → β (Topology.WithScott.toScott a)；a : Topology.WithScott α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor for `WithScott`. Use as `induction x`.
-/
protected def rec {β : WithScott α → Sort _}
    (h : ∀ a, β (toScott a)) : ∀ a, β a := fun a ↦ h (ofScott a)
/-
**Topology.WithScott.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithScott`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Nonempty (WithScott α) := ‹Nonempty α›
/-
**Topology.WithScott.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithScott`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (WithScott α) := ‹Inhabited α›

variable [Preorder α]
/-
**Topology.WithScott.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithScott`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder (WithScott α) := ‹Preorder α›
/-
**Topology.WithScott.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithScott`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (WithScott α) :=
  -- fast_instance% scott α univ fails
  letI : TopologicalSpace α := scott α univ
  inferInstanceAs <| TopologicalSpace α
/-
**Topology.WithScott.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithScott`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScott (WithScott α) univ := ⟨rfl⟩
/-
**Topology.WithScott.isOpen_iff_isUpperSet_and_scottHausdorff_open'** 是 Mathlib 
中的一个引理，位于命名空间 `Topology.WithScott`。
形式化陈述：isOpen_iff_isUpperSet_and_scottHausdorff_open' {u : Set α} : IsOpen (WithS
cott.ofScott ⁻¹' u) ↔ IsUpperSet u ∧ (scottHausdorff α univ).IsOpen u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isOpen_iff_isUpperSet_and_scottHausdorff_open' {u : Set α} :
    IsOpen (WithScott.ofScott ⁻¹' u) ↔ IsUpperSet u ∧ (scottHausdorff α univ).IsOpen u := Iff.rfl

end WithScott
end Scott

variable [Preorder α]

/-
**Topology.scottHausdorff_le_lower** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：scottHausdorff_le_lower : scottHausdorff α univ <= lower α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsScottHausdorff.isOpen_of_isLowerSet`：isOpen_of_isLowerSet (hD
L : IsLowerSet D) (h : IsLowerSet s) : IsOpen s
· 使用定理 `Topology.instIsScottHausdorff`：∀ (α : Type u_3) (D : Set (Set α)) [inst 
: Preorder α], Topology.IsScottHausdorff α D
· 使用定理 `isLowerSet_univ`：∀ {α : Type u_1} [inst : LE α], IsLowerSet Set.univ
· 使用定理 `Topology.IsLower.isLowerSet_of_isOpen`：isLowerSet_of_isOpen (h : IsOpen 
s) : IsLowerSet s
· 使用定理 `Topology.instIsLowerWithLower`：∀ {α : Type u_1} [inst : Preorder α], Top
ology.IsLower (Topology.WithLower α)
-/
lemma scottHausdorff_le_lower : scottHausdorff α univ ≤ lower α :=
  let : TopologicalSpace α := scottHausdorff α univ
  fun s h ↦ IsScottHausdorff.isOpen_of_isLowerSet isLowerSet_univ <|
    @IsLower.isLowerSet_of_isOpen (Topology.WithLower α) _ _ _ s h

variable [TopologicalSpace α]

/-- If `α` is equipped with the Scott topology, then it is homeomorphic to `WithScott α`.
-/
/-
**Topology.IsScott.withScottHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Topology.IsSco
tt`。
形式化陈述：{α : Type u_1} →   [inst : Preorder α] → [inst_1 : TopologicalSpace α] → [
Topology.IsScott α Set.univ] → Topology.WithScott α ≃ₜ α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is equipped with the Scott topology, then it is homeomorphic to `WithScot
t α`.
-/
def IsScott.withScottHomeomorph [IsScott α univ] : WithScott α ≃ₜ α :=
  WithScott.ofScott.toHomeomorphOfIsInducing ⟨IsScott.topology_eq α univ ▸ induced_id.symm⟩
/-
**Topology.IsScott.scottHausdorff_le** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsScott
`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : TopologicalSpace α] [Topolo
gy.IsScott α Set.univ],   Topology.scottHausdorff α Set.univ ≤ inst_1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsScott.topology_eq`：topology_eq [IsScott α D] : ‹_› = scott α 
D
· 使用定理 `Topology.scott.eq_1`：∀ (α : Type u_3) (D : Set (Set α)) [inst : Preorder
 α],   Topology.scott α D = Topology.upperSet α ⊔ Topology.scottHausdorff α D
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma IsScott.scottHausdorff_le [IsScott α univ] :
    scottHausdorff α univ ≤ ‹TopologicalSpace α› := by
  rw [IsScott.topology_eq α univ, scott]; exact le_sup_right
/-
**Topology.IsLower.scottHausdorff_le** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsLower
`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : TopologicalSpace α] [Topolo
gy.IsLower α],   Topology.scottHausdorff α Set.univ ≤ inst_1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsLower.topology_eq`：topology_eq : ‹_› = lower α
· 使用引理 `Topology.scottHausdorff_le_lower`：scottHausdorff_le_lower : scottHausdor
ff α univ <= lower α
-/
lemma IsLower.scottHausdorff_le [IsLower α] : scottHausdorff α univ ≤ ‹TopologicalSpace α› := by
  rw [IsLower.topology_eq α]
  exact scottHausdorff_le_lower

end Topology

