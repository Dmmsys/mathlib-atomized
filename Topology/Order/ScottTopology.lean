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
/--
Definition of `scottHausdorff` / `scottHausdorff` 的定义

English:
definition scottHausdorff
  signature: (α : Type*) (D : Set (Set α)) [Preorder α]
  body: forall ⦃d : Set α⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a : α⦄, IsLUB d a ->
    a in u -> exists b in d, Ici b inter d subseteq u
  isOpen_univ := fun d _ ⟨b, hb⟩ _ _ _ _ => ⟨b, hb, (Ici b inter d).subset_univ⟩
  isOpen_inter s t hs ht d hd₀ hd₁ hd₂ a hd₃ ha := by
    obtain ⟨b₁, hb₁d, hb₁ds⟩ := hs hd₀ hd₁ hd₂ hd₃ ha.1
    obtain ⟨b₂, hb₂d, hb₂dt⟩ := ht hd₀ hd₁ hd₂ hd₃ ha.2
    obtain ⟨c, hcd, hc⟩ := hd₂ b₁ hb₁d b₂ hb₂d
    exact ⟨c, hcd, fun e ⟨hce, hed⟩ => ⟨hb₁ds ⟨hc.1.trans hce, hed⟩, hb₂dt ⟨hc.2.trans hce, hed⟩⟩⟩
  isOpen_sUnion := fun s h d hd₀ hd₁ hd₂ a hd₃ ⟨s₀, hs₀s, has₀⟩ => by
    obtain ⟨b, hbd, hbds₀⟩ := h s₀ hs₀s hd₀ hd₁ hd₂ hd₃ has₀
    exact ⟨b, hbd, Set.subset_sUnion_of_subset s s₀ hbds₀ hs₀s⟩

中文:
定义 scottHausdorff
  签名: (α : 类型) (D : 集合 (集合 α)) [预序 α]
  定义体: forall ⦃d : Set α⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a : α⦄, IsLUB d a ->
    a in u -> exists b in d, Ici b inter d subseteq u
  isOpen_univ := fun d _ ⟨b, hb⟩ _ _ _ _ => ⟨b, hb, (Ici b inter d).subset_univ⟩
  isOpen_inter s t hs ht d hd₀ hd₁ hd₂ a hd₃ ha := by
    obtain ⟨b₁, hb₁d, hb₁ds⟩ := hs hd₀ hd₁ hd₂ hd₃ ha.1
    obtain ⟨b₂, hb₂d, hb₂dt⟩ := ht hd₀ hd₁ hd₂ hd₃ ha.2
    obtain ⟨c, hcd, hc⟩ := hd₂ b₁ hb₁d b₂ hb₂d
    exact ⟨c, hcd, fun e ⟨hce, hed⟩ => ⟨hb₁ds ⟨hc.1.trans hce, hed⟩, hb₂dt ⟨hc.2.trans hce, hed⟩⟩⟩
  isOpen_sUnion := fun s h d hd₀ hd₁ hd₂ a hd₃ ⟨s₀, hs₀s, has₀⟩ => by
    obtain ⟨b, hbd, hbds₀⟩ := h s₀ hs₀s hd₀ hd₁ hd₂ hd₃ has₀
    exact ⟨b, hbd, Set.subset_sUnion_of_subset s s₀ hbds₀ hs₀s⟩

Depends on / 依赖: DirectedOn, Nonempty, d.Nonempty
-/
def scottHausdorff (α : Type*) (D : Set (Set α)) [Preorder α] : TopologicalSpace α where
  IsOpen u := forall ⦃d : Set α⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a : α⦄, IsLUB d a ->
    a in u -> exists b in d, Ici b inter d subseteq u
  isOpen_univ := fun d _ ⟨b, hb⟩ _ _ _ _ => ⟨b, hb, (Ici b inter d).subset_univ⟩
  isOpen_inter s t hs ht d hd₀ hd₁ hd₂ a hd₃ ha := by
    obtain ⟨b₁, hb₁d, hb₁ds⟩ := hs hd₀ hd₁ hd₂ hd₃ ha.1
    obtain ⟨b₂, hb₂d, hb₂dt⟩ := ht hd₀ hd₁ hd₂ hd₃ ha.2
    obtain ⟨c, hcd, hc⟩ := hd₂ b₁ hb₁d b₂ hb₂d
    exact ⟨c, hcd, fun e ⟨hce, hed⟩ => ⟨hb₁ds ⟨hc.1.trans hce, hed⟩, hb₂dt ⟨hc.2.trans hce, hed⟩⟩⟩
  isOpen_sUnion := fun s h d hd₀ hd₁ hd₂ a hd₃ ⟨s₀, hs₀s, has₀⟩ => by
    obtain ⟨b, hbd, hbds₀⟩ := h s₀ hs₀s hd₀ hd₁ hd₂ hd₃ has₀
    exact ⟨b, hbd, Set.subset_sUnion_of_subset s s₀ hbds₀ hs₀s⟩

/--
Definition of `IsScottHausdorff` / `IsScottHausdorff` 的定义

English:
class IsScottHausdorff
  parameters: (α) (D : Set (Set α)) [Preorder α] [TopologicalSpace α]
  axioms and operations (1):
    - topology_eq_scottHausdorff : ‹TopologicalSpace α› = scottHausdorff α D

中文:
类 是ScottHausdorff
  参数: (α) (D : 集合 (集合 α)) [预序 α] [拓扑空间 α]
  公理与运算 (1 个):
    - topology_eq_scottHausdorff : ‹拓扑空间 α› = scottHausdorff α D
-/
class IsScottHausdorff (α) (D : Set (Set α)) [Preorder α] [TopologicalSpace α] : Prop where
  topology_eq_scottHausdorff : ‹TopologicalSpace α› = scottHausdorff α D

instance (α) (D : Set (Set α)) [Preorder α] : @IsScottHausdorff α D _ (scottHausdorff α D) :=
  @IsScottHausdorff.mk _ _ _ (scottHausdorff α D) rfl

namespace IsScottHausdorff

variable {s : Set α} {D : Set (Set α)} [Preorder α] [t : TopologicalSpace α]

section General

variable [IsScottHausdorff α D]

variable (α D) in
/--
lemma `topology_eq` / 引理 `topology_eq`

English:
lemma topology_eq
  statement: ‹_› = scottHausdorff α D
  proof: topology_eq_scottHausdorff

中文:
引理 topology_eq
  结论: ‹_› = scottHausdorff α D
  证明: topology_eq_scottHausdorff

Depends on / 依赖: topology_eq_scottHausdorff
-/
lemma topology_eq : ‹_› = scottHausdorff α D := topology_eq_scottHausdorff

/--
lemma `isOpen_iff` / 引理 `isOpen_iff`

English:
lemma isOpen_iff
  proof: by
  simp +instances [topology_eq_scottHausdorff (α := α) (D := D), IsOpen, scottHausdorff]

中文:
引理 isOpen_iff
  证明: by
  simp +instances [topology_eq_scottHausdorff (α := α) (D := D), IsOpen, scottHausdorff]

Depends on / 依赖: IsOpen, instances, scottHausdorff, topology_eq_scottHausdorff
-/
lemma isOpen_iff :
    IsOpen s ↔ forall ⦃d : Set α⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a : α⦄, IsLUB d a ->
      a in s -> exists b in d, Ici b inter d subseteq s := by
  simp +instances [topology_eq_scottHausdorff (α := α) (D := D), IsOpen, scottHausdorff]

/--
lemma `dirSupInaccOn_of_isOpen` / 引理 `dirSupInaccOn_of_isOpen`

English:
lemma dirSupInaccOn_of_isOpen
  given: (h : IsOpen s)
  statement: DirSupInaccOn D s
  proof: .of_inter_subset (isOpen_iff.1 h)

中文:
引理 dirSupInaccOn_of_isOpen
  条件: (h : 是开集 s)
  结论: DirSupInaccOn D s
  证明: .of_inter_subset (isOpen_iff.1 h)

Depends on / 依赖: isOpen_iff, of_inter_subset
-/
lemma dirSupInaccOn_of_isOpen (h : IsOpen s) : DirSupInaccOn D s :=
  .of_inter_subset (isOpen_iff.1 h)

/--
lemma `dirSupClosedOn_of_isClosed` / 引理 `dirSupClosedOn_of_isClosed`

English:
lemma dirSupClosedOn_of_isClosed
  given: (h : IsClosed s)
  statement: DirSupClosedOn D s
  proof: .of_compl (dirSupInaccOn_of_isOpen h.isOpen_compl)

中文:
引理 dirSupClosedOn_of_isClosed
  条件: (h : 是闭集 s)
  结论: DirSupClosedOn D s
  证明: .of_compl (dirSupInaccOn_of_isOpen h.isOpen_compl)

Depends on / 依赖: dirSupInaccOn_of_isOpen, h.isOpen_compl, isOpen_compl, of_compl
-/
lemma dirSupClosedOn_of_isClosed (h : IsClosed s) : DirSupClosedOn D s :=
  .of_compl (dirSupInaccOn_of_isOpen h.isOpen_compl)

/--
theorem `isOpen_iff_dirSupInaccOn` / 定理 `isOpen_iff_dirSupInaccOn`

English:
theorem isOpen_iff_dirSupInaccOn
  given: (hDL : IsLowerSet D)
  statement: IsOpen s ↔ DirSupInaccOn D s
  proof: by
  rw [isOpen_iff (D := D)]; rw [dirSupInaccOn_iff_inter_subset hDL]

中文:
定理 isOpen_iff_dirSupInaccOn
  条件: (hDL : 是下集 D)
  结论: 是开集 s ↔ DirSupInaccOn D s
  证明: by
  rw [isOpen_iff (D := D)]; rw [dirSupInaccOn_iff_inter_subset hDL]

Depends on / 依赖: dirSupInaccOn_iff_inter_subset, isOpen_iff
-/
theorem isOpen_iff_dirSupInaccOn (hDL : IsLowerSet D) : IsOpen s ↔ DirSupInaccOn D s := by
  rw [isOpen_iff (D := D)]; rw [dirSupInaccOn_iff_inter_subset hDL]

/--
theorem `isClosed_iff_dirSupClosedOn` / 定理 `isClosed_iff_dirSupClosedOn`

English:
theorem isClosed_iff_dirSupClosedOn
  given: (hDL : IsLowerSet D)
  statement: IsClosed s ↔ DirSupClosedOn D s
  proof: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_dirSupInaccOn hDL]; rw [dirSupInaccOn_compl]

中文:
定理 isClosed_iff_dirSupClosedOn
  条件: (hDL : 是下集 D)
  结论: 是闭集 s ↔ DirSupClosedOn D s
  证明: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_dirSupInaccOn hDL]; rw [dirSupInaccOn_compl]

Depends on / 依赖: dirSupInaccOn_compl, isOpen_compl_iff, isOpen_iff_dirSupInaccOn
-/
theorem isClosed_iff_dirSupClosedOn (hDL : IsLowerSet D) : IsClosed s ↔ DirSupClosedOn D s := by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_dirSupInaccOn hDL]; rw [dirSupInaccOn_compl]

/--
theorem `isOpen_of_isLowerSet` / 定理 `isOpen_of_isLowerSet`

English:
theorem isOpen_of_isLowerSet
  given: (hDL : IsLowerSet D) (h : IsLowerSet s)
  statement: IsOpen s
  proof: (isOpen_iff_dirSupInaccOn hDL).2 h.dirSupInaccOn

中文:
定理 isOpen_of_isLowerSet
  条件: (hDL : 是下集 D) (h : 是下集 s)
  结论: 是开集 s
  证明: (isOpen_iff_dirSupInaccOn hDL).2 h.dirSupInaccOn

Depends on / 依赖: dirSupInaccOn, h.dirSupInaccOn, isOpen_iff_dirSupInaccOn
-/
theorem isOpen_of_isLowerSet (hDL : IsLowerSet D) (h : IsLowerSet s) : IsOpen s :=
  (isOpen_iff_dirSupInaccOn hDL).2 h.dirSupInaccOn

/--
theorem `isClosed_of_isUpperSet` / 定理 `isClosed_of_isUpperSet`

English:
theorem isClosed_of_isUpperSet
  given: (hDL : IsLowerSet D) (h : IsUpperSet s)
  statement: IsClosed s
  proof: (isClosed_iff_dirSupClosedOn hDL).2 h.dirSupClosedOn

中文:
定理 isClosed_of_isUpperSet
  条件: (hDL : 是下集 D) (h : 是上集 s)
  结论: 是闭集 s
  证明: (isClosed_iff_dirSupClosedOn hDL).2 h.dirSupClosedOn

Depends on / 依赖: dirSupClosedOn, h.dirSupClosedOn, isClosed_iff_dirSupClosedOn
-/
theorem isClosed_of_isUpperSet (hDL : IsLowerSet D) (h : IsUpperSet s) : IsClosed s :=
  (isClosed_iff_dirSupClosedOn hDL).2 h.dirSupClosedOn

end General

section univ

variable [IsScottHausdorff α univ]

/--
theorem `isOpen_iff_dirSupInacc` / 定理 `isOpen_iff_dirSupInacc`

English:
theorem isOpen_iff_dirSupInacc
  statement: IsOpen s ↔ DirSupInacc s
  proof: by
  rw [isOpen_iff_dirSupInaccOn isLowerSet_univ]; rw [dirSupInaccOn_univ]

中文:
定理 isOpen_iff_dirSupInacc
  结论: 是开集 s ↔ DirSupInacc s
  证明: by
  rw [isOpen_iff_dirSupInaccOn isLowerSet_univ]; rw [dirSupInaccOn_univ]

Depends on / 依赖: dirSupInaccOn_univ, isLowerSet_univ, isOpen_iff_dirSupInaccOn
-/
theorem isOpen_iff_dirSupInacc : IsOpen s ↔ DirSupInacc s := by
  rw [isOpen_iff_dirSupInaccOn isLowerSet_univ]; rw [dirSupInaccOn_univ]

/--
theorem `isClosed_iff_dirSupClosed` / 定理 `isClosed_iff_dirSupClosed`

English:
theorem isClosed_iff_dirSupClosed
  statement: IsClosed s ↔ DirSupClosed s
  proof: by
  rw [isClosed_iff_dirSupClosedOn isLowerSet_univ]; rw [dirSupClosedOn_univ]

中文:
定理 isClosed_iff_dirSupClosed
  结论: 是闭集 s ↔ DirSupClosed s
  证明: by
  rw [isClosed_iff_dirSupClosedOn isLowerSet_univ]; rw [dirSupClosedOn_univ]

Depends on / 依赖: dirSupClosedOn_univ, isClosed_iff_dirSupClosedOn, isLowerSet_univ
-/
theorem isClosed_iff_dirSupClosed : IsClosed s ↔ DirSupClosed s := by
  rw [isClosed_iff_dirSupClosedOn isLowerSet_univ]; rw [dirSupClosedOn_univ]

end univ
end IsScottHausdorff

/-! ### Scott topology -/

section Scott
section Preorder

/-- The Scott topology.

It is defined as the join of the topology of upper sets and the Scott-Hausdorff topology. -/
@[instance_reducible]
/--
Definition of `scott` / `scott` 的定义

English:
definition scott
  signature: (α : Type*) (D : Set (Set α)) [Preorder α]
  body: upperSet α ⊔ scottHausdorff α D

中文:
定义 scott
  签名: (α : 类型) (D : 集合 (集合 α)) [预序 α]
  定义体: upperSet α ⊔ scottHausdorff α D

Depends on / 依赖: scottHausdorff, upperSet
-/
def scott (α : Type*) (D : Set (Set α)) [Preorder α] : TopologicalSpace α :=
  upperSet α ⊔ scottHausdorff α D

/--
lemma `upperSet_le_scott` / 引理 `upperSet_le_scott`

English:
lemma upperSet_le_scott
  given: [Preorder α]
  statement: upperSet α <= scott α univ
  proof: le_sup_left

中文:
引理 upperSet_le_scott
  条件: [预序 α]
  结论: upperSet α <= scott α univ
  证明: le_sup_left

Depends on / 依赖: le_sup_left
-/
lemma upperSet_le_scott [Preorder α] : upperSet α <= scott α univ := le_sup_left

/--
lemma `scottHausdorff_le_scott` / 引理 `scottHausdorff_le_scott`

English:
lemma scottHausdorff_le_scott
  given: [Preorder α]
  statement: scottHausdorff α univ <= scott α univ
  proof: le_sup_right

中文:
引理 scottHausdorff_le_scott
  条件: [预序 α]
  结论: scottHausdorff α univ <= scott α univ
  证明: le_sup_right

Depends on / 依赖: le_sup_right
-/
lemma scottHausdorff_le_scott [Preorder α] : scottHausdorff α univ <= scott α univ := le_sup_right

variable (α) (D) [Preorder α] [TopologicalSpace α]

/--
Definition of `IsScott` / `IsScott` 的定义

English:
class IsScott
  parameters: : Prop where
  axioms and operations (1):
    - topology_eq_scott : ‹TopologicalSpace α› = scott α D

中文:
类 是Scott
  参数: : 命题 where
  公理与运算 (1 个):
    - topology_eq_scott : ‹拓扑空间 α› = scott α D
-/
class IsScott : Prop where
  topology_eq_scott : ‹TopologicalSpace α› = scott α D

end Preorder

namespace IsScott
section Preorder
variable (α) (D) [Preorder α] [TopologicalSpace α]

/--
lemma `topology_eq` / 引理 `topology_eq`

English:
lemma topology_eq
  given: [IsScott α D]
  statement: ‹_› = scott α D
  proof: topology_eq_scott

中文:
引理 topology_eq
  条件: [是Scott α D]
  结论: ‹_› = scott α D
  证明: topology_eq_scott

Depends on / 依赖: topology_eq_scott
-/
lemma topology_eq [IsScott α D] : ‹_› = scott α D := topology_eq_scott

variable {α} {D} {s : Set α} {a : α}

/--
lemma `isOpen_iff_isUpperSet_and_scottHausdorff_open` / 引理 `isOpen_iff_isUpperSet_and_scottHausdorff_open`

English:
lemma isOpen_iff_isUpperSet_and_scottHausdorff_open
  given: [IsScott α D]
  proof: by rw [topology_eq α D]; rfl

中文:
引理 isOpen_iff_isUpperSet_and_scottHausdorff_open
  条件: [是Scott α D]
  证明: by rw [topology_eq α D]; rfl

Depends on / 依赖: topology_eq
-/
lemma isOpen_iff_isUpperSet_and_scottHausdorff_open [IsScott α D] :
    IsOpen s ↔ IsUpperSet s ∧ IsOpen[scottHausdorff α D] s := by rw [topology_eq α D]; rfl

/--
lemma `isOpen_iff_isUpperSet_and_dirSupInaccOn` / 引理 `isOpen_iff_isUpperSet_and_dirSupInaccOn`

English:
lemma isOpen_iff_isUpperSet_and_dirSupInaccOn
  given: [IsScott α D]
  proof: by
  rw [isOpen_iff_isUpperSet_and_scottHausdorff_open (D := D)]
  refine and_congr_right fun h =>
    ⟨IsScottHausdorff.dirSupInaccOn_of_isOpen (t := scottHausdorff α D),
      fun h' d d₀ d₁ d₂ _ d₃ ha => ?_⟩
  obtain ⟨b, hbd, hbu⟩ := h' d₀ d₁ d₂ d₃ ha
  exact ⟨b, hbd, Subset.trans inter_subset_left (h.Ici_subset hbu)⟩

中文:
引理 isOpen_iff_isUpperSet_and_dirSupInaccOn
  条件: [是Scott α D]
  证明: by
  rw [isOpen_iff_isUpperSet_and_scottHausdorff_open (D := D)]
  refine and_congr_right fun h =>
    ⟨IsScottHausdorff.dirSupInaccOn_of_isOpen (t := scottHausdorff α D),
      fun h' d d₀ d₁ d₂ _ d₃ ha => ?_⟩
  obtain ⟨b, hbd, hbu⟩ := h' d₀ d₁ d₂ d₃ ha
  exact ⟨b, hbd, Subset.trans inter_subset_left (h.Ici_subset hbu)⟩

Depends on / 依赖: Ici_subset, IsScottHausdorff, IsScottHausdorff.dirSupInaccOn_of_isOpen, Subset, Subset.trans, and_congr_right, dirSupInaccOn_of_isOpen, h.Ici_subset, inter_subset_left, isOpen_iff_isUpperSet_and_scottHausdorff_open, scottHausdorff
-/
lemma isOpen_iff_isUpperSet_and_dirSupInaccOn [IsScott α D] :
    IsOpen s ↔ IsUpperSet s ∧ DirSupInaccOn D s := by
  rw [isOpen_iff_isUpperSet_and_scottHausdorff_open (D := D)]
  refine and_congr_right fun h =>
    ⟨IsScottHausdorff.dirSupInaccOn_of_isOpen (t := scottHausdorff α D),
      fun h' d d₀ d₁ d₂ _ d₃ ha => ?_⟩
  obtain ⟨b, hbd, hbu⟩ := h' d₀ d₁ d₂ d₃ ha
  exact ⟨b, hbd, Subset.trans inter_subset_left (h.Ici_subset hbu)⟩

/--
lemma `isClosed_iff_isLowerSet_and_dirSupClosed` / 引理 `isClosed_iff_isLowerSet_and_dirSupClosed`

English:
lemma isClosed_iff_isLowerSet_and_dirSupClosed
  given: [IsScott α univ]
  proof: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ)]; rw [isUpperSet_compl]; rw [dirSupInaccOn_univ]; rw [dirSupInacc_compl]

中文:
引理 isClosed_iff_isLowerSet_and_dirSupClosed
  条件: [是Scott α univ]
  证明: by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ)]; rw [isUpperSet_compl]; rw [dirSupInaccOn_univ]; rw [dirSupInacc_compl]

Depends on / 依赖: dirSupInaccOn_univ, dirSupInacc_compl, isOpen_compl_iff, isOpen_iff_isUpperSet_and_dirSupInaccOn, isUpperSet_compl
-/
lemma isClosed_iff_isLowerSet_and_dirSupClosed [IsScott α univ] :
    IsClosed s ↔ IsLowerSet s ∧ DirSupClosed s := by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ)]; rw [isUpperSet_compl]; rw [dirSupInaccOn_univ]; rw [dirSupInacc_compl]

/--
lemma `isUpperSet_of_isOpen` / 引理 `isUpperSet_of_isOpen`

English:
lemma isUpperSet_of_isOpen
  given: [IsScott α D]
  statement: IsOpen s -> IsUpperSet s
  proof: fun h =>
  (isOpen_iff_isUpperSet_and_scottHausdorff_open (D := D).mp h).left

中文:
引理 isUpperSet_of_isOpen
  条件: [是Scott α D]
  结论: 是开集 s -> 是上集 s
  证明: fun h =>
  (isOpen_iff_isUpperSet_and_scottHausdorff_open (D := D).mp h).left
-/
lemma isUpperSet_of_isOpen [IsScott α D] : IsOpen s -> IsUpperSet s := fun h =>
  (isOpen_iff_isUpperSet_and_scottHausdorff_open (D := D).mp h).left

/--
lemma `isLowerSet_of_isClosed` / 引理 `isLowerSet_of_isClosed`

English:
lemma isLowerSet_of_isClosed
  given: [IsScott α univ]
  statement: IsClosed s -> IsLowerSet s
  proof: fun h =>
  (isClosed_iff_isLowerSet_and_dirSupClosed.mp h).left

中文:
引理 isLowerSet_of_isClosed
  条件: [是Scott α univ]
  结论: 是闭集 s -> 是下集 s
  证明: fun h =>
  (isClosed_iff_isLowerSet_and_dirSupClosed.mp h).left
-/
lemma isLowerSet_of_isClosed [IsScott α univ] : IsClosed s -> IsLowerSet s := fun h =>
  (isClosed_iff_isLowerSet_and_dirSupClosed.mp h).left

/--
lemma `dirSupClosed_of_isClosed` / 引理 `dirSupClosed_of_isClosed`

English:
lemma dirSupClosed_of_isClosed
  given: [IsScott α univ]
  statement: IsClosed s -> DirSupClosed s
  proof: fun h =>
  (isClosed_iff_isLowerSet_and_dirSupClosed.mp h).right

中文:
引理 dirSupClosed_of_isClosed
  条件: [是Scott α univ]
  结论: 是闭集 s -> DirSupClosed s
  证明: fun h =>
  (isClosed_iff_isLowerSet_and_dirSupClosed.mp h).right
-/
lemma dirSupClosed_of_isClosed [IsScott α univ] : IsClosed s -> DirSupClosed s := fun h =>
  (isClosed_iff_isLowerSet_and_dirSupClosed.mp h).right

/--
lemma `lowerClosure_subset_closure` / 引理 `lowerClosure_subset_closure`

English:
lemma lowerClosure_subset_closure
  given: [IsScott α univ]
  statement: ↑(lowerClosure s) subseteq closure s
  proof: by
  convert! closure.mono (@upperSet_le_scott α _)
  · rw [@IsUpperSet.closure_eq_lowerClosure α _ (upperSet α) ?_ s]
    infer_instance
  · exact topology_eq α univ

中文:
引理 lowerClosure_subset_closure
  条件: [是Scott α univ]
  结论: ↑(lowerClosure s) subseteq closure s
  证明: by
  convert! closure.mono (@upperSet_le_scott α _)
  · rw [@IsUpperSet.closure_eq_lowerClosure α _ (upperSet α) ?_ s]
    infer_instance
  · exact topology_eq α univ

Depends on / 依赖: IsUpperSet, IsUpperSet.closure_eq_lowerClosure, closure, closure.mono, closure_eq_lowerClosure, convert, infer_instance, topology_eq, upperSet, upperSet_le_scott
-/
lemma lowerClosure_subset_closure [IsScott α univ] : ↑(lowerClosure s) subseteq closure s := by
  convert! closure.mono (@upperSet_le_scott α _)
  · rw [@IsUpperSet.closure_eq_lowerClosure α _ (upperSet α) ?_ s]
    infer_instance
  · exact topology_eq α univ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsScott
  signature: α univ] : ClosedIicTopology α where
  body: isClosed_iff_isLowerSet_and_dirSupClosed.2 ⟨isLowerSet_Iic _, dirSupClosed_Iic _⟩

中文:
实例 [是Scott
  签名: α univ] : ClosedIic拓扑 α where
  定义体: isClosed_iff_isLowerSet_and_dirSupClosed.2 ⟨isLowerSet_Iic _, dirSupClosed_Iic _⟩

Depends on / 依赖: dirSupClosed_Iic, isClosed_iff_isLowerSet_and_dirSupClosed, isLowerSet_Iic
-/
instance [IsScott α univ] : ClosedIicTopology α where
  isClosed_Iic _ :=
    isClosed_iff_isLowerSet_and_dirSupClosed.2 ⟨isLowerSet_Iic _, dirSupClosed_Iic _⟩

/--
lemma `closure_singleton` / 引理 `closure_singleton`

English:
lemma closure_singleton
  given: [IsScott α univ]
  statement: closure {a} = Iic a
  proof: le_antisymm
(closure_minimal (by rw [singleton_subset_iff, mem_Iic]) isClosed_Iic) by
    rw [← LowerSet.coe_Iic]; rw [← lowerClosure_singleton]
    apply lowerClosure_subset_closure

中文:
引理 closure_singleton
  条件: [是Scott α univ]
  结论: closure {a} = 左无界右闭区间 a
  证明: le_antisymm
(closure_minimal (by rw [singleton_subset_iff, mem_Iic]) isClosed_Iic) by
    rw [← LowerSet.coe_Iic]; rw [← lowerClosure_singleton]
    apply lowerClosure_subset_closure
-/
@[simp] lemma closure_singleton [IsScott α univ] : closure {a} = Iic a := le_antisymm
(closure_minimal (by rw [singleton_subset_iff, mem_Iic]) isClosed_Iic) by
    rw [← LowerSet.coe_Iic]; rw [← lowerClosure_singleton]
    apply lowerClosure_subset_closure

variable [Preorder β] [TopologicalSpace β] [IsScott β univ] {f : α -> β}

/--
lemma `monotone_of_continuous` / 引理 `monotone_of_continuous`

English:
lemma monotone_of_continuous
  given: [IsScott α D] (hf : Continuous f)
  statement: Monotone f
  proof: fun _ b hab => by
  by_contra h
  simpa only [mem_compl_iff, mem_preimage, mem_Iic, le_refl, not_true]
    using isUpperSet_of_isOpen (D := D) ((isOpen_compl_iff.2 isClosed_Iic).preimage hf) hab h

中文:
引理 monotone_of_continuous
  条件: [是Scott α D] (hf : 连续 f)
  结论: 递增 f
  证明: fun _ b hab => by
  by_contra h
  simpa only [mem_compl_iff, mem_preimage, mem_Iic, le_refl, not_true]
    using isUpperSet_of_isOpen (D := D) ((isOpen_compl_iff.2 isClosed_Iic).preimage hf) hab h

Depends on / 依赖: isClosed_Iic, isOpen_compl_iff, isUpperSet_of_isOpen, le_refl, mem_Iic, mem_compl_iff, mem_preimage, not_true, preimage
-/
lemma monotone_of_continuous [IsScott α D] (hf : Continuous f) : Monotone f := fun _ b hab => by
  by_contra h
  simpa only [mem_compl_iff, mem_preimage, mem_Iic, le_refl, not_true]
    using isUpperSet_of_isOpen (D := D) ((isOpen_compl_iff.2 isClosed_Iic).preimage hf) hab h

/--
lemma `scottContinuousOn_iff_continuous` / 引理 `scottContinuousOn_iff_continuous`

English:
lemma scottContinuousOn_iff_continuous
  statement: {D : Set (Set α)} [Topology.IsScott α D]
  proof: by
  refine ⟨fun h => continuous_def.2 fun u hu => ?_, ?_⟩
  · rw [isOpen_iff_isUpperSet_and_dirSupInaccOn (D := D)]
    exact ⟨(isUpperSet_of_isOpen (D := univ) hu).preimage (h.monotone D hD),
fun t h₀ hd₁ hd₂ a hd₃ ha => image_inter_nonempty_iff.mp
        (isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ).mp hu).2 trivial (Nonempty.image f hd₁)
        (directedOn_image.mpr (hd₂.mono @(h.monotone D hD))) (h h₀ hd₁ hd₂ hd₃) ha⟩
  · refine fun hf t h₀ d₁ d₂ a d₃ =>
      ⟨(monotone_of_continuous (D := D) hf).mem_upperBounds_image d₃.1,
      fun b hb => ?_⟩
    by_contra h
    let u := (Iic b)ᶜ
    have hu : IsOpen (f ⁻¹' u) := isClosed_Iic.isOpen_compl.preimage hf
    rw [isOpen_iff_isUpperSet_and_dirSupInaccOn (D := D)] at hu
    obtain ⟨c, hcd, hfcb⟩ := hu.2 h₀ d₁ d₂ d₃ h
    simp only [upperBounds, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      mem_ofPred] at hb
exact hfcb hb _ hcd

中文:
引理 scottContinuousOn_iff_continuous
  结论: {D : 集合 (集合 α)} [拓扑.是Scott α D]
  证明: by
  refine ⟨fun h => continuous_def.2 fun u hu => ?_, ?_⟩
  · rw [isOpen_iff_isUpperSet_and_dirSupInaccOn (D := D)]
    exact ⟨(isUpperSet_of_isOpen (D := univ) hu).preimage (h.monotone D hD),
fun t h₀ hd₁ hd₂ a hd₃ ha => image_inter_nonempty_iff.mp
        (isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ).mp hu).2 trivial (Nonempty.image f hd₁)
        (directedOn_image.mpr (hd₂.mono @(h.monotone D hD))) (h h₀ hd₁ hd₂ hd₃) ha⟩
  · refine fun hf t h₀ d₁ d₂ a d₃ =>
      ⟨(monotone_of_continuous (D := D) hf).mem_upperBounds_image d₃.1,
      fun b hb => ?_⟩
    by_contra h
    let u := (Iic b)ᶜ
    have hu : IsOpen (f ⁻¹' u) := isClosed_Iic.isOpen_compl.preimage hf
    rw [isOpen_iff_isUpperSet_and_dirSupInaccOn (D := D)] at hu
    obtain ⟨c, hcd, hfcb⟩ := hu.2 h₀ d₁ d₂ d₃ h
    simp only [upperBounds, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      mem_ofPred] at hb
exact hfcb hb _ hcd
-/
@[simp] lemma scottContinuousOn_iff_continuous {D : Set (Set α)} [Topology.IsScott α D]
    (hD : forall a b : α, a <= b -> {a, b} in D) : ScottContinuousOn D f ↔ Continuous f := by
  refine ⟨fun h => continuous_def.2 fun u hu => ?_, ?_⟩
  · rw [isOpen_iff_isUpperSet_and_dirSupInaccOn (D := D)]
    exact ⟨(isUpperSet_of_isOpen (D := univ) hu).preimage (h.monotone D hD),
fun t h₀ hd₁ hd₂ a hd₃ ha => image_inter_nonempty_iff.mp
        (isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ).mp hu).2 trivial (Nonempty.image f hd₁)
        (directedOn_image.mpr (hd₂.mono @(h.monotone D hD))) (h h₀ hd₁ hd₂ hd₃) ha⟩
  · refine fun hf t h₀ d₁ d₂ a d₃ =>
      ⟨(monotone_of_continuous (D := D) hf).mem_upperBounds_image d₃.1,
      fun b hb => ?_⟩
    by_contra h
    let u := (Iic b)ᶜ
    have hu : IsOpen (f ⁻¹' u) := isClosed_Iic.isOpen_compl.preimage hf
    rw [isOpen_iff_isUpperSet_and_dirSupInaccOn (D := D)] at hu
    obtain ⟨c, hcd, hfcb⟩ := hu.2 h₀ d₁ d₂ d₃ h
    simp only [upperBounds, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      mem_ofPred] at hb
exact hfcb hb _ hcd

end Preorder

section PartialOrder
variable [PartialOrder α] [TopologicalSpace α] [IsScott α univ]

/--
The Scott topology on a partial order is T₀.
-/
-- see Note [lower instance priority]
instance (priority := 90) : T0Space α :=
(t0Space_iff_inseparable α).2 fun x y h => Iic_injective by
    simpa only [inseparable_iff_closure_eq, IsScott.closure_singleton] using h

end PartialOrder

section CompleteLinearOrder

variable [CompleteLinearOrder α]

/--
lemma `isOpen_iff_Iic_compl_or_univ` / 引理 `isOpen_iff_Iic_compl_or_univ`

English:
lemma isOpen_iff_Iic_compl_or_univ
  given: [TopologicalSpace α] [Topology.IsScott α univ] (U : Set α)
  proof: by
  constructor
  · intro hU
    rcases eq_empty_or_nonempty Uᶜ with eUc | neUc
    · exact Or.inl (compl_empty_iff.mp eUc)
    · apply Or.inr
      use sSup Uᶜ
      rw [compl_eq_comm]; rw [le_antisymm_iff]
      refine ⟨fun _ ha => le_sSup ha, (isLowerSet_of_isClosed hU.isClosed_compl).Iic_subset ?_⟩
      exact dirSupClosed_iff_forall_sSup.mp (dirSupClosed_of_isClosed hU.isClosed_compl) le_rfl neUc
        (isChain_of_trichotomous Uᶜ).directedOn
  · rintro (rfl | ⟨a, rfl⟩)
    · exact isOpen_univ
    · exact isClosed_Iic.isOpen_compl

中文:
引理 isOpen_iff_Iic_compl_or_univ
  条件: [拓扑空间 α] [拓扑.是Scott α univ] (U : 集合 α)
  证明: by
  constructor
  · intro hU
    rcases eq_empty_or_nonempty Uᶜ with eUc | neUc
    · exact Or.inl (compl_empty_iff.mp eUc)
    · apply Or.inr
      use sSup Uᶜ
      rw [compl_eq_comm]; rw [le_antisymm_iff]
      refine ⟨fun _ ha => le_sSup ha, (isLowerSet_of_isClosed hU.isClosed_compl).Iic_subset ?_⟩
      exact dirSupClosed_iff_forall_sSup.mp (dirSupClosed_of_isClosed hU.isClosed_compl) le_rfl neUc
        (isChain_of_trichotomous Uᶜ).directedOn
  · rintro (rfl | ⟨a, rfl⟩)
    · exact isOpen_univ
    · exact isClosed_Iic.isOpen_compl

Depends on / 依赖: Iic_subset, Or.inl, Or.inr, compl_empty_iff, compl_empty_iff.mp, compl_eq_comm, dirSupClosed_iff_forall_sSup, dirSupClosed_iff_forall_sSup.mp, dirSupClosed_of_isClosed, directedOn, eq_empty_or_nonempty, hU.isClosed_compl, isChain_of_trichotomous, isClosed_Iic, isClosed_Iic.isOpen_compl, isClosed_compl, isLowerSet_of_isClosed, isOpen_compl, isOpen_univ, le_antisymm_iff
-/
lemma isOpen_iff_Iic_compl_or_univ [TopologicalSpace α] [Topology.IsScott α univ] (U : Set α) :
    IsOpen U ↔ U = univ ∨ exists a, (Iic a)ᶜ = U := by
  constructor
  · intro hU
    rcases eq_empty_or_nonempty Uᶜ with eUc | neUc
    · exact Or.inl (compl_empty_iff.mp eUc)
    · apply Or.inr
      use sSup Uᶜ
      rw [compl_eq_comm]; rw [le_antisymm_iff]
      refine ⟨fun _ ha => le_sSup ha, (isLowerSet_of_isClosed hU.isClosed_compl).Iic_subset ?_⟩
      exact dirSupClosed_iff_forall_sSup.mp (dirSupClosed_of_isClosed hU.isClosed_compl) le_rfl neUc
        (isChain_of_trichotomous Uᶜ).directedOn
  · rintro (rfl | ⟨a, rfl⟩)
    · exact isOpen_univ
    · exact isClosed_Iic.isOpen_compl

-- N.B. A number of conditions equivalent to `scott α = upper α` are given in Gierz _et al_,
-- Chapter III, Exercise 3.23.
/--
lemma `scott_eq_upper_of_completeLinearOrder` / 引理 `scott_eq_upper_of_completeLinearOrder`

English:
lemma scott_eq_upper_of_completeLinearOrder
  statement: scott α univ = upper α
  proof: by
  let := upper α
  ext U
  rw [@Topology.IsUpper.isTopologicalSpace_basis _ _ (upper α)
    ({ topology_eq_upperTopology := rfl }) U]
  let := scott α univ
  rw [@isOpen_iff_Iic_compl_or_univ _ _ (scott α univ) ({ topology_eq_scott := rfl }) U]

中文:
引理 scott_eq_upper_of_completeLinearOrder
  结论: scott α univ = upper α
  证明: by
  let := upper α
  ext U
  rw [@Topology.IsUpper.isTopologicalSpace_basis _ _ (upper α)
    ({ topology_eq_upperTopology := rfl }) U]
  let := scott α univ
  rw [@isOpen_iff_Iic_compl_or_univ _ _ (scott α univ) ({ topology_eq_scott := rfl }) U]

Depends on / 依赖: IsUpper, Topology, Topology.IsUpper.isTopologicalSpace_basis, isOpen_iff_Iic_compl_or_univ, isTopologicalSpace_basis, topology_eq_scott, topology_eq_upperTopology
-/
lemma scott_eq_upper_of_completeLinearOrder : scott α univ = upper α := by
  let := upper α
  ext U
  rw [@Topology.IsUpper.isTopologicalSpace_basis _ _ (upper α)
    ({ topology_eq_upperTopology := rfl }) U]
  let := scott α univ
  rw [@isOpen_iff_Iic_compl_or_univ _ _ (scott α univ) ({ topology_eq_scott := rfl }) U]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [IsUpper α] : IsScott α univ where
  body: by
    rw [scott_eq_upper_of_completeLinearOrder]
    exact IsUpper.topology_eq α

中文:
实例 [拓扑空间
  签名: α] [是Upper α] : 是Scott α univ where
  定义体: by
    rw [scott_eq_upper_of_completeLinearOrder]
    exact IsUpper.topology_eq α

Depends on / 依赖: IsUpper, IsUpper.topology_eq, scott_eq_upper_of_completeLinearOrder, topology_eq
-/
instance [TopologicalSpace α] [IsUpper α] : IsScott α univ where
  topology_eq_scott := by
    rw [scott_eq_upper_of_completeLinearOrder]
    exact IsUpper.topology_eq α

end CompleteLinearOrder

/--
lemma `isOpen_iff_scottContinuous_mem` / 引理 `isOpen_iff_scottContinuous_mem`

English:
lemma isOpen_iff_scottContinuous_mem
  statement: [Preorder α] {s : Set α} [TopologicalSpace α]
  proof: by
  rw [← scottContinuousOn_univ]; rw [scottContinuousOn_iff_continuous (fun _ _ _ => by trivial)]
  exact isOpen_iff_continuous_mem

中文:
引理 isOpen_iff_scottContinuous_mem
  结论: [预序 α] {s : 集合 α} [拓扑空间 α]
  证明: by
  rw [← scottContinuousOn_univ]; rw [scottContinuousOn_iff_continuous (fun _ _ _ => by trivial)]
  exact isOpen_iff_continuous_mem

Depends on / 依赖: isOpen_iff_continuous_mem, scottContinuousOn_iff_continuous, scottContinuousOn_univ
-/
lemma isOpen_iff_scottContinuous_mem [Preorder α] {s : Set α} [TopologicalSpace α]
    [IsScott α univ] : IsOpen s ↔ ScottContinuous fun x => x in s := by
  rw [← scottContinuousOn_univ]; rw [scottContinuousOn_iff_continuous (fun _ _ _ => by trivial)]
  exact isOpen_iff_continuous_mem

end IsScott

/--
Definition of `WithScott` / `WithScott` 的定义

English:
definition WithScott
  signature: (α : Type*)
  body: α

中文:
定义 WithScott
  签名: (α : 类型)
  定义体: α
-/
def WithScott (α : Type*) := α

namespace WithScott

/--
Definition of `toScott` / `toScott` 的定义

English:
definition toScott
  signature: : α ≃ WithScott α
  body: Equiv.refl _

中文:
定义 toScott
  签名: : α ≃ WithScott α
  定义体: Equiv.refl _
-/
@[match_pattern] def toScott : α ≃ WithScott α := Equiv.refl _

/--
Definition of `ofScott` / `ofScott` 的定义

English:
definition ofScott
  signature: : WithScott α ≃ α
  body: Equiv.refl _

中文:
定义 ofScott
  签名: : WithScott α ≃ α
  定义体: Equiv.refl _
-/
@[match_pattern] def ofScott : WithScott α ≃ α := Equiv.refl _

/--
lemma `toScott_symm_eq` / 引理 `toScott_symm_eq`

English:
lemma toScott_symm_eq
  statement: (@toScott α).symm = ofScott
  proof: rfl

中文:
引理 toScott_symm_eq
  结论: (@toScott α).symm = ofScott
  证明: rfl
-/
@[simp] lemma toScott_symm_eq : (@toScott α).symm = ofScott := rfl
/--
lemma `ofScott_symm_eq` / 引理 `ofScott_symm_eq`

English:
lemma ofScott_symm_eq
  statement: (@ofScott α).symm = toScott
  proof: rfl

中文:
引理 ofScott_symm_eq
  结论: (@ofScott α).symm = toScott
  证明: rfl
-/
@[simp] lemma ofScott_symm_eq : (@ofScott α).symm = toScott := rfl
/--
lemma `toScott_ofScott` / 引理 `toScott_ofScott`

English:
lemma toScott_ofScott
  given: (a : WithScott α)
  statement: toScott (ofScott a) = a
  proof: rfl

中文:
引理 toScott_ofScott
  条件: (a : WithScott α)
  结论: toScott (ofScott a) = a
  证明: rfl
-/
@[simp] lemma toScott_ofScott (a : WithScott α) : toScott (ofScott a) = a := rfl
/--
lemma `ofScott_toScott` / 引理 `ofScott_toScott`

English:
lemma ofScott_toScott
  given: (a : α)
  statement: ofScott (toScott a) = a
  proof: rfl

中文:
引理 ofScott_toScott
  条件: (a : α)
  结论: ofScott (toScott a) = a
  证明: rfl
-/
@[simp] lemma ofScott_toScott (a : α) : ofScott (toScott a) = a := rfl

/--
lemma `toScott_inj` / 引理 `toScott_inj`

English:
lemma toScott_inj
  given: {a b : α}
  statement: toScott a = toScott b ↔ a = b
  proof: Iff.rfl

中文:
引理 toScott_inj
  条件: {a b : α}
  结论: toScott a = toScott b ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma toScott_inj {a b : α} : toScott a = toScott b ↔ a = b := Iff.rfl

/--
lemma `ofScott_inj` / 引理 `ofScott_inj`

English:
lemma ofScott_inj
  given: {a b : WithScott α}
  statement: ofScott a = ofScott b ↔ a = b
  proof: Iff.rfl

中文:
引理 ofScott_inj
  条件: {a b : WithScott α}
  结论: ofScott a = ofScott b ↔ a = b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma ofScott_inj {a b : WithScott α} : ofScott a = ofScott b ↔ a = b := Iff.rfl
/-- A recursor for `WithScott`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: {β : WithScott α -> Sort _}
  body: fun a => h (ofScott a)

中文:
定义 rec
  签名: {β : WithScott α -> 类型层 _}
  定义体: fun a => h (ofScott a)
-/
protected def rec {β : WithScott α -> Sort _}
    (h : forall a, β (toScott a)) : forall a, β a := fun a => h (ofScott a)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nonempty (WithScott α)
  body: ‹Nonempty α›

中文:
实例 [非空
  签名: α] : 非空 (WithScott α)
  定义体: ‹Nonempty α›

Depends on / 依赖: Nonempty
-/
instance [Nonempty α] : Nonempty (WithScott α) := ‹Nonempty α›
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (WithScott α)
  body: ‹Inhabited α›

中文:
实例 [可居
  签名: α] : 可居 (WithScott α)
  定义体: ‹Inhabited α›

Depends on / 依赖: Inhabited
-/
instance [Inhabited α] : Inhabited (WithScott α) := ‹Inhabited α›

variable [Preorder α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder (WithScott α)
  body: ‹Preorder α›

中文:
实例 :
  签名: 预序 (WithScott α)
  定义体: ‹Preorder α›

Depends on / 依赖: Preorder
-/
instance : Preorder (WithScott α) := ‹Preorder α›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (WithScott α)
  body: -- fast_instance% scott α univ fails
  letI : TopologicalSpace α := scott α univ
inferInstanceAs TopologicalSpace α

中文:
实例 :
  签名: 拓扑空间 (WithScott α)
  定义体: -- fast_instance% scott α univ fails
  letI : TopologicalSpace α := scott α univ
inferInstanceAs TopologicalSpace α
-/
instance : TopologicalSpace (WithScott α) :=
  -- fast_instance% scott α univ fails
  letI : TopologicalSpace α := scott α univ
inferInstanceAs TopologicalSpace α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScott (WithScott α) univ
  body: ⟨rfl⟩

中文:
实例 :
  签名: 是Scott (WithScott α) univ
  定义体: ⟨rfl⟩
-/
instance : IsScott (WithScott α) univ := ⟨rfl⟩

/--
lemma `isOpen_iff_isUpperSet_and_scottHausdorff_open'` / 引理 `isOpen_iff_isUpperSet_and_scottHausdorff_open'`

English:
lemma isOpen_iff_isUpperSet_and_scottHausdorff_open'
  given: {u : Set α}
  proof: Iff.rfl

中文:
引理 isOpen_iff_isUpperSet_and_scottHausdorff_open'
  条件: {u : 集合 α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isOpen_iff_isUpperSet_and_scottHausdorff_open' {u : Set α} :
    IsOpen (WithScott.ofScott ⁻¹' u) ↔ IsUpperSet u ∧ (scottHausdorff α univ).IsOpen u := Iff.rfl

end WithScott
end Scott

variable [Preorder α]

/--
lemma `scottHausdorff_le_lower` / 引理 `scottHausdorff_le_lower`

English:
lemma scottHausdorff_le_lower
  statement: scottHausdorff α univ <= lower α
  proof: let : TopologicalSpace α := scottHausdorff α univ
fun s h => IsScottHausdorff.isOpen_of_isLowerSet isLowerSet_univ
    @IsLower.isLowerSet_of_isOpen (Topology.WithLower α) _ _ _ s h

中文:
引理 scottHausdorff_le_lower
  结论: scottHausdorff α univ <= lower α
  证明: let : TopologicalSpace α := scottHausdorff α univ
fun s h => IsScottHausdorff.isOpen_of_isLowerSet isLowerSet_univ
    @IsLower.isLowerSet_of_isOpen (Topology.WithLower α) _ _ _ s h

Depends on / 依赖: IsLower, IsLower.isLowerSet_of_isOpen, IsScottHausdorff, IsScottHausdorff.isOpen_of_isLowerSet, TopologicalSpace, Topology, Topology.WithLower, WithLower, isLowerSet_of_isOpen, isLowerSet_univ, isOpen_of_isLowerSet, scottHausdorff
-/
lemma scottHausdorff_le_lower : scottHausdorff α univ <= lower α :=
  let : TopologicalSpace α := scottHausdorff α univ
fun s h => IsScottHausdorff.isOpen_of_isLowerSet isLowerSet_univ
    @IsLower.isLowerSet_of_isOpen (Topology.WithLower α) _ _ _ s h

variable [TopologicalSpace α]

/--
Definition of `IsScott.withScottHomeomorph` / `IsScott.withScottHomeomorph` 的定义

English:
definition IsScott.withScottHomeomorph
  signature: [IsScott α univ]
  body: WithScott.ofScott.toHomeomorphOfIsInducing ⟨IsScott.topology_eq α univ ▸ induced_id.symm⟩

中文:
定义 是Scott.withScottHomeomorph
  签名: [是Scott α univ]
  定义体: WithScott.ofScott.toHomeomorphOfIsInducing ⟨IsScott.topology_eq α univ ▸ induced_id.symm⟩

Depends on / 依赖: IsScott, IsScott.topology_eq, WithScott, WithScott.ofScott.toHomeomorphOfIsInducing, induced_id, induced_id.symm, ofScott, toHomeomorphOfIsInducing, topology_eq
-/
def IsScott.withScottHomeomorph [IsScott α univ] : WithScott α ≃ₜ α :=
  WithScott.ofScott.toHomeomorphOfIsInducing ⟨IsScott.topology_eq α univ ▸ induced_id.symm⟩

/--
lemma `IsScott.scottHausdorff_le` / 引理 `IsScott.scottHausdorff_le`

English:
lemma IsScott.scottHausdorff_le
  given: [IsScott α univ]
  proof: by
  rw [IsScott.topology_eq α univ]; rw [scott]; exact le_sup_right

中文:
引理 是Scott.scottHausdorff_le
  条件: [是Scott α univ]
  证明: by
  rw [IsScott.topology_eq α univ]; rw [scott]; exact le_sup_right

Depends on / 依赖: IsScott, IsScott.topology_eq, le_sup_right, topology_eq
-/
lemma IsScott.scottHausdorff_le [IsScott α univ] :
    scottHausdorff α univ <= ‹TopologicalSpace α› := by
  rw [IsScott.topology_eq α univ]; rw [scott]; exact le_sup_right

/--
lemma `IsLower.scottHausdorff_le` / 引理 `IsLower.scottHausdorff_le`

English:
lemma IsLower.scottHausdorff_le
  given: [IsLower α]
  statement: scottHausdorff α univ <= ‹TopologicalSpace α›
  proof: by
  rw [IsLower.topology_eq α]
  exact scottHausdorff_le_lower

中文:
引理 是Lower.scottHausdorff_le
  条件: [是Lower α]
  结论: scottHausdorff α univ <= ‹拓扑空间 α›
  证明: by
  rw [IsLower.topology_eq α]
  exact scottHausdorff_le_lower

Depends on / 依赖: IsLower, IsLower.topology_eq, scottHausdorff_le_lower, topology_eq
-/
lemma IsLower.scottHausdorff_le [IsLower α] : scottHausdorff α univ <= ‹TopologicalSpace α› := by
  rw [IsLower.topology_eq α]
  exact scottHausdorff_le_lower

end Topology
