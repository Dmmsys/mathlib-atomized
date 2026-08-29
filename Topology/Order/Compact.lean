/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.Order.LocalExtr

/-!
# Compactness of a closed interval

In this file we prove that a closed interval in a conditionally complete linear ordered type with
order topology (or a product of such types) is compact.

We prove the extreme value theorem (`IsCompact.exists_isMinOn`, `IsCompact.exists_isMaxOn`):
a continuous function on a compact set takes its minimum and maximum values. We provide many
variations of this theorem.

We also prove that the image of a closed interval under a continuous map is a closed interval, see
`ContinuousOn.image_Icc`.

## Tags

compact, extreme value theorem
-/

public section

open Filter OrderDual TopologicalSpace Function Set

open scoped Filter Topology

/-!
### Compactness of a closed interval

In this section we define a typeclass `CompactIccSpace α` saying that all closed intervals in `α`
are compact. Then we provide an instance for a `ConditionallyCompleteLinearOrder` and prove that
the product (both `α × β` and an indexed product) of spaces with this property inherits the
property.

We also prove some simple lemmas about spaces with this property.
-/


/--
Definition of `CompactIccSpace` / `CompactIccSpace` 的定义

English:
class CompactIccSpace
  parameters: (α : Type*) [TopologicalSpace α] [Preorder α]
  axioms and operations (1):
    - isCompact_Icc : forall {a b : α}, IsCompact (Icc a b)

中文:
类 CompactIccSpace
  参数: (α : 类型) [TopologicalSpace α] [Preorder α]
  公理与运算 (1 个):
    - isCompact_Icc : 对任意 {a b : α}, IsCompact (Icc a b)
-/
class CompactIccSpace (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- A closed interval `Set.Icc a b` is a compact set for all `a` and `b`. -/
  isCompact_Icc : forall {a b : α}, IsCompact (Icc a b)

export CompactIccSpace (isCompact_Icc)
attribute [compactness .] isCompact_Icc

variable {α : Type*}

-- TODO: make it the definition
/--
lemma `CompactIccSpace.mk'` / 引理 `CompactIccSpace.mk'`

English:
lemma CompactIccSpace.mk'
  statement: [TopologicalSpace α] [Preorder α]
  proof: by_cases h fun hab => by rw [Icc_eq_empty hab]; exact isCompact_empty

中文:
引理 CompactIccSpace.mk'
  结论: [TopologicalSpace α] [Preorder α]
  证明: by_cases h fun hab => by rw [Icc_eq_empty hab]; exact isCompact_empty

Depends on / 依赖: Icc_eq_empty, isCompact_empty
-/
lemma CompactIccSpace.mk' [TopologicalSpace α] [Preorder α]
    (h : forall {a b : α}, a <= b -> IsCompact (Icc a b)) : CompactIccSpace α where
  isCompact_Icc {a b} := by_cases h fun hab => by rw [Icc_eq_empty hab]; exact isCompact_empty

-- TODO: drop one `'`
/--
lemma `CompactIccSpace.mk''` / 引理 `CompactIccSpace.mk''`

English:
lemma CompactIccSpace.mk''
  statement: [TopologicalSpace α] [PartialOrder α]
  proof: .mk' fun hab => hab.eq_or_lt.elim (by rintro rfl; simp) h

中文:
引理 CompactIccSpace.mk''
  结论: [TopologicalSpace α] [PartialOrder α]
  证明: .mk' fun hab => hab.eq_or_lt.elim (by rintro rfl; simp) h

Depends on / 依赖: eq_or_lt, hab.eq_or_lt.elim
-/
lemma CompactIccSpace.mk'' [TopologicalSpace α] [PartialOrder α]
    (h : forall {a b : α}, a < b -> IsCompact (Icc a b)) : CompactIccSpace α :=
  .mk' fun hab => hab.eq_or_lt.elim (by rintro rfl; simp) h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [Preorder α] [CompactIccSpace α] : CompactIccSpace (αᵒᵈ) where
  body: by
    intro a b
    convert! isCompact_Icc (α := α) (a := b) (b := a) using 1
    exact Icc_toDual (α := α)

中文:
实例 [TopologicalSpace
  签名: α] [Preorder α] [CompactIccSpace α] : CompactIccSpace (αᵒᵈ) where
  定义体: by
    intro a b
    convert! isCompact_Icc (α := α) (a := b) (b := a) using 1
    exact Icc_toDual (α := α)

Depends on / 依赖: Icc_toDual, convert, isCompact_Icc
-/
instance [TopologicalSpace α] [Preorder α] [CompactIccSpace α] : CompactIccSpace (αᵒᵈ) where
  isCompact_Icc := by
    intro a b
    convert! isCompact_Icc (α := α) (a := b) (b := a) using 1
    exact Icc_toDual (α := α)

/-- A closed interval in a conditionally complete linear order is compact. -/
instance (priority := 100) ConditionallyCompleteLinearOrder.toCompactIccSpace (α : Type*)
    [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] :
    CompactIccSpace α := ⟨fun {_ _} => ConditionallyCompleteLinearOrder.isCompact_Icc _ _⟩

instance {ι : Type*} {α : ι -> Type*} [forall i, Preorder (α i)] [forall i, TopologicalSpace (α i)]
    [forall i, CompactIccSpace (α i)] : CompactIccSpace (forall i, α i) :=
  ⟨fun {a b} => (pi_univ_Icc a b ▸ isCompact_univ_pi) fun _ => isCompact_Icc⟩

/--
Instance `Pi.compact_Icc_space'` / 实例 `Pi.compact_Icc_space'`

English:
instance Pi.compact_Icc_space'
  signature: {α β : Type*} [Preorder β] [TopologicalSpace β]
  body: inferInstance

中文:
实例 Pi.compact_Icc_space'
  签名: {α β : 类型} [Preorder β] [TopologicalSpace β]
  定义体: inferInstance
-/
instance Pi.compact_Icc_space' {α β : Type*} [Preorder β] [TopologicalSpace β]
    [CompactIccSpace β] : CompactIccSpace (α -> β) :=
  inferInstance

instance {α β : Type*} [Preorder α] [TopologicalSpace α] [CompactIccSpace α] [Preorder β]
    [TopologicalSpace β] [CompactIccSpace β] : CompactIccSpace (α × β) :=
  ⟨fun {a b} => (Icc_prod_eq a b).symm ▸ isCompact_Icc.prod isCompact_Icc⟩

/-- An unordered closed interval is compact. -/
@[compactness .]
/--
theorem `isCompact_uIcc` / 定理 `isCompact_uIcc`

English:
theorem isCompact_uIcc
  statement: {α : Type*} [LinearOrder α] [TopologicalSpace α] [CompactIccSpace α]
  proof: isCompact_Icc

中文:
定理 isCompact_uIcc
  结论: {α : 类型} [LinearOrder α] [TopologicalSpace α] [CompactIccSpace α]
  证明: isCompact_Icc

Depends on / 依赖: isCompact_Icc
-/
theorem isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalSpace α] [CompactIccSpace α]
    {a b : α} : IsCompact (uIcc a b) :=
  isCompact_Icc

-- See note [lower instance priority]
/-- A complete linear order is a compact space.

We do not register an instance for a `[CompactIccSpace α]` because this would only add instances
for products (indexed or not) of complete linear orders, and we have instances with higher priority
that cover these cases. -/
instance (priority := 100) compactSpace_of_completeLinearOrder {α : Type*} [CompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] : CompactSpace α :=
  ⟨by simp only [← Icc_bot_top, isCompact_Icc]⟩

section

variable {α : Type*} [Preorder α] [TopologicalSpace α] [CompactIccSpace α]

/--
Instance `compactSpace_Icc` / 实例 `compactSpace_Icc`

English:
instance compactSpace_Icc
  signature: (a b : α)
  body: isCompact_iff_compactSpace.mp isCompact_Icc

中文:
实例 compactSpace_Icc
  签名: (a b : α)
  定义体: isCompact_iff_compactSpace.mp isCompact_Icc

Depends on / 依赖: isCompact_Icc, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp
-/
instance compactSpace_Icc (a b : α) : CompactSpace (Icc a b) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

end

section openIntervals
variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]

/-- `Set.Ico a b` is only compact if it is empty. -/
@[simp]
/--
theorem `isCompact_Ico_iff` / 定理 `isCompact_Ico_iff`

English:
theorem isCompact_Ico_iff
  given: {a b : α}
  statement: IsCompact (Set.Ico a b) ↔ b <= a
  proof: ⟨fun h => isClosed_Ico_iff.mp h.isClosed, by simp_all⟩

中文:
定理 isCompact_Ico_iff
  条件: {a b : α}
  结论: IsCompact (Set.Ico a b) ↔ b <= a
  证明: ⟨fun h => isClosed_Ico_iff.mp h.isClosed, by simp_all⟩

Depends on / 依赖: h.isClosed, isClosed, isClosed_Ico_iff, isClosed_Ico_iff.mp
-/
theorem isCompact_Ico_iff {a b : α} : IsCompact (Set.Ico a b) ↔ b <= a :=
  ⟨fun h => isClosed_Ico_iff.mp h.isClosed, by simp_all⟩

/-- `Set.Ioc a b` is only compact if it is empty. -/
@[simp]
/--
theorem `isCompact_Ioc_iff` / 定理 `isCompact_Ioc_iff`

English:
theorem isCompact_Ioc_iff
  given: {a b : α}
  statement: IsCompact (Set.Ioc a b) ↔ b <= a
  proof: ⟨fun h => isClosed_Ioc_iff.mp h.isClosed, by simp_all⟩

中文:
定理 isCompact_Ioc_iff
  条件: {a b : α}
  结论: IsCompact (Set.Ioc a b) ↔ b <= a
  证明: ⟨fun h => isClosed_Ioc_iff.mp h.isClosed, by simp_all⟩

Depends on / 依赖: h.isClosed, isClosed, isClosed_Ioc_iff, isClosed_Ioc_iff.mp
-/
theorem isCompact_Ioc_iff {a b : α} : IsCompact (Set.Ioc a b) ↔ b <= a :=
  ⟨fun h => isClosed_Ioc_iff.mp h.isClosed, by simp_all⟩

/-- `Set.Ioo a b` is only compact if it is empty. -/
@[simp]
/--
theorem `isCompact_Ioo_iff` / 定理 `isCompact_Ioo_iff`

English:
theorem isCompact_Ioo_iff
  given: {a b : α}
  statement: IsCompact (Set.Ioo a b) ↔ b <= a
  proof: ⟨fun h => isClosed_Ioo_iff.mp h.isClosed, by simp_all⟩

中文:
定理 isCompact_Ioo_iff
  条件: {a b : α}
  结论: IsCompact (Set.Ioo a b) ↔ b <= a
  证明: ⟨fun h => isClosed_Ioo_iff.mp h.isClosed, by simp_all⟩

Depends on / 依赖: h.isClosed, isClosed, isClosed_Ioo_iff, isClosed_Ioo_iff.mp
-/
theorem isCompact_Ioo_iff {a b : α} : IsCompact (Set.Ioo a b) ↔ b <= a :=
  ⟨fun h => isClosed_Ioo_iff.mp h.isClosed, by simp_all⟩

end openIntervals

/-!
### Extreme value theorem
-/

section LinearOrder

variable {α β γ : Type*} [LinearOrder α] [TopologicalSpace α]
  [TopologicalSpace β] [TopologicalSpace γ]

/--
theorem `IsCompact.exists_isLeast` / 定理 `IsCompact.exists_isLeast`

English:
theorem IsCompact.exists_isLeast
  statement: [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
  proof: by
  have : Nonempty s := ne_s.to_subtype
  suffices (s inter ⋂ x in s, Iic x).Nonempty from
    ⟨this.choose, this.choose_spec.1, mem_iInter₂.mp this.choose_spec.2⟩
  rw [biInter_eq_iInter]
  by_contra H
  rw [not_nonempty_iff_eq_empty] at H
  rcases hs.elim_directed_family_closed (fun x : s => Iic

中文:
定理 IsCompact.exists_isLeast
  结论: [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
  证明: by
  have : Nonempty s := ne_s.to_subtype
  suffices (s inter ⋂ x in s, Iic x).Nonempty from
    ⟨this.choose, this.choose_spec.1, mem_iInter₂.mp this.choose_spec.2⟩
  rw [biInter_eq_iInter]
  by_contra H
  rw [not_nonempty_iff_eq_empty] at H
  rcases hs.elim_directed_family_closed (fun x : s => Iic

Depends on / 依赖: Iic_subset_Iic, Iic_subset_Iic.mpr, Monotone, Monotone.directed_ge, Nonempty, biInter_eq_iInter, choose_spec, directed_ge, elim_directed_family_closed, hs.elim_directed_family_closed, isClosed_Iic, le_rfl, ne_s, ne_s.to_subtype, not_nonempty_iff_eq_empty, not_nonempty_iff_eq_empty.mpr, this.choose, this.choose_spec, to_subtype
-/
theorem IsCompact.exists_isLeast [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : exists x, IsLeast s x := by
  have : Nonempty s := ne_s.to_subtype
  suffices (s inter ⋂ x in s, Iic x).Nonempty from
    ⟨this.choose, this.choose_spec.1, mem_iInter₂.mp this.choose_spec.2⟩
  rw [biInter_eq_iInter]
  by_contra H
  rw [not_nonempty_iff_eq_empty] at H
  rcases hs.elim_directed_family_closed (fun x : s => Iic ↑x) (fun x => isClosed_Iic) H
      (Monotone.directed_ge fun _ _ h => Iic_subset_Iic.mpr h) with ⟨x, hx⟩
  exact not_nonempty_iff_eq_empty.mpr hx ⟨x, x.2, le_rfl⟩

/--
theorem `IsCompact.exists_isGreatest` / 定理 `IsCompact.exists_isGreatest`

English:
theorem IsCompact.exists_isGreatest
  statement: [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
  proof: IsCompact.exists_isLeast (α := αᵒᵈ) hs ne_s

中文:
定理 IsCompact.exists_isGreatest
  结论: [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
  证明: IsCompact.exists_isLeast (α := αᵒᵈ) hs ne_s

Depends on / 依赖: IsCompact, IsCompact.exists_isLeast, exists_isLeast, ne_s
-/
theorem IsCompact.exists_isGreatest [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : exists x, IsGreatest s x :=
  IsCompact.exists_isLeast (α := αᵒᵈ) hs ne_s

/--
theorem `IsCompact.exists_isGLB` / 定理 `IsCompact.exists_isGLB`

English:
theorem IsCompact.exists_isGLB
  statement: [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
  proof: (hs.exists_isLeast ne_s).imp (fun x (hx : IsLeast s x) => ⟨hx.1, hx.isGLB⟩)

中文:
定理 IsCompact.exists_isGLB
  结论: [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
  证明: (hs.exists_isLeast ne_s).imp (fun x (hx : IsLeast s x) => ⟨hx.1, hx.isGLB⟩)

Depends on / 依赖: IsLeast, exists_isLeast, hs.exists_isLeast, hx.isGLB, ne_s
-/
theorem IsCompact.exists_isGLB [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : exists x in s, IsGLB s x :=
  (hs.exists_isLeast ne_s).imp (fun x (hx : IsLeast s x) => ⟨hx.1, hx.isGLB⟩)

/--
theorem `IsCompact.exists_isLUB` / 定理 `IsCompact.exists_isLUB`

English:
theorem IsCompact.exists_isLUB
  statement: [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
  proof: IsCompact.exists_isGLB (α := αᵒᵈ) hs ne_s

中文:
定理 IsCompact.exists_isLUB
  结论: [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
  证明: IsCompact.exists_isGLB (α := αᵒᵈ) hs ne_s

Depends on / 依赖: IsCompact, IsCompact.exists_isGLB, exists_isGLB, ne_s
-/
theorem IsCompact.exists_isLUB [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : exists x in s, IsLUB s x :=
  IsCompact.exists_isGLB (α := αᵒᵈ) hs ne_s

/--
theorem `cocompact_le_atBot_atTop` / 定理 `cocompact_le_atBot_atTop`

English:
theorem cocompact_le_atBot_atTop
  given: [CompactIccSpace α]
  proof: by
refine fun s hs => mem_cocompact.mpr (isEmpty_or_nonempty α).casesOn ?_ ?_ <;> intro
  · exact ⟨∅, isCompact_empty, fun x _ => (IsEmpty.false x).elim⟩
  · obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs.1
    obtain ⟨u, hu⟩ := mem_atTop_sets.mp hs.2
    refine ⟨Icc t u, isCompact_Icc, fun x hx => ?_⟩
    

中文:
定理 cocompact_le_atBot_atTop
  条件: [CompactIccSpace α]
  证明: by
refine fun s hs => mem_cocompact.mpr (isEmpty_or_nonempty α).casesOn ?_ ?_ <;> intro
  · exact ⟨∅, isCompact_empty, fun x _ => (IsEmpty.false x).elim⟩
  · obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs.1
    obtain ⟨u, hu⟩ := mem_atTop_sets.mp hs.2
    refine ⟨Icc t u, isCompact_Icc, fun x hx => ?_⟩
    

Depends on / 依赖: IsEmpty, IsEmpty.false, casesOn, isCompact_Icc, isCompact_empty, isEmpty_or_nonempty, le_of_not_ge, mem_atBot_sets, mem_atBot_sets.mp, mem_atTop_sets, mem_atTop_sets.mp, mem_cocompact, mem_cocompact.mpr, not_and_or, not_and_or.mp
-/
theorem cocompact_le_atBot_atTop [CompactIccSpace α] :
    cocompact α <= atBot ⊔ atTop := by
refine fun s hs => mem_cocompact.mpr (isEmpty_or_nonempty α).casesOn ?_ ?_ <;> intro
  · exact ⟨∅, isCompact_empty, fun x _ => (IsEmpty.false x).elim⟩
  · obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs.1
    obtain ⟨u, hu⟩ := mem_atTop_sets.mp hs.2
    refine ⟨Icc t u, isCompact_Icc, fun x hx => ?_⟩
    exact (not_and_or.mp hx).casesOn (fun h => ht x (le_of_not_ge h)) fun h => hu x (le_of_not_ge h)

/--
theorem `cocompact_le_atBot` / 定理 `cocompact_le_atBot`

English:
theorem cocompact_le_atBot
  given: [OrderTop α] [CompactIccSpace α]
  proof: by
refine fun _ hs => mem_cocompact.mpr (isEmpty_or_nonempty α).casesOn ?_ ?_ <;> intro
  · exact ⟨∅, isCompact_empty, fun x _ => (IsEmpty.false x).elim⟩
  · obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs
    refine ⟨Icc t ⊤, isCompact_Icc, fun _ hx => ?_⟩
    exact (not_and_or.mp hx).casesOn (fun h => ht _

中文:
定理 cocompact_le_atBot
  条件: [OrderTop α] [CompactIccSpace α]
  证明: by
refine fun _ hs => mem_cocompact.mpr (isEmpty_or_nonempty α).casesOn ?_ ?_ <;> intro
  · exact ⟨∅, isCompact_empty, fun x _ => (IsEmpty.false x).elim⟩
  · obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs
    refine ⟨Icc t ⊤, isCompact_Icc, fun _ hx => ?_⟩
    exact (not_and_or.mp hx).casesOn (fun h => ht _

Depends on / 依赖: IsEmpty, IsEmpty.false, casesOn, isCompact_Icc, isCompact_empty, isEmpty_or_nonempty, le_of_not_ge, le_top, mem_atBot_sets, mem_atBot_sets.mp, mem_cocompact, mem_cocompact.mpr, not_and_or, not_and_or.mp
-/
theorem cocompact_le_atBot [OrderTop α] [CompactIccSpace α] :
    cocompact α <= atBot := by
refine fun _ hs => mem_cocompact.mpr (isEmpty_or_nonempty α).casesOn ?_ ?_ <;> intro
  · exact ⟨∅, isCompact_empty, fun x _ => (IsEmpty.false x).elim⟩
  · obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs
    refine ⟨Icc t ⊤, isCompact_Icc, fun _ hx => ?_⟩
    exact (not_and_or.mp hx).casesOn (fun h => ht _ (le_of_not_ge h)) (fun h => (h le_top).elim)

/--
theorem `cocompact_le_atTop` / 定理 `cocompact_le_atTop`

English:
theorem cocompact_le_atTop
  given: [OrderBot α] [CompactIccSpace α]
  proof: cocompact_le_atBot (α := αᵒᵈ)

中文:
定理 cocompact_le_atTop
  条件: [OrderBot α] [CompactIccSpace α]
  证明: cocompact_le_atBot (α := αᵒᵈ)

Depends on / 依赖: cocompact_le_atBot
-/
theorem cocompact_le_atTop [OrderBot α] [CompactIccSpace α] :
    cocompact α <= atTop :=
  cocompact_le_atBot (α := αᵒᵈ)

/--
theorem `atBot_le_cocompact` / 定理 `atBot_le_cocompact`

English:
theorem atBot_le_cocompact
  given: [NoMinOrder α] [ClosedIicTopology α]
  proof: by
  refine fun s hs => ?_
  obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hs
  refine (Set.eq_empty_or_nonempty t).casesOn (fun h_empty => ?_) (fun h_nonempty => ?_)
  · rewrite [compl_univ_iff.mpr h_empty, univ_subset_iff] at hts
    convert! univ_mem
  · have := h_nonempty.nonempty
    obtain ⟨a, ha⟩ :

中文:
定理 atBot_le_cocompact
  条件: [NoMinOrder α] [ClosedIicTopology α]
  证明: by
  refine fun s hs => ?_
  obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hs
  refine (Set.eq_empty_or_nonempty t).casesOn (fun h_empty => ?_) (fun h_nonempty => ?_)
  · rewrite [compl_univ_iff.mpr h_empty, univ_subset_iff] at hts
    convert! univ_mem
  · have := h_nonempty.nonempty
    obtain ⟨a, ha⟩ :

Depends on / 依赖: Classical, Classical.byContradiction, Filter, Filter.mem_atBot_sets.mpr, LT.lt.false, Set.eq_empty_or_nonempty, byContradiction, casesOn, compl_univ_iff, compl_univ_iff.mpr, convert, eq_empty_or_nonempty, exists_isLeast, exists_lt, h_empty, h_nonempty, h_nonempty.nonempty, hb.trans_le, ht.exists_isLeast, mem_atBot_sets
-/
theorem atBot_le_cocompact [NoMinOrder α] [ClosedIicTopology α] :
    atBot <= cocompact α := by
  refine fun s hs => ?_
  obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hs
  refine (Set.eq_empty_or_nonempty t).casesOn (fun h_empty => ?_) (fun h_nonempty => ?_)
  · rewrite [compl_univ_iff.mpr h_empty, univ_subset_iff] at hts
    convert! univ_mem
  · have := h_nonempty.nonempty
    obtain ⟨a, ha⟩ := ht.exists_isLeast h_nonempty
    obtain ⟨b, hb⟩ := exists_lt a
exact Filter.mem_atBot_sets.mpr ⟨b, fun b' hb' => hts Classical.byContradiction
fun hc => LT.lt.false hb'.trans_lt hb.trans_le ha.2 (not_notMem.mp hc)⟩

/--
theorem `atTop_le_cocompact` / 定理 `atTop_le_cocompact`

English:
theorem atTop_le_cocompact
  given: [NoMaxOrder α] [ClosedIciTopology α]
  proof: atBot_le_cocompact (α := αᵒᵈ)

中文:
定理 atTop_le_cocompact
  条件: [NoMaxOrder α] [ClosedIciTopology α]
  证明: atBot_le_cocompact (α := αᵒᵈ)

Depends on / 依赖: atBot_le_cocompact
-/
theorem atTop_le_cocompact [NoMaxOrder α] [ClosedIciTopology α] :
    atTop <= cocompact α :=
  atBot_le_cocompact (α := αᵒᵈ)

/--
theorem `atBot_atTop_le_cocompact` / 定理 `atBot_atTop_le_cocompact`

English:
theorem atBot_atTop_le_cocompact
  statement: [NoMinOrder α] [NoMaxOrder α]
  proof: sup_le atBot_le_cocompact atTop_le_cocompact

@[simp 900]

中文:
定理 atBot_atTop_le_cocompact
  结论: [NoMinOrder α] [NoMaxOrder α]
  证明: sup_le atBot_le_cocompact atTop_le_cocompact

@[simp 900]

Depends on / 依赖: atBot_le_cocompact, atTop_le_cocompact, sup_le
-/
theorem atBot_atTop_le_cocompact [NoMinOrder α] [NoMaxOrder α]
    [OrderClosedTopology α] : atBot ⊔ atTop <= cocompact α :=
  sup_le atBot_le_cocompact atTop_le_cocompact

@[simp 900]
/--
theorem `cocompact_eq_atBot_atTop` / 定理 `cocompact_eq_atBot_atTop`

English:
theorem cocompact_eq_atBot_atTop
  statement: [NoMaxOrder α] [NoMinOrder α]
  proof: cocompact_le_atBot_atTop.antisymm atBot_atTop_le_cocompact

@[simp]

中文:
定理 cocompact_eq_atBot_atTop
  结论: [NoMaxOrder α] [NoMinOrder α]
  证明: cocompact_le_atBot_atTop.antisymm atBot_atTop_le_cocompact

@[simp]

Depends on / 依赖: antisymm, atBot_atTop_le_cocompact, cocompact_le_atBot_atTop, cocompact_le_atBot_atTop.antisymm
-/
theorem cocompact_eq_atBot_atTop [NoMaxOrder α] [NoMinOrder α]
    [OrderClosedTopology α] [CompactIccSpace α] : cocompact α = atBot ⊔ atTop :=
  cocompact_le_atBot_atTop.antisymm atBot_atTop_le_cocompact

@[simp]
/--
theorem `cocompact_eq_atBot` / 定理 `cocompact_eq_atBot`

English:
theorem cocompact_eq_atBot
  statement: [NoMinOrder α] [OrderTop α]
  proof: cocompact_le_atBot.antisymm atBot_le_cocompact

@[simp]

中文:
定理 cocompact_eq_atBot
  结论: [NoMinOrder α] [OrderTop α]
  证明: cocompact_le_atBot.antisymm atBot_le_cocompact

@[simp]

Depends on / 依赖: antisymm, atBot_le_cocompact, cocompact_le_atBot, cocompact_le_atBot.antisymm
-/
theorem cocompact_eq_atBot [NoMinOrder α] [OrderTop α]
    [ClosedIicTopology α] [CompactIccSpace α] : cocompact α = atBot :=
  cocompact_le_atBot.antisymm atBot_le_cocompact

@[simp]
/--
theorem `cocompact_eq_atTop` / 定理 `cocompact_eq_atTop`

English:
theorem cocompact_eq_atTop
  statement: [NoMaxOrder α] [OrderBot α]
  proof: cocompact_le_atTop.antisymm atTop_le_cocompact

中文:
定理 cocompact_eq_atTop
  结论: [NoMaxOrder α] [OrderBot α]
  证明: cocompact_le_atTop.antisymm atTop_le_cocompact

Depends on / 依赖: antisymm, atTop_le_cocompact, cocompact_le_atTop, cocompact_le_atTop.antisymm
-/
theorem cocompact_eq_atTop [NoMaxOrder α] [OrderBot α]
    [ClosedIciTopology α] [CompactIccSpace α] : cocompact α = atTop :=
  cocompact_le_atTop.antisymm atTop_le_cocompact

/--
theorem `IsCompact.exists_isMinOn` / 定理 `IsCompact.exists_isMinOn`

English:
theorem IsCompact.exists_isMinOn
  statement: [ClosedIicTopology α] {s : Set β} (hs : IsCompact s)
  proof: by
  rcases (hs.image_of_continuousOn hf).exists_isLeast (ne_s.image f) with ⟨_, ⟨x, hxs, rfl⟩, hx⟩
  refine ⟨x, hxs, forall_mem_image.1 (fun _ hb => hx <| mem_image_of_mem f ?_)⟩
  rwa [(image_id' s).symm]

中文:
定理 IsCompact.exists_isMinOn
  结论: [ClosedIicTopology α] {s : Set β} (hs : IsCompact s)
  证明: by
  rcases (hs.image_of_continuousOn hf).exists_isLeast (ne_s.image f) with ⟨_, ⟨x, hxs, rfl⟩, hx⟩
  refine ⟨x, hxs, forall_mem_image.1 (fun _ hb => hx <| mem_image_of_mem f ?_)⟩
  rwa [(image_id' s).symm]

Depends on / 依赖: exists_isLeast, forall_mem_image, hs.image_of_continuousOn, image_id, image_of_continuousOn, mem_image_of_mem, ne_s, ne_s.image
-/
theorem IsCompact.exists_isMinOn [ClosedIicTopology α] {s : Set β} (hs : IsCompact s)
    (ne_s : s.Nonempty) {f : β -> α} (hf : ContinuousOn f s) : exists x in s, IsMinOn f s x := by
  rcases (hs.image_of_continuousOn hf).exists_isLeast (ne_s.image f) with ⟨_, ⟨x, hxs, rfl⟩, hx⟩
  refine ⟨x, hxs, forall_mem_image.1 (fun _ hb => hx <| mem_image_of_mem f ?_)⟩
  rwa [(image_id' s).symm]

/--
theorem `IsCompact.exists_forall_le'` / 定理 `IsCompact.exists_forall_le'`

English:
theorem IsCompact.exists_forall_le'
  statement: [ClosedIicTopology α] [NoMaxOrder α] {f : β -> α}
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | hs')
  · obtain ⟨a', ha'⟩ := exists_gt a
    exact ⟨a', ha', fun _ a => a.elim⟩
  · obtain ⟨x, hx, hx'⟩ := hs.exists_isMinOn hs' hf
    exact ⟨f x, hf' x hx, hx'⟩

中文:
定理 IsCompact.exists_forall_le'
  结论: [ClosedIicTopology α] [NoMaxOrder α] {f : β -> α}
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | hs')
  · obtain ⟨a', ha'⟩ := exists_gt a
    exact ⟨a', ha', fun _ a => a.elim⟩
  · obtain ⟨x, hx, hx'⟩ := hs.exists_isMinOn hs' hf
    exact ⟨f x, hf' x hx, hx'⟩

Depends on / 依赖: a.elim, eq_empty_or_nonempty, exists_gt, exists_isMinOn, hs.exists_isMinOn, s.eq_empty_or_nonempty
-/
theorem IsCompact.exists_forall_le' [ClosedIicTopology α] [NoMaxOrder α] {f : β -> α}
    {s : Set β} (hs : IsCompact s) (hf : ContinuousOn f s) {a : α} (hf' : forall b in s, a < f b) :
    exists a', a < a' ∧ forall b in s, a' <= f b := by
  rcases s.eq_empty_or_nonempty with (rfl | hs')
  · obtain ⟨a', ha'⟩ := exists_gt a
    exact ⟨a', ha', fun _ a => a.elim⟩
  · obtain ⟨x, hx, hx'⟩ := hs.exists_isMinOn hs' hf
    exact ⟨f x, hf' x hx, hx'⟩

/--
theorem `IsCompact.exists_isMaxOn` / 定理 `IsCompact.exists_isMaxOn`

English:
theorem IsCompact.exists_isMaxOn
  statement: [ClosedIciTopology α] {s : Set β} (hs : IsCompact s)
  proof: IsCompact.exists_isMinOn (α := αᵒᵈ) hs ne_s hf

中文:
定理 IsCompact.exists_isMaxOn
  结论: [ClosedIciTopology α] {s : Set β} (hs : IsCompact s)
  证明: IsCompact.exists_isMinOn (α := αᵒᵈ) hs ne_s hf

Depends on / 依赖: IsCompact, IsCompact.exists_isMinOn, exists_isMinOn, ne_s
-/
theorem IsCompact.exists_isMaxOn [ClosedIciTopology α] {s : Set β} (hs : IsCompact s)
    (ne_s : s.Nonempty) {f : β -> α} (hf : ContinuousOn f s) : exists x in s, IsMaxOn f s x :=
  IsCompact.exists_isMinOn (α := αᵒᵈ) hs ne_s hf

/--
theorem `ContinuousOn.exists_isMinOn'` / 定理 `ContinuousOn.exists_isMinOn'`

English:
theorem ContinuousOn.exists_isMinOn'
  statement: [ClosedIicTopology α] {s : Set β} {f : β -> α}
  proof: by
  rcases (hasBasis_cocompact.inf_principal _).eventually_iff.1 hc with ⟨K, hK, hKf⟩
  have hsub : insert x₀ (K inter s) subseteq s := insert_subset_iff.2 ⟨h₀, inter_subset_right⟩
  obtain ⟨x, hx, hxf⟩ : exists x in insert x₀ (K inter s), forall y in insert x₀ (K inter s), f x <= f y :=
    ((hK.i

中文:
定理 ContinuousOn.exists_isMinOn'
  结论: [ClosedIicTopology α] {s : Set β} {f : β -> α}
  证明: by
  rcases (hasBasis_cocompact.inf_principal _).eventually_iff.1 hc with ⟨K, hK, hKf⟩
  have hsub : insert x₀ (K inter s) subseteq s := insert_subset_iff.2 ⟨h₀, inter_subset_right⟩
  obtain ⟨x, hx, hxf⟩ : exists x in insert x₀ (K inter s), forall y in insert x₀ (K inter s), f x <= f y :=
    ((hK.i

Depends on / 依赖: Or.inl, Or.inr, eventually_iff, exacts, exists_isMinOn, hK.inter_right, hasBasis_cocompact, hasBasis_cocompact.inf_principal, hf.mono, inf_principal, insert, insert_nonempty, insert_subset_iff, inter_right, inter_subset_right, subseteq
-/
theorem ContinuousOn.exists_isMinOn' [ClosedIicTopology α] {s : Set β} {f : β -> α}
    (hf : ContinuousOn f s) (hsc : IsClosed s) {x₀ : β} (h₀ : x₀ in s)
    (hc : forallᶠ x in cocompact β ⊓ 𝓟 s, f x₀ <= f x) : exists x in s, IsMinOn f s x := by
  rcases (hasBasis_cocompact.inf_principal _).eventually_iff.1 hc with ⟨K, hK, hKf⟩
  have hsub : insert x₀ (K inter s) subseteq s := insert_subset_iff.2 ⟨h₀, inter_subset_right⟩
  obtain ⟨x, hx, hxf⟩ : exists x in insert x₀ (K inter s), forall y in insert x₀ (K inter s), f x <= f y :=
    ((hK.inter_right hsc).insert x₀).exists_isMinOn (insert_nonempty _ _) (hf.mono hsub)
  refine ⟨x, hsub hx, fun y hy => ?_⟩
  by_cases hyK : y in K
  exacts [hxf _ (Or.inr ⟨hyK, hy⟩), (hxf _ (Or.inl rfl)).trans (hKf ⟨hyK, hy⟩)]

/--
theorem `ContinuousOn.exists_isMaxOn'` / 定理 `ContinuousOn.exists_isMaxOn'`

English:
theorem ContinuousOn.exists_isMaxOn'
  statement: [ClosedIciTopology α] {s : Set β} {f : β -> α}
  proof: ContinuousOn.exists_isMinOn' (α := αᵒᵈ) hf hsc h₀ hc

中文:
定理 ContinuousOn.exists_isMaxOn'
  结论: [ClosedIciTopology α] {s : Set β} {f : β -> α}
  证明: ContinuousOn.exists_isMinOn' (α := αᵒᵈ) hf hsc h₀ hc

Depends on / 依赖: ContinuousOn, ContinuousOn.exists_isMinOn, exists_isMinOn
-/
theorem ContinuousOn.exists_isMaxOn' [ClosedIciTopology α] {s : Set β} {f : β -> α}
    (hf : ContinuousOn f s) (hsc : IsClosed s) {x₀ : β} (h₀ : x₀ in s)
    (hc : forallᶠ x in cocompact β ⊓ 𝓟 s, f x <= f x₀) : exists x in s, IsMaxOn f s x :=
  ContinuousOn.exists_isMinOn' (α := αᵒᵈ) hf hsc h₀ hc

/--
theorem `Continuous.exists_forall_le'` / 定理 `Continuous.exists_forall_le'`

English:
theorem Continuous.exists_forall_le'
  statement: [ClosedIicTopology α] {f : β -> α} (hf : Continuous f)
  proof: let ⟨x, _, hx⟩ := hf.continuousOn.exists_isMinOn' isClosed_univ (mem_univ x₀)
    (by rwa [principal_univ, inf_top_eq])
  ⟨x, fun y => hx (mem_univ y)⟩

中文:
定理 Continuous.exists_forall_le'
  结论: [ClosedIicTopology α] {f : β -> α} (hf : Continuous f)
  证明: let ⟨x, _, hx⟩ := hf.continuousOn.exists_isMinOn' isClosed_univ (mem_univ x₀)
    (by rwa [principal_univ, inf_top_eq])
  ⟨x, fun y => hx (mem_univ y)⟩

Depends on / 依赖: continuousOn, exists_isMinOn, hf.continuousOn.exists_isMinOn, inf_top_eq, isClosed_univ, mem_univ, principal_univ
-/
theorem Continuous.exists_forall_le' [ClosedIicTopology α] {f : β -> α} (hf : Continuous f)
    (x₀ : β) (h : forallᶠ x in cocompact β, f x₀ <= f x) : exists x : β, forall y : β, f x <= f y :=
  let ⟨x, _, hx⟩ := hf.continuousOn.exists_isMinOn' isClosed_univ (mem_univ x₀)
    (by rwa [principal_univ, inf_top_eq])
  ⟨x, fun y => hx (mem_univ y)⟩

/--
theorem `Continuous.exists_forall_ge'` / 定理 `Continuous.exists_forall_ge'`

English:
theorem Continuous.exists_forall_ge'
  statement: [ClosedIciTopology α] {f : β -> α} (hf : Continuous f)
  proof: Continuous.exists_forall_le' (α := αᵒᵈ) hf x₀ h

中文:
定理 Continuous.exists_forall_ge'
  结论: [ClosedIciTopology α] {f : β -> α} (hf : Continuous f)
  证明: Continuous.exists_forall_le' (α := αᵒᵈ) hf x₀ h

Depends on / 依赖: Continuous, Continuous.exists_forall_le, exists_forall_le
-/
theorem Continuous.exists_forall_ge' [ClosedIciTopology α] {f : β -> α} (hf : Continuous f)
    (x₀ : β) (h : forallᶠ x in cocompact β, f x <= f x₀) : exists x : β, forall y : β, f y <= f x :=
  Continuous.exists_forall_le' (α := αᵒᵈ) hf x₀ h

/--
theorem `Continuous.exists_forall_le` / 定理 `Continuous.exists_forall_le`

English:
theorem Continuous.exists_forall_le
  statement: [ClosedIicTopology α] [Nonempty β] {f : β -> α}
  proof: by
  inhabit β
  exact hf.exists_forall_le' default (hlim.eventually <| eventually_ge_atTop _)

中文:
定理 Continuous.exists_forall_le
  结论: [ClosedIicTopology α] [Nonempty β] {f : β -> α}
  证明: by
  inhabit β
  exact hf.exists_forall_le' default (hlim.eventually <| eventually_ge_atTop _)

Depends on / 依赖: eventually, eventually_ge_atTop, exists_forall_le, hf.exists_forall_le, hlim.eventually, inhabit
-/
theorem Continuous.exists_forall_le [ClosedIicTopology α] [Nonempty β] {f : β -> α}
    (hf : Continuous f) (hlim : Tendsto f (cocompact β) atTop) : exists x, forall y, f x <= f y := by
  inhabit β
  exact hf.exists_forall_le' default (hlim.eventually <| eventually_ge_atTop _)

/--
theorem `Continuous.exists_forall_ge` / 定理 `Continuous.exists_forall_ge`

English:
theorem Continuous.exists_forall_ge
  statement: [ClosedIciTopology α] [Nonempty β] {f : β -> α}
  proof: Continuous.exists_forall_le (α := αᵒᵈ) hf hlim

中文:
定理 Continuous.exists_forall_ge
  结论: [ClosedIciTopology α] [Nonempty β] {f : β -> α}
  证明: Continuous.exists_forall_le (α := αᵒᵈ) hf hlim

Depends on / 依赖: Continuous, Continuous.exists_forall_le, exists_forall_le
-/
theorem Continuous.exists_forall_ge [ClosedIciTopology α] [Nonempty β] {f : β -> α}
    (hf : Continuous f) (hlim : Tendsto f (cocompact β) atBot) : exists x, forall y, f y <= f x :=
  Continuous.exists_forall_le (α := αᵒᵈ) hf hlim

/-- A continuous function with compact support has a global minimum. -/
@[to_additive /-- A continuous function with compact support has a global minimum. -/]
/--
theorem `Continuous.exists_forall_le_of_hasCompactMulSupport` / 定理 `Continuous.exists_forall_le_of_hasCompactMulSupport`

English:
theorem Continuous.exists_forall_le_of_hasCompactMulSupport
  statement: [ClosedIicTopology α] [Nonempty β]
  proof: by
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := (h.isCompact_range hf).exists_isLeast (range_nonempty _)
  rw [mem_lowerBounds]; rw [forall_mem_range] at hx
  exact ⟨x, hx⟩

中文:
定理 Continuous.exists_forall_le_of_hasCompactMulSupport
  结论: [ClosedIicTopology α] [Nonempty β]
  证明: by
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := (h.isCompact_range hf).exists_isLeast (range_nonempty _)
  rw [mem_lowerBounds]; rw [forall_mem_range] at hx
  exact ⟨x, hx⟩

Depends on / 依赖: exists_isLeast, forall_mem_range, h.isCompact_range, isCompact_range, mem_lowerBounds, range_nonempty
-/
theorem Continuous.exists_forall_le_of_hasCompactMulSupport [ClosedIicTopology α] [Nonempty β]
    [One α] {f : β -> α} (hf : Continuous f) (h : HasCompactMulSupport f) :
    exists x : β, forall y : β, f x <= f y := by
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := (h.isCompact_range hf).exists_isLeast (range_nonempty _)
  rw [mem_lowerBounds]; rw [forall_mem_range] at hx
  exact ⟨x, hx⟩

/-- A continuous function with compact support has a global maximum. -/
@[to_additive /-- A continuous function with compact support has a global maximum. -/]
/--
theorem `Continuous.exists_forall_ge_of_hasCompactMulSupport` / 定理 `Continuous.exists_forall_ge_of_hasCompactMulSupport`

English:
theorem Continuous.exists_forall_ge_of_hasCompactMulSupport
  statement: [ClosedIciTopology α] [Nonempty β]
  proof: Continuous.exists_forall_le_of_hasCompactMulSupport (α := αᵒᵈ) hf h

中文:
定理 Continuous.exists_forall_ge_of_hasCompactMulSupport
  结论: [ClosedIciTopology α] [Nonempty β]
  证明: Continuous.exists_forall_le_of_hasCompactMulSupport (α := αᵒᵈ) hf h

Depends on / 依赖: Continuous, Continuous.exists_forall_le_of_hasCompactMulSupport, exists_forall_le_of_hasCompactMulSupport
-/
theorem Continuous.exists_forall_ge_of_hasCompactMulSupport [ClosedIciTopology α] [Nonempty β]
    [One α] {f : β -> α} (hf : Continuous f) (h : HasCompactMulSupport f) :
    exists x : β, forall y : β, f y <= f x :=
  Continuous.exists_forall_le_of_hasCompactMulSupport (α := αᵒᵈ) hf h

/--
theorem `IsCompact.bddBelow` / 定理 `IsCompact.bddBelow`

English:
theorem IsCompact.bddBelow
  given: [ClosedIicTopology α] [Nonempty α] {s : Set α} (hs : IsCompact s)
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact bddBelow_empty
  · obtain ⟨a, -, has⟩ := hs.exists_isLeast hne
    exact ⟨a, has⟩

中文:
定理 IsCompact.bddBelow
  条件: [ClosedIicTopology α] [Nonempty α] {s : Set α} (hs : IsCompact s)
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact bddBelow_empty
  · obtain ⟨a, -, has⟩ := hs.exists_isLeast hne
    exact ⟨a, has⟩

Depends on / 依赖: bddBelow_empty, eq_empty_or_nonempty, exists_isLeast, hs.exists_isLeast, s.eq_empty_or_nonempty
-/
theorem IsCompact.bddBelow [ClosedIicTopology α] [Nonempty α] {s : Set α} (hs : IsCompact s) :
    BddBelow s := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact bddBelow_empty
  · obtain ⟨a, -, has⟩ := hs.exists_isLeast hne
    exact ⟨a, has⟩

/--
theorem `IsCompact.bddAbove` / 定理 `IsCompact.bddAbove`

English:
theorem IsCompact.bddAbove
  given: [ClosedIciTopology α] [Nonempty α] {s : Set α} (hs : IsCompact s)
  proof: IsCompact.bddBelow (α := αᵒᵈ) hs

中文:
定理 IsCompact.bddAbove
  条件: [ClosedIciTopology α] [Nonempty α] {s : Set α} (hs : IsCompact s)
  证明: IsCompact.bddBelow (α := αᵒᵈ) hs

Depends on / 依赖: IsCompact, IsCompact.bddBelow, bddBelow
-/
theorem IsCompact.bddAbove [ClosedIciTopology α] [Nonempty α] {s : Set α} (hs : IsCompact s) :
    BddAbove s :=
  IsCompact.bddBelow (α := αᵒᵈ) hs

/--
theorem `IsCompact.bddBelow_image` / 定理 `IsCompact.bddBelow_image`

English:
theorem IsCompact.bddBelow_image
  statement: [ClosedIicTopology α] [Nonempty α] {f : β -> α} {K : Set β}
  proof: (hK.image_of_continuousOn hf).bddBelow

中文:
定理 IsCompact.bddBelow_image
  结论: [ClosedIicTopology α] [Nonempty α] {f : β -> α} {K : Set β}
  证明: (hK.image_of_continuousOn hf).bddBelow

Depends on / 依赖: bddBelow, hK.image_of_continuousOn, image_of_continuousOn
-/
theorem IsCompact.bddBelow_image [ClosedIicTopology α] [Nonempty α] {f : β -> α} {K : Set β}
    (hK : IsCompact K) (hf : ContinuousOn f K) : BddBelow (f '' K) :=
  (hK.image_of_continuousOn hf).bddBelow

/--
theorem `IsCompact.bddAbove_image` / 定理 `IsCompact.bddAbove_image`

English:
theorem IsCompact.bddAbove_image
  statement: [ClosedIciTopology α] [Nonempty α] {f : β -> α} {K : Set β}
  proof: IsCompact.bddBelow_image (α := αᵒᵈ) hK hf

中文:
定理 IsCompact.bddAbove_image
  结论: [ClosedIciTopology α] [Nonempty α] {f : β -> α} {K : Set β}
  证明: IsCompact.bddBelow_image (α := αᵒᵈ) hK hf

Depends on / 依赖: IsCompact, IsCompact.bddBelow_image, bddBelow_image
-/
theorem IsCompact.bddAbove_image [ClosedIciTopology α] [Nonempty α] {f : β -> α} {K : Set β}
    (hK : IsCompact K) (hf : ContinuousOn f K) : BddAbove (f '' K) :=
  IsCompact.bddBelow_image (α := αᵒᵈ) hK hf

/-- A continuous function with compact support is bounded below. -/
@[to_additive /-- A continuous function with compact support is bounded below. -/]
/--
theorem `Continuous.bddBelow_range_of_hasCompactMulSupport` / 定理 `Continuous.bddBelow_range_of_hasCompactMulSupport`

English:
theorem Continuous.bddBelow_range_of_hasCompactMulSupport
  statement: [ClosedIicTopology α] [One α]
  proof: (h.isCompact_range hf).bddBelow

中文:
定理 Continuous.bddBelow_range_of_hasCompactMulSupport
  结论: [ClosedIicTopology α] [One α]
  证明: (h.isCompact_range hf).bddBelow

Depends on / 依赖: bddBelow, h.isCompact_range, isCompact_range
-/
theorem Continuous.bddBelow_range_of_hasCompactMulSupport [ClosedIicTopology α] [One α]
    {f : β -> α} (hf : Continuous f) (h : HasCompactMulSupport f) : BddBelow (range f) :=
  (h.isCompact_range hf).bddBelow

/-- A continuous function with compact support is bounded above. -/
@[to_additive /-- A continuous function with compact support is bounded above. -/]
/--
theorem `Continuous.bddAbove_range_of_hasCompactMulSupport` / 定理 `Continuous.bddAbove_range_of_hasCompactMulSupport`

English:
theorem Continuous.bddAbove_range_of_hasCompactMulSupport
  statement: [ClosedIciTopology α] [One α]
  proof: Continuous.bddBelow_range_of_hasCompactMulSupport (α := αᵒᵈ) hf h

中文:
定理 Continuous.bddAbove_range_of_hasCompactMulSupport
  结论: [ClosedIciTopology α] [One α]
  证明: Continuous.bddBelow_range_of_hasCompactMulSupport (α := αᵒᵈ) hf h

Depends on / 依赖: Continuous, Continuous.bddBelow_range_of_hasCompactMulSupport, bddBelow_range_of_hasCompactMulSupport
-/
theorem Continuous.bddAbove_range_of_hasCompactMulSupport [ClosedIciTopology α] [One α]
    {f : β -> α} (hf : Continuous f) (h : HasCompactMulSupport f) : BddAbove (range f) :=
  Continuous.bddBelow_range_of_hasCompactMulSupport (α := αᵒᵈ) hf h

end LinearOrder

section ConditionallyCompleteLinearOrder

variable {α β γ : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
  [TopologicalSpace β] [TopologicalSpace γ]

/--
theorem `IsCompact.sSup_lt_iff_of_continuous` / 定理 `IsCompact.sSup_lt_iff_of_continuous`

English:
theorem IsCompact.sSup_lt_iff_of_continuous
  statement: [ClosedIciTopology α] {f : β -> α} {K : Set β}
  proof: by
  refine ⟨fun h x hx => (le_csSup (hK.bddAbove_image hf) <| mem_image_of_mem f hx).trans_lt h,
    fun h => ?_⟩
  obtain ⟨x, hx, h2x⟩ := hK.exists_isMaxOn h0K hf
  refine (csSup_le (h0K.image f) ?_).trans_lt (h x hx)
  rintro _ ⟨x', hx', rfl⟩; exact h2x hx'

中文:
定理 IsCompact.sSup_lt_iff_of_continuous
  结论: [ClosedIciTopology α] {f : β -> α} {K : Set β}
  证明: by
  refine ⟨fun h x hx => (le_csSup (hK.bddAbove_image hf) <| mem_image_of_mem f hx).trans_lt h,
    fun h => ?_⟩
  obtain ⟨x, hx, h2x⟩ := hK.exists_isMaxOn h0K hf
  refine (csSup_le (h0K.image f) ?_).trans_lt (h x hx)
  rintro _ ⟨x', hx', rfl⟩; exact h2x hx'

Depends on / 依赖: bddAbove_image, csSup_le, exists_isMaxOn, h0K.image, hK.bddAbove_image, hK.exists_isMaxOn, le_csSup, mem_image_of_mem, trans_lt
-/
theorem IsCompact.sSup_lt_iff_of_continuous [ClosedIciTopology α] {f : β -> α} {K : Set β}
    (hK : IsCompact K) (h0K : K.Nonempty) (hf : ContinuousOn f K) (y : α) :
    sSup (f '' K) < y ↔ forall x in K, f x < y := by
  refine ⟨fun h x hx => (le_csSup (hK.bddAbove_image hf) <| mem_image_of_mem f hx).trans_lt h,
    fun h => ?_⟩
  obtain ⟨x, hx, h2x⟩ := hK.exists_isMaxOn h0K hf
  refine (csSup_le (h0K.image f) ?_).trans_lt (h x hx)
  rintro _ ⟨x', hx', rfl⟩; exact h2x hx'

/--
theorem `IsCompact.lt_sInf_iff_of_continuous` / 定理 `IsCompact.lt_sInf_iff_of_continuous`

English:
theorem IsCompact.lt_sInf_iff_of_continuous
  statement: [ClosedIicTopology α] {f : β -> α} {K : Set β}
  proof: IsCompact.sSup_lt_iff_of_continuous (α := αᵒᵈ) hK h0K hf y

中文:
定理 IsCompact.lt_sInf_iff_of_continuous
  结论: [ClosedIicTopology α] {f : β -> α} {K : Set β}
  证明: IsCompact.sSup_lt_iff_of_continuous (α := αᵒᵈ) hK h0K hf y

Depends on / 依赖: IsCompact, IsCompact.sSup_lt_iff_of_continuous, sSup_lt_iff_of_continuous
-/
theorem IsCompact.lt_sInf_iff_of_continuous [ClosedIicTopology α] {f : β -> α} {K : Set β}
    (hK : IsCompact K) (h0K : K.Nonempty) (hf : ContinuousOn f K) (y : α) :
    y < sInf (f '' K) ↔ forall x in K, y < f x :=
  IsCompact.sSup_lt_iff_of_continuous (α := αᵒᵈ) hK h0K hf y

end ConditionallyCompleteLinearOrder

/-!
### Min and max elements of a compact set
-/

section InfSup

variable {α β : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
  [TopologicalSpace β]

/--
theorem `IsCompact.sInf_mem` / 定理 `IsCompact.sInf_mem`

English:
theorem IsCompact.sInf_mem
  statement: [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
  proof: let ⟨_a, ha⟩ := hs.exists_isLeast ne_s
  ha.csInf_mem

中文:
定理 IsCompact.sInf_mem
  结论: [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
  证明: let ⟨_a, ha⟩ := hs.exists_isLeast ne_s
  ha.csInf_mem

Depends on / 依赖: csInf_mem, exists_isLeast, ha.csInf_mem, hs.exists_isLeast, ne_s
-/
theorem IsCompact.sInf_mem [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : sInf s in s :=
  let ⟨_a, ha⟩ := hs.exists_isLeast ne_s
  ha.csInf_mem

/--
theorem `IsCompact.sSup_mem` / 定理 `IsCompact.sSup_mem`

English:
theorem IsCompact.sSup_mem
  statement: [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
  proof: IsCompact.sInf_mem (α := αᵒᵈ) hs ne_s

中文:
定理 IsCompact.sSup_mem
  结论: [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
  证明: IsCompact.sInf_mem (α := αᵒᵈ) hs ne_s

Depends on / 依赖: IsCompact, IsCompact.sInf_mem, ne_s, sInf_mem
-/
theorem IsCompact.sSup_mem [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : sSup s in s :=
  IsCompact.sInf_mem (α := αᵒᵈ) hs ne_s

/--
theorem `IsCompact.isGLB_sInf` / 定理 `IsCompact.isGLB_sInf`

English:
theorem IsCompact.isGLB_sInf
  statement: [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
  proof: isGLB_csInf ne_s hs.bddBelow

中文:
定理 IsCompact.isGLB_sInf
  结论: [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
  证明: isGLB_csInf ne_s hs.bddBelow

Depends on / 依赖: bddBelow, hs.bddBelow, isGLB_csInf, ne_s
-/
theorem IsCompact.isGLB_sInf [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : IsGLB s (sInf s) :=
  isGLB_csInf ne_s hs.bddBelow

/--
theorem `IsCompact.isLUB_sSup` / 定理 `IsCompact.isLUB_sSup`

English:
theorem IsCompact.isLUB_sSup
  statement: [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
  proof: IsCompact.isGLB_sInf (α := αᵒᵈ) hs ne_s

中文:
定理 IsCompact.isLUB_sSup
  结论: [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
  证明: IsCompact.isGLB_sInf (α := αᵒᵈ) hs ne_s

Depends on / 依赖: IsCompact, IsCompact.isGLB_sInf, isGLB_sInf, ne_s
-/
theorem IsCompact.isLUB_sSup [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : IsLUB s (sSup s) :=
  IsCompact.isGLB_sInf (α := αᵒᵈ) hs ne_s

/--
theorem `IsCompact.isLeast_sInf` / 定理 `IsCompact.isLeast_sInf`

English:
theorem IsCompact.isLeast_sInf
  statement: [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
  proof: ⟨hs.sInf_mem ne_s, (hs.isGLB_sInf ne_s).1⟩

中文:
定理 IsCompact.isLeast_sInf
  结论: [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
  证明: ⟨hs.sInf_mem ne_s, (hs.isGLB_sInf ne_s).1⟩

Depends on / 依赖: hs.isGLB_sInf, hs.sInf_mem, isGLB_sInf, ne_s, sInf_mem
-/
theorem IsCompact.isLeast_sInf [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : IsLeast s (sInf s) :=
  ⟨hs.sInf_mem ne_s, (hs.isGLB_sInf ne_s).1⟩

/--
theorem `IsCompact.isGreatest_sSup` / 定理 `IsCompact.isGreatest_sSup`

English:
theorem IsCompact.isGreatest_sSup
  statement: [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
  proof: IsCompact.isLeast_sInf (α := αᵒᵈ) hs ne_s

中文:
定理 IsCompact.isGreatest_sSup
  结论: [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
  证明: IsCompact.isLeast_sInf (α := αᵒᵈ) hs ne_s

Depends on / 依赖: IsCompact, IsCompact.isLeast_sInf, isLeast_sInf, ne_s
-/
theorem IsCompact.isGreatest_sSup [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : IsGreatest s (sSup s) :=
  IsCompact.isLeast_sInf (α := αᵒᵈ) hs ne_s

/--
theorem `IsCompact.exists_sInf_image_eq_and_le` / 定理 `IsCompact.exists_sInf_image_eq_and_le`

English:
theorem IsCompact.exists_sInf_image_eq_and_le
  statement: [ClosedIicTopology α] {s : Set β}
  proof: let ⟨x, hxs, hx⟩ := (hs.image_of_continuousOn hf).sInf_mem (ne_s.image f)
  ⟨x, hxs, hx.symm, fun _y hy =>
hx.trans_le csInf_le (hs.image_of_continuousOn hf).bddBelow mem_image_of_mem f hy⟩

中文:
定理 IsCompact.exists_sInf_image_eq_and_le
  结论: [ClosedIicTopology α] {s : Set β}
  证明: let ⟨x, hxs, hx⟩ := (hs.image_of_continuousOn hf).sInf_mem (ne_s.image f)
  ⟨x, hxs, hx.symm, fun _y hy =>
hx.trans_le csInf_le (hs.image_of_continuousOn hf).bddBelow mem_image_of_mem f hy⟩

Depends on / 依赖: bddBelow, csInf_le, hs.image_of_continuousOn, hx.symm, hx.trans_le, image_of_continuousOn, mem_image_of_mem, ne_s, ne_s.image, sInf_mem, trans_le
-/
theorem IsCompact.exists_sInf_image_eq_and_le [ClosedIicTopology α] {s : Set β}
    (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : ContinuousOn f s) :
    exists x in s, sInf (f '' s) = f x ∧ forall y in s, f x <= f y :=
  let ⟨x, hxs, hx⟩ := (hs.image_of_continuousOn hf).sInf_mem (ne_s.image f)
  ⟨x, hxs, hx.symm, fun _y hy =>
hx.trans_le csInf_le (hs.image_of_continuousOn hf).bddBelow mem_image_of_mem f hy⟩

/--
theorem `IsCompact.exists_sSup_image_eq_and_ge` / 定理 `IsCompact.exists_sSup_image_eq_and_ge`

English:
theorem IsCompact.exists_sSup_image_eq_and_ge
  statement: [ClosedIciTopology α] {s : Set β}
  proof: IsCompact.exists_sInf_image_eq_and_le (α := αᵒᵈ) hs ne_s hf

中文:
定理 IsCompact.exists_sSup_image_eq_and_ge
  结论: [ClosedIciTopology α] {s : Set β}
  证明: IsCompact.exists_sInf_image_eq_and_le (α := αᵒᵈ) hs ne_s hf

Depends on / 依赖: IsCompact, IsCompact.exists_sInf_image_eq_and_le, exists_sInf_image_eq_and_le, ne_s
-/
theorem IsCompact.exists_sSup_image_eq_and_ge [ClosedIciTopology α] {s : Set β}
    (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : ContinuousOn f s) :
    exists x in s, sSup (f '' s) = f x ∧ forall y in s, f y <= f x :=
  IsCompact.exists_sInf_image_eq_and_le (α := αᵒᵈ) hs ne_s hf

/--
theorem `IsCompact.exists_sInf_image_eq` / 定理 `IsCompact.exists_sInf_image_eq`

English:
theorem IsCompact.exists_sInf_image_eq
  statement: [ClosedIicTopology α] {s : Set β} (hs : IsCompact s)
  proof: let ⟨x, hxs, hx, _⟩ := hs.exists_sInf_image_eq_and_le ne_s hf
  ⟨x, hxs, hx⟩

中文:
定理 IsCompact.exists_sInf_image_eq
  结论: [ClosedIicTopology α] {s : Set β} (hs : IsCompact s)
  证明: let ⟨x, hxs, hx, _⟩ := hs.exists_sInf_image_eq_and_le ne_s hf
  ⟨x, hxs, hx⟩

Depends on / 依赖: exists_sInf_image_eq_and_le, hs.exists_sInf_image_eq_and_le, ne_s
-/
theorem IsCompact.exists_sInf_image_eq [ClosedIicTopology α] {s : Set β} (hs : IsCompact s)
    (ne_s : s.Nonempty) {f : β -> α} (hf : ContinuousOn f s) : exists x in s, sInf (f '' s) = f x :=
  let ⟨x, hxs, hx, _⟩ := hs.exists_sInf_image_eq_and_le ne_s hf
  ⟨x, hxs, hx⟩

/--
theorem `IsCompact.exists_sSup_image_eq` / 定理 `IsCompact.exists_sSup_image_eq`

English:
theorem IsCompact.exists_sSup_image_eq
  statement: [ClosedIciTopology α] {s : Set β} (hs : IsCompact s)
  proof: IsCompact.exists_sInf_image_eq (α := αᵒᵈ) hs ne_s

中文:
定理 IsCompact.exists_sSup_image_eq
  结论: [ClosedIciTopology α] {s : Set β} (hs : IsCompact s)
  证明: IsCompact.exists_sInf_image_eq (α := αᵒᵈ) hs ne_s

Depends on / 依赖: IsCompact, IsCompact.exists_sInf_image_eq, exists_sInf_image_eq, ne_s
-/
theorem IsCompact.exists_sSup_image_eq [ClosedIciTopology α] {s : Set β} (hs : IsCompact s)
    (ne_s : s.Nonempty) : forall {f : β -> α}, ContinuousOn f s -> exists x in s, sSup (f '' s) = f x :=
  IsCompact.exists_sInf_image_eq (α := αᵒᵈ) hs ne_s

end InfSup

section ExistsExtr

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [TopologicalSpace β]

/--
theorem `IsCompact.exists_isMinOn_mem_subset` / 定理 `IsCompact.exists_isMinOn_mem_subset`

English:
theorem IsCompact.exists_isMinOn_mem_subset
  statement: [ClosedIicTopology α] {f : β -> α} {s t : Set β}
  proof: let ⟨x, hxt, hfx⟩ := ht.exists_isMinOn ⟨z, hz⟩ hf
  ⟨x, by_contra fun hxs => (hfz x ⟨hxt, hxs⟩).not_ge (hfx hz), hfx⟩

中文:
定理 IsCompact.exists_isMinOn_mem_subset
  结论: [ClosedIicTopology α] {f : β -> α} {s t : Set β}
  证明: let ⟨x, hxt, hfx⟩ := ht.exists_isMinOn ⟨z, hz⟩ hf
  ⟨x, by_contra fun hxs => (hfz x ⟨hxt, hxs⟩).not_ge (hfx hz), hfx⟩

Depends on / 依赖: exists_isMinOn, ht.exists_isMinOn, not_ge
-/
theorem IsCompact.exists_isMinOn_mem_subset [ClosedIicTopology α] {f : β -> α} {s t : Set β}
    {z : β} (ht : IsCompact t) (hf : ContinuousOn f t) (hz : z in t)
    (hfz : forall z' in t \ s, f z < f z') : exists x in s, IsMinOn f t x :=
  let ⟨x, hxt, hfx⟩ := ht.exists_isMinOn ⟨z, hz⟩ hf
  ⟨x, by_contra fun hxs => (hfz x ⟨hxt, hxs⟩).not_ge (hfx hz), hfx⟩

/--
theorem `IsCompact.exists_isMaxOn_mem_subset` / 定理 `IsCompact.exists_isMaxOn_mem_subset`

English:
theorem IsCompact.exists_isMaxOn_mem_subset
  statement: [ClosedIciTopology α] {f : β -> α} {s t : Set β}
  proof: let ⟨x, hxt, hfx⟩ := ht.exists_isMaxOn ⟨z, hz⟩ hf
  ⟨x, by_contra fun hxs => (hfz x ⟨hxt, hxs⟩).not_ge (hfx hz), hfx⟩

中文:
定理 IsCompact.exists_isMaxOn_mem_subset
  结论: [ClosedIciTopology α] {f : β -> α} {s t : Set β}
  证明: let ⟨x, hxt, hfx⟩ := ht.exists_isMaxOn ⟨z, hz⟩ hf
  ⟨x, by_contra fun hxs => (hfz x ⟨hxt, hxs⟩).not_ge (hfx hz), hfx⟩

Depends on / 依赖: exists_isMaxOn, ht.exists_isMaxOn, not_ge
-/
theorem IsCompact.exists_isMaxOn_mem_subset [ClosedIciTopology α] {f : β -> α} {s t : Set β}
    {z : β} (ht : IsCompact t) (hf : ContinuousOn f t) (hz : z in t)
    (hfz : forall z' in t \ s, f z' < f z) : exists x in s, IsMaxOn f t x :=
  let ⟨x, hxt, hfx⟩ := ht.exists_isMaxOn ⟨z, hz⟩ hf
  ⟨x, by_contra fun hxs => (hfz x ⟨hxt, hxs⟩).not_ge (hfx hz), hfx⟩

-- TODO: we could assume `t ∈ 𝓝ˢ s` (a.k.a. `s ⊆ interior t`) instead of `s ⊆ t` and `IsOpen s`.
/--
theorem `IsCompact.exists_isLocalMin_mem_open` / 定理 `IsCompact.exists_isLocalMin_mem_open`

English:
theorem IsCompact.exists_isLocalMin_mem_open
  statement: [ClosedIicTopology α] {f : β -> α} {s t : Set β}
  proof: let ⟨x, hxs, h⟩ := ht.exists_isMinOn_mem_subset hf hz hfz
⟨x, hxs, h.isLocalMin mem_nhds_iff.2 ⟨s, hst, hs, hxs⟩⟩

中文:
定理 IsCompact.exists_isLocalMin_mem_open
  结论: [ClosedIicTopology α] {f : β -> α} {s t : Set β}
  证明: let ⟨x, hxs, h⟩ := ht.exists_isMinOn_mem_subset hf hz hfz
⟨x, hxs, h.isLocalMin mem_nhds_iff.2 ⟨s, hst, hs, hxs⟩⟩

Depends on / 依赖: exists_isMinOn_mem_subset, h.isLocalMin, ht.exists_isMinOn_mem_subset, isLocalMin, mem_nhds_iff
-/
theorem IsCompact.exists_isLocalMin_mem_open [ClosedIicTopology α] {f : β -> α} {s t : Set β}
    {z : β} (ht : IsCompact t) (hst : s subseteq t) (hf : ContinuousOn f t) (hz : z in t)
    (hfz : forall z' in t \ s, f z < f z') (hs : IsOpen s) : exists x in s, IsLocalMin f x :=
  let ⟨x, hxs, h⟩ := ht.exists_isMinOn_mem_subset hf hz hfz
⟨x, hxs, h.isLocalMin mem_nhds_iff.2 ⟨s, hst, hs, hxs⟩⟩

/--
theorem `IsCompact.exists_isLocalMax_mem_open` / 定理 `IsCompact.exists_isLocalMax_mem_open`

English:
theorem IsCompact.exists_isLocalMax_mem_open
  statement: [ClosedIciTopology α] {f : β -> α} {s t : Set β}
  proof: let ⟨x, hxs, h⟩ := ht.exists_isMaxOn_mem_subset hf hz hfz
⟨x, hxs, h.isLocalMax mem_nhds_iff.2 ⟨s, hst, hs, hxs⟩⟩

中文:
定理 IsCompact.exists_isLocalMax_mem_open
  结论: [ClosedIciTopology α] {f : β -> α} {s t : Set β}
  证明: let ⟨x, hxs, h⟩ := ht.exists_isMaxOn_mem_subset hf hz hfz
⟨x, hxs, h.isLocalMax mem_nhds_iff.2 ⟨s, hst, hs, hxs⟩⟩

Depends on / 依赖: exists_isMaxOn_mem_subset, h.isLocalMax, ht.exists_isMaxOn_mem_subset, isLocalMax, mem_nhds_iff
-/
theorem IsCompact.exists_isLocalMax_mem_open [ClosedIciTopology α] {f : β -> α} {s t : Set β}
    {z : β} (ht : IsCompact t) (hst : s subseteq t) (hf : ContinuousOn f t) (hz : z in t)
    (hfz : forall z' in t \ s, f z' < f z) (hs : IsOpen s) : exists x in s, IsLocalMax f x :=
  let ⟨x, hxs, h⟩ := ht.exists_isMaxOn_mem_subset hf hz hfz
⟨x, hxs, h.isLocalMax mem_nhds_iff.2 ⟨s, hst, hs, hxs⟩⟩

end ExistsExtr

variable {α β γ : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
  [OrderTopology α] [TopologicalSpace β] [TopologicalSpace γ]

/--
theorem `eq_Icc_of_connected_compact` / 定理 `eq_Icc_of_connected_compact`

English:
theorem eq_Icc_of_connected_compact
  given: {s : Set α} (h₁ : IsConnected s) (h₂ : IsCompact s)
  proof: eq_Icc_csInf_csSup_of_connected_bdd_closed h₁ h₂.bddBelow h₂.bddAbove h₂.isClosed

中文:
定理 eq_Icc_of_connected_compact
  条件: {s : Set α} (h₁ : IsConnected s) (h₂ : IsCompact s)
  证明: eq_Icc_csInf_csSup_of_connected_bdd_closed h₁ h₂.bddBelow h₂.bddAbove h₂.isClosed

Depends on / 依赖: bddAbove, bddBelow, eq_Icc_csInf_csSup_of_connected_bdd_closed, isClosed
-/
theorem eq_Icc_of_connected_compact {s : Set α} (h₁ : IsConnected s) (h₂ : IsCompact s) :
    s = Icc (sInf s) (sSup s) :=
  eq_Icc_csInf_csSup_of_connected_bdd_closed h₁ h₂.bddBelow h₂.bddAbove h₂.isClosed

/-- If `f : γ → β → α` is a function that is continuous as a function on `γ × β`, `α` is a
conditionally complete linear order, and `K : Set β` is a compact set, then
`fun x ↦ sSup (f x '' K)` is a continuous function. -/
/--
theorem `IsCompact.continuous_sSup` / 定理 `IsCompact.continuous_sSup`

English:
theorem IsCompact.continuous_sSup
  statement: {f : γ -> β -> α} {K : Set β} (hK : IsCompact K)
  proof: by
  rcases eq_empty_or_nonempty K with (rfl | h0K)
  · simp_rw [image_empty]
    exact continuous_const
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨y, hyK, h2y, hy⟩ :=
    hK.exists_sSup_image_eq_and_ge h0K
      (show Continuous (f x) from hf.comp <| .prodMk_right x).continuousOn
  rw [

中文:
定理 IsCompact.continuous_sSup
  结论: {f : γ -> β -> α} {K : Set β} (hK : IsCompact K)
  证明: by
  rcases eq_empty_or_nonempty K with (rfl | h0K)
  · simp_rw [image_empty]
    exact continuous_const
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨y, hyK, h2y, hy⟩ :=
    hK.exists_sSup_image_eq_and_ge h0K
      (show Continuous (f x) from hf.comp <| .prodMk_right x).continuousOn
  rw [

Depends on / 依赖: Continuous, ContinuousAt, continuousOn, continuous_const, continuous_iff_continuousAt, eq_empty_or_nonempty, exists_sSup_image_eq_and_ge, hK.exists_sSup_image_eq_and_ge, hf.comp, image_empty, prodMk_left, prodMk_right, simp_rw, tendsto, tendsto_order, tendsto_order.mp
-/
theorem IsCompact.continuous_sSup {f : γ -> β -> α} {K : Set β} (hK : IsCompact K)
    (hf : Continuous ↿f) : Continuous fun x => sSup (f x '' K) := by
  rcases eq_empty_or_nonempty K with (rfl | h0K)
  · simp_rw [image_empty]
    exact continuous_const
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨y, hyK, h2y, hy⟩ :=
    hK.exists_sSup_image_eq_and_ge h0K
      (show Continuous (f x) from hf.comp <| .prodMk_right x).continuousOn
  rw [ContinuousAt]; rw [h2y]; rw [tendsto_order]
  have := tendsto_order.mp ((show Continuous fun x => f x y
from hf.comp .prodMk_left _).tendsto x)
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · refine (this.1 z hz).mono fun x' hx' =>
hx'.trans_le le_csSup ?_ mem_image_of_mem (f x') hyK
    exact hK.bddAbove_image (hf.comp <| .prodMk_right x').continuousOn
  · have h : ({x} : Set γ) ×ˢ K subseteq ↿f ⁻¹' Iio z := by
      rintro ⟨x', y'⟩ ⟨(rfl : x' = x), hy'⟩
      exact (hy y' hy').trans_lt hz
    obtain ⟨u, v, hu, _, hxu, hKv, huv⟩ :=
      generalized_tube_lemma isCompact_singleton hK (isOpen_Iio.preimage hf) h
    refine eventually_of_mem (hu.mem_nhds (singleton_subset_iff.mp hxu)) fun x' hx' => ?_
    rw [hK.sSup_lt_iff_of_continuous h0K
        (show Continuous (f x') from hf.comp <| .prodMk_right x').continuousOn]
    exact fun y' hy' => huv (mk_mem_prod hx' (hKv hy'))

/--
theorem `IsCompact.continuous_sInf` / 定理 `IsCompact.continuous_sInf`

English:
theorem IsCompact.continuous_sInf
  statement: {f : γ -> β -> α} {K : Set β} (hK : IsCompact K)
  proof: IsCompact.continuous_sSup (α := αᵒᵈ) hK hf

中文:
定理 IsCompact.continuous_sInf
  结论: {f : γ -> β -> α} {K : Set β} (hK : IsCompact K)
  证明: IsCompact.continuous_sSup (α := αᵒᵈ) hK hf

Depends on / 依赖: IsCompact, IsCompact.continuous_sSup, continuous_sSup
-/
theorem IsCompact.continuous_sInf {f : γ -> β -> α} {K : Set β} (hK : IsCompact K)
    (hf : Continuous ↿f) : Continuous fun x => sInf (f x '' K) :=
  IsCompact.continuous_sSup (α := αᵒᵈ) hK hf

namespace ContinuousOn

/-!
### Image of a closed interval
-/

variable [DenselyOrdered α] [ConditionallyCompleteLinearOrder β] [OrderTopology β] {f : α -> β}
  {a b c : α}

open scoped Interval

/--
theorem `image_Icc` / 定理 `image_Icc`

English:
theorem image_Icc
  given: (hab : a <= b) (h : ContinuousOn f <| Icc a b)
  proof: eq_Icc_of_connected_compact ⟨(nonempty_Icc.2 hab).image f, isPreconnected_Icc.image f h⟩
    (isCompact_Icc.image_of_continuousOn h)

中文:
定理 image_Icc
  条件: (hab : a <= b) (h : ContinuousOn f <| Icc a b)
  证明: eq_Icc_of_connected_compact ⟨(nonempty_Icc.2 hab).image f, isPreconnected_Icc.image f h⟩
    (isCompact_Icc.image_of_continuousOn h)

Depends on / 依赖: eq_Icc_of_connected_compact, image_of_continuousOn, isCompact_Icc, isCompact_Icc.image_of_continuousOn, isPreconnected_Icc, isPreconnected_Icc.image, nonempty_Icc
-/
theorem image_Icc (hab : a <= b) (h : ContinuousOn f <| Icc a b) :
    f '' Icc a b = Icc (sInf <| f '' Icc a b) (sSup <| f '' Icc a b) :=
  eq_Icc_of_connected_compact ⟨(nonempty_Icc.2 hab).image f, isPreconnected_Icc.image f h⟩
    (isCompact_Icc.image_of_continuousOn h)

/--
theorem `image_uIcc_eq_Icc` / 定理 `image_uIcc_eq_Icc`

English:
theorem image_uIcc_eq_Icc
  given: (h : ContinuousOn f [[a, b]])
  proof: image_Icc min_le_max h

中文:
定理 image_uIcc_eq_Icc
  条件: (h : ContinuousOn f [[a, b]])
  证明: image_Icc min_le_max h

Depends on / 依赖: image_Icc, min_le_max
-/
theorem image_uIcc_eq_Icc (h : ContinuousOn f [[a, b]]) :
    f '' [[a, b]] = Icc (sInf (f '' [[a, b]])) (sSup (f '' [[a, b]])) :=
  image_Icc min_le_max h

/--
theorem `image_uIcc` / 定理 `image_uIcc`

English:
theorem image_uIcc
  given: (h : ContinuousOn f <| [[a, b]])
  proof: by
  refine h.image_uIcc_eq_Icc.trans (uIcc_of_le ?_).symm
  refine csInf_le_csSup (nonempty_uIcc.image _) ?_ ?_ <;> rw [h.image_uIcc_eq_Icc]
  exacts [bddBelow_Icc, bddAbove_Icc]

中文:
定理 image_uIcc
  条件: (h : ContinuousOn f <| [[a, b]])
  证明: by
  refine h.image_uIcc_eq_Icc.trans (uIcc_of_le ?_).symm
  refine csInf_le_csSup (nonempty_uIcc.image _) ?_ ?_ <;> rw [h.image_uIcc_eq_Icc]
  exacts [bddBelow_Icc, bddAbove_Icc]

Depends on / 依赖: bddAbove_Icc, bddBelow_Icc, csInf_le_csSup, exacts, h.image_uIcc_eq_Icc, h.image_uIcc_eq_Icc.trans, image_uIcc_eq_Icc, nonempty_uIcc, nonempty_uIcc.image, uIcc_of_le
-/
theorem image_uIcc (h : ContinuousOn f <| [[a, b]]) :
    f '' [[a, b]] = [[sInf (f '' [[a, b]]), sSup (f '' [[a, b]])]] := by
  refine h.image_uIcc_eq_Icc.trans (uIcc_of_le ?_).symm
  refine csInf_le_csSup (nonempty_uIcc.image _) ?_ ?_ <;> rw [h.image_uIcc_eq_Icc]
  exacts [bddBelow_Icc, bddAbove_Icc]

/--
theorem `sInf_image_Icc_le` / 定理 `sInf_image_Icc_le`

English:
theorem sInf_image_Icc_le
  given: (h : ContinuousOn f <| Icc a b) (hc : c in Icc a b)
  proof: by
  have := mem_image_of_mem f hc
  rw [h.image_Icc (hc.1.trans hc.2)] at this
  exact this.1

中文:
定理 sInf_image_Icc_le
  条件: (h : ContinuousOn f <| Icc a b) (hc : c in Icc a b)
  证明: by
  have := mem_image_of_mem f hc
  rw [h.image_Icc (hc.1.trans hc.2)] at this
  exact this.1

Depends on / 依赖: h.image_Icc, image_Icc, mem_image_of_mem
-/
theorem sInf_image_Icc_le (h : ContinuousOn f <| Icc a b) (hc : c in Icc a b) :
    sInf (f '' Icc a b) <= f c := by
  have := mem_image_of_mem f hc
  rw [h.image_Icc (hc.1.trans hc.2)] at this
  exact this.1

/--
theorem `le_sSup_image_Icc` / 定理 `le_sSup_image_Icc`

English:
theorem le_sSup_image_Icc
  given: (h : ContinuousOn f <| Icc a b) (hc : c in Icc a b)
  proof: by
  have := mem_image_of_mem f hc
  rw [h.image_Icc (hc.1.trans hc.2)] at this
  exact this.2

中文:
定理 le_sSup_image_Icc
  条件: (h : ContinuousOn f <| Icc a b) (hc : c in Icc a b)
  证明: by
  have := mem_image_of_mem f hc
  rw [h.image_Icc (hc.1.trans hc.2)] at this
  exact this.2

Depends on / 依赖: h.image_Icc, image_Icc, mem_image_of_mem
-/
theorem le_sSup_image_Icc (h : ContinuousOn f <| Icc a b) (hc : c in Icc a b) :
    f c <= sSup (f '' Icc a b) := by
  have := mem_image_of_mem f hc
  rw [h.image_Icc (hc.1.trans hc.2)] at this
  exact this.2

end ContinuousOn
