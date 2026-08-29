/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Order.OrderClosed

/-!
# Exposed sets

This file defines exposed sets and exposed points for sets in a real vector space.

An exposed subset of `A` is a subset of `A` that is the set of all maximal points of a functional
(a continuous linear map `E → 𝕜`) over `A`. By convention, `∅` is an exposed subset of all sets.
This allows for better functoriality of the definition (the intersection of two exposed subsets is
exposed, faces of a polytope form a bounded lattice).
This is an analytic notion of "being on the side of". It is stronger than being extreme (see
`IsExposed.isExtreme`), but weaker (for exposed points) than being a vertex.

An exposed set of `A` is sometimes called a "face of `A`", but we decided to reserve this
terminology to the more specific notion of a face of a polytope (sometimes hopefully soon out
on mathlib!).

## Main declarations

* `IsExposed 𝕜 A B`: States that `B` is an exposed set of `A` (in the literature, `A` is often
  implicit).
* `IsExposed.isExtreme`: An exposed set is also extreme.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

## TODO

Prove lemmas relating exposed sets and points to the intrinsic frontier.
-/

@[expose] public section

open Affine Set

section PreorderSemiring

variable (𝕜 : Type*) {E : Type*} [TopologicalSpace 𝕜] [Semiring 𝕜] [Preorder 𝕜] [AddCommMonoid E]
  [TopologicalSpace E] [Module 𝕜 E] {A B : Set E}

/--
Definition of `IsExposed` / `IsExposed` 的定义

English:
definition IsExposed
  signature: (A B : Set E)
  body: B.Nonempty -> exists l : StrongDual 𝕜 E, B = { x in A | forall y in A, l y <= l x }

中文:
定义 IsExposed
  签名: (A B : 集合 E)
  定义体: B.Nonempty -> exists l : StrongDual 𝕜 E, B = { x in A | forall y in A, l y <= l x }

Depends on / 依赖: B.Nonempty, Nonempty, StrongDual
-/
def IsExposed (A B : Set E) : Prop :=
  B.Nonempty -> exists l : StrongDual 𝕜 E, B = { x in A | forall y in A, l y <= l x }

end PreorderSemiring

section OrderedRing

variable {𝕜 : Type*} {E : Type*} [TopologicalSpace 𝕜] [Ring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
  [TopologicalSpace E] [Module 𝕜 E] {l : StrongDual 𝕜 E} {A B C : Set E} {x : E}

/--
Definition of `ContinuousLinearMap.toExposed` / `ContinuousLinearMap.toExposed` 的定义

English:
definition ContinuousLinearMap.toExposed
  signature: (l : StrongDual 𝕜 E) (A : Set E)
  body: { x in A | forall y in A, l y <= l x }

中文:
定义 连续线性映射.toExposed
  签名: (l : StrongDual 𝕜 E) (A : 集合 E)
  定义体: { x in A | forall y in A, l y <= l x }
-/
def ContinuousLinearMap.toExposed (l : StrongDual 𝕜 E) (A : Set E) : Set E :=
  { x in A | forall y in A, l y <= l x }

/--
theorem `ContinuousLinearMap.toExposed.isExposed` / 定理 `ContinuousLinearMap.toExposed.isExposed`

English:
theorem ContinuousLinearMap.toExposed.isExposed
  statement: IsExposed 𝕜 A (l.toExposed A)
  proof: fun _ => ⟨l, rfl⟩

中文:
定理 连续线性映射.toExposed.isExposed
  结论: IsExposed 𝕜 A (l.toExposed A)
  证明: fun _ => ⟨l, rfl⟩
-/
theorem ContinuousLinearMap.toExposed.isExposed : IsExposed 𝕜 A (l.toExposed A) := fun _ => ⟨l, rfl⟩

/--
theorem `isExposed_empty` / 定理 `isExposed_empty`

English:
theorem isExposed_empty
  statement: IsExposed 𝕜 A ∅
  proof: fun ⟨_, hx⟩ => by
  exfalso
  exact hx

中文:
定理 isExposed_empty
  结论: IsExposed 𝕜 A ∅
  证明: fun ⟨_, hx⟩ => by
  exfalso
  exact hx
-/
theorem isExposed_empty : IsExposed 𝕜 A ∅ := fun ⟨_, hx⟩ => by
  exfalso
  exact hx

namespace IsExposed

/--
theorem `subset` / 定理 `subset`

English:
theorem subset
  given: (hAB : IsExposed 𝕜 A B)
  statement: B subseteq A
  proof: by
  rintro x hx
  obtain ⟨_, rfl⟩ := hAB ⟨x, hx⟩
  exact hx.1

@[refl]

中文:
定理 subset
  条件: (hAB : IsExposed 𝕜 A B)
  结论: B subseteq A
  证明: by
  rintro x hx
  obtain ⟨_, rfl⟩ := hAB ⟨x, hx⟩
  exact hx.1

@[refl]
-/
protected theorem subset (hAB : IsExposed 𝕜 A B) : B subseteq A := by
  rintro x hx
  obtain ⟨_, rfl⟩ := hAB ⟨x, hx⟩
  exact hx.1

@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (A : Set E)
  statement: IsExposed 𝕜 A A
  proof: fun ⟨_, _⟩ =>
  ⟨0, Subset.antisymm (fun _ hx => ⟨hx, fun _ _ => le_refl 0⟩) fun _ hx => hx.1⟩

中文:
定理 refl
  条件: (A : 集合 E)
  结论: IsExposed 𝕜 A A
  证明: fun ⟨_, _⟩ =>
  ⟨0, Subset.antisymm (fun _ hx => ⟨hx, fun _ _ => le_refl 0⟩) fun _ hx => hx.1⟩
-/
protected theorem refl (A : Set E) : IsExposed 𝕜 A A := fun ⟨_, _⟩ =>
  ⟨0, Subset.antisymm (fun _ hx => ⟨hx, fun _ _ => le_refl 0⟩) fun _ hx => hx.1⟩

/--
theorem `antisymm` / 定理 `antisymm`

English:
theorem antisymm
  given: (hB : IsExposed 𝕜 A B) (hA : IsExposed 𝕜 B A)
  statement: A = B
  proof: hA.subset.antisymm hB.subset

中文:
定理 antisymm
  条件: (hB : IsExposed 𝕜 A B) (hA : IsExposed 𝕜 B A)
  结论: A = B
  证明: hA.subset.antisymm hB.subset
-/
protected theorem antisymm (hB : IsExposed 𝕜 A B) (hA : IsExposed 𝕜 B A) : A = B :=
  hA.subset.antisymm hB.subset


/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (hC : IsExposed 𝕜 A C) (hBA : B subseteq A) (hCB : C subseteq B)
  statement: IsExposed 𝕜 B C
  proof: by
  rintro ⟨w, hw⟩
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩
  exact ⟨l, Subset.antisymm (fun x hx => ⟨hCB hx, fun y hy => hx.2 y (hBA hy)⟩) fun x hx =>
    ⟨hBA hx.1, fun y hy => (hw.2 y hy).trans (hx.2 w (hCB hw))⟩⟩

中文:
定理 mono
  条件: (hC : IsExposed 𝕜 A C) (hBA : B subseteq A) (hCB : C subseteq B)
  结论: IsExposed 𝕜 B C
  证明: by
  rintro ⟨w, hw⟩
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩
  exact ⟨l, Subset.antisymm (fun x hx => ⟨hCB hx, fun y hy => hx.2 y (hBA hy)⟩) fun x hx =>
    ⟨hBA hx.1, fun y hy => (hw.2 y hy).trans (hx.2 w (hCB hw))⟩⟩
-/
protected theorem mono (hC : IsExposed 𝕜 A C) (hBA : B subseteq A) (hCB : C subseteq B) : IsExposed 𝕜 B C := by
  rintro ⟨w, hw⟩
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩
  exact ⟨l, Subset.antisymm (fun x hx => ⟨hCB hx, fun y hy => hx.2 y (hBA hy)⟩) fun x hx =>
    ⟨hBA hx.1, fun y hy => (hw.2 y hy).trans (hx.2 w (hCB hw))⟩⟩

/--
theorem `eq_inter_halfSpace'` / 定理 `eq_inter_halfSpace'`

English:
theorem eq_inter_halfSpace'
  given: {A B : Set E} (hAB : IsExposed 𝕜 A B) (hB : B.Nonempty)
  proof: by
  obtain ⟨l, rfl⟩ := hAB hB
  obtain ⟨w, hw⟩ := hB
  exact ⟨l, l w, Subset.antisymm (fun x hx => ⟨hx.1, hx.2 w hw.1⟩) fun x hx =>
    ⟨hx.1, fun y hy => (hw.2 y hy).trans hx.2⟩⟩

中文:
定理 eq_inter_halfSpace'
  条件: {A B : 集合 E} (hAB : IsExposed 𝕜 A B) (hB : B.非空)
  证明: by
  obtain ⟨l, rfl⟩ := hAB hB
  obtain ⟨w, hw⟩ := hB
  exact ⟨l, l w, Subset.antisymm (fun x hx => ⟨hx.1, hx.2 w hw.1⟩) fun x hx =>
    ⟨hx.1, fun y hy => (hw.2 y hy).trans hx.2⟩⟩

Depends on / 依赖: Subset, Subset.antisymm, antisymm
-/
theorem eq_inter_halfSpace' {A B : Set E} (hAB : IsExposed 𝕜 A B) (hB : B.Nonempty) :
    exists l : StrongDual 𝕜 E, exists a, B = { x in A | a <= l x } := by
  obtain ⟨l, rfl⟩ := hAB hB
  obtain ⟨w, hw⟩ := hB
  exact ⟨l, l w, Subset.antisymm (fun x hx => ⟨hx.1, hx.2 w hw.1⟩) fun x hx =>
    ⟨hx.1, fun y hy => (hw.2 y hy).trans hx.2⟩⟩

/--
theorem `eq_inter_halfSpace` / 定理 `eq_inter_halfSpace`

English:
theorem eq_inter_halfSpace
  given: [IsOrderedRing 𝕜] [Nontrivial 𝕜] {A B : Set E} (hAB : IsExposed 𝕜 A B)
  proof: by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · refine ⟨0, 1, ?_⟩
    rw [eq_comm]; rw [eq_empty_iff_forall_notMem]
    rintro x ⟨-, h⟩
    rw [zero_apply] at h
    have : ¬(1 : 𝕜) <= 0 := not_le_of_gt zero_lt_one
    contradiction
  exact hAB.eq_inter_halfSpace' hB

中文:
定理 eq_inter_halfSpace
  条件: [是Ordered环 𝕜] [非平凡 𝕜] {A B : 集合 E} (hAB : IsExposed 𝕜 A B)
  证明: by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · refine ⟨0, 1, ?_⟩
    rw [eq_comm]; rw [eq_empty_iff_forall_notMem]
    rintro x ⟨-, h⟩
    rw [zero_apply] at h
    have : ¬(1 : 𝕜) <= 0 := not_le_of_gt zero_lt_one
    contradiction
  exact hAB.eq_inter_halfSpace' hB

Depends on / 依赖: B.eq_empty_or_nonempty, eq_comm, eq_empty_iff_forall_notMem, eq_empty_or_nonempty, eq_inter_halfSpace, hAB.eq_inter_halfSpace, not_le_of_gt, zero_apply, zero_lt_one
-/
theorem eq_inter_halfSpace [IsOrderedRing 𝕜] [Nontrivial 𝕜] {A B : Set E} (hAB : IsExposed 𝕜 A B) :
    exists l : StrongDual 𝕜 E, exists a, B = { x in A | a <= l x } := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · refine ⟨0, 1, ?_⟩
    rw [eq_comm]; rw [eq_empty_iff_forall_notMem]
    rintro x ⟨-, h⟩
    rw [zero_apply] at h
    have : ¬(1 : 𝕜) <= 0 := not_le_of_gt zero_lt_one
    contradiction
  exact hAB.eq_inter_halfSpace' hB

/--
theorem `inter` / 定理 `inter`

English:
theorem inter
  statement: [IsOrderedRing 𝕜] [ContinuousAdd 𝕜] {A B C : Set E} (hB : IsExposed 𝕜 A B)
  proof: by
  rintro ⟨w, hwB, hwC⟩
  obtain ⟨l₁, rfl⟩ := hB ⟨w, hwB⟩
  obtain ⟨l₂, rfl⟩ := hC ⟨w, hwC⟩
  refine ⟨l₁ + l₂, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨⟨hxA, hxB⟩, ⟨-, hxC⟩⟩
    exact ⟨hxA, fun z hz => add_le_add (hxB z hz) (hxC z hz)⟩
  rintro x ⟨hxA, hx⟩
  refine ⟨⟨hxA, fun y hy => ?_⟩, hxA, fun y h

中文:
定理 inter
  结论: [是Ordered环 𝕜] [连续加法 𝕜] {A B C : 集合 E} (hB : IsExposed 𝕜 A B)
  证明: by
  rintro ⟨w, hwB, hwC⟩
  obtain ⟨l₁, rfl⟩ := hB ⟨w, hwB⟩
  obtain ⟨l₂, rfl⟩ := hC ⟨w, hwC⟩
  refine ⟨l₁ + l₂, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨⟨hxA, hxB⟩, ⟨-, hxC⟩⟩
    exact ⟨hxA, fun z hz => add_le_add (hxB z hz) (hxC z hz)⟩
  rintro x ⟨hxA, hx⟩
  refine ⟨⟨hxA, fun y hy => ?_⟩, hxA, fun y h
-/
protected theorem inter [IsOrderedRing 𝕜] [ContinuousAdd 𝕜] {A B C : Set E} (hB : IsExposed 𝕜 A B)
    (hC : IsExposed 𝕜 A C) : IsExposed 𝕜 A (B inter C) := by
  rintro ⟨w, hwB, hwC⟩
  obtain ⟨l₁, rfl⟩ := hB ⟨w, hwB⟩
  obtain ⟨l₂, rfl⟩ := hC ⟨w, hwC⟩
  refine ⟨l₁ + l₂, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨⟨hxA, hxB⟩, ⟨-, hxC⟩⟩
    exact ⟨hxA, fun z hz => add_le_add (hxB z hz) (hxC z hz)⟩
  rintro x ⟨hxA, hx⟩
  refine ⟨⟨hxA, fun y hy => ?_⟩, hxA, fun y hy => ?_⟩
  · exact
      (add_le_add_iff_right (l₂ x)).1 ((add_le_add (hwB.2 y hy) (hwC.2 x hxA)).trans (hx w hwB.1))
  · exact
      (add_le_add_iff_left (l₁ x)).1 (le_trans (add_le_add (hwB.2 x hxA) (hwC.2 y hy)) (hx w hwB.1))

/--
theorem `sInter` / 定理 `sInter`

English:
theorem sInter
  statement: [IsOrderedRing 𝕜] [ContinuousAdd 𝕜] {F : Finset (Set E)} (hF : F.Nonempty)
  proof: by
  induction F using Finset.induction with
  | empty => exfalso; exact Finset.not_nonempty_empty hF
  | insert C F _ hF' =>
    rw [Finset.coe_insert]; rw [sInter_insert]
    obtain rfl | hFnemp := F.eq_empty_or_nonempty
    · rw [Finset.coe_empty, sInter_empty, inter_univ]
      exact hAF C (Fins

中文:
定理 集合交集
  结论: [是Ordered环 𝕜] [连续加法 𝕜] {F : 有限集 (集合 E)} (hF : F.非空)
  证明: by
  induction F using Finset.induction with
  | empty => exfalso; exact Finset.not_nonempty_empty hF
  | insert C F _ hF' =>
    rw [Finset.coe_insert]; rw [sInter_insert]
    obtain rfl | hFnemp := F.eq_empty_or_nonempty
    · rw [Finset.coe_empty, sInter_empty, inter_univ]
      exact hAF C (Fins

Depends on / 依赖: F.eq_empty_or_nonempty, Finset, Finset.coe_empty, Finset.coe_insert, Finset.induction, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.mem_singleton_self, Finset.not_nonempty_empty, coe_empty, coe_insert, eq_empty_or_nonempty, hFnemp, insert, inter_univ, mem_insert_of_mem, mem_insert_self, mem_singleton_self, not_nonempty_empty, sInter_empty
-/
theorem sInter [IsOrderedRing 𝕜] [ContinuousAdd 𝕜] {F : Finset (Set E)} (hF : F.Nonempty)
    (hAF : forall B in F, IsExposed 𝕜 A B) : IsExposed 𝕜 A (⋂₀ F) := by
  induction F using Finset.induction with
  | empty => exfalso; exact Finset.not_nonempty_empty hF
  | insert C F _ hF' =>
    rw [Finset.coe_insert]; rw [sInter_insert]
    obtain rfl | hFnemp := F.eq_empty_or_nonempty
    · rw [Finset.coe_empty, sInter_empty, inter_univ]
      exact hAF C (Finset.mem_singleton_self C)
    · exact (hAF C (Finset.mem_insert_self C F)).inter
        (hF' hFnemp fun B hB => hAF B (Finset.mem_insert_of_mem hB))

/--
theorem `inter_left` / 定理 `inter_left`

English:
theorem inter_left
  given: (hC : IsExposed 𝕜 A C) (hCB : C subseteq B)
  statement: IsExposed 𝕜 (A inter B) C
  proof: by
  rintro ⟨w, hw⟩
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩
  exact ⟨l, Subset.antisymm (fun x hx => ⟨⟨hx.1, hCB hx⟩, fun y hy => hx.2 y hy.1⟩)
    fun x ⟨⟨hxC, _⟩, hx⟩ => ⟨hxC, fun y hy => (hw.2 y hy).trans (hx w ⟨hC.subset hw, hCB hw⟩)⟩⟩

中文:
定理 inter_left
  条件: (hC : IsExposed 𝕜 A C) (hCB : C subseteq B)
  结论: IsExposed 𝕜 (A inter B) C
  证明: by
  rintro ⟨w, hw⟩
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩
  exact ⟨l, Subset.antisymm (fun x hx => ⟨⟨hx.1, hCB hx⟩, fun y hy => hx.2 y hy.1⟩)
    fun x ⟨⟨hxC, _⟩, hx⟩ => ⟨hxC, fun y hy => (hw.2 y hy).trans (hx w ⟨hC.subset hw, hCB hw⟩)⟩⟩

Depends on / 依赖: Subset, Subset.antisymm, antisymm, hC.subset, subset
-/
theorem inter_left (hC : IsExposed 𝕜 A C) (hCB : C subseteq B) : IsExposed 𝕜 (A inter B) C := by
  rintro ⟨w, hw⟩
  obtain ⟨l, rfl⟩ := hC ⟨w, hw⟩
  exact ⟨l, Subset.antisymm (fun x hx => ⟨⟨hx.1, hCB hx⟩, fun y hy => hx.2 y hy.1⟩)
    fun x ⟨⟨hxC, _⟩, hx⟩ => ⟨hxC, fun y hy => (hw.2 y hy).trans (hx w ⟨hC.subset hw, hCB hw⟩)⟩⟩

/--
theorem `inter_right` / 定理 `inter_right`

English:
theorem inter_right
  given: (hC : IsExposed 𝕜 B C) (hCA : C subseteq A)
  statement: IsExposed 𝕜 (A inter B) C
  proof: by
  rw [inter_comm]
  exact hC.inter_left hCA

中文:
定理 inter_right
  条件: (hC : IsExposed 𝕜 B C) (hCA : C subseteq A)
  结论: IsExposed 𝕜 (A inter B) C
  证明: by
  rw [inter_comm]
  exact hC.inter_left hCA

Depends on / 依赖: hC.inter_left, inter_comm, inter_left
-/
theorem inter_right (hC : IsExposed 𝕜 B C) (hCA : C subseteq A) : IsExposed 𝕜 (A inter B) C := by
  rw [inter_comm]
  exact hC.inter_left hCA

/--
theorem `isClosed` / 定理 `isClosed`

English:
theorem isClosed
  statement: [OrderClosedTopology 𝕜] {A B : Set E} (hAB : IsExposed 𝕜 A B)
  proof: by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp
  obtain ⟨l, a, rfl⟩ := hAB.eq_inter_halfSpace' hB
  exact hA.isClosed_le continuousOn_const l.continuous.continuousOn

中文:
定理 isClosed
  结论: [OrderClosed拓扑 𝕜] {A B : 集合 E} (hAB : IsExposed 𝕜 A B)
  证明: by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp
  obtain ⟨l, a, rfl⟩ := hAB.eq_inter_halfSpace' hB
  exact hA.isClosed_le continuousOn_const l.continuous.continuousOn
-/
protected theorem isClosed [OrderClosedTopology 𝕜] {A B : Set E} (hAB : IsExposed 𝕜 A B)
    (hA : IsClosed A) : IsClosed B := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · simp
  obtain ⟨l, a, rfl⟩ := hAB.eq_inter_halfSpace' hB
  exact hA.isClosed_le continuousOn_const l.continuous.continuousOn

/--
theorem `isCompact` / 定理 `isCompact`

English:
theorem isCompact
  statement: [OrderClosedTopology 𝕜] [T2Space E] {A B : Set E}
  proof: hA.of_isClosed_subset (hAB.isClosed hA.isClosed) hAB.subset

中文:
定理 isCompact
  结论: [OrderClosed拓扑 𝕜] [T2空间 E] {A B : 集合 E}
  证明: hA.of_isClosed_subset (hAB.isClosed hA.isClosed) hAB.subset
-/
protected theorem isCompact [OrderClosedTopology 𝕜] [T2Space E] {A B : Set E}
    (hAB : IsExposed 𝕜 A B) (hA : IsCompact A) : IsCompact B :=
  hA.of_isClosed_subset (hAB.isClosed hA.isClosed) hAB.subset

end IsExposed

variable (𝕜) in
/--
Definition of `Set.exposedPoints` / `Set.exposedPoints` 的定义

English:
definition Set.exposedPoints
  signature: (A : Set E)
  body: { x in A | exists l : StrongDual 𝕜 E, forall y in A, l y <= l x ∧ (l x <= l y -> y = x) }

中文:
定义 集合.exposedPoints
  签名: (A : 集合 E)
  定义体: { x in A | exists l : StrongDual 𝕜 E, forall y in A, l y <= l x ∧ (l x <= l y -> y = x) }

Depends on / 依赖: StrongDual
-/
def Set.exposedPoints (A : Set E) : Set E :=
  { x in A | exists l : StrongDual 𝕜 E, forall y in A, l y <= l x ∧ (l x <= l y -> y = x) }

/--
theorem `exposed_point_def` / 定理 `exposed_point_def`

English:
theorem exposed_point_def
  proof: Iff.rfl

中文:
定理 exposed_point_def
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem exposed_point_def :
    x in A.exposedPoints 𝕜 ↔ x in A ∧ exists l :
    StrongDual 𝕜 E, forall y in A, l y <= l x ∧ (l x <= l y -> y = x) := Iff.rfl

/--
theorem `exposedPoints_subset` / 定理 `exposedPoints_subset`

English:
theorem exposedPoints_subset
  statement: A.exposedPoints 𝕜 subseteq A
  proof: fun _ hx => hx.1

@[simp]

中文:
定理 exposedPoints_subset
  结论: A.exposedPoints 𝕜 subseteq A
  证明: fun _ hx => hx.1

@[simp]
-/
theorem exposedPoints_subset : A.exposedPoints 𝕜 subseteq A := fun _ hx => hx.1

@[simp]
/--
theorem `exposedPoints_empty` / 定理 `exposedPoints_empty`

English:
theorem exposedPoints_empty
  statement: (∅ : Set E).exposedPoints 𝕜 = ∅
  proof: subset_empty_iff.1 exposedPoints_subset

中文:
定理 exposedPoints_empty
  结论: (∅ : 集合 E).exposedPoints 𝕜 = ∅
  证明: subset_empty_iff.1 exposedPoints_subset

Depends on / 依赖: exposedPoints_subset, subset_empty_iff
-/
theorem exposedPoints_empty : (∅ : Set E).exposedPoints 𝕜 = ∅ :=
  subset_empty_iff.1 exposedPoints_subset

/--
theorem `mem_exposedPoints_iff_exposed_singleton` / 定理 `mem_exposedPoints_iff_exposed_singleton`

English:
theorem mem_exposedPoints_iff_exposed_singleton
  statement: x in A.exposedPoints 𝕜 ↔ IsExposed 𝕜 A {x}
  proof: by
  use fun ⟨hxA, l, hl⟩ _ =>
    ⟨l,
Eq.symm
        eq_singleton_iff_unique_mem.2
          ⟨⟨hxA, fun y hy => (hl y hy).1⟩, fun z hz => (hl z hz.1).2 (hz.2 x hxA)⟩⟩
  rintro h
  obtain ⟨l, hl⟩ := h ⟨x, mem_singleton _⟩
  rw [eq_comm]; rw [eq_singleton_iff_unique_mem] at hl
  exact
    ⟨hl.1.1, l

中文:
定理 mem_exposedPoints_iff_exposed_singleton
  结论: x in A.exposedPoints 𝕜 ↔ IsExposed 𝕜 A {x}
  证明: by
  use fun ⟨hxA, l, hl⟩ _ =>
    ⟨l,
Eq.symm
        eq_singleton_iff_unique_mem.2
          ⟨⟨hxA, fun y hy => (hl y hy).1⟩, fun z hz => (hl z hz.1).2 (hz.2 x hxA)⟩⟩
  rintro h
  obtain ⟨l, hl⟩ := h ⟨x, mem_singleton _⟩
  rw [eq_comm]; rw [eq_singleton_iff_unique_mem] at hl
  exact
    ⟨hl.1.1, l

Depends on / 依赖: Eq.symm, eq_comm, eq_singleton_iff_unique_mem, mem_singleton
-/
theorem mem_exposedPoints_iff_exposed_singleton : x in A.exposedPoints 𝕜 ↔ IsExposed 𝕜 A {x} := by
  use fun ⟨hxA, l, hl⟩ _ =>
    ⟨l,
Eq.symm
        eq_singleton_iff_unique_mem.2
          ⟨⟨hxA, fun y hy => (hl y hy).1⟩, fun z hz => (hl z hz.1).2 (hz.2 x hxA)⟩⟩
  rintro h
  obtain ⟨l, hl⟩ := h ⟨x, mem_singleton _⟩
  rw [eq_comm]; rw [eq_singleton_iff_unique_mem] at hl
  exact
    ⟨hl.1.1, l, fun y hy =>
      ⟨hl.1.2 y hy, fun hxy => hl.2 y ⟨hy, fun z hz => (hl.1.2 z hz).trans hxy⟩⟩⟩

end OrderedRing

section LinearOrderedRing

variable {𝕜 : Type*} {E : Type*} [TopologicalSpace 𝕜]
  [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommMonoid E]
  [TopologicalSpace E] [Module 𝕜 E] {A B : Set E}

namespace IsExposed

/--
theorem `convex` / 定理 `convex`

English:
theorem convex
  given: (hAB : IsExposed 𝕜 A B) (hA : Convex 𝕜 A)
  statement: Convex 𝕜 B
  proof: by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · exact convex_empty
  obtain ⟨l, rfl⟩ := hAB hB
  exact fun x₁ hx₁ x₂ hx₂ a b ha hb hab =>
    ⟨hA hx₁.1 hx₂.1 ha hb hab, fun y hy =>
      ((l.toLinearMap.concaveOn convex_univ).convex_ge _ ⟨mem_univ _, hx₁.2 y hy⟩
          ⟨mem_univ _, hx₂.2 y hy⟩

中文:
定理 convex
  条件: (hAB : IsExposed 𝕜 A B) (hA : 凸 𝕜 A)
  结论: 凸 𝕜 B
  证明: by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · exact convex_empty
  obtain ⟨l, rfl⟩ := hAB hB
  exact fun x₁ hx₁ x₂ hx₂ a b ha hb hab =>
    ⟨hA hx₁.1 hx₂.1 ha hb hab, fun y hy =>
      ((l.toLinearMap.concaveOn convex_univ).convex_ge _ ⟨mem_univ _, hx₁.2 y hy⟩
          ⟨mem_univ _, hx₂.2 y hy⟩
-/
protected theorem convex (hAB : IsExposed 𝕜 A B) (hA : Convex 𝕜 A) : Convex 𝕜 B := by
  obtain rfl | hB := B.eq_empty_or_nonempty
  · exact convex_empty
  obtain ⟨l, rfl⟩ := hAB hB
  exact fun x₁ hx₁ x₂ hx₂ a b ha hb hab =>
    ⟨hA hx₁.1 hx₂.1 ha hb hab, fun y hy =>
      ((l.toLinearMap.concaveOn convex_univ).convex_ge _ ⟨mem_univ _, hx₁.2 y hy⟩
          ⟨mem_univ _, hx₂.2 y hy⟩ ha hb hab).2⟩

/--
theorem `isExtreme` / 定理 `isExtreme`

English:
theorem isExtreme
  given: (hAB : IsExposed 𝕜 A B)
  statement: IsExtreme 𝕜 A B
  proof: by
  refine ⟨hAB.subset, fun x₁ hx₁A x₂ hx₂A x hxB hx => ?_⟩
  obtain ⟨l, rfl⟩ := hAB ⟨x, hxB⟩
  have hl : ConvexOn 𝕜 univ l := l.toLinearMap.convexOn convex_univ
  have hlx₁ := hxB.2 x₁ hx₁A
  have hlx₂ := hxB.2 x₂ hx₂A
  refine ⟨hx₁A, fun y hy => ?_⟩
  rw [hlx₁.antisymm (hl.le_left_of_right_le (me

中文:
定理 isExtreme
  条件: (hAB : IsExposed 𝕜 A B)
  结论: 是Extreme 𝕜 A B
  证明: by
  refine ⟨hAB.subset, fun x₁ hx₁A x₂ hx₂A x hxB hx => ?_⟩
  obtain ⟨l, rfl⟩ := hAB ⟨x, hxB⟩
  have hl : ConvexOn 𝕜 univ l := l.toLinearMap.convexOn convex_univ
  have hlx₁ := hxB.2 x₁ hx₁A
  have hlx₂ := hxB.2 x₂ hx₂A
  refine ⟨hx₁A, fun y hy => ?_⟩
  rw [hlx₁.antisymm (hl.le_left_of_right_le (me
-/
protected theorem isExtreme (hAB : IsExposed 𝕜 A B) : IsExtreme 𝕜 A B := by
  refine ⟨hAB.subset, fun x₁ hx₁A x₂ hx₂A x hxB hx => ?_⟩
  obtain ⟨l, rfl⟩ := hAB ⟨x, hxB⟩
  have hl : ConvexOn 𝕜 univ l := l.toLinearMap.convexOn convex_univ
  have hlx₁ := hxB.2 x₁ hx₁A
  have hlx₂ := hxB.2 x₂ hx₂A
  refine ⟨hx₁A, fun y hy => ?_⟩
  rw [hlx₁.antisymm (hl.le_left_of_right_le (mem_univ _) (mem_univ _) hx hlx₂)]
  exact hxB.2 y hy

end IsExposed

/--
theorem `exposedPoints_subset_extremePoints` / 定理 `exposedPoints_subset_extremePoints`

English:
theorem exposedPoints_subset_extremePoints
  statement: A.exposedPoints 𝕜 subseteq A.extremePoints 𝕜
  proof: fun _ hx =>
  (mem_exposedPoints_iff_exposed_singleton.1 hx).isExtreme.mem_extremePoints

中文:
定理 exposedPoints_subset_extremePoints
  结论: A.exposedPoints 𝕜 subseteq A.extremePoints 𝕜
  证明: fun _ hx =>
  (mem_exposedPoints_iff_exposed_singleton.1 hx).isExtreme.mem_extremePoints
-/
theorem exposedPoints_subset_extremePoints : A.exposedPoints 𝕜 subseteq A.extremePoints 𝕜 := fun _ hx =>
  (mem_exposedPoints_iff_exposed_singleton.1 hx).isExtreme.mem_extremePoints

end LinearOrderedRing
