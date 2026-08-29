/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Order.Closure

/-!
# Convex hull

This file defines the convex hull of a set `s` in a module. `convexHull 𝕜 s` is the smallest convex
set containing `s`. In order theory speak, this is a closure operator.

## Implementation notes

`convexHull` is defined as a closure operator. This gives access to the `ClosureOperator` API
while the impact on writing code is minimal as `convexHull 𝕜 s` is automatically elaborated as
`(convexHull 𝕜) s`.
-/

@[expose] public section


open Set

open scoped Pointwise

variable {𝕜 E F : Type*}

section convexHull

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable (𝕜)
variable [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F]

/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
@[simps! isClosed]
/--
Definition of `convexHull` / `convexHull` 的定义

English:
definition convexHull
  signature: : ClosureOperator (Set E)
  body: .ofCompletePred (Convex 𝕜) fun _ => convex_sInter

中文:
定义 convexHull
  签名: : 闭包算子 (集合 E)
  定义体: .ofCompletePred (Convex 𝕜) fun _ => convex_sInter

Depends on / 依赖: Convex, convex_sInter, ofCompletePred
-/
def convexHull : ClosureOperator (Set E) := .ofCompletePred (Convex 𝕜) fun _ => convex_sInter

variable (s : Set E)

/--
theorem `subset_convexHull` / 定理 `subset_convexHull`

English:
theorem subset_convexHull
  statement: s subseteq convexHull 𝕜 s
  proof: (convexHull 𝕜).le_closure s

中文:
定理 subset_convexHull
  结论: s subseteq convexHull 𝕜 s
  证明: (convexHull 𝕜).le_closure s

Depends on / 依赖: convexHull, le_closure
-/
theorem subset_convexHull : s subseteq convexHull 𝕜 s :=
  (convexHull 𝕜).le_closure s

/--
theorem `convex_convexHull` / 定理 `convex_convexHull`

English:
theorem convex_convexHull
  statement: Convex 𝕜 (convexHull 𝕜 s)
  proof: (convexHull 𝕜).isClosed_closure s

中文:
定理 convex_convexHull
  结论: 凸 𝕜 (convexHull 𝕜 s)
  证明: (convexHull 𝕜).isClosed_closure s

Depends on / 依赖: convexHull, isClosed_closure
-/
theorem convex_convexHull : Convex 𝕜 (convexHull 𝕜 s) := (convexHull 𝕜).isClosed_closure s

set_option backward.isDefEq.respectTransparency false in
/--
theorem `convexHull_eq_iInter` / 定理 `convexHull_eq_iInter`

English:
theorem convexHull_eq_iInter
  statement: convexHull 𝕜 s = ⋂ (t : Set E) (_ : s subseteq t) (_ : Convex 𝕜 t), t
  proof: by
  simp [convexHull, iInter_subtype, iInter_and]

中文:
定理 convexHull_eq_i整数er
  结论: convexHull 𝕜 s = ⋂ (t : 集合 E) (_ : s subseteq t) (_ : 凸 𝕜 t), t
  证明: by
  simp [convexHull, iInter_subtype, iInter_and]

Depends on / 依赖: convexHull, iInter_and, iInter_subtype
-/
theorem convexHull_eq_iInter : convexHull 𝕜 s = ⋂ (t : Set E) (_ : s subseteq t) (_ : Convex 𝕜 t), t := by
  simp [convexHull, iInter_subtype, iInter_and]

variable {𝕜 s} {t : Set E} {x y : E}

/--
theorem `mem_convexHull_iff` / 定理 `mem_convexHull_iff`

English:
theorem mem_convexHull_iff
  statement: x in convexHull 𝕜 s ↔ forall t, s subseteq t -> Convex 𝕜 t -> x in t
  proof: by
  simp_rw [convexHull_eq_iInter, mem_iInter]

中文:
定理 mem_convexHull_iff
  结论: x in convexHull 𝕜 s ↔ 对任意 t, s subseteq t -> 凸 𝕜 t -> x in t
  证明: by
  simp_rw [convexHull_eq_iInter, mem_iInter]

Depends on / 依赖: convexHull_eq_iInter, mem_iInter, simp_rw
-/
theorem mem_convexHull_iff : x in convexHull 𝕜 s ↔ forall t, s subseteq t -> Convex 𝕜 t -> x in t := by
  simp_rw [convexHull_eq_iInter, mem_iInter]

/--
theorem `convexHull_min` / 定理 `convexHull_min`

English:
theorem convexHull_min
  statement: s subseteq t -> Convex 𝕜 t -> convexHull 𝕜 s subseteq t
  proof: (convexHull 𝕜).closure_min

中文:
定理 convexHull_min
  结论: s subseteq t -> 凸 𝕜 t -> convexHull 𝕜 s subseteq t
  证明: (convexHull 𝕜).closure_min

Depends on / 依赖: closure_min, convexHull
-/
theorem convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHull 𝕜 s subseteq t := (convexHull 𝕜).closure_min

/--
theorem `Convex.convexHull_subset_iff` / 定理 `Convex.convexHull_subset_iff`

English:
theorem Convex.convexHull_subset_iff
  given: (ht : Convex 𝕜 t)
  statement: convexHull 𝕜 s subseteq t ↔ s subseteq t
  proof: (show (convexHull 𝕜).IsClosed t from ht).closure_le_iff

@[mono, gcongr]

中文:
定理 凸.convexHull_subset_iff
  条件: (ht : 凸 𝕜 t)
  结论: convexHull 𝕜 s subseteq t ↔ s subseteq t
  证明: (show (convexHull 𝕜).IsClosed t from ht).closure_le_iff

@[mono, gcongr]

Depends on / 依赖: IsClosed, closure_le_iff, convexHull
-/
theorem Convex.convexHull_subset_iff (ht : Convex 𝕜 t) : convexHull 𝕜 s subseteq t ↔ s subseteq t :=
  (show (convexHull 𝕜).IsClosed t from ht).closure_le_iff

@[mono, gcongr]
/--
theorem `convexHull_mono` / 定理 `convexHull_mono`

English:
theorem convexHull_mono
  given: (hst : s subseteq t)
  statement: convexHull 𝕜 s subseteq convexHull 𝕜 t
  proof: (convexHull 𝕜).monotone hst

中文:
定理 convexHull_mono
  条件: (hst : s subseteq t)
  结论: convexHull 𝕜 s subseteq convexHull 𝕜 t
  证明: (convexHull 𝕜).monotone hst

Depends on / 依赖: convexHull, monotone
-/
theorem convexHull_mono (hst : s subseteq t) : convexHull 𝕜 s subseteq convexHull 𝕜 t :=
  (convexHull 𝕜).monotone hst

/--
lemma `convexHull_eq_self` / 引理 `convexHull_eq_self`

English:
lemma convexHull_eq_self
  statement: convexHull 𝕜 s = s ↔ Convex 𝕜 s
  proof: (convexHull 𝕜).isClosed_iff.symm

alias ⟨_, Convex.convexHull_eq⟩ := convexHull_eq_self

@[simp]

中文:
引理 convexHull_eq_self
  结论: convexHull 𝕜 s = s ↔ 凸 𝕜 s
  证明: (convexHull 𝕜).isClosed_iff.symm

alias ⟨_, Convex.convexHull_eq⟩ := convexHull_eq_self

@[simp]

Depends on / 依赖: convexHull, isClosed_iff, isClosed_iff.symm
-/
lemma convexHull_eq_self : convexHull 𝕜 s = s ↔ Convex 𝕜 s := (convexHull 𝕜).isClosed_iff.symm

alias ⟨_, Convex.convexHull_eq⟩ := convexHull_eq_self

@[simp]
/--
theorem `convexHull_univ` / 定理 `convexHull_univ`

English:
theorem convexHull_univ
  statement: convexHull 𝕜 (univ : Set E) = univ
  proof: ClosureOperator.closure_top (convexHull 𝕜)

@[simp]

中文:
定理 convexHull_univ
  结论: convexHull 𝕜 (univ : 集合 E) = univ
  证明: ClosureOperator.closure_top (convexHull 𝕜)

@[simp]

Depends on / 依赖: ClosureOperator, ClosureOperator.closure_top, closure_top, convexHull
-/
theorem convexHull_univ : convexHull 𝕜 (univ : Set E) = univ :=
  ClosureOperator.closure_top (convexHull 𝕜)

@[simp]
/--
theorem `convexHull_empty` / 定理 `convexHull_empty`

English:
theorem convexHull_empty
  statement: convexHull 𝕜 (∅ : Set E) = ∅
  proof: convex_empty.convexHull_eq

@[simp]

中文:
定理 convexHull_empty
  结论: convexHull 𝕜 (∅ : 集合 E) = ∅
  证明: convex_empty.convexHull_eq

@[simp]

Depends on / 依赖: convexHull_eq, convex_empty, convex_empty.convexHull_eq
-/
theorem convexHull_empty : convexHull 𝕜 (∅ : Set E) = ∅ :=
  convex_empty.convexHull_eq

@[simp]
/--
theorem `convexHull_eq_empty` / 定理 `convexHull_eq_empty`

English:
theorem convexHull_eq_empty
  statement: convexHull 𝕜 s = ∅ ↔ s = ∅
  proof: by
  constructor
  · intro h
    rw [← Set.subset_empty_iff]; rw [← h]
    exact subset_convexHull 𝕜 _
  · rintro rfl
    exact convexHull_empty

@[simp]

中文:
定理 convexHull_eq_empty
  结论: convexHull 𝕜 s = ∅ ↔ s = ∅
  证明: by
  constructor
  · intro h
    rw [← Set.subset_empty_iff]; rw [← h]
    exact subset_convexHull 𝕜 _
  · rintro rfl
    exact convexHull_empty

@[simp]

Depends on / 依赖: Set.subset_empty_iff, convexHull_empty, subset_convexHull, subset_empty_iff
-/
theorem convexHull_eq_empty : convexHull 𝕜 s = ∅ ↔ s = ∅ := by
  constructor
  · intro h
    rw [← Set.subset_empty_iff]; rw [← h]
    exact subset_convexHull 𝕜 _
  · rintro rfl
    exact convexHull_empty

@[simp]
/--
theorem `convexHull_nonempty_iff` / 定理 `convexHull_nonempty_iff`

English:
theorem convexHull_nonempty_iff
  statement: (convexHull 𝕜 s).Nonempty ↔ s.Nonempty
  proof: by
  rw [nonempty_iff_ne_empty]; rw [nonempty_iff_ne_empty]; rw [Ne]; rw [Ne]
  exact not_congr convexHull_eq_empty

protected alias ⟨_, Set.Nonempty.convexHull⟩ := convexHull_nonempty_iff

中文:
定理 convexHull_nonempty_iff
  结论: (convexHull 𝕜 s).非空 ↔ s.非空
  证明: by
  rw [nonempty_iff_ne_empty]; rw [nonempty_iff_ne_empty]; rw [Ne]; rw [Ne]
  exact not_congr convexHull_eq_empty

protected alias ⟨_, Set.Nonempty.convexHull⟩ := convexHull_nonempty_iff

Depends on / 依赖: convexHull_eq_empty, nonempty_iff_ne_empty, not_congr
-/
theorem convexHull_nonempty_iff : (convexHull 𝕜 s).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty]; rw [nonempty_iff_ne_empty]; rw [Ne]; rw [Ne]
  exact not_congr convexHull_eq_empty

protected alias ⟨_, Set.Nonempty.convexHull⟩ := convexHull_nonempty_iff

/--
theorem `segment_subset_convexHull` / 定理 `segment_subset_convexHull`

English:
theorem segment_subset_convexHull
  given: (hx : x in s) (hy : y in s)
  statement: segment 𝕜 x y subseteq convexHull 𝕜 s
  proof: (convex_convexHull _ _).segment_subset (subset_convexHull _ _ hx) (subset_convexHull _ _ hy)

@[simp]

中文:
定理 segment_subset_convexHull
  条件: (hx : x in s) (hy : y in s)
  结论: segment 𝕜 x y subseteq convexHull 𝕜 s
  证明: (convex_convexHull _ _).segment_subset (subset_convexHull _ _ hx) (subset_convexHull _ _ hy)

@[simp]

Depends on / 依赖: convex_convexHull, segment_subset, subset_convexHull
-/
theorem segment_subset_convexHull (hx : x in s) (hy : y in s) : segment 𝕜 x y subseteq convexHull 𝕜 s :=
  (convex_convexHull _ _).segment_subset (subset_convexHull _ _ hx) (subset_convexHull _ _ hy)

@[simp]
/--
theorem `convexHull_singleton` / 定理 `convexHull_singleton`

English:
theorem convexHull_singleton
  given: (x : E)
  statement: convexHull 𝕜 ({x} : Set E) = {x}
  proof: (convex_singleton x).convexHull_eq

中文:
定理 convexHull_singleton
  条件: (x : E)
  结论: convexHull 𝕜 ({x} : 集合 E) = {x}
  证明: (convex_singleton x).convexHull_eq

Depends on / 依赖: convexHull_eq, convex_singleton
-/
theorem convexHull_singleton (x : E) : convexHull 𝕜 ({x} : Set E) = {x} :=
  (convex_singleton x).convexHull_eq

/--
lemma `convexHull_eq_singleton` / 引理 `convexHull_eq_singleton`

English:
lemma convexHull_eq_singleton
  statement: convexHull 𝕜 s = {x} ↔ s = {x} where
  proof: by
    rw [← Set.Nonempty.subset_singleton_iff]; rw [← hs]
    · exact subset_convexHull ..
    · by_contra! hs
      simp_all [eq_comm (a := ∅)]
  mpr hs := by simp [hs]

@[simp]

中文:
引理 convexHull_eq_singleton
  结论: convexHull 𝕜 s = {x} ↔ s = {x} where
  证明: by
    rw [← Set.Nonempty.subset_singleton_iff]; rw [← hs]
    · exact subset_convexHull ..
    · by_contra! hs
      simp_all [eq_comm (a := ∅)]
  mpr hs := by simp [hs]

@[simp]
-/
@[simp] lemma convexHull_eq_singleton : convexHull 𝕜 s = {x} ↔ s = {x} where
  mp hs := by
    rw [← Set.Nonempty.subset_singleton_iff]; rw [← hs]
    · exact subset_convexHull ..
    · by_contra! hs
      simp_all [eq_comm (a := ∅)]
  mpr hs := by simp [hs]

@[simp]
/--
theorem `convexHull_zero` / 定理 `convexHull_zero`

English:
theorem convexHull_zero
  statement: convexHull 𝕜 (0 : Set E) = 0
  proof: convexHull_singleton 0

中文:
定理 convexHull_zero
  结论: convexHull 𝕜 (0 : 集合 E) = 0
  证明: convexHull_singleton 0

Depends on / 依赖: convexHull_singleton
-/
theorem convexHull_zero : convexHull 𝕜 (0 : Set E) = 0 :=
  convexHull_singleton 0

/--
lemma `convexHull_eq_zero` / 引理 `convexHull_eq_zero`

English:
lemma convexHull_eq_zero
  statement: convexHull 𝕜 s = 0 ↔ s = 0
  proof: convexHull_eq_singleton

@[simp]

中文:
引理 convexHull_eq_zero
  结论: convexHull 𝕜 s = 0 ↔ s = 0
  证明: convexHull_eq_singleton

@[simp]
-/
@[simp] lemma convexHull_eq_zero : convexHull 𝕜 s = 0 ↔ s = 0 := convexHull_eq_singleton

@[simp]
/--
theorem `convexHull_pair` / 定理 `convexHull_pair`

English:
theorem convexHull_pair
  given: [IsOrderedRing 𝕜] (x y : E)
  statement: convexHull 𝕜 {x, y} = segment 𝕜 x y
  proof: by
  refine (convexHull_min ?_ <| convex_segment _ _).antisymm
    (segment_subset_convexHull (mem_insert _ _) <| subset_insert _ _ <| mem_singleton _)
  rw [insert_subset_iff]; rw [singleton_subset_iff]
  exact ⟨left_mem_segment _ _ _, right_mem_segment _ _ _⟩

中文:
定理 convexHull_pair
  条件: [是Ordered环 𝕜] (x y : E)
  结论: convexHull 𝕜 {x, y} = segment 𝕜 x y
  证明: by
  refine (convexHull_min ?_ <| convex_segment _ _).antisymm
    (segment_subset_convexHull (mem_insert _ _) <| subset_insert _ _ <| mem_singleton _)
  rw [insert_subset_iff]; rw [singleton_subset_iff]
  exact ⟨left_mem_segment _ _ _, right_mem_segment _ _ _⟩

Depends on / 依赖: antisymm, convexHull_min, convex_segment, insert_subset_iff, left_mem_segment, mem_insert, mem_singleton, right_mem_segment, segment_subset_convexHull, singleton_subset_iff, subset_insert
-/
theorem convexHull_pair [IsOrderedRing 𝕜] (x y : E) : convexHull 𝕜 {x, y} = segment 𝕜 x y := by
  refine (convexHull_min ?_ <| convex_segment _ _).antisymm
    (segment_subset_convexHull (mem_insert _ _) <| subset_insert _ _ <| mem_singleton _)
  rw [insert_subset_iff]; rw [singleton_subset_iff]
  exact ⟨left_mem_segment _ _ _, right_mem_segment _ _ _⟩

/--
theorem `convexHull_convexHull_union_left` / 定理 `convexHull_convexHull_union_left`

English:
theorem convexHull_convexHull_union_left
  given: (s t : Set E)
  proof: ClosureOperator.closure_sup_closure_left _ _ _

中文:
定理 convexHull_convexHull_union_left
  条件: (s t : 集合 E)
  证明: ClosureOperator.closure_sup_closure_left _ _ _

Depends on / 依赖: ClosureOperator, ClosureOperator.closure_sup_closure_left, closure_sup_closure_left
-/
theorem convexHull_convexHull_union_left (s t : Set E) :
    convexHull 𝕜 (convexHull 𝕜 s union t) = convexHull 𝕜 (s union t) :=
  ClosureOperator.closure_sup_closure_left _ _ _

/--
theorem `convexHull_convexHull_union_right` / 定理 `convexHull_convexHull_union_right`

English:
theorem convexHull_convexHull_union_right
  given: (s t : Set E)
  proof: ClosureOperator.closure_sup_closure_right _ _ _

中文:
定理 convexHull_convexHull_union_right
  条件: (s t : 集合 E)
  证明: ClosureOperator.closure_sup_closure_right _ _ _

Depends on / 依赖: ClosureOperator, ClosureOperator.closure_sup_closure_right, closure_sup_closure_right
-/
theorem convexHull_convexHull_union_right (s t : Set E) :
    convexHull 𝕜 (s union convexHull 𝕜 t) = convexHull 𝕜 (s union t) :=
  ClosureOperator.closure_sup_closure_right _ _ _

/--
theorem `Convex.convex_remove_iff_notMem_convexHull_remove` / 定理 `Convex.convex_remove_iff_notMem_convexHull_remove`

English:
theorem Convex.convex_remove_iff_notMem_convexHull_remove
  given: {s : Set E} (hs : Convex 𝕜 s) (x : E)
  proof: by
  constructor
  · rintro hsx hx
    rw [hsx.convexHull_eq] at hx
    exact hx.2 (mem_singleton _)
  rintro hx
  suffices h : s \ {x} = convexHull 𝕜 (s \ {x}) by
    rw [h]
    exact convex_convexHull 𝕜 _
  exact
    Subset.antisymm (subset_convexHull 𝕜 _) fun y hy =>
      ⟨convexHull_min sdiff_s

中文:
定理 凸.convex_remove_iff_notMem_convexHull_remove
  条件: {s : 集合 E} (hs : 凸 𝕜 s) (x : E)
  证明: by
  constructor
  · rintro hsx hx
    rw [hsx.convexHull_eq] at hx
    exact hx.2 (mem_singleton _)
  rintro hx
  suffices h : s \ {x} = convexHull 𝕜 (s \ {x}) by
    rw [h]
    exact convex_convexHull 𝕜 _
  exact
    Subset.antisymm (subset_convexHull 𝕜 _) fun y hy =>
      ⟨convexHull_min sdiff_s

Depends on / 依赖: Subset, Subset.antisymm, antisymm, convexHull, convexHull_eq, convexHull_min, convex_convexHull, hsx.convexHull_eq, mem_singleton, sdiff_subset, subset_convexHull
-/
theorem Convex.convex_remove_iff_notMem_convexHull_remove {s : Set E} (hs : Convex 𝕜 s) (x : E) :
    Convex 𝕜 (s \ {x}) ↔ x ∉ convexHull 𝕜 (s \ {x}) := by
  constructor
  · rintro hsx hx
    rw [hsx.convexHull_eq] at hx
    exact hx.2 (mem_singleton _)
  rintro hx
  suffices h : s \ {x} = convexHull 𝕜 (s \ {x}) by
    rw [h]
    exact convex_convexHull 𝕜 _
  exact
    Subset.antisymm (subset_convexHull 𝕜 _) fun y hy =>
      ⟨convexHull_min sdiff_subset hs hy, by
        rintro (rfl : y = x)
        exact hx hy⟩

/--
theorem `IsLinearMap.image_convexHull` / 定理 `IsLinearMap.image_convexHull`

English:
theorem IsLinearMap.image_convexHull
  given: {f : E -> F} (hf : IsLinearMap 𝕜 f) (s : Set E)
  proof: Set.Subset.antisymm
    (image_subset_iff.2 <|
      convexHull_min (image_subset_iff.1 <| subset_convexHull 𝕜 _)
        ((convex_convexHull 𝕜 _).is_linear_preimage hf))
    (convexHull_min (image_mono (subset_convexHull 𝕜 s)) <|
      (convex_convexHull 𝕜 s).is_linear_image hf)

中文:
定理 是线性映射.image_convexHull
  条件: {f : E -> F} (hf : 是线性映射 𝕜 f) (s : 集合 E)
  证明: Set.Subset.antisymm
    (image_subset_iff.2 <|
      convexHull_min (image_subset_iff.1 <| subset_convexHull 𝕜 _)
        ((convex_convexHull 𝕜 _).is_linear_preimage hf))
    (convexHull_min (image_mono (subset_convexHull 𝕜 s)) <|
      (convex_convexHull 𝕜 s).is_linear_image hf)

Depends on / 依赖: Set.Subset.antisymm, Subset, antisymm, convexHull_min, convex_convexHull, image_mono, image_subset_iff, is_linear_image, is_linear_preimage, subset_convexHull
-/
theorem IsLinearMap.image_convexHull {f : E -> F} (hf : IsLinearMap 𝕜 f) (s : Set E) :
    f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s) :=
  Set.Subset.antisymm
    (image_subset_iff.2 <|
      convexHull_min (image_subset_iff.1 <| subset_convexHull 𝕜 _)
        ((convex_convexHull 𝕜 _).is_linear_preimage hf))
    (convexHull_min (image_mono (subset_convexHull 𝕜 s)) <|
      (convex_convexHull 𝕜 s).is_linear_image hf)

/--
theorem `LinearMap.image_convexHull` / 定理 `LinearMap.image_convexHull`

English:
theorem LinearMap.image_convexHull
  given: (f : E ->ₗ[𝕜] F) (s : Set E)
  proof: f.isLinear.image_convexHull s

中文:
定理 线性映射.image_convexHull
  条件: (f : E ->ₗ[𝕜] F) (s : 集合 E)
  证明: f.isLinear.image_convexHull s

Depends on / 依赖: f.isLinear.image_convexHull, image_convexHull, isLinear
-/
theorem LinearMap.image_convexHull (f : E ->ₗ[𝕜] F) (s : Set E) :
    f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s) :=
  f.isLinear.image_convexHull s

/--
theorem `convexHull_add_subset` / 定理 `convexHull_add_subset`

English:
theorem convexHull_add_subset
  given: {s t : Set E}
  proof: convexHull_min (add_subset_add (subset_convexHull _ _) (subset_convexHull _ _))
    (Convex.add (convex_convexHull 𝕜 s) (convex_convexHull 𝕜 t))

中文:
定理 convexHull_add_subset
  条件: {s t : 集合 E}
  证明: convexHull_min (add_subset_add (subset_convexHull _ _) (subset_convexHull _ _))
    (Convex.add (convex_convexHull 𝕜 s) (convex_convexHull 𝕜 t))

Depends on / 依赖: Convex, Convex.add, add_subset_add, convexHull_min, convex_convexHull, subset_convexHull
-/
theorem convexHull_add_subset {s t : Set E} :
    convexHull 𝕜 (s + t) subseteq convexHull 𝕜 s + convexHull 𝕜 t :=
  convexHull_min (add_subset_add (subset_convexHull _ _) (subset_convexHull _ _))
    (Convex.add (convex_convexHull 𝕜 s) (convex_convexHull 𝕜 t))

end AddCommMonoid

end OrderedSemiring

section CommSemiring

variable [CommSemiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]

/--
theorem `convexHull_smul` / 定理 `convexHull_smul`

English:
theorem convexHull_smul
  given: (a : 𝕜) (s : Set E)
  statement: convexHull 𝕜 (a • s) = a • convexHull 𝕜 s
  proof: .symm (LinearMap.lsmul _ _ a).image_convexHull _

中文:
定理 convexHull_smul
  条件: (a : 𝕜) (s : 集合 E)
  结论: convexHull 𝕜 (a • s) = a • convexHull 𝕜 s
  证明: .symm (LinearMap.lsmul _ _ a).image_convexHull _

Depends on / 依赖: LinearMap, LinearMap.lsmul, image_convexHull
-/
theorem convexHull_smul (a : 𝕜) (s : Set E) : convexHull 𝕜 (a • s) = a • convexHull 𝕜 s :=
.symm (LinearMap.lsmul _ _ a).image_convexHull _

end CommSemiring

section OrderedRing

variable [Ring 𝕜] [PartialOrder 𝕜]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]

/--
theorem `AffineMap.image_convexHull` / 定理 `AffineMap.image_convexHull`

English:
theorem AffineMap.image_convexHull
  given: (f : E ->ᵃ[𝕜] F) (s : Set E)
  proof: by
  apply Set.Subset.antisymm
  · rw [Set.image_subset_iff]
    refine convexHull_min ?_ ((convex_convexHull 𝕜 (f '' s)).affine_preimage f)
    rw [← Set.image_subset_iff]
    exact subset_convexHull 𝕜 (f '' s)
  · exact convexHull_min (Set.image_mono (subset_convexHull 𝕜 s))
      ((convex_convexH

中文:
定理 仿射映射.image_convexHull
  条件: (f : E ->ᵃ[𝕜] F) (s : 集合 E)
  证明: by
  apply Set.Subset.antisymm
  · rw [Set.image_subset_iff]
    refine convexHull_min ?_ ((convex_convexHull 𝕜 (f '' s)).affine_preimage f)
    rw [← Set.image_subset_iff]
    exact subset_convexHull 𝕜 (f '' s)
  · exact convexHull_min (Set.image_mono (subset_convexHull 𝕜 s))
      ((convex_convexH

Depends on / 依赖: Set.Subset.antisymm, Set.image_mono, Set.image_subset_iff, Subset, affine_image, affine_preimage, antisymm, convexHull_min, convex_convexHull, image_mono, image_subset_iff, subset_convexHull
-/
theorem AffineMap.image_convexHull (f : E ->ᵃ[𝕜] F) (s : Set E) :
    f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s) := by
  apply Set.Subset.antisymm
  · rw [Set.image_subset_iff]
    refine convexHull_min ?_ ((convex_convexHull 𝕜 (f '' s)).affine_preimage f)
    rw [← Set.image_subset_iff]
    exact subset_convexHull 𝕜 (f '' s)
  · exact convexHull_min (Set.image_mono (subset_convexHull 𝕜 s))
      ((convex_convexHull 𝕜 s).affine_image f)

/--
theorem `convexHull_subset_affineSpan` / 定理 `convexHull_subset_affineSpan`

English:
theorem convexHull_subset_affineSpan
  given: (s : Set E)
  statement: convexHull 𝕜 s subseteq (affineSpan 𝕜 s : Set E)
  proof: convexHull_min (subset_affineSpan 𝕜 s) (affineSpan 𝕜 s).convex

@[simp]

中文:
定理 convexHull_subset_affineSpan
  条件: (s : 集合 E)
  结论: convexHull 𝕜 s subseteq (affineSpan 𝕜 s : 集合 E)
  证明: convexHull_min (subset_affineSpan 𝕜 s) (affineSpan 𝕜 s).convex

@[simp]

Depends on / 依赖: affineSpan, convex, convexHull_min, subset_affineSpan
-/
theorem convexHull_subset_affineSpan (s : Set E) : convexHull 𝕜 s subseteq (affineSpan 𝕜 s : Set E) :=
  convexHull_min (subset_affineSpan 𝕜 s) (affineSpan 𝕜 s).convex

@[simp]
/--
theorem `affineSpan_convexHull` / 定理 `affineSpan_convexHull`

English:
theorem affineSpan_convexHull
  given: (s : Set E)
  statement: affineSpan 𝕜 (convexHull 𝕜 s) = affineSpan 𝕜 s
  proof: by
  refine le_antisymm ?_ (affineSpan_mono 𝕜 (subset_convexHull 𝕜 s))
  rw [affineSpan_le]
  exact convexHull_subset_affineSpan s

中文:
定理 affineSpan_convexHull
  条件: (s : 集合 E)
  结论: affineSpan 𝕜 (convexHull 𝕜 s) = affineSpan 𝕜 s
  证明: by
  refine le_antisymm ?_ (affineSpan_mono 𝕜 (subset_convexHull 𝕜 s))
  rw [affineSpan_le]
  exact convexHull_subset_affineSpan s

Depends on / 依赖: affineSpan_le, affineSpan_mono, convexHull_subset_affineSpan, le_antisymm, subset_convexHull
-/
theorem affineSpan_convexHull (s : Set E) : affineSpan 𝕜 (convexHull 𝕜 s) = affineSpan 𝕜 s := by
  refine le_antisymm ?_ (affineSpan_mono 𝕜 (subset_convexHull 𝕜 s))
  rw [affineSpan_le]
  exact convexHull_subset_affineSpan s

/--
theorem `convexHull_neg` / 定理 `convexHull_neg`

English:
theorem convexHull_neg
  given: (s : Set E)
  statement: convexHull 𝕜 (-s) = -convexHull 𝕜 s
  proof: by
  simp_rw [← image_neg_eq_neg]
.symm exact AffineMap.image_convexHull (-1) _

中文:
定理 convexHull_neg
  条件: (s : 集合 E)
  结论: convexHull 𝕜 (-s) = -convexHull 𝕜 s
  证明: by
  simp_rw [← image_neg_eq_neg]
.symm exact AffineMap.image_convexHull (-1) _

Depends on / 依赖: AffineMap, AffineMap.image_convexHull, image_convexHull, image_neg_eq_neg, simp_rw
-/
theorem convexHull_neg (s : Set E) : convexHull 𝕜 (-s) = -convexHull 𝕜 s := by
  simp_rw [← image_neg_eq_neg]
.symm exact AffineMap.image_convexHull (-1) _

/--
lemma `convexHull_vadd` / 引理 `convexHull_vadd`

English:
lemma convexHull_vadd
  given: (x : E) (s : Set E)
  statement: convexHull 𝕜 (x +ᵥ s) = x +ᵥ convexHull 𝕜 s
  proof: .symm (AffineEquiv.constVAdd 𝕜 _ x).toAffineMap.image_convexHull s

中文:
引理 convexHull_vadd
  条件: (x : E) (s : 集合 E)
  结论: convexHull 𝕜 (x +ᵥ s) = x +ᵥ convexHull 𝕜 s
  证明: .symm (AffineEquiv.constVAdd 𝕜 _ x).toAffineMap.image_convexHull s

Depends on / 依赖: AffineEquiv, AffineEquiv.constVAdd, constVAdd, image_convexHull, toAffineMap, toAffineMap.image_convexHull
-/
lemma convexHull_vadd (x : E) (s : Set E) : convexHull 𝕜 (x +ᵥ s) = x +ᵥ convexHull 𝕜 s :=
.symm (AffineEquiv.constVAdd 𝕜 _ x).toAffineMap.image_convexHull s

end AddCommGroup

end OrderedRing

end convexHull
