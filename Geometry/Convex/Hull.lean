/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.Set
public import Mathlib.Order.Closure

/-!
# Convex hull

This file defines the convex hull of a set in a convex space. `convexHull R s` is the smallest
convex set containing `s`. In order theory speak, this is a closure operator.
-/

public section

open Set

namespace Convexity
variable {R X Y : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]
  [ConvexSpace R Y] {C s t : Set X} {x y : X}

variable (R) in
/--
Definition of `convexHull` / `convexHull` 的定义

English:
definition convexHull
  signature: : ClosureOperator (Set X)
  body: .ofCompletePred (IsConvexSet R) (fun _ => .sInter)

中文:
定义 convexHull
  签名: : ClosureOperator (Set X)
  定义体: .ofCompletePred (IsConvexSet R) (fun _ => .sInter)

Depends on / 依赖: IsConvexSet, ofCompletePred, sInter
-/
def convexHull : ClosureOperator (Set X) :=
  .ofCompletePred (IsConvexSet R) (fun _ => .sInter)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `subset_convexHull_iff` / 引理 `subset_convexHull_iff`

English:
lemma subset_convexHull_iff
  statement: t subseteq convexHull R s ↔ forall C, s subseteq C -> IsConvexSet R C -> t subseteq C
  proof: by
  simp [convexHull, iInter_subtype, iInter_and]

中文:
引理 subset_convexHull_iff
  结论: t subseteq convexHull R s ↔ 对任意 C, s subseteq C -> IsConvexSet R C -> t subseteq C
  证明: by
  simp [convexHull, iInter_subtype, iInter_and]

Depends on / 依赖: convexHull, iInter_and, iInter_subtype
-/
lemma subset_convexHull_iff : t subseteq convexHull R s ↔ forall C, s subseteq C -> IsConvexSet R C -> t subseteq C := by
  simp [convexHull, iInter_subtype, iInter_and]

/--
lemma `subset_convexHull_self` / 引理 `subset_convexHull_self`

English:
lemma subset_convexHull_self
  statement: s subseteq convexHull R s
  proof: ClosureOperator.le_closure _ s

中文:
引理 subset_convexHull_self
  结论: s subseteq convexHull R s
  证明: ClosureOperator.le_closure _ s
-/
@[simp] lemma subset_convexHull_self : s subseteq convexHull R s := ClosureOperator.le_closure _ s

/--
lemma `IsConvexSet.convexHull` / 引理 `IsConvexSet.convexHull`

English:
lemma IsConvexSet.convexHull
  statement: IsConvexSet R (convexHull R s)
  proof: ClosureOperator.isClosed_closure (.ofCompletePred (IsConvexSet R) _) s

中文:
引理 IsConvexSet.convexHull
  结论: IsConvexSet R (convexHull R s)
  证明: ClosureOperator.isClosed_closure (.ofCompletePred (IsConvexSet R) _) s
-/
protected lemma IsConvexSet.convexHull : IsConvexSet R (convexHull R s) :=
  ClosureOperator.isClosed_closure (.ofCompletePred (IsConvexSet R) _) s

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `convexHull_eq_iInter` / 引理 `convexHull_eq_iInter`

English:
lemma convexHull_eq_iInter
  proof: by
  simp [convexHull, iInter_subtype, iInter_and]

中文:
引理 convexHull_eq_iInter
  证明: by
  simp [convexHull, iInter_subtype, iInter_and]

Depends on / 依赖: convexHull, iInter_and, iInter_subtype
-/
lemma convexHull_eq_iInter :
    convexHull R s = ⋂ (t : Set X) (_ : s subseteq t) (_ : IsConvexSet R t), t := by
  simp [convexHull, iInter_subtype, iInter_and]

/--
lemma `mem_convexHull_iff` / 引理 `mem_convexHull_iff`

English:
lemma mem_convexHull_iff
  statement: x in convexHull R s ↔ forall t, s subseteq t -> IsConvexSet R t -> x in t
  proof: by
  simp_rw [convexHull_eq_iInter, mem_iInter]

中文:
引理 mem_convexHull_iff
  结论: x in convexHull R s ↔ 对任意 t, s subseteq t -> IsConvexSet R t -> x in t
  证明: by
  simp_rw [convexHull_eq_iInter, mem_iInter]

Depends on / 依赖: convexHull_eq_iInter, mem_iInter, simp_rw
-/
lemma mem_convexHull_iff : x in convexHull R s ↔ forall t, s subseteq t -> IsConvexSet R t -> x in t := by
  simp_rw [convexHull_eq_iInter, mem_iInter]

/--
lemma `convexHull_min` / 引理 `convexHull_min`

English:
lemma convexHull_min
  statement: s subseteq C -> IsConvexSet R C -> convexHull R s subseteq C
  proof: (ClosureOperator.ofCompletePred (IsConvexSet R) _).closure_min

中文:
引理 convexHull_min
  结论: s subseteq C -> IsConvexSet R C -> convexHull R s subseteq C
  证明: (ClosureOperator.ofCompletePred (IsConvexSet R) _).closure_min

Depends on / 依赖: ClosureOperator, ClosureOperator.ofCompletePred, IsConvexSet, closure_min, ofCompletePred
-/
lemma convexHull_min : s subseteq C -> IsConvexSet R C -> convexHull R s subseteq C :=
  (ClosureOperator.ofCompletePred (IsConvexSet R) _).closure_min

/--
lemma `IsConvexSet.convexHull_subset_iff` / 引理 `IsConvexSet.convexHull_subset_iff`

English:
lemma IsConvexSet.convexHull_subset_iff
  given: (hC : IsConvexSet R C)
  statement: convexHull R s subseteq C ↔ s subseteq C
  proof: ClosureOperator.IsClosed.closure_le_iff hC

@[gcongr]

中文:
引理 IsConvexSet.convexHull_subset_iff
  条件: (hC : IsConvexSet R C)
  结论: convexHull R s subseteq C ↔ s subseteq C
  证明: ClosureOperator.IsClosed.closure_le_iff hC

@[gcongr]

Depends on / 依赖: ClosureOperator, ClosureOperator.IsClosed.closure_le_iff, IsClosed, closure_le_iff
-/
lemma IsConvexSet.convexHull_subset_iff (hC : IsConvexSet R C) : convexHull R s subseteq C ↔ s subseteq C :=
  ClosureOperator.IsClosed.closure_le_iff hC

@[gcongr]
/--
lemma `convexHull_mono` / 引理 `convexHull_mono`

English:
lemma convexHull_mono
  given: (hst : s subseteq t)
  statement: convexHull R s subseteq convexHull R t
  proof: ClosureOperator.monotone _ hst

中文:
引理 convexHull_mono
  条件: (hst : s subseteq t)
  结论: convexHull R s subseteq convexHull R t
  证明: ClosureOperator.monotone _ hst

Depends on / 依赖: ClosureOperator, ClosureOperator.monotone, monotone
-/
lemma convexHull_mono (hst : s subseteq t) : convexHull R s subseteq convexHull R t :=
  ClosureOperator.monotone _ hst

/--
lemma `convexHull_eq_self` / 引理 `convexHull_eq_self`

English:
lemma convexHull_eq_self
  statement: convexHull R C = C ↔ IsConvexSet R C
  proof: (ClosureOperator.isClosed_iff _).symm

中文:
引理 convexHull_eq_self
  结论: convexHull R C = C ↔ IsConvexSet R C
  证明: (ClosureOperator.isClosed_iff _).symm

Depends on / 依赖: ClosureOperator, ClosureOperator.isClosed_iff, isClosed_iff
-/
lemma convexHull_eq_self : convexHull R C = C ↔ IsConvexSet R C :=
  (ClosureOperator.isClosed_iff _).symm

/--
lemma `convexHull_subset_self` / 引理 `convexHull_subset_self`

English:
lemma convexHull_subset_self
  statement: convexHull R C subseteq C ↔ IsConvexSet R C
  proof: by
  simp [← convexHull_eq_self, subset_antisymm_iff]

protected alias ⟨_, IsConvexSet.convexHull_eq_self⟩ := convexHull_eq_self

中文:
引理 convexHull_subset_self
  结论: convexHull R C subseteq C ↔ IsConvexSet R C
  证明: by
  simp [← convexHull_eq_self, subset_antisymm_iff]

protected alias ⟨_, IsConvexSet.convexHull_eq_self⟩ := convexHull_eq_self

Depends on / 依赖: convexHull_eq_self, subset_antisymm_iff
-/
lemma convexHull_subset_self : convexHull R C subseteq C ↔ IsConvexSet R C := by
  simp [← convexHull_eq_self, subset_antisymm_iff]

protected alias ⟨_, IsConvexSet.convexHull_eq_self⟩ := convexHull_eq_self

variable (R) in
/--
lemma `convexHull_empty` / 引理 `convexHull_empty`

English:
lemma convexHull_empty
  statement: convexHull R (∅ : Set X) = ∅
  proof: IsConvexSet.empty.convexHull_eq_self

中文:
引理 convexHull_empty
  结论: convexHull R (∅ : Set X) = ∅
  证明: IsConvexSet.empty.convexHull_eq_self
-/
@[simp] lemma convexHull_empty : convexHull R (∅ : Set X) = ∅ :=
  IsConvexSet.empty.convexHull_eq_self

/--
lemma `convexHull_eq_empty` / 引理 `convexHull_eq_empty`

English:
lemma convexHull_eq_empty
  statement: convexHull R s = ∅ ↔ s = ∅
  proof: by
  simp [← subset_empty_iff, IsConvexSet.empty.convexHull_subset_iff]

中文:
引理 convexHull_eq_empty
  结论: convexHull R s = ∅ ↔ s = ∅
  证明: by
  simp [← subset_empty_iff, IsConvexSet.empty.convexHull_subset_iff]
-/
@[simp] lemma convexHull_eq_empty : convexHull R s = ∅ ↔ s = ∅ := by
  simp [← subset_empty_iff, IsConvexSet.empty.convexHull_subset_iff]

/--
lemma `convexHull_nonempty` / 引理 `convexHull_nonempty`

English:
lemma convexHull_nonempty
  statement: (convexHull R s).Nonempty ↔ s.Nonempty
  proof: by
  simp [nonempty_iff_ne_empty]

protected alias ⟨_, Set.Nonempty.convexHull'⟩ := convexHull_nonempty

中文:
引理 convexHull_nonempty
  结论: (convexHull R s).Nonempty ↔ s.Nonempty
  证明: by
  simp [nonempty_iff_ne_empty]

protected alias ⟨_, Set.Nonempty.convexHull'⟩ := convexHull_nonempty
-/
@[simp] lemma convexHull_nonempty : (convexHull R s).Nonempty ↔ s.Nonempty := by
  simp [nonempty_iff_ne_empty]

protected alias ⟨_, Set.Nonempty.convexHull'⟩ := convexHull_nonempty

variable (R x) in
/--
lemma `convexHull_singleton` / 引理 `convexHull_singleton`

English:
lemma convexHull_singleton
  statement: convexHull R {x} = {x}
  proof: IsConvexSet.singleton.convexHull_eq_self

中文:
引理 convexHull_singleton
  结论: convexHull R {x} = {x}
  证明: IsConvexSet.singleton.convexHull_eq_self
-/
@[simp] lemma convexHull_singleton : convexHull R {x} = {x} :=
  IsConvexSet.singleton.convexHull_eq_self

/--
lemma `convexHull_univ` / 引理 `convexHull_univ`

English:
lemma convexHull_univ
  statement: convexHull R (univ : Set X) = univ
  proof: IsConvexSet.univ.convexHull_eq_self

中文:
引理 convexHull_univ
  结论: convexHull R (univ : Set X) = univ
  证明: IsConvexSet.univ.convexHull_eq_self
-/
@[simp] lemma convexHull_univ : convexHull R (univ : Set X) = univ :=
  IsConvexSet.univ.convexHull_eq_self

/--
lemma `convexHull_eq_singleton` / 引理 `convexHull_eq_singleton`

English:
lemma convexHull_eq_singleton
  statement: convexHull R s = {x} ↔ s = {x} where
  proof: by
    rw [← Set.Nonempty.subset_singleton_iff]; rw [← hs]
    · exact subset_convexHull_self
    · by_contra! hs
      simp_all [eq_comm (a := ∅)]
  mpr hs := by simp [hs]

中文:
引理 convexHull_eq_singleton
  结论: convexHull R s = {x} ↔ s = {x} where
  证明: by
    rw [← Set.Nonempty.subset_singleton_iff]; rw [← hs]
    · exact subset_convexHull_self
    · by_contra! hs
      simp_all [eq_comm (a := ∅)]
  mpr hs := by simp [hs]
-/
@[simp] lemma convexHull_eq_singleton : convexHull R s = {x} ↔ s = {x} where
  mp hs := by
    rw [← Set.Nonempty.subset_singleton_iff]; rw [← hs]
    · exact subset_convexHull_self
    · by_contra! hs
      simp_all [eq_comm (a := ∅)]
  mpr hs := by simp [hs]

variable (R s t) in
@[simp]
/--
lemma `convexHull_convexHull_union` / 引理 `convexHull_convexHull_union`

English:
lemma convexHull_convexHull_union
  proof: ClosureOperator.closure_sup_closure_left ..

中文:
引理 convexHull_convexHull_union
  证明: ClosureOperator.closure_sup_closure_left ..

Depends on / 依赖: ClosureOperator, ClosureOperator.closure_sup_closure_left, closure_sup_closure_left
-/
lemma convexHull_convexHull_union :
    convexHull R (convexHull R s union t) = convexHull R (s union t) :=
  ClosureOperator.closure_sup_closure_left ..

variable (R s t) in
@[simp]
/--
lemma `convexHull_union_convexHull` / 引理 `convexHull_union_convexHull`

English:
lemma convexHull_union_convexHull
  proof: ClosureOperator.closure_sup_closure_right ..

中文:
引理 convexHull_union_convexHull
  证明: ClosureOperator.closure_sup_closure_right ..

Depends on / 依赖: ClosureOperator, ClosureOperator.closure_sup_closure_right, closure_sup_closure_right
-/
lemma convexHull_union_convexHull :
    convexHull R (s union convexHull R t) = convexHull R (s union t) :=
  ClosureOperator.closure_sup_closure_right ..

/--
lemma `IsConvexSet.sdiff_singleton_iff_notMem_convexHull` / 引理 `IsConvexSet.sdiff_singleton_iff_notMem_convexHull`

English:
lemma IsConvexSet.sdiff_singleton_iff_notMem_convexHull
  given: (hs : IsConvexSet R s)
  proof: by
    rw [hsx.convexHull_eq_self] at hx
    exact hx.2 (mem_singleton _)
  mpr hx := by
    rw [← convexHull_subset_self]
    rintro y hy
    exact ⟨convexHull_min sdiff_subset hs hy, by rintro rfl; exact hx hy⟩

中文:
引理 IsConvexSet.sdiff_singleton_iff_notMem_convexHull
  条件: (hs : IsConvexSet R s)
  证明: by
    rw [hsx.convexHull_eq_self] at hx
    exact hx.2 (mem_singleton _)
  mpr hx := by
    rw [← convexHull_subset_self]
    rintro y hy
    exact ⟨convexHull_min sdiff_subset hs hy, by rintro rfl; exact hx hy⟩

Depends on / 依赖: convexHull_eq_self, convexHull_min, convexHull_subset_self, hsx.convexHull_eq_self, mem_singleton, sdiff_subset
-/
lemma IsConvexSet.sdiff_singleton_iff_notMem_convexHull (hs : IsConvexSet R s) :
    IsConvexSet R (s \ {x}) ↔ x ∉ convexHull R (s \ {x}) where
  mp hsx hx := by
    rw [hsx.convexHull_eq_self] at hx
    exact hx.2 (mem_singleton _)
  mpr hx := by
    rw [← convexHull_subset_self]
    rintro y hy
    exact ⟨convexHull_min sdiff_subset hs hy, by rintro rfl; exact hx hy⟩

/--
lemma `IsAffineMap.image_convexHull` / 引理 `IsAffineMap.image_convexHull`

English:
lemma IsAffineMap.image_convexHull
  given: {f : X -> Y} (hf : IsAffineMap R f) (s : Set X)
  proof: by
  rw [subset_antisymm_iff]; rw [image_subset_iff]; rw [(IsConvexSet.convexHull.preimage hf).convexHull_subset_iff]; rw [← image_subset_iff]; rw [(IsConvexSet.convexHull.image hf).convexHull_subset_iff]
  exact ⟨subset_convexHull_self, image_mono subset_convexHull_self⟩

中文:
引理 IsAffineMap.image_convexHull
  条件: {f : X -> Y} (hf : IsAffineMap R f) (s : Set X)
  证明: by
  rw [subset_antisymm_iff]; rw [image_subset_iff]; rw [(IsConvexSet.convexHull.preimage hf).convexHull_subset_iff]; rw [← image_subset_iff]; rw [(IsConvexSet.convexHull.image hf).convexHull_subset_iff]
  exact ⟨subset_convexHull_self, image_mono subset_convexHull_self⟩

Depends on / 依赖: IsConvexSet, IsConvexSet.convexHull.image, IsConvexSet.convexHull.preimage, convexHull, convexHull_subset_iff, image_mono, image_subset_iff, preimage, subset_antisymm_iff, subset_convexHull_self
-/
lemma IsAffineMap.image_convexHull {f : X -> Y} (hf : IsAffineMap R f) (s : Set X) :
    f '' convexHull R s = convexHull R (f '' s) := by
  rw [subset_antisymm_iff]; rw [image_subset_iff]; rw [(IsConvexSet.convexHull.preimage hf).convexHull_subset_iff]; rw [← image_subset_iff]; rw [(IsConvexSet.convexHull.image hf).convexHull_subset_iff]
  exact ⟨subset_convexHull_self, image_mono subset_convexHull_self⟩

end Convexity
