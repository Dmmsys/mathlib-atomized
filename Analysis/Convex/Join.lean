/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Hull

/-!
# Convex join

This file defines the convex join of two sets. The convex join of `s` and `t` is the union of the
segments with one end in `s` and the other in `t`. This is notably a useful gadget to deal with
convex hulls of finite sets.
-/

@[expose] public section


open Set

variable {ι : Sort*} {𝕜 E : Type*}

section OrderedSemiring

variable (𝕜) [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]
  {s t s₁ s₂ t₁ t₂ u : Set E}
  {x y : E}

/--
Definition of `convexJoin` / `convexJoin` 的定义

English:
definition convexJoin
  signature: (s t : Set E)
  body: ⋃ (x in s) (y in t), segment 𝕜 x y

中文:
定义 convexJoin
  签名: (s t : 集合 E)
  定义体: ⋃ (x in s) (y in t), segment 𝕜 x y

Depends on / 依赖: segment
-/
def convexJoin (s t : Set E) : Set E :=
  ⋃ (x in s) (y in t), segment 𝕜 x y

variable {𝕜}

/--
theorem `mem_convexJoin` / 定理 `mem_convexJoin`

English:
theorem mem_convexJoin
  statement: x in convexJoin 𝕜 s t ↔ exists a in s, exists b in t, x in segment 𝕜 a b
  proof: by
  simp [convexJoin]

中文:
定理 mem_convexJoin
  结论: x in convexJoin 𝕜 s t ↔ 存在 a in s, 存在 b in t, x in segment 𝕜 a b
  证明: by
  simp [convexJoin]

Depends on / 依赖: convexJoin
-/
theorem mem_convexJoin : x in convexJoin 𝕜 s t ↔ exists a in s, exists b in t, x in segment 𝕜 a b := by
  simp [convexJoin]

/--
theorem `convexJoin_comm` / 定理 `convexJoin_comm`

English:
theorem convexJoin_comm
  given: (s t : Set E)
  statement: convexJoin 𝕜 s t = convexJoin 𝕜 t s
  proof: (iUnion₂_comm _).trans by simp_rw [convexJoin, segment_symm]

中文:
定理 convexJoin_comm
  条件: (s t : 集合 E)
  结论: convexJoin 𝕜 s t = convexJoin 𝕜 t s
  证明: (iUnion₂_comm _).trans by simp_rw [convexJoin, segment_symm]

Depends on / 依赖: convexJoin, segment_symm, simp_rw
-/
theorem convexJoin_comm (s t : Set E) : convexJoin 𝕜 s t = convexJoin 𝕜 t s :=
(iUnion₂_comm _).trans by simp_rw [convexJoin, segment_symm]

/--
theorem `convexJoin_mono` / 定理 `convexJoin_mono`

English:
theorem convexJoin_mono
  given: (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂)
  statement: convexJoin 𝕜 s₁ t₁ subseteq convexJoin 𝕜 s₂ t₂
  proof: biUnion_mono hs fun _ _ => biUnion_subset_biUnion_left ht

中文:
定理 convexJoin_mono
  条件: (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂)
  结论: convexJoin 𝕜 s₁ t₁ subseteq convexJoin 𝕜 s₂ t₂
  证明: biUnion_mono hs fun _ _ => biUnion_subset_biUnion_left ht

Depends on / 依赖: biUnion_mono, biUnion_subset_biUnion_left
-/
theorem convexJoin_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : convexJoin 𝕜 s₁ t₁ subseteq convexJoin 𝕜 s₂ t₂ :=
  biUnion_mono hs fun _ _ => biUnion_subset_biUnion_left ht

/--
theorem `convexJoin_mono_left` / 定理 `convexJoin_mono_left`

English:
theorem convexJoin_mono_left
  given: (hs : s₁ subseteq s₂)
  statement: convexJoin 𝕜 s₁ t subseteq convexJoin 𝕜 s₂ t
  proof: convexJoin_mono hs Subset.rfl

中文:
定理 convexJoin_mono_left
  条件: (hs : s₁ subseteq s₂)
  结论: convexJoin 𝕜 s₁ t subseteq convexJoin 𝕜 s₂ t
  证明: convexJoin_mono hs Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, convexJoin_mono
-/
theorem convexJoin_mono_left (hs : s₁ subseteq s₂) : convexJoin 𝕜 s₁ t subseteq convexJoin 𝕜 s₂ t :=
  convexJoin_mono hs Subset.rfl

/--
theorem `convexJoin_mono_right` / 定理 `convexJoin_mono_right`

English:
theorem convexJoin_mono_right
  given: (ht : t₁ subseteq t₂)
  statement: convexJoin 𝕜 s t₁ subseteq convexJoin 𝕜 s t₂
  proof: convexJoin_mono Subset.rfl ht

@[simp]

中文:
定理 convexJoin_mono_right
  条件: (ht : t₁ subseteq t₂)
  结论: convexJoin 𝕜 s t₁ subseteq convexJoin 𝕜 s t₂
  证明: convexJoin_mono Subset.rfl ht

@[simp]

Depends on / 依赖: Subset, Subset.rfl, convexJoin_mono
-/
theorem convexJoin_mono_right (ht : t₁ subseteq t₂) : convexJoin 𝕜 s t₁ subseteq convexJoin 𝕜 s t₂ :=
  convexJoin_mono Subset.rfl ht

@[simp]
/--
theorem `convexJoin_empty_left` / 定理 `convexJoin_empty_left`

English:
theorem convexJoin_empty_left
  given: (t : Set E)
  statement: convexJoin 𝕜 ∅ t = ∅
  proof: by simp [convexJoin]

@[simp]

中文:
定理 convexJoin_empty_left
  条件: (t : 集合 E)
  结论: convexJoin 𝕜 ∅ t = ∅
  证明: by simp [convexJoin]

@[simp]

Depends on / 依赖: convexJoin
-/
theorem convexJoin_empty_left (t : Set E) : convexJoin 𝕜 ∅ t = ∅ := by simp [convexJoin]

@[simp]
/--
theorem `convexJoin_empty_right` / 定理 `convexJoin_empty_right`

English:
theorem convexJoin_empty_right
  given: (s : Set E)
  statement: convexJoin 𝕜 s ∅ = ∅
  proof: by simp [convexJoin]

@[simp]

中文:
定理 convexJoin_empty_right
  条件: (s : 集合 E)
  结论: convexJoin 𝕜 s ∅ = ∅
  证明: by simp [convexJoin]

@[simp]

Depends on / 依赖: convexJoin
-/
theorem convexJoin_empty_right (s : Set E) : convexJoin 𝕜 s ∅ = ∅ := by simp [convexJoin]

@[simp]
/--
theorem `convexJoin_singleton_left` / 定理 `convexJoin_singleton_left`

English:
theorem convexJoin_singleton_left
  given: (t : Set E) (x : E)
  proof: by simp [convexJoin]

@[simp]

中文:
定理 convexJoin_singleton_left
  条件: (t : 集合 E) (x : E)
  证明: by simp [convexJoin]

@[simp]

Depends on / 依赖: convexJoin
-/
theorem convexJoin_singleton_left (t : Set E) (x : E) :
    convexJoin 𝕜 {x} t = ⋃ y in t, segment 𝕜 x y := by simp [convexJoin]

@[simp]
/--
theorem `convexJoin_singleton_right` / 定理 `convexJoin_singleton_right`

English:
theorem convexJoin_singleton_right
  given: (s : Set E) (y : E)
  proof: by simp [convexJoin]

中文:
定理 convexJoin_singleton_right
  条件: (s : 集合 E) (y : E)
  证明: by simp [convexJoin]

Depends on / 依赖: convexJoin
-/
theorem convexJoin_singleton_right (s : Set E) (y : E) :
    convexJoin 𝕜 s {y} = ⋃ x in s, segment 𝕜 x y := by simp [convexJoin]

/--
theorem `convexJoin_singletons` / 定理 `convexJoin_singletons`

English:
theorem convexJoin_singletons
  given: (x : E)
  statement: convexJoin 𝕜 {x} {y} = segment 𝕜 x y
  proof: by simp

@[simp]

中文:
定理 convexJoin_singletons
  条件: (x : E)
  结论: convexJoin 𝕜 {x} {y} = segment 𝕜 x y
  证明: by simp

@[simp]
-/
theorem convexJoin_singletons (x : E) : convexJoin 𝕜 {x} {y} = segment 𝕜 x y := by simp

@[simp]
/--
theorem `convexJoin_union_left` / 定理 `convexJoin_union_left`

English:
theorem convexJoin_union_left
  given: (s₁ s₂ t : Set E)
  proof: by
  simp_rw [convexJoin, mem_union, iUnion_or, iUnion_union_distrib]

@[simp]

中文:
定理 convexJoin_union_left
  条件: (s₁ s₂ t : 集合 E)
  证明: by
  simp_rw [convexJoin, mem_union, iUnion_or, iUnion_union_distrib]

@[simp]

Depends on / 依赖: convexJoin, iUnion_or, iUnion_union_distrib, mem_union, simp_rw
-/
theorem convexJoin_union_left (s₁ s₂ t : Set E) :
    convexJoin 𝕜 (s₁ union s₂) t = convexJoin 𝕜 s₁ t union convexJoin 𝕜 s₂ t := by
  simp_rw [convexJoin, mem_union, iUnion_or, iUnion_union_distrib]

@[simp]
/--
theorem `convexJoin_union_right` / 定理 `convexJoin_union_right`

English:
theorem convexJoin_union_right
  given: (s t₁ t₂ : Set E)
  proof: by
  simp_rw [convexJoin_comm s, convexJoin_union_left]

@[simp]

中文:
定理 convexJoin_union_right
  条件: (s t₁ t₂ : 集合 E)
  证明: by
  simp_rw [convexJoin_comm s, convexJoin_union_left]

@[simp]

Depends on / 依赖: convexJoin_comm, convexJoin_union_left, simp_rw
-/
theorem convexJoin_union_right (s t₁ t₂ : Set E) :
    convexJoin 𝕜 s (t₁ union t₂) = convexJoin 𝕜 s t₁ union convexJoin 𝕜 s t₂ := by
  simp_rw [convexJoin_comm s, convexJoin_union_left]

@[simp]
/--
theorem `convexJoin_iUnion_left` / 定理 `convexJoin_iUnion_left`

English:
theorem convexJoin_iUnion_left
  given: (s : ι -> Set E) (t : Set E)
  proof: by
  simp_rw [convexJoin, mem_iUnion, iUnion_exists]
  exact iUnion_comm _

@[simp]

中文:
定理 convexJoin_iUnion_left
  条件: (s : ι -> 集合 E) (t : 集合 E)
  证明: by
  simp_rw [convexJoin, mem_iUnion, iUnion_exists]
  exact iUnion_comm _

@[simp]

Depends on / 依赖: convexJoin, iUnion_comm, iUnion_exists, mem_iUnion, simp_rw
-/
theorem convexJoin_iUnion_left (s : ι -> Set E) (t : Set E) :
    convexJoin 𝕜 (⋃ i, s i) t = ⋃ i, convexJoin 𝕜 (s i) t := by
  simp_rw [convexJoin, mem_iUnion, iUnion_exists]
  exact iUnion_comm _

@[simp]
/--
theorem `convexJoin_iUnion_right` / 定理 `convexJoin_iUnion_right`

English:
theorem convexJoin_iUnion_right
  given: (s : Set E) (t : ι -> Set E)
  proof: by
  simp_rw [convexJoin_comm s, convexJoin_iUnion_left]

中文:
定理 convexJoin_iUnion_right
  条件: (s : 集合 E) (t : ι -> 集合 E)
  证明: by
  simp_rw [convexJoin_comm s, convexJoin_iUnion_left]

Depends on / 依赖: convexJoin_comm, convexJoin_iUnion_left, simp_rw
-/
theorem convexJoin_iUnion_right (s : Set E) (t : ι -> Set E) :
    convexJoin 𝕜 s (⋃ i, t i) = ⋃ i, convexJoin 𝕜 s (t i) := by
  simp_rw [convexJoin_comm s, convexJoin_iUnion_left]

/--
theorem `segment_subset_convexJoin` / 定理 `segment_subset_convexJoin`

English:
theorem segment_subset_convexJoin
  given: (hx : x in s) (hy : y in t)
  statement: segment 𝕜 x y subseteq convexJoin 𝕜 s t
  proof: subset_iUnion₂_of_subset x hx subset_iUnion₂ (s := fun y _ => segment 𝕜 x y) y hy

中文:
定理 segment_subset_convexJoin
  条件: (hx : x in s) (hy : y in t)
  结论: segment 𝕜 x y subseteq convexJoin 𝕜 s t
  证明: subset_iUnion₂_of_subset x hx subset_iUnion₂ (s := fun y _ => segment 𝕜 x y) y hy

Depends on / 依赖: segment
-/
theorem segment_subset_convexJoin (hx : x in s) (hy : y in t) : segment 𝕜 x y subseteq convexJoin 𝕜 s t :=
subset_iUnion₂_of_subset x hx subset_iUnion₂ (s := fun y _ => segment 𝕜 x y) y hy

section
variable [IsOrderedRing 𝕜]

/--
theorem `subset_convexJoin_left` / 定理 `subset_convexJoin_left`

English:
theorem subset_convexJoin_left
  given: (h : t.Nonempty)
  statement: s subseteq convexJoin 𝕜 s t
  proof: fun _x hx =>
  let ⟨_y, hy⟩ := h
segment_subset_convexJoin hx hy left_mem_segment _ _ _

中文:
定理 subset_convexJoin_left
  条件: (h : t.非空)
  结论: s subseteq convexJoin 𝕜 s t
  证明: fun _x hx =>
  let ⟨_y, hy⟩ := h
segment_subset_convexJoin hx hy left_mem_segment _ _ _
-/
theorem subset_convexJoin_left (h : t.Nonempty) : s subseteq convexJoin 𝕜 s t := fun _x hx =>
  let ⟨_y, hy⟩ := h
segment_subset_convexJoin hx hy left_mem_segment _ _ _

/--
theorem `subset_convexJoin_right` / 定理 `subset_convexJoin_right`

English:
theorem subset_convexJoin_right
  given: (h : s.Nonempty)
  statement: t subseteq convexJoin 𝕜 s t
  proof: convexJoin_comm (𝕜 := 𝕜) t s ▸ subset_convexJoin_left h

中文:
定理 subset_convexJoin_right
  条件: (h : s.非空)
  结论: t subseteq convexJoin 𝕜 s t
  证明: convexJoin_comm (𝕜 := 𝕜) t s ▸ subset_convexJoin_left h

Depends on / 依赖: convexJoin_comm, subset_convexJoin_left
-/
theorem subset_convexJoin_right (h : s.Nonempty) : t subseteq convexJoin 𝕜 s t :=
  convexJoin_comm (𝕜 := 𝕜) t s ▸ subset_convexJoin_left h

end

/--
theorem `convexJoin_subset` / 定理 `convexJoin_subset`

English:
theorem convexJoin_subset
  given: (hs : s subseteq u) (ht : t subseteq u) (hu : Convex 𝕜 u)
  statement: convexJoin 𝕜 s t subseteq u
  proof: iUnion₂_subset fun _x hx => iUnion₂_subset fun _y hy => hu.segment_subset (hs hx) (ht hy)

中文:
定理 convexJoin_subset
  条件: (hs : s subseteq u) (ht : t subseteq u) (hu : 凸 𝕜 u)
  结论: convexJoin 𝕜 s t subseteq u
  证明: iUnion₂_subset fun _x hx => iUnion₂_subset fun _y hy => hu.segment_subset (hs hx) (ht hy)

Depends on / 依赖: hu.segment_subset, segment_subset
-/
theorem convexJoin_subset (hs : s subseteq u) (ht : t subseteq u) (hu : Convex 𝕜 u) : convexJoin 𝕜 s t subseteq u :=
  iUnion₂_subset fun _x hx => iUnion₂_subset fun _y hy => hu.segment_subset (hs hx) (ht hy)

/--
theorem `convexJoin_subset_convexHull` / 定理 `convexJoin_subset_convexHull`

English:
theorem convexJoin_subset_convexHull
  given: (s t : Set E)
  statement: convexJoin 𝕜 s t subseteq convexHull 𝕜 (s union t)
  proof: convexJoin_subset (subset_union_left.trans <| subset_convexHull _ _)
(subset_union_right.trans <| subset_convexHull _ _)
    convex_convexHull _ _

中文:
定理 convexJoin_subset_convexHull
  条件: (s t : 集合 E)
  结论: convexJoin 𝕜 s t subseteq convexHull 𝕜 (s union t)
  证明: convexJoin_subset (subset_union_left.trans <| subset_convexHull _ _)
(subset_union_right.trans <| subset_convexHull _ _)
    convex_convexHull _ _

Depends on / 依赖: convexJoin_subset, convex_convexHull, subset_convexHull, subset_union_left, subset_union_left.trans, subset_union_right, subset_union_right.trans
-/
theorem convexJoin_subset_convexHull (s t : Set E) : convexJoin 𝕜 s t subseteq convexHull 𝕜 (s union t) :=
  convexJoin_subset (subset_union_left.trans <| subset_convexHull _ _)
(subset_union_right.trans <| subset_convexHull _ _)
    convex_convexHull _ _

end OrderedSemiring

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] {s t : Set E} {x : E}

/--
theorem `convexJoin_assoc_aux` / 定理 `convexJoin_assoc_aux`

English:
theorem convexJoin_assoc_aux
  given: (s t u : Set E)
  proof: by
  simp_rw [subset_def, mem_convexJoin]
  rintro _ ⟨z, ⟨x, hx, y, hy, a₁, b₁, ha₁, hb₁, hab₁, rfl⟩, z, hz, a₂, b₂, ha₂, hb₂, hab₂, rfl⟩
  obtain rfl | hb₂ := hb₂.eq_or_lt
  · refine ⟨x, hx, y, ⟨y, hy, z, hz, left_mem_segment 𝕜 _ _⟩, a₁, b₁, ha₁, hb₁, hab₁, ?_⟩
    linear_combination (norm := module) -hab₂ • (a₁ • x + b₁ • y)
  refine
    ⟨x, hx, (a₂ * b₁ / (a₂ * b₁ + b₂)) • y + (b₂ / (a₂ * b₁ + b₂)) • z,
      ⟨y, hy, z, hz, _, _, by positivity, by positivity, by field, rfl⟩,
      a₂ * a₁, a₂ * b₁ + b₂, by positivity, by positivity, ?_, ?_⟩
  · linear_combination a₂ * hab₁ + hab₂
  · match_scalars <;> field

中文:
定理 convexJoin_assoc_aux
  条件: (s t u : 集合 E)
  证明: by
  simp_rw [subset_def, mem_convexJoin]
  rintro _ ⟨z, ⟨x, hx, y, hy, a₁, b₁, ha₁, hb₁, hab₁, rfl⟩, z, hz, a₂, b₂, ha₂, hb₂, hab₂, rfl⟩
  obtain rfl | hb₂ := hb₂.eq_or_lt
  · refine ⟨x, hx, y, ⟨y, hy, z, hz, left_mem_segment 𝕜 _ _⟩, a₁, b₁, ha₁, hb₁, hab₁, ?_⟩
    linear_combination (norm := module) -hab₂ • (a₁ • x + b₁ • y)
  refine
    ⟨x, hx, (a₂ * b₁ / (a₂ * b₁ + b₂)) • y + (b₂ / (a₂ * b₁ + b₂)) • z,
      ⟨y, hy, z, hz, _, _, by positivity, by positivity, by field, rfl⟩,
      a₂ * a₁, a₂ * b₁ + b₂, by positivity, by positivity, ?_, ?_⟩
  · linear_combination a₂ * hab₁ + hab₂
  · match_scalars <;> field

Depends on / 依赖: eq_or_lt, left_mem_segment, linear_combination, mem_convexJoin, module, simp_rw, subset_def
-/
theorem convexJoin_assoc_aux (s t u : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) u subseteq convexJoin 𝕜 s (convexJoin 𝕜 t u) := by
  simp_rw [subset_def, mem_convexJoin]
  rintro _ ⟨z, ⟨x, hx, y, hy, a₁, b₁, ha₁, hb₁, hab₁, rfl⟩, z, hz, a₂, b₂, ha₂, hb₂, hab₂, rfl⟩
  obtain rfl | hb₂ := hb₂.eq_or_lt
  · refine ⟨x, hx, y, ⟨y, hy, z, hz, left_mem_segment 𝕜 _ _⟩, a₁, b₁, ha₁, hb₁, hab₁, ?_⟩
    linear_combination (norm := module) -hab₂ • (a₁ • x + b₁ • y)
  refine
    ⟨x, hx, (a₂ * b₁ / (a₂ * b₁ + b₂)) • y + (b₂ / (a₂ * b₁ + b₂)) • z,
      ⟨y, hy, z, hz, _, _, by positivity, by positivity, by field, rfl⟩,
      a₂ * a₁, a₂ * b₁ + b₂, by positivity, by positivity, ?_, ?_⟩
  · linear_combination a₂ * hab₁ + hab₂
  · match_scalars <;> field

/--
theorem `convexJoin_assoc` / 定理 `convexJoin_assoc`

English:
theorem convexJoin_assoc
  given: (s t u : Set E)
  proof: by
  refine (convexJoin_assoc_aux _ _ _).antisymm ?_
  simp_rw [convexJoin_comm s, convexJoin_comm _ u]
  exact convexJoin_assoc_aux _ _ _

中文:
定理 convexJoin_assoc
  条件: (s t u : 集合 E)
  证明: by
  refine (convexJoin_assoc_aux _ _ _).antisymm ?_
  simp_rw [convexJoin_comm s, convexJoin_comm _ u]
  exact convexJoin_assoc_aux _ _ _

Depends on / 依赖: antisymm, convexJoin_assoc_aux, convexJoin_comm, simp_rw
-/
theorem convexJoin_assoc (s t u : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) u = convexJoin 𝕜 s (convexJoin 𝕜 t u) := by
  refine (convexJoin_assoc_aux _ _ _).antisymm ?_
  simp_rw [convexJoin_comm s, convexJoin_comm _ u]
  exact convexJoin_assoc_aux _ _ _

/--
theorem `convexJoin_left_comm` / 定理 `convexJoin_left_comm`

English:
theorem convexJoin_left_comm
  given: (s t u : Set E)
  proof: by
  simp_rw [← convexJoin_assoc, convexJoin_comm]

中文:
定理 convexJoin_left_comm
  条件: (s t u : 集合 E)
  证明: by
  simp_rw [← convexJoin_assoc, convexJoin_comm]

Depends on / 依赖: convexJoin_assoc, convexJoin_comm, simp_rw
-/
theorem convexJoin_left_comm (s t u : Set E) :
    convexJoin 𝕜 s (convexJoin 𝕜 t u) = convexJoin 𝕜 t (convexJoin 𝕜 s u) := by
  simp_rw [← convexJoin_assoc, convexJoin_comm]

/--
theorem `convexJoin_right_comm` / 定理 `convexJoin_right_comm`

English:
theorem convexJoin_right_comm
  given: (s t u : Set E)
  proof: by
  simp_rw [convexJoin_assoc, convexJoin_comm]

中文:
定理 convexJoin_right_comm
  条件: (s t u : 集合 E)
  证明: by
  simp_rw [convexJoin_assoc, convexJoin_comm]

Depends on / 依赖: convexJoin_assoc, convexJoin_comm, simp_rw
-/
theorem convexJoin_right_comm (s t u : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) u = convexJoin 𝕜 (convexJoin 𝕜 s u) t := by
  simp_rw [convexJoin_assoc, convexJoin_comm]

/--
theorem `convexJoin_convexJoin_convexJoin_comm` / 定理 `convexJoin_convexJoin_convexJoin_comm`

English:
theorem convexJoin_convexJoin_convexJoin_comm
  given: (s t u v : Set E)
  proof: by
  simp_rw [← convexJoin_assoc, convexJoin_right_comm]

中文:
定理 convexJoin_convexJoin_convexJoin_comm
  条件: (s t u v : 集合 E)
  证明: by
  simp_rw [← convexJoin_assoc, convexJoin_right_comm]

Depends on / 依赖: convexJoin_assoc, convexJoin_right_comm, simp_rw
-/
theorem convexJoin_convexJoin_convexJoin_comm (s t u v : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) (convexJoin 𝕜 u v) =
      convexJoin 𝕜 (convexJoin 𝕜 s u) (convexJoin 𝕜 t v) := by
  simp_rw [← convexJoin_assoc, convexJoin_right_comm]

/--
theorem `Convex.convexJoin` / 定理 `Convex.convexJoin`

English:
theorem Convex.convexJoin
  given: (hs : Convex 𝕜 s) (ht : Convex 𝕜 t)
  proof: by
  simp only [Convex, StarConvex, convexJoin, mem_iUnion]
  rintro _ ⟨x₁, hx₁, y₁, hy₁, a₁, b₁, ha₁, hb₁, hab₁, rfl⟩
    _ ⟨x₂, hx₂, y₂, hy₂, a₂, b₂, ha₂, hb₂, hab₂, rfl⟩ p q hp hq hpq
  rcases hs.exists_mem_add_smul_eq hx₁ hx₂ (mul_nonneg hp ha₁) (mul_nonneg hq ha₂) with ⟨x, hxs, hx⟩
  rcases ht.exists_mem_add_smul_eq hy₁ hy₂ (mul_nonneg hp hb₁) (mul_nonneg hq hb₂) with ⟨y, hyt, hy⟩
  refine ⟨_, hxs, _, hyt, p * a₁ + q * a₂, p * b₁ + q * b₂, ?_, ?_, ?_, ?_⟩ <;> try positivity
  · linear_combination p * hab₁ + q * hab₂ + hpq
  · rw [hx, hy]
    module

中文:
定理 凸.convexJoin
  条件: (hs : 凸 𝕜 s) (ht : 凸 𝕜 t)
  证明: by
  simp only [Convex, StarConvex, convexJoin, mem_iUnion]
  rintro _ ⟨x₁, hx₁, y₁, hy₁, a₁, b₁, ha₁, hb₁, hab₁, rfl⟩
    _ ⟨x₂, hx₂, y₂, hy₂, a₂, b₂, ha₂, hb₂, hab₂, rfl⟩ p q hp hq hpq
  rcases hs.exists_mem_add_smul_eq hx₁ hx₂ (mul_nonneg hp ha₁) (mul_nonneg hq ha₂) with ⟨x, hxs, hx⟩
  rcases ht.exists_mem_add_smul_eq hy₁ hy₂ (mul_nonneg hp hb₁) (mul_nonneg hq hb₂) with ⟨y, hyt, hy⟩
  refine ⟨_, hxs, _, hyt, p * a₁ + q * a₂, p * b₁ + q * b₂, ?_, ?_, ?_, ?_⟩ <;> try positivity
  · linear_combination p * hab₁ + q * hab₂ + hpq
  · rw [hx, hy]
    module
-/
protected theorem Convex.convexJoin (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
    Convex 𝕜 (convexJoin 𝕜 s t) := by
  simp only [Convex, StarConvex, convexJoin, mem_iUnion]
  rintro _ ⟨x₁, hx₁, y₁, hy₁, a₁, b₁, ha₁, hb₁, hab₁, rfl⟩
    _ ⟨x₂, hx₂, y₂, hy₂, a₂, b₂, ha₂, hb₂, hab₂, rfl⟩ p q hp hq hpq
  rcases hs.exists_mem_add_smul_eq hx₁ hx₂ (mul_nonneg hp ha₁) (mul_nonneg hq ha₂) with ⟨x, hxs, hx⟩
  rcases ht.exists_mem_add_smul_eq hy₁ hy₂ (mul_nonneg hp hb₁) (mul_nonneg hq hb₂) with ⟨y, hyt, hy⟩
  refine ⟨_, hxs, _, hyt, p * a₁ + q * a₂, p * b₁ + q * b₂, ?_, ?_, ?_, ?_⟩ <;> try positivity
  · linear_combination p * hab₁ + q * hab₂ + hpq
  · rw [hx, hy]
    module

/--
theorem `Convex.convexHull_union` / 定理 `Convex.convexHull_union`

English:
theorem Convex.convexHull_union
  statement: (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) (hs₀ : s.Nonempty)
  proof: (convexHull_min (union_subset (subset_convexJoin_left ht₀) <| subset_convexJoin_right hs₀) <|
        hs.convexJoin ht).antisymm <|
    convexJoin_subset_convexHull _ _

中文:
定理 凸.convexHull_union
  结论: (hs : 凸 𝕜 s) (ht : 凸 𝕜 t) (hs₀ : s.非空)
  证明: (convexHull_min (union_subset (subset_convexJoin_left ht₀) <| subset_convexJoin_right hs₀) <|
        hs.convexJoin ht).antisymm <|
    convexJoin_subset_convexHull _ _
-/
protected theorem Convex.convexHull_union (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) (hs₀ : s.Nonempty)
    (ht₀ : t.Nonempty) : convexHull 𝕜 (s union t) = convexJoin 𝕜 s t :=
  (convexHull_min (union_subset (subset_convexJoin_left ht₀) <| subset_convexJoin_right hs₀) <|
        hs.convexJoin ht).antisymm <|
    convexJoin_subset_convexHull _ _

/--
theorem `convexHull_union` / 定理 `convexHull_union`

English:
theorem convexHull_union
  given: (hs : s.Nonempty) (ht : t.Nonempty)
  proof: by
  rw [← convexHull_convexHull_union_left]; rw [← convexHull_convexHull_union_right]
  exact (convex_convexHull 𝕜 s).convexHull_union (convex_convexHull 𝕜 t) hs.convexHull ht.convexHull

中文:
定理 convexHull_union
  条件: (hs : s.非空) (ht : t.非空)
  证明: by
  rw [← convexHull_convexHull_union_left]; rw [← convexHull_convexHull_union_right]
  exact (convex_convexHull 𝕜 s).convexHull_union (convex_convexHull 𝕜 t) hs.convexHull ht.convexHull

Depends on / 依赖: convexHull, convexHull_convexHull_union_left, convexHull_convexHull_union_right, convexHull_union, convex_convexHull, hs.convexHull, ht.convexHull
-/
theorem convexHull_union (hs : s.Nonempty) (ht : t.Nonempty) :
    convexHull 𝕜 (s union t) = convexJoin 𝕜 (convexHull 𝕜 s) (convexHull 𝕜 t) := by
  rw [← convexHull_convexHull_union_left]; rw [← convexHull_convexHull_union_right]
  exact (convex_convexHull 𝕜 s).convexHull_union (convex_convexHull 𝕜 t) hs.convexHull ht.convexHull

/--
theorem `convexHull_insert` / 定理 `convexHull_insert`

English:
theorem convexHull_insert
  given: (hs : s.Nonempty)
  proof: by
  rw [insert_eq]; rw [convexHull_union (singleton_nonempty _) hs]; rw [convexHull_singleton]

中文:
定理 convexHull_insert
  条件: (hs : s.非空)
  证明: by
  rw [insert_eq]; rw [convexHull_union (singleton_nonempty _) hs]; rw [convexHull_singleton]

Depends on / 依赖: convexHull_singleton, convexHull_union, insert_eq, singleton_nonempty
-/
theorem convexHull_insert (hs : s.Nonempty) :
    convexHull 𝕜 (insert x s) = convexJoin 𝕜 {x} (convexHull 𝕜 s) := by
  rw [insert_eq]; rw [convexHull_union (singleton_nonempty _) hs]; rw [convexHull_singleton]

/--
theorem `convexJoin_segments` / 定理 `convexJoin_segments`

English:
theorem convexJoin_segments
  given: (a b c d : E)
  proof: by
  simp_rw [← convexHull_pair, convexHull_insert (insert_nonempty _ _),
    convexHull_insert (singleton_nonempty _), convexJoin_assoc,
    convexHull_singleton]

中文:
定理 convexJoin_segments
  条件: (a b c d : E)
  证明: by
  simp_rw [← convexHull_pair, convexHull_insert (insert_nonempty _ _),
    convexHull_insert (singleton_nonempty _), convexJoin_assoc,
    convexHull_singleton]

Depends on / 依赖: convexHull_insert, convexHull_pair, convexHull_singleton, convexJoin_assoc, insert_nonempty, simp_rw, singleton_nonempty
-/
theorem convexJoin_segments (a b c d : E) :
    convexJoin 𝕜 (segment 𝕜 a b) (segment 𝕜 c d) = convexHull 𝕜 {a, b, c, d} := by
  simp_rw [← convexHull_pair, convexHull_insert (insert_nonempty _ _),
    convexHull_insert (singleton_nonempty _), convexJoin_assoc,
    convexHull_singleton]

/--
theorem `convexJoin_segment_singleton` / 定理 `convexJoin_segment_singleton`

English:
theorem convexJoin_segment_singleton
  given: (a b c : E)
  proof: by
  rw [← pair_eq_singleton]; rw [← convexJoin_segments]; rw [segment_same]; rw [pair_eq_singleton]

中文:
定理 convexJoin_segment_singleton
  条件: (a b c : E)
  证明: by
  rw [← pair_eq_singleton]; rw [← convexJoin_segments]; rw [segment_same]; rw [pair_eq_singleton]

Depends on / 依赖: convexJoin_segments, pair_eq_singleton, segment_same
-/
theorem convexJoin_segment_singleton (a b c : E) :
    convexJoin 𝕜 (segment 𝕜 a b) {c} = convexHull 𝕜 {a, b, c} := by
  rw [← pair_eq_singleton]; rw [← convexJoin_segments]; rw [segment_same]; rw [pair_eq_singleton]

/--
theorem `convexJoin_singleton_segment` / 定理 `convexJoin_singleton_segment`

English:
theorem convexJoin_singleton_segment
  given: (a b c : E)
  proof: by
  rw [← segment_same 𝕜]; rw [convexJoin_segments]; rw [insert_idem]

中文:
定理 convexJoin_singleton_segment
  条件: (a b c : E)
  证明: by
  rw [← segment_same 𝕜]; rw [convexJoin_segments]; rw [insert_idem]

Depends on / 依赖: convexJoin_segments, insert_idem, segment_same
-/
theorem convexJoin_singleton_segment (a b c : E) :
    convexJoin 𝕜 {a} (segment 𝕜 b c) = convexHull 𝕜 {a, b, c} := by
  rw [← segment_same 𝕜]; rw [convexJoin_segments]; rw [insert_idem]

end LinearOrderedField
