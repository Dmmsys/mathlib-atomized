/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Ring.Action.Pointwise.Set
public import Mathlib.Analysis.Convex.Star
public import Mathlib.Tactic.Field
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.Tactic.NoncommRing

/-!
# Convex sets

In a 𝕜-vector space, we define the following property:
* `Convex 𝕜 s`: A set `s` is convex if for any two points `x y ∈ s` it includes `segment 𝕜 x y`.

We provide various equivalent versions, and prove that some specific sets are convex.

## TODO

Generalize all this file to affine spaces.
-/

@[expose] public section


variable {𝕜 E F β : Type*}

open LinearMap Set

open scoped Convex Pointwise

/-! ### Convexity of sets -/


section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section SMul

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 F] (s : Set E) {x : E}

/--
Definition of `Convex` / `Convex` 的定义

English:
definition Convex
  signature: : Prop
  body: forall ⦃x : E⦄, x in s -> StarConvex 𝕜 x s

中文:
定义 Convex
  签名: : 命题
  定义体: forall ⦃x : E⦄, x in s -> StarConvex 𝕜 x s

Depends on / 依赖: StarConvex
-/
def Convex : Prop :=
  forall ⦃x : E⦄, x in s -> StarConvex 𝕜 x s

variable {𝕜 s}

/--
theorem `Convex.starConvex` / 定理 `Convex.starConvex`

English:
theorem Convex.starConvex
  given: (hs : Convex 𝕜 s) (hx : x in s)
  statement: StarConvex 𝕜 x s
  proof: hs hx

中文:
定理 Convex.starConvex
  条件: (hs : Convex 𝕜 s) (hx : x in s)
  结论: StarConvex 𝕜 x s
  证明: hs hx
-/
theorem Convex.starConvex (hs : Convex 𝕜 s) (hx : x in s) : StarConvex 𝕜 x s :=
  hs hx

/--
theorem `convex_iff_segment_subset` / 定理 `convex_iff_segment_subset`

English:
theorem convex_iff_segment_subset
  statement: Convex 𝕜 s ↔ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> [x -[𝕜] y] subseteq s
  proof: forall₂_congr fun _ _ => starConvex_iff_segment_subset

中文:
定理 convex_iff_segment_subset
  结论: Convex 𝕜 s ↔ 对任意 ⦃x⦄, x in s -> 对任意 ⦃y⦄, y in s -> [x -[𝕜] y] subseteq s
  证明: forall₂_congr fun _ _ => starConvex_iff_segment_subset

Depends on / 依赖: starConvex_iff_segment_subset
-/
theorem convex_iff_segment_subset : Convex 𝕜 s ↔ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> [x -[𝕜] y] subseteq s :=
  forall₂_congr fun _ _ => starConvex_iff_segment_subset

/--
theorem `Convex.segment_subset` / 定理 `Convex.segment_subset`

English:
theorem Convex.segment_subset
  given: (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in s)
  proof: convex_iff_segment_subset.1 h hx hy

中文:
定理 Convex.segment_subset
  条件: (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in s)
  证明: convex_iff_segment_subset.1 h hx hy

Depends on / 依赖: convex_iff_segment_subset
-/
theorem Convex.segment_subset (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in s) :
    [x -[𝕜] y] subseteq s :=
  convex_iff_segment_subset.1 h hx hy

/--
theorem `Convex.openSegment_subset` / 定理 `Convex.openSegment_subset`

English:
theorem Convex.openSegment_subset
  given: (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in s)
  proof: (openSegment_subset_segment 𝕜 x y).trans (h.segment_subset hx hy)

中文:
定理 Convex.openSegment_subset
  条件: (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in s)
  证明: (openSegment_subset_segment 𝕜 x y).trans (h.segment_subset hx hy)

Depends on / 依赖: h.segment_subset, openSegment_subset_segment, segment_subset
-/
theorem Convex.openSegment_subset (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in s) :
    openSegment 𝕜 x y subseteq s :=
  (openSegment_subset_segment 𝕜 x y).trans (h.segment_subset hx hy)

/--
theorem `convex_iff_add_mem` / 定理 `convex_iff_add_mem`

English:
theorem convex_iff_add_mem
  statement: Convex 𝕜 s ↔
  proof: by
  simp_rw [convex_iff_segment_subset, segment_subset_iff]

中文:
定理 convex_iff_add_mem
  结论: Convex 𝕜 s ↔
  证明: by
  simp_rw [convex_iff_segment_subset, segment_subset_iff]

Depends on / 依赖: convex_iff_segment_subset, segment_subset_iff, simp_rw
-/
theorem convex_iff_add_mem : Convex 𝕜 s ↔
    forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 -> a • x + b • y in s := by
  simp_rw [convex_iff_segment_subset, segment_subset_iff]

/--
theorem `convex_iff_pointwise_add_subset` / 定理 `convex_iff_pointwise_add_subset`

English:
theorem convex_iff_pointwise_add_subset
  proof: Iff.intro
    (by
      rintro hA a b ha hb hab w ⟨au, ⟨u, hu, rfl⟩, bv, ⟨v, hv, rfl⟩, rfl⟩
      exact hA hu hv ha hb hab)
    fun h _ hx _ hy _ _ ha hb hab => (h ha hb hab) (Set.add_mem_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩)

alias ⟨Convex.set_combo_subset, _⟩ := convex_iff_pointwise_add_subset

中文:
定理 convex_iff_pointwise_add_subset
  证明: Iff.intro
    (by
      rintro hA a b ha hb hab w ⟨au, ⟨u, hu, rfl⟩, bv, ⟨v, hv, rfl⟩, rfl⟩
      exact hA hu hv ha hb hab)
    fun h _ hx _ hy _ _ ha hb hab => (h ha hb hab) (Set.add_mem_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩)

alias ⟨Convex.set_combo_subset, _⟩ := convex_iff_pointwise_add_subset

Depends on / 依赖: Iff.intro, Set.add_mem_add, add_mem_add
-/
theorem convex_iff_pointwise_add_subset :
    Convex 𝕜 s ↔ forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 -> a • s + b • s subseteq s :=
  Iff.intro
    (by
      rintro hA a b ha hb hab w ⟨au, ⟨u, hu, rfl⟩, bv, ⟨v, hv, rfl⟩, rfl⟩
      exact hA hu hv ha hb hab)
    fun h _ hx _ hy _ _ ha hb hab => (h ha hb hab) (Set.add_mem_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩)

alias ⟨Convex.set_combo_subset, _⟩ := convex_iff_pointwise_add_subset

/--
theorem `convex_empty` / 定理 `convex_empty`

English:
theorem convex_empty
  statement: Convex 𝕜 (∅ : Set E)
  proof: fun _ => False.elim

中文:
定理 convex_empty
  结论: Convex 𝕜 (∅ : Set E)
  证明: fun _ => False.elim

Depends on / 依赖: False.elim
-/
theorem convex_empty : Convex 𝕜 (∅ : Set E) := fun _ => False.elim

/--
theorem `convex_univ` / 定理 `convex_univ`

English:
theorem convex_univ
  statement: Convex 𝕜 (Set.univ : Set E)
  proof: fun _ _ => starConvex_univ _

中文:
定理 convex_univ
  结论: Convex 𝕜 (Set.univ : Set E)
  证明: fun _ _ => starConvex_univ _

Depends on / 依赖: starConvex_univ
-/
theorem convex_univ : Convex 𝕜 (Set.univ : Set E) := fun _ _ => starConvex_univ _

/--
theorem `Convex.inter` / 定理 `Convex.inter`

English:
theorem Convex.inter
  given: {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t)
  statement: Convex 𝕜 (s inter t)
  proof: fun _ hx => (hs hx.1).inter (ht hx.2)

中文:
定理 Convex.inter
  条件: {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t)
  结论: Convex 𝕜 (s inter t)
  证明: fun _ hx => (hs hx.1).inter (ht hx.2)
-/
theorem Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s inter t) :=
  fun _ hx => (hs hx.1).inter (ht hx.2)

/--
theorem `convex_sInter` / 定理 `convex_sInter`

English:
theorem convex_sInter
  given: {S : Set (Set E)} (h : forall s in S, Convex 𝕜 s)
  statement: Convex 𝕜 (⋂₀ S)
  proof: fun _ hx =>
starConvex_sInter fun _ hs => h _ hs hx _ hs

中文:
定理 convex_sInter
  条件: {S : Set (Set E)} (h : 对任意 s in S, Convex 𝕜 s)
  结论: Convex 𝕜 (⋂₀ S)
  证明: fun _ hx =>
starConvex_sInter fun _ hs => h _ hs hx _ hs
-/
theorem convex_sInter {S : Set (Set E)} (h : forall s in S, Convex 𝕜 s) : Convex 𝕜 (⋂₀ S) := fun _ hx =>
starConvex_sInter fun _ hs => h _ hs hx _ hs

/--
theorem `convex_iInter` / 定理 `convex_iInter`

English:
theorem convex_iInter
  given: {ι : Sort*} {s : ι -> Set E} (h : forall i, Convex 𝕜 (s i))
  proof: sInter_range s ▸ convex_sInter forall_mem_range.2 h

中文:
定理 convex_iInter
  条件: {ι : Sort*} {s : ι -> Set E} (h : 对任意 i, Convex 𝕜 (s i))
  证明: sInter_range s ▸ convex_sInter forall_mem_range.2 h

Depends on / 依赖: convex_sInter, forall_mem_range, sInter_range
-/
theorem convex_iInter {ι : Sort*} {s : ι -> Set E} (h : forall i, Convex 𝕜 (s i)) :
    Convex 𝕜 (⋂ i, s i) :=
sInter_range s ▸ convex_sInter forall_mem_range.2 h

/--
theorem `convex_iInter₂` / 定理 `convex_iInter₂`

English:
theorem convex_iInter₂
  statement: {ι : Sort*} {κ : ι -> Sort*} {s : (i : ι) -> κ i -> Set E}
  proof: convex_iInter fun i => convex_iInter h i

中文:
定理 convex_iInter₂
  结论: {ι : Sort*} {κ : ι -> Sort*} {s : (i : ι) -> κ i -> Set E}
  证明: convex_iInter fun i => convex_iInter h i

Depends on / 依赖: convex_iInter
-/
theorem convex_iInter₂ {ι : Sort*} {κ : ι -> Sort*} {s : (i : ι) -> κ i -> Set E}
    (h : forall i j, Convex 𝕜 (s i j)) : Convex 𝕜 (⋂ (i) (j), s i j) :=
convex_iInter fun i => convex_iInter h i

/--
theorem `Convex.prod` / 定理 `Convex.prod`

English:
theorem Convex.prod
  given: {s : Set E} {t : Set F} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t)
  proof: fun _ hx => (hs hx.1).prod (ht hx.2)

中文:
定理 Convex.prod
  条件: {s : Set E} {t : Set F} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t)
  证明: fun _ hx => (hs hx.1).prod (ht hx.2)
-/
theorem Convex.prod {s : Set E} {t : Set F} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
    Convex 𝕜 (s ×ˢ t) := fun _ hx => (hs hx.1).prod (ht hx.2)

/--
theorem `convex_pi` / 定理 `convex_pi`

English:
theorem convex_pi
  statement: {ι : Type*} {E : ι -> Type*} [forall i, AddCommMonoid (E i)] [forall i, SMul 𝕜 (E i)]
  proof: fun _ hx => starConvex_pi fun _ hi => ht hi hx _ hi

中文:
定理 convex_pi
  结论: {ι : 类型} {E : ι -> 类型} [对任意 i, AddCommMonoid (E i)] [对任意 i, SMul 𝕜 (E i)]
  证明: fun _ hx => starConvex_pi fun _ hi => ht hi hx _ hi

Depends on / 依赖: starConvex_pi
-/
theorem convex_pi {ι : Type*} {E : ι -> Type*} [forall i, AddCommMonoid (E i)] [forall i, SMul 𝕜 (E i)]
    {s : Set ι} {t : forall i, Set (E i)} (ht : forall ⦃i⦄, i in s -> Convex 𝕜 (t i)) : Convex 𝕜 (s.pi t) :=
fun _ hx => starConvex_pi fun _ hi => ht hi hx _ hi

/--
theorem `Directed.convex_iUnion` / 定理 `Directed.convex_iUnion`

English:
theorem Directed.convex_iUnion
  statement: {ι : Sort*} {s : ι -> Set E} (hdir : Directed (· subseteq ·) s)
  proof: by
  rintro x hx y hy a b ha hb hab
  rw [mem_iUnion] at hx hy ⊢
  obtain ⟨i, hx⟩ := hx
  obtain ⟨j, hy⟩ := hy
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact ⟨k, hc (hik hx) (hjk hy) ha hb hab⟩

中文:
定理 Directed.convex_iUnion
  结论: {ι : Sort*} {s : ι -> Set E} (hdir : Directed (· subseteq ·) s)
  证明: by
  rintro x hx y hy a b ha hb hab
  rw [mem_iUnion] at hx hy ⊢
  obtain ⟨i, hx⟩ := hx
  obtain ⟨j, hy⟩ := hy
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact ⟨k, hc (hik hx) (hjk hy) ha hb hab⟩

Depends on / 依赖: mem_iUnion
-/
theorem Directed.convex_iUnion {ι : Sort*} {s : ι -> Set E} (hdir : Directed (· subseteq ·) s)
    (hc : forall ⦃i : ι⦄, Convex 𝕜 (s i)) : Convex 𝕜 (⋃ i, s i) := by
  rintro x hx y hy a b ha hb hab
  rw [mem_iUnion] at hx hy ⊢
  obtain ⟨i, hx⟩ := hx
  obtain ⟨j, hy⟩ := hy
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact ⟨k, hc (hik hx) (hjk hy) ha hb hab⟩

/--
theorem `DirectedOn.convex_sUnion` / 定理 `DirectedOn.convex_sUnion`

English:
theorem DirectedOn.convex_sUnion
  statement: {c : Set (Set E)} (hdir : DirectedOn (· subseteq ·) c)
  proof: by
  rw [sUnion_eq_iUnion]
  exact (directedOn_iff_directed.1 hdir).convex_iUnion fun A => hc A.2

中文:
定理 DirectedOn.convex_sUnion
  结论: {c : Set (Set E)} (hdir : DirectedOn (· subseteq ·) c)
  证明: by
  rw [sUnion_eq_iUnion]
  exact (directedOn_iff_directed.1 hdir).convex_iUnion fun A => hc A.2

Depends on / 依赖: convex_iUnion, directedOn_iff_directed, sUnion_eq_iUnion
-/
theorem DirectedOn.convex_sUnion {c : Set (Set E)} (hdir : DirectedOn (· subseteq ·) c)
    (hc : forall ⦃A : Set E⦄, A in c -> Convex 𝕜 A) : Convex 𝕜 (⋃₀ c) := by
  rw [sUnion_eq_iUnion]
  exact (directedOn_iff_directed.1 hdir).convex_iUnion fun A => hc A.2

/--
theorem `Convex.setOfPred_const_imp` / 定理 `Convex.setOfPred_const_imp`

English:
theorem Convex.setOfPred_const_imp
  given: {P : Prop} (hs : Convex 𝕜 s)
  statement: Convex 𝕜 {x | P -> x in s}
  proof: by
  by_cases hP : P <;> simp [hP, hs, convex_univ]

@[deprecated (since := "2026-07-09")] alias Convex.setOf_const_imp := Convex.setOfPred_const_imp

中文:
定理 Convex.setOfPred_const_imp
  条件: {P : 命题} (hs : Convex 𝕜 s)
  结论: Convex 𝕜 {x | P -> x in s}
  证明: by
  by_cases hP : P <;> simp [hP, hs, convex_univ]

@[deprecated (since := "2026-07-09")] alias Convex.setOf_const_imp := Convex.setOfPred_const_imp

Depends on / 依赖: convex_univ
-/
theorem Convex.setOfPred_const_imp {P : Prop} (hs : Convex 𝕜 s) : Convex 𝕜 {x | P -> x in s} := by
  by_cases hP : P <;> simp [hP, hs, convex_univ]

@[deprecated (since := "2026-07-09")] alias Convex.setOf_const_imp := Convex.setOfPred_const_imp

end SMul

section Module

variable [Module 𝕜 E] [Module 𝕜 F] {s : Set E} {x : E}

/--
theorem `convex_iff_openSegment_subset` / 定理 `convex_iff_openSegment_subset`

English:
theorem convex_iff_openSegment_subset
  given: [ZeroLEOneClass 𝕜]
  proof: forall₂_congr fun _ => starConvex_iff_openSegment_subset

中文:
定理 convex_iff_openSegment_subset
  条件: [ZeroLEOneClass 𝕜]
  证明: forall₂_congr fun _ => starConvex_iff_openSegment_subset

Depends on / 依赖: starConvex_iff_openSegment_subset
-/
theorem convex_iff_openSegment_subset [ZeroLEOneClass 𝕜] :
    Convex 𝕜 s ↔ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> openSegment 𝕜 x y subseteq s :=
  forall₂_congr fun _ => starConvex_iff_openSegment_subset

/--
theorem `convex_iff_forall_pos` / 定理 `convex_iff_forall_pos`

English:
theorem convex_iff_forall_pos
  proof: forall₂_congr fun _ => starConvex_iff_forall_pos

中文:
定理 convex_iff_forall_pos
  证明: forall₂_congr fun _ => starConvex_iff_forall_pos

Depends on / 依赖: starConvex_iff_forall_pos
-/
theorem convex_iff_forall_pos :
    Convex 𝕜 s ↔
      forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • x + b • y in s :=
  forall₂_congr fun _ => starConvex_iff_forall_pos

/--
theorem `convex_iff_pairwise_pos` / 定理 `convex_iff_pairwise_pos`

English:
theorem convex_iff_pairwise_pos
  statement: Convex 𝕜 s ↔
  proof: by
  refine convex_iff_forall_pos.trans ⟨fun h x hx y hy _ => h hx hy, ?_⟩
  intro h x hx y hy a b ha hb hab
  obtain rfl | hxy := eq_or_ne x y
  · rwa [Convex.combo_self hab]
  · exact h hx hy hxy ha hb hab

中文:
定理 convex_iff_pairwise_pos
  结论: Convex 𝕜 s ↔
  证明: by
  refine convex_iff_forall_pos.trans ⟨fun h x hx y hy _ => h hx hy, ?_⟩
  intro h x hx y hy a b ha hb hab
  obtain rfl | hxy := eq_or_ne x y
  · rwa [Convex.combo_self hab]
  · exact h hx hy hxy ha hb hab

Depends on / 依赖: Convex, Convex.combo_self, combo_self, convex_iff_forall_pos, convex_iff_forall_pos.trans, eq_or_ne
-/
theorem convex_iff_pairwise_pos : Convex 𝕜 s ↔
    s.Pairwise fun x y => forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • x + b • y in s := by
  refine convex_iff_forall_pos.trans ⟨fun h x hx y hy _ => h hx hy, ?_⟩
  intro h x hx y hy a b ha hb hab
  obtain rfl | hxy := eq_or_ne x y
  · rwa [Convex.combo_self hab]
  · exact h hx hy hxy ha hb hab

/--
theorem `Convex.starConvex_iff` / 定理 `Convex.starConvex_iff`

English:
theorem Convex.starConvex_iff
  given: [ZeroLEOneClass 𝕜] (hs : Convex 𝕜 s) (h : s.Nonempty)
  proof: ⟨fun hxs => hxs.mem h, hs.starConvex⟩

中文:
定理 Convex.starConvex_iff
  条件: [ZeroLEOneClass 𝕜] (hs : Convex 𝕜 s) (h : s.Nonempty)
  证明: ⟨fun hxs => hxs.mem h, hs.starConvex⟩

Depends on / 依赖: hs.starConvex, hxs.mem, starConvex
-/
theorem Convex.starConvex_iff [ZeroLEOneClass 𝕜] (hs : Convex 𝕜 s) (h : s.Nonempty) :
    StarConvex 𝕜 x s ↔ x in s :=
  ⟨fun hxs => hxs.mem h, hs.starConvex⟩

/--
theorem `Set.Subsingleton.convex` / 定理 `Set.Subsingleton.convex`

English:
theorem Set.Subsingleton.convex
  given: {s : Set E} (h : s.Subsingleton)
  statement: Convex 𝕜 s
  proof: convex_iff_pairwise_pos.mpr (h.pairwise _)

中文:
定理 Set.Subsingleton.convex
  条件: {s : Set E} (h : s.Subsingleton)
  结论: Convex 𝕜 s
  证明: convex_iff_pairwise_pos.mpr (h.pairwise _)
-/
protected theorem Set.Subsingleton.convex {s : Set E} (h : s.Subsingleton) : Convex 𝕜 s :=
  convex_iff_pairwise_pos.mpr (h.pairwise _)

/--
theorem `convex_singleton` / 定理 `convex_singleton`

English:
theorem convex_singleton
  given: (c : E)
  statement: Convex 𝕜 ({c} : Set E)
  proof: subsingleton_singleton.convex

中文:
定理 convex_singleton
  条件: (c : E)
  结论: Convex 𝕜 ({c} : Set E)
  证明: subsingleton_singleton.convex
-/
@[simp] theorem convex_singleton (c : E) : Convex 𝕜 ({c} : Set E) :=
  subsingleton_singleton.convex

/--
theorem `convex_zero` / 定理 `convex_zero`

English:
theorem convex_zero
  statement: Convex 𝕜 (0 : Set E)
  proof: convex_singleton _

中文:
定理 convex_zero
  结论: Convex 𝕜 (0 : Set E)
  证明: convex_singleton _

Depends on / 依赖: convex_singleton
-/
theorem convex_zero : Convex 𝕜 (0 : Set E) :=
  convex_singleton _

/--
theorem `convex_segment` / 定理 `convex_segment`

English:
theorem convex_segment
  given: [IsOrderedRing 𝕜] (x y : E)
  statement: Convex 𝕜 [x -[𝕜] y]
  proof: by
  rintro p ⟨ap, bp, hap, hbp, habp, rfl⟩ q ⟨aq, bq, haq, hbq, habq, rfl⟩ a b ha hb hab
  refine
    ⟨a * ap + b * aq, a * bp + b * bq, add_nonneg (mul_nonneg ha hap) (mul_nonneg hb haq),
      add_nonneg (mul_nonneg ha hbp) (mul_nonneg hb hbq), ?_, ?_⟩
  · rw [add_add_add_comm, ← mul_add, ← mul_a

中文:
定理 convex_segment
  条件: [IsOrderedRing 𝕜] (x y : E)
  结论: Convex 𝕜 [x -[𝕜] y]
  证明: by
  rintro p ⟨ap, bp, hap, hbp, habp, rfl⟩ q ⟨aq, bq, haq, hbq, habq, rfl⟩ a b ha hb hab
  refine
    ⟨a * ap + b * aq, a * bp + b * bq, add_nonneg (mul_nonneg ha hap) (mul_nonneg hb haq),
      add_nonneg (mul_nonneg ha hbp) (mul_nonneg hb hbq), ?_, ?_⟩
  · rw [add_add_add_comm, ← mul_add, ← mul_a

Depends on / 依赖: add_add_add_comm, add_nonneg, match_scalars, mul_add, mul_nonneg, mul_one, noncomm_ring
-/
theorem convex_segment [IsOrderedRing 𝕜] (x y : E) : Convex 𝕜 [x -[𝕜] y] := by
  rintro p ⟨ap, bp, hap, hbp, habp, rfl⟩ q ⟨aq, bq, haq, hbq, habq, rfl⟩ a b ha hb hab
  refine
    ⟨a * ap + b * aq, a * bp + b * bq, add_nonneg (mul_nonneg ha hap) (mul_nonneg hb haq),
      add_nonneg (mul_nonneg ha hbp) (mul_nonneg hb hbq), ?_, ?_⟩
  · rw [add_add_add_comm, ← mul_add, ← mul_add, habp, habq, mul_one, mul_one, hab]
  · match_scalars <;> noncomm_ring

/--
theorem `Convex.linear_image` / 定理 `Convex.linear_image`

English:
theorem Convex.linear_image
  given: (hs : Convex 𝕜 s) (f : E ->ₗ[𝕜] F)
  statement: Convex 𝕜 (f '' s)
  proof: by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, hs hx hy ha hb hab, by rw [f.map_add, f.map_smul, f.map_smul]⟩

中文:
定理 Convex.linear_image
  条件: (hs : Convex 𝕜 s) (f : E ->ₗ[𝕜] F)
  结论: Convex 𝕜 (f '' s)
  证明: by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, hs hx hy ha hb hab, by rw [f.map_add, f.map_smul, f.map_smul]⟩

Depends on / 依赖: f.map_add, f.map_smul, map_add, map_smul
-/
theorem Convex.linear_image (hs : Convex 𝕜 s) (f : E ->ₗ[𝕜] F) : Convex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, hs hx hy ha hb hab, by rw [f.map_add, f.map_smul, f.map_smul]⟩

/--
theorem `Convex.is_linear_image` / 定理 `Convex.is_linear_image`

English:
theorem Convex.is_linear_image
  given: (hs : Convex 𝕜 s) {f : E -> F} (hf : IsLinearMap 𝕜 f)
  proof: hs.linear_image hf.mk' f

中文:
定理 Convex.is_linear_image
  条件: (hs : Convex 𝕜 s) {f : E -> F} (hf : IsLinearMap 𝕜 f)
  证明: hs.linear_image hf.mk' f

Depends on / 依赖: hf.mk, hs.linear_image, linear_image
-/
theorem Convex.is_linear_image (hs : Convex 𝕜 s) {f : E -> F} (hf : IsLinearMap 𝕜 f) :
    Convex 𝕜 (f '' s) :=
hs.linear_image hf.mk' f

/--
theorem `Convex.linear_preimage` / 定理 `Convex.linear_preimage`

English:
theorem Convex.linear_preimage
  given: {s : Set F} (hs : Convex 𝕜 s) (f : E ->ₗ[𝕜] F)
  statement: Convex 𝕜 (f ⁻¹' s)
  proof: fun x hx y hy a b ha hb hab => by
    rw [mem_preimage]; rw [f.map_add]; rw [LinearMap.map_smul_of_tower]; rw [LinearMap.map_smul_of_tower]
    exact hs hx hy ha hb hab

中文:
定理 Convex.linear_preimage
  条件: {s : Set F} (hs : Convex 𝕜 s) (f : E ->ₗ[𝕜] F)
  结论: Convex 𝕜 (f ⁻¹' s)
  证明: fun x hx y hy a b ha hb hab => by
    rw [mem_preimage]; rw [f.map_add]; rw [LinearMap.map_smul_of_tower]; rw [LinearMap.map_smul_of_tower]
    exact hs hx hy ha hb hab

Depends on / 依赖: LinearMap, LinearMap.map_smul_of_tower, f.map_add, map_add, map_smul_of_tower, mem_preimage
-/
theorem Convex.linear_preimage {s : Set F} (hs : Convex 𝕜 s) (f : E ->ₗ[𝕜] F) : Convex 𝕜 (f ⁻¹' s) :=
  fun x hx y hy a b ha hb hab => by
    rw [mem_preimage]; rw [f.map_add]; rw [LinearMap.map_smul_of_tower]; rw [LinearMap.map_smul_of_tower]
    exact hs hx hy ha hb hab

/--
theorem `Convex.is_linear_preimage` / 定理 `Convex.is_linear_preimage`

English:
theorem Convex.is_linear_preimage
  given: {s : Set F} (hs : Convex 𝕜 s) {f : E -> F} (hf : IsLinearMap 𝕜 f)
  proof: hs.linear_preimage hf.mk' f

中文:
定理 Convex.is_linear_preimage
  条件: {s : Set F} (hs : Convex 𝕜 s) {f : E -> F} (hf : IsLinearMap 𝕜 f)
  证明: hs.linear_preimage hf.mk' f

Depends on / 依赖: hf.mk, hs.linear_preimage, linear_preimage
-/
theorem Convex.is_linear_preimage {s : Set F} (hs : Convex 𝕜 s) {f : E -> F} (hf : IsLinearMap 𝕜 f) :
Convex 𝕜 (f ⁻¹' s) := hs.linear_preimage hf.mk' f

/--
theorem `Convex.add` / 定理 `Convex.add`

English:
theorem Convex.add
  given: {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t)
  statement: Convex 𝕜 (s + t)
  proof: by
  rw [← add_image_prod]
  exact (hs.prod ht).is_linear_image IsLinearMap.isLinearMap_add

中文:
定理 Convex.add
  条件: {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t)
  结论: Convex 𝕜 (s + t)
  证明: by
  rw [← add_image_prod]
  exact (hs.prod ht).is_linear_image IsLinearMap.isLinearMap_add

Depends on / 依赖: IsLinearMap, IsLinearMap.isLinearMap_add, add_image_prod, hs.prod, isLinearMap_add, is_linear_image
-/
theorem Convex.add {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s + t) := by
  rw [← add_image_prod]
  exact (hs.prod ht).is_linear_image IsLinearMap.isLinearMap_add

variable (𝕜 E)

/--
Definition of `convexAddSubmonoid` / `convexAddSubmonoid` 的定义

English:
definition convexAddSubmonoid
  signature: : AddSubmonoid (Set E) where
  body: {s : Set E | Convex 𝕜 s}
  zero_mem' := convex_zero
  add_mem' := Convex.add

@[simp, norm_cast]

中文:
定义 convexAddSubmonoid
  签名: : AddSubmonoid (Set E) where
  定义体: {s : Set E | Convex 𝕜 s}
  zero_mem' := convex_zero
  add_mem' := Convex.add

@[simp, norm_cast]

Depends on / 依赖: Convex
-/
noncomputable def convexAddSubmonoid : AddSubmonoid (Set E) where
  carrier := {s : Set E | Convex 𝕜 s}
  zero_mem' := convex_zero
  add_mem' := Convex.add

@[simp, norm_cast]
/--
theorem `coe_convexAddSubmonoid` / 定理 `coe_convexAddSubmonoid`

English:
theorem coe_convexAddSubmonoid
  statement: ↑(convexAddSubmonoid 𝕜 E) = {s : Set E | Convex 𝕜 s}
  proof: rfl

中文:
定理 coe_convexAddSubmonoid
  结论: ↑(convexAddSubmonoid 𝕜 E) = {s : Set E | Convex 𝕜 s}
  证明: rfl
-/
theorem coe_convexAddSubmonoid : ↑(convexAddSubmonoid 𝕜 E) = {s : Set E | Convex 𝕜 s} :=
  rfl

variable {𝕜 E}

@[simp]
/--
theorem `mem_convexAddSubmonoid` / 定理 `mem_convexAddSubmonoid`

English:
theorem mem_convexAddSubmonoid
  given: {s : Set E}
  statement: s in convexAddSubmonoid 𝕜 E ↔ Convex 𝕜 s
  proof: Iff.rfl

中文:
定理 mem_convexAddSubmonoid
  条件: {s : Set E}
  结论: s in convexAddSubmonoid 𝕜 E ↔ Convex 𝕜 s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_convexAddSubmonoid {s : Set E} : s in convexAddSubmonoid 𝕜 E ↔ Convex 𝕜 s :=
  Iff.rfl

/--
theorem `convex_list_sum` / 定理 `convex_list_sum`

English:
theorem convex_list_sum
  given: {l : List (Set E)} (h : forall i in l, Convex 𝕜 i)
  statement: Convex 𝕜 l.sum
  proof: (convexAddSubmonoid 𝕜 E).list_sum_mem h

中文:
定理 convex_list_sum
  条件: {l : List (Set E)} (h : 对任意 i in l, Convex 𝕜 i)
  结论: Convex 𝕜 l.sum
  证明: (convexAddSubmonoid 𝕜 E).list_sum_mem h

Depends on / 依赖: convexAddSubmonoid, list_sum_mem
-/
theorem convex_list_sum {l : List (Set E)} (h : forall i in l, Convex 𝕜 i) : Convex 𝕜 l.sum :=
  (convexAddSubmonoid 𝕜 E).list_sum_mem h

/--
theorem `convex_multiset_sum` / 定理 `convex_multiset_sum`

English:
theorem convex_multiset_sum
  given: {s : Multiset (Set E)} (h : forall i in s, Convex 𝕜 i)
  statement: Convex 𝕜 s.sum
  proof: (convexAddSubmonoid 𝕜 E).multiset_sum_mem _ h

中文:
定理 convex_multiset_sum
  条件: {s : Multiset (Set E)} (h : 对任意 i in s, Convex 𝕜 i)
  结论: Convex 𝕜 s.sum
  证明: (convexAddSubmonoid 𝕜 E).multiset_sum_mem _ h

Depends on / 依赖: convexAddSubmonoid, multiset_sum_mem
-/
theorem convex_multiset_sum {s : Multiset (Set E)} (h : forall i in s, Convex 𝕜 i) : Convex 𝕜 s.sum :=
  (convexAddSubmonoid 𝕜 E).multiset_sum_mem _ h

/--
theorem `convex_sum` / 定理 `convex_sum`

English:
theorem convex_sum
  given: {ι} {s : Finset ι} (t : ι -> Set E) (h : forall i in s, Convex 𝕜 (t i))
  proof: (convexAddSubmonoid 𝕜 E).sum_mem h

中文:
定理 convex_sum
  条件: {ι} {s : Finset ι} (t : ι -> Set E) (h : 对任意 i in s, Convex 𝕜 (t i))
  证明: (convexAddSubmonoid 𝕜 E).sum_mem h

Depends on / 依赖: convexAddSubmonoid, sum_mem
-/
theorem convex_sum {ι} {s : Finset ι} (t : ι -> Set E) (h : forall i in s, Convex 𝕜 (t i)) :
    Convex 𝕜 (∑ i in s, t i) :=
  (convexAddSubmonoid 𝕜 E).sum_mem h

/--
theorem `Convex.vadd` / 定理 `Convex.vadd`

English:
theorem Convex.vadd
  given: (hs : Convex 𝕜 s) (z : E)
  statement: Convex 𝕜 (z +ᵥ s)
  proof: by
  simp_rw [← image_vadd, vadd_eq_add, ← singleton_add]
  exact (convex_singleton _).add hs

中文:
定理 Convex.vadd
  条件: (hs : Convex 𝕜 s) (z : E)
  结论: Convex 𝕜 (z +ᵥ s)
  证明: by
  simp_rw [← image_vadd, vadd_eq_add, ← singleton_add]
  exact (convex_singleton _).add hs

Depends on / 依赖: convex_singleton, image_vadd, simp_rw, singleton_add, vadd_eq_add
-/
theorem Convex.vadd (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 (z +ᵥ s) := by
  simp_rw [← image_vadd, vadd_eq_add, ← singleton_add]
  exact (convex_singleton _).add hs

/--
theorem `Convex.translate` / 定理 `Convex.translate`

English:
theorem Convex.translate
  given: (hs : Convex 𝕜 s) (z : E)
  statement: Convex 𝕜 ((fun x => z + x) '' s)
  proof: hs.vadd _

中文:
定理 Convex.translate
  条件: (hs : Convex 𝕜 s) (z : E)
  结论: Convex 𝕜 ((fun x => z + x) '' s)
  证明: hs.vadd _

Depends on / 依赖: hs.vadd
-/
theorem Convex.translate (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 ((fun x => z + x) '' s) :=
  hs.vadd _

/--
theorem `Convex.translate_preimage_right` / 定理 `Convex.translate_preimage_right`

English:
theorem Convex.translate_preimage_right
  given: (hs : Convex 𝕜 s) (z : E)
  proof: by
  intro x hx y hy a b ha hb hab
  have h := hs hx hy ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul] at h

中文:
定理 Convex.translate_preimage_right
  条件: (hs : Convex 𝕜 s) (z : E)
  证明: by
  intro x hx y hy a b ha hb hab
  have h := hs hx hy ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul] at h

Depends on / 依赖: add_add_add_comm, add_smul, one_smul, smul_add
-/
theorem Convex.translate_preimage_right (hs : Convex 𝕜 s) (z : E) :
    Convex 𝕜 ((fun x => z + x) ⁻¹' s) := by
  intro x hx y hy a b ha hb hab
  have h := hs hx hy ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul] at h

/--
theorem `Convex.translate_preimage_left` / 定理 `Convex.translate_preimage_left`

English:
theorem Convex.translate_preimage_left
  given: (hs : Convex 𝕜 s) (z : E)
  proof: by
  simpa only [add_comm] using hs.translate_preimage_right z

中文:
定理 Convex.translate_preimage_left
  条件: (hs : Convex 𝕜 s) (z : E)
  证明: by
  simpa only [add_comm] using hs.translate_preimage_right z

Depends on / 依赖: add_comm, hs.translate_preimage_right, translate_preimage_right
-/
theorem Convex.translate_preimage_left (hs : Convex 𝕜 s) (z : E) :
    Convex 𝕜 ((fun x => x + z) ⁻¹' s) := by
  simpa only [add_comm] using hs.translate_preimage_right z

section OrderedAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulMono 𝕜 β]

/--
theorem `convex_Iic` / 定理 `convex_Iic`

English:
theorem convex_Iic
  given: (r : β)
  statement: Convex 𝕜 (Iic r)
  proof: fun x hx y hy a b ha hb hab =>
  calc
    a • x + b • y <= a • r + b • r :=
      add_le_add (smul_le_smul_of_nonneg_left hx ha) (smul_le_smul_of_nonneg_left hy hb)
    _ = r := Convex.combo_self hab _

中文:
定理 convex_Iic
  条件: (r : β)
  结论: Convex 𝕜 (Iic r)
  证明: fun x hx y hy a b ha hb hab =>
  calc
    a • x + b • y <= a • r + b • r :=
      add_le_add (smul_le_smul_of_nonneg_left hx ha) (smul_le_smul_of_nonneg_left hy hb)
    _ = r := Convex.combo_self hab _
-/
theorem convex_Iic (r : β) : Convex 𝕜 (Iic r) := fun x hx y hy a b ha hb hab =>
  calc
    a • x + b • y <= a • r + b • r :=
      add_le_add (smul_le_smul_of_nonneg_left hx ha) (smul_le_smul_of_nonneg_left hy hb)
    _ = r := Convex.combo_self hab _

/--
theorem `convex_Ici` / 定理 `convex_Ici`

English:
theorem convex_Ici
  given: (r : β)
  statement: Convex 𝕜 (Ici r)
  proof: convex_Iic (β := βᵒᵈ) r

中文:
定理 convex_Ici
  条件: (r : β)
  结论: Convex 𝕜 (Ici r)
  证明: convex_Iic (β := βᵒᵈ) r

Depends on / 依赖: convex_Iic
-/
theorem convex_Ici (r : β) : Convex 𝕜 (Ici r) :=
  convex_Iic (β := βᵒᵈ) r

/--
theorem `convex_Icc` / 定理 `convex_Icc`

English:
theorem convex_Icc
  given: (r s : β)
  statement: Convex 𝕜 (Icc r s)
  proof: Ici_inter_Iic.subst ((convex_Ici r).inter <| convex_Iic s)

中文:
定理 convex_Icc
  条件: (r s : β)
  结论: Convex 𝕜 (Icc r s)
  证明: Ici_inter_Iic.subst ((convex_Ici r).inter <| convex_Iic s)

Depends on / 依赖: Ici_inter_Iic, Ici_inter_Iic.subst, convex_Ici, convex_Iic
-/
theorem convex_Icc (r s : β) : Convex 𝕜 (Icc r s) :=
  Ici_inter_Iic.subst ((convex_Ici r).inter <| convex_Iic s)

/--
theorem `convex_halfSpace_le` / 定理 `convex_halfSpace_le`

English:
theorem convex_halfSpace_le
  given: {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β)
  statement: Convex 𝕜 { w | f w <= r }
  proof: (convex_Iic r).is_linear_preimage h

中文:
定理 convex_halfSpace_le
  条件: {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β)
  结论: Convex 𝕜 { w | f w <= r }
  证明: (convex_Iic r).is_linear_preimage h

Depends on / 依赖: convex_Iic, is_linear_preimage
-/
theorem convex_halfSpace_le {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w <= r } :=
  (convex_Iic r).is_linear_preimage h
/--
theorem `convex_halfSpace_ge` / 定理 `convex_halfSpace_ge`

English:
theorem convex_halfSpace_ge
  given: {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β)
  statement: Convex 𝕜 { w | r <= f w }
  proof: (convex_Ici r).is_linear_preimage h

中文:
定理 convex_halfSpace_ge
  条件: {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β)
  结论: Convex 𝕜 { w | r <= f w }
  证明: (convex_Ici r).is_linear_preimage h

Depends on / 依赖: convex_Ici, is_linear_preimage
-/
theorem convex_halfSpace_ge {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | r <= f w } :=
  (convex_Ici r).is_linear_preimage h
/--
theorem `convex_hyperplane` / 定理 `convex_hyperplane`

English:
theorem convex_hyperplane
  given: {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β)
  statement: Convex 𝕜 { w | f w = r }
  proof: by
  simp_rw [le_antisymm_iff]
  exact (convex_halfSpace_le h r).inter (convex_halfSpace_ge h r)

中文:
定理 convex_hyperplane
  条件: {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β)
  结论: Convex 𝕜 { w | f w = r }
  证明: by
  simp_rw [le_antisymm_iff]
  exact (convex_halfSpace_le h r).inter (convex_halfSpace_ge h r)

Depends on / 依赖: convex_halfSpace_ge, convex_halfSpace_le, le_antisymm_iff, simp_rw
-/
theorem convex_hyperplane {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w = r } := by
  simp_rw [le_antisymm_iff]
  exact (convex_halfSpace_le h r).inter (convex_halfSpace_ge h r)

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedCancelAddMonoid β]
  [Module 𝕜 β] [PosSMulStrictMono 𝕜 β]

/--
theorem `convex_Iio` / 定理 `convex_Iio`

English:
theorem convex_Iio
  given: (r : β)
  statement: Convex 𝕜 (Iio r)
  proof: by
  intro x hx y hy a b ha hb hab
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    rwa [zero_smul, zero_add, hab, one_smul]
  rw [mem_Iio] at hx hy
  calc
    a • x + b • y < a • r + b • r := add_lt_add_of_lt_of_le
        (smul_lt_smul_of_pos_left hx ha') (smul_le_smul_of_nonneg_left

中文:
定理 convex_Iio
  条件: (r : β)
  结论: Convex 𝕜 (Iio r)
  证明: by
  intro x hx y hy a b ha hb hab
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    rwa [zero_smul, zero_add, hab, one_smul]
  rw [mem_Iio] at hx hy
  calc
    a • x + b • y < a • r + b • r := add_lt_add_of_lt_of_le
        (smul_lt_smul_of_pos_left hx ha') (smul_le_smul_of_nonneg_left

Depends on / 依赖: Convex, Convex.combo_self, add_lt_add_of_lt_of_le, combo_self, eq_or_lt, ha.eq_or_lt, hy.le, mem_Iio, one_smul, smul_le_smul_of_nonneg_left, smul_lt_smul_of_pos_left, zero_add, zero_smul
-/
theorem convex_Iio (r : β) : Convex 𝕜 (Iio r) := by
  intro x hx y hy a b ha hb hab
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    rwa [zero_smul, zero_add, hab, one_smul]
  rw [mem_Iio] at hx hy
  calc
    a • x + b • y < a • r + b • r := add_lt_add_of_lt_of_le
        (smul_lt_smul_of_pos_left hx ha') (smul_le_smul_of_nonneg_left hy.le hb)
    _ = r := Convex.combo_self hab _

/--
theorem `convex_Ioi` / 定理 `convex_Ioi`

English:
theorem convex_Ioi
  given: (r : β)
  statement: Convex 𝕜 (Ioi r)
  proof: convex_Iio (β := βᵒᵈ) r

中文:
定理 convex_Ioi
  条件: (r : β)
  结论: Convex 𝕜 (Ioi r)
  证明: convex_Iio (β := βᵒᵈ) r

Depends on / 依赖: convex_Iio
-/
theorem convex_Ioi (r : β) : Convex 𝕜 (Ioi r) :=
  convex_Iio (β := βᵒᵈ) r

/--
theorem `convex_Ioo` / 定理 `convex_Ioo`

English:
theorem convex_Ioo
  given: (r s : β)
  statement: Convex 𝕜 (Ioo r s)
  proof: Ioi_inter_Iio.subst ((convex_Ioi r).inter <| convex_Iio s)

中文:
定理 convex_Ioo
  条件: (r s : β)
  结论: Convex 𝕜 (Ioo r s)
  证明: Ioi_inter_Iio.subst ((convex_Ioi r).inter <| convex_Iio s)

Depends on / 依赖: Ioi_inter_Iio, Ioi_inter_Iio.subst, convex_Iio, convex_Ioi
-/
theorem convex_Ioo (r s : β) : Convex 𝕜 (Ioo r s) :=
  Ioi_inter_Iio.subst ((convex_Ioi r).inter <| convex_Iio s)

/--
theorem `convex_Ico` / 定理 `convex_Ico`

English:
theorem convex_Ico
  given: (r s : β)
  statement: Convex 𝕜 (Ico r s)
  proof: Ici_inter_Iio.subst ((convex_Ici r).inter <| convex_Iio s)

中文:
定理 convex_Ico
  条件: (r s : β)
  结论: Convex 𝕜 (Ico r s)
  证明: Ici_inter_Iio.subst ((convex_Ici r).inter <| convex_Iio s)

Depends on / 依赖: Ici_inter_Iio, Ici_inter_Iio.subst, convex_Ici, convex_Iio
-/
theorem convex_Ico (r s : β) : Convex 𝕜 (Ico r s) :=
  Ici_inter_Iio.subst ((convex_Ici r).inter <| convex_Iio s)

/--
theorem `convex_Ioc` / 定理 `convex_Ioc`

English:
theorem convex_Ioc
  given: (r s : β)
  statement: Convex 𝕜 (Ioc r s)
  proof: Ioi_inter_Iic.subst ((convex_Ioi r).inter <| convex_Iic s)

中文:
定理 convex_Ioc
  条件: (r s : β)
  结论: Convex 𝕜 (Ioc r s)
  证明: Ioi_inter_Iic.subst ((convex_Ioi r).inter <| convex_Iic s)

Depends on / 依赖: Ioi_inter_Iic, Ioi_inter_Iic.subst, convex_Iic, convex_Ioi
-/
theorem convex_Ioc (r s : β) : Convex 𝕜 (Ioc r s) :=
  Ioi_inter_Iic.subst ((convex_Ioi r).inter <| convex_Iic s)

/--
theorem `convex_halfSpace_lt` / 定理 `convex_halfSpace_lt`

English:
theorem convex_halfSpace_lt
  given: {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β)
  statement: Convex 𝕜 { w | f w < r }
  proof: (convex_Iio r).is_linear_preimage h

中文:
定理 convex_halfSpace_lt
  条件: {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β)
  结论: Convex 𝕜 { w | f w < r }
  证明: (convex_Iio r).is_linear_preimage h

Depends on / 依赖: convex_Iio, is_linear_preimage
-/
theorem convex_halfSpace_lt {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w < r } :=
  (convex_Iio r).is_linear_preimage h
/--
theorem `convex_halfSpace_gt` / 定理 `convex_halfSpace_gt`

English:
theorem convex_halfSpace_gt
  given: {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β)
  statement: Convex 𝕜 { w | r < f w }
  proof: (convex_Ioi r).is_linear_preimage h

中文:
定理 convex_halfSpace_gt
  条件: {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β)
  结论: Convex 𝕜 { w | r < f w }
  证明: (convex_Ioi r).is_linear_preimage h

Depends on / 依赖: convex_Ioi, is_linear_preimage
-/
theorem convex_halfSpace_gt {f : E -> β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | r < f w } :=
  (convex_Ioi r).is_linear_preimage h
end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulMono 𝕜 β]

/--
theorem `convex_uIcc` / 定理 `convex_uIcc`

English:
theorem convex_uIcc
  given: (r s : β)
  statement: Convex 𝕜 (uIcc r s)
  proof: convex_Icc _ _

中文:
定理 convex_uIcc
  条件: (r s : β)
  结论: Convex 𝕜 (uIcc r s)
  证明: convex_Icc _ _

Depends on / 依赖: convex_Icc
-/
theorem convex_uIcc (r s : β) : Convex 𝕜 (uIcc r s) :=
  convex_Icc _ _

end LinearOrderedAddCommMonoid

end Module

section IsScalarTower

variable [ZeroLEOneClass 𝕜] [Module 𝕜 E]
variable (R : Type*) [Semiring R] [PartialOrder R] [Module R E]
variable [Module R 𝕜] [IsScalarTower R 𝕜 E]

/--
theorem `Convex.lift` / 定理 `Convex.lift`

English:
theorem Convex.lift
  given: [SMulPosMono R 𝕜] {s : Set E} (hs : Convex 𝕜 s)
  statement: Convex R s
  proof: by
  intro x hx y hy a b ha hb hab
  suffices (a • (1 : 𝕜)) • x + (b • (1 : 𝕜)) • y in s by simpa using this
  refine hs hx hy ?_ ?_ (by simpa [add_smul] using congr($(hab) • (1 : 𝕜)))
  all_goals exact zero_smul R (1 : 𝕜) ▸ smul_le_smul_of_nonneg_right ‹_› zero_le_one

中文:
定理 Convex.lift
  条件: [SMulPosMono R 𝕜] {s : Set E} (hs : Convex 𝕜 s)
  结论: Convex R s
  证明: by
  intro x hx y hy a b ha hb hab
  suffices (a • (1 : 𝕜)) • x + (b • (1 : 𝕜)) • y in s by simpa using this
  refine hs hx hy ?_ ?_ (by simpa [add_smul] using congr($(hab) • (1 : 𝕜)))
  all_goals exact zero_smul R (1 : 𝕜) ▸ smul_le_smul_of_nonneg_right ‹_› zero_le_one

Depends on / 依赖: add_smul, all_goals, smul_le_smul_of_nonneg_right, zero_le_one, zero_smul
-/
theorem Convex.lift [SMulPosMono R 𝕜] {s : Set E} (hs : Convex 𝕜 s) : Convex R s := by
  intro x hx y hy a b ha hb hab
  suffices (a • (1 : 𝕜)) • x + (b • (1 : 𝕜)) • y in s by simpa using this
  refine hs hx hy ?_ ?_ (by simpa [add_smul] using congr($(hab) • (1 : 𝕜)))
  all_goals exact zero_smul R (1 : 𝕜) ▸ smul_le_smul_of_nonneg_right ‹_› zero_le_one

end IsScalarTower

end AddCommMonoid

section LinearOrderedAddCommMonoid

variable [AddCommMonoid E] [LinearOrder E] [IsOrderedAddMonoid E]
  [PartialOrder β] [Module 𝕜 E] [PosSMulMono 𝕜 E]
  {s : Set E} {f : E -> β}

/--
theorem `MonotoneOn.convex_le` / 定理 `MonotoneOn.convex_le`

English:
theorem MonotoneOn.convex_le
  given: (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β)
  proof: fun x hx y hy _ _ ha hb hab =>
  ⟨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' (· in s) hx.1 hy.1)
      (Convex.combo_le_max x y ha hb hab)).trans
      (max_rec' (f · <= r) hx.2 hy.2)⟩

中文:
定理 MonotoneOn.convex_le
  条件: (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β)
  证明: fun x hx y hy _ _ ha hb hab =>
  ⟨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' (· in s) hx.1 hy.1)
      (Convex.combo_le_max x y ha hb hab)).trans
      (max_rec' (f · <= r) hx.2 hy.2)⟩
-/
theorem MonotoneOn.convex_le (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x in s | f x <= r }) := fun x hx y hy _ _ ha hb hab =>
  ⟨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' (· in s) hx.1 hy.1)
      (Convex.combo_le_max x y ha hb hab)).trans
      (max_rec' (f · <= r) hx.2 hy.2)⟩

/--
theorem `MonotoneOn.convex_lt` / 定理 `MonotoneOn.convex_lt`

English:
theorem MonotoneOn.convex_lt
  given: (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β)
  proof: fun x hx y hy _ _ ha hb hab =>
  ⟨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' (· in s) hx.1 hy.1)
          (Convex.combo_le_max x y ha hb hab)).trans_lt
      (max_rec' (f · < r) hx.2 hy.2)⟩

中文:
定理 MonotoneOn.convex_lt
  条件: (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β)
  证明: fun x hx y hy _ _ ha hb hab =>
  ⟨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' (· in s) hx.1 hy.1)
          (Convex.combo_le_max x y ha hb hab)).trans_lt
      (max_rec' (f · < r) hx.2 hy.2)⟩
-/
theorem MonotoneOn.convex_lt (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x in s | f x < r }) := fun x hx y hy _ _ ha hb hab =>
  ⟨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' (· in s) hx.1 hy.1)
          (Convex.combo_le_max x y ha hb hab)).trans_lt
      (max_rec' (f · < r) hx.2 hy.2)⟩

/--
theorem `MonotoneOn.convex_ge` / 定理 `MonotoneOn.convex_ge`

English:
theorem MonotoneOn.convex_ge
  given: (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β)
  proof: MonotoneOn.convex_le (E := Eᵒᵈ) (β := βᵒᵈ) hf.dual (by exact hs) r

中文:
定理 MonotoneOn.convex_ge
  条件: (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β)
  证明: MonotoneOn.convex_le (E := Eᵒᵈ) (β := βᵒᵈ) hf.dual (by exact hs) r

Depends on / 依赖: MonotoneOn, MonotoneOn.convex_le, convex_le, hf.dual
-/
theorem MonotoneOn.convex_ge (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x in s | r <= f x }) :=
  MonotoneOn.convex_le (E := Eᵒᵈ) (β := βᵒᵈ) hf.dual (by exact hs) r

/--
theorem `MonotoneOn.convex_gt` / 定理 `MonotoneOn.convex_gt`

English:
theorem MonotoneOn.convex_gt
  given: (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β)
  proof: MonotoneOn.convex_lt (E := Eᵒᵈ) (β := βᵒᵈ) hf.dual (by exact hs) r

中文:
定理 MonotoneOn.convex_gt
  条件: (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β)
  证明: MonotoneOn.convex_lt (E := Eᵒᵈ) (β := βᵒᵈ) hf.dual (by exact hs) r

Depends on / 依赖: MonotoneOn, MonotoneOn.convex_lt, convex_lt, hf.dual
-/
theorem MonotoneOn.convex_gt (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x in s | r < f x }) :=
  MonotoneOn.convex_lt (E := Eᵒᵈ) (β := βᵒᵈ) hf.dual (by exact hs) r

/--
theorem `AntitoneOn.convex_le` / 定理 `AntitoneOn.convex_le`

English:
theorem AntitoneOn.convex_le
  given: (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β)
  proof: MonotoneOn.convex_ge (β := βᵒᵈ) hf hs r

中文:
定理 AntitoneOn.convex_le
  条件: (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β)
  证明: MonotoneOn.convex_ge (β := βᵒᵈ) hf hs r

Depends on / 依赖: MonotoneOn, MonotoneOn.convex_ge, convex_ge
-/
theorem AntitoneOn.convex_le (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x in s | f x <= r }) :=
  MonotoneOn.convex_ge (β := βᵒᵈ) hf hs r

/--
theorem `AntitoneOn.convex_lt` / 定理 `AntitoneOn.convex_lt`

English:
theorem AntitoneOn.convex_lt
  given: (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β)
  proof: MonotoneOn.convex_gt (β := βᵒᵈ) hf hs r

中文:
定理 AntitoneOn.convex_lt
  条件: (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β)
  证明: MonotoneOn.convex_gt (β := βᵒᵈ) hf hs r

Depends on / 依赖: MonotoneOn, MonotoneOn.convex_gt, convex_gt
-/
theorem AntitoneOn.convex_lt (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x in s | f x < r }) :=
  MonotoneOn.convex_gt (β := βᵒᵈ) hf hs r

/--
theorem `AntitoneOn.convex_ge` / 定理 `AntitoneOn.convex_ge`

English:
theorem AntitoneOn.convex_ge
  given: (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β)
  proof: MonotoneOn.convex_le (β := βᵒᵈ) hf hs r

中文:
定理 AntitoneOn.convex_ge
  条件: (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β)
  证明: MonotoneOn.convex_le (β := βᵒᵈ) hf hs r

Depends on / 依赖: MonotoneOn, MonotoneOn.convex_le, convex_le
-/
theorem AntitoneOn.convex_ge (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x in s | r <= f x }) :=
  MonotoneOn.convex_le (β := βᵒᵈ) hf hs r

/--
theorem `AntitoneOn.convex_gt` / 定理 `AntitoneOn.convex_gt`

English:
theorem AntitoneOn.convex_gt
  given: (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β)
  proof: MonotoneOn.convex_lt (β := βᵒᵈ) hf hs r

中文:
定理 AntitoneOn.convex_gt
  条件: (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β)
  证明: MonotoneOn.convex_lt (β := βᵒᵈ) hf hs r

Depends on / 依赖: MonotoneOn, MonotoneOn.convex_lt, convex_lt
-/
theorem AntitoneOn.convex_gt (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x in s | r < f x }) :=
  MonotoneOn.convex_lt (β := βᵒᵈ) hf hs r

/--
theorem `Monotone.convex_le` / 定理 `Monotone.convex_le`

English:
theorem Monotone.convex_le
  given: (hf : Monotone f) (r : β)
  statement: Convex 𝕜 { x | f x <= r }
  proof: Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)

中文:
定理 Monotone.convex_le
  条件: (hf : Monotone f) (r : β)
  结论: Convex 𝕜 { x | f x <= r }
  证明: Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)

Depends on / 依赖: Set.sep_univ.subst, convex_le, convex_univ, hf.monotoneOn, monotoneOn, sep_univ
-/
theorem Monotone.convex_le (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x <= r } :=
  Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)

/--
theorem `Monotone.convex_lt` / 定理 `Monotone.convex_lt`

English:
theorem Monotone.convex_lt
  given: (hf : Monotone f) (r : β)
  statement: Convex 𝕜 { x | f x <= r }
  proof: Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)

中文:
定理 Monotone.convex_lt
  条件: (hf : Monotone f) (r : β)
  结论: Convex 𝕜 { x | f x <= r }
  证明: Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)

Depends on / 依赖: Set.sep_univ.subst, convex_le, convex_univ, hf.monotoneOn, monotoneOn, sep_univ
-/
theorem Monotone.convex_lt (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x <= r } :=
  Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)

/--
theorem `Monotone.convex_ge` / 定理 `Monotone.convex_ge`

English:
theorem Monotone.convex_ge
  given: (hf : Monotone f) (r : β)
  statement: Convex 𝕜 { x | r <= f x }
  proof: Set.sep_univ.subst ((hf.monotoneOn univ).convex_ge convex_univ r)

中文:
定理 Monotone.convex_ge
  条件: (hf : Monotone f) (r : β)
  结论: Convex 𝕜 { x | r <= f x }
  证明: Set.sep_univ.subst ((hf.monotoneOn univ).convex_ge convex_univ r)

Depends on / 依赖: Set.sep_univ.subst, convex_ge, convex_univ, hf.monotoneOn, monotoneOn, sep_univ
-/
theorem Monotone.convex_ge (hf : Monotone f) (r : β) : Convex 𝕜 { x | r <= f x } :=
  Set.sep_univ.subst ((hf.monotoneOn univ).convex_ge convex_univ r)

/--
theorem `Monotone.convex_gt` / 定理 `Monotone.convex_gt`

English:
theorem Monotone.convex_gt
  given: (hf : Monotone f) (r : β)
  statement: Convex 𝕜 { x | f x <= r }
  proof: Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)

中文:
定理 Monotone.convex_gt
  条件: (hf : Monotone f) (r : β)
  结论: Convex 𝕜 { x | f x <= r }
  证明: Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)

Depends on / 依赖: Set.sep_univ.subst, convex_le, convex_univ, hf.monotoneOn, monotoneOn, sep_univ
-/
theorem Monotone.convex_gt (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x <= r } :=
  Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)

/--
theorem `Antitone.convex_le` / 定理 `Antitone.convex_le`

English:
theorem Antitone.convex_le
  given: (hf : Antitone f) (r : β)
  statement: Convex 𝕜 { x | f x <= r }
  proof: Set.sep_univ.subst ((hf.antitoneOn univ).convex_le convex_univ r)

中文:
定理 Antitone.convex_le
  条件: (hf : Antitone f) (r : β)
  结论: Convex 𝕜 { x | f x <= r }
  证明: Set.sep_univ.subst ((hf.antitoneOn univ).convex_le convex_univ r)

Depends on / 依赖: Set.sep_univ.subst, antitoneOn, convex_le, convex_univ, hf.antitoneOn, sep_univ
-/
theorem Antitone.convex_le (hf : Antitone f) (r : β) : Convex 𝕜 { x | f x <= r } :=
  Set.sep_univ.subst ((hf.antitoneOn univ).convex_le convex_univ r)

/--
theorem `Antitone.convex_lt` / 定理 `Antitone.convex_lt`

English:
theorem Antitone.convex_lt
  given: (hf : Antitone f) (r : β)
  statement: Convex 𝕜 { x | f x < r }
  proof: Set.sep_univ.subst ((hf.antitoneOn univ).convex_lt convex_univ r)

中文:
定理 Antitone.convex_lt
  条件: (hf : Antitone f) (r : β)
  结论: Convex 𝕜 { x | f x < r }
  证明: Set.sep_univ.subst ((hf.antitoneOn univ).convex_lt convex_univ r)

Depends on / 依赖: Set.sep_univ.subst, antitoneOn, convex_lt, convex_univ, hf.antitoneOn, sep_univ
-/
theorem Antitone.convex_lt (hf : Antitone f) (r : β) : Convex 𝕜 { x | f x < r } :=
  Set.sep_univ.subst ((hf.antitoneOn univ).convex_lt convex_univ r)

/--
theorem `Antitone.convex_ge` / 定理 `Antitone.convex_ge`

English:
theorem Antitone.convex_ge
  given: (hf : Antitone f) (r : β)
  statement: Convex 𝕜 { x | r <= f x }
  proof: Set.sep_univ.subst ((hf.antitoneOn univ).convex_ge convex_univ r)

中文:
定理 Antitone.convex_ge
  条件: (hf : Antitone f) (r : β)
  结论: Convex 𝕜 { x | r <= f x }
  证明: Set.sep_univ.subst ((hf.antitoneOn univ).convex_ge convex_univ r)

Depends on / 依赖: Set.sep_univ.subst, antitoneOn, convex_ge, convex_univ, hf.antitoneOn, sep_univ
-/
theorem Antitone.convex_ge (hf : Antitone f) (r : β) : Convex 𝕜 { x | r <= f x } :=
  Set.sep_univ.subst ((hf.antitoneOn univ).convex_ge convex_univ r)

/--
theorem `Antitone.convex_gt` / 定理 `Antitone.convex_gt`

English:
theorem Antitone.convex_gt
  given: (hf : Antitone f) (r : β)
  statement: Convex 𝕜 { x | r < f x }
  proof: Set.sep_univ.subst ((hf.antitoneOn univ).convex_gt convex_univ r)

中文:
定理 Antitone.convex_gt
  条件: (hf : Antitone f) (r : β)
  结论: Convex 𝕜 { x | r < f x }
  证明: Set.sep_univ.subst ((hf.antitoneOn univ).convex_gt convex_univ r)

Depends on / 依赖: Set.sep_univ.subst, antitoneOn, convex_gt, convex_univ, hf.antitoneOn, sep_univ
-/
theorem Antitone.convex_gt (hf : Antitone f) (r : β) : Convex 𝕜 { x | r < f x } :=
  Set.sep_univ.subst ((hf.antitoneOn univ).convex_gt convex_univ r)

end LinearOrderedAddCommMonoid

end OrderedSemiring

section OrderedCommSemiring

variable [CommSemiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

/--
theorem `Convex.smul` / 定理 `Convex.smul`

English:
theorem Convex.smul
  given: (hs : Convex 𝕜 s) (c : 𝕜)
  statement: Convex 𝕜 (c • s)
  proof: hs.linear_image (LinearMap.lsmul _ _ c)

中文:
定理 Convex.smul
  条件: (hs : Convex 𝕜 s) (c : 𝕜)
  结论: Convex 𝕜 (c • s)
  证明: hs.linear_image (LinearMap.lsmul _ _ c)

Depends on / 依赖: LinearMap, LinearMap.lsmul, hs.linear_image, linear_image
-/
theorem Convex.smul (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 (c • s) :=
  hs.linear_image (LinearMap.lsmul _ _ c)

/--
theorem `Convex.smul_preimage` / 定理 `Convex.smul_preimage`

English:
theorem Convex.smul_preimage
  given: (hs : Convex 𝕜 s) (c : 𝕜)
  statement: Convex 𝕜 ((fun z => c • z) ⁻¹' s)
  proof: hs.linear_preimage (LinearMap.lsmul _ _ c)

中文:
定理 Convex.smul_preimage
  条件: (hs : Convex 𝕜 s) (c : 𝕜)
  结论: Convex 𝕜 ((fun z => c • z) ⁻¹' s)
  证明: hs.linear_preimage (LinearMap.lsmul _ _ c)

Depends on / 依赖: LinearMap, LinearMap.lsmul, hs.linear_preimage, linear_preimage
-/
theorem Convex.smul_preimage (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 ((fun z => c • z) ⁻¹' s) :=
  hs.linear_preimage (LinearMap.lsmul _ _ c)

/--
theorem `Convex.affinity` / 定理 `Convex.affinity`

English:
theorem Convex.affinity
  given: (hs : Convex 𝕜 s) (z : E) (c : 𝕜)
  proof: by
  simpa only [← image_smul, ← image_vadd, image_image] using! (hs.smul c).vadd z

中文:
定理 Convex.affinity
  条件: (hs : Convex 𝕜 s) (z : E) (c : 𝕜)
  证明: by
  simpa only [← image_smul, ← image_vadd, image_image] using! (hs.smul c).vadd z

Depends on / 依赖: hs.smul, image_image, image_smul, image_vadd
-/
theorem Convex.affinity (hs : Convex 𝕜 s) (z : E) (c : 𝕜) :
    Convex 𝕜 ((fun x => z + c • x) '' s) := by
  simpa only [← image_smul, ← image_vadd, image_image] using! (hs.smul c).vadd z

end AddCommMonoid

end OrderedCommSemiring

section StrictOrderedCommSemiring

variable [CommSemiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

/--
theorem `convex_openSegment` / 定理 `convex_openSegment`

English:
theorem convex_openSegment
  given: (a b : E)
  statement: Convex 𝕜 (openSegment 𝕜 a b)
  proof: by
  rw [convex_iff_openSegment_subset]
  rintro p ⟨ap, bp, hap, hbp, habp, rfl⟩ q ⟨aq, bq, haq, hbq, habq, rfl⟩ z ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨a * ap + b * aq, a * bp + b * bq, by positivity, by positivity, ?_, ?_⟩
  · linear_combination (norm := noncomm_ring) a * habp + b * habq + hab
  · mo

中文:
定理 convex_openSegment
  条件: (a b : E)
  结论: Convex 𝕜 (openSegment 𝕜 a b)
  证明: by
  rw [convex_iff_openSegment_subset]
  rintro p ⟨ap, bp, hap, hbp, habp, rfl⟩ q ⟨aq, bq, haq, hbq, habq, rfl⟩ z ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨a * ap + b * aq, a * bp + b * bq, by positivity, by positivity, ?_, ?_⟩
  · linear_combination (norm := noncomm_ring) a * habp + b * habq + hab
  · mo

Depends on / 依赖: convex_iff_openSegment_subset, linear_combination, module, noncomm_ring
-/
theorem convex_openSegment (a b : E) : Convex 𝕜 (openSegment 𝕜 a b) := by
  rw [convex_iff_openSegment_subset]
  rintro p ⟨ap, bp, hap, hbp, habp, rfl⟩ q ⟨aq, bq, haq, hbq, habq, rfl⟩ z ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨a * ap + b * aq, a * bp + b * bq, by positivity, by positivity, ?_, ?_⟩
  · linear_combination (norm := noncomm_ring) a * habp + b * habq + hab
  · module

end StrictOrderedCommSemiring

section OrderedRing

variable [Ring 𝕜] [PartialOrder 𝕜]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s t : Set E}

@[simp]
/--
theorem `convex_vadd` / 定理 `convex_vadd`

English:
theorem convex_vadd
  given: (a : E)
  statement: Convex 𝕜 (a +ᵥ s) ↔ Convex 𝕜 s
  proof: ⟨fun h => by simpa using h.vadd (-a), fun h => h.vadd _⟩

中文:
定理 convex_vadd
  条件: (a : E)
  结论: Convex 𝕜 (a +ᵥ s) ↔ Convex 𝕜 s
  证明: ⟨fun h => by simpa using h.vadd (-a), fun h => h.vadd _⟩

Depends on / 依赖: h.vadd
-/
theorem convex_vadd (a : E) : Convex 𝕜 (a +ᵥ s) ↔ Convex 𝕜 s :=
  ⟨fun h => by simpa using h.vadd (-a), fun h => h.vadd _⟩

/--
theorem `AffineSubspace.convex` / 定理 `AffineSubspace.convex`

English:
theorem AffineSubspace.convex
  given: (Q : AffineSubspace 𝕜 E)
  statement: Convex 𝕜 (Q : Set E)
  proof: fun x hx y hy a b _ _ hab => by simpa [Convex.combo_eq_smul_sub_add hab] using! Q.2 _ hy hx hx

中文:
定理 AffineSubspace.convex
  条件: (Q : AffineSubspace 𝕜 E)
  结论: Convex 𝕜 (Q : Set E)
  证明: fun x hx y hy a b _ _ hab => by simpa [Convex.combo_eq_smul_sub_add hab] using! Q.2 _ hy hx hx

Depends on / 依赖: Convex, Convex.combo_eq_smul_sub_add, combo_eq_smul_sub_add
-/
theorem AffineSubspace.convex (Q : AffineSubspace 𝕜 E) : Convex 𝕜 (Q : Set E) :=
  fun x hx y hy a b _ _ hab => by simpa [Convex.combo_eq_smul_sub_add hab] using! Q.2 _ hy hx hx

/--
theorem `Convex.affine_preimage` / 定理 `Convex.affine_preimage`

English:
theorem Convex.affine_preimage
  given: (f : E ->ᵃ[𝕜] F) {s : Set F} (hs : Convex 𝕜 s)
  statement: Convex 𝕜 (f ⁻¹' s)
  proof: fun _ hx => (hs hx).affine_preimage _

中文:
定理 Convex.affine_preimage
  条件: (f : E ->ᵃ[𝕜] F) {s : Set F} (hs : Convex 𝕜 s)
  结论: Convex 𝕜 (f ⁻¹' s)
  证明: fun _ hx => (hs hx).affine_preimage _

Depends on / 依赖: affine_preimage
-/
theorem Convex.affine_preimage (f : E ->ᵃ[𝕜] F) {s : Set F} (hs : Convex 𝕜 s) : Convex 𝕜 (f ⁻¹' s) :=
  fun _ hx => (hs hx).affine_preimage _

/--
theorem `Convex.affine_image` / 定理 `Convex.affine_image`

English:
theorem Convex.affine_image
  given: (f : E ->ᵃ[𝕜] F) (hs : Convex 𝕜 s)
  statement: Convex 𝕜 (f '' s)
  proof: by
  rintro _ ⟨x, hx, rfl⟩
  exact (hs hx).affine_image _

中文:
定理 Convex.affine_image
  条件: (f : E ->ᵃ[𝕜] F) (hs : Convex 𝕜 s)
  结论: Convex 𝕜 (f '' s)
  证明: by
  rintro _ ⟨x, hx, rfl⟩
  exact (hs hx).affine_image _

Depends on / 依赖: affine_image
-/
theorem Convex.affine_image (f : E ->ᵃ[𝕜] F) (hs : Convex 𝕜 s) : Convex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  exact (hs hx).affine_image _

/--
theorem `Convex.neg` / 定理 `Convex.neg`

English:
theorem Convex.neg
  given: (hs : Convex 𝕜 s)
  statement: Convex 𝕜 (-s)
  proof: hs.is_linear_preimage IsLinearMap.isLinearMap_neg

中文:
定理 Convex.neg
  条件: (hs : Convex 𝕜 s)
  结论: Convex 𝕜 (-s)
  证明: hs.is_linear_preimage IsLinearMap.isLinearMap_neg

Depends on / 依赖: IsLinearMap, IsLinearMap.isLinearMap_neg, hs.is_linear_preimage, isLinearMap_neg, is_linear_preimage
-/
theorem Convex.neg (hs : Convex 𝕜 s) : Convex 𝕜 (-s) :=
  hs.is_linear_preimage IsLinearMap.isLinearMap_neg

/--
theorem `Convex.sub` / 定理 `Convex.sub`

English:
theorem Convex.sub
  given: (hs : Convex 𝕜 s) (ht : Convex 𝕜 t)
  statement: Convex 𝕜 (s - t)
  proof: by
  rw [sub_eq_add_neg]
  exact hs.add ht.neg

中文:
定理 Convex.sub
  条件: (hs : Convex 𝕜 s) (ht : Convex 𝕜 t)
  结论: Convex 𝕜 (s - t)
  证明: by
  rw [sub_eq_add_neg]
  exact hs.add ht.neg

Depends on / 依赖: hs.add, ht.neg, sub_eq_add_neg
-/
theorem Convex.sub (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s - t) := by
  rw [sub_eq_add_neg]
  exact hs.add ht.neg

variable [AddRightMono 𝕜]

/--
theorem `Convex.add_smul_mem` / 定理 `Convex.add_smul_mem`

English:
theorem Convex.add_smul_mem
  statement: (hs : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : x + y in s) {t : 𝕜}
  proof: by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by match_scalars <;> noncomm_ring
  rw [h]
  exact hs hx hy (sub_nonneg_of_le ht.2) ht.1 (sub_add_cancel _ _)

中文:
定理 Convex.add_smul_mem
  结论: (hs : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : x + y in s) {t : 𝕜}
  证明: by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by match_scalars <;> noncomm_ring
  rw [h]
  exact hs hx hy (sub_nonneg_of_le ht.2) ht.1 (sub_add_cancel _ _)

Depends on / 依赖: match_scalars, noncomm_ring, sub_add_cancel, sub_nonneg_of_le
-/
theorem Convex.add_smul_mem (hs : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : x + y in s) {t : 𝕜}
    (ht : t in Icc (0 : 𝕜) 1) : x + t • y in s := by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by match_scalars <;> noncomm_ring
  rw [h]
  exact hs hx hy (sub_nonneg_of_le ht.2) ht.1 (sub_add_cancel _ _)

/--
theorem `Convex.smul_mem_of_zero_mem` / 定理 `Convex.smul_mem_of_zero_mem`

English:
theorem Convex.smul_mem_of_zero_mem
  statement: (hs : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) in s) (hx : x in s)
  proof: by
  simpa using hs.add_smul_mem zero_mem (by simpa using hx) ht

中文:
定理 Convex.smul_mem_of_zero_mem
  结论: (hs : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) in s) (hx : x in s)
  证明: by
  simpa using hs.add_smul_mem zero_mem (by simpa using hx) ht

Depends on / 依赖: add_smul_mem, hs.add_smul_mem, zero_mem
-/
theorem Convex.smul_mem_of_zero_mem (hs : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) in s) (hx : x in s)
    {t : 𝕜} (ht : t in Icc (0 : 𝕜) 1) : t • x in s := by
  simpa using hs.add_smul_mem zero_mem (by simpa using hx) ht

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Convex.mapsTo_lineMap` / 定理 `Convex.mapsTo_lineMap`

English:
theorem Convex.mapsTo_lineMap
  given: (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in s)
  proof: by
  simpa only [mapsTo_iff_image_subset, segment_eq_image_lineMap] using h.segment_subset hx hy

中文:
定理 Convex.mapsTo_lineMap
  条件: (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in s)
  证明: by
  simpa only [mapsTo_iff_image_subset, segment_eq_image_lineMap] using h.segment_subset hx hy

Depends on / 依赖: h.segment_subset, mapsTo_iff_image_subset, segment_eq_image_lineMap, segment_subset
-/
theorem Convex.mapsTo_lineMap (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in s) :
    MapsTo (AffineMap.lineMap x y) (Icc (0 : 𝕜) 1) s := by
  simpa only [mapsTo_iff_image_subset, segment_eq_image_lineMap] using h.segment_subset hx hy

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Convex.lineMap_mem` / 定理 `Convex.lineMap_mem`

English:
theorem Convex.lineMap_mem
  statement: (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in s) {t : 𝕜}
  proof: h.mapsTo_lineMap hx hy ht

中文:
定理 Convex.lineMap_mem
  结论: (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in s) {t : 𝕜}
  证明: h.mapsTo_lineMap hx hy ht

Depends on / 依赖: h.mapsTo_lineMap, mapsTo_lineMap
-/
theorem Convex.lineMap_mem (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in s) {t : 𝕜}
    (ht : t in Icc 0 1) : AffineMap.lineMap x y t in s :=
  h.mapsTo_lineMap hx hy ht

/--
theorem `Convex.add_smul_sub_mem` / 定理 `Convex.add_smul_sub_mem`

English:
theorem Convex.add_smul_sub_mem
  statement: (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in s) {t : 𝕜}
  proof: by
  rw [add_comm]
  exact h.lineMap_mem hx hy ht

中文:
定理 Convex.add_smul_sub_mem
  结论: (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in s) {t : 𝕜}
  证明: by
  rw [add_comm]
  exact h.lineMap_mem hx hy ht

Depends on / 依赖: add_comm, h.lineMap_mem, lineMap_mem
-/
theorem Convex.add_smul_sub_mem (h : Convex 𝕜 s) {x y : E} (hx : x in s) (hy : y in s) {t : 𝕜}
    (ht : t in Icc (0 : 𝕜) 1) : x + t • (y - x) in s := by
  rw [add_comm]
  exact h.lineMap_mem hx hy ht

end AddCommGroup

end OrderedRing

section LinearOrder

variable [Semiring 𝕜] [AddCommMonoid E]
section SemilinearMap

variable [PartialOrder 𝕜]
variable {𝕜' : Type*} [Semiring 𝕜'] [PartialOrder 𝕜']
variable {σ : 𝕜 ->+* 𝕜'} [RingHomSurjective σ]
variable {F' : Type*} [AddCommMonoid F'] [Module 𝕜' F'] [Module 𝕜 E]

/--
theorem `Convex.semilinear_image` / 定理 `Convex.semilinear_image`

English:
theorem Convex.semilinear_image
  statement: {s : Set E} (hs : Convex 𝕜 s) (hσ : forall {s t}, σ s <= σ t ↔ s <= t)
  proof: by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  obtain ⟨r, rfl⟩ : exists r : 𝕜, σ r = a := RingHomSurjective.is_surjective ..
  obtain ⟨t, rfl⟩ : exists t : 𝕜, σ t = b := RingHomSurjective.is_surjective ..
  refine ⟨r • x + t • y, hs hx hy (by simp_all [(@hσ 0 r).mp]) (by simp_all [(@hσ 0 

中文:
定理 Convex.semilinear_image
  结论: {s : Set E} (hs : Convex 𝕜 s) (hσ : 对任意 {s t}, σ s <= σ t ↔ s <= t)
  证明: by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  obtain ⟨r, rfl⟩ : exists r : 𝕜, σ r = a := RingHomSurjective.is_surjective ..
  obtain ⟨t, rfl⟩ : exists t : 𝕜, σ t = b := RingHomSurjective.is_surjective ..
  refine ⟨r • x + t • y, hs hx hy (by simp_all [(@hσ 0 r).mp]) (by simp_all [(@hσ 0 

Depends on / 依赖: Function, Function.Injective.of_eq_imp_le, Injective, RingHomSurjective, RingHomSurjective.is_surjective, apply_fun, is_surjective, of_eq_imp_le
-/
theorem Convex.semilinear_image {s : Set E} (hs : Convex 𝕜 s) (hσ : forall {s t}, σ s <= σ t ↔ s <= t)
    (f : E ->ₛₗ[σ] F') : Convex 𝕜' (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  obtain ⟨r, rfl⟩ : exists r : 𝕜, σ r = a := RingHomSurjective.is_surjective ..
  obtain ⟨t, rfl⟩ : exists t : 𝕜, σ t = b := RingHomSurjective.is_surjective ..
  refine ⟨r • x + t • y, hs hx hy (by simp_all [(@hσ 0 r).mp]) (by simp_all [(@hσ 0 t).mp])
    ?_, by simp⟩
  apply_fun σ using Function.Injective.of_eq_imp_le (hσ.mp ·.le)
  simpa

end SemilinearMap

variable [LinearOrder 𝕜] [IsOrderedRing 𝕜]

/--
theorem `Convex_subadditive_le` / 定理 `Convex_subadditive_le`

English:
theorem Convex_subadditive_le
  statement: [SMul 𝕜 E] {f : E -> 𝕜} (hf1 : forall x y, f (x + y) <= (f x) + (f y))
  proof: by
  rw [convex_iff_segment_subset]
  rintro x hx y hy z ⟨a, b, ha, hb, hs, rfl⟩
  calc
    _ <= a • (f x) + b • (f y) := le_trans (hf1 _ _) (add_le_add (hf2 x ha) (hf2 y hb))
    _ <= a • B + b • B := by gcongr <;> assumption
    _ <= B := by rw [← add_smul, hs, one_smul]

中文:
定理 Convex_subadditive_le
  结论: [SMul 𝕜 E] {f : E -> 𝕜} (hf1 : 对任意 x y, f (x + y) <= (f x) + (f y))
  证明: by
  rw [convex_iff_segment_subset]
  rintro x hx y hy z ⟨a, b, ha, hb, hs, rfl⟩
  calc
    _ <= a • (f x) + b • (f y) := le_trans (hf1 _ _) (add_le_add (hf2 x ha) (hf2 y hb))
    _ <= a • B + b • B := by gcongr <;> assumption
    _ <= B := by rw [← add_smul, hs, one_smul]

Depends on / 依赖: add_le_add, add_smul, convex_iff_segment_subset, le_trans, one_smul
-/
theorem Convex_subadditive_le [SMul 𝕜 E] {f : E -> 𝕜} (hf1 : forall x y, f (x + y) <= (f x) + (f y))
    (hf2 : forall ⦃c⦄ x, 0 <= c -> f (c • x) <= c * f x) (B : 𝕜) :
    Convex 𝕜 { x | f x <= B } := by
  rw [convex_iff_segment_subset]
  rintro x hx y hy z ⟨a, b, ha, hb, hs, rfl⟩
  calc
    _ <= a • (f x) + b • (f y) := le_trans (hf1 _ _) (add_le_add (hf2 x ha) (hf2 y hb))
    _ <= a • B + b • B := by gcongr <;> assumption
    _ <= B := by rw [← add_smul, hs, one_smul]

end LinearOrder

/--
theorem `Convex.midpoint_mem` / 定理 `Convex.midpoint_mem`

English:
theorem Convex.midpoint_mem
  statement: [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  proof: h.segment_subset hx hy midpoint_mem_segment x y

中文:
定理 Convex.midpoint_mem
  结论: [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  证明: h.segment_subset hx hy midpoint_mem_segment x y

Depends on / 依赖: h.segment_subset, midpoint_mem_segment, segment_subset
-/
theorem Convex.midpoint_mem [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Invertible (2 : 𝕜)] {s : Set E} {x y : E}
    (h : Convex 𝕜 s) (hx : x in s) (hy : y in s) : midpoint 𝕜 x y in s :=
h.segment_subset hx hy midpoint_mem_segment x y

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

/--
theorem `convex_iff_div` / 定理 `convex_iff_div`

English:
theorem convex_iff_div
  proof: forall₂_congr fun _ _ => starConvex_iff_div

中文:
定理 convex_iff_div
  证明: forall₂_congr fun _ _ => starConvex_iff_div

Depends on / 依赖: starConvex_iff_div
-/
theorem convex_iff_div :
    Convex 𝕜 s ↔ forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s ->
      forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> 0 < a + b -> (a / (a + b)) • x + (b / (a + b)) • y in s :=
  forall₂_congr fun _ _ => starConvex_iff_div

/--
theorem `Convex.mem_smul_of_zero_mem` / 定理 `Convex.mem_smul_of_zero_mem`

English:
theorem Convex.mem_smul_of_zero_mem
  statement: (h : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) in s) (hx : x in s)
  proof: by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne']
  exact h.smul_mem_of_zero_mem zero_mem hx
    ⟨inv_nonneg.2 (zero_le_one.trans ht), inv_le_one_of_one_le₀ ht⟩

中文:
定理 Convex.mem_smul_of_zero_mem
  结论: (h : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) in s) (hx : x in s)
  证明: by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne']
  exact h.smul_mem_of_zero_mem zero_mem hx
    ⟨inv_nonneg.2 (zero_le_one.trans ht), inv_le_one_of_one_le₀ ht⟩

Depends on / 依赖: h.smul_mem_of_zero_mem, inv_nonneg, smul_mem_of_zero_mem, trans_le, zero_le_one, zero_le_one.trans, zero_lt_one, zero_lt_one.trans_le, zero_mem
-/
theorem Convex.mem_smul_of_zero_mem (h : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) in s) (hx : x in s)
    {t : 𝕜} (ht : 1 <= t) : x in t • s := by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne']
  exact h.smul_mem_of_zero_mem zero_mem hx
    ⟨inv_nonneg.2 (zero_le_one.trans ht), inv_le_one_of_one_le₀ ht⟩

/--
theorem `Convex.exists_mem_add_smul_eq` / 定理 `Convex.exists_mem_add_smul_eq`

English:
theorem Convex.exists_mem_add_smul_eq
  statement: (h : Convex 𝕜 s) {x y : E} {p q : 𝕜} (hx : x in s) (hy : y in s)
  proof: by
  rcases _root_.em (p = 0 ∧ q = 0) with (⟨rfl, rfl⟩ | hpq)
  · use x, hx
    simp
  · replace hpq : 0 < p + q :=
      (add_nonneg hp hq).lt_of_ne' (mt (add_eq_zero_iff_of_nonneg hp hq).1 hpq)
    refine ⟨_, convex_iff_div.1 h hx hy hp hq hpq, ?_⟩
    match_scalars <;> field

中文:
定理 Convex.exists_mem_add_smul_eq
  结论: (h : Convex 𝕜 s) {x y : E} {p q : 𝕜} (hx : x in s) (hy : y in s)
  证明: by
  rcases _root_.em (p = 0 ∧ q = 0) with (⟨rfl, rfl⟩ | hpq)
  · use x, hx
    simp
  · replace hpq : 0 < p + q :=
      (add_nonneg hp hq).lt_of_ne' (mt (add_eq_zero_iff_of_nonneg hp hq).1 hpq)
    refine ⟨_, convex_iff_div.1 h hx hy hp hq hpq, ?_⟩
    match_scalars <;> field

Depends on / 依赖: _root_, _root_.em, add_eq_zero_iff_of_nonneg, add_nonneg, convex_iff_div, lt_of_ne, match_scalars, replace
-/
theorem Convex.exists_mem_add_smul_eq (h : Convex 𝕜 s) {x y : E} {p q : 𝕜} (hx : x in s) (hy : y in s)
    (hp : 0 <= p) (hq : 0 <= q) : exists z in s, (p + q) • z = p • x + q • y := by
  rcases _root_.em (p = 0 ∧ q = 0) with (⟨rfl, rfl⟩ | hpq)
  · use x, hx
    simp
  · replace hpq : 0 < p + q :=
      (add_nonneg hp hq).lt_of_ne' (mt (add_eq_zero_iff_of_nonneg hp hq).1 hpq)
    refine ⟨_, convex_iff_div.1 h hx hy hp hq hpq, ?_⟩
    match_scalars <;> field

/--
theorem `Convex.add_smul` / 定理 `Convex.add_smul`

English:
theorem Convex.add_smul
  given: (h_conv : Convex 𝕜 s) {p q : 𝕜} (hp : 0 <= p) (hq : 0 <= q)
  proof: (add_smul_subset _ _ _).antisymm by
  rintro _ ⟨_, ⟨v₁, h₁, rfl⟩, _, ⟨v₂, h₂, rfl⟩, rfl⟩
  exact h_conv.exists_mem_add_smul_eq h₁ h₂ hp hq

中文:
定理 Convex.add_smul
  条件: (h_conv : Convex 𝕜 s) {p q : 𝕜} (hp : 0 <= p) (hq : 0 <= q)
  证明: (add_smul_subset _ _ _).antisymm by
  rintro _ ⟨_, ⟨v₁, h₁, rfl⟩, _, ⟨v₂, h₂, rfl⟩, rfl⟩
  exact h_conv.exists_mem_add_smul_eq h₁ h₂ hp hq
-/
protected theorem Convex.add_smul (h_conv : Convex 𝕜 s) {p q : 𝕜} (hp : 0 <= p) (hq : 0 <= q) :
(p + q) • s = p • s + q • s := (add_smul_subset _ _ _).antisymm by
  rintro _ ⟨_, ⟨v₁, h₁, rfl⟩, _, ⟨v₂, h₂, rfl⟩, rfl⟩
  exact h_conv.exists_mem_add_smul_eq h₁ h₂ hp hq

/--
theorem `Convex.add_half_self_eq_self` / 定理 `Convex.add_half_self_eq_self`

English:
theorem Convex.add_half_self_eq_self
  given: (h_conv : Convex 𝕜 s)
  statement: (2 : 𝕜)⁻¹ • s + (2 : 𝕜)⁻¹ • s = s
  proof: by
  rw [← h_conv.add_smul (by norm_num) (by norm_num)]
  ring_nf
  rw [one_smul]

中文:
定理 Convex.add_half_self_eq_self
  条件: (h_conv : Convex 𝕜 s)
  结论: (2 : 𝕜)⁻¹ • s + (2 : 𝕜)⁻¹ • s = s
  证明: by
  rw [← h_conv.add_smul (by norm_num) (by norm_num)]
  ring_nf
  rw [one_smul]

Depends on / 依赖: add_smul, h_conv, h_conv.add_smul, one_smul, ring_nf
-/
theorem Convex.add_half_self_eq_self (h_conv : Convex 𝕜 s) : (2 : 𝕜)⁻¹ • s + (2 : 𝕜)⁻¹ • s = s := by
  rw [← h_conv.add_smul (by norm_num) (by norm_num)]
  ring_nf
  rw [one_smul]

end AddCommGroup

end LinearOrderedField

/-!
#### Convex sets in an ordered space
Relates `Convex` and `OrdConnected`.
-/


section

/--
theorem `Set.OrdConnected.convex_of_chain` / 定理 `Set.OrdConnected.convex_of_chain`

English:
theorem Set.OrdConnected.convex_of_chain
  statement: [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
  proof: by
  refine convex_iff_segment_subset.mpr fun x hx y hy => ?_
  obtain hxy | hyx := h.total hx hy
  · exact (segment_subset_Icc hxy).trans (hs.out hx hy)
  · rw [segment_symm]
    exact (segment_subset_Icc hyx).trans (hs.out hy hx)

中文:
定理 Set.OrdConnected.convex_of_chain
  结论: [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
  证明: by
  refine convex_iff_segment_subset.mpr fun x hx y hy => ?_
  obtain hxy | hyx := h.total hx hy
  · exact (segment_subset_Icc hxy).trans (hs.out hx hy)
  · rw [segment_symm]
    exact (segment_subset_Icc hyx).trans (hs.out hy hx)

Depends on / 依赖: convex_iff_segment_subset, convex_iff_segment_subset.mpr, h.total, hs.out, segment_subset_Icc, segment_symm
-/
theorem Set.OrdConnected.convex_of_chain [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
    [PartialOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E] {s : Set E}
    (hs : s.OrdConnected) (h : IsChain (· <= ·) s) : Convex 𝕜 s := by
  refine convex_iff_segment_subset.mpr fun x hx y hy => ?_
  obtain hxy | hyx := h.total hx hy
  · exact (segment_subset_Icc hxy).trans (hs.out hx hy)
  · rw [segment_symm]
    exact (segment_subset_Icc hyx).trans (hs.out hy hx)

/--
theorem `Set.OrdConnected.convex` / 定理 `Set.OrdConnected.convex`

English:
theorem Set.OrdConnected.convex
  statement: [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [LinearOrder E]
  proof: hs.convex_of_chain isChain_of_trichotomous s

中文:
定理 Set.OrdConnected.convex
  结论: [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [LinearOrder E]
  证明: hs.convex_of_chain isChain_of_trichotomous s

Depends on / 依赖: convex_of_chain, hs.convex_of_chain, isChain_of_trichotomous
-/
theorem Set.OrdConnected.convex [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [LinearOrder E]
    [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E] {s : Set E} (hs : s.OrdConnected) :
    Convex 𝕜 s :=
hs.convex_of_chain isChain_of_trichotomous s

/--
theorem `convex_iff_ordConnected` / 定理 `convex_iff_ordConnected`

English:
theorem convex_iff_ordConnected
  given: [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜}
  proof: by
  simp_rw [convex_iff_segment_subset, segment_eq_uIcc, ordConnected_iff_uIcc_subset]

alias ⟨Convex.ordConnected, _⟩ := convex_iff_ordConnected

中文:
定理 convex_iff_ordConnected
  条件: [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜}
  证明: by
  simp_rw [convex_iff_segment_subset, segment_eq_uIcc, ordConnected_iff_uIcc_subset]

alias ⟨Convex.ordConnected, _⟩ := convex_iff_ordConnected

Depends on / 依赖: convex_iff_segment_subset, ordConnected_iff_uIcc_subset, segment_eq_uIcc, simp_rw
-/
theorem convex_iff_ordConnected [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜} :
    Convex 𝕜 s ↔ s.OrdConnected := by
  simp_rw [convex_iff_segment_subset, segment_eq_uIcc, ordConnected_iff_uIcc_subset]

alias ⟨Convex.ordConnected, _⟩ := convex_iff_ordConnected

end

/-! #### Convexity of submodules/subspaces -/


namespace Submodule

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]

/--
theorem `convex` / 定理 `convex`

English:
theorem convex
  given: (K : Submodule 𝕜 E)
  statement: Convex 𝕜 (↑K : Set E)
  proof: by
  repeat' intro
  refine add_mem (smul_mem _ _ ?_) (smul_mem _ _ ?_) <;> assumption

中文:
定理 convex
  条件: (K : Submodule 𝕜 E)
  结论: Convex 𝕜 (↑K : Set E)
  证明: by
  repeat' intro
  refine add_mem (smul_mem _ _ ?_) (smul_mem _ _ ?_) <;> assumption
-/
protected theorem convex (K : Submodule 𝕜 E) : Convex 𝕜 (↑K : Set E) := by
  repeat' intro
  refine add_mem (smul_mem _ _ ?_) (smul_mem _ _ ?_) <;> assumption

/--
theorem `starConvex` / 定理 `starConvex`

English:
theorem starConvex
  given: (K : Submodule 𝕜 E)
  statement: StarConvex 𝕜 (0 : E) K
  proof: K.convex K.zero_mem

中文:
定理 starConvex
  条件: (K : Submodule 𝕜 E)
  结论: StarConvex 𝕜 (0 : E) K
  证明: K.convex K.zero_mem
-/
protected theorem starConvex (K : Submodule 𝕜 E) : StarConvex 𝕜 (0 : E) K :=
  K.convex K.zero_mem

/--
theorem `Convex.semilinear_range` / 定理 `Convex.semilinear_range`

English:
theorem Convex.semilinear_range
  statement: {𝕜' : Type*} [Semiring 𝕜'] {σ : 𝕜' ->+* 𝕜}
  proof: Submodule.convex ..

中文:
定理 Convex.semilinear_range
  结论: {𝕜' : 类型} [Semiring 𝕜'] {σ : 𝕜' ->+* 𝕜}
  证明: Submodule.convex ..

Depends on / 依赖: Submodule, Submodule.convex, convex
-/
theorem Convex.semilinear_range {𝕜' : Type*} [Semiring 𝕜'] {σ : 𝕜' ->+* 𝕜}
    [RingHomSurjective σ] {F' : Type*} [AddCommMonoid F'] [Module 𝕜' F']
    (f : F' ->ₛₗ[σ] E) : Convex 𝕜 (LinearMap.range f : Set E) := Submodule.convex ..

end Submodule

section CommSemiring

variable {R : Type*} [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]
variable {M : Type*} [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]
variable [PartialOrder R] [PartialOrder A]

/--
lemma `convex_of_nonneg_surjective_algebraMap` / 引理 `convex_of_nonneg_surjective_algebraMap`

English:
lemma convex_of_nonneg_surjective_algebraMap
  statement: [FaithfulSMul R A] {s : Set M}
  proof: by
  simp only [Convex, StarConvex] at hs ⊢
  intro u hu v hv a b ha hb hab
  obtain ⟨c, hc1, hc2⟩ := halg ha
  obtain ⟨d, hd1, hd2⟩ := halg hb
  convert hs hu hv hc1 hd1 _
  · rw [← hc2, algebraMap_smul]
  · rw [← hd2, algebraMap_smul]
  rw [← hc2]; rw [← hd2]; rw [← algebraMap.coe_add] at hab
  ex

中文:
引理 convex_of_nonneg_surjective_algebraMap
  结论: [FaithfulSMul R A] {s : Set M}
  证明: by
  simp only [Convex, StarConvex] at hs ⊢
  intro u hu v hv a b ha hb hab
  obtain ⟨c, hc1, hc2⟩ := halg ha
  obtain ⟨d, hd1, hd2⟩ := halg hb
  convert hs hu hv hc1 hd1 _
  · rw [← hc2, algebraMap_smul]
  · rw [← hd2, algebraMap_smul]
  rw [← hc2]; rw [← hd2]; rw [← algebraMap.coe_add] at hab
  ex

Depends on / 依赖: Convex, FaithfulSMul, FaithfulSMul.algebraMap_eq_one_iff, StarConvex, algebraMap, algebraMap.coe_add, algebraMap_eq_one_iff, algebraMap_smul, coe_add, convert
-/
lemma convex_of_nonneg_surjective_algebraMap [FaithfulSMul R A] {s : Set M}
    (halg : Set.Ici 0 subseteq algebraMap R A '' Set.Ici 0) (hs : Convex R s) :
    Convex A s := by
  simp only [Convex, StarConvex] at hs ⊢
  intro u hu v hv a b ha hb hab
  obtain ⟨c, hc1, hc2⟩ := halg ha
  obtain ⟨d, hd1, hd2⟩ := halg hb
  convert hs hu hv hc1 hd1 _
  · rw [← hc2, algebraMap_smul]
  · rw [← hd2, algebraMap_smul]
  rw [← hc2]; rw [← hd2]; rw [← algebraMap.coe_add] at hab
  exact (FaithfulSMul.algebraMap_eq_one_iff R A).mp hab

end CommSemiring
