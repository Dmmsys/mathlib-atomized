/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Order.Basic

/-!
# Strictly convex sets

This file defines strictly convex sets.

A set is strictly convex if the open segment between any two distinct points lies in its interior.
-/

@[expose] public section


open Set

open Convex Pointwise

variable {𝕜 𝕝 E F β : Type*}

open Function Set

open Convex

section OrderedSemiring

/--
Definition of `StrictConvex` / `StrictConvex` 的定义

English:
definition StrictConvex
  signature: (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [TopologicalSpace E]
  body: s.Pairwise fun x y => forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • x + b • y in interior s

中文:
定义 StrictConvex
  签名: (𝕜 : 类型) {E : 类型} [Semiring 𝕜] [PartialOrder 𝕜] [TopologicalSpace E]
  定义体: s.Pairwise fun x y => forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • x + b • y in interior s

Depends on / 依赖: Pairwise, interior, s.Pairwise
-/
def StrictConvex (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [TopologicalSpace E]
    [AddCommMonoid E] [SMul 𝕜 E] (s : Set E) : Prop :=
  s.Pairwise fun x y => forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • x + b • y in interior s

variable [Semiring 𝕜] [PartialOrder 𝕜] [TopologicalSpace E] [TopologicalSpace F]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section SMul

variable [SMul 𝕜 E] [SMul 𝕜 F] (s : Set E)

variable {s}
variable {x y : E} {a b : 𝕜}

/--
theorem `strictConvex_iff_openSegment_subset` / 定理 `strictConvex_iff_openSegment_subset`

English:
theorem strictConvex_iff_openSegment_subset
  proof: forall₅_congr fun _ _ _ _ _ => (openSegment_subset_iff 𝕜).symm

中文:
定理 strictConvex_iff_openSegment_subset
  证明: forall₅_congr fun _ _ _ _ _ => (openSegment_subset_iff 𝕜).symm

Depends on / 依赖: openSegment_subset_iff
-/
theorem strictConvex_iff_openSegment_subset :
    StrictConvex 𝕜 s ↔ s.Pairwise fun x y => openSegment 𝕜 x y subseteq interior s :=
  forall₅_congr fun _ _ _ _ _ => (openSegment_subset_iff 𝕜).symm

/--
theorem `StrictConvex.openSegment_subset` / 定理 `StrictConvex.openSegment_subset`

English:
theorem StrictConvex.openSegment_subset
  statement: (hs : StrictConvex 𝕜 s) (hx : x in s) (hy : y in s)
  proof: strictConvex_iff_openSegment_subset.1 hs hx hy h

中文:
定理 StrictConvex.openSegment_subset
  结论: (hs : StrictConvex 𝕜 s) (hx : x in s) (hy : y in s)
  证明: strictConvex_iff_openSegment_subset.1 hs hx hy h

Depends on / 依赖: strictConvex_iff_openSegment_subset
-/
theorem StrictConvex.openSegment_subset (hs : StrictConvex 𝕜 s) (hx : x in s) (hy : y in s)
    (h : x != y) : openSegment 𝕜 x y subseteq interior s :=
  strictConvex_iff_openSegment_subset.1 hs hx hy h

/--
theorem `strictConvex_empty` / 定理 `strictConvex_empty`

English:
theorem strictConvex_empty
  statement: StrictConvex 𝕜 (∅ : Set E)
  proof: pairwise_empty _

中文:
定理 strictConvex_empty
  结论: StrictConvex 𝕜 (∅ : Set E)
  证明: pairwise_empty _

Depends on / 依赖: pairwise_empty
-/
theorem strictConvex_empty : StrictConvex 𝕜 (∅ : Set E) :=
  pairwise_empty _

/--
theorem `strictConvex_univ` / 定理 `strictConvex_univ`

English:
theorem strictConvex_univ
  statement: StrictConvex 𝕜 (univ : Set E)
  proof: by
  intro x _ y _ _ a b _ _ _
  rw [interior_univ]
  exact mem_univ _

protected nonrec theorem StrictConvex.eq (hs : StrictConvex 𝕜 s) (hx : x in s) (hy : y in s)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (h : a • x + b • y ∉ interior s) : x = y :=
hs.eq hx hy fun H => h H ha hb hab

中文:
定理 strictConvex_univ
  结论: StrictConvex 𝕜 (univ : Set E)
  证明: by
  intro x _ y _ _ a b _ _ _
  rw [interior_univ]
  exact mem_univ _

protected nonrec theorem StrictConvex.eq (hs : StrictConvex 𝕜 s) (hx : x in s) (hy : y in s)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (h : a • x + b • y ∉ interior s) : x = y :=
hs.eq hx hy fun H => h H ha hb hab

Depends on / 依赖: interior_univ, mem_univ
-/
theorem strictConvex_univ : StrictConvex 𝕜 (univ : Set E) := by
  intro x _ y _ _ a b _ _ _
  rw [interior_univ]
  exact mem_univ _

protected nonrec theorem StrictConvex.eq (hs : StrictConvex 𝕜 s) (hx : x in s) (hy : y in s)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (h : a • x + b • y ∉ interior s) : x = y :=
hs.eq hx hy fun H => h H ha hb hab

/--
theorem `StrictConvex.inter` / 定理 `StrictConvex.inter`

English:
theorem StrictConvex.inter
  given: {t : Set E} (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t)
  proof: by
  intro x hx y hy hxy a b ha hb hab
  rw [interior_inter]
  exact ⟨hs hx.1 hy.1 hxy ha hb hab, ht hx.2 hy.2 hxy ha hb hab⟩

中文:
定理 StrictConvex.inter
  条件: {t : Set E} (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t)
  证明: by
  intro x hx y hy hxy a b ha hb hab
  rw [interior_inter]
  exact ⟨hs hx.1 hy.1 hxy ha hb hab, ht hx.2 hy.2 hxy ha hb hab⟩
-/
protected theorem StrictConvex.inter {t : Set E} (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) :
    StrictConvex 𝕜 (s inter t) := by
  intro x hx y hy hxy a b ha hb hab
  rw [interior_inter]
  exact ⟨hs hx.1 hy.1 hxy ha hb hab, ht hx.2 hy.2 hxy ha hb hab⟩

/--
theorem `Directed.strictConvex_iUnion` / 定理 `Directed.strictConvex_iUnion`

English:
theorem Directed.strictConvex_iUnion
  statement: {ι : Sort*} {s : ι -> Set E} (hdir : Directed (· subseteq ·) s)
  proof: by
  rintro x hx y hy hxy a b ha hb hab
  rw [mem_iUnion] at hx hy
  obtain ⟨i, hx⟩ := hx
  obtain ⟨j, hy⟩ := hy
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact interior_mono (subset_iUnion s k) (hs (hik hx) (hjk hy) hxy ha hb hab)

中文:
定理 Directed.strictConvex_iUnion
  结论: {ι : Sort*} {s : ι -> Set E} (hdir : Directed (· subseteq ·) s)
  证明: by
  rintro x hx y hy hxy a b ha hb hab
  rw [mem_iUnion] at hx hy
  obtain ⟨i, hx⟩ := hx
  obtain ⟨j, hy⟩ := hy
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact interior_mono (subset_iUnion s k) (hs (hik hx) (hjk hy) hxy ha hb hab)

Depends on / 依赖: interior_mono, mem_iUnion, subset_iUnion
-/
theorem Directed.strictConvex_iUnion {ι : Sort*} {s : ι -> Set E} (hdir : Directed (· subseteq ·) s)
    (hs : forall ⦃i : ι⦄, StrictConvex 𝕜 (s i)) : StrictConvex 𝕜 (⋃ i, s i) := by
  rintro x hx y hy hxy a b ha hb hab
  rw [mem_iUnion] at hx hy
  obtain ⟨i, hx⟩ := hx
  obtain ⟨j, hy⟩ := hy
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact interior_mono (subset_iUnion s k) (hs (hik hx) (hjk hy) hxy ha hb hab)

/--
theorem `DirectedOn.strictConvex_sUnion` / 定理 `DirectedOn.strictConvex_sUnion`

English:
theorem DirectedOn.strictConvex_sUnion
  statement: {S : Set (Set E)} (hdir : DirectedOn (· subseteq ·) S)
  proof: by
  rw [sUnion_eq_iUnion]
  exact (directedOn_iff_directed.1 hdir).strictConvex_iUnion fun s => hS _ s.2

中文:
定理 DirectedOn.strictConvex_sUnion
  结论: {S : Set (Set E)} (hdir : DirectedOn (· subseteq ·) S)
  证明: by
  rw [sUnion_eq_iUnion]
  exact (directedOn_iff_directed.1 hdir).strictConvex_iUnion fun s => hS _ s.2

Depends on / 依赖: directedOn_iff_directed, sUnion_eq_iUnion, strictConvex_iUnion
-/
theorem DirectedOn.strictConvex_sUnion {S : Set (Set E)} (hdir : DirectedOn (· subseteq ·) S)
    (hS : forall s in S, StrictConvex 𝕜 s) : StrictConvex 𝕜 (⋃₀ S) := by
  rw [sUnion_eq_iUnion]
  exact (directedOn_iff_directed.1 hdir).strictConvex_iUnion fun s => hS _ s.2

end SMul

section Module

variable [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

/--
theorem `StrictConvex.convex` / 定理 `StrictConvex.convex`

English:
theorem StrictConvex.convex
  given: (hs : StrictConvex 𝕜 s)
  statement: Convex 𝕜 s
  proof: convex_iff_pairwise_pos.2 fun _ hx _ hy hxy _ _ ha hb hab =>
interior_subset hs hx hy hxy ha hb hab

中文:
定理 StrictConvex.convex
  条件: (hs : StrictConvex 𝕜 s)
  结论: Convex 𝕜 s
  证明: convex_iff_pairwise_pos.2 fun _ hx _ hy hxy _ _ ha hb hab =>
interior_subset hs hx hy hxy ha hb hab
-/
protected theorem StrictConvex.convex (hs : StrictConvex 𝕜 s) : Convex 𝕜 s :=
  convex_iff_pairwise_pos.2 fun _ hx _ hy hxy _ _ ha hb hab =>
interior_subset hs hx hy hxy ha hb hab

/--
theorem `Convex.strictConvex_of_isOpen` / 定理 `Convex.strictConvex_of_isOpen`

English:
theorem Convex.strictConvex_of_isOpen
  given: (h : IsOpen s) (hs : Convex 𝕜 s)
  proof: fun _ hx _ hy _ _ _ ha hb hab => h.interior_eq.symm ▸ hs hx hy ha.le hb.le hab

中文:
定理 Convex.strictConvex_of_isOpen
  条件: (h : IsOpen s) (hs : Convex 𝕜 s)
  证明: fun _ hx _ hy _ _ _ ha hb hab => h.interior_eq.symm ▸ hs hx hy ha.le hb.le hab
-/
protected theorem Convex.strictConvex_of_isOpen (h : IsOpen s) (hs : Convex 𝕜 s) :
    StrictConvex 𝕜 s :=
  fun _ hx _ hy _ _ _ ha hb hab => h.interior_eq.symm ▸ hs hx hy ha.le hb.le hab

/--
theorem `IsOpen.strictConvex_iff` / 定理 `IsOpen.strictConvex_iff`

English:
theorem IsOpen.strictConvex_iff
  given: (h : IsOpen s)
  statement: StrictConvex 𝕜 s ↔ Convex 𝕜 s
  proof: ⟨StrictConvex.convex, Convex.strictConvex_of_isOpen h⟩

中文:
定理 IsOpen.strictConvex_iff
  条件: (h : IsOpen s)
  结论: StrictConvex 𝕜 s ↔ Convex 𝕜 s
  证明: ⟨StrictConvex.convex, Convex.strictConvex_of_isOpen h⟩

Depends on / 依赖: Convex, Convex.strictConvex_of_isOpen, StrictConvex, StrictConvex.convex, convex, strictConvex_of_isOpen
-/
theorem IsOpen.strictConvex_iff (h : IsOpen s) : StrictConvex 𝕜 s ↔ Convex 𝕜 s :=
  ⟨StrictConvex.convex, Convex.strictConvex_of_isOpen h⟩

/--
theorem `strictConvex_singleton` / 定理 `strictConvex_singleton`

English:
theorem strictConvex_singleton
  given: (c : E)
  statement: StrictConvex 𝕜 ({c} : Set E)
  proof: pairwise_singleton _ _

中文:
定理 strictConvex_singleton
  条件: (c : E)
  结论: StrictConvex 𝕜 ({c} : Set E)
  证明: pairwise_singleton _ _

Depends on / 依赖: pairwise_singleton
-/
theorem strictConvex_singleton (c : E) : StrictConvex 𝕜 ({c} : Set E) :=
  pairwise_singleton _ _

/--
theorem `Set.Subsingleton.strictConvex` / 定理 `Set.Subsingleton.strictConvex`

English:
theorem Set.Subsingleton.strictConvex
  given: (hs : s.Subsingleton)
  statement: StrictConvex 𝕜 s
  proof: hs.pairwise _

中文:
定理 Set.Subsingleton.strictConvex
  条件: (hs : s.Subsingleton)
  结论: StrictConvex 𝕜 s
  证明: hs.pairwise _

Depends on / 依赖: hs.pairwise, pairwise
-/
theorem Set.Subsingleton.strictConvex (hs : s.Subsingleton) : StrictConvex 𝕜 s :=
  hs.pairwise _

/--
theorem `StrictConvex.linear_image` / 定理 `StrictConvex.linear_image`

English:
theorem StrictConvex.linear_image
  statement: [Semiring 𝕝] [Module 𝕝 E] [Module 𝕝 F]
  proof: by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab
  refine hf.image_interior_subset _ ⟨a • x + b • y, hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, ?_⟩
  rw [map_add]; rw [f.map_smul_of_tower a]; rw [f.map_smul_of_tower b]

中文:
定理 StrictConvex.linear_image
  结论: [Semiring 𝕝] [Module 𝕝 E] [Module 𝕝 F]
  证明: by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab
  refine hf.image_interior_subset _ ⟨a • x + b • y, hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, ?_⟩
  rw [map_add]; rw [f.map_smul_of_tower a]; rw [f.map_smul_of_tower b]

Depends on / 依赖: f.map_smul_of_tower, hf.image_interior_subset, image_interior_subset, map_add, map_smul_of_tower, ne_of_apply_ne
-/
theorem StrictConvex.linear_image [Semiring 𝕝] [Module 𝕝 E] [Module 𝕝 F]
    [LinearMap.CompatibleSMul E F 𝕜 𝕝] (hs : StrictConvex 𝕜 s) (f : E ->ₗ[𝕝] F) (hf : IsOpenMap f) :
    StrictConvex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab
  refine hf.image_interior_subset _ ⟨a • x + b • y, hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, ?_⟩
  rw [map_add]; rw [f.map_smul_of_tower a]; rw [f.map_smul_of_tower b]

/--
theorem `StrictConvex.is_linear_image` / 定理 `StrictConvex.is_linear_image`

English:
theorem StrictConvex.is_linear_image
  statement: (hs : StrictConvex 𝕜 s) {f : E -> F} (h : IsLinearMap 𝕜 f)
  proof: hs.linear_image (h.mk' f) hf

中文:
定理 StrictConvex.is_linear_image
  结论: (hs : StrictConvex 𝕜 s) {f : E -> F} (h : IsLinearMap 𝕜 f)
  证明: hs.linear_image (h.mk' f) hf

Depends on / 依赖: h.mk, hs.linear_image, linear_image
-/
theorem StrictConvex.is_linear_image (hs : StrictConvex 𝕜 s) {f : E -> F} (h : IsLinearMap 𝕜 f)
    (hf : IsOpenMap f) : StrictConvex 𝕜 (f '' s) :=
  hs.linear_image (h.mk' f) hf

/--
theorem `StrictConvex.linear_preimage` / 定理 `StrictConvex.linear_preimage`

English:
theorem StrictConvex.linear_preimage
  statement: {s : Set F} (hs : StrictConvex 𝕜 s) (f : E ->ₗ[𝕜] F)
  proof: by
  intro x hx y hy hxy a b ha hb hab
  refine preimage_interior_subset_interior_preimage hf ?_
  rw [mem_preimage]; rw [f.map_add]; rw [f.map_smul]; rw [f.map_smul]
  exact hs hx hy (hfinj.ne hxy) ha hb hab

中文:
定理 StrictConvex.linear_preimage
  结论: {s : Set F} (hs : StrictConvex 𝕜 s) (f : E ->ₗ[𝕜] F)
  证明: by
  intro x hx y hy hxy a b ha hb hab
  refine preimage_interior_subset_interior_preimage hf ?_
  rw [mem_preimage]; rw [f.map_add]; rw [f.map_smul]; rw [f.map_smul]
  exact hs hx hy (hfinj.ne hxy) ha hb hab

Depends on / 依赖: f.map_add, f.map_smul, hfinj.ne, map_add, map_smul, mem_preimage, preimage_interior_subset_interior_preimage
-/
theorem StrictConvex.linear_preimage {s : Set F} (hs : StrictConvex 𝕜 s) (f : E ->ₗ[𝕜] F)
    (hf : Continuous f) (hfinj : Injective f) : StrictConvex 𝕜 (s.preimage f) := by
  intro x hx y hy hxy a b ha hb hab
  refine preimage_interior_subset_interior_preimage hf ?_
  rw [mem_preimage]; rw [f.map_add]; rw [f.map_smul]; rw [f.map_smul]
  exact hs hx hy (hfinj.ne hxy) ha hb hab

/--
theorem `StrictConvex.is_linear_preimage` / 定理 `StrictConvex.is_linear_preimage`

English:
theorem StrictConvex.is_linear_preimage
  statement: {s : Set F} (hs : StrictConvex 𝕜 s) {f : E -> F}
  proof: hs.linear_preimage (h.mk' f) hf hfinj

中文:
定理 StrictConvex.is_linear_preimage
  结论: {s : Set F} (hs : StrictConvex 𝕜 s) {f : E -> F}
  证明: hs.linear_preimage (h.mk' f) hf hfinj

Depends on / 依赖: h.mk, hs.linear_preimage, linear_preimage
-/
theorem StrictConvex.is_linear_preimage {s : Set F} (hs : StrictConvex 𝕜 s) {f : E -> F}
    (h : IsLinearMap 𝕜 f) (hf : Continuous f) (hfinj : Injective f) :
    StrictConvex 𝕜 (s.preimage f) :=
  hs.linear_preimage (h.mk' f) hf hfinj

section LinearOrderedCancelAddCommMonoid

variable [TopologicalSpace β] [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]
  [OrderTopology β] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β]

/--
theorem `Set.OrdConnected.strictConvex` / 定理 `Set.OrdConnected.strictConvex`

English:
theorem Set.OrdConnected.strictConvex
  given: {s : Set β} (hs : OrdConnected s)
  proof: by
  refine strictConvex_iff_openSegment_subset.2 fun x hx y hy hxy => ?_
  rcases hxy.lt_or_gt with hlt | hlt <;> [skip; rw [openSegment_symm]] <;>
    exact
      (openSegment_subset_Ioo hlt).trans
        (isOpen_Ioo.subset_interior_iff.2 <| Ioo_subset_Icc_self.trans <| hs.out ‹_› ‹_›)

中文:
定理 Set.OrdConnected.strictConvex
  条件: {s : Set β} (hs : OrdConnected s)
  证明: by
  refine strictConvex_iff_openSegment_subset.2 fun x hx y hy hxy => ?_
  rcases hxy.lt_or_gt with hlt | hlt <;> [skip; rw [openSegment_symm]] <;>
    exact
      (openSegment_subset_Ioo hlt).trans
        (isOpen_Ioo.subset_interior_iff.2 <| Ioo_subset_Icc_self.trans <| hs.out ‹_› ‹_›)
-/
protected theorem Set.OrdConnected.strictConvex {s : Set β} (hs : OrdConnected s) :
    StrictConvex 𝕜 s := by
  refine strictConvex_iff_openSegment_subset.2 fun x hx y hy hxy => ?_
  rcases hxy.lt_or_gt with hlt | hlt <;> [skip; rw [openSegment_symm]] <;>
    exact
      (openSegment_subset_Ioo hlt).trans
        (isOpen_Ioo.subset_interior_iff.2 <| Ioo_subset_Icc_self.trans <| hs.out ‹_› ‹_›)

/--
theorem `strictConvex_Iic` / 定理 `strictConvex_Iic`

English:
theorem strictConvex_Iic
  given: (r : β)
  statement: StrictConvex 𝕜 (Iic r)
  proof: ordConnected_Iic.strictConvex

中文:
定理 strictConvex_Iic
  条件: (r : β)
  结论: StrictConvex 𝕜 (Iic r)
  证明: ordConnected_Iic.strictConvex

Depends on / 依赖: ordConnected_Iic, ordConnected_Iic.strictConvex, strictConvex
-/
theorem strictConvex_Iic (r : β) : StrictConvex 𝕜 (Iic r) :=
  ordConnected_Iic.strictConvex

/--
theorem `strictConvex_Ici` / 定理 `strictConvex_Ici`

English:
theorem strictConvex_Ici
  given: (r : β)
  statement: StrictConvex 𝕜 (Ici r)
  proof: ordConnected_Ici.strictConvex

中文:
定理 strictConvex_Ici
  条件: (r : β)
  结论: StrictConvex 𝕜 (Ici r)
  证明: ordConnected_Ici.strictConvex

Depends on / 依赖: ordConnected_Ici, ordConnected_Ici.strictConvex, strictConvex
-/
theorem strictConvex_Ici (r : β) : StrictConvex 𝕜 (Ici r) :=
  ordConnected_Ici.strictConvex

/--
theorem `strictConvex_Iio` / 定理 `strictConvex_Iio`

English:
theorem strictConvex_Iio
  given: (r : β)
  statement: StrictConvex 𝕜 (Iio r)
  proof: ordConnected_Iio.strictConvex

中文:
定理 strictConvex_Iio
  条件: (r : β)
  结论: StrictConvex 𝕜 (Iio r)
  证明: ordConnected_Iio.strictConvex

Depends on / 依赖: ordConnected_Iio, ordConnected_Iio.strictConvex, strictConvex
-/
theorem strictConvex_Iio (r : β) : StrictConvex 𝕜 (Iio r) :=
  ordConnected_Iio.strictConvex

/--
theorem `strictConvex_Ioi` / 定理 `strictConvex_Ioi`

English:
theorem strictConvex_Ioi
  given: (r : β)
  statement: StrictConvex 𝕜 (Ioi r)
  proof: ordConnected_Ioi.strictConvex

中文:
定理 strictConvex_Ioi
  条件: (r : β)
  结论: StrictConvex 𝕜 (Ioi r)
  证明: ordConnected_Ioi.strictConvex

Depends on / 依赖: ordConnected_Ioi, ordConnected_Ioi.strictConvex, strictConvex
-/
theorem strictConvex_Ioi (r : β) : StrictConvex 𝕜 (Ioi r) :=
  ordConnected_Ioi.strictConvex

/--
theorem `strictConvex_Icc` / 定理 `strictConvex_Icc`

English:
theorem strictConvex_Icc
  given: (r s : β)
  statement: StrictConvex 𝕜 (Icc r s)
  proof: ordConnected_Icc.strictConvex

中文:
定理 strictConvex_Icc
  条件: (r s : β)
  结论: StrictConvex 𝕜 (Icc r s)
  证明: ordConnected_Icc.strictConvex

Depends on / 依赖: ordConnected_Icc, ordConnected_Icc.strictConvex, strictConvex
-/
theorem strictConvex_Icc (r s : β) : StrictConvex 𝕜 (Icc r s) :=
  ordConnected_Icc.strictConvex

/--
theorem `strictConvex_Ioo` / 定理 `strictConvex_Ioo`

English:
theorem strictConvex_Ioo
  given: (r s : β)
  statement: StrictConvex 𝕜 (Ioo r s)
  proof: ordConnected_Ioo.strictConvex

中文:
定理 strictConvex_Ioo
  条件: (r s : β)
  结论: StrictConvex 𝕜 (Ioo r s)
  证明: ordConnected_Ioo.strictConvex

Depends on / 依赖: ordConnected_Ioo, ordConnected_Ioo.strictConvex, strictConvex
-/
theorem strictConvex_Ioo (r s : β) : StrictConvex 𝕜 (Ioo r s) :=
  ordConnected_Ioo.strictConvex

/--
theorem `strictConvex_Ico` / 定理 `strictConvex_Ico`

English:
theorem strictConvex_Ico
  given: (r s : β)
  statement: StrictConvex 𝕜 (Ico r s)
  proof: ordConnected_Ico.strictConvex

中文:
定理 strictConvex_Ico
  条件: (r s : β)
  结论: StrictConvex 𝕜 (Ico r s)
  证明: ordConnected_Ico.strictConvex

Depends on / 依赖: ordConnected_Ico, ordConnected_Ico.strictConvex, strictConvex
-/
theorem strictConvex_Ico (r s : β) : StrictConvex 𝕜 (Ico r s) :=
  ordConnected_Ico.strictConvex

/--
theorem `strictConvex_Ioc` / 定理 `strictConvex_Ioc`

English:
theorem strictConvex_Ioc
  given: (r s : β)
  statement: StrictConvex 𝕜 (Ioc r s)
  proof: ordConnected_Ioc.strictConvex

中文:
定理 strictConvex_Ioc
  条件: (r s : β)
  结论: StrictConvex 𝕜 (Ioc r s)
  证明: ordConnected_Ioc.strictConvex

Depends on / 依赖: ordConnected_Ioc, ordConnected_Ioc.strictConvex, strictConvex
-/
theorem strictConvex_Ioc (r s : β) : StrictConvex 𝕜 (Ioc r s) :=
  ordConnected_Ioc.strictConvex

/--
theorem `strictConvex_uIcc` / 定理 `strictConvex_uIcc`

English:
theorem strictConvex_uIcc
  given: (r s : β)
  statement: StrictConvex 𝕜 (uIcc r s)
  proof: strictConvex_Icc _ _

中文:
定理 strictConvex_uIcc
  条件: (r s : β)
  结论: StrictConvex 𝕜 (uIcc r s)
  证明: strictConvex_Icc _ _

Depends on / 依赖: strictConvex_Icc
-/
theorem strictConvex_uIcc (r s : β) : StrictConvex 𝕜 (uIcc r s) :=
  strictConvex_Icc _ _

/--
theorem `strictConvex_uIoc` / 定理 `strictConvex_uIoc`

English:
theorem strictConvex_uIoc
  given: (r s : β)
  statement: StrictConvex 𝕜 (uIoc r s)
  proof: strictConvex_Ioc _ _

中文:
定理 strictConvex_uIoc
  条件: (r s : β)
  结论: StrictConvex 𝕜 (uIoc r s)
  证明: strictConvex_Ioc _ _

Depends on / 依赖: strictConvex_Ioc
-/
theorem strictConvex_uIoc (r s : β) : StrictConvex 𝕜 (uIoc r s) :=
  strictConvex_Ioc _ _

end LinearOrderedCancelAddCommMonoid

end Module

end AddCommMonoid

section AddCancelCommMonoid

variable [AddCancelCommMonoid E] [ContinuousAdd E] [Module 𝕜 E] {s : Set E}

/--
theorem `StrictConvex.preimage_add_right` / 定理 `StrictConvex.preimage_add_right`

English:
theorem StrictConvex.preimage_add_right
  given: (hs : StrictConvex 𝕜 s) (z : E)
  proof: by
  intro x hx y hy hxy a b ha hb hab
  refine preimage_interior_subset_interior_preimage (continuous_const_add _) ?_
  have h := hs hx hy ((add_right_injective _).ne hxy) ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← _root_.add_smul, hab, one_smul] at h

中文:
定理 StrictConvex.preimage_add_right
  条件: (hs : StrictConvex 𝕜 s) (z : E)
  证明: by
  intro x hx y hy hxy a b ha hb hab
  refine preimage_interior_subset_interior_preimage (continuous_const_add _) ?_
  have h := hs hx hy ((add_right_injective _).ne hxy) ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← _root_.add_smul, hab, one_smul] at h

Depends on / 依赖: _root_, _root_.add_smul, add_add_add_comm, add_right_injective, add_smul, continuous_const_add, one_smul, preimage_interior_subset_interior_preimage, smul_add
-/
theorem StrictConvex.preimage_add_right (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => z + x) ⁻¹' s) := by
  intro x hx y hy hxy a b ha hb hab
  refine preimage_interior_subset_interior_preimage (continuous_const_add _) ?_
  have h := hs hx hy ((add_right_injective _).ne hxy) ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← _root_.add_smul, hab, one_smul] at h

/--
theorem `StrictConvex.preimage_add_left` / 定理 `StrictConvex.preimage_add_left`

English:
theorem StrictConvex.preimage_add_left
  given: (hs : StrictConvex 𝕜 s) (z : E)
  proof: by
  simpa only [add_comm] using hs.preimage_add_right z

中文:
定理 StrictConvex.preimage_add_left
  条件: (hs : StrictConvex 𝕜 s) (z : E)
  证明: by
  simpa only [add_comm] using hs.preimage_add_right z

Depends on / 依赖: add_comm, hs.preimage_add_right, preimage_add_right
-/
theorem StrictConvex.preimage_add_left (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => x + z) ⁻¹' s) := by
  simpa only [add_comm] using hs.preimage_add_right z

end AddCancelCommMonoid

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]

section continuous_add

variable [ContinuousAdd E] {s t : Set E}

/--
theorem `StrictConvex.add` / 定理 `StrictConvex.add`

English:
theorem StrictConvex.add
  given: (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t)
  proof: by
  rintro _ ⟨v, hv, w, hw, rfl⟩ _ ⟨x, hx, y, hy, rfl⟩ h a b ha hb hab
  rw [smul_add]; rw [smul_add]; rw [add_add_add_comm]
  obtain rfl | hvx := eq_or_ne v x
  · refine interior_mono (add_subset_add (singleton_subset_iff.2 hv) Subset.rfl) ?_
    rw [Convex.combo_self hab]; rw [singleton_add]
    

中文:
定理 StrictConvex.add
  条件: (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t)
  证明: by
  rintro _ ⟨v, hv, w, hw, rfl⟩ _ ⟨x, hx, y, hy, rfl⟩ h a b ha hb hab
  rw [smul_add]; rw [smul_add]; rw [add_add_add_comm]
  obtain rfl | hvx := eq_or_ne v x
  · refine interior_mono (add_subset_add (singleton_subset_iff.2 hv) Subset.rfl) ?_
    rw [Convex.combo_self hab]; rw [singleton_add]
    

Depends on / 依赖: Convex, Convex.combo_self, Subset, Subset.rfl, add_add_add_comm, add_mem_add, add_subset_add, combo_self, convex, eq_or_ne, ha.le, hb.le, ht.convex, image_interior_subset, interior_mono, isOpenMap_add_left, mem_image_of_mem, ne_of_apply_ne, singleton_add, singleton_subset_iff
-/
theorem StrictConvex.add (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) :
    StrictConvex 𝕜 (s + t) := by
  rintro _ ⟨v, hv, w, hw, rfl⟩ _ ⟨x, hx, y, hy, rfl⟩ h a b ha hb hab
  rw [smul_add]; rw [smul_add]; rw [add_add_add_comm]
  obtain rfl | hvx := eq_or_ne v x
  · refine interior_mono (add_subset_add (singleton_subset_iff.2 hv) Subset.rfl) ?_
    rw [Convex.combo_self hab]; rw [singleton_add]
    exact
      (isOpenMap_add_left _).image_interior_subset _
        (mem_image_of_mem _ <| ht hw hy (ne_of_apply_ne _ h) ha hb hab)
  exact
    subset_interior_add_left
      (add_mem_add (hs hv hx hvx ha hb hab) <| ht.convex hw hy ha.le hb.le hab)

/--
theorem `StrictConvex.add_left` / 定理 `StrictConvex.add_left`

English:
theorem StrictConvex.add_left
  given: (hs : StrictConvex 𝕜 s) (z : E)
  proof: by
  simpa only [singleton_add] using (strictConvex_singleton z).add hs

中文:
定理 StrictConvex.add_left
  条件: (hs : StrictConvex 𝕜 s) (z : E)
  证明: by
  simpa only [singleton_add] using (strictConvex_singleton z).add hs

Depends on / 依赖: singleton_add, strictConvex_singleton
-/
theorem StrictConvex.add_left (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => z + x) '' s) := by
  simpa only [singleton_add] using (strictConvex_singleton z).add hs

/--
theorem `StrictConvex.add_right` / 定理 `StrictConvex.add_right`

English:
theorem StrictConvex.add_right
  given: (hs : StrictConvex 𝕜 s) (z : E)
  proof: by simpa only [add_comm] using hs.add_left z

中文:
定理 StrictConvex.add_right
  条件: (hs : StrictConvex 𝕜 s) (z : E)
  证明: by simpa only [add_comm] using hs.add_left z

Depends on / 依赖: add_comm, add_left, hs.add_left
-/
theorem StrictConvex.add_right (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => x + z) '' s) := by simpa only [add_comm] using hs.add_left z

/--
theorem `StrictConvex.vadd` / 定理 `StrictConvex.vadd`

English:
theorem StrictConvex.vadd
  given: (hs : StrictConvex 𝕜 s) (x : E)
  statement: StrictConvex 𝕜 (x +ᵥ s)
  proof: hs.add_left x

中文:
定理 StrictConvex.vadd
  条件: (hs : StrictConvex 𝕜 s) (x : E)
  结论: StrictConvex 𝕜 (x +ᵥ s)
  证明: hs.add_left x

Depends on / 依赖: add_left, hs.add_left
-/
theorem StrictConvex.vadd (hs : StrictConvex 𝕜 s) (x : E) : StrictConvex 𝕜 (x +ᵥ s) :=
  hs.add_left x

end continuous_add

section ContinuousSMul

variable [Field 𝕝] [Module 𝕝 E] [ContinuousConstSMul 𝕝 E]
  [LinearMap.CompatibleSMul E E 𝕜 𝕝] {s : Set E} {x : E}

/--
theorem `StrictConvex.smul` / 定理 `StrictConvex.smul`

English:
theorem StrictConvex.smul
  given: (hs : StrictConvex 𝕜 s) (c : 𝕝)
  statement: StrictConvex 𝕜 (c • s)
  proof: by
  obtain rfl | hc := eq_or_ne c 0
  · exact (subsingleton_zero_smul_set _).strictConvex
  · exact hs.linear_image (LinearMap.lsmul _ _ c) (isOpenMap_smul₀ hc)

中文:
定理 StrictConvex.smul
  条件: (hs : StrictConvex 𝕜 s) (c : 𝕝)
  结论: StrictConvex 𝕜 (c • s)
  证明: by
  obtain rfl | hc := eq_or_ne c 0
  · exact (subsingleton_zero_smul_set _).strictConvex
  · exact hs.linear_image (LinearMap.lsmul _ _ c) (isOpenMap_smul₀ hc)

Depends on / 依赖: LinearMap, LinearMap.lsmul, eq_or_ne, hs.linear_image, linear_image, strictConvex, subsingleton_zero_smul_set
-/
theorem StrictConvex.smul (hs : StrictConvex 𝕜 s) (c : 𝕝) : StrictConvex 𝕜 (c • s) := by
  obtain rfl | hc := eq_or_ne c 0
  · exact (subsingleton_zero_smul_set _).strictConvex
  · exact hs.linear_image (LinearMap.lsmul _ _ c) (isOpenMap_smul₀ hc)

/--
theorem `StrictConvex.affinity` / 定理 `StrictConvex.affinity`

English:
theorem StrictConvex.affinity
  given: [ContinuousAdd E] (hs : StrictConvex 𝕜 s) (z : E) (c : 𝕝)
  proof: (hs.smul c).vadd z

中文:
定理 StrictConvex.affinity
  条件: [ContinuousAdd E] (hs : StrictConvex 𝕜 s) (z : E) (c : 𝕝)
  证明: (hs.smul c).vadd z

Depends on / 依赖: hs.smul
-/
theorem StrictConvex.affinity [ContinuousAdd E] (hs : StrictConvex 𝕜 s) (z : E) (c : 𝕝) :
    StrictConvex 𝕜 (z +ᵥ c • s) :=
  (hs.smul c).vadd z

end ContinuousSMul

end AddCommGroup

end OrderedSemiring

section CommSemiring
variable [CommSemiring 𝕜] [IsDomain 𝕜] [PartialOrder 𝕜] [TopologicalSpace E] [AddCommGroup E]
  [Module 𝕜 E] [Module.IsTorsionFree 𝕜 E] [ContinuousConstSMul 𝕜 E] {s : Set E}

/--
theorem `StrictConvex.preimage_smul` / 定理 `StrictConvex.preimage_smul`

English:
theorem StrictConvex.preimage_smul
  given: (hs : StrictConvex 𝕜 s) (c : 𝕜)
  proof: by
  classical
    obtain rfl | hc := eq_or_ne c 0
    · simp_rw [zero_smul, preimage_const]
      split_ifs
      · exact strictConvex_univ
      · exact strictConvex_empty
    refine hs.linear_preimage (LinearMap.lsmul _ _ c) ?_ (smul_right_injective E hc)
    unfold LinearMap.lsmul LinearMap.mk₂ 

中文:
定理 StrictConvex.preimage_smul
  条件: (hs : StrictConvex 𝕜 s) (c : 𝕜)
  证明: by
  classical
    obtain rfl | hc := eq_or_ne c 0
    · simp_rw [zero_smul, preimage_const]
      split_ifs
      · exact strictConvex_univ
      · exact strictConvex_empty
    refine hs.linear_preimage (LinearMap.lsmul _ _ c) ?_ (smul_right_injective E hc)
    unfold LinearMap.lsmul LinearMap.mk₂ 

Depends on / 依赖: LinearMap, LinearMap.lsmul, LinearMap.mk, classical, continuous_const_smul, eq_or_ne, hs.linear_preimage, linear_preimage, preimage_const, simp_rw, smul_right_injective, split_ifs, strictConvex_empty, strictConvex_univ, zero_smul
-/
theorem StrictConvex.preimage_smul (hs : StrictConvex 𝕜 s) (c : 𝕜) :
    StrictConvex 𝕜 ((fun z => c • z) ⁻¹' s) := by
  classical
    obtain rfl | hc := eq_or_ne c 0
    · simp_rw [zero_smul, preimage_const]
      split_ifs
      · exact strictConvex_univ
      · exact strictConvex_empty
    refine hs.linear_preimage (LinearMap.lsmul _ _ c) ?_ (smul_right_injective E hc)
    unfold LinearMap.lsmul LinearMap.mk₂ LinearMap.mk₂' LinearMap.mk₂'ₛₗ
    exact continuous_const_smul _

end CommSemiring

section OrderedRing

variable [Ring 𝕜] [PartialOrder 𝕜] [TopologicalSpace E] [TopologicalSpace F]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s t : Set E} {x y : E}

/--
theorem `StrictConvex.eq_of_openSegment_subset_frontier` / 定理 `StrictConvex.eq_of_openSegment_subset_frontier`

English:
theorem StrictConvex.eq_of_openSegment_subset_frontier
  proof: by
  obtain ⟨a, ha₀, ha₁⟩ := DenselyOrdered.dense (0 : 𝕜) 1 zero_lt_one
  classical
    by_contra hxy
    exact
      (h ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel _ _, rfl⟩).2
        (hs hx hy hxy ha₀ (sub_pos_of_lt ha₁) <| add_sub_cancel _ _)

中文:
定理 StrictConvex.eq_of_openSegment_subset_frontier
  证明: by
  obtain ⟨a, ha₀, ha₁⟩ := DenselyOrdered.dense (0 : 𝕜) 1 zero_lt_one
  classical
    by_contra hxy
    exact
      (h ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel _ _, rfl⟩).2
        (hs hx hy hxy ha₀ (sub_pos_of_lt ha₁) <| add_sub_cancel _ _)

Depends on / 依赖: DenselyOrdered, DenselyOrdered.dense, add_sub_cancel, classical, sub_pos_of_lt, zero_lt_one
-/
theorem StrictConvex.eq_of_openSegment_subset_frontier
    [IsOrderedRing 𝕜] [Nontrivial 𝕜] [DenselyOrdered 𝕜]
    (hs : StrictConvex 𝕜 s) (hx : x in s) (hy : y in s) (h : openSegment 𝕜 x y subseteq frontier s) :
    x = y := by
  obtain ⟨a, ha₀, ha₁⟩ := DenselyOrdered.dense (0 : 𝕜) 1 zero_lt_one
  classical
    by_contra hxy
    exact
      (h ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel _ _, rfl⟩).2
        (hs hx hy hxy ha₀ (sub_pos_of_lt ha₁) <| add_sub_cancel _ _)

/--
theorem `StrictConvex.add_smul_mem` / 定理 `StrictConvex.add_smul_mem`

English:
theorem StrictConvex.add_smul_mem
  statement: [AddRightStrictMono 𝕜]
  proof: by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by match_scalars <;> simp
  rw [h]
  exact hs hx hxy (fun h => hy <| add_left_cancel (a := x) (by rw [← h, add_zero]))
    (sub_pos_of_lt ht₁) ht₀ (sub_add_cancel 1 t)

中文:
定理 StrictConvex.add_smul_mem
  结论: [AddRightStrictMono 𝕜]
  证明: by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by match_scalars <;> simp
  rw [h]
  exact hs hx hxy (fun h => hy <| add_left_cancel (a := x) (by rw [← h, add_zero]))
    (sub_pos_of_lt ht₁) ht₀ (sub_add_cancel 1 t)

Depends on / 依赖: add_left_cancel, add_zero, match_scalars, sub_add_cancel, sub_pos_of_lt
-/
theorem StrictConvex.add_smul_mem [AddRightStrictMono 𝕜]
    (hs : StrictConvex 𝕜 s) (hx : x in s) (hxy : x + y in s)
    (hy : y != 0) {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) : x + t • y in interior s := by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by match_scalars <;> simp
  rw [h]
  exact hs hx hxy (fun h => hy <| add_left_cancel (a := x) (by rw [← h, add_zero]))
    (sub_pos_of_lt ht₁) ht₀ (sub_add_cancel 1 t)

/--
theorem `StrictConvex.smul_mem_of_zero_mem` / 定理 `StrictConvex.smul_mem_of_zero_mem`

English:
theorem StrictConvex.smul_mem_of_zero_mem
  statement: [AddRightStrictMono 𝕜]
  proof: by
  simpa using hs.add_smul_mem zero_mem (by simpa using hx) hx₀ ht₀ ht₁

中文:
定理 StrictConvex.smul_mem_of_zero_mem
  结论: [AddRightStrictMono 𝕜]
  证明: by
  simpa using hs.add_smul_mem zero_mem (by simpa using hx) hx₀ ht₀ ht₁

Depends on / 依赖: add_smul_mem, hs.add_smul_mem, zero_mem
-/
theorem StrictConvex.smul_mem_of_zero_mem [AddRightStrictMono 𝕜]
    (hs : StrictConvex 𝕜 s) (zero_mem : (0 : E) in s)
    (hx : x in s) (hx₀ : x != 0) {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) : t • x in interior s := by
  simpa using hs.add_smul_mem zero_mem (by simpa using hx) hx₀ ht₀ ht₁

/--
theorem `StrictConvex.add_smul_sub_mem` / 定理 `StrictConvex.add_smul_sub_mem`

English:
theorem StrictConvex.add_smul_sub_mem
  statement: [AddRightMono 𝕜]
  proof: by
  apply h.openSegment_subset hx hy hxy
  rw [openSegment_eq_image']
  exact mem_image_of_mem _ ⟨ht₀, ht₁⟩

中文:
定理 StrictConvex.add_smul_sub_mem
  结论: [AddRightMono 𝕜]
  证明: by
  apply h.openSegment_subset hx hy hxy
  rw [openSegment_eq_image']
  exact mem_image_of_mem _ ⟨ht₀, ht₁⟩

Depends on / 依赖: h.openSegment_subset, mem_image_of_mem, openSegment_eq_image, openSegment_subset
-/
theorem StrictConvex.add_smul_sub_mem [AddRightMono 𝕜]
    (h : StrictConvex 𝕜 s) (hx : x in s) (hy : y in s) (hxy : x != y)
    {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) : x + t • (y - x) in interior s := by
  apply h.openSegment_subset hx hy hxy
  rw [openSegment_eq_image']
  exact mem_image_of_mem _ ⟨ht₀, ht₁⟩

/--
theorem `StrictConvex.affine_preimage` / 定理 `StrictConvex.affine_preimage`

English:
theorem StrictConvex.affine_preimage
  statement: {s : Set F} (hs : StrictConvex 𝕜 s) {f : E ->ᵃ[𝕜] F}
  proof: by
  intro x hx y hy hxy a b ha hb hab
  refine preimage_interior_subset_interior_preimage hf ?_
  rw [mem_preimage]; rw [Convex.combo_affine_apply hab]
  exact hs hx hy (hfinj.ne hxy) ha hb hab

中文:
定理 StrictConvex.affine_preimage
  结论: {s : Set F} (hs : StrictConvex 𝕜 s) {f : E ->ᵃ[𝕜] F}
  证明: by
  intro x hx y hy hxy a b ha hb hab
  refine preimage_interior_subset_interior_preimage hf ?_
  rw [mem_preimage]; rw [Convex.combo_affine_apply hab]
  exact hs hx hy (hfinj.ne hxy) ha hb hab

Depends on / 依赖: Convex, Convex.combo_affine_apply, combo_affine_apply, hfinj.ne, mem_preimage, preimage_interior_subset_interior_preimage
-/
theorem StrictConvex.affine_preimage {s : Set F} (hs : StrictConvex 𝕜 s) {f : E ->ᵃ[𝕜] F}
    (hf : Continuous f) (hfinj : Injective f) : StrictConvex 𝕜 (f ⁻¹' s) := by
  intro x hx y hy hxy a b ha hb hab
  refine preimage_interior_subset_interior_preimage hf ?_
  rw [mem_preimage]; rw [Convex.combo_affine_apply hab]
  exact hs hx hy (hfinj.ne hxy) ha hb hab

/--
theorem `StrictConvex.affine_image` / 定理 `StrictConvex.affine_image`

English:
theorem StrictConvex.affine_image
  given: (hs : StrictConvex 𝕜 s) {f : E ->ᵃ[𝕜] F} (hf : IsOpenMap f)
  proof: by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab
  exact
    hf.image_interior_subset _
      ⟨a • x + b • y, ⟨hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, Convex.combo_affine_apply hab⟩⟩

中文:
定理 StrictConvex.affine_image
  条件: (hs : StrictConvex 𝕜 s) {f : E ->ᵃ[𝕜] F} (hf : IsOpenMap f)
  证明: by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab
  exact
    hf.image_interior_subset _
      ⟨a • x + b • y, ⟨hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, Convex.combo_affine_apply hab⟩⟩

Depends on / 依赖: Convex, Convex.combo_affine_apply, combo_affine_apply, hf.image_interior_subset, image_interior_subset, ne_of_apply_ne
-/
theorem StrictConvex.affine_image (hs : StrictConvex 𝕜 s) {f : E ->ᵃ[𝕜] F} (hf : IsOpenMap f) :
    StrictConvex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab
  exact
    hf.image_interior_subset _
      ⟨a • x + b • y, ⟨hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, Convex.combo_affine_apply hab⟩⟩

variable [IsTopologicalAddGroup E]

/--
theorem `StrictConvex.neg` / 定理 `StrictConvex.neg`

English:
theorem StrictConvex.neg
  given: (hs : StrictConvex 𝕜 s)
  statement: StrictConvex 𝕜 (-s)
  proof: hs.is_linear_preimage IsLinearMap.isLinearMap_neg continuous_id.neg neg_injective

中文:
定理 StrictConvex.neg
  条件: (hs : StrictConvex 𝕜 s)
  结论: StrictConvex 𝕜 (-s)
  证明: hs.is_linear_preimage IsLinearMap.isLinearMap_neg continuous_id.neg neg_injective

Depends on / 依赖: IsLinearMap, IsLinearMap.isLinearMap_neg, continuous_id, continuous_id.neg, hs.is_linear_preimage, isLinearMap_neg, is_linear_preimage, neg_injective
-/
theorem StrictConvex.neg (hs : StrictConvex 𝕜 s) : StrictConvex 𝕜 (-s) :=
  hs.is_linear_preimage IsLinearMap.isLinearMap_neg continuous_id.neg neg_injective

/--
theorem `StrictConvex.sub` / 定理 `StrictConvex.sub`

English:
theorem StrictConvex.sub
  given: (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t)
  statement: StrictConvex 𝕜 (s - t)
  proof: (sub_eq_add_neg s t).symm ▸ hs.add ht.neg

中文:
定理 StrictConvex.sub
  条件: (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t)
  结论: StrictConvex 𝕜 (s - t)
  证明: (sub_eq_add_neg s t).symm ▸ hs.add ht.neg

Depends on / 依赖: hs.add, ht.neg, sub_eq_add_neg
-/
theorem StrictConvex.sub (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) : StrictConvex 𝕜 (s - t) :=
  (sub_eq_add_neg s t).symm ▸ hs.add ht.neg

end AddCommGroup

end OrderedRing

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace E]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E} {x : E}

/--
theorem `strictConvex_iff_div` / 定理 `strictConvex_iff_div`

English:
theorem strictConvex_iff_div
  proof: ⟨fun h x hx y hy hxy a b ha hb => h hx hy hxy (by positivity) (by positivity) (by field),
    fun h x hx y hy hxy a b ha hb hab => by
    convert! h hx hy hxy ha hb <;> rw [hab, div_one]⟩

中文:
定理 strictConvex_iff_div
  证明: ⟨fun h x hx y hy hxy a b ha hb => h hx hy hxy (by positivity) (by positivity) (by field),
    fun h x hx y hy hxy a b ha hb hab => by
    convert! h hx hy hxy ha hb <;> rw [hab, div_one]⟩

Depends on / 依赖: convert, div_one
-/
theorem strictConvex_iff_div :
    StrictConvex 𝕜 s ↔
      s.Pairwise fun x y =>
        forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> (a / (a + b)) • x + (b / (a + b)) • y in interior s :=
  ⟨fun h x hx y hy hxy a b ha hb => h hx hy hxy (by positivity) (by positivity) (by field),
    fun h x hx y hy hxy a b ha hb hab => by
    convert! h hx hy hxy ha hb <;> rw [hab, div_one]⟩

/--
theorem `StrictConvex.mem_smul_of_zero_mem` / 定理 `StrictConvex.mem_smul_of_zero_mem`

English:
theorem StrictConvex.mem_smul_of_zero_mem
  statement: (hs : StrictConvex 𝕜 s) (zero_mem : (0 : E) in s)
  proof: by
  rw [mem_smul_set_iff_inv_smul_mem₀ (by positivity)]
  exact hs.smul_mem_of_zero_mem zero_mem hx hx₀ (by positivity) (inv_lt_one_of_one_lt₀ ht)

中文:
定理 StrictConvex.mem_smul_of_zero_mem
  结论: (hs : StrictConvex 𝕜 s) (zero_mem : (0 : E) in s)
  证明: by
  rw [mem_smul_set_iff_inv_smul_mem₀ (by positivity)]
  exact hs.smul_mem_of_zero_mem zero_mem hx hx₀ (by positivity) (inv_lt_one_of_one_lt₀ ht)

Depends on / 依赖: hs.smul_mem_of_zero_mem, smul_mem_of_zero_mem, zero_mem
-/
theorem StrictConvex.mem_smul_of_zero_mem (hs : StrictConvex 𝕜 s) (zero_mem : (0 : E) in s)
    (hx : x in s) (hx₀ : x != 0) {t : 𝕜} (ht : 1 < t) : x in t • interior s := by
  rw [mem_smul_set_iff_inv_smul_mem₀ (by positivity)]
  exact hs.smul_mem_of_zero_mem zero_mem hx hx₀ (by positivity) (inv_lt_one_of_one_lt₀ ht)

end AddCommGroup

end LinearOrderedField

/-!
#### Convex sets in an ordered space

Relates `Convex` and `Set.OrdConnected`.
-/


section

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {s : Set 𝕜}

/-- A set in a linear ordered field is strictly convex if and only if it is convex. -/
@[simp]
/--
theorem `strictConvex_iff_convex` / 定理 `strictConvex_iff_convex`

English:
theorem strictConvex_iff_convex
  statement: StrictConvex 𝕜 s ↔ Convex 𝕜 s
  proof: ⟨StrictConvex.convex, fun hs => hs.ordConnected.strictConvex⟩

中文:
定理 strictConvex_iff_convex
  结论: StrictConvex 𝕜 s ↔ Convex 𝕜 s
  证明: ⟨StrictConvex.convex, fun hs => hs.ordConnected.strictConvex⟩

Depends on / 依赖: StrictConvex, StrictConvex.convex, convex, hs.ordConnected.strictConvex, ordConnected, strictConvex
-/
theorem strictConvex_iff_convex : StrictConvex 𝕜 s ↔ Convex 𝕜 s :=
  ⟨StrictConvex.convex, fun hs => hs.ordConnected.strictConvex⟩

/--
theorem `strictConvex_iff_ordConnected` / 定理 `strictConvex_iff_ordConnected`

English:
theorem strictConvex_iff_ordConnected
  statement: StrictConvex 𝕜 s ↔ s.OrdConnected
  proof: strictConvex_iff_convex.trans convex_iff_ordConnected

alias ⟨StrictConvex.ordConnected, _⟩ := strictConvex_iff_ordConnected

中文:
定理 strictConvex_iff_ordConnected
  结论: StrictConvex 𝕜 s ↔ s.OrdConnected
  证明: strictConvex_iff_convex.trans convex_iff_ordConnected

alias ⟨StrictConvex.ordConnected, _⟩ := strictConvex_iff_ordConnected

Depends on / 依赖: convex_iff_ordConnected, strictConvex_iff_convex, strictConvex_iff_convex.trans
-/
theorem strictConvex_iff_ordConnected : StrictConvex 𝕜 s ↔ s.OrdConnected :=
  strictConvex_iff_convex.trans convex_iff_ordConnected

alias ⟨StrictConvex.ordConnected, _⟩ := strictConvex_iff_ordConnected

end
