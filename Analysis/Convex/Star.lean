/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Module.LinearMap.Prod
public import Mathlib.Algebra.Order.Module.Synonym
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Module

/-!
# Star-convex sets

This file defines star-convex sets (aka star domains, star-shaped set, radially convex set).

A set is star-convex at `x` if every segment from `x` to a point in the set is contained in the set.

This is the prototypical example of a contractible set in homotopy theory (by scaling every point
towards `x`), but has wider uses.

Note that this has nothing to do with star rings, `Star` and co.

## Main declarations

* `StarConvex 𝕜 x s`: `s` is star-convex at `x` with scalars `𝕜`.

## Implementation notes

Instead of saying that a set is star-convex, we say a set is star-convex *at a point*. This has the
advantage of allowing us to talk about convexity as being "everywhere star-convexity" and of making
the union of star-convex sets be star-convex.

Incidentally, this choice means we don't need to assume a set is nonempty for it to be star-convex.
Concretely, the empty set is star-convex at every point.

## TODO

The closure of a star-convex set is star-convex.

A nonempty open star-convex set in `ℝ^n` is diffeomorphic to the entire space.

Replace with `Convexity.IsStarConvexSet`.
-/

@[expose] public section


open Set

open Convex Pointwise

variable {𝕜 E F : Type*}

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section SMul

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 F] (x : E) (s : Set E)

/--
Definition of `StarConvex` / `StarConvex` 的定义

English:
definition StarConvex
  signature: (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  body: forall ⦃y : E⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 -> a • x + b • y in s

中文:
定义 StarConvex
  签名: (𝕜 : 类型) {E : 类型} [半环 𝕜] [偏序 𝕜]
  定义体: forall ⦃y : E⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 -> a • x + b • y in s
-/
def StarConvex (𝕜 : Type*) {E : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] (x : E) (s : Set E) : Prop :=
  forall ⦃y : E⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 -> a • x + b • y in s

variable {𝕜 x s} {t : Set E}

/--
theorem `starConvex_iff_segment_subset` / 定理 `starConvex_iff_segment_subset`

English:
theorem starConvex_iff_segment_subset
  statement: StarConvex 𝕜 x s ↔ forall ⦃y⦄, y in s -> [x -[𝕜] y] subseteq s
  proof: by
  constructor
  · rintro h y hy z ⟨a, b, ha, hb, hab, rfl⟩
    exact h hy ha hb hab
  · rintro h y hy a b ha hb hab
    exact h hy ⟨a, b, ha, hb, hab, rfl⟩

中文:
定理 starConvex_iff_segment_subset
  结论: StarConvex 𝕜 x s ↔ 对任意 ⦃y⦄, y in s -> [x -[𝕜] y] subseteq s
  证明: by
  constructor
  · rintro h y hy z ⟨a, b, ha, hb, hab, rfl⟩
    exact h hy ha hb hab
  · rintro h y hy a b ha hb hab
    exact h hy ⟨a, b, ha, hb, hab, rfl⟩
-/
theorem starConvex_iff_segment_subset : StarConvex 𝕜 x s ↔ forall ⦃y⦄, y in s -> [x -[𝕜] y] subseteq s := by
  constructor
  · rintro h y hy z ⟨a, b, ha, hb, hab, rfl⟩
    exact h hy ha hb hab
  · rintro h y hy a b ha hb hab
    exact h hy ⟨a, b, ha, hb, hab, rfl⟩

/--
theorem `StarConvex.segment_subset` / 定理 `StarConvex.segment_subset`

English:
theorem StarConvex.segment_subset
  given: (h : StarConvex 𝕜 x s) {y : E} (hy : y in s)
  statement: [x -[𝕜] y] subseteq s
  proof: starConvex_iff_segment_subset.1 h hy

中文:
定理 StarConvex.segment_subset
  条件: (h : StarConvex 𝕜 x s) {y : E} (hy : y in s)
  结论: [x -[𝕜] y] subseteq s
  证明: starConvex_iff_segment_subset.1 h hy

Depends on / 依赖: starConvex_iff_segment_subset
-/
theorem StarConvex.segment_subset (h : StarConvex 𝕜 x s) {y : E} (hy : y in s) : [x -[𝕜] y] subseteq s :=
  starConvex_iff_segment_subset.1 h hy

/--
theorem `StarConvex.openSegment_subset` / 定理 `StarConvex.openSegment_subset`

English:
theorem StarConvex.openSegment_subset
  given: (h : StarConvex 𝕜 x s) {y : E} (hy : y in s)
  proof: (openSegment_subset_segment 𝕜 x y).trans (h.segment_subset hy)

中文:
定理 StarConvex.openSegment_subset
  条件: (h : StarConvex 𝕜 x s) {y : E} (hy : y in s)
  证明: (openSegment_subset_segment 𝕜 x y).trans (h.segment_subset hy)

Depends on / 依赖: h.segment_subset, openSegment_subset_segment, segment_subset
-/
theorem StarConvex.openSegment_subset (h : StarConvex 𝕜 x s) {y : E} (hy : y in s) :
    openSegment 𝕜 x y subseteq s :=
  (openSegment_subset_segment 𝕜 x y).trans (h.segment_subset hy)

/--
theorem `starConvex_iff_pointwise_add_subset` / 定理 `starConvex_iff_pointwise_add_subset`

English:
theorem starConvex_iff_pointwise_add_subset
  proof: by
  refine
    ⟨?_, fun h y hy a b ha hb hab =>
      h ha hb hab (add_mem_add (smul_mem_smul_set <| mem_singleton _) ⟨_, hy, rfl⟩)⟩
  rintro hA a b ha hb hab w ⟨au, ⟨u, rfl : u = x, rfl⟩, bv, ⟨v, hv, rfl⟩, rfl⟩
  exact hA hv ha hb hab

中文:
定理 starConvex_iff_pointwise_add_subset
  证明: by
  refine
    ⟨?_, fun h y hy a b ha hb hab =>
      h ha hb hab (add_mem_add (smul_mem_smul_set <| mem_singleton _) ⟨_, hy, rfl⟩)⟩
  rintro hA a b ha hb hab w ⟨au, ⟨u, rfl : u = x, rfl⟩, bv, ⟨v, hv, rfl⟩, rfl⟩
  exact hA hv ha hb hab

Depends on / 依赖: add_mem_add, mem_singleton, smul_mem_smul_set
-/
theorem starConvex_iff_pointwise_add_subset :
    StarConvex 𝕜 x s ↔ forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> a + b = 1 -> a • {x} + b • s subseteq s := by
  refine
    ⟨?_, fun h y hy a b ha hb hab =>
      h ha hb hab (add_mem_add (smul_mem_smul_set <| mem_singleton _) ⟨_, hy, rfl⟩)⟩
  rintro hA a b ha hb hab w ⟨au, ⟨u, rfl : u = x, rfl⟩, bv, ⟨v, hv, rfl⟩, rfl⟩
  exact hA hv ha hb hab

/--
theorem `starConvex_empty` / 定理 `starConvex_empty`

English:
theorem starConvex_empty
  given: (x : E)
  statement: StarConvex 𝕜 x ∅
  proof: fun _ hy => hy.elim

中文:
定理 starConvex_empty
  条件: (x : E)
  结论: StarConvex 𝕜 x ∅
  证明: fun _ hy => hy.elim

Depends on / 依赖: hy.elim
-/
theorem starConvex_empty (x : E) : StarConvex 𝕜 x ∅ := fun _ hy => hy.elim

/--
theorem `starConvex_univ` / 定理 `starConvex_univ`

English:
theorem starConvex_univ
  given: (x : E)
  statement: StarConvex 𝕜 x univ
  proof: fun _ _ _ _ _ _ _ => trivial

中文:
定理 starConvex_univ
  条件: (x : E)
  结论: StarConvex 𝕜 x univ
  证明: fun _ _ _ _ _ _ _ => trivial
-/
theorem starConvex_univ (x : E) : StarConvex 𝕜 x univ := fun _ _ _ _ _ _ _ => trivial

/--
theorem `StarConvex.inter` / 定理 `StarConvex.inter`

English:
theorem StarConvex.inter
  given: (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 x t)
  statement: StarConvex 𝕜 x (s inter t)
  proof: fun _ hy _ _ ha hb hab => ⟨hs hy.left ha hb hab, ht hy.right ha hb hab⟩

中文:
定理 StarConvex.inter
  条件: (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 x t)
  结论: StarConvex 𝕜 x (s inter t)
  证明: fun _ hy _ _ ha hb hab => ⟨hs hy.left ha hb hab, ht hy.right ha hb hab⟩

Depends on / 依赖: hy.left, hy.right
-/
theorem StarConvex.inter (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 x t) : StarConvex 𝕜 x (s inter t) :=
  fun _ hy _ _ ha hb hab => ⟨hs hy.left ha hb hab, ht hy.right ha hb hab⟩

/--
theorem `starConvex_sInter` / 定理 `starConvex_sInter`

English:
theorem starConvex_sInter
  given: {S : Set (Set E)} (h : forall s in S, StarConvex 𝕜 x s)
  proof: fun _ hy _ _ ha hb hab s hs => h s hs (hy s hs) ha hb hab

中文:
定理 starConvex_s整数er
  条件: {S : 集合 (集合 E)} (h : 对任意 s in S, StarConvex 𝕜 x s)
  证明: fun _ hy _ _ ha hb hab s hs => h s hs (hy s hs) ha hb hab
-/
theorem starConvex_sInter {S : Set (Set E)} (h : forall s in S, StarConvex 𝕜 x s) :
    StarConvex 𝕜 x (⋂₀ S) := fun _ hy _ _ ha hb hab s hs => h s hs (hy s hs) ha hb hab

/--
theorem `starConvex_iInter` / 定理 `starConvex_iInter`

English:
theorem starConvex_iInter
  given: {ι : Sort*} {s : ι -> Set E} (h : forall i, StarConvex 𝕜 x (s i))
  proof: sInter_range s ▸ starConvex_sInter forall_mem_range.2 h

中文:
定理 starConvex_i整数er
  条件: {ι : 类型层*} {s : ι -> 集合 E} (h : 对任意 i, StarConvex 𝕜 x (s i))
  证明: sInter_range s ▸ starConvex_sInter forall_mem_range.2 h

Depends on / 依赖: forall_mem_range, sInter_range, starConvex_sInter
-/
theorem starConvex_iInter {ι : Sort*} {s : ι -> Set E} (h : forall i, StarConvex 𝕜 x (s i)) :
    StarConvex 𝕜 x (⋂ i, s i) :=
sInter_range s ▸ starConvex_sInter forall_mem_range.2 h

/--
theorem `starConvex_iInter₂` / 定理 `starConvex_iInter₂`

English:
theorem starConvex_iInter₂
  statement: {ι : Sort*} {κ : ι -> Sort*} {s : (i : ι) -> κ i -> Set E}
  proof: starConvex_iInter fun i => starConvex_iInter (h i)

中文:
定理 starConvex_i整数er₂
  结论: {ι : 类型层*} {κ : ι -> 类型层*} {s : (i : ι) -> κ i -> 集合 E}
  证明: starConvex_iInter fun i => starConvex_iInter (h i)

Depends on / 依赖: starConvex_iInter
-/
theorem starConvex_iInter₂ {ι : Sort*} {κ : ι -> Sort*} {s : (i : ι) -> κ i -> Set E}
    (h : forall i j, StarConvex 𝕜 x (s i j)) : StarConvex 𝕜 x (⋂ (i) (j), s i j) :=
  starConvex_iInter fun i => starConvex_iInter (h i)

/--
theorem `StarConvex.union` / 定理 `StarConvex.union`

English:
theorem StarConvex.union
  given: (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 x t)
  proof: by
  rintro y (hy | hy) a b ha hb hab
  · exact Or.inl (hs hy ha hb hab)
  · exact Or.inr (ht hy ha hb hab)

中文:
定理 StarConvex.union
  条件: (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 x t)
  证明: by
  rintro y (hy | hy) a b ha hb hab
  · exact Or.inl (hs hy ha hb hab)
  · exact Or.inr (ht hy ha hb hab)

Depends on / 依赖: Or.inl, Or.inr
-/
theorem StarConvex.union (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 x t) :
    StarConvex 𝕜 x (s union t) := by
  rintro y (hy | hy) a b ha hb hab
  · exact Or.inl (hs hy ha hb hab)
  · exact Or.inr (ht hy ha hb hab)

/--
theorem `starConvex_iUnion` / 定理 `starConvex_iUnion`

English:
theorem starConvex_iUnion
  given: {ι : Sort*} {s : ι -> Set E} (hs : forall i, StarConvex 𝕜 x (s i))
  proof: by
  rintro y hy a b ha hb hab
  rw [mem_iUnion] at hy ⊢
  obtain ⟨i, hy⟩ := hy
  exact ⟨i, hs i hy ha hb hab⟩

中文:
定理 starConvex_iUnion
  条件: {ι : 类型层*} {s : ι -> 集合 E} (hs : 对任意 i, StarConvex 𝕜 x (s i))
  证明: by
  rintro y hy a b ha hb hab
  rw [mem_iUnion] at hy ⊢
  obtain ⟨i, hy⟩ := hy
  exact ⟨i, hs i hy ha hb hab⟩

Depends on / 依赖: mem_iUnion
-/
theorem starConvex_iUnion {ι : Sort*} {s : ι -> Set E} (hs : forall i, StarConvex 𝕜 x (s i)) :
    StarConvex 𝕜 x (⋃ i, s i) := by
  rintro y hy a b ha hb hab
  rw [mem_iUnion] at hy ⊢
  obtain ⟨i, hy⟩ := hy
  exact ⟨i, hs i hy ha hb hab⟩

/--
theorem `starConvex_iUnion₂` / 定理 `starConvex_iUnion₂`

English:
theorem starConvex_iUnion₂
  statement: {ι : Sort*} {κ : ι -> Sort*} {s : (i : ι) -> κ i -> Set E}
  proof: starConvex_iUnion fun i => starConvex_iUnion (h i)

中文:
定理 starConvex_iUnion₂
  结论: {ι : 类型层*} {κ : ι -> 类型层*} {s : (i : ι) -> κ i -> 集合 E}
  证明: starConvex_iUnion fun i => starConvex_iUnion (h i)

Depends on / 依赖: starConvex_iUnion
-/
theorem starConvex_iUnion₂ {ι : Sort*} {κ : ι -> Sort*} {s : (i : ι) -> κ i -> Set E}
    (h : forall i j, StarConvex 𝕜 x (s i j)) : StarConvex 𝕜 x (⋃ (i) (j), s i j) :=
  starConvex_iUnion fun i => starConvex_iUnion (h i)

/--
theorem `starConvex_sUnion` / 定理 `starConvex_sUnion`

English:
theorem starConvex_sUnion
  given: {S : Set (Set E)} (hS : forall s in S, StarConvex 𝕜 x s)
  proof: by
  rw [sUnion_eq_iUnion]
  exact starConvex_iUnion fun s => hS _ s.2

中文:
定理 starConvex_sUnion
  条件: {S : 集合 (集合 E)} (hS : 对任意 s in S, StarConvex 𝕜 x s)
  证明: by
  rw [sUnion_eq_iUnion]
  exact starConvex_iUnion fun s => hS _ s.2

Depends on / 依赖: sUnion_eq_iUnion, starConvex_iUnion
-/
theorem starConvex_sUnion {S : Set (Set E)} (hS : forall s in S, StarConvex 𝕜 x s) :
    StarConvex 𝕜 x (⋃₀ S) := by
  rw [sUnion_eq_iUnion]
  exact starConvex_iUnion fun s => hS _ s.2

/--
theorem `StarConvex.prod` / 定理 `StarConvex.prod`

English:
theorem StarConvex.prod
  statement: {y : F} {s : Set E} {t : Set F} (hs : StarConvex 𝕜 x s)
  proof: fun _ hy _ _ ha hb hab =>
  ⟨hs hy.1 ha hb hab, ht hy.2 ha hb hab⟩

中文:
定理 StarConvex.乘积
  结论: {y : F} {s : 集合 E} {t : 集合 F} (hs : StarConvex 𝕜 x s)
  证明: fun _ hy _ _ ha hb hab =>
  ⟨hs hy.1 ha hb hab, ht hy.2 ha hb hab⟩
-/
theorem StarConvex.prod {y : F} {s : Set E} {t : Set F} (hs : StarConvex 𝕜 x s)
    (ht : StarConvex 𝕜 y t) : StarConvex 𝕜 (x, y) (s ×ˢ t) := fun _ hy _ _ ha hb hab =>
  ⟨hs hy.1 ha hb hab, ht hy.2 ha hb hab⟩

/--
theorem `starConvex_pi` / 定理 `starConvex_pi`

English:
theorem starConvex_pi
  statement: {ι : Type*} {E : ι -> Type*} [forall i, AddCommMonoid (E i)] [forall i, SMul 𝕜 (E i)]
  proof: fun _ hy _ _ ha hb hab i hi => ht hi (hy i hi) ha hb hab

中文:
定理 starConvex_pi
  结论: {ι : 类型} {E : ι -> 类型} [对任意 i, 加法交换幺半群 (E i)] [对任意 i, 标量乘法 𝕜 (E i)]
  证明: fun _ hy _ _ ha hb hab i hi => ht hi (hy i hi) ha hb hab
-/
theorem starConvex_pi {ι : Type*} {E : ι -> Type*} [forall i, AddCommMonoid (E i)] [forall i, SMul 𝕜 (E i)]
    {x : forall i, E i} {s : Set ι} {t : forall i, Set (E i)} (ht : forall ⦃i⦄, i in s -> StarConvex 𝕜 (x i) (t i)) :
    StarConvex 𝕜 x (s.pi t) := fun _ hy _ _ ha hb hab i hi => ht hi (hy i hi) ha hb hab

end SMul

section Module

variable [Module 𝕜 E] [Module 𝕜 F] {x y z : E} {s : Set E}

/--
theorem `StarConvex.mem` / 定理 `StarConvex.mem`

English:
theorem StarConvex.mem
  given: [ZeroLEOneClass 𝕜] (hs : StarConvex 𝕜 x s) (h : s.Nonempty)
  statement: x in s
  proof: by
  obtain ⟨y, hy⟩ := h
  convert! hs hy zero_le_one le_rfl (add_zero 1)
  rw [one_smul]; rw [zero_smul]; rw [add_zero]

中文:
定理 StarConvex.mem
  条件: [ZeroLEOne类 𝕜] (hs : StarConvex 𝕜 x s) (h : s.非空)
  结论: x in s
  证明: by
  obtain ⟨y, hy⟩ := h
  convert! hs hy zero_le_one le_rfl (add_zero 1)
  rw [one_smul]; rw [zero_smul]; rw [add_zero]

Depends on / 依赖: add_zero, convert, le_rfl, one_smul, zero_le_one, zero_smul
-/
theorem StarConvex.mem [ZeroLEOneClass 𝕜] (hs : StarConvex 𝕜 x s) (h : s.Nonempty) : x in s := by
  obtain ⟨y, hy⟩ := h
  convert! hs hy zero_le_one le_rfl (add_zero 1)
  rw [one_smul]; rw [zero_smul]; rw [add_zero]

/--
theorem `starConvex_iff_forall_pos` / 定理 `starConvex_iff_forall_pos`

English:
theorem starConvex_iff_forall_pos
  given: (hx : x in s)
  statement: StarConvex 𝕜 x s ↔
  proof: by
  refine ⟨fun h y hy a b ha hb hab => h hy ha.le hb.le hab, ?_⟩
  intro h y hy a b ha hb hab
  obtain rfl | ha := ha.eq_or_lt
  · rw [zero_add] at hab
    rwa [hab, one_smul, zero_smul, zero_add]
  obtain rfl | hb := hb.eq_or_lt
  · rw [add_zero] at hab
    rwa [hab, one_smul, zero_smul, add_zero

中文:
定理 starConvex_iff_对任意_pos
  条件: (hx : x in s)
  结论: StarConvex 𝕜 x s ↔
  证明: by
  refine ⟨fun h y hy a b ha hb hab => h hy ha.le hb.le hab, ?_⟩
  intro h y hy a b ha hb hab
  obtain rfl | ha := ha.eq_or_lt
  · rw [zero_add] at hab
    rwa [hab, one_smul, zero_smul, zero_add]
  obtain rfl | hb := hb.eq_or_lt
  · rw [add_zero] at hab
    rwa [hab, one_smul, zero_smul, add_zero

Depends on / 依赖: add_zero, eq_or_lt, ha.eq_or_lt, ha.le, hb.eq_or_lt, hb.le, one_smul, zero_add, zero_smul
-/
theorem starConvex_iff_forall_pos (hx : x in s) : StarConvex 𝕜 x s ↔
    forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • x + b • y in s := by
  refine ⟨fun h y hy a b ha hb hab => h hy ha.le hb.le hab, ?_⟩
  intro h y hy a b ha hb hab
  obtain rfl | ha := ha.eq_or_lt
  · rw [zero_add] at hab
    rwa [hab, one_smul, zero_smul, zero_add]
  obtain rfl | hb := hb.eq_or_lt
  · rw [add_zero] at hab
    rwa [hab, one_smul, zero_smul, add_zero]
  exact h hy ha hb hab

/--
theorem `starConvex_iff_forall_ne_pos` / 定理 `starConvex_iff_forall_ne_pos`

English:
theorem starConvex_iff_forall_ne_pos
  given: (hx : x in s)
  proof: by
  refine ⟨fun h y hy _ a b ha hb hab => h hy ha.le hb.le hab, ?_⟩
  intro h y hy a b ha hb hab
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    rwa [hab, zero_smul, one_smul, zero_add]
  obtain rfl | hb' := hb.eq_or_lt
  · rw [add_zero] at hab
    rwa [hab, zero_smul, one_smul, add_

中文:
定理 starConvex_iff_对任意_ne_pos
  条件: (hx : x in s)
  证明: by
  refine ⟨fun h y hy _ a b ha hb hab => h hy ha.le hb.le hab, ?_⟩
  intro h y hy a b ha hb hab
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    rwa [hab, zero_smul, one_smul, zero_add]
  obtain rfl | hb' := hb.eq_or_lt
  · rw [add_zero] at hab
    rwa [hab, zero_smul, one_smul, add_

Depends on / 依赖: Convex, Convex.combo_self, add_zero, combo_self, eq_or_lt, eq_or_ne, ha.eq_or_lt, ha.le, hb.eq_or_lt, hb.le, one_smul, zero_add, zero_smul
-/
theorem starConvex_iff_forall_ne_pos (hx : x in s) :
    StarConvex 𝕜 x s ↔
      forall ⦃y⦄, y in s -> x != y -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 -> a • x + b • y in s := by
  refine ⟨fun h y hy _ a b ha hb hab => h hy ha.le hb.le hab, ?_⟩
  intro h y hy a b ha hb hab
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    rwa [hab, zero_smul, one_smul, zero_add]
  obtain rfl | hb' := hb.eq_or_lt
  · rw [add_zero] at hab
    rwa [hab, zero_smul, one_smul, add_zero]
  obtain rfl | hxy := eq_or_ne x y
  · rwa [Convex.combo_self hab]
  exact h hy hxy ha' hb' hab

/--
theorem `starConvex_iff_openSegment_subset` / 定理 `starConvex_iff_openSegment_subset`

English:
theorem starConvex_iff_openSegment_subset
  given: [ZeroLEOneClass 𝕜] (hx : x in s)
  proof: starConvex_iff_segment_subset.trans
    forall₂_congr fun _ hy => (openSegment_subset_iff_segment_subset hx hy).symm

中文:
定理 starConvex_iff_openSegment_subset
  条件: [ZeroLEOne类 𝕜] (hx : x in s)
  证明: starConvex_iff_segment_subset.trans
    forall₂_congr fun _ hy => (openSegment_subset_iff_segment_subset hx hy).symm

Depends on / 依赖: openSegment_subset_iff_segment_subset, starConvex_iff_segment_subset, starConvex_iff_segment_subset.trans
-/
theorem starConvex_iff_openSegment_subset [ZeroLEOneClass 𝕜] (hx : x in s) :
    StarConvex 𝕜 x s ↔ forall ⦃y⦄, y in s -> openSegment 𝕜 x y subseteq s :=
starConvex_iff_segment_subset.trans
    forall₂_congr fun _ hy => (openSegment_subset_iff_segment_subset hx hy).symm

/--
theorem `starConvex_singleton` / 定理 `starConvex_singleton`

English:
theorem starConvex_singleton
  given: (x : E)
  statement: StarConvex 𝕜 x {x}
  proof: by
  rintro y (rfl : y = x) a b _ _ hab
  exact Convex.combo_self hab _

中文:
定理 starConvex_singleton
  条件: (x : E)
  结论: StarConvex 𝕜 x {x}
  证明: by
  rintro y (rfl : y = x) a b _ _ hab
  exact Convex.combo_self hab _

Depends on / 依赖: Convex, Convex.combo_self, combo_self
-/
theorem starConvex_singleton (x : E) : StarConvex 𝕜 x {x} := by
  rintro y (rfl : y = x) a b _ _ hab
  exact Convex.combo_self hab _

/--
theorem `StarConvex.linear_image` / 定理 `StarConvex.linear_image`

English:
theorem StarConvex.linear_image
  given: (hs : StarConvex 𝕜 x s) (f : E ->ₗ[𝕜] F)
  proof: by
  rintro _ ⟨y, hy, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, hs hy ha hb hab, by rw [f.map_add, f.map_smul, f.map_smul]⟩

中文:
定理 StarConvex.linear_image
  条件: (hs : StarConvex 𝕜 x s) (f : E ->ₗ[𝕜] F)
  证明: by
  rintro _ ⟨y, hy, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, hs hy ha hb hab, by rw [f.map_add, f.map_smul, f.map_smul]⟩

Depends on / 依赖: f.map_add, f.map_smul, map_add, map_smul
-/
theorem StarConvex.linear_image (hs : StarConvex 𝕜 x s) (f : E ->ₗ[𝕜] F) :
    StarConvex 𝕜 (f x) (f '' s) := by
  rintro _ ⟨y, hy, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, hs hy ha hb hab, by rw [f.map_add, f.map_smul, f.map_smul]⟩

/--
theorem `StarConvex.is_linear_image` / 定理 `StarConvex.is_linear_image`

English:
theorem StarConvex.is_linear_image
  given: (hs : StarConvex 𝕜 x s) {f : E -> F} (hf : IsLinearMap 𝕜 f)
  proof: hs.linear_image hf.mk' f

中文:
定理 StarConvex.is_linear_image
  条件: (hs : StarConvex 𝕜 x s) {f : E -> F} (hf : 是线性映射 𝕜 f)
  证明: hs.linear_image hf.mk' f

Depends on / 依赖: hf.mk, hs.linear_image, linear_image
-/
theorem StarConvex.is_linear_image (hs : StarConvex 𝕜 x s) {f : E -> F} (hf : IsLinearMap 𝕜 f) :
    StarConvex 𝕜 (f x) (f '' s) :=
hs.linear_image hf.mk' f

/--
theorem `StarConvex.linear_preimage` / 定理 `StarConvex.linear_preimage`

English:
theorem StarConvex.linear_preimage
  given: {s : Set F} (f : E ->ₗ[𝕜] F) (hs : StarConvex 𝕜 (f x) s)
  proof: by
  intro y hy a b ha hb hab
  rw [mem_preimage]; rw [f.map_add]; rw [f.map_smul]; rw [f.map_smul]
  exact hs hy ha hb hab

中文:
定理 StarConvex.linear_preimage
  条件: {s : 集合 F} (f : E ->ₗ[𝕜] F) (hs : StarConvex 𝕜 (f x) s)
  证明: by
  intro y hy a b ha hb hab
  rw [mem_preimage]; rw [f.map_add]; rw [f.map_smul]; rw [f.map_smul]
  exact hs hy ha hb hab

Depends on / 依赖: f.map_add, f.map_smul, map_add, map_smul, mem_preimage
-/
theorem StarConvex.linear_preimage {s : Set F} (f : E ->ₗ[𝕜] F) (hs : StarConvex 𝕜 (f x) s) :
    StarConvex 𝕜 x (f ⁻¹' s) := by
  intro y hy a b ha hb hab
  rw [mem_preimage]; rw [f.map_add]; rw [f.map_smul]; rw [f.map_smul]
  exact hs hy ha hb hab

/--
theorem `StarConvex.is_linear_preimage` / 定理 `StarConvex.is_linear_preimage`

English:
theorem StarConvex.is_linear_preimage
  statement: {s : Set F} {f : E -> F} (hs : StarConvex 𝕜 (f x) s)
  proof: hs.linear_preimage hf.mk' f

中文:
定理 StarConvex.is_linear_preimage
  结论: {s : 集合 F} {f : E -> F} (hs : StarConvex 𝕜 (f x) s)
  证明: hs.linear_preimage hf.mk' f

Depends on / 依赖: hf.mk, hs.linear_preimage, linear_preimage
-/
theorem StarConvex.is_linear_preimage {s : Set F} {f : E -> F} (hs : StarConvex 𝕜 (f x) s)
    (hf : IsLinearMap 𝕜 f) : StarConvex 𝕜 x (preimage f s) :=
hs.linear_preimage hf.mk' f

/--
theorem `StarConvex.add` / 定理 `StarConvex.add`

English:
theorem StarConvex.add
  given: {t : Set E} (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t)
  proof: by
  rw [← add_image_prod]
  exact (hs.prod ht).is_linear_image IsLinearMap.isLinearMap_add

中文:
定理 StarConvex.add
  条件: {t : 集合 E} (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t)
  证明: by
  rw [← add_image_prod]
  exact (hs.prod ht).is_linear_image IsLinearMap.isLinearMap_add

Depends on / 依赖: IsLinearMap, IsLinearMap.isLinearMap_add, add_image_prod, hs.prod, isLinearMap_add, is_linear_image
-/
theorem StarConvex.add {t : Set E} (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t) :
    StarConvex 𝕜 (x + y) (s + t) := by
  rw [← add_image_prod]
  exact (hs.prod ht).is_linear_image IsLinearMap.isLinearMap_add

/--
theorem `StarConvex.add_left` / 定理 `StarConvex.add_left`

English:
theorem StarConvex.add_left
  given: (hs : StarConvex 𝕜 x s) (z : E)
  proof: by
  intro y hy a b ha hb hab
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨a • x + b • y', hs hy' ha hb hab, ?_⟩
  match_scalars <;> simp [hab]

中文:
定理 StarConvex.add_left
  条件: (hs : StarConvex 𝕜 x s) (z : E)
  证明: by
  intro y hy a b ha hb hab
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨a • x + b • y', hs hy' ha hb hab, ?_⟩
  match_scalars <;> simp [hab]

Depends on / 依赖: match_scalars
-/
theorem StarConvex.add_left (hs : StarConvex 𝕜 x s) (z : E) :
    StarConvex 𝕜 (z + x) ((fun x => z + x) '' s) := by
  intro y hy a b ha hb hab
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨a • x + b • y', hs hy' ha hb hab, ?_⟩
  match_scalars <;> simp [hab]

/--
theorem `StarConvex.add_right` / 定理 `StarConvex.add_right`

English:
theorem StarConvex.add_right
  given: (hs : StarConvex 𝕜 x s) (z : E)
  proof: by
  intro y hy a b ha hb hab
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨a • x + b • y', hs hy' ha hb hab, ?_⟩
  match_scalars <;> simp [hab]

中文:
定理 StarConvex.add_right
  条件: (hs : StarConvex 𝕜 x s) (z : E)
  证明: by
  intro y hy a b ha hb hab
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨a • x + b • y', hs hy' ha hb hab, ?_⟩
  match_scalars <;> simp [hab]

Depends on / 依赖: match_scalars
-/
theorem StarConvex.add_right (hs : StarConvex 𝕜 x s) (z : E) :
    StarConvex 𝕜 (x + z) ((fun x => x + z) '' s) := by
  intro y hy a b ha hb hab
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨a • x + b • y', hs hy' ha hb hab, ?_⟩
  match_scalars <;> simp [hab]

/--
theorem `StarConvex.preimage_add_right` / 定理 `StarConvex.preimage_add_right`

English:
theorem StarConvex.preimage_add_right
  given: (hs : StarConvex 𝕜 (z + x) s)
  proof: by
  intro y hy a b ha hb hab
  have h := hs hy ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul] at h

中文:
定理 StarConvex.preimage_add_right
  条件: (hs : StarConvex 𝕜 (z + x) s)
  证明: by
  intro y hy a b ha hb hab
  have h := hs hy ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul] at h

Depends on / 依赖: add_add_add_comm, add_smul, one_smul, smul_add
-/
theorem StarConvex.preimage_add_right (hs : StarConvex 𝕜 (z + x) s) :
    StarConvex 𝕜 x ((fun x => z + x) ⁻¹' s) := by
  intro y hy a b ha hb hab
  have h := hs hy ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul] at h

/--
theorem `StarConvex.preimage_add_left` / 定理 `StarConvex.preimage_add_left`

English:
theorem StarConvex.preimage_add_left
  given: (hs : StarConvex 𝕜 (x + z) s)
  proof: by
  rw [add_comm] at hs
  simpa only [add_comm] using hs.preimage_add_right

中文:
定理 StarConvex.preimage_add_left
  条件: (hs : StarConvex 𝕜 (x + z) s)
  证明: by
  rw [add_comm] at hs
  simpa only [add_comm] using hs.preimage_add_right

Depends on / 依赖: add_comm, hs.preimage_add_right, preimage_add_right
-/
theorem StarConvex.preimage_add_left (hs : StarConvex 𝕜 (x + z) s) :
    StarConvex 𝕜 x ((fun x => x + z) ⁻¹' s) := by
  rw [add_comm] at hs
  simpa only [add_comm] using hs.preimage_add_right

end Module

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup E] [Module 𝕜 E] {x y : E}

/--
theorem `StarConvex.sub'` / 定理 `StarConvex.sub'`

English:
theorem StarConvex.sub'
  given: {s : Set (E × E)} (hs : StarConvex 𝕜 (x, y) s)
  proof: hs.is_linear_image IsLinearMap.isLinearMap_sub

中文:
定理 StarConvex.sub'
  条件: {s : 集合 (E × E)} (hs : StarConvex 𝕜 (x, y) s)
  证明: hs.is_linear_image IsLinearMap.isLinearMap_sub

Depends on / 依赖: IsLinearMap, IsLinearMap.isLinearMap_sub, hs.is_linear_image, isLinearMap_sub, is_linear_image
-/
theorem StarConvex.sub' {s : Set (E × E)} (hs : StarConvex 𝕜 (x, y) s) :
    StarConvex 𝕜 (x - y) ((fun x : E × E => x.1 - x.2) '' s) :=
  hs.is_linear_image IsLinearMap.isLinearMap_sub

end AddCommGroup

end OrderedSemiring

section OrderedCommSemiring

variable [CommSemiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F] {x : E} {s : Set E}

/--
theorem `StarConvex.smul` / 定理 `StarConvex.smul`

English:
theorem StarConvex.smul
  given: (hs : StarConvex 𝕜 x s) (c : 𝕜)
  statement: StarConvex 𝕜 (c • x) (c • s)
  proof: hs.linear_image LinearMap.lsmul _ _ c

中文:
定理 StarConvex.smul
  条件: (hs : StarConvex 𝕜 x s) (c : 𝕜)
  结论: StarConvex 𝕜 (c • x) (c • s)
  证明: hs.linear_image LinearMap.lsmul _ _ c

Depends on / 依赖: LinearMap, LinearMap.lsmul, hs.linear_image, linear_image
-/
theorem StarConvex.smul (hs : StarConvex 𝕜 x s) (c : 𝕜) : StarConvex 𝕜 (c • x) (c • s) :=
hs.linear_image LinearMap.lsmul _ _ c

/--
theorem `StarConvex.zero_smul` / 定理 `StarConvex.zero_smul`

English:
theorem StarConvex.zero_smul
  given: (hs : StarConvex 𝕜 0 s) (c : 𝕜)
  statement: StarConvex 𝕜 0 (c • s)
  proof: by
  simpa using hs.smul c

中文:
定理 StarConvex.zero_smul
  条件: (hs : StarConvex 𝕜 0 s) (c : 𝕜)
  结论: StarConvex 𝕜 0 (c • s)
  证明: by
  simpa using hs.smul c

Depends on / 依赖: hs.smul
-/
theorem StarConvex.zero_smul (hs : StarConvex 𝕜 0 s) (c : 𝕜) : StarConvex 𝕜 0 (c • s) := by
  simpa using hs.smul c

/--
theorem `StarConvex.preimage_smul` / 定理 `StarConvex.preimage_smul`

English:
theorem StarConvex.preimage_smul
  given: {c : 𝕜} (hs : StarConvex 𝕜 (c • x) s)
  proof: hs.linear_preimage (LinearMap.lsmul _ _ c)

中文:
定理 StarConvex.preimage_smul
  条件: {c : 𝕜} (hs : StarConvex 𝕜 (c • x) s)
  证明: hs.linear_preimage (LinearMap.lsmul _ _ c)

Depends on / 依赖: LinearMap, LinearMap.lsmul, hs.linear_preimage, linear_preimage
-/
theorem StarConvex.preimage_smul {c : 𝕜} (hs : StarConvex 𝕜 (c • x) s) :
    StarConvex 𝕜 x ((fun z => c • z) ⁻¹' s) :=
  hs.linear_preimage (LinearMap.lsmul _ _ c)

/--
theorem `StarConvex.affinity` / 定理 `StarConvex.affinity`

English:
theorem StarConvex.affinity
  given: (hs : StarConvex 𝕜 x s) (z : E) (c : 𝕜)
  proof: by
  have h := (hs.smul c).add_left z
  rwa [← image_smul, image_image] at h

中文:
定理 StarConvex.affinity
  条件: (hs : StarConvex 𝕜 x s) (z : E) (c : 𝕜)
  证明: by
  have h := (hs.smul c).add_left z
  rwa [← image_smul, image_image] at h

Depends on / 依赖: add_left, hs.smul, image_image, image_smul
-/
theorem StarConvex.affinity (hs : StarConvex 𝕜 x s) (z : E) (c : 𝕜) :
    StarConvex 𝕜 (z + c • x) ((fun x => z + c • x) '' s) := by
  have h := (hs.smul c).add_left z
  rwa [← image_smul, image_image] at h

end AddCommMonoid

end OrderedCommSemiring

section OrderedRing

variable [Ring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddRightMono 𝕜] [AddCommMonoid E] [SMulWithZero 𝕜 E] {s : Set E}

/--
theorem `starConvex_zero_iff` / 定理 `starConvex_zero_iff`

English:
theorem starConvex_zero_iff
  proof: by
  refine
    forall_congr' fun x => forall_congr' fun _ => ⟨fun h a ha₀ ha₁ => ?_, fun h a b ha hb hab => ?_⟩
  · simpa only [sub_add_cancel, eq_self_iff_true, forall_true_left, zero_add, smul_zero] using
      h (sub_nonneg_of_le ha₁) ha₀
  · rw [smul_zero, zero_add]
    exact h hb (by rw [← hab

中文:
定理 starConvex_zero_iff
  证明: by
  refine
    forall_congr' fun x => forall_congr' fun _ => ⟨fun h a ha₀ ha₁ => ?_, fun h a b ha hb hab => ?_⟩
  · simpa only [sub_add_cancel, eq_self_iff_true, forall_true_left, zero_add, smul_zero] using
      h (sub_nonneg_of_le ha₁) ha₀
  · rw [smul_zero, zero_add]
    exact h hb (by rw [← hab

Depends on / 依赖: eq_self_iff_true, forall_congr, forall_true_left, le_add_of_nonneg_left, smul_zero, sub_add_cancel, sub_nonneg_of_le, zero_add
-/
theorem starConvex_zero_iff :
    StarConvex 𝕜 0 s ↔ forall ⦃x : E⦄, x in s -> forall ⦃a : 𝕜⦄, 0 <= a -> a <= 1 -> a • x in s := by
  refine
    forall_congr' fun x => forall_congr' fun _ => ⟨fun h a ha₀ ha₁ => ?_, fun h a b ha hb hab => ?_⟩
  · simpa only [sub_add_cancel, eq_self_iff_true, forall_true_left, zero_add, smul_zero] using
      h (sub_nonneg_of_le ha₁) ha₀
  · rw [smul_zero, zero_add]
    exact h hb (by rw [← hab]; exact le_add_of_nonneg_left ha)

end AddCommMonoid

section AddCommGroup

section AddRightMono

variable [AddRightMono 𝕜] [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]
  {x y : E} {s t : Set E}

/--
theorem `StarConvex.add_smul_mem` / 定理 `StarConvex.add_smul_mem`

English:
theorem StarConvex.add_smul_mem
  statement: (hs : StarConvex 𝕜 x s) (hy : x + y in s) {t : 𝕜} (ht₀ : 0 <= t)
  proof: by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by
    rw [smul_add]; rw [← add_assoc]; rw [← add_smul]; rw [sub_add_cancel]; rw [one_smul]
  rw [h]
  exact hs hy (sub_nonneg_of_le ht₁) ht₀ (sub_add_cancel _ _)

中文:
定理 StarConvex.add_smul_mem
  结论: (hs : StarConvex 𝕜 x s) (hy : x + y in s) {t : 𝕜} (ht₀ : 0 <= t)
  证明: by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by
    rw [smul_add]; rw [← add_assoc]; rw [← add_smul]; rw [sub_add_cancel]; rw [one_smul]
  rw [h]
  exact hs hy (sub_nonneg_of_le ht₁) ht₀ (sub_add_cancel _ _)

Depends on / 依赖: add_assoc, add_smul, one_smul, smul_add, sub_add_cancel, sub_nonneg_of_le
-/
theorem StarConvex.add_smul_mem (hs : StarConvex 𝕜 x s) (hy : x + y in s) {t : 𝕜} (ht₀ : 0 <= t)
    (ht₁ : t <= 1) : x + t • y in s := by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by
    rw [smul_add]; rw [← add_assoc]; rw [← add_smul]; rw [sub_add_cancel]; rw [one_smul]
  rw [h]
  exact hs hy (sub_nonneg_of_le ht₁) ht₀ (sub_add_cancel _ _)

/--
theorem `StarConvex.smul_mem` / 定理 `StarConvex.smul_mem`

English:
theorem StarConvex.smul_mem
  statement: (hs : StarConvex 𝕜 0 s) (hx : x in s) {t : 𝕜} (ht₀ : 0 <= t)
  proof: by simpa using hs.add_smul_mem (by simpa using hx) ht₀ ht₁

中文:
定理 StarConvex.smul_mem
  结论: (hs : StarConvex 𝕜 0 s) (hx : x in s) {t : 𝕜} (ht₀ : 0 <= t)
  证明: by simpa using hs.add_smul_mem (by simpa using hx) ht₀ ht₁

Depends on / 依赖: add_smul_mem, hs.add_smul_mem
-/
theorem StarConvex.smul_mem (hs : StarConvex 𝕜 0 s) (hx : x in s) {t : 𝕜} (ht₀ : 0 <= t)
    (ht₁ : t <= 1) : t • x in s := by simpa using hs.add_smul_mem (by simpa using hx) ht₀ ht₁

/--
theorem `StarConvex.add_smul_sub_mem` / 定理 `StarConvex.add_smul_sub_mem`

English:
theorem StarConvex.add_smul_sub_mem
  statement: (hs : StarConvex 𝕜 x s) (hy : y in s) {t : 𝕜} (ht₀ : 0 <= t)
  proof: by
  apply hs.segment_subset hy
  rw [segment_eq_image']
  exact mem_image_of_mem _ ⟨ht₀, ht₁⟩

中文:
定理 StarConvex.add_smul_sub_mem
  结论: (hs : StarConvex 𝕜 x s) (hy : y in s) {t : 𝕜} (ht₀ : 0 <= t)
  证明: by
  apply hs.segment_subset hy
  rw [segment_eq_image']
  exact mem_image_of_mem _ ⟨ht₀, ht₁⟩

Depends on / 依赖: hs.segment_subset, mem_image_of_mem, segment_eq_image, segment_subset
-/
theorem StarConvex.add_smul_sub_mem (hs : StarConvex 𝕜 x s) (hy : y in s) {t : 𝕜} (ht₀ : 0 <= t)
    (ht₁ : t <= 1) : x + t • (y - x) in s := by
  apply hs.segment_subset hy
  rw [segment_eq_image']
  exact mem_image_of_mem _ ⟨ht₀, ht₁⟩

end AddRightMono

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {x y : E} {s t : Set E}

/--
theorem `StarConvex.affine_preimage` / 定理 `StarConvex.affine_preimage`

English:
theorem StarConvex.affine_preimage
  given: (f : E ->ᵃ[𝕜] F) {s : Set F} (hs : StarConvex 𝕜 (f x) s)
  proof: by
  intro y hy a b ha hb hab
  rw [mem_preimage]; rw [Convex.combo_affine_apply hab]
  exact hs hy ha hb hab

中文:
定理 StarConvex.affine_preimage
  条件: (f : E ->ᵃ[𝕜] F) {s : 集合 F} (hs : StarConvex 𝕜 (f x) s)
  证明: by
  intro y hy a b ha hb hab
  rw [mem_preimage]; rw [Convex.combo_affine_apply hab]
  exact hs hy ha hb hab

Depends on / 依赖: Convex, Convex.combo_affine_apply, combo_affine_apply, mem_preimage
-/
theorem StarConvex.affine_preimage (f : E ->ᵃ[𝕜] F) {s : Set F} (hs : StarConvex 𝕜 (f x) s) :
    StarConvex 𝕜 x (f ⁻¹' s) := by
  intro y hy a b ha hb hab
  rw [mem_preimage]; rw [Convex.combo_affine_apply hab]
  exact hs hy ha hb hab

/--
theorem `StarConvex.affine_image` / 定理 `StarConvex.affine_image`

English:
theorem StarConvex.affine_image
  given: (f : E ->ᵃ[𝕜] F) {s : Set E} (hs : StarConvex 𝕜 x s)
  proof: by
  rintro y ⟨y', ⟨hy', hy'f⟩⟩ a b ha hb hab
  refine ⟨a • x + b • y', ⟨hs hy' ha hb hab, ?_⟩⟩
  rw [Convex.combo_affine_apply hab]; rw [hy'f]

中文:
定理 StarConvex.affine_image
  条件: (f : E ->ᵃ[𝕜] F) {s : 集合 E} (hs : StarConvex 𝕜 x s)
  证明: by
  rintro y ⟨y', ⟨hy', hy'f⟩⟩ a b ha hb hab
  refine ⟨a • x + b • y', ⟨hs hy' ha hb hab, ?_⟩⟩
  rw [Convex.combo_affine_apply hab]; rw [hy'f]

Depends on / 依赖: Convex, Convex.combo_affine_apply, combo_affine_apply
-/
theorem StarConvex.affine_image (f : E ->ᵃ[𝕜] F) {s : Set E} (hs : StarConvex 𝕜 x s) :
    StarConvex 𝕜 (f x) (f '' s) := by
  rintro y ⟨y', ⟨hy', hy'f⟩⟩ a b ha hb hab
  refine ⟨a • x + b • y', ⟨hs hy' ha hb hab, ?_⟩⟩
  rw [Convex.combo_affine_apply hab]; rw [hy'f]

/--
theorem `StarConvex.neg` / 定理 `StarConvex.neg`

English:
theorem StarConvex.neg
  given: (hs : StarConvex 𝕜 x s)
  statement: StarConvex 𝕜 (-x) (-s)
  proof: by
  rw [← image_neg_eq_neg]
  exact hs.is_linear_image IsLinearMap.isLinearMap_neg

中文:
定理 StarConvex.neg
  条件: (hs : StarConvex 𝕜 x s)
  结论: StarConvex 𝕜 (-x) (-s)
  证明: by
  rw [← image_neg_eq_neg]
  exact hs.is_linear_image IsLinearMap.isLinearMap_neg

Depends on / 依赖: IsLinearMap, IsLinearMap.isLinearMap_neg, hs.is_linear_image, image_neg_eq_neg, isLinearMap_neg, is_linear_image
-/
theorem StarConvex.neg (hs : StarConvex 𝕜 x s) : StarConvex 𝕜 (-x) (-s) := by
  rw [← image_neg_eq_neg]
  exact hs.is_linear_image IsLinearMap.isLinearMap_neg

/--
theorem `StarConvex.sub` / 定理 `StarConvex.sub`

English:
theorem StarConvex.sub
  given: (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t)
  proof: by
  simp_rw [sub_eq_add_neg]
  exact hs.add ht.neg

中文:
定理 StarConvex.sub
  条件: (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t)
  证明: by
  simp_rw [sub_eq_add_neg]
  exact hs.add ht.neg

Depends on / 依赖: hs.add, ht.neg, simp_rw, sub_eq_add_neg
-/
theorem StarConvex.sub (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t) :
    StarConvex 𝕜 (x - y) (s - t) := by
  simp_rw [sub_eq_add_neg]
  exact hs.add ht.neg

end AddCommGroup

section OrderedAddCommGroup

variable [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module 𝕜 E]
  [IsStrictOrderedModule 𝕜 E] [PosSMulReflectLT 𝕜 E] {x y : E}

/--
lemma `starConvex_compl_Iic` / 引理 `starConvex_compl_Iic`

English:
lemma starConvex_compl_Iic
  given: (h : x < y)
  statement: StarConvex 𝕜 y (Iic x)ᶜ
  proof: by
  refine (starConvex_iff_forall_pos <| by simp [h.not_ge]).mpr fun z hz a b ha hb hab => ?_
  rw [mem_compl_iff]; rw [mem_Iic] at hz ⊢
  contrapose hz
  refine (lt_of_smul_lt_smul_of_nonneg_left ?_ hb.le).le
  calc
    b • z <= (a + b) • x - a • y := by rwa [le_sub_iff_add_le', hab, one_smul]
   

中文:
引理 starConvex_compl_Iic
  条件: (h : x < y)
  结论: StarConvex 𝕜 y (左无界右闭区间 x)ᶜ
  证明: by
  refine (starConvex_iff_forall_pos <| by simp [h.not_ge]).mpr fun z hz a b ha hb hab => ?_
  rw [mem_compl_iff]; rw [mem_Iic] at hz ⊢
  contrapose hz
  refine (lt_of_smul_lt_smul_of_nonneg_left ?_ hb.le).le
  calc
    b • z <= (a + b) • x - a • y := by rwa [le_sub_iff_add_le', hab, one_smul]
   

Depends on / 依赖: add_smul, contrapose, h.not_ge, hb.le, le_sub_iff_add_le, lt_of_smul_lt_smul_of_nonneg_left, mem_Iic, mem_compl_iff, not_ge, one_smul, starConvex_iff_forall_pos, sub_lt_iff_lt_add
-/
lemma starConvex_compl_Iic (h : x < y) : StarConvex 𝕜 y (Iic x)ᶜ := by
  refine (starConvex_iff_forall_pos <| by simp [h.not_ge]).mpr fun z hz a b ha hb hab => ?_
  rw [mem_compl_iff]; rw [mem_Iic] at hz ⊢
  contrapose hz
  refine (lt_of_smul_lt_smul_of_nonneg_left ?_ hb.le).le
  calc
    b • z <= (a + b) • x - a • y := by rwa [le_sub_iff_add_le', hab, one_smul]
    _ < b • x := by
      rw [add_smul]; rw [sub_lt_iff_lt_add']
      gcongr

/--
lemma `starConvex_compl_Ici` / 引理 `starConvex_compl_Ici`

English:
lemma starConvex_compl_Ici
  given: (h : x < y)
  statement: StarConvex 𝕜 x (Ici y)ᶜ
  proof: starConvex_compl_Iic (E := Eᵒᵈ) h

中文:
引理 starConvex_compl_Ici
  条件: (h : x < y)
  结论: StarConvex 𝕜 x (左闭右无界区间 y)ᶜ
  证明: starConvex_compl_Iic (E := Eᵒᵈ) h

Depends on / 依赖: starConvex_compl_Iic
-/
lemma starConvex_compl_Ici (h : x < y) : StarConvex 𝕜 x (Ici y)ᶜ :=
  starConvex_compl_Iic (E := Eᵒᵈ) h

end OrderedAddCommGroup

end OrderedRing

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

section AddCommGroup

variable [AddCommGroup E] [Module 𝕜 E] {x : E} {s : Set E}

/--
theorem `starConvex_iff_div` / 定理 `starConvex_iff_div`

English:
theorem starConvex_iff_div
  statement: StarConvex 𝕜 x s ↔ forall ⦃y⦄, y in s ->
  proof: ⟨fun h y hy a b ha hb hab => by
    apply h hy
    · positivity
    · positivity
    · rw [← add_div]
      exact div_self hab.ne',
  fun h y hy a b ha hb hab => by
    have h' := h hy ha hb
    rw [hab]; rw [div_one]; rw [div_one] at h'
    exact h' zero_lt_one⟩

中文:
定理 starConvex_iff_div
  结论: StarConvex 𝕜 x s ↔ 对任意 ⦃y⦄, y in s ->
  证明: ⟨fun h y hy a b ha hb hab => by
    apply h hy
    · positivity
    · positivity
    · rw [← add_div]
      exact div_self hab.ne',
  fun h y hy a b ha hb hab => by
    have h' := h hy ha hb
    rw [hab]; rw [div_one]; rw [div_one] at h'
    exact h' zero_lt_one⟩

Depends on / 依赖: add_div, div_one, div_self, hab.ne, zero_lt_one
-/
theorem starConvex_iff_div : StarConvex 𝕜 x s ↔ forall ⦃y⦄, y in s ->
    forall ⦃a b : 𝕜⦄, 0 <= a -> 0 <= b -> 0 < a + b -> (a / (a + b)) • x + (b / (a + b)) • y in s :=
  ⟨fun h y hy a b ha hb hab => by
    apply h hy
    · positivity
    · positivity
    · rw [← add_div]
      exact div_self hab.ne',
  fun h y hy a b ha hb hab => by
    have h' := h hy ha hb
    rw [hab]; rw [div_one]; rw [div_one] at h'
    exact h' zero_lt_one⟩

/--
theorem `StarConvex.mem_smul` / 定理 `StarConvex.mem_smul`

English:
theorem StarConvex.mem_smul
  given: (hs : StarConvex 𝕜 0 s) (hx : x in s) {t : 𝕜} (ht : 1 <= t)
  proof: by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne']
  exact hs.smul_mem hx (by positivity) (inv_le_one_of_one_le₀ ht)

中文:
定理 StarConvex.mem_smul
  条件: (hs : StarConvex 𝕜 0 s) (hx : x in s) {t : 𝕜} (ht : 1 <= t)
  证明: by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne']
  exact hs.smul_mem hx (by positivity) (inv_le_one_of_one_le₀ ht)

Depends on / 依赖: hs.smul_mem, smul_mem, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem StarConvex.mem_smul (hs : StarConvex 𝕜 0 s) (hx : x in s) {t : 𝕜} (ht : 1 <= t) :
    x in t • s := by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne']
  exact hs.smul_mem hx (by positivity) (inv_le_one_of_one_le₀ ht)

end AddCommGroup

end LinearOrderedField

/-!
#### Star-convex sets in an ordered space

Relates `starConvex` and `Set.ordConnected`.
-/

section OrdConnected

/--
theorem `Set.OrdConnected.starConvex` / 定理 `Set.OrdConnected.starConvex`

English:
theorem Set.OrdConnected.starConvex
  statement: [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [PartialOrder E]
  proof: by
  intro y hy a b ha hb hab
  obtain hxy | hyx := h _ hy
  · refine hs.out hx hy (mem_Icc.2 ⟨?_, ?_⟩)
    · calc
        x = a • x + b • x := (Convex.combo_self hab _).symm
        _ <= a • x + b • y := by gcongr
    calc
      a • x + b • y <= a • y + b • y := by gcongr
      _ = y := Convex.comb

中文:
定理 集合.序连通.starConvex
  结论: [半环 𝕜] [偏序 𝕜] [加法交换幺半群 E] [偏序 E]
  证明: by
  intro y hy a b ha hb hab
  obtain hxy | hyx := h _ hy
  · refine hs.out hx hy (mem_Icc.2 ⟨?_, ?_⟩)
    · calc
        x = a • x + b • x := (Convex.combo_self hab _).symm
        _ <= a • x + b • y := by gcongr
    calc
      a • x + b • y <= a • y + b • y := by gcongr
      _ = y := Convex.comb

Depends on / 依赖: Convex, Convex.combo_self, combo_self, hs.out, mem_Icc
-/
theorem Set.OrdConnected.starConvex [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module 𝕜 E] [PosSMulMono 𝕜 E] {x : E} {s : Set E} (hs : s.OrdConnected)
    (hx : x in s) (h : forall y in s, x <= y ∨ y <= x) : StarConvex 𝕜 x s := by
  intro y hy a b ha hb hab
  obtain hxy | hyx := h _ hy
  · refine hs.out hx hy (mem_Icc.2 ⟨?_, ?_⟩)
    · calc
        x = a • x + b • x := (Convex.combo_self hab _).symm
        _ <= a • x + b • y := by gcongr
    calc
      a • x + b • y <= a • y + b • y := by gcongr
      _ = y := Convex.combo_self hab _
  · refine hs.out hy hx (mem_Icc.2 ⟨?_, ?_⟩)
    · calc
        y = a • y + b • y := (Convex.combo_self hab _).symm
        _ <= a • x + b • y := by gcongr
    calc
      a • x + b • y <= a • x + b • x := by gcongr
      _ = x := Convex.combo_self hab _

/--
theorem `starConvex_iff_ordConnected` / 定理 `starConvex_iff_ordConnected`

English:
theorem starConvex_iff_ordConnected
  statement: [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  proof: by
  simp_rw [ordConnected_iff_uIcc_subset_left hx, starConvex_iff_segment_subset, segment_eq_uIcc]

alias ⟨StarConvex.ordConnected, _⟩ := starConvex_iff_ordConnected

中文:
定理 starConvex_iff_ordConnected
  结论: [域 𝕜] [线性序 𝕜] [是StrictOrdered环 𝕜]
  证明: by
  simp_rw [ordConnected_iff_uIcc_subset_left hx, starConvex_iff_segment_subset, segment_eq_uIcc]

alias ⟨StarConvex.ordConnected, _⟩ := starConvex_iff_ordConnected

Depends on / 依赖: ordConnected_iff_uIcc_subset_left, segment_eq_uIcc, simp_rw, starConvex_iff_segment_subset
-/
theorem starConvex_iff_ordConnected [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {x : 𝕜} {s : Set 𝕜} (hx : x in s) :
    StarConvex 𝕜 x s ↔ s.OrdConnected := by
  simp_rw [ordConnected_iff_uIcc_subset_left hx, starConvex_iff_segment_subset, segment_eq_uIcc]

alias ⟨StarConvex.ordConnected, _⟩ := starConvex_iff_ordConnected

end OrdConnected
