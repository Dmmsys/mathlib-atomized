/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.Set

/-!
# Star-convex sets

This file defines star-convex sets in a convex space.

A set is star-convex at `x` if every segment from `x` to a point in the set is contained in the set.

This is the prototypical example of a contractible set in homotopy theory (by scaling every point
towards `x`), but has wider uses.

Note that this has nothing to do with star rings, `Star` and co.

## Implementation notes

Instead of saying that a set is star-convex, we say a set is star-convex *at a point*. This has the
advantage of allowing us to talk about convexity as being "everywhere star-convexity" and of making
the union of star-convex sets be star-convex.

Incidentally, this choice means we don't need to assume a set is nonempty for it to be star-convex.
Concretely, the empty set is star-convex at every point.
-/

open Finsupp Set

public section

namespace Convexity
variable {R X Y : Type*} {ι : Sort*} {κ : ι -> Sort*}

section Semiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X] [ConvexSpace R Y]
  {f : X -> Y} {w : StdSimplex R X} {x : X} {s t : Set X} {y : X}

variable (R x s) in
/-- A set `s` is star-convex at a point `x` if every segment from `x` to a point in `s` is
contained in `s`.

TODO: Replace `StarConvex` with this predicate. -/
@[expose]
/--
Definition of `IsStarConvexSet` / `IsStarConvexSet` 的定义

English:
definition IsStarConvexSet
  signature: : Prop
  body: forall ⦃y⦄, y in s -> forall ⦃a b : R⦄ ha hb hab, convexCombPair a b ha hb hab x y in s

中文:
定义 IsStarConvexSet
  签名: : 命题
  定义体: forall ⦃y⦄, y in s -> forall ⦃a b : R⦄ ha hb hab, convexCombPair a b ha hb hab x y in s

Depends on / 依赖: convexCombPair
-/
def IsStarConvexSet : Prop :=
  forall ⦃y⦄, y in s -> forall ⦃a b : R⦄ ha hb hab, convexCombPair a b ha hb hab x y in s

/--
lemma `IsStarConvexSet.empty` / 引理 `IsStarConvexSet.empty`

English:
lemma IsStarConvexSet.empty
  statement: IsStarConvexSet R x ∅
  proof: by simp [IsStarConvexSet]

@[simp]

中文:
引理 IsStarConvexSet.empty
  结论: IsStarConvexSet R x ∅
  证明: by simp [IsStarConvexSet]

@[simp]
-/
@[simp] protected lemma IsStarConvexSet.empty : IsStarConvexSet R x ∅ := by simp [IsStarConvexSet]

@[simp]
/--
lemma `IsStarConvexSet.univ` / 引理 `IsStarConvexSet.univ`

English:
lemma IsStarConvexSet.univ
  statement: IsStarConvexSet R x .univ
  proof: by simp [IsStarConvexSet]

中文:
引理 IsStarConvexSet.univ
  结论: IsStarConvexSet R x .univ
  证明: by simp [IsStarConvexSet]
-/
protected lemma IsStarConvexSet.univ : IsStarConvexSet R x .univ := by simp [IsStarConvexSet]

/--
lemma `IsStarConvexSet.singleton` / 引理 `IsStarConvexSet.singleton`

English:
lemma IsStarConvexSet.singleton
  statement: IsStarConvexSet R x {x}
  proof: by
  simp [IsStarConvexSet]

@[grind ←]

中文:
引理 IsStarConvexSet.singleton
  结论: IsStarConvexSet R x {x}
  证明: by
  simp [IsStarConvexSet]

@[grind ←]
-/
@[simp] protected lemma IsStarConvexSet.singleton : IsStarConvexSet R x {x} := by
  simp [IsStarConvexSet]

@[grind ←]
/--
lemma `IsStarConvexSet.inter` / 引理 `IsStarConvexSet.inter`

English:
lemma IsStarConvexSet.inter
  given: (hs : IsStarConvexSet R x s) (ht : IsStarConvexSet R x t)
  proof: by simp +contextual [IsStarConvexSet, hs _, ht _]

@[grind ←]

中文:
引理 IsStarConvexSet.inter
  条件: (hs : IsStarConvexSet R x s) (ht : IsStarConvexSet R x t)
  证明: by simp +contextual [IsStarConvexSet, hs _, ht _]

@[grind ←]
-/
protected lemma IsStarConvexSet.inter (hs : IsStarConvexSet R x s) (ht : IsStarConvexSet R x t) :
    IsStarConvexSet R x (s inter t) := by simp +contextual [IsStarConvexSet, hs _, ht _]

@[grind ←]
/--
lemma `IsStarConvexSet.union` / 引理 `IsStarConvexSet.union`

English:
lemma IsStarConvexSet.union
  given: (hs : IsStarConvexSet R x s) (ht : IsStarConvexSet R x t)
  proof: by simp +contextual [IsStarConvexSet, hs _, ht _, or_imp]

@[grind ←]

中文:
引理 IsStarConvexSet.union
  条件: (hs : IsStarConvexSet R x s) (ht : IsStarConvexSet R x t)
  证明: by simp +contextual [IsStarConvexSet, hs _, ht _, or_imp]

@[grind ←]
-/
protected lemma IsStarConvexSet.union (hs : IsStarConvexSet R x s) (ht : IsStarConvexSet R x t) :
    IsStarConvexSet R x (s union t) := by simp +contextual [IsStarConvexSet, hs _, ht _, or_imp]

@[grind ←]
/--
lemma `IsStarConvexSet.sInter` / 引理 `IsStarConvexSet.sInter`

English:
lemma IsStarConvexSet.sInter
  given: {S : Set (Set X)} (hS : forall s in S, IsStarConvexSet R x s)
  proof: by simp +contextual [IsStarConvexSet, hS _ _ _]

@[grind ←]

中文:
引理 IsStarConvexSet.sInter
  条件: {S : Set (Set X)} (hS : 对任意 s in S, IsStarConvexSet R x s)
  证明: by simp +contextual [IsStarConvexSet, hS _ _ _]

@[grind ←]
-/
protected lemma IsStarConvexSet.sInter {S : Set (Set X)} (hS : forall s in S, IsStarConvexSet R x s) :
    IsStarConvexSet R x (⋂₀ S) := by simp +contextual [IsStarConvexSet, hS _ _ _]

@[grind ←]
/--
lemma `IsStarConvexSet.iInter` / 引理 `IsStarConvexSet.iInter`

English:
lemma IsStarConvexSet.iInter
  given: {s : ι -> Set X} (hs : forall i, IsStarConvexSet R x (s i))
  proof: by simp +contextual [IsStarConvexSet, hs _ _]

中文:
引理 IsStarConvexSet.iInter
  条件: {s : ι -> Set X} (hs : 对任意 i, IsStarConvexSet R x (s i))
  证明: by simp +contextual [IsStarConvexSet, hs _ _]
-/
protected lemma IsStarConvexSet.iInter {s : ι -> Set X} (hs : forall i, IsStarConvexSet R x (s i)) :
    IsStarConvexSet R x (⋂ i, s i) := by simp +contextual [IsStarConvexSet, hs _ _]

/--
lemma `IsStarConvexSet.iInter₂` / 引理 `IsStarConvexSet.iInter₂`

English:
lemma IsStarConvexSet.iInter₂
  given: {s : forall i, κ i -> Set X} (h : forall i j, IsStarConvexSet R x (s i j))
  proof: .iInter fun i => .iInter h i

@[grind ←]

中文:
引理 IsStarConvexSet.iInter₂
  条件: {s : 对任意 i, κ i -> Set X} (h : 对任意 i j, IsStarConvexSet R x (s i j))
  证明: .iInter fun i => .iInter h i

@[grind ←]

Depends on / 依赖: iInter
-/
lemma IsStarConvexSet.iInter₂ {s : forall i, κ i -> Set X} (h : forall i j, IsStarConvexSet R x (s i j)) :
IsStarConvexSet R x (⋂ i, ⋂ j, s i j) := .iInter fun i => .iInter h i

@[grind ←]
/--
lemma `IsStarConvexSet.sUnion` / 引理 `IsStarConvexSet.sUnion`

English:
lemma IsStarConvexSet.sUnion
  given: {S : Set (Set X)} (hS : forall s in S, IsStarConvexSet R x s)
  proof: by
  rintro y ⟨s, hs, hy⟩ a ha b hb hab; exact ⟨s, hs, hS _ hs hy _ ..⟩

@[grind ←]

中文:
引理 IsStarConvexSet.sUnion
  条件: {S : Set (Set X)} (hS : 对任意 s in S, IsStarConvexSet R x s)
  证明: by
  rintro y ⟨s, hs, hy⟩ a ha b hb hab; exact ⟨s, hs, hS _ hs hy _ ..⟩

@[grind ←]
-/
protected lemma IsStarConvexSet.sUnion {S : Set (Set X)} (hS : forall s in S, IsStarConvexSet R x s) :
    IsStarConvexSet R x (⋃₀ S) := by
  rintro y ⟨s, hs, hy⟩ a ha b hb hab; exact ⟨s, hs, hS _ hs hy _ ..⟩

@[grind ←]
/--
lemma `IsStarConvexSet.iUnion` / 引理 `IsStarConvexSet.iUnion`

English:
lemma IsStarConvexSet.iUnion
  given: {s : ι -> Set X} (hs : forall i, IsStarConvexSet R x (s i))
  proof: .sUnion by simpa

中文:
引理 IsStarConvexSet.iUnion
  条件: {s : ι -> Set X} (hs : 对任意 i, IsStarConvexSet R x (s i))
  证明: .sUnion by simpa
-/
protected lemma IsStarConvexSet.iUnion {s : ι -> Set X} (hs : forall i, IsStarConvexSet R x (s i)) :
IsStarConvexSet R x (⋃ i, s i) := .sUnion by simpa

/--
lemma `IsStarConvexSet.iUnion₂` / 引理 `IsStarConvexSet.iUnion₂`

English:
lemma IsStarConvexSet.iUnion₂
  statement: {s : forall i, κ i -> Set X}
  proof: .iUnion fun i => .iUnion h i

中文:
引理 IsStarConvexSet.iUnion₂
  结论: {s : 对任意 i, κ i -> Set X}
  证明: .iUnion fun i => .iUnion h i
-/
protected lemma IsStarConvexSet.iUnion₂ {s : forall i, κ i -> Set X}
    (h : forall i j, IsStarConvexSet R x (s i j)) : IsStarConvexSet R x (⋃ i, ⋃ j, s i j) :=
.iUnion fun i => .iUnion h i

/--
lemma `IsConvexSet.isStarConvexSet` / 引理 `IsConvexSet.isStarConvexSet`

English:
lemma IsConvexSet.isStarConvexSet
  given: (hs : IsConvexSet R s) (hx : x in s)
  statement: IsStarConvexSet R x s
  proof: fun _y hy _a _b _ha _hb _hab => hs.convexCombPair_mem hx hy ..

中文:
引理 IsConvexSet.isStarConvexSet
  条件: (hs : IsConvexSet R s) (hx : x in s)
  结论: IsStarConvexSet R x s
  证明: fun _y hy _a _b _ha _hb _hab => hs.convexCombPair_mem hx hy ..

Depends on / 依赖: _hab, convexCombPair_mem, hs.convexCombPair_mem
-/
lemma IsConvexSet.isStarConvexSet (hs : IsConvexSet R s) (hx : x in s) : IsStarConvexSet R x s :=
  fun _y hy _a _b _ha _hb _hab => hs.convexCombPair_mem hx hy ..

/--
lemma `IsStarConvexSet.mem` / 引理 `IsStarConvexSet.mem`

English:
lemma IsStarConvexSet.mem
  given: (hs : IsStarConvexSet R x s) (hs₀ : s.Nonempty)
  statement: x in s
  proof: by
  obtain ⟨y, hy⟩ := hs₀; simpa using hs hy zero_le_one le_rfl (add_zero _)

@[grind ←]

中文:
引理 IsStarConvexSet.mem
  条件: (hs : IsStarConvexSet R x s) (hs₀ : s.Nonempty)
  结论: x in s
  证明: by
  obtain ⟨y, hy⟩ := hs₀; simpa using hs hy zero_le_one le_rfl (add_zero _)

@[grind ←]

Depends on / 依赖: add_zero, le_rfl, zero_le_one
-/
lemma IsStarConvexSet.mem (hs : IsStarConvexSet R x s) (hs₀ : s.Nonempty) : x in s := by
  obtain ⟨y, hy⟩ := hs₀; simpa using hs hy zero_le_one le_rfl (add_zero _)

@[grind ←]
/--
lemma `IsStarConvexSet.preimage` / 引理 `IsStarConvexSet.preimage`

English:
lemma IsStarConvexSet.preimage
  statement: {s : Set Y} (hf : IsAffineMap R f)
  proof: fun y hy a b ha hb hab => by simpa [mem_preimage, hf.map_convexCombPair] using hs hy _ ..

@[grind <=]

中文:
引理 IsStarConvexSet.preimage
  结论: {s : Set Y} (hf : IsAffineMap R f)
  证明: fun y hy a b ha hb hab => by simpa [mem_preimage, hf.map_convexCombPair] using hs hy _ ..

@[grind <=]
-/
protected lemma IsStarConvexSet.preimage {s : Set Y} (hf : IsAffineMap R f)
    (hs : IsStarConvexSet R (f x) s) : IsStarConvexSet R x (f ⁻¹' s) :=
  fun y hy a b ha hb hab => by simpa [mem_preimage, hf.map_convexCombPair] using hs hy _ ..

@[grind <=]
/--
lemma `IsStarConvexSet.image` / 引理 `IsStarConvexSet.image`

English:
lemma IsStarConvexSet.image
  given: (hf : IsAffineMap R f) (hs : IsStarConvexSet R x s)
  proof: by
  rintro _ ⟨y, hy, rfl⟩ a b ha hb hab; exact ⟨_, hs hy _ .., hf.map_convexCombPair ..⟩

@[grind ←]

中文:
引理 IsStarConvexSet.image
  条件: (hf : IsAffineMap R f) (hs : IsStarConvexSet R x s)
  证明: by
  rintro _ ⟨y, hy, rfl⟩ a b ha hb hab; exact ⟨_, hs hy _ .., hf.map_convexCombPair ..⟩

@[grind ←]
-/
protected lemma IsStarConvexSet.image (hf : IsAffineMap R f) (hs : IsStarConvexSet R x s) :
    IsStarConvexSet R (f x) (f '' s) := by
  rintro _ ⟨y, hy, rfl⟩ a b ha hb hab; exact ⟨_, hs hy _ .., hf.map_convexCombPair ..⟩

@[grind ←]
/--
lemma `IsStarConvexSet.prod` / 引理 `IsStarConvexSet.prod`

English:
lemma IsStarConvexSet.prod
  statement: {t : Set Y} {y : Y} (hs : IsStarConvexSet R x s)
  proof: by
  rintro ⟨w, z⟩ ⟨hw, hz⟩ a b ha hb hab; exact ⟨by simpa using hs hw _ .., by simpa using ht hz _ ..⟩

@[grind ←]

中文:
引理 IsStarConvexSet.prod
  结论: {t : Set Y} {y : Y} (hs : IsStarConvexSet R x s)
  证明: by
  rintro ⟨w, z⟩ ⟨hw, hz⟩ a b ha hb hab; exact ⟨by simpa using hs hw _ .., by simpa using ht hz _ ..⟩

@[grind ←]
-/
protected lemma IsStarConvexSet.prod {t : Set Y} {y : Y} (hs : IsStarConvexSet R x s)
    (ht : IsStarConvexSet R y t) : IsStarConvexSet R (x, y) (s ×ˢ t) := by
  rintro ⟨w, z⟩ ⟨hw, hz⟩ a b ha hb hab; exact ⟨by simpa using hs hw _ .., by simpa using ht hz _ ..⟩

@[grind ←]
/--
lemma `IsStarConvexSet.pi` / 引理 `IsStarConvexSet.pi`

English:
lemma IsStarConvexSet.pi
  statement: {ι : Type*} {X : ι -> Type*} [forall i, ConvexSpace R (X i)]
  proof: fun y hy a b ha hb hab i hi => by simpa using ht _ hi (hy _ hi) _ ..

中文:
引理 IsStarConvexSet.pi
  结论: {ι : 类型} {X : ι -> 类型} [对任意 i, ConvexSpace R (X i)]
  证明: fun y hy a b ha hb hab i hi => by simpa using ht _ hi (hy _ hi) _ ..
-/
protected lemma IsStarConvexSet.pi {ι : Type*} {X : ι -> Type*} [forall i, ConvexSpace R (X i)]
    {s : Set ι} {x : forall i, X i} {t : forall i, Set (X i)} (ht : forall i in s, IsStarConvexSet R (x i) (t i)) :
    IsStarConvexSet R x (s.pi t) :=
  fun y hy a b ha hb hab i hi => by simpa using ht _ hi (hy _ hi) _ ..

end Semiring
end Convexity
