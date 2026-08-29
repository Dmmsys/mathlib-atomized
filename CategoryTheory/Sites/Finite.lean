/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.CategoryTheory.Sites.Pretopology
public import Mathlib.Data.Set.Finite.Lattice

/-! # The Finite Pretopology

In this file we define the finite pretopology on a category, which consists of presieves that
contain only finitely many arrows.

## Main Definitions

- `CategoryTheory.Precoverage.finite`: The finite precoverage on a category.
- `CategoryTheory.Pretopology.finite`: The finite pretopology on a category.
-/

@[expose] public section

universe v v₁ u u₁

namespace CategoryTheory

open Presieve

namespace Precoverage

/--
Definition of `finite` / `finite` 的定义

English:
definition finite
  signature: (C : Type u) [Category.{v} C]
  body: { s : Presieve X | s.uncurry.Finite }

中文:
定义 finite
  签名: (C : 类型u) [Category.{v} C]
  定义体: { s : Presieve X | s.uncurry.Finite }

Depends on / 依赖: Finite, Presieve, s.uncurry.Finite, uncurry
-/
def finite (C : Type u) [Category.{v} C] : Precoverage C where
  coverings X := { s : Presieve X | s.uncurry.Finite }

variable {C : Type u} [Category.{v} C]

/--
lemma `mem_finite_iff` / 引理 `mem_finite_iff`

English:
lemma mem_finite_iff
  given: {X : C} {s : Presieve X}
  proof: Iff.rfl

中文:
引理 mem_finite_iff
  条件: {X : C} {s : Presieve X}
  证明: Iff.rfl
-/
@[simp] lemma mem_finite_iff {X : C} {s : Presieve X} :
    s in finite C X ↔ s.uncurry.Finite := Iff.rfl

/--
theorem `ofArrows_mem_finite` / 定理 `ofArrows_mem_finite`

English:
theorem ofArrows_mem_finite
  given: {X : C} {ι : Type*} [Finite ι] (Y : ι -> C) (f : (i : ι) -> Y i ⟶ X)
  proof: by
  simpa using Set.finite_range _

中文:
定理 ofArrows_mem_finite
  条件: {X : C} {ι : 类型} [Finite ι] (Y : ι -> C) (f : (i : ι) -> Y i ⟶ X)
  证明: by
  simpa using Set.finite_range _

Depends on / 依赖: Set.finite_range, finite_range
-/
theorem ofArrows_mem_finite {X : C} {ι : Type*} [Finite ι] (Y : ι -> C) (f : (i : ι) -> Y i ⟶ X) :
    ofArrows Y f in finite C X := by
  simpa using Set.finite_range _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (finite C).HasIsos
  body: by simp

中文:
实例 :
  签名: (finite C).HasIsos
  定义体: by simp
-/
instance : (finite C).HasIsos where
  mem_coverings_of_isIso := by simp

end Precoverage

namespace Pretopology

open Limits

/-- The finite pretopology on a category consists of finite presieves, i.e. a presieve with finitely
many maps after uncurrying. -/
@[simps toPrecoverage]
/--
Definition of `finite` / `finite` 的定义

English:
definition finite
  signature: (C : Type u) [Category.{v} C] [HasPullbacks C]
  body: Precoverage.finite C
  has_isos _ _ _ := Precoverage.mem_coverings_of_isIso _
  pullbacks X Y u s hs := by simpa using hs.image _
  transitive X s t hs ht := by simpa using hs.biUnion' fun _ _ => (ht _ _).image _

中文:
定义 finite
  签名: (C : 类型u) [Category.{v} C] [HasPullbacks C]
  定义体: Precoverage.finite C
  has_isos _ _ _ := Precoverage.mem_coverings_of_isIso _
  pullbacks X Y u s hs := by simpa using hs.image _
  transitive X s t hs ht := by simpa using hs.biUnion' fun _ _ => (ht _ _).image _

Depends on / 依赖: Precoverage, Precoverage.finite, finite
-/
def finite (C : Type u) [Category.{v} C] [HasPullbacks C] : Pretopology C where
  __ := Precoverage.finite C
  has_isos _ _ _ := Precoverage.mem_coverings_of_isIso _
  pullbacks X Y u s hs := by simpa using hs.image _
  transitive X s t hs ht := by simpa using hs.biUnion' fun _ _ => (ht _ _).image _

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/--
theorem `ofArrows_mem_finite` / 定理 `ofArrows_mem_finite`

English:
theorem ofArrows_mem_finite
  given: {X : C} {ι : Type*} [Finite ι] (Y : ι -> C) (f : (i : ι) -> Y i ⟶ X)
  proof: Precoverage.ofArrows_mem_finite _ _

中文:
定理 ofArrows_mem_finite
  条件: {X : C} {ι : 类型} [Finite ι] (Y : ι -> C) (f : (i : ι) -> Y i ⟶ X)
  证明: Precoverage.ofArrows_mem_finite _ _

Depends on / 依赖: Precoverage, Precoverage.ofArrows_mem_finite, ofArrows_mem_finite
-/
theorem ofArrows_mem_finite {X : C} {ι : Type*} [Finite ι] (Y : ι -> C) (f : (i : ι) -> Y i ⟶ X) :
    ofArrows Y f in (finite C).coverings X :=
  Precoverage.ofArrows_mem_finite _ _

end Pretopology

end CategoryTheory
