/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Order.Group.Nat

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.LinearAlgebra.Dimension.Basic

/-!
# Linear and semilinear sets

This file defines linear and semilinear sets. In an `AddCommMonoid`, a linear set is a coset of a
finitely generated additive submonoid, and a semilinear set is a finite union of linear sets.

We prove that semilinear sets are closed under union, projection, set addition and additive closure.
We also prove that any semilinear set can be decomposed into a finite union of proper linear sets,
which are linear sets with linearly independent submonoid generators (periods).

## Main Definitions

- `IsLinearSet`: a set is linear if it is a coset of a finitely generated additive submonoid.
- `IsSemilinearSet`: a set is semilinear if it is a finite union of linear sets.
- `IsProperLinearSet`: a linear set is proper if its submonoid generators (periods) are linearly
  independent.
- `IsProperSemilinearSet`: a semilinear set is proper if it is a finite union of proper linear sets.

## Main Results

- `IsSemilinearSet` is closed under union, projection, set addition and additive closure.
- `IsSemilinearSet.isProperSemilinearSet`: every semilinear set is a finite union of proper linear
  sets.
- `Nat.isSemilinearSet_iff_ultimately_periodic`: A set of `ℕ` is semilinear if and only if it is
  ultimately periodic, i.e. periodic after some number `k`.

## Naming convention

`IsSemilinearSet.proj` projects a semilinear set of `ι ⊕ κ → M` to `ι → M` by taking `Sum.inl` on
the index. It is a special case of `IsSemilinearSet.image`, and is useful in proving semilinearity
of sets in form `{ x | ∃ y, p x y }`.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

@[expose] public section

variable {M N ι κ F : Type*} [AddCommMonoid M] [AddCommMonoid N]
  [FunLike F M N] [AddMonoidHomClass F M N] {a : M} {s s₁ s₂ : Set M}

open Set Pointwise AddSubmonoid

/--
Definition of `IsLinearSet` / `IsLinearSet` 的定义

English:
definition IsLinearSet
  signature: (s : Set M)
  body: exists (a : M) (t : Set M), t.Finite ∧ s = a +ᵥ (closure t : Set M)

中文:
定义 IsLinearSet
  签名: (s : 集合 M)
  定义体: exists (a : M) (t : Set M), t.Finite ∧ s = a +ᵥ (closure t : Set M)

Depends on / 依赖: Finite, closure, t.Finite
-/
def IsLinearSet (s : Set M) : Prop :=
  exists (a : M) (t : Set M), t.Finite ∧ s = a +ᵥ (closure t : Set M)

/--
theorem `isLinearSet_iff` / 定理 `isLinearSet_iff`

English:
theorem isLinearSet_iff
  proof: by
  simp [IsLinearSet, Finset.exists]

@[simp]

中文:
定理 isLinearSet_iff
  证明: by
  simp [IsLinearSet, Finset.exists]

@[simp]

Depends on / 依赖: Finset, Finset.exists, IsLinearSet
-/
theorem isLinearSet_iff :
    IsLinearSet s ↔ exists (a : M) (t : Finset M), s = a +ᵥ (closure (t : Set M) : Set M) := by
  simp [IsLinearSet, Finset.exists]

@[simp]
/--
theorem `IsLinearSet.singleton` / 定理 `IsLinearSet.singleton`

English:
theorem IsLinearSet.singleton
  given: (a : M)
  statement: IsLinearSet {a}
  proof: ⟨a, ∅, by simp⟩

中文:
定理 IsLinearSet.singleton
  条件: (a : M)
  结论: IsLinearSet {a}
  证明: ⟨a, ∅, by simp⟩
-/
theorem IsLinearSet.singleton (a : M) : IsLinearSet {a} :=
  ⟨a, ∅, by simp⟩

/--
theorem `IsLinearSet.closure_finset` / 定理 `IsLinearSet.closure_finset`

English:
theorem IsLinearSet.closure_finset
  given: (s : Finset M)
  statement: IsLinearSet (closure (s : Set M) : Set M)
  proof: ⟨0, s, by simp⟩

中文:
定理 IsLinearSet.closure_finset
  条件: (s : 有限集 M)
  结论: IsLinearSet (closure (s : 集合 M) : 集合 M)
  证明: ⟨0, s, by simp⟩
-/
theorem IsLinearSet.closure_finset (s : Finset M) : IsLinearSet (closure (s : Set M) : Set M) :=
  ⟨0, s, by simp⟩

/--
theorem `IsLinearSet.closure_of_finite` / 定理 `IsLinearSet.closure_of_finite`

English:
theorem IsLinearSet.closure_of_finite
  given: (hs : s.Finite)
  proof: ⟨0, s, hs, by simp⟩

中文:
定理 IsLinearSet.closure_of_finite
  条件: (hs : s.有限)
  证明: ⟨0, s, hs, by simp⟩
-/
theorem IsLinearSet.closure_of_finite (hs : s.Finite) :
    IsLinearSet (closure s : Set M) :=
  ⟨0, s, hs, by simp⟩

/--
theorem `isLinearSet_iff_exists_fg_eq_vadd` / 定理 `isLinearSet_iff_exists_fg_eq_vadd`

English:
theorem isLinearSet_iff_exists_fg_eq_vadd
  proof: isLinearSet_iff.trans (exists_congr fun a =>
    ⟨fun ⟨t, hs⟩ => ⟨_, ⟨t, rfl⟩, hs⟩, fun ⟨P, ⟨t, hP⟩, hs⟩ => ⟨t, by rwa [hP]⟩⟩)

中文:
定理 isLinearSet_iff_存在_fg_eq_vadd
  证明: isLinearSet_iff.trans (exists_congr fun a =>
    ⟨fun ⟨t, hs⟩ => ⟨_, ⟨t, rfl⟩, hs⟩, fun ⟨P, ⟨t, hP⟩, hs⟩ => ⟨t, by rwa [hP]⟩⟩)

Depends on / 依赖: exists_congr, isLinearSet_iff, isLinearSet_iff.trans
-/
theorem isLinearSet_iff_exists_fg_eq_vadd :
    IsLinearSet s ↔ exists (a : M) (P : AddSubmonoid M), P.FG ∧ s = a +ᵥ (P : Set M) :=
  isLinearSet_iff.trans (exists_congr fun a =>
    ⟨fun ⟨t, hs⟩ => ⟨_, ⟨t, rfl⟩, hs⟩, fun ⟨P, ⟨t, hP⟩, hs⟩ => ⟨t, by rwa [hP]⟩⟩)

/--
theorem `IsLinearSet.of_fg` / 定理 `IsLinearSet.of_fg`

English:
theorem IsLinearSet.of_fg
  given: {P : AddSubmonoid M} (hP : P.FG)
  statement: IsLinearSet (P : Set M)
  proof: by
  rw [isLinearSet_iff_exists_fg_eq_vadd]
  exact ⟨0, P, hP, by simp⟩

@[simp]

中文:
定理 IsLinearSet.of_fg
  条件: {P : 加法子幺半群 M} (hP : P.FG)
  结论: IsLinearSet (P : 集合 M)
  证明: by
  rw [isLinearSet_iff_exists_fg_eq_vadd]
  exact ⟨0, P, hP, by simp⟩

@[simp]

Depends on / 依赖: isLinearSet_iff_exists_fg_eq_vadd
-/
theorem IsLinearSet.of_fg {P : AddSubmonoid M} (hP : P.FG) : IsLinearSet (P : Set M) := by
  rw [isLinearSet_iff_exists_fg_eq_vadd]
  exact ⟨0, P, hP, by simp⟩

@[simp]
/--
theorem `IsLinearSet.univ` / 定理 `IsLinearSet.univ`

English:
theorem IsLinearSet.univ
  given: [AddMonoid.FG M]
  statement: IsLinearSet (univ : Set M)
  proof: of_fg AddMonoid.FG.fg_top

中文:
定理 IsLinearSet.univ
  条件: [加法幺半群.FG M]
  结论: IsLinearSet (univ : 集合 M)
  证明: of_fg AddMonoid.FG.fg_top
-/
protected theorem IsLinearSet.univ [AddMonoid.FG M] : IsLinearSet (univ : Set M) :=
  of_fg AddMonoid.FG.fg_top

/--
theorem `IsLinearSet.vadd` / 定理 `IsLinearSet.vadd`

English:
theorem IsLinearSet.vadd
  given: (a : M) (hs : IsLinearSet s)
  statement: IsLinearSet (a +ᵥ s)
  proof: by
  rcases hs with ⟨b, t, ht, rfl⟩
  exact ⟨a + b, t, ht, by rw [vadd_vadd]⟩

中文:
定理 IsLinearSet.vadd
  条件: (a : M) (hs : IsLinearSet s)
  结论: IsLinearSet (a +ᵥ s)
  证明: by
  rcases hs with ⟨b, t, ht, rfl⟩
  exact ⟨a + b, t, ht, by rw [vadd_vadd]⟩

Depends on / 依赖: vadd_vadd
-/
theorem IsLinearSet.vadd (a : M) (hs : IsLinearSet s) : IsLinearSet (a +ᵥ s) := by
  rcases hs with ⟨b, t, ht, rfl⟩
  exact ⟨a + b, t, ht, by rw [vadd_vadd]⟩

/--
theorem `IsLinearSet.add` / 定理 `IsLinearSet.add`

English:
theorem IsLinearSet.add
  given: (hs₁ : IsLinearSet s₁) (hs₂ : IsLinearSet s₂)
  statement: IsLinearSet (s₁ + s₂)
  proof: by
  rcases hs₁ with ⟨a, t₁, ht₁, rfl⟩
  rcases hs₂ with ⟨b, t₂, ht₂, rfl⟩
  exact ⟨a + b, t₁ union t₂, ht₁.union ht₂, by simp [vadd_add_vadd, closure_union, coe_sup]⟩

中文:
定理 IsLinearSet.add
  条件: (hs₁ : IsLinearSet s₁) (hs₂ : IsLinearSet s₂)
  结论: IsLinearSet (s₁ + s₂)
  证明: by
  rcases hs₁ with ⟨a, t₁, ht₁, rfl⟩
  rcases hs₂ with ⟨b, t₂, ht₂, rfl⟩
  exact ⟨a + b, t₁ union t₂, ht₁.union ht₂, by simp [vadd_add_vadd, closure_union, coe_sup]⟩

Depends on / 依赖: closure_union, coe_sup, vadd_add_vadd
-/
theorem IsLinearSet.add (hs₁ : IsLinearSet s₁) (hs₂ : IsLinearSet s₂) : IsLinearSet (s₁ + s₂) := by
  rcases hs₁ with ⟨a, t₁, ht₁, rfl⟩
  rcases hs₂ with ⟨b, t₂, ht₂, rfl⟩
  exact ⟨a + b, t₁ union t₂, ht₁.union ht₂, by simp [vadd_add_vadd, closure_union, coe_sup]⟩

/--
theorem `IsLinearSet.image` / 定理 `IsLinearSet.image`

English:
theorem IsLinearSet.image
  given: (hs : IsLinearSet s) (f : F)
  statement: IsLinearSet (f '' s)
  proof: by
  rcases hs with ⟨a, t, ht, rfl⟩
  refine ⟨f a, f '' t, ht.image f, ?_⟩
  simp [image_vadd_distrib, ← AddMonoidHom.map_mclosure]

中文:
定理 IsLinearSet.像
  条件: (hs : IsLinearSet s) (f : F)
  结论: IsLinearSet (f '' s)
  证明: by
  rcases hs with ⟨a, t, ht, rfl⟩
  refine ⟨f a, f '' t, ht.image f, ?_⟩
  simp [image_vadd_distrib, ← AddMonoidHom.map_mclosure]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.map_mclosure, ht.image, image_vadd_distrib, map_mclosure
-/
theorem IsLinearSet.image (hs : IsLinearSet s) (f : F) : IsLinearSet (f '' s) := by
  rcases hs with ⟨a, t, ht, rfl⟩
  refine ⟨f a, f '' t, ht.image f, ?_⟩
  simp [image_vadd_distrib, ← AddMonoidHom.map_mclosure]

/--
Definition of `IsSemilinearSet` / `IsSemilinearSet` 的定义

English:
definition IsSemilinearSet
  signature: (s : Set M)
  body: exists (S : Set (Set M)), S.Finite ∧ (forall t in S, IsLinearSet t) ∧ s = ⋃₀ S

中文:
定义 IsSemilinearSet
  签名: (s : 集合 M)
  定义体: exists (S : Set (Set M)), S.Finite ∧ (forall t in S, IsLinearSet t) ∧ s = ⋃₀ S

Depends on / 依赖: Finite, IsLinearSet, S.Finite
-/
def IsSemilinearSet (s : Set M) : Prop :=
  exists (S : Set (Set M)), S.Finite ∧ (forall t in S, IsLinearSet t) ∧ s = ⋃₀ S

/--
theorem `isSemilinearSet_iff` / 定理 `isSemilinearSet_iff`

English:
theorem isSemilinearSet_iff
  proof: Set.exists_finite_iff_finset

中文:
定理 isSemilinearSet_iff
  证明: Set.exists_finite_iff_finset

Depends on / 依赖: Set.exists_finite_iff_finset, exists_finite_iff_finset
-/
theorem isSemilinearSet_iff :
    IsSemilinearSet s ↔ exists (S : Finset (Set M)), (forall t in S, IsLinearSet t) ∧ s = ⋃₀ S :=
  Set.exists_finite_iff_finset

/--
theorem `IsLinearSet.isSemilinearSet` / 定理 `IsLinearSet.isSemilinearSet`

English:
theorem IsLinearSet.isSemilinearSet
  given: (h : IsLinearSet s)
  statement: IsSemilinearSet s
  proof: ⟨{s}, by simpa⟩

@[simp]

中文:
定理 IsLinearSet.isSemilinearSet
  条件: (h : IsLinearSet s)
  结论: IsSemilinearSet s
  证明: ⟨{s}, by simpa⟩

@[simp]
-/
theorem IsLinearSet.isSemilinearSet (h : IsLinearSet s) : IsSemilinearSet s :=
  ⟨{s}, by simpa⟩

@[simp]
/--
theorem `IsSemilinearSet.empty` / 定理 `IsSemilinearSet.empty`

English:
theorem IsSemilinearSet.empty
  statement: IsSemilinearSet (∅ : Set M)
  proof: ⟨∅, by simp⟩

@[simp]

中文:
定理 IsSemilinearSet.empty
  结论: IsSemilinearSet (∅ : 集合 M)
  证明: ⟨∅, by simp⟩

@[simp]
-/
theorem IsSemilinearSet.empty : IsSemilinearSet (∅ : Set M) :=
  ⟨∅, by simp⟩

@[simp]
/--
theorem `IsSemilinearSet.singleton` / 定理 `IsSemilinearSet.singleton`

English:
theorem IsSemilinearSet.singleton
  given: (a : M)
  statement: IsSemilinearSet {a}
  proof: (IsLinearSet.singleton a).isSemilinearSet

中文:
定理 IsSemilinearSet.singleton
  条件: (a : M)
  结论: IsSemilinearSet {a}
  证明: (IsLinearSet.singleton a).isSemilinearSet

Depends on / 依赖: IsLinearSet, IsLinearSet.singleton, isSemilinearSet, singleton
-/
theorem IsSemilinearSet.singleton (a : M) : IsSemilinearSet {a} :=
  (IsLinearSet.singleton a).isSemilinearSet

/--
theorem `IsSemilinearSet.closure_finset` / 定理 `IsSemilinearSet.closure_finset`

English:
theorem IsSemilinearSet.closure_finset
  given: (s : Finset M)
  proof: (IsLinearSet.closure_finset s).isSemilinearSet

中文:
定理 IsSemilinearSet.closure_finset
  条件: (s : 有限集 M)
  证明: (IsLinearSet.closure_finset s).isSemilinearSet

Depends on / 依赖: IsLinearSet, IsLinearSet.closure_finset, closure_finset, isSemilinearSet
-/
theorem IsSemilinearSet.closure_finset (s : Finset M) :
    IsSemilinearSet (closure (s : Set M) : Set M) :=
  (IsLinearSet.closure_finset s).isSemilinearSet

/--
theorem `IsSemilinearSet.closure_of_finite` / 定理 `IsSemilinearSet.closure_of_finite`

English:
theorem IsSemilinearSet.closure_of_finite
  given: (hs : s.Finite)
  proof: (IsLinearSet.closure_of_finite hs).isSemilinearSet

中文:
定理 IsSemilinearSet.closure_of_finite
  条件: (hs : s.有限)
  证明: (IsLinearSet.closure_of_finite hs).isSemilinearSet

Depends on / 依赖: IsLinearSet, IsLinearSet.closure_of_finite, closure_of_finite, isSemilinearSet
-/
theorem IsSemilinearSet.closure_of_finite (hs : s.Finite) :
    IsSemilinearSet (closure s : Set M) :=
  (IsLinearSet.closure_of_finite hs).isSemilinearSet

/--
theorem `IsSemilinearSet.of_fg` / 定理 `IsSemilinearSet.of_fg`

English:
theorem IsSemilinearSet.of_fg
  given: {P : AddSubmonoid M} (hP : P.FG)
  proof: (IsLinearSet.of_fg hP).isSemilinearSet

@[simp]

中文:
定理 IsSemilinearSet.of_fg
  条件: {P : 加法子幺半群 M} (hP : P.FG)
  证明: (IsLinearSet.of_fg hP).isSemilinearSet

@[simp]

Depends on / 依赖: IsLinearSet, IsLinearSet.of_fg, isSemilinearSet, of_fg
-/
theorem IsSemilinearSet.of_fg {P : AddSubmonoid M} (hP : P.FG) :
    IsSemilinearSet (P : Set M) :=
  (IsLinearSet.of_fg hP).isSemilinearSet

@[simp]
/--
theorem `IsSemilinearSet.univ` / 定理 `IsSemilinearSet.univ`

English:
theorem IsSemilinearSet.univ
  given: [AddMonoid.FG M]
  statement: IsSemilinearSet (univ : Set M)
  proof: IsLinearSet.univ.isSemilinearSet

中文:
定理 IsSemilinearSet.univ
  条件: [加法幺半群.FG M]
  结论: IsSemilinearSet (univ : 集合 M)
  证明: IsLinearSet.univ.isSemilinearSet
-/
protected theorem IsSemilinearSet.univ [AddMonoid.FG M] : IsSemilinearSet (univ : Set M) :=
  IsLinearSet.univ.isSemilinearSet

/--
theorem `IsSemilinearSet.union` / 定理 `IsSemilinearSet.union`

English:
theorem IsSemilinearSet.union
  given: (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂)
  proof: by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  rw [← sUnion_union]
  refine ⟨S₁ union S₂, hS₁.union hS₂, fun s hs => ?_, rfl⟩
  rw [mem_union] at hs
  exact hs.elim (hS₁' s) (hS₂' s)

中文:
定理 IsSemilinearSet.union
  条件: (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂)
  证明: by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  rw [← sUnion_union]
  refine ⟨S₁ union S₂, hS₁.union hS₂, fun s hs => ?_, rfl⟩
  rw [mem_union] at hs
  exact hs.elim (hS₁' s) (hS₂' s)

Depends on / 依赖: hs.elim, mem_union, sUnion_union
-/
theorem IsSemilinearSet.union (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) :
    IsSemilinearSet (s₁ union s₂) := by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  rw [← sUnion_union]
  refine ⟨S₁ union S₂, hS₁.union hS₂, fun s hs => ?_, rfl⟩
  rw [mem_union] at hs
  exact hs.elim (hS₁' s) (hS₂' s)

/--
theorem `IsSemilinearSet.sUnion` / 定理 `IsSemilinearSet.sUnion`

English:
theorem IsSemilinearSet.sUnion
  statement: {S : Set (Set M)} (hS : S.Finite)
  proof: by
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa using hS'.1.union (ih hS'.2)

中文:
定理 IsSemilinearSet.集合并集
  结论: {S : 集合 (集合 M)} (hS : S.有限)
  证明: by
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa using hS'.1.union (ih hS'.2)

Depends on / 依赖: Finite, Finite.induction_on, forall_eq_or_imp, induction_on, insert, mem_insert_iff, simp_rw
-/
theorem IsSemilinearSet.sUnion {S : Set (Set M)} (hS : S.Finite)
    (hS' : forall s in S, IsSemilinearSet s) : IsSemilinearSet (⋃₀ S) := by
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa using hS'.1.union (ih hS'.2)

/--
theorem `IsSemilinearSet.iUnion` / 定理 `IsSemilinearSet.iUnion`

English:
theorem IsSemilinearSet.iUnion
  given: [Finite ι] {s : ι -> Set M} (hs : forall i, IsSemilinearSet (s i))
  proof: by
  rw [← sUnion_range]
  apply sUnion (finite_range s)
  simpa

中文:
定理 IsSemilinearSet.iUnion
  条件: [有限 ι] {s : ι -> 集合 M} (hs : 对任意 i, IsSemilinearSet (s i))
  证明: by
  rw [← sUnion_range]
  apply sUnion (finite_range s)
  simpa

Depends on / 依赖: finite_range, sUnion, sUnion_range
-/
theorem IsSemilinearSet.iUnion [Finite ι] {s : ι -> Set M} (hs : forall i, IsSemilinearSet (s i)) :
    IsSemilinearSet (⋃ i, s i) := by
  rw [← sUnion_range]
  apply sUnion (finite_range s)
  simpa

/--
theorem `IsSemilinearSet.biUnion` / 定理 `IsSemilinearSet.biUnion`

English:
theorem IsSemilinearSet.biUnion
  statement: {s : Set ι} {t : ι -> Set M} (hs : s.Finite)
  proof: by
  rw [← sUnion_image]
  apply sUnion (hs.image t)
  simpa

中文:
定理 IsSemilinearSet.biUnion
  结论: {s : 集合 ι} {t : ι -> 集合 M} (hs : s.有限)
  证明: by
  rw [← sUnion_image]
  apply sUnion (hs.image t)
  simpa

Depends on / 依赖: hs.image, sUnion, sUnion_image
-/
theorem IsSemilinearSet.biUnion {s : Set ι} {t : ι -> Set M} (hs : s.Finite)
    (ht : forall i in s, IsSemilinearSet (t i)) : IsSemilinearSet (⋃ i in s, t i) := by
  rw [← sUnion_image]
  apply sUnion (hs.image t)
  simpa

/--
theorem `IsSemilinearSet.biUnion_finset` / 定理 `IsSemilinearSet.biUnion_finset`

English:
theorem IsSemilinearSet.biUnion_finset
  statement: {s : Finset ι} {t : ι -> Set M}
  proof: biUnion s.finite_toSet ht

中文:
定理 IsSemilinearSet.biUnion_finset
  结论: {s : 有限集 ι} {t : ι -> 集合 M}
  证明: biUnion s.finite_toSet ht

Depends on / 依赖: biUnion, finite_toSet, s.finite_toSet
-/
theorem IsSemilinearSet.biUnion_finset {s : Finset ι} {t : ι -> Set M}
    (ht : forall i in s, IsSemilinearSet (t i)) : IsSemilinearSet (⋃ i in s, t i) :=
  biUnion s.finite_toSet ht

/--
theorem `IsSemilinearSet.of_finite` / 定理 `IsSemilinearSet.of_finite`

English:
theorem IsSemilinearSet.of_finite
  given: (hs : s.Finite)
  statement: IsSemilinearSet s
  proof: by
  rw [← biUnion_of_singleton s]
  apply biUnion hs
  simp

中文:
定理 IsSemilinearSet.of_finite
  条件: (hs : s.有限)
  结论: IsSemilinearSet s
  证明: by
  rw [← biUnion_of_singleton s]
  apply biUnion hs
  simp

Depends on / 依赖: biUnion, biUnion_of_singleton
-/
theorem IsSemilinearSet.of_finite (hs : s.Finite) : IsSemilinearSet s := by
  rw [← biUnion_of_singleton s]
  apply biUnion hs
  simp

/--
theorem `IsSemilinearSet.vadd` / 定理 `IsSemilinearSet.vadd`

English:
theorem IsSemilinearSet.vadd
  given: (a : M) (hs : IsSemilinearSet s)
  statement: IsSemilinearSet (a +ᵥ s)
  proof: by
  rcases hs with ⟨S, hS, hS', rfl⟩
  rw [vadd_set_sUnion]
  exact biUnion hS fun s hs => ((hS' s hs).vadd a).isSemilinearSet

中文:
定理 IsSemilinearSet.vadd
  条件: (a : M) (hs : IsSemilinearSet s)
  结论: IsSemilinearSet (a +ᵥ s)
  证明: by
  rcases hs with ⟨S, hS, hS', rfl⟩
  rw [vadd_set_sUnion]
  exact biUnion hS fun s hs => ((hS' s hs).vadd a).isSemilinearSet

Depends on / 依赖: biUnion, isSemilinearSet, vadd_set_sUnion
-/
theorem IsSemilinearSet.vadd (a : M) (hs : IsSemilinearSet s) : IsSemilinearSet (a +ᵥ s) := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  rw [vadd_set_sUnion]
  exact biUnion hS fun s hs => ((hS' s hs).vadd a).isSemilinearSet

/--
theorem `IsSemilinearSet.add` / 定理 `IsSemilinearSet.add`

English:
theorem IsSemilinearSet.add
  given: (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂)
  proof: by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  simp_rw [sUnion_add, add_sUnion]
  exact biUnion hS₁ fun s₁ hs₁ => biUnion hS₂ fun s₂ hs₂ =>
    ((hS₁' s₁ hs₁).add (hS₂' s₂ hs₂)).isSemilinearSet

中文:
定理 IsSemilinearSet.add
  条件: (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂)
  证明: by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  simp_rw [sUnion_add, add_sUnion]
  exact biUnion hS₁ fun s₁ hs₁ => biUnion hS₂ fun s₂ hs₂ =>
    ((hS₁' s₁ hs₁).add (hS₂' s₂ hs₂)).isSemilinearSet

Depends on / 依赖: add_sUnion, biUnion, isSemilinearSet, sUnion_add, simp_rw
-/
theorem IsSemilinearSet.add (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) :
    IsSemilinearSet (s₁ + s₂) := by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  simp_rw [sUnion_add, add_sUnion]
  exact biUnion hS₁ fun s₁ hs₁ => biUnion hS₂ fun s₂ hs₂ =>
    ((hS₁' s₁ hs₁).add (hS₂' s₂ hs₂)).isSemilinearSet

/--
theorem `IsSemilinearSet.image` / 定理 `IsSemilinearSet.image`

English:
theorem IsSemilinearSet.image
  given: (hs : IsSemilinearSet s) (f : F)
  statement: IsSemilinearSet (f '' s)
  proof: by
  rcases hs with ⟨S, hS, hS', rfl⟩
  simp_rw [sUnion_eq_biUnion, image_iUnion]
  exact biUnion hS fun s hs => ((hS' s hs).image f).isSemilinearSet

中文:
定理 IsSemilinearSet.像
  条件: (hs : IsSemilinearSet s) (f : F)
  结论: IsSemilinearSet (f '' s)
  证明: by
  rcases hs with ⟨S, hS, hS', rfl⟩
  simp_rw [sUnion_eq_biUnion, image_iUnion]
  exact biUnion hS fun s hs => ((hS' s hs).image f).isSemilinearSet

Depends on / 依赖: biUnion, image_iUnion, isSemilinearSet, sUnion_eq_biUnion, simp_rw
-/
theorem IsSemilinearSet.image (hs : IsSemilinearSet s) (f : F) : IsSemilinearSet (f '' s) := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  simp_rw [sUnion_eq_biUnion, image_iUnion]
  exact biUnion hS fun s hs => ((hS' s hs).image f).isSemilinearSet

/--
theorem `isSemilinearSet_image_iff` / 定理 `isSemilinearSet_image_iff`

English:
theorem isSemilinearSet_image_iff
  given: {F : Type*} [EquivLike F M N] [AddEquivClass F M N] (f : F)
  proof: by
  constructor <;> intro h
  · convert! h.image (f : M ≃+ N).symm
    simp [image_image]
  · exact h.image f

中文:
定理 isSemilinearSet_image_iff
  条件: {F : 类型} [等价状 F M N] [加法等价类 F M N] (f : F)
  证明: by
  constructor <;> intro h
  · convert! h.image (f : M ≃+ N).symm
    simp [image_image]
  · exact h.image f

Depends on / 依赖: convert, h.image, image_image
-/
theorem isSemilinearSet_image_iff {F : Type*} [EquivLike F M N] [AddEquivClass F M N] (f : F) :
    IsSemilinearSet (f '' s) ↔ IsSemilinearSet s := by
  constructor <;> intro h
  · convert! h.image (f : M ≃+ N).symm
    simp [image_image]
  · exact h.image f

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsSemilinearSet.proj` / 定理 `IsSemilinearSet.proj`

English:
theorem IsSemilinearSet.proj
  given: {s : Set (ι oplus κ -> M)} (hs : IsSemilinearSet s)
  proof: by
  convert! hs.image (LinearMap.funLeft Nat M Sum.inl)
  ext x
  constructor
  · intro ⟨y, hy⟩
    exact ⟨Sum.elim x y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y ∘ Sum.inr, ?_⟩
    simpa [LinearMap.funLeft]

中文:
定理 IsSemilinearSet.proj
  条件: {s : 集合 (ι oplus κ -> M)} (hs : IsSemilinearSet s)
  证明: by
  convert! hs.image (LinearMap.funLeft Nat M Sum.inl)
  ext x
  constructor
  · intro ⟨y, hy⟩
    exact ⟨Sum.elim x y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y ∘ Sum.inr, ?_⟩
    simpa [LinearMap.funLeft]

Depends on / 依赖: LinearMap, LinearMap.funLeft, Sum.elim, Sum.inl, Sum.inr, convert, funLeft, hs.image
-/
theorem IsSemilinearSet.proj {s : Set (ι oplus κ -> M)} (hs : IsSemilinearSet s) :
    IsSemilinearSet { x | exists y, Sum.elim x y in s } := by
  convert! hs.image (LinearMap.funLeft Nat M Sum.inl)
  ext x
  constructor
  · intro ⟨y, hy⟩
    exact ⟨Sum.elim x y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y ∘ Sum.inr, ?_⟩
    simpa [LinearMap.funLeft]

/--
theorem `IsSemilinearSet.proj'` / 定理 `IsSemilinearSet.proj'`

English:
theorem IsSemilinearSet.proj'
  given: {p : (ι -> M) -> (κ -> M) -> Prop}
  proof: proj

中文:
定理 IsSemilinearSet.proj'
  条件: {p : (ι -> M) -> (κ -> M) -> 命题}
  证明: proj
-/
theorem IsSemilinearSet.proj' {p : (ι -> M) -> (κ -> M) -> Prop} :
    IsSemilinearSet { x | p (x ∘ Sum.inl) (x ∘ Sum.inr) } -> IsSemilinearSet { x | exists y, p x y } :=
  proj

/--
lemma `IsLinearSet.closure` / 引理 `IsLinearSet.closure`

English:
lemma IsLinearSet.closure
  given: (hs : IsLinearSet s)
  statement: IsSemilinearSet (closure s : Set M)
  proof: by
  rcases hs with ⟨a, t, ht, rfl⟩
  convert! (IsSemilinearSet.singleton 0).union (isSemilinearSet ⟨a, { a } union t, by simp [ht], rfl⟩)
  ext x
  simp only [SetLike.mem_coe, singleton_union, mem_insert_iff, mem_vadd_set, vadd_eq_add]
  constructor
  · intro hx
    induction hx using closure_induc

中文:
引理 IsLinearSet.closure
  条件: (hs : IsLinearSet s)
  结论: IsSemilinearSet (closure s : 集合 M)
  证明: by
  rcases hs with ⟨a, t, ht, rfl⟩
  convert! (IsSemilinearSet.singleton 0).union (isSemilinearSet ⟨a, { a } union t, by simp [ht], rfl⟩)
  ext x
  simp only [SetLike.mem_coe, singleton_union, mem_insert_iff, mem_vadd_set, vadd_eq_add]
  constructor
  · intro hx
    induction hx using closure_induc
-/
protected lemma IsLinearSet.closure (hs : IsLinearSet s) : IsSemilinearSet (closure s : Set M) := by
  rcases hs with ⟨a, t, ht, rfl⟩
  convert! (IsSemilinearSet.singleton 0).union (isSemilinearSet ⟨a, { a } union t, by simp [ht], rfl⟩)
  ext x
  simp only [SetLike.mem_coe, singleton_union, mem_insert_iff, mem_vadd_set, vadd_eq_add]
  constructor
  · intro hx
    induction hx using closure_induction with
    | mem x hx =>
      rcases hx with ⟨x, hx, rfl⟩
      exact Or.inr ⟨x, closure_mono (subset_insert _ _) hx, rfl⟩
    | zero => exact Or.inl rfl
    | add x y _ _ ih₁ ih₂ =>
      rcases ih₁ with rfl | ⟨x, hx, rfl⟩
      · simpa
      · rcases ih₂ with rfl | ⟨y, hy, rfl⟩
        · exact Or.inr ⟨x, hx, by simp⟩
        · refine Or.inr ⟨_, add_mem (mem_closure_of_mem (mem_insert _ _)) (add_mem hx hy), ?_⟩
          simp_rw [← add_assoc, add_right_comm a a x]
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · simp
    · simp_rw [insert_eq, closure_union, mem_sup, mem_closure_singleton] at hx
      rcases hx with ⟨_, ⟨n, rfl⟩, ⟨x, hx, rfl⟩⟩
      rw [add_left_comm]
      refine add_mem (nsmul_mem (mem_closure_of_mem ?_) _)
        (mem_closure_of_mem (vadd_mem_vadd_set hx))
      nth_rw 2 [← add_zero a]
      exact vadd_mem_vadd_set (zero_mem _)

/--
theorem `IsSemilinearSet.closure` / 定理 `IsSemilinearSet.closure`

English:
theorem IsSemilinearSet.closure
  given: (hs : IsSemilinearSet s)
  proof: by
  rcases hs with ⟨S, hS, hS', rfl⟩
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa [closure_union, coe_sup] using hS'.1.closure.add (ih hS'.2)

中文:
定理 IsSemilinearSet.closure
  条件: (hs : IsSemilinearSet s)
  证明: by
  rcases hs with ⟨S, hS, hS', rfl⟩
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa [closure_union, coe_sup] using hS'.1.closure.add (ih hS'.2)
-/
protected theorem IsSemilinearSet.closure (hs : IsSemilinearSet s) :
    IsSemilinearSet (closure s : Set M) := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa [closure_union, coe_sup] using hS'.1.closure.add (ih hS'.2)

/--
Definition of `IsProperLinearSet` / `IsProperLinearSet` 的定义

English:
definition IsProperLinearSet
  signature: (s : Set M)
  body: exists (a : M) (t : Set M), t.Finite ∧ LinearIndepOn Nat id t ∧ s = a +ᵥ (closure t : Set M)

中文:
定义 IsProperLinearSet
  签名: (s : 集合 M)
  定义体: exists (a : M) (t : Set M), t.Finite ∧ LinearIndepOn Nat id t ∧ s = a +ᵥ (closure t : Set M)

Depends on / 依赖: Finite, LinearIndepOn, closure, t.Finite
-/
def IsProperLinearSet (s : Set M) : Prop :=
  exists (a : M) (t : Set M), t.Finite ∧ LinearIndepOn Nat id t ∧ s = a +ᵥ (closure t : Set M)

/--
theorem `isProperLinearSet_iff` / 定理 `isProperLinearSet_iff`

English:
theorem isProperLinearSet_iff
  proof: exists_congr fun a =>
    ⟨fun ⟨t, ht, hs⟩ => ⟨ht.toFinset, by simpa⟩, fun ⟨t, hs⟩ => ⟨t, t.finite_toSet, hs⟩⟩

中文:
定理 isProperLinearSet_iff
  证明: exists_congr fun a =>
    ⟨fun ⟨t, ht, hs⟩ => ⟨ht.toFinset, by simpa⟩, fun ⟨t, hs⟩ => ⟨t, t.finite_toSet, hs⟩⟩

Depends on / 依赖: exists_congr, finite_toSet, ht.toFinset, t.finite_toSet, toFinset
-/
theorem isProperLinearSet_iff :
    IsProperLinearSet s ↔ exists (a : M) (t : Finset M),
      LinearIndepOn Nat id (t : Set M) ∧ s = a +ᵥ (closure (t : Set M) : Set M) :=
  exists_congr fun a =>
    ⟨fun ⟨t, ht, hs⟩ => ⟨ht.toFinset, by simpa⟩, fun ⟨t, hs⟩ => ⟨t, t.finite_toSet, hs⟩⟩

/--
theorem `IsProperLinearSet.isLinearSet` / 定理 `IsProperLinearSet.isLinearSet`

English:
theorem IsProperLinearSet.isLinearSet
  given: (hs : IsProperLinearSet s)
  statement: IsLinearSet s
  proof: by
  rcases hs with ⟨a, t, ht, _, rfl⟩
  exact ⟨a, t, ht, rfl⟩

@[simp]

中文:
定理 IsProperLinearSet.isLinearSet
  条件: (hs : IsProperLinearSet s)
  结论: IsLinearSet s
  证明: by
  rcases hs with ⟨a, t, ht, _, rfl⟩
  exact ⟨a, t, ht, rfl⟩

@[simp]
-/
theorem IsProperLinearSet.isLinearSet (hs : IsProperLinearSet s) : IsLinearSet s := by
  rcases hs with ⟨a, t, ht, _, rfl⟩
  exact ⟨a, t, ht, rfl⟩

@[simp]
/--
theorem `IsProperLinearSet.singleton` / 定理 `IsProperLinearSet.singleton`

English:
theorem IsProperLinearSet.singleton
  given: (a : M)
  statement: IsProperLinearSet {a}
  proof: ⟨a, ∅, by simp⟩

中文:
定理 IsProperLinearSet.singleton
  条件: (a : M)
  结论: IsProperLinearSet {a}
  证明: ⟨a, ∅, by simp⟩
-/
theorem IsProperLinearSet.singleton (a : M) : IsProperLinearSet {a} :=
  ⟨a, ∅, by simp⟩

/--
Definition of `IsProperSemilinearSet` / `IsProperSemilinearSet` 的定义

English:
definition IsProperSemilinearSet
  signature: (s : Set M)
  body: exists (S : Set (Set M)), S.Finite ∧ (forall t in S, IsProperLinearSet t) ∧ s = ⋃₀ S

中文:
定义 IsProperSemilinearSet
  签名: (s : 集合 M)
  定义体: exists (S : Set (Set M)), S.Finite ∧ (forall t in S, IsProperLinearSet t) ∧ s = ⋃₀ S

Depends on / 依赖: Finite, IsProperLinearSet, S.Finite
-/
def IsProperSemilinearSet (s : Set M) : Prop :=
  exists (S : Set (Set M)), S.Finite ∧ (forall t in S, IsProperLinearSet t) ∧ s = ⋃₀ S

/--
theorem `isProperSemilinearSet_iff` / 定理 `isProperSemilinearSet_iff`

English:
theorem isProperSemilinearSet_iff
  proof: Set.exists_finite_iff_finset

中文:
定理 isProperSemilinearSet_iff
  证明: Set.exists_finite_iff_finset

Depends on / 依赖: Set.exists_finite_iff_finset, exists_finite_iff_finset
-/
theorem isProperSemilinearSet_iff :
    IsProperSemilinearSet s ↔ exists (S : Finset (Set M)), (forall t in S, IsProperLinearSet t) ∧ s = ⋃₀ S :=
  Set.exists_finite_iff_finset

/--
theorem `IsProperSemilinearSet.isSemilinearSet` / 定理 `IsProperSemilinearSet.isSemilinearSet`

English:
theorem IsProperSemilinearSet.isSemilinearSet
  given: (hs : IsProperSemilinearSet s)
  proof: by
  rcases hs with ⟨S, hS, hS', rfl⟩
  exact ⟨S, hS, fun s hs => (hS' s hs).isLinearSet, rfl⟩

中文:
定理 IsProperSemilinearSet.isSemilinearSet
  条件: (hs : IsProperSemilinearSet s)
  证明: by
  rcases hs with ⟨S, hS, hS', rfl⟩
  exact ⟨S, hS, fun s hs => (hS' s hs).isLinearSet, rfl⟩

Depends on / 依赖: isLinearSet
-/
theorem IsProperSemilinearSet.isSemilinearSet (hs : IsProperSemilinearSet s) :
    IsSemilinearSet s := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  exact ⟨S, hS, fun s hs => (hS' s hs).isLinearSet, rfl⟩

/--
theorem `IsProperLinearSet.isProperSemilinearSet` / 定理 `IsProperLinearSet.isProperSemilinearSet`

English:
theorem IsProperLinearSet.isProperSemilinearSet
  given: (hs : IsProperLinearSet s)
  proof: ⟨{s}, by simpa⟩

@[simp]

中文:
定理 IsProperLinearSet.isProperSemilinearSet
  条件: (hs : IsProperLinearSet s)
  证明: ⟨{s}, by simpa⟩

@[simp]
-/
theorem IsProperLinearSet.isProperSemilinearSet (hs : IsProperLinearSet s) :
    IsProperSemilinearSet s :=
  ⟨{s}, by simpa⟩

@[simp]
/--
theorem `IsProperSemilinearSet.empty` / 定理 `IsProperSemilinearSet.empty`

English:
theorem IsProperSemilinearSet.empty
  statement: IsProperSemilinearSet (∅ : Set M)
  proof: ⟨∅, by simp⟩

中文:
定理 IsProperSemilinearSet.empty
  结论: IsProperSemilinearSet (∅ : 集合 M)
  证明: ⟨∅, by simp⟩
-/
theorem IsProperSemilinearSet.empty : IsProperSemilinearSet (∅ : Set M) :=
  ⟨∅, by simp⟩

/--
theorem `IsProperSemilinearSet.union` / 定理 `IsProperSemilinearSet.union`

English:
theorem IsProperSemilinearSet.union
  statement: (hs₁ : IsProperSemilinearSet s₁)
  proof: by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  rw [← sUnion_union]
  refine ⟨S₁ union S₂, hS₁.union hS₂, fun s hs => ?_, rfl⟩
  rw [mem_union] at hs
  exact hs.elim (hS₁' s) (hS₂' s)

中文:
定理 IsProperSemilinearSet.union
  结论: (hs₁ : IsProperSemilinearSet s₁)
  证明: by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  rw [← sUnion_union]
  refine ⟨S₁ union S₂, hS₁.union hS₂, fun s hs => ?_, rfl⟩
  rw [mem_union] at hs
  exact hs.elim (hS₁' s) (hS₂' s)

Depends on / 依赖: hs.elim, mem_union, sUnion_union
-/
theorem IsProperSemilinearSet.union (hs₁ : IsProperSemilinearSet s₁)
    (hs₂ : IsProperSemilinearSet s₂) : IsProperSemilinearSet (s₁ union s₂) := by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  rw [← sUnion_union]
  refine ⟨S₁ union S₂, hS₁.union hS₂, fun s hs => ?_, rfl⟩
  rw [mem_union] at hs
  exact hs.elim (hS₁' s) (hS₂' s)

/--
theorem `IsProperSemilinearSet.sUnion` / 定理 `IsProperSemilinearSet.sUnion`

English:
theorem IsProperSemilinearSet.sUnion
  statement: {S : Set (Set M)} (hS : S.Finite)
  proof: by
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa using hS'.1.union (ih hS'.2)

中文:
定理 IsProperSemilinearSet.集合并集
  结论: {S : 集合 (集合 M)} (hS : S.有限)
  证明: by
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa using hS'.1.union (ih hS'.2)

Depends on / 依赖: Finite, Finite.induction_on, forall_eq_or_imp, induction_on, insert, mem_insert_iff, simp_rw
-/
theorem IsProperSemilinearSet.sUnion {S : Set (Set M)} (hS : S.Finite)
    (hS' : forall s in S, IsProperSemilinearSet s) : IsProperSemilinearSet (⋃₀ S) := by
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa using hS'.1.union (ih hS'.2)

/--
theorem `IsProperSemilinearSet.biUnion` / 定理 `IsProperSemilinearSet.biUnion`

English:
theorem IsProperSemilinearSet.biUnion
  statement: {s : Set ι} {t : ι -> Set M} (hs : s.Finite)
  proof: by
  rw [← sUnion_image]
  apply sUnion (hs.image t)
  simpa

中文:
定理 IsProperSemilinearSet.biUnion
  结论: {s : 集合 ι} {t : ι -> 集合 M} (hs : s.有限)
  证明: by
  rw [← sUnion_image]
  apply sUnion (hs.image t)
  simpa

Depends on / 依赖: hs.image, sUnion, sUnion_image
-/
theorem IsProperSemilinearSet.biUnion {s : Set ι} {t : ι -> Set M} (hs : s.Finite)
    (ht : forall i in s, IsProperSemilinearSet (t i)) : IsProperSemilinearSet (⋃ i in s, t i) := by
  rw [← sUnion_image]
  apply sUnion (hs.image t)
  simpa

/--
theorem `IsProperSemilinearSet.biUnion_finset` / 定理 `IsProperSemilinearSet.biUnion_finset`

English:
theorem IsProperSemilinearSet.biUnion_finset
  statement: {s : Finset ι} {t : ι -> Set M}
  proof: biUnion s.finite_toSet ht

中文:
定理 IsProperSemilinearSet.biUnion_finset
  结论: {s : 有限集 ι} {t : ι -> 集合 M}
  证明: biUnion s.finite_toSet ht

Depends on / 依赖: biUnion, finite_toSet, s.finite_toSet
-/
theorem IsProperSemilinearSet.biUnion_finset {s : Finset ι} {t : ι -> Set M}
    (ht : forall i in s, IsProperSemilinearSet (t i)) : IsProperSemilinearSet (⋃ i in s, t i) :=
  biUnion s.finite_toSet ht

/--
lemma `IsLinearSet.isProperSemilinearSet` / 引理 `IsLinearSet.isProperSemilinearSet`

English:
lemma IsLinearSet.isProperSemilinearSet
  given: [IsCancelAdd M] (hs : IsLinearSet s)
  proof: by
  classical
  rw [isLinearSet_iff] at hs
  rcases hs with ⟨a, t, rfl⟩
  induction hn : t.card using Nat.strong_induction_on generalizing a t with | _ n ih
  subst hn
  by_cases hindep : LinearIndepOn Nat id (t : Set M)
  · exact IsProperLinearSet.isProperSemilinearSet ⟨a, t, by simpa⟩
  rw [not_l

中文:
引理 IsLinearSet.isProperSemilinearSet
  条件: [是消去加法 M] (hs : IsLinearSet s)
  证明: by
  classical
  rw [isLinearSet_iff] at hs
  rcases hs with ⟨a, t, rfl⟩
  induction hn : t.card using Nat.strong_induction_on generalizing a t with | _ n ih
  subst hn
  by_cases hindep : LinearIndepOn Nat id (t : Set M)
  · exact IsProperLinearSet.isProperSemilinearSet ⟨a, t, by simpa⟩
  rw [not_l

Depends on / 依赖: Finset, Finset.range, Function, Function.id_def, IsProperLinearSet, IsProperLinearSet.isProperSemilinearSet, IsProperSemilinearSet, LinearIndepOn, Nat.strong_induction_on, classical, closure, convert_to, generalizing, hindep, id_def, isLinearSet_iff, isProperSemilinearSet, strong_induction_on, t.card
-/
lemma IsLinearSet.isProperSemilinearSet [IsCancelAdd M] (hs : IsLinearSet s) :
    IsProperSemilinearSet s := by
  classical
  rw [isLinearSet_iff] at hs
  rcases hs with ⟨a, t, rfl⟩
  induction hn : t.card using Nat.strong_induction_on generalizing a t with | _ n ih
  subst hn
  by_cases hindep : LinearIndepOn Nat id (t : Set M)
  · exact IsProperLinearSet.isProperSemilinearSet ⟨a, t, by simpa⟩
  rw [not_linearIndepOn_finset_iffₒₛ] at hindep
  rcases hindep with ⟨t', ht', f, heq, i, hi, hfi⟩
  simp only [Function.id_def] at heq
  convert_to IsProperSemilinearSet (⋃ j in t', ⋃ k in Finset.range (f j),
    (a + k • j) +ᵥ (closure (t.erase j : Set M) : Set M))
  · ext x
    simp only [mem_vadd_set, SetLike.mem_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_closure_finset] at hy
      rcases hy with ⟨g, -, rfl⟩
      induction hn : g i using Nat.strong_induction_on generalizing g with | _ n ih'
      subst hn
      by_cases! hfg : forall j in t', f j <= g j
      · convert!
        ih' (g i - f i) (Nat.sub_lt_self hfi (hfg i hi))
          (fun j => if j in t' then g j - f j else g j + f j) (by simp [hi]) using 1
        conv_lhs => rw [← Finset.union_sdiff_of_subset ht']
        simp_rw [vadd_eq_add, add_left_cancel_iff, Finset.sum_union Finset.sdiff_disjoint.symm,
          ite_smul, Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 ht',
          Finset.filter_notMem_eq_sdiff, add_smul, Finset.sum_add_distrib, ← heq, ← add_assoc,
          add_right_comm, ← Finset.sum_add_distrib]
        congr! 2 with j hj
        rw [← add_smul]; rw [tsub_add_cancel_of_le (hfg j hj)]
      · rcases hfg with ⟨j, hj, hgj⟩
        simp only [mem_iUnion, Finset.mem_range, mem_vadd_set, SetLike.mem_coe, vadd_eq_add]
        refine ⟨j, hj, g j, hgj, ∑ k in t.erase j, g k • k,
          sum_mem fun x hx => (nsmul_mem (mem_closure_of_mem hx) _), ?_⟩
        rw [← Finset.sum_erase_add _ _ (ht' hj)]; rw [← add_assoc]; rw [add_right_comm]
    · simp only [mem_iUnion, Finset.mem_range, mem_vadd_set, SetLike.mem_coe, vadd_eq_add]
      rintro ⟨j, hj, k, hk, y, hy, rfl⟩
      refine ⟨k • j + y,
        add_mem (nsmul_mem (mem_closure_of_mem (ht' hj)) _)
          ((closure_mono (t.erase_subset j)) hy), ?_⟩
      rw [add_assoc]
  · exact .biUnion_finset fun j hj => .biUnion_finset fun k hk =>
      ih _ (Finset.card_lt_card (Finset.erase_ssubset (ht' hj))) _ _ rfl

/--
theorem `IsSemilinearSet.isProperSemilinearSet` / 定理 `IsSemilinearSet.isProperSemilinearSet`

English:
theorem IsSemilinearSet.isProperSemilinearSet
  given: [IsCancelAdd M] (hs : IsSemilinearSet s)
  proof: by
  rcases hs with ⟨S, hS, hS', rfl⟩
  simp_rw [sUnion_eq_biUnion]
  exact IsProperSemilinearSet.biUnion hS fun s hs => (hS' s hs).isProperSemilinearSet

中文:
定理 IsSemilinearSet.isProperSemilinearSet
  条件: [是消去加法 M] (hs : IsSemilinearSet s)
  证明: by
  rcases hs with ⟨S, hS, hS', rfl⟩
  simp_rw [sUnion_eq_biUnion]
  exact IsProperSemilinearSet.biUnion hS fun s hs => (hS' s hs).isProperSemilinearSet

Depends on / 依赖: IsProperSemilinearSet, IsProperSemilinearSet.biUnion, biUnion, isProperSemilinearSet, sUnion_eq_biUnion, simp_rw
-/
theorem IsSemilinearSet.isProperSemilinearSet [IsCancelAdd M] (hs : IsSemilinearSet s) :
    IsProperSemilinearSet s := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  simp_rw [sUnion_eq_biUnion]
  exact IsProperSemilinearSet.biUnion hS fun s hs => (hS' s hs).isProperSemilinearSet



/--
theorem `Nat.isSemilinearSet_iff_ultimately_periodic` / 定理 `Nat.isSemilinearSet_iff_ultimately_periodic`

English:
theorem Nat.isSemilinearSet_iff_ultimately_periodic
  given: {s : Set Nat}
  proof: by
  constructor
  · intro hs
    apply IsSemilinearSet.isProperSemilinearSet at hs
    rw [isProperSemilinearSet_iff] at hs
    rcases hs with ⟨S, hS, rfl⟩
    replace hS : forall t in S, exists k, exists p > 0, forall x >= k, x in t ↔ x + p in t := by
      intro t ht
      apply hS at ht
      rw

中文:
定理 自然数.isSemilinearSet_iff_ultimately_periodic
  条件: {s : 集合 自然数}
  证明: by
  constructor
  · intro hs
    apply IsSemilinearSet.isProperSemilinearSet at hs
    rw [isProperSemilinearSet_iff] at hs
    rcases hs with ⟨S, hS, rfl⟩
    replace hS : forall t in S, exists k, exists p > 0, forall x >= k, x in t ↔ x + p in t := by
      intro t ht
      apply hS at ht
      rw

Depends on / 依赖: CommSemiring, CommSemiring.rank_self, Finset, Finset.card_le_one_iff_subset_singleton, Finset.subset_singleton_iff, IsSemilinearSet, IsSemilinearSet.isProperSemilinearSet, card_le_one_iff_subset_singleton, cardinal_le_rank, ht.cardinal_le_rank, isProperLinearSet_iff, isProperSemilinearSet, isProperSemilinearSet_iff, rank_self, replace, simp_rw, subset_singleton_iff, t.card
-/
theorem Nat.isSemilinearSet_iff_ultimately_periodic {s : Set Nat} :
    IsSemilinearSet s ↔ exists k, exists p > 0, forall x >= k, x in s ↔ x + p in s := by
  constructor
  · intro hs
    apply IsSemilinearSet.isProperSemilinearSet at hs
    rw [isProperSemilinearSet_iff] at hs
    rcases hs with ⟨S, hS, rfl⟩
    replace hS : forall t in S, exists k, exists p > 0, forall x >= k, x in t ↔ x + p in t := by
      intro t ht
      apply hS at ht
      rw [isProperLinearSet_iff] at ht
      rcases ht with ⟨a, t, ht, rfl⟩
      have hcard : t.card <= 1 := by simpa [CommSemiring.rank_self] using ht.cardinal_le_rank
      simp_rw [Finset.card_le_one_iff_subset_singleton, Finset.subset_singleton_iff] at hcard
      rcases hcard with ⟨b, (rfl | rfl)⟩
      · refine ⟨a + 1, 1, zero_lt_one, fun x hx => ?_⟩
        simp [(by grind : x != a), (by grind : x + 1 != a)]
      · have hb : b != 0 := by simpa [ne_comm] using ht.zero_notMem_image
        rw [Nat.ne_zero_iff_zero_lt] at hb
        refine ⟨a, b, hb, fun x hx => ?_⟩
        simp only [Finset.coe_singleton, mem_vadd_set, SetLike.mem_coe,
          AddSubmonoid.mem_closure_singleton, smul_eq_mul, vadd_eq_add, exists_exists_eq_and]
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨x + 1, by grind⟩
        · rintro ⟨y, heq⟩
          cases y with
          | zero => exact ⟨0, by grind⟩
          | succ y => exact ⟨y, by grind⟩
    choose! k p hS hS' using hS
    refine ⟨S.sup k, S.lcm p, ?_, fun x hx => ?_⟩
    · grind [Finset.lcm_eq_zero_iff]
    · simp only [mem_sUnion, SetLike.mem_coe]
      refine exists_congr fun t => and_congr_right fun ht => ?_
      have hpt : p t ∣ S.lcm p := Finset.dvd_lcm ht
      rw [dvd_iff_exists_eq_mul_left] at hpt
      rcases hpt with ⟨m, hpt⟩
      rw [hpt]
      clear hpt
      induction m with grind [Finset.sup_le_iff]
  · intro ⟨k, p, hp, hs⟩
    have h₁ : {x in s | x < k}.Finite := (Set.finite_lt_nat k).subset (sep_subset_ofPred _ _)
    have h₂ : {x in s | k <= x ∧ x < k + p}.Finite :=
      (Set.finite_Ico k (k + p)).subset (sep_subset_ofPred _ _)
    convert! (IsSemilinearSet.of_finite h₁).union (.add (.of_finite h₂) (.closure_finset { p }))
    ext x
    simp only [sep_and, Finset.coe_singleton, mem_union, mem_ofPred_eq, mem_add, mem_inter_iff,
      SetLike.mem_coe, AddSubmonoid.mem_closure_singleton, smul_eq_mul, exists_exists_eq_and]
    constructor
    · intro hx
      by_cases hx' : x < k
      · exact Or.inl ⟨hx, hx'⟩
      · rw [not_lt] at hx'
        refine Or.inr ⟨k + (x - k) % p, ⟨⟨?_1, ?_2⟩, ?_1, ?_3⟩, (x - k) / p, ?_4⟩
        · rw [← add_tsub_cancel_of_le hx', ← Nat.mod_add_div' (x - k) p, ← add_assoc] at hx
          generalize (x - k) / p = m at hx
          induction m with grind
        · grind
        · exact Nat.add_lt_add_left (Nat.mod_lt _ hp) _
        · rw [add_assoc, Nat.mod_add_div', add_tsub_cancel_of_le hx']
    · rintro (⟨hx, hx'⟩ | ⟨x, ⟨⟨hx, hx'⟩, _⟩, m, rfl⟩)
      · exact hx
      · induction m with grind
