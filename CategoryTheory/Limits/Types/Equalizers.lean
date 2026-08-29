/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# Equalizers in Type

The equalizer of a pair of maps `(g, h)` from `X` to `Y` is the subtype `{x : Y // g x = h x}`.

-/

@[expose] public section

universe v u

open CategoryTheory Limits ConcreteCategory

namespace CategoryTheory.Limits.Types

variable {X Y Z : Type u} (f : X ⟶ Y) {g h : Y ⟶ Z} (w : f ≫ g = f ≫ h)

/--
Definition of `typeEqualizerOfUnique` / `typeEqualizerOfUnique` 的定义

English:
definition typeEqualizerOfUnique
  signature: (t : forall y : Y, g y = h y -> exists! x : X, f x = y)
  body: Fork.IsLimit.mk' _ fun s => by
    refine ⟨↾fun i => ?_, ?_, ?_⟩
    · apply Classical.choose (t (s.ι i) _)
      apply congr_hom s.condition i
    · ext i
      exact (Classical.choose_spec (t (s.ι i) (congr_hom s.condition i))).1
    · intro m hm
      ext i
      exact (Classical.choose_spec (t (

中文:
定义 typeEqualizerOfUnique
  签名: (t : 对任意 y : Y, g y = h y -> 存在! x : X, f x = y)
  定义体: Fork.IsLimit.mk' _ fun s => by
    refine ⟨↾fun i => ?_, ?_, ?_⟩
    · apply Classical.choose (t (s.ι i) _)
      apply congr_hom s.condition i
    · ext i
      exact (Classical.choose_spec (t (s.ι i) (congr_hom s.condition i))).1
    · intro m hm
      ext i
      exact (Classical.choose_spec (t (

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, Fork.IsLimit.mk, IsLimit, choose_spec, condition, congr_hom, s.condition
-/
noncomputable def typeEqualizerOfUnique (t : forall y : Y, g y = h y -> exists! x : X, f x = y) :
    IsLimit (Fork.ofι _ w) :=
  Fork.IsLimit.mk' _ fun s => by
    refine ⟨↾fun i => ?_, ?_, ?_⟩
    · apply Classical.choose (t (s.ι i) _)
      apply congr_hom s.condition i
    · ext i
      exact (Classical.choose_spec (t (s.ι i) (congr_hom s.condition i))).1
    · intro m hm
      ext i
      exact (Classical.choose_spec (t (s.ι i) (congr_hom s.condition i))).2 _ (congr_hom hm i)

/--
theorem `unique_of_type_equalizer` / 定理 `unique_of_type_equalizer`

English:
theorem unique_of_type_equalizer
  given: (t : IsLimit (Fork.ofι _ w)) (y : Y) (hy : g y = h y)
  proof: by
  let y' : PUnit ⟶ Y := ↾fun _ => y
  have hy' : y' ≫ g = y' ≫ h := by ext; exact hy
  refine ⟨(Fork.IsLimit.lift' t _ hy').1 ⟨⟩, congr_hom (Fork.IsLimit.lift' t y' _).2 ⟨⟩, ?_⟩
  intro x' hx'
  suffices (fun _ : PUnit => x') = (Fork.IsLimit.lift' t y' hy').1 by
    rw [← this]
  apply TypeCat.ho

中文:
定理 unique_of_type_equalizer
  条件: (t : IsLimit (Fork.ofι _ w)) (y : Y) (hy : g y = h y)
  证明: by
  let y' : PUnit ⟶ Y := ↾fun _ => y
  have hy' : y' ≫ g = y' ≫ h := by ext; exact hy
  refine ⟨(Fork.IsLimit.lift' t _ hy').1 ⟨⟩, congr_hom (Fork.IsLimit.lift' t y' _).2 ⟨⟩, ?_⟩
  intro x' hx'
  suffices (fun _ : PUnit => x') = (Fork.IsLimit.lift' t y' hy').1 by
    rw [← this]
  apply TypeCat.ho

Depends on / 依赖: Fork.IsLimit.hom_ext, Fork.IsLimit.lift, IsLimit, TypeCat, TypeCat.homEquiv.symm.injective, congr_hom, homEquiv, hom_ext, injective
-/
theorem unique_of_type_equalizer (t : IsLimit (Fork.ofι _ w)) (y : Y) (hy : g y = h y) :
    exists! x : X, f x = y := by
  let y' : PUnit ⟶ Y := ↾fun _ => y
  have hy' : y' ≫ g = y' ≫ h := by ext; exact hy
  refine ⟨(Fork.IsLimit.lift' t _ hy').1 ⟨⟩, congr_hom (Fork.IsLimit.lift' t y' _).2 ⟨⟩, ?_⟩
  intro x' hx'
  suffices (fun _ : PUnit => x') = (Fork.IsLimit.lift' t y' hy').1 by
    rw [← this]
  apply TypeCat.homEquiv.symm.injective
  apply Fork.IsLimit.hom_ext t
  ext ⟨⟩
  apply hx'.trans (congr_hom (Fork.IsLimit.lift' t _ hy').2 ⟨⟩).symm

/--
theorem `type_equalizer_iff_unique` / 定理 `type_equalizer_iff_unique`

English:
theorem type_equalizer_iff_unique
  proof: ⟨fun i => unique_of_type_equalizer _ _ (Classical.choice i), fun k =>
    ⟨typeEqualizerOfUnique f w k⟩⟩

中文:
定理 type_equalizer_iff_unique
  证明: ⟨fun i => unique_of_type_equalizer _ _ (Classical.choice i), fun k =>
    ⟨typeEqualizerOfUnique f w k⟩⟩

Depends on / 依赖: Classical, Classical.choice, choice, typeEqualizerOfUnique, unique_of_type_equalizer
-/
theorem type_equalizer_iff_unique :
    Nonempty (IsLimit (Fork.ofι _ w)) ↔ forall y : Y, g y = h y -> exists! x : X, f x = y :=
  ⟨fun i => unique_of_type_equalizer _ _ (Classical.choice i), fun k =>
    ⟨typeEqualizerOfUnique f w k⟩⟩

/--
Definition of `equalizerLimit` / `equalizerLimit` 的定义

English:
definition equalizerLimit
  signature: : Limits.LimitCone (parallelPair g h) where
  body: Fork.ofι (↾(Subtype.val : { x : Y // g x = h x } -> Y))
    (by ext x; exact x.prop)
  isLimit :=
    Fork.IsLimit.mk' _ fun s =>
      ⟨↾fun i => ⟨s.ι i, by apply congr_hom s.condition i⟩, rfl, fun hm =>
        by ext x; exact Subtype.ext (by exact congr_hom hm x)⟩

中文:
定义 equalizerLimit
  签名: : Limits.LimitCone (parallelPair g h) where
  定义体: Fork.ofι (↾(Subtype.val : { x : Y // g x = h x } -> Y))
    (by ext x; exact x.prop)
  isLimit :=
    Fork.IsLimit.mk' _ fun s =>
      ⟨↾fun i => ⟨s.ι i, by apply congr_hom s.condition i⟩, rfl, fun hm =>
        by ext x; exact Subtype.ext (by exact congr_hom hm x)⟩

Depends on / 依赖: FintypeCat, FintypeCat.instCoeSort, Fork.of, Subtype, Subtype.val, instCoeSort
-/
def equalizerLimit : Limits.LimitCone (parallelPair g h) where
  cone := Fork.ofι (↾(Subtype.val : { x : Y // g x = h x } -> Y))
    (by ext x; exact x.prop)
  isLimit :=
    Fork.IsLimit.mk' _ fun s =>
      ⟨↾fun i => ⟨s.ι i, by apply congr_hom s.condition i⟩, rfl, fun hm =>
        by ext x; exact Subtype.ext (by exact congr_hom hm x)⟩

variable (g h)

/--
Definition of `equalizerIso` / `equalizerIso` 的定义

English:
definition equalizerIso
  signature: : equalizer g h ≅ { x : Y // g x = h x }
  body: limit.isoLimitCone equalizerLimit

@[elementwise (attr := simp)]

中文:
定义 equalizerIso
  签名: : equalizer g h ≅ { x : Y // g x = h x }
  定义体: limit.isoLimitCone equalizerLimit

@[elementwise (attr := simp)]

Depends on / 依赖: Matrix, equalizerLimit, isoLimitCone, limit.isoLimitCone
-/
noncomputable def equalizerIso : equalizer g h ≅ { x : Y // g x = h x } :=
  limit.isoLimitCone equalizerLimit

@[elementwise (attr := simp)]
/--
theorem `equalizerIso_hom_comp_subtype` / 定理 `equalizerIso_hom_comp_subtype`

English:
theorem equalizerIso_hom_comp_subtype
  proof: by
  rfl

@[elementwise (attr := simp)]

中文:
定理 equalizerIso_hom_comp_subtype
  证明: by
  rfl

@[elementwise (attr := simp)]
-/
theorem equalizerIso_hom_comp_subtype :
    (equalizerIso g h).hom ≫ ↾Subtype.val = equalizer.ι g h := by
  rfl

@[elementwise (attr := simp)]
/--
theorem `equalizerIso_inv_comp_ι` / 定理 `equalizerIso_inv_comp_ι`

English:
theorem equalizerIso_inv_comp_ι
  statement: (equalizerIso g h).inv ≫ equalizer.ι g h =
  proof: limit.isoLimitCone_inv_π equalizerLimit WalkingParallelPair.zero

中文:
定理 equalizerIso_inv_comp_ι
  结论: (equalizerIso g h).inv ≫ equalizer.ι g h =
  证明: limit.isoLimitCone_inv_π equalizerLimit WalkingParallelPair.zero

Depends on / 依赖: WalkingParallelPair, WalkingParallelPair.zero, equalizerLimit, limit.isoLimitCone_inv_
-/
theorem equalizerIso_inv_comp_ι : (equalizerIso g h).inv ≫ equalizer.ι g h =
    ↾Subtype.val :=
  limit.isoLimitCone_inv_π equalizerLimit WalkingParallelPair.zero

end CategoryTheory.Limits.Types
