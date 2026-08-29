/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Join.Basic
public import Mathlib.CategoryTheory.Sums.Basic

/-!
# Embedding of `C ⊕ D` into `C ⋆ D`

This file constructs a canonical functor `Join.fromSum` from `C ⊕ D` to `C ⋆ D` and gives
its characterization in terms of the canonical inclusions.
We also provide `Faithful` and `EssSurj` instances on this functor.

-/

@[expose] public section

namespace CategoryTheory.Join

variable (C D : Type*) [Category* C] [Category* D]

/-- The canonical functor from the sum to the join.
It sends `inl c` to `left c` and `inr d` to `right d`. -/
@[simps! obj] -- Maps get characterized w.r.t. the inclusions below
/--
Definition of `fromSum` / `fromSum` 的定义

English:
definition fromSum
  signature: : C oplus D ⥤ C ⋆ D
  body: (inclLeft C D).sum' inclRight C D

中文:
定义 fromSum
  签名: : C oplus D ⥤ C ⋆ D
  定义体: (inclLeft C D).sum' inclRight C D

Depends on / 依赖: inclLeft, inclRight
-/
def fromSum : C oplus D ⥤ C ⋆ D := (inclLeft C D).sum' inclRight C D

variable {C} in
@[simp]
/--
lemma `fromSum_map_inl` / 引理 `fromSum_map_inl`

English:
lemma fromSum_map_inl
  given: {c c' : C} (f : c ⟶ c')
  proof: rfl

中文:
引理 fromSum_map_inl
  条件: {c c' : C} (f : c ⟶ c')
  证明: rfl
-/
lemma fromSum_map_inl {c c' : C} (f : c ⟶ c') :
    (fromSum C D).map ((Sum.inl_ C D).map f) = (inclLeft C D).map f :=
  rfl

variable {D} in
@[simp]
/--
lemma `fromSum_map_inr` / 引理 `fromSum_map_inr`

English:
lemma fromSum_map_inr
  given: {d d' : D} (f : d ⟶ d')
  proof: rfl

中文:
引理 fromSum_map_inr
  条件: {d d' : D} (f : d ⟶ d')
  证明: rfl
-/
lemma fromSum_map_inr {d d' : D} (f : d ⟶ d') :
    (fromSum C D).map ((Sum.inr_ C D).map f) = (inclRight C D).map f :=
  rfl

/-- Characterization of `fromSum` with respect to the left inclusion. -/
@[simps! hom_app inv_app]
/--
Definition of `inlCompFromSum` / `inlCompFromSum` 的定义

English:
definition inlCompFromSum
  signature: : Sum.inl_ C D ⋙ fromSum C D ≅ inclLeft C D
  body: Functor.inlCompSum' _ _

中文:
定义 inlCompFromSum
  签名: : Sum.inl_ C D ⋙ fromSum C D ≅ inclLeft C D
  定义体: Functor.inlCompSum' _ _

Depends on / 依赖: Functor, Functor.inlCompSum, inlCompSum
-/
def inlCompFromSum : Sum.inl_ C D ⋙ fromSum C D ≅ inclLeft C D := Functor.inlCompSum' _ _

/-- Characterization of `fromSum` with respect to the right inclusion. -/
@[simps! hom_app inv_app]
/--
Definition of `inrCompFromSum` / `inrCompFromSum` 的定义

English:
definition inrCompFromSum
  signature: : Sum.inr_ C D ⋙ fromSum C D ≅ inclRight C D
  body: Functor.inrCompSum' _ _

中文:
定义 inrCompFromSum
  签名: : Sum.inr_ C D ⋙ fromSum C D ≅ inclRight C D
  定义体: Functor.inrCompSum' _ _

Depends on / 依赖: Functor, Functor.inrCompSum, inrCompSum
-/
def inrCompFromSum : Sum.inr_ C D ⋙ fromSum C D ≅ inclRight C D := Functor.inrCompSum' _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (fromSum C D).EssSurj

中文:
实例 :
  签名: (fromSum C D).EssSurj
-/
instance : (fromSum C D).EssSurj where
  mem_essImage
    | left c => Functor.obj_mem_essImage _ (Sum.inl c)
    | right d => Functor.obj_mem_essImage _ (Sum.inr d)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (fromSum C D).Faithful
  body: by
    cases h <;> cases h'
    all_goals
      simp only [fromSum_map_inl, fromSum_map_inr] at heq
      simp [Functor.map_injective _ heq]

中文:
实例 :
  签名: (fromSum C D).Faithful
  定义体: by
    cases h <;> cases h'
    all_goals
      simp only [fromSum_map_inl, fromSum_map_inr] at heq
      simp [Functor.map_injective _ heq]

Depends on / 依赖: Functor, Functor.map_injective, all_goals, fromSum_map_inl, fromSum_map_inr, map_injective
-/
instance : (fromSum C D).Faithful where
  map_injective {x y} h h' heq := by
    cases h <;> cases h'
    all_goals
      simp only [fromSum_map_inl, fromSum_map_inr] at heq
      simp [Functor.map_injective _ heq]

end CategoryTheory.Join
