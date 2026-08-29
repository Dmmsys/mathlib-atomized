/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsClosure
public import Mathlib.CategoryTheory.SmallRepresentatives
public import Mathlib.CategoryTheory.Comma.CardinalArrow

/-!
# Closure of a property of objects under colimits of bounded cardinality

In this file, given `P : ObjectProperty C` and `κ : Cardinal.{w}`,
we introduce the closure `P.colimitsCardinalClosure κ`
of `P` under colimits of shapes given by categories `J` such
that `Arrow J` is of cardinality `< κ`.

If `C` is locally `w`-small and `P` is essentially `w`-small,
we show that this closure `P.colimitsCardinalClosure κ` is
also essentially `w`-small.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C) (κ : Cardinal.{w})

/--
Definition of `colimitsCardinalClosure` / `colimitsCardinalClosure` 的定义

English:
definition colimitsCardinalClosure
  signature: : ObjectProperty C
  body: P.colimitsClosure (SmallCategoryCardinalLT.categoryFamily κ)

中文:
定义 colimitsCardinalClosure
  签名: : ObjectProperty C
  定义体: P.colimitsClosure (SmallCategoryCardinalLT.categoryFamily κ)

Depends on / 依赖: P.colimitsClosure, SmallCategoryCardinalLT, SmallCategoryCardinalLT.categoryFamily, categoryFamily, colimitsClosure
-/
def colimitsCardinalClosure : ObjectProperty C :=
  P.colimitsClosure (SmallCategoryCardinalLT.categoryFamily κ)

/--
lemma `le_colimitsCardinalClosure` / 引理 `le_colimitsCardinalClosure`

English:
lemma le_colimitsCardinalClosure
  statement: P <= P.colimitsCardinalClosure κ
  proof: P.le_colimitsClosure _

中文:
引理 le_colimitsCardinalClosure
  结论: P <= P.colimitsCardinalClosure κ
  证明: P.le_colimitsClosure _

Depends on / 依赖: P.le_colimitsClosure, le_colimitsClosure
-/
lemma le_colimitsCardinalClosure : P <= P.colimitsCardinalClosure κ :=
  P.le_colimitsClosure _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (P.colimitsCardinalClosure κ).IsClosedUnderIsomorphisms
  body: by
  dsimp [colimitsCardinalClosure]
  infer_instance

中文:
实例 :
  签名: (P.colimitsCardinalClosure κ).在同构下封闭
  定义体: by
  dsimp [colimitsCardinalClosure]
  infer_instance

Depends on / 依赖: colimitsCardinalClosure, infer_instance
-/
instance : (P.colimitsCardinalClosure κ).IsClosedUnderIsomorphisms := by
  dsimp [colimitsCardinalClosure]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ObjectProperty.EssentiallySmall.{w}
  signature: P] [LocallySmall.{w} C] :
  body: by
  dsimp [colimitsCardinalClosure]
  infer_instance

中文:
实例 [ObjectProperty.EssentiallySmall.{w}
  签名: P] [LocallySmall.{w} C] :
  定义体: by
  dsimp [colimitsCardinalClosure]
  infer_instance

Depends on / 依赖: colimitsCardinalClosure, infer_instance
-/
instance [ObjectProperty.EssentiallySmall.{w} P] [LocallySmall.{w} C] :
    ObjectProperty.EssentiallySmall.{w} (P.colimitsCardinalClosure κ) := by
  dsimp [colimitsCardinalClosure]
  infer_instance

instance (S : SmallCategoryCardinalLT κ) :
    (P.colimitsCardinalClosure κ).IsClosedUnderColimitsOfShape
      (SmallCategoryCardinalLT.categoryFamily κ S) := by
  dsimp [colimitsCardinalClosure]
  infer_instance

/--
lemma `isClosedUnderColimitsOfShape_colimitsCardinalClosure` / 引理 `isClosedUnderColimitsOfShape_colimitsCardinalClosure`

English:
lemma isClosedUnderColimitsOfShape_colimitsCardinalClosure
  proof: by
  obtain ⟨S, ⟨e⟩⟩ := SmallCategoryCardinalLT.exists_equivalence κ J hJ
  rw [isClosedUnderColimitsOfShape_iff_of_equivalence _ e.symm]
  infer_instance

中文:
引理 isClosedUnderColimitsOfShape_colimitsCardinalClosure
  证明: by
  obtain ⟨S, ⟨e⟩⟩ := SmallCategoryCardinalLT.exists_equivalence κ J hJ
  rw [isClosedUnderColimitsOfShape_iff_of_equivalence _ e.symm]
  infer_instance

Depends on / 依赖: SmallCategoryCardinalLT, SmallCategoryCardinalLT.exists_equivalence, e.symm, exists_equivalence, infer_instance, isClosedUnderColimitsOfShape_iff_of_equivalence
-/
lemma isClosedUnderColimitsOfShape_colimitsCardinalClosure
    (J : Type u') [Category.{v'} J] (hJ : HasCardinalLT (Arrow J) κ) :
    (P.colimitsCardinalClosure κ).IsClosedUnderColimitsOfShape J := by
  obtain ⟨S, ⟨e⟩⟩ := SmallCategoryCardinalLT.exists_equivalence κ J hJ
  rw [isClosedUnderColimitsOfShape_iff_of_equivalence _ e.symm]
  infer_instance

/--
lemma `colimitsCardinalClosure_le` / 引理 `colimitsCardinalClosure_le`

English:
lemma colimitsCardinalClosure_le
  statement: {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms]
  proof: by
  have (i : SmallCategoryCardinalLT κ) := hQ _ i.hasCardinalLT
  exact colimitsClosure_le h

中文:
引理 colimitsCardinalClosure_le
  结论: {Q : ObjectProperty C} [Q.在同构下封闭]
  证明: by
  have (i : SmallCategoryCardinalLT κ) := hQ _ i.hasCardinalLT
  exact colimitsClosure_le h

Depends on / 依赖: SmallCategoryCardinalLT, colimitsClosure_le, hasCardinalLT, i.hasCardinalLT
-/
lemma colimitsCardinalClosure_le {Q : ObjectProperty C} [Q.IsClosedUnderIsomorphisms]
    (hQ : forall (J : Type w) [SmallCategory J] (_ : HasCardinalLT (Arrow J) κ),
      Q.IsClosedUnderColimitsOfShape J) (h : P <= Q) :
    P.colimitsCardinalClosure κ <= Q := by
  have (i : SmallCategoryCardinalLT κ) := hQ _ i.hasCardinalLT
  exact colimitsClosure_le h

section

open Limits

/--
Instance `isStableUnderRetracts_colimitsCardinalClosure` / 实例 `isStableUnderRetracts_colimitsCardinalClosure`

English:
instance isStableUnderRetracts_colimitsCardinalClosure
  signature: [Fact κ.IsRegular]
  body: by
  have := P.isClosedUnderColimitsOfShape_colimitsCardinalClosure κ
    WalkingParallelPair (HasCardinalLT.of_le (by
      simp only [hasCardinalLT_aleph0_iff]
      infer_instance)
    (Cardinal.IsRegular.aleph0_le Fact.out))
  infer_instance

中文:
实例 isStableUnderRetracts_colimitsCardinalClosure
  签名: [Fact κ.是正则]
  定义体: by
  have := P.isClosedUnderColimitsOfShape_colimitsCardinalClosure κ
    WalkingParallelPair (HasCardinalLT.of_le (by
      simp only [hasCardinalLT_aleph0_iff]
      infer_instance)
    (Cardinal.IsRegular.aleph0_le Fact.out))
  infer_instance

Depends on / 依赖: Cardinal, Cardinal.IsRegular.aleph0_le, Fact.out, HasCardinalLT, HasCardinalLT.of_le, IsRegular, P.isClosedUnderColimitsOfShape_colimitsCardinalClosure, WalkingParallelPair, aleph0_le, hasCardinalLT_aleph0_iff, infer_instance, isClosedUnderColimitsOfShape_colimitsCardinalClosure, of_le
-/
instance isStableUnderRetracts_colimitsCardinalClosure [Fact κ.IsRegular] :
    (P.colimitsCardinalClosure κ).IsStableUnderRetracts := by
  have := P.isClosedUnderColimitsOfShape_colimitsCardinalClosure κ
    WalkingParallelPair (HasCardinalLT.of_le (by
      simp only [hasCardinalLT_aleph0_iff]
      infer_instance)
    (Cardinal.IsRegular.aleph0_le Fact.out))
  infer_instance

end

end CategoryTheory.ObjectProperty
