/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Morphism properties from object properties

Given two object properties `P` and `Q`, we introduce a morphism property
`ofObjectProperty P Q`, given by all morphisms whose source satisfies `P` and
target satisfies `Q`.

-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category* C]

/--
Definition of `ofObjectProperty` / `ofObjectProperty` 的定义

English:
definition ofObjectProperty
  signature: (P Q : ObjectProperty C)
  body: fun X Y _ => P X ∧ Q Y

中文:
定义 ofObjectProperty
  签名: (P Q : ObjectProperty C)
  定义体: fun X Y _ => P X ∧ Q Y
-/
def ofObjectProperty (P Q : ObjectProperty C) : MorphismProperty C := fun X Y _ => P X ∧ Q Y

variable (P Q : ObjectProperty C)

/--
lemma `ofObjectProperty_iff` / 引理 `ofObjectProperty_iff`

English:
lemma ofObjectProperty_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: Iff.rfl

中文:
引理 ofObjectProperty_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma ofObjectProperty_iff {X Y : C} (f : X ⟶ Y) :
    ofObjectProperty P Q f ↔ P X ∧ Q Y := Iff.rfl

variable {P} in
/--
lemma `monotone_ofObjectProperty_left` / 引理 `monotone_ofObjectProperty_left`

English:
lemma monotone_ofObjectProperty_left
  given: {P' : ObjectProperty C} (h : P <= P')
  proof: by
  intro _ _ _ ⟨hX, hY⟩
  exact ⟨h _ hX, hY⟩

中文:
引理 monotone_ofObjectProperty_left
  条件: {P' : ObjectProperty C} (h : P <= P')
  证明: by
  intro _ _ _ ⟨hX, hY⟩
  exact ⟨h _ hX, hY⟩
-/
lemma monotone_ofObjectProperty_left {P' : ObjectProperty C} (h : P <= P') :
    ofObjectProperty P Q <= ofObjectProperty P' Q := by
  intro _ _ _ ⟨hX, hY⟩
  exact ⟨h _ hX, hY⟩

variable {Q} in
/--
lemma `monotone_ofObjectProperty_right` / 引理 `monotone_ofObjectProperty_right`

English:
lemma monotone_ofObjectProperty_right
  given: {Q' : ObjectProperty C} (h : Q <= Q')
  proof: by
  intro _ _ _ ⟨hX, hY⟩
  exact ⟨hX, h _ hY⟩

中文:
引理 monotone_ofObjectProperty_right
  条件: {Q' : ObjectProperty C} (h : Q <= Q')
  证明: by
  intro _ _ _ ⟨hX, hY⟩
  exact ⟨hX, h _ hY⟩
-/
lemma monotone_ofObjectProperty_right {Q' : ObjectProperty C} (h : Q <= Q') :
    ofObjectProperty P Q <= ofObjectProperty P Q' := by
  intro _ _ _ ⟨hX, hY⟩
  exact ⟨hX, h _ hY⟩

/--
lemma `ofObjectProperty_inverseImage` / 引理 `ofObjectProperty_inverseImage`

English:
lemma ofObjectProperty_inverseImage
  given: {D : Type*} [Category* D] (F : D ⥤ C)
  proof: by
  rfl

中文:
引理 ofObjectProperty_inverseImage
  条件: {D : 类型} [范畴* D] (F : D ⥤ C)
  证明: by
  rfl
-/
lemma ofObjectProperty_inverseImage {D : Type*} [Category* D] (F : D ⥤ C) :
    ofObjectProperty (P.inverseImage F) (Q.inverseImage F) =
    (ofObjectProperty P Q).inverseImage F := by
  rfl

/--
lemma `ofObjectProperty_map_le` / 引理 `ofObjectProperty_map_le`

English:
lemma ofObjectProperty_map_le
  given: {D : Type*} [Category* D] (F : C ⥤ D)
  proof: by
  intro X Y f ⟨X', Y', f', ⟨hX', hY'⟩, ⟨i⟩⟩
  exact ⟨⟨X', hX', ⟨Comma.leftIso i⟩⟩, ⟨Y', hY', ⟨Comma.rightIso i⟩⟩⟩

中文:
引理 ofObjectProperty_map_le
  条件: {D : 类型} [范畴* D] (F : C ⥤ D)
  证明: by
  intro X Y f ⟨X', Y', f', ⟨hX', hY'⟩, ⟨i⟩⟩
  exact ⟨⟨X', hX', ⟨Comma.leftIso i⟩⟩, ⟨Y', hY', ⟨Comma.rightIso i⟩⟩⟩

Depends on / 依赖: Comma.leftIso, Comma.rightIso, leftIso, rightIso
-/
lemma ofObjectProperty_map_le {D : Type*} [Category* D] (F : C ⥤ D) :
    (ofObjectProperty P Q).map F <= ofObjectProperty (P.map F) (Q.map F) := by
  intro X Y f ⟨X', Y', f', ⟨hX', hY'⟩, ⟨i⟩⟩
  exact ⟨⟨X', hX', ⟨Comma.leftIso i⟩⟩, ⟨Y', hY', ⟨Comma.rightIso i⟩⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderIsomorphisms]
  signature: : (ofObjectProperty P Q).RespectsLeft (isomorphisms C) where
  body: by
    intro X Y Z i hi f ⟨hY, hZ⟩
    rw [isomorphisms.iff] at hi
    exact ⟨(P.prop_iff_of_isIso i).mpr hY, hZ⟩

中文:
实例 [P.在同构下封闭]
  签名: : (ofObjectProperty P Q).RespectsLeft (isomorphisms C) where
  定义体: by
    intro X Y Z i hi f ⟨hY, hZ⟩
    rw [isomorphisms.iff] at hi
    exact ⟨(P.prop_iff_of_isIso i).mpr hY, hZ⟩

Depends on / 依赖: P.prop_iff_of_isIso, isomorphisms, isomorphisms.iff, prop_iff_of_isIso
-/
instance [P.IsClosedUnderIsomorphisms] : (ofObjectProperty P Q).RespectsLeft (isomorphisms C) where
  precomp := by
    intro X Y Z i hi f ⟨hY, hZ⟩
    rw [isomorphisms.iff] at hi
    exact ⟨(P.prop_iff_of_isIso i).mpr hY, hZ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Q.IsClosedUnderIsomorphisms]
  signature: : (ofObjectProperty P Q).RespectsRight (isomorphisms C) where
  body: by
    intro X Y Z i hi f ⟨hY, hZ⟩
    rw [isomorphisms.iff] at hi
    exact ⟨hY, (Q.prop_iff_of_isIso i).mp hZ⟩

中文:
实例 [Q.在同构下封闭]
  签名: : (ofObjectProperty P Q).RespectsRight (isomorphisms C) where
  定义体: by
    intro X Y Z i hi f ⟨hY, hZ⟩
    rw [isomorphisms.iff] at hi
    exact ⟨hY, (Q.prop_iff_of_isIso i).mp hZ⟩

Depends on / 依赖: Q.prop_iff_of_isIso, isomorphisms, isomorphisms.iff, prop_iff_of_isIso
-/
instance [Q.IsClosedUnderIsomorphisms] : (ofObjectProperty P Q).RespectsRight (isomorphisms C) where
  postcomp := by
    intro X Y Z i hi f ⟨hY, hZ⟩
    rw [isomorphisms.iff] at hi
    exact ⟨hY, (Q.prop_iff_of_isIso i).mp hZ⟩

end CategoryTheory.MorphismProperty
