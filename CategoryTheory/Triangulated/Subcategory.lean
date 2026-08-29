/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Triangulated subcategories

In this file, given a pretriangulated category `C` and `P : ObjectProperty C`,
we introduce a typeclass `P.IsTriangulated` to express that `P`
is a triangulated subcategory of `C`. When `P` is a triangulated
subcategory, we introduce a class of morphisms `P.trW : MorphismProperty C`
consisting of the morphisms whose "cone" belongs to `P` (up to isomorphisms),
and we show that it has both calculus of left and right fractions.

We also show that `P.FullSubcategory` is equipped with a pretriangulated structure,
which is triangulated if `C` is.

## Implementation notes

In the definition of `P.IsTriangulated`, we do not assume that the predicate
on objects is closed under isomorphisms (i.e. that the subcategory is "strictly full").
Part of the theory would be more convenient under this stronger assumption
(e.g. the subtype of `ObjectProperty C` consisting of triangulated subcategories
would be a lattice), but some applications require this:
for example, the subcategory of bounded below complexes in the homotopy category
of an additive category is not closed under isomorphisms.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Category Limits Preadditive ZeroObject Pretriangulated Triangulated

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C Int]
  [Preadditive C] [forall (n : Int), (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D Int]
  [forall (n : Int), (shiftFunctor D n).Additive] [Pretriangulated D]
  {E : Type*} [Category* E] [HasShift E Int]

namespace ObjectProperty

variable (P : ObjectProperty C)

/--
Definition of `IsTriangulatedClosed₁` / `IsTriangulatedClosed₁` 的定义

English:
class IsTriangulatedClosed₁
  parameters: : Prop where
  axioms and operations (1):
    - ext₁'((T : Triangle C) (_ : T in distTriang C)) : P T.obj₂ -> P T.obj₃ -> P.isoClosure T.obj₁

中文:
类 是TriangulatedClosed₁
  参数: : 命题 where
  公理与运算 (1 个):
    - ext₁'((T : Triangle C) (_ : T in distTriang C)) : P T.obj₂ -> P T.obj₃ -> P.isoClosure T.obj₁
-/
class IsTriangulatedClosed₁ : Prop where
  ext₁' (T : Triangle C) (_ : T in distTriang C) : P T.obj₂ -> P T.obj₃ -> P.isoClosure T.obj₁

/--
Definition of `IsTriangulatedClosed₂` / `IsTriangulatedClosed₂` 的定义

English:
class IsTriangulatedClosed₂
  parameters: : Prop where
  axioms and operations (1):
    - ext₂'((T : Triangle C) (_ : T in distTriang C)) : P T.obj₁ -> P T.obj₃ -> P.isoClosure T.obj₂

中文:
类 是TriangulatedClosed₂
  参数: : 命题 where
  公理与运算 (1 个):
    - ext₂'((T : Triangle C) (_ : T in distTriang C)) : P T.obj₁ -> P T.obj₃ -> P.isoClosure T.obj₂
-/
class IsTriangulatedClosed₂ : Prop where
  ext₂' (T : Triangle C) (_ : T in distTriang C) : P T.obj₁ -> P T.obj₃ -> P.isoClosure T.obj₂

/--
Definition of `IsTriangulatedClosed₃` / `IsTriangulatedClosed₃` 的定义

English:
class IsTriangulatedClosed₃
  parameters: : Prop where
  axioms and operations (1):
    - ext₃'((T : Triangle C) (_ : T in distTriang C)) : P T.obj₁ -> P T.obj₂ -> P.isoClosure T.obj₃

中文:
类 是TriangulatedClosed₃
  参数: : 命题 where
  公理与运算 (1 个):
    - ext₃'((T : Triangle C) (_ : T in distTriang C)) : P T.obj₁ -> P T.obj₂ -> P.isoClosure T.obj₃
-/
class IsTriangulatedClosed₃ : Prop where
  ext₃' (T : Triangle C) (_ : T in distTriang C) : P T.obj₁ -> P T.obj₂ -> P.isoClosure T.obj₃

/--
lemma `ext_of_isTriangulatedClosed₁'` / 引理 `ext_of_isTriangulatedClosed₁'`

English:
lemma ext_of_isTriangulatedClosed₁'
  proof: IsTriangulatedClosed₁.ext₁' T hT h₂ h₃

中文:
引理 ext_of_isTriangulatedClosed₁'
  证明: IsTriangulatedClosed₁.ext₁' T hT h₂ h₃
-/
lemma ext_of_isTriangulatedClosed₁'
    [P.IsTriangulatedClosed₁] (T : Triangle C) (hT : T in distTriang C)
    (h₂ : P T.obj₂) (h₃ : P T.obj₃) : P.isoClosure T.obj₁ :=
  IsTriangulatedClosed₁.ext₁' T hT h₂ h₃

/--
lemma `ext_of_isTriangulatedClosed₂'` / 引理 `ext_of_isTriangulatedClosed₂'`

English:
lemma ext_of_isTriangulatedClosed₂'
  proof: IsTriangulatedClosed₂.ext₂' T hT h₁ h₃

中文:
引理 ext_of_isTriangulatedClosed₂'
  证明: IsTriangulatedClosed₂.ext₂' T hT h₁ h₃
-/
lemma ext_of_isTriangulatedClosed₂'
    [P.IsTriangulatedClosed₂] (T : Triangle C) (hT : T in distTriang C)
    (h₁ : P T.obj₁) (h₃ : P T.obj₃) : P.isoClosure T.obj₂ :=
  IsTriangulatedClosed₂.ext₂' T hT h₁ h₃

/--
lemma `ext_of_isTriangulatedClosed₃'` / 引理 `ext_of_isTriangulatedClosed₃'`

English:
lemma ext_of_isTriangulatedClosed₃'
  proof: IsTriangulatedClosed₃.ext₃' T hT h₁ h₂

中文:
引理 ext_of_isTriangulatedClosed₃'
  证明: IsTriangulatedClosed₃.ext₃' T hT h₁ h₂
-/
lemma ext_of_isTriangulatedClosed₃'
    [P.IsTriangulatedClosed₃] (T : Triangle C) (hT : T in distTriang C)
    (h₁ : P T.obj₁) (h₂ : P T.obj₂) : P.isoClosure T.obj₃ :=
  IsTriangulatedClosed₃.ext₃' T hT h₁ h₂

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `distinguished_cocone_triangle` / 引理 `distinguished_cocone_triangle`

English:
lemma distinguished_cocone_triangle
  statement: [P.IsTriangulatedClosed₃]
  proof: by
  obtain ⟨Z, b, c, h⟩ := distinguished_cocone_triangle a
  obtain ⟨Z', hZ', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₃' _ h hX hY
  exact ⟨Z', hZ', b ≫ e.hom, e.inv ≫ c, isomorphic_distinguished _ h _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm )⟩

中文:
引理 distinguished_cocone_triangle
  结论: [P.是TriangulatedClosed₃]
  证明: by
  obtain ⟨Z, b, c, h⟩ := distinguished_cocone_triangle a
  obtain ⟨Z', hZ', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₃' _ h hX hY
  exact ⟨Z', hZ', b ≫ e.hom, e.inv ≫ c, isomorphic_distinguished _ h _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm )⟩
-/
protected lemma distinguished_cocone_triangle [P.IsTriangulatedClosed₃]
    {X Y : C} (a : X ⟶ Y) (hX : P X) (hY : P Y) :
    exists (Z : C) (_ : P Z) (b : Y ⟶ Z) (c : Z ⟶ X⟦(1 : Int)⟧), Triangle.mk a b c in distTriang _ := by
  obtain ⟨Z, b, c, h⟩ := distinguished_cocone_triangle a
  obtain ⟨Z', hZ', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₃' _ h hX hY
  exact ⟨Z', hZ', b ≫ e.hom, e.inv ≫ c, isomorphic_distinguished _ h _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm )⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `distinguished_cocone_triangle₁` / 引理 `distinguished_cocone_triangle₁`

English:
lemma distinguished_cocone_triangle₁
  statement: [P.IsTriangulatedClosed₁]
  proof: by
  obtain ⟨X, a, c, h⟩ := distinguished_cocone_triangle₁ b
  obtain ⟨X', hX', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₁' _ h hY hZ
  exact ⟨X', hX', e.inv ≫ a, c ≫ e.hom⟦1⟧', isomorphic_distinguished _ h _
    (Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _))⟩

中文:
引理 distinguished_cocone_triangle₁
  结论: [P.是TriangulatedClosed₁]
  证明: by
  obtain ⟨X, a, c, h⟩ := distinguished_cocone_triangle₁ b
  obtain ⟨X', hX', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₁' _ h hY hZ
  exact ⟨X', hX', e.inv ≫ a, c ≫ e.hom⟦1⟧', isomorphic_distinguished _ h _
    (Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _))⟩
-/
protected lemma distinguished_cocone_triangle₁ [P.IsTriangulatedClosed₁]
    {Y Z : C} (b : Y ⟶ Z) (hY : P Y) (hZ : P Z) :
    exists (X : C) (_ : P X) (a : X ⟶ Y) (c : Z ⟶ X⟦(1 : Int)⟧), Triangle.mk a b c in distTriang _ := by
  obtain ⟨X, a, c, h⟩ := distinguished_cocone_triangle₁ b
  obtain ⟨X', hX', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₁' _ h hY hZ
  exact ⟨X', hX', e.inv ≫ a, c ≫ e.hom⟦1⟧', isomorphic_distinguished _ h _
    (Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _))⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `distinguished_cocone_triangle₂` / 引理 `distinguished_cocone_triangle₂`

English:
lemma distinguished_cocone_triangle₂
  statement: [P.IsTriangulatedClosed₂]
  proof: by
  obtain ⟨Y, a, b, h⟩ := distinguished_cocone_triangle₂ c
  obtain ⟨Y', hY', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₂' _ h hX hZ
  exact ⟨Y', hY', a ≫ e.hom, e.inv ≫ b, isomorphic_distinguished _ h _
    (Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _))⟩

中文:
引理 distinguished_cocone_triangle₂
  结论: [P.是TriangulatedClosed₂]
  证明: by
  obtain ⟨Y, a, b, h⟩ := distinguished_cocone_triangle₂ c
  obtain ⟨Y', hY', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₂' _ h hX hZ
  exact ⟨Y', hY', a ≫ e.hom, e.inv ≫ b, isomorphic_distinguished _ h _
    (Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _))⟩
-/
protected lemma distinguished_cocone_triangle₂ [P.IsTriangulatedClosed₂]
    {X Z : C} (c : Z ⟶ X⟦(1 : Int)⟧) (hX : P X) (hZ : P Z) :
    exists (Y : C) (_ : P Y) (a : X ⟶ Y) (b : Y ⟶ Z), Triangle.mk a b c in distTriang _ := by
  obtain ⟨Y, a, b, h⟩ := distinguished_cocone_triangle₂ c
  obtain ⟨Y', hY', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₂' _ h hX hZ
  exact ⟨Y', hY', a ≫ e.hom, e.inv ≫ b, isomorphic_distinguished _ h _
    (Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _))⟩

/--
lemma `ext_of_isTriangulatedClosed₁` / 引理 `ext_of_isTriangulatedClosed₁`

English:
lemma ext_of_isTriangulatedClosed₁
  proof: by
  simpa only [isoClosure_eq_self] using P.ext_of_isTriangulatedClosed₁' T hT h₂ h₃

中文:
引理 ext_of_isTriangulatedClosed₁
  证明: by
  simpa only [isoClosure_eq_self] using P.ext_of_isTriangulatedClosed₁' T hT h₂ h₃

Depends on / 依赖: P.ext_of_isTriangulatedClosed, isoClosure_eq_self
-/
lemma ext_of_isTriangulatedClosed₁
    [P.IsTriangulatedClosed₁] [P.IsClosedUnderIsomorphisms]
    (T : Triangle C) (hT : T in distTriang C)
    (h₂ : P T.obj₂) (h₃ : P T.obj₃) : P T.obj₁ := by
  simpa only [isoClosure_eq_self] using P.ext_of_isTriangulatedClosed₁' T hT h₂ h₃

/--
lemma `ext_of_isTriangulatedClosed₂` / 引理 `ext_of_isTriangulatedClosed₂`

English:
lemma ext_of_isTriangulatedClosed₂
  proof: by
  simpa only [isoClosure_eq_self] using P.ext_of_isTriangulatedClosed₂' T hT h₁ h₃

中文:
引理 ext_of_isTriangulatedClosed₂
  证明: by
  simpa only [isoClosure_eq_self] using P.ext_of_isTriangulatedClosed₂' T hT h₁ h₃

Depends on / 依赖: P.ext_of_isTriangulatedClosed, isoClosure_eq_self
-/
lemma ext_of_isTriangulatedClosed₂
    [P.IsTriangulatedClosed₂] [P.IsClosedUnderIsomorphisms]
    (T : Triangle C) (hT : T in distTriang C)
    (h₁ : P T.obj₁) (h₃ : P T.obj₃) : P T.obj₂ := by
  simpa only [isoClosure_eq_self] using P.ext_of_isTriangulatedClosed₂' T hT h₁ h₃

/--
lemma `ext_of_isTriangulatedClosed₃` / 引理 `ext_of_isTriangulatedClosed₃`

English:
lemma ext_of_isTriangulatedClosed₃
  proof: by
  simpa only [isoClosure_eq_self] using P.ext_of_isTriangulatedClosed₃' T hT h₁ h₂

中文:
引理 ext_of_isTriangulatedClosed₃
  证明: by
  simpa only [isoClosure_eq_self] using P.ext_of_isTriangulatedClosed₃' T hT h₁ h₂

Depends on / 依赖: P.ext_of_isTriangulatedClosed, isoClosure_eq_self
-/
lemma ext_of_isTriangulatedClosed₃
    [P.IsTriangulatedClosed₃] [P.IsClosedUnderIsomorphisms]
    (T : Triangle C) (hT : T in distTriang C)
    (h₁ : P T.obj₁) (h₂ : P T.obj₂) : P T.obj₃ := by
  simpa only [isoClosure_eq_self] using P.ext_of_isTriangulatedClosed₃' T hT h₁ h₂

variable {P}

/--
lemma `IsTriangulatedClosed₁.mk'` / 引理 `IsTriangulatedClosed₁.mk'`

English:
lemma IsTriangulatedClosed₁.mk'
  statement: [P.IsClosedUnderIsomorphisms]
  proof: by simpa only [isoClosure_eq_self] using hP

中文:
引理 是TriangulatedClosed₁.mk'
  结论: [P.在同构下封闭]
  证明: by simpa only [isoClosure_eq_self] using hP

Depends on / 依赖: isoClosure_eq_self
-/
lemma IsTriangulatedClosed₁.mk' [P.IsClosedUnderIsomorphisms]
    (hP : forall (T : Triangle C) (_ : T in distTriang C)
      (_ : P T.obj₂) (_ : P T.obj₃), P T.obj₁) : P.IsTriangulatedClosed₁ where
  ext₁' := by simpa only [isoClosure_eq_self] using hP

/--
lemma `IsTriangulatedClosed₂.mk'` / 引理 `IsTriangulatedClosed₂.mk'`

English:
lemma IsTriangulatedClosed₂.mk'
  statement: [P.IsClosedUnderIsomorphisms]
  proof: by simpa only [isoClosure_eq_self] using hP

中文:
引理 是TriangulatedClosed₂.mk'
  结论: [P.在同构下封闭]
  证明: by simpa only [isoClosure_eq_self] using hP

Depends on / 依赖: isoClosure_eq_self
-/
lemma IsTriangulatedClosed₂.mk' [P.IsClosedUnderIsomorphisms]
    (hP : forall (T : Triangle C) (_ : T in distTriang C)
      (_ : P T.obj₁) (_ : P T.obj₃), P T.obj₂) : P.IsTriangulatedClosed₂ where
  ext₂' := by simpa only [isoClosure_eq_self] using hP

/--
lemma `IsTriangulatedClosed₃.mk'` / 引理 `IsTriangulatedClosed₃.mk'`

English:
lemma IsTriangulatedClosed₃.mk'
  statement: [P.IsClosedUnderIsomorphisms]
  proof: by simpa only [isoClosure_eq_self] using hP

中文:
引理 是TriangulatedClosed₃.mk'
  结论: [P.在同构下封闭]
  证明: by simpa only [isoClosure_eq_self] using hP

Depends on / 依赖: isoClosure_eq_self
-/
lemma IsTriangulatedClosed₃.mk' [P.IsClosedUnderIsomorphisms]
    (hP : forall (T : Triangle C) (_ : T in distTriang C)
      (_ : P T.obj₁) (_ : P T.obj₂), P T.obj₃) : P.IsTriangulatedClosed₃ where
  ext₃' := by simpa only [isoClosure_eq_self] using hP

/--
lemma `IsTriangulatedClosed₂.of_isTriangulatedClosed₃` / 引理 `IsTriangulatedClosed₂.of_isTriangulatedClosed₃`

English:
lemma IsTriangulatedClosed₂.of_isTriangulatedClosed₃
  proof: P.ext_of_isTriangulatedClosed₃' _ (inv_rot_of_distTriang _ hT)
      (P.le_shift _ _ h₃) h₁

中文:
引理 是TriangulatedClosed₂.of_isTriangulatedClosed₃
  证明: P.ext_of_isTriangulatedClosed₃' _ (inv_rot_of_distTriang _ hT)
      (P.le_shift _ _ h₃) h₁

Depends on / 依赖: P.ext_of_isTriangulatedClosed, P.le_shift, inv_rot_of_distTriang, le_shift
-/
lemma IsTriangulatedClosed₂.of_isTriangulatedClosed₃
    [P.IsTriangulatedClosed₃] [P.IsStableUnderShift Int] :
    P.IsTriangulatedClosed₂ where
  ext₂' _ hT h₁ h₃ :=
    P.ext_of_isTriangulatedClosed₃' _ (inv_rot_of_distTriang _ hT)
      (P.le_shift _ _ h₃) h₁

variable (P)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsTriangulatedClosed₂]
  signature: : P.isoClosure.IsTriangulatedClosed₂ where
  body: by
    rintro T hT ⟨X₁, h₁, ⟨e₁⟩⟩ ⟨X₃, h₃, ⟨e₃⟩⟩
    exact ObjectProperty.le_isoClosure _ _
      (P.ext_of_isTriangulatedClosed₂'
        (Triangle.mk (e₁.inv ≫ T.mor₁) (T.mor₂ ≫ e₃.hom) (e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦1⟧'))
      (isomorphic_distinguished _ hT _
        (Triangle.isoMk _ _ e₁.symm (Iso.refl _) e₃.symm (by simp) (by simp) (by
          dsimp
          simp only [assoc, ← Functor.map_comp, e₁.hom_inv_id,
            Functor.map_id, comp_id]))) h₁ h₃)

中文:
实例 [P.是TriangulatedClosed₂]
  签名: : P.isoClosure.是TriangulatedClosed₂ where
  定义体: by
    rintro T hT ⟨X₁, h₁, ⟨e₁⟩⟩ ⟨X₃, h₃, ⟨e₃⟩⟩
    exact ObjectProperty.le_isoClosure _ _
      (P.ext_of_isTriangulatedClosed₂'
        (Triangle.mk (e₁.inv ≫ T.mor₁) (T.mor₂ ≫ e₃.hom) (e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦1⟧'))
      (isomorphic_distinguished _ hT _
        (Triangle.isoMk _ _ e₁.symm (Iso.refl _) e₃.symm (by simp) (by simp) (by
          dsimp
          simp only [assoc, ← Functor.map_comp, e₁.hom_inv_id,
            Functor.map_id, comp_id]))) h₁ h₃)

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_id, Iso.refl, ObjectProperty, ObjectProperty.le_isoClosure, P.ext_of_isTriangulatedClosed, T.mor, Triangle, Triangle.isoMk, Triangle.mk, comp_id, hom_inv_id, isomorphic_distinguished, le_isoClosure, map_comp, map_id
-/
instance [P.IsTriangulatedClosed₂] : P.isoClosure.IsTriangulatedClosed₂ where
  ext₂' := by
    rintro T hT ⟨X₁, h₁, ⟨e₁⟩⟩ ⟨X₃, h₃, ⟨e₃⟩⟩
    exact ObjectProperty.le_isoClosure _ _
      (P.ext_of_isTriangulatedClosed₂'
        (Triangle.mk (e₁.inv ≫ T.mor₁) (T.mor₂ ≫ e₃.hom) (e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦1⟧'))
      (isomorphic_distinguished _ hT _
        (Triangle.isoMk _ _ e₁.symm (Iso.refl _) e₃.symm (by simp) (by simp) (by
          dsimp
          simp only [assoc, ← Functor.map_comp, e₁.hom_inv_id,
            Functor.map_id, comp_id]))) h₁ h₃)

/--
Definition of `IsTriangulated` / `IsTriangulated` 的定义

English:
class IsTriangulated
  parameters: : Prop extends P.ContainsZero, P.IsStableUnderShift Int,
  extends: P.ContainsZero, P.IsStableUnderShift Int, 
  (no additional axioms)

中文:
类 是三角
  参数: : 命题 extends P.余ntainsZero, P.是StableUnderShift 整数,
  继承: P.余ntainsZero, P.是StableUnderShift 整数, 
  (无附加公理)
-/
protected class IsTriangulated : Prop extends P.ContainsZero, P.IsStableUnderShift Int,
    P.IsTriangulatedClosed₂ where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsTriangulated]
  signature: : P.IsTriangulatedClosed₁ where
  body: P.ext_of_isTriangulatedClosed₂' _ (inv_rot_of_distTriang _ hT) (P.le_shift _ _ h₃) h₂

中文:
实例 [P.是三角]
  签名: : P.是TriangulatedClosed₁ where
  定义体: P.ext_of_isTriangulatedClosed₂' _ (inv_rot_of_distTriang _ hT) (P.le_shift _ _ h₃) h₂

Depends on / 依赖: P.ext_of_isTriangulatedClosed, P.le_shift, inv_rot_of_distTriang, le_shift
-/
instance [P.IsTriangulated] : P.IsTriangulatedClosed₁ where
  ext₁' _ hT h₂ h₃ :=
    P.ext_of_isTriangulatedClosed₂' _ (inv_rot_of_distTriang _ hT) (P.le_shift _ _ h₃) h₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsTriangulated]
  signature: : P.IsTriangulatedClosed₃ where
  body: P.ext_of_isTriangulatedClosed₂' _ (rot_of_distTriang _ hT) h₂ (P.le_shift _ _ h₁)

中文:
实例 [P.是三角]
  签名: : P.是TriangulatedClosed₃ where
  定义体: P.ext_of_isTriangulatedClosed₂' _ (rot_of_distTriang _ hT) h₂ (P.le_shift _ _ h₁)

Depends on / 依赖: P.ext_of_isTriangulatedClosed, P.le_shift, le_shift, rot_of_distTriang
-/
instance [P.IsTriangulated] : P.IsTriangulatedClosed₃ where
  ext₃' _ hT h₁ h₂ :=
    P.ext_of_isTriangulatedClosed₂' _ (rot_of_distTriang _ hT) h₂ (P.le_shift _ _ h₁)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsTriangulated]
  signature: : P.isoClosure.IsTriangulated where

中文:
实例 [P.是三角]
  签名: : P.isoClosure.是三角 where
-/
instance [P.IsTriangulated] : P.isoClosure.IsTriangulated where

instance {Q : ObjectProperty C} [P.IsTriangulated] [Q.IsTriangulated]
    [Q.IsClosedUnderIsomorphisms] :
    (P ⊓ Q).IsTriangulated where
  ext₂' T hT h₁ h₃ := by
    obtain ⟨Y, hY, ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₂' T hT h₁.1 h₃.1
    exact ⟨Y, ⟨hY, Q.prop_of_iso e (Q.ext_of_isTriangulatedClosed₂ T hT h₁.2 h₃.2)⟩, ⟨e⟩⟩

section

variable (Q R : ObjectProperty C)

/--
Definition of `extensionProduct` / `extensionProduct` 的定义

English:
definition extensionProduct
  signature: : ObjectProperty C
  body: fun X => exists (Y Z : C) (f : Y ⟶ X) (g : X ⟶ Z) (h : Z ⟶ Y⟦(1 : Int)⟧),
    Triangle.mk f g h in distTriang C ∧ P Y ∧ Q Z

中文:
定义 extensionProduct
  签名: : ObjectProperty C
  定义体: fun X => exists (Y Z : C) (f : Y ⟶ X) (g : X ⟶ Z) (h : Z ⟶ Y⟦(1 : Int)⟧),
    Triangle.mk f g h in distTriang C ∧ P Y ∧ Q Z

Depends on / 依赖: Triangle, Triangle.mk, distTriang
-/
def extensionProduct : ObjectProperty C :=
  fun X => exists (Y Z : C) (f : Y ⟶ X) (g : X ⟶ Z) (h : Z ⟶ Y⟦(1 : Int)⟧),
    Triangle.mk f g h in distTriang C ∧ P Y ∧ Q Z

/--
lemma `extensionProduct_iff` / 引理 `extensionProduct_iff`

English:
lemma extensionProduct_iff
  given: (X : C)
  statement: extensionProduct P Q X ↔
  proof: Iff.rfl

中文:
引理 extensionProduct_iff
  条件: (X : C)
  结论: extensionProduct P Q X ↔
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma extensionProduct_iff (X : C) : extensionProduct P Q X ↔
  exists (Y Z : C) (f : Y ⟶ X) (g : X ⟶ Z) (h : Z ⟶ Y⟦(1 : Int)⟧),
    Triangle.mk f g h in distTriang C ∧ P Y ∧ Q Z := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.Nonempty]
  signature: [Q.Nonempty]
  body: by
  obtain ⟨Y, f, g, hT⟩ := distinguished_cocone_triangle₂ (0 : Q.arbitrary ⟶ P.arbitrary⟦(1 : Int)⟧)
  exact ⟨_, _, _, _, _, _, hT, P.prop_arbitrary, Q.prop_arbitrary⟩

@[simp]

中文:
实例 [P.非空]
  签名: [Q.非空]
  定义体: by
  obtain ⟨Y, f, g, hT⟩ := distinguished_cocone_triangle₂ (0 : Q.arbitrary ⟶ P.arbitrary⟦(1 : Int)⟧)
  exact ⟨_, _, _, _, _, _, hT, P.prop_arbitrary, Q.prop_arbitrary⟩

@[simp]

Depends on / 依赖: P.arbitrary, P.prop_arbitrary, Q.arbitrary, Q.prop_arbitrary, arbitrary, prop_arbitrary
-/
instance [P.Nonempty] [Q.Nonempty] : (extensionProduct P Q).Nonempty := by
  obtain ⟨Y, f, g, hT⟩ := distinguished_cocone_triangle₂ (0 : Q.arbitrary ⟶ P.arbitrary⟦(1 : Int)⟧)
  exact ⟨_, _, _, _, _, _, hT, P.prop_arbitrary, Q.prop_arbitrary⟩

@[simp]
/--
lemma `extensionProduct_bot_left` / 引理 `extensionProduct_bot_left`

English:
lemma extensionProduct_bot_left
  statement: extensionProduct ⊥ P = ⊥
  proof: by
  rw [eq_bot_iff]
  intro _ ⟨_, _, _, _, _, _, h, _⟩
  exact h

@[simp]

中文:
引理 extensionProduct_bot_left
  结论: extensionProduct ⊥ P = ⊥
  证明: by
  rw [eq_bot_iff]
  intro _ ⟨_, _, _, _, _, _, h, _⟩
  exact h

@[simp]

Depends on / 依赖: eq_bot_iff
-/
lemma extensionProduct_bot_left : extensionProduct ⊥ P = ⊥ := by
  rw [eq_bot_iff]
  intro _ ⟨_, _, _, _, _, _, h, _⟩
  exact h

@[simp]
/--
lemma `extensionProduct_bot_right` / 引理 `extensionProduct_bot_right`

English:
lemma extensionProduct_bot_right
  statement: extensionProduct P ⊥ = ⊥
  proof: by
  rw [eq_bot_iff]
  intro _ ⟨_, _, _, _, _, _, _, h⟩
  exact h

中文:
引理 extensionProduct_bot_right
  结论: extensionProduct P ⊥ = ⊥
  证明: by
  rw [eq_bot_iff]
  intro _ ⟨_, _, _, _, _, _, _, h⟩
  exact h

Depends on / 依赖: eq_bot_iff
-/
lemma extensionProduct_bot_right : extensionProduct P ⊥ = ⊥ := by
  rw [eq_bot_iff]
  intro _ ⟨_, _, _, _, _, _, _, h⟩
  exact h

variable {P} in
/--
lemma `monotone_extensionProduct_left` / 引理 `monotone_extensionProduct_left`

English:
lemma monotone_extensionProduct_left
  given: {P' : ObjectProperty C} (h : P <= P')
  proof: by
  intro X ⟨Y, Z, f, g, k, hT, hP, hQ⟩
  exact ⟨Y, Z, f, g, k, hT, h Y hP, hQ⟩

中文:
引理 monotone_extensionProduct_left
  条件: {P' : ObjectProperty C} (h : P <= P')
  证明: by
  intro X ⟨Y, Z, f, g, k, hT, hP, hQ⟩
  exact ⟨Y, Z, f, g, k, hT, h Y hP, hQ⟩
-/
lemma monotone_extensionProduct_left {P' : ObjectProperty C} (h : P <= P') :
    extensionProduct P Q <= extensionProduct P' Q := by
  intro X ⟨Y, Z, f, g, k, hT, hP, hQ⟩
  exact ⟨Y, Z, f, g, k, hT, h Y hP, hQ⟩

variable {Q} in
/--
lemma `monotone_extensionProduct_right` / 引理 `monotone_extensionProduct_right`

English:
lemma monotone_extensionProduct_right
  given: {Q' : ObjectProperty C} (h : Q <= Q')
  proof: by
  intro X ⟨Y, Z, f, g, k, hT, hP, hQ⟩
  exact ⟨Y, Z, f, g, k, hT, hP, h Z hQ⟩

中文:
引理 monotone_extensionProduct_right
  条件: {Q' : ObjectProperty C} (h : Q <= Q')
  证明: by
  intro X ⟨Y, Z, f, g, k, hT, hP, hQ⟩
  exact ⟨Y, Z, f, g, k, hT, hP, h Z hQ⟩
-/
lemma monotone_extensionProduct_right {Q' : ObjectProperty C} (h : Q <= Q') :
    extensionProduct P Q <= extensionProduct P Q' := by
  intro X ⟨Y, Z, f, g, k, hT, hP, hQ⟩
  exact ⟨Y, Z, f, g, k, hT, hP, h Z hQ⟩

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (extensionProduct P Q).IsClosedUnderIsomorphisms
  body: by
    intro X X' i ⟨Y, Z, f, g, h, hT, hP, hQ⟩
    refine ⟨Y, Z, f ≫ i.hom, i.inv ≫ g, h, ?_, hP, hQ⟩
exact isomorphic_distinguished _ hT _ Triangle.isoMk _ _ (Iso.refl _) i.symm (Iso.refl _)

中文:
实例 :
  签名: (extensionProduct P Q).在同构下封闭
  定义体: by
    intro X X' i ⟨Y, Z, f, g, h, hT, hP, hQ⟩
    refine ⟨Y, Z, f ≫ i.hom, i.inv ≫ g, h, ?_, hP, hQ⟩
exact isomorphic_distinguished _ hT _ Triangle.isoMk _ _ (Iso.refl _) i.symm (Iso.refl _)

Depends on / 依赖: Iso.refl, Triangle, Triangle.isoMk, i.hom, i.inv, i.symm, isomorphic_distinguished
-/
instance : (extensionProduct P Q).IsClosedUnderIsomorphisms where
  of_iso := by
    intro X X' i ⟨Y, Z, f, g, h, hT, hP, hQ⟩
    refine ⟨Y, Z, f ≫ i.hom, i.inv ≫ g, h, ?_, hP, hQ⟩
exact isomorphic_distinguished _ hT _ Triangle.isoMk _ _ (Iso.refl _) i.symm (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `extensionProduct_isoClosure_left` / 引理 `extensionProduct_isoClosure_left`

English:
lemma extensionProduct_isoClosure_left
  proof: by
  refine le_antisymm ?_ (monotone_extensionProduct_left Q P.le_isoClosure)
  intro X ⟨Y, Z, f, g, h, hT, ⟨Y', hP, ⟨i⟩⟩, hQ⟩
  refine ⟨Y', Z, i.inv ≫ f, g, h ≫ i.hom⟦1⟧', ?_, hP, hQ⟩
exact isomorphic_distinguished _ hT _ Triangle.isoMk _ _ i.symm (Iso.refl _) (Iso.refl _)

中文:
引理 extensionProduct_isoClosure_left
  证明: by
  refine le_antisymm ?_ (monotone_extensionProduct_left Q P.le_isoClosure)
  intro X ⟨Y, Z, f, g, h, hT, ⟨Y', hP, ⟨i⟩⟩, hQ⟩
  refine ⟨Y', Z, i.inv ≫ f, g, h ≫ i.hom⟦1⟧', ?_, hP, hQ⟩
exact isomorphic_distinguished _ hT _ Triangle.isoMk _ _ i.symm (Iso.refl _) (Iso.refl _)

Depends on / 依赖: Iso.refl, List.getElem, P.le_isoClosure, Triangle, Triangle.isoMk, _eq_getElem, getElem, getVert_eq_support_getElem, i.hom, i.inv, i.symm, isomorphic_distinguished, le_antisymm, le_isoClosure, monotone_extensionProduct_left
-/
lemma extensionProduct_isoClosure_left :
    extensionProduct P.isoClosure Q = extensionProduct P Q := by
  refine le_antisymm ?_ (monotone_extensionProduct_left Q P.le_isoClosure)
  intro X ⟨Y, Z, f, g, h, hT, ⟨Y', hP, ⟨i⟩⟩, hQ⟩
  refine ⟨Y', Z, i.inv ≫ f, g, h ≫ i.hom⟦1⟧', ?_, hP, hQ⟩
exact isomorphic_distinguished _ hT _ Triangle.isoMk _ _ i.symm (Iso.refl _) (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `extensionProduct_isoClosure_right` / 引理 `extensionProduct_isoClosure_right`

English:
lemma extensionProduct_isoClosure_right
  proof: by
  refine le_antisymm ?_ (monotone_extensionProduct_right _ Q.le_isoClosure)
  intro X ⟨Y, Z, f, g, h, hT, hP, ⟨Z', hQ, ⟨i⟩⟩⟩
  refine ⟨Y, Z', f, g ≫ i.hom, i.inv ≫ h, ?_, hP, hQ⟩
exact isomorphic_distinguished _ hT _ Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) i.symm

中文:
引理 extensionProduct_isoClosure_right
  证明: by
  refine le_antisymm ?_ (monotone_extensionProduct_right _ Q.le_isoClosure)
  intro X ⟨Y, Z, f, g, h, hT, hP, ⟨Z', hQ, ⟨i⟩⟩⟩
  refine ⟨Y, Z', f, g ≫ i.hom, i.inv ≫ h, ?_, hP, hQ⟩
exact isomorphic_distinguished _ hT _ Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) i.symm

Depends on / 依赖: Iso.refl, Q.le_isoClosure, Triangle, Triangle.isoMk, i.hom, i.inv, i.symm, isomorphic_distinguished, le_antisymm, le_isoClosure, monotone_extensionProduct_right
-/
lemma extensionProduct_isoClosure_right :
    extensionProduct P Q.isoClosure = extensionProduct P Q := by
  refine le_antisymm ?_ (monotone_extensionProduct_right _ Q.le_isoClosure)
  intro X ⟨Y, Z, f, g, h, hT, hP, ⟨Z', hQ, ⟨i⟩⟩⟩
  refine ⟨Y, Z', f, g ≫ i.hom, i.inv ≫ h, ?_, hP, hQ⟩
exact isomorphic_distinguished _ hT _ Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) i.symm

variable {P} in
/--
lemma `le_extensionProduct_left` / 引理 `le_extensionProduct_left`

English:
lemma le_extensionProduct_left
  given: [Q.ContainsZero]
  statement: P <= extensionProduct P Q
  proof: by
  intro X hX
  rw [← extensionProduct_isoClosure_right]
  obtain ⟨Z, hZ, hQ⟩ := Q.exists_prop_of_containsZero
  refine ⟨_, _, _, _, _, contractible_distinguished X, hX, ?_⟩
  exact ⟨Z, hQ, ⟨IsZero.iso (isZero_zero C) hZ⟩⟩

中文:
引理 le_extensionProduct_left
  条件: [Q.余ntainsZero]
  结论: P <= extensionProduct P Q
  证明: by
  intro X hX
  rw [← extensionProduct_isoClosure_right]
  obtain ⟨Z, hZ, hQ⟩ := Q.exists_prop_of_containsZero
  refine ⟨_, _, _, _, _, contractible_distinguished X, hX, ?_⟩
  exact ⟨Z, hQ, ⟨IsZero.iso (isZero_zero C) hZ⟩⟩

Depends on / 依赖: IsZero, IsZero.iso, Q.exists_prop_of_containsZero, contractible_distinguished, exists_prop_of_containsZero, extensionProduct_isoClosure_right, isZero_zero
-/
lemma le_extensionProduct_left [Q.ContainsZero] : P <= extensionProduct P Q := by
  intro X hX
  rw [← extensionProduct_isoClosure_right]
  obtain ⟨Z, hZ, hQ⟩ := Q.exists_prop_of_containsZero
  refine ⟨_, _, _, _, _, contractible_distinguished X, hX, ?_⟩
  exact ⟨Z, hQ, ⟨IsZero.iso (isZero_zero C) hZ⟩⟩

variable {Q} in
/--
lemma `le_extensionProduct_right` / 引理 `le_extensionProduct_right`

English:
lemma le_extensionProduct_right
  given: [P.ContainsZero]
  statement: Q <= extensionProduct P Q
  proof: by
  intro X hX
  rw [← extensionProduct_isoClosure_left]
  obtain ⟨Z, hZ, hP⟩ := P.exists_prop_of_containsZero
  refine ⟨_, _, _, _, _, inv_rot_of_distTriang _ (contractible_distinguished X), ?_, hX⟩
  exact ⟨Z, hP, ⟨IsZero.iso (Functor.map_isZero _ (isZero_zero C)) hZ⟩⟩

中文:
引理 le_extensionProduct_right
  条件: [P.余ntainsZero]
  结论: Q <= extensionProduct P Q
  证明: by
  intro X hX
  rw [← extensionProduct_isoClosure_left]
  obtain ⟨Z, hZ, hP⟩ := P.exists_prop_of_containsZero
  refine ⟨_, _, _, _, _, inv_rot_of_distTriang _ (contractible_distinguished X), ?_, hX⟩
  exact ⟨Z, hP, ⟨IsZero.iso (Functor.map_isZero _ (isZero_zero C)) hZ⟩⟩

Depends on / 依赖: Functor, Functor.map_isZero, IsZero, IsZero.iso, P.exists_prop_of_containsZero, contractible_distinguished, exists_prop_of_containsZero, extensionProduct_isoClosure_left, inv_rot_of_distTriang, isZero_zero, map_isZero
-/
lemma le_extensionProduct_right [P.ContainsZero] : Q <= extensionProduct P Q := by
  intro X hX
  rw [← extensionProduct_isoClosure_left]
  obtain ⟨Z, hZ, hP⟩ := P.exists_prop_of_containsZero
  refine ⟨_, _, _, _, _, inv_rot_of_distTriang _ (contractible_distinguished X), ?_, hX⟩
  exact ⟨Z, hP, ⟨IsZero.iso (Functor.map_isZero _ (isZero_zero C)) hZ⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderShift
  signature: Int] [Q.IsStableUnderShift Int] :
  body: IsStableUnderShiftBy.mk by
    intro X ⟨Y, Z, f, g, h, hT, hP, hQ⟩
    refine ⟨_, _, _, _, _, Triangle.shift_distinguished _ hT a, ?_, ?_⟩
    all_goals apply IsStableUnderShiftBy.le_shift; assumption

@[stacks 0FX1]

中文:
实例 [P.是StableUnderShift
  签名: 整数] [Q.是StableUnderShift 整数] :
  定义体: IsStableUnderShiftBy.mk by
    intro X ⟨Y, Z, f, g, h, hT, hP, hQ⟩
    refine ⟨_, _, _, _, _, Triangle.shift_distinguished _ hT a, ?_, ?_⟩
    all_goals apply IsStableUnderShiftBy.le_shift; assumption

@[stacks 0FX1]

Depends on / 依赖: IsStableUnderShiftBy, IsStableUnderShiftBy.le_shift, IsStableUnderShiftBy.mk, Triangle, Triangle.shift_distinguished, all_goals, le_shift, shift_distinguished
-/
instance [P.IsStableUnderShift Int] [Q.IsStableUnderShift Int] :
    (extensionProduct P Q).IsStableUnderShift Int where
isStableUnderShiftBy a := IsStableUnderShiftBy.mk by
    intro X ⟨Y, Z, f, g, h, hT, hP, hQ⟩
    refine ⟨_, _, _, _, _, Triangle.shift_distinguished _ hT a, ?_, ?_⟩
    all_goals apply IsStableUnderShiftBy.le_shift; assumption

@[stacks 0FX1]
/--
lemma `extensionProduct_assoc` / 引理 `extensionProduct_assoc`

English:
lemma extensionProduct_assoc
  given: [IsTriangulated C]
  proof: by
  ext X
  constructor
  · intro ⟨Y, C, f, g, h, hT, ⟨A, B, f', g', h', hT', hP, hQ⟩, hR⟩
    obtain ⟨Y, g'', h'', hT''⟩ := distinguished_cocone_triangle (f' ≫ f)
    let o := someOctahedron rfl hT' hT hT''
    exact ⟨_, _, _, _, _, hT'', hP, ⟨_, _, _, _, _, o.mem, hQ, hR⟩⟩
  · intro ⟨A, Z, f, g, h, hT, hP, ⟨B, C, f', g', h', hT', hQ, hR⟩⟩
    obtain ⟨Y, f'', h'', hT''⟩ := distinguished_cocone_triangle₁ (g ≫ g')
    let o := someOctahedron' rfl hT hT' hT''
    exact ⟨_, _, _, _, _, hT'', ⟨_, _, _, _, _, o.mem, hP, hQ⟩, hR⟩

中文:
引理 extensionProduct_assoc
  条件: [是三角 C]
  证明: by
  ext X
  constructor
  · intro ⟨Y, C, f, g, h, hT, ⟨A, B, f', g', h', hT', hP, hQ⟩, hR⟩
    obtain ⟨Y, g'', h'', hT''⟩ := distinguished_cocone_triangle (f' ≫ f)
    let o := someOctahedron rfl hT' hT hT''
    exact ⟨_, _, _, _, _, hT'', hP, ⟨_, _, _, _, _, o.mem, hQ, hR⟩⟩
  · intro ⟨A, Z, f, g, h, hT, hP, ⟨B, C, f', g', h', hT', hQ, hR⟩⟩
    obtain ⟨Y, f'', h'', hT''⟩ := distinguished_cocone_triangle₁ (g ≫ g')
    let o := someOctahedron' rfl hT hT' hT''
    exact ⟨_, _, _, _, _, hT'', ⟨_, _, _, _, _, o.mem, hP, hQ⟩, hR⟩

Depends on / 依赖: distinguished_cocone_triangle, o.mem, someOctahedron
-/
lemma extensionProduct_assoc [IsTriangulated C] :
    extensionProduct (extensionProduct P Q) R = extensionProduct P (extensionProduct Q R) := by
  ext X
  constructor
  · intro ⟨Y, C, f, g, h, hT, ⟨A, B, f', g', h', hT', hP, hQ⟩, hR⟩
    obtain ⟨Y, g'', h'', hT''⟩ := distinguished_cocone_triangle (f' ≫ f)
    let o := someOctahedron rfl hT' hT hT''
    exact ⟨_, _, _, _, _, hT'', hP, ⟨_, _, _, _, _, o.mem, hQ, hR⟩⟩
  · intro ⟨A, Z, f, g, h, hT, hP, ⟨B, C, f', g', h', hT', hQ, hR⟩⟩
    obtain ⟨Y, f'', h'', hT''⟩ := distinguished_cocone_triangle₁ (g ≫ g')
    let o := someOctahedron' rfl hT hT' hT''
    exact ⟨_, _, _, _, _, hT'', ⟨_, _, _, _, _, o.mem, hP, hQ⟩, hR⟩

/--
lemma `extensionProduct_le_of_isTriangulatedClosed₂'` / 引理 `extensionProduct_le_of_isTriangulatedClosed₂'`

English:
lemma extensionProduct_le_of_isTriangulatedClosed₂'
  statement: {P₁ P₂ Q : ObjectProperty C}
  proof: by
  intro _ ⟨_, _, _, _, _, hT, hY, hZ⟩
  exact ext_of_isTriangulatedClosed₂' Q _ hT (h₁ _ hY) (h₂ _ hZ)

中文:
引理 extensionProduct_le_of_isTriangulatedClosed₂'
  结论: {P₁ P₂ Q : ObjectProperty C}
  证明: by
  intro _ ⟨_, _, _, _, _, hT, hY, hZ⟩
  exact ext_of_isTriangulatedClosed₂' Q _ hT (h₁ _ hY) (h₂ _ hZ)
-/
lemma extensionProduct_le_of_isTriangulatedClosed₂' {P₁ P₂ Q : ObjectProperty C}
    [Q.IsTriangulatedClosed₂] (h₁ : P₁ <= Q) (h₂ : P₂ <= Q) :
    extensionProduct P₁ P₂ <= Q.isoClosure := by
  intro _ ⟨_, _, _, _, _, hT, hY, hZ⟩
  exact ext_of_isTriangulatedClosed₂' Q _ hT (h₁ _ hY) (h₂ _ hZ)

/--
lemma `extensionProduct_le_of_isTriangulatedClosed₂` / 引理 `extensionProduct_le_of_isTriangulatedClosed₂`

English:
lemma extensionProduct_le_of_isTriangulatedClosed₂
  statement: {P₁ P₂ Q : ObjectProperty C}
  proof: by
  intro _ ⟨_, _, _, _, _, hT, hY, hZ⟩
  exact ext_of_isTriangulatedClosed₂ Q _ hT (h₁ _ hY) (h₂ _ hZ)

中文:
引理 extensionProduct_le_of_isTriangulatedClosed₂
  结论: {P₁ P₂ Q : ObjectProperty C}
  证明: by
  intro _ ⟨_, _, _, _, _, hT, hY, hZ⟩
  exact ext_of_isTriangulatedClosed₂ Q _ hT (h₁ _ hY) (h₂ _ hZ)
-/
lemma extensionProduct_le_of_isTriangulatedClosed₂ {P₁ P₂ Q : ObjectProperty C}
    [Q.IsTriangulatedClosed₂] [Q.IsClosedUnderIsomorphisms] (h₁ : P₁ <= Q) (h₂ : P₂ <= Q) :
    extensionProduct P₁ P₂ <= Q := by
  intro _ ⟨_, _, _, _, _, hT, hY, hZ⟩
  exact ext_of_isTriangulatedClosed₂ Q _ hT (h₁ _ hY) (h₂ _ hZ)

set_option backward.defeqAttrib.useBackward true in
@[stacks 0FX2 "first part"]
/--
lemma `extensionProduct_retractClosure_retractClosure_le` / 引理 `extensionProduct_retractClosure_retractClosure_le`

English:
lemma extensionProduct_retractClosure_retractClosure_le
  proof: by
  intro X ⟨A, B, f₁, f₂, f₃, hT, ⟨A', hP, ⟨a₁, b₁, h₁⟩⟩, ⟨B', hQ, ⟨a₃, b₃, h₃⟩⟩⟩
  obtain ⟨X', g₁, g₂, hT'⟩ := distinguished_cocone_triangle₂ (b₃ ≫ f₃ ≫ a₁⟦(1 : Int)⟧')
  obtain ⟨a₂ : X ⟶ X', ha₁₂, ha₂₃⟩ :=
    complete_distinguished_triangle_morphism₂ _ _ hT hT' a₁ a₃ (by dsimp; grind)
  obtain ⟨b₂ : X' ⟶ X, hb₁₂, hb₂₃⟩ :=
    complete_distinguished_triangle_morphism₂ _ _ hT' hT b₁ b₃ (by dsimp; grind)
  dsimp at ha₁₂ ha₂₃ hb₁₂ hb₂₃
  refine ⟨X', ⟨_, _, _, _, _, hT', hP, hQ⟩, ⟨?_⟩⟩
  let φ := Triangle.homMk (Triangle.mk f₁ f₂ f₃) (Triangle.mk f₁ f₂ f₃) (𝟙 A)
    (a₂ ≫ b₂) (𝟙 B) (by dsimp; grind) (by dsimp; grind)
  haveI : IsIso (a₂ ≫ b₂) := isIso₂_of_isIso₁₃ φ hT hT (IsIso.id _) (IsIso.id _)
  exact ⟨a₂, b₂ ≫ inv (a₂ ≫ b₂), by grind⟩

@[stacks 0FX2 "second part"]

中文:
引理 extensionProduct_retractClosure_retractClosure_le
  证明: by
  intro X ⟨A, B, f₁, f₂, f₃, hT, ⟨A', hP, ⟨a₁, b₁, h₁⟩⟩, ⟨B', hQ, ⟨a₃, b₃, h₃⟩⟩⟩
  obtain ⟨X', g₁, g₂, hT'⟩ := distinguished_cocone_triangle₂ (b₃ ≫ f₃ ≫ a₁⟦(1 : Int)⟧')
  obtain ⟨a₂ : X ⟶ X', ha₁₂, ha₂₃⟩ :=
    complete_distinguished_triangle_morphism₂ _ _ hT hT' a₁ a₃ (by dsimp; grind)
  obtain ⟨b₂ : X' ⟶ X, hb₁₂, hb₂₃⟩ :=
    complete_distinguished_triangle_morphism₂ _ _ hT' hT b₁ b₃ (by dsimp; grind)
  dsimp at ha₁₂ ha₂₃ hb₁₂ hb₂₃
  refine ⟨X', ⟨_, _, _, _, _, hT', hP, hQ⟩, ⟨?_⟩⟩
  let φ := Triangle.homMk (Triangle.mk f₁ f₂ f₃) (Triangle.mk f₁ f₂ f₃) (𝟙 A)
    (a₂ ≫ b₂) (𝟙 B) (by dsimp; grind) (by dsimp; grind)
  haveI : IsIso (a₂ ≫ b₂) := isIso₂_of_isIso₁₃ φ hT hT (IsIso.id _) (IsIso.id _)
  exact ⟨a₂, b₂ ≫ inv (a₂ ≫ b₂), by grind⟩

@[stacks 0FX2 "second part"]

Depends on / 依赖: Triangle, Triangle.homMk
-/
lemma extensionProduct_retractClosure_retractClosure_le :
    extensionProduct P.retractClosure Q.retractClosure <=
      (extensionProduct P Q).retractClosure := by
  intro X ⟨A, B, f₁, f₂, f₃, hT, ⟨A', hP, ⟨a₁, b₁, h₁⟩⟩, ⟨B', hQ, ⟨a₃, b₃, h₃⟩⟩⟩
  obtain ⟨X', g₁, g₂, hT'⟩ := distinguished_cocone_triangle₂ (b₃ ≫ f₃ ≫ a₁⟦(1 : Int)⟧')
  obtain ⟨a₂ : X ⟶ X', ha₁₂, ha₂₃⟩ :=
    complete_distinguished_triangle_morphism₂ _ _ hT hT' a₁ a₃ (by dsimp; grind)
  obtain ⟨b₂ : X' ⟶ X, hb₁₂, hb₂₃⟩ :=
    complete_distinguished_triangle_morphism₂ _ _ hT' hT b₁ b₃ (by dsimp; grind)
  dsimp at ha₁₂ ha₂₃ hb₁₂ hb₂₃
  refine ⟨X', ⟨_, _, _, _, _, hT', hP, hQ⟩, ⟨?_⟩⟩
  let φ := Triangle.homMk (Triangle.mk f₁ f₂ f₃) (Triangle.mk f₁ f₂ f₃) (𝟙 A)
    (a₂ ≫ b₂) (𝟙 B) (by dsimp; grind) (by dsimp; grind)
  haveI : IsIso (a₂ ≫ b₂) := isIso₂_of_isIso₁₃ φ hT hT (IsIso.id _) (IsIso.id _)
  exact ⟨a₂, b₂ ≫ inv (a₂ ≫ b₂), by grind⟩

@[stacks 0FX2 "second part"]
/--
lemma `retractClosure_extensionProduct_retractClosure_retractClosure` / 引理 `retractClosure_extensionProduct_retractClosure_retractClosure`

English:
lemma retractClosure_extensionProduct_retractClosure_retractClosure
  proof: by
  apply le_antisymm
  · rw [retractClosure_le_iff]
    exact extensionProduct_retractClosure_retractClosure_le P Q
  · apply monotone_retractClosure
    grw [monotone_extensionProduct_right _ (le_retractClosure Q),
      monotone_extensionProduct_left _ (le_retractClosure P)]

中文:
引理 retractClosure_extensionProduct_retractClosure_retractClosure
  证明: by
  apply le_antisymm
  · rw [retractClosure_le_iff]
    exact extensionProduct_retractClosure_retractClosure_le P Q
  · apply monotone_retractClosure
    grw [monotone_extensionProduct_right _ (le_retractClosure Q),
      monotone_extensionProduct_left _ (le_retractClosure P)]

Depends on / 依赖: extensionProduct_retractClosure_retractClosure_le, le_antisymm, le_retractClosure, monotone_extensionProduct_left, monotone_extensionProduct_right, monotone_retractClosure, retractClosure_le_iff
-/
lemma retractClosure_extensionProduct_retractClosure_retractClosure :
    (extensionProduct P.retractClosure Q.retractClosure).retractClosure =
      (extensionProduct P Q).retractClosure := by
  apply le_antisymm
  · rw [retractClosure_le_iff]
    exact extensionProduct_retractClosure_retractClosure_le P Q
  · apply monotone_retractClosure
    grw [monotone_extensionProduct_right _ (le_retractClosure Q),
      monotone_extensionProduct_left _ (le_retractClosure P)]

/--
Definition of `extensionProductIter` / `extensionProductIter` 的定义

English:
definition extensionProductIter
  signature: (n : Nat)
  body: (extensionProduct P)^[n] P

@[simp]

中文:
定义 extensionProductIter
  签名: (n : 自然数)
  定义体: (extensionProduct P)^[n] P

@[simp]

Depends on / 依赖: extensionProduct
-/
def extensionProductIter (n : Nat) : ObjectProperty C := (extensionProduct P)^[n] P

@[simp]
/--
lemma `extensionProductIter_zero` / 引理 `extensionProductIter_zero`

English:
lemma extensionProductIter_zero
  statement: P.extensionProductIter 0 = P
  proof: rfl

中文:
引理 extensionProductIter_zero
  结论: P.extensionProductIter 0 = P
  证明: rfl
-/
lemma extensionProductIter_zero : P.extensionProductIter 0 = P := rfl

/--
lemma `extensionProductIter_succ` / 引理 `extensionProductIter_succ`

English:
lemma extensionProductIter_succ
  given: (n : Nat)
  proof: Function.iterate_succ_apply' _ _ _

中文:
引理 extensionProductIter_succ
  条件: (n : 自然数)
  证明: Function.iterate_succ_apply' _ _ _

Depends on / 依赖: Function, Function.iterate_succ_apply, iterate_succ_apply
-/
lemma extensionProductIter_succ (n : Nat) :
    P.extensionProductIter (n + 1) = extensionProduct P (P.extensionProductIter n) :=
  Function.iterate_succ_apply' _ _ _

/--
lemma `extensionProductIter_succ'` / 引理 `extensionProductIter_succ'`

English:
lemma extensionProductIter_succ'
  given: [IsTriangulated C] (n : Nat)
  proof: by
  induction n with
  | zero => rfl
  | succ n h =>
    rw [extensionProductIter_succ]; rw [h]; rw [← extensionProduct_assoc]; rw [← extensionProductIter_succ]; rw [← h]

中文:
引理 extensionProductIter_succ'
  条件: [是三角 C] (n : 自然数)
  证明: by
  induction n with
  | zero => rfl
  | succ n h =>
    rw [extensionProductIter_succ]; rw [h]; rw [← extensionProduct_assoc]; rw [← extensionProductIter_succ]; rw [← h]

Depends on / 依赖: extensionProductIter_succ, extensionProduct_assoc
-/
lemma extensionProductIter_succ' [IsTriangulated C] (n : Nat) :
    P.extensionProductIter (n + 1) = extensionProduct (P.extensionProductIter n) P := by
  induction n with
  | zero => rfl
  | succ n h =>
    rw [extensionProductIter_succ]; rw [h]; rw [← extensionProduct_assoc]; rw [← extensionProductIter_succ]; rw [← h]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.Nonempty]
  signature: (n : Nat)
  body: by
  induction n with
  | zero => rwa [extensionProductIter_zero]
  | succ n h => rw [extensionProductIter_succ]; infer_instance

中文:
实例 [P.非空]
  签名: (n : 自然数)
  定义体: by
  induction n with
  | zero => rwa [extensionProductIter_zero]
  | succ n h => rw [extensionProductIter_succ]; infer_instance

Depends on / 依赖: extensionProductIter_succ, extensionProductIter_zero, infer_instance
-/
instance [P.Nonempty] (n : Nat) : (P.extensionProductIter n).Nonempty := by
  induction n with
  | zero => rwa [extensionProductIter_zero]
  | succ n h => rw [extensionProductIter_succ]; infer_instance

/--
lemma `extensionProductIter_add` / 引理 `extensionProductIter_add`

English:
lemma extensionProductIter_add
  given: [IsTriangulated C] {n m n' : Nat} (h : n = n' + 1)
  proof: by
  induction m with
  | zero => rw [add_zero, extensionProductIter_zero, h, extensionProductIter_succ']
  | succ m hm =>
    rw [← add_assoc]; rw [extensionProductIter_succ']; rw [extensionProductIter_succ']; rw [hm]; rw [extensionProduct_assoc]

中文:
引理 extensionProductIter_add
  条件: [是三角 C] {n m n' : 自然数} (h : n = n' + 1)
  证明: by
  induction m with
  | zero => rw [add_zero, extensionProductIter_zero, h, extensionProductIter_succ']
  | succ m hm =>
    rw [← add_assoc]; rw [extensionProductIter_succ']; rw [extensionProductIter_succ']; rw [hm]; rw [extensionProduct_assoc]

Depends on / 依赖: add_assoc, add_zero, extensionProductIter_succ, extensionProductIter_zero, extensionProduct_assoc
-/
lemma extensionProductIter_add [IsTriangulated C] {n m n' : Nat} (h : n = n' + 1) :
    P.extensionProductIter (n + m) =
      extensionProduct (P.extensionProductIter n') (P.extensionProductIter m) := by
  induction m with
  | zero => rw [add_zero, extensionProductIter_zero, h, extensionProductIter_succ']
  | succ m hm =>
    rw [← add_assoc]; rw [extensionProductIter_succ']; rw [extensionProductIter_succ']; rw [hm]; rw [extensionProduct_assoc]

/--
lemma `extensionProductIter_add'` / 引理 `extensionProductIter_add'`

English:
lemma extensionProductIter_add'
  given: [IsTriangulated C] {n m m' : Nat} (h : m = m' + 1)
  proof: by
  induction n with
  | zero => rw [zero_add, extensionProductIter_zero, h, extensionProductIter_succ]
  | succ n hn => rw [add_assoc, add_comm 1 m, ← add_assoc, extensionProductIter_succ,
    extensionProductIter_succ, hn, extensionProduct_assoc]

中文:
引理 extensionProductIter_add'
  条件: [是三角 C] {n m m' : 自然数} (h : m = m' + 1)
  证明: by
  induction n with
  | zero => rw [zero_add, extensionProductIter_zero, h, extensionProductIter_succ]
  | succ n hn => rw [add_assoc, add_comm 1 m, ← add_assoc, extensionProductIter_succ,
    extensionProductIter_succ, hn, extensionProduct_assoc]

Depends on / 依赖: add_assoc, add_comm, extensionProductIter_succ, extensionProductIter_zero, extensionProduct_assoc, zero_add
-/
lemma extensionProductIter_add' [IsTriangulated C] {n m m' : Nat} (h : m = m' + 1) :
    P.extensionProductIter (n + m) =
      extensionProduct (P.extensionProductIter n) (P.extensionProductIter m') := by
  induction n with
  | zero => rw [zero_add, extensionProductIter_zero, h, extensionProductIter_succ]
  | succ n hn => rw [add_assoc, add_comm 1 m, ← add_assoc, extensionProductIter_succ,
    extensionProductIter_succ, hn, extensionProduct_assoc]

variable {P} in
/--
lemma `monotone_extensionProductIter` / 引理 `monotone_extensionProductIter`

English:
lemma monotone_extensionProductIter
  given: {Q : ObjectProperty C} (hPQ : P <= Q) (n : Nat)
  proof: by
  induction n with
  | zero => exact hPQ
  | succ n h => grw [extensionProductIter_succ, extensionProductIter_succ,
    monotone_extensionProduct_left _ hPQ, monotone_extensionProduct_right _ h]

中文:
引理 monotone_extensionProductIter
  条件: {Q : ObjectProperty C} (hPQ : P <= Q) (n : 自然数)
  证明: by
  induction n with
  | zero => exact hPQ
  | succ n h => grw [extensionProductIter_succ, extensionProductIter_succ,
    monotone_extensionProduct_left _ hPQ, monotone_extensionProduct_right _ h]

Depends on / 依赖: extensionProductIter_succ, monotone_extensionProduct_left, monotone_extensionProduct_right
-/
lemma monotone_extensionProductIter {Q : ObjectProperty C} (hPQ : P <= Q) (n : Nat) :
    P.extensionProductIter n <= Q.extensionProductIter n := by
  induction n with
  | zero => exact hPQ
  | succ n h => grw [extensionProductIter_succ, extensionProductIter_succ,
    monotone_extensionProduct_left _ hPQ, monotone_extensionProduct_right _ h]

/--
lemma `monotone'_extensionProductIter` / 引理 `monotone'_extensionProductIter`

English:
lemma monotone'_extensionProductIter
  given: [P.ContainsZero] {n m : Nat} (h : n <= m)
  proof: by
  induction m, h using Nat.le_induction
  case base => rfl
  case succ n m hnm h =>
    refine le_trans h ?_
    rw [extensionProductIter_succ]
    exact le_extensionProduct_right P

中文:
引理 monotone'_extensionProductIter
  条件: [P.余ntainsZero] {n m : 自然数} (h : n <= m)
  证明: by
  induction m, h using Nat.le_induction
  case base => rfl
  case succ n m hnm h =>
    refine le_trans h ?_
    rw [extensionProductIter_succ]
    exact le_extensionProduct_right P
-/
lemma monotone'_extensionProductIter [P.ContainsZero] {n m : Nat} (h : n <= m) :
    P.extensionProductIter n <= P.extensionProductIter m := by
  induction m, h using Nat.le_induction
  case base => rfl
  case succ n m hnm h =>
    refine le_trans h ?_
    rw [extensionProductIter_succ]
    exact le_extensionProduct_right P

/--
lemma `le_extensionProductIter` / 引理 `le_extensionProductIter`

English:
lemma le_extensionProductIter
  given: [P.ContainsZero] (n : Nat)
  statement: P <= P.extensionProductIter n
  proof: P.monotone'_extensionProductIter (Nat.zero_le n)

@[simp]

中文:
引理 le_extensionProductIter
  条件: [P.余ntainsZero] (n : 自然数)
  结论: P <= P.extensionProductIter n
  证明: P.monotone'_extensionProductIter (Nat.zero_le n)

@[simp]

Depends on / 依赖: Nat.zero_le, P.monotone, _extensionProductIter, monotone, zero_le
-/
lemma le_extensionProductIter [P.ContainsZero] (n : Nat) : P <= P.extensionProductIter n :=
  P.monotone'_extensionProductIter (Nat.zero_le n)

@[simp]
/--
lemma `extensionProductIter_bot` / 引理 `extensionProductIter_bot`

English:
lemma extensionProductIter_bot
  given: (n : Nat)
  statement: extensionProductIter (⊥ : ObjectProperty C) n = ⊥
  proof: by
  cases n
  case zero => rw [extensionProductIter_zero]
  case succ n => rw [extensionProductIter_succ, extensionProduct_bot_left]

@[simp]

中文:
引理 extensionProductIter_bot
  条件: (n : 自然数)
  结论: extensionProductIter (⊥ : ObjectProperty C) n = ⊥
  证明: by
  cases n
  case zero => rw [extensionProductIter_zero]
  case succ n => rw [extensionProductIter_succ, extensionProduct_bot_left]

@[simp]

Depends on / 依赖: extensionProductIter_succ, extensionProductIter_zero, extensionProduct_bot_left
-/
lemma extensionProductIter_bot (n : Nat) : extensionProductIter (⊥ : ObjectProperty C) n = ⊥ := by
  cases n
  case zero => rw [extensionProductIter_zero]
  case succ n => rw [extensionProductIter_succ, extensionProduct_bot_left]

@[simp]
/--
lemma `extensionProductIter_top` / 引理 `extensionProductIter_top`

English:
lemma extensionProductIter_top
  given: (n : Nat)
  statement: extensionProductIter (⊤ : ObjectProperty C) n = ⊤
  proof: eq_top_iff.mpr (le_extensionProductIter _ n)

中文:
引理 extensionProductIter_top
  条件: (n : 自然数)
  结论: extensionProductIter (⊤ : ObjectProperty C) n = ⊤
  证明: eq_top_iff.mpr (le_extensionProductIter _ n)

Depends on / 依赖: eq_top_iff, eq_top_iff.mpr, le_extensionProductIter
-/
lemma extensionProductIter_top (n : Nat) : extensionProductIter (⊤ : ObjectProperty C) n = ⊤ :=
  eq_top_iff.mpr (le_extensionProductIter _ n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderShift
  signature: Int] (n
  body: by
  induction n with
  | zero => assumption
  | succ n h =>
    rw [extensionProductIter_succ]
    infer_instance

中文:
实例 [P.是StableUnderShift
  签名: 整数] (n
  定义体: by
  induction n with
  | zero => assumption
  | succ n h =>
    rw [extensionProductIter_succ]
    infer_instance

Depends on / 依赖: extensionProductIter_succ, infer_instance
-/
instance [P.IsStableUnderShift Int] (n : Nat) : (P.extensionProductIter n).IsStableUnderShift Int := by
  induction n with
  | zero => assumption
  | succ n h =>
    rw [extensionProductIter_succ]
    infer_instance

/--
lemma `extensionProductIter_le_of_isTriangulatedClosed₂'` / 引理 `extensionProductIter_le_of_isTriangulatedClosed₂'`

English:
lemma extensionProductIter_le_of_isTriangulatedClosed₂'
  statement: {Q : ObjectProperty C}
  proof: by
  induction n with
  | zero =>
    rw [extensionProductIter_zero]
    exact h.trans Q.le_isoClosure
  | succ n H =>
    rw [extensionProductIter_succ]
    exact extensionProduct_le_of_isTriangulatedClosed₂ (h.trans Q.le_isoClosure) H

中文:
引理 extensionProductIter_le_of_isTriangulatedClosed₂'
  结论: {Q : ObjectProperty C}
  证明: by
  induction n with
  | zero =>
    rw [extensionProductIter_zero]
    exact h.trans Q.le_isoClosure
  | succ n H =>
    rw [extensionProductIter_succ]
    exact extensionProduct_le_of_isTriangulatedClosed₂ (h.trans Q.le_isoClosure) H

Depends on / 依赖: Q.le_isoClosure, extensionProductIter_succ, extensionProductIter_zero, h.trans, le_isoClosure
-/
lemma extensionProductIter_le_of_isTriangulatedClosed₂' {Q : ObjectProperty C}
    [Q.IsTriangulatedClosed₂] (h : P <= Q) (n : Nat) : P.extensionProductIter n <= Q.isoClosure := by
  induction n with
  | zero =>
    rw [extensionProductIter_zero]
    exact h.trans Q.le_isoClosure
  | succ n H =>
    rw [extensionProductIter_succ]
    exact extensionProduct_le_of_isTriangulatedClosed₂ (h.trans Q.le_isoClosure) H

/--
lemma `extensionProductIter_le_of_isTriangulatedClosed₂` / 引理 `extensionProductIter_le_of_isTriangulatedClosed₂`

English:
lemma extensionProductIter_le_of_isTriangulatedClosed₂
  statement: {Q : ObjectProperty C}
  proof: Q.isoClosure_eq_self ▸ P.extensionProductIter_le_of_isTriangulatedClosed₂' h n

中文:
引理 extensionProductIter_le_of_isTriangulatedClosed₂
  结论: {Q : ObjectProperty C}
  证明: Q.isoClosure_eq_self ▸ P.extensionProductIter_le_of_isTriangulatedClosed₂' h n

Depends on / 依赖: P.extensionProductIter_le_of_isTriangulatedClosed, Q.isoClosure_eq_self, isoClosure_eq_self
-/
lemma extensionProductIter_le_of_isTriangulatedClosed₂ {Q : ObjectProperty C}
    [Q.IsTriangulatedClosed₂] [Q.IsClosedUnderIsomorphisms] (h : P <= Q) (n : Nat) :
    P.extensionProductIter n <= Q :=
  Q.isoClosure_eq_self ▸ P.extensionProductIter_le_of_isTriangulatedClosed₂' h n

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderShift
  signature: Int] (n
  body: by
  induction n with
  | zero => rwa [extensionProductIter_zero]
  | succ n H => rw [extensionProductIter_succ]; infer_instance

中文:
实例 [P.是StableUnderShift
  签名: 整数] (n
  定义体: by
  induction n with
  | zero => rwa [extensionProductIter_zero]
  | succ n H => rw [extensionProductIter_succ]; infer_instance

Depends on / 依赖: extensionProductIter_succ, extensionProductIter_zero, infer_instance
-/
instance [P.IsStableUnderShift Int] (n : Nat) : (P.extensionProductIter n).IsStableUnderShift Int := by
  induction n with
  | zero => rwa [extensionProductIter_zero]
  | succ n H => rw [extensionProductIter_succ]; infer_instance

/--
lemma `extensionProductIter_retractClosure_le` / 引理 `extensionProductIter_retractClosure_le`

English:
lemma extensionProductIter_retractClosure_le
  given: {n : Nat}
  proof: by
  induction n with
  | zero => simp
  | succ n H =>
    grw [extensionProductIter_succ, extensionProductIter_succ, monotone_extensionProduct_right _ H,
      extensionProduct_retractClosure_retractClosure_le]

中文:
引理 extensionProductIter_retractClosure_le
  条件: {n : 自然数}
  证明: by
  induction n with
  | zero => simp
  | succ n H =>
    grw [extensionProductIter_succ, extensionProductIter_succ, monotone_extensionProduct_right _ H,
      extensionProduct_retractClosure_retractClosure_le]

Depends on / 依赖: extensionProductIter_succ, extensionProduct_retractClosure_retractClosure_le, monotone_extensionProduct_right
-/
lemma extensionProductIter_retractClosure_le {n : Nat} :
    (P.retractClosure.extensionProductIter n) <= (P.extensionProductIter n).retractClosure := by
  induction n with
  | zero => simp
  | succ n H =>
    grw [extensionProductIter_succ, extensionProductIter_succ, monotone_extensionProduct_right _ H,
      extensionProduct_retractClosure_retractClosure_le]

/--
lemma `retractClosure_extensionProductIter_retractClosure` / 引理 `retractClosure_extensionProductIter_retractClosure`

English:
lemma retractClosure_extensionProductIter_retractClosure
  given: {n : Nat}
  proof: by
  apply le_antisymm
  · rw [retractClosure_le_iff]
    exact extensionProductIter_retractClosure_le P
  · exact monotone_retractClosure (monotone_extensionProductIter (le_retractClosure P) n)

中文:
引理 retractClosure_extensionProductIter_retractClosure
  条件: {n : 自然数}
  证明: by
  apply le_antisymm
  · rw [retractClosure_le_iff]
    exact extensionProductIter_retractClosure_le P
  · exact monotone_retractClosure (monotone_extensionProductIter (le_retractClosure P) n)

Depends on / 依赖: extensionProductIter_retractClosure_le, le_antisymm, le_retractClosure, monotone_extensionProductIter, monotone_retractClosure, retractClosure_le_iff
-/
lemma retractClosure_extensionProductIter_retractClosure {n : Nat} :
    (P.retractClosure.extensionProductIter n).retractClosure =
      (P.extensionProductIter n).retractClosure := by
  apply le_antisymm
  · rw [retractClosure_le_iff]
    exact extensionProductIter_retractClosure_le P
  · exact monotone_retractClosure (monotone_extensionProductIter (le_retractClosure P) n)

end

/--
Definition of `trW` / `trW` 的定义

English:
definition trW
  signature: : MorphismProperty C
  body: fun X Y f => exists (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : Int)⟧)
    (_ : Triangle.mk f g h in distTriang C), P Z

中文:
定义 trW
  签名: : MorphismProperty C
  定义体: fun X Y f => exists (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : Int)⟧)
    (_ : Triangle.mk f g h in distTriang C), P Z

Depends on / 依赖: Triangle, Triangle.mk, distTriang
-/
def trW : MorphismProperty C :=
  fun X Y f => exists (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : Int)⟧)
    (_ : Triangle.mk f g h in distTriang C), P Z

/--
lemma `trW_iff` / 引理 `trW_iff`

English:
lemma trW_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: by rfl

中文:
引理 trW_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by rfl
-/
lemma trW_iff {X Y : C} (f : X ⟶ Y) :
    P.trW f ↔ exists (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : Int)⟧)
      (_ : Triangle.mk f g h in distTriang C), P Z := by rfl

/--
lemma `trW_iff'` / 引理 `trW_iff'`

English:
lemma trW_iff'
  given: [P.IsStableUnderShift Int] {Y Z : C} (g : Y ⟶ Z)
  proof: by
  rw [P.trW_iff]
  constructor
  · rintro ⟨Z, g, h, H, mem⟩
    exact ⟨_, _, _, inv_rot_of_distTriang _ H, P.le_shift (-1) _ mem⟩
  · rintro ⟨Z, g, h, H, mem⟩
    exact ⟨_, _, _, rot_of_distTriang _ H, P.le_shift 1 _ mem⟩

中文:
引理 trW_iff'
  条件: [P.是StableUnderShift 整数] {Y Z : C} (g : Y ⟶ Z)
  证明: by
  rw [P.trW_iff]
  constructor
  · rintro ⟨Z, g, h, H, mem⟩
    exact ⟨_, _, _, inv_rot_of_distTriang _ H, P.le_shift (-1) _ mem⟩
  · rintro ⟨Z, g, h, H, mem⟩
    exact ⟨_, _, _, rot_of_distTriang _ H, P.le_shift 1 _ mem⟩

Depends on / 依赖: P.le_shift, P.trW_iff, inv_rot_of_distTriang, le_shift, rot_of_distTriang, trW_iff
-/
lemma trW_iff' [P.IsStableUnderShift Int] {Y Z : C} (g : Y ⟶ Z) :
    P.trW g ↔ exists (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦(1 : Int)⟧)
      (_ : Triangle.mk f g h in distTriang C), P X := by
  rw [P.trW_iff]
  constructor
  · rintro ⟨Z, g, h, H, mem⟩
    exact ⟨_, _, _, inv_rot_of_distTriang _ H, P.le_shift (-1) _ mem⟩
  · rintro ⟨Z, g, h, H, mem⟩
    exact ⟨_, _, _, rot_of_distTriang _ H, P.le_shift 1 _ mem⟩

/--
lemma `trW.mk` / 引理 `trW.mk`

English:
lemma trW.mk
  given: {T : Triangle C} (hT : T in distTriang C) (h : P T.obj₃)
  statement: P.trW T.mor₁
  proof: ⟨_, _, _, hT, h⟩

中文:
引理 trW.mk
  条件: {T : Triangle C} (hT : T in distTriang C) (h : P T.obj₃)
  结论: P.trW T.mor₁
  证明: ⟨_, _, _, hT, h⟩
-/
lemma trW.mk {T : Triangle C} (hT : T in distTriang C) (h : P T.obj₃) : P.trW T.mor₁ :=
  ⟨_, _, _, hT, h⟩

/--
lemma `trW.mk'` / 引理 `trW.mk'`

English:
lemma trW.mk'
  statement: [P.IsStableUnderShift Int] {T : Triangle C} (hT : T in distTriang C)
  proof: by
  rw [trW_iff']
  exact ⟨_, _, _, hT, h⟩

中文:
引理 trW.mk'
  结论: [P.是StableUnderShift 整数] {T : Triangle C} (hT : T in distTriang C)
  证明: by
  rw [trW_iff']
  exact ⟨_, _, _, hT, h⟩

Depends on / 依赖: trW_iff
-/
lemma trW.mk' [P.IsStableUnderShift Int] {T : Triangle C} (hT : T in distTriang C)
    (h : P T.obj₁) : P.trW T.mor₂ := by
  rw [trW_iff']
  exact ⟨_, _, _, hT, h⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `trW_isoClosure` / 引理 `trW_isoClosure`

English:
lemma trW_isoClosure
  statement: P.isoClosure.trW = P.trW
  proof: by
  ext X Y f
  constructor
  · rintro ⟨Z, g, h, mem, ⟨Z', hZ', ⟨e⟩⟩⟩
    refine ⟨Z', g ≫ e.hom, e.inv ≫ h, isomorphic_distinguished _ mem _ ?_, hZ'⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
  · rintro ⟨Z, g, h, mem, hZ⟩
    exact ⟨Z, g, h, mem, ObjectProperty.le_isoClosure _ _ hZ⟩

中文:
引理 trW_isoClosure
  结论: P.isoClosure.trW = P.trW
  证明: by
  ext X Y f
  constructor
  · rintro ⟨Z, g, h, mem, ⟨Z', hZ', ⟨e⟩⟩⟩
    refine ⟨Z', g ≫ e.hom, e.inv ≫ h, isomorphic_distinguished _ mem _ ?_, hZ'⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
  · rintro ⟨Z, g, h, mem, hZ⟩
    exact ⟨Z, g, h, mem, ObjectProperty.le_isoClosure _ _ hZ⟩

Depends on / 依赖: Iso.refl, ObjectProperty, ObjectProperty.le_isoClosure, Triangle, Triangle.isoMk, e.hom, e.inv, e.symm, isomorphic_distinguished, le_isoClosure
-/
lemma trW_isoClosure : P.isoClosure.trW = P.trW := by
  ext X Y f
  constructor
  · rintro ⟨Z, g, h, mem, ⟨Z', hZ', ⟨e⟩⟩⟩
    refine ⟨Z', g ≫ e.hom, e.inv ≫ h, isomorphic_distinguished _ mem _ ?_, hZ'⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
  · rintro ⟨Z, g, h, mem, hZ⟩
    exact ⟨Z, g, h, mem, ObjectProperty.le_isoClosure _ _ hZ⟩

variable {P} in
/--
lemma `trW_monotone` / 引理 `trW_monotone`

English:
lemma trW_monotone
  given: {Q : ObjectProperty C} (h : P <= Q)
  statement: P.trW <= Q.trW
  proof: by
  intro X Y f hf
  rw [trW_iff] at hf ⊢
  obtain ⟨Z, a, b, hT, hZ⟩ := hf
  exact ⟨Z, a, b, hT, h _ hZ⟩

中文:
引理 trW_monotone
  条件: {Q : ObjectProperty C} (h : P <= Q)
  结论: P.trW <= Q.trW
  证明: by
  intro X Y f hf
  rw [trW_iff] at hf ⊢
  obtain ⟨Z, a, b, hT, hZ⟩ := hf
  exact ⟨Z, a, b, hT, h _ hZ⟩

Depends on / 依赖: trW_iff
-/
lemma trW_monotone {Q : ObjectProperty C} (h : P <= Q) : P.trW <= Q.trW := by
  intro X Y f hf
  rw [trW_iff] at hf ⊢
  obtain ⟨Z, a, b, hT, hZ⟩ := hf
  exact ⟨Z, a, b, hT, h _ hZ⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.trW.RespectsIso
  body: by
    rintro f ⟨Z, g, h, mem, mem'⟩
    refine ⟨Z, g, h ≫ inv e⟦(1 : Int)⟧', isomorphic_distinguished _ mem _ ?_, mem'⟩
    refine Triangle.isoMk _ _ (asIso e) (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_
    dsimp
    simp only [Functor.map_inv, assoc, IsIso.inv_hom_id, comp_id, id_comp]
  postcomp {X Y Y'} e (he : IsIso e) := by
    rintro f ⟨Z, g, h, mem, mem'⟩
    refine ⟨Z, inv e ≫ g, h, isomorphic_distinguished _ mem _ ?_, mem'⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (asIso e).symm (Iso.refl _)

中文:
实例 :
  签名: P.trW.RespectsIso
  定义体: by
    rintro f ⟨Z, g, h, mem, mem'⟩
    refine ⟨Z, g, h ≫ inv e⟦(1 : Int)⟧', isomorphic_distinguished _ mem _ ?_, mem'⟩
    refine Triangle.isoMk _ _ (asIso e) (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_
    dsimp
    simp only [Functor.map_inv, assoc, IsIso.inv_hom_id, comp_id, id_comp]
  postcomp {X Y Y'} e (he : IsIso e) := by
    rintro f ⟨Z, g, h, mem, mem'⟩
    refine ⟨Z, inv e ≫ g, h, isomorphic_distinguished _ mem _ ?_, mem'⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (asIso e).symm (Iso.refl _)

Depends on / 依赖: Functor, Functor.map_inv, IsIso.inv_hom_id, Iso.refl, Triangle, Triangle.isoMk, comp_id, id_comp, inv_hom_id, isomorphic_distinguished, map_inv, postcomp
-/
instance : P.trW.RespectsIso where
  precomp {X' X Y} e (he : IsIso e) := by
    rintro f ⟨Z, g, h, mem, mem'⟩
    refine ⟨Z, g, h ≫ inv e⟦(1 : Int)⟧', isomorphic_distinguished _ mem _ ?_, mem'⟩
    refine Triangle.isoMk _ _ (asIso e) (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_
    dsimp
    simp only [Functor.map_inv, assoc, IsIso.inv_hom_id, comp_id, id_comp]
  postcomp {X Y Y'} e (he : IsIso e) := by
    rintro f ⟨Z, g, h, mem, mem'⟩
    refine ⟨Z, inv e ≫ g, h, isomorphic_distinguished _ mem _ ?_, mem'⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (asIso e).symm (Iso.refl _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.ContainsZero]
  signature: : P.trW.ContainsIdentities
  body: by
  rw [← trW_isoClosure]
  exact ⟨fun X => ⟨_, _, _, contractible_distinguished X, prop_zero _⟩⟩

中文:
实例 [P.余ntainsZero]
  签名: : P.trW.余ntainsIdentities
  定义体: by
  rw [← trW_isoClosure]
  exact ⟨fun X => ⟨_, _, _, contractible_distinguished X, prop_zero _⟩⟩

Depends on / 依赖: contractible_distinguished, prop_zero, trW_isoClosure
-/
instance [P.ContainsZero] : P.trW.ContainsIdentities := by
  rw [← trW_isoClosure]
  exact ⟨fun X => ⟨_, _, _, contractible_distinguished X, prop_zero _⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `trW_of_isIso` / 引理 `trW_of_isIso`

English:
lemma trW_of_isIso
  given: [P.ContainsZero] {X Y : C} (f : X ⟶ Y) [IsIso f]
  statement: P.trW f
  proof: by
  refine (P.trW.arrow_mk_iso_iff ?_).1 (MorphismProperty.id_mem _ X)
  exact Arrow.isoMk (Iso.refl _) (asIso f)

中文:
引理 trW_of_isIso
  条件: [P.余ntainsZero] {X Y : C} (f : X ⟶ Y) [是同构 f]
  结论: P.trW f
  证明: by
  refine (P.trW.arrow_mk_iso_iff ?_).1 (MorphismProperty.id_mem _ X)
  exact Arrow.isoMk (Iso.refl _) (asIso f)

Depends on / 依赖: Arrow.isoMk, Iso.refl, MorphismProperty, MorphismProperty.id_mem, P.trW.arrow_mk_iso_iff, arrow_mk_iso_iff, id_mem
-/
lemma trW_of_isIso [P.ContainsZero] {X Y : C} (f : X ⟶ Y) [IsIso f] : P.trW f := by
  refine (P.trW.arrow_mk_iso_iff ?_).1 (MorphismProperty.id_mem _ X)
  exact Arrow.isoMk (Iso.refl _) (asIso f)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `smul_mem_trW_iff` / 引理 `smul_mem_trW_iff`

English:
lemma smul_mem_trW_iff
  given: {X Y : C} (f : X ⟶ Y) (n : Intˣ)
  proof: P.trW.arrow_mk_iso_iff (Arrow.isoMk (n • (Iso.refl _)) (Iso.refl _))

中文:
引理 smul_mem_trW_iff
  条件: {X Y : C} (f : X ⟶ Y) (n : 整数ˣ)
  证明: P.trW.arrow_mk_iso_iff (Arrow.isoMk (n • (Iso.refl _)) (Iso.refl _))

Depends on / 依赖: Arrow.isoMk, Iso.refl, P.trW.arrow_mk_iso_iff, arrow_mk_iso_iff
-/
lemma smul_mem_trW_iff {X Y : C} (f : X ⟶ Y) (n : Intˣ) :
    P.trW (n • f) ↔ P.trW f :=
  P.trW.arrow_mk_iso_iff (Arrow.isoMk (n • (Iso.refl _)) (Iso.refl _))

variable {P} in
/--
lemma `trW.shift` / 引理 `trW.shift`

English:
lemma trW.shift
  statement: [P.IsStableUnderShift Int]
  proof: by
  rw [← smul_mem_trW_iff _ _ (n.negOnePow)]
  obtain ⟨X₃, g, h, hT, mem⟩ := hf
  exact ⟨_, _, _, Pretriangulated.Triangle.shift_distinguished _ hT n, P.le_shift _ _ mem⟩

中文:
引理 trW.shift
  结论: [P.是StableUnderShift 整数]
  证明: by
  rw [← smul_mem_trW_iff _ _ (n.negOnePow)]
  obtain ⟨X₃, g, h, hT, mem⟩ := hf
  exact ⟨_, _, _, Pretriangulated.Triangle.shift_distinguished _ hT n, P.le_shift _ _ mem⟩

Depends on / 依赖: P.le_shift, Pretriangulated, Pretriangulated.Triangle.shift_distinguished, Triangle, le_shift, n.negOnePow, negOnePow, shift_distinguished, smul_mem_trW_iff
-/
lemma trW.shift [P.IsStableUnderShift Int]
    {X₁ X₂ : C} {f : X₁ ⟶ X₂} (hf : P.trW f) (n : Int) : P.trW (f⟦n⟧') := by
  rw [← smul_mem_trW_iff _ _ (n.negOnePow)]
  obtain ⟨X₃, g, h, hT, mem⟩ := hf
  exact ⟨_, _, _, Pretriangulated.Triangle.shift_distinguished _ hT n, P.le_shift _ _ mem⟩

/--
lemma `trW.unshift` / 引理 `trW.unshift`

English:
lemma trW.unshift
  statement: [P.IsStableUnderShift Int]
  proof: (P.trW.arrow_mk_iso_iff
     (Arrow.isoOfNatIso (shiftEquiv C n).unitIso (Arrow.mk f))).2 (hf.shift (-n))

中文:
引理 trW.unshift
  结论: [P.是StableUnderShift 整数]
  证明: (P.trW.arrow_mk_iso_iff
     (Arrow.isoOfNatIso (shiftEquiv C n).unitIso (Arrow.mk f))).2 (hf.shift (-n))

Depends on / 依赖: Arrow.isoOfNatIso, Arrow.mk, P.trW.arrow_mk_iso_iff, arrow_mk_iso_iff, hf.shift, isoOfNatIso, shiftEquiv, unitIso
-/
lemma trW.unshift [P.IsStableUnderShift Int]
    {X₁ X₂ : C} {f : X₁ ⟶ X₂} {n : Int} (hf : P.trW (f⟦n⟧')) : P.trW f :=
  (P.trW.arrow_mk_iso_iff
     (Arrow.isoOfNatIso (shiftEquiv C n).unitIso (Arrow.mk f))).2 (hf.shift (-n))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderShift
  signature: Int] : P.trW.IsCompatibleWithShift Int where
  body: by
    ext K L f
    exact ⟨fun hf => hf.unshift, fun hf => hf.shift n⟩

中文:
实例 [P.是StableUnderShift
  签名: 整数] : P.trW.是余mpatibleWithShift 整数 where
  定义体: by
    ext K L f
    exact ⟨fun hf => hf.unshift, fun hf => hf.shift n⟩

Depends on / 依赖: hf.shift, hf.unshift, unshift
-/
instance [P.IsStableUnderShift Int] : P.trW.IsCompatibleWithShift Int where
  condition n := by
    ext K L f
    exact ⟨fun hf => hf.unshift, fun hf => hf.shift n⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTriangulated
  signature: C] [P.IsTriangulated] : P.trW.IsMultiplicative where
  body: by
    rw [← trW_isoClosure]
    rintro X₁ X₂ X₃ u₁₂ u₂₃ ⟨Z₁₂, v₁₂, w₁₂, H₁₂, mem₁₂⟩ ⟨Z₂₃, v₂₃, w₂₃, H₂₃, mem₂₃⟩
    obtain ⟨Z₁₃, v₁₃, w₁₂, H₁₃⟩ := distinguished_cocone_triangle (u₁₂ ≫ u₂₃)
    exact ⟨_, _, _, H₁₃, P.isoClosure.ext_of_isTriangulatedClosed₂
      _ (someOctahedron rfl H₁₂ H₂₃ H₁₃).mem mem₁₂ mem₂₃⟩

中文:
实例 [是三角
  签名: C] [P.是三角] : P.trW.是Multiplicative where
  定义体: by
    rw [← trW_isoClosure]
    rintro X₁ X₂ X₃ u₁₂ u₂₃ ⟨Z₁₂, v₁₂, w₁₂, H₁₂, mem₁₂⟩ ⟨Z₂₃, v₂₃, w₂₃, H₂₃, mem₂₃⟩
    obtain ⟨Z₁₃, v₁₃, w₁₂, H₁₃⟩ := distinguished_cocone_triangle (u₁₂ ≫ u₂₃)
    exact ⟨_, _, _, H₁₃, P.isoClosure.ext_of_isTriangulatedClosed₂
      _ (someOctahedron rfl H₁₂ H₂₃ H₁₃).mem mem₁₂ mem₂₃⟩

Depends on / 依赖: P.isoClosure.ext_of_isTriangulatedClosed, distinguished_cocone_triangle, isoClosure, someOctahedron, trW_isoClosure
-/
instance [IsTriangulated C] [P.IsTriangulated] : P.trW.IsMultiplicative where
  comp_mem := by
    rw [← trW_isoClosure]
    rintro X₁ X₂ X₃ u₁₂ u₂₃ ⟨Z₁₂, v₁₂, w₁₂, H₁₂, mem₁₂⟩ ⟨Z₂₃, v₂₃, w₂₃, H₂₃, mem₂₃⟩
    obtain ⟨Z₁₃, v₁₃, w₁₂, H₁₃⟩ := distinguished_cocone_triangle (u₁₂ ≫ u₂₃)
    exact ⟨_, _, _, H₁₃, P.isoClosure.ext_of_isTriangulatedClosed₂
      _ (someOctahedron rfl H₁₂ H₂₃ H₁₃).mem mem₁₂ mem₂₃⟩

/--
lemma `trW_iff_of_distinguished` / 引理 `trW_iff_of_distinguished`

English:
lemma trW_iff_of_distinguished
  proof: by
  constructor
  · rintro ⟨Z, g, h, hT', mem⟩
    obtain ⟨e, _⟩ := exists_iso_of_arrow_iso _ _ hT' hT (Iso.refl _)
    exact P.prop_of_iso (Triangle.π₃.mapIso e) mem
  · intro h
    exact ⟨_, _, _, hT, h⟩

中文:
引理 trW_iff_of_distinguished
  证明: by
  constructor
  · rintro ⟨Z, g, h, hT', mem⟩
    obtain ⟨e, _⟩ := exists_iso_of_arrow_iso _ _ hT' hT (Iso.refl _)
    exact P.prop_of_iso (Triangle.π₃.mapIso e) mem
  · intro h
    exact ⟨_, _, _, hT, h⟩

Depends on / 依赖: Iso.refl, P.prop_of_iso, Triangle, exists_iso_of_arrow_iso, mapIso, prop_of_iso
-/
lemma trW_iff_of_distinguished
    [P.IsClosedUnderIsomorphisms] (T : Triangle C) (hT : T in distTriang C) :
    P.trW T.mor₁ ↔ P T.obj₃ := by
  constructor
  · rintro ⟨Z, g, h, hT', mem⟩
    obtain ⟨e, _⟩ := exists_iso_of_arrow_iso _ _ hT' hT (Iso.refl _)
    exact P.prop_of_iso (Triangle.π₃.mapIso e) mem
  · intro h
    exact ⟨_, _, _, hT, h⟩

/--
lemma `trW_iff_of_distinguished'` / 引理 `trW_iff_of_distinguished'`

English:
lemma trW_iff_of_distinguished'
  statement: [P.IsStableUnderShift Int]
  proof: by
  simpa [P.prop_shift_iff_of_isStableUnderShift]
    using! P.trW_iff_of_distinguished _ (rot_of_distTriang _ hT)

中文:
引理 trW_iff_of_distinguished'
  结论: [P.是StableUnderShift 整数]
  证明: by
  simpa [P.prop_shift_iff_of_isStableUnderShift]
    using! P.trW_iff_of_distinguished _ (rot_of_distTriang _ hT)

Depends on / 依赖: P.prop_shift_iff_of_isStableUnderShift, P.trW_iff_of_distinguished, prop_shift_iff_of_isStableUnderShift, rot_of_distTriang, trW_iff_of_distinguished
-/
lemma trW_iff_of_distinguished' [P.IsStableUnderShift Int]
    [P.IsClosedUnderIsomorphisms] (T : Triangle C) (hT : T in distTriang C) :
    P.trW T.mor₂ ↔ P T.obj₁ := by
  simpa [P.prop_shift_iff_of_isStableUnderShift]
    using! P.trW_iff_of_distinguished _ (rot_of_distTriang _ hT)

section

variable (F : D ⥤ C) [F.CommShift Int] [F.IsTriangulated]
  [P.IsClosedUnderIsomorphisms]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsTriangulated]
  signature: : (P.inverseImage F).IsTriangulated where
  body: .mk' (fun T hT h₁ h₃ =>
    P.ext_of_isTriangulatedClosed₂ _ (F.map_distinguished T hT) h₁ h₃)

中文:
实例 [P.是三角]
  签名: : (P.inverseImage F).是三角 where
  定义体: .mk' (fun T hT h₁ h₃ =>
    P.ext_of_isTriangulatedClosed₂ _ (F.map_distinguished T hT) h₁ h₃)
-/
instance [P.IsTriangulated] : (P.inverseImage F).IsTriangulated where
  toIsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ =>
    P.ext_of_isTriangulatedClosed₂ _ (F.map_distinguished T hT) h₁ h₃)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `inverseImage_trW_iff` / 引理 `inverseImage_trW_iff`

English:
lemma inverseImage_trW_iff
  given: {X Y : D} (s : X ⟶ Y)
  proof: by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle s
  have eq₁ := (P.inverseImage F).trW_iff_of_distinguished _ hT
  have eq₂ := P.trW_iff_of_distinguished _ (F.map_distinguished _ hT)
  dsimp at eq₁ eq₂
  rw [eq₁]; rw [prop_inverseImage_iff]; rw [eq₂]

中文:
引理 inverseImage_trW_iff
  条件: {X Y : D} (s : X ⟶ Y)
  证明: by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle s
  have eq₁ := (P.inverseImage F).trW_iff_of_distinguished _ hT
  have eq₂ := P.trW_iff_of_distinguished _ (F.map_distinguished _ hT)
  dsimp at eq₁ eq₂
  rw [eq₁]; rw [prop_inverseImage_iff]; rw [eq₂]

Depends on / 依赖: F.map_distinguished, P.inverseImage, P.trW_iff_of_distinguished, distinguished_cocone_triangle, inverseImage, map_distinguished, prop_inverseImage_iff, trW_iff_of_distinguished
-/
lemma inverseImage_trW_iff {X Y : D} (s : X ⟶ Y) :
    (P.inverseImage F).trW s ↔ P.trW (F.map s) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle s
  have eq₁ := (P.inverseImage F).trW_iff_of_distinguished _ hT
  have eq₂ := P.trW_iff_of_distinguished _ (F.map_distinguished _ hT)
  dsimp at eq₁ eq₂
  rw [eq₁]; rw [prop_inverseImage_iff]; rw [eq₂]

/--
lemma `inverseImage_trW_isInverted` / 引理 `inverseImage_trW_isInverted`

English:
lemma inverseImage_trW_isInverted
  statement: {E : Type*} [Category E]
  proof: fun X Y f hf => Localization.inverts L P.trW (F.map f)
    (by simpa only [inverseImage_trW_iff] using hf)

中文:
引理 inverseImage_trW_isInverted
  结论: {E : 类型} [范畴 E]
  证明: fun X Y f hf => Localization.inverts L P.trW (F.map f)
    (by simpa only [inverseImage_trW_iff] using hf)

Depends on / 依赖: F.map, Localization, Localization.inverts, P.trW, inverseImage_trW_iff, inverts
-/
lemma inverseImage_trW_isInverted {E : Type*} [Category E]
    (L : C ⥤ E) [L.IsLocalization P.trW] :
    (P.inverseImage F).trW.IsInvertedBy (F ⋙ L) :=
  fun X Y f hf => Localization.inverts L P.trW (F.map f)
    (by simpa only [inverseImage_trW_iff] using hf)

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTriangulated
  signature: C] [P.IsTriangulated] : P.trW.HasLeftCalculusOfFractions where
  body: by
    obtain ⟨Z, f, g, H, mem⟩ := φ.hs
    obtain ⟨Y', s', f', mem'⟩ := distinguished_cocone_triangle₂ (g ≫ φ.f⟦1⟧')
    obtain ⟨b, ⟨hb₁, _⟩⟩ :=
      complete_distinguished_triangle_morphism₂ _ _ H mem' φ.f (𝟙 Z) (by simp)
    exact ⟨MorphismProperty.LeftFraction.mk b s' ⟨_, _, _, mem', mem⟩, hb₁.symm⟩
  ext := by
    rintro X' X Y f₁ f₂ s ⟨Z, g, h, H, mem⟩ hf₁
    have hf₂ : s ≫ (f₁ - f₂) = 0 := by rw [comp_sub, hf₁, sub_self]
    obtain ⟨q, hq⟩ := Triangle.yoneda_exact₂ _ H _ hf₂
    obtain ⟨Y', r, t, mem'⟩ := distinguished_cocone_triangle q
    refine ⟨Y', r, ?_, ?_⟩
    · exact ⟨_, _, _, rot_of_distTriang _ mem', P.le_shift _ _ mem⟩
    · have eq := comp_distTriang_mor_zero₁₂ _ mem'
      dsimp at eq
      rw [← sub_eq_zero]; rw [← sub_comp]; rw [hq]; rw [assoc]; rw [eq]; rw [comp_zero]

中文:
实例 [是三角
  签名: C] [P.是三角] : P.trW.有LeftCalculusOfFractions where
  定义体: by
    obtain ⟨Z, f, g, H, mem⟩ := φ.hs
    obtain ⟨Y', s', f', mem'⟩ := distinguished_cocone_triangle₂ (g ≫ φ.f⟦1⟧')
    obtain ⟨b, ⟨hb₁, _⟩⟩ :=
      complete_distinguished_triangle_morphism₂ _ _ H mem' φ.f (𝟙 Z) (by simp)
    exact ⟨MorphismProperty.LeftFraction.mk b s' ⟨_, _, _, mem', mem⟩, hb₁.symm⟩
  ext := by
    rintro X' X Y f₁ f₂ s ⟨Z, g, h, H, mem⟩ hf₁
    have hf₂ : s ≫ (f₁ - f₂) = 0 := by rw [comp_sub, hf₁, sub_self]
    obtain ⟨q, hq⟩ := Triangle.yoneda_exact₂ _ H _ hf₂
    obtain ⟨Y', r, t, mem'⟩ := distinguished_cocone_triangle q
    refine ⟨Y', r, ?_, ?_⟩
    · exact ⟨_, _, _, rot_of_distTriang _ mem', P.le_shift _ _ mem⟩
    · have eq := comp_distTriang_mor_zero₁₂ _ mem'
      dsimp at eq
      rw [← sub_eq_zero]; rw [← sub_comp]; rw [hq]; rw [assoc]; rw [eq]; rw [comp_zero]

Depends on / 依赖: LeftFraction, MorphismProperty, MorphismProperty.LeftFraction.mk, Triangle, Triangle.yoneda_exact, comp_sub, distinguished_cocone, sub_self
-/
instance [IsTriangulated C] [P.IsTriangulated] : P.trW.HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ := by
    obtain ⟨Z, f, g, H, mem⟩ := φ.hs
    obtain ⟨Y', s', f', mem'⟩ := distinguished_cocone_triangle₂ (g ≫ φ.f⟦1⟧')
    obtain ⟨b, ⟨hb₁, _⟩⟩ :=
      complete_distinguished_triangle_morphism₂ _ _ H mem' φ.f (𝟙 Z) (by simp)
    exact ⟨MorphismProperty.LeftFraction.mk b s' ⟨_, _, _, mem', mem⟩, hb₁.symm⟩
  ext := by
    rintro X' X Y f₁ f₂ s ⟨Z, g, h, H, mem⟩ hf₁
    have hf₂ : s ≫ (f₁ - f₂) = 0 := by rw [comp_sub, hf₁, sub_self]
    obtain ⟨q, hq⟩ := Triangle.yoneda_exact₂ _ H _ hf₂
    obtain ⟨Y', r, t, mem'⟩ := distinguished_cocone_triangle q
    refine ⟨Y', r, ?_, ?_⟩
    · exact ⟨_, _, _, rot_of_distTriang _ mem', P.le_shift _ _ mem⟩
    · have eq := comp_distTriang_mor_zero₁₂ _ mem'
      dsimp at eq
      rw [← sub_eq_zero]; rw [← sub_comp]; rw [hq]; rw [assoc]; rw [eq]; rw [comp_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTriangulated
  signature: C] [P.IsTriangulated] : P.trW.HasRightCalculusOfFractions where
  body: by
    obtain ⟨Z, f, g, H, mem⟩ := φ.hs
    obtain ⟨X', f', h', mem'⟩ := distinguished_cocone_triangle₁ (φ.f ≫ f)
    obtain ⟨a, ⟨ha₁, _⟩⟩ := complete_distinguished_triangle_morphism₁ _ _
      mem' H φ.f (𝟙 Z) (by simp)
    exact ⟨MorphismProperty.RightFraction.mk f' ⟨_, _, _, mem', mem⟩ a, ha₁⟩
  ext Y Z Z' f₁ f₂ s hs hf₁ := by
    rw [P.trW_iff'] at hs
    obtain ⟨Z, g, h, H, mem⟩ := hs
    have hf₂ : (f₁ - f₂) ≫ s = 0 := by rw [sub_comp, hf₁, sub_self]
    obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ _ H _ hf₂
    obtain ⟨Y', r, t, mem'⟩ := distinguished_cocone_triangle₁ q
    refine ⟨Y', r, ?_, ?_⟩
    · exact ⟨_, _, _, mem', mem⟩
    · have eq := comp_distTriang_mor_zero₁₂ _ mem'
      dsimp at eq
      rw [← sub_eq_zero]; rw [← comp_sub]; rw [hq]; rw [reassoc_of% eq]; rw [zero_comp]

中文:
实例 [是三角
  签名: C] [P.是三角] : P.trW.有RightCalculusOfFractions where
  定义体: by
    obtain ⟨Z, f, g, H, mem⟩ := φ.hs
    obtain ⟨X', f', h', mem'⟩ := distinguished_cocone_triangle₁ (φ.f ≫ f)
    obtain ⟨a, ⟨ha₁, _⟩⟩ := complete_distinguished_triangle_morphism₁ _ _
      mem' H φ.f (𝟙 Z) (by simp)
    exact ⟨MorphismProperty.RightFraction.mk f' ⟨_, _, _, mem', mem⟩ a, ha₁⟩
  ext Y Z Z' f₁ f₂ s hs hf₁ := by
    rw [P.trW_iff'] at hs
    obtain ⟨Z, g, h, H, mem⟩ := hs
    have hf₂ : (f₁ - f₂) ≫ s = 0 := by rw [sub_comp, hf₁, sub_self]
    obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ _ H _ hf₂
    obtain ⟨Y', r, t, mem'⟩ := distinguished_cocone_triangle₁ q
    refine ⟨Y', r, ?_, ?_⟩
    · exact ⟨_, _, _, mem', mem⟩
    · have eq := comp_distTriang_mor_zero₁₂ _ mem'
      dsimp at eq
      rw [← sub_eq_zero]; rw [← comp_sub]; rw [hq]; rw [reassoc_of% eq]; rw [zero_comp]

Depends on / 依赖: MorphismProperty, MorphismProperty.RightFraction.mk, P.trW_iff, RightFraction, Triangle, Triangle.coyoneda_exact, sub_comp, sub_self, trW_iff
-/
instance [IsTriangulated C] [P.IsTriangulated] : P.trW.HasRightCalculusOfFractions where
  exists_rightFraction X Y φ := by
    obtain ⟨Z, f, g, H, mem⟩ := φ.hs
    obtain ⟨X', f', h', mem'⟩ := distinguished_cocone_triangle₁ (φ.f ≫ f)
    obtain ⟨a, ⟨ha₁, _⟩⟩ := complete_distinguished_triangle_morphism₁ _ _
      mem' H φ.f (𝟙 Z) (by simp)
    exact ⟨MorphismProperty.RightFraction.mk f' ⟨_, _, _, mem', mem⟩ a, ha₁⟩
  ext Y Z Z' f₁ f₂ s hs hf₁ := by
    rw [P.trW_iff'] at hs
    obtain ⟨Z, g, h, H, mem⟩ := hs
    have hf₂ : (f₁ - f₂) ≫ s = 0 := by rw [sub_comp, hf₁, sub_self]
    obtain ⟨q, hq⟩ := Triangle.coyoneda_exact₂ _ H _ hf₂
    obtain ⟨Y', r, t, mem'⟩ := distinguished_cocone_triangle₁ q
    refine ⟨Y', r, ?_, ?_⟩
    · exact ⟨_, _, _, mem', mem⟩
    · have eq := comp_distTriang_mor_zero₁₂ _ mem'
      dsimp at eq
      rw [← sub_eq_zero]; rw [← comp_sub]; rw [hq]; rw [reassoc_of% eq]; rw [zero_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTriangulated
  signature: C] [P.IsTriangulated] : P.trW.IsCompatibleWithTriangulation
  body: ⟨by
  rintro T₁ T₃ mem₁ mem₃ a b ⟨Z₅, g₅, h₅, mem₅, mem₅'⟩ ⟨Z₄, g₄, h₄, mem₄, mem₄'⟩ comm
  obtain ⟨Z₂, g₂, h₂, mem₂⟩ := distinguished_cocone_triangle (T₁.mor₁ ≫ b)
  have H := someOctahedron rfl mem₁ mem₄ mem₂
  have H' := someOctahedron comm.symm mem₅ mem₃ mem₂
  let φ : T₁ ⟶ T₃ := H.triangleMorphism₁ ≫ H'.triangleMorphism₂
  exact ⟨φ.hom₃, P.trW.comp_mem _ _ (trW.mk P H.mem mem₄') (trW.mk' P H'.mem mem₅'),
    by simpa [φ] using φ.comm₂, by simpa [φ] using φ.comm₃⟩⟩

中文:
实例 [是三角
  签名: C] [P.是三角] : P.trW.是余mpatibleWithTriangulation
  定义体: ⟨by
  rintro T₁ T₃ mem₁ mem₃ a b ⟨Z₅, g₅, h₅, mem₅, mem₅'⟩ ⟨Z₄, g₄, h₄, mem₄, mem₄'⟩ comm
  obtain ⟨Z₂, g₂, h₂, mem₂⟩ := distinguished_cocone_triangle (T₁.mor₁ ≫ b)
  have H := someOctahedron rfl mem₁ mem₄ mem₂
  have H' := someOctahedron comm.symm mem₅ mem₃ mem₂
  let φ : T₁ ⟶ T₃ := H.triangleMorphism₁ ≫ H'.triangleMorphism₂
  exact ⟨φ.hom₃, P.trW.comp_mem _ _ (trW.mk P H.mem mem₄') (trW.mk' P H'.mem mem₅'),
    by simpa [φ] using φ.comm₂, by simpa [φ] using φ.comm₃⟩⟩

Depends on / 依赖: H.mem, H.triangleMorphism, P.trW.comp_mem, comm.symm, comp_mem, distinguished_cocone_triangle, someOctahedron, trW.mk
-/
instance [IsTriangulated C] [P.IsTriangulated] : P.trW.IsCompatibleWithTriangulation := ⟨by
  rintro T₁ T₃ mem₁ mem₃ a b ⟨Z₅, g₅, h₅, mem₅, mem₅'⟩ ⟨Z₄, g₄, h₄, mem₄, mem₄'⟩ comm
  obtain ⟨Z₂, g₂, h₂, mem₂⟩ := distinguished_cocone_triangle (T₁.mor₁ ≫ b)
  have H := someOctahedron rfl mem₁ mem₄ mem₂
  have H' := someOctahedron comm.symm mem₅ mem₃ mem₂
  let φ : T₁ ⟶ T₃ := H.triangleMorphism₁ ≫ H'.triangleMorphism₂
  exact ⟨φ.hom₃, P.trW.comp_mem _ _ (trW.mk P H.mem mem₄') (trW.mk' P H'.mem mem₅'),
    by simpa [φ] using φ.comm₂, by simpa [φ] using φ.comm₃⟩⟩

instance (P' : ObjectProperty C) [P.IsTriangulatedClosed₂] [P.IsClosedUnderIsomorphisms]
    [P'.IsTriangulatedClosed₂] :
    (P ⊓ P').IsTriangulatedClosed₂ where
  ext₂' T hT h₁ h₃ := by
    obtain ⟨X₂, h₂, ⟨e⟩⟩ := P'.ext_of_isTriangulatedClosed₂' T hT h₁.2 h₃.2
    exact ⟨X₂, ⟨P.prop_of_iso e (P.ext_of_isTriangulatedClosed₂ T hT h₁.1 h₃.1), h₂⟩, ⟨e⟩⟩

instance (P' : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    [P'.IsTriangulated] :
    (P ⊓ P').IsTriangulated where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsTriangulated]
  signature: [P.IsClosedUnderIsomorphisms]
  body: by
    rintro X ⟨p⟩
    refine P.prop_of_iso ?_ (P.ext_of_isTriangulatedClosed₂ _
      (binaryProductTriangle_distinguished _ _)
      (p.prop_diag_obj (.mk .left)) (p.prop_diag_obj (.mk .right)))
    exact IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

中文:
实例 [P.是三角]
  签名: [P.在同构下封闭]
  定义体: by
    rintro X ⟨p⟩
    refine P.prop_of_iso ?_ (P.ext_of_isTriangulatedClosed₂ _
      (binaryProductTriangle_distinguished _ _)
      (p.prop_diag_obj (.mk .left)) (p.prop_diag_obj (.mk .right)))
    exact IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, IsLimit.postcomposeHomEquiv, P.ext_of_isTriangulatedClosed, P.prop_of_iso, binaryProductTriangle_distinguished, conePointUniqueUpToIso, diagramIsoPair, isLimit, p.diag, p.isLimit, p.prop_diag_obj, postcomposeHomEquiv, prodIsProd, prop_diag_obj, prop_of_iso
-/
instance [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] :
    P.IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    refine P.prop_of_iso ?_ (P.ext_of_isTriangulatedClosed₂ _
      (binaryProductTriangle_distinguished _ _)
      (p.prop_diag_obj (.mk .left)) (p.prop_diag_obj (.mk .right)))
    exact IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsTriangulated]
  signature: [P.IsClosedUnderIsomorphisms]
  body: .mk'

中文:
实例 [P.是三角]
  签名: [P.在同构下封闭]
  定义体: .mk'
-/
instance [P.IsTriangulated] [P.IsClosedUnderIsomorphisms] :
    P.IsClosedUnderFiniteProducts := .mk'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsTriangulated]
  signature: : P.trW.IsStableUnderFiniteProducts
  body: by
  rw [← trW_isoClosure]
  exact ⟨fun J _ => by
    refine MorphismProperty.IsStableUnderProductsOfShape.mk _ _ ?_
    intro _ _ X₁ X₂ f hf
    exact trW.mk _ (productTriangle_distinguished _
      (fun j => (hf j).choose_spec.choose_spec.choose_spec.choose))
      (P.isoClosure.prop_pi _
        (fun j => (hf j).choose_spec.choose_spec.choose_spec.choose_spec))⟩

中文:
实例 [P.是三角]
  签名: : P.trW.是StableUnderFiniteProducts
  定义体: by
  rw [← trW_isoClosure]
  exact ⟨fun J _ => by
    refine MorphismProperty.IsStableUnderProductsOfShape.mk _ _ ?_
    intro _ _ X₁ X₂ f hf
    exact trW.mk _ (productTriangle_distinguished _
      (fun j => (hf j).choose_spec.choose_spec.choose_spec.choose))
      (P.isoClosure.prop_pi _
        (fun j => (hf j).choose_spec.choose_spec.choose_spec.choose_spec))⟩

Depends on / 依赖: IsStableUnderProductsOfShape, MorphismProperty, MorphismProperty.IsStableUnderProductsOfShape.mk, P.isoClosure.prop_pi, choose_spec, choose_spec.choose_spec.choose_spec.choose, choose_spec.choose_spec.choose_spec.choose_spec, isoClosure, productTriangle_distinguished, prop_pi, trW.mk, trW_isoClosure
-/
instance [P.IsTriangulated] : P.trW.IsStableUnderFiniteProducts := by
  rw [← trW_isoClosure]
  exact ⟨fun J _ => by
    refine MorphismProperty.IsStableUnderProductsOfShape.mk _ _ ?_
    intro _ _ X₁ X₂ f hf
    exact trW.mk _ (productTriangle_distinguished _
      (fun j => (hf j).choose_spec.choose_spec.choose_spec.choose))
      (P.isoClosure.prop_pi _
        (fun j => (hf j).choose_spec.choose_spec.choose_spec.choose_spec))⟩

section

variable [P.IsTriangulated]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pretriangulated P.FullSubcategory
  body: P.ι.mapTriangle.obj ⁻¹' (distTriang C)
  isomorphic_distinguished T₁ hT₁ T₂ e :=
    isomorphic_distinguished _ hT₁ _ (P.ι.mapTriangle.mapIso e)
  contractible_distinguished X :=
    isomorphic_distinguished _ (contractible_distinguished (P.ι.obj X)) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) P.ι.mapZeroObject)
  distinguished_cocone_triangle {X Y} f := by
    obtain ⟨Z', g', h', mem⟩ := distinguished_cocone_triangle (P.ι.map f)
    obtain ⟨Z'', hZ'', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₃' _ mem X.2 Y.2
    exact ⟨⟨Z'', hZ''⟩, P.fullyFaithfulι.preimage (g' ≫ e.hom),
      P.fullyFaithfulι.preimage (e.inv ≫ h' ≫ (P.ι.commShiftIso (1 : Int)).inv.app X),
      isomorphic_distinguished _ mem _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm)⟩
  rotate_distinguished_triangle T :=
    (rotate_distinguished_triangle (P.ι.mapTriangle.obj T)).trans
      (distinguished_iff_of_iso (P.ι.mapTriangleRotateIso.app T))
  complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ a b comm := by
    obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := complete_distinguished_triangle_morphism (P.ι.mapTriangle.obj T₁)
      (P.ι.mapTriangle.obj T₂) hT₁ hT₂ (P.ι.map a) (P.ι.map b)
      (by simpa using P.ι.congr_map comm)
    refine ⟨P.fullyFaithfulι.preimage c, ⟨by cat_disch, ?_⟩⟩
    ext
    have := P.ι.commShiftIso_hom_naturality a (1 : Int)
    rw [← cancel_mono ((Functor.commShiftIso P.ι (1 : Int)).hom.app T₂.obj₁)]
    cat_disch

中文:
实例 :
  签名: 预三角 P.满子范畴
  定义体: P.ι.mapTriangle.obj ⁻¹' (distTriang C)
  isomorphic_distinguished T₁ hT₁ T₂ e :=
    isomorphic_distinguished _ hT₁ _ (P.ι.mapTriangle.mapIso e)
  contractible_distinguished X :=
    isomorphic_distinguished _ (contractible_distinguished (P.ι.obj X)) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) P.ι.mapZeroObject)
  distinguished_cocone_triangle {X Y} f := by
    obtain ⟨Z', g', h', mem⟩ := distinguished_cocone_triangle (P.ι.map f)
    obtain ⟨Z'', hZ'', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₃' _ mem X.2 Y.2
    exact ⟨⟨Z'', hZ''⟩, P.fullyFaithfulι.preimage (g' ≫ e.hom),
      P.fullyFaithfulι.preimage (e.inv ≫ h' ≫ (P.ι.commShiftIso (1 : Int)).inv.app X),
      isomorphic_distinguished _ mem _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm)⟩
  rotate_distinguished_triangle T :=
    (rotate_distinguished_triangle (P.ι.mapTriangle.obj T)).trans
      (distinguished_iff_of_iso (P.ι.mapTriangleRotateIso.app T))
  complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ a b comm := by
    obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := complete_distinguished_triangle_morphism (P.ι.mapTriangle.obj T₁)
      (P.ι.mapTriangle.obj T₂) hT₁ hT₂ (P.ι.map a) (P.ι.map b)
      (by simpa using P.ι.congr_map comm)
    refine ⟨P.fullyFaithfulι.preimage c, ⟨by cat_disch, ?_⟩⟩
    ext
    have := P.ι.commShiftIso_hom_naturality a (1 : Int)
    rw [← cancel_mono ((Functor.commShiftIso P.ι (1 : Int)).hom.app T₂.obj₁)]
    cat_disch

Depends on / 依赖: distTriang, mapTriangle, mapTriangle.obj
-/
noncomputable instance : Pretriangulated P.FullSubcategory where
  distinguishedTriangles := P.ι.mapTriangle.obj ⁻¹' (distTriang C)
  isomorphic_distinguished T₁ hT₁ T₂ e :=
    isomorphic_distinguished _ hT₁ _ (P.ι.mapTriangle.mapIso e)
  contractible_distinguished X :=
    isomorphic_distinguished _ (contractible_distinguished (P.ι.obj X)) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) P.ι.mapZeroObject)
  distinguished_cocone_triangle {X Y} f := by
    obtain ⟨Z', g', h', mem⟩ := distinguished_cocone_triangle (P.ι.map f)
    obtain ⟨Z'', hZ'', ⟨e⟩⟩ := P.ext_of_isTriangulatedClosed₃' _ mem X.2 Y.2
    exact ⟨⟨Z'', hZ''⟩, P.fullyFaithfulι.preimage (g' ≫ e.hom),
      P.fullyFaithfulι.preimage (e.inv ≫ h' ≫ (P.ι.commShiftIso (1 : Int)).inv.app X),
      isomorphic_distinguished _ mem _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm)⟩
  rotate_distinguished_triangle T :=
    (rotate_distinguished_triangle (P.ι.mapTriangle.obj T)).trans
      (distinguished_iff_of_iso (P.ι.mapTriangleRotateIso.app T))
  complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ a b comm := by
    obtain ⟨c, ⟨hc₁, hc₂⟩⟩ := complete_distinguished_triangle_morphism (P.ι.mapTriangle.obj T₁)
      (P.ι.mapTriangle.obj T₂) hT₁ hT₂ (P.ι.map a) (P.ι.map b)
      (by simpa using P.ι.congr_map comm)
    refine ⟨P.fullyFaithfulι.preimage c, ⟨by cat_disch, ?_⟩⟩
    ext
    have := P.ι.commShiftIso_hom_naturality a (1 : Int)
    rw [← cancel_mono ((Functor.commShiftIso P.ι (1 : Int)).hom.app T₂.obj₁)]
    cat_disch

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.ι.IsTriangulated
  body: hT

中文:
实例 :
  签名: P.ι.是三角
  定义体: hT
-/
instance : P.ι.IsTriangulated where
  map_distinguished _ hT := hT

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTriangulated
  signature: C] : IsTriangulated P.FullSubcategory
  body: IsTriangulated.of_fully_faithful_triangulated_functor P.ι

中文:
实例 [是三角
  签名: C] : 是三角 P.满子范畴
  定义体: IsTriangulated.of_fully_faithful_triangulated_functor P.ι

Depends on / 依赖: IsTriangulated, IsTriangulated.of_fully_faithful_triangulated_functor, of_fully_faithful_triangulated_functor
-/
instance [IsTriangulated C] : IsTriangulated P.FullSubcategory :=
  IsTriangulated.of_fully_faithful_triangulated_functor P.ι

set_option backward.defeqAttrib.useBackward true in
instance (F : C ⥤ D) [F.CommShift Int] [F.IsTriangulated] [F.Full] :
    F.essImage.IsTriangulated where
  isStableUnderShiftBy n :=
    { le_shift := by
        rintro Y ⟨X, ⟨e⟩⟩
        exact ⟨X⟦n⟧, ⟨(F.commShiftIso n).app _ ≪≫ (shiftFunctor D n).mapIso e⟩⟩ }
  exists_zero := ⟨0, isZero_zero D, ⟨0, ⟨F.mapZeroObject⟩⟩⟩
  toIsTriangulatedClosed₂ := .mk' (by
    rintro T hT ⟨X₁, ⟨e₁⟩⟩ ⟨X₃, ⟨e₃⟩⟩
    have ⟨h, hh⟩ := F.map_surjective (e₃.hom ≫ T.mor₃ ≫ e₁.inv⟦1⟧' ≫
      (F.commShiftIso (1 : Int)).inv.app X₁)
    obtain ⟨X₂, f, g, H⟩ := distinguished_cocone_triangle₂ h
    exact ⟨X₂, ⟨Triangle.π₂.mapIso
      (isoTriangleOfIso₁₃ _ _ (F.map_distinguished _ H) hT e₁ e₃
        (by simp [hh, ← Functor.map_comp]))⟩⟩)

/--
Instance `isTriangulated_lift` / 实例 `isTriangulated_lift`

English:
instance isTriangulated_lift
  signature: (F : E ⥤ C) (hF : forall (X : E), P (F.obj X))
  body: by
  rw [Functor.isTriangulated_iff_comp_right (P.liftCompιIso F hF)]
  infer_instance

中文:
实例 isTriangulated_lift
  签名: (F : E ⥤ C) (hF : 对任意 (X : E), P (F.obj X))
  定义体: by
  rw [Functor.isTriangulated_iff_comp_right (P.liftCompιIso F hF)]
  infer_instance

Depends on / 依赖: Functor, Functor.isTriangulated_iff_comp_right, P.liftComp, infer_instance, isTriangulated_iff_comp_right
-/
instance isTriangulated_lift (F : E ⥤ C) (hF : forall (X : E), P (F.obj X))
    [Preadditive E] [F.CommShift Int] [HasZeroObject E]
    [forall (n : Int), (shiftFunctor E n).Additive] [Pretriangulated E] [F.IsTriangulated] :
    (P.lift F hF).IsTriangulated := by
  rw [Functor.isTriangulated_iff_comp_right (P.liftCompιIso F hF)]
  infer_instance

instance {D : Type*} [Category D] [HasZeroObject D] [Preadditive D]
    [HasShift D Int] [forall (n : Int), (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift Int] [F.IsTriangulated] [F.Full] :
    (P.map F).IsTriangulated := by
  rw [← F.essImage_ι_comp]
  infer_instance

end

end ObjectProperty

end CategoryTheory
