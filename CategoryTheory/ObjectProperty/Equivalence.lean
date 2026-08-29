/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Order.BooleanAlgebra.Defs

/-!
# Equivalence of full subcategories

The inclusion functor `P.FullSubcategory ⥤ Q.FullSubcategory` induced
by an inequality `P ≤ Q` in `ObjectProperty C` is an equivalence iff
`Q ≤ P.isoClosure`.

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] {P Q : ObjectProperty C} (h : P <= Q)

/--
lemma `essSurj_ιOfLE_iff` / 引理 `essSurj_ιOfLE_iff`

English:
lemma essSurj_ιOfLE_iff
  statement: (ιOfLE h).EssSurj ↔ Q <= P.isoClosure
  proof: by
  refine ⟨fun _ X hX => ?_, fun hPQ => ⟨fun ⟨Y, hY⟩ => ?_⟩⟩
  · exact ⟨_, ((ιOfLE h).objPreimage ⟨X, hX⟩).2,
      ⟨Q.ι.mapIso ((ιOfLE h).objObjPreimageIso ⟨X, hX⟩).symm⟩⟩
  · obtain ⟨X, hX, ⟨e⟩⟩ := hPQ _ hY
    exact ⟨⟨X, hX⟩, ⟨Q.ι.preimageIso e.symm⟩⟩

中文:
引理 essSurj_ιOfLE_iff
  结论: (ιOfLE h).本质满射 ↔ Q <= P.isoClosure
  证明: by
  refine ⟨fun _ X hX => ?_, fun hPQ => ⟨fun ⟨Y, hY⟩ => ?_⟩⟩
  · exact ⟨_, ((ιOfLE h).objPreimage ⟨X, hX⟩).2,
      ⟨Q.ι.mapIso ((ιOfLE h).objObjPreimageIso ⟨X, hX⟩).symm⟩⟩
  · obtain ⟨X, hX, ⟨e⟩⟩ := hPQ _ hY
    exact ⟨⟨X, hX⟩, ⟨Q.ι.preimageIso e.symm⟩⟩

Depends on / 依赖: e.symm, mapIso, objObjPreimageIso, objPreimage, preimageIso
-/
lemma essSurj_ιOfLE_iff : (ιOfLE h).EssSurj ↔ Q <= P.isoClosure := by
  refine ⟨fun _ X hX => ?_, fun hPQ => ⟨fun ⟨Y, hY⟩ => ?_⟩⟩
  · exact ⟨_, ((ιOfLE h).objPreimage ⟨X, hX⟩).2,
      ⟨Q.ι.mapIso ((ιOfLE h).objObjPreimageIso ⟨X, hX⟩).symm⟩⟩
  · obtain ⟨X, hX, ⟨e⟩⟩ := hPQ _ hY
    exact ⟨⟨X, hX⟩, ⟨Q.ι.preimageIso e.symm⟩⟩

/--
lemma `isEquivalence_ιOfLE_iff` / 引理 `isEquivalence_ιOfLE_iff`

English:
lemma isEquivalence_ιOfLE_iff
  statement: (ιOfLE h).IsEquivalence ↔ Q <= P.isoClosure
  proof: by
  rw [← essSurj_ιOfLE_iff h]
  exact ⟨fun _ => inferInstance, fun _ => { }⟩

中文:
引理 isEquivalence_ιOfLE_iff
  结论: (ιOfLE h).是等价 ↔ Q <= P.isoClosure
  证明: by
  rw [← essSurj_ιOfLE_iff h]
  exact ⟨fun _ => inferInstance, fun _ => { }⟩

Depends on / 依赖: IsZero, IsZero.of_iso, infer_instance, isGE_iff_isZero_truncLT_obj, of_iso, t.isGE_iff_isZero_truncLT_obj, t.isIso, t.triangleLTGE_distinguished, t.truncLT, triangleLTGE_distinguished, truncLT
-/
lemma isEquivalence_ιOfLE_iff : (ιOfLE h).IsEquivalence ↔ Q <= P.isoClosure := by
  rw [← essSurj_ιOfLE_iff h]
  exact ⟨fun _ => inferInstance, fun _ => { }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ιOfLE P.le_isoClosure).IsEquivalence
  body: by rw [isEquivalence_ιOfLE_iff]

中文:
实例 :
  签名: (ιOfLE P.le_isoClosure).是等价
  定义体: by rw [isEquivalence_ιOfLE_iff]

Depends on / 依赖: IsZero, IsZero.of_iso, infer_instance, isLE_iff_isZero_truncGE_obj, of_iso, t.isIso, t.isLE_iff_isZero_truncGE_obj, t.triangleLTGE_distinguished, t.truncGE, triangleLTGE_distinguished, truncGE
-/
instance : (ιOfLE P.le_isoClosure).IsEquivalence := by rw [isEquivalence_ιOfLE_iff]

set_option backward.defeqAttrib.useBackward true in
variable (C) in
/-- The equivalence between the full subcategory `⊤` of a category `C` and `C` itself. -/
@[simps]
/--
Definition of `topEquivalence` / `topEquivalence` 的定义

English:
definition topEquivalence
  signature: : ObjectProperty.FullSubcategory (C := C) ⊤ ≌ C where
  body: ObjectProperty.ι _
  inverse := ObjectProperty.lift _ (𝟭 _) (by simp)
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp := by cat_disch

中文:
定义 topEquivalence
  签名: : ObjectProperty.满子范畴 (C := C) ⊤ ≌ C where
  定义体: ObjectProperty.ι _
  inverse := ObjectProperty.lift _ (𝟭 _) (by simp)
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp := by cat_disch

Depends on / 依赖: infer_instance
-/
def topEquivalence : ObjectProperty.FullSubcategory (C := C) ⊤ ≌ C where
  functor := ObjectProperty.ι _
  inverse := ObjectProperty.lift _ (𝟭 _) (by simp)
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp := by cat_disch

end CategoryTheory.ObjectProperty

namespace CategoryTheory.Equivalence

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {P : ObjectProperty C} {Q : ObjectProperty D} (e : C ≌ D)

/-- The equivalence of categories between two fullsubcategories `P` and `Q`
of categories `C` and `D` that is induced by an equivalence `e : C ≌ D`
when `Q.inverseImage e.functor = P` and `Q` respects isomorphisms. -/
@[simps]
/--
Definition of `congrFullSubcategory` / `congrFullSubcategory` 的定义

English:
definition congrFullSubcategory
  signature: [Q.IsClosedUnderIsomorphisms] (h : Q.inverseImage e.functor = P)
  body: Q.lift (P.ι ⋙ e.functor) (fun ⟨X, hX⟩ => by rwa [← h] at hX)
  inverse := P.lift (Q.ι ⋙ e.inverse) (fun ⟨Y, hY⟩ => by
    rw [← h]
    exact Q.prop_of_iso (e.counitIso.app Y).symm hY)
  unitIso := (P.fullyFaithfulι.whiskeringRight _).preimageIso
    (P.ι.isoWhiskerLeft e.unitIso)
  counitIso := (Q.f

中文:
定义 congrFullSubcategory
  签名: [Q.在同构下封闭] (h : Q.inverseImage e.functor = P)
  定义体: Q.lift (P.ι ⋙ e.functor) (fun ⟨X, hX⟩ => by rwa [← h] at hX)
  inverse := P.lift (Q.ι ⋙ e.inverse) (fun ⟨Y, hY⟩ => by
    rw [← h]
    exact Q.prop_of_iso (e.counitIso.app Y).symm hY)
  unitIso := (P.fullyFaithfulι.whiskeringRight _).preimageIso
    (P.ι.isoWhiskerLeft e.unitIso)
  counitIso := (Q.f

Depends on / 依赖: Q.lift, e.functor, functor, infer_instance
-/
def congrFullSubcategory [Q.IsClosedUnderIsomorphisms] (h : Q.inverseImage e.functor = P) :
    P.FullSubcategory ≌ Q.FullSubcategory where
  functor := Q.lift (P.ι ⋙ e.functor) (fun ⟨X, hX⟩ => by rwa [← h] at hX)
  inverse := P.lift (Q.ι ⋙ e.inverse) (fun ⟨Y, hY⟩ => by
    rw [← h]
    exact Q.prop_of_iso (e.counitIso.app Y).symm hY)
  unitIso := (P.fullyFaithfulι.whiskeringRight _).preimageIso
    (P.ι.isoWhiskerLeft e.unitIso)
  counitIso := (Q.fullyFaithfulι.whiskeringRight _).preimageIso
    (Q.ι.isoWhiskerLeft e.counitIso)
  functor_unitIso_comp X :=
    ObjectProperty.hom_ext _ (e.functor_unit_comp X.obj)

end CategoryTheory.Equivalence
