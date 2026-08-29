/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Separators in preadditive categories

This file contains characterizations of separating sets and objects that are valid in all
preadditive categories.

-/

public section


universe v u

open CategoryTheory Opposite ObjectProperty

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/--
theorem `Preadditive.isSeparating_iff` / 定理 `Preadditive.isSeparating_iff`

English:
theorem Preadditive.isSeparating_iff
  given: (P : ObjectProperty C)
  proof: ⟨fun h𝒢 X Y f hf => h𝒢 _ _ (by simpa only [Limits.comp_zero] using hf), fun h𝒢 X Y f g hfg =>
sub_eq_zero.1 h𝒢 _ (by simpa only [Preadditive.comp_sub, sub_eq_zero] using hfg)⟩

中文:
定理 Preadditive.isSeparating_iff
  条件: (P : Object命题erty C)
  证明: ⟨fun h𝒢 X Y f hf => h𝒢 _ _ (by simpa only [Limits.comp_zero] using hf), fun h𝒢 X Y f g hfg =>
sub_eq_zero.1 h𝒢 _ (by simpa only [Preadditive.comp_sub, sub_eq_zero] using hfg)⟩

Depends on / 依赖: Limits, Limits.comp_zero, Preadditive, Preadditive.comp_sub, comp_sub, comp_zero, sub_eq_zero
-/
theorem Preadditive.isSeparating_iff (P : ObjectProperty C) :
    P.IsSeparating ↔
      forall ⦃X Y : C⦄ (f : X ⟶ Y), (forall (G : C) (_ : P G), forall (h : G ⟶ X), h ≫ f = 0) -> f = 0 :=
  ⟨fun h𝒢 X Y f hf => h𝒢 _ _ (by simpa only [Limits.comp_zero] using hf), fun h𝒢 X Y f g hfg =>
sub_eq_zero.1 h𝒢 _ (by simpa only [Preadditive.comp_sub, sub_eq_zero] using hfg)⟩

/--
theorem `Preadditive.isCoseparating_iff` / 定理 `Preadditive.isCoseparating_iff`

English:
theorem Preadditive.isCoseparating_iff
  given: (P : ObjectProperty C)
  proof: ⟨fun h𝒢 X Y f hf => h𝒢 _ _ (by simpa only [Limits.zero_comp] using hf), fun h𝒢 X Y f g hfg =>
sub_eq_zero.1 h𝒢 _ (by simpa only [Preadditive.sub_comp, sub_eq_zero] using hfg)⟩

中文:
定理 Preadditive.isCoseparating_iff
  条件: (P : Object命题erty C)
  证明: ⟨fun h𝒢 X Y f hf => h𝒢 _ _ (by simpa only [Limits.zero_comp] using hf), fun h𝒢 X Y f g hfg =>
sub_eq_zero.1 h𝒢 _ (by simpa only [Preadditive.sub_comp, sub_eq_zero] using hfg)⟩

Depends on / 依赖: Limits, Limits.zero_comp, Preadditive, Preadditive.sub_comp, sub_comp, sub_eq_zero, zero_comp
-/
theorem Preadditive.isCoseparating_iff (P : ObjectProperty C) :
    P.IsCoseparating ↔
      forall ⦃X Y : C⦄ (f : X ⟶ Y), (forall (G : C) (_ : P G), forall (h : Y ⟶ G), f ≫ h = 0) -> f = 0 :=
  ⟨fun h𝒢 X Y f hf => h𝒢 _ _ (by simpa only [Limits.zero_comp] using hf), fun h𝒢 X Y f g hfg =>
sub_eq_zero.1 h𝒢 _ (by simpa only [Preadditive.sub_comp, sub_eq_zero] using hfg)⟩

/--
theorem `Preadditive.isSeparator_iff` / 定理 `Preadditive.isSeparator_iff`

English:
theorem Preadditive.isSeparator_iff
  given: (G : C)
  proof: ⟨fun hG X Y f hf => hG.def _ _ (by simpa only [Limits.comp_zero] using hf), fun hG =>
    (isSeparator_def _).2 fun X Y f g hfg =>
sub_eq_zero.1 hG _ (by simpa only [Preadditive.comp_sub, sub_eq_zero] using hfg)⟩

中文:
定理 Preadditive.isSeparator_iff
  条件: (G : C)
  证明: ⟨fun hG X Y f hf => hG.def _ _ (by simpa only [Limits.comp_zero] using hf), fun hG =>
    (isSeparator_def _).2 fun X Y f g hfg =>
sub_eq_zero.1 hG _ (by simpa only [Preadditive.comp_sub, sub_eq_zero] using hfg)⟩

Depends on / 依赖: Limits, Limits.comp_zero, Preadditive, Preadditive.comp_sub, comp_sub, comp_zero, hG.def, isSeparator_def, sub_eq_zero
-/
theorem Preadditive.isSeparator_iff (G : C) :
    IsSeparator G ↔ forall ⦃X Y : C⦄ (f : X ⟶ Y), (forall h : G ⟶ X, h ≫ f = 0) -> f = 0 :=
  ⟨fun hG X Y f hf => hG.def _ _ (by simpa only [Limits.comp_zero] using hf), fun hG =>
    (isSeparator_def _).2 fun X Y f g hfg =>
sub_eq_zero.1 hG _ (by simpa only [Preadditive.comp_sub, sub_eq_zero] using hfg)⟩

/--
theorem `Preadditive.isCoseparator_iff` / 定理 `Preadditive.isCoseparator_iff`

English:
theorem Preadditive.isCoseparator_iff
  given: (G : C)
  proof: ⟨fun hG X Y f hf => hG.def _ _ (by simpa only [Limits.zero_comp] using hf), fun hG =>
    (isCoseparator_def _).2 fun X Y f g hfg =>
sub_eq_zero.1 hG _ (by simpa only [Preadditive.sub_comp, sub_eq_zero] using hfg)⟩

中文:
定理 Preadditive.isCoseparator_iff
  条件: (G : C)
  证明: ⟨fun hG X Y f hf => hG.def _ _ (by simpa only [Limits.zero_comp] using hf), fun hG =>
    (isCoseparator_def _).2 fun X Y f g hfg =>
sub_eq_zero.1 hG _ (by simpa only [Preadditive.sub_comp, sub_eq_zero] using hfg)⟩

Depends on / 依赖: Limits, Limits.zero_comp, Preadditive, Preadditive.sub_comp, hG.def, isCoseparator_def, sub_comp, sub_eq_zero, zero_comp
-/
theorem Preadditive.isCoseparator_iff (G : C) :
    IsCoseparator G ↔ forall ⦃X Y : C⦄ (f : X ⟶ Y), (forall h : Y ⟶ G, f ≫ h = 0) -> f = 0 :=
  ⟨fun hG X Y f hf => hG.def _ _ (by simpa only [Limits.zero_comp] using hf), fun hG =>
    (isCoseparator_def _).2 fun X Y f g hfg =>
sub_eq_zero.1 hG _ (by simpa only [Preadditive.sub_comp, sub_eq_zero] using hfg)⟩

/--
theorem `isSeparator_iff_faithful_preadditiveCoyoneda` / 定理 `isSeparator_iff_faithful_preadditiveCoyoneda`

English:
theorem isSeparator_iff_faithful_preadditiveCoyoneda
  given: (G : C)
  proof: by
  rw [isSeparator_iff_faithful_coyoneda_obj]; rw [← whiskering_preadditiveCoyoneda]; rw [Functor.comp_obj]; rw [Functor.whiskeringRight_obj_obj]
  exact ⟨fun h => Functor.Faithful.of_comp _ (forget AddCommGrpCat),
    fun h => Functor.Faithful.comp _ _⟩

中文:
定理 isSeparator_iff_faithful_preadditiveCoyoneda
  条件: (G : C)
  证明: by
  rw [isSeparator_iff_faithful_coyoneda_obj]; rw [← whiskering_preadditiveCoyoneda]; rw [Functor.comp_obj]; rw [Functor.whiskeringRight_obj_obj]
  exact ⟨fun h => Functor.Faithful.of_comp _ (forget AddCommGrpCat),
    fun h => Functor.Faithful.comp _ _⟩

Depends on / 依赖: AddCommGrpCat, Faithful, Functor, Functor.Faithful.comp, Functor.Faithful.of_comp, Functor.comp_obj, Functor.whiskeringRight_obj_obj, comp_obj, forget, isSeparator_iff_faithful_coyoneda_obj, of_comp, whiskeringRight_obj_obj, whiskering_preadditiveCoyoneda
-/
theorem isSeparator_iff_faithful_preadditiveCoyoneda (G : C) :
    IsSeparator G ↔ (preadditiveCoyoneda.obj (op G)).Faithful := by
  rw [isSeparator_iff_faithful_coyoneda_obj]; rw [← whiskering_preadditiveCoyoneda]; rw [Functor.comp_obj]; rw [Functor.whiskeringRight_obj_obj]
  exact ⟨fun h => Functor.Faithful.of_comp _ (forget AddCommGrpCat),
    fun h => Functor.Faithful.comp _ _⟩

/--
theorem `isSeparator_iff_faithful_preadditiveCoyonedaObj` / 定理 `isSeparator_iff_faithful_preadditiveCoyonedaObj`

English:
theorem isSeparator_iff_faithful_preadditiveCoyonedaObj
  given: (G : C)
  proof: by
  rw [isSeparator_iff_faithful_preadditiveCoyoneda]; rw [preadditiveCoyoneda_obj]
  exact ⟨fun h => Functor.Faithful.of_comp _ (forget₂ _ AddCommGrpCat.{v}),
    fun h => Functor.Faithful.comp _ _⟩

中文:
定理 isSeparator_iff_faithful_preadditiveCoyonedaObj
  条件: (G : C)
  证明: by
  rw [isSeparator_iff_faithful_preadditiveCoyoneda]; rw [preadditiveCoyoneda_obj]
  exact ⟨fun h => Functor.Faithful.of_comp _ (forget₂ _ AddCommGrpCat.{v}),
    fun h => Functor.Faithful.comp _ _⟩

Depends on / 依赖: AddCommGrpCat, Faithful, Functor, Functor.Faithful.comp, Functor.Faithful.of_comp, isSeparator_iff_faithful_preadditiveCoyoneda, of_comp, preadditiveCoyoneda_obj
-/
theorem isSeparator_iff_faithful_preadditiveCoyonedaObj (G : C) :
    IsSeparator G ↔ (preadditiveCoyonedaObj G).Faithful := by
  rw [isSeparator_iff_faithful_preadditiveCoyoneda]; rw [preadditiveCoyoneda_obj]
  exact ⟨fun h => Functor.Faithful.of_comp _ (forget₂ _ AddCommGrpCat.{v}),
    fun h => Functor.Faithful.comp _ _⟩

/--
theorem `isCoseparator_iff_faithful_preadditiveYoneda` / 定理 `isCoseparator_iff_faithful_preadditiveYoneda`

English:
theorem isCoseparator_iff_faithful_preadditiveYoneda
  given: (G : C)
  proof: by
  rw [isCoseparator_iff_faithful_yoneda_obj]; rw [← whiskering_preadditiveYoneda]; rw [Functor.comp_obj]; rw [Functor.whiskeringRight_obj_obj]
  exact ⟨fun h => Functor.Faithful.of_comp _ (forget AddCommGrpCat),
    fun h => Functor.Faithful.comp _ _⟩

中文:
定理 isCoseparator_iff_faithful_preadditiveYoneda
  条件: (G : C)
  证明: by
  rw [isCoseparator_iff_faithful_yoneda_obj]; rw [← whiskering_preadditiveYoneda]; rw [Functor.comp_obj]; rw [Functor.whiskeringRight_obj_obj]
  exact ⟨fun h => Functor.Faithful.of_comp _ (forget AddCommGrpCat),
    fun h => Functor.Faithful.comp _ _⟩

Depends on / 依赖: AddCommGrpCat, Faithful, Functor, Functor.Faithful.comp, Functor.Faithful.of_comp, Functor.comp_obj, Functor.whiskeringRight_obj_obj, comp_obj, forget, isCoseparator_iff_faithful_yoneda_obj, of_comp, whiskeringRight_obj_obj, whiskering_preadditiveYoneda
-/
theorem isCoseparator_iff_faithful_preadditiveYoneda (G : C) :
    IsCoseparator G ↔ (preadditiveYoneda.obj G).Faithful := by
  rw [isCoseparator_iff_faithful_yoneda_obj]; rw [← whiskering_preadditiveYoneda]; rw [Functor.comp_obj]; rw [Functor.whiskeringRight_obj_obj]
  exact ⟨fun h => Functor.Faithful.of_comp _ (forget AddCommGrpCat),
    fun h => Functor.Faithful.comp _ _⟩

/--
theorem `isCoseparator_iff_faithful_preadditiveYonedaObj` / 定理 `isCoseparator_iff_faithful_preadditiveYonedaObj`

English:
theorem isCoseparator_iff_faithful_preadditiveYonedaObj
  given: (G : C)
  proof: by
  rw [isCoseparator_iff_faithful_preadditiveYoneda]; rw [preadditiveYoneda_obj]
  exact ⟨fun h => Functor.Faithful.of_comp _ (forget₂ _ AddCommGrpCat.{v}),
    fun h => Functor.Faithful.comp _ _⟩

中文:
定理 isCoseparator_iff_faithful_preadditiveYonedaObj
  条件: (G : C)
  证明: by
  rw [isCoseparator_iff_faithful_preadditiveYoneda]; rw [preadditiveYoneda_obj]
  exact ⟨fun h => Functor.Faithful.of_comp _ (forget₂ _ AddCommGrpCat.{v}),
    fun h => Functor.Faithful.comp _ _⟩

Depends on / 依赖: AddCommGrpCat, Faithful, Functor, Functor.Faithful.comp, Functor.Faithful.of_comp, isCoseparator_iff_faithful_preadditiveYoneda, of_comp, preadditiveYoneda_obj
-/
theorem isCoseparator_iff_faithful_preadditiveYonedaObj (G : C) :
    IsCoseparator G ↔ (preadditiveYonedaObj G).Faithful := by
  rw [isCoseparator_iff_faithful_preadditiveYoneda]; rw [preadditiveYoneda_obj]
  exact ⟨fun h => Functor.Faithful.of_comp _ (forget₂ _ AddCommGrpCat.{v}),
    fun h => Functor.Faithful.comp _ _⟩

end CategoryTheory
