/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Constructions related to weakly initial objects

This file gives constructions related to weakly initial objects, namely:
* If a category has small products and a small weakly initial set of objects, then it has a weakly
  initial object.
* If a category has wide equalizers and a weakly initial object, then it has an initial object.

These are primarily useful to show the General Adjoint Functor Theorem.
-/

public section


universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/--
theorem `has_weakly_initial_of_weakly_initial_set_and_hasProducts` / 定理 `has_weakly_initial_of_weakly_initial_set_and_hasProducts`

English:
theorem has_weakly_initial_of_weakly_initial_set_and_hasProducts
  statement: [HasProducts.{v} C] {ι : Type v}
  proof: ⟨∏ᶜ B, fun X => ⟨Pi.π _ _ ≫ (hB X).choose_spec.some⟩⟩

中文:
定理 has_weakly_initial_of_weakly_initial_set_and_hasProducts
  结论: [HasProducts.{v} C] {ι : 类型v}
  证明: ⟨∏ᶜ B, fun X => ⟨Pi.π _ _ ≫ (hB X).choose_spec.some⟩⟩

Depends on / 依赖: choose_spec, choose_spec.some
-/
theorem has_weakly_initial_of_weakly_initial_set_and_hasProducts [HasProducts.{v} C] {ι : Type v}
    {B : ι -> C} (hB : forall A : C, exists i, Nonempty (B i ⟶ A)) : exists T : C, forall X, Nonempty (T ⟶ X) :=
  ⟨∏ᶜ B, fun X => ⟨Pi.π _ _ ≫ (hB X).choose_spec.some⟩⟩

/--
theorem `hasInitial_of_weakly_initial_and_hasWideEqualizers` / 定理 `hasInitial_of_weakly_initial_and_hasWideEqualizers`

English:
theorem hasInitial_of_weakly_initial_and_hasWideEqualizers
  statement: [HasWideEqualizers.{v} C] {T : C}
  proof: by
  let endos := T ⟶ T
  let i := wideEqualizer.ι (id : endos -> endos)
  have : Nonempty endos := ⟨𝟙 _⟩
  have : forall X : C, Unique (wideEqualizer (id : endos -> endos) ⟶ X) := by
    intro X
    refine ⟨⟨i ≫ Classical.choice (hT X)⟩, fun a => ?_⟩
    let E := equalizer a (i ≫ Classical.choice (hT _))
    let e : E ⟶ wideEqualizer id := equalizer.ι _ _
    let h : T ⟶ E := Classical.choice (hT E)
    have : ((i ≫ h) ≫ e) ≫ i = i ≫ 𝟙 _ := by
      rw [Category.assoc]; rw [Category.assoc]
      apply wideEqualizer.condition (id : endos -> endos) (h ≫ e ≫ i)
    rw [Category.comp_id]; rw [cancel_mono_id i] at this
    have : IsSplitEpi e := IsSplitEpi.mk' ⟨i ≫ h, this⟩
    rw [← cancel_epi e]
    apply equalizer.condition
  exact hasInitial_of_unique (wideEqualizer (id : endos -> endos))

中文:
定理 hasInitial_of_weakly_initial_and_hasWideEqualizers
  结论: [HasWideEqualizers.{v} C] {T : C}
  证明: by
  let endos := T ⟶ T
  let i := wideEqualizer.ι (id : endos -> endos)
  have : Nonempty endos := ⟨𝟙 _⟩
  have : forall X : C, Unique (wideEqualizer (id : endos -> endos) ⟶ X) := by
    intro X
    refine ⟨⟨i ≫ Classical.choice (hT X)⟩, fun a => ?_⟩
    let E := equalizer a (i ≫ Classical.choice (hT _))
    let e : E ⟶ wideEqualizer id := equalizer.ι _ _
    let h : T ⟶ E := Classical.choice (hT E)
    have : ((i ≫ h) ≫ e) ≫ i = i ≫ 𝟙 _ := by
      rw [Category.assoc]; rw [Category.assoc]
      apply wideEqualizer.condition (id : endos -> endos) (h ≫ e ≫ i)
    rw [Category.comp_id]; rw [cancel_mono_id i] at this
    have : IsSplitEpi e := IsSplitEpi.mk' ⟨i ≫ h, this⟩
    rw [← cancel_epi e]
    apply equalizer.condition
  exact hasInitial_of_unique (wideEqualizer (id : endos -> endos))

Depends on / 依赖: Category, Category.assoc, Classical, Classical.choice, Nonempty, Unique, choice, condition, equalizer, wideEqualizer, wideEqualizer.condition
-/
theorem hasInitial_of_weakly_initial_and_hasWideEqualizers [HasWideEqualizers.{v} C] {T : C}
    (hT : forall X, Nonempty (T ⟶ X)) : HasInitial C := by
  let endos := T ⟶ T
  let i := wideEqualizer.ι (id : endos -> endos)
  have : Nonempty endos := ⟨𝟙 _⟩
  have : forall X : C, Unique (wideEqualizer (id : endos -> endos) ⟶ X) := by
    intro X
    refine ⟨⟨i ≫ Classical.choice (hT X)⟩, fun a => ?_⟩
    let E := equalizer a (i ≫ Classical.choice (hT _))
    let e : E ⟶ wideEqualizer id := equalizer.ι _ _
    let h : T ⟶ E := Classical.choice (hT E)
    have : ((i ≫ h) ≫ e) ≫ i = i ≫ 𝟙 _ := by
      rw [Category.assoc]; rw [Category.assoc]
      apply wideEqualizer.condition (id : endos -> endos) (h ≫ e ≫ i)
    rw [Category.comp_id]; rw [cancel_mono_id i] at this
    have : IsSplitEpi e := IsSplitEpi.mk' ⟨i ≫ h, this⟩
    rw [← cancel_epi e]
    apply equalizer.condition
  exact hasInitial_of_unique (wideEqualizer (id : endos -> endos))

end CategoryTheory
