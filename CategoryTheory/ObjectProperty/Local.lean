/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Objects that are local with respect to a property of morphisms

Given `W : MorphismProperty C`, we define `W.isLocal : ObjectProperty C`
which is the property of objects `Z` such that for any `f : X ⟶ Y` satisfying `W`,
the precomposition with `f` gives a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`.
(In the file `Mathlib/CategoryTheory/Localization/Bousfield.lean`, it is shown that this is
part of a Galois connection, with "dual" construction
`ObjectProperty.isLocal : ObjectProperty C → MorphismProperty C`.)

We also introduce the dual notion `W.isColocal : ObjectProperty C`.

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (W W' : MorphismProperty C)

/--
Definition of `isLocal` / `isLocal` 的定义

English:
definition isLocal
  signature: : ObjectProperty C
  body: fun Z => forall ⦃X Y : C⦄ (f : X ⟶ Y),
    W f -> Function.Bijective (fun (g : _ ⟶ Z) => f ≫ g)

中文:
定义 isLocal
  签名: : ObjectProperty C
  定义体: fun Z => forall ⦃X Y : C⦄ (f : X ⟶ Y),
    W f -> Function.Bijective (fun (g : _ ⟶ Z) => f ≫ g)

Depends on / 依赖: Bijective, Function, Function.Bijective
-/
def isLocal : ObjectProperty C :=
  fun Z => forall ⦃X Y : C⦄ (f : X ⟶ Y),
    W f -> Function.Bijective (fun (g : _ ⟶ Z) => f ≫ g)

/--
lemma `isLocal_iff` / 引理 `isLocal_iff`

English:
lemma isLocal_iff
  given: (Z : C)
  proof: Iff.rfl

中文:
引理 isLocal_iff
  条件: (Z : C)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isLocal_iff (Z : C) :
    W.isLocal Z ↔ forall ⦃X Y : C⦄ (f : X ⟶ Y),
      W f -> Function.Bijective (fun (g : _ ⟶ Z) => f ≫ g) := Iff.rfl

/--
Definition of `isColocal` / `isColocal` 的定义

English:
definition isColocal
  signature: : ObjectProperty C
  body: fun X => forall ⦃Y Z : C⦄ (g : Y ⟶ Z),
    W g -> Function.Bijective (fun (f : X ⟶ _) => f ≫ g)

中文:
定义 isColocal
  签名: : ObjectProperty C
  定义体: fun X => forall ⦃Y Z : C⦄ (g : Y ⟶ Z),
    W g -> Function.Bijective (fun (f : X ⟶ _) => f ≫ g)

Depends on / 依赖: Bijective, Function, Function.Bijective
-/
def isColocal : ObjectProperty C :=
  fun X => forall ⦃Y Z : C⦄ (g : Y ⟶ Z),
    W g -> Function.Bijective (fun (f : X ⟶ _) => f ≫ g)

/--
lemma `isColocal_iff` / 引理 `isColocal_iff`

English:
lemma isColocal_iff
  given: (X : C)
  proof: Iff.rfl

中文:
引理 isColocal_iff
  条件: (X : C)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isColocal_iff (X : C) :
    W.isColocal X ↔ forall ⦃Y Z : C⦄ (g : Y ⟶ Z),
      W g -> Function.Bijective (fun (f : X ⟶ Y) => f ≫ g) := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: W.isLocal.IsClosedUnderIsomorphisms
  body: by
    rw [← Function.Bijective.of_comp_iff _ (Iso.homToEquiv e).bijective]
    convert! (Iso.homToEquiv e).bijective.comp (hZ f hf) using 1
    aesop

中文:
实例 :
  签名: W.isLocal.在同构下封闭
  定义体: by
    rw [← Function.Bijective.of_comp_iff _ (Iso.homToEquiv e).bijective]
    convert! (Iso.homToEquiv e).bijective.comp (hZ f hf) using 1
    aesop

Depends on / 依赖: Bijective, Function, Function.Bijective.of_comp_iff, Iso.homToEquiv, bijective, bijective.comp, convert, homToEquiv, of_comp_iff
-/
instance : W.isLocal.IsClosedUnderIsomorphisms where
  of_iso {Z Z'} e hZ X Y f hf := by
    rw [← Function.Bijective.of_comp_iff _ (Iso.homToEquiv e).bijective]
    convert! (Iso.homToEquiv e).bijective.comp (hZ f hf) using 1
    aesop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: W.isColocal.IsClosedUnderIsomorphisms
  body: by
    rw [← Function.Bijective.of_comp_iff _ (Iso.homFromEquiv e).bijective]
    convert! (Iso.homFromEquiv e).bijective.comp (hX g hg) using 1
    aesop

中文:
实例 :
  签名: W.isColocal.在同构下封闭
  定义体: by
    rw [← Function.Bijective.of_comp_iff _ (Iso.homFromEquiv e).bijective]
    convert! (Iso.homFromEquiv e).bijective.comp (hX g hg) using 1
    aesop

Depends on / 依赖: Bijective, Function, Function.Bijective.of_comp_iff, Iso.homFromEquiv, bijective, bijective.comp, convert, homFromEquiv, of_comp_iff
-/
instance : W.isColocal.IsClosedUnderIsomorphisms where
  of_iso {X X'} e hX Y Z g hg := by
    rw [← Function.Bijective.of_comp_iff _ (Iso.homFromEquiv e).bijective]
    convert! (Iso.homFromEquiv e).bijective.comp (hX g hg) using 1
    aesop

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (J : Type u') [Category.{v'} J] :
    W.isLocal.IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := fun Z ⟨p⟩ X Y f hf => by
    refine ⟨fun g₁ g₂ h => p.isLimit.hom_ext
      (fun j => (p.prop_diag_obj j f hf).1 (by simp [reassoc_of% h])), fun g => ?_⟩
    choose app h using fun j => (p.prop_diag_obj j f hf).2 (g ≫ p.π.app j)
    exact ⟨p.isLimit.lift (Cone.mk _
      { app := app
        naturality _ _ a := (p.prop_diag_obj _ f hf).1
          (by simp [reassoc_of% h, h, p.w a]) }),
      p.isLimit.hom_ext (fun j => by simp [p.isLimit.fac, h])⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (J : Type u') [Category.{v'} J] :
    W.isColocal.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := fun X ⟨p⟩ Y Z g hg => by
    refine ⟨fun f₁ f₂ h => p.isColimit.hom_ext
      (fun j => (p.prop_diag_obj j g hg).1 (by simp [h])), fun f => ?_⟩
    choose app h using fun j => (p.prop_diag_obj j g hg).2 (p.ι.app j ≫ f)
    exact ⟨p.isColimit.desc (Cocone.mk _
      { app := app
        naturality _ _ a := (p.prop_diag_obj _ g hg).1
          (by simp [h]) }),
      p.isColimit.hom_ext (fun j => by simp [p.isColimit.fac_assoc, h])⟩

variable {W W'} in
attribute [local simp] isLocal_iff in
/--
lemma `isLocal_antitone` / 引理 `isLocal_antitone`

English:
lemma isLocal_antitone
  given: (h : W <= W')
  proof: by
  intro f hf
  aesop

中文:
引理 isLocal_antitone
  条件: (h : W <= W')
  证明: by
  intro f hf
  aesop
-/
lemma isLocal_antitone (h : W <= W') :
    W'.isLocal <= W.isLocal := by
  intro f hf
  aesop

variable {W W'} in
attribute [local simp] isColocal_iff in
/--
lemma `isColocal_antitone` / 引理 `isColocal_antitone`

English:
lemma isColocal_antitone
  given: (h : W <= W')
  proof: by
  intro f hf
  aesop

中文:
引理 isColocal_antitone
  条件: (h : W <= W')
  证明: by
  intro f hf
  aesop
-/
lemma isColocal_antitone (h : W <= W') :
    W'.isColocal <= W.isColocal := by
  intro f hf
  aesop

attribute [local simp] isLocal_iff in
@[simp]
/--
lemma `isLocal_iSup` / 引理 `isLocal_iSup`

English:
lemma isLocal_iSup
  given: {ι : Sort*} (W : ι -> MorphismProperty C)
  proof: by
  aesop

中文:
引理 isLocal_iSup
  条件: {ι : 类型层*} (W : ι -> MorphismProperty C)
  证明: by
  aesop
-/
lemma isLocal_iSup {ι : Sort*} (W : ι -> MorphismProperty C) :
    (⨆ (i : ι), W i).isLocal = ⨅ (i : ι), (W i).isLocal := by
  aesop

attribute [local simp] isColocal_iff in
@[simp]
/--
lemma `isColocal_iSup` / 引理 `isColocal_iSup`

English:
lemma isColocal_iSup
  given: {ι : Sort*} (W : ι -> MorphismProperty C)
  proof: by
  aesop

中文:
引理 isColocal_iSup
  条件: {ι : 类型层*} (W : ι -> MorphismProperty C)
  证明: by
  aesop
-/
lemma isColocal_iSup {ι : Sort*} (W : ι -> MorphismProperty C) :
    (⨆ (i : ι), W i).isColocal = ⨅ (i : ι), (W i).isColocal := by
  aesop

/--
lemma `isLocal_single_iff_bijective` / 引理 `isLocal_single_iff_bijective`

English:
lemma isLocal_single_iff_bijective
  given: {X Y : C} (f : X ⟶ Y) (Z : C)
  proof: ⟨fun h => h _ ⟨⟨⟩⟩, fun h => by rintro _ _ _ ⟨_⟩; exact h⟩

中文:
引理 isLocal_single_iff_bijective
  条件: {X Y : C} (f : X ⟶ Y) (Z : C)
  证明: ⟨fun h => h _ ⟨⟨⟩⟩, fun h => by rintro _ _ _ ⟨_⟩; exact h⟩
-/
lemma isLocal_single_iff_bijective {X Y : C} (f : X ⟶ Y) (Z : C) :
    (MorphismProperty.single f).isLocal Z ↔
      (Function.Bijective (fun (g : _ ⟶ Z) => f ≫ g)) :=
  ⟨fun h => h _ ⟨⟨⟩⟩, fun h => by rintro _ _ _ ⟨_⟩; exact h⟩

/--
lemma `isColocal_single_iff_bijective` / 引理 `isColocal_single_iff_bijective`

English:
lemma isColocal_single_iff_bijective
  given: {X Y : C} (f : X ⟶ Y) (Z : C)
  proof: ⟨fun h => h _ ⟨⟨⟩⟩, fun h => by rintro _ _ _ ⟨_⟩; exact h⟩

中文:
引理 isColocal_single_iff_bijective
  条件: {X Y : C} (f : X ⟶ Y) (Z : C)
  证明: ⟨fun h => h _ ⟨⟨⟩⟩, fun h => by rintro _ _ _ ⟨_⟩; exact h⟩
-/
lemma isColocal_single_iff_bijective {X Y : C} (f : X ⟶ Y) (Z : C) :
    (MorphismProperty.single f).isColocal Z ↔
      (Function.Bijective (fun (g : Z ⟶ _) => g ≫ f)) :=
  ⟨fun h => h _ ⟨⟨⟩⟩, fun h => by rintro _ _ _ ⟨_⟩; exact h⟩

end MorphismProperty

end CategoryTheory
