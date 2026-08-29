/-
Copyright (c) 2024 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# A closed monoidal category is enriched in itself

From the data of a closed monoidal category `C`, we define a `C`-category structure for `C`.
where the hom-object is given by the internal hom (coming from the closed structure).

We use `scoped instance` to avoid potential issues where `C` may also have
a `C`-category structure coming from another source (e.g. the type of simplicial sets
`SSet.{v}` has an instance of `EnrichedCategory SSet.{v}` as a category of simplicial objects;
see `Mathlib/AlgebraicTopology/SimplicialCategory/SimplicialObject.lean`).

All structure field values are defined in `Mathlib/CategoryTheory/Closed/Monoidal.lean`.

-/

public section

universe u v

namespace CategoryTheory

open Category MonoidalCategory

namespace MonoidalClosed

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- For `C` closed monoidal, build an instance of `C` as a `C`-category -/
scoped instance enrichedCategorySelf : EnrichedCategory C C where
  Hom x := (ihom x).obj
  id _ := id _
  comp _ _ _ := comp _ _ _
  assoc _ _ _ _ := assoc _ _ _ _

section

variable {C}

/--
lemma `enrichedCategorySelf_hom` / 引理 `enrichedCategorySelf_hom`

English:
lemma enrichedCategorySelf_hom
  given: (X Y : C)
  proof: rfl

中文:
引理 enrichedCategorySelf_hom
  条件: (X Y : C)
  证明: rfl
-/
lemma enrichedCategorySelf_hom (X Y : C) :
    EnrichedCategory.Hom X Y = (ihom X).obj Y := rfl

/--
lemma `enrichedCategorySelf_id` / 引理 `enrichedCategorySelf_id`

English:
lemma enrichedCategorySelf_id
  given: (X : C)
  proof: rfl

中文:
引理 enrichedCategorySelf_id
  条件: (X : C)
  证明: rfl
-/
lemma enrichedCategorySelf_id (X : C) :
    eId C X = id X := rfl

/--
lemma `enrichedCategorySelf_comp` / 引理 `enrichedCategorySelf_comp`

English:
lemma enrichedCategorySelf_comp
  given: (X Y Z : C)
  proof: rfl

中文:
引理 enrichedCategorySelf_comp
  条件: (X Y Z : C)
  证明: rfl
-/
lemma enrichedCategorySelf_comp (X Y Z : C) :
    eComp C X Y Z = comp X Y Z := rfl

end

/-- A monoidal closed category is an enriched ordinary category over itself. -/
scoped instance enrichedOrdinaryCategorySelf : EnrichedOrdinaryCategory C C where
  homEquiv := curryHomEquiv'
  homEquiv_id X := curry'_id X
  homEquiv_comp := curry'_comp

/--
lemma `enrichedOrdinaryCategorySelf_eHomWhiskerLeft` / 引理 `enrichedOrdinaryCategorySelf_eHomWhiskerLeft`

English:
lemma enrichedOrdinaryCategorySelf_eHomWhiskerLeft
  given: (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂)
  proof: by
  change (ρ_ _).inv ≫ _ ◁ curry' g ≫ comp X Y₁ Y₂ = _
  rw [whiskerLeft_curry'_comp]; rw [Iso.inv_hom_id_assoc]

中文:
引理 enrichedOrdinaryCategorySelf_eHomWhiskerLeft
  条件: (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂)
  证明: by
  change (ρ_ _).inv ≫ _ ◁ curry' g ≫ comp X Y₁ Y₂ = _
  rw [whiskerLeft_curry'_comp]; rw [Iso.inv_hom_id_assoc]

Depends on / 依赖: Iso.inv_hom_id_assoc, _comp, inv_hom_id_assoc, whiskerLeft_curry
-/
lemma enrichedOrdinaryCategorySelf_eHomWhiskerLeft (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    eHomWhiskerLeft C X g = (ihom X).map g := by
  change (ρ_ _).inv ≫ _ ◁ curry' g ≫ comp X Y₁ Y₂ = _
  rw [whiskerLeft_curry'_comp]; rw [Iso.inv_hom_id_assoc]

/--
lemma `enrichedOrdinaryCategorySelf_eHomWhiskerRight` / 引理 `enrichedOrdinaryCategorySelf_eHomWhiskerRight`

English:
lemma enrichedOrdinaryCategorySelf_eHomWhiskerRight
  given: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C)
  proof: by
  change (fun_ _).inv ≫ curry' f ▷ _ ≫ comp X₁ X₂ Y = _
  rw [curry'_whiskerRight_comp]; rw [Iso.inv_hom_id_assoc]

中文:
引理 enrichedOrdinaryCategorySelf_eHomWhiskerRight
  条件: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C)
  证明: by
  change (fun_ _).inv ≫ curry' f ▷ _ ≫ comp X₁ X₂ Y = _
  rw [curry'_whiskerRight_comp]; rw [Iso.inv_hom_id_assoc]

Depends on / 依赖: Iso.inv_hom_id_assoc, _whiskerRight_comp, fun_, hasSheafCompose_of_preservesMulticospan, inv_hom_id_assoc
-/
lemma enrichedOrdinaryCategorySelf_eHomWhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    eHomWhiskerRight C f Y = (pre f).app Y := by
  change (fun_ _).inv ≫ curry' f ▷ _ ≫ comp X₁ X₂ Y = _
  rw [curry'_whiskerRight_comp]; rw [Iso.inv_hom_id_assoc]

/--
lemma `enrichedOrdinaryCategorySelf_homEquiv` / 引理 `enrichedOrdinaryCategorySelf_homEquiv`

English:
lemma enrichedOrdinaryCategorySelf_homEquiv
  given: {X Y : C} (f : X ⟶ Y)
  proof: rfl

中文:
引理 enrichedOrdinaryCategorySelf_homEquiv
  条件: {X Y : C} (f : X ⟶ Y)
  证明: rfl
-/
lemma enrichedOrdinaryCategorySelf_homEquiv {X Y : C} (f : X ⟶ Y) :
    eHomEquiv C f = curry' f := rfl

/--
lemma `enrichedOrdinaryCategorySelf_homEquiv_symm` / 引理 `enrichedOrdinaryCategorySelf_homEquiv_symm`

English:
lemma enrichedOrdinaryCategorySelf_homEquiv_symm
  given: {X Y : C} (g : 𝟙_ C ⟶ (ihom X).obj Y)
  proof: rfl

中文:
引理 enrichedOrdinaryCategorySelf_homEquiv_symm
  条件: {X Y : C} (g : 𝟙_ C ⟶ (ihom X).obj Y)
  证明: rfl
-/
lemma enrichedOrdinaryCategorySelf_homEquiv_symm {X Y : C} (g : 𝟙_ C ⟶ (ihom X).obj Y) :
    (eHomEquiv C).symm g = uncurry' g := rfl

end MonoidalClosed

end CategoryTheory
