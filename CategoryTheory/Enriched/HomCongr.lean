/-
Copyright (c) 2024 Nick Ward. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nick Ward
-/
module

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# Congruence of enriched homs

Recall that when `C` is both a category and a `V`-enriched category, we say it
is an `EnrichedOrdinaryCategory` if it comes equipped with a sufficiently
compatible equivalence between morphisms `X ⟶ Y` in `C` and morphisms
`𝟙_ V ⟶ (X ⟶[V] Y)` in `V`.

In such a `V`-enriched ordinary category `C`, isomorphisms in `C` induce
isomorphisms between hom-objects in `V`. We define this isomorphism in
`CategoryTheory.Iso.eHomCongr` and prove that it respects composition in `C`.

The treatment here parallels that for unenriched categories in
`Mathlib/CategoryTheory/HomCongr.lean` and that for sorts in
`Mathlib/Logic/Equiv/Defs.lean` (cf. `Equiv.arrowCongr`). Note, however, that
they construct equivalences between `Type`s and `Sort`s, respectively, while
in this file we construct isomorphisms between objects in `V`.
-/

@[expose] public section

universe v' v u u'

namespace CategoryTheory
namespace Iso

open Category MonoidalCategory

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- Given isomorphisms `α : X ≅ X₁` and `β : Y ≅ Y₁` in `C`, we can construct
an isomorphism between `V` objects `X ⟶[V] Y` and `X₁ ⟶[V] Y₁`. -/
@[simps]
/--
Definition of `eHomCongr` / `eHomCongr` 的定义

English:
definition eHomCongr
  signature: {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁)
  body: eHomWhiskerRight V α.inv Y ≫ eHomWhiskerLeft V X₁ β.hom
  inv := eHomWhiskerRight V α.hom Y₁ ≫ eHomWhiskerLeft V X β.inv
  hom_inv_id := by
    rw [← eHom_whisker_exchange]
    slice_lhs 2 3 => rw [← eHomWhiskerRight_comp]
    simp [← eHomWhiskerLeft_comp]
  inv_hom_id := by
    rw [← eHom_whisker_exchange]
    slice_lhs 2 3 => rw [← eHomWhiskerRight_comp]
    simp [← eHomWhiskerLeft_comp]

中文:
定义 eHomCongr
  签名: {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁)
  定义体: eHomWhiskerRight V α.inv Y ≫ eHomWhiskerLeft V X₁ β.hom
  inv := eHomWhiskerRight V α.hom Y₁ ≫ eHomWhiskerLeft V X β.inv
  hom_inv_id := by
    rw [← eHom_whisker_exchange]
    slice_lhs 2 3 => rw [← eHomWhiskerRight_comp]
    simp [← eHomWhiskerLeft_comp]
  inv_hom_id := by
    rw [← eHom_whisker_exchange]
    slice_lhs 2 3 => rw [← eHomWhiskerRight_comp]
    simp [← eHomWhiskerLeft_comp]

Depends on / 依赖: eHomWhiskerLeft, eHomWhiskerRight
-/
def eHomCongr {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶[V] Y) ≅ (X₁ ⟶[V] Y₁) where
  hom := eHomWhiskerRight V α.inv Y ≫ eHomWhiskerLeft V X₁ β.hom
  inv := eHomWhiskerRight V α.hom Y₁ ≫ eHomWhiskerLeft V X β.inv
  hom_inv_id := by
    rw [← eHom_whisker_exchange]
    slice_lhs 2 3 => rw [← eHomWhiskerRight_comp]
    simp [← eHomWhiskerLeft_comp]
  inv_hom_id := by
    rw [← eHom_whisker_exchange]
    slice_lhs 2 3 => rw [← eHomWhiskerRight_comp]
    simp [← eHomWhiskerLeft_comp]

/--
lemma `eHomCongr_refl` / 引理 `eHomCongr_refl`

English:
lemma eHomCongr_refl
  given: (X Y : C)
  proof: by aesop

中文:
引理 eHomCongr_refl
  条件: (X Y : C)
  证明: by aesop
-/
lemma eHomCongr_refl (X Y : C) :
    eHomCongr V (Iso.refl X) (Iso.refl Y) = Iso.refl (X ⟶[V] Y) := by aesop

/--
lemma `eHomCongr_trans` / 引理 `eHomCongr_trans`

English:
lemma eHomCongr_trans
  statement: {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (α₁ : X₁ ≅ X₂) (β₁ : Y₁ ≅ Y₂)
  proof: by
  ext; simp [eHom_whisker_exchange_assoc]

中文:
引理 eHomCongr_trans
  结论: {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (α₁ : X₁ ≅ X₂) (β₁ : Y₁ ≅ Y₂)
  证明: by
  ext; simp [eHom_whisker_exchange_assoc]

Depends on / 依赖: eHom_whisker_exchange_assoc
-/
lemma eHomCongr_trans {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (α₁ : X₁ ≅ X₂) (β₁ : Y₁ ≅ Y₂)
    (α₂ : X₂ ≅ X₃) (β₂ : Y₂ ≅ Y₃) :
    eHomCongr V (α₁ ≪≫ α₂) (β₁ ≪≫ β₂) =
      eHomCongr V α₁ β₁ ≪≫ eHomCongr V α₂ β₂ := by
  ext; simp [eHom_whisker_exchange_assoc]

/--
lemma `eHomCongr_symm` / 引理 `eHomCongr_symm`

English:
lemma eHomCongr_symm
  given: {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁)
  proof: rfl

中文:
引理 eHomCongr_symm
  条件: {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁)
  证明: rfl
-/
lemma eHomCongr_symm {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (eHomCongr V α β).symm = eHomCongr V α.symm β.symm := rfl

/-- `eHomCongr` respects composition of morphisms. Recall that for any
composable pair of arrows `f : X ⟶ Y` and `g : Y ⟶ Z` in `C`, the composite
`f ≫ g` in `C` defines a morphism `𝟙_ V ⟶ (X ⟶[V] Z)` in `V`. Composing with
the isomorphism `eHomCongr V α γ` yields a morphism in `V` that can be factored
through the enriched composition map as shown:
`𝟙_ V ⟶ 𝟙_ V ⊗ 𝟙_ V ⟶ (X₁ ⟶[V] Y₁) ⊗ (Y₁ ⟶[V] Z₁) ⟶ (X₁ ⟶[V] Z₁)`. -/
@[reassoc]
/--
lemma `eHomCongr_comp` / 引理 `eHomCongr_comp`

English:
lemma eHomCongr_comp
  statement: {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (γ : Z ≅ Z₁)
  proof: by
  simp only [eHomCongr, MonoidalCategory.whiskerRight_id, assoc,
    MonoidalCategory.whiskerLeft_comp]
  rw [rightUnitor_inv_naturality_assoc]; rw [rightUnitor_inv_naturality_assoc]; rw [rightUnitor_inv_naturality_assoc]; rw [hom_inv_id_assoc]; rw [← whisker_exchange_assoc]; rw [← whisker_exchange_assoc]; rw [← eComp_eHomWhiskerLeft]; rw [eHom_whisker_cancel_assoc]; rw [← eComp_eHomWhiskerRight_assoc]; rw [← tensorHom_def_assoc]; rw [← eHomEquiv_comp_assoc]

中文:
引理 eHomCongr_comp
  结论: {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (γ : Z ≅ Z₁)
  证明: by
  simp only [eHomCongr, MonoidalCategory.whiskerRight_id, assoc,
    MonoidalCategory.whiskerLeft_comp]
  rw [rightUnitor_inv_naturality_assoc]; rw [rightUnitor_inv_naturality_assoc]; rw [rightUnitor_inv_naturality_assoc]; rw [hom_inv_id_assoc]; rw [← whisker_exchange_assoc]; rw [← whisker_exchange_assoc]; rw [← eComp_eHomWhiskerLeft]; rw [eHom_whisker_cancel_assoc]; rw [← eComp_eHomWhiskerRight_assoc]; rw [← tensorHom_def_assoc]; rw [← eHomEquiv_comp_assoc]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerRight_id, eComp_eHomWhiskerLeft, eComp_eHomWhiskerRight_assoc, eHomCongr, eHomEquiv_comp_assoc, eHom_whisker_cancel_assoc, hom_inv_id_assoc, rightUnitor_inv_naturality_assoc, tensorHom_def_assoc, whiskerLeft_comp, whiskerRight_id, whisker_exchange_assoc
-/
lemma eHomCongr_comp {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (γ : Z ≅ Z₁)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V (f ≫ g) ≫ (eHomCongr V α γ).hom =
      (fun_ _).inv ≫ (eHomEquiv V f ≫ (eHomCongr V α β).hom) ▷ _ ≫
        _ ◁ (eHomEquiv V g ≫ (eHomCongr V β γ).hom) ≫ eComp V X₁ Y₁ Z₁ := by
  simp only [eHomCongr, MonoidalCategory.whiskerRight_id, assoc,
    MonoidalCategory.whiskerLeft_comp]
  rw [rightUnitor_inv_naturality_assoc]; rw [rightUnitor_inv_naturality_assoc]; rw [rightUnitor_inv_naturality_assoc]; rw [hom_inv_id_assoc]; rw [← whisker_exchange_assoc]; rw [← whisker_exchange_assoc]; rw [← eComp_eHomWhiskerLeft]; rw [eHom_whisker_cancel_assoc]; rw [← eComp_eHomWhiskerRight_assoc]; rw [← tensorHom_def_assoc]; rw [← eHomEquiv_comp_assoc]

/-- The inverse map defined by `eHomCongr` respects composition of morphisms. -/
@[reassoc]
/--
lemma `eHomCongr_inv_comp` / 引理 `eHomCongr_inv_comp`

English:
lemma eHomCongr_inv_comp
  statement: {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁)
  proof: eHomCongr_comp V α.symm β.symm γ.symm f g

中文:
引理 eHomCongr_inv_comp
  结论: {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁)
  证明: eHomCongr_comp V α.symm β.symm γ.symm f g

Depends on / 依赖: eHomCongr_comp
-/
lemma eHomCongr_inv_comp {X Y Z X₁ Y₁ Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁)
    (γ : Z ≅ Z₁) (f : X₁ ⟶ Y₁) (g : Y₁ ⟶ Z₁) :
    eHomEquiv V (f ≫ g) ≫ (eHomCongr V α γ).inv =
      (fun_ _).inv ≫ (eHomEquiv V f ≫ (eHomCongr V α β).inv) ▷ _ ≫
        _ ◁ (eHomEquiv V g ≫ (eHomCongr V β γ).inv) ≫ eComp V X Y Z :=
  eHomCongr_comp V α.symm β.symm γ.symm f g

end Iso
end CategoryTheory
