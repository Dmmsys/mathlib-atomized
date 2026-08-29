/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
public import Mathlib.CategoryTheory.Enriched.FunctorCategory

/-!
# Functor categories are monoidal closed

Let `C` be a monoidal closed category. Let `J` be a category. In this file,
we obtain that the category `J ⥤ C` is monoidal closed if `C` has suitable
limits.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits MonoidalCategory

namespace MonoidalClosed

namespace FunctorCategory

open Enriched.FunctorCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]
  {J : Type u₂} [Category.{v₂} J]
  [forall (F₁ F₂ : J ⥤ C), HasFunctorEnrichedHom C F₁ F₂]

attribute [local simp] enrichedCategorySelf_hom

section

variable {F₁ F₂ F₂' F₃ F₃' : J ⥤ C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: : (F₁ otimes F₂ ⟶ F₃) ≃ (F₂ ⟶ functorEnrichedHom C F₁ F₃) where
  body: { app j := end_.lift (fun k => F₂.map k.hom ≫ curry (f.app k.right))
        (fun k₁ k₂ φ => by
          dsimp
          simp only [enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Category.assoc,
            enrichedOrdinaryCategorySelf_eHomWhiskerRight]
          rw [← curry_natural_left_assoc]; rw [← curry_natural_left_assoc]; rw [← curry_natural_right]; rw [curry_pre_app]; rw [Category.assoc]; rw [← f.naturality φ.right]; rw [Monoidal.tensorObj_map]; rw [tensorHom_def_assoc]; rw [← Under.w φ]; rw [Functor.map_comp]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [whisker_exchange_assoc]) }
  invFun g :=
    { app j := uncurry (g.app j ≫ enrichedHomπ C _ _ (Under.mk (𝟙 j)))
      naturality j j' φ := by
        dsimp
        rw [← uncurry_natural_right]; rw [tensorHom_def'_assoc]; rw [← uncurry_pre_app]; rw [← uncurry_natural_left]; rw [Category.assoc]; rw [Category.assoc]; rw [NatTrans.naturality_assoc]; rw [functorEnrichedHom_map]; rw [end_.lift_π_assoc]; rw [enrichedOrdinaryCategorySelf_eHomWhiskerRight]
        dsimp
        rw [pre_id]; rw [NatTrans.id_app]; rw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft]; rw [Functor.map_id]; rw [Category.comp_id]; rw [Category.comp_id]
        congr 2
        rw [← enrichedOrdinaryCategorySelf_eHomWhiskerRight]; rw [← enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
        let α : Under.mk (𝟙 j) ⟶ (Under.map φ).obj (Under.mk (𝟙 j')) := Under.homMk φ
        exact (enrichedHom_condition C (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₃) α).symm }
  left_inv f := by cat_disch
  right_inv g := by
    ext j
    dsimp
    ext k
    -- this following list was obtained by
    -- `simp? [enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Under.map, Comma.mapLeft]`
    simp only [diagram_obj_obj, Functor.comp_obj, Under.forget_obj, enrichedCategorySelf_hom,
      curry_uncurry, NatTrans.naturality_assoc, functorEnrichedHom_obj, functorEnrichedHom_map,
      Under.map, Comma.mapLeft, Functor.const_obj_obj, Functor.id_obj, Discrete.natTrans_app,
      StructuredArrow.left_eq_id, end_.lift_π, Under.mk_right, Under.mk_hom, Iso.refl_inv,
      NatTrans.id_app, enrichedOrdinaryCategorySelf_eHomWhiskerRight, pre_id, Iso.refl_hom,
      enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Functor.map_id, Category.comp_id]
    congr
    simp

中文:
定义 homEquiv
  签名: : (F₁ otimes F₂ ⟶ F₃) ≃ (F₂ ⟶ functorEnrichedHom C F₁ F₃) where
  定义体: { app j := end_.lift (fun k => F₂.map k.hom ≫ curry (f.app k.right))
        (fun k₁ k₂ φ => by
          dsimp
          simp only [enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Category.assoc,
            enrichedOrdinaryCategorySelf_eHomWhiskerRight]
          rw [← curry_natural_left_assoc]; rw [← curry_natural_left_assoc]; rw [← curry_natural_right]; rw [curry_pre_app]; rw [Category.assoc]; rw [← f.naturality φ.right]; rw [Monoidal.tensorObj_map]; rw [tensorHom_def_assoc]; rw [← Under.w φ]; rw [Functor.map_comp]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [whisker_exchange_assoc]) }
  invFun g :=
    { app j := uncurry (g.app j ≫ enrichedHomπ C _ _ (Under.mk (𝟙 j)))
      naturality j j' φ := by
        dsimp
        rw [← uncurry_natural_right]; rw [tensorHom_def'_assoc]; rw [← uncurry_pre_app]; rw [← uncurry_natural_left]; rw [Category.assoc]; rw [Category.assoc]; rw [NatTrans.naturality_assoc]; rw [functorEnrichedHom_map]; rw [end_.lift_π_assoc]; rw [enrichedOrdinaryCategorySelf_eHomWhiskerRight]
        dsimp
        rw [pre_id]; rw [NatTrans.id_app]; rw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft]; rw [Functor.map_id]; rw [Category.comp_id]; rw [Category.comp_id]
        congr 2
        rw [← enrichedOrdinaryCategorySelf_eHomWhiskerRight]; rw [← enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
        let α : Under.mk (𝟙 j) ⟶ (Under.map φ).obj (Under.mk (𝟙 j')) := Under.homMk φ
        exact (enrichedHom_condition C (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₃) α).symm }
  left_inv f := by cat_disch
  right_inv g := by
    ext j
    dsimp
    ext k
    -- this following list was obtained by
    -- `simp? [enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Under.map, Comma.mapLeft]`
    simp only [diagram_obj_obj, Functor.comp_obj, Under.forget_obj, enrichedCategorySelf_hom,
      curry_uncurry, NatTrans.naturality_assoc, functorEnrichedHom_obj, functorEnrichedHom_map,
      Under.map, Comma.mapLeft, Functor.const_obj_obj, Functor.id_obj, Discrete.natTrans_app,
      StructuredArrow.left_eq_id, end_.lift_π, Under.mk_right, Under.mk_hom, Iso.refl_inv,
      NatTrans.id_app, enrichedOrdinaryCategorySelf_eHomWhiskerRight, pre_id, Iso.refl_hom,
      enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Functor.map_id, Category.comp_id]
    congr
    simp

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, Monoidal, Monoidal.tensorObj_map, MonoidalCategory, MonoidalCategory.whisk, Under.w, curry_natural_left_assoc, curry_natural_right, curry_pre_app, end_, end_.lift, enrichedOrdinaryCategorySelf_eHomWhiskerLeft, enrichedOrdinaryCategorySelf_eHomWhiskerRight, f.app, f.naturality, k.hom, k.right
-/
noncomputable def homEquiv : (F₁ otimes F₂ ⟶ F₃) ≃ (F₂ ⟶ functorEnrichedHom C F₁ F₃) where
  toFun f :=
    { app j := end_.lift (fun k => F₂.map k.hom ≫ curry (f.app k.right))
        (fun k₁ k₂ φ => by
          dsimp
          simp only [enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Category.assoc,
            enrichedOrdinaryCategorySelf_eHomWhiskerRight]
          rw [← curry_natural_left_assoc]; rw [← curry_natural_left_assoc]; rw [← curry_natural_right]; rw [curry_pre_app]; rw [Category.assoc]; rw [← f.naturality φ.right]; rw [Monoidal.tensorObj_map]; rw [tensorHom_def_assoc]; rw [← Under.w φ]; rw [Functor.map_comp]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [whisker_exchange_assoc]) }
  invFun g :=
    { app j := uncurry (g.app j ≫ enrichedHomπ C _ _ (Under.mk (𝟙 j)))
      naturality j j' φ := by
        dsimp
        rw [← uncurry_natural_right]; rw [tensorHom_def'_assoc]; rw [← uncurry_pre_app]; rw [← uncurry_natural_left]; rw [Category.assoc]; rw [Category.assoc]; rw [NatTrans.naturality_assoc]; rw [functorEnrichedHom_map]; rw [end_.lift_π_assoc]; rw [enrichedOrdinaryCategorySelf_eHomWhiskerRight]
        dsimp
        rw [pre_id]; rw [NatTrans.id_app]; rw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft]; rw [Functor.map_id]; rw [Category.comp_id]; rw [Category.comp_id]
        congr 2
        rw [← enrichedOrdinaryCategorySelf_eHomWhiskerRight]; rw [← enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
        let α : Under.mk (𝟙 j) ⟶ (Under.map φ).obj (Under.mk (𝟙 j')) := Under.homMk φ
        exact (enrichedHom_condition C (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₃) α).symm }
  left_inv f := by cat_disch
  right_inv g := by
    ext j
    dsimp
    ext k
    -- this following list was obtained by
    -- `simp? [enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Under.map, Comma.mapLeft]`
    simp only [diagram_obj_obj, Functor.comp_obj, Under.forget_obj, enrichedCategorySelf_hom,
      curry_uncurry, NatTrans.naturality_assoc, functorEnrichedHom_obj, functorEnrichedHom_map,
      Under.map, Comma.mapLeft, Functor.const_obj_obj, Functor.id_obj, Discrete.natTrans_app,
      StructuredArrow.left_eq_id, end_.lift_π, Under.mk_right, Under.mk_hom, Iso.refl_inv,
      NatTrans.id_app, enrichedOrdinaryCategorySelf_eHomWhiskerRight, pre_id, Iso.refl_hom,
      enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Functor.map_id, Category.comp_id]
    congr
    simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `homEquiv_naturality_two_symm` / 引理 `homEquiv_naturality_two_symm`

English:
lemma homEquiv_naturality_two_symm
  given: (f₂ : F₂ ⟶ F₂') (g : F₂' ⟶ functorEnrichedHom C F₁ F₃)
  proof: by
  dsimp [homEquiv]
  ext j
  simp [← uncurry_natural_left]

中文:
引理 homEquiv_naturality_two_symm
  条件: (f₂ : F₂ ⟶ F₂') (g : F₂' ⟶ functorEnrichedHom C F₁ F₃)
  证明: by
  dsimp [homEquiv]
  ext j
  simp [← uncurry_natural_left]

Depends on / 依赖: homEquiv, uncurry_natural_left
-/
lemma homEquiv_naturality_two_symm (f₂ : F₂ ⟶ F₂') (g : F₂' ⟶ functorEnrichedHom C F₁ F₃) :
    homEquiv.symm (f₂ ≫ g) = F₁ ◁ f₂ ≫ homEquiv.symm g := by
  dsimp [homEquiv]
  ext j
  simp [← uncurry_natural_left]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `homEquiv_naturality_three` / 引理 `homEquiv_naturality_three`

English:
lemma homEquiv_naturality_three
  statement: [forall (F₁ F₂ : J ⥤ C), HasEnrichedHom C F₁ F₂]
  proof: by
  dsimp [homEquiv]
  ext j
  dsimp
  ext k
  rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [end_.lift_π]; rw [enrichedComp_π]; rw [tensorHom_def]; rw [Category.assoc]; rw [whisker_exchange_assoc]; rw [whiskerRight_id_assoc]; rw [Iso.inv_hom_id_assoc]; rw [end_.lift_π_assoc]; rw [Category.assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [Category.assoc]; rw [end_.lift_π]; rw [enrichedOrdinaryCategorySelf_eHomWhiskerRight]; rw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
  dsimp
  rw [pre_id]; rw [NatTrans.id_app]; rw [Functor.map_id]; rw [Category.comp_id]; rw [Category.comp_id]; rw [homEquiv_apply_π]; rw [curry_natural_right]
  congr 2
  symm
  apply enrichedOrdinaryCategorySelf_eHomWhiskerLeft

中文:
引理 homEquiv_naturality_three
  结论: [对任意 (F₁ F₂ : J ⥤ C), HasEnrichedHom C F₁ F₂]
  证明: by
  dsimp [homEquiv]
  ext j
  dsimp
  ext k
  rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [end_.lift_π]; rw [enrichedComp_π]; rw [tensorHom_def]; rw [Category.assoc]; rw [whisker_exchange_assoc]; rw [whiskerRight_id_assoc]; rw [Iso.inv_hom_id_assoc]; rw [end_.lift_π_assoc]; rw [Category.assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [Category.assoc]; rw [end_.lift_π]; rw [enrichedOrdinaryCategorySelf_eHomWhiskerRight]; rw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
  dsimp
  rw [pre_id]; rw [NatTrans.id_app]; rw [Functor.map_id]; rw [Category.comp_id]; rw [Category.comp_id]; rw [homEquiv_apply_π]; rw [curry_natural_right]
  congr 2
  symm
  apply enrichedOrdinaryCategorySelf_eHomWhiskerLeft

Depends on / 依赖: Category, Category.assoc, Iso.inv_hom_id_assoc, MonoidalCategory, MonoidalCategory.whiskerLeft_comp_assoc, end_, end_.lift_, enrichedOrdinaryCategorySelf_eHomWhiskerLeft, enrichedOrdinaryCategorySelf_eHomWhiskerRight, homEquiv, inv_hom_id_assoc, tensorHom_def, whiskerLeft_comp_assoc, whiskerRight_id_assoc, whisker_exchange_assoc
-/
lemma homEquiv_naturality_three [forall (F₁ F₂ : J ⥤ C), HasEnrichedHom C F₁ F₂]
    (f : F₁ otimes F₂ ⟶ F₃) (f₃ : F₃ ⟶ F₃') :
    homEquiv (f ≫ f₃) = homEquiv f ≫ (ρ_ _).inv ≫ _ ◁ functorHomEquiv _ f₃ ≫
      functorEnrichedComp C F₁ F₃ F₃' := by
  dsimp [homEquiv]
  ext j
  dsimp
  ext k
  rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [end_.lift_π]; rw [enrichedComp_π]; rw [tensorHom_def]; rw [Category.assoc]; rw [whisker_exchange_assoc]; rw [whiskerRight_id_assoc]; rw [Iso.inv_hom_id_assoc]; rw [end_.lift_π_assoc]; rw [Category.assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [Category.assoc]; rw [end_.lift_π]; rw [enrichedOrdinaryCategorySelf_eHomWhiskerRight]; rw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
  dsimp
  rw [pre_id]; rw [NatTrans.id_app]; rw [Functor.map_id]; rw [Category.comp_id]; rw [Category.comp_id]; rw [homEquiv_apply_π]; rw [curry_natural_right]
  congr 2
  symm
  apply enrichedOrdinaryCategorySelf_eHomWhiskerLeft

end

variable [forall (F₁ F₂ : J ⥤ C), HasEnrichedHom C F₁ F₂]
attribute [local instance] Enriched.FunctorCategory.functorEnrichedOrdinaryCategory

/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: (F : J ⥤ C)
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => homEquiv
      homEquiv_naturality_left_symm := homEquiv_naturality_two_symm
      homEquiv_naturality_right := homEquiv_naturality_three }

中文:
定义 adj
  签名: (F : J ⥤ C)
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => homEquiv
      homEquiv_naturality_left_symm := homEquiv_naturality_two_symm
      homEquiv_naturality_right := homEquiv_naturality_three }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right, homEquiv_naturality_three, homEquiv_naturality_two_symm, mkOfHomEquiv
-/
noncomputable def adj (F : J ⥤ C) :
    MonoidalCategory.tensorLeft F ⊣ (eHomFunctor _ _).obj ⟨F⟩ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => homEquiv
      homEquiv_naturality_left_symm := homEquiv_naturality_two_symm
      homEquiv_naturality_right := homEquiv_naturality_three }

/-- When `C` is monoidal closed and has suitable limits,
then for any `F : J ⥤ C`, `tensorLeft F` has a right adjoint. -/
@[instance_reducible]
/--
Definition of `closed` / `closed` 的定义

English:
definition closed
  signature: (F : J ⥤ C)
  body: (eHomFunctor _ _).obj ⟨F⟩
  adj := adj F

中文:
定义 closed
  签名: (F : J ⥤ C)
  定义体: (eHomFunctor _ _).obj ⟨F⟩
  adj := adj F

Depends on / 依赖: eHomFunctor
-/
noncomputable def closed (F : J ⥤ C) : Closed F where
  rightAdj := (eHomFunctor _ _).obj ⟨F⟩
  adj := adj F

/-- If `C` is monoidal closed and has suitable limits, the functor
category `J ⥤ C` is monoidal closed. -/
noncomputable scoped instance monoidalClosed : MonoidalClosed (J ⥤ C) where
  closed := closed

end FunctorCategory

end MonoidalClosed

end CategoryTheory
