/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.IndYoneda
public import Mathlib.CategoryTheory.Limits.Indization.IndObject

/-!
# There are only `v`-many natural transformations between Ind-objects

We provide the instance `LocallySmall.{v} (FullSubcategory (IsIndObject (C := C)))`, which will
serve as the basis for our definition of the category of Ind-objects.

## Future work

The equivalence established here serves as the basis for a well-known calculation of hom-sets of
ind-objects as a limit of a colimit.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v v₁ v₂ u u₁ u₂

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

section

variable {I : Type u₁} [Category.{v₁} I] [HasColimitsOfShape I (Type v)]
  [HasLimitsOfShape Iᵒᵖ (Type v)]
variable {J : Type u₂} [Category.{v₂} J]
  [HasLimitsOfShape Iᵒᵖ (Type (max u v))]
variable (F : I ⥤ C) (G : Cᵒᵖ ⥤ Type v)

/--
Definition of `colimitYonedaHomEquiv` / `colimitYonedaHomEquiv` 的定义

English:
definition colimitYonedaHomEquiv
  signature: :
  body: Equiv.symm Equiv.ulift.symm.trans Equiv.symm Iso.toEquiv calc
  (colimit (F ⋙ yoneda) ⟶ G) ≅ limit (F.op ⋙ G ⋙ uliftFunctor.{u}) :=
        colimitYonedaHomIsoLimitOp _ _
  _ ≅ limit ((F.op ⋙ G) ⋙ uliftFunctor.{u}) :=
        HasLimit.isoOfNatIso (Functor.associator _ _ _).symm
  _ ≅ uliftFunctor.{u

中文:
定义 colimitYonedaHomEquiv
  签名: :
  定义体: Equiv.symm Equiv.ulift.symm.trans Equiv.symm Iso.toEquiv calc
  (colimit (F ⋙ yoneda) ⟶ G) ≅ limit (F.op ⋙ G ⋙ uliftFunctor.{u}) :=
        colimitYonedaHomIsoLimitOp _ _
  _ ≅ limit ((F.op ⋙ G) ⋙ uliftFunctor.{u}) :=
        HasLimit.isoOfNatIso (Functor.associator _ _ _).symm
  _ ≅ uliftFunctor.{u

Depends on / 依赖: Equiv.symm, Equiv.ulift.symm.trans, F.op, Functor, Functor.associator, HasLimit, HasLimit.isoOfNatIso, Iso.toEquiv, associator, colimit, colimitYonedaHomIsoLimitOp, isoOfNatIso, preservesLimitIso, toEquiv, uliftFunctor, yoneda
-/
noncomputable def colimitYonedaHomEquiv :
    (colimit (F ⋙ yoneda) ⟶ G) ≃ (limit (F.op ⋙ G)) :=
Equiv.symm Equiv.ulift.symm.trans Equiv.symm Iso.toEquiv calc
  (colimit (F ⋙ yoneda) ⟶ G) ≅ limit (F.op ⋙ G ⋙ uliftFunctor.{u}) :=
        colimitYonedaHomIsoLimitOp _ _
  _ ≅ limit ((F.op ⋙ G) ⋙ uliftFunctor.{u}) :=
        HasLimit.isoOfNatIso (Functor.associator _ _ _).symm
  _ ≅ uliftFunctor.{u}.obj (limit (F.op ⋙ G)) :=
        (preservesLimitIso _ _).symm

attribute [elementwise] HasLimit.isoOfNatIso_hom_π

set_option backward.defeqAttrib.useBackward true in
unif_hint {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (G : D ⥤ Type*) (X X' : C)
  where X ≟ X'⊢ (F ⋙ G).obj X ≟ (G.obj (F.obj X)) in
@[simp]
/--
theorem `colimitYonedaHomEquiv_π_apply` / 定理 `colimitYonedaHomEquiv_π_apply`

English:
theorem colimitYonedaHomEquiv_π_apply
  given: (η : colimit (F ⋙ yoneda) ⟶ G) (i : Iᵒᵖ)
  proof: by
  simp only [colimitYonedaHomEquiv, Iso.toEquiv, uliftFunctor_obj,
    Iso.trans_def, Iso.trans_assoc, Iso.trans_hom, Iso.trans_inv,
    Category.assoc, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_mk, comp_apply,
    Equiv.ulift_apply]
  have (a : limit ((F.op ⋙ G) ⋙ uliftFunctor.{u, v}

中文:
定理 colimitYonedaHomEquiv_π_apply
  条件: (η : colimit (F ⋙ yoneda) ⟶ G) (i : Iᵒᵖ)
  证明: by
  simp only [colimitYonedaHomEquiv, Iso.toEquiv, uliftFunctor_obj,
    Iso.trans_def, Iso.trans_assoc, Iso.trans_hom, Iso.trans_inv,
    Category.assoc, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_mk, comp_apply,
    Equiv.ulift_apply]
  have (a : limit ((F.op ⋙ G) ⋙ uliftFunctor.{u, v}

Depends on / 依赖: Category, Category.assoc, ConcreteCategory, ConcreteCategory.congr_hom, Eq.trans, Equiv.coe_fn_mk, Equiv.symm_symm, Equiv.symm_trans_apply, Equiv.ulift_apply, F.op, HasLimit, HasLimit.isoOfNatIso_hom_, Iso.toEquiv, Iso.trans_assoc, Iso.trans_def, Iso.trans_hom, Iso.trans_inv, SmallHom, SmallHom.mk_comp_mk, ULift.down
-/
theorem colimitYonedaHomEquiv_π_apply (η : colimit (F ⋙ yoneda) ⟶ G) (i : Iᵒᵖ) :
    dsimp% limit.π (F.op ⋙ G) i (colimitYonedaHomEquiv F G η) =
      η.app (op (F.obj i.unop)) ((colimit.ι (F ⋙ yoneda) i.unop).app _ (𝟙 _)) := by
  simp only [colimitYonedaHomEquiv, Iso.toEquiv, uliftFunctor_obj,
    Iso.trans_def, Iso.trans_assoc, Iso.trans_hom, Iso.trans_inv,
    Category.assoc, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_mk, comp_apply,
    Equiv.ulift_apply]
  have (a : limit ((F.op ⋙ G) ⋙ uliftFunctor.{u, v})) := congrArg ULift.down
    (ConcreteCategory.congr_hom (preservesLimitIso_inv_π uliftFunctor.{u, v} (F.op ⋙ G) i) a)
  refine Eq.trans (dsimp% this _) ?_
  rw [HasLimit.isoOfNatIso_hom_π_apply]
  dsimp
  erw [colimitYonedaHomIsoLimitOp_π_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Small.{v} (colimit (F ⋙ yoneda) ⟶ G)
  body: ⟨_, ⟨colimitYonedaHomEquiv F G⟩⟩

中文:
实例 :
  签名: Small.{v} (colimit (F ⋙ yoneda) ⟶ G)
  定义体: ⟨_, ⟨colimitYonedaHomEquiv F G⟩⟩

Depends on / 依赖: Iso.refl, colimitYonedaHomEquiv, eX.symm, eY.symm, eZ.symm, hasSmallLocalizedHom_of_isos, smallHomMap, smallHomMap_comp
-/
instance : Small.{v} (colimit (F ⋙ yoneda) ⟶ G) where
  equiv_small := ⟨_, ⟨colimitYonedaHomEquiv F G⟩⟩

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LocallySmall.{v} (ObjectProperty.FullSubcategory (IsIndObject (C := C)))
  body: by
    obtain ⟨⟨P⟩⟩ := X.2
    obtain ⟨⟨Q⟩⟩ := Y.2
    let e₁ := IsColimit.coconePointUniqueUpToIso (P.isColimit) (colimit.isColimit _)
    let e₂ := IsColimit.coconePointUniqueUpToIso (Q.isColimit) (colimit.isColimit _)
    let e₃ := Iso.homCongr e₁ e₂
    dsimp only [colimit.cocone_x] at e₃
    ex

中文:
实例 :
  签名: LocallySmall.{v} (ObjectProperty.满子范畴 (是IndObject (C := C)))
  定义体: by
    obtain ⟨⟨P⟩⟩ := X.2
    obtain ⟨⟨Q⟩⟩ := Y.2
    let e₁ := IsColimit.coconePointUniqueUpToIso (P.isColimit) (colimit.isColimit _)
    let e₂ := IsColimit.coconePointUniqueUpToIso (Q.isColimit) (colimit.isColimit _)
    let e₃ := Iso.homCongr e₁ e₂
    dsimp only [colimit.cocone_x] at e₃
    ex
-/
instance : LocallySmall.{v} (ObjectProperty.FullSubcategory (IsIndObject (C := C))) where
  hom_small X Y := by
    obtain ⟨⟨P⟩⟩ := X.2
    obtain ⟨⟨Q⟩⟩ := Y.2
    let e₁ := IsColimit.coconePointUniqueUpToIso (P.isColimit) (colimit.isColimit _)
    let e₂ := IsColimit.coconePointUniqueUpToIso (Q.isColimit) (colimit.isColimit _)
    let e₃ := Iso.homCongr e₁ e₂
    dsimp only [colimit.cocone_x] at e₃
    exact small_map (InducedCategory.homEquiv.trans e₃)

end CategoryTheory
