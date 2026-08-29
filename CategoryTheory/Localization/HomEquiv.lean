/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism
public import Mathlib.CategoryTheory.HomCongr

/-!
# Bijections between morphisms in two localized categories

Given two localization functors `L₁ : C ⥤ D₁` and `L₂ : C ⥤ D₂` for the same
class of morphisms `W : MorphismProperty C`, we define a bijection
`Localization.homEquiv W L₁ L₂ : (L₁.obj X ⟶ L₁.obj Y) ≃ (L₂.obj X ⟶ L₂.obj Y)`
between the types of morphisms in the two localized categories.

More generally, given a localizer morphism `Φ : LocalizerMorphism W₁ W₂`, we define a map
`Φ.homMap L₁ L₂ : (L₁.obj X ⟶ L₁.obj Y) ⟶ (L₂.obj (Φ.functor.obj X) ⟶ L₂.obj (Φ.functor.obj Y))`.
The definition `Localization.homEquiv` is obtained by applying the construction
to the identity localizer morphism.

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C]
  [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃]

namespace LocalizerMorphism

variable {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂} {W₃ : MorphismProperty C₃}
  (Φ : LocalizerMorphism W₁ W₂) (Ψ : LocalizerMorphism W₂ W₃)
  (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]
  (L₃ : C₃ ⥤ D₃) [L₃.IsLocalization W₃]
  {X Y Z : C₁}

/--
Definition of `homMap` / `homMap` 的定义

English:
definition homMap
  signature: (f : L₁.obj X ⟶ L₁.obj Y)
  body: Iso.homCongr ((CatCommSq.iso _ _ _ _).symm.app _) ((CatCommSq.iso _ _ _ _).symm.app _)
    ((Φ.localizedFunctor L₁ L₂).map f)

@[simp]

中文:
定义 homMap
  签名: (f : L₁.obj X ⟶ L₁.obj Y)
  定义体: Iso.homCongr ((CatCommSq.iso _ _ _ _).symm.app _) ((CatCommSq.iso _ _ _ _).symm.app _)
    ((Φ.localizedFunctor L₁ L₂).map f)

@[simp]

Depends on / 依赖: CatCommSq, CatCommSq.iso, Iso.homCongr, homCongr, localizedFunctor, symm.app
-/
noncomputable def homMap (f : L₁.obj X ⟶ L₁.obj Y) :
    L₂.obj (Φ.functor.obj X) ⟶ L₂.obj (Φ.functor.obj Y) :=
  Iso.homCongr ((CatCommSq.iso _ _ _ _).symm.app _) ((CatCommSq.iso _ _ _ _).symm.app _)
    ((Φ.localizedFunctor L₁ L₂).map f)

@[simp]
/--
lemma `homMap_map` / 引理 `homMap_map`

English:
lemma homMap_map
  given: (f : X ⟶ Y)
  proof: by
  dsimp [homMap]
  simp

中文:
引理 homMap_map
  条件: (f : X ⟶ Y)
  证明: by
  dsimp [homMap]
  simp

Depends on / 依赖: Iso.hom, NatTrans, NatTrans.congr_app, _assoc, congr_app, congr_arg, homMap, shiftFunctorAdd
-/
lemma homMap_map (f : X ⟶ Y) :
    Φ.homMap L₁ L₂ (L₁.map f) = L₂.map (Φ.functor.map f) := by
  dsimp [homMap]
  simp

variable (X) in
@[simp]
/--
lemma `homMap_id` / 引理 `homMap_id`

English:
lemma homMap_id
  proof: by
  simpa using Φ.homMap_map L₁ L₂ (𝟙 X)

@[reassoc]

中文:
引理 homMap_id
  证明: by
  simpa using Φ.homMap_map L₁ L₂ (𝟙 X)

@[reassoc]

Depends on / 依赖: Iso.inv, NatTrans, NatTrans.congr_app, _assoc, congr_app, congr_arg, homMap_map, shiftFunctorAdd
-/
lemma homMap_id :
    Φ.homMap L₁ L₂ (𝟙 (L₁.obj X)) = 𝟙 (L₂.obj (Φ.functor.obj X)) := by
  simpa using Φ.homMap_map L₁ L₂ (𝟙 X)

@[reassoc]
/--
lemma `homMap_comp` / 引理 `homMap_comp`

English:
lemma homMap_comp
  given: (f : L₁.obj X ⟶ L₁.obj Y) (g : L₁.obj Y ⟶ L₁.obj Z)
  proof: by
  simp [homMap]

@[reassoc]

中文:
引理 homMap_comp
  条件: (f : L₁.obj X ⟶ L₁.obj Y) (g : L₁.obj Y ⟶ L₁.obj Z)
  证明: by
  simp [homMap]

@[reassoc]

Depends on / 依赖: homMap
-/
lemma homMap_comp (f : L₁.obj X ⟶ L₁.obj Y) (g : L₁.obj Y ⟶ L₁.obj Z) :
    Φ.homMap L₁ L₂ (f ≫ g) = Φ.homMap L₁ L₂ f ≫ Φ.homMap L₁ L₂ g := by
  simp [homMap]

@[reassoc]
/--
lemma `homMap_apply` / 引理 `homMap_apply`

English:
lemma homMap_apply
  given: (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G) (f : L₁.obj X ⟶ L₁.obj Y)
  proof: by
  let G' := Φ.localizedFunctor L₁ L₂
  let e' := CatCommSq.iso Φ.functor L₁ L₂ G'
  change e'.hom.app X ≫ G'.map f ≫ e'.inv.app Y = _
  let : Localization.Lifting L₁ W₁ (Φ.functor ⋙ L₂) G := ⟨e.symm⟩
  let α : G' ≅ G := Localization.liftNatIso L₁ W₁ (L₁ ⋙ G') (Φ.functor ⋙ L₂) _ _ e'.symm
  have :

中文:
引理 homMap_apply
  条件: (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G) (f : L₁.obj X ⟶ L₁.obj Y)
  证明: by
  let G' := Φ.localizedFunctor L₁ L₂
  let e' := CatCommSq.iso Φ.functor L₁ L₂ G'
  change e'.hom.app X ≫ G'.map f ≫ e'.inv.app Y = _
  let : Localization.Lifting L₁ W₁ (Φ.functor ⋙ L₂) G := ⟨e.symm⟩
  let α : G' ≅ G := Localization.liftNatIso L₁ W₁ (L₁ ⋙ G') (Φ.functor ⋙ L₂) _ _ e'.symm
  have :

Depends on / 依赖: CatCommSq, CatCommSq.iso, Functor, Functor.isoWhiskerLeft, Lifting, Localization, Localization.Lifting, Localization.liftNatIso, e.symm, functor, hom.app, inv.app, isoWhiskerLeft, liftNatIso, localizedFunctor
-/
lemma homMap_apply (G : D₁ ⥤ D₂) (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G) (f : L₁.obj X ⟶ L₁.obj Y) :
    Φ.homMap L₁ L₂ f = e.hom.app X ≫ G.map f ≫ e.inv.app Y := by
  let G' := Φ.localizedFunctor L₁ L₂
  let e' := CatCommSq.iso Φ.functor L₁ L₂ G'
  change e'.hom.app X ≫ G'.map f ≫ e'.inv.app Y = _
  let : Localization.Lifting L₁ W₁ (Φ.functor ⋙ L₂) G := ⟨e.symm⟩
  let α : G' ≅ G := Localization.liftNatIso L₁ W₁ (L₁ ⋙ G') (Φ.functor ⋙ L₂) _ _ e'.symm
  have : e = e' ≪≫ Functor.isoWhiskerLeft _ α := by
    ext
    simp [α, this]
  simp [this]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `id_homMap` / 引理 `id_homMap`

English:
lemma id_homMap
  given: (f : L₁.obj X ⟶ L₁.obj Y)
  proof: by
  simpa using (id W₁).homMap_apply L₁ L₁ (𝟭 D₁) (Iso.refl _) f

中文:
引理 id_homMap
  条件: (f : L₁.obj X ⟶ L₁.obj Y)
  证明: by
  simpa using (id W₁).homMap_apply L₁ L₁ (𝟭 D₁) (Iso.refl _) f

Depends on / 依赖: Iso.refl, homMap_apply
-/
lemma id_homMap (f : L₁.obj X ⟶ L₁.obj Y) :
    (id W₁).homMap L₁ L₁ f = f := by
  simpa using (id W₁).homMap_apply L₁ L₁ (𝟭 D₁) (Iso.refl _) f

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `homMap_homMap` / 引理 `homMap_homMap`

English:
lemma homMap_homMap
  given: (f : L₁.obj X ⟶ L₁.obj Y)
  proof: by
  let G := Φ.localizedFunctor L₁ L₂
  let G' := Ψ.localizedFunctor L₂ L₃
  let e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G := CatCommSq.iso _ _ _ _
  let e' : Ψ.functor ⋙ L₃ ≅ L₂ ⋙ G' := CatCommSq.iso _ _ _ _
  rw [Φ.homMap_apply L₁ L₂ G e]; rw [Ψ.homMap_apply L₂ L₃ G' e']; rw [(Φ.comp Ψ).homMap_apply L₁ L₃ (G ⋙

中文:
引理 homMap_homMap
  条件: (f : L₁.obj X ⟶ L₁.obj Y)
  证明: by
  let G := Φ.localizedFunctor L₁ L₂
  let G' := Ψ.localizedFunctor L₂ L₃
  let e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G := CatCommSq.iso _ _ _ _
  let e' : Ψ.functor ⋙ L₃ ≅ L₂ ⋙ G' := CatCommSq.iso _ _ _ _
  rw [Φ.homMap_apply L₁ L₂ G e]; rw [Ψ.homMap_apply L₂ L₃ G' e']; rw [(Φ.comp Ψ).homMap_apply L₁ L₃ (G ⋙

Depends on / 依赖: CatCommSq, CatCommSq.iso, Functor, Functor.associator, Functor.isoWhiskerLeft, Functor.isoWhiskerRight, Functor.map_comp, associator, comp_id, functor, homMap_apply, isoWhiskerLeft, isoWhiskerRight, localizedFunctor, map_comp
-/
lemma homMap_homMap (f : L₁.obj X ⟶ L₁.obj Y) :
    Ψ.homMap L₂ L₃ (Φ.homMap L₁ L₂ f) = (Φ.comp Ψ).homMap L₁ L₃ f := by
  let G := Φ.localizedFunctor L₁ L₂
  let G' := Ψ.localizedFunctor L₂ L₃
  let e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G := CatCommSq.iso _ _ _ _
  let e' : Ψ.functor ⋙ L₃ ≅ L₂ ⋙ G' := CatCommSq.iso _ _ _ _
  rw [Φ.homMap_apply L₁ L₂ G e]; rw [Ψ.homMap_apply L₂ L₃ G' e']; rw [(Φ.comp Ψ).homMap_apply L₁ L₃ (G ⋙ G')
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e' ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e _ ≪≫
      Functor.associator _ _ _)]
  dsimp
  simp only [Functor.map_comp, assoc, comp_id, id_comp]

end LocalizerMorphism

namespace Localization

variable (W : MorphismProperty C) (L₁ : C ⥤ D₁) [L₁.IsLocalization W]
  (L₂ : C ⥤ D₂) [L₂.IsLocalization W] (L₃ : C ⥤ D₃) [L₃.IsLocalization W]
  {X Y Z : C}

set_option backward.isDefEq.respectTransparency false in
/-- Bijection between types of morphisms in two localized categories
for the same class of morphisms `W`. -/
@[simps -isSimp apply]
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: :
  body: (LocalizerMorphism.id W).homMap L₁ L₂
  invFun := (LocalizerMorphism.id W).homMap L₂ L₁
  left_inv f := by
    rw [LocalizerMorphism.homMap_homMap]
    apply LocalizerMorphism.id_homMap
  right_inv g := by
    rw [LocalizerMorphism.homMap_homMap]
    apply LocalizerMorphism.id_homMap

@[simp]

中文:
定义 homEquiv
  签名: :
  定义体: (LocalizerMorphism.id W).homMap L₁ L₂
  invFun := (LocalizerMorphism.id W).homMap L₂ L₁
  left_inv f := by
    rw [LocalizerMorphism.homMap_homMap]
    apply LocalizerMorphism.id_homMap
  right_inv g := by
    rw [LocalizerMorphism.homMap_homMap]
    apply LocalizerMorphism.id_homMap

@[simp]

Depends on / 依赖: LocalizerMorphism, LocalizerMorphism.id, homMap
-/
noncomputable def homEquiv :
    (L₁.obj X ⟶ L₁.obj Y) ≃ (L₂.obj X ⟶ L₂.obj Y) where
  toFun := (LocalizerMorphism.id W).homMap L₁ L₂
  invFun := (LocalizerMorphism.id W).homMap L₂ L₁
  left_inv f := by
    rw [LocalizerMorphism.homMap_homMap]
    apply LocalizerMorphism.id_homMap
  right_inv g := by
    rw [LocalizerMorphism.homMap_homMap]
    apply LocalizerMorphism.id_homMap

@[simp]
/--
lemma `homEquiv_symm_apply` / 引理 `homEquiv_symm_apply`

English:
lemma homEquiv_symm_apply
  given: (g : L₂.obj X ⟶ L₂.obj Y)
  proof: rfl

中文:
引理 homEquiv_symm_apply
  条件: (g : L₂.obj X ⟶ L₂.obj Y)
  证明: rfl
-/
lemma homEquiv_symm_apply (g : L₂.obj X ⟶ L₂.obj Y) :
    (homEquiv W L₁ L₂).symm g = homEquiv W L₂ L₁ g := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `homEquiv_eq` / 引理 `homEquiv_eq`

English:
lemma homEquiv_eq
  given: (G : D₁ ⥤ D₂) (e : L₁ ⋙ G ≅ L₂) (f : L₁.obj X ⟶ L₁.obj Y)
  proof: by
  rw [homEquiv_apply]; rw [LocalizerMorphism.homMap_apply (LocalizerMorphism.id W) L₁ L₂ G e.symm]; rw [Iso.symm_hom]; rw [Iso.symm_inv]

@[simp]

中文:
引理 homEquiv_eq
  条件: (G : D₁ ⥤ D₂) (e : L₁ ⋙ G ≅ L₂) (f : L₁.obj X ⟶ L₁.obj Y)
  证明: by
  rw [homEquiv_apply]; rw [LocalizerMorphism.homMap_apply (LocalizerMorphism.id W) L₁ L₂ G e.symm]; rw [Iso.symm_hom]; rw [Iso.symm_inv]

@[simp]

Depends on / 依赖: Iso.symm_hom, Iso.symm_inv, LocalizerMorphism, LocalizerMorphism.homMap_apply, LocalizerMorphism.id, e.symm, homEquiv_apply, homMap_apply, symm_hom, symm_inv
-/
lemma homEquiv_eq (G : D₁ ⥤ D₂) (e : L₁ ⋙ G ≅ L₂) (f : L₁.obj X ⟶ L₁.obj Y) :
    homEquiv W L₁ L₂ f = e.inv.app X ≫ G.map f ≫ e.hom.app Y := by
  rw [homEquiv_apply]; rw [LocalizerMorphism.homMap_apply (LocalizerMorphism.id W) L₁ L₂ G e.symm]; rw [Iso.symm_hom]; rw [Iso.symm_inv]

@[simp]
/--
lemma `homEquiv_refl` / 引理 `homEquiv_refl`

English:
lemma homEquiv_refl
  given: (f : L₁.obj X ⟶ L₁.obj Y)
  proof: by
  apply LocalizerMorphism.id_homMap

中文:
引理 homEquiv_refl
  条件: (f : L₁.obj X ⟶ L₁.obj Y)
  证明: by
  apply LocalizerMorphism.id_homMap

Depends on / 依赖: LocalizerMorphism, LocalizerMorphism.id_homMap, id_homMap
-/
lemma homEquiv_refl (f : L₁.obj X ⟶ L₁.obj Y) :
    homEquiv W L₁ L₁ f = f := by
  apply LocalizerMorphism.id_homMap

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `homEquiv_trans` / 引理 `homEquiv_trans`

English:
lemma homEquiv_trans
  given: (f : L₁.obj X ⟶ L₁.obj Y)
  proof: by
  dsimp only [homEquiv_apply]
  apply LocalizerMorphism.homMap_homMap

中文:
引理 homEquiv_trans
  条件: (f : L₁.obj X ⟶ L₁.obj Y)
  证明: by
  dsimp only [homEquiv_apply]
  apply LocalizerMorphism.homMap_homMap

Depends on / 依赖: LocalizerMorphism, LocalizerMorphism.homMap_homMap, homEquiv_apply, homMap_homMap
-/
lemma homEquiv_trans (f : L₁.obj X ⟶ L₁.obj Y) :
    homEquiv W L₂ L₃ (homEquiv W L₁ L₂ f) = homEquiv W L₁ L₃ f := by
  dsimp only [homEquiv_apply]
  apply LocalizerMorphism.homMap_homMap

/--
lemma `homEquiv_comp` / 引理 `homEquiv_comp`

English:
lemma homEquiv_comp
  given: (f : L₁.obj X ⟶ L₁.obj Y) (g : L₁.obj Y ⟶ L₁.obj Z)
  proof: by
  apply LocalizerMorphism.homMap_comp

中文:
引理 homEquiv_comp
  条件: (f : L₁.obj X ⟶ L₁.obj Y) (g : L₁.obj Y ⟶ L₁.obj Z)
  证明: by
  apply LocalizerMorphism.homMap_comp

Depends on / 依赖: IsEquivalence, LocalizerMorphism, LocalizerMorphism.homMap_comp, functor, functor.IsEquivalence, homMap_comp, infer_instance, shiftEquiv
-/
lemma homEquiv_comp (f : L₁.obj X ⟶ L₁.obj Y) (g : L₁.obj Y ⟶ L₁.obj Z) :
    homEquiv W L₁ L₂ (f ≫ g) = homEquiv W L₁ L₂ f ≫ homEquiv W L₁ L₂ g := by
  apply LocalizerMorphism.homMap_comp

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `homEquiv_map` / 引理 `homEquiv_map`

English:
lemma homEquiv_map
  given: (f : X ⟶ Y)
  statement: homEquiv W L₁ L₂ (L₁.map f) = L₂.map f
  proof: by
  simp [homEquiv_apply]

中文:
引理 homEquiv_map
  条件: (f : X ⟶ Y)
  结论: homEquiv W L₁ L₂ (L₁.map f) = L₂.map f
  证明: by
  simp [homEquiv_apply]

Depends on / 依赖: homEquiv_apply
-/
lemma homEquiv_map (f : X ⟶ Y) : homEquiv W L₁ L₂ (L₁.map f) = L₂.map f := by
  simp [homEquiv_apply]

set_option backward.defeqAttrib.useBackward true in
variable (X) in
@[simp]
/--
lemma `homEquiv_id` / 引理 `homEquiv_id`

English:
lemma homEquiv_id
  statement: homEquiv W L₁ L₂ (𝟙 (L₁.obj X)) = 𝟙 (L₂.obj X)
  proof: by
  simp [homEquiv_apply]

中文:
引理 homEquiv_id
  结论: homEquiv W L₁ L₂ (𝟙 (L₁.obj X)) = 𝟙 (L₂.obj X)
  证明: by
  simp [homEquiv_apply]

Depends on / 依赖: homEquiv_apply
-/
lemma homEquiv_id : homEquiv W L₁ L₂ (𝟙 (L₁.obj X)) = 𝟙 (L₂.obj X) := by
  simp [homEquiv_apply]

/--
lemma `homEquiv_isoOfHom_inv` / 引理 `homEquiv_isoOfHom_inv`

English:
lemma homEquiv_isoOfHom_inv
  given: (f : Y ⟶ X) (hf : W f)
  proof: by
  rw [← cancel_mono (isoOfHom L₂ W f hf).hom]; rw [Iso.inv_hom_id]; rw [isoOfHom_hom]; rw [← homEquiv_map W L₁ L₂ f]; rw [← homEquiv_comp]; rw [isoOfHom_inv_hom_id]; rw [homEquiv_id]

中文:
引理 homEquiv_isoOfHom_inv
  条件: (f : Y ⟶ X) (hf : W f)
  证明: by
  rw [← cancel_mono (isoOfHom L₂ W f hf).hom]; rw [Iso.inv_hom_id]; rw [isoOfHom_hom]; rw [← homEquiv_map W L₁ L₂ f]; rw [← homEquiv_comp]; rw [isoOfHom_inv_hom_id]; rw [homEquiv_id]

Depends on / 依赖: Iso.inv_hom_id, cancel_mono, homEquiv_comp, homEquiv_id, homEquiv_map, inv_hom_id, isoOfHom, isoOfHom_hom, isoOfHom_inv_hom_id
-/
lemma homEquiv_isoOfHom_inv (f : Y ⟶ X) (hf : W f) :
    homEquiv W L₁ L₂ (isoOfHom L₁ W f hf).inv = (isoOfHom L₂ W f hf).inv := by
  rw [← cancel_mono (isoOfHom L₂ W f hf).hom]; rw [Iso.inv_hom_id]; rw [isoOfHom_hom]; rw [← homEquiv_map W L₁ L₂ f]; rw [← homEquiv_comp]; rw [isoOfHom_inv_hom_id]; rw [homEquiv_id]

end Localization

end CategoryTheory
