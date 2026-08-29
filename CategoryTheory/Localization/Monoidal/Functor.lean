/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Localization.Trifunctor
public import Mathlib.CategoryTheory.Monoidal.Multifunctor
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.Tactic.CategoryTheory.Coherence

/-!

# Universal property of localized monoidal categories

This file proves that, given a monoidal localization functor `L : C ⥤ D`, and a functor
`F : D ⥤ E` to a monoidal category, such that `F` lifts along `L` to a monoidal functor `G`,
then `F` is monoidal. See `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

namespace CategoryTheory

open CategoryTheory MonoidalCategory CategoryTheory.Functor MonoidalCategory.Functor Monoidal
open LaxMonoidal OplaxMonoidal

namespace Localization.Monoidal

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.Monoidal]
  (F : D ⥤ E) (G : C ⥤ E) [G.Monoidal] [W.ContainsIdentities] [Lifting L W G F]

@[simps]
/--
Instance `lifting₂CurriedTensorPre` / 实例 `lifting₂CurriedTensorPre`

English:
instance lifting₂CurriedTensorPre
  signature: :
  body: curriedTensorPreFunctor.mapIso (Lifting.iso L W G F)

@[simps]

中文:
实例 lifting₂CurriedTensorPre
  签名: :
  定义体: curriedTensorPreFunctor.mapIso (Lifting.iso L W G F)

@[simps]

Depends on / 依赖: Lifting, Lifting.iso, curriedTensorPreFunctor, curriedTensorPreFunctor.mapIso, mapIso
-/
instance lifting₂CurriedTensorPre :
    Lifting₂ L L W W (curriedTensorPre G) (curriedTensorPre F) where
  iso := curriedTensorPreFunctor.mapIso (Lifting.iso L W G F)

@[simps]
/--
Instance `lifting₂CurriedTensorPost` / 实例 `lifting₂CurriedTensorPost`

English:
instance lifting₂CurriedTensorPost
  signature: :
  body: (postcompose₂.obj F).mapIso (curriedTensorPreIsoPost L) ≪≫
    curriedTensorPostFunctor.mapIso (Lifting.iso L W G F)

中文:
实例 lifting₂CurriedTensorPost
  签名: :
  定义体: (postcompose₂.obj F).mapIso (curriedTensorPreIsoPost L) ≪≫
    curriedTensorPostFunctor.mapIso (Lifting.iso L W G F)

Depends on / 依赖: curriedTensorPreIsoPost, mapIso
-/
instance lifting₂CurriedTensorPost :
    Lifting₂ L L W W (curriedTensorPost G) (curriedTensorPost F) where
  iso := (postcompose₂.obj F).mapIso (curriedTensorPreIsoPost L) ≪≫
    curriedTensorPostFunctor.mapIso (Lifting.iso L W G F)

/--
Definition of `curriedTensorPreIsoPost` / `curriedTensorPreIsoPost` 的定义

English:
definition curriedTensorPreIsoPost
  signature: : curriedTensorPre F ≅ curriedTensorPost F
  body: lift₂NatIso L L W W (curriedTensorPre G) (curriedTensorPost G) _ _
    (Functor.curriedTensorPreIsoPost G)

中文:
定义 curriedTensorPreIsoPost
  签名: : curriedTensorPre F ≅ curriedTensorPost F
  定义体: lift₂NatIso L L W W (curriedTensorPre G) (curriedTensorPost G) _ _
    (Functor.curriedTensorPreIsoPost G)

Depends on / 依赖: Functor, Functor.curriedTensorPreIsoPost, curriedTensorPost, curriedTensorPre, curriedTensorPreIsoPost
-/
noncomputable def curriedTensorPreIsoPost : curriedTensorPre F ≅ curriedTensorPost F :=
  lift₂NatIso L L W W (curriedTensorPre G) (curriedTensorPost G) _ _
    (Functor.curriedTensorPreIsoPost G)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `curriedTensorPreIsoPost_hom_app_app` / 引理 `curriedTensorPreIsoPost_hom_app_app`

English:
lemma curriedTensorPreIsoPost_hom_app_app
  given: (X₁ X₂ : C)
  proof: Lifting.iso L W G F
    ((curriedTensorPreIsoPost L W F G).hom.app (L.obj X₁)).app (L.obj X₂) =
      (e.hom.app _ otimesₘ e.hom.app _) ≫ LaxMonoidal.μ G X₁ X₂ ≫ e.inv.app _ ≫
        F.map (OplaxMonoidal.δ L _ _) := by
  simp [curriedTensorPreIsoPost]

中文:
引理 curriedTensorPreIsoPost_hom_app_app
  条件: (X₁ X₂ : C)
  证明: Lifting.iso L W G F
    ((curriedTensorPreIsoPost L W F G).hom.app (L.obj X₁)).app (L.obj X₂) =
      (e.hom.app _ otimesₘ e.hom.app _) ≫ LaxMonoidal.μ G X₁ X₂ ≫ e.inv.app _ ≫
        F.map (OplaxMonoidal.δ L _ _) := by
  simp [curriedTensorPreIsoPost]

Depends on / 依赖: Lifting, Lifting.iso
-/
lemma curriedTensorPreIsoPost_hom_app_app (X₁ X₂ : C) :
    letI e := Lifting.iso L W G F
    ((curriedTensorPreIsoPost L W F G).hom.app (L.obj X₁)).app (L.obj X₂) =
      (e.hom.app _ otimesₘ e.hom.app _) ≫ LaxMonoidal.μ G X₁ X₂ ≫ e.inv.app _ ≫
        F.map (OplaxMonoidal.δ L _ _) := by
  simp [curriedTensorPreIsoPost]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `curriedTensorPreIsoPost_hom_app_app'` / 引理 `curriedTensorPreIsoPost_hom_app_app'`

English:
lemma curriedTensorPreIsoPost_hom_app_app'
  statement: {X₁ X₂ : C} {Y₁ Y₂ : D}
  proof: Lifting.iso L W G F
    ((curriedTensorPreIsoPost L W F G).hom.app Y₁).app Y₂ =
      ((F.map e₁.hom ≫ e.hom.app _) otimesₘ (F.map e₂.hom ≫ e.hom.app _)) ≫
        LaxMonoidal.μ G X₁ X₂ ≫ e.inv.app _ ≫
        F.map (OplaxMonoidal.δ L _ _ ≫ (e₁.inv otimesₘ e₂.inv)) := by
  have h₁ := ((curriedTensor

中文:
引理 curriedTensorPreIsoPost_hom_app_app'
  结论: {X₁ X₂ : C} {Y₁ Y₂ : D}
  证明: Lifting.iso L W G F
    ((curriedTensorPreIsoPost L W F G).hom.app Y₁).app Y₂ =
      ((F.map e₁.hom ≫ e.hom.app _) otimesₘ (F.map e₂.hom ≫ e.hom.app _)) ≫
        LaxMonoidal.μ G X₁ X₂ ≫ e.inv.app _ ≫
        F.map (OplaxMonoidal.δ L _ _ ≫ (e₁.inv otimesₘ e₂.inv)) := by
  have h₁ := ((curriedTensor

Depends on / 依赖: Lifting, Lifting.iso
-/
lemma curriedTensorPreIsoPost_hom_app_app' {X₁ X₂ : C} {Y₁ Y₂ : D}
    (e₁ : Y₁ ≅ L.obj X₁) (e₂ : Y₂ ≅ L.obj X₂) :
    letI e := Lifting.iso L W G F
    ((curriedTensorPreIsoPost L W F G).hom.app Y₁).app Y₂ =
      ((F.map e₁.hom ≫ e.hom.app _) otimesₘ (F.map e₂.hom ≫ e.hom.app _)) ≫
        LaxMonoidal.μ G X₁ X₂ ≫ e.inv.app _ ≫
        F.map (OplaxMonoidal.δ L _ _ ≫ (e₁.inv otimesₘ e₂.inv)) := by
  have h₁ := ((curriedTensorPreIsoPost L W F G).hom.app Y₁).naturality e₂.hom
  have h₂ := congr_app ((curriedTensorPreIsoPost L W F G).hom.naturality e₁.hom)
  dsimp at h₁ h₂ ⊢
  rw [← cancel_mono (F.map (Y₁ ◁ e₂.hom))]; rw [← h₁]; rw [← cancel_mono (F.map (e₁.hom ▷ L.obj X₂))]; rw [Category.assoc]; rw [← h₂]; rw [curriedTensorPreIsoPost_hom_app_app]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [← tensorHom_def'_assoc]; rw [tensorHom_comp_tensorHom_assoc]; rw [← Functor.map_comp]; rw [← tensorHom_def']; rw [← Functor.map_comp]; rw [Category.assoc]; rw [tensorHom_comp_tensorHom]; rw [Iso.inv_hom_id]; rw [Iso.inv_hom_id]; rw [tensorHom_id]; rw [id_whiskerRight]; rw [Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
/--
Monoidal structure on `F`, given that `F` lifts along `L` to a monoidal functor `G`,
where `L` is a monoidal localization functor.
-/
@[simps!]
/--
Definition of `functorCoreMonoidalOfComp` / `functorCoreMonoidalOfComp` 的定义

English:
definition functorCoreMonoidalOfComp
  signature: : F.CoreMonoidal
  body: by
  letI e := Lifting.iso L W G F
  refine Functor.CoreMonoidal.ofBifunctor
    (εIso G ≪≫ e.symm.app _ ≪≫ F.mapIso (εIso L).symm) (curriedTensorPreIsoPost L W F G) ?_ ?_ ?_
  · refine natTrans₃_ext L L L W W W (fun X₁ X₂ X₃ => ?_)
    dsimp [e]
    rw [curriedTensorPreIsoPost_hom_app_app]; rw [cur

中文:
定义 functorCoreMonoidalOfComp
  签名: : F.余reMonoidal
  定义体: by
  letI e := Lifting.iso L W G F
  refine Functor.CoreMonoidal.ofBifunctor
    (εIso G ≪≫ e.symm.app _ ≪≫ F.mapIso (εIso L).symm) (curriedTensorPreIsoPost L W F G) ?_ ?_ ?_
  · refine natTrans₃_ext L L L W W W (fun X₁ X₂ X₃ => ?_)
    dsimp [e]
    rw [curriedTensorPreIsoPost_hom_app_app]; rw [cur

Depends on / 依赖: CoreMonoidal, F.mapIso, Functor, Functor.CoreMonoidal.ofBifunctor, Iso.refl, Lifting, Lifting.iso, curriedTensorPreIsoPost, curriedTensorPreIsoPost_hom_app_app, e.symm.app, mapIso, monoidal_simps, ofBifunctor
-/
noncomputable def functorCoreMonoidalOfComp : F.CoreMonoidal := by
  letI e := Lifting.iso L W G F
  refine Functor.CoreMonoidal.ofBifunctor
    (εIso G ≪≫ e.symm.app _ ≪≫ F.mapIso (εIso L).symm) (curriedTensorPreIsoPost L W F G) ?_ ?_ ?_
  · refine natTrans₃_ext L L L W W W (fun X₁ X₂ X₃ => ?_)
    dsimp [e]
    rw [curriedTensorPreIsoPost_hom_app_app]; rw [curriedTensorPreIsoPost_hom_app_app]; rw [curriedTensorPreIsoPost_hom_app_app' L W F G (μIso L _ _) (Iso.refl _)]; rw [curriedTensorPreIsoPost_hom_app_app' L W F G (Iso.refl _) (μIso L _ _)]
    monoidal_simps
    /-
    The following `simp only` block was generated by:
    ```
    simp? [← comp_whiskerRight_assoc, -comp_whiskerRight, whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, -MonoidalCategory.whiskerLeft_comp]
    ```
    -/
    simp only [comp_obj, μIso_hom, Iso.refl_hom, map_id, Category.id_comp, μIso_inv, Iso.refl_inv,
      MonoidalCategory.whiskerLeft_id, Category.comp_id, map_comp, Category.assoc,
      ← comp_whiskerRight_assoc, map_δ_μ_assoc, Iso.inv_hom_id_app, id_whiskerRight,
      whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, whiskerRight_tensor]
    simp [← whisker_exchange_assoc, tensor_whiskerLeft_symm, -tensor_whiskerLeft,
      ← LaxMonoidal.associativity_assoc G, ← Functor.map_comp]
  · refine natTrans_ext L W (fun X₂ => ?_)
    have := NatTrans.congr_app ((curriedTensorPreIsoPost L W F G).hom.naturality (εIso L).inv)
      (L.obj X₂)
    dsimp [e] at this ⊢
    monoidal_simps
    simp [reassoc_of% this, curriedTensorPreIsoPost_hom_app_app, ← comp_whiskerRight_assoc,
      -comp_whiskerRight, tensorHom_def, ← whisker_exchange_assoc, ← map_comp]
  · refine natTrans_ext L W (fun X₁ => ?_)
    have := ((curriedTensorPreIsoPost L W F G).hom.app (L.obj X₁)).naturality (εIso L).inv
    dsimp [e] at this ⊢
    monoidal_simps
    simp [reassoc_of% this, curriedTensorPreIsoPost_hom_app_app, tensorHom_def,
      whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, ← map_comp]

/--
Monoidal structure on `F`, given that `F` lifts along `L` to a monoidal functor `G`,
where `L` is a monoidal localization functor.
-/
@[instance_reducible]
/--
Definition of `functorMonoidalOfComp` / `functorMonoidalOfComp` 的定义

English:
definition functorMonoidalOfComp
  signature: : F.Monoidal
  body: (functorCoreMonoidalOfComp L W F G).toMonoidal

@[reassoc]

中文:
定义 functorMonoidalOfComp
  签名: : F.幺半群
  定义体: (functorCoreMonoidalOfComp L W F G).toMonoidal

@[reassoc]

Depends on / 依赖: functorCoreMonoidalOfComp, toMonoidal
-/
noncomputable def functorMonoidalOfComp : F.Monoidal :=
  (functorCoreMonoidalOfComp L W F G).toMonoidal

@[reassoc]
/--
lemma `functorMonoidalOfComp_ε` / 引理 `functorMonoidalOfComp_ε`

English:
lemma functorMonoidalOfComp_ε
  statement: letI
  proof: functorMonoidalOfComp L W F G
    letI e := Lifting.iso L W G F
    ε F = ε G ≫ e.inv.app _ ≫ F.map (η L) :=
  rfl

@[reassoc]

中文:
引理 functorMonoidalOfComp_ε
  结论: letI
  证明: functorMonoidalOfComp L W F G
    letI e := Lifting.iso L W G F
    ε F = ε G ≫ e.inv.app _ ≫ F.map (η L) :=
  rfl

@[reassoc]

Depends on / 依赖: functorMonoidalOfComp
-/
lemma functorMonoidalOfComp_ε : letI := functorMonoidalOfComp L W F G
    letI e := Lifting.iso L W G F
    ε F = ε G ≫ e.inv.app _ ≫ F.map (η L) :=
  rfl

@[reassoc]
/--
lemma `functorMonoidalOfComp_μ` / 引理 `functorMonoidalOfComp_μ`

English:
lemma functorMonoidalOfComp_μ
  given: (X Y : C)
  statement: letI
  proof: functorMonoidalOfComp L W F G
    letI e := Lifting.iso L W G F
    μ F (L.obj X) (L.obj Y) = (e.hom.app _ otimesₘ e.hom.app _) ≫ μ G X Y ≫ e.inv.app _ ≫
        F.map (δ L _ _) := by
  simp [Functor.CoreMonoidal.toLaxMonoidal_μ, curriedTensorPreIsoPost_hom_app_app]

中文:
引理 functorMonoidalOfComp_μ
  条件: (X Y : C)
  结论: letI
  证明: functorMonoidalOfComp L W F G
    letI e := Lifting.iso L W G F
    μ F (L.obj X) (L.obj Y) = (e.hom.app _ otimesₘ e.hom.app _) ≫ μ G X Y ≫ e.inv.app _ ≫
        F.map (δ L _ _) := by
  simp [Functor.CoreMonoidal.toLaxMonoidal_μ, curriedTensorPreIsoPost_hom_app_app]

Depends on / 依赖: functorMonoidalOfComp
-/
lemma functorMonoidalOfComp_μ (X Y : C) : letI := functorMonoidalOfComp L W F G
    letI e := Lifting.iso L W G F
    μ F (L.obj X) (L.obj Y) = (e.hom.app _ otimesₘ e.hom.app _) ≫ μ G X Y ≫ e.inv.app _ ≫
        F.map (δ L _ _) := by
  simp [Functor.CoreMonoidal.toLaxMonoidal_μ, curriedTensorPreIsoPost_hom_app_app]

/--
Instance `lifting_isMonoidal` / 实例 `lifting_isMonoidal`

English:
instance lifting_isMonoidal
  signature: :
  body: functorMonoidalOfComp L W F G
    (Lifting.iso L W G F).hom.IsMonoidal := by
  let : F.Monoidal := functorMonoidalOfComp L W F G
  refine ⟨?_, fun _ _ => ?_⟩
  · simp [functorMonoidalOfComp_ε]
  · simp [functorMonoidalOfComp_μ]

中文:
实例 lifting_isMonoidal
  签名: :
  定义体: functorMonoidalOfComp L W F G
    (Lifting.iso L W G F).hom.IsMonoidal := by
  let : F.Monoidal := functorMonoidalOfComp L W F G
  refine ⟨?_, fun _ _ => ?_⟩
  · simp [functorMonoidalOfComp_ε]
  · simp [functorMonoidalOfComp_μ]

Depends on / 依赖: functorMonoidalOfComp
-/
instance lifting_isMonoidal :
    letI : F.Monoidal := functorMonoidalOfComp L W F G
    (Lifting.iso L W G F).hom.IsMonoidal := by
  let : F.Monoidal := functorMonoidalOfComp L W F G
  refine ⟨?_, fun _ _ => ?_⟩
  · simp [functorMonoidalOfComp_ε]
  · simp [functorMonoidalOfComp_μ]

end CategoryTheory.Localization.Monoidal
