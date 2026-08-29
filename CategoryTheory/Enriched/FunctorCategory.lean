/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.Shapes.End

/-!
# Functor categories are enriched

If `C` is a `V`-enriched ordinary category, then `J ⥤ C` is also
both a `V`-enriched ordinary category and a `J ⥤ V`-enriched
ordinary category, provided `C` has suitable limits.

We first define the `V`-enriched structure on `J ⥤ C` by saying
that if `F₁` and `F₂` are in `J ⥤ C`, then `enrichedHom V F₁ F₂ : V`
is a suitable limit involving `F₁.obj j ⟶[V] F₂.obj j` for all `j : C`.
The `J ⥤ V` object of morphisms `functorEnrichedHom V F₁ F₂ : J ⥤ V`
is defined by sending `j : J` to the previously defined `enrichedHom`
for the "restriction" of `F₁` and `F₂` to the category `Under j`.
The definition `isLimitConeFunctorEnrichedHom` shows that
`enriched V F₁ F₂` is the limit of the functor `functorEnrichedHom V F₁ F₂`.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Enriched.FunctorCategory

open Category MonoidalCategory Limits CategoryTheory.Functor

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V]
  {C : Type u₂} [Category.{v₂} C] {J : Type u₃} [Category.{v₃} J]
  {K : Type u₄} [Category.{v₄} K] [EnrichedOrdinaryCategory V C]

variable (F₁ F₂ F₃ F₄ : J ⥤ C)

/-- Given two functors `F₁` and `F₂` from a category `J` to a `V`-enriched
ordinary category `C`, this is the diagram `Jᵒᵖ ⥤ J ⥤ V` whose end shall be
the `V`-morphisms in `J ⥤ V` from `F₁` to `F₂`. -/
@[simps!]
/--
Definition of `diagram` / `diagram` 的定义

English:
definition diagram
  signature: : Jᵒᵖ ⥤ J ⥤ V
  body: F₁.op ⋙ eHomFunctor V C ⋙ (whiskeringLeft J C V).obj F₂

中文:
定义 diagram
  签名: : Jᵒᵖ ⥤ J ⥤ V
  定义体: F₁.op ⋙ eHomFunctor V C ⋙ (whiskeringLeft J C V).obj F₂

Depends on / 依赖: eHomFunctor, whiskeringLeft
-/
def diagram : Jᵒᵖ ⥤ J ⥤ V := F₁.op ⋙ eHomFunctor V C ⋙ (whiskeringLeft J C V).obj F₂

/--
Definition of `HasEnrichedHom` / `HasEnrichedHom` 的定义

English:
abbreviation HasEnrichedHom
  body: HasEnd (diagram V F₁ F₂)

中文:
缩写 HasEnrichedHom
  定义体: HasEnd (diagram V F₁ F₂)

Depends on / 依赖: HasEnd, diagram
-/
abbrev HasEnrichedHom := HasEnd (diagram V F₁ F₂)

section

variable [HasEnrichedHom V F₁ F₂]

/--
Definition of `enrichedHom` / `enrichedHom` 的定义

English:
abbreviation enrichedHom
  signature: : V
  body: end_ (diagram V F₁ F₂)

中文:
缩写 enrichedHom
  签名: : V
  定义体: end_ (diagram V F₁ F₂)

Depends on / 依赖: diagram, end_
-/
noncomputable abbrev enrichedHom : V := end_ (diagram V F₁ F₂)

/--
Definition of `enrichedHomπ` / `enrichedHomπ` 的定义

English:
abbreviation enrichedHomπ
  signature: (j : J)
  body: end_.π _ j

@[reassoc]

中文:
缩写 enrichedHomπ
  签名: (j : J)
  定义体: end_.π _ j

@[reassoc]

Depends on / 依赖: end_
-/
noncomputable abbrev enrichedHomπ (j : J) : enrichedHom V F₁ F₂ ⟶ F₁.obj j ⟶[V] F₂.obj j :=
  end_.π _ j

@[reassoc]
/--
lemma `enrichedHom_condition` / 引理 `enrichedHom_condition`

English:
lemma enrichedHom_condition
  given: {i j : J} (f : i ⟶ j)
  proof: end_.condition (diagram V F₁ F₂) f

@[reassoc]

中文:
引理 enrichedHom_condition
  条件: {i j : J} (f : i ⟶ j)
  证明: end_.condition (diagram V F₁ F₂) f

@[reassoc]

Depends on / 依赖: condition, diagram, end_, end_.condition
-/
lemma enrichedHom_condition {i j : J} (f : i ⟶ j) :
    enrichedHomπ V F₁ F₂ i ≫ eHomWhiskerLeft V (F₁.obj i) (F₂.map f) =
    enrichedHomπ V F₁ F₂ j ≫ eHomWhiskerRight V (F₁.map f) (F₂.obj j) :=
  end_.condition (diagram V F₁ F₂) f

@[reassoc]
/--
lemma `enrichedHom_condition'` / 引理 `enrichedHom_condition'`

English:
lemma enrichedHom_condition'
  given: {i j : J} (f : i ⟶ j)
  proof: end_.condition (diagram V F₁ F₂) f

中文:
引理 enrichedHom_condition'
  条件: {i j : J} (f : i ⟶ j)
  证明: end_.condition (diagram V F₁ F₂) f

Depends on / 依赖: condition, diagram, end_, end_.condition
-/
lemma enrichedHom_condition' {i j : J} (f : i ⟶ j) :
    enrichedHomπ V F₁ F₂ i ≫ (ρ_ _).inv ≫
      _ ◁ (eHomEquiv V) (F₂.map f) ≫ eComp V _ _ _ =
    enrichedHomπ V F₁ F₂ j ≫ (fun_ _).inv ≫
      (eHomEquiv V) (F₁.map f) ▷ _ ≫ eComp V _ _ _ :=
  end_.condition (diagram V F₁ F₂) f

variable {F₁ F₂}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: : (F₁ ⟶ F₂) ≃ (𝟙_ V ⟶ enrichedHom V F₁ F₂) where
  body: end_.lift (fun j => eHomEquiv V (τ.app j)) (fun i j f => by
    trans eHomEquiv V (τ.app i ≫ F₂.map f)
    · dsimp
      simp only [eHomEquiv_comp, tensorHom_def_assoc, MonoidalCategory.whiskerRight_id,
        ← unitors_equal, assoc, Iso.inv_hom_id_assoc, eHomWhiskerLeft]
    · dsimp
      simp onl

中文:
定义 homEquiv
  签名: : (F₁ ⟶ F₂) ≃ (𝟙_ V ⟶ enrichedHom V F₁ F₂) where
  定义体: end_.lift (fun j => eHomEquiv V (τ.app j)) (fun i j f => by
    trans eHomEquiv V (τ.app i ≫ F₂.map f)
    · dsimp
      simp only [eHomEquiv_comp, tensorHom_def_assoc, MonoidalCategory.whiskerRight_id,
        ← unitors_equal, assoc, Iso.inv_hom_id_assoc, eHomWhiskerLeft]
    · dsimp
      simp onl

Depends on / 依赖: Iso.inv_hom_id_assoc, MonoidalCategory, MonoidalCategory.whiskerRight_id, NatTrans, NatTrans.naturality, eHomEquiv, eHomEquiv_comp, eHomWhiskerLeft, eHomWhiskerRight, end_, end_.lift, id_whiskerLeft, invFun, inv_hom_id_assoc, naturality, tensorHom_def, tensorHom_def_assoc, unitors_equal, whiskerRight_id
-/
noncomputable def homEquiv : (F₁ ⟶ F₂) ≃ (𝟙_ V ⟶ enrichedHom V F₁ F₂) where
  toFun τ := end_.lift (fun j => eHomEquiv V (τ.app j)) (fun i j f => by
    trans eHomEquiv V (τ.app i ≫ F₂.map f)
    · dsimp
      simp only [eHomEquiv_comp, tensorHom_def_assoc, MonoidalCategory.whiskerRight_id,
        ← unitors_equal, assoc, Iso.inv_hom_id_assoc, eHomWhiskerLeft]
    · dsimp
      simp only [← NatTrans.naturality, eHomEquiv_comp, tensorHom_def', id_whiskerLeft,
        assoc, Iso.inv_hom_id_assoc, eHomWhiskerRight])
  invFun g :=
    { app := fun j => (eHomEquiv V).symm (g ≫ end_.π _ j)
      naturality := fun i j f => (eHomEquiv V).injective (by
        simp only [eHomEquiv_comp, Equiv.apply_symm_apply, Iso.cancel_iso_inv_left]
        conv_rhs =>
          rw [tensorHom_def_assoc]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [assoc]; rw [enrichedHom_condition' V F₁ F₂ f]
        conv_lhs =>
          rw [tensorHom_def'_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [id_whiskerLeft_assoc]; rw [id_whiskerLeft_assoc]; rw [Iso.inv_hom_id_assoc]; rw [unitors_equal]) }
  left_inv τ := by aesop
  right_inv g := by aesop

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `homEquiv_apply_π` / 引理 `homEquiv_apply_π`

English:
lemma homEquiv_apply_π
  given: (τ : F₁ ⟶ F₂) (j : J)
  proof: by
  simp [homEquiv]

中文:
引理 homEquiv_apply_π
  条件: (τ : F₁ ⟶ F₂) (j : J)
  证明: by
  simp [homEquiv]

Depends on / 依赖: homEquiv
-/
lemma homEquiv_apply_π (τ : F₁ ⟶ F₂) (j : J) :
    homEquiv V τ ≫ enrichedHomπ V _ _ j = eHomEquiv V (τ.app j) := by
  simp [homEquiv]

end

section

variable [HasEnrichedHom V F₁ F₁]

/--
Definition of `enrichedId` / `enrichedId` 的定义

English:
definition enrichedId
  signature: : 𝟙_ V ⟶ enrichedHom V F₁ F₁
  body: homEquiv _ (𝟙 F₁)

@[reassoc (attr := simp)]

中文:
定义 enrichedId
  签名: : 𝟙_ V ⟶ enrichedHom V F₁ F₁
  定义体: homEquiv _ (𝟙 F₁)

@[reassoc (attr := simp)]

Depends on / 依赖: homEquiv
-/
noncomputable def enrichedId : 𝟙_ V ⟶ enrichedHom V F₁ F₁ := homEquiv _ (𝟙 F₁)

@[reassoc (attr := simp)]
/--
lemma `enrichedId_π` / 引理 `enrichedId_π`

English:
lemma enrichedId_π
  given: (j : J)
  statement: enrichedId V F₁ ≫ end_.π _ j = eId V (F₁.obj j)
  proof: by
  simp [enrichedId]

@[simp]

中文:
引理 enrichedId_π
  条件: (j : J)
  结论: enrichedId V F₁ ≫ end_.π _ j = eId V (F₁.obj j)
  证明: by
  simp [enrichedId]

@[simp]

Depends on / 依赖: enrichedId
-/
lemma enrichedId_π (j : J) : enrichedId V F₁ ≫ end_.π _ j = eId V (F₁.obj j) := by
  simp [enrichedId]

@[simp]
/--
lemma `homEquiv_id` / 引理 `homEquiv_id`

English:
lemma homEquiv_id
  statement: homEquiv V (𝟙 F₁) = enrichedId V F₁
  proof: rfl

中文:
引理 homEquiv_id
  结论: homEquiv V (𝟙 F₁) = enrichedId V F₁
  证明: rfl
-/
lemma homEquiv_id : homEquiv V (𝟙 F₁) = enrichedId V F₁ := rfl

end

section

variable [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₂ F₃] [HasEnrichedHom V F₁ F₃]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `enrichedComp` / `enrichedComp` 的定义

English:
definition enrichedComp
  signature: : enrichedHom V F₁ F₂ otimes enrichedHom V F₂ F₃ ⟶ enrichedHom V F₁ F₃
  body: end_.lift (fun j => (end_.π _ j otimesₘ end_.π _ j) ≫ eComp V _ _ _) (fun i j f => by
    dsimp
    trans (end_.π (diagram V F₁ F₂) i otimesₘ end_.π (diagram V F₂ F₃) j) ≫
      (ρ_ _).inv ▷ _ ≫ (_ ◁ (eHomEquiv V (F₂.map f))) ▷ _ ≫ eComp V _ (F₂.obj i) _ ▷ _ ≫
        eComp V _ (F₂.obj j) _
    · ha

中文:
定义 enrichedComp
  签名: : enrichedHom V F₁ F₂ otimes enrichedHom V F₂ F₃ ⟶ enrichedHom V F₁ F₃
  定义体: end_.lift (fun j => (end_.π _ j otimesₘ end_.π _ j) ≫ eComp V _ _ _) (fun i j f => by
    dsimp
    trans (end_.π (diagram V F₁ F₂) i otimesₘ end_.π (diagram V F₂ F₃) j) ≫
      (ρ_ _).inv ▷ _ ≫ (_ ◁ (eHomEquiv V (F₂.map f))) ▷ _ ≫ eComp V _ (F₂.obj i) _ ▷ _ ≫
        eComp V _ (F₂.obj j) _
    · ha

Depends on / 依赖: condition, conv_lhs, conv_rhs, diagram, eHomEquiv, eHomWhiskerLeft, eHomWhiskerRight, e_assoc, end_, end_.condition, end_.lift, tensorHom_def_assoc, triangl, whisker_assoc_assoc
-/
noncomputable def enrichedComp : enrichedHom V F₁ F₂ otimes enrichedHom V F₂ F₃ ⟶ enrichedHom V F₁ F₃ :=
  end_.lift (fun j => (end_.π _ j otimesₘ end_.π _ j) ≫ eComp V _ _ _) (fun i j f => by
    dsimp
    trans (end_.π (diagram V F₁ F₂) i otimesₘ end_.π (diagram V F₂ F₃) j) ≫
      (ρ_ _).inv ▷ _ ≫ (_ ◁ (eHomEquiv V (F₂.map f))) ▷ _ ≫ eComp V _ (F₂.obj i) _ ▷ _ ≫
        eComp V _ (F₂.obj j) _
    · have := end_.condition (diagram V F₂ F₃) f
      dsimp [eHomWhiskerLeft, eHomWhiskerRight] at this ⊢
      conv_lhs => rw [assoc, tensorHom_def_assoc]
      conv_rhs =>
        rw [tensorHom_def_assoc]; rw [whisker_assoc_assoc]; rw [e_assoc]; rw [triangle_assoc_comp_right_inv_assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [assoc]; rw [assoc]; rw [← this]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [← e_assoc]; rw [whiskerLeft_rightUnitor_inv_assoc]; rw [associator_inv_naturality_right_assoc]; rw [Iso.hom_inv_id_assoc]; rw [whisker_exchange_assoc]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [Iso.inv_hom_id_assoc]
    · have := end_.condition (diagram V F₁ F₂) f
      dsimp [eHomWhiskerLeft, eHomWhiskerRight] at this ⊢
      conv_lhs =>
        rw [tensorHom_def'_assoc]; rw [← comp_whiskerRight_assoc]; rw [← comp_whiskerRight_assoc]; rw [← comp_whiskerRight_assoc]; rw [assoc]; rw [assoc]; rw [this]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [leftUnitor_inv_whiskerRight_assoc]; rw [← associator_inv_naturality_left_assoc]; rw [← e_assoc']; rw [Iso.inv_hom_id_assoc]; rw [← whisker_exchange_assoc]; rw [id_whiskerLeft_assoc]; rw [Iso.inv_hom_id_assoc]
      conv_rhs => rw [assoc, tensorHom_def'_assoc])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `enrichedComp_π` / 引理 `enrichedComp_π`

English:
lemma enrichedComp_π
  given: (j : J)
  proof: by
  simp [enrichedComp]

中文:
引理 enrichedComp_π
  条件: (j : J)
  证明: by
  simp [enrichedComp]

Depends on / 依赖: enrichedComp
-/
lemma enrichedComp_π (j : J) :
    enrichedComp V F₁ F₂ F₃ ≫ end_.π _ j =
      (end_.π (diagram V F₁ F₂) j otimesₘ end_.π (diagram V F₂ F₃) j) ≫ eComp V _ _ _ := by
  simp [enrichedComp]

variable {F₁ F₂ F₃}

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `homEquiv_comp` / 引理 `homEquiv_comp`

English:
lemma homEquiv_comp
  given: (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃)
  proof: by
  ext j
  simp only [homEquiv_apply_π, NatTrans.comp_app, eHomEquiv_comp, assoc,
    enrichedComp_π, Functor.op_obj, tensorHom_comp_tensorHom_assoc]

中文:
引理 homEquiv_comp
  条件: (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃)
  证明: by
  ext j
  simp only [homEquiv_apply_π, NatTrans.comp_app, eHomEquiv_comp, assoc,
    enrichedComp_π, Functor.op_obj, tensorHom_comp_tensorHom_assoc]

Depends on / 依赖: Functor, Functor.op_obj, NatTrans, NatTrans.comp_app, comp_app, eHomEquiv_comp, op_obj, tensorHom_comp_tensorHom_assoc
-/
lemma homEquiv_comp (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) :
    (homEquiv V) (f ≫ g) = (fun_ (𝟙_ V)).inv ≫ ((homEquiv V) f otimesₘ (homEquiv V) g) ≫
    enrichedComp V F₁ F₂ F₃ := by
  ext j
  simp only [homEquiv_apply_π, NatTrans.comp_app, eHomEquiv_comp, assoc,
    enrichedComp_π, Functor.op_obj, tensorHom_comp_tensorHom_assoc]

end

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `enriched_id_comp` / 引理 `enriched_id_comp`

English:
lemma enriched_id_comp
  given: [HasEnrichedHom V F₁ F₁] [HasEnrichedHom V F₁ F₂]
  proof: by
  ext j
  rw [assoc]; rw [assoc]; rw [enrichedComp_π]; rw [id_comp]; rw [tensorHom_def]; rw [assoc]; rw [← comp_whiskerRight_assoc]; rw [enrichedId_π]; rw [← whisker_exchange_assoc]; rw [id_whiskerLeft]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]
  dsimp
  rw [e_id_comp]; rw [comp_id]

中文:
引理 enriched_id_comp
  条件: [HasEnrichedHom V F₁ F₁] [HasEnrichedHom V F₁ F₂]
  证明: by
  ext j
  rw [assoc]; rw [assoc]; rw [enrichedComp_π]; rw [id_comp]; rw [tensorHom_def]; rw [assoc]; rw [← comp_whiskerRight_assoc]; rw [enrichedId_π]; rw [← whisker_exchange_assoc]; rw [id_whiskerLeft]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]
  dsimp
  rw [e_id_comp]; rw [comp_id]

Depends on / 依赖: Iso.inv_hom_id_assoc, comp_id, comp_whiskerRight_assoc, e_id_comp, id_comp, id_whiskerLeft, inv_hom_id_assoc, tensorHom_def, whisker_exchange_assoc
-/
lemma enriched_id_comp [HasEnrichedHom V F₁ F₁] [HasEnrichedHom V F₁ F₂] :
    (fun_ (enrichedHom V F₁ F₂)).inv ≫ enrichedId V F₁ ▷ enrichedHom V F₁ F₂ ≫
      enrichedComp V F₁ F₁ F₂ = 𝟙 _ := by
  ext j
  rw [assoc]; rw [assoc]; rw [enrichedComp_π]; rw [id_comp]; rw [tensorHom_def]; rw [assoc]; rw [← comp_whiskerRight_assoc]; rw [enrichedId_π]; rw [← whisker_exchange_assoc]; rw [id_whiskerLeft]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]
  dsimp
  rw [e_id_comp]; rw [comp_id]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `enriched_comp_id` / 引理 `enriched_comp_id`

English:
lemma enriched_comp_id
  given: [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₂ F₂]
  proof: by
  ext j
  rw [assoc]; rw [assoc]; rw [enrichedComp_π]; rw [id_comp]; rw [tensorHom_def']; rw [assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [enrichedId_π]; rw [whisker_exchange_assoc]; rw [MonoidalCategory.whiskerRight_id]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]
  dsimp
  

中文:
引理 enriched_comp_id
  条件: [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₂ F₂]
  证明: by
  ext j
  rw [assoc]; rw [assoc]; rw [enrichedComp_π]; rw [id_comp]; rw [tensorHom_def']; rw [assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [enrichedId_π]; rw [whisker_exchange_assoc]; rw [MonoidalCategory.whiskerRight_id]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]
  dsimp
  

Depends on / 依赖: Iso.inv_hom_id_assoc, MonoidalCategory, MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerRight_id, comp_id, e_comp_id, id_comp, inv_hom_id_assoc, tensorHom_def, whiskerLeft_comp_assoc, whiskerRight_id, whisker_exchange_assoc
-/
lemma enriched_comp_id [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₂ F₂] :
    (ρ_ (enrichedHom V F₁ F₂)).inv ≫ enrichedHom V F₁ F₂ ◁ enrichedId V F₂ ≫
      enrichedComp V F₁ F₂ F₂ = 𝟙 _ := by
  ext j
  rw [assoc]; rw [assoc]; rw [enrichedComp_π]; rw [id_comp]; rw [tensorHom_def']; rw [assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [enrichedId_π]; rw [whisker_exchange_assoc]; rw [MonoidalCategory.whiskerRight_id]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]
  dsimp
  rw [e_comp_id]; rw [comp_id]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `enriched_assoc` / 引理 `enriched_assoc`

English:
lemma enriched_assoc
  statement: [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₃] [HasEnrichedHom V F₁ F₄]
  proof: by
  ext j
  conv_lhs =>
    rw [assoc]; rw [assoc]; rw [enrichedComp_π]; rw [tensorHom_def_assoc]; rw [← comp_whiskerRight_assoc]; rw [enrichedComp_π]; rw [comp_whiskerRight_assoc]; rw [← whisker_exchange_assoc]; rw [← whisker_exchange_assoc]; rw [← tensorHom_def'_assoc]; rw [← associator_inv_natur

中文:
引理 enriched_assoc
  结论: [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₃] [HasEnrichedHom V F₁ F₄]
  证明: by
  ext j
  conv_lhs =>
    rw [assoc]; rw [assoc]; rw [enrichedComp_π]; rw [tensorHom_def_assoc]; rw [← comp_whiskerRight_assoc]; rw [enrichedComp_π]; rw [comp_whiskerRight_assoc]; rw [← whisker_exchange_assoc]; rw [← whisker_exchange_assoc]; rw [← tensorHom_def'_assoc]; rw [← associator_inv_natur

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp_assoc, _assoc, associator_inv_naturality_assoc, comp_whiskerRight_assoc, conv_lhs, conv_rhs, tensorHom_def, tensorHom_def_assoc, whiskerLeft_comp_assoc, whisker_exchange_assoc
-/
lemma enriched_assoc [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₃] [HasEnrichedHom V F₁ F₄]
    [HasEnrichedHom V F₂ F₃] [HasEnrichedHom V F₂ F₄] [HasEnrichedHom V F₃ F₄] :
    (α_ (enrichedHom V F₁ F₂) (enrichedHom V F₂ F₃) (enrichedHom V F₃ F₄)).inv ≫
      enrichedComp V F₁ F₂ F₃ ▷ enrichedHom V F₃ F₄ ≫ enrichedComp V F₁ F₃ F₄ =
      enrichedHom V F₁ F₂ ◁ enrichedComp V F₂ F₃ F₄ ≫ enrichedComp V F₁ F₂ F₄ := by
  ext j
  conv_lhs =>
    rw [assoc]; rw [assoc]; rw [enrichedComp_π]; rw [tensorHom_def_assoc]; rw [← comp_whiskerRight_assoc]; rw [enrichedComp_π]; rw [comp_whiskerRight_assoc]; rw [← whisker_exchange_assoc]; rw [← whisker_exchange_assoc]; rw [← tensorHom_def'_assoc]; rw [← associator_inv_naturality_assoc]
  conv_rhs =>
    rw [assoc]; rw [enrichedComp_π]; rw [tensorHom_def'_assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]; rw [enrichedComp_π]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [whisker_exchange_assoc]; rw [whisker_exchange_assoc]; rw [← tensorHom_def_assoc]
  dsimp
  rw [e_assoc]

variable (J C)

/-- If `C` is a `V`-enriched ordinary category, and `C` has suitable limits,
then `J ⥤ C` is also a `V`-enriched ordinary category. -/
@[instance_reducible]
/--
Definition of `enrichedOrdinaryCategory` / `enrichedOrdinaryCategory` 的定义

English:
definition enrichedOrdinaryCategory
  signature: [forall (F₁ F₂ : J ⥤ C), HasEnrichedHom V F₁ F₂]
  body: enrichedHom V F₁ F₂
  id F := enrichedId V F
  comp F₁ F₂ F₃ := enrichedComp V F₁ F₂ F₃
  assoc _ _ _ _ := enriched_assoc _ _ _ _ _
  homEquiv := homEquiv V
  homEquiv_id _ := homEquiv_id V _
  homEquiv_comp f g := homEquiv_comp V f g

中文:
定义 enrichedOrdinaryCategory
  签名: [对任意 (F₁ F₂ : J ⥤ C), HasEnrichedHom V F₁ F₂]
  定义体: enrichedHom V F₁ F₂
  id F := enrichedId V F
  comp F₁ F₂ F₃ := enrichedComp V F₁ F₂ F₃
  assoc _ _ _ _ := enriched_assoc _ _ _ _ _
  homEquiv := homEquiv V
  homEquiv_id _ := homEquiv_id V _
  homEquiv_comp f g := homEquiv_comp V f g

Depends on / 依赖: enrichedHom
-/
noncomputable def enrichedOrdinaryCategory [forall (F₁ F₂ : J ⥤ C), HasEnrichedHom V F₁ F₂] :
    EnrichedOrdinaryCategory V (J ⥤ C) where
  Hom F₁ F₂ := enrichedHom V F₁ F₂
  id F := enrichedId V F
  comp F₁ F₂ F₃ := enrichedComp V F₁ F₂ F₃
  assoc _ _ _ _ := enriched_assoc _ _ _ _ _
  homEquiv := homEquiv V
  homEquiv_id _ := homEquiv_id V _
  homEquiv_comp f g := homEquiv_comp V f g

variable {J C}

section

variable (G : K ⥤ J) [HasEnrichedHom V F₁ F₂]

variable {F₁ F₂} in
/--
Definition of `precompEnrichedHom'` / `precompEnrichedHom'` 的定义

English:
abbreviation precompEnrichedHom'
  signature: {F₁' F₂' : K ⥤ C}
  body: end_.lift (fun x => enrichedHomπ V F₁ F₂ (G.obj x) ≫
    (eHomWhiskerRight _ (e₁.inv.app x) _ ≫ eHomWhiskerLeft _ _ (e₂.hom.app x)))
    (fun i j f => by
      dsimp
      rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [← eHomWhiskerLeft_comp]; rw [← eHom_whisker_exchange]; rw [← e₂.hom.naturali

中文:
缩写 precompEnrichedHom'
  签名: {F₁' F₂' : K ⥤ C}
  定义体: end_.lift (fun x => enrichedHomπ V F₁ F₂ (G.obj x) ≫
    (eHomWhiskerRight _ (e₁.inv.app x) _ ≫ eHomWhiskerLeft _ _ (e₂.hom.app x)))
    (fun i j f => by
      dsimp
      rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [← eHomWhiskerLeft_comp]; rw [← eHom_whisker_exchange]; rw [← e₂.hom.naturali

Depends on / 依赖: G.obj, NatTrans, eHomWhiskerLeft, eHomWhiskerLeft_comp, eHomWhiskerLeft_comp_assoc, eHomWhiskerRight, eHomWhiskerRight_comp_assoc, eHom_whisker_exchange, end_, end_.lift, enrichedHom_condition_assoc, hom.app, hom.naturality, inv.app, naturality
-/
noncomputable abbrev precompEnrichedHom' {F₁' F₂' : K ⥤ C}
    [HasEnrichedHom V F₁' F₂'] (e₁ : G ⋙ F₁ ≅ F₁') (e₂ : G ⋙ F₂ ≅ F₂') :
    enrichedHom V F₁ F₂ ⟶ enrichedHom V F₁' F₂' :=
  end_.lift (fun x => enrichedHomπ V F₁ F₂ (G.obj x) ≫
    (eHomWhiskerRight _ (e₁.inv.app x) _ ≫ eHomWhiskerLeft _ _ (e₂.hom.app x)))
    (fun i j f => by
      dsimp
      rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [← eHomWhiskerLeft_comp]; rw [← eHom_whisker_exchange]; rw [← e₂.hom.naturality f]; rw [eHomWhiskerLeft_comp_assoc]
      dsimp
      rw [enrichedHom_condition_assoc]; rw [eHom_whisker_exchange]; rw [eHom_whisker_exchange]; rw [← eHomWhiskerRight_comp_assoc]; rw [← eHomWhiskerRight_comp_assoc]; rw [NatTrans.naturality]
      dsimp)

/--
Definition of `precompEnrichedHom` / `precompEnrichedHom` 的定义

English:
abbreviation precompEnrichedHom
  body: precompEnrichedHom' V G (Iso.refl _) (Iso.refl _)

中文:
缩写 precompEnrichedHom
  定义体: precompEnrichedHom' V G (Iso.refl _) (Iso.refl _)

Depends on / 依赖: Iso.refl, precompEnrichedHom
-/
noncomputable abbrev precompEnrichedHom
    [HasEnrichedHom V (G ⋙ F₁) (G ⋙ F₂)] :
    enrichedHom V F₁ F₂ ⟶ enrichedHom V (G ⋙ F₁) (G ⋙ F₂) :=
  precompEnrichedHom' V G (Iso.refl _) (Iso.refl _)

end


section

/--
Definition of `HasFunctorEnrichedHom` / `HasFunctorEnrichedHom` 的定义

English:
abbreviation HasFunctorEnrichedHom
  body: forall (j : J), HasEnrichedHom V (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂)

中文:
缩写 HasFunctorEnrichedHom
  定义体: forall (j : J), HasEnrichedHom V (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂)

Depends on / 依赖: HasEnrichedHom, Under.forget, forget
-/
abbrev HasFunctorEnrichedHom :=
  forall (j : J), HasEnrichedHom V (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂)

variable [HasFunctorEnrichedHom V F₁ F₂]

instance {j j' : J} (f : j ⟶ j') :
    HasEnrichedHom V (Under.map f ⋙ Under.forget j ⋙ F₁)
      (Under.map f ⋙ Under.forget j ⋙ F₂) :=
  inferInstanceAs (HasEnrichedHom V (Under.forget j' ⋙ F₁) (Under.forget j' ⋙ F₂))

set_option backward.isDefEq.respectTransparency false in
/-- Given functors `F₁` and `F₂` in `J ⥤ C`, where `C` is a category enriched in `V`,
this is the enriched hom functor from `F₁` to `F₂` in `J ⥤ V`. -/
@[simps!]
/--
Definition of `functorEnrichedHom` / `functorEnrichedHom` 的定义

English:
definition functorEnrichedHom
  signature: : J ⥤ V where
  body: enrichedHom V (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂)
  map f := precompEnrichedHom' V (Under.map f) (Iso.refl _) (Iso.refl _)
  map_id X := by
    ext j
    -- this was produced by `simp?`
    simp only [diagram_obj_obj, Functor.comp_obj, Under.forget_obj, end_.lift_π,
      Under.map_obj_right

中文:
定义 functorEnrichedHom
  签名: : J ⥤ V where
  定义体: enrichedHom V (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂)
  map f := precompEnrichedHom' V (Under.map f) (Iso.refl _) (Iso.refl _)
  map_id X := by
    ext j
    -- this was produced by `simp?`
    simp only [diagram_obj_obj, Functor.comp_obj, Under.forget_obj, end_.lift_π,
      Under.map_obj_right

Depends on / 依赖: F.isColimitOfIsWellOrderContinuous, Under.forget, enrichedHom, forget, isColimitOfIsWellOrderContinuous, isColimitOfPreserves, preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape
-/
noncomputable def functorEnrichedHom : J ⥤ V where
  obj j := enrichedHom V (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂)
  map f := precompEnrichedHom' V (Under.map f) (Iso.refl _) (Iso.refl _)
  map_id X := by
    ext j
    -- this was produced by `simp?`
    simp only [diagram_obj_obj, Functor.comp_obj, Under.forget_obj, end_.lift_π,
      Under.map_obj_right, Iso.refl_inv, NatTrans.id_app, eHomWhiskerRight_id, Iso.refl_hom,
      eHomWhiskerLeft_id, comp_id, id_comp]
    congr 1
    simp [Under.map, Comma.mapLeft]
    rfl
  map_comp f g := by
    ext j
    -- this was produced by `simp?`
    simp only [diagram_obj_obj, Functor.comp_obj, Under.forget_obj, end_.lift_π,
      Under.map_obj_right, Iso.refl_inv, NatTrans.id_app, eHomWhiskerRight_id, Iso.refl_hom,
      eHomWhiskerLeft_id, comp_id, assoc]
    congr 1
    simp [Under.map, Comma.mapLeft]

variable [HasEnrichedHom V F₁ F₂]

set_option backward.isDefEq.respectTransparency false in
/-- The (limit) cone expressing that the limit of `functorEnrichedHom V F₁ F₂`
is `enrichedHom V F₁ F₂`. -/
@[simps]
/--
Definition of `coneFunctorEnrichedHom` / `coneFunctorEnrichedHom` 的定义

English:
definition coneFunctorEnrichedHom
  signature: : Cone (functorEnrichedHom V F₁ F₂) where
  body: enrichedHom V F₁ F₂
  π := { app := fun j => precompEnrichedHom V F₁ F₂ (Under.forget j) }

中文:
定义 coneFunctorEnrichedHom
  签名: : 锥 (functorEnrichedHom V F₁ F₂) where
  定义体: enrichedHom V F₁ F₂
  π := { app := fun j => precompEnrichedHom V F₁ F₂ (Under.forget j) }

Depends on / 依赖: enrichedHom, infer_instance, preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape
-/
noncomputable def coneFunctorEnrichedHom : Cone (functorEnrichedHom V F₁ F₂) where
  pt := enrichedHom V F₁ F₂
  π := { app := fun j => precompEnrichedHom V F₁ F₂ (Under.forget j) }

namespace isLimitConeFunctorEnrichedHom

variable {V F₁ F₂} (s : Cone (functorEnrichedHom V F₁ F₂))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : s.pt ⟶ enrichedHom V F₁ F₂
  body: end_.lift (fun j => s.π.app j ≫ enrichedHomπ V _ _ (Under.mk (𝟙 j))) (fun j j' f => by
    dsimp
    rw [← s.w f]; rw [assoc]; rw [assoc]; rw [assoc]
    -- this was produced by `simp?`
    simp only [functorEnrichedHom_obj, functorEnrichedHom_map, end_.lift_π_assoc, diagram_obj_obj,
      Functor.c

中文:
定义 lift
  签名: : s.pt ⟶ enrichedHom V F₁ F₂
  定义体: end_.lift (fun j => s.π.app j ≫ enrichedHomπ V _ _ (Under.mk (𝟙 j))) (fun j j' f => by
    dsimp
    rw [← s.w f]; rw [assoc]; rw [assoc]; rw [assoc]
    -- this was produced by `simp?`
    simp only [functorEnrichedHom_obj, functorEnrichedHom_map, end_.lift_π_assoc, diagram_obj_obj,
      Functor.c

Depends on / 依赖: Under.mk, end_, end_.lift
-/
noncomputable def lift : s.pt ⟶ enrichedHom V F₁ F₂ :=
  end_.lift (fun j => s.π.app j ≫ enrichedHomπ V _ _ (Under.mk (𝟙 j))) (fun j j' f => by
    dsimp
    rw [← s.w f]; rw [assoc]; rw [assoc]; rw [assoc]
    -- this was produced by `simp?`
    simp only [functorEnrichedHom_obj, functorEnrichedHom_map, end_.lift_π_assoc, diagram_obj_obj,
      Functor.comp_obj, Under.forget_obj, Under.mk_right, Under.map_obj_right, Iso.refl_inv,
      NatTrans.id_app, eHomWhiskerRight_id, Iso.refl_hom, eHomWhiskerLeft_id, comp_id]
    have := enrichedHom_condition V (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂)
      (Under.homMk f : Under.mk (𝟙 j) ⟶ Under.mk f)
    dsimp at this
    rw [this]
    congr 3
    simp [Under.map, Comma.mapLeft]
    rfl)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `fac` / 引理 `fac`

English:
lemma fac
  given: (j : J)
  statement: lift s ≫ (coneFunctorEnrichedHom V F₁ F₂).π.app j = s.π.app j
  proof: by
  dsimp [coneFunctorEnrichedHom]
  ext k
  have := s.w k.hom
  dsimp at this
  -- this was produced by `simp? [lift, ← this]`
  simp only [diagram_obj_obj, Functor.comp_obj, Under.forget_obj, lift, functorEnrichedHom_obj,
    assoc, end_.lift_π, Iso.refl_inv, NatTrans.id_app, eHomWhiskerRight_id,

中文:
引理 fac
  条件: (j : J)
  结论: lift s ≫ (coneFunctorEnrichedHom V F₁ F₂).π.app j = s.π.app j
  证明: by
  dsimp [coneFunctorEnrichedHom]
  ext k
  have := s.w k.hom
  dsimp at this
  -- this was produced by `simp? [lift, ← this]`
  simp only [diagram_obj_obj, Functor.comp_obj, Under.forget_obj, lift, functorEnrichedHom_obj,
    assoc, end_.lift_π, Iso.refl_inv, NatTrans.id_app, eHomWhiskerRight_id,

Depends on / 依赖: coneFunctorEnrichedHom, k.hom
-/
lemma fac (j : J) : lift s ≫ (coneFunctorEnrichedHom V F₁ F₂).π.app j = s.π.app j := by
  dsimp [coneFunctorEnrichedHom]
  ext k
  have := s.w k.hom
  dsimp at this
  -- this was produced by `simp? [lift, ← this]`
  simp only [diagram_obj_obj, Functor.comp_obj, Under.forget_obj, lift, functorEnrichedHom_obj,
    assoc, end_.lift_π, Iso.refl_inv, NatTrans.id_app, eHomWhiskerRight_id, Iso.refl_hom,
    eHomWhiskerLeft_id, comp_id, ← this, Under.map_obj_right, Under.mk_right]
  congr
  simp [Under.map, Comma.mapLeft]
  rfl

end isLimitConeFunctorEnrichedHom

set_option backward.isDefEq.respectTransparency false in
open isLimitConeFunctorEnrichedHom in
/--
Definition of `isLimitConeFunctorEnrichedHom` / `isLimitConeFunctorEnrichedHom` 的定义

English:
definition isLimitConeFunctorEnrichedHom
  signature: :
  body: lift
  fac := fac
  uniq s m hm := by
    dsimp
    ext j
    simpa using ((hm j).trans (fac s j).symm) =≫ enrichedHomπ V _ _ (Under.mk (𝟙 j))

中文:
定义 isLimitConeFunctorEnrichedHom
  签名: :
  定义体: lift
  fac := fac
  uniq s m hm := by
    dsimp
    ext j
    simpa using ((hm j).trans (fac s j).symm) =≫ enrichedHomπ V _ _ (Under.mk (𝟙 j))
-/
noncomputable def isLimitConeFunctorEnrichedHom :
    IsLimit (coneFunctorEnrichedHom V F₁ F₂) where
  lift := lift
  fac := fac
  uniq s m hm := by
    dsimp
    ext j
    simpa using ((hm j).trans (fac s j).symm) =≫ enrichedHomπ V _ _ (Under.mk (𝟙 j))

end

set_option backward.isDefEq.respectTransparency false in
/-- The identity for the `J ⥤ V`-enrichment of the category `J ⥤ C`. -/
@[simps]
/--
Definition of `functorEnrichedId` / `functorEnrichedId` 的定义

English:
definition functorEnrichedId
  signature: [HasFunctorEnrichedHom V F₁ F₁]
  body: enrichedId V _

中文:
定义 functorEnrichedId
  签名: [HasFunctorEnrichedHom V F₁ F₁]
  定义体: enrichedId V _

Depends on / 依赖: enrichedId
-/
noncomputable def functorEnrichedId [HasFunctorEnrichedHom V F₁ F₁] :
    𝟙_ (J ⥤ V) ⟶ functorEnrichedHom V F₁ F₁ where
  app j := enrichedId V _

set_option backward.isDefEq.respectTransparency false in
/-- The composition for the `J ⥤ V`-enrichment of the category `J ⥤ C`. -/
@[simps]
/--
Definition of `functorEnrichedComp` / `functorEnrichedComp` 的定义

English:
definition functorEnrichedComp
  signature: [HasFunctorEnrichedHom V F₁ F₂]
  body: enrichedComp V _ _ _
  naturality j j' f := by
    dsimp
    ext k
    dsimp
    rw [assoc]; rw [assoc]; rw [enrichedComp_π]
    dsimp
    rw [tensorHom_comp_tensorHom_assoc]
    simp

@[reassoc (attr := simp)]

中文:
定义 functorEnrichedComp
  签名: [HasFunctorEnrichedHom V F₁ F₂]
  定义体: enrichedComp V _ _ _
  naturality j j' f := by
    dsimp
    ext k
    dsimp
    rw [assoc]; rw [assoc]; rw [enrichedComp_π]
    dsimp
    rw [tensorHom_comp_tensorHom_assoc]
    simp

@[reassoc (attr := simp)]

Depends on / 依赖: enrichedComp
-/
noncomputable def functorEnrichedComp [HasFunctorEnrichedHom V F₁ F₂]
    [HasFunctorEnrichedHom V F₂ F₃] [HasFunctorEnrichedHom V F₁ F₃] :
    functorEnrichedHom V F₁ F₂ otimes functorEnrichedHom V F₂ F₃ ⟶ functorEnrichedHom V F₁ F₃ where
  app j := enrichedComp V _ _ _
  naturality j j' f := by
    dsimp
    ext k
    dsimp
    rw [assoc]; rw [assoc]; rw [enrichedComp_π]
    dsimp
    rw [tensorHom_comp_tensorHom_assoc]
    simp

@[reassoc (attr := simp)]
/--
lemma `functorEnriched_id_comp` / 引理 `functorEnriched_id_comp`

English:
lemma functorEnriched_id_comp
  given: [HasFunctorEnrichedHom V F₁ F₂] [HasFunctorEnrichedHom V F₁ F₁]
  proof: by cat_disch

@[reassoc (attr := simp)]

中文:
引理 functorEnriched_id_comp
  条件: [HasFunctorEnrichedHom V F₁ F₂] [HasFunctorEnrichedHom V F₁ F₁]
  证明: by cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: cat_disch
-/
lemma functorEnriched_id_comp [HasFunctorEnrichedHom V F₁ F₂] [HasFunctorEnrichedHom V F₁ F₁] :
    (fun_ (functorEnrichedHom V F₁ F₂)).inv ≫
      functorEnrichedId V F₁ ▷ functorEnrichedHom V F₁ F₂ ≫
        functorEnrichedComp V F₁ F₁ F₂ = 𝟙 (functorEnrichedHom V F₁ F₂) := by cat_disch

@[reassoc (attr := simp)]
/--
lemma `functorEnriched_comp_id` / 引理 `functorEnriched_comp_id`

English:
lemma functorEnriched_comp_id
  given: [HasFunctorEnrichedHom V F₁ F₂] [HasFunctorEnrichedHom V F₂ F₂]
  proof: by cat_disch

@[reassoc]

中文:
引理 functorEnriched_comp_id
  条件: [HasFunctorEnrichedHom V F₁ F₂] [HasFunctorEnrichedHom V F₂ F₂]
  证明: by cat_disch

@[reassoc]

Depends on / 依赖: cat_disch
-/
lemma functorEnriched_comp_id [HasFunctorEnrichedHom V F₁ F₂] [HasFunctorEnrichedHom V F₂ F₂] :
    (ρ_ (functorEnrichedHom V F₁ F₂)).inv ≫
      functorEnrichedHom V F₁ F₂ ◁ functorEnrichedId V F₂ ≫
        functorEnrichedComp V F₁ F₂ F₂ = 𝟙 (functorEnrichedHom V F₁ F₂) := by cat_disch

@[reassoc]
/--
lemma `functorEnriched_assoc` / 引理 `functorEnriched_assoc`

English:
lemma functorEnriched_assoc
  statement: [HasFunctorEnrichedHom V F₁ F₂] [HasFunctorEnrichedHom V F₂ F₃]
  proof: by
  ext j
  dsimp
  rw [enriched_assoc]

中文:
引理 functorEnriched_assoc
  结论: [HasFunctorEnrichedHom V F₁ F₂] [HasFunctorEnrichedHom V F₂ F₃]
  证明: by
  ext j
  dsimp
  rw [enriched_assoc]

Depends on / 依赖: enriched_assoc
-/
lemma functorEnriched_assoc [HasFunctorEnrichedHom V F₁ F₂] [HasFunctorEnrichedHom V F₂ F₃]
    [HasFunctorEnrichedHom V F₃ F₄] [HasFunctorEnrichedHom V F₁ F₃]
    [HasFunctorEnrichedHom V F₂ F₄] [HasFunctorEnrichedHom V F₁ F₄] :
    (α_ _ _ _).inv ≫ functorEnrichedComp V F₁ F₂ F₃ ▷ functorEnrichedHom V F₃ F₄ ≫
      functorEnrichedComp V F₁ F₃ F₄ =
        functorEnrichedHom V F₁ F₂ ◁ functorEnrichedComp V F₂ F₃ F₄ ≫
          functorEnrichedComp V F₁ F₂ F₄ := by
  ext j
  dsimp
  rw [enriched_assoc]

variable (J C) in
/-- If `C` is a `V`-enriched ordinary category, and `C` has suitable limits,
then `J ⥤ C` is also a `J ⥤ V`-enriched ordinary category. -/
@[instance_reducible]
/--
Definition of `functorEnrichedCategory` / `functorEnrichedCategory` 的定义

English:
definition functorEnrichedCategory
  body: functorEnrichedHom V F₁ F₂
  id F := functorEnrichedId V F
  comp F₁ F₂ F₃ := functorEnrichedComp V F₁ F₂ F₃
  assoc F₁ F₂ F₃ F₄ := functorEnriched_assoc V F₁ F₂ F₃ F₄

中文:
定义 functorEnrichedCategory
  定义体: functorEnrichedHom V F₁ F₂
  id F := functorEnrichedId V F
  comp F₁ F₂ F₃ := functorEnrichedComp V F₁ F₂ F₃
  assoc F₁ F₂ F₃ F₄ := functorEnriched_assoc V F₁ F₂ F₃ F₄

Depends on / 依赖: functorEnrichedHom
-/
noncomputable def functorEnrichedCategory
    [forall (F₁ F₂ : J ⥤ C), HasFunctorEnrichedHom V F₁ F₂] :
    EnrichedCategory (J ⥤ V) (J ⥤ C) where
  Hom F₁ F₂ := functorEnrichedHom V F₁ F₂
  id F := functorEnrichedId V F
  comp F₁ F₂ F₃ := functorEnrichedComp V F₁ F₂ F₃
  assoc F₁ F₂ F₃ F₄ := functorEnriched_assoc V F₁ F₂ F₃ F₄

variable {F₁ F₂} in
/-- Given functors `F₁` and `F₂` in `J ⥤ C`, where `C` is a `V`-enriched ordinary category,
this is the bijection `(F₁ ⟶ F₂) ≃ (𝟙_ (J ⥤ V) ⟶ functorEnrichedHom V F₁ F₂)`. -/
@[simps! apply_app]
/--
Definition of `functorHomEquiv` / `functorHomEquiv` 的定义

English:
definition functorHomEquiv
  signature: [HasFunctorEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₂]
  body: (homEquiv V).trans (isLimitConeFunctorEnrichedHom V F₁ F₂).homEquiv

中文:
定义 functorHomEquiv
  签名: [HasFunctorEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₂]
  定义体: (homEquiv V).trans (isLimitConeFunctorEnrichedHom V F₁ F₂).homEquiv

Depends on / 依赖: homEquiv, isLimitConeFunctorEnrichedHom
-/
noncomputable def functorHomEquiv [HasFunctorEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₂] :
    (F₁ ⟶ F₂) ≃ (𝟙_ (J ⥤ V) ⟶ functorEnrichedHom V F₁ F₂) :=
  (homEquiv V).trans (isLimitConeFunctorEnrichedHom V F₁ F₂).homEquiv

set_option backward.isDefEq.respectTransparency false in
/--
lemma `functorHomEquiv_id` / 引理 `functorHomEquiv_id`

English:
lemma functorHomEquiv_id
  given: [HasFunctorEnrichedHom V F₁ F₁] [HasEnrichedHom V F₁ F₁]
  proof: by cat_disch

中文:
引理 functorHomEquiv_id
  条件: [HasFunctorEnrichedHom V F₁ F₁] [HasEnrichedHom V F₁ F₁]
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma functorHomEquiv_id [HasFunctorEnrichedHom V F₁ F₁] [HasEnrichedHom V F₁ F₁] :
    (functorHomEquiv V) (𝟙 F₁) = functorEnrichedId V F₁ := by cat_disch

set_option backward.isDefEq.respectTransparency false in
variable {F₁ F₂ F₃} in
/--
lemma `functorHomEquiv_comp` / 引理 `functorHomEquiv_comp`

English:
lemma functorHomEquiv_comp
  statement: [HasFunctorEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₂]
  proof: by
  ext j
  dsimp
  ext k
  rw [homEquiv_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [end_.lift_π]; rw [enrichedComp_π]
  simp [tensorHom_comp_tensorHom_assoc]

中文:
引理 functorHomEquiv_comp
  结论: [HasFunctorEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₂]
  证明: by
  ext j
  dsimp
  ext k
  rw [homEquiv_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [end_.lift_π]; rw [enrichedComp_π]
  simp [tensorHom_comp_tensorHom_assoc]

Depends on / 依赖: end_, end_.lift_, homEquiv_comp, tensorHom_comp_tensorHom_assoc
-/
lemma functorHomEquiv_comp [HasFunctorEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₂]
    [HasFunctorEnrichedHom V F₂ F₃] [HasEnrichedHom V F₂ F₃]
    [HasFunctorEnrichedHom V F₁ F₃] [HasEnrichedHom V F₁ F₃]
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) :
    (functorHomEquiv V) (f ≫ g) = (fun_ (𝟙_ (J ⥤ V))).inv ≫
      ((functorHomEquiv V) f otimesₘ (functorHomEquiv V) g) ≫ functorEnrichedComp V F₁ F₂ F₃ := by
  ext j
  dsimp
  ext k
  rw [homEquiv_comp]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [end_.lift_π]; rw [enrichedComp_π]
  simp [tensorHom_comp_tensorHom_assoc]

attribute [local instance] functorEnrichedCategory

variable (J C) in
/-- If `C` is a `V`-enriched ordinary category, and `C` has suitable limits,
then `J ⥤ C` is also a `J ⥤ V`-enriched ordinary category. -/
@[instance_reducible]
/--
Definition of `functorEnrichedOrdinaryCategory` / `functorEnrichedOrdinaryCategory` 的定义

English:
definition functorEnrichedOrdinaryCategory
  body: functorHomEquiv V
  homEquiv_id F := functorHomEquiv_id V F
  homEquiv_comp f g := functorHomEquiv_comp V f g

中文:
定义 functorEnrichedOrdinaryCategory
  定义体: functorHomEquiv V
  homEquiv_id F := functorHomEquiv_id V F
  homEquiv_comp f g := functorHomEquiv_comp V f g

Depends on / 依赖: Groupoid, Groupoid.invEquivalence, Groupoid.ofIsGroupoid, functorHomEquiv, invEquivalence, ofIsGroupoid, preservesLimitsOfShape_of_equiv
-/
noncomputable def functorEnrichedOrdinaryCategory
    [forall (F₁ F₂ : J ⥤ C), HasFunctorEnrichedHom V F₁ F₂]
    [forall (F₁ F₂ : J ⥤ C), HasEnrichedHom V F₁ F₂] :
    EnrichedOrdinaryCategory (J ⥤ V) (J ⥤ C) where
  homEquiv := functorHomEquiv V
  homEquiv_id F := functorHomEquiv_id V F
  homEquiv_comp f g := functorHomEquiv_comp V f g

end CategoryTheory.Enriched.FunctorCategory
