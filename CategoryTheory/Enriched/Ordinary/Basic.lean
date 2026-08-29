/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Monoidal.Types.Coyoneda

/-!
# Enriched ordinary categories

If `V` is a monoidal category, a `V`-enriched category `C` does not need
to be a category. However, when we have both `Category C` and `EnrichedCategory V C`,
we may require that the type of morphisms `X ⟶ Y` in `C` identify to
`𝟙_ V ⟶ EnrichedCategory.Hom X Y`. This data shall be packaged in the
typeclass `EnrichedOrdinaryCategory V C`.

In particular, if `C` is a `V`-enriched category, it is shown that
the "underlying" category `ForgetEnrichment V C` is equipped with a
`EnrichedOrdinaryCategory V C` instance.

Simplicial categories are implemented in `AlgebraicTopology.SimplicialCategory.Basic`
using an abbreviation for `EnrichedOrdinaryCategory SSet C`.

-/

@[expose] public section

universe v' v v'' u u' u''

open CategoryTheory Category MonoidalCategory Opposite

namespace CategoryTheory

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  (C : Type u) [Category.{v} C]

/--
Definition of `EnrichedOrdinaryCategory` / `EnrichedOrdinaryCategory` 的定义

English:
class EnrichedOrdinaryCategory
  parameters: extends EnrichedCategory V C
  extends: EnrichedCategory V C
  axioms and operations (3):
    - homEquiv({X Y : C}) : (X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y))
    - homEquiv_id((X : C)) : homEquiv (𝟙 X) = eId V X  [default: by cat_disch]
    - homEquiv_comp({X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)) : homEquiv (f ≫ g) = (fun_ _).inv ≫ (homEquiv f otimesₘ homEquiv g) ≫ eComp V X Y Z  [default: by cat_disch]

中文:
类 EnrichedOrdinary范畴
  参数: extends Enriched范畴 V C
  继承: Enriched范畴 V C
  公理与运算 (3 个):
    - homEquiv({X Y : C}) : (X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y))
    - homEquiv_id((X : C)) : homEquiv (𝟙 X) = eId V X  [默认: by cat_disch]
    - homEquiv_comp({X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)) : homEquiv (f ≫ g) = (fun_ _).inv ≫ (homEquiv f otimesₘ homEquiv g) ≫ eComp V X Y Z  [默认: by cat_disch]

Depends on / 依赖: cat_disch, fun_, homEquiv, homEquiv_comp
-/
class EnrichedOrdinaryCategory extends EnrichedCategory V C where
  /-- morphisms `X ⟶ Y` in the category identify morphisms `𝟙_ V ⟶ (X ⟶[V] Y)` in `V` -/
  homEquiv {X Y : C} : (X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y))
  homEquiv_id (X : C) : homEquiv (𝟙 X) = eId V X := by cat_disch
  homEquiv_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homEquiv (f ≫ g) = (fun_ _).inv ≫ (homEquiv f otimesₘ homEquiv g) ≫
      eComp V X Y Z := by cat_disch

variable [EnrichedOrdinaryCategory V C] {C}

/--
Definition of `eHomEquiv` / `eHomEquiv` 的定义

English:
definition eHomEquiv
  signature: {X Y : C}
  body: EnrichedOrdinaryCategory.homEquiv

@[simp]

中文:
定义 eHomEquiv
  签名: {X Y : C}
  定义体: EnrichedOrdinaryCategory.homEquiv

@[simp]

Depends on / 依赖: EnrichedOrdinaryCategory, EnrichedOrdinaryCategory.homEquiv, homEquiv
-/
def eHomEquiv {X Y : C} : (X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y)) :=
  EnrichedOrdinaryCategory.homEquiv

@[simp]
/--
lemma `eHomEquiv_id` / 引理 `eHomEquiv_id`

English:
lemma eHomEquiv_id
  given: (X : C)
  statement: eHomEquiv V (𝟙 X) = eId V X
  proof: EnrichedOrdinaryCategory.homEquiv_id _

@[reassoc]

中文:
引理 eHomEquiv_id
  条件: (X : C)
  结论: eHomEquiv V (𝟙 X) = eId V X
  证明: EnrichedOrdinaryCategory.homEquiv_id _

@[reassoc]

Depends on / 依赖: EnrichedOrdinaryCategory, EnrichedOrdinaryCategory.homEquiv_id, homEquiv_id
-/
lemma eHomEquiv_id (X : C) : eHomEquiv V (𝟙 X) = eId V X :=
  EnrichedOrdinaryCategory.homEquiv_id _

@[reassoc]
/--
lemma `eHomEquiv_comp` / 引理 `eHomEquiv_comp`

English:
lemma eHomEquiv_comp
  given: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: EnrichedOrdinaryCategory.homEquiv_comp _ _

中文:
引理 eHomEquiv_comp
  条件: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: EnrichedOrdinaryCategory.homEquiv_comp _ _

Depends on / 依赖: EnrichedOrdinaryCategory, EnrichedOrdinaryCategory.homEquiv_comp, homEquiv_comp
-/
lemma eHomEquiv_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V (f ≫ g) = (fun_ _).inv ≫ (eHomEquiv V f otimesₘ eHomEquiv V g) ≫ eComp V X Y Z :=
  EnrichedOrdinaryCategory.homEquiv_comp _ _

/--
Definition of `eHomWhiskerRight` / `eHomWhiskerRight` 的定义

English:
definition eHomWhiskerRight
  signature: {X X' : C} (f : X ⟶ X') (Y : C)
  body: (fun_ _).inv ≫ eHomEquiv V f ▷ _ ≫ eComp V X X' Y

@[simp]

中文:
定义 eHomWhiskerRight
  签名: {X X' : C} (f : X ⟶ X') (Y : C)
  定义体: (fun_ _).inv ≫ eHomEquiv V f ▷ _ ≫ eComp V X X' Y

@[simp]

Depends on / 依赖: eHomEquiv, fun_
-/
def eHomWhiskerRight {X X' : C} (f : X ⟶ X') (Y : C) :
    (X' ⟶[V] Y) ⟶ (X ⟶[V] Y) :=
  (fun_ _).inv ≫ eHomEquiv V f ▷ _ ≫ eComp V X X' Y

@[simp]
/--
lemma `eHomWhiskerRight_id` / 引理 `eHomWhiskerRight_id`

English:
lemma eHomWhiskerRight_id
  given: (X Y : C)
  statement: eHomWhiskerRight V (𝟙 X) Y = 𝟙 _
  proof: by
  simp [eHomWhiskerRight]

@[simp, reassoc]

中文:
引理 eHomWhiskerRight_id
  条件: (X Y : C)
  结论: eHomWhiskerRight V (𝟙 X) Y = 𝟙 _
  证明: by
  simp [eHomWhiskerRight]

@[simp, reassoc]

Depends on / 依赖: eHomWhiskerRight
-/
lemma eHomWhiskerRight_id (X Y : C) : eHomWhiskerRight V (𝟙 X) Y = 𝟙 _ := by
  simp [eHomWhiskerRight]

@[simp, reassoc]
/--
lemma `eHomWhiskerRight_comp` / 引理 `eHomWhiskerRight_comp`

English:
lemma eHomWhiskerRight_comp
  given: {X X' X'' : C} (f : X ⟶ X') (f' : X' ⟶ X'') (Y : C)
  proof: by
  dsimp [eHomWhiskerRight]
  rw [assoc]; rw [assoc]; rw [eHomEquiv_comp]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [← e_assoc']; rw [tensorHom_def']; rw [comp_whiskerRight_assoc]; rw [id_whiskerLeft]; rw [comp_whiskerRight_assoc]; rw [← comp_whiskerRight_assoc]; rw [Iso.inv_hom_id]; rw [id_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [leftUnitor_inv_whiskerRight_assoc]; rw [← associator_inv_naturality_left_assoc]; rw [Iso.inv_hom_id_assoc]; rw [← whisker_exchange_assoc]; rw [id_whiskerLeft_assoc]; rw [Iso.inv_hom_id_assoc]

中文:
引理 eHomWhiskerRight_comp
  条件: {X X' X'' : C} (f : X ⟶ X') (f' : X' ⟶ X'') (Y : C)
  证明: by
  dsimp [eHomWhiskerRight]
  rw [assoc]; rw [assoc]; rw [eHomEquiv_comp]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [← e_assoc']; rw [tensorHom_def']; rw [comp_whiskerRight_assoc]; rw [id_whiskerLeft]; rw [comp_whiskerRight_assoc]; rw [← comp_whiskerRight_assoc]; rw [Iso.inv_hom_id]; rw [id_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [leftUnitor_inv_whiskerRight_assoc]; rw [← associator_inv_naturality_left_assoc]; rw [Iso.inv_hom_id_assoc]; rw [← whisker_exchange_assoc]; rw [id_whiskerLeft_assoc]; rw [Iso.inv_hom_id_assoc]

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, associator_inv_naturality_left_assoc, comp_whiskerRight_assoc, eHomEquiv_comp, eHomWhiskerRight, e_assoc, id_whiskerLeft, id_whiskerRight_assoc, inv_hom_id, inv_hom_id_assoc, leftUnitor_inv_whiskerRight_assoc, tensorHom_def, whisker_exchange_as
-/
lemma eHomWhiskerRight_comp {X X' X'' : C} (f : X ⟶ X') (f' : X' ⟶ X'') (Y : C) :
    eHomWhiskerRight V (f ≫ f') Y = eHomWhiskerRight V f' Y ≫ eHomWhiskerRight V f Y := by
  dsimp [eHomWhiskerRight]
  rw [assoc]; rw [assoc]; rw [eHomEquiv_comp]; rw [comp_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [← e_assoc']; rw [tensorHom_def']; rw [comp_whiskerRight_assoc]; rw [id_whiskerLeft]; rw [comp_whiskerRight_assoc]; rw [← comp_whiskerRight_assoc]; rw [Iso.inv_hom_id]; rw [id_whiskerRight_assoc]; rw [comp_whiskerRight_assoc]; rw [leftUnitor_inv_whiskerRight_assoc]; rw [← associator_inv_naturality_left_assoc]; rw [Iso.inv_hom_id_assoc]; rw [← whisker_exchange_assoc]; rw [id_whiskerLeft_assoc]; rw [Iso.inv_hom_id_assoc]

/-- Whiskering commutes with the enriched composition. -/
@[reassoc]
/--
lemma `eComp_eHomWhiskerRight` / 引理 `eComp_eHomWhiskerRight`

English:
lemma eComp_eHomWhiskerRight
  given: {X X' : C} (f : X ⟶ X') (Y Z : C)
  proof: by
  dsimp [eHomWhiskerRight]
  rw [leftUnitor_inv_naturality_assoc]; rw [whisker_exchange_assoc]
  simp [e_assoc']

中文:
引理 eComp_eHomWhiskerRight
  条件: {X X' : C} (f : X ⟶ X') (Y Z : C)
  证明: by
  dsimp [eHomWhiskerRight]
  rw [leftUnitor_inv_naturality_assoc]; rw [whisker_exchange_assoc]
  simp [e_assoc']

Depends on / 依赖: eHomWhiskerRight, e_assoc, leftUnitor_inv_naturality_assoc, whisker_exchange_assoc
-/
lemma eComp_eHomWhiskerRight {X X' : C} (f : X ⟶ X') (Y Z : C) :
    eComp V X' Y Z ≫ eHomWhiskerRight V f Z =
      eHomWhiskerRight V f Y ▷ _ ≫ eComp V X Y Z := by
  dsimp [eHomWhiskerRight]
  rw [leftUnitor_inv_naturality_assoc]; rw [whisker_exchange_assoc]
  simp [e_assoc']

/--
Definition of `eHomWhiskerLeft` / `eHomWhiskerLeft` 的定义

English:
definition eHomWhiskerLeft
  signature: (X : C) {Y Y' : C} (g : Y ⟶ Y')
  body: (ρ_ _).inv ≫ _ ◁ eHomEquiv V g ≫ eComp V X Y Y'

@[simp]

中文:
定义 eHomWhiskerLeft
  签名: (X : C) {Y Y' : C} (g : Y ⟶ Y')
  定义体: (ρ_ _).inv ≫ _ ◁ eHomEquiv V g ≫ eComp V X Y Y'

@[simp]

Depends on / 依赖: eHomEquiv
-/
def eHomWhiskerLeft (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    (X ⟶[V] Y) ⟶ (X ⟶[V] Y') :=
  (ρ_ _).inv ≫ _ ◁ eHomEquiv V g ≫ eComp V X Y Y'

@[simp]
/--
lemma `eHomWhiskerLeft_id` / 引理 `eHomWhiskerLeft_id`

English:
lemma eHomWhiskerLeft_id
  given: (X Y : C)
  statement: eHomWhiskerLeft V X (𝟙 Y) = 𝟙 _
  proof: by
  simp [eHomWhiskerLeft]

@[simp, reassoc]

中文:
引理 eHomWhiskerLeft_id
  条件: (X Y : C)
  结论: eHomWhiskerLeft V X (𝟙 Y) = 𝟙 _
  证明: by
  simp [eHomWhiskerLeft]

@[simp, reassoc]

Depends on / 依赖: eHomWhiskerLeft
-/
lemma eHomWhiskerLeft_id (X Y : C) : eHomWhiskerLeft V X (𝟙 Y) = 𝟙 _ := by
  simp [eHomWhiskerLeft]

@[simp, reassoc]
/--
lemma `eHomWhiskerLeft_comp` / 引理 `eHomWhiskerLeft_comp`

English:
lemma eHomWhiskerLeft_comp
  given: (X : C) {Y Y' Y'' : C} (g : Y ⟶ Y') (g' : Y' ⟶ Y'')
  proof: by
  dsimp [eHomWhiskerLeft]
  rw [assoc]; rw [assoc]; rw [eHomEquiv_comp]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [← e_assoc]; rw [tensorHom_def]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [whiskerLeft_rightUnitor_assoc]; rw [whiskerLeft_rightUnitor_inv_assoc]; rw [triangle_assoc_comp_left_inv_assoc]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [Iso.hom_inv_id_assoc]; rw [Iso.inv_hom_id_assoc]; rw [associator_inv_naturality_right_assoc]; rw [Iso.hom_inv_id_assoc]; rw [whisker_exchange_assoc]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [Iso.inv_hom_id_assoc]

中文:
引理 eHomWhiskerLeft_comp
  条件: (X : C) {Y Y' Y'' : C} (g : Y ⟶ Y') (g' : Y' ⟶ Y'')
  证明: by
  dsimp [eHomWhiskerLeft]
  rw [assoc]; rw [assoc]; rw [eHomEquiv_comp]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [← e_assoc]; rw [tensorHom_def]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [whiskerLeft_rightUnitor_assoc]; rw [whiskerLeft_rightUnitor_inv_assoc]; rw [triangle_assoc_comp_left_inv_assoc]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [Iso.hom_inv_id_assoc]; rw [Iso.inv_hom_id_assoc]; rw [associator_inv_naturality_right_assoc]; rw [Iso.hom_inv_id_assoc]; rw [whisker_exchange_assoc]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [Iso.inv_hom_id_assoc]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerRight_id_assoc, eHomEquiv_comp, eHomWhiskerLeft, e_assoc, tensorHom_def, triangle_assoc_comp_left_inv_assoc, whiskerLeft_comp_assoc, whiskerLeft_rightUnitor_assoc, whiskerLeft_rightUnitor_inv_assoc, whiskerRight_id_assoc
-/
lemma eHomWhiskerLeft_comp (X : C) {Y Y' Y'' : C} (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    eHomWhiskerLeft V X (g ≫ g') = eHomWhiskerLeft V X g ≫ eHomWhiskerLeft V X g' := by
  dsimp [eHomWhiskerLeft]
  rw [assoc]; rw [assoc]; rw [eHomEquiv_comp]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [← e_assoc]; rw [tensorHom_def]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [MonoidalCategory.whiskerLeft_comp_assoc]; rw [whiskerLeft_rightUnitor_assoc]; rw [whiskerLeft_rightUnitor_inv_assoc]; rw [triangle_assoc_comp_left_inv_assoc]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [Iso.hom_inv_id_assoc]; rw [Iso.inv_hom_id_assoc]; rw [associator_inv_naturality_right_assoc]; rw [Iso.hom_inv_id_assoc]; rw [whisker_exchange_assoc]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [Iso.inv_hom_id_assoc]

/-- Whiskering commutes with the enriched composition. -/
@[reassoc]
/--
lemma `eComp_eHomWhiskerLeft` / 引理 `eComp_eHomWhiskerLeft`

English:
lemma eComp_eHomWhiskerLeft
  given: (X Y : C) {Z Z' : C} (g : Z ⟶ Z')
  proof: by
  dsimp [eHomWhiskerLeft]
  rw [rightUnitor_inv_naturality_assoc]; rw [← whisker_exchange_assoc]
  simp

中文:
引理 eComp_eHomWhiskerLeft
  条件: (X Y : C) {Z Z' : C} (g : Z ⟶ Z')
  证明: by
  dsimp [eHomWhiskerLeft]
  rw [rightUnitor_inv_naturality_assoc]; rw [← whisker_exchange_assoc]
  simp

Depends on / 依赖: eHomWhiskerLeft, rightUnitor_inv_naturality_assoc, whisker_exchange_assoc
-/
lemma eComp_eHomWhiskerLeft (X Y : C) {Z Z' : C} (g : Z ⟶ Z') :
    eComp V X Y Z ≫ eHomWhiskerLeft V X g =
      _ ◁ eHomWhiskerLeft V Y g ≫ eComp V X Y Z' := by
  dsimp [eHomWhiskerLeft]
  rw [rightUnitor_inv_naturality_assoc]; rw [← whisker_exchange_assoc]
  simp

/-- Given an isomorphism `α : Y ≅ Y₁` in C, the enriched composition map
`eComp V X Y Z : (X ⟶[V] Y) ⊗ (Y ⟶[V] Z) ⟶ (X ⟶[V] Z)` factors through the `V`
object `(X ⟶[V] Y₁) ⊗ (Y₁ ⟶[V] Z)` via the map defined by whiskering in the
middle with `α.hom` and `α.inv`. -/
@[reassoc]
/--
lemma `eHom_whisker_cancel` / 引理 `eHom_whisker_cancel`

English:
lemma eHom_whisker_cancel
  given: {X Y Y₁ Z : C} (α : Y ≅ Y₁)
  proof: by
  dsimp [eHomWhiskerLeft, eHomWhiskerRight]
  simp only [MonoidalCategory.whiskerLeft_comp_assoc, whisker_assoc_symm,
    triangle_assoc_comp_left_inv_assoc, e_assoc', assoc]
  simp only [← comp_whiskerRight_assoc]
  change (eHomWhiskerLeft V X α.hom ≫ eHomWhiskerLeft V X α.inv) ▷ _ ≫ _ = _
  simp [← eHomWhiskerLeft_comp]

@[reassoc]

中文:
引理 eHom_whisker_cancel
  条件: {X Y Y₁ Z : C} (α : Y ≅ Y₁)
  证明: by
  dsimp [eHomWhiskerLeft, eHomWhiskerRight]
  simp only [MonoidalCategory.whiskerLeft_comp_assoc, whisker_assoc_symm,
    triangle_assoc_comp_left_inv_assoc, e_assoc', assoc]
  simp only [← comp_whiskerRight_assoc]
  change (eHomWhiskerLeft V X α.hom ≫ eHomWhiskerLeft V X α.inv) ▷ _ ≫ _ = _
  simp [← eHomWhiskerLeft_comp]

@[reassoc]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp_assoc, comp_whiskerRight_assoc, eHomWhiskerLeft, eHomWhiskerLeft_comp, eHomWhiskerRight, e_assoc, triangle_assoc_comp_left_inv_assoc, whiskerLeft_comp_assoc, whisker_assoc_symm
-/
lemma eHom_whisker_cancel {X Y Y₁ Z : C} (α : Y ≅ Y₁) :
    eHomWhiskerLeft V X α.hom ▷ _ ≫ _ ◁ eHomWhiskerRight V α.inv Z ≫
      eComp V X Y₁ Z = eComp V X Y Z := by
  dsimp [eHomWhiskerLeft, eHomWhiskerRight]
  simp only [MonoidalCategory.whiskerLeft_comp_assoc, whisker_assoc_symm,
    triangle_assoc_comp_left_inv_assoc, e_assoc', assoc]
  simp only [← comp_whiskerRight_assoc]
  change (eHomWhiskerLeft V X α.hom ≫ eHomWhiskerLeft V X α.inv) ▷ _ ≫ _ = _
  simp [← eHomWhiskerLeft_comp]

@[reassoc]
/--
lemma `eHom_whisker_cancel_inv` / 引理 `eHom_whisker_cancel_inv`

English:
lemma eHom_whisker_cancel_inv
  given: {X Y Y₁ Z : C} (α : Y ≅ Y₁)
  proof: eHom_whisker_cancel V α.symm

@[reassoc]

中文:
引理 eHom_whisker_cancel_inv
  条件: {X Y Y₁ Z : C} (α : Y ≅ Y₁)
  证明: eHom_whisker_cancel V α.symm

@[reassoc]

Depends on / 依赖: eHom_whisker_cancel
-/
lemma eHom_whisker_cancel_inv {X Y Y₁ Z : C} (α : Y ≅ Y₁) :
    eHomWhiskerLeft V X α.inv ▷ _ ≫ _ ◁ eHomWhiskerRight V α.hom Z ≫
      eComp V X Y Z = eComp V X Y₁ Z := eHom_whisker_cancel V α.symm

@[reassoc]
/--
lemma `eHom_whisker_exchange` / 引理 `eHom_whisker_exchange`

English:
lemma eHom_whisker_exchange
  given: {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y')
  proof: by
  dsimp [eHomWhiskerLeft, eHomWhiskerRight]
  rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [leftUnitor_inv_naturality_assoc]; rw [whisker_exchange_assoc]; rw [← e_assoc]; rw [leftUnitor_tensor_inv_assoc]; rw [associator_inv_naturality_left_assoc]; rw [Iso.hom_inv_id_assoc]; rw [← comp_whiskerRight_assoc]; rw [whisker_exchange_assoc]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [whisker_exchange_assoc]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [Iso.inv_hom_id_assoc]

中文:
引理 eHom_whisker_exchange
  条件: {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y')
  证明: by
  dsimp [eHomWhiskerLeft, eHomWhiskerRight]
  rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [leftUnitor_inv_naturality_assoc]; rw [whisker_exchange_assoc]; rw [← e_assoc]; rw [leftUnitor_tensor_inv_assoc]; rw [associator_inv_naturality_left_assoc]; rw [Iso.hom_inv_id_assoc]; rw [← comp_whiskerRight_assoc]; rw [whisker_exchange_assoc]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [whisker_exchange_assoc]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [Iso.inv_hom_id_assoc]

Depends on / 依赖: Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, MonoidalCategory, MonoidalCategory.whiskerRight_id_assoc, associator_inv_naturality_left_assoc, comp_whiskerRight_assoc, eHomWhiskerLeft, eHomWhiskerRight, e_assoc, hom_inv_id_assoc, inv_hom_id_assoc, leftUnitor_inv_naturality_assoc, leftUnitor_tensor_inv_assoc, whiskerRight_id_assoc, whisker_exchange_assoc
-/
lemma eHom_whisker_exchange {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    eHomWhiskerLeft V X' g ≫ eHomWhiskerRight V f Y' =
      eHomWhiskerRight V f Y ≫ eHomWhiskerLeft V X g := by
  dsimp [eHomWhiskerLeft, eHomWhiskerRight]
  rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [leftUnitor_inv_naturality_assoc]; rw [whisker_exchange_assoc]; rw [← e_assoc]; rw [leftUnitor_tensor_inv_assoc]; rw [associator_inv_naturality_left_assoc]; rw [Iso.hom_inv_id_assoc]; rw [← comp_whiskerRight_assoc]; rw [whisker_exchange_assoc]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [whisker_exchange_assoc]; rw [MonoidalCategory.whiskerRight_id_assoc]; rw [Iso.inv_hom_id_assoc]

attribute [local simp] eHom_whisker_exchange

variable (C) in
/-- The bifunctor `Cᵒᵖ ⥤ C ⥤ V` which sends `X : Cᵒᵖ` and `Y : C` to `X ⟶[V] Y`. -/
@[simps]
/--
Definition of `eHomFunctor` / `eHomFunctor` 的定义

English:
definition eHomFunctor
  signature: : Cᵒᵖ ⥤ C ⥤ V where
  body: { obj := fun Y => X.unop ⟶[V] Y
      map := fun φ => eHomWhiskerLeft V X.unop φ }
  map φ :=
    { app := fun Y => eHomWhiskerRight V φ.unop Y }

中文:
定义 eHomFunctor
  签名: : Cᵒᵖ ⥤ C ⥤ V where
  定义体: { obj := fun Y => X.unop ⟶[V] Y
      map := fun φ => eHomWhiskerLeft V X.unop φ }
  map φ :=
    { app := fun Y => eHomWhiskerRight V φ.unop Y }

Depends on / 依赖: X.unop, eHomWhiskerLeft, eHomWhiskerRight
-/
def eHomFunctor : Cᵒᵖ ⥤ C ⥤ V where
  obj X :=
    { obj := fun Y => X.unop ⟶[V] Y
      map := fun φ => eHomWhiskerLeft V X.unop φ }
  map φ :=
    { app := fun Y => eHomWhiskerRight V φ.unop Y }

/--
Instance `ForgetEnrichment.enrichedOrdinaryCategory` / 实例 `ForgetEnrichment.enrichedOrdinaryCategory`

English:
instance ForgetEnrichment.enrichedOrdinaryCategory
  signature: {D : Type*} [EnrichedCategory V D]
  body: inferInstanceAs (EnrichedCategory V D)
  homEquiv := Equiv.refl _
  homEquiv_id _ := Category.id_comp _
  homEquiv_comp _ _ := Category.assoc _ _ _

中文:
实例 ForgetEnrichment.enrichedOrdinaryCategory
  签名: {D : 类型} [Enriched范畴 V D]
  定义体: inferInstanceAs (EnrichedCategory V D)
  homEquiv := Equiv.refl _
  homEquiv_id _ := Category.id_comp _
  homEquiv_comp _ _ := Category.assoc _ _ _

Depends on / 依赖: EnrichedCategory
-/
instance ForgetEnrichment.enrichedOrdinaryCategory {D : Type*} [EnrichedCategory V D] :
    EnrichedOrdinaryCategory V (ForgetEnrichment V D) where
  toEnrichedCategory := inferInstanceAs (EnrichedCategory V D)
  homEquiv := Equiv.refl _
  homEquiv_id _ := Category.id_comp _
  homEquiv_comp _ _ := Category.assoc _ _ _

/-- If `D` is already an enriched ordinary category, there is a canonical functor from `D` to
`ForgetEnrichment V D`. -/
@[simps]
/--
Definition of `ForgetEnrichment.equivInverse` / `ForgetEnrichment.equivInverse` 的定义

English:
definition ForgetEnrichment.equivInverse
  signature: (D : Type u'') [Category.{v''} D] [EnrichedOrdinaryCategory V D]
  body: .of V X
  map f := ForgetEnrichment.homOf V (eHomEquiv V f)
  map_comp f g := by simp [eHomEquiv_comp]

中文:
定义 ForgetEnrichment.equivInverse
  签名: (D : 类型u'') [范畴.{v''} D] [EnrichedOrdinary范畴 V D]
  定义体: .of V X
  map f := ForgetEnrichment.homOf V (eHomEquiv V f)
  map_comp f g := by simp [eHomEquiv_comp]
-/
def ForgetEnrichment.equivInverse (D : Type u'') [Category.{v''} D] [EnrichedOrdinaryCategory V D] :
    D ⥤ ForgetEnrichment V D where
  obj X := .of V X
  map f := ForgetEnrichment.homOf V (eHomEquiv V f)
  map_comp f g := by simp [eHomEquiv_comp]

/-- If `D` is already an enriched ordinary category, there is a canonical functor from
`ForgetEnrichment V D` to `D`. -/
@[simps]
/--
Definition of `ForgetEnrichment.equivFunctor` / `ForgetEnrichment.equivFunctor` 的定义

English:
definition ForgetEnrichment.equivFunctor
  signature: (D : Type u'') [Category.{v''} D] [EnrichedOrdinaryCategory V D]
  body: ForgetEnrichment.to V X
  map f := (eHomEquiv V).symm (ForgetEnrichment.homTo V f)
  map_id X := by rw [ForgetEnrichment.homTo_id, ← eHomEquiv_id, Equiv.symm_apply_apply]
  map_comp {X} {Y} {Z} f g := Equiv.injective
    (eHomEquiv V (X := ForgetEnrichment.to V X) (Y := ForgetEnrichment.to V Z))
    (by simp [eHomEquiv_comp])

中文:
定义 ForgetEnrichment.equivFunctor
  签名: (D : 类型u'') [范畴.{v''} D] [EnrichedOrdinary范畴 V D]
  定义体: ForgetEnrichment.to V X
  map f := (eHomEquiv V).symm (ForgetEnrichment.homTo V f)
  map_id X := by rw [ForgetEnrichment.homTo_id, ← eHomEquiv_id, Equiv.symm_apply_apply]
  map_comp {X} {Y} {Z} f g := Equiv.injective
    (eHomEquiv V (X := ForgetEnrichment.to V X) (Y := ForgetEnrichment.to V Z))
    (by simp [eHomEquiv_comp])

Depends on / 依赖: ForgetEnrichment, ForgetEnrichment.to
-/
def ForgetEnrichment.equivFunctor (D : Type u'') [Category.{v''} D] [EnrichedOrdinaryCategory V D] :
    ForgetEnrichment V D ⥤ D where
  obj X := ForgetEnrichment.to V X
  map f := (eHomEquiv V).symm (ForgetEnrichment.homTo V f)
  map_id X := by rw [ForgetEnrichment.homTo_id, ← eHomEquiv_id, Equiv.symm_apply_apply]
  map_comp {X} {Y} {Z} f g := Equiv.injective
    (eHomEquiv V (X := ForgetEnrichment.to V X) (Y := ForgetEnrichment.to V Z))
    (by simp [eHomEquiv_comp])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `D` is already an enriched ordinary category, it is equivalent to `ForgetEnrichment V D`. -/
@[simps]
/--
Definition of `ForgetEnrichment.equiv` / `ForgetEnrichment.equiv` 的定义

English:
definition ForgetEnrichment.equiv
  signature: {D : Type u''} [Category.{v''} D] [EnrichedOrdinaryCategory V D]
  body: equivFunctor V D
  inverse := equivInverse V D
  unitIso := NatIso.ofComponents (fun X => Iso.refl _)
  counitIso := NatIso.ofComponents (fun X => Iso.refl _)
  functor_unitIso_comp X := Equiv.injective
    (eHomEquiv V (X := ForgetEnrichment.to V X) (Y := ForgetEnrichment.to V X)) (by simp)

中文:
定义 ForgetEnrichment.equiv
  签名: {D : 类型u''} [范畴.{v''} D] [EnrichedOrdinary范畴 V D]
  定义体: equivFunctor V D
  inverse := equivInverse V D
  unitIso := NatIso.ofComponents (fun X => Iso.refl _)
  counitIso := NatIso.ofComponents (fun X => Iso.refl _)
  functor_unitIso_comp X := Equiv.injective
    (eHomEquiv V (X := ForgetEnrichment.to V X) (Y := ForgetEnrichment.to V X)) (by simp)

Depends on / 依赖: equivFunctor
-/
def ForgetEnrichment.equiv {D : Type u''} [Category.{v''} D] [EnrichedOrdinaryCategory V D] :
    ForgetEnrichment V D ≌ D where
  functor := equivFunctor V D
  inverse := equivInverse V D
  unitIso := NatIso.ofComponents (fun X => Iso.refl _)
  counitIso := NatIso.ofComponents (fun X => Iso.refl _)
  functor_unitIso_comp X := Equiv.injective
    (eHomEquiv V (X := ForgetEnrichment.to V X) (Y := ForgetEnrichment.to V X)) (by simp)

/--
Definition of `eCoyoneda` / `eCoyoneda` 的定义

English:
abbreviation eCoyoneda
  signature: (X : C)
  body: (eHomFunctor V C).obj (op X)

中文:
缩写 eCoyoneda
  签名: (X : C)
  定义体: (eHomFunctor V C).obj (op X)

Depends on / 依赖: eHomFunctor
-/
abbrev eCoyoneda (X : C) := (eHomFunctor V C).obj (op X)

section TransportEnrichment

variable {V} {W : Type u''} [Category.{v''} W] [MonoidalCategory W]
  (F : V ⥤ W) [F.LaxMonoidal]
  (C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (TransportEnrichment F C)
  body: inferInstanceAs (Category C)

中文:
实例 :
  签名: 范畴 (TransportEnrichment F C)
  定义体: inferInstanceAs (Category C)

Depends on / 依赖: Category
-/
instance : Category (TransportEnrichment F C) := inferInstanceAs (Category C)

/--
Definition of `TransportEnrichment.ofOrdinaryEnrichedCategoryEquiv` / `TransportEnrichment.ofOrdinaryEnrichedCategoryEquiv` 的定义

English:
definition TransportEnrichment.ofOrdinaryEnrichedCategoryEquiv
  signature: : TransportEnrichment F C ≌ C
  body: Equivalence.refl

中文:
定义 TransportEnrichment.ofOrdinaryEnrichedCategoryEquiv
  签名: : TransportEnrichment F C ≌ C
  定义体: Equivalence.refl

Depends on / 依赖: Equivalence, Equivalence.refl
-/
def TransportEnrichment.ofOrdinaryEnrichedCategoryEquiv : TransportEnrichment F C ≌ C :=
  Equivalence.refl

open EnrichedCategory

set_option backward.isDefEq.respectTransparency false in
/-- If for a lax monoidal functor `F : V ⥤ W` the canonical function
`(𝟙_ V ⟶ v) → (𝟙_ W ⟶ F.obj v)` is bijective, and `C` is an enriched ordinary category on `V`,
then `F` induces the structure of a `W`-enriched ordinary category on `TransportEnrichment F C`,
i.e. on the same underlying category `C`. -/
@[instance_reducible]
/--
Definition of `TransportEnrichment.enrichedOrdinaryCategory` / `TransportEnrichment.enrichedOrdinaryCategory` 的定义

English:
definition TransportEnrichment.enrichedOrdinaryCategory
  body: (eHomEquiv V (C := C)).trans (e (Hom (C := C) X Y))
  homEquiv_id {X} := by simpa using! h _ (eId V _)
  homEquiv_comp f g := by
    dsimp +instances [instEnrichedCategoryTransportEnrichment]
    rw [h]; rw [h]; rw [h]; rw [← tensorHom_comp_tensorHom_assoc]; rw [eComp_eq]; rw [tensorHom_def_assoc]; rw [whiskerRight_id_assoc]; rw [unitors_inv_equal]; rw [Iso.inv_hom_id_assoc]; rw [Functor.LaxMonoidal.μ_natural_assoc]; rw [Functor.LaxMonoidal.right_unitality_inv_assoc]; rw [eHomEquiv_comp]; rw [← F.map_comp]; rw [← F.map_comp]; rw [unitors_inv_equal]

中文:
定义 TransportEnrichment.enrichedOrdinaryCategory
  定义体: (eHomEquiv V (C := C)).trans (e (Hom (C := C) X Y))
  homEquiv_id {X} := by simpa using! h _ (eId V _)
  homEquiv_comp f g := by
    dsimp +instances [instEnrichedCategoryTransportEnrichment]
    rw [h]; rw [h]; rw [h]; rw [← tensorHom_comp_tensorHom_assoc]; rw [eComp_eq]; rw [tensorHom_def_assoc]; rw [whiskerRight_id_assoc]; rw [unitors_inv_equal]; rw [Iso.inv_hom_id_assoc]; rw [Functor.LaxMonoidal.μ_natural_assoc]; rw [Functor.LaxMonoidal.right_unitality_inv_assoc]; rw [eHomEquiv_comp]; rw [← F.map_comp]; rw [← F.map_comp]; rw [unitors_inv_equal]

Depends on / 依赖: eHomEquiv
-/
def TransportEnrichment.enrichedOrdinaryCategory
    (e : forall v : V, (𝟙_ V ⟶ v) ≃ (𝟙_ W ⟶ F.obj v))
    (h : forall v : V, forall f : 𝟙_ V ⟶ v, e v f = Functor.LaxMonoidal.ε F ≫ F.map f) :
    EnrichedOrdinaryCategory W (TransportEnrichment F C) where
  homEquiv {X Y} := (eHomEquiv V (C := C)).trans (e (Hom (C := C) X Y))
  homEquiv_id {X} := by simpa using! h _ (eId V _)
  homEquiv_comp f g := by
    dsimp +instances [instEnrichedCategoryTransportEnrichment]
    rw [h]; rw [h]; rw [h]; rw [← tensorHom_comp_tensorHom_assoc]; rw [eComp_eq]; rw [tensorHom_def_assoc]; rw [whiskerRight_id_assoc]; rw [unitors_inv_equal]; rw [Iso.inv_hom_id_assoc]; rw [Functor.LaxMonoidal.μ_natural_assoc]; rw [Functor.LaxMonoidal.right_unitality_inv_assoc]; rw [eHomEquiv_comp]; rw [← F.map_comp]; rw [← F.map_comp]; rw [unitors_inv_equal]

section Equiv

variable {W : Type u''} [Category.{v''} W] [MonoidalCategory W]
  (F : V ⥤ W) [F.LaxMonoidal]
  (D : Type u) [EnrichedCategory V D]
  (e : forall v : V, (𝟙_ V ⟶ v) ≃ (𝟙_ W ⟶ F.obj v))
  (h : forall (v : V) (f : 𝟙_ V ⟶ v), (e v) f = Functor.LaxMonoidal.ε F ≫ F.map f)

set_option backward.isDefEq.respectTransparency false in
/-- The functor that makes up `TransportEnrichment.forgetEnrichmentEquiv`. -/
@[simps]
/--
Definition of `TransportEnrichment.forgetEnrichmentEquivFunctor` / `TransportEnrichment.forgetEnrichmentEquivFunctor` 的定义

English:
definition TransportEnrichment.forgetEnrichmentEquivFunctor
  signature: :
  body: ForgetEnrichment.of W X
map {X} {Y} f := ForgetEnrichment.homOf W (e (Hom (C := ForgetEnrichment V D) X Y))
    ForgetEnrichment.homTo V f
  map_id X := by
    rw [h]; rw [ForgetEnrichment.homTo_id]; rw [← TransportEnrichment.eId_eq]
    simp [ForgetEnrichment.to]
  map_comp f g := by
    rw [h]; rw [h]; rw [h]; rw [ForgetEnrichment.homTo_comp]; rw [F.map_comp]; rw [F.map_comp]; rw [← Category.assoc]; rw [← Functor.LaxMonoidal.left_unitality_inv]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [← Functor.LaxMonoidal.μ_natural_assoc]; rw [← TransportEnrichment.eComp_eq]; rw [← ForgetEnrichment.homOf_comp]; rw [leftUnitor_inv_naturality_assoc]; rw [← tensorHom_def'_assoc]; rw [tensorHom_comp_tensorHom_assoc]
    rfl

中文:
定义 TransportEnrichment.forgetEnrichmentEquivFunctor
  签名: :
  定义体: ForgetEnrichment.of W X
map {X} {Y} f := ForgetEnrichment.homOf W (e (Hom (C := ForgetEnrichment V D) X Y))
    ForgetEnrichment.homTo V f
  map_id X := by
    rw [h]; rw [ForgetEnrichment.homTo_id]; rw [← TransportEnrichment.eId_eq]
    simp [ForgetEnrichment.to]
  map_comp f g := by
    rw [h]; rw [h]; rw [h]; rw [ForgetEnrichment.homTo_comp]; rw [F.map_comp]; rw [F.map_comp]; rw [← Category.assoc]; rw [← Functor.LaxMonoidal.left_unitality_inv]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [← Functor.LaxMonoidal.μ_natural_assoc]; rw [← TransportEnrichment.eComp_eq]; rw [← ForgetEnrichment.homOf_comp]; rw [leftUnitor_inv_naturality_assoc]; rw [← tensorHom_def'_assoc]; rw [tensorHom_comp_tensorHom_assoc]
    rfl

Depends on / 依赖: ForgetEnrichment, ForgetEnrichment.of
-/
def TransportEnrichment.forgetEnrichmentEquivFunctor :
    TransportEnrichment F (ForgetEnrichment V D) ⥤
      ForgetEnrichment W (TransportEnrichment F D) where
  obj X := ForgetEnrichment.of W X
map {X} {Y} f := ForgetEnrichment.homOf W (e (Hom (C := ForgetEnrichment V D) X Y))
    ForgetEnrichment.homTo V f
  map_id X := by
    rw [h]; rw [ForgetEnrichment.homTo_id]; rw [← TransportEnrichment.eId_eq]
    simp [ForgetEnrichment.to]
  map_comp f g := by
    rw [h]; rw [h]; rw [h]; rw [ForgetEnrichment.homTo_comp]; rw [F.map_comp]; rw [F.map_comp]; rw [← Category.assoc]; rw [← Functor.LaxMonoidal.left_unitality_inv]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [← Functor.LaxMonoidal.μ_natural_assoc]; rw [← TransportEnrichment.eComp_eq]; rw [← ForgetEnrichment.homOf_comp]; rw [leftUnitor_inv_naturality_assoc]; rw [← tensorHom_def'_assoc]; rw [tensorHom_comp_tensorHom_assoc]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse functor that makes up `TransportEnrichment.forgetEnrichmentEquiv`. -/
@[simps]
/--
Definition of `TransportEnrichment.forgetEnrichmentEquivInverse` / `TransportEnrichment.forgetEnrichmentEquivInverse` 的定义

English:
definition TransportEnrichment.forgetEnrichmentEquivInverse
  signature: :
  body: ForgetEnrichment.of V (ForgetEnrichment.to (C := TransportEnrichment F D) W X)
  map f := ForgetEnrichment.homOf V ((e _).symm (ForgetEnrichment.homTo W f))
  map_id X := by
    rw [← ForgetEnrichment.homOf_eId]
    congr 1
    apply Equiv.injective (e _)
    rw [ForgetEnrichment.homTo_id]; rw [Equiv.apply_symm_apply]; rw [h]; rw [TransportEnrichment.eId_eq]
  map_comp f g := by
    rw [← ForgetEnrichment.homOf_comp]
    congr
    apply Equiv.injective (e _)
    rw [Equiv.apply_symm_apply]; rw [h]
    simp only [ForgetEnrichment.homTo_comp, eComp_eq, Category.assoc, Functor.map_comp]
    slice_rhs 1 3 =>
      rw [← Functor.LaxMonoidal.left_unitality_inv]; rw [Category.assoc]; rw [Category.assoc]; rw [← Functor.LaxMonoidal.μ_natural]; rw [← leftUnitor_inv_comp_tensorHom_assoc]; rw [tensorHom_comp_tensorHom_assoc]
    simp [← h]

中文:
定义 TransportEnrichment.forgetEnrichmentEquivInverse
  签名: :
  定义体: ForgetEnrichment.of V (ForgetEnrichment.to (C := TransportEnrichment F D) W X)
  map f := ForgetEnrichment.homOf V ((e _).symm (ForgetEnrichment.homTo W f))
  map_id X := by
    rw [← ForgetEnrichment.homOf_eId]
    congr 1
    apply Equiv.injective (e _)
    rw [ForgetEnrichment.homTo_id]; rw [Equiv.apply_symm_apply]; rw [h]; rw [TransportEnrichment.eId_eq]
  map_comp f g := by
    rw [← ForgetEnrichment.homOf_comp]
    congr
    apply Equiv.injective (e _)
    rw [Equiv.apply_symm_apply]; rw [h]
    simp only [ForgetEnrichment.homTo_comp, eComp_eq, Category.assoc, Functor.map_comp]
    slice_rhs 1 3 =>
      rw [← Functor.LaxMonoidal.left_unitality_inv]; rw [Category.assoc]; rw [Category.assoc]; rw [← Functor.LaxMonoidal.μ_natural]; rw [← leftUnitor_inv_comp_tensorHom_assoc]; rw [tensorHom_comp_tensorHom_assoc]
    simp [← h]

Depends on / 依赖: ForgetEnrichment, ForgetEnrichment.of, ForgetEnrichment.to, TransportEnrichment
-/
def TransportEnrichment.forgetEnrichmentEquivInverse :
    ForgetEnrichment W (TransportEnrichment F D) ⥤ TransportEnrichment F (ForgetEnrichment V D)
      where
  obj X := ForgetEnrichment.of V (ForgetEnrichment.to (C := TransportEnrichment F D) W X)
  map f := ForgetEnrichment.homOf V ((e _).symm (ForgetEnrichment.homTo W f))
  map_id X := by
    rw [← ForgetEnrichment.homOf_eId]
    congr 1
    apply Equiv.injective (e _)
    rw [ForgetEnrichment.homTo_id]; rw [Equiv.apply_symm_apply]; rw [h]; rw [TransportEnrichment.eId_eq]
  map_comp f g := by
    rw [← ForgetEnrichment.homOf_comp]
    congr
    apply Equiv.injective (e _)
    rw [Equiv.apply_symm_apply]; rw [h]
    simp only [ForgetEnrichment.homTo_comp, eComp_eq, Category.assoc, Functor.map_comp]
    slice_rhs 1 3 =>
      rw [← Functor.LaxMonoidal.left_unitality_inv]; rw [Category.assoc]; rw [Category.assoc]; rw [← Functor.LaxMonoidal.μ_natural]; rw [← leftUnitor_inv_comp_tensorHom_assoc]; rw [tensorHom_comp_tensorHom_assoc]
    simp [← h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `D` is a `V`-enriched category, then forgetting the enrichment and transporting the resulting
enriched ordinary category along a functor `F : V ⥤ W`, for which
`f ↦ Functor.LaxMonoidal.ε F ≫ F.map f` has an inverse, results in a category equivalent to
transporting along `F` and then forgetting about the resulting `W`-enrichment. -/
@[simps]
/--
Definition of `TransportEnrichment.forgetEnrichmentEquiv` / `TransportEnrichment.forgetEnrichmentEquiv` 的定义

English:
definition TransportEnrichment.forgetEnrichmentEquiv
  signature: : TransportEnrichment F (ForgetEnrichment V D) ≌
  body: forgetEnrichmentEquivFunctor _ _ e h
  inverse := forgetEnrichmentEquivInverse _ _ e h
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun f => by
    simp [ForgetEnrichment.to, ForgetEnrichment.of]
  functor_unitIso_comp X := by
    simp only [Functor.id_obj, forgetEnrichmentEquivFunctor_obj, Functor.comp_obj,
      forgetEnrichmentEquivInverse_obj, ForgetEnrichment.to_of, NatIso.ofComponents_hom_app,
      Iso.refl_hom, forgetEnrichmentEquivFunctor_map, h, Category.comp_id]
    rw [← ForgetEnrichment.homOf_eId]; rw [TransportEnrichment.eId_eq]; rw [ForgetEnrichment.homTo_id]
    rfl

中文:
定义 TransportEnrichment.forgetEnrichmentEquiv
  签名: : TransportEnrichment F (ForgetEnrichment V D) ≌
  定义体: forgetEnrichmentEquivFunctor _ _ e h
  inverse := forgetEnrichmentEquivInverse _ _ e h
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun f => by
    simp [ForgetEnrichment.to, ForgetEnrichment.of]
  functor_unitIso_comp X := by
    simp only [Functor.id_obj, forgetEnrichmentEquivFunctor_obj, Functor.comp_obj,
      forgetEnrichmentEquivInverse_obj, ForgetEnrichment.to_of, NatIso.ofComponents_hom_app,
      Iso.refl_hom, forgetEnrichmentEquivFunctor_map, h, Category.comp_id]
    rw [← ForgetEnrichment.homOf_eId]; rw [TransportEnrichment.eId_eq]; rw [ForgetEnrichment.homTo_id]
    rfl

Depends on / 依赖: forgetEnrichmentEquivFunctor
-/
def TransportEnrichment.forgetEnrichmentEquiv : TransportEnrichment F (ForgetEnrichment V D) ≌
    ForgetEnrichment W (TransportEnrichment F D) where
  functor := forgetEnrichmentEquivFunctor _ _ e h
  inverse := forgetEnrichmentEquivInverse _ _ e h
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun f => by
    simp [ForgetEnrichment.to, ForgetEnrichment.of]
  functor_unitIso_comp X := by
    simp only [Functor.id_obj, forgetEnrichmentEquivFunctor_obj, Functor.comp_obj,
      forgetEnrichmentEquivInverse_obj, ForgetEnrichment.to_of, NatIso.ofComponents_hom_app,
      Iso.refl_hom, forgetEnrichmentEquivFunctor_map, h, Category.comp_id]
    rw [← ForgetEnrichment.homOf_eId]; rw [TransportEnrichment.eId_eq]; rw [ForgetEnrichment.homTo_id]
    rfl

end Equiv

end TransportEnrichment

section full_subcategory

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- A full subcategory of an enriched ordinary category is an enriched ordinary category. -/
instance (P : ObjectProperty C) :
    EnrichedOrdinaryCategory V (ObjectProperty.FullSubcategory P) where
  Hom X Y := X.obj ⟶[V] Y.obj
  id X := eId V X.obj
  comp X Y Z := eComp V X.obj Y.obj Z.obj
  homEquiv {X} {Y} := P.fullyFaithfulι.homEquiv.trans (eHomEquiv V)
  homEquiv_id {X} := by
    change _ = eId V X.obj
    rw [← eHomEquiv_id]
    rfl
  homEquiv_comp f g := by
    simp only [ObjectProperty.ι_obj]
    change (eHomEquiv V) (P.ι.map (f ≫ g)) = _
    rw [Functor.map_comp]; rw [eHomEquiv_comp]
    rfl

end full_subcategory

end CategoryTheory
