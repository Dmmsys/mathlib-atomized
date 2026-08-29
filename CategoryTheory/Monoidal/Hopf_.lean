/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Bimon_
public import Mathlib.CategoryTheory.Monoidal.Conv

/-!
# The category of Hopf monoids in a braided monoidal category.


## TODO

* Show that in a Cartesian monoidal category Hopf monoids are exactly group objects.
* Show that `Hopf (ModuleCat R) ≌ HopfAlgCat R`.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]

open scoped MonObj ComonObj

/--
Definition of `HopfObj` / `HopfObj` 的定义

English:
class HopfObj
  parameters: (X : C)
  extends: BimonObj X
  axioms and operations (3):
    - antipode : X ⟶ X
    - antipode_left((X)) : Δ ≫ antipode ▷ X ≫ μ = ε ≫ η  [default: by cat_disch]
    - antipode_right((X)) : Δ ≫ X ◁ antipode ≫ μ = ε ≫ η  [default: by cat_disch]

中文:
类 HopfObj
  参数: (X : C)
  继承: BimonObj X
  公理与运算 (3 个):
    - antipode : X ⟶ X
    - antipode_left((X)) : Δ ≫ antipode ▷ X ≫ μ = ε ≫ η  [默认: by cat_disch]
    - antipode_right((X)) : Δ ≫ X ◁ antipode ≫ μ = ε ≫ η  [默认: by cat_disch]

Depends on / 依赖: antipode, antipode_right, cat_disch
-/
class HopfObj (X : C) extends BimonObj X where
  /-- The antipode is an endomorphism of the underlying object of the Hopf monoid. -/
  antipode : X ⟶ X
  antipode_left (X) : Δ ≫ antipode ▷ X ≫ μ = ε ≫ η := by cat_disch
  antipode_right (X) : Δ ≫ X ◁ antipode ≫ μ = ε ≫ η := by cat_disch

namespace HopfObj

@[inherit_doc] scoped notation "𝒮" => HopfObj.antipode
@[inherit_doc] scoped notation "𝒮[" M "]" => HopfObj.antipode (X := M)

attribute [reassoc (attr := simp)] antipode_left antipode_right


end HopfObj

variable (C)

/--
Definition of `Hopf` / `Hopf` 的定义

English:
structure Hopf
  parameters: where
  axioms and operations (2):
    - X : C
    - [hopf : HopfObj X]

中文:
结构 Hopf
  参数: where
  公理与运算 (2 个):
    - X : C
    - [hopf : HopfObj X]
-/
structure Hopf where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [hopf : HopfObj X]

attribute [instance] Hopf.hopf

namespace Hopf

variable {C}

/--
Definition of `toBimon` / `toBimon` 的定义

English:
definition toBimon
  signature: (A : Hopf C)
  body: .mk' A.X

中文:
定义 toBimon
  签名: (A : Hopf C)
  定义体: .mk' A.X
-/
def toBimon (A : Hopf C) : Bimon C := .mk' A.X

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Hopf C)
  body: inferInstanceAs Category (InducedCategory (Bimon C) Hopf.toBimon)

中文:
实例 :
  签名: 范畴 (Hopf C)
  定义体: inferInstanceAs Category (InducedCategory (Bimon C) Hopf.toBimon)

Depends on / 依赖: Category, Hopf.toBimon, InducedCategory, toBimon
-/
instance : Category (Hopf C) :=
inferInstanceAs Category (InducedCategory (Bimon C) Hopf.toBimon)

end Hopf

namespace HopfObj

variable {C}

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `hom_antipode` / 定理 `hom_antipode`

English:
theorem hom_antipode
  given: {A B : C} [HopfObj A] [HopfObj B] (f : A ⟶ B) [IsBimonHom f]
  proof: by
  -- We show these elements are equal by exhibiting an element in the convolution algebra
  -- between `A` (as a comonoid) and `B` (as a monoid),
  -- such that the LHS is a left inverse, and the RHS is a right inverse.
  apply left_inv_eq_right_inv
    (M := Conv A B)
    (a := f)
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [comp_whiskerRight, Category.assoc]
    slice_lhs 3 4 =>
      rw [← whisker_exchange]
    slice_lhs 2 3 =>
      rw [← tensorHom_def]
    slice_lhs 1 2 =>
      rw [← IsComonHom.hom_comul f]
    slice_lhs 2 4 =>
      rw [antipode_left]
    slice_lhs 1 2 =>
      rw [IsComonHom.hom_counit]
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [whiskerLeft_comp, Category.assoc]
    slice_lhs 2 3 =>
      rw [← whisker_exchange]
    slice_lhs 3 4 =>
      rw [← tensorHom_def]
    slice_lhs 3 4 =>
      rw [← IsMonHom.mul_hom]
    slice_lhs 1 3 =>
      rw [antipode_right]
    slice_lhs 2 3 =>
      rw [IsMonHom.one_hom]

@[reassoc (attr := simp)]

中文:
定理 hom_antipode
  条件: {A B : C} [HopfObj A] [HopfObj B] (f : A ⟶ B) [是Bimon态射 f]
  证明: by
  -- We show these elements are equal by exhibiting an element in the convolution algebra
  -- between `A` (as a comonoid) and `B` (as a monoid),
  -- such that the LHS is a left inverse, and the RHS is a right inverse.
  apply left_inv_eq_right_inv
    (M := Conv A B)
    (a := f)
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [comp_whiskerRight, Category.assoc]
    slice_lhs 3 4 =>
      rw [← whisker_exchange]
    slice_lhs 2 3 =>
      rw [← tensorHom_def]
    slice_lhs 1 2 =>
      rw [← IsComonHom.hom_comul f]
    slice_lhs 2 4 =>
      rw [antipode_left]
    slice_lhs 1 2 =>
      rw [IsComonHom.hom_counit]
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [whiskerLeft_comp, Category.assoc]
    slice_lhs 2 3 =>
      rw [← whisker_exchange]
    slice_lhs 3 4 =>
      rw [← tensorHom_def]
    slice_lhs 3 4 =>
      rw [← IsMonHom.mul_hom]
    slice_lhs 1 3 =>
      rw [antipode_right]
    slice_lhs 2 3 =>
      rw [IsMonHom.one_hom]

@[reassoc (attr := simp)]
-/
theorem hom_antipode {A B : C} [HopfObj A] [HopfObj B] (f : A ⟶ B) [IsBimonHom f] :
    f ≫ 𝒮 = 𝒮 ≫ f := by
  -- We show these elements are equal by exhibiting an element in the convolution algebra
  -- between `A` (as a comonoid) and `B` (as a monoid),
  -- such that the LHS is a left inverse, and the RHS is a right inverse.
  apply left_inv_eq_right_inv
    (M := Conv A B)
    (a := f)
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [comp_whiskerRight, Category.assoc]
    slice_lhs 3 4 =>
      rw [← whisker_exchange]
    slice_lhs 2 3 =>
      rw [← tensorHom_def]
    slice_lhs 1 2 =>
      rw [← IsComonHom.hom_comul f]
    slice_lhs 2 4 =>
      rw [antipode_left]
    slice_lhs 1 2 =>
      rw [IsComonHom.hom_counit]
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [whiskerLeft_comp, Category.assoc]
    slice_lhs 2 3 =>
      rw [← whisker_exchange]
    slice_lhs 3 4 =>
      rw [← tensorHom_def]
    slice_lhs 3 4 =>
      rw [← IsMonHom.mul_hom]
    slice_lhs 1 3 =>
      rw [antipode_right]
    slice_lhs 2 3 =>
      rw [IsMonHom.one_hom]

@[reassoc (attr := simp)]
/--
theorem `one_antipode` / 定理 `one_antipode`

English:
theorem one_antipode
  given: (A : C) [HopfObj A]
  statement: η[A] ≫ 𝒮[A] = η[A]
  proof: by
  have := (rfl : η[A] ≫ Δ[A] ≫ (𝒮[A] ▷ A) ≫ μ[A] = _)
  conv at this =>
    rhs
    rw [antipode_left]
  rw [Bimon.one_comul_assoc]; rw [tensorHom_def_assoc]; rw [unitors_inv_equal]; rw [← rightUnitor_inv_naturality_assoc]; rw [whisker_exchange_assoc]; rw [← rightUnitor_inv_naturality_assoc]; rw [rightUnitor_inv_naturality_assoc] at this
  simpa

@[reassoc (attr := simp)]

中文:
定理 one_antipode
  条件: (A : C) [HopfObj A]
  结论: η[A] ≫ 𝒮[A] = η[A]
  证明: by
  have := (rfl : η[A] ≫ Δ[A] ≫ (𝒮[A] ▷ A) ≫ μ[A] = _)
  conv at this =>
    rhs
    rw [antipode_left]
  rw [Bimon.one_comul_assoc]; rw [tensorHom_def_assoc]; rw [unitors_inv_equal]; rw [← rightUnitor_inv_naturality_assoc]; rw [whisker_exchange_assoc]; rw [← rightUnitor_inv_naturality_assoc]; rw [rightUnitor_inv_naturality_assoc] at this
  simpa

@[reassoc (attr := simp)]

Depends on / 依赖: Bimon.one_comul_assoc, antipode_left, one_comul_assoc, rightUnitor_inv_naturality_assoc, tensorHom_def_assoc, unitors_inv_equal, whisker_exchange_assoc
-/
theorem one_antipode (A : C) [HopfObj A] : η[A] ≫ 𝒮[A] = η[A] := by
  have := (rfl : η[A] ≫ Δ[A] ≫ (𝒮[A] ▷ A) ≫ μ[A] = _)
  conv at this =>
    rhs
    rw [antipode_left]
  rw [Bimon.one_comul_assoc]; rw [tensorHom_def_assoc]; rw [unitors_inv_equal]; rw [← rightUnitor_inv_naturality_assoc]; rw [whisker_exchange_assoc]; rw [← rightUnitor_inv_naturality_assoc]; rw [rightUnitor_inv_naturality_assoc] at this
  simpa

@[reassoc (attr := simp)]
/--
theorem `antipode_counit` / 定理 `antipode_counit`

English:
theorem antipode_counit
  given: (A : C) [HopfObj A]
  statement: 𝒮[A] ≫ ε[A] = ε[A]
  proof: by
  have := (rfl : Δ[A] ≫ (𝒮[A] ▷ A) ≫ μ[A] ≫ ε[A] = _)
  conv at this =>
    rhs
    rw [antipode_left_assoc]
  rw [Bimon.mul_counit]; rw [tensorHom_def']; rw [Category.assoc]; rw [← whisker_exchange_assoc] at this
  simpa [unitors_equal]

中文:
定理 antipode_counit
  条件: (A : C) [HopfObj A]
  结论: 𝒮[A] ≫ ε[A] = ε[A]
  证明: by
  have := (rfl : Δ[A] ≫ (𝒮[A] ▷ A) ≫ μ[A] ≫ ε[A] = _)
  conv at this =>
    rhs
    rw [antipode_left_assoc]
  rw [Bimon.mul_counit]; rw [tensorHom_def']; rw [Category.assoc]; rw [← whisker_exchange_assoc] at this
  simpa [unitors_equal]

Depends on / 依赖: Bimon.mul_counit, Category, Category.assoc, Final.preservesColimitsOfShape_of_final, FinallySmall, FinallySmall.fromFilteredFinalModel, antipode_left_assoc, fromFilteredFinalModel, mul_counit, preservesColimitsOfShape_of_final, tensorHom_def, unitors_equal, whisker_exchange_assoc
-/
theorem antipode_counit (A : C) [HopfObj A] : 𝒮[A] ≫ ε[A] = ε[A] := by
  have := (rfl : Δ[A] ≫ (𝒮[A] ▷ A) ≫ μ[A] ≫ ε[A] = _)
  conv at this =>
    rhs
    rw [antipode_left_assoc]
  rw [Bimon.mul_counit]; rw [tensorHom_def']; rw [Category.assoc]; rw [← whisker_exchange_assoc] at this
  simpa [unitors_equal]


/--
theorem `antipode_comul₁` / 定理 `antipode_comul₁`

English:
theorem antipode_comul₁
  given: (A : C) [HopfObj A]
  proof: by
  slice_lhs 3 5 =>
    rw [← associator_naturality_right]; rw [← Category.assoc]; rw [← tensorHom_def]
  slice_lhs 3 9 =>
    rw [Bimon.compatibility]
  slice_lhs 1 3 =>
    rw [antipode_left]
  simp [MonObj.tensorObj.one_def]

中文:
定理 antipode_comul₁
  条件: (A : C) [HopfObj A]
  证明: by
  slice_lhs 3 5 =>
    rw [← associator_naturality_right]; rw [← Category.assoc]; rw [← tensorHom_def]
  slice_lhs 3 9 =>
    rw [Bimon.compatibility]
  slice_lhs 1 3 =>
    rw [antipode_left]
  simp [MonObj.tensorObj.one_def]

Depends on / 依赖: Bimon.compatibility, Category, Category.assoc, Final.preservesColimitsOfShape_of_final, FinallySmall, FinallySmall.fromFilteredFinalModel, MonObj, MonObj.tensorObj.one_def, antipode_left, associator_naturality_right, compatibility, fromFilteredFinalModel, one_def, preservesColimitsOfShape_of_final, slice_lhs, tensorHom_def, tensorObj
-/
theorem antipode_comul₁ (A : C) [HopfObj A] :
    Δ[A] ≫
      𝒮[A] ▷ A ≫
      Δ[A] ▷ A ≫
      (α_ A A A).hom ≫
      A ◁ A ◁ Δ[A] ≫
      A ◁ (α_ A A A).inv ≫
      A ◁ (β_ A A).hom ▷ A ≫
      A ◁ (α_ A A A).hom ≫
      (α_ A A (A otimes A)).inv ≫
      (μ[A] otimesₘ μ[A]) =
    ε[A] ≫ (fun_ (𝟙_ C)).inv ≫ (η[A] otimesₘ η[A]) := by
  slice_lhs 3 5 =>
    rw [← associator_naturality_right]; rw [← Category.assoc]; rw [← tensorHom_def]
  slice_lhs 3 9 =>
    rw [Bimon.compatibility]
  slice_lhs 1 3 =>
    rw [antipode_left]
  simp [MonObj.tensorObj.one_def]

/--
theorem `antipode_comul₂` / 定理 `antipode_comul₂`

English:
theorem antipode_comul₂
  given: (A : C) [HopfObj A]
  proof: by
  -- We should write a version of `slice_lhs` that zooms through whiskerings.
  slice_lhs 6 6 =>
    simp only [tensorHom_def', whiskerLeft_comp]
  slice_lhs 7 8 =>
    rw [← whiskerLeft_comp]; rw [associator_inv_naturality_middle]; rw [whiskerLeft_comp]
  slice_lhs 8 9 =>
    rw [← whiskerLeft_comp]; rw [← comp_whiskerRight]; rw [BraidedCategory.braiding_naturality_right]; rw [comp_whiskerRight]; rw [whiskerLeft_comp]
  slice_lhs 9 10 =>
    rw [← whiskerLeft_comp]; rw [associator_naturality_left]; rw [whiskerLeft_comp]
  slice_lhs 5 6 =>
    rw [← whiskerLeft_comp]; rw [← whiskerLeft_comp]; rw [← BraidedCategory.braiding_naturality_left]; rw [whiskerLeft_comp]; rw [whiskerLeft_comp]
  slice_lhs 11 12 =>
    rw [tensorHom_def']; rw [← Category.assoc]; rw [← associator_inv_naturality_right]
  slice_lhs 10 11 =>
    rw [← whiskerLeft_comp]; rw [← whisker_exchange]; rw [whiskerLeft_comp]
  slice_lhs 6 10 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.hexagon_reverse_assoc]; rw [Iso.inv_hom_id_assoc]; rw [← BraidedCategory.braiding_naturality_left]
    simp only [whiskerLeft_comp]
  rw [ComonObj.comul_assoc_flip_assoc]; rw [Iso.inv_hom_id_assoc]
  slice_lhs 2 3 =>
    simp only [← whiskerLeft_comp]
    rw [ComonObj.comul_assoc]
    simp only [whiskerLeft_comp]
  slice_lhs 3 7 =>
    simp only [← whiskerLeft_comp]
    rw [← associator_naturality_middle_assoc]; rw [Iso.hom_inv_id_assoc]
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
    simp only [whiskerLeft_comp]
  slice_lhs 2 3 =>
    simp only [← whiskerLeft_comp]
    rw [ComonObj.counit_comul]
  slice_lhs 3 4 =>
    simp only [← whiskerLeft_comp]
    rw [BraidedCategory.braiding_naturality_left]
    simp only [whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← whiskerLeft_comp]
    rw [whisker_exchange]
    simp only [whiskerLeft_comp]
  slice_lhs 5 7 =>
    rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange]
  simp only [braiding_tensorUnit_left,
    whiskerLeft_comp, whiskerLeft_rightUnitor_inv,
    whiskerRight_id, whiskerLeft_rightUnitor, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc, whiskerLeft_inv_hom_assoc, antipode_right_assoc]
  rw [rightUnitor_inv_naturality_assoc]; rw [tensorHom_def]
  monoidal

中文:
定理 antipode_comul₂
  条件: (A : C) [HopfObj A]
  证明: by
  -- We should write a version of `slice_lhs` that zooms through whiskerings.
  slice_lhs 6 6 =>
    simp only [tensorHom_def', whiskerLeft_comp]
  slice_lhs 7 8 =>
    rw [← whiskerLeft_comp]; rw [associator_inv_naturality_middle]; rw [whiskerLeft_comp]
  slice_lhs 8 9 =>
    rw [← whiskerLeft_comp]; rw [← comp_whiskerRight]; rw [BraidedCategory.braiding_naturality_right]; rw [comp_whiskerRight]; rw [whiskerLeft_comp]
  slice_lhs 9 10 =>
    rw [← whiskerLeft_comp]; rw [associator_naturality_left]; rw [whiskerLeft_comp]
  slice_lhs 5 6 =>
    rw [← whiskerLeft_comp]; rw [← whiskerLeft_comp]; rw [← BraidedCategory.braiding_naturality_left]; rw [whiskerLeft_comp]; rw [whiskerLeft_comp]
  slice_lhs 11 12 =>
    rw [tensorHom_def']; rw [← Category.assoc]; rw [← associator_inv_naturality_right]
  slice_lhs 10 11 =>
    rw [← whiskerLeft_comp]; rw [← whisker_exchange]; rw [whiskerLeft_comp]
  slice_lhs 6 10 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.hexagon_reverse_assoc]; rw [Iso.inv_hom_id_assoc]; rw [← BraidedCategory.braiding_naturality_left]
    simp only [whiskerLeft_comp]
  rw [ComonObj.comul_assoc_flip_assoc]; rw [Iso.inv_hom_id_assoc]
  slice_lhs 2 3 =>
    simp only [← whiskerLeft_comp]
    rw [ComonObj.comul_assoc]
    simp only [whiskerLeft_comp]
  slice_lhs 3 7 =>
    simp only [← whiskerLeft_comp]
    rw [← associator_naturality_middle_assoc]; rw [Iso.hom_inv_id_assoc]
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
    simp only [whiskerLeft_comp]
  slice_lhs 2 3 =>
    simp only [← whiskerLeft_comp]
    rw [ComonObj.counit_comul]
  slice_lhs 3 4 =>
    simp only [← whiskerLeft_comp]
    rw [BraidedCategory.braiding_naturality_left]
    simp only [whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← whiskerLeft_comp]
    rw [whisker_exchange]
    simp only [whiskerLeft_comp]
  slice_lhs 5 7 =>
    rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange]
  simp only [braiding_tensorUnit_left,
    whiskerLeft_comp, whiskerLeft_rightUnitor_inv,
    whiskerRight_id, whiskerLeft_rightUnitor, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc, whiskerLeft_inv_hom_assoc, antipode_right_assoc]
  rw [rightUnitor_inv_naturality_assoc]; rw [tensorHom_def]
  monoidal
-/
theorem antipode_comul₂ (A : C) [HopfObj A] :
    Δ[A] ≫
      Δ[A] ▷ A ≫
      (α_ A A A).hom ≫
      A ◁ A ◁ Δ[A] ≫
      A ◁ A ◁ (β_ A A).hom ≫
      A ◁ A ◁ (𝒮[A] otimesₘ 𝒮[A]) ≫
      A ◁ (α_ A A A).inv ≫
      A ◁ (β_ A A).hom ▷ A ≫
      A ◁ (α_ A A A).hom ≫
      (α_ A A (A otimes A)).inv ≫
      (μ[A] otimesₘ μ[A]) =
    ε[A] ≫ (fun_ (𝟙_ C)).inv ≫ (η[A] otimesₘ η[A]) := by
  -- We should write a version of `slice_lhs` that zooms through whiskerings.
  slice_lhs 6 6 =>
    simp only [tensorHom_def', whiskerLeft_comp]
  slice_lhs 7 8 =>
    rw [← whiskerLeft_comp]; rw [associator_inv_naturality_middle]; rw [whiskerLeft_comp]
  slice_lhs 8 9 =>
    rw [← whiskerLeft_comp]; rw [← comp_whiskerRight]; rw [BraidedCategory.braiding_naturality_right]; rw [comp_whiskerRight]; rw [whiskerLeft_comp]
  slice_lhs 9 10 =>
    rw [← whiskerLeft_comp]; rw [associator_naturality_left]; rw [whiskerLeft_comp]
  slice_lhs 5 6 =>
    rw [← whiskerLeft_comp]; rw [← whiskerLeft_comp]; rw [← BraidedCategory.braiding_naturality_left]; rw [whiskerLeft_comp]; rw [whiskerLeft_comp]
  slice_lhs 11 12 =>
    rw [tensorHom_def']; rw [← Category.assoc]; rw [← associator_inv_naturality_right]
  slice_lhs 10 11 =>
    rw [← whiskerLeft_comp]; rw [← whisker_exchange]; rw [whiskerLeft_comp]
  slice_lhs 6 10 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.hexagon_reverse_assoc]; rw [Iso.inv_hom_id_assoc]; rw [← BraidedCategory.braiding_naturality_left]
    simp only [whiskerLeft_comp]
  rw [ComonObj.comul_assoc_flip_assoc]; rw [Iso.inv_hom_id_assoc]
  slice_lhs 2 3 =>
    simp only [← whiskerLeft_comp]
    rw [ComonObj.comul_assoc]
    simp only [whiskerLeft_comp]
  slice_lhs 3 7 =>
    simp only [← whiskerLeft_comp]
    rw [← associator_naturality_middle_assoc]; rw [Iso.hom_inv_id_assoc]
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
    simp only [whiskerLeft_comp]
  slice_lhs 2 3 =>
    simp only [← whiskerLeft_comp]
    rw [ComonObj.counit_comul]
  slice_lhs 3 4 =>
    simp only [← whiskerLeft_comp]
    rw [BraidedCategory.braiding_naturality_left]
    simp only [whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← whiskerLeft_comp]
    rw [whisker_exchange]
    simp only [whiskerLeft_comp]
  slice_lhs 5 7 =>
    rw [associator_inv_naturality_right_assoc]; rw [whisker_exchange]
  simp only [braiding_tensorUnit_left,
    whiskerLeft_comp, whiskerLeft_rightUnitor_inv,
    whiskerRight_id, whiskerLeft_rightUnitor, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc, whiskerLeft_inv_hom_assoc, antipode_right_assoc]
  rw [rightUnitor_inv_naturality_assoc]; rw [tensorHom_def]
  monoidal

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `antipode_comul` / 定理 `antipode_comul`

English:
theorem antipode_comul
  given: (A : C) [HopfObj A]
  proof: by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv A (A otimes A))
    (a := Δ[A])
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [comp_whiskerRight, tensor_whiskerLeft, MonObj.tensorObj.mul_def, Category.assoc,
      MonObj.tensorObj.one_def]
    simp only [tensorμ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact antipode_comul₁ A
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [whiskerLeft_comp, tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc,
      MonObj.tensorObj.mul_def, MonObj.tensorObj.one_def]
    simp only [tensorμ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact antipode_comul₂ A

中文:
定理 antipode_comul
  条件: (A : C) [HopfObj A]
  证明: by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv A (A otimes A))
    (a := Δ[A])
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [comp_whiskerRight, tensor_whiskerLeft, MonObj.tensorObj.mul_def, Category.assoc,
      MonObj.tensorObj.one_def]
    simp only [tensorμ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact antipode_comul₁ A
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [whiskerLeft_comp, tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc,
      MonObj.tensorObj.mul_def, MonObj.tensorObj.one_def]
    simp only [tensorμ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact antipode_comul₂ A

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, isColimitPresheafFiberCocone, isIso_hom, otimes, tensor
-/
theorem antipode_comul (A : C) [HopfObj A] :
    𝒮[A] ≫ Δ[A] = Δ[A] ≫ (β_ _ _).hom ≫ (𝒮[A] otimesₘ 𝒮[A]) := by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv A (A otimes A))
    (a := Δ[A])
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [comp_whiskerRight, tensor_whiskerLeft, MonObj.tensorObj.mul_def, Category.assoc,
      MonObj.tensorObj.one_def]
    simp only [tensorμ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact antipode_comul₁ A
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [whiskerLeft_comp, tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc,
      MonObj.tensorObj.mul_def, MonObj.tensorObj.one_def]
    simp only [tensorμ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact antipode_comul₂ A

/--
theorem `mul_antipode₁` / 定理 `mul_antipode₁`

English:
theorem mul_antipode₁
  given: (A : C) [HopfObj A]
  proof: by
  slice_lhs 8 9 =>
    rw [associator_naturality_left]
  slice_lhs 9 10 =>
    rw [← whisker_exchange]
  slice_lhs 7 8 =>
    rw [associator_naturality_left]
  slice_lhs 8 9 =>
    rw [← tensorHom_def]
  simp

中文:
定理 mul_antipode₁
  条件: (A : C) [HopfObj A]
  证明: by
  slice_lhs 8 9 =>
    rw [associator_naturality_left]
  slice_lhs 9 10 =>
    rw [← whisker_exchange]
  slice_lhs 7 8 =>
    rw [associator_naturality_left]
  slice_lhs 8 9 =>
    rw [← tensorHom_def]
  simp

Depends on / 依赖: associator_naturality_left, slice_lhs, tensorHom_def, whisker_exchange
-/
theorem mul_antipode₁ (A : C) [HopfObj A] :
    (Δ[A] otimesₘ Δ[A]) ≫
      (α_ A A (A otimes A)).hom ≫
      A ◁ (α_ A A A).inv ≫
      A ◁ (β_ A A).hom ▷ A ≫
      (α_ A (A otimes A) A).inv ≫
      (α_ A A A).inv ▷ A ≫
      μ[A] ▷ A ▷ A ≫
      𝒮[A] ▷ A ▷ A ≫
      (α_ A A A).hom ≫
      A ◁ μ[A] ≫
      μ[A] =
    (ε[A] otimesₘ ε[A]) ≫ (fun_ (𝟙_ C)).hom ≫ η[A] := by
  slice_lhs 8 9 =>
    rw [associator_naturality_left]
  slice_lhs 9 10 =>
    rw [← whisker_exchange]
  slice_lhs 7 8 =>
    rw [associator_naturality_left]
  slice_lhs 8 9 =>
    rw [← tensorHom_def]
  simp


/--
theorem `mul_antipode₂` / 定理 `mul_antipode₂`

English:
theorem mul_antipode₂
  given: (A : C) [HopfObj A]
  proof: by
  slice_lhs 7 8 =>
    rw [associator_naturality_left]
  slice_lhs 8 9 =>
    rw [← whisker_exchange]
  slice_lhs 9 10 =>
    rw [← whisker_exchange]
  slice_lhs 11 12 =>
    rw [MonObj.mul_assoc_flip]
  slice_lhs 10 11 =>
    rw [associator_inv_naturality_left]
  slice_lhs 11 12 =>
    simp only [← comp_whiskerRight]
    rw [MonObj.mul_assoc]
    simp only [comp_whiskerRight]
  rw [tensorHom_def]
  rw [tensor_whiskerLeft _ _ (β_ A A).hom]
  rw [pentagon_inv_inv_hom_hom_inv_assoc]
  slice_lhs 7 8 =>
    rw [Iso.inv_hom_id]
  rw [Category.id_comp]
  slice_lhs 5 7 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.hexagon_forward]
    simp only [whiskerLeft_comp]
  simp only [tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc, pentagon_inv_inv_hom_inv_inv,
    whisker_assoc, MonObj.mul_assoc, whiskerLeft_inv_hom_assoc]
  slice_lhs 3 4 =>
    simp only [← whiskerLeft_comp]
    rw [BraidedCategory.braiding_naturality_right]
    simp only [whiskerLeft_comp]
  rw [tensorHom_def']
  simp only [whiskerLeft_comp]
  slice_lhs 5 6 =>
    simp only [← whiskerLeft_comp]
    rw [← associator_naturality_right]
    simp only [whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← whiskerLeft_comp]
    rw [← whisker_exchange]
    simp only [whiskerLeft_comp]
  slice_lhs 5 9 =>
    simp only [← whiskerLeft_comp]
    rw [associator_inv_naturality_middle_assoc]; rw [Iso.hom_inv_id_assoc]
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
    simp only [whiskerLeft_comp]
  slice_lhs 6 7 =>
    simp only [← whiskerLeft_comp]
    rw [MonObj.one_mul]
  slice_lhs 3 4 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.braiding_naturality_left]
    simp only [whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.braiding_naturality_right]
    simp only [whiskerLeft_comp]
  rw [← associator_naturality_middle_assoc]
  simp only [braiding_tensorUnit_right, whiskerLeft_comp]
  slice_lhs 6 7 =>
    simp only [← whiskerLeft_comp]
    rw [Iso.inv_hom_id]
  simp only [whiskerLeft_id, Category.id_comp]
  slice_lhs 5 6 =>
    rw [whiskerLeft_rightUnitor]; rw [Category.assoc]; rw [← rightUnitor_naturality]
  rw [associator_inv_naturality_right_assoc]; rw [Iso.hom_inv_id_assoc]
  slice_lhs 3 4 =>
    rw [whisker_exchange]
  slice_lhs 1 3 =>
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
  slice_lhs 2 3 =>
    rw [← whisker_exchange]
  slice_lhs 1 2 =>
    rw [← tensorHom_def]
  slice_lhs 2 3 =>
    rw [rightUnitor_naturality]
  monoidal

中文:
定理 mul_antipode₂
  条件: (A : C) [HopfObj A]
  证明: by
  slice_lhs 7 8 =>
    rw [associator_naturality_left]
  slice_lhs 8 9 =>
    rw [← whisker_exchange]
  slice_lhs 9 10 =>
    rw [← whisker_exchange]
  slice_lhs 11 12 =>
    rw [MonObj.mul_assoc_flip]
  slice_lhs 10 11 =>
    rw [associator_inv_naturality_left]
  slice_lhs 11 12 =>
    simp only [← comp_whiskerRight]
    rw [MonObj.mul_assoc]
    simp only [comp_whiskerRight]
  rw [tensorHom_def]
  rw [tensor_whiskerLeft _ _ (β_ A A).hom]
  rw [pentagon_inv_inv_hom_hom_inv_assoc]
  slice_lhs 7 8 =>
    rw [Iso.inv_hom_id]
  rw [Category.id_comp]
  slice_lhs 5 7 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.hexagon_forward]
    simp only [whiskerLeft_comp]
  simp only [tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc, pentagon_inv_inv_hom_inv_inv,
    whisker_assoc, MonObj.mul_assoc, whiskerLeft_inv_hom_assoc]
  slice_lhs 3 4 =>
    simp only [← whiskerLeft_comp]
    rw [BraidedCategory.braiding_naturality_right]
    simp only [whiskerLeft_comp]
  rw [tensorHom_def']
  simp only [whiskerLeft_comp]
  slice_lhs 5 6 =>
    simp only [← whiskerLeft_comp]
    rw [← associator_naturality_right]
    simp only [whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← whiskerLeft_comp]
    rw [← whisker_exchange]
    simp only [whiskerLeft_comp]
  slice_lhs 5 9 =>
    simp only [← whiskerLeft_comp]
    rw [associator_inv_naturality_middle_assoc]; rw [Iso.hom_inv_id_assoc]
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
    simp only [whiskerLeft_comp]
  slice_lhs 6 7 =>
    simp only [← whiskerLeft_comp]
    rw [MonObj.one_mul]
  slice_lhs 3 4 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.braiding_naturality_left]
    simp only [whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.braiding_naturality_right]
    simp only [whiskerLeft_comp]
  rw [← associator_naturality_middle_assoc]
  simp only [braiding_tensorUnit_right, whiskerLeft_comp]
  slice_lhs 6 7 =>
    simp only [← whiskerLeft_comp]
    rw [Iso.inv_hom_id]
  simp only [whiskerLeft_id, Category.id_comp]
  slice_lhs 5 6 =>
    rw [whiskerLeft_rightUnitor]; rw [Category.assoc]; rw [← rightUnitor_naturality]
  rw [associator_inv_naturality_right_assoc]; rw [Iso.hom_inv_id_assoc]
  slice_lhs 3 4 =>
    rw [whisker_exchange]
  slice_lhs 1 3 =>
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
  slice_lhs 2 3 =>
    rw [← whisker_exchange]
  slice_lhs 1 2 =>
    rw [← tensorHom_def]
  slice_lhs 2 3 =>
    rw [rightUnitor_naturality]
  monoidal

Depends on / 依赖: Category, Category.id_comp, Iso.inv_hom_id, MonObj, MonObj.mul_assoc, MonObj.mul_assoc_flip, associator_inv_naturality_left, associator_naturality_left, comp_whiskerRight, id_comp, inv_hom_id, mul_assoc, mul_assoc_flip, pentagon_inv_inv_hom_hom_inv_assoc, slice_lhs, tensorHom_def, tensor_whiskerLeft, whisker_exchange
-/
theorem mul_antipode₂ (A : C) [HopfObj A] :
    (Δ[A] otimesₘ Δ[A]) ≫
      (α_ A A (A otimes A)).hom ≫
      A ◁ (α_ A A A).inv ≫
      A ◁ (β_ A A).hom ▷ A ≫
      (α_ A (A otimes A) A).inv ≫
      (α_ A A A).inv ▷ A ≫
      μ[A] ▷ A ▷ A ≫
      (α_ A A A).hom ≫
      A ◁ (β_ A A).hom ≫
      A ◁ (𝒮[A] otimesₘ 𝒮[A]) ≫
      A ◁ μ[A] ≫ μ[A] =
    (ε[A] otimesₘ ε[A]) ≫ (fun_ (𝟙_ C)).hom ≫ η[A] := by
  slice_lhs 7 8 =>
    rw [associator_naturality_left]
  slice_lhs 8 9 =>
    rw [← whisker_exchange]
  slice_lhs 9 10 =>
    rw [← whisker_exchange]
  slice_lhs 11 12 =>
    rw [MonObj.mul_assoc_flip]
  slice_lhs 10 11 =>
    rw [associator_inv_naturality_left]
  slice_lhs 11 12 =>
    simp only [← comp_whiskerRight]
    rw [MonObj.mul_assoc]
    simp only [comp_whiskerRight]
  rw [tensorHom_def]
  rw [tensor_whiskerLeft _ _ (β_ A A).hom]
  rw [pentagon_inv_inv_hom_hom_inv_assoc]
  slice_lhs 7 8 =>
    rw [Iso.inv_hom_id]
  rw [Category.id_comp]
  slice_lhs 5 7 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.hexagon_forward]
    simp only [whiskerLeft_comp]
  simp only [tensor_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc, pentagon_inv_inv_hom_inv_inv,
    whisker_assoc, MonObj.mul_assoc, whiskerLeft_inv_hom_assoc]
  slice_lhs 3 4 =>
    simp only [← whiskerLeft_comp]
    rw [BraidedCategory.braiding_naturality_right]
    simp only [whiskerLeft_comp]
  rw [tensorHom_def']
  simp only [whiskerLeft_comp]
  slice_lhs 5 6 =>
    simp only [← whiskerLeft_comp]
    rw [← associator_naturality_right]
    simp only [whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← whiskerLeft_comp]
    rw [← whisker_exchange]
    simp only [whiskerLeft_comp]
  slice_lhs 5 9 =>
    simp only [← whiskerLeft_comp]
    rw [associator_inv_naturality_middle_assoc]; rw [Iso.hom_inv_id_assoc]
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
    simp only [whiskerLeft_comp]
  slice_lhs 6 7 =>
    simp only [← whiskerLeft_comp]
    rw [MonObj.one_mul]
  slice_lhs 3 4 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.braiding_naturality_left]
    simp only [whiskerLeft_comp]
  slice_lhs 4 5 =>
    simp only [← whiskerLeft_comp]
    rw [← BraidedCategory.braiding_naturality_right]
    simp only [whiskerLeft_comp]
  rw [← associator_naturality_middle_assoc]
  simp only [braiding_tensorUnit_right, whiskerLeft_comp]
  slice_lhs 6 7 =>
    simp only [← whiskerLeft_comp]
    rw [Iso.inv_hom_id]
  simp only [whiskerLeft_id, Category.id_comp]
  slice_lhs 5 6 =>
    rw [whiskerLeft_rightUnitor]; rw [Category.assoc]; rw [← rightUnitor_naturality]
  rw [associator_inv_naturality_right_assoc]; rw [Iso.hom_inv_id_assoc]
  slice_lhs 3 4 =>
    rw [whisker_exchange]
  slice_lhs 1 3 =>
    simp only [← comp_whiskerRight]
    rw [antipode_right]
    simp only [comp_whiskerRight]
  slice_lhs 2 3 =>
    rw [← whisker_exchange]
  slice_lhs 1 2 =>
    rw [← tensorHom_def]
  slice_lhs 2 3 =>
    rw [rightUnitor_naturality]
  monoidal

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mul_antipode` / 定理 `mul_antipode`

English:
theorem mul_antipode
  given: (A : C) [HopfObj A]
  proof: by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv (A otimes A) A)
    (a := μ[A])
  · -- Unfold the algebra structure in the convolution monoid,
    -- then `simp?, simp only [tensor_μ], simp?`.
    rw [Conv.mul_eq]; rw [Conv.one_eq]
    simp only [Comon.tensorObj_comul, whiskerRight_tensor, comp_whiskerRight, Category.assoc,
      Comon.tensorObj_counit]
    simp only [tensorμ]
    simp only [Category.assoc, pentagon_hom_inv_inv_inv_inv_assoc]
    exact mul_antipode₁ A
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [Comon.tensorObj_comul, whiskerRight_tensor,
      BraidedCategory.braiding_naturality_assoc, whiskerLeft_comp, Category.assoc,
      Comon.tensorObj_counit]
    simp only [tensorμ]
    simp only [Category.assoc, pentagon_hom_inv_inv_inv_inv_assoc]
    exact mul_antipode₂ A

中文:
定理 mul_antipode
  条件: (A : C) [HopfObj A]
  证明: by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv (A otimes A) A)
    (a := μ[A])
  · -- Unfold the algebra structure in the convolution monoid,
    -- then `simp?, simp only [tensor_μ], simp?`.
    rw [Conv.mul_eq]; rw [Conv.one_eq]
    simp only [Comon.tensorObj_comul, whiskerRight_tensor, comp_whiskerRight, Category.assoc,
      Comon.tensorObj_counit]
    simp only [tensorμ]
    simp only [Category.assoc, pentagon_hom_inv_inv_inv_inv_assoc]
    exact mul_antipode₁ A
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [Comon.tensorObj_comul, whiskerRight_tensor,
      BraidedCategory.braiding_naturality_assoc, whiskerLeft_comp, Category.assoc,
      Comon.tensorObj_counit]
    simp only [tensorμ]
    simp only [Category.assoc, pentagon_hom_inv_inv_inv_inv_assoc]
    exact mul_antipode₂ A
-/
theorem mul_antipode (A : C) [HopfObj A] :
    μ[A] ≫ 𝒮[A] = (𝒮[A] otimesₘ 𝒮[A]) ≫ (β_ _ _).hom ≫ μ[A] := by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv (A otimes A) A)
    (a := μ[A])
  · -- Unfold the algebra structure in the convolution monoid,
    -- then `simp?, simp only [tensor_μ], simp?`.
    rw [Conv.mul_eq]; rw [Conv.one_eq]
    simp only [Comon.tensorObj_comul, whiskerRight_tensor, comp_whiskerRight, Category.assoc,
      Comon.tensorObj_counit]
    simp only [tensorμ]
    simp only [Category.assoc, pentagon_hom_inv_inv_inv_inv_assoc]
    exact mul_antipode₁ A
  · rw [Conv.mul_eq, Conv.one_eq]
    simp only [Comon.tensorObj_comul, whiskerRight_tensor,
      BraidedCategory.braiding_naturality_assoc, whiskerLeft_comp, Category.assoc,
      Comon.tensorObj_counit]
    simp only [tensorμ]
    simp only [Category.assoc, pentagon_hom_inv_inv_inv_inv_assoc]
    exact mul_antipode₂ A

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `antipode_antipode` / 定理 `antipode_antipode`

English:
theorem antipode_antipode
  given: (A : C) [HopfObj A] (comm : (β_ _ _).hom ≫ μ[A] = μ[A])
  proof: by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv A A)
    (a := 𝒮[A])
  · -- Unfold the algebra structure in the convolution monoid,
    -- then `simp?`.
    rw [Conv.mul_eq]; rw [Conv.one_eq]
    simp only [comp_whiskerRight, Category.assoc]
    rw [← comm]; rw [← tensorHom_def_assoc]; rw [← mul_antipode]
    simp
  · rw [Conv.mul_eq, Conv.one_eq]
    simp

中文:
定理 antipode_antipode
  条件: (A : C) [HopfObj A] (comm : (β_ _ _).hom ≫ μ[A] = μ[A])
  证明: by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv A A)
    (a := 𝒮[A])
  · -- Unfold the algebra structure in the convolution monoid,
    -- then `simp?`.
    rw [Conv.mul_eq]; rw [Conv.one_eq]
    simp only [comp_whiskerRight, Category.assoc]
    rw [← comm]; rw [← tensorHom_def_assoc]; rw [← mul_antipode]
    simp
  · rw [Conv.mul_eq, Conv.one_eq]
    simp
-/
theorem antipode_antipode (A : C) [HopfObj A] (comm : (β_ _ _).hom ≫ μ[A] = μ[A]) :
    𝒮[A] ≫ 𝒮[A] = 𝟙 A := by
  -- Again, it is a "left inverse equals right inverse" argument in the convolution monoid.
  apply left_inv_eq_right_inv
    (M := Conv A A)
    (a := 𝒮[A])
  · -- Unfold the algebra structure in the convolution monoid,
    -- then `simp?`.
    rw [Conv.mul_eq]; rw [Conv.one_eq]
    simp only [comp_whiskerRight, Category.assoc]
    rw [← comm]; rw [← tensorHom_def_assoc]; rw [← mul_antipode]
    simp
  · rw [Conv.mul_eq, Conv.one_eq]
    simp

end HopfObj

end CategoryTheory
