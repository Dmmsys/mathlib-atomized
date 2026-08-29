/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.End
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Distributive monoidal categories

## Main definitions

A monoidal category `C` with binary coproducts is left distributive if the left tensor product
preserves binary coproducts. This means that, for all objects `X`, `Y`, and `Z` in `C`,
the cogap map `(X ⊗ Y) ⨿ (X ⊗ Z) ⟶ X ⊗ (Y ⨿ Z)` can be promoted to an isomorphism. We refer to
this isomorphism as the left distributivity isomorphism.

A monoidal category `C` with binary coproducts is right distributive if the right tensor product
preserves binary coproducts. This means that, for all objects `X`, `Y`, and `Z` in `C`,
the cogap map `(Y ⊗ X) ⨿ (Z ⊗ X) ⟶ (Y ⨿ Z) ⊗ X` can be promoted to an isomorphism. We refer to
this isomorphism as the right distributivity isomorphism.

A distributive monoidal category is a monoidal category that is both left and right distributive.

## Main results

- A symmetric monoidal category is left distributive if and only if it is right distributive.

- A closed monoidal category is left distributive.

- For a category `C` the category of endofunctors `C ⥤ C` is left distributive (but almost
  never right distributive). The left distributivity is tantamount to the fact that the coproduct
  in the functor categories is computed pointwise.

- We show that any preadditive monoidal category with coproducts is distributive. This includes the
  examples of abelian groups, R-modules, and vector bundles.

## TODO

Show that a distributive monoidal category whose unit is weakly terminal is finitary distributive.

Show that the category of pointed types with the monoidal structure given by the smash product of
pointed types and the coproduct given by the wedge sum is distributive.

## References

* [Hans-Joachim Baues, Mamuka Jibladze, Andy Tonks, Cohomology of
  monoids in monoidal categories, in: Operads: Proceedings of Renaissance
  Conferences, Contemporary Mathematics 202, AMS (1997) 137-166][MR1268290]

-/

@[expose] public section

universe v v₂ u u₂

noncomputable section

namespace CategoryTheory

open Category MonoidalCategory Limits Iso

/--
Definition of `IsMonoidalLeftDistrib` / `IsMonoidalLeftDistrib` 的定义

English:
class IsMonoidalLeftDistrib
  parameters: (C : Type u) [Category.{v} C]
  axioms and operations (1):
    - preservesBinaryCoproducts_tensorLeft((X : C)) : PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft X)  [default: by infer_instance]

中文:
类 IsMonoidalLeftDistrib
  参数: (C : 类型u) [Category.{v} C]
  公理与运算 (1 个):
    - preservesBinaryCoproducts_tensorLeft((X : C)) : PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft X)  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsMonoidalLeftDistrib (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasBinaryCoproducts C] : Prop where
  preservesBinaryCoproducts_tensorLeft (X : C) :
    PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft X) := by infer_instance

/--
Definition of `IsMonoidalRightDistrib` / `IsMonoidalRightDistrib` 的定义

English:
class IsMonoidalRightDistrib
  parameters: (C : Type u) [Category.{v} C]
  axioms and operations (1):
    - preservesBinaryCoproducts_tensorRight((X : C)) : PreservesColimitsOfShape (Discrete WalkingPair) (tensorRight X)  [default: by infer_instance]

中文:
类 IsMonoidalRightDistrib
  参数: (C : 类型u) [Category.{v} C]
  公理与运算 (1 个):
    - preservesBinaryCoproducts_tensorRight((X : C)) : PreservesColimitsOfShape (Discrete WalkingPair) (tensorRight X)  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsMonoidalRightDistrib (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasBinaryCoproducts C] : Prop where
  preservesBinaryCoproducts_tensorRight (X : C) :
    PreservesColimitsOfShape (Discrete WalkingPair) (tensorRight X) := by infer_instance

/--
Definition of `IsMonoidalDistrib` / `IsMonoidalDistrib` 的定义

English:
class IsMonoidalDistrib
  parameters: (C : Type u) [Category.{v} C]
  (no additional axioms)

中文:
类 IsMonoidalDistrib
  参数: (C : 类型u) [Category.{v} C]
  (无附加公理)
-/
class IsMonoidalDistrib (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasBinaryCoproducts C] extends
  IsMonoidalLeftDistrib C, IsMonoidalRightDistrib C

variable {C} [Category.{v} C] [MonoidalCategory C] [HasBinaryCoproducts C]

section IsMonoidalLeftDistrib

attribute [instance] IsMonoidalLeftDistrib.preservesBinaryCoproducts_tensorLeft

/--
Definition of `leftDistrib` / `leftDistrib` 的定义

English:
definition leftDistrib
  signature: [IsMonoidalLeftDistrib C] (X Y Z : C)
  body: PreservesColimitPair.iso (tensorLeft X) Y Z

中文:
定义 leftDistrib
  签名: [IsMonoidalLeftDistrib C] (X Y Z : C)
  定义体: PreservesColimitPair.iso (tensorLeft X) Y Z

Depends on / 依赖: PreservesColimitPair, PreservesColimitPair.iso, tensorLeft
-/
def leftDistrib [IsMonoidalLeftDistrib C] (X Y Z : C) :
    (X otimes Y) ⨿ (X otimes Z) ≅ X otimes (Y ⨿ Z) :=
  PreservesColimitPair.iso (tensorLeft X) Y Z

end IsMonoidalLeftDistrib

namespace Distributive

/-- Notation for the forward direction morphism of the canonical left distributivity isomorphism -/
scoped notation "∂L" => leftDistrib

end Distributive

open Distributive

/--
lemma `IsMonoidalLeftDistrib.of_isIso_coprodComparisonTensorLeft` / 引理 `IsMonoidalLeftDistrib.of_isIso_coprodComparisonTensorLeft`

English:
lemma IsMonoidalLeftDistrib.of_isIso_coprodComparisonTensorLeft
  proof: preservesBinaryCoproducts_of_isIso_coprodComparison (tensorLeft X)

中文:
引理 IsMonoidalLeftDistrib.of_isIso_coprodComparisonTensorLeft
  证明: preservesBinaryCoproducts_of_isIso_coprodComparison (tensorLeft X)

Depends on / 依赖: preservesBinaryCoproducts_of_isIso_coprodComparison, tensorLeft
-/
lemma IsMonoidalLeftDistrib.of_isIso_coprodComparisonTensorLeft
    [i : forall {X Y Z : C}, IsIso (coprodComparison (tensorLeft X) Y Z)] : IsMonoidalLeftDistrib C where
  preservesBinaryCoproducts_tensorLeft X :=
    preservesBinaryCoproducts_of_isIso_coprodComparison (tensorLeft X)

/--
lemma `leftDistrib_hom` / 引理 `leftDistrib_hom`

English:
lemma leftDistrib_hom
  given: [IsMonoidalLeftDistrib C] {X Y Z : C}
  proof: by rfl

@[reassoc (attr := simp)]

中文:
引理 leftDistrib_hom
  条件: [IsMonoidalLeftDistrib C] {X Y Z : C}
  证明: by rfl

@[reassoc (attr := simp)]
-/
lemma leftDistrib_hom [IsMonoidalLeftDistrib C] {X Y Z : C} :
    (∂L X Y Z).hom = coprod.desc (_ ◁ coprod.inl) (_ ◁ coprod.inr) := by rfl

@[reassoc (attr := simp)]
/--
lemma `coprod_inl_leftDistrib_hom` / 引理 `coprod_inl_leftDistrib_hom`

English:
lemma coprod_inl_leftDistrib_hom
  given: [IsMonoidalLeftDistrib C] {X Y Z : C}
  proof: by
  rw [leftDistrib_hom]; rw [coprod.inl_desc]

@[reassoc (attr := simp)]

中文:
引理 coprod_inl_leftDistrib_hom
  条件: [IsMonoidalLeftDistrib C] {X Y Z : C}
  证明: by
  rw [leftDistrib_hom]; rw [coprod.inl_desc]

@[reassoc (attr := simp)]

Depends on / 依赖: coprod, coprod.inl_desc, inl_desc, leftDistrib_hom
-/
lemma coprod_inl_leftDistrib_hom [IsMonoidalLeftDistrib C] {X Y Z : C} :
    coprod.inl ≫ (∂L X Y Z).hom = X ◁ coprod.inl := by
  rw [leftDistrib_hom]; rw [coprod.inl_desc]

@[reassoc (attr := simp)]
/--
lemma `coprod_inr_leftDistrib_hom` / 引理 `coprod_inr_leftDistrib_hom`

English:
lemma coprod_inr_leftDistrib_hom
  given: [IsMonoidalLeftDistrib C] {X Y Z : C}
  proof: by
  rw [leftDistrib_hom]; rw [coprod.inr_desc]

中文:
引理 coprod_inr_leftDistrib_hom
  条件: [IsMonoidalLeftDistrib C] {X Y Z : C}
  证明: by
  rw [leftDistrib_hom]; rw [coprod.inr_desc]

Depends on / 依赖: coprod, coprod.inr_desc, inr_desc, leftDistrib_hom
-/
lemma coprod_inr_leftDistrib_hom [IsMonoidalLeftDistrib C] {X Y Z : C} :
    coprod.inr ≫ (∂L X Y Z).hom = X ◁ coprod.inr := by
  rw [leftDistrib_hom]; rw [coprod.inr_desc]

/-- The composite of `(X ◁ coprod.inl) : X ⊗ Y ⟶ X ⊗ (Y ⨿ Z)` and
`(∂L X Y Z).inv : X ⊗ (Y ⨿ Z) ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`
is equal to the left coprojection `coprod.inl : X ⊗ Y ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`. -/
@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_coprod_inl_leftDistrib_inv` / 引理 `whiskerLeft_coprod_inl_leftDistrib_inv`

English:
lemma whiskerLeft_coprod_inl_leftDistrib_inv
  given: [IsMonoidalLeftDistrib C] {X Y Z : C}
  proof: by
  apply (cancel_iso_hom_right _ _ (∂L X Y Z)).mp
  rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [coprod_inl_leftDistrib_hom]

中文:
引理 whiskerLeft_coprod_inl_leftDistrib_inv
  条件: [IsMonoidalLeftDistrib C] {X Y Z : C}
  证明: by
  apply (cancel_iso_hom_right _ _ (∂L X Y Z)).mp
  rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [coprod_inl_leftDistrib_hom]

Depends on / 依赖: Iso.inv_hom_id, cancel_iso_hom_right, comp_id, coprod_inl_leftDistrib_hom, inv_hom_id
-/
lemma whiskerLeft_coprod_inl_leftDistrib_inv [IsMonoidalLeftDistrib C] {X Y Z : C} :
    (X ◁ coprod.inl) ≫ (∂L X Y Z).inv = coprod.inl := by
  apply (cancel_iso_hom_right _ _ (∂L X Y Z)).mp
  rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [coprod_inl_leftDistrib_hom]

/-- The composite of `(X ◁ coprod.inr) : X ⊗ Z ⟶ X ⊗ (Y ⨿ Z)` and
`(∂L X Y Z).inv : X ⊗ (Y ⨿ Z) ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`
is equal to the right coprojection `coprod.inr : X ⊗ Z ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`. -/
@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_coprod_inr_leftDistrib_inv` / 引理 `whiskerLeft_coprod_inr_leftDistrib_inv`

English:
lemma whiskerLeft_coprod_inr_leftDistrib_inv
  given: [IsMonoidalLeftDistrib C] {X Y Z : C}
  proof: by
  apply (cancel_iso_hom_right _ _ (∂L X Y Z)).mp
  rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [coprod_inr_leftDistrib_hom]

中文:
引理 whiskerLeft_coprod_inr_leftDistrib_inv
  条件: [IsMonoidalLeftDistrib C] {X Y Z : C}
  证明: by
  apply (cancel_iso_hom_right _ _ (∂L X Y Z)).mp
  rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [coprod_inr_leftDistrib_hom]

Depends on / 依赖: Iso.inv_hom_id, cancel_iso_hom_right, comp_id, coprod_inr_leftDistrib_hom, inv_hom_id
-/
lemma whiskerLeft_coprod_inr_leftDistrib_inv [IsMonoidalLeftDistrib C] {X Y Z : C} :
    (X ◁ coprod.inr) ≫ (∂L X Y Z).inv = coprod.inr := by
  apply (cancel_iso_hom_right _ _ (∂L X Y Z)).mp
  rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [coprod_inr_leftDistrib_hom]

section IsMonoidalRightDistrib

attribute [instance] IsMonoidalRightDistrib.preservesBinaryCoproducts_tensorRight

/--
Definition of `rightDistrib` / `rightDistrib` 的定义

English:
definition rightDistrib
  signature: [IsMonoidalRightDistrib C] (X Y Z : C)
  body: PreservesColimitPair.iso (tensorRight X) Y Z

中文:
定义 rightDistrib
  签名: [IsMonoidalRightDistrib C] (X Y Z : C)
  定义体: PreservesColimitPair.iso (tensorRight X) Y Z

Depends on / 依赖: PreservesColimitPair, PreservesColimitPair.iso, tensorRight
-/
def rightDistrib [IsMonoidalRightDistrib C] (X Y Z : C) : (Y otimes X) ⨿ (Z otimes X) ≅ (Y ⨿ Z) otimes X :=
  PreservesColimitPair.iso (tensorRight X) Y Z

end IsMonoidalRightDistrib

namespace Distributive

/-- Notation for the forward direction morphism of the canonical right distributivity isomorphism -/
notation "∂R" => rightDistrib

end Distributive

/--
lemma `IsMonoidalRightDistrib.of_isIso_coprodComparisonTensorRight` / 引理 `IsMonoidalRightDistrib.of_isIso_coprodComparisonTensorRight`

English:
lemma IsMonoidalRightDistrib.of_isIso_coprodComparisonTensorRight
  proof: .preservesColimit⟩ ⟨preservesBinaryCoproducts_of_isIso_coprodComparison _

中文:
引理 IsMonoidalRightDistrib.of_isIso_coprodComparisonTensorRight
  证明: .preservesColimit⟩ ⟨preservesBinaryCoproducts_of_isIso_coprodComparison _

Depends on / 依赖: preservesBinaryCoproducts_of_isIso_coprodComparison, preservesColimit
-/
lemma IsMonoidalRightDistrib.of_isIso_coprodComparisonTensorRight
    [i : forall {X Y Z : C}, IsIso (coprodComparison (tensorRight X) Y Z)] :
    IsMonoidalRightDistrib C where
  preservesBinaryCoproducts_tensorRight _ :=
.preservesColimit⟩ ⟨preservesBinaryCoproducts_of_isIso_coprodComparison _

/--
lemma `rightDistrib_hom` / 引理 `rightDistrib_hom`

English:
lemma rightDistrib_hom
  given: [IsMonoidalRightDistrib C] {X Y Z : C}
  proof: by rfl

@[reassoc (attr := simp)]

中文:
引理 rightDistrib_hom
  条件: [IsMonoidalRightDistrib C] {X Y Z : C}
  证明: by rfl

@[reassoc (attr := simp)]
-/
lemma rightDistrib_hom [IsMonoidalRightDistrib C] {X Y Z : C} :
    (∂R X Y Z).hom = coprod.desc (coprod.inl ▷ _) (coprod.inr ▷ _) := by rfl

@[reassoc (attr := simp)]
/--
lemma `coprod_inl_rightDistrib_hom` / 引理 `coprod_inl_rightDistrib_hom`

English:
lemma coprod_inl_rightDistrib_hom
  given: [IsMonoidalRightDistrib C] {X Y Z : C}
  proof: by
  rw [rightDistrib_hom]; rw [coprod.inl_desc]

@[reassoc (attr := simp)]

中文:
引理 coprod_inl_rightDistrib_hom
  条件: [IsMonoidalRightDistrib C] {X Y Z : C}
  证明: by
  rw [rightDistrib_hom]; rw [coprod.inl_desc]

@[reassoc (attr := simp)]

Depends on / 依赖: coprod, coprod.inl_desc, inl_desc, rightDistrib_hom
-/
lemma coprod_inl_rightDistrib_hom [IsMonoidalRightDistrib C] {X Y Z : C} :
    coprod.inl ≫ (∂R X Y Z).hom = coprod.inl ▷ X := by
  rw [rightDistrib_hom]; rw [coprod.inl_desc]

@[reassoc (attr := simp)]
/--
lemma `coprod_inr_rightDistrib_hom` / 引理 `coprod_inr_rightDistrib_hom`

English:
lemma coprod_inr_rightDistrib_hom
  given: [IsMonoidalRightDistrib C] {X Y Z : C}
  proof: by
  rw [rightDistrib_hom]; rw [coprod.inr_desc]

中文:
引理 coprod_inr_rightDistrib_hom
  条件: [IsMonoidalRightDistrib C] {X Y Z : C}
  证明: by
  rw [rightDistrib_hom]; rw [coprod.inr_desc]

Depends on / 依赖: coprod, coprod.inr_desc, inr_desc, rightDistrib_hom
-/
lemma coprod_inr_rightDistrib_hom [IsMonoidalRightDistrib C] {X Y Z : C} :
    coprod.inr ≫ (∂R X Y Z).hom = coprod.inr ▷ X := by
  rw [rightDistrib_hom]; rw [coprod.inr_desc]

/-- The composite of `(coprod.inl ▷ X) : Y ⊗ X ⟶ (Y ⨿ Z) ⊗ X` and
`(∂R X Y Z).inv : (Y ⨿ Z) ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)` is equal to the left coprojection
`coprod.inl : Y ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)`. -/
@[reassoc (attr := simp)]
/--
lemma `whiskerRight_coprod_inl_rightDistrib_inv` / 引理 `whiskerRight_coprod_inl_rightDistrib_inv`

English:
lemma whiskerRight_coprod_inl_rightDistrib_inv
  given: [IsMonoidalRightDistrib C] {X Y Z : C}
  proof: by
  apply (cancel_iso_hom_right _ _ (∂R X Y Z)).mp
  rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [coprod_inl_rightDistrib_hom]

中文:
引理 whiskerRight_coprod_inl_rightDistrib_inv
  条件: [IsMonoidalRightDistrib C] {X Y Z : C}
  证明: by
  apply (cancel_iso_hom_right _ _ (∂R X Y Z)).mp
  rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [coprod_inl_rightDistrib_hom]

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, cancel_iso_hom_right, colimit, colimit.post, colimitObjIsoColimitCompEvaluation, comp_id, coprod_inl_rightDistrib_hom, coyoneda, coyoneda.obj, inv_hom_id, inv_hom_id_assoc, preservesColimit_of_isIso_post, yoneda, yoneda.obj, yonedaYonedaColimit, yonedaYonedaColimit_app_inv
-/
lemma whiskerRight_coprod_inl_rightDistrib_inv [IsMonoidalRightDistrib C] {X Y Z : C} :
    (coprod.inl ▷ X) ≫ (∂R X Y Z).inv = coprod.inl := by
  apply (cancel_iso_hom_right _ _ (∂R X Y Z)).mp
  rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [coprod_inl_rightDistrib_hom]

/-- The composite of `(coprod.inr ▷ X) : Z ⊗ X ⟶ (Y ⨿ Z) ⊗ X` and
`(∂R X Y Z).inv : (Y ⨿ Z) ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)` is equal to the right coprojection
`coprod.inr : Z ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)`. -/
@[reassoc (attr := simp)]
/--
lemma `whiskerRight_coprod_inr_rightDistrib_inv` / 引理 `whiskerRight_coprod_inr_rightDistrib_inv`

English:
lemma whiskerRight_coprod_inr_rightDistrib_inv
  given: [IsMonoidalRightDistrib C] {X Y Z : C}
  proof: by
  apply (cancel_iso_hom_right _ _ (∂R X Y Z)).mp
  rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [coprod_inr_rightDistrib_hom]

中文:
引理 whiskerRight_coprod_inr_rightDistrib_inv
  条件: [IsMonoidalRightDistrib C] {X Y Z : C}
  证明: by
  apply (cancel_iso_hom_right _ _ (∂R X Y Z)).mp
  rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [coprod_inr_rightDistrib_hom]

Depends on / 依赖: Iso.inv_hom_id, cancel_iso_hom_right, comp_id, coprod_inr_rightDistrib_hom, inv_hom_id
-/
lemma whiskerRight_coprod_inr_rightDistrib_inv [IsMonoidalRightDistrib C] {X Y Z : C} :
    (coprod.inr ▷ X) ≫ (∂R X Y Z).inv = coprod.inr := by
  apply (cancel_iso_hom_right _ _ (∂R X Y Z)).mp
  rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [coprod_inr_rightDistrib_hom]

set_option backward.defeqAttrib.useBackward true in
/-- In a symmetric monoidal category, the left distributivity is equal to
the right distributivity up to braiding isomorphisms. -/
@[simp]
/--
lemma `coprodComparison_tensorLeft_braiding_hom` / 引理 `coprodComparison_tensorLeft_braiding_hom`

English:
lemma coprodComparison_tensorLeft_braiding_hom
  given: [BraidedCategory C] {X Y Z : C}
  proof: by
  simp [coprodComparison]

中文:
引理 coprodComparison_tensorLeft_braiding_hom
  条件: [BraidedCategory C] {X Y Z : C}
  证明: by
  simp [coprodComparison]

Depends on / 依赖: coprodComparison, createsLimitsOfShapeOfCreatesFiniteLimits
-/
lemma coprodComparison_tensorLeft_braiding_hom [BraidedCategory C] {X Y Z : C} :
    (coprodComparison (tensorLeft X) Y Z) ≫ (β_ X (Y ⨿ Z)).hom =
    (coprod.map (β_ X Y).hom (β_ X Z).hom) ≫ (coprodComparison (tensorRight X) Y Z) := by
  simp [coprodComparison]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- In a symmetric monoidal category, the right distributivity is equal to
the left distributivity up to braiding isomorphisms. -/
@[simp]
/--
lemma `coprodComparison_tensorRight_braiding_hom` / 引理 `coprodComparison_tensorRight_braiding_hom`

English:
lemma coprodComparison_tensorRight_braiding_hom
  given: [SymmetricCategory C] {X Y Z : C}
  proof: by
  simp [coprodComparison]

中文:
引理 coprodComparison_tensorRight_braiding_hom
  条件: [SymmetricCategory C] {X Y Z : C}
  证明: by
  simp [coprodComparison]

Depends on / 依赖: coprodComparison
-/
lemma coprodComparison_tensorRight_braiding_hom [SymmetricCategory C] {X Y Z : C} :
    (coprodComparison (tensorRight X) Y Z) ≫ (β_ (Y ⨿ Z) X).hom =
    (coprod.map (β_ Y X).hom (β_ Z X).hom) ≫ (coprodComparison (tensorLeft X) Y Z) := by
  simp [coprodComparison]

/--
lemma `SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib` / 引理 `SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib`

English:
lemma SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib
  proof: preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

中文:
引理 SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib
  证明: preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

Depends on / 依赖: BraidedCategory, BraidedCategory.tensorLeftIsoTensorRight, CreatesLimitsOfSize0, CreatesLimitsOfSize0.createsFiniteLimits, createsFiniteLimits, preservesColimitsOfShape_of_natIso, tensorLeftIsoTensorRight
-/
lemma SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib
    [SymmetricCategory C] [IsMonoidalLeftDistrib C] : IsMonoidalDistrib C where
      preservesBinaryCoproducts_tensorRight X :=
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- The right distributivity isomorphism of the a left distributive symmetric monoidal category
is given by `(β_ (Y ⨿ Z) X).hom ≫ (∂L X Y Z).inv ≫ (coprod.map (β_ X Y).hom (β_ X Z).hom)`. -/
@[simp]
/--
lemma `SymmetricCategory.rightDistrib_of_leftDistrib` / 引理 `SymmetricCategory.rightDistrib_of_leftDistrib`

English:
lemma SymmetricCategory.rightDistrib_of_leftDistrib
  proof: by
  ext <;> simp [leftDistrib_hom, rightDistrib_hom]

中文:
引理 SymmetricCategory.rightDistrib_of_leftDistrib
  证明: by
  ext <;> simp [leftDistrib_hom, rightDistrib_hom]

Depends on / 依赖: CreatesLimits, CreatesLimits.createsFiniteLimits, createsFiniteLimits, leftDistrib_hom, rightDistrib_hom
-/
lemma SymmetricCategory.rightDistrib_of_leftDistrib
    [SymmetricCategory C] [IsMonoidalDistrib C] {X Y Z : C} :
    ∂R X Y Z = (coprod.mapIso (β_ Y X) (β_ Z X)) ≪≫ (∂L X Y Z) ≪≫ (β_ X (Y ⨿ Z)) := by
  ext <;> simp [leftDistrib_hom, rightDistrib_hom]

/--
Instance `MonoidalClosed.isMonoidalLeftDistrib` / 实例 `MonoidalClosed.isMonoidalLeftDistrib`

English:
instance MonoidalClosed.isMonoidalLeftDistrib
  signature: [MonoidalClosed C]
  body: by
    infer_instance

中文:
实例 MonoidalClosed.isMonoidalLeftDistrib
  签名: [MonoidalClosed C]
  定义体: by
    infer_instance

Depends on / 依赖: infer_instance
-/
instance MonoidalClosed.isMonoidalLeftDistrib [MonoidalClosed C] :
    IsMonoidalLeftDistrib C where
  preservesBinaryCoproducts_tensorLeft X := by
    infer_instance

/--
Instance `isMonoidalDistrib.of_symmetric_monoidal_closed` / 实例 `isMonoidalDistrib.of_symmetric_monoidal_closed`

English:
instance isMonoidalDistrib.of_symmetric_monoidal_closed
  signature: [SymmetricCategory C] [MonoidalClosed C]
  body: by
  apply SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib

中文:
实例 isMonoidalDistrib.of_symmetric_monoidal_closed
  签名: [SymmetricCategory C] [MonoidalClosed C]
  定义体: by
  apply SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib

Depends on / 依赖: SymmetricCategory, SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib, isMonoidalDistrib_of_isMonoidalLeftDistrib
-/
instance isMonoidalDistrib.of_symmetric_monoidal_closed [SymmetricCategory C] [MonoidalClosed C] :
    IsMonoidalDistrib C := by
  apply SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib

set_option backward.isDefEq.respectTransparency false in
/--
lemma `MonoidalClosed.leftDistrib_inv` / 引理 `MonoidalClosed.leftDistrib_inv`

English:
lemma MonoidalClosed.leftDistrib_inv
  given: [MonoidalClosed C] {X Y Z : C}
  proof: by
  rw [← curry_eq_iff]
  ext <;> simp [← curry_natural_left]

中文:
引理 MonoidalClosed.leftDistrib_inv
  条件: [MonoidalClosed C] {X Y Z : C}
  证明: by
  rw [← curry_eq_iff]
  ext <;> simp [← curry_natural_left]

Depends on / 依赖: curry_eq_iff, curry_natural_left
-/
lemma MonoidalClosed.leftDistrib_inv [MonoidalClosed C] {X Y Z : C} :
    (leftDistrib X Y Z).inv =
      uncurry (coprod.desc (curry coprod.inl) (curry coprod.inr)) := by
  rw [← curry_eq_iff]
  ext <;> simp [← curry_natural_left]

section Endofunctors

attribute [local instance] endofunctorMonoidalCategory

/--
Instance `isMonoidalLeftDistrib.of_endofunctors` / 实例 `isMonoidalLeftDistrib.of_endofunctors`

English:
instance isMonoidalLeftDistrib.of_endofunctors
  signature: : IsMonoidalLeftDistrib (C ⥤ C) where
  body: inferInstanceAs (PreservesColimitsOfShape _ ((Functor.whiskeringLeft C C C).obj F))

中文:
实例 isMonoidalLeftDistrib.of_endofunctors
  签名: : IsMonoidalLeftDistrib (C ⥤ C) where
  定义体: inferInstanceAs (PreservesColimitsOfShape _ ((Functor.whiskeringLeft C C C).obj F))

Depends on / 依赖: Functor, Functor.whiskeringLeft, PreservesColimitsOfShape, whiskeringLeft
-/
instance isMonoidalLeftDistrib.of_endofunctors : IsMonoidalLeftDistrib (C ⥤ C) where
  preservesBinaryCoproducts_tensorLeft F :=
    inferInstanceAs (PreservesColimitsOfShape _ ((Functor.whiskeringLeft C C C).obj F))

end Endofunctors

section MonoidalPreadditive

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
  preservesBinaryCoproducts_of_preservesBinaryBiproducts

/--
Instance `IsMonoidalDistrib.of_MonoidalPreadditive_with_binary_coproducts` / 实例 `IsMonoidalDistrib.of_MonoidalPreadditive_with_binary_coproducts`

English:
instance IsMonoidalDistrib.of_MonoidalPreadditive_with_binary_coproducts
  signature: [Preadditive C]

中文:
实例 IsMonoidalDistrib.of_MonoidalPreadditive_with_binary_coproducts
  签名: [Preadditive C]

Depends on / 依赖: preservesFiniteLimits_of_createsFiniteLimits_and_hasFiniteLimits
-/
instance IsMonoidalDistrib.of_MonoidalPreadditive_with_binary_coproducts [Preadditive C]
    [MonoidalPreadditive C] :
    IsMonoidalDistrib C where

end MonoidalPreadditive

end CategoryTheory
