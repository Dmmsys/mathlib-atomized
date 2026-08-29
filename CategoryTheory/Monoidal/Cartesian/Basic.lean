/-
Copyright (c) 2019 Kim Morrison, Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Simon Hudon, Adam Topaz, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Categories with chosen finite products

We introduce a class, `CartesianMonoidalCategory`, which bundles explicit choices
for a terminal object and binary products in a category `C`.
This is primarily useful for categories which have finite products with good
definitional properties, such as the category of types.

For better defeqs, we also extend `MonoidalCategory`.

## Implementation notes

For Cartesian monoidal categories, the oplax-monoidal/monoidal/braided structure of a functor `F`
preserving finite products is uniquely determined. See the `ofChosenFiniteProducts` declarations.

We however develop the theory for any `F.OplaxMonoidal`/`F.Monoidal`/`F.Braided` instance instead of
requiring it to be the `ofChosenFiniteProducts` one. This is to avoid diamonds: Consider
e.g. `𝟭 C` and `F ⋙ G`.

In applications requiring a finite-product-preserving functor to be
oplax-monoidal/monoidal/braided, avoid `attribute [local instance] ofChosenFiniteProducts` but
instead turn on the corresponding `ofChosenFiniteProducts` declaration for that functor only.

## Projects

- Construct an instance of chosen finite products in the category of affine scheme, using
  the tensor product.
- Construct chosen finite products in other categories appearing "in nature".

-/

@[expose] public section

namespace CategoryTheory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

open MonoidalCategory Limits

/--
Definition of `SemiCartesianMonoidalCategory` / `SemiCartesianMonoidalCategory` 的定义

English:
class SemiCartesianMonoidalCategory
  parameters: (C : Type u) [Category.{v} C]
  extends: MonoidalCategory C
  axioms and operations (5):
    - isTerminalTensorUnit : IsTerminal (𝟙_ C)
    - fst((X Y : C)) : X otimes Y ⟶ X
    - snd((X Y : C)) : X otimes Y ⟶ Y
    - fst_def((X Y : C)) : fst X Y = X ◁ isTerminalTensorUnit.from Y ≫ (ρ_ X).hom  [default: by cat_disch]
    - snd_def((X Y : C)) : snd X Y = isTerminalTensorUnit.from X ▷ Y ≫ (fun_ Y).hom  [default: by cat_disch]

中文:
类 SemiCartesianMonoidalCategory
  参数: (C : 类型u) [Category.{v} C]
  继承: MonoidalCategory C
  公理与运算 (5 个):
    - isTerminalTensorUnit : IsTerminal (𝟙_ C)
    - fst((X Y : C)) : X otimes Y ⟶ X
    - snd((X Y : C)) : X otimes Y ⟶ Y
    - fst_def((X Y : C)) : fst X Y = X ◁ isTerminalTensorUnit.from Y ≫ (ρ_ X).hom  [默认: by cat_disch]
    - snd_def((X Y : C)) : snd X Y = isTerminalTensorUnit.from X ▷ Y ≫ (fun_ Y).hom  [默认: by cat_disch]

Depends on / 依赖: cat_disch, fun_, isTerminalTensorUnit, isTerminalTensorUnit.from, snd_def
-/
class SemiCartesianMonoidalCategory (C : Type u) [Category.{v} C] extends MonoidalCategory C where
  /-- The tensor unit is a terminal object. -/
  isTerminalTensorUnit : IsTerminal (𝟙_ C)
  /-- The first projection from the product. -/
  fst (X Y : C) : X otimes Y ⟶ X
  /-- The second projection from the product. -/
  snd (X Y : C) : X otimes Y ⟶ Y
  fst_def (X Y : C) : fst X Y = X ◁ isTerminalTensorUnit.from Y ≫ (ρ_ X).hom := by cat_disch
  snd_def (X Y : C) : snd X Y = isTerminalTensorUnit.from X ▷ Y ≫ (fun_ Y).hom := by cat_disch

namespace SemiCartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [SemiCartesianMonoidalCategory C]

/--
Definition of `toUnit` / `toUnit` 的定义

English:
definition toUnit
  signature: (X : C)
  body: isTerminalTensorUnit.from X

中文:
定义 toUnit
  签名: (X : C)
  定义体: isTerminalTensorUnit.from X

Depends on / 依赖: J.overEquiv_symm_mem_over, isTerminalTensorUnit, isTerminalTensorUnit.from, overEquiv_symm_mem_over
-/
def toUnit (X : C) : X ⟶ 𝟙_ C := isTerminalTensorUnit.from X

instance (X : C) : Unique (X ⟶ 𝟙_ C) := isTerminalEquivUnique _ _ isTerminalTensorUnit _

/--
lemma `default_eq_toUnit` / 引理 `default_eq_toUnit`

English:
lemma default_eq_toUnit
  given: (X : C)
  statement: default = toUnit X
  proof: rfl

中文:
引理 default_eq_toUnit
  条件: (X : C)
  结论: default = toUnit X
  证明: rfl

Depends on / 依赖: Functor, Functor.isContinuous_of_coverPreserving, isContinuous_of_coverPreserving, over_forget_compatiblePreserving, over_forget_coverPreserving
-/
lemma default_eq_toUnit (X : C) : default = toUnit X := rfl

/--
This lemma follows from the preexisting `Unique` instance, but
it is often convenient to use it directly as `apply toUnit_unique` forcing
lean to do the necessary elaboration.
-/
@[ext]
/--
lemma `toUnit_unique` / 引理 `toUnit_unique`

English:
lemma toUnit_unique
  given: {X : C} (f g : X ⟶ 𝟙_ _)
  statement: f = g
  proof: Subsingleton.elim _ _

中文:
引理 toUnit_unique
  条件: {X : C} (f g : X ⟶ 𝟙_ _)
  结论: f = g
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
lemma toUnit_unique {X : C} (f g : X ⟶ 𝟙_ _) : f = g :=
  Subsingleton.elim _ _

/--
lemma `toUnit_unit` / 引理 `toUnit_unit`

English:
lemma toUnit_unit
  statement: toUnit (𝟙_ C) = 𝟙 (𝟙_ C)
  proof: toUnit_unique ..

@[reassoc (attr := simp)]

中文:
引理 toUnit_unit
  结论: toUnit (𝟙_ C) = 𝟙 (𝟙_ C)
  证明: toUnit_unique ..

@[reassoc (attr := simp)]
-/
@[simp] lemma toUnit_unit : toUnit (𝟙_ C) = 𝟙 (𝟙_ C) := toUnit_unique ..

@[reassoc (attr := simp)]
/--
theorem `comp_toUnit` / 定理 `comp_toUnit`

English:
theorem comp_toUnit
  given: {X Y : C} (f : X ⟶ Y)
  statement: f ≫ toUnit Y = toUnit X
  proof: toUnit_unique _ _

中文:
定理 comp_toUnit
  条件: {X Y : C} (f : X ⟶ Y)
  结论: f ≫ toUnit Y = toUnit X
  证明: toUnit_unique _ _

Depends on / 依赖: toUnit_unique
-/
theorem comp_toUnit {X Y : C} (f : X ⟶ Y) : f ≫ toUnit Y = toUnit X :=
  toUnit_unique _ _

end SemiCartesianMonoidalCategory

variable (C) in
/--
Definition of `CartesianMonoidalCategory` / `CartesianMonoidalCategory` 的定义

English:
class CartesianMonoidalCategory
  parameters: (C : Type u) [Category.{v} C]
  axioms and operations (1):
    - tensorProductIsBinaryProduct((X Y : C)) : IsLimit BinaryFan.mk (fst X Y) (snd X Y)

中文:
类 CartesianMonoidalCategory
  参数: (C : 类型u) [Category.{v} C]
  公理与运算 (1 个):
    - tensorProductIsBinaryProduct((X Y : C)) : IsLimit BinaryFan.mk (fst X Y) (snd X Y)

Depends on / 依赖: Functor, Functor.isContinuous_of_coverPreserving, isContinuous_of_coverPreserving, over_map_compatiblePreserving, over_map_coverPreserving
-/
class CartesianMonoidalCategory (C : Type u) [Category.{v} C] extends
    SemiCartesianMonoidalCategory C where
  /-- The monoidal product is the categorical product. -/
tensorProductIsBinaryProduct (X Y : C) : IsLimit BinaryFan.mk (fst X Y) (snd X Y)

namespace CartesianMonoidalCategory

export SemiCartesianMonoidalCategory (isTerminalTensorUnit fst snd fst_def snd_def toUnit
  toUnit_unique toUnit_unit comp_toUnit comp_toUnit_assoc default_eq_toUnit)

variable {C : Type u} [Category.{v} C]

section OfChosenFiniteProducts
variable (𝒯 : LimitCone (Functor.empty.{0} C)) (ℬ : forall X Y : C, LimitCone (pair X Y))
  {X₁ X₂ X₃ Y₁ Y₂ Y₃ Z₁ Z₂ : C}

namespace ofChosenFiniteProducts

/--
Definition of `tensorObj` / `tensorObj` 的定义

English:
abbreviation tensorObj
  signature: (X Y : C)
  body: (ℬ X Y).cone.pt

中文:
缩写 tensorObj
  签名: (X Y : C)
  定义体: (ℬ X Y).cone.pt

Depends on / 依赖: J.mem_over_iff, Sieve.overEquiv_functorPullback_map, cone.pt, mem_over_iff, overEquiv_functorPullback_map
-/
abbrev tensorObj (X Y : C) : C := (ℬ X Y).cone.pt

/--
Definition of `tensorHom` / `tensorHom` 的定义

English:
abbreviation tensorHom
  signature: (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  body: (BinaryFan.IsLimit.lift' (ℬ Y₁ Y₂).isLimit ((ℬ X₁ X₂).cone.π.app ⟨.left⟩ ≫ f)
      (((ℬ X₁ X₂).cone.π.app ⟨.right⟩ : (ℬ X₁ X₂).cone.pt ⟶ X₂) ≫ g)).val

中文:
缩写 tensorHom
  签名: (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
  定义体: (BinaryFan.IsLimit.lift' (ℬ Y₁ Y₂).isLimit ((ℬ X₁ X₂).cone.π.app ⟨.left⟩ ≫ f)
      (((ℬ X₁ X₂).cone.π.app ⟨.right⟩ : (ℬ X₁ X₂).cone.pt ⟶ X₂) ≫ g)).val

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.lift, IsCocontinuous, IsLimit, J.over, K.over, cone.pt, isLimit
-/
abbrev tensorHom (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : tensorObj ℬ X₁ X₂ ⟶ tensorObj ℬ Y₁ Y₂ :=
  (BinaryFan.IsLimit.lift' (ℬ Y₁ Y₂).isLimit ((ℬ X₁ X₂).cone.π.app ⟨.left⟩ ≫ f)
      (((ℬ X₁ X₂).cone.π.app ⟨.right⟩ : (ℬ X₁ X₂).cone.pt ⟶ X₂) ≫ g)).val

set_option backward.isDefEq.respectTransparency false in
/--
lemma `id_tensorHom_id` / 引理 `id_tensorHom_id`

English:
lemma id_tensorHom_id
  given: (X Y : C)
  statement: tensorHom ℬ (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj ℬ X Y)
  proof: (ℬ _ _).isLimit.hom_ext by rintro ⟨_ | _⟩ <;> simp [tensorHom]

中文:
引理 id_tensorHom_id
  条件: (X Y : C)
  结论: tensorHom ℬ (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj ℬ X Y)
  证明: (ℬ _ _).isLimit.hom_ext by rintro ⟨_ | _⟩ <;> simp [tensorHom]

Depends on / 依赖: hom_ext, isLimit, isLimit.hom_ext, tensorHom
-/
lemma id_tensorHom_id (X Y : C) : tensorHom ℬ (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj ℬ X Y) :=
(ℬ _ _).isLimit.hom_ext by rintro ⟨_ | _⟩ <;> simp [tensorHom]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `tensorHom_comp_tensorHom` / 引理 `tensorHom_comp_tensorHom`

English:
lemma tensorHom_comp_tensorHom
  given: (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂)
  proof: (ℬ _ _).isLimit.hom_ext by rintro ⟨_ | _⟩ <;> simp [tensorHom]

中文:
引理 tensorHom_comp_tensorHom
  条件: (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂)
  证明: (ℬ _ _).isLimit.hom_ext by rintro ⟨_ | _⟩ <;> simp [tensorHom]

Depends on / 依赖: Category, Category.assoc, E.mem, GrothendieckTopology, GrothendieckTopology.mem_over_iff, Over.forget, Over.forget_map, Over.forget_obj, Over.hom, Over.homMk, Over.mk, Over.w, PreZeroHypercover, PreZeroHypercover.sieve, Sieve.overEquiv_preOneHypercover_sieve, forget, forget_map, forget_obj, hom_ext, isLimit
-/
lemma tensorHom_comp_tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom ℬ f₁ f₂ ≫ tensorHom ℬ g₁ g₂ = tensorHom ℬ (f₁ ≫ g₁) (f₂ ≫ g₂) :=
(ℬ _ _).isLimit.hom_ext by rintro ⟨_ | _⟩ <;> simp [tensorHom]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `pentagon` / 引理 `pentagon`

English:
lemma pentagon
  given: (W X Y Z : C)
  proof: by
  dsimp [tensorHom]
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩
  · simp
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩
  · simp
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩ <;> simp

中文:
引理 pentagon
  条件: (W X Y Z : C)
  证明: by
  dsimp [tensorHom]
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩
  · simp
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩
  · simp
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩ <;> simp

Depends on / 依赖: E.map, GrothendieckTopology, GrothendieckTopology.mem_over_iff, Over.forget, Over.post_forget_eq_forget_comp, Over.post_obj, PreOneHypercover, PreOneHypercover.map_comp, PreZeroHypercover, PreZeroHypercover.sieve, Sieve.functorPushforward_ofArrows, Sieve.overEquiv_ofArrows, Sieve.overEquiv_preOneHypercover_sieve, forget, functorPushforward_ofArrows, hom_ext, isLimit, isLimit.hom_ext, map_comp, mem_over_iff
-/
lemma pentagon (W X Y Z : C) :
    tensorHom ℬ (BinaryFan.associatorOfLimitCone ℬ W X Y).hom (𝟙 Z) ≫
        (BinaryFan.associatorOfLimitCone ℬ W (tensorObj ℬ X Y) Z).hom ≫
          tensorHom ℬ (𝟙 W) (BinaryFan.associatorOfLimitCone ℬ X Y Z).hom =
      (BinaryFan.associatorOfLimitCone ℬ (tensorObj ℬ W X) Y Z).hom ≫
        (BinaryFan.associatorOfLimitCone ℬ W X (tensorObj ℬ Y Z)).hom := by
  dsimp [tensorHom]
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩
  · simp
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩
  · simp
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩ <;> simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `triangle` / 引理 `triangle`

English:
lemma triangle
  given: (X Y : C)
  proof: (ℬ _ _).isLimit.hom_ext by rintro ⟨_ | _⟩ <;> simp

中文:
引理 triangle
  条件: (X Y : C)
  证明: (ℬ _ _).isLimit.hom_ext by rintro ⟨_ | _⟩ <;> simp

Depends on / 依赖: Functor, Functor.isContinuous_comp, K.over, hom_ext, isContinuous_comp, isLimit, isLimit.hom_ext
-/
lemma triangle (X Y : C) :
    (BinaryFan.associatorOfLimitCone ℬ X 𝒯.cone.pt Y).hom ≫
        tensorHom ℬ (𝟙 X) (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt Y).isLimit).hom =
      tensorHom ℬ (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X 𝒯.cone.pt).isLimit).hom (𝟙 Y) :=
(ℬ _ _).isLimit.hom_ext by rintro ⟨_ | _⟩ <;> simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `leftUnitor_naturality` / 引理 `leftUnitor_naturality`

English:
lemma leftUnitor_naturality
  given: (f : X₁ ⟶ X₂)
  proof: by
  simp [tensorHom]

中文:
引理 leftUnitor_naturality
  条件: (f : X₁ ⟶ X₂)
  证明: by
  simp [tensorHom]

Depends on / 依赖: tensorHom
-/
lemma leftUnitor_naturality (f : X₁ ⟶ X₂) :
    tensorHom ℬ (𝟙 𝒯.cone.pt) f ≫ (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X₂).isLimit).hom =
      (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X₁).isLimit).hom ≫ f := by
  simp [tensorHom]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `rightUnitor_naturality` / 引理 `rightUnitor_naturality`

English:
lemma rightUnitor_naturality
  given: (f : X₁ ⟶ X₂)
  proof: by
  simp [tensorHom]

中文:
引理 rightUnitor_naturality
  条件: (f : X₁ ⟶ X₂)
  证明: by
  simp [tensorHom]

Depends on / 依赖: tensorHom
-/
lemma rightUnitor_naturality (f : X₁ ⟶ X₂) :
    tensorHom ℬ f (𝟙 𝒯.cone.pt) ≫ (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X₂ 𝒯.cone.pt).isLimit).hom =
      (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X₁ 𝒯.cone.pt).isLimit).hom ≫ f := by
  simp [tensorHom]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `associator_naturality` / 引理 `associator_naturality`

English:
lemma associator_naturality
  given: (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
  proof: by
  dsimp [tensorHom]
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩
  · simp
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩ <;> simp

中文:
引理 associator_naturality
  条件: (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
  证明: by
  dsimp [tensorHom]
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩
  · simp
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩ <;> simp

Depends on / 依赖: hom_ext, isLimit, isLimit.hom_ext, tensorHom
-/
lemma associator_naturality (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensorHom ℬ (tensorHom ℬ f₁ f₂) f₃ ≫ (BinaryFan.associatorOfLimitCone ℬ Y₁ Y₂ Y₃).hom =
      (BinaryFan.associatorOfLimitCone ℬ X₁ X₂ X₃).hom ≫ tensorHom ℬ f₁ (tensorHom ℬ f₂ f₃) := by
  dsimp [tensorHom]
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩
  · simp
  apply (ℬ _ _).isLimit.hom_ext
  rintro ⟨_ | _⟩ <;> simp

end ofChosenFiniteProducts

open ofChosenFiniteProducts

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofChosenFiniteProducts` / `ofChosenFiniteProducts` 的定义

English:
abbreviation ofChosenFiniteProducts
  signature: : CartesianMonoidalCategory C
  body: letI : MonoidalCategoryStruct C := {
    tensorUnit := 𝒯.cone.pt
    tensorObj := tensorObj ℬ
    tensorHom := tensorHom ℬ
    whiskerLeft X {_ _} g := tensorHom ℬ (𝟙 X) g
    whiskerRight {_ _} f Y := tensorHom ℬ f (𝟙 Y)
    associator := BinaryFan.associatorOfLimitCone ℬ
    leftUnitor X := Binary

中文:
缩写 ofChosenFiniteProducts
  签名: : CartesianMonoidalCategory C
  定义体: letI : MonoidalCategoryStruct C := {
    tensorUnit := 𝒯.cone.pt
    tensorObj := tensorObj ℬ
    tensorHom := tensorHom ℬ
    whiskerLeft X {_ _} g := tensorHom ℬ (𝟙 X) g
    whiskerRight {_ _} f Y := tensorHom ℬ f (𝟙 Y)
    associator := BinaryFan.associatorOfLimitCone ℬ
    leftUnitor X := Binary

Depends on / 依赖: BinaryFan, BinaryFan.associatorOfLimitCone, BinaryFan.leftUnitor, BinaryFan.rightUnitor, Functor, Functor.isContinuous_of_coverPreserving, J.over, MonoidalCategoryStruct, Over.star, associator, associatorOfLimitCone, compatiblePreservingOfFlat, cone.pt, coverPreserving_over_star, id_tensorHom_id, isContinuous_of_coverPreserving, isLimit, leftUnitor, ofTensorHom, rightUnitor
-/
abbrev ofChosenFiniteProducts : CartesianMonoidalCategory C :=
  letI : MonoidalCategoryStruct C := {
    tensorUnit := 𝒯.cone.pt
    tensorObj := tensorObj ℬ
    tensorHom := tensorHom ℬ
    whiskerLeft X {_ _} g := tensorHom ℬ (𝟙 X) g
    whiskerRight {_ _} f Y := tensorHom ℬ f (𝟙 Y)
    associator := BinaryFan.associatorOfLimitCone ℬ
    leftUnitor X := BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X).isLimit
    rightUnitor X := BinaryFan.rightUnitor 𝒯.isLimit (ℬ X 𝒯.cone.pt).isLimit
  }
  {
  toMonoidalCategory := .ofTensorHom
    (id_tensorHom_id := id_tensorHom_id ℬ)
    (tensorHom_comp_tensorHom := tensorHom_comp_tensorHom ℬ)
    (pentagon := pentagon ℬ)
    (triangle := triangle 𝒯 ℬ)
    (leftUnitor_naturality := leftUnitor_naturality 𝒯 ℬ)
    (rightUnitor_naturality := rightUnitor_naturality 𝒯 ℬ)
    (associator_naturality := associator_naturality ℬ)
  isTerminalTensorUnit :=
    .ofUniqueHom (𝒯.isLimit.lift <| asEmptyCone ·) fun _ _ => 𝒯.isLimit.hom_ext (by simp)
  fst X Y := BinaryFan.fst (ℬ X Y).cone
  snd X Y := BinaryFan.snd (ℬ X Y).cone
  tensorProductIsBinaryProduct X Y := BinaryFan.IsLimit.mk _
    (fun f g => (BinaryFan.IsLimit.lift' (ℬ X Y).isLimit f g).1)
    (fun f g => (BinaryFan.IsLimit.lift' (ℬ X Y).isLimit f g).2.1)
    (fun f g => (BinaryFan.IsLimit.lift' (ℬ X Y).isLimit f g).2.2)
    (fun f g m hf hg =>
      BinaryFan.IsLimit.hom_ext (ℬ X Y).isLimit (by simpa using hf) (by simpa using hg))
  fst_def X Y := (((ℬ X 𝒯.cone.pt).isLimit.fac
    (BinaryFan.mk _ _) ⟨.left⟩).trans (Category.comp_id _)).symm
  snd_def X Y := (((ℬ 𝒯.cone.pt Y).isLimit.fac
    (BinaryFan.mk _ _) ⟨.right⟩).trans (Category.comp_id _)).symm
  }

omit 𝒯 in
/--
Definition of `ofHasFiniteProducts` / `ofHasFiniteProducts` 的定义

English:
abbreviation ofHasFiniteProducts
  signature: [HasFiniteProducts C]
  body: .ofChosenFiniteProducts (getLimitCone (.empty C)) (getLimitCone <| pair · ·)

中文:
缩写 ofHasFiniteProducts
  签名: [HasFiniteProducts C]
  定义体: .ofChosenFiniteProducts (getLimitCone (.empty C)) (getLimitCone <| pair · ·)

Depends on / 依赖: getLimitCone, ofChosenFiniteProducts
-/
noncomputable abbrev ofHasFiniteProducts [HasFiniteProducts C] : CartesianMonoidalCategory C :=
  .ofChosenFiniteProducts (getLimitCone (.empty C)) (getLimitCone <| pair · ·)

end OfChosenFiniteProducts

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open MonoidalCategory

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y)
  body: (BinaryFan.IsLimit.lift' (tensorProductIsBinaryProduct X Y) f g).1

@[reassoc (attr := simp)]

中文:
定义 lift
  签名: {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y)
  定义体: (BinaryFan.IsLimit.lift' (tensorProductIsBinaryProduct X Y) f g).1

@[reassoc (attr := simp)]

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.lift, IsLimit, tensorProductIsBinaryProduct
-/
def lift {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : T ⟶ X otimes Y :=
  (BinaryFan.IsLimit.lift' (tensorProductIsBinaryProduct X Y) f g).1

@[reassoc (attr := simp)]
/--
lemma `lift_fst` / 引理 `lift_fst`

English:
lemma lift_fst
  given: {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y)
  statement: lift f g ≫ fst _ _ = f
  proof: (BinaryFan.IsLimit.lift' (tensorProductIsBinaryProduct X Y) f g).2.1

@[reassoc (attr := simp)]

中文:
引理 lift_fst
  条件: {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y)
  结论: lift f g ≫ fst _ _ = f
  证明: (BinaryFan.IsLimit.lift' (tensorProductIsBinaryProduct X Y) f g).2.1

@[reassoc (attr := simp)]

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.lift, IsLimit, tensorProductIsBinaryProduct
-/
lemma lift_fst {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f :=
  (BinaryFan.IsLimit.lift' (tensorProductIsBinaryProduct X Y) f g).2.1

@[reassoc (attr := simp)]
/--
lemma `lift_snd` / 引理 `lift_snd`

English:
lemma lift_snd
  given: {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y)
  statement: lift f g ≫ snd _ _ = g
  proof: (BinaryFan.IsLimit.lift' (tensorProductIsBinaryProduct X Y) f g).2.2

中文:
引理 lift_snd
  条件: {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y)
  结论: lift f g ≫ snd _ _ = g
  证明: (BinaryFan.IsLimit.lift' (tensorProductIsBinaryProduct X Y) f g).2.2

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.lift, IsLimit, tensorProductIsBinaryProduct
-/
lemma lift_snd {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g :=
  (BinaryFan.IsLimit.lift' (tensorProductIsBinaryProduct X Y) f g).2.2

/--
Instance `mono_lift_of_mono_left` / 实例 `mono_lift_of_mono_left`

English:
instance mono_lift_of_mono_left
  signature: {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)
  body: mono_of_mono_fac lift_fst _ _

中文:
实例 mono_lift_of_mono_left
  签名: {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)
  定义体: mono_of_mono_fac lift_fst _ _

Depends on / 依赖: lift_fst, mono_of_mono_fac
-/
instance mono_lift_of_mono_left {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (lift f g) :=
mono_of_mono_fac lift_fst _ _

/--
Instance `mono_lift_of_mono_right` / 实例 `mono_lift_of_mono_right`

English:
instance mono_lift_of_mono_right
  signature: {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)
  body: mono_of_mono_fac lift_snd _ _

@[ext 1050]

中文:
实例 mono_lift_of_mono_right
  签名: {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)
  定义体: mono_of_mono_fac lift_snd _ _

@[ext 1050]

Depends on / 依赖: lift_snd, mono_of_mono_fac
-/
instance mono_lift_of_mono_right {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (lift f g) :=
mono_of_mono_fac lift_snd _ _

@[ext 1050]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {T X Y : C} (f g : T ⟶ X otimes Y)
  proof: BinaryFan.IsLimit.hom_ext (tensorProductIsBinaryProduct X Y) h_fst h_snd

中文:
引理 hom_ext
  结论: {T X Y : C} (f g : T ⟶ X otimes Y)
  证明: BinaryFan.IsLimit.hom_ext (tensorProductIsBinaryProduct X Y) h_fst h_snd

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.hom_ext, IsLimit, h_fst, h_snd, hom_ext, tensorProductIsBinaryProduct
-/
lemma hom_ext {T X Y : C} (f g : T ⟶ X otimes Y)
    (h_fst : f ≫ fst _ _ = g ≫ fst _ _)
    (h_snd : f ≫ snd _ _ = g ≫ snd _ _) :
    f = g :=
  BinaryFan.IsLimit.hom_ext (tensorProductIsBinaryProduct X Y) h_fst h_snd

-- Similarly to `CategoryTheory.Limits.prod.comp_lift`, we do not make the `assoc` version a simp
-- lemma
@[reassoc, simp]
/--
lemma `comp_lift` / 引理 `comp_lift`

English:
lemma comp_lift
  given: {V W X Y : C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y)
  proof: by ext <;> simp

@[simp]

中文:
引理 comp_lift
  条件: {V W X Y : C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y)
  证明: by ext <;> simp

@[simp]
-/
lemma comp_lift {V W X Y : C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) :
    f ≫ lift g h = lift (f ≫ g) (f ≫ h) := by ext <;> simp

@[simp]
/--
lemma `lift_fst_snd` / 引理 `lift_fst_snd`

English:
lemma lift_fst_snd
  given: {X Y : C}
  statement: lift (fst X Y) (snd X Y) = 𝟙 (X otimes Y)
  proof: by ext <;> simp

@[simp]

中文:
引理 lift_fst_snd
  条件: {X Y : C}
  结论: lift (fst X Y) (snd X Y) = 𝟙 (X otimes Y)
  证明: by ext <;> simp

@[simp]
-/
lemma lift_fst_snd {X Y : C} : lift (fst X Y) (snd X Y) = 𝟙 (X otimes Y) := by ext <;> simp

@[simp]
/--
lemma `lift_comp_fst_snd` / 引理 `lift_comp_fst_snd`

English:
lemma lift_comp_fst_snd
  given: {X Y Z : C} (f : X ⟶ Y otimes Z)
  proof: by
  cat_disch

中文:
引理 lift_comp_fst_snd
  条件: {X Y Z : C} (f : X ⟶ Y otimes Z)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma lift_comp_fst_snd {X Y Z : C} (f : X ⟶ Y otimes Z) :
    lift (f ≫ fst _ _) (f ≫ snd _ _) = f := by
  cat_disch

/-- The universal property of a cartesian `⊗` as an equivalence. -/
@[simps]
/--
Definition of `liftEquiv` / `liftEquiv` 的定义

English:
definition liftEquiv
  signature: {T X Y : C}
  body: lift f.1 f.2
  invFun f := ⟨f ≫ fst _ _, f ≫ snd _ _⟩
  left_inv := by cat_disch
  right_inv := by cat_disch

@[reassoc (attr := simp)]

中文:
定义 liftEquiv
  签名: {T X Y : C}
  定义体: lift f.1 f.2
  invFun f := ⟨f ≫ fst _ _, f ≫ snd _ _⟩
  left_inv := by cat_disch
  right_inv := by cat_disch

@[reassoc (attr := simp)]
-/
def liftEquiv {T X Y : C} : (T ⟶ X) × (T ⟶ Y) ≃ (T ⟶ X otimes Y) where
  toFun f := lift f.1 f.2
  invFun f := ⟨f ≫ fst _ _, f ≫ snd _ _⟩
  left_inv := by cat_disch
  right_inv := by cat_disch

@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_fst` / 引理 `whiskerLeft_fst`

English:
lemma whiskerLeft_fst
  given: (X : C) {Y Z : C} (f : Y ⟶ Z)
  statement: X ◁ f ≫ fst _ _ = fst _ _
  proof: by
  simp [fst_def, ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]

中文:
引理 whiskerLeft_fst
  条件: (X : C) {Y Z : C} (f : Y ⟶ Z)
  结论: X ◁ f ≫ fst _ _ = fst _ _
  证明: by
  simp [fst_def, ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: fst_def, whiskerLeft_comp_assoc
-/
lemma whiskerLeft_fst (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ fst _ _ = fst _ _ := by
  simp [fst_def, ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]
/--
lemma `whiskerLeft_snd` / 引理 `whiskerLeft_snd`

English:
lemma whiskerLeft_snd
  given: (X : C) {Y Z : C} (f : Y ⟶ Z)
  statement: X ◁ f ≫ snd _ _ = snd _ _ ≫ f
  proof: by
  simp [snd_def, whisker_exchange_assoc]

@[reassoc (attr := simp)]

中文:
引理 whiskerLeft_snd
  条件: (X : C) {Y Z : C} (f : Y ⟶ Z)
  结论: X ◁ f ≫ snd _ _ = snd _ _ ≫ f
  证明: by
  simp [snd_def, whisker_exchange_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.mem_over_iff, Over.iteratedSliceBackward_forget_forget, Sieve.functorPushforward_comp, Sieve.overEquiv, functorPushforward_comp, iteratedSliceBackward_forget_forget, mem_over_iff, overEquiv, snd_def, whisker_exchange_assoc
-/
lemma whiskerLeft_snd (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ snd _ _ = snd _ _ ≫ f := by
  simp [snd_def, whisker_exchange_assoc]

@[reassoc (attr := simp)]
/--
lemma `whiskerRight_fst` / 引理 `whiskerRight_fst`

English:
lemma whiskerRight_fst
  given: {X Y : C} (f : X ⟶ Y) (Z : C)
  statement: f ▷ Z ≫ fst _ _ = fst _ _ ≫ f
  proof: by
  simp [fst_def, ← whisker_exchange_assoc]

@[reassoc (attr := simp)]

中文:
引理 whiskerRight_fst
  条件: {X Y : C} (f : X ⟶ Y) (Z : C)
  结论: f ▷ Z ≫ fst _ _ = fst _ _ ≫ f
  证明: by
  simp [fst_def, ← whisker_exchange_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: IsContinuous, f.iteratedSliceEquiv.functor.IsContinuous, fst_def, functor, iteratedSliceEquiv, whisker_exchange_assoc
-/
lemma whiskerRight_fst {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ fst _ _ = fst _ _ ≫ f := by
  simp [fst_def, ← whisker_exchange_assoc]

@[reassoc (attr := simp)]
/--
lemma `whiskerRight_snd` / 引理 `whiskerRight_snd`

English:
lemma whiskerRight_snd
  given: {X Y : C} (f : X ⟶ Y) (Z : C)
  statement: f ▷ Z ≫ snd _ _ = snd _ _
  proof: by
  simp [snd_def, ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]

中文:
引理 whiskerRight_snd
  条件: {X Y : C} (f : X ⟶ Y) (Z : C)
  结论: f ▷ Z ≫ snd _ _ = snd _ _
  证明: by
  simp [snd_def, ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: IsCocontinuous, comp_whiskerRight_assoc, f.iteratedSliceEquiv.functor.IsCocontinuous, functor, iteratedSliceEquiv, snd_def
-/
lemma whiskerRight_snd {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ snd _ _ = snd _ _ := by
  simp [snd_def, ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]
/--
lemma `tensorHom_fst` / 引理 `tensorHom_fst`

English:
lemma tensorHom_fst
  given: {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
  proof: by simp [tensorHom_def]

@[reassoc (attr := simp)]

中文:
引理 tensorHom_fst
  条件: {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
  证明: by simp [tensorHom_def]

@[reassoc (attr := simp)]

Depends on / 依赖: IsContinuous, f.iteratedSliceEquiv.inverse.IsContinuous, inverse, iteratedSliceEquiv, tensorHom_def
-/
lemma tensorHom_fst {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (f otimesₘ g) ≫ fst _ _ = fst _ _ ≫ f := by simp [tensorHom_def]

@[reassoc (attr := simp)]
/--
lemma `tensorHom_snd` / 引理 `tensorHom_snd`

English:
lemma tensorHom_snd
  given: {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
  proof: by simp [tensorHom_def]

@[reassoc (attr := simp)]

中文:
引理 tensorHom_snd
  条件: {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
  证明: by simp [tensorHom_def]

@[reassoc (attr := simp)]

Depends on / 依赖: IsCocontinuous, f.iteratedSliceEquiv.inverse.IsCocontinuous, inverse, iteratedSliceEquiv, tensorHom_def
-/
lemma tensorHom_snd {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (f otimesₘ g) ≫ snd _ _ = snd _ _ ≫ g := by simp [tensorHom_def]

@[reassoc (attr := simp)]
/--
lemma `lift_map` / 引理 `lift_map`

English:
lemma lift_map
  given: {V W X Y Z : C} (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z)
  proof: by ext <;> simp

@[simp]

中文:
引理 lift_map
  条件: {V W X Y Z : C} (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z)
  证明: by ext <;> simp

@[simp]
-/
lemma lift_map {V W X Y Z : C} (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) :
    lift f g ≫ (h otimesₘ k) = lift (f ≫ h) (g ≫ k) := by ext <;> simp

@[simp]
/--
lemma `lift_fst_comp_snd_comp` / 引理 `lift_fst_comp_snd_comp`

English:
lemma lift_fst_comp_snd_comp
  given: {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z)
  proof: by ext <;> simp

@[reassoc (attr := simp)]

中文:
引理 lift_fst_comp_snd_comp
  条件: {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z)
  证明: by ext <;> simp

@[reassoc (attr := simp)]
-/
lemma lift_fst_comp_snd_comp {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z) :
    lift (fst _ _ ≫ g) (snd _ _ ≫ g') = g otimesₘ g' := by ext <;> simp

@[reassoc (attr := simp)]
/--
lemma `lift_whiskerRight` / 引理 `lift_whiskerRight`

English:
lemma lift_whiskerRight
  given: {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W)
  proof: by
  cat_disch

@[reassoc (attr := simp)]

中文:
引理 lift_whiskerRight
  条件: {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W)
  证明: by
  cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: cat_disch
-/
lemma lift_whiskerRight {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) :
    lift f g ≫ (h ▷ Z) = lift (f ≫ h) g := by
  cat_disch

@[reassoc (attr := simp)]
/--
lemma `lift_whiskerLeft` / 引理 `lift_whiskerLeft`

English:
lemma lift_whiskerLeft
  given: {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Z ⟶ W)
  proof: by
  cat_disch

@[reassoc (attr := simp)]

中文:
引理 lift_whiskerLeft
  条件: {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Z ⟶ W)
  证明: by
  cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: cat_disch
-/
lemma lift_whiskerLeft {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Z ⟶ W) :
    lift f g ≫ (Y ◁ h) = lift f (g ≫ h) := by
  cat_disch

@[reassoc (attr := simp)]
/--
lemma `associator_hom_fst` / 引理 `associator_hom_fst`

English:
lemma associator_hom_fst
  given: (X Y Z : C)
  proof: by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor,
    ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]

中文:
引理 associator_hom_fst
  条件: (X Y Z : C)
  证明: by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor,
    ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: fst_def, whiskerLeft_comp_assoc, whiskerLeft_rightUnitor, whiskerLeft_rightUnitor_assoc
-/
lemma associator_hom_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ fst _ _ = fst _ _ ≫ fst _ _ := by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor,
    ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]
/--
lemma `associator_hom_snd_fst` / 引理 `associator_hom_snd_fst`

English:
lemma associator_hom_snd_fst
  given: (X Y Z : C)
  proof: by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor]

@[reassoc (attr := simp)]

中文:
引理 associator_hom_snd_fst
  条件: (X Y Z : C)
  证明: by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor]

@[reassoc (attr := simp)]

Depends on / 依赖: fst_def, whiskerLeft_rightUnitor, whiskerLeft_rightUnitor_assoc
-/
lemma associator_hom_snd_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ snd _ _ ≫ fst _ _ = fst _ _ ≫ snd _ _ := by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor]

@[reassoc (attr := simp)]
/--
lemma `associator_hom_snd_snd` / 引理 `associator_hom_snd_snd`

English:
lemma associator_hom_snd_snd
  given: (X Y Z : C)
  proof: by
  simp [snd_def, ← leftUnitor_whiskerRight_assoc, -leftUnitor_whiskerRight,
    ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]

中文:
引理 associator_hom_snd_snd
  条件: (X Y Z : C)
  证明: by
  simp [snd_def, ← leftUnitor_whiskerRight_assoc, -leftUnitor_whiskerRight,
    ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: comp_whiskerRight_assoc, leftUnitor_whiskerRight, leftUnitor_whiskerRight_assoc, snd_def
-/
lemma associator_hom_snd_snd (X Y Z : C) :
    (α_ X Y Z).hom ≫ snd _ _ ≫ snd _ _ = snd _ _ := by
  simp [snd_def, ← leftUnitor_whiskerRight_assoc, -leftUnitor_whiskerRight,
    ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]
/--
lemma `associator_inv_fst_fst` / 引理 `associator_inv_fst_fst`

English:
lemma associator_inv_fst_fst
  given: (X Y Z : C)
  proof: by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor,
    ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]

中文:
引理 associator_inv_fst_fst
  条件: (X Y Z : C)
  证明: by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor,
    ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: fst_def, whiskerLeft_comp_assoc, whiskerLeft_rightUnitor, whiskerLeft_rightUnitor_assoc
-/
lemma associator_inv_fst_fst (X Y Z : C) :
    (α_ X Y Z).inv ≫ fst _ _ ≫ fst _ _ = fst _ _ := by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor,
    ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]
/--
lemma `associator_inv_fst_snd` / 引理 `associator_inv_fst_snd`

English:
lemma associator_inv_fst_snd
  given: (X Y Z : C)
  proof: by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor]

@[reassoc (attr := simp)]

中文:
引理 associator_inv_fst_snd
  条件: (X Y Z : C)
  证明: by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor]

@[reassoc (attr := simp)]

Depends on / 依赖: fst_def, whiskerLeft_rightUnitor, whiskerLeft_rightUnitor_assoc
-/
lemma associator_inv_fst_snd (X Y Z : C) :
    (α_ X Y Z).inv ≫ fst _ _ ≫ snd _ _ = snd _ _ ≫ fst _ _ := by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor]

@[reassoc (attr := simp)]
/--
lemma `associator_inv_snd` / 引理 `associator_inv_snd`

English:
lemma associator_inv_snd
  given: (X Y Z : C)
  proof: by
  simp [snd_def, ← leftUnitor_whiskerRight_assoc, -leftUnitor_whiskerRight,
    ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]

中文:
引理 associator_inv_snd
  条件: (X Y Z : C)
  证明: by
  simp [snd_def, ← leftUnitor_whiskerRight_assoc, -leftUnitor_whiskerRight,
    ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: comp_whiskerRight_assoc, leftUnitor_whiskerRight, leftUnitor_whiskerRight_assoc, snd_def
-/
lemma associator_inv_snd (X Y Z : C) :
    (α_ X Y Z).inv ≫ snd _ _ = snd _ _ ≫ snd _ _ := by
  simp [snd_def, ← leftUnitor_whiskerRight_assoc, -leftUnitor_whiskerRight,
    ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]
/--
lemma `lift_lift_associator_hom` / 引理 `lift_lift_associator_hom`

English:
lemma lift_lift_associator_hom
  given: {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W)
  proof: by
  cat_disch

@[reassoc (attr := simp)]

中文:
引理 lift_lift_associator_hom
  条件: {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W)
  证明: by
  cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: cat_disch
-/
lemma lift_lift_associator_hom {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) :
    lift (lift f g) h ≫ (α_ Y Z W).hom = lift f (lift g h) := by
  cat_disch

@[reassoc (attr := simp)]
/--
lemma `lift_lift_associator_inv` / 引理 `lift_lift_associator_inv`

English:
lemma lift_lift_associator_inv
  given: {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W)
  proof: by
  cat_disch

中文:
引理 lift_lift_associator_inv
  条件: {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma lift_lift_associator_inv {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) :
    lift f (lift g h) ≫ (α_ Y Z W).inv = lift (lift f g) h := by
  cat_disch

/--
lemma `leftUnitor_hom` / 引理 `leftUnitor_hom`

English:
lemma leftUnitor_hom
  given: (X : C)
  statement: (fun_ X).hom = snd _ _
  proof: by simp [snd_def]

中文:
引理 leftUnitor_hom
  条件: (X : C)
  结论: (fun_ X).hom = snd _ _
  证明: by simp [snd_def]

Depends on / 依赖: snd_def
-/
lemma leftUnitor_hom (X : C) : (fun_ X).hom = snd _ _ := by simp [snd_def]
/--
lemma `rightUnitor_hom` / 引理 `rightUnitor_hom`

English:
lemma rightUnitor_hom
  given: (X : C)
  statement: (ρ_ X).hom = fst _ _
  proof: by simp [fst_def]

@[reassoc (attr := simp)]

中文:
引理 rightUnitor_hom
  条件: (X : C)
  结论: (ρ_ X).hom = fst _ _
  证明: by simp [fst_def]

@[reassoc (attr := simp)]

Depends on / 依赖: fst_def
-/
lemma rightUnitor_hom (X : C) : (ρ_ X).hom = fst _ _ := by simp [fst_def]

@[reassoc (attr := simp)]
/--
lemma `leftUnitor_inv_fst` / 引理 `leftUnitor_inv_fst`

English:
lemma leftUnitor_inv_fst
  given: (X : C)
  proof: toUnit_unique _ _

@[reassoc (attr := simp)]

中文:
引理 leftUnitor_inv_fst
  条件: (X : C)
  证明: toUnit_unique _ _

@[reassoc (attr := simp)]

Depends on / 依赖: toUnit_unique
-/
lemma leftUnitor_inv_fst (X : C) :
    (fun_ X).inv ≫ fst _ _ = toUnit _ := toUnit_unique _ _

@[reassoc (attr := simp)]
/--
lemma `leftUnitor_inv_snd` / 引理 `leftUnitor_inv_snd`

English:
lemma leftUnitor_inv_snd
  given: (X : C)
  proof: by simp [snd_def]

@[reassoc (attr := simp)]

中文:
引理 leftUnitor_inv_snd
  条件: (X : C)
  证明: by simp [snd_def]

@[reassoc (attr := simp)]

Depends on / 依赖: snd_def
-/
lemma leftUnitor_inv_snd (X : C) :
    (fun_ X).inv ≫ snd _ _ = 𝟙 X := by simp [snd_def]

@[reassoc (attr := simp)]
/--
lemma `rightUnitor_inv_fst` / 引理 `rightUnitor_inv_fst`

English:
lemma rightUnitor_inv_fst
  given: (X : C)
  proof: by simp [fst_def]

@[reassoc (attr := simp)]

中文:
引理 rightUnitor_inv_fst
  条件: (X : C)
  证明: by simp [fst_def]

@[reassoc (attr := simp)]

Depends on / 依赖: fst_def
-/
lemma rightUnitor_inv_fst (X : C) :
    (ρ_ X).inv ≫ fst _ _ = 𝟙 X := by simp [fst_def]

@[reassoc (attr := simp)]
/--
lemma `rightUnitor_inv_snd` / 引理 `rightUnitor_inv_snd`

English:
lemma rightUnitor_inv_snd
  given: (X : C)
  proof: toUnit_unique _ _

@[reassoc]

中文:
引理 rightUnitor_inv_snd
  条件: (X : C)
  证明: toUnit_unique _ _

@[reassoc]

Depends on / 依赖: toUnit_unique
-/
lemma rightUnitor_inv_snd (X : C) :
    (ρ_ X).inv ≫ snd _ _ = toUnit _ := toUnit_unique _ _

@[reassoc]
/--
lemma `whiskerLeft_toUnit_comp_rightUnitor_hom` / 引理 `whiskerLeft_toUnit_comp_rightUnitor_hom`

English:
lemma whiskerLeft_toUnit_comp_rightUnitor_hom
  given: (X Y : C)
  statement: X ◁ toUnit Y ≫ (ρ_ X).hom = fst X Y
  proof: by
  rw [← cancel_mono (ρ_ X).inv]; aesop

@[reassoc]

中文:
引理 whiskerLeft_toUnit_comp_rightUnitor_hom
  条件: (X Y : C)
  结论: X ◁ toUnit Y ≫ (ρ_ X).hom = fst X Y
  证明: by
  rw [← cancel_mono (ρ_ X).inv]; aesop

@[reassoc]

Depends on / 依赖: cancel_mono
-/
lemma whiskerLeft_toUnit_comp_rightUnitor_hom (X Y : C) : X ◁ toUnit Y ≫ (ρ_ X).hom = fst X Y := by
  rw [← cancel_mono (ρ_ X).inv]; aesop

@[reassoc]
/--
lemma `whiskerRight_toUnit_comp_leftUnitor_hom` / 引理 `whiskerRight_toUnit_comp_leftUnitor_hom`

English:
lemma whiskerRight_toUnit_comp_leftUnitor_hom
  given: (X Y : C)
  statement: toUnit X ▷ Y ≫ (fun_ Y).hom = snd X Y
  proof: by
  rw [← cancel_mono (fun_ Y).inv]; aesop

@[reassoc (attr := simp)]

中文:
引理 whiskerRight_toUnit_comp_leftUnitor_hom
  条件: (X Y : C)
  结论: toUnit X ▷ Y ≫ (fun_ Y).hom = snd X Y
  证明: by
  rw [← cancel_mono (fun_ Y).inv]; aesop

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_mono, fun_
-/
lemma whiskerRight_toUnit_comp_leftUnitor_hom (X Y : C) : toUnit X ▷ Y ≫ (fun_ Y).hom = snd X Y := by
  rw [← cancel_mono (fun_ Y).inv]; aesop

@[reassoc (attr := simp)]
/--
lemma `lift_leftUnitor_hom` / 引理 `lift_leftUnitor_hom`

English:
lemma lift_leftUnitor_hom
  given: {X Y : C} (f : X ⟶ 𝟙_ C) (g : X ⟶ Y)
  proof: by
  rw [← Iso.eq_comp_inv]
  cat_disch

@[reassoc (attr := simp)]

中文:
引理 lift_leftUnitor_hom
  条件: {X Y : C} (f : X ⟶ 𝟙_ C) (g : X ⟶ Y)
  证明: by
  rw [← Iso.eq_comp_inv]
  cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.eq_comp_inv, cat_disch, eq_comp_inv
-/
lemma lift_leftUnitor_hom {X Y : C} (f : X ⟶ 𝟙_ C) (g : X ⟶ Y) :
    lift f g ≫ (fun_ Y).hom = g := by
  rw [← Iso.eq_comp_inv]
  cat_disch

@[reassoc (attr := simp)]
/--
lemma `lift_rightUnitor_hom` / 引理 `lift_rightUnitor_hom`

English:
lemma lift_rightUnitor_hom
  given: {X Y : C} (f : X ⟶ Y) (g : X ⟶ 𝟙_ C)
  proof: by
  rw [← Iso.eq_comp_inv]
  cat_disch

中文:
引理 lift_rightUnitor_hom
  条件: {X Y : C} (f : X ⟶ Y) (g : X ⟶ 𝟙_ C)
  证明: by
  rw [← Iso.eq_comp_inv]
  cat_disch

Depends on / 依赖: Iso.eq_comp_inv, cat_disch, eq_comp_inv
-/
lemma lift_rightUnitor_hom {X Y : C} (f : X ⟶ Y) (g : X ⟶ 𝟙_ C) :
    lift f g ≫ (ρ_ Y).hom = f := by
  rw [← Iso.eq_comp_inv]
  cat_disch

/-- Universal property of the Cartesian product: Maps to `X ⊗ Y` correspond to pairs of maps to `X`
and to `Y`. -/
@[simps]
/--
Definition of `homEquivToProd` / `homEquivToProd` 的定义

English:
definition homEquivToProd
  signature: {X Y Z : C}
  body: ⟨f ≫ fst _ _, f ≫ snd _ _⟩
  invFun f := lift f.1 f.2
  left_inv _ := by simp
  right_inv _ := by simp

中文:
定义 homEquivToProd
  签名: {X Y Z : C}
  定义体: ⟨f ≫ fst _ _, f ≫ snd _ _⟩
  invFun f := lift f.1 f.2
  left_inv _ := by simp
  right_inv _ := by simp
-/
def homEquivToProd {X Y Z : C} : (Z ⟶ X otimes Y) ≃ (Z ⟶ X) × (Z ⟶ Y) where
  toFun f := ⟨f ≫ fst _ _, f ≫ snd _ _⟩
  invFun f := lift f.1 f.2
  left_inv _ := by simp
  right_inv _ := by simp

section BraidedCategory

variable [BraidedCategory C]

@[reassoc (attr := simp)]
/--
theorem `braiding_hom_fst` / 定理 `braiding_hom_fst`

English:
theorem braiding_hom_fst
  given: (X Y : C)
  statement: (β_ X Y).hom ≫ fst _ _ = snd _ _
  proof: by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_naturality_left_assoc]

@[reassoc (attr := simp)]

中文:
定理 braiding_hom_fst
  条件: (X Y : C)
  结论: (β_ X Y).hom ≫ fst _ _ = snd _ _
  证明: by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_naturality_left_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: BraidedCategory, BraidedCategory.braiding_naturality_left_assoc, braiding_naturality_left_assoc, fst_def, snd_def
-/
theorem braiding_hom_fst (X Y : C) : (β_ X Y).hom ≫ fst _ _ = snd _ _ := by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_naturality_left_assoc]

@[reassoc (attr := simp)]
/--
theorem `braiding_hom_snd` / 定理 `braiding_hom_snd`

English:
theorem braiding_hom_snd
  given: (X Y : C)
  statement: (β_ X Y).hom ≫ snd _ _ = fst _ _
  proof: by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_naturality_right_assoc]

@[reassoc (attr := simp)]

中文:
定理 braiding_hom_snd
  条件: (X Y : C)
  结论: (β_ X Y).hom ≫ snd _ _ = fst _ _
  证明: by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_naturality_right_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: BraidedCategory, BraidedCategory.braiding_naturality_right_assoc, braiding_naturality_right_assoc, fst_def, snd_def
-/
theorem braiding_hom_snd (X Y : C) : (β_ X Y).hom ≫ snd _ _ = fst _ _ := by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_naturality_right_assoc]

@[reassoc (attr := simp)]
/--
theorem `braiding_inv_fst` / 定理 `braiding_inv_fst`

English:
theorem braiding_inv_fst
  given: (X Y : C)
  statement: (β_ X Y).inv ≫ fst _ _ = snd _ _
  proof: by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_inv_naturality_left_assoc]

@[reassoc (attr := simp)]

中文:
定理 braiding_inv_fst
  条件: (X Y : C)
  结论: (β_ X Y).inv ≫ fst _ _ = snd _ _
  证明: by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_inv_naturality_left_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: BraidedCategory, BraidedCategory.braiding_inv_naturality_left_assoc, braiding_inv_naturality_left_assoc, fst_def, snd_def
-/
theorem braiding_inv_fst (X Y : C) : (β_ X Y).inv ≫ fst _ _ = snd _ _ := by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_inv_naturality_left_assoc]

@[reassoc (attr := simp)]
/--
theorem `braiding_inv_snd` / 定理 `braiding_inv_snd`

English:
theorem braiding_inv_snd
  given: (X Y : C)
  statement: (β_ X Y).inv ≫ snd _ _ = fst _ _
  proof: by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_inv_naturality_right_assoc]

@[reassoc (attr := simp)]

中文:
定理 braiding_inv_snd
  条件: (X Y : C)
  结论: (β_ X Y).inv ≫ snd _ _ = fst _ _
  证明: by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_inv_naturality_right_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: BraidedCategory, BraidedCategory.braiding_inv_naturality_right_assoc, braiding_inv_naturality_right_assoc, fst_def, snd_def
-/
theorem braiding_inv_snd (X Y : C) : (β_ X Y).inv ≫ snd _ _ = fst _ _ := by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_inv_naturality_right_assoc]

@[reassoc (attr := simp)]
/--
lemma `tensorμ_fst` / 引理 `tensorμ_fst`

English:
lemma tensorμ_fst
  given: (W X Y Z : C)
  statement: tensorμ W X Y Z ≫ fst (W otimes Y) (X otimes Z) = fst W X otimesₘ fst Y Z
  proof: by
  ext <;> simp [tensorμ]

@[reassoc (attr := simp)]

中文:
引理 tensorμ_fst
  条件: (W X Y Z : C)
  结论: tensorμ W X Y Z ≫ fst (W otimes Y) (X otimes Z) = fst W X otimesₘ fst Y Z
  证明: by
  ext <;> simp [tensorμ]

@[reassoc (attr := simp)]
-/
lemma tensorμ_fst (W X Y Z : C) : tensorμ W X Y Z ≫ fst (W otimes Y) (X otimes Z) = fst W X otimesₘ fst Y Z := by
  ext <;> simp [tensorμ]

@[reassoc (attr := simp)]
/--
lemma `tensorμ_snd` / 引理 `tensorμ_snd`

English:
lemma tensorμ_snd
  given: (W X Y Z : C)
  statement: tensorμ W X Y Z ≫ snd (W otimes Y) (X otimes Z) = snd W X otimesₘ snd Y Z
  proof: by
  ext <;> simp [tensorμ]

@[reassoc (attr := simp)]

中文:
引理 tensorμ_snd
  条件: (W X Y Z : C)
  结论: tensorμ W X Y Z ≫ snd (W otimes Y) (X otimes Z) = snd W X otimesₘ snd Y Z
  证明: by
  ext <;> simp [tensorμ]

@[reassoc (attr := simp)]
-/
lemma tensorμ_snd (W X Y Z : C) : tensorμ W X Y Z ≫ snd (W otimes Y) (X otimes Z) = snd W X otimesₘ snd Y Z := by
  ext <;> simp [tensorμ]

@[reassoc (attr := simp)]
/--
lemma `tensorδ_fst` / 引理 `tensorδ_fst`

English:
lemma tensorδ_fst
  given: (W X Y Z : C)
  statement: tensorδ W X Y Z ≫ fst (W otimes X) (Y otimes Z) = fst W Y otimesₘ fst X Z
  proof: by
  ext <;> simp [tensorδ]

@[reassoc (attr := simp)]

中文:
引理 tensorδ_fst
  条件: (W X Y Z : C)
  结论: tensorδ W X Y Z ≫ fst (W otimes X) (Y otimes Z) = fst W Y otimesₘ fst X Z
  证明: by
  ext <;> simp [tensorδ]

@[reassoc (attr := simp)]
-/
lemma tensorδ_fst (W X Y Z : C) : tensorδ W X Y Z ≫ fst (W otimes X) (Y otimes Z) = fst W Y otimesₘ fst X Z := by
  ext <;> simp [tensorδ]

@[reassoc (attr := simp)]
/--
lemma `tensorδ_snd` / 引理 `tensorδ_snd`

English:
lemma tensorδ_snd
  given: (W X Y Z : C)
  statement: tensorδ W X Y Z ≫ snd (W otimes X) (Y otimes Z) = snd W Y otimesₘ snd X Z
  proof: by
  ext <;> simp [tensorδ]

中文:
引理 tensorδ_snd
  条件: (W X Y Z : C)
  结论: tensorδ W X Y Z ≫ snd (W otimes X) (Y otimes Z) = snd W Y otimesₘ snd X Z
  证明: by
  ext <;> simp [tensorδ]
-/
lemma tensorδ_snd (W X Y Z : C) : tensorδ W X Y Z ≫ snd (W otimes X) (Y otimes Z) = snd W Y otimesₘ snd X Z := by
  ext <;> simp [tensorδ]

/--
theorem `lift_snd_fst` / 定理 `lift_snd_fst`

English:
theorem lift_snd_fst
  given: {X Y : C}
  statement: lift (snd X Y) (fst X Y) = (β_ X Y).hom
  proof: by cat_disch

@[simp, reassoc]

中文:
定理 lift_snd_fst
  条件: {X Y : C}
  结论: lift (snd X Y) (fst X Y) = (β_ X Y).hom
  证明: by cat_disch

@[simp, reassoc]

Depends on / 依赖: cat_disch
-/
theorem lift_snd_fst {X Y : C} : lift (snd X Y) (fst X Y) = (β_ X Y).hom := by cat_disch

@[simp, reassoc]
/--
lemma `lift_snd_comp_fst_comp` / 引理 `lift_snd_comp_fst_comp`

English:
lemma lift_snd_comp_fst_comp
  given: {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z)
  proof: by cat_disch

@[reassoc (attr := simp)]

中文:
引理 lift_snd_comp_fst_comp
  条件: {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z)
  证明: by cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: cat_disch
-/
lemma lift_snd_comp_fst_comp {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z) :
    lift (snd _ _ ≫ g') (fst _ _ ≫ g) = (β_ _ _).hom ≫ (g' otimesₘ g) := by cat_disch

@[reassoc (attr := simp)]
/--
lemma `lift_braiding_hom` / 引理 `lift_braiding_hom`

English:
lemma lift_braiding_hom
  given: {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y)
  proof: by aesop

@[reassoc (attr := simp)]

中文:
引理 lift_braiding_hom
  条件: {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y)
  证明: by aesop

@[reassoc (attr := simp)]
-/
lemma lift_braiding_hom {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) :
    lift f g ≫ (β_ X Y).hom = lift g f := by aesop

@[reassoc (attr := simp)]
/--
lemma `lift_braiding_inv` / 引理 `lift_braiding_inv`

English:
lemma lift_braiding_inv
  given: {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y)
  proof: by aesop

中文:
引理 lift_braiding_inv
  条件: {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y)
  证明: by aesop
-/
lemma lift_braiding_inv {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) :
    lift f g ≫ (β_ Y X).inv = lift g f := by aesop

-- See note [lower instance priority]
instance (priority := low) toSymmetricCategory : SymmetricCategory C where

/-- `CartesianMonoidalCategory` implies `BraidedCategory`.
This is not an instance to prevent diamonds. -/
@[instance_reducible]
/--
Definition of `_root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory` / `_root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory` 的定义

English:
definition _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory
  signature: : BraidedCategory C where
  body: { hom := lift (snd _ _) (fst _ _), inv := lift (snd _ _) (fst _ _) }

中文:
定义 _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory
  签名: : BraidedCategory C where
  定义体: { hom := lift (snd _ _) (fst _ _), inv := lift (snd _ _) (fst _ _) }
-/
def _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory : BraidedCategory C where
  braiding X Y := { hom := lift (snd _ _) (fst _ _), inv := lift (snd _ _) (fst _ _) }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (BraidedCategory C)
  body: ⟨.ofCartesianMonoidalCategory⟩

中文:
实例 :
  签名: Nonempty (BraidedCategory C)
  定义体: ⟨.ofCartesianMonoidalCategory⟩

Depends on / 依赖: ofCartesianMonoidalCategory
-/
instance : Nonempty (BraidedCategory C) := ⟨.ofCartesianMonoidalCategory⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (BraidedCategory C)

中文:
实例 :
  签名: Subsingleton (BraidedCategory C)
-/
instance : Subsingleton (BraidedCategory C) where
  allEq
  | ⟨e₁, a₁, b₁, c₁, d₁⟩, ⟨e₂, a₂, b₂, c₂, d₂⟩ => by
      congr
      ext
      · exact (@braiding_hom_fst C _ ‹_› ⟨e₁, a₁, b₁, c₁, d₁⟩ ..).trans
          (@braiding_hom_fst C _ ‹_› ⟨e₂, a₂, b₂, c₂, d₂⟩ ..).symm
      · exact (@braiding_hom_snd C _ ‹_› ⟨e₁, a₁, b₁, c₁, d₁⟩ ..).trans
          (@braiding_hom_snd C _ ‹_› ⟨e₂, a₂, b₂, c₂, d₂⟩ ..).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (SymmetricCategory C)
  body: by rintro ⟨_⟩ ⟨_⟩; congr; exact Subsingleton.elim _ _

中文:
实例 :
  签名: Subsingleton (SymmetricCategory C)
  定义体: by rintro ⟨_⟩ ⟨_⟩; congr; exact Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
instance : Subsingleton (SymmetricCategory C) where
  allEq := by rintro ⟨_⟩ ⟨_⟩; congr; exact Subsingleton.elim _ _

end BraidedCategory

instance (priority := 100) : Limits.HasFiniteProducts C :=
  letI : forall (X Y : C), Limits.HasLimit (Limits.pair X Y) := fun _ _ =>
    .mk ⟨_, tensorProductIsBinaryProduct _ _⟩
  letI : Limits.HasBinaryProducts C := Limits.hasBinaryProducts_of_hasLimit_pair _
  letI : Limits.HasTerminal C := Limits.hasTerminal_of_unique (𝟙_ C)
  hasFiniteProducts_of_has_binary_and_terminal

section CartesianMonoidalCategoryComparison

variable {D : Type u₁} [Category.{v₁} D] [CartesianMonoidalCategory D] (F : C ⥤ D)
variable {E : Type u₂} [Category.{v₂} E] [CartesianMonoidalCategory E] (G : D ⥤ E)

section terminalComparison

/--
Definition of `terminalComparison` / `terminalComparison` 的定义

English:
abbreviation terminalComparison
  signature: : F.obj (𝟙_ C) ⟶ 𝟙_ D
  body: toUnit _

@[reassoc]

中文:
缩写 terminalComparison
  签名: : F.obj (𝟙_ C) ⟶ 𝟙_ D
  定义体: toUnit _

@[reassoc]

Depends on / 依赖: toUnit
-/
abbrev terminalComparison : F.obj (𝟙_ C) ⟶ 𝟙_ D := toUnit _

@[reassoc]
/--
lemma `map_toUnit_comp_terminalComparison` / 引理 `map_toUnit_comp_terminalComparison`

English:
lemma map_toUnit_comp_terminalComparison
  given: (A : C)
  proof: toUnit_unique _ _

中文:
引理 map_toUnit_comp_terminalComparison
  条件: (A : C)
  证明: toUnit_unique _ _

Depends on / 依赖: toUnit_unique
-/
lemma map_toUnit_comp_terminalComparison (A : C) :
    F.map (toUnit A) ≫ terminalComparison F = toUnit _ := toUnit_unique _ _

open Limits

/--
lemma `preservesLimit_empty_of_isIso_terminalComparison` / 引理 `preservesLimit_empty_of_isIso_terminalComparison`

English:
lemma preservesLimit_empty_of_isIso_terminalComparison
  given: [IsIso (terminalComparison F)]
  proof: by
  apply preservesLimit_of_preserves_limit_cone isTerminalTensorUnit
  apply isLimitChangeEmptyCone D isTerminalTensorUnit
.symm exact asIso (terminalComparison F)

中文:
引理 preservesLimit_empty_of_isIso_terminalComparison
  条件: [IsIso (terminalComparison F)]
  证明: by
  apply preservesLimit_of_preserves_limit_cone isTerminalTensorUnit
  apply isLimitChangeEmptyCone D isTerminalTensorUnit
.symm exact asIso (terminalComparison F)

Depends on / 依赖: isLimitChangeEmptyCone, isTerminalTensorUnit, mem_coverings_of_isIso, preservesLimit_of_preserves_limit_cone, terminalComparison
-/
lemma preservesLimit_empty_of_isIso_terminalComparison [IsIso (terminalComparison F)] :
    PreservesLimit (Functor.empty.{0} C) F := by
  apply preservesLimit_of_preserves_limit_cone isTerminalTensorUnit
  apply isLimitChangeEmptyCone D isTerminalTensorUnit
.symm exact asIso (terminalComparison F)

/--
Definition of `preservesTerminalIso` / `preservesTerminalIso` 的定义

English:
definition preservesTerminalIso
  signature: [h : PreservesLimit (Functor.empty.{0} C) F]
  body: (isLimitChangeEmptyCone D (isLimitOfPreserves _ isTerminalTensorUnit) (asEmptyCone (F.obj (𝟙_ C)))
    (Iso.refl _)).conePointUniqueUpToIso isTerminalTensorUnit

@[simp]

中文:
定义 preservesTerminalIso
  签名: [h : PreservesLimit (Functor.empty.{0} C) F]
  定义体: (isLimitChangeEmptyCone D (isLimitOfPreserves _ isTerminalTensorUnit) (asEmptyCone (F.obj (𝟙_ C)))
    (Iso.refl _)).conePointUniqueUpToIso isTerminalTensorUnit

@[simp]

Depends on / 依赖: F.obj, Iso.refl, asEmptyCone, conePointUniqueUpToIso, isLimitChangeEmptyCone, isLimitOfPreserves, isTerminalTensorUnit, mem_coverings_of_isPullback
-/
noncomputable def preservesTerminalIso [h : PreservesLimit (Functor.empty.{0} C) F] :
    F.obj (𝟙_ C) ≅ 𝟙_ D :=
  (isLimitChangeEmptyCone D (isLimitOfPreserves _ isTerminalTensorUnit) (asEmptyCone (F.obj (𝟙_ C)))
    (Iso.refl _)).conePointUniqueUpToIso isTerminalTensorUnit

@[simp]
/--
lemma `preservesTerminalIso_hom` / 引理 `preservesTerminalIso_hom`

English:
lemma preservesTerminalIso_hom
  given: [PreservesLimit (Functor.empty.{0} C) F]
  proof: toUnit_unique _ _

中文:
引理 preservesTerminalIso_hom
  条件: [PreservesLimit (Functor.empty.{0} C) F]
  证明: toUnit_unique _ _

Depends on / 依赖: comp_mem_coverings, toUnit_unique
-/
lemma preservesTerminalIso_hom [PreservesLimit (Functor.empty.{0} C) F] :
    (preservesTerminalIso F).hom = terminalComparison F := toUnit_unique _ _

/--
Instance `terminalComparison_isIso_of_preservesLimits` / 实例 `terminalComparison_isIso_of_preservesLimits`

English:
instance terminalComparison_isIso_of_preservesLimits
  signature: [PreservesLimit (Functor.empty.{0} C) F]
  body: by
  rw [← preservesTerminalIso_hom]
  infer_instance

@[simp]

中文:
实例 terminalComparison_isIso_of_preservesLimits
  签名: [PreservesLimit (Functor.empty.{0} C) F]
  定义体: by
  rw [← preservesTerminalIso_hom]
  infer_instance

@[simp]

Depends on / 依赖: J.sup_mem_coverings, K.sup_mem_coverings, infer_instance, preservesTerminalIso_hom, sup_mem_coverings
-/
instance terminalComparison_isIso_of_preservesLimits [PreservesLimit (Functor.empty.{0} C) F] :
    IsIso (terminalComparison F) := by
  rw [← preservesTerminalIso_hom]
  infer_instance

@[simp]
/--
lemma `preservesTerminalIso_id` / 引理 `preservesTerminalIso_id`

English:
lemma preservesTerminalIso_id
  statement: preservesTerminalIso (𝟭 C) = .refl _
  proof: by
  cat_disch

@[simp]

中文:
引理 preservesTerminalIso_id
  结论: preservesTerminalIso (𝟭 C) = .refl _
  证明: by
  cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
lemma preservesTerminalIso_id : preservesTerminalIso (𝟭 C) = .refl _ := by
  cat_disch

@[simp]
/--
lemma `preservesTerminalIso_comp` / 引理 `preservesTerminalIso_comp`

English:
lemma preservesTerminalIso_comp
  statement: [PreservesLimit (Functor.empty.{0} C) F]
  proof: by
  cat_disch

中文:
引理 preservesTerminalIso_comp
  结论: [PreservesLimit (Functor.empty.{0} C) F]
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma preservesTerminalIso_comp [PreservesLimit (Functor.empty.{0} C) F]
    [PreservesLimit (Functor.empty.{0} D) G] [PreservesLimit (Functor.empty.{0} C) (F ⋙ G)] :
    preservesTerminalIso (F ⋙ G) =
      G.mapIso (preservesTerminalIso F) ≪≫ preservesTerminalIso G := by
  cat_disch

end terminalComparison

section prodComparison

variable (A B : C)

/--
Definition of `prodComparison` / `prodComparison` 的定义

English:
definition prodComparison
  signature: (A B : C)
  body: lift (F.map (fst A B)) (F.map (snd A B))

@[reassoc (attr := simp)]

中文:
定义 prodComparison
  签名: (A B : C)
  定义体: lift (F.map (fst A B)) (F.map (snd A B))

@[reassoc (attr := simp)]

Depends on / 依赖: F.map
-/
def prodComparison (A B : C) : F.obj (A otimes B) ⟶ F.obj A otimes F.obj B :=
  lift (F.map (fst A B)) (F.map (snd A B))

@[reassoc (attr := simp)]
/--
theorem `prodComparison_fst` / 定理 `prodComparison_fst`

English:
theorem prodComparison_fst
  statement: prodComparison F A B ≫ fst _ _ = F.map (fst A B)
  proof: lift_fst _ _

@[reassoc (attr := simp)]

中文:
定理 prodComparison_fst
  结论: prodComparison F A B ≫ fst _ _ = F.map (fst A B)
  证明: lift_fst _ _

@[reassoc (attr := simp)]

Depends on / 依赖: lift_fst
-/
theorem prodComparison_fst : prodComparison F A B ≫ fst _ _ = F.map (fst A B) :=
  lift_fst _ _

@[reassoc (attr := simp)]
/--
theorem `prodComparison_snd` / 定理 `prodComparison_snd`

English:
theorem prodComparison_snd
  statement: prodComparison F A B ≫ snd _ _ = F.map (snd A B)
  proof: lift_snd _ _

@[reassoc (attr := simp)]

中文:
定理 prodComparison_snd
  结论: prodComparison F A B ≫ snd _ _ = F.map (snd A B)
  证明: lift_snd _ _

@[reassoc (attr := simp)]

Depends on / 依赖: lift_snd
-/
theorem prodComparison_snd : prodComparison F A B ≫ snd _ _ = F.map (snd A B) :=
  lift_snd _ _

@[reassoc (attr := simp)]
/--
theorem `inv_prodComparison_map_fst` / 定理 `inv_prodComparison_map_fst`

English:
theorem inv_prodComparison_map_fst
  given: [IsIso (prodComparison F A B)]
  proof: by simp [IsIso.inv_comp_eq]

@[reassoc (attr := simp)]

中文:
定理 inv_prodComparison_map_fst
  条件: [IsIso (prodComparison F A B)]
  证明: by simp [IsIso.inv_comp_eq]

@[reassoc (attr := simp)]

Depends on / 依赖: IsIso.inv_comp_eq, inv_comp_eq
-/
theorem inv_prodComparison_map_fst [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map (fst _ _) = fst _ _ := by simp [IsIso.inv_comp_eq]

@[reassoc (attr := simp)]
/--
theorem `inv_prodComparison_map_snd` / 定理 `inv_prodComparison_map_snd`

English:
theorem inv_prodComparison_map_snd
  given: [IsIso (prodComparison F A B)]
  proof: by simp [IsIso.inv_comp_eq]

中文:
定理 inv_prodComparison_map_snd
  条件: [IsIso (prodComparison F A B)]
  证明: by simp [IsIso.inv_comp_eq]

Depends on / 依赖: IsIso.inv_comp_eq, inv_comp_eq
-/
theorem inv_prodComparison_map_snd [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map (snd _ _) = snd _ _ := by simp [IsIso.inv_comp_eq]

variable {A B} {A' B' : C}

/-- Naturality of the `prodComparison` morphism in both arguments. -/
@[reassoc]
/--
theorem `prodComparison_natural` / 定理 `prodComparison_natural`

English:
theorem prodComparison_natural
  given: (f : A ⟶ A') (g : B ⟶ B')
  proof: by
  apply hom_ext <;>
  simp only [Category.assoc, prodComparison_fst, tensorHom_fst, prodComparison_fst_assoc,
    prodComparison_snd, tensorHom_snd, prodComparison_snd_assoc, ← F.map_comp]

中文:
定理 prodComparison_natural
  条件: (f : A ⟶ A') (g : B ⟶ B')
  证明: by
  apply hom_ext <;>
  simp only [Category.assoc, prodComparison_fst, tensorHom_fst, prodComparison_fst_assoc,
    prodComparison_snd, tensorHom_snd, prodComparison_snd_assoc, ← F.map_comp]

Depends on / 依赖: Category, Category.assoc, F.map_comp, hom_ext, map_comp, prodComparison_fst, prodComparison_fst_assoc, prodComparison_snd, prodComparison_snd_assoc, tensorHom_fst, tensorHom_snd
-/
theorem prodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    F.map (f otimesₘ g) ≫ prodComparison F A' B' =
      prodComparison F A B ≫ (F.map f otimesₘ F.map g) := by
  apply hom_ext <;>
  simp only [Category.assoc, prodComparison_fst, tensorHom_fst, prodComparison_fst_assoc,
    prodComparison_snd, tensorHom_snd, prodComparison_snd_assoc, ← F.map_comp]

/-- Naturality of the `prodComparison` morphism in the right argument. -/
@[reassoc]
/--
theorem `prodComparison_natural_whiskerLeft` / 定理 `prodComparison_natural_whiskerLeft`

English:
theorem prodComparison_natural_whiskerLeft
  given: (g : B ⟶ B')
  proof: by
  ext <;> simp [← Functor.map_comp]

中文:
定理 prodComparison_natural_whiskerLeft
  条件: (g : B ⟶ B')
  证明: by
  ext <;> simp [← Functor.map_comp]

Depends on / 依赖: Functor, Functor.map_comp, map_comp
-/
theorem prodComparison_natural_whiskerLeft (g : B ⟶ B') :
    F.map (A ◁ g) ≫ prodComparison F A B' =
      prodComparison F A B ≫ (F.obj A ◁ F.map g) := by
  ext <;> simp [← Functor.map_comp]

/-- Naturality of the `prodComparison` morphism in the left argument. -/
@[reassoc]
/--
theorem `prodComparison_natural_whiskerRight` / 定理 `prodComparison_natural_whiskerRight`

English:
theorem prodComparison_natural_whiskerRight
  given: (f : A ⟶ A')
  proof: by
  ext <;> simp [← Functor.map_comp]

中文:
定理 prodComparison_natural_whiskerRight
  条件: (f : A ⟶ A')
  证明: by
  ext <;> simp [← Functor.map_comp]

Depends on / 依赖: Functor, Functor.map_comp, map_comp
-/
theorem prodComparison_natural_whiskerRight (f : A ⟶ A') :
    F.map (f ▷ B) ≫ prodComparison F A' B =
      prodComparison F A B ≫ (F.map f ▷ F.obj B) := by
  ext <;> simp [← Functor.map_comp]

section
variable [IsIso (prodComparison F A B)]

/-- If the product comparison morphism is an iso, its inverse is natural in both argument. -/
@[reassoc]
/--
theorem `prodComparison_inv_natural` / 定理 `prodComparison_inv_natural`

English:
theorem prodComparison_inv_natural
  given: (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A' B')]
  proof: by
  rw [IsIso.eq_comp_inv]; rw [Category.assoc]; rw [IsIso.inv_comp_eq]; rw [prodComparison_natural]

中文:
定理 prodComparison_inv_natural
  条件: (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A' B')]
  证明: by
  rw [IsIso.eq_comp_inv]; rw [Category.assoc]; rw [IsIso.inv_comp_eq]; rw [prodComparison_natural]

Depends on / 依赖: Category, Category.assoc, IsIso.eq_comp_inv, IsIso.inv_comp_eq, eq_comp_inv, inv_comp_eq, prodComparison_natural
-/
theorem prodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A' B')] :
    inv (prodComparison F A B) ≫ F.map (f otimesₘ g) =
      (F.map f otimesₘ F.map g) ≫ inv (prodComparison F A' B') := by
  rw [IsIso.eq_comp_inv]; rw [Category.assoc]; rw [IsIso.inv_comp_eq]; rw [prodComparison_natural]

/-- If the product comparison morphism is an iso, its inverse is natural in the right argument. -/
@[reassoc]
/--
theorem `prodComparison_inv_natural_whiskerLeft` / 定理 `prodComparison_inv_natural_whiskerLeft`

English:
theorem prodComparison_inv_natural_whiskerLeft
  given: (g : B ⟶ B') [IsIso (prodComparison F A B')]
  proof: by
  rw [IsIso.eq_comp_inv]; rw [Category.assoc]; rw [IsIso.inv_comp_eq]; rw [prodComparison_natural_whiskerLeft]

中文:
定理 prodComparison_inv_natural_whiskerLeft
  条件: (g : B ⟶ B') [IsIso (prodComparison F A B')]
  证明: by
  rw [IsIso.eq_comp_inv]; rw [Category.assoc]; rw [IsIso.inv_comp_eq]; rw [prodComparison_natural_whiskerLeft]

Depends on / 依赖: Category, Category.assoc, IsIso.eq_comp_inv, IsIso.inv_comp_eq, eq_comp_inv, inv_comp_eq, prodComparison_natural_whiskerLeft
-/
theorem prodComparison_inv_natural_whiskerLeft (g : B ⟶ B') [IsIso (prodComparison F A B')] :
    inv (prodComparison F A B) ≫ F.map (A ◁ g) =
      (F.obj A ◁ F.map g) ≫ inv (prodComparison F A B') := by
  rw [IsIso.eq_comp_inv]; rw [Category.assoc]; rw [IsIso.inv_comp_eq]; rw [prodComparison_natural_whiskerLeft]

/-- If the product comparison morphism is an iso, its inverse is natural in the left argument. -/
@[reassoc]
/--
theorem `prodComparison_inv_natural_whiskerRight` / 定理 `prodComparison_inv_natural_whiskerRight`

English:
theorem prodComparison_inv_natural_whiskerRight
  given: (f : A ⟶ A') [IsIso (prodComparison F A' B)]
  proof: by
  rw [IsIso.eq_comp_inv]; rw [Category.assoc]; rw [IsIso.inv_comp_eq]; rw [prodComparison_natural_whiskerRight]

中文:
定理 prodComparison_inv_natural_whiskerRight
  条件: (f : A ⟶ A') [IsIso (prodComparison F A' B)]
  证明: by
  rw [IsIso.eq_comp_inv]; rw [Category.assoc]; rw [IsIso.inv_comp_eq]; rw [prodComparison_natural_whiskerRight]

Depends on / 依赖: Category, Category.assoc, IsIso.eq_comp_inv, IsIso.inv_comp_eq, eq_comp_inv, inv_comp_eq, prodComparison_natural_whiskerRight
-/
theorem prodComparison_inv_natural_whiskerRight (f : A ⟶ A') [IsIso (prodComparison F A' B)] :
    inv (prodComparison F A B) ≫ F.map (f ▷ B) =
      (F.map f ▷ F.obj B) ≫ inv (prodComparison F A' B) := by
  rw [IsIso.eq_comp_inv]; rw [Category.assoc]; rw [IsIso.inv_comp_eq]; rw [prodComparison_natural_whiskerRight]

end

set_option backward.defeqAttrib.useBackward true in
/--
lemma `prodComparison_comp` / 引理 `prodComparison_comp`

English:
lemma prodComparison_comp
  proof: by
  unfold prodComparison
  ext <;> simp [← G.map_comp]

@[simp]

中文:
引理 prodComparison_comp
  证明: by
  unfold prodComparison
  ext <;> simp [← G.map_comp]

@[simp]

Depends on / 依赖: G.map_comp, map_comp, prodComparison
-/
lemma prodComparison_comp :
    prodComparison (F ⋙ G) A B =
      G.map (prodComparison F A B) ≫ prodComparison G (F.obj A) (F.obj B) := by
  unfold prodComparison
  ext <;> simp [← G.map_comp]

@[simp]
/--
lemma `prodComparison_id` / 引理 `prodComparison_id`

English:
lemma prodComparison_id
  proof: lift_fst_snd

中文:
引理 prodComparison_id
  证明: lift_fst_snd

Depends on / 依赖: lift_fst_snd
-/
lemma prodComparison_id :
    prodComparison (𝟭 C) A B = 𝟙 (A otimes B) := lift_fst_snd

set_option backward.defeqAttrib.useBackward true in
/-- The product comparison morphism from `F(A ⊗ -)` to `FA ⊗ F-`, whose components are given by
`prodComparison`. -/
@[simps]
/--
Definition of `prodComparisonNatTrans` / `prodComparisonNatTrans` 的定义

English:
definition prodComparisonNatTrans
  signature: (A : C)
  body: prodComparison F A B
  naturality x y f := by
    apply hom_ext <;>
    simp only [Functor.comp_obj, curriedTensor_obj_obj,
      Functor.comp_map, curriedTensor_obj_map, Category.assoc, prodComparison_fst, whiskerLeft_fst,
      prodComparison_snd, prodComparison_snd_assoc, whiskerLeft_snd, ← F.map

中文:
定义 prodComparisonNatTrans
  签名: (A : C)
  定义体: prodComparison F A B
  naturality x y f := by
    apply hom_ext <;>
    simp only [Functor.comp_obj, curriedTensor_obj_obj,
      Functor.comp_map, curriedTensor_obj_map, Category.assoc, prodComparison_fst, whiskerLeft_fst,
      prodComparison_snd, prodComparison_snd_assoc, whiskerLeft_snd, ← F.map

Depends on / 依赖: prodComparison
-/
def prodComparisonNatTrans (A : C) :
    (curriedTensor C).obj A ⋙ F ⟶ F ⋙ (curriedTensor D).obj (F.obj A) where
  app B := prodComparison F A B
  naturality x y f := by
    apply hom_ext <;>
    simp only [Functor.comp_obj, curriedTensor_obj_obj,
      Functor.comp_map, curriedTensor_obj_map, Category.assoc, prodComparison_fst, whiskerLeft_fst,
      prodComparison_snd, prodComparison_snd_assoc, whiskerLeft_snd, ← F.map_comp]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `prodComparisonNatTrans_comp` / 定理 `prodComparisonNatTrans_comp`

English:
theorem prodComparisonNatTrans_comp
  proof: by
  ext; simp [prodComparison_comp]

中文:
定理 prodComparisonNatTrans_comp
  证明: by
  ext; simp [prodComparison_comp]

Depends on / 依赖: prodComparison_comp
-/
theorem prodComparisonNatTrans_comp :
    prodComparisonNatTrans (F ⋙ G) A = Functor.whiskerRight (prodComparisonNatTrans F A) G ≫
      Functor.whiskerLeft F (prodComparisonNatTrans G (F.obj A)) := by
  ext; simp [prodComparison_comp]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `prodComparisonNatTrans_id` / 引理 `prodComparisonNatTrans_id`

English:
lemma prodComparisonNatTrans_id
  proof: by ext; simp

中文:
引理 prodComparisonNatTrans_id
  证明: by ext; simp
-/
lemma prodComparisonNatTrans_id :
    prodComparisonNatTrans (𝟭 C) A = 𝟙 _ := by ext; simp

set_option backward.defeqAttrib.useBackward true in
/-- The product comparison morphism from `F(- ⊗ -)` to `F- ⊗ F-`, whose components are given by
`prodComparison`. -/
@[simps]
/--
Definition of `prodComparisonBifunctorNatTrans` / `prodComparisonBifunctorNatTrans` 的定义

English:
definition prodComparisonBifunctorNatTrans
  signature: :
  body: prodComparisonNatTrans F A
  naturality x y f := by
    ext z
    apply hom_ext <;> simp [← Functor.map_comp]

中文:
定义 prodComparisonBifunctorNatTrans
  签名: :
  定义体: prodComparisonNatTrans F A
  naturality x y f := by
    ext z
    apply hom_ext <;> simp [← Functor.map_comp]

Depends on / 依赖: prodComparisonNatTrans
-/
def prodComparisonBifunctorNatTrans :
    curriedTensor C ⋙ (Functor.whiskeringRight _ _ _).obj F ⟶
      F ⋙ curriedTensor D ⋙ (Functor.whiskeringLeft _ _ _).obj F where
  app A := prodComparisonNatTrans F A
  naturality x y f := by
    ext z
    apply hom_ext <;> simp [← Functor.map_comp]

variable {E : Type u₂} [Category.{v₂} E] [CartesianMonoidalCategory E] (G : D ⥤ E)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `prodComparisonBifunctorNatTrans_comp` / 定理 `prodComparisonBifunctorNatTrans_comp`

English:
theorem prodComparisonBifunctorNatTrans_comp
  statement: prodComparisonBifunctorNatTrans (F ⋙ G) =
  proof: by
  ext; simp [prodComparison_comp]

中文:
定理 prodComparisonBifunctorNatTrans_comp
  结论: prodComparisonBifunctor自然数Trans (F ⋙ G) =
  证明: by
  ext; simp [prodComparison_comp]

Depends on / 依赖: prodComparison_comp
-/
theorem prodComparisonBifunctorNatTrans_comp : prodComparisonBifunctorNatTrans (F ⋙ G) =
    Functor.whiskerRight
      (prodComparisonBifunctorNatTrans F) ((Functor.whiskeringRight _ _ _).obj G) ≫
        Functor.whiskerLeft F (Functor.whiskerRight (prodComparisonBifunctorNatTrans G)
          ((Functor.whiskeringLeft _ _ _).obj F)) := by
  ext; simp [prodComparison_comp]

instance (A : C) [forall B, IsIso (prodComparison F A B)] : IsIso (prodComparisonNatTrans F A) := by
  let : forall X, IsIso ((prodComparisonNatTrans F A).app X) := by assumption
  apply NatIso.isIso_of_isIso_app

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: A B, IsIso (prodComparison F A B)] : IsIso (prodComparisonBifunctorNatTrans F)
  body: by
  let : forall X, IsIso ((prodComparisonBifunctorNatTrans F).app X) :=
    fun _ => by dsimp; apply NatIso.isIso_of_isIso_app
  apply NatIso.isIso_of_isIso_app

中文:
实例 [forall
  签名: A B, IsIso (prodComparison F A B)] : IsIso (prodComparisonBifunctor自然数Trans F)
  定义体: by
  let : forall X, IsIso ((prodComparisonBifunctorNatTrans F).app X) :=
    fun _ => by dsimp; apply NatIso.isIso_of_isIso_app
  apply NatIso.isIso_of_isIso_app

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, isIso_of_isIso_app, prodComparisonBifunctorNatTrans
-/
instance [forall A B, IsIso (prodComparison F A B)] : IsIso (prodComparisonBifunctorNatTrans F) := by
  let : forall X, IsIso ((prodComparisonBifunctorNatTrans F).app X) :=
    fun _ => by dsimp; apply NatIso.isIso_of_isIso_app
  apply NatIso.isIso_of_isIso_app

open Limits
section PreservesLimitPairs

section
variable (A B)
variable [PreservesLimit (pair A B) F]

/--
Definition of `isLimitCartesianMonoidalCategoryOfPreservesLimits` / `isLimitCartesianMonoidalCategoryOfPreservesLimits` 的定义

English:
definition isLimitCartesianMonoidalCategoryOfPreservesLimits
  signature: :
  body: mapIsLimitOfPreservesOfIsLimit F (fst _ _) (snd _ _)
(tensorProductIsBinaryProduct A B).ofIsoLimit
      isoBinaryFanMk (BinaryFan.mk (fst A B) (snd A B))

中文:
定义 isLimitCartesianMonoidalCategoryOfPreservesLimits
  签名: :
  定义体: mapIsLimitOfPreservesOfIsLimit F (fst _ _) (snd _ _)
(tensorProductIsBinaryProduct A B).ofIsoLimit
      isoBinaryFanMk (BinaryFan.mk (fst A B) (snd A B))

Depends on / 依赖: BinaryFan, BinaryFan.mk, isoBinaryFanMk, mapIsLimitOfPreservesOfIsLimit, ofIsoLimit, tensorProductIsBinaryProduct
-/
noncomputable def isLimitCartesianMonoidalCategoryOfPreservesLimits :
IsLimit BinaryFan.mk (F.map (fst A B)) (F.map (snd A B)) :=
mapIsLimitOfPreservesOfIsLimit F (fst _ _) (snd _ _)
(tensorProductIsBinaryProduct A B).ofIsoLimit
      isoBinaryFanMk (BinaryFan.mk (fst A B) (snd A B))

/--
Definition of `prodComparisonIso` / `prodComparisonIso` 的定义

English:
definition prodComparisonIso
  signature: : F.obj (A otimes B) ≅ F.obj A otimes F.obj B
  body: IsLimit.conePointUniqueUpToIso (isLimitCartesianMonoidalCategoryOfPreservesLimits F A B)
    (tensorProductIsBinaryProduct _ _)

@[simp]

中文:
定义 prodComparisonIso
  签名: : F.obj (A otimes B) ≅ F.obj A otimes F.obj B
  定义体: IsLimit.conePointUniqueUpToIso (isLimitCartesianMonoidalCategoryOfPreservesLimits F A B)
    (tensorProductIsBinaryProduct _ _)

@[simp]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, isLimitCartesianMonoidalCategoryOfPreservesLimits, tensorProductIsBinaryProduct
-/
noncomputable def prodComparisonIso : F.obj (A otimes B) ≅ F.obj A otimes F.obj B :=
  IsLimit.conePointUniqueUpToIso (isLimitCartesianMonoidalCategoryOfPreservesLimits F A B)
    (tensorProductIsBinaryProduct _ _)

@[simp]
/--
lemma `prodComparisonIso_hom` / 引理 `prodComparisonIso_hom`

English:
lemma prodComparisonIso_hom
  statement: (prodComparisonIso F A B).hom = prodComparison F A B
  proof: rfl

中文:
引理 prodComparisonIso_hom
  结论: (prodComparisonIso F A B).hom = prodComparison F A B
  证明: rfl
-/
lemma prodComparisonIso_hom : (prodComparisonIso F A B).hom = prodComparison F A B :=
  rfl

/--
Instance `isIso_prodComparison_of_preservesLimit_pair` / 实例 `isIso_prodComparison_of_preservesLimit_pair`

English:
instance isIso_prodComparison_of_preservesLimit_pair
  signature: : IsIso (prodComparison F A B)
  body: by
  rw [← prodComparisonIso_hom]
  infer_instance

中文:
实例 isIso_prodComparison_of_preservesLimit_pair
  签名: : IsIso (prodComparison F A B)
  定义体: by
  rw [← prodComparisonIso_hom]
  infer_instance

Depends on / 依赖: infer_instance, prodComparisonIso_hom
-/
instance isIso_prodComparison_of_preservesLimit_pair : IsIso (prodComparison F A B) := by
  rw [← prodComparisonIso_hom]
  infer_instance

/--
lemma `prodComparisonIso_id` / 引理 `prodComparisonIso_id`

English:
lemma prodComparisonIso_id
  statement: prodComparisonIso (𝟭 C) A B = .refl _
  proof: by ext <;> simp

中文:
引理 prodComparisonIso_id
  结论: prodComparisonIso (𝟭 C) A B = .refl _
  证明: by ext <;> simp
-/
@[simp] lemma prodComparisonIso_id : prodComparisonIso (𝟭 C) A B = .refl _ := by ext <;> simp

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `prodComparisonIso_comp` / 引理 `prodComparisonIso_comp`

English:
lemma prodComparisonIso_comp
  statement: [PreservesLimit (pair A B) (F ⋙ G)]
  proof: by
  ext <;> simp [CartesianMonoidalCategory.prodComparison, ← G.map_comp]

中文:
引理 prodComparisonIso_comp
  结论: [PreservesLimit (pair A B) (F ⋙ G)]
  证明: by
  ext <;> simp [CartesianMonoidalCategory.prodComparison, ← G.map_comp]

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.prodComparison, G.map_comp, map_comp, prodComparison
-/
lemma prodComparisonIso_comp [PreservesLimit (pair A B) (F ⋙ G)]
    [PreservesLimit (pair (F.obj A) (F.obj B)) G] :
    prodComparisonIso (F ⋙ G) A B =
      G.mapIso (prodComparisonIso F A B) ≪≫ prodComparisonIso G (F.obj A) (F.obj B) := by
  ext <;> simp [CartesianMonoidalCategory.prodComparison, ← G.map_comp]

end

/-- The natural isomorphism `F(A ⊗ -) ≅ FA ⊗ F-`, provided each `prodComparison F A B` is an
isomorphism (as `B` changes). -/
@[simps! hom inv]
/--
Definition of `prodComparisonNatIso` / `prodComparisonNatIso` 的定义

English:
definition prodComparisonNatIso
  signature: (A : C) [forall B, PreservesLimit (pair A B) F]
  body: asIso (prodComparisonNatTrans F A)

中文:
定义 prodComparisonNatIso
  签名: (A : C) [对任意 B, PreservesLimit (pair A B) F]
  定义体: asIso (prodComparisonNatTrans F A)

Depends on / 依赖: prodComparisonNatTrans
-/
noncomputable def prodComparisonNatIso (A : C) [forall B, PreservesLimit (pair A B) F] :
    (curriedTensor C).obj A ⋙ F ≅ F ⋙ (curriedTensor D).obj (F.obj A) :=
  asIso (prodComparisonNatTrans F A)

/-- The natural isomorphism of bifunctors `F(- ⊗ -) ≅ F- ⊗ F-`, provided each
`prodComparison F A B` is an isomorphism. -/
@[simps! hom inv]
/--
Definition of `prodComparisonBifunctorNatIso` / `prodComparisonBifunctorNatIso` 的定义

English:
definition prodComparisonBifunctorNatIso
  signature: [forall A B, PreservesLimit (pair A B) F]
  body: asIso (prodComparisonBifunctorNatTrans F)

中文:
定义 prodComparisonBifunctorNatIso
  签名: [对任意 A B, PreservesLimit (pair A B) F]
  定义体: asIso (prodComparisonBifunctorNatTrans F)

Depends on / 依赖: prodComparisonBifunctorNatTrans
-/
noncomputable def prodComparisonBifunctorNatIso [forall A B, PreservesLimit (pair A B) F] :
    curriedTensor C ⋙ (Functor.whiskeringRight _ _ _).obj F ≅
      F ⋙ curriedTensor D ⋙ (Functor.whiskeringLeft _ _ _).obj F :=
  asIso (prodComparisonBifunctorNatTrans F)

end PreservesLimitPairs

section ProdComparisonIso

set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesLimit_pair_of_isIso_prodComparison` / 引理 `preservesLimit_pair_of_isIso_prodComparison`

English:
lemma preservesLimit_pair_of_isIso_prodComparison
  statement: (A B : C)
  proof: by
  apply preservesLimit_of_preserves_limit_cone (tensorProductIsBinaryProduct A B)
  refine IsLimit.equivOfNatIsoOfIso (pairComp A B F) _
    ((BinaryFan.mk (fst (F.obj A) (F.obj B)) (snd _ _)).extend (prodComparison F A B))
.invFun (BinaryFan.ext (by exact Iso.refl _) ?_ ?_)
      (IsLimit.extend

中文:
引理 preservesLimit_pair_of_isIso_prodComparison
  结论: (A B : C)
  证明: by
  apply preservesLimit_of_preserves_limit_cone (tensorProductIsBinaryProduct A B)
  refine IsLimit.equivOfNatIsoOfIso (pairComp A B F) _
    ((BinaryFan.mk (fst (F.obj A) (F.obj B)) (snd _ _)).extend (prodComparison F A B))
.invFun (BinaryFan.ext (by exact Iso.refl _) ?_ ?_)
      (IsLimit.extend

Depends on / 依赖: BinaryFan, BinaryFan.ext, BinaryFan.fst, BinaryFan.mk, BinaryFan.snd, F.obj, IsLimit, IsLimit.equivOfNatIsoOfIso, IsLimit.extendIso, Iso.refl, equivOfNatIsoOfIso, extend, extendIso, invFun, mem_toPrecoverage_iff, pairComp, preservesLimit_of_preserves_limit_cone, prodComparison, tensorProductIsBinaryProduct
-/
lemma preservesLimit_pair_of_isIso_prodComparison (A B : C)
    [IsIso (prodComparison F A B)] :
    PreservesLimit (pair A B) F := by
  apply preservesLimit_of_preserves_limit_cone (tensorProductIsBinaryProduct A B)
  refine IsLimit.equivOfNatIsoOfIso (pairComp A B F) _
    ((BinaryFan.mk (fst (F.obj A) (F.obj B)) (snd _ _)).extend (prodComparison F A B))
.invFun (BinaryFan.ext (by exact Iso.refl _) ?_ ?_)
      (IsLimit.extendIso _ (tensorProductIsBinaryProduct (F.obj A) (F.obj B)))
  · dsimp only [BinaryFan.fst]
    simp [pairComp]
  · dsimp only [BinaryFan.snd]
    simp [pairComp]

/--
lemma `preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison` / 引理 `preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison`

English:
lemma preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison
  proof: by
  constructor
  intro K
  refine @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoPair K).symm ?_
  apply preservesLimit_pair_of_isIso_prodComparison

中文:
引理 preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison
  证明: by
  constructor
  intro K
  refine @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoPair K).symm ?_
  apply preservesLimit_pair_of_isIso_prodComparison

Depends on / 依赖: J.bindOfArrows, Presieve, Presieve.bindOfArrows_ofArrows, bindOfArrows, bindOfArrows_ofArrows, diagramIsoPair, mem_toPrecoverage_iff, preservesLimit_of_iso_diagram, preservesLimit_pair_of_isIso_prodComparison
-/
lemma preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison
    [forall A B, IsIso (prodComparison F A B)] : PreservesLimitsOfShape (Discrete WalkingPair) F := by
  constructor
  intro K
  refine @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoPair K).symm ?_
  apply preservesLimit_pair_of_isIso_prodComparison

end ProdComparisonIso

end prodComparison

end CartesianMonoidalCategoryComparison

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `tensorLeftIsoProd` / `tensorLeftIsoProd` 的定义

English:
definition tensorLeftIsoProd
  signature: [HasBinaryProducts C] (X : C)
  body: NatIso.ofComponents fun Y =>
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso
      (limit.isLimit _)

中文:
定义 tensorLeftIsoProd
  签名: [HasBinaryProducts C] (X : C)
  定义体: NatIso.ofComponents fun Y =>
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso
      (limit.isLimit _)

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.tensorProductIsBinaryProduct, J.pullback_stable, NatIso, NatIso.ofComponents, Sieve.ofArrows, Sieve.ofArrows_eq_pullback_of_isPullback, conePointUniqueUpToIso, isLimit, limit.isLimit, mem_toPrecoverage_iff, ofArrows, ofArrows_eq_pullback_of_isPullback, ofComponents, pullback_stable, tensorProductIsBinaryProduct
-/
noncomputable def tensorLeftIsoProd [HasBinaryProducts C] (X : C) :
    MonoidalCategory.tensorLeft X ≅ prod.functor.obj X :=
  NatIso.ofComponents fun Y =>
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso
      (limit.isLimit _)

open Limits

variable {P : ObjectProperty C}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
-- TODO: Introduce `ClosedUnderFiniteProducts`?
/-- The restriction of a Cartesian-monoidal category along an object property that's closed under
finite products is Cartesian-monoidal. -/
@[simps!]
/--
Instance `fullSubcategory` / 实例 `fullSubcategory`

English:
instance fullSubcategory
  body: MonoidalCategory.fullSubcategory P
      (P.prop_of_isLimit isTerminalTensorUnit (by simp))
      (fun X Y hX hY => P.prop_of_isLimit (tensorProductIsBinaryProduct X Y)
        (by rintro (_ | _) <;> assumption))
  isTerminalTensorUnit := .ofUniqueHom (fun X => ObjectProperty.homMk (toUnit X.1))
   

中文:
实例 fullSubcategory
  定义体: MonoidalCategory.fullSubcategory P
      (P.prop_of_isLimit isTerminalTensorUnit (by simp))
      (fun X Y hX hY => P.prop_of_isLimit (tensorProductIsBinaryProduct X Y)
        (by rintro (_ | _) <;> assumption))
  isTerminalTensorUnit := .ofUniqueHom (fun X => ObjectProperty.homMk (toUnit X.1))
   

Depends on / 依赖: MonoidalCategory, MonoidalCategory.fullSubcategory, fullSubcategory
-/
instance fullSubcategory
    [P.IsClosedUnderLimitsOfShape (Discrete PEmpty)]
    [P.IsClosedUnderLimitsOfShape (Discrete WalkingPair)] :
    CartesianMonoidalCategory P.FullSubcategory where
  __ := MonoidalCategory.fullSubcategory P
      (P.prop_of_isLimit isTerminalTensorUnit (by simp))
      (fun X Y hX hY => P.prop_of_isLimit (tensorProductIsBinaryProduct X Y)
        (by rintro (_ | _) <;> assumption))
  isTerminalTensorUnit := .ofUniqueHom (fun X => ObjectProperty.homMk (toUnit X.1))
    fun _ _ => by ext; apply toUnit_unique
  fst X Y := ObjectProperty.homMk (fst X.1 Y.1)
  snd X Y := ObjectProperty.homMk (snd X.1 Y.1)
  tensorProductIsBinaryProduct X Y :=
    BinaryFan.IsLimit.mk _ (fun f g => ObjectProperty.homMk (lift f.hom g.hom))
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  fst_def X Y := by ext; exact fst_def X.1 Y.1
  snd_def X Y := by ext; exact snd_def X.1 Y.1

end CartesianMonoidalCategory

open MonoidalCategory CartesianMonoidalCategory

variable
  {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [CartesianMonoidalCategory E]
  (F : C ⥤ D) (G : D ⥤ E) {X Y Z : C}

open Functor.LaxMonoidal Functor.OplaxMonoidal
open Limits (PreservesFiniteProducts)

namespace Functor.OplaxMonoidal
variable [F.OplaxMonoidal]

/--
lemma `η_of_cartesianMonoidalCategory` / 引理 `η_of_cartesianMonoidalCategory`

English:
lemma η_of_cartesianMonoidalCategory
  proof: toUnit_unique ..

@[reassoc (attr := simp)]

中文:
引理 η_of_cartesianMonoidalCategory
  证明: toUnit_unique ..

@[reassoc (attr := simp)]

Depends on / 依赖: toUnit_unique
-/
lemma η_of_cartesianMonoidalCategory :
    η F = CartesianMonoidalCategory.terminalComparison F := toUnit_unique ..

@[reassoc (attr := simp)]
/--
lemma `δ_fst` / 引理 `δ_fst`

English:
lemma δ_fst
  given: (X Y : C)
  proof: by
  trans F.map (X ◁ toUnit Y) ≫ F.map (ρ_ X).hom
  · rw [← whiskerLeft_fst _ (F.map (toUnit Y)), δ_natural_right_assoc]
    simp [← OplaxMonoidal.right_unitality_hom, rightUnitor_hom (F.obj X)]
  · simp [← Functor.map_comp, rightUnitor_hom]

@[reassoc (attr := simp)]

中文:
引理 δ_fst
  条件: (X Y : C)
  证明: by
  trans F.map (X ◁ toUnit Y) ≫ F.map (ρ_ X).hom
  · rw [← whiskerLeft_fst _ (F.map (toUnit Y)), δ_natural_right_assoc]
    simp [← OplaxMonoidal.right_unitality_hom, rightUnitor_hom (F.obj X)]
  · simp [← Functor.map_comp, rightUnitor_hom]

@[reassoc (attr := simp)]

Depends on / 依赖: F.map, F.obj, Functor, Functor.map_comp, OplaxMonoidal, OplaxMonoidal.right_unitality_hom, map_comp, rightUnitor_hom, right_unitality_hom, toUnit, whiskerLeft_fst
-/
lemma δ_fst (X Y : C) :
    δ F X Y ≫ fst _ _ = F.map (fst _ _) := by
  trans F.map (X ◁ toUnit Y) ≫ F.map (ρ_ X).hom
  · rw [← whiskerLeft_fst _ (F.map (toUnit Y)), δ_natural_right_assoc]
    simp [← OplaxMonoidal.right_unitality_hom, rightUnitor_hom (F.obj X)]
  · simp [← Functor.map_comp, rightUnitor_hom]

@[reassoc (attr := simp)]
/--
lemma `δ_snd` / 引理 `δ_snd`

English:
lemma δ_snd
  given: (X Y : C)
  proof: by
  trans F.map (toUnit X ▷ Y) ≫ F.map (fun_ Y).hom
  · rw [← whiskerRight_snd (F.map (toUnit X)), δ_natural_left_assoc]
    simp [← OplaxMonoidal.left_unitality_hom, leftUnitor_hom (F.obj Y)]
  · simp [← Functor.map_comp, leftUnitor_hom]

@[reassoc (attr := simp)]

中文:
引理 δ_snd
  条件: (X Y : C)
  证明: by
  trans F.map (toUnit X ▷ Y) ≫ F.map (fun_ Y).hom
  · rw [← whiskerRight_snd (F.map (toUnit X)), δ_natural_left_assoc]
    simp [← OplaxMonoidal.left_unitality_hom, leftUnitor_hom (F.obj Y)]
  · simp [← Functor.map_comp, leftUnitor_hom]

@[reassoc (attr := simp)]

Depends on / 依赖: F.map, F.obj, Functor, Functor.map_comp, OplaxMonoidal, OplaxMonoidal.left_unitality_hom, fun_, leftUnitor_hom, left_unitality_hom, map_comp, toUnit, whiskerRight_snd
-/
lemma δ_snd (X Y : C) :
    δ F X Y ≫ snd _ _ = F.map (snd _ _) := by
  trans F.map (toUnit X ▷ Y) ≫ F.map (fun_ Y).hom
  · rw [← whiskerRight_snd (F.map (toUnit X)), δ_natural_left_assoc]
    simp [← OplaxMonoidal.left_unitality_hom, leftUnitor_hom (F.obj Y)]
  · simp [← Functor.map_comp, leftUnitor_hom]

@[reassoc (attr := simp)]
/--
lemma `lift_δ` / 引理 `lift_δ`

English:
lemma lift_δ
  given: (f : X ⟶ Y) (g : X ⟶ Z)
  statement: F.map (lift f g) ≫ δ F _ _ = lift (F.map f) (F.map g)
  proof: by
  ext <;> simp [← map_comp]

中文:
引理 lift_δ
  条件: (f : X ⟶ Y) (g : X ⟶ Z)
  结论: F.map (lift f g) ≫ δ F _ _ = lift (F.map f) (F.map g)
  证明: by
  ext <;> simp [← map_comp]

Depends on / 依赖: map_comp
-/
lemma lift_δ (f : X ⟶ Y) (g : X ⟶ Z) : F.map (lift f g) ≫ δ F _ _ = lift (F.map f) (F.map g) := by
  ext <;> simp [← map_comp]

/--
lemma `δ_of_cartesianMonoidalCategory` / 引理 `δ_of_cartesianMonoidalCategory`

English:
lemma δ_of_cartesianMonoidalCategory
  given: (X Y : C)
  proof: by cat_disch

中文:
引理 δ_of_cartesianMonoidalCategory
  条件: (X Y : C)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma δ_of_cartesianMonoidalCategory (X Y : C) :
    δ F X Y = CartesianMonoidalCategory.prodComparison F X Y := by cat_disch

variable [PreservesFiniteProducts F]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (η F)
  body: η_of_cartesianMonoidalCategory F ▸ terminalComparison_isIso_of_preservesLimits F

中文:
实例 :
  签名: IsIso (η F)
  定义体: η_of_cartesianMonoidalCategory F ▸ terminalComparison_isIso_of_preservesLimits F

Depends on / 依赖: terminalComparison_isIso_of_preservesLimits
-/
instance : IsIso (η F) :=
  η_of_cartesianMonoidalCategory F ▸ terminalComparison_isIso_of_preservesLimits F

instance (X Y : C) : IsIso (δ F X Y) :=
  δ_of_cartesianMonoidalCategory F X Y ▸ isIso_prodComparison_of_preservesLimit_pair F X Y

omit [F.OplaxMonoidal] in
/-- Any functor between Cartesian-monoidal categories is oplax monoidal.

This is not made an instance because it would create a diamond for the oplax monoidal structure on
the identity and composition of functors. -/
@[instance_reducible]
/--
Definition of `ofChosenFiniteProducts` / `ofChosenFiniteProducts` 的定义

English:
definition ofChosenFiniteProducts
  signature: (F : C ⥤ D)
  body: terminalComparison F
  δ X Y := prodComparison F X Y
  δ_natural_left f X := by ext <;> simp [← Functor.map_comp]
  δ_natural_right X g := by ext <;> simp [← Functor.map_comp]
  oplax_associativity _ _ _ := by ext <;> simp [← Functor.map_comp]
  oplax_left_unitality _ := by ext; simp [← Functor.map_

中文:
定义 ofChosenFiniteProducts
  签名: (F : C ⥤ D)
  定义体: terminalComparison F
  δ X Y := prodComparison F X Y
  δ_natural_left f X := by ext <;> simp [← Functor.map_comp]
  δ_natural_right X g := by ext <;> simp [← Functor.map_comp]
  oplax_associativity _ _ _ := by ext <;> simp [← Functor.map_comp]
  oplax_left_unitality _ := by ext; simp [← Functor.map_

Depends on / 依赖: terminalComparison
-/
def ofChosenFiniteProducts (F : C ⥤ D) : F.OplaxMonoidal where
  η := terminalComparison F
  δ X Y := prodComparison F X Y
  δ_natural_left f X := by ext <;> simp [← Functor.map_comp]
  δ_natural_right X g := by ext <;> simp [← Functor.map_comp]
  oplax_associativity _ _ _ := by ext <;> simp [← Functor.map_comp]
  oplax_left_unitality _ := by ext; simp [← Functor.map_comp]
  oplax_right_unitality _ := by ext; simp [← Functor.map_comp]

omit [F.OplaxMonoidal] in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton F.OplaxMonoidal
  body: by
    ext1
    · exact toUnit_unique _ _
    · ext1; ext1; rw [δ_of_cartesianMonoidalCategory, δ_of_cartesianMonoidalCategory]

中文:
实例 :
  签名: Subsingleton F.OplaxMonoidal
  定义体: by
    ext1
    · exact toUnit_unique _ _
    · ext1; ext1; rw [δ_of_cartesianMonoidalCategory, δ_of_cartesianMonoidalCategory]

Depends on / 依赖: toUnit_unique
-/
instance : Subsingleton F.OplaxMonoidal where
  allEq a b := by
    ext1
    · exact toUnit_unique _ _
    · ext1; ext1; rw [δ_of_cartesianMonoidalCategory, δ_of_cartesianMonoidalCategory]

end OplaxMonoidal

namespace Monoidal
variable [F.Monoidal] [G.Monoidal]

@[reassoc (attr := simp)]
/--
lemma `toUnit_ε` / 引理 `toUnit_ε`

English:
lemma toUnit_ε
  given: (X : C)
  statement: toUnit (F.obj X) ≫ ε F = F.map (toUnit X)
  proof: by
  rw [← cancel_mono (εIso F).inv]; exact toUnit_unique ..

@[reassoc (attr := simp)]

中文:
引理 toUnit_ε
  条件: (X : C)
  结论: toUnit (F.obj X) ≫ ε F = F.map (toUnit X)
  证明: by
  rw [← cancel_mono (εIso F).inv]; exact toUnit_unique ..

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_mono, toUnit_unique
-/
lemma toUnit_ε (X : C) : toUnit (F.obj X) ≫ ε F = F.map (toUnit X) := by
  rw [← cancel_mono (εIso F).inv]; exact toUnit_unique ..

@[reassoc (attr := simp)]
/--
lemma `lift_μ` / 引理 `lift_μ`

English:
lemma lift_μ
  given: (f : X ⟶ Y) (g : X ⟶ Z)
  statement: lift (F.map f) (F.map g) ≫ μ F _ _ = F.map (lift f g)
  proof: (cancel_mono (μIso _ _ _).inv).1 (by simp)

@[reassoc (attr := simp)]

中文:
引理 lift_μ
  条件: (f : X ⟶ Y) (g : X ⟶ Z)
  结论: lift (F.map f) (F.map g) ≫ μ F _ _ = F.map (lift f g)
  证明: (cancel_mono (μIso _ _ _).inv).1 (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_mono
-/
lemma lift_μ (f : X ⟶ Y) (g : X ⟶ Z) : lift (F.map f) (F.map g) ≫ μ F _ _ = F.map (lift f g) :=
  (cancel_mono (μIso _ _ _).inv).1 (by simp)

@[reassoc (attr := simp)]
/--
lemma `μ_fst` / 引理 `μ_fst`

English:
lemma μ_fst
  given: (X Y : C)
  statement: μ F X Y ≫ F.map (fst X Y) = fst (F.obj X) (F.obj Y)
  proof: (cancel_epi (μIso _ _ _).inv).1 (by simp)

@[reassoc (attr := simp)]

中文:
引理 μ_fst
  条件: (X Y : C)
  结论: μ F X Y ≫ F.map (fst X Y) = fst (F.obj X) (F.obj Y)
  证明: (cancel_epi (μIso _ _ _).inv).1 (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_epi
-/
lemma μ_fst (X Y : C) : μ F X Y ≫ F.map (fst X Y) = fst (F.obj X) (F.obj Y) :=
  (cancel_epi (μIso _ _ _).inv).1 (by simp)

@[reassoc (attr := simp)]
/--
lemma `μ_snd` / 引理 `μ_snd`

English:
lemma μ_snd
  given: (X Y : C)
  statement: μ F X Y ≫ F.map (snd X Y) = snd (F.obj X) (F.obj Y)
  proof: (cancel_epi (μIso _ _ _).inv).1 (by simp)

中文:
引理 μ_snd
  条件: (X Y : C)
  结论: μ F X Y ≫ F.map (snd X Y) = snd (F.obj X) (F.obj Y)
  证明: (cancel_epi (μIso _ _ _).inv).1 (by simp)

Depends on / 依赖: cancel_epi
-/
lemma μ_snd (X Y : C) : μ F X Y ≫ F.map (snd X Y) = snd (F.obj X) (F.obj Y) :=
  (cancel_epi (μIso _ _ _).inv).1 (by simp)

set_option backward.defeqAttrib.useBackward true in
attribute [-instance] Functor.LaxMonoidal.comp Functor.Monoidal.instComp in
@[reassoc]
/--
lemma `μ_comp` / 引理 `μ_comp`

English:
lemma μ_comp
  given: [(F ⋙ G).Monoidal] (X Y : C)
  statement: μ (F ⋙ G) X Y = μ G _ _ ≫ G.map (μ F X Y)
  proof: by
  rw [← cancel_mono (μIso _ _ _).inv]; ext <;> simp [← Functor.comp_obj, ← Functor.map_comp]

中文:
引理 μ_comp
  条件: [(F ⋙ G).Monoidal] (X Y : C)
  结论: μ (F ⋙ G) X Y = μ G _ _ ≫ G.map (μ F X Y)
  证明: by
  rw [← cancel_mono (μIso _ _ _).inv]; ext <;> simp [← Functor.comp_obj, ← Functor.map_comp]

Depends on / 依赖: Functor, Functor.comp_obj, Functor.map_comp, cancel_mono, comp_obj, map_comp
-/
lemma μ_comp [(F ⋙ G).Monoidal] (X Y : C) : μ (F ⋙ G) X Y = μ G _ _ ≫ G.map (μ F X Y) := by
  rw [← cancel_mono (μIso _ _ _).inv]; ext <;> simp [← Functor.comp_obj, ← Functor.map_comp]

variable [PreservesFiniteProducts F]

/--
lemma `ε_of_cartesianMonoidalCategory` / 引理 `ε_of_cartesianMonoidalCategory`

English:
lemma ε_of_cartesianMonoidalCategory
  statement: ε F = (preservesTerminalIso F).inv
  proof: by
  change (εIso F).symm.inv = _; congr; ext

中文:
引理 ε_of_cartesianMonoidalCategory
  结论: ε F = (preservesTerminalIso F).inv
  证明: by
  change (εIso F).symm.inv = _; congr; ext

Depends on / 依赖: symm.inv
-/
lemma ε_of_cartesianMonoidalCategory : ε F = (preservesTerminalIso F).inv := by
  change (εIso F).symm.inv = _; congr; ext

/--
lemma `μ_of_cartesianMonoidalCategory` / 引理 `μ_of_cartesianMonoidalCategory`

English:
lemma μ_of_cartesianMonoidalCategory
  given: (X Y : C)
  statement: μ F X Y = (prodComparisonIso F X Y).inv
  proof: by
  change (μIso F X Y).symm.inv = _; congr; ext : 1; simpa using δ_of_cartesianMonoidalCategory F X Y

中文:
引理 μ_of_cartesianMonoidalCategory
  条件: (X Y : C)
  结论: μ F X Y = (prodComparisonIso F X Y).inv
  证明: by
  change (μIso F X Y).symm.inv = _; congr; ext : 1; simpa using δ_of_cartesianMonoidalCategory F X Y

Depends on / 依赖: symm.inv
-/
lemma μ_of_cartesianMonoidalCategory (X Y : C) : μ F X Y = (prodComparisonIso F X Y).inv := by
  change (μIso F X Y).symm.inv = _; congr; ext : 1; simpa using δ_of_cartesianMonoidalCategory F X Y

attribute [local instance] Functor.OplaxMonoidal.ofChosenFiniteProducts in
omit [F.Monoidal] in
/-- A finite-product-preserving functor between Cartesian monoidal categories is monoidal.

This is not made an instance because it would create a diamond for the monoidal structure on
the identity and composition of functors. -/
@[instance_reducible]
/--
Definition of `ofChosenFiniteProducts` / `ofChosenFiniteProducts` 的定义

English:
definition ofChosenFiniteProducts
  signature: (F : C ⥤ D) [PreservesFiniteProducts F]
  body: .ofOplaxMonoidal F

中文:
定义 ofChosenFiniteProducts
  签名: (F : C ⥤ D) [PreservesFiniteProducts F]
  定义体: .ofOplaxMonoidal F

Depends on / 依赖: IsLimit, IsLimit.mapConeEquiv, J.yoneda.mapCocone, J.yonedaOpCompCoyoneda, X.obj, c.op, coyoneda, coyoneda.mapCone, evaluation, evaluationJointlyReflectsLimits, hc.op, isColimitOfOp, isLimitOfPreserves, isLimitOfReflects, isoWhiskerRight, mapCocone, mapCone, mapConeEquiv, ofOplaxMonoidal, uliftFunctor
-/
noncomputable def ofChosenFiniteProducts (F : C ⥤ D) [PreservesFiniteProducts F] : F.Monoidal :=
  .ofOplaxMonoidal F

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton F.Monoidal
  body: (toOplaxMonoidal_injective F).subsingleton

中文:
实例 :
  签名: Subsingleton F.Monoidal
  定义体: (toOplaxMonoidal_injective F).subsingleton

Depends on / 依赖: subsingleton, toOplaxMonoidal_injective
-/
instance : Subsingleton F.Monoidal := (toOplaxMonoidal_injective F).subsingleton

end Monoidal

namespace Monoidal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.Monoidal]
  signature: : PreservesFiniteProducts F
  body: have (A B : _) : IsIso (CartesianMonoidalCategory.prodComparison F A B) :=
    δ_of_cartesianMonoidalCategory F A B ▸ inferInstance
  have : IsIso (CartesianMonoidalCategory.terminalComparison F) :=
    η_of_cartesianMonoidalCategory F ▸ inferInstance
  have := preservesLimitsOfShape_discrete_walkin

中文:
实例 [F.Monoidal]
  签名: : PreservesFiniteProducts F
  定义体: have (A B : _) : IsIso (CartesianMonoidalCategory.prodComparison F A B) :=
    δ_of_cartesianMonoidalCategory F A B ▸ inferInstance
  have : IsIso (CartesianMonoidalCategory.terminalComparison F) :=
    η_of_cartesianMonoidalCategory F ▸ inferInstance
  have := preservesLimitsOfShape_discrete_walkin

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.prodComparison, CartesianMonoidalCategory.terminalComparison, IsLimit, IsLimit.mapConeEquiv, J.uliftYoneda.mapCocone, J.uliftYonedaOpCompCoyoneda, Limits, Limits.preservesLimitsOfShape_pempty_of_preservesTerminal, X.obj, c.op, coyoneda, coyoneda.mapCone, evaluation, evaluationJointlyReflectsLimits, hc.op, isColimitOfOp, isLimitOfPreserves, isLimitOfReflects, isoWhiskerRight
-/
instance [F.Monoidal] : PreservesFiniteProducts F :=
  have (A B : _) : IsIso (CartesianMonoidalCategory.prodComparison F A B) :=
    δ_of_cartesianMonoidalCategory F A B ▸ inferInstance
  have : IsIso (CartesianMonoidalCategory.terminalComparison F) :=
    η_of_cartesianMonoidalCategory F ▸ inferInstance
  have := preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison F
  have := preservesLimit_empty_of_isIso_terminalComparison F
  have := Limits.preservesLimitsOfShape_pempty_of_preservesTerminal F
  .of_preserves_binary_and_terminal _

attribute [local instance] OplaxMonoidal.ofChosenFiniteProducts in
/--
lemma `nonempty_monoidal_iff_preservesFiniteProducts` / 引理 `nonempty_monoidal_iff_preservesFiniteProducts`

English:
lemma nonempty_monoidal_iff_preservesFiniteProducts
  proof: ⟨fun ⟨_⟩ => inferInstance, fun _ => ⟨ofChosenFiniteProducts F⟩⟩

中文:
引理 nonempty_monoidal_iff_preservesFiniteProducts
  证明: ⟨fun ⟨_⟩ => inferInstance, fun _ => ⟨ofChosenFiniteProducts F⟩⟩

Depends on / 依赖: ofChosenFiniteProducts
-/
lemma nonempty_monoidal_iff_preservesFiniteProducts :
    Nonempty F.Monoidal ↔ PreservesFiniteProducts F :=
  ⟨fun ⟨_⟩ => inferInstance, fun _ => ⟨ofChosenFiniteProducts F⟩⟩

end Monoidal

namespace Braided
variable [BraidedCategory C] [BraidedCategory D]

attribute [local instance] Functor.Monoidal.ofChosenFiniteProducts in
/-- A finite-product-preserving functor between Cartesian monoidal categories is braided.

This is not made an instance because it would create a diamond for the monoidal structure on
the identity and composition of functors. -/
@[instance_reducible]
/--
Definition of `ofChosenFiniteProducts` / `ofChosenFiniteProducts` 的定义

English:
definition ofChosenFiniteProducts
  signature: (F : C ⥤ D) [PreservesFiniteProducts F]
  body: by rw [← cancel_mono (Monoidal.μIso _ _ _).inv]; ext <;> simp [← F.map_comp]

中文:
定义 ofChosenFiniteProducts
  签名: (F : C ⥤ D) [PreservesFiniteProducts F]
  定义体: by rw [← cancel_mono (Monoidal.μIso _ _ _).inv]; ext <;> simp [← F.map_comp]

Depends on / 依赖: F.map_comp, Monoidal, cancel_mono, map_comp
-/
noncomputable def ofChosenFiniteProducts (F : C ⥤ D) [PreservesFiniteProducts F] : F.Braided where
  braided X Y := by rw [← cancel_mono (Monoidal.μIso _ _ _).inv]; ext <;> simp [← F.map_comp]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton F.Braided
  body: (Braided.toMonoidal_injective F).subsingleton

中文:
实例 :
  签名: Subsingleton F.Braided
  定义体: (Braided.toMonoidal_injective F).subsingleton

Depends on / 依赖: Braided, Braided.toMonoidal_injective, J.uliftYonedaIsoYoneda, preservesColimit_of_natIso, subsingleton, toMonoidal_injective, uliftYonedaIsoYoneda
-/
instance : Subsingleton F.Braided := (Braided.toMonoidal_injective F).subsingleton

end Braided

namespace EssImageSubcategory
variable [F.Full] [F.Faithful] [PreservesFiniteProducts F] {T X Y Z : F.EssImageSubcategory}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `tensor_obj` / 引理 `tensor_obj`

English:
lemma tensor_obj
  given: (X Y : F.EssImageSubcategory)
  statement: (X otimes Y).obj = X.obj otimes Y.obj
  proof: rfl

中文:
引理 tensor_obj
  条件: (X Y : F.EssImageSubcategory)
  结论: (X otimes Y).obj = X.obj otimes Y.obj
  证明: rfl
-/
lemma tensor_obj (X Y : F.EssImageSubcategory) : (X otimes Y).obj = X.obj otimes Y.obj := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `lift_def` / 引理 `lift_def`

English:
lemma lift_def
  given: (f : T ⟶ X) (g : T ⟶ Y)
  statement: lift f g = ObjectProperty.homMk (lift f.hom g.hom)
  proof: rfl

中文:
引理 lift_def
  条件: (f : T ⟶ X) (g : T ⟶ Y)
  结论: lift f g = Object命题erty.homMk (lift f.hom g.hom)
  证明: rfl
-/
lemma lift_def (f : T ⟶ X) (g : T ⟶ Y) : lift f g = ObjectProperty.homMk (lift f.hom g.hom) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `associator_hom_def` / 引理 `associator_hom_def`

English:
lemma associator_hom_def
  given: (X Y Z : F.EssImageSubcategory)
  proof: rfl

中文:
引理 associator_hom_def
  条件: (X Y Z : F.EssImageSubcategory)
  证明: rfl
-/
lemma associator_hom_def (X Y Z : F.EssImageSubcategory) :
    (α_ X Y Z).hom = ObjectProperty.homMk (α_ X.obj Y.obj Z.obj).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `associator_inv_def` / 引理 `associator_inv_def`

English:
lemma associator_inv_def
  given: (X Y Z : F.EssImageSubcategory)
  proof: rfl

中文:
引理 associator_inv_def
  条件: (X Y Z : F.EssImageSubcategory)
  证明: rfl
-/
lemma associator_inv_def (X Y Z : F.EssImageSubcategory) :
    (α_ X Y Z).inv = ObjectProperty.homMk (α_ X.obj Y.obj Z.obj).inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `toUnit_def` / 引理 `toUnit_def`

English:
lemma toUnit_def
  given: (X : F.EssImageSubcategory)
  proof: rfl

中文:
引理 toUnit_def
  条件: (X : F.EssImageSubcategory)
  证明: rfl
-/
lemma toUnit_def (X : F.EssImageSubcategory) :
    toUnit X = ObjectProperty.homMk (toUnit X.obj) := rfl

end Functor.EssImageSubcategory

namespace NatTrans
variable (F G : C ⥤ D) [F.Monoidal] [G.Monoidal]

/--
Instance `IsMonoidal.of_cartesianMonoidalCategory` / 实例 `IsMonoidal.of_cartesianMonoidalCategory`

English:
instance IsMonoidal.of_cartesianMonoidalCategory
  signature: (α : F ⟶ G)
  body: (cancel_mono (Functor.Monoidal.εIso _).inv).1 (toUnit_unique _ _)
  tensor {X Y} := by
    rw [← cancel_mono (Functor.Monoidal.μIso _ _ _).inv]
    rw [← cancel_epi (Functor.Monoidal.μIso _ _ _).inv]
    apply CartesianMonoidalCategory.hom_ext <;> simp

中文:
实例 IsMonoidal.of_cartesianMonoidalCategory
  签名: (α : F ⟶ G)
  定义体: (cancel_mono (Functor.Monoidal.εIso _).inv).1 (toUnit_unique _ _)
  tensor {X Y} := by
    rw [← cancel_mono (Functor.Monoidal.μIso _ _ _).inv]
    rw [← cancel_epi (Functor.Monoidal.μIso _ _ _).inv]
    apply CartesianMonoidalCategory.hom_ext <;> simp

Depends on / 依赖: Functor, Functor.Monoidal, Monoidal, cancel_mono, toUnit_unique
-/
instance IsMonoidal.of_cartesianMonoidalCategory (α : F ⟶ G) : IsMonoidal α where
  unit := (cancel_mono (Functor.Monoidal.εIso _).inv).1 (toUnit_unique _ _)
  tensor {X Y} := by
    rw [← cancel_mono (Functor.Monoidal.μIso _ _ _).inv]
    rw [← cancel_epi (Functor.Monoidal.μIso _ _ _).inv]
    apply CartesianMonoidalCategory.hom_ext <;> simp

end NatTrans

end CategoryTheory
