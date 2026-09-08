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

/-- A monoidal category with binary coproducts is left distributive
if the left tensor product functor preserves binary coproducts. -/
/-
**CategoryTheory.IsMonoidalLeftDistrib** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`
。
形式化陈述：IsMonoidalLeftDistrib (C : Type u) [Category.{v} C] [MonoidalCategory C] [
HasBinaryCoproducts C] : Prop where preservesBinaryCoproducts_tensorLeft (X : C)
 : PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft X)
参数：C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoidal category with binary coproducts is left distributive
if the left tensor product functor preserves binary coproducts.
-/
class IsMonoidalLeftDistrib (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasBinaryCoproducts C] : Prop where
  preservesBinaryCoproducts_tensorLeft (X : C) :
    PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft X) := by infer_instance

/-- A monoidal category with binary coproducts is right distributive
if the right tensor product functor preserves binary coproducts. -/
/-
**CategoryTheory.IsMonoidalRightDistrib** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory
`。
形式化陈述：IsMonoidalRightDistrib (C : Type u) [Category.{v} C] [MonoidalCategory C] 
[HasBinaryCoproducts C] : Prop where preservesBinaryCoproducts_tensorRight (X : 
C) : PreservesColimitsOfShape (Discrete WalkingPair) (tensorRight X)
参数：C : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoidal category with binary coproducts is right distributive
if the right tensor product functor preserves binary coproducts.
-/
class IsMonoidalRightDistrib (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasBinaryCoproducts C] : Prop where
  preservesBinaryCoproducts_tensorRight (X : C) :
    PreservesColimitsOfShape (Discrete WalkingPair) (tensorRight X) := by infer_instance

/-- A monoidal category with binary coproducts is distributive
if it is both left and right distributive. -/
/-
**CategoryTheory.IsMonoidalDistrib** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.MonoidalCategory C] → [CategoryTheory.Limits.HasBinaryCoproducts C] → Pro
p
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoidal category with binary coproducts is distributive
if it is both left and right distributive.
-/
class IsMonoidalDistrib (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasBinaryCoproducts C] extends
  IsMonoidalLeftDistrib C, IsMonoidalRightDistrib C

variable {C} [Category.{v} C] [MonoidalCategory C] [HasBinaryCoproducts C]

section IsMonoidalLeftDistrib

attribute [instance] IsMonoidalLeftDistrib.preservesBinaryCoproducts_tensorLeft

/-- The canonical left distributivity isomorphism -/
/-
**CategoryTheory.leftDistrib** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：leftDistrib [IsMonoidalLeftDistrib C] (X Y Z : C) : (X otimes Y) ⨿ (X otim
es Z) ≅ X otimes (Y ⨿ Z)
参数：X Y Z : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical left distributivity isomorphism
-/
def leftDistrib [IsMonoidalLeftDistrib C] (X Y Z : C) :
    (X ⊗ Y) ⨿ (X ⊗ Z) ≅ X ⊗ (Y ⨿ Z) :=
  PreservesColimitPair.iso (tensorLeft X) Y Z

end IsMonoidalLeftDistrib

namespace Distributive

/-- Notation for the forward direction morphism of the canonical left distributivity isomorphism -/
scoped notation "∂L" => leftDistrib

end Distributive

open Distributive

/-
**CategoryTheory.IsMonoidalLeftDistrib.of_isIso_coprodComparisonTensorLeft** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.IsMonoidalLeftDistrib`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasBinaryCopro
ducts C]   [i :     ∀ {X Y Z : C},       CategoryTheory.IsIso (CategoryTheory.Li
mits.coprodComparison (CategoryTheory.MonoidalCategory.tensorLeft X) Y Z)],   Ca
tegoryTheory.IsMonoidalLeftDistrib C
参数：CategoryTheory.Limits.coprodComparison (CategoryTheory.MonoidalCategory.tenso
rLeft X) Y Z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用引理 `CategoryTheory.Limits.preservesBinaryCoproducts_of_isIso_coprodCompariso
n`：preservesBinaryCoproducts_of_isIso_coprodComparison [HasBinaryCoproducts C] [
HasBinaryCoproducts D] [i : forall {X Y : C}, IsIso (coprodComp…
-/
lemma IsMonoidalLeftDistrib.of_isIso_coprodComparisonTensorLeft
    [i : ∀ {X Y Z : C}, IsIso (coprodComparison (tensorLeft X) Y Z)] : IsMonoidalLeftDistrib C where
  preservesBinaryCoproducts_tensorLeft X :=
    preservesBinaryCoproducts_of_isIso_coprodComparison (tensorLeft X)

/-- The forward direction of the left distributivity isomorphism is the cogap morphism
`coprod.desc (_ ◁ coprod.inl) (_ ◁ coprod.inr) : (X ⊗ Y) ⨿ (X ⊗ Z) ⟶ X ⊗ (Y ⨿ Z)`. -/
/-
**CategoryTheory.leftDistrib_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：leftDistrib_hom [IsMonoidalLeftDistrib C] {X Y Z : C} : (∂L X Y Z).hom = c
oprod.desc (_ ◁ coprod.inl) (_ ◁ coprod.inr)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
The forward direction of the left distributivity isomorphism is the cogap morphi
sm
`coprod.desc (_ ◁ coprod.inl) (_ ◁ coprod.inr) : (X ⊗ Y) ⨿ (X ⊗ Z) ⟶ X ⊗ (Y ⨿ Z)
`.
-/
lemma leftDistrib_hom [IsMonoidalLeftDistrib C] {X Y Z : C} :
    (∂L X Y Z).hom = coprod.desc (_ ◁ coprod.inl) (_ ◁ coprod.inr) := by rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.coprod_inl_leftDistrib_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：coprod_inl_leftDistrib_hom [IsMonoidalLeftDistrib C] {X Y Z : C} : coprod.
inl ≫ (∂L X Y Z).hom = X ◁ coprod.inl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.leftDistrib_hom`：leftDistrib_hom [IsMonoidalLeftDistrib C
] {X Y Z : C} : (∂L X Y Z).hom = coprod.desc (_ ◁ coprod.inl) (_ ◁ coprod.inr)
· 使用定理 `CategoryTheory.Limits.coprod.inl_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryC
oproduct X Y] (f : X ⟶ W) (…
-/
lemma coprod_inl_leftDistrib_hom [IsMonoidalLeftDistrib C] {X Y Z : C} :
    coprod.inl ≫ (∂L X Y Z).hom = X ◁ coprod.inl := by
  rw [leftDistrib_hom, coprod.inl_desc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.coprod_inr_leftDistrib_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：coprod_inr_leftDistrib_hom [IsMonoidalLeftDistrib C] {X Y Z : C} : coprod.
inr ≫ (∂L X Y Z).hom = X ◁ coprod.inr
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.leftDistrib_hom`：leftDistrib_hom [IsMonoidalLeftDistrib C
] {X Y Z : C} : (∂L X Y Z).hom = coprod.desc (_ ◁ coprod.inl) (_ ◁ coprod.inr)
· 使用定理 `CategoryTheory.Limits.coprod.inr_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryC
oproduct X Y] (f : X ⟶ W) (…
-/
lemma coprod_inr_leftDistrib_hom [IsMonoidalLeftDistrib C] {X Y Z : C} :
    coprod.inr ≫ (∂L X Y Z).hom = X ◁ coprod.inr := by
  rw [leftDistrib_hom, coprod.inr_desc]

/-- The composite of `(X ◁ coprod.inl) : X ⊗ Y ⟶ X ⊗ (Y ⨿ Z)` and
`(∂L X Y Z).inv :  X ⊗ (Y ⨿ Z) ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`
is equal to the left coprojection `coprod.inl : X ⊗ Y ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`. -/
@[reassoc (attr := simp)]
/-
**CategoryTheory.whiskerLeft_coprod_inl_leftDistrib_inv** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory`。
形式化陈述：whiskerLeft_coprod_inl_leftDistrib_inv [IsMonoidalLeftDistrib C] {X Y Z : 
C} : (X ◁ coprod.inl) ≫ (∂L X Y Z).inv = coprod.inl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Iso.cancel_iso_hom_right`：cancel_iso_hom_right {X Y Z : C
} (f f' : X ⟶ Y) (g : Y ≅ Z) : f ≫ g.hom = f' ≫ g.hom ↔ f = f'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.coprod_inl_leftDistrib_hom`：coprod_inl_leftDistrib_hom [I
sMonoidalLeftDistrib C] {X Y Z : C} : coprod.inl ≫ (∂L X Y Z).hom = X ◁ coprod.i
nl

--- 原说明 ---
The composite of `(X ◁ coprod.inl) : X ⊗ Y ⟶ X ⊗ (Y ⨿ Z)` and
`(∂L X Y Z).inv :  X ⊗ (Y ⨿ Z) ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`
is equal to the left coprojection `coprod.inl : X ⊗ Y ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`.
-/
lemma whiskerLeft_coprod_inl_leftDistrib_inv [IsMonoidalLeftDistrib C] {X Y Z : C} :
    (X ◁ coprod.inl) ≫ (∂L X Y Z).inv = coprod.inl := by
  apply (cancel_iso_hom_right _ _ (∂L X Y Z)).mp
  rw [assoc, Iso.inv_hom_id, comp_id, coprod_inl_leftDistrib_hom]

/-- The composite of `(X ◁ coprod.inr) : X ⊗ Z ⟶ X ⊗ (Y ⨿ Z)` and
`(∂L X Y Z).inv :  X ⊗ (Y ⨿ Z) ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`
is equal to the right coprojection `coprod.inr : X ⊗ Z ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`. -/
@[reassoc (attr := simp)]
/-
**CategoryTheory.whiskerLeft_coprod_inr_leftDistrib_inv** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory`。
形式化陈述：whiskerLeft_coprod_inr_leftDistrib_inv [IsMonoidalLeftDistrib C] {X Y Z : 
C} : (X ◁ coprod.inr) ≫ (∂L X Y Z).inv = coprod.inr
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Iso.cancel_iso_hom_right`：cancel_iso_hom_right {X Y Z : C
} (f f' : X ⟶ Y) (g : Y ≅ Z) : f ≫ g.hom = f' ≫ g.hom ↔ f = f'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.coprod_inr_leftDistrib_hom`：coprod_inr_leftDistrib_hom [I
sMonoidalLeftDistrib C] {X Y Z : C} : coprod.inr ≫ (∂L X Y Z).hom = X ◁ coprod.i
nr

--- 原说明 ---
The composite of `(X ◁ coprod.inr) : X ⊗ Z ⟶ X ⊗ (Y ⨿ Z)` and
`(∂L X Y Z).inv :  X ⊗ (Y ⨿ Z) ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`
is equal to the right coprojection `coprod.inr : X ⊗ Z ⟶ (X ⊗ Y) ⨿ (X ⊗ Z)`.
-/
lemma whiskerLeft_coprod_inr_leftDistrib_inv [IsMonoidalLeftDistrib C] {X Y Z : C} :
    (X ◁ coprod.inr) ≫ (∂L X Y Z).inv = coprod.inr := by
  apply (cancel_iso_hom_right _ _ (∂L X Y Z)).mp
  rw [assoc, Iso.inv_hom_id, comp_id, coprod_inr_leftDistrib_hom]

section IsMonoidalRightDistrib

attribute [instance] IsMonoidalRightDistrib.preservesBinaryCoproducts_tensorRight

/-- The canonical right distributivity isomorphism -/
/-
**CategoryTheory.rightDistrib** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：rightDistrib [IsMonoidalRightDistrib C] (X Y Z : C) : (Y otimes X) ⨿ (Z ot
imes X) ≅ (Y ⨿ Z) otimes X
参数：X Y Z : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical right distributivity isomorphism
-/
def rightDistrib [IsMonoidalRightDistrib C] (X Y Z : C) : (Y ⊗ X) ⨿ (Z ⊗ X) ≅ (Y ⨿ Z) ⊗ X :=
  PreservesColimitPair.iso (tensorRight X) Y Z

end IsMonoidalRightDistrib

namespace Distributive

/-- Notation for the forward direction morphism of the canonical right distributivity isomorphism -/
notation "∂R" => rightDistrib

end Distributive

/-
**CategoryTheory.IsMonoidalRightDistrib.of_isIso_coprodComparisonTensorRight** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsMonoidalRightDistrib`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasBinaryCopro
ducts C]   [i :     ∀ {X Y Z : C},       CategoryTheory.IsIso         (CategoryT
heory.Limits.coprodComparison (CategoryTheory.MonoidalCategory.tensorRight X) Y 
Z)],   CategoryTheory.IsMonoidalRightDistrib C
参数：CategoryTheory.Limits.coprodComparison (CategoryTheory.MonoidalCategory.tenso
rRight X) Y Z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用引理 `CategoryTheory.Limits.preservesBinaryCoproducts_of_isIso_coprodCompariso
n`：preservesBinaryCoproducts_of_isIso_coprodComparison [HasBinaryCoproducts C] [
HasBinaryCoproducts D] [i : forall {X Y : C}, IsIso (coprodComp…
-/
lemma IsMonoidalRightDistrib.of_isIso_coprodComparisonTensorRight
    [i : ∀ {X Y Z : C}, IsIso (coprodComparison (tensorRight X) Y Z)] :
    IsMonoidalRightDistrib C where
  preservesBinaryCoproducts_tensorRight _ :=
    ⟨preservesBinaryCoproducts_of_isIso_coprodComparison _ |>.preservesColimit⟩

/-- The forward direction of the right distributivity isomorphism is equal to the cogap morphism
`coprod.desc (coprod.inl ▷ _) (coprod.inr ▷ _) : (Y ⊗ X) ⨿ (Z ⊗ X) ⟶ (Y ⨿ Z) ⊗ X`. -/
/-
**CategoryTheory.rightDistrib_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：rightDistrib_hom [IsMonoidalRightDistrib C] {X Y Z : C} : (∂R X Y Z).hom =
 coprod.desc (coprod.inl ▷ _) (coprod.inr ▷ _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
The forward direction of the right distributivity isomorphism is equal to the co
gap morphism
`coprod.desc (coprod.inl ▷ _) (coprod.inr ▷ _) : (Y ⊗ X) ⨿ (Z ⊗ X) ⟶ (Y ⨿ Z) ⊗ X
`.
-/
lemma rightDistrib_hom [IsMonoidalRightDistrib C] {X Y Z : C} :
    (∂R X Y Z).hom = coprod.desc (coprod.inl ▷ _) (coprod.inr ▷ _) := by rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.coprod_inl_rightDistrib_hom** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory`。
形式化陈述：coprod_inl_rightDistrib_hom [IsMonoidalRightDistrib C] {X Y Z : C} : copro
d.inl ≫ (∂R X Y Z).hom = coprod.inl ▷ X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.rightDistrib_hom`：rightDistrib_hom [IsMonoidalRightDistri
b C] {X Y Z : C} : (∂R X Y Z).hom = coprod.desc (coprod.inl ▷ _) (coprod.inr ▷ _
)
· 使用定理 `CategoryTheory.Limits.coprod.inl_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryC
oproduct X Y] (f : X ⟶ W) (…
-/
lemma coprod_inl_rightDistrib_hom [IsMonoidalRightDistrib C] {X Y Z : C} :
    coprod.inl ≫ (∂R X Y Z).hom = coprod.inl ▷ X := by
  rw [rightDistrib_hom, coprod.inl_desc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.coprod_inr_rightDistrib_hom** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory`。
形式化陈述：coprod_inr_rightDistrib_hom [IsMonoidalRightDistrib C] {X Y Z : C} : copro
d.inr ≫ (∂R X Y Z).hom = coprod.inr ▷ X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.rightDistrib_hom`：rightDistrib_hom [IsMonoidalRightDistri
b C] {X Y Z : C} : (∂R X Y Z).hom = coprod.desc (coprod.inl ▷ _) (coprod.inr ▷ _
)
· 使用定理 `CategoryTheory.Limits.coprod.inr_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryC
oproduct X Y] (f : X ⟶ W) (…
-/
lemma coprod_inr_rightDistrib_hom [IsMonoidalRightDistrib C] {X Y Z : C} :
    coprod.inr ≫ (∂R X Y Z).hom = coprod.inr ▷ X := by
  rw [rightDistrib_hom, coprod.inr_desc]

/-- The composite of `(coprod.inl ▷ X) : Y ⊗ X ⟶ (Y ⨿ Z) ⊗ X` and
`(∂R X Y Z).inv :  (Y ⨿ Z) ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)` is equal to the left coprojection
`coprod.inl : Y ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)`. -/
@[reassoc (attr := simp)]
/-
**CategoryTheory.whiskerRight_coprod_inl_rightDistrib_inv** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory`。
形式化陈述：whiskerRight_coprod_inl_rightDistrib_inv [IsMonoidalRightDistrib C] {X Y Z
 : C} : (coprod.inl ▷ X) ≫ (∂R X Y Z).inv = coprod.inl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Iso.cancel_iso_hom_right`：cancel_iso_hom_right {X Y Z : C
} (f f' : X ⟶ Y) (g : Y ≅ Z) : f ≫ g.hom = f' ≫ g.hom ↔ f = f'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.coprod_inl_rightDistrib_hom`：coprod_inl_rightDistrib_hom 
[IsMonoidalRightDistrib C] {X Y Z : C} : coprod.inl ≫ (∂R X Y Z).hom = coprod.in
l ▷ X

--- 原说明 ---
The composite of `(coprod.inl ▷ X) : Y ⊗ X ⟶ (Y ⨿ Z) ⊗ X` and
`(∂R X Y Z).inv :  (Y ⨿ Z) ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)` is equal to the left coproje
ction
`coprod.inl : Y ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)`.
-/
lemma whiskerRight_coprod_inl_rightDistrib_inv [IsMonoidalRightDistrib C] {X Y Z : C} :
    (coprod.inl ▷ X) ≫ (∂R X Y Z).inv = coprod.inl := by
  apply (cancel_iso_hom_right _ _ (∂R X Y Z)).mp
  rw [assoc, Iso.inv_hom_id, comp_id, coprod_inl_rightDistrib_hom]

/-- The composite of `(coprod.inr ▷ X) : Z ⊗ X ⟶ (Y ⨿ Z) ⊗ X` and
`(∂R X Y Z).inv :  (Y ⨿ Z) ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)` is equal to the right coprojection
`coprod.inr : Z ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)`. -/
@[reassoc (attr := simp)]
/-
**CategoryTheory.whiskerRight_coprod_inr_rightDistrib_inv** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory`。
形式化陈述：whiskerRight_coprod_inr_rightDistrib_inv [IsMonoidalRightDistrib C] {X Y Z
 : C} : (coprod.inr ▷ X) ≫ (∂R X Y Z).inv = coprod.inr
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Iso.cancel_iso_hom_right`：cancel_iso_hom_right {X Y Z : C
} (f f' : X ⟶ Y) (g : Y ≅ Z) : f ≫ g.hom = f' ≫ g.hom ↔ f = f'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.coprod_inr_rightDistrib_hom`：coprod_inr_rightDistrib_hom 
[IsMonoidalRightDistrib C] {X Y Z : C} : coprod.inr ≫ (∂R X Y Z).hom = coprod.in
r ▷ X

--- 原说明 ---
The composite of `(coprod.inr ▷ X) : Z ⊗ X ⟶ (Y ⨿ Z) ⊗ X` and
`(∂R X Y Z).inv :  (Y ⨿ Z) ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)` is equal to the right coproj
ection
`coprod.inr : Z ⊗ X ⟶ (Y ⊗ X) ⨿ (Z ⊗ X)`.
-/
lemma whiskerRight_coprod_inr_rightDistrib_inv [IsMonoidalRightDistrib C] {X Y Z : C} :
    (coprod.inr ▷ X) ≫ (∂R X Y Z).inv = coprod.inr := by
  apply (cancel_iso_hom_right _ _ (∂R X Y Z)).mp
  rw [assoc, Iso.inv_hom_id, comp_id, coprod_inr_rightDistrib_hom]

set_option backward.defeqAttrib.useBackward true in
/-- In a symmetric monoidal category, the left distributivity is equal to
the right distributivity up to braiding isomorphisms. -/
@[simp]
/-
**CategoryTheory.coprodComparison_tensorLeft_braiding_hom** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory`。
形式化陈述：coprodComparison_tensorLeft_braiding_hom [BraidedCategory C] {X Y Z : C} :
 (coprodComparison (tensorLeft X) Y Z) ≫ (β_ X (Y ⨿ Z)).hom = (coprod.map (β_ X 
Y).hom (β_ X Z).hom) ≫ (coprodComparison (tensorRight X) Y Z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_right`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCate
gory C}   [self : CategoryTheory.BraidedCatego…
· 使用定理 `CategoryTheory.Limits.coprod.map_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {S T U V W : C}   [inst_1 : CategoryTheory.Limits.HasBin
aryCoproduct U W] [inst_2 :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In a symmetric monoidal category, the left distributivity is equal to
the right distributivity up to braiding isomorphisms.
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
/-
**CategoryTheory.coprodComparison_tensorRight_braiding_hom** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory`。
形式化陈述：coprodComparison_tensorRight_braiding_hom [SymmetricCategory C] {X Y Z : C
} : (coprodComparison (tensorRight X) Y Z) ≫ (β_ (Y ⨿ Z) X).hom = (coprod.map (β
_ Y X).hom (β_ Z X).hom) ≫ (coprodComparison (tensorLeft X) Y Z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_left`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCateg
ory C}   [self : CategoryTheory.BraidedCatego…
· 使用定理 `CategoryTheory.Limits.coprod.map_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {S T U V W : C}   [inst_1 : CategoryTheory.Limits.HasBin
aryCoproduct U W] [inst_2 :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In a symmetric monoidal category, the right distributivity is equal to
the left distributivity up to braiding isomorphisms.
-/
lemma coprodComparison_tensorRight_braiding_hom [SymmetricCategory C] {X Y Z : C} :
    (coprodComparison (tensorRight X) Y Z) ≫ (β_ (Y ⨿ Z) X).hom =
    (coprod.map (β_ Y X).hom (β_ Z X).hom) ≫ (coprodComparison (tensorLeft X) Y Z) := by
  simp [coprodComparison]

/-- A left distributive symmetric monoidal category is distributive. -/
/-
**CategoryTheory.SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib** 
是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.SymmetricCategory`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasBinaryCopro
ducts C] [CategoryTheory.SymmetricCategory C]   [CategoryTheory.IsMonoidalLeftDi
strib C], CategoryTheory.IsMonoidalDistrib C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_natIso`：preservesColim
itsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfShape J F] : 
PreservesColimitsOfShape J G where preservesCo…
· 使用定理 `CategoryTheory.IsMonoidalLeftDistrib.preservesBinaryCoproducts_tensorLef
t`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTh
eory.MonoidalCategory C}   {inst_2 : CategoryTheory.Limits.HasB…

--- 原说明 ---
A left distributive symmetric monoidal category is distributive.
-/
lemma SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib
    [SymmetricCategory C] [IsMonoidalLeftDistrib C] : IsMonoidalDistrib C where
      preservesBinaryCoproducts_tensorRight X :=
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- The right distributivity isomorphism of the a left distributive symmetric monoidal category
is given by `(β_ (Y ⨿ Z) X).hom ≫ (∂L X Y Z).inv ≫ (coprod.map (β_ X Y).hom (β_ X Z).hom)`. -/
@[simp]
/-
**CategoryTheory.SymmetricCategory.rightDistrib_of_leftDistrib** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.SymmetricCategory`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasBinaryCopro
ducts C] [inst_3 : CategoryTheory.SymmetricCategory C]   [inst_4 : CategoryTheor
y.IsMonoidalDistrib C] {X Y Z : C},   ∂R X Y Z = CategoryTheory.Limits.coprod.ma
pIso (β_ Y X) (β_ Z X) ≪≫ CategoryTheory.leftDistrib X Y Z ≪≫ β_ X (Y ⨿ Z)
参数：β_ Y X；β_ Z X；Y ⨿ Z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsMonoidalDistrib.toIsMonoidalRightDistrib`：∀ {C : Type u
} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCat
egory C}   {inst_2 : CategoryTheory.Limits.HasB…
· 使用定理 `CategoryTheory.IsMonoidalDistrib.toIsMonoidalLeftDistrib`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCate
gory C}   {inst_2 : CategoryTheory.Limits.HasB…
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.rightDistrib_hom`：rightDistrib_hom [IsMonoidalRightDistri
b C] {X Y Z : C} : (∂R X Y Z).hom = coprod.desc (coprod.inl ▷ _) (coprod.inr ▷ _
)
· 使用定理 `CategoryTheory.Limits.coprod.mapIso_hom`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBin
aryCoproduct W X] [inst_2 : C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.leftDistrib_hom`：leftDistrib_hom [IsMonoidalLeftDistrib C
] {X Y Z : C} : (∂L X Y Z).hom = coprod.desc (_ ◁ coprod.inl) (_ ◁ coprod.inr)
· 使用定理 `CategoryTheory.Limits.coprod.desc_comp`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBina
ryCoproduct X Y] (f : V ⟶ W)…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_right`：∀ {C : Type u}
 {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCate
gory C}   [self : CategoryTheory.BraidedCatego…
· 使用定理 `CategoryTheory.Limits.coprod.map_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {S T U V W : C}   [inst_1 : CategoryTheory.Limits.HasBin
aryCoproduct U W] [inst_2 :…
· 使用定理 `CategoryTheory.SymmetricCategory.symmetry_assoc`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}  
 [self : CategoryTheory.SymmetricCate…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The right distributivity isomorphism of the a left distributive symmetric monoid
al category
is given by `(β_ (Y ⨿ Z) X).hom ≫ (∂L X Y Z).inv ≫ (coprod.map (β_ X Y).hom (β_ 
X Z).hom)`.
-/
lemma SymmetricCategory.rightDistrib_of_leftDistrib
    [SymmetricCategory C] [IsMonoidalDistrib C] {X Y Z : C} :
    ∂R X Y Z = (coprod.mapIso (β_ Y X) (β_ Z X)) ≪≫ (∂L X Y Z) ≪≫ (β_ X (Y ⨿ Z)) := by
  ext <;> simp [leftDistrib_hom, rightDistrib_hom]

/-- A closed monoidal category is left distributive. -/
/-
**CategoryTheory.MonoidalClosed.isMonoidalLeftDistrib** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.MonoidalClosed`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasBinaryCopro
ducts C] [CategoryTheory.MonoidalClosed C],   CategoryTheory.IsMonoidalLeftDistr
ib C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instPreservesColimitsTensorLeft`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C] (A
 : C)   [CategoryTheory.Closed A], C…

--- 原说明 ---
A closed monoidal category is left distributive.
-/
instance MonoidalClosed.isMonoidalLeftDistrib [MonoidalClosed C] :
    IsMonoidalLeftDistrib C where
  preservesBinaryCoproducts_tensorLeft X := by
    infer_instance
/-
**CategoryTheory.isMonoidalDistrib.of_symmetric_monoidal_closed** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.isMonoidalDistrib`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasBinaryCopro
ducts C] [CategoryTheory.SymmetricCategory C]   [CategoryTheory.MonoidalClosed C
], CategoryTheory.IsMonoidalDistrib C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDist
rib`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.MonoidalClosed.isMonoidalLeftDistrib`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C]   [inst_2 : CategoryTheory.Limits.…
-/
instance isMonoidalDistrib.of_symmetric_monoidal_closed [SymmetricCategory C] [MonoidalClosed C] :
    IsMonoidalDistrib C := by
  apply SymmetricCategory.isMonoidalDistrib_of_isMonoidalLeftDistrib

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of distributivity isomorphism from the closed monoidal structure -/
/-
**CategoryTheory.MonoidalClosed.leftDistrib_inv** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.MonoidalClosed`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasBinaryCopro
ducts C] [inst_3 : CategoryTheory.MonoidalClosed C] {X Y Z : C},   (CategoryTheo
ry.leftDistrib X Y Z).inv =     CategoryTheory.MonoidalClosed.uncurry       (Cat
egoryTheory.Limits.coprod.desc (CategoryTheory.MonoidalClosed.curry CategoryTheo
ry.Limits.coprod.inl)         (CategoryTheory.MonoidalClosed.curry CategoryTheor
y.Limits.coprod.inr))
参数：CategoryTheory.leftDistrib X Y Z；CategoryTheory.Limits.coprod.desc (CategoryT
heory.MonoidalClosed.curry CategoryTheory.Limits.coprod.inl)         (CategoryTh
eory.MonoidalClosed.curry CategoryTheory.Limits.coprod.inr)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.MonoidalClosed.isMonoidalLeftDistrib`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C]   [inst_2 : CategoryTheory.Limits.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalClosed.curry_eq_iff`：curry_eq_iff (f : A otimes Y
 ⟶ X) (g : Y ⟶ A ⟶[C] X) : curry f = g ↔ f = uncurry g
· 使用定理 `CategoryTheory.Limits.coprod.hom_ext`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryCo
product X Y] {f g : X ⨿ Y …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.whiskerLeft_coprod_inl_leftDistrib_inv`：whiskerLeft_copro
d_inl_leftDistrib_inv [IsMonoidalLeftDistrib C] {X Y Z : C} : (X ◁ coprod.inl) ≫
 (∂L X Y Z).inv = coprod.inl
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.whiskerLeft_coprod_inr_leftDistrib_inv`：whiskerLeft_copro
d_inr_leftDistrib_inv [IsMonoidalLeftDistrib C] {X Y Z : C} : (X ◁ coprod.inr) ≫
 (∂L X Y Z).inv = coprod.inr

--- 原说明 ---
The inverse of distributivity isomorphism from the closed monoidal structure
-/
lemma MonoidalClosed.leftDistrib_inv [MonoidalClosed C] {X Y Z : C} :
    (leftDistrib X Y Z).inv =
      uncurry (coprod.desc (curry coprod.inl) (curry coprod.inr)) := by
  rw [← curry_eq_iff]
  ext <;> simp [← curry_natural_left]

section Endofunctors

attribute [local instance] endofunctorMonoidalCategory

/-- The monoidal structure on the category of endofunctors is left distributive. -/
/-
**CategoryTheory.isMonoidalLeftDistrib.of_endofunctors** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.isMonoidalLeftDistrib`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.Limits.HasBinaryCoproducts C],   CategoryTheory.IsMonoidalLeftDistri
b (CategoryTheory.Functor C C)
参数：CategoryTheory.Functor C C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoidal structure on the category of endofunctors is left distributive.
-/
instance isMonoidalLeftDistrib.of_endofunctors : IsMonoidalLeftDistrib (C ⥤ C) where
  preservesBinaryCoproducts_tensorLeft F :=
    inferInstanceAs (PreservesColimitsOfShape _ ((Functor.whiskeringLeft C C C).obj F))

end Endofunctors

section MonoidalPreadditive

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts
  preservesBinaryCoproducts_of_preservesBinaryBiproducts

/-- A preadditive monoidal category with binary biproducts is distributive. -/
/-
**CategoryTheory.IsMonoidalDistrib.of_MonoidalPreadditive_with_binary_coproducts
** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsMonoidalDistrib`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : Cat
egoryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Limits.HasBinaryCopro
ducts C] [inst_3 : CategoryTheory.Preadditive C]   [CategoryTheory.MonoidalPread
ditive C], CategoryTheory.IsMonoidalDistrib C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesBinaryCoproducts_of_preservesBinaryBiprod
ucts`：preservesBinaryCoproducts_of_preservesBinaryBiproducts [PreservesBinaryBip
roducts F] : PreservesColimitsOfShape (Discrete WalkingPair) F whe…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.tensoringLeft_additive`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   [inst_2 
: CategoryTheory.MonoidalCa…
· 使用引理 `CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts`：
preservesBinaryBiproducts_of_preservesBiproducts (F : C ⥤ D) [PreservesZeroMorph
isms F] [PreservesBiproductsOfShape WalkingPair F] : Preserv…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteBiproducts.preserves`：∀ {C : Type u
₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryT
heory.Category.{v₂, u₂} D}   {inst_2 : Category…
· 使用定理 `CategoryTheory.instPreservesFiniteBiproductsTensorLeft`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preaddit
ive C]   [inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Functor.instPreservesZeroMorphismsObjFlip`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.MonoidalPreadditive.instAdditiveFunctorCurriedTensor`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Preadditive C]   [inst_2 : CategoryTheory.MonoidalCa…
· 使用定理 `CategoryTheory.instPreservesFiniteBiproductsTensorRight`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preaddi
tive C]   [inst_2 : CategoryTheory.MonoidalCa…

--- 原说明 ---
A preadditive monoidal category with binary biproducts is distributive.
-/
instance IsMonoidalDistrib.of_MonoidalPreadditive_with_binary_coproducts [Preadditive C]
    [MonoidalPreadditive C] :
    IsMonoidalDistrib C where

end MonoidalPreadditive

end CategoryTheory

