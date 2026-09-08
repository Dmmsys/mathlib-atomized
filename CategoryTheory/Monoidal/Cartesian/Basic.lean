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

/-- A monoidal category is semicartesian if the unit for the tensor product is a terminal object. -/
/-
**CategoryTheory.SemiCartesianMonoidalCategory** 是 Mathlib 中的一个类，位于命名空间 `Categor
yTheory`。
形式化陈述：SemiCartesianMonoidalCategory (C : Type u) [Category.{v} C] extends Monoid
alCategory C where /-- The tensor unit is a terminal object. -/ isTerminalTensor
Unit : IsTerminal (𝟙_ C) /-- The first projection from the product. -/ fst (X Y 
: C) : X otimes Y ⟶ X /-- The second projection from the product. -/ snd (X Y : 
C) : X otimes Y ⟶ Y fst_def (X Y : C) : fst X Y = X ◁ isTerminalTensorUnit.from 
Y ≫ (ρ_ X).hom
参数：C : Type u。
继承自：MonoidalCategory C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoidal category is semicartesian if the unit for the tensor product is a ter
minal object.
-/
class SemiCartesianMonoidalCategory (C : Type u) [Category.{v} C] extends MonoidalCategory C where
  /-- The tensor unit is a terminal object. -/
  isTerminalTensorUnit : IsTerminal (𝟙_ C)
  /-- The first projection from the product. -/
  fst (X Y : C) : X ⊗ Y ⟶ X
  /-- The second projection from the product. -/
  snd (X Y : C) : X ⊗ Y ⟶ Y
  fst_def (X Y : C) : fst X Y = X ◁ isTerminalTensorUnit.from Y ≫ (ρ_ X).hom := by cat_disch
  snd_def (X Y : C) : snd X Y = isTerminalTensorUnit.from X ▷ Y ≫ (λ_ Y).hom := by cat_disch

namespace SemiCartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [SemiCartesianMonoidalCategory C]

/-- The unique map to the terminal object. -/
/-
**CategoryTheory.SemiCartesianMonoidalCategory.toUnit** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.SemiCartesianMonoidalCategory`。
形式化陈述：toUnit (X : C) : X ⟶ 𝟙_ C
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique map to the terminal object.
-/
def toUnit (X : C) : X ⟶ 𝟙_ C := isTerminalTensorUnit.from X
/-
**CategoryTheory.SemiCartesianMonoidalCategory.** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.SemiCartesianMonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) : Unique (X ⟶ 𝟙_ C) := isTerminalEquivUnique _ _ isTerminalTensorUnit _
/-
**CategoryTheory.SemiCartesianMonoidalCategory.default_eq_toUnit** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.SemiCartesianMonoidalCategory`。
形式化陈述：default_eq_toUnit (X : C) : default = toUnit X
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma default_eq_toUnit (X : C) : default = toUnit X := rfl

/--
This lemma follows from the preexisting `Unique` instance, but
it is often convenient to use it directly as `apply toUnit_unique` forcing
lean to do the necessary elaboration.
-/
@[ext]
/-
**CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.SemiCartesianMonoidalCategory`。
形式化陈述：toUnit_unique {X : C} (f g : X ⟶ 𝟙_ _) : f = g
参数：f g : X ⟶ 𝟙_ _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
This lemma follows from the preexisting `Unique` instance, but
it is often convenient to use it directly as `apply toUnit_unique` forcing
lean to do the necessary elaboration.
-/
lemma toUnit_unique {X : C} (f g : X ⟶ 𝟙_ _) : f = g :=
  Subsingleton.elim _ _
/-
**CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unit** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.SemiCartesianMonoidalCategory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.SemiCartesianMonoidalCategory C],   CategoryTheory.SemiCartesianMonoidal
Category.toUnit (CategoryTheory.MonoidalCategoryStruct.tensorUnit C) =     Categ
oryTheory.CategoryStruct.id (CategoryTheory.MonoidalCategoryStruct.tensorUnit C)
参数：CategoryTheory.MonoidalCategoryStruct.tensorUnit C；CategoryTheory.MonoidalCat
egoryStruct.tensorUnit C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
-/
@[simp] lemma toUnit_unit : toUnit (𝟙_ C) = 𝟙 (𝟙_ C) := toUnit_unique ..

@[reassoc (attr := simp)]
/-
**CategoryTheory.SemiCartesianMonoidalCategory.comp_toUnit** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.SemiCartesianMonoidalCategory`。
形式化陈述：comp_toUnit {X Y : C} (f : X ⟶ Y) : f ≫ toUnit Y = toUnit X
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
-/
theorem comp_toUnit {X Y : C} (f : X ⟶ Y) : f ≫ toUnit Y = toUnit X :=
  toUnit_unique _ _

end SemiCartesianMonoidalCategory

variable (C) in
/--
An instance of `CartesianMonoidalCategory C` bundles an explicit choice of a binary
product of two objects of `C`, and a terminal object in `C`.

Users should use the monoidal notation: `X ⊗ Y` for the product and `𝟙_ C` for
the terminal object.
-/
/-
**CategoryTheory.CartesianMonoidalCategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `Category
Theory`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An instance of `CartesianMonoidalCategory C` bundles an explicit choice of a bin
ary
product of two objects of `C`, and a terminal object in `C`.

Users should use the monoidal notation: `X ⊗ Y` for the product and `𝟙_ C` for
the terminal object.
-/
class CartesianMonoidalCategory (C : Type u) [Category.{v} C] extends
    SemiCartesianMonoidalCategory C where
  /-- The monoidal product is the categorical product. -/
  tensorProductIsBinaryProduct (X Y : C) : IsLimit <| BinaryFan.mk (fst X Y) (snd X Y)

namespace CartesianMonoidalCategory

export SemiCartesianMonoidalCategory (isTerminalTensorUnit fst snd fst_def snd_def toUnit
  toUnit_unique toUnit_unit comp_toUnit comp_toUnit_assoc default_eq_toUnit)

variable {C : Type u} [Category.{v} C]

section OfChosenFiniteProducts
variable (𝒯 : LimitCone (Functor.empty.{0} C)) (ℬ : ∀ X Y : C, LimitCone (pair X Y))
  {X₁ X₂ X₃ Y₁ Y₂ Y₃ Z₁ Z₂ : C}

namespace ofChosenFiniteProducts

/-- Implementation of the tensor product for `CartesianMonoidalCategory.ofChosenFiniteProducts`. -/
/-
**CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts.tensorObj** 是 
Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.CartesianMonoidalCategory.ofChosenFinite
Products`。
形式化陈述：tensorObj (X Y : C) : C
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of the tensor product for `CartesianMonoidalCategory.ofChosenFini
teProducts`.
-/
abbrev tensorObj (X Y : C) : C := (ℬ X Y).cone.pt

/-- Implementation of the tensor product of morphisms for
`CartesianMonoidalCategory.ofChosenFiniteProducts`. -/
/-
**CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts.tensorHom** 是 
Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.CartesianMonoidalCategory.ofChosenFinite
Products`。
形式化陈述：tensorHom (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : tensorObj ℬ X₁ X₂ ⟶ tensorObj ℬ Y₁
 Y₂
参数：f : X₁ ⟶ Y₁；g : X₂ ⟶ Y₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation of the tensor product of morphisms for
`CartesianMonoidalCategory.ofChosenFiniteProducts`.
-/
abbrev tensorHom (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : tensorObj ℬ X₁ X₂ ⟶ tensorObj ℬ Y₁ Y₂ :=
  (BinaryFan.IsLimit.lift' (ℬ Y₁ Y₂).isLimit ((ℬ X₁ X₂).cone.π.app ⟨.left⟩ ≫ f)
      (((ℬ X₁ X₂).cone.π.app ⟨.right⟩ : (ℬ X₁ X₂).cone.pt ⟶ X₂) ≫ g)).val

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts.id_tensorHom_i
d** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory.ofChosenFi
niteProducts`。
形式化陈述：id_tensorHom_id (X Y : C) : tensorHom ℬ (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj ℬ X Y)
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.BinaryFan.IsLimit.lift'_coe`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.Binar
yFan X Y}   (h : CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma id_tensorHom_id (X Y : C) : tensorHom ℬ (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj ℬ X Y) :=
  (ℬ _ _).isLimit.hom_ext <| by rintro ⟨_ | _⟩ <;> simp [tensorHom]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts.tensorHom_comp
_tensorHom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory.o
fChosenFiniteProducts`。
形式化陈述：tensorHom_comp_tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ 
: Y₂ ⟶ Z₂) : tensorHom ℬ f₁ f₂ ≫ tensorHom ℬ g₁ g₂ = tensorHom ℬ (f₁ ≫ g₁) (f₂ ≫
 g₂)
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂；g₁ : Y₁ ⟶ Z₁；g₂ : Y₂ ⟶ Z₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.BinaryFan.IsLimit.lift'_coe`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.Binar
yFan X Y}   (h : CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac_assoc`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensorHom_comp_tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom ℬ f₁ f₂ ≫ tensorHom ℬ g₁ g₂ = tensorHom ℬ (f₁ ≫ g₁) (f₂ ≫ g₂) :=
  (ℬ _ _).isLimit.hom_ext <| by rintro ⟨_ | _⟩ <;> simp [tensorHom]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts.pentagon** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory.ofChosenFinitePro
ducts`。
形式化陈述：pentagon (W X Y Z : C) : tensorHom ℬ (BinaryFan.associatorOfLimitCone ℬ W 
X Y).hom (𝟙 Z) ≫ (BinaryFan.associatorOfLimitCone ℬ W (tensorObj ℬ X Y) Z).hom ≫
 tensorHom ℬ (𝟙 W) (BinaryFan.associatorOfLimitCone ℬ X Y Z).hom = (BinaryFan.as
sociatorOfLimitCone ℬ (tensorObj ℬ W X) Y Z).hom ≫ (BinaryFan.associatorOfLimitC
one ℬ W X (tensorObj ℬ Y Z)).hom
参数：W X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.BinaryFan.IsLimit.lift'_coe`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.Binar
yFan X Y}   (h : CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac_assoc`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp_assoc`：∀ {
J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 :
 CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-
**CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts.triangle** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory.ofChosenFinitePro
ducts`。
形式化陈述：triangle (X Y : C) : (BinaryFan.associatorOfLimitCone ℬ X 𝒯.cone.pt Y).hom
 ≫ tensorHom ℬ (𝟙 X) (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt Y).isLimit).ho
m = tensorHom ℬ (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X 𝒯.cone.pt).isLimit).hom (𝟙
 Y)
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.BinaryFan.leftUnitor_hom`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X : C}   {s : CategoryTheory.Limits.Cone (Cate
goryTheory.Functor.empty C)} (P : Ca…
· 使用定理 `CategoryTheory.Limits.BinaryFan.IsLimit.lift'_coe`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.Binar
yFan X Y}   (h : CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
· 使用定理 `CategoryTheory.Limits.BinaryFan.rightUnitor_hom`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {X : C}   {s : CategoryTheory.Limits.Cone (Cat
egoryTheory.Functor.empty C)} (P : Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp_assoc`：∀ {
J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 :
 CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
lemma triangle (X Y : C) :
    (BinaryFan.associatorOfLimitCone ℬ X 𝒯.cone.pt Y).hom ≫
        tensorHom ℬ (𝟙 X) (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt Y).isLimit).hom =
      tensorHom ℬ (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X 𝒯.cone.pt).isLimit).hom (𝟙 Y) :=
  (ℬ _ _).isLimit.hom_ext <| by rintro ⟨_ | _⟩ <;> simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts.leftUnitor_nat
urality** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory.ofCh
osenFiniteProducts`。
形式化陈述：leftUnitor_naturality (f : X₁ ⟶ X₂) : tensorHom ℬ (𝟙 𝒯.cone.pt) f ≫ (Binar
yFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X₂).isLimit).hom = (BinaryFan.leftUnitor 
𝒯.isLimit (ℬ 𝒯.cone.pt X₁).isLimit).hom ≫ f
参数：f : X₁ ⟶ X₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.BinaryFan.IsLimit.lift'_coe`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.Binar
yFan X Y}   (h : CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Limits.BinaryFan.leftUnitor_hom`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X : C}   {s : CategoryTheory.Limits.Cone (Cate
goryTheory.Functor.empty C)} (P : Ca…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftUnitor_naturality (f : X₁ ⟶ X₂) :
    tensorHom ℬ (𝟙 𝒯.cone.pt) f ≫ (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X₂).isLimit).hom =
      (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X₁).isLimit).hom ≫ f := by
  simp [tensorHom]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts.rightUnitor_na
turality** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory.ofC
hosenFiniteProducts`。
形式化陈述：rightUnitor_naturality (f : X₁ ⟶ X₂) : tensorHom ℬ f (𝟙 𝒯.cone.pt) ≫ (Bina
ryFan.rightUnitor 𝒯.isLimit (ℬ X₂ 𝒯.cone.pt).isLimit).hom = (BinaryFan.rightUnit
or 𝒯.isLimit (ℬ X₁ 𝒯.cone.pt).isLimit).hom ≫ f
参数：f : X₁ ⟶ X₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.BinaryFan.IsLimit.lift'_coe`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.Binar
yFan X Y}   (h : CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Limits.BinaryFan.rightUnitor_hom`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {X : C}   {s : CategoryTheory.Limits.Cone (Cat
egoryTheory.Functor.empty C)} (P : Ca…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightUnitor_naturality (f : X₁ ⟶ X₂) :
    tensorHom ℬ f (𝟙 𝒯.cone.pt) ≫ (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X₂ 𝒯.cone.pt).isLimit).hom =
      (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X₁ 𝒯.cone.pt).isLimit).hom ≫ f := by
  simp [tensorHom]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts.associator_nat
urality** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory.ofCh
osenFiniteProducts`。
形式化陈述：associator_naturality (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) : tenso
rHom ℬ (tensorHom ℬ f₁ f₂) f₃ ≫ (BinaryFan.associatorOfLimitCone ℬ Y₁ Y₂ Y₃).hom
 = (BinaryFan.associatorOfLimitCone ℬ X₁ X₂ X₃).hom ≫ tensorHom ℬ f₁ (tensorHom 
ℬ f₂ f₃)
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂；f₃ : X₃ ⟶ Y₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.BinaryFan.IsLimit.lift'_coe`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.Binar
yFan X Y}   (h : CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac_assoc`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp_assoc`：∀ {
J : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 :
 CategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-- Construct an instance of `CartesianMonoidalCategory C` given a terminal object and limit cones
over arbitrary pairs of objects. -/
/-
**CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts** 是 Mathlib 中的
一个缩写定义，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：ofChosenFiniteProducts : CartesianMonoidalCategory C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts.id_tenso
rHom_id`：id_tensorHom_id (X Y : C) : tensorHom ℬ (𝟙 X) (𝟙 Y) = 𝟙 (tensorObj ℬ X 
Y)
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts.tensorHo
m_comp_tensorHom`：tensorHom_comp_tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y
₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) : tensorHom ℬ f₁ f₂ ≫ tensorHom ℬ g₁ g₂ = tensorHom ℬ (…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts.associat
or_naturality`：associator_naturality (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃
) : tensorHom ℬ (tensorHom ℬ f₁ f₂) f₃ ≫ (BinaryFan.associatorOfLimitCone ℬ…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts.leftUnit
or_naturality`：leftUnitor_naturality (f : X₁ ⟶ X₂) : tensorHom ℬ (𝟙 𝒯.cone.pt) f
 ≫ (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X₂).isLimit).hom = (BinaryF…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts.rightUni
tor_naturality`：rightUnitor_naturality (f : X₁ ⟶ X₂) : tensorHom ℬ f (𝟙 𝒯.cone.p
t) ≫ (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X₂ 𝒯.cone.pt).isLimit).hom = (Binar…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts.pentagon
`：pentagon (W X Y Z : C) : tensorHom ℬ (BinaryFan.associatorOfLimitCone ℬ W X Y)
.hom (𝟙 Z) ≫ (BinaryFan.associatorOfLimitCone ℬ W (tensorObj ℬ…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.ofChosenFiniteProducts.triangle
`：triangle (X Y : C) : (BinaryFan.associatorOfLimitCone ℬ X 𝒯.cone.pt Y).hom ≫ t
ensorHom ℬ (𝟙 X) (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt …

--- 原说明 ---
Construct an instance of `CartesianMonoidalCategory C` given a terminal object a
nd limit cones
over arbitrary pairs of objects.
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
    .ofUniqueHom (𝒯.isLimit.lift <| asEmptyCone ·) fun _ _ ↦ 𝒯.isLimit.hom_ext (by simp)
  fst X Y := BinaryFan.fst (ℬ X Y).cone
  snd X Y := BinaryFan.snd (ℬ X Y).cone
  tensorProductIsBinaryProduct X Y := BinaryFan.IsLimit.mk _
    (fun f g ↦ (BinaryFan.IsLimit.lift' (ℬ X Y).isLimit f g).1)
    (fun f g ↦ (BinaryFan.IsLimit.lift' (ℬ X Y).isLimit f g).2.1)
    (fun f g ↦ (BinaryFan.IsLimit.lift' (ℬ X Y).isLimit f g).2.2)
    (fun f g m hf hg ↦
      BinaryFan.IsLimit.hom_ext (ℬ X Y).isLimit (by simpa using hf) (by simpa using hg))
  fst_def X Y := (((ℬ X 𝒯.cone.pt).isLimit.fac
    (BinaryFan.mk _ _) ⟨.left⟩).trans (Category.comp_id _)).symm
  snd_def X Y := (((ℬ 𝒯.cone.pt Y).isLimit.fac
    (BinaryFan.mk _ _) ⟨.right⟩).trans (Category.comp_id _)).symm
  }

omit 𝒯 in
/-- Constructs an instance of `CartesianMonoidalCategory C` given the existence of finite products
in `C`. -/
/-
**CategoryTheory.CartesianMonoidalCategory.ofHasFiniteProducts** 是 Mathlib 中的一个缩
写定义，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：ofHasFiniteProducts [HasFiniteProducts C] : CartesianMonoidalCategory C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an instance of `CartesianMonoidalCategory C` given the existence of f
inite products
in `C`.
-/
noncomputable abbrev ofHasFiniteProducts [HasFiniteProducts C] : CartesianMonoidalCategory C :=
  .ofChosenFiniteProducts (getLimitCone (.empty C)) (getLimitCone <| pair · ·)

end OfChosenFiniteProducts

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open MonoidalCategory

/--
Constructs a morphism to the product given its two components.
-/
/-
**CategoryTheory.CartesianMonoidalCategory.lift** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.CartesianMonoidalCategory`。
形式化陈述：lift {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : T ⟶ X otimes Y
参数：f : T ⟶ X；g : T ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs a morphism to the product given its two components.
-/
def lift {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : T ⟶ X ⊗ Y :=
  (BinaryFan.IsLimit.lift' (tensorProductIsBinaryProduct X Y) f g).1

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_fst** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.CartesianMonoidalCategory`。
形式化陈述：lift_fst {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
参数：f : T ⟶ X；g : T ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma lift_fst {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f :=
  (BinaryFan.IsLimit.lift' (tensorProductIsBinaryProduct X Y) f g).2.1

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_snd** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.CartesianMonoidalCategory`。
形式化陈述：lift_snd {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
参数：f : T ⟶ X；g : T ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma lift_snd {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g :=
  (BinaryFan.IsLimit.lift' (tensorProductIsBinaryProduct X Y) f g).2.2
/-
**CategoryTheory.CartesianMonoidalCategory.mono_lift_of_mono_left** 是 Mathlib 中的
一个实例，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：mono_lift_of_mono_left {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y) [Mono f] : Mono
 (lift f g)
参数：f : W ⟶ X；g : W ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
-/
instance mono_lift_of_mono_left {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (lift f g) :=
  mono_of_mono_fac <| lift_fst _ _
/-
**CategoryTheory.CartesianMonoidalCategory.mono_lift_of_mono_right** 是 Mathlib 中
的一个实例，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：mono_lift_of_mono_right {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y) [Mono g] : Mon
o (lift f g)
参数：f : W ⟶ X；g : W ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
-/
instance mono_lift_of_mono_right {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (lift f g) :=
  mono_of_mono_fac <| lift_snd _ _

@[ext 1050]
/-
**CategoryTheory.CartesianMonoidalCategory.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.CartesianMonoidalCategory`。
形式化陈述：hom_ext {T X Y : C} (f g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst 
_ _) (h_snd : f ≫ snd _ _ = g ≫ snd _ _) : f = g
参数：f g : T ⟶ X otimes Y；h_fst : f ≫ fst _ _ = g ≫ fst _ _；h_snd : f ≫ snd _ _ = 
g ≫ snd _ _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.BinaryFan.IsLimit.hom_ext`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {W X Y : C} {s : CategoryTheory.Limits.BinaryF
an X Y}   (h : CategoryTheory.Limits.…
-/
lemma hom_ext {T X Y : C} (f g : T ⟶ X ⊗ Y)
    (h_fst : f ≫ fst _ _ = g ≫ fst _ _)
    (h_snd : f ≫ snd _ _ = g ≫ snd _ _) :
    f = g :=
  BinaryFan.IsLimit.hom_ext (tensorProductIsBinaryProduct X Y) h_fst h_snd

-- Similarly to `CategoryTheory.Limits.prod.comp_lift`, we do not make the `assoc` version a simp
-- lemma
@[reassoc, simp]
/-
**CategoryTheory.CartesianMonoidalCategory.comp_lift** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：comp_lift {V W X Y : C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) : f ≫ lift g h
 = lift (f ≫ g) (f ≫ h)
参数：f : V ⟶ W；g : W ⟶ X；h : W ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
-/
lemma comp_lift {V W X Y : C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) :
    f ≫ lift g h = lift (f ≫ g) (f ≫ h) := by ext <;> simp

@[simp]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_fst_snd** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：lift_fst_snd {X Y : C} : lift (fst X Y) (snd X Y) = 𝟙 (X otimes Y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
-/
lemma lift_fst_snd {X Y : C} : lift (fst X Y) (snd X Y) = 𝟙 (X ⊗ Y) := by ext <;> simp

@[simp]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_comp_fst_snd** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：lift_comp_fst_snd {X Y Z : C} (f : X ⟶ Y otimes Z) : lift (f ≫ fst _ _) (f
 ≫ snd _ _) = f
参数：f : X ⟶ Y otimes Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
-/
lemma lift_comp_fst_snd {X Y Z : C} (f : X ⟶ Y ⊗ Z) :
    lift (f ≫ fst _ _) (f ≫ snd _ _) = f := by
  cat_disch

/-- The universal property of a cartesian `⊗` as an equivalence. -/
@[simps]
/-
**CategoryTheory.CartesianMonoidalCategory.liftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：liftEquiv {T X Y : C} : (T ⟶ X) × (T ⟶ Y) ≃ (T ⟶ X otimes Y) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of a cartesian `⊗` as an equivalence.
-/
def liftEquiv {T X Y : C} : (T ⟶ X) × (T ⟶ Y) ≃ (T ⟶ X ⊗ Y) where
  toFun f := lift f.1 f.2
  invFun f := ⟨f ≫ fst _ _, f ≫ snd _ _⟩
  left_inv := by cat_disch
  right_inv := by cat_disch

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.whiskerLeft_fst** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：whiskerLeft_fst (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ fst _ _ = fst _ _
参数：X : C；f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.fst_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.IsTerminal.comp_from`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {Z : C} (t : CategoryTheory.Limits.IsTerminal Z)
 {X Y : C}   (f : X ⟶ Y), Catego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerLeft_fst (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ fst _ _ = fst _ _ := by
  simp [fst_def, ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.whiskerLeft_snd** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：whiskerLeft_snd (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ snd _ _ = snd _ _ 
≫ f
参数：X : C；f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.snd_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerLeft_snd (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ snd _ _ = snd _ _ ≫ f := by
  simp [snd_def, whisker_exchange_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.whiskerRight_fst** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：whiskerRight_fst {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ fst _ _ = fst _ _
 ≫ f
参数：f : X ⟶ Y；Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.fst_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerRight_fst {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ fst _ _ = fst _ _ ≫ f := by
  simp [fst_def, ← whisker_exchange_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.whiskerRight_snd** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：whiskerRight_snd {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ snd _ _ = snd _ _
参数：f : X ⟶ Y；Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.snd_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.IsTerminal.comp_from`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {Z : C} (t : CategoryTheory.Limits.IsTerminal Z)
 {X Y : C}   (f : X ⟶ Y), Catego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerRight_snd {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ snd _ _ = snd _ _ := by
  simp [snd_def, ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.tensorHom_fst** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：tensorHom_fst {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g
) ≫ fst _ _ = fst _ _ ≫ f
参数：f : X₁ ⟶ X₂；g : Y₁ ⟶ Y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_fst`：whiskerLeft_fs
t (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ fst _ _ = fst _ _
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerRight_fst`：whiskerRight_
fst {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ fst _ _ = fst _ _ ≫ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensorHom_fst {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (f ⊗ₘ g) ≫ fst _ _ = fst _ _ ≫ f := by simp [tensorHom_def]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.tensorHom_snd** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：tensorHom_snd {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g
) ≫ snd _ _ = snd _ _ ≫ g
参数：f : X₁ ⟶ X₂；g : Y₁ ⟶ Y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_snd`：whiskerLeft_sn
d (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ snd _ _ = snd _ _ ≫ f
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.whiskerRight_snd_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Carte
sianMonoidalCategory C] {X Y : C}   (f : X ⟶ Y) (Z : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensorHom_snd {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (f ⊗ₘ g) ≫ snd _ _ = snd _ _ ≫ g := by simp [tensorHom_def]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_map** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.CartesianMonoidalCategory`。
形式化陈述：lift_map {V W X Y Z : C} (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) :
 lift f g ≫ (h otimesₘ k) = lift (f ≫ h) (g ≫ k)
参数：f : V ⟶ W；g : V ⟶ X；h : W ⟶ Y；k : X ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.tensorHom_fst`：tensorHom_fst {X
₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g) ≫ fst _ _ = fst _ _ 
≫ f
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_fst_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMono
idalCategory C]   {T X Y : C} (f : T ⟶ X) (g …
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.tensorHom_snd`：tensorHom_snd {X
₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g) ≫ snd _ _ = snd _ _ 
≫ g
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_snd_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMono
idalCategory C]   {T X Y : C} (f : T ⟶ X) (g …
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
-/
lemma lift_map {V W X Y Z : C} (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) :
    lift f g ≫ (h ⊗ₘ k) = lift (f ≫ h) (g ≫ k) := by ext <;> simp

@[simp]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_fst_comp_snd_comp** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：lift_fst_comp_snd_comp {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z) : lift (fst 
_ _ ≫ g) (snd _ _ ≫ g') = g otimesₘ g'
参数：g : W ⟶ X；g' : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.tensorHom_fst`：tensorHom_fst {X
₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g) ≫ fst _ _ = fst _ _ 
≫ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.tensorHom_snd`：tensorHom_snd {X
₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g) ≫ snd _ _ = snd _ _ 
≫ g
-/
lemma lift_fst_comp_snd_comp {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z) :
    lift (fst _ _ ≫ g) (snd _ _ ≫ g') = g ⊗ₘ g' := by ext <;> simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_whiskerRight** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：lift_whiskerRight {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) : lift
 f g ≫ (h ▷ Z) = lift (f ≫ h) g
参数：f : X ⟶ Y；g : X ⟶ Z；h : Y ⟶ W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerRight_fst`：whiskerRight_
fst {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ fst _ _ = fst _ _ ≫ f
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_fst_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMono
idalCategory C]   {T X Y : C} (f : T ⟶ X) (g …
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerRight_snd`：whiskerRight_
snd {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ snd _ _ = snd _ _
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
-/
lemma lift_whiskerRight {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) :
    lift f g ≫ (h ▷ Z) = lift (f ≫ h) g := by
  cat_disch

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_whiskerLeft** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：lift_whiskerLeft {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Z ⟶ W) : lift 
f g ≫ (Y ◁ h) = lift f (g ≫ h)
参数：f : X ⟶ Y；g : X ⟶ Z；h : Z ⟶ W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_fst`：whiskerLeft_fs
t (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ fst _ _ = fst _ _
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_snd`：whiskerLeft_sn
d (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ snd _ _ = snd _ _ ≫ f
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_snd_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMono
idalCategory C]   {T X Y : C} (f : T ⟶ X) (g …
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
-/
lemma lift_whiskerLeft {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Z ⟶ W) :
    lift f g ≫ (Y ◁ h) = lift f (g ≫ h) := by
  cat_disch

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.associator_hom_fst** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：associator_hom_fst (X Y Z : C) : (α_ X Y Z).hom ≫ fst _ _ = fst _ _ ≫ fst 
_ _
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.fst_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsTerminal.comp_from`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {Z : C} (t : CategoryTheory.Limits.IsTerminal Z)
 {X Y : C}   (f : X ⟶ Y), Catego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_hom_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ fst _ _ = fst _ _ ≫ fst _ _ := by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor,
    ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.associator_hom_snd_fst** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：associator_hom_snd_fst (X Y Z : C) : (α_ X Y Z).hom ≫ snd _ _ ≫ fst _ _ = 
fst _ _ ≫ snd _ _
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.fst_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_snd`：whiskerLeft_sn
d (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ snd _ _ = snd _ _ ≫ f
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_snd_assoc`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Cartes
ianMonoidalCategory C] (X : C)   {Y Z : C} (f : Y ⟶ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_hom_snd_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ snd _ _ ≫ fst _ _ = fst _ _ ≫ snd _ _ := by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.associator_hom_snd_snd** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：associator_hom_snd_snd (X Y Z : C) : (α_ X Y Z).hom ≫ snd _ _ ≫ snd _ _ = 
snd _ _
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.snd_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.IsTerminal.comp_from`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {Z : C} (t : CategoryTheory.Limits.IsTerminal Z)
 {X Y : C}   (f : X ⟶ Y), Catego…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_hom_snd_snd (X Y Z : C) :
    (α_ X Y Z).hom ≫ snd _ _ ≫ snd _ _ = snd _ _ := by
  simp [snd_def, ← leftUnitor_whiskerRight_assoc, -leftUnitor_whiskerRight,
    ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.associator_inv_fst_fst** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：associator_inv_fst_fst (X Y Z : C) : (α_ X Y Z).inv ≫ fst _ _ ≫ fst _ _ = 
fst _ _
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.fst_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsTerminal.comp_from`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {Z : C} (t : CategoryTheory.Limits.IsTerminal Z)
 {X Y : C}   (f : X ⟶ Y), Catego…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_inv_fst_fst (X Y Z : C) :
    (α_ X Y Z).inv ≫ fst _ _ ≫ fst _ _ = fst _ _ := by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor,
    ← whiskerLeft_comp_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.associator_inv_fst_snd** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：associator_inv_fst_snd (X Y Z : C) : (α_ X Y Z).inv ≫ fst _ _ ≫ snd _ _ = 
snd _ _ ≫ fst _ _
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.fst_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `CategoryTheory.MonoidalCategory.tensor_whiskerLeft`：tensor_whiskerLeft (
X Y : C) {Z Z' : C} (f : Z ⟶ Z') : (X otimes Y) ◁ f = (α_ X Y Z).hom ≫ X ◁ Y ◁ f
 ≫ (α_ X Y Z').inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_snd`：whiskerLeft_sn
d (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ snd _ _ = snd _ _ ≫ f
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_snd_assoc`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Cartes
ianMonoidalCategory C] (X : C)   {Y Z : C} (f : Y ⟶ …
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_inv_fst_snd (X Y Z : C) :
    (α_ X Y Z).inv ≫ fst _ _ ≫ snd _ _ = snd _ _ ≫ fst _ _ := by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.associator_inv_snd** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：associator_inv_snd (X Y Z : C) : (α_ X Y Z).inv ≫ snd _ _ = snd _ _ ≫ snd 
_ _
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.snd_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor`：whiskerRight_tensor
 {X X' : C} (f : X ⟶ X') (Y Z : C) : f ▷ (Y otimes Z) = (α_ X Y Z).inv ≫ f ▷ Y ▷
 Z ≫ (α_ X' Y Z).hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.IsTerminal.comp_from`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {Z : C} (t : CategoryTheory.Limits.IsTerminal Z)
 {X Y : C}   (f : X ⟶ Y), Catego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_inv_snd (X Y Z : C) :
    (α_ X Y Z).inv ≫ snd _ _ = snd _ _ ≫ snd _ _ := by
  simp [snd_def, ← leftUnitor_whiskerRight_assoc, -leftUnitor_whiskerRight,
    ← comp_whiskerRight_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_lift_associator_hom** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：lift_lift_associator_hom {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W)
 : lift (lift f g) h ≫ (α_ Y Z W).hom = lift f (lift g h)
参数：f : X ⟶ Y；g : X ⟶ Z；h : X ⟶ W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.associator_hom_fst`：associator_
hom_fst (X Y Z : C) : (α_ X Y Z).hom ≫ fst _ _ = fst _ _ ≫ fst _ _
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_fst_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMono
idalCategory C]   {T X Y : C} (f : T ⟶ X) (g …
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.associator_hom_snd_fst`：associa
tor_hom_snd_fst (X Y Z : C) : (α_ X Y Z).hom ≫ snd _ _ ≫ fst _ _ = fst _ _ ≫ snd
 _ _
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.associator_hom_snd_snd`：associa
tor_hom_snd_snd (X Y Z : C) : (α_ X Y Z).hom ≫ snd _ _ ≫ snd _ _ = snd _ _
-/
lemma lift_lift_associator_hom {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) :
    lift (lift f g) h ≫ (α_ Y Z W).hom = lift f (lift g h) := by
  cat_disch

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_lift_associator_inv** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：lift_lift_associator_inv {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W)
 : lift f (lift g h) ≫ (α_ Y Z W).inv = lift (lift f g) h
参数：f : X ⟶ Y；g : X ⟶ Z；h : X ⟶ W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.associator_inv_fst_fst`：associa
tor_inv_fst_fst (X Y Z : C) : (α_ X Y Z).inv ≫ fst _ _ ≫ fst _ _ = fst _ _
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.associator_inv_fst_snd`：associa
tor_inv_fst_snd (X Y Z : C) : (α_ X Y Z).inv ≫ fst _ _ ≫ snd _ _ = snd _ _ ≫ fst
 _ _
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_snd_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMono
idalCategory C]   {T X Y : C} (f : T ⟶ X) (g …
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.associator_inv_snd`：associator_
inv_snd (X Y Z : C) : (α_ X Y Z).inv ≫ snd _ _ = snd _ _ ≫ snd _ _
-/
lemma lift_lift_associator_inv {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) :
    lift f (lift g h) ≫ (α_ Y Z W).inv = lift (lift f g) h := by
  cat_disch
/-
**CategoryTheory.CartesianMonoidalCategory.leftUnitor_hom** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：leftUnitor_hom (X : C) : (fun_ X).hom = snd _ _
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.snd_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.IsTerminal.from_self`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {X : C} (t : CategoryTheory.Limits.IsTerminal X)
,   t.from X = CategoryTheory.Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftUnitor_hom (X : C) : (λ_ X).hom = snd _ _ := by simp [snd_def]
/-
**CategoryTheory.CartesianMonoidalCategory.rightUnitor_hom** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：rightUnitor_hom (X : C) : (ρ_ X).hom = fst _ _
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.fst_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.IsTerminal.from_self`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {X : C} (t : CategoryTheory.Limits.IsTerminal X)
,   t.from X = CategoryTheory.Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightUnitor_hom (X : C) : (ρ_ X).hom = fst _ _ := by simp [fst_def]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.leftUnitor_inv_fst** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：leftUnitor_inv_fst (X : C) : (fun_ X).inv ≫ fst _ _ = toUnit _
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
-/
lemma leftUnitor_inv_fst (X : C) :
    (λ_ X).inv ≫ fst _ _ = toUnit _ := toUnit_unique _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.leftUnitor_inv_snd** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：leftUnitor_inv_snd (X : C) : (fun_ X).inv ≫ snd _ _ = 𝟙 X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.snd_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.IsTerminal.from_self`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {X : C} (t : CategoryTheory.Limits.IsTerminal X)
,   t.from X = CategoryTheory.Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftUnitor_inv_snd (X : C) :
    (λ_ X).inv ≫ snd _ _ = 𝟙 X := by simp [snd_def]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.rightUnitor_inv_fst** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：rightUnitor_inv_fst (X : C) : (ρ_ X).inv ≫ fst _ _ = 𝟙 X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.fst_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `CategoryTheory.Limits.IsTerminal.from_self`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {X : C} (t : CategoryTheory.Limits.IsTerminal X)
,   t.from X = CategoryTheory.Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_id`：∀ {C : Type u} {𝒞 : Cate
goryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : 
C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightUnitor_inv_fst (X : C) :
    (ρ_ X).inv ≫ fst _ _ = 𝟙 X := by simp [fst_def]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.rightUnitor_inv_snd** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：rightUnitor_inv_snd (X : C) : (ρ_ X).inv ≫ snd _ _ = toUnit _
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
-/
lemma rightUnitor_inv_snd (X : C) :
    (ρ_ X).inv ≫ snd _ _ = toUnit _ := toUnit_unique _ _

@[reassoc]
/-
**CategoryTheory.CartesianMonoidalCategory.whiskerLeft_toUnit_comp_rightUnitor_h
om** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：whiskerLeft_toUnit_comp_rightUnitor_hom (X Y : C) : X ◁ toUnit Y ≫ (ρ_ X).
hom = fst X Y
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_fst`：whiskerLeft_fs
t (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ fst _ _ = fst _ _
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.rightUnitor_inv_fst`：rightUnito
r_inv_fst (X : C) : (ρ_ X).inv ≫ fst _ _ = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
-/
lemma whiskerLeft_toUnit_comp_rightUnitor_hom (X Y : C) : X ◁ toUnit Y ≫ (ρ_ X).hom = fst X Y := by
  rw [← cancel_mono (ρ_ X).inv]; aesop

@[reassoc]
/-
**CategoryTheory.CartesianMonoidalCategory.whiskerRight_toUnit_comp_leftUnitor_h
om** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：whiskerRight_toUnit_comp_leftUnitor_hom (X Y : C) : toUnit X ▷ Y ≫ (fun_ Y
).hom = snd X Y
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerRight_snd`：whiskerRight_
snd {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ snd _ _ = snd _ _
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.leftUnitor_inv_snd`：leftUnitor_
inv_snd (X : C) : (fun_ X).inv ≫ snd _ _ = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerRight_toUnit_comp_leftUnitor_hom (X Y : C) : toUnit X ▷ Y ≫ (λ_ Y).hom = snd X Y := by
  rw [← cancel_mono (λ_ Y).inv]; aesop

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_leftUnitor_hom** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：lift_leftUnitor_hom {X Y : C} (f : X ⟶ 𝟙_ C) (g : X ⟶ Y) : lift f g ≫ (fun
_ Y).hom = g
参数：f : X ⟶ 𝟙_ C；g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.leftUnitor_inv_snd`：leftUnitor_
inv_snd (X : C) : (fun_ X).inv ≫ snd _ _ = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_leftUnitor_hom {X Y : C} (f : X ⟶ 𝟙_ C) (g : X ⟶ Y) :
    lift f g ≫ (λ_ Y).hom = g := by
  rw [← Iso.eq_comp_inv]
  cat_disch

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_rightUnitor_hom** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：lift_rightUnitor_hom {X Y : C} (f : X ⟶ Y) (g : X ⟶ 𝟙_ C) : lift f g ≫ (ρ_
 Y).hom = f
参数：f : X ⟶ Y；g : X ⟶ 𝟙_ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.rightUnitor_inv_fst`：rightUnito
r_inv_fst (X : C) : (ρ_ X).inv ≫ fst _ _ = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
-/
lemma lift_rightUnitor_hom {X Y : C} (f : X ⟶ Y) (g : X ⟶ 𝟙_ C) :
    lift f g ≫ (ρ_ Y).hom = f := by
  rw [← Iso.eq_comp_inv]
  cat_disch

/-- Universal property of the Cartesian product: Maps to `X ⊗ Y` correspond to pairs of maps to `X`
and to `Y`. -/
@[simps]
/-
**CategoryTheory.CartesianMonoidalCategory.homEquivToProd** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：homEquivToProd {X Y Z : C} : (Z ⟶ X otimes Y) ≃ (Z ⟶ X) × (Z ⟶ Y) where to
Fun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Universal property of the Cartesian product: Maps to `X ⊗ Y` correspond to pairs
 of maps to `X`
and to `Y`.
-/
def homEquivToProd {X Y Z : C} : (Z ⟶ X ⊗ Y) ≃ (Z ⟶ X) × (Z ⟶ Y) where
  toFun f := ⟨f ≫ fst _ _, f ≫ snd _ _⟩
  invFun f := lift f.1 f.2
  left_inv _ := by simp
  right_inv _ := by simp

section BraidedCategory

variable [BraidedCategory C]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.braiding_hom_fst** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：braiding_hom_fst (X Y : C) : (β_ X Y).hom ≫ fst _ _ = snd _ _
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.fst_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.braiding_tensorUnit_left`：braiding_tensorUnit_left (X : C
) : (β_ (𝟙_ C) X).hom = (fun_ X).hom ≫ (ρ_ X).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.snd_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem braiding_hom_fst (X Y : C) : (β_ X Y).hom ≫ fst _ _ = snd _ _ := by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_naturality_left_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.braiding_hom_snd** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：braiding_hom_snd (X Y : C) : (β_ X Y).hom ≫ snd _ _ = fst _ _
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.snd_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.braiding_tensorUnit_right`：braiding_tensorUnit_right (X :
 C) : (β_ X (𝟙_ C)).hom = (ρ_ X).hom ≫ (fun_ X).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.fst_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem braiding_hom_snd (X Y : C) : (β_ X Y).hom ≫ snd _ _ = fst _ _ := by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_naturality_right_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.braiding_inv_fst** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：braiding_inv_fst (X Y : C) : (β_ X Y).inv ≫ fst _ _ = snd _ _
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.fst_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.braiding_inv_tensorUnit_right`：braiding_inv_tensorUnit_ri
ght (X : C) : (β_ X (𝟙_ C)).inv = (fun_ X).hom ≫ (ρ_ X).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.snd_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem braiding_inv_fst (X Y : C) : (β_ X Y).inv ≫ fst _ _ = snd _ _ := by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_inv_naturality_left_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.braiding_inv_snd** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：braiding_inv_snd (X Y : C) : (β_ X Y).inv ≫ snd _ _ = fst _ _
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.snd_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.braiding_inv_tensorUnit_left`：braiding_inv_tensorUnit_lef
t (X : C) : (β_ (𝟙_ C) X).inv = (ρ_ X).hom ≫ (fun_ X).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.SemiCartesianMonoidalCategory.fst_def`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.SemiCartesianMonoi
dalCategory C]   (X Y : C),   CategoryTheo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem braiding_inv_snd (X Y : C) : (β_ X Y).inv ≫ snd _ _ = fst _ _ := by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_inv_naturality_right_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.tensor** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.CartesianMonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorμ_fst (W X Y Z : C) : tensorμ W X Y Z ≫ fst (W ⊗ Y) (X ⊗ Z) = fst W X ⊗ₘ fst Y Z := by
  ext <;> simp [tensorμ]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.tensor** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.CartesianMonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorμ_snd (W X Y Z : C) : tensorμ W X Y Z ≫ snd (W ⊗ Y) (X ⊗ Z) = snd W X ⊗ₘ snd Y Z := by
  ext <;> simp [tensorμ]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.tensor** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.CartesianMonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorδ_fst (W X Y Z : C) : tensorδ W X Y Z ≫ fst (W ⊗ X) (Y ⊗ Z) = fst W Y ⊗ₘ fst X Z := by
  ext <;> simp [tensorδ]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.tensor** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.CartesianMonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorδ_snd (W X Y Z : C) : tensorδ W X Y Z ≫ snd (W ⊗ X) (Y ⊗ Z) = snd W Y ⊗ₘ snd X Z := by
  ext <;> simp [tensorδ]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_snd_fst** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：lift_snd_fst {X Y : C} : lift (snd X Y) (fst X Y) = (β_ X Y).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.braiding_hom_fst`：braiding_hom_
fst (X Y : C) : (β_ X Y).hom ≫ fst _ _ = snd _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.braiding_hom_snd`：braiding_hom_
snd (X Y : C) : (β_ X Y).hom ≫ snd _ _ = fst _ _
-/
theorem lift_snd_fst {X Y : C} : lift (snd X Y) (fst X Y) = (β_ X Y).hom := by cat_disch

@[simp, reassoc]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_snd_comp_fst_comp** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：lift_snd_comp_fst_comp {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z) : lift (snd 
_ _ ≫ g') (fst _ _ ≫ g) = (β_ _ _).hom ≫ (g' otimesₘ g)
参数：g : W ⟶ X；g' : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.tensorHom_fst`：tensorHom_fst {X
₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g) ≫ fst _ _ = fst _ _ 
≫ f
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.braiding_hom_fst_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Carte
sianMonoidalCategory C]   [inst_2 : CategoryTheory.Br…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.tensorHom_snd`：tensorHom_snd {X
₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g) ≫ snd _ _ = snd _ _ 
≫ g
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.braiding_hom_snd_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Carte
sianMonoidalCategory C]   [inst_2 : CategoryTheory.Br…
-/
lemma lift_snd_comp_fst_comp {W X Y Z : C} (g : W ⟶ X) (g' : Y ⟶ Z) :
    lift (snd _ _ ≫ g') (fst _ _ ≫ g) = (β_ _ _).hom ≫ (g' ⊗ₘ g) := by cat_disch

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_braiding_hom** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：lift_braiding_hom {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ (β_ X Y
).hom = lift g f
参数：f : T ⟶ X；g : T ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.braiding_hom_fst`：braiding_hom_
fst (X Y : C) : (β_ X Y).hom ≫ fst _ _ = snd _ _
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.braiding_hom_snd`：braiding_hom_
snd (X Y : C) : (β_ X Y).hom ≫ snd _ _ = fst _ _
-/
lemma lift_braiding_hom {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) :
    lift f g ≫ (β_ X Y).hom = lift g f := by aesop

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_braiding_inv** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：lift_braiding_inv {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ (β_ Y X
).inv = lift g f
参数：f : T ⟶ X；g : T ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.braiding_inv_fst`：braiding_inv_
fst (X Y : C) : (β_ X Y).inv ≫ fst _ _ = snd _ _
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.braiding_inv_snd`：braiding_inv_
snd (X Y : C) : (β_ X Y).inv ≫ snd _ _ = fst _ _
-/
lemma lift_braiding_inv {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) :
    lift f g ≫ (β_ Y X).inv = lift g f := by aesop

-- See note [lower instance priority]
/-
**CategoryTheory.CartesianMonoidalCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.CartesianMonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) toSymmetricCategory : SymmetricCategory C where

/-- `CartesianMonoidalCategory` implies `BraidedCategory`.
This is not an instance to prevent diamonds. -/
@[instance_reducible]
/-
**CategoryTheory.CartesianMonoidalCategory._root_.CategoryTheory.BraidedCategory
.ofCartesianMonoidalCategory** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cartesian
MonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CartesianMonoidalCategory` implies `BraidedCategory`.
This is not an instance to prevent diamonds.
-/
def _root_.CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory : BraidedCategory C where
  braiding X Y := { hom := lift (snd _ _) (fst _ _), inv := lift (snd _ _) (fst _ _) }
/-
**CategoryTheory.CartesianMonoidalCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.CartesianMonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (BraidedCategory C) := ⟨.ofCartesianMonoidalCategory⟩
/-
**CategoryTheory.CartesianMonoidalCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.CartesianMonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CategoryTheory.CartesianMonoidalCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.CartesianMonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton (SymmetricCategory C) where
  allEq := by rintro ⟨_⟩ ⟨_⟩; congr; exact Subsingleton.elim _ _

end BraidedCategory

/-
**CategoryTheory.CartesianMonoidalCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.CartesianMonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : Limits.HasFiniteProducts C :=
  letI : ∀ (X Y : C), Limits.HasLimit (Limits.pair X Y) := fun _ _ =>
    .mk ⟨_, tensorProductIsBinaryProduct _ _⟩
  letI : Limits.HasBinaryProducts C := Limits.hasBinaryProducts_of_hasLimit_pair _
  letI : Limits.HasTerminal C := Limits.hasTerminal_of_unique (𝟙_ C)
  hasFiniteProducts_of_has_binary_and_terminal

section CartesianMonoidalCategoryComparison

variable {D : Type u₁} [Category.{v₁} D] [CartesianMonoidalCategory D] (F : C ⥤ D)
variable {E : Type u₂} [Category.{v₂} E] [CartesianMonoidalCategory E] (G : D ⥤ E)

section terminalComparison

/-- When `C` and `D` have chosen finite products and `F : C ⥤ D` is any functor,
`terminalComparison F` is the unique map `F (𝟙_ C) ⟶ 𝟙_ D`. -/
/-
**CategoryTheory.CartesianMonoidalCategory.terminalComparison** 是 Mathlib 中的一个缩写
定义，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：terminalComparison : F.obj (𝟙_ C) ⟶ 𝟙_ D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `C` and `D` have chosen finite products and `F : C ⥤ D` is any functor,
`terminalComparison F` is the unique map `F (𝟙_ C) ⟶ 𝟙_ D`.
-/
abbrev terminalComparison : F.obj (𝟙_ C) ⟶ 𝟙_ D := toUnit _

@[reassoc]
/-
**CategoryTheory.CartesianMonoidalCategory.map_toUnit_comp_terminalComparison** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：map_toUnit_comp_terminalComparison (A : C) : F.map (toUnit A) ≫ terminalCo
mparison F = toUnit _
参数：A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
-/
lemma map_toUnit_comp_terminalComparison (A : C) :
    F.map (toUnit A) ≫ terminalComparison F = toUnit _ := toUnit_unique _ _

open Limits

/-- If `terminalComparison F` is an Iso, then `F` preserves terminal objects. -/
/-
**CategoryTheory.CartesianMonoidalCategory.preservesLimit_empty_of_isIso_termina
lComparison** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`
。
形式化陈述：preservesLimit_empty_of_isIso_terminalComparison [IsIso (terminalCompariso
n F)] : PreservesLimit (Functor.empty.{0} C) F
参数：terminalComparison F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…

--- 原说明 ---
If `terminalComparison F` is an Iso, then `F` preserves terminal objects.
-/
lemma preservesLimit_empty_of_isIso_terminalComparison [IsIso (terminalComparison F)] :
    PreservesLimit (Functor.empty.{0} C) F := by
  apply preservesLimit_of_preserves_limit_cone isTerminalTensorUnit
  apply isLimitChangeEmptyCone D isTerminalTensorUnit
  exact asIso (terminalComparison F) |>.symm

/-- If `F` preserves terminal objects, then `terminalComparison F` is an isomorphism. -/
/-
**CategoryTheory.CartesianMonoidalCategory.preservesTerminalIso** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：preservesTerminalIso [h : PreservesLimit (Functor.empty.{0} C) F] : F.obj 
(𝟙_ C) ≅ 𝟙_ D
参数：Functor.empty.{0} C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` preserves terminal objects, then `terminalComparison F` is an isomorphism
.
-/
noncomputable def preservesTerminalIso [h : PreservesLimit (Functor.empty.{0} C) F] :
    F.obj (𝟙_ C) ≅ 𝟙_ D :=
  (isLimitChangeEmptyCone D (isLimitOfPreserves _ isTerminalTensorUnit) (asEmptyCone (F.obj (𝟙_ C)))
    (Iso.refl _)).conePointUniqueUpToIso isTerminalTensorUnit

@[simp]
/-
**CategoryTheory.CartesianMonoidalCategory.preservesTerminalIso_hom** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：preservesTerminalIso_hom [PreservesLimit (Functor.empty.{0} C) F] : (prese
rvesTerminalIso F).hom = terminalComparison F
参数：Functor.empty.{0} C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
-/
lemma preservesTerminalIso_hom [PreservesLimit (Functor.empty.{0} C) F] :
    (preservesTerminalIso F).hom = terminalComparison F := toUnit_unique _ _
/-
**CategoryTheory.CartesianMonoidalCategory.terminalComparison_isIso_of_preserves
Limits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：terminalComparison_isIso_of_preservesLimits [PreservesLimit (Functor.empty
.{0} C) F] : IsIso (terminalComparison F)
参数：Functor.empty.{0} C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.preservesTerminalIso_hom`：prese
rvesTerminalIso_hom [PreservesLimit (Functor.empty.{0} C) F] : (preservesTermina
lIso F).hom = terminalComparison F
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance terminalComparison_isIso_of_preservesLimits [PreservesLimit (Functor.empty.{0} C) F] :
    IsIso (terminalComparison F) := by
  rw [← preservesTerminalIso_hom]
  infer_instance

@[simp]
/-
**CategoryTheory.CartesianMonoidalCategory.preservesTerminalIso_id** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：preservesTerminalIso_id : preservesTerminalIso (𝟭 C) = .refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
-/
lemma preservesTerminalIso_id : preservesTerminalIso (𝟭 C) = .refl _ := by
  cat_disch

@[simp]
/-
**CategoryTheory.CartesianMonoidalCategory.preservesTerminalIso_comp** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：preservesTerminalIso_comp [PreservesLimit (Functor.empty.{0} C) F] [Preser
vesLimit (Functor.empty.{0} D) G] [PreservesLimit (Functor.empty.{0} C) (F ⋙ G)]
 : preservesTerminalIso (F ⋙ G) = G.mapIso (preservesTerminalIso F) ≪≫ preserves
TerminalIso G
参数：Functor.empty.{0} C；Functor.empty.{0} D；Functor.empty.{0} C；F ⋙ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
-/
lemma preservesTerminalIso_comp [PreservesLimit (Functor.empty.{0} C) F]
    [PreservesLimit (Functor.empty.{0} D) G] [PreservesLimit (Functor.empty.{0} C) (F ⋙ G)] :
    preservesTerminalIso (F ⋙ G) =
      G.mapIso (preservesTerminalIso F) ≪≫ preservesTerminalIso G := by
  cat_disch

end terminalComparison

section prodComparison

variable (A B : C)

/-- When `C` and `D` have chosen finite products and `F : C ⥤ D` is any functor,
`prodComparison F A B` is the canonical comparison morphism from `F (A ⊗ B)` to `F(A) ⊗ F(B)`. -/
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparison** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparison (A B : C) : F.obj (A otimes B) ⟶ F.obj A otimes F.obj B
参数：A B : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `C` and `D` have chosen finite products and `F : C ⥤ D` is any functor,
`prodComparison F A B` is the canonical comparison morphism from `F (A ⊗ B)` to 
`F(A) ⊗ F(B)`.
-/
def prodComparison (A B : C) : F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B :=
  lift (F.map (fst A B)) (F.map (snd A B))

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparison_fst** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparison_fst : prodComparison F A B ≫ fst _ _ = F.map (fst A B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
-/
theorem prodComparison_fst : prodComparison F A B ≫ fst _ _ = F.map (fst A B) :=
  lift_fst _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparison_snd** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparison_snd : prodComparison F A B ≫ snd _ _ = F.map (snd A B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
-/
theorem prodComparison_snd : prodComparison F A B ≫ snd _ _ = F.map (snd A B) :=
  lift_snd _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.inv_prodComparison_map_fst** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：inv_prodComparison_map_fst [IsIso (prodComparison F A B)] : inv (prodCompa
rison F A B) ≫ F.map (fst _ _) = fst _ _
参数：prodComparison F A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_fst`：prodCompari
son_fst : prodComparison F A B ≫ fst _ _ = F.map (fst A B)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_prodComparison_map_fst [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map (fst _ _) = fst _ _ := by simp [IsIso.inv_comp_eq]

@[reassoc (attr := simp)]
/-
**CategoryTheory.CartesianMonoidalCategory.inv_prodComparison_map_snd** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：inv_prodComparison_map_snd [IsIso (prodComparison F A B)] : inv (prodCompa
rison F A B) ≫ F.map (snd _ _) = snd _ _
参数：prodComparison F A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_snd`：prodCompari
son_snd : prodComparison F A B ≫ snd _ _ = F.map (snd A B)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_prodComparison_map_snd [IsIso (prodComparison F A B)] :
    inv (prodComparison F A B) ≫ F.map (snd _ _) = snd _ _ := by simp [IsIso.inv_comp_eq]

variable {A B} {A' B' : C}

/-- Naturality of the `prodComparison` morphism in both arguments. -/
@[reassoc]
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparison_natural** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparison_natural (f : A ⟶ A') (g : B ⟶ B') : F.map (f otimesₘ g) ≫ p
rodComparison F A' B' = prodComparison F A B ≫ (F.map f otimesₘ F.map g)
参数：f : A ⟶ A'；g : B ⟶ B'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_fst`：prodCompari
son_fst : prodComparison F A B ≫ fst _ _ = F.map (fst A B)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.tensorHom_fst`：tensorHom_fst {X
₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g) ≫ fst _ _ = fst _ _ 
≫ f
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_fst_assoc`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Car
tesianMonoidalCategory C]   {D : Type u₁} [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_snd`：prodCompari
son_snd : prodComparison F A B ≫ snd _ _ = F.map (snd A B)
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.tensorHom_snd`：tensorHom_snd {X
₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g) ≫ snd _ _ = snd _ _ 
≫ g
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_snd_assoc`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Car
tesianMonoidalCategory C]   {D : Type u₁} [inst_2 : Cat…

--- 原说明 ---
Naturality of the `prodComparison` morphism in both arguments.
-/
theorem prodComparison_natural (f : A ⟶ A') (g : B ⟶ B') :
    F.map (f ⊗ₘ g) ≫ prodComparison F A' B' =
      prodComparison F A B ≫ (F.map f ⊗ₘ F.map g) := by
  apply hom_ext <;>
  simp only [Category.assoc, prodComparison_fst, tensorHom_fst, prodComparison_fst_assoc,
    prodComparison_snd, tensorHom_snd, prodComparison_snd_assoc, ← F.map_comp]

/-- Naturality of the `prodComparison` morphism in the right argument. -/
@[reassoc]
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparison_natural_whiskerLeft** 
是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparison_natural_whiskerLeft (g : B ⟶ B') : F.map (A ◁ g) ≫ prodComp
arison F A B' = prodComparison F A B ≫ (F.obj A ◁ F.map g)
参数：g : B ⟶ B'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_fst`：prodCompari
son_fst : prodComparison F A B ≫ fst _ _ = F.map (fst A B)
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_fst`：whiskerLeft_fs
t (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ fst _ _ = fst _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_snd`：prodCompari
son_snd : prodComparison F A B ≫ snd _ _ = F.map (snd A B)
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_snd`：whiskerLeft_sn
d (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ snd _ _ = snd _ _ ≫ f
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_snd_assoc`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Car
tesianMonoidalCategory C]   {D : Type u₁} [inst_2 : Cat…

--- 原说明 ---
Naturality of the `prodComparison` morphism in the right argument.
-/
theorem prodComparison_natural_whiskerLeft (g : B ⟶ B') :
    F.map (A ◁ g) ≫ prodComparison F A B' =
      prodComparison F A B ≫ (F.obj A ◁ F.map g) := by
  ext <;> simp [← Functor.map_comp]

/-- Naturality of the `prodComparison` morphism in the left argument. -/
@[reassoc]
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparison_natural_whiskerRight**
 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparison_natural_whiskerRight (f : A ⟶ A') : F.map (f ▷ B) ≫ prodCom
parison F A' B = prodComparison F A B ≫ (F.map f ▷ F.obj B)
参数：f : A ⟶ A'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_fst`：prodCompari
son_fst : prodComparison F A B ≫ fst _ _ = F.map (fst A B)
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerRight_fst`：whiskerRight_
fst {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ fst _ _ = fst _ _ ≫ f
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_fst_assoc`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Car
tesianMonoidalCategory C]   {D : Type u₁} [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_snd`：prodCompari
son_snd : prodComparison F A B ≫ snd _ _ = F.map (snd A B)
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerRight_snd`：whiskerRight_
snd {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ snd _ _ = snd _ _

--- 原说明 ---
Naturality of the `prodComparison` morphism in the left argument.
-/
theorem prodComparison_natural_whiskerRight (f : A ⟶ A') :
    F.map (f ▷ B) ≫ prodComparison F A' B =
      prodComparison F A B ≫ (F.map f ▷ F.obj B) := by
  ext <;> simp [← Functor.map_comp]

section
variable [IsIso (prodComparison F A B)]

/-- If the product comparison morphism is an iso, its inverse is natural in both argument. -/
@[reassoc]
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparison_inv_natural** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodCompariso
n F A' B')] : inv (prodComparison F A B) ≫ F.map (f otimesₘ g) = (F.map f otimes
ₘ F.map g) ≫ inv (prodComparison F A' B')
参数：f : A ⟶ A'；g : B ⟶ B'；prodComparison F A' B'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.eq_comp_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_comp_eq`：inv_comp_eq (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_natural`：prodCom
parison_natural (f : A ⟶ A') (g : B ⟶ B') : F.map (f otimesₘ g) ≫ prodComparison
 F A' B' = prodComparison F A B ≫ (F.map f otimesₘ F.…

--- 原说明 ---
If the product comparison morphism is an iso, its inverse is natural in both arg
ument.
-/
theorem prodComparison_inv_natural (f : A ⟶ A') (g : B ⟶ B') [IsIso (prodComparison F A' B')] :
    inv (prodComparison F A B) ≫ F.map (f ⊗ₘ g) =
      (F.map f ⊗ₘ F.map g) ≫ inv (prodComparison F A' B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural]

/-- If the product comparison morphism is an iso, its inverse is natural in the right argument. -/
@[reassoc]
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparison_inv_natural_whiskerLef
t** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparison_inv_natural_whiskerLeft (g : B ⟶ B') [IsIso (prodComparison
 F A B')] : inv (prodComparison F A B) ≫ F.map (A ◁ g) = (F.obj A ◁ F.map g) ≫ i
nv (prodComparison F A B')
参数：g : B ⟶ B'；prodComparison F A B'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.eq_comp_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_comp_eq`：inv_comp_eq (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_natural_whiskerL
eft`：prodComparison_natural_whiskerLeft (g : B ⟶ B') : F.map (A ◁ g) ≫ prodCompa
rison F A B' = prodComparison F A B ≫ (F.obj A ◁ F.map g)

--- 原说明 ---
If the product comparison morphism is an iso, its inverse is natural in the righ
t argument.
-/
theorem prodComparison_inv_natural_whiskerLeft (g : B ⟶ B') [IsIso (prodComparison F A B')] :
    inv (prodComparison F A B) ≫ F.map (A ◁ g) =
      (F.obj A ◁ F.map g) ≫ inv (prodComparison F A B') := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural_whiskerLeft]

/-- If the product comparison morphism is an iso, its inverse is natural in the left argument. -/
@[reassoc]
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparison_inv_natural_whiskerRig
ht** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparison_inv_natural_whiskerRight (f : A ⟶ A') [IsIso (prodCompariso
n F A' B)] : inv (prodComparison F A B) ≫ F.map (f ▷ B) = (F.map f ▷ F.obj B) ≫ 
inv (prodComparison F A' B)
参数：f : A ⟶ A'；prodComparison F A' B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.eq_comp_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_comp_eq`：inv_comp_eq (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_natural_whiskerR
ight`：prodComparison_natural_whiskerRight (f : A ⟶ A') : F.map (f ▷ B) ≫ prodCom
parison F A' B = prodComparison F A B ≫ (F.map f ▷ F.obj B)

--- 原说明 ---
If the product comparison morphism is an iso, its inverse is natural in the left
 argument.
-/
theorem prodComparison_inv_natural_whiskerRight (f : A ⟶ A') [IsIso (prodComparison F A' B)] :
    inv (prodComparison F A B) ≫ F.map (f ▷ B) =
      (F.map f ▷ F.obj B) ≫ inv (prodComparison F A' B) := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natural_whiskerRight]

end

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparison_comp** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparison_comp : prodComparison (F ⋙ G) A B = G.map (prodComparison F
 A B) ≫ prodComparison G (F.obj A) (F.obj B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.comp_lift`：comp_lift {V W X Y :
 C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) : f ≫ lift g h = lift (f ≫ g) (f ≫ h)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prodComparison_comp :
    prodComparison (F ⋙ G) A B =
      G.map (prodComparison F A B) ≫ prodComparison G (F.obj A) (F.obj B) := by
  unfold prodComparison
  ext <;> simp [← G.map_comp]

@[simp]
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparison_id** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparison_id : prodComparison (𝟭 C) A B = 𝟙 (A otimes B)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst_snd`：lift_fst_snd {X Y
 : C} : lift (fst X Y) (snd X Y) = 𝟙 (X otimes Y)
-/
lemma prodComparison_id :
    prodComparison (𝟭 C) A B = 𝟙 (A ⊗ B) := lift_fst_snd

set_option backward.defeqAttrib.useBackward true in
/-- The product comparison morphism from `F(A ⊗ -)` to `FA ⊗ F-`, whose components are given by
`prodComparison`. -/
@[simps]
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparisonNatTrans** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparisonNatTrans (A : C) : (curriedTensor C).obj A ⋙ F ⟶ F ⋙ (currie
dTensor D).obj (F.obj A) where app B
参数：A : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product comparison morphism from `F(A ⊗ -)` to `FA ⊗ F-`, whose components a
re given by
`prodComparison`.
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
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparisonNatTrans_comp** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparisonNatTrans_comp : prodComparisonNatTrans (F ⋙ G) A = Functor.w
hiskerRight (prodComparisonNatTrans F A) G ≫ Functor.whiskerLeft F (prodComparis
onNatTrans G (F.obj A))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_comp`：prodCompar
ison_comp : prodComparison (F ⋙ G) A B = G.map (prodComparison F A B) ≫ prodComp
arison G (F.obj A) (F.obj B)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prodComparisonNatTrans_comp :
    prodComparisonNatTrans (F ⋙ G) A = Functor.whiskerRight (prodComparisonNatTrans F A) G ≫
      Functor.whiskerLeft F (prodComparisonNatTrans G (F.obj A)) := by
  ext; simp [prodComparison_comp]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparisonNatTrans_id** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparisonNatTrans_id : prodComparisonNatTrans (𝟭 C) A = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_id`：prodComparis
on_id : prodComparison (𝟭 C) A B = 𝟙 (A otimes B)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prodComparisonNatTrans_id :
    prodComparisonNatTrans (𝟭 C) A = 𝟙 _ := by ext; simp

set_option backward.defeqAttrib.useBackward true in
/-- The product comparison morphism from `F(- ⊗ -)` to `F- ⊗ F-`, whose components are given by
`prodComparison`. -/
@[simps]
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparisonBifunctorNatTrans** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparisonBifunctorNatTrans : curriedTensor C ⋙ (Functor.whiskeringRig
ht _ _ _).obj F ⟶ F ⋙ curriedTensor D ⋙ (Functor.whiskeringLeft _ _ _).obj F whe
re app A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product comparison morphism from `F(- ⊗ -)` to `F- ⊗ F-`, whose components a
re given by
`prodComparison`.
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
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparisonBifunctorNatTrans_comp*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparisonBifunctorNatTrans_comp : prodComparisonBifunctorNatTrans (F 
⋙ G) = Functor.whiskerRight (prodComparisonBifunctorNatTrans F) ((Functor.whiske
ringRight _ _ _).obj G) ≫ Functor.whiskerLeft F (Functor.whiskerRight (prodCompa
risonBifunctorNatTrans G) ((Functor.whiskeringLeft _ _ _).obj F))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_comp`：prodCompar
ison_comp : prodComparison (F ⋙ G) A B = G.map (prodComparison F A B) ≫ prodComp
arison G (F.obj A) (F.obj B)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prodComparisonBifunctorNatTrans_comp : prodComparisonBifunctorNatTrans (F ⋙ G) =
    Functor.whiskerRight
      (prodComparisonBifunctorNatTrans F) ((Functor.whiskeringRight _ _ _).obj G) ≫
        Functor.whiskerLeft F (Functor.whiskerRight (prodComparisonBifunctorNatTrans G)
          ((Functor.whiskeringLeft _ _ _).obj F)) := by
  ext; simp [prodComparison_comp]
/-
**CategoryTheory.CartesianMonoidalCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.CartesianMonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : C) [∀ B, IsIso (prodComparison F A B)] : IsIso (prodComparisonNatTrans F A) := by
  let : ∀ X, IsIso ((prodComparisonNatTrans F A).app X) := by assumption
  apply NatIso.isIso_of_isIso_app

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.CartesianMonoidalCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.CartesianMonoidalCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ A B, IsIso (prodComparison F A B)] : IsIso (prodComparisonBifunctorNatTrans F) := by
  let : ∀ X, IsIso ((prodComparisonBifunctorNatTrans F).app X) :=
    fun _ ↦ by dsimp; apply NatIso.isIso_of_isIso_app
  apply NatIso.isIso_of_isIso_app

open Limits
section PreservesLimitPairs

section
variable (A B)
variable [PreservesLimit (pair A B) F]

/-- If `F` preserves the limit of the pair `(A, B)`, then the binary fan given by
`(F.map fst A B, F.map (snd A B))` is a limit cone. -/
/-
**CategoryTheory.CartesianMonoidalCategory.isLimitCartesianMonoidalCategoryOfPre
servesLimits** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CartesianMonoidalCategory
`。
形式化陈述：isLimitCartesianMonoidalCategoryOfPreservesLimits : IsLimit BinaryFan.mk (
F.map (fst A B)) (F.map (snd A B))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` preserves the limit of the pair `(A, B)`, then the binary fan given by
`(F.map fst A B, F.map (snd A B))` is a limit cone.
-/
noncomputable def isLimitCartesianMonoidalCategoryOfPreservesLimits :
    IsLimit <| BinaryFan.mk (F.map (fst A B)) (F.map (snd A B)) :=
  mapIsLimitOfPreservesOfIsLimit F (fst _ _) (snd _ _) <|
    (tensorProductIsBinaryProduct A B).ofIsoLimit <|
      isoBinaryFanMk (BinaryFan.mk (fst A B) (snd A B))

/-- If `F` preserves the limit of the pair `(A, B)`, then `prodComparison F A B` is an isomorphism.
-/
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparisonIso** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparisonIso : F.obj (A otimes B) ≅ F.obj A otimes F.obj B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` preserves the limit of the pair `(A, B)`, then `prodComparison F A B` is 
an isomorphism.
-/
noncomputable def prodComparisonIso : F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B :=
  IsLimit.conePointUniqueUpToIso (isLimitCartesianMonoidalCategoryOfPreservesLimits F A B)
    (tensorProductIsBinaryProduct _ _)

@[simp]
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparisonIso_hom** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparisonIso_hom : (prodComparisonIso F A B).hom = prodComparison F A
 B
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prodComparisonIso_hom : (prodComparisonIso F A B).hom = prodComparison F A B :=
  rfl
/-
**CategoryTheory.CartesianMonoidalCategory.isIso_prodComparison_of_preservesLimi
t_pair** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：isIso_prodComparison_of_preservesLimit_pair : IsIso (prodComparison F A B)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.prodComparisonIso_hom`：prodComp
arisonIso_hom : (prodComparisonIso F A B).hom = prodComparison F A B
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance isIso_prodComparison_of_preservesLimit_pair : IsIso (prodComparison F A B) := by
  rw [← prodComparisonIso_hom]
  infer_instance
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparisonIso_id** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.CartesianMonoidalCategory C]   (A B : C),   CategoryTheory.CartesianMono
idalCategory.prodComparisonIso (CategoryTheory.Functor.id C) A B =     CategoryT
heory.Iso.refl ((CategoryTheory.Functor.id C).obj (CategoryTheory.MonoidalCatego
ryStruct.tensorObj A B))
参数：A B : C；CategoryTheory.Functor.id C；(CategoryTheory.Functor.id C).obj (Catego
ryTheory.MonoidalCategoryStruct.tensorObj A B)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_id`：prodComparis
on_id : prodComparison (𝟭 C) A B = 𝟙 (A otimes B)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma prodComparisonIso_id : prodComparisonIso (𝟭 C) A B = .refl _ := by ext <;> simp

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparisonIso_comp** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparisonIso_comp [PreservesLimit (pair A B) (F ⋙ G)] [PreservesLimit
 (pair (F.obj A) (F.obj B)) G] : prodComparisonIso (F ⋙ G) A B = G.mapIso (prodC
omparisonIso F A B) ≪≫ prodComparisonIso G (F.obj A) (F.obj B)
参数：pair A B；F ⋙ G；pair (F.obj A) (F.obj B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst`：lift_fst {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.comp_lift`：comp_lift {V W X Y :
 C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) : f ≫ lift g h = lift (f ≫ g) (f ≫ h)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_snd`：lift_snd {T X Y : C} 
(f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparisonNatIso** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparisonNatIso (A : C) [forall B, PreservesLimit (pair A B) F] : (cu
rriedTensor C).obj A ⋙ F ≅ F ⋙ (curriedTensor D).obj (F.obj A)
参数：A : C；pair A B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism `F(A ⊗ -) ≅ FA ⊗ F-`, provided each `prodComparison F A 
B` is an
isomorphism (as `B` changes).
-/
noncomputable def prodComparisonNatIso (A : C) [∀ B, PreservesLimit (pair A B) F] :
    (curriedTensor C).obj A ⋙ F ≅ F ⋙ (curriedTensor D).obj (F.obj A) :=
  asIso (prodComparisonNatTrans F A)

/-- The natural isomorphism of bifunctors `F(- ⊗ -) ≅ F- ⊗ F-`, provided each
`prodComparison F A B` is an isomorphism. -/
@[simps! hom inv]
/-
**CategoryTheory.CartesianMonoidalCategory.prodComparisonBifunctorNatIso** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：prodComparisonBifunctorNatIso [forall A B, PreservesLimit (pair A B) F] : 
curriedTensor C ⋙ (Functor.whiskeringRight _ _ _).obj F ≅ F ⋙ curriedTensor D ⋙ 
(Functor.whiskeringLeft _ _ _).obj F
参数：pair A B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism of bifunctors `F(- ⊗ -) ≅ F- ⊗ F-`, provided each
`prodComparison F A B` is an isomorphism.
-/
noncomputable def prodComparisonBifunctorNatIso [∀ A B, PreservesLimit (pair A B) F] :
    curriedTensor C ⋙ (Functor.whiskeringRight _ _ _).obj F ≅
      F ⋙ curriedTensor D ⋙ (Functor.whiskeringLeft _ _ _).obj F :=
  asIso (prodComparisonBifunctorNatTrans F)

end PreservesLimitPairs

section ProdComparisonIso

set_option backward.isDefEq.respectTransparency false in
/-- If `prodComparison F A B` is an isomorphism, then `F` preserves the limit of `pair A B`. -/
/-
**CategoryTheory.CartesianMonoidalCategory.preservesLimit_pair_of_isIso_prodComp
arison** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：preservesLimit_pair_of_isIso_prodComparison (A B : C) [IsIso (prodComparis
on F A B)] : PreservesLimit (pair A B) F
参数：A B : C；prodComparison F A B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.diagramIsoPair_hom_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C]   (F : CategoryTheory.Functor (CategoryTheory.Dis
crete CategoryTheory.Limits.Walkin…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_fst`：prodCompari
son_fst : prodComparison F A B ≫ fst _ _ = F.map (fst A B)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_snd`：prodCompari
son_snd : prodComparison F A B ≫ snd _ _ = F.map (snd A B)

--- 原说明 ---
If `prodComparison F A B` is an isomorphism, then `F` preserves the limit of `pa
ir A B`.
-/
lemma preservesLimit_pair_of_isIso_prodComparison (A B : C)
    [IsIso (prodComparison F A B)] :
    PreservesLimit (pair A B) F := by
  apply preservesLimit_of_preserves_limit_cone (tensorProductIsBinaryProduct A B)
  refine IsLimit.equivOfNatIsoOfIso (pairComp A B F) _
    ((BinaryFan.mk (fst (F.obj A) (F.obj B)) (snd _ _)).extend (prodComparison F A B))
      (BinaryFan.ext (by exact Iso.refl _) ?_ ?_) |>.invFun
      (IsLimit.extendIso _ (tensorProductIsBinaryProduct (F.obj A) (F.obj B)))
  · dsimp only [BinaryFan.fst]
    simp [pairComp]
  · dsimp only [BinaryFan.snd]
    simp [pairComp]

/-- If `prodComparison F A B` is an isomorphism for all `A B` then `F` preserves limits of shape
`Discrete (WalkingPair)`. -/
/-
**CategoryTheory.CartesianMonoidalCategory.preservesLimitsOfShape_discrete_walki
ngPair_of_isIso_prodComparison** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Cartesi
anMonoidalCategory`。
形式化陈述：preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison [foral
l A B, IsIso (prodComparison F A B)] : PreservesLimitsOfShape (Discrete WalkingP
air) F
参数：prodComparison F A B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.preservesLimit_pair_of_isIso_pr
odComparison`：preservesLimit_pair_of_isIso_prodComparison (A B : C) [IsIso (prod
Comparison F A B)] : PreservesLimit (pair A B) F

--- 原说明 ---
If `prodComparison F A B` is an isomorphism for all `A B` then `F` preserves lim
its of shape
`Discrete (WalkingPair)`.
-/
lemma preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison
    [∀ A B, IsIso (prodComparison F A B)] : PreservesLimitsOfShape (Discrete WalkingPair) F := by
  constructor
  intro K
  refine @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoPair K).symm ?_
  apply preservesLimit_pair_of_isIso_prodComparison

end ProdComparisonIso

end prodComparison

end CartesianMonoidalCategoryComparison

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- In a cartesian monoidal category, `tensorLeft X` is naturally isomorphic `prod.functor.obj X`.
-/
/-
**CategoryTheory.CartesianMonoidalCategory.tensorLeftIsoProd** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：tensorLeftIsoProd [HasBinaryProducts C] (X : C) : MonoidalCategory.tensorL
eft X ≅ prod.functor.obj X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a cartesian monoidal category, `tensorLeft X` is naturally isomorphic `prod.f
unctor.obj X`.
-/
noncomputable def tensorLeftIsoProd [HasBinaryProducts C] (X : C) :
    MonoidalCategory.tensorLeft X ≅ prod.functor.obj X :=
  NatIso.ofComponents fun Y ↦
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
/-
**CategoryTheory.CartesianMonoidalCategory.fullSubcategory** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：fullSubcategory [P.IsClosedUnderLimitsOfShape (Discrete PEmpty)] [P.IsClos
edUnderLimitsOfShape (Discrete WalkingPair)] : CartesianMonoidalCategory P.FullS
ubcategory where __
参数：Discrete PEmpty；Discrete WalkingPair。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a Cartesian-monoidal category along an object property that's
 closed under
finite products is Cartesian-monoidal.
-/
instance fullSubcategory
    [P.IsClosedUnderLimitsOfShape (Discrete PEmpty)]
    [P.IsClosedUnderLimitsOfShape (Discrete WalkingPair)] :
    CartesianMonoidalCategory P.FullSubcategory where
  __ := MonoidalCategory.fullSubcategory P
      (P.prop_of_isLimit isTerminalTensorUnit (by simp))
      (fun X Y hX hY ↦ P.prop_of_isLimit (tensorProductIsBinaryProduct X Y)
        (by rintro (_ | _) <;> assumption))
  isTerminalTensorUnit := .ofUniqueHom (fun X ↦ ObjectProperty.homMk (toUnit X.1))
    fun _ _ ↦ by ext; apply toUnit_unique
  fst X Y := ObjectProperty.homMk (fst X.1 Y.1)
  snd X Y := ObjectProperty.homMk (snd X.1 Y.1)
  tensorProductIsBinaryProduct X Y :=
    BinaryFan.IsLimit.mk _ (fun f g ↦ ObjectProperty.homMk (lift f.hom g.hom))
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

/-
**CategoryTheory.Functor.OplaxMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Functor.OplaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma η_of_cartesianMonoidalCategory :
    η F = CartesianMonoidalCategory.terminalComparison F := toUnit_unique ..

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.OplaxMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Functor.OplaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_fst (X Y : C) :
    δ F X Y ≫ fst _ _ = F.map (fst _ _) := by
  trans F.map (X ◁ toUnit Y) ≫ F.map (ρ_ X).hom
  · rw [← whiskerLeft_fst _ (F.map (toUnit Y)), δ_natural_right_assoc]
    simp [← OplaxMonoidal.right_unitality_hom, rightUnitor_hom (F.obj X)]
  · simp [← Functor.map_comp, rightUnitor_hom]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.OplaxMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Functor.OplaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_snd (X Y : C) :
    δ F X Y ≫ snd _ _ = F.map (snd _ _) := by
  trans F.map (toUnit X ▷ Y) ≫ F.map (λ_ Y).hom
  · rw [← whiskerRight_snd (F.map (toUnit X)), δ_natural_left_assoc]
    simp [← OplaxMonoidal.left_unitality_hom, leftUnitor_hom (F.obj Y)]
  · simp [← Functor.map_comp, leftUnitor_hom]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.OplaxMonoidal.lift_** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor.OplaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_δ (f : X ⟶ Y) (g : X ⟶ Z) : F.map (lift f g) ≫ δ F _ _ = lift (F.map f) (F.map g) := by
  ext <;> simp [← map_comp]
/-
**CategoryTheory.Functor.OplaxMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Functor.OplaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_of_cartesianMonoidalCategory (X Y : C) :
    δ F X Y = CartesianMonoidalCategory.prodComparison F X Y := by cat_disch

variable [PreservesFiniteProducts F]
/-
**CategoryTheory.Functor.OplaxMonoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Functor.OplaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (η F) :=
  η_of_cartesianMonoidalCategory F ▸ terminalComparison_isIso_of_preservesLimits F
/-
**CategoryTheory.Functor.OplaxMonoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Functor.OplaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : C) : IsIso (δ F X Y) :=
  δ_of_cartesianMonoidalCategory F X Y ▸ isIso_prodComparison_of_preservesLimit_pair F X Y

omit [F.OplaxMonoidal] in
/-- Any functor between Cartesian-monoidal categories is oplax monoidal.

This is not made an instance because it would create a diamond for the oplax monoidal structure on
the identity and composition of functors. -/
@[instance_reducible]
/-
**CategoryTheory.Functor.OplaxMonoidal.ofChosenFiniteProducts** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Functor.OplaxMonoidal`。
形式化陈述：ofChosenFiniteProducts (F : C ⥤ D) : F.OplaxMonoidal where η
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any functor between Cartesian-monoidal categories is oplax monoidal.

This is not made an instance because it would create a diamond for the oplax mon
oidal structure on
the identity and composition of functors.
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
/-- Any functor between Cartesian-monoidal categories is oplax monoidal in a unique way. -/
/-
**CategoryTheory.Functor.OplaxMonoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Functor.OplaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any functor between Cartesian-monoidal categories is oplax monoidal in a unique 
way.
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
/-
**CategoryTheory.Functor.Monoidal.toUnit_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toUnit_ε (X : C) : toUnit (F.obj X) ≫ ε F = F.map (toUnit X) := by
  rw [← cancel_mono (εIso F).inv]; exact toUnit_unique ..

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Monoidal.lift_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_μ (f : X ⟶ Y) (g : X ⟶ Z) : lift (F.map f) (F.map g) ≫ μ F _ _ = F.map (lift f g) :=
  (cancel_mono (μIso _ _ _).inv).1 (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_fst (X Y : C) : μ F X Y ≫ F.map (fst X Y) = fst (F.obj X) (F.obj Y) :=
  (cancel_epi (μIso _ _ _).inv).1 (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_snd (X Y : C) : μ F X Y ≫ F.map (snd X Y) = snd (F.obj X) (F.obj Y) :=
  (cancel_epi (μIso _ _ _).inv).1 (by simp)

set_option backward.defeqAttrib.useBackward true in
attribute [-instance] Functor.LaxMonoidal.comp Functor.Monoidal.instComp in
@[reassoc]
/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_comp [(F ⋙ G).Monoidal] (X Y : C) : μ (F ⋙ G) X Y = μ G _ _ ≫ G.map (μ F X Y) := by
  rw [← cancel_mono (μIso _ _ _).inv]; ext <;> simp [← Functor.comp_obj, ← Functor.map_comp]

variable [PreservesFiniteProducts F]
/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ε_of_cartesianMonoidalCategory : ε F = (preservesTerminalIso F).inv := by
  change (εIso F).symm.inv = _; congr; ext
/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_of_cartesianMonoidalCategory (X Y : C) : μ F X Y = (prodComparisonIso F X Y).inv := by
  change (μIso F X Y).symm.inv = _; congr; ext : 1; simpa using δ_of_cartesianMonoidalCategory F X Y

attribute [local instance] Functor.OplaxMonoidal.ofChosenFiniteProducts in
omit [F.Monoidal] in
/-- A finite-product-preserving functor between Cartesian monoidal categories is monoidal.

This is not made an instance because it would create a diamond for the monoidal structure on
the identity and composition of functors. -/
@[instance_reducible]
/-
**CategoryTheory.Functor.Monoidal.ofChosenFiniteProducts** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Functor.Monoidal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       {D : Type u₂} →         
[inst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheo
ry.CartesianMonoidalCategory D] →             (F : CategoryTheory.Functor C D) →
 [CategoryTheory.Limits.PreservesFiniteProducts F] → F.Monoidal
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite-product-preserving functor between Cartesian monoidal categories is mon
oidal.

This is not made an instance because it would create a diamond for the monoidal 
structure on
the identity and composition of functors.
-/
noncomputable def ofChosenFiniteProducts (F : C ⥤ D) [PreservesFiniteProducts F] : F.Monoidal :=
  .ofOplaxMonoidal F
/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton F.Monoidal := (toOplaxMonoidal_injective F).subsingleton

end Monoidal

namespace Monoidal

/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
A functor between Cartesian monoidal categories is monoidal iff it preserves finite products.
-/
/-
**CategoryTheory.Functor.Monoidal.nonempty_monoidal_iff_preservesFiniteProducts*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.Monoidal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   {D : Type u₂} [inst_2 : CategoryTheory
.Category.{v₂, u₂} D] [inst_3 : CategoryTheory.CartesianMonoidalCategory D]   (F
 : CategoryTheory.Functor C D), Nonempty F.Monoidal ↔ CategoryTheory.Limits.Pres
ervesFiniteProducts F
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Monoidal.instPreservesFiniteProducts`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Cartes
ianMonoidalCategory C]   {D : Type u₂} [inst_2 : …

--- 原说明 ---
A functor between Cartesian monoidal categories is monoidal iff it preserves fin
ite products.
-/
lemma nonempty_monoidal_iff_preservesFiniteProducts :
    Nonempty F.Monoidal ↔ PreservesFiniteProducts F :=
  ⟨fun ⟨_⟩ ↦ inferInstance, fun _ ↦ ⟨ofChosenFiniteProducts F⟩⟩

end Monoidal

namespace Braided
variable [BraidedCategory C] [BraidedCategory D]

attribute [local instance] Functor.Monoidal.ofChosenFiniteProducts in
/-- A finite-product-preserving functor between Cartesian monoidal categories is braided.

This is not made an instance because it would create a diamond for the monoidal structure on
the identity and composition of functors. -/
@[instance_reducible]
/-
**CategoryTheory.Functor.Braided.ofChosenFiniteProducts** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Functor.Braided`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.CartesianMonoidalCategory C] →       {D : Type u₂} →         
[inst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheo
ry.CartesianMonoidalCategory D] →             [inst_4 : CategoryTheory.BraidedCa
tegory C] →               [inst_5 : CategoryTheory.BraidedCategory D] →         
        (F : CategoryTheory.Functor C D) → [CategoryTheory.Limits.PreservesFinit
eProducts F] → F.Braided
参数：F : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite-product-preserving functor between Cartesian monoidal categories is bra
ided.

This is not made an instance because it would create a diamond for the monoidal 
structure on
the identity and composition of functors.
-/
noncomputable def ofChosenFiniteProducts (F : C ⥤ D) [PreservesFiniteProducts F] : F.Braided where
  braided X Y := by rw [← cancel_mono (Monoidal.μIso _ _ _).inv]; ext <;> simp [← F.map_comp]
/-
**CategoryTheory.Functor.Braided.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Func
tor.Braided`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton F.Braided := (Braided.toMonoidal_injective F).subsingleton

end Braided

namespace EssImageSubcategory
variable [F.Full] [F.Faithful] [PreservesFiniteProducts F] {T X Y Z : F.EssImageSubcategory}

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.EssImageSubcategory.tensor_obj** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Functor.EssImageSubcategory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   {D : Type u₂} [inst_2 : CategoryTheory
.Category.{v₂, u₂} D] [inst_3 : CategoryTheory.CartesianMonoidalCategory D]   (F
 : CategoryTheory.Functor C D) [inst_4 : F.Full] [inst_5 : F.Faithful]   [inst_6
 : CategoryTheory.Limits.PreservesFiniteProducts F] (X Y : F.EssImageSubcategory
),   (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y).obj =     CategoryThe
ory.MonoidalCategoryStruct.tensorObj X.obj Y.obj
参数：F : CategoryTheory.Functor C D；X Y : F.EssImageSubcategory；CategoryTheory.Mon
oidalCategoryStruct.tensorObj X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instIsClosedUnderLimitsOfShapeEssImageOfHasLimitsO
fShapeOfPreservesLimitsOfShapeOfFullOfFaithful`：∀ {J : Type w} [inst : CategoryT
heory.Category.{w', w} J] {C : Type u₁} [inst_1 : CategoryTheory.Category.{v₁, u
₁} C]   {D : Type u₂} [inst_…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma tensor_obj (X Y : F.EssImageSubcategory) : (X ⊗ Y).obj = X.obj ⊗ Y.obj := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.EssImageSubcategory.lift_def** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Functor.EssImageSubcategory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   {D : Type u₂} [inst_2 : CategoryTheory
.Category.{v₂, u₂} D] [inst_3 : CategoryTheory.CartesianMonoidalCategory D]   (F
 : CategoryTheory.Functor C D) [inst_4 : F.Full] [inst_5 : F.Faithful]   [inst_6
 : CategoryTheory.Limits.PreservesFiniteProducts F] {T X Y : F.EssImageSubcatego
ry} (f : T ⟶ X) (g : T ⟶ Y),   CategoryTheory.CartesianMonoidalCategory.lift f g
 =     CategoryTheory.ObjectProperty.homMk (CategoryTheory.CartesianMonoidalCate
gory.lift f.hom g.hom)
参数：F : CategoryTheory.Functor C D；f : T ⟶ X；g : T ⟶ Y；CategoryTheory.CartesianMo
noidalCategory.lift f.hom g.hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instIsClosedUnderLimitsOfShapeEssImageOfHasLimitsO
fShapeOfPreservesLimitsOfShapeOfFullOfFaithful`：∀ {J : Type w} [inst : CategoryT
heory.Category.{w', w} J] {C : Type u₁} [inst_1 : CategoryTheory.Category.{v₁, u
₁} C]   {D : Type u₂} [inst_…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma lift_def (f : T ⟶ X) (g : T ⟶ Y) : lift f g = ObjectProperty.homMk (lift f.hom g.hom) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.EssImageSubcategory.associator_hom_def** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Functor.EssImageSubcategory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   {D : Type u₂} [inst_2 : CategoryTheory
.Category.{v₂, u₂} D] [inst_3 : CategoryTheory.CartesianMonoidalCategory D]   (F
 : CategoryTheory.Functor C D) [inst_4 : F.Full] [inst_5 : F.Faithful]   [inst_6
 : CategoryTheory.Limits.PreservesFiniteProducts F] (X Y Z : F.EssImageSubcatego
ry),   (CategoryTheory.MonoidalCategoryStruct.associator X Y Z).hom =     Catego
ryTheory.ObjectProperty.homMk (CategoryTheory.MonoidalCategoryStruct.associator 
X.obj Y.obj Z.obj).hom
参数：F : CategoryTheory.Functor C D；X Y Z : F.EssImageSubcategory；CategoryTheory.M
onoidalCategoryStruct.associator X Y Z；CategoryTheory.MonoidalCategoryStruct.ass
ociator X.obj Y.obj Z.obj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instIsClosedUnderLimitsOfShapeEssImageOfHasLimitsO
fShapeOfPreservesLimitsOfShapeOfFullOfFaithful`：∀ {J : Type w} [inst : CategoryT
heory.Category.{w', w} J] {C : Type u₁} [inst_1 : CategoryTheory.Category.{v₁, u
₁} C]   {D : Type u₂} [inst_…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma associator_hom_def (X Y Z : F.EssImageSubcategory) :
    (α_ X Y Z).hom = ObjectProperty.homMk (α_ X.obj Y.obj Z.obj).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.EssImageSubcategory.associator_inv_def** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Functor.EssImageSubcategory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   {D : Type u₂} [inst_2 : CategoryTheory
.Category.{v₂, u₂} D] [inst_3 : CategoryTheory.CartesianMonoidalCategory D]   (F
 : CategoryTheory.Functor C D) [inst_4 : F.Full] [inst_5 : F.Faithful]   [inst_6
 : CategoryTheory.Limits.PreservesFiniteProducts F] (X Y Z : F.EssImageSubcatego
ry),   (CategoryTheory.MonoidalCategoryStruct.associator X Y Z).inv =     Catego
ryTheory.ObjectProperty.homMk (CategoryTheory.MonoidalCategoryStruct.associator 
X.obj Y.obj Z.obj).inv
参数：F : CategoryTheory.Functor C D；X Y Z : F.EssImageSubcategory；CategoryTheory.M
onoidalCategoryStruct.associator X Y Z；CategoryTheory.MonoidalCategoryStruct.ass
ociator X.obj Y.obj Z.obj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instIsClosedUnderLimitsOfShapeEssImageOfHasLimitsO
fShapeOfPreservesLimitsOfShapeOfFullOfFaithful`：∀ {J : Type w} [inst : CategoryT
heory.Category.{w', w} J] {C : Type u₁} [inst_1 : CategoryTheory.Category.{v₁, u
₁} C]   {D : Type u₂} [inst_…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma associator_inv_def (X Y Z : F.EssImageSubcategory) :
    (α_ X Y Z).inv = ObjectProperty.homMk (α_ X.obj Y.obj Z.obj).inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.EssImageSubcategory.toUnit_def** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Functor.EssImageSubcategory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   {D : Type u₂} [inst_2 : CategoryTheory
.Category.{v₂, u₂} D] [inst_3 : CategoryTheory.CartesianMonoidalCategory D]   (F
 : CategoryTheory.Functor C D) [inst_4 : F.Full] [inst_5 : F.Faithful]   [inst_6
 : CategoryTheory.Limits.PreservesFiniteProducts F] (X : F.EssImageSubcategory),
   CategoryTheory.SemiCartesianMonoidalCategory.toUnit X =     CategoryTheory.Ob
jectProperty.homMk (CategoryTheory.SemiCartesianMonoidalCategory.toUnit X.obj)
参数：F : CategoryTheory.Functor C D；X : F.EssImageSubcategory；CategoryTheory.SemiC
artesianMonoidalCategory.toUnit X.obj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instIsClosedUnderLimitsOfShapeEssImageOfHasLimitsO
fShapeOfPreservesLimitsOfShapeOfFullOfFaithful`：∀ {J : Type w} [inst : CategoryT
heory.Category.{w', w} J] {C : Type u₁} [inst_1 : CategoryTheory.Category.{v₁, u
₁} C]   {D : Type u₂} [inst_…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma toUnit_def (X : F.EssImageSubcategory) :
    toUnit X = ObjectProperty.homMk (toUnit X.obj) := rfl

end Functor.EssImageSubcategory

namespace NatTrans
variable (F G : C ⥤ D) [F.Monoidal] [G.Monoidal]

/-
**CategoryTheory.NatTrans.IsMonoidal.of_cartesianMonoidalCategory** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.NatTrans.IsMonoidal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   {D : Type u₂} [inst_2 : CategoryTheory
.Category.{v₂, u₂} D] [inst_3 : CategoryTheory.CartesianMonoidalCategory D]   (F
 G : CategoryTheory.Functor C D) [inst_4 : F.Monoidal] [inst_5 : G.Monoidal] (α 
: F ⟶ G),   CategoryTheory.NatTrans.IsMonoidal α
参数：F G : CategoryTheory.Functor C D；α : F ⟶ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用引理 `CategoryTheory.SemiCartesianMonoidalCategory.toUnit_unique`：toUnit_uniqu
e {X : C} (f g : X ⟶ 𝟙_ _) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.hom_ext`：hom_ext {T X Y : C} (f
 g : T ⟶ X otimes Y) (h_fst : f ≫ fst _ _ = g ≫ fst _ _) (h_snd : f ≫ snd _ _ = 
g ≫ snd _ _) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.Monoidal.μIso_inv`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D : 
Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用引理 `CategoryTheory.Functor.OplaxMonoidal.δ_fst`：δ_fst (X Y : C) : δ F X Y ≫ 
fst _ _ = F.map (fst _ _)
· 使用定理 `CategoryTheory.Functor.Monoidal.μ_δ`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.tensorHom_fst`：tensorHom_fst {X
₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g) ≫ fst _ _ = fst _ _ 
≫ f
· 使用定理 `CategoryTheory.Functor.OplaxMonoidal.δ_fst_assoc`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.CartesianMonoidal
Category C]   {D : Type u₂} [inst_2 : …
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Functor.OplaxMonoidal.δ_snd`：δ_snd (X Y : C) : δ F X Y ≫ 
snd _ _ = F.map (snd _ _)
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.tensorHom_snd`：tensorHom_snd {X
₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g) ≫ snd _ _ = snd _ _ 
≫ g
· 使用定理 `CategoryTheory.Functor.OplaxMonoidal.δ_snd_assoc`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.CartesianMonoidal
Category C]   {D : Type u₂} [inst_2 : …
-/
instance IsMonoidal.of_cartesianMonoidalCategory (α : F ⟶ G) : IsMonoidal α where
  unit := (cancel_mono (Functor.Monoidal.εIso _).inv).1 (toUnit_unique _ _)
  tensor {X Y} := by
    rw [← cancel_mono (Functor.Monoidal.μIso _ _ _).inv]
    rw [← cancel_epi (Functor.Monoidal.μIso _ _ _).inv]
    apply CartesianMonoidalCategory.hom_ext <;> simp

end NatTrans

end CategoryTheory

