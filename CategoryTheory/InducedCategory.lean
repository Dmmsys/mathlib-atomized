/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Induced categories and full subcategories

Given a category `D` and a function `F : C → D` from a type `C` to the
objects of `D`, there is an essentially unique way to give `C` a
category structure such that `F` becomes a fully faithful functor,
namely by taking $ Hom_C(X, Y) = Hom_D(FX, FY) $. We call this the
category induced from `D` along `F`.

## Implementation notes

The type of morphisms between `X` and `Y` in `InducedCategory D F` is
not definitionally equal to `F X ⟶ F Y`. Instead, this type is made
a `1`-field structure. Use `InducedCategory.homMk` to construct
morphisms in induced categories.

-/

@[expose] public section


namespace CategoryTheory

universe v v₂ u₁ u₂
-- morphism levels before object levels. See note [category theory universes].

section Induced

variable {C : Type u₁} (D : Type u₂) [Category.{v} D]
variable (F : C → D)

/-- `InducedCategory D F`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y`.
-/
@[nolint unusedArguments, implicit_reducible]
/-
**CategoryTheory.InducedCategory** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：InducedCategory (_F : C -> D) : Type u₁
参数：_F : C -> D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`InducedCategory D F`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphi
sms
in `D` from `F X` to `F Y`.
-/
def InducedCategory (_F : C → D) : Type u₁ :=
  C

variable {D}

namespace InducedCategory

/-
**CategoryTheory.InducedCategory.hasCoeToSort** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.InducedCategory`。
形式化陈述：hasCoeToSort {α : Sort*} [CoeSort D α] : CoeSort (InducedCategory D F) α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeToSort {α : Sort*} [CoeSort D α] :
    CoeSort (InducedCategory D F) α :=
  ⟨fun c => F c⟩

variable {F}

/-- The type of morphisms in `InducedCategory D F` between `X` and `Y`
is a 1-field structure which identifies to `F X ⟶ F Y`. -/
@[ext]
/-
**CategoryTheory.InducedCategory.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory
.InducedCategory`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [CategoryTheory.Category.{v, u₂} D] 
→       {F : C → D} → CategoryTheory.InducedCategory D F → CategoryTheory.Induce
dCategory D F → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `InducedCategory D F` between `X` and `Y`
is a 1-field structure which identifies to `F X ⟶ F Y`.
-/
structure Hom (X Y : InducedCategory D F) where
  /-- The underlying morphism. -/
  hom : F X ⟶ F Y

@[simps id_hom comp_hom]
/-
**CategoryTheory.InducedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Indu
cedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category.{v} (InducedCategory D F) where
  Hom X Y := Hom X Y
  id X := { hom := 𝟙 _ }
  comp f g := { hom := f.hom ≫ g.hom }

attribute [reassoc] comp_hom

@[ext]
/-
**CategoryTheory.InducedCategory.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.InducedCategory`。
形式化陈述：hom_ext {X Y : InducedCategory D F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f 
= g
参数：h : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.InducedCategory.Hom.ext`：∀ {C : Type u₁} {D : Type u₂} {i
nst : CategoryTheory.Category.{v, u₂} D} {F : C → D}   {X Y : CategoryTheory.Ind
ucedCategory D F} {x y : X.H…
-/
lemma hom_ext {X Y : InducedCategory D F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-- Construct a morphism in the induced category
from a morphism in the original category. -/
/-
**CategoryTheory.InducedCategory.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.InducedCategory`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v, 
u₂} D] →       {F : C → D} → {X Y : CategoryTheory.InducedCategory D F} → (F X ⟶
 F Y) → (X ⟶ Y)
参数：F X ⟶ F Y；X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism in the induced category
from a morphism in the original category.
-/
@[simps] def homMk {X Y : InducedCategory D F} (f : F X ⟶ F Y) : X ⟶ Y where
  hom := f

/-- Morphisms in `InducedCategory D F` identify to morphisms in `D`. -/
@[simps!]
/-
**CategoryTheory.InducedCategory.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.InducedCategory`。
形式化陈述：homEquiv {X Y : InducedCategory D F} : (X ⟶ Y) ≃ (F X ⟶ F Y) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms in `InducedCategory D F` identify to morphisms in `D`.
-/
def homEquiv {X Y : InducedCategory D F} : (X ⟶ Y) ≃ (F X ⟶ F Y) where
  toFun f := f.hom
  invFun f := homMk f

/-- Construct an isomorphism in the induced category
from an isomorphism in the original category. -/
/-
**CategoryTheory.InducedCategory.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.InducedCategory`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v, 
u₂} D] →       {F : C → D} → {X Y : CategoryTheory.InducedCategory D F} → (F X ≅
 F Y) → (X ≅ Y)
参数：F X ≅ F Y；X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism in the induced category
from an isomorphism in the original category.
-/
@[simps] def isoMk {X Y : InducedCategory D F} (f : F X ≅ F Y) : X ≅ Y where
  hom := homMk f.hom
  inv := homMk f.inv

end InducedCategory

/-- The forgetful functor from an induced category to the original category,
forgetting the extra data.
-/
@[simps, implicit_reducible]
/-
**CategoryTheory.inducedFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：inducedFunctor : InducedCategory D F ⥤ D where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from an induced category to the original category,
forgetting the extra data.
-/
def inducedFunctor : InducedCategory D F ⥤ D where
  obj := F
  map f := f.hom

/-- The induced functor `inducedFunctor F : InducedCategory D F ⥤ D` is fully faithful. -/
/-
**CategoryTheory.fullyFaithfulInducedFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory`。
形式化陈述：fullyFaithfulInducedFunctor : (inducedFunctor F).FullyFaithful where preim
age f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced functor `inducedFunctor F : InducedCategory D F ⥤ D` is fully faithf
ul.
-/
def fullyFaithfulInducedFunctor : (inducedFunctor F).FullyFaithful where
  preimage f := InducedCategory.homMk f
/-
**CategoryTheory.InducedCategory.full** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
InducedCategory`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v, u₂} D] (
F : C → D),   (CategoryTheory.inducedFunctor F).Full
参数：F : C → D；CategoryTheory.inducedFunctor F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
-/
instance InducedCategory.full : (inducedFunctor F).Full :=
  (fullyFaithfulInducedFunctor F).full
/-
**CategoryTheory.InducedCategory.faithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.InducedCategory`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v, u₂} D] (
F : C → D),   (CategoryTheory.inducedFunctor F).Faithful
参数：F : C → D；CategoryTheory.inducedFunctor F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.faithful`：faithful : F.Faithful whe
re map_injective
-/
instance InducedCategory.faithful : (inducedFunctor F).Faithful :=
  (fullyFaithfulInducedFunctor F).faithful

end Induced

end CategoryTheory

