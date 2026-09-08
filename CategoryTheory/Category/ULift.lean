/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Data.ULift

/-!
# Basic API for ULift

This file contains a very basic API for working with the categorical
instance on `ULift C` where `C` is a type with a category instance.

1. `CategoryTheory.ULift.upFunctor` is the functorial version of the usual `ULift.up`.
2. `CategoryTheory.ULift.downFunctor` is the functorial version of the usual `ULift.down`.
3. `CategoryTheory.ULift.equivalence` is the categorical equivalence between
  `C` and `ULift C`.

## ULiftHom

Given a type `C : Type u`, `ULiftHom.{w} C` is just an alias for `C`.
If we have `Category.{v} C`, then `ULiftHom.{w} C` is endowed with a category instance
whose morphisms are obtained by applying `ULift.{w}` to the morphisms from `C`.

This is a category equivalent to `C`. The forward direction of the equivalence is `ULiftHom.up`,
the backward direction is `ULiftHom.down` and the equivalence is `ULiftHom.equiv`.

## AsSmall

This file also contains a construction which takes a type `C : Type u` with a
category instance `Category.{v} C` and makes a small category
`AsSmall.{w} C : Type (max w v u)` equivalent to `C`.

The forward direction of the equivalence, `C ⥤ AsSmall C`, is denoted `AsSmall.up`
and the backward direction is `AsSmall.down`. The equivalence itself is `AsSmall.equiv`.
-/

@[expose] public section

universe w₁ v₁ v₂ u₁ u₂

namespace CategoryTheory

attribute [local instance] uliftCategory

variable {C : Type u₁} [Category.{v₁} C]

/-- The functorial version of `ULift.up`. -/
@[simps]
/-
**CategoryTheory.ULift.upFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ULift
`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → CategoryTheo
ry.Functor C (ULift.{u₂, u₁} C)
参数：ULift.{u₂, u₁} C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functorial version of `ULift.up`.
-/
def ULift.upFunctor : C ⥤ ULift.{u₂} C where
  obj := ULift.up
  map f := f

/-- The functorial version of `ULift.down`. -/
@[simps]
/-
**CategoryTheory.ULift.downFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ULi
ft`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → CategoryTheo
ry.Functor (ULift.{u₂, u₁} C) C
参数：ULift.{u₂, u₁} C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functorial version of `ULift.down`.
-/
def ULift.downFunctor : ULift.{u₂} C ⥤ C where
  obj := ULift.down
  map f := f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The categorical equivalence between `C` and `ULift C`. -/
@[simps]
/-
**CategoryTheory.ULift.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ULi
ft`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → C ≌ ULift.{u
₂, u₁} C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical equivalence between `C` and `ULift C`.
-/
def ULift.equivalence : C ≌ ULift.{u₂} C where
  functor := ULift.upFunctor
  inverse := ULift.downFunctor
  unitIso :=
    { hom := 𝟙 _
      inv := 𝟙 _ }
  counitIso :=
    { hom := { app := fun _ => 𝟙 _ }
      inv := { app := fun _ => 𝟙 _ } }

section ULiftHom

/-- `ULiftHom.{w} C` is an alias for `C`, which is endowed with a category instance
  whose morphisms are obtained by applying `ULift.{w}` to the morphisms from `C`.
-/
/-
**CategoryTheory.ULiftHom.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ULiftHom.{w} C` is an alias for `C`, which is endowed with a category instance
  whose morphisms are obtained by applying `ULift.{w}` to the morphisms from `C`
.
-/
def ULiftHom.{w, u} (C : Type u) : Type u :=
  let _ := ULift.{w} C
  C
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C} [Inhabited C] : Inhabited (ULiftHom C) :=
  ⟨(default : C)⟩

/-- The obvious function `ULiftHom C → C`. -/
/-
**CategoryTheory.ULiftHom.objDown** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ULif
tHom`。
形式化陈述：{C : Type u_1} → CategoryTheory.ULiftHom C → C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious function `ULiftHom C → C`.
-/
def ULiftHom.objDown {C} (A : ULiftHom C) : C :=
  A

/-- The obvious function `C → ULiftHom C`. -/
/-
**CategoryTheory.ULiftHom.objUp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ULiftH
om`。
形式化陈述：{C : Type u_1} → C → CategoryTheory.ULiftHom C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious function `C → ULiftHom C`.
-/
def ULiftHom.objUp {C} (A : C) : ULiftHom C :=
  A

/-- The type-level equivalence between `C` and `ULiftHom C`. -/
/-
**CategoryTheory.ULiftHom.objEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ULi
ftHom`。
形式化陈述：{C : Type u_1} → C ≃ CategoryTheory.ULiftHom C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type-level equivalence between `C` and `ULiftHom C`.
-/
def ULiftHom.objEquiv {C} : C ≃ ULiftHom C where
  toFun := ULiftHom.objUp
  invFun := ULiftHom.objDown

@[simp]
/-
**CategoryTheory.objDown_objUp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：objDown_objUp {C} (A : C) : (ULiftHom.objUp A).objDown = A
参数：A : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem objDown_objUp {C} (A : C) : (ULiftHom.objUp A).objDown = A :=
  rfl

@[simp]
/-
**CategoryTheory.objUp_objDown** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：objUp_objDown {C} (A : ULiftHom C) : ULiftHom.objUp A.objDown = A
参数：A : ULiftHom C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem objUp_objDown {C} (A : ULiftHom C) : ULiftHom.objUp A.objDown = A :=
  rfl
/-
**CategoryTheory.ULiftHom.category** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ULi
ftHom`。
形式化陈述：{C : Type u₁} →   [CategoryTheory.Category.{v₁, u₁} C] → CategoryTheory.Ca
tegory.{max v₂ v₁, u₁} (CategoryTheory.ULiftHom C)
参数：CategoryTheory.ULiftHom C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ULiftHom.category : Category.{max v₂ v₁} (ULiftHom.{v₂} C) where
  Hom A B := ULift.{v₂} <| A.objDown ⟶ B.objDown
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.down ≫ g.down⟩

/-- One half of the equivalence between `C` and `ULiftHom C`. -/
@[simps]
/-
**CategoryTheory.ULiftHom.up** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ULiftHom`
。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → CategoryTheo
ry.Functor C (CategoryTheory.ULiftHom C)
参数：CategoryTheory.ULiftHom C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One half of the equivalence between `C` and `ULiftHom C`.
-/
def ULiftHom.up : C ⥤ ULiftHom C where
  obj := ULiftHom.objUp
  map f := ⟨f⟩

/-- One half of the equivalence between `C` and `ULiftHom C`. -/
@[simps]
/-
**CategoryTheory.ULiftHom.down** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ULiftHo
m`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → CategoryTheo
ry.Functor (CategoryTheory.ULiftHom C) C
参数：CategoryTheory.ULiftHom C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One half of the equivalence between `C` and `ULiftHom C`.
-/
def ULiftHom.down : ULiftHom C ⥤ C where
  obj := ULiftHom.objDown
  map f := f.down

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence between `C` and `ULiftHom C`. -/
/-
**CategoryTheory.ULiftHom.equiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ULiftH
om`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → C ≌ Category
Theory.ULiftHom C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `C` and `ULiftHom C`.
-/
def ULiftHom.equiv : C ≌ ULiftHom C where
  functor := ULiftHom.up
  inverse := ULiftHom.down
  unitIso := NatIso.ofComponents fun _ => eqToIso rfl
  counitIso := NatIso.ofComponents fun _ => eqToIso rfl

end ULiftHom

/-- `AsSmall C` is a small category equivalent to `C`.
  More specifically, if `C : Type u` is endowed with `Category.{v} C`, then
  `AsSmall.{w} C : Type (max w v u)` is endowed with an instance of a small category.

  The objects and morphisms of `AsSmall C` are defined by applying `ULift` to the
  objects and morphisms of `C`.

  Note: We require a category instance for this definition in order to have direct
  access to the universe level `v`.
-/
@[nolint unusedArguments]
/-
**CategoryTheory.AsSmall.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AsSmall C` is a small category equivalent to `C`.
  More specifically, if `C : Type u` is endowed with `Category.{v} C`, then
  `AsSmall.{w} C : Type (max w v u)` is endowed with an instance of a small cate
gory.

  The objects and morphisms of `AsSmall C` are defined by applying `ULift` to th
e
  objects and morphisms of `C`.

  Note: We require a category instance for this definition in order to have dire
ct
  access to the universe level `v`.
-/
def AsSmall.{w, v, u} (D : Type u) [Category.{v} D] := ULift.{max w v} D
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SmallCategory (AsSmall.{w₁} C) where
  Hom X Y := ULift.{max w₁ u₁} <| X.down ⟶ Y.down
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.down ≫ g.down⟩

/-- One half of the equivalence between `C` and `AsSmall C`. -/
@[simps]
/-
**CategoryTheory.AsSmall.up** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.AsSmall`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → CategoryTheo
ry.Functor C (CategoryTheory.AsSmall C)
参数：CategoryTheory.AsSmall C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One half of the equivalence between `C` and `AsSmall C`.
-/
def AsSmall.up : C ⥤ AsSmall C where
  obj X := ⟨X⟩
  map f := ⟨f⟩

/-- One half of the equivalence between `C` and `AsSmall C`. -/
@[simps]
/-
**CategoryTheory.AsSmall.down** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.AsSmall`
。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → CategoryTheo
ry.Functor (CategoryTheory.AsSmall C) C
参数：CategoryTheory.AsSmall C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One half of the equivalence between `C` and `AsSmall C`.
-/
def AsSmall.down : AsSmall C ⥤ C where
  obj X := ULift.down X
  map f := f.down

@[reassoc]
/-
**CategoryTheory.down_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：down_comp {X Y Z : AsSmall C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).down = f.d
own ≫ g.down
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem down_comp {X Y Z : AsSmall C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).down = f.down ≫ g.down :=
  rfl

@[simp]
/-
**CategoryTheory.eqToHom_down** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：eqToHom_down {X Y : AsSmall C} (h : X = Y) : (eqToHom h).down = eqToHom (c
ongrArg ULift.down h)
参数：h : X = Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem eqToHom_down {X Y : AsSmall C} (h : X = Y) :
    (eqToHom h).down = eqToHom (congrArg ULift.down h) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence between `C` and `AsSmall C`. -/
@[simps]
/-
**CategoryTheory.AsSmall.equiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.AsSmall
`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → C ≌ Category
Theory.AsSmall C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `C` and `AsSmall C`.
-/
def AsSmall.equiv : C ≌ AsSmall C where
  functor := AsSmall.up
  inverse := AsSmall.down
  unitIso := NatIso.ofComponents fun _ => eqToIso rfl
  counitIso := NatIso.ofComponents fun _ => eqToIso <| ULift.ext _ _ rfl
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited C] : Inhabited (AsSmall C) :=
  ⟨⟨default⟩⟩

/-- The type-level equivalence between `C` and `ULiftHom (ULift C)`. -/
/-
**CategoryTheory.ULiftHomULiftCategory.objEquiv.** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type-level equivalence between `C` and `ULiftHom (ULift C)`.
-/
def ULiftHomULiftCategory.objEquiv.{v', u', u} {C : Type u} :
    C ≃ ULiftHom.{v'} (ULift.{u'} C) :=
  Equiv.ulift.symm.trans ULiftHom.objEquiv

/-- The equivalence between `C` and `ULiftHom (ULift C)`. -/
/-
**CategoryTheory.ULiftHomULiftCategory.equiv.** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `C` and `ULiftHom (ULift C)`.
-/
def ULiftHomULiftCategory.equiv.{v', u', v, u} (C : Type u) [Category.{v} C] :
    C ≌ ULiftHom.{v'} (ULift.{u'} C) :=
  ULift.equivalence.trans ULiftHom.equiv

/-- A type-level equivalence `(C ⥤ D) ≃ (C ⥤ (ULiftHom.{v'} (ULift.{u'} D)))`. Note that this is
not ensured by a categorical equivalence, and so needs special treatment. -/
/-
**CategoryTheory.ULiftHomULiftCategory.equivCongrLeft.** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type-level equivalence `(C ⥤ D) ≃ (C ⥤ (ULiftHom.{v'} (ULift.{u'} D)))`. Note 
that this is
not ensured by a categorical equivalence, and so needs special treatment.
-/
def ULiftHomULiftCategory.equivCongrLeft.{v', u'}
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] :
    (C ⥤ D) ≃ (C ⥤ (ULiftHom.{v'} (ULift.{u'} D))) where
  toFun F := F ⋙ ULift.upFunctor ⋙ ULiftHom.up
  invFun F := F ⋙ ULiftHom.down ⋙ ULift.downFunctor

end CategoryTheory

