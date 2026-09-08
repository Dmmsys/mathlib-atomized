/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# The category of types is a (symmetric) monoidal category
-/

@[expose] public section


open CategoryTheory Limits MonoidalCategory

universe v u

namespace CategoryTheory

/-
**CategoryTheory.typesCartesianMonoidalCategory** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory`。
形式化陈述：typesCartesianMonoidalCategory : CartesianMonoidalCategory (Type u) where 
tensorObj X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance typesCartesianMonoidalCategory : CartesianMonoidalCategory (Type u) where
  tensorObj X Y := X × Y
  tensorUnit := PUnit
  __ := CartesianMonoidalCategory.ofChosenFiniteProducts
    Types.terminalLimitCone Types.binaryProductLimitCone
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BraidedCategory (Type u) := .ofCartesianMonoidalCategory
/-
**CategoryTheory.types_tensorObj_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：types_tensorObj_def {X Y : Type u} : X otimes Y = (X × Y)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem types_tensorObj_def {X Y : Type u} : X ⊗ Y = (X × Y) := rfl
/-
**CategoryTheory.types_tensorUnit_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：types_tensorUnit_def : 𝟙_ (Type u) = PUnit
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem types_tensorUnit_def : 𝟙_ (Type u) = PUnit := rfl

attribute [local simp] types_tensorObj_def types_tensorUnit_def

@[simp]
/-
**CategoryTheory.tensor_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：tensor_apply {W X Y Z : Type u} (f : W ⟶ X) (g : Y ⟶ Z) (p : W otimes Y) :
 dsimp% (f otimesₘ g) p = (f p.1, g p.2)
参数：f : W ⟶ X；g : Y ⟶ Z；p : W otimes Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensor_apply {W X Y Z : Type u} (f : W ⟶ X) (g : Y ⟶ Z) (p : W ⊗ Y) :
    dsimp% (f ⊗ₘ g) p = (f p.1, g p.2) :=
  rfl

@[simp]
/-
**CategoryTheory.whiskerLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：whiskerLeft_apply (X : Type u) {Y Z : Type u} (f : Y ⟶ Z) (p : X otimes Y)
 : dsimp% (X ◁ f) p = (p.1, f p.2)
参数：X : Type u；f : Y ⟶ Z；p : X otimes Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerLeft_apply (X : Type u) {Y Z : Type u} (f : Y ⟶ Z) (p : X ⊗ Y) :
    dsimp% (X ◁ f) p = (p.1, f p.2) :=
  rfl

@[simp]
/-
**CategoryTheory.whiskerRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：whiskerRight_apply {Y Z : Type u} (f : Y ⟶ Z) (X : Type u) (p : Y otimes X
) : dsimp% (f ▷ X) p = (f p.1, p.2)
参数：f : Y ⟶ Z；X : Type u；p : Y otimes X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerRight_apply {Y Z : Type u} (f : Y ⟶ Z) (X : Type u) (p : Y ⊗ X) :
    dsimp% (f ▷ X) p = (f p.1, p.2) :=
  rfl

@[simp]
/-
**CategoryTheory.leftUnitor_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：leftUnitor_hom_apply {X : Type u} {x : X} {p : PUnit} : dsimp% (fun_ X).ho
m (p, x) = x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftUnitor_hom_apply {X : Type u} {x : X} {p : PUnit} :
    dsimp% (λ_ X).hom (p, x) = x :=
  rfl

@[simp]
/-
**CategoryTheory.leftUnitor_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：leftUnitor_inv_apply {X : Type u} {x : X} : dsimp% (fun_ X).inv x = (PUnit
.unit, x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftUnitor_inv_apply {X : Type u} {x : X} :
    dsimp% (λ_ X).inv x = (PUnit.unit, x) :=
  rfl

@[simp]
/-
**CategoryTheory.rightUnitor_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：rightUnitor_hom_apply {X : Type u} {x : X} {p : PUnit} : dsimp% (ρ_ X).hom
 (x, p) = x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightUnitor_hom_apply {X : Type u} {x : X} {p : PUnit} :
    dsimp% (ρ_ X).hom (x, p) = x :=
  rfl

@[simp]
/-
**CategoryTheory.rightUnitor_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：rightUnitor_inv_apply {X : Type u} {x : X} : dsimp% (ρ_ X).inv x = (x, PUn
it.unit)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightUnitor_inv_apply {X : Type u} {x : X} :
    dsimp% (ρ_ X).inv x = (x, PUnit.unit) :=
  rfl

@[simp]
/-
**CategoryTheory.associator_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：associator_hom_apply {X Y Z : Type u} {x : X} {y : Y} {z : Z} : dsimp% (α_
 X Y Z).hom ((x, y), z) = (x, (y, z))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_hom_apply {X Y Z : Type u} {x : X} {y : Y} {z : Z} :
    dsimp% (α_ X Y Z).hom ((x, y), z) = (x, (y, z)) :=
  rfl

@[simp]
/-
**CategoryTheory.associator_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：associator_inv_apply {X Y Z : Type u} {x : X} {y : Y} {z : Z} : dsimp% (α_
 X Y Z).inv (x, (y, z)) = ((x, y), z)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem associator_inv_apply {X Y Z : Type u} {x : X} {y : Y} {z : Z} :
    dsimp% (α_ X Y Z).inv (x, (y, z)) = ((x, y), z) :=
  rfl
/-
**CategoryTheory.associator_hom_apply_1** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：∀ {X Y Z : Type u}   {x :     (fun X => X)       (CategoryTheory.MonoidalC
ategoryStruct.tensorObj (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) Z)
},   ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.MonoidalCategoryStruc
t.associator X Y Z).hom) x).1 = x.1.1
参数：fun X => X；CategoryTheory.MonoidalCategoryStruct.tensorObj (CategoryTheory.Mo
noidalCategoryStruct.tensorObj X Y) Z；(CategoryTheory.ConcreteCategory.hom (Cate
goryTheory.MonoidalCategoryStruct.associator X Y Z).hom) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem associator_hom_apply_1 {X Y Z : Type u} {x} :
    dsimp% ((α_ X Y Z).hom x).1 = x.1.1 :=
  rfl
/-
**CategoryTheory.associator_hom_apply_2_1** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：∀ {X Y Z : Type u}   {x :     (fun X => X)       (CategoryTheory.MonoidalC
ategoryStruct.tensorObj (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) Z)
},   ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.MonoidalCategoryStruc
t.associator X Y Z).hom) x).2.1 = x.1.2
参数：fun X => X；CategoryTheory.MonoidalCategoryStruct.tensorObj (CategoryTheory.Mo
noidalCategoryStruct.tensorObj X Y) Z；(CategoryTheory.ConcreteCategory.hom (Cate
goryTheory.MonoidalCategoryStruct.associator X Y Z).hom) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem associator_hom_apply_2_1 {X Y Z : Type u} {x} :
    dsimp% ((α_ X Y Z).hom x).2.1 = x.1.2 :=
  rfl
/-
**CategoryTheory.associator_hom_apply_2_2** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：∀ {X Y Z : Type u}   {x :     (fun X => X)       (CategoryTheory.MonoidalC
ategoryStruct.tensorObj (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) Z)
},   ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.MonoidalCategoryStruc
t.associator X Y Z).hom) x).2.2 = x.2
参数：fun X => X；CategoryTheory.MonoidalCategoryStruct.tensorObj (CategoryTheory.Mo
noidalCategoryStruct.tensorObj X Y) Z；(CategoryTheory.ConcreteCategory.hom (Cate
goryTheory.MonoidalCategoryStruct.associator X Y Z).hom) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem associator_hom_apply_2_2 {X Y Z : Type u} {x} :
    dsimp% ((α_ X Y Z).hom x).2.2 = x.2 :=
  rfl
/-
**CategoryTheory.associator_inv_apply_1_1** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：∀ {X Y Z : Type u}   {x :     (fun X => X)       (CategoryTheory.MonoidalC
ategoryStruct.tensorObj X (CategoryTheory.MonoidalCategoryStruct.tensorObj Y Z))
},   ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.MonoidalCategoryStruc
t.associator X Y Z).inv) x).1.1 = x.1
参数：fun X => X；CategoryTheory.MonoidalCategoryStruct.tensorObj X (CategoryTheory.
MonoidalCategoryStruct.tensorObj Y Z)；(CategoryTheory.ConcreteCategory.hom (Cate
goryTheory.MonoidalCategoryStruct.associator X Y Z).inv) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem associator_inv_apply_1_1 {X Y Z : Type u} {x} :
    dsimp% ((α_ X Y Z).inv x).1.1 = x.1 :=
  rfl
/-
**CategoryTheory.associator_inv_apply_1_2** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory`。
形式化陈述：∀ {X Y Z : Type u}   {x :     (fun X => X)       (CategoryTheory.MonoidalC
ategoryStruct.tensorObj X (CategoryTheory.MonoidalCategoryStruct.tensorObj Y Z))
},   ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.MonoidalCategoryStruc
t.associator X Y Z).inv) x).1.2 = x.2.1
参数：fun X => X；CategoryTheory.MonoidalCategoryStruct.tensorObj X (CategoryTheory.
MonoidalCategoryStruct.tensorObj Y Z)；(CategoryTheory.ConcreteCategory.hom (Cate
goryTheory.MonoidalCategoryStruct.associator X Y Z).inv) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem associator_inv_apply_1_2 {X Y Z : Type u} {x} :
    dsimp% ((α_ X Y Z).inv x).1.2 = x.2.1 :=
  rfl
/-
**CategoryTheory.associator_inv_apply_2** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：∀ {X Y Z : Type u}   {x :     (fun X => X)       (CategoryTheory.MonoidalC
ategoryStruct.tensorObj X (CategoryTheory.MonoidalCategoryStruct.tensorObj Y Z))
},   ((CategoryTheory.ConcreteCategory.hom (CategoryTheory.MonoidalCategoryStruc
t.associator X Y Z).inv) x).2 = x.2.2
参数：fun X => X；CategoryTheory.MonoidalCategoryStruct.tensorObj X (CategoryTheory.
MonoidalCategoryStruct.tensorObj Y Z)；(CategoryTheory.ConcreteCategory.hom (Cate
goryTheory.MonoidalCategoryStruct.associator X Y Z).inv) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem associator_inv_apply_2 {X Y Z : Type u} {x} :
    dsimp% ((α_ X Y Z).inv x).2 = x.2.2 :=
  rfl

@[simp]
/-
**CategoryTheory.braiding_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：braiding_hom_apply {X Y : Type u} {x : X} {y : Y} : dsimp% (β_ X Y).hom (x
, y) = (y, x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem braiding_hom_apply {X Y : Type u} {x : X} {y : Y} :
    dsimp% (β_ X Y).hom (x, y) = (y, x) :=
  rfl

@[simp]
/-
**CategoryTheory.braiding_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：braiding_inv_apply {X Y : Type u} {x : X} {y : Y} : dsimp% (β_ X Y).inv (y
, x) = (x, y)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem braiding_inv_apply {X Y : Type u} {x : X} {y : Y} :
    dsimp% (β_ X Y).inv (y, x) = (x, y) :=
  rfl

@[simp]
/-
**CategoryTheory.CartesianMonoidalCategory.lift_apply** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.CartesianMonoidalCategory`。
形式化陈述：∀ {X Y Z : Type u} {f : X ⟶ Y} {g : X ⟶ Z} {x : X},   (CategoryTheory.Conc
reteCategory.hom (CategoryTheory.CartesianMonoidalCategory.lift f g)) x =     ((
CategoryTheory.ConcreteCategory.hom f) x, (CategoryTheory.ConcreteCategory.hom g
) x)
参数：CategoryTheory.ConcreteCategory.hom (CategoryTheory.CartesianMonoidalCategory
.lift f g)；(CategoryTheory.ConcreteCategory.hom f) x, (CategoryTheory.ConcreteCa
tegory.hom g) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem CartesianMonoidalCategory.lift_apply {X Y Z : Type u} {f : X ⟶ Y} {g : X ⟶ Z} {x : X} :
    dsimp% lift f g x = (f x, g x) :=
  rfl

-- We don't yet have an API for tensor products indexed by finite ordered types,
-- but it would be nice to state how monoidal functors preserve these.
/-- If `F` is a monoidal functor out of `Type`, it takes the (n+1)st Cartesian power
of a type to the image of that type, tensored with the image of the nth Cartesian power. -/
/-
**CategoryTheory.MonoidalFunctor.mapPi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.MonoidalFunctor`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.MonoidalCategory C] →       (F : CategoryTheory.Functor (T
ype u_2) C) →         [F.Monoidal] →           (n : ℕ) →             (β : Type u
_2) →               F.obj (Fin (n + 1) → β) ≅ CategoryTheory.MonoidalCategoryStr
uct.tensorObj (F.obj β) (F.obj (Fin n → β))
参数：F : CategoryTheory.Functor (Type u_2) C；n : ℕ；β : Type u_2；Fin (n + 1) → β；F.
obj β；F.obj (Fin n → β)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `F` is a monoidal functor out of `Type`, it takes the (n+1)st Cartesian power
of a type to the image of that type, tensored with the image of the nth Cartesia
n power.
-/
noncomputable def MonoidalFunctor.mapPi {C : Type*} [Category* C] [MonoidalCategory C]
    (F : Type _ ⥤ C) [F.Monoidal] (n : ℕ) (β : Type*) :
    F.obj (Fin (n + 1) → β) ≅ F.obj β ⊗ F.obj (Fin n → β) :=
  Functor.mapIso _ (Fin.consEquiv _).symm.toIso ≪≫ (Functor.Monoidal.μIso F β (Fin n → β)).symm

end CategoryTheory

