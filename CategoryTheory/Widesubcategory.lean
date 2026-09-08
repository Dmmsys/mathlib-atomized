/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Wide subcategories

A wide subcategory of a category `C` is a subcategory containing all the objects of `C`.

## Main declarations

Given a category `D`, a function `F : C → D` from a type `C` to the objects of `D`,
and a morphism property `P` on `D` which contains identities and is stable under
composition, the type class `InducedWideCategory D F P` is a typeclass
synonym for `C` which comes equipped with a category structure whose morphisms `X ⟶ Y` are the
morphisms in `D` which have the property `P`.

The instance `WideSubcategory.category` provides a category structure on `WideSubcategory P`
whose objects are the objects of `C` and morphisms are the morphisms in `C` which have the
property `P`.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

open MorphismProperty

section Induced

variable {C : Type u₁} (D : Type u₂) [Category.{v₁} D]
variable (F : C → D) (P : MorphismProperty D) [P.IsMultiplicative]

/-- `InducedWideCategory D F P`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y` which satisfy a property `P : MorphismProperty D` that is multiplicative.
-/
@[nolint unusedArguments]
/-
**CategoryTheory.InducedWideCategory** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：InducedWideCategory (_F : C -> D) (_P : MorphismProperty D) [IsMultiplicat
ive _P]
参数：_F : C -> D；_P : MorphismProperty D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`InducedWideCategory D F P`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphi
sms
in `D` from `F X` to `F Y` which satisfy a property `P : MorphismProperty D` tha
t is multiplicative.
-/
def InducedWideCategory (_F : C → D) (_P : MorphismProperty D) [IsMultiplicative _P] :=
  C

variable {D}
/-
**CategoryTheory.InducedWideCategory.hasCoeToSort** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.InducedWideCategory`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₂} D] →       (F : C → D) →         (P : CategoryTheory.MorphismProperty D) → 
          [inst_1 : P.IsMultiplicative] →             {α : Sort u_1} → [CoeSort 
D α] → CoeSort (CategoryTheory.InducedWideCategory D F P) α
参数：F : C → D；P : CategoryTheory.MorphismProperty D；CategoryTheory.InducedWideCat
egory D F P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance InducedWideCategory.hasCoeToSort {α : Sort*} [CoeSort D α] :
    CoeSort (InducedWideCategory D F P) α :=
  ⟨fun c => F c⟩

variable {F P} in
/-- The type of morphisms in `InducedWideCategory D F P` between `X` and `Y`
is a 2-field structure consisting of a morphism `F X ⟶ F Y` in `D` that satisfies
the property `P`. -/
@[ext]
/-
**CategoryTheory.InducedWideCategory.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.InducedWideCategory`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₂} D] →       {F : C → D} →         {P : CategoryTheory.MorphismProperty D} → 
          [inst_1 : P.IsMultiplicative] →             CategoryTheory.InducedWide
Category D F P → CategoryTheory.InducedWideCategory D F P → Type v₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `InducedWideCategory D F P` between `X` and `Y`
is a 2-field structure consisting of a morphism `F X ⟶ F Y` in `D` that satisfie
s
the property `P`.
-/
structure InducedWideCategory.Hom (X Y : InducedWideCategory D F P) where
  /-- The underlying morphism. -/
  hom : F X ⟶ F Y
  /-- The property that the morphism satisfies. -/
  property : P hom

@[simps!]
/-
**CategoryTheory.InducedWideCategory.category** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.InducedWideCategory`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₂} D] →       (F : C → D) →         (P : CategoryTheory.MorphismProperty D) → 
          [inst_1 : P.IsMultiplicative] → CategoryTheory.Category.{v₁, u₁} (Cate
goryTheory.InducedWideCategory D F P)
参数：F : C → D；P : CategoryTheory.MorphismProperty D；CategoryTheory.InducedWideCat
egory D F P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance InducedWideCategory.category :
    Category (InducedWideCategory D F P) where
  Hom X Y := Hom X Y
  id X := ⟨𝟙 (F X), P.id_mem (F X)⟩
  comp {_ _ _} f g := ⟨f.1 ≫ g.1, P.comp_mem _ _ f.2 g.2⟩

/-- The forgetful functor from an induced wide category to the original category. -/
@[simps]
/-
**CategoryTheory.wideInducedFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：wideInducedFunctor : InducedWideCategory D F P ⥤ D where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from an induced wide category to the original category.
-/
def wideInducedFunctor : InducedWideCategory D F P ⥤ D where
  obj := F
  map {_ _} f := f.1

/-- The induced functor `wideInducedFunctor F P : InducedWideCategory D F P ⥤ D`
is faithful. -/
/-
**CategoryTheory.InducedWideCategory.faithful** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.InducedWideCategory`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₂} D] 
(F : C → D)   (P : CategoryTheory.MorphismProperty D) [inst_1 : P.IsMultiplicati
ve],   (CategoryTheory.wideInducedFunctor F P).Faithful
参数：F : C → D；P : CategoryTheory.MorphismProperty D；CategoryTheory.wideInducedFun
ctor F P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.wideInducedFunctor_map`：∀ {C : Type u₁} {D : Type u₂} [in
st : CategoryTheory.Category.{v₁, u₂} D] (F : C → D)   (P : CategoryTheory.Morph
ismProperty D) [inst_1 : P.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.InducedWideCategory.Hom.mk.congr_simp`：∀ {C : Type u₁} {D
 : Type u₂} [inst : CategoryTheory.Category.{v₁, u₂} D] {F : C → D}   {P : Categ
oryTheory.MorphismProperty D} [inst_1 : P.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The induced functor `wideInducedFunctor F P : InducedWideCategory D F P ⥤ D`
is faithful.
-/
instance InducedWideCategory.faithful : (wideInducedFunctor F P).Faithful where
  map_injective {X Y} f g eq := by
    cases f
    cases g
    aesop

end Induced

section WideSubcategory

variable {C : Type u₁} [Category.{v₁} C]
variable (P : MorphismProperty C) [IsMultiplicative P]

/--
Structure for wide subcategories. Objects ignore the morphism property.
-/
@[ext, nolint unusedArguments]
/-
**CategoryTheory.WideSubcategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (_P : 
CategoryTheory.MorphismProperty C) → [_P.IsMultiplicative] → Type u₁
参数：_P : CategoryTheory.MorphismProperty C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure for wide subcategories. Objects ignore the morphism property.
-/
structure WideSubcategory (_P : MorphismProperty C) [IsMultiplicative _P] where
  /-- The category of which this is a wide subcategory -/
  obj : C
/-
**CategoryTheory.WideSubcategory.category** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.WideSubcategory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (P : C
ategoryTheory.MorphismProperty C) →       [inst_1 : P.IsMultiplicative] → Catego
ryTheory.Category.{v₁, u₁} (CategoryTheory.WideSubcategory P)
参数：P : CategoryTheory.MorphismProperty C；CategoryTheory.WideSubcategory P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance WideSubcategory.category : Category.{v₁} (WideSubcategory P) :=
  InducedWideCategory.category WideSubcategory.obj P

@[ext]
/-
**CategoryTheory.WideSubcategory.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.WideSubcategory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (P : CategoryT
heory.MorphismProperty C)   [inst_1 : P.IsMultiplicative] {X Y : CategoryTheory.
WideSubcategory P} {f g : X ⟶ Y}, f.hom = g.hom → f = g
参数：P : CategoryTheory.MorphismProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.InducedWideCategory.Hom.ext`：∀ {C : Type u₁} {D : Type u₂
} {inst : CategoryTheory.Category.{v₁, u₂} D} {F : C → D}   {P : CategoryTheory.
MorphismProperty D} {inst_1 : P.…
-/
lemma WideSubcategory.hom_ext {X Y : WideSubcategory P} {f g : X ⟶ Y} (h : f.hom = g.hom) :
    f = g :=
  InducedWideCategory.Hom.ext h

@[simp]
/-
**CategoryTheory.WideSubcategory.id_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.WideSubcategory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (P : CategoryT
heory.MorphismProperty C)   [inst_1 : P.IsMultiplicative] (X : CategoryTheory.Wi
deSubcategory P),   (CategoryTheory.CategoryStruct.id X).hom = CategoryTheory.Ca
tegoryStruct.id X.obj
参数：P : CategoryTheory.MorphismProperty C；X : CategoryTheory.WideSubcategory P；Ca
tegoryTheory.CategoryStruct.id X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma WideSubcategory.id_def (X : WideSubcategory P) : (CategoryStruct.id X).1 = 𝟙 X.obj := rfl

@[simp]
/-
**CategoryTheory.WideSubcategory.comp_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.WideSubcategory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (P : CategoryT
heory.MorphismProperty C)   [inst_1 : P.IsMultiplicative] {X Y Z : CategoryTheor
y.WideSubcategory P} (f : X ⟶ Y) (g : Y ⟶ Z),   (CategoryTheory.CategoryStruct.c
omp f g).hom = CategoryTheory.CategoryStruct.comp f.hom g.hom
参数：P : CategoryTheory.MorphismProperty C；f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.Cate
goryStruct.comp f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma WideSubcategory.comp_def {X Y Z : WideSubcategory P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = (f.1 ≫ g.1 : X.obj ⟶ Z.obj) := rfl

/-- The forgetful functor from a wide subcategory into the original category
("forgetting" the condition).
-/
/-
**CategoryTheory.wideSubcategoryInclusion** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory`。
形式化陈述：wideSubcategoryInclusion : WideSubcategory P ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from a wide subcategory into the original category
("forgetting" the condition).
-/
def wideSubcategoryInclusion : WideSubcategory P ⥤ C :=
  wideInducedFunctor WideSubcategory.obj P

@[simp]
/-
**CategoryTheory.wideSubcategoryInclusion.obj** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.wideSubcategoryInclusion`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (P : CategoryT
heory.MorphismProperty C)   [inst_1 : P.IsMultiplicative] (X : CategoryTheory.Wi
deSubcategory P),   (CategoryTheory.wideSubcategoryInclusion P).obj X = X.obj
参数：P : CategoryTheory.MorphismProperty C；X : CategoryTheory.WideSubcategory P；Ca
tegoryTheory.wideSubcategoryInclusion P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wideSubcategoryInclusion.obj (X) : (wideSubcategoryInclusion P).obj X = X.obj :=
  rfl

@[simp]
/-
**CategoryTheory.wideSubcategoryInclusion.map** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.wideSubcategoryInclusion`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (P : CategoryT
heory.MorphismProperty C)   [inst_1 : P.IsMultiplicative] {X Y : CategoryTheory.
WideSubcategory P} {f : X ⟶ Y},   (CategoryTheory.wideSubcategoryInclusion P).ma
p f = f.hom
参数：P : CategoryTheory.MorphismProperty C；CategoryTheory.wideSubcategoryInclusion
 P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wideSubcategoryInclusion.map {X Y} {f : X ⟶ Y} :
    (wideSubcategoryInclusion P).map f = f.1 :=
  rfl

/-- The inclusion of a wide subcategory is faithful. -/
/-
**CategoryTheory.wideSubcategory.faithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.wideSubcategory`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (P : CategoryT
heory.MorphismProperty C)   [inst_1 : P.IsMultiplicative], (CategoryTheory.wideS
ubcategoryInclusion P).Faithful
参数：P : CategoryTheory.MorphismProperty C；CategoryTheory.wideSubcategoryInclusion
 P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a wide subcategory is faithful.
-/
instance wideSubcategory.faithful : (wideSubcategoryInclusion P).Faithful :=
  inferInstanceAs (wideInducedFunctor WideSubcategory.obj P).Faithful

variable {P} in
/-- Build an isomorphism in `WideSubcategory P` from an isomorphism in `C`. -/
@[simps!]
/-
**CategoryTheory.WideSubcategory.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.WideSubcategory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {P : C
ategoryTheory.MorphismProperty C} →       [inst_1 : P.IsMultiplicative] →       
  {X Y : CategoryTheory.WideSubcategory P} → (e : X.obj ≅ Y.obj) → P e.hom → P e
.inv → (X ≅ Y)
参数：e : X.obj ≅ Y.obj；X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build an isomorphism in `WideSubcategory P` from an isomorphism in `C`.
-/
def WideSubcategory.isoMk {X Y : WideSubcategory P} (e : X.obj ≅ Y.obj)
    (h₁ : P e.hom) (h₂ : P e.inv) : X ≅ Y where
  hom := ⟨e.hom, h₁⟩
  inv := ⟨e.inv, h₂⟩

@[deprecated (since := "2026-08-07")] alias isoMk := WideSubcategory.isoMk

end WideSubcategory

end CategoryTheory

