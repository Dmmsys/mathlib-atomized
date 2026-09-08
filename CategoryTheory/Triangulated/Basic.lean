/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Shift.Basic

/-!
# Triangles

This file contains the definition of triangles in an additive category with an additive shift.
It also defines morphisms between these triangles.

TODO: generalise this to n-angles in n-angulated categories as in https://arxiv.org/abs/1006.4592
-/

@[expose] public section


noncomputable section

open CategoryTheory Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory.Pretriangulated

open CategoryTheory.Category

/-
We work in a category `C` equipped with a shift.
-/
variable (C : Type u) [Category.{v} C] [HasShift C ℤ]

/-- A triangle in `C` is a sextuple `(X,Y,Z,f,g,h)` where `X,Y,Z` are objects of `C`,
and `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ X⟦1⟧` are morphisms in `C`. -/
@[stacks 0144]
/-
**CategoryTheory.Pretriangulated.Triangle** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory.Pretriangulated`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.HasShift C ℤ] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A triangle in `C` is a sextuple `(X,Y,Z,f,g,h)` where `X,Y,Z` are objects of `C`
,
and `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ X⟦1⟧` are morphisms in `C`.
-/
structure Triangle where mk' ::
  /-- the first object of a triangle -/
  obj₁ : C
  /-- the second object of a triangle -/
  obj₂ : C
  /-- the third object of a triangle -/
  obj₃ : C
  /-- the first morphism of a triangle -/
  mor₁ : obj₁ ⟶ obj₂
  /-- the second morphism of a triangle -/
  mor₂ : obj₂ ⟶ obj₃
  /-- the third morphism of a triangle -/
  mor₃ : obj₃ ⟶ obj₁⟦(1 : ℤ)⟧

variable {C}

/-- A triangle `(X,Y,Z,f,g,h)` in `C` is defined by the morphisms `f : X ⟶ Y`, `g : Y ⟶ Z`
and `h : Z ⟶ X⟦1⟧`.
-/
@[simps]
/-
**CategoryTheory.Pretriangulated.Triangle.mk** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Pretriangulated.Triangle`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.HasShift C ℤ] →       {X Y Z : C} →         (X ⟶ Y) → (Y ⟶ Z) → 
(Z ⟶ (CategoryTheory.shiftFunctor C 1).obj X) → CategoryTheory.Pretriangulated.T
riangle C
参数：X ⟶ Y；Y ⟶ Z；Z ⟶ (CategoryTheory.shiftFunctor C 1).obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A triangle `(X,Y,Z,f,g,h)` in `C` is defined by the morphisms `f : X ⟶ Y`, `g : 
Y ⟶ Z`
and `h : Z ⟶ X⟦1⟧`.
-/
def Triangle.mk {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧) : Triangle C where
  obj₁ := X
  obj₂ := Y
  obj₃ := Z
  mor₁ := f
  mor₂ := g
  mor₃ := h

section

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

/-
**CategoryTheory.Pretriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pret
riangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Triangle C) :=
  ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

/-- For each object in `C`, there is a triangle of the form `(X,X,0,𝟙 X,0,0)`
-/
@[simps!]
/-
**CategoryTheory.Pretriangulated.contractibleTriangle** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Pretriangulated`。
形式化陈述：contractibleTriangle (X : C) : Triangle C
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For each object in `C`, there is a triangle of the form `(X,X,0,𝟙 X,0,0)`
-/
def contractibleTriangle (X : C) : Triangle C :=
  Triangle.mk (𝟙 X) (0 : X ⟶ 0) 0

end

/-- A morphism of triangles `(X,Y,Z,f,g,h) ⟶ (X',Y',Z',f',g',h')` in `C` is a triple of morphisms
`a : X ⟶ X'`, `b : Y ⟶ Y'`, `c : Z ⟶ Z'` such that
`a ≫ f' = f ≫ b`, `b ≫ g' = g ≫ c`, and `a⟦1⟧' ≫ h = h' ≫ c`.
In other words, we have a commutative diagram:
```
     f      g      h
  X  ───> Y  ───> Z  ───> X⟦1⟧
  │       │       │        │
  │a      │b      │c       │a⟦1⟧'
  V       V       V        V
  X' ───> Y' ───> Z' ───> X'⟦1⟧
     f'     g'     h'
```
-/
@[ext, stacks 0144]
/-
**CategoryTheory.Pretriangulated.TriangleMorphism** 是 Mathlib 中的一个结构，位于命名空间 `Cat
egoryTheory.Pretriangulated`。
形式化陈述：TriangleMorphism (T₁ : Triangle C) (T₂ : Triangle C) where /-- the first m
orphism in a triangle morphism -/ hom₁ : T₁.obj₁ ⟶ T₂.obj₁ /-- the second morphi
sm in a triangle morphism -/ hom₂ : T₁.obj₂ ⟶ T₂.obj₂ /-- the third morphism in 
a triangle morphism -/ hom₃ : T₁.obj₃ ⟶ T₂.obj₃ /-- the first commutative square
 of a triangle morphism -/ comm₁ : T₁.mor₁ ≫ hom₂ = hom₁ ≫ T₂.mor₁
参数：T₁ : Triangle C；T₂ : Triangle C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of triangles `(X,Y,Z,f,g,h) ⟶ (X',Y',Z',f',g',h')` in `C` is a triple
 of morphisms
`a : X ⟶ X'`, `b : Y ⟶ Y'`, `c : Z ⟶ Z'` such that
`a ≫ f' = f ≫ b`, `b ≫ g' = g ≫ c`, and `a⟦1⟧' ≫ h = h' ≫ c`.
In other words, we have a commutative diagram:
```
     f      g      h
  X  ───> Y  ───> Z  ───> X⟦1⟧
  │       │       │        │
  │a      │b      │c       │a⟦1⟧'
  V       V       V        V
  X' ───> Y' ───> Z' ───> X'⟦1⟧
     f'     g'     h'
```
-/
structure TriangleMorphism (T₁ : Triangle C) (T₂ : Triangle C) where
  /-- the first morphism in a triangle morphism -/
  hom₁ : T₁.obj₁ ⟶ T₂.obj₁
  /-- the second morphism in a triangle morphism -/
  hom₂ : T₁.obj₂ ⟶ T₂.obj₂
  /-- the third morphism in a triangle morphism -/
  hom₃ : T₁.obj₃ ⟶ T₂.obj₃
  /-- the first commutative square of a triangle morphism -/
  comm₁ : T₁.mor₁ ≫ hom₂ = hom₁ ≫ T₂.mor₁ := by cat_disch
  /-- the second commutative square of a triangle morphism -/
  comm₂ : T₁.mor₂ ≫ hom₃ = hom₂ ≫ T₂.mor₂ := by cat_disch
  /-- the third commutative square of a triangle morphism -/
  comm₃ : T₁.mor₃ ≫ hom₁⟦1⟧' = hom₃ ≫ T₂.mor₃ := by cat_disch

attribute [reassoc (attr := simp)] TriangleMorphism.comm₁ TriangleMorphism.comm₂
  TriangleMorphism.comm₃

/-- The identity triangle morphism.
-/
@[simps]
/-
**CategoryTheory.Pretriangulated.triangleMorphismId** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Pretriangulated`。
形式化陈述：triangleMorphismId (T : Triangle C) : TriangleMorphism T T where hom₁
参数：T : Triangle C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity triangle morphism.
-/
def triangleMorphismId (T : Triangle C) : TriangleMorphism T T where
  hom₁ := 𝟙 T.obj₁
  hom₂ := 𝟙 T.obj₂
  hom₃ := 𝟙 T.obj₃
/-
**CategoryTheory.Pretriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pret
riangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (T : Triangle C) : Inhabited (TriangleMorphism T T) :=
  ⟨triangleMorphismId T⟩

variable {T₁ T₂ T₃ : Triangle C}

/-- Composition of triangle morphisms gives a triangle morphism.
-/
@[simps]
/-
**CategoryTheory.Pretriangulated.TriangleMorphism.comp** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Pretriangulated.TriangleMorphism`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.HasShift C ℤ] →       {T₁ T₂ T₃ : CategoryTheory.Pretriangulated
.Triangle C} →         CategoryTheory.Pretriangulated.TriangleMorphism T₁ T₂ →  
         CategoryTheory.Pretriangulated.TriangleMorphism T₂ T₃ → CategoryTheory.
Pretriangulated.TriangleMorphism T₁ T₃
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of triangle morphisms gives a triangle morphism.
-/
def TriangleMorphism.comp (f : TriangleMorphism T₁ T₂) (g : TriangleMorphism T₂ T₃) :
    TriangleMorphism T₁ T₃ where
  hom₁ := f.hom₁ ≫ g.hom₁
  hom₂ := f.hom₂ ≫ g.hom₂
  hom₃ := f.hom₃ ≫ g.hom₃

/-- Triangles with triangle morphisms form a category.
-/
@[simps]
/-
**CategoryTheory.Pretriangulated.triangleCategory** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Pretriangulated`。
形式化陈述：triangleCategory : Category (Triangle C) where Hom A B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Triangles with triangle morphisms form a category.
-/
instance triangleCategory : Category (Triangle C) where
  Hom A B := TriangleMorphism A B
  id A := triangleMorphismId A
  comp f g := f.comp g

@[ext]
/-
**CategoryTheory.Pretriangulated.Triangle.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Pretriangulated.Triangle`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.HasShift C ℤ]   {A B : CategoryTheory.Pretriangulated.Triangle C} (f g :
 A ⟶ B),   f.hom₁ = g.hom₁ → f.hom₂ = g.hom₂ → f.hom₃ = g.hom₃ → f = g
参数：f g : A ⟶ B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.TriangleMorphism.ext`：∀ {C : Type u} {ins
t : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.HasShift C ℤ}   {
T₁ T₂ : CategoryTheory.Pretriangulated.Tr…
-/
lemma Triangle.hom_ext {A B : Triangle C} (f g : A ⟶ B)
    (h₁ : f.hom₁ = g.hom₁) (h₂ : f.hom₂ = g.hom₂) (h₃ : f.hom₃ = g.hom₃) : f = g :=
  TriangleMorphism.ext h₁ h₂ h₃
/-
**CategoryTheory.Pretriangulated.id_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_hom₁ (A : Triangle C) : TriangleMorphism.hom₁ (𝟙 A) = 𝟙 _ := rfl
/-
**CategoryTheory.Pretriangulated.id_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_hom₂ (A : Triangle C) : TriangleMorphism.hom₂ (𝟙 A) = 𝟙 _ := rfl
/-
**CategoryTheory.Pretriangulated.id_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_hom₃ (A : Triangle C) : TriangleMorphism.hom₃ (𝟙 A) = 𝟙 _ := rfl

@[reassoc]
/-
**CategoryTheory.Pretriangulated.comp_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_hom₁ {X Y Z : Triangle C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom₁ = f.hom₁ ≫ g.hom₁ := rfl
@[reassoc]
/-
**CategoryTheory.Pretriangulated.comp_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_hom₂ {X Y Z : Triangle C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom₂ = f.hom₂ ≫ g.hom₂ := rfl
@[reassoc]
/-
**CategoryTheory.Pretriangulated.comp_hom** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_hom₃ {X Y Z : Triangle C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom₃ = f.hom₃ ≫ g.hom₃ := rfl

/-- Make a morphism between triangles from the required data. -/
@[simps]
/-
**CategoryTheory.Pretriangulated.Triangle.homMk** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Pretriangulated.Triangle`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.HasShift C ℤ] →       (A B : CategoryTheory.Pretriangulated.Tria
ngle C) →         (hom₁ : A.obj₁ ⟶ B.obj₁) →           (hom₂ : A.obj₂ ⟶ B.obj₂) 
→             (hom₃ : A.obj₃ ⟶ B.obj₃) →               autoParam                
   (CategoryTheory.CategoryStruct.comp A.mor₁ hom₂ = CategoryTheory.CategoryStru
ct.comp hom₁ B.mor₁)                   CategoryTheory.Pretriangulated.Triangle.h
omMk._auto_1 →                 autoParam                     (CategoryTheory.Cat
egoryStruct.comp A.mor₂ hom₃ = CategoryTheory.CategoryStruct.comp hom₂ B.mor₂)  
                   CategoryTheory.Pretriangulated.Triangle.homMk._auto_3 →      
             autoParam                       (CategoryTheory.CategoryStruct.comp
 A.mor₃ ((CategoryTheory.shiftFunctor C 1).map hom₁) =                         C
ategoryTheory.CategoryStruct.comp hom₃ B.mor₃)                       CategoryThe
ory.Pretriangulated.Triangle.homMk._auto_5 →                     (A ⟶ B)
参数：A B : CategoryTheory.Pretriangulated.Triangle C；hom₁ : A.obj₁ ⟶ B.obj₁；hom₂ :
 A.obj₂ ⟶ B.obj₂；hom₃ : A.obj₃ ⟶ B.obj₃；CategoryTheory.CategoryStruct.comp A.mor
₁ hom₂ = CategoryTheory.CategoryStruct.comp hom₁ B.mor₁；CategoryTheory.CategoryS
truct.comp A.mor₂ hom₃ = CategoryTheory.CategoryStruct.comp hom₂ B.mor₂；Category
Theory.CategoryStruct.comp A.mor₃ ((CategoryTheory.shiftFunctor C 1).map hom₁) =
                         CategoryTheory.CategoryStruct.comp hom₃ B.mor₃；A ⟶ B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a morphism between triangles from the required data.
-/
def Triangle.homMk (A B : Triangle C)
    (hom₁ : A.obj₁ ⟶ B.obj₁) (hom₂ : A.obj₂ ⟶ B.obj₂) (hom₃ : A.obj₃ ⟶ B.obj₃)
    (comm₁ : A.mor₁ ≫ hom₂ = hom₁ ≫ B.mor₁ := by cat_disch)
    (comm₂ : A.mor₂ ≫ hom₃ = hom₂ ≫ B.mor₂ := by cat_disch)
    (comm₃ : A.mor₃ ≫ hom₁⟦1⟧' = hom₃ ≫ B.mor₃ := by cat_disch) :
    A ⟶ B where
  hom₁ := hom₁
  hom₂ := hom₂
  hom₃ := hom₃
  comm₁ := comm₁
  comm₂ := comm₂
  comm₃ := comm₃

/-- Make an isomorphism between triangles from the required data. -/
@[simps]
/-
**CategoryTheory.Pretriangulated.Triangle.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Pretriangulated.Triangle`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.HasShift C ℤ] →       (A B : CategoryTheory.Pretriangulated.Tria
ngle C) →         (iso₁ : A.obj₁ ≅ B.obj₁) →           (iso₂ : A.obj₂ ≅ B.obj₂) 
→             (iso₃ : A.obj₃ ≅ B.obj₃) →               autoParam                
   (CategoryTheory.CategoryStruct.comp A.mor₁ iso₂.hom =                     Cat
egoryTheory.CategoryStruct.comp iso₁.hom B.mor₁)                   CategoryTheor
y.Pretriangulated.Triangle.isoMk._auto_1 →                 autoParam            
         (CategoryTheory.CategoryStruct.comp A.mor₂ iso₃.hom =                  
     CategoryTheory.CategoryStruct.comp iso₂.hom B.mor₂)                     Cat
egoryTheory.Pretriangulated.Triangle.isoMk._auto_3 →                   autoParam
                       (CategoryTheory.CategoryStruct.comp A.mor₃ ((CategoryTheo
ry.shiftFunctor C 1).map iso₁.hom) =                         CategoryTheory.Cate
goryStruct.comp iso₃.hom B.mor₃)                       CategoryTheory.Pretriangu
lated.Triangle.isoMk._auto_5 →                     (A ≅ B)
参数：A B : CategoryTheory.Pretriangulated.Triangle C；iso₁ : A.obj₁ ≅ B.obj₁；iso₂ :
 A.obj₂ ≅ B.obj₂；iso₃ : A.obj₃ ≅ B.obj₃；CategoryTheory.CategoryStruct.comp A.mor
₁ iso₂.hom =                     CategoryTheory.CategoryStruct.comp iso₁.hom B.m
or₁；CategoryTheory.CategoryStruct.comp A.mor₂ iso₃.hom =                       C
ategoryTheory.CategoryStruct.comp iso₂.hom B.mor₂；CategoryTheory.CategoryStruct.
comp A.mor₃ ((CategoryTheory.shiftFunctor C 1).map iso₁.hom) =                  
       CategoryTheory.CategoryStruct.comp iso₃.hom B.mor₃；A ≅ B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make an isomorphism between triangles from the required data.
-/
def Triangle.isoMk (A B : Triangle C)
    (iso₁ : A.obj₁ ≅ B.obj₁) (iso₂ : A.obj₂ ≅ B.obj₂) (iso₃ : A.obj₃ ≅ B.obj₃)
    (comm₁ : A.mor₁ ≫ iso₂.hom = iso₁.hom ≫ B.mor₁ := by cat_disch)
    (comm₂ : A.mor₂ ≫ iso₃.hom = iso₂.hom ≫ B.mor₂ := by cat_disch)
    (comm₃ : A.mor₃ ≫ iso₁.hom⟦1⟧' = iso₃.hom ≫ B.mor₃ := by cat_disch) : A ≅ B where
  hom := Triangle.homMk _ _ iso₁.hom iso₂.hom iso₃.hom comm₁ comm₂ comm₃
  inv := Triangle.homMk _ _ iso₁.inv iso₂.inv iso₃.inv
    (by simp only [← cancel_mono iso₂.hom, assoc, Iso.inv_hom_id, comp_id,
      comm₁, Iso.inv_hom_id_assoc])
    (by simp only [← cancel_mono iso₃.hom, assoc, Iso.inv_hom_id, comp_id,
      comm₂, Iso.inv_hom_id_assoc])
    (by simp only [← cancel_mono (iso₁.hom⟦(1 : ℤ)⟧'), Category.assoc, comm₃,
      Iso.inv_hom_id_assoc, ← Functor.map_comp, Iso.inv_hom_id,
      Functor.map_id, Category.comp_id])
/-
**CategoryTheory.Pretriangulated.Triangle.isIso_of_isIsos** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Pretriangulated.Triangle`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.HasShift C ℤ]   {A B : CategoryTheory.Pretriangulated.Triangle C} (f : A
 ⟶ B),   CategoryTheory.IsIso f.hom₁ → CategoryTheory.IsIso f.hom₂ → CategoryThe
ory.IsIso f.hom₃ → CategoryTheory.IsIso f
参数：f : A ⟶ B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pretriangulated.TriangleMorphism.comm₁`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {T₁ T₂ : CategoryTheory.Pretriangulated.Tr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Pretriangulated.TriangleMorphism.comm₂`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {T₁ T₂ : CategoryTheory.Pretriangulated.Tr…
· 使用定理 `CategoryTheory.Pretriangulated.TriangleMorphism.comm₃`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {T₁ T₂ : CategoryTheory.Pretriangulated.Tr…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma Triangle.isIso_of_isIsos {A B : Triangle C} (f : A ⟶ B)
    (h₁ : IsIso f.hom₁) (h₂ : IsIso f.hom₂) (h₃ : IsIso f.hom₃) : IsIso f := by
  let e := Triangle.isoMk A B (asIso f.hom₁) (asIso f.hom₂) (asIso f.hom₃)
    (by simp) (by simp) (by simp)
  exact (inferInstance : IsIso e.hom)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Pretriangulated._root_.CategoryTheory.Iso.hom_inv_id_triangle_h
om** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₁ {A B : Triangle C} (e : A ≅ B) :
    e.hom.hom₁ ≫ e.inv.hom₁ = 𝟙 _ := by rw [← comp_hom₁, e.hom_inv_id, id_hom₁]
@[reassoc (attr := simp)]
/-
**CategoryTheory.Pretriangulated._root_.CategoryTheory.Iso.hom_inv_id_triangle_h
om** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₂ {A B : Triangle C} (e : A ≅ B) :
    e.hom.hom₂ ≫ e.inv.hom₂ = 𝟙 _ := by rw [← comp_hom₂, e.hom_inv_id, id_hom₂]
@[reassoc (attr := simp)]
/-
**CategoryTheory.Pretriangulated._root_.CategoryTheory.Iso.hom_inv_id_triangle_h
om** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₃ {A B : Triangle C} (e : A ≅ B) :
    e.hom.hom₃ ≫ e.inv.hom₃ = 𝟙 _ := by rw [← comp_hom₃, e.hom_inv_id, id_hom₃]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Pretriangulated._root_.CategoryTheory.Iso.inv_hom_id_triangle_h
om** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₁ {A B : Triangle C} (e : A ≅ B) :
    e.inv.hom₁ ≫ e.hom.hom₁ = 𝟙 _ := by rw [← comp_hom₁, e.inv_hom_id, id_hom₁]
@[reassoc (attr := simp)]
/-
**CategoryTheory.Pretriangulated._root_.CategoryTheory.Iso.inv_hom_id_triangle_h
om** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₂ {A B : Triangle C} (e : A ≅ B) :
    e.inv.hom₂ ≫ e.hom.hom₂ = 𝟙 _ := by rw [← comp_hom₂, e.inv_hom_id, id_hom₂]
@[reassoc (attr := simp)]
/-
**CategoryTheory.Pretriangulated._root_.CategoryTheory.Iso.inv_hom_id_triangle_h
om** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₃ {A B : Triangle C} (e : A ≅ B) :
    e.inv.hom₃ ≫ e.hom.hom₃ = 𝟙 _ := by rw [← comp_hom₃, e.inv_hom_id, id_hom₃]
/-
**CategoryTheory.Pretriangulated.Triangle.eqToHom_hom** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Triangle.eqToHom_hom₁ {A B : Triangle C} (h : A = B) :
    (eqToHom h).hom₁ = eqToHom (by subst h; rfl) := by subst h; rfl
/-
**CategoryTheory.Pretriangulated.Triangle.eqToHom_hom** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Triangle.eqToHom_hom₂ {A B : Triangle C} (h : A = B) :
    (eqToHom h).hom₂ = eqToHom (by subst h; rfl) := by subst h; rfl
/-
**CategoryTheory.Pretriangulated.Triangle.eqToHom_hom** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Triangle.eqToHom_hom₃ {A B : Triangle C} (h : A = B) :
    (eqToHom h).hom₃ = eqToHom (by subst h; rfl) := by subst h; rfl

namespace Triangle

section Preadditive

variable [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]

@[simps (attr := grind =)]
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (T₁ ⟶ T₂) where
  zero :=
    { hom₁ := 0
      hom₂ := 0
      hom₃ := 0 }

@[simps (attr := grind =)]
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (T₁ ⟶ T₂) where
  add f g :=
    { hom₁ := f.hom₁ + g.hom₁
      hom₂ := f.hom₂ + g.hom₂
      hom₃ := f.hom₃ + g.hom₃ }

@[simps (attr := grind =)]
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (T₁ ⟶ T₂) where
  neg f :=
    { hom₁ := -f.hom₁
      hom₂ := -f.hom₂
      hom₃ := -f.hom₃ }

@[simps (attr := grind =)]
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (T₁ ⟶ T₂) where
  sub f g :=
    { hom₁ := f.hom₁ - g.hom₁
      hom₂ := f.hom₂ - g.hom₂
      hom₃ := f.hom₃ - g.hom₃ }

section

variable {R : Type*} [Semiring R] [Linear R C]
  [∀ (n : ℤ), Functor.Linear R (shiftFunctor C n)]

@[simps (attr := grind =)]
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul R (T₁ ⟶ T₂) where
  smul n f :=
    { hom₁ := n • f.hom₁
      hom₂ := n • f.hom₂
      hom₃ := n • f.hom₃ }

omit [∀ (n : ℤ), (shiftFunctor C n).Additive]

end

/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (T₁ ⟶ T₂) where
  zero_add f := by ext <;> apply zero_add
  add_assoc f g h := by ext <;> apply add_assoc
  add_zero f := by ext <;> apply add_zero
  add_comm f g := by ext <;> apply add_comm
  neg_add_cancel f := by ext <;> apply neg_add_cancel
  sub_eq_add_neg f g := by ext <;> apply sub_eq_add_neg
  nsmul_zero f := by cat_disch
  nsmul_succ n f := by ext <;> apply AddMonoid.nsmul_succ
  zsmul_zero' := by cat_disch
  zsmul_succ' n f := by ext <;> apply SubNegMonoid.zsmul_succ'
  zsmul_neg' n f := by ext <;> apply SubNegMonoid.zsmul_neg'
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive (Triangle C) where

end Preadditive

section Linear

variable [Preadditive C] {R : Type*} [Semiring R] [Linear R C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [∀ (n : ℤ), Functor.Linear R (shiftFunctor C n)]

attribute [local simp] mul_smul add_smul in
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R (T₁ ⟶ T₂) where
  one_smul := by aesop
  mul_smul := by aesop
  smul_zero := by aesop
  smul_add := by aesop
  add_smul := by aesop
  zero_smul := by aesop
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Linear R (Triangle C) where

end Linear

end Triangle

/-- The obvious triangle `X₁ ⟶ X₁ ⊞ X₂ ⟶ X₂ ⟶ X₁⟦1⟧`. -/
@[simps!]
/-
**CategoryTheory.Pretriangulated.binaryBiproductTriangle** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Pretriangulated`。
形式化陈述：binaryBiproductTriangle (X₁ X₂ : C) [HasZeroMorphisms C] [HasBinaryBiprodu
ct X₁ X₂] : Triangle C
参数：X₁ X₂ : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious triangle `X₁ ⟶ X₁ ⊞ X₂ ⟶ X₂ ⟶ X₁⟦1⟧`.
-/
def binaryBiproductTriangle (X₁ X₂ : C) [HasZeroMorphisms C] [HasBinaryBiproduct X₁ X₂] :
    Triangle C :=
  Triangle.mk biprod.inl (Limits.biprod.snd : X₁ ⊞ X₂ ⟶ _) 0

/-- The obvious triangle `X₁ ⟶ X₁ ⨯ X₂ ⟶ X₂ ⟶ X₁⟦1⟧`. -/
@[simps!]
/-
**CategoryTheory.Pretriangulated.binaryProductTriangle** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Pretriangulated`。
形式化陈述：binaryProductTriangle (X₁ X₂ : C) [HasZeroMorphisms C] [HasBinaryProduct X
₁ X₂] : Triangle C
参数：X₁ X₂ : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious triangle `X₁ ⟶ X₁ ⨯ X₂ ⟶ X₂ ⟶ X₁⟦1⟧`.
-/
def binaryProductTriangle (X₁ X₂ : C) [HasZeroMorphisms C] [HasBinaryProduct X₁ X₂] :
    Triangle C :=
  Triangle.mk ((Limits.prod.lift (𝟙 X₁) 0)) (Limits.prod.snd : X₁ ⨯ X₂ ⟶ _) 0

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism of triangles
`binaryProductTriangle X₁ X₂ ≅ binaryBiproductTriangle X₁ X₂`. -/
@[simps!]
/-
**CategoryTheory.Pretriangulated.binaryProductTriangleIsoBinaryBiproductTriangle
** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：binaryProductTriangleIsoBinaryBiproductTriangle (X₁ X₂ : C) [HasZeroMorphi
sms C] [HasBinaryBiproduct X₁ X₂] : binaryProductTriangle X₁ X₂ ≅ binaryBiproduc
tTriangle X₁ X₂
参数：X₁ X₂ : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproduct.hasLimit_pair`：∀ {C : Type uC} 
[inst : CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {P Q : C} [CategoryTheory…

--- 原说明 ---
The canonical isomorphism of triangles
`binaryProductTriangle X₁ X₂ ≅ binaryBiproductTriangle X₁ X₂`.
-/
def binaryProductTriangleIsoBinaryBiproductTriangle
    (X₁ X₂ : C) [HasZeroMorphisms C] [HasBinaryBiproduct X₁ X₂] :
    binaryProductTriangle X₁ X₂ ≅ binaryBiproductTriangle X₁ X₂ :=
  Triangle.isoMk _ _ (Iso.refl _) (biprod.isoProd X₁ X₂).symm (Iso.refl _)
    (by cat_disch) (by simp) (by simp)

section

variable {J : Type*} (T : J → Triangle C)
  [HasProduct (fun j => (T j).obj₁)] [HasProduct (fun j => (T j).obj₂)]
  [HasProduct (fun j => (T j).obj₃)] [HasProduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧)]

/-- The product of a family of triangles. -/
@[simps!]
/-
**CategoryTheory.Pretriangulated.productTriangle** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Pretriangulated`。
形式化陈述：productTriangle : Triangle C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of a family of triangles.
-/
def productTriangle : Triangle C :=
  Triangle.mk (Limits.Pi.map (fun j => (T j).mor₁))
    (Limits.Pi.map (fun j => (T j).mor₂))
    (Limits.Pi.map (fun j => (T j).mor₃) ≫ inv (piComparison _ _))

set_option backward.defeqAttrib.useBackward true in
/-- A projection from the product of a family of triangles. -/
@[simps]
/-
**CategoryTheory.Pretriangulated.productTriangle.** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A projection from the product of a family of triangles.
-/
def productTriangle.π (j : J) :
    productTriangle T ⟶ T j where
  hom₁ := Pi.π _ j
  hom₂ := Pi.π _ j
  hom₃ := Pi.π _ j

/-- The fan given by `productTriangle T`. -/
@[simp]
/-
**CategoryTheory.Pretriangulated.productTriangle.fan** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Pretriangulated.productTriangle`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.HasShift C ℤ] →       {J : Type u_1} →         (T : J → Category
Theory.Pretriangulated.Triangle C) →           [CategoryTheory.Limits.HasProduct
 fun j => (T j).obj₁] →             [CategoryTheory.Limits.HasProduct fun j => (
T j).obj₂] →               [CategoryTheory.Limits.HasProduct fun j => (T j).obj₃
] →                 [CategoryTheory.Limits.HasProduct fun j => (CategoryTheory.s
hiftFunctor C 1).obj (T j).obj₁] →                   CategoryTheory.Limits.Fan T
参数：T : J → CategoryTheory.Pretriangulated.Triangle C；T j；T j；T j；CategoryTheory.
shiftFunctor C 1；T j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fan given by `productTriangle T`.
-/
def productTriangle.fan : Fan T := Fan.mk (productTriangle T) (productTriangle.π T)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A family of morphisms `T' ⟶ T j` lifts to a morphism `T' ⟶ productTriangle T`. -/
@[simps]
/-
**CategoryTheory.Pretriangulated.productTriangle.lift** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Pretriangulated.productTriangle`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.HasShift C ℤ] →       {J : Type u_1} →         (T : J → Category
Theory.Pretriangulated.Triangle C) →           [inst_2 : CategoryTheory.Limits.H
asProduct fun j => (T j).obj₁] →             [inst_3 : CategoryTheory.Limits.Has
Product fun j => (T j).obj₂] →               [inst_4 : CategoryTheory.Limits.Has
Product fun j => (T j).obj₃] →                 [inst_5 : CategoryTheory.Limits.H
asProduct fun j => (CategoryTheory.shiftFunctor C 1).obj (T j).obj₁] →          
         {T' : CategoryTheory.Pretriangulated.Triangle C} →                     
((j : J) → T' ⟶ T j) → (T' ⟶ CategoryTheory.Pretriangulated.productTriangle T)
参数：T : J → CategoryTheory.Pretriangulated.Triangle C；T j；T j；T j；CategoryTheory.
shiftFunctor C 1；T j；(j : J) → T' ⟶ T j；T' ⟶ CategoryTheory.Pretriangulated.prod
uctTriangle T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of morphisms `T' ⟶ T j` lifts to a morphism `T' ⟶ productTriangle T`.
-/
def productTriangle.lift {T' : Triangle C} (φ : ∀ j, T' ⟶ T j) :
    T' ⟶ productTriangle T where
  hom₁ := Pi.lift (fun j => (φ j).hom₁)
  hom₂ := Pi.lift (fun j => (φ j).hom₂)
  hom₃ := Pi.lift (fun j => (φ j).hom₃)
  comm₃ := by
    dsimp
    rw [← cancel_mono (piComparison _ _), assoc, assoc, assoc, IsIso.inv_hom_id, comp_id]
    cat_disch

set_option backward.isDefEq.respectTransparency false in
/-- The triangle `productTriangle T` satisfies the universal property of the categorical
product of the triangles `T`. -/
/-
**CategoryTheory.Pretriangulated.productTriangle.isLimitFan** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Pretriangulated.productTriangle`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.HasShift C ℤ] →       {J : Type u_1} →         (T : J → Category
Theory.Pretriangulated.Triangle C) →           [inst_2 : CategoryTheory.Limits.H
asProduct fun j => (T j).obj₁] →             [inst_3 : CategoryTheory.Limits.Has
Product fun j => (T j).obj₂] →               [inst_4 : CategoryTheory.Limits.Has
Product fun j => (T j).obj₃] →                 [inst_5 : CategoryTheory.Limits.H
asProduct fun j => (CategoryTheory.shiftFunctor C 1).obj (T j).obj₁] →          
         CategoryTheory.Limits.IsLimit (CategoryTheory.Pretriangulated.productTr
iangle.fan T)
参数：T : J → CategoryTheory.Pretriangulated.Triangle C；T j；T j；T j；CategoryTheory.
shiftFunctor C 1；T j；CategoryTheory.Pretriangulated.productTriangle.fan T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The triangle `productTriangle T` satisfies the universal property of the categor
ical
product of the triangles `T`.
-/
def productTriangle.isLimitFan : IsLimit (productTriangle.fan T) :=
  Fan.IsLimit.mk _ (fun s => productTriangle.lift T s.proj) (fun s j => by cat_disch) (by
    intro s m hm
    ext1
    all_goals
      exact Pi.hom_ext _ _ (fun j => (by simp [← hm])))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Pretriangulated.productTriangle.zero** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Pretriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma productTriangle.zero₃₁ [HasZeroMorphisms C]
    (h : ∀ j, (T j).mor₃ ≫ (T j).mor₁⟦(1 : ℤ)⟧' = 0) :
    (productTriangle T).mor₃ ≫ (productTriangle T).mor₁⟦1⟧' = 0 := by
  have : HasProduct (fun j => (T j).obj₂⟦(1 : ℤ)⟧) :=
    ⟨_, isLimitFanMkObjOfIsLimit (shiftFunctor C (1 : ℤ)) _ _
      (productIsProduct (fun j => (T j).obj₂))⟩
  dsimp
  change _ ≫ (Pi.lift (fun j => Pi.π _ j ≫ (T j).mor₁))⟦(1 : ℤ)⟧' = 0
  rw [assoc, ← cancel_mono (piComparison _ _), zero_comp, assoc, assoc]
  ext j
  simp [h j]

end

set_option backward.defeqAttrib.useBackward true in
variable (C) in
/-- The functor `C ⥤ Triangle C` which sends `X` to `contractibleTriangle X`. -/
@[simps]
/-
**CategoryTheory.Pretriangulated.contractibleTriangleFunctor** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Pretriangulated`。
形式化陈述：contractibleTriangleFunctor [HasZeroObject C] [HasZeroMorphisms C] : C ⥤ T
riangle C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `C ⥤ Triangle C` which sends `X` to `contractibleTriangle X`.
-/
def contractibleTriangleFunctor [HasZeroObject C] [HasZeroMorphisms C] : C ⥤ Triangle C where
  obj X := contractibleTriangle X
  map f :=
    { hom₁ := f
      hom₂ := f
      hom₃ := 0 }

namespace Triangle

/-- The first projection `Triangle C ⥤ C`. -/
@[simps]
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection `Triangle C ⥤ C`.
-/
def π₁ : Triangle C ⥤ C where
  obj T := T.obj₁
  map f := f.hom₁

/-- The second projection `Triangle C ⥤ C`. -/
@[simps]
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection `Triangle C ⥤ C`.
-/
def π₂ : Triangle C ⥤ C where
  obj T := T.obj₂
  map f := f.hom₂

/-- The third projection `Triangle C ⥤ C`. -/
@[simps]
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The third projection `Triangle C ⥤ C`.
-/
def π₃ : Triangle C ⥤ C where
  obj T := T.obj₃
  map f := f.hom₃

set_option backward.defeqAttrib.useBackward true in
/-- The first morphism of a triangle, as a natural transformation `π₁ ⟶ π₂`. -/
@[simps]
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first morphism of a triangle, as a natural transformation `π₁ ⟶ π₂`.
-/
def π₁Toπ₂ : (π₁ : Triangle C ⥤ C) ⟶ Triangle.π₂ where
  app T := T.mor₁

set_option backward.defeqAttrib.useBackward true in
/-- The second morphism of a triangle, as a natural transformation `π₂ ⟶ π₃`. -/
@[simps]
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second morphism of a triangle, as a natural transformation `π₂ ⟶ π₃`.
-/
def π₂Toπ₃ : (π₂ : Triangle C ⥤ C) ⟶ Triangle.π₃ where
  app T := T.mor₂

set_option backward.defeqAttrib.useBackward true in
/-- The third morphism of a triangle, as a natural
transformation `π₃ ⟶ π₁ ⋙ shiftFunctor _ (1 : ℤ)`. -/
@[simps]
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The third morphism of a triangle, as a natural
transformation `π₃ ⟶ π₁ ⋙ shiftFunctor _ (1 : ℤ)`.
-/
def π₃Toπ₁ : (π₃ : Triangle C ⥤ C) ⟶ π₁ ⋙ shiftFunctor C (1 : ℤ) where
  app T := T.mor₃

section

variable {A B : Triangle C} (φ : A ⟶ B) [IsIso φ]

/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso φ.hom₁ := (inferInstance : IsIso (π₁.map φ))
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso φ.hom₂ := (inferInstance : IsIso (π₂.map φ))
/-
**CategoryTheory.Pretriangulated.Triangle.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Pretriangulated.Triangle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso φ.hom₃ := (inferInstance : IsIso (π₃.map φ))

end

section

open CategoryTheory.Functor

variable {J : Type*} [Category* J]

set_option backward.isDefEq.respectTransparency false in
/-- Constructor for functors to the category of triangles. -/
@[simps]
/-
**CategoryTheory.Pretriangulated.Triangle.functorMk** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Pretriangulated.Triangle`。
形式化陈述：functorMk {obj₁ obj₂ obj₃ : J ⥤ C} (mor₁ : obj₁ ⟶ obj₂) (mor₂ : obj₂ ⟶ obj
₃) (mor₃ : obj₃ ⟶ obj₁ ⋙ shiftFunctor C (1 : Int)) : J ⥤ Triangle C where obj j
参数：mor₁ : obj₁ ⟶ obj₂；mor₂ : obj₂ ⟶ obj₃；mor₃ : obj₃ ⟶ obj₁ ⋙ shiftFunctor C (1 
: Int)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for functors to the category of triangles.
-/
def functorMk {obj₁ obj₂ obj₃ : J ⥤ C}
    (mor₁ : obj₁ ⟶ obj₂) (mor₂ : obj₂ ⟶ obj₃) (mor₃ : obj₃ ⟶ obj₁ ⋙ shiftFunctor C (1 : ℤ)) :
    J ⥤ Triangle C where
  obj j := mk (mor₁.app j) (mor₂.app j) (mor₃.app j)
  map φ :=
    { hom₁ := obj₁.map φ
      hom₂ := obj₂.map φ
      hom₃ := obj₃.map φ }

/-- Constructor for natural transformations between functors to the
category of triangles. -/
@[simps]
/-
**CategoryTheory.Pretriangulated.Triangle.functorHomMk** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Pretriangulated.Triangle`。
形式化陈述：functorHomMk (A B : J ⥤ Triangle C) (hom₁ : A ⋙ π₁ ⟶ B ⋙ π₁) (hom₂ : A ⋙ π
₂ ⟶ B ⋙ π₂) (hom₃ : A ⋙ π₃ ⟶ B ⋙ π₃) (comm₁ : whiskerLeft A π₁Toπ₂ ≫ hom₂ = hom₁
 ≫ whiskerLeft B π₁Toπ₂
参数：A B : J ⥤ Triangle C；hom₁ : A ⋙ π₁ ⟶ B ⋙ π₁；hom₂ : A ⋙ π₂ ⟶ B ⋙ π₂；hom₃ : A ⋙
 π₃ ⟶ B ⋙ π₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for natural transformations between functors to the
category of triangles.
-/
def functorHomMk (A B : J ⥤ Triangle C) (hom₁ : A ⋙ π₁ ⟶ B ⋙ π₁)
    (hom₂ : A ⋙ π₂ ⟶ B ⋙ π₂) (hom₃ : A ⋙ π₃ ⟶ B ⋙ π₃)
    (comm₁ : whiskerLeft A π₁Toπ₂ ≫ hom₂ = hom₁ ≫ whiskerLeft B π₁Toπ₂ := by cat_disch)
    (comm₂ : whiskerLeft A π₂Toπ₃ ≫ hom₃ = hom₂ ≫ whiskerLeft B π₂Toπ₃ := by cat_disch)
    (comm₃ : whiskerLeft A π₃Toπ₁ ≫ whiskerRight hom₁ (shiftFunctor C (1 : ℤ)) =
      hom₃ ≫ whiskerLeft B π₃Toπ₁ := by cat_disch) : A ⟶ B where
  app j :=
    { hom₁ := hom₁.app j
      hom₂ := hom₂.app j
      hom₃ := hom₃.app j
      comm₁ := NatTrans.congr_app comm₁ j
      comm₂ := NatTrans.congr_app comm₂ j
      comm₃ := NatTrans.congr_app comm₃ j }
  naturality _ _ φ := by
    ext
    · exact hom₁.naturality φ
    · exact hom₂.naturality φ
    · exact hom₃.naturality φ

/-- Constructor for natural transformations between functors constructed
with `functorMk`. -/
@[simps!]
/-
**CategoryTheory.Pretriangulated.Triangle.functorHomMk'** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Pretriangulated.Triangle`。
形式化陈述：functorHomMk' {obj₁ obj₂ obj₃ : J ⥤ C} {mor₁ : obj₁ ⟶ obj₂} {mor₂ : obj₂ ⟶
 obj₃} {mor₃ : obj₃ ⟶ obj₁ ⋙ shiftFunctor C (1 : Int)} {obj₁' obj₂' obj₃' : J ⥤ 
C} {mor₁' : obj₁' ⟶ obj₂'} {mor₂' : obj₂' ⟶ obj₃'} {mor₃' : obj₃' ⟶ obj₁' ⋙ shif
tFunctor C (1 : Int)} (hom₁ : obj₁ ⟶ obj₁') (hom₂ : obj₂ ⟶ obj₂') (hom₃ : obj₃ ⟶
 obj₃') (comm₁ : mor₁ ≫ hom₂ = hom₁ ≫ mor₁') (comm₂ : mor₂ ≫ hom₃ = hom₂ ≫ mor₂'
) (comm₃ : mor₃ ≫ whiskerRight hom₁ (shiftFunctor C (1 : Int)) = hom₃ ≫ mor₃') :
 functorMk mor₁ mor₂ mor₃ 
参数：1 : Int；1 : Int；hom₁ : obj₁ ⟶ obj₁'；hom₂ : obj₂ ⟶ obj₂'；hom₃ : obj₃ ⟶ obj₃'；c
omm₁ : mor₁ ≫ hom₂ = hom₁ ≫ mor₁'；comm₂ : mor₂ ≫ hom₃ = hom₂ ≫ mor₂'；comm₃ : mor
₃ ≫ whiskerRight hom₁ (shiftFunctor C (1 : Int)) = hom₃ ≫ mor₃'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for natural transformations between functors constructed
with `functorMk`.
-/
def functorHomMk'
    {obj₁ obj₂ obj₃ : J ⥤ C}
    {mor₁ : obj₁ ⟶ obj₂} {mor₂ : obj₂ ⟶ obj₃} {mor₃ : obj₃ ⟶ obj₁ ⋙ shiftFunctor C (1 : ℤ)}
    {obj₁' obj₂' obj₃' : J ⥤ C}
    {mor₁' : obj₁' ⟶ obj₂'} {mor₂' : obj₂' ⟶ obj₃'}
    {mor₃' : obj₃' ⟶ obj₁' ⋙ shiftFunctor C (1 : ℤ)}
    (hom₁ : obj₁ ⟶ obj₁') (hom₂ : obj₂ ⟶ obj₂') (hom₃ : obj₃ ⟶ obj₃')
    (comm₁ : mor₁ ≫ hom₂ = hom₁ ≫ mor₁')
    (comm₂ : mor₂ ≫ hom₃ = hom₂ ≫ mor₂')
    (comm₃ : mor₃ ≫ whiskerRight hom₁ (shiftFunctor C (1 : ℤ)) = hom₃ ≫ mor₃') :
    functorMk mor₁ mor₂ mor₃ ⟶ functorMk mor₁' mor₂' mor₃' :=
  functorHomMk _ _ hom₁ hom₂ hom₃ comm₁ comm₂ comm₃

set_option backward.isDefEq.respectTransparency false in
/-- Constructor for natural isomorphisms between functors to the
category of triangles. -/
@[simps]
/-
**CategoryTheory.Pretriangulated.Triangle.functorIsoMk** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Pretriangulated.Triangle`。
形式化陈述：functorIsoMk (A B : J ⥤ Triangle C) (iso₁ : A ⋙ π₁ ≅ B ⋙ π₁) (iso₂ : A ⋙ π
₂ ≅ B ⋙ π₂) (iso₃ : A ⋙ π₃ ≅ B ⋙ π₃) (comm₁ : whiskerLeft A π₁Toπ₂ ≫ iso₂.hom = 
iso₁.hom ≫ whiskerLeft B π₁Toπ₂) (comm₂ : whiskerLeft A π₂Toπ₃ ≫ iso₃.hom = iso₂
.hom ≫ whiskerLeft B π₂Toπ₃) (comm₃ : whiskerLeft A π₃Toπ₁ ≫ whiskerRight iso₁.h
om (shiftFunctor C (1 : Int)) = iso₃.hom ≫ whiskerLeft B π₃Toπ₁) : A ≅ B where h
om
参数：A B : J ⥤ Triangle C；iso₁ : A ⋙ π₁ ≅ B ⋙ π₁；iso₂ : A ⋙ π₂ ≅ B ⋙ π₂；iso₃ : A ⋙
 π₃ ≅ B ⋙ π₃；comm₁ : whiskerLeft A π₁Toπ₂ ≫ iso₂.hom = iso₁.hom ≫ whiskerLeft B 
π₁Toπ₂；comm₂ : whiskerLeft A π₂Toπ₃ ≫ iso₃.hom = iso₂.hom ≫ whiskerLeft B π₂Toπ₃
；comm₃ : whiskerLeft A π₃Toπ₁ ≫ whiskerRight iso₁.hom (shiftFunctor C (1 : Int))
 = iso₃.hom ≫ whiskerLeft B π₃Toπ₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for natural isomorphisms between functors to the
category of triangles.
-/
def functorIsoMk (A B : J ⥤ Triangle C) (iso₁ : A ⋙ π₁ ≅ B ⋙ π₁)
    (iso₂ : A ⋙ π₂ ≅ B ⋙ π₂) (iso₃ : A ⋙ π₃ ≅ B ⋙ π₃)
    (comm₁ : whiskerLeft A π₁Toπ₂ ≫ iso₂.hom = iso₁.hom ≫ whiskerLeft B π₁Toπ₂)
    (comm₂ : whiskerLeft A π₂Toπ₃ ≫ iso₃.hom = iso₂.hom ≫ whiskerLeft B π₂Toπ₃)
    (comm₃ : whiskerLeft A π₃Toπ₁ ≫ whiskerRight iso₁.hom (shiftFunctor C (1 : ℤ)) =
      iso₃.hom ≫ whiskerLeft B π₃Toπ₁) : A ≅ B where
  hom := functorHomMk _ _ iso₁.hom iso₂.hom iso₃.hom comm₁ comm₂ comm₃
  inv := functorHomMk _ _ iso₁.inv iso₂.inv iso₃.inv
    (by simp only [← cancel_epi iso₁.hom, ← reassoc_of% comm₁,
          Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc])
    (by simp only [← cancel_epi iso₂.hom, ← reassoc_of% comm₂,
          Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc])
    (by
      simp only [← cancel_epi iso₃.hom, ← reassoc_of% comm₃, Iso.hom_inv_id_assoc,
        ← whiskerRight_comp, Iso.hom_inv_id, whiskerRight_id']
      apply comp_id)

/-- Constructor for natural isomorphisms between functors constructed
with `functorMk`. -/
@[simps!]
/-
**CategoryTheory.Pretriangulated.Triangle.functorIsoMk'** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Pretriangulated.Triangle`。
形式化陈述：functorIsoMk' {obj₁ obj₂ obj₃ : J ⥤ C} {mor₁ : obj₁ ⟶ obj₂} {mor₂ : obj₂ ⟶
 obj₃} {mor₃ : obj₃ ⟶ obj₁ ⋙ shiftFunctor C (1 : Int)} {obj₁' obj₂' obj₃' : J ⥤ 
C} {mor₁' : obj₁' ⟶ obj₂'} {mor₂' : obj₂' ⟶ obj₃'} {mor₃' : obj₃' ⟶ obj₁' ⋙ shif
tFunctor C (1 : Int)} (iso₁ : obj₁ ≅ obj₁') (iso₂ : obj₂ ≅ obj₂') (iso₃ : obj₃ ≅
 obj₃') (comm₁ : mor₁ ≫ iso₂.hom = iso₁.hom ≫ mor₁') (comm₂ : mor₂ ≫ iso₃.hom = 
iso₂.hom ≫ mor₂') (comm₃ : mor₃ ≫ whiskerRight iso₁.hom (shiftFunctor C (1 : Int
)) = iso₃.hom ≫ mor₃') : f
参数：1 : Int；1 : Int；iso₁ : obj₁ ≅ obj₁'；iso₂ : obj₂ ≅ obj₂'；iso₃ : obj₃ ≅ obj₃'；c
omm₁ : mor₁ ≫ iso₂.hom = iso₁.hom ≫ mor₁'；comm₂ : mor₂ ≫ iso₃.hom = iso₂.hom ≫ m
or₂'；comm₃ : mor₃ ≫ whiskerRight iso₁.hom (shiftFunctor C (1 : Int)) = iso₃.hom 
≫ mor₃'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for natural isomorphisms between functors constructed
with `functorMk`.
-/
def functorIsoMk'
    {obj₁ obj₂ obj₃ : J ⥤ C}
    {mor₁ : obj₁ ⟶ obj₂} {mor₂ : obj₂ ⟶ obj₃} {mor₃ : obj₃ ⟶ obj₁ ⋙ shiftFunctor C (1 : ℤ)}
    {obj₁' obj₂' obj₃' : J ⥤ C}
    {mor₁' : obj₁' ⟶ obj₂'} {mor₂' : obj₂' ⟶ obj₃'}
    {mor₃' : obj₃' ⟶ obj₁' ⋙ shiftFunctor C (1 : ℤ)}
    (iso₁ : obj₁ ≅ obj₁') (iso₂ : obj₂ ≅ obj₂') (iso₃ : obj₃ ≅ obj₃')
    (comm₁ : mor₁ ≫ iso₂.hom = iso₁.hom ≫ mor₁')
    (comm₂ : mor₂ ≫ iso₃.hom = iso₂.hom ≫ mor₂')
    (comm₃ : mor₃ ≫ whiskerRight iso₁.hom (shiftFunctor C (1 : ℤ)) = iso₃.hom ≫ mor₃') :
    functorMk mor₁ mor₂ mor₃ ≅ functorMk mor₁' mor₂' mor₃' :=
  functorIsoMk _ _ iso₁ iso₂ iso₃ comm₁ comm₂ comm₃

end

end Triangle

end CategoryTheory.Pretriangulated

