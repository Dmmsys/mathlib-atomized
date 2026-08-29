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
variable (C : Type u) [Category.{v} C] [HasShift C Int]

/-- A triangle in `C` is a sextuple `(X,Y,Z,f,g,h)` where `X,Y,Z` are objects of `C`,
and `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ X⟦1⟧` are morphisms in `C`. -/
@[stacks 0144]
/--
Definition of `Triangle` / `Triangle` 的定义

English:
structure Triangle
  parameters: where mk'
  (no additional axioms)

中文:
结构 Triangle
  参数: where mk'
  (无附加公理)
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
  mor₃ : obj₃ ⟶ obj₁⟦(1 : Int)⟧

variable {C}

/-- A triangle `(X,Y,Z,f,g,h)` in `C` is defined by the morphisms `f : X ⟶ Y`, `g : Y ⟶ Z`
and `h : Z ⟶ X⟦1⟧`.
-/
@[simps]
/--
Definition of `Triangle.mk` / `Triangle.mk` 的定义

English:
definition Triangle.mk
  signature: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : Int)⟧)
  body: X
  obj₂ := Y
  obj₃ := Z
  mor₁ := f
  mor₂ := g
  mor₃ := h

中文:
定义 Triangle.mk
  签名: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : 整数)⟧)
  定义体: X
  obj₂ := Y
  obj₃ := Z
  mor₁ := f
  mor₂ := g
  mor₃ := h
-/
def Triangle.mk {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : Int)⟧) : Triangle C where
  obj₁ := X
  obj₂ := Y
  obj₃ := Z
  mor₁ := f
  mor₂ := g
  mor₃ := h

section

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Triangle C)
  body: ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

中文:
实例 :
  签名: 可居 (Triangle C)
  定义体: ⟨⟨0, 0, 0, 0, 0, 0⟩⟩
-/
instance : Inhabited (Triangle C) :=
  ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

/-- For each object in `C`, there is a triangle of the form `(X,X,0,𝟙 X,0,0)`
-/
@[simps!]
/--
Definition of `contractibleTriangle` / `contractibleTriangle` 的定义

English:
definition contractibleTriangle
  signature: (X : C)
  body: Triangle.mk (𝟙 X) (0 : X ⟶ 0) 0

中文:
定义 contractibleTriangle
  签名: (X : C)
  定义体: Triangle.mk (𝟙 X) (0 : X ⟶ 0) 0

Depends on / 依赖: Triangle, Triangle.mk
-/
def contractibleTriangle (X : C) : Triangle C :=
  Triangle.mk (𝟙 X) (0 : X ⟶ 0) 0

end

/-- A morphism of triangles `(X,Y,Z,f,g,h) ⟶ (X',Y',Z',f',g',h')` in `C` is a triple of morphisms
`a : X ⟶ X'`, `b : Y ⟶ Y'`, `c : Z ⟶ Z'` such that
`a ≫ f' = f ≫ b`, `b ≫ g' = g ≫ c`, and `a⟦1⟧' ≫ h = h' ≫ c`.
In other words, we have a commutative diagram:
```
     f g h
  X ───> Y ───> Z ───> X⟦1⟧
  │ │ │ │
  │a │b │c │a⟦1⟧'
  V V V V
  X' ───> Y' ───> Z' ───> X'⟦1⟧
     f' g' h'
```
-/
@[ext, stacks 0144]
/--
Definition of `TriangleMorphism` / `TriangleMorphism` 的定义

English:
structure TriangleMorphism
  parameters: (T₁ : Triangle C) (T₂ : Triangle C)
  axioms and operations (6):
    - hom₁ : T₁.obj₁ ⟶ T₂.obj₁
    - hom₂ : T₁.obj₂ ⟶ T₂.obj₂
    - hom₃ : T₁.obj₃ ⟶ T₂.obj₃
    - comm₁ : T₁.mor₁ ≫ hom₂ = hom₁ ≫ T₂.mor₁  [default: by cat_disch]
    - comm₂ : T₁.mor₂ ≫ hom₃ = hom₂ ≫ T₂.mor₂  [default: by cat_disch]
    - comm₃ : T₁.mor₃ ≫ hom₁⟦1⟧' = hom₃ ≫ T₂.mor₃  [default: by cat_disch]

中文:
结构 Triangle态射
  参数: (T₁ : Triangle C) (T₂ : Triangle C)
  公理与运算 (6 个):
    - hom₁ : T₁.obj₁ ⟶ T₂.obj₁
    - hom₂ : T₁.obj₂ ⟶ T₂.obj₂
    - hom₃ : T₁.obj₃ ⟶ T₂.obj₃
    - comm₁ : T₁.mor₁ ≫ hom₂ = hom₁ ≫ T₂.mor₁  [默认: by cat_disch]
    - comm₂ : T₁.mor₂ ≫ hom₃ = hom₂ ≫ T₂.mor₂  [默认: by cat_disch]
    - comm₃ : T₁.mor₃ ≫ hom₁⟦1⟧' = hom₃ ≫ T₂.mor₃  [默认: by cat_disch]

Depends on / 依赖: cat_disch
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
/--
Definition of `triangleMorphismId` / `triangleMorphismId` 的定义

English:
definition triangleMorphismId
  signature: (T : Triangle C)
  body: 𝟙 T.obj₁
  hom₂ := 𝟙 T.obj₂
  hom₃ := 𝟙 T.obj₃

中文:
定义 triangleMorphismId
  签名: (T : Triangle C)
  定义体: 𝟙 T.obj₁
  hom₂ := 𝟙 T.obj₂
  hom₃ := 𝟙 T.obj₃

Depends on / 依赖: T.obj
-/
def triangleMorphismId (T : Triangle C) : TriangleMorphism T T where
  hom₁ := 𝟙 T.obj₁
  hom₂ := 𝟙 T.obj₂
  hom₃ := 𝟙 T.obj₃

instance (T : Triangle C) : Inhabited (TriangleMorphism T T) :=
  ⟨triangleMorphismId T⟩

variable {T₁ T₂ T₃ : Triangle C}

/-- Composition of triangle morphisms gives a triangle morphism.
-/
@[simps]
/--
Definition of `TriangleMorphism.comp` / `TriangleMorphism.comp` 的定义

English:
definition TriangleMorphism.comp
  signature: (f : TriangleMorphism T₁ T₂) (g : TriangleMorphism T₂ T₃)
  body: f.hom₁ ≫ g.hom₁
  hom₂ := f.hom₂ ≫ g.hom₂
  hom₃ := f.hom₃ ≫ g.hom₃

中文:
定义 Triangle态射.comp
  签名: (f : Triangle态射 T₁ T₂) (g : Triangle态射 T₂ T₃)
  定义体: f.hom₁ ≫ g.hom₁
  hom₂ := f.hom₂ ≫ g.hom₂
  hom₃ := f.hom₃ ≫ g.hom₃

Depends on / 依赖: f.hom, g.hom
-/
def TriangleMorphism.comp (f : TriangleMorphism T₁ T₂) (g : TriangleMorphism T₂ T₃) :
    TriangleMorphism T₁ T₃ where
  hom₁ := f.hom₁ ≫ g.hom₁
  hom₂ := f.hom₂ ≫ g.hom₂
  hom₃ := f.hom₃ ≫ g.hom₃

/-- Triangles with triangle morphisms form a category.
-/
@[simps]
/--
Instance `triangleCategory` / 实例 `triangleCategory`

English:
instance triangleCategory
  signature: : Category (Triangle C) where
  body: TriangleMorphism A B
  id A := triangleMorphismId A
  comp f g := f.comp g

@[ext]

中文:
实例 triangleCategory
  签名: : 范畴 (Triangle C) where
  定义体: TriangleMorphism A B
  id A := triangleMorphismId A
  comp f g := f.comp g

@[ext]

Depends on / 依赖: TriangleMorphism
-/
instance triangleCategory : Category (Triangle C) where
  Hom A B := TriangleMorphism A B
  id A := triangleMorphismId A
  comp f g := f.comp g

@[ext]
/--
lemma `Triangle.hom_ext` / 引理 `Triangle.hom_ext`

English:
lemma Triangle.hom_ext
  statement: {A B : Triangle C} (f g : A ⟶ B)
  proof: TriangleMorphism.ext h₁ h₂ h₃

中文:
引理 Triangle.hom_ext
  结论: {A B : Triangle C} (f g : A ⟶ B)
  证明: TriangleMorphism.ext h₁ h₂ h₃

Depends on / 依赖: TriangleMorphism, TriangleMorphism.ext
-/
lemma Triangle.hom_ext {A B : Triangle C} (f g : A ⟶ B)
    (h₁ : f.hom₁ = g.hom₁) (h₂ : f.hom₂ = g.hom₂) (h₃ : f.hom₃ = g.hom₃) : f = g :=
  TriangleMorphism.ext h₁ h₂ h₃

/--
lemma `id_hom₁` / 引理 `id_hom₁`

English:
lemma id_hom₁
  given: (A : Triangle C)
  statement: TriangleMorphism.hom₁ (𝟙 A) = 𝟙 _
  proof: rfl

中文:
引理 id_hom₁
  条件: (A : Triangle C)
  结论: Triangle态射.hom₁ (𝟙 A) = 𝟙 _
  证明: rfl
-/
lemma id_hom₁ (A : Triangle C) : TriangleMorphism.hom₁ (𝟙 A) = 𝟙 _ := rfl
/--
lemma `id_hom₂` / 引理 `id_hom₂`

English:
lemma id_hom₂
  given: (A : Triangle C)
  statement: TriangleMorphism.hom₂ (𝟙 A) = 𝟙 _
  proof: rfl

中文:
引理 id_hom₂
  条件: (A : Triangle C)
  结论: Triangle态射.hom₂ (𝟙 A) = 𝟙 _
  证明: rfl
-/
lemma id_hom₂ (A : Triangle C) : TriangleMorphism.hom₂ (𝟙 A) = 𝟙 _ := rfl
/--
lemma `id_hom₃` / 引理 `id_hom₃`

English:
lemma id_hom₃
  given: (A : Triangle C)
  statement: TriangleMorphism.hom₃ (𝟙 A) = 𝟙 _
  proof: rfl

@[reassoc]

中文:
引理 id_hom₃
  条件: (A : Triangle C)
  结论: Triangle态射.hom₃ (𝟙 A) = 𝟙 _
  证明: rfl

@[reassoc]
-/
lemma id_hom₃ (A : Triangle C) : TriangleMorphism.hom₃ (𝟙 A) = 𝟙 _ := rfl

@[reassoc]
/--
lemma `comp_hom₁` / 引理 `comp_hom₁`

English:
lemma comp_hom₁
  given: {X Y Z : Triangle C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl
@[reassoc]

中文:
引理 comp_hom₁
  条件: {X Y Z : Triangle C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
@[reassoc]
-/
lemma comp_hom₁ {X Y Z : Triangle C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom₁ = f.hom₁ ≫ g.hom₁ := rfl
@[reassoc]
/--
lemma `comp_hom₂` / 引理 `comp_hom₂`

English:
lemma comp_hom₂
  given: {X Y Z : Triangle C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl
@[reassoc]

中文:
引理 comp_hom₂
  条件: {X Y Z : Triangle C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
@[reassoc]
-/
lemma comp_hom₂ {X Y Z : Triangle C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom₂ = f.hom₂ ≫ g.hom₂ := rfl
@[reassoc]
/--
lemma `comp_hom₃` / 引理 `comp_hom₃`

English:
lemma comp_hom₃
  given: {X Y Z : Triangle C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 comp_hom₃
  条件: {X Y Z : Triangle C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma comp_hom₃ {X Y Z : Triangle C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom₃ = f.hom₃ ≫ g.hom₃ := rfl

/-- Make a morphism between triangles from the required data. -/
@[simps]
/--
Definition of `Triangle.homMk` / `Triangle.homMk` 的定义

English:
definition Triangle.homMk
  signature: (A B : Triangle C)
  body: hom₁
  hom₂ := hom₂
  hom₃ := hom₃
  comm₁ := comm₁
  comm₂ := comm₂
  comm₃ := comm₃

中文:
定义 Triangle.homMk
  签名: (A B : Triangle C)
  定义体: hom₁
  hom₂ := hom₂
  hom₃ := hom₃
  comm₁ := comm₁
  comm₂ := comm₂
  comm₃ := comm₃

Depends on / 依赖: A.mor, B.mor, cat_disch
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
/--
Definition of `Triangle.isoMk` / `Triangle.isoMk` 的定义

English:
definition Triangle.isoMk
  signature: (A B : Triangle C)
  body: Triangle.homMk _ _ iso₁.hom iso₂.hom iso₃.hom comm₁ comm₂ comm₃
  inv := Triangle.homMk _ _ iso₁.inv iso₂.inv iso₃.inv
    (by simp only [← cancel_mono iso₂.hom, assoc, Iso.inv_hom_id, comp_id,
      comm₁, Iso.inv_hom_id_assoc])
    (by simp only [← cancel_mono iso₃.hom, assoc, Iso.inv_hom_id, comp_id,
      comm₂, Iso.inv_hom_id_assoc])
    (by simp only [← cancel_mono (iso₁.hom⟦(1 : Int)⟧'), Category.assoc, comm₃,
      Iso.inv_hom_id_assoc, ← Functor.map_comp, Iso.inv_hom_id,
      Functor.map_id, Category.comp_id])

中文:
定义 Triangle.isoMk
  签名: (A B : Triangle C)
  定义体: Triangle.homMk _ _ iso₁.hom iso₂.hom iso₃.hom comm₁ comm₂ comm₃
  inv := Triangle.homMk _ _ iso₁.inv iso₂.inv iso₃.inv
    (by simp only [← cancel_mono iso₂.hom, assoc, Iso.inv_hom_id, comp_id,
      comm₁, Iso.inv_hom_id_assoc])
    (by simp only [← cancel_mono iso₃.hom, assoc, Iso.inv_hom_id, comp_id,
      comm₂, Iso.inv_hom_id_assoc])
    (by simp only [← cancel_mono (iso₁.hom⟦(1 : Int)⟧'), Category.assoc, comm₃,
      Iso.inv_hom_id_assoc, ← Functor.map_comp, Iso.inv_hom_id,
      Functor.map_id, Category.comp_id])

Depends on / 依赖: A.mor, B.mor, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Triangle, Triangle.homMk, cancel_mono, cat_disch, comp_id, inv_hom_id, inv_hom_id_assoc
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
    (by simp only [← cancel_mono (iso₁.hom⟦(1 : Int)⟧'), Category.assoc, comm₃,
      Iso.inv_hom_id_assoc, ← Functor.map_comp, Iso.inv_hom_id,
      Functor.map_id, Category.comp_id])

/--
lemma `Triangle.isIso_of_isIsos` / 引理 `Triangle.isIso_of_isIsos`

English:
lemma Triangle.isIso_of_isIsos
  statement: {A B : Triangle C} (f : A ⟶ B)
  proof: by
  let e := Triangle.isoMk A B (asIso f.hom₁) (asIso f.hom₂) (asIso f.hom₃)
    (by simp) (by simp) (by simp)
  exact (inferInstance : IsIso e.hom)

@[reassoc (attr := simp)]

中文:
引理 Triangle.isIso_of_isIsos
  结论: {A B : Triangle C} (f : A ⟶ B)
  证明: by
  let e := Triangle.isoMk A B (asIso f.hom₁) (asIso f.hom₂) (asIso f.hom₃)
    (by simp) (by simp) (by simp)
  exact (inferInstance : IsIso e.hom)

@[reassoc (attr := simp)]

Depends on / 依赖: Triangle, Triangle.isoMk, e.hom, f.hom
-/
lemma Triangle.isIso_of_isIsos {A B : Triangle C} (f : A ⟶ B)
    (h₁ : IsIso f.hom₁) (h₂ : IsIso f.hom₂) (h₃ : IsIso f.hom₃) : IsIso f := by
  let e := Triangle.isoMk A B (asIso f.hom₁) (asIso f.hom₂) (asIso f.hom₃)
    (by simp) (by simp) (by simp)
  exact (inferInstance : IsIso e.hom)

@[reassoc (attr := simp)]
/--
lemma `_root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₁` / 引理 `_root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₁`

English:
lemma _root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₁
  given: {A B : Triangle C} (e : A ≅ B)
  proof: by rw [← comp_hom₁, e.hom_inv_id, id_hom₁]
@[reassoc (attr := simp)]

中文:
引理 _root_.范畴论.同构.hom_inv_id_triangle_hom₁
  条件: {A B : Triangle C} (e : A ≅ B)
  证明: by rw [← comp_hom₁, e.hom_inv_id, id_hom₁]
@[reassoc (attr := simp)]

Depends on / 依赖: e.hom_inv_id, hom_inv_id, reassoc
-/
lemma _root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₁ {A B : Triangle C} (e : A ≅ B) :
    e.hom.hom₁ ≫ e.inv.hom₁ = 𝟙 _ := by rw [← comp_hom₁, e.hom_inv_id, id_hom₁]
@[reassoc (attr := simp)]
/--
lemma `_root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₂` / 引理 `_root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₂`

English:
lemma _root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₂
  given: {A B : Triangle C} (e : A ≅ B)
  proof: by rw [← comp_hom₂, e.hom_inv_id, id_hom₂]
@[reassoc (attr := simp)]

中文:
引理 _root_.范畴论.同构.hom_inv_id_triangle_hom₂
  条件: {A B : Triangle C} (e : A ≅ B)
  证明: by rw [← comp_hom₂, e.hom_inv_id, id_hom₂]
@[reassoc (attr := simp)]

Depends on / 依赖: e.hom_inv_id, hom_inv_id, reassoc
-/
lemma _root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₂ {A B : Triangle C} (e : A ≅ B) :
    e.hom.hom₂ ≫ e.inv.hom₂ = 𝟙 _ := by rw [← comp_hom₂, e.hom_inv_id, id_hom₂]
@[reassoc (attr := simp)]
/--
lemma `_root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₃` / 引理 `_root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₃`

English:
lemma _root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₃
  given: {A B : Triangle C} (e : A ≅ B)
  proof: by rw [← comp_hom₃, e.hom_inv_id, id_hom₃]

@[reassoc (attr := simp)]

中文:
引理 _root_.范畴论.同构.hom_inv_id_triangle_hom₃
  条件: {A B : Triangle C} (e : A ≅ B)
  证明: by rw [← comp_hom₃, e.hom_inv_id, id_hom₃]

@[reassoc (attr := simp)]

Depends on / 依赖: e.hom_inv_id, hom_inv_id
-/
lemma _root_.CategoryTheory.Iso.hom_inv_id_triangle_hom₃ {A B : Triangle C} (e : A ≅ B) :
    e.hom.hom₃ ≫ e.inv.hom₃ = 𝟙 _ := by rw [← comp_hom₃, e.hom_inv_id, id_hom₃]

@[reassoc (attr := simp)]
/--
lemma `_root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₁` / 引理 `_root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₁`

English:
lemma _root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₁
  given: {A B : Triangle C} (e : A ≅ B)
  proof: by rw [← comp_hom₁, e.inv_hom_id, id_hom₁]
@[reassoc (attr := simp)]

中文:
引理 _root_.范畴论.同构.inv_hom_id_triangle_hom₁
  条件: {A B : Triangle C} (e : A ≅ B)
  证明: by rw [← comp_hom₁, e.inv_hom_id, id_hom₁]
@[reassoc (attr := simp)]

Depends on / 依赖: e.inv_hom_id, inv_hom_id, reassoc
-/
lemma _root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₁ {A B : Triangle C} (e : A ≅ B) :
    e.inv.hom₁ ≫ e.hom.hom₁ = 𝟙 _ := by rw [← comp_hom₁, e.inv_hom_id, id_hom₁]
@[reassoc (attr := simp)]
/--
lemma `_root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₂` / 引理 `_root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₂`

English:
lemma _root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₂
  given: {A B : Triangle C} (e : A ≅ B)
  proof: by rw [← comp_hom₂, e.inv_hom_id, id_hom₂]
@[reassoc (attr := simp)]

中文:
引理 _root_.范畴论.同构.inv_hom_id_triangle_hom₂
  条件: {A B : Triangle C} (e : A ≅ B)
  证明: by rw [← comp_hom₂, e.inv_hom_id, id_hom₂]
@[reassoc (attr := simp)]

Depends on / 依赖: e.inv_hom_id, inv_hom_id, reassoc
-/
lemma _root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₂ {A B : Triangle C} (e : A ≅ B) :
    e.inv.hom₂ ≫ e.hom.hom₂ = 𝟙 _ := by rw [← comp_hom₂, e.inv_hom_id, id_hom₂]
@[reassoc (attr := simp)]
/--
lemma `_root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₃` / 引理 `_root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₃`

English:
lemma _root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₃
  given: {A B : Triangle C} (e : A ≅ B)
  proof: by rw [← comp_hom₃, e.inv_hom_id, id_hom₃]

中文:
引理 _root_.范畴论.同构.inv_hom_id_triangle_hom₃
  条件: {A B : Triangle C} (e : A ≅ B)
  证明: by rw [← comp_hom₃, e.inv_hom_id, id_hom₃]

Depends on / 依赖: e.inv_hom_id, inv_hom_id
-/
lemma _root_.CategoryTheory.Iso.inv_hom_id_triangle_hom₃ {A B : Triangle C} (e : A ≅ B) :
    e.inv.hom₃ ≫ e.hom.hom₃ = 𝟙 _ := by rw [← comp_hom₃, e.inv_hom_id, id_hom₃]

/--
lemma `Triangle.eqToHom_hom₁` / 引理 `Triangle.eqToHom_hom₁`

English:
lemma Triangle.eqToHom_hom₁
  given: {A B : Triangle C} (h : A = B)
  proof: by subst h; rfl

中文:
引理 Triangle.eqToHom_hom₁
  条件: {A B : Triangle C} (h : A = B)
  证明: by subst h; rfl
-/
lemma Triangle.eqToHom_hom₁ {A B : Triangle C} (h : A = B) :
    (eqToHom h).hom₁ = eqToHom (by subst h; rfl) := by subst h; rfl
/--
lemma `Triangle.eqToHom_hom₂` / 引理 `Triangle.eqToHom_hom₂`

English:
lemma Triangle.eqToHom_hom₂
  given: {A B : Triangle C} (h : A = B)
  proof: by subst h; rfl

中文:
引理 Triangle.eqToHom_hom₂
  条件: {A B : Triangle C} (h : A = B)
  证明: by subst h; rfl
-/
lemma Triangle.eqToHom_hom₂ {A B : Triangle C} (h : A = B) :
    (eqToHom h).hom₂ = eqToHom (by subst h; rfl) := by subst h; rfl
/--
lemma `Triangle.eqToHom_hom₃` / 引理 `Triangle.eqToHom_hom₃`

English:
lemma Triangle.eqToHom_hom₃
  given: {A B : Triangle C} (h : A = B)
  proof: by subst h; rfl

中文:
引理 Triangle.eqToHom_hom₃
  条件: {A B : Triangle C} (h : A = B)
  证明: by subst h; rfl
-/
lemma Triangle.eqToHom_hom₃ {A B : Triangle C} (h : A = B) :
    (eqToHom h).hom₃ = eqToHom (by subst h; rfl) := by subst h; rfl

namespace Triangle

section Preadditive

variable [Preadditive C] [forall (n : Int), (shiftFunctor C n).Additive]

@[simps (attr := grind =)]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (T₁ ⟶ T₂)
  body: { hom₁ := 0
      hom₂ := 0
      hom₃ := 0 }

@[simps (attr := grind =)]

中文:
实例 :
  签名: 零 (T₁ ⟶ T₂)
  定义体: { hom₁ := 0
      hom₂ := 0
      hom₃ := 0 }

@[simps (attr := grind =)]
-/
instance : Zero (T₁ ⟶ T₂) where
  zero :=
    { hom₁ := 0
      hom₂ := 0
      hom₃ := 0 }

@[simps (attr := grind =)]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (T₁ ⟶ T₂)
  body: { hom₁ := f.hom₁ + g.hom₁
      hom₂ := f.hom₂ + g.hom₂
      hom₃ := f.hom₃ + g.hom₃ }

@[simps (attr := grind =)]

中文:
实例 :
  签名: 加法 (T₁ ⟶ T₂)
  定义体: { hom₁ := f.hom₁ + g.hom₁
      hom₂ := f.hom₂ + g.hom₂
      hom₃ := f.hom₃ + g.hom₃ }

@[simps (attr := grind =)]

Depends on / 依赖: f.hom, g.hom
-/
instance : Add (T₁ ⟶ T₂) where
  add f g :=
    { hom₁ := f.hom₁ + g.hom₁
      hom₂ := f.hom₂ + g.hom₂
      hom₃ := f.hom₃ + g.hom₃ }

@[simps (attr := grind =)]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (T₁ ⟶ T₂)
  body: { hom₁ := -f.hom₁
      hom₂ := -f.hom₂
      hom₃ := -f.hom₃ }

@[simps (attr := grind =)]

中文:
实例 :
  签名: 取负 (T₁ ⟶ T₂)
  定义体: { hom₁ := -f.hom₁
      hom₂ := -f.hom₂
      hom₃ := -f.hom₃ }

@[simps (attr := grind =)]

Depends on / 依赖: f.hom
-/
instance : Neg (T₁ ⟶ T₂) where
  neg f :=
    { hom₁ := -f.hom₁
      hom₂ := -f.hom₂
      hom₃ := -f.hom₃ }

@[simps (attr := grind =)]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (T₁ ⟶ T₂)
  body: { hom₁ := f.hom₁ - g.hom₁
      hom₂ := f.hom₂ - g.hom₂
      hom₃ := f.hom₃ - g.hom₃ }

中文:
实例 :
  签名: 减法 (T₁ ⟶ T₂)
  定义体: { hom₁ := f.hom₁ - g.hom₁
      hom₂ := f.hom₂ - g.hom₂
      hom₃ := f.hom₃ - g.hom₃ }

Depends on / 依赖: f.hom, g.hom
-/
instance : Sub (T₁ ⟶ T₂) where
  sub f g :=
    { hom₁ := f.hom₁ - g.hom₁
      hom₂ := f.hom₂ - g.hom₂
      hom₃ := f.hom₃ - g.hom₃ }

section

variable {R : Type*} [Semiring R] [Linear R C]
  [forall (n : Int), Functor.Linear R (shiftFunctor C n)]

@[simps (attr := grind =)]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R (T₁ ⟶ T₂)
  body: { hom₁ := n • f.hom₁
      hom₂ := n • f.hom₂
      hom₃ := n • f.hom₃ }

omit [forall (n : Int), (shiftFunctor C n).Additive]

中文:
实例 :
  签名: 标量乘法 R (T₁ ⟶ T₂)
  定义体: { hom₁ := n • f.hom₁
      hom₂ := n • f.hom₂
      hom₃ := n • f.hom₃ }

omit [forall (n : Int), (shiftFunctor C n).Additive]

Depends on / 依赖: f.hom
-/
instance : SMul R (T₁ ⟶ T₂) where
  smul n f :=
    { hom₁ := n • f.hom₁
      hom₂ := n • f.hom₂
      hom₃ := n • f.hom₃ }

omit [forall (n : Int), (shiftFunctor C n).Additive]

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (T₁ ⟶ T₂)
  body: by ext <;> apply zero_add
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

中文:
实例 :
  签名: 加法交换群 (T₁ ⟶ T₂)
  定义体: by ext <;> apply zero_add
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

Depends on / 依赖: AddMonoid, AddMonoid.nsmul_succ, SubNegMonoid, SubNegMonoid.zsmul_neg, SubNegMonoid.zsmul_succ, add_assoc, add_comm, add_zero, cat_disch, neg_add_cancel, nsmul_succ, nsmul_zero, sub_eq_add_neg, zero_add, zsmul_neg, zsmul_succ, zsmul_zero
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (Triangle C)

中文:
实例 :
  签名: 预加性 (Triangle C)
-/
instance : Preadditive (Triangle C) where

end Preadditive

section Linear

variable [Preadditive C] {R : Type*} [Semiring R] [Linear R C]
  [forall (n : Int), (shiftFunctor C n).Additive]
  [forall (n : Int), Functor.Linear R (shiftFunctor C n)]

attribute [local simp] mul_smul add_smul in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (T₁ ⟶ T₂)
  body: by aesop
  mul_smul := by aesop
  smul_zero := by aesop
  smul_add := by aesop
  add_smul := by aesop
  zero_smul := by aesop

中文:
实例 :
  签名: 模 R (T₁ ⟶ T₂)
  定义体: by aesop
  mul_smul := by aesop
  smul_zero := by aesop
  smul_add := by aesop
  add_smul := by aesop
  zero_smul := by aesop

Depends on / 依赖: add_smul, mul_smul, smul_add, smul_zero, zero_smul
-/
instance : Module R (T₁ ⟶ T₂) where
  one_smul := by aesop
  mul_smul := by aesop
  smul_zero := by aesop
  smul_add := by aesop
  add_smul := by aesop
  zero_smul := by aesop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Linear R (Triangle C)

中文:
实例 :
  签名: 线性 R (Triangle C)
-/
instance : Linear R (Triangle C) where

end Linear

end Triangle

/-- The obvious triangle `X₁ ⟶ X₁ ⊞ X₂ ⟶ X₂ ⟶ X₁⟦1⟧`. -/
@[simps!]
/--
Definition of `binaryBiproductTriangle` / `binaryBiproductTriangle` 的定义

English:
definition binaryBiproductTriangle
  signature: (X₁ X₂ : C) [HasZeroMorphisms C] [HasBinaryBiproduct X₁ X₂]
  body: Triangle.mk biprod.inl (Limits.biprod.snd : X₁ ⊞ X₂ ⟶ _) 0

中文:
定义 binaryBiproductTriangle
  签名: (X₁ X₂ : C) [有ZeroMorphisms C] [有BinaryBiproduct X₁ X₂]
  定义体: Triangle.mk biprod.inl (Limits.biprod.snd : X₁ ⊞ X₂ ⟶ _) 0

Depends on / 依赖: Limits, Limits.biprod.snd, Triangle, Triangle.mk, biprod, biprod.inl
-/
def binaryBiproductTriangle (X₁ X₂ : C) [HasZeroMorphisms C] [HasBinaryBiproduct X₁ X₂] :
    Triangle C :=
  Triangle.mk biprod.inl (Limits.biprod.snd : X₁ ⊞ X₂ ⟶ _) 0

/-- The obvious triangle `X₁ ⟶ X₁ ⨯ X₂ ⟶ X₂ ⟶ X₁⟦1⟧`. -/
@[simps!]
/--
Definition of `binaryProductTriangle` / `binaryProductTriangle` 的定义

English:
definition binaryProductTriangle
  signature: (X₁ X₂ : C) [HasZeroMorphisms C] [HasBinaryProduct X₁ X₂]
  body: Triangle.mk ((Limits.prod.lift (𝟙 X₁) 0)) (Limits.prod.snd : X₁ ⨯ X₂ ⟶ _) 0

中文:
定义 binaryProductTriangle
  签名: (X₁ X₂ : C) [有ZeroMorphisms C] [HasBinaryProduct X₁ X₂]
  定义体: Triangle.mk ((Limits.prod.lift (𝟙 X₁) 0)) (Limits.prod.snd : X₁ ⨯ X₂ ⟶ _) 0

Depends on / 依赖: Limits, Limits.prod.lift, Limits.prod.snd, Triangle, Triangle.mk
-/
def binaryProductTriangle (X₁ X₂ : C) [HasZeroMorphisms C] [HasBinaryProduct X₁ X₂] :
    Triangle C :=
  Triangle.mk ((Limits.prod.lift (𝟙 X₁) 0)) (Limits.prod.snd : X₁ ⨯ X₂ ⟶ _) 0

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism of triangles
`binaryProductTriangle X₁ X₂ ≅ binaryBiproductTriangle X₁ X₂`. -/
@[simps!]
/--
Definition of `binaryProductTriangleIsoBinaryBiproductTriangle` / `binaryProductTriangleIsoBinaryBiproductTriangle` 的定义

English:
definition binaryProductTriangleIsoBinaryBiproductTriangle
  body: Triangle.isoMk _ _ (Iso.refl _) (biprod.isoProd X₁ X₂).symm (Iso.refl _)
    (by cat_disch) (by simp) (by simp)

中文:
定义 binaryProductTriangleIsoBinaryBiproductTriangle
  定义体: Triangle.isoMk _ _ (Iso.refl _) (biprod.isoProd X₁ X₂).symm (Iso.refl _)
    (by cat_disch) (by simp) (by simp)

Depends on / 依赖: Iso.refl, Triangle, Triangle.isoMk, biprod, biprod.isoProd, cat_disch, isoProd
-/
def binaryProductTriangleIsoBinaryBiproductTriangle
    (X₁ X₂ : C) [HasZeroMorphisms C] [HasBinaryBiproduct X₁ X₂] :
    binaryProductTriangle X₁ X₂ ≅ binaryBiproductTriangle X₁ X₂ :=
  Triangle.isoMk _ _ (Iso.refl _) (biprod.isoProd X₁ X₂).symm (Iso.refl _)
    (by cat_disch) (by simp) (by simp)

section

variable {J : Type*} (T : J -> Triangle C)
  [HasProduct (fun j => (T j).obj₁)] [HasProduct (fun j => (T j).obj₂)]
  [HasProduct (fun j => (T j).obj₃)] [HasProduct (fun j => (T j).obj₁⟦(1 : Int)⟧)]

/-- The product of a family of triangles. -/
@[simps!]
/--
Definition of `productTriangle` / `productTriangle` 的定义

English:
definition productTriangle
  signature: : Triangle C
  body: Triangle.mk (Limits.Pi.map (fun j => (T j).mor₁))
    (Limits.Pi.map (fun j => (T j).mor₂))
    (Limits.Pi.map (fun j => (T j).mor₃) ≫ inv (piComparison _ _))

中文:
定义 productTriangle
  签名: : Triangle C
  定义体: Triangle.mk (Limits.Pi.map (fun j => (T j).mor₁))
    (Limits.Pi.map (fun j => (T j).mor₂))
    (Limits.Pi.map (fun j => (T j).mor₃) ≫ inv (piComparison _ _))

Depends on / 依赖: Limits, Limits.Pi.map, Triangle, Triangle.mk, piComparison
-/
def productTriangle : Triangle C :=
  Triangle.mk (Limits.Pi.map (fun j => (T j).mor₁))
    (Limits.Pi.map (fun j => (T j).mor₂))
    (Limits.Pi.map (fun j => (T j).mor₃) ≫ inv (piComparison _ _))

set_option backward.defeqAttrib.useBackward true in
/-- A projection from the product of a family of triangles. -/
@[simps]
/--
Definition of `productTriangle.π` / `productTriangle.π` 的定义

English:
definition productTriangle.π
  signature: (j : J)
  body: Pi.π _ j
  hom₂ := Pi.π _ j
  hom₃ := Pi.π _ j

中文:
定义 productTriangle.π
  签名: (j : J)
  定义体: Pi.π _ j
  hom₂ := Pi.π _ j
  hom₃ := Pi.π _ j
-/
def productTriangle.π (j : J) :
    productTriangle T ⟶ T j where
  hom₁ := Pi.π _ j
  hom₂ := Pi.π _ j
  hom₃ := Pi.π _ j

/-- The fan given by `productTriangle T`. -/
@[simp]
/--
Definition of `productTriangle.fan` / `productTriangle.fan` 的定义

English:
definition productTriangle.fan
  signature: : Fan T
  body: Fan.mk (productTriangle T) (productTriangle.π T)

中文:
定义 productTriangle.fan
  签名: : Fan T
  定义体: Fan.mk (productTriangle T) (productTriangle.π T)

Depends on / 依赖: Fan.mk, productTriangle
-/
def productTriangle.fan : Fan T := Fan.mk (productTriangle T) (productTriangle.π T)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A family of morphisms `T' ⟶ T j` lifts to a morphism `T' ⟶ productTriangle T`. -/
@[simps]
/--
Definition of `productTriangle.lift` / `productTriangle.lift` 的定义

English:
definition productTriangle.lift
  signature: {T' : Triangle C} (φ : forall j, T' ⟶ T j)
  body: Pi.lift (fun j => (φ j).hom₁)
  hom₂ := Pi.lift (fun j => (φ j).hom₂)
  hom₃ := Pi.lift (fun j => (φ j).hom₃)
  comm₃ := by
    dsimp
    rw [← cancel_mono (piComparison _ _)]; rw [assoc]; rw [assoc]; rw [assoc]; rw [IsIso.inv_hom_id]; rw [comp_id]
    cat_disch

中文:
定义 productTriangle.lift
  签名: {T' : Triangle C} (φ : 对任意 j, T' ⟶ T j)
  定义体: Pi.lift (fun j => (φ j).hom₁)
  hom₂ := Pi.lift (fun j => (φ j).hom₂)
  hom₃ := Pi.lift (fun j => (φ j).hom₃)
  comm₃ := by
    dsimp
    rw [← cancel_mono (piComparison _ _)]; rw [assoc]; rw [assoc]; rw [assoc]; rw [IsIso.inv_hom_id]; rw [comp_id]
    cat_disch

Depends on / 依赖: Pi.lift
-/
def productTriangle.lift {T' : Triangle C} (φ : forall j, T' ⟶ T j) :
    T' ⟶ productTriangle T where
  hom₁ := Pi.lift (fun j => (φ j).hom₁)
  hom₂ := Pi.lift (fun j => (φ j).hom₂)
  hom₃ := Pi.lift (fun j => (φ j).hom₃)
  comm₃ := by
    dsimp
    rw [← cancel_mono (piComparison _ _)]; rw [assoc]; rw [assoc]; rw [assoc]; rw [IsIso.inv_hom_id]; rw [comp_id]
    cat_disch

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `productTriangle.isLimitFan` / `productTriangle.isLimitFan` 的定义

English:
definition productTriangle.isLimitFan
  signature: : IsLimit (productTriangle.fan T)
  body: Fan.IsLimit.mk _ (fun s => productTriangle.lift T s.proj) (fun s j => by cat_disch) (by
    intro s m hm
    ext1
    all_goals
      exact Pi.hom_ext _ _ (fun j => (by simp [← hm])))

中文:
定义 productTriangle.isLimitFan
  签名: : 是极限 (productTriangle.fan T)
  定义体: Fan.IsLimit.mk _ (fun s => productTriangle.lift T s.proj) (fun s j => by cat_disch) (by
    intro s m hm
    ext1
    all_goals
      exact Pi.hom_ext _ _ (fun j => (by simp [← hm])))

Depends on / 依赖: Fan.IsLimit.mk, IsLimit, Pi.hom_ext, all_goals, cat_disch, hom_ext, productTriangle, productTriangle.lift, s.proj
-/
def productTriangle.isLimitFan : IsLimit (productTriangle.fan T) :=
  Fan.IsLimit.mk _ (fun s => productTriangle.lift T s.proj) (fun s j => by cat_disch) (by
    intro s m hm
    ext1
    all_goals
      exact Pi.hom_ext _ _ (fun j => (by simp [← hm])))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `productTriangle.zero₃₁` / 引理 `productTriangle.zero₃₁`

English:
lemma productTriangle.zero₃₁
  statement: [HasZeroMorphisms C]
  proof: by
  have : HasProduct (fun j => (T j).obj₂⟦(1 : Int)⟧) :=
    ⟨_, isLimitFanMkObjOfIsLimit (shiftFunctor C (1 : Int)) _ _
      (productIsProduct (fun j => (T j).obj₂))⟩
  dsimp
  change _ ≫ (Pi.lift (fun j => Pi.π _ j ≫ (T j).mor₁))⟦(1 : Int)⟧' = 0
  rw [assoc]; rw [← cancel_mono (piComparison _ _)]; rw [zero_comp]; rw [assoc]; rw [assoc]
  ext j
  simp [h j]

中文:
引理 productTriangle.zero₃₁
  结论: [有ZeroMorphisms C]
  证明: by
  have : HasProduct (fun j => (T j).obj₂⟦(1 : Int)⟧) :=
    ⟨_, isLimitFanMkObjOfIsLimit (shiftFunctor C (1 : Int)) _ _
      (productIsProduct (fun j => (T j).obj₂))⟩
  dsimp
  change _ ≫ (Pi.lift (fun j => Pi.π _ j ≫ (T j).mor₁))⟦(1 : Int)⟧' = 0
  rw [assoc]; rw [← cancel_mono (piComparison _ _)]; rw [zero_comp]; rw [assoc]; rw [assoc]
  ext j
  simp [h j]

Depends on / 依赖: HasProduct, Pi.lift, cancel_mono, isLimitFanMkObjOfIsLimit, piComparison, productIsProduct, shiftFunctor, zero_comp
-/
lemma productTriangle.zero₃₁ [HasZeroMorphisms C]
    (h : forall j, (T j).mor₃ ≫ (T j).mor₁⟦(1 : Int)⟧' = 0) :
    (productTriangle T).mor₃ ≫ (productTriangle T).mor₁⟦1⟧' = 0 := by
  have : HasProduct (fun j => (T j).obj₂⟦(1 : Int)⟧) :=
    ⟨_, isLimitFanMkObjOfIsLimit (shiftFunctor C (1 : Int)) _ _
      (productIsProduct (fun j => (T j).obj₂))⟩
  dsimp
  change _ ≫ (Pi.lift (fun j => Pi.π _ j ≫ (T j).mor₁))⟦(1 : Int)⟧' = 0
  rw [assoc]; rw [← cancel_mono (piComparison _ _)]; rw [zero_comp]; rw [assoc]; rw [assoc]
  ext j
  simp [h j]

end

set_option backward.defeqAttrib.useBackward true in
variable (C) in
/-- The functor `C ⥤ Triangle C` which sends `X` to `contractibleTriangle X`. -/
@[simps]
/--
Definition of `contractibleTriangleFunctor` / `contractibleTriangleFunctor` 的定义

English:
definition contractibleTriangleFunctor
  signature: [HasZeroObject C] [HasZeroMorphisms C]
  body: contractibleTriangle X
  map f :=
    { hom₁ := f
      hom₂ := f
      hom₃ := 0 }

中文:
定义 contractibleTriangleFunctor
  签名: [有ZeroObject C] [有ZeroMorphisms C]
  定义体: contractibleTriangle X
  map f :=
    { hom₁ := f
      hom₂ := f
      hom₃ := 0 }

Depends on / 依赖: contractibleTriangle
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
/--
Definition of `π₁` / `π₁` 的定义

English:
definition π₁
  signature: : Triangle C ⥤ C where
  body: T.obj₁
  map f := f.hom₁

中文:
定义 π₁
  签名: : Triangle C ⥤ C where
  定义体: T.obj₁
  map f := f.hom₁

Depends on / 依赖: T.obj
-/
def π₁ : Triangle C ⥤ C where
  obj T := T.obj₁
  map f := f.hom₁

/-- The second projection `Triangle C ⥤ C`. -/
@[simps]
/--
Definition of `π₂` / `π₂` 的定义

English:
definition π₂
  signature: : Triangle C ⥤ C where
  body: T.obj₂
  map f := f.hom₂

中文:
定义 π₂
  签名: : Triangle C ⥤ C where
  定义体: T.obj₂
  map f := f.hom₂

Depends on / 依赖: T.obj, isFalse, isTrue
-/
def π₂ : Triangle C ⥤ C where
  obj T := T.obj₂
  map f := f.hom₂

/-- The third projection `Triangle C ⥤ C`. -/
@[simps]
/--
Definition of `π₃` / `π₃` 的定义

English:
definition π₃
  signature: : Triangle C ⥤ C where
  body: T.obj₃
  map f := f.hom₃

中文:
定义 π₃
  签名: : Triangle C ⥤ C where
  定义体: T.obj₃
  map f := f.hom₃

Depends on / 依赖: T.obj
-/
def π₃ : Triangle C ⥤ C where
  obj T := T.obj₃
  map f := f.hom₃

set_option backward.defeqAttrib.useBackward true in
/-- The first morphism of a triangle, as a natural transformation `π₁ ⟶ π₂`. -/
@[simps]
/--
Definition of `π₁Toπ₂` / `π₁Toπ₂` 的定义

English:
definition π₁Toπ₂
  signature: : (π₁ : Triangle C ⥤ C) ⟶ Triangle.π₂ where
  body: T.mor₁

中文:
定义 π₁Toπ₂
  签名: : (π₁ : Triangle C ⥤ C) ⟶ Triangle.π₂ where
  定义体: T.mor₁

Depends on / 依赖: T.mor
-/
def π₁Toπ₂ : (π₁ : Triangle C ⥤ C) ⟶ Triangle.π₂ where
  app T := T.mor₁

set_option backward.defeqAttrib.useBackward true in
/-- The second morphism of a triangle, as a natural transformation `π₂ ⟶ π₃`. -/
@[simps]
/--
Definition of `π₂Toπ₃` / `π₂Toπ₃` 的定义

English:
definition π₂Toπ₃
  signature: : (π₂ : Triangle C ⥤ C) ⟶ Triangle.π₃ where
  body: T.mor₂

中文:
定义 π₂Toπ₃
  签名: : (π₂ : Triangle C ⥤ C) ⟶ Triangle.π₃ where
  定义体: T.mor₂

Depends on / 依赖: T.mor
-/
def π₂Toπ₃ : (π₂ : Triangle C ⥤ C) ⟶ Triangle.π₃ where
  app T := T.mor₂

set_option backward.defeqAttrib.useBackward true in
/-- The third morphism of a triangle, as a natural
transformation `π₃ ⟶ π₁ ⋙ shiftFunctor _ (1 : ℤ)`. -/
@[simps]
/--
Definition of `π₃Toπ₁` / `π₃Toπ₁` 的定义

English:
definition π₃Toπ₁
  signature: : (π₃ : Triangle C ⥤ C) ⟶ π₁ ⋙ shiftFunctor C (1 : Int) where
  body: T.mor₃

中文:
定义 π₃Toπ₁
  签名: : (π₃ : Triangle C ⥤ C) ⟶ π₁ ⋙ shiftFunctor C (1 : 整数) where
  定义体: T.mor₃

Depends on / 依赖: T.mor
-/
def π₃Toπ₁ : (π₃ : Triangle C ⥤ C) ⟶ π₁ ⋙ shiftFunctor C (1 : Int) where
  app T := T.mor₃

section

variable {A B : Triangle C} (φ : A ⟶ B) [IsIso φ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso φ.hom₁
  body: (inferInstance : IsIso (π₁.map φ))

中文:
实例 :
  签名: 是同构 φ.hom₁
  定义体: (inferInstance : IsIso (π₁.map φ))
-/
instance : IsIso φ.hom₁ := (inferInstance : IsIso (π₁.map φ))
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso φ.hom₂
  body: (inferInstance : IsIso (π₂.map φ))

中文:
实例 :
  签名: 是同构 φ.hom₂
  定义体: (inferInstance : IsIso (π₂.map φ))
-/
instance : IsIso φ.hom₂ := (inferInstance : IsIso (π₂.map φ))
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso φ.hom₃
  body: (inferInstance : IsIso (π₃.map φ))

中文:
实例 :
  签名: 是同构 φ.hom₃
  定义体: (inferInstance : IsIso (π₃.map φ))
-/
instance : IsIso φ.hom₃ := (inferInstance : IsIso (π₃.map φ))

end

section

open CategoryTheory.Functor

variable {J : Type*} [Category* J]

set_option backward.isDefEq.respectTransparency false in
/-- Constructor for functors to the category of triangles. -/
@[simps]
/--
Definition of `functorMk` / `functorMk` 的定义

English:
definition functorMk
  signature: {obj₁ obj₂ obj₃ : J ⥤ C}
  body: mk (mor₁.app j) (mor₂.app j) (mor₃.app j)
  map φ :=
    { hom₁ := obj₁.map φ
      hom₂ := obj₂.map φ
      hom₃ := obj₃.map φ }

中文:
定义 functorMk
  签名: {obj₁ obj₂ obj₃ : J ⥤ C}
  定义体: mk (mor₁.app j) (mor₂.app j) (mor₃.app j)
  map φ :=
    { hom₁ := obj₁.map φ
      hom₂ := obj₂.map φ
      hom₃ := obj₃.map φ }
-/
def functorMk {obj₁ obj₂ obj₃ : J ⥤ C}
    (mor₁ : obj₁ ⟶ obj₂) (mor₂ : obj₂ ⟶ obj₃) (mor₃ : obj₃ ⟶ obj₁ ⋙ shiftFunctor C (1 : Int)) :
    J ⥤ Triangle C where
  obj j := mk (mor₁.app j) (mor₂.app j) (mor₃.app j)
  map φ :=
    { hom₁ := obj₁.map φ
      hom₂ := obj₂.map φ
      hom₃ := obj₃.map φ }

/-- Constructor for natural transformations between functors to the
category of triangles. -/
@[simps]
/--
Definition of `functorHomMk` / `functorHomMk` 的定义

English:
definition functorHomMk
  signature: (A B : J ⥤ Triangle C) (hom₁ : A ⋙ π₁ ⟶ B ⋙ π₁)
  body: { hom₁ := hom₁.app j
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

中文:
定义 functorHomMk
  签名: (A B : J ⥤ Triangle C) (hom₁ : A ⋙ π₁ ⟶ B ⋙ π₁)
  定义体: { hom₁ := hom₁.app j
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

Depends on / 依赖: NatTrans, NatTrans.congr_app, cat_disch, congr_app, naturality, shiftFunctor, whiskerLeft, whiskerRight
-/
def functorHomMk (A B : J ⥤ Triangle C) (hom₁ : A ⋙ π₁ ⟶ B ⋙ π₁)
    (hom₂ : A ⋙ π₂ ⟶ B ⋙ π₂) (hom₃ : A ⋙ π₃ ⟶ B ⋙ π₃)
    (comm₁ : whiskerLeft A π₁Toπ₂ ≫ hom₂ = hom₁ ≫ whiskerLeft B π₁Toπ₂ := by cat_disch)
    (comm₂ : whiskerLeft A π₂Toπ₃ ≫ hom₃ = hom₂ ≫ whiskerLeft B π₂Toπ₃ := by cat_disch)
    (comm₃ : whiskerLeft A π₃Toπ₁ ≫ whiskerRight hom₁ (shiftFunctor C (1 : Int)) =
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
/--
Definition of `functorHomMk'` / `functorHomMk'` 的定义

English:
definition functorHomMk'
  body: functorHomMk _ _ hom₁ hom₂ hom₃ comm₁ comm₂ comm₃

中文:
定义 functorHomMk'
  定义体: functorHomMk _ _ hom₁ hom₂ hom₃ comm₁ comm₂ comm₃

Depends on / 依赖: functorHomMk
-/
def functorHomMk'
    {obj₁ obj₂ obj₃ : J ⥤ C}
    {mor₁ : obj₁ ⟶ obj₂} {mor₂ : obj₂ ⟶ obj₃} {mor₃ : obj₃ ⟶ obj₁ ⋙ shiftFunctor C (1 : Int)}
    {obj₁' obj₂' obj₃' : J ⥤ C}
    {mor₁' : obj₁' ⟶ obj₂'} {mor₂' : obj₂' ⟶ obj₃'}
    {mor₃' : obj₃' ⟶ obj₁' ⋙ shiftFunctor C (1 : Int)}
    (hom₁ : obj₁ ⟶ obj₁') (hom₂ : obj₂ ⟶ obj₂') (hom₃ : obj₃ ⟶ obj₃')
    (comm₁ : mor₁ ≫ hom₂ = hom₁ ≫ mor₁')
    (comm₂ : mor₂ ≫ hom₃ = hom₂ ≫ mor₂')
    (comm₃ : mor₃ ≫ whiskerRight hom₁ (shiftFunctor C (1 : Int)) = hom₃ ≫ mor₃') :
    functorMk mor₁ mor₂ mor₃ ⟶ functorMk mor₁' mor₂' mor₃' :=
  functorHomMk _ _ hom₁ hom₂ hom₃ comm₁ comm₂ comm₃

set_option backward.isDefEq.respectTransparency false in
/-- Constructor for natural isomorphisms between functors to the
category of triangles. -/
@[simps]
/--
Definition of `functorIsoMk` / `functorIsoMk` 的定义

English:
definition functorIsoMk
  signature: (A B : J ⥤ Triangle C) (iso₁ : A ⋙ π₁ ≅ B ⋙ π₁)
  body: functorHomMk _ _ iso₁.hom iso₂.hom iso₃.hom comm₁ comm₂ comm₃
  inv := functorHomMk _ _ iso₁.inv iso₂.inv iso₃.inv
    (by simp only [← cancel_epi iso₁.hom, ← reassoc_of% comm₁,
          Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc])
    (by simp only [← cancel_epi iso₂.hom, ← reassoc_of% comm₂,
          Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc])
    (by
      simp only [← cancel_epi iso₃.hom, ← reassoc_of% comm₃, Iso.hom_inv_id_assoc,
        ← whiskerRight_comp, Iso.hom_inv_id, whiskerRight_id']
      apply comp_id)

中文:
定义 functorIsoMk
  签名: (A B : J ⥤ Triangle C) (iso₁ : A ⋙ π₁ ≅ B ⋙ π₁)
  定义体: functorHomMk _ _ iso₁.hom iso₂.hom iso₃.hom comm₁ comm₂ comm₃
  inv := functorHomMk _ _ iso₁.inv iso₂.inv iso₃.inv
    (by simp only [← cancel_epi iso₁.hom, ← reassoc_of% comm₁,
          Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc])
    (by simp only [← cancel_epi iso₂.hom, ← reassoc_of% comm₂,
          Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc])
    (by
      simp only [← cancel_epi iso₃.hom, ← reassoc_of% comm₃, Iso.hom_inv_id_assoc,
        ← whiskerRight_comp, Iso.hom_inv_id, whiskerRight_id']
      apply comp_id)

Depends on / 依赖: functorHomMk
-/
def functorIsoMk (A B : J ⥤ Triangle C) (iso₁ : A ⋙ π₁ ≅ B ⋙ π₁)
    (iso₂ : A ⋙ π₂ ≅ B ⋙ π₂) (iso₃ : A ⋙ π₃ ≅ B ⋙ π₃)
    (comm₁ : whiskerLeft A π₁Toπ₂ ≫ iso₂.hom = iso₁.hom ≫ whiskerLeft B π₁Toπ₂)
    (comm₂ : whiskerLeft A π₂Toπ₃ ≫ iso₃.hom = iso₂.hom ≫ whiskerLeft B π₂Toπ₃)
    (comm₃ : whiskerLeft A π₃Toπ₁ ≫ whiskerRight iso₁.hom (shiftFunctor C (1 : Int)) =
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
/--
Definition of `functorIsoMk'` / `functorIsoMk'` 的定义

English:
definition functorIsoMk'
  body: functorIsoMk _ _ iso₁ iso₂ iso₃ comm₁ comm₂ comm₃

中文:
定义 functorIsoMk'
  定义体: functorIsoMk _ _ iso₁ iso₂ iso₃ comm₁ comm₂ comm₃

Depends on / 依赖: functorIsoMk
-/
def functorIsoMk'
    {obj₁ obj₂ obj₃ : J ⥤ C}
    {mor₁ : obj₁ ⟶ obj₂} {mor₂ : obj₂ ⟶ obj₃} {mor₃ : obj₃ ⟶ obj₁ ⋙ shiftFunctor C (1 : Int)}
    {obj₁' obj₂' obj₃' : J ⥤ C}
    {mor₁' : obj₁' ⟶ obj₂'} {mor₂' : obj₂' ⟶ obj₃'}
    {mor₃' : obj₃' ⟶ obj₁' ⋙ shiftFunctor C (1 : Int)}
    (iso₁ : obj₁ ≅ obj₁') (iso₂ : obj₂ ≅ obj₂') (iso₃ : obj₃ ≅ obj₃')
    (comm₁ : mor₁ ≫ iso₂.hom = iso₁.hom ≫ mor₁')
    (comm₂ : mor₂ ≫ iso₃.hom = iso₂.hom ≫ mor₂')
    (comm₃ : mor₃ ≫ whiskerRight iso₁.hom (shiftFunctor C (1 : Int)) = iso₃.hom ≫ mor₃') :
    functorMk mor₁ mor₂ mor₃ ≅ functorMk mor₁' mor₂' mor₃' :=
  functorIsoMk _ _ iso₁ iso₂ iso₃ comm₁ comm₂ comm₃

end

end Triangle

end CategoryTheory.Pretriangulated
