/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Short complexes

This file defines the category `ShortComplex C` of diagrams
`X₁ ⟶ X₂ ⟶ X₃` such that the composition is zero.

Note: This structure `ShortComplex C` was first introduced in
the Liquid Tensor Experiment.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]

variable (C) in
/-- A short complex in a category `C` with zero morphisms is the datum
of two composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such that
`f ≫ g = 0`. -/
/-
**CategoryTheory.ShortComplex** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：ShortComplex where /-- the first (left) object of a `ShortComplex` -/ {X₁ 
: C} /-- the second (middle) object of a `ShortComplex` -/ {X₂ : C} /-- the thir
d (right) object of a `ShortComplex` -/ {X₃ : C} /-- the first morphism of a `Sh
ortComplex` -/ f : X₁ ⟶ X₂ /-- the second morphism of a `ShortComplex` -/ g : X₂
 ⟶ X₃ /-- the composition of the two given morphisms is zero -/ zero : f ≫ g = 0
参数：left；middle；right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A short complex in a category `C` with zero morphisms is the datum
of two composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such that
`f ≫ g = 0`.
-/
structure ShortComplex where
  /-- the first (left) object of a `ShortComplex` -/
  {X₁ : C}
  /-- the second (middle) object of a `ShortComplex` -/
  {X₂ : C}
  /-- the third (right) object of a `ShortComplex` -/
  {X₃ : C}
  /-- the first morphism of a `ShortComplex` -/
  f : X₁ ⟶ X₂
  /-- the second morphism of a `ShortComplex` -/
  g : X₂ ⟶ X₃
  /-- the composition of the two given morphisms is zero -/
  zero : f ≫ g = 0 := by cat_disch

namespace ShortComplex

attribute [reassoc (attr := simp)] ShortComplex.zero

/-- Morphisms of short complexes are the commutative diagrams of the obvious shape. -/
@[ext]
/-
**CategoryTheory.ShortComplex.Hom** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Shor
tComplex`。
形式化陈述：Hom (S₁ S₂ : ShortComplex C) where /-- the morphism on the left objects -/
 τ₁ : S₁.X₁ ⟶ S₂.X₁ /-- the morphism on the middle objects -/ τ₂ : S₁.X₂ ⟶ S₂.X₂
 /-- the morphism on the right objects -/ τ₃ : S₁.X₃ ⟶ S₂.X₃ /-- the left commut
ative square of a morphism in `ShortComplex` -/ comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂
参数：S₁ S₂ : ShortComplex C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms of short complexes are the commutative diagrams of the obvious shape.
-/
structure Hom (S₁ S₂ : ShortComplex C) where
  /-- the morphism on the left objects -/
  τ₁ : S₁.X₁ ⟶ S₂.X₁
  /-- the morphism on the middle objects -/
  τ₂ : S₁.X₂ ⟶ S₂.X₂
  /-- the morphism on the right objects -/
  τ₃ : S₁.X₃ ⟶ S₂.X₃
  /-- the left commutative square of a morphism in `ShortComplex` -/
  comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂ := by cat_disch
  /-- the right commutative square of a morphism in `ShortComplex` -/
  comm₂₃ : τ₂ ≫ S₂.g = S₁.g ≫ τ₃ := by cat_disch

attribute [reassoc] Hom.comm₁₂ Hom.comm₂₃
attribute [local simp] Hom.comm₁₂ Hom.comm₂₃ Hom.comm₁₂_assoc Hom.comm₂₃_assoc

variable (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

/-- The identity morphism of a short complex. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.S
hortComplex.Hom`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] → (S : CategoryTheory.ShortComp
lex C) → S.Hom S
参数：S : CategoryTheory.ShortComplex C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism of a short complex.
-/
def Hom.id : Hom S S where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _

/-- The composition of morphisms of short complexes. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ShortComplex.Hom`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {S₁ S₂ S₃ : CategoryThe
ory.ShortComplex C} → S₁.Hom S₂ → S₂.Hom S₃ → S₁.Hom S₃
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of morphisms of short complexes.
-/
def Hom.comp (φ₁₂ : Hom S₁ S₂) (φ₂₃ : Hom S₂ S₃) : Hom S₁ S₃ where
  τ₁ := φ₁₂.τ₁ ≫ φ₂₃.τ₁
  τ₂ := φ₁₂.τ₂ ≫ φ₂₃.τ₂
  τ₃ := φ₁₂.τ₃ ≫ φ₂₃.τ₃
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (ShortComplex C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
/-
**CategoryTheory.ShortComplex.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ShortComplex`。
形式化陈述：hom_ext (f g : S₁ ⟶ S₂) (h₁ : f.τ₁ = g.τ₁) (h₂ : f.τ₂ = g.τ₂) (h₃ : f.τ₃ =
 g.τ₃) : f = g
参数：f g : S₁ ⟶ S₂；h₁ : f.τ₁ = g.τ₁；h₂ : f.τ₂ = g.τ₂；h₃ : f.τ₃ = g.τ₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Hom.ext`：∀ {C : Type u_1} {inst : CategoryTh
eory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} 
  {S₁ S₂ : CategoryTheory…
-/
lemma hom_ext (f g : S₁ ⟶ S₂) (h₁ : f.τ₁ = g.τ₁) (h₂ : f.τ₂ = g.τ₂) (h₃ : f.τ₃ = g.τ₃) : f = g :=
  Hom.ext h₁ h₂ h₃

/-- A constructor for morphisms in `ShortComplex C` when the commutativity conditions
are not obvious. -/
@[simps]
/-
**CategoryTheory.ShortComplex.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sh
ortComplex`。
形式化陈述：homMk {S₁ S₂ : ShortComplex C} (τ₁ : S₁.X₁ ⟶ S₂.X₁) (τ₂ : S₁.X₂ ⟶ S₂.X₂) (
τ₃ : S₁.X₃ ⟶ S₂.X₃) (comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂) (comm₂₃ : τ₂ ≫ S₂.g = S₁.g 
≫ τ₃) : S₁ ⟶ S₂
参数：τ₁ : S₁.X₁ ⟶ S₂.X₁；τ₂ : S₁.X₂ ⟶ S₂.X₂；τ₃ : S₁.X₃ ⟶ S₂.X₃；comm₁₂ : τ₁ ≫ S₂.f =
 S₁.f ≫ τ₂；comm₂₃ : τ₂ ≫ S₂.g = S₁.g ≫ τ₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for morphisms in `ShortComplex C` when the commutativity condition
s
are not obvious.
-/
def homMk {S₁ S₂ : ShortComplex C} (τ₁ : S₁.X₁ ⟶ S₂.X₁) (τ₂ : S₁.X₂ ⟶ S₂.X₂)
    (τ₃ : S₁.X₃ ⟶ S₂.X₃) (comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂)
    (comm₂₃ : τ₂ ≫ S₂.g = S₁.g ≫ τ₃) : S₁ ⟶ S₂ := ⟨τ₁, τ₂, τ₃, comm₁₂, comm₂₃⟩
/-
**CategoryTheory.ShortComplex.id_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Shor
tComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma id_τ₁ : Hom.τ₁ (𝟙 S) = 𝟙 _ := rfl
/-
**CategoryTheory.ShortComplex.id_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Shor
tComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma id_τ₂ : Hom.τ₂ (𝟙 S) = 𝟙 _ := rfl
/-
**CategoryTheory.ShortComplex.id_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Shor
tComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma id_τ₃ : Hom.τ₃ (𝟙 S) = 𝟙 _ := rfl
/-
**CategoryTheory.ShortComplex.comp_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sh
ortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[reassoc] lemma comp_τ₁ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₁ = φ₁₂.τ₁ ≫ φ₂₃.τ₁ := rfl
/-
**CategoryTheory.ShortComplex.comp_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sh
ortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[reassoc] lemma comp_τ₂ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₂ = φ₁₂.τ₂ ≫ φ₂₃.τ₂ := rfl
/-
**CategoryTheory.ShortComplex.comp_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sh
ortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[reassoc] lemma comp_τ₃ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₃ = φ₁₂.τ₃ ≫ φ₂₃.τ₃ := rfl

attribute [simp] comp_τ₁ comp_τ₂ comp_τ₃
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (S₁ ⟶ S₂) := ⟨{ τ₁ := 0, τ₂ := 0, τ₃ := 0 }⟩

variable (S₁ S₂)
/-
**CategoryTheory.ShortComplex.zero_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sh
ortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zero_τ₁ : Hom.τ₁ (0 : S₁ ⟶ S₂) = 0 := rfl
/-
**CategoryTheory.ShortComplex.zero_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sh
ortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zero_τ₂ : Hom.τ₂ (0 : S₁ ⟶ S₂) = 0 := rfl
/-
**CategoryTheory.ShortComplex.zero_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sh
ortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zero_τ₃ : Hom.τ₃ (0 : S₁ ⟶ S₂) = 0 := rfl

variable {S₁ S₂}
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasZeroMorphisms (ShortComplex C) where

/-- The first projection functor `ShortComplex C ⥤ C`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection functor `ShortComplex C ⥤ C`.
-/
def π₁ : ShortComplex C ⥤ C where
  obj S := S.X₁
  map f := f.τ₁

/-- The second projection functor `ShortComplex C ⥤ C`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection functor `ShortComplex C ⥤ C`.
-/
def π₂ : ShortComplex C ⥤ C where
  obj S := S.X₂
  map f := f.τ₂

/-- The third projection functor `ShortComplex C ⥤ C`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The third projection functor `ShortComplex C ⥤ C`.
-/
def π₃ : ShortComplex C ⥤ C where
  obj S := S.X₃
  map f := f.τ₃
/-
**CategoryTheory.ShortComplex.preservesZeroMorphisms_** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesZeroMorphisms_π₁ : Functor.PreservesZeroMorphisms (π₁ : _ ⥤ C) where
/-
**CategoryTheory.ShortComplex.preservesZeroMorphisms_** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesZeroMorphisms_π₂ : Functor.PreservesZeroMorphisms (π₂ : _ ⥤ C) where
/-
**CategoryTheory.ShortComplex.preservesZeroMorphisms_** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preservesZeroMorphisms_π₃ : Functor.PreservesZeroMorphisms (π₃ : _ ⥤ C) where
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : S₁ ⟶ S₂) [IsIso f] : IsIso f.τ₁ := (inferInstance : IsIso (π₁.mapIso (asIso f)).hom)
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : S₁ ⟶ S₂) [IsIso f] : IsIso f.τ₂ := (inferInstance : IsIso (π₂.mapIso (asIso f)).hom)
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : S₁ ⟶ S₂) [IsIso f] : IsIso f.τ₃ := (inferInstance : IsIso (π₃.mapIso (asIso f)).hom)

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `π₁ ⟶ π₂` induced by `S.f` for all `S : ShortComplex C`. -/
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `π₁ ⟶ π₂` induced by `S.f` for all `S : ShortComplex 
C`.
-/
@[simps] def π₁Toπ₂ : (π₁ : _ ⥤ C) ⟶ π₂ where
  app S := S.f

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `π₂ ⟶ π₃` induced by `S.g` for all `S : ShortComplex C`. -/
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `π₂ ⟶ π₃` induced by `S.g` for all `S : ShortComplex 
C`.
-/
@[simps] def π₂Toπ₃ : (π₂ : _ ⥤ C) ⟶ π₃ where
  app S := S.g

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π₁Toπ₂_comp_π₂Toπ₃ : (π₁Toπ₂ : (_ : _ ⥤ C) ⟶ _) ≫ π₂Toπ₃ = 0 := by cat_disch

/-- The short complex in `D` obtained by applying a functor `F : C ⥤ D` to a
short complex in `C`, assuming that `F` preserves zero morphisms. -/
@[simps]
/-
**CategoryTheory.ShortComplex.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Shor
tComplex`。
形式化陈述：map (F : C ⥤ D) [F.PreservesZeroMorphisms] : ShortComplex D
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short complex in `D` obtained by applying a functor `F : C ⥤ D` to a
short complex in `C`, assuming that `F` preserves zero morphisms.
-/
def map (F : C ⥤ D) [F.PreservesZeroMorphisms] : ShortComplex D :=
  ShortComplex.mk (F.map S.f) (F.map S.g) (by rw [← F.map_comp, S.zero, F.map_zero])
/-
**CategoryTheory.ShortComplex.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.S
hortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   (S : CategoryTheory.ShortComplex C), 
S.map (CategoryTheory.Functor.id C) = S
参数：S : CategoryTheory.ShortComplex C；CategoryTheory.Functor.id C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_full`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.Full.id`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C], (CategoryTheory.Functor.id C).Full
-/
@[simp] lemma map_id (S : ShortComplex C) : S.map (𝟭 C) = S := rfl
/-
**CategoryTheory.ShortComplex.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} {E : Type u_3} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : C
ategoryTheory.Category.{v_3, u_3} E]   [inst_3 : CategoryTheory.Limits.HasZeroMo
rphisms C] [inst_4 : CategoryTheory.Limits.HasZeroMorphisms D]   [inst_5 : Categ
oryTheory.Limits.HasZeroMorphisms E] (S : CategoryTheory.ShortComplex C)   (F : 
CategoryTheory.Functor C D) [inst_6 : F.PreservesZeroMorphisms] (G : CategoryThe
ory.Functor D E)   [inst_7 : G.PreservesZeroMorphisms], S.map (F.comp G) = (S.ma
p F).map G
参数：S : CategoryTheory.ShortComplex C；F : CategoryTheory.Functor C D；G : Category
Theory.Functor D E；F.comp G；S.map F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma map_comp (S : ShortComplex C)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (G : D ⥤ E) [G.PreservesZeroMorphisms] :
    S.map (F ⋙ G) = (S.map F).map G := rfl

set_option backward.defeqAttrib.useBackward true in
/-- The morphism of short complexes `S.map F ⟶ S.map G` induced by
a natural transformation `F ⟶ G`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.mapNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ShortComplex`。
形式化陈述：mapNatTrans {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorph
isms] (τ : F ⟶ G) : S.map F ⟶ S.map G where τ₁
参数：τ : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism of short complexes `S.map F ⟶ S.map G` induced by
a natural transformation `F ⟶ G`.
-/
def mapNatTrans {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ⟶ G) :
    S.map F ⟶ S.map G where
  τ₁ := τ.app _
  τ₂ := τ.app _
  τ₃ := τ.app _

set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism of short complexes `S.map F ≅ S.map G` induced by
a natural isomorphism `F ≅ G`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.mapNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ShortComplex`。
形式化陈述：mapNatIso {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphis
ms] (τ : F ≅ G) : S.map F ≅ S.map G where hom
参数：τ : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism of short complexes `S.map F ≅ S.map G` induced by
a natural isomorphism `F ≅ G`.
-/
def mapNatIso {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ≅ G) :
    S.map F ≅ S.map G where
  hom := S.mapNatTrans τ.hom
  inv := S.mapNatTrans τ.inv

set_option backward.defeqAttrib.useBackward true in
/-- The functor `ShortComplex C ⥤ ShortComplex D` induced by a functor `C ⥤ D` which
preserves zero morphisms. -/
@[simps]
/-
**CategoryTheory.ShortComplex._root_.CategoryTheory.Functor.mapShortComplex** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ShortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `ShortComplex C ⥤ ShortComplex D` induced by a functor `C ⥤ D` which
preserves zero morphisms.
-/
def _root_.CategoryTheory.Functor.mapShortComplex (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    ShortComplex C ⥤ ShortComplex D where
  obj S := S.map F
  map φ :=
    { τ₁ := F.map φ.τ₁
      τ₂ := F.map φ.τ₂
      τ₃ := F.map φ.τ₃
      comm₁₂ := by
        dsimp
        simp only [← F.map_comp, φ.comm₁₂]
      comm₂₃ := by
        dsimp
        simp only [← F.map_comp, φ.comm₂₃] }

/-- A constructor for isomorphisms in the category `ShortComplex C` -/
@[simps]
/-
**CategoryTheory.ShortComplex.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sh
ortComplex`。
形式化陈述：isoMk (e₁ : S₁.X₁ ≅ S₂.X₁) (e₂ : S₁.X₂ ≅ S₂.X₂) (e₃ : S₁.X₃ ≅ S₂.X₃) (comm
₁₂ : e₁.hom ≫ S₂.f = S₁.f ≫ e₂.hom
参数：e₁ : S₁.X₁ ≅ S₂.X₁；e₂ : S₁.X₂ ≅ S₂.X₂；e₃ : S₁.X₃ ≅ S₂.X₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for isomorphisms in the category `ShortComplex C`
-/
def isoMk (e₁ : S₁.X₁ ≅ S₂.X₁) (e₂ : S₁.X₂ ≅ S₂.X₂) (e₃ : S₁.X₃ ≅ S₂.X₃)
    (comm₁₂ : e₁.hom ≫ S₂.f = S₁.f ≫ e₂.hom := by cat_disch)
    (comm₂₃ : e₂.hom ≫ S₂.g = S₁.g ≫ e₃.hom := by cat_disch) :
    S₁ ≅ S₂ where
  hom := ⟨e₁.hom, e₂.hom, e₃.hom, comm₁₂, comm₂₃⟩
  inv := homMk e₁.inv e₂.inv e₃.inv
    (by rw [← cancel_mono e₂.hom, assoc, assoc, e₂.inv_hom_id, comp_id,
          ← comm₁₂, e₁.inv_hom_id_assoc])
    (by rw [← cancel_mono e₃.hom, assoc, assoc, e₃.inv_hom_id, comp_id,
          ← comm₂₃, e₂.inv_hom_id_assoc])
/-
**CategoryTheory.ShortComplex.isIso_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：isIso_of_isIso (f : S₁ ⟶ S₂) [IsIso f.τ₁] [IsIso f.τ₂] [IsIso f.τ₃] : IsIs
o f
参数：f : S₁ ⟶ S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₁₂`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₂₃`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…
-/
lemma isIso_of_isIso (f : S₁ ⟶ S₂) [IsIso f.τ₁] [IsIso f.τ₂] [IsIso f.τ₃] : IsIso f :=
  (isoMk (asIso f.τ₁) (asIso f.τ₂) (asIso f.τ₃)).isIso_hom
/-
**CategoryTheory.ShortComplex.isIso_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.ShortComplex`。
形式化陈述：isIso_iff (f : S₁ ⟶ S₂) : IsIso f ↔ IsIso f.τ₁ ∧ IsIso f.τ₂ ∧ IsIso f.τ₃
参数：f : S₁ ⟶ S₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoτ₁`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoτ₂`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.instIsIsoτ₃`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms
 C]   {S₁ S₂ : CategoryTheory…
· 使用引理 `CategoryTheory.ShortComplex.isIso_of_isIso`：isIso_of_isIso (f : S₁ ⟶ S₂)
 [IsIso f.τ₁] [IsIso f.τ₂] [IsIso f.τ₃] : IsIso f
-/
lemma isIso_iff (f : S₁ ⟶ S₂) :
    IsIso f ↔ IsIso f.τ₁ ∧ IsIso f.τ₂ ∧ IsIso f.τ₃ := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance, inferInstance⟩, ?_⟩
  rintro ⟨_, _, _⟩
  apply isIso_of_isIso

/-- The first map of a short complex, as a functor. -/
/-
**CategoryTheory.ShortComplex.fFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       CategoryTheory.Functor 
(CategoryTheory.ShortComplex C) (CategoryTheory.Arrow C)
参数：CategoryTheory.ShortComplex C；CategoryTheory.Arrow C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₁₂`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…

--- 原说明 ---
The first map of a short complex, as a functor.
-/
@[simps] def fFunctor : ShortComplex C ⥤ Arrow C where
  obj S := .mk S.f
  map {S T} f := Arrow.homMk f.τ₁ f.τ₂ f.comm₁₂

/-- The second map of a short complex, as a functor. -/
/-
**CategoryTheory.ShortComplex.gFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Limits.HasZeroMorphisms C] →       CategoryTheory.Functor 
(CategoryTheory.ShortComplex C) (CategoryTheory.Arrow C)
参数：CategoryTheory.ShortComplex C；CategoryTheory.Arrow C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₂₃`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…

--- 原说明 ---
The second map of a short complex, as a functor.
-/
@[simps] def gFunctor : ShortComplex C ⥤ Arrow C where
  obj S := .mk S.g
  map {S T} f := Arrow.homMk f.τ₂ f.τ₃ f.comm₂₃

/-- The opposite `ShortComplex` in `Cᵒᵖ` associated to a short complex in `C`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Short
Complex`。
形式化陈述：op : ShortComplex Cᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite `ShortComplex` in `Cᵒᵖ` associated to a short complex in `C`.
-/
def op : ShortComplex Cᵒᵖ :=
  mk S.g.op S.f.op (by simp only [← op_comp, S.zero]; rfl)

set_option backward.defeqAttrib.useBackward true in
/-- The opposite morphism in `ShortComplex Cᵒᵖ` associated to a morphism in `ShortComplex C` -/
@[simps]
/-
**CategoryTheory.ShortComplex.opMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sh
ortComplex`。
形式化陈述：opMap (φ : S₁ ⟶ S₂) : S₂.op ⟶ S₁.op where τ₁
参数：φ : S₁ ⟶ S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite morphism in `ShortComplex Cᵒᵖ` associated to a morphism in `ShortCo
mplex C`
-/
def opMap (φ : S₁ ⟶ S₂) : S₂.op ⟶ S₁.op where
  τ₁ := φ.τ₃.op
  τ₂ := φ.τ₂.op
  τ₃ := φ.τ₁.op
  comm₁₂ := by
    dsimp
    simp only [← op_comp, φ.comm₂₃]
  comm₂₃ := by
    dsimp
    simp only [← op_comp, φ.comm₁₂]

@[simp]
/-
**CategoryTheory.ShortComplex.opMap_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：opMap_id : opMap (𝟙 S) = 𝟙 S.op
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opMap_id : opMap (𝟙 S) = 𝟙 S.op := rfl

/-- The `ShortComplex` in `C` associated to a short complex in `Cᵒᵖ`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sho
rtComplex`。
形式化陈述：unop (S : ShortComplex Cᵒᵖ) : ShortComplex C
参数：S : ShortComplex Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ShortComplex` in `C` associated to a short complex in `Cᵒᵖ`.
-/
def unop (S : ShortComplex Cᵒᵖ) : ShortComplex C :=
  mk S.g.unop S.f.unop (by simp only [← unop_comp, S.zero]; rfl)

set_option backward.defeqAttrib.useBackward true in
/-- The morphism in `ShortComplex C` associated to a morphism in `ShortComplex Cᵒᵖ` -/
@[simps]
/-
**CategoryTheory.ShortComplex.unopMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
ShortComplex`。
形式化陈述：unopMap {S₁ S₂ : ShortComplex Cᵒᵖ} (φ : S₁ ⟶ S₂) : S₂.unop ⟶ S₁.unop where
 τ₁
参数：φ : S₁ ⟶ S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism in `ShortComplex C` associated to a morphism in `ShortComplex Cᵒᵖ`
-/
def unopMap {S₁ S₂ : ShortComplex Cᵒᵖ} (φ : S₁ ⟶ S₂) : S₂.unop ⟶ S₁.unop where
  τ₁ := φ.τ₃.unop
  τ₂ := φ.τ₂.unop
  τ₃ := φ.τ₁.unop
  comm₁₂ := by
    dsimp
    simp only [← unop_comp, φ.comm₂₃]
  comm₂₃ := by
    dsimp
    simp only [← unop_comp, φ.comm₁₂]

@[simp]
/-
**CategoryTheory.ShortComplex.unopMap_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.ShortComplex`。
形式化陈述：unopMap_id (S : ShortComplex Cᵒᵖ) : unopMap (𝟙 S) = 𝟙 S.unop
参数：S : ShortComplex Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unopMap_id (S : ShortComplex Cᵒᵖ) : unopMap (𝟙 S) = 𝟙 S.unop := rfl

variable (C)

/-- The obvious functor `(ShortComplex C)ᵒᵖ ⥤ ShortComplex Cᵒᵖ`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.opFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ShortComplex`。
形式化陈述：opFunctor : (ShortComplex C)ᵒᵖ ⥤ ShortComplex Cᵒᵖ where obj S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious functor `(ShortComplex C)ᵒᵖ ⥤ ShortComplex Cᵒᵖ`.
-/
def opFunctor : (ShortComplex C)ᵒᵖ ⥤ ShortComplex Cᵒᵖ where
  obj S := (Opposite.unop S).op
  map φ := opMap φ.unop

/-- The obvious functor `ShortComplex Cᵒᵖ ⥤ (ShortComplex C)ᵒᵖ`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.unopFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ShortComplex`。
形式化陈述：unopFunctor : ShortComplex Cᵒᵖ ⥤ (ShortComplex C)ᵒᵖ where obj S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious functor `ShortComplex Cᵒᵖ ⥤ (ShortComplex C)ᵒᵖ`.
-/
def unopFunctor : ShortComplex Cᵒᵖ ⥤ (ShortComplex C)ᵒᵖ where
  obj S := Opposite.op (S.unop)
  map φ := (unopMap φ).op

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The obvious equivalence of categories `(ShortComplex C)ᵒᵖ ≌ ShortComplex Cᵒᵖ`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
ShortComplex`。
形式化陈述：opEquiv : (ShortComplex C)ᵒᵖ ≌ ShortComplex Cᵒᵖ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious equivalence of categories `(ShortComplex C)ᵒᵖ ≌ ShortComplex Cᵒᵖ`.
-/
def opEquiv : (ShortComplex C)ᵒᵖ ≌ ShortComplex Cᵒᵖ where
  functor := opFunctor C
  inverse := unopFunctor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

variable {C}

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical isomorphism `S.unop.op ≅ S` for a short complex `S` in `Cᵒᵖ` -/
/-
**CategoryTheory.ShortComplex.unopOp** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：unopOp (S : ShortComplex Cᵒᵖ) : S.unop.op ≅ S
参数：S : ShortComplex Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `S.unop.op ≅ S` for a short complex `S` in `Cᵒᵖ`
-/
abbrev unopOp (S : ShortComplex Cᵒᵖ) : S.unop.op ≅ S := (opEquiv C).counitIso.app S

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical isomorphism `S.op.unop ≅ S` for a short complex `S` -/
/-
**CategoryTheory.ShortComplex.opUnop** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：opUnop (S : ShortComplex C) : S.op.unop ≅ S
参数：S : ShortComplex C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `S.op.unop ≅ S` for a short complex `S`
-/
abbrev opUnop (S : ShortComplex C) : S.op.unop ≅ S :=
  Iso.unop ((opEquiv C).unitIso.app (Opposite.op S))

end ShortComplex

end CategoryTheory

