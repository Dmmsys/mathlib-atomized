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
/--
Definition of `ShortComplex` / `ShortComplex` 的定义

English:
structure ShortComplex
  parameters: where
  axioms and operations (6):
    - {X₁ : C}
    - {X₂ : C}
    - {X₃ : C}
    - f : X₁ ⟶ X₂
    - g : X₂ ⟶ X₃
    - zero : f ≫ g = 0  [default: by cat_disch]

中文:
结构 ShortComplex
  参数: where
  公理与运算 (6 个):
    - {X₁ : C}
    - {X₂ : C}
    - {X₃ : C}
    - f : X₁ ⟶ X₂
    - g : X₂ ⟶ X₃
    - zero : f ≫ g = 0  [默认: by cat_disch]

Depends on / 依赖: cat_disch
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
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (S₁ S₂ : ShortComplex C)
  axioms and operations (5):
    - τ₁ : S₁.X₁ ⟶ S₂.X₁
    - τ₂ : S₁.X₂ ⟶ S₂.X₂
    - τ₃ : S₁.X₃ ⟶ S₂.X₃
    - comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂  [default: by cat_disch]
    - comm₂₃ : τ₂ ≫ S₂.g = S₁.g ≫ τ₃  [default: by cat_disch]

中文:
结构 Hom
  参数: (S₁ S₂ : ShortComplex C)
  公理与运算 (5 个):
    - τ₁ : S₁.X₁ ⟶ S₂.X₁
    - τ₂ : S₁.X₂ ⟶ S₂.X₂
    - τ₃ : S₁.X₃ ⟶ S₂.X₃
    - comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂  [默认: by cat_disch]
    - comm₂₃ : τ₂ ≫ S₂.g = S₁.g ≫ τ₃  [默认: by cat_disch]

Depends on / 依赖: cat_disch
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
/--
Definition of `Hom.id` / `Hom.id` 的定义

English:
definition Hom.id
  signature: : Hom S S where
  body: 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _

中文:
定义 Hom.id
  签名: : Hom S S where
  定义体: 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
-/
def Hom.id : Hom S S where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _

/-- The composition of morphisms of short complexes. -/
@[simps]
/--
Definition of `Hom.comp` / `Hom.comp` 的定义

English:
definition Hom.comp
  signature: (φ₁₂ : Hom S₁ S₂) (φ₂₃ : Hom S₂ S₃)
  body: φ₁₂.τ₁ ≫ φ₂₃.τ₁
  τ₂ := φ₁₂.τ₂ ≫ φ₂₃.τ₂
  τ₃ := φ₁₂.τ₃ ≫ φ₂₃.τ₃

中文:
定义 Hom.comp
  签名: (φ₁₂ : Hom S₁ S₂) (φ₂₃ : Hom S₂ S₃)
  定义体: φ₁₂.τ₁ ≫ φ₂₃.τ₁
  τ₂ := φ₁₂.τ₂ ≫ φ₂₃.τ₂
  τ₃ := φ₁₂.τ₃ ≫ φ₂₃.τ₃
-/
def Hom.comp (φ₁₂ : Hom S₁ S₂) (φ₂₃ : Hom S₂ S₃) : Hom S₁ S₃ where
  τ₁ := φ₁₂.τ₁ ≫ φ₂₃.τ₁
  τ₂ := φ₁₂.τ₂ ≫ φ₂₃.τ₂
  τ₃ := φ₁₂.τ₃ ≫ φ₂₃.τ₃

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (ShortComplex C)
  body: Hom
  id := Hom.id
  comp := Hom.comp

@[ext]

中文:
实例 :
  签名: Category (ShortComplex C)
  定义体: Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
-/
instance : Category (ShortComplex C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: (f g : S₁ ⟶ S₂) (h₁ : f.τ₁ = g.τ₁) (h₂ : f.τ₂ = g.τ₂) (h₃ : f.τ₃ = g.τ₃)
  statement: f = g
  proof: Hom.ext h₁ h₂ h₃

中文:
引理 hom_ext
  条件: (f g : S₁ ⟶ S₂) (h₁ : f.τ₁ = g.τ₁) (h₂ : f.τ₂ = g.τ₂) (h₃ : f.τ₃ = g.τ₃)
  结论: f = g
  证明: Hom.ext h₁ h₂ h₃

Depends on / 依赖: Hom.ext
-/
lemma hom_ext (f g : S₁ ⟶ S₂) (h₁ : f.τ₁ = g.τ₁) (h₂ : f.τ₂ = g.τ₂) (h₃ : f.τ₃ = g.τ₃) : f = g :=
  Hom.ext h₁ h₂ h₃

/-- A constructor for morphisms in `ShortComplex C` when the commutativity conditions
are not obvious. -/
@[simps]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {S₁ S₂ : ShortComplex C} (τ₁ : S₁.X₁ ⟶ S₂.X₁) (τ₂ : S₁.X₂ ⟶ S₂.X₂)
  body: ⟨τ₁, τ₂, τ₃, comm₁₂, comm₂₃⟩

中文:
定义 homMk
  签名: {S₁ S₂ : ShortComplex C} (τ₁ : S₁.X₁ ⟶ S₂.X₁) (τ₂ : S₁.X₂ ⟶ S₂.X₂)
  定义体: ⟨τ₁, τ₂, τ₃, comm₁₂, comm₂₃⟩
-/
def homMk {S₁ S₂ : ShortComplex C} (τ₁ : S₁.X₁ ⟶ S₂.X₁) (τ₂ : S₁.X₂ ⟶ S₂.X₂)
    (τ₃ : S₁.X₃ ⟶ S₂.X₃) (comm₁₂ : τ₁ ≫ S₂.f = S₁.f ≫ τ₂)
    (comm₂₃ : τ₂ ≫ S₂.g = S₁.g ≫ τ₃) : S₁ ⟶ S₂ := ⟨τ₁, τ₂, τ₃, comm₁₂, comm₂₃⟩

/--
lemma `id_τ₁` / 引理 `id_τ₁`

English:
lemma id_τ₁
  statement: Hom.τ₁ (𝟙 S) = 𝟙 _
  proof: rfl

中文:
引理 id_τ₁
  结论: Hom.τ₁ (𝟙 S) = 𝟙 _
  证明: rfl
-/
@[simp] lemma id_τ₁ : Hom.τ₁ (𝟙 S) = 𝟙 _ := rfl
/--
lemma `id_τ₂` / 引理 `id_τ₂`

English:
lemma id_τ₂
  statement: Hom.τ₂ (𝟙 S) = 𝟙 _
  proof: rfl

中文:
引理 id_τ₂
  结论: Hom.τ₂ (𝟙 S) = 𝟙 _
  证明: rfl
-/
@[simp] lemma id_τ₂ : Hom.τ₂ (𝟙 S) = 𝟙 _ := rfl
/--
lemma `id_τ₃` / 引理 `id_τ₃`

English:
lemma id_τ₃
  statement: Hom.τ₃ (𝟙 S) = 𝟙 _
  proof: rfl

中文:
引理 id_τ₃
  结论: Hom.τ₃ (𝟙 S) = 𝟙 _
  证明: rfl
-/
@[simp] lemma id_τ₃ : Hom.τ₃ (𝟙 S) = 𝟙 _ := rfl
/--
lemma `comp_τ₁` / 引理 `comp_τ₁`

English:
lemma comp_τ₁
  given: (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃)
  proof: rfl

中文:
引理 comp_τ₁
  条件: (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃)
  证明: rfl
-/
@[reassoc] lemma comp_τ₁ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₁ = φ₁₂.τ₁ ≫ φ₂₃.τ₁ := rfl
/--
lemma `comp_τ₂` / 引理 `comp_τ₂`

English:
lemma comp_τ₂
  given: (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃)
  proof: rfl

中文:
引理 comp_τ₂
  条件: (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃)
  证明: rfl
-/
@[reassoc] lemma comp_τ₂ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₂ = φ₁₂.τ₂ ≫ φ₂₃.τ₂ := rfl
/--
lemma `comp_τ₃` / 引理 `comp_τ₃`

English:
lemma comp_τ₃
  given: (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃)
  proof: rfl

中文:
引理 comp_τ₃
  条件: (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃)
  证明: rfl
-/
@[reassoc] lemma comp_τ₃ (φ₁₂ : S₁ ⟶ S₂) (φ₂₃ : S₂ ⟶ S₃) :
    (φ₁₂ ≫ φ₂₃).τ₃ = φ₁₂.τ₃ ≫ φ₂₃.τ₃ := rfl

attribute [simp] comp_τ₁ comp_τ₂ comp_τ₃

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (S₁ ⟶ S₂)
  body: ⟨{ τ₁ := 0, τ₂ := 0, τ₃ := 0 }⟩

中文:
实例 :
  签名: Zero (S₁ ⟶ S₂)
  定义体: ⟨{ τ₁ := 0, τ₂ := 0, τ₃ := 0 }⟩
-/
instance : Zero (S₁ ⟶ S₂) := ⟨{ τ₁ := 0, τ₂ := 0, τ₃ := 0 }⟩

variable (S₁ S₂)

/--
lemma `zero_τ₁` / 引理 `zero_τ₁`

English:
lemma zero_τ₁
  statement: Hom.τ₁ (0 : S₁ ⟶ S₂) = 0
  proof: rfl

中文:
引理 zero_τ₁
  结论: Hom.τ₁ (0 : S₁ ⟶ S₂) = 0
  证明: rfl
-/
@[simp] lemma zero_τ₁ : Hom.τ₁ (0 : S₁ ⟶ S₂) = 0 := rfl
/--
lemma `zero_τ₂` / 引理 `zero_τ₂`

English:
lemma zero_τ₂
  statement: Hom.τ₂ (0 : S₁ ⟶ S₂) = 0
  proof: rfl

中文:
引理 zero_τ₂
  结论: Hom.τ₂ (0 : S₁ ⟶ S₂) = 0
  证明: rfl
-/
@[simp] lemma zero_τ₂ : Hom.τ₂ (0 : S₁ ⟶ S₂) = 0 := rfl
/--
lemma `zero_τ₃` / 引理 `zero_τ₃`

English:
lemma zero_τ₃
  statement: Hom.τ₃ (0 : S₁ ⟶ S₂) = 0
  proof: rfl

中文:
引理 zero_τ₃
  结论: Hom.τ₃ (0 : S₁ ⟶ S₂) = 0
  证明: rfl
-/
@[simp] lemma zero_τ₃ : Hom.τ₃ (0 : S₁ ⟶ S₂) = 0 := rfl

variable {S₁ S₂}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasZeroMorphisms (ShortComplex C)

中文:
实例 :
  签名: HasZeroMorphisms (ShortComplex C)
-/
instance : HasZeroMorphisms (ShortComplex C) where

/-- The first projection functor `ShortComplex C ⥤ C`. -/
@[simps]
/--
Definition of `π₁` / `π₁` 的定义

English:
definition π₁
  signature: : ShortComplex C ⥤ C where
  body: S.X₁
  map f := f.τ₁

中文:
定义 π₁
  签名: : ShortComplex C ⥤ C where
  定义体: S.X₁
  map f := f.τ₁
-/
def π₁ : ShortComplex C ⥤ C where
  obj S := S.X₁
  map f := f.τ₁

/-- The second projection functor `ShortComplex C ⥤ C`. -/
@[simps]
/--
Definition of `π₂` / `π₂` 的定义

English:
definition π₂
  signature: : ShortComplex C ⥤ C where
  body: S.X₂
  map f := f.τ₂

中文:
定义 π₂
  签名: : ShortComplex C ⥤ C where
  定义体: S.X₂
  map f := f.τ₂
-/
def π₂ : ShortComplex C ⥤ C where
  obj S := S.X₂
  map f := f.τ₂

/-- The third projection functor `ShortComplex C ⥤ C`. -/
@[simps]
/--
Definition of `π₃` / `π₃` 的定义

English:
definition π₃
  signature: : ShortComplex C ⥤ C where
  body: S.X₃
  map f := f.τ₃

中文:
定义 π₃
  签名: : ShortComplex C ⥤ C where
  定义体: S.X₃
  map f := f.τ₃
-/
def π₃ : ShortComplex C ⥤ C where
  obj S := S.X₃
  map f := f.τ₃

/--
Instance `preservesZeroMorphisms_π₁` / 实例 `preservesZeroMorphisms_π₁`

English:
instance preservesZeroMorphisms_π₁
  signature: : Functor.PreservesZeroMorphisms (π₁ : _ ⥤ C) where

中文:
实例 preservesZeroMorphisms_π₁
  签名: : Functor.PreservesZeroMorphisms (π₁ : _ ⥤ C) where
-/
instance preservesZeroMorphisms_π₁ : Functor.PreservesZeroMorphisms (π₁ : _ ⥤ C) where
/--
Instance `preservesZeroMorphisms_π₂` / 实例 `preservesZeroMorphisms_π₂`

English:
instance preservesZeroMorphisms_π₂
  signature: : Functor.PreservesZeroMorphisms (π₂ : _ ⥤ C) where

中文:
实例 preservesZeroMorphisms_π₂
  签名: : Functor.PreservesZeroMorphisms (π₂ : _ ⥤ C) where
-/
instance preservesZeroMorphisms_π₂ : Functor.PreservesZeroMorphisms (π₂ : _ ⥤ C) where
/--
Instance `preservesZeroMorphisms_π₃` / 实例 `preservesZeroMorphisms_π₃`

English:
instance preservesZeroMorphisms_π₃
  signature: : Functor.PreservesZeroMorphisms (π₃ : _ ⥤ C) where

中文:
实例 preservesZeroMorphisms_π₃
  签名: : Functor.PreservesZeroMorphisms (π₃ : _ ⥤ C) where
-/
instance preservesZeroMorphisms_π₃ : Functor.PreservesZeroMorphisms (π₃ : _ ⥤ C) where

instance (f : S₁ ⟶ S₂) [IsIso f] : IsIso f.τ₁ := (inferInstance : IsIso (π₁.mapIso (asIso f)).hom)
instance (f : S₁ ⟶ S₂) [IsIso f] : IsIso f.τ₂ := (inferInstance : IsIso (π₂.mapIso (asIso f)).hom)
instance (f : S₁ ⟶ S₂) [IsIso f] : IsIso f.τ₃ := (inferInstance : IsIso (π₃.mapIso (asIso f)).hom)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `π₁Toπ₂` / `π₁Toπ₂` 的定义

English:
definition π₁Toπ₂
  signature: : (π₁ : _ ⥤ C) ⟶ π₂ where
  body: S.f

中文:
定义 π₁Toπ₂
  签名: : (π₁ : _ ⥤ C) ⟶ π₂ where
  定义体: S.f
-/
@[simps] def π₁Toπ₂ : (π₁ : _ ⥤ C) ⟶ π₂ where
  app S := S.f

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `π₂Toπ₃` / `π₂Toπ₃` 的定义

English:
definition π₂Toπ₃
  signature: : (π₂ : _ ⥤ C) ⟶ π₃ where
  body: S.g

中文:
定义 π₂Toπ₃
  签名: : (π₂ : _ ⥤ C) ⟶ π₃ where
  定义体: S.g
-/
@[simps] def π₂Toπ₃ : (π₂ : _ ⥤ C) ⟶ π₃ where
  app S := S.g

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `π₁Toπ₂_comp_π₂Toπ₃` / 引理 `π₁Toπ₂_comp_π₂Toπ₃`

English:
lemma π₁Toπ₂_comp_π₂Toπ₃
  statement: (π₁Toπ₂ : (_ : _ ⥤ C) ⟶ _) ≫ π₂Toπ₃ = 0
  proof: by cat_disch

中文:
引理 π₁Toπ₂_comp_π₂Toπ₃
  结论: (π₁Toπ₂ : (_ : _ ⥤ C) ⟶ _) ≫ π₂Toπ₃ = 0
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma π₁Toπ₂_comp_π₂Toπ₃ : (π₁Toπ₂ : (_ : _ ⥤ C) ⟶ _) ≫ π₂Toπ₃ = 0 := by cat_disch

/-- The short complex in `D` obtained by applying a functor `F : C ⥤ D` to a
short complex in `C`, assuming that `F` preserves zero morphisms. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (F : C ⥤ D) [F.PreservesZeroMorphisms]
  body: ShortComplex.mk (F.map S.f) (F.map S.g) (by rw [← F.map_comp, S.zero, F.map_zero])

中文:
定义 map
  签名: (F : C ⥤ D) [F.PreservesZeroMorphisms]
  定义体: ShortComplex.mk (F.map S.f) (F.map S.g) (by rw [← F.map_comp, S.zero, F.map_zero])

Depends on / 依赖: F.map, F.map_comp, F.map_zero, S.zero, ShortComplex, ShortComplex.mk, map_comp, map_zero
-/
def map (F : C ⥤ D) [F.PreservesZeroMorphisms] : ShortComplex D :=
  ShortComplex.mk (F.map S.f) (F.map S.g) (by rw [← F.map_comp, S.zero, F.map_zero])

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (S : ShortComplex C)
  statement: S.map (𝟭 C) = S
  proof: rfl

中文:
引理 map_id
  条件: (S : ShortComplex C)
  结论: S.map (𝟭 C) = S
  证明: rfl
-/
@[simp] lemma map_id (S : ShortComplex C) : S.map (𝟭 C) = S := rfl

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  statement: (S : ShortComplex C)
  proof: rfl

中文:
引理 map_comp
  结论: (S : ShortComplex C)
  证明: rfl
-/
@[simp] lemma map_comp (S : ShortComplex C)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (G : D ⥤ E) [G.PreservesZeroMorphisms] :
    S.map (F ⋙ G) = (S.map F).map G := rfl

set_option backward.defeqAttrib.useBackward true in
/-- The morphism of short complexes `S.map F ⟶ S.map G` induced by
a natural transformation `F ⟶ G`. -/
@[simps]
/--
Definition of `mapNatTrans` / `mapNatTrans` 的定义

English:
definition mapNatTrans
  signature: {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ⟶ G)
  body: τ.app _
  τ₂ := τ.app _
  τ₃ := τ.app _

中文:
定义 mapNatTrans
  签名: {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ⟶ G)
  定义体: τ.app _
  τ₂ := τ.app _
  τ₃ := τ.app _
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
/--
Definition of `mapNatIso` / `mapNatIso` 的定义

English:
definition mapNatIso
  signature: {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ≅ G)
  body: S.mapNatTrans τ.hom
  inv := S.mapNatTrans τ.inv

中文:
定义 mapNatIso
  签名: {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ≅ G)
  定义体: S.mapNatTrans τ.hom
  inv := S.mapNatTrans τ.inv

Depends on / 依赖: S.mapNatTrans, mapNatTrans
-/
def mapNatIso {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (τ : F ≅ G) :
    S.map F ≅ S.map G where
  hom := S.mapNatTrans τ.hom
  inv := S.mapNatTrans τ.inv

set_option backward.defeqAttrib.useBackward true in
/-- The functor `ShortComplex C ⥤ ShortComplex D` induced by a functor `C ⥤ D` which
preserves zero morphisms. -/
@[simps]
/--
Definition of `_root_.CategoryTheory.Functor.mapShortComplex` / `_root_.CategoryTheory.Functor.mapShortComplex` 的定义

English:
definition _root_.CategoryTheory.Functor.mapShortComplex
  signature: (F : C ⥤ D) [F.PreservesZeroMorphisms]
  body: S.map F
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

中文:
定义 _root_.CategoryTheory.Functor.mapShortComplex
  签名: (F : C ⥤ D) [F.PreservesZeroMorphisms]
  定义体: S.map F
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

Depends on / 依赖: S.map
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
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: (e₁ : S₁.X₁ ≅ S₂.X₁) (e₂ : S₁.X₂ ≅ S₂.X₂) (e₃ : S₁.X₃ ≅ S₂.X₃)
  body: ⟨e₁.hom, e₂.hom, e₃.hom, comm₁₂, comm₂₃⟩
  inv := homMk e₁.inv e₂.inv e₃.inv
    (by rw [← cancel_mono e₂.hom, assoc, assoc, e₂.inv_hom_id, comp_id,
          ← comm₁₂, e₁.inv_hom_id_assoc])
    (by rw [← cancel_mono e₃.hom, assoc, assoc, e₃.inv_hom_id, comp_id,
          ← comm₂₃, e₂.inv_hom_id_ass

中文:
定义 isoMk
  签名: (e₁ : S₁.X₁ ≅ S₂.X₁) (e₂ : S₁.X₂ ≅ S₂.X₂) (e₃ : S₁.X₃ ≅ S₂.X₃)
  定义体: ⟨e₁.hom, e₂.hom, e₃.hom, comm₁₂, comm₂₃⟩
  inv := homMk e₁.inv e₂.inv e₃.inv
    (by rw [← cancel_mono e₂.hom, assoc, assoc, e₂.inv_hom_id, comp_id,
          ← comm₁₂, e₁.inv_hom_id_assoc])
    (by rw [← cancel_mono e₃.hom, assoc, assoc, e₃.inv_hom_id, comp_id,
          ← comm₂₃, e₂.inv_hom_id_ass

Depends on / 依赖: ShortComplex, ShortComplex.exact_iff_exact_up_to_refinements, _exact.exact_up_to_refinements, cancel_mono, cat_disch, comp_id, condition, exact_iff_exact_up_to_refinements, exact_up_to_refinements, hom_ext, inv_hom_id, inv_hom_id_assoc, pullback, pullback.condition, pullback.fst, pullback.hom_ext, reassoc_of, zero_comp
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

/--
lemma `isIso_of_isIso` / 引理 `isIso_of_isIso`

English:
lemma isIso_of_isIso
  given: (f : S₁ ⟶ S₂) [IsIso f.τ₁] [IsIso f.τ₂] [IsIso f.τ₃]
  statement: IsIso f
  proof: (isoMk (asIso f.τ₁) (asIso f.τ₂) (asIso f.τ₃)).isIso_hom

中文:
引理 isIso_of_isIso
  条件: (f : S₁ ⟶ S₂) [IsIso f.τ₁] [IsIso f.τ₂] [IsIso f.τ₃]
  结论: IsIso f
  证明: (isoMk (asIso f.τ₁) (asIso f.τ₂) (asIso f.τ₃)).isIso_hom

Depends on / 依赖: isIso_hom
-/
lemma isIso_of_isIso (f : S₁ ⟶ S₂) [IsIso f.τ₁] [IsIso f.τ₂] [IsIso f.τ₃] : IsIso f :=
  (isoMk (asIso f.τ₁) (asIso f.τ₂) (asIso f.τ₃)).isIso_hom

/--
lemma `isIso_iff` / 引理 `isIso_iff`

English:
lemma isIso_iff
  given: (f : S₁ ⟶ S₂)
  proof: by
  refine ⟨fun _ => ⟨inferInstance, inferInstance, inferInstance⟩, ?_⟩
  rintro ⟨_, _, _⟩
  apply isIso_of_isIso

中文:
引理 isIso_iff
  条件: (f : S₁ ⟶ S₂)
  证明: by
  refine ⟨fun _ => ⟨inferInstance, inferInstance, inferInstance⟩, ?_⟩
  rintro ⟨_, _, _⟩
  apply isIso_of_isIso

Depends on / 依赖: isIso_of_isIso
-/
lemma isIso_iff (f : S₁ ⟶ S₂) :
    IsIso f ↔ IsIso f.τ₁ ∧ IsIso f.τ₂ ∧ IsIso f.τ₃ := by
  refine ⟨fun _ => ⟨inferInstance, inferInstance, inferInstance⟩, ?_⟩
  rintro ⟨_, _, _⟩
  apply isIso_of_isIso

/--
Definition of `fFunctor` / `fFunctor` 的定义

English:
definition fFunctor
  signature: : ShortComplex C ⥤ Arrow C where
  body: .mk S.f
  map {S T} f := Arrow.homMk f.τ₁ f.τ₂ f.comm₁₂

中文:
定义 fFunctor
  签名: : ShortComplex C ⥤ Arrow C where
  定义体: .mk S.f
  map {S T} f := Arrow.homMk f.τ₁ f.τ₂ f.comm₁₂
-/
@[simps] def fFunctor : ShortComplex C ⥤ Arrow C where
  obj S := .mk S.f
  map {S T} f := Arrow.homMk f.τ₁ f.τ₂ f.comm₁₂

/--
Definition of `gFunctor` / `gFunctor` 的定义

English:
definition gFunctor
  signature: : ShortComplex C ⥤ Arrow C where
  body: .mk S.g
  map {S T} f := Arrow.homMk f.τ₂ f.τ₃ f.comm₂₃

中文:
定义 gFunctor
  签名: : ShortComplex C ⥤ Arrow C where
  定义体: .mk S.g
  map {S T} f := Arrow.homMk f.τ₂ f.τ₃ f.comm₂₃
-/
@[simps] def gFunctor : ShortComplex C ⥤ Arrow C where
  obj S := .mk S.g
  map {S T} f := Arrow.homMk f.τ₂ f.τ₃ f.comm₂₃

/-- The opposite `ShortComplex` in `Cᵒᵖ` associated to a short complex in `C`. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: : ShortComplex Cᵒᵖ
  body: mk S.g.op S.f.op (by simp only [← op_comp, S.zero]; rfl)

中文:
定义 op
  签名: : ShortComplex Cᵒᵖ
  定义体: mk S.g.op S.f.op (by simp only [← op_comp, S.zero]; rfl)

Depends on / 依赖: S.f.op, S.g.op, S.zero, op_comp
-/
def op : ShortComplex Cᵒᵖ :=
  mk S.g.op S.f.op (by simp only [← op_comp, S.zero]; rfl)

set_option backward.defeqAttrib.useBackward true in
/-- The opposite morphism in `ShortComplex Cᵒᵖ` associated to a morphism in `ShortComplex C` -/
@[simps]
/--
Definition of `opMap` / `opMap` 的定义

English:
definition opMap
  signature: (φ : S₁ ⟶ S₂)
  body: φ.τ₃.op
  τ₂ := φ.τ₂.op
  τ₃ := φ.τ₁.op
  comm₁₂ := by
    dsimp
    simp only [← op_comp, φ.comm₂₃]
  comm₂₃ := by
    dsimp
    simp only [← op_comp, φ.comm₁₂]

@[simp]

中文:
定义 opMap
  签名: (φ : S₁ ⟶ S₂)
  定义体: φ.τ₃.op
  τ₂ := φ.τ₂.op
  τ₃ := φ.τ₁.op
  comm₁₂ := by
    dsimp
    simp only [← op_comp, φ.comm₂₃]
  comm₂₃ := by
    dsimp
    simp only [← op_comp, φ.comm₁₂]

@[simp]
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
/--
lemma `opMap_id` / 引理 `opMap_id`

English:
lemma opMap_id
  statement: opMap (𝟙 S) = 𝟙 S.op
  proof: rfl

中文:
引理 opMap_id
  结论: opMap (𝟙 S) = 𝟙 S.op
  证明: rfl
-/
lemma opMap_id : opMap (𝟙 S) = 𝟙 S.op := rfl

/-- The `ShortComplex` in `C` associated to a short complex in `Cᵒᵖ`. -/
@[simps]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: (S : ShortComplex Cᵒᵖ)
  body: mk S.g.unop S.f.unop (by simp only [← unop_comp, S.zero]; rfl)

中文:
定义 unop
  签名: (S : ShortComplex Cᵒᵖ)
  定义体: mk S.g.unop S.f.unop (by simp only [← unop_comp, S.zero]; rfl)

Depends on / 依赖: S.f.unop, S.g.unop, S.zero, unop_comp
-/
def unop (S : ShortComplex Cᵒᵖ) : ShortComplex C :=
  mk S.g.unop S.f.unop (by simp only [← unop_comp, S.zero]; rfl)

set_option backward.defeqAttrib.useBackward true in
/-- The morphism in `ShortComplex C` associated to a morphism in `ShortComplex Cᵒᵖ` -/
@[simps]
/--
Definition of `unopMap` / `unopMap` 的定义

English:
definition unopMap
  signature: {S₁ S₂ : ShortComplex Cᵒᵖ} (φ : S₁ ⟶ S₂)
  body: φ.τ₃.unop
  τ₂ := φ.τ₂.unop
  τ₃ := φ.τ₁.unop
  comm₁₂ := by
    dsimp
    simp only [← unop_comp, φ.comm₂₃]
  comm₂₃ := by
    dsimp
    simp only [← unop_comp, φ.comm₁₂]

@[simp]

中文:
定义 unopMap
  签名: {S₁ S₂ : ShortComplex Cᵒᵖ} (φ : S₁ ⟶ S₂)
  定义体: φ.τ₃.unop
  τ₂ := φ.τ₂.unop
  τ₃ := φ.τ₁.unop
  comm₁₂ := by
    dsimp
    simp only [← unop_comp, φ.comm₂₃]
  comm₂₃ := by
    dsimp
    simp only [← unop_comp, φ.comm₁₂]

@[simp]
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
/--
lemma `unopMap_id` / 引理 `unopMap_id`

English:
lemma unopMap_id
  given: (S : ShortComplex Cᵒᵖ)
  statement: unopMap (𝟙 S) = 𝟙 S.unop
  proof: rfl

中文:
引理 unopMap_id
  条件: (S : ShortComplex Cᵒᵖ)
  结论: unopMap (𝟙 S) = 𝟙 S.unop
  证明: rfl
-/
lemma unopMap_id (S : ShortComplex Cᵒᵖ) : unopMap (𝟙 S) = 𝟙 S.unop := rfl

variable (C)

/-- The obvious functor `(ShortComplex C)ᵒᵖ ⥤ ShortComplex Cᵒᵖ`. -/
@[simps]
/--
Definition of `opFunctor` / `opFunctor` 的定义

English:
definition opFunctor
  signature: : (ShortComplex C)ᵒᵖ ⥤ ShortComplex Cᵒᵖ where
  body: (Opposite.unop S).op
  map φ := opMap φ.unop

中文:
定义 opFunctor
  签名: : (ShortComplex C)ᵒᵖ ⥤ ShortComplex Cᵒᵖ where
  定义体: (Opposite.unop S).op
  map φ := opMap φ.unop

Depends on / 依赖: Opposite, Opposite.unop
-/
def opFunctor : (ShortComplex C)ᵒᵖ ⥤ ShortComplex Cᵒᵖ where
  obj S := (Opposite.unop S).op
  map φ := opMap φ.unop

/-- The obvious functor `ShortComplex Cᵒᵖ ⥤ (ShortComplex C)ᵒᵖ`. -/
@[simps]
/--
Definition of `unopFunctor` / `unopFunctor` 的定义

English:
definition unopFunctor
  signature: : ShortComplex Cᵒᵖ ⥤ (ShortComplex C)ᵒᵖ where
  body: Opposite.op (S.unop)
  map φ := (unopMap φ).op

中文:
定义 unopFunctor
  签名: : ShortComplex Cᵒᵖ ⥤ (ShortComplex C)ᵒᵖ where
  定义体: Opposite.op (S.unop)
  map φ := (unopMap φ).op

Depends on / 依赖: Opposite, Opposite.op, S.exact_C, S.snd_, S.unop, ShortComplex, ShortComplex.exact_iff_exact_up_to_refinements, _down.exact_up_to_refinements, comp_zero, exact_iff_exact_up_to_refinements, exact_up_to_refinements, pullback, pullback.fst, reassoc_of, surjective_up_to_refinements_of_epi
-/
def unopFunctor : ShortComplex Cᵒᵖ ⥤ (ShortComplex C)ᵒᵖ where
  obj S := Opposite.op (S.unop)
  map φ := (unopMap φ).op

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The obvious equivalence of categories `(ShortComplex C)ᵒᵖ ≌ ShortComplex Cᵒᵖ`. -/
@[simps]
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: : (ShortComplex C)ᵒᵖ ≌ ShortComplex Cᵒᵖ where
  body: opFunctor C
  inverse := unopFunctor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 opEquiv
  签名: : (ShortComplex C)ᵒᵖ ≌ ShortComplex Cᵒᵖ where
  定义体: opFunctor C
  inverse := unopFunctor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: opFunctor
-/
def opEquiv : (ShortComplex C)ᵒᵖ ≌ ShortComplex Cᵒᵖ where
  functor := opFunctor C
  inverse := unopFunctor C
  unitIso := Iso.refl _
  counitIso := Iso.refl _

variable {C}

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `unopOp` / `unopOp` 的定义

English:
abbreviation unopOp
  signature: (S : ShortComplex Cᵒᵖ)
  body: (opEquiv C).counitIso.app S

中文:
缩写 unopOp
  签名: (S : ShortComplex Cᵒᵖ)
  定义体: (opEquiv C).counitIso.app S

Depends on / 依赖: counitIso, counitIso.app, opEquiv, pushoutIsoUnopPullback
-/
abbrev unopOp (S : ShortComplex Cᵒᵖ) : S.unop.op ≅ S := (opEquiv C).counitIso.app S

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `opUnop` / `opUnop` 的定义

English:
abbreviation opUnop
  signature: (S : ShortComplex C)
  body: Iso.unop ((opEquiv C).unitIso.app (Opposite.op S))

中文:
缩写 opUnop
  签名: (S : ShortComplex C)
  定义体: Iso.unop ((opEquiv C).unitIso.app (Opposite.op S))

Depends on / 依赖: Iso.unop, Opposite, Opposite.op, opEquiv, unitIso, unitIso.app
-/
abbrev opUnop (S : ShortComplex C) : S.op.unop ≅ S :=
  Iso.unop ((opEquiv C).unitIso.app (Opposite.op S))

end ShortComplex

end CategoryTheory
