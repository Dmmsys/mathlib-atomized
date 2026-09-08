/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.CatCommSq
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# Resolutions for a morphism of localizers

Given a morphism of localizers `Φ : LocalizerMorphism W₁ W₂` (i.e. `W₁` and `W₂` are
morphism properties on categories `C₁` and `C₂`, and we have a functor
`Φ.functor : C₁ ⥤ C₂` which sends morphisms in `W₁` to morphisms in `W₂`), we introduce
the notion of right resolutions of objects in `C₂`, for `X₂ : C₂`.
A right resolution consists of an object `X₁ : C₁` and a morphism
`w : X₂ ⟶ Φ.functor.obj X₁` that is in `W₂`. Then, the typeclass
`Φ.HasRightResolutions` holds when any `X₂ : C₂` has a right resolution.

The type of right resolutions `Φ.RightResolution X₂` is endowed with a category
structure.

Similar definitions are done for left resolutions.

## Future work

* show that if `C` is an abelian category with enough injectives, there is a derivability
  structure associated to the inclusion of the full subcategory of complexes of injective
  objects into the bounded below homotopy category of `C` (TODO @joelriou)
* formalize dual results

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

@[expose] public section

universe v₁ v₂ v₂' u₁ u₂ u₂'

namespace CategoryTheory

open Category Localization

variable {C₁ C₂ D₁ D₂ H : Type*}
  [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂] [Category* H]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {W₁' : MorphismProperty D₁} {W₂' : MorphismProperty D₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)

/-- The category of right resolutions of an object in the target category
of a localizer morphism. -/
/-
**CategoryTheory.LocalizerMorphism.RightResolution** 是 Mathlib 中的一个归纳类型，位于命名空间 `
CategoryTheory.LocalizerMorphism`。
形式化陈述：{C₁ : Type u_1} →   {C₂ : Type u_2} →     [inst : CategoryTheory.Category.
{v_1, u_1} C₁] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] →       
  {W₁ : CategoryTheory.MorphismProperty C₁} →           {W₂ : CategoryTheory.Mor
phismProperty C₂} → CategoryTheory.LocalizerMorphism W₁ W₂ → C₂ → Type (max u_1 
v_2)
参数：max u_1 v_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of right resolutions of an object in the target category
of a localizer morphism.
-/
structure RightResolution (X₂ : C₂) where
  /-- an object in the source category -/
  {X₁ : C₁}
  /-- a morphism to an object of the form `Φ.functor.obj X₁` -/
  w : X₂ ⟶ Φ.functor.obj X₁
  hw : W₂ w

/-- The category of left resolutions of an object in the target category
of a localizer morphism. -/
/-
**CategoryTheory.LocalizerMorphism.LeftResolution** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.LocalizerMorphism`。
形式化陈述：{C₁ : Type u_1} →   {C₂ : Type u_2} →     [inst : CategoryTheory.Category.
{v_1, u_1} C₁] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] →       
  {W₁ : CategoryTheory.MorphismProperty C₁} →           {W₂ : CategoryTheory.Mor
phismProperty C₂} → CategoryTheory.LocalizerMorphism W₁ W₂ → C₂ → Type (max u_1 
v_2)
参数：max u_1 v_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of left resolutions of an object in the target category
of a localizer morphism.
-/
structure LeftResolution (X₂ : C₂) where
  /-- an object in the source category -/
  {X₁ : C₁}
  /-- a morphism from an object of the form `Φ.functor.obj X₁` -/
  w : Φ.functor.obj X₁ ⟶ X₂
  hw : W₂ w

variable {Φ X₂} in
/-
**CategoryTheory.LocalizerMorphism.RightResolution.mk_surjective** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.LocalizerMorphism.RightResolution`。
形式化陈述：∀ {C₁ : Type u_1} {C₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_
1} C₁]   [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] {W₁ : CategoryTheory.M
orphismProperty C₁}   {W₂ : CategoryTheory.MorphismProperty C₂} {Φ : CategoryThe
ory.LocalizerMorphism W₁ W₂} {X₂ : C₂}   (R : Φ.RightResolution X₂), ∃ X₁ w, ∃ (
hw : W₂ w), R = { X₁ := X₁, w := w, hw := hw }
参数：R : Φ.RightResolution X₂；hw : W₂ w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.LocalizerMorphism.RightResolution.hw`：∀ {C₁ : Type u_1} {
C₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
-/
lemma RightResolution.mk_surjective (R : Φ.RightResolution X₂) :
    ∃ (X₁ : C₁) (w : X₂ ⟶ Φ.functor.obj X₁) (hw : W₂ w), R = RightResolution.mk w hw :=
  ⟨_, R.w, R.hw, rfl⟩

variable {Φ X₂} in
/-
**CategoryTheory.LocalizerMorphism.LeftResolution.mk_surjective** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.LocalizerMorphism.LeftResolution`。
形式化陈述：∀ {C₁ : Type u_1} {C₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_
1} C₁]   [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] {W₁ : CategoryTheory.M
orphismProperty C₁}   {W₂ : CategoryTheory.MorphismProperty C₂} {Φ : CategoryThe
ory.LocalizerMorphism W₁ W₂} {X₂ : C₂}   (L : Φ.LeftResolution X₂), ∃ X₁ w, ∃ (h
w : W₂ w), L = { X₁ := X₁, w := w, hw := hw }
参数：L : Φ.LeftResolution X₂；hw : W₂ w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.LocalizerMorphism.LeftResolution.hw`：∀ {C₁ : Type u_1} {C
₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
-/
lemma LeftResolution.mk_surjective (L : Φ.LeftResolution X₂) :
    ∃ (X₁ : C₁) (w : Φ.functor.obj X₁ ⟶ X₂) (hw : W₂ w), L = LeftResolution.mk w hw :=
  ⟨_, L.w, L.hw, rfl⟩

/-- A localizer morphism has right resolutions when any object has a right resolution. -/
/-
**CategoryTheory.LocalizerMorphism.HasRightResolutions** 是 Mathlib 中的一个缩写定义，位于命名
空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：HasRightResolutions
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A localizer morphism has right resolutions when any object has a right resolutio
n.
-/
abbrev HasRightResolutions := ∀ (X₂ : C₂), Nonempty (Φ.RightResolution X₂)

/-- A localizer morphism has left resolutions when any object has a left resolution. -/
/-
**CategoryTheory.LocalizerMorphism.HasLeftResolutions** 是 Mathlib 中的一个缩写定义，位于命名空
间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：HasLeftResolutions
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A localizer morphism has left resolutions when any object has a left resolution.
-/
abbrev HasLeftResolutions := ∀ (X₂ : C₂), Nonempty (Φ.LeftResolution X₂)

namespace RightResolution

variable {Φ} {X₂ : C₂}

/-- The type of morphisms in the category `Φ.RightResolution X₂`. -/
@[ext]
/-
**CategoryTheory.LocalizerMorphism.RightResolution.Hom** 是 Mathlib 中的一个结构，位于命名空间
 `CategoryTheory.LocalizerMorphism.RightResolution`。
形式化陈述：Hom (R R' : Φ.RightResolution X₂) where /-- a morphism in the source categ
ory -/ f : R.X₁ ⟶ R'.X₁ comm : R.w ≫ Φ.functor.map f = R'.w
参数：R R' : Φ.RightResolution X₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in the category `Φ.RightResolution X₂`.
-/
structure Hom (R R' : Φ.RightResolution X₂) where
  /-- a morphism in the source category -/
  f : R.X₁ ⟶ R'.X₁
  comm : R.w ≫ Φ.functor.map f = R'.w := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

/-- The identity of an object in `Φ.RightResolution X₂`. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.RightResolution.Hom.id** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.LocalizerMorphism.RightResolution.Hom`。
形式化陈述：{C₁ : Type u_1} →   {C₂ : Type u_2} →     [inst : CategoryTheory.Category.
{v_1, u_1} C₁] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] →       
  {W₁ : CategoryTheory.MorphismProperty C₁} →           {W₂ : CategoryTheory.Mor
phismProperty C₂} →             {Φ : CategoryTheory.LocalizerMorphism W₁ W₂} → {
X₂ : C₂} → (R : Φ.RightResolution X₂) → R.Hom R
参数：R : Φ.RightResolution X₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity of an object in `Φ.RightResolution X₂`.
-/
def Hom.id (R : Φ.RightResolution X₂) : Hom R R where
  f := 𝟙 _

/-- The composition of morphisms in `Φ.RightResolution X₂`. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.RightResolution.Hom.comp** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.LocalizerMorphism.RightResolution.Hom`。
形式化陈述：{C₁ : Type u_1} →   {C₂ : Type u_2} →     [inst : CategoryTheory.Category.
{v_1, u_1} C₁] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] →       
  {W₁ : CategoryTheory.MorphismProperty C₁} →           {W₂ : CategoryTheory.Mor
phismProperty C₂} →             {Φ : CategoryTheory.LocalizerMorphism W₁ W₂} →  
             {X₂ : C₂} → {R R' R'' : Φ.RightResolution X₂} → R.Hom R' → R'.Hom R
'' → R.Hom R''
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of morphisms in `Φ.RightResolution X₂`.
-/
def Hom.comp {R R' R'' : Φ.RightResolution X₂}
    (φ : Hom R R') (ψ : Hom R' R'') :
    Hom R R'' where
  f := φ.f ≫ ψ.f
/-
**CategoryTheory.LocalizerMorphism.RightResolution.** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.LocalizerMorphism.RightResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Φ.RightResolution X₂) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[simp]
/-
**CategoryTheory.LocalizerMorphism.RightResolution.id_f** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.LocalizerMorphism.RightResolution`。
形式化陈述：id_f (R : Φ.RightResolution X₂) : Hom.f (𝟙 R) = 𝟙 R.X₁
参数：R : Φ.RightResolution X₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_f (R : Φ.RightResolution X₂) : Hom.f (𝟙 R) = 𝟙 R.X₁ := rfl

@[simp, reassoc]
/-
**CategoryTheory.LocalizerMorphism.RightResolution.comp_f** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.LocalizerMorphism.RightResolution`。
形式化陈述：comp_f {R R' R'' : Φ.RightResolution X₂} (φ : R ⟶ R') (ψ : R' ⟶ R'') : (φ 
≫ ψ).f = φ.f ≫ ψ.f
参数：φ : R ⟶ R'；ψ : R' ⟶ R''。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_f {R R' R'' : Φ.RightResolution X₂} (φ : R ⟶ R') (ψ : R' ⟶ R'') :
    (φ ≫ ψ).f = φ.f ≫ ψ.f := rfl

@[ext]
/-
**CategoryTheory.LocalizerMorphism.RightResolution.hom_ext** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.LocalizerMorphism.RightResolution`。
形式化陈述：hom_ext {R R' : Φ.RightResolution X₂} {φ₁ φ₂ : R ⟶ R'} (h : φ₁.f = φ₂.f) :
 φ₁ = φ₂
参数：h : φ₁.f = φ₂.f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.LocalizerMorphism.RightResolution.Hom.ext`：∀ {C₁ : Type u
_1} {C₂ : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C₁}   {inst_1 : C
ategoryTheory.Category.{v_2, u_2} C₂} {W₁ : Ca…
-/
lemma hom_ext {R R' : Φ.RightResolution X₂} {φ₁ φ₂ : R ⟶ R'} (h : φ₁.f = φ₂.f) :
    φ₁ = φ₂ :=
  Hom.ext h

end RightResolution

namespace LeftResolution

variable {Φ} {X₂ : C₂}

/-- The type of morphisms in the category `Φ.LeftResolution X₂`. -/
@[ext]
/-
**CategoryTheory.LocalizerMorphism.LeftResolution.Hom** 是 Mathlib 中的一个结构，位于命名空间 
`CategoryTheory.LocalizerMorphism.LeftResolution`。
形式化陈述：Hom (L L' : Φ.LeftResolution X₂) where /-- a morphism in the source catego
ry -/ f : L.X₁ ⟶ L'.X₁ comm : Φ.functor.map f ≫ L'.w = L.w
参数：L L' : Φ.LeftResolution X₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in the category `Φ.LeftResolution X₂`.
-/
structure Hom (L L' : Φ.LeftResolution X₂) where
  /-- a morphism in the source category -/
  f : L.X₁ ⟶ L'.X₁
  comm : Φ.functor.map f ≫ L'.w = L.w := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

/-- The identity of an object in `Φ.LeftResolution X₂`. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.LeftResolution.Hom.id** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.LocalizerMorphism.LeftResolution.Hom`。
形式化陈述：{C₁ : Type u_1} →   {C₂ : Type u_2} →     [inst : CategoryTheory.Category.
{v_1, u_1} C₁] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] →       
  {W₁ : CategoryTheory.MorphismProperty C₁} →           {W₂ : CategoryTheory.Mor
phismProperty C₂} →             {Φ : CategoryTheory.LocalizerMorphism W₁ W₂} → {
X₂ : C₂} → (L : Φ.LeftResolution X₂) → L.Hom L
参数：L : Φ.LeftResolution X₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity of an object in `Φ.LeftResolution X₂`.
-/
def Hom.id (L : Φ.LeftResolution X₂) : Hom L L where
  f := 𝟙 _

/-- The composition of morphisms in `Φ.LeftResolution X₂`. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.LeftResolution.Hom.comp** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.LocalizerMorphism.LeftResolution.Hom`。
形式化陈述：{C₁ : Type u_1} →   {C₂ : Type u_2} →     [inst : CategoryTheory.Category.
{v_1, u_1} C₁] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] →       
  {W₁ : CategoryTheory.MorphismProperty C₁} →           {W₂ : CategoryTheory.Mor
phismProperty C₂} →             {Φ : CategoryTheory.LocalizerMorphism W₁ W₂} →  
             {X₂ : C₂} → {L L' L'' : Φ.LeftResolution X₂} → L.Hom L' → L'.Hom L'
' → L.Hom L''
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of morphisms in `Φ.LeftResolution X₂`.
-/
def Hom.comp {L L' L'' : Φ.LeftResolution X₂}
    (φ : Hom L L') (ψ : Hom L' L'') :
    Hom L L'' where
  f := φ.f ≫ ψ.f
/-
**CategoryTheory.LocalizerMorphism.LeftResolution.** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.LocalizerMorphism.LeftResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Φ.LeftResolution X₂) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[simp]
/-
**CategoryTheory.LocalizerMorphism.LeftResolution.id_f** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.LocalizerMorphism.LeftResolution`。
形式化陈述：id_f (L : Φ.LeftResolution X₂) : Hom.f (𝟙 L) = 𝟙 L.X₁
参数：L : Φ.LeftResolution X₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_f (L : Φ.LeftResolution X₂) : Hom.f (𝟙 L) = 𝟙 L.X₁ := rfl

@[simp, reassoc]
/-
**CategoryTheory.LocalizerMorphism.LeftResolution.comp_f** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.LocalizerMorphism.LeftResolution`。
形式化陈述：comp_f {L L' L'' : Φ.LeftResolution X₂} (φ : L ⟶ L') (ψ : L' ⟶ L'') : (φ ≫
 ψ).f = φ.f ≫ ψ.f
参数：φ : L ⟶ L'；ψ : L' ⟶ L''。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_f {L L' L'' : Φ.LeftResolution X₂} (φ : L ⟶ L') (ψ : L' ⟶ L'') :
    (φ ≫ ψ).f = φ.f ≫ ψ.f := rfl

@[ext]
/-
**CategoryTheory.LocalizerMorphism.LeftResolution.hom_ext** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.LocalizerMorphism.LeftResolution`。
形式化陈述：hom_ext {L L' : Φ.LeftResolution X₂} {φ₁ φ₂ : L ⟶ L'} (h : φ₁.f = φ₂.f) : 
φ₁ = φ₂
参数：h : φ₁.f = φ₂.f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.LocalizerMorphism.LeftResolution.Hom.ext`：∀ {C₁ : Type u_
1} {C₂ : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C₁}   {inst_1 : Ca
tegoryTheory.Category.{v_2, u_2} C₂} {W₁ : Ca…
-/
lemma hom_ext {L L' : Φ.LeftResolution X₂} {φ₁ φ₂ : L ⟶ L'} (h : φ₁.f = φ₂.f) :
    φ₁ = φ₂ :=
  Hom.ext h

end LeftResolution

variable {Φ}

/-- The canonical map `Φ.LeftResolution X₂ → Φ.op.RightResolution (Opposite.op X₂)`. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.LeftResolution.op** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.LocalizerMorphism.LeftResolution`。
形式化陈述：{C₁ : Type u_1} →   {C₂ : Type u_2} →     [inst : CategoryTheory.Category.
{v_1, u_1} C₁] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] →       
  {W₁ : CategoryTheory.MorphismProperty C₁} →           {W₂ : CategoryTheory.Mor
phismProperty C₂} →             {Φ : CategoryTheory.LocalizerMorphism W₁ W₂} →  
             {X₂ : C₂} → Φ.LeftResolution X₂ → Φ.op.RightResolution (Opposite.op
 X₂)
参数：Opposite.op X₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.LocalizerMorphism.LeftResolution.hw`：∀ {C₁ : Type u_1} {C
₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…

--- 原说明 ---
The canonical map `Φ.LeftResolution X₂ → Φ.op.RightResolution (Opposite.op X₂)`.
-/
def LeftResolution.op {X₂ : C₂} (L : Φ.LeftResolution X₂) :
    Φ.op.RightResolution (Opposite.op X₂) where
  X₁ := Opposite.op L.X₁
  w := L.w.op
  hw := L.hw

/-- The canonical map `Φ.op.LeftResolution X₂ → Φ.RightResolution X₂`. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.LeftResolution.unop** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.LocalizerMorphism.LeftResolution`。
形式化陈述：{C₁ : Type u_1} →   {C₂ : Type u_2} →     [inst : CategoryTheory.Category.
{v_1, u_1} C₁] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] →       
  {W₁ : CategoryTheory.MorphismProperty C₁} →           {W₂ : CategoryTheory.Mor
phismProperty C₂} →             {Φ : CategoryTheory.LocalizerMorphism W₁ W₂} →  
             {X₂ : C₂ᵒᵖ} → Φ.op.LeftResolution X₂ → Φ.RightResolution (Opposite.
unop X₂)
参数：Opposite.unop X₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `Φ.op.LeftResolution X₂ → Φ.RightResolution X₂`.
-/
def LeftResolution.unop {X₂ : C₂ᵒᵖ} (L : Φ.op.LeftResolution X₂) :
    Φ.RightResolution X₂.unop where
  X₁ := Opposite.unop L.X₁
  w := L.w.unop
  hw := L.hw

/-- The canonical map `Φ.RightResolution X₂ → Φ.op.LeftResolution (Opposite.op X₂)`. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.RightResolution.op** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.LocalizerMorphism.RightResolution`。
形式化陈述：{C₁ : Type u_1} →   {C₂ : Type u_2} →     [inst : CategoryTheory.Category.
{v_1, u_1} C₁] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] →       
  {W₁ : CategoryTheory.MorphismProperty C₁} →           {W₂ : CategoryTheory.Mor
phismProperty C₂} →             {Φ : CategoryTheory.LocalizerMorphism W₁ W₂} →  
             {X₂ : C₂} → Φ.RightResolution X₂ → Φ.op.LeftResolution (Opposite.op
 X₂)
参数：Opposite.op X₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.LocalizerMorphism.RightResolution.hw`：∀ {C₁ : Type u_1} {
C₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…

--- 原说明 ---
The canonical map `Φ.RightResolution X₂ → Φ.op.LeftResolution (Opposite.op X₂)`.
-/
def RightResolution.op {X₂ : C₂} (L : Φ.RightResolution X₂) :
    Φ.op.LeftResolution (Opposite.op X₂) where
  X₁ := Opposite.op L.X₁
  w := L.w.op
  hw := L.hw

/-- The canonical map `Φ.op.RightResolution X₂ → Φ.LeftResolution X₂`. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.RightResolution.unop** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.LocalizerMorphism.RightResolution`。
形式化陈述：{C₁ : Type u_1} →   {C₂ : Type u_2} →     [inst : CategoryTheory.Category.
{v_1, u_1} C₁] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] →       
  {W₁ : CategoryTheory.MorphismProperty C₁} →           {W₂ : CategoryTheory.Mor
phismProperty C₂} →             {Φ : CategoryTheory.LocalizerMorphism W₁ W₂} →  
             {X₂ : C₂ᵒᵖ} → Φ.op.RightResolution X₂ → Φ.LeftResolution (Opposite.
unop X₂)
参数：Opposite.unop X₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `Φ.op.RightResolution X₂ → Φ.LeftResolution X₂`.
-/
def RightResolution.unop {X₂ : C₂ᵒᵖ} (L : Φ.op.RightResolution X₂) :
    Φ.LeftResolution X₂.unop where
  X₁ := Opposite.unop L.X₁
  w := L.w.unop
  hw := L.hw

variable (Φ)
/-
**CategoryTheory.LocalizerMorphism.nonempty_leftResolution_iff_op** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：nonempty_leftResolution_iff_op (X₂ : C₂) : Nonempty (Φ.LeftResolution X₂) 
↔ Nonempty (Φ.op.RightResolution (Opposite.op X₂))
参数：X₂ : C₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
-/
lemma nonempty_leftResolution_iff_op (X₂ : C₂) :
    Nonempty (Φ.LeftResolution X₂) ↔ Nonempty (Φ.op.RightResolution (Opposite.op X₂)) :=
  Equiv.nonempty_congr
    { toFun := fun L => L.op
      invFun := fun R => R.unop }
/-
**CategoryTheory.LocalizerMorphism.nonempty_rightResolution_iff_op** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：nonempty_rightResolution_iff_op (X₂ : C₂) : Nonempty (Φ.RightResolution X₂
) ↔ Nonempty (Φ.op.LeftResolution (Opposite.op X₂))
参数：X₂ : C₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
-/
lemma nonempty_rightResolution_iff_op (X₂ : C₂) :
    Nonempty (Φ.RightResolution X₂) ↔ Nonempty (Φ.op.LeftResolution (Opposite.op X₂)) :=
  Equiv.nonempty_congr
    { toFun := fun R => R.op
      invFun := fun L => L.unop }
/-
**CategoryTheory.LocalizerMorphism.hasLeftResolutions_iff_op** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：hasLeftResolutions_iff_op : Φ.HasLeftResolutions ↔ Φ.op.HasRightResolution
s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasLeftResolutions_iff_op : Φ.HasLeftResolutions ↔ Φ.op.HasRightResolutions :=
  ⟨fun _ X₂ => ⟨(Classical.arbitrary (Φ.LeftResolution X₂.unop)).op⟩,
    fun _ X₂ => ⟨(Classical.arbitrary (Φ.op.RightResolution (Opposite.op X₂))).unop⟩⟩
/-
**CategoryTheory.LocalizerMorphism.hasRightResolutions_iff_op** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：hasRightResolutions_iff_op : Φ.HasRightResolutions ↔ Φ.op.HasLeftResolutio
ns
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasRightResolutions_iff_op : Φ.HasRightResolutions ↔ Φ.op.HasLeftResolutions :=
  ⟨fun _ X₂ => ⟨(Classical.arbitrary (Φ.RightResolution X₂.unop)).op⟩,
    fun _ X₂ => ⟨(Classical.arbitrary (Φ.op.LeftResolution (Opposite.op X₂))).unop⟩⟩
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Φ.HasRightResolutions] : Φ.op.HasLeftResolutions := by
  rwa [← hasRightResolutions_iff_op]
/-
**CategoryTheory.LocalizerMorphism.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Lo
calizerMorphism`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Φ.HasLeftResolutions] : Φ.op.HasRightResolutions := by
  rwa [← hasLeftResolutions_iff_op]

/-- The functor `(Φ.LeftResolution X₂)ᵒᵖ ⥤ Φ.op.RightResolution (Opposite.op X₂)`. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.LeftResolution.opFunctor** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.LocalizerMorphism.LeftResolution`。
形式化陈述：{C₁ : Type u_1} →   {C₂ : Type u_2} →     [inst : CategoryTheory.Category.
{v_1, u_1} C₁] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] →       
  {W₁ : CategoryTheory.MorphismProperty C₁} →           {W₂ : CategoryTheory.Mor
phismProperty C₂} →             (Φ : CategoryTheory.LocalizerMorphism W₁ W₂) →  
             (X₂ : C₂) → CategoryTheory.Functor (Φ.LeftResolution X₂)ᵒᵖ (Φ.op.Ri
ghtResolution (Opposite.op X₂))
参数：Φ : CategoryTheory.LocalizerMorphism W₁ W₂；X₂ : C₂；Φ.LeftResolution X₂；Φ.op.R
ightResolution (Opposite.op X₂)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `(Φ.LeftResolution X₂)ᵒᵖ ⥤ Φ.op.RightResolution (Opposite.op X₂)`.
-/
def LeftResolution.opFunctor (X₂ : C₂) :
    (Φ.LeftResolution X₂)ᵒᵖ ⥤ Φ.op.RightResolution (Opposite.op X₂) where
  obj L := L.unop.op
  map φ :=
    { f := φ.unop.f.op
      comm := Quiver.Hom.unop_inj φ.unop.comm }

/-- The functor `(Φ.op.RightResolution X₂)ᵒᵖ ⥤ Φ.LeftResolution X₂.unop`. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.RightResolution.unopFunctor** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.LocalizerMorphism.RightResolution`。
形式化陈述：{C₁ : Type u_1} →   {C₂ : Type u_2} →     [inst : CategoryTheory.Category.
{v_1, u_1} C₁] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] →       
  {W₁ : CategoryTheory.MorphismProperty C₁} →           {W₂ : CategoryTheory.Mor
phismProperty C₂} →             (Φ : CategoryTheory.LocalizerMorphism W₁ W₂) →  
             (X₂ : C₂ᵒᵖ) → CategoryTheory.Functor (Φ.op.RightResolution X₂)ᵒᵖ (Φ
.LeftResolution (Opposite.unop X₂))
参数：Φ : CategoryTheory.LocalizerMorphism W₁ W₂；X₂ : C₂ᵒᵖ；Φ.op.RightResolution X₂；
Φ.LeftResolution (Opposite.unop X₂)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `(Φ.op.RightResolution X₂)ᵒᵖ ⥤ Φ.LeftResolution X₂.unop`.
-/
def RightResolution.unopFunctor (X₂ : C₂ᵒᵖ) :
    (Φ.op.RightResolution X₂)ᵒᵖ ⥤ Φ.LeftResolution X₂.unop where
  obj R := R.unop.unop
  map φ :=
    { f := φ.unop.f.unop
      comm := Quiver.Hom.op_inj φ.unop.comm }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories
`(Φ.LeftResolution X₂)ᵒᵖ ≌ Φ.op.RightResolution (Opposite.op X₂)`. -/
@[simps]
/-
**CategoryTheory.LocalizerMorphism.LeftResolution.opEquivalence** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.LocalizerMorphism.LeftResolution`。
形式化陈述：{C₁ : Type u_1} →   {C₂ : Type u_2} →     [inst : CategoryTheory.Category.
{v_1, u_1} C₁] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} C₂] →       
  {W₁ : CategoryTheory.MorphismProperty C₁} →           {W₂ : CategoryTheory.Mor
phismProperty C₂} →             (Φ : CategoryTheory.LocalizerMorphism W₁ W₂) →  
             (X₂ : C₂) → (Φ.LeftResolution X₂)ᵒᵖ ≌ Φ.op.RightResolution (Opposit
e.op X₂)
参数：Φ : CategoryTheory.LocalizerMorphism W₁ W₂；X₂ : C₂；Φ.LeftResolution X₂；Opposi
te.op X₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories
`(Φ.LeftResolution X₂)ᵒᵖ ≌ Φ.op.RightResolution (Opposite.op X₂)`.
-/
def LeftResolution.opEquivalence (X₂ : C₂) :
    (Φ.LeftResolution X₂)ᵒᵖ ≌ Φ.op.RightResolution (Opposite.op X₂) where
  functor := LeftResolution.opFunctor Φ X₂
  inverse := (RightResolution.unopFunctor Φ (Opposite.op X₂)).rightOp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

section

variable (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]

/-
**CategoryTheory.LocalizerMorphism.essSurj_of_hasRightResolutions** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：essSurj_of_hasRightResolutions [Φ.HasRightResolutions] : (Φ.functor ⋙ L₂).
EssSurj where mem_essImage X₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj
· 使用定理 `CategoryTheory.LocalizerMorphism.RightResolution.hw`：∀ {C₁ : Type u_1} {
C₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
-/
lemma essSurj_of_hasRightResolutions [Φ.HasRightResolutions] : (Φ.functor ⋙ L₂).EssSurj where
  mem_essImage X₂ := by
    have := Localization.essSurj L₂ W₂
    have R : Φ.RightResolution (L₂.objPreimage X₂) := Classical.arbitrary _
    exact ⟨R.X₁, ⟨(Localization.isoOfHom L₂ W₂ _ R.hw).symm ≪≫ L₂.objObjPreimageIso X₂⟩⟩
/-
**CategoryTheory.LocalizerMorphism.isIso_iff_of_hasRightResolutions** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isIso_iff_of_hasRightResolutions [Φ.HasRightResolutions] {F G : D₂ ⥤ H} (α
 : F ⟶ G) : IsIso α ↔ forall (X₁ : C₁), IsIso (α.app (L₂.obj (Φ.functor.obj X₁))
)
参数：α : F ⟶ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.LocalizerMorphism.essSurj_of_hasRightResolutions`：essSurj
_of_hasRightResolutions [Φ.HasRightResolutions] : (Φ.functor ⋙ L₂).EssSurj where
 mem_essImage X₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.NatTrans.isIso_app_iff_of_iso`：isIso_app_iff_of_iso {F G 
: C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) : IsIso (α.app X) ↔ IsIso (α.app Y)
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
-/
lemma isIso_iff_of_hasRightResolutions [Φ.HasRightResolutions] {F G : D₂ ⥤ H} (α : F ⟶ G) :
    IsIso α ↔ ∀ (X₁ : C₁), IsIso (α.app (L₂.obj (Φ.functor.obj X₁))) := by
  constructor
  · intros
    infer_instance
  · intro hα
    have : ∀ (X₂ : D₂), IsIso (α.app X₂) := fun X₂ => by
      have := Φ.essSurj_of_hasRightResolutions L₂
      rw [← NatTrans.isIso_app_iff_of_iso α ((Φ.functor ⋙ L₂).objObjPreimageIso X₂)]
      apply hα
    exact NatIso.isIso_of_isIso_app α
/-
**CategoryTheory.LocalizerMorphism.essSurj_of_hasLeftResolutions** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：essSurj_of_hasLeftResolutions [Φ.HasLeftResolutions] : (Φ.functor ⋙ L₂).Es
sSurj where mem_essImage X₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.essSurj`：essSurj (W) [L.IsLocalization W] : 
L.EssSurj
· 使用定理 `CategoryTheory.LocalizerMorphism.LeftResolution.hw`：∀ {C₁ : Type u_1} {C
₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
-/
lemma essSurj_of_hasLeftResolutions [Φ.HasLeftResolutions] : (Φ.functor ⋙ L₂).EssSurj where
  mem_essImage X₂ := by
    have := Localization.essSurj L₂ W₂
    have L : Φ.LeftResolution (L₂.objPreimage X₂) := Classical.arbitrary _
    exact ⟨L.X₁, ⟨Localization.isoOfHom L₂ W₂ _ L.hw ≪≫ L₂.objObjPreimageIso X₂⟩⟩
/-
**CategoryTheory.LocalizerMorphism.isIso_iff_of_hasLeftResolutions** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：isIso_iff_of_hasLeftResolutions [Φ.HasLeftResolutions] {F G : D₂ ⥤ H} (α :
 F ⟶ G) : IsIso α ↔ forall (X₁ : C₁), IsIso (α.app (L₂.obj (Φ.functor.obj X₁)))
参数：α : F ⟶ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.LocalizerMorphism.essSurj_of_hasLeftResolutions`：essSurj_
of_hasLeftResolutions [Φ.HasLeftResolutions] : (Φ.functor ⋙ L₂).EssSurj where me
m_essImage X₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.NatTrans.isIso_app_iff_of_iso`：isIso_app_iff_of_iso {F G 
: C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) : IsIso (α.app X) ↔ IsIso (α.app Y)
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
-/
lemma isIso_iff_of_hasLeftResolutions [Φ.HasLeftResolutions] {F G : D₂ ⥤ H} (α : F ⟶ G) :
    IsIso α ↔ ∀ (X₁ : C₁), IsIso (α.app (L₂.obj (Φ.functor.obj X₁))) := by
  constructor
  · intros
    infer_instance
  · intro hα
    have : ∀ (X₂ : D₂), IsIso (α.app X₂) := fun X₂ => by
      have := Φ.essSurj_of_hasLeftResolutions L₂
      rw [← NatTrans.isIso_app_iff_of_iso α ((Φ.functor ⋙ L₂).objObjPreimageIso X₂)]
      apply hα
    exact NatIso.isIso_of_isIso_app α

end

section

variable {T : LocalizerMorphism W₁ W₂} {L : LocalizerMorphism W₁ W₁'}
  {R : LocalizerMorphism W₂ W₂'} {B : LocalizerMorphism W₁' W₂'}

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.LocalizerMorphism.hasRightResolutions_of_iso_of_essSurj** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：hasRightResolutions_of_iso_of_essSurj [R.functor.EssSurj] [W₂'.RespectsIso
] (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [T.HasRightResolutions] 
: B.HasRightResolutions
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EssSurj.mem_essImage`：∀ {C : Type u₁} {D : Type u
₂} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   (F : CategoryTheor…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.LocalizerMorphism.map`：∀ {C₁ : Type u₁} {C₂ : Type u₂} [i
nst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{
v₂, u₂} C₂] {W₁ : Category…
· 使用定理 `CategoryTheory.LocalizerMorphism.RightResolution.hw`：∀ {C₁ : Type u_1} {
C₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
-/
lemma hasRightResolutions_of_iso_of_essSurj
    [R.functor.EssSurj] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [T.HasRightResolutions] :
    B.HasRightResolutions := by
  intro Y₂
  obtain ⟨X₂, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := R.functor) Y₂
  let ρ : T.RightResolution X₂ := Classical.arbitrary _
  exact ⟨{
    X₁ := L.functor.obj ρ.X₁
    w := e.inv ≫ R.functor.map ρ.w ≫ iso.hom.app _
    hw := (W₂'.arrow_mk_iso_iff (Arrow.isoMk e (iso.app _))).1 (R.map _ ρ.hw) }⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.LocalizerMorphism.hasLeftResolutions_of_iso_of_essSurj** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：hasLeftResolutions_of_iso_of_essSurj [R.functor.EssSurj] [W₂'.RespectsIso]
 (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [T.HasLeftResolutions] : 
B.HasLeftResolutions
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EssSurj.mem_essImage`：∀ {C : Type u₁} {D : Type u
₂} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   (F : CategoryTheor…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.LocalizerMorphism.map`：∀ {C₁ : Type u₁} {C₂ : Type u₂} [i
nst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{
v₂, u₂} C₂] {W₁ : Category…
· 使用定理 `CategoryTheory.LocalizerMorphism.LeftResolution.hw`：∀ {C₁ : Type u_1} {C
₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
-/
lemma hasLeftResolutions_of_iso_of_essSurj
    [R.functor.EssSurj] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [T.HasLeftResolutions] :
    B.HasLeftResolutions := by
  intro Y₂
  obtain ⟨X₂, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := R.functor) Y₂
  let ρ : T.LeftResolution X₂ := Classical.arbitrary _
  exact ⟨{
    X₁ := L.functor.obj ρ.X₁
    w := iso.inv.app _ ≫ R.functor.map ρ.w ≫ e.hom
    hw := (W₂'.arrow_mk_iso_iff (Arrow.isoMk (iso.app _) e)).1 (R.map _ ρ.hw) }⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.LocalizerMorphism.hasRightResolutions_of_iso_of_essSurj_of_full
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：hasRightResolutions_of_iso_of_essSurj_of_full [L.functor.EssSurj] [R.funct
or.Full] [R.IsInduced] [W₂'.RespectsIso] (iso : T.functor ⋙ R.functor ≅ L.functo
r ⋙ B.functor) [B.HasRightResolutions] : T.HasRightResolutions
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EssSurj.mem_essImage`：∀ {C : Type u₁} {D : Type u
₂} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   (F : CategoryTheor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.LocalizerMorphism.IsInduced.inverseImage_eq`：∀ {C₁ : Type
 u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} C₁}   {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Iso.map_inv_hom_id`：map_inv_hom_id (F : C ⥤ D) : F.map e.
inv ≫ F.map e.hom = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.LocalizerMorphism.RightResolution.hw`：∀ {C₁ : Type u_1} {
C₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
-/
lemma hasRightResolutions_of_iso_of_essSurj_of_full
    [L.functor.EssSurj] [R.functor.Full] [R.IsInduced] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [B.HasRightResolutions] :
    T.HasRightResolutions := by
  intro X₂
  let ρ : B.RightResolution (R.functor.obj X₂) := Classical.arbitrary _
  obtain ⟨X₁, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage L.functor ρ.X₁
  exact ⟨{
    X₁ := X₁
    w := R.functor.preimage (ρ.w ≫ B.functor.map e.inv ≫ iso.inv.app X₁)
    hw := by
      simp only [← R.inverseImage_eq, MorphismProperty.inverseImage_iff, Functor.map_preimage]
      refine (W₂'.arrow_mk_iso_iff ?_).2 ρ.hw
      exact Arrow.isoMk (Iso.refl _) (iso.app _ ≪≫ B.functor.mapIso e)}⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.LocalizerMorphism.hasLeftResolutions_of_iso_of_essSurj_of_full*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：hasLeftResolutions_of_iso_of_essSurj_of_full [L.functor.EssSurj] [R.functo
r.Full] [R.IsInduced] [W₂'.RespectsIso] (iso : T.functor ⋙ R.functor ≅ L.functor
 ⋙ B.functor) [B.HasLeftResolutions] : T.HasLeftResolutions
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EssSurj.mem_essImage`：∀ {C : Type u₁} {D : Type u
₂} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   (F : CategoryTheor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.LocalizerMorphism.IsInduced.inverseImage_eq`：∀ {C₁ : Type
 u₁} {C₂ : Type u₂} {inst : CategoryTheory.Category.{v₁, u₁} C₁}   {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} C₂} {W₁ : Category…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.LocalizerMorphism.LeftResolution.hw`：∀ {C₁ : Type u_1} {C
₂ : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C₁]   [inst_1 : Categor
yTheory.Category.{v_2, u_2} C₂] {W₁ : Ca…
-/
lemma hasLeftResolutions_of_iso_of_essSurj_of_full
    [L.functor.EssSurj] [R.functor.Full] [R.IsInduced] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [B.HasLeftResolutions] :
    T.HasLeftResolutions := by
  intro X₂
  let ρ : B.LeftResolution (R.functor.obj X₂) := Classical.arbitrary _
  obtain ⟨X₁, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage L.functor ρ.X₁
  exact ⟨{
    X₁ := X₁
    w := R.functor.preimage (iso.hom.app X₁ ≫ B.functor.map e.hom ≫ ρ.w)
    hw := by
      simp only [← R.inverseImage_eq, MorphismProperty.inverseImage_iff, Functor.map_preimage]
      refine (W₂'.arrow_mk_iso_iff ?_).2 ρ.hw
      exact Arrow.isoMk (iso.app _ ≪≫ B.functor.mapIso e) (Iso.refl _) }⟩
/-
**CategoryTheory.LocalizerMorphism.hasRightResolutions_iff_iso_of_essSurj_of_ful
l** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：hasRightResolutions_iff_iso_of_essSurj_of_full [R.functor.EssSurj] [R.func
tor.Full] [R.IsInduced] [L.functor.EssSurj] [W₂'.RespectsIso] (iso : T.functor ⋙
 R.functor ≅ L.functor ⋙ B.functor) : T.HasRightResolutions ↔ B.HasRightResoluti
ons
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.hasRightResolutions_of_iso_of_essSurj`：
hasRightResolutions_of_iso_of_essSurj [R.functor.EssSurj] [W₂'.RespectsIso] (iso
 : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [T.HasRigh…
· 使用引理 `CategoryTheory.LocalizerMorphism.hasRightResolutions_of_iso_of_essSurj_o
f_full`：hasRightResolutions_of_iso_of_essSurj_of_full [L.functor.EssSurj] [R.fun
ctor.Full] [R.IsInduced] [W₂'.RespectsIso] (iso : T.functor ⋙ R.func…
-/
lemma hasRightResolutions_iff_iso_of_essSurj_of_full
    [R.functor.EssSurj] [R.functor.Full] [R.IsInduced] [L.functor.EssSurj] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) :
    T.HasRightResolutions ↔ B.HasRightResolutions :=
  ⟨fun _ ↦ hasRightResolutions_of_iso_of_essSurj iso,
    fun _ ↦ hasRightResolutions_of_iso_of_essSurj_of_full iso⟩
/-
**CategoryTheory.LocalizerMorphism.hasLeftResolutions_iff_iso_of_essSurj_of_full
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：hasLeftResolutions_iff_iso_of_essSurj_of_full [R.functor.EssSurj] [R.funct
or.Full] [R.IsInduced] [L.functor.EssSurj] [W₂'.RespectsIso] (iso : T.functor ⋙ 
R.functor ≅ L.functor ⋙ B.functor) : T.HasLeftResolutions ↔ B.HasLeftResolutions
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.hasLeftResolutions_of_iso_of_essSurj`：h
asLeftResolutions_of_iso_of_essSurj [R.functor.EssSurj] [W₂'.RespectsIso] (iso :
 T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [T.HasLeftR…
· 使用引理 `CategoryTheory.LocalizerMorphism.hasLeftResolutions_of_iso_of_essSurj_of
_full`：hasLeftResolutions_of_iso_of_essSurj_of_full [L.functor.EssSurj] [R.funct
or.Full] [R.IsInduced] [W₂'.RespectsIso] (iso : T.functor ⋙ R.funct…
-/
lemma hasLeftResolutions_iff_iso_of_essSurj_of_full
    [R.functor.EssSurj] [R.functor.Full] [R.IsInduced] [L.functor.EssSurj] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) :
    T.HasLeftResolutions ↔ B.HasLeftResolutions :=
  ⟨fun _ ↦ hasLeftResolutions_of_iso_of_essSurj iso,
    fun _ ↦ hasLeftResolutions_of_iso_of_essSurj_of_full iso⟩
/-
**CategoryTheory.LocalizerMorphism.hasRightResolutions_arrow_of_essSurj_of_full*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：hasRightResolutions_arrow_of_essSurj_of_full [R.functor.EssSurj] [R.functo
r.Full] [W₂'.RespectsIso] (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) 
[T.arrow.HasRightResolutions] : B.arrow.HasRightResolutions
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.hasRightResolutions_of_iso_of_essSurj`：
hasRightResolutions_of_iso_of_essSurj [R.functor.EssSurj] [W₂'.RespectsIso] (iso
 : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [T.HasRigh…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoArrowArrow`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v, u_1} C] (W : CategoryTheory.MorphismProp
erty C) [W.RespectsIso],   W.arrow.RespectsIso
-/
lemma hasRightResolutions_arrow_of_essSurj_of_full
    [R.functor.EssSurj] [R.functor.Full] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [T.arrow.HasRightResolutions] :
    B.arrow.HasRightResolutions := by
  let : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  exact hasRightResolutions_of_iso_of_essSurj
    (CatCommSq.iso T.arrow.functor L.arrow.functor R.arrow.functor B.arrow.functor)
/-
**CategoryTheory.LocalizerMorphism.hasLeftResolutions_arrow_of_essSurj_of_full**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：hasLeftResolutions_arrow_of_essSurj_of_full [R.functor.EssSurj] [R.functor
.Full] [W₂'.RespectsIso] (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [
T.arrow.HasLeftResolutions] : B.arrow.HasLeftResolutions
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.hasLeftResolutions_of_iso_of_essSurj`：h
asLeftResolutions_of_iso_of_essSurj [R.functor.EssSurj] [W₂'.RespectsIso] (iso :
 T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [T.HasLeftR…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoArrowArrow`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v, u_1} C] (W : CategoryTheory.MorphismProp
erty C) [W.RespectsIso],   W.arrow.RespectsIso
-/
lemma hasLeftResolutions_arrow_of_essSurj_of_full
    [R.functor.EssSurj] [R.functor.Full] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [T.arrow.HasLeftResolutions] :
    B.arrow.HasLeftResolutions := by
  let : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  exact hasLeftResolutions_of_iso_of_essSurj
    (CatCommSq.iso T.arrow.functor L.arrow.functor R.arrow.functor B.arrow.functor)
/-
**CategoryTheory.LocalizerMorphism.hasRightResolutions_arrow_iff_of_equivalences
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：hasRightResolutions_arrow_iff_of_equivalences [R.functor.IsEquivalence] [R
.IsInduced] [L.functor.IsEquivalence] [W₂'.RespectsIso] (iso : T.functor ⋙ R.fun
ctor ≅ L.functor ⋙ B.functor) : T.arrow.HasRightResolutions ↔ B.arrow.HasRightRe
solutions
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.hasRightResolutions_iff_iso_of_essSurj_
of_full`：hasRightResolutions_iff_iso_of_essSurj_of_full [R.functor.EssSurj] [R.f
unctor.Full] [R.IsInduced] [L.functor.EssSurj] [W₂'.RespectsIso] (iso…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.essSurj`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.LocalizerMorphism.instIsInducedArrowArrowArrow`：∀ {C₁ : T
ype u₁} {C₂ : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : 
CategoryTheory.Category.{v₂, u₂} C₂] {W₁ : Category…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoArrowArrow`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v, u_1} C] (W : CategoryTheory.MorphismProp
erty C) [W.RespectsIso],   W.arrow.RespectsIso
-/
lemma hasRightResolutions_arrow_iff_of_equivalences
    [R.functor.IsEquivalence] [R.IsInduced] [L.functor.IsEquivalence] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) :
    T.arrow.HasRightResolutions ↔ B.arrow.HasRightResolutions := by
  let : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  exact hasRightResolutions_iff_iso_of_essSurj_of_full
    (CatCommSq.iso T.arrow.functor L.arrow.functor R.arrow.functor B.arrow.functor)
/-
**CategoryTheory.LocalizerMorphism.hasLeftResolutions_arrow_iff_of_equivalences*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.LocalizerMorphism`。
形式化陈述：hasLeftResolutions_arrow_iff_of_equivalences [R.functor.IsEquivalence] [R.
IsInduced] [L.functor.IsEquivalence] [W₂'.RespectsIso] (iso : T.functor ⋙ R.func
tor ≅ L.functor ⋙ B.functor) : T.arrow.HasLeftResolutions ↔ B.arrow.HasLeftResol
utions
参数：iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.LocalizerMorphism.hasLeftResolutions_iff_iso_of_essSurj_o
f_full`：hasLeftResolutions_iff_iso_of_essSurj_of_full [R.functor.EssSurj] [R.fun
ctor.Full] [R.IsInduced] [L.functor.EssSurj] [W₂'.RespectsIso] (iso …
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.essSurj`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.LocalizerMorphism.instIsInducedArrowArrowArrow`：∀ {C₁ : T
ype u₁} {C₂ : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : 
CategoryTheory.Category.{v₂, u₂} C₂] {W₁ : Category…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoArrowArrow`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v, u_1} C] (W : CategoryTheory.MorphismProp
erty C) [W.RespectsIso],   W.arrow.RespectsIso
-/
lemma hasLeftResolutions_arrow_iff_of_equivalences
    [R.functor.IsEquivalence] [R.IsInduced] [L.functor.IsEquivalence] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) :
    T.arrow.HasLeftResolutions ↔ B.arrow.HasLeftResolutions := by
  let : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  exact hasLeftResolutions_iff_iso_of_essSurj_of_full
    (CatCommSq.iso T.arrow.functor L.arrow.functor R.arrow.functor B.arrow.functor)

end

end LocalizerMorphism

end CategoryTheory

