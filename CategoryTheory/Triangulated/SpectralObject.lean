/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.One
public import Mathlib.CategoryTheory.ComposableArrows.Two
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Spectral objects in triangulated categories

In this file, we introduce the category `SpectralObject C ι` of spectral
objects in a pretriangulated category `C` indexed by the category `ι`.

## TODO (@joelriou)
* construct the spectral object indexed by `WithTop (WithBot ℤ)` consisting
  of all truncations of an object of a triangulated category equipped with a t-structure
* define a similar notion of spectral objects in abelian categories, show that
  by applying a homological functor `C ⥤ A` to a spectral object in the
  triangulated category `C`, we obtain a spectral object in the abelian category `A`
* construct the spectral sequence attached to a spectral object in an abelian category

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated ComposableArrows

variable (C ι : Type*) [Category* C] [Category* ι] [HasZeroObject C]
  [HasShift C ℤ] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Triangulated

/-- A spectral object in a pretriangulated category `C` indexed by a category `ι` consists
of a functor `ω₁ : ComposableArrows ι 1 ⥤ C`, and a functorial distinguished triangle
from the category `ComposableArrows ι 2`, which must be of the form
`ω₁.obj (mk₁ f) ⟶ ω₁.obj (mk₁ (f ≫ g)) ⟶ ω₁.obj (mk₁ g) ⟶ ...` when evaluated
on `mk₂ f g : ComposableArrows ι 2`. -/
/-
**CategoryTheory.Triangulated.SpectralObject** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.Triangulated`。
形式化陈述：(C : Type u_1) →   (ι : Type u_2) →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [CategoryTheory.Category.{v_2, u_2} ι] →         [inst_2 : C
ategoryTheory.Limits.HasZeroObject C] →           [inst_3 : CategoryTheory.HasSh
ift C ℤ] →             [inst_4 : CategoryTheory.Preadditive C] →               [
inst_5 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] →               
  [CategoryTheory.Pretriangulated C] → Type (max (max (max u_1 u_2) v_1) v_2)
参数：max (max u_1 u_2) v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A spectral object in a pretriangulated category `C` indexed by a category `ι` co
nsists
of a functor `ω₁ : ComposableArrows ι 1 ⥤ C`, and a functorial distinguished tri
angle
from the category `ComposableArrows ι 2`, which must be of the form
`ω₁.obj (mk₁ f) ⟶ ω₁.obj (mk₁ (f ≫ g)) ⟶ ω₁.obj (mk₁ g) ⟶ ...` when evaluated
on `mk₂ f g : ComposableArrows ι 2`.
-/
structure SpectralObject where
  /-- A functor from `ComposableArrows ι 1` to the pretriangulated category. -/
  ω₁ : ComposableArrows ι 1 ⥤ C
  /-- The connecting homomorphism of the spectral object. -/
  δ' : functorArrows ι 1 2 2 ⋙ ω₁ ⟶ functorArrows ι 0 1 2 ⋙ ω₁ ⋙ shiftFunctor C (1 : ℤ)
  distinguished' (D : ComposableArrows ι 2) :
    Triangle.mk (ω₁.map ((mapFunctorArrows ι 0 1 0 2 2).app D))
      (ω₁.map ((mapFunctorArrows ι 0 2 1 2 2).app D)) (δ'.app D) ∈ distTriang C

namespace SpectralObject

variable {C ι} (X : SpectralObject C ι)

/-- The functorial (distinguished) triangle attached to a spectral object in
a pretriangulated category. -/
@[simps!]
/-
**CategoryTheory.Triangulated.SpectralObject.** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Triangulated.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functorial (distinguished) triangle attached to a spectral object in
a pretriangulated category.
-/
noncomputable def ω₂ : ComposableArrows ι 2 ⥤ Triangle C :=
  Triangle.functorMk (Functor.whiskerRight (mapFunctorArrows ι 0 1 0 2 2) X.ω₁)
    (Functor.whiskerRight (mapFunctorArrows ι 0 2 1 2 2) X.ω₁) X.δ'
/-
**CategoryTheory.Triangulated.SpectralObject.** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Triangulated.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ω₂_obj_distinguished (D : ComposableArrows ι 2) :
    X.ω₂.obj D ∈ distTriang C :=
  X.distinguished' D

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

/-- The connecting homomorphism `X.ω₁.obj (mk₁ g) ⟶ (X.ω₁.obj (mk₁ f))⟦(1 : ℤ)⟧`
of a spectral object `X` in a pretriangulated category when `f : i ⟶ j` and `g : j ⟶ k`
are composable. -/
/-
**CategoryTheory.Triangulated.SpectralObject.** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Triangulated.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connecting homomorphism `X.ω₁.obj (mk₁ g) ⟶ (X.ω₁.obj (mk₁ f))⟦(1 : ℤ)⟧`
of a spectral object `X` in a pretriangulated category when `f : i ⟶ j` and `g :
 j ⟶ k`
are composable.
-/
def δ : X.ω₁.obj (mk₁ g) ⟶ (X.ω₁.obj (mk₁ f))⟦(1 : ℤ)⟧ :=
  X.δ'.app (mk₂ f g)

/-- The distinguished triangle attached to a spectral object `E : SpectralObject C ι`
and composable morphisms `f : i ⟶ j` and `g : j ⟶ k` in `ι`. -/
@[simps!]
/-
**CategoryTheory.Triangulated.SpectralObject.triangle** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Triangulated.SpectralObject`。
形式化陈述：triangle : Triangle C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distinguished triangle attached to a spectral object `E : SpectralObject C ι
`
and composable morphisms `f : i ⟶ j` and `g : j ⟶ k` in `ι`.
-/
def triangle : Triangle C :=
  Triangle.mk (X.ω₁.map (twoδ₂Toδ₁ f g _ rfl))
    (X.ω₁.map (twoδ₁Toδ₀ f g _ rfl)) (X.δ f g)
/-
**CategoryTheory.Triangulated.SpectralObject.triangle_distinguished** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Triangulated.SpectralObject`。
形式化陈述：triangle_distinguished : X.triangle f g in distTriang C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.SpectralObject.ω₂_obj_distinguished`：ω₂_obj_
distinguished (D : ComposableArrows ι 2) : X.ω₂.obj D in distTriang C
-/
lemma triangle_distinguished : X.triangle f g ∈ distTriang C :=
  X.ω₂_obj_distinguished (mk₂ f g)

end

section

variable {ι' : Type*} [Category ι'] (F : ι' ⥤ ι)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] Precomp.map Precomp.obj δ in
/-- The precomposition of a spectral object with a functor. -/
/-
**CategoryTheory.Triangulated.SpectralObject.precomp** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Triangulated.SpectralObject`。
形式化陈述：precomp : SpectralObject C ι' where ω₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The precomposition of a spectral object with a functor.
-/
def precomp : SpectralObject C ι' where
  ω₁ := F.mapComposableArrows 1 ⋙ X.ω₁
  δ'.app D := X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom ≫
      X.δ'.app ((F.mapComposableArrows 2).obj D) ≫
      (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).inv)⟦1⟧'
  δ'.naturality D₁ D₂ f := by
    have := X.δ'.naturality ((F.mapComposableArrows 2).map f)
    rw [← cancel_epi (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom)] at this
    rw [← cancel_mono ((X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom)⟦(1 : ℤ)⟧')]
    dsimp at this ⊢
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc,
      Iso.inv_hom_id, Functor.map_id, Category.comp_id] at this ⊢
    convert! this using 3
    · cat_disch
    · congr 2; cat_disch
  distinguished' D := by
    obtain ⟨_, _, _, f, g, rfl⟩ := ComposableArrows.mk₂_surjective D
    refine isomorphic_distinguished _ (X.triangle_distinguished (F.map f) (F.map g)) _ ?_
    refine Triangle.isoMk _ _ (X.ω₁.mapIso (ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _)))
      (X.ω₁.mapIso (ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _)))
      (X.ω₁.mapIso (ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _))) ?_ ?_ ?_
    · dsimp
      simp only [← Functor.map_comp]
      congr 1
      cat_disch
    · dsimp
      simp only [← Functor.map_comp]
      congr 1
      cat_disch
    · have := X.δ'.naturality (F.mapComposableArrowsObjMk₂Iso f g).hom
      dsimp at this ⊢
      rw [← cancel_epi (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).inv)]
      simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc,
        Iso.inv_hom_id, Functor.map_id, Category.id_comp] at this ⊢
      convert! this.symm using 3
      · congr; cat_disch
      · cat_disch

end

section

variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]

/-- The image of a spectral by a triangulated functor. -/
@[simps]
/-
**CategoryTheory.Triangulated.SpectralObject.mapTriangulatedFunctor** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Triangulated.SpectralObject`。
形式化陈述：mapTriangulatedFunctor : SpectralObject D ι where ω₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a spectral by a triangulated functor.
-/
def mapTriangulatedFunctor :
    SpectralObject D ι where
  ω₁ := X.ω₁ ⋙ F
  δ' := Functor.whiskerRight X.δ' F ≫
      Functor.whiskerLeft (functorArrows ι 0 1 2 ⋙ X.ω₁) (F.commShiftIso (1 : ℤ)).hom
  distinguished' D := F.map_distinguished _ (X.distinguished' D)

@[simp]
/-
**CategoryTheory.Triangulated.SpectralObject.mapTriangulatedFunctor_** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Triangulated.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapTriangulatedFunctor_δ {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) :
    (X.mapTriangulatedFunctor F).δ f g = F.map (X.δ f g) ≫ (F.commShiftIso 1).hom.app _ := rfl

end

/-- The type of morphisms between spectral objects in pretriangulated categories. -/
@[ext]
/-
**CategoryTheory.Triangulated.SpectralObject.Hom** 是 Mathlib 中的一个结构，位于命名空间 `Cate
goryTheory.Triangulated.SpectralObject`。
形式化陈述：Hom (Y : SpectralObject C ι) where /-- The natural transformation that is 
part of a morphism between spectral objects. -/ hom : X.ω₁ ⟶ Y.ω₁ comm {i j k : 
ι} (f : i ⟶ j) (g : j ⟶ k) : X.δ f g ≫ (hom.app (mk₁ f))⟦(1 : Int)⟧' = hom.app (
mk₁ g) ≫ Y.δ f g
参数：Y : SpectralObject C ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms between spectral objects in pretriangulated categories.
-/
structure Hom (Y : SpectralObject C ι) where
  /-- The natural transformation that is part of a morphism between spectral objects. -/
  hom : X.ω₁ ⟶ Y.ω₁
  comm {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) :
    X.δ f g ≫ (hom.app (mk₁ f))⟦(1 : ℤ)⟧' = hom.app (mk₁ g) ≫ Y.δ f g := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm
/-
**CategoryTheory.Triangulated.SpectralObject.** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Triangulated.SpectralObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (SpectralObject C ι) where
  Hom := Hom
  id X := { hom := 𝟙 _ }
  comp f g :=
    { hom := f.hom ≫ g.hom }

section

variable {X} {Y Z : SpectralObject C ι}

@[ext]
/-
**CategoryTheory.Triangulated.SpectralObject.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Triangulated.SpectralObject`。
形式化陈述：hom_ext {α β : X ⟶ Y} (h : α.hom = β.hom) : α = β
参数：h : α.hom = β.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Triangulated.SpectralObject.Hom.ext`：∀ {C : Type u_1} {ι 
: Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTh
eory.Category.{v_2, u_2} ι} {inst_2 : Ca…
-/
lemma hom_ext {α β : X ⟶ Y} (h : α.hom = β.hom) : α = β := Hom.ext h

variable (X) in
@[simp]
/-
**CategoryTheory.Triangulated.SpectralObject.id_hom** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Triangulated.SpectralObject`。
形式化陈述：id_hom : Hom.hom (𝟙 X) = 𝟙 _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_hom : Hom.hom (𝟙 X) = 𝟙 _ := rfl

@[simp, reassoc]
/-
**CategoryTheory.Triangulated.SpectralObject.comp_hom** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Triangulated.SpectralObject`。
形式化陈述：comp_hom (α : X ⟶ Y) (β : Y ⟶ Z) : (α ≫ β).hom = α.hom ≫ β.hom
参数：α : X ⟶ Y；β : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_hom (α : X ⟶ Y) (β : Y ⟶ Z) :
    (α ≫ β).hom = α.hom ≫ β.hom := rfl

end

end SpectralObject

end Triangulated

namespace Functor

variable {C}

set_option backward.defeqAttrib.useBackward true in
/-- The functor between categories of spectral objects that is induced by
a triangulated functor. -/
/-
**CategoryTheory.Functor.mapTriangulatedSpectralObject** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：mapTriangulatedSpectralObject (F : C ⥤ D) [F.CommShift Int] [F.IsTriangula
ted] (ι : Type*) [Category* ι] : Triangulated.SpectralObject C ι ⥤ Triangulated.
SpectralObject D ι where obj X
参数：F : C ⥤ D；ι : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor between categories of spectral objects that is induced by
a triangulated functor.
-/
def mapTriangulatedSpectralObject (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (ι : Type*) [Category* ι] :
    Triangulated.SpectralObject C ι ⥤ Triangulated.SpectralObject D ι where
  obj X := X.mapTriangulatedFunctor F
  map α :=
    { hom := Functor.whiskerRight α.hom _
      comm f g := by
        have hf := (F.commShiftIso (1 : ℤ)).hom.naturality (α.hom.app (mk₁ f))
        dsimp at hf ⊢
        rw [Category.assoc, ← hf, ← F.map_comp_assoc, α.comm, F.map_comp_assoc] }

end Functor

end CategoryTheory

