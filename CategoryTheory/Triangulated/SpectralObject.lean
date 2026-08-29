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
  [HasShift C Int] [Preadditive C] [forall (n : Int), (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type*} [Category* D] [HasZeroObject D] [HasShift D Int] [Preadditive D]
  [forall (n : Int), (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Triangulated

/--
Definition of `SpectralObject` / `SpectralObject` 的定义

English:
structure SpectralObject
  parameters: where
  axioms and operations (3):
    - ω₁ : ComposableArrows ι 1 ⥤ C
    - δ' : functorArrows ι 1 2 2 ⋙ ω₁ ⟶ functorArrows ι 0 1 2 ⋙ ω₁ ⋙ shiftFunctor C (1 : Int)
    - distinguished'((D : ComposableArrows ι 2)) : Triangle.mk (ω₁.map ((mapFunctorArrows ι 0 1 0 2 2).app D)) (ω₁.map ((mapFunctorArrows ι 0 2 1 2 2).app D)) (δ'.app D) in distTriang C

中文:
结构 SpectralObject
  参数: where
  公理与运算 (3 个):
    - ω₁ : ComposableArrows ι 1 ⥤ C
    - δ' : functorArrows ι 1 2 2 ⋙ ω₁ ⟶ functorArrows ι 0 1 2 ⋙ ω₁ ⋙ shiftFunctor C (1 : 整数)
    - distinguished'((D : ComposableArrows ι 2)) : Triangle.mk (ω₁.map ((mapFunctorArrows ι 0 1 0 2 2).app D)) (ω₁.map ((mapFunctorArrows ι 0 2 1 2 2).app D)) (δ'.app D) in distTriang C
-/
structure SpectralObject where
  /-- A functor from `ComposableArrows ι 1` to the pretriangulated category. -/
  ω₁ : ComposableArrows ι 1 ⥤ C
  /-- The connecting homomorphism of the spectral object. -/
  δ' : functorArrows ι 1 2 2 ⋙ ω₁ ⟶ functorArrows ι 0 1 2 ⋙ ω₁ ⋙ shiftFunctor C (1 : Int)
  distinguished' (D : ComposableArrows ι 2) :
    Triangle.mk (ω₁.map ((mapFunctorArrows ι 0 1 0 2 2).app D))
      (ω₁.map ((mapFunctorArrows ι 0 2 1 2 2).app D)) (δ'.app D) in distTriang C

namespace SpectralObject

variable {C ι} (X : SpectralObject C ι)

/-- The functorial (distinguished) triangle attached to a spectral object in
a pretriangulated category. -/
@[simps!]
/--
Definition of `ω₂` / `ω₂` 的定义

English:
definition ω₂
  signature: : ComposableArrows ι 2 ⥤ Triangle C
  body: Triangle.functorMk (Functor.whiskerRight (mapFunctorArrows ι 0 1 0 2 2) X.ω₁)
    (Functor.whiskerRight (mapFunctorArrows ι 0 2 1 2 2) X.ω₁) X.δ'

中文:
定义 ω₂
  签名: : ComposableArrows ι 2 ⥤ Triangle C
  定义体: Triangle.functorMk (Functor.whiskerRight (mapFunctorArrows ι 0 1 0 2 2) X.ω₁)
    (Functor.whiskerRight (mapFunctorArrows ι 0 2 1 2 2) X.ω₁) X.δ'

Depends on / 依赖: Functor, Functor.whiskerRight, Triangle, Triangle.functorMk, functorMk, mapFunctorArrows, whiskerRight
-/
noncomputable def ω₂ : ComposableArrows ι 2 ⥤ Triangle C :=
  Triangle.functorMk (Functor.whiskerRight (mapFunctorArrows ι 0 1 0 2 2) X.ω₁)
    (Functor.whiskerRight (mapFunctorArrows ι 0 2 1 2 2) X.ω₁) X.δ'

/--
lemma `ω₂_obj_distinguished` / 引理 `ω₂_obj_distinguished`

English:
lemma ω₂_obj_distinguished
  given: (D : ComposableArrows ι 2)
  proof: X.distinguished' D

中文:
引理 ω₂_obj_distinguished
  条件: (D : ComposableArrows ι 2)
  证明: X.distinguished' D

Depends on / 依赖: X.distinguished, distinguished
-/
lemma ω₂_obj_distinguished (D : ComposableArrows ι 2) :
    X.ω₂.obj D in distTriang C :=
  X.distinguished' D

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

/--
Definition of `δ` / `δ` 的定义

English:
definition δ
  signature: : X.ω₁.obj (mk₁ g) ⟶ (X.ω₁.obj (mk₁ f))⟦(1 : Int)⟧
  body: X.δ'.app (mk₂ f g)

中文:
定义 δ
  签名: : X.ω₁.obj (mk₁ g) ⟶ (X.ω₁.obj (mk₁ f))⟦(1 : 整数)⟧
  定义体: X.δ'.app (mk₂ f g)
-/
def δ : X.ω₁.obj (mk₁ g) ⟶ (X.ω₁.obj (mk₁ f))⟦(1 : Int)⟧ :=
  X.δ'.app (mk₂ f g)

/-- The distinguished triangle attached to a spectral object `E : SpectralObject C ι`
and composable morphisms `f : i ⟶ j` and `g : j ⟶ k` in `ι`. -/
@[simps!]
/--
Definition of `triangle` / `triangle` 的定义

English:
definition triangle
  signature: : Triangle C
  body: Triangle.mk (X.ω₁.map (twoδ₂Toδ₁ f g _ rfl))
    (X.ω₁.map (twoδ₁Toδ₀ f g _ rfl)) (X.δ f g)

中文:
定义 triangle
  签名: : Triangle C
  定义体: Triangle.mk (X.ω₁.map (twoδ₂Toδ₁ f g _ rfl))
    (X.ω₁.map (twoδ₁Toδ₀ f g _ rfl)) (X.δ f g)

Depends on / 依赖: Triangle, Triangle.mk
-/
def triangle : Triangle C :=
  Triangle.mk (X.ω₁.map (twoδ₂Toδ₁ f g _ rfl))
    (X.ω₁.map (twoδ₁Toδ₀ f g _ rfl)) (X.δ f g)

/--
lemma `triangle_distinguished` / 引理 `triangle_distinguished`

English:
lemma triangle_distinguished
  statement: X.triangle f g in distTriang C
  proof: X.ω₂_obj_distinguished (mk₂ f g)

中文:
引理 triangle_distinguished
  结论: X.triangle f g in distTriang C
  证明: X.ω₂_obj_distinguished (mk₂ f g)
-/
lemma triangle_distinguished : X.triangle f g in distTriang C :=
  X.ω₂_obj_distinguished (mk₂ f g)

end

section

variable {ι' : Type*} [Category ι'] (F : ι' ⥤ ι)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] Precomp.map Precomp.obj δ in
/--
Definition of `precomp` / `precomp` 的定义

English:
definition precomp
  signature: : SpectralObject C ι' where
  body: F.mapComposableArrows 1 ⋙ X.ω₁
  δ'.app D := X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom ≫
      X.δ'.app ((F.mapComposableArrows 2).obj D) ≫
      (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).inv)⟦1⟧'
  δ'.naturality D₁ D₂ f := by
    have := X.δ'.naturality ((F.mapComposableArrows 2).map f)
    rw [← cancel_epi (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom)] at this
    rw [← cancel_mono ((X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom)⟦(1 : Int)⟧')]
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

中文:
定义 precomp
  签名: : SpectralObject C ι' where
  定义体: F.mapComposableArrows 1 ⋙ X.ω₁
  δ'.app D := X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom ≫
      X.δ'.app ((F.mapComposableArrows 2).obj D) ≫
      (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).inv)⟦1⟧'
  δ'.naturality D₁ D₂ f := by
    have := X.δ'.naturality ((F.mapComposableArrows 2).map f)
    rw [← cancel_epi (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom)] at this
    rw [← cancel_mono ((X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom)⟦(1 : Int)⟧')]
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

Depends on / 依赖: F.mapComposableArrows, mapComposableArrows
-/
def precomp : SpectralObject C ι' where
  ω₁ := F.mapComposableArrows 1 ⋙ X.ω₁
  δ'.app D := X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom ≫
      X.δ'.app ((F.mapComposableArrows 2).obj D) ≫
      (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).inv)⟦1⟧'
  δ'.naturality D₁ D₂ f := by
    have := X.δ'.naturality ((F.mapComposableArrows 2).map f)
    rw [← cancel_epi (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom)] at this
    rw [← cancel_mono ((X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom)⟦(1 : Int)⟧')]
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

variable (F : C ⥤ D) [F.CommShift Int] [F.IsTriangulated]

/-- The image of a spectral by a triangulated functor. -/
@[simps]
/--
Definition of `mapTriangulatedFunctor` / `mapTriangulatedFunctor` 的定义

English:
definition mapTriangulatedFunctor
  signature: :
  body: X.ω₁ ⋙ F
  δ' := Functor.whiskerRight X.δ' F ≫
      Functor.whiskerLeft (functorArrows ι 0 1 2 ⋙ X.ω₁) (F.commShiftIso (1 : Int)).hom
  distinguished' D := F.map_distinguished _ (X.distinguished' D)

@[simp]

中文:
定义 mapTriangulatedFunctor
  签名: :
  定义体: X.ω₁ ⋙ F
  δ' := Functor.whiskerRight X.δ' F ≫
      Functor.whiskerLeft (functorArrows ι 0 1 2 ⋙ X.ω₁) (F.commShiftIso (1 : Int)).hom
  distinguished' D := F.map_distinguished _ (X.distinguished' D)

@[simp]
-/
def mapTriangulatedFunctor :
    SpectralObject D ι where
  ω₁ := X.ω₁ ⋙ F
  δ' := Functor.whiskerRight X.δ' F ≫
      Functor.whiskerLeft (functorArrows ι 0 1 2 ⋙ X.ω₁) (F.commShiftIso (1 : Int)).hom
  distinguished' D := F.map_distinguished _ (X.distinguished' D)

@[simp]
/--
lemma `mapTriangulatedFunctor_δ` / 引理 `mapTriangulatedFunctor_δ`

English:
lemma mapTriangulatedFunctor_δ
  given: {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  proof: rfl

中文:
引理 mapTriangulatedFunctor_δ
  条件: {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  证明: rfl
-/
lemma mapTriangulatedFunctor_δ {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) :
    (X.mapTriangulatedFunctor F).δ f g = F.map (X.δ f g) ≫ (F.commShiftIso 1).hom.app _ := rfl

end

/-- The type of morphisms between spectral objects in pretriangulated categories. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (Y : SpectralObject C ι)
  axioms and operations (2):
    - hom : X.ω₁ ⟶ Y.ω₁
    - comm({i j k : ι} (f : i ⟶ j) (g : j ⟶ k)) : X.δ f g ≫ (hom.app (mk₁ f))⟦(1 : Int)⟧' = hom.app (mk₁ g) ≫ Y.δ f g  [default: by cat_disch]

中文:
结构 态射
  参数: (Y : SpectralObject C ι)
  公理与运算 (2 个):
    - hom : X.ω₁ ⟶ Y.ω₁
    - comm({i j k : ι} (f : i ⟶ j) (g : j ⟶ k)) : X.δ f g ≫ (hom.app (mk₁ f))⟦(1 : 整数)⟧' = hom.app (mk₁ g) ≫ Y.δ f g  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (Y : SpectralObject C ι) where
  /-- The natural transformation that is part of a morphism between spectral objects. -/
  hom : X.ω₁ ⟶ Y.ω₁
  comm {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) :
    X.δ f g ≫ (hom.app (mk₁ f))⟦(1 : Int)⟧' = hom.app (mk₁ g) ≫ Y.δ f g := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (SpectralObject C ι)
  body: Hom
  id X := { hom := 𝟙 _ }
  comp f g :=
    { hom := f.hom ≫ g.hom }

中文:
实例 :
  签名: 范畴 (SpectralObject C ι)
  定义体: Hom
  id X := { hom := 𝟙 _ }
  comp f g :=
    { hom := f.hom ≫ g.hom }
-/
instance : Category (SpectralObject C ι) where
  Hom := Hom
  id X := { hom := 𝟙 _ }
  comp f g :=
    { hom := f.hom ≫ g.hom }

section

variable {X} {Y Z : SpectralObject C ι}

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {α β : X ⟶ Y} (h : α.hom = β.hom)
  statement: α = β
  proof: Hom.ext h

中文:
引理 hom_ext
  条件: {α β : X ⟶ Y} (h : α.hom = β.hom)
  结论: α = β
  证明: Hom.ext h

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {α β : X ⟶ Y} (h : α.hom = β.hom) : α = β := Hom.ext h

variable (X) in
@[simp]
/--
lemma `id_hom` / 引理 `id_hom`

English:
lemma id_hom
  statement: Hom.hom (𝟙 X) = 𝟙 _
  proof: rfl

@[simp, reassoc]

中文:
引理 id_hom
  结论: 态射.hom (𝟙 X) = 𝟙 _
  证明: rfl

@[simp, reassoc]
-/
lemma id_hom : Hom.hom (𝟙 X) = 𝟙 _ := rfl

@[simp, reassoc]
/--
lemma `comp_hom` / 引理 `comp_hom`

English:
lemma comp_hom
  given: (α : X ⟶ Y) (β : Y ⟶ Z)
  proof: rfl

中文:
引理 comp_hom
  条件: (α : X ⟶ Y) (β : Y ⟶ Z)
  证明: rfl
-/
lemma comp_hom (α : X ⟶ Y) (β : Y ⟶ Z) :
    (α ≫ β).hom = α.hom ≫ β.hom := rfl

end

end SpectralObject

end Triangulated

namespace Functor

variable {C}

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mapTriangulatedSpectralObject` / `mapTriangulatedSpectralObject` 的定义

English:
definition mapTriangulatedSpectralObject
  signature: (F : C ⥤ D) [F.CommShift Int] [F.IsTriangulated]
  body: X.mapTriangulatedFunctor F
  map α :=
    { hom := Functor.whiskerRight α.hom _
      comm f g := by
        have hf := (F.commShiftIso (1 : Int)).hom.naturality (α.hom.app (mk₁ f))
        dsimp at hf ⊢
        rw [Category.assoc]; rw [← hf]; rw [← F.map_comp_assoc]; rw [α.comm]; rw [F.map_comp_assoc] }

中文:
定义 mapTriangulatedSpectralObject
  签名: (F : C ⥤ D) [F.交换Shift 整数] [F.是三角]
  定义体: X.mapTriangulatedFunctor F
  map α :=
    { hom := Functor.whiskerRight α.hom _
      comm f g := by
        have hf := (F.commShiftIso (1 : Int)).hom.naturality (α.hom.app (mk₁ f))
        dsimp at hf ⊢
        rw [Category.assoc]; rw [← hf]; rw [← F.map_comp_assoc]; rw [α.comm]; rw [F.map_comp_assoc] }

Depends on / 依赖: X.mapTriangulatedFunctor, mapTriangulatedFunctor
-/
def mapTriangulatedSpectralObject (F : C ⥤ D) [F.CommShift Int] [F.IsTriangulated]
    (ι : Type*) [Category* ι] :
    Triangulated.SpectralObject C ι ⥤ Triangulated.SpectralObject D ι where
  obj X := X.mapTriangulatedFunctor F
  map α :=
    { hom := Functor.whiskerRight α.hom _
      comm f g := by
        have hf := (F.commShiftIso (1 : Int)).hom.naturality (α.hom.app (mk₁ f))
        dsimp at hf ⊢
        rw [Category.assoc]; rw [← hf]; rw [← F.map_comp_assoc]; rw [α.comm]; rw [F.map_comp_assoc] }

end Functor

end CategoryTheory
