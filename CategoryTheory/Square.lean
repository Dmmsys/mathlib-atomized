/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.CommSq

/-!
# The category of commutative squares

In this file, we define a bundled version of `CommSq`
which allows to consider commutative squares as
objects in a category `Square C`.

The four objects in a commutative square are
numbered as follows:
```
X₁ --> X₂
| |
v v
X₃ --> X₄
```

We define the flip functor, and two equivalences with
the category `Arrow (Arrow C)`, depending on whether
we consider a commutative square as a horizontal
morphism between two vertical maps (`arrowArrowEquivalence`)
or a vertical morphism between two horizontal
maps (`arrowArrowEquivalence'`).

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Category

variable (C : Type u) [Category.{v} C] {D : Type u'} [Category.{v'} D]

/--
Definition of `Square` / `Square` 的定义

English:
structure Square
  parameters: where
  axioms and operations (9):
    - {X₁ : C}
    - {X₂ : C}
    - {X₃ : C}
    - {X₄ : C}
    - f₁₂ : X₁ ⟶ X₂
    - f₁₃ : X₁ ⟶ X₃
    - f₂₄ : X₂ ⟶ X₄
    - f₃₄ : X₃ ⟶ X₄
    - fac : f₁₂ ≫ f₂₄ = f₁₃ ≫ f₃₄

中文:
结构 Square
  参数: where
  公理与运算 (9 个):
    - {X₁ : C}
    - {X₂ : C}
    - {X₃ : C}
    - {X₄ : C}
    - f₁₂ : X₁ ⟶ X₂
    - f₁₃ : X₁ ⟶ X₃
    - f₂₄ : X₂ ⟶ X₄
    - f₃₄ : X₃ ⟶ X₄
    - fac : f₁₂ ≫ f₂₄ = f₁₃ ≫ f₃₄
-/
structure Square where
  /-- the top-left object -/
  {X₁ : C}
  /-- the top-right object -/
  {X₂ : C}
  /-- the bottom-left object -/
  {X₃ : C}
  /-- the bottom-right object -/
  {X₄ : C}
  /-- the top morphism -/
  f₁₂ : X₁ ⟶ X₂
  /-- the left morphism -/
  f₁₃ : X₁ ⟶ X₃
  /-- the right morphism -/
  f₂₄ : X₂ ⟶ X₄
  /-- the bottom morphism -/
  f₃₄ : X₃ ⟶ X₄
  fac : f₁₂ ≫ f₂₄ = f₁₃ ≫ f₃₄

namespace Square

variable {C}

/--
lemma `commSq` / 引理 `commSq`

English:
lemma commSq
  given: (sq : Square C)
  statement: CommSq sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄ where
  proof: sq.fac

中文:
引理 commSq
  条件: (sq : Square C)
  结论: CommSq sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄ where
  证明: sq.fac

Depends on / 依赖: sq.fac
-/
lemma commSq (sq : Square C) : CommSq sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄ where
  w := sq.fac

/-- A morphism between two commutative squares consists of 4 morphisms
which extend these two squares into a commuting cube. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (sq₁ sq₂ : Square C)
  axioms and operations (8):
    - τ₁ : sq₁.X₁ ⟶ sq₂.X₁
    - τ₂ : sq₁.X₂ ⟶ sq₂.X₂
    - τ₃ : sq₁.X₃ ⟶ sq₂.X₃
    - τ₄ : sq₁.X₄ ⟶ sq₂.X₄
    - comm₁₂ : sq₁.f₁₂ ≫ τ₂ = τ₁ ≫ sq₂.f₁₂  [default: by cat_disch]
    - comm₁₃ : sq₁.f₁₃ ≫ τ₃ = τ₁ ≫ sq₂.f₁₃  [default: by cat_disch]
    - comm₂₄ : sq₁.f₂₄ ≫ τ₄ = τ₂ ≫ sq₂.f₂₄  [default: by cat_disch]
    - comm₃₄ : sq₁.f₃₄ ≫ τ₄ = τ₃ ≫ sq₂.f₃₄  [default: by cat_disch]

中文:
结构 Hom
  参数: (sq₁ sq₂ : Square C)
  公理与运算 (8 个):
    - τ₁ : sq₁.X₁ ⟶ sq₂.X₁
    - τ₂ : sq₁.X₂ ⟶ sq₂.X₂
    - τ₃ : sq₁.X₃ ⟶ sq₂.X₃
    - τ₄ : sq₁.X₄ ⟶ sq₂.X₄
    - comm₁₂ : sq₁.f₁₂ ≫ τ₂ = τ₁ ≫ sq₂.f₁₂  [默认: by cat_disch]
    - comm₁₃ : sq₁.f₁₃ ≫ τ₃ = τ₁ ≫ sq₂.f₁₃  [默认: by cat_disch]
    - comm₂₄ : sq₁.f₂₄ ≫ τ₄ = τ₂ ≫ sq₂.f₂₄  [默认: by cat_disch]
    - comm₃₄ : sq₁.f₃₄ ≫ τ₄ = τ₃ ≫ sq₂.f₃₄  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (sq₁ sq₂ : Square C) where
  /-- the top-left morphism -/
  τ₁ : sq₁.X₁ ⟶ sq₂.X₁
  /-- the top-right morphism -/
  τ₂ : sq₁.X₂ ⟶ sq₂.X₂
  /-- the bottom-left morphism -/
  τ₃ : sq₁.X₃ ⟶ sq₂.X₃
  /-- the bottom-right morphism -/
  τ₄ : sq₁.X₄ ⟶ sq₂.X₄
  comm₁₂ : sq₁.f₁₂ ≫ τ₂ = τ₁ ≫ sq₂.f₁₂ := by cat_disch
  comm₁₃ : sq₁.f₁₃ ≫ τ₃ = τ₁ ≫ sq₂.f₁₃ := by cat_disch
  comm₂₄ : sq₁.f₂₄ ≫ τ₄ = τ₂ ≫ sq₂.f₂₄ := by cat_disch
  comm₃₄ : sq₁.f₃₄ ≫ τ₄ = τ₃ ≫ sq₂.f₃₄ := by cat_disch

namespace Hom

attribute [reassoc (attr := simp)] comm₁₂ comm₁₃ comm₂₄ comm₃₄

/-- The identity of a commutative square. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (sq : Square C)
  body: 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  τ₄ := 𝟙 _

中文:
定义 id
  签名: (sq : Square C)
  定义体: 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  τ₄ := 𝟙 _
-/
def id (sq : Square C) : Hom sq sq where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  τ₄ := 𝟙 _

/-- The composition of morphisms of squares. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {sq₁ sq₂ sq₃ : Square C} (f : Hom sq₁ sq₂) (g : Hom sq₂ sq₃)
  body: f.τ₁ ≫ g.τ₁
  τ₂ := f.τ₂ ≫ g.τ₂
  τ₃ := f.τ₃ ≫ g.τ₃
  τ₄ := f.τ₄ ≫ g.τ₄

中文:
定义 comp
  签名: {sq₁ sq₂ sq₃ : Square C} (f : Hom sq₁ sq₂) (g : Hom sq₂ sq₃)
  定义体: f.τ₁ ≫ g.τ₁
  τ₂ := f.τ₂ ≫ g.τ₂
  τ₃ := f.τ₃ ≫ g.τ₃
  τ₄ := f.τ₄ ≫ g.τ₄
-/
def comp {sq₁ sq₂ sq₃ : Square C} (f : Hom sq₁ sq₂) (g : Hom sq₂ sq₃) : Hom sq₁ sq₃ where
  τ₁ := f.τ₁ ≫ g.τ₁
  τ₂ := f.τ₂ ≫ g.τ₂
  τ₃ := f.τ₃ ≫ g.τ₃
  τ₄ := f.τ₄ ≫ g.τ₄

end Hom

@[simps!]
/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : Category (Square C) where
  body: Hom
  id := Hom.id
  comp := Hom.comp

@[ext]

中文:
实例 category
  签名: : Category (Square C) where
  定义体: Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
-/
instance category : Category (Square C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {sq₁ sq₂ : Square C} {f g : sq₁ ⟶ sq₂}
  proof: Hom.ext h₁ h₂ h₃ h₄

中文:
引理 hom_ext
  结论: {sq₁ sq₂ : Square C} {f g : sq₁ ⟶ sq₂}
  证明: Hom.ext h₁ h₂ h₃ h₄

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {sq₁ sq₂ : Square C} {f g : sq₁ ⟶ sq₂}
    (h₁ : f.τ₁ = g.τ₁) (h₂ : f.τ₂ = g.τ₂)
    (h₃ : f.τ₃ = g.τ₃) (h₄ : f.τ₄ = g.τ₄) : f = g :=
  Hom.ext h₁ h₂ h₃ h₄

/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {sq₁ sq₂ : Square C} (e₁ : sq₁.X₁ ≅ sq₂.X₁) (e₂ : sq₁.X₂ ≅ sq₂.X₂)
  body: { τ₁ := e₁.hom
      τ₂ := e₂.hom
      τ₃ := e₃.hom
      τ₄ := e₄.hom }
  inv :=
    { τ₁ := e₁.inv
      τ₂ := e₂.inv
      τ₃ := e₃.inv
      τ₄ := e₄.inv
      comm₁₂ := by simp only [← cancel_mono e₂.hom, assoc, Iso.inv_hom_id,
                      comp_id, comm₁₂, Iso.inv_hom_id_assoc]
     

中文:
定义 isoMk
  签名: {sq₁ sq₂ : Square C} (e₁ : sq₁.X₁ ≅ sq₂.X₁) (e₂ : sq₁.X₂ ≅ sq₂.X₂)
  定义体: { τ₁ := e₁.hom
      τ₂ := e₂.hom
      τ₃ := e₃.hom
      τ₄ := e₄.hom }
  inv :=
    { τ₁ := e₁.inv
      τ₂ := e₂.inv
      τ₃ := e₃.inv
      τ₄ := e₄.inv
      comm₁₂ := by simp only [← cancel_mono e₂.hom, assoc, Iso.inv_hom_id,
                      comp_id, comm₁₂, Iso.inv_hom_id_assoc]
     

Depends on / 依赖: Iso.in, Iso.inv_hom_id, Iso.inv_hom_id_assoc, cancel_mono, comp_id, inv_hom_id, inv_hom_id_assoc
-/
def isoMk {sq₁ sq₂ : Square C} (e₁ : sq₁.X₁ ≅ sq₂.X₁) (e₂ : sq₁.X₂ ≅ sq₂.X₂)
    (e₃ : sq₁.X₃ ≅ sq₂.X₃) (e₄ : sq₁.X₄ ≅ sq₂.X₄)
    (comm₁₂ : sq₁.f₁₂ ≫ e₂.hom = e₁.hom ≫ sq₂.f₁₂)
    (comm₁₃ : sq₁.f₁₃ ≫ e₃.hom = e₁.hom ≫ sq₂.f₁₃)
    (comm₂₄ : sq₁.f₂₄ ≫ e₄.hom = e₂.hom ≫ sq₂.f₂₄)
    (comm₃₄ : sq₁.f₃₄ ≫ e₄.hom = e₃.hom ≫ sq₂.f₃₄) :
    sq₁ ≅ sq₂ where
  hom :=
    { τ₁ := e₁.hom
      τ₂ := e₂.hom
      τ₃ := e₃.hom
      τ₄ := e₄.hom }
  inv :=
    { τ₁ := e₁.inv
      τ₂ := e₂.inv
      τ₃ := e₃.inv
      τ₄ := e₄.inv
      comm₁₂ := by simp only [← cancel_mono e₂.hom, assoc, Iso.inv_hom_id,
                      comp_id, comm₁₂, Iso.inv_hom_id_assoc]
      comm₁₃ := by simp only [← cancel_mono e₃.hom, assoc, Iso.inv_hom_id,
                      comp_id, comm₁₃, Iso.inv_hom_id_assoc]
      comm₂₄ := by simp only [← cancel_mono e₄.hom, assoc, Iso.inv_hom_id,
                      comp_id, comm₂₄, Iso.inv_hom_id_assoc]
      comm₃₄ := by simp only [← cancel_mono e₄.hom, assoc, Iso.inv_hom_id,
                      comp_id, comm₃₄, Iso.inv_hom_id_assoc] }

/-- Flipping a square by switching the top-right and the bottom-left objects. -/
@[simps]
/--
Definition of `flip` / `flip` 的定义

English:
definition flip
  signature: (sq : Square C)
  body: sq.f₁₃
  f₁₃ := sq.f₁₂
  f₂₄ := sq.f₃₄
  f₃₄ := sq.f₂₄
  fac := sq.fac.symm

中文:
定义 flip
  签名: (sq : Square C)
  定义体: sq.f₁₃
  f₁₃ := sq.f₁₂
  f₂₄ := sq.f₃₄
  f₃₄ := sq.f₂₄
  fac := sq.fac.symm

Depends on / 依赖: sq.f
-/
def flip (sq : Square C) : Square C where
  f₁₂ := sq.f₁₃
  f₁₃ := sq.f₁₂
  f₂₄ := sq.f₃₄
  f₃₄ := sq.f₂₄
  fac := sq.fac.symm

set_option backward.defeqAttrib.useBackward true in
/-- The functor which flips commutative squares. -/
@[simps]
/--
Definition of `flipFunctor` / `flipFunctor` 的定义

English:
definition flipFunctor
  signature: : Square C ⥤ Square C where
  body: flip
  map φ :=
    { τ₁ := φ.τ₁
      τ₂ := φ.τ₃
      τ₃ := φ.τ₂
      τ₄ := φ.τ₄ }

中文:
定义 flipFunctor
  签名: : Square C ⥤ Square C where
  定义体: flip
  map φ :=
    { τ₁ := φ.τ₁
      τ₂ := φ.τ₃
      τ₃ := φ.τ₂
      τ₄ := φ.τ₄ }
-/
def flipFunctor : Square C ⥤ Square C where
  obj := flip
  map φ :=
    { τ₁ := φ.τ₁
      τ₂ := φ.τ₃
      τ₃ := φ.τ₂
      τ₄ := φ.τ₄ }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Flipping commutative squares is an auto-equivalence. -/
@[simps]
/--
Definition of `flipEquivalence` / `flipEquivalence` 的定义

English:
definition flipEquivalence
  signature: : Square C ≌ Square C where
  body: flipFunctor
  inverse := flipFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 flipEquivalence
  签名: : Square C ≌ Square C where
  定义体: flipFunctor
  inverse := flipFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: flipFunctor
-/
def flipEquivalence : Square C ≌ Square C where
  functor := flipFunctor
  inverse := flipFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor `Square C ⥤ Arrow (Arrow C)` which sends a
commutative square `sq` to the obvious arrow from the left morphism of `sq`
to the right morphism of `sq`. -/
@[simps!]
/--
Definition of `toArrowArrowFunctor` / `toArrowArrowFunctor` 的定义

English:
definition toArrowArrowFunctor
  signature: : Square C ⥤ Arrow (Arrow C) where
  body: Arrow.mk (Arrow.homMk _ _ sq.fac : Arrow.mk sq.f₁₃ ⟶ Arrow.mk sq.f₂₄)
  map φ := Arrow.homMk (Arrow.homMk _ _ φ.comm₁₃.symm)
    (Arrow.homMk _ _ φ.comm₂₄.symm)

中文:
定义 toArrowArrowFunctor
  签名: : Square C ⥤ Arrow (Arrow C) where
  定义体: Arrow.mk (Arrow.homMk _ _ sq.fac : Arrow.mk sq.f₁₃ ⟶ Arrow.mk sq.f₂₄)
  map φ := Arrow.homMk (Arrow.homMk _ _ φ.comm₁₃.symm)
    (Arrow.homMk _ _ φ.comm₂₄.symm)

Depends on / 依赖: Arrow.homMk, Arrow.mk, sq.f, sq.fac
-/
def toArrowArrowFunctor : Square C ⥤ Arrow (Arrow C) where
  obj sq := Arrow.mk (Arrow.homMk _ _ sq.fac : Arrow.mk sq.f₁₃ ⟶ Arrow.mk sq.f₂₄)
  map φ := Arrow.homMk (Arrow.homMk _ _ φ.comm₁₃.symm)
    (Arrow.homMk _ _ φ.comm₂₄.symm)

/-- The functor `Arrow (Arrow C) ⥤ Square C` which sends
a morphism `Arrow.mk f ⟶ Arrow.mk g` to the commutative square
with `f` on the left side and `g` on the right side. -/
@[simps!]
/--
Definition of `fromArrowArrowFunctor` / `fromArrowArrowFunctor` 的定义

English:
definition fromArrowArrowFunctor
  signature: : Arrow (Arrow C) ⥤ Square C where
  body: { fac := f.hom.w, .. }
  map φ :=
    { τ₁ := φ.left.left
      τ₂ := φ.right.left
      τ₃ := φ.left.right
      τ₄ := φ.right.right
      comm₁₂ := Arrow.leftFunc.congr_map φ.w.symm
      comm₁₃ := φ.left.w.symm
      comm₂₄ := φ.right.w.symm
      comm₃₄ := Arrow.rightFunc.congr_map φ.w.symm }

中文:
定义 fromArrowArrowFunctor
  签名: : Arrow (Arrow C) ⥤ Square C where
  定义体: { fac := f.hom.w, .. }
  map φ :=
    { τ₁ := φ.left.left
      τ₂ := φ.right.left
      τ₃ := φ.left.right
      τ₄ := φ.right.right
      comm₁₂ := Arrow.leftFunc.congr_map φ.w.symm
      comm₁₃ := φ.left.w.symm
      comm₂₄ := φ.right.w.symm
      comm₃₄ := Arrow.rightFunc.congr_map φ.w.symm }

Depends on / 依赖: f.hom.w
-/
def fromArrowArrowFunctor : Arrow (Arrow C) ⥤ Square C where
  obj f := { fac := f.hom.w, .. }
  map φ :=
    { τ₁ := φ.left.left
      τ₂ := φ.right.left
      τ₃ := φ.left.right
      τ₄ := φ.right.right
      comm₁₂ := Arrow.leftFunc.congr_map φ.w.symm
      comm₁₃ := φ.left.w.symm
      comm₂₄ := φ.right.w.symm
      comm₃₄ := Arrow.rightFunc.congr_map φ.w.symm }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `Square C ≌ Arrow (Arrow C)` which sends a
commutative square `sq` to the obvious arrow from the left morphism of `sq`
to the right morphism of `sq`. -/
@[simps]
/--
Definition of `arrowArrowEquivalence` / `arrowArrowEquivalence` 的定义

English:
definition arrowArrowEquivalence
  signature: : Square C ≌ Arrow (Arrow C) where
  body: toArrowArrowFunctor
  inverse := fromArrowArrowFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 arrowArrowEquivalence
  签名: : Square C ≌ Arrow (Arrow C) where
  定义体: toArrowArrowFunctor
  inverse := fromArrowArrowFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: toArrowArrowFunctor
-/
def arrowArrowEquivalence : Square C ≌ Arrow (Arrow C) where
  functor := toArrowArrowFunctor
  inverse := fromArrowArrowFunctor
  unitIso := Iso.refl _
  counitIso := Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor `Square C ⥤ Arrow (Arrow C)` which sends a
commutative square `sq` to the obvious arrow from the top morphism of `sq`
to the bottom morphism of `sq`. -/
@[simps!]
/--
Definition of `toArrowArrowFunctor'` / `toArrowArrowFunctor'` 的定义

English:
definition toArrowArrowFunctor'
  signature: : Square C ⥤ Arrow (Arrow C) where
  body: Arrow.mk (Arrow.homMk _ _ sq.fac.symm : Arrow.mk sq.f₁₂ ⟶ Arrow.mk sq.f₃₄)
  map φ := Arrow.homMk (Arrow.homMk _ _ φ.comm₁₂.symm)
    (Arrow.homMk _ _ φ.comm₃₄.symm)

中文:
定义 toArrowArrowFunctor'
  签名: : Square C ⥤ Arrow (Arrow C) where
  定义体: Arrow.mk (Arrow.homMk _ _ sq.fac.symm : Arrow.mk sq.f₁₂ ⟶ Arrow.mk sq.f₃₄)
  map φ := Arrow.homMk (Arrow.homMk _ _ φ.comm₁₂.symm)
    (Arrow.homMk _ _ φ.comm₃₄.symm)

Depends on / 依赖: Arrow.homMk, Arrow.mk, sq.f, sq.fac.symm
-/
def toArrowArrowFunctor' : Square C ⥤ Arrow (Arrow C) where
  obj sq := Arrow.mk (Arrow.homMk _ _ sq.fac.symm : Arrow.mk sq.f₁₂ ⟶ Arrow.mk sq.f₃₄)
  map φ := Arrow.homMk (Arrow.homMk _ _ φ.comm₁₂.symm)
    (Arrow.homMk _ _ φ.comm₃₄.symm)

/-- The functor `Arrow (Arrow C) ⥤ Square C` which sends
a morphism `Arrow.mk f ⟶ Arrow.mk g` to the commutative square
with `f` on the top side and `g` on the bottom side. -/
@[simps!]
/--
Definition of `fromArrowArrowFunctor'` / `fromArrowArrowFunctor'` 的定义

English:
definition fromArrowArrowFunctor'
  signature: : Arrow (Arrow C) ⥤ Square C where
  body: { fac := f.hom.w.symm, .. }
  map φ :=
    { τ₁ := φ.left.left
      τ₂ := φ.left.right
      τ₃ := φ.right.left
      τ₄ := φ.right.right
      comm₁₂ := φ.left.w.symm
      comm₁₃ := Arrow.leftFunc.congr_map φ.w.symm
      comm₂₄ := Arrow.rightFunc.congr_map φ.w.symm
      comm₃₄ := φ.right.w.symm

中文:
定义 fromArrowArrowFunctor'
  签名: : Arrow (Arrow C) ⥤ Square C where
  定义体: { fac := f.hom.w.symm, .. }
  map φ :=
    { τ₁ := φ.left.left
      τ₂ := φ.left.right
      τ₃ := φ.right.left
      τ₄ := φ.right.right
      comm₁₂ := φ.left.w.symm
      comm₁₃ := Arrow.leftFunc.congr_map φ.w.symm
      comm₂₄ := Arrow.rightFunc.congr_map φ.w.symm
      comm₃₄ := φ.right.w.symm

Depends on / 依赖: f.hom.w.symm
-/
def fromArrowArrowFunctor' : Arrow (Arrow C) ⥤ Square C where
  obj f := { fac := f.hom.w.symm, .. }
  map φ :=
    { τ₁ := φ.left.left
      τ₂ := φ.left.right
      τ₃ := φ.right.left
      τ₄ := φ.right.right
      comm₁₂ := φ.left.w.symm
      comm₁₃ := Arrow.leftFunc.congr_map φ.w.symm
      comm₂₄ := Arrow.rightFunc.congr_map φ.w.symm
      comm₃₄ := φ.right.w.symm }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `Square C ≌ Arrow (Arrow C)` which sends a
commutative square `sq` to the obvious arrow from the top morphism of `sq`
to the bottom morphism of `sq`. -/
@[simps]
/--
Definition of `arrowArrowEquivalence'` / `arrowArrowEquivalence'` 的定义

English:
definition arrowArrowEquivalence'
  signature: : Square C ≌ Arrow (Arrow C) where
  body: toArrowArrowFunctor'
  inverse := fromArrowArrowFunctor'
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 arrowArrowEquivalence'
  签名: : Square C ≌ Arrow (Arrow C) where
  定义体: toArrowArrowFunctor'
  inverse := fromArrowArrowFunctor'
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: toArrowArrowFunctor
-/
def arrowArrowEquivalence' : Square C ≌ Arrow (Arrow C) where
  functor := toArrowArrowFunctor'
  inverse := fromArrowArrowFunctor'
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The top-left evaluation `Square C ⥤ C`. -/
@[simps]
/--
Definition of `evaluation₁` / `evaluation₁` 的定义

English:
definition evaluation₁
  signature: : Square C ⥤ C where
  body: sq.X₁
  map φ := φ.τ₁

中文:
定义 evaluation₁
  签名: : Square C ⥤ C where
  定义体: sq.X₁
  map φ := φ.τ₁

Depends on / 依赖: sq.X
-/
def evaluation₁ : Square C ⥤ C where
  obj sq := sq.X₁
  map φ := φ.τ₁

/-- The top-right evaluation `Square C ⥤ C`. -/
@[simps]
/--
Definition of `evaluation₂` / `evaluation₂` 的定义

English:
definition evaluation₂
  signature: : Square C ⥤ C where
  body: sq.X₂
  map φ := φ.τ₂

中文:
定义 evaluation₂
  签名: : Square C ⥤ C where
  定义体: sq.X₂
  map φ := φ.τ₂

Depends on / 依赖: sq.X
-/
def evaluation₂ : Square C ⥤ C where
  obj sq := sq.X₂
  map φ := φ.τ₂

/-- The bottom-left evaluation `Square C ⥤ C`. -/
@[simps]
/--
Definition of `evaluation₃` / `evaluation₃` 的定义

English:
definition evaluation₃
  signature: : Square C ⥤ C where
  body: sq.X₃
  map φ := φ.τ₃

中文:
定义 evaluation₃
  签名: : Square C ⥤ C where
  定义体: sq.X₃
  map φ := φ.τ₃

Depends on / 依赖: sq.X
-/
def evaluation₃ : Square C ⥤ C where
  obj sq := sq.X₃
  map φ := φ.τ₃

/-- The bottom-right evaluation `Square C ⥤ C`. -/
@[simps]
/--
Definition of `evaluation₄` / `evaluation₄` 的定义

English:
definition evaluation₄
  signature: : Square C ⥤ C where
  body: sq.X₄
  map φ := φ.τ₄

中文:
定义 evaluation₄
  签名: : Square C ⥤ C where
  定义体: sq.X₄
  map φ := φ.τ₄

Depends on / 依赖: sq.X
-/
def evaluation₄ : Square C ⥤ C where
  obj sq := sq.X₄
  map φ := φ.τ₄

/-- The map `Square C → Square Cᵒᵖ` which switches `X₁` and `X₃`, but
does not move `X₂` and `X₃`. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (sq : Square C)
  body: sq.f₂₄.op
  f₁₃ := sq.f₃₄.op
  f₂₄ := sq.f₁₂.op
  f₃₄ := sq.f₁₃.op
  fac := Quiver.Hom.unop_inj sq.fac

中文:
定义 op
  签名: (sq : Square C)
  定义体: sq.f₂₄.op
  f₁₃ := sq.f₃₄.op
  f₂₄ := sq.f₁₂.op
  f₃₄ := sq.f₁₃.op
  fac := Quiver.Hom.unop_inj sq.fac
-/
protected def op (sq : Square C) : Square Cᵒᵖ where
  f₁₂ := sq.f₂₄.op
  f₁₃ := sq.f₃₄.op
  f₂₄ := sq.f₁₂.op
  f₃₄ := sq.f₁₃.op
  fac := Quiver.Hom.unop_inj sq.fac

/-- The map `Square Cᵒᵖ → Square C` which switches `X₁` and `X₃`, but
does not move `X₂` and `X₃`. -/
@[simps]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: (sq : Square Cᵒᵖ)
  body: sq.f₂₄.unop
  f₁₃ := sq.f₃₄.unop
  f₂₄ := sq.f₁₂.unop
  f₃₄ := sq.f₁₃.unop
  fac := Quiver.Hom.op_inj sq.fac

中文:
定义 unop
  签名: (sq : Square Cᵒᵖ)
  定义体: sq.f₂₄.unop
  f₁₃ := sq.f₃₄.unop
  f₂₄ := sq.f₁₂.unop
  f₃₄ := sq.f₁₃.unop
  fac := Quiver.Hom.op_inj sq.fac
-/
protected def unop (sq : Square Cᵒᵖ) : Square C where
  f₁₂ := sq.f₂₄.unop
  f₁₃ := sq.f₃₄.unop
  f₂₄ := sq.f₁₂.unop
  f₃₄ := sq.f₁₃.unop
  fac := Quiver.Hom.op_inj sq.fac

set_option backward.defeqAttrib.useBackward true in
/-- The functor `(Square C)ᵒᵖ ⥤ Square Cᵒᵖ`. -/
@[simps]
/--
Definition of `opFunctor` / `opFunctor` 的定义

English:
definition opFunctor
  signature: : (Square C)ᵒᵖ ⥤ Square Cᵒᵖ where
  body: sq.unop.op
  map φ :=
    { τ₁ := φ.unop.τ₄.op
      τ₂ := φ.unop.τ₂.op
      τ₃ := φ.unop.τ₃.op
      τ₄ := φ.unop.τ₁.op
      comm₁₂ := Quiver.Hom.unop_inj (by simp)
      comm₁₃ := Quiver.Hom.unop_inj (by simp)
      comm₂₄ := Quiver.Hom.unop_inj (by simp)
      comm₃₄ := Quiver.Hom.unop_inj (by 

中文:
定义 opFunctor
  签名: : (Square C)ᵒᵖ ⥤ Square Cᵒᵖ where
  定义体: sq.unop.op
  map φ :=
    { τ₁ := φ.unop.τ₄.op
      τ₂ := φ.unop.τ₂.op
      τ₃ := φ.unop.τ₃.op
      τ₄ := φ.unop.τ₁.op
      comm₁₂ := Quiver.Hom.unop_inj (by simp)
      comm₁₃ := Quiver.Hom.unop_inj (by simp)
      comm₂₄ := Quiver.Hom.unop_inj (by simp)
      comm₃₄ := Quiver.Hom.unop_inj (by 

Depends on / 依赖: sq.unop.op
-/
def opFunctor : (Square C)ᵒᵖ ⥤ Square Cᵒᵖ where
  obj sq := sq.unop.op
  map φ :=
    { τ₁ := φ.unop.τ₄.op
      τ₂ := φ.unop.τ₂.op
      τ₃ := φ.unop.τ₃.op
      τ₄ := φ.unop.τ₁.op
      comm₁₂ := Quiver.Hom.unop_inj (by simp)
      comm₁₃ := Quiver.Hom.unop_inj (by simp)
      comm₂₄ := Quiver.Hom.unop_inj (by simp)
      comm₃₄ := Quiver.Hom.unop_inj (by simp) }

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `unopFunctor` / `unopFunctor` 的定义

English:
definition unopFunctor
  signature: : (Square Cᵒᵖ)ᵒᵖ ⥤ Square C where
  body: sq.unop.unop
  map φ :=
    { τ₁ := φ.unop.τ₄.unop
      τ₂ := φ.unop.τ₂.unop
      τ₃ := φ.unop.τ₃.unop
      τ₄ := φ.unop.τ₁.unop
      comm₁₂ := Quiver.Hom.op_inj (by simp)
      comm₁₃ := Quiver.Hom.op_inj (by simp)
      comm₂₄ := Quiver.Hom.op_inj (by simp)
      comm₃₄ := Quiver.Hom.op_inj (b

中文:
定义 unopFunctor
  签名: : (Square Cᵒᵖ)ᵒᵖ ⥤ Square C where
  定义体: sq.unop.unop
  map φ :=
    { τ₁ := φ.unop.τ₄.unop
      τ₂ := φ.unop.τ₂.unop
      τ₃ := φ.unop.τ₃.unop
      τ₄ := φ.unop.τ₁.unop
      comm₁₂ := Quiver.Hom.op_inj (by simp)
      comm₁₃ := Quiver.Hom.op_inj (by simp)
      comm₂₄ := Quiver.Hom.op_inj (by simp)
      comm₃₄ := Quiver.Hom.op_inj (b

Depends on / 依赖: sq.unop.unop
-/
def unopFunctor : (Square Cᵒᵖ)ᵒᵖ ⥤ Square C where
  obj sq := sq.unop.unop
  map φ :=
    { τ₁ := φ.unop.τ₄.unop
      τ₂ := φ.unop.τ₂.unop
      τ₃ := φ.unop.τ₃.unop
      τ₄ := φ.unop.τ₁.unop
      comm₁₂ := Quiver.Hom.op_inj (by simp)
      comm₁₃ := Quiver.Hom.op_inj (by simp)
      comm₂₄ := Quiver.Hom.op_inj (by simp)
      comm₃₄ := Quiver.Hom.op_inj (by simp) }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `opEquivalence` / `opEquivalence` 的定义

English:
definition opEquivalence
  signature: : (Square C)ᵒᵖ ≌ Square Cᵒᵖ where
  body: opFunctor
  inverse := unopFunctor.rightOp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 opEquivalence
  签名: : (Square C)ᵒᵖ ≌ Square Cᵒᵖ where
  定义体: opFunctor
  inverse := unopFunctor.rightOp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: opFunctor
-/
def opEquivalence : (Square C)ᵒᵖ ≌ Square Cᵒᵖ where
  functor := opFunctor
  inverse := unopFunctor.rightOp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The image of a commutative square by a functor. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (sq : Square C) (F : C ⥤ D)
  body: F.map sq.f₁₂
  f₁₃ := F.map sq.f₁₃
  f₂₄ := F.map sq.f₂₄
  f₃₄ := F.map sq.f₃₄
  fac := by simpa using F.congr_map sq.fac

中文:
定义 map
  签名: (sq : Square C) (F : C ⥤ D)
  定义体: F.map sq.f₁₂
  f₁₃ := F.map sq.f₁₃
  f₂₄ := F.map sq.f₂₄
  f₃₄ := F.map sq.f₃₄
  fac := by simpa using F.congr_map sq.fac

Depends on / 依赖: F.map, sq.f
-/
def map (sq : Square C) (F : C ⥤ D) : Square D where
  f₁₂ := F.map sq.f₁₂
  f₁₃ := F.map sq.f₁₃
  f₂₄ := F.map sq.f₂₄
  f₃₄ := F.map sq.f₃₄
  fac := by simpa using F.congr_map sq.fac

end Square

variable {C}

namespace Functor

/-- The functor `Square C ⥤ Square D` induced by a functor `C ⥤ D`. -/
@[simps]
/--
Definition of `mapSquare` / `mapSquare` 的定义

English:
definition mapSquare
  signature: (F : C ⥤ D)
  body: sq.map F
  map φ :=
    { τ₁ := F.map φ.τ₁
      τ₂ := F.map φ.τ₂
      τ₃ := F.map φ.τ₃
      τ₄ := F.map φ.τ₄
      comm₁₂ := by simpa only [Functor.map_comp] using! F.congr_map φ.comm₁₂
      comm₁₃ := by simpa only [Functor.map_comp] using! F.congr_map φ.comm₁₃
      comm₂₄ := by simpa only [Fun

中文:
定义 mapSquare
  签名: (F : C ⥤ D)
  定义体: sq.map F
  map φ :=
    { τ₁ := F.map φ.τ₁
      τ₂ := F.map φ.τ₂
      τ₃ := F.map φ.τ₃
      τ₄ := F.map φ.τ₄
      comm₁₂ := by simpa only [Functor.map_comp] using! F.congr_map φ.comm₁₂
      comm₁₃ := by simpa only [Functor.map_comp] using! F.congr_map φ.comm₁₃
      comm₂₄ := by simpa only [Fun

Depends on / 依赖: sq.map
-/
def mapSquare (F : C ⥤ D) : Square C ⥤ Square D where
  obj sq := sq.map F
  map φ :=
    { τ₁ := F.map φ.τ₁
      τ₂ := F.map φ.τ₂
      τ₃ := F.map φ.τ₃
      τ₄ := F.map φ.τ₄
      comm₁₂ := by simpa only [Functor.map_comp] using! F.congr_map φ.comm₁₂
      comm₁₃ := by simpa only [Functor.map_comp] using! F.congr_map φ.comm₁₃
      comm₂₄ := by simpa only [Functor.map_comp] using! F.congr_map φ.comm₂₄
      comm₃₄ := by simpa only [Functor.map_comp] using! F.congr_map φ.comm₃₄ }

end Functor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `F.mapSquare ⟶ G.mapSquare` induces
by a natural transformation `F ⟶ G`. -/
@[simps]
/--
Definition of `NatTrans.mapSquare` / `NatTrans.mapSquare` 的定义

English:
definition NatTrans.mapSquare
  signature: {F G : C ⥤ D} (τ : F ⟶ G)
  body: { τ₁ := τ.app _
      τ₂ := τ.app _
      τ₃ := τ.app _
      τ₄ := τ.app _ }

中文:
定义 NatTrans.mapSquare
  签名: {F G : C ⥤ D} (τ : F ⟶ G)
  定义体: { τ₁ := τ.app _
      τ₂ := τ.app _
      τ₃ := τ.app _
      τ₄ := τ.app _ }
-/
def NatTrans.mapSquare {F G : C ⥤ D} (τ : F ⟶ G) :
    F.mapSquare ⟶ G.mapSquare where
  app sq :=
    { τ₁ := τ.app _
      τ₂ := τ.app _
      τ₃ := τ.app _
      τ₄ := τ.app _ }

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `(C ⥤ D) ⥤ Square C ⥤ Square D`. -/
@[simps]
/--
Definition of `Square.mapFunctor` / `Square.mapFunctor` 的定义

English:
definition Square.mapFunctor
  signature: : (C ⥤ D) ⥤ Square C ⥤ Square D where
  body: F.mapSquare
  map τ := NatTrans.mapSquare τ

中文:
定义 Square.mapFunctor
  签名: : (C ⥤ D) ⥤ Square C ⥤ Square D where
  定义体: F.mapSquare
  map τ := NatTrans.mapSquare τ

Depends on / 依赖: F.mapSquare, mapSquare
-/
def Square.mapFunctor : (C ⥤ D) ⥤ Square C ⥤ Square D where
  obj F := F.mapSquare
  map τ := NatTrans.mapSquare τ

end CategoryTheory
