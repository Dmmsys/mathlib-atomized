/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# The category of points of a site

We define the category structure on the points of a site `(C, J)`:
a morphism between `Φ₁ ⟶ Φ₂` between two points consists of a
morphism `Φ₂.fiber ⟶ Φ₁.fiber` (SGA 4 IV 3.2).

## References
* [Alexander Grothendieck and Jean-Louis Verdier, *Exposé IV : Topos*,
  SGA 4 IV 3.2][sga-4-tome-1]

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace GrothendieckTopology.Point

/-- A morphism between points of a site consists of a morphism
between the functors `Point.fiber`, in the opposite direction. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (Φ₁ Φ₂ : Point.{w} J)
  axioms and operations (1):
    - hom : Φ₂.fiber ⟶ Φ₁.fiber

中文:
结构 Hom
  参数: (Φ₁ Φ₂ : Point.{w} J)
  公理与运算 (1 个):
    - hom : Φ₂.fiber ⟶ Φ₁.fiber
-/
structure Hom (Φ₁ Φ₂ : Point.{w} J) where
  /-- a natural transformation, in the opposite direction -/
  hom : Φ₂.fiber ⟶ Φ₁.fiber

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Point.{w} J)
  body: Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨g.hom ≫ f.hom⟩

@[ext]

中文:
实例 :
  签名: Category (Point.{w} J)
  定义体: Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨g.hom ≫ f.hom⟩

@[ext]
-/
instance : Category (Point.{w} J) where
  Hom := Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨g.hom ≫ f.hom⟩

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {Φ₁ Φ₂ : Point.{w} J} {f g : Φ₁ ⟶ Φ₂} (h : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext h

@[simp]

中文:
引理 hom_ext
  条件: {Φ₁ Φ₂ : Point.{w} J} {f g : Φ₁ ⟶ Φ₂} (h : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext h

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {Φ₁ Φ₂ : Point.{w} J} {f g : Φ₁ ⟶ Φ₂} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp]
/--
lemma `id_hom` / 引理 `id_hom`

English:
lemma id_hom
  given: (Φ : Point.{w} J)
  statement: Hom.hom (𝟙 Φ) = 𝟙 _
  proof: rfl

@[simp, reassoc]

中文:
引理 id_hom
  条件: (Φ : Point.{w} J)
  结论: Hom.hom (𝟙 Φ) = 𝟙 _
  证明: rfl

@[simp, reassoc]
-/
lemma id_hom (Φ : Point.{w} J) : Hom.hom (𝟙 Φ) = 𝟙 _ := rfl

@[simp, reassoc]
/--
lemma `comp_hom` / 引理 `comp_hom`

English:
lemma comp_hom
  given: {Φ₁ Φ₂ Φ₃ : Point.{w} J} (f : Φ₁ ⟶ Φ₂) (g : Φ₂ ⟶ Φ₃)
  proof: rfl

中文:
引理 comp_hom
  条件: {Φ₁ Φ₂ Φ₃ : Point.{w} J} (f : Φ₁ ⟶ Φ₂) (g : Φ₂ ⟶ Φ₃)
  证明: rfl
-/
lemma comp_hom {Φ₁ Φ₂ Φ₃ : Point.{w} J} (f : Φ₁ ⟶ Φ₂) (g : Φ₂ ⟶ Φ₃) :
    (f ≫ g).hom = g.hom ≫ f.hom := rfl

variable {A : Type u'} [Category.{v'} A]
  [HasColimitsOfSize.{w, w} A]

namespace Hom

variable {Φ₁ Φ₂ Φ₃ : Point.{w} J} (f : Φ₁ ⟶ Φ₂) (g : Φ₂ ⟶ Φ₃)

attribute [local simp] FunctorToTypes.naturality in
/-- The natural transformation on fibers of presheaves that is induced
by a morphism of points of a site. -/
@[simps]
/--
Definition of `presheafFiber` / `presheafFiber` 的定义

English:
definition presheafFiber
  signature: :
  body: Φ₂.presheafFiberDesc (fun X x => Φ₁.toPresheafFiber X (f.hom.app X x) P)

@[simp]

中文:
定义 presheafFiber
  签名: :
  定义体: Φ₂.presheafFiberDesc (fun X x => Φ₁.toPresheafFiber X (f.hom.app X x) P)

@[simp]

Depends on / 依赖: presheafFiber
-/
noncomputable def presheafFiber :
    Φ₂.presheafFiber (A := A) ⟶ Φ₁.presheafFiber where
  app P := Φ₂.presheafFiberDesc (fun X x => Φ₁.toPresheafFiber X (f.hom.app X x) P)

@[simp]
/--
lemma `presheafFiber_id` / 引理 `presheafFiber_id`

English:
lemma presheafFiber_id
  given: (Φ : Point.{w} J)
  proof: by
  cat_disch

@[reassoc, simp]

中文:
引理 presheafFiber_id
  条件: (Φ : Point.{w} J)
  证明: by
  cat_disch

@[reassoc, simp]

Depends on / 依赖: cat_disch
-/
lemma presheafFiber_id (Φ : Point.{w} J) :
    presheafFiber (𝟙 Φ) (A := A) = 𝟙 _ := by
  cat_disch

@[reassoc, simp]
/--
lemma `presheafFiber_comp` / 引理 `presheafFiber_comp`

English:
lemma presheafFiber_comp
  proof: by
  cat_disch

中文:
引理 presheafFiber_comp
  证明: by
  cat_disch

Depends on / 依赖: cat_disch, f.presheafFiber, g.presheafFiber, presheafFiber
-/
lemma presheafFiber_comp :
    (f ≫ g).presheafFiber (A := A) = g.presheafFiber ≫ f.presheafFiber := by
  cat_disch

/--
Definition of `sheafFiber` / `sheafFiber` 的定义

English:
abbreviation sheafFiber
  signature: :
  body: Functor.whiskerLeft _ f.presheafFiber

@[simp]

中文:
缩写 sheafFiber
  签名: :
  定义体: Functor.whiskerLeft _ f.presheafFiber

@[simp]

Depends on / 依赖: sheafFiber
-/
noncomputable abbrev sheafFiber :
    Φ₂.sheafFiber (A := A) ⟶ Φ₁.sheafFiber :=
  Functor.whiskerLeft _ f.presheafFiber

@[simp]
/--
lemma `sheafFiber_id` / 引理 `sheafFiber_id`

English:
lemma sheafFiber_id
  given: (Φ : Point.{w} J)
  proof: by
  cat_disch

@[reassoc, simp]

中文:
引理 sheafFiber_id
  条件: (Φ : Point.{w} J)
  证明: by
  cat_disch

@[reassoc, simp]

Depends on / 依赖: cat_disch
-/
lemma sheafFiber_id (Φ : Point.{w} J) :
    sheafFiber (𝟙 Φ) (A := A) = 𝟙 _ := by
  cat_disch

@[reassoc, simp]
/--
lemma `sheafFiber_comp` / 引理 `sheafFiber_comp`

English:
lemma sheafFiber_comp
  proof: by
  cat_disch

中文:
引理 sheafFiber_comp
  证明: by
  cat_disch

Depends on / 依赖: cat_disch, f.sheafFiber, g.sheafFiber, sheafFiber
-/
lemma sheafFiber_comp :
    (f ≫ g).sheafFiber (A := A) = g.sheafFiber ≫ f.sheafFiber := by
  cat_disch

end Hom

end GrothendieckTopology.Point

end CategoryTheory
