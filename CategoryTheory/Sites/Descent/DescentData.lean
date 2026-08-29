/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Descent data

In this file, given a pseudofunctor `F` from `LocallyDiscrete Cᵒᵖ` to `Cat`,
and a family of maps `f i : X i ⟶ S` in the category `C`,
we define the category `F.DescentData f` of objects over the `X i`
equipped with descent data relative to the morphisms `f i : X i ⟶ S`.

We show that up to an equivalence, the category `F.DescentData f` is unchanged
when we replace `S` by an isomorphic object, or the family `f i : X i ⟶ S`
by another family which generates the same sieve
(see `Pseudofunctor.DescentData.pullFunctorEquivalence`).

Given a presieve `R`, we introduce predicates `F.IsPrestackFor R` and `F.IsStackFor R`
saying the functor `F.DescentData (fun (f : R.category) ↦ f.obj.hom)` attached
to `R` is respectively fully faithful or an equivalence. We show that
`F` satisfies `F.IsPrestack J` for a Grothendieck topology `J` iff it
satisfies `F.IsPrestackFor R.arrows` for all covering sieves `R`.

## TODO (@joelriou, @chrisflav)
* Introduce multiple variants of `DescentData` (when `C` has pullbacks,
  when `F` also has a covariant functoriality, etc.).

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe t t' t'' v' v u' u

namespace CategoryTheory

open Opposite

namespace Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι -> C} (f : forall i, X i ⟶ S)

/--
Definition of `DescentData` / `DescentData` 的定义

English:
structure DescentData
  parameters: where
  axioms and operations (5):
    - obj((i : ι)) : F.obj (.mk (op (X i)))
    - hom(⦃Y) : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (_hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (_hf₂ : f₂ ≫ f i₂ = q := by cat_disch) : (F.map f₁.op.toLoc).toFunctor.obj (obj i₁) ⟶ (F.map f₂.op.toLoc).toFunctor.obj (obj i₂)
    - pullHom_hom(⦃Y' Y) : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q') ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) : pullHom (hom q f₁ f₂) g gf₁ gf₂ = hom q' gf₁ gf₂  [default: by cat_disch]
    - hom_self(⦃Y) : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (_ : g ≫ f i = q) : hom q g g = 𝟙 _  [default: by cat_disch]
    - hom_comp(⦃Y) : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) : hom q f₁ f₂ hf₁ hf₂ ≫ hom q f₂ f₃ hf₂ hf₃ = hom q f₁ f₃ hf₁ hf₃  [default: by cat_disch]

中文:
结构 DescentData
  参数: where
  公理与运算 (5 个):
    - obj((i : ι)) : F.obj (.mk (op (X i)))
    - hom(⦃Y) : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (_hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (_hf₂ : f₂ ≫ f i₂ = q := by cat_disch) : (F.map f₁.op.toLoc).toFunctor.obj (obj i₁) ⟶ (F.map f₂.op.toLoc).toFunctor.obj (obj i₂)
    - pullHom_hom(⦃Y' Y) : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q') ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) : pullHom (hom q f₁ f₂) g gf₁ gf₂ = hom q' gf₁ gf₂  [默认: by cat_disch]
    - hom_self(⦃Y) : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (_ : g ≫ f i = q) : hom q g g = 𝟙 _  [默认: by cat_disch]
    - hom_comp(⦃Y) : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) : hom q f₁ f₂ hf₁ hf₂ ≫ hom q f₂ f₃ hf₂ hf₃ = hom q f₁ f₃ hf₁ hf₃  [默认: by cat_disch]

Depends on / 依赖: F.map, cat_disch, hom_self, op.toLoc, pullHom, pullHom_hom, toFunctor, toFunctor.obj
-/
structure DescentData where
  /-- The objects over `X i` for all `i` -/
  obj (i : ι) : F.obj (.mk (op (X i)))
  /-- The compatibility morphisms after pullbacks. It follows from the conditions
  `hom_self` and `hom_comp` that these are isomorphisms, see
  `CategoryTheory.Pseudofunctor.DescentData.iso` below. -/
  hom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (_hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (_hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
      (F.map f₁.op.toLoc).toFunctor.obj (obj i₁) ⟶ (F.map f₂.op.toLoc).toFunctor.obj (obj i₂)
  pullHom_hom ⦃Y' Y : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q')
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
      pullHom (hom q f₁ f₂) g gf₁ gf₂ = hom q' gf₁ gf₂ := by cat_disch
  hom_self ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (_ : g ≫ f i = q) :
      hom q g g = 𝟙 _ := by cat_disch
  hom_comp ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃)
      (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
      hom q f₁ f₂ hf₁ hf₂ ≫ hom q f₂ f₃ hf₂ hf₃ = hom q f₁ f₃ hf₁ hf₃ := by cat_disch

namespace DescentData

variable {F f} (D : F.DescentData f)

attribute [local simp] hom_self pullHom_hom
attribute [reassoc (attr := simp)] hom_comp

/-- The morphisms `DescentData.hom`, as isomorphisms. -/
@[simps]
/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: ⦃Y
  body: D.hom q f₁ f₂
  inv := D.hom q f₂ f₁

中文:
定义 iso
  签名: ⦃Y
  定义体: D.hom q f₁ f₂
  inv := D.hom q f₂ f₁

Depends on / 依赖: D.hom, D.obj, F.map, cat_disch, op.toLoc, toFunctor, toFunctor.obj
-/
def iso ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (_hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (_hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    (F.map f₁.op.toLoc).toFunctor.obj (D.obj i₁) ≅
      (F.map f₂.op.toLoc).toFunctor.obj (D.obj i₂) where
  hom := D.hom q f₁ f₂
  inv := D.hom q f₂ f₁

instance {Y : C} (q : Y ⟶ S) {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    IsIso (D.hom q f₁ f₂ hf₁ hf₂) :=
  (D.iso q f₁ f₂).isIso_hom

/-- The type of morphisms in the category `Pseudofunctor.DescentData`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (D₁ D₂ : F.DescentData f)
  axioms and operations (2):
    - hom((i : ι)) : D₁.obj i ⟶ D₂.obj i
    - comm(⦃Y) : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) : (F.map f₁.op.toLoc).toFunctor.map (hom i₁) ≫ D₂.hom q f₁ f₂ = D₁.hom q f₁ f₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (hom i₂)  [default: by cat_disch]

中文:
结构 Hom
  参数: (D₁ D₂ : F.DescentData f)
  公理与运算 (2 个):
    - hom((i : ι)) : D₁.obj i ⟶ D₂.obj i
    - comm(⦃Y) : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) : (F.map f₁.op.toLoc).toFunctor.map (hom i₁) ≫ D₂.hom q f₁ f₂ = D₁.hom q f₁ f₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (hom i₂)  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (D₁ D₂ : F.DescentData f) where
  /-- The morphisms between the `obj` fields of descent data. -/
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (F.map f₁.op.toLoc).toFunctor.map (hom i₁) ≫ D₂.hom q f₁ f₂ =
        D₁.hom q f₁ f₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (hom i₂) := by cat_disch

attribute [reassoc (attr := local simp)] Hom.comm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (F.DescentData f)
  body: Hom
  id D := { hom _ := 𝟙 _ }
  comp φ φ' := { hom i := φ.hom i ≫ φ'.hom i }

@[ext]

中文:
实例 :
  签名: Category (F.DescentData f)
  定义体: Hom
  id D := { hom _ := 𝟙 _ }
  comp φ φ' := { hom i := φ.hom i ≫ φ'.hom i }

@[ext]
-/
instance : Category (F.DescentData f) where
  Hom := Hom
  id D := { hom _ := 𝟙 _ }
  comp φ φ' := { hom i := φ.hom i ≫ φ'.hom i }

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {D₁ D₂ : F.DescentData f} {φ φ' : D₁ ⟶ D₂}
  proof: Hom.ext (funext h)

@[simp]

中文:
引理 hom_ext
  结论: {D₁ D₂ : F.DescentData f} {φ φ' : D₁ ⟶ D₂}
  证明: Hom.ext (funext h)

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {D₁ D₂ : F.DescentData f} {φ φ' : D₁ ⟶ D₂}
    (h : forall i, φ.hom i = φ'.hom i) : φ = φ' :=
  Hom.ext (funext h)

@[simp]
/--
lemma `id_hom` / 引理 `id_hom`

English:
lemma id_hom
  given: (D : F.DescentData f) (i : ι)
  statement: Hom.hom (𝟙 D) i = 𝟙 _
  proof: rfl

@[simp, reassoc]

中文:
引理 id_hom
  条件: (D : F.DescentData f) (i : ι)
  结论: Hom.hom (𝟙 D) i = 𝟙 _
  证明: rfl

@[simp, reassoc]
-/
lemma id_hom (D : F.DescentData f) (i : ι) : Hom.hom (𝟙 D) i = 𝟙 _ := rfl

@[simp, reassoc]
/--
lemma `comp_hom` / 引理 `comp_hom`

English:
lemma comp_hom
  given: {D₁ D₂ D₃ : F.DescentData f} (φ : D₁ ⟶ D₂) (φ' : D₂ ⟶ D₃) (i : ι)
  proof: rfl

中文:
引理 comp_hom
  条件: {D₁ D₂ D₃ : F.DescentData f} (φ : D₁ ⟶ D₂) (φ' : D₂ ⟶ D₃) (i : ι)
  证明: rfl
-/
lemma comp_hom {D₁ D₂ D₃ : F.DescentData f} (φ : D₁ ⟶ D₂) (φ' : D₂ ⟶ D₃) (i : ι) :
    (φ ≫ φ').hom i = φ.hom i ≫ φ'.hom i := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a family of morphisms `f : X i ⟶ S`, and `M : F.obj (.mk (op S))`,
this is the object in `F.DescentData f` that is obtained by pulling back `M`
over the `X i`. -/
@[simps]
/--
Definition of `ofObj` / `ofObj` 的定义

English:
definition ofObj
  signature: (M : F.obj (.mk (op S)))
  body: (F.map (f i).op.toLoc).toFunctor.obj M
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    (F.mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc (by grind)).inv.toNatTrans.app _ ≫
      (F.mapComp' (f i₂).op.toLoc f₂.op.toLoc q.op.toLoc (by grind)).hom.toNatTrans.app _
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂

中文:
定义 ofObj
  签名: (M : F.obj (.mk (op S)))
  定义体: (F.map (f i).op.toLoc).toFunctor.obj M
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    (F.mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc (by grind)).inv.toNatTrans.app _ ≫
      (F.mapComp' (f i₂).op.toLoc f₂.op.toLoc q.op.toLoc (by grind)).hom.toNatTrans.app _
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂

Depends on / 依赖: F.map, op.toLoc, toFunctor, toFunctor.obj
-/
def ofObj (M : F.obj (.mk (op S))) : F.DescentData f where
  obj i := (F.map (f i).op.toLoc).toFunctor.obj M
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    (F.mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc (by grind)).inv.toNatTrans.app _ ≫
      (F.mapComp' (f i₂).op.toLoc f₂.op.toLoc q.op.toLoc (by grind)).hom.toNatTrans.app _
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    simp only [pullHom, Functor.map_comp, Category.assoc,
      F.mapComp'₀₁₃_inv_app (f i₁).op.toLoc f₁.op.toLoc g.op.toLoc q.op.toLoc
        gf₁.op.toLoc q'.op.toLoc (by grind) (by grind) (by grind),
      F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app (f i₂).op.toLoc f₂.op.toLoc g.op.toLoc
      q.op.toLoc gf₂.op.toLoc q'.op.toLoc (by grind) (by grind) (by grind)]

/-- Constructor for isomorphisms in `Pseudofunctor.DescentData`. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {D₁ D₂ : F.DescentData f} (e : forall (i : ι), D₁.obj i ≅ D₂.obj i)
  body: { hom i := (e i).hom }
  inv :=
    { hom i := (e i).inv
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        rw [← cancel_mono ((F.map f₂.op.toLoc).toFunctor.map (e i₂).hom)]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.map_inv_hom_id]; rw [Category.comp_id]; rw [← cancel_epi ((F.map f₁.op.toLoc)

中文:
定义 isoMk
  签名: {D₁ D₂ : F.DescentData f} (e : 对任意 (i : ι), D₁.obj i ≅ D₂.obj i)
  定义体: { hom i := (e i).hom }
  inv :=
    { hom i := (e i).inv
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        rw [← cancel_mono ((F.map f₂.op.toLoc).toFunctor.map (e i₂).hom)]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.map_inv_hom_id]; rw [Category.comp_id]; rw [← cancel_epi ((F.map f₁.op.toLoc)

Depends on / 依赖: Category, Category.assoc, Category.comp_id, F.map, Iso.map_hom_inv_id_assoc, Iso.map_inv_hom_id, cancel_epi, cancel_mono, cat_disch, comp_id, map_hom_inv_id_assoc, map_inv_hom_id, op.toLoc, toFunctor, toFunctor.map
-/
def isoMk {D₁ D₂ : F.DescentData f} (e : forall (i : ι), D₁.obj i ≅ D₂.obj i)
    (comm : forall ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
    (F.map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫ D₂.hom q f₁ f₂ =
      D₁.hom q f₁ f₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (e i₂).hom := by cat_disch) : D₁ ≅ D₂ where
  hom :=
    { hom i := (e i).hom }
  inv :=
    { hom i := (e i).inv
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        rw [← cancel_mono ((F.map f₂.op.toLoc).toFunctor.map (e i₂).hom)]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.map_inv_hom_id]; rw [Category.comp_id]; rw [← cancel_epi ((F.map f₁.op.toLoc).toFunctor.map (e i₁).hom)]; rw [Iso.map_hom_inv_id_assoc]; rw [comm q f₁ f₂ hf₁ hf₂] }

end DescentData

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `F.obj (.mk (op S)) ⥤ F.DescentData f`. -/
@[simps]
/--
Definition of `toDescentData` / `toDescentData` 的定义

English:
definition toDescentData
  signature: : F.obj (.mk (op S)) ⥤ F.DescentData f where
  body: .ofObj M
  map {M M'} φ := { hom i := (F.map (f i).op.toLoc).toFunctor.map φ }

中文:
定义 toDescentData
  签名: : F.obj (.mk (op S)) ⥤ F.DescentData f where
  定义体: .ofObj M
  map {M M'} φ := { hom i := (F.map (f i).op.toLoc).toFunctor.map φ }
-/
def toDescentData : F.obj (.mk (op S)) ⥤ F.DescentData f where
  obj M := .ofObj M
  map {M M'} φ := { hom i := (F.map (f i).op.toLoc).toFunctor.map φ }

namespace DescentData

section

variable {F f} {S' : C} {p : S' ⟶ S} {ι' : Type t'} {X' : ι' -> C} {f' : forall j, X' j ⟶ S'}
  {α : ι' -> ι} {p' : forall j, X' j ⟶ X (α j)} (w : forall j, p' j ≫ f (α j) = f' j ≫ p)

/--
Definition of `pullFunctorObjHom` / `pullFunctorObjHom` 的定义

English:
definition pullFunctorObjHom
  signature: (D : F.DescentData f)
  body: (F.mapComp (p' j₁).op.toLoc f₁.op.toLoc).inv.toNatTrans.app _ ≫
    D.hom (q ≫ p) (f₁ ≫ p' _) (f₂ ≫ p' _) (by simp [w, reassoc_of% hf₁])
      (by simp [w, reassoc_of% hf₂]) ≫
    (F.mapComp (p' j₂).op.toLoc f₂.op.toLoc).hom.toNatTrans.app _

中文:
定义 pullFunctorObjHom
  签名: (D : F.DescentData f)
  定义体: (F.mapComp (p' j₁).op.toLoc f₁.op.toLoc).inv.toNatTrans.app _ ≫
    D.hom (q ≫ p) (f₁ ≫ p' _) (f₂ ≫ p' _) (by simp [w, reassoc_of% hf₁])
      (by simp [w, reassoc_of% hf₂]) ≫
    (F.mapComp (p' j₂).op.toLoc f₂.op.toLoc).hom.toNatTrans.app _

Depends on / 依赖: D.hom, D.obj, F.map, F.mapComp, cat_disch, hom.toNatTrans.app, inv.toNatTrans.app, mapComp, op.toLoc, reassoc_of, toFunctor, toFunctor.obj, toNatTrans
-/
def pullFunctorObjHom (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S') ⦃j₁ j₂ : ι'⦄ (f₁ : Y ⟶ X' j₁) (f₂ : Y ⟶ X' j₂)
    (hf₁ : f₁ ≫ f' j₁ = q := by cat_disch) (hf₂ : f₂ ≫ f' j₂ = q := by cat_disch) :
    (F.map f₁.op.toLoc).toFunctor.obj ((F.map (p' j₁).op.toLoc).toFunctor.obj (D.obj (α j₁))) ⟶
      (F.map f₂.op.toLoc).toFunctor.obj ((F.map (p' j₂).op.toLoc).toFunctor.obj (D.obj (α j₂))) :=
  (F.mapComp (p' j₁).op.toLoc f₁.op.toLoc).inv.toNatTrans.app _ ≫
    D.hom (q ≫ p) (f₁ ≫ p' _) (f₂ ≫ p' _) (by simp [w, reassoc_of% hf₁])
      (by simp [w, reassoc_of% hf₂]) ≫
    (F.mapComp (p' j₂).op.toLoc f₂.op.toLoc).hom.toNatTrans.app _

set_option backward.isDefEq.respectTransparency false in -- Needed below.
@[reassoc]
/--
lemma `pullFunctorObjHom_eq` / 引理 `pullFunctorObjHom_eq`

English:
lemma pullFunctorObjHom_eq
  statement: (D : F.DescentData f)
  proof: by
  subst hq' hf₁' hf₂'
  simp [mapComp'_eq_mapComp, pullFunctorObjHom]

中文:
引理 pullFunctorObjHom_eq
  结论: (D : F.DescentData f)
  证明: by
  subst hq' hf₁' hf₂'
  simp [mapComp'_eq_mapComp, pullFunctorObjHom]

Depends on / 依赖: Category, Category.assoc, D.hom, F.mapComp, _eq_mapComp, cat_disch, hom.toNatTrans.app, inv.toNatTrans.app, mapComp, pullFunctorObjHom, reassoc_of, toNatTrans
-/
lemma pullFunctorObjHom_eq (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S') ⦃j₁ j₂ : ι'⦄ (f₁ : Y ⟶ X' j₁) (f₂ : Y ⟶ X' j₂)
    (q' : Y ⟶ S) (f₁' : Y ⟶ X (α j₁)) (f₂' : Y ⟶ X (α j₂))
    (hf₁ : f₁ ≫ f' j₁ = q := by cat_disch) (hf₂ : f₂ ≫ f' j₂ = q := by cat_disch)
    (hq' : q ≫ p = q' := by cat_disch)
    (hf₁' : f₁ ≫ p' j₁ = f₁' := by cat_disch)
    (hf₂' : f₂ ≫ p' j₂ = f₂' := by cat_disch) :
  pullFunctorObjHom w D q f₁ f₂ =
    (F.mapComp' _ _ _).inv.toNatTrans.app _ ≫ D.hom q' f₁' f₂'
      (by rw [← hq', ← hf₁', Category.assoc, w, reassoc_of% hf₁])
      (by rw [← hq', ← hf₂', Category.assoc, w, reassoc_of% hf₂]) ≫
      (F.mapComp' _ _ _).hom.toNatTrans.app _ := by
  subst hq' hf₁' hf₂'
  simp [mapComp'_eq_mapComp, pullFunctorObjHom]

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `pullFunctor`. -/
@[simps]
/--
Definition of `pullFunctorObj` / `pullFunctorObj` 的定义

English:
definition pullFunctorObj
  signature: (D : F.DescentData f)
  body: (F.map (p' _).op.toLoc).toFunctor.obj (D.obj (α j))
  hom Y q j₁ j₂ f₁ f₂ hf₁ hf₂ := pullFunctorObjHom w _ _ _ _
  pullHom_hom Y' Y g q q' hq j₁ j₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    rw [pullFunctorObjHom_eq _ _ _ _ _ (q' ≫ p) (gf₁ ≫ p' j₁) (gf₂ ≫ p' j₂)]; rw [pullFunctorObjHom_eq _ _ _ _ _ (

中文:
定义 pullFunctorObj
  签名: (D : F.DescentData f)
  定义体: (F.map (p' _).op.toLoc).toFunctor.obj (D.obj (α j))
  hom Y q j₁ j₂ f₁ f₂ hf₁ hf₂ := pullFunctorObjHom w _ _ _ _
  pullHom_hom Y' Y g q q' hq j₁ j₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    rw [pullFunctorObjHom_eq _ _ _ _ _ (q' ≫ p) (gf₁ ≫ p' j₁) (gf₂ ≫ p' j₂)]; rw [pullFunctorObjHom_eq _ _ _ _ _ (

Depends on / 依赖: D.obj, F.map, op.toLoc, toFunctor, toFunctor.obj
-/
def pullFunctorObj (D : F.DescentData f) :
    F.DescentData f' where
  obj j := (F.map (p' _).op.toLoc).toFunctor.obj (D.obj (α j))
  hom Y q j₁ j₂ f₁ f₂ hf₁ hf₂ := pullFunctorObjHom w _ _ _ _
  pullHom_hom Y' Y g q q' hq j₁ j₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    rw [pullFunctorObjHom_eq _ _ _ _ _ (q' ≫ p) (gf₁ ≫ p' j₁) (gf₂ ≫ p' j₂)]; rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)]
    rw [← D.pullHom_hom g (q ≫ p) (q' ≫ p) (by rw [reassoc_of% hq])
      (f₁ ≫ p' j₁) (f₂ ≫ p' j₂) (by rw [Category.assoc, w, reassoc_of% hf₁])
      (by rw [Category.assoc, w, reassoc_of% hf₂]) (gf₁ ≫ p' j₁) (gf₂ ≫ p' j₂)
      (by cat_disch) (by cat_disch)]
    dsimp [pullHom]
    simp only [Functor.map_comp, Category.assoc]
    rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc _ _ _ _ _ _ _ _ (by cat_disch)]; rw [mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app _ _ _ _ _ _ _ _ _ (by cat_disch)]
  hom_self Y q j g hg := by
    rw [pullFunctorObjHom_eq _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl]; rw [D.hom_self _ _ (by cat_disch)]
    simp
  hom_comp Y q j₁ j₂ j₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)]; rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₂ ≫ p' j₂) (f₃ ≫ p' j₃)]; rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₃ ≫ p' j₃)]
    simp

variable (F)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a family of morphisms `f : X i ⟶ S` and `f' : X' j ⟶ S'`, and suitable
commutative diagrams `p' j ≫ f (α j) = f' j ≫ p`, this is the
induced functor `F.DescentData f ⥤ F.DescentData f'`. (Up to a (unique) isomorphism,
this functor only depends on `f` and `f'`, see `pullFunctorIso`.) -/
@[simps]
/--
Definition of `pullFunctor` / `pullFunctor` 的定义

English:
definition pullFunctor
  signature: : F.DescentData f ⥤ F.DescentData f' where
  body: pullFunctorObj w D
  map {D₁ D₂} φ :=
    { hom j := (F.map (p' j).op.toLoc).toFunctor.map (φ.hom (α j))
      comm Y q j₁ j₂ f₁ f₂ hf₁ hf₂ := by
        have := φ.comm (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)
          (by rw [Category.assoc, w, reassoc_of% hf₁])
          (by rw [Category.assoc, w, reass

中文:
定义 pullFunctor
  签名: : F.DescentData f ⥤ F.DescentData f' where
  定义体: pullFunctorObj w D
  map {D₁ D₂} φ :=
    { hom j := (F.map (p' j).op.toLoc).toFunctor.map (φ.hom (α j))
      comm Y q j₁ j₂ f₁ f₂ hf₁ hf₂ := by
        have := φ.comm (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)
          (by rw [Category.assoc, w, reassoc_of% hf₁])
          (by rw [Category.assoc, w, reass

Depends on / 依赖: pullFunctorObj
-/
def pullFunctor : F.DescentData f ⥤ F.DescentData f' where
  obj D := pullFunctorObj w D
  map {D₁ D₂} φ :=
    { hom j := (F.map (p' j).op.toLoc).toFunctor.map (φ.hom (α j))
      comm Y q j₁ j₂ f₁ f₂ hf₁ hf₂ := by
        have := φ.comm (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)
          (by rw [Category.assoc, w, reassoc_of% hf₁])
          (by rw [Category.assoc, w, reassoc_of% hf₂])
        dsimp at this ⊢
        rw [pullFunctorObjHom_eq_assoc _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)]; rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)]
        dsimp
        rw [mapComp'_inv_naturality_assoc]; rw [← mapComp'_hom_naturality]; rw [reassoc_of% this] }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toDescentDataCompPullFunctorIso` / `toDescentDataCompPullFunctorIso` 的定义

English:
definition toDescentDataCompPullFunctorIso
  signature: :
  body: NatIso.ofComponents
    (fun M => isoMk (fun i => (Cat.Hom.toNatIso
        (F.isoMapOfCommSq (CommSq.mk (w i)).op.toLoc)).symm.app M)
      (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ => by
        dsimp
        rw [F.isoMapOfCommSq_eq _ _ rfl]; rw [F.isoMapOfCommSq_eq _ _ rfl]
        dsimp
        simp only [Fu

中文:
定义 toDescentDataCompPullFunctorIso
  签名: :
  定义体: NatIso.ofComponents
    (fun M => isoMk (fun i => (Cat.Hom.toNatIso
        (F.isoMapOfCommSq (CommSq.mk (w i)).op.toLoc)).symm.app M)
      (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ => by
        dsimp
        rw [F.isoMapOfCommSq_eq _ _ rfl]; rw [F.isoMapOfCommSq_eq _ _ rfl]
        dsimp
        simp only [Fu

Depends on / 依赖: Cat.Hom.toNatIso, Category, Category.assoc, CommSq, CommSq.mk, F.isoMapOfCommSq, F.isoMapOfCommSq_eq, F.mapComp, Functor, Functor.map_comp, NatIso, NatIso.ofComponents, isoMapOfCommSq, isoMapOfCommSq_eq, mapComp, map_comp, ofComponents, op.toLoc, p.op.toLoc, pullFunctorObjHom_eq
-/
def toDescentDataCompPullFunctorIso :
    F.toDescentData f ⋙ pullFunctor F w ≅ (F.map p.op.toLoc).toFunctor ⋙ F.toDescentData f' :=
  NatIso.ofComponents
    (fun M => isoMk (fun i => (Cat.Hom.toNatIso
        (F.isoMapOfCommSq (CommSq.mk (w i)).op.toLoc)).symm.app M)
      (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ => by
        dsimp
        rw [F.isoMapOfCommSq_eq _ _ rfl]; rw [F.isoMapOfCommSq_eq _ _ rfl]
        dsimp
        simp only [Functor.map_comp, Category.assoc]
        rw [← F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app_assoc p.op.toLoc
            (f' i₁).op.toLoc f₁.op.toLoc _ q.op.toLoc (p.op.toLoc ≫ q.op.toLoc) rfl
            (by grind) (by grind) M]; rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' i₁) (f₂ ≫ p' i₂)]; rw [← cancel_mono ((F.mapComp' (f' i₂).op.toLoc f₂.op.toLoc q.op.toLoc
            (by grind)).inv.toNatTrans.app _)]
        dsimp
        simp only [Category.assoc,
          ← F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app p.op.toLoc
            (f' i₂).op.toLoc f₂.op.toLoc _ q.op.toLoc (p.op.toLoc ≫ q.op.toLoc) rfl
            (by grind) (by grind) M,
          ← F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc (f (α i₁)).op.toLoc
            (p' i₁).op.toLoc f₁.op.toLoc (p.op.toLoc ≫ (f' i₁).op.toLoc) _
            (p.op.toLoc ≫ q.op.toLoc) (by grind) rfl (by grind) M,
          F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc (f (α i₂)).op.toLoc
            (p' i₂).op.toLoc f₂.op.toLoc (p.op.toLoc ≫ (f' i₂).op.toLoc) _
            (p.op.toLoc ≫ q.op.toLoc) (by grind) rfl (by grind) M]
        simp))
    (fun f => by
      ext i
      exact (F.isoMapOfCommSq (CommSq.mk (w i)).op.toLoc).inv.toNatTrans.naturality f)

set_option backward.isDefEq.respectTransparency false in
/-- Up to a (unique) isomorphism, the functor
`pullFunctor : F.DescentData f ⥤ F.DescentData f'` does not depend
on the auxiliary data. -/
@[simps!]
/--
Definition of `pullFunctorIso` / `pullFunctorIso` 的定义

English:
definition pullFunctorIso
  signature: {β : ι' -> ι} {p'' : forall j, X' j ⟶ X (β j)}
  body: NatIso.ofComponents (fun D => isoMk (fun j => D.iso _ _ _) (by
    intro Y q j₁ j₂ f₁ f₂ hf₁ hf₂
    dsimp
    rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) _ _ rfl (by cat_disch) (by cat_disch)]; rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) _ _ rfl (by cat_disch) (by cat_disch)]; rw [map_eq_pullHom_asso

中文:
定义 pullFunctorIso
  签名: {β : ι' -> ι} {p'' : 对任意 j, X' j ⟶ X (β j)}
  定义体: NatIso.ofComponents (fun D => isoMk (fun j => D.iso _ _ _) (by
    intro Y q j₁ j₂ f₁ f₂ hf₁ hf₂
    dsimp
    rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) _ _ rfl (by cat_disch) (by cat_disch)]; rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) _ _ rfl (by cat_disch) (by cat_disch)]; rw [map_eq_pullHom_asso

Depends on / 依赖: Cat.Hom.hom_inv_id_toNatTrans_app_assoc, Category, Category.assoc, D.iso, NatIso, NatIso.ofComponents, cat_disch, hom_inv_id_toNatTrans_app_assoc, map_eq_pullHom, map_eq_pullHom_assoc, ofComponents, pullFunctorObjHom_eq
-/
def pullFunctorIso {β : ι' -> ι} {p'' : forall j, X' j ⟶ X (β j)}
    (w' : forall j, p'' j ≫ f (β j) = f' j ≫ p) :
    pullFunctor F w ≅ pullFunctor F w' :=
  NatIso.ofComponents (fun D => isoMk (fun j => D.iso _ _ _) (by
    intro Y q j₁ j₂ f₁ f₂ hf₁ hf₂
    dsimp
    rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) _ _ rfl (by cat_disch) (by cat_disch)]; rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) _ _ rfl (by cat_disch) (by cat_disch)]; rw [map_eq_pullHom_assoc _ _ (f₁ ≫ p' j₁) (f₁ ≫ p'' j₁) (by cat_disch) (by cat_disch)]; rw [map_eq_pullHom _ _ (f₂ ≫ p' j₂) (f₂ ≫ p'' j₂) (by cat_disch) (by cat_disch)]
    simp only [Cat.Hom.hom_inv_id_toNatTrans_app_assoc, Category.assoc]
    rw [pullHom_hom _ _ _ (q ≫ p) (by rw [w]; rw [reassoc_of% hf₁]) _ _
        rfl (by cat_disch) _ _ rfl rfl, hom_comp_assoc,
      pullHom_hom _ _ _ (q ≫ p) (by rw [w, reassoc_of% hf₂]) _ _
        rfl (by cat_disch) _ _ rfl rfl, hom_comp_assoc]))
    (fun φ => by
      ext j
      exact φ.comm _ _ _ rfl (by cat_disch))

set_option backward.isDefEq.respectTransparency false in
variable (S) in
/-- The functor `F.DescentData f ⥤ F.DescentData f` corresponding to `pullFunctor`
applied to identity morphisms is isomorphic to the identity functor. -/
@[simps!]
/--
Definition of `pullFunctorIdIso` / `pullFunctorIdIso` 的定义

English:
definition pullFunctorIdIso
  signature: :
  body: NatIso.ofComponents (fun D => isoMk (fun i => (Cat.Hom.toNatIso (F.mapId _)).app _) (by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    dsimp
    rw [pullFunctorObjHom_eq_assoc _ _ _ _ _ q f₁ f₂ rfl]
    simp [mapComp'_id_comp_inv_app_assoc, mapComp'_id_comp_hom_app, ← Functor.map_comp]))

中文:
定义 pullFunctorIdIso
  签名: :
  定义体: NatIso.ofComponents (fun D => isoMk (fun i => (Cat.Hom.toNatIso (F.mapId _)).app _) (by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    dsimp
    rw [pullFunctorObjHom_eq_assoc _ _ _ _ _ q f₁ f₂ rfl]
    simp [mapComp'_id_comp_inv_app_assoc, mapComp'_id_comp_hom_app, ← Functor.map_comp]))

Depends on / 依赖: DescentData, F.DescentData
-/
def pullFunctorIdIso :
    pullFunctor F (p := 𝟙 S) (p' := fun _ => 𝟙 _) (w := by simp) ≅ 𝟭 (F.DescentData f) :=
  NatIso.ofComponents (fun D => isoMk (fun i => (Cat.Hom.toNatIso (F.mapId _)).app _) (by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    dsimp
    rw [pullFunctorObjHom_eq_assoc _ _ _ _ _ q f₁ f₂ rfl]
    simp [mapComp'_id_comp_inv_app_assoc, mapComp'_id_comp_hom_app, ← Functor.map_comp]))

set_option backward.isDefEq.respectTransparency.types false in
/-- The composition of two functors `pullFunctor` is isomorphic to `pullFunctor` applied
to the compositions. -/
@[simps!]
/--
Definition of `pullFunctorCompIso` / `pullFunctorCompIso` 的定义

English:
definition pullFunctorCompIso
  body: NatIso.ofComponents
    (fun D => isoMk (fun _ => (Cat.Hom.toNatIso (F.mapComp' _ _ _ (by grind))).symm.app _) (by
      intro Y s k₁ k₂ f₁ f₂ hf₁ hf₂
      dsimp
      rw [pullFunctorObjHom_eq _ _ _ _ _ (s ≫ r) _ _ rfl]; rw [pullFunctorObjHom_eq _ _ _ _ _ (s ≫ q) (f₁ ≫ q' k₁) (f₂ ≫ q' k₂)]
      ds

中文:
定义 pullFunctorCompIso
  定义体: NatIso.ofComponents
    (fun D => isoMk (fun _ => (Cat.Hom.toNatIso (F.mapComp' _ _ _ (by grind))).symm.app _) (by
      intro Y s k₁ k₂ f₁ f₂ hf₁ hf₂
      dsimp
      rw [pullFunctorObjHom_eq _ _ _ _ _ (s ≫ r) _ _ rfl]; rw [pullFunctorObjHom_eq _ _ _ _ _ (s ≫ q) (f₁ ≫ q' k₁) (f₂ ≫ q' k₂)]
      ds

Depends on / 依赖: Cat.Hom.toNatIso, Category, Category.assoc, F.mapComp, NatIso, NatIso.ofComponents, cat_disch, mapComp, ofComponents, pullFunctor, pullFunctorObjHom_eq, reassoc_of, symm.app, toNatIso
-/
def pullFunctorCompIso
    {S'' : C} {q : S'' ⟶ S'} {ι'' : Type t''} {X'' : ι'' -> C} {f'' : forall k, X'' k ⟶ S''}
    {β : ι'' -> ι'} {q' : forall k, X'' k ⟶ X' (β k)} (w' : forall k, q' k ≫ f' (β k) = f'' k ≫ q)
    (r : S'' ⟶ S) {r' : forall k, X'' k ⟶ X (α (β k))}
    (hr : q ≫ p = r := by cat_disch) (hr' : forall k, q' k ≫ p' (β k) = r' k := by cat_disch) :
    pullFunctor F w ⋙ pullFunctor F w' ≅
      pullFunctor F (p := r) (α := α ∘ β) (p' := r') (fun k => by
        dsimp
        rw [← hr']; rw [Category.assoc]; rw [w]; rw [reassoc_of% w']; rw [hr]) :=
  NatIso.ofComponents
    (fun D => isoMk (fun _ => (Cat.Hom.toNatIso (F.mapComp' _ _ _ (by grind))).symm.app _) (by
      intro Y s k₁ k₂ f₁ f₂ hf₁ hf₂
      dsimp
      rw [pullFunctorObjHom_eq _ _ _ _ _ (s ≫ r) _ _ rfl]; rw [pullFunctorObjHom_eq _ _ _ _ _ (s ≫ q) (f₁ ≫ q' k₁) (f₂ ≫ q' k₂)]
      dsimp
      rw [pullFunctorObjHom_eq _ _ _ _ _ (s ≫ r) (f₁ ≫ r' k₁) (f₂ ≫ r' k₂)
        rfl (by simp [w']; rw [reassoc_of% hf₁]; rw [reassoc_of% hf₂]) (by
          simp [reassoc_of% w', reassoc_of% hf₁, hr])]
      dsimp
      simp only [Category.assoc]
      rw [mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc _ _ _ _ _ _ _
        (by grind) rfl rfl]; rw [mapComp'₀₂₃_hom_app _ _ _ _ _ _ _ _ rfl rfl]))

end

set_option backward.isDefEq.respectTransparency false in
variable {f} in
/-- Up to an equivalence, the category `DescentData` for a pseudofunctor `F` and
a family of morphisms `f : X i ⟶ S` is unchanged when we replace `S` by an isomorphic object,
or when we replace `f` by another family which generate the same sieve. -/
@[simps]
/--
Definition of `pullFunctorEquivalence` / `pullFunctorEquivalence` 的定义

English:
definition pullFunctorEquivalence
  signature: {S' : C} {ι' : Type t'} {X' : ι' -> C} {f' : forall j, X' j ⟶ S'}
  body: pullFunctor F w
  inverse := pullFunctor F w'
  unitIso :=
    (pullFunctorIdIso F S).symm ≪≫ pullFunctorIso _ _ _ ≪≫
      (pullFunctorCompIso _ _ _ _ e.inv_hom_id (fun _ => rfl)).symm
  counitIso :=
    pullFunctorCompIso _ _ _ _ e.hom_inv_id (fun _ => rfl) ≪≫
      pullFunctorIso _ _ _ ≪≫ pullFun

中文:
定义 pullFunctorEquivalence
  签名: {S' : C} {ι' : Type t'} {X' : ι' -> C} {f' : 对任意 j, X' j ⟶ S'}
  定义体: pullFunctor F w
  inverse := pullFunctor F w'
  unitIso :=
    (pullFunctorIdIso F S).symm ≪≫ pullFunctorIso _ _ _ ≪≫
      (pullFunctorCompIso _ _ _ _ e.inv_hom_id (fun _ => rfl)).symm
  counitIso :=
    pullFunctorCompIso _ _ _ _ e.hom_inv_id (fun _ => rfl) ≪≫
      pullFunctorIso _ _ _ ≪≫ pullFun

Depends on / 依赖: pullFunctor
-/
def pullFunctorEquivalence {S' : C} {ι' : Type t'} {X' : ι' -> C} {f' : forall j, X' j ⟶ S'}
    (e : S' ≅ S) {α : ι' -> ι} {p' : forall j, X' j ⟶ X (α j)}
    (w : forall j, p' j ≫ f (α j) = f' j ≫ e.hom)
    {β : ι -> ι'} {q' : forall i, X i ⟶ X' (β i)} (w' : forall i, q' i ≫ f' (β i) = f i ≫ e.inv) :
    F.DescentData f ≌ F.DescentData f' where
  functor := pullFunctor F w
  inverse := pullFunctor F w'
  unitIso :=
    (pullFunctorIdIso F S).symm ≪≫ pullFunctorIso _ _ _ ≪≫
      (pullFunctorCompIso _ _ _ _ e.inv_hom_id (fun _ => rfl)).symm
  counitIso :=
    pullFunctorCompIso _ _ _ _ e.hom_inv_id (fun _ => rfl) ≪≫
      pullFunctorIso _ _ _ ≪≫ pullFunctorIdIso F S'
  functor_unitIso_comp D := by
    ext j
    dsimp
    simp only [Category.id_comp, Functor.map_comp, Category.assoc]
    rw [pullFunctorObjHom_eq_assoc _ _ _ _ _ (p' _ ≫ f _) (p' _ ≫ q' _ ≫ p' _) (p' _) (by simp)
        (by simp [w']; rw [reassoc_of% w]),
      map_eq_pullHom_assoc _ (p' j) (p' j) (p' _ ≫ q' _ ≫ p' _) (by simp) (by simp),
      D.pullHom_hom _ _ (p' j ≫ f _) (by simp) _ _ (by simp)
        (by simp [w, reassoc_of% w']) _ _ (by simp) rfl]
    dsimp
    rw [← F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app_assoc _ _ _ _ _ _ rfl rfl (by simp)]; rw [mapComp'_comp_id_hom_app]; rw [mapComp'_id_comp_inv_app_assoc]; rw [← Functor.map_comp_assoc]; rw [Cat.Hom.inv_hom_id_toNatTrans_app]
    simp [D.hom_self _ _ rfl]

/--
lemma `exists_equivalence_of_sieve_eq` / 引理 `exists_equivalence_of_sieve_eq`

English:
lemma exists_equivalence_of_sieve_eq
  proof: by
  have h₁ (i' : ι') : exists (i : ι) (g' : X' i' ⟶ X i), g' ≫ f i = f' i' := by
    obtain ⟨_, _, _, ⟨i⟩, fac⟩ : Sieve.ofArrows X f (f' i') := by
      rw [h]; apply Sieve.ofArrows_mk
    exact ⟨i, _, fac⟩
  have h₂ (i : ι) : exists (i' : ι') (g : X i ⟶ X' i'), g ≫ f' i' = f i := by
    obtain ⟨_

中文:
引理 exists_equivalence_of_sieve_eq
  证明: by
  have h₁ (i' : ι') : exists (i : ι) (g' : X' i' ⟶ X i), g' ≫ f i = f' i' := by
    obtain ⟨_, _, _, ⟨i⟩, fac⟩ : Sieve.ofArrows X f (f' i') := by
      rw [h]; apply Sieve.ofArrows_mk
    exact ⟨i, _, fac⟩
  have h₂ (i : ι) : exists (i' : ι') (g : X i ⟶ X' i'), g ≫ f' i' = f i := by
    obtain ⟨_

Depends on / 依赖: Iso.refl, Sieve.ofArrows, Sieve.ofArrows_mk, ofArrows, ofArrows_mk, pullFunctorEquivalence
-/
lemma exists_equivalence_of_sieve_eq
    {ι' : Type t'} {X' : ι' -> C} (f' : forall i', X' i' ⟶ S)
    (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') :
    exists (e : F.DescentData f ≌ F.DescentData f'),
      Nonempty (F.toDescentData f ⋙ e.functor ≅ F.toDescentData f') := by
  have h₁ (i' : ι') : exists (i : ι) (g' : X' i' ⟶ X i), g' ≫ f i = f' i' := by
    obtain ⟨_, _, _, ⟨i⟩, fac⟩ : Sieve.ofArrows X f (f' i') := by
      rw [h]; apply Sieve.ofArrows_mk
    exact ⟨i, _, fac⟩
  have h₂ (i : ι) : exists (i' : ι') (g : X i ⟶ X' i'), g ≫ f' i' = f i := by
    obtain ⟨_, _, _, ⟨i'⟩, fac⟩ : Sieve.ofArrows X' f' (f i) := by
      rw [← h]; apply Sieve.ofArrows_mk
    exact ⟨i', _, fac⟩
  choose α p' w using h₁
  choose β q' w' using h₂
  exact ⟨pullFunctorEquivalence (p' := p') (q' := q') F (Iso.refl _)
    (by cat_disch) (by cat_disch), ⟨toDescentDataCompPullFunctorIso _ _ ≪≫
    Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId _)) _ ≪≫ Functor.leftUnitor _⟩⟩

/--
lemma `nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq` / 引理 `nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq`

English:
lemma nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq
  proof: by
  obtain ⟨e, ⟨iso⟩⟩ := DescentData.exists_equivalence_of_sieve_eq F f f' h
  exact ⟨fun ⟨h⟩ => ⟨(h.comp e.fullyFaithfulFunctor).ofIso iso⟩,
    fun ⟨h⟩ => ⟨(h.comp e.fullyFaithfulInverse).ofIso iso.symm.compInverseIso⟩⟩

中文:
引理 nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq
  证明: by
  obtain ⟨e, ⟨iso⟩⟩ := DescentData.exists_equivalence_of_sieve_eq F f f' h
  exact ⟨fun ⟨h⟩ => ⟨(h.comp e.fullyFaithfulFunctor).ofIso iso⟩,
    fun ⟨h⟩ => ⟨(h.comp e.fullyFaithfulInverse).ofIso iso.symm.compInverseIso⟩⟩

Depends on / 依赖: DescentData, DescentData.exists_equivalence_of_sieve_eq, compInverseIso, e.fullyFaithfulFunctor, e.fullyFaithfulInverse, exists_equivalence_of_sieve_eq, fullyFaithfulFunctor, fullyFaithfulInverse, h.comp, iso.symm.compInverseIso
-/
lemma nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq
    {ι : Type t} {S : C} {X : ι -> C} (f : forall i, X i ⟶ S)
    {ι' : Type t'} {X' : ι' -> C} (f' : forall i', X' i' ⟶ S)
    (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') :
    Nonempty (F.toDescentData f).FullyFaithful ↔
      Nonempty (F.toDescentData f').FullyFaithful := by
  obtain ⟨e, ⟨iso⟩⟩ := DescentData.exists_equivalence_of_sieve_eq F f f' h
  exact ⟨fun ⟨h⟩ => ⟨(h.comp e.fullyFaithfulFunctor).ofIso iso⟩,
    fun ⟨h⟩ => ⟨(h.comp e.fullyFaithfulInverse).ofIso iso.symm.compInverseIso⟩⟩

/--
lemma `isEquivalence_toDescentData_iff_of_sieve_eq` / 引理 `isEquivalence_toDescentData_iff_of_sieve_eq`

English:
lemma isEquivalence_toDescentData_iff_of_sieve_eq
  proof: by
  obtain ⟨e, ⟨iso⟩⟩ := DescentData.exists_equivalence_of_sieve_eq F f f' h
  rw [← Functor.isEquivalence_iff_of_iso iso]
  exact ⟨fun _ => inferInstance,
    fun _ => Functor.isEquivalence_of_comp_right _ e.functor⟩

中文:
引理 isEquivalence_toDescentData_iff_of_sieve_eq
  证明: by
  obtain ⟨e, ⟨iso⟩⟩ := DescentData.exists_equivalence_of_sieve_eq F f f' h
  rw [← Functor.isEquivalence_iff_of_iso iso]
  exact ⟨fun _ => inferInstance,
    fun _ => Functor.isEquivalence_of_comp_right _ e.functor⟩

Depends on / 依赖: DescentData, DescentData.exists_equivalence_of_sieve_eq, Functor, Functor.isEquivalence_iff_of_iso, Functor.isEquivalence_of_comp_right, e.functor, exists_equivalence_of_sieve_eq, functor, isEquivalence_iff_of_iso, isEquivalence_of_comp_right
-/
lemma isEquivalence_toDescentData_iff_of_sieve_eq
    {ι : Type t} {S : C} {X : ι -> C} (f : forall i, X i ⟶ S)
    {ι' : Type t'} {X' : ι' -> C} (f' : forall i', X' i' ⟶ S)
    (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') :
    (F.toDescentData f).IsEquivalence ↔ (F.toDescentData f').IsEquivalence := by
  obtain ⟨e, ⟨iso⟩⟩ := DescentData.exists_equivalence_of_sieve_eq F f f' h
  rw [← Functor.isEquivalence_iff_of_iso iso]
  exact ⟨fun _ => inferInstance,
    fun _ => Functor.isEquivalence_of_comp_right _ e.functor⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `subtypeCompatibleHomEquiv` / `subtypeCompatibleHomEquiv` 的定义

English:
definition subtypeCompatibleHomEquiv
  signature: {M N : F.obj (.mk (op S))}
  body: { hom := φ.val
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        have := φ.property i₁ i₂ (Over.mk q) (Over.homMk f₁) (Over.homMk f₂) (by cat_disch)
        simp_all [map_eq_pullHom] }
  invFun g :=
    { val := g.hom
      property i₁ i₂ Z f₁ f₂ h := by
        simpa [map_eq_pullHom (g.hom i₁) f₁.le

中文:
定义 subtypeCompatibleHomEquiv
  签名: {M N : F.obj (.mk (op S))}
  定义体: { hom := φ.val
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        have := φ.property i₁ i₂ (Over.mk q) (Over.homMk f₁) (Over.homMk f₂) (by cat_disch)
        simp_all [map_eq_pullHom] }
  invFun g :=
    { val := g.hom
      property i₁ i₂ Z f₁ f₂ h := by
        simpa [map_eq_pullHom (g.hom i₁) f₁.le

Depends on / 依赖: Over.homMk, Over.mk
-/
def subtypeCompatibleHomEquiv {M N : F.obj (.mk (op S))} :
    Subtype (Presieve.Arrows.Compatible (F.presheafHom M N)
      (X := fun i => Over.mk (f i)) (B := Over.mk (𝟙 S)) (fun i => Over.homMk (f i))) ≃
    ((F.toDescentData f).obj M ⟶ (F.toDescentData f).obj N) where
  toFun φ :=
    { hom := φ.val
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        have := φ.property i₁ i₂ (Over.mk q) (Over.homMk f₁) (Over.homMk f₂) (by cat_disch)
        simp_all [map_eq_pullHom] }
  invFun g :=
    { val := g.hom
      property i₁ i₂ Z f₁ f₂ h := by
        simpa [map_eq_pullHom (g.hom i₁) f₁.left Z.hom Z.hom (Over.w f₁) (Over.w f₁),
          map_eq_pullHom (g.hom i₂) f₂.left Z.hom Z.hom (Over.w f₂) (Over.w f₂),
          cancel_epi, cancel_mono] using g.comm Z.hom f₁.left f₂.left (Over.w f₁) (Over.w f₂) }

set_option backward.isDefEq.respectTransparency false in
/--
lemma `subtypeCompatibleHomEquiv_toCompatible_presheafHomObjHomEquiv` / 引理 `subtypeCompatibleHomEquiv_toCompatible_presheafHomObjHomEquiv`

English:
lemma subtypeCompatibleHomEquiv_toCompatible_presheafHomObjHomEquiv
  proof: by
  ext i
  simp [subtypeCompatibleHomEquiv, presheafHomObjHomEquiv, pullHom,
    ← Functor.map_comp, Pseudofunctor.mapComp'_id_comp_hom_app_assoc,
    Pseudofunctor.mapComp'_id_comp_inv_app]

中文:
引理 subtypeCompatibleHomEquiv_toCompatible_presheafHomObjHomEquiv
  证明: by
  ext i
  simp [subtypeCompatibleHomEquiv, presheafHomObjHomEquiv, pullHom,
    ← Functor.map_comp, Pseudofunctor.mapComp'_id_comp_hom_app_assoc,
    Pseudofunctor.mapComp'_id_comp_inv_app]

Depends on / 依赖: Functor, Functor.map_comp, Pseudofunctor, Pseudofunctor.mapComp, _id_comp_hom_app_assoc, _id_comp_inv_app, mapComp, map_comp, presheafHomObjHomEquiv, pullHom, subtypeCompatibleHomEquiv
-/
lemma subtypeCompatibleHomEquiv_toCompatible_presheafHomObjHomEquiv
    {M N : F.obj (.mk (op S))} (φ : M ⟶ N) :
    subtypeCompatibleHomEquiv F f (Presieve.Arrows.toCompatible _ _
      (F.presheafHomObjHomEquiv φ)) = (F.toDescentData f).map φ := by
  ext i
  simp [subtypeCompatibleHomEquiv, presheafHomObjHomEquiv, pullHom,
    ← Functor.map_comp, Pseudofunctor.mapComp'_id_comp_hom_app_assoc,
    Pseudofunctor.mapComp'_id_comp_inv_app]

end DescentData

/-- The condition that a pseudofunctor satisfies the descent of morphisms
relative to a presieve. -/
@[mk_iff]
/--
Definition of `IsPrestackFor` / `IsPrestackFor` 的定义

English:
structure IsPrestackFor
  parameters: (R : Presieve S)
  axioms and operations (1):
    - nonempty_fullyFaithful : Nonempty (F.toDescentData (fun (f : R.category) => f.obj.hom)).FullyFaithful

中文:
结构 IsPrestackFor
  参数: (R : Presieve S)
  公理与运算 (1 个):
    - nonempty_fullyFaithful : Nonempty (F.toDescentData (fun (f : R.category) => f.obj.hom)).FullyFaithful
-/
structure IsPrestackFor (R : Presieve S) : Prop where
  nonempty_fullyFaithful :
    Nonempty (F.toDescentData (fun (f : R.category) => f.obj.hom)).FullyFaithful

variable {F} in
/--
Definition of `IsPrestackFor.fullyFaithful` / `IsPrestackFor.fullyFaithful` 的定义

English:
definition IsPrestackFor.fullyFaithful
  signature: {R : Presieve S} (hF : F.IsPrestackFor R)
  body: hF.nonempty_fullyFaithful.some

中文:
定义 IsPrestackFor.fullyFaithful
  签名: {R : Presieve S} (hF : F.IsPrestackFor R)
  定义体: hF.nonempty_fullyFaithful.some

Depends on / 依赖: hF.nonempty_fullyFaithful.some, nonempty_fullyFaithful
-/
noncomputable def IsPrestackFor.fullyFaithful {R : Presieve S} (hF : F.IsPrestackFor R) :
    (F.toDescentData (fun (f : R.category) => f.obj.hom)).FullyFaithful :=
  hF.nonempty_fullyFaithful.some

/--
lemma `isPrestackFor_iff_of_sieve_eq` / 引理 `isPrestackFor_iff_of_sieve_eq`

English:
lemma isPrestackFor_iff_of_sieve_eq
  proof: by
  simp only [isPrestackFor_iff]
  obtain ⟨_, _, f, rfl⟩ := Presieve.exists_eq_ofArrows R
  obtain ⟨_, _, f', rfl⟩ := Presieve.exists_eq_ofArrows R'
  apply DescentData.nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq
  simpa only [Sieve.ofArrows_category']

@[simp]

中文:
引理 isPrestackFor_iff_of_sieve_eq
  证明: by
  simp only [isPrestackFor_iff]
  obtain ⟨_, _, f, rfl⟩ := Presieve.exists_eq_ofArrows R
  obtain ⟨_, _, f', rfl⟩ := Presieve.exists_eq_ofArrows R'
  apply DescentData.nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq
  simpa only [Sieve.ofArrows_category']

@[simp]

Depends on / 依赖: DescentData, DescentData.nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq, Presieve, Presieve.exists_eq_ofArrows, Sieve.ofArrows_category, exists_eq_ofArrows, isPrestackFor_iff, nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq, ofArrows_category
-/
lemma isPrestackFor_iff_of_sieve_eq
    {R R' : Presieve S} (h : Sieve.generate R = Sieve.generate R') :
    F.IsPrestackFor R ↔ F.IsPrestackFor R' := by
  simp only [isPrestackFor_iff]
  obtain ⟨_, _, f, rfl⟩ := Presieve.exists_eq_ofArrows R
  obtain ⟨_, _, f', rfl⟩ := Presieve.exists_eq_ofArrows R'
  apply DescentData.nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq
  simpa only [Sieve.ofArrows_category']

@[simp]
/--
lemma `IsPrestackFor_generate_iff` / 引理 `IsPrestackFor_generate_iff`

English:
lemma IsPrestackFor_generate_iff
  given: (R : Presieve S)
  proof: F.isPrestackFor_iff_of_sieve_eq (by simp)

中文:
引理 IsPrestackFor_generate_iff
  条件: (R : Presieve S)
  证明: F.isPrestackFor_iff_of_sieve_eq (by simp)

Depends on / 依赖: F.isPrestackFor_iff_of_sieve_eq, isPrestackFor_iff_of_sieve_eq
-/
lemma IsPrestackFor_generate_iff (R : Presieve S) :
    F.IsPrestackFor (Sieve.generate R).arrows ↔ F.IsPrestackFor R :=
  F.isPrestackFor_iff_of_sieve_eq (by simp)

/--
lemma `isPrestackFor_ofArrows_iff` / 引理 `isPrestackFor_ofArrows_iff`

English:
lemma isPrestackFor_ofArrows_iff
  proof: by
  simp only [isPrestackFor_iff]
  apply DescentData.nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq
  rw [Sieve.ofArrows_category']

中文:
引理 isPrestackFor_ofArrows_iff
  证明: by
  simp only [isPrestackFor_iff]
  apply DescentData.nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq
  rw [Sieve.ofArrows_category']

Depends on / 依赖: DescentData, DescentData.nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq, Sieve.ofArrows_category, isPrestackFor_iff, nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq, ofArrows_category
-/
lemma isPrestackFor_ofArrows_iff :
    F.IsPrestackFor (Presieve.ofArrows _ f) ↔
      Nonempty (F.toDescentData f).FullyFaithful := by
  simp only [isPrestackFor_iff]
  apply DescentData.nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq
  rw [Sieve.ofArrows_category']

/-- The condition that a pseudofunctor has effective descent
relative to a presieve. -/
@[mk_iff]
/--
Definition of `IsStackFor` / `IsStackFor` 的定义

English:
structure IsStackFor
  parameters: (R : Presieve S)
  axioms and operations (1):
    - isEquivalence : (F.toDescentData (fun (f : R.category) => f.obj.hom)).IsEquivalence

中文:
结构 IsStackFor
  参数: (R : Presieve S)
  公理与运算 (1 个):
    - isEquivalence : (F.toDescentData (fun (f : R.category) => f.obj.hom)).IsEquivalence
-/
structure IsStackFor (R : Presieve S) : Prop where
  isEquivalence :
    (F.toDescentData (fun (f : R.category) => f.obj.hom)).IsEquivalence

variable {F} in
/--
lemma `IsStackFor.isPrestackFor` / 引理 `IsStackFor.isPrestackFor`

English:
lemma IsStackFor.isPrestackFor
  given: {R : Presieve S} (h : F.IsStackFor R)
  proof: ⟨by
    rw [isStackFor_iff] at h
    exact .ofFullyFaithful _⟩

中文:
引理 IsStackFor.isPrestackFor
  条件: {R : Presieve S} (h : F.IsStackFor R)
  证明: ⟨by
    rw [isStackFor_iff] at h
    exact .ofFullyFaithful _⟩

Depends on / 依赖: isStackFor_iff, ofFullyFaithful
-/
lemma IsStackFor.isPrestackFor {R : Presieve S} (h : F.IsStackFor R) :
    F.IsPrestackFor R where
  nonempty_fullyFaithful := ⟨by
    rw [isStackFor_iff] at h
    exact .ofFullyFaithful _⟩

variable {F} in
/--
lemma `IsStackFor.essSurj` / 引理 `IsStackFor.essSurj`

English:
lemma IsStackFor.essSurj
  given: {R : Presieve S} (h : F.IsStackFor R)
  proof: by
  have := h.isEquivalence
  infer_instance

中文:
引理 IsStackFor.essSurj
  条件: {R : Presieve S} (h : F.IsStackFor R)
  证明: by
  have := h.isEquivalence
  infer_instance

Depends on / 依赖: h.isEquivalence, infer_instance, isEquivalence
-/
lemma IsStackFor.essSurj {R : Presieve S} (h : F.IsStackFor R) :
    (F.toDescentData (fun (f : R.category) => f.obj.hom)).EssSurj := by
  have := h.isEquivalence
  infer_instance

/--
lemma `isStackFor_iff_of_sieve_eq` / 引理 `isStackFor_iff_of_sieve_eq`

English:
lemma isStackFor_iff_of_sieve_eq
  proof: by
  simp only [isStackFor_iff]
  obtain ⟨_, _, f, rfl⟩ := Presieve.exists_eq_ofArrows R
  obtain ⟨_, _, f', rfl⟩ := Presieve.exists_eq_ofArrows R'
  apply DescentData.isEquivalence_toDescentData_iff_of_sieve_eq
  simpa only [Sieve.ofArrows_category']

@[simp]

中文:
引理 isStackFor_iff_of_sieve_eq
  证明: by
  simp only [isStackFor_iff]
  obtain ⟨_, _, f, rfl⟩ := Presieve.exists_eq_ofArrows R
  obtain ⟨_, _, f', rfl⟩ := Presieve.exists_eq_ofArrows R'
  apply DescentData.isEquivalence_toDescentData_iff_of_sieve_eq
  simpa only [Sieve.ofArrows_category']

@[simp]

Depends on / 依赖: DescentData, DescentData.isEquivalence_toDescentData_iff_of_sieve_eq, Presieve, Presieve.exists_eq_ofArrows, Sieve.ofArrows_category, exists_eq_ofArrows, isEquivalence_toDescentData_iff_of_sieve_eq, isStackFor_iff, ofArrows_category
-/
lemma isStackFor_iff_of_sieve_eq
    {R R' : Presieve S} (h : Sieve.generate R = Sieve.generate R') :
    F.IsStackFor R ↔ F.IsStackFor R' := by
  simp only [isStackFor_iff]
  obtain ⟨_, _, f, rfl⟩ := Presieve.exists_eq_ofArrows R
  obtain ⟨_, _, f', rfl⟩ := Presieve.exists_eq_ofArrows R'
  apply DescentData.isEquivalence_toDescentData_iff_of_sieve_eq
  simpa only [Sieve.ofArrows_category']

@[simp]
/--
lemma `IsStackFor_generate_iff` / 引理 `IsStackFor_generate_iff`

English:
lemma IsStackFor_generate_iff
  given: (R : Presieve S)
  proof: F.isStackFor_iff_of_sieve_eq (by simp)

中文:
引理 IsStackFor_generate_iff
  条件: (R : Presieve S)
  证明: F.isStackFor_iff_of_sieve_eq (by simp)

Depends on / 依赖: F.isStackFor_iff_of_sieve_eq, isStackFor_iff_of_sieve_eq
-/
lemma IsStackFor_generate_iff (R : Presieve S) :
    F.IsStackFor (Sieve.generate R).arrows ↔ F.IsStackFor R :=
  F.isStackFor_iff_of_sieve_eq (by simp)

/--
lemma `isStackFor_ofArrows_iff` / 引理 `isStackFor_ofArrows_iff`

English:
lemma isStackFor_ofArrows_iff
  proof: by
  simp only [isStackFor_iff]
  apply DescentData.isEquivalence_toDescentData_iff_of_sieve_eq
  rw [Sieve.ofArrows_category']

中文:
引理 isStackFor_ofArrows_iff
  证明: by
  simp only [isStackFor_iff]
  apply DescentData.isEquivalence_toDescentData_iff_of_sieve_eq
  rw [Sieve.ofArrows_category']

Depends on / 依赖: DescentData, DescentData.isEquivalence_toDescentData_iff_of_sieve_eq, Sieve.ofArrows_category, isEquivalence_toDescentData_iff_of_sieve_eq, isStackFor_iff, ofArrows_category
-/
lemma isStackFor_ofArrows_iff :
    F.IsStackFor (Presieve.ofArrows _ f) ↔
      (F.toDescentData f).IsEquivalence := by
  simp only [isStackFor_iff]
  apply DescentData.isEquivalence_toDescentData_iff_of_sieve_eq
  rw [Sieve.ofArrows_category']

variable {F} in
/--
lemma `bijective_toDescentData_map_iff` / 引理 `bijective_toDescentData_map_iff`

English:
lemma bijective_toDescentData_map_iff
  given: (M N : F.obj (.mk (op S)))
  proof: by
  rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible]; rw [← (DescentData.subtypeCompatibleHomEquiv F f).bijective.of_comp_iff']; rw [← Function.Bijective.of_comp_iff _ (presheafHomObjHomEquiv F).bijective]
  convert! Iff.rfl
  ext φ : 1
  apply DescentData.subtypeCompatibleHomEquiv_toCo

中文:
引理 bijective_toDescentData_map_iff
  条件: (M N : F.obj (.mk (op S)))
  证明: by
  rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible]; rw [← (DescentData.subtypeCompatibleHomEquiv F f).bijective.of_comp_iff']; rw [← Function.Bijective.of_comp_iff _ (presheafHomObjHomEquiv F).bijective]
  convert! Iff.rfl
  ext φ : 1
  apply DescentData.subtypeCompatibleHomEquiv_toCo

Depends on / 依赖: Over.mk
-/
lemma bijective_toDescentData_map_iff (M N : F.obj (.mk (op S))) :
    Function.Bijective ((F.toDescentData f).map : (M ⟶ N) -> _) ↔
  Presieve.IsSheafFor (F.presheafHom M N) (X := Over.mk (𝟙 S))
    (Presieve.ofArrows (Y := fun i => Over.mk (f i)) (fun i => Over.homMk (f i))) := by
  rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible]; rw [← (DescentData.subtypeCompatibleHomEquiv F f).bijective.of_comp_iff']; rw [← Function.Bijective.of_comp_iff _ (presheafHomObjHomEquiv F).bijective]
  convert! Iff.rfl
  ext φ : 1
  apply DescentData.subtypeCompatibleHomEquiv_toCompatible_presheafHomObjHomEquiv

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isPrestackFor_iff_isSheafFor` / 引理 `isPrestackFor_iff_isSheafFor`

English:
lemma isPrestackFor_iff_isSheafFor
  given: {S : C} (R : Sieve S)
  proof: by
  rw [isPrestackFor_iff]; rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
  refine forall_congr' (fun M => forall_congr' (fun N => ?_))
  rw [bijective_toDescentData_map_iff]
  convert! Iff.rfl
  refine le_antisymm ?_ ?_
  · rintro X f (hf : R.arrows f.left)
    obtain ⟨X, g, rfl⟩ := Over.m

中文:
引理 isPrestackFor_iff_isSheafFor
  条件: {S : C} (R : Sieve S)
  证明: by
  rw [isPrestackFor_iff]; rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
  refine forall_congr' (fun M => forall_congr' (fun N => ?_))
  rw [bijective_toDescentData_map_iff]
  convert! Iff.rfl
  refine le_antisymm ?_ ?_
  · rintro X f (hf : R.arrows f.left)
    obtain ⟨X, g, rfl⟩ := Over.m

Depends on / 依赖: F.presheafHom, presheafHom
-/
lemma isPrestackFor_iff_isSheafFor {S : C} (R : Sieve S) :
    F.IsPrestackFor R.arrows ↔ forall (M N : F.obj (.mk (op S))),
      Presieve.IsSheafFor (P := F.presheafHom M N)
        ((Sieve.overEquiv (Over.mk (𝟙 S))).symm R).arrows := by
  rw [isPrestackFor_iff]; rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
  refine forall_congr' (fun M => forall_congr' (fun N => ?_))
  rw [bijective_toDescentData_map_iff]
  convert! Iff.rfl
  refine le_antisymm ?_ ?_
  · rintro X f (hf : R.arrows f.left)
    obtain ⟨X, g, rfl⟩ := Over.mk_surjective X
    obtain rfl : f = Over.homMk g := by ext; simpa using Over.w f
    exact Presieve.ofArrows.mk (ι := R.arrows.category) ⟨Over.mk g, hf⟩
  · rintro _ _ ⟨_, h⟩
    exact h

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isPrestackFor_iff_isSheafFor'` / 引理 `isPrestackFor_iff_isSheafFor'`

English:
lemma isPrestackFor_iff_isSheafFor'
  given: {S : C} (R : Sieve S)
  proof: by
  rw [isPrestackFor_iff_isSheafFor]
  refine ⟨fun h S₀ M N a => ?_, by tauto⟩
  replace h := h ((F.map a.op.toLoc).toFunctor.obj M) ((F.map a.op.toLoc).toFunctor.obj N)
  rw [← Presieve.isSheafFor_iff_of_iso (F.overMapCompPresheafHomIso M N a)]; rw [Presieve.isSheafFor_over_map_op_comp_iff (X' :=

中文:
引理 isPrestackFor_iff_isSheafFor'
  条件: {S : C} (R : Sieve S)
  证明: by
  rw [isPrestackFor_iff_isSheafFor]
  refine ⟨fun h S₀ M N a => ?_, by tauto⟩
  replace h := h ((F.map a.op.toLoc).toFunctor.obj M) ((F.map a.op.toLoc).toFunctor.obj N)
  rw [← Presieve.isSheafFor_iff_of_iso (F.overMapCompPresheafHomIso M N a)]; rw [Presieve.isSheafFor_over_map_op_comp_iff (X' :=

Depends on / 依赖: F.map, F.overMapCompPresheafHomIso, Iso.refl, Over.homMk, Over.isoMk, Over.mk, Over.w, Presieve, Presieve.isSheafFor_iff_of_iso, Presieve.isSheafFor_over_map_op_comp_iff, a.op.toLoc, cat_disch, convert, f.left, isPrestackFor_iff_isSheafFor, isSheafFor_iff_of_iso, isSheafFor_over_map_op_comp_iff, le_antisymm, overMapCompPresheafHomIso, replace
-/
lemma isPrestackFor_iff_isSheafFor' {S : C} (R : Sieve S) :
    F.IsPrestackFor R.arrows ↔ forall ⦃S₀ : C⦄ (M N : F.obj (.mk (op S₀))) (a : S ⟶ S₀),
      Presieve.IsSheafFor (F.presheafHom M N) ((Sieve.overEquiv (Over.mk a)).symm R).arrows := by
  rw [isPrestackFor_iff_isSheafFor]
  refine ⟨fun h S₀ M N a => ?_, by tauto⟩
  replace h := h ((F.map a.op.toLoc).toFunctor.obj M) ((F.map a.op.toLoc).toFunctor.obj N)
  rw [← Presieve.isSheafFor_iff_of_iso (F.overMapCompPresheafHomIso M N a)]; rw [Presieve.isSheafFor_over_map_op_comp_iff (X' := Over.mk a)
      (e := Over.isoMk (Iso.refl _))] at h
  convert! h
  refine le_antisymm ?_ ?_
  · intro Y f hf
    exact ⟨Over.mk f.left, Over.homMk f.left, Over.homMk (𝟙 _) (by simpa using Over.w f),
      hf, by cat_disch⟩
  · rintro X b ⟨Y, c, d, h, fac⟩
    replace fac := (Over.forget _).congr_map fac
    dsimp at fac
    rw [Category.comp_id] at fac
    change R.arrows b.left
    simpa [fac] using R.downward_closed h d.left

set_option backward.isDefEq.respectTransparency false in
variable {F} in
/--
lemma `IsPrestackFor.isSheafFor'` / 引理 `IsPrestackFor.isSheafFor'`

English:
lemma IsPrestackFor.isSheafFor'
  proof: by
  rw [isPrestackFor_iff_isSheafFor'] at hF
  obtain ⟨S, a, rfl⟩ := S.mk_surjective
  simpa using hF M N a

中文:
引理 IsPrestackFor.isSheafFor'
  证明: by
  rw [isPrestackFor_iff_isSheafFor'] at hF
  obtain ⟨S, a, rfl⟩ := S.mk_surjective
  simpa using hF M N a

Depends on / 依赖: S.mk_surjective, isPrestackFor_iff_isSheafFor, mk_surjective
-/
lemma IsPrestackFor.isSheafFor'
    {S₀ : C} (S : Over S₀) {R : Sieve S} (hF : F.IsPrestackFor (Sieve.overEquiv _ R).arrows)
    (M N : F.obj (.mk (op S₀))) :
    Presieve.IsSheafFor (F.presheafHom M N) R.arrows := by
  rw [isPrestackFor_iff_isSheafFor'] at hF
  obtain ⟨S, a, rfl⟩ := S.mk_surjective
  simpa using hF M N a

variable {J : GrothendieckTopology C}

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `fullyFaithfulToDescentData` / `fullyFaithfulToDescentData` 的定义

English:
definition fullyFaithfulToDescentData
  signature: [F.IsPrestack J] (hf : Sieve.ofArrows _ f in J S)
  body: Nonempty.some (by
    rw [← isPrestackFor_ofArrows_iff]; rw [← IsPrestackFor_generate_iff]; rw [isPrestackFor_iff_isSheafFor]
    intro M N
    refine ((isSheaf_iff_isSheaf_of_type _ _).1
      (IsPrestack.isSheaf J M N)).isSheafFor _ ?_
    rwa [GrothendieckTopology.mem_over_iff, Sieve.generate_sie

中文:
定义 fullyFaithfulToDescentData
  签名: [F.IsPrestack J] (hf : Sieve.ofArrows _ f in J S)
  定义体: Nonempty.some (by
    rw [← isPrestackFor_ofArrows_iff]; rw [← IsPrestackFor_generate_iff]; rw [isPrestackFor_iff_isSheafFor]
    intro M N
    refine ((isSheaf_iff_isSheaf_of_type _ _).1
      (IsPrestack.isSheaf J M N)).isSheafFor _ ?_
    rwa [GrothendieckTopology.mem_over_iff, Sieve.generate_sie

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.mem_over_iff, IsPrestack, IsPrestack.isSheaf, IsPrestackFor_generate_iff, Nonempty, Nonempty.some, OrderIso, OrderIso.apply_symm_apply, Sieve.generate_sieve, apply_symm_apply, generate_sieve, isPrestackFor_iff_isSheafFor, isPrestackFor_ofArrows_iff, isSheaf, isSheafFor, isSheaf_iff_isSheaf_of_type, mem_over_iff
-/
noncomputable def fullyFaithfulToDescentData [F.IsPrestack J] (hf : Sieve.ofArrows _ f in J S) :
    (F.toDescentData f).FullyFaithful :=
  Nonempty.some (by
    rw [← isPrestackFor_ofArrows_iff]; rw [← IsPrestackFor_generate_iff]; rw [isPrestackFor_iff_isSheafFor]
    intro M N
    refine ((isSheaf_iff_isSheaf_of_type _ _).1
      (IsPrestack.isSheaf J M N)).isSheafFor _ ?_
    rwa [GrothendieckTopology.mem_over_iff, Sieve.generate_sieve, OrderIso.apply_symm_apply])

/--
lemma `isPrestackFor` / 引理 `isPrestackFor`

English:
lemma isPrestackFor
  given: [F.IsPrestack J] {S : C} (R : Presieve S) (hR : Sieve.generate R in J S)
  proof: by
  rw [isPrestackFor_iff]
  exact ⟨F.fullyFaithfulToDescentData _ (by rwa [Sieve.ofArrows_category'])⟩

中文:
引理 isPrestackFor
  条件: [F.IsPrestack J] {S : C} (R : Presieve S) (hR : Sieve.generate R in J S)
  证明: by
  rw [isPrestackFor_iff]
  exact ⟨F.fullyFaithfulToDescentData _ (by rwa [Sieve.ofArrows_category'])⟩

Depends on / 依赖: F.fullyFaithfulToDescentData, Sieve.ofArrows_category, fullyFaithfulToDescentData, isPrestackFor_iff, ofArrows_category
-/
lemma isPrestackFor [F.IsPrestack J] {S : C} (R : Presieve S) (hR : Sieve.generate R in J S) :
    F.IsPrestackFor R := by
  rw [isPrestackFor_iff]
  exact ⟨F.fullyFaithfulToDescentData _ (by rwa [Sieve.ofArrows_category'])⟩

/--
lemma `isPrestackFor'` / 引理 `isPrestackFor'`

English:
lemma isPrestackFor'
  given: [F.IsPrestack J] {S : C} (R : Sieve S) (hR : R in J S)
  proof: F.isPrestackFor _ (by simpa)

中文:
引理 isPrestackFor'
  条件: [F.IsPrestack J] {S : C} (R : Sieve S) (hR : R in J S)
  证明: F.isPrestackFor _ (by simpa)

Depends on / 依赖: F.isPrestackFor, isPrestackFor
-/
lemma isPrestackFor' [F.IsPrestack J] {S : C} (R : Sieve S) (hR : R in J S) :
    F.IsPrestackFor R.arrows :=
  F.isPrestackFor _ (by simpa)

variable {F} in
/--
lemma `IsPrestack.of_isPrestackFor` / 引理 `IsPrestack.of_isPrestackFor`

English:
lemma IsPrestack.of_isPrestackFor
  proof: by
    rw [isSheaf_iff_isSheaf_of_type]
    intro U S hS
    obtain ⟨U, u, rfl⟩ := Over.mk_surjective U
    apply (hF _ _ hS).isSheafFor'

中文:
引理 IsPrestack.of_isPrestackFor
  证明: by
    rw [isSheaf_iff_isSheaf_of_type]
    intro U S hS
    obtain ⟨U, u, rfl⟩ := Over.mk_surjective U
    apply (hF _ _ hS).isSheafFor'

Depends on / 依赖: Over.mk_surjective, isSheafFor, isSheaf_iff_isSheaf_of_type, mk_surjective
-/
lemma IsPrestack.of_isPrestackFor
    (hF : forall (S : C) (R : Sieve S) (_ : R in J S), F.IsPrestackFor R.arrows) :
    F.IsPrestack J where
  isSheaf M N := by
    rw [isSheaf_iff_isSheaf_of_type]
    intro U S hS
    obtain ⟨U, u, rfl⟩ := Over.mk_surjective U
    apply (hF _ _ hS).isSheafFor'

end Pseudofunctor

end CategoryTheory
