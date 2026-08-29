/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# The bicategory of adjunctions in a bicategory

Given a bicategory `B`, we construct a bicategory `Adj B` that has essentially
the same objects as `B` but whose `1`-morphisms are adjunctions (in the same
direction as the left adjoints), and `2`-morphisms are tuples of mate maps
between the left and right adjoints (where the map between right
adjoints is in the opposite direction).

Certain pseudofunctors to the bicategory `Adj Cat` are analogous to bifibered categories:
in various contexts, this may be used in order to formalize the properties of
both pullback and pushforward functors.

## References

* https://ncatlab.org/nlab/show/2-category+of+adjunctions
* https://ncatlab.org/nlab/show/transformation+of+adjoints
* https://ncatlab.org/nlab/show/mate

-/

@[expose] public section

universe w v u

namespace CategoryTheory

namespace Bicategory

/--
Definition of `Adj` / `Adj` 的定义

English:
structure Adj
  parameters: (B : Type u) [Bicategory.{w, v} B]
  axioms and operations (1):
    - obj : B

中文:
结构 伴随
  参数: (B : 类型u) [双范畴.{w, v} B]
  公理与运算 (1 个):
    - obj : B
-/
structure Adj (B : Type u) [Bicategory.{w, v} B] where
  /-- If `a : Adj B`, `a.obj : B` is the underlying object of the bicategory `B`. -/
  obj : B

variable {B : Type u} [Bicategory.{w, v} B]

namespace Adj

/--
lemma `mk_obj` / 引理 `mk_obj`

English:
lemma mk_obj
  given: (b : Adj B)
  statement: mk b.obj = b
  proof: rfl

中文:
引理 mk_obj
  条件: (b : 伴随 B)
  结论: mk b.obj = b
  证明: rfl
-/
@[simp] lemma mk_obj (b : Adj B) : mk b.obj = b := rfl

section

variable (a b : B)

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: where
  axioms and operations (3):
    - {l : a ⟶ b}
    - {r : b ⟶ a}
    - adj : l ⊣ r

中文:
结构 态射
  参数: where
  公理与运算 (3 个):
    - {l : a ⟶ b}
    - {r : b ⟶ a}
    - adj : l ⊣ r
-/
structure Hom where
  /-- the left adjoint -/
  {l : a ⟶ b}
  /-- the right adjoint -/
  {r : b ⟶ a}
  /-- the adjunction -/
  adj : l ⊣ r

end

@[simps! id_l id_r id_adj comp_l comp_r comp_adj]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryStruct (Adj B)
  body: Hom a.obj b.obj
  id a := .mk (Adjunction.id a.obj)
  comp f g := .mk (f.adj.comp g.adj)

中文:
实例 :
  签名: CategoryStruct (伴随 B)
  定义体: Hom a.obj b.obj
  id a := .mk (Adjunction.id a.obj)
  comp f g := .mk (f.adj.comp g.adj)

Depends on / 依赖: a.obj, b.obj
-/
instance : CategoryStruct (Adj B) where
  Hom a b := Hom a.obj b.obj
  id a := .mk (Adjunction.id a.obj)
  comp f g := .mk (f.adj.comp g.adj)

variable {a b c d : Adj B}

/-- A morphism between two adjunctions consists of a tuple of mate maps. -/
@[ext]
/--
Definition of `Hom₂` / `Hom₂` 的定义

English:
structure Hom₂
  parameters: (α β : a ⟶ b)
  axioms and operations (3):
    - τl : α.l ⟶ β.l
    - τr : β.r ⟶ α.r
    - conjugateEquiv_τl : conjugateEquiv β.adj α.adj τl = τr  [default: by cat_disch]

中文:
结构 Hom₂
  参数: (α β : a ⟶ b)
  公理与运算 (3 个):
    - τl : α.l ⟶ β.l
    - τr : β.r ⟶ α.r
    - conjugateEquiv_τl : conjugateEquiv β.adj α.adj τl = τr  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom₂ (α β : a ⟶ b) where
  /-- the morphism between left adjoints -/
  τl : α.l ⟶ β.l
  /-- the morphism in the opposite direction between right adjoints -/
  τr : β.r ⟶ α.r
  conjugateEquiv_τl : conjugateEquiv β.adj α.adj τl = τr := by cat_disch

/--
lemma `Hom₂.conjugateEquiv_symm_τr` / 引理 `Hom₂.conjugateEquiv_symm_τr`

English:
lemma Hom₂.conjugateEquiv_symm_τr
  given: {α β : a ⟶ b} (p : Hom₂ α β)
  proof: by
  rw [← Hom₂.conjugateEquiv_τl]; rw [Equiv.symm_apply_apply]

@[simps!]

中文:
引理 Hom₂.conjugateEquiv_symm_τr
  条件: {α β : a ⟶ b} (p : Hom₂ α β)
  证明: by
  rw [← Hom₂.conjugateEquiv_τl]; rw [Equiv.symm_apply_apply]

@[simps!]

Depends on / 依赖: Equiv.symm_apply_apply, symm_apply_apply
-/
lemma Hom₂.conjugateEquiv_symm_τr {α β : a ⟶ b} (p : Hom₂ α β) :
    (conjugateEquiv β.adj α.adj).symm p.τr = p.τl := by
  rw [← Hom₂.conjugateEquiv_τl]; rw [Equiv.symm_apply_apply]

@[simps!]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryStruct (a ⟶ b)
  body: Hom₂ α β
  id α :=
    { τl := 𝟙 _
      τr := 𝟙 _ }
  comp {a b c} x y :=
    { τl := x.τl ≫ y.τl
      τr := y.τr ≫ x.τr
      conjugateEquiv_τl := by
        simp [← conjugateEquiv_comp c.adj b.adj a.adj y.τl x.τl,
          Hom₂.conjugateEquiv_τl] }

中文:
实例 :
  签名: CategoryStruct (a ⟶ b)
  定义体: Hom₂ α β
  id α :=
    { τl := 𝟙 _
      τr := 𝟙 _ }
  comp {a b c} x y :=
    { τl := x.τl ≫ y.τl
      τr := y.τr ≫ x.τr
      conjugateEquiv_τl := by
        simp [← conjugateEquiv_comp c.adj b.adj a.adj y.τl x.τl,
          Hom₂.conjugateEquiv_τl] }
-/
instance : CategoryStruct (a ⟶ b) where
  Hom α β := Hom₂ α β
  id α :=
    { τl := 𝟙 _
      τr := 𝟙 _ }
  comp {a b c} x y :=
    { τl := x.τl ≫ y.τl
      τr := y.τr ≫ x.τr
      conjugateEquiv_τl := by
        simp [← conjugateEquiv_comp c.adj b.adj a.adj y.τl x.τl,
          Hom₂.conjugateEquiv_τl] }

attribute [reassoc] comp_τl comp_τr

@[ext]
/--
lemma `hom₂_ext` / 引理 `hom₂_ext`

English:
lemma hom₂_ext
  given: {α β : a ⟶ b} {x y : α ⟶ β} (hl : x.τl = y.τl)
  statement: x = y
  proof: Hom₂.ext hl (by simp only [← Hom₂.conjugateEquiv_τl, hl])

中文:
引理 hom₂_ext
  条件: {α β : a ⟶ b} {x y : α ⟶ β} (hl : x.τl = y.τl)
  结论: x = y
  证明: Hom₂.ext hl (by simp only [← Hom₂.conjugateEquiv_τl, hl])
-/
lemma hom₂_ext {α β : a ⟶ b} {x y : α ⟶ β} (hl : x.τl = y.τl) : x = y :=
  Hom₂.ext hl (by simp only [← Hom₂.conjugateEquiv_τl, hl])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (a ⟶ b)

中文:
实例 :
  签名: 范畴 (a ⟶ b)
-/
instance : Category (a ⟶ b) where

/-- Constructor for isomorphisms between 1-morphisms in the bicategory `Adj B`. -/
@[simps]
/--
Definition of `iso₂Mk` / `iso₂Mk` 的定义

English:
definition iso₂Mk
  signature: {α β : a ⟶ b} (el : α.l ≅ β.l) (er : β.r ≅ α.r)
  body: { τl := el.hom
      τr := er.hom
      conjugateEquiv_τl := h }
  inv :=
    { τl := el.inv
      τr := er.inv
      conjugateEquiv_τl := by
        rw [← cancel_mono er.hom]; rw [Iso.inv_hom_id]; rw [← h]; rw [conjugateEquiv_comp]; rw [Iso.hom_inv_id]; rw [conjugateEquiv_id] }

中文:
定义 iso₂Mk
  签名: {α β : a ⟶ b} (el : α.l ≅ β.l) (er : β.r ≅ α.r)
  定义体: { τl := el.hom
      τr := er.hom
      conjugateEquiv_τl := h }
  inv :=
    { τl := el.inv
      τr := er.inv
      conjugateEquiv_τl := by
        rw [← cancel_mono er.hom]; rw [Iso.inv_hom_id]; rw [← h]; rw [conjugateEquiv_comp]; rw [Iso.hom_inv_id]; rw [conjugateEquiv_id] }

Depends on / 依赖: Iso.hom_inv_id, Iso.inv_hom_id, cancel_mono, cat_disch, conjugateEquiv_comp, conjugateEquiv_id, el.hom, el.inv, er.hom, er.inv, hom_inv_id, inv_hom_id
-/
def iso₂Mk {α β : a ⟶ b} (el : α.l ≅ β.l) (er : β.r ≅ α.r)
    (h : conjugateEquiv β.adj α.adj el.hom = er.hom := by cat_disch) :
    α ≅ β where
  hom :=
    { τl := el.hom
      τr := er.hom
      conjugateEquiv_τl := h }
  inv :=
    { τl := el.inv
      τr := er.inv
      conjugateEquiv_τl := by
        rw [← cancel_mono er.hom]; rw [Iso.inv_hom_id]; rw [← h]; rw [conjugateEquiv_comp]; rw [Iso.hom_inv_id]; rw [conjugateEquiv_id] }

namespace Bicategory

set_option linter.dupNamespace false in
/-- The associator in the bicategory `Adj B`. -/
@[simps!]
/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  signature: (α : a ⟶ b) (β : b ⟶ c) (γ : c ⟶ d)
  body: iso₂Mk (α_ _ _ _) (α_ _ _ _) (conjugateEquiv_associator_hom _ _ _)

中文:
定义 associator
  签名: (α : a ⟶ b) (β : b ⟶ c) (γ : c ⟶ d)
  定义体: iso₂Mk (α_ _ _ _) (α_ _ _ _) (conjugateEquiv_associator_hom _ _ _)

Depends on / 依赖: conjugateEquiv_associator_hom
-/
def associator (α : a ⟶ b) (β : b ⟶ c) (γ : c ⟶ d) : (α ≫ β) ≫ γ ≅ α ≫ β ≫ γ :=
  iso₂Mk (α_ _ _ _) (α_ _ _ _) (conjugateEquiv_associator_hom _ _ _)

set_option linter.dupNamespace false in
/-- The left unitor in the bicategory `Adj B`. -/
@[simps!]
/--
Definition of `leftUnitor` / `leftUnitor` 的定义

English:
definition leftUnitor
  signature: (α : a ⟶ b)
  body: iso₂Mk (fun_ _) (ρ_ _).symm
    (by simpa using conjugateEquiv_id_comp_right_apply α.adj α.adj (𝟙 _))

中文:
定义 leftUnitor
  签名: (α : a ⟶ b)
  定义体: iso₂Mk (fun_ _) (ρ_ _).symm
    (by simpa using conjugateEquiv_id_comp_right_apply α.adj α.adj (𝟙 _))

Depends on / 依赖: conjugateEquiv_id_comp_right_apply, fun_
-/
def leftUnitor (α : a ⟶ b) : 𝟙 a ≫ α ≅ α :=
  iso₂Mk (fun_ _) (ρ_ _).symm
    (by simpa using conjugateEquiv_id_comp_right_apply α.adj α.adj (𝟙 _))

set_option linter.dupNamespace false in
/-- The right unitor in the bicategory `Adj B`. -/
@[simps!]
/--
Definition of `rightUnitor` / `rightUnitor` 的定义

English:
definition rightUnitor
  signature: (α : a ⟶ b)
  body: iso₂Mk (ρ_ _) (fun_ _).symm
    (by simpa using conjugateEquiv_comp_id_right_apply α.adj α.adj (𝟙 _))

中文:
定义 rightUnitor
  签名: (α : a ⟶ b)
  定义体: iso₂Mk (ρ_ _) (fun_ _).symm
    (by simpa using conjugateEquiv_comp_id_right_apply α.adj α.adj (𝟙 _))

Depends on / 依赖: conjugateEquiv_comp_id_right_apply, fun_
-/
def rightUnitor (α : a ⟶ b) : α ≫ 𝟙 b ≅ α :=
  iso₂Mk (ρ_ _) (fun_ _).symm
    (by simpa using conjugateEquiv_comp_id_right_apply α.adj α.adj (𝟙 _))

set_option linter.dupNamespace false in
/-- The left whiskering in the bicategory `Adj B`. -/
@[simps]
/--
Definition of `whiskerLeft` / `whiskerLeft` 的定义

English:
definition whiskerLeft
  signature: (α : a ⟶ b) {β β' : b ⟶ c} (y : β ⟶ β')
  body: _ ◁ y.τl
  τr := y.τr ▷ _
  conjugateEquiv_τl := by
    simp [conjugateEquiv_whiskerLeft, Hom₂.conjugateEquiv_τl]

中文:
定义 whiskerLeft
  签名: (α : a ⟶ b) {β β' : b ⟶ c} (y : β ⟶ β')
  定义体: _ ◁ y.τl
  τr := y.τr ▷ _
  conjugateEquiv_τl := by
    simp [conjugateEquiv_whiskerLeft, Hom₂.conjugateEquiv_τl]
-/
def whiskerLeft (α : a ⟶ b) {β β' : b ⟶ c} (y : β ⟶ β') : α ≫ β ⟶ α ≫ β' where
  τl := _ ◁ y.τl
  τr := y.τr ▷ _
  conjugateEquiv_τl := by
    simp [conjugateEquiv_whiskerLeft, Hom₂.conjugateEquiv_τl]

set_option linter.dupNamespace false in
/-- The right whiskering in the bicategory `Adj B`. -/
@[simps]
/--
Definition of `whiskerRight` / `whiskerRight` 的定义

English:
definition whiskerRight
  signature: {α α' : a ⟶ b} (x : α ⟶ α') (β : b ⟶ c)
  body: x.τl ▷ _
  τr := _ ◁ x.τr
  conjugateEquiv_τl := by
    simp [conjugateEquiv_whiskerRight, Hom₂.conjugateEquiv_τl]

中文:
定义 whiskerRight
  签名: {α α' : a ⟶ b} (x : α ⟶ α') (β : b ⟶ c)
  定义体: x.τl ▷ _
  τr := _ ◁ x.τr
  conjugateEquiv_τl := by
    simp [conjugateEquiv_whiskerRight, Hom₂.conjugateEquiv_τl]
-/
def whiskerRight {α α' : a ⟶ b} (x : α ⟶ α') (β : b ⟶ c) : α ≫ β ⟶ α' ≫ β where
  τl := x.τl ▷ _
  τr := _ ◁ x.τr
  conjugateEquiv_τl := by
    simp [conjugateEquiv_whiskerRight, Hom₂.conjugateEquiv_τl]

end Bicategory

attribute [local simp] whisker_exchange

@[simps! whiskerRight_τr whiskerRight_τl whiskerLeft_τr whiskerLeft_τl
  associator_hom_τr associator_inv_τr associator_hom_τl associator_inv_τl
  leftUnitor_hom_τr leftUnitor_inv_τr leftUnitor_hom_τl leftUnitor_inv_τl
  rightUnitor_hom_τr rightUnitor_inv_τr rightUnitor_hom_τl rightUnitor_inv_τl]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bicategory (Adj B)
  body: Bicategory.whiskerLeft
  whiskerRight := Bicategory.whiskerRight
  associator := Bicategory.associator
  leftUnitor := Bicategory.leftUnitor
  rightUnitor := Bicategory.rightUnitor

中文:
实例 :
  签名: 双范畴 (伴随 B)
  定义体: Bicategory.whiskerLeft
  whiskerRight := Bicategory.whiskerRight
  associator := Bicategory.associator
  leftUnitor := Bicategory.leftUnitor
  rightUnitor := Bicategory.rightUnitor

Depends on / 依赖: Bicategory, Bicategory.whiskerLeft, whiskerLeft
-/
instance : Bicategory (Adj B) where
  whiskerLeft := Bicategory.whiskerLeft
  whiskerRight := Bicategory.whiskerRight
  associator := Bicategory.associator
  leftUnitor := Bicategory.leftUnitor
  rightUnitor := Bicategory.rightUnitor

/-- The forget pseudofunctor from `Adj B` to `B`. -/
@[simps]
/--
Definition of `forget₁` / `forget₁` 的定义

English:
definition forget₁
  signature: : Adj B ⥤ᵖ B where
  body: a.obj
  map x := x.l
  map₂ α := α.τl
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _

中文:
定义 forget₁
  签名: : 伴随 B ⥤ᵖ B where
  定义体: a.obj
  map x := x.l
  map₂ α := α.τl
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _

Depends on / 依赖: a.obj
-/
def forget₁ : Adj B ⥤ᵖ B where
  obj a := a.obj
  map x := x.l
  map₂ α := α.τl
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _

-- TODO: define `forget₂` which sends an adjunction to its right adjoint functor

/-- Given an isomorphism between two 1-morphisms in `Adj B`, this is the
underlying isomorphism between the left adjoints. -/
@[simps]
/--
Definition of `lIso` / `lIso` 的定义

English:
definition lIso
  signature: {a b : Adj B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂)
  body: e.hom.τl
  inv := e.inv.τl
  hom_inv_id := by rw [← comp_τl, e.hom_inv_id, id_τl]
  inv_hom_id := by rw [← comp_τl, e.inv_hom_id, id_τl]

中文:
定义 lIso
  签名: {a b : 伴随 B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂)
  定义体: e.hom.τl
  inv := e.inv.τl
  hom_inv_id := by rw [← comp_τl, e.hom_inv_id, id_τl]
  inv_hom_id := by rw [← comp_τl, e.inv_hom_id, id_τl]

Depends on / 依赖: e.hom
-/
def lIso {a b : Adj B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂) : adj₁.l ≅ adj₂.l where
  hom := e.hom.τl
  inv := e.inv.τl
  hom_inv_id := by rw [← comp_τl, e.hom_inv_id, id_τl]
  inv_hom_id := by rw [← comp_τl, e.inv_hom_id, id_τl]

/-- Given an isomorphism between two 1-morphisms in `Adj B`, this is the
underlying isomorphism between the right adjoints. -/
@[simps]
/--
Definition of `rIso` / `rIso` 的定义

English:
definition rIso
  signature: {a b : Adj B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂)
  body: e.inv.τr
  inv := e.hom.τr
  hom_inv_id := by rw [← comp_τr, e.hom_inv_id, id_τr]
  inv_hom_id := by rw [← comp_τr, e.inv_hom_id, id_τr]

中文:
定义 rIso
  签名: {a b : 伴随 B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂)
  定义体: e.inv.τr
  inv := e.hom.τr
  hom_inv_id := by rw [← comp_τr, e.hom_inv_id, id_τr]
  inv_hom_id := by rw [← comp_τr, e.inv_hom_id, id_τr]

Depends on / 依赖: e.inv
-/
def rIso {a b : Adj B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂) : adj₁.r ≅ adj₂.r where
  hom := e.inv.τr
  inv := e.hom.τr
  hom_inv_id := by rw [← comp_τr, e.hom_inv_id, id_τr]
  inv_hom_id := by rw [← comp_τr, e.inv_hom_id, id_τr]

end Adj

end Bicategory

end CategoryTheory
