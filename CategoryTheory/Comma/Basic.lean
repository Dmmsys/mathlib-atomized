/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Products.Unitor

/-!
# Comma categories

A comma category is a construction in category theory, which builds a category out of two functors
with a common codomain. Specifically, for functors `L : A ⥤ T` and `R : B ⥤ T`, an object in
`Comma L R` is a morphism `hom : L.obj left ⟶ R.obj right` for some objects `left : A` and
`right : B`, and a morphism in `Comma L R` between `hom : L.obj left ⟶ R.obj right` and
`hom' : L.obj left' ⟶ R.obj right'` is a commutative square

```
L.obj left ⟶ L.obj left'
      | |
  hom | | hom'
      ↓ ↓
R.obj right ⟶ R.obj right',
```

where the top and bottom morphism come from morphisms `left ⟶ left'` and `right ⟶ right'`,
respectively.

## Main definitions

* `Comma L R`: the comma category of the functors `L` and `R`.
* `Over X`: the over category of the object `X` (developed in `Over.lean`).
* `Under X`: the under category of the object `X` (also developed in `Over.lean`).
* `Arrow T`: the arrow category of the category `T` (developed in `Arrow.lean`).

## References

* <https://ncatlab.org/nlab/show/comma+category>

## Tags

comma, slice, coslice, over, under, arrow
-/

@[expose] public section

namespace CategoryTheory

open Category

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]
variable {A' : Type u₄} [Category.{v₄} A']
variable {B' : Type u₅} [Category.{v₅} B']
variable {T' : Type u₆} [Category.{v₆} T']

to_dual_name_hint Left Right, Fst Snd, L R, L₁ R₁, L₂ R₂, A B, F₁ F₂

set_option linter.translate.warnInvalid false in
/-- The objects of the comma category are triples of an object `left : A`, an object
`right : B` and a morphism `hom : L.obj left ⟶ R.obj right`. -/
@[to_dual self (reorder := A B, 2 4, L R), wikidata Q1780005]
/--
Definition of `Comma` / `Comma` 的定义

English:
structure Comma
  parameters: (L : A ⥤ T) (R : B ⥤ T)
  axioms and operations (3):
    - left : A
    - right : B
    - hom : L.obj left ⟶ R.obj right

中文:
结构 Comma
  参数: (L : A ⥤ T) (R : B ⥤ T)
  公理与运算 (3 个):
    - left : A
    - right : B
    - hom : L.obj left ⟶ R.obj right
-/
structure Comma (L : A ⥤ T) (R : B ⥤ T) : Type max u₁ u₂ v₃ where
  /-- The left subobject -/
  left : A
  /-- The right subobject -/
  right : B
  /-- A morphism from `L.obj left` to `R.obj right` -/
  hom : L.obj left ⟶ R.obj right

attribute [to_dual existing] Comma.left
attribute [to_dual self] Comma.hom Comma.mk

-- Satisfying the inhabited linter
/--
Instance `Comma.inhabited` / 实例 `Comma.inhabited`

English:
instance Comma.inhabited
  signature: [Inhabited T]
  body: { left := default
      right := default
      hom := 𝟙 default }

中文:
实例 Comma.inhabited
  签名: [Inhabited T]
  定义体: { left := default
      right := default
      hom := 𝟙 default }
-/
instance Comma.inhabited [Inhabited T] : Inhabited (Comma (𝟭 T) (𝟭 T)) where
  default :=
    { left := default
      right := default
      hom := 𝟙 default }

variable {L : A ⥤ T} {R : B ⥤ T}

set_option linter.translate.warnInvalid false in
/-- A morphism between two objects in the comma category is a commutative square connecting the
morphisms coming from the two objects using morphisms in the image of the functors `L` and `R`.
-/
@[ext, to_dual self (reorder := A B, 2 4, L R, X Y)]
/--
Definition of `CommaMorphism` / `CommaMorphism` 的定义

English:
structure CommaMorphism
  parameters: (X Y : Comma L R)
  axioms and operations (3):
    - left : X.left ⟶ Y.left
    - right : X.right ⟶ Y.right
    - w : L.map left ≫ Y.hom = X.hom ≫ R.map right  [default: by cat_disch]

中文:
结构 CommaMorphism
  参数: (X Y : Comma L R)
  公理与运算 (3 个):
    - left : X.left ⟶ Y.left
    - right : X.right ⟶ Y.right
    - w : L.map left ≫ Y.hom = X.hom ≫ R.map right  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure CommaMorphism (X Y : Comma L R) where
  /-- Morphism on left objects -/
  left : X.left ⟶ Y.left
  /-- Morphism on right objects -/
  right : X.right ⟶ Y.right
  w : L.map left ≫ Y.hom = X.hom ≫ R.map right := by cat_disch

attribute [to_dual existing] CommaMorphism.left

@[to_dual existing w]
/--
theorem `CommaMorphism.w'` / 定理 `CommaMorphism.w'`

English:
theorem CommaMorphism.w'
  given: {X Y : Comma R L} (self : CommaMorphism Y X)
  proof: self.w.symm

中文:
定理 CommaMorphism.w'
  条件: {X Y : Comma R L} (self : CommaMorphism Y X)
  证明: self.w.symm

Depends on / 依赖: self.w.symm
-/
theorem CommaMorphism.w' {X Y : Comma R L} (self : CommaMorphism Y X) :
    Y.hom ≫ L.map self.right = R.map self.left ≫ X.hom :=
  self.w.symm

/-- `CommaMorphism.mk'` is the dual of `CommaMorphism.mk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing mk]
/--
Definition of `CommaMorphism.mk'` / `CommaMorphism.mk'` 的定义

English:
abbreviation CommaMorphism.mk'
  signature: {X Y : Comma R L}
  body: w.symm

中文:
缩写 CommaMorphism.mk'
  签名: {X Y : Comma R L}
  定义体: w.symm

Depends on / 依赖: w.symm
-/
abbrev CommaMorphism.mk' {X Y : Comma R L}
    (right : Y.right ⟶ X.right) (left : Y.left ⟶ X.left)
    (w : Y.hom ≫ L.map right = R.map left ≫ X.hom) :
    CommaMorphism Y X where
  left; right; w := w.symm

-- Satisfying the inhabited linter
/--
Instance `CommaMorphism.inhabited` / 实例 `CommaMorphism.inhabited`

English:
instance CommaMorphism.inhabited
  signature: [Inhabited (Comma L R)]
  body: ⟨{ left := 𝟙 _, right := 𝟙 _}⟩

中文:
实例 CommaMorphism.inhabited
  签名: [Inhabited (Comma L R)]
  定义体: ⟨{ left := 𝟙 _, right := 𝟙 _}⟩
-/
instance CommaMorphism.inhabited [Inhabited (Comma L R)] :
    Inhabited (CommaMorphism (default : Comma L R) default) :=
    ⟨{ left := 𝟙 _, right := 𝟙 _}⟩

attribute [reassoc (attr := simp)] CommaMorphism.w

@[to_dual self]
/--
Instance `commaCategory` / 实例 `commaCategory`

English:
instance commaCategory
  signature: : Category (Comma L R) where
  body: CommaMorphism X Y
  id X :=
    { left := 𝟙 X.left
      right := 𝟙 X.right }
  comp f g :=
    { left := f.left ≫ g.left
      right := f.right ≫ g.right }

中文:
实例 commaCategory
  签名: : Category (Comma L R) where
  定义体: CommaMorphism X Y
  id X :=
    { left := 𝟙 X.left
      right := 𝟙 X.right }
  comp f g :=
    { left := f.left ≫ g.left
      right := f.right ≫ g.right }

Depends on / 依赖: CommaMorphism
-/
instance commaCategory : Category (Comma L R) where
  Hom X Y := CommaMorphism X Y
  id X :=
    { left := 𝟙 X.left
      right := 𝟙 X.right }
  comp f g :=
    { left := f.left ≫ g.left
      right := f.right ≫ g.right }

namespace Comma

section

variable {X Y Z : Comma L R} {f : X ⟶ Y} {g : Y ⟶ Z}

@[ext, to_dual self (reorder := A B, 2 4, L R, X Y, h₁ h₂)]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right)
  statement: f = g
  proof: CommaMorphism.ext h₁ h₂

@[to_dual (attr := simp)]

中文:
引理 hom_ext
  条件: (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right)
  结论: f = g
  证明: CommaMorphism.ext h₁ h₂

@[to_dual (attr := simp)]

Depends on / 依赖: CommaMorphism, CommaMorphism.ext
-/
lemma hom_ext (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) : f = g :=
  CommaMorphism.ext h₁ h₂

@[to_dual (attr := simp)]
/--
theorem `id_left` / 定理 `id_left`

English:
theorem id_left
  statement: (𝟙 X : CommaMorphism X X).left = 𝟙 X.left
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 id_left
  结论: (𝟙 X : CommaMorphism X X).left = 𝟙 X.left
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem id_left : (𝟙 X : CommaMorphism X X).left = 𝟙 X.left :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `comp_left` / 定理 `comp_left`

English:
theorem comp_left
  statement: (f ≫ g).left = f.left ≫ g.left
  proof: rfl

中文:
定理 comp_left
  结论: (f ≫ g).left = f.left ≫ g.left
  证明: rfl
-/
theorem comp_left : (f ≫ g).left = f.left ≫ g.left :=
  rfl

end

variable (L) (R)

set_option linter.translate.warnInvalid false in
/-- The functor sending an object `X` in the comma category to `X.left`. -/
@[to_dual (reorder := L R) (attr := simps, implicit_reducible)
/-- The functor sending an object `X` in the comma category to `X.right`. -/]
/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : Comma L R ⥤ A where
  body: X.left
  map f := f.left

中文:
定义 fst
  签名: : Comma L R ⥤ A where
  定义体: X.left
  map f := f.left

Depends on / 依赖: X.left
-/
def fst : Comma L R ⥤ A where
  obj X := X.left
  map f := f.left

attribute [to_dual existing] fst_map

set_option backward.defeqAttrib.useBackward true in
/-- We can interpret the commutative square constituting a morphism in the comma category as a
natural transformation between the functors `fst ⋙ L` and `snd ⋙ R` from the comma category
to `T`, where the components are given by the morphism that constitutes an object of the comma
category. -/
@[simps, to_dual self]
/--
Definition of `natTrans` / `natTrans` 的定义

English:
definition natTrans
  signature: : fst L R ⋙ L ⟶ snd L R ⋙ R where app X
  body: X.hom

@[simp]

中文:
定义 natTrans
  签名: : fst L R ⋙ L ⟶ snd L R ⋙ R where app X
  定义体: X.hom

@[simp]

Depends on / 依赖: X.hom
-/
def natTrans : fst L R ⋙ L ⟶ snd L R ⋙ R where app X := X.hom

@[simp]
/--
theorem `eqToHom_left` / 定理 `eqToHom_left`

English:
theorem eqToHom_left
  given: (X Y : Comma L R) (H : X = Y)
  proof: by
  cases H
  rfl

@[simp]

中文:
定理 eqToHom_left
  条件: (X Y : Comma L R) (H : X = Y)
  证明: by
  cases H
  rfl

@[simp]
-/
theorem eqToHom_left (X Y : Comma L R) (H : X = Y) :
    CommaMorphism.left (eqToHom H) = eqToHom (by cases H; rfl) := by
  cases H
  rfl

@[simp]
/--
theorem `eqToHom_right` / 定理 `eqToHom_right`

English:
theorem eqToHom_right
  given: (X Y : Comma L R) (H : X = Y)
  proof: by
  cases H
  rfl

中文:
定理 eqToHom_right
  条件: (X Y : Comma L R) (H : X = Y)
  证明: by
  cases H
  rfl

Depends on / 依赖: hasInitial, isInitialElementsMkShrinkYonedaObjObjEquivId
-/
theorem eqToHom_right (X Y : Comma L R) (H : X = Y) :
    CommaMorphism.right (eqToHom H) = eqToHom (by cases H; rfl) := by
  cases H
  rfl

section

variable {L R} {X Y : Comma L R} (e : X ⟶ Y)

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIso
  signature: e] : IsIso e.left
  body: (Comma.fst L R).map_isIso e

@[to_dual (attr := simp, push ←)]

中文:
实例 [IsIso
  签名: e] : IsIso e.left
  定义体: (Comma.fst L R).map_isIso e

@[to_dual (attr := simp, push ←)]

Depends on / 依赖: Comma.fst, map_isIso
-/
instance [IsIso e] : IsIso e.left :=
  (Comma.fst L R).map_isIso e

@[to_dual (attr := simp, push ←)]
/--
lemma `inv_left` / 引理 `inv_left`

English:
lemma inv_left
  given: [IsIso e]
  statement: (inv e).left = inv e.left
  proof: by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← Comma.comp_left]; rw [IsIso.hom_inv_id]; rw [id_left]

@[to_dual inv_left_hom_right]

中文:
引理 inv_left
  条件: [IsIso e]
  结论: (inv e).left = inv e.left
  证明: by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← Comma.comp_left]; rw [IsIso.hom_inv_id]; rw [id_left]

@[to_dual inv_left_hom_right]

Depends on / 依赖: Comma.comp_left, IsIso.eq_inv_of_hom_inv_id, IsIso.hom_inv_id, comp_left, eq_inv_of_hom_inv_id, hom_inv_id, id_left
-/
lemma inv_left [IsIso e] : (inv e).left = inv e.left := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← Comma.comp_left]; rw [IsIso.hom_inv_id]; rw [id_left]

@[to_dual inv_left_hom_right]
/--
lemma `left_hom_inv_right` / 引理 `left_hom_inv_right`

English:
lemma left_hom_inv_right
  given: [IsIso e]
  statement: L.map (e.left) ≫ Y.hom ≫ R.map (inv e.right) = X.hom
  proof: by
  simp

中文:
引理 left_hom_inv_right
  条件: [IsIso e]
  结论: L.map (e.left) ≫ Y.hom ≫ R.map (inv e.right) = X.hom
  证明: by
  simp
-/
lemma left_hom_inv_right [IsIso e] : L.map (e.left) ≫ Y.hom ≫ R.map (inv e.right) = X.hom := by
  simp

end

section

variable {L₁ L₂ L₃ : A ⥤ T} {R₁ R₂ R₃ : B ⥤ T}

set_option linter.translate.warnInvalid false in
/-- Extract the isomorphism between the left objects from an isomorphism in the comma category. -/
@[to_dual (attr := simps!)
/-- Extract the isomorphism between the right objects from an isomorphism in the comma category. -/]
/--
Definition of `leftIso` / `leftIso` 的定义

English:
definition leftIso
  signature: {X Y : Comma L₁ R₁} (α : X ≅ Y)
  body: (fst L₁ R₁).mapIso α

中文:
定义 leftIso
  签名: {X Y : Comma L₁ R₁} (α : X ≅ Y)
  定义体: (fst L₁ R₁).mapIso α

Depends on / 依赖: mapIso
-/
def leftIso {X Y : Comma L₁ R₁} (α : X ≅ Y) : X.left ≅ Y.left := (fst L₁ R₁).mapIso α

attribute [to_dual existing rightIso_inv] leftIso_hom
attribute [to_dual existing rightIso_hom] leftIso_inv

/-- Construct an isomorphism in the comma category given isomorphisms of the objects whose forward
directions give a commutative square.
-/
@[to_dual none, simps (attr := to_dual none)]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {X Y : Comma L₁ R₁} (l : X.left ≅ Y.left) (r : X.right ≅ Y.right)
  body: { left := l.hom
      right := r.hom
      w := h }
  inv :=
    { left := l.inv
      right := r.inv
      w := by
        rw [← L₁.mapIso_inv l]; rw [Iso.inv_comp_eq]; rw [L₁.mapIso_hom]; rw [← Category.assoc]; rw [h]; rw [Category.assoc]; rw [← R₁.map_comp]
        simp }

中文:
定义 isoMk
  签名: {X Y : Comma L₁ R₁} (l : X.left ≅ Y.left) (r : X.right ≅ Y.right)
  定义体: { left := l.hom
      right := r.hom
      w := h }
  inv :=
    { left := l.inv
      right := r.inv
      w := by
        rw [← L₁.mapIso_inv l]; rw [Iso.inv_comp_eq]; rw [L₁.mapIso_hom]; rw [← Category.assoc]; rw [h]; rw [Category.assoc]; rw [← R₁.map_comp]
        simp }

Depends on / 依赖: Category, Category.assoc, Iso.inv_comp_eq, cat_disch, inv_comp_eq, l.hom, l.inv, mapIso_hom, mapIso_inv, map_comp, r.hom, r.inv
-/
def isoMk {X Y : Comma L₁ R₁} (l : X.left ≅ Y.left) (r : X.right ≅ Y.right)
    (h : L₁.map l.hom ≫ Y.hom = X.hom ≫ R₁.map r.hom := by cat_disch) : X ≅ Y where
  hom :=
    { left := l.hom
      right := r.hom
      w := h }
  inv :=
    { left := l.inv
      right := r.inv
      w := by
        rw [← L₁.mapIso_inv l]; rw [Iso.inv_comp_eq]; rw [L₁.mapIso_hom]; rw [← Category.assoc]; rw [h]; rw [Category.assoc]; rw [← R₁.map_comp]
        simp }

section

variable {L R}
variable {L' : A' ⥤ T'} {R' : B' ⥤ T'}
  {F₁ : A ⥤ A'} {F₂ : B ⥤ B'} {F : T ⥤ T'}
  (α : F₁ ⋙ L' ⟶ L ⋙ F) (β : R ⋙ F ⟶ F₂ ⋙ R')

/-- The functor `Comma L R ⥤ Comma L' R'` induced by three functors `F₁`, `F₂`, `F`
and two natural transformations `F₁ ⋙ L' ⟶ L ⋙ F` and `R ⋙ F ⟶ F₂ ⋙ R'`. -/
@[simps, implicit_reducible,
  to_dual self (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β)]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : Comma L R ⥤ Comma L' R' where
  body: { left := F₁.obj X.left
      right := F₂.obj X.right
      hom := α.app X.left ≫ F.map X.hom ≫ β.app X.right }
  map {X Y} φ :=
    { left := F₁.map φ.left
      right := F₂.map φ.right
      w := by
        dsimp
        rw [assoc]; rw [assoc]; rw [← Functor.comp_map]; rw [α.naturality_assoc]; rw 

中文:
定义 map
  签名: : Comma L R ⥤ Comma L' R' where
  定义体: { left := F₁.obj X.left
      right := F₂.obj X.right
      hom := α.app X.left ≫ F.map X.hom ≫ β.app X.right }
  map {X Y} φ :=
    { left := F₁.map φ.left
      right := F₂.map φ.right
      w := by
        dsimp
        rw [assoc]; rw [assoc]; rw [← Functor.comp_map]; rw [α.naturality_assoc]; rw 

Depends on / 依赖: F.map, F.map_comp_assoc, Functor, Functor.comp_map, X.hom, X.left, X.right, comp_map, map_comp_assoc, naturality, naturality_assoc
-/
def map : Comma L R ⥤ Comma L' R' where
  obj X :=
    { left := F₁.obj X.left
      right := F₂.obj X.right
      hom := α.app X.left ≫ F.map X.hom ≫ β.app X.right }
  map {X Y} φ :=
    { left := F₁.map φ.left
      right := F₂.map φ.right
      w := by
        dsimp
        rw [assoc]; rw [assoc]; rw [← Functor.comp_map]; rw [α.naturality_assoc]; rw [← Functor.comp_map]; rw [← β.naturality]
        dsimp
        rw [← F.map_comp_assoc]; rw [← F.map_comp_assoc]; rw [φ.w] }

attribute [to_dual existing] map_obj_left
attribute [to_dual existing (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β, X Y)]
  map_map_left

@[to_dual existing (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β) map_obj_hom]
/--
theorem `map_obj_hom'` / 定理 `map_obj_hom'`

English:
theorem map_obj_hom'
  given: (X : Comma L R)
  proof: by simp

@[to_dual self (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β, 22 23)]

中文:
定理 map_obj_hom'
  条件: (X : Comma L R)
  证明: by simp

@[to_dual self (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β, 22 23)]
-/
theorem map_obj_hom' (X : Comma L R) :
    ((map α β).obj X).hom = (α.app X.left ≫ F.map X.hom) ≫ β.app X.right := by simp

@[to_dual self (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β, 22 23)]
/--
Instance `faithful_map` / 实例 `faithful_map`

English:
instance faithful_map
  signature: [F₁.Faithful] [F₂.Faithful]
  body: by
    ext
    · exact F₁.map_injective (congr_arg CommaMorphism.left h)
    · exact F₂.map_injective (congr_arg CommaMorphism.right h)

@[to_dual self (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β, 23 24, 25 26)]

中文:
实例 faithful_map
  签名: [F₁.Faithful] [F₂.Faithful]
  定义体: by
    ext
    · exact F₁.map_injective (congr_arg CommaMorphism.left h)
    · exact F₂.map_injective (congr_arg CommaMorphism.right h)

@[to_dual self (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β, 23 24, 25 26)]

Depends on / 依赖: CommaMorphism, CommaMorphism.left, CommaMorphism.right, congr_arg, map_injective
-/
instance faithful_map [F₁.Faithful] [F₂.Faithful] : (map α β).Faithful where
  map_injective {X Y} f g h := by
    ext
    · exact F₁.map_injective (congr_arg CommaMorphism.left h)
    · exact F₂.map_injective (congr_arg CommaMorphism.right h)

@[to_dual self (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β, 23 24, 25 26)]
/--
Instance `full_map` / 实例 `full_map`

English:
instance full_map
  signature: [F.Faithful] [F₁.Full] [F₂.Full] [IsIso α] [IsIso β]
  body: ⟨{left := F₁.preimage φ.left
      right := F₂.preimage φ.right
      w := F.map_injective (by
        rw [← cancel_mono (β.app _)]; rw [← cancel_epi (α.app _)]; rw [F.map_comp]; rw [F.map_comp]; rw [assoc]; rw [assoc]
        calc
        _ = (F₁ ⋙ L').map (F₁.preimage φ.left) ≫ α.app Y.left ≫ F.ma

中文:
实例 full_map
  签名: [F.Faithful] [F₁.Full] [F₂.Full] [IsIso α] [IsIso β]
  定义体: ⟨{left := F₁.preimage φ.left
      right := F₂.preimage φ.right
      w := F.map_injective (by
        rw [← cancel_mono (β.app _)]; rw [← cancel_epi (α.app _)]; rw [F.map_comp]; rw [F.map_comp]; rw [assoc]; rw [assoc]
        calc
        _ = (F₁ ⋙ L').map (F₁.preimage φ.left) ≫ α.app Y.left ≫ F.ma

Depends on / 依赖: F.map, F.map_comp, F.map_injective, Functor, Functor.comp_map, Functor.map_preimage, X.hom, X.left, X.right, Y.hom, Y.left, Y.right, cancel_epi, cancel_mono, comp_map, map_comp, map_injective, map_obj_hom, map_preimage, naturality_assoc
-/
instance full_map [F.Faithful] [F₁.Full] [F₂.Full] [IsIso α] [IsIso β] : (map α β).Full where
  map_surjective {X Y} φ :=
    ⟨{left := F₁.preimage φ.left
      right := F₂.preimage φ.right
      w := F.map_injective (by
        rw [← cancel_mono (β.app _)]; rw [← cancel_epi (α.app _)]; rw [F.map_comp]; rw [F.map_comp]; rw [assoc]; rw [assoc]
        calc
        _ = (F₁ ⋙ L').map (F₁.preimage φ.left) ≫ α.app Y.left ≫ F.map Y.hom ≫ β.app Y.right := by
          rw [← Functor.comp_map]; rw [← α.naturality_assoc]
        _ = α.app X.left ≫ F.map X.hom ≫ β.app X.right ≫ (F₂ ⋙ R').map (F₂.preimage φ.right) := by
          simp only [Functor.comp_map, Functor.map_preimage, ← map_obj_hom α β Y, φ.w,
            map_obj_hom α β X, assoc]
        _ = _ := by rw [← Functor.comp_map, β.naturality] )},
      by cat_disch⟩

set_option backward.defeqAttrib.useBackward true in
@[to_dual self (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β, 22 23, 25 26)]
/--
Instance `essSurj_map` / 实例 `essSurj_map`

English:
instance essSurj_map
  signature: [F₁.EssSurj] [F₂.EssSurj] [F.Full] [IsIso α] [IsIso β]
  body: ⟨{left := F₁.objPreimage X.left
      right := F₂.objPreimage X.right
      hom := F.preimage ((inv α).app _ ≫ L'.map (F₁.objObjPreimageIso X.left).hom ≫
        X.hom ≫ R'.map (F₂.objObjPreimageIso X.right).inv ≫ (inv β).app _) },
          ⟨isoMk (F₁.objObjPreimageIso X.left) (F₂.objObjPreimageIso

中文:
实例 essSurj_map
  签名: [F₁.EssSurj] [F₂.EssSurj] [F.Full] [IsIso α] [IsIso β]
  定义体: ⟨{left := F₁.objPreimage X.left
      right := F₂.objPreimage X.right
      hom := F.preimage ((inv α).app _ ≫ L'.map (F₁.objObjPreimageIso X.left).hom ≫
        X.hom ≫ R'.map (F₂.objObjPreimageIso X.right).inv ≫ (inv β).app _) },
          ⟨isoMk (F₁.objObjPreimageIso X.left) (F₂.objObjPreimageIso

Depends on / 依赖: F.preimage, Functor, Functor.comp_obj, Functor.map_preimage, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id, Iso.inv_hom_id, NatIso, NatIso.isIso_inv_app, X.hom, X.left, X.right, comp_id, comp_obj, hom_inv_id_assoc, inv_hom_id, isIso_inv_app, map_comp, map_id, map_preimage
-/
instance essSurj_map [F₁.EssSurj] [F₂.EssSurj] [F.Full] [IsIso α] [IsIso β] :
    (map α β).EssSurj where
  mem_essImage X :=
    ⟨{left := F₁.objPreimage X.left
      right := F₂.objPreimage X.right
      hom := F.preimage ((inv α).app _ ≫ L'.map (F₁.objObjPreimageIso X.left).hom ≫
        X.hom ≫ R'.map (F₂.objObjPreimageIso X.right).inv ≫ (inv β).app _) },
          ⟨isoMk (F₁.objObjPreimageIso X.left) (F₂.objObjPreimageIso X.right) (by
            dsimp
            simp only [NatIso.isIso_inv_app, Functor.comp_obj, Functor.map_preimage, assoc,
              IsIso.inv_hom_id, comp_id, IsIso.hom_inv_id_assoc]
            rw [← R'.map_comp]; rw [Iso.inv_hom_id]; rw [R'.map_id]; rw [comp_id])⟩⟩

@[to_dual self (reorder := A B, 2 4, A' B', 8 10, L R, L' R', F₁ F₂, α β, 22 23, 26 27)]
/--
Instance `isEquivalenceMap` / 实例 `isEquivalenceMap`

English:
instance isEquivalenceMap

中文:
实例 isEquivalenceMap
-/
noncomputable instance isEquivalenceMap
    [F₁.IsEquivalence] [F₂.IsEquivalence] [F.Faithful] [F.Full] [IsIso α] [IsIso β] :
    (map α β).IsEquivalence where

/-- The equality between `map α β ⋙ fst L' R'` and `fst L R ⋙ F₁`,
where `α : F₁ ⋙ L' ⟶ L ⋙ F`. -/
@[to_dual (attr := simp) (reorder := α β)
/-- The equality between `map α β ⋙ snd L' R'` and `snd L R ⋙ F₂`,
where `β : R ⋙ F ⟶ F₂ ⋙ R'`. -/]
/--
theorem `map_fst` / 定理 `map_fst`

English:
theorem map_fst
  statement: map α β ⋙ fst L' R' = fst L R ⋙ F₁
  proof: rfl

中文:
定理 map_fst
  结论: map α β ⋙ fst L' R' = fst L R ⋙ F₁
  证明: rfl
-/
theorem map_fst : map α β ⋙ fst L' R' = fst L R ⋙ F₁ :=
  rfl

set_option linter.translate.warnInvalid false in
/-- The isomorphism between `map α β ⋙ fst L' R'` and `fst L R ⋙ F₁`,
where `α : F₁ ⋙ L' ⟶ L ⋙ F`. -/
@[to_dual (attr := simps!) (reorder := α β)
/-- The isomorphism between `map α β ⋙ snd L' R'` and `snd L R ⋙ F₂`,
where `β : R ⋙ F ⟶ F₂ ⋙ R'`. -/]
/--
Definition of `mapFst` / `mapFst` 的定义

English:
definition mapFst
  signature: : map α β ⋙ fst L' R' ≅ fst L R ⋙ F₁
  body: NatIso.ofComponents (fun _ => Iso.refl _) (by simp)

中文:
定义 mapFst
  签名: : map α β ⋙ fst L' R' ≅ fst L R ⋙ F₁
  定义体: NatIso.ofComponents (fun _ => Iso.refl _) (by simp)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def mapFst : map α β ⋙ fst L' R' ≅ fst L R ⋙ F₁ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by simp)

end

set_option linter.translate.warnInvalid false in
/-- A natural transformation `L₁ ⟶ L₂` induces a functor `Comma L₂ R ⥤ Comma L₁ R`. -/
@[to_dual (attr := simps, implicit_reducible)
/-- A natural transformation `R₁ ⟶ R₂` induces a functor `Comma L R₁ ⥤ Comma L R₂`. -/]
/--
Definition of `mapLeft` / `mapLeft` 的定义

English:
definition mapLeft
  signature: (l : L₁ ⟶ L₂)
  body: { left := X.left
      right := X.right
      hom := l.app X.left ≫ X.hom }
  map f :=
    { left := f.left
      right := f.right }

中文:
定义 mapLeft
  签名: (l : L₁ ⟶ L₂)
  定义体: { left := X.left
      right := X.right
      hom := l.app X.left ≫ X.hom }
  map f :=
    { left := f.left
      right := f.right }

Depends on / 依赖: X.hom, X.left, X.right, f.left, f.right, l.app
-/
def mapLeft (l : L₁ ⟶ L₂) : Comma L₂ R ⥤ Comma L₁ R where
  obj X :=
    { left := X.left
      right := X.right
      hom := l.app X.left ≫ X.hom }
  map f :=
    { left := f.left
      right := f.right }

attribute [to_dual existing] mapLeft_map_left
attribute [to_dual existing] mapLeft_map_right

set_option linter.translate.warnInvalid false in
/-- The functor `Comma L R ⥤ Comma L R` induced by the identity natural transformation on `L` is
naturally isomorphic to the identity functor. -/
@[to_dual (attr := simps!)
/-- The functor `Comma L R ⥤ Comma L R` induced by the identity natural transformation on `R` is
naturally isomorphic to the identity functor. -/]
/--
Definition of `mapLeftId` / `mapLeftId` 的定义

English:
definition mapLeftId
  signature: : mapLeft R (𝟙 L) ≅ 𝟭 _
  body: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

中文:
定义 mapLeftId
  签名: : mapLeft R (𝟙 L) ≅ 𝟭 _
  定义体: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def mapLeftId : mapLeft R (𝟙 L) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option linter.translate.warnInvalid false in
/-- The functor `Comma L₁ R ⥤ Comma L₃ R` induced by the composition of two natural transformations
`l : L₁ ⟶ L₂` and `l' : L₂ ⟶ L₃` is naturally isomorphic to the composition of the two functors
induced by these natural transformations. -/
@[to_dual (attr := simps!)
/-- The functor `Comma L R₁ ⥤ Comma L R₃` induced by the composition of the natural transformations
`r : R₁ ⟶ R₂` and `r' : R₂ ⟶ R₃` is naturally isomorphic to the composition of the functors
induced by these natural transformations. -/]
/--
Definition of `mapLeftComp` / `mapLeftComp` 的定义

English:
definition mapLeftComp
  signature: (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃)
  body: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

中文:
定义 mapLeftComp
  签名: (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃)
  定义体: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def mapLeftComp (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃) :
    mapLeft R (l ≫ l') ≅ mapLeft R l' ⋙ mapLeft R l :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option linter.translate.warnInvalid false in
/-- Two equal natural transformations `L₁ ⟶ L₂` yield naturally isomorphic functors
`Comma L₁ R ⥤ Comma L₂ R`. -/
@[to_dual (attr := simps!)
/-- Two equal natural transformations `R₁ ⟶ R₂` yield naturally isomorphic functors
`Comma L R₁ ⥤ Comma L R₂`. -/]
/--
Definition of `mapLeftEq` / `mapLeftEq` 的定义

English:
definition mapLeftEq
  signature: (l l' : L₁ ⟶ L₂) (h : l = l')
  body: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

中文:
定义 mapLeftEq
  签名: (l l' : L₁ ⟶ L₂) (h : l = l')
  定义体: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def mapLeftEq (l l' : L₁ ⟶ L₂) (h : l = l') : mapLeft R l ≅ mapLeft R l' :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

set_option backward.defeqAttrib.useBackward true in
set_option linter.translate.warnInvalid false in
/-- A natural isomorphism `L₁ ≅ L₂` induces an equivalence of categories
`Comma L₁ R ≌ Comma L₂ R`. -/
@[to_dual (attr := simps!, implicit_reducible)
/-- A natural isomorphism `R₁ ≅ R₂` induces an equivalence of categories
`Comma L R₁ ≌ Comma L R₂`. -/]
/--
Definition of `mapLeftIso` / `mapLeftIso` 的定义

English:
definition mapLeftIso
  signature: (i : L₁ ≅ L₂)
  body: mapLeft _ i.inv
  inverse := mapLeft _ i.hom
  unitIso := (mapLeftId _ _).symm ≪≫ mapLeftEq _ _ _ i.hom_inv_id.symm ≪≫ mapLeftComp _ _ _
  counitIso := (mapLeftComp _ _ _).symm ≪≫ mapLeftEq _ _ _ i.inv_hom_id ≪≫ mapLeftId _ _

中文:
定义 mapLeftIso
  签名: (i : L₁ ≅ L₂)
  定义体: mapLeft _ i.inv
  inverse := mapLeft _ i.hom
  unitIso := (mapLeftId _ _).symm ≪≫ mapLeftEq _ _ _ i.hom_inv_id.symm ≪≫ mapLeftComp _ _ _
  counitIso := (mapLeftComp _ _ _).symm ≪≫ mapLeftEq _ _ _ i.inv_hom_id ≪≫ mapLeftId _ _

Depends on / 依赖: i.inv, mapLeft
-/
def mapLeftIso (i : L₁ ≅ L₂) : Comma L₁ R ≌ Comma L₂ R where
  functor := mapLeft _ i.inv
  inverse := mapLeft _ i.hom
  unitIso := (mapLeftId _ _).symm ≪≫ mapLeftEq _ _ _ i.hom_inv_id.symm ≪≫ mapLeftComp _ _ _
  counitIso := (mapLeftComp _ _ _).symm ≪≫ mapLeftEq _ _ _ i.inv_hom_id ≪≫ mapLeftId _ _

end

section

variable {C : Type u₄} [Category.{v₄} C]

set_option linter.translate.warnInvalid false in
/-- The functor `(F ⋙ L, R) ⥤ (L, R)` -/
@[to_dual (attr := simps,
  implicit_reducible) (reorder := F L R) /-- The functor `(L, F ⋙ R) ⥤ (L, R)` -/]
/--
Definition of `preLeft` / `preLeft` 的定义

English:
definition preLeft
  signature: (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T)
  body: { left := F.obj X.left
      right := X.right
      hom := X.hom }
  map f :=
    { left := F.map f.left
      right := f.right
      w := by simpa using! f.w }

中文:
定义 preLeft
  签名: (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T)
  定义体: { left := F.obj X.left
      right := X.right
      hom := X.hom }
  map f :=
    { left := F.map f.left
      right := f.right
      w := by simpa using! f.w }

Depends on / 依赖: F.map, F.obj, X.hom, X.left, X.right, f.left, f.right
-/
def preLeft (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) : Comma (F ⋙ L) R ⥤ Comma L R where
  obj X :=
    { left := F.obj X.left
      right := X.right
      hom := X.hom }
  map f :=
    { left := F.map f.left
      right := f.right
      w := by simpa using! f.w }

set_option backward.defeqAttrib.useBackward true in
/-- `Comma.preLeft` is a particular case of `Comma.map`,
but with better definitional properties. -/
@[to_dual (reorder := F L R)
/-- `Comma.preRight` is a particular case of `Comma.map`,
but with better definitional properties. -/]
/--
Definition of `preLeftIso` / `preLeftIso` 的定义

English:
definition preLeftIso
  signature: (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T)
  body: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _) (by simp -implicitDefEqProofs))

@[to_dual]

中文:
定义 preLeftIso
  签名: (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T)
  定义体: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _) (by simp -implicitDefEqProofs))

@[to_dual]

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, implicitDefEqProofs, ofComponents
-/
def preLeftIso (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) :
    preLeft F L R ≅ map (F ⋙ L).rightUnitor.inv (R.rightUnitor.hom ≫ R.leftUnitor.inv) :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _) (by simp -implicitDefEqProofs))

@[to_dual]
instance (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.Faithful] : (preLeft F L R).Faithful :=
  Functor.Faithful.of_iso (preLeftIso F L R).symm

@[to_dual]
instance (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.Full] : (preLeft F L R).Full :=
  Functor.Full.of_iso (preLeftIso F L R).symm

@[to_dual]
instance (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.EssSurj] : (preLeft F L R).EssSurj :=
  Functor.essSurj_of_iso (preLeftIso F L R).symm

/-- If `F` is an equivalence, then so is `preLeft F L R`. -/
@[to_dual /-- If `F` is an equivalence, then so is `preRight L F R`. -/]
/--
Instance `isEquivalence_preLeft` / 实例 `isEquivalence_preLeft`

English:
instance isEquivalence_preLeft
  signature: (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.IsEquivalence]

中文:
实例 isEquivalence_preLeft
  签名: (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.IsEquivalence]
-/
instance isEquivalence_preLeft (F : C ⥤ A) (L : A ⥤ T) (R : B ⥤ T) [F.IsEquivalence] :
    (preLeft F L R).IsEquivalence where

/-- The functor `(L, R) ⥤ (L ⋙ F, R ⋙ F)` -/
@[implicit_reducible, to_dual self, simps]
/--
Definition of `post` / `post` 的定义

English:
definition post
  signature: (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C)
  body: { left := X.left
      right := X.right
      hom := F.map X.hom }
  map f :=
    { left := f.left
      right := f.right
      w := by simp only [Functor.comp_map, ← F.map_comp, f.w] }

中文:
定义 post
  签名: (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C)
  定义体: { left := X.left
      right := X.right
      hom := F.map X.hom }
  map f :=
    { left := f.left
      right := f.right
      w := by simp only [Functor.comp_map, ← F.map_comp, f.w] }

Depends on / 依赖: F.map, F.map_comp, Functor, Functor.comp_map, X.hom, X.left, X.right, comp_map, f.left, f.right, map_comp
-/
def post (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) : Comma L R ⥤ Comma (L ⋙ F) (R ⋙ F) where
  obj X :=
    { left := X.left
      right := X.right
      hom := F.map X.hom }
  map f :=
    { left := f.left
      right := f.right
      w := by simp only [Functor.comp_map, ← F.map_comp, f.w] }

attribute [to_dual existing] post_obj_left
attribute [to_dual self] post_obj_hom

/-- `Comma.post` is a particular case of `Comma.map`, but with better definitional properties. -/
@[to_dual self]
/--
Definition of `postIso` / `postIso` 的定义

English:
definition postIso
  signature: (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C)
  body: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

@[to_dual self]

中文:
定义 postIso
  签名: (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C)
  定义体: NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

@[to_dual self]

Depends on / 依赖: leftUnitor, leftUnitor.hom, leftUnitor.inv
-/
def postIso (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) :
    post L R F ≅ map (F₁ := 𝟭 _) (F₂ := 𝟭 _) (L ⋙ F).leftUnitor.hom (R ⋙ F).leftUnitor.inv :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

@[to_dual self]
instance (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) : (post L R F).Faithful :=
  Functor.Faithful.of_iso (postIso L R F).symm

@[to_dual self]
instance (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) [F.Faithful] : (post L R F).Full :=
  Functor.Full.of_iso (postIso L R F).symm

@[to_dual self]
instance (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) [F.Full] : (post L R F).EssSurj :=
  Functor.essSurj_of_iso (postIso L R F).symm

/-- If `F` is an equivalence, then so is `post L R F`. -/
@[to_dual self]
/--
Instance `isEquivalence_post` / 实例 `isEquivalence_post`

English:
instance isEquivalence_post
  signature: (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) [F.IsEquivalence]

中文:
实例 isEquivalence_post
  签名: (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) [F.IsEquivalence]
-/
instance isEquivalence_post (L : A ⥤ T) (R : B ⥤ T) (F : T ⥤ C) [F.IsEquivalence] :
    (post L R F).IsEquivalence where

/-- The canonical functor from the product of two categories to the comma category of their
respective functors into `Discrete PUnit`. -/
@[implicit_reducible, simps]
/--
Definition of `fromProd` / `fromProd` 的定义

English:
definition fromProd
  signature: (L : A ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit)
  body: { left := X.1
      right := X.2
      hom := Discrete.eqToHom rfl }
  map {X} {Y} f :=
    { left := f.1
      right := f.2 }

中文:
定义 fromProd
  签名: (L : A ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit)
  定义体: { left := X.1
      right := X.2
      hom := Discrete.eqToHom rfl }
  map {X} {Y} f :=
    { left := f.1
      right := f.2 }

Depends on / 依赖: Discrete, Discrete.eqToHom, eqToHom
-/
def fromProd (L : A ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit) :
    A × B ⥤ Comma L R where
  obj X :=
    { left := X.1
      right := X.2
      hom := Discrete.eqToHom rfl }
  map {X} {Y} f :=
    { left := f.1
      right := f.2 }

set_option backward.defeqAttrib.useBackward true in
/-- Taking the comma category of two functors into `Discrete PUnit` results in something
is equivalent to their product. -/
@[simps!]
/--
Definition of `equivProd` / `equivProd` 的定义

English:
definition equivProd
  signature: (L : A ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit)
  body: (fst L R).prod' (snd L R)
  inverse := fromProd L R
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 equivProd
  签名: (L : A ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit)
  定义体: (fst L R).prod' (snd L R)
  inverse := fromProd L R
  unitIso := Iso.refl _
  counitIso := Iso.refl _
-/
def equivProd (L : A ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit) :
    Comma L R ≌ A × B where
  functor := (fst L R).prod' (snd L R)
  inverse := fromProd L R
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/--
Definition of `toPUnitIdEquiv` / `toPUnitIdEquiv` 的定义

English:
definition toPUnitIdEquiv
  signature: (L : A ⥤ Discrete PUnit) (R : Discrete PUnit ⥤ Discrete PUnit)
  body: (equivProd L _).trans (prod.rightUnitorEquivalence A)

@[simp]

中文:
定义 toPUnitIdEquiv
  签名: (L : A ⥤ Discrete PUnit) (R : Discrete PUnit ⥤ Discrete PUnit)
  定义体: (equivProd L _).trans (prod.rightUnitorEquivalence A)

@[simp]

Depends on / 依赖: equivProd, prod.rightUnitorEquivalence, rightUnitorEquivalence
-/
def toPUnitIdEquiv (L : A ⥤ Discrete PUnit) (R : Discrete PUnit ⥤ Discrete PUnit) :
    Comma L R ≌ A :=
  (equivProd L _).trans (prod.rightUnitorEquivalence A)

@[simp]
/--
theorem `toPUnitIdEquiv_functor_iso` / 定理 `toPUnitIdEquiv_functor_iso`

English:
theorem toPUnitIdEquiv_functor_iso
  statement: {L : A ⥤ Discrete PUnit}
  proof: rfl

中文:
定理 toPUnitIdEquiv_functor_iso
  结论: {L : A ⥤ Discrete PUnit}
  证明: rfl
-/
theorem toPUnitIdEquiv_functor_iso {L : A ⥤ Discrete PUnit}
    {R : Discrete PUnit ⥤ Discrete PUnit} :
    (toPUnitIdEquiv L R).functor = fst L R :=
  rfl

/--
Definition of `toIdPUnitEquiv` / `toIdPUnitEquiv` 的定义

English:
definition toIdPUnitEquiv
  signature: (L : Discrete PUnit ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit)
  body: (equivProd _ R).trans (prod.leftUnitorEquivalence B)

@[simp]

中文:
定义 toIdPUnitEquiv
  签名: (L : Discrete PUnit ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit)
  定义体: (equivProd _ R).trans (prod.leftUnitorEquivalence B)

@[simp]

Depends on / 依赖: equivProd, leftUnitorEquivalence, prod.leftUnitorEquivalence
-/
def toIdPUnitEquiv (L : Discrete PUnit ⥤ Discrete PUnit) (R : B ⥤ Discrete PUnit) :
    Comma L R ≌ B :=
  (equivProd _ R).trans (prod.leftUnitorEquivalence B)

@[simp]
/--
theorem `toIdPUnitEquiv_functor_iso` / 定理 `toIdPUnitEquiv_functor_iso`

English:
theorem toIdPUnitEquiv_functor_iso
  statement: {L : Discrete PUnit ⥤ Discrete PUnit}
  proof: rfl

中文:
定理 toIdPUnitEquiv_functor_iso
  结论: {L : Discrete PUnit ⥤ Discrete PUnit}
  证明: rfl

Depends on / 依赖: IsThin, Quiver, Quiver.IsThin
-/
theorem toIdPUnitEquiv_functor_iso {L : Discrete PUnit ⥤ Discrete PUnit}
    {R : B ⥤ Discrete PUnit} :
    (toIdPUnitEquiv L R).functor = snd L R :=
  rfl

end

section Opposite

open Opposite

set_option backward.defeqAttrib.useBackward true in
/-- The canonical functor from `Comma L R` to `(Comma R.op L.op)ᵒᵖ`. -/
@[implicit_reducible, simps]
/--
Definition of `opFunctor` / `opFunctor` 的定义

English:
definition opFunctor
  signature: : Comma L R ⥤ (Comma R.op L.op)ᵒᵖ where
  body: ⟨op X.right, op X.left, op X.hom⟩
  map f := ⟨op f.right, op f.left, Quiver.Hom.unop_inj (by simp)⟩

中文:
定义 opFunctor
  签名: : Comma L R ⥤ (Comma R.op L.op)ᵒᵖ where
  定义体: ⟨op X.right, op X.left, op X.hom⟩
  map f := ⟨op f.right, op f.left, Quiver.Hom.unop_inj (by simp)⟩

Depends on / 依赖: X.hom, X.left, X.right
-/
def opFunctor : Comma L R ⥤ (Comma R.op L.op)ᵒᵖ where
  obj X := ⟨op X.right, op X.left, op X.hom⟩
  map f := ⟨op f.right, op f.left, Quiver.Hom.unop_inj (by simp)⟩

/-- Composing the `leftOp` of `opFunctor L R` with `fst L.op R.op` is naturally isomorphic
to `snd L R`. -/
@[simps!]
/--
Definition of `opFunctorCompFst` / `opFunctorCompFst` 的定义

English:
definition opFunctorCompFst
  signature: : (opFunctor L R).leftOp ⋙ fst _ _ ≅ (snd _ _).op
  body: Iso.refl _

中文:
定义 opFunctorCompFst
  签名: : (opFunctor L R).leftOp ⋙ fst _ _ ≅ (snd _ _).op
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def opFunctorCompFst : (opFunctor L R).leftOp ⋙ fst _ _ ≅ (snd _ _).op :=
  Iso.refl _

/-- Composing the `leftOp` of `opFunctor L R` with `snd L.op R.op` is naturally isomorphic
to `fst L R`. -/
@[simps!]
/--
Definition of `opFunctorCompSnd` / `opFunctorCompSnd` 的定义

English:
definition opFunctorCompSnd
  signature: : (opFunctor L R).leftOp ⋙ snd _ _ ≅ (fst _ _).op
  body: Iso.refl _

中文:
定义 opFunctorCompSnd
  签名: : (opFunctor L R).leftOp ⋙ snd _ _ ≅ (fst _ _).op
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def opFunctorCompSnd : (opFunctor L R).leftOp ⋙ snd _ _ ≅ (fst _ _).op :=
  Iso.refl _

/-- The canonical functor from `Comma L.op R.op` to `(Comma R L)ᵒᵖ`. -/
@[implicit_reducible, simps]
/--
Definition of `unopFunctor` / `unopFunctor` 的定义

English:
definition unopFunctor
  signature: : Comma L.op R.op ⥤ (Comma R L)ᵒᵖ where
  body: ⟨X.right.unop, X.left.unop, X.hom.unop⟩
  map f := ⟨f.right.unop, f.left.unop, Quiver.Hom.op_inj (by simpa using! f.w.symm)⟩

中文:
定义 unopFunctor
  签名: : Comma L.op R.op ⥤ (Comma R L)ᵒᵖ where
  定义体: ⟨X.right.unop, X.left.unop, X.hom.unop⟩
  map f := ⟨f.right.unop, f.left.unop, Quiver.Hom.op_inj (by simpa using! f.w.symm)⟩

Depends on / 依赖: X.hom.unop, X.left.unop, X.right.unop
-/
def unopFunctor : Comma L.op R.op ⥤ (Comma R L)ᵒᵖ where
  obj X := ⟨X.right.unop, X.left.unop, X.hom.unop⟩
  map f := ⟨f.right.unop, f.left.unop, Quiver.Hom.op_inj (by simpa using! f.w.symm)⟩

/-- Composing `unopFunctor L R` with `(fst L R).op` is isomorphic to `snd L.op R.op`. -/
@[simps!]
/--
Definition of `unopFunctorCompFst` / `unopFunctorCompFst` 的定义

English:
definition unopFunctorCompFst
  signature: : unopFunctor L R ⋙ (fst _ _).op ≅ snd _ _
  body: Iso.refl _

中文:
定义 unopFunctorCompFst
  签名: : unopFunctor L R ⋙ (fst _ _).op ≅ snd _ _
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def unopFunctorCompFst : unopFunctor L R ⋙ (fst _ _).op ≅ snd _ _ :=
  Iso.refl _

/-- Composing `unopFunctor L R` with `(snd L R).op` is isomorphic to `fst L.op R.op`. -/
@[simps!]
/--
Definition of `unopFunctorCompSnd` / `unopFunctorCompSnd` 的定义

English:
definition unopFunctorCompSnd
  signature: : unopFunctor L R ⋙ (snd _ _).op ≅ fst _ _
  body: Iso.refl _

中文:
定义 unopFunctorCompSnd
  签名: : unopFunctor L R ⋙ (snd _ _).op ≅ fst _ _
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def unopFunctorCompSnd : unopFunctor L R ⋙ (snd _ _).op ≅ fst _ _ :=
  Iso.refl _

/-- The canonical equivalence between `Comma L R` and `(Comma R.op L.op)ᵒᵖ`. -/
@[simps]
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: : Comma L R ≌ (Comma R.op L.op)ᵒᵖ where
  body: opFunctor L R
  inverse := (unopFunctor R L).leftOp
  unitIso := NatIso.ofComponents (fun X => Iso.refl _)
  counitIso := NatIso.ofComponents (fun X => Iso.refl _)

中文:
定义 opEquiv
  签名: : Comma L R ≌ (Comma R.op L.op)ᵒᵖ where
  定义体: opFunctor L R
  inverse := (unopFunctor R L).leftOp
  unitIso := NatIso.ofComponents (fun X => Iso.refl _)
  counitIso := NatIso.ofComponents (fun X => Iso.refl _)

Depends on / 依赖: opFunctor
-/
def opEquiv : Comma L R ≌ (Comma R.op L.op)ᵒᵖ where
  functor := opFunctor L R
  inverse := (unopFunctor R L).leftOp
  unitIso := NatIso.ofComponents (fun X => Iso.refl _)
  counitIso := NatIso.ofComponents (fun X => Iso.refl _)

end Opposite

end Comma

end CategoryTheory
