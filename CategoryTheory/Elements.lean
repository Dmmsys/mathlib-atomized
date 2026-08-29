/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# The category of elements

This file defines the category of elements, also known as (a special case of) the Grothendieck
construction.

Given a functor `F : C ⥤ Type`, an object of `F.Elements` is a pair `(X : C, x : F.obj X)`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`.

## Implementation notes

This construction is equivalent to a special case of a comma construction, so this is mostly just a
more convenient API. We prove the equivalence in
`CategoryTheory.CategoryOfElements.structuredArrowEquivalence`.

## References
* [Emily Riehl, *Category Theory in Context*, Section 2.4][riehl2017]
* <https://en.wikipedia.org/wiki/Category_of_elements>
* <https://ncatlab.org/nlab/show/category+of+elements>

## Tags
category of elements, Grothendieck construction, comma category
-/

@[expose] public section


namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C]

/--
Definition of `Functor.Elements` / `Functor.Elements` 的定义

English:
definition Functor.Elements
  signature: (F : C ⥤ Type w)
  body: Σ c : C, F.obj c

中文:
定义 函子.Elements
  签名: (F : C ⥤ 类型 w)
  定义体: Σ c : C, F.obj c

Depends on / 依赖: F.obj
-/
def Functor.Elements (F : C ⥤ Type w) :=
  Σ c : C, F.obj c

/--
Definition of `Functor.elementsMk` / `Functor.elementsMk` 的定义

English:
abbreviation Functor.elementsMk
  signature: (F : C ⥤ Type w) (X : C) (x : F.obj X)
  body: ⟨X, x⟩

中文:
缩写 函子.elementsMk
  签名: (F : C ⥤ 类型 w) (X : C) (x : F.obj X)
  定义体: ⟨X, x⟩
-/
abbrev Functor.elementsMk (F : C ⥤ Type w) (X : C) (x : F.obj X) : F.Elements := ⟨X, x⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Functor.Elements.ext` / 引理 `Functor.Elements.ext`

English:
lemma Functor.Elements.ext
  statement: {F : C ⥤ Type w} (x y : F.Elements) (h₁ : x.fst = y.fst)
  proof: by
  cases x
  cases y
  cases h₁
  simp_all

中文:
引理 函子.Elements.ext
  结论: {F : C ⥤ 类型 w} (x y : F.Elements) (h₁ : x.fst = y.fst)
  证明: by
  cases x
  cases y
  cases h₁
  simp_all
-/
lemma Functor.Elements.ext {F : C ⥤ Type w} (x y : F.Elements) (h₁ : x.fst = y.fst)
    (h₂ : F.map (eqToHom h₁) x.snd = y.snd) : x = y := by
  cases x
  cases y
  cases h₁
  simp_all

/--
Instance `categoryOfElements` / 实例 `categoryOfElements`

English:
instance categoryOfElements
  signature: (F : C ⥤ Type w)
  body: { f : p.1 ⟶ q.1 // (F.map f) p.2 = q.2 }
  id p := ⟨𝟙 p.1, by simp⟩
  comp {X Y Z} f g := ⟨f.val ≫ g.val, by simp [f.2, g.2]⟩

中文:
实例 categoryOfElements
  签名: (F : C ⥤ 类型 w)
  定义体: { f : p.1 ⟶ q.1 // (F.map f) p.2 = q.2 }
  id p := ⟨𝟙 p.1, by simp⟩
  comp {X Y Z} f g := ⟨f.val ≫ g.val, by simp [f.2, g.2]⟩

Depends on / 依赖: F.map
-/
instance categoryOfElements (F : C ⥤ Type w) : Category.{v} F.Elements where
  Hom p q := { f : p.1 ⟶ q.1 // (F.map f) p.2 = q.2 }
  id p := ⟨𝟙 p.1, by simp⟩
  comp {X Y Z} f g := ⟨f.val ≫ g.val, by simp [f.2, g.2]⟩

/-- Natural transformations are mapped to functors between categories of elements. -/
@[simps]
/--
Definition of `NatTrans.mapElements` / `NatTrans.mapElements` 的定义

English:
definition NatTrans.mapElements
  signature: {F G : C ⥤ Type w} (φ : F ⟶ G)
  body: fun ⟨X, x⟩ => ⟨_, φ.app X x⟩
  map {p q} := fun ⟨f, h⟩ => ⟨f, by have hb := φ.naturality_apply f p.2; cat_disch⟩

中文:
定义 自然变换.mapElements
  签名: {F G : C ⥤ 类型 w} (φ : F ⟶ G)
  定义体: fun ⟨X, x⟩ => ⟨_, φ.app X x⟩
  map {p q} := fun ⟨f, h⟩ => ⟨f, by have hb := φ.naturality_apply f p.2; cat_disch⟩
-/
def NatTrans.mapElements {F G : C ⥤ Type w} (φ : F ⟶ G) : F.Elements ⥤ G.Elements where
  obj := fun ⟨X, x⟩ => ⟨_, φ.app X x⟩
  map {p q} := fun ⟨f, h⟩ => ⟨f, by have hb := φ.naturality_apply f p.2; cat_disch⟩

/-- The functor mapping functors `C ⥤ Type w` to their category of elements -/
@[simps]
/--
Definition of `Functor.elementsFunctor` / `Functor.elementsFunctor` 的定义

English:
definition Functor.elementsFunctor
  signature: : (C ⥤ Type w) ⥤ Cat where
  body: Cat.of F.Elements
  map n := (NatTrans.mapElements n).toCatHom

中文:
定义 函子.elementsFunctor
  签名: : (C ⥤ 类型 w) ⥤ Cat where
  定义体: Cat.of F.Elements
  map n := (NatTrans.mapElements n).toCatHom

Depends on / 依赖: Cat.of, Elements, F.Elements
-/
def Functor.elementsFunctor : (C ⥤ Type w) ⥤ Cat where
  obj F := Cat.of F.Elements
  map n := (NatTrans.mapElements n).toCatHom

namespace CategoryOfElements

/-- Constructor for morphisms in the category of elements of a functor to types. -/
@[simps]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {F : C ⥤ Type w} (x y : F.Elements) (f : x.1 ⟶ y.1) (hf : F.map f x.snd = y.snd)
  body: ⟨f, hf⟩

@[ext]

中文:
定义 homMk
  签名: {F : C ⥤ 类型 w} (x y : F.Elements) (f : x.1 ⟶ y.1) (hf : F.map f x.snd = y.snd)
  定义体: ⟨f, hf⟩

@[ext]
-/
def homMk {F : C ⥤ Type w} (x y : F.Elements) (f : x.1 ⟶ y.1) (hf : F.map f x.snd = y.snd) :
    x ⟶ y :=
  ⟨f, hf⟩

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (F : C ⥤ Type w) {x y : F.Elements} (f g : x ⟶ y) (w : f.val = g.val)
  statement: f = g
  proof: Subtype.ext w

@[simp]

中文:
定理 ext
  条件: (F : C ⥤ 类型 w) {x y : F.Elements} (f g : x ⟶ y) (w : f.val = g.val)
  结论: f = g
  证明: Subtype.ext w

@[simp]

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem ext (F : C ⥤ Type w) {x y : F.Elements} (f g : x ⟶ y) (w : f.val = g.val) : f = g :=
  Subtype.ext w

@[simp]
/--
theorem `comp_val` / 定理 `comp_val`

English:
theorem comp_val
  given: {F : C ⥤ Type w} {p q r : F.Elements} {f : p ⟶ q} {g : q ⟶ r}
  proof: rfl

@[simp]

中文:
定理 comp_val
  条件: {F : C ⥤ 类型 w} {p q r : F.Elements} {f : p ⟶ q} {g : q ⟶ r}
  证明: rfl

@[simp]
-/
theorem comp_val {F : C ⥤ Type w} {p q r : F.Elements} {f : p ⟶ q} {g : q ⟶ r} :
    (f ≫ g).val = f.val ≫ g.val :=
  rfl

@[simp]
/--
theorem `id_val` / 定理 `id_val`

English:
theorem id_val
  given: {F : C ⥤ Type w} {p : F.Elements}
  statement: (𝟙 p : p ⟶ p).val = 𝟙 p.1
  proof: rfl

@[simp]

中文:
定理 id_val
  条件: {F : C ⥤ 类型 w} {p : F.Elements}
  结论: (𝟙 p : p ⟶ p).val = 𝟙 p.1
  证明: rfl

@[simp]
-/
theorem id_val {F : C ⥤ Type w} {p : F.Elements} : (𝟙 p : p ⟶ p).val = 𝟙 p.1 :=
  rfl

@[simp]
/--
theorem `map_snd` / 定理 `map_snd`

English:
theorem map_snd
  given: {F : C ⥤ Type w} {p q : F.Elements} (f : p ⟶ q)
  statement: (F.map f.val) p.2 = q.2
  proof: f.property

中文:
定理 map_snd
  条件: {F : C ⥤ 类型 w} {p q : F.Elements} (f : p ⟶ q)
  结论: (F.map f.val) p.2 = q.2
  证明: f.property

Depends on / 依赖: f.property, property
-/
theorem map_snd {F : C ⥤ Type w} {p q : F.Elements} (f : p ⟶ q) : (F.map f.val) p.2 = q.2 :=
  f.property

/-- Constructor for isomorphisms in the category of elements of a functor to types. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {F : C ⥤ Type w} (x y : F.Elements) (e : x.1 ≅ y.1)
  body: homMk x y e.hom he
  inv := homMk y x e.inv (by rw [← he, Functor.map_hom_inv'_apply])

中文:
定义 isoMk
  签名: {F : C ⥤ 类型 w} (x y : F.Elements) (e : x.1 ≅ y.1)
  定义体: homMk x y e.hom he
  inv := homMk y x e.inv (by rw [← he, Functor.map_hom_inv'_apply])

Depends on / 依赖: e.hom
-/
def isoMk {F : C ⥤ Type w} (x y : F.Elements) (e : x.1 ≅ y.1)
    (he : F.map e.hom x.snd = y.snd) : x ≅ y where
  hom := homMk x y e.hom he
  inv := homMk y x e.inv (by rw [← he, Functor.map_hom_inv'_apply])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallySmall.{w}
  signature: C] (F
  body: by
    rintro ⟨X, _⟩ ⟨Y, y⟩
    exact small_of_injective (f := fun g => g.val) (by cat_disch)

中文:
实例 [LocallySmall.{w}
  签名: C] (F
  定义体: by
    rintro ⟨X, _⟩ ⟨Y, y⟩
    exact small_of_injective (f := fun g => g.val) (by cat_disch)

Depends on / 依赖: cat_disch, g.val, small_of_injective
-/
instance [LocallySmall.{w} C] (F : C ⥤ Type w) : LocallySmall.{w} F.Elements where
  hom_small := by
    rintro ⟨X, _⟩ ⟨Y, y⟩
    exact small_of_injective (f := fun g => g.val) (by cat_disch)

end CategoryOfElements

/--
Instance `groupoidOfElements` / 实例 `groupoidOfElements`

English:
instance groupoidOfElements
  signature: {G : Type u} [Groupoid.{v} G] (F : G ⥤ Type w)
  body: ⟨Groupoid.inv f.val,
      calc
        F.map (Groupoid.inv f.val) q.2 = F.map (Groupoid.inv f.val) (F.map f.val p.2) := by rw [f.2]
        _ = (F.map f.val ≫ F.map (Groupoid.inv f.val)) p.2 := rfl
        _ = p.2 := by
          rw [← F.map_comp]
          simp
        ⟩
  inv_comp _ := by
    ext

中文:
实例 groupoidOfElements
  签名: {G : 类型u} [群胚.{v} G] (F : G ⥤ 类型 w)
  定义体: ⟨Groupoid.inv f.val,
      calc
        F.map (Groupoid.inv f.val) q.2 = F.map (Groupoid.inv f.val) (F.map f.val p.2) := by rw [f.2]
        _ = (F.map f.val ≫ F.map (Groupoid.inv f.val)) p.2 := rfl
        _ = p.2 := by
          rw [← F.map_comp]
          simp
        ⟩
  inv_comp _ := by
    ext

Depends on / 依赖: F.map, F.map_comp, Groupoid, Groupoid.inv, comp_inv, f.val, inv_comp, map_comp
-/
instance groupoidOfElements {G : Type u} [Groupoid.{v} G] (F : G ⥤ Type w) :
    Groupoid F.Elements where
  inv {p q} f :=
    ⟨Groupoid.inv f.val,
      calc
        F.map (Groupoid.inv f.val) q.2 = F.map (Groupoid.inv f.val) (F.map f.val p.2) := by rw [f.2]
        _ = (F.map f.val ≫ F.map (Groupoid.inv f.val)) p.2 := rfl
        _ = p.2 := by
          rw [← F.map_comp]
          simp
        ⟩
  inv_comp _ := by
    ext
    simp
  comp_inv _ := by
    ext
    simp

namespace CategoryOfElements

variable (F : C ⥤ Type w)

/-- The functor out of the category of elements which forgets the element. -/
@[simps]
/--
Definition of `π` / `π` 的定义

English:
definition π
  signature: : F.Elements ⥤ C where
  body: X.1
  map f := f.val

中文:
定义 π
  签名: : F.Elements ⥤ C where
  定义体: X.1
  map f := f.val
-/
def π : F.Elements ⥤ C where
  obj X := X.1
  map f := f.val

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (π F).Faithful

中文:
实例 :
  签名: (π F).忠实
-/
instance : (π F).Faithful where

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (π F).ReflectsIsomorphisms
  body: by
    refine ⟨⟨(inv ((π F).map f) :), ?_⟩, ?_, ?_⟩
    · simp only [← map_snd f, ← Functor.map_comp_apply,
        π_obj, π_map, IsIso.hom_inv_id, Functor.map_id_apply]
    · cat_disch
    · cat_disch

中文:
实例 :
  签名: (π F).反映同构
  定义体: by
    refine ⟨⟨(inv ((π F).map f) :), ?_⟩, ?_, ?_⟩
    · simp only [← map_snd f, ← Functor.map_comp_apply,
        π_obj, π_map, IsIso.hom_inv_id, Functor.map_id_apply]
    · cat_disch
    · cat_disch

Depends on / 依赖: Functor, Functor.map_comp_apply, Functor.map_id_apply, IsIso.hom_inv_id, cat_disch, hom_inv_id, map_comp_apply, map_id_apply, map_snd
-/
instance : (π F).ReflectsIsomorphisms where
  reflects f h := by
    refine ⟨⟨(inv ((π F).map f) :), ?_⟩, ?_, ?_⟩
    · simp only [← map_snd f, ← Functor.map_comp_apply,
        π_obj, π_map, IsIso.hom_inv_id, Functor.map_id_apply]
    · cat_disch
    · cat_disch

/-- A natural transformation between functors induces a functor between the categories of elements.
-/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂)
  body: ⟨t.1, α.app t.1 t.2⟩
  map {t₁ t₂} k := ⟨k.1, by simpa [map_snd] using (NatTrans.naturality_apply α k.1 t₁.2).symm⟩

@[simp]

中文:
定义 map
  签名: {F₁ F₂ : C ⥤ 类型 w} (α : F₁ ⟶ F₂)
  定义体: ⟨t.1, α.app t.1 t.2⟩
  map {t₁ t₂} k := ⟨k.1, by simpa [map_snd] using (NatTrans.naturality_apply α k.1 t₁.2).symm⟩

@[simp]
-/
def map {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : F₁.Elements ⥤ F₂.Elements where
  obj t := ⟨t.1, α.app t.1 t.2⟩
  map {t₁ t₂} k := ⟨k.1, by simpa [map_snd] using (NatTrans.naturality_apply α k.1 t₁.2).symm⟩

@[simp]
/--
theorem `map_π` / 定理 `map_π`

English:
theorem map_π
  given: {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂)
  statement: map α ⋙ π F₂ = π F₁
  proof: rfl

中文:
定理 map_π
  条件: {F₁ F₂ : C ⥤ 类型 w} (α : F₁ ⟶ F₂)
  结论: map α ⋙ π F₂ = π F₁
  证明: rfl
-/
theorem map_π {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : map α ⋙ π F₂ = π F₁ :=
  rfl

/--
Definition of `toStructuredArrow` / `toStructuredArrow` 的定义

English:
definition toStructuredArrow
  signature: : F.Elements ⥤ StructuredArrow PUnit F where
  body: StructuredArrow.mk ↾fun _ => X.2
  map {X Y} f := StructuredArrow.homMk f.val (by ext; simp [f.2])

@[simp]

中文:
定义 toStructuredArrow
  签名: : F.Elements ⥤ 结构化箭头 命题单元 F where
  定义体: StructuredArrow.mk ↾fun _ => X.2
  map {X Y} f := StructuredArrow.homMk f.val (by ext; simp [f.2])

@[simp]

Depends on / 依赖: StructuredArrow, StructuredArrow.mk
-/
def toStructuredArrow : F.Elements ⥤ StructuredArrow PUnit F where
obj X := StructuredArrow.mk ↾fun _ => X.2
  map {X Y} f := StructuredArrow.homMk f.val (by ext; simp [f.2])

@[simp]
/--
theorem `toStructuredArrow_obj` / 定理 `toStructuredArrow_obj`

English:
theorem toStructuredArrow_obj
  given: (X)
  proof: rfl

@[simp]

中文:
定理 toStructuredArrow_obj
  条件: (X)
  证明: rfl

@[simp]
-/
theorem toStructuredArrow_obj (X) :
    (toStructuredArrow F).obj X =
      { left := ⟨⟨⟩⟩
        right := X.1
        hom := ↾fun _ => X.2 } :=
  rfl

@[simp]
/--
theorem `to_comma_map_right` / 定理 `to_comma_map_right`

English:
theorem to_comma_map_right
  given: {X Y} (f : X ⟶ Y)
  statement: ((toStructuredArrow F).map f).right = f.val
  proof: rfl

中文:
定理 to_comma_map_right
  条件: {X Y} (f : X ⟶ Y)
  结论: ((toStructuredArrow F).map f).right = f.val
  证明: rfl
-/
theorem to_comma_map_right {X Y} (f : X ⟶ Y) : ((toStructuredArrow F).map f).right = f.val :=
  rfl

/--
Definition of `fromStructuredArrow` / `fromStructuredArrow` 的定义

English:
definition fromStructuredArrow
  signature: : StructuredArrow PUnit F ⥤ F.Elements where
  body: Functor.elementsMk _ X.right (X.hom .unit)
  map f := ⟨f.right, by simp [ConcreteCategory.congr_hom f.w.symm .unit]; rfl⟩

@[simp]

中文:
定义 fromStructuredArrow
  签名: : 结构化箭头 命题单元 F ⥤ F.Elements where
  定义体: Functor.elementsMk _ X.right (X.hom .unit)
  map f := ⟨f.right, by simp [ConcreteCategory.congr_hom f.w.symm .unit]; rfl⟩

@[simp]

Depends on / 依赖: Functor, Functor.elementsMk, X.hom, X.right, elementsMk
-/
def fromStructuredArrow : StructuredArrow PUnit F ⥤ F.Elements where
  obj X := Functor.elementsMk _ X.right (X.hom .unit)
  map f := ⟨f.right, by simp [ConcreteCategory.congr_hom f.w.symm .unit]; rfl⟩

@[simp]
/--
theorem `fromStructuredArrow_obj` / 定理 `fromStructuredArrow_obj`

English:
theorem fromStructuredArrow_obj
  given: (X)
  statement: (fromStructuredArrow F).obj X = ⟨X.right, X.hom PUnit.unit⟩
  proof: rfl

@[simp]

中文:
定理 fromStructuredArrow_obj
  条件: (X)
  结论: (fromStructuredArrow F).obj X = ⟨X.right, X.hom 命题单元.unit⟩
  证明: rfl

@[simp]
-/
theorem fromStructuredArrow_obj (X) : (fromStructuredArrow F).obj X = ⟨X.right, X.hom PUnit.unit⟩ :=
  rfl

@[simp]
/--
theorem `fromStructuredArrow_map` / 定理 `fromStructuredArrow_map`

English:
theorem fromStructuredArrow_map
  given: {X Y} (f : X ⟶ Y)
  proof: rfl

中文:
定理 fromStructuredArrow_map
  条件: {X Y} (f : X ⟶ Y)
  证明: rfl
-/
theorem fromStructuredArrow_map {X Y} (f : X ⟶ Y) :
    (fromStructuredArrow F).map f =
      ⟨f.right, by simp [ConcreteCategory.congr_hom f.w.symm PUnit.unit]; rfl⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence between the category of elements `F.Elements`
and the comma category `(*, F)`. -/
@[simps]
/--
Definition of `structuredArrowEquivalence` / `structuredArrowEquivalence` 的定义

English:
definition structuredArrowEquivalence
  signature: : F.Elements ≌ StructuredArrow PUnit F where
  body: toStructuredArrow F
  inverse := fromStructuredArrow F
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 structuredArrowEquivalence
  签名: : F.Elements ≌ 结构化箭头 命题单元 F where
  定义体: toStructuredArrow F
  inverse := fromStructuredArrow F
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: toStructuredArrow
-/
def structuredArrowEquivalence : F.Elements ≌ StructuredArrow PUnit F where
  functor := toStructuredArrow F
  inverse := fromStructuredArrow F
  unitIso := Iso.refl _
  counitIso := Iso.refl _

open Opposite

set_option backward.isDefEq.respectTransparency.types false in
/-- The forward direction of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)`,
given by `CategoryTheory.yonedaEquiv`.
-/
@[simps]
/--
Definition of `toCostructuredArrow` / `toCostructuredArrow` 的定义

English:
definition toCostructuredArrow
  signature: (F : Cᵒᵖ ⥤ Type v)
  body: CostructuredArrow.mk (yonedaEquiv.symm (unop X).2)
  map f :=
    CostructuredArrow.homMk f.unop.val.unop (by
      ext Z y
      simp [yonedaEquiv])

中文:
定义 toCostructuredArrow
  签名: (F : Cᵒᵖ ⥤ 类型v)
  定义体: CostructuredArrow.mk (yonedaEquiv.symm (unop X).2)
  map f :=
    CostructuredArrow.homMk f.unop.val.unop (by
      ext Z y
      simp [yonedaEquiv])

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, yonedaEquiv, yonedaEquiv.symm
-/
def toCostructuredArrow (F : Cᵒᵖ ⥤ Type v) : F.Elementsᵒᵖ ⥤ CostructuredArrow yoneda F where
  obj X := CostructuredArrow.mk (yonedaEquiv.symm (unop X).2)
  map f :=
    CostructuredArrow.homMk f.unop.val.unop (by
      ext Z y
      simp [yonedaEquiv])

set_option backward.defeqAttrib.useBackward true in
/-- The reverse direction of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)`,
given by `CategoryTheory.yonedaEquiv`.
-/
@[simps]
/--
Definition of `fromCostructuredArrow` / `fromCostructuredArrow` 的定义

English:
definition fromCostructuredArrow
  signature: (F : Cᵒᵖ ⥤ Type v)
  body: ⟨op (unop X).1, yonedaEquiv.1 (unop X).3⟩
  map {X Y} f := ⟨f.unop.1.op, by simp [yonedaEquiv_naturality]⟩

@[simp]

中文:
定义 fromCostructuredArrow
  签名: (F : Cᵒᵖ ⥤ 类型v)
  定义体: ⟨op (unop X).1, yonedaEquiv.1 (unop X).3⟩
  map {X Y} f := ⟨f.unop.1.op, by simp [yonedaEquiv_naturality]⟩

@[simp]

Depends on / 依赖: yonedaEquiv
-/
def fromCostructuredArrow (F : Cᵒᵖ ⥤ Type v) :
    (CostructuredArrow yoneda F)ᵒᵖ ⥤ F.Elements where
  obj X := ⟨op (unop X).1, yonedaEquiv.1 (unop X).3⟩
  map {X Y} f := ⟨f.unop.1.op, by simp [yonedaEquiv_naturality]⟩

@[simp]
/--
theorem `fromCostructuredArrow_obj_mk` / 定理 `fromCostructuredArrow_obj_mk`

English:
theorem fromCostructuredArrow_obj_mk
  given: (F : Cᵒᵖ ⥤ Type v) {X : C} (f : yoneda.obj X ⟶ F)
  proof: rfl

中文:
定理 fromCostructuredArrow_obj_mk
  条件: (F : Cᵒᵖ ⥤ 类型v) {X : C} (f : yoneda.obj X ⟶ F)
  证明: rfl
-/
theorem fromCostructuredArrow_obj_mk (F : Cᵒᵖ ⥤ Type v) {X : C} (f : yoneda.obj X ⟶ F) :
    (fromCostructuredArrow F).obj (op (CostructuredArrow.mk f)) = ⟨op X, yonedaEquiv.1 f⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)` given by yoneda lemma. -/
@[simps]
/--
Definition of `costructuredArrowYonedaEquivalence` / `costructuredArrowYonedaEquivalence` 的定义

English:
definition costructuredArrowYonedaEquivalence
  signature: (F : Cᵒᵖ ⥤ Type v)
  body: toCostructuredArrow F
  inverse := (fromCostructuredArrow F).rightOp
  unitIso :=
    NatIso.ofComponents
      (fun X => Iso.op (CategoryOfElements.isoMk _ _ (Iso.refl _) (by simp; rfl))) (by
        rintro ⟨x⟩ ⟨y⟩ ⟨f : y ⟶ x⟩
        exact Quiver.Hom.unop_inj (by ext; simp))
  counitIso := NatIso.

中文:
定义 costructuredArrowYonedaEquivalence
  签名: (F : Cᵒᵖ ⥤ 类型v)
  定义体: toCostructuredArrow F
  inverse := (fromCostructuredArrow F).rightOp
  unitIso :=
    NatIso.ofComponents
      (fun X => Iso.op (CategoryOfElements.isoMk _ _ (Iso.refl _) (by simp; rfl))) (by
        rintro ⟨x⟩ ⟨y⟩ ⟨f : y ⟶ x⟩
        exact Quiver.Hom.unop_inj (by ext; simp))
  counitIso := NatIso.

Depends on / 依赖: toCostructuredArrow
-/
def costructuredArrowYonedaEquivalence (F : Cᵒᵖ ⥤ Type v) :
    F.Elementsᵒᵖ ≌ CostructuredArrow yoneda F where
  functor := toCostructuredArrow F
  inverse := (fromCostructuredArrow F).rightOp
  unitIso :=
    NatIso.ofComponents
      (fun X => Iso.op (CategoryOfElements.isoMk _ _ (Iso.refl _) (by simp; rfl))) (by
        rintro ⟨x⟩ ⟨y⟩ ⟨f : y ⟶ x⟩
        exact Quiver.Hom.unop_inj (by ext; simp))
  counitIso := NatIso.ofComponents (fun X => CostructuredArrow.isoMk (Iso.refl _) (by
    dsimp
    simpa only [Functor.map_id, Category.id_comp] using!
      (yonedaEquiv.symm_apply_apply X.hom).symm))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `costructuredArrow_yoneda_equivalence_naturality` / 定理 `costructuredArrow_yoneda_equivalence_naturality`

English:
theorem costructuredArrow_yoneda_equivalence_naturality
  given: {F₁ F₂ : Cᵒᵖ ⥤ Type v} (α : F₁ ⟶ F₂)
  proof: by
  fapply Functor.ext
  · intro X
    simp only [CostructuredArrow.map_mk, toCostructuredArrow_obj, Functor.op_obj,
      Functor.comp_obj]
    congr
    ext _ f
    exact (α.naturality_apply f.op (unop X).snd).symm
  · simp

中文:
定理 costructuredArrow_yoneda_equivalence_naturality
  条件: {F₁ F₂ : Cᵒᵖ ⥤ 类型v} (α : F₁ ⟶ F₂)
  证明: by
  fapply Functor.ext
  · intro X
    simp only [CostructuredArrow.map_mk, toCostructuredArrow_obj, Functor.op_obj,
      Functor.comp_obj]
    congr
    ext _ f
    exact (α.naturality_apply f.op (unop X).snd).symm
  · simp

Depends on / 依赖: CostructuredArrow, CostructuredArrow.map_mk, Functor, Functor.comp_obj, Functor.ext, Functor.op_obj, comp_obj, f.op, fapply, map_mk, naturality_apply, op_obj, toCostructuredArrow_obj
-/
theorem costructuredArrow_yoneda_equivalence_naturality {F₁ F₂ : Cᵒᵖ ⥤ Type v} (α : F₁ ⟶ F₂) :
    (map α).op ⋙ toCostructuredArrow F₂ = toCostructuredArrow F₁ ⋙ CostructuredArrow.map α := by
  fapply Functor.ext
  · intro X
    simp only [CostructuredArrow.map_mk, toCostructuredArrow_obj, Functor.op_obj,
      Functor.comp_obj]
    congr
    ext _ f
    exact (α.naturality_apply f.op (unop X).snd).symm
  · simp

/-- The equivalence `F.elementsᵒᵖ ≌ (yoneda, F)` is compatible with the forgetful functors. -/
@[simps!]
/--
Definition of `costructuredArrowYonedaEquivalenceFunctorProj` / `costructuredArrowYonedaEquivalenceFunctorProj` 的定义

English:
definition costructuredArrowYonedaEquivalenceFunctorProj
  signature: (F : Cᵒᵖ ⥤ Type v)
  body: Iso.refl _

中文:
定义 costructuredArrowYonedaEquivalenceFunctorProj
  签名: (F : Cᵒᵖ ⥤ 类型v)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def costructuredArrowYonedaEquivalenceFunctorProj (F : Cᵒᵖ ⥤ Type v) :
    (costructuredArrowYonedaEquivalence F).functor ⋙ CostructuredArrow.proj _ _ ≅ (π F).leftOp :=
  Iso.refl _

/-- The equivalence `F.elementsᵒᵖ ≌ (yoneda, F)` is compatible with the forgetful functors. -/
@[simps!]
/--
Definition of `costructuredArrowYonedaEquivalenceInverseπ` / `costructuredArrowYonedaEquivalenceInverseπ` 的定义

English:
definition costructuredArrowYonedaEquivalenceInverseπ
  signature: (F : Cᵒᵖ ⥤ Type v)
  body: Iso.refl _

中文:
定义 costructuredArrowYonedaEquivalenceInverseπ
  签名: (F : Cᵒᵖ ⥤ 类型v)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def costructuredArrowYonedaEquivalenceInverseπ (F : Cᵒᵖ ⥤ Type v) :
    (costructuredArrowYonedaEquivalence F).inverse ⋙ (π F).leftOp ≅ CostructuredArrow.proj _ _ :=
  Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The opposite of the category of elements of a presheaf of types
is equivalent to a category of costructured arrows for the Yoneda embedding functor. -/
@[simps]
/--
Definition of `costructuredArrowULiftYonedaEquivalence` / `costructuredArrowULiftYonedaEquivalence` 的定义

English:
definition costructuredArrowULiftYonedaEquivalence
  signature: (F : Cᵒᵖ ⥤ Type (max w v))
  body: { obj x := CostructuredArrow.mk (uliftYonedaEquiv.{w}.symm x.unop.2)
      map f := CostructuredArrow.homMk f.1.1.unop (by
        dsimp
        rw [← uliftYonedaEquiv_symm_map]; rw [map_snd]) }
  inverse :=
    { obj X := op (F.elementsMk _ (uliftYonedaEquiv.{w} X.hom))
      map f := (homMk _ _ f.

中文:
定义 costructuredArrowULiftYonedaEquivalence
  签名: (F : Cᵒᵖ ⥤ 类型 (最大值 w v))
  定义体: { obj x := CostructuredArrow.mk (uliftYonedaEquiv.{w}.symm x.unop.2)
      map f := CostructuredArrow.homMk f.1.1.unop (by
        dsimp
        rw [← uliftYonedaEquiv_symm_map]; rw [map_snd]) }
  inverse :=
    { obj X := op (F.elementsMk _ (uliftYonedaEquiv.{w} X.hom))
      map f := (homMk _ _ f.

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, CostructuredArrow.mk, CostructuredArrow.w, F.elementsMk, Functor, Functor.map_id_apply, Iso.op, Iso.refl, NatIso, NatIso.ofComponents, Quiver, Quiver.Hom.unop_op, X.hom, elementsMk, f.left.op, inverse, map_id_apply, map_snd, ofComponents
-/
def costructuredArrowULiftYonedaEquivalence (F : Cᵒᵖ ⥤ Type (max w v)) :
    F.Elementsᵒᵖ ≌ CostructuredArrow uliftYoneda.{w} F where
  functor :=
    { obj x := CostructuredArrow.mk (uliftYonedaEquiv.{w}.symm x.unop.2)
      map f := CostructuredArrow.homMk f.1.1.unop (by
        dsimp
        rw [← uliftYonedaEquiv_symm_map]; rw [map_snd]) }
  inverse :=
    { obj X := op (F.elementsMk _ (uliftYonedaEquiv.{w} X.hom))
      map f := (homMk _ _ f.left.op (by
        dsimp
        rw [← CostructuredArrow.w f]; rw [uliftYonedaEquiv_naturality]; rw [Quiver.Hom.unop_op])).op }
  unitIso := NatIso.ofComponents (fun x => Iso.op (isoMk _ _ (Iso.refl _) (by
    dsimp
    simpa only [Functor.map_id_apply] using
      uliftYonedaEquiv.apply_symm_apply (unop x).snd)))
    (fun f => Quiver.Hom.unop_inj (by aesop))
  counitIso := NatIso.ofComponents (fun X => CostructuredArrow.isoMk (Iso.refl _))

/--
Definition of `costructuredArrowULiftYonedaEquivalenceFunctorCompProjIso` / `costructuredArrowULiftYonedaEquivalenceFunctorCompProjIso` 的定义

English:
definition costructuredArrowULiftYonedaEquivalenceFunctorCompProjIso
  signature: (F : Cᵒᵖ ⥤ Type (max w v))
  body: Iso.refl _

中文:
定义 costructuredArrowULiftYonedaEquivalenceFunctorCompProjIso
  签名: (F : Cᵒᵖ ⥤ 类型 (最大值 w v))
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def costructuredArrowULiftYonedaEquivalenceFunctorCompProjIso (F : Cᵒᵖ ⥤ Type (max w v)) :
    (costructuredArrowULiftYonedaEquivalence.{w} F).functor ⋙ CostructuredArrow.proj _ _ ≅
      (π F).leftOp :=
  Iso.refl _

end CategoryOfElements

namespace Functor

/-- The initial object in `F.Elements` if `F` is representable. -/
@[simps]
/--
Definition of `Elements.initialOfRepresentableBy` / `Elements.initialOfRepresentableBy` 的定义

English:
definition Elements.initialOfRepresentableBy
  signature: {F : Cᵒᵖ ⥤ Type*} {X : C} (h : F.RepresentableBy X)
  body: ⟨.op X, h.homEquiv (𝟙 X)⟩

中文:
定义 Elements.initialOfRepresentableBy
  签名: {F : Cᵒᵖ ⥤ 类型} {X : C} (h : F.可表示 X)
  定义体: ⟨.op X, h.homEquiv (𝟙 X)⟩

Depends on / 依赖: h.homEquiv, homEquiv
-/
def Elements.initialOfRepresentableBy {F : Cᵒᵖ ⥤ Type*} {X : C} (h : F.RepresentableBy X) :
    F.Elements :=
  ⟨.op X, h.homEquiv (𝟙 X)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Elements.isInitialOfRepresentableBy` / `Elements.isInitialOfRepresentableBy` 的定义

English:
definition Elements.isInitialOfRepresentableBy
  signature: {F : Cᵒᵖ ⥤ Type*} {X : C} (h : F.RepresentableBy X)
  body: .ofUniqueHom (fun Y => ⟨h.homEquiv.symm Y.snd |>.op, by simp [← h.homEquiv_comp]⟩) fun Y m => by
    simp [← m.2, ← h.homEquiv_unop_comp]

中文:
定义 Elements.isInitialOfRepresentableBy
  签名: {F : Cᵒᵖ ⥤ 类型} {X : C} (h : F.可表示 X)
  定义体: .ofUniqueHom (fun Y => ⟨h.homEquiv.symm Y.snd |>.op, by simp [← h.homEquiv_comp]⟩) fun Y m => by
    simp [← m.2, ← h.homEquiv_unop_comp]

Depends on / 依赖: Y.snd, h.homEquiv.symm, h.homEquiv_comp, h.homEquiv_unop_comp, homEquiv, homEquiv_comp, homEquiv_unop_comp, ofUniqueHom
-/
def Elements.isInitialOfRepresentableBy {F : Cᵒᵖ ⥤ Type*} {X : C} (h : F.RepresentableBy X) :
    Limits.IsInitial (initialOfRepresentableBy h) :=
  .ofUniqueHom (fun Y => ⟨h.homEquiv.symm Y.snd |>.op, by simp [← h.homEquiv_comp]⟩) fun Y m => by
    simp [← m.2, ← h.homEquiv_unop_comp]

/-- The initial object in `F.Elements` if `F` is corepresentable. -/
@[simps]
/--
Definition of `Elements.initialOfCorepresentableBy` / `Elements.initialOfCorepresentableBy` 的定义

English:
definition Elements.initialOfCorepresentableBy
  signature: {F : C ⥤ Type*} {X : C} (h : F.CorepresentableBy X)
  body: ⟨X, h.homEquiv (𝟙 X)⟩

中文:
定义 Elements.initialOfCorepresentableBy
  签名: {F : C ⥤ 类型} {X : C} (h : F.余representableBy X)
  定义体: ⟨X, h.homEquiv (𝟙 X)⟩

Depends on / 依赖: h.homEquiv, homEquiv
-/
def Elements.initialOfCorepresentableBy {F : C ⥤ Type*} {X : C} (h : F.CorepresentableBy X) :
    F.Elements :=
  ⟨X, h.homEquiv (𝟙 X)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Elements.isInitialOfCorepresentableBy` / `Elements.isInitialOfCorepresentableBy` 的定义

English:
definition Elements.isInitialOfCorepresentableBy
  signature: {F : C ⥤ Type*} {X : C} (h : F.CorepresentableBy X)
  body: .ofUniqueHom (fun Y => ⟨h.homEquiv.symm Y.snd, by simp [← h.homEquiv_comp]⟩) fun Y m => by
    simp [← m.2, ← h.homEquiv_comp]

中文:
定义 Elements.isInitialOfCorepresentableBy
  签名: {F : C ⥤ 类型} {X : C} (h : F.余representableBy X)
  定义体: .ofUniqueHom (fun Y => ⟨h.homEquiv.symm Y.snd, by simp [← h.homEquiv_comp]⟩) fun Y m => by
    simp [← m.2, ← h.homEquiv_comp]

Depends on / 依赖: Y.snd, h.homEquiv.symm, h.homEquiv_comp, homEquiv, homEquiv_comp, ofUniqueHom
-/
def Elements.isInitialOfCorepresentableBy {F : C ⥤ Type*} {X : C} (h : F.CorepresentableBy X) :
    Limits.IsInitial (initialOfCorepresentableBy h) :=
  .ofUniqueHom (fun Y => ⟨h.homEquiv.symm Y.snd, by simp [← h.homEquiv_comp]⟩) fun Y m => by
    simp [← m.2, ← h.homEquiv_comp]

/--
Definition of `Elements.initial` / `Elements.initial` 的定义

English:
definition Elements.initial
  signature: (A : C)
  body: ⟨Opposite.op A, 𝟙 _⟩

中文:
定义 Elements.initial
  签名: (A : C)
  定义体: ⟨Opposite.op A, 𝟙 _⟩

Depends on / 依赖: Opposite, Opposite.op
-/
def Elements.initial (A : C) : (yoneda.obj A).Elements :=
  ⟨Opposite.op A, 𝟙 _⟩

/--
Definition of `Elements.isInitial` / `Elements.isInitial` 的定义

English:
definition Elements.isInitial
  signature: (A : C)
  body: isInitialOfRepresentableBy (.yoneda A)

中文:
定义 Elements.isInitial
  签名: (A : C)
  定义体: isInitialOfRepresentableBy (.yoneda A)

Depends on / 依赖: isInitialOfRepresentableBy, yoneda
-/
def Elements.isInitial (A : C) : Limits.IsInitial (Elements.initial A) :=
  isInitialOfRepresentableBy (.yoneda A)

/-- The functor `(F ⋙ G).Elements ⥤ G.Elements`. -/
@[simps]
/--
Definition of `Elements.precomp` / `Elements.precomp` 的定义

English:
definition Elements.precomp
  signature: {D : Type*} [Category D] (F : C ⥤ D) (G : D ⥤ Type w)
  body: G.elementsMk (F.obj x.fst) x.snd
  map f := ⟨F.map f.1, f.2⟩

中文:
定义 Elements.precomp
  签名: {D : 类型} [范畴 D] (F : C ⥤ D) (G : D ⥤ 类型 w)
  定义体: G.elementsMk (F.obj x.fst) x.snd
  map f := ⟨F.map f.1, f.2⟩

Depends on / 依赖: F.obj, G.elementsMk, elementsMk, x.fst, x.snd
-/
def Elements.precomp {D : Type*} [Category D] (F : C ⥤ D) (G : D ⥤ Type w) :
    (F ⋙ G).Elements ⥤ G.Elements where
  obj x := G.elementsMk (F.obj x.fst) x.snd
  map f := ⟨F.map f.1, f.2⟩

/--
Instance `Elements.essentiallySmall` / 实例 `Elements.essentiallySmall`

English:
instance Elements.essentiallySmall
  signature: {C : Type u} [Category.{v} C]
  body: by
  rw [essentiallySmall_iff_objectPropertyEssentiallySmall_top]
  obtain ⟨P, _, hP⟩ := ObjectProperty.EssentiallySmall.exists_small_le' (⊤ : ObjectProperty C)
  refine ⟨fun x => P x.1, ?_, fun y _ => ?_⟩
  · exact small_of_surjective.{w} (α := Σ (Z : Subtype P), F.obj Z.1)
      (f := fun x => ⟨F.

中文:
实例 Elements.essentiallySmall
  签名: {C : 类型u} [范畴.{v} C]
  定义体: by
  rw [essentiallySmall_iff_objectPropertyEssentiallySmall_top]
  obtain ⟨P, _, hP⟩ := ObjectProperty.EssentiallySmall.exists_small_le' (⊤ : ObjectProperty C)
  refine ⟨fun x => P x.1, ?_, fun y _ => ?_⟩
  · exact small_of_surjective.{w} (α := Σ (Z : Subtype P), F.obj Z.1)
      (f := fun x => ⟨F.

Depends on / 依赖: CategoryOfElements, CategoryOfElements.isoMk, EssentiallySmall, F.elementsMk, F.map, F.obj, ObjectProperty, ObjectProperty.EssentiallySmall.exists_small_le, Subtype, e.hom, elementsMk, essentiallySmall_iff_objectPropertyEssentiallySmall_top, exists_small_le, small_of_surjective, y.fst, y.snd
-/
instance Elements.essentiallySmall {C : Type u} [Category.{v} C]
    (F : C ⥤ Type w) [EssentiallySmall.{w} C] :
    EssentiallySmall.{w} F.Elements := by
  rw [essentiallySmall_iff_objectPropertyEssentiallySmall_top]
  obtain ⟨P, _, hP⟩ := ObjectProperty.EssentiallySmall.exists_small_le' (⊤ : ObjectProperty C)
  refine ⟨fun x => P x.1, ?_, fun y _ => ?_⟩
  · exact small_of_surjective.{w} (α := Σ (Z : Subtype P), F.obj Z.1)
      (f := fun x => ⟨F.elementsMk _ x.2, x.1.2⟩)
      (fun ⟨x, hx⟩ => ⟨⟨⟨x.1, hx⟩, x.2⟩, rfl⟩)
  · obtain ⟨Z, hZ, ⟨e⟩⟩ := hP y.fst (by simp)
    exact ⟨F.elementsMk Z (F.map e.hom y.snd), hZ,
      ⟨CategoryOfElements.isoMk _ _ e rfl⟩⟩

end Functor

end CategoryTheory
