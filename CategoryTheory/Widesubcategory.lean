/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Wide subcategories

A wide subcategory of a category `C` is a subcategory containing all the objects of `C`.

## Main declarations

Given a category `D`, a function `F : C → D` from a type `C` to the objects of `D`,
and a morphism property `P` on `D` which contains identities and is stable under
composition, the type class `InducedWideCategory D F P` is a typeclass
synonym for `C` which comes equipped with a category structure whose morphisms `X ⟶ Y` are the
morphisms in `D` which have the property `P`.

The instance `WideSubcategory.category` provides a category structure on `WideSubcategory P`
whose objects are the objects of `C` and morphisms are the morphisms in `C` which have the
property `P`.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

open MorphismProperty

section Induced

variable {C : Type u₁} (D : Type u₂) [Category.{v₁} D]
variable (F : C -> D) (P : MorphismProperty D) [P.IsMultiplicative]

/-- `InducedWideCategory D F P`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y` which satisfy a property `P : MorphismProperty D` that is multiplicative.
-/
@[nolint unusedArguments]
/--
Definition of `InducedWideCategory` / `InducedWideCategory` 的定义

English:
definition InducedWideCategory
  signature: (_F : C -> D) (_P : MorphismProperty D) [IsMultiplicative _P]
  body: C

中文:
定义 InducedWideCategory
  签名: (_F : C -> D) (_P : MorphismProperty D) [是Multiplicative _P]
  定义体: C
-/
def InducedWideCategory (_F : C -> D) (_P : MorphismProperty D) [IsMultiplicative _P] :=
  C

variable {D}

/--
Instance `InducedWideCategory.hasCoeToSort` / 实例 `InducedWideCategory.hasCoeToSort`

English:
instance InducedWideCategory.hasCoeToSort
  signature: {α : Sort*} [CoeSort D α]
  body: ⟨fun c => F c⟩

中文:
实例 InducedWideCategory.hasCoeToSort
  签名: {α : 类型层*} [CoeSort D α]
  定义体: ⟨fun c => F c⟩
-/
instance InducedWideCategory.hasCoeToSort {α : Sort*} [CoeSort D α] :
    CoeSort (InducedWideCategory D F P) α :=
  ⟨fun c => F c⟩

variable {F P} in
/-- The type of morphisms in `InducedWideCategory D F P` between `X` and `Y`
is a 2-field structure consisting of a morphism `F X ⟶ F Y` in `D` that satisfies
the property `P`. -/
@[ext]
/--
Definition of `InducedWideCategory.Hom` / `InducedWideCategory.Hom` 的定义

English:
structure InducedWideCategory.Hom
  parameters: (X Y : InducedWideCategory D F P)
  axioms and operations (2):
    - hom : F X ⟶ F Y
    - property : P hom

中文:
结构 InducedWideCategory.态射
  参数: (X Y : InducedWideCategory D F P)
  公理与运算 (2 个):
    - hom : F X ⟶ F Y
    - property : P hom
-/
structure InducedWideCategory.Hom (X Y : InducedWideCategory D F P) where
  /-- The underlying morphism. -/
  hom : F X ⟶ F Y
  /-- The property that the morphism satisfies. -/
  property : P hom

@[simps!]
/--
Instance `InducedWideCategory.category` / 实例 `InducedWideCategory.category`

English:
instance InducedWideCategory.category
  signature: :
  body: Hom X Y
  id X := ⟨𝟙 (F X), P.id_mem (F X)⟩
  comp {_ _ _} f g := ⟨f.1 ≫ g.1, P.comp_mem _ _ f.2 g.2⟩

中文:
实例 InducedWideCategory.category
  签名: :
  定义体: Hom X Y
  id X := ⟨𝟙 (F X), P.id_mem (F X)⟩
  comp {_ _ _} f g := ⟨f.1 ≫ g.1, P.comp_mem _ _ f.2 g.2⟩
-/
instance InducedWideCategory.category :
    Category (InducedWideCategory D F P) where
  Hom X Y := Hom X Y
  id X := ⟨𝟙 (F X), P.id_mem (F X)⟩
  comp {_ _ _} f g := ⟨f.1 ≫ g.1, P.comp_mem _ _ f.2 g.2⟩

/-- The forgetful functor from an induced wide category to the original category. -/
@[simps]
/--
Definition of `wideInducedFunctor` / `wideInducedFunctor` 的定义

English:
definition wideInducedFunctor
  signature: : InducedWideCategory D F P ⥤ D where
  body: F
  map {_ _} f := f.1

中文:
定义 wideInducedFunctor
  签名: : InducedWideCategory D F P ⥤ D where
  定义体: F
  map {_ _} f := f.1
-/
def wideInducedFunctor : InducedWideCategory D F P ⥤ D where
  obj := F
  map {_ _} f := f.1

/--
Instance `InducedWideCategory.faithful` / 实例 `InducedWideCategory.faithful`

English:
instance InducedWideCategory.faithful
  signature: : (wideInducedFunctor F P).Faithful where
  body: by
    cases f
    cases g
    aesop

中文:
实例 InducedWideCategory.faithful
  签名: : (wideInducedFunctor F P).忠实 where
  定义体: by
    cases f
    cases g
    aesop
-/
instance InducedWideCategory.faithful : (wideInducedFunctor F P).Faithful where
  map_injective {X Y} f g eq := by
    cases f
    cases g
    aesop

end Induced

section WideSubcategory

variable {C : Type u₁} [Category.{v₁} C]
variable (P : MorphismProperty C) [IsMultiplicative P]

/--
Structure for wide subcategories. Objects ignore the morphism property.
-/
@[ext, nolint unusedArguments]
/--
Definition of `WideSubcategory` / `WideSubcategory` 的定义

English:
structure WideSubcategory
  parameters: (_P : MorphismProperty C) [IsMultiplicative _P]
  axioms and operations (1):
    - obj : C

中文:
结构 宽子范畴
  参数: (_P : MorphismProperty C) [是Multiplicative _P]
  公理与运算 (1 个):
    - obj : C
-/
structure WideSubcategory (_P : MorphismProperty C) [IsMultiplicative _P] where
  /-- The category of which this is a wide subcategory -/
  obj : C

/--
Instance `WideSubcategory.category` / 实例 `WideSubcategory.category`

English:
instance WideSubcategory.category
  signature: : Category.{v₁} (WideSubcategory P)
  body: InducedWideCategory.category WideSubcategory.obj P

@[ext]

中文:
实例 宽子范畴.category
  签名: : 范畴.{v₁} (宽子范畴 P)
  定义体: InducedWideCategory.category WideSubcategory.obj P

@[ext]

Depends on / 依赖: InducedWideCategory, InducedWideCategory.category, WideSubcategory, WideSubcategory.obj, category
-/
instance WideSubcategory.category : Category.{v₁} (WideSubcategory P) :=
  InducedWideCategory.category WideSubcategory.obj P

@[ext]
/--
lemma `WideSubcategory.hom_ext` / 引理 `WideSubcategory.hom_ext`

English:
lemma WideSubcategory.hom_ext
  given: {X Y : WideSubcategory P} {f g : X ⟶ Y} (h : f.hom = g.hom)
  proof: InducedWideCategory.Hom.ext h

@[simp]

中文:
引理 宽子范畴.hom_ext
  条件: {X Y : 宽子范畴 P} {f g : X ⟶ Y} (h : f.hom = g.hom)
  证明: InducedWideCategory.Hom.ext h

@[simp]

Depends on / 依赖: InducedWideCategory, InducedWideCategory.Hom.ext
-/
lemma WideSubcategory.hom_ext {X Y : WideSubcategory P} {f g : X ⟶ Y} (h : f.hom = g.hom) :
    f = g :=
  InducedWideCategory.Hom.ext h

@[simp]
/--
lemma `WideSubcategory.id_def` / 引理 `WideSubcategory.id_def`

English:
lemma WideSubcategory.id_def
  given: (X : WideSubcategory P)
  statement: (CategoryStruct.id X).1 = 𝟙 X.obj
  proof: rfl

@[simp]

中文:
引理 宽子范畴.id_def
  条件: (X : 宽子范畴 P)
  结论: (CategoryStruct.id X).1 = 𝟙 X.obj
  证明: rfl

@[simp]
-/
lemma WideSubcategory.id_def (X : WideSubcategory P) : (CategoryStruct.id X).1 = 𝟙 X.obj := rfl

@[simp]
/--
lemma `WideSubcategory.comp_def` / 引理 `WideSubcategory.comp_def`

English:
lemma WideSubcategory.comp_def
  given: {X Y Z : WideSubcategory P} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 宽子范畴.comp_def
  条件: {X Y Z : 宽子范畴 P} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma WideSubcategory.comp_def {X Y Z : WideSubcategory P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = (f.1 ≫ g.1 : X.obj ⟶ Z.obj) := rfl

/--
Definition of `wideSubcategoryInclusion` / `wideSubcategoryInclusion` 的定义

English:
definition wideSubcategoryInclusion
  signature: : WideSubcategory P ⥤ C
  body: wideInducedFunctor WideSubcategory.obj P

@[simp]

中文:
定义 wideSubcategoryInclusion
  签名: : 宽子范畴 P ⥤ C
  定义体: wideInducedFunctor WideSubcategory.obj P

@[simp]

Depends on / 依赖: WideSubcategory, WideSubcategory.obj, wideInducedFunctor
-/
def wideSubcategoryInclusion : WideSubcategory P ⥤ C :=
  wideInducedFunctor WideSubcategory.obj P

@[simp]
/--
theorem `wideSubcategoryInclusion.obj` / 定理 `wideSubcategoryInclusion.obj`

English:
theorem wideSubcategoryInclusion.obj
  given: (X)
  statement: (wideSubcategoryInclusion P).obj X = X.obj
  proof: rfl

@[simp]

中文:
定理 wideSubcategoryInclusion.obj
  条件: (X)
  结论: (wideSubcategoryInclusion P).obj X = X.obj
  证明: rfl

@[simp]
-/
theorem wideSubcategoryInclusion.obj (X) : (wideSubcategoryInclusion P).obj X = X.obj :=
  rfl

@[simp]
/--
theorem `wideSubcategoryInclusion.map` / 定理 `wideSubcategoryInclusion.map`

English:
theorem wideSubcategoryInclusion.map
  given: {X Y} {f : X ⟶ Y}
  proof: rfl

中文:
定理 wideSubcategoryInclusion.map
  条件: {X Y} {f : X ⟶ Y}
  证明: rfl
-/
theorem wideSubcategoryInclusion.map {X Y} {f : X ⟶ Y} :
    (wideSubcategoryInclusion P).map f = f.1 :=
  rfl

/--
Instance `wideSubcategory.faithful` / 实例 `wideSubcategory.faithful`

English:
instance wideSubcategory.faithful
  signature: : (wideSubcategoryInclusion P).Faithful
  body: inferInstanceAs (wideInducedFunctor WideSubcategory.obj P).Faithful

中文:
实例 wideSubcategory.faithful
  签名: : (wideSubcategoryInclusion P).忠实
  定义体: inferInstanceAs (wideInducedFunctor WideSubcategory.obj P).Faithful

Depends on / 依赖: Faithful, WideSubcategory, WideSubcategory.obj, wideInducedFunctor
-/
instance wideSubcategory.faithful : (wideSubcategoryInclusion P).Faithful :=
  inferInstanceAs (wideInducedFunctor WideSubcategory.obj P).Faithful

variable {P} in
/-- Build an isomorphism in `WideSubcategory P` from an isomorphism in `C`. -/
@[simps!]
/--
Definition of `WideSubcategory.isoMk` / `WideSubcategory.isoMk` 的定义

English:
definition WideSubcategory.isoMk
  signature: {X Y : WideSubcategory P} (e : X.obj ≅ Y.obj)
  body: ⟨e.hom, h₁⟩
  inv := ⟨e.inv, h₂⟩

@[deprecated (since := "2026-08-07")] alias isoMk := WideSubcategory.isoMk

中文:
定义 宽子范畴.isoMk
  签名: {X Y : 宽子范畴 P} (e : X.obj ≅ Y.obj)
  定义体: ⟨e.hom, h₁⟩
  inv := ⟨e.inv, h₂⟩

@[deprecated (since := "2026-08-07")] alias isoMk := WideSubcategory.isoMk

Depends on / 依赖: e.hom
-/
def WideSubcategory.isoMk {X Y : WideSubcategory P} (e : X.obj ≅ Y.obj)
    (h₁ : P e.hom) (h₂ : P e.inv) : X ≅ Y where
  hom := ⟨e.hom, h₁⟩
  inv := ⟨e.inv, h₂⟩

@[deprecated (since := "2026-08-07")] alias isoMk := WideSubcategory.isoMk

end WideSubcategory

end CategoryTheory
