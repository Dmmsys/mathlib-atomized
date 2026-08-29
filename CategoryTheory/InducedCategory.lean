/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Induced categories and full subcategories

Given a category `D` and a function `F : C → D` from a type `C` to the
objects of `D`, there is an essentially unique way to give `C` a
category structure such that `F` becomes a fully faithful functor,
namely by taking $ Hom_C(X, Y) = Hom_D(FX, FY) $. We call this the
category induced from `D` along `F`.

## Implementation notes

The type of morphisms between `X` and `Y` in `InducedCategory D F` is
not definitionally equal to `F X ⟶ F Y`. Instead, this type is made
a `1`-field structure. Use `InducedCategory.homMk` to construct
morphisms in induced categories.

-/

@[expose] public section


namespace CategoryTheory

universe v v₂ u₁ u₂
-- morphism levels before object levels. See note [category theory universes].

section Induced

variable {C : Type u₁} (D : Type u₂) [Category.{v} D]
variable (F : C -> D)

/-- `InducedCategory D F`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y`.
-/
@[nolint unusedArguments, implicit_reducible]
/--
Definition of `InducedCategory` / `InducedCategory` 的定义

English:
definition InducedCategory
  signature: (_F : C -> D)
  body: C

中文:
定义 InducedCategory
  签名: (_F : C -> D)
  定义体: C
-/
def InducedCategory (_F : C -> D) : Type u₁ :=
  C

variable {D}

namespace InducedCategory

/--
Instance `hasCoeToSort` / 实例 `hasCoeToSort`

English:
instance hasCoeToSort
  signature: {α : Sort*} [CoeSort D α]
  body: ⟨fun c => F c⟩

中文:
实例 hasCoeToSort
  签名: {α : 类型层*} [CoeSort D α]
  定义体: ⟨fun c => F c⟩
-/
instance hasCoeToSort {α : Sort*} [CoeSort D α] :
    CoeSort (InducedCategory D F) α :=
  ⟨fun c => F c⟩

variable {F}

/-- The type of morphisms in `InducedCategory D F` between `X` and `Y`
is a 1-field structure which identifies to `F X ⟶ F Y`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : InducedCategory D F)
  axioms and operations (1):
    - hom : F X ⟶ F Y

中文:
结构 态射
  参数: (X Y : InducedCategory D F)
  公理与运算 (1 个):
    - hom : F X ⟶ F Y
-/
structure Hom (X Y : InducedCategory D F) where
  /-- The underlying morphism. -/
  hom : F X ⟶ F Y

@[simps id_hom comp_hom]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category.{v} (InducedCategory D F)
  body: Hom X Y
  id X := { hom := 𝟙 _ }
  comp f g := { hom := f.hom ≫ g.hom }

中文:
实例 :
  签名: 范畴.{v} (InducedCategory D F)
  定义体: Hom X Y
  id X := { hom := 𝟙 _ }
  comp f g := { hom := f.hom ≫ g.hom }
-/
instance : Category.{v} (InducedCategory D F) where
  Hom X Y := Hom X Y
  id X := { hom := 𝟙 _ }
  comp f g := { hom := f.hom ≫ g.hom }

attribute [reassoc] comp_hom

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : InducedCategory D F} {f g : X ⟶ Y} (h : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext h

中文:
引理 hom_ext
  条件: {X Y : InducedCategory D F} {f g : X ⟶ Y} (h : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext h

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : InducedCategory D F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {X Y : InducedCategory D F} (f : F X ⟶ F Y)
  body: f

中文:
定义 homMk
  签名: {X Y : InducedCategory D F} (f : F X ⟶ F Y)
  定义体: f
-/
@[simps] def homMk {X Y : InducedCategory D F} (f : F X ⟶ F Y) : X ⟶ Y where
  hom := f

/-- Morphisms in `InducedCategory D F` identify to morphisms in `D`. -/
@[simps!]
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: {X Y : InducedCategory D F}
  body: f.hom
  invFun f := homMk f

中文:
定义 homEquiv
  签名: {X Y : InducedCategory D F}
  定义体: f.hom
  invFun f := homMk f

Depends on / 依赖: f.hom
-/
def homEquiv {X Y : InducedCategory D F} : (X ⟶ Y) ≃ (F X ⟶ F Y) where
  toFun f := f.hom
  invFun f := homMk f

/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {X Y : InducedCategory D F} (f : F X ≅ F Y)
  body: homMk f.hom
  inv := homMk f.inv

中文:
定义 isoMk
  签名: {X Y : InducedCategory D F} (f : F X ≅ F Y)
  定义体: homMk f.hom
  inv := homMk f.inv
-/
@[simps] def isoMk {X Y : InducedCategory D F} (f : F X ≅ F Y) : X ≅ Y where
  hom := homMk f.hom
  inv := homMk f.inv

end InducedCategory

/-- The forgetful functor from an induced category to the original category,
forgetting the extra data.
-/
@[simps, implicit_reducible]
/--
Definition of `inducedFunctor` / `inducedFunctor` 的定义

English:
definition inducedFunctor
  signature: : InducedCategory D F ⥤ D where
  body: F
  map f := f.hom

中文:
定义 inducedFunctor
  签名: : InducedCategory D F ⥤ D where
  定义体: F
  map f := f.hom
-/
def inducedFunctor : InducedCategory D F ⥤ D where
  obj := F
  map f := f.hom

/--
Definition of `fullyFaithfulInducedFunctor` / `fullyFaithfulInducedFunctor` 的定义

English:
definition fullyFaithfulInducedFunctor
  signature: : (inducedFunctor F).FullyFaithful where
  body: InducedCategory.homMk f

中文:
定义 fullyFaithfulInducedFunctor
  签名: : (inducedFunctor F).满忠实 where
  定义体: InducedCategory.homMk f

Depends on / 依赖: InducedCategory, InducedCategory.homMk
-/
def fullyFaithfulInducedFunctor : (inducedFunctor F).FullyFaithful where
  preimage f := InducedCategory.homMk f

/--
Instance `InducedCategory.full` / 实例 `InducedCategory.full`

English:
instance InducedCategory.full
  signature: : (inducedFunctor F).Full
  body: (fullyFaithfulInducedFunctor F).full

中文:
实例 InducedCategory.full
  签名: : (inducedFunctor F).满
  定义体: (fullyFaithfulInducedFunctor F).full

Depends on / 依赖: fullyFaithfulInducedFunctor
-/
instance InducedCategory.full : (inducedFunctor F).Full :=
  (fullyFaithfulInducedFunctor F).full

/--
Instance `InducedCategory.faithful` / 实例 `InducedCategory.faithful`

English:
instance InducedCategory.faithful
  signature: : (inducedFunctor F).Faithful
  body: (fullyFaithfulInducedFunctor F).faithful

中文:
实例 InducedCategory.faithful
  签名: : (inducedFunctor F).忠实
  定义体: (fullyFaithfulInducedFunctor F).faithful

Depends on / 依赖: faithful, fullyFaithfulInducedFunctor
-/
instance InducedCategory.faithful : (inducedFunctor F).Faithful :=
  (fullyFaithfulInducedFunctor F).faithful

end Induced

end CategoryTheory
