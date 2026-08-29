/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Chosen pullbacks along a morphism

## Main declarations

- `ChosenPullbacksAlong` : For a morphism `f : Y ⟶ X` in `C`, the type class
  `ChosenPullbacksAlong f` provides the data of a pullback functor `Over X ⥤ Over Y`
  as a right adjoint to `Over.map f`.

## Main results

- We prove that `ChosenPullbacksAlong` has good closure properties: isos have chosen pullbacks,
  and composition of morphisms with chosen pullbacks have chosen pullbacks.

- We prove that chosen pullbacks yield usual pullbacks: `ChosenPullbacksAlong.isPullback`
  proves that for morphisms `f` and `g` with the same codomain, the object
  `ChosenPullbacksAlong.pullbackObj f g` together with morphisms
  `ChosenPullbacksAlong.fst f g` and `ChosenPullbacksAlong.snd f g` form a pullback square
  over `f` and `g`.

- We prove that in cartesian monoidal categories, morphisms to the terminal tensor unit and
  the product projections have chosen pullbacks.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits CartesianMonoidalCategory MonoidalCategory Over

variable {C : Type u₁} [Category.{v₁} C]

/--
Definition of `ChosenPullbacksAlong` / `ChosenPullbacksAlong` 的定义

English:
class ChosenPullbacksAlong
  parameters: {Y X : C} (f : Y ⟶ X)
  axioms and operations (2):
    - pullback : Over X ⥤ Over Y
    - mapPullbackAdj((f)) : Over.map f ⊣ pullback

中文:
类 ChosenPullbacksAlong
  参数: {Y X : C} (f : Y ⟶ X)
  公理与运算 (2 个):
    - pullback : Over X ⥤ Over Y
    - mapPullbackAdj((f)) : Over.map f ⊣ pullback
-/
class ChosenPullbacksAlong {Y X : C} (f : Y ⟶ X) where
  /-- The pullback functor along `f`. -/
  pullback : Over X ⥤ Over Y
  /-- The adjunction between `Over.map f` and `pullback f`. -/
  mapPullbackAdj (f) : Over.map f ⊣ pullback

variable (C) in
/--
Definition of `ChosenPullbacks` / `ChosenPullbacks` 的定义

English:
abbreviation ChosenPullbacks
  body: Π {X Y : C} (f : Y ⟶ X), ChosenPullbacksAlong f

中文:
缩写 ChosenPullbacks
  定义体: Π {X Y : C} (f : Y ⟶ X), ChosenPullbacksAlong f

Depends on / 依赖: ChosenPullbacksAlong
-/
abbrev ChosenPullbacks := Π {X Y : C} (f : Y ⟶ X), ChosenPullbacksAlong f

namespace ChosenPullbacksAlong

/-- Relating the existing noncomputable `HasPullbacksAlong` typeclass to `ChosenPullbacksAlong`. -/
@[simps, instance_reducible]
/--
Definition of `ofHasPullbacksAlong` / `ofHasPullbacksAlong` 的定义

English:
definition ofHasPullbacksAlong
  signature: {Y X : C} (f : Y ⟶ X) [HasPullbacksAlong f]
  body: Over.pullback f
  mapPullbackAdj := Over.mapPullbackAdj f

中文:
定义 ofHasPullbacksAlong
  签名: {Y X : C} (f : Y ⟶ X) [有PullbacksAlong f]
  定义体: Over.pullback f
  mapPullbackAdj := Over.mapPullbackAdj f

Depends on / 依赖: Over.pullback, pullback
-/
noncomputable def ofHasPullbacksAlong {Y X : C} (f : Y ⟶ X) [HasPullbacksAlong f] :
    ChosenPullbacksAlong f where
  pullback := Over.pullback f
  mapPullbackAdj := Over.mapPullbackAdj f

/-- The identity morphism has a functorial choice of pullbacks. -/
@[instance_reducible]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (X : C)
  body: 𝟭 _
  mapPullbackAdj := (Adjunction.id).ofNatIsoLeft (Over.mapId _).symm

中文:
定义 id
  签名: (X : C)
  定义体: 𝟭 _
  mapPullbackAdj := (Adjunction.id).ofNatIsoLeft (Over.mapId _).symm
-/
def id (X : C) : ChosenPullbacksAlong (𝟙 X) where
  pullback := 𝟭 _
  mapPullbackAdj := (Adjunction.id).ofNatIsoLeft (Over.mapId _).symm

/--
Definition of `pullbackId` / `pullbackId` 的定义

English:
definition pullbackId
  signature: (X : C) [ChosenPullbacksAlong (𝟙 X)]
  body: (mapPullbackAdj (𝟙 X)).rightAdjointUniq (id X).mapPullbackAdj

@[reassoc (attr := simp)]

中文:
定义 pullbackId
  签名: (X : C) [ChosenPullbacksAlong (𝟙 X)]
  定义体: (mapPullbackAdj (𝟙 X)).rightAdjointUniq (id X).mapPullbackAdj

@[reassoc (attr := simp)]

Depends on / 依赖: mapPullbackAdj, rightAdjointUniq
-/
def pullbackId (X : C) [ChosenPullbacksAlong (𝟙 X)] :
    pullback (𝟙 X) ≅ 𝟭 (Over X) :=
  (mapPullbackAdj (𝟙 X)).rightAdjointUniq (id X).mapPullbackAdj

@[reassoc (attr := simp)]
/--
theorem `unit_pullbackId_hom_app` / 定理 `unit_pullbackId_hom_app`

English:
theorem unit_pullbackId_hom_app
  given: (X : C) [ChosenPullbacksAlong (𝟙 X)] (Y : Over X)
  proof: by
  rw [pullbackId]; rw [Adjunction.unit_rightAdjointUniq_hom_app]

@[reassoc (attr := simp)]

中文:
定理 unit_pullbackId_hom_app
  条件: (X : C) [ChosenPullbacksAlong (𝟙 X)] (Y : Over X)
  证明: by
  rw [pullbackId]; rw [Adjunction.unit_rightAdjointUniq_hom_app]

@[reassoc (attr := simp)]

Depends on / 依赖: Adjunction, Adjunction.unit_rightAdjointUniq_hom_app, pullbackId, unit_rightAdjointUniq_hom_app
-/
theorem unit_pullbackId_hom_app (X : C) [ChosenPullbacksAlong (𝟙 X)] (Y : Over X) :
    (mapPullbackAdj (𝟙 X)).unit.app Y ≫ (pullbackId X).hom.app ((Over.map (𝟙 X)).obj Y) =
      (id X).mapPullbackAdj.unit.app Y := by
  rw [pullbackId]; rw [Adjunction.unit_rightAdjointUniq_hom_app]

@[reassoc (attr := simp)]
/--
theorem `unit_pullbackId_hom` / 定理 `unit_pullbackId_hom`

English:
theorem unit_pullbackId_hom
  given: (X : C) [ChosenPullbacksAlong (𝟙 X)]
  proof: by
  rw [pullbackId]; rw [Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]

中文:
定理 unit_pullbackId_hom
  条件: (X : C) [ChosenPullbacksAlong (𝟙 X)]
  证明: by
  rw [pullbackId]; rw [Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]

Depends on / 依赖: Adjunction, Adjunction.unit_rightAdjointUniq_hom, pullbackId, unit_rightAdjointUniq_hom
-/
theorem unit_pullbackId_hom (X : C) [ChosenPullbacksAlong (𝟙 X)] :
    (mapPullbackAdj (𝟙 X)).unit ≫ (Over.map (𝟙 X)).whiskerLeft (pullbackId X).hom =
      (id X).mapPullbackAdj.unit := by
  rw [pullbackId]; rw [Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]
/--
theorem `pullbackId_hom_counit` / 定理 `pullbackId_hom_counit`

English:
theorem pullbackId_hom_counit
  given: (X : C) [ChosenPullbacksAlong (𝟙 X)]
  proof: by
  have := Adjunction.rightAdjointUniq_hom_counit (mapPullbackAdj (𝟙 X)) (id X).mapPullbackAdj
  rw [pullbackId]; rw [Adjunction.rightAdjointUniq_hom_counit]

中文:
定理 pullbackId_hom_counit
  条件: (X : C) [ChosenPullbacksAlong (𝟙 X)]
  证明: by
  have := Adjunction.rightAdjointUniq_hom_counit (mapPullbackAdj (𝟙 X)) (id X).mapPullbackAdj
  rw [pullbackId]; rw [Adjunction.rightAdjointUniq_hom_counit]

Depends on / 依赖: Adjunction, Adjunction.rightAdjointUniq_hom_counit, mapPullbackAdj, pullbackId, rightAdjointUniq_hom_counit
-/
theorem pullbackId_hom_counit (X : C) [ChosenPullbacksAlong (𝟙 X)] :
    Functor.whiskerRight (pullbackId X).hom (Over.map (𝟙 X)) ≫ (id X).mapPullbackAdj.counit =
      (mapPullbackAdj (𝟙 X)).counit := by
  have := Adjunction.rightAdjointUniq_hom_counit (mapPullbackAdj (𝟙 X)) (id X).mapPullbackAdj
  rw [pullbackId]; rw [Adjunction.rightAdjointUniq_hom_counit]

set_option backward.defeqAttrib.useBackward true in
/-- Every isomorphism has a functorial choice of pullbacks. -/
@[simps, instance_reducible]
/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: {Y X : C} (f : Y ≅ X)
  body: Over.mk (Z.hom ≫ f.inv)
  pullback.map {Y Z} g := Over.homMk (g.left)
  mapPullbackAdj.unit.app T := Over.homMk (𝟙 T.left)
  mapPullbackAdj.counit.app U := Over.homMk (𝟙 _)

中文:
定义 iso
  签名: {Y X : C} (f : Y ≅ X)
  定义体: Over.mk (Z.hom ≫ f.inv)
  pullback.map {Y Z} g := Over.homMk (g.left)
  mapPullbackAdj.unit.app T := Over.homMk (𝟙 T.left)
  mapPullbackAdj.counit.app U := Over.homMk (𝟙 _)

Depends on / 依赖: Over.mk, Z.hom, f.inv
-/
def iso {Y X : C} (f : Y ≅ X) : ChosenPullbacksAlong f.hom where
  pullback.obj Z := Over.mk (Z.hom ≫ f.inv)
  pullback.map {Y Z} g := Over.homMk (g.left)
  mapPullbackAdj.unit.app T := Over.homMk (𝟙 T.left)
  mapPullbackAdj.counit.app U := Over.homMk (𝟙 _)

/-- The inverse of an isomorphism has a functorial choice of pullbacks. -/
@[simps!, instance_reducible]
/--
Definition of `isoInv` / `isoInv` 的定义

English:
definition isoInv
  signature: {Y X : C} (f : Y ≅ X)
  body: iso f.symm

中文:
定义 isoInv
  签名: {Y X : C} (f : Y ≅ X)
  定义体: iso f.symm

Depends on / 依赖: f.symm
-/
def isoInv {Y X : C} (f : Y ≅ X) : ChosenPullbacksAlong f.inv := iso f.symm

/-- The composition of morphisms with chosen pullbacks has a chosen pullback. -/
@[instance_reducible]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  body: pullback g ⋙ pullback f
  mapPullbackAdj := ((mapPullbackAdj f).comp (mapPullbackAdj g)).ofNatIsoLeft
    (Over.mapComp f g).symm

中文:
定义 comp
  签名: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  定义体: pullback g ⋙ pullback f
  mapPullbackAdj := ((mapPullbackAdj f).comp (mapPullbackAdj g)).ofNatIsoLeft
    (Over.mapComp f g).symm

Depends on / 依赖: pullback
-/
def comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] : ChosenPullbacksAlong (f ≫ g) where
  pullback := pullback g ⋙ pullback f
  mapPullbackAdj := ((mapPullbackAdj f).comp (mapPullbackAdj g)).ofNatIsoLeft
    (Over.mapComp f g).symm

/--
Definition of `pullbackComp` / `pullbackComp` 的定义

English:
definition pullbackComp
  signature: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  body: Adjunction.rightAdjointUniq (mapPullbackAdj (f ≫ g)) ((comp f g).mapPullbackAdj)

@[reassoc (attr := simp)]

中文:
定义 pullbackComp
  签名: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  定义体: Adjunction.rightAdjointUniq (mapPullbackAdj (f ≫ g)) ((comp f g).mapPullbackAdj)

@[reassoc (attr := simp)]

Depends on / 依赖: Adjunction, Adjunction.rightAdjointUniq, mapPullbackAdj, rightAdjointUniq
-/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  Adjunction.rightAdjointUniq (mapPullbackAdj (f ≫ g)) ((comp f g).mapPullbackAdj)

@[reassoc (attr := simp)]
/--
theorem `unit_pullbackComp_hom` / 定理 `unit_pullbackComp_hom`

English:
theorem unit_pullbackComp_hom
  statement: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  rw [pullbackComp]; rw [Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]

中文:
定理 unit_pullbackComp_hom
  结论: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  rw [pullbackComp]; rw [Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]

Depends on / 依赖: Adjunction, Adjunction.unit_rightAdjointUniq_hom, pullbackComp, unit_rightAdjointUniq_hom
-/
theorem unit_pullbackComp_hom {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] :
    (mapPullbackAdj (f ≫ g)).unit ≫ (Over.map (f ≫ g)).whiskerLeft (pullbackComp f g).hom =
      (comp f g).mapPullbackAdj.unit := by
  rw [pullbackComp]; rw [Adjunction.unit_rightAdjointUniq_hom]

@[reassoc (attr := simp)]
/--
theorem `pullbackComp_hom_counit` / 定理 `pullbackComp_hom_counit`

English:
theorem pullbackComp_hom_counit
  statement: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  rw [pullbackComp]; rw [Adjunction.rightAdjointUniq_hom_counit]

中文:
定理 pullbackComp_hom_counit
  结论: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  rw [pullbackComp]; rw [Adjunction.rightAdjointUniq_hom_counit]

Depends on / 依赖: Adjunction, Adjunction.rightAdjointUniq_hom_counit, pullbackComp, rightAdjointUniq_hom_counit
-/
theorem pullbackComp_hom_counit {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [ChosenPullbacksAlong f] [ChosenPullbacksAlong g] [ChosenPullbacksAlong (f ≫ g)] :
    Functor.whiskerRight (pullbackComp f g).hom (Over.map (f ≫ g)) ≫
      (comp f g).mapPullbackAdj.counit =
      (mapPullbackAdj (f ≫ g)).counit := by
  rw [pullbackComp]; rw [Adjunction.rightAdjointUniq_hom_counit]

set_option backward.defeqAttrib.useBackward true in
/-- In cartesian monoidal categories, any morphism to the terminal tensor unit has a functorial
choice of pullbacks. -/
@[instance_reducible, simps]
/--
Definition of `cartesianMonoidalCategoryToUnit` / `cartesianMonoidalCategoryToUnit` 的定义

English:
definition cartesianMonoidalCategoryToUnit
  signature: [CartesianMonoidalCategory C] {X : C} (f : X ⟶ 𝟙_ C)
  body: Over.mk (snd Y.left X)
  pullback.map {Y Z} g := Over.homMk (g.left ▷ X)
  mapPullbackAdj.unit.app T := Over.homMk (lift (𝟙 _) (T.hom))
  mapPullbackAdj.counit.app U := Over.homMk (fst _ _)

中文:
定义 cartesianMonoidalCategoryToUnit
  签名: [CartesianMonoidal范畴 C] {X : C} (f : X ⟶ 𝟙_ C)
  定义体: Over.mk (snd Y.left X)
  pullback.map {Y Z} g := Over.homMk (g.left ▷ X)
  mapPullbackAdj.unit.app T := Over.homMk (lift (𝟙 _) (T.hom))
  mapPullbackAdj.counit.app U := Over.homMk (fst _ _)

Depends on / 依赖: Over.mk, Y.left
-/
def cartesianMonoidalCategoryToUnit [CartesianMonoidalCategory C] {X : C} (f : X ⟶ 𝟙_ C) :
    ChosenPullbacksAlong f where
  pullback.obj Y := Over.mk (snd Y.left X)
  pullback.map {Y Z} g := Over.homMk (g.left ▷ X)
  mapPullbackAdj.unit.app T := Over.homMk (lift (𝟙 _) (T.hom))
  mapPullbackAdj.counit.app U := Over.homMk (fst _ _)

set_option backward.defeqAttrib.useBackward true in
/-- In cartesian monoidal categories, the first product projections `fst` have a functorial choice
of pullbacks. -/
@[simps, instance_reducible]
/--
Definition of `cartesianMonoidalCategoryFst` / `cartesianMonoidalCategoryFst` 的定义

English:
definition cartesianMonoidalCategoryFst
  signature: [CartesianMonoidalCategory C] (X Y : C)
  body: Over.mk (Z.hom ▷ Y)
  pullback.map g := Over.homMk (g.left ▷ Y)
  mapPullbackAdj.unit.app T := Over.homMk (lift (𝟙 _) (T.hom ≫ snd _ _))
  mapPullbackAdj.counit.app U := Over.homMk (fst _ _)

中文:
定义 cartesianMonoidalCategoryFst
  签名: [CartesianMonoidal范畴 C] (X Y : C)
  定义体: Over.mk (Z.hom ▷ Y)
  pullback.map g := Over.homMk (g.left ▷ Y)
  mapPullbackAdj.unit.app T := Over.homMk (lift (𝟙 _) (T.hom ≫ snd _ _))
  mapPullbackAdj.counit.app U := Over.homMk (fst _ _)

Depends on / 依赖: Over.mk, Z.hom
-/
def cartesianMonoidalCategoryFst [CartesianMonoidalCategory C] (X Y : C) :
    ChosenPullbacksAlong (fst X Y : X otimes Y ⟶ X) where
  pullback.obj Z := Over.mk (Z.hom ▷ Y)
  pullback.map g := Over.homMk (g.left ▷ Y)
  mapPullbackAdj.unit.app T := Over.homMk (lift (𝟙 _) (T.hom ≫ snd _ _))
  mapPullbackAdj.counit.app U := Over.homMk (fst _ _)

set_option backward.defeqAttrib.useBackward true in
/-- In cartesian monoidal categories, the second product projections `snd` have a functorial choice
of pullbacks. -/
@[simps, instance_reducible]
/--
Definition of `cartesianMonoidalCategorySnd` / `cartesianMonoidalCategorySnd` 的定义

English:
definition cartesianMonoidalCategorySnd
  signature: [CartesianMonoidalCategory C] (X Y : C)
  body: Over.mk (X ◁ Z.hom)
  pullback.map g := Over.homMk (X ◁ g.left)
  mapPullbackAdj.unit.app T := Over.homMk (lift (T.hom ≫ fst _ _) (𝟙 _))
  mapPullbackAdj.counit.app U := Over.homMk (snd _ _)

中文:
定义 cartesianMonoidalCategorySnd
  签名: [CartesianMonoidal范畴 C] (X Y : C)
  定义体: Over.mk (X ◁ Z.hom)
  pullback.map g := Over.homMk (X ◁ g.left)
  mapPullbackAdj.unit.app T := Over.homMk (lift (T.hom ≫ fst _ _) (𝟙 _))
  mapPullbackAdj.counit.app U := Over.homMk (snd _ _)

Depends on / 依赖: Over.mk, Z.hom
-/
def cartesianMonoidalCategorySnd [CartesianMonoidalCategory C] (X Y : C) :
    ChosenPullbacksAlong (snd X Y : X otimes Y ⟶ Y) where
  pullback.obj Z := Over.mk (X ◁ Z.hom)
  pullback.map g := Over.homMk (X ◁ g.left)
  mapPullbackAdj.unit.app T := Over.homMk (lift (T.hom ≫ fst _ _) (𝟙 _))
  mapPullbackAdj.counit.app U := Over.homMk (snd _ _)

section PullbackFromChosenPullbacksAlongs

variable {Y Z X : C} (f : Y ⟶ X) (g : Z ⟶ X) [ChosenPullbacksAlong g]

/--
Definition of `pullbackObj` / `pullbackObj` 的定义

English:
abbreviation pullbackObj
  signature: : C
  body: ((pullback g).obj (Over.mk f)).left

中文:
缩写 pullbackObj
  签名: : C
  定义体: ((pullback g).obj (Over.mk f)).left

Depends on / 依赖: Over.mk, pullback
-/
abbrev pullbackObj : C := ((pullback g).obj (Over.mk f)).left

/--
Definition of `fst'` / `fst'` 的定义

English:
abbreviation fst'
  signature: : (Over.map g).obj ((pullback g).obj (Over.mk f)) ⟶ Over.mk f
  body: (mapPullbackAdj g).counit.app Over.mk f

中文:
缩写 fst'
  签名: : (Over.map g).obj ((pullback g).obj (Over.mk f)) ⟶ Over.mk f
  定义体: (mapPullbackAdj g).counit.app Over.mk f

Depends on / 依赖: Over.mk, counit, counit.app, mapPullbackAdj
-/
abbrev fst' : (Over.map g).obj ((pullback g).obj (Over.mk f)) ⟶ Over.mk f :=
(mapPullbackAdj g).counit.app Over.mk f

/-- The first projection from the chosen pullback along `g` of `f` to the domain of `f`. -/
.left abbrev fst : pullbackObj f g ⟶ Y := fst' f g

/--
theorem `fst'_left` / 定理 `fst'_left`

English:
theorem fst'_left
  statement: (fst' f g).left = fst f g
  proof: rfl

中文:
定理 fst'_left
  结论: (fst' f g).left = fst f g
  证明: rfl
-/
theorem fst'_left : (fst' f g).left = fst f g := rfl

/-- The second projection from the chosen pullback along `g` of `f` to the domain of `g`. -/
.hom abbrev snd : pullbackObj f g ⟶ Z := (pullback g).obj (Over.mk f)

/--
Definition of `snd'` / `snd'` 的定义

English:
abbreviation snd'
  signature: : (Over.map g).obj ((pullback g).obj (Over.mk f)) ⟶ (Over.mk g)
  body: Over.homMk (snd f g)

中文:
缩写 snd'
  签名: : (Over.map g).obj ((pullback g).obj (Over.mk f)) ⟶ (Over.mk g)
  定义体: Over.homMk (snd f g)

Depends on / 依赖: Over.homMk
-/
abbrev snd' : (Over.map g).obj ((pullback g).obj (Over.mk f)) ⟶ (Over.mk g) :=
  Over.homMk (snd f g)

/--
theorem `snd'_left` / 定理 `snd'_left`

English:
theorem snd'_left
  statement: (snd' f g).left = snd f g
  proof: rfl

中文:
定理 snd'_left
  结论: (snd' f g).left = snd f g
  证明: rfl
-/
theorem snd'_left : (snd' f g).left = snd f g := rfl

variable {f g}

@[reassoc]
/--
theorem `condition` / 定理 `condition`

English:
theorem condition
  statement: fst f g ≫ f = snd f g ≫ g
  proof: Over.w (fst' f g)

中文:
定理 condition
  结论: fst f g ≫ f = snd f g ≫ g
  证明: Over.w (fst' f g)

Depends on / 依赖: Over.w
-/
theorem condition : fst f g ≫ f = snd f g ≫ g :=
  Over.w (fst' f g)

variable (f g) in
@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {W : C} {φ₁ φ₂ : W ⟶ pullbackObj f g} (h₁ : φ₁ ≫ fst _ _ = φ₂ ≫ fst _ _)
  proof: by
  let adj := mapPullbackAdj g
  let U : Over Z := Over.mk (φ₁ ≫ snd f g)
  let φ₁' : U ⟶ (pullback g).obj (Over.mk f) := Over.homMk φ₁
  let φ₂' : U ⟶ (pullback g).obj (Over.mk f) := Over.homMk φ₂ (by simpa using! h₂.symm)
  have : φ₁' = φ₂' := by
    apply (adj.homEquiv U _).symm.injective
    a

中文:
定理 hom_ext
  结论: {W : C} {φ₁ φ₂ : W ⟶ pullbackObj f g} (h₁ : φ₁ ≫ fst _ _ = φ₂ ≫ fst _ _)
  证明: by
  let adj := mapPullbackAdj g
  let U : Over Z := Over.mk (φ₁ ≫ snd f g)
  let φ₁' : U ⟶ (pullback g).obj (Over.mk f) := Over.homMk φ₁
  let φ₂' : U ⟶ (pullback g).obj (Over.mk f) := Over.homMk φ₂ (by simpa using! h₂.symm)
  have : φ₁' = φ₂' := by
    apply (adj.homEquiv U _).symm.injective
    a

Depends on / 依赖: CommaMorphism, CommaMorphism.left, Over.forget, Over.homMk, Over.mk, adj.homEquiv, congr_arg, forget, homEquiv, injective, mapPullbackAdj, map_injective, pullback, symm.injective
-/
theorem hom_ext {W : C} {φ₁ φ₂ : W ⟶ pullbackObj f g} (h₁ : φ₁ ≫ fst _ _ = φ₂ ≫ fst _ _)
    (h₂ : φ₁ ≫ snd _ _ = φ₂ ≫ snd _ _) :
    φ₁ = φ₂ := by
  let adj := mapPullbackAdj g
  let U : Over Z := Over.mk (φ₁ ≫ snd f g)
  let φ₁' : U ⟶ (pullback g).obj (Over.mk f) := Over.homMk φ₁
  let φ₂' : U ⟶ (pullback g).obj (Over.mk f) := Over.homMk φ₂ (by simpa using! h₂.symm)
  have : φ₁' = φ₂' := by
    apply (adj.homEquiv U _).symm.injective
    apply (Over.forget X).map_injective
    simpa using! h₁
  exact congr_arg CommaMorphism.left this

section Lift

variable {W : C} (a : W ⟶ Y) (b : W ⟶ Z) (h : a ≫ f = b ≫ g := by cat_disch)

set_option backward.privateInPublic true in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : W ⟶ pullbackObj f g
  body: (((mapPullbackAdj g).homEquiv (Over.mk b) (Over.mk f)) (Over.homMk a)).left

中文:
定义 lift
  签名: : W ⟶ pullbackObj f g
  定义体: (((mapPullbackAdj g).homEquiv (Over.mk b) (Over.mk f)) (Over.homMk a)).left

Depends on / 依赖: Over.homMk, Over.mk, homEquiv, mapPullbackAdj
-/
def lift : W ⟶ pullbackObj f g :=
  (((mapPullbackAdj g).homEquiv (Over.mk b) (Over.mk f)) (Over.homMk a)).left

set_option backward.privateInPublic true in
@[reassoc (attr := simp)]
/--
theorem `lift_fst` / 定理 `lift_fst`

English:
theorem lift_fst
  statement: lift a b h ≫ fst f g = a
  proof: by
  let adj := mapPullbackAdj g
  let a' : (Over.map g).obj (Over.mk b) ⟶ Over.mk f := Over.homMk a h
  have : (Over.map g).map (adj.homEquiv (.mk b) (.mk f) (Over.homMk a)) ≫ fst' f g = a' := by
    simp only [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply, adj, a']
  exact congr_arg CommaMo

中文:
定理 lift_fst
  结论: lift a b h ≫ fst f g = a
  证明: by
  let adj := mapPullbackAdj g
  let a' : (Over.map g).obj (Over.mk b) ⟶ Over.mk f := Over.homMk a h
  have : (Over.map g).map (adj.homEquiv (.mk b) (.mk f) (Over.homMk a)) ≫ fst' f g = a' := by
    simp only [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply, adj, a']
  exact congr_arg CommaMo

Depends on / 依赖: Adjunction, Adjunction.homEquiv_counit, CommaMorphism, CommaMorphism.left, Equiv.symm_apply_apply, Over.homMk, Over.map, Over.mk, adj.homEquiv, congr_arg, homEquiv, homEquiv_counit, mapPullbackAdj, symm_apply_apply
-/
theorem lift_fst : lift a b h ≫ fst f g = a := by
  let adj := mapPullbackAdj g
  let a' : (Over.map g).obj (Over.mk b) ⟶ Over.mk f := Over.homMk a h
  have : (Over.map g).map (adj.homEquiv (.mk b) (.mk f) (Over.homMk a)) ≫ fst' f g = a' := by
    simp only [← Adjunction.homEquiv_counit, Equiv.symm_apply_apply, adj, a']
  exact congr_arg CommaMorphism.left this

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
@[reassoc (attr := simp)]
/--
theorem `lift_snd` / 定理 `lift_snd`

English:
theorem lift_snd
  statement: lift a b h ≫ snd f g = b
  proof: by
  simp [lift]

中文:
定理 lift_snd
  结论: lift a b h ≫ snd f g = b
  证明: by
  simp [lift]
-/
theorem lift_snd : lift a b h ≫ snd f g = b := by
  simp [lift]

end Lift

section PullbackMap

variable (f g)

/--
Definition of `pullbackMap` / `pullbackMap` 的定义

English:
definition pullbackMap
  signature: {Y' Z' X' : C} (f' : Y' ⟶ X') (g' : Z' ⟶ X') [ChosenPullbacksAlong g']
  body: lift (fst f' g' ≫ γ₁) (snd f' g' ≫ γ₂)
    (by rw [assoc, ← comm₁, ← assoc, condition, assoc, comm₂, assoc])

中文:
定义 pullbackMap
  签名: {Y' Z' X' : C} (f' : Y' ⟶ X') (g' : Z' ⟶ X') [ChosenPullbacksAlong g']
  定义体: lift (fst f' g' ≫ γ₁) (snd f' g' ≫ γ₂)
    (by rw [assoc, ← comm₁, ← assoc, condition, assoc, comm₂, assoc])

Depends on / 依赖: cat_disch, condition, pullbackObj
-/
def pullbackMap {Y' Z' X' : C} (f' : Y' ⟶ X') (g' : Z' ⟶ X') [ChosenPullbacksAlong g']
    (γ₁ : Y' ⟶ Y) (γ₂ : Z' ⟶ Z) (γ₃ : X' ⟶ X)
    (comm₁ : f' ≫ γ₃ = γ₁ ≫ f := by cat_disch) (comm₂ : g' ≫ γ₃ = γ₂ ≫ g := by cat_disch) :
    pullbackObj f' g' ⟶ pullbackObj f g :=
  lift (fst f' g' ≫ γ₁) (snd f' g' ≫ γ₂)
    (by rw [assoc, ← comm₁, ← assoc, condition, assoc, comm₂, assoc])

variable {f g}

@[reassoc (attr := simp)]
/--
theorem `pullbackMap_fst` / 定理 `pullbackMap_fst`

English:
theorem pullbackMap_fst
  statement: {Y' Z' X' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} [ChosenPullbacksAlong g']
  proof: by
  simp only [pullbackMap, lift_fst]

@[reassoc (attr := simp)]

中文:
定理 pullbackMap_fst
  结论: {Y' Z' X' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} [ChosenPullbacksAlong g']
  证明: by
  simp only [pullbackMap, lift_fst]

@[reassoc (attr := simp)]

Depends on / 依赖: cat_disch, lift_fst, pullbackMap
-/
theorem pullbackMap_fst {Y' Z' X' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} [ChosenPullbacksAlong g']
    {γ₁ : Y' ⟶ Y} {γ₂ : Z' ⟶ Z} {γ₃ : X' ⟶ X} (comm₁ comm₂ := by cat_disch) :
    pullbackMap f g f' g' γ₁ γ₂ γ₃ comm₁ comm₂ ≫ fst f g = fst f' g' ≫ γ₁ := by
  simp only [pullbackMap, lift_fst]

@[reassoc (attr := simp)]
/--
theorem `pullbackMap_snd` / 定理 `pullbackMap_snd`

English:
theorem pullbackMap_snd
  statement: {Y' Z' X' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} [ChosenPullbacksAlong g']
  proof: by
  simp only [pullbackMap, lift_snd]

@[simp]

中文:
定理 pullbackMap_snd
  结论: {Y' Z' X' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} [ChosenPullbacksAlong g']
  证明: by
  simp only [pullbackMap, lift_snd]

@[simp]

Depends on / 依赖: cat_disch, lift_snd, pullbackMap
-/
theorem pullbackMap_snd {Y' Z' X' : C} {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} [ChosenPullbacksAlong g']
    {γ₁ : Y' ⟶ Y} {γ₂ : Z' ⟶ Z} {γ₃ : X' ⟶ X} (comm₁ comm₂ := by cat_disch) :
    pullbackMap f g f' g' γ₁ γ₂ γ₃ comm₁ comm₂ ≫ snd f g = snd f' g' ≫ γ₂ := by
  simp only [pullbackMap, lift_snd]

@[simp]
/--
theorem `pullbackMap_id` / 定理 `pullbackMap_id`

English:
theorem pullbackMap_id
  statement: pullbackMap f g f g (𝟙 Y) (𝟙 Z) (𝟙 X) = 𝟙 _
  proof: by
  cat_disch

@[reassoc (attr := simp)]

中文:
定理 pullbackMap_id
  结论: pullbackMap f g f g (𝟙 Y) (𝟙 Z) (𝟙 X) = 𝟙 _
  证明: by
  cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: cat_disch
-/
theorem pullbackMap_id : pullbackMap f g f g (𝟙 Y) (𝟙 Z) (𝟙 X) = 𝟙 _ := by
  cat_disch

@[reassoc (attr := simp)]
/--
theorem `pullbackMap_comp` / 定理 `pullbackMap_comp`

English:
theorem pullbackMap_comp
  statement: {Y' Z' X' Y'' Z'' X'' : C}
  proof: by
  cat_disch

中文:
定理 pullbackMap_comp
  结论: {Y' Z' X' Y'' Z'' X'' : C}
  证明: by
  cat_disch

Depends on / 依赖: cat_disch, pullbackMap, reassoc_of
-/
theorem pullbackMap_comp {Y' Z' X' Y'' Z'' X'' : C}
    {f' : Y' ⟶ X'} {g' : Z' ⟶ X'} {f'' : Y'' ⟶ X''} {g'' : Z'' ⟶ X''}
    [ChosenPullbacksAlong g'] [ChosenPullbacksAlong g'']
    {γ₁ : Y' ⟶ Y} {γ₂ : Z' ⟶ Z} {γ₃ : X' ⟶ X}
    {δ₁ : Y'' ⟶ Y'} {δ₂ : Z'' ⟶ Z'} {δ₃ : X'' ⟶ X'}
    (comm₁ comm₂ comm₁' comm₂' := by cat_disch) :
    pullbackMap f' g' f'' g'' δ₁ δ₂ δ₃ comm₁' comm₂' ≫
      pullbackMap f g f' g' γ₁ γ₂ γ₃ comm₁ comm₂ =
    pullbackMap f g f'' g'' (δ₁ ≫ γ₁) (δ₂ ≫ γ₂) (δ₃ ≫ γ₃)
      (by rw [reassoc_of% comm₁', comm₁, assoc]) (by rw [reassoc_of% comm₂', comm₂, assoc]) := by
  cat_disch

end PullbackMap

variable (f g)

/--
Definition of `pullbackCone` / `pullbackCone` 的定义

English:
definition pullbackCone
  signature: : PullbackCone f g
  body: PullbackCone.mk (fst f g) (snd f g) (by rw [condition])

中文:
定义 pullbackCone
  签名: : PullbackCone f g
  定义体: PullbackCone.mk (fst f g) (snd f g) (by rw [condition])

Depends on / 依赖: PullbackCone, PullbackCone.mk, condition
-/
def pullbackCone : PullbackCone f g :=
  PullbackCone.mk (fst f g) (snd f g) (by rw [condition])

/--
lemma `pullbackCone_fst` / 引理 `pullbackCone_fst`

English:
lemma pullbackCone_fst
  statement: (pullbackCone f g).fst = fst f g
  proof: rfl

中文:
引理 pullbackCone_fst
  结论: (pullbackCone f g).fst = fst f g
  证明: rfl
-/
@[simp] lemma pullbackCone_fst : (pullbackCone f g).fst = fst f g := rfl

/--
lemma `pullbackCone_snd` / 引理 `pullbackCone_snd`

English:
lemma pullbackCone_snd
  statement: (pullbackCone f g).snd = snd f g
  proof: rfl

中文:
引理 pullbackCone_snd
  结论: (pullbackCone f g).snd = snd f g
  证明: rfl
-/
@[simp] lemma pullbackCone_snd : (pullbackCone f g).snd = snd f g := rfl

/--
Definition of `isLimitPullbackCone` / `isLimitPullbackCone` 的定义

English:
definition isLimitPullbackCone
  signature: :
  body: PullbackCone.IsLimit.mk condition (fun s => lift s.fst s.snd s.condition)
    (by cat_disch) (by cat_disch) (by cat_disch)

中文:
定义 isLimitPullbackCone
  签名: :
  定义体: PullbackCone.IsLimit.mk condition (fun s => lift s.fst s.snd s.condition)
    (by cat_disch) (by cat_disch) (by cat_disch)

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.mk, cat_disch, condition, s.condition, s.fst, s.snd
-/
def isLimitPullbackCone :
    IsLimit (pullbackCone f g) :=
  PullbackCone.IsLimit.mk condition (fun s => lift s.fst s.snd s.condition)
    (by cat_disch) (by cat_disch) (by cat_disch)

/--
theorem `isPullback` / 定理 `isPullback`

English:
theorem isPullback
  statement: IsPullback (fst f g) (snd f g) f g where
  proof: condition
  isLimit' := ⟨isLimitPullbackCone f g⟩

中文:
定理 isPullback
  结论: 是拉回 (fst f g) (snd f g) f g where
  证明: condition
  isLimit' := ⟨isLimitPullbackCone f g⟩

Depends on / 依赖: condition
-/
theorem isPullback : IsPullback (fst f g) (snd f g) f g where
  w := condition
  isLimit' := ⟨isLimitPullbackCone f g⟩

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] condition in
/-- If `g` has a chosen pullback, then `Over.ChosenPullbacksAlong.fst f g` has a chosen pullback. -/
@[instance_reducible]
/--
Definition of `chosenPullbacksAlongFst` / `chosenPullbacksAlongFst` 的定义

English:
definition chosenPullbacksAlongFst
  signature: : ChosenPullbacksAlong (fst f g) where
  body: Over.mk (pullbackMap _ _ _ _ W.hom (𝟙 _) (𝟙 _))
  pullback.map {W' W} k := Over.homMk (lift (fst _ g ≫ k.left) (snd _ g)) _
  mapPullbackAdj.unit.app Q := Over.homMk (lift (𝟙 _) (Q.hom ≫ snd _ _))
  mapPullbackAdj.counit.app W := Over.homMk (fst _ g)

中文:
定义 chosenPullbacksAlongFst
  签名: : ChosenPullbacksAlong (fst f g) where
  定义体: Over.mk (pullbackMap _ _ _ _ W.hom (𝟙 _) (𝟙 _))
  pullback.map {W' W} k := Over.homMk (lift (fst _ g ≫ k.left) (snd _ g)) _
  mapPullbackAdj.unit.app Q := Over.homMk (lift (𝟙 _) (Q.hom ≫ snd _ _))
  mapPullbackAdj.counit.app W := Over.homMk (fst _ g)

Depends on / 依赖: Over.mk, W.hom, pullbackMap
-/
def chosenPullbacksAlongFst : ChosenPullbacksAlong (fst f g) where
  pullback.obj W := Over.mk (pullbackMap _ _ _ _ W.hom (𝟙 _) (𝟙 _))
  pullback.map {W' W} k := Over.homMk (lift (fst _ g ≫ k.left) (snd _ g)) _
  mapPullbackAdj.unit.app Q := Over.homMk (lift (𝟙 _) (Q.hom ≫ snd _ _))
  mapPullbackAdj.counit.app W := Over.homMk (fst _ g)

/--
Instance `hasPullbackAlong` / 实例 `hasPullbackAlong`

English:
instance hasPullbackAlong
  signature: : HasPullbacksAlong g
  body: fun f => (isPullback f g).hasPullback

中文:
实例 hasPullbackAlong
  签名: : 有PullbacksAlong g
  定义体: fun f => (isPullback f g).hasPullback

Depends on / 依赖: hasPullback, isPullback
-/
instance hasPullbackAlong : HasPullbacksAlong g := fun f => (isPullback f g).hasPullback

/--
Instance `hasPullbacks` / 实例 `hasPullbacks`

English:
instance hasPullbacks
  signature: [ChosenPullbacks C]
  body: hasPullbacks_of_hasLimit_cospan _

中文:
实例 hasPullbacks
  签名: [ChosenPullbacks C]
  定义体: hasPullbacks_of_hasLimit_cospan _

Depends on / 依赖: hasPullbacks_of_hasLimit_cospan
-/
instance hasPullbacks [ChosenPullbacks C] : HasPullbacks C :=
  hasPullbacks_of_hasLimit_cospan _

/--
Definition of `pullbackIsoOverPullback` / `pullbackIsoOverPullback` 的定义

English:
definition pullbackIsoOverPullback
  signature: : ChosenPullbacksAlong.pullback g ≅ Over.pullback g
  body: (ChosenPullbacksAlong.mapPullbackAdj g).rightAdjointUniq (Over.mapPullbackAdj g)

@[reassoc (attr := simp)]

中文:
定义 pullbackIsoOverPullback
  签名: : ChosenPullbacksAlong.pullback g ≅ Over.pullback g
  定义体: (ChosenPullbacksAlong.mapPullbackAdj g).rightAdjointUniq (Over.mapPullbackAdj g)

@[reassoc (attr := simp)]

Depends on / 依赖: ChosenPullbacksAlong, ChosenPullbacksAlong.mapPullbackAdj, Over.mapPullbackAdj, mapPullbackAdj, rightAdjointUniq
-/
noncomputable def pullbackIsoOverPullback : ChosenPullbacksAlong.pullback g ≅ Over.pullback g :=
  (ChosenPullbacksAlong.mapPullbackAdj g).rightAdjointUniq (Over.mapPullbackAdj g)

@[reassoc (attr := simp)]
/--
theorem `pullbackIsoOverPullback_hom_app_comp_fst` / 定理 `pullbackIsoOverPullback_hom_app_comp_fst`

English:
theorem pullbackIsoOverPullback_hom_app_comp_fst
  given: (T : Over X)
  proof: by
  simpa using! (Over.forget _).congr_map
    ((ChosenPullbacksAlong.mapPullbackAdj g).rightAdjointUniq_hom_app_counit
      (Over.mapPullbackAdj g) T)

@[reassoc (attr := simp)]

中文:
定理 pullbackIsoOverPullback_hom_app_comp_fst
  条件: (T : Over X)
  证明: by
  simpa using! (Over.forget _).congr_map
    ((ChosenPullbacksAlong.mapPullbackAdj g).rightAdjointUniq_hom_app_counit
      (Over.mapPullbackAdj g) T)

@[reassoc (attr := simp)]

Depends on / 依赖: ChosenPullbacksAlong, ChosenPullbacksAlong.mapPullbackAdj, Over.forget, Over.mapPullbackAdj, congr_map, forget, mapPullbackAdj, rightAdjointUniq_hom_app_counit
-/
theorem pullbackIsoOverPullback_hom_app_comp_fst (T : Over X) :
    ((pullbackIsoOverPullback g).hom.app T).left ≫ pullback.fst _ _ = fst _ _ := by
  simpa using! (Over.forget _).congr_map
    ((ChosenPullbacksAlong.mapPullbackAdj g).rightAdjointUniq_hom_app_counit
      (Over.mapPullbackAdj g) T)

@[reassoc (attr := simp)]
/--
theorem `pullbackIsoOverPullback_hom_app_comp_snd` / 定理 `pullbackIsoOverPullback_hom_app_comp_snd`

English:
theorem pullbackIsoOverPullback_hom_app_comp_snd
  given: (T : Over X)
  proof: Over.w ((pullbackIsoOverPullback g).hom.app T)

@[reassoc (attr := simp)]

中文:
定理 pullbackIsoOverPullback_hom_app_comp_snd
  条件: (T : Over X)
  证明: Over.w ((pullbackIsoOverPullback g).hom.app T)

@[reassoc (attr := simp)]

Depends on / 依赖: Over.w, hom.app, pullbackIsoOverPullback
-/
theorem pullbackIsoOverPullback_hom_app_comp_snd (T : Over X) :
    ((pullbackIsoOverPullback g).hom.app T).left ≫ pullback.snd _ _ = snd _ _ :=
  Over.w ((pullbackIsoOverPullback g).hom.app T)

@[reassoc (attr := simp)]
/--
theorem `pullbackIsoOverPullback_inv_app_comp_fst` / 定理 `pullbackIsoOverPullback_inv_app_comp_fst`

English:
theorem pullbackIsoOverPullback_inv_app_comp_fst
  given: (T : Over X)
  proof: by
  simp [← pullbackIsoOverPullback_hom_app_comp_fst, ← Over.comp_left_assoc]

@[reassoc (attr := simp)]

中文:
定理 pullbackIsoOverPullback_inv_app_comp_fst
  条件: (T : Over X)
  证明: by
  simp [← pullbackIsoOverPullback_hom_app_comp_fst, ← Over.comp_left_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: Over.comp_left_assoc, comp_left_assoc, pullbackIsoOverPullback_hom_app_comp_fst
-/
theorem pullbackIsoOverPullback_inv_app_comp_fst (T : Over X) :
    ((pullbackIsoOverPullback g).inv.app T).left ≫ fst _ _ = pullback.fst _ _ := by
  simp [← pullbackIsoOverPullback_hom_app_comp_fst, ← Over.comp_left_assoc]

@[reassoc (attr := simp)]
/--
theorem `pullbackIsoOverPullback_inv_app_comp_snd` / 定理 `pullbackIsoOverPullback_inv_app_comp_snd`

English:
theorem pullbackIsoOverPullback_inv_app_comp_snd
  given: (T : Over X)
  proof: Over.w ((pullbackIsoOverPullback g).inv.app T)

中文:
定理 pullbackIsoOverPullback_inv_app_comp_snd
  条件: (T : Over X)
  证明: Over.w ((pullbackIsoOverPullback g).inv.app T)

Depends on / 依赖: Over.w, inv.app, pullbackIsoOverPullback
-/
theorem pullbackIsoOverPullback_inv_app_comp_snd (T : Over X) :
    ((pullbackIsoOverPullback g).inv.app T).left ≫ snd _ _ = pullback.snd _ _ :=
  Over.w ((pullbackIsoOverPullback g).inv.app T)

end PullbackFromChosenPullbacksAlongs

end ChosenPullbacksAlong

end CategoryTheory
