/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Geometry.RingedSpace.Stalks

/-!
# The category of locally ringed spaces

We define (bundled) locally ringed spaces (as `SheafedSpace CommRing` along with the fact that the
stalks are local rings), and morphisms between these (morphisms in `SheafedSpace` with
`IsLocalHom` on the stalk maps).
-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

universe u

open CategoryTheory

open TopCat

open TopologicalSpace Topology

open Opposite

open CategoryTheory.Category CategoryTheory.Functor

namespace AlgebraicGeometry

/--
Definition of `LocallyRingedSpace` / `LocallyRingedSpace` 的定义

English:
structure LocallyRingedSpace
  parameters: extends SheafedSpace CommRingCat.{u}
  extends: SheafedSpace CommRingCat.{u}
  axioms and operations (1):
    - isLocalRing : forall x, IsLocalRing (presheaf.stalk x)

中文:
结构 LocallyRingedSpace
  参数: extends SheafedSpace CommRingCat.{u}
  继承: SheafedSpace CommRingCat.{u}
  公理与运算 (1 个):
    - isLocalRing : 对任意 x, IsLocalRing (presheaf.stalk x)
-/
structure LocallyRingedSpace extends SheafedSpace CommRingCat.{u} where
  /-- Stalks of a locally ringed space are local rings. -/
  isLocalRing : forall x, IsLocalRing (presheaf.stalk x)

attribute [instance] LocallyRingedSpace.isLocalRing

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/--
Definition of `toRingedSpace` / `toRingedSpace` 的定义

English:
abbreviation toRingedSpace
  signature: : RingedSpace
  body: X.toSheafedSpace

中文:
缩写 toRingedSpace
  签名: : RingedSpace
  定义体: X.toSheafedSpace

Depends on / 依赖: X.toSheafedSpace, toSheafedSpace
-/
abbrev toRingedSpace : RingedSpace :=
  X.toSheafedSpace

/-- The underlying topological space of a locally ringed space. -/
@[implicit_reducible]
/--
Definition of `toTopCat` / `toTopCat` 的定义

English:
definition toTopCat
  signature: : TopCat
  body: X.1.carrier

中文:
定义 toTopCat
  签名: : TopCat
  定义体: X.1.carrier

Depends on / 依赖: carrier
-/
def toTopCat : TopCat :=
  X.1.carrier

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort LocallyRingedSpace (Type u)
  body: ⟨fun X : LocallyRingedSpace => (X.toTopCat : Type _)⟩

中文:
实例 :
  签名: CoeSort LocallyRingedSpace (类型u)
  定义体: ⟨fun X : LocallyRingedSpace => (X.toTopCat : Type _)⟩

Depends on / 依赖: LocallyRingedSpace, X.toTopCat, toTopCat
-/
instance : CoeSort LocallyRingedSpace (Type u) :=
  ⟨fun X : LocallyRingedSpace => (X.toTopCat : Type _)⟩

instance (x : X) : IsLocalRing (X.presheaf.stalk x) :=
  X.isLocalRing x

-- PROJECT: how about a typeclass "HasStructureSheaf" to mediate the 𝒪 notation, rather
-- than defining it over and over for `PresheafedSpace`, `LocallyRingedSpace`, `Scheme`, etc.
/--
Definition of `𝒪` / `𝒪` 的定义

English:
definition 𝒪
  signature: : Sheaf CommRingCat X.toTopCat
  body: X.sheaf

中文:
定义 𝒪
  签名: : Sheaf CommRingCat X.toTopCat
  定义体: X.sheaf

Depends on / 依赖: X.sheaf
-/
def 𝒪 : Sheaf CommRingCat X.toTopCat :=
  X.sheaf

/-- A morphism of locally ringed spaces is a morphism of ringed spaces
such that the morphisms induced on stalks are local ring homomorphisms. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : LocallyRingedSpace.{u})
  extends: X.toPresheafedSpace.Hom Y.toPresheafedSpace
  axioms and operations (1):
    - prop : forall x, IsLocalHom (toHom.stalkMap x).hom

中文:
结构 Hom
  参数: (X Y : LocallyRingedSpace.{u})
  继承: X.toPresheafedSpace.Hom Y.toPresheafedSpace
  公理与运算 (1 个):
    - prop : 对任意 x, IsLocalHom (toHom.stalkMap x).hom
-/
structure Hom (X Y : LocallyRingedSpace.{u}) : Type _
    extends X.toPresheafedSpace.Hom Y.toPresheafedSpace where
  /-- the underlying morphism induces a local ring homomorphism on stalks -/
  prop : forall x, IsLocalHom (toHom.stalkMap x).hom

/--
Definition of `Hom.toShHom` / `Hom.toShHom` 的定义

English:
abbreviation Hom.toShHom
  signature: {X Y : LocallyRingedSpace.{u}} (f : X.Hom Y)
  body: InducedCategory.homMk f.1

@[simp]

中文:
缩写 Hom.toShHom
  签名: {X Y : LocallyRingedSpace.{u}} (f : X.Hom Y)
  定义体: InducedCategory.homMk f.1

@[simp]

Depends on / 依赖: InducedCategory, InducedCategory.homMk
-/
abbrev Hom.toShHom {X Y : LocallyRingedSpace.{u}} (f : X.Hom Y) :
  X.toSheafedSpace ⟶ Y.toSheafedSpace := InducedCategory.homMk f.1

@[simp]
/--
lemma `Hom.toShHom_mk` / 引理 `Hom.toShHom_mk`

English:
lemma Hom.toShHom_mk
  statement: {X Y : LocallyRingedSpace.{u}}
  proof: rfl

中文:
引理 Hom.toShHom_mk
  结论: {X Y : LocallyRingedSpace.{u}}
  证明: rfl
-/
lemma Hom.toShHom_mk {X Y : LocallyRingedSpace.{u}}
    (f : X.toPresheafedSpace.Hom Y.toPresheafedSpace) (hf) :
  Hom.toShHom ⟨f, hf⟩ = InducedCategory.homMk f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Quiver LocallyRingedSpace
  body: ⟨Hom⟩

中文:
实例 :
  签名: Quiver LocallyRingedSpace
  定义体: ⟨Hom⟩
-/
instance : Quiver LocallyRingedSpace :=
  ⟨Hom⟩

/--
lemma `Hom.ext'` / 引理 `Hom.ext'`

English:
lemma Hom.ext'
  statement: {X Y : LocallyRingedSpace.{u}} {f g : X ⟶ Y}
  proof: by cases f; cases g; congr

中文:
引理 Hom.ext'
  结论: {X Y : LocallyRingedSpace.{u}} {f g : X ⟶ Y}
  证明: by cases f; cases g; congr
-/
@[ext] lemma Hom.ext' {X Y : LocallyRingedSpace.{u}} {f g : X ⟶ Y}
    (h : f.toHom = g.toHom) :
    f = g := by cases f; cases g; congr

/--
Definition of `Hom.stalkMap` / `Hom.stalkMap` 的定义

English:
definition Hom.stalkMap
  signature: {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X)
  body: f.toShHom.hom.stalkMap x

@[instance]

中文:
定义 Hom.stalkMap
  签名: {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X)
  定义体: f.toShHom.hom.stalkMap x

@[instance]

Depends on / 依赖: f.toShHom.hom.stalkMap, stalkMap, toShHom
-/
noncomputable def Hom.stalkMap {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    Y.presheaf.stalk (f.1.1 x) ⟶ X.presheaf.stalk x :=
  f.toShHom.hom.stalkMap x

@[instance]
/--
theorem `isLocalHomStalkMap` / 定理 `isLocalHomStalkMap`

English:
theorem isLocalHomStalkMap
  given: {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X)
  proof: f.2 x

中文:
定理 isLocalHomStalkMap
  条件: {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X)
  证明: f.2 x
-/
theorem isLocalHomStalkMap {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    IsLocalHom (f.stalkMap x).hom :=
  f.2 x

/--
Instance `isLocalHomStalkMap'` / 实例 `isLocalHomStalkMap'`

English:
instance isLocalHomStalkMap'
  signature: {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X)
  body: isLocalHomStalkMap f x

@[instance]

中文:
实例 isLocalHomStalkMap'
  签名: {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X)
  定义体: isLocalHomStalkMap f x

@[instance]

Depends on / 依赖: isLocalHomStalkMap
-/
instance isLocalHomStalkMap' {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    IsLocalHom (f.toHom.stalkMap x).hom :=
  isLocalHomStalkMap f x

@[instance]
/--
theorem `isLocalHomValStalkMap` / 定理 `isLocalHomValStalkMap`

English:
theorem isLocalHomValStalkMap
  given: {X Y : LocallyRingedSpace.{u}} (f : Hom X Y) (x : X)
  proof: f.2 x

中文:
定理 isLocalHomValStalkMap
  条件: {X Y : LocallyRingedSpace.{u}} (f : Hom X Y) (x : X)
  证明: f.2 x
-/
theorem isLocalHomValStalkMap {X Y : LocallyRingedSpace.{u}} (f : Hom X Y) (x : X) :
    IsLocalHom (f.stalkMap x).hom :=
  f.2 x

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (X : LocallyRingedSpace.{u})
  body: ⟨𝟙 X.toPresheafedSpace, fun x => by dsimp; rw [PresheafedSpace.stalkMap.id]; infer_instance⟩

中文:
定义 id
  签名: (X : LocallyRingedSpace.{u})
  定义体: ⟨𝟙 X.toPresheafedSpace, fun x => by dsimp; rw [PresheafedSpace.stalkMap.id]; infer_instance⟩

Depends on / 依赖: PresheafedSpace, PresheafedSpace.stalkMap.id, X.toPresheafedSpace, infer_instance, stalkMap, toPresheafedSpace
-/
def id (X : LocallyRingedSpace.{u}) : Hom X X :=
  ⟨𝟙 X.toPresheafedSpace, fun x => by dsimp; rw [PresheafedSpace.stalkMap.id]; infer_instance⟩

instance (X : LocallyRingedSpace.{u}) : Inhabited (Hom X X) :=
  ⟨id X⟩

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {X Y Z : LocallyRingedSpace.{u}} (f : Hom X Y) (g : Hom Y Z)
  body: (f.toHom ≫ g.toHom : X.toPresheafedSpace ⟶ Z.toPresheafedSpace)
  prop x := by
    rw [PresheafedSpace.stalkMap.comp]
    apply +allowSynthFailures RingHom.isLocalHom_comp
    all_goals apply isLocalHomValStalkMap

中文:
定义 comp
  签名: {X Y Z : LocallyRingedSpace.{u}} (f : Hom X Y) (g : Hom Y Z)
  定义体: (f.toHom ≫ g.toHom : X.toPresheafedSpace ⟶ Z.toPresheafedSpace)
  prop x := by
    rw [PresheafedSpace.stalkMap.comp]
    apply +allowSynthFailures RingHom.isLocalHom_comp
    all_goals apply isLocalHomValStalkMap

Depends on / 依赖: X.toPresheafedSpace, Z.toPresheafedSpace, f.toHom, g.toHom, toPresheafedSpace
-/
def comp {X Y Z : LocallyRingedSpace.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toHom := (f.toHom ≫ g.toHom : X.toPresheafedSpace ⟶ Z.toPresheafedSpace)
  prop x := by
    rw [PresheafedSpace.stalkMap.comp]
    apply +allowSynthFailures RingHom.isLocalHom_comp
    all_goals apply isLocalHomValStalkMap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category LocallyRingedSpace.{u}
  body: Hom
  id := id
  comp f g := comp f g

中文:
实例 :
  签名: Category LocallyRingedSpace.{u}
  定义体: Hom
  id := id
  comp f g := comp f g
-/
instance : Category LocallyRingedSpace.{u} where
  Hom := Hom
  id := id
  comp f g := comp f g

/-- The forgetful functor from `LocallyRingedSpace` to `SheafedSpace CommRing`. -/
@[simps]
/--
Definition of `forgetToSheafedSpace` / `forgetToSheafedSpace` 的定义

English:
definition forgetToSheafedSpace
  signature: : LocallyRingedSpace.{u} ⥤ SheafedSpace CommRingCat.{u} where
  body: X.toSheafedSpace
  map f := InducedCategory.homMk f.1

中文:
定义 forgetToSheafedSpace
  签名: : LocallyRingedSpace.{u} ⥤ SheafedSpace CommRingCat.{u} where
  定义体: X.toSheafedSpace
  map f := InducedCategory.homMk f.1

Depends on / 依赖: X.toSheafedSpace, toSheafedSpace
-/
def forgetToSheafedSpace : LocallyRingedSpace.{u} ⥤ SheafedSpace CommRingCat.{u} where
  obj X := X.toSheafedSpace
  map f := InducedCategory.homMk f.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: forgetToSheafedSpace.Faithful
  body: by
    ext : 1
    exact congr_arg InducedCategory.Hom.hom h

中文:
实例 :
  签名: forgetToSheafedSpace.Faithful
  定义体: by
    ext : 1
    exact congr_arg InducedCategory.Hom.hom h

Depends on / 依赖: InducedCategory, InducedCategory.Hom.hom, congr_arg
-/
instance : forgetToSheafedSpace.Faithful where
  map_injective h := by
    ext : 1
    exact congr_arg InducedCategory.Hom.hom h

/-- Constructor for morphisms in `LocallyRingedSpace`. -/
@[simps toHom]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {X Y : LocallyRingedSpace.{u}} (f : X.toSheafedSpace ⟶ Y.toSheafedSpace)
  body: f.hom
  prop := by assumption

中文:
定义 homMk
  签名: {X Y : LocallyRingedSpace.{u}} (f : X.toSheafedSpace ⟶ Y.toSheafedSpace)
  定义体: f.hom
  prop := by assumption

Depends on / 依赖: f.hom, infer_instance
-/
def homMk {X Y : LocallyRingedSpace.{u}} (f : X.toSheafedSpace ⟶ Y.toSheafedSpace)
    (h : forall (x : X), IsLocalHom (f.hom.stalkMap x).hom := by infer_instance) : X ⟶ Y where
  toHom := f.hom
  prop := by assumption

/-- The forgetful functor from `LocallyRingedSpace` to `Top`. -/
@[simps!]
/--
Definition of `forgetToTop` / `forgetToTop` 的定义

English:
definition forgetToTop
  signature: : LocallyRingedSpace.{u} ⥤ TopCat.{u}
  body: forgetToSheafedSpace ⋙ SheafedSpace.forget _

@[simp]

中文:
定义 forgetToTop
  签名: : LocallyRingedSpace.{u} ⥤ TopCat.{u}
  定义体: forgetToSheafedSpace ⋙ SheafedSpace.forget _

@[simp]

Depends on / 依赖: SheafedSpace, SheafedSpace.forget, forget, forgetToSheafedSpace
-/
def forgetToTop : LocallyRingedSpace.{u} ⥤ TopCat.{u} :=
  forgetToSheafedSpace ⋙ SheafedSpace.forget _

@[simp]
/--
theorem `id_toHom` / 定理 `id_toHom`

English:
theorem id_toHom
  given: (X : LocallyRingedSpace.{u})
  proof: rfl

@[simp]

中文:
定理 id_toHom
  条件: (X : LocallyRingedSpace.{u})
  证明: rfl

@[simp]
-/
theorem id_toHom (X : LocallyRingedSpace.{u}) :
    Hom.toHom (𝟙 X) = 𝟙 X.toPresheafedSpace :=
  rfl

@[simp]
/--
theorem `comp_toHom` / 定理 `comp_toHom`

English:
theorem comp_toHom
  given: {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

@[simp]

中文:
定理 comp_toHom
  条件: {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl

@[simp]
-/
theorem comp_toHom {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toHom = (f.toHom ≫ g.toHom : X.toPresheafedSpace ⟶ Z.toPresheafedSpace) :=
  rfl

@[simp]
/--
theorem `comp_toShHom` / 定理 `comp_toShHom`

English:
theorem comp_toShHom
  given: {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
定理 comp_toShHom
  条件: {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
theorem comp_toShHom {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toShHom = f.toShHom ≫ g.toShHom :=
  rfl

/--
theorem `id_toShHom'` / 定理 `id_toShHom'`

English:
theorem id_toShHom'
  given: (X : LocallyRingedSpace.{u})
  proof: rfl

中文:
定理 id_toShHom'
  条件: (X : LocallyRingedSpace.{u})
  证明: rfl
-/
@[simp] theorem id_toShHom' (X : LocallyRingedSpace.{u}) :
    Hom.toShHom (𝟙 X) = 𝟙 X.toSheafedSpace :=
  rfl

/--
theorem `comp_base` / 定理 `comp_base`

English:
theorem comp_base
  given: {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
定理 comp_base
  条件: {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
theorem comp_base {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

/--
theorem `comp_c` / 定理 `comp_c`

English:
theorem comp_c
  given: {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
定理 comp_c
  条件: {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
theorem comp_c {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).c = g.c ≫ (Presheaf.pushforward _ g.base).map f.c :=
  rfl

/--
theorem `comp_c_app` / 定理 `comp_c_app`

English:
theorem comp_c_app
  given: {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : (Opens Z)ᵒᵖ)
  proof: rfl

中文:
定理 comp_c_app
  条件: {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : (Opens Z)ᵒᵖ)
  证明: rfl
-/
theorem comp_c_app {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : (Opens Z)ᵒᵖ) :
    (f ≫ g).c.app U = g.c.app U ≫ f.c.app (op <| (Opens.map g.base).obj U.unop) :=
  rfl

/-- Given two locally ringed spaces `X` and `Y`, an isomorphism between `X` and `Y` as _sheafed_
spaces can be lifted to a morphism `X ⟶ Y` as locally ringed spaces.

See also `isoOfSheafedSpaceIso`.
-/
@[simps! toHom]
/--
Definition of `homOfSheafedSpaceHomOfIsIso` / `homOfSheafedSpaceHomOfIsIso` 的定义

English:
definition homOfSheafedSpaceHomOfIsIso
  signature: {X Y : LocallyRingedSpace.{u}}
  body: f.hom
  prop _ :=
    -- Here we need to see that the stalk maps are really local ring homomorphisms.
    -- This can be solved by type class inference, because stalk maps of isomorphisms
    -- are isomorphisms and isomorphisms are local ring homomorphisms.
    inferInstance

中文:
定义 homOfSheafedSpaceHomOfIsIso
  签名: {X Y : LocallyRingedSpace.{u}}
  定义体: f.hom
  prop _ :=
    -- Here we need to see that the stalk maps are really local ring homomorphisms.
    -- This can be solved by type class inference, because stalk maps of isomorphisms
    -- are isomorphisms and isomorphisms are local ring homomorphisms.
    inferInstance

Depends on / 依赖: f.hom
-/
def homOfSheafedSpaceHomOfIsIso {X Y : LocallyRingedSpace.{u}}
    (f : X.toSheafedSpace ⟶ Y.toSheafedSpace) [IsIso f] : X ⟶ Y where
  toHom := f.hom
  prop _ :=
    -- Here we need to see that the stalk maps are really local ring homomorphisms.
    -- This can be solved by type class inference, because stalk maps of isomorphisms
    -- are isomorphisms and isomorphisms are local ring homomorphisms.
    inferInstance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isoOfSheafedSpaceIso` / `isoOfSheafedSpaceIso` 的定义

English:
definition isoOfSheafedSpaceIso
  signature: {X Y : LocallyRingedSpace.{u}} (f : X.toSheafedSpace ≅ Y.toSheafedSpace)
  body: homOfSheafedSpaceHomOfIsIso f.hom
  inv := homOfSheafedSpaceHomOfIsIso f.inv
  hom_inv_id := by
    ext : 1
    dsimp
    rw [← InducedCategory.comp_hom]; rw [f.hom_inv_id]; rw [SheafedSpace.id_hom]
  inv_hom_id := by
    ext : 1
    dsimp
    rw [← InducedCategory.comp_hom]; rw [f.inv_hom_id]; rw [

中文:
定义 isoOfSheafedSpaceIso
  签名: {X Y : LocallyRingedSpace.{u}} (f : X.toSheafedSpace ≅ Y.toSheafedSpace)
  定义体: homOfSheafedSpaceHomOfIsIso f.hom
  inv := homOfSheafedSpaceHomOfIsIso f.inv
  hom_inv_id := by
    ext : 1
    dsimp
    rw [← InducedCategory.comp_hom]; rw [f.hom_inv_id]; rw [SheafedSpace.id_hom]
  inv_hom_id := by
    ext : 1
    dsimp
    rw [← InducedCategory.comp_hom]; rw [f.inv_hom_id]; rw [

Depends on / 依赖: f.hom, homOfSheafedSpaceHomOfIsIso
-/
def isoOfSheafedSpaceIso {X Y : LocallyRingedSpace.{u}} (f : X.toSheafedSpace ≅ Y.toSheafedSpace) :
    X ≅ Y where
  hom := homOfSheafedSpaceHomOfIsIso f.hom
  inv := homOfSheafedSpaceHomOfIsIso f.inv
  hom_inv_id := by
    ext : 1
    dsimp
    rw [← InducedCategory.comp_hom]; rw [f.hom_inv_id]; rw [SheafedSpace.id_hom]
  inv_hom_id := by
    ext : 1
    dsimp
    rw [← InducedCategory.comp_hom]; rw [f.inv_hom_id]; rw [SheafedSpace.id_hom]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: forgetToSheafedSpace.ReflectsIsomorphisms
  body: (isoOfSheafedSpaceIso (asIso (forgetToSheafedSpace.map f))).isIso_hom

中文:
实例 :
  签名: forgetToSheafedSpace.ReflectsIsomorphisms
  定义体: (isoOfSheafedSpaceIso (asIso (forgetToSheafedSpace.map f))).isIso_hom

Depends on / 依赖: forgetToSheafedSpace, forgetToSheafedSpace.map, isIso_hom, isoOfSheafedSpaceIso
-/
instance : forgetToSheafedSpace.ReflectsIsomorphisms where
  reflects f _ := (isoOfSheafedSpaceIso (asIso (forgetToSheafedSpace.map f))).isIso_hom

/--
Instance `is_sheafedSpace_iso` / 实例 `is_sheafedSpace_iso`

English:
instance is_sheafedSpace_iso
  signature: {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [IsIso f]
  body: LocallyRingedSpace.forgetToSheafedSpace.map_isIso f

中文:
实例 is_sheafedSpace_iso
  签名: {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [IsIso f]
  定义体: LocallyRingedSpace.forgetToSheafedSpace.map_isIso f

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.forgetToSheafedSpace.map_isIso, forgetToSheafedSpace, map_isIso
-/
instance is_sheafedSpace_iso {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [IsIso f] :
    IsIso f.toShHom :=
  LocallyRingedSpace.forgetToSheafedSpace.map_isIso f

/-- The restriction of a locally ringed space along an open embedding.
-/
@[simps!]
/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: {U : TopCat.{u}} (X : LocallyRingedSpace.{u}) {f : U ⟶ X.toTopCat}
  body: by
    intro x
    -- We show that the stalk of the restriction is isomorphic to the original stalk,
    apply @RingEquiv.isLocalRing _ _ _ (X.isLocalRing (f x))
    exact (X.restrictStalkIso h x).symm.commRingCatIsoToRingEquiv
  toSheafedSpace := X.toSheafedSpace.restrict h

中文:
定义 restrict
  签名: {U : TopCat.{u}} (X : LocallyRingedSpace.{u}) {f : U ⟶ X.toTopCat}
  定义体: by
    intro x
    -- We show that the stalk of the restriction is isomorphic to the original stalk,
    apply @RingEquiv.isLocalRing _ _ _ (X.isLocalRing (f x))
    exact (X.restrictStalkIso h x).symm.commRingCatIsoToRingEquiv
  toSheafedSpace := X.toSheafedSpace.restrict h
-/
def restrict {U : TopCat.{u}} (X : LocallyRingedSpace.{u}) {f : U ⟶ X.toTopCat}
    (h : IsOpenEmbedding f) : LocallyRingedSpace where
  isLocalRing := by
    intro x
    -- We show that the stalk of the restriction is isomorphic to the original stalk,
    apply @RingEquiv.isLocalRing _ _ _ (X.isLocalRing (f x))
    exact (X.restrictStalkIso h x).symm.commRingCatIsoToRingEquiv
  toSheafedSpace := X.toSheafedSpace.restrict h

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofRestrict` / `ofRestrict` 的定义

English:
definition ofRestrict
  signature: {U : TopCat.{u}} (X : LocallyRingedSpace.{u})
  body: ⟨X.toPresheafedSpace.ofRestrict h, fun _ => inferInstance⟩

中文:
定义 ofRestrict
  签名: {U : TopCat.{u}} (X : LocallyRingedSpace.{u})
  定义体: ⟨X.toPresheafedSpace.ofRestrict h, fun _ => inferInstance⟩

Depends on / 依赖: X.toPresheafedSpace.ofRestrict, ofRestrict, toPresheafedSpace
-/
def ofRestrict {U : TopCat.{u}} (X : LocallyRingedSpace.{u})
    {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f) : X.restrict h ⟶ X :=
  ⟨X.toPresheafedSpace.ofRestrict h, fun _ => inferInstance⟩

/--
Definition of `restrictTopIso` / `restrictTopIso` 的定义

English:
definition restrictTopIso
  signature: (X : LocallyRingedSpace.{u})
  body: isoOfSheafedSpaceIso X.toSheafedSpace.restrictTopIso

中文:
定义 restrictTopIso
  签名: (X : LocallyRingedSpace.{u})
  定义体: isoOfSheafedSpaceIso X.toSheafedSpace.restrictTopIso

Depends on / 依赖: X.toSheafedSpace.restrictTopIso, isoOfSheafedSpaceIso, restrictTopIso, toSheafedSpace
-/
def restrictTopIso (X : LocallyRingedSpace.{u}) :
    X.restrict (Opens.isOpenEmbedding ⊤) ≅ X :=
  isoOfSheafedSpaceIso X.toSheafedSpace.restrictTopIso

/--
Definition of `Γ` / `Γ` 的定义

English:
definition Γ
  signature: : LocallyRingedSpace.{u}ᵒᵖ ⥤ CommRingCat.{u}
  body: forgetToSheafedSpace.op ⋙ SheafedSpace.Γ

中文:
定义 Γ
  签名: : LocallyRingedSpace.{u}ᵒᵖ ⥤ CommRingCat.{u}
  定义体: forgetToSheafedSpace.op ⋙ SheafedSpace.Γ

Depends on / 依赖: SheafedSpace, forgetToSheafedSpace, forgetToSheafedSpace.op
-/
def Γ : LocallyRingedSpace.{u}ᵒᵖ ⥤ CommRingCat.{u} :=
  forgetToSheafedSpace.op ⋙ SheafedSpace.Γ

/--
theorem `Γ_def` / 定理 `Γ_def`

English:
theorem Γ_def
  statement: Γ = forgetToSheafedSpace.op ⋙ SheafedSpace.Γ
  proof: rfl

@[simp]

中文:
定理 Γ_def
  结论: Γ = forgetToSheafedSpace.op ⋙ SheafedSpace.Γ
  证明: rfl

@[simp]
-/
theorem Γ_def : Γ = forgetToSheafedSpace.op ⋙ SheafedSpace.Γ :=
  rfl

@[simp]
/--
theorem `Γ_obj` / 定理 `Γ_obj`

English:
theorem Γ_obj
  given: (X : LocallyRingedSpace.{u}ᵒᵖ)
  statement: Γ.obj X = X.unop.presheaf.obj (op ⊤)
  proof: rfl

中文:
定理 Γ_obj
  条件: (X : LocallyRingedSpace.{u}ᵒᵖ)
  结论: Γ.obj X = X.unop.presheaf.obj (op ⊤)
  证明: rfl
-/
theorem Γ_obj (X : LocallyRingedSpace.{u}ᵒᵖ) : Γ.obj X = X.unop.presheaf.obj (op ⊤) :=
  rfl

/--
theorem `Γ_obj_op` / 定理 `Γ_obj_op`

English:
theorem Γ_obj_op
  given: (X : LocallyRingedSpace.{u})
  statement: Γ.obj (op X) = X.presheaf.obj (op ⊤)
  proof: rfl

@[simp]

中文:
定理 Γ_obj_op
  条件: (X : LocallyRingedSpace.{u})
  结论: Γ.obj (op X) = X.presheaf.obj (op ⊤)
  证明: rfl

@[simp]
-/
theorem Γ_obj_op (X : LocallyRingedSpace.{u}) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl

@[simp]
/--
theorem `Γ_map` / 定理 `Γ_map`

English:
theorem Γ_map
  given: {X Y : LocallyRingedSpace.{u}ᵒᵖ} (f : X ⟶ Y)
  statement: Γ.map f = f.unop.c.app (op ⊤)
  proof: rfl

中文:
定理 Γ_map
  条件: {X Y : LocallyRingedSpace.{u}ᵒᵖ} (f : X ⟶ Y)
  结论: Γ.map f = f.unop.c.app (op ⊤)
  证明: rfl
-/
theorem Γ_map {X Y : LocallyRingedSpace.{u}ᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.c.app (op ⊤) :=
  rfl

/--
theorem `Γ_map_op` / 定理 `Γ_map_op`

English:
theorem Γ_map_op
  given: {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
  statement: Γ.map f.op = f.c.app (op ⊤)
  proof: rfl

中文:
定理 Γ_map_op
  条件: {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
  结论: Γ.map f.op = f.c.app (op ⊤)
  证明: rfl
-/
theorem Γ_map_op {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl

/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: : LocallyRingedSpace.{u} where
  body: TopCat.of PEmpty
  presheaf := (CategoryTheory.Functor.const _).obj (CommRingCat.of PUnit)
  IsSheaf := Presheaf.isSheaf_of_isTerminal _ CommRingCat.punitIsTerminal
  isLocalRing x := PEmpty.elim x

中文:
定义 empty
  签名: : LocallyRingedSpace.{u} where
  定义体: TopCat.of PEmpty
  presheaf := (CategoryTheory.Functor.const _).obj (CommRingCat.of PUnit)
  IsSheaf := Presheaf.isSheaf_of_isTerminal _ CommRingCat.punitIsTerminal
  isLocalRing x := PEmpty.elim x

Depends on / 依赖: PEmpty, TopCat, TopCat.of
-/
def empty : LocallyRingedSpace.{u} where
  carrier := TopCat.of PEmpty
  presheaf := (CategoryTheory.Functor.const _).obj (CommRingCat.of PUnit)
  IsSheaf := Presheaf.isSheaf_of_isTerminal _ CommRingCat.punitIsTerminal
  isLocalRing x := PEmpty.elim x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EmptyCollection LocallyRingedSpace.{u}
  body: ⟨LocallyRingedSpace.empty⟩

中文:
实例 :
  签名: EmptyCollection LocallyRingedSpace.{u}
  定义体: ⟨LocallyRingedSpace.empty⟩

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.empty
-/
instance : EmptyCollection LocallyRingedSpace.{u} := ⟨LocallyRingedSpace.empty⟩

/--
Definition of `emptyTo` / `emptyTo` 的定义

English:
definition emptyTo
  signature: (X : LocallyRingedSpace.{u})
  body: ⟨⟨ofHom ⟨fun x => PEmpty.elim x, by fun_prop⟩,
    { app := fun U => CommRingCat.ofHom <| by refine ⟨⟨⟨0, ?_⟩, ?_⟩, ?_, ?_⟩ <;> intros <;> rfl }⟩,
    fun x => PEmpty.elim x⟩

noncomputable

中文:
定义 emptyTo
  签名: (X : LocallyRingedSpace.{u})
  定义体: ⟨⟨ofHom ⟨fun x => PEmpty.elim x, by fun_prop⟩,
    { app := fun U => CommRingCat.ofHom <| by refine ⟨⟨⟨0, ?_⟩, ?_⟩, ?_, ?_⟩ <;> intros <;> rfl }⟩,
    fun x => PEmpty.elim x⟩

noncomputable

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, PEmpty, PEmpty.elim, fun_prop, intros
-/
def emptyTo (X : LocallyRingedSpace.{u}) : ∅ ⟶ X :=
  ⟨⟨ofHom ⟨fun x => PEmpty.elim x, by fun_prop⟩,
    { app := fun U => CommRingCat.ofHom <| by refine ⟨⟨⟨0, ?_⟩, ?_⟩, ?_, ?_⟩ <;> intros <;> rfl }⟩,
    fun x => PEmpty.elim x⟩

noncomputable
instance {X : LocallyRingedSpace.{u}} : Unique (∅ ⟶ X) where
  default := LocallyRingedSpace.emptyTo X
  uniq f := by ext ⟨⟩ x; cat_disch

/-- The empty space is initial in `LocallyRingedSpace`. -/
noncomputable
/--
Definition of `emptyIsInitial` / `emptyIsInitial` 的定义

English:
definition emptyIsInitial
  signature: : Limits.IsInitial (∅ : LocallyRingedSpace.{u})
  body: Limits.IsInitial.ofUnique _

中文:
定义 emptyIsInitial
  签名: : Limits.IsInitial (∅ : LocallyRingedSpace.{u})
  定义体: Limits.IsInitial.ofUnique _

Depends on / 依赖: IsInitial, Limits, Limits.IsInitial.ofUnique, ofUnique
-/
def emptyIsInitial : Limits.IsInitial (∅ : LocallyRingedSpace.{u}) := Limits.IsInitial.ofUnique _

-- This actually holds for all ringed spaces with nontrivial stalks.
/--
theorem `basicOpen_zero` / 定理 `basicOpen_zero`

English:
theorem basicOpen_zero
  given: (X : LocallyRingedSpace.{u}) (U : Opens X.carrier)
  proof: by
  ext x
  simp only [RingedSpace.basicOpen, Opens.coe_mk, Set.mem_ofPred_eq,
    Opens.coe_bot, Set.mem_empty_iff_false,
    iff_false, not_exists]
  intro hx
  rw [map_zero]; rw [isUnit_zero_iff]
  change (0 : X.presheaf.stalk x) != (1 : X.presheaf.stalk x)
  exact zero_ne_one

@[simp]

中文:
定理 basicOpen_zero
  条件: (X : LocallyRingedSpace.{u}) (U : Opens X.carrier)
  证明: by
  ext x
  simp only [RingedSpace.basicOpen, Opens.coe_mk, Set.mem_ofPred_eq,
    Opens.coe_bot, Set.mem_empty_iff_false,
    iff_false, not_exists]
  intro hx
  rw [map_zero]; rw [isUnit_zero_iff]
  change (0 : X.presheaf.stalk x) != (1 : X.presheaf.stalk x)
  exact zero_ne_one

@[simp]

Depends on / 依赖: Opens.coe_bot, Opens.coe_mk, RingedSpace, RingedSpace.basicOpen, Set.mem_empty_iff_false, Set.mem_ofPred_eq, X.presheaf.stalk, basicOpen, coe_bot, coe_mk, iff_false, isUnit_zero_iff, map_zero, mem_empty_iff_false, mem_ofPred_eq, not_exists, presheaf, zero_ne_one
-/
theorem basicOpen_zero (X : LocallyRingedSpace.{u}) (U : Opens X.carrier) :
    X.toRingedSpace.basicOpen (0 : X.presheaf.obj <| op U) = ⊥ := by
  ext x
  simp only [RingedSpace.basicOpen, Opens.coe_mk, Set.mem_ofPred_eq,
    Opens.coe_bot, Set.mem_empty_iff_false,
    iff_false, not_exists]
  intro hx
  rw [map_zero]; rw [isUnit_zero_iff]
  change (0 : X.presheaf.stalk x) != (1 : X.presheaf.stalk x)
  exact zero_ne_one

@[simp]
/--
lemma `basicOpen_eq_bot_of_isNilpotent` / 引理 `basicOpen_eq_bot_of_isNilpotent`

English:
lemma basicOpen_eq_bot_of_isNilpotent
  statement: (X : LocallyRingedSpace.{u}) (U : Opens X.carrier)
  proof: by
  obtain ⟨n, hn⟩ := hf
  cases n.eq_zero_or_pos with
  | inr h =>
    rw [← X.toRingedSpace.basicOpen_pow f n h]; rw [hn]
    simp [basicOpen_zero]
  | inl h =>
    rw [h]; rw [pow_zero] at hn
    simp [eq_zero_of_zero_eq_one hn.symm f, basicOpen_zero]

中文:
引理 basicOpen_eq_bot_of_isNilpotent
  结论: (X : LocallyRingedSpace.{u}) (U : Opens X.carrier)
  证明: by
  obtain ⟨n, hn⟩ := hf
  cases n.eq_zero_or_pos with
  | inr h =>
    rw [← X.toRingedSpace.basicOpen_pow f n h]; rw [hn]
    simp [basicOpen_zero]
  | inl h =>
    rw [h]; rw [pow_zero] at hn
    simp [eq_zero_of_zero_eq_one hn.symm f, basicOpen_zero]

Depends on / 依赖: X.toRingedSpace.basicOpen_pow, basicOpen_pow, basicOpen_zero, eq_zero_of_zero_eq_one, eq_zero_or_pos, hn.symm, n.eq_zero_or_pos, pow_zero, toRingedSpace
-/
lemma basicOpen_eq_bot_of_isNilpotent (X : LocallyRingedSpace.{u}) (U : Opens X.carrier)
    (f : (X.presheaf.obj <| op U)) (hf : IsNilpotent f) :
    X.toRingedSpace.basicOpen f = ⊥ := by
  obtain ⟨n, hn⟩ := hf
  cases n.eq_zero_or_pos with
  | inr h =>
    rw [← X.toRingedSpace.basicOpen_pow f n h]; rw [hn]
    simp [basicOpen_zero]
  | inl h =>
    rw [h]; rw [pow_zero] at hn
    simp [eq_zero_of_zero_eq_one hn.symm f, basicOpen_zero]

/--
Instance `component_nontrivial` / 实例 `component_nontrivial`

English:
instance component_nontrivial
  signature: (X : LocallyRingedSpace.{u}) (U : Opens X.carrier) [hU : Nonempty U]
  body: (X.presheaf.germ _ _ hU.some.2).hom.domain_nontrivial

@[simp]

中文:
实例 component_nontrivial
  签名: (X : LocallyRingedSpace.{u}) (U : Opens X.carrier) [hU : Nonempty U]
  定义体: (X.presheaf.germ _ _ hU.some.2).hom.domain_nontrivial

@[simp]

Depends on / 依赖: X.presheaf.germ, domain_nontrivial, hU.some, hom.domain_nontrivial, presheaf
-/
instance component_nontrivial (X : LocallyRingedSpace.{u}) (U : Opens X.carrier) [hU : Nonempty U] :
    Nontrivial (X.presheaf.obj <| op U) :=
  (X.presheaf.germ _ _ hU.some.2).hom.domain_nontrivial

@[simp]
/--
lemma `iso_hom_base_inv_base` / 引理 `iso_hom_base_inv_base`

English:
lemma iso_hom_base_inv_base
  given: {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y)
  proof: by
  simp only [← comp_base, Iso.hom_inv_id, id_toHom, PresheafedSpace.id_base]

@[simp]

中文:
引理 iso_hom_base_inv_base
  条件: {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y)
  证明: by
  simp only [← comp_base, Iso.hom_inv_id, id_toHom, PresheafedSpace.id_base]

@[simp]

Depends on / 依赖: Iso.hom_inv_id, PresheafedSpace, PresheafedSpace.id_base, comp_base, hom_inv_id, id_base, id_toHom
-/
lemma iso_hom_base_inv_base {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) :
    e.hom.base ≫ e.inv.base = 𝟙 _ := by
  simp only [← comp_base, Iso.hom_inv_id, id_toHom, PresheafedSpace.id_base]

@[simp]
/--
lemma `iso_hom_base_inv_base_apply` / 引理 `iso_hom_base_inv_base_apply`

English:
lemma iso_hom_base_inv_base_apply
  given: {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (x : X)
  proof: by
  change (e.hom.base ≫ e.inv.base) x = 𝟙 X.toPresheafedSpace x
  simp

@[simp]

中文:
引理 iso_hom_base_inv_base_apply
  条件: {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (x : X)
  证明: by
  change (e.hom.base ≫ e.inv.base) x = 𝟙 X.toPresheafedSpace x
  simp

@[simp]

Depends on / 依赖: X.toPresheafedSpace, e.hom.base, e.inv.base, toPresheafedSpace
-/
lemma iso_hom_base_inv_base_apply {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (x : X) :
    (e.inv.base (e.hom.base x)) = x := by
  change (e.hom.base ≫ e.inv.base) x = 𝟙 X.toPresheafedSpace x
  simp

@[simp]
/--
lemma `iso_inv_base_hom_base` / 引理 `iso_inv_base_hom_base`

English:
lemma iso_inv_base_hom_base
  given: {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y)
  proof: by
  simp only [← comp_base, Iso.inv_hom_id, id_toHom, PresheafedSpace.id_base]

@[simp]

中文:
引理 iso_inv_base_hom_base
  条件: {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y)
  证明: by
  simp only [← comp_base, Iso.inv_hom_id, id_toHom, PresheafedSpace.id_base]

@[simp]

Depends on / 依赖: Iso.inv_hom_id, PresheafedSpace, PresheafedSpace.id_base, comp_base, id_base, id_toHom, inv_hom_id
-/
lemma iso_inv_base_hom_base {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) :
    e.inv.base ≫ e.hom.base = 𝟙 _ := by
  simp only [← comp_base, Iso.inv_hom_id, id_toHom, PresheafedSpace.id_base]

@[simp]
/--
lemma `iso_inv_base_hom_base_apply` / 引理 `iso_inv_base_hom_base_apply`

English:
lemma iso_inv_base_hom_base_apply
  given: {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (y : Y)
  proof: by
  change (e.inv.base ≫ e.hom.base) y = 𝟙 Y.toPresheafedSpace y
  simp

中文:
引理 iso_inv_base_hom_base_apply
  条件: {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (y : Y)
  证明: by
  change (e.inv.base ≫ e.hom.base) y = 𝟙 Y.toPresheafedSpace y
  simp

Depends on / 依赖: Y.toPresheafedSpace, e.hom.base, e.inv.base, toPresheafedSpace
-/
lemma iso_inv_base_hom_base_apply {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (y : Y) :
    (e.hom.base (e.inv.base y)) = y := by
  change (e.inv.base ≫ e.hom.base) y = 𝟙 Y.toPresheafedSpace y
  simp

section Stalks

variable {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

@[simp]
/--
lemma `stalkMap_id` / 引理 `stalkMap_id`

English:
lemma stalkMap_id
  given: (X : LocallyRingedSpace.{u}) (x : X)
  proof: PresheafedSpace.stalkMap.id _ x

中文:
引理 stalkMap_id
  条件: (X : LocallyRingedSpace.{u}) (x : X)
  证明: PresheafedSpace.stalkMap.id _ x

Depends on / 依赖: PresheafedSpace, PresheafedSpace.stalkMap.id, stalkMap
-/
lemma stalkMap_id (X : LocallyRingedSpace.{u}) (x : X) :
    (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.presheaf.stalk x) :=
  PresheafedSpace.stalkMap.id _ x

/--
lemma `stalkMap_comp` / 引理 `stalkMap_comp`

English:
lemma stalkMap_comp
  given: (x : X)
  proof: PresheafedSpace.stalkMap.comp f.toHom g.toHom x

@[reassoc]

中文:
引理 stalkMap_comp
  条件: (x : X)
  证明: PresheafedSpace.stalkMap.comp f.toHom g.toHom x

@[reassoc]

Depends on / 依赖: PresheafedSpace, PresheafedSpace.stalkMap.comp, f.toHom, g.toHom, stalkMap
-/
lemma stalkMap_comp (x : X) :
    (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap (f.base x) ≫ f.stalkMap x :=
  PresheafedSpace.stalkMap.comp f.toHom g.toHom x

@[reassoc]
/--
lemma `stalkSpecializes_stalkMap` / 引理 `stalkSpecializes_stalkMap`

English:
lemma stalkSpecializes_stalkMap
  given: (x x' : X) (h : x ⤳ x')
  proof: PresheafedSpace.stalkMap.stalkSpecializes_stalkMap f.toHom h

中文:
引理 stalkSpecializes_stalkMap
  条件: (x x' : X) (h : x ⤳ x')
  证明: PresheafedSpace.stalkMap.stalkSpecializes_stalkMap f.toHom h

Depends on / 依赖: PresheafedSpace, PresheafedSpace.stalkMap.stalkSpecializes_stalkMap, f.toHom, stalkMap, stalkSpecializes_stalkMap
-/
lemma stalkSpecializes_stalkMap (x x' : X) (h : x ⤳ x') :
    Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h) ≫ f.stalkMap x =
      f.stalkMap x' ≫ X.presheaf.stalkSpecializes h :=
  PresheafedSpace.stalkMap.stalkSpecializes_stalkMap f.toHom h

/--
lemma `stalkSpecializes_stalkMap_apply` / 引理 `stalkSpecializes_stalkMap_apply`

English:
lemma stalkSpecializes_stalkMap_apply
  given: (x x' : X) (h : x ⤳ x') (y)
  proof: DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkSpecializes_stalkMap f x x' h)) y

中文:
引理 stalkSpecializes_stalkMap_apply
  条件: (x x' : X) (h : x ⤳ x') (y)
  证明: DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkSpecializes_stalkMap f x x' h)) y

Depends on / 依赖: CommRingCat, CommRingCat.hom_ext_iff.mp, DFunLike, DFunLike.congr_fun, congr_fun, hom_ext_iff, stalkSpecializes_stalkMap
-/
lemma stalkSpecializes_stalkMap_apply (x x' : X) (h : x ⤳ x') (y) :
    f.stalkMap x (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes h) y) =
      (X.presheaf.stalkSpecializes h (f.stalkMap x' y)) :=
  DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkSpecializes_stalkMap f x x' h)) y

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `stalkMap_congr` / 引理 `stalkMap_congr`

English:
lemma stalkMap_congr
  given: (f g : X ⟶ Y) (hfg : f = g) (x x' : X) (hxx' : x = x')
  proof: by
  subst hfg
  subst hxx'
  simp

@[reassoc]

中文:
引理 stalkMap_congr
  条件: (f g : X ⟶ Y) (hfg : f = g) (x x' : X) (hxx' : x = x')
  证明: by
  subst hfg
  subst hxx'
  simp

@[reassoc]
-/
lemma stalkMap_congr (f g : X ⟶ Y) (hfg : f = g) (x x' : X) (hxx' : x = x') :
    f.stalkMap x ≫ X.presheaf.stalkSpecializes (specializes_of_eq hxx'.symm) =
      Y.presheaf.stalkSpecializes (specializes_of_eq <| hfg ▸ hxx' ▸ rfl) ≫ g.stalkMap x' := by
  subst hfg
  subst hxx'
  simp

@[reassoc]
/--
lemma `stalkMap_congr_hom` / 引理 `stalkMap_congr_hom`

English:
lemma stalkMap_congr_hom
  given: (f g : X ⟶ Y) (hfg : f = g) (x : X)
  proof: by
  subst hfg
  simp

中文:
引理 stalkMap_congr_hom
  条件: (f g : X ⟶ Y) (hfg : f = g) (x : X)
  证明: by
  subst hfg
  simp
-/
lemma stalkMap_congr_hom (f g : X ⟶ Y) (hfg : f = g) (x : X) :
    f.stalkMap x = Y.presheaf.stalkSpecializes (specializes_of_eq <| hfg ▸ rfl) ≫
      g.stalkMap x := by
  subst hfg
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `stalkMap_congr_point` / 引理 `stalkMap_congr_point`

English:
lemma stalkMap_congr_point
  given: {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x x' : X) (hxx' : x = x')
  proof: by
  subst hxx'
  simp

中文:
引理 stalkMap_congr_point
  条件: {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x x' : X) (hxx' : x = x')
  证明: by
  subst hxx'
  simp
-/
lemma stalkMap_congr_point {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x x' : X) (hxx' : x = x') :
    f.stalkMap x ≫ X.presheaf.stalkSpecializes (specializes_of_eq hxx'.symm) =
      Y.presheaf.stalkSpecializes (specializes_of_eq <| hxx' ▸ rfl) ≫ f.stalkMap x' := by
  subst hxx'
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `stalkMap_hom_inv` / 引理 `stalkMap_hom_inv`

English:
lemma stalkMap_hom_inv
  given: (e : X ≅ Y) (y : Y)
  proof: by
  rw [← stalkMap_comp]; rw [LocallyRingedSpace.stalkMap_congr_hom (e.inv ≫ e.hom) (𝟙 _) (by simp)]
  simp

中文:
引理 stalkMap_hom_inv
  条件: (e : X ≅ Y) (y : Y)
  证明: by
  rw [← stalkMap_comp]; rw [LocallyRingedSpace.stalkMap_congr_hom (e.inv ≫ e.hom) (𝟙 _) (by simp)]
  simp

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.stalkMap_congr_hom, e.hom, e.inv, stalkMap_comp, stalkMap_congr_hom
-/
lemma stalkMap_hom_inv (e : X ≅ Y) (y : Y) :
    e.hom.stalkMap (e.inv.base y) ≫ e.inv.stalkMap y =
      Y.presheaf.stalkSpecializes (specializes_of_eq <| by simp) := by
  rw [← stalkMap_comp]; rw [LocallyRingedSpace.stalkMap_congr_hom (e.inv ≫ e.hom) (𝟙 _) (by simp)]
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `stalkMap_hom_inv_apply` / 引理 `stalkMap_hom_inv_apply`

English:
lemma stalkMap_hom_inv_apply
  given: (e : X ≅ Y) (y : Y) (z)
  proof: DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_hom_inv e y)) z

中文:
引理 stalkMap_hom_inv_apply
  条件: (e : X ≅ Y) (y : Y) (z)
  证明: DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_hom_inv e y)) z

Depends on / 依赖: CommRingCat, CommRingCat.hom_ext_iff.mp, DFunLike, DFunLike.congr_fun, congr_fun, hom_ext_iff, stalkMap_hom_inv
-/
lemma stalkMap_hom_inv_apply (e : X ≅ Y) (y : Y) (z) :
    e.inv.stalkMap y (e.hom.stalkMap (e.inv.base y) z) =
      Y.presheaf.stalkSpecializes (specializes_of_eq <| by simp) z :=
  DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_hom_inv e y)) z

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `stalkMap_inv_hom` / 引理 `stalkMap_inv_hom`

English:
lemma stalkMap_inv_hom
  given: (e : X ≅ Y) (x : X)
  proof: by
  rw [← stalkMap_comp]; rw [LocallyRingedSpace.stalkMap_congr_hom (e.hom ≫ e.inv) (𝟙 _) (by simp)]
  simp

中文:
引理 stalkMap_inv_hom
  条件: (e : X ≅ Y) (x : X)
  证明: by
  rw [← stalkMap_comp]; rw [LocallyRingedSpace.stalkMap_congr_hom (e.hom ≫ e.inv) (𝟙 _) (by simp)]
  simp

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.stalkMap_congr_hom, e.hom, e.inv, stalkMap_comp, stalkMap_congr_hom
-/
lemma stalkMap_inv_hom (e : X ≅ Y) (x : X) :
    e.inv.stalkMap (e.hom.base x) ≫ e.hom.stalkMap x =
      X.presheaf.stalkSpecializes (specializes_of_eq <| by simp) := by
  rw [← stalkMap_comp]; rw [LocallyRingedSpace.stalkMap_congr_hom (e.hom ≫ e.inv) (𝟙 _) (by simp)]
  simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `stalkMap_inv_hom_apply` / 引理 `stalkMap_inv_hom_apply`

English:
lemma stalkMap_inv_hom_apply
  given: (e : X ≅ Y) (x : X) (y)
  proof: DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_inv_hom e x)) y

@[reassoc (attr := simp)]

中文:
引理 stalkMap_inv_hom_apply
  条件: (e : X ≅ Y) (x : X) (y)
  证明: DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_inv_hom e x)) y

@[reassoc (attr := simp)]

Depends on / 依赖: CommRingCat, CommRingCat.hom_ext_iff.mp, DFunLike, DFunLike.congr_fun, congr_fun, hom_ext_iff, stalkMap_inv_hom
-/
lemma stalkMap_inv_hom_apply (e : X ≅ Y) (x : X) (y) :
    e.hom.stalkMap x (e.inv.stalkMap (e.hom.base x) y) =
      X.presheaf.stalkSpecializes (specializes_of_eq <| by simp) y :=
  DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (stalkMap_inv_hom e x)) y

@[reassoc (attr := simp)]
/--
lemma `stalkMap_germ` / 引理 `stalkMap_germ`

English:
lemma stalkMap_germ
  given: (U : Opens Y) (x : X) (hx : f.base x in U)
  proof: PresheafedSpace.stalkMap_germ f.toHom U x hx

中文:
引理 stalkMap_germ
  条件: (U : Opens Y) (x : X) (hx : f.base x in U)
  证明: PresheafedSpace.stalkMap_germ f.toHom U x hx

Depends on / 依赖: PresheafedSpace, PresheafedSpace.stalkMap_germ, f.toHom, stalkMap_germ
-/
lemma stalkMap_germ (U : Opens Y) (x : X) (hx : f.base x in U) :
    Y.presheaf.germ U (f.base x) hx ≫ f.stalkMap x =
      f.c.app (op U) ≫ X.presheaf.germ ((Opens.map f.base).obj U) x hx :=
  PresheafedSpace.stalkMap_germ f.toHom U x hx

/--
lemma `stalkMap_germ_apply` / 引理 `stalkMap_germ_apply`

English:
lemma stalkMap_germ_apply
  given: (U : Opens Y) (x : X) (hx : f.base x in U) (y)
  proof: PresheafedSpace.stalkMap_germ_apply f.toHom U x hx y

中文:
引理 stalkMap_germ_apply
  条件: (U : Opens Y) (x : X) (hx : f.base x in U) (y)
  证明: PresheafedSpace.stalkMap_germ_apply f.toHom U x hx y

Depends on / 依赖: PresheafedSpace, PresheafedSpace.stalkMap_germ_apply, f.toHom, stalkMap_germ_apply
-/
lemma stalkMap_germ_apply (U : Opens Y) (x : X) (hx : f.base x in U) (y) :
    f.stalkMap x (Y.presheaf.germ U (f.base x) hx y) =
      X.presheaf.germ ((Opens.map f.base).obj U) x hx (f.c.app (op U) y) :=
  PresheafedSpace.stalkMap_germ_apply f.toHom U x hx y

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `preimage_basicOpen` / 定理 `preimage_basicOpen`

English:
theorem preimage_basicOpen
  statement: {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) {U : Opens Y}
  proof: by
  ext x
  constructor
  · rintro ⟨hxU, hx⟩
    rw [SetLike.mem_coe]; rw [X.toRingedSpace.mem_basicOpen _ _ hxU]
    delta toRingedSpace
    rw [← stalkMap_germ_apply]
    exact (f.stalkMap _).hom.isUnit_map hx
  · rintro ⟨hxU, hx⟩
    simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, t

中文:
定理 preimage_basicOpen
  结论: {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) {U : Opens Y}
  证明: by
  ext x
  constructor
  · rintro ⟨hxU, hx⟩
    rw [SetLike.mem_coe]; rw [X.toRingedSpace.mem_basicOpen _ _ hxU]
    delta toRingedSpace
    rw [← stalkMap_germ_apply]
    exact (f.stalkMap _).hom.isUnit_map hx
  · rintro ⟨hxU, hx⟩
    simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, t

Depends on / 依赖: Opens.map_coe, RingedSpace, RingedSpace.mem_basicOpen, Set.mem_preimage, SetLike, SetLike.mem_coe, X.toRingedSpace.mem_basicOpen, f.base, f.stalkMap, hom.isUnit_map, isUnit_map, isUnit_map_iff, map_coe, mem_basicOpen, mem_coe, mem_preimage, stalkMap, stalkMap_germ_apply, toRingedSpace
-/
theorem preimage_basicOpen {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) {U : Opens Y}
    (s : Y.presheaf.obj (op U)) :
    (Opens.map f.base).obj (Y.toRingedSpace.basicOpen s) =
      @RingedSpace.basicOpen X.toRingedSpace ((Opens.map f.base).obj U) (f.c.app _ s) := by
  ext x
  constructor
  · rintro ⟨hxU, hx⟩
    rw [SetLike.mem_coe]; rw [X.toRingedSpace.mem_basicOpen _ _ hxU]
    delta toRingedSpace
    rw [← stalkMap_germ_apply]
    exact (f.stalkMap _).hom.isUnit_map hx
  · rintro ⟨hxU, hx⟩
    simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, toRingedSpace] at hx ⊢
    rw [RingedSpace.mem_basicOpen _ s (f.base x) hxU]
    rw [← stalkMap_germ_apply] at hx
    exact (isUnit_map_iff (f.stalkMap x).hom _).mp hx

variable {U : TopCat.{u}} (X : LocallyRingedSpace.{u}) {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f)
  (V : Opens U) (x : U) (hx : x in V)

/-- For an open embedding `f : U ⟶ X` and a point `x : U`, we get an isomorphism between the stalk
of `X` at `f x` and the stalk of the restriction of `X` along `f` at `x`. -/
noncomputable
/--
Definition of `restrictStalkIso` / `restrictStalkIso` 的定义

English:
definition restrictStalkIso
  signature: : (X.restrict h).presheaf.stalk x ≅ X.presheaf.stalk (f x)
  body: X.toPresheafedSpace.restrictStalkIso h x

@[reassoc (attr := simp)]

中文:
定义 restrictStalkIso
  签名: : (X.restrict h).presheaf.stalk x ≅ X.presheaf.stalk (f x)
  定义体: X.toPresheafedSpace.restrictStalkIso h x

@[reassoc (attr := simp)]

Depends on / 依赖: X.toPresheafedSpace.restrictStalkIso, restrictStalkIso, toPresheafedSpace
-/
def restrictStalkIso : (X.restrict h).presheaf.stalk x ≅ X.presheaf.stalk (f x) :=
  X.toPresheafedSpace.restrictStalkIso h x

@[reassoc (attr := simp)]
/--
lemma `restrictStalkIso_hom_eq_germ` / 引理 `restrictStalkIso_hom_eq_germ`

English:
lemma restrictStalkIso_hom_eq_germ
  proof: PresheafedSpace.restrictStalkIso_hom_eq_germ X.toPresheafedSpace h V x hx

中文:
引理 restrictStalkIso_hom_eq_germ
  证明: PresheafedSpace.restrictStalkIso_hom_eq_germ X.toPresheafedSpace h V x hx

Depends on / 依赖: PresheafedSpace, PresheafedSpace.restrictStalkIso_hom_eq_germ, X.toPresheafedSpace, restrictStalkIso_hom_eq_germ, toPresheafedSpace
-/
lemma restrictStalkIso_hom_eq_germ :
    (X.restrict h).presheaf.germ _ x hx ≫ (X.restrictStalkIso h x).hom =
      X.presheaf.germ (h.functor.obj V) (f x) ⟨x, hx, rfl⟩ :=
  PresheafedSpace.restrictStalkIso_hom_eq_germ X.toPresheafedSpace h V x hx

/--
lemma `restrictStalkIso_hom_eq_germ_apply` / 引理 `restrictStalkIso_hom_eq_germ_apply`

English:
lemma restrictStalkIso_hom_eq_germ_apply
  given: (y)
  proof: PresheafedSpace.restrictStalkIso_hom_eq_germ_apply X.toPresheafedSpace h V x hx y

@[reassoc (attr := simp)]

中文:
引理 restrictStalkIso_hom_eq_germ_apply
  条件: (y)
  证明: PresheafedSpace.restrictStalkIso_hom_eq_germ_apply X.toPresheafedSpace h V x hx y

@[reassoc (attr := simp)]

Depends on / 依赖: PresheafedSpace, PresheafedSpace.restrictStalkIso_hom_eq_germ_apply, X.toPresheafedSpace, restrictStalkIso_hom_eq_germ_apply, toPresheafedSpace
-/
lemma restrictStalkIso_hom_eq_germ_apply (y) :
    (X.restrictStalkIso h x).hom ((X.restrict h).presheaf.germ _ x hx y) =
      X.presheaf.germ (h.functor.obj V) (f x) ⟨x, hx, rfl⟩ y :=
  PresheafedSpace.restrictStalkIso_hom_eq_germ_apply X.toPresheafedSpace h V x hx y

@[reassoc (attr := simp)]
/--
lemma `restrictStalkIso_inv_eq_germ` / 引理 `restrictStalkIso_inv_eq_germ`

English:
lemma restrictStalkIso_inv_eq_germ
  proof: PresheafedSpace.restrictStalkIso_inv_eq_germ X.toPresheafedSpace h V x hx

中文:
引理 restrictStalkIso_inv_eq_germ
  证明: PresheafedSpace.restrictStalkIso_inv_eq_germ X.toPresheafedSpace h V x hx

Depends on / 依赖: PresheafedSpace, PresheafedSpace.restrictStalkIso_inv_eq_germ, X.toPresheafedSpace, restrictStalkIso_inv_eq_germ, toPresheafedSpace
-/
lemma restrictStalkIso_inv_eq_germ :
    X.presheaf.germ (h.functor.obj V) (f x) ⟨x, hx, rfl⟩ ≫
      (X.restrictStalkIso h x).inv = (X.restrict h).presheaf.germ _ x hx :=
  PresheafedSpace.restrictStalkIso_inv_eq_germ X.toPresheafedSpace h V x hx

/--
lemma `restrictStalkIso_inv_eq_germ_apply` / 引理 `restrictStalkIso_inv_eq_germ_apply`

English:
lemma restrictStalkIso_inv_eq_germ_apply
  given: (y)
  proof: PresheafedSpace.restrictStalkIso_inv_eq_germ_apply X.toPresheafedSpace h V x hx y

中文:
引理 restrictStalkIso_inv_eq_germ_apply
  条件: (y)
  证明: PresheafedSpace.restrictStalkIso_inv_eq_germ_apply X.toPresheafedSpace h V x hx y

Depends on / 依赖: PresheafedSpace, PresheafedSpace.restrictStalkIso_inv_eq_germ_apply, X.toPresheafedSpace, restrictStalkIso_inv_eq_germ_apply, toPresheafedSpace
-/
lemma restrictStalkIso_inv_eq_germ_apply (y) :
    (X.restrictStalkIso h x).inv
      (X.presheaf.germ (h.functor.obj V) (f x) ⟨x, hx, rfl⟩ y) =
        (X.restrict h).presheaf.germ _ x hx y :=
  PresheafedSpace.restrictStalkIso_inv_eq_germ_apply X.toPresheafedSpace h V x hx y

/--
lemma `restrictStalkIso_inv_eq_ofRestrict` / 引理 `restrictStalkIso_inv_eq_ofRestrict`

English:
lemma restrictStalkIso_inv_eq_ofRestrict
  proof: PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict X.toPresheafedSpace h x

中文:
引理 restrictStalkIso_inv_eq_ofRestrict
  证明: PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict X.toPresheafedSpace h x

Depends on / 依赖: PresheafedSpace, PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict, X.toPresheafedSpace, restrictStalkIso_inv_eq_ofRestrict, toPresheafedSpace
-/
lemma restrictStalkIso_inv_eq_ofRestrict :
    (X.restrictStalkIso h x).inv = (X.ofRestrict h).stalkMap x :=
  PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict X.toPresheafedSpace h x

/--
Instance `ofRestrict_stalkMap_isIso` / 实例 `ofRestrict_stalkMap_isIso`

English:
instance ofRestrict_stalkMap_isIso
  signature: : IsIso ((X.ofRestrict h).stalkMap x)
  body: PresheafedSpace.ofRestrict_stalkMap_isIso X.toPresheafedSpace h x

中文:
实例 ofRestrict_stalkMap_isIso
  签名: : IsIso ((X.ofRestrict h).stalkMap x)
  定义体: PresheafedSpace.ofRestrict_stalkMap_isIso X.toPresheafedSpace h x

Depends on / 依赖: PresheafedSpace, PresheafedSpace.ofRestrict_stalkMap_isIso, X.toPresheafedSpace, ofRestrict_stalkMap_isIso, toPresheafedSpace
-/
instance ofRestrict_stalkMap_isIso : IsIso ((X.ofRestrict h).stalkMap x) :=
  PresheafedSpace.ofRestrict_stalkMap_isIso X.toPresheafedSpace h x

end Stalks

end LocallyRingedSpace

end AlgebraicGeometry
