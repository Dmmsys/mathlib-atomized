/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison, Mario Carneiro
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Category instance for topological spaces

We introduce the bundled category `TopCat` of topological spaces together with the functors
`TopCat.discrete` and `TopCat.trivial` from the category of types to `TopCat` which equip a type
with the corresponding discrete, resp. trivial, topology. For a proof that these functors are left,
resp. right adjoint to the forgetful functor, see
`Mathlib/Topology/Category/TopCat/Adjunctions.lean`.
-/

@[expose] public section

assert_not_exists Module

open CategoryTheory TopologicalSpace Topology

universe u

/--
Definition of `TopCat` / `TopCat` 的定义

English:
structure TopCat
  parameters: where
  axioms and operations (3):
    - of : :
    - carrier : Type u
    - [str : TopologicalSpace carrier]

中文:
结构 TopCat
  参数: where
  公理与运算 (3 个):
    - of : :
    - carrier : 类型u
    - [str : TopologicalSpace carrier]
-/
structure TopCat where
  /-- The object in `TopCat` associated to a type equipped with the appropriate
  typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [str : TopologicalSpace carrier]

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `TopCat.of X` being printed as `{ carrier := X, str := ... }` by
`delabStructureInstance`. -/
@[app_delab TopCat.of]
meta def TopCat.delabOf : Delab := delabApp

end Notation

attribute [instance] TopCat.str

initialize_simps_projections TopCat (-str)

namespace TopCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (TopCat) (Type u)
  body: ⟨TopCat.carrier⟩

中文:
实例 :
  签名: CoeSort (TopCat) (类型u)
  定义体: ⟨TopCat.carrier⟩

Depends on / 依赖: TopCat, TopCat.carrier, carrier
-/
instance : CoeSort (TopCat) (Type u) :=
  ⟨TopCat.carrier⟩

attribute [coe] TopCat.carrier

/--
lemma `coe_of` / 引理 `coe_of`

English:
lemma coe_of
  given: (X : Type u) [TopologicalSpace X]
  statement: (of X : Type u) = X
  proof: rfl

中文:
引理 coe_of
  条件: (X : 类型u) [TopologicalSpace X]
  结论: (of X : 类型u) = X
  证明: rfl
-/
lemma coe_of (X : Type u) [TopologicalSpace X] : (of X : Type u) = X :=
  rfl

/--
lemma `of_carrier` / 引理 `of_carrier`

English:
lemma of_carrier
  given: (X : TopCat.{u})
  statement: of X = X
  proof: rfl

中文:
引理 of_carrier
  条件: (X : TopCat.{u})
  结论: of X = X
  证明: rfl
-/
lemma of_carrier (X : TopCat.{u}) : of X = X := rfl

variable {X} in
/-- The type of morphisms in `TopCat`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : TopCat.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : C(X, Y)

中文:
结构 Hom
  参数: (X Y : TopCat.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : C(X, Y)
-/
structure Hom (X Y : TopCat.{u}) where
  private mk ::
  /-- The underlying `ContinuousMap`. -/
  hom' : C(X, Y)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category TopCat
  body: Hom X Y
  id X := ⟨ContinuousMap.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: Category TopCat
  定义体: Hom X Y
  id X := ⟨ContinuousMap.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category TopCat where
  Hom X Y := Hom X Y
  id X := ⟨ContinuousMap.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory.{u} TopCat (fun X Y => C(X, Y))
  body: Hom.hom'
  ofHom f := ⟨f⟩

中文:
实例 :
  签名: ConcreteCategory.{u} TopCat (fun X Y => C(X, Y))
  定义体: Hom.hom'
  ofHom f := ⟨f⟩

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory.{u} TopCat (fun X Y => C(X, Y)) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : TopCat.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := TopCat) f

中文:
缩写 Hom.hom
  签名: {X Y : TopCat.{u}} (f : Hom X Y)
  定义体: ConcreteCategory.hom (C := TopCat) f
-/
abbrev Hom.hom {X Y : TopCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := TopCat) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
  body: ConcreteCategory.ofHom (C := TopCat) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
  定义体: ConcreteCategory.ofHom (C := TopCat) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, TopCat
-/
abbrev ofHom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := TopCat) f

/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : TopCat) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 Hom.Simps.hom
  签名: (X Y : TopCat) (f : Hom X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (X Y : TopCat) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {X : TopCat.{u}}
  statement: (𝟙 X : X ⟶ X).hom = ContinuousMap.id X
  proof: rfl

@[simp]

中文:
引理 hom_id
  条件: {X : TopCat.{u}}
  结论: (𝟙 X : X ⟶ X).hom = ContinuousMap.id X
  证明: rfl

@[simp]
-/
lemma hom_id {X : TopCat.{u}} : (𝟙 X : X ⟶ X).hom = ContinuousMap.id X := rfl

@[simp]
/--
theorem `id_app` / 定理 `id_app`

English:
theorem id_app
  given: (X : TopCat.{u}) (x : ↑X)
  statement: (𝟙 X : X ⟶ X) x = x
  proof: rfl

中文:
定理 id_app
  条件: (X : TopCat.{u}) (x : ↑X)
  结论: (𝟙 X : X ⟶ X) x = x
  证明: rfl
-/
theorem id_app (X : TopCat.{u}) (x : ↑X) : (𝟙 X : X ⟶ X) x = x := rfl

/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  given: (X : TopCat.{u})
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[simp]

中文:
定理 coe_id
  条件: (X : TopCat.{u})
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[simp]
-/
@[simp] theorem coe_id (X : TopCat.{u}) : (𝟙 X : X -> X) = id := rfl

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

@[simp]

中文:
引理 hom_comp
  条件: {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl

@[simp]
-/
lemma hom_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp]
/--
theorem `comp_app` / 定理 `comp_app`

English:
theorem comp_app
  given: {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: rfl

中文:
定理 comp_app
  条件: {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: rfl
-/
theorem comp_app {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X -> Z) x = g (f x) := rfl

/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

@[ext]

中文:
定理 coe_comp
  条件: {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl

@[ext]
-/
@[simp] theorem coe_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : X -> Z) = g ∘ f := rfl

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : TopCat.{u}} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[ext]

中文:
引理 hom_ext
  条件: {X Y : TopCat.{u}} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[ext]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : TopCat.{u}} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : TopCat.{u}} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

@[simp]

中文:
引理 ext
  条件: {X Y : TopCat.{u}} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : TopCat.{u}} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  条件: {X Y : 类型u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
  证明: rfl

@[simp]
-/
lemma hom_ofHom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    (ofHom f).hom = f := rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : TopCat.{u}} (f : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {X Y : TopCat.{u}} (f : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma ofHom_hom {X Y : TopCat.{u}} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {X : Type u} [TopologicalSpace X]
  statement: ofHom (ContinuousMap.id X) = 𝟙 (of X)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {X : 类型u} [TopologicalSpace X]
  结论: ofHom (ContinuousMap.id X) = 𝟙 (of X)
  证明: rfl

@[simp]
-/
lemma ofHom_id {X : Type u} [TopologicalSpace X] : ofHom (ContinuousMap.id X) = 𝟙 (of X) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {X Y Z : 类型u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  证明: rfl
-/
lemma ofHom_comp {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X)
  proof: rfl

中文:
引理 ofHom_apply
  条件: {X Y : 类型u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X)
  证明: rfl
-/
lemma ofHom_apply {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    (ofHom f) x = f x := rfl

/--
lemma `hom_inv_id_apply` / 引理 `hom_inv_id_apply`

English:
lemma hom_inv_id_apply
  given: {X Y : TopCat.{u}} (f : X ≅ Y) (x : X)
  statement: f.inv (f.hom x) = x
  proof: by
  simp

中文:
引理 hom_inv_id_apply
  条件: {X Y : TopCat.{u}} (f : X ≅ Y) (x : X)
  结论: f.inv (f.hom x) = x
  证明: by
  simp
-/
lemma hom_inv_id_apply {X Y : TopCat.{u}} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x := by
  simp

/--
lemma `inv_hom_id_apply` / 引理 `inv_hom_id_apply`

English:
lemma inv_hom_id_apply
  given: {X Y : TopCat.{u}} (f : X ≅ Y) (y : Y)
  statement: f.hom (f.inv y) = y
  proof: by
  simp

中文:
引理 inv_hom_id_apply
  条件: {X Y : TopCat.{u}} (f : X ≅ Y) (y : Y)
  结论: f.hom (f.inv y) = y
  证明: by
  simp
-/
lemma inv_hom_id_apply {X Y : TopCat.{u}} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y := by
  simp

/-- Morphisms in `TopCat` are equivalent to continuous maps. -/
@[simps]
/--
Definition of `Hom.equivContinuousMap` / `Hom.equivContinuousMap` 的定义

English:
definition Hom.equivContinuousMap
  signature: (X Y : TopCat.{u})
  body: f.hom
  invFun f := ofHom f

中文:
定义 Hom.equivContinuousMap
  签名: (X Y : TopCat.{u})
  定义体: f.hom
  invFun f := ofHom f

Depends on / 依赖: f.hom
-/
def Hom.equivContinuousMap (X Y : TopCat.{u}) : (X ⟶ Y) ≃ C(X, Y) where
  toFun f := f.hom
  invFun f := ofHom f

/--
Replace a function coercion for a morphism `TopCat.of X ⟶ TopCat.of Y` with the definitionally
equal function coercion for a continuous map `C(X, Y)`.
-/
@[deprecated "No replacement" (since := "2026-04-23")]
/--
theorem `coe_of_of` / 定理 `coe_of_of`

English:
theorem coe_of_of
  statement: {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  proof: rfl

中文:
定理 coe_of_of
  结论: {X Y : 类型u} [TopologicalSpace X] [TopologicalSpace Y]
  证明: rfl
-/
theorem coe_of_of {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} {x} :
    @DFunLike.coe (TopCat.of X ⟶ TopCat.of Y) ((CategoryTheory.forget TopCat).obj (TopCat.of X))
      (fun _ => (CategoryTheory.forget TopCat).obj (TopCat.of Y)) ConcreteCategory.instFunLike
      (ofHom f) x =
    @DFunLike.coe C(X, Y) X
      (fun _ => Y) _
      f x :=
  rfl

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited TopCat
  body: ⟨TopCat.of Empty⟩

中文:
实例 inhabited
  签名: : Inhabited TopCat
  定义体: ⟨TopCat.of Empty⟩

Depends on / 依赖: TopCat, TopCat.of
-/
instance inhabited : Inhabited TopCat :=
  ⟨TopCat.of Empty⟩

/--
Definition of `discrete` / `discrete` 的定义

English:
definition discrete
  signature: : Type u ⥤ TopCat.{u} where
  body: @of X ⊥
map f := @ofHom _ _ ⊥ ⊥ @ContinuousMap.mk _ _ ⊥ ⊥ f continuous_bot

中文:
定义 discrete
  签名: : 类型u ⥤ TopCat.{u} where
  定义体: @of X ⊥
map f := @ofHom _ _ ⊥ ⊥ @ContinuousMap.mk _ _ ⊥ ⊥ f continuous_bot
-/
def discrete : Type u ⥤ TopCat.{u} where
  obj X := @of X ⊥
map f := @ofHom _ _ ⊥ ⊥ @ContinuousMap.mk _ _ ⊥ ⊥ f continuous_bot

instance {X : Type u} : DiscreteTopology (discrete.obj X) :=
  ⟨rfl⟩

/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: : Type u ⥤ TopCat.{u} where
  body: @of X ⊤
map f := @ofHom _ _ ⊤ ⊤ @ContinuousMap.mk _ _ ⊤ ⊤ f continuous_top

中文:
定义 trivial
  签名: : 类型u ⥤ TopCat.{u} where
  定义体: @of X ⊤
map f := @ofHom _ _ ⊤ ⊤ @ContinuousMap.mk _ _ ⊤ ⊤ f continuous_top
-/
def trivial : Type u ⥤ TopCat.{u} where
  obj X := @of X ⊤
map f := @ofHom _ _ ⊤ ⊤ @ContinuousMap.mk _ _ ⊤ ⊤ f continuous_top

/-- Any homeomorphisms induces an isomorphism in `Top`. -/
@[simps]
/--
Definition of `isoOfHomeo` / `isoOfHomeo` 的定义

English:
definition isoOfHomeo
  signature: {X Y : TopCat.{u}} (f : X ≃ₜ Y)
  body: ofHom f
  inv := ofHom f.symm

中文:
定义 isoOfHomeo
  签名: {X Y : TopCat.{u}} (f : X ≃ₜ Y)
  定义体: ofHom f
  inv := ofHom f.symm
-/
def isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := ofHom f
  inv := ofHom f.symm

/-- Any isomorphism in `Top` induces a homeomorphism. -/
@[simps]
/--
Definition of `homeoOfIso` / `homeoOfIso` 的定义

English:
definition homeoOfIso
  signature: {X Y : TopCat.{u}} (f : X ≅ Y)
  body: f.hom
  invFun := f.inv
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := f.hom.hom.continuous
  continuous_invFun := f.inv.hom.continuous

@[simp]

中文:
定义 homeoOfIso
  签名: {X Y : TopCat.{u}} (f : X ≅ Y)
  定义体: f.hom
  invFun := f.inv
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := f.hom.hom.continuous
  continuous_invFun := f.inv.hom.continuous

@[simp]

Depends on / 依赖: f.hom
-/
def homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := f.hom.hom.continuous
  continuous_invFun := f.inv.hom.continuous

@[simp]
/--
theorem `of_isoOfHomeo` / 定理 `of_isoOfHomeo`

English:
theorem of_isoOfHomeo
  given: {X Y : TopCat.{u}} (f : X ≃ₜ Y)
  statement: homeoOfIso (isoOfHomeo f) = f
  proof: by
  ext
  rfl

@[simp]

中文:
定理 of_isoOfHomeo
  条件: {X Y : TopCat.{u}} (f : X ≃ₜ Y)
  结论: homeoOfIso (isoOfHomeo f) = f
  证明: by
  ext
  rfl

@[simp]
-/
theorem of_isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : homeoOfIso (isoOfHomeo f) = f := by
  ext
  rfl

@[simp]
/--
theorem `of_homeoOfIso` / 定理 `of_homeoOfIso`

English:
theorem of_homeoOfIso
  given: {X Y : TopCat.{u}} (f : X ≅ Y)
  statement: isoOfHomeo (homeoOfIso f) = f
  proof: by
  ext
  rfl

中文:
定理 of_homeoOfIso
  条件: {X Y : TopCat.{u}} (f : X ≅ Y)
  结论: isoOfHomeo (homeoOfIso f) = f
  证明: by
  ext
  rfl
-/
theorem of_homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : isoOfHomeo (homeoOfIso f) = f := by
  ext
  rfl

/--
lemma `isIso_of_bijective_of_isOpenMap` / 引理 `isIso_of_bijective_of_isOpenMap`

English:
lemma isIso_of_bijective_of_isOpenMap
  statement: {X Y : TopCat.{u}} (f : X ⟶ Y)
  proof: let e : X ≃ₜ Y :=
    (Equiv.ofBijective f hfbij).toHomeomorphOfContinuousOpen f.hom.continuous hfcl
inferInstanceAs IsIso (TopCat.isoOfHomeo e).hom

中文:
引理 isIso_of_bijective_of_isOpenMap
  结论: {X Y : TopCat.{u}} (f : X ⟶ Y)
  证明: let e : X ≃ₜ Y :=
    (Equiv.ofBijective f hfbij).toHomeomorphOfContinuousOpen f.hom.continuous hfcl
inferInstanceAs IsIso (TopCat.isoOfHomeo e).hom

Depends on / 依赖: Equiv.ofBijective, TopCat, TopCat.isoOfHomeo, continuous, f.hom.continuous, isoOfHomeo, ofBijective, toHomeomorphOfContinuousOpen
-/
lemma isIso_of_bijective_of_isOpenMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hfbij : Function.Bijective f) (hfcl : IsOpenMap f) : IsIso f :=
  let e : X ≃ₜ Y :=
    (Equiv.ofBijective f hfbij).toHomeomorphOfContinuousOpen f.hom.continuous hfcl
inferInstanceAs IsIso (TopCat.isoOfHomeo e).hom

/--
lemma `isIso_of_bijective_of_isClosedMap` / 引理 `isIso_of_bijective_of_isClosedMap`

English:
lemma isIso_of_bijective_of_isClosedMap
  statement: {X Y : TopCat.{u}} (f : X ⟶ Y)
  proof: let e : X ≃ₜ Y :=
    (Equiv.ofBijective f hfbij).toHomeomorphOfContinuousClosed f.hom.continuous hfcl
inferInstanceAs IsIso (TopCat.isoOfHomeo e).hom

中文:
引理 isIso_of_bijective_of_isClosedMap
  结论: {X Y : TopCat.{u}} (f : X ⟶ Y)
  证明: let e : X ≃ₜ Y :=
    (Equiv.ofBijective f hfbij).toHomeomorphOfContinuousClosed f.hom.continuous hfcl
inferInstanceAs IsIso (TopCat.isoOfHomeo e).hom

Depends on / 依赖: Equiv.ofBijective, TopCat, TopCat.isoOfHomeo, continuous, f.hom.continuous, isoOfHomeo, ofBijective, toHomeomorphOfContinuousClosed
-/
lemma isIso_of_bijective_of_isClosedMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hfbij : Function.Bijective f) (hfcl : IsClosedMap f) : IsIso f :=
  let e : X ≃ₜ Y :=
    (Equiv.ofBijective f hfbij).toHomeomorphOfContinuousClosed f.hom.continuous hfcl
inferInstanceAs IsIso (TopCat.isoOfHomeo e).hom

/--
lemma `isIso_iff_isHomeomorph` / 引理 `isIso_iff_isHomeomorph`

English:
lemma isIso_iff_isHomeomorph
  given: {X Y : TopCat.{u}} (f : X ⟶ Y)
  proof: ⟨fun _ => (homeoOfIso (asIso f)).isHomeomorph,
    fun H => isIso_of_bijective_of_isOpenMap _ H.bijective H.isOpenMap⟩

中文:
引理 isIso_iff_isHomeomorph
  条件: {X Y : TopCat.{u}} (f : X ⟶ Y)
  证明: ⟨fun _ => (homeoOfIso (asIso f)).isHomeomorph,
    fun H => isIso_of_bijective_of_isOpenMap _ H.bijective H.isOpenMap⟩

Depends on / 依赖: H.bijective, H.isOpenMap, bijective, homeoOfIso, isHomeomorph, isIso_of_bijective_of_isOpenMap, isOpenMap
-/
lemma isIso_iff_isHomeomorph {X Y : TopCat.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsHomeomorph f :=
  ⟨fun _ => (homeoOfIso (asIso f)).isHomeomorph,
    fun H => isIso_of_bijective_of_isOpenMap _ H.bijective H.isOpenMap⟩

/--
theorem `isOpenEmbedding_iff_comp_isIso` / 定理 `isOpenEmbedding_iff_comp_isIso`

English:
theorem isOpenEmbedding_iff_comp_isIso
  given: {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g]
  proof: (TopCat.homeoOfIso (asIso g)).isOpenEmbedding.of_comp_iff f

@[simp]

中文:
定理 isOpenEmbedding_iff_comp_isIso
  条件: {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g]
  证明: (TopCat.homeoOfIso (asIso g)).isOpenEmbedding.of_comp_iff f

@[simp]

Depends on / 依赖: TopCat, TopCat.homeoOfIso, homeoOfIso, isOpenEmbedding, isOpenEmbedding.of_comp_iff, of_comp_iff
-/
theorem isOpenEmbedding_iff_comp_isIso {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    IsOpenEmbedding (f ≫ g) ↔ IsOpenEmbedding f :=
  (TopCat.homeoOfIso (asIso g)).isOpenEmbedding.of_comp_iff f

@[simp]
/--
theorem `isOpenEmbedding_iff_comp_isIso'` / 定理 `isOpenEmbedding_iff_comp_isIso'`

English:
theorem isOpenEmbedding_iff_comp_isIso'
  given: {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g]
  proof: by
  simp only
  exact isOpenEmbedding_iff_comp_isIso f g

中文:
定理 isOpenEmbedding_iff_comp_isIso'
  条件: {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g]
  证明: by
  simp only
  exact isOpenEmbedding_iff_comp_isIso f g

Depends on / 依赖: isOpenEmbedding_iff_comp_isIso
-/
theorem isOpenEmbedding_iff_comp_isIso' {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    IsOpenEmbedding (g ∘ f) ↔ IsOpenEmbedding f := by
  simp only
  exact isOpenEmbedding_iff_comp_isIso f g

/--
theorem `isOpenEmbedding_iff_isIso_comp` / 定理 `isOpenEmbedding_iff_isIso_comp`

English:
theorem isOpenEmbedding_iff_isIso_comp
  given: {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f]
  proof: by
  constructor
  · intro h
    convert! h.comp (TopCat.homeoOfIso (asIso f).symm).isOpenEmbedding
    exact congr_arg (DFunLike.coe ∘ ConcreteCategory.hom) (IsIso.inv_hom_id_assoc f g).symm
  · exact fun h => h.comp (TopCat.homeoOfIso (asIso f)).isOpenEmbedding

@[simp]

中文:
定理 isOpenEmbedding_iff_isIso_comp
  条件: {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f]
  证明: by
  constructor
  · intro h
    convert! h.comp (TopCat.homeoOfIso (asIso f).symm).isOpenEmbedding
    exact congr_arg (DFunLike.coe ∘ ConcreteCategory.hom) (IsIso.inv_hom_id_assoc f g).symm
  · exact fun h => h.comp (TopCat.homeoOfIso (asIso f)).isOpenEmbedding

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, DFunLike, DFunLike.coe, IsIso.inv_hom_id_assoc, TopCat, TopCat.homeoOfIso, congr_arg, convert, h.comp, homeoOfIso, inv_hom_id_assoc, isOpenEmbedding
-/
theorem isOpenEmbedding_iff_isIso_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    IsOpenEmbedding (f ≫ g) ↔ IsOpenEmbedding g := by
  constructor
  · intro h
    convert! h.comp (TopCat.homeoOfIso (asIso f).symm).isOpenEmbedding
    exact congr_arg (DFunLike.coe ∘ ConcreteCategory.hom) (IsIso.inv_hom_id_assoc f g).symm
  · exact fun h => h.comp (TopCat.homeoOfIso (asIso f)).isOpenEmbedding

@[simp]
/--
theorem `isOpenEmbedding_iff_isIso_comp'` / 定理 `isOpenEmbedding_iff_isIso_comp'`

English:
theorem isOpenEmbedding_iff_isIso_comp'
  given: {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f]
  proof: by
  simp only
  exact isOpenEmbedding_iff_isIso_comp f g

中文:
定理 isOpenEmbedding_iff_isIso_comp'
  条件: {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f]
  证明: by
  simp only
  exact isOpenEmbedding_iff_isIso_comp f g

Depends on / 依赖: isOpenEmbedding_iff_isIso_comp
-/
theorem isOpenEmbedding_iff_isIso_comp' {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    IsOpenEmbedding (g ∘ f) ↔ IsOpenEmbedding g := by
  simp only
  exact isOpenEmbedding_iff_isIso_comp f g

/--
Definition of `isEmbedding` / `isEmbedding` 的定义

English:
abbreviation isEmbedding
  signature: : MorphismProperty TopCat
  body: fun ⦃A X : TopCat⦄ (f : A ⟶ X) => Topology.IsEmbedding f.hom

@[simp]

中文:
缩写 isEmbedding
  签名: : Morphism命题erty TopCat
  定义体: fun ⦃A X : TopCat⦄ (f : A ⟶ X) => Topology.IsEmbedding f.hom

@[simp]

Depends on / 依赖: IsEmbedding, TopCat, Topology, Topology.IsEmbedding, f.hom
-/
abbrev isEmbedding : MorphismProperty TopCat :=
  fun ⦃A X : TopCat⦄ (f : A ⟶ X) => Topology.IsEmbedding f.hom

@[simp]
/--
lemma `isEmbedding_iff` / 引理 `isEmbedding_iff`

English:
lemma isEmbedding_iff
  given: ⦃A X
  statement: TopCat⦄ (f : A ⟶ X) : isEmbedding f ↔ Topology.IsEmbedding f.hom
  proof: .rfl

中文:
引理 isEmbedding_iff
  条件: ⦃A X
  结论: TopCat⦄ (f : A ⟶ X) : isEmbedding f ↔ Topology.IsEmbedding f.hom
  证明: .rfl
-/
lemma isEmbedding_iff ⦃A X : TopCat⦄ (f : A ⟶ X) : isEmbedding f ↔ Topology.IsEmbedding f.hom :=
  .rfl

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: {X Y : TopCat.{u}} (y : Y)
  body: ofHom ⟨fun _ => y, by fun_prop⟩

@[simp]

中文:
定义 const
  签名: {X Y : TopCat.{u}} (y : Y)
  定义体: ofHom ⟨fun _ => y, by fun_prop⟩

@[simp]

Depends on / 依赖: fun_prop
-/
def const {X Y : TopCat.{u}} (y : Y) : X ⟶ Y :=
  ofHom ⟨fun _ => y, by fun_prop⟩

@[simp]
/--
lemma `const_apply` / 引理 `const_apply`

English:
lemma const_apply
  given: {X Y : TopCat.{u}} (y : Y) (x : X)
  proof: rfl

中文:
引理 const_apply
  条件: {X Y : TopCat.{u}} (y : Y) (x : X)
  证明: rfl
-/
lemma const_apply {X Y : TopCat.{u}} (y : Y) (x : X) :
    const y x = y := rfl

end TopCat
