/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Category.TopCat.Basic
/-!

# The category of sequential topological spaces

We define the category `Sequential` of sequential topological spaces. We follow the usual template
for defining categories of topological spaces, by giving it the induced category structure from
`TopCat`.
-/

@[expose] public section

open CategoryTheory

universe u

/--
Definition of `Sequential` / `Sequential` 的定义

English:
structure Sequential
  parameters: where
  axioms and operations (2):
    - toTop : TopCat.{u} -- TODO: turn this into `extends`
    - [is_sequential : SequentialSpace toTop]

中文:
结构 Sequential
  参数: where
  公理与运算 (2 个):
    - toTop : TopCat.{u} -- TODO: turn this into `extends`
    - [is_sequential : SequentialSpace toTop]
-/
structure Sequential where
  /-- The underlying topological space of an object of `Sequential`. -/
  toTop : TopCat.{u} -- TODO: turn this into `extends`
  /-- The underlying topological space is sequential. -/
  [is_sequential : SequentialSpace toTop]

namespace Sequential

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Sequential.{u}
  body: ⟨{ toTop := TopCat.of (ULift (Fin 37)) }⟩

中文:
实例 :
  签名: Inhabited Sequential.{u}
  定义体: ⟨{ toTop := TopCat.of (ULift (Fin 37)) }⟩

Depends on / 依赖: TopCat, TopCat.of
-/
instance : Inhabited Sequential.{u} :=
  ⟨{ toTop := TopCat.of (ULift (Fin 37)) }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort Sequential Type*
  body: ⟨fun X => X.toTop⟩

中文:
实例 :
  签名: CoeSort Sequential 类型
  定义体: ⟨fun X => X.toTop⟩

Depends on / 依赖: X.toTop
-/
instance : CoeSort Sequential Type* :=
  ⟨fun X => X.toTop⟩

attribute [instance] is_sequential

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category.{u, u + 1} Sequential.{u}
  body: inferInstanceAs Category (InducedCategory _ toTop)

中文:
实例 :
  签名: Category.{u, u + 1} Sequential.{u}
  定义体: inferInstanceAs Category (InducedCategory _ toTop)

Depends on / 依赖: Category, InducedCategory
-/
instance : Category.{u, u + 1} Sequential.{u} :=
inferInstanceAs Category (InducedCategory _ toTop)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory.{u} Sequential.{u} (C(·, ·))
  body: inferInstanceAs ConcreteCategory (InducedCategory _ toTop) _

中文:
实例 :
  签名: ConcreteCategory.{u} Sequential.{u} (C(·, ·))
  定义体: inferInstanceAs ConcreteCategory (InducedCategory _ toTop) _

Depends on / 依赖: ConcreteCategory, InducedCategory
-/
instance : ConcreteCategory.{u} Sequential.{u} (C(·, ·)) :=
inferInstanceAs ConcreteCategory (InducedCategory _ toTop) _

variable (X : Type u) [TopologicalSpace X] [SequentialSpace X]

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: : Sequential.{u} where
  body: TopCat.of X
  is_sequential := ‹_›

中文:
缩写 of
  签名: : Sequential.{u} where
  定义体: TopCat.of X
  is_sequential := ‹_›

Depends on / 依赖: TopCat, TopCat.of
-/
abbrev of : Sequential.{u} where
  toTop := TopCat.of X
  is_sequential := ‹_›

/-- The fully faithful embedding of `Sequential` in `TopCat`. -/
@[simps!]
/--
Definition of `sequentialToTop` / `sequentialToTop` 的定义

English:
definition sequentialToTop
  signature: : Sequential.{u} ⥤ TopCat.{u}
  body: inducedFunctor _

中文:
定义 sequentialToTop
  签名: : Sequential.{u} ⥤ TopCat.{u}
  定义体: inducedFunctor _

Depends on / 依赖: inducedFunctor
-/
def sequentialToTop : Sequential.{u} ⥤ TopCat.{u} :=
  inducedFunctor _

/--
Definition of `fullyFaithfulSequentialToTop` / `fullyFaithfulSequentialToTop` 的定义

English:
definition fullyFaithfulSequentialToTop
  signature: : sequentialToTop.FullyFaithful
  body: fullyFaithfulInducedFunctor _

中文:
定义 fullyFaithfulSequentialToTop
  签名: : sequentialToTop.FullyFaithful
  定义体: fullyFaithfulInducedFunctor _

Depends on / 依赖: fullyFaithfulInducedFunctor
-/
def fullyFaithfulSequentialToTop : sequentialToTop.FullyFaithful :=
  fullyFaithfulInducedFunctor _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: sequentialToTop.{u}.Full
  body: inferInstanceAs (inducedFunctor _).Full

中文:
实例 :
  签名: sequentialToTop.{u}.Full
  定义体: inferInstanceAs (inducedFunctor _).Full

Depends on / 依赖: inducedFunctor
-/
instance : sequentialToTop.{u}.Full :=
  inferInstanceAs (inducedFunctor _).Full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: sequentialToTop.{u}.Faithful
  body: inferInstanceAs (inducedFunctor _).Faithful

中文:
实例 :
  签名: sequentialToTop.{u}.Faithful
  定义体: inferInstanceAs (inducedFunctor _).Faithful

Depends on / 依赖: Faithful, inducedFunctor
-/
instance : sequentialToTop.{u}.Faithful :=
  inferInstanceAs (inducedFunctor _).Faithful

/-- Construct an isomorphism from a homeomorphism. -/
@[simps hom inv]
/--
Definition of `isoOfHomeo` / `isoOfHomeo` 的定义

English:
definition isoOfHomeo
  signature: {X Y : Sequential.{u}} (f : X ≃ₜ Y)
  body: InducedCategory.homMk (TopCat.ofHom ⟨f, f.continuous⟩)
  inv := InducedCategory.homMk (TopCat.ofHom ⟨f.symm, f.symm.continuous⟩)
  hom_inv_id := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact f.apply_symm_apply x

中文:
定义 isoOfHomeo
  签名: {X Y : Sequential.{u}} (f : X ≃ₜ Y)
  定义体: InducedCategory.homMk (TopCat.ofHom ⟨f, f.continuous⟩)
  inv := InducedCategory.homMk (TopCat.ofHom ⟨f.symm, f.symm.continuous⟩)
  hom_inv_id := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact f.apply_symm_apply x

Depends on / 依赖: InducedCategory, InducedCategory.homMk, TopCat, TopCat.ofHom, continuous, f.continuous
-/
def isoOfHomeo {X Y : Sequential.{u}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := InducedCategory.homMk (TopCat.ofHom ⟨f, f.continuous⟩)
  inv := InducedCategory.homMk (TopCat.ofHom ⟨f.symm, f.symm.continuous⟩)
  hom_inv_id := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact f.apply_symm_apply x

/-- Construct a homeomorphism from an isomorphism. -/
@[simps]
/--
Definition of `homeoOfIso` / `homeoOfIso` 的定义

English:
definition homeoOfIso
  signature: {X Y : Sequential.{u}} (f : X ≅ Y)
  body: f.hom
  invFun := f.inv
  left_inv := f.hom_inv_id_apply
  right_inv := f.inv_hom_id_apply
  continuous_toFun := f.hom.hom.hom.continuous
  continuous_invFun := f.inv.hom.hom.continuous

中文:
定义 homeoOfIso
  签名: {X Y : Sequential.{u}} (f : X ≅ Y)
  定义体: f.hom
  invFun := f.inv
  left_inv := f.hom_inv_id_apply
  right_inv := f.inv_hom_id_apply
  continuous_toFun := f.hom.hom.hom.continuous
  continuous_invFun := f.inv.hom.hom.continuous

Depends on / 依赖: f.hom
-/
def homeoOfIso {X Y : Sequential.{u}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv := f.hom_inv_id_apply
  right_inv := f.inv_hom_id_apply
  continuous_toFun := f.hom.hom.hom.continuous
  continuous_invFun := f.inv.hom.hom.continuous

/-- The equivalence between isomorphisms in `Sequential` and homeomorphisms
of topological spaces. -/
@[simps]
/--
Definition of `isoEquivHomeo` / `isoEquivHomeo` 的定义

English:
definition isoEquivHomeo
  signature: {X Y : Sequential.{u}}
  body: homeoOfIso
  invFun := isoOfHomeo

中文:
定义 isoEquivHomeo
  签名: {X Y : Sequential.{u}}
  定义体: homeoOfIso
  invFun := isoOfHomeo

Depends on / 依赖: homeoOfIso
-/
def isoEquivHomeo {X Y : Sequential.{u}} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo

end Sequential
