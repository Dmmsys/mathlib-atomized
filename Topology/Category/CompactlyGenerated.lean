/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.CategoryTheory.Elementwise
/-!

# Compactly generated topological spaces

This file defines the category of compactly generated topological spaces. These are spaces `X` such
that a map `f : X → Y` is continuous whenever the composition `S → X → Y` is continuous for all
compact Hausdorff spaces `S` mapping continuously to `X`.

## TODO

* `CompactlyGenerated` is a reflective subcategory of `TopCat`.
* `CompactlyGenerated` is Cartesian closed.
* Every first-countable space is `u`-compactly generated for every universe `u`.
-/

@[expose] public section

universe u w

open CategoryTheory Topology TopologicalSpace

/--
Definition of `CompactlyGenerated` / `CompactlyGenerated` 的定义

English:
structure CompactlyGenerated
  parameters: where
  axioms and operations (2):
    - toTop : TopCat.{w}
    - [is_compactly_generated : UCompactlyGeneratedSpace.{u} toTop]

中文:
结构 余mpactlyGenerated
  参数: where
  公理与运算 (2 个):
    - toTop : 顶元素范畴.{w}
    - [is_compactly_generated : UCompactlyGenerated空间.{u} toTop]
-/
structure CompactlyGenerated where
  /-- The underlying topological space of an object of `CompactlyGenerated`. -/
  toTop : TopCat.{w}
  /-- The underlying topological space is compactly generated. -/
  [is_compactly_generated : UCompactlyGeneratedSpace.{u} toTop]

namespace CompactlyGenerated

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited CompactlyGenerated.{u, w}
  body: ⟨{ toTop := TopCat.of (ULift (Fin 37)) }⟩

中文:
实例 :
  签名: 可居 余mpactlyGenerated.{u, w}
  定义体: ⟨{ toTop := TopCat.of (ULift (Fin 37)) }⟩

Depends on / 依赖: TopCat, TopCat.of
-/
instance : Inhabited CompactlyGenerated.{u, w} :=
  ⟨{ toTop := TopCat.of (ULift (Fin 37)) }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort CompactlyGenerated Type*
  body: ⟨fun X => X.toTop⟩

中文:
实例 :
  签名: CoeSort 余mpactlyGenerated 类型
  定义体: ⟨fun X => X.toTop⟩

Depends on / 依赖: X.toTop
-/
instance : CoeSort CompactlyGenerated Type* :=
  ⟨fun X => X.toTop⟩

attribute [instance] is_compactly_generated

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category.{w, w + 1} CompactlyGenerated.{u, w}
  body: inferInstanceAs Category (InducedCategory _ toTop)

中文:
实例 :
  签名: 范畴.{w, w + 1} 余mpactlyGenerated.{u, w}
  定义体: inferInstanceAs Category (InducedCategory _ toTop)

Depends on / 依赖: Category, InducedCategory
-/
instance : Category.{w, w + 1} CompactlyGenerated.{u, w} :=
inferInstanceAs Category (InducedCategory _ toTop)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory.{w} CompactlyGenerated.{u, w} (C(·, ·))
  body: inferInstanceAs ConcreteCategory (InducedCategory _ toTop) _

中文:
实例 :
  签名: 余ncrete范畴.{w} 余mpactlyGenerated.{u, w} (C(·, ·))
  定义体: inferInstanceAs ConcreteCategory (InducedCategory _ toTop) _

Depends on / 依赖: ConcreteCategory, InducedCategory
-/
instance : ConcreteCategory.{w} CompactlyGenerated.{u, w} (C(·, ·)) :=
inferInstanceAs ConcreteCategory (InducedCategory _ toTop) _

variable (X : Type w) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X]

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: : CompactlyGenerated.{u, w} where
  body: TopCat.of X
  is_compactly_generated := ‹_›

中文:
缩写 of
  签名: : 余mpactlyGenerated.{u, w} where
  定义体: TopCat.of X
  is_compactly_generated := ‹_›

Depends on / 依赖: TopCat, TopCat.of
-/
abbrev of : CompactlyGenerated.{u, w} where
  toTop := TopCat.of X
  is_compactly_generated := ‹_›

section

variable {X} {Y : Type w} [TopologicalSpace Y] [UCompactlyGeneratedSpace.{u} Y]

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: (f : C(X, Y))
  body: ConcreteCategory.ofHom f

中文:
缩写 ofHom
  签名: (f : C(X, Y))
  定义体: ConcreteCategory.ofHom f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom (f : C(X, Y)) : of X ⟶ of Y := ConcreteCategory.ofHom f

end

/-- The fully faithful embedding of `CompactlyGenerated` in `TopCat`. -/
@[simps!]
/--
Definition of `compactlyGeneratedToTop` / `compactlyGeneratedToTop` 的定义

English:
definition compactlyGeneratedToTop
  signature: : CompactlyGenerated.{u, w} ⥤ TopCat.{w}
  body: inducedFunctor _

中文:
定义 compactlyGeneratedToTop
  签名: : 余mpactlyGenerated.{u, w} ⥤ 顶元素范畴.{w}
  定义体: inducedFunctor _

Depends on / 依赖: inducedFunctor
-/
def compactlyGeneratedToTop : CompactlyGenerated.{u, w} ⥤ TopCat.{w} :=
  inducedFunctor _

/--
Definition of `fullyFaithfulCompactlyGeneratedToTop` / `fullyFaithfulCompactlyGeneratedToTop` 的定义

English:
definition fullyFaithfulCompactlyGeneratedToTop
  signature: : compactlyGeneratedToTop.{u, w}.FullyFaithful
  body: fullyFaithfulInducedFunctor _

中文:
定义 fullyFaithfulCompactlyGeneratedToTop
  签名: : compactlyGeneratedToTop.{u, w}.满忠实
  定义体: fullyFaithfulInducedFunctor _

Depends on / 依赖: fullyFaithfulInducedFunctor
-/
def fullyFaithfulCompactlyGeneratedToTop : compactlyGeneratedToTop.{u, w}.FullyFaithful :=
  fullyFaithfulInducedFunctor _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: compactlyGeneratedToTop.{u, w}.Full
  body: fullyFaithfulCompactlyGeneratedToTop.full

中文:
实例 :
  签名: compactlyGeneratedToTop.{u, w}.满
  定义体: fullyFaithfulCompactlyGeneratedToTop.full

Depends on / 依赖: fullyFaithfulCompactlyGeneratedToTop, fullyFaithfulCompactlyGeneratedToTop.full
-/
instance : compactlyGeneratedToTop.{u, w}.Full := fullyFaithfulCompactlyGeneratedToTop.full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: compactlyGeneratedToTop.{u, w}.Faithful
  body: fullyFaithfulCompactlyGeneratedToTop.faithful

中文:
实例 :
  签名: compactlyGeneratedToTop.{u, w}.忠实
  定义体: fullyFaithfulCompactlyGeneratedToTop.faithful

Depends on / 依赖: faithful, fullyFaithfulCompactlyGeneratedToTop, fullyFaithfulCompactlyGeneratedToTop.faithful
-/
instance : compactlyGeneratedToTop.{u, w}.Faithful := fullyFaithfulCompactlyGeneratedToTop.faithful

/-- Construct an isomorphism from a homeomorphism. -/
@[simps hom inv]
/--
Definition of `isoOfHomeo` / `isoOfHomeo` 的定义

English:
definition isoOfHomeo
  signature: {X Y : CompactlyGenerated.{u, w}} (f : X ≃ₜ Y)
  body: ofHom ⟨f, f.continuous⟩
  inv := ofHom ⟨f.symm, f.symm.continuous⟩
  hom_inv_id := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact f.apply_symm_apply x

中文:
定义 isoOfHomeo
  签名: {X Y : 余mpactlyGenerated.{u, w}} (f : X ≃ₜ Y)
  定义体: ofHom ⟨f, f.continuous⟩
  inv := ofHom ⟨f.symm, f.symm.continuous⟩
  hom_inv_id := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact f.apply_symm_apply x

Depends on / 依赖: continuous, f.continuous
-/
def isoOfHomeo {X Y : CompactlyGenerated.{u, w}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := ofHom ⟨f, f.continuous⟩
  inv := ofHom ⟨f.symm, f.symm.continuous⟩
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
  signature: {X Y : CompactlyGenerated.{u, w}} (f : X ≅ Y)
  body: f.hom
  invFun := f.inv
  left_inv := f.hom_inv_id_apply
  right_inv := f.inv_hom_id_apply
  continuous_toFun := f.hom.hom.hom.continuous
  continuous_invFun := f.inv.hom.hom.continuous

中文:
定义 homeoOfIso
  签名: {X Y : 余mpactlyGenerated.{u, w}} (f : X ≅ Y)
  定义体: f.hom
  invFun := f.inv
  left_inv := f.hom_inv_id_apply
  right_inv := f.inv_hom_id_apply
  continuous_toFun := f.hom.hom.hom.continuous
  continuous_invFun := f.inv.hom.hom.continuous

Depends on / 依赖: f.hom
-/
def homeoOfIso {X Y : CompactlyGenerated.{u, w}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv := f.hom_inv_id_apply
  right_inv := f.inv_hom_id_apply
  continuous_toFun := f.hom.hom.hom.continuous
  continuous_invFun := f.inv.hom.hom.continuous

/-- The equivalence between isomorphisms in `CompactlyGenerated` and homeomorphisms
of topological spaces. -/
@[simps]
/--
Definition of `isoEquivHomeo` / `isoEquivHomeo` 的定义

English:
definition isoEquivHomeo
  signature: {X Y : CompactlyGenerated.{u, w}}
  body: homeoOfIso
  invFun := isoOfHomeo

中文:
定义 isoEquivHomeo
  签名: {X Y : 余mpactlyGenerated.{u, w}}
  定义体: homeoOfIso
  invFun := isoOfHomeo

Depends on / 依赖: homeoOfIso
-/
def isoEquivHomeo {X Y : CompactlyGenerated.{u, w}} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo

end CompactlyGenerated
