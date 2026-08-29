/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Yuyang Zhao
-/
module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Algebra.Category.Grp.Basic

/-!

## Main definitions and results

* `FiniteGrp` is the category of finite groups.

-/

@[expose] public section

universe u v

open CategoryTheory

/-- The category of finite groups. -/
@[pp_with_univ]
/--
Definition of `FiniteGrp` / `FiniteGrp` 的定义

English:
structure FiniteGrp
  parameters: where
  axioms and operations (2):
    - toGrp : GrpCat.{u}
    - [isFinite : Finite toGrp]

中文:
结构 FiniteGrp
  参数: where
  公理与运算 (2 个):
    - toGrp : 群范畴.{u}
    - [isFinite : 有限 toGrp]
-/
structure FiniteGrp where
  /-- A group that is finite -/
  toGrp : GrpCat.{u}
  [isFinite : Finite toGrp]

/-- The category of finite additive groups. -/
@[pp_with_univ]
/--
Definition of `FiniteAddGrp` / `FiniteAddGrp` 的定义

English:
structure FiniteAddGrp
  parameters: where
  axioms and operations (2):
    - toAddGrp : AddGrpCat.{u}
    - [isFinite : Finite toAddGrp]

中文:
结构 FiniteAddGrp
  参数: where
  公理与运算 (2 个):
    - toAddGrp : 加法群范畴.{u}
    - [isFinite : 有限 toAddGrp]
-/
structure FiniteAddGrp where
  /-- An additive group that is finite -/
  toAddGrp : AddGrpCat.{u}
  [isFinite : Finite toAddGrp]

attribute [to_additive] FiniteGrp

namespace FiniteGrp

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort FiniteGrp.{u} (Type u)
  body: G.toGrp

@[to_additive]

中文:
实例 :
  签名: CoeSort FiniteGrp.{u} (类型u)
  定义体: G.toGrp

@[to_additive]

Depends on / 依赖: G.toGrp
-/
instance : CoeSort FiniteGrp.{u} (Type u) where
  coe G := G.toGrp

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category FiniteGrp
  body: inferInstanceAs Category (InducedCategory _ FiniteGrp.toGrp)

@[to_additive]

中文:
实例 :
  签名: 范畴 FiniteGrp
  定义体: inferInstanceAs Category (InducedCategory _ FiniteGrp.toGrp)

@[to_additive]

Depends on / 依赖: Category, FiniteGrp, FiniteGrp.toGrp, InducedCategory
-/
instance : Category FiniteGrp :=
inferInstanceAs Category (InducedCategory _ FiniteGrp.toGrp)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory FiniteGrp (· ->* ·)
  body: inferInstanceAs ConcreteCategory (InducedCategory _ toGrp) _

@[to_additive]

中文:
实例 :
  签名: 余ncrete范畴 FiniteGrp (· ->* ·)
  定义体: inferInstanceAs ConcreteCategory (InducedCategory _ toGrp) _

@[to_additive]

Depends on / 依赖: ConcreteCategory, InducedCategory
-/
instance : ConcreteCategory FiniteGrp (· ->* ·) :=
inferInstanceAs ConcreteCategory (InducedCategory _ toGrp) _

@[to_additive]
instance (G : FiniteGrp) : Group G := inferInstanceAs Group G.toGrp

@[to_additive]
instance (G : FiniteGrp) : Finite G := G.isFinite

/-- Construct a term of `FiniteGrp` from a type endowed with the structure of a finite group. -/
@[to_additive /-- Construct a term of `FiniteAddGrp` from a type endowed with the structure of a
finite additive group. -/]
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (G : Type u) [Group G] [Finite G]
  body: GrpCat.of G
  isFinite := ‹_›

中文:
定义 of
  签名: (G : 类型u) [群 G] [有限 G]
  定义体: GrpCat.of G
  isFinite := ‹_›

Depends on / 依赖: GrpCat, GrpCat.of
-/
def of (G : Type u) [Group G] [Finite G] : FiniteGrp where
  toGrp := GrpCat.of G
  isFinite := ‹_›

/-- The morphism in `FiniteGrp`, induced from a morphism of the category `GrpCat`. -/
@[to_additive
/-- The morphism in `FiniteAddGrp`, induced from a morphism of the category `AddGrpCat` -/]
/--
Definition of `ofHom` / `ofHom` 的定义

English:
definition ofHom
  signature: {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y] (f : X ->* Y)
  body: InducedCategory.homMk (GrpCat.ofHom f)

@[to_additive]

中文:
定义 ofHom
  签名: {X Y : 类型u} [群 X] [有限 X] [群 Y] [有限 Y] (f : X ->* Y)
  定义体: InducedCategory.homMk (GrpCat.ofHom f)

@[to_additive]

Depends on / 依赖: GrpCat, GrpCat.ofHom, InducedCategory, InducedCategory.homMk
-/
def ofHom {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y] (f : X ->* Y) : of X ⟶ of Y :=
  InducedCategory.homMk (GrpCat.ofHom f)

@[to_additive]
/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y] (f : X ->* Y) (x : X)
  proof: rfl

中文:
引理 ofHom_apply
  条件: {X Y : 类型u} [群 X] [有限 X] [群 Y] [有限 Y] (f : X ->* Y) (x : X)
  证明: rfl
-/
lemma ofHom_apply {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y] (f : X ->* Y) (x : X) :
    ofHom f x = f x :=
  rfl

end FiniteGrp
