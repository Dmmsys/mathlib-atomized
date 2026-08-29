/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.Topology.Bornology.Hom

/-!
# The category of bornologies

This defines `Born`, the category of bornologies.
-/

public section


universe u

open CategoryTheory

/--
Definition of `Born` / `Born` 的定义

English:
structure Born
  parameters: where
  axioms and operations (3):
    - of : :
    - carrier : Type*
    - [str : Bornology carrier]

中文:
结构 Born
  参数: where
  公理与运算 (3 个):
    - of : :
    - carrier : 类型
    - [str : Bornology carrier]
-/
structure Born where
  /-- Construct a bundled `Born` from a `Bornology`. -/
  of ::
  /-- The underlying bornology. -/
  carrier : Type*
  [str : Bornology carrier]

attribute [instance] Born.str

namespace Born

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort Born Type*
  body: ⟨carrier⟩

中文:
实例 :
  签名: CoeSort Born 类型
  定义体: ⟨carrier⟩

Depends on / 依赖: carrier
-/
instance : CoeSort Born Type* :=
  ⟨carrier⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Born
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: Inhabited Born
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited Born :=
  ⟨of PUnit⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LargeCategory.{u} Born
  body: LocallyBoundedMap X Y
  id X := LocallyBoundedMap.id X
  comp f g := g.comp f

中文:
实例 :
  签名: LargeCategory.{u} Born
  定义体: LocallyBoundedMap X Y
  id X := LocallyBoundedMap.id X
  comp f g := g.comp f

Depends on / 依赖: LocallyBoundedMap
-/
instance : LargeCategory.{u} Born where
  Hom X Y := LocallyBoundedMap X Y
  id X := LocallyBoundedMap.id X
  comp f g := g.comp f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory Born (LocallyBoundedMap · ·)
  body: f
  ofHom f := f

中文:
实例 :
  签名: ConcreteCategory Born (LocallyBoundedMap · ·)
  定义体: f
  ofHom f := f
-/
instance : ConcreteCategory Born (LocallyBoundedMap · ·) where
  hom f := f
  ofHom f := f

end Born
