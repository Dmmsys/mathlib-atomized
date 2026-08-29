/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.CategoryTheory.Category.Bipointed

/-!
# The category of groups with zero

This file defines `GrpWithZero`, the category of groups with zero.
-/

@[expose] public section

assert_not_exists Ring

universe u

open CategoryTheory

/--
Definition of `GrpWithZero` / `GrpWithZero` 的定义

English:
structure GrpWithZero
  parameters: where
  axioms and operations (3):
    - of : :
    - carrier : Type*
    - [str : GroupWithZero carrier]

中文:
结构 带零群
  参数: where
  公理与运算 (3 个):
    - of : :
    - carrier : 类型
    - [str : 带零群 carrier]
-/
structure GrpWithZero where
  /-- Construct a bundled `GrpWithZero` from a `GroupWithZero`. -/
  of ::
  /-- The underlying group with zero. -/
  carrier : Type*
  [str : GroupWithZero carrier]

attribute [instance] GrpWithZero.str

namespace GrpWithZero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort GrpWithZero Type*
  body: ⟨carrier⟩

中文:
实例 :
  签名: CoeSort 带零群 类型
  定义体: ⟨carrier⟩

Depends on / 依赖: carrier
-/
instance : CoeSort GrpWithZero Type* :=
  ⟨carrier⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited GrpWithZero
  body: ⟨of (WithZero PUnit)⟩

中文:
实例 :
  签名: 可居 带零群
  定义体: ⟨of (WithZero PUnit)⟩

Depends on / 依赖: WithZero
-/
instance : Inhabited GrpWithZero :=
  ⟨of (WithZero PUnit)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LargeCategory.{u} GrpWithZero
  body: MonoidWithZeroHom X Y
  id X := MonoidWithZeroHom.id X
  comp f g := g.comp f

中文:
实例 :
  签名: 大范畴.{u} 带零群
  定义体: MonoidWithZeroHom X Y
  id X := MonoidWithZeroHom.id X
  comp f g := g.comp f

Depends on / 依赖: Algebra, MonoidWithZeroHom
-/
instance : LargeCategory.{u} GrpWithZero where
  Hom X Y := MonoidWithZeroHom X Y
  id X := MonoidWithZeroHom.id X
  comp f g := g.comp f

/--
Instance `groupWithZeroConcreteCategory` / 实例 `groupWithZeroConcreteCategory`

English:
instance groupWithZeroConcreteCategory
  signature: : ConcreteCategory GrpWithZero (MonoidWithZeroHom · ·) where
  body: f
  ofHom f := f

中文:
实例 groupWithZeroConcreteCategory
  签名: : 余ncrete范畴 带零群 (带零幺半群态射 · ·) where
  定义体: f
  ofHom f := f
-/
instance groupWithZeroConcreteCategory : ConcreteCategory GrpWithZero (MonoidWithZeroHom · ·) where
  hom f := f
  ofHom f := f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [GroupWithZero X] [GroupWithZero Y]
  body: ConcreteCategory.ofHom f

@[simp]

中文:
缩写 ofHom
  签名: {X Y : 类型u} [带零群 X] [带零群 Y]
  定义体: ConcreteCategory.ofHom f

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {X Y : Type u} [GroupWithZero X] [GroupWithZero Y]
    (f : MonoidWithZeroHom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom f

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {X : GrpWithZero}
  statement: ConcreteCategory.hom (𝟙 X : X ⟶ X) = MonoidWithZeroHom.id X
  proof: rfl

@[simp]

中文:
引理 hom_id
  条件: {X : 带零群}
  结论: 余ncrete范畴.hom (𝟙 X : X ⟶ X) = 带零幺半群态射.id X
  证明: rfl

@[simp]
-/
lemma hom_id {X : GrpWithZero} : ConcreteCategory.hom (𝟙 X : X ⟶ X) = MonoidWithZeroHom.id X := rfl

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {X Y Z : GrpWithZero} {f : X ⟶ Y} {g : Y ⟶ Z}
  proof: rfl

中文:
引理 hom_comp
  条件: {X Y Z : 带零群} {f : X ⟶ Y} {g : Y ⟶ Z}
  证明: rfl
-/
lemma hom_comp {X Y Z : GrpWithZero} {f : X ⟶ Y} {g : Y ⟶ Z} :
    ConcreteCategory.hom (f ≫ g) = g.comp f := rfl

/--
lemma `coe_id` / 引理 `coe_id`

English:
lemma coe_id
  given: {X : GrpWithZero}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

中文:
引理 coe_id
  条件: {X : 带零群}
  结论: (𝟙 X : X -> X) = id
  证明: rfl
-/
lemma coe_id {X : GrpWithZero} : (𝟙 X : X -> X) = id := rfl

/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : GrpWithZero} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

中文:
引理 coe_comp
  条件: {X Y Z : 带零群} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl
-/
lemma coe_comp {X Y Z : GrpWithZero} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: {X Y : GrpWithZero} (f : X ⟶ Y)
  proof: rfl

中文:
引理 forget_map
  条件: {X Y : 带零群} (f : X ⟶ Y)
  证明: rfl
-/
@[simp] lemma forget_map {X Y : GrpWithZero} (f : X ⟶ Y) :
    (forget GrpWithZero).map f = (f : _ -> _) :=
  rfl

/--
Instance `hasForgetToBipointed` / 实例 `hasForgetToBipointed`

English:
instance hasForgetToBipointed
  signature: : HasForget₂ GrpWithZero Bipointed where
  body: { obj := fun X => ⟨X, 0, 1⟩
        map := fun f => ⟨f, f.map_zero', f.map_one'⟩ }

中文:
实例 hasForgetToBipointed
  签名: : 有Forget₂ 带零群 Bipointed where
  定义体: { obj := fun X => ⟨X, 0, 1⟩
        map := fun f => ⟨f, f.map_zero', f.map_one'⟩ }

Depends on / 依赖: f.map_one, f.map_zero, map_one, map_zero
-/
instance hasForgetToBipointed : HasForget₂ GrpWithZero Bipointed where
  forget₂ :=
      { obj := fun X => ⟨X, 0, 1⟩
        map := fun f => ⟨f, f.map_zero', f.map_one'⟩ }

/--
Instance `hasForgetToMon` / 实例 `hasForgetToMon`

English:
instance hasForgetToMon
  signature: : HasForget₂ GrpWithZero MonCat where
  body: { obj := fun X => MonCat.of X
        map := fun f => MonCat.ofHom f.toMonoidHom }

中文:
实例 hasForgetToMon
  签名: : 有Forget₂ 带零群 幺半群范畴 where
  定义体: { obj := fun X => MonCat.of X
        map := fun f => MonCat.ofHom f.toMonoidHom }

Depends on / 依赖: MonCat, MonCat.of, MonCat.ofHom, f.toMonoidHom, toMonoidHom
-/
instance hasForgetToMon : HasForget₂ GrpWithZero MonCat where
  forget₂ :=
      { obj := fun X => MonCat.of X
        map := fun f => MonCat.ofHom f.toMonoidHom }

/-- Constructs an isomorphism of groups with zero from a group isomorphism between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : GrpWithZero.{u}} (e : α ≃* β)
  body: ofHom (.ofClass e)
  inv := ofHom (.ofClass e.symm)
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _

中文:
定义 同构.mk
  签名: {α β : 带零群.{u}} (e : α ≃* β)
  定义体: ofHom (.ofClass e)
  inv := ofHom (.ofClass e.symm)
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _
-/
def Iso.mk {α β : GrpWithZero.{u}} (e : α ≃* β) : α ≅ β where
  hom := ofHom (.ofClass e)
  inv := ofHom (.ofClass e.symm)
  hom_inv_id := by
    ext
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext
    exact e.apply_symm_apply _

end GrpWithZero
