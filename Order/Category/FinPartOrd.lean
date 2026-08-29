/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.Order.Category.PartOrd

/-!
# The category of finite partial orders

This defines `FinPartOrd`, the category of finite partial orders.

Note: `FinPartOrd` is *not* a subcategory of `BddOrd` because finite orders are not necessarily
bounded.

## TODO

`FinPartOrd` is equivalent to a small category.
-/

@[expose] public section


universe u v

open CategoryTheory


/--
Definition of `FinPartOrd` / `FinPartOrd` 的定义

English:
structure FinPartOrd
  parameters: extends PartOrd
  extends: PartOrd
  axioms and operations (1):
    - [isFintype : Fintype toPartOrd]

中文:
结构 有限偏序
  参数: extends 偏序
  继承: 偏序
  公理与运算 (1 个):
    - [isFintype : 有限类型 toPartOrd]
-/
structure FinPartOrd extends PartOrd where
  [isFintype : Fintype toPartOrd]

namespace FinPartOrd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort FinPartOrd Type*
  body: ⟨fun X => X.toPartOrd⟩

中文:
实例 :
  签名: CoeSort 有限偏序 类型
  定义体: ⟨fun X => X.toPartOrd⟩

Depends on / 依赖: X.toPartOrd, toPartOrd
-/
instance : CoeSort FinPartOrd Type* :=
  ⟨fun X => X.toPartOrd⟩

instance (X : FinPartOrd) : PartialOrder X :=
  X.toPartOrd.str

attribute [instance] FinPartOrd.isFintype

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (α : Type*) [PartialOrder α] [Fintype α]
  body: α

中文:
缩写 of
  签名: (α : 类型) [偏序 α] [有限类型 α]
  定义体: α
-/
abbrev of (α : Type*) [PartialOrder α] [Fintype α] : FinPartOrd where
  carrier := α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited FinPartOrd
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: 可居 有限偏序
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited FinPartOrd :=
  ⟨of PUnit⟩

/--
Instance `largeCategory` / 实例 `largeCategory`

English:
instance largeCategory
  signature: : LargeCategory FinPartOrd
  body: inferInstanceAs Category (InducedCategory _ toPartOrd)

中文:
实例 largeCategory
  签名: : 大范畴 有限偏序
  定义体: inferInstanceAs Category (InducedCategory _ toPartOrd)

Depends on / 依赖: Category, InducedCategory, toPartOrd
-/
instance largeCategory : LargeCategory FinPartOrd :=
inferInstanceAs Category (InducedCategory _ toPartOrd)

/--
Instance `concreteCategory` / 实例 `concreteCategory`

English:
instance concreteCategory
  signature: : ConcreteCategory FinPartOrd (· ->o ·)
  body: inferInstanceAs ConcreteCategory (InducedCategory _ toPartOrd) _

中文:
实例 concreteCategory
  签名: : 余ncrete范畴 有限偏序 (· ->o ·)
  定义体: inferInstanceAs ConcreteCategory (InducedCategory _ toPartOrd) _

Depends on / 依赖: ConcreteCategory, InducedCategory, toPartOrd
-/
instance concreteCategory : ConcreteCategory FinPartOrd (· ->o ·) :=
inferInstanceAs ConcreteCategory (InducedCategory _ toPartOrd) _

/--
Instance `hasForgetToPartOrd` / 实例 `hasForgetToPartOrd`

English:
instance hasForgetToPartOrd
  signature: : HasForget₂ FinPartOrd PartOrd
  body: inferInstanceAs HasForget₂ (InducedCategory _ toPartOrd) _

中文:
实例 hasForgetToPartOrd
  签名: : 有Forget₂ 有限偏序 偏序
  定义体: inferInstanceAs HasForget₂ (InducedCategory _ toPartOrd) _

Depends on / 依赖: InducedCategory, toPartOrd
-/
instance hasForgetToPartOrd : HasForget₂ FinPartOrd PartOrd :=
inferInstanceAs HasForget₂ (InducedCategory _ toPartOrd) _

/--
Instance `hasForgetToFintype` / 实例 `hasForgetToFintype`

English:
instance hasForgetToFintype
  signature: : HasForget₂ FinPartOrd FintypeCat where
  body: .of X
  forget₂.map f := FintypeCat.homMk f.hom

中文:
实例 hasForgetToFintype
  签名: : 有Forget₂ 有限偏序 FintypeCat where
  定义体: .of X
  forget₂.map f := FintypeCat.homMk f.hom
-/
instance hasForgetToFintype : HasForget₂ FinPartOrd FintypeCat where
  forget₂.obj X := .of X
  forget₂.map f := FintypeCat.homMk f.hom

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [PartialOrder X] [Fintype X] [PartialOrder Y] [Fintype Y] (f : X ->o Y)
  body: ConcreteCategory.ofHom (C := FinPartOrd) f

@[simp]

中文:
缩写 ofHom
  签名: {X Y : 类型u} [偏序 X] [有限类型 X] [偏序 Y] [有限类型 Y] (f : X ->o Y)
  定义体: ConcreteCategory.ofHom (C := FinPartOrd) f

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, FinPartOrd
-/
abbrev ofHom {X Y : Type u} [PartialOrder X] [Fintype X] [PartialOrder Y] [Fintype Y] (f : X ->o Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := FinPartOrd) f

@[simp]
/--
lemma `hom_hom_id` / 引理 `hom_hom_id`

English:
lemma hom_hom_id
  given: {X : FinPartOrd}
  statement: (𝟙 X : X ⟶ X).hom.hom = OrderHom.id
  proof: rfl

中文:
引理 hom_hom_id
  条件: {X : 有限偏序}
  结论: (𝟙 X : X ⟶ X).hom.hom = 序态射.id
  证明: rfl
-/
lemma hom_hom_id {X : FinPartOrd} : (𝟙 X : X ⟶ X).hom.hom = OrderHom.id := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (X : FinPartOrd) (x : X)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (X : 有限偏序) (x : X)
  证明: by simp

@[simp]
-/
lemma id_apply (X : FinPartOrd) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/--
lemma `hom_hom_comp` / 引理 `hom_hom_comp`

English:
lemma hom_hom_comp
  given: {X Y Z : FinPartOrd} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 hom_hom_comp
  条件: {X Y Z : 有限偏序} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma hom_hom_comp {X Y Z : FinPartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom.hom = g.hom.hom.comp f.hom.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {X Y Z : FinPartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {X Y Z : 有限偏序} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: by simp

@[ext]
-/
lemma comp_apply {X Y Z : FinPartOrd} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : FinPartOrd} {f g : X ⟶ Y} (hf : f.hom.hom = g.hom.hom)
  statement: f = g
  proof: InducedCategory.hom_ext (ConcreteCategory.ext hf)

@[simp]

中文:
引理 hom_ext
  条件: {X Y : 有限偏序} {f g : X ⟶ Y} (hf : f.hom.hom = g.hom.hom)
  结论: f = g
  证明: InducedCategory.hom_ext (ConcreteCategory.ext hf)

@[simp]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ext, InducedCategory, InducedCategory.hom_ext, hom_ext
-/
lemma hom_ext {X Y : FinPartOrd} {f g : X ⟶ Y} (hf : f.hom.hom = g.hom.hom) : f = g :=
  InducedCategory.hom_ext (ConcreteCategory.ext hf)

@[simp]
/--
lemma `hom_hom_ofHom` / 引理 `hom_hom_ofHom`

English:
lemma hom_hom_ofHom
  statement: {X Y : Type u} [PartialOrder X] [Fintype X] [PartialOrder Y] [Fintype Y]
  proof: rfl

@[simp]

中文:
引理 hom_hom_ofHom
  结论: {X Y : 类型u} [偏序 X] [有限类型 X] [偏序 Y] [有限类型 Y]
  证明: rfl

@[simp]
-/
lemma hom_hom_ofHom {X Y : Type u} [PartialOrder X] [Fintype X] [PartialOrder Y] [Fintype Y]
    (f : X ->o Y) :
  (ofHom f).hom.hom = f := rfl

@[simp]
/--
lemma `ofHom_hom_hom` / 引理 `ofHom_hom_hom`

English:
lemma ofHom_hom_hom
  given: {X Y : FinPartOrd} (f : X ⟶ Y)
  proof: rfl

中文:
引理 ofHom_hom_hom
  条件: {X Y : 有限偏序} (f : X ⟶ Y)
  证明: rfl
-/
lemma ofHom_hom_hom {X Y : FinPartOrd} (f : X ⟶ Y) :
    ofHom f.hom.hom = f := rfl

/-- Constructs an isomorphism of finite partial orders from an order isomorphism between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : FinPartOrd.{u}} (e : α ≃o β)
  body: ofHom e
  inv := ofHom e.symm

中文:
定义 同构.mk
  签名: {α β : 有限偏序.{u}} (e : α ≃o β)
  定义体: ofHom e
  inv := ofHom e.symm
-/
def Iso.mk {α β : FinPartOrd.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : FinPartOrd ⥤ FinPartOrd where
  body: of Xᵒᵈ
  map f := ofHom f.hom.hom.dual

中文:
定义 dual
  签名: : 有限偏序 ⥤ 有限偏序 where
  定义体: of Xᵒᵈ
  map f := ofHom f.hom.hom.dual
-/
def dual : FinPartOrd ⥤ FinPartOrd where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.hom.dual

/-- The equivalence between `FinPartOrd` and itself induced by `OrderDual` both ways. -/
@[simps]
/--
Definition of `dualEquiv` / `dualEquiv` 的定义

English:
definition dualEquiv
  signature: : FinPartOrd ≌ FinPartOrd where
  body: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

中文:
定义 dualEquiv
  签名: : 有限偏序 ≌ 有限偏序 where
  定义体: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
-/
def dualEquiv : FinPartOrd ≌ FinPartOrd where
  functor := dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

end FinPartOrd

/--
theorem `FinPartOrd_dual_comp_forget_to_partOrd` / 定理 `FinPartOrd_dual_comp_forget_to_partOrd`

English:
theorem FinPartOrd_dual_comp_forget_to_partOrd
  proof: rfl

中文:
定理 FinPartOrd_dual_comp_forget_to_partOrd
  证明: rfl
-/
theorem FinPartOrd_dual_comp_forget_to_partOrd :
    FinPartOrd.dual ⋙ forget₂ FinPartOrd PartOrd =
      forget₂ FinPartOrd PartOrd ⋙ PartOrd.dual := rfl
