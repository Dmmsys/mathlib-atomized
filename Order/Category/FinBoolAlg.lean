/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Category.BoolAlg
public import Mathlib.Order.Category.FinBddDistLat
public import Mathlib.Order.Hom.CompleteLattice
public import Mathlib.Data.Set.Subsingleton

/-!
# The category of finite Boolean algebras

This file defines `FinBoolAlg`, the category of finite Boolean algebras.

## TODO

Birkhoff's representation for finite Boolean algebras.

```
FintypeCat_to_FinBoolAlg_op.left_op ⋙ FinBoolAlg.dual ≅
FintypeCat_to_FinBoolAlg_op.left_op
```

`FinBoolAlg` is essentially small.
-/

@[expose] public section


universe u

open CategoryTheory OrderDual Opposite

/--
Definition of `FinBoolAlg` / `FinBoolAlg` 的定义

English:
structure FinBoolAlg
  parameters: extends BoolAlg
  extends: BoolAlg
  axioms and operations (1):
    - [isFintype : Fintype toBoolAlg]

中文:
结构 FinBoolAlg
  参数: extends 布尔Alg
  继承: BoolAlg
  公理与运算 (1 个):
    - [isFintype : Fintype to布尔Alg]
-/
structure FinBoolAlg extends BoolAlg where
  [isFintype : Fintype toBoolAlg]

attribute [instance] FinBoolAlg.isFintype

namespace FinBoolAlg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort FinBoolAlg Type*
  body: ⟨fun X => X.carrier⟩

中文:
实例 :
  签名: CoeSort Fin布尔Alg 类型
  定义体: ⟨fun X => X.carrier⟩

Depends on / 依赖: X.carrier, carrier
-/
instance : CoeSort FinBoolAlg Type* :=
  ⟨fun X => X.carrier⟩

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (α : Type*) [BooleanAlgebra α] [Fintype α]
  body: α

中文:
缩写 of
  签名: (α : 类型) [布尔eanAlgebra α] [Fintype α]
  定义体: α
-/
abbrev of (α : Type*) [BooleanAlgebra α] [Fintype α] : FinBoolAlg where
  carrier := α

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (α : Type*) [BooleanAlgebra α] [Fintype α]
  statement: ↥(of α) = α
  proof: rfl

中文:
定理 coe_of
  条件: (α : 类型) [布尔eanAlgebra α] [Fintype α]
  结论: ↥(of α) = α
  证明: rfl
-/
theorem coe_of (α : Type*) [BooleanAlgebra α] [Fintype α] : ↥(of α) = α :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited FinBoolAlg
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: Inhabited Fin布尔Alg
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited FinBoolAlg :=
  ⟨of PUnit⟩

/--
Instance `largeCategory` / 实例 `largeCategory`

English:
instance largeCategory
  signature: : LargeCategory FinBoolAlg
  body: inferInstanceAs Category (InducedCategory _ toBoolAlg)

中文:
实例 largeCategory
  签名: : LargeCategory Fin布尔Alg
  定义体: inferInstanceAs Category (InducedCategory _ toBoolAlg)

Depends on / 依赖: Category, InducedCategory, toBoolAlg
-/
instance largeCategory : LargeCategory FinBoolAlg :=
inferInstanceAs Category (InducedCategory _ toBoolAlg)

/--
Instance `concreteCategory` / 实例 `concreteCategory`

English:
instance concreteCategory
  signature: : ConcreteCategory FinBoolAlg (BoundedLatticeHom · ·)
  body: inferInstanceAs ConcreteCategory (InducedCategory _ toBoolAlg) _

中文:
实例 concreteCategory
  签名: : ConcreteCategory Fin布尔Alg (BoundedLatticeHom · ·)
  定义体: inferInstanceAs ConcreteCategory (InducedCategory _ toBoolAlg) _

Depends on / 依赖: ConcreteCategory, InducedCategory, toBoolAlg
-/
instance concreteCategory : ConcreteCategory FinBoolAlg (BoundedLatticeHom · ·) :=
inferInstanceAs ConcreteCategory (InducedCategory _ toBoolAlg) _

/--
Instance `hasForgetToBoolAlg` / 实例 `hasForgetToBoolAlg`

English:
instance hasForgetToBoolAlg
  signature: : HasForget₂ FinBoolAlg BoolAlg
  body: inferInstanceAs HasForget₂ (InducedCategory _ toBoolAlg) _

中文:
实例 hasForgetToBoolAlg
  签名: : HasForget₂ Fin布尔Alg 布尔Alg
  定义体: inferInstanceAs HasForget₂ (InducedCategory _ toBoolAlg) _

Depends on / 依赖: InducedCategory, toBoolAlg
-/
instance hasForgetToBoolAlg : HasForget₂ FinBoolAlg BoolAlg :=
inferInstanceAs HasForget₂ (InducedCategory _ toBoolAlg) _

/--
Instance `hasForgetToFinBddDistLat` / 实例 `hasForgetToFinBddDistLat`

English:
instance hasForgetToFinBddDistLat
  signature: : HasForget₂ FinBoolAlg FinBddDistLat where
  body: .of X
  forget₂.map f := FinBddDistLat.ofHom f.hom.hom

中文:
实例 hasForgetToFinBddDistLat
  签名: : HasForget₂ Fin布尔Alg FinBddDistLat where
  定义体: .of X
  forget₂.map f := FinBddDistLat.ofHom f.hom.hom
-/
instance hasForgetToFinBddDistLat : HasForget₂ FinBoolAlg FinBddDistLat where
  forget₂.obj X := .of X
  forget₂.map f := FinBddDistLat.ofHom f.hom.hom

/--
Instance `forgetToBoolAlg_full` / 实例 `forgetToBoolAlg_full`

English:
instance forgetToBoolAlg_full
  signature: : (forget₂ FinBoolAlg BoolAlg).Full
  body: InducedCategory.full _

中文:
实例 forgetToBoolAlg_full
  签名: : (forget₂ Fin布尔Alg 布尔Alg).Full
  定义体: InducedCategory.full _

Depends on / 依赖: AddCommGroup, InducedCategory, InducedCategory.full
-/
instance forgetToBoolAlg_full : (forget₂ FinBoolAlg BoolAlg).Full :=
  InducedCategory.full _

/--
Instance `forgetToBoolAlgFaithful` / 实例 `forgetToBoolAlgFaithful`

English:
instance forgetToBoolAlgFaithful
  signature: : (forget₂ FinBoolAlg BoolAlg).Faithful
  body: InducedCategory.faithful _

@[simps]

中文:
实例 forgetToBoolAlgFaithful
  签名: : (forget₂ Fin布尔Alg 布尔Alg).Faithful
  定义体: InducedCategory.faithful _

@[simps]

Depends on / 依赖: InducedCategory, InducedCategory.faithful, faithful
-/
instance forgetToBoolAlgFaithful : (forget₂ FinBoolAlg BoolAlg).Faithful :=
  InducedCategory.faithful _

@[simps]
/--
Instance `hasForgetToFinPartOrd` / 实例 `hasForgetToFinPartOrd`

English:
instance hasForgetToFinPartOrd
  signature: : HasForget₂ FinBoolAlg FinPartOrd where
  body: .of X
  forget₂.map {X Y} f := InducedCategory.homMk (PartOrd.ofHom f.hom.hom)

中文:
实例 hasForgetToFinPartOrd
  签名: : HasForget₂ Fin布尔Alg FinPartOrd where
  定义体: .of X
  forget₂.map {X Y} f := InducedCategory.homMk (PartOrd.ofHom f.hom.hom)
-/
instance hasForgetToFinPartOrd : HasForget₂ FinBoolAlg FinPartOrd where
  forget₂.obj X := .of X
  forget₂.map {X Y} f := InducedCategory.homMk (PartOrd.ofHom f.hom.hom)

/--
Instance `forgetToFinPartOrdFaithful` / 实例 `forgetToFinPartOrdFaithful`

English:
instance forgetToFinPartOrdFaithful
  signature: : (forget₂ FinBoolAlg FinPartOrd).Faithful where
  body: by
    ext x
    exact CategoryTheory.congr_fun h x

中文:
实例 forgetToFinPartOrdFaithful
  签名: : (forget₂ Fin布尔Alg FinPartOrd).Faithful where
  定义体: by
    ext x
    exact CategoryTheory.congr_fun h x

Depends on / 依赖: CategoryTheory, CategoryTheory.congr_fun, congr_fun
-/
instance forgetToFinPartOrdFaithful : (forget₂ FinBoolAlg FinPartOrd).Faithful where
  map_injective h := by
    ext x
    exact CategoryTheory.congr_fun h x

/-- Constructs an equivalence between finite Boolean algebras from an order isomorphism between
them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : FinBoolAlg.{u}} (e : α ≃o β)
  body: InducedCategory.homMk (BoolAlg.ofHom e)
  inv := InducedCategory.homMk (BoolAlg.ofHom e.symm)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

中文:
定义 Iso.mk
  签名: {α β : Fin布尔Alg.{u}} (e : α ≃o β)
  定义体: InducedCategory.homMk (BoolAlg.ofHom e)
  inv := InducedCategory.homMk (BoolAlg.ofHom e.symm)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
-/
def Iso.mk {α β : FinBoolAlg.{u}} (e : α ≃o β) : α ≅ β where
  hom := InducedCategory.homMk (BoolAlg.ofHom e)
  inv := InducedCategory.homMk (BoolAlg.ofHom e.symm)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps map]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : FinBoolAlg ⥤ FinBoolAlg where
  body: of Xᵒᵈ
  map f := InducedCategory.homMk (BoolAlg.ofHom f.hom.hom.dual)

中文:
定义 dual
  签名: : Fin布尔Alg ⥤ Fin布尔Alg where
  定义体: of Xᵒᵈ
  map f := InducedCategory.homMk (BoolAlg.ofHom f.hom.hom.dual)
-/
def dual : FinBoolAlg ⥤ FinBoolAlg where
  obj X := of Xᵒᵈ
  map f := InducedCategory.homMk (BoolAlg.ofHom f.hom.hom.dual)

/-- The equivalence between `FinBoolAlg` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/--
Definition of `dualEquiv` / `dualEquiv` 的定义

English:
definition dualEquiv
  signature: : FinBoolAlg ≌ FinBoolAlg where
  body: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

中文:
定义 dualEquiv
  签名: : Fin布尔Alg ≌ Fin布尔Alg where
  定义体: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
-/
def dualEquiv : FinBoolAlg ≌ FinBoolAlg where
  functor := dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

end FinBoolAlg

/--
theorem `finBoolAlg_dual_comp_forget_to_finBddDistLat` / 定理 `finBoolAlg_dual_comp_forget_to_finBddDistLat`

English:
theorem finBoolAlg_dual_comp_forget_to_finBddDistLat
  proof: rfl

中文:
定理 finBoolAlg_dual_comp_forget_to_finBddDistLat
  证明: rfl
-/
theorem finBoolAlg_dual_comp_forget_to_finBddDistLat :
    FinBoolAlg.dual ⋙ forget₂ FinBoolAlg FinBddDistLat =
      forget₂ FinBoolAlg FinBddDistLat ⋙ FinBddDistLat.dual :=
  rfl

attribute [local instance] FintypeCat.fintype in
/-- The powerset functor. `Set` as a functor. -/
@[simps]
/--
Definition of `fintypeToFinBoolAlgOp` / `fintypeToFinBoolAlgOp` 的定义

English:
definition fintypeToFinBoolAlgOp
  signature: : FintypeCat ⥤ FinBoolAlgᵒᵖ where
  body: op .of (Set X)
  map {X Y} f :=
Quiver.Hom.op InducedCategory.homMk
BoolAlg.ofHom CompleteLatticeHom.setPreimage f

中文:
定义 fintypeToFinBoolAlgOp
  签名: : FintypeCat ⥤ Fin布尔Algᵒᵖ where
  定义体: op .of (Set X)
  map {X Y} f :=
Quiver.Hom.op InducedCategory.homMk
BoolAlg.ofHom CompleteLatticeHom.setPreimage f
-/
noncomputable def fintypeToFinBoolAlgOp : FintypeCat ⥤ FinBoolAlgᵒᵖ where
obj X := op .of (Set X)
  map {X Y} f :=
Quiver.Hom.op InducedCategory.homMk
BoolAlg.ofHom CompleteLatticeHom.setPreimage f
