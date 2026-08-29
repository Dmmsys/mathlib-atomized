/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.BddLat
public import Mathlib.Order.Hom.CompleteLattice

/-!
# The category of complete lattices

This file defines `CompleteLat`, the category of complete lattices.
-/

@[expose] public section


universe u

open CategoryTheory

/--
Definition of `CompleteLat` / `CompleteLat` 的定义

English:
structure CompleteLat
  parameters: where
  axioms and operations (3):
    - of : :
    - (carrier : Type*)
    - [str : CompleteLattice carrier]

中文:
结构 余mpleteLat
  参数: where
  公理与运算 (3 个):
    - of : :
    - (carrier : 类型)
    - [str : 完备格 carrier]
-/
structure CompleteLat where
  /-- Construct a bundled `CompleteLat` from the underlying type and typeclass. -/
  of ::
  /-- The underlying lattice. -/
  (carrier : Type*)
  [str : CompleteLattice carrier]

attribute [instance] CompleteLat.str

initialize_simps_projections CompleteLat (carrier -> coe, -str)

namespace CompleteLat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort CompleteLat (Type _)
  body: ⟨CompleteLat.carrier⟩

中文:
实例 :
  签名: CoeSort 余mpleteLat (类型 _)
  定义体: ⟨CompleteLat.carrier⟩

Depends on / 依赖: CompleteLat, CompleteLat.carrier, carrier
-/
instance : CoeSort CompleteLat (Type _) :=
  ⟨CompleteLat.carrier⟩

attribute [coe] CompleteLat.carrier

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (α : Type*) [CompleteLattice α]
  statement: ↥(of α) = α
  proof: rfl

中文:
定理 coe_of
  条件: (α : 类型) [完备格 α]
  结论: ↥(of α) = α
  证明: rfl
-/
theorem coe_of (α : Type*) [CompleteLattice α] : ↥(of α) = α :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited CompleteLat
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: 可居 余mpleteLat
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited CompleteLat :=
  ⟨of PUnit⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LargeCategory.{u} CompleteLat
  body: CompleteLatticeHom X Y
  id X := CompleteLatticeHom.id X
  comp f g := g.comp f

中文:
实例 :
  签名: 大范畴.{u} 余mpleteLat
  定义体: CompleteLatticeHom X Y
  id X := CompleteLatticeHom.id X
  comp f g := g.comp f

Depends on / 依赖: CompleteLatticeHom
-/
instance : LargeCategory.{u} CompleteLat where
  Hom X Y := CompleteLatticeHom X Y
  id X := CompleteLatticeHom.id X
  comp f g := g.comp f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory CompleteLat (CompleteLatticeHom · ·)
  body: f
  ofHom f := f

中文:
实例 :
  签名: 余ncrete范畴 余mpleteLat (完备格态射 · ·)
  定义体: f
  ofHom f := f
-/
instance : ConcreteCategory CompleteLat (CompleteLatticeHom · ·) where
  hom f := f
  ofHom f := f

/--
Instance `hasForgetToBddLat` / 实例 `hasForgetToBddLat`

English:
instance hasForgetToBddLat
  signature: : HasForget₂ CompleteLat BddLat where
  body: .of X
  forget₂.map f := BddLat.ofHom (CompleteLatticeHom.toBoundedLatticeHom f)

中文:
实例 hasForgetToBddLat
  签名: : 有Forget₂ 余mpleteLat 有界格 where
  定义体: .of X
  forget₂.map f := BddLat.ofHom (CompleteLatticeHom.toBoundedLatticeHom f)
-/
instance hasForgetToBddLat : HasForget₂ CompleteLat BddLat where
  forget₂.obj X := .of X
  forget₂.map f := BddLat.ofHom (CompleteLatticeHom.toBoundedLatticeHom f)

/-- Constructs an isomorphism of complete lattices from an order isomorphism between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : CompleteLat.{u}} (e : α ≃o β)
  body: ConcreteCategory.ofHom e
  inv := ConcreteCategory.ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

中文:
定义 同构.mk
  签名: {α β : 余mpleteLat.{u}} (e : α ≃o β)
  定义体: ConcreteCategory.ofHom e
  inv := ConcreteCategory.ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
-/
def Iso.mk {α β : CompleteLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := ConcreteCategory.ofHom e
  inv := ConcreteCategory.ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps map]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : CompleteLat ⥤ CompleteLat where
  body: of Xᵒᵈ
  map {_ _} := CompleteLatticeHom.dual

中文:
定义 dual
  签名: : 余mpleteLat ⥤ 余mpleteLat where
  定义体: of Xᵒᵈ
  map {_ _} := CompleteLatticeHom.dual
-/
def dual : CompleteLat ⥤ CompleteLat where
  obj X := of Xᵒᵈ
  map {_ _} := CompleteLatticeHom.dual

/-- The equivalence between `CompleteLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/--
Definition of `dualEquiv` / `dualEquiv` 的定义

English:
definition dualEquiv
  signature: : CompleteLat ≌ CompleteLat where
  body: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

中文:
定义 dualEquiv
  签名: : 余mpleteLat ≌ 余mpleteLat where
  定义体: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
-/
def dualEquiv : CompleteLat ≌ CompleteLat where
  functor := dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

end CompleteLat

/--
theorem `completeLat_dual_comp_forget_to_bddLat` / 定理 `completeLat_dual_comp_forget_to_bddLat`

English:
theorem completeLat_dual_comp_forget_to_bddLat
  proof: rfl

中文:
定理 completeLat_dual_comp_forget_to_bddLat
  证明: rfl
-/
theorem completeLat_dual_comp_forget_to_bddLat :
    CompleteLat.dual ⋙ forget₂ CompleteLat BddLat =
    forget₂ CompleteLat BddLat ⋙ BddLat.dual :=
  rfl
