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

/-- The category of complete lattices. -/
/-
**CompleteLat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of complete lattices.
-/
structure CompleteLat where
  /-- Construct a bundled `CompleteLat` from the underlying type and typeclass. -/
  of ::
  /-- The underlying lattice. -/
  (carrier : Type*)
  [str : CompleteLattice carrier]

attribute [instance] CompleteLat.str

initialize_simps_projections CompleteLat (carrier → coe, -str)

namespace CompleteLat

/-
**CompleteLat.** 是 Mathlib 中的一个实例，位于命名空间 `CompleteLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort CompleteLat (Type _) :=
  ⟨CompleteLat.carrier⟩

attribute [coe] CompleteLat.carrier
/-
**CompleteLat.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `CompleteLat`。
形式化陈述：coe_of (α : Type*) [CompleteLattice α] : ↥(of α) = α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (α : Type*) [CompleteLattice α] : ↥(of α) = α :=
  rfl
/-
**CompleteLat.** 是 Mathlib 中的一个实例，位于命名空间 `CompleteLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited CompleteLat :=
  ⟨of PUnit⟩
/-
**CompleteLat.** 是 Mathlib 中的一个实例，位于命名空间 `CompleteLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LargeCategory.{u} CompleteLat where
  Hom X Y := CompleteLatticeHom X Y
  id X := CompleteLatticeHom.id X
  comp f g := g.comp f
/-
**CompleteLat.** 是 Mathlib 中的一个实例，位于命名空间 `CompleteLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory CompleteLat (CompleteLatticeHom · ·) where
  hom f := f
  ofHom f := f
/-
**CompleteLat.hasForgetToBddLat** 是 Mathlib 中的一个实例，位于命名空间 `CompleteLat`。
形式化陈述：hasForgetToBddLat : HasForget₂ CompleteLat BddLat where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToBddLat : HasForget₂ CompleteLat BddLat where
  forget₂.obj X := .of X
  forget₂.map f := BddLat.ofHom (CompleteLatticeHom.toBoundedLatticeHom f)

/-- Constructs an isomorphism of complete lattices from an order isomorphism between them. -/
@[simps]
/-
**CompleteLat.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `CompleteLat.Iso`。
形式化陈述：{α β : CompleteLat} → ↑α ≃o ↑β → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an isomorphism of complete lattices from an order isomorphism between
 them.
-/
def Iso.mk {α β : CompleteLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := ConcreteCategory.ofHom e
  inv := ConcreteCategory.ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps map]
/-
**CompleteLat.dual** 是 Mathlib 中的一个定义，位于命名空间 `CompleteLat`。
形式化陈述：dual : CompleteLat ⥤ CompleteLat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` as a functor.
-/
def dual : CompleteLat ⥤ CompleteLat where
  obj X := of Xᵒᵈ
  map {_ _} := CompleteLatticeHom.dual

/-- The equivalence between `CompleteLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/-
**CompleteLat.dualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CompleteLat`。
形式化陈述：dualEquiv : CompleteLat ≌ CompleteLat where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `CompleteLat` and itself induced by `OrderDual` both way
s.
-/
def dualEquiv : CompleteLat ≌ CompleteLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end CompleteLat

/-
**completeLat_dual_comp_forget_to_bddLat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：completeLat_dual_comp_forget_to_bddLat : CompleteLat.dual ⋙ forget₂ Comple
teLat BddLat = forget₂ CompleteLat BddLat ⋙ BddLat.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem completeLat_dual_comp_forget_to_bddLat :
    CompleteLat.dual ⋙ forget₂ CompleteLat BddLat =
    forget₂ CompleteLat BddLat ⋙ BddLat.dual :=
  rfl
