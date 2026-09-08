/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.PartOrd
public import Mathlib.Order.Hom.BoundedLattice

/-!
# The categories of semilattices

This defines `SemilatSupCat` and `SemilatInfCat`, the categories of sup-semilattices with a bottom
element and inf-semilattices with a top element.

## References

* [nLab, *semilattice*](https://ncatlab.org/nlab/show/semilattice)
-/

@[expose] public section


universe u

open CategoryTheory

/-- The category of sup-semilattices with a bottom element. -/
/-
**SemilatSupCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of sup-semilattices with a bottom element.
-/
structure SemilatSupCat : Type (u + 1) where
  /-- Construct a bundled `SemilatSupCat` from a `SemilatticeSup`. -/
  of ::
  /-- The underlying type of a sup-semilattice with a bottom element. -/
  protected X : Type u
  [isSemilatticeSup : SemilatticeSup X]
  [isOrderBot : OrderBot.{u} X]

/-- The category of inf-semilattices with a top element. -/
/-
**SemilatInfCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of inf-semilattices with a top element.
-/
structure SemilatInfCat : Type (u + 1) where
  /-- Construct a bundled `SemilatInfCat` from a `SemilatticeInf`. -/
  of ::
  /-- The underlying type of an inf-semilattice with a top element. -/
  protected X : Type u
  [isSemilatticeInf : SemilatticeInf X]
  [isOrderTop : OrderTop.{u} X]

namespace SemilatSupCat

/-
**SemilatSupCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemilatSupCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort SemilatSupCat Type* :=
  ⟨SemilatSupCat.X⟩

attribute [instance] isSemilatticeSup isOrderBot
/-
**SemilatSupCat.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `SemilatSupCat`。
形式化陈述：coe_of (α : Type*) [SemilatticeSup α] [OrderBot α] : ↥(of α) = α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (α : Type*) [SemilatticeSup α] [OrderBot α] : ↥(of α) = α :=
  rfl
/-
**SemilatSupCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemilatSupCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited SemilatSupCat :=
  ⟨of PUnit⟩
/-
**SemilatSupCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemilatSupCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LargeCategory.{u} SemilatSupCat where
  Hom X Y := SupBotHom X Y
  id X := SupBotHom.id X
  comp f g := g.comp f
  id_comp := SupBotHom.comp_id
  comp_id := SupBotHom.id_comp
  assoc _ _ _ := SupBotHom.comp_assoc _ _ _
/-
**SemilatSupCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemilatSupCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory SemilatSupCat (SupBotHom · ·) where
  hom f := f
  ofHom f := f
/-
**SemilatSupCat.hasForgetToPartOrd** 是 Mathlib 中的一个实例，位于命名空间 `SemilatSupCat`。
形式化陈述：hasForgetToPartOrd : HasForget₂ SemilatSupCat PartOrd where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToPartOrd : HasForget₂ SemilatSupCat PartOrd where
  forget₂.obj X := .of X
  forget₂.map f := PartOrd.ofHom ⟨f.toSupHom, OrderHomClass.mono f.toSupHom⟩

@[simp]
/-
**SemilatSupCat.coe_forget_to_partOrd** 是 Mathlib 中的一个定理，位于命名空间 `SemilatSupCat`。
形式化陈述：coe_forget_to_partOrd (X : SemilatSupCat) : ↥((forget₂ SemilatSupCat PartO
rd).obj X) = ↥X
参数：X : SemilatSupCat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_forget_to_partOrd (X : SemilatSupCat) :
    ↥((forget₂ SemilatSupCat PartOrd).obj X) = ↥X :=
  rfl

end SemilatSupCat

namespace SemilatInfCat

/-
**SemilatInfCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemilatInfCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort SemilatInfCat Type* :=
  ⟨SemilatInfCat.X⟩

attribute [instance] isSemilatticeInf isOrderTop
/-
**SemilatInfCat.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `SemilatInfCat`。
形式化陈述：coe_of (α : Type*) [SemilatticeInf α] [OrderTop α] : ↥(of α) = α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (α : Type*) [SemilatticeInf α] [OrderTop α] : ↥(of α) = α :=
  rfl
/-
**SemilatInfCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemilatInfCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited SemilatInfCat :=
  ⟨of PUnit⟩
/-
**SemilatInfCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemilatInfCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LargeCategory.{u} SemilatInfCat where
  Hom X Y := InfTopHom X Y
  id X := InfTopHom.id X
  comp f g := g.comp f
  id_comp := InfTopHom.comp_id
  comp_id := InfTopHom.id_comp
  assoc _ _ _ := InfTopHom.comp_assoc _ _ _
/-
**SemilatInfCat.** 是 Mathlib 中的一个实例，位于命名空间 `SemilatInfCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory SemilatInfCat (InfTopHom · ·) where
  hom f := f
  ofHom f := f
/-
**SemilatInfCat.hasForgetToPartOrd** 是 Mathlib 中的一个实例，位于命名空间 `SemilatInfCat`。
形式化陈述：hasForgetToPartOrd : HasForget₂ SemilatInfCat PartOrd where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToPartOrd : HasForget₂ SemilatInfCat PartOrd where
  forget₂.obj X := .of X
  forget₂.map f := PartOrd.ofHom ⟨f.toInfHom, OrderHomClass.mono f.toInfHom⟩

@[simp]
/-
**SemilatInfCat.coe_forget_to_partOrd** 是 Mathlib 中的一个定理，位于命名空间 `SemilatInfCat`。
形式化陈述：coe_forget_to_partOrd (X : SemilatInfCat) : ↥((forget₂ SemilatInfCat PartO
rd).obj X) = ↥X
参数：X : SemilatInfCat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_forget_to_partOrd (X : SemilatInfCat) :
    ↥((forget₂ SemilatInfCat PartOrd).obj X) = ↥X :=
  rfl

end SemilatInfCat

/-! ### Order dual -/

namespace SemilatSupCat

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
/-
**SemilatSupCat.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `SemilatSupCat.Iso`。
形式化陈述：{α β : SemilatSupCat} → α.X ≃o β.X → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an isomorphism of lattices from an order isomorphism between them.
-/
def Iso.mk {α β : SemilatSupCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : SupBotHom _ _)
  inv := (e.symm : SupBotHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps map]
/-
**SemilatSupCat.dual** 是 Mathlib 中的一个定义，位于命名空间 `SemilatSupCat`。
形式化陈述：dual : SemilatSupCat ⥤ SemilatInfCat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` as a functor.
-/
def dual : SemilatSupCat ⥤ SemilatInfCat where
  obj X := .of Xᵒᵈ
  map {_ _} := SupBotHom.dual

end SemilatSupCat

namespace SemilatInfCat

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
/-
**SemilatInfCat.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `SemilatInfCat.Iso`。
形式化陈述：{α β : SemilatInfCat} → α.X ≃o β.X → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an isomorphism of lattices from an order isomorphism between them.
-/
def Iso.mk {α β : SemilatInfCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : InfTopHom _ _)
  inv := (e.symm : InfTopHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps]
/-
**SemilatInfCat.dual** 是 Mathlib 中的一个定义，位于命名空间 `SemilatInfCat`。
形式化陈述：dual : SemilatInfCat ⥤ SemilatSupCat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` as a functor.
-/
def dual : SemilatInfCat ⥤ SemilatSupCat where
  obj X := .of Xᵒᵈ
  map {_ _} := InfTopHom.dual

end SemilatInfCat

/-- The equivalence between `SemilatSupCat` and `SemilatInfCat` induced by `OrderDual` both ways. -/
@[simps functor inverse]
/-
**SemilatSupCatEquivSemilatInfCat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SemilatSupCatEquivSemilatInfCat : SemilatSupCat ≌ SemilatInfCat where func
tor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `SemilatSupCat` and `SemilatInfCat` induced by `OrderDua
l` both ways.
-/
def SemilatSupCatEquivSemilatInfCat : SemilatSupCat ≌ SemilatInfCat where
  functor := SemilatSupCat.dual
  inverse := SemilatInfCat.dual
  unitIso := NatIso.ofComponents fun X => SemilatSupCat.Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => SemilatInfCat.Iso.mk <| OrderIso.dualDual X
/-
**SemilatSupCat_dual_comp_forget_to_partOrd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemilatSupCat_dual_comp_forget_to_partOrd : SemilatSupCat.dual ⋙ forget₂ S
emilatInfCat PartOrd = forget₂ SemilatSupCat PartOrd ⋙ PartOrd.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SemilatSupCat_dual_comp_forget_to_partOrd :
    SemilatSupCat.dual ⋙ forget₂ SemilatInfCat PartOrd =
      forget₂ SemilatSupCat PartOrd ⋙ PartOrd.dual :=
  rfl
/-
**SemilatInfCat_dual_comp_forget_to_partOrd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemilatInfCat_dual_comp_forget_to_partOrd : SemilatInfCat.dual ⋙ forget₂ S
emilatSupCat PartOrd = forget₂ SemilatInfCat PartOrd ⋙ PartOrd.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SemilatInfCat_dual_comp_forget_to_partOrd :
    SemilatInfCat.dual ⋙ forget₂ SemilatSupCat PartOrd =
      forget₂ SemilatInfCat PartOrd ⋙ PartOrd.dual :=
  rfl
