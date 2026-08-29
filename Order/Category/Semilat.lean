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

/--
Definition of `SemilatSupCat` / `SemilatSupCat` 的定义

English:
structure SemilatSupCat
  parameters: : Type (u + 1) where
  axioms and operations (4):
    - of : :
    - X : Type u
    - [isSemilatticeSup : SemilatticeSup X]
    - [isOrderBot : OrderBot.{u} X]

中文:
结构 SemilatSup范畴
  参数: : 类型 (u + 1) where
  公理与运算 (4 个):
    - of : :
    - X : 类型u
    - [isSemilatticeSup : SemilatticeSup X]
    - [isOrderBot : 有底序.{u} X]
-/
structure SemilatSupCat : Type (u + 1) where
  /-- Construct a bundled `SemilatSupCat` from a `SemilatticeSup`. -/
  of ::
  /-- The underlying type of a sup-semilattice with a bottom element. -/
  protected X : Type u
  [isSemilatticeSup : SemilatticeSup X]
  [isOrderBot : OrderBot.{u} X]

/--
Definition of `SemilatInfCat` / `SemilatInfCat` 的定义

English:
structure SemilatInfCat
  parameters: : Type (u + 1) where
  axioms and operations (4):
    - of : :
    - X : Type u
    - [isSemilatticeInf : SemilatticeInf X]
    - [isOrderTop : OrderTop.{u} X]

中文:
结构 SemilatInf范畴
  参数: : 类型 (u + 1) where
  公理与运算 (4 个):
    - of : :
    - X : 类型u
    - [isSemilatticeInf : SemilatticeInf X]
    - [isOrderTop : 有顶序.{u} X]
-/
structure SemilatInfCat : Type (u + 1) where
  /-- Construct a bundled `SemilatInfCat` from a `SemilatticeInf`. -/
  of ::
  /-- The underlying type of an inf-semilattice with a top element. -/
  protected X : Type u
  [isSemilatticeInf : SemilatticeInf X]
  [isOrderTop : OrderTop.{u} X]

namespace SemilatSupCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort SemilatSupCat Type*
  body: ⟨SemilatSupCat.X⟩

中文:
实例 :
  签名: CoeSort SemilatSup范畴 类型
  定义体: ⟨SemilatSupCat.X⟩

Depends on / 依赖: SemilatSupCat, SemilatSupCat.X
-/
instance : CoeSort SemilatSupCat Type* :=
  ⟨SemilatSupCat.X⟩

attribute [instance] isSemilatticeSup isOrderBot

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (α : Type*) [SemilatticeSup α] [OrderBot α]
  statement: ↥(of α) = α
  proof: rfl

中文:
定理 coe_of
  条件: (α : 类型) [SemilatticeSup α] [有底序 α]
  结论: ↥(of α) = α
  证明: rfl
-/
theorem coe_of (α : Type*) [SemilatticeSup α] [OrderBot α] : ↥(of α) = α :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited SemilatSupCat
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: 可居 SemilatSup范畴
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited SemilatSupCat :=
  ⟨of PUnit⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LargeCategory.{u} SemilatSupCat
  body: SupBotHom X Y
  id X := SupBotHom.id X
  comp f g := g.comp f
  id_comp := SupBotHom.comp_id
  comp_id := SupBotHom.id_comp
  assoc _ _ _ := SupBotHom.comp_assoc _ _ _

中文:
实例 :
  签名: 大范畴.{u} SemilatSup范畴
  定义体: SupBotHom X Y
  id X := SupBotHom.id X
  comp f g := g.comp f
  id_comp := SupBotHom.comp_id
  comp_id := SupBotHom.id_comp
  assoc _ _ _ := SupBotHom.comp_assoc _ _ _

Depends on / 依赖: SupBotHom
-/
instance : LargeCategory.{u} SemilatSupCat where
  Hom X Y := SupBotHom X Y
  id X := SupBotHom.id X
  comp f g := g.comp f
  id_comp := SupBotHom.comp_id
  comp_id := SupBotHom.id_comp
  assoc _ _ _ := SupBotHom.comp_assoc _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory SemilatSupCat (SupBotHom · ·)
  body: f
  ofHom f := f

中文:
实例 :
  签名: 余ncrete范畴 SemilatSup范畴 (SupBot态射 · ·)
  定义体: f
  ofHom f := f
-/
instance : ConcreteCategory SemilatSupCat (SupBotHom · ·) where
  hom f := f
  ofHom f := f

/--
Instance `hasForgetToPartOrd` / 实例 `hasForgetToPartOrd`

English:
instance hasForgetToPartOrd
  signature: : HasForget₂ SemilatSupCat PartOrd where
  body: .of X
  forget₂.map f := PartOrd.ofHom ⟨f.toSupHom, OrderHomClass.mono f.toSupHom⟩

@[simp]

中文:
实例 hasForgetToPartOrd
  签名: : 有Forget₂ SemilatSup范畴 偏序 where
  定义体: .of X
  forget₂.map f := PartOrd.ofHom ⟨f.toSupHom, OrderHomClass.mono f.toSupHom⟩

@[simp]
-/
instance hasForgetToPartOrd : HasForget₂ SemilatSupCat PartOrd where
  forget₂.obj X := .of X
  forget₂.map f := PartOrd.ofHom ⟨f.toSupHom, OrderHomClass.mono f.toSupHom⟩

@[simp]
/--
theorem `coe_forget_to_partOrd` / 定理 `coe_forget_to_partOrd`

English:
theorem coe_forget_to_partOrd
  given: (X : SemilatSupCat)
  proof: rfl

中文:
定理 coe_forget_to_partOrd
  条件: (X : SemilatSup范畴)
  证明: rfl
-/
theorem coe_forget_to_partOrd (X : SemilatSupCat) :
    ↥((forget₂ SemilatSupCat PartOrd).obj X) = ↥X :=
  rfl

end SemilatSupCat

namespace SemilatInfCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort SemilatInfCat Type*
  body: ⟨SemilatInfCat.X⟩

中文:
实例 :
  签名: CoeSort SemilatInf范畴 类型
  定义体: ⟨SemilatInfCat.X⟩

Depends on / 依赖: SemilatInfCat, SemilatInfCat.X
-/
instance : CoeSort SemilatInfCat Type* :=
  ⟨SemilatInfCat.X⟩

attribute [instance] isSemilatticeInf isOrderTop

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (α : Type*) [SemilatticeInf α] [OrderTop α]
  statement: ↥(of α) = α
  proof: rfl

中文:
定理 coe_of
  条件: (α : 类型) [SemilatticeInf α] [有顶序 α]
  结论: ↥(of α) = α
  证明: rfl
-/
theorem coe_of (α : Type*) [SemilatticeInf α] [OrderTop α] : ↥(of α) = α :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited SemilatInfCat
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: 可居 SemilatInf范畴
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited SemilatInfCat :=
  ⟨of PUnit⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LargeCategory.{u} SemilatInfCat
  body: InfTopHom X Y
  id X := InfTopHom.id X
  comp f g := g.comp f
  id_comp := InfTopHom.comp_id
  comp_id := InfTopHom.id_comp
  assoc _ _ _ := InfTopHom.comp_assoc _ _ _

中文:
实例 :
  签名: 大范畴.{u} SemilatInf范畴
  定义体: InfTopHom X Y
  id X := InfTopHom.id X
  comp f g := g.comp f
  id_comp := InfTopHom.comp_id
  comp_id := InfTopHom.id_comp
  assoc _ _ _ := InfTopHom.comp_assoc _ _ _

Depends on / 依赖: InfTopHom
-/
instance : LargeCategory.{u} SemilatInfCat where
  Hom X Y := InfTopHom X Y
  id X := InfTopHom.id X
  comp f g := g.comp f
  id_comp := InfTopHom.comp_id
  comp_id := InfTopHom.id_comp
  assoc _ _ _ := InfTopHom.comp_assoc _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory SemilatInfCat (InfTopHom · ·)
  body: f
  ofHom f := f

中文:
实例 :
  签名: 余ncrete范畴 SemilatInf范畴 (InfTop态射 · ·)
  定义体: f
  ofHom f := f
-/
instance : ConcreteCategory SemilatInfCat (InfTopHom · ·) where
  hom f := f
  ofHom f := f

/--
Instance `hasForgetToPartOrd` / 实例 `hasForgetToPartOrd`

English:
instance hasForgetToPartOrd
  signature: : HasForget₂ SemilatInfCat PartOrd where
  body: .of X
  forget₂.map f := PartOrd.ofHom ⟨f.toInfHom, OrderHomClass.mono f.toInfHom⟩

@[simp]

中文:
实例 hasForgetToPartOrd
  签名: : 有Forget₂ SemilatInf范畴 偏序 where
  定义体: .of X
  forget₂.map f := PartOrd.ofHom ⟨f.toInfHom, OrderHomClass.mono f.toInfHom⟩

@[simp]
-/
instance hasForgetToPartOrd : HasForget₂ SemilatInfCat PartOrd where
  forget₂.obj X := .of X
  forget₂.map f := PartOrd.ofHom ⟨f.toInfHom, OrderHomClass.mono f.toInfHom⟩

@[simp]
/--
theorem `coe_forget_to_partOrd` / 定理 `coe_forget_to_partOrd`

English:
theorem coe_forget_to_partOrd
  given: (X : SemilatInfCat)
  proof: rfl

中文:
定理 coe_forget_to_partOrd
  条件: (X : SemilatInf范畴)
  证明: rfl
-/
theorem coe_forget_to_partOrd (X : SemilatInfCat) :
    ↥((forget₂ SemilatInfCat PartOrd).obj X) = ↥X :=
  rfl

end SemilatInfCat

/-! ### Order dual -/

namespace SemilatSupCat

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : SemilatSupCat.{u}} (e : α ≃o β)
  body: (e : SupBotHom _ _)
  inv := (e.symm : SupBotHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

中文:
定义 同构.mk
  签名: {α β : SemilatSup范畴.{u}} (e : α ≃o β)
  定义体: (e : SupBotHom _ _)
  inv := (e.symm : SupBotHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
-/
def Iso.mk {α β : SemilatSupCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : SupBotHom _ _)
  inv := (e.symm : SupBotHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps map]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : SemilatSupCat ⥤ SemilatInfCat where
  body: .of Xᵒᵈ
  map {_ _} := SupBotHom.dual

中文:
定义 dual
  签名: : SemilatSup范畴 ⥤ SemilatInf范畴 where
  定义体: .of Xᵒᵈ
  map {_ _} := SupBotHom.dual
-/
def dual : SemilatSupCat ⥤ SemilatInfCat where
  obj X := .of Xᵒᵈ
  map {_ _} := SupBotHom.dual

end SemilatSupCat

namespace SemilatInfCat

/-- Constructs an isomorphism of lattices from an order isomorphism between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : SemilatInfCat.{u}} (e : α ≃o β)
  body: (e : InfTopHom _ _)
  inv := (e.symm : InfTopHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

中文:
定义 同构.mk
  签名: {α β : SemilatInf范畴.{u}} (e : α ≃o β)
  定义体: (e : InfTopHom _ _)
  inv := (e.symm : InfTopHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
-/
def Iso.mk {α β : SemilatInfCat.{u}} (e : α ≃o β) : α ≅ β where
  hom := (e : InfTopHom _ _)
  inv := (e.symm : InfTopHom _ _)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : SemilatInfCat ⥤ SemilatSupCat where
  body: .of Xᵒᵈ
  map {_ _} := InfTopHom.dual

中文:
定义 dual
  签名: : SemilatInf范畴 ⥤ SemilatSup范畴 where
  定义体: .of Xᵒᵈ
  map {_ _} := InfTopHom.dual
-/
def dual : SemilatInfCat ⥤ SemilatSupCat where
  obj X := .of Xᵒᵈ
  map {_ _} := InfTopHom.dual

end SemilatInfCat

/-- The equivalence between `SemilatSupCat` and `SemilatInfCat` induced by `OrderDual` both ways. -/
@[simps functor inverse]
/--
Definition of `SemilatSupCatEquivSemilatInfCat` / `SemilatSupCatEquivSemilatInfCat` 的定义

English:
definition SemilatSupCatEquivSemilatInfCat
  signature: : SemilatSupCat ≌ SemilatInfCat where
  body: SemilatSupCat.dual
  inverse := SemilatInfCat.dual
unitIso := NatIso.ofComponents fun X => SemilatSupCat.Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => SemilatInfCat.Iso.mk OrderIso.dualDual X

中文:
定义 SemilatSupCatEquivSemilatInfCat
  签名: : SemilatSup范畴 ≌ SemilatInf范畴 where
  定义体: SemilatSupCat.dual
  inverse := SemilatInfCat.dual
unitIso := NatIso.ofComponents fun X => SemilatSupCat.Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => SemilatInfCat.Iso.mk OrderIso.dualDual X

Depends on / 依赖: SemilatSupCat, SemilatSupCat.dual
-/
def SemilatSupCatEquivSemilatInfCat : SemilatSupCat ≌ SemilatInfCat where
  functor := SemilatSupCat.dual
  inverse := SemilatInfCat.dual
unitIso := NatIso.ofComponents fun X => SemilatSupCat.Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => SemilatInfCat.Iso.mk OrderIso.dualDual X

/--
theorem `SemilatSupCat_dual_comp_forget_to_partOrd` / 定理 `SemilatSupCat_dual_comp_forget_to_partOrd`

English:
theorem SemilatSupCat_dual_comp_forget_to_partOrd
  proof: rfl

中文:
定理 SemilatSupCat_dual_comp_forget_to_partOrd
  证明: rfl
-/
theorem SemilatSupCat_dual_comp_forget_to_partOrd :
    SemilatSupCat.dual ⋙ forget₂ SemilatInfCat PartOrd =
      forget₂ SemilatSupCat PartOrd ⋙ PartOrd.dual :=
  rfl

/--
theorem `SemilatInfCat_dual_comp_forget_to_partOrd` / 定理 `SemilatInfCat_dual_comp_forget_to_partOrd`

English:
theorem SemilatInfCat_dual_comp_forget_to_partOrd
  proof: rfl

中文:
定理 SemilatInfCat_dual_comp_forget_to_partOrd
  证明: rfl
-/
theorem SemilatInfCat_dual_comp_forget_to_partOrd :
    SemilatInfCat.dual ⋙ forget₂ SemilatSupCat PartOrd =
      forget₂ SemilatInfCat PartOrd ⋙ PartOrd.dual :=
  rfl
