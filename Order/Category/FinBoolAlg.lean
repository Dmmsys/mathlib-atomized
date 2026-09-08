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

/-- The category of finite Boolean algebras with bounded lattice morphisms. -/
/-
**FinBoolAlg** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of finite Boolean algebras with bounded lattice morphisms.
-/
structure FinBoolAlg extends BoolAlg where
  [isFintype : Fintype toBoolAlg]

attribute [instance] FinBoolAlg.isFintype

namespace FinBoolAlg

/-
**FinBoolAlg.** 是 Mathlib 中的一个实例，位于命名空间 `FinBoolAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort FinBoolAlg Type* :=
  ⟨fun X => X.carrier⟩

/-- Construct a bundled `FinBoolAlg` from `BooleanAlgebra` + `Fintype`. -/
/-
**FinBoolAlg.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `FinBoolAlg`。
形式化陈述：of (α : Type*) [BooleanAlgebra α] [Fintype α] : FinBoolAlg where carrier
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `FinBoolAlg` from `BooleanAlgebra` + `Fintype`.
-/
abbrev of (α : Type*) [BooleanAlgebra α] [Fintype α] : FinBoolAlg where
  carrier := α
/-
**FinBoolAlg.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `FinBoolAlg`。
形式化陈述：coe_of (α : Type*) [BooleanAlgebra α] [Fintype α] : ↥(of α) = α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (α : Type*) [BooleanAlgebra α] [Fintype α] : ↥(of α) = α :=
  rfl
/-
**FinBoolAlg.** 是 Mathlib 中的一个实例，位于命名空间 `FinBoolAlg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited FinBoolAlg :=
  ⟨of PUnit⟩
/-
**FinBoolAlg.largeCategory** 是 Mathlib 中的一个实例，位于命名空间 `FinBoolAlg`。
形式化陈述：largeCategory : LargeCategory FinBoolAlg
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance largeCategory : LargeCategory FinBoolAlg :=
  inferInstanceAs <| Category (InducedCategory _ toBoolAlg)
/-
**FinBoolAlg.concreteCategory** 是 Mathlib 中的一个实例，位于命名空间 `FinBoolAlg`。
形式化陈述：concreteCategory : ConcreteCategory FinBoolAlg (BoundedLatticeHom · ·)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance concreteCategory : ConcreteCategory FinBoolAlg (BoundedLatticeHom · ·) :=
  inferInstanceAs <| ConcreteCategory (InducedCategory _ toBoolAlg) _
/-
**FinBoolAlg.hasForgetToBoolAlg** 是 Mathlib 中的一个实例，位于命名空间 `FinBoolAlg`。
形式化陈述：hasForgetToBoolAlg : HasForget₂ FinBoolAlg BoolAlg
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToBoolAlg : HasForget₂ FinBoolAlg BoolAlg :=
  inferInstanceAs <| HasForget₂ (InducedCategory _ toBoolAlg) _
/-
**FinBoolAlg.hasForgetToFinBddDistLat** 是 Mathlib 中的一个实例，位于命名空间 `FinBoolAlg`。
形式化陈述：hasForgetToFinBddDistLat : HasForget₂ FinBoolAlg FinBddDistLat where forge
t₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToFinBddDistLat : HasForget₂ FinBoolAlg FinBddDistLat where
  forget₂.obj X := .of X
  forget₂.map f := FinBddDistLat.ofHom f.hom.hom
/-
**FinBoolAlg.forgetToBoolAlg_full** 是 Mathlib 中的一个实例，位于命名空间 `FinBoolAlg`。
形式化陈述：forgetToBoolAlg_full : (forget₂ FinBoolAlg BoolAlg).Full
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.InducedCategory.full`：∀ {C : Type u₁} {D : Type u₂} [inst
 : CategoryTheory.Category.{v, u₂} D] (F : C → D),   (CategoryTheory.inducedFunc
tor F).Full
-/
instance forgetToBoolAlg_full : (forget₂ FinBoolAlg BoolAlg).Full :=
  InducedCategory.full _
/-
**FinBoolAlg.forgetToBoolAlgFaithful** 是 Mathlib 中的一个实例，位于命名空间 `FinBoolAlg`。
形式化陈述：forgetToBoolAlgFaithful : (forget₂ FinBoolAlg BoolAlg).Faithful
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.InducedCategory.faithful`：∀ {C : Type u₁} {D : Type u₂} [
inst : CategoryTheory.Category.{v, u₂} D] (F : C → D),   (CategoryTheory.induced
Functor F).Faithful
-/
instance forgetToBoolAlgFaithful : (forget₂ FinBoolAlg BoolAlg).Faithful :=
  InducedCategory.faithful _

@[simps]
/-
**FinBoolAlg.hasForgetToFinPartOrd** 是 Mathlib 中的一个实例，位于命名空间 `FinBoolAlg`。
形式化陈述：hasForgetToFinPartOrd : HasForget₂ FinBoolAlg FinPartOrd where forget₂.obj
 X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToFinPartOrd : HasForget₂ FinBoolAlg FinPartOrd where
  forget₂.obj X := .of X
  forget₂.map {X Y} f := InducedCategory.homMk (PartOrd.ofHom f.hom.hom)
/-
**FinBoolAlg.forgetToFinPartOrdFaithful** 是 Mathlib 中的一个实例，位于命名空间 `FinBoolAlg`。
形式化陈述：forgetToFinPartOrdFaithful : (forget₂ FinBoolAlg FinPartOrd).Faithful wher
e map_injective h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `BoundedLatticeHom.ext`：ext {f g : BoundedLatticeHom α β} (h : forall a, 
f a = g a) : f = g
· 使用定理 `CategoryTheory.congr_fun`：∀ {C : Type u_1} [inst : CategoryTheory.Catego
ry.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C → Type w
)} [inst_1 : o…
-/
instance forgetToFinPartOrdFaithful : (forget₂ FinBoolAlg FinPartOrd).Faithful where
  map_injective h := by
    ext x
    exact CategoryTheory.congr_fun h x

/-- Constructs an equivalence between finite Boolean algebras from an order isomorphism between
them. -/
@[simps]
/-
**FinBoolAlg.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `FinBoolAlg.Iso`。
形式化陈述：{α β : FinBoolAlg} → ↑α.toBoolAlg ≃o ↑β.toBoolAlg → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an equivalence between finite Boolean algebras from an order isomorph
ism between
them.
-/
def Iso.mk {α β : FinBoolAlg.{u}} (e : α ≃o β) : α ≅ β where
  hom := InducedCategory.homMk (BoolAlg.ofHom e)
  inv := InducedCategory.homMk (BoolAlg.ofHom e.symm)
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps map]
/-
**FinBoolAlg.dual** 是 Mathlib 中的一个定义，位于命名空间 `FinBoolAlg`。
形式化陈述：dual : FinBoolAlg ⥤ FinBoolAlg where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` as a functor.
-/
def dual : FinBoolAlg ⥤ FinBoolAlg where
  obj X := of Xᵒᵈ
  map f := InducedCategory.homMk (BoolAlg.ofHom f.hom.hom.dual)

/-- The equivalence between `FinBoolAlg` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/-
**FinBoolAlg.dualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FinBoolAlg`。
形式化陈述：dualEquiv : FinBoolAlg ≌ FinBoolAlg where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `FinBoolAlg` and itself induced by `OrderDual` both ways
.
-/
def dualEquiv : FinBoolAlg ≌ FinBoolAlg where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end FinBoolAlg

/-
**finBoolAlg_dual_comp_forget_to_finBddDistLat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finBoolAlg_dual_comp_forget_to_finBddDistLat : FinBoolAlg.dual ⋙ forget₂ F
inBoolAlg FinBddDistLat = forget₂ FinBoolAlg FinBddDistLat ⋙ FinBddDistLat.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finBoolAlg_dual_comp_forget_to_finBddDistLat :
    FinBoolAlg.dual ⋙ forget₂ FinBoolAlg FinBddDistLat =
      forget₂ FinBoolAlg FinBddDistLat ⋙ FinBddDistLat.dual :=
  rfl

attribute [local instance] FintypeCat.fintype in
/-- The powerset functor. `Set` as a functor. -/
@[simps]
/-
**fintypeToFinBoolAlgOp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fintypeToFinBoolAlgOp : FintypeCat ⥤ FinBoolAlgᵒᵖ where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The powerset functor. `Set` as a functor.
-/
noncomputable def fintypeToFinBoolAlgOp : FintypeCat ⥤ FinBoolAlgᵒᵖ where
  obj X := op <| .of (Set X)
  map {X Y} f :=
    Quiver.Hom.op <| InducedCategory.homMk <|
      BoolAlg.ofHom <| CompleteLatticeHom.setPreimage f
