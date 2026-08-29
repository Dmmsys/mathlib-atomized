/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.Frm
public import Mathlib.Topology.Category.CompHaus.Frm

/-!
# The category of locales

This file defines `Locale`, the category of locales. This is the opposite of the category of frames.
-/

@[expose] public section


universe u

open CategoryTheory Opposite Order TopologicalSpace


/--
Definition of `Locale` / `Locale` 的定义

English:
definition Locale
  body: Frmᵒᵖ deriving LargeCategory

中文:
定义 Locale
  定义体: Frmᵒᵖ deriving LargeCategory

Depends on / 依赖: LargeCategory, deriving
-/
def Locale :=
  Frmᵒᵖ deriving LargeCategory

namespace Locale

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort Locale Type*
  body: ⟨fun X => X.unop⟩

中文:
实例 :
  签名: CoeSort Locale 类型
  定义体: ⟨fun X => X.unop⟩

Depends on / 依赖: X.unop
-/
instance : CoeSort Locale Type* :=
  ⟨fun X => X.unop⟩

instance (X : Locale) : Frame X :=
  X.unop.str

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (α : Type*) [Frame α]
  body: op Frm.of α

@[simp]

中文:
定义 of
  签名: (α : 类型) [Frame α]
  定义体: op Frm.of α

@[simp]

Depends on / 依赖: Frm.of
-/
def of (α : Type*) [Frame α] : Locale :=
op Frm.of α

@[simp]
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (α : Type*) [Frame α]
  statement: ↥(of α) = α
  proof: rfl

中文:
定理 coe_of
  条件: (α : 类型) [Frame α]
  结论: ↥(of α) = α
  证明: rfl
-/
theorem coe_of (α : Type*) [Frame α] : ↥(of α) = α :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Locale
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: Inhabited Locale
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited Locale :=
  ⟨of PUnit⟩

end Locale

/-- The forgetful functor from `Top` to `Locale` which forgets that the space has "enough points".
-/
@[simps!]
/--
Definition of `topToLocale` / `topToLocale` 的定义

English:
definition topToLocale
  signature: : TopCat ⥤ Locale
  body: topCatOpToFrm.rightOp

中文:
定义 topToLocale
  签名: : TopCat ⥤ Locale
  定义体: topCatOpToFrm.rightOp

Depends on / 依赖: rightOp, topCatOpToFrm, topCatOpToFrm.rightOp
-/
def topToLocale : TopCat ⥤ Locale :=
  topCatOpToFrm.rightOp

-- Note, `CompHaus` is too strong. We only need `T0Space`.
/--
Instance `CompHausToLocale.faithful` / 实例 `CompHausToLocale.faithful`

English:
instance CompHausToLocale.faithful
  signature: : (compHausToTop ⋙ topToLocale.{u}).Faithful
  body: ⟨fun h => by
    dsimp at h
    exact ConcreteCategory.ext (Opens.comap_injective (congr_arg Frm.Hom.hom
      (Quiver.Hom.op_inj h)))⟩

中文:
实例 CompHausToLocale.faithful
  签名: : (compHausToTop ⋙ topToLocale.{u}).Faithful
  定义体: ⟨fun h => by
    dsimp at h
    exact ConcreteCategory.ext (Opens.comap_injective (congr_arg Frm.Hom.hom
      (Quiver.Hom.op_inj h)))⟩

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ext, Frm.Hom.hom, Opens.comap_injective, Quiver, Quiver.Hom.op_inj, comap_injective, congr_arg, op_inj
-/
instance CompHausToLocale.faithful : (compHausToTop ⋙ topToLocale.{u}).Faithful :=
  ⟨fun h => by
    dsimp at h
    exact ConcreteCategory.ext (Opens.comap_injective (congr_arg Frm.Hom.hom
      (Quiver.Hom.op_inj h)))⟩
