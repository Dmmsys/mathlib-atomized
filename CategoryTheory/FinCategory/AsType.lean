/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.Data.Fintype.EquivFin

/-!
# Finite categories are equivalent to categories in `Type 0`.
-/

@[expose] public section

universe w v u

noncomputable section

namespace CategoryTheory

namespace FinCategory

variable (α : Type*) [Fintype α] [SmallCategory α] [FinCategory α]

--@[nolint unused_arguments]
/--
Definition of `ObjAsType` / `ObjAsType` 的定义

English:
abbreviation ObjAsType
  signature: : Type
  body: InducedCategory α (Fintype.equivFin α).symm

中文:
缩写 ObjAsType
  签名: : 类型
  定义体: InducedCategory α (Fintype.equivFin α).symm

Depends on / 依赖: Fintype, Fintype.equivFin, InducedCategory, equivFin
-/
abbrev ObjAsType : Type :=
  InducedCategory α (Fintype.equivFin α).symm

instance {i j : ObjAsType α} : Fintype (i ⟶ j) :=
  Fintype.ofEquiv _ InducedCategory.homEquiv.symm

/--
Definition of `objAsTypeEquiv` / `objAsTypeEquiv` 的定义

English:
definition objAsTypeEquiv
  signature: : ObjAsType α ≌ α
  body: (inducedFunctor (Fintype.equivFin α).symm).asEquivalence

中文:
定义 objAsTypeEquiv
  签名: : ObjAsType α ≌ α
  定义体: (inducedFunctor (Fintype.equivFin α).symm).asEquivalence

Depends on / 依赖: Fintype, Fintype.equivFin, asEquivalence, equivFin, inducedFunctor
-/
noncomputable def objAsTypeEquiv : ObjAsType α ≌ α :=
  (inducedFunctor (Fintype.equivFin α).symm).asEquivalence

--@[nolint unused_arguments]
/--
Definition of `AsType` / `AsType` 的定义

English:
abbreviation AsType
  signature: : Type
  body: Fin (Fintype.card α)

中文:
缩写 AsType
  签名: : 类型
  定义体: Fin (Fintype.card α)

Depends on / 依赖: Fintype, Fintype.card
-/
abbrev AsType : Type :=
  Fin (Fintype.card α)

set_option backward.isDefEq.respectTransparency.types false in
@[simps -isSimp id comp]
/--
Instance `categoryAsType` / 实例 `categoryAsType`

English:
instance categoryAsType
  signature: : SmallCategory (AsType α) where
  body: Fin (Fintype.card (@Quiver.Hom (ObjAsType α) _ i j))
  id _ := Fintype.equivFin _ (𝟙 _)
  comp f g := Fintype.equivFin _ ((Fintype.equivFin _).symm f ≫ (Fintype.equivFin _).symm g)

中文:
实例 categoryAsType
  签名: : 小范畴 (AsType α) where
  定义体: Fin (Fintype.card (@Quiver.Hom (ObjAsType α) _ i j))
  id _ := Fintype.equivFin _ (𝟙 _)
  comp f g := Fintype.equivFin _ ((Fintype.equivFin _).symm f ≫ (Fintype.equivFin _).symm g)

Depends on / 依赖: Fintype, Fintype.card, ObjAsType, Quiver, Quiver.Hom
-/
noncomputable instance categoryAsType : SmallCategory (AsType α) where
  Hom i j := Fin (Fintype.card (@Quiver.Hom (ObjAsType α) _ i j))
  id _ := Fintype.equivFin _ (𝟙 _)
  comp f g := Fintype.equivFin _ ((Fintype.equivFin _).symm f ≫ (Fintype.equivFin _).symm g)

attribute [local simp] categoryAsType_id categoryAsType_comp

set_option backward.isDefEq.respectTransparency.types false in
/-- The "identity" functor from `AsType α` to `ObjAsType α`. -/
@[simps]
/--
Definition of `asTypeToObjAsType` / `asTypeToObjAsType` 的定义

English:
definition asTypeToObjAsType
  signature: : AsType α ⥤ ObjAsType α where
  body: id
  map {_ _} := (Fintype.equivFin _).symm

中文:
定义 asTypeToObjAsType
  签名: : AsType α ⥤ ObjAsType α where
  定义体: id
  map {_ _} := (Fintype.equivFin _).symm
-/
noncomputable def asTypeToObjAsType : AsType α ⥤ ObjAsType α where
  obj := id
  map {_ _} := (Fintype.equivFin _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The "identity" functor from `ObjAsType α` to `AsType α`. -/
@[simps]
/--
Definition of `objAsTypeToAsType` / `objAsTypeToAsType` 的定义

English:
definition objAsTypeToAsType
  signature: : ObjAsType α ⥤ AsType α where
  body: id
  map {_ _} := Fintype.equivFin _

中文:
定义 objAsTypeToAsType
  签名: : ObjAsType α ⥤ AsType α where
  定义体: id
  map {_ _} := Fintype.equivFin _
-/
noncomputable def objAsTypeToAsType : ObjAsType α ⥤ AsType α where
  obj := id
  map {_ _} := Fintype.equivFin _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `asTypeEquivObjAsType` / `asTypeEquivObjAsType` 的定义

English:
definition asTypeEquivObjAsType
  signature: : AsType α ≌ ObjAsType α where
  body: asTypeToObjAsType α
  inverse := objAsTypeToAsType α
  unitIso := NatIso.ofComponents Iso.refl
  counitIso := NatIso.ofComponents Iso.refl

中文:
定义 asTypeEquivObjAsType
  签名: : AsType α ≌ ObjAsType α where
  定义体: asTypeToObjAsType α
  inverse := objAsTypeToAsType α
  unitIso := NatIso.ofComponents Iso.refl
  counitIso := NatIso.ofComponents Iso.refl

Depends on / 依赖: asTypeToObjAsType
-/
noncomputable def asTypeEquivObjAsType : AsType α ≌ ObjAsType α where
  functor := asTypeToObjAsType α
  inverse := objAsTypeToAsType α
  unitIso := NatIso.ofComponents Iso.refl
  counitIso := NatIso.ofComponents Iso.refl

/--
Instance `asTypeFinCategory` / 实例 `asTypeFinCategory`

English:
instance asTypeFinCategory
  signature: : FinCategory (AsType α) where
  body: fun _ _ => show Fintype (Fin _) from inferInstance

中文:
实例 asTypeFinCategory
  签名: : 有限范畴 (AsType α) where
  定义体: fun _ _ => show Fintype (Fin _) from inferInstance

Depends on / 依赖: Fintype
-/
noncomputable instance asTypeFinCategory : FinCategory (AsType α) where
  fintypeHom := fun _ _ => show Fintype (Fin _) from inferInstance

/--
Definition of `equivAsType` / `equivAsType` 的定义

English:
definition equivAsType
  signature: : AsType α ≌ α
  body: (asTypeEquivObjAsType α).trans (objAsTypeEquiv α)

中文:
定义 equivAsType
  签名: : AsType α ≌ α
  定义体: (asTypeEquivObjAsType α).trans (objAsTypeEquiv α)

Depends on / 依赖: asTypeEquivObjAsType, objAsTypeEquiv
-/
noncomputable def equivAsType : AsType α ≌ α :=
  (asTypeEquivObjAsType α).trans (objAsTypeEquiv α)

end FinCategory

end CategoryTheory
