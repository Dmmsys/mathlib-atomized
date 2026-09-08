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

/-- A FinCategory `α` is equivalent to a category with objects in `Type`. -/
--@[nolint unused_arguments]
/-
**CategoryTheory.FinCategory.ObjAsType** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.FinCategory`。
形式化陈述：ObjAsType : Type
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
abbrev ObjAsType : Type :=
  InducedCategory α (Fintype.equivFin α).symm
/-
**CategoryTheory.FinCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.FinCateg
ory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {i j : ObjAsType α} : Fintype (i ⟶ j) :=
  Fintype.ofEquiv _ InducedCategory.homEquiv.symm

/-- The constructed category is indeed equivalent to `α`. -/
/-
**CategoryTheory.FinCategory.objAsTypeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.FinCategory`。
形式化陈述：objAsTypeEquiv : ObjAsType α ≌ α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The constructed category is indeed equivalent to `α`.
-/
noncomputable def objAsTypeEquiv : ObjAsType α ≌ α :=
  (inducedFunctor (Fintype.equivFin α).symm).asEquivalence

/-- A FinCategory `α` is equivalent to a FinCategory in `Type`. -/
--@[nolint unused_arguments]
/-
**CategoryTheory.FinCategory.AsType** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
FinCategory`。
形式化陈述：AsType : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev AsType : Type :=
  Fin (Fintype.card α)

set_option backward.isDefEq.respectTransparency.types false in
@[simps -isSimp id comp]
/-
**CategoryTheory.FinCategory.categoryAsType** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.FinCategory`。
形式化陈述：categoryAsType : SmallCategory (AsType α) where Hom i j
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
noncomputable instance categoryAsType : SmallCategory (AsType α) where
  Hom i j := Fin (Fintype.card (@Quiver.Hom (ObjAsType α) _ i j))
  id _ := Fintype.equivFin _ (𝟙 _)
  comp f g := Fintype.equivFin _ ((Fintype.equivFin _).symm f ≫ (Fintype.equivFin _).symm g)

attribute [local simp] categoryAsType_id categoryAsType_comp

set_option backward.isDefEq.respectTransparency.types false in
/-- The "identity" functor from `AsType α` to `ObjAsType α`. -/
@[simps]
/-
**CategoryTheory.FinCategory.asTypeToObjAsType** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.FinCategory`。
形式化陈述：asTypeToObjAsType : AsType α ⥤ ObjAsType α where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The "identity" functor from `AsType α` to `ObjAsType α`.
-/
noncomputable def asTypeToObjAsType : AsType α ⥤ ObjAsType α where
  obj := id
  map {_ _} := (Fintype.equivFin _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The "identity" functor from `ObjAsType α` to `AsType α`. -/
@[simps]
/-
**CategoryTheory.FinCategory.objAsTypeToAsType** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.FinCategory`。
形式化陈述：objAsTypeToAsType : ObjAsType α ⥤ AsType α where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The "identity" functor from `ObjAsType α` to `AsType α`.
-/
noncomputable def objAsTypeToAsType : ObjAsType α ⥤ AsType α where
  obj := id
  map {_ _} := Fintype.equivFin _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constructed category (`AsType α`) is equivalent to `ObjAsType α`. -/
/-
**CategoryTheory.FinCategory.asTypeEquivObjAsType** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.FinCategory`。
形式化陈述：asTypeEquivObjAsType : AsType α ≌ ObjAsType α where functor
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The constructed category (`AsType α`) is equivalent to `ObjAsType α`.
-/
noncomputable def asTypeEquivObjAsType : AsType α ≌ ObjAsType α where
  functor := asTypeToObjAsType α
  inverse := objAsTypeToAsType α
  unitIso := NatIso.ofComponents Iso.refl
  counitIso := NatIso.ofComponents Iso.refl
/-
**CategoryTheory.FinCategory.asTypeFinCategory** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.FinCategory`。
形式化陈述：asTypeFinCategory : FinCategory (AsType α) where fintypeHom
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
noncomputable instance asTypeFinCategory : FinCategory (AsType α) where
  fintypeHom := fun _ _ => show Fintype (Fin _) from inferInstance

/-- The constructed category (`AsType α`) is indeed equivalent to `α`. -/
/-
**CategoryTheory.FinCategory.equivAsType** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.FinCategory`。
形式化陈述：equivAsType : AsType α ≌ α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The constructed category (`AsType α`) is indeed equivalent to `α`.
-/
noncomputable def equivAsType : AsType α ≌ α :=
  (asTypeEquivObjAsType α).trans (objAsTypeEquiv α)

end FinCategory

end CategoryTheory

