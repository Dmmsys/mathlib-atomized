/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Category.ULift

/-!
# Finite categories

A category is finite in this sense if it has finitely many objects, and finitely many morphisms.

## Implementation
Prior to https://github.com/leanprover-community/mathlib4/pull/14046, `FinCategory` required a `DecidableEq` instance on the object and morphism types.
This does not seem to have had any practical payoff (i.e. making some definition constructive)
so we have removed these requirements to avoid
having to supply instances or delay with non-defeq conflicts between instances.
-/

public section


universe w v u

noncomputable section

namespace CategoryTheory

/-
**CategoryTheory.discreteFintype** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：discreteFintype {α : Type*} [Fintype α] : Fintype (Discrete α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance discreteFintype {α : Type*} [Fintype α] : Fintype (Discrete α) :=
  Fintype.ofEquiv α discreteEquiv.symm
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} [Finite α] : Finite (Discrete α) :=
  Finite.of_equiv α discreteEquiv.symm
/-
**CategoryTheory.discreteHomFintype** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：discreteHomFintype {α : Type*} (X Y : Discrete α) : Fintype (X ⟶ Y)
参数：X Y : Discrete α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance discreteHomFintype {α : Type*} (X Y : Discrete α) : Fintype (X ⟶ Y) := by
  classical
  apply ULift.fintype

/-- A category with a `Fintype` of objects, and a `Fintype` for each morphism space. -/
/-
**CategoryTheory.FinCategory** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：FinCategory (J : Type v) [SmallCategory J] where fintypeObj : Fintype J
参数：J : Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category with a `Fintype` of objects, and a `Fintype` for each morphism space.
-/
class FinCategory (J : Type v) [SmallCategory J] where
  fintypeObj : Fintype J := by infer_instance
  fintypeHom : ∀ j j' : J, Fintype (j ⟶ j') := by infer_instance

attribute [instance_reducible, instance] FinCategory.fintypeObj FinCategory.fintypeHom
/-
**CategoryTheory.finCategoryDiscreteOfFintype** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory`。
形式化陈述：(J : Type v) → [Fintype J] → CategoryTheory.FinCategory (CategoryTheory.Di
screte J)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance finCategoryDiscreteOfFintype (J : Type v) [Fintype J] : FinCategory (Discrete J) where
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type u} [Fintype J] [SmallCategory J] [Quiver.IsThin J] : FinCategory J :=
  FinCategory.mk ‹Fintype J› fun j j' ↦ Fintype.ofFinite (j ⟶ j')

open Opposite

/-- The opposite of a finite category is finite.
-/
/-
**CategoryTheory.finCategoryOpposite** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：finCategoryOpposite {J : Type v} [SmallCategory J] [FinCategory J] : FinCa
tegory Jᵒᵖ where fintypeObj
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The opposite of a finite category is finite.
-/
instance finCategoryOpposite {J : Type v} [SmallCategory J] [FinCategory J] : FinCategory Jᵒᵖ where
  fintypeObj := Fintype.ofEquiv _ equivToOpposite
  fintypeHom j j' := Fintype.ofEquiv _ (opEquiv j j').symm

attribute [local instance] uliftCategory in
/-- Applying `ULift` to morphisms and objects of a category preserves finiteness. -/
/-
**CategoryTheory.finCategoryUlift** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：finCategoryUlift {J : Type v} [SmallCategory J] [FinCategory J] : FinCateg
ory.{max w v} (ULiftHom.{w, max w v} (ULift.{w, v} J)) where fintypeObj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying `ULift` to morphisms and objects of a category preserves finiteness.
-/
instance finCategoryUlift {J : Type v} [SmallCategory J] [FinCategory J] :
    FinCategory.{max w v} (ULiftHom.{w, max w v} (ULift.{w, v} J)) where
  fintypeObj := ULift.fintype J
  fintypeHom := fun _ _ => ULift.fintype _

end CategoryTheory

