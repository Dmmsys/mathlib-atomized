/-
Copyright (c) 2025 Moisés Herradón Cueto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moisés Herradón Cueto
-/
module

public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.CategoryTheory.WithTerminal.Basic
public import Mathlib.Data.Fintype.Option

/-!

# `WithTerminal C` and `WithInitial C` are finite whenever `C` is

If `C` has finitely many objects, then so do `WithTerminal C` and `WithInitial C`,
and likewise if `C` has finitely many morphisms as well.

-/

@[expose] public section


universe v u

variable (C : Type u) [CategoryTheory.Category.{v} C]

namespace CategoryTheory.WithTerminal

/-- The equivalence between `Option C` and `WithTerminal C` (they are both the
type `C` plus an extra object `none` or `star`). -/
/-
**CategoryTheory.WithTerminal.optionEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.WithTerminal`。
形式化陈述：optionEquiv : Option C ≃ WithTerminal C where toFun | some a => of a | non
e => star invFun | of a => some a | star => none left_inv a
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `Option C` and `WithTerminal C` (they are both the
type `C` plus an extra object `none` or `star`).
-/
def optionEquiv : Option C ≃ WithTerminal C where
  toFun
  | some a => of a
  | none => star
  invFun
  | of a => some a
  | star => none
  left_inv a := by cases a <;> simp
  right_inv a := by cases a <;> simp
/-
**CategoryTheory.WithTerminal.instFintype** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.WithTerminal`。
形式化陈述：instFintype [Fintype C] : Fintype (WithTerminal C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFintype [Fintype C] : Fintype (WithTerminal C) :=
  .ofEquiv (Option C) <| optionEquiv C
/-
**CategoryTheory.WithTerminal.instFinCategory** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.WithTerminal`。
形式化陈述：instFinCategory [SmallCategory C] [FinCategory C] : FinCategory (WithTermi
nal C) where fintypeObj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFinCategory [SmallCategory C] [FinCategory C] :
    FinCategory (WithTerminal C) where
  fintypeObj := inferInstance
  fintypeHom
  | star, star
  | of _, star => (inferInstance : Fintype PUnit)
  | star, of _ => (inferInstance : Fintype PEmpty)
  | of a, of b => (inferInstance : Fintype (a ⟶ b))

end CategoryTheory.WithTerminal

namespace CategoryTheory.WithInitial

/-- The equivalence between `Option C` and `WithInitial C` (they are both the
type `C` plus an extra object `none` or `star`). -/
/-
**CategoryTheory.WithInitial.optionEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.WithInitial`。
形式化陈述：optionEquiv : Option C ≃ WithInitial C where toFun | some a => of a | none
 => star invFun | of a => some a | star => none left_inv a
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `Option C` and `WithInitial C` (they are both the
type `C` plus an extra object `none` or `star`).
-/
def optionEquiv : Option C ≃ WithInitial C where
  toFun
  | some a => of a
  | none => star
  invFun
  | of a => some a
  | star => none
  left_inv a := by cases a <;> simp
  right_inv a := by cases a <;> simp
/-
**CategoryTheory.WithInitial.instFintype** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.WithInitial`。
形式化陈述：instFintype [Fintype C] : Fintype (WithInitial C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFintype [Fintype C] : Fintype (WithInitial C) :=
  .ofEquiv (Option C) <| optionEquiv C
/-
**CategoryTheory.WithInitial.instFinCategory** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.WithInitial`。
形式化陈述：instFinCategory [SmallCategory C] [FinCategory C] : FinCategory (WithIniti
al C) where fintypeObj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFinCategory [SmallCategory C] [FinCategory C] :
    FinCategory (WithInitial C) where
  fintypeObj := inferInstance
  fintypeHom
  | star, star
  | star, of _ => (inferInstance : Fintype PUnit)
  | of _, star => (inferInstance : Fintype PEmpty)
  | of a, of b => (inferInstance : Fintype (a ⟶ b))

end CategoryTheory.WithInitial

