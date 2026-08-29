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

/--
Definition of `optionEquiv` / `optionEquiv` 的定义

English:
definition optionEquiv
  signature: : Option C ≃ WithTerminal C where
  body: by cases a <;> simp
  right_inv a := by cases a <;> simp

中文:
定义 optionEquiv
  签名: : Option C ≃ WithTerminal C where
  定义体: by cases a <;> simp
  right_inv a := by cases a <;> simp

Depends on / 依赖: right_inv
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

/--
Instance `instFintype` / 实例 `instFintype`

English:
instance instFintype
  signature: [Fintype C]
  body: .ofEquiv (Option C) optionEquiv C

中文:
实例 instFintype
  签名: [Fintype C]
  定义体: .ofEquiv (Option C) optionEquiv C

Depends on / 依赖: ofEquiv, optionEquiv
-/
instance instFintype [Fintype C] : Fintype (WithTerminal C) :=
.ofEquiv (Option C) optionEquiv C

/--
Instance `instFinCategory` / 实例 `instFinCategory`

English:
instance instFinCategory
  signature: [SmallCategory C] [FinCategory C]
  body: inferInstance
  fintypeHom
  | star, star
  | of _, star => (inferInstance : Fintype PUnit)
  | star, of _ => (inferInstance : Fintype PEmpty)
  | of a, of b => (inferInstance : Fintype (a ⟶ b))

中文:
实例 instFinCategory
  签名: [SmallCategory C] [FinCategory C]
  定义体: inferInstance
  fintypeHom
  | star, star
  | of _, star => (inferInstance : Fintype PUnit)
  | star, of _ => (inferInstance : Fintype PEmpty)
  | of a, of b => (inferInstance : Fintype (a ⟶ b))
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

/--
Definition of `optionEquiv` / `optionEquiv` 的定义

English:
definition optionEquiv
  signature: : Option C ≃ WithInitial C where
  body: by cases a <;> simp
  right_inv a := by cases a <;> simp

中文:
定义 optionEquiv
  签名: : Option C ≃ WithInitial C where
  定义体: by cases a <;> simp
  right_inv a := by cases a <;> simp

Depends on / 依赖: right_inv
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

/--
Instance `instFintype` / 实例 `instFintype`

English:
instance instFintype
  signature: [Fintype C]
  body: .ofEquiv (Option C) optionEquiv C

中文:
实例 instFintype
  签名: [Fintype C]
  定义体: .ofEquiv (Option C) optionEquiv C

Depends on / 依赖: ofEquiv, optionEquiv
-/
instance instFintype [Fintype C] : Fintype (WithInitial C) :=
.ofEquiv (Option C) optionEquiv C

/--
Instance `instFinCategory` / 实例 `instFinCategory`

English:
instance instFinCategory
  signature: [SmallCategory C] [FinCategory C]
  body: inferInstance
  fintypeHom
  | star, star
  | star, of _ => (inferInstance : Fintype PUnit)
  | of _, star => (inferInstance : Fintype PEmpty)
  | of a, of b => (inferInstance : Fintype (a ⟶ b))

中文:
实例 instFinCategory
  签名: [SmallCategory C] [FinCategory C]
  定义体: inferInstance
  fintypeHom
  | star, star
  | star, of _ => (inferInstance : Fintype PUnit)
  | of _, star => (inferInstance : Fintype PEmpty)
  | of a, of b => (inferInstance : Fintype (a ⟶ b))
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
