/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin, Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.CategoryTheory.Simple
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Simple objects in the category of `R`-modules

We prove simple modules are exactly simple objects in the category of `R`-modules.
-/

public section


variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

open CategoryTheory ModuleCat

/--
theorem `simple_iff_isSimpleModule` / 定理 `simple_iff_isSimpleModule`

English:
theorem simple_iff_isSimpleModule
  statement: Simple (of R M) ↔ IsSimpleModule R M
  proof: by
  rw [simple_iff_subobject_isSimpleOrder]; rw [(subobjectModule (of R M)).isSimpleOrder_iff]; rw [isSimpleModule_iff]

中文:
定理 simple_iff_isSimpleModule
  结论: 单 (of R M) ↔ 是单模 R M
  证明: by
  rw [simple_iff_subobject_isSimpleOrder]; rw [(subobjectModule (of R M)).isSimpleOrder_iff]; rw [isSimpleModule_iff]

Depends on / 依赖: isSimpleModule_iff, isSimpleOrder_iff, simple_iff_subobject_isSimpleOrder, subobjectModule
-/
theorem simple_iff_isSimpleModule : Simple (of R M) ↔ IsSimpleModule R M := by
  rw [simple_iff_subobject_isSimpleOrder]; rw [(subobjectModule (of R M)).isSimpleOrder_iff]; rw [isSimpleModule_iff]

/--
theorem `simple_iff_isSimpleModule'` / 定理 `simple_iff_isSimpleModule'`

English:
theorem simple_iff_isSimpleModule'
  given: (M : ModuleCat R)
  statement: Simple M ↔ IsSimpleModule R M
  proof: simple_iff_isSimpleModule

中文:
定理 simple_iff_isSimpleModule'
  条件: (M : 模范畴 R)
  结论: 单 M ↔ 是单模 R M
  证明: simple_iff_isSimpleModule

Depends on / 依赖: simple_iff_isSimpleModule
-/
theorem simple_iff_isSimpleModule' (M : ModuleCat R) : Simple M ↔ IsSimpleModule R M :=
  simple_iff_isSimpleModule

/--
Instance `simple_of_isSimpleModule` / 实例 `simple_of_isSimpleModule`

English:
instance simple_of_isSimpleModule
  signature: [IsSimpleModule R M]
  body: simple_iff_isSimpleModule.mpr ‹_›

中文:
实例 simple_of_isSimpleModule
  签名: [是单模 R M]
  定义体: simple_iff_isSimpleModule.mpr ‹_›

Depends on / 依赖: simple_iff_isSimpleModule, simple_iff_isSimpleModule.mpr
-/
instance simple_of_isSimpleModule [IsSimpleModule R M] : Simple (of R M) :=
  simple_iff_isSimpleModule.mpr ‹_›

/--
Instance `isSimpleModule_of_simple` / 实例 `isSimpleModule_of_simple`

English:
instance isSimpleModule_of_simple
  signature: (M : ModuleCat R) [Simple M]
  body: simple_iff_isSimpleModule.mp ‹_›

中文:
实例 isSimpleModule_of_simple
  签名: (M : 模范畴 R) [单 M]
  定义体: simple_iff_isSimpleModule.mp ‹_›

Depends on / 依赖: simple_iff_isSimpleModule, simple_iff_isSimpleModule.mp
-/
instance isSimpleModule_of_simple (M : ModuleCat R) [Simple M] : IsSimpleModule R M :=
  simple_iff_isSimpleModule.mp ‹_›

open Module

attribute [local instance] moduleOfAlgebraModule isScalarTower_of_algebra_moduleCat

/--
theorem `simple_of_finrank_eq_one` / 定理 `simple_of_finrank_eq_one`

English:
theorem simple_of_finrank_eq_one
  statement: {k : Type*} [Field k] [Algebra k R] {V : ModuleCat R}
  proof: (simple_iff_isSimpleModule' V).mpr (isSimpleModule_iff ..).mpr
    is_simple_module_of_finrank_eq_one h

中文:
定理 simple_of_finrank_eq_one
  结论: {k : 类型} [域 k] [代数 k R] {V : 模范畴 R}
  证明: (simple_iff_isSimpleModule' V).mpr (isSimpleModule_iff ..).mpr
    is_simple_module_of_finrank_eq_one h

Depends on / 依赖: isSimpleModule_iff, is_simple_module_of_finrank_eq_one, simple_iff_isSimpleModule
-/
theorem simple_of_finrank_eq_one {k : Type*} [Field k] [Algebra k R] {V : ModuleCat R}
    (h : finrank k V = 1) : Simple V :=
(simple_iff_isSimpleModule' V).mpr (isSimpleModule_iff ..).mpr
    is_simple_module_of_finrank_eq_one h
