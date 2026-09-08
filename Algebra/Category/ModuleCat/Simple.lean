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

/-
**simple_iff_isSimpleModule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：simple_iff_isSimpleModule : Simple (of R M) ↔ IsSimpleModule R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `ModuleCat.instHasZeroObject`：∀ {R : Type u} [inst : Ring R], CategoryThe
ory.Limits.HasZeroObject (ModuleCat R)
· 使用定理 `CategoryTheory.Limits.HasZeroObject.initialMonoClass`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C], 
  CategoryTheory.Limits.InitialMonoClass C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.simple_iff_subobject_isSimpleOrder`：simple_iff_subobject_
isSimpleOrder (X : C) : Simple X ↔ IsSimpleOrder (Subobject X)
· 使用定理 `OrderIso.isSimpleOrder_iff`：isSimpleOrder_iff [BoundedOrder α] [BoundedO
rder β] (f : α ≃o β) : IsSimpleOrder α ↔ IsSimpleOrder β
· 使用定理 `isSimpleModule_iff`：∀ (R : Type u_2) [inst : Ring R] (M : Type u_4) [ins
t_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsSimpleModule R M ↔ IsSim
pleOrder…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem simple_iff_isSimpleModule : Simple (of R M) ↔ IsSimpleModule R M := by
  rw [simple_iff_subobject_isSimpleOrder, (subobjectModule (of R M)).isSimpleOrder_iff,
    isSimpleModule_iff]
/-
**simple_iff_isSimpleModule'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：simple_iff_isSimpleModule' (M : ModuleCat R) : Simple M ↔ IsSimpleModule R
 M
参数：M : ModuleCat R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `simple_iff_isSimpleModule`：simple_iff_isSimpleModule : Simple (of R M) ↔
 IsSimpleModule R M
-/
theorem simple_iff_isSimpleModule' (M : ModuleCat R) : Simple M ↔ IsSimpleModule R M :=
  simple_iff_isSimpleModule

/-- A simple module is a simple object in the category of modules. -/
/-
**simple_of_isSimpleModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：simple_of_isSimpleModule [IsSimpleModule R M] : Simple (of R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `simple_iff_isSimpleModule`：simple_iff_isSimpleModule : Simple (of R M) ↔
 IsSimpleModule R M

--- 原说明 ---
A simple module is a simple object in the category of modules.
-/
instance simple_of_isSimpleModule [IsSimpleModule R M] : Simple (of R M) :=
  simple_iff_isSimpleModule.mpr ‹_›

/-- A simple object in the category of modules is a simple module. -/
/-
**isSimpleModule_of_simple** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isSimpleModule_of_simple (M : ModuleCat R) [Simple M] : IsSimpleModule R M
参数：M : ModuleCat R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `simple_iff_isSimpleModule`：simple_iff_isSimpleModule : Simple (of R M) ↔
 IsSimpleModule R M

--- 原说明 ---
A simple object in the category of modules is a simple module.
-/
instance isSimpleModule_of_simple (M : ModuleCat R) [Simple M] : IsSimpleModule R M :=
  simple_iff_isSimpleModule.mp ‹_›

open Module

attribute [local instance] moduleOfAlgebraModule isScalarTower_of_algebra_moduleCat

/-- Any `k`-algebra module which is 1-dimensional over `k` is simple. -/
/-
**simple_of_finrank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：simple_of_finrank_eq_one {k : Type*} [Field k] [Algebra k R] {V : ModuleCa
t R} (h : finrank k V = 1) : Simple V
参数：h : finrank k V = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `simple_iff_isSimpleModule'`：simple_iff_isSimpleModule' (M : ModuleCat R)
 : Simple M ↔ IsSimpleModule R M
· 使用定理 `isSimpleModule_iff`：∀ (R : Type u_2) [inst : Ring R] (M : Type u_4) [ins
t_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsSimpleModule R M ↔ IsSim
pleOrder…
· 使用定理 `is_simple_module_of_finrank_eq_one`：is_simple_module_of_finrank_eq_one {
A} [Semiring A] [Module A V] [SMul K A] [IsScalarTower K A V] (h : finrank K V =
 1) : IsSimpleOrder (Sub…
· 使用定理 `ModuleCat.isScalarTower_of_algebra_moduleCat`：isScalarTower_of_algebra_m
oduleCat (M : ModuleCat.{v} A) : IsScalarTower k A M

--- 原说明 ---
Any `k`-algebra module which is 1-dimensional over `k` is simple.
-/
theorem simple_of_finrank_eq_one {k : Type*} [Field k] [Algebra k R] {V : ModuleCat R}
    (h : finrank k V = 1) : Simple V :=
  (simple_iff_isSimpleModule' V).mpr <| (isSimpleModule_iff ..).mpr <|
    is_simple_module_of_finrank_eq_one h
