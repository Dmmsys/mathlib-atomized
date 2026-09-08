/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Isomorphisms between free groups imply equivalences of their generators

-/

@[expose] public section

noncomputable section

variable {α β G H : Type*}

open IsFreeGroup Module

/-- `A` is a basis of the ℤ-module `FreeAbelianGroup A`. -/
/-
**FreeAbelianGroup.basis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FreeAbelianGroup.basis (α : Type*) : Basis α Int (FreeAbelianGroup α)
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A` is a basis of the ℤ-module `FreeAbelianGroup A`.
-/
noncomputable def FreeAbelianGroup.basis (α : Type*) : Basis α ℤ (FreeAbelianGroup α) :=
  ⟨(FreeAbelianGroup.equivFinsupp α).toIntLinearEquiv⟩

/-- Isomorphic free abelian groups (as modules) have equivalent bases. -/
/-
**Equiv.ofFreeAbelianGroupLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Equiv.ofFreeAbelianGroupLinearEquiv (e : FreeAbelianGroup α ≃ₗ[Int] FreeAb
elianGroup β) : α ≃ β
参数：e : FreeAbelianGroup α ≃ₗ[Int] FreeAbelianGroup β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `invariantBasisNumber_of_nontrivial_of_commRing`：∀ {R : Type u} [inst : C
ommRing R] [Nontrivial R], InvariantBasisNumber R

--- 原说明 ---
Isomorphic free abelian groups (as modules) have equivalent bases.
-/
def Equiv.ofFreeAbelianGroupLinearEquiv (e : FreeAbelianGroup α ≃ₗ[ℤ] FreeAbelianGroup β) : α ≃ β :=
  let t : Basis α ℤ (FreeAbelianGroup β) := (FreeAbelianGroup.basis α).map e
  t.indexEquiv <| FreeAbelianGroup.basis _

/-- Isomorphic free abelian groups (as additive groups) have equivalent bases. -/
/-
**Equiv.ofFreeAbelianGroupEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Equiv.ofFreeAbelianGroupEquiv (e : FreeAbelianGroup α ≃+ FreeAbelianGroup 
β) : α ≃ β
参数：e : FreeAbelianGroup α ≃+ FreeAbelianGroup β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphic free abelian groups (as additive groups) have equivalent bases.
-/
def Equiv.ofFreeAbelianGroupEquiv (e : FreeAbelianGroup α ≃+ FreeAbelianGroup β) : α ≃ β :=
  .ofFreeAbelianGroupLinearEquiv e.toIntLinearEquiv

/-- Isomorphic free groups have equivalent bases. -/
/-
**Equiv.ofFreeGroupEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Equiv.ofFreeGroupEquiv (e : FreeGroup α ≃* FreeGroup β) : α ≃ β
参数：e : FreeGroup α ≃* FreeGroup β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphic free groups have equivalent bases.
-/
def Equiv.ofFreeGroupEquiv (e : FreeGroup α ≃* FreeGroup β) : α ≃ β :=
  .ofFreeAbelianGroupEquiv (MulEquiv.toAdditive e.abelianizationCongr)

/-- Isomorphic free groups have equivalent bases (`IsFreeGroup` variant). -/
/-
**Equiv.ofIsFreeGroupEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Equiv.ofIsFreeGroupEquiv [Group G] [Group H] [IsFreeGroup G] [IsFreeGroup 
H] (e : G ≃* H) : Generators G ≃ Generators H
参数：e : G ≃* H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphic free groups have equivalent bases (`IsFreeGroup` variant).
-/
def Equiv.ofIsFreeGroupEquiv [Group G] [Group H] [IsFreeGroup G] [IsFreeGroup H] (e : G ≃* H) :
    Generators G ≃ Generators H :=
  .ofFreeGroupEquiv <| (toFreeGroup G).symm.trans <| e.trans <| toFreeGroup H
