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

/--
Definition of `FreeAbelianGroup.basis` / `FreeAbelianGroup.basis` 的定义

English:
definition FreeAbelianGroup.basis
  signature: (α : Type*)
  body: ⟨(FreeAbelianGroup.equivFinsupp α).toIntLinearEquiv⟩

中文:
定义 FreeAbelianGroup.basis
  签名: (α : 类型)
  定义体: ⟨(FreeAbelianGroup.equivFinsupp α).toIntLinearEquiv⟩

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.equivFinsupp, equivFinsupp, toIntLinearEquiv
-/
noncomputable def FreeAbelianGroup.basis (α : Type*) : Basis α Int (FreeAbelianGroup α) :=
  ⟨(FreeAbelianGroup.equivFinsupp α).toIntLinearEquiv⟩

/--
Definition of `Equiv.ofFreeAbelianGroupLinearEquiv` / `Equiv.ofFreeAbelianGroupLinearEquiv` 的定义

English:
definition Equiv.ofFreeAbelianGroupLinearEquiv
  signature: (e : FreeAbelianGroup α ≃ₗ[Int] FreeAbelianGroup β)
  body: let t : Basis α Int (FreeAbelianGroup β) := (FreeAbelianGroup.basis α).map e
t.indexEquiv FreeAbelianGroup.basis _

中文:
定义 Equiv.ofFreeAbelianGroupLinearEquiv
  签名: (e : FreeAbelianGroup α ≃ₗ[整数] FreeAbelianGroup β)
  定义体: let t : Basis α Int (FreeAbelianGroup β) := (FreeAbelianGroup.basis α).map e
t.indexEquiv FreeAbelianGroup.basis _

Depends on / 依赖: FreeAbelianGroup, FreeAbelianGroup.basis, indexEquiv, t.indexEquiv
-/
def Equiv.ofFreeAbelianGroupLinearEquiv (e : FreeAbelianGroup α ≃ₗ[Int] FreeAbelianGroup β) : α ≃ β :=
  let t : Basis α Int (FreeAbelianGroup β) := (FreeAbelianGroup.basis α).map e
t.indexEquiv FreeAbelianGroup.basis _

/--
Definition of `Equiv.ofFreeAbelianGroupEquiv` / `Equiv.ofFreeAbelianGroupEquiv` 的定义

English:
definition Equiv.ofFreeAbelianGroupEquiv
  signature: (e : FreeAbelianGroup α ≃+ FreeAbelianGroup β)
  body: .ofFreeAbelianGroupLinearEquiv e.toIntLinearEquiv

中文:
定义 Equiv.ofFreeAbelianGroupEquiv
  签名: (e : FreeAbelianGroup α ≃+ FreeAbelianGroup β)
  定义体: .ofFreeAbelianGroupLinearEquiv e.toIntLinearEquiv

Depends on / 依赖: e.toIntLinearEquiv, ofFreeAbelianGroupLinearEquiv, toIntLinearEquiv
-/
def Equiv.ofFreeAbelianGroupEquiv (e : FreeAbelianGroup α ≃+ FreeAbelianGroup β) : α ≃ β :=
  .ofFreeAbelianGroupLinearEquiv e.toIntLinearEquiv

/--
Definition of `Equiv.ofFreeGroupEquiv` / `Equiv.ofFreeGroupEquiv` 的定义

English:
definition Equiv.ofFreeGroupEquiv
  signature: (e : FreeGroup α ≃* FreeGroup β)
  body: .ofFreeAbelianGroupEquiv (MulEquiv.toAdditive e.abelianizationCongr)

中文:
定义 Equiv.ofFreeGroupEquiv
  签名: (e : FreeGroup α ≃* FreeGroup β)
  定义体: .ofFreeAbelianGroupEquiv (MulEquiv.toAdditive e.abelianizationCongr)

Depends on / 依赖: MulEquiv, MulEquiv.toAdditive, abelianizationCongr, e.abelianizationCongr, ofFreeAbelianGroupEquiv, toAdditive
-/
def Equiv.ofFreeGroupEquiv (e : FreeGroup α ≃* FreeGroup β) : α ≃ β :=
  .ofFreeAbelianGroupEquiv (MulEquiv.toAdditive e.abelianizationCongr)

/--
Definition of `Equiv.ofIsFreeGroupEquiv` / `Equiv.ofIsFreeGroupEquiv` 的定义

English:
definition Equiv.ofIsFreeGroupEquiv
  signature: [Group G] [Group H] [IsFreeGroup G] [IsFreeGroup H] (e : G ≃* H)
  body: .ofFreeGroupEquiv (toFreeGroup G).symm.trans e.trans toFreeGroup H

中文:
定义 Equiv.ofIsFreeGroupEquiv
  签名: [Group G] [Group H] [IsFreeGroup G] [IsFreeGroup H] (e : G ≃* H)
  定义体: .ofFreeGroupEquiv (toFreeGroup G).symm.trans e.trans toFreeGroup H

Depends on / 依赖: e.trans, ofFreeGroupEquiv, symm.trans, toFreeGroup
-/
def Equiv.ofIsFreeGroupEquiv [Group G] [Group H] [IsFreeGroup G] [IsFreeGroup H] (e : G ≃* H) :
    Generators G ≃ Generators H :=
.ofFreeGroupEquiv (toFreeGroup G).symm.trans e.trans toFreeGroup H
