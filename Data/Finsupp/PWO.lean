/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Mathlib.Order.Preorder.Finsupp
public import Mathlib.Order.WellFoundedSet

/-!
# Partial well ordering on finsupps

This file contains the fact that finitely supported functions from a fintype are
partially well-ordered when the codomain is a linear order that is well ordered.
It is in a separate file for now so as to not add imports to the file `Order.WellFoundedSet`.

## Main statements

* `Finsupp.isPWO` - finitely supported functions from a fintype are partially well-ordered when
  the codomain is a linear order that is well ordered

## Tags

Dickson, order, partial well order
-/

public section
/--
Instance `Finsupp.wellQuasiOrderedLE` / 实例 `Finsupp.wellQuasiOrderedLE`

English:
instance Finsupp.wellQuasiOrderedLE
  signature: {α σ : Type*} [Zero α] [Preorder α] [WellQuasiOrderedLE α]
  body: orderIsoFunOnFinite.wellQuasiOrderedLE_iff.2 inferInstance

中文:
实例 有限支撑.wellQuasiOrderedLE
  签名: {α σ : 类型} [零 α] [预序 α] [良拟序 α]
  定义体: orderIsoFunOnFinite.wellQuasiOrderedLE_iff.2 inferInstance

Depends on / 依赖: orderIsoFunOnFinite, orderIsoFunOnFinite.wellQuasiOrderedLE_iff, wellQuasiOrderedLE_iff
-/
instance Finsupp.wellQuasiOrderedLE {α σ : Type*} [Zero α] [Preorder α] [WellQuasiOrderedLE α]
    [Finite σ] : WellQuasiOrderedLE (σ ->₀ α) :=
  orderIsoFunOnFinite.wellQuasiOrderedLE_iff.2 inferInstance
