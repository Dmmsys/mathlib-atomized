/-
Copyright (c) 2025 Sophie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Finsupp.ToDFinsupp
public import Mathlib.Data.DFinsupp.Defs
public import Mathlib.Logic.Small.Basic

/-!
# Smallness of the `DFinsupp` type

Let `π : ι → Type v`. If `ι` and all the `π i` are `w`-small, this provides a `Small.{w}`
instance on `DFinsupp π`.

As an application, `σ →₀ R` has a `Small.{v}` instance if `σ` and `R` have one.
-/

public section

universe u v w

variable {ι : Type u} {π : ι -> Type v} [forall i, Zero (π i)]

section Small

/--
Instance `DFinsupp.small` / 实例 `DFinsupp.small`

English:
instance DFinsupp.small
  signature: [Small.{w} ι] [forall (i : ι), Small.{w} (π i)]
  body: small_of_injective (f := fun x j => x j) (fun f f' eq => by ext j; exact congr_fun eq j)

中文:
实例 直和有限支撑.small
  签名: [Small.{w} ι] [对任意 (i : ι), Small.{w} (π i)]
  定义体: small_of_injective (f := fun x j => x j) (fun f f' eq => by ext j; exact congr_fun eq j)

Depends on / 依赖: congr_fun, small_of_injective
-/
instance DFinsupp.small [Small.{w} ι] [forall (i : ι), Small.{w} (π i)] :
    Small.{w} (DFinsupp π) :=
  small_of_injective (f := fun x j => x j) (fun f f' eq => by ext j; exact congr_fun eq j)

/--
Instance `Finsupp.small` / 实例 `Finsupp.small`

English:
instance Finsupp.small
  signature: {σ : Type*} {R : Type*} [Zero R]
  body: by
  classical
  exact small_map finsuppEquivDFinsupp

中文:
实例 有限支撑.small
  签名: {σ : 类型} {R : 类型} [零 R]
  定义体: by
  classical
  exact small_map finsuppEquivDFinsupp

Depends on / 依赖: classical, finsuppEquivDFinsupp, small_map
-/
instance Finsupp.small {σ : Type*} {R : Type*} [Zero R]
    [Small.{u} R] [Small.{u} σ] :
    Small.{u} (σ ->₀ R) := by
  classical
  exact small_map finsuppEquivDFinsupp

end Small
