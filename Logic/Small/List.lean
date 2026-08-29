/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Logic.Small.Basic
public import Mathlib.Data.Vector.Basic

/-!
# Instances for `Small (List α)` and `Small (Vector α)`.

These must not be in `Logic.Small.Basic` as this is very low in the import hierarchy,
and is used by category theory files which do not need everything imported by `Data.Vector.Basic`.
-/

public section


universe u v

open Mathlib

/--
Instance `smallVector` / 实例 `smallVector`

English:
instance smallVector
  signature: {α : Type v} {n : Nat} [Small.{u} α]
  body: small_of_injective (Equiv.vectorEquivFin α n).injective

中文:
实例 smallVector
  签名: {α : 类型v} {n : 自然数} [Small.{u} α]
  定义体: small_of_injective (Equiv.vectorEquivFin α n).injective

Depends on / 依赖: Equiv.vectorEquivFin, injective, small_of_injective, vectorEquivFin
-/
instance smallVector {α : Type v} {n : Nat} [Small.{u} α] : Small.{u} (List.Vector α n) :=
  small_of_injective (Equiv.vectorEquivFin α n).injective

/--
Instance `smallList` / 实例 `smallList`

English:
instance smallList
  signature: {α : Type v} [Small.{u} α]
  body: by
  let e : (Σ n, List.Vector α n) ≃ List α := Equiv.sigmaFiberEquiv List.length
  exact small_of_surjective e.surjective

中文:
实例 smallList
  签名: {α : 类型v} [Small.{u} α]
  定义体: by
  let e : (Σ n, List.Vector α n) ≃ List α := Equiv.sigmaFiberEquiv List.length
  exact small_of_surjective e.surjective

Depends on / 依赖: Equiv.sigmaFiberEquiv, List.Vector, List.length, Vector, e.surjective, length, sigmaFiberEquiv, small_of_surjective, surjective
-/
instance smallList {α : Type v} [Small.{u} α] : Small.{u} (List α) := by
  let e : (Σ n, List.Vector α n) ≃ List α := Equiv.sigmaFiberEquiv List.length
  exact small_of_surjective e.surjective
