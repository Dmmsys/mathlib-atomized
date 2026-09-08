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

/-
**smallVector** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：smallVector {α : Type v} {n : Nat} [Small.{u} α] : Small.{u} (List.Vector 
α n)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
instance smallVector {α : Type v} {n : ℕ} [Small.{u} α] : Small.{u} (List.Vector α n) :=
  small_of_injective (Equiv.vectorEquivFin α n).injective
/-
**smallList** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：smallList {α : Type v} [Small.{u} α] : Small.{u} (List α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
instance smallList {α : Type v} [Small.{u} α] : Small.{u} (List α) := by
  let e : (Σ n, List.Vector α n) ≃ List α := Equiv.sigmaFiberEquiv List.length
  exact small_of_surjective e.surjective
