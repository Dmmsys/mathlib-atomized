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

variable {ι : Type u} {π : ι → Type v} [∀ i, Zero (π i)]

section Small

/-
**DFinsupp.small** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：DFinsupp.small [Small.{w} ι] [forall (i : ι), Small.{w} (π i)] : Small.{w}
 (DFinsupp π)
参数：i : ι；π i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
instance DFinsupp.small [Small.{w} ι] [∀ (i : ι), Small.{w} (π i)] :
    Small.{w} (DFinsupp π) :=
  small_of_injective (f := fun x j ↦ x j) (fun f f' eq ↦ by ext j; exact congr_fun eq j)
/-
**Finsupp.small** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Finsupp.small {σ : Type*} {R : Type*} [Zero R] [Small.{u} R] [Small.{u} σ]
 : Small.{u} (σ ->₀ R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_map`：small_map {α : Type*} {β : Type*} [hβ : Small.{w} β] (e : α ≃
 β) : Small.{w} α
-/
instance Finsupp.small {σ : Type*} {R : Type*} [Zero R]
    [Small.{u} R] [Small.{u} σ] :
    Small.{u} (σ →₀ R) := by
  classical
  exact small_map finsuppEquivDFinsupp

end Small

