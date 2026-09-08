/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Logic.Small.Set

/-!
# Small instances for pointwise operations
-/

public section

universe u

variable {α β : Type*} (s t : Set α)

open scoped Pointwise

/-
**small_set_zero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_set_zero [Zero α] : Small.{u} (0 : Set α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_single`：small_single (x : α) : Small.{u} ({x} : Set α)
-/
instance small_set_zero [Zero α] : Small.{u} (0 : Set α) := small_single _
/-
**small_set_one** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_set_one [One α] : Small.{u} (1 : Set α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `small_single`：small_single (x : α) : Small.{u} ({x} : Set α)
-/
instance small_set_one [One α] : Small.{u} (1 : Set α) := small_single _
/-
**small_neg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_neg [InvolutiveNeg α] [Small.{u} s] : Small.{u} (-s :)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_neg_eq_neg`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s : Set
 α}, (fun x => -x) '' s = -s
-/
instance small_neg [InvolutiveNeg α] [Small.{u} s] : Small.{u} (-s :) := by
  rw [← Set.image_neg_eq_neg]
  infer_instance
/-
**small_add** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_add [Add α] [Small.{u} s] [Small.{u} t] : Small.{u} (s + t)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance small_add [Add α] [Small.{u} s] [Small.{u} t] : Small.{u} (s + t) := small_image2 ..
/-
**small_sub** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_sub [Sub α] [Small.{u} s] [Small.{u} t] : Small.{u} (s - t)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance small_sub [Sub α] [Small.{u} s] [Small.{u} t] : Small.{u} (s - t) := small_image2 ..
/-
**small_mul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_mul [Mul α] [Small.{u} s] [Small.{u} t] : Small.{u} (s * t)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance small_mul [Mul α] [Small.{u} s] [Small.{u} t] : Small.{u} (s * t) := small_image2 ..
/-
**small_div** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：small_div [Div α] [Small.{u} s] [Small.{u} t] : Small.{u} (s / t)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance small_div [Div α] [Small.{u} s] [Small.{u} t] : Small.{u} (s / t) := small_image2 ..
