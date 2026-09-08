/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Fintype.Vector

/-!
# Finiteness of vector types
-/

public section

variable {α : Type*}

/-
**List.Vector.finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：List.Vector.finite [Finite α] {n : Nat} : Finite (Vector α n)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Vector.instFinite`：∀ {α : Type u_1} [Finite α] {n : ℕ}, Finite (Lis
t.Vector α n)
-/
instance List.Vector.finite [Finite α] {n : ℕ} : Finite (Vector α n) := by
  have := Fintype.ofFinite α
  infer_instance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite α] {n : ℕ} : Finite (Sym α n) := by
  have := Fintype.ofFinite α
  infer_instance
