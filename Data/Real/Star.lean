/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Data.Real.Basic

/-!
# The real numbers are a \*-ring, with the trivial \*-structure
-/

public section

/-- The real numbers are a \*-ring, with the trivial \*-structure. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The real numbers are a \*-ring, with the trivial \*-structure.
-/
instance : StarRing ℝ :=
  starRingOfComm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TrivialStar ℝ :=
  ⟨fun _ => rfl⟩
