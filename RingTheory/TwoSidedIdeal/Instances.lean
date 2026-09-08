/-
Copyright (c) 2024 euprunin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: euprunin
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.RingTheory.NonUnitalSubring.Defs
public import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# Additional instances for two-sided ideals.
-/

public section
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R} [NonUnitalNonAssocRing R] : NonUnitalSubringClass (TwoSidedIdeal R) R where
  mul_mem _ hb := TwoSidedIdeal.mul_mem_left _ _ _ hb
