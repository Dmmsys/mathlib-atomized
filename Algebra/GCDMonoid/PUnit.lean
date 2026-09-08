/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.Ring.PUnit

/-!
# `PUnit` is a GCD monoid

This file collects facts about algebraic structures on the one-element type, e.g. that it is has a
GCD.
-/

public section

namespace PUnit

-- This is too high-powered and should be split off also
/-
**PUnit.** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StrongNormalizedGCDMonoid PUnit where
  gcd _ _ := unit
  lcm _ _ := unit
  normUnit _ := 1
  normUnit_zero := rfl
  normUnit_mul := by subsingleton
  normUnit_coe_units := by subsingleton
  gcd_dvd_left _ _ := ⟨unit, by subsingleton⟩
  gcd_dvd_right _ _ := ⟨unit, by subsingleton⟩
  dvd_gcd {_ _} _ _ _ := ⟨unit, by subsingleton⟩
  gcd_mul_lcm _ _ := ⟨1, by subsingleton⟩
  lcm_zero_left := by subsingleton
  lcm_zero_right := by subsingleton
  normalize_gcd := by subsingleton
  normalize_lcm := by subsingleton
/-
**PUnit.normalizedGCDMonoid** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：normalizedGCDMonoid : NormalizedGCDMonoid PUnit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance normalizedGCDMonoid : NormalizedGCDMonoid PUnit := inferInstance

@[simp]
/-
**PUnit.gcd_eq** 是 Mathlib 中的一个定理，位于命名空间 `PUnit`。
形式化陈述：gcd_eq {x y : PUnit} : gcd x y = unit
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gcd_eq {x y : PUnit} : gcd x y = unit :=
  rfl

@[simp]
/-
**PUnit.lcm_eq** 是 Mathlib 中的一个定理，位于命名空间 `PUnit`。
形式化陈述：lcm_eq {x y : PUnit} : lcm x y = unit
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lcm_eq {x y : PUnit} : lcm x y = unit :=
  rfl

@[simp]
/-
**PUnit.norm_unit_eq** 是 Mathlib 中的一个定理，位于命名空间 `PUnit`。
形式化陈述：norm_unit_eq {x : PUnit} : normUnit x = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_unit_eq {x : PUnit} : normUnit x = 1 :=
  rfl

end PUnit

