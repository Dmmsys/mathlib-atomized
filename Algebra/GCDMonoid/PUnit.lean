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
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StrongNormalizedGCDMonoid PUnit
  body: unit
  lcm _ _ := unit
  normUnit _ := 1
  normUnit_zero := rfl
  normUnit_mul := by subsingleton
  normUnit_coe_units := by subsingleton
  gcd_dvd_left _ _ := ⟨unit, by subsingleton⟩
  gcd_dvd_right _ _ := ⟨unit, by subsingleton⟩
  dvd_gcd {_ _} _ _ _ := ⟨unit, by subsingleton⟩
  gcd_mul_lcm _ _ :=

中文:
实例 :
  签名: StrongNormalizedGCDMonoid PUnit
  定义体: unit
  lcm _ _ := unit
  normUnit _ := 1
  normUnit_zero := rfl
  normUnit_mul := by subsingleton
  normUnit_coe_units := by subsingleton
  gcd_dvd_left _ _ := ⟨unit, by subsingleton⟩
  gcd_dvd_right _ _ := ⟨unit, by subsingleton⟩
  dvd_gcd {_ _} _ _ _ := ⟨unit, by subsingleton⟩
  gcd_mul_lcm _ _ :=
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

/--
Instance `normalizedGCDMonoid` / 实例 `normalizedGCDMonoid`

English:
instance normalizedGCDMonoid
  signature: : NormalizedGCDMonoid PUnit
  body: inferInstance

@[simp]

中文:
实例 normalizedGCDMonoid
  签名: : NormalizedGCDMonoid PUnit
  定义体: inferInstance

@[simp]
-/
instance normalizedGCDMonoid : NormalizedGCDMonoid PUnit := inferInstance

@[simp]
/--
theorem `gcd_eq` / 定理 `gcd_eq`

English:
theorem gcd_eq
  given: {x y : PUnit}
  statement: gcd x y = unit
  proof: rfl

@[simp]

中文:
定理 gcd_eq
  条件: {x y : PUnit}
  结论: gcd x y = unit
  证明: rfl

@[simp]
-/
theorem gcd_eq {x y : PUnit} : gcd x y = unit :=
  rfl

@[simp]
/--
theorem `lcm_eq` / 定理 `lcm_eq`

English:
theorem lcm_eq
  given: {x y : PUnit}
  statement: lcm x y = unit
  proof: rfl

@[simp]

中文:
定理 lcm_eq
  条件: {x y : PUnit}
  结论: lcm x y = unit
  证明: rfl

@[simp]
-/
theorem lcm_eq {x y : PUnit} : lcm x y = unit :=
  rfl

@[simp]
/--
theorem `norm_unit_eq` / 定理 `norm_unit_eq`

English:
theorem norm_unit_eq
  given: {x : PUnit}
  statement: normUnit x = 1
  proof: rfl

中文:
定理 norm_unit_eq
  条件: {x : PUnit}
  结论: normUnit x = 1
  证明: rfl
-/
theorem norm_unit_eq {x : PUnit} : normUnit x = 1 :=
  rfl

end PUnit
