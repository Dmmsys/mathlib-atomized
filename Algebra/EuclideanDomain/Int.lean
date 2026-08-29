/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.EuclideanDomain.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Instances for Euclidean domains

* `Int.euclideanDomain`: shows that `ℤ` is a Euclidean domain.
-/

public section

/--
Instance `Int.euclideanDomain` / 实例 `Int.euclideanDomain`

English:
instance Int.euclideanDomain
  signature: : EuclideanDomain Int
  body: { (inferInstance : CommRing Int), (inferInstance : Nontrivial Int) with
    quotient := (· / ·), quotient_zero := Int.ediv_zero, remainder := (· % ·),
    quotient_mul_add_remainder_eq := Int.mul_ediv_add_emod,
    r := fun a b => a.natAbs < b.natAbs,
    r_wellFounded := (measure natAbs).wf
remainder_lt := fun a b b0 => Int.ofNat_lt.1 by
      rw [Int.natAbs_of_nonneg (Int.emod_nonneg _ b0)]; rw [← Int.abs_eq_natAbs]
      exact Int.emod_lt_abs _ b0
    mul_left_not_lt := fun a b b0 =>
not_lt_of_ge by
        rw [← mul_one a.natAbs]; rw [Int.natAbs_mul]
        rw [← Int.natAbs_pos] at b0
        exact Nat.mul_le_mul_left _ b0 }

中文:
实例 整数.euclideanDomain
  签名: : 欧几里得整环 整数
  定义体: { (inferInstance : CommRing Int), (inferInstance : Nontrivial Int) with
    quotient := (· / ·), quotient_zero := Int.ediv_zero, remainder := (· % ·),
    quotient_mul_add_remainder_eq := Int.mul_ediv_add_emod,
    r := fun a b => a.natAbs < b.natAbs,
    r_wellFounded := (measure natAbs).wf
remainder_lt := fun a b b0 => Int.ofNat_lt.1 by
      rw [Int.natAbs_of_nonneg (Int.emod_nonneg _ b0)]; rw [← Int.abs_eq_natAbs]
      exact Int.emod_lt_abs _ b0
    mul_left_not_lt := fun a b b0 =>
not_lt_of_ge by
        rw [← mul_one a.natAbs]; rw [Int.natAbs_mul]
        rw [← Int.natAbs_pos] at b0
        exact Nat.mul_le_mul_left _ b0 }

Depends on / 依赖: CommRing, Int.abs_eq_natAbs, Int.ediv_zero, Int.emod_lt_abs, Int.emod_nonneg, Int.mul_ediv_add_emod, Int.natAbs_of_nonneg, Int.ofNat_lt, Nontrivial, a.natAbs, abs_eq_natAbs, b.natAbs, ediv_zero, emod_lt_abs, emod_nonneg, measure, mul_ediv_add_emod, mul_left_not_lt, mul_one, natAbs
-/
instance Int.euclideanDomain : EuclideanDomain Int :=
  { (inferInstance : CommRing Int), (inferInstance : Nontrivial Int) with
    quotient := (· / ·), quotient_zero := Int.ediv_zero, remainder := (· % ·),
    quotient_mul_add_remainder_eq := Int.mul_ediv_add_emod,
    r := fun a b => a.natAbs < b.natAbs,
    r_wellFounded := (measure natAbs).wf
remainder_lt := fun a b b0 => Int.ofNat_lt.1 by
      rw [Int.natAbs_of_nonneg (Int.emod_nonneg _ b0)]; rw [← Int.abs_eq_natAbs]
      exact Int.emod_lt_abs _ b0
    mul_left_not_lt := fun a b b0 =>
not_lt_of_ge by
        rw [← mul_one a.natAbs]; rw [Int.natAbs_mul]
        rw [← Int.natAbs_pos] at b0
        exact Nat.mul_le_mul_left _ b0 }
