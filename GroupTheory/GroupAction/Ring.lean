/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Ring.Defs

/-!
# Commutativity and associativity of action of integers on rings

This file proves that `ℕ` and `ℤ` act commutatively and associatively on (semi)rings.

## TODO

Those instances are in their own file only because they require much less imports than any existing
file they could go to. This is unfortunate and should be fixed by reorganising files.
-/

public section

open scoped Int

variable {R : Type*}

/--
Instance `NonUnitalNonAssocSemiring.toDistribSMul` / 实例 `NonUnitalNonAssocSemiring.toDistribSMul`

English:
instance NonUnitalNonAssocSemiring.toDistribSMul
  signature: [NonUnitalNonAssocSemiring R]
  body: mul_add

中文:
实例 NonUnitalNonAssocSemiring.toDistribSMul
  签名: [NonUnitalNonAssocSemiring R]
  定义体: mul_add

Depends on / 依赖: mul_add
-/
instance NonUnitalNonAssocSemiring.toDistribSMul [NonUnitalNonAssocSemiring R] :
    DistribSMul R R where smul_add := mul_add

/--
Instance `NonUnitalNonAssocSemiring.nat_isScalarTower` / 实例 `NonUnitalNonAssocSemiring.nat_isScalarTower`

English:
instance NonUnitalNonAssocSemiring.nat_isScalarTower
  signature: [NonUnitalNonAssocSemiring R]
  body: by
    induction n with
    | zero => simp
    | succ n ih => simp_rw [succ_nsmul, ← ih, smul_eq_mul, add_mul]

中文:
实例 NonUnitalNonAssocSemiring.nat_isScalarTower
  签名: [NonUnitalNonAssocSemiring R]
  定义体: by
    induction n with
    | zero => simp
    | succ n ih => simp_rw [succ_nsmul, ← ih, smul_eq_mul, add_mul]

Depends on / 依赖: add_mul, simp_rw, smul_eq_mul, succ_nsmul
-/
instance NonUnitalNonAssocSemiring.nat_isScalarTower [NonUnitalNonAssocSemiring R] :
    IsScalarTower Nat R R where
  smul_assoc n x y := by
    induction n with
    | zero => simp
    | succ n ih => simp_rw [succ_nsmul, ← ih, smul_eq_mul, add_mul]

/--
Instance `NonUnitalNonAssocRing.int_isScalarTower` / 实例 `NonUnitalNonAssocRing.int_isScalarTower`

English:
instance NonUnitalNonAssocRing.int_isScalarTower
  signature: [NonUnitalNonAssocRing R]
  body: match n with
    | (n : Nat) => by simp_rw [natCast_zsmul, smul_assoc]
    | -[n+1] => by simp_rw [negSucc_zsmul, smul_eq_mul, neg_mul, smul_mul_assoc]

中文:
实例 NonUnitalNonAssocRing.int_isScalarTower
  签名: [NonUnitalNonAssocRing R]
  定义体: match n with
    | (n : Nat) => by simp_rw [natCast_zsmul, smul_assoc]
    | -[n+1] => by simp_rw [negSucc_zsmul, smul_eq_mul, neg_mul, smul_mul_assoc]

Depends on / 依赖: natCast_zsmul, negSucc_zsmul, neg_mul, simp_rw, smul_assoc, smul_eq_mul, smul_mul_assoc
-/
instance NonUnitalNonAssocRing.int_isScalarTower [NonUnitalNonAssocRing R] :
    IsScalarTower Int R R where
  smul_assoc n x y :=
    match n with
    | (n : Nat) => by simp_rw [natCast_zsmul, smul_assoc]
    | -[n+1] => by simp_rw [negSucc_zsmul, smul_eq_mul, neg_mul, smul_mul_assoc]
