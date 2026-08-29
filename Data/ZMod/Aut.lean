/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Ring.AddAut
public import Mathlib.Data.ZMod.Basic

/-!
# Automorphism Group of `ZMod`.
-/

@[expose] public section

assert_not_exists Field TwoSidedIdeal

namespace ZMod

variable (n : Nat)

set_option backward.isDefEq.respectTransparency.types false in
/-- The automorphism group of `ZMod n` is isomorphic to the group of units of `ZMod n`. -/
@[simps]
/--
Definition of `AddAutEquivUnits` / `AddAutEquivUnits` 的定义

English:
definition AddAutEquivUnits
  signature: : AddAut (ZMod n) ≃+ Additive (ZMod n)ˣ
  body: have h (f : AddAut (ZMod n)) (x : ZMod n) : f 1 * x = f x := by
    rw [mul_comm]; rw [← x.intCast_zmod_cast]; rw [← zsmul_eq_mul]; rw [← map_zsmul]; rw [zsmul_one]
  { toFun f := .ofMul <| Units.mkOfMulEqOne (f 1) ((-f) 1) ((h f _).trans (f.apply_neg_self _ _))
    invFun x := AddAut.mulLeft x.toMu

中文:
定义 AddAutEquivUnits
  签名: : AddAut (ZMod n) ≃+ 加性 (ZMod n)ˣ
  定义体: have h (f : AddAut (ZMod n)) (x : ZMod n) : f 1 * x = f x := by
    rw [mul_comm]; rw [← x.intCast_zmod_cast]; rw [← zsmul_eq_mul]; rw [← map_zsmul]; rw [zsmul_one]
  { toFun f := .ofMul <| Units.mkOfMulEqOne (f 1) ((-f) 1) ((h f _).trans (f.apply_neg_self _ _))
    invFun x := AddAut.mulLeft x.toMu

Depends on / 依赖: AddAut, AddAut.mulLeft, Additi, Additive, Additive.toMul_symm_eq, DFunLike, DFunLike.ext_iff, Equiv.symm_apply_eq, Units.ext_iff, Units.mkOfMulEqOne, Units.smul_def, apply_neg_self, ext_iff, f.apply_neg_self, intCast_zmod_cast, invFun, left_inv, map_add, map_zsmul, mkOfMulEqOne
-/
def AddAutEquivUnits : AddAut (ZMod n) ≃+ Additive (ZMod n)ˣ :=
  have h (f : AddAut (ZMod n)) (x : ZMod n) : f 1 * x = f x := by
    rw [mul_comm]; rw [← x.intCast_zmod_cast]; rw [← zsmul_eq_mul]; rw [← map_zsmul]; rw [zsmul_one]
  { toFun f := .ofMul <| Units.mkOfMulEqOne (f 1) ((-f) 1) ((h f _).trans (f.apply_neg_self _ _))
    invFun x := AddAut.mulLeft x.toMul
    left_inv g := by simp [DFunLike.ext_iff, Units.smul_def, h]
    right_inv x := by simp [← Additive.toMul_symm_eq, Equiv.symm_apply_eq,
      Units.ext_iff, Units.smul_def, -toMul_smul]
    map_add' f g := by simp [← Additive.toMul_symm_eq, Equiv.symm_apply_eq, Units.ext_iff, h] }

end ZMod
