/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Lemmas about quotients in characteristic zero
-/

public section


variable {R : Type*} [DivisionRing R] [CharZero R] {p : R}

namespace AddSubgroup

/--
theorem `zsmul_mem_zmultiples_iff_exists_sub_div` / 定理 `zsmul_mem_zmultiples_iff_exists_sub_div`

English:
theorem zsmul_mem_zmultiples_iff_exists_sub_div
  given: {r : R} {z : Int} (hz : z != 0)
  proof: by
  rw [AddSubgroup.mem_zmultiples_iff]
  simp_rw [AddSubgroup.mem_zmultiples_iff, div_eq_mul_inv, ← smul_mul_assoc, eq_sub_iff_add_eq]
  have hz' : (z : R) != 0 := Int.cast_ne_zero.mpr hz
  conv_rhs => simp +singlePass only [← (mul_right_injective₀ hz').eq_iff]
  simp_rw [← zsmul_eq_mul, smul_add,

中文:
定理 zsmul_mem_zmultiples_iff_存在_sub_div
  条件: {r : R} {z : 整数} (hz : z != 0)
  证明: by
  rw [AddSubgroup.mem_zmultiples_iff]
  simp_rw [AddSubgroup.mem_zmultiples_iff, div_eq_mul_inv, ← smul_mul_assoc, eq_sub_iff_add_eq]
  have hz' : (z : R) != 0 := Int.cast_ne_zero.mpr hz
  conv_rhs => simp +singlePass only [← (mul_right_injective₀ hz').eq_iff]
  simp_rw [← zsmul_eq_mul, smul_add,

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_zmultiples_iff, Int.cast_ne_zero.mpr, Int.ofNa, add_smul, cast_ne_zero, conv_rhs, div_eq_mul_inv, eq_iff, eq_sub_iff_add_eq, mem_zmultiples_iff, mul_one, mul_smul_comm, natCast_zsmul, simp_rw, singlePass, smul_add, smul_mul_assoc, smul_smul, zsmul_eq_mul
-/
theorem zsmul_mem_zmultiples_iff_exists_sub_div {r : R} {z : Int} (hz : z != 0) :
    z • r in AddSubgroup.zmultiples p ↔
      exists k : Fin z.natAbs, r - (k : Nat) • (p / z : R) in AddSubgroup.zmultiples p := by
  rw [AddSubgroup.mem_zmultiples_iff]
  simp_rw [AddSubgroup.mem_zmultiples_iff, div_eq_mul_inv, ← smul_mul_assoc, eq_sub_iff_add_eq]
  have hz' : (z : R) != 0 := Int.cast_ne_zero.mpr hz
  conv_rhs => simp +singlePass only [← (mul_right_injective₀ hz').eq_iff]
  simp_rw [← zsmul_eq_mul, smul_add, ← mul_smul_comm, zsmul_eq_mul (z : R)⁻¹, mul_inv_cancel₀ hz',
    mul_one, ← natCast_zsmul, smul_smul, ← add_smul]
  constructor
  · rintro ⟨k, h⟩
    simp_rw [← h]
    refine ⟨⟨(k % z).toNat, ?_⟩, k / z, ?_⟩
    · rw [← Int.ofNat_lt, Int.toNat_of_nonneg (Int.emod_nonneg _ hz)]
      exact (Int.emod_lt_abs _ hz).trans_eq (Int.abs_eq_natAbs _)
    rw [Fin.val_mk]; rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hz)]
    nth_rewrite 3 [← Int.mul_ediv_add_emod k z]
    rfl
  · rintro ⟨k, n, h⟩
    exact ⟨_, h⟩

/--
theorem `nsmul_mem_zmultiples_iff_exists_sub_div` / 定理 `nsmul_mem_zmultiples_iff_exists_sub_div`

English:
theorem nsmul_mem_zmultiples_iff_exists_sub_div
  given: {r : R} {n : Nat} (hn : n != 0)
  proof: by
  rw [← natCast_zsmul r]; rw [zsmul_mem_zmultiples_iff_exists_sub_div (Int.natCast_ne_zero.mpr hn)]; rw [Int.cast_natCast]
  rfl

中文:
定理 nsmul_mem_zmultiples_iff_存在_sub_div
  条件: {r : R} {n : 自然数} (hn : n != 0)
  证明: by
  rw [← natCast_zsmul r]; rw [zsmul_mem_zmultiples_iff_exists_sub_div (Int.natCast_ne_zero.mpr hn)]; rw [Int.cast_natCast]
  rfl

Depends on / 依赖: Int.cast_natCast, Int.natCast_ne_zero.mpr, cast_natCast, natCast_ne_zero, natCast_zsmul, zsmul_mem_zmultiples_iff_exists_sub_div
-/
theorem nsmul_mem_zmultiples_iff_exists_sub_div {r : R} {n : Nat} (hn : n != 0) :
    n • r in AddSubgroup.zmultiples p ↔
      exists k : Fin n, r - (k : Nat) • (p / n : R) in AddSubgroup.zmultiples p := by
  rw [← natCast_zsmul r]; rw [zsmul_mem_zmultiples_iff_exists_sub_div (Int.natCast_ne_zero.mpr hn)]; rw [Int.cast_natCast]
  rfl

end AddSubgroup

namespace QuotientAddGroup

/--
theorem `zmultiples_zsmul_eq_zsmul_iff` / 定理 `zmultiples_zsmul_eq_zsmul_iff`

English:
theorem zmultiples_zsmul_eq_zsmul_iff
  given: {ψ θ : R ⧸ AddSubgroup.zmultiples p} {z : Int} (hz : z != 0)
  proof: by
  induction ψ using Quotient.inductionOn
  induction θ using Quotient.inductionOn
  simp_rw [← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_add,
    QuotientAddGroup.eq_iff_sub_mem, ← smul_sub, ← sub_sub]
  exact AddSubgroup.zsmul_mem_zmultiples_iff_exists_sub_div hz

中文:
定理 zmultiples_zsmul_eq_zsmul_iff
  条件: {ψ θ : R ⧸ 加法子群.zmultiples p} {z : 整数} (hz : z != 0)
  证明: by
  induction ψ using Quotient.inductionOn
  induction θ using Quotient.inductionOn
  simp_rw [← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_add,
    QuotientAddGroup.eq_iff_sub_mem, ← smul_sub, ← sub_sub]
  exact AddSubgroup.zsmul_mem_zmultiples_iff_exists_sub_div hz

Depends on / 依赖: AddSubgroup, AddSubgroup.zsmul_mem_zmultiples_iff_exists_sub_div, Quotient, Quotient.inductionOn, QuotientAddGroup, QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.mk_add, QuotientAddGroup.mk_zsmul, eq_iff_sub_mem, inductionOn, mk_add, mk_zsmul, simp_rw, smul_sub, sub_sub, zsmul_mem_zmultiples_iff_exists_sub_div
-/
theorem zmultiples_zsmul_eq_zsmul_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {z : Int} (hz : z != 0) :
    z • ψ = z • θ ↔ exists k : Fin z.natAbs, ψ = θ + ((k : Nat) • (p / z) : R) := by
  induction ψ using Quotient.inductionOn
  induction θ using Quotient.inductionOn
  simp_rw [← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_add,
    QuotientAddGroup.eq_iff_sub_mem, ← smul_sub, ← sub_sub]
  exact AddSubgroup.zsmul_mem_zmultiples_iff_exists_sub_div hz

/--
theorem `zmultiples_nsmul_eq_nsmul_iff` / 定理 `zmultiples_nsmul_eq_nsmul_iff`

English:
theorem zmultiples_nsmul_eq_nsmul_iff
  given: {ψ θ : R ⧸ AddSubgroup.zmultiples p} {n : Nat} (hz : n != 0)
  proof: by
  rw [← natCast_zsmul ψ]; rw [← natCast_zsmul θ]; rw [zmultiples_zsmul_eq_zsmul_iff (Int.natCast_ne_zero.mpr hz)]; rw [Int.cast_natCast]
  rfl

中文:
定理 zmultiples_nsmul_eq_nsmul_iff
  条件: {ψ θ : R ⧸ 加法子群.zmultiples p} {n : 自然数} (hz : n != 0)
  证明: by
  rw [← natCast_zsmul ψ]; rw [← natCast_zsmul θ]; rw [zmultiples_zsmul_eq_zsmul_iff (Int.natCast_ne_zero.mpr hz)]; rw [Int.cast_natCast]
  rfl

Depends on / 依赖: Int.cast_natCast, Int.natCast_ne_zero.mpr, cast_natCast, natCast_ne_zero, natCast_zsmul, zmultiples_zsmul_eq_zsmul_iff
-/
theorem zmultiples_nsmul_eq_nsmul_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {n : Nat} (hz : n != 0) :
    n • ψ = n • θ ↔ exists k : Fin n, ψ = θ + (k : Nat) • (p / n : R) := by
  rw [← natCast_zsmul ψ]; rw [← natCast_zsmul θ]; rw [zmultiples_zsmul_eq_zsmul_iff (Int.natCast_ne_zero.mpr hz)]; rw [Int.cast_natCast]
  rfl

end QuotientAddGroup
