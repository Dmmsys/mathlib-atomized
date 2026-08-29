/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Topology.Instances.Int

/-! # ℤ as a normed group -/

public section

open NNReal

variable {α : Type*}
namespace Int

/--
Instance `instNormedAddCommGroup` / 实例 `instNormedAddCommGroup`

English:
instance instNormedAddCommGroup
  signature: : NormedAddCommGroup Int where
  body: ‖(n : Real)‖
  dist_eq m n := by
    simp only [dist_eq, norm, cast_add, cast_neg]
    rw [abs_sub_comm]; rw [neg_add_eq_sub]

@[norm_cast]

中文:
实例 instNormedAddCommGroup
  签名: : NormedAddCommGroup 整数 where
  定义体: ‖(n : Real)‖
  dist_eq m n := by
    simp only [dist_eq, norm, cast_add, cast_neg]
    rw [abs_sub_comm]; rw [neg_add_eq_sub]

@[norm_cast]
-/
instance instNormedAddCommGroup : NormedAddCommGroup Int where
  norm n := ‖(n : Real)‖
  dist_eq m n := by
    simp only [dist_eq, norm, cast_add, cast_neg]
    rw [abs_sub_comm]; rw [neg_add_eq_sub]

@[norm_cast]
/--
theorem `norm_cast_real` / 定理 `norm_cast_real`

English:
theorem norm_cast_real
  given: (m : Int)
  statement: ‖(m : Real)‖ = ‖m‖
  proof: rfl

中文:
定理 norm_cast_real
  条件: (m : 整数)
  结论: ‖(m : 实数)‖ = ‖m‖
  证明: rfl
-/
theorem norm_cast_real (m : Int) : ‖(m : Real)‖ = ‖m‖ :=
  rfl

/--
theorem `norm_eq_abs` / 定理 `norm_eq_abs`

English:
theorem norm_eq_abs
  given: (n : Int)
  statement: ‖n‖ = |(n : Real)|
  proof: rfl

中文:
定理 norm_eq_abs
  条件: (n : 整数)
  结论: ‖n‖ = |(n : 实数)|
  证明: rfl
-/
theorem norm_eq_abs (n : Int) : ‖n‖ = |(n : Real)| :=
  rfl

/--
theorem `norm_natCast` / 定理 `norm_natCast`

English:
theorem norm_natCast
  given: (n : Nat)
  statement: ‖(n : Int)‖ = n
  proof: by simp [Int.norm_eq_abs]

中文:
定理 norm_natCast
  条件: (n : 自然数)
  结论: ‖(n : 整数)‖ = n
  证明: by simp [Int.norm_eq_abs]

Depends on / 依赖: Int.norm_eq_abs, norm_eq_abs
-/
theorem norm_natCast (n : Nat) : ‖(n : Int)‖ = n := by simp [Int.norm_eq_abs]

/--
theorem `_root_.NNReal.natCast_natAbs` / 定理 `_root_.NNReal.natCast_natAbs`

English:
theorem _root_.NNReal.natCast_natAbs
  given: (n : Int)
  statement: (n.natAbs : Real>=0) = ‖n‖₊
  proof: NNReal.eq
    calc
      ((n.natAbs : Real>=0) : Real) = (n.natAbs : Int) := by simp only [Int.cast_natCast, NNReal.coe_natCast]
      _ = |(n : Real)| := by simp only [Int.natCast_natAbs, Int.cast_abs]
      _ = ‖n‖ := (norm_eq_abs n).symm

中文:
定理 _root_.NNReal.natCast_natAbs
  条件: (n : 整数)
  结论: (n.natAbs : 实数>=0) = ‖n‖₊
  证明: NNReal.eq
    calc
      ((n.natAbs : Real>=0) : Real) = (n.natAbs : Int) := by simp only [Int.cast_natCast, NNReal.coe_natCast]
      _ = |(n : Real)| := by simp only [Int.natCast_natAbs, Int.cast_abs]
      _ = ‖n‖ := (norm_eq_abs n).symm

Depends on / 依赖: Int.cast_abs, Int.cast_natCast, Int.natCast_natAbs, NNReal, NNReal.coe_natCast, NNReal.eq, cast_abs, cast_natCast, coe_natCast, n.natAbs, natAbs, natCast_natAbs, norm_eq_abs
-/
theorem _root_.NNReal.natCast_natAbs (n : Int) : (n.natAbs : Real>=0) = ‖n‖₊ :=
NNReal.eq
    calc
      ((n.natAbs : Real>=0) : Real) = (n.natAbs : Int) := by simp only [Int.cast_natCast, NNReal.coe_natCast]
      _ = |(n : Real)| := by simp only [Int.natCast_natAbs, Int.cast_abs]
      _ = ‖n‖ := (norm_eq_abs n).symm

/--
theorem `abs_le_floor_nnreal_iff` / 定理 `abs_le_floor_nnreal_iff`

English:
theorem abs_le_floor_nnreal_iff
  given: (z : Int) (c : Real>=0)
  statement: |z| <= ⌊c⌋₊ ↔ ‖z‖₊ <= c
  proof: by
  rw [Int.abs_eq_natAbs]; rw [Int.ofNat_le]; rw [Nat.le_floor_iff zero_le]; rw [NNReal.natCast_natAbs z]

中文:
定理 abs_le_floor_nnreal_iff
  条件: (z : 整数) (c : 实数>=0)
  结论: |z| <= ⌊c⌋₊ ↔ ‖z‖₊ <= c
  证明: by
  rw [Int.abs_eq_natAbs]; rw [Int.ofNat_le]; rw [Nat.le_floor_iff zero_le]; rw [NNReal.natCast_natAbs z]

Depends on / 依赖: Int.abs_eq_natAbs, Int.ofNat_le, NNReal, NNReal.natCast_natAbs, Nat.le_floor_iff, abs_eq_natAbs, le_floor_iff, natCast_natAbs, ofNat_le, zero_le
-/
theorem abs_le_floor_nnreal_iff (z : Int) (c : Real>=0) : |z| <= ⌊c⌋₊ ↔ ‖z‖₊ <= c := by
  rw [Int.abs_eq_natAbs]; rw [Int.ofNat_le]; rw [Nat.le_floor_iff zero_le]; rw [NNReal.natCast_natAbs z]

end Int

-- Now that we've installed the norm on `ℤ`,
-- we can state some lemmas about `zsmul`.
section

variable [SeminormedCommGroup α]

@[to_additive norm_zsmul_le]
/--
theorem `norm_zpow_le_mul_norm` / 定理 `norm_zpow_le_mul_norm`

English:
theorem norm_zpow_le_mul_norm
  given: (n : Int) (a : α)
  statement: ‖a ^ n‖ <= ‖n‖ * ‖a‖
  proof: by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩ <;> simpa [Int.norm_natCast] using norm_pow_le_mul_norm

@[to_additive nnnorm_zsmul_le]

中文:
定理 norm_zpow_le_mul_norm
  条件: (n : 整数) (a : α)
  结论: ‖a ^ n‖ <= ‖n‖ * ‖a‖
  证明: by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩ <;> simpa [Int.norm_natCast] using norm_pow_le_mul_norm

@[to_additive nnnorm_zsmul_le]

Depends on / 依赖: Int.norm_natCast, eq_nat_or_neg, n.eq_nat_or_neg, norm_natCast, norm_pow_le_mul_norm
-/
theorem norm_zpow_le_mul_norm (n : Int) (a : α) : ‖a ^ n‖ <= ‖n‖ * ‖a‖ := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩ <;> simpa [Int.norm_natCast] using norm_pow_le_mul_norm

@[to_additive nnnorm_zsmul_le]
/--
theorem `nnnorm_zpow_le_mul_norm` / 定理 `nnnorm_zpow_le_mul_norm`

English:
theorem nnnorm_zpow_le_mul_norm
  given: (n : Int) (a : α)
  statement: ‖a ^ n‖₊ <= ‖n‖₊ * ‖a‖₊
  proof: by
  simpa only [← NNReal.coe_le_coe, NNReal.coe_mul] using! norm_zpow_le_mul_norm n a

中文:
定理 nnnorm_zpow_le_mul_norm
  条件: (n : 整数) (a : α)
  结论: ‖a ^ n‖₊ <= ‖n‖₊ * ‖a‖₊
  证明: by
  simpa only [← NNReal.coe_le_coe, NNReal.coe_mul] using! norm_zpow_le_mul_norm n a

Depends on / 依赖: NNReal, NNReal.coe_le_coe, NNReal.coe_mul, coe_le_coe, coe_mul, norm_zpow_le_mul_norm
-/
theorem nnnorm_zpow_le_mul_norm (n : Int) (a : α) : ‖a ^ n‖₊ <= ‖n‖₊ * ‖a‖₊ := by
  simpa only [← NNReal.coe_le_coe, NNReal.coe_mul] using! norm_zpow_le_mul_norm n a

end
