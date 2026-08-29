/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Rat
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Module.Defs

/-!
# Monotonicity of the action by rational numbers
-/

public section

variable {α : Type*}

/--
Instance `PosSMulMono.nnrat_of_rat` / 实例 `PosSMulMono.nnrat_of_rat`

English:
instance PosSMulMono.nnrat_of_rat
  signature: [Preorder α] [MulAction Rat α] [MulAction Rat>=0 α]
  body: by
    rw [← NNRat.cast_smul_eq_nnqsmul Rat]; rw [← NNRat.cast_smul_eq_nnqsmul Rat]
    exact smul_le_smul_of_nonneg_left (α := Rat) ha hq

中文:
实例 正标量乘递增.nnrat_of_rat
  签名: [预序 α] [乘法作用 有理数 α] [乘法作用 有理数>=0 α]
  定义体: by
    rw [← NNRat.cast_smul_eq_nnqsmul Rat]; rw [← NNRat.cast_smul_eq_nnqsmul Rat]
    exact smul_le_smul_of_nonneg_left (α := Rat) ha hq

Depends on / 依赖: NNRat.cast_smul_eq_nnqsmul, cast_smul_eq_nnqsmul, smul_le_smul_of_nonneg_left
-/
instance PosSMulMono.nnrat_of_rat [Preorder α] [MulAction Rat α] [MulAction Rat>=0 α]
    [IsScalarTower Rat>=0 Rat α] [PosSMulMono Rat α] :
    PosSMulMono Rat>=0 α where
  smul_le_smul_of_nonneg_left _q hq _a₁ _a₂ ha := by
    rw [← NNRat.cast_smul_eq_nnqsmul Rat]; rw [← NNRat.cast_smul_eq_nnqsmul Rat]
    exact smul_le_smul_of_nonneg_left (α := Rat) ha hq

/--
Instance `PosSMulStrictMono.nnrat_of_rat` / 实例 `PosSMulStrictMono.nnrat_of_rat`

English:
instance PosSMulStrictMono.nnrat_of_rat
  signature: [Preorder α] [MulAction Rat>=0 α] [MulAction Rat α]
  body: by
    rw [← NNRat.cast_smul_eq_nnqsmul Rat]; rw [← NNRat.cast_smul_eq_nnqsmul Rat]
    exact smul_lt_smul_of_pos_left (α := Rat) ha hq

中文:
实例 正标量乘严格递增.nnrat_of_rat
  签名: [预序 α] [乘法作用 有理数>=0 α] [乘法作用 有理数 α]
  定义体: by
    rw [← NNRat.cast_smul_eq_nnqsmul Rat]; rw [← NNRat.cast_smul_eq_nnqsmul Rat]
    exact smul_lt_smul_of_pos_left (α := Rat) ha hq

Depends on / 依赖: NNRat.cast_smul_eq_nnqsmul, cast_smul_eq_nnqsmul, smul_lt_smul_of_pos_left
-/
instance PosSMulStrictMono.nnrat_of_rat [Preorder α] [MulAction Rat>=0 α] [MulAction Rat α]
    [IsScalarTower Rat>=0 Rat α] [PosSMulStrictMono Rat α] :
    PosSMulStrictMono Rat>=0 α where
  smul_lt_smul_of_pos_left _q hq _a₁ _a₂ ha := by
    rw [← NNRat.cast_smul_eq_nnqsmul Rat]; rw [← NNRat.cast_smul_eq_nnqsmul Rat]
    exact smul_lt_smul_of_pos_left (α := Rat) ha hq

section LinearOrderedAddCommGroup
variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/--
lemma `abs_nnqsmul` / 引理 `abs_nnqsmul`

English:
lemma abs_nnqsmul
  given: [DistribMulAction Rat>=0 α] [PosSMulMono Rat>=0 α] (q : Rat>=0) (a : α)
  proof: by
  obtain ha | ha := le_total a 0 <;>
    simp [*, abs_of_nonneg, abs_of_nonpos, smul_nonneg, smul_nonpos_of_nonneg_of_nonpos]

中文:
引理 abs_nnqsmul
  条件: [分配乘法作用 有理数>=0 α] [正标量乘递增 有理数>=0 α] (q : 有理数>=0) (a : α)
  证明: by
  obtain ha | ha := le_total a 0 <;>
    simp [*, abs_of_nonneg, abs_of_nonpos, smul_nonneg, smul_nonpos_of_nonneg_of_nonpos]
-/
@[simp] lemma abs_nnqsmul [DistribMulAction Rat>=0 α] [PosSMulMono Rat>=0 α] (q : Rat>=0) (a : α) :
    |q • a| = q • |a| := by
  obtain ha | ha := le_total a 0 <;>
    simp [*, abs_of_nonneg, abs_of_nonpos, smul_nonneg, smul_nonpos_of_nonneg_of_nonpos]

end LinearOrderedAddCommGroup

section LinearOrderedSemifield
variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]

/--
Instance `LinearOrderedSemifield.toPosSMulStrictMono_rat` / 实例 `LinearOrderedSemifield.toPosSMulStrictMono_rat`

English:
instance LinearOrderedSemifield.toPosSMulStrictMono_rat
  signature: : PosSMulStrictMono Rat>=0 α where
  body: by
rw [NNRat.smul_def]; rw [NNRat.smul_def]; exact mul_lt_mul_of_pos_left hab NNRat.cast_pos.2 hq

中文:
实例 LinearOrderedSemifield.toPosSMulStrictMono_rat
  签名: : 正标量乘严格递增 有理数>=0 α where
  定义体: by
rw [NNRat.smul_def]; rw [NNRat.smul_def]; exact mul_lt_mul_of_pos_left hab NNRat.cast_pos.2 hq

Depends on / 依赖: NNRat.cast_pos, NNRat.smul_def, cast_pos, mul_lt_mul_of_pos_left, smul_def
-/
instance LinearOrderedSemifield.toPosSMulStrictMono_rat : PosSMulStrictMono Rat>=0 α where
  smul_lt_smul_of_pos_left q hq a b hab := by
rw [NNRat.smul_def]; rw [NNRat.smul_def]; exact mul_lt_mul_of_pos_left hab NNRat.cast_pos.2 hq

end LinearOrderedSemifield

section LinearOrderedField
variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/--
Instance `LinearOrderedField.toPosSMulStrictMono_rat` / 实例 `LinearOrderedField.toPosSMulStrictMono_rat`

English:
instance LinearOrderedField.toPosSMulStrictMono_rat
  signature: : PosSMulStrictMono Rat α where
  body: by
rw [Rat.smul_def]; rw [Rat.smul_def]; exact mul_lt_mul_of_pos_left hab Rat.cast_pos.2 hq

中文:
实例 LinearOrderedField.toPosSMulStrictMono_rat
  签名: : 正标量乘严格递增 有理数 α where
  定义体: by
rw [Rat.smul_def]; rw [Rat.smul_def]; exact mul_lt_mul_of_pos_left hab Rat.cast_pos.2 hq

Depends on / 依赖: Rat.cast_pos, Rat.smul_def, cast_pos, mul_lt_mul_of_pos_left, smul_def
-/
instance LinearOrderedField.toPosSMulStrictMono_rat : PosSMulStrictMono Rat α where
  smul_lt_smul_of_pos_left q hq a b hab := by
rw [Rat.smul_def]; rw [Rat.smul_def]; exact mul_lt_mul_of_pos_left hab Rat.cast_pos.2 hq

end LinearOrderedField
