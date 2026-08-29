/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Cauchy's bound on polynomial roots.

The bound is given by `Polynomial.cauchyBound`, which for `a_n x^n + a_(n-1) x^(n - 1) + ⋯ + a_0` is
`1 + max_(0 ≤ i < n) a_i / a_n`.

The theorem that this gives a bound to polynomial roots is `Polynomial.IsRoot.norm_lt_cauchyBound`.
-/

@[expose] public section

variable {K : Type*} [NormedDivisionRing K]

namespace Polynomial

open Finset NNReal

/--
Definition of `cauchyBound` / `cauchyBound` 的定义

English:
definition cauchyBound
  signature: (p : K[X])
  body: sup (range p.natDegree) (‖p.coeff ·‖₊) / ‖p.leadingCoeff‖₊ + 1

@[simp]

中文:
定义 cauchyBound
  签名: (p : K[X])
  定义体: sup (range p.natDegree) (‖p.coeff ·‖₊) / ‖p.leadingCoeff‖₊ + 1

@[simp]

Depends on / 依赖: leadingCoeff, natDegree, p.coeff, p.leadingCoeff, p.natDegree
-/
noncomputable def cauchyBound (p : K[X]) : Real>=0 :=
  sup (range p.natDegree) (‖p.coeff ·‖₊) / ‖p.leadingCoeff‖₊ + 1

@[simp]
/--
lemma `one_le_cauchyBound` / 引理 `one_le_cauchyBound`

English:
lemma one_le_cauchyBound
  given: (p : K[X])
  statement: 1 <= cauchyBound p
  proof: by
  simp [cauchyBound]

@[simp]

中文:
引理 one_le_cauchyBound
  条件: (p : K[X])
  结论: 1 <= cauchyBound p
  证明: by
  simp [cauchyBound]

@[simp]

Depends on / 依赖: cauchyBound
-/
lemma one_le_cauchyBound (p : K[X]) : 1 <= cauchyBound p := by
  simp [cauchyBound]

@[simp]
/--
lemma `cauchyBound_zero` / 引理 `cauchyBound_zero`

English:
lemma cauchyBound_zero
  statement: cauchyBound (0 : K[X]) = 1
  proof: by
  simp [cauchyBound]

@[simp]

中文:
引理 cauchyBound_zero
  结论: cauchyBound (0 : K[X]) = 1
  证明: by
  simp [cauchyBound]

@[simp]

Depends on / 依赖: cauchyBound
-/
lemma cauchyBound_zero : cauchyBound (0 : K[X]) = 1 := by
  simp [cauchyBound]

@[simp]
/--
lemma `cauchyBound_C` / 引理 `cauchyBound_C`

English:
lemma cauchyBound_C
  given: (x : K)
  statement: cauchyBound (C x) = 1
  proof: by
  simp [cauchyBound]

@[simp]

中文:
引理 cauchyBound_C
  条件: (x : K)
  结论: cauchyBound (C x) = 1
  证明: by
  simp [cauchyBound]

@[simp]

Depends on / 依赖: cauchyBound
-/
lemma cauchyBound_C (x : K) : cauchyBound (C x) = 1 := by
  simp [cauchyBound]

@[simp]
/--
lemma `cauchyBound_one` / 引理 `cauchyBound_one`

English:
lemma cauchyBound_one
  statement: cauchyBound (1 : K[X]) = 1
  proof: cauchyBound_C 1

@[simp]

中文:
引理 cauchyBound_one
  结论: cauchyBound (1 : K[X]) = 1
  证明: cauchyBound_C 1

@[simp]

Depends on / 依赖: cauchyBound_C
-/
lemma cauchyBound_one : cauchyBound (1 : K[X]) = 1 := cauchyBound_C 1

@[simp]
/--
lemma `cauchyBound_X` / 引理 `cauchyBound_X`

English:
lemma cauchyBound_X
  statement: cauchyBound (X : K[X]) = 1
  proof: by
  simp [cauchyBound]

@[simp]

中文:
引理 cauchyBound_X
  结论: cauchyBound (X : K[X]) = 1
  证明: by
  simp [cauchyBound]

@[simp]

Depends on / 依赖: cauchyBound
-/
lemma cauchyBound_X : cauchyBound (X : K[X]) = 1 := by
  simp [cauchyBound]

@[simp]
/--
lemma `cauchyBound_X_add_C` / 引理 `cauchyBound_X_add_C`

English:
lemma cauchyBound_X_add_C
  given: (x : K)
  statement: cauchyBound (X + C x) = ‖x‖₊ + 1
  proof: by
  simp [cauchyBound]

@[simp]

中文:
引理 cauchyBound_X_add_C
  条件: (x : K)
  结论: cauchyBound (X + C x) = ‖x‖₊ + 1
  证明: by
  simp [cauchyBound]

@[simp]

Depends on / 依赖: cauchyBound
-/
lemma cauchyBound_X_add_C (x : K) : cauchyBound (X + C x) = ‖x‖₊ + 1 := by
  simp [cauchyBound]

@[simp]
/--
lemma `cauchyBound_X_sub_C` / 引理 `cauchyBound_X_sub_C`

English:
lemma cauchyBound_X_sub_C
  given: (x : K)
  statement: cauchyBound (X - C x) = ‖x‖₊ + 1
  proof: by
  simp [cauchyBound]

@[simp]

中文:
引理 cauchyBound_X_sub_C
  条件: (x : K)
  结论: cauchyBound (X - C x) = ‖x‖₊ + 1
  证明: by
  simp [cauchyBound]

@[simp]

Depends on / 依赖: cauchyBound
-/
lemma cauchyBound_X_sub_C (x : K) : cauchyBound (X - C x) = ‖x‖₊ + 1 := by
  simp [cauchyBound]

@[simp]
/--
lemma `cauchyBound_smul` / 引理 `cauchyBound_smul`

English:
lemma cauchyBound_smul
  given: {x : K} (hx : x != 0) (p : K[X])
  statement: cauchyBound (x • p) = cauchyBound p
  proof: by
  simp only [cauchyBound, (IsRegular.of_ne_zero hx).left.isSMulRegular,
    natDegree_smul_of_smul_regular, coeff_smul, smul_eq_mul, nnnorm_mul, ← mul_finset_sup,
    leadingCoeff_smul_of_smul_regular, add_left_inj]
  apply mul_div_mul_left
  simpa

中文:
引理 cauchyBound_smul
  条件: {x : K} (hx : x != 0) (p : K[X])
  结论: cauchyBound (x • p) = cauchyBound p
  证明: by
  simp only [cauchyBound, (IsRegular.of_ne_zero hx).left.isSMulRegular,
    natDegree_smul_of_smul_regular, coeff_smul, smul_eq_mul, nnnorm_mul, ← mul_finset_sup,
    leadingCoeff_smul_of_smul_regular, add_left_inj]
  apply mul_div_mul_left
  simpa

Depends on / 依赖: IsRegular, IsRegular.of_ne_zero, add_left_inj, cauchyBound, coeff_smul, isSMulRegular, leadingCoeff_smul_of_smul_regular, left.isSMulRegular, mul_div_mul_left, mul_finset_sup, natDegree_smul_of_smul_regular, nnnorm_mul, of_ne_zero, smul_eq_mul
-/
lemma cauchyBound_smul {x : K} (hx : x != 0) (p : K[X]) : cauchyBound (x • p) = cauchyBound p := by
  simp only [cauchyBound, (IsRegular.of_ne_zero hx).left.isSMulRegular,
    natDegree_smul_of_smul_regular, coeff_smul, smul_eq_mul, nnnorm_mul, ← mul_finset_sup,
    leadingCoeff_smul_of_smul_regular, add_left_inj]
  apply mul_div_mul_left
  simpa

/--
theorem `IsRoot.norm_lt_cauchyBound` / 定理 `IsRoot.norm_lt_cauchyBound`

English:
theorem IsRoot.norm_lt_cauchyBound
  given: {p : K[X]} (hp : p != 0) {a : K} (h : p.IsRoot a)
  proof: by
  rw [IsRoot.def]; rw [eval_eq_sum_range]; rw [range_add_one] at h
  simp only [mem_range, lt_self_iff_false, not_false_eq_true, sum_insert, coeff_natDegree,
    add_eq_zero_iff_eq_neg] at h
  apply_fun nnnorm at h
  simp only [nnnorm_mul, nnnorm_pow, nnnorm_neg] at h
  suffices ‖a‖₊ ^ p.natDegree <= (cauchyBound p - 1) * ∑ x in range p.natDegree, ‖a‖₊ ^ x by
    rcases eq_or_ne ‖a‖₊ 1 with ha | ha
    · simp only [ha, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, gt_iff_lt] at this ⊢
      apply lt_of_le_of_ne (by simp)
      intro nh
      simp [← nh, tsub_self] at this
    rcases lt_or_gt_of_ne ha with ha | ha
    · apply ha.trans_le
      simp
    · rw [geom_sum_of_one_lt ha] at this
      calc
        ‖a‖₊ = ‖a‖₊ - 1 + 1 := (tsub_add_cancel_of_le ha.le).symm
        _ = ‖a‖₊ ^ p.natDegree * (‖a‖₊ - 1) / ‖a‖₊ ^ p.natDegree + 1 := by field
        _ <= (cauchyBound p - 1) * ((‖a‖₊ ^ p.natDegree - 1) / (‖a‖₊ - 1)) * (‖a‖₊ - 1)
            / ‖a‖₊ ^ p.natDegree + 1 := by gcongr
        _ = (cauchyBound p - 1) * (‖a‖₊ ^ p.natDegree - 1) / ‖a‖₊ ^ p.natDegree + 1 := by
          congr 2
          have : ‖a‖₊ - 1 != 0 := fun nh => (ha.trans_le (tsub_eq_zero_iff_le.mp nh)).false
          field
        _ < (cauchyBound p - 1) * ‖a‖₊ ^ p.natDegree / ‖a‖₊ ^ p.natDegree + 1 := by
          gcongr
          · apply lt_of_le_of_ne (by simp)
            contrapose! this
            simp only [← this, zero_mul]
            apply pow_pos
            exact zero_lt_one.trans ha
          simp [zero_lt_one.trans ha]
        _ = cauchyBound p := by simp [field, tsub_add_cancel_of_le]
  apply le_of_eq at h
  have pld : ‖p.leadingCoeff‖₊ != 0 := by simpa
  calc ‖a‖₊ ^ p.natDegree
    _ = ‖p.leadingCoeff‖₊ * ‖a‖₊ ^ p.natDegree / ‖p.leadingCoeff‖₊ := by
      rw [mul_div_cancel_left₀]
      simpa
    _ <= ‖∑ x in range p.natDegree, p.coeff x * a ^ x‖₊ / ‖p.leadingCoeff‖₊ := by gcongr
    _ <= (∑ x in range p.natDegree, ‖p.coeff x * a ^ x‖₊) / ‖p.leadingCoeff‖₊ := by
      gcongr
      apply nnnorm_sum_le
    _ = (∑ x in range p.natDegree, ‖p.coeff x‖₊ * ‖a‖₊ ^ x) / ‖p.leadingCoeff‖₊ := by simp
    _ <= (∑ x in range p.natDegree, ‖p.leadingCoeff‖₊ * (cauchyBound p - 1) * ‖a‖₊ ^ x) /
        ‖p.leadingCoeff‖₊ := by
      gcongr (∑ x in _, ?_ * _) / _
      rw [cauchyBound]; rw [add_tsub_cancel_right]
      field_simp
      apply le_sup (f := (‖p.coeff ·‖₊)) ‹_›
    _ = (cauchyBound p - 1) * ∑ x in range p.natDegree, ‖a‖₊ ^ x := by
      simp only [← mul_sum]
      field

中文:
定理 IsRoot.norm_lt_cauchyBound
  条件: {p : K[X]} (hp : p != 0) {a : K} (h : p.IsRoot a)
  证明: by
  rw [IsRoot.def]; rw [eval_eq_sum_range]; rw [range_add_one] at h
  simp only [mem_range, lt_self_iff_false, not_false_eq_true, sum_insert, coeff_natDegree,
    add_eq_zero_iff_eq_neg] at h
  apply_fun nnnorm at h
  simp only [nnnorm_mul, nnnorm_pow, nnnorm_neg] at h
  suffices ‖a‖₊ ^ p.natDegree <= (cauchyBound p - 1) * ∑ x in range p.natDegree, ‖a‖₊ ^ x by
    rcases eq_or_ne ‖a‖₊ 1 with ha | ha
    · simp only [ha, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, gt_iff_lt] at this ⊢
      apply lt_of_le_of_ne (by simp)
      intro nh
      simp [← nh, tsub_self] at this
    rcases lt_or_gt_of_ne ha with ha | ha
    · apply ha.trans_le
      simp
    · rw [geom_sum_of_one_lt ha] at this
      calc
        ‖a‖₊ = ‖a‖₊ - 1 + 1 := (tsub_add_cancel_of_le ha.le).symm
        _ = ‖a‖₊ ^ p.natDegree * (‖a‖₊ - 1) / ‖a‖₊ ^ p.natDegree + 1 := by field
        _ <= (cauchyBound p - 1) * ((‖a‖₊ ^ p.natDegree - 1) / (‖a‖₊ - 1)) * (‖a‖₊ - 1)
            / ‖a‖₊ ^ p.natDegree + 1 := by gcongr
        _ = (cauchyBound p - 1) * (‖a‖₊ ^ p.natDegree - 1) / ‖a‖₊ ^ p.natDegree + 1 := by
          congr 2
          have : ‖a‖₊ - 1 != 0 := fun nh => (ha.trans_le (tsub_eq_zero_iff_le.mp nh)).false
          field
        _ < (cauchyBound p - 1) * ‖a‖₊ ^ p.natDegree / ‖a‖₊ ^ p.natDegree + 1 := by
          gcongr
          · apply lt_of_le_of_ne (by simp)
            contrapose! this
            simp only [← this, zero_mul]
            apply pow_pos
            exact zero_lt_one.trans ha
          simp [zero_lt_one.trans ha]
        _ = cauchyBound p := by simp [field, tsub_add_cancel_of_le]
  apply le_of_eq at h
  have pld : ‖p.leadingCoeff‖₊ != 0 := by simpa
  calc ‖a‖₊ ^ p.natDegree
    _ = ‖p.leadingCoeff‖₊ * ‖a‖₊ ^ p.natDegree / ‖p.leadingCoeff‖₊ := by
      rw [mul_div_cancel_left₀]
      simpa
    _ <= ‖∑ x in range p.natDegree, p.coeff x * a ^ x‖₊ / ‖p.leadingCoeff‖₊ := by gcongr
    _ <= (∑ x in range p.natDegree, ‖p.coeff x * a ^ x‖₊) / ‖p.leadingCoeff‖₊ := by
      gcongr
      apply nnnorm_sum_le
    _ = (∑ x in range p.natDegree, ‖p.coeff x‖₊ * ‖a‖₊ ^ x) / ‖p.leadingCoeff‖₊ := by simp
    _ <= (∑ x in range p.natDegree, ‖p.leadingCoeff‖₊ * (cauchyBound p - 1) * ‖a‖₊ ^ x) /
        ‖p.leadingCoeff‖₊ := by
      gcongr (∑ x in _, ?_ * _) / _
      rw [cauchyBound]; rw [add_tsub_cancel_right]
      field_simp
      apply le_sup (f := (‖p.coeff ·‖₊)) ‹_›
    _ = (cauchyBound p - 1) * ∑ x in range p.natDegree, ‖a‖₊ ^ x := by
      simp only [← mul_sum]
      field

Depends on / 依赖: IsRoot, IsRoot.def, add_eq_zero_iff_eq_neg, apply_fun, card_range, cauchyBound, coeff_natDegree, eq_or_ne, eval_eq_sum_range, gt_iff_lt, lt_of_le_of_ne, lt_self_iff_false, mem_range, mul_one, natDegree, nnnorm, nnnorm_mul, nnnorm_neg, nnnorm_pow, not_false_eq_true
-/
theorem IsRoot.norm_lt_cauchyBound {p : K[X]} (hp : p != 0) {a : K} (h : p.IsRoot a) :
    ‖a‖₊ < cauchyBound p := by
  rw [IsRoot.def]; rw [eval_eq_sum_range]; rw [range_add_one] at h
  simp only [mem_range, lt_self_iff_false, not_false_eq_true, sum_insert, coeff_natDegree,
    add_eq_zero_iff_eq_neg] at h
  apply_fun nnnorm at h
  simp only [nnnorm_mul, nnnorm_pow, nnnorm_neg] at h
  suffices ‖a‖₊ ^ p.natDegree <= (cauchyBound p - 1) * ∑ x in range p.natDegree, ‖a‖₊ ^ x by
    rcases eq_or_ne ‖a‖₊ 1 with ha | ha
    · simp only [ha, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, gt_iff_lt] at this ⊢
      apply lt_of_le_of_ne (by simp)
      intro nh
      simp [← nh, tsub_self] at this
    rcases lt_or_gt_of_ne ha with ha | ha
    · apply ha.trans_le
      simp
    · rw [geom_sum_of_one_lt ha] at this
      calc
        ‖a‖₊ = ‖a‖₊ - 1 + 1 := (tsub_add_cancel_of_le ha.le).symm
        _ = ‖a‖₊ ^ p.natDegree * (‖a‖₊ - 1) / ‖a‖₊ ^ p.natDegree + 1 := by field
        _ <= (cauchyBound p - 1) * ((‖a‖₊ ^ p.natDegree - 1) / (‖a‖₊ - 1)) * (‖a‖₊ - 1)
            / ‖a‖₊ ^ p.natDegree + 1 := by gcongr
        _ = (cauchyBound p - 1) * (‖a‖₊ ^ p.natDegree - 1) / ‖a‖₊ ^ p.natDegree + 1 := by
          congr 2
          have : ‖a‖₊ - 1 != 0 := fun nh => (ha.trans_le (tsub_eq_zero_iff_le.mp nh)).false
          field
        _ < (cauchyBound p - 1) * ‖a‖₊ ^ p.natDegree / ‖a‖₊ ^ p.natDegree + 1 := by
          gcongr
          · apply lt_of_le_of_ne (by simp)
            contrapose! this
            simp only [← this, zero_mul]
            apply pow_pos
            exact zero_lt_one.trans ha
          simp [zero_lt_one.trans ha]
        _ = cauchyBound p := by simp [field, tsub_add_cancel_of_le]
  apply le_of_eq at h
  have pld : ‖p.leadingCoeff‖₊ != 0 := by simpa
  calc ‖a‖₊ ^ p.natDegree
    _ = ‖p.leadingCoeff‖₊ * ‖a‖₊ ^ p.natDegree / ‖p.leadingCoeff‖₊ := by
      rw [mul_div_cancel_left₀]
      simpa
    _ <= ‖∑ x in range p.natDegree, p.coeff x * a ^ x‖₊ / ‖p.leadingCoeff‖₊ := by gcongr
    _ <= (∑ x in range p.natDegree, ‖p.coeff x * a ^ x‖₊) / ‖p.leadingCoeff‖₊ := by
      gcongr
      apply nnnorm_sum_le
    _ = (∑ x in range p.natDegree, ‖p.coeff x‖₊ * ‖a‖₊ ^ x) / ‖p.leadingCoeff‖₊ := by simp
    _ <= (∑ x in range p.natDegree, ‖p.leadingCoeff‖₊ * (cauchyBound p - 1) * ‖a‖₊ ^ x) /
        ‖p.leadingCoeff‖₊ := by
      gcongr (∑ x in _, ?_ * _) / _
      rw [cauchyBound]; rw [add_tsub_cancel_right]
      field_simp
      apply le_sup (f := (‖p.coeff ·‖₊)) ‹_›
    _ = (cauchyBound p - 1) * ∑ x in range p.natDegree, ‖a‖₊ ^ x := by
      simp only [← mul_sum]
      field

end Polynomial
