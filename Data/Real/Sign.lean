/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Eric Wieser
-/
module

public import Mathlib.Data.Real.Basic

/-!
# Real sign function

This file introduces and contains some results about `Real.sign` which maps negative
real numbers to -1, positive real numbers to 1, and 0 to 0.

## Main definitions

* `Real.sign r` is $\begin{cases} -1 & \text{if } r < 0, \\
                              ~~\, 0 & \text{if } r = 0, \\
                              ~~\, 1 & \text{if } r > 0. \end{cases}$

## Tags

sign function
-/

@[expose] public section


namespace Real

/--
Definition of `sign` / `sign` 的定义

English:
definition sign
  signature: (r : Real)
  body: if r < 0 then -1 else if 0 < r then 1 else 0

中文:
定义 sign
  签名: (r : 实数)
  定义体: if r < 0 then -1 else if 0 < r then 1 else 0
-/
noncomputable def sign (r : Real) : Real :=
  if r < 0 then -1 else if 0 < r then 1 else 0

/--
theorem `sign_of_neg` / 定理 `sign_of_neg`

English:
theorem sign_of_neg
  given: {r : Real} (hr : r < 0)
  statement: sign r = -1
  proof: by rw [sign, if_pos hr]

中文:
定理 sign_of_neg
  条件: {r : 实数} (hr : r < 0)
  结论: sign r = -1
  证明: by rw [sign, if_pos hr]

Depends on / 依赖: if_pos
-/
theorem sign_of_neg {r : Real} (hr : r < 0) : sign r = -1 := by rw [sign, if_pos hr]

/--
theorem `sign_of_pos` / 定理 `sign_of_pos`

English:
theorem sign_of_pos
  given: {r : Real} (hr : 0 < r)
  statement: sign r = 1
  proof: by rw [sign, if_pos hr, if_neg hr.not_gt]

@[simp]

中文:
定理 sign_of_pos
  条件: {r : 实数} (hr : 0 < r)
  结论: sign r = 1
  证明: by rw [sign, if_pos hr, if_neg hr.not_gt]

@[simp]

Depends on / 依赖: hr.not_gt, if_neg, if_pos, not_gt
-/
theorem sign_of_pos {r : Real} (hr : 0 < r) : sign r = 1 := by rw [sign, if_pos hr, if_neg hr.not_gt]

@[simp]
/--
theorem `sign_zero` / 定理 `sign_zero`

English:
theorem sign_zero
  statement: sign 0 = 0
  proof: by rw [sign, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]

@[simp]

中文:
定理 sign_zero
  结论: sign 0 = 0
  证明: by rw [sign, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]

@[simp]

Depends on / 依赖: if_neg, lt_irrefl
-/
theorem sign_zero : sign 0 = 0 := by rw [sign, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]

@[simp]
/--
theorem `sign_one` / 定理 `sign_one`

English:
theorem sign_one
  statement: sign 1 = 1
  proof: sign_of_pos by simp

中文:
定理 sign_one
  结论: sign 1 = 1
  证明: sign_of_pos by simp

Depends on / 依赖: sign_of_pos
-/
theorem sign_one : sign 1 = 1 :=
sign_of_pos by simp

/--
theorem `sign_apply_eq` / 定理 `sign_apply_eq`

English:
theorem sign_apply_eq
  given: (r : Real)
  statement: sign r = -1 ∨ sign r = 0 ∨ sign r = 1
  proof: by
  obtain hn | rfl | hp := lt_trichotomy r (0 : Real)
· exact Or.inl sign_of_neg hn
· exact Or.inr Or.inl sign_zero
· exact Or.inr Or.inr sign_of_pos hp

中文:
定理 sign_apply_eq
  条件: (r : 实数)
  结论: sign r = -1 ∨ sign r = 0 ∨ sign r = 1
  证明: by
  obtain hn | rfl | hp := lt_trichotomy r (0 : Real)
· exact Or.inl sign_of_neg hn
· exact Or.inr Or.inl sign_zero
· exact Or.inr Or.inr sign_of_pos hp

Depends on / 依赖: Or.inl, Or.inr, lt_trichotomy, sign_of_neg, sign_of_pos, sign_zero
-/
theorem sign_apply_eq (r : Real) : sign r = -1 ∨ sign r = 0 ∨ sign r = 1 := by
  obtain hn | rfl | hp := lt_trichotomy r (0 : Real)
· exact Or.inl sign_of_neg hn
· exact Or.inr Or.inl sign_zero
· exact Or.inr Or.inr sign_of_pos hp

/--
theorem `sign_apply_eq_of_ne_zero` / 定理 `sign_apply_eq_of_ne_zero`

English:
theorem sign_apply_eq_of_ne_zero
  given: (r : Real) (h : r != 0)
  statement: sign r = -1 ∨ sign r = 1
  proof: h.lt_or_gt.imp sign_of_neg sign_of_pos

@[simp]

中文:
定理 sign_apply_eq_of_ne_zero
  条件: (r : 实数) (h : r != 0)
  结论: sign r = -1 ∨ sign r = 1
  证明: h.lt_or_gt.imp sign_of_neg sign_of_pos

@[simp]

Depends on / 依赖: h.lt_or_gt.imp, lt_or_gt, sign_of_neg, sign_of_pos
-/
theorem sign_apply_eq_of_ne_zero (r : Real) (h : r != 0) : sign r = -1 ∨ sign r = 1 :=
  h.lt_or_gt.imp sign_of_neg sign_of_pos

@[simp]
/--
theorem `sign_eq_zero_iff` / 定理 `sign_eq_zero_iff`

English:
theorem sign_eq_zero_iff
  given: {r : Real}
  statement: sign r = 0 ↔ r = 0
  proof: by
  refine ⟨fun h => ?_, fun h => h.symm ▸ sign_zero⟩
  obtain hn | rfl | hp := lt_trichotomy r (0 : Real)
  · rw [sign_of_neg hn, neg_eq_zero] at h
    exact (one_ne_zero h).elim
  · rfl
  · rw [sign_of_pos hp] at h
    exact (one_ne_zero h).elim

中文:
定理 sign_eq_zero_iff
  条件: {r : 实数}
  结论: sign r = 0 ↔ r = 0
  证明: by
  refine ⟨fun h => ?_, fun h => h.symm ▸ sign_zero⟩
  obtain hn | rfl | hp := lt_trichotomy r (0 : Real)
  · rw [sign_of_neg hn, neg_eq_zero] at h
    exact (one_ne_zero h).elim
  · rfl
  · rw [sign_of_pos hp] at h
    exact (one_ne_zero h).elim

Depends on / 依赖: h.symm, lt_trichotomy, neg_eq_zero, one_ne_zero, sign_of_neg, sign_of_pos, sign_zero
-/
theorem sign_eq_zero_iff {r : Real} : sign r = 0 ↔ r = 0 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ sign_zero⟩
  obtain hn | rfl | hp := lt_trichotomy r (0 : Real)
  · rw [sign_of_neg hn, neg_eq_zero] at h
    exact (one_ne_zero h).elim
  · rfl
  · rw [sign_of_pos hp] at h
    exact (one_ne_zero h).elim

/--
theorem `sign_intCast` / 定理 `sign_intCast`

English:
theorem sign_intCast
  given: (z : Int)
  statement: sign (z : Real) = ↑(Int.sign z)
  proof: by
  obtain hn | rfl | hp := lt_trichotomy z (0 : Int)
  · rw [sign_of_neg (Int.cast_lt_zero.mpr hn), Int.sign_eq_neg_one_of_neg hn, Int.cast_neg,
      Int.cast_one]
  · rw [Int.cast_zero, sign_zero, Int.sign_zero, Int.cast_zero]
  · rw [sign_of_pos (Int.cast_pos.mpr hp), Int.sign_eq_one_of_pos hp, Int.cast_one]

中文:
定理 sign_intCast
  条件: (z : 整数)
  结论: sign (z : 实数) = ↑(整数.sign z)
  证明: by
  obtain hn | rfl | hp := lt_trichotomy z (0 : Int)
  · rw [sign_of_neg (Int.cast_lt_zero.mpr hn), Int.sign_eq_neg_one_of_neg hn, Int.cast_neg,
      Int.cast_one]
  · rw [Int.cast_zero, sign_zero, Int.sign_zero, Int.cast_zero]
  · rw [sign_of_pos (Int.cast_pos.mpr hp), Int.sign_eq_one_of_pos hp, Int.cast_one]

Depends on / 依赖: Int.cast_lt_zero.mpr, Int.cast_neg, Int.cast_one, Int.cast_pos.mpr, Int.cast_zero, Int.sign_eq_neg_one_of_neg, Int.sign_eq_one_of_pos, Int.sign_zero, cast_lt_zero, cast_neg, cast_one, cast_pos, cast_zero, lt_trichotomy, sign_eq_neg_one_of_neg, sign_eq_one_of_pos, sign_of_neg, sign_of_pos, sign_zero
-/
theorem sign_intCast (z : Int) : sign (z : Real) = ↑(Int.sign z) := by
  obtain hn | rfl | hp := lt_trichotomy z (0 : Int)
  · rw [sign_of_neg (Int.cast_lt_zero.mpr hn), Int.sign_eq_neg_one_of_neg hn, Int.cast_neg,
      Int.cast_one]
  · rw [Int.cast_zero, sign_zero, Int.sign_zero, Int.cast_zero]
  · rw [sign_of_pos (Int.cast_pos.mpr hp), Int.sign_eq_one_of_pos hp, Int.cast_one]

/--
theorem `sign_neg` / 定理 `sign_neg`

English:
theorem sign_neg
  given: {r : Real}
  statement: sign (-r) = -sign r
  proof: by
  obtain hn | rfl | hp := lt_trichotomy r (0 : Real)
  · rw [sign_of_neg hn, sign_of_pos (neg_pos.mpr hn), neg_neg]
  · rw [sign_zero, neg_zero, sign_zero]
  · rw [sign_of_pos hp, sign_of_neg (neg_lt_zero.mpr hp)]

中文:
定理 sign_neg
  条件: {r : 实数}
  结论: sign (-r) = -sign r
  证明: by
  obtain hn | rfl | hp := lt_trichotomy r (0 : Real)
  · rw [sign_of_neg hn, sign_of_pos (neg_pos.mpr hn), neg_neg]
  · rw [sign_zero, neg_zero, sign_zero]
  · rw [sign_of_pos hp, sign_of_neg (neg_lt_zero.mpr hp)]

Depends on / 依赖: lt_trichotomy, neg_lt_zero, neg_lt_zero.mpr, neg_neg, neg_pos, neg_pos.mpr, neg_zero, sign_of_neg, sign_of_pos, sign_zero
-/
theorem sign_neg {r : Real} : sign (-r) = -sign r := by
  obtain hn | rfl | hp := lt_trichotomy r (0 : Real)
  · rw [sign_of_neg hn, sign_of_pos (neg_pos.mpr hn), neg_neg]
  · rw [sign_zero, neg_zero, sign_zero]
  · rw [sign_of_pos hp, sign_of_neg (neg_lt_zero.mpr hp)]

/--
theorem `sign_mul_nonneg` / 定理 `sign_mul_nonneg`

English:
theorem sign_mul_nonneg
  given: (r : Real)
  statement: 0 <= sign r * r
  proof: by
  obtain hn | rfl | hp := lt_trichotomy r (0 : Real)
  · rw [sign_of_neg hn]
    exact mul_nonneg_of_nonpos_of_nonpos (by simp) hn.le
  · rw [mul_zero]
  · rw [sign_of_pos hp, one_mul]
    exact hp.le

中文:
定理 sign_mul_nonneg
  条件: (r : 实数)
  结论: 0 <= sign r * r
  证明: by
  obtain hn | rfl | hp := lt_trichotomy r (0 : Real)
  · rw [sign_of_neg hn]
    exact mul_nonneg_of_nonpos_of_nonpos (by simp) hn.le
  · rw [mul_zero]
  · rw [sign_of_pos hp, one_mul]
    exact hp.le

Depends on / 依赖: hn.le, hp.le, lt_trichotomy, mul_nonneg_of_nonpos_of_nonpos, mul_zero, one_mul, sign_of_neg, sign_of_pos
-/
theorem sign_mul_nonneg (r : Real) : 0 <= sign r * r := by
  obtain hn | rfl | hp := lt_trichotomy r (0 : Real)
  · rw [sign_of_neg hn]
    exact mul_nonneg_of_nonpos_of_nonpos (by simp) hn.le
  · rw [mul_zero]
  · rw [sign_of_pos hp, one_mul]
    exact hp.le

/--
theorem `sign_mul_pos_of_ne_zero` / 定理 `sign_mul_pos_of_ne_zero`

English:
theorem sign_mul_pos_of_ne_zero
  given: (r : Real) (hr : r != 0)
  statement: 0 < sign r * r
  proof: by
  refine lt_of_le_of_ne (sign_mul_nonneg r) fun h => hr ?_
  have hs0 := (zero_eq_mul.mp h).resolve_right hr
  exact sign_eq_zero_iff.mp hs0

@[simp]

中文:
定理 sign_mul_pos_of_ne_zero
  条件: (r : 实数) (hr : r != 0)
  结论: 0 < sign r * r
  证明: by
  refine lt_of_le_of_ne (sign_mul_nonneg r) fun h => hr ?_
  have hs0 := (zero_eq_mul.mp h).resolve_right hr
  exact sign_eq_zero_iff.mp hs0

@[simp]

Depends on / 依赖: lt_of_le_of_ne, resolve_right, sign_eq_zero_iff, sign_eq_zero_iff.mp, sign_mul_nonneg, zero_eq_mul, zero_eq_mul.mp
-/
theorem sign_mul_pos_of_ne_zero (r : Real) (hr : r != 0) : 0 < sign r * r := by
  refine lt_of_le_of_ne (sign_mul_nonneg r) fun h => hr ?_
  have hs0 := (zero_eq_mul.mp h).resolve_right hr
  exact sign_eq_zero_iff.mp hs0

@[simp]
/--
theorem `inv_sign` / 定理 `inv_sign`

English:
theorem inv_sign
  given: (r : Real)
  statement: (sign r)⁻¹ = sign r
  proof: by
  obtain hn | hz | hp := sign_apply_eq r
  · rw [hn]
    simp
  · rw [hz]
    exact inv_zero
  · rw [hp]
    exact inv_one

@[simp]

中文:
定理 inv_sign
  条件: (r : 实数)
  结论: (sign r)⁻¹ = sign r
  证明: by
  obtain hn | hz | hp := sign_apply_eq r
  · rw [hn]
    simp
  · rw [hz]
    exact inv_zero
  · rw [hp]
    exact inv_one

@[simp]

Depends on / 依赖: inv_one, inv_zero, sign_apply_eq
-/
theorem inv_sign (r : Real) : (sign r)⁻¹ = sign r := by
  obtain hn | hz | hp := sign_apply_eq r
  · rw [hn]
    simp
  · rw [hz]
    exact inv_zero
  · rw [hp]
    exact inv_one

@[simp]
/--
theorem `sign_inv` / 定理 `sign_inv`

English:
theorem sign_inv
  given: (r : Real)
  statement: sign r⁻¹ = sign r
  proof: by
  obtain hn | rfl | hp := lt_trichotomy r (0 : Real)
  · rw [sign_of_neg hn, sign_of_neg (inv_lt_zero.mpr hn)]
  · rw [sign_zero, inv_zero, sign_zero]
  · rw [sign_of_pos hp, sign_of_pos (inv_pos.mpr hp)]

中文:
定理 sign_inv
  条件: (r : 实数)
  结论: sign r⁻¹ = sign r
  证明: by
  obtain hn | rfl | hp := lt_trichotomy r (0 : Real)
  · rw [sign_of_neg hn, sign_of_neg (inv_lt_zero.mpr hn)]
  · rw [sign_zero, inv_zero, sign_zero]
  · rw [sign_of_pos hp, sign_of_pos (inv_pos.mpr hp)]

Depends on / 依赖: inv_lt_zero, inv_lt_zero.mpr, inv_pos, inv_pos.mpr, inv_zero, lt_trichotomy, sign_of_neg, sign_of_pos, sign_zero
-/
theorem sign_inv (r : Real) : sign r⁻¹ = sign r := by
  obtain hn | rfl | hp := lt_trichotomy r (0 : Real)
  · rw [sign_of_neg hn, sign_of_neg (inv_lt_zero.mpr hn)]
  · rw [sign_zero, inv_zero, sign_zero]
  · rw [sign_of_pos hp, sign_of_pos (inv_pos.mpr hp)]

end Real
