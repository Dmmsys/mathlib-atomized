/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Square root on `RCLike`

This file contains the definitions `Complex.sqrt` and `RCLike.sqrt` and builds basic API.
-/

@[expose] public section

variable {𝕜 : Type*} [RCLike 𝕜]

open ComplexOrder

/--
Definition of `Complex.sqrt` / `Complex.sqrt` 的定义

English:
definition Complex.sqrt
  signature: (a : Complex)
  body: a ^ (2⁻¹ : Complex)

中文:
定义 复形.sqrt
  签名: (a : 复形)
  定义体: a ^ (2⁻¹ : Complex)
-/
noncomputable def Complex.sqrt (a : Complex) : Complex := a ^ (2⁻¹ : Complex)

/--
theorem `Complex.sqrt_zero` / 定理 `Complex.sqrt_zero`

English:
theorem Complex.sqrt_zero
  statement: (0 : Complex).sqrt = 0
  proof: by simp [sqrt]

中文:
定理 复形.sqrt_zero
  结论: (0 : 复形).sqrt = 0
  证明: by simp [sqrt]
-/
@[simp] theorem Complex.sqrt_zero : (0 : Complex).sqrt = 0 := by simp [sqrt]
/--
theorem `Complex.sqrt_one` / 定理 `Complex.sqrt_one`

English:
theorem Complex.sqrt_one
  statement: (1 : Complex).sqrt = 1
  proof: by simp [sqrt]

中文:
定理 复形.sqrt_one
  结论: (1 : 复形).sqrt = 1
  证明: by simp [sqrt]
-/
@[simp] theorem Complex.sqrt_one : (1 : Complex).sqrt = 1 := by simp [sqrt]

/--
theorem `Complex.sqrt_eq_real_add_ite` / 定理 `Complex.sqrt_eq_real_add_ite`

English:
theorem Complex.sqrt_eq_real_add_ite
  given: {a : Complex}
  proof: by
  rw [← cpow_inv_two_re]; rw [sqrt]
  by_cases! h : 0 <= a.im
  · simp [← cpow_inv_two_im_eq_sqrt h, h]
  simp only [re_add_im, ↓reduceIte, h.not_ge, neg_one_mul, ← ofReal_neg,
    ← cpow_inv_two_im_eq_neg_sqrt h]

中文:
定理 复形.sqrt_eq_real_add_ite
  条件: {a : 复形}
  证明: by
  rw [← cpow_inv_two_re]; rw [sqrt]
  by_cases! h : 0 <= a.im
  · simp [← cpow_inv_two_im_eq_sqrt h, h]
  simp only [re_add_im, ↓reduceIte, h.not_ge, neg_one_mul, ← ofReal_neg,
    ← cpow_inv_two_im_eq_neg_sqrt h]

Depends on / 依赖: a.im, cpow_inv_two_im_eq_neg_sqrt, cpow_inv_two_im_eq_sqrt, cpow_inv_two_re, h.not_ge, neg_one_mul, not_ge, ofReal_neg, re_add_im, reduceIte
-/
theorem Complex.sqrt_eq_real_add_ite {a : Complex} :
    a.sqrt = √((‖a‖ + a.re) / 2) + (if 0 <= a.im then 1 else -1) * √((‖a‖ - a.re) / 2) * I := by
  rw [← cpow_inv_two_re]; rw [sqrt]
  by_cases! h : 0 <= a.im
  · simp [← cpow_inv_two_im_eq_sqrt h, h]
  simp only [re_add_im, ↓reduceIte, h.not_ge, neg_one_mul, ← ofReal_neg,
    ← cpow_inv_two_im_eq_neg_sqrt h]

open Complex in
/--
lemma `sqrt_eq_exp` / 引理 `sqrt_eq_exp`

English:
lemma sqrt_eq_exp
  given: {z : Complex} (hz : z != 0)
  statement: sqrt z = exp (log z / 2)
  proof: by
  simp [sqrt, cpow_def, hz, div_eq_mul_inv]

中文:
引理 sqrt_eq_exp
  条件: {z : 复形} (hz : z != 0)
  结论: sqrt z = exp (log z / 2)
  证明: by
  simp [sqrt, cpow_def, hz, div_eq_mul_inv]

Depends on / 依赖: cpow_def, div_eq_mul_inv, epi_of_iso
-/
lemma sqrt_eq_exp {z : Complex} (hz : z != 0) : sqrt z = exp (log z / 2) := by
  simp [sqrt, cpow_def, hz, div_eq_mul_inv]

/--
Definition of `RCLike.sqrt` / `RCLike.sqrt` 的定义

English:
definition RCLike.sqrt
  signature: (a : 𝕜)
  body: map Complex 𝕜 (map 𝕜 Complex a).sqrt

中文:
定义 RCLike.sqrt
  签名: (a : 𝕜)
  定义体: map Complex 𝕜 (map 𝕜 Complex a).sqrt
-/
noncomputable def RCLike.sqrt (a : 𝕜) : 𝕜 := map Complex 𝕜 (map 𝕜 Complex a).sqrt

/--
theorem `RCLike.sqrt_eq_ite` / 定理 `RCLike.sqrt_eq_ite`

English:
theorem RCLike.sqrt_eq_ite
  given: {a : 𝕜}
  proof: by
  rw [sqrt]; rw [eq_comm]
  split_ifs with h
  · simp
  have : (I : 𝕜) = 0 := by grind [I_eq_zero_or_im_I_eq_one]
  simp_all only [Complex.sqrt, im_eq_zero this, map_apply, add_zero, re_to_complex, im_to_complex,
    mul_zero, algebraMap.coe_inj, Complex.cpow_inv_two_re]
  by_cases! ha' : 0 <= re

中文:
定理 RCLike.sqrt_eq_ite
  条件: {a : 𝕜}
  证明: by
  rw [sqrt]; rw [eq_comm]
  split_ifs with h
  · simp
  have : (I : 𝕜) = 0 := by grind [I_eq_zero_or_im_I_eq_one]
  simp_all only [Complex.sqrt, im_eq_zero this, map_apply, add_zero, re_to_complex, im_to_complex,
    mul_zero, algebraMap.coe_inj, Complex.cpow_inv_two_re]
  by_cases! ha' : 0 <= re

Depends on / 依赖: Complex.cpow_inv_two_re, Complex.sqrt, I_eq_zero_or_im_I_eq_one, Real.sqrt_eq_zero, abs_of_nonneg, abs_of_nonpos, add_zero, algebraMap, algebraMap.coe_inj, coe_inj, cpow_inv_two_re, eq_comm, im_eq_zero, im_to_complex, map_apply, mul_zero, re_to_complex, split_ifs, sqrt_eq_zero, two_mul
-/
theorem RCLike.sqrt_eq_ite {a : 𝕜} :
    sqrt a = if h : im (I : 𝕜) = 1 then (complexRingEquiv h).symm (complexRingEquiv h a).sqrt
      else √(re a) := by
  rw [sqrt]; rw [eq_comm]
  split_ifs with h
  · simp
  have : (I : 𝕜) = 0 := by grind [I_eq_zero_or_im_I_eq_one]
  simp_all only [Complex.sqrt, im_eq_zero this, map_apply, add_zero, re_to_complex, im_to_complex,
    mul_zero, algebraMap.coe_inj, Complex.cpow_inv_two_re]
  by_cases! ha' : 0 <= re a
  · simp [abs_of_nonneg ha', ← two_mul]
  simp [abs_of_nonpos ha'.le, Real.sqrt_eq_zero', ha'.le]

/--
theorem `RCLike.sqrt_eq_real_add_ite` / 定理 `RCLike.sqrt_eq_real_add_ite`

English:
theorem RCLike.sqrt_eq_real_add_ite
  given: {a : 𝕜}
  proof: by
  rw [sqrt]; rw [Complex.sqrt_eq_real_add_ite]
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · rw [← re_add_im a]
    simp [h, im_eq_zero]
  aesop

中文:
定理 RCLike.sqrt_eq_real_add_ite
  条件: {a : 𝕜}
  证明: by
  rw [sqrt]; rw [Complex.sqrt_eq_real_add_ite]
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · rw [← re_add_im a]
    simp [h, im_eq_zero]
  aesop

Depends on / 依赖: Complex.sqrt_eq_real_add_ite, I_eq_zero_or_im_I_eq_one, im_eq_zero, re_add_im, sqrt_eq_real_add_ite
-/
theorem RCLike.sqrt_eq_real_add_ite {a : 𝕜} :
    sqrt a = √((‖a‖ + re a) / 2) + (if 0 <= im a then 1 else -1) * √((‖a‖ - re a) / 2) * I := by
  rw [sqrt]; rw [Complex.sqrt_eq_real_add_ite]
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · rw [← re_add_im a]
    simp [h, im_eq_zero]
  aesop

/--
theorem `RCLike.sqrt_zero` / 定理 `RCLike.sqrt_zero`

English:
theorem RCLike.sqrt_zero
  statement: sqrt (0 : 𝕜) = 0
  proof: by simp [sqrt]

中文:
定理 RCLike.sqrt_zero
  结论: sqrt (0 : 𝕜) = 0
  证明: by simp [sqrt]
-/
@[simp] theorem RCLike.sqrt_zero : sqrt (0 : 𝕜) = 0 := by simp [sqrt]
/--
theorem `RCLike.sqrt_one` / 定理 `RCLike.sqrt_one`

English:
theorem RCLike.sqrt_one
  statement: sqrt (1 : 𝕜) = 1
  proof: by simp [sqrt]

中文:
定理 RCLike.sqrt_one
  结论: sqrt (1 : 𝕜) = 1
  证明: by simp [sqrt]
-/
@[simp] theorem RCLike.sqrt_one : sqrt (1 : 𝕜) = 1 := by simp [sqrt]

/--
theorem `Complex.re_sqrt_ofReal` / 定理 `Complex.re_sqrt_ofReal`

English:
theorem Complex.re_sqrt_ofReal
  given: {a : Real}
  proof: by
  simp only [cpow_inv_two_re, norm_real, Real.norm_eq_abs, ofReal_re, Complex.sqrt]
  grind

中文:
定理 复形.re_sqrt_of实数
  条件: {a : 实数}
  证明: by
  simp only [cpow_inv_two_re, norm_real, Real.norm_eq_abs, ofReal_re, Complex.sqrt]
  grind

Depends on / 依赖: Complex.sqrt, Real.norm_eq_abs, cpow_inv_two_re, norm_eq_abs, norm_real, ofReal_re
-/
theorem Complex.re_sqrt_ofReal {a : Real} :
    (sqrt (a : Complex)).re = √a := by
  simp only [cpow_inv_two_re, norm_real, Real.norm_eq_abs, ofReal_re, Complex.sqrt]
  grind

/--
theorem `RCLike.re_sqrt_ofReal` / 定理 `RCLike.re_sqrt_ofReal`

English:
theorem RCLike.re_sqrt_ofReal
  given: {a : Real}
  proof: by
  aesop (add simp [sqrt, Complex.re_sqrt_ofReal])

中文:
定理 RCLike.re_sqrt_of实数
  条件: {a : 实数}
  证明: by
  aesop (add simp [sqrt, Complex.re_sqrt_ofReal])

Depends on / 依赖: Complex.re_sqrt_ofReal, re_sqrt_ofReal
-/
theorem RCLike.re_sqrt_ofReal {a : Real} :
    re (sqrt (a : 𝕜)) = √a := by
  aesop (add simp [sqrt, Complex.re_sqrt_ofReal])

/--
theorem `RCLike.sqrt_real` / 定理 `RCLike.sqrt_real`

English:
theorem RCLike.sqrt_real
  given: {a : Real}
  proof: by simp [← re_sqrt_ofReal (𝕜 := Real)]

中文:
定理 RCLike.sqrt_real
  条件: {a : 实数}
  证明: by simp [← re_sqrt_ofReal (𝕜 := Real)]
-/
@[simp] theorem RCLike.sqrt_real {a : Real} :
    sqrt a = √a := by simp [← re_sqrt_ofReal (𝕜 := Real)]

/--
theorem `RCLike.sqrt_complex` / 定理 `RCLike.sqrt_complex`

English:
theorem RCLike.sqrt_complex
  given: {a : Complex}
  proof: by simp [sqrt]

中文:
定理 RCLike.sqrt_complex
  条件: {a : 复形}
  证明: by simp [sqrt]
-/
@[simp] theorem RCLike.sqrt_complex {a : Complex} :
    sqrt a = a.sqrt := by simp [sqrt]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Complex.sqrt_of_nonneg` / 定理 `Complex.sqrt_of_nonneg`

English:
theorem Complex.sqrt_of_nonneg
  given: {a : Complex} (ha : 0 <= a)
  proof: by
  obtain ⟨α : Real, hα, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp ha
  simp only [coe_algebraMap, ofReal_re]
  rw [← re_add_im (α : Complex).sqrt]; rw [re_sqrt_ofReal]
  simp [sqrt, cpow_inv_two_im_eq_sqrt, abs_of_nonneg hα]

中文:
定理 复形.sqrt_of_nonneg
  条件: {a : 复形} (ha : 0 <= a)
  证明: by
  obtain ⟨α : Real, hα, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp ha
  simp only [coe_algebraMap, ofReal_re]
  rw [← re_add_im (α : Complex).sqrt]; rw [re_sqrt_ofReal]
  simp [sqrt, cpow_inv_two_im_eq_sqrt, abs_of_nonneg hα]

Depends on / 依赖: RCLike, RCLike.nonneg_iff_exists_ofReal.mp, abs_of_nonneg, coe_algebraMap, cpow_inv_two_im_eq_sqrt, nonneg_iff_exists_ofReal, ofReal_re, re_add_im, re_sqrt_ofReal
-/
theorem Complex.sqrt_of_nonneg {a : Complex} (ha : 0 <= a) :
    a.sqrt = √a.re := by
  obtain ⟨α : Real, hα, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp ha
  simp only [coe_algebraMap, ofReal_re]
  rw [← re_add_im (α : Complex).sqrt]; rw [re_sqrt_ofReal]
  simp [sqrt, cpow_inv_two_im_eq_sqrt, abs_of_nonneg hα]

/--
theorem `RCLike.sqrt_map` / 定理 `RCLike.sqrt_map`

English:
theorem RCLike.sqrt_map
  given: {𝕜' : Type*} [RCLike 𝕜'] {a : 𝕜} (h : im (I : 𝕜) = im (I : 𝕜'))
  proof: by
  have := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  have := I_eq_zero_or_im_I_eq_one (K := 𝕜')
  aesop (add simp [RCLike.sqrt, im_eq_zero])

中文:
定理 RCLike.sqrt_map
  条件: {𝕜' : 类型} [RCLike 𝕜'] {a : 𝕜} (h : im (I : 𝕜) = im (I : 𝕜'))
  证明: by
  have := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  have := I_eq_zero_or_im_I_eq_one (K := 𝕜')
  aesop (add simp [RCLike.sqrt, im_eq_zero])

Depends on / 依赖: I_eq_zero_or_im_I_eq_one, RCLike, RCLike.sqrt, im_eq_zero
-/
theorem RCLike.sqrt_map {𝕜' : Type*} [RCLike 𝕜'] {a : 𝕜} (h : im (I : 𝕜) = im (I : 𝕜')) :
    sqrt (map 𝕜 𝕜' a) = map 𝕜 𝕜' (sqrt a) := by
  have := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  have := I_eq_zero_or_im_I_eq_one (K := 𝕜')
  aesop (add simp [RCLike.sqrt, im_eq_zero])

/--
theorem `Complex.sqrt_map` / 定理 `Complex.sqrt_map`

English:
theorem Complex.sqrt_map
  given: {a : 𝕜} (h : RCLike.im (RCLike.I : 𝕜) = 1)
  proof: by
  aesop (add simp [RCLike.sqrt])

中文:
定理 复形.sqrt_map
  条件: {a : 𝕜} (h : RCLike.im (RCLike.I : 𝕜) = 1)
  证明: by
  aesop (add simp [RCLike.sqrt])

Depends on / 依赖: RCLike, RCLike.sqrt
-/
theorem Complex.sqrt_map {a : 𝕜} (h : RCLike.im (RCLike.I : 𝕜) = 1) :
    (RCLike.map 𝕜 Complex a).sqrt = RCLike.map 𝕜 Complex (RCLike.sqrt a) := by
  aesop (add simp [RCLike.sqrt])

/--
theorem `RCLike.sqrt_of_nonneg` / 定理 `RCLike.sqrt_of_nonneg`

English:
theorem RCLike.sqrt_of_nonneg
  given: {a : 𝕜} (ha : 0 <= a)
  proof: by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · simp [h, sqrt_eq_ite]
  rw [sqrt_eq_ite]; rw [dif_pos h]; rw [RingEquiv.symm_apply_eq]; rw [Complex.sqrt_of_nonneg (by simpa)]
  simp

中文:
定理 RCLike.sqrt_of_nonneg
  条件: {a : 𝕜} (ha : 0 <= a)
  证明: by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · simp [h, sqrt_eq_ite]
  rw [sqrt_eq_ite]; rw [dif_pos h]; rw [RingEquiv.symm_apply_eq]; rw [Complex.sqrt_of_nonneg (by simpa)]
  simp

Depends on / 依赖: Complex.sqrt_of_nonneg, I_eq_zero_or_im_I_eq_one, RingEquiv, RingEquiv.symm_apply_eq, dif_pos, sqrt_eq_ite, sqrt_of_nonneg, symm_apply_eq
-/
theorem RCLike.sqrt_of_nonneg {a : 𝕜} (ha : 0 <= a) :
    sqrt a = √(re a) := by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · simp [h, sqrt_eq_ite]
  rw [sqrt_eq_ite]; rw [dif_pos h]; rw [RingEquiv.symm_apply_eq]; rw [Complex.sqrt_of_nonneg (by simpa)]
  simp

/--
theorem `Complex.sqrt_neg_of_nonneg` / 定理 `Complex.sqrt_neg_of_nonneg`

English:
theorem Complex.sqrt_neg_of_nonneg
  given: {a : Complex} (ha : 0 <= a)
  proof: by
  obtain ⟨α, hα, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp ha
  rw [Complex.sqrt_of_nonneg ha]
  simp only [coe_algebraMap, ofReal_re]
  rw [← re_add_im (-(α : Complex)).sqrt]
  simp [sqrt, cpow_inv_two_im_eq_sqrt, abs_of_nonneg hα, cpow_inv_two_re, mul_comm]

中文:
定理 复形.sqrt_neg_of_nonneg
  条件: {a : 复形} (ha : 0 <= a)
  证明: by
  obtain ⟨α, hα, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp ha
  rw [Complex.sqrt_of_nonneg ha]
  simp only [coe_algebraMap, ofReal_re]
  rw [← re_add_im (-(α : Complex)).sqrt]
  simp [sqrt, cpow_inv_two_im_eq_sqrt, abs_of_nonneg hα, cpow_inv_two_re, mul_comm]

Depends on / 依赖: Complex.sqrt_of_nonneg, RCLike, RCLike.nonneg_iff_exists_ofReal.mp, abs_of_nonneg, coe_algebraMap, cpow_inv_two_im_eq_sqrt, cpow_inv_two_re, mul_comm, nonneg_iff_exists_ofReal, ofReal_re, re_add_im, sqrt_of_nonneg
-/
theorem Complex.sqrt_neg_of_nonneg {a : Complex} (ha : 0 <= a) :
    (-a).sqrt = I * a.sqrt := by
  obtain ⟨α, hα, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp ha
  rw [Complex.sqrt_of_nonneg ha]
  simp only [coe_algebraMap, ofReal_re]
  rw [← re_add_im (-(α : Complex)).sqrt]
  simp [sqrt, cpow_inv_two_im_eq_sqrt, abs_of_nonneg hα, cpow_inv_two_re, mul_comm]

/--
theorem `RCLike.sqrt_neg_of_nonneg` / 定理 `RCLike.sqrt_neg_of_nonneg`

English:
theorem RCLike.sqrt_neg_of_nonneg
  given: {a : 𝕜} (ha : 0 <= a)
  proof: by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · simp [h, sqrt_eq_ite, Real.sqrt_eq_zero', nonneg_iff.mp ha]
  rw [sqrt_eq_ite]; rw [dif_pos h]; rw [RingEquiv.symm_apply_eq]; rw [map_neg]; rw [Complex.sqrt_neg_of_nonneg (by simpa)]
  simp [h, sqrt, map_mul]

中文:
定理 RCLike.sqrt_neg_of_nonneg
  条件: {a : 𝕜} (ha : 0 <= a)
  证明: by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · simp [h, sqrt_eq_ite, Real.sqrt_eq_zero', nonneg_iff.mp ha]
  rw [sqrt_eq_ite]; rw [dif_pos h]; rw [RingEquiv.symm_apply_eq]; rw [map_neg]; rw [Complex.sqrt_neg_of_nonneg (by simpa)]
  simp [h, sqrt, map_mul]

Depends on / 依赖: Complex.sqrt_neg_of_nonneg, I_eq_zero_or_im_I_eq_one, Real.sqrt_eq_zero, RingEquiv, RingEquiv.symm_apply_eq, dif_pos, map_mul, map_neg, nonneg_iff, nonneg_iff.mp, sqrt_eq_ite, sqrt_eq_zero, sqrt_neg_of_nonneg, symm_apply_eq
-/
theorem RCLike.sqrt_neg_of_nonneg {a : 𝕜} (ha : 0 <= a) :
    sqrt (-a) = I * sqrt a := by
  obtain (h | h) := I_eq_zero_or_im_I_eq_one (K := 𝕜)
  · simp [h, sqrt_eq_ite, Real.sqrt_eq_zero', nonneg_iff.mp ha]
  rw [sqrt_eq_ite]; rw [dif_pos h]; rw [RingEquiv.symm_apply_eq]; rw [map_neg]; rw [Complex.sqrt_neg_of_nonneg (by simpa)]
  simp [h, sqrt, map_mul]

/--
theorem `Complex.sqrt_neg_one` / 定理 `Complex.sqrt_neg_one`

English:
theorem Complex.sqrt_neg_one
  statement: sqrt (-1) = I
  proof: by
  simp [sqrt_neg_of_nonneg (a := 1) (by simp)]

中文:
定理 复形.sqrt_neg_one
  结论: sqrt (-1) = I
  证明: by
  simp [sqrt_neg_of_nonneg (a := 1) (by simp)]

Depends on / 依赖: sqrt_neg_of_nonneg
-/
theorem Complex.sqrt_neg_one : sqrt (-1) = I := by
  simp [sqrt_neg_of_nonneg (a := 1) (by simp)]

/--
theorem `RCLike.sqrt_neg_one` / 定理 `RCLike.sqrt_neg_one`

English:
theorem RCLike.sqrt_neg_one
  statement: sqrt (-1) = (I : 𝕜)
  proof: by
  simp [sqrt_neg_of_nonneg (a := (1 : 𝕜)) (by simp)]

中文:
定理 RCLike.sqrt_neg_one
  结论: sqrt (-1) = (I : 𝕜)
  证明: by
  simp [sqrt_neg_of_nonneg (a := (1 : 𝕜)) (by simp)]

Depends on / 依赖: sqrt_neg_of_nonneg
-/
theorem RCLike.sqrt_neg_one : sqrt (-1) = (I : 𝕜) := by
  simp [sqrt_neg_of_nonneg (a := (1 : 𝕜)) (by simp)]

/--
theorem `Complex.sqrt_I` / 定理 `Complex.sqrt_I`

English:
theorem Complex.sqrt_I
  statement: sqrt (I : Complex) = √2⁻¹ * (1 + I)
  proof: by
  rw [sqrt]; rw [← re_add_im (I ^ 2⁻¹)]; rw [cpow_inv_two_im_eq_sqrt (by simp)]; rw [cpow_inv_two_re]
  simp [mul_add]

中文:
定理 复形.sqrt_I
  结论: sqrt (I : 复形) = √2⁻¹ * (1 + I)
  证明: by
  rw [sqrt]; rw [← re_add_im (I ^ 2⁻¹)]; rw [cpow_inv_two_im_eq_sqrt (by simp)]; rw [cpow_inv_two_re]
  simp [mul_add]

Depends on / 依赖: cpow_inv_two_im_eq_sqrt, cpow_inv_two_re, mul_add, re_add_im
-/
theorem Complex.sqrt_I : sqrt (I : Complex) = √2⁻¹ * (1 + I) := by
  rw [sqrt]; rw [← re_add_im (I ^ 2⁻¹)]; rw [cpow_inv_two_im_eq_sqrt (by simp)]; rw [cpow_inv_two_re]
  simp [mul_add]

/--
theorem `Complex.sqrt_neg_I` / 定理 `Complex.sqrt_neg_I`

English:
theorem Complex.sqrt_neg_I
  statement: sqrt (-I : Complex) = √2⁻¹ * (1 - I)
  proof: by
  rw [sqrt]; rw [← re_add_im ((-I) ^ 2⁻¹)]; rw [cpow_inv_two_im_eq_neg_sqrt (by simp)]; rw [cpow_inv_two_re]
  simp [mul_sub, ← sub_eq_add_neg]

中文:
定理 复形.sqrt_neg_I
  结论: sqrt (-I : 复形) = √2⁻¹ * (1 - I)
  证明: by
  rw [sqrt]; rw [← re_add_im ((-I) ^ 2⁻¹)]; rw [cpow_inv_two_im_eq_neg_sqrt (by simp)]; rw [cpow_inv_two_re]
  simp [mul_sub, ← sub_eq_add_neg]

Depends on / 依赖: cpow_inv_two_im_eq_neg_sqrt, cpow_inv_two_re, mul_sub, re_add_im, sub_eq_add_neg
-/
theorem Complex.sqrt_neg_I : sqrt (-I : Complex) = √2⁻¹ * (1 - I) := by
  rw [sqrt]; rw [← re_add_im ((-I) ^ 2⁻¹)]; rw [cpow_inv_two_im_eq_neg_sqrt (by simp)]; rw [cpow_inv_two_re]
  simp [mul_sub, ← sub_eq_add_neg]

/--
theorem `RCLike.sqrt_I` / 定理 `RCLike.sqrt_I`

English:
theorem RCLike.sqrt_I
  statement: sqrt (I : 𝕜) = √2⁻¹ * (1 - I) * I
  proof: by
  rw [sqrt_eq_ite]
  split_ifs with h
  · simp_rw [RingEquiv.symm_apply_eq, map_mul]
    simp [h, mul_assoc, mul_add, add_comm, Complex.sqrt_I, add_mul]
  grind [I_eq_zero_or_im_I_eq_one]

中文:
定理 RCLike.sqrt_I
  结论: sqrt (I : 𝕜) = √2⁻¹ * (1 - I) * I
  证明: by
  rw [sqrt_eq_ite]
  split_ifs with h
  · simp_rw [RingEquiv.symm_apply_eq, map_mul]
    simp [h, mul_assoc, mul_add, add_comm, Complex.sqrt_I, add_mul]
  grind [I_eq_zero_or_im_I_eq_one]

Depends on / 依赖: Complex.sqrt_I, I_eq_zero_or_im_I_eq_one, RingEquiv, RingEquiv.symm_apply_eq, add_comm, add_mul, map_mul, mul_add, mul_assoc, simp_rw, split_ifs, sqrt_I, sqrt_eq_ite, symm_apply_eq
-/
theorem RCLike.sqrt_I : sqrt (I : 𝕜) = √2⁻¹ * (1 - I) * I := by
  rw [sqrt_eq_ite]
  split_ifs with h
  · simp_rw [RingEquiv.symm_apply_eq, map_mul]
    simp [h, mul_assoc, mul_add, add_comm, Complex.sqrt_I, add_mul]
  grind [I_eq_zero_or_im_I_eq_one]

/--
theorem `RCLike.sqrt_neg_I` / 定理 `RCLike.sqrt_neg_I`

English:
theorem RCLike.sqrt_neg_I
  statement: sqrt (-I : 𝕜) = √2⁻¹ * (1 + I) * -I
  proof: by
  rw [sqrt_eq_ite]
  split_ifs with h
  · simp_rw [RingEquiv.symm_apply_eq, map_mul]
    simp [h, mul_assoc, add_comm, Complex.sqrt_neg_I, neg_mul, mul_add, add_mul, mul_sub,
      mul_comm Complex.I, ← sub_eq_add_neg]
  grind [I_eq_zero_or_im_I_eq_one]

中文:
定理 RCLike.sqrt_neg_I
  结论: sqrt (-I : 𝕜) = √2⁻¹ * (1 + I) * -I
  证明: by
  rw [sqrt_eq_ite]
  split_ifs with h
  · simp_rw [RingEquiv.symm_apply_eq, map_mul]
    simp [h, mul_assoc, add_comm, Complex.sqrt_neg_I, neg_mul, mul_add, add_mul, mul_sub,
      mul_comm Complex.I, ← sub_eq_add_neg]
  grind [I_eq_zero_or_im_I_eq_one]

Depends on / 依赖: Complex.I, Complex.sqrt_neg_I, I_eq_zero_or_im_I_eq_one, RingEquiv, RingEquiv.symm_apply_eq, add_comm, add_mul, map_mul, mul_add, mul_assoc, mul_comm, mul_sub, neg_mul, simp_rw, split_ifs, sqrt_eq_ite, sqrt_neg_I, sub_eq_add_neg, symm_apply_eq
-/
theorem RCLike.sqrt_neg_I : sqrt (-I : 𝕜) = √2⁻¹ * (1 + I) * -I := by
  rw [sqrt_eq_ite]
  split_ifs with h
  · simp_rw [RingEquiv.symm_apply_eq, map_mul]
    simp [h, mul_assoc, add_comm, Complex.sqrt_neg_I, neg_mul, mul_add, add_mul, mul_sub,
      mul_comm Complex.I, ← sub_eq_add_neg]
  grind [I_eq_zero_or_im_I_eq_one]
