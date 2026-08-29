/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Inverse of the tanh function

In this file we define an inverse of tanh as a function from ℝ to (-1, 1).

## Main definitions

- `Real.artanh`: An inverse function of `Real.tanh` as a function from ℝ to (-1, 1).

- `Real.tanhPartialEquiv`: `Real.tanh` and `Real.artanh` bundled as a `PartialEquiv`
  from ℝ to (-1, 1).

## Main Results

- `Real.tanh_artanh`, `Real.artanh_tanh`: tanh and artanh are inverse in the appropriate domains.

- `Real.tanh_bijOn`, `Real.tanh_injective`, `Real.tanh_surjOn`: `Real.tanh` is
  bijective, injective and surjective as a function from ℝ to (-1, 1)

- `Real.artanh_bijOn`, `Real.artanh_injOn`, `Real.artanh_surjOn`: `Real.artanh` is bijective,
  injective and surjective as a function from (-1, 1) to ℝ

## Tags

artanh, arctanh, argtanh, atanh
-/

@[expose] public section


noncomputable section

open Function Filter Set

open scoped Topology

namespace Real

variable {x y : Real}

/-- `artanh` is defined using a logarithm, `artanh x = log √((1 + x) / (1 - x))`. -/
@[pp_nodot]
/--
Definition of `artanh` / `artanh` 的定义

English:
definition artanh
  signature: (x : Real)
  body: log √((1 + x) / (1 - x))

中文:
定义 artanh
  签名: (x : 实数)
  定义体: log √((1 + x) / (1 - x))
-/
def artanh (x : Real) :=
  log √((1 + x) / (1 - x))

/--
theorem `artanh_eq_half_log` / 定理 `artanh_eq_half_log`

English:
theorem artanh_eq_half_log
  given: {x : Real} (hx : x in Icc (-1) 1)
  proof: by
  rw [artanh]; rw [log_sqrt <| div_nonneg (by grind) (by grind)]; rw [one_div_mul_eq_div]

中文:
定理 artanh_eq_half_log
  条件: {x : 实数} (hx : x in Icc (-1) 1)
  证明: by
  rw [artanh]; rw [log_sqrt <| div_nonneg (by grind) (by grind)]; rw [one_div_mul_eq_div]

Depends on / 依赖: artanh, div_nonneg, log_sqrt, one_div_mul_eq_div
-/
theorem artanh_eq_half_log {x : Real} (hx : x in Icc (-1) 1) :
    artanh x = 1 / 2 * log ((1 + x) / (1 - x)) := by
  rw [artanh]; rw [log_sqrt <| div_nonneg (by grind) (by grind)]; rw [one_div_mul_eq_div]

/--
theorem `exp_artanh` / 定理 `exp_artanh`

English:
theorem exp_artanh
  given: {x : Real} (hx : x in Ioo (-1) 1)
  statement: exp (artanh x) = √((1 + x) / (1 - x))
  proof: exp_log sqrt_pos_of_pos div_pos (by grind) (by grind)

@[simp]

中文:
定理 exp_artanh
  条件: {x : 实数} (hx : x in Ioo (-1) 1)
  结论: exp (artanh x) = √((1 + x) / (1 - x))
  证明: exp_log sqrt_pos_of_pos div_pos (by grind) (by grind)

@[simp]

Depends on / 依赖: div_pos, exp_log, sqrt_pos_of_pos
-/
theorem exp_artanh {x : Real} (hx : x in Ioo (-1) 1) : exp (artanh x) = √((1 + x) / (1 - x)) :=
exp_log sqrt_pos_of_pos div_pos (by grind) (by grind)

@[simp]
/--
theorem `artanh_zero` / 定理 `artanh_zero`

English:
theorem artanh_zero
  statement: artanh 0 = 0
  proof: by simp [artanh]

中文:
定理 artanh_zero
  结论: artanh 0 = 0
  证明: by simp [artanh]

Depends on / 依赖: artanh
-/
theorem artanh_zero : artanh 0 = 0 := by simp [artanh]

/--
theorem `sinh_artanh` / 定理 `sinh_artanh`

English:
theorem sinh_artanh
  given: {x : Real} (hx : x in Ioo (-1) 1)
  statement: sinh (artanh x) = x / √(1 - x ^ 2)
  proof: by
have : 0 < √((1 + x) / (1 - x)) := sqrt_pos_of_pos div_pos (by grind) (by grind)
  rw [← one_pow]; rw [sq_sub_sq 1 x]; rw [sqrt_mul]
    <;> grind [artanh, sinh_eq, exp_neg, exp_log, sqrt_div]

中文:
定理 sinh_artanh
  条件: {x : 实数} (hx : x in Ioo (-1) 1)
  结论: sinh (artanh x) = x / √(1 - x ^ 2)
  证明: by
have : 0 < √((1 + x) / (1 - x)) := sqrt_pos_of_pos div_pos (by grind) (by grind)
  rw [← one_pow]; rw [sq_sub_sq 1 x]; rw [sqrt_mul]
    <;> grind [artanh, sinh_eq, exp_neg, exp_log, sqrt_div]

Depends on / 依赖: artanh, div_pos, exp_log, exp_neg, one_pow, sinh_eq, sq_sub_sq, sqrt_div, sqrt_mul, sqrt_pos_of_pos
-/
theorem sinh_artanh {x : Real} (hx : x in Ioo (-1) 1) : sinh (artanh x) = x / √(1 - x ^ 2) := by
have : 0 < √((1 + x) / (1 - x)) := sqrt_pos_of_pos div_pos (by grind) (by grind)
  rw [← one_pow]; rw [sq_sub_sq 1 x]; rw [sqrt_mul]
    <;> grind [artanh, sinh_eq, exp_neg, exp_log, sqrt_div]

/--
theorem `cosh_artanh` / 定理 `cosh_artanh`

English:
theorem cosh_artanh
  given: {x : Real} (hx : x in Ioo (-1) 1)
  statement: cosh (artanh x) = 1 / √(1 - x ^ 2)
  proof: by
have : 0 < √((1 + x) / (1 - x)) := sqrt_pos_of_pos div_pos (by grind) (by grind)
  rw [← one_pow]; rw [sq_sub_sq 1 x]; rw [sqrt_mul]
    <;> grind [artanh, cosh_eq, exp_neg, exp_log, sqrt_div]

中文:
定理 cosh_artanh
  条件: {x : 实数} (hx : x in Ioo (-1) 1)
  结论: cosh (artanh x) = 1 / √(1 - x ^ 2)
  证明: by
have : 0 < √((1 + x) / (1 - x)) := sqrt_pos_of_pos div_pos (by grind) (by grind)
  rw [← one_pow]; rw [sq_sub_sq 1 x]; rw [sqrt_mul]
    <;> grind [artanh, cosh_eq, exp_neg, exp_log, sqrt_div]

Depends on / 依赖: artanh, cosh_eq, div_pos, exp_log, exp_neg, one_pow, sq_sub_sq, sqrt_div, sqrt_mul, sqrt_pos_of_pos
-/
theorem cosh_artanh {x : Real} (hx : x in Ioo (-1) 1) : cosh (artanh x) = 1 / √(1 - x ^ 2) := by
have : 0 < √((1 + x) / (1 - x)) := sqrt_pos_of_pos div_pos (by grind) (by grind)
  rw [← one_pow]; rw [sq_sub_sq 1 x]; rw [sqrt_mul]
    <;> grind [artanh, cosh_eq, exp_neg, exp_log, sqrt_div]

/--
theorem `tanh_artanh` / 定理 `tanh_artanh`

English:
theorem tanh_artanh
  given: {x : Real} (hx : x in Ioo (-1) 1)
  statement: tanh (artanh x) = x
  proof: by
  have := sq_sub_sq 1 x
  grind [tanh_eq_sinh_div_cosh, sinh_artanh, cosh_artanh, sqrt_ne_zero', mul_pos]

中文:
定理 tanh_artanh
  条件: {x : 实数} (hx : x in Ioo (-1) 1)
  结论: tanh (artanh x) = x
  证明: by
  have := sq_sub_sq 1 x
  grind [tanh_eq_sinh_div_cosh, sinh_artanh, cosh_artanh, sqrt_ne_zero', mul_pos]

Depends on / 依赖: cosh_artanh, mul_pos, sinh_artanh, sq_sub_sq, sqrt_ne_zero, tanh_eq_sinh_div_cosh
-/
theorem tanh_artanh {x : Real} (hx : x in Ioo (-1) 1) : tanh (artanh x) = x := by
  have := sq_sub_sq 1 x
  grind [tanh_eq_sinh_div_cosh, sinh_artanh, cosh_artanh, sqrt_ne_zero', mul_pos]

/--
theorem `artanh_tanh` / 定理 `artanh_tanh`

English:
theorem artanh_tanh
  given: (x : Real)
  statement: artanh (tanh x) = x
  proof: by
  have h : 0 < (1 + tanh x) / (1 - tanh x) :=
    div_pos (by grind [neg_one_lt_tanh]) (by grind [tanh_lt_one])
  rw [artanh]; rw [← exp_eq_exp]; rw [exp_log (sqrt_pos_of_pos h)]; rw [← sq_eq_sq₀ (le_of_lt <| sqrt_pos_of_pos h) (exp_nonneg x)]; rw [sq_sqrt (le_of_lt h)]; rw [tanh_eq]; rw [exp_neg

中文:
定理 artanh_tanh
  条件: (x : 实数)
  结论: artanh (tanh x) = x
  证明: by
  have h : 0 < (1 + tanh x) / (1 - tanh x) :=
    div_pos (by grind [neg_one_lt_tanh]) (by grind [tanh_lt_one])
  rw [artanh]; rw [← exp_eq_exp]; rw [exp_log (sqrt_pos_of_pos h)]; rw [← sq_eq_sq₀ (le_of_lt <| sqrt_pos_of_pos h) (exp_nonneg x)]; rw [sq_sqrt (le_of_lt h)]; rw [tanh_eq]; rw [exp_neg

Depends on / 依赖: artanh, div_pos, exp_eq_exp, exp_log, exp_neg, exp_nonneg, le_of_lt, neg_one_lt_tanh, sq_sqrt, sqrt_pos_of_pos, tanh_eq, tanh_lt_one
-/
theorem artanh_tanh (x : Real) : artanh (tanh x) = x := by
  have h : 0 < (1 + tanh x) / (1 - tanh x) :=
    div_pos (by grind [neg_one_lt_tanh]) (by grind [tanh_lt_one])
  rw [artanh]; rw [← exp_eq_exp]; rw [exp_log (sqrt_pos_of_pos h)]; rw [← sq_eq_sq₀ (le_of_lt <| sqrt_pos_of_pos h) (exp_nonneg x)]; rw [sq_sqrt (le_of_lt h)]; rw [tanh_eq]; rw [exp_neg]
  field

/--
theorem `strictMonoOn_one_add_div_one_sub` / 定理 `strictMonoOn_one_add_div_one_sub`

English:
theorem strictMonoOn_one_add_div_one_sub
  proof: by
  intro x hx y hy h
  field_simp [show 0 < 1 - x by grind, show 0 < 1 - y by grind]
  grind

中文:
定理 strictMonoOn_one_add_div_one_sub
  证明: by
  intro x hx y hy h
  field_simp [show 0 < 1 - x by grind, show 0 < 1 - y by grind]
  grind
-/
theorem strictMonoOn_one_add_div_one_sub :
    StrictMonoOn (fun (x : Real) => (1 + x) / (1 - x)) (Ioo (-1) 1) := by
  intro x hx y hy h
  field_simp [show 0 < 1 - x by grind, show 0 < 1 - y by grind]
  grind

/--
theorem `strictMonoOn_artanh` / 定理 `strictMonoOn_artanh`

English:
theorem strictMonoOn_artanh
  statement: StrictMonoOn artanh (Ioo (-1) 1)
  proof: by
apply strictMonoOn_log.comp ?_ fun x hx => sqrt_pos_of_pos div_pos (by grind) (by grind)
  apply strictMonoOn_sqrt.comp strictMonoOn_one_add_div_one_sub
    fun x hx => show 0 <= (1 + x) / (1 - x) by exact div_nonneg (by grind) (by grind)

中文:
定理 strictMonoOn_artanh
  结论: StrictMonoOn artanh (Ioo (-1) 1)
  证明: by
apply strictMonoOn_log.comp ?_ fun x hx => sqrt_pos_of_pos div_pos (by grind) (by grind)
  apply strictMonoOn_sqrt.comp strictMonoOn_one_add_div_one_sub
    fun x hx => show 0 <= (1 + x) / (1 - x) by exact div_nonneg (by grind) (by grind)

Depends on / 依赖: div_nonneg, div_pos, sqrt_pos_of_pos, strictMonoOn_log, strictMonoOn_log.comp, strictMonoOn_one_add_div_one_sub, strictMonoOn_sqrt, strictMonoOn_sqrt.comp
-/
theorem strictMonoOn_artanh : StrictMonoOn artanh (Ioo (-1) 1) := by
apply strictMonoOn_log.comp ?_ fun x hx => sqrt_pos_of_pos div_pos (by grind) (by grind)
  apply strictMonoOn_sqrt.comp strictMonoOn_one_add_div_one_sub
    fun x hx => show 0 <= (1 + x) / (1 - x) by exact div_nonneg (by grind) (by grind)

/--
theorem `artanh_le_artanh_iff` / 定理 `artanh_le_artanh_iff`

English:
theorem artanh_le_artanh_iff
  given: {x y : Real} (hx : x in Ioo (-1) 1) (hy : y in Ioo (-1) 1)
  proof: strictMonoOn_artanh.le_iff_le hx hy

中文:
定理 artanh_le_artanh_iff
  条件: {x y : 实数} (hx : x in Ioo (-1) 1) (hy : y in Ioo (-1) 1)
  证明: strictMonoOn_artanh.le_iff_le hx hy

Depends on / 依赖: le_iff_le, strictMonoOn_artanh, strictMonoOn_artanh.le_iff_le
-/
theorem artanh_le_artanh_iff {x y : Real} (hx : x in Ioo (-1) 1) (hy : y in Ioo (-1) 1) :
    artanh x <= artanh y ↔ x <= y :=
  strictMonoOn_artanh.le_iff_le hx hy

/--
theorem `artanh_lt_artanh_iff` / 定理 `artanh_lt_artanh_iff`

English:
theorem artanh_lt_artanh_iff
  given: {x y : Real} (hx : x in Ioo (-1) 1) (hy : y in Ioo (-1) 1)
  proof: strictMonoOn_artanh.lt_iff_lt hx hy

中文:
定理 artanh_lt_artanh_iff
  条件: {x y : 实数} (hx : x in Ioo (-1) 1) (hy : y in Ioo (-1) 1)
  证明: strictMonoOn_artanh.lt_iff_lt hx hy

Depends on / 依赖: lt_iff_lt, strictMonoOn_artanh, strictMonoOn_artanh.lt_iff_lt
-/
theorem artanh_lt_artanh_iff {x y : Real} (hx : x in Ioo (-1) 1) (hy : y in Ioo (-1) 1) :
    artanh x < artanh y ↔ x < y :=
  strictMonoOn_artanh.lt_iff_lt hx hy

/--
theorem `artanh_le_artanh` / 定理 `artanh_le_artanh`

English:
theorem artanh_le_artanh
  given: {x y : Real} (hx : -1 < x) (hy : y < 1) (hxy : x <= y)
  proof: (artanh_le_artanh_iff (by grind) (by grind)).mpr hxy

中文:
定理 artanh_le_artanh
  条件: {x y : 实数} (hx : -1 < x) (hy : y < 1) (hxy : x <= y)
  证明: (artanh_le_artanh_iff (by grind) (by grind)).mpr hxy

Depends on / 依赖: artanh_le_artanh_iff
-/
theorem artanh_le_artanh {x y : Real} (hx : -1 < x) (hy : y < 1) (hxy : x <= y) :
    artanh x <= artanh y :=
  (artanh_le_artanh_iff (by grind) (by grind)).mpr hxy

/--
theorem `artanh_lt_artanh` / 定理 `artanh_lt_artanh`

English:
theorem artanh_lt_artanh
  given: {x y : Real} (hx : -1 < x) (hy : y < 1) (hxy : x < y)
  proof: (artanh_lt_artanh_iff (by grind) (by grind)).mpr hxy

中文:
定理 artanh_lt_artanh
  条件: {x y : 实数} (hx : -1 < x) (hy : y < 1) (hxy : x < y)
  证明: (artanh_lt_artanh_iff (by grind) (by grind)).mpr hxy

Depends on / 依赖: artanh_lt_artanh_iff
-/
theorem artanh_lt_artanh {x y : Real} (hx : -1 < x) (hy : y < 1) (hxy : x < y) :
    artanh x < artanh y :=
  (artanh_lt_artanh_iff (by grind) (by grind)).mpr hxy

/--
theorem `artanh_eq_zero_iff` / 定理 `artanh_eq_zero_iff`

English:
theorem artanh_eq_zero_iff
  given: {x : Real}
  statement: artanh x = 0 ↔ x <= -1 ∨ x = 0 ∨ 1 <= x
  proof: by
  grind [artanh, log_eq_zero, div_nonpos_iff]

中文:
定理 artanh_eq_zero_iff
  条件: {x : 实数}
  结论: artanh x = 0 ↔ x <= -1 ∨ x = 0 ∨ 1 <= x
  证明: by
  grind [artanh, log_eq_zero, div_nonpos_iff]

Depends on / 依赖: artanh, div_nonpos_iff, log_eq_zero
-/
theorem artanh_eq_zero_iff {x : Real} : artanh x = 0 ↔ x <= -1 ∨ x = 0 ∨ 1 <= x := by
  grind [artanh, log_eq_zero, div_nonpos_iff]

/--
theorem `artanh_pos` / 定理 `artanh_pos`

English:
theorem artanh_pos
  given: {x : Real} (hx : x in Ioo 0 1)
  statement: 0 < artanh x
  proof: by
  rw [← artanh_zero]; rw [artanh_lt_artanh_iff (by grind) (by grind)]
  exact hx.1

中文:
定理 artanh_pos
  条件: {x : 实数} (hx : x in Ioo 0 1)
  结论: 0 < artanh x
  证明: by
  rw [← artanh_zero]; rw [artanh_lt_artanh_iff (by grind) (by grind)]
  exact hx.1

Depends on / 依赖: artanh_lt_artanh_iff, artanh_zero
-/
theorem artanh_pos {x : Real} (hx : x in Ioo 0 1) : 0 < artanh x := by
  rw [← artanh_zero]; rw [artanh_lt_artanh_iff (by grind) (by grind)]
  exact hx.1

/--
theorem `artanh_neg` / 定理 `artanh_neg`

English:
theorem artanh_neg
  given: {x : Real} (hx : x in Ioo (-1) 0)
  statement: artanh x < 0
  proof: by
  rw [← artanh_zero]; rw [artanh_lt_artanh_iff (by grind) (by grind)]
  exact hx.2

中文:
定理 artanh_neg
  条件: {x : 实数} (hx : x in Ioo (-1) 0)
  结论: artanh x < 0
  证明: by
  rw [← artanh_zero]; rw [artanh_lt_artanh_iff (by grind) (by grind)]
  exact hx.2

Depends on / 依赖: artanh_lt_artanh_iff, artanh_zero
-/
theorem artanh_neg {x : Real} (hx : x in Ioo (-1) 0) : artanh x < 0 := by
  rw [← artanh_zero]; rw [artanh_lt_artanh_iff (by grind) (by grind)]
  exact hx.2

/--
theorem `artanh_nonneg` / 定理 `artanh_nonneg`

English:
theorem artanh_nonneg
  given: {x : Real} (hx : 0 <= x)
  statement: 0 <= artanh x
  proof: by
  by_cases x < 1
  case pos =>
    rw [← artanh_zero]; rw [artanh_le_artanh_iff (by grind) (by grind)]
    exact hx
  case neg => grind [artanh_eq_zero_iff]

中文:
定理 artanh_nonneg
  条件: {x : 实数} (hx : 0 <= x)
  结论: 0 <= artanh x
  证明: by
  by_cases x < 1
  case pos =>
    rw [← artanh_zero]; rw [artanh_le_artanh_iff (by grind) (by grind)]
    exact hx
  case neg => grind [artanh_eq_zero_iff]

Depends on / 依赖: artanh_eq_zero_iff, artanh_le_artanh_iff, artanh_zero
-/
theorem artanh_nonneg {x : Real} (hx : 0 <= x) : 0 <= artanh x := by
  by_cases x < 1
  case pos =>
    rw [← artanh_zero]; rw [artanh_le_artanh_iff (by grind) (by grind)]
    exact hx
  case neg => grind [artanh_eq_zero_iff]

/--
theorem `artanh_nonpos` / 定理 `artanh_nonpos`

English:
theorem artanh_nonpos
  given: {x : Real} (hx : x <= 0)
  statement: artanh x <= 0
  proof: by
  by_cases -1 < x
  case pos =>
    rw [← artanh_zero]; rw [artanh_le_artanh_iff (by grind) (by grind)]
    exact hx
  case neg => grind [artanh_eq_zero_iff]

中文:
定理 artanh_nonpos
  条件: {x : 实数} (hx : x <= 0)
  结论: artanh x <= 0
  证明: by
  by_cases -1 < x
  case pos =>
    rw [← artanh_zero]; rw [artanh_le_artanh_iff (by grind) (by grind)]
    exact hx
  case neg => grind [artanh_eq_zero_iff]

Depends on / 依赖: artanh_eq_zero_iff, artanh_le_artanh_iff, artanh_zero
-/
theorem artanh_nonpos {x : Real} (hx : x <= 0) : artanh x <= 0 := by
  by_cases -1 < x
  case pos =>
    rw [← artanh_zero]; rw [artanh_le_artanh_iff (by grind) (by grind)]
    exact hx
  case neg => grind [artanh_eq_zero_iff]

/--
Definition of `tanhPartialEquiv` / `tanhPartialEquiv` 的定义

English:
definition tanhPartialEquiv
  signature: : PartialEquiv Real Real where
  body: tanh
  invFun := artanh
  source := univ
  target := Ioo (-1) 1
  map_source' r _ := mem_Ioo.mpr ⟨neg_one_lt_tanh r, tanh_lt_one r⟩
  map_target' _ _ := trivial
  left_inv' r _ := artanh_tanh r
  right_inv' _ hr := tanh_artanh hr

中文:
定义 tanhPartialEquiv
  签名: : PartialEquiv 实数 实数 where
  定义体: tanh
  invFun := artanh
  source := univ
  target := Ioo (-1) 1
  map_source' r _ := mem_Ioo.mpr ⟨neg_one_lt_tanh r, tanh_lt_one r⟩
  map_target' _ _ := trivial
  left_inv' r _ := artanh_tanh r
  right_inv' _ hr := tanh_artanh hr
-/
def tanhPartialEquiv : PartialEquiv Real Real where
  toFun := tanh
  invFun := artanh
  source := univ
  target := Ioo (-1) 1
  map_source' r _ := mem_Ioo.mpr ⟨neg_one_lt_tanh r, tanh_lt_one r⟩
  map_target' _ _ := trivial
  left_inv' r _ := artanh_tanh r
  right_inv' _ hr := tanh_artanh hr

/--
theorem `tanh_bijOn` / 定理 `tanh_bijOn`

English:
theorem tanh_bijOn
  statement: BijOn tanh univ (Ioo (-1) 1)
  proof: tanhPartialEquiv.bijOn

中文:
定理 tanh_bijOn
  结论: BijOn tanh univ (Ioo (-1) 1)
  证明: tanhPartialEquiv.bijOn

Depends on / 依赖: tanhPartialEquiv, tanhPartialEquiv.bijOn
-/
theorem tanh_bijOn : BijOn tanh univ (Ioo (-1) 1) := tanhPartialEquiv.bijOn

/--
theorem `tanh_injective` / 定理 `tanh_injective`

English:
theorem tanh_injective
  statement: Injective tanh
  proof: fun _ _ => tanhPartialEquiv.injOn trivial trivial

中文:
定理 tanh_injective
  结论: Injective tanh
  证明: fun _ _ => tanhPartialEquiv.injOn trivial trivial

Depends on / 依赖: tanhPartialEquiv, tanhPartialEquiv.injOn
-/
theorem tanh_injective : Injective tanh := fun _ _ => tanhPartialEquiv.injOn trivial trivial

/--
theorem `tanh_surjOn` / 定理 `tanh_surjOn`

English:
theorem tanh_surjOn
  statement: SurjOn tanh univ (Ioo (-1) 1)
  proof: tanhPartialEquiv.surjOn

中文:
定理 tanh_surjOn
  结论: SurjOn tanh univ (Ioo (-1) 1)
  证明: tanhPartialEquiv.surjOn

Depends on / 依赖: surjOn, tanhPartialEquiv, tanhPartialEquiv.surjOn
-/
theorem tanh_surjOn : SurjOn tanh univ (Ioo (-1) 1) := tanhPartialEquiv.surjOn

/--
theorem `artanh_bijOn` / 定理 `artanh_bijOn`

English:
theorem artanh_bijOn
  statement: BijOn artanh (Ioo (-1) 1) univ
  proof: tanhPartialEquiv.symm.bijOn

中文:
定理 artanh_bijOn
  结论: BijOn artanh (Ioo (-1) 1) univ
  证明: tanhPartialEquiv.symm.bijOn

Depends on / 依赖: tanhPartialEquiv, tanhPartialEquiv.symm.bijOn
-/
theorem artanh_bijOn : BijOn artanh (Ioo (-1) 1) univ := tanhPartialEquiv.symm.bijOn

/--
theorem `artanh_injOn` / 定理 `artanh_injOn`

English:
theorem artanh_injOn
  statement: InjOn artanh (Ioo (-1) 1)
  proof: tanhPartialEquiv.symm.injOn

中文:
定理 artanh_injOn
  结论: InjOn artanh (Ioo (-1) 1)
  证明: tanhPartialEquiv.symm.injOn

Depends on / 依赖: tanhPartialEquiv, tanhPartialEquiv.symm.injOn
-/
theorem artanh_injOn : InjOn artanh (Ioo (-1) 1) := tanhPartialEquiv.symm.injOn

/--
theorem `artanh_surjOn` / 定理 `artanh_surjOn`

English:
theorem artanh_surjOn
  statement: SurjOn artanh (Ioo (-1) 1) univ
  proof: tanhPartialEquiv.symm.surjOn

中文:
定理 artanh_surjOn
  结论: SurjOn artanh (Ioo (-1) 1) univ
  证明: tanhPartialEquiv.symm.surjOn

Depends on / 依赖: surjOn, tanhPartialEquiv, tanhPartialEquiv.symm.surjOn
-/
theorem artanh_surjOn : SurjOn artanh (Ioo (-1) 1) univ := tanhPartialEquiv.symm.surjOn

end Real
