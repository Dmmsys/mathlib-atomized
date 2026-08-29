/-
Copyright (c) 2025 Ilmārs Cīrulis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilmārs Cīrulis, Alex Meiburg
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Sign.Defs

/-!
# Normalized vector

Function that returns unit length vector that points in the same direction
(if the given vector is nonzero vector) or returns zero vector
(if the given vector is zero vector).
-/

@[expose] public section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]

/--
Definition of `NormedSpace.normalize` / `NormedSpace.normalize` 的定义

English:
definition NormedSpace.normalize
  signature: (x : V)
  body: ‖x‖⁻¹ • x

中文:
定义 NormedSpace.normalize
  签名: (x : V)
  定义体: ‖x‖⁻¹ • x
-/
noncomputable def NormedSpace.normalize (x : V) : V := ‖x‖⁻¹ • x

namespace NormedSpace

@[simp]
/--
theorem `normalize_zero_eq_zero` / 定理 `normalize_zero_eq_zero`

English:
theorem normalize_zero_eq_zero
  statement: normalize (0 : V) = 0
  proof: by
  simp [normalize]

@[simp]

中文:
定理 normalize_zero_eq_zero
  结论: normalize (0 : V) = 0
  证明: by
  simp [normalize]

@[simp]

Depends on / 依赖: normalize
-/
theorem normalize_zero_eq_zero : normalize (0 : V) = 0 := by
  simp [normalize]

@[simp]
/--
theorem `normalize_eq_zero_iff` / 定理 `normalize_eq_zero_iff`

English:
theorem normalize_eq_zero_iff
  given: (x : V)
  statement: normalize x = 0 ↔ x = 0
  proof: by
  by_cases hx : x = 0 <;> simp [normalize, hx]

@[simp]

中文:
定理 normalize_eq_zero_iff
  条件: (x : V)
  结论: normalize x = 0 ↔ x = 0
  证明: by
  by_cases hx : x = 0 <;> simp [normalize, hx]

@[simp]

Depends on / 依赖: normalize
-/
theorem normalize_eq_zero_iff (x : V) : normalize x = 0 ↔ x = 0 := by
  by_cases hx : x = 0 <;> simp [normalize, hx]

@[simp]
/--
theorem `norm_smul_normalize` / 定理 `norm_smul_normalize`

English:
theorem norm_smul_normalize
  given: (x : V)
  statement: ‖x‖ • normalize x = x
  proof: by
  by_cases hx : x = 0 <;> simp [normalize, hx]

@[simp]

中文:
定理 norm_smul_normalize
  条件: (x : V)
  结论: ‖x‖ • normalize x = x
  证明: by
  by_cases hx : x = 0 <;> simp [normalize, hx]

@[simp]

Depends on / 依赖: normalize
-/
theorem norm_smul_normalize (x : V) : ‖x‖ • normalize x = x := by
  by_cases hx : x = 0 <;> simp [normalize, hx]

@[simp]
/--
lemma `norm_normalize_eq_one_iff` / 引理 `norm_normalize_eq_one_iff`

English:
lemma norm_normalize_eq_one_iff
  given: {x : V}
  statement: ‖normalize x‖ = 1 ↔ x != 0
  proof: by
  by_cases hx : x = 0 <;> simp [normalize, hx, norm_smul]

alias ⟨_, norm_normalize⟩ := norm_normalize_eq_one_iff

中文:
引理 norm_normalize_eq_one_iff
  条件: {x : V}
  结论: ‖normalize x‖ = 1 ↔ x != 0
  证明: by
  by_cases hx : x = 0 <;> simp [normalize, hx, norm_smul]

alias ⟨_, norm_normalize⟩ := norm_normalize_eq_one_iff

Depends on / 依赖: norm_smul, normalize
-/
lemma norm_normalize_eq_one_iff {x : V} : ‖normalize x‖ = 1 ↔ x != 0 := by
  by_cases hx : x = 0 <;> simp [normalize, hx, norm_smul]

alias ⟨_, norm_normalize⟩ := norm_normalize_eq_one_iff

/--
lemma `normalize_eq_self_of_norm_eq_one` / 引理 `normalize_eq_self_of_norm_eq_one`

English:
lemma normalize_eq_self_of_norm_eq_one
  given: {x : V} (h : ‖x‖ = 1)
  statement: normalize x = x
  proof: by
  simp [normalize, h]

@[simp]

中文:
引理 normalize_eq_self_of_norm_eq_one
  条件: {x : V} (h : ‖x‖ = 1)
  结论: normalize x = x
  证明: by
  simp [normalize, h]

@[simp]

Depends on / 依赖: normalize
-/
lemma normalize_eq_self_of_norm_eq_one {x : V} (h : ‖x‖ = 1) : normalize x = x := by
  simp [normalize, h]

@[simp]
/--
theorem `normalize_normalize` / 定理 `normalize_normalize`

English:
theorem normalize_normalize
  given: (x : V)
  statement: normalize (normalize x) = normalize x
  proof: by
  by_cases hx : x = 0
  · simp [hx]
  · simp [normalize_eq_self_of_norm_eq_one, hx]

@[simp]

中文:
定理 normalize_normalize
  条件: (x : V)
  结论: normalize (normalize x) = normalize x
  证明: by
  by_cases hx : x = 0
  · simp [hx]
  · simp [normalize_eq_self_of_norm_eq_one, hx]

@[simp]

Depends on / 依赖: normalize_eq_self_of_norm_eq_one
-/
theorem normalize_normalize (x : V) : normalize (normalize x) = normalize x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [normalize_eq_self_of_norm_eq_one, hx]

@[simp]
/--
theorem `normalize_neg` / 定理 `normalize_neg`

English:
theorem normalize_neg
  given: (x : V)
  statement: normalize (-x) = - normalize x
  proof: by
  simp [normalize]

中文:
定理 normalize_neg
  条件: (x : V)
  结论: normalize (-x) = - normalize x
  证明: by
  simp [normalize]

Depends on / 依赖: normalize
-/
theorem normalize_neg (x : V) : normalize (-x) = - normalize x := by
  simp [normalize]

/--
theorem `normalize_smul_of_pos` / 定理 `normalize_smul_of_pos`

English:
theorem normalize_smul_of_pos
  given: {r : Real} (hr : 0 < r) (x : V)
  proof: by
  simp [normalize, norm_smul, smul_smul, abs_of_pos hr, hr.ne']

中文:
定理 normalize_smul_of_pos
  条件: {r : 实数} (hr : 0 < r) (x : V)
  证明: by
  simp [normalize, norm_smul, smul_smul, abs_of_pos hr, hr.ne']

Depends on / 依赖: abs_of_pos, hr.ne, norm_smul, normalize, smul_smul
-/
theorem normalize_smul_of_pos {r : Real} (hr : 0 < r) (x : V) :
    normalize (r • x) = normalize x := by
  simp [normalize, norm_smul, smul_smul, abs_of_pos hr, hr.ne']

/--
theorem `normalize_smul_of_neg` / 定理 `normalize_smul_of_neg`

English:
theorem normalize_smul_of_neg
  given: {r : Real} (hr : r < 0) (x : V)
  proof: by
  simpa using normalize_smul_of_pos (show 0 < -r by linarith) (-x)

中文:
定理 normalize_smul_of_neg
  条件: {r : 实数} (hr : r < 0) (x : V)
  证明: by
  simpa using normalize_smul_of_pos (show 0 < -r by linarith) (-x)

Depends on / 依赖: normalize_smul_of_pos
-/
theorem normalize_smul_of_neg {r : Real} (hr : r < 0) (x : V) :
    normalize (r • x) = - normalize x := by
  simpa using normalize_smul_of_pos (show 0 < -r by linarith) (-x)

/--
theorem `normalize_smul` / 定理 `normalize_smul`

English:
theorem normalize_smul
  given: (r : Real) (x : V)
  proof: by
  rcases lt_trichotomy 0 r with (h_pos | rfl | h_neg)
  · simp [normalize_smul_of_pos, h_pos]
  · simp
  · simp [normalize_smul_of_neg, h_neg]

中文:
定理 normalize_smul
  条件: (r : 实数) (x : V)
  证明: by
  rcases lt_trichotomy 0 r with (h_pos | rfl | h_neg)
  · simp [normalize_smul_of_pos, h_pos]
  · simp
  · simp [normalize_smul_of_neg, h_neg]

Depends on / 依赖: h_neg, h_pos, lt_trichotomy, normalize_smul_of_neg, normalize_smul_of_pos
-/
theorem normalize_smul (r : Real) (x : V) :
    normalize (r • x) = (SignType.sign r : Real) • normalize x := by
  rcases lt_trichotomy 0 r with (h_pos | rfl | h_neg)
  · simp [normalize_smul_of_pos, h_pos]
  · simp
  · simp [normalize_smul_of_neg, h_neg]

end NormedSpace
