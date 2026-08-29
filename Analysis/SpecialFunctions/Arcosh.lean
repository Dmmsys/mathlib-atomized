/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Inverse of the cosh function

In this file we define an inverse of cosh as a function from $[0, ∞)$ to $[1, ∞)$.

## Main definitions

- `Real.arcosh`: An inverse function of `Real.cosh` as a function from $[0, ∞)$ to $[1, ∞)$.

- `Real.coshPartialEquiv`: `Real.cosh` and `Real.arcosh` bundled as a `PartialEquiv`
  from $[0, ∞)$ to $[1, ∞)$.

- `Real.coshOpenPartialHomeomorph`: `Real.cosh` as an `OpenPartialHomeomorph` from $(0, ∞)$ to
  $(1, ∞)$.

## Main Results

- `Real.cosh_arcosh`, `Real.arcosh_cosh`: cosh and arcosh are inverse in the appropriate domains.

- `Real.cosh_bijOn`, `Real.cosh_injOn`, `Real.cosh_surjOn`: `Real.cosh` is bijective, injective and
  surjective as a function from $[0, ∞)$ to $[1, ∞)$

- `Real.arcosh_bijOn`, `Real.arcosh_injOn`, `Real.arcosh_surjOn`: `Real.arcosh` is bijective,
  injective and surjective as a function from $[1, ∞)$ to $[0, ∞)$

- `Real.continuousOn_arcosh`: arcosh is continuous on $[1, ∞)$

- `Real.differentiableOn_arcosh`, `Real.contDiffOn_arcosh`: `Real.arcosh` is
  differentiable, and continuously differentiable on $(1, ∞)$

## Tags

arcosh, arccosh, argcosh, acosh
-/

@[expose] public section


noncomputable section

open Function Filter Set

open scoped Topology

namespace Real

variable {x y : Real}

/-- `arcosh` is defined using a logarithm, `arcosh x = log (x + √(x ^ 2 - 1))`. -/
@[pp_nodot]
/--
Definition of `arcosh` / `arcosh` 的定义

English:
definition arcosh
  signature: (x : Real)
  body: log (x + √(x ^ 2 - 1))

中文:
定义 arcosh
  签名: (x : 实数)
  定义体: log (x + √(x ^ 2 - 1))
-/
def arcosh (x : Real) :=
  log (x + √(x ^ 2 - 1))

/--
theorem `exp_arcosh` / 定理 `exp_arcosh`

English:
theorem exp_arcosh
  given: {x : Real} (hx : 1 <= x)
  statement: exp (arcosh x) = x + √(x ^ 2 - 1)
  proof: by
  apply exp_log
  positivity

@[simp]

中文:
定理 exp_arcosh
  条件: {x : 实数} (hx : 1 <= x)
  结论: exp (arcosh x) = x + √(x ^ 2 - 1)
  证明: by
  apply exp_log
  positivity

@[simp]

Depends on / 依赖: exp_log
-/
theorem exp_arcosh {x : Real} (hx : 1 <= x) : exp (arcosh x) = x + √(x ^ 2 - 1) := by
  apply exp_log
  positivity

@[simp]
/--
theorem `arcosh_zero` / 定理 `arcosh_zero`

English:
theorem arcosh_zero
  statement: arcosh 1 = 0
  proof: by simp [arcosh]

中文:
定理 arcosh_zero
  结论: arcosh 1 = 0
  证明: by simp [arcosh]

Depends on / 依赖: arcosh
-/
theorem arcosh_zero : arcosh 1 = 0 := by simp [arcosh]

/--
lemma `add_sqrt_self_sq_sub_one_inv` / 引理 `add_sqrt_self_sq_sub_one_inv`

English:
lemma add_sqrt_self_sq_sub_one_inv
  given: {x : Real} (hx : 1 <= x)
  proof: by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_two_sub_pow_two]; rw [sq_sqrt (sub_nonneg_of_le (one_le_pow₀ hx))]; rw [sub_sub_cancel]

中文:
引理 add_sqrt_self_sq_sub_one_inv
  条件: {x : 实数} (hx : 1 <= x)
  证明: by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_two_sub_pow_two]; rw [sq_sqrt (sub_nonneg_of_le (one_le_pow₀ hx))]; rw [sub_sub_cancel]

Depends on / 依赖: inv_eq_of_mul_eq_one_right, pow_two_sub_pow_two, sq_sqrt, sub_nonneg_of_le, sub_sub_cancel
-/
lemma add_sqrt_self_sq_sub_one_inv {x : Real} (hx : 1 <= x) :
    (x + √(x ^ 2 - 1))⁻¹ = x - √(x ^ 2 - 1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_two_sub_pow_two]; rw [sq_sqrt (sub_nonneg_of_le (one_le_pow₀ hx))]; rw [sub_sub_cancel]

/--
theorem `cosh_arcosh` / 定理 `cosh_arcosh`

English:
theorem cosh_arcosh
  given: {x : Real} (hx : 1 <= x)
  statement: cosh (arcosh x) = x
  proof: by
  rw [arcosh]; rw [cosh_eq]; rw [exp_neg]; rw [exp_log (by positivity)]; rw [add_sqrt_self_sq_sub_one_inv hx]
  ring

中文:
定理 cosh_arcosh
  条件: {x : 实数} (hx : 1 <= x)
  结论: cosh (arcosh x) = x
  证明: by
  rw [arcosh]; rw [cosh_eq]; rw [exp_neg]; rw [exp_log (by positivity)]; rw [add_sqrt_self_sq_sub_one_inv hx]
  ring

Depends on / 依赖: add_sqrt_self_sq_sub_one_inv, arcosh, cosh_eq, exp_log, exp_neg
-/
theorem cosh_arcosh {x : Real} (hx : 1 <= x) : cosh (arcosh x) = x := by
  rw [arcosh]; rw [cosh_eq]; rw [exp_neg]; rw [exp_log (by positivity)]; rw [add_sqrt_self_sq_sub_one_inv hx]
  ring

/--
theorem `arcosh_eq_zero_iff` / 定理 `arcosh_eq_zero_iff`

English:
theorem arcosh_eq_zero_iff
  given: {x : Real} (hx : 1 <= x)
  statement: arcosh x = 0 ↔ x = 1
  proof: by
  rw [← exp_injective.eq_iff]; rw [exp_arcosh hx]; rw [exp_zero]
  grind

中文:
定理 arcosh_eq_zero_iff
  条件: {x : 实数} (hx : 1 <= x)
  结论: arcosh x = 0 ↔ x = 1
  证明: by
  rw [← exp_injective.eq_iff]; rw [exp_arcosh hx]; rw [exp_zero]
  grind

Depends on / 依赖: eq_iff, exp_arcosh, exp_injective, exp_injective.eq_iff, exp_zero
-/
theorem arcosh_eq_zero_iff {x : Real} (hx : 1 <= x) : arcosh x = 0 ↔ x = 1 := by
  rw [← exp_injective.eq_iff]; rw [exp_arcosh hx]; rw [exp_zero]
  grind

/--
theorem `sinh_arcosh` / 定理 `sinh_arcosh`

English:
theorem sinh_arcosh
  given: {x : Real} (hx : 1 <= x)
  statement: sinh (arcosh x) = √(x ^ 2 - 1)
  proof: by
  rw [arcosh]; rw [sinh_eq]; rw [exp_neg]; rw [exp_log (by positivity)]; rw [add_sqrt_self_sq_sub_one_inv hx]
  ring

中文:
定理 sinh_arcosh
  条件: {x : 实数} (hx : 1 <= x)
  结论: sinh (arcosh x) = √(x ^ 2 - 1)
  证明: by
  rw [arcosh]; rw [sinh_eq]; rw [exp_neg]; rw [exp_log (by positivity)]; rw [add_sqrt_self_sq_sub_one_inv hx]
  ring

Depends on / 依赖: add_sqrt_self_sq_sub_one_inv, arcosh, exp_log, exp_neg, sinh_eq
-/
theorem sinh_arcosh {x : Real} (hx : 1 <= x) : sinh (arcosh x) = √(x ^ 2 - 1) := by
  rw [arcosh]; rw [sinh_eq]; rw [exp_neg]; rw [exp_log (by positivity)]; rw [add_sqrt_self_sq_sub_one_inv hx]
  ring

/--
theorem `tanh_arcosh` / 定理 `tanh_arcosh`

English:
theorem tanh_arcosh
  given: {x : Real} (hx : 1 <= x)
  statement: tanh (arcosh x) = √(x ^ 2 - 1) / x
  proof: by
  rw [tanh_eq_sinh_div_cosh]; rw [sinh_arcosh hx]; rw [cosh_arcosh hx]

中文:
定理 tanh_arcosh
  条件: {x : 实数} (hx : 1 <= x)
  结论: tanh (arcosh x) = √(x ^ 2 - 1) / x
  证明: by
  rw [tanh_eq_sinh_div_cosh]; rw [sinh_arcosh hx]; rw [cosh_arcosh hx]

Depends on / 依赖: cosh_arcosh, sinh_arcosh, tanh_eq_sinh_div_cosh
-/
theorem tanh_arcosh {x : Real} (hx : 1 <= x) : tanh (arcosh x) = √(x ^ 2 - 1) / x := by
  rw [tanh_eq_sinh_div_cosh]; rw [sinh_arcosh hx]; rw [cosh_arcosh hx]

/--
theorem `arcosh_cosh` / 定理 `arcosh_cosh`

English:
theorem arcosh_cosh
  given: {x : Real} (hx : 0 <= x)
  statement: arcosh (cosh x) = x
  proof: by
  rw [arcosh]; rw [← exp_eq_exp]; rw [exp_log (by positivity)]; rw [← eq_sub_iff_add_eq']; rw [exp_sub_cosh]; rw [← sq_eq_sq₀ (sqrt_nonneg _) (sinh_nonneg_iff.mpr hx)]; rw [← sinh_sq]; rw [sq_sqrt (pow_two_nonneg _)]

中文:
定理 arcosh_cosh
  条件: {x : 实数} (hx : 0 <= x)
  结论: arcosh (cosh x) = x
  证明: by
  rw [arcosh]; rw [← exp_eq_exp]; rw [exp_log (by positivity)]; rw [← eq_sub_iff_add_eq']; rw [exp_sub_cosh]; rw [← sq_eq_sq₀ (sqrt_nonneg _) (sinh_nonneg_iff.mpr hx)]; rw [← sinh_sq]; rw [sq_sqrt (pow_two_nonneg _)]

Depends on / 依赖: arcosh, eq_sub_iff_add_eq, exp_eq_exp, exp_log, exp_sub_cosh, pow_two_nonneg, sinh_nonneg_iff, sinh_nonneg_iff.mpr, sinh_sq, sq_sqrt, sqrt_nonneg
-/
theorem arcosh_cosh {x : Real} (hx : 0 <= x) : arcosh (cosh x) = x := by
  rw [arcosh]; rw [← exp_eq_exp]; rw [exp_log (by positivity)]; rw [← eq_sub_iff_add_eq']; rw [exp_sub_cosh]; rw [← sq_eq_sq₀ (sqrt_nonneg _) (sinh_nonneg_iff.mpr hx)]; rw [← sinh_sq]; rw [sq_sqrt (pow_two_nonneg _)]

/--
theorem `arcosh_nonneg` / 定理 `arcosh_nonneg`

English:
theorem arcosh_nonneg
  given: {x : Real} (hx : 1 <= x)
  statement: 0 <= arcosh x
  proof: by
  apply log_nonneg
  calc
    1 <= x + 0 := by simpa
    _ <= x + √(x ^ 2 - 1) := by gcongr; positivity

中文:
定理 arcosh_nonneg
  条件: {x : 实数} (hx : 1 <= x)
  结论: 0 <= arcosh x
  证明: by
  apply log_nonneg
  calc
    1 <= x + 0 := by simpa
    _ <= x + √(x ^ 2 - 1) := by gcongr; positivity

Depends on / 依赖: log_nonneg
-/
theorem arcosh_nonneg {x : Real} (hx : 1 <= x) : 0 <= arcosh x := by
  apply log_nonneg
  calc
    1 <= x + 0 := by simpa
    _ <= x + √(x ^ 2 - 1) := by gcongr; positivity

/--
theorem `arcosh_pos` / 定理 `arcosh_pos`

English:
theorem arcosh_pos
  given: {x : Real} (hx : 1 < x)
  statement: 0 < arcosh x
  proof: by
  apply log_pos
  calc
    1 < x + 0 := by simpa
    _ <= x + √(x ^ 2 - 1) := by gcongr; positivity

中文:
定理 arcosh_pos
  条件: {x : 实数} (hx : 1 < x)
  结论: 0 < arcosh x
  证明: by
  apply log_pos
  calc
    1 < x + 0 := by simpa
    _ <= x + √(x ^ 2 - 1) := by gcongr; positivity

Depends on / 依赖: log_pos
-/
theorem arcosh_pos {x : Real} (hx : 1 < x) : 0 < arcosh x := by
  apply log_pos
  calc
    1 < x + 0 := by simpa
    _ <= x + √(x ^ 2 - 1) := by gcongr; positivity

/--
theorem `strictMonoOn_arcosh` / 定理 `strictMonoOn_arcosh`

English:
theorem strictMonoOn_arcosh
  statement: StrictMonoOn arcosh (Ioi 0)
  proof: by
  refine strictMonoOn_log.comp ?_ fun x (hx : 0 < x) => show 0 < x + √(x ^ 2 - 1) by positivity
  exact strictMonoOn_id.add_monotone fun x (hx : 0 < x) y (hy : 0 < y) hxy => by gcongr

中文:
定理 strictMonoOn_arcosh
  结论: StrictMonoOn arcosh (Ioi 0)
  证明: by
  refine strictMonoOn_log.comp ?_ fun x (hx : 0 < x) => show 0 < x + √(x ^ 2 - 1) by positivity
  exact strictMonoOn_id.add_monotone fun x (hx : 0 < x) y (hy : 0 < y) hxy => by gcongr

Depends on / 依赖: add_monotone, strictMonoOn_id, strictMonoOn_id.add_monotone, strictMonoOn_log, strictMonoOn_log.comp
-/
theorem strictMonoOn_arcosh : StrictMonoOn arcosh (Ioi 0) := by
  refine strictMonoOn_log.comp ?_ fun x (hx : 0 < x) => show 0 < x + √(x ^ 2 - 1) by positivity
  exact strictMonoOn_id.add_monotone fun x (hx : 0 < x) y (hy : 0 < y) hxy => by gcongr

/--
theorem `arcosh_le_arcosh` / 定理 `arcosh_le_arcosh`

English:
theorem arcosh_le_arcosh
  given: {x y : Real} (hx : 0 < x) (hy : 0 < y)
  statement: arcosh x <= arcosh y ↔ x <= y
  proof: strictMonoOn_arcosh.le_iff_le hx hy

中文:
定理 arcosh_le_arcosh
  条件: {x y : 实数} (hx : 0 < x) (hy : 0 < y)
  结论: arcosh x <= arcosh y ↔ x <= y
  证明: strictMonoOn_arcosh.le_iff_le hx hy

Depends on / 依赖: le_iff_le, strictMonoOn_arcosh, strictMonoOn_arcosh.le_iff_le
-/
theorem arcosh_le_arcosh {x y : Real} (hx : 0 < x) (hy : 0 < y) : arcosh x <= arcosh y ↔ x <= y :=
  strictMonoOn_arcosh.le_iff_le hx hy

/--
theorem `arcosh_lt_arcosh` / 定理 `arcosh_lt_arcosh`

English:
theorem arcosh_lt_arcosh
  given: {x y : Real} (hx : 0 < x) (hy : 0 < y)
  statement: arcosh x < arcosh y ↔ x < y
  proof: strictMonoOn_arcosh.lt_iff_lt hx hy

中文:
定理 arcosh_lt_arcosh
  条件: {x y : 实数} (hx : 0 < x) (hy : 0 < y)
  结论: arcosh x < arcosh y ↔ x < y
  证明: strictMonoOn_arcosh.lt_iff_lt hx hy

Depends on / 依赖: lt_iff_lt, strictMonoOn_arcosh, strictMonoOn_arcosh.lt_iff_lt
-/
theorem arcosh_lt_arcosh {x y : Real} (hx : 0 < x) (hy : 0 < y) : arcosh x < arcosh y ↔ x < y :=
  strictMonoOn_arcosh.lt_iff_lt hx hy

/--
Definition of `coshPartialEquiv` / `coshPartialEquiv` 的定义

English:
definition coshPartialEquiv
  signature: : PartialEquiv Real Real where
  body: cosh
  invFun := arcosh
  source := Ici 0
  target := Ici 1
  map_source' r _ := one_le_cosh r
  map_target' _ hr := arcosh_nonneg hr
  left_inv' _ hr := arcosh_cosh hr
  right_inv' _ hr := cosh_arcosh hr

中文:
定义 coshPartialEquiv
  签名: : PartialEquiv 实数 实数 where
  定义体: cosh
  invFun := arcosh
  source := Ici 0
  target := Ici 1
  map_source' r _ := one_le_cosh r
  map_target' _ hr := arcosh_nonneg hr
  left_inv' _ hr := arcosh_cosh hr
  right_inv' _ hr := cosh_arcosh hr
-/
def coshPartialEquiv : PartialEquiv Real Real where
  toFun := cosh
  invFun := arcosh
  source := Ici 0
  target := Ici 1
  map_source' r _ := one_le_cosh r
  map_target' _ hr := arcosh_nonneg hr
  left_inv' _ hr := arcosh_cosh hr
  right_inv' _ hr := cosh_arcosh hr

/--
theorem `continuousOn_arcosh` / 定理 `continuousOn_arcosh`

English:
theorem continuousOn_arcosh
  statement: ContinuousOn arcosh (Ici 1)
  proof: have {x : Real} (hx : x in Ici 1) : 0 < x + √(x ^ 2 - 1) :=
    add_pos_of_pos_of_nonneg (show 0 < x by grind) (sqrt_nonneg _)
  continuousOn_log.comp (by fun_prop) (by grind [MapsTo])

中文:
定理 continuousOn_arcosh
  结论: ContinuousOn arcosh (Ici 1)
  证明: have {x : Real} (hx : x in Ici 1) : 0 < x + √(x ^ 2 - 1) :=
    add_pos_of_pos_of_nonneg (show 0 < x by grind) (sqrt_nonneg _)
  continuousOn_log.comp (by fun_prop) (by grind [MapsTo])

Depends on / 依赖: MapsTo, add_pos_of_pos_of_nonneg, continuousOn_log, continuousOn_log.comp, fun_prop, sqrt_nonneg
-/
theorem continuousOn_arcosh : ContinuousOn arcosh (Ici 1) :=
  have {x : Real} (hx : x in Ici 1) : 0 < x + √(x ^ 2 - 1) :=
    add_pos_of_pos_of_nonneg (show 0 < x by grind) (sqrt_nonneg _)
  continuousOn_log.comp (by fun_prop) (by grind [MapsTo])

/--
Definition of `coshOpenPartialHomeomorph` / `coshOpenPartialHomeomorph` 的定义

English:
definition coshOpenPartialHomeomorph
  signature: : OpenPartialHomeomorph Real Real where
  body: cosh
  invFun := arcosh
  source := Ioi 0
  target := Ioi 1
  map_source' _ hr := one_lt_cosh.mpr (ne_of_lt hr).symm
  map_target' _ hr := arcosh_pos hr
  left_inv' _ hr := arcosh_cosh (le_of_lt hr)
  right_inv' _ hr := cosh_arcosh (le_of_lt hr)
  open_source := isOpen_Ioi
  open_target := isOpen_Io

中文:
定义 coshOpenPartialHomeomorph
  签名: : OpenPartialHomeomorph 实数 实数 where
  定义体: cosh
  invFun := arcosh
  source := Ioi 0
  target := Ioi 1
  map_source' _ hr := one_lt_cosh.mpr (ne_of_lt hr).symm
  map_target' _ hr := arcosh_pos hr
  left_inv' _ hr := arcosh_cosh (le_of_lt hr)
  right_inv' _ hr := cosh_arcosh (le_of_lt hr)
  open_source := isOpen_Ioi
  open_target := isOpen_Io
-/
def coshOpenPartialHomeomorph : OpenPartialHomeomorph Real Real where
  toFun := cosh
  invFun := arcosh
  source := Ioi 0
  target := Ioi 1
  map_source' _ hr := one_lt_cosh.mpr (ne_of_lt hr).symm
  map_target' _ hr := arcosh_pos hr
  left_inv' _ hr := arcosh_cosh (le_of_lt hr)
  right_inv' _ hr := cosh_arcosh (le_of_lt hr)
  open_source := isOpen_Ioi
  open_target := isOpen_Ioi
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := continuousOn_arcosh.mono Ioi_subset_Ici_self

/--
theorem `hasStrictDerivAt_arcosh` / 定理 `hasStrictDerivAt_arcosh`

English:
theorem hasStrictDerivAt_arcosh
  given: {x : Real} (hx : x in Ioi 1)
  proof: by
  rw [← sinh_arcosh (le_of_lt hx)]
  refine coshOpenPartialHomeomorph.hasStrictDerivAt_symm hx ?_ (hasStrictDerivAt_cosh _)
  rw [ne_eq]; rw [sinh_eq_zero]
  exact ne_of_gt (arcosh_pos hx)

中文:
定理 hasStrictDerivAt_arcosh
  条件: {x : 实数} (hx : x in Ioi 1)
  证明: by
  rw [← sinh_arcosh (le_of_lt hx)]
  refine coshOpenPartialHomeomorph.hasStrictDerivAt_symm hx ?_ (hasStrictDerivAt_cosh _)
  rw [ne_eq]; rw [sinh_eq_zero]
  exact ne_of_gt (arcosh_pos hx)

Depends on / 依赖: arcosh_pos, coshOpenPartialHomeomorph, coshOpenPartialHomeomorph.hasStrictDerivAt_symm, hasStrictDerivAt_cosh, hasStrictDerivAt_symm, le_of_lt, ne_eq, ne_of_gt, sinh_arcosh, sinh_eq_zero
-/
theorem hasStrictDerivAt_arcosh {x : Real} (hx : x in Ioi 1) :
    HasStrictDerivAt arcosh (√(x ^ 2 - 1))⁻¹ x := by
  rw [← sinh_arcosh (le_of_lt hx)]
  refine coshOpenPartialHomeomorph.hasStrictDerivAt_symm hx ?_ (hasStrictDerivAt_cosh _)
  rw [ne_eq]; rw [sinh_eq_zero]
  exact ne_of_gt (arcosh_pos hx)

/--
theorem `hasDerivAt_arcosh` / 定理 `hasDerivAt_arcosh`

English:
theorem hasDerivAt_arcosh
  given: {x : Real} (hx : x in Ioi 1)
  statement: HasDerivAt arcosh (√(x ^ 2 - 1))⁻¹ x
  proof: (hasStrictDerivAt_arcosh hx).hasDerivAt

中文:
定理 hasDerivAt_arcosh
  条件: {x : 实数} (hx : x in Ioi 1)
  结论: HasDerivAt arcosh (√(x ^ 2 - 1))⁻¹ x
  证明: (hasStrictDerivAt_arcosh hx).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_arcosh
-/
theorem hasDerivAt_arcosh {x : Real} (hx : x in Ioi 1) : HasDerivAt arcosh (√(x ^ 2 - 1))⁻¹ x :=
  (hasStrictDerivAt_arcosh hx).hasDerivAt

/--
theorem `differentiableAt_arcosh` / 定理 `differentiableAt_arcosh`

English:
theorem differentiableAt_arcosh
  given: {x : Real} (hx : x in Ioi 1)
  statement: DifferentiableAt Real arcosh x
  proof: (hasDerivAt_arcosh hx).differentiableAt

中文:
定理 differentiableAt_arcosh
  条件: {x : 实数} (hx : x in Ioi 1)
  结论: DifferentiableAt 实数 arcosh x
  证明: (hasDerivAt_arcosh hx).differentiableAt

Depends on / 依赖: differentiableAt, hasDerivAt_arcosh
-/
theorem differentiableAt_arcosh {x : Real} (hx : x in Ioi 1) : DifferentiableAt Real arcosh x :=
  (hasDerivAt_arcosh hx).differentiableAt

/--
theorem `differentiableOn_arcosh` / 定理 `differentiableOn_arcosh`

English:
theorem differentiableOn_arcosh
  statement: DifferentiableOn Real arcosh (Ioi 1)
  proof: fun _ hx =>
  (differentiableAt_arcosh hx).differentiableWithinAt

中文:
定理 differentiableOn_arcosh
  结论: DifferentiableOn 实数 arcosh (Ioi 1)
  证明: fun _ hx =>
  (differentiableAt_arcosh hx).differentiableWithinAt
-/
theorem differentiableOn_arcosh : DifferentiableOn Real arcosh (Ioi 1) := fun _ hx =>
  (differentiableAt_arcosh hx).differentiableWithinAt

/--
theorem `contDiffAt_arcosh` / 定理 `contDiffAt_arcosh`

English:
theorem contDiffAt_arcosh
  given: {n : WithTop Nat∞} {x : Real} (hx : x in Ioi 1)
  statement: ContDiffAt Real n arcosh x
  proof: by
  refine coshOpenPartialHomeomorph.contDiffAt_symm_deriv ?_ hx (hasDerivAt_cosh _)
    contDiff_cosh.contDiffAt
  rw [ne_eq]; rw [sinh_eq_zero]
  exact (arcosh_pos hx).ne'

中文:
定理 contDiffAt_arcosh
  条件: {n : WithTop 自然数∞} {x : 实数} (hx : x in Ioi 1)
  结论: ContDiffAt 实数 n arcosh x
  证明: by
  refine coshOpenPartialHomeomorph.contDiffAt_symm_deriv ?_ hx (hasDerivAt_cosh _)
    contDiff_cosh.contDiffAt
  rw [ne_eq]; rw [sinh_eq_zero]
  exact (arcosh_pos hx).ne'

Depends on / 依赖: arcosh_pos, contDiffAt, contDiffAt_symm_deriv, contDiff_cosh, contDiff_cosh.contDiffAt, coshOpenPartialHomeomorph, coshOpenPartialHomeomorph.contDiffAt_symm_deriv, hasDerivAt_cosh, ne_eq, sinh_eq_zero
-/
theorem contDiffAt_arcosh {n : WithTop Nat∞} {x : Real} (hx : x in Ioi 1) : ContDiffAt Real n arcosh x := by
  refine coshOpenPartialHomeomorph.contDiffAt_symm_deriv ?_ hx (hasDerivAt_cosh _)
    contDiff_cosh.contDiffAt
  rw [ne_eq]; rw [sinh_eq_zero]
  exact (arcosh_pos hx).ne'

/--
theorem `contDiffOn_arcosh` / 定理 `contDiffOn_arcosh`

English:
theorem contDiffOn_arcosh
  given: {n : WithTop Nat∞}
  statement: ContDiffOn Real n arcosh (Ioi 1)
  proof: fun _ hx =>
  (contDiffAt_arcosh hx).contDiffWithinAt

中文:
定理 contDiffOn_arcosh
  条件: {n : WithTop 自然数∞}
  结论: ContDiffOn 实数 n arcosh (Ioi 1)
  证明: fun _ hx =>
  (contDiffAt_arcosh hx).contDiffWithinAt
-/
theorem contDiffOn_arcosh {n : WithTop Nat∞} : ContDiffOn Real n arcosh (Ioi 1) := fun _ hx =>
  (contDiffAt_arcosh hx).contDiffWithinAt

/-- The function `Real.arcosh` is real analytic. -/
@[fun_prop]
/--
lemma `analyticAt_arcosh` / 引理 `analyticAt_arcosh`

English:
lemma analyticAt_arcosh
  given: {x : Real} (hx : x in Ioi 1)
  statement: AnalyticAt Real arcosh x
  proof: (contDiffAt_arcosh hx).analyticAt

中文:
引理 analyticAt_arcosh
  条件: {x : 实数} (hx : x in Ioi 1)
  结论: AnalyticAt 实数 arcosh x
  证明: (contDiffAt_arcosh hx).analyticAt

Depends on / 依赖: analyticAt, contDiffAt_arcosh
-/
lemma analyticAt_arcosh {x : Real} (hx : x in Ioi 1) : AnalyticAt Real arcosh x :=
  (contDiffAt_arcosh hx).analyticAt

/--
lemma `analyticWithinAt_arcosh` / 引理 `analyticWithinAt_arcosh`

English:
lemma analyticWithinAt_arcosh
  given: {s : Set Real} {x : Real} (hx : x in Ioi 1)
  proof: (contDiffAt_arcosh hx).contDiffWithinAt.analyticWithinAt

中文:
引理 analyticWithinAt_arcosh
  条件: {s : Set 实数} {x : 实数} (hx : x in Ioi 1)
  证明: (contDiffAt_arcosh hx).contDiffWithinAt.analyticWithinAt

Depends on / 依赖: analyticWithinAt, contDiffAt_arcosh, contDiffWithinAt, contDiffWithinAt.analyticWithinAt
-/
lemma analyticWithinAt_arcosh {s : Set Real} {x : Real} (hx : x in Ioi 1) :
    AnalyticWithinAt Real arcosh s x :=
  (contDiffAt_arcosh hx).contDiffWithinAt.analyticWithinAt

/--
theorem `analyticOnNhd_arcosh` / 定理 `analyticOnNhd_arcosh`

English:
theorem analyticOnNhd_arcosh
  given: {s : Set Real} (hs : s subseteq Ioi 1)
  statement: AnalyticOnNhd Real arcosh s
  proof: fun _ hx => analyticAt_arcosh (hs hx)

中文:
定理 analyticOnNhd_arcosh
  条件: {s : Set 实数} (hs : s subseteq Ioi 1)
  结论: AnalyticOnNhd 实数 arcosh s
  证明: fun _ hx => analyticAt_arcosh (hs hx)

Depends on / 依赖: analyticAt_arcosh
-/
theorem analyticOnNhd_arcosh {s : Set Real} (hs : s subseteq Ioi 1) : AnalyticOnNhd Real arcosh s :=
  fun _ hx => analyticAt_arcosh (hs hx)

/--
lemma `analyticOn_arcosh` / 引理 `analyticOn_arcosh`

English:
lemma analyticOn_arcosh
  given: {s : Set Real} (hs : s subseteq Ioi 1)
  statement: AnalyticOn Real arcosh s
  proof: contDiffOn_arcosh.analyticOn.mono hs

中文:
引理 analyticOn_arcosh
  条件: {s : Set 实数} (hs : s subseteq Ioi 1)
  结论: AnalyticOn 实数 arcosh s
  证明: contDiffOn_arcosh.analyticOn.mono hs

Depends on / 依赖: analyticOn, contDiffOn_arcosh, contDiffOn_arcosh.analyticOn.mono
-/
lemma analyticOn_arcosh {s : Set Real} (hs : s subseteq Ioi 1) : AnalyticOn Real arcosh s :=
  contDiffOn_arcosh.analyticOn.mono hs

/--
theorem `cosh_bijOn` / 定理 `cosh_bijOn`

English:
theorem cosh_bijOn
  statement: BijOn cosh (Ici 0) (Ici 1)
  proof: coshPartialEquiv.bijOn

中文:
定理 cosh_bijOn
  结论: BijOn cosh (Ici 0) (Ici 1)
  证明: coshPartialEquiv.bijOn

Depends on / 依赖: coshPartialEquiv, coshPartialEquiv.bijOn
-/
theorem cosh_bijOn : BijOn cosh (Ici 0) (Ici 1) := coshPartialEquiv.bijOn

/--
theorem `cosh_injOn` / 定理 `cosh_injOn`

English:
theorem cosh_injOn
  statement: InjOn cosh (Ici 0)
  proof: coshPartialEquiv.injOn

中文:
定理 cosh_injOn
  结论: InjOn cosh (Ici 0)
  证明: coshPartialEquiv.injOn

Depends on / 依赖: coshPartialEquiv, coshPartialEquiv.injOn
-/
theorem cosh_injOn : InjOn cosh (Ici 0) := coshPartialEquiv.injOn

/--
theorem `cosh_surjOn` / 定理 `cosh_surjOn`

English:
theorem cosh_surjOn
  statement: SurjOn cosh (Ici 0) (Ici 1)
  proof: coshPartialEquiv.surjOn

中文:
定理 cosh_surjOn
  结论: SurjOn cosh (Ici 0) (Ici 1)
  证明: coshPartialEquiv.surjOn

Depends on / 依赖: coshPartialEquiv, coshPartialEquiv.surjOn, surjOn
-/
theorem cosh_surjOn : SurjOn cosh (Ici 0) (Ici 1) := coshPartialEquiv.surjOn

/--
theorem `arcosh_bijOn` / 定理 `arcosh_bijOn`

English:
theorem arcosh_bijOn
  statement: BijOn arcosh (Ici 1) (Ici 0)
  proof: coshPartialEquiv.symm.bijOn

中文:
定理 arcosh_bijOn
  结论: BijOn arcosh (Ici 1) (Ici 0)
  证明: coshPartialEquiv.symm.bijOn

Depends on / 依赖: coshPartialEquiv, coshPartialEquiv.symm.bijOn
-/
theorem arcosh_bijOn : BijOn arcosh (Ici 1) (Ici 0) := coshPartialEquiv.symm.bijOn

/--
theorem `arcosh_injOn` / 定理 `arcosh_injOn`

English:
theorem arcosh_injOn
  statement: InjOn arcosh (Ici 1)
  proof: coshPartialEquiv.symm.injOn

中文:
定理 arcosh_injOn
  结论: InjOn arcosh (Ici 1)
  证明: coshPartialEquiv.symm.injOn

Depends on / 依赖: coshPartialEquiv, coshPartialEquiv.symm.injOn
-/
theorem arcosh_injOn : InjOn arcosh (Ici 1) := coshPartialEquiv.symm.injOn

/--
theorem `arcosh_surjOn` / 定理 `arcosh_surjOn`

English:
theorem arcosh_surjOn
  statement: SurjOn arcosh (Ici 1) (Ici 0)
  proof: coshPartialEquiv.symm.surjOn

中文:
定理 arcosh_surjOn
  结论: SurjOn arcosh (Ici 1) (Ici 0)
  证明: coshPartialEquiv.symm.surjOn

Depends on / 依赖: coshPartialEquiv, coshPartialEquiv.symm.surjOn, surjOn
-/
theorem arcosh_surjOn : SurjOn arcosh (Ici 1) (Ici 0) := coshPartialEquiv.symm.surjOn

end Real
