/-
Copyright (c) 2020 James Arthur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Chris Hughes, Shing Tak Lam
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Inverse of the sinh function

In this file we prove that sinh is bijective and hence has an
inverse, arsinh.

## Main definitions

- `Real.arsinh`: The inverse function of `Real.sinh`.

- `Real.sinhEquiv`, `Real.sinhOrderIso`, `Real.sinhHomeomorph`: `Real.sinh` as an `Equiv`,
  `OrderIso`, and `Homeomorph`, respectively.

## Main Results

- `Real.sinh_surjective`, `Real.sinh_bijective`: `Real.sinh` is surjective and bijective;

- `Real.arsinh_injective`, `Real.arsinh_surjective`, `Real.arsinh_bijective`: `Real.arsinh` is
  injective, surjective, and bijective;

- `Real.continuous_arsinh`, `Real.differentiable_arsinh`, `Real.contDiff_arsinh`: `Real.arsinh` is
  continuous, differentiable, and continuously differentiable; we also provide dot notation
  convenience lemmas like `Filter.Tendsto.arsinh` and `ContDiffAt.arsinh`.

## Tags

arsinh, arcsinh, argsinh, asinh, sinh injective, sinh bijective, sinh surjective
-/

@[expose] public section

noncomputable section

open Function Filter Set

open scoped Topology

namespace Real

variable {x y : Real}

/-- `arsinh` is defined using a logarithm, `arsinh x = log (x + √(1 + x^2))`. -/
@[pp_nodot]
/--
Definition of `arsinh` / `arsinh` 的定义

English:
definition arsinh
  signature: (x : Real)
  body: log (x + √(1 + x ^ 2))

中文:
定义 arsinh
  签名: (x : 实数)
  定义体: log (x + √(1 + x ^ 2))
-/
def arsinh (x : Real) :=
  log (x + √(1 + x ^ 2))

/--
theorem `exp_arsinh` / 定理 `exp_arsinh`

English:
theorem exp_arsinh
  given: (x : Real)
  statement: exp (arsinh x) = x + √(1 + x ^ 2)
  proof: by
  apply exp_log
  rw [← neg_lt_iff_pos_add']
  apply lt_sqrt_of_sq_lt
  simp

@[simp]

中文:
定理 exp_arsinh
  条件: (x : 实数)
  结论: exp (arsinh x) = x + √(1 + x ^ 2)
  证明: by
  apply exp_log
  rw [← neg_lt_iff_pos_add']
  apply lt_sqrt_of_sq_lt
  simp

@[simp]

Depends on / 依赖: exp_log, lt_sqrt_of_sq_lt, neg_lt_iff_pos_add
-/
theorem exp_arsinh (x : Real) : exp (arsinh x) = x + √(1 + x ^ 2) := by
  apply exp_log
  rw [← neg_lt_iff_pos_add']
  apply lt_sqrt_of_sq_lt
  simp

@[simp]
/--
theorem `arsinh_zero` / 定理 `arsinh_zero`

English:
theorem arsinh_zero
  statement: arsinh 0 = 0
  proof: by simp [arsinh]

@[simp]

中文:
定理 arsinh_zero
  结论: arsinh 0 = 0
  证明: by simp [arsinh]

@[simp]

Depends on / 依赖: arsinh
-/
theorem arsinh_zero : arsinh 0 = 0 := by simp [arsinh]

@[simp]
/--
theorem `arsinh_neg` / 定理 `arsinh_neg`

English:
theorem arsinh_neg
  given: (x : Real)
  statement: arsinh (-x) = -arsinh x
  proof: by
  rw [← exp_eq_exp]; rw [exp_arsinh]; rw [exp_neg]; rw [exp_arsinh]
  apply eq_inv_of_mul_eq_one_left
  rw [neg_sq]; rw [neg_add_eq_sub]; rw [add_comm x]; rw [mul_comm]; rw [← sq_sub_sq]; rw [sq_sqrt]; rw [add_sub_cancel_right]
  exact add_nonneg zero_le_one (sq_nonneg _)

中文:
定理 arsinh_neg
  条件: (x : 实数)
  结论: arsinh (-x) = -arsinh x
  证明: by
  rw [← exp_eq_exp]; rw [exp_arsinh]; rw [exp_neg]; rw [exp_arsinh]
  apply eq_inv_of_mul_eq_one_left
  rw [neg_sq]; rw [neg_add_eq_sub]; rw [add_comm x]; rw [mul_comm]; rw [← sq_sub_sq]; rw [sq_sqrt]; rw [add_sub_cancel_right]
  exact add_nonneg zero_le_one (sq_nonneg _)

Depends on / 依赖: add_comm, add_nonneg, add_sub_cancel_right, eq_inv_of_mul_eq_one_left, exp_arsinh, exp_eq_exp, exp_neg, mul_comm, neg_add_eq_sub, neg_sq, sq_nonneg, sq_sqrt, sq_sub_sq, zero_le_one
-/
theorem arsinh_neg (x : Real) : arsinh (-x) = -arsinh x := by
  rw [← exp_eq_exp]; rw [exp_arsinh]; rw [exp_neg]; rw [exp_arsinh]
  apply eq_inv_of_mul_eq_one_left
  rw [neg_sq]; rw [neg_add_eq_sub]; rw [add_comm x]; rw [mul_comm]; rw [← sq_sub_sq]; rw [sq_sqrt]; rw [add_sub_cancel_right]
  exact add_nonneg zero_le_one (sq_nonneg _)

/-- `arsinh` is the right inverse of `sinh`. -/
@[simp]
/--
theorem `sinh_arsinh` / 定理 `sinh_arsinh`

English:
theorem sinh_arsinh
  given: (x : Real)
  statement: sinh (arsinh x) = x
  proof: by
  rw [sinh_eq]; rw [← arsinh_neg]; rw [exp_arsinh]; rw [exp_arsinh]; rw [neg_sq]; simp

@[simp]

中文:
定理 sinh_arsinh
  条件: (x : 实数)
  结论: sinh (arsinh x) = x
  证明: by
  rw [sinh_eq]; rw [← arsinh_neg]; rw [exp_arsinh]; rw [exp_arsinh]; rw [neg_sq]; simp

@[simp]

Depends on / 依赖: arsinh_neg, exp_arsinh, neg_sq, sinh_eq
-/
theorem sinh_arsinh (x : Real) : sinh (arsinh x) = x := by
  rw [sinh_eq]; rw [← arsinh_neg]; rw [exp_arsinh]; rw [exp_arsinh]; rw [neg_sq]; simp

@[simp]
/--
theorem `cosh_arsinh` / 定理 `cosh_arsinh`

English:
theorem cosh_arsinh
  given: (x : Real)
  statement: cosh (arsinh x) = √(1 + x ^ 2)
  proof: by
  rw [← sqrt_sq (cosh_pos _).le]; rw [cosh_sq']; rw [sinh_arsinh]

@[simp]

中文:
定理 cosh_arsinh
  条件: (x : 实数)
  结论: cosh (arsinh x) = √(1 + x ^ 2)
  证明: by
  rw [← sqrt_sq (cosh_pos _).le]; rw [cosh_sq']; rw [sinh_arsinh]

@[simp]

Depends on / 依赖: cosh_pos, cosh_sq, sinh_arsinh, sqrt_sq
-/
theorem cosh_arsinh (x : Real) : cosh (arsinh x) = √(1 + x ^ 2) := by
  rw [← sqrt_sq (cosh_pos _).le]; rw [cosh_sq']; rw [sinh_arsinh]

@[simp]
/--
theorem `tanh_arsinh` / 定理 `tanh_arsinh`

English:
theorem tanh_arsinh
  given: (x : Real)
  statement: tanh (arsinh x) = x / √(1 + x ^ 2)
  proof: by
  rw [tanh_eq_sinh_div_cosh]; rw [sinh_arsinh]; rw [cosh_arsinh]

中文:
定理 tanh_arsinh
  条件: (x : 实数)
  结论: tanh (arsinh x) = x / √(1 + x ^ 2)
  证明: by
  rw [tanh_eq_sinh_div_cosh]; rw [sinh_arsinh]; rw [cosh_arsinh]

Depends on / 依赖: cosh_arsinh, sinh_arsinh, tanh_eq_sinh_div_cosh
-/
theorem tanh_arsinh (x : Real) : tanh (arsinh x) = x / √(1 + x ^ 2) := by
  rw [tanh_eq_sinh_div_cosh]; rw [sinh_arsinh]; rw [cosh_arsinh]

/--
theorem `sinh_surjective` / 定理 `sinh_surjective`

English:
theorem sinh_surjective
  statement: Surjective sinh
  proof: LeftInverse.surjective sinh_arsinh

中文:
定理 sinh_surjective
  结论: 满射 sinh
  证明: LeftInverse.surjective sinh_arsinh

Depends on / 依赖: LeftInverse, LeftInverse.surjective, sinh_arsinh, surjective
-/
theorem sinh_surjective : Surjective sinh :=
  LeftInverse.surjective sinh_arsinh

/--
theorem `sinh_bijective` / 定理 `sinh_bijective`

English:
theorem sinh_bijective
  statement: Bijective sinh
  proof: ⟨sinh_injective, sinh_surjective⟩

中文:
定理 sinh_bijective
  结论: 双射 sinh
  证明: ⟨sinh_injective, sinh_surjective⟩

Depends on / 依赖: sinh_injective, sinh_surjective
-/
theorem sinh_bijective : Bijective sinh :=
  ⟨sinh_injective, sinh_surjective⟩

/-- `arsinh` is the left inverse of `sinh`. -/
@[simp]
/--
theorem `arsinh_sinh` / 定理 `arsinh_sinh`

English:
theorem arsinh_sinh
  given: (x : Real)
  statement: arsinh (sinh x) = x
  proof: rightInverse_of_injective_of_leftInverse sinh_injective sinh_arsinh x

中文:
定理 arsinh_sinh
  条件: (x : 实数)
  结论: arsinh (sinh x) = x
  证明: rightInverse_of_injective_of_leftInverse sinh_injective sinh_arsinh x

Depends on / 依赖: rightInverse_of_injective_of_leftInverse, sinh_arsinh, sinh_injective
-/
theorem arsinh_sinh (x : Real) : arsinh (sinh x) = x :=
  rightInverse_of_injective_of_leftInverse sinh_injective sinh_arsinh x

/-- `Real.sinh` as an `Equiv`. -/
@[simps]
/--
Definition of `sinhEquiv` / `sinhEquiv` 的定义

English:
definition sinhEquiv
  signature: : Real ≃ Real where
  body: sinh
  invFun := arsinh
  left_inv := arsinh_sinh
  right_inv := sinh_arsinh

中文:
定义 sinhEquiv
  签名: : 实数 ≃ 实数 where
  定义体: sinh
  invFun := arsinh
  left_inv := arsinh_sinh
  right_inv := sinh_arsinh
-/
def sinhEquiv : Real ≃ Real where
  toFun := sinh
  invFun := arsinh
  left_inv := arsinh_sinh
  right_inv := sinh_arsinh

/-- `Real.sinh` as an `OrderIso`. -/
@[simps! -fullyApplied]
/--
Definition of `sinhOrderIso` / `sinhOrderIso` 的定义

English:
definition sinhOrderIso
  signature: : Real ≃o Real where
  body: sinhEquiv
  map_rel_iff' := @sinh_le_sinh

中文:
定义 sinhOrderIso
  签名: : 实数 ≃o 实数 where
  定义体: sinhEquiv
  map_rel_iff' := @sinh_le_sinh

Depends on / 依赖: sinhEquiv
-/
def sinhOrderIso : Real ≃o Real where
  toEquiv := sinhEquiv
  map_rel_iff' := @sinh_le_sinh

/-- `Real.sinh` as a `Homeomorph`. -/
@[simps! -fullyApplied]
/--
Definition of `sinhHomeomorph` / `sinhHomeomorph` 的定义

English:
definition sinhHomeomorph
  signature: : Real ≃ₜ Real
  body: sinhOrderIso.toHomeomorph

中文:
定义 sinhHomeomorph
  签名: : 实数 ≃ₜ 实数
  定义体: sinhOrderIso.toHomeomorph

Depends on / 依赖: sinhOrderIso, sinhOrderIso.toHomeomorph, toHomeomorph
-/
def sinhHomeomorph : Real ≃ₜ Real :=
  sinhOrderIso.toHomeomorph

/--
theorem `arsinh_bijective` / 定理 `arsinh_bijective`

English:
theorem arsinh_bijective
  statement: Bijective arsinh
  proof: sinhEquiv.symm.bijective

中文:
定理 arsinh_bijective
  结论: 双射 arsinh
  证明: sinhEquiv.symm.bijective

Depends on / 依赖: bijective, sinhEquiv, sinhEquiv.symm.bijective
-/
theorem arsinh_bijective : Bijective arsinh :=
  sinhEquiv.symm.bijective

/--
theorem `arsinh_injective` / 定理 `arsinh_injective`

English:
theorem arsinh_injective
  statement: Injective arsinh
  proof: sinhEquiv.symm.injective

中文:
定理 arsinh_injective
  结论: 单射 arsinh
  证明: sinhEquiv.symm.injective

Depends on / 依赖: injective, sinhEquiv, sinhEquiv.symm.injective
-/
theorem arsinh_injective : Injective arsinh :=
  sinhEquiv.symm.injective

/--
theorem `arsinh_surjective` / 定理 `arsinh_surjective`

English:
theorem arsinh_surjective
  statement: Surjective arsinh
  proof: sinhEquiv.symm.surjective

中文:
定理 arsinh_surjective
  结论: 满射 arsinh
  证明: sinhEquiv.symm.surjective

Depends on / 依赖: sinhEquiv, sinhEquiv.symm.surjective, surjective
-/
theorem arsinh_surjective : Surjective arsinh :=
  sinhEquiv.symm.surjective

/--
theorem `arsinh_strictMono` / 定理 `arsinh_strictMono`

English:
theorem arsinh_strictMono
  statement: StrictMono arsinh
  proof: sinhOrderIso.symm.strictMono

@[simp]

中文:
定理 arsinh_strictMono
  结论: 严格递增 arsinh
  证明: sinhOrderIso.symm.strictMono

@[simp]

Depends on / 依赖: sinhOrderIso, sinhOrderIso.symm.strictMono, strictMono
-/
theorem arsinh_strictMono : StrictMono arsinh :=
  sinhOrderIso.symm.strictMono

@[simp]
/--
theorem `arsinh_inj` / 定理 `arsinh_inj`

English:
theorem arsinh_inj
  statement: arsinh x = arsinh y ↔ x = y
  proof: arsinh_injective.eq_iff

@[simp, gcongr]

中文:
定理 arsinh_inj
  结论: arsinh x = arsinh y ↔ x = y
  证明: arsinh_injective.eq_iff

@[simp, gcongr]

Depends on / 依赖: arsinh_injective, arsinh_injective.eq_iff, eq_iff
-/
theorem arsinh_inj : arsinh x = arsinh y ↔ x = y :=
  arsinh_injective.eq_iff

@[simp, gcongr]
/--
theorem `arsinh_le_arsinh` / 定理 `arsinh_le_arsinh`

English:
theorem arsinh_le_arsinh
  statement: arsinh x <= arsinh y ↔ x <= y
  proof: sinhOrderIso.symm.le_iff_le

@[simp]

中文:
定理 arsinh_le_arsinh
  结论: arsinh x <= arsinh y ↔ x <= y
  证明: sinhOrderIso.symm.le_iff_le

@[simp]

Depends on / 依赖: le_iff_le, sinhOrderIso, sinhOrderIso.symm.le_iff_le
-/
theorem arsinh_le_arsinh : arsinh x <= arsinh y ↔ x <= y :=
  sinhOrderIso.symm.le_iff_le

@[simp]
/--
theorem `arsinh_lt_arsinh` / 定理 `arsinh_lt_arsinh`

English:
theorem arsinh_lt_arsinh
  statement: arsinh x < arsinh y ↔ x < y
  proof: sinhOrderIso.symm.lt_iff_lt

@[simp]

中文:
定理 arsinh_lt_arsinh
  结论: arsinh x < arsinh y ↔ x < y
  证明: sinhOrderIso.symm.lt_iff_lt

@[simp]

Depends on / 依赖: lt_iff_lt, sinhOrderIso, sinhOrderIso.symm.lt_iff_lt
-/
theorem arsinh_lt_arsinh : arsinh x < arsinh y ↔ x < y :=
  sinhOrderIso.symm.lt_iff_lt

@[simp]
/--
theorem `arsinh_eq_zero_iff` / 定理 `arsinh_eq_zero_iff`

English:
theorem arsinh_eq_zero_iff
  statement: arsinh x = 0 ↔ x = 0
  proof: arsinh_injective.eq_iff' arsinh_zero

@[simp]

中文:
定理 arsinh_eq_zero_iff
  结论: arsinh x = 0 ↔ x = 0
  证明: arsinh_injective.eq_iff' arsinh_zero

@[simp]

Depends on / 依赖: arsinh_injective, arsinh_injective.eq_iff, arsinh_zero, eq_iff
-/
theorem arsinh_eq_zero_iff : arsinh x = 0 ↔ x = 0 :=
  arsinh_injective.eq_iff' arsinh_zero

@[simp]
/--
theorem `arsinh_nonneg_iff` / 定理 `arsinh_nonneg_iff`

English:
theorem arsinh_nonneg_iff
  statement: 0 <= arsinh x ↔ 0 <= x
  proof: by rw [← sinh_le_sinh, sinh_zero, sinh_arsinh]

@[simp]

中文:
定理 arsinh_nonneg_iff
  结论: 0 <= arsinh x ↔ 0 <= x
  证明: by rw [← sinh_le_sinh, sinh_zero, sinh_arsinh]

@[simp]

Depends on / 依赖: sinh_arsinh, sinh_le_sinh, sinh_zero
-/
theorem arsinh_nonneg_iff : 0 <= arsinh x ↔ 0 <= x := by rw [← sinh_le_sinh, sinh_zero, sinh_arsinh]

@[simp]
/--
theorem `arsinh_nonpos_iff` / 定理 `arsinh_nonpos_iff`

English:
theorem arsinh_nonpos_iff
  statement: arsinh x <= 0 ↔ x <= 0
  proof: by rw [← sinh_le_sinh, sinh_zero, sinh_arsinh]

@[simp]

中文:
定理 arsinh_nonpos_iff
  结论: arsinh x <= 0 ↔ x <= 0
  证明: by rw [← sinh_le_sinh, sinh_zero, sinh_arsinh]

@[simp]

Depends on / 依赖: sinh_arsinh, sinh_le_sinh, sinh_zero
-/
theorem arsinh_nonpos_iff : arsinh x <= 0 ↔ x <= 0 := by rw [← sinh_le_sinh, sinh_zero, sinh_arsinh]

@[simp]
/--
theorem `arsinh_pos_iff` / 定理 `arsinh_pos_iff`

English:
theorem arsinh_pos_iff
  statement: 0 < arsinh x ↔ 0 < x
  proof: lt_iff_lt_of_le_iff_le arsinh_nonpos_iff

@[simp]

中文:
定理 arsinh_pos_iff
  结论: 0 < arsinh x ↔ 0 < x
  证明: lt_iff_lt_of_le_iff_le arsinh_nonpos_iff

@[simp]

Depends on / 依赖: arsinh_nonpos_iff, lt_iff_lt_of_le_iff_le
-/
theorem arsinh_pos_iff : 0 < arsinh x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le arsinh_nonpos_iff

@[simp]
/--
theorem `arsinh_neg_iff` / 定理 `arsinh_neg_iff`

English:
theorem arsinh_neg_iff
  statement: arsinh x < 0 ↔ x < 0
  proof: lt_iff_lt_of_le_iff_le arsinh_nonneg_iff

中文:
定理 arsinh_neg_iff
  结论: arsinh x < 0 ↔ x < 0
  证明: lt_iff_lt_of_le_iff_le arsinh_nonneg_iff

Depends on / 依赖: arsinh_nonneg_iff, lt_iff_lt_of_le_iff_le
-/
theorem arsinh_neg_iff : arsinh x < 0 ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le arsinh_nonneg_iff

/--
theorem `hasStrictDerivAt_arsinh` / 定理 `hasStrictDerivAt_arsinh`

English:
theorem hasStrictDerivAt_arsinh
  given: (x : Real)
  statement: HasStrictDerivAt arsinh (√(1 + x ^ 2))⁻¹ x
  proof: by
  convert!
    sinhHomeomorph.toOpenPartialHomeomorph.hasStrictDerivAt_symm (mem_univ x) (cosh_pos _).ne'
      (hasStrictDerivAt_sinh _) using 2
  exact (cosh_arsinh _).symm

中文:
定理 hasStrictDerivAt_arsinh
  条件: (x : 实数)
  结论: HasStrictDerivAt arsinh (√(1 + x ^ 2))⁻¹ x
  证明: by
  convert!
    sinhHomeomorph.toOpenPartialHomeomorph.hasStrictDerivAt_symm (mem_univ x) (cosh_pos _).ne'
      (hasStrictDerivAt_sinh _) using 2
  exact (cosh_arsinh _).symm

Depends on / 依赖: convert, cosh_arsinh, cosh_pos, hasStrictDerivAt_sinh, hasStrictDerivAt_symm, mem_univ, sinhHomeomorph, sinhHomeomorph.toOpenPartialHomeomorph.hasStrictDerivAt_symm, toOpenPartialHomeomorph
-/
theorem hasStrictDerivAt_arsinh (x : Real) : HasStrictDerivAt arsinh (√(1 + x ^ 2))⁻¹ x := by
  convert!
    sinhHomeomorph.toOpenPartialHomeomorph.hasStrictDerivAt_symm (mem_univ x) (cosh_pos _).ne'
      (hasStrictDerivAt_sinh _) using 2
  exact (cosh_arsinh _).symm

/--
theorem `hasDerivAt_arsinh` / 定理 `hasDerivAt_arsinh`

English:
theorem hasDerivAt_arsinh
  given: (x : Real)
  statement: HasDerivAt arsinh (√(1 + x ^ 2))⁻¹ x
  proof: (hasStrictDerivAt_arsinh x).hasDerivAt

@[fun_prop]

中文:
定理 hasDerivAt_arsinh
  条件: (x : 实数)
  结论: 在点处可导 arsinh (√(1 + x ^ 2))⁻¹ x
  证明: (hasStrictDerivAt_arsinh x).hasDerivAt

@[fun_prop]

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_arsinh
-/
theorem hasDerivAt_arsinh (x : Real) : HasDerivAt arsinh (√(1 + x ^ 2))⁻¹ x :=
  (hasStrictDerivAt_arsinh x).hasDerivAt

@[fun_prop]
/--
theorem `differentiable_arsinh` / 定理 `differentiable_arsinh`

English:
theorem differentiable_arsinh
  statement: Differentiable Real arsinh
  proof: fun x =>
  (hasDerivAt_arsinh x).differentiableAt

@[fun_prop]

中文:
定理 differentiable_arsinh
  结论: 可微 实数 arsinh
  证明: fun x =>
  (hasDerivAt_arsinh x).differentiableAt

@[fun_prop]
-/
theorem differentiable_arsinh : Differentiable Real arsinh := fun x =>
  (hasDerivAt_arsinh x).differentiableAt

@[fun_prop]
/--
theorem `contDiff_arsinh` / 定理 `contDiff_arsinh`

English:
theorem contDiff_arsinh
  given: {n : WithTop Nat∞}
  statement: ContDiff Real n arsinh
  proof: sinhHomeomorph.contDiff_symm_deriv (fun x => (cosh_pos x).ne') hasDerivAt_sinh contDiff_sinh

@[continuity]

中文:
定理 contDiff_arsinh
  条件: {n : WithTop 自然数∞}
  结论: 连续可微 实数 n arsinh
  证明: sinhHomeomorph.contDiff_symm_deriv (fun x => (cosh_pos x).ne') hasDerivAt_sinh contDiff_sinh

@[continuity]

Depends on / 依赖: contDiff_sinh, contDiff_symm_deriv, cosh_pos, hasDerivAt_sinh, sinhHomeomorph, sinhHomeomorph.contDiff_symm_deriv
-/
theorem contDiff_arsinh {n : WithTop Nat∞} : ContDiff Real n arsinh :=
  sinhHomeomorph.contDiff_symm_deriv (fun x => (cosh_pos x).ne') hasDerivAt_sinh contDiff_sinh

@[continuity]
/--
theorem `continuous_arsinh` / 定理 `continuous_arsinh`

English:
theorem continuous_arsinh
  statement: Continuous arsinh
  proof: sinhHomeomorph.symm.continuous

中文:
定理 continuous_arsinh
  结论: 连续 arsinh
  证明: sinhHomeomorph.symm.continuous

Depends on / 依赖: continuous, sinhHomeomorph, sinhHomeomorph.symm.continuous
-/
theorem continuous_arsinh : Continuous arsinh :=
  sinhHomeomorph.symm.continuous

/-- The function `Real.arsinh` is real analytic. -/
@[fun_prop]
/--
lemma `analyticAt_arsinh` / 引理 `analyticAt_arsinh`

English:
lemma analyticAt_arsinh
  statement: AnalyticAt Real arsinh x
  proof: contDiff_arsinh.contDiffAt.analyticAt

中文:
引理 analyticAt_arsinh
  结论: AnalyticAt 实数 arsinh x
  证明: contDiff_arsinh.contDiffAt.analyticAt

Depends on / 依赖: analyticAt, contDiffAt, contDiff_arsinh, contDiff_arsinh.contDiffAt.analyticAt
-/
lemma analyticAt_arsinh : AnalyticAt Real arsinh x :=
  contDiff_arsinh.contDiffAt.analyticAt

/--
lemma `analyticWithinAt_arsinh` / 引理 `analyticWithinAt_arsinh`

English:
lemma analyticWithinAt_arsinh
  given: {s : Set Real}
  statement: AnalyticWithinAt Real arsinh s x
  proof: contDiff_arsinh.contDiffWithinAt.analyticWithinAt

中文:
引理 analyticWithinAt_arsinh
  条件: {s : 集合 实数}
  结论: AnalyticWithinAt 实数 arsinh s x
  证明: contDiff_arsinh.contDiffWithinAt.analyticWithinAt

Depends on / 依赖: analyticWithinAt, contDiffWithinAt, contDiff_arsinh, contDiff_arsinh.contDiffWithinAt.analyticWithinAt
-/
lemma analyticWithinAt_arsinh {s : Set Real} : AnalyticWithinAt Real arsinh s x :=
  contDiff_arsinh.contDiffWithinAt.analyticWithinAt

/--
theorem `analyticOnNhd_arsinh` / 定理 `analyticOnNhd_arsinh`

English:
theorem analyticOnNhd_arsinh
  given: {s : Set Real}
  statement: AnalyticOnNhd Real arsinh s
  proof: fun _ _ => analyticAt_arsinh

中文:
定理 analyticOnNhd_arsinh
  条件: {s : 集合 实数}
  结论: AnalyticOnNhd 实数 arsinh s
  证明: fun _ _ => analyticAt_arsinh

Depends on / 依赖: analyticAt_arsinh
-/
theorem analyticOnNhd_arsinh {s : Set Real} : AnalyticOnNhd Real arsinh s :=
  fun _ _ => analyticAt_arsinh

/--
lemma `analyticOn_arsinh` / 引理 `analyticOn_arsinh`

English:
lemma analyticOn_arsinh
  given: {s : Set Real}
  statement: AnalyticOn Real arsinh s
  proof: contDiff_arsinh.contDiffOn.analyticOn

中文:
引理 analyticOn_arsinh
  条件: {s : 集合 实数}
  结论: AnalyticOn 实数 arsinh s
  证明: contDiff_arsinh.contDiffOn.analyticOn

Depends on / 依赖: analyticOn, contDiffOn, contDiff_arsinh, contDiff_arsinh.contDiffOn.analyticOn
-/
lemma analyticOn_arsinh {s : Set Real} : AnalyticOn Real arsinh s :=
  contDiff_arsinh.contDiffOn.analyticOn

end Real

open Real

/--
theorem `Filter.Tendsto.arsinh` / 定理 `Filter.Tendsto.arsinh`

English:
theorem Filter.Tendsto.arsinh
  statement: {α : Type*} {l : Filter α} {f : α -> Real} {a : Real}
  proof: (continuous_arsinh.tendsto _).comp h

中文:
定理 滤子.收敛.arsinh
  结论: {α : 类型} {l : 滤子 α} {f : α -> 实数} {a : 实数}
  证明: (continuous_arsinh.tendsto _).comp h

Depends on / 依赖: continuous_arsinh, continuous_arsinh.tendsto, tendsto
-/
theorem Filter.Tendsto.arsinh {α : Type*} {l : Filter α} {f : α -> Real} {a : Real}
    (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => arsinh (f x)) l (𝓝 (arsinh a)) :=
  (continuous_arsinh.tendsto _).comp h

section Continuous

variable {X : Type*} [TopologicalSpace X] {f : X -> Real} {s : Set X} {a : X}

nonrec theorem ContinuousAt.arsinh (h : ContinuousAt f a) :
    ContinuousAt (fun x => arsinh (f x)) a :=
  h.arsinh

nonrec theorem ContinuousWithinAt.arsinh (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => arsinh (f x)) s a :=
  h.arsinh

/--
theorem `ContinuousOn.arsinh` / 定理 `ContinuousOn.arsinh`

English:
theorem ContinuousOn.arsinh
  given: (h : ContinuousOn f s)
  statement: ContinuousOn (fun x => arsinh (f x)) s
  proof: fun x hx => (h x hx).arsinh

中文:
定理 ContinuousOn.arsinh
  条件: (h : ContinuousOn f s)
  结论: ContinuousOn (fun x => arsinh (f x)) s
  证明: fun x hx => (h x hx).arsinh

Depends on / 依赖: arsinh
-/
theorem ContinuousOn.arsinh (h : ContinuousOn f s) : ContinuousOn (fun x => arsinh (f x)) s :=
  fun x hx => (h x hx).arsinh

/--
theorem `Continuous.arsinh` / 定理 `Continuous.arsinh`

English:
theorem Continuous.arsinh
  given: (h : Continuous f)
  statement: Continuous fun x => arsinh (f x)
  proof: continuous_arsinh.comp h

中文:
定理 连续.arsinh
  条件: (h : 连续 f)
  结论: 连续 fun x => arsinh (f x)
  证明: continuous_arsinh.comp h

Depends on / 依赖: continuous_arsinh, continuous_arsinh.comp
-/
theorem Continuous.arsinh (h : Continuous f) : Continuous fun x => arsinh (f x) :=
  continuous_arsinh.comp h

end Continuous

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f : E -> Real} {s : Set E} {a : E}
  {f' : StrongDual Real E} {n : Nat∞}

/--
theorem `HasStrictFDerivAt.arsinh` / 定理 `HasStrictFDerivAt.arsinh`

English:
theorem HasStrictFDerivAt.arsinh
  given: (hf : HasStrictFDerivAt f f' a)
  proof: (hasStrictDerivAt_arsinh _).comp_hasStrictFDerivAt a hf

中文:
定理 HasStrictFDerivAt.arsinh
  条件: (hf : HasStrictFDerivAt f f' a)
  证明: (hasStrictDerivAt_arsinh _).comp_hasStrictFDerivAt a hf

Depends on / 依赖: comp_hasStrictFDerivAt, hasStrictDerivAt_arsinh
-/
theorem HasStrictFDerivAt.arsinh (hf : HasStrictFDerivAt f f' a) :
    HasStrictFDerivAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a :=
  (hasStrictDerivAt_arsinh _).comp_hasStrictFDerivAt a hf

/--
theorem `HasFDerivAt.arsinh` / 定理 `HasFDerivAt.arsinh`

English:
theorem HasFDerivAt.arsinh
  given: (hf : HasFDerivAt f f' a)
  proof: (hasDerivAt_arsinh _).comp_hasFDerivAt a hf

中文:
定理 在点处Fréchet可导.arsinh
  条件: (hf : 在点处Fréchet可导 f f' a)
  证明: (hasDerivAt_arsinh _).comp_hasFDerivAt a hf

Depends on / 依赖: comp_hasFDerivAt, hasDerivAt_arsinh
-/
theorem HasFDerivAt.arsinh (hf : HasFDerivAt f f' a) :
    HasFDerivAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a :=
  (hasDerivAt_arsinh _).comp_hasFDerivAt a hf

/--
theorem `HasFDerivWithinAt.arsinh` / 定理 `HasFDerivWithinAt.arsinh`

English:
theorem HasFDerivWithinAt.arsinh
  given: (hf : HasFDerivWithinAt f f' s a)
  proof: (hasDerivAt_arsinh _).comp_hasFDerivWithinAt a hf

@[fun_prop]

中文:
定理 HasFDerivWithinAt.arsinh
  条件: (hf : HasFDerivWithinAt f f' s a)
  证明: (hasDerivAt_arsinh _).comp_hasFDerivWithinAt a hf

@[fun_prop]

Depends on / 依赖: comp_hasFDerivWithinAt, hasDerivAt_arsinh
-/
theorem HasFDerivWithinAt.arsinh (hf : HasFDerivWithinAt f f' s a) :
    HasFDerivWithinAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') s a :=
  (hasDerivAt_arsinh _).comp_hasFDerivWithinAt a hf

@[fun_prop]
/--
theorem `DifferentiableAt.arsinh` / 定理 `DifferentiableAt.arsinh`

English:
theorem DifferentiableAt.arsinh
  given: (h : DifferentiableAt Real f a)
  proof: (differentiable_arsinh _).comp a h

@[fun_prop]

中文:
定理 DifferentiableAt.arsinh
  条件: (h : DifferentiableAt 实数 f a)
  证明: (differentiable_arsinh _).comp a h

@[fun_prop]

Depends on / 依赖: differentiable_arsinh
-/
theorem DifferentiableAt.arsinh (h : DifferentiableAt Real f a) :
    DifferentiableAt Real (fun x => arsinh (f x)) a :=
  (differentiable_arsinh _).comp a h

@[fun_prop]
/--
theorem `DifferentiableWithinAt.arsinh` / 定理 `DifferentiableWithinAt.arsinh`

English:
theorem DifferentiableWithinAt.arsinh
  given: (h : DifferentiableWithinAt Real f s a)
  proof: (differentiable_arsinh _).comp_differentiableWithinAt a h

@[fun_prop]

中文:
定理 DifferentiableWithinAt.arsinh
  条件: (h : DifferentiableWithinAt 实数 f s a)
  证明: (differentiable_arsinh _).comp_differentiableWithinAt a h

@[fun_prop]

Depends on / 依赖: comp_differentiableWithinAt, differentiable_arsinh
-/
theorem DifferentiableWithinAt.arsinh (h : DifferentiableWithinAt Real f s a) :
    DifferentiableWithinAt Real (fun x => arsinh (f x)) s a :=
  (differentiable_arsinh _).comp_differentiableWithinAt a h

@[fun_prop]
/--
theorem `DifferentiableOn.arsinh` / 定理 `DifferentiableOn.arsinh`

English:
theorem DifferentiableOn.arsinh
  given: (h : DifferentiableOn Real f s)
  proof: fun x hx => (h x hx).arsinh

@[fun_prop]

中文:
定理 DifferentiableOn.arsinh
  条件: (h : DifferentiableOn 实数 f s)
  证明: fun x hx => (h x hx).arsinh

@[fun_prop]

Depends on / 依赖: arsinh
-/
theorem DifferentiableOn.arsinh (h : DifferentiableOn Real f s) :
    DifferentiableOn Real (fun x => arsinh (f x)) s := fun x hx => (h x hx).arsinh

@[fun_prop]
/--
theorem `Differentiable.arsinh` / 定理 `Differentiable.arsinh`

English:
theorem Differentiable.arsinh
  given: (h : Differentiable Real f)
  statement: Differentiable Real fun x => arsinh (f x)
  proof: differentiable_arsinh.comp h

@[fun_prop]

中文:
定理 可微.arsinh
  条件: (h : 可微 实数 f)
  结论: 可微 实数 fun x => arsinh (f x)
  证明: differentiable_arsinh.comp h

@[fun_prop]

Depends on / 依赖: differentiable_arsinh, differentiable_arsinh.comp
-/
theorem Differentiable.arsinh (h : Differentiable Real f) : Differentiable Real fun x => arsinh (f x) :=
  differentiable_arsinh.comp h

@[fun_prop]
/--
theorem `ContDiffAt.arsinh` / 定理 `ContDiffAt.arsinh`

English:
theorem ContDiffAt.arsinh
  given: (h : ContDiffAt Real n f a)
  statement: ContDiffAt Real n (fun x => arsinh (f x)) a
  proof: contDiff_arsinh.contDiffAt.comp a h

@[fun_prop]

中文:
定理 ContDiffAt.arsinh
  条件: (h : ContDiffAt 实数 n f a)
  结论: ContDiffAt 实数 n (fun x => arsinh (f x)) a
  证明: contDiff_arsinh.contDiffAt.comp a h

@[fun_prop]

Depends on / 依赖: contDiffAt, contDiff_arsinh, contDiff_arsinh.contDiffAt.comp
-/
theorem ContDiffAt.arsinh (h : ContDiffAt Real n f a) : ContDiffAt Real n (fun x => arsinh (f x)) a :=
  contDiff_arsinh.contDiffAt.comp a h

@[fun_prop]
/--
theorem `ContDiffWithinAt.arsinh` / 定理 `ContDiffWithinAt.arsinh`

English:
theorem ContDiffWithinAt.arsinh
  given: (h : ContDiffWithinAt Real n f s a)
  proof: contDiff_arsinh.contDiffAt.comp_contDiffWithinAt a h

@[fun_prop]

中文:
定理 ContDiffWithinAt.arsinh
  条件: (h : ContDiffWithinAt 实数 n f s a)
  证明: contDiff_arsinh.contDiffAt.comp_contDiffWithinAt a h

@[fun_prop]

Depends on / 依赖: comp_contDiffWithinAt, contDiffAt, contDiff_arsinh, contDiff_arsinh.contDiffAt.comp_contDiffWithinAt
-/
theorem ContDiffWithinAt.arsinh (h : ContDiffWithinAt Real n f s a) :
    ContDiffWithinAt Real n (fun x => arsinh (f x)) s a :=
  contDiff_arsinh.contDiffAt.comp_contDiffWithinAt a h

@[fun_prop]
/--
theorem `ContDiff.arsinh` / 定理 `ContDiff.arsinh`

English:
theorem ContDiff.arsinh
  given: (h : ContDiff Real n f)
  statement: ContDiff Real n fun x => arsinh (f x)
  proof: contDiff_arsinh.comp h

@[fun_prop]

中文:
定理 连续可微.arsinh
  条件: (h : 连续可微 实数 n f)
  结论: 连续可微 实数 n fun x => arsinh (f x)
  证明: contDiff_arsinh.comp h

@[fun_prop]

Depends on / 依赖: contDiff_arsinh, contDiff_arsinh.comp
-/
theorem ContDiff.arsinh (h : ContDiff Real n f) : ContDiff Real n fun x => arsinh (f x) :=
  contDiff_arsinh.comp h

@[fun_prop]
/--
theorem `ContDiffOn.arsinh` / 定理 `ContDiffOn.arsinh`

English:
theorem ContDiffOn.arsinh
  given: (h : ContDiffOn Real n f s)
  statement: ContDiffOn Real n (fun x => arsinh (f x)) s
  proof: fun x hx => (h x hx).arsinh

中文:
定理 ContDiffOn.arsinh
  条件: (h : ContDiffOn 实数 n f s)
  结论: ContDiffOn 实数 n (fun x => arsinh (f x)) s
  证明: fun x hx => (h x hx).arsinh

Depends on / 依赖: arsinh
-/
theorem ContDiffOn.arsinh (h : ContDiffOn Real n f s) : ContDiffOn Real n (fun x => arsinh (f x)) s :=
  fun x hx => (h x hx).arsinh

end fderiv

section deriv

variable {f : Real -> Real} {s : Set Real} {a f' : Real}

/--
theorem `HasStrictDerivAt.arsinh` / 定理 `HasStrictDerivAt.arsinh`

English:
theorem HasStrictDerivAt.arsinh
  given: (hf : HasStrictDerivAt f f' a)
  proof: (hasStrictDerivAt_arsinh _).comp a hf

中文:
定理 HasStrictDerivAt.arsinh
  条件: (hf : HasStrictDerivAt f f' a)
  证明: (hasStrictDerivAt_arsinh _).comp a hf

Depends on / 依赖: hasStrictDerivAt_arsinh
-/
theorem HasStrictDerivAt.arsinh (hf : HasStrictDerivAt f f' a) :
    HasStrictDerivAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a :=
  (hasStrictDerivAt_arsinh _).comp a hf

/--
theorem `HasDerivAt.arsinh` / 定理 `HasDerivAt.arsinh`

English:
theorem HasDerivAt.arsinh
  given: (hf : HasDerivAt f f' a)
  proof: (hasDerivAt_arsinh _).comp a hf

中文:
定理 在点处可导.arsinh
  条件: (hf : 在点处可导 f f' a)
  证明: (hasDerivAt_arsinh _).comp a hf

Depends on / 依赖: hasDerivAt_arsinh
-/
theorem HasDerivAt.arsinh (hf : HasDerivAt f f' a) :
    HasDerivAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') a :=
  (hasDerivAt_arsinh _).comp a hf

/--
theorem `HasDerivWithinAt.arsinh` / 定理 `HasDerivWithinAt.arsinh`

English:
theorem HasDerivWithinAt.arsinh
  given: (hf : HasDerivWithinAt f f' s a)
  proof: (hasDerivAt_arsinh _).comp_hasDerivWithinAt a hf

中文:
定理 HasDerivWithinAt.arsinh
  条件: (hf : HasDerivWithinAt f f' s a)
  证明: (hasDerivAt_arsinh _).comp_hasDerivWithinAt a hf

Depends on / 依赖: comp_hasDerivWithinAt, hasDerivAt_arsinh
-/
theorem HasDerivWithinAt.arsinh (hf : HasDerivWithinAt f f' s a) :
    HasDerivWithinAt (fun x => arsinh (f x)) ((√(1 + f a ^ 2))⁻¹ • f') s a :=
  (hasDerivAt_arsinh _).comp_hasDerivWithinAt a hf

end deriv
