/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Definition of `mulExpNegMulSq` and properties

`mulExpNegMulSq` is the mapping `fun (ε : ℝ) (x : ℝ) => x * Real.exp (- (ε * x * x))`. By
composition, it can be used to transform a function `g : E → ℝ` into a bounded function
`mulExpNegMulSq ε ∘ g : E → ℝ = fun x => g x * Real.exp (-ε * g x * g x)` with useful
boundedness and convergence properties.

## Main Properties

- `abs_mulExpNegMulSq_le`: For fixed `ε > 0`, the mapping `x ↦ mulExpNegMulSq ε x` is
  bounded by `Real.sqrt ε⁻¹`;
- `tendsto_mulExpNegMulSq`: For fixed `x : ℝ`, the mapping `mulExpNegMulSq ε x`
  converges pointwise to `x` as `ε → 0`;
- `lipschitzWith_one_mulExpNegMulSq`: For fixed `ε > 0`, the mapping `mulExpNegMulSq ε` is
  Lipschitz with constant `1`;
- `abs_mulExpNegMulSq_comp_le_norm`: For a fixed bounded continuous function `g`, the mapping
  `mulExpNegMulSq ε ∘ g` is bounded by `norm g`, uniformly in `ε ≥ 0`;
-/

@[expose] public section

open NNReal ENNReal BoundedContinuousFunction Filter

open scoped Topology

namespace Real

/-! ### Definition and properties of `fun x => x * Real.exp (- (ε * x * x))` -/

/--
Mapping `fun ε x => x * Real.exp (- (ε * x * x))`. By composition, it can be used to transform
functions into bounded functions.
-/
noncomputable
/--
Definition of `mulExpNegMulSq` / `mulExpNegMulSq` 的定义

English:
definition mulExpNegMulSq
  signature: (ε x : Real)
  body: x * exp (-(ε * x * x))

中文:
定义 mulExpNegMulSq
  签名: (ε x : 实数)
  定义体: x * exp (-(ε * x * x))
-/
def mulExpNegMulSq (ε x : Real) := x * exp (-(ε * x * x))

/--
theorem `mulExpNegSq_apply` / 定理 `mulExpNegSq_apply`

English:
theorem mulExpNegSq_apply
  given: (ε x : Real)
  statement: mulExpNegMulSq ε x = x * exp (-(ε * x * x))
  proof: rfl

中文:
定理 mulExpNegSq_apply
  条件: (ε x : 实数)
  结论: mulExpNegMulSq ε x = x * exp (-(ε * x * x))
  证明: rfl
-/
theorem mulExpNegSq_apply (ε x : Real) : mulExpNegMulSq ε x = x * exp (-(ε * x * x)) := rfl

/--
theorem `neg_mulExpNegMulSq_neg` / 定理 `neg_mulExpNegMulSq_neg`

English:
theorem neg_mulExpNegMulSq_neg
  given: (ε x : Real)
  statement: - mulExpNegMulSq ε (-x) = mulExpNegMulSq ε x
  proof: by
  simp [mulExpNegMulSq]

中文:
定理 neg_mulExpNegMulSq_neg
  条件: (ε x : 实数)
  结论: - mulExpNegMulSq ε (-x) = mulExpNegMulSq ε x
  证明: by
  simp [mulExpNegMulSq]

Depends on / 依赖: mulExpNegMulSq
-/
theorem neg_mulExpNegMulSq_neg (ε x : Real) : - mulExpNegMulSq ε (-x) = mulExpNegMulSq ε x := by
  simp [mulExpNegMulSq]

/--
theorem `mulExpNegMulSq_one_le_one` / 定理 `mulExpNegMulSq_one_le_one`

English:
theorem mulExpNegMulSq_one_le_one
  given: (x : Real)
  statement: mulExpNegMulSq 1 x <= 1
  proof: by
  simp only [mulExpNegMulSq, one_mul]
  rw [← le_div_iff₀ (exp_pos (-(x * x)))]; rw [exp_neg]; rw [div_inv_eq_mul]; rw [one_mul]
  apply le_trans _ (add_one_le_exp (x * x))
  nlinarith

中文:
定理 mulExpNegMulSq_one_le_one
  条件: (x : 实数)
  结论: mulExpNegMulSq 1 x <= 1
  证明: by
  simp only [mulExpNegMulSq, one_mul]
  rw [← le_div_iff₀ (exp_pos (-(x * x)))]; rw [exp_neg]; rw [div_inv_eq_mul]; rw [one_mul]
  apply le_trans _ (add_one_le_exp (x * x))
  nlinarith

Depends on / 依赖: add_one_le_exp, div_inv_eq_mul, exp_neg, exp_pos, le_trans, mulExpNegMulSq, one_mul
-/
theorem mulExpNegMulSq_one_le_one (x : Real) : mulExpNegMulSq 1 x <= 1 := by
  simp only [mulExpNegMulSq, one_mul]
  rw [← le_div_iff₀ (exp_pos (-(x * x)))]; rw [exp_neg]; rw [div_inv_eq_mul]; rw [one_mul]
  apply le_trans _ (add_one_le_exp (x * x))
  nlinarith

/--
theorem `neg_one_le_mulExpNegMulSq_one` / 定理 `neg_one_le_mulExpNegMulSq_one`

English:
theorem neg_one_le_mulExpNegMulSq_one
  given: (x : Real)
  statement: -1 <= mulExpNegMulSq 1 x
  proof: by
  rw [← neg_mulExpNegMulSq_neg]; rw [neg_le_neg_iff]
  exact mulExpNegMulSq_one_le_one (-x)

中文:
定理 neg_one_le_mulExpNegMulSq_one
  条件: (x : 实数)
  结论: -1 <= mulExpNegMulSq 1 x
  证明: by
  rw [← neg_mulExpNegMulSq_neg]; rw [neg_le_neg_iff]
  exact mulExpNegMulSq_one_le_one (-x)

Depends on / 依赖: mulExpNegMulSq_one_le_one, neg_le_neg_iff, neg_mulExpNegMulSq_neg
-/
theorem neg_one_le_mulExpNegMulSq_one (x : Real) : -1 <= mulExpNegMulSq 1 x := by
  rw [← neg_mulExpNegMulSq_neg]; rw [neg_le_neg_iff]
  exact mulExpNegMulSq_one_le_one (-x)

/--
theorem `abs_mulExpNegMulSq_one_le_one` / 定理 `abs_mulExpNegMulSq_one_le_one`

English:
theorem abs_mulExpNegMulSq_one_le_one
  given: (x : Real)
  statement: |mulExpNegMulSq 1 x| <= 1
  proof: abs_le.mpr ⟨neg_one_le_mulExpNegMulSq_one x, mulExpNegMulSq_one_le_one x⟩

中文:
定理 abs_mulExpNegMulSq_one_le_one
  条件: (x : 实数)
  结论: |mulExpNegMulSq 1 x| <= 1
  证明: abs_le.mpr ⟨neg_one_le_mulExpNegMulSq_one x, mulExpNegMulSq_one_le_one x⟩

Depends on / 依赖: abs_le, abs_le.mpr, mulExpNegMulSq_one_le_one, neg_one_le_mulExpNegMulSq_one
-/
theorem abs_mulExpNegMulSq_one_le_one (x : Real) : |mulExpNegMulSq 1 x| <= 1 :=
  abs_le.mpr ⟨neg_one_le_mulExpNegMulSq_one x, mulExpNegMulSq_one_le_one x⟩

variable {ε : Real}

@[continuity, fun_prop]
/--
theorem `continuous_mulExpNegMulSq` / 定理 `continuous_mulExpNegMulSq`

English:
theorem continuous_mulExpNegMulSq
  statement: Continuous (fun x => mulExpNegMulSq ε x)
  proof: Continuous.mul continuous_id (by fun_prop)

@[continuity, fun_prop]

中文:
定理 continuous_mulExpNegMulSq
  结论: 连续 (fun x => mulExpNegMulSq ε x)
  证明: Continuous.mul continuous_id (by fun_prop)

@[continuity, fun_prop]

Depends on / 依赖: Continuous, Continuous.mul, continuous_id, fun_prop
-/
theorem continuous_mulExpNegMulSq : Continuous (fun x => mulExpNegMulSq ε x) :=
  Continuous.mul continuous_id (by fun_prop)

@[continuity, fun_prop]
/--
theorem `_root_.Continuous.mulExpNegMulSq` / 定理 `_root_.Continuous.mulExpNegMulSq`

English:
theorem _root_.Continuous.mulExpNegMulSq
  statement: {α : Type*} [TopologicalSpace α] {f : α -> Real}
  proof: continuous_mulExpNegMulSq.comp hf

中文:
定理 _root_.连续.mulExpNegMulSq
  结论: {α : 类型} [拓扑空间 α] {f : α -> 实数}
  证明: continuous_mulExpNegMulSq.comp hf

Depends on / 依赖: continuous_mulExpNegMulSq, continuous_mulExpNegMulSq.comp
-/
theorem _root_.Continuous.mulExpNegMulSq {α : Type*} [TopologicalSpace α] {f : α -> Real}
    (hf : Continuous f) : Continuous (fun x => mulExpNegMulSq ε (f x)) :=
  continuous_mulExpNegMulSq.comp hf

/--
theorem `differentiableAt_mulExpNegMulSq` / 定理 `differentiableAt_mulExpNegMulSq`

English:
theorem differentiableAt_mulExpNegMulSq
  given: (y : Real)
  proof: DifferentiableAt.mul differentiableAt_fun_id (by fun_prop)

中文:
定理 differentiableAt_mulExpNegMulSq
  条件: (y : 实数)
  证明: DifferentiableAt.mul differentiableAt_fun_id (by fun_prop)

Depends on / 依赖: DifferentiableAt, DifferentiableAt.mul, differentiableAt_fun_id, fun_prop
-/
theorem differentiableAt_mulExpNegMulSq (y : Real) :
    DifferentiableAt Real (mulExpNegMulSq ε) y :=
  DifferentiableAt.mul differentiableAt_fun_id (by fun_prop)

/--
theorem `differentiable_mulExpNegMulSq` / 定理 `differentiable_mulExpNegMulSq`

English:
theorem differentiable_mulExpNegMulSq
  statement: Differentiable Real (mulExpNegMulSq ε)
  proof: fun _ => differentiableAt_mulExpNegMulSq _

中文:
定理 differentiable_mulExpNegMulSq
  结论: 可微 实数 (mulExpNegMulSq ε)
  证明: fun _ => differentiableAt_mulExpNegMulSq _
-/
@[fun_prop] theorem differentiable_mulExpNegMulSq : Differentiable Real (mulExpNegMulSq ε) :=
  fun _ => differentiableAt_mulExpNegMulSq _

/--
theorem `hasDerivAt_mulExpNegMulSq` / 定理 `hasDerivAt_mulExpNegMulSq`

English:
theorem hasDerivAt_mulExpNegMulSq
  given: (y : Real)
  proof: by
  nth_rw 1 [← one_mul (exp (-(ε * y * y)))]
  apply HasDerivAt.mul (hasDerivAt_id' y)
  apply HasDerivAt.exp (HasDerivAt.congr_deriv (HasDerivAt.neg
    (HasDerivAt.mul (HasDerivAt.const_mul ε (hasDerivAt_id' y)) (hasDerivAt_id' y))) (by ring))

中文:
定理 hasDerivAt_mulExpNegMulSq
  条件: (y : 实数)
  证明: by
  nth_rw 1 [← one_mul (exp (-(ε * y * y)))]
  apply HasDerivAt.mul (hasDerivAt_id' y)
  apply HasDerivAt.exp (HasDerivAt.congr_deriv (HasDerivAt.neg
    (HasDerivAt.mul (HasDerivAt.const_mul ε (hasDerivAt_id' y)) (hasDerivAt_id' y))) (by ring))

Depends on / 依赖: HasDerivAt, HasDerivAt.congr_deriv, HasDerivAt.const_mul, HasDerivAt.exp, HasDerivAt.mul, HasDerivAt.neg, congr_deriv, const_mul, hasDerivAt_id, nth_rw, one_mul
-/
theorem hasDerivAt_mulExpNegMulSq (y : Real) :
    HasDerivAt (mulExpNegMulSq ε)
    (exp (-(ε * y * y)) + y * (exp (-(ε * y * y)) * (-2 * ε * y))) y := by
  nth_rw 1 [← one_mul (exp (-(ε * y * y)))]
  apply HasDerivAt.mul (hasDerivAt_id' y)
  apply HasDerivAt.exp (HasDerivAt.congr_deriv (HasDerivAt.neg
    (HasDerivAt.mul (HasDerivAt.const_mul ε (hasDerivAt_id' y)) (hasDerivAt_id' y))) (by ring))

/--
theorem `deriv_mulExpNegMulSq` / 定理 `deriv_mulExpNegMulSq`

English:
theorem deriv_mulExpNegMulSq
  given: (y : Real)
  statement: deriv (mulExpNegMulSq ε) y =
  proof: HasDerivAt.deriv (hasDerivAt_mulExpNegMulSq y)

中文:
定理 deriv_mulExpNegMulSq
  条件: (y : 实数)
  结论: deriv (mulExpNegMulSq ε) y =
  证明: HasDerivAt.deriv (hasDerivAt_mulExpNegMulSq y)

Depends on / 依赖: HasDerivAt, HasDerivAt.deriv, hasDerivAt_mulExpNegMulSq
-/
theorem deriv_mulExpNegMulSq (y : Real) : deriv (mulExpNegMulSq ε) y =
    exp (-(ε * y * y)) + y * (exp (-(ε * y * y)) * (-2 * ε * y)) :=
  HasDerivAt.deriv (hasDerivAt_mulExpNegMulSq y)

/--
theorem `norm_deriv_mulExpNegMulSq_le_one` / 定理 `norm_deriv_mulExpNegMulSq_le_one`

English:
theorem norm_deriv_mulExpNegMulSq_le_one
  given: (hε : 0 < ε) (x : Real)
  proof: by
  rw [norm_eq_abs]; rw [deriv_mulExpNegMulSq]
  have heq : exp (-(ε * x * x)) + x * (exp (-(ε * x * x)) * (-2 * ε * x))
      = exp (-(ε * x * x)) * (1 - 2 * (ε * x * x)) := by ring
  rw [heq]; rw [abs_mul]; rw [abs_exp]
  set y := ε * x * x with hy
  have hynonneg : 0 <= y := by
    rw [hy]; rw [mul_assoc]
    exact mul_nonneg hε.le (mul_self_nonneg x)
  apply mul_le_of_le_inv_mul₀ (zero_le_one' Real) (exp_nonneg _)
  simp only [← exp_neg (-y), neg_neg, mul_one, abs_le, neg_le_sub_iff_le_add, tsub_le_iff_right]
  refine ⟨le_trans two_mul_le_exp ((le_add_iff_nonneg_left (exp y)).mpr zero_le_one), ?_⟩
  exact le_trans (one_le_exp hynonneg) (le_add_of_nonneg_right (by simp [hynonneg]))

中文:
定理 norm_deriv_mulExpNegMulSq_le_one
  条件: (hε : 0 < ε) (x : 实数)
  证明: by
  rw [norm_eq_abs]; rw [deriv_mulExpNegMulSq]
  have heq : exp (-(ε * x * x)) + x * (exp (-(ε * x * x)) * (-2 * ε * x))
      = exp (-(ε * x * x)) * (1 - 2 * (ε * x * x)) := by ring
  rw [heq]; rw [abs_mul]; rw [abs_exp]
  set y := ε * x * x with hy
  have hynonneg : 0 <= y := by
    rw [hy]; rw [mul_assoc]
    exact mul_nonneg hε.le (mul_self_nonneg x)
  apply mul_le_of_le_inv_mul₀ (zero_le_one' Real) (exp_nonneg _)
  simp only [← exp_neg (-y), neg_neg, mul_one, abs_le, neg_le_sub_iff_le_add, tsub_le_iff_right]
  refine ⟨le_trans two_mul_le_exp ((le_add_iff_nonneg_left (exp y)).mpr zero_le_one), ?_⟩
  exact le_trans (one_le_exp hynonneg) (le_add_of_nonneg_right (by simp [hynonneg]))

Depends on / 依赖: abs_exp, abs_le, abs_mul, deriv_mulExpNegMulSq, exp_neg, exp_nonneg, hynonneg, mul_assoc, mul_nonneg, mul_one, mul_self_nonneg, neg_le_sub_iff_le_add, neg_neg, norm_eq_abs, tsub_le_iff_right, zero_le_one
-/
theorem norm_deriv_mulExpNegMulSq_le_one (hε : 0 < ε) (x : Real) :
    ‖deriv (mulExpNegMulSq ε) x‖ <= 1 := by
  rw [norm_eq_abs]; rw [deriv_mulExpNegMulSq]
  have heq : exp (-(ε * x * x)) + x * (exp (-(ε * x * x)) * (-2 * ε * x))
      = exp (-(ε * x * x)) * (1 - 2 * (ε * x * x)) := by ring
  rw [heq]; rw [abs_mul]; rw [abs_exp]
  set y := ε * x * x with hy
  have hynonneg : 0 <= y := by
    rw [hy]; rw [mul_assoc]
    exact mul_nonneg hε.le (mul_self_nonneg x)
  apply mul_le_of_le_inv_mul₀ (zero_le_one' Real) (exp_nonneg _)
  simp only [← exp_neg (-y), neg_neg, mul_one, abs_le, neg_le_sub_iff_le_add, tsub_le_iff_right]
  refine ⟨le_trans two_mul_le_exp ((le_add_iff_nonneg_left (exp y)).mpr zero_le_one), ?_⟩
  exact le_trans (one_le_exp hynonneg) (le_add_of_nonneg_right (by simp [hynonneg]))

/--
theorem `nnnorm_deriv_mulExpNegMulSq_le_one` / 定理 `nnnorm_deriv_mulExpNegMulSq_le_one`

English:
theorem nnnorm_deriv_mulExpNegMulSq_le_one
  given: (hε : 0 < ε) (x : Real)
  proof: by
  rw [← NNReal.coe_le_coe]; rw [coe_nnnorm]
  exact norm_deriv_mulExpNegMulSq_le_one hε x

中文:
定理 nnnorm_deriv_mulExpNegMulSq_le_one
  条件: (hε : 0 < ε) (x : 实数)
  证明: by
  rw [← NNReal.coe_le_coe]; rw [coe_nnnorm]
  exact norm_deriv_mulExpNegMulSq_le_one hε x

Depends on / 依赖: NNReal, NNReal.coe_le_coe, coe_le_coe, coe_nnnorm, norm_deriv_mulExpNegMulSq_le_one
-/
theorem nnnorm_deriv_mulExpNegMulSq_le_one (hε : 0 < ε) (x : Real) :
    ‖deriv (mulExpNegMulSq ε) x‖₊ <= 1 := by
  rw [← NNReal.coe_le_coe]; rw [coe_nnnorm]
  exact norm_deriv_mulExpNegMulSq_le_one hε x

/--
theorem `lipschitzWith_one_mulExpNegMulSq` / 定理 `lipschitzWith_one_mulExpNegMulSq`

English:
theorem lipschitzWith_one_mulExpNegMulSq
  given: (hε : 0 < ε)
  proof: by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_mulExpNegMulSq
  exact nnnorm_deriv_mulExpNegMulSq_le_one hε

中文:
定理 lipschitzWith_one_mulExpNegMulSq
  条件: (hε : 0 < ε)
  证明: by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_mulExpNegMulSq
  exact nnnorm_deriv_mulExpNegMulSq_le_one hε

Depends on / 依赖: differentiable_mulExpNegMulSq, lipschitzWith_of_nnnorm_deriv_le, nnnorm_deriv_mulExpNegMulSq_le_one
-/
theorem lipschitzWith_one_mulExpNegMulSq (hε : 0 < ε) :
    LipschitzWith 1 (mulExpNegMulSq ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_mulExpNegMulSq
  exact nnnorm_deriv_mulExpNegMulSq_le_one hε

/--
theorem `mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one` / 定理 `mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one`

English:
theorem mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one
  given: (hε : 0 < ε) (x : Real)
  proof: by
  grind [mulExpNegMulSq]

中文:
定理 mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one
  条件: (hε : 0 < ε) (x : 实数)
  证明: by
  grind [mulExpNegMulSq]

Depends on / 依赖: mulExpNegMulSq
-/
theorem mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one (hε : 0 < ε) (x : Real) :
    mulExpNegMulSq ε x = (√ε)⁻¹ * mulExpNegMulSq 1 (sqrt ε * x) := by
  grind [mulExpNegMulSq]

/--
theorem `abs_mulExpNegMulSq_le` / 定理 `abs_mulExpNegMulSq_le`

English:
theorem abs_mulExpNegMulSq_le
  given: (hε : 0 < ε) {x : Real}
  statement: |mulExpNegMulSq ε x| <= (√ε)⁻¹
  proof: by
  rw [mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one hε x]; rw [abs_mul]; rw [abs_of_pos (by positivity)]
  apply mul_le_of_le_one_right
  · positivity
  · exact abs_mulExpNegMulSq_one_le_one (√ε * x)

中文:
定理 abs_mulExpNegMulSq_le
  条件: (hε : 0 < ε) {x : 实数}
  结论: |mulExpNegMulSq ε x| <= (√ε)⁻¹
  证明: by
  rw [mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one hε x]; rw [abs_mul]; rw [abs_of_pos (by positivity)]
  apply mul_le_of_le_one_right
  · positivity
  · exact abs_mulExpNegMulSq_one_le_one (√ε * x)

Depends on / 依赖: abs_mul, abs_mulExpNegMulSq_one_le_one, abs_of_pos, mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one, mul_le_of_le_one_right
-/
theorem abs_mulExpNegMulSq_le (hε : 0 < ε) {x : Real} : |mulExpNegMulSq ε x| <= (√ε)⁻¹ := by
  rw [mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one hε x]; rw [abs_mul]; rw [abs_of_pos (by positivity)]
  apply mul_le_of_le_one_right
  · positivity
  · exact abs_mulExpNegMulSq_one_le_one (√ε * x)

/--
theorem `dist_mulExpNegMulSq_le_two_mul_sqrt` / 定理 `dist_mulExpNegMulSq_le_two_mul_sqrt`

English:
theorem dist_mulExpNegMulSq_le_two_mul_sqrt
  given: (hε : 0 < ε) (x y : Real)
  proof: by
  apply le_trans (dist_triangle (mulExpNegMulSq ε x) 0 (mulExpNegMulSq ε y))
  simp only [dist_zero_right, norm_eq_abs, dist_zero_left, two_mul]
  exact add_le_add (abs_mulExpNegMulSq_le hε) (abs_mulExpNegMulSq_le hε)

中文:
定理 dist_mulExpNegMulSq_le_two_mul_sqrt
  条件: (hε : 0 < ε) (x y : 实数)
  证明: by
  apply le_trans (dist_triangle (mulExpNegMulSq ε x) 0 (mulExpNegMulSq ε y))
  simp only [dist_zero_right, norm_eq_abs, dist_zero_left, two_mul]
  exact add_le_add (abs_mulExpNegMulSq_le hε) (abs_mulExpNegMulSq_le hε)

Depends on / 依赖: abs_mulExpNegMulSq_le, add_le_add, dist_triangle, dist_zero_left, dist_zero_right, le_trans, mulExpNegMulSq, norm_eq_abs, two_mul
-/
theorem dist_mulExpNegMulSq_le_two_mul_sqrt (hε : 0 < ε) (x y : Real) :
    dist (mulExpNegMulSq ε x) (mulExpNegMulSq ε y) <= 2 * (√ε)⁻¹ := by
  apply le_trans (dist_triangle (mulExpNegMulSq ε x) 0 (mulExpNegMulSq ε y))
  simp only [dist_zero_right, norm_eq_abs, dist_zero_left, two_mul]
  exact add_le_add (abs_mulExpNegMulSq_le hε) (abs_mulExpNegMulSq_le hε)

/--
theorem `dist_mulExpNegMulSq_le_dist` / 定理 `dist_mulExpNegMulSq_le_dist`

English:
theorem dist_mulExpNegMulSq_le_dist
  given: (hε : 0 < ε) {x y : Real}
  proof: by
  have h := lipschitzWith_one_mulExpNegMulSq hε x y
  rwa [ENNReal.coe_one, one_mul, ← (toReal_le_toReal (edist_ne_top _ _) (edist_ne_top _ _))] at h

中文:
定理 dist_mulExpNegMulSq_le_dist
  条件: (hε : 0 < ε) {x y : 实数}
  证明: by
  have h := lipschitzWith_one_mulExpNegMulSq hε x y
  rwa [ENNReal.coe_one, one_mul, ← (toReal_le_toReal (edist_ne_top _ _) (edist_ne_top _ _))] at h

Depends on / 依赖: ENNReal, ENNReal.coe_one, coe_one, edist_ne_top, lipschitzWith_one_mulExpNegMulSq, one_mul, toReal_le_toReal
-/
theorem dist_mulExpNegMulSq_le_dist (hε : 0 < ε) {x y : Real} :
    dist (mulExpNegMulSq ε x) (mulExpNegMulSq ε y) <= dist x y := by
  have h := lipschitzWith_one_mulExpNegMulSq hε x y
  rwa [ENNReal.coe_one, one_mul, ← (toReal_le_toReal (edist_ne_top _ _) (edist_ne_top _ _))] at h

/--
theorem `tendsto_mulExpNegMulSq` / 定理 `tendsto_mulExpNegMulSq`

English:
theorem tendsto_mulExpNegMulSq
  given: {x : Real}
  proof: by
  have : x = (fun ε : Real => mulExpNegMulSq ε x) 0 := by
    simp only [mulExpNegMulSq, zero_mul, neg_zero, exp_zero, mul_one]
  nth_rw 2 [this]
  apply Continuous.tendsto (Continuous.mul continuous_const (by fun_prop))

中文:
定理 tendsto_mulExpNegMulSq
  条件: {x : 实数}
  证明: by
  have : x = (fun ε : Real => mulExpNegMulSq ε x) 0 := by
    simp only [mulExpNegMulSq, zero_mul, neg_zero, exp_zero, mul_one]
  nth_rw 2 [this]
  apply Continuous.tendsto (Continuous.mul continuous_const (by fun_prop))

Depends on / 依赖: Continuous, Continuous.mul, Continuous.tendsto, continuous_const, exp_zero, fun_prop, mulExpNegMulSq, mul_one, neg_zero, nth_rw, tendsto, zero_mul
-/
theorem tendsto_mulExpNegMulSq {x : Real} :
    Tendsto (fun ε => mulExpNegMulSq ε x) (𝓝 0) (𝓝 x) := by
  have : x = (fun ε : Real => mulExpNegMulSq ε x) 0 := by
    simp only [mulExpNegMulSq, zero_mul, neg_zero, exp_zero, mul_one]
  nth_rw 2 [this]
  apply Continuous.tendsto (Continuous.mul continuous_const (by fun_prop))

/--
theorem `abs_mulExpNegMulSq_comp_le_norm` / 定理 `abs_mulExpNegMulSq_comp_le_norm`

English:
theorem abs_mulExpNegMulSq_comp_le_norm
  statement: {E : Type*} [TopologicalSpace E] {x : E}
  proof: by
  simp only [Function.comp_apply, mulExpNegMulSq, abs_mul, abs_exp]
  apply le_trans (mul_le_of_le_one_right (abs_nonneg (g x)) _) (g.norm_coe_le_norm x)
  rw [exp_le_one_iff]; rw [Left.neg_nonpos_iff]; rw [mul_assoc]
  exact mul_nonneg hε (mul_self_nonneg (g x))

中文:
定理 abs_mulExpNegMulSq_comp_le_norm
  结论: {E : 类型} [拓扑空间 E] {x : E}
  证明: by
  simp only [Function.comp_apply, mulExpNegMulSq, abs_mul, abs_exp]
  apply le_trans (mul_le_of_le_one_right (abs_nonneg (g x)) _) (g.norm_coe_le_norm x)
  rw [exp_le_one_iff]; rw [Left.neg_nonpos_iff]; rw [mul_assoc]
  exact mul_nonneg hε (mul_self_nonneg (g x))

Depends on / 依赖: Function, Function.comp_apply, Left.neg_nonpos_iff, abs_exp, abs_mul, abs_nonneg, comp_apply, exp_le_one_iff, g.norm_coe_le_norm, le_trans, mulExpNegMulSq, mul_assoc, mul_le_of_le_one_right, mul_nonneg, mul_self_nonneg, neg_nonpos_iff, norm_coe_le_norm
-/
theorem abs_mulExpNegMulSq_comp_le_norm {E : Type*} [TopologicalSpace E] {x : E}
    (g : BoundedContinuousFunction E Real) (hε : 0 <= ε) :
    |(mulExpNegMulSq ε ∘ g) x| <= ‖g‖ := by
  simp only [Function.comp_apply, mulExpNegMulSq, abs_mul, abs_exp]
  apply le_trans (mul_le_of_le_one_right (abs_nonneg (g x)) _) (g.norm_coe_le_norm x)
  rw [exp_le_one_iff]; rw [Left.neg_nonpos_iff]; rw [mul_assoc]
  exact mul_nonneg hε (mul_self_nonneg (g x))

end Real
