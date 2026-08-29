/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.MetricSpace.CauSeqFilter

/-!
# Calculus results on exponential in a Banach algebra

In this file, we prove basic properties about the derivative of the exponential map `exp`
in a Banach algebra `𝔸` over a field `𝕂`. We keep them separate from the main file
`Analysis.Normed.Algebra.Exponential` in order to minimize dependencies.

## Main results

We prove most results for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `hasStrictFDerivAt_exp_zero_of_radius_pos` : `NormedSpace.exp` has strict Fréchet derivative
  `1 : 𝔸 →L[𝕂] 𝔸` at zero, as long as it converges on a neighborhood of zero
  (see also `hasStrictDerivAt_exp_zero_of_radius_pos` for the case `𝔸 = 𝕂`)
- `hasStrictFDerivAt_exp_of_lt_radius` : if `𝕂` has characteristic zero and `𝔸` is commutative,
  then given a point `x` in the disk of convergence, `NormedSpace.exp` has strict Fréchet
  derivative `NormedSpace.exp x • 1 : 𝔸 →L[𝕂] 𝔸` at x
  (see also `hasStrictDerivAt_exp_of_lt_radius` for the case `𝔸 = 𝕂`)
- `hasStrictFDerivAt_exp_smul_const_of_mem_ball`: even when `𝔸` is non-commutative,
  if we have an intermediate algebra `𝕊` which is commutative, the function
  `(u : 𝕊) ↦ NormedSpace.exp (u • x)`, still has strict Fréchet derivative
  `NormedSpace.exp (t • x) • (1 : 𝕊 →L[𝕂] 𝕊).smulRight x` at `t` if
  `t • x` is in the radius of convergence.

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `hasStrictFDerivAt_exp_zero` : `NormedSpace.exp` has strict Fréchet derivative `1 : 𝔸 →L[𝕂] 𝔸`
  at zero (see also `hasStrictDerivAt_exp_zero` for the case `𝔸 = 𝕂`)
- `hasStrictFDerivAt_exp` : if `𝔸` is commutative, then given any point `x`, `NormedSpace.exp`
  has strict Fréchet derivative `NormedSpace.exp x • 1 : 𝔸 →L[𝕂] 𝔸` at x
  (see also `hasStrictDerivAt_exp` for the case `𝔸 = 𝕂`)
- `hasStrictFDerivAt_exp_smul_const`: even when `𝔸` is non-commutative, if we have
  an intermediate algebra `𝕊` which is commutative, the function
  `(u : 𝕊) ↦ NormedSpace.exp (u • x)` still has strict Fréchet derivative
  `NormedSpace.exp (t • x) • (1 : 𝔸 →L[𝕂] 𝔸).smulRight x` at `t`.

### Compatibility with `Real.exp` and `Complex.exp`

- `Complex.exp_eq_exp_ℂ` : `Complex.exp = NormedSpace.exp ℂ ℂ`
- `Real.exp_eq_exp_ℝ` : `Real.exp = NormedSpace.exp ℝ ℝ`

-/

public section


open Filter RCLike ContinuousMultilinearMap NormedField NormedSpace Asymptotics

open scoped Nat Topology ENNReal

section AnyFieldAnyAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedRing 𝔸] [CharZero 𝕂] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

/--
theorem `hasStrictFDerivAt_exp_zero_of_radius_pos` / 定理 `hasStrictFDerivAt_exp_zero_of_radius_pos`

English:
theorem hasStrictFDerivAt_exp_zero_of_radius_pos
  given: (h : 0 < (expSeries 𝕂 𝔸).radius)
  proof: by
  convert! (hasFPowerSeriesAt_exp_zero_of_radius_pos h).hasStrictFDerivAt
  ext x
  change x = expSeries 𝕂 𝔸 1 fun _ => x
  simp [expSeries_apply_eq, Nat.factorial]

中文:
定理 hasStrictFDerivAt_exp_zero_of_radius_pos
  条件: (h : 0 < (expSeries 𝕂 𝔸).radius)
  证明: by
  convert! (hasFPowerSeriesAt_exp_zero_of_radius_pos h).hasStrictFDerivAt
  ext x
  change x = expSeries 𝕂 𝔸 1 fun _ => x
  simp [expSeries_apply_eq, Nat.factorial]

Depends on / 依赖: Nat.factorial, convert, expSeries, expSeries_apply_eq, factorial, hasFPowerSeriesAt_exp_zero_of_radius_pos, hasStrictFDerivAt
-/
theorem hasStrictFDerivAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasStrictFDerivAt exp (1 : 𝔸 ->L[𝕂] 𝔸) 0 := by
  convert! (hasFPowerSeriesAt_exp_zero_of_radius_pos h).hasStrictFDerivAt
  ext x
  change x = expSeries 𝕂 𝔸 1 fun _ => x
  simp [expSeries_apply_eq, Nat.factorial]

/--
theorem `hasFDerivAt_exp_zero_of_radius_pos` / 定理 `hasFDerivAt_exp_zero_of_radius_pos`

English:
theorem hasFDerivAt_exp_zero_of_radius_pos
  given: (h : 0 < (expSeries 𝕂 𝔸).radius)
  proof: (hasStrictFDerivAt_exp_zero_of_radius_pos h).hasFDerivAt

中文:
定理 hasFDerivAt_exp_zero_of_radius_pos
  条件: (h : 0 < (expSeries 𝕂 𝔸).radius)
  证明: (hasStrictFDerivAt_exp_zero_of_radius_pos h).hasFDerivAt

Depends on / 依赖: hasFDerivAt, hasStrictFDerivAt_exp_zero_of_radius_pos
-/
theorem hasFDerivAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝔸).radius) :
    HasFDerivAt exp (1 : 𝔸 ->L[𝕂] 𝔸) 0 :=
  (hasStrictFDerivAt_exp_zero_of_radius_pos h).hasFDerivAt

end AnyFieldAnyAlgebra

section AnyFieldCommAlgebra

variable {𝕂 𝔸 : Type*} [NontriviallyNormedField 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸] [CharZero 𝕂]

/--
theorem `hasFDerivAt_exp_of_mem_ball` / 定理 `hasFDerivAt_exp_of_mem_ball`

English:
theorem hasFDerivAt_exp_of_mem_ball
  statement: {x : 𝔸}
  proof: by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  suffices
    (fun h => exp x * (exp (0 + h) - exp 0 - ContinuousLinearMap.id 𝕂 𝔸 h)) =ᶠ[𝓝 0] fun h =>
      exp (x + h) - exp x - exp x • ContinuousLinearMap.id 𝕂 𝔸 h by
    refine (IsLittleO.const_mul_left ?_ _).congr' this (EventuallyEq.refl _ _)
   

中文:
定理 hasFDerivAt_exp_of_mem_ball
  结论: {x : 𝔸}
  证明: by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  suffices
    (fun h => exp x * (exp (0 + h) - exp 0 - ContinuousLinearMap.id 𝕂 𝔸 h)) =ᶠ[𝓝 0] fun h =>
      exp (x + h) - exp x - exp x • ContinuousLinearMap.id 𝕂 𝔸 h by
    refine (IsLittleO.const_mul_left ?_ _).congr' this (EventuallyEq.refl _ _)
   

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, EventuallyEq, EventuallyEq.refl, IsLittleO, IsLittleO.const_mul_left, Metric, Metric.eball, Metric.eball_mem_nhds, const_mul_left, eball_mem_nhds, expSeries, filter_upwards, hasFDerivAt_exp_zero_of_radius_pos, hasFDerivAt_iff_isLittleO_nhds_zero, hx.pos, radius
-/
theorem hasFDerivAt_exp_of_mem_ball {x : 𝔸}
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasFDerivAt exp (exp x • (1 : 𝔸 ->L[𝕂] 𝔸)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  suffices
    (fun h => exp x * (exp (0 + h) - exp 0 - ContinuousLinearMap.id 𝕂 𝔸 h)) =ᶠ[𝓝 0] fun h =>
      exp (x + h) - exp x - exp x • ContinuousLinearMap.id 𝕂 𝔸 h by
    refine (IsLittleO.const_mul_left ?_ _).congr' this (EventuallyEq.refl _ _)
    rw [← hasFDerivAt_iff_isLittleO_nhds_zero]
    exact hasFDerivAt_exp_zero_of_radius_pos hx.pos
  have : forallᶠ h in 𝓝 (0 : 𝔸), h in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius :=
    Metric.eball_mem_nhds _ hx.pos
  filter_upwards [this] with _ hh
  rw [exp_add_of_mem_ball hx hh]; rw [exp_zero]; rw [zero_add]; rw [ContinuousLinearMap.id_apply]; rw [smul_eq_mul]
  ring

/--
theorem `hasStrictFDerivAt_exp_of_mem_ball` / 定理 `hasStrictFDerivAt_exp_of_mem_ball`

English:
theorem hasStrictFDerivAt_exp_of_mem_ball
  statement: {x : 𝔸}
  proof: let ⟨_, hp⟩ := analyticAt_exp_of_mem_ball x hx
  hp.hasFDerivAt.unique (hasFDerivAt_exp_of_mem_ball hx) ▸ hp.hasStrictFDerivAt

中文:
定理 hasStrictFDerivAt_exp_of_mem_ball
  结论: {x : 𝔸}
  证明: let ⟨_, hp⟩ := analyticAt_exp_of_mem_ball x hx
  hp.hasFDerivAt.unique (hasFDerivAt_exp_of_mem_ball hx) ▸ hp.hasStrictFDerivAt

Depends on / 依赖: analyticAt_exp_of_mem_ball, hasFDerivAt, hasFDerivAt_exp_of_mem_ball, hasStrictFDerivAt, hp.hasFDerivAt.unique, hp.hasStrictFDerivAt, unique
-/
theorem hasStrictFDerivAt_exp_of_mem_ball {x : 𝔸}
    (hx : x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictFDerivAt exp (exp x • (1 : 𝔸 ->L[𝕂] 𝔸)) x :=
  let ⟨_, hp⟩ := analyticAt_exp_of_mem_ball x hx
  hp.hasFDerivAt.unique (hasFDerivAt_exp_of_mem_ball hx) ▸ hp.hasStrictFDerivAt

end AnyFieldCommAlgebra

section deriv

variable {𝕂 : Type*} [NontriviallyNormedField 𝕂] [CompleteSpace 𝕂] [CharZero 𝕂]

/--
theorem `hasStrictDerivAt_exp_of_mem_ball` / 定理 `hasStrictDerivAt_exp_of_mem_ball`

English:
theorem hasStrictDerivAt_exp_of_mem_ball
  statement: {x : 𝕂}
  proof: by
  simpa using (hasStrictFDerivAt_exp_of_mem_ball hx).hasStrictDerivAt

中文:
定理 hasStrictDerivAt_exp_of_mem_ball
  结论: {x : 𝕂}
  证明: by
  simpa using (hasStrictFDerivAt_exp_of_mem_ball hx).hasStrictDerivAt

Depends on / 依赖: hasStrictDerivAt, hasStrictFDerivAt_exp_of_mem_ball
-/
theorem hasStrictDerivAt_exp_of_mem_ball {x : 𝕂}
    (hx : x in Metric.eball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) :
    HasStrictDerivAt exp (exp x) x := by
  simpa using (hasStrictFDerivAt_exp_of_mem_ball hx).hasStrictDerivAt

/--
theorem `hasDerivAt_exp_of_mem_ball` / 定理 `hasDerivAt_exp_of_mem_ball`

English:
theorem hasDerivAt_exp_of_mem_ball
  statement: {x : 𝕂}
  proof: (hasStrictDerivAt_exp_of_mem_ball hx).hasDerivAt

中文:
定理 hasDerivAt_exp_of_mem_ball
  结论: {x : 𝕂}
  证明: (hasStrictDerivAt_exp_of_mem_ball hx).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_exp_of_mem_ball
-/
theorem hasDerivAt_exp_of_mem_ball {x : 𝕂}
    (hx : x in Metric.eball (0 : 𝕂) (expSeries 𝕂 𝕂).radius) : HasDerivAt exp (exp x) x :=
  (hasStrictDerivAt_exp_of_mem_ball hx).hasDerivAt

/--
theorem `hasStrictDerivAt_exp_zero_of_radius_pos` / 定理 `hasStrictDerivAt_exp_zero_of_radius_pos`

English:
theorem hasStrictDerivAt_exp_zero_of_radius_pos
  given: (h : 0 < (expSeries 𝕂 𝕂).radius)
  proof: (hasStrictFDerivAt_exp_zero_of_radius_pos h).hasStrictDerivAt

中文:
定理 hasStrictDerivAt_exp_zero_of_radius_pos
  条件: (h : 0 < (expSeries 𝕂 𝕂).radius)
  证明: (hasStrictFDerivAt_exp_zero_of_radius_pos h).hasStrictDerivAt

Depends on / 依赖: hasStrictDerivAt, hasStrictFDerivAt_exp_zero_of_radius_pos
-/
theorem hasStrictDerivAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝕂).radius) :
    HasStrictDerivAt exp (1 : 𝕂) 0 :=
  (hasStrictFDerivAt_exp_zero_of_radius_pos h).hasStrictDerivAt

/--
theorem `hasDerivAt_exp_zero_of_radius_pos` / 定理 `hasDerivAt_exp_zero_of_radius_pos`

English:
theorem hasDerivAt_exp_zero_of_radius_pos
  given: (h : 0 < (expSeries 𝕂 𝕂).radius)
  proof: (hasStrictDerivAt_exp_zero_of_radius_pos h).hasDerivAt

中文:
定理 hasDerivAt_exp_zero_of_radius_pos
  条件: (h : 0 < (expSeries 𝕂 𝕂).radius)
  证明: (hasStrictDerivAt_exp_zero_of_radius_pos h).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_exp_zero_of_radius_pos
-/
theorem hasDerivAt_exp_zero_of_radius_pos (h : 0 < (expSeries 𝕂 𝕂).radius) :
    HasDerivAt exp (1 : 𝕂) 0 :=
  (hasStrictDerivAt_exp_zero_of_radius_pos h).hasDerivAt

end deriv

section RCLikeAnyAlgebra

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/--
theorem `hasStrictFDerivAt_exp_zero` / 定理 `hasStrictFDerivAt_exp_zero`

English:
theorem hasStrictFDerivAt_exp_zero
  statement: HasStrictFDerivAt exp (1 : 𝔸 ->L[𝕂] 𝔸) 0
  proof: hasStrictFDerivAt_exp_zero_of_radius_pos (expSeries_radius_pos 𝕂 𝔸)

中文:
定理 hasStrictFDerivAt_exp_zero
  结论: HasStrictFDerivAt exp (1 : 𝔸 ->L[𝕂] 𝔸) 0
  证明: hasStrictFDerivAt_exp_zero_of_radius_pos (expSeries_radius_pos 𝕂 𝔸)

Depends on / 依赖: expSeries_radius_pos, hasStrictFDerivAt_exp_zero_of_radius_pos
-/
theorem hasStrictFDerivAt_exp_zero : HasStrictFDerivAt exp (1 : 𝔸 ->L[𝕂] 𝔸) 0 :=
  hasStrictFDerivAt_exp_zero_of_radius_pos (expSeries_radius_pos 𝕂 𝔸)

/--
theorem `hasFDerivAt_exp_zero` / 定理 `hasFDerivAt_exp_zero`

English:
theorem hasFDerivAt_exp_zero
  statement: HasFDerivAt exp (1 : 𝔸 ->L[𝕂] 𝔸) 0
  proof: hasStrictFDerivAt_exp_zero.hasFDerivAt

中文:
定理 hasFDerivAt_exp_zero
  结论: 在点处Fréchet可导 exp (1 : 𝔸 ->L[𝕂] 𝔸) 0
  证明: hasStrictFDerivAt_exp_zero.hasFDerivAt

Depends on / 依赖: hasFDerivAt, hasStrictFDerivAt_exp_zero, hasStrictFDerivAt_exp_zero.hasFDerivAt
-/
theorem hasFDerivAt_exp_zero : HasFDerivAt exp (1 : 𝔸 ->L[𝕂] 𝔸) 0 :=
  hasStrictFDerivAt_exp_zero.hasFDerivAt

end RCLikeAnyAlgebra

section RCLikeCommAlgebra

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/--
theorem `hasStrictFDerivAt_exp` / 定理 `hasStrictFDerivAt_exp`

English:
theorem hasStrictFDerivAt_exp
  given: {x : 𝔸}
  statement: HasStrictFDerivAt exp (exp x • (1 : 𝔸 ->L[𝕂] 𝔸)) x
  proof: hasStrictFDerivAt_exp_of_mem_ball ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

中文:
定理 hasStrictFDerivAt_exp
  条件: {x : 𝔸}
  结论: HasStrictFDerivAt exp (exp x • (1 : 𝔸 ->L[𝕂] 𝔸)) x
  证明: hasStrictFDerivAt_exp_of_mem_ball ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, hasStrictFDerivAt_exp_of_mem_ball
-/
theorem hasStrictFDerivAt_exp {x : 𝔸} : HasStrictFDerivAt exp (exp x • (1 : 𝔸 ->L[𝕂] 𝔸)) x :=
  hasStrictFDerivAt_exp_of_mem_ball ((expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _)

/--
theorem `hasFDerivAt_exp` / 定理 `hasFDerivAt_exp`

English:
theorem hasFDerivAt_exp
  given: {x : 𝔸}
  statement: HasFDerivAt exp (exp x • (1 : 𝔸 ->L[𝕂] 𝔸)) x
  proof: hasStrictFDerivAt_exp.hasFDerivAt

中文:
定理 hasFDerivAt_exp
  条件: {x : 𝔸}
  结论: 在点处Fréchet可导 exp (exp x • (1 : 𝔸 ->L[𝕂] 𝔸)) x
  证明: hasStrictFDerivAt_exp.hasFDerivAt

Depends on / 依赖: hasFDerivAt, hasStrictFDerivAt_exp, hasStrictFDerivAt_exp.hasFDerivAt
-/
theorem hasFDerivAt_exp {x : 𝔸} : HasFDerivAt exp (exp x • (1 : 𝔸 ->L[𝕂] 𝔸)) x :=
  hasStrictFDerivAt_exp.hasFDerivAt

end RCLikeCommAlgebra

section DerivRCLike

variable {𝕂 : Type*} [RCLike 𝕂]

/--
theorem `hasStrictDerivAt_exp` / 定理 `hasStrictDerivAt_exp`

English:
theorem hasStrictDerivAt_exp
  given: {x : 𝕂}
  statement: HasStrictDerivAt exp (exp x) x
  proof: hasStrictDerivAt_exp_of_mem_ball ((expSeries_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

中文:
定理 hasStrictDerivAt_exp
  条件: {x : 𝕂}
  结论: HasStrictDerivAt exp (exp x) x
  证明: hasStrictDerivAt_exp_of_mem_ball ((expSeries_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, hasStrictDerivAt_exp_of_mem_ball
-/
theorem hasStrictDerivAt_exp {x : 𝕂} : HasStrictDerivAt exp (exp x) x :=
  hasStrictDerivAt_exp_of_mem_ball ((expSeries_radius_eq_top 𝕂 𝕂).symm ▸ edist_lt_top _ _)

/--
theorem `hasDerivAt_exp` / 定理 `hasDerivAt_exp`

English:
theorem hasDerivAt_exp
  given: {x : 𝕂}
  statement: HasDerivAt exp (exp x) x
  proof: hasStrictDerivAt_exp.hasDerivAt

中文:
定理 hasDerivAt_exp
  条件: {x : 𝕂}
  结论: 在点处可导 exp (exp x) x
  证明: hasStrictDerivAt_exp.hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_exp, hasStrictDerivAt_exp.hasDerivAt
-/
theorem hasDerivAt_exp {x : 𝕂} : HasDerivAt exp (exp x) x :=
  hasStrictDerivAt_exp.hasDerivAt

/--
theorem `hasStrictDerivAt_exp_zero` / 定理 `hasStrictDerivAt_exp_zero`

English:
theorem hasStrictDerivAt_exp_zero
  statement: HasStrictDerivAt exp (1 : 𝕂) 0
  proof: hasStrictDerivAt_exp_zero_of_radius_pos (expSeries_radius_pos 𝕂 𝕂)

中文:
定理 hasStrictDerivAt_exp_zero
  结论: HasStrictDerivAt exp (1 : 𝕂) 0
  证明: hasStrictDerivAt_exp_zero_of_radius_pos (expSeries_radius_pos 𝕂 𝕂)

Depends on / 依赖: expSeries_radius_pos, hasStrictDerivAt_exp_zero_of_radius_pos
-/
theorem hasStrictDerivAt_exp_zero : HasStrictDerivAt exp (1 : 𝕂) 0 :=
  hasStrictDerivAt_exp_zero_of_radius_pos (expSeries_radius_pos 𝕂 𝕂)

/--
theorem `hasDerivAt_exp_zero` / 定理 `hasDerivAt_exp_zero`

English:
theorem hasDerivAt_exp_zero
  statement: HasDerivAt exp (1 : 𝕂) 0
  proof: hasStrictDerivAt_exp_zero.hasDerivAt

中文:
定理 hasDerivAt_exp_zero
  结论: 在点处可导 exp (1 : 𝕂) 0
  证明: hasStrictDerivAt_exp_zero.hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_exp_zero, hasStrictDerivAt_exp_zero.hasDerivAt
-/
theorem hasDerivAt_exp_zero : HasDerivAt exp (1 : 𝕂) 0 :=
  hasStrictDerivAt_exp_zero.hasDerivAt

end DerivRCLike

/--
theorem `Complex.exp_eq_exp_Complex` / 定理 `Complex.exp_eq_exp_Complex`

English:
theorem Complex.exp_eq_exp_Complex
  statement: Complex.exp = NormedSpace.exp
  proof: by
  refine funext fun x => ?_
  rw [Complex.exp]; rw [exp_eq_tsum_div]
  exact tendsto_nhds_unique x.exp'.tendsto_limit (expSeries_div_summable x).hasSum.tendsto_sum_nat

中文:
定理 复形.exp_eq_exp_Complex
  结论: 复形.exp = 赋范空间.exp
  证明: by
  refine funext fun x => ?_
  rw [Complex.exp]; rw [exp_eq_tsum_div]
  exact tendsto_nhds_unique x.exp'.tendsto_limit (expSeries_div_summable x).hasSum.tendsto_sum_nat

Depends on / 依赖: Complex.exp, expSeries_div_summable, exp_eq_tsum_div, hasSum, hasSum.tendsto_sum_nat, tendsto_limit, tendsto_nhds_unique, tendsto_sum_nat, x.exp
-/
theorem Complex.exp_eq_exp_Complex : Complex.exp = NormedSpace.exp := by
  refine funext fun x => ?_
  rw [Complex.exp]; rw [exp_eq_tsum_div]
  exact tendsto_nhds_unique x.exp'.tendsto_limit (expSeries_div_summable x).hasSum.tendsto_sum_nat

/--
theorem `Real.exp_eq_exp_Real` / 定理 `Real.exp_eq_exp_Real`

English:
theorem Real.exp_eq_exp_Real
  statement: Real.exp = NormedSpace.exp
  proof: by
  ext x; exact mod_cast congr_fun Complex.exp_eq_exp_Complex x

中文:
定理 实数.exp_eq_exp_实数
  结论: 实数.exp = 赋范空间.exp
  证明: by
  ext x; exact mod_cast congr_fun Complex.exp_eq_exp_Complex x

Depends on / 依赖: Complex.exp_eq_exp_Complex, congr_fun, exp_eq_exp_Complex, mod_cast
-/
theorem Real.exp_eq_exp_Real : Real.exp = NormedSpace.exp := by
  ext x; exact mod_cast congr_fun Complex.exp_eq_exp_Complex x

/-! ### Derivative of $\exp (ux)$ by $u$

Note that since for `x : 𝔸` we have `NormedRing 𝔸` not `NormedCommRing 𝔸`, we cannot deduce
these results from `hasFDerivAt_exp_of_mem_ball` applied to the algebra `𝔸`.

One possible solution for that would be to apply `hasFDerivAt_exp_of_mem_ball` to the
commutative algebra `Algebra.elementalAlgebra 𝕊 x`. Unfortunately we don't have all the required
API, so we leave that to a future refactor (see https://github.com/leanprover-community/mathlib3/pull/19062 for discussion).

We could also go the other way around and deduce `hasFDerivAt_exp_of_mem_ball` from
`hasFDerivAt_exp_smul_const_of_mem_ball` applied to `𝕊 := 𝔸`, `x := (1 : 𝔸)`, and `t := x`.
However, doing so would make the aforementioned `elementalAlgebra` refactor harder, so for now we
just prove these two lemmas independently.

A last strategy would be to deduce everything from the more general non-commutative case,
$$\frac{d}{dt}e^{x(t)} = \int_0^1 e^{sx(t)} \left(\frac{d}{dt}e^{x(t)}\right) e^{(1-s)x(t)} ds$$
but this is harder to prove, and typically is shown by going via these results first.

TODO: prove this result too!
-/


section exp_smul

variable {𝕂 𝕊 𝔸 : Type*}
variable (𝕂)

open scoped Topology

open Asymptotics Filter

section MemBall

variable [NontriviallyNormedField 𝕂] [CharZero 𝕂]
variable [NormedCommRing 𝕊] [NormedRing 𝔸]
variable [NormedSpace 𝕂 𝕊] [NormedAlgebra 𝕂 𝔸] [Algebra 𝕊 𝔸] [ContinuousSMul 𝕊 𝔸]
variable [IsScalarTower 𝕂 𝕊 𝔸]
variable [CompleteSpace 𝔸]

/--
theorem `hasFDerivAt_exp_smul_const_of_mem_ball` / 定理 `hasFDerivAt_exp_smul_const_of_mem_ball`

English:
theorem hasFDerivAt_exp_smul_const_of_mem_ball
  statement: (x : 𝔸) (t : 𝕊)
  proof: by
  -- TODO: prove this via `hasFDerivAt_exp_of_mem_ball` using the commutative ring
  -- `Algebra.elementalAlgebra 𝕊 x`. See https://github.com/leanprover-community/mathlib3/pull/19062 for discussion.
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  suffices (fun (h : 𝕊) => exp (t • x) *
      (exp ((

中文:
定理 hasFDerivAt_exp_smul_const_of_mem_ball
  结论: (x : 𝔸) (t : 𝕊)
  证明: by
  -- TODO: prove this via `hasFDerivAt_exp_of_mem_ball` using the commutative ring
  -- `Algebra.elementalAlgebra 𝕊 x`. See https://github.com/leanprover-community/mathlib3/pull/19062 for discussion.
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  suffices (fun (h : 𝕊) => exp (t • x) *
      (exp ((
-/
theorem hasFDerivAt_exp_smul_const_of_mem_ball (x : 𝔸) (t : 𝕊)
    (htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasFDerivAt (fun u : 𝕊 => exp (u • x)) (exp (t • x) • (1 : 𝕊 ->L[𝕂] 𝕊).smulRight x) t := by
  -- TODO: prove this via `hasFDerivAt_exp_of_mem_ball` using the commutative ring
  -- `Algebra.elementalAlgebra 𝕊 x`. See https://github.com/leanprover-community/mathlib3/pull/19062 for discussion.
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  suffices (fun (h : 𝕊) => exp (t • x) *
      (exp ((0 + h) • x) - exp ((0 : 𝕊) • x) - ((1 : 𝕊 ->L[𝕂] 𝕊).smulRight x) h)) =ᶠ[𝓝 0]
        fun h =>
          exp ((t + h) • x) - exp (t • x) - (exp (t • x) • (1 : 𝕊 ->L[𝕂] 𝕊).smulRight x) h by
    apply (IsLittleO.const_mul_left _ _).congr' this (EventuallyEq.refl _ _)
    rw [← hasFDerivAt_iff_isLittleO_nhds_zero (f := fun u => exp (u • x))
      (f' := (1 : 𝕊 ->L[𝕂] 𝕊).smulRight x) (x := 0)]
    have : HasFDerivAt exp (1 : 𝔸 ->L[𝕂] 𝔸) ((1 : 𝕊 ->L[𝕂] 𝕊).smulRight x 0) := by
      rw [ContinuousLinearMap.smulRight_apply]; rw [one_apply_eq_self]; rw [zero_smul]
      exact hasFDerivAt_exp_zero_of_radius_pos htx.pos
    exact this.comp 0 ((1 : 𝕊 ->L[𝕂] 𝕊).smulRight x).hasFDerivAt
  have : Tendsto (fun h : 𝕊 => h • x) (𝓝 0) (𝓝 0) := by
    rw [← zero_smul 𝕊 x]
    exact tendsto_id.smul_const x
  have : forallᶠ h in 𝓝 (0 : 𝕊), h • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius :=
    this.eventually (Metric.eball_mem_nhds _ htx.pos)
  filter_upwards [this] with h hh
  have : Commute (t • x) (h • x) := ((Commute.refl x).smul_left t).smul_right h
  rw [add_smul t h]; rw [exp_add_of_commute_of_mem_ball this htx hh]; rw [zero_add]; rw [zero_smul]; rw [exp_zero]; rw [ContinuousLinearMap.smulRight_apply]; rw [one_apply_eq_self]; rw [smul_apply]; rw [ContinuousLinearMap.smulRight_apply]; rw [one_apply_eq_self]; rw [smul_eq_mul]; rw [mul_sub_left_distrib]; rw [mul_sub_left_distrib]; rw [mul_one]

/--
theorem `hasFDerivAt_exp_smul_const_of_mem_ball'` / 定理 `hasFDerivAt_exp_smul_const_of_mem_ball'`

English:
theorem hasFDerivAt_exp_smul_const_of_mem_ball'
  statement: (x : 𝔸) (t : 𝕊)
  proof: by
  convert! hasFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _ htx using 1
  ext t'
  change Commute (t' • x) (exp (t • x))
  exact (((Commute.refl x).smul_left t').smul_right t).exp_right

中文:
定理 hasFDerivAt_exp_smul_const_of_mem_ball'
  结论: (x : 𝔸) (t : 𝕊)
  证明: by
  convert! hasFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _ htx using 1
  ext t'
  change Commute (t' • x) (exp (t • x))
  exact (((Commute.refl x).smul_left t').smul_right t).exp_right

Depends on / 依赖: Commute, Commute.refl, convert, exp_right, hasFDerivAt_exp_smul_const_of_mem_ball, smul_left, smul_right
-/
theorem hasFDerivAt_exp_smul_const_of_mem_ball' (x : 𝔸) (t : 𝕊)
    (htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasFDerivAt (fun u : 𝕊 => exp (u • x))
      (((1 : 𝕊 ->L[𝕂] 𝕊).smulRight x).smulRight (exp (t • x))) t := by
  convert! hasFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _ htx using 1
  ext t'
  change Commute (t' • x) (exp (t • x))
  exact (((Commute.refl x).smul_left t').smul_right t).exp_right

/--
theorem `hasStrictFDerivAt_exp_smul_const_of_mem_ball` / 定理 `hasStrictFDerivAt_exp_smul_const_of_mem_ball`

English:
theorem hasStrictFDerivAt_exp_smul_const_of_mem_ball
  statement: (x : 𝔸) (t : 𝕊)
  proof: let ⟨_, hp⟩ := analyticAt_exp_of_mem_ball (t • x) htx
  have deriv₁ : HasStrictFDerivAt (fun u : 𝕊 => exp (u • x)) _ t :=
    hp.hasStrictFDerivAt.comp t ((ContinuousLinearMap.id 𝕂 𝕊).smulRight x).hasStrictFDerivAt
  have deriv₂ : HasFDerivAt (fun u : 𝕊 => exp (u • x)) _ t :=
    hasFDerivAt_exp_smu

中文:
定理 hasStrictFDerivAt_exp_smul_const_of_mem_ball
  结论: (x : 𝔸) (t : 𝕊)
  证明: let ⟨_, hp⟩ := analyticAt_exp_of_mem_ball (t • x) htx
  have deriv₁ : HasStrictFDerivAt (fun u : 𝕊 => exp (u • x)) _ t :=
    hp.hasStrictFDerivAt.comp t ((ContinuousLinearMap.id 𝕂 𝕊).smulRight x).hasStrictFDerivAt
  have deriv₂ : HasFDerivAt (fun u : 𝕊 => exp (u • x)) _ t :=
    hasFDerivAt_exp_smu

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, HasFDerivAt, HasStrictFDerivAt, analyticAt_exp_of_mem_ball, hasFDerivAt, hasFDerivAt.unique, hasFDerivAt_exp_smul_const_of_mem_ball, hasStrictFDerivAt, hp.hasStrictFDerivAt.comp, smulRight, unique
-/
theorem hasStrictFDerivAt_exp_smul_const_of_mem_ball (x : 𝔸) (t : 𝕊)
    (htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictFDerivAt (fun u : 𝕊 => exp (u • x))
      (exp (t • x) • (1 : 𝕊 ->L[𝕂] 𝕊).smulRight x) t :=
  let ⟨_, hp⟩ := analyticAt_exp_of_mem_ball (t • x) htx
  have deriv₁ : HasStrictFDerivAt (fun u : 𝕊 => exp (u • x)) _ t :=
    hp.hasStrictFDerivAt.comp t ((ContinuousLinearMap.id 𝕂 𝕊).smulRight x).hasStrictFDerivAt
  have deriv₂ : HasFDerivAt (fun u : 𝕊 => exp (u • x)) _ t :=
    hasFDerivAt_exp_smul_const_of_mem_ball 𝕂 x t htx
  deriv₁.hasFDerivAt.unique deriv₂ ▸ deriv₁

/--
theorem `hasStrictFDerivAt_exp_smul_const_of_mem_ball'` / 定理 `hasStrictFDerivAt_exp_smul_const_of_mem_ball'`

English:
theorem hasStrictFDerivAt_exp_smul_const_of_mem_ball'
  statement: (x : 𝔸) (t : 𝕊)
  proof: by
  let ⟨_, _⟩ := analyticAt_exp_of_mem_ball (t • x) htx
  convert! hasStrictFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _ htx using 1
  ext t'
  change Commute (t' • x) (exp (t • x))
  exact (((Commute.refl x).smul_left t').smul_right t).exp_right

中文:
定理 hasStrictFDerivAt_exp_smul_const_of_mem_ball'
  结论: (x : 𝔸) (t : 𝕊)
  证明: by
  let ⟨_, _⟩ := analyticAt_exp_of_mem_ball (t • x) htx
  convert! hasStrictFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _ htx using 1
  ext t'
  change Commute (t' • x) (exp (t • x))
  exact (((Commute.refl x).smul_left t').smul_right t).exp_right

Depends on / 依赖: Adhesive, Adhesive.toRegularMonoCategory, Commute, Commute.refl, analyticAt_exp_of_mem_ball, convert, exp_right, hasStrictFDerivAt_exp_smul_const_of_mem_ball, smul_left, smul_right, toRegularMonoCategory
-/
theorem hasStrictFDerivAt_exp_smul_const_of_mem_ball' (x : 𝔸) (t : 𝕊)
    (htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictFDerivAt (fun u : 𝕊 => exp (u • x))
      (((1 : 𝕊 ->L[𝕂] 𝕊).smulRight x).smulRight (exp (t • x))) t := by
  let ⟨_, _⟩ := analyticAt_exp_of_mem_ball (t • x) htx
  convert! hasStrictFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _ htx using 1
  ext t'
  change Commute (t' • x) (exp (t • x))
  exact (((Commute.refl x).smul_left t').smul_right t).exp_right

variable {𝕂}

/--
theorem `hasStrictDerivAt_exp_smul_const_of_mem_ball` / 定理 `hasStrictDerivAt_exp_smul_const_of_mem_ball`

English:
theorem hasStrictDerivAt_exp_smul_const_of_mem_ball
  statement: (x : 𝔸) (t : 𝕂)
  proof: by
  simpa using (hasStrictFDerivAt_exp_smul_const_of_mem_ball 𝕂 x t htx).hasStrictDerivAt

中文:
定理 hasStrictDerivAt_exp_smul_const_of_mem_ball
  结论: (x : 𝔸) (t : 𝕂)
  证明: by
  simpa using (hasStrictFDerivAt_exp_smul_const_of_mem_ball 𝕂 x t htx).hasStrictDerivAt

Depends on / 依赖: hasStrictDerivAt, hasStrictFDerivAt_exp_smul_const_of_mem_ball
-/
theorem hasStrictDerivAt_exp_smul_const_of_mem_ball (x : 𝔸) (t : 𝕂)
    (htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictDerivAt (fun u : 𝕂 => exp (u • x)) (exp (t • x) * x) t := by
  simpa using (hasStrictFDerivAt_exp_smul_const_of_mem_ball 𝕂 x t htx).hasStrictDerivAt

/--
theorem `hasStrictDerivAt_exp_smul_const_of_mem_ball'` / 定理 `hasStrictDerivAt_exp_smul_const_of_mem_ball'`

English:
theorem hasStrictDerivAt_exp_smul_const_of_mem_ball'
  statement: (x : 𝔸) (t : 𝕂)
  proof: by
  simpa using (hasStrictFDerivAt_exp_smul_const_of_mem_ball' 𝕂 x t htx).hasStrictDerivAt

中文:
定理 hasStrictDerivAt_exp_smul_const_of_mem_ball'
  结论: (x : 𝔸) (t : 𝕂)
  证明: by
  simpa using (hasStrictFDerivAt_exp_smul_const_of_mem_ball' 𝕂 x t htx).hasStrictDerivAt

Depends on / 依赖: hasStrictDerivAt, hasStrictFDerivAt_exp_smul_const_of_mem_ball
-/
theorem hasStrictDerivAt_exp_smul_const_of_mem_ball' (x : 𝔸) (t : 𝕂)
    (htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasStrictDerivAt (fun u : 𝕂 => exp (u • x)) (x * exp (t • x)) t := by
  simpa using (hasStrictFDerivAt_exp_smul_const_of_mem_ball' 𝕂 x t htx).hasStrictDerivAt

/--
theorem `hasDerivAt_exp_smul_const_of_mem_ball` / 定理 `hasDerivAt_exp_smul_const_of_mem_ball`

English:
theorem hasDerivAt_exp_smul_const_of_mem_ball
  statement: (x : 𝔸) (t : 𝕂)
  proof: (hasStrictDerivAt_exp_smul_const_of_mem_ball x t htx).hasDerivAt

中文:
定理 hasDerivAt_exp_smul_const_of_mem_ball
  结论: (x : 𝔸) (t : 𝕂)
  证明: (hasStrictDerivAt_exp_smul_const_of_mem_ball x t htx).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_exp_smul_const_of_mem_ball
-/
theorem hasDerivAt_exp_smul_const_of_mem_ball (x : 𝔸) (t : 𝕂)
    (htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasDerivAt (fun u : 𝕂 => exp (u • x)) (exp (t • x) * x) t :=
  (hasStrictDerivAt_exp_smul_const_of_mem_ball x t htx).hasDerivAt

/--
theorem `hasDerivAt_exp_smul_const_of_mem_ball'` / 定理 `hasDerivAt_exp_smul_const_of_mem_ball'`

English:
theorem hasDerivAt_exp_smul_const_of_mem_ball'
  statement: (x : 𝔸) (t : 𝕂)
  proof: (hasStrictDerivAt_exp_smul_const_of_mem_ball' x t htx).hasDerivAt

中文:
定理 hasDerivAt_exp_smul_const_of_mem_ball'
  结论: (x : 𝔸) (t : 𝕂)
  证明: (hasStrictDerivAt_exp_smul_const_of_mem_ball' x t htx).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_exp_smul_const_of_mem_ball
-/
theorem hasDerivAt_exp_smul_const_of_mem_ball' (x : 𝔸) (t : 𝕂)
    (htx : t • x in Metric.eball (0 : 𝔸) (expSeries 𝕂 𝔸).radius) :
    HasDerivAt (fun u : 𝕂 => exp (u • x)) (x * exp (t • x)) t :=
  (hasStrictDerivAt_exp_smul_const_of_mem_ball' x t htx).hasDerivAt

end MemBall

section RCLike

variable [RCLike 𝕂]
variable [NormedCommRing 𝕊] [NormedRing 𝔸]
variable [NormedAlgebra 𝕂 𝕊] [NormedAlgebra 𝕂 𝔸] [Algebra 𝕊 𝔸] [ContinuousSMul 𝕊 𝔸]
variable [IsScalarTower 𝕂 𝕊 𝔸]
variable [CompleteSpace 𝔸]

/--
theorem `hasFDerivAt_exp_smul_const` / 定理 `hasFDerivAt_exp_smul_const`

English:
theorem hasFDerivAt_exp_smul_const
  given: (x : 𝔸) (t : 𝕊)
  proof: hasFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

中文:
定理 hasFDerivAt_exp_smul_const
  条件: (x : 𝔸) (t : 𝕊)
  证明: hasFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, hasFDerivAt_exp_smul_const_of_mem_ball
-/
theorem hasFDerivAt_exp_smul_const (x : 𝔸) (t : 𝕊) :
    HasFDerivAt (fun u : 𝕊 => exp (u • x)) (exp (t • x) • (1 : 𝕊 ->L[𝕂] 𝕊).smulRight x) t :=
hasFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

/--
theorem `hasFDerivAt_exp_smul_const'` / 定理 `hasFDerivAt_exp_smul_const'`

English:
theorem hasFDerivAt_exp_smul_const'
  given: (x : 𝔸) (t : 𝕊)
  proof: hasFDerivAt_exp_smul_const_of_mem_ball' 𝕂 _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

中文:
定理 hasFDerivAt_exp_smul_const'
  条件: (x : 𝔸) (t : 𝕊)
  证明: hasFDerivAt_exp_smul_const_of_mem_ball' 𝕂 _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, hasFDerivAt_exp_smul_const_of_mem_ball
-/
theorem hasFDerivAt_exp_smul_const' (x : 𝔸) (t : 𝕊) :
    HasFDerivAt (fun u : 𝕊 => exp (u • x))
      (((1 : 𝕊 ->L[𝕂] 𝕊).smulRight x).smulRight (exp (t • x))) t :=
hasFDerivAt_exp_smul_const_of_mem_ball' 𝕂 _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

/--
theorem `hasStrictFDerivAt_exp_smul_const` / 定理 `hasStrictFDerivAt_exp_smul_const`

English:
theorem hasStrictFDerivAt_exp_smul_const
  given: (x : 𝔸) (t : 𝕊)
  proof: hasStrictFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

中文:
定理 hasStrictFDerivAt_exp_smul_const
  条件: (x : 𝔸) (t : 𝕊)
  证明: hasStrictFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, hasStrictFDerivAt_exp_smul_const_of_mem_ball
-/
theorem hasStrictFDerivAt_exp_smul_const (x : 𝔸) (t : 𝕊) :
    HasStrictFDerivAt (fun u : 𝕊 => exp (u • x))
      (exp (t • x) • (1 : 𝕊 ->L[𝕂] 𝕊).smulRight x) t :=
hasStrictFDerivAt_exp_smul_const_of_mem_ball 𝕂 _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

/--
theorem `hasStrictFDerivAt_exp_smul_const'` / 定理 `hasStrictFDerivAt_exp_smul_const'`

English:
theorem hasStrictFDerivAt_exp_smul_const'
  given: (x : 𝔸) (t : 𝕊)
  proof: hasStrictFDerivAt_exp_smul_const_of_mem_ball' 𝕂 _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

中文:
定理 hasStrictFDerivAt_exp_smul_const'
  条件: (x : 𝔸) (t : 𝕊)
  证明: hasStrictFDerivAt_exp_smul_const_of_mem_ball' 𝕂 _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, hasStrictFDerivAt_exp_smul_const_of_mem_ball
-/
theorem hasStrictFDerivAt_exp_smul_const' (x : 𝔸) (t : 𝕊) :
    HasStrictFDerivAt (fun u : 𝕊 => exp (u • x))
      (((1 : 𝕊 ->L[𝕂] 𝕊).smulRight x).smulRight (exp (t • x))) t :=
hasStrictFDerivAt_exp_smul_const_of_mem_ball' 𝕂 _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

variable {𝕂}

/--
theorem `hasStrictDerivAt_exp_smul_const` / 定理 `hasStrictDerivAt_exp_smul_const`

English:
theorem hasStrictDerivAt_exp_smul_const
  given: (x : 𝔸) (t : 𝕂)
  proof: hasStrictDerivAt_exp_smul_const_of_mem_ball _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

中文:
定理 hasStrictDerivAt_exp_smul_const
  条件: (x : 𝔸) (t : 𝕂)
  证明: hasStrictDerivAt_exp_smul_const_of_mem_ball _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, hasStrictDerivAt_exp_smul_const_of_mem_ball
-/
theorem hasStrictDerivAt_exp_smul_const (x : 𝔸) (t : 𝕂) :
    HasStrictDerivAt (fun u : 𝕂 => exp (u • x)) (exp (t • x) * x) t :=
hasStrictDerivAt_exp_smul_const_of_mem_ball _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

/--
theorem `hasStrictDerivAt_exp_smul_const'` / 定理 `hasStrictDerivAt_exp_smul_const'`

English:
theorem hasStrictDerivAt_exp_smul_const'
  given: (x : 𝔸) (t : 𝕂)
  proof: hasStrictDerivAt_exp_smul_const_of_mem_ball' _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

中文:
定理 hasStrictDerivAt_exp_smul_const'
  条件: (x : 𝔸) (t : 𝕂)
  证明: hasStrictDerivAt_exp_smul_const_of_mem_ball' _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, hasStrictDerivAt_exp_smul_const_of_mem_ball
-/
theorem hasStrictDerivAt_exp_smul_const' (x : 𝔸) (t : 𝕂) :
    HasStrictDerivAt (fun u : 𝕂 => exp (u • x)) (x * exp (t • x)) t :=
hasStrictDerivAt_exp_smul_const_of_mem_ball' _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

/--
theorem `hasDerivAt_exp_smul_const` / 定理 `hasDerivAt_exp_smul_const`

English:
theorem hasDerivAt_exp_smul_const
  given: (x : 𝔸) (t : 𝕂)
  proof: hasDerivAt_exp_smul_const_of_mem_ball _ _ (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

中文:
定理 hasDerivAt_exp_smul_const
  条件: (x : 𝔸) (t : 𝕂)
  证明: hasDerivAt_exp_smul_const_of_mem_ball _ _ (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, hasDerivAt_exp_smul_const_of_mem_ball
-/
theorem hasDerivAt_exp_smul_const (x : 𝔸) (t : 𝕂) :
    HasDerivAt (fun u : 𝕂 => exp (u • x)) (exp (t • x) * x) t :=
hasDerivAt_exp_smul_const_of_mem_ball _ _ (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

/--
theorem `hasDerivAt_exp_smul_const'` / 定理 `hasDerivAt_exp_smul_const'`

English:
theorem hasDerivAt_exp_smul_const'
  given: (x : 𝔸) (t : 𝕂)
  proof: hasDerivAt_exp_smul_const_of_mem_ball' _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

中文:
定理 hasDerivAt_exp_smul_const'
  条件: (x : 𝔸) (t : 𝕂)
  证明: hasDerivAt_exp_smul_const_of_mem_ball' _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

Depends on / 依赖: edist_lt_top, expSeries_radius_eq_top, hasDerivAt_exp_smul_const_of_mem_ball
-/
theorem hasDerivAt_exp_smul_const' (x : 𝔸) (t : 𝕂) :
    HasDerivAt (fun u : 𝕂 => exp (u • x)) (x * exp (t • x)) t :=
hasDerivAt_exp_smul_const_of_mem_ball' _ _
    (expSeries_radius_eq_top 𝕂 𝔸).symm ▸ edist_lt_top _ _

variable (𝕂) in
@[fun_prop]
/--
lemma `differentiable_exp_smul_const` / 引理 `differentiable_exp_smul_const`

English:
lemma differentiable_exp_smul_const
  given: (x : 𝔸)
  proof: (⟨_, hasDerivAt_exp_smul_const x ·⟩)

@[fun_prop]

中文:
引理 differentiable_exp_smul_const
  条件: (x : 𝔸)
  证明: (⟨_, hasDerivAt_exp_smul_const x ·⟩)

@[fun_prop]

Depends on / 依赖: hasDerivAt_exp_smul_const
-/
lemma differentiable_exp_smul_const (x : 𝔸) :
    Differentiable 𝕂 (fun t : 𝕂 => exp (t • x)) :=
  (⟨_, hasDerivAt_exp_smul_const x ·⟩)

@[fun_prop]
/--
lemma `differentiableAt_exp_smul_const` / 引理 `differentiableAt_exp_smul_const`

English:
lemma differentiableAt_exp_smul_const
  given: (x : 𝔸) (r : 𝕂)
  proof: .differentiableAt differentiable_exp_smul_const 𝕂 x

中文:
引理 differentiableAt_exp_smul_const
  条件: (x : 𝔸) (r : 𝕂)
  证明: .differentiableAt differentiable_exp_smul_const 𝕂 x

Depends on / 依赖: differentiableAt, differentiable_exp_smul_const
-/
lemma differentiableAt_exp_smul_const (x : 𝔸) (r : 𝕂) :
    DifferentiableAt 𝕂 (fun t : 𝕂 => exp (t • x)) r :=
.differentiableAt differentiable_exp_smul_const 𝕂 x

end RCLike

end exp_smul

section tsum_tprod

variable {𝔸 : Type*} [NormedCommRing 𝔸] [NormedAlgebra Rat 𝔸] [CompleteSpace 𝔸]

/--
lemma `HasSum.exp` / 引理 `HasSum.exp`

English:
lemma HasSum.exp
  given: {ι : Type*} {f : ι -> 𝔸} {a : 𝔸} (h : HasSum f a)
  proof: Tendsto.congr (fun s => exp_sum s f) Tendsto.exp h

中文:
引理 HasSum.exp
  条件: {ι : 类型} {f : ι -> 𝔸} {a : 𝔸} (h : HasSum f a)
  证明: Tendsto.congr (fun s => exp_sum s f) Tendsto.exp h

Depends on / 依赖: Tendsto, Tendsto.congr, Tendsto.exp, exp_sum
-/
lemma HasSum.exp {ι : Type*} {f : ι -> 𝔸} {a : 𝔸} (h : HasSum f a) :
    HasProd (exp ∘ f) (exp a) :=
Tendsto.congr (fun s => exp_sum s f) Tendsto.exp h

end tsum_tprod
