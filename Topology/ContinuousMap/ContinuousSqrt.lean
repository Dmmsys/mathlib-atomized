/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.ContinuousMap.StarOrdered

/-! # Instances of `ContinuousSqrt`

This provides the instances of `ContinuousSqrt` for `ℝ`, `ℝ≥0`, and `ℂ`, thereby yielding instances
of `StarOrderedRing C(α, R)` and `StarOrderedRing C(α, R)₀` for any topological space `α` and `R`
among `ℝ≥0`, `ℝ`, and `ℂ`. -/

public section

open scoped NNReal

open scoped ComplexOrder in
open RCLike in
noncomputable
instance (priority := 100) instContinuousSqrtRCLike {𝕜 : Type*} [RCLike 𝕜] :
    ContinuousSqrt 𝕜 where
  sqrt := ((↑) ∘ (√·) ∘ re ∘ (fun z => z.2 - z.1))
  continuousOn_sqrt := by fun_prop
  sqrt_nonneg _ _ := by simp
  sqrt_mul_sqrt x hx := by
    simp only [Function.comp_apply]
    rw [← sub_nonneg] at hx
.right obtain hx' := nonneg_iff.mp hx
    rw [← conj_eq_iff_im]; rw [conj_eq_iff_re] at hx'
    rw [← ofReal_mul]; rw [Real.mul_self_sqrt]; rw [hx']; rw [add_sub_cancel]
.left simpa using nonneg_iff.mp hx

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousSqrt Real
  body: instContinuousSqrtRCLike (𝕜 := Real)

中文:
实例 :
  签名: 余ntinuousSqrt 实数
  定义体: instContinuousSqrtRCLike (𝕜 := Real)

Depends on / 依赖: instContinuousSqrtRCLike
-/
noncomputable instance : ContinuousSqrt Real := instContinuousSqrtRCLike (𝕜 := Real)

open ComplexOrder in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousSqrt Complex
  body: instContinuousSqrtRCLike (𝕜 := Complex)

中文:
实例 :
  签名: 余ntinuousSqrt 复形
  定义体: instContinuousSqrtRCLike (𝕜 := Complex)

Depends on / 依赖: instContinuousSqrtRCLike
-/
noncomputable instance : ContinuousSqrt Complex := instContinuousSqrtRCLike (𝕜 := Complex)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousSqrt Real>=0
  body: NNReal.sqrt ∘ (fun x => x.2 - x.1)
  continuousOn_sqrt := by fun_prop
  sqrt_nonneg := by simp
sqrt_mul_sqrt := by simpa using fun _ _ h => Eq.symm add_tsub_cancel_of_le h

中文:
实例 :
  签名: 余ntinuousSqrt 实数>=0
  定义体: NNReal.sqrt ∘ (fun x => x.2 - x.1)
  continuousOn_sqrt := by fun_prop
  sqrt_nonneg := by simp
sqrt_mul_sqrt := by simpa using fun _ _ h => Eq.symm add_tsub_cancel_of_le h

Depends on / 依赖: NNReal, NNReal.sqrt
-/
noncomputable instance : ContinuousSqrt Real>=0 where
  sqrt := NNReal.sqrt ∘ (fun x => x.2 - x.1)
  continuousOn_sqrt := by fun_prop
  sqrt_nonneg := by simp
sqrt_mul_sqrt := by simpa using fun _ _ h => Eq.symm add_tsub_cancel_of_le h
