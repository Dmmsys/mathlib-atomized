/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Derivatives of `Complex.sqrt`

This file proves that `Complex.sqrt` is differentiable on the slit plane
`Complex.slitPlane` and computes its derivative.

## Main results

* `Complex.hasDerivAt_sqrt`: the derivative of `Complex.sqrt` at `z ∈ slitPlane`
  is `z ^ (-1 / 2 : ℂ) / 2`.
* `Complex.differentiableOn_sqrt`: `Complex.sqrt` is differentiable on `slitPlane`.
* `Complex.deriv_sqrt`: the derivative equals `z ^ (-1 / 2 : ℂ) / 2`.
-/

public section

namespace Complex

/--
lemma `hasStrictDerivAt_sqrt` / 引理 `hasStrictDerivAt_sqrt`

English:
lemma hasStrictDerivAt_sqrt
  given: {z : Complex} (hz : z in slitPlane)
  proof: by
  exact (Complex.hasStrictDerivAt_cpow_const (c := 2⁻¹) hz).congr_deriv (by
    rw [show (2 : Complex)⁻¹ - 1 = -1 / 2 by norm_num]; rw [mul_comm]; rw [← div_eq_mul_inv])

中文:
引理 hasStrictDerivAt_sqrt
  条件: {z : 复形} (hz : z in slitPlane)
  证明: by
  exact (Complex.hasStrictDerivAt_cpow_const (c := 2⁻¹) hz).congr_deriv (by
    rw [show (2 : Complex)⁻¹ - 1 = -1 / 2 by norm_num]; rw [mul_comm]; rw [← div_eq_mul_inv])

Depends on / 依赖: Complex.hasStrictDerivAt_cpow_const, congr_deriv, div_eq_mul_inv, hasStrictDerivAt_cpow_const, mul_comm
-/
lemma hasStrictDerivAt_sqrt {z : Complex} (hz : z in slitPlane) :
    HasStrictDerivAt sqrt (z ^ (-1 / 2 : Complex) / 2) z := by
  exact (Complex.hasStrictDerivAt_cpow_const (c := 2⁻¹) hz).congr_deriv (by
    rw [show (2 : Complex)⁻¹ - 1 = -1 / 2 by norm_num]; rw [mul_comm]; rw [← div_eq_mul_inv])

/--
lemma `hasDerivAt_sqrt` / 引理 `hasDerivAt_sqrt`

English:
lemma hasDerivAt_sqrt
  given: {z : Complex} (hz : z in slitPlane)
  statement: HasDerivAt sqrt (z ^ (-1 / 2 : Complex) / 2) z
  proof: (hasStrictDerivAt_sqrt hz).hasDerivAt

中文:
引理 hasDerivAt_sqrt
  条件: {z : 复形} (hz : z in slitPlane)
  结论: 在点处可导 sqrt (z ^ (-1 / 2 : 复形) / 2) z
  证明: (hasStrictDerivAt_sqrt hz).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_sqrt
-/
lemma hasDerivAt_sqrt {z : Complex} (hz : z in slitPlane) : HasDerivAt sqrt (z ^ (-1 / 2 : Complex) / 2) z :=
  (hasStrictDerivAt_sqrt hz).hasDerivAt

/--
lemma `hasDerivWithinAt_sqrt` / 引理 `hasDerivWithinAt_sqrt`

English:
lemma hasDerivWithinAt_sqrt
  given: {z : Complex} {s : Set Complex} (hz : z in slitPlane)
  proof: (hasDerivAt_sqrt hz).hasDerivWithinAt

@[fun_prop]

中文:
引理 hasDerivWithinAt_sqrt
  条件: {z : 复形} {s : 集合 复形} (hz : z in slitPlane)
  证明: (hasDerivAt_sqrt hz).hasDerivWithinAt

@[fun_prop]

Depends on / 依赖: hasDerivAt_sqrt, hasDerivWithinAt
-/
lemma hasDerivWithinAt_sqrt {z : Complex} {s : Set Complex} (hz : z in slitPlane) :
    HasDerivWithinAt sqrt (z ^ (-1 / 2 : Complex) / 2) s z :=
  (hasDerivAt_sqrt hz).hasDerivWithinAt

@[fun_prop]
/--
lemma `differentiableAt_sqrt` / 引理 `differentiableAt_sqrt`

English:
lemma differentiableAt_sqrt
  given: {z : Complex} (hz : z in slitPlane)
  statement: DifferentiableAt Complex sqrt z
  proof: (hasDerivAt_sqrt hz).differentiableAt

@[fun_prop]

中文:
引理 differentiableAt_sqrt
  条件: {z : 复形} (hz : z in slitPlane)
  结论: DifferentiableAt 复形 sqrt z
  证明: (hasDerivAt_sqrt hz).differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, hasDerivAt_sqrt
-/
lemma differentiableAt_sqrt {z : Complex} (hz : z in slitPlane) : DifferentiableAt Complex sqrt z :=
  (hasDerivAt_sqrt hz).differentiableAt

@[fun_prop]
/--
lemma `differentiableWithinAt_sqrt` / 引理 `differentiableWithinAt_sqrt`

English:
lemma differentiableWithinAt_sqrt
  given: {z : Complex} {s : Set Complex} (hz : z in slitPlane)
  proof: (differentiableAt_sqrt hz).differentiableWithinAt

@[fun_prop]

中文:
引理 differentiableWithinAt_sqrt
  条件: {z : 复形} {s : 集合 复形} (hz : z in slitPlane)
  证明: (differentiableAt_sqrt hz).differentiableWithinAt

@[fun_prop]

Depends on / 依赖: differentiableAt_sqrt, differentiableWithinAt
-/
lemma differentiableWithinAt_sqrt {z : Complex} {s : Set Complex} (hz : z in slitPlane) :
    DifferentiableWithinAt Complex sqrt s z :=
  (differentiableAt_sqrt hz).differentiableWithinAt

@[fun_prop]
/--
lemma `differentiableOn_sqrt` / 引理 `differentiableOn_sqrt`

English:
lemma differentiableOn_sqrt
  statement: DifferentiableOn Complex sqrt slitPlane
  proof: fun _ hz => (differentiableAt_sqrt hz).differentiableWithinAt

中文:
引理 differentiableOn_sqrt
  结论: DifferentiableOn 复形 sqrt slitPlane
  证明: fun _ hz => (differentiableAt_sqrt hz).differentiableWithinAt

Depends on / 依赖: differentiableAt_sqrt, differentiableWithinAt
-/
lemma differentiableOn_sqrt : DifferentiableOn Complex sqrt slitPlane :=
  fun _ hz => (differentiableAt_sqrt hz).differentiableWithinAt

/--
lemma `deriv_sqrt` / 引理 `deriv_sqrt`

English:
lemma deriv_sqrt
  given: {z : Complex} (hz : z in slitPlane)
  statement: deriv sqrt z = z ^ (-1 / 2 : Complex) / 2
  proof: (hasDerivAt_sqrt hz).deriv

中文:
引理 deriv_sqrt
  条件: {z : 复形} (hz : z in slitPlane)
  结论: deriv sqrt z = z ^ (-1 / 2 : 复形) / 2
  证明: (hasDerivAt_sqrt hz).deriv

Depends on / 依赖: hasDerivAt_sqrt
-/
lemma deriv_sqrt {z : Complex} (hz : z in slitPlane) : deriv sqrt z = z ^ (-1 / 2 : Complex) / 2 :=
  (hasDerivAt_sqrt hz).deriv

/--
lemma `derivWithin_sqrt` / 引理 `derivWithin_sqrt`

English:
lemma derivWithin_sqrt
  given: {z : Complex} (hz : z in slitPlane)
  proof: (hasDerivWithinAt_sqrt hz).derivWithin (isOpen_slitPlane.uniqueDiffWithinAt hz)

中文:
引理 derivWithin_sqrt
  条件: {z : 复形} (hz : z in slitPlane)
  证明: (hasDerivWithinAt_sqrt hz).derivWithin (isOpen_slitPlane.uniqueDiffWithinAt hz)

Depends on / 依赖: derivWithin, hasDerivWithinAt_sqrt, isOpen_slitPlane, isOpen_slitPlane.uniqueDiffWithinAt, uniqueDiffWithinAt
-/
lemma derivWithin_sqrt {z : Complex} (hz : z in slitPlane) :
    derivWithin sqrt slitPlane z = z ^ (-1 / 2 : Complex) / 2 :=
  (hasDerivWithinAt_sqrt hz).derivWithin (isOpen_slitPlane.uniqueDiffWithinAt hz)

/--
lemma `continuousAt_sqrt` / 引理 `continuousAt_sqrt`

English:
lemma continuousAt_sqrt
  given: {z : Complex} (hz : 0 <= z.re ∨ z.im != 0)
  statement: ContinuousAt sqrt z
  proof: continuousAt_cpow_const_of_re_pos hz (by norm_num)

中文:
引理 continuousAt_sqrt
  条件: {z : 复形} (hz : 0 <= z.re ∨ z.im != 0)
  结论: ContinuousAt sqrt z
  证明: continuousAt_cpow_const_of_re_pos hz (by norm_num)

Depends on / 依赖: continuousAt_cpow_const_of_re_pos
-/
lemma continuousAt_sqrt {z : Complex} (hz : 0 <= z.re ∨ z.im != 0) : ContinuousAt sqrt z :=
  continuousAt_cpow_const_of_re_pos hz (by norm_num)

/--
lemma `continuousOn_sqrt` / 引理 `continuousOn_sqrt`

English:
lemma continuousOn_sqrt
  statement: ContinuousOn sqrt slitPlane
  proof: fun _ hz => (continuousAt_sqrt (hz.imp le_of_lt id)).continuousWithinAt

中文:
引理 continuousOn_sqrt
  结论: ContinuousOn sqrt slitPlane
  证明: fun _ hz => (continuousAt_sqrt (hz.imp le_of_lt id)).continuousWithinAt

Depends on / 依赖: continuousAt_sqrt, continuousWithinAt, hz.imp, le_of_lt
-/
lemma continuousOn_sqrt : ContinuousOn sqrt slitPlane :=
  fun _ hz => (continuousAt_sqrt (hz.imp le_of_lt id)).continuousWithinAt

end Complex
