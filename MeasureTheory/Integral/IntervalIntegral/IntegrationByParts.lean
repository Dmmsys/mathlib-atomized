/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Integration by parts and by substitution

We derive additional integration techniques from FTC-2:
* `intervalIntegral.integral_mul_deriv_eq_deriv_mul` - integration by parts
* `intervalIntegral.integral_comp_mul_deriv''` - integration by substitution

Versions of the change of variables formula for monotone and antitone functions, but with much
weaker assumptions on the integrands and not restricted to intervals,
can be found in `Mathlib/MeasureTheory/Function/JacobianOneDim.lean`

## Tags

integration by parts, change of variables in integrals
-/

public section

open MeasureTheory Set

open scoped Topology Interval

namespace intervalIntegral

variable {a b : Real}

section Parts

section Mul

variable {A : Type*} [NormedRing A] [NormedAlgebra Real A] [CompleteSpace A] {u v u' v' : Real -> A}

/--
theorem `integral_deriv_mul_eq_sub_of_hasDeriv_right` / 定理 `integral_deriv_mul_eq_sub_of_hasDeriv_right`

English:
theorem integral_deriv_mul_eq_sub_of_hasDeriv_right
  statement: (hu : ContinuousOn u [[a, b]])
  proof: by
  apply integral_eq_sub_of_hasDeriv_right (hu.mul hv) fun x hx => (huu' x hx).mul (hvv' x hx)
  exact (hu'.mul_continuousOn hv).add (hv'.continuousOn_mul hu)

中文:
定理 integral_deriv_mul_eq_sub_of_hasDeriv_right
  结论: (hu : ContinuousOn u [[a, b]])
  证明: by
  apply integral_eq_sub_of_hasDeriv_right (hu.mul hv) fun x hx => (huu' x hx).mul (hvv' x hx)
  exact (hu'.mul_continuousOn hv).add (hv'.continuousOn_mul hu)

Depends on / 依赖: continuousOn_mul, hu.mul, integral_eq_sub_of_hasDeriv_right, mul_continuousOn
-/
theorem integral_deriv_mul_eq_sub_of_hasDeriv_right (hu : ContinuousOn u [[a, b]])
    (hv : ContinuousOn v [[a, b]])
    (huu' : forall x in Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : forall x in Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a := by
  apply integral_eq_sub_of_hasDeriv_right (hu.mul hv) fun x hx => (huu' x hx).mul (hvv' x hx)
  exact (hu'.mul_continuousOn hv).add (hv'.continuousOn_mul hu)

/--
theorem `integral_deriv_mul_eq_sub_of_hasDerivAt` / 定理 `integral_deriv_mul_eq_sub_of_hasDerivAt`

English:
theorem integral_deriv_mul_eq_sub_of_hasDerivAt
  statement: (hu : ContinuousOn u [[a, b]])
  proof: integral_deriv_mul_eq_sub_of_hasDeriv_right hu hv
    (fun x hx => huu' x hx |>.hasDerivWithinAt) (fun x hx => hvv' x hx |>.hasDerivWithinAt) hu' hv'

中文:
定理 integral_deriv_mul_eq_sub_of_hasDerivAt
  结论: (hu : ContinuousOn u [[a, b]])
  证明: integral_deriv_mul_eq_sub_of_hasDeriv_right hu hv
    (fun x hx => huu' x hx |>.hasDerivWithinAt) (fun x hx => hvv' x hx |>.hasDerivWithinAt) hu' hv'

Depends on / 依赖: hasDerivWithinAt, integral_deriv_mul_eq_sub_of_hasDeriv_right
-/
theorem integral_deriv_mul_eq_sub_of_hasDerivAt (hu : ContinuousOn u [[a, b]])
    (hv : ContinuousOn v [[a, b]]) (huu' : forall x in Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hvv' : forall x in Ioo (min a b) (max a b), HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a :=
  integral_deriv_mul_eq_sub_of_hasDeriv_right hu hv
    (fun x hx => huu' x hx |>.hasDerivWithinAt) (fun x hx => hvv' x hx |>.hasDerivWithinAt) hu' hv'

/--
theorem `integral_deriv_mul_eq_sub_of_hasDerivWithinAt` / 定理 `integral_deriv_mul_eq_sub_of_hasDerivWithinAt`

English:
theorem integral_deriv_mul_eq_sub_of_hasDerivWithinAt
  proof: integral_deriv_mul_eq_sub_of_hasDerivAt
    (fun x hx => (hu x hx).continuousWithinAt)
    (fun x hx => (hv x hx).continuousWithinAt)
    (fun x hx => hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx => hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
  

中文:
定理 integral_deriv_mul_eq_sub_of_hasDerivWithinAt
  证明: integral_deriv_mul_eq_sub_of_hasDerivAt
    (fun x hx => (hu x hx).continuousWithinAt)
    (fun x hx => (hv x hx).continuousWithinAt)
    (fun x hx => hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx => hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
  

Depends on / 依赖: Icc_mem_nhds, continuousWithinAt, hasDerivAt, integral_deriv_mul_eq_sub_of_hasDerivAt, mem_Icc_of_Ioo
-/
theorem integral_deriv_mul_eq_sub_of_hasDerivWithinAt
    (hu : forall x in [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x)
    (hv : forall x in [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a :=
  integral_deriv_mul_eq_sub_of_hasDerivAt
    (fun x hx => (hu x hx).continuousWithinAt)
    (fun x hx => (hv x hx).continuousWithinAt)
    (fun x hx => hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx => hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    hu' hv'

/--
theorem `integral_deriv_mul_eq_sub` / 定理 `integral_deriv_mul_eq_sub`

English:
theorem integral_deriv_mul_eq_sub
  proof: integral_deriv_mul_eq_sub_of_hasDerivWithinAt
    (fun x hx => hu x hx |>.hasDerivWithinAt) (fun x hx => hv x hx |>.hasDerivWithinAt) hu' hv'

中文:
定理 integral_deriv_mul_eq_sub
  证明: integral_deriv_mul_eq_sub_of_hasDerivWithinAt
    (fun x hx => hu x hx |>.hasDerivWithinAt) (fun x hx => hv x hx |>.hasDerivWithinAt) hu' hv'

Depends on / 依赖: hasDerivWithinAt, integral_deriv_mul_eq_sub_of_hasDerivWithinAt
-/
theorem integral_deriv_mul_eq_sub
    (hu : forall x in [[a, b]], HasDerivAt u (u' x) x) (hv : forall x in [[a, b]], HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a :=
  integral_deriv_mul_eq_sub_of_hasDerivWithinAt
    (fun x hx => hu x hx |>.hasDerivWithinAt) (fun x hx => hv x hx |>.hasDerivWithinAt) hu' hv'

/--
theorem `integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right` / 定理 `integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`

English:
theorem integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
  proof: by
  rw [← integral_deriv_mul_eq_sub_of_hasDeriv_right hu hv huu' hvv' hu' hv']; rw [← integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact (hu'.mul_continuousOn hv).add (hv'.continuousOn_mul hu)
  · exact hu'.mul_continuousOn hv

中文:
定理 integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
  证明: by
  rw [← integral_deriv_mul_eq_sub_of_hasDeriv_right hu hv huu' hvv' hu' hv']; rw [← integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact (hu'.mul_continuousOn hv).add (hv'.continuousOn_mul hu)
  · exact hu'.mul_continuousOn hv

Depends on / 依赖: add_sub_cancel_left, continuousOn_mul, integral_deriv_mul_eq_sub_of_hasDeriv_right, integral_sub, mul_continuousOn, simp_rw
-/
theorem integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (hu : ContinuousOn u [[a, b]]) (hv : ContinuousOn v [[a, b]])
    (huu' : forall x in Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : forall x in Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x := by
  rw [← integral_deriv_mul_eq_sub_of_hasDeriv_right hu hv huu' hvv' hu' hv']; rw [← integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact (hu'.mul_continuousOn hv).add (hv'.continuousOn_mul hu)
  · exact hu'.mul_continuousOn hv

/--
theorem `integral_mul_deriv_eq_deriv_mul_of_hasDerivAt` / 定理 `integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`

English:
theorem integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
  proof: integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hu hv
        (fun x hx => (huu' x hx).hasDerivWithinAt) (fun x hx => (hvv' x hx).hasDerivWithinAt) hu' hv'

中文:
定理 integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
  证明: integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hu hv
        (fun x hx => (huu' x hx).hasDerivWithinAt) (fun x hx => (hvv' x hx).hasDerivWithinAt) hu' hv'

Depends on / 依赖: hasDerivWithinAt, integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
-/
theorem integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (hu : ContinuousOn u [[a, b]]) (hv : ContinuousOn v [[a, b]])
    (huu' : forall x in Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hvv' : forall x in Ioo (min a b) (max a b), HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x :=
  integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right hu hv
        (fun x hx => (huu' x hx).hasDerivWithinAt) (fun x hx => (hvv' x hx).hasDerivWithinAt) hu' hv'

/--
theorem `integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt` / 定理 `integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt`

English:
theorem integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
  proof: integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (fun x hx => (hu x hx).continuousWithinAt)
    (fun x hx => (hv x hx).continuousWithinAt)
    (fun x hx => hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx => hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.

中文:
定理 integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
  证明: integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (fun x hx => (hu x hx).continuousWithinAt)
    (fun x hx => (hv x hx).continuousWithinAt)
    (fun x hx => hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx => hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.

Depends on / 依赖: Icc_mem_nhds, continuousWithinAt, hasDerivAt, integral_mul_deriv_eq_deriv_mul_of_hasDerivAt, mem_Icc_of_Ioo
-/
theorem integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (hu : forall x in [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x)
    (hv : forall x in [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x :=
  integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (fun x hx => (hu x hx).continuousWithinAt)
    (fun x hx => (hv x hx).continuousWithinAt)
    (fun x hx => hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx => hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    hu' hv'

/--
theorem `integral_mul_deriv_eq_deriv_mul` / 定理 `integral_mul_deriv_eq_deriv_mul`

English:
theorem integral_mul_deriv_eq_deriv_mul
  proof: integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (fun x hx => (hu x hx).hasDerivWithinAt) (fun x hx => (hv x hx).hasDerivWithinAt) hu' hv'

中文:
定理 integral_mul_deriv_eq_deriv_mul
  证明: integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (fun x hx => (hu x hx).hasDerivWithinAt) (fun x hx => (hv x hx).hasDerivWithinAt) hu' hv'

Depends on / 依赖: hasDerivWithinAt, integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
-/
theorem integral_mul_deriv_eq_deriv_mul
    (hu : forall x in [[a, b]], HasDerivAt u (u' x) x) (hv : forall x in [[a, b]], HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x :=
  integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (fun x hx => (hu x hx).hasDerivWithinAt) (fun x hx => (hv x hx).hasDerivWithinAt) hu' hv'

end Mul

section SMul

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra Real 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace Real E] [CompleteSpace E]
variable [IsScalarTower Real 𝕜 E]

variable {u u' : Real -> 𝕜}
variable {v v' : Real -> E}

/--
theorem `integral_deriv_smul_eq_sub_of_hasDeriv_right` / 定理 `integral_deriv_smul_eq_sub_of_hasDeriv_right`

English:
theorem integral_deriv_smul_eq_sub_of_hasDeriv_right
  statement: (hu : ContinuousOn u [[a, b]])
  proof: by
  simp_rw [add_comm]
  apply integral_eq_sub_of_hasDeriv_right (hu.smul hv) fun x hx => (huu' x hx).smul (hvv' x hx)
  exact (hv'.continuousOn_smul hu).add (hu'.smul_continuousOn hv)

中文:
定理 integral_deriv_smul_eq_sub_of_hasDeriv_right
  结论: (hu : ContinuousOn u [[a, b]])
  证明: by
  simp_rw [add_comm]
  apply integral_eq_sub_of_hasDeriv_right (hu.smul hv) fun x hx => (huu' x hx).smul (hvv' x hx)
  exact (hv'.continuousOn_smul hu).add (hu'.smul_continuousOn hv)

Depends on / 依赖: add_comm, continuousOn_smul, hu.smul, integral_eq_sub_of_hasDeriv_right, simp_rw, smul_continuousOn
-/
theorem integral_deriv_smul_eq_sub_of_hasDeriv_right (hu : ContinuousOn u [[a, b]])
    (hv : ContinuousOn v [[a, b]])
    (huu' : forall x in Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : forall x in Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u' x • v x + u x • v' x = u b • v b - u a • v a := by
  simp_rw [add_comm]
  apply integral_eq_sub_of_hasDeriv_right (hu.smul hv) fun x hx => (huu' x hx).smul (hvv' x hx)
  exact (hv'.continuousOn_smul hu).add (hu'.smul_continuousOn hv)

/--
theorem `integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right` / 定理 `integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right`

English:
theorem integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right
  proof: by
  rw [← integral_deriv_smul_eq_sub_of_hasDeriv_right hu hv huu' hvv' hu' hv']; rw [← integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact (hu'.smul_continuousOn hv).add (hv'.continuousOn_smul hu)
  · exact hu'.smul_continuousOn hv

中文:
定理 integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right
  证明: by
  rw [← integral_deriv_smul_eq_sub_of_hasDeriv_right hu hv huu' hvv' hu' hv']; rw [← integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact (hu'.smul_continuousOn hv).add (hv'.continuousOn_smul hu)
  · exact hu'.smul_continuousOn hv

Depends on / 依赖: add_sub_cancel_left, continuousOn_smul, integral_deriv_smul_eq_sub_of_hasDeriv_right, integral_sub, simp_rw, smul_continuousOn
-/
theorem integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right
    (hu : ContinuousOn u [[a, b]]) (hv : ContinuousOn v [[a, b]])
    (huu' : forall x in Ioo (min a b) (max a b), HasDerivWithinAt u (u' x) (Ioi x) x)
    (hvv' : forall x in Ioo (min a b) (max a b), HasDerivWithinAt v (v' x) (Ioi x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x := by
  rw [← integral_deriv_smul_eq_sub_of_hasDeriv_right hu hv huu' hvv' hu' hv']; rw [← integral_sub]
  · simp_rw [add_sub_cancel_left]
  · exact (hu'.smul_continuousOn hv).add (hv'.continuousOn_smul hu)
  · exact hu'.smul_continuousOn hv

/--
theorem `integral_smul_deriv_eq_deriv_smul_of_hasDerivAt` / 定理 `integral_smul_deriv_eq_deriv_smul_of_hasDerivAt`

English:
theorem integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
  proof: integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right hu hv
        (fun x hx => (huu' x hx).hasDerivWithinAt) (fun x hx => (hvv' x hx).hasDerivWithinAt) hu' hv'

中文:
定理 integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
  证明: integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right hu hv
        (fun x hx => (huu' x hx).hasDerivWithinAt) (fun x hx => (hvv' x hx).hasDerivWithinAt) hu' hv'

Depends on / 依赖: hasDerivWithinAt, integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right
-/
theorem integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (hu : ContinuousOn u [[a, b]]) (hv : ContinuousOn v [[a, b]])
    (huu' : forall x in Ioo (min a b) (max a b), HasDerivAt u (u' x) x)
    (hvv' : forall x in Ioo (min a b) (max a b), HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x :=
  integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right hu hv
        (fun x hx => (huu' x hx).hasDerivWithinAt) (fun x hx => (hvv' x hx).hasDerivWithinAt) hu' hv'

/--
theorem `integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt` / 定理 `integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt`

English:
theorem integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
  proof: integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (fun x hx => (hu x hx).continuousWithinAt)
    (fun x hx => (hv x hx).continuousWithinAt)
    (fun x hx => hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx => hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 h

中文:
定理 integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
  证明: integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (fun x hx => (hu x hx).continuousWithinAt)
    (fun x hx => (hv x hx).continuousWithinAt)
    (fun x hx => hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx => hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 h

Depends on / 依赖: Icc_mem_nhds, continuousWithinAt, hasDerivAt, integral_smul_deriv_eq_deriv_smul_of_hasDerivAt, mem_Icc_of_Ioo
-/
theorem integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
    (hu : forall x in [[a, b]], HasDerivWithinAt u (u' x) [[a, b]] x)
    (hv : forall x in [[a, b]], HasDerivWithinAt v (v' x) [[a, b]] x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x :=
  integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (fun x hx => (hu x hx).continuousWithinAt)
    (fun x hx => (hv x hx).continuousWithinAt)
    (fun x hx => hu x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    (fun x hx => hv x (mem_Icc_of_Ioo hx) |>.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
    hu' hv'

/--
theorem `integral_smul_deriv_eq_deriv_smul` / 定理 `integral_smul_deriv_eq_deriv_smul`

English:
theorem integral_smul_deriv_eq_deriv_smul
  proof: integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
    (fun x hx => (hu x hx).hasDerivWithinAt) (fun x hx => (hv x hx).hasDerivWithinAt) hu' hv'

中文:
定理 integral_smul_deriv_eq_deriv_smul
  证明: integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
    (fun x hx => (hu x hx).hasDerivWithinAt) (fun x hx => (hv x hx).hasDerivWithinAt) hu' hv'

Depends on / 依赖: hasDerivWithinAt, integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
-/
theorem integral_smul_deriv_eq_deriv_smul
    (hu : forall x in [[a, b]], HasDerivAt u (u' x) x) (hv : forall x in [[a, b]], HasDerivAt v (v' x) x)
    (hu' : IntervalIntegrable u' volume a b) (hv' : IntervalIntegrable v' volume a b) :
    ∫ x in a..b, u x • v' x = u b • v b - u a • v a - ∫ x in a..b, u' x • v x :=
  integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
    (fun x hx => (hu x hx).hasDerivWithinAt) (fun x hx => (hv x hx).hasDerivWithinAt) hu' hv'

end SMul

end Parts

/-!
### Integration by substitution / Change of variables
-/

section SMul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f f' : Real -> Real} {g g' : Real -> E}

/--
theorem `integral_deriv_smul_comp'''` / 定理 `integral_deriv_smul_comp'''`

English:
theorem integral_deriv_smul_comp'''
  statement: (hf : ContinuousOn f [[a, b]])
  proof: by
  by_cases hE : CompleteSpace E; swap
  · simp [intervalIntegral, integral, hE]
  rw [hf.image_uIcc]; rw [← intervalIntegrable_iff'] at hg1
  have h_cont : ContinuousOn (fun u => ∫ t in f a..f u, g t) [[a, b]] := by
    refine (continuousOn_primitive_interval' hg1 ?_).comp hf ?_
    · rw [← hf.im

中文:
定理 integral_deriv_smul_comp'''
  结论: (hf : ContinuousOn f [[a, b]])
  证明: by
  by_cases hE : CompleteSpace E; swap
  · simp [intervalIntegral, integral, hE]
  rw [hf.image_uIcc]; rw [← intervalIntegrable_iff'] at hg1
  have h_cont : ContinuousOn (fun u => ∫ t in f a..f u, g t) [[a, b]] := by
    refine (continuousOn_primitive_interval' hg1 ?_).comp hf ?_
    · rw [← hf.im

Depends on / 依赖: CompleteSpace, ContinuousOn, HasDerivWithinAt, continuousOn_primitive_interval, h_cont, h_der, hf.image_uIcc, image_uIcc, integral, intervalIntegrable_iff, intervalIntegral, left_mem_uIcc, mapsTo_image, mem_image_of_mem
-/
theorem integral_deriv_smul_comp''' (hf : ContinuousOn f [[a, b]])
    (hff' : forall x in Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hg_cont : ContinuousOn g (f '' Ioo (min a b) (max a b))) (hg1 : IntegrableOn g (f '' [[a, b]]))
    (hg2 : IntegrableOn (fun x => f' x • (g ∘ f) x) [[a, b]]) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := by
  by_cases hE : CompleteSpace E; swap
  · simp [intervalIntegral, integral, hE]
  rw [hf.image_uIcc]; rw [← intervalIntegrable_iff'] at hg1
  have h_cont : ContinuousOn (fun u => ∫ t in f a..f u, g t) [[a, b]] := by
    refine (continuousOn_primitive_interval' hg1 ?_).comp hf ?_
    · rw [← hf.image_uIcc]; exact mem_image_of_mem f left_mem_uIcc
    · rw [← hf.image_uIcc]; exact mapsTo_image _ _
  have h_der :
    forall x in Ioo (min a b) (max a b),
      HasDerivWithinAt (fun u => ∫ t in f a..f u, g t) (f' x • (g ∘ f) x) (Ioi x) x := by
    intro x hx
    obtain ⟨c, hc⟩ := nonempty_Ioo.mpr hx.1
    obtain ⟨d, hd⟩ := nonempty_Ioo.mpr hx.2
    have cdsub : [[c, d]] subseteq Ioo (min a b) (max a b) := by
      rw [uIcc_of_le (hc.2.trans hd.1).le]
      exact Icc_subset_Ioo hc.1 hd.2
    replace hg_cont := hg_cont.mono (image_mono cdsub)
    let J := [[sInf (f '' [[c, d]]), sSup (f '' [[c, d]])]]
    have hJ : f '' [[c, d]] = J := (hf.mono (cdsub.trans Ioo_subset_Icc_self)).image_uIcc
    rw [hJ] at hg_cont
    have h2x : f x in J := by rw [← hJ]; exact mem_image_of_mem _ (mem_uIcc_of_le hc.2.le hd.1.le)
    have h2g : IntervalIntegrable g volume (f a) (f x) := by
      refine hg1.mono_set ?_
      rw [← hf.image_uIcc]
      exact hf.surjOn_uIcc left_mem_uIcc (Ioo_subset_Icc_self hx)
    have h3g : StronglyMeasurableAtFilter g (𝓝[J] f x) :=
      hg_cont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc (f x)
    have : Fact (f x in J) := ⟨h2x⟩
    have : HasDerivWithinAt (fun u => ∫ x in f a..u, g x) (g (f x)) J (f x) :=
      intervalIntegral.integral_hasDerivWithinAt_right h2g h3g (hg_cont (f x) h2x)
    refine (this.scomp x ((hff' x hx).Ioo_of_Ioi hd.1) ?_).Ioi_of_Ioo hd.1
    rw [← hJ]
    refine (mapsTo_image _ _).mono ?_ Subset.rfl
    exact Ioo_subset_Icc_self.trans ((Icc_subset_Icc_left hc.2.le).trans Icc_subset_uIcc)
  rw [← intervalIntegrable_iff'] at hg2
  simp_rw [integral_eq_sub_of_hasDeriv_right h_cont h_der hg2, integral_same, sub_zero]

@[deprecated (since := "2026-03-19")]
alias integral_comp_smul_deriv''' := integral_deriv_smul_comp'''

/--
theorem `integral_deriv_smul_comp''` / 定理 `integral_deriv_smul_comp''`

English:
theorem integral_deriv_smul_comp''
  statement: (hf : ContinuousOn f [[a, b]])
  proof: by
  refine integral_deriv_smul_comp''' hf hff' (hg.mono <| image_mono Ioo_subset_Icc_self) ?_
    (hf'.smul (hg.comp hf <| subset_preimage_image f _)).integrableOn_Icc
  rw [hf.image_uIcc] at hg ⊢
  exact hg.integrableOn_Icc

@[deprecated (since := "2026-03-19")]
alias integral_comp_smul_deriv'' :=

中文:
定理 integral_deriv_smul_comp''
  结论: (hf : ContinuousOn f [[a, b]])
  证明: by
  refine integral_deriv_smul_comp''' hf hff' (hg.mono <| image_mono Ioo_subset_Icc_self) ?_
    (hf'.smul (hg.comp hf <| subset_preimage_image f _)).integrableOn_Icc
  rw [hf.image_uIcc] at hg ⊢
  exact hg.integrableOn_Icc

@[deprecated (since := "2026-03-19")]
alias integral_comp_smul_deriv'' :=

Depends on / 依赖: Ioo_subset_Icc_self, hf.image_uIcc, hg.comp, hg.integrableOn_Icc, hg.mono, image_mono, image_uIcc, integrableOn_Icc, integral_deriv_smul_comp, subset_preimage_image
-/
theorem integral_deriv_smul_comp'' (hf : ContinuousOn f [[a, b]])
    (hff' : forall x in Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g (f '' [[a, b]])) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := by
  refine integral_deriv_smul_comp''' hf hff' (hg.mono <| image_mono Ioo_subset_Icc_self) ?_
    (hf'.smul (hg.comp hf <| subset_preimage_image f _)).integrableOn_Icc
  rw [hf.image_uIcc] at hg ⊢
  exact hg.integrableOn_Icc

@[deprecated (since := "2026-03-19")]
alias integral_comp_smul_deriv'' := integral_deriv_smul_comp''

/--
theorem `integral_deriv_smul_comp'` / 定理 `integral_deriv_smul_comp'`

English:
theorem integral_deriv_smul_comp'
  statement: (h : forall x in uIcc a b, HasDerivAt f (f' x) x)
  proof: integral_deriv_smul_comp'' (fun x hx => (h x hx).continuousAt.continuousWithinAt)
    (fun x hx => (h x <| Ioo_subset_Icc_self hx).hasDerivWithinAt) h' hg

@[deprecated (since := "2026-03-19")]
alias integral_comp_smul_deriv' := integral_deriv_smul_comp'

中文:
定理 integral_deriv_smul_comp'
  结论: (h : 对任意 x in uIcc a b, 在点处可导 f (f' x) x)
  证明: integral_deriv_smul_comp'' (fun x hx => (h x hx).continuousAt.continuousWithinAt)
    (fun x hx => (h x <| Ioo_subset_Icc_self hx).hasDerivWithinAt) h' hg

@[deprecated (since := "2026-03-19")]
alias integral_comp_smul_deriv' := integral_deriv_smul_comp'

Depends on / 依赖: Ioo_subset_Icc_self, continuousAt, continuousAt.continuousWithinAt, continuousWithinAt, hasDerivWithinAt, integral_deriv_smul_comp
-/
theorem integral_deriv_smul_comp' (h : forall x in uIcc a b, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (uIcc a b)) (hg : ContinuousOn g (f '' [[a, b]])) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ x in f a..f b, g x :=
  integral_deriv_smul_comp'' (fun x hx => (h x hx).continuousAt.continuousWithinAt)
    (fun x hx => (h x <| Ioo_subset_Icc_self hx).hasDerivWithinAt) h' hg

@[deprecated (since := "2026-03-19")]
alias integral_comp_smul_deriv' := integral_deriv_smul_comp'

/--
theorem `integral_deriv_smul_comp` / 定理 `integral_deriv_smul_comp`

English:
theorem integral_deriv_smul_comp
  statement: (h : forall x in uIcc a b, HasDerivAt f (f' x) x)
  proof: integral_deriv_smul_comp' h h' hg.continuousOn

@[deprecated (since := "2026-03-19")]
alias integral_comp_smul_deriv := integral_deriv_smul_comp

中文:
定理 integral_deriv_smul_comp
  结论: (h : 对任意 x in uIcc a b, 在点处可导 f (f' x) x)
  证明: integral_deriv_smul_comp' h h' hg.continuousOn

@[deprecated (since := "2026-03-19")]
alias integral_comp_smul_deriv := integral_deriv_smul_comp

Depends on / 依赖: continuousOn, hg.continuousOn, integral_deriv_smul_comp
-/
theorem integral_deriv_smul_comp (h : forall x in uIcc a b, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (uIcc a b)) (hg : Continuous g) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ x in f a..f b, g x :=
  integral_deriv_smul_comp' h h' hg.continuousOn

@[deprecated (since := "2026-03-19")]
alias integral_comp_smul_deriv := integral_deriv_smul_comp

/--
theorem `integral_deriv_smul_comp_of_deriv_nonneg` / 定理 `integral_deriv_smul_comp_of_deriv_nonneg`

English:
theorem integral_deriv_smul_comp_of_deriv_nonneg
  statement: (hf : ContinuousOn f [[a, b]])
  proof: by
  have M : MonotoneOn f (uIcc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_uIcc a b) hf
    · rw [uIcc, interior_Icc]
      exact fun z hz => (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [uIcc, interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z h

中文:
定理 integral_deriv_smul_comp_of_deriv_nonneg
  结论: (hf : ContinuousOn f [[a, b]])
  证明: by
  have M : MonotoneOn f (uIcc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_uIcc a b) hf
    · rw [uIcc, interior_Icc]
      exact fun z hz => (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [uIcc, interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z h

Depends on / 依赖: Function, Function.comp_apply, MonotoneOn, comp_apply, convex_uIcc, differentiableAt, differentiableAt.differentiableWithinAt, differentiableWithinAt, integral_Icc_deriv_smul_of_deriv_nonneg, integral_Icc_eq_integral_Ioc, integral_of_le, interior_Icc, le_or_gt, left_m, monotoneOn_of_deriv_nonneg
-/
theorem integral_deriv_smul_comp_of_deriv_nonneg (hf : ContinuousOn f [[a, b]])
    (hff' : forall x in Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hf' : forall x in Ioo (min a b) (max a b), 0 <= f' x) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := by
  have M : MonotoneOn f (uIcc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_uIcc a b) hf
    · rw [uIcc, interior_Icc]
      exact fun z hz => (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [uIcc, interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z hz
  simp only [Function.comp_apply]
  rcases le_or_gt a b with hab | hab
  · rw [integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      integral_Icc_deriv_smul_of_deriv_nonneg, integral_of_le, ← integral_Icc_eq_integral_Ioc]
    · apply M left_mem_uIcc right_mem_uIcc hab
    · rwa [uIcc_of_le hab] at hf
    · grind
    · grind
    · exact hab
  · rw [integral_of_ge hab.le, ← integral_Icc_eq_integral_Ioc,
      integral_Icc_deriv_smul_of_deriv_nonneg, integral_of_ge, ← integral_Icc_eq_integral_Ioc]
    · apply M right_mem_uIcc left_mem_uIcc hab.le
    · rwa [uIcc_of_ge hab.le] at hf
    · grind
    · grind
    · exact hab.le

/--
lemma `integrable_deriv_smul_comp_iff_of_deriv_nonneg` / 引理 `integrable_deriv_smul_comp_iff_of_deriv_nonneg`

English:
lemma integrable_deriv_smul_comp_iff_of_deriv_nonneg
  statement: (hf : ContinuousOn f [[a, b]])
  proof: by
  have M : MonotoneOn f (uIcc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_uIcc a b) hf
    · rw [uIcc, interior_Icc]
      exact fun z hz => (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [uIcc, interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z h

中文:
引理 integrable_deriv_smul_comp_iff_of_deriv_nonneg
  结论: (hf : ContinuousOn f [[a, b]])
  证明: by
  have M : MonotoneOn f (uIcc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_uIcc a b) hf
    · rw [uIcc, interior_Icc]
      exact fun z hz => (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [uIcc, interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z h

Depends on / 依赖: Function, Function.comp_apply, MonotoneOn, comp_apply, convex_uIcc, differentiableAt, differentiableAt.differentiableWithinAt, differentiableWithinAt, integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg, interior_Icc, intervalIntegrable_iff_integrableOn_Icc_of_le, le_or_gt, monotoneOn_of_deriv_nonneg
-/
lemma integrable_deriv_smul_comp_iff_of_deriv_nonneg (hf : ContinuousOn f [[a, b]])
    (hff' : forall x in Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hf' : forall x in Ioo (min a b) (max a b), 0 <= f' x) :
    IntervalIntegrable (fun x => f' x • (g ∘ f) x) volume a b ↔
      IntervalIntegrable g volume (f a) (f b) := by
  have M : MonotoneOn f (uIcc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_uIcc a b) hf
    · rw [uIcc, interior_Icc]
      exact fun z hz => (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [uIcc, interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z hz
  simp only [Function.comp_apply]
  rcases le_or_gt a b with hab | hab
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab,
      integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg,
      intervalIntegrable_iff_integrableOn_Icc_of_le]
    · apply M left_mem_uIcc right_mem_uIcc hab
    · rwa [uIcc_of_le hab] at hf
    · grind
    · grind
    · exact hab
  · rw [IntervalIntegrable.symm_iff, intervalIntegrable_iff_integrableOn_Icc_of_le hab.le,
      integrableOn_Icc_deriv_smul_iff_of_deriv_nonneg,
      IntervalIntegrable.symm_iff, intervalIntegrable_iff_integrableOn_Icc_of_le]
    · apply M right_mem_uIcc left_mem_uIcc hab.le
    · rwa [uIcc_of_ge hab.le] at hf
    · grind
    · grind
    · exact hab.le

/--
theorem `integral_deriv_smul_comp_of_deriv_nonpos` / 定理 `integral_deriv_smul_comp_of_deriv_nonpos`

English:
theorem integral_deriv_smul_comp_of_deriv_nonpos
  statement: (hf : ContinuousOn f [[a, b]])
  proof: by
  have M : AntitoneOn f (uIcc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_uIcc a b) hf
    · rw [uIcc, interior_Icc]
      exact fun z hz => (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [uIcc, interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z h

中文:
定理 integral_deriv_smul_comp_of_deriv_nonpos
  结论: (hf : ContinuousOn f [[a, b]])
  证明: by
  have M : AntitoneOn f (uIcc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_uIcc a b) hf
    · rw [uIcc, interior_Icc]
      exact fun z hz => (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [uIcc, interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z h

Depends on / 依赖: AntitoneOn, Function, Function.comp_apply, antitoneOn_of_deriv_nonpos, comp_apply, convex_uIcc, differentiableAt, differentiableAt.differentiableWithinAt, differentiableWithinAt, integral_Icc_deriv_smul_of_deriv_nonpos, integral_Icc_eq_integral_Ioc, integral_of_ge, integral_of_le, interior_Icc, le_or_gt, left_m
-/
theorem integral_deriv_smul_comp_of_deriv_nonpos (hf : ContinuousOn f [[a, b]])
    (hff' : forall x in Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hf' : forall x in Ioo (min a b) (max a b), f' x <= 0) :
    (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := by
  have M : AntitoneOn f (uIcc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_uIcc a b) hf
    · rw [uIcc, interior_Icc]
      exact fun z hz => (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [uIcc, interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z hz
  simp only [Function.comp_apply]
  rcases le_or_gt a b with hab | hab
  · rw [integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      integral_Icc_deriv_smul_of_deriv_nonpos, integral_of_ge, ← integral_Icc_eq_integral_Ioc]
    · apply M left_mem_uIcc right_mem_uIcc hab
    · rwa [uIcc_of_le hab] at hf
    · grind
    · grind
    · exact hab
  · rw [integral_of_ge hab.le, ← integral_Icc_eq_integral_Ioc,
      integral_Icc_deriv_smul_of_deriv_nonpos, integral_of_le, ← integral_Icc_eq_integral_Ioc,
      neg_neg]
    · apply M right_mem_uIcc left_mem_uIcc hab.le
    · rwa [uIcc_of_ge hab.le] at hf
    · grind
    · grind
    · exact hab.le

/--
lemma `integrable_deriv_smul_comp_iff_of_deriv_nonpos` / 引理 `integrable_deriv_smul_comp_iff_of_deriv_nonpos`

English:
lemma integrable_deriv_smul_comp_iff_of_deriv_nonpos
  statement: (hf : ContinuousOn f [[a, b]])
  proof: by
  have M : AntitoneOn f (uIcc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_uIcc a b) hf
    · rw [uIcc, interior_Icc]
      exact fun z hz => (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [uIcc, interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z h

中文:
引理 integrable_deriv_smul_comp_iff_of_deriv_nonpos
  结论: (hf : ContinuousOn f [[a, b]])
  证明: by
  have M : AntitoneOn f (uIcc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_uIcc a b) hf
    · rw [uIcc, interior_Icc]
      exact fun z hz => (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [uIcc, interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z h

Depends on / 依赖: AntitoneOn, Function, Function.comp_apply, IntervalIntegrable, IntervalIntegrable.symm_iff, antitoneOn_of_deriv_nonpos, comp_apply, convex_uIcc, differentiableAt, differentiableAt.differentiableWithinAt, differentiableWithinAt, integrableOn_Icc_deriv_smul_iff_of_deriv_nonpos, interior_Icc, intervalIntegrable_iff_integ, intervalIntegrable_iff_integrableOn_Icc_of_le, le_or_gt, symm_iff
-/
lemma integrable_deriv_smul_comp_iff_of_deriv_nonpos (hf : ContinuousOn f [[a, b]])
    (hff' : forall x in Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hf' : forall x in Ioo (min a b) (max a b), f' x <= 0) :
    IntervalIntegrable (fun x => f' x • (g ∘ f) x) volume a b ↔
      IntervalIntegrable g volume (f a) (f b) := by
  have M : AntitoneOn f (uIcc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_uIcc a b) hf
    · rw [uIcc, interior_Icc]
      exact fun z hz => (hff' z hz).differentiableAt.differentiableWithinAt
    · rw [uIcc, interior_Icc]
      intro z hz
      simpa [(hff' z hz).deriv] using hf' z hz
  simp only [Function.comp_apply]
  rcases le_or_gt a b with hab | hab
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab,
      integrableOn_Icc_deriv_smul_iff_of_deriv_nonpos,
      IntervalIntegrable.symm_iff, intervalIntegrable_iff_integrableOn_Icc_of_le]
    · apply M left_mem_uIcc right_mem_uIcc hab
    · rwa [uIcc_of_le hab] at hf
    · grind
    · grind
    · exact hab
  · rw [IntervalIntegrable.symm_iff, intervalIntegrable_iff_integrableOn_Icc_of_le hab.le,
      integrableOn_Icc_deriv_smul_iff_of_deriv_nonpos,
      intervalIntegrable_iff_integrableOn_Icc_of_le]
    · apply M right_mem_uIcc left_mem_uIcc hab.le
    · rwa [uIcc_of_ge hab.le] at hf
    · grind
    · grind
    · exact hab.le

section CompleteSpace

variable [CompleteSpace E]

/--
theorem `integral_deriv_smul_deriv_comp'` / 定理 `integral_deriv_smul_deriv_comp'`

English:
theorem integral_deriv_smul_deriv_comp'
  statement: (hf : ContinuousOn f [[a, b]])
  proof: by
  rw [integral_deriv_smul_comp'' hf hff' hf' hg']; rw [integral_eq_sub_of_hasDeriv_right hg hgg' (hg'.mono _).intervalIntegrable]
  exacts [rfl, intermediate_value_uIcc hf]

@[deprecated (since := "2026-03-19")]
alias integral_deriv_comp_smul_deriv' := integral_deriv_smul_deriv_comp'

中文:
定理 integral_deriv_smul_deriv_comp'
  结论: (hf : ContinuousOn f [[a, b]])
  证明: by
  rw [integral_deriv_smul_comp'' hf hff' hf' hg']; rw [integral_eq_sub_of_hasDeriv_right hg hgg' (hg'.mono _).intervalIntegrable]
  exacts [rfl, intermediate_value_uIcc hf]

@[deprecated (since := "2026-03-19")]
alias integral_deriv_comp_smul_deriv' := integral_deriv_smul_deriv_comp'

Depends on / 依赖: exacts, integral_deriv_smul_comp, integral_eq_sub_of_hasDeriv_right, intermediate_value_uIcc, intervalIntegrable
-/
theorem integral_deriv_smul_deriv_comp' (hf : ContinuousOn f [[a, b]])
    (hff' : forall x in Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g [[f a, f b]])
    (hgg' : forall x in Ioo (min (f a) (f b)) (max (f a) (f b)), HasDerivWithinAt g (g' x) (Ioi x) x)
    (hg' : ContinuousOn g' (f '' [[a, b]])) :
    (∫ x in a..b, f' x • (g' ∘ f) x) = (g ∘ f) b - (g ∘ f) a := by
  rw [integral_deriv_smul_comp'' hf hff' hf' hg']; rw [integral_eq_sub_of_hasDeriv_right hg hgg' (hg'.mono _).intervalIntegrable]
  exacts [rfl, intermediate_value_uIcc hf]

@[deprecated (since := "2026-03-19")]
alias integral_deriv_comp_smul_deriv' := integral_deriv_smul_deriv_comp'

/--
theorem `integral_deriv_smul_deriv_comp` / 定理 `integral_deriv_smul_deriv_comp`

English:
theorem integral_deriv_smul_deriv_comp
  statement: (hf : forall x in uIcc a b, HasDerivAt f (f' x) x)
  proof: integral_eq_sub_of_hasDerivAt (fun x hx => (hg x hx).scomp x <| hf x hx)
    (hf'.smul (hg'.comp_continuousOn <| HasDerivAt.continuousOn hf)).intervalIntegrable

@[deprecated (since := "2026-03-19")]
alias integral_deriv_comp_smul_deriv := integral_deriv_smul_deriv_comp

中文:
定理 integral_deriv_smul_deriv_comp
  结论: (hf : 对任意 x in uIcc a b, 在点处可导 f (f' x) x)
  证明: integral_eq_sub_of_hasDerivAt (fun x hx => (hg x hx).scomp x <| hf x hx)
    (hf'.smul (hg'.comp_continuousOn <| HasDerivAt.continuousOn hf)).intervalIntegrable

@[deprecated (since := "2026-03-19")]
alias integral_deriv_comp_smul_deriv := integral_deriv_smul_deriv_comp

Depends on / 依赖: HasDerivAt, HasDerivAt.continuousOn, comp_continuousOn, continuousOn, integral_eq_sub_of_hasDerivAt, intervalIntegrable
-/
theorem integral_deriv_smul_deriv_comp (hf : forall x in uIcc a b, HasDerivAt f (f' x) x)
    (hg : forall x in uIcc a b, HasDerivAt g (g' (f x)) (f x)) (hf' : ContinuousOn f' (uIcc a b))
    (hg' : Continuous g') : (∫ x in a..b, f' x • (g' ∘ f) x) = (g ∘ f) b - (g ∘ f) a :=
  integral_eq_sub_of_hasDerivAt (fun x hx => (hg x hx).scomp x <| hf x hx)
    (hf'.smul (hg'.comp_continuousOn <| HasDerivAt.continuousOn hf)).intervalIntegrable

@[deprecated (since := "2026-03-19")]
alias integral_deriv_comp_smul_deriv := integral_deriv_smul_deriv_comp

end CompleteSpace

end SMul

section Mul

/--
theorem `integral_comp_mul_deriv'''` / 定理 `integral_comp_mul_deriv'''`

English:
theorem integral_comp_mul_deriv'''
  statement: {a b : Real} {f f' : Real -> Real} {g : Real -> Real}
  proof: by
  have hg2' : IntegrableOn (fun x => f' x • (g ∘ f) x) [[a, b]] := by simpa [mul_comm] using hg2
  simpa [mul_comm] using integral_deriv_smul_comp''' hf hff' hg_cont hg1 hg2'

中文:
定理 integral_comp_mul_deriv'''
  结论: {a b : 实数} {f f' : 实数 -> 实数} {g : 实数 -> 实数}
  证明: by
  have hg2' : IntegrableOn (fun x => f' x • (g ∘ f) x) [[a, b]] := by simpa [mul_comm] using hg2
  simpa [mul_comm] using integral_deriv_smul_comp''' hf hff' hg_cont hg1 hg2'

Depends on / 依赖: IntegrableOn, hg_cont, integral_deriv_smul_comp, mul_comm
-/
theorem integral_comp_mul_deriv''' {a b : Real} {f f' : Real -> Real} {g : Real -> Real}
    (hf : ContinuousOn f [[a, b]])
    (hff' : forall x in Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hg_cont : ContinuousOn g (f '' Ioo (min a b) (max a b))) (hg1 : IntegrableOn g (f '' [[a, b]]))
    (hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) [[a, b]]) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ u in f a..f b, g u := by
  have hg2' : IntegrableOn (fun x => f' x • (g ∘ f) x) [[a, b]] := by simpa [mul_comm] using hg2
  simpa [mul_comm] using integral_deriv_smul_comp''' hf hff' hg_cont hg1 hg2'

/--
theorem `integral_comp_mul_deriv''` / 定理 `integral_comp_mul_deriv''`

English:
theorem integral_comp_mul_deriv''
  statement: {f f' g : Real -> Real} (hf : ContinuousOn f [[a, b]])
  proof: by
  simpa [mul_comm] using integral_deriv_smul_comp'' hf hff' hf' hg

中文:
定理 integral_comp_mul_deriv''
  结论: {f f' g : 实数 -> 实数} (hf : ContinuousOn f [[a, b]])
  证明: by
  simpa [mul_comm] using integral_deriv_smul_comp'' hf hff' hf' hg

Depends on / 依赖: integral_deriv_smul_comp, mul_comm
-/
theorem integral_comp_mul_deriv'' {f f' g : Real -> Real} (hf : ContinuousOn f [[a, b]])
    (hff' : forall x in Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g (f '' [[a, b]])) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ u in f a..f b, g u := by
  simpa [mul_comm] using integral_deriv_smul_comp'' hf hff' hf' hg

/--
theorem `integral_comp_mul_deriv'` / 定理 `integral_comp_mul_deriv'`

English:
theorem integral_comp_mul_deriv'
  statement: {f f' g : Real -> Real} (h : forall x in uIcc a b, HasDerivAt f (f' x) x)
  proof: by
  simpa [mul_comm] using integral_deriv_smul_comp' h h' hg

中文:
定理 integral_comp_mul_deriv'
  结论: {f f' g : 实数 -> 实数} (h : 对任意 x in uIcc a b, 在点处可导 f (f' x) x)
  证明: by
  simpa [mul_comm] using integral_deriv_smul_comp' h h' hg

Depends on / 依赖: integral_deriv_smul_comp, mul_comm
-/
theorem integral_comp_mul_deriv' {f f' g : Real -> Real} (h : forall x in uIcc a b, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (uIcc a b)) (hg : ContinuousOn g (f '' [[a, b]])) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ x in f a..f b, g x := by
  simpa [mul_comm] using integral_deriv_smul_comp' h h' hg

/-- Change of variables, most common version. If `f` has continuous derivative `f'` on `[a, b]`,
and `g` is continuous, then we can substitute `u = f x` to get
`∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
-/
@[wikidata Q1071270]
/--
theorem `integral_comp_mul_deriv` / 定理 `integral_comp_mul_deriv`

English:
theorem integral_comp_mul_deriv
  statement: {f f' g : Real -> Real} (h : forall x in uIcc a b, HasDerivAt f (f' x) x)
  proof: integral_comp_mul_deriv' h h' hg.continuousOn

中文:
定理 integral_comp_mul_deriv
  结论: {f f' g : 实数 -> 实数} (h : 对任意 x in uIcc a b, 在点处可导 f (f' x) x)
  证明: integral_comp_mul_deriv' h h' hg.continuousOn

Depends on / 依赖: continuousOn, hg.continuousOn, integral_comp_mul_deriv
-/
theorem integral_comp_mul_deriv {f f' g : Real -> Real} (h : forall x in uIcc a b, HasDerivAt f (f' x) x)
    (h' : ContinuousOn f' (uIcc a b)) (hg : Continuous g) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ x in f a..f b, g x :=
  integral_comp_mul_deriv' h h' hg.continuousOn

/--
theorem `integral_comp_mul_deriv_of_deriv_nonneg` / 定理 `integral_comp_mul_deriv_of_deriv_nonneg`

English:
theorem integral_comp_mul_deriv_of_deriv_nonneg
  statement: {f f' g : Real -> Real} (hf : ContinuousOn f [[a, b]])
  proof: by
  simpa [mul_comm] using! integral_deriv_smul_comp_of_deriv_nonneg hf hff' hf'

中文:
定理 integral_comp_mul_deriv_of_deriv_nonneg
  结论: {f f' g : 实数 -> 实数} (hf : ContinuousOn f [[a, b]])
  证明: by
  simpa [mul_comm] using! integral_deriv_smul_comp_of_deriv_nonneg hf hff' hf'

Depends on / 依赖: integral_deriv_smul_comp_of_deriv_nonneg, mul_comm
-/
theorem integral_comp_mul_deriv_of_deriv_nonneg {f f' g : Real -> Real} (hf : ContinuousOn f [[a, b]])
    (hff' : forall x in Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hf' : forall x in Ioo (min a b) (max a b), 0 <= f' x) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ u in f a..f b, g u := by
  simpa [mul_comm] using! integral_deriv_smul_comp_of_deriv_nonneg hf hff' hf'

/--
theorem `integral_comp_mul_deriv_of_deriv_nonpos` / 定理 `integral_comp_mul_deriv_of_deriv_nonpos`

English:
theorem integral_comp_mul_deriv_of_deriv_nonpos
  statement: {f f' g : Real -> Real} (hf : ContinuousOn f [[a, b]])
  proof: by
  simpa [mul_comm] using! integral_deriv_smul_comp_of_deriv_nonpos hf hff' hf'

中文:
定理 integral_comp_mul_deriv_of_deriv_nonpos
  结论: {f f' g : 实数 -> 实数} (hf : ContinuousOn f [[a, b]])
  证明: by
  simpa [mul_comm] using! integral_deriv_smul_comp_of_deriv_nonpos hf hff' hf'

Depends on / 依赖: integral_deriv_smul_comp_of_deriv_nonpos, mul_comm
-/
theorem integral_comp_mul_deriv_of_deriv_nonpos {f f' g : Real -> Real} (hf : ContinuousOn f [[a, b]])
    (hff' : forall x in Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hf' : forall x in Ioo (min a b) (max a b), f' x <= 0) :
    (∫ x in a..b, (g ∘ f) x * f' x) = ∫ u in f a..f b, g u := by
  simpa [mul_comm] using! integral_deriv_smul_comp_of_deriv_nonpos hf hff' hf'

/--
lemma `integrable_comp_mul_deriv_iff_of_deriv_nonneg` / 引理 `integrable_comp_mul_deriv_iff_of_deriv_nonneg`

English:
lemma integrable_comp_mul_deriv_iff_of_deriv_nonneg
  statement: {f f' g : Real -> Real} (hf : ContinuousOn f [[a, b]])
  proof: by
  simpa [mul_comm] using! integrable_deriv_smul_comp_iff_of_deriv_nonneg hf hff' hf'

中文:
引理 integrable_comp_mul_deriv_iff_of_deriv_nonneg
  结论: {f f' g : 实数 -> 实数} (hf : ContinuousOn f [[a, b]])
  证明: by
  simpa [mul_comm] using! integrable_deriv_smul_comp_iff_of_deriv_nonneg hf hff' hf'

Depends on / 依赖: integrable_deriv_smul_comp_iff_of_deriv_nonneg, mul_comm
-/
lemma integrable_comp_mul_deriv_iff_of_deriv_nonneg {f f' g : Real -> Real} (hf : ContinuousOn f [[a, b]])
    (hff' : forall x in Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hf' : forall x in Ioo (min a b) (max a b), 0 <= f' x) :
    IntervalIntegrable (fun x => (g ∘ f) x * f' x) volume a b ↔
      IntervalIntegrable g volume (f a) (f b) := by
  simpa [mul_comm] using! integrable_deriv_smul_comp_iff_of_deriv_nonneg hf hff' hf'

/--
lemma `integrable_comp_mul_deriv_iff_of_deriv_nonpos` / 引理 `integrable_comp_mul_deriv_iff_of_deriv_nonpos`

English:
lemma integrable_comp_mul_deriv_iff_of_deriv_nonpos
  statement: {f f' g : Real -> Real} (hf : ContinuousOn f [[a, b]])
  proof: by
  simpa [mul_comm] using! integrable_deriv_smul_comp_iff_of_deriv_nonpos hf hff' hf'

中文:
引理 integrable_comp_mul_deriv_iff_of_deriv_nonpos
  结论: {f f' g : 实数 -> 实数} (hf : ContinuousOn f [[a, b]])
  证明: by
  simpa [mul_comm] using! integrable_deriv_smul_comp_iff_of_deriv_nonpos hf hff' hf'

Depends on / 依赖: integrable_deriv_smul_comp_iff_of_deriv_nonpos, mul_comm
-/
lemma integrable_comp_mul_deriv_iff_of_deriv_nonpos {f f' g : Real -> Real} (hf : ContinuousOn f [[a, b]])
    (hff' : forall x in Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hf' : forall x in Ioo (min a b) (max a b), f' x <= 0) :
    IntervalIntegrable (fun x => (g ∘ f) x * f' x) volume a b ↔
      IntervalIntegrable g volume (f a) (f b) := by
  simpa [mul_comm] using! integrable_deriv_smul_comp_iff_of_deriv_nonpos hf hff' hf'

/--
theorem `integral_deriv_comp_mul_deriv'` / 定理 `integral_deriv_comp_mul_deriv'`

English:
theorem integral_deriv_comp_mul_deriv'
  statement: {f f' g g' : Real -> Real} (hf : ContinuousOn f [[a, b]])
  proof: by
  simpa [mul_comm] using integral_deriv_smul_deriv_comp' hf hff' hf' hg hgg' hg'

中文:
定理 integral_deriv_comp_mul_deriv'
  结论: {f f' g g' : 实数 -> 实数} (hf : ContinuousOn f [[a, b]])
  证明: by
  simpa [mul_comm] using integral_deriv_smul_deriv_comp' hf hff' hf' hg hgg' hg'

Depends on / 依赖: integral_deriv_smul_deriv_comp, mul_comm
-/
theorem integral_deriv_comp_mul_deriv' {f f' g g' : Real -> Real} (hf : ContinuousOn f [[a, b]])
    (hff' : forall x in Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hf' : ContinuousOn f' [[a, b]]) (hg : ContinuousOn g [[f a, f b]])
    (hgg' : forall x in Ioo (min (f a) (f b)) (max (f a) (f b)), HasDerivWithinAt g (g' x) (Ioi x) x)
    (hg' : ContinuousOn g' (f '' [[a, b]])) :
    (∫ x in a..b, (g' ∘ f) x * f' x) = (g ∘ f) b - (g ∘ f) a := by
  simpa [mul_comm] using integral_deriv_smul_deriv_comp' hf hff' hf' hg hgg' hg'

/--
theorem `integral_deriv_comp_mul_deriv` / 定理 `integral_deriv_comp_mul_deriv`

English:
theorem integral_deriv_comp_mul_deriv
  statement: {f f' g g' : Real -> Real}
  proof: by
  simpa [mul_comm] using integral_deriv_smul_deriv_comp hf hg hf' hg'

中文:
定理 integral_deriv_comp_mul_deriv
  结论: {f f' g g' : 实数 -> 实数}
  证明: by
  simpa [mul_comm] using integral_deriv_smul_deriv_comp hf hg hf' hg'

Depends on / 依赖: integral_deriv_smul_deriv_comp, mul_comm
-/
theorem integral_deriv_comp_mul_deriv {f f' g g' : Real -> Real}
    (hf : forall x in uIcc a b, HasDerivAt f (f' x) x)
    (hg : forall x in uIcc a b, HasDerivAt g (g' (f x)) (f x)) (hf' : ContinuousOn f' (uIcc a b))
    (hg' : Continuous g') : (∫ x in a..b, (g' ∘ f) x * f' x) = (g ∘ f) b - (g ∘ f) a := by
  simpa [mul_comm] using integral_deriv_smul_deriv_comp hf hg hf' hg'

end Mul

end intervalIntegral
