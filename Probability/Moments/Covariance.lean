/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Notation

/-!
# Covariance

We define the covariance of two real-valued random variables.

## Main definitions

* `covariance`: covariance of two real-valued random variables, with notation `cov[X, Y; μ]`.
  `cov[X, Y; μ] = ∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ`.

## Main statements

* `covariance_self`: `cov[X, X; μ] = Var[X; μ]`

## Notation

* `cov[X, Y; μ] = covariance X Y μ`
* `cov[X, Y] = covariance X Y volume`

-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y Z T : Ω -> Real} {μ : Measure Ω}

/--
Definition of `covariance` / `covariance` 的定义

English:
definition covariance
  signature: (X Y : Ω -> Real) (μ : Measure Ω)
  body: ∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ

@[inherit_doc]
scoped notation "cov[" X ", " Y "; " μ "]" => ProbabilityTheory.covariance X Y μ

中文:
定义 covariance
  签名: (X Y : Ω -> 实数) (μ : Measure Ω)
  定义体: ∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ

@[inherit_doc]
scoped notation "cov[" X ", " Y "; " μ "]" => ProbabilityTheory.covariance X Y μ
-/
noncomputable def covariance (X Y : Ω -> Real) (μ : Measure Ω) : Real :=
  ∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ

@[inherit_doc]
scoped notation "cov[" X ", " Y "; " μ "]" => ProbabilityTheory.covariance X Y μ

/-- The covariance of the real-valued random variables `X` and `Y`
according to the volume measure. -/
scoped notation "cov[" X ", " Y "]" => cov[X, Y; MeasureTheory.MeasureSpace.volume]

/--
lemma `covariance_eq_sub` / 引理 `covariance_eq_sub`

English:
lemma covariance_eq_sub
  given: [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
  proof: by
   simp_rw [covariance, sub_mul, mul_sub]
   repeat rw [integral_sub]
   · simp_rw [integral_mul_const, integral_const_mul, integral_const, probReal_univ,
       one_smul]
     simp
.integrable (by simp) · exact hY.const_mul _
   · exact integrable_const _
   · exact hX.integrable_mul hY
.integra

中文:
引理 covariance_eq_sub
  条件: [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
  证明: by
   simp_rw [covariance, sub_mul, mul_sub]
   repeat rw [integral_sub]
   · simp_rw [integral_mul_const, integral_const_mul, integral_const, probReal_univ,
       one_smul]
     simp
.integrable (by simp) · exact hY.const_mul _
   · exact integrable_const _
   · exact hX.integrable_mul hY
.integra

Depends on / 依赖: const_mul, covariance, hX.integrable_mul, hX.mul_const, hY.const_mul, integrable, integrable_const, integrable_mul, integral_const, integral_const_mul, integral_mul_const, integral_sub, mul_const, mul_sub, one_smul, probReal_univ, repeat, simp_rw, sub_mul
-/
lemma covariance_eq_sub [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
     cov[X, Y; μ] = μ[X * Y] - μ[X] * μ[Y] := by
   simp_rw [covariance, sub_mul, mul_sub]
   repeat rw [integral_sub]
   · simp_rw [integral_mul_const, integral_const_mul, integral_const, probReal_univ,
       one_smul]
     simp
.integrable (by simp) · exact hY.const_mul _
   · exact integrable_const _
   · exact hX.integrable_mul hY
.integrable (by simp) · exact hX.mul_const _
   · exact (hX.integrable_mul hY).sub (hX.mul_const _ |>.integrable (by simp))
   · exact (hY.const_mul _ |>.integrable (by simp)).sub (integrable_const _)

/--
lemma `covariance_zero_left` / 引理 `covariance_zero_left`

English:
lemma covariance_zero_left
  statement: cov[0, Y; μ] = 0
  proof: by simp [covariance]

中文:
引理 covariance_zero_left
  结论: cov[0, Y; μ] = 0
  证明: by simp [covariance]
-/
@[simp] lemma covariance_zero_left : cov[0, Y; μ] = 0 := by simp [covariance]

/--
lemma `covariance_zero_right` / 引理 `covariance_zero_right`

English:
lemma covariance_zero_right
  statement: cov[X, 0; μ] = 0
  proof: by simp [covariance]

中文:
引理 covariance_zero_right
  结论: cov[X, 0; μ] = 0
  证明: by simp [covariance]
-/
@[simp] lemma covariance_zero_right : cov[X, 0; μ] = 0 := by simp [covariance]

/--
lemma `covariance_zero_measure` / 引理 `covariance_zero_measure`

English:
lemma covariance_zero_measure
  statement: cov[X, Y; (0 : Measure Ω)] = 0
  proof: by simp [covariance]

中文:
引理 covariance_zero_measure
  结论: cov[X, Y; (0 : Measure Ω)] = 0
  证明: by simp [covariance]
-/
@[simp] lemma covariance_zero_measure : cov[X, Y; (0 : Measure Ω)] = 0 := by simp [covariance]

variable (X Y) in
/--
lemma `covariance_comm` / 引理 `covariance_comm`

English:
lemma covariance_comm
  statement: cov[X, Y; μ] = cov[Y, X; μ]
  proof: by
  simp_rw [covariance]
  congr with x
  ring

@[simp]

中文:
引理 covariance_comm
  结论: cov[X, Y; μ] = cov[Y, X; μ]
  证明: by
  simp_rw [covariance]
  congr with x
  ring

@[simp]

Depends on / 依赖: covariance, simp_rw
-/
lemma covariance_comm : cov[X, Y; μ] = cov[Y, X; μ] := by
  simp_rw [covariance]
  congr with x
  ring

@[simp]
/--
lemma `covariance_const_left` / 引理 `covariance_const_left`

English:
lemma covariance_const_left
  given: [IsProbabilityMeasure μ] (c : Real)
  statement: cov[fun _ => c, Y; μ] = 0
  proof: by
  simp [covariance]

@[simp]

中文:
引理 covariance_const_left
  条件: [IsProbabilityMeasure μ] (c : 实数)
  结论: cov[fun _ => c, Y; μ] = 0
  证明: by
  simp [covariance]

@[simp]

Depends on / 依赖: covariance
-/
lemma covariance_const_left [IsProbabilityMeasure μ] (c : Real) : cov[fun _ => c, Y; μ] = 0 := by
  simp [covariance]

@[simp]
/--
lemma `covariance_const_right` / 引理 `covariance_const_right`

English:
lemma covariance_const_right
  given: [IsProbabilityMeasure μ] (c : Real)
  statement: cov[X, fun _ => c; μ] = 0
  proof: by
  simp [covariance]

@[simp]

中文:
引理 covariance_const_right
  条件: [IsProbabilityMeasure μ] (c : 实数)
  结论: cov[X, fun _ => c; μ] = 0
  证明: by
  simp [covariance]

@[simp]

Depends on / 依赖: covariance
-/
lemma covariance_const_right [IsProbabilityMeasure μ] (c : Real) : cov[X, fun _ => c; μ] = 0 := by
  simp [covariance]

@[simp]
/--
lemma `covariance_add_const_left` / 引理 `covariance_add_const_left`

English:
lemma covariance_add_const_left
  given: [IsProbabilityMeasure μ] (hX : Integrable X μ) (c : Real)
  proof: by
  simp_rw [covariance]
  congr with ω
  rw [integral_add hX (by fun_prop)]
  simp

@[simp]

中文:
引理 covariance_add_const_left
  条件: [IsProbabilityMeasure μ] (hX : 整数egrable X μ) (c : 实数)
  证明: by
  simp_rw [covariance]
  congr with ω
  rw [integral_add hX (by fun_prop)]
  simp

@[simp]

Depends on / 依赖: covariance, fun_prop, integral_add, simp_rw
-/
lemma covariance_add_const_left [IsProbabilityMeasure μ] (hX : Integrable X μ) (c : Real) :
    cov[fun ω => X ω + c, Y; μ] = cov[X, Y; μ] := by
  simp_rw [covariance]
  congr with ω
  rw [integral_add hX (by fun_prop)]
  simp

@[simp]
/--
lemma `covariance_const_add_left` / 引理 `covariance_const_add_left`

English:
lemma covariance_const_add_left
  given: [IsProbabilityMeasure μ] (hX : Integrable X μ) (c : Real)
  proof: by
  simp_rw [add_comm c]
  exact covariance_add_const_left hX c

@[simp]

中文:
引理 covariance_const_add_left
  条件: [IsProbabilityMeasure μ] (hX : 整数egrable X μ) (c : 实数)
  证明: by
  simp_rw [add_comm c]
  exact covariance_add_const_left hX c

@[simp]

Depends on / 依赖: add_comm, covariance_add_const_left, simp_rw
-/
lemma covariance_const_add_left [IsProbabilityMeasure μ] (hX : Integrable X μ) (c : Real) :
    cov[fun ω => c + X ω, Y; μ] = cov[X, Y; μ] := by
  simp_rw [add_comm c]
  exact covariance_add_const_left hX c

@[simp]
/--
lemma `covariance_add_const_right` / 引理 `covariance_add_const_right`

English:
lemma covariance_add_const_right
  given: [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : Real)
  proof: by
  rw [covariance_comm]; rw [covariance_add_const_left hY c]; rw [covariance_comm]

@[simp]

中文:
引理 covariance_add_const_right
  条件: [IsProbabilityMeasure μ] (hY : 整数egrable Y μ) (c : 实数)
  证明: by
  rw [covariance_comm]; rw [covariance_add_const_left hY c]; rw [covariance_comm]

@[simp]

Depends on / 依赖: covariance_add_const_left, covariance_comm
-/
lemma covariance_add_const_right [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : Real) :
    cov[X, fun ω => Y ω + c; μ] = cov[X, Y; μ] := by
  rw [covariance_comm]; rw [covariance_add_const_left hY c]; rw [covariance_comm]

@[simp]
/--
lemma `covariance_const_add_right` / 引理 `covariance_const_add_right`

English:
lemma covariance_const_add_right
  given: [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : Real)
  proof: by
  simp_rw [add_comm c]
  exact covariance_add_const_right hY c

中文:
引理 covariance_const_add_right
  条件: [IsProbabilityMeasure μ] (hY : 整数egrable Y μ) (c : 实数)
  证明: by
  simp_rw [add_comm c]
  exact covariance_add_const_right hY c

Depends on / 依赖: add_comm, covariance_add_const_right, simp_rw
-/
lemma covariance_const_add_right [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : Real) :
    cov[X, fun ω => c + Y ω; μ] = cov[X, Y; μ] := by
  simp_rw [add_comm c]
  exact covariance_add_const_right hY c

/--
lemma `covariance_add_left` / 引理 `covariance_add_left`

English:
lemma covariance_add_left
  statement: [IsFiniteMeasure μ]
  proof: by
  simp_rw [covariance, Pi.add_apply]
  rw [← integral_add]
  · congr with x
    rw [integral_add (hX.integrable (by simp)) (hY.integrable (by simp))]
    ring
  · exact (hX.sub (memLp_const _)).integrable_mul (hZ.sub (memLp_const _))
  · exact (hY.sub (memLp_const _)).integrable_mul (hZ.sub (memL

中文:
引理 covariance_add_left
  结论: [IsFiniteMeasure μ]
  证明: by
  simp_rw [covariance, Pi.add_apply]
  rw [← integral_add]
  · congr with x
    rw [integral_add (hX.integrable (by simp)) (hY.integrable (by simp))]
    ring
  · exact (hX.sub (memLp_const _)).integrable_mul (hZ.sub (memLp_const _))
  · exact (hY.sub (memLp_const _)).integrable_mul (hZ.sub (memL

Depends on / 依赖: Pi.add_apply, add_apply, covariance, hX.integrable, hX.sub, hY.integrable, hY.sub, hZ.sub, integrable, integrable_mul, integral_add, memLp_const, simp_rw
-/
lemma covariance_add_left [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X + Y, Z; μ] = cov[X, Z; μ] + cov[Y, Z; μ] := by
  simp_rw [covariance, Pi.add_apply]
  rw [← integral_add]
  · congr with x
    rw [integral_add (hX.integrable (by simp)) (hY.integrable (by simp))]
    ring
  · exact (hX.sub (memLp_const _)).integrable_mul (hZ.sub (memLp_const _))
  · exact (hY.sub (memLp_const _)).integrable_mul (hZ.sub (memLp_const _))

/--
lemma `covariance_add_right` / 引理 `covariance_add_right`

English:
lemma covariance_add_right
  statement: [IsFiniteMeasure μ]
  proof: by
  rw [covariance_comm]; rw [covariance_add_left hY hZ hX]; rw [covariance_comm X]; rw [covariance_comm Z]

中文:
引理 covariance_add_right
  结论: [IsFiniteMeasure μ]
  证明: by
  rw [covariance_comm]; rw [covariance_add_left hY hZ hX]; rw [covariance_comm X]; rw [covariance_comm Z]

Depends on / 依赖: covariance_add_left, covariance_comm
-/
lemma covariance_add_right [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X, Y + Z; μ] = cov[X, Y; μ] + cov[X, Z; μ] := by
  rw [covariance_comm]; rw [covariance_add_left hY hZ hX]; rw [covariance_comm X]; rw [covariance_comm Z]

/--
lemma `covariance_smul_left` / 引理 `covariance_smul_left`

English:
lemma covariance_smul_left
  given: (c : Real)
  statement: cov[c • X, Y; μ] = c * cov[X, Y; μ]
  proof: by
  simp_rw [covariance, Pi.smul_apply, smul_eq_mul, ← integral_const_mul, ← mul_assoc, mul_sub,
    integral_const_mul]

中文:
引理 covariance_smul_left
  条件: (c : 实数)
  结论: cov[c • X, Y; μ] = c * cov[X, Y; μ]
  证明: by
  simp_rw [covariance, Pi.smul_apply, smul_eq_mul, ← integral_const_mul, ← mul_assoc, mul_sub,
    integral_const_mul]

Depends on / 依赖: Pi.smul_apply, covariance, integral_const_mul, mul_assoc, mul_sub, simp_rw, smul_apply, smul_eq_mul
-/
lemma covariance_smul_left (c : Real) : cov[c • X, Y; μ] = c * cov[X, Y; μ] := by
  simp_rw [covariance, Pi.smul_apply, smul_eq_mul, ← integral_const_mul, ← mul_assoc, mul_sub,
    integral_const_mul]

/--
lemma `covariance_smul_right` / 引理 `covariance_smul_right`

English:
lemma covariance_smul_right
  given: (c : Real)
  statement: cov[X, c • Y; μ] = c * cov[X, Y; μ]
  proof: by
  rw [covariance_comm]; rw [covariance_smul_left]; rw [covariance_comm]

中文:
引理 covariance_smul_right
  条件: (c : 实数)
  结论: cov[X, c • Y; μ] = c * cov[X, Y; μ]
  证明: by
  rw [covariance_comm]; rw [covariance_smul_left]; rw [covariance_comm]

Depends on / 依赖: covariance_comm, covariance_smul_left
-/
lemma covariance_smul_right (c : Real) : cov[X, c • Y; μ] = c * cov[X, Y; μ] := by
  rw [covariance_comm]; rw [covariance_smul_left]; rw [covariance_comm]

/--
lemma `covariance_const_mul_left` / 引理 `covariance_const_mul_left`

English:
lemma covariance_const_mul_left
  given: (c : Real)
  statement: cov[fun ω => c * X ω, Y; μ] = c * cov[X, Y; μ]
  proof: covariance_smul_left c

中文:
引理 covariance_const_mul_left
  条件: (c : 实数)
  结论: cov[fun ω => c * X ω, Y; μ] = c * cov[X, Y; μ]
  证明: covariance_smul_left c

Depends on / 依赖: covariance_smul_left
-/
lemma covariance_const_mul_left (c : Real) : cov[fun ω => c * X ω, Y; μ] = c * cov[X, Y; μ] :=
  covariance_smul_left c

/--
lemma `covariance_const_mul_right` / 引理 `covariance_const_mul_right`

English:
lemma covariance_const_mul_right
  given: (c : Real)
  statement: cov[X, fun ω => c * Y ω; μ] = c * cov[X, Y; μ]
  proof: covariance_smul_right c

中文:
引理 covariance_const_mul_right
  条件: (c : 实数)
  结论: cov[X, fun ω => c * Y ω; μ] = c * cov[X, Y; μ]
  证明: covariance_smul_right c

Depends on / 依赖: covariance_smul_right
-/
lemma covariance_const_mul_right (c : Real) : cov[X, fun ω => c * Y ω; μ] = c * cov[X, Y; μ] :=
  covariance_smul_right c

/--
lemma `covariance_mul_const_left` / 引理 `covariance_mul_const_left`

English:
lemma covariance_mul_const_left
  given: (c : Real)
  statement: cov[fun ω => X ω * c, Y; μ] = cov[X, Y; μ] * c
  proof: by
  simp [mul_comm, covariance_const_mul_left]

中文:
引理 covariance_mul_const_left
  条件: (c : 实数)
  结论: cov[fun ω => X ω * c, Y; μ] = cov[X, Y; μ] * c
  证明: by
  simp [mul_comm, covariance_const_mul_left]

Depends on / 依赖: covariance_const_mul_left, mul_comm
-/
lemma covariance_mul_const_left (c : Real) : cov[fun ω => X ω * c, Y; μ] = cov[X, Y; μ] * c := by
  simp [mul_comm, covariance_const_mul_left]

/--
lemma `covariance_mul_const_right` / 引理 `covariance_mul_const_right`

English:
lemma covariance_mul_const_right
  given: (c : Real)
  statement: cov[X, fun ω => Y ω * c; μ] = cov[X, Y; μ] * c
  proof: by
  simp [mul_comm, covariance_const_mul_right]

中文:
引理 covariance_mul_const_right
  条件: (c : 实数)
  结论: cov[X, fun ω => Y ω * c; μ] = cov[X, Y; μ] * c
  证明: by
  simp [mul_comm, covariance_const_mul_right]

Depends on / 依赖: covariance_const_mul_right, mul_comm
-/
lemma covariance_mul_const_right (c : Real) : cov[X, fun ω => Y ω * c; μ] = cov[X, Y; μ] * c := by
  simp [mul_comm, covariance_const_mul_right]

/--
lemma `covariance_fun_div_left` / 引理 `covariance_fun_div_left`

English:
lemma covariance_fun_div_left
  given: (c : Real)
  proof: by
  simp_rw [← inv_mul_eq_div, covariance_const_mul_left]

中文:
引理 covariance_fun_div_left
  条件: (c : 实数)
  证明: by
  simp_rw [← inv_mul_eq_div, covariance_const_mul_left]

Depends on / 依赖: covariance_const_mul_left, inv_mul_eq_div, simp_rw
-/
lemma covariance_fun_div_left (c : Real) :
    cov[fun ω => X ω / c, Y; μ] = cov[X, Y; μ] / c := by
  simp_rw [← inv_mul_eq_div, covariance_const_mul_left]

/--
lemma `covariance_fun_div_right` / 引理 `covariance_fun_div_right`

English:
lemma covariance_fun_div_right
  given: (c : Real)
  proof: by
  simp_rw [← inv_mul_eq_div, covariance_const_mul_right]

@[simp]

中文:
引理 covariance_fun_div_right
  条件: (c : 实数)
  证明: by
  simp_rw [← inv_mul_eq_div, covariance_const_mul_right]

@[simp]

Depends on / 依赖: covariance_const_mul_right, inv_mul_eq_div, simp_rw
-/
lemma covariance_fun_div_right (c : Real) :
    cov[X, fun ω => Y ω / c; μ] = cov[X, Y; μ] / c := by
  simp_rw [← inv_mul_eq_div, covariance_const_mul_right]

@[simp]
/--
lemma `covariance_neg_left` / 引理 `covariance_neg_left`

English:
lemma covariance_neg_left
  statement: cov[-X, Y; μ] = -cov[X, Y; μ]
  proof: by
  calc cov[-X, Y; μ]
  _ = cov[(-1 : Real) • X, Y; μ] := by simp
  _ = -cov[X, Y; μ] := by rw [covariance_smul_left]; simp

@[simp]

中文:
引理 covariance_neg_left
  结论: cov[-X, Y; μ] = -cov[X, Y; μ]
  证明: by
  calc cov[-X, Y; μ]
  _ = cov[(-1 : Real) • X, Y; μ] := by simp
  _ = -cov[X, Y; μ] := by rw [covariance_smul_left]; simp

@[simp]

Depends on / 依赖: covariance_smul_left
-/
lemma covariance_neg_left : cov[-X, Y; μ] = -cov[X, Y; μ] := by
  calc cov[-X, Y; μ]
  _ = cov[(-1 : Real) • X, Y; μ] := by simp
  _ = -cov[X, Y; μ] := by rw [covariance_smul_left]; simp

@[simp]
/--
lemma `covariance_fun_neg_left` / 引理 `covariance_fun_neg_left`

English:
lemma covariance_fun_neg_left
  statement: cov[fun ω => -X ω, Y; μ] = -cov[X, Y; μ]
  proof: covariance_neg_left

@[simp]

中文:
引理 covariance_fun_neg_left
  结论: cov[fun ω => -X ω, Y; μ] = -cov[X, Y; μ]
  证明: covariance_neg_left

@[simp]

Depends on / 依赖: covariance_neg_left
-/
lemma covariance_fun_neg_left : cov[fun ω => -X ω, Y; μ] = -cov[X, Y; μ] :=
  covariance_neg_left

@[simp]
/--
lemma `covariance_neg_right` / 引理 `covariance_neg_right`

English:
lemma covariance_neg_right
  statement: cov[X, -Y; μ] = -cov[X, Y; μ]
  proof: by
  calc cov[X, -Y; μ]
  _ = cov[X, (-1 : Real) • Y; μ] := by simp
  _ = -cov[X, Y; μ] := by rw [covariance_smul_right]; simp

@[simp]

中文:
引理 covariance_neg_right
  结论: cov[X, -Y; μ] = -cov[X, Y; μ]
  证明: by
  calc cov[X, -Y; μ]
  _ = cov[X, (-1 : Real) • Y; μ] := by simp
  _ = -cov[X, Y; μ] := by rw [covariance_smul_right]; simp

@[simp]

Depends on / 依赖: covariance_smul_right
-/
lemma covariance_neg_right : cov[X, -Y; μ] = -cov[X, Y; μ] := by
  calc cov[X, -Y; μ]
  _ = cov[X, (-1 : Real) • Y; μ] := by simp
  _ = -cov[X, Y; μ] := by rw [covariance_smul_right]; simp

@[simp]
/--
lemma `covariance_fun_neg_right` / 引理 `covariance_fun_neg_right`

English:
lemma covariance_fun_neg_right
  statement: cov[X, fun ω => -Y ω; μ] = -cov[X, Y; μ]
  proof: covariance_neg_right

中文:
引理 covariance_fun_neg_right
  结论: cov[X, fun ω => -Y ω; μ] = -cov[X, Y; μ]
  证明: covariance_neg_right

Depends on / 依赖: covariance_neg_right
-/
lemma covariance_fun_neg_right : cov[X, fun ω => -Y ω; μ] = -cov[X, Y; μ] :=
  covariance_neg_right

/--
lemma `covariance_sub_left` / 引理 `covariance_sub_left`

English:
lemma covariance_sub_left
  statement: [IsFiniteMeasure μ]
  proof: by
  simp_rw [sub_eq_add_neg, covariance_add_left hX hY.neg hZ, covariance_neg_left]

中文:
引理 covariance_sub_left
  结论: [IsFiniteMeasure μ]
  证明: by
  simp_rw [sub_eq_add_neg, covariance_add_left hX hY.neg hZ, covariance_neg_left]

Depends on / 依赖: covariance_add_left, covariance_neg_left, hY.neg, simp_rw, sub_eq_add_neg
-/
lemma covariance_sub_left [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X - Y, Z; μ] = cov[X, Z; μ] - cov[Y, Z; μ] := by
  simp_rw [sub_eq_add_neg, covariance_add_left hX hY.neg hZ, covariance_neg_left]

/--
lemma `covariance_fun_sub_left` / 引理 `covariance_fun_sub_left`

English:
lemma covariance_fun_sub_left
  statement: [IsFiniteMeasure μ]
  proof: covariance_sub_left hX hY hZ

中文:
引理 covariance_fun_sub_left
  结论: [IsFiniteMeasure μ]
  证明: covariance_sub_left hX hY hZ

Depends on / 依赖: Algebra, Algebra.FormallySmooth.of_perfectField, FormallySmooth, covariance_sub_left, of_perfectField
-/
lemma covariance_fun_sub_left [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[fun ω => X ω - Y ω, Z; μ] = cov[X, Z; μ] - cov[Y, Z; μ] := covariance_sub_left hX hY hZ

/--
lemma `covariance_sub_right` / 引理 `covariance_sub_right`

English:
lemma covariance_sub_right
  statement: [IsFiniteMeasure μ]
  proof: by
  simp_rw [sub_eq_add_neg, covariance_add_right hX hY hZ.neg, covariance_neg_right]

中文:
引理 covariance_sub_right
  结论: [IsFiniteMeasure μ]
  证明: by
  simp_rw [sub_eq_add_neg, covariance_add_right hX hY hZ.neg, covariance_neg_right]

Depends on / 依赖: covariance_add_right, covariance_neg_right, hZ.neg, simp_rw, sub_eq_add_neg
-/
lemma covariance_sub_right [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X, Y - Z; μ] = cov[X, Y; μ] - cov[X, Z; μ] := by
  simp_rw [sub_eq_add_neg, covariance_add_right hX hY hZ.neg, covariance_neg_right]

/--
lemma `covariance_fun_sub_right` / 引理 `covariance_fun_sub_right`

English:
lemma covariance_fun_sub_right
  statement: [IsFiniteMeasure μ]
  proof: covariance_sub_right hX hY hZ

中文:
引理 covariance_fun_sub_right
  结论: [IsFiniteMeasure μ]
  证明: covariance_sub_right hX hY hZ

Depends on / 依赖: covariance_sub_right
-/
lemma covariance_fun_sub_right [IsFiniteMeasure μ]
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) :
    cov[X, fun ω => Y ω - Z ω; μ] = cov[X, Y; μ] - cov[X, Z; μ] := covariance_sub_right hX hY hZ

/--
lemma `covariance_sub_sub` / 引理 `covariance_sub_sub`

English:
lemma covariance_sub_sub
  statement: [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
  proof: by
  rw [covariance_sub_left hX hY (hZ.sub hT)]; rw [covariance_sub_right hX hZ hT]; rw [covariance_sub_right hY hZ hT]
  abel

中文:
引理 covariance_sub_sub
  结论: [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
  证明: by
  rw [covariance_sub_left hX hY (hZ.sub hT)]; rw [covariance_sub_right hX hZ hT]; rw [covariance_sub_right hY hZ hT]
  abel

Depends on / 依赖: covariance_sub_left, covariance_sub_right, hZ.sub
-/
lemma covariance_sub_sub [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hZ : MemLp Z 2 μ) (hT : MemLp T 2 μ) :
    cov[X - Y, Z - T; μ] = cov[X, Z; μ] - cov[X, T; μ] - cov[Y, Z; μ] + cov[Y, T; μ] := by
  rw [covariance_sub_left hX hY (hZ.sub hT)]; rw [covariance_sub_right hX hZ hT]; rw [covariance_sub_right hY hZ hT]
  abel

/--
lemma `covariance_fun_sub_fun_sub` / 引理 `covariance_fun_sub_fun_sub`

English:
lemma covariance_fun_sub_fun_sub
  statement: [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
  proof: covariance_sub_sub hX hY hZ hT

@[simp]

中文:
引理 covariance_fun_sub_fun_sub
  结论: [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
  证明: covariance_sub_sub hX hY hZ hT

@[simp]

Depends on / 依赖: covariance_sub_sub
-/
lemma covariance_fun_sub_fun_sub [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hZ : MemLp Z 2 μ) (hT : MemLp T 2 μ) :
    cov[fun ω => X ω - Y ω, fun ω => Z ω - T ω; μ] =
      cov[X, Z; μ] - cov[X, T; μ] - cov[Y, Z; μ] + cov[Y, T; μ] :=
  covariance_sub_sub hX hY hZ hT

@[simp]
/--
lemma `covariance_sub_const_left` / 引理 `covariance_sub_const_left`

English:
lemma covariance_sub_const_left
  given: [IsProbabilityMeasure μ] (hX : Integrable X μ) (c : Real)
  proof: by
  simp [sub_eq_add_neg, hX]

@[simp]

中文:
引理 covariance_sub_const_left
  条件: [IsProbabilityMeasure μ] (hX : 整数egrable X μ) (c : 实数)
  证明: by
  simp [sub_eq_add_neg, hX]

@[simp]

Depends on / 依赖: sub_eq_add_neg
-/
lemma covariance_sub_const_left [IsProbabilityMeasure μ] (hX : Integrable X μ) (c : Real) :
    cov[fun ω => X ω - c, Y; μ] = cov[X, Y; μ] := by
  simp [sub_eq_add_neg, hX]

@[simp]
/--
lemma `covariance_const_sub_left` / 引理 `covariance_const_sub_left`

English:
lemma covariance_const_sub_left
  given: [IsProbabilityMeasure μ] (hX : Integrable X μ) (c : Real)
  proof: by
  simp [sub_eq_add_neg, hX.fun_neg]

@[simp]

中文:
引理 covariance_const_sub_left
  条件: [IsProbabilityMeasure μ] (hX : 整数egrable X μ) (c : 实数)
  证明: by
  simp [sub_eq_add_neg, hX.fun_neg]

@[simp]

Depends on / 依赖: fun_neg, hX.fun_neg, sub_eq_add_neg
-/
lemma covariance_const_sub_left [IsProbabilityMeasure μ] (hX : Integrable X μ) (c : Real) :
    cov[fun ω => c - X ω, Y; μ] = -cov[X, Y; μ] := by
  simp [sub_eq_add_neg, hX.fun_neg]

@[simp]
/--
lemma `covariance_sub_const_right` / 引理 `covariance_sub_const_right`

English:
lemma covariance_sub_const_right
  given: [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : Real)
  proof: by
  simp [sub_eq_add_neg, hY]

@[simp]

中文:
引理 covariance_sub_const_right
  条件: [IsProbabilityMeasure μ] (hY : 整数egrable Y μ) (c : 实数)
  证明: by
  simp [sub_eq_add_neg, hY]

@[simp]

Depends on / 依赖: sub_eq_add_neg
-/
lemma covariance_sub_const_right [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : Real) :
    cov[X, fun ω => Y ω - c; μ] = cov[X, Y; μ] := by
  simp [sub_eq_add_neg, hY]

@[simp]
/--
lemma `covariance_const_sub_right` / 引理 `covariance_const_sub_right`

English:
lemma covariance_const_sub_right
  given: [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : Real)
  proof: by
  simp [sub_eq_add_neg, hY.fun_neg]

中文:
引理 covariance_const_sub_right
  条件: [IsProbabilityMeasure μ] (hY : 整数egrable Y μ) (c : 实数)
  证明: by
  simp [sub_eq_add_neg, hY.fun_neg]

Depends on / 依赖: fun_neg, hY.fun_neg, sub_eq_add_neg
-/
lemma covariance_const_sub_right [IsProbabilityMeasure μ] (hY : Integrable Y μ) (c : Real) :
    cov[X, fun ω => c - Y ω; μ] = -cov[X, Y; μ] := by
  simp [sub_eq_add_neg, hY.fun_neg]

section Sum

variable {ι : Type*} {X : ι -> Ω -> Real} {s : Finset ι} [IsFiniteMeasure μ]

/--
lemma `covariance_sum_left'` / 引理 `covariance_sum_left'`

English:
lemma covariance_sum_left'
  given: (hX : forall i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ)
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi h_ind =>
    rw [Finset.sum_insert hi]; rw [Finset.sum_insert hi]; rw [covariance_add_left]; rw [h_ind]
    · exact fun j hj => hX j (by simp [hj])
    · exact hX i (by simp)
    · exact memLp_finsetSum' s (

中文:
引理 covariance_sum_left'
  条件: (hX : 对任意 i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ)
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi h_ind =>
    rw [Finset.sum_insert hi]; rw [Finset.sum_insert hi]; rw [covariance_add_left]; rw [h_ind]
    · exact fun j hj => hX j (by simp [hj])
    · exact hX i (by simp)
    · exact memLp_finsetSum' s (

Depends on / 依赖: Finset, Finset.induction, Finset.sum_insert, classical, covariance_add_left, h_ind, insert, memLp_finsetSum, sum_insert
-/
lemma covariance_sum_left' (hX : forall i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[∑ i in s, X i, Y; μ] = ∑ i in s, cov[X i, Y; μ] := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi h_ind =>
    rw [Finset.sum_insert hi]; rw [Finset.sum_insert hi]; rw [covariance_add_left]; rw [h_ind]
    · exact fun j hj => hX j (by simp [hj])
    · exact hX i (by simp)
    · exact memLp_finsetSum' s (fun j hj => hX j (by simp [hj]))
    · exact hY

/--
lemma `covariance_sum_left` / 引理 `covariance_sum_left`

English:
lemma covariance_sum_left
  given: [Fintype ι] (hX : forall i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ)
  proof: covariance_sum_left' (fun _ _ => hX _) hY

中文:
引理 covariance_sum_left
  条件: [Fintype ι] (hX : 对任意 i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ)
  证明: covariance_sum_left' (fun _ _ => hX _) hY

Depends on / 依赖: covariance_sum_left
-/
lemma covariance_sum_left [Fintype ι] (hX : forall i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[∑ i, X i, Y; μ] = ∑ i, cov[X i, Y; μ] :=
  covariance_sum_left' (fun _ _ => hX _) hY

/--
lemma `covariance_fun_sum_left'` / 引理 `covariance_fun_sum_left'`

English:
lemma covariance_fun_sum_left'
  given: (hX : forall i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ)
  proof: by
  convert! covariance_sum_left' hX hY
  simp

中文:
引理 covariance_fun_sum_left'
  条件: (hX : 对任意 i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ)
  证明: by
  convert! covariance_sum_left' hX hY
  simp

Depends on / 依赖: convert, covariance_sum_left
-/
lemma covariance_fun_sum_left' (hX : forall i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[fun ω => ∑ i in s, X i ω, Y; μ] = ∑ i in s, cov[X i, Y; μ] := by
  convert! covariance_sum_left' hX hY
  simp

/--
lemma `covariance_fun_sum_left` / 引理 `covariance_fun_sum_left`

English:
lemma covariance_fun_sum_left
  given: [Fintype ι] (hX : forall i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ)
  proof: by
  convert! covariance_sum_left hX hY
  simp

中文:
引理 covariance_fun_sum_left
  条件: [Fintype ι] (hX : 对任意 i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ)
  证明: by
  convert! covariance_sum_left hX hY
  simp

Depends on / 依赖: convert, covariance_sum_left
-/
lemma covariance_fun_sum_left [Fintype ι] (hX : forall i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[fun ω => ∑ i, X i ω, Y; μ] = ∑ i, cov[X i, Y; μ] := by
  convert! covariance_sum_left hX hY
  simp

/--
lemma `covariance_sum_right'` / 引理 `covariance_sum_right'`

English:
lemma covariance_sum_right'
  given: (hX : forall i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ)
  proof: by
  rw [covariance_comm]; rw [covariance_sum_left' hX hY]
  simp_rw [covariance_comm]

中文:
引理 covariance_sum_right'
  条件: (hX : 对任意 i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ)
  证明: by
  rw [covariance_comm]; rw [covariance_sum_left' hX hY]
  simp_rw [covariance_comm]

Depends on / 依赖: covariance_comm, covariance_sum_left, simp_rw
-/
lemma covariance_sum_right' (hX : forall i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[Y, ∑ i in s, X i; μ] = ∑ i in s, cov[Y, X i; μ] := by
  rw [covariance_comm]; rw [covariance_sum_left' hX hY]
  simp_rw [covariance_comm]

/--
lemma `covariance_sum_right` / 引理 `covariance_sum_right`

English:
lemma covariance_sum_right
  given: [Fintype ι] (hX : forall i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ)
  proof: covariance_sum_right' (fun _ _ => hX _) hY

中文:
引理 covariance_sum_right
  条件: [Fintype ι] (hX : 对任意 i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ)
  证明: covariance_sum_right' (fun _ _ => hX _) hY

Depends on / 依赖: covariance_sum_right
-/
lemma covariance_sum_right [Fintype ι] (hX : forall i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[Y, ∑ i, X i; μ] = ∑ i, cov[Y, X i; μ] :=
  covariance_sum_right' (fun _ _ => hX _) hY

/--
lemma `covariance_fun_sum_right'` / 引理 `covariance_fun_sum_right'`

English:
lemma covariance_fun_sum_right'
  given: (hX : forall i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ)
  proof: by
  convert! covariance_sum_right' hX hY
  simp

中文:
引理 covariance_fun_sum_right'
  条件: (hX : 对任意 i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ)
  证明: by
  convert! covariance_sum_right' hX hY
  simp

Depends on / 依赖: convert, covariance_sum_right
-/
lemma covariance_fun_sum_right' (hX : forall i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[Y, fun ω => ∑ i in s, X i ω; μ] = ∑ i in s, cov[Y, X i; μ] := by
  convert! covariance_sum_right' hX hY
  simp

/--
lemma `covariance_fun_sum_right` / 引理 `covariance_fun_sum_right`

English:
lemma covariance_fun_sum_right
  given: [Fintype ι] (hX : forall i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ)
  proof: covariance_fun_sum_right' (fun _ _ => hX _) hY

中文:
引理 covariance_fun_sum_right
  条件: [Fintype ι] (hX : 对任意 i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ)
  证明: covariance_fun_sum_right' (fun _ _ => hX _) hY

Depends on / 依赖: covariance_fun_sum_right
-/
lemma covariance_fun_sum_right [Fintype ι] (hX : forall i, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) :
    cov[Y, fun ω => ∑ i, X i ω; μ] = ∑ i, cov[Y, X i; μ] :=
  covariance_fun_sum_right' (fun _ _ => hX _) hY

/--
lemma `covariance_sum_sum'` / 引理 `covariance_sum_sum'`

English:
lemma covariance_sum_sum'
  statement: {ι' : Type*} {Y : ι' -> Ω -> Real} {t : Finset ι'}
  proof: by
  rw [covariance_sum_left' hX]
  · exact Finset.sum_congr rfl fun i hi => by rw [covariance_sum_right' hY (hX i hi)]
  · exact memLp_finsetSum' t hY

中文:
引理 covariance_sum_sum'
  结论: {ι' : 类型} {Y : ι' -> Ω -> 实数} {t : Finset ι'}
  证明: by
  rw [covariance_sum_left' hX]
  · exact Finset.sum_congr rfl fun i hi => by rw [covariance_sum_right' hY (hX i hi)]
  · exact memLp_finsetSum' t hY

Depends on / 依赖: Finset, Finset.sum_congr, covariance_sum_left, covariance_sum_right, memLp_finsetSum, sum_congr
-/
lemma covariance_sum_sum' {ι' : Type*} {Y : ι' -> Ω -> Real} {t : Finset ι'}
    (hX : forall i in s, MemLp (X i) 2 μ) (hY : forall i in t, MemLp (Y i) 2 μ) :
    cov[∑ i in s, X i, ∑ j in t, Y j; μ] = ∑ i in s, ∑ j in t, cov[X i, Y j; μ] := by
  rw [covariance_sum_left' hX]
  · exact Finset.sum_congr rfl fun i hi => by rw [covariance_sum_right' hY (hX i hi)]
  · exact memLp_finsetSum' t hY

/--
lemma `covariance_sum_sum` / 引理 `covariance_sum_sum`

English:
lemma covariance_sum_sum
  statement: [Fintype ι] {ι' : Type*} [Fintype ι'] {Y : ι' -> Ω -> Real}
  proof: covariance_sum_sum' (fun _ _ => hX _) (fun _ _ => hY _)

中文:
引理 covariance_sum_sum
  结论: [Fintype ι] {ι' : 类型} [Fintype ι'] {Y : ι' -> Ω -> 实数}
  证明: covariance_sum_sum' (fun _ _ => hX _) (fun _ _ => hY _)

Depends on / 依赖: covariance_sum_sum
-/
lemma covariance_sum_sum [Fintype ι] {ι' : Type*} [Fintype ι'] {Y : ι' -> Ω -> Real}
    (hX : forall i, MemLp (X i) 2 μ) (hY : forall i, MemLp (Y i) 2 μ) :
    cov[∑ i, X i, ∑ j, Y j; μ] = ∑ i, ∑ j, cov[X i, Y j; μ] :=
  covariance_sum_sum' (fun _ _ => hX _) (fun _ _ => hY _)

/--
lemma `covariance_fun_sum_fun_sum'` / 引理 `covariance_fun_sum_fun_sum'`

English:
lemma covariance_fun_sum_fun_sum'
  statement: {ι' : Type*} {Y : ι' -> Ω -> Real} {t : Finset ι'}
  proof: by
  convert! covariance_sum_sum' hX hY
  all_goals simp

中文:
引理 covariance_fun_sum_fun_sum'
  结论: {ι' : 类型} {Y : ι' -> Ω -> 实数} {t : Finset ι'}
  证明: by
  convert! covariance_sum_sum' hX hY
  all_goals simp

Depends on / 依赖: all_goals, convert, covariance_sum_sum
-/
lemma covariance_fun_sum_fun_sum' {ι' : Type*} {Y : ι' -> Ω -> Real} {t : Finset ι'}
    (hX : forall i in s, MemLp (X i) 2 μ) (hY : forall i in t, MemLp (Y i) 2 μ) :
    cov[fun ω => ∑ i in s, X i ω, fun ω => ∑ j in t, Y j ω; μ]
      = ∑ i in s, ∑ j in t, cov[X i, Y j; μ] := by
  convert! covariance_sum_sum' hX hY
  all_goals simp

/--
lemma `covariance_fun_sum_fun_sum` / 引理 `covariance_fun_sum_fun_sum`

English:
lemma covariance_fun_sum_fun_sum
  statement: [Fintype ι] {ι' : Type*} [Fintype ι'] {Y : ι' -> Ω -> Real}
  proof: covariance_fun_sum_fun_sum' (fun _ _ => hX _) (fun _ _ => hY _)

中文:
引理 covariance_fun_sum_fun_sum
  结论: [Fintype ι] {ι' : 类型} [Fintype ι'] {Y : ι' -> Ω -> 实数}
  证明: covariance_fun_sum_fun_sum' (fun _ _ => hX _) (fun _ _ => hY _)

Depends on / 依赖: covariance_fun_sum_fun_sum
-/
lemma covariance_fun_sum_fun_sum [Fintype ι] {ι' : Type*} [Fintype ι'] {Y : ι' -> Ω -> Real}
    (hX : forall i, MemLp (X i) 2 μ) (hY : forall i, MemLp (Y i) 2 μ) :
    cov[fun ω => ∑ i, X i ω, fun ω => ∑ j, Y j ω; μ] = ∑ i, ∑ j, cov[X i, Y j; μ] :=
  covariance_fun_sum_fun_sum' (fun _ _ => hX _) (fun _ _ => hY _)

end Sum

section Map

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}

/--
lemma `covariance_map_equiv` / 引理 `covariance_map_equiv`

English:
lemma covariance_map_equiv
  given: (X Y : Ω -> Real) (Z : Ω' ≃ᵐ Ω)
  proof: by
  simp_rw [covariance, integral_map_equiv, Function.comp_apply]

中文:
引理 covariance_map_equiv
  条件: (X Y : Ω -> 实数) (Z : Ω' ≃ᵐ Ω)
  证明: by
  simp_rw [covariance, integral_map_equiv, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, covariance, integral_map_equiv, simp_rw
-/
lemma covariance_map_equiv (X Y : Ω -> Real) (Z : Ω' ≃ᵐ Ω) :
    cov[X, Y; μ.map Z] = cov[X ∘ Z, Y ∘ Z; μ] := by
  simp_rw [covariance, integral_map_equiv, Function.comp_apply]

/--
lemma `covariance_map` / 引理 `covariance_map`

English:
lemma covariance_map
  statement: {Z : Ω' -> Ω} (hX : AEStronglyMeasurable X (μ.map Z))
  proof: by
  simp_rw [covariance, Function.comp_apply]
  repeat rw [integral_map]
  any_goals assumption
  exact (hX.sub aestronglyMeasurable_const).mul (hY.sub aestronglyMeasurable_const)

中文:
引理 covariance_map
  结论: {Z : Ω' -> Ω} (hX : AEStronglyMeasurable X (μ.map Z))
  证明: by
  simp_rw [covariance, Function.comp_apply]
  repeat rw [integral_map]
  any_goals assumption
  exact (hX.sub aestronglyMeasurable_const).mul (hY.sub aestronglyMeasurable_const)

Depends on / 依赖: Function, Function.comp_apply, aestronglyMeasurable_const, any_goals, comp_apply, covariance, hX.sub, hY.sub, integral_map, repeat, simp_rw
-/
lemma covariance_map {Z : Ω' -> Ω} (hX : AEStronglyMeasurable X (μ.map Z))
    (hY : AEStronglyMeasurable Y (μ.map Z)) (hZ : AEMeasurable Z μ) :
    cov[X, Y; μ.map Z] = cov[X ∘ Z, Y ∘ Z; μ] := by
  simp_rw [covariance, Function.comp_apply]
  repeat rw [integral_map]
  any_goals assumption
  exact (hX.sub aestronglyMeasurable_const).mul (hY.sub aestronglyMeasurable_const)

/--
lemma `covariance_map_fun` / 引理 `covariance_map_fun`

English:
lemma covariance_map_fun
  statement: {Z : Ω' -> Ω} (hX : AEStronglyMeasurable X (μ.map Z))
  proof: covariance_map hX hY hZ

中文:
引理 covariance_map_fun
  结论: {Z : Ω' -> Ω} (hX : AEStronglyMeasurable X (μ.map Z))
  证明: covariance_map hX hY hZ

Depends on / 依赖: covariance_map
-/
lemma covariance_map_fun {Z : Ω' -> Ω} (hX : AEStronglyMeasurable X (μ.map Z))
    (hY : AEStronglyMeasurable Y (μ.map Z)) (hZ : AEMeasurable Z μ) :
    cov[X, Y; μ.map Z] = cov[fun ω => X (Z ω), fun ω => Y (Z ω); μ] :=
  covariance_map hX hY hZ

end Map

/--
lemma `IndepFun.covariance_eq_zero` / 引理 `IndepFun.covariance_eq_zero`

English:
lemma IndepFun.covariance_eq_zero
  given: (h : X ⟂ᵢ[μ] Y) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
  proof: by
   by_cases h' : forallᵐ ω ∂μ, X ω = 0
   · refine integral_eq_zero_of_ae ?_
     filter_upwards [h'] with ω hω
     simp [hω, integral_eq_zero_of_ae h']
   have := hX.isProbabilityMeasure_of_indepFun X Y (by simp) (by simp) h' h
   rw [covariance_eq_sub hX hY]; rw [h.integral_mul_eq_mul_integral

中文:
引理 IndepFun.covariance_eq_zero
  条件: (h : X ⟂ᵢ[μ] Y) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
  证明: by
   by_cases h' : forallᵐ ω ∂μ, X ω = 0
   · refine integral_eq_zero_of_ae ?_
     filter_upwards [h'] with ω hω
     simp [hω, integral_eq_zero_of_ae h']
   have := hX.isProbabilityMeasure_of_indepFun X Y (by simp) (by simp) h' h
   rw [covariance_eq_sub hX hY]; rw [h.integral_mul_eq_mul_integral

Depends on / 依赖: aestronglyMeasurable, covariance_eq_sub, filter_upwards, h.integral_mul_eq_mul_integral, hX.aestronglyMeasurable, hX.isProbabilityMeasure_of_indepFun, hY.aestronglyMeasurable, integral_eq_zero_of_ae, integral_mul_eq_mul_integral, isProbabilityMeasure_of_indepFun, sub_self
-/
lemma IndepFun.covariance_eq_zero (h : X ⟂ᵢ[μ] Y) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
     cov[X, Y; μ] = 0 := by
   by_cases h' : forallᵐ ω ∂μ, X ω = 0
   · refine integral_eq_zero_of_ae ?_
     filter_upwards [h'] with ω hω
     simp [hω, integral_eq_zero_of_ae h']
   have := hX.isProbabilityMeasure_of_indepFun X Y (by simp) (by simp) h' h
   rw [covariance_eq_sub hX hY]; rw [h.integral_mul_eq_mul_integral
       hX.aestronglyMeasurable hY.aestronglyMeasurable]; rw [sub_self]

section Prod

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {X : Ω -> Real} {Y : Ω' -> Real}

/--
lemma `covariance_fst_snd_prod` / 引理 `covariance_fst_snd_prod`

English:
lemma covariance_fst_snd_prod
  given: (hfμ : MemLp X 2 μ) (hgν : MemLp Y 2 ν)
  proof: (indepFun_prod₀ hfμ.aemeasurable hgν.aemeasurable).covariance_eq_zero
    (hfμ.comp_fst ν) (hgν.comp_snd μ)

中文:
引理 covariance_fst_snd_prod
  条件: (hfμ : MemLp X 2 μ) (hgν : MemLp Y 2 ν)
  证明: (indepFun_prod₀ hfμ.aemeasurable hgν.aemeasurable).covariance_eq_zero
    (hfμ.comp_fst ν) (hgν.comp_snd μ)

Depends on / 依赖: aemeasurable, comp_fst, comp_snd, covariance_eq_zero
-/
lemma covariance_fst_snd_prod (hfμ : MemLp X 2 μ) (hgν : MemLp Y 2 ν) :
    cov[fun p => X p.1, fun p => Y p.2; μ.prod ν] = 0 :=
  (indepFun_prod₀ hfμ.aemeasurable hgν.aemeasurable).covariance_eq_zero
    (hfμ.comp_fst ν) (hgν.comp_snd μ)

end Prod

end ProbabilityTheory
