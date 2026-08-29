/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Algebra.Field.NegOnePow
public import Mathlib.Algebra.Field.Periodic
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Trigonometric functions

## Main definitions

This file contains the definition of `π`.

See also `Analysis.SpecialFunctions.Trigonometric.Inverse` and
`Analysis.SpecialFunctions.Trigonometric.Arctan` for the inverse trigonometric functions.

See also `Analysis.SpecialFunctions.Complex.Arg` and
`Analysis.SpecialFunctions.Complex.Log` for the complex argument function
and the complex logarithm.

## Main statements

Many basic inequalities on the real trigonometric functions are established.

The continuity of the usual trigonometric functions is proved.

Several facts about the real trigonometric functions have the proofs deferred to
`Analysis.SpecialFunctions.Trigonometric.Complex`,
as they are most easily proved by appealing to the corresponding fact for
complex trigonometric functions.

See also `Analysis.SpecialFunctions.Trigonometric.Chebyshev` for the multiple angle formulas
in terms of Chebyshev polynomials.

## Tags

sin, cos, tan, angle
-/

@[expose] public section


noncomputable section

open Topology Filter Set

namespace Complex

@[continuity, fun_prop]
/--
theorem `continuous_sin` / 定理 `continuous_sin`

English:
theorem continuous_sin
  statement: Continuous sin
  proof: by
  change Continuous fun z => (exp (-z * I) - exp (z * I)) * I / 2
  fun_prop

@[fun_prop]

中文:
定理 continuous_sin
  结论: Continuous sin
  证明: by
  change Continuous fun z => (exp (-z * I) - exp (z * I)) * I / 2
  fun_prop

@[fun_prop]

Depends on / 依赖: Continuous, fun_prop
-/
theorem continuous_sin : Continuous sin := by
  change Continuous fun z => (exp (-z * I) - exp (z * I)) * I / 2
  fun_prop

@[fun_prop]
/--
theorem `continuousOn_sin` / 定理 `continuousOn_sin`

English:
theorem continuousOn_sin
  given: {s : Set Complex}
  statement: ContinuousOn sin s
  proof: continuous_sin.continuousOn

@[continuity, fun_prop]

中文:
定理 continuousOn_sin
  条件: {s : Set Complex}
  结论: ContinuousOn sin s
  证明: continuous_sin.continuousOn

@[continuity, fun_prop]

Depends on / 依赖: continuousOn, continuous_sin, continuous_sin.continuousOn
-/
theorem continuousOn_sin {s : Set Complex} : ContinuousOn sin s :=
  continuous_sin.continuousOn

@[continuity, fun_prop]
/--
theorem `continuous_cos` / 定理 `continuous_cos`

English:
theorem continuous_cos
  statement: Continuous cos
  proof: by
  change Continuous fun z => (exp (z * I) + exp (-z * I)) / 2
  fun_prop

@[fun_prop]

中文:
定理 continuous_cos
  结论: Continuous cos
  证明: by
  change Continuous fun z => (exp (z * I) + exp (-z * I)) / 2
  fun_prop

@[fun_prop]

Depends on / 依赖: Continuous, fun_prop
-/
theorem continuous_cos : Continuous cos := by
  change Continuous fun z => (exp (z * I) + exp (-z * I)) / 2
  fun_prop

@[fun_prop]
/--
theorem `continuousOn_cos` / 定理 `continuousOn_cos`

English:
theorem continuousOn_cos
  given: {s : Set Complex}
  statement: ContinuousOn cos s
  proof: continuous_cos.continuousOn

@[continuity, fun_prop]

中文:
定理 continuousOn_cos
  条件: {s : Set Complex}
  结论: ContinuousOn cos s
  证明: continuous_cos.continuousOn

@[continuity, fun_prop]

Depends on / 依赖: continuousOn, continuous_cos, continuous_cos.continuousOn
-/
theorem continuousOn_cos {s : Set Complex} : ContinuousOn cos s :=
  continuous_cos.continuousOn

@[continuity, fun_prop]
/--
theorem `continuous_sinh` / 定理 `continuous_sinh`

English:
theorem continuous_sinh
  statement: Continuous sinh
  proof: by
  change Continuous fun z => (exp z - exp (-z)) / 2
  fun_prop

@[continuity, fun_prop]

中文:
定理 continuous_sinh
  结论: Continuous sinh
  证明: by
  change Continuous fun z => (exp z - exp (-z)) / 2
  fun_prop

@[continuity, fun_prop]

Depends on / 依赖: Continuous, fun_prop
-/
theorem continuous_sinh : Continuous sinh := by
  change Continuous fun z => (exp z - exp (-z)) / 2
  fun_prop

@[continuity, fun_prop]
/--
theorem `continuous_cosh` / 定理 `continuous_cosh`

English:
theorem continuous_cosh
  statement: Continuous cosh
  proof: by
  change Continuous fun z => (exp z + exp (-z)) / 2
  fun_prop

中文:
定理 continuous_cosh
  结论: Continuous cosh
  证明: by
  change Continuous fun z => (exp z + exp (-z)) / 2
  fun_prop

Depends on / 依赖: Continuous, fun_prop
-/
theorem continuous_cosh : Continuous cosh := by
  change Continuous fun z => (exp z + exp (-z)) / 2
  fun_prop

end Complex

namespace Real

variable {x y z : Real}

@[continuity, fun_prop]
/--
theorem `continuous_sin` / 定理 `continuous_sin`

English:
theorem continuous_sin
  statement: Continuous sin
  proof: Complex.continuous_re.comp (Complex.continuous_sin.comp Complex.continuous_ofReal)

@[fun_prop]

中文:
定理 continuous_sin
  结论: Continuous sin
  证明: Complex.continuous_re.comp (Complex.continuous_sin.comp Complex.continuous_ofReal)

@[fun_prop]

Depends on / 依赖: Complex.continuous_ofReal, Complex.continuous_re.comp, Complex.continuous_sin.comp, continuous_ofReal, continuous_re, continuous_sin
-/
theorem continuous_sin : Continuous sin :=
  Complex.continuous_re.comp (Complex.continuous_sin.comp Complex.continuous_ofReal)

@[fun_prop]
/--
theorem `continuousOn_sin` / 定理 `continuousOn_sin`

English:
theorem continuousOn_sin
  given: {s}
  statement: ContinuousOn sin s
  proof: continuous_sin.continuousOn

@[continuity, fun_prop]

中文:
定理 continuousOn_sin
  条件: {s}
  结论: ContinuousOn sin s
  证明: continuous_sin.continuousOn

@[continuity, fun_prop]

Depends on / 依赖: continuousOn, continuous_sin, continuous_sin.continuousOn
-/
theorem continuousOn_sin {s} : ContinuousOn sin s :=
  continuous_sin.continuousOn

@[continuity, fun_prop]
/--
theorem `continuous_cos` / 定理 `continuous_cos`

English:
theorem continuous_cos
  statement: Continuous cos
  proof: Complex.continuous_re.comp (Complex.continuous_cos.comp Complex.continuous_ofReal)

@[fun_prop]

中文:
定理 continuous_cos
  结论: Continuous cos
  证明: Complex.continuous_re.comp (Complex.continuous_cos.comp Complex.continuous_ofReal)

@[fun_prop]

Depends on / 依赖: Complex.continuous_cos.comp, Complex.continuous_ofReal, Complex.continuous_re.comp, continuous_cos, continuous_ofReal, continuous_re
-/
theorem continuous_cos : Continuous cos :=
  Complex.continuous_re.comp (Complex.continuous_cos.comp Complex.continuous_ofReal)

@[fun_prop]
/--
theorem `continuousOn_cos` / 定理 `continuousOn_cos`

English:
theorem continuousOn_cos
  given: {s}
  statement: ContinuousOn cos s
  proof: continuous_cos.continuousOn

@[continuity, fun_prop]

中文:
定理 continuousOn_cos
  条件: {s}
  结论: ContinuousOn cos s
  证明: continuous_cos.continuousOn

@[continuity, fun_prop]

Depends on / 依赖: Faithful, StructuredArrow, StructuredArrow.pre, continuousOn, continuous_cos, continuous_cos.continuousOn
-/
theorem continuousOn_cos {s} : ContinuousOn cos s :=
  continuous_cos.continuousOn

@[continuity, fun_prop]
/--
theorem `continuous_sinh` / 定理 `continuous_sinh`

English:
theorem continuous_sinh
  statement: Continuous sinh
  proof: Complex.continuous_re.comp (Complex.continuous_sinh.comp Complex.continuous_ofReal)

@[continuity, fun_prop]

中文:
定理 continuous_sinh
  结论: Continuous sinh
  证明: Complex.continuous_re.comp (Complex.continuous_sinh.comp Complex.continuous_ofReal)

@[continuity, fun_prop]

Depends on / 依赖: Complex.continuous_ofReal, Complex.continuous_re.comp, Complex.continuous_sinh.comp, StructuredArrow, StructuredArrow.pre, continuous_ofReal, continuous_re, continuous_sinh
-/
theorem continuous_sinh : Continuous sinh :=
  Complex.continuous_re.comp (Complex.continuous_sinh.comp Complex.continuous_ofReal)

@[continuity, fun_prop]
/--
theorem `continuous_cosh` / 定理 `continuous_cosh`

English:
theorem continuous_cosh
  statement: Continuous cosh
  proof: Complex.continuous_re.comp (Complex.continuous_cosh.comp Complex.continuous_ofReal)

中文:
定理 continuous_cosh
  结论: Continuous cosh
  证明: Complex.continuous_re.comp (Complex.continuous_cosh.comp Complex.continuous_ofReal)

Depends on / 依赖: Complex.continuous_cosh.comp, Complex.continuous_ofReal, Complex.continuous_re.comp, EssSurj, StructuredArrow, StructuredArrow.pre, continuous_cosh, continuous_ofReal, continuous_re
-/
theorem continuous_cosh : Continuous cosh :=
  Complex.continuous_re.comp (Complex.continuous_cosh.comp Complex.continuous_ofReal)

end Real

namespace Real

/--
theorem `exists_cos_eq_zero` / 定理 `exists_cos_eq_zero`

English:
theorem exists_cos_eq_zero
  statement: 0 in cos '' Icc (1 : Real) 2
  proof: intermediate_value_Icc' (by simp) continuousOn_cos
    ⟨le_of_lt cos_two_neg, le_of_lt cos_one_pos⟩

中文:
定理 exists_cos_eq_zero
  结论: 0 in cos '' Icc (1 : 实数) 2
  证明: intermediate_value_Icc' (by simp) continuousOn_cos
    ⟨le_of_lt cos_two_neg, le_of_lt cos_one_pos⟩

Depends on / 依赖: continuousOn_cos, cos_one_pos, cos_two_neg, intermediate_value_Icc, le_of_lt
-/
theorem exists_cos_eq_zero : 0 in cos '' Icc (1 : Real) 2 :=
  intermediate_value_Icc' (by simp) continuousOn_cos
    ⟨le_of_lt cos_two_neg, le_of_lt cos_one_pos⟩

/-- The number π = 3.14159265... Defined here using choice as twice a zero of cos in [1,2],
from which one can derive all its properties. For explicit bounds on π,
see `Mathlib/Analysis/Real/Pi/Bounds.lean`.

Denoted `π`, once the `Real` namespace is opened. -/
@[wikidata Q167]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def pi
  body: 2 * Classical.choose exists_cos_eq_zero

@[inherit_doc]
scoped notation "π" => Real.pi

@[simp]

中文:
定义 noncomputable
  签名: def pi
  定义体: 2 * Classical.choose exists_cos_eq_zero

@[inherit_doc]
scoped notation "π" => Real.pi

@[simp]
-/
protected noncomputable def pi : Real :=
  2 * Classical.choose exists_cos_eq_zero

@[inherit_doc]
scoped notation "π" => Real.pi

@[simp]
/--
theorem `cos_pi_div_two` / 定理 `cos_pi_div_two`

English:
theorem cos_pi_div_two
  statement: cos (π / 2) = 0
  proof: by
  rw [Real.pi]; rw [mul_div_cancel_left₀ _ two_ne_zero]
  exact (Classical.choose_spec exists_cos_eq_zero).2

中文:
定理 cos_pi_div_two
  结论: cos (π / 2) = 0
  证明: by
  rw [Real.pi]; rw [mul_div_cancel_left₀ _ two_ne_zero]
  exact (Classical.choose_spec exists_cos_eq_zero).2

Depends on / 依赖: Classical, Classical.choose_spec, Real.pi, choose_spec, exists_cos_eq_zero, two_ne_zero
-/
theorem cos_pi_div_two : cos (π / 2) = 0 := by
  rw [Real.pi]; rw [mul_div_cancel_left₀ _ two_ne_zero]
  exact (Classical.choose_spec exists_cos_eq_zero).2

/--
theorem `one_le_pi_div_two` / 定理 `one_le_pi_div_two`

English:
theorem one_le_pi_div_two
  statement: (1 : Real) <= π / 2
  proof: by
  rw [Real.pi]; rw [mul_div_cancel_left₀ _ two_ne_zero]
  exact (Classical.choose_spec exists_cos_eq_zero).1.1

中文:
定理 one_le_pi_div_two
  结论: (1 : 实数) <= π / 2
  证明: by
  rw [Real.pi]; rw [mul_div_cancel_left₀ _ two_ne_zero]
  exact (Classical.choose_spec exists_cos_eq_zero).1.1

Depends on / 依赖: Classical, Classical.choose_spec, Real.pi, choose_spec, exists_cos_eq_zero, two_ne_zero
-/
theorem one_le_pi_div_two : (1 : Real) <= π / 2 := by
  rw [Real.pi]; rw [mul_div_cancel_left₀ _ two_ne_zero]
  exact (Classical.choose_spec exists_cos_eq_zero).1.1

/--
theorem `pi_div_two_le_two` / 定理 `pi_div_two_le_two`

English:
theorem pi_div_two_le_two
  statement: π / 2 <= 2
  proof: by
  rw [Real.pi]; rw [mul_div_cancel_left₀ _ two_ne_zero]
  exact (Classical.choose_spec exists_cos_eq_zero).1.2

中文:
定理 pi_div_two_le_two
  结论: π / 2 <= 2
  证明: by
  rw [Real.pi]; rw [mul_div_cancel_left₀ _ two_ne_zero]
  exact (Classical.choose_spec exists_cos_eq_zero).1.2

Depends on / 依赖: Classical, Classical.choose_spec, Real.pi, choose_spec, exists_cos_eq_zero, two_ne_zero
-/
theorem pi_div_two_le_two : π / 2 <= 2 := by
  rw [Real.pi]; rw [mul_div_cancel_left₀ _ two_ne_zero]
  exact (Classical.choose_spec exists_cos_eq_zero).1.2

/--
theorem `two_le_pi` / 定理 `two_le_pi`

English:
theorem two_le_pi
  statement: (2 : Real) <= π
  proof: (div_le_div_iff_of_pos_right zero_lt_two).1
    (by rw [div_self two_ne_zero]; exact one_le_pi_div_two)

中文:
定理 two_le_pi
  结论: (2 : 实数) <= π
  证明: (div_le_div_iff_of_pos_right zero_lt_two).1
    (by rw [div_self two_ne_zero]; exact one_le_pi_div_two)

Depends on / 依赖: div_le_div_iff_of_pos_right, div_self, one_le_pi_div_two, two_ne_zero, zero_lt_two
-/
theorem two_le_pi : (2 : Real) <= π :=
  (div_le_div_iff_of_pos_right zero_lt_two).1
    (by rw [div_self two_ne_zero]; exact one_le_pi_div_two)

/--
theorem `pi_le_four` / 定理 `pi_le_four`

English:
theorem pi_le_four
  statement: π <= 4
  proof: (div_le_div_iff_of_pos_right zero_lt_two).1
    (calc
      π / 2 <= 2 := pi_div_two_le_two
      _ = 4 / 2 := by norm_num)

@[bound]

中文:
定理 pi_le_four
  结论: π <= 4
  证明: (div_le_div_iff_of_pos_right zero_lt_two).1
    (calc
      π / 2 <= 2 := pi_div_two_le_two
      _ = 4 / 2 := by norm_num)

@[bound]

Depends on / 依赖: div_le_div_iff_of_pos_right, pi_div_two_le_two, zero_lt_two
-/
theorem pi_le_four : π <= 4 :=
  (div_le_div_iff_of_pos_right zero_lt_two).1
    (calc
      π / 2 <= 2 := pi_div_two_le_two
      _ = 4 / 2 := by norm_num)

@[bound]
/--
theorem `pi_pos` / 定理 `pi_pos`

English:
theorem pi_pos
  statement: 0 < π
  proof: lt_of_lt_of_le (by simp) two_le_pi

@[bound]

中文:
定理 pi_pos
  结论: 0 < π
  证明: lt_of_lt_of_le (by simp) two_le_pi

@[bound]

Depends on / 依赖: lt_of_lt_of_le, two_le_pi
-/
theorem pi_pos : 0 < π :=
  lt_of_lt_of_le (by simp) two_le_pi

@[bound]
/--
theorem `pi_nonneg` / 定理 `pi_nonneg`

English:
theorem pi_nonneg
  statement: 0 <= π
  proof: pi_pos.le

@[simp]

中文:
定理 pi_nonneg
  结论: 0 <= π
  证明: pi_pos.le

@[simp]

Depends on / 依赖: pi_pos, pi_pos.le
-/
theorem pi_nonneg : 0 <= π :=
  pi_pos.le

@[simp]
/--
theorem `pi_ne_zero` / 定理 `pi_ne_zero`

English:
theorem pi_ne_zero
  statement: π != 0
  proof: pi_pos.ne'

中文:
定理 pi_ne_zero
  结论: π != 0
  证明: pi_pos.ne'

Depends on / 依赖: pi_pos, pi_pos.ne
-/
theorem pi_ne_zero : π != 0 :=
  pi_pos.ne'

/--
theorem `pi_div_two_pos` / 定理 `pi_div_two_pos`

English:
theorem pi_div_two_pos
  statement: 0 < π / 2
  proof: half_pos pi_pos

中文:
定理 pi_div_two_pos
  结论: 0 < π / 2
  证明: half_pos pi_pos

Depends on / 依赖: half_pos, pi_pos
-/
theorem pi_div_two_pos : 0 < π / 2 :=
  half_pos pi_pos

/--
theorem `two_pi_pos` / 定理 `two_pi_pos`

English:
theorem two_pi_pos
  statement: 0 < 2 * π
  proof: by linarith [pi_pos]

中文:
定理 two_pi_pos
  结论: 0 < 2 * π
  证明: by linarith [pi_pos]

Depends on / 依赖: pi_pos
-/
theorem two_pi_pos : 0 < 2 * π := by linarith [pi_pos]

end Real

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `π` is always positive. -/
@[positivity Real.pi]
meta def evalRealPi : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(Real.pi) =>
    assertInstancesCommute
    pure (.positive q(Real.pi_pos))
  | _, _, _ => throwError "not Real.pi"

end Mathlib.Meta.Positivity

namespace NNReal

open Real

open Real NNReal

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: : Real>=0
  body: ⟨π, Real.pi_pos.le⟩

@[simp]

中文:
定义 pi
  签名: : 实数>=0
  定义体: ⟨π, Real.pi_pos.le⟩

@[simp]

Depends on / 依赖: Real.pi_pos.le, pi_pos
-/
noncomputable def pi : Real>=0 :=
  ⟨π, Real.pi_pos.le⟩

@[simp]
/--
theorem `coe_real_pi` / 定理 `coe_real_pi`

English:
theorem coe_real_pi
  statement: (pi : Real) = π
  proof: rfl

中文:
定理 coe_real_pi
  结论: (pi : 实数) = π
  证明: rfl
-/
theorem coe_real_pi : (pi : Real) = π :=
  rfl

/--
theorem `pi_pos` / 定理 `pi_pos`

English:
theorem pi_pos
  statement: 0 < pi
  proof: mod_cast Real.pi_pos

中文:
定理 pi_pos
  结论: 0 < pi
  证明: mod_cast Real.pi_pos

Depends on / 依赖: Real.pi_pos, mod_cast, pi_pos
-/
theorem pi_pos : 0 < pi := mod_cast Real.pi_pos

/--
theorem `pi_ne_zero` / 定理 `pi_ne_zero`

English:
theorem pi_ne_zero
  statement: pi != 0
  proof: pi_pos.ne'

中文:
定理 pi_ne_zero
  结论: pi != 0
  证明: pi_pos.ne'

Depends on / 依赖: pi_pos, pi_pos.ne
-/
theorem pi_ne_zero : pi != 0 :=
  pi_pos.ne'

end NNReal

namespace Real

@[simp]
/--
theorem `sin_pi` / 定理 `sin_pi`

English:
theorem sin_pi
  statement: sin π = 0
  proof: by
  rw [← mul_div_cancel_left₀ π two_ne_zero]; rw [two_mul]; rw [add_div]; rw [sin_add]; rw [cos_pi_div_two]; simp

@[simp]

中文:
定理 sin_pi
  结论: sin π = 0
  证明: by
  rw [← mul_div_cancel_left₀ π two_ne_zero]; rw [two_mul]; rw [add_div]; rw [sin_add]; rw [cos_pi_div_two]; simp

@[simp]

Depends on / 依赖: add_div, cos_pi_div_two, sin_add, two_mul, two_ne_zero
-/
theorem sin_pi : sin π = 0 := by
  rw [← mul_div_cancel_left₀ π two_ne_zero]; rw [two_mul]; rw [add_div]; rw [sin_add]; rw [cos_pi_div_two]; simp

@[simp]
/--
theorem `cos_pi` / 定理 `cos_pi`

English:
theorem cos_pi
  statement: cos π = -1
  proof: by
  rw [← mul_div_cancel_left₀ π two_ne_zero]; rw [mul_div_assoc]; rw [cos_two_mul]; rw [cos_pi_div_two]
  norm_num

@[simp]

中文:
定理 cos_pi
  结论: cos π = -1
  证明: by
  rw [← mul_div_cancel_left₀ π two_ne_zero]; rw [mul_div_assoc]; rw [cos_two_mul]; rw [cos_pi_div_two]
  norm_num

@[simp]

Depends on / 依赖: cos_pi_div_two, cos_two_mul, mul_div_assoc, two_ne_zero
-/
theorem cos_pi : cos π = -1 := by
  rw [← mul_div_cancel_left₀ π two_ne_zero]; rw [mul_div_assoc]; rw [cos_two_mul]; rw [cos_pi_div_two]
  norm_num

@[simp]
/--
theorem `sin_two_pi` / 定理 `sin_two_pi`

English:
theorem sin_two_pi
  statement: sin (2 * π) = 0
  proof: by simp [two_mul, sin_add]

@[simp]

中文:
定理 sin_two_pi
  结论: sin (2 * π) = 0
  证明: by simp [two_mul, sin_add]

@[simp]

Depends on / 依赖: sin_add, two_mul
-/
theorem sin_two_pi : sin (2 * π) = 0 := by simp [two_mul, sin_add]

@[simp]
/--
theorem `cos_two_pi` / 定理 `cos_two_pi`

English:
theorem cos_two_pi
  statement: cos (2 * π) = 1
  proof: by simp [two_mul, cos_add]

中文:
定理 cos_two_pi
  结论: cos (2 * π) = 1
  证明: by simp [two_mul, cos_add]

Depends on / 依赖: cos_add, two_mul
-/
theorem cos_two_pi : cos (2 * π) = 1 := by simp [two_mul, cos_add]

/--
theorem `sin_antiperiodic` / 定理 `sin_antiperiodic`

English:
theorem sin_antiperiodic
  statement: Function.Antiperiodic sin π
  proof: by simp [sin_add]

中文:
定理 sin_antiperiodic
  结论: Function.Antiperiodic sin π
  证明: by simp [sin_add]

Depends on / 依赖: sin_add
-/
theorem sin_antiperiodic : Function.Antiperiodic sin π := by simp [sin_add]

/--
theorem `sin_periodic` / 定理 `sin_periodic`

English:
theorem sin_periodic
  statement: Function.Periodic sin (2 * π)
  proof: sin_antiperiodic.periodic_two_mul

@[simp]

中文:
定理 sin_periodic
  结论: Function.Periodic sin (2 * π)
  证明: sin_antiperiodic.periodic_two_mul

@[simp]

Depends on / 依赖: periodic_two_mul, sin_antiperiodic, sin_antiperiodic.periodic_two_mul
-/
theorem sin_periodic : Function.Periodic sin (2 * π) :=
  sin_antiperiodic.periodic_two_mul

@[simp]
/--
theorem `sin_add_pi` / 定理 `sin_add_pi`

English:
theorem sin_add_pi
  given: (x : Real)
  statement: sin (x + π) = -sin x
  proof: sin_antiperiodic x

@[simp]

中文:
定理 sin_add_pi
  条件: (x : 实数)
  结论: sin (x + π) = -sin x
  证明: sin_antiperiodic x

@[simp]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, Functor, Functor.toCostructuredArrow, Functor.toOver, cat_disch, f.hom, g.hom, sin_antiperiodic, toCostructuredArrow, toOver
-/
theorem sin_add_pi (x : Real) : sin (x + π) = -sin x :=
  sin_antiperiodic x

@[simp]
/--
theorem `sin_add_two_pi` / 定理 `sin_add_two_pi`

English:
theorem sin_add_two_pi
  given: (x : Real)
  statement: sin (x + 2 * π) = sin x
  proof: sin_periodic x

@[simp]

中文:
定理 sin_add_two_pi
  条件: (x : 实数)
  结论: sin (x + 2 * π) = sin x
  证明: sin_periodic x

@[simp]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, Functor, Functor.toCostructuredArrow, Over.forget, cat_disch, f.hom, f.left.hom, forget, sin_periodic, toCostructuredArrow
-/
theorem sin_add_two_pi (x : Real) : sin (x + 2 * π) = sin x :=
  sin_periodic x

@[simp]
/--
theorem `sin_sub_pi` / 定理 `sin_sub_pi`

English:
theorem sin_sub_pi
  given: (x : Real)
  statement: sin (x - π) = -sin x
  proof: sin_antiperiodic.sub_eq x

@[simp]

中文:
定理 sin_sub_pi
  条件: (x : 实数)
  结论: sin (x - π) = -sin x
  证明: sin_antiperiodic.sub_eq x

@[simp]

Depends on / 依赖: sin_antiperiodic, sin_antiperiodic.sub_eq, sub_eq
-/
theorem sin_sub_pi (x : Real) : sin (x - π) = -sin x :=
  sin_antiperiodic.sub_eq x

@[simp]
/--
theorem `sin_sub_two_pi` / 定理 `sin_sub_two_pi`

English:
theorem sin_sub_two_pi
  given: (x : Real)
  statement: sin (x - 2 * π) = sin x
  proof: sin_periodic.sub_eq x

@[simp]

中文:
定理 sin_sub_two_pi
  条件: (x : 实数)
  结论: sin (x - 2 * π) = sin x
  证明: sin_periodic.sub_eq x

@[simp]

Depends on / 依赖: sin_periodic, sin_periodic.sub_eq, sub_eq
-/
theorem sin_sub_two_pi (x : Real) : sin (x - 2 * π) = sin x :=
  sin_periodic.sub_eq x

@[simp]
/--
theorem `sin_pi_sub` / 定理 `sin_pi_sub`

English:
theorem sin_pi_sub
  given: (x : Real)
  statement: sin (π - x) = sin x
  proof: neg_neg (sin x) ▸ sin_neg x ▸ sin_antiperiodic.sub_eq'

@[simp]

中文:
定理 sin_pi_sub
  条件: (x : 实数)
  结论: sin (π - x) = sin x
  证明: neg_neg (sin x) ▸ sin_neg x ▸ sin_antiperiodic.sub_eq'

@[simp]

Depends on / 依赖: neg_neg, sin_antiperiodic, sin_antiperiodic.sub_eq, sin_neg, sub_eq
-/
theorem sin_pi_sub (x : Real) : sin (π - x) = sin x :=
  neg_neg (sin x) ▸ sin_neg x ▸ sin_antiperiodic.sub_eq'

@[simp]
/--
theorem `sin_two_pi_sub` / 定理 `sin_two_pi_sub`

English:
theorem sin_two_pi_sub
  given: (x : Real)
  statement: sin (2 * π - x) = -sin x
  proof: sin_neg x ▸ sin_periodic.sub_eq'

@[simp]

中文:
定理 sin_two_pi_sub
  条件: (x : 实数)
  结论: sin (2 * π - x) = -sin x
  证明: sin_neg x ▸ sin_periodic.sub_eq'

@[simp]

Depends on / 依赖: sin_neg, sin_periodic, sin_periodic.sub_eq, sub_eq
-/
theorem sin_two_pi_sub (x : Real) : sin (2 * π - x) = -sin x :=
  sin_neg x ▸ sin_periodic.sub_eq'

@[simp]
/--
theorem `sin_nat_mul_pi` / 定理 `sin_nat_mul_pi`

English:
theorem sin_nat_mul_pi
  given: (n : Nat)
  statement: sin (n * π) = 0
  proof: sin_antiperiodic.nat_mul_eq_of_eq_zero sin_zero n

@[simp]

中文:
定理 sin_nat_mul_pi
  条件: (n : 自然数)
  结论: sin (n * π) = 0
  证明: sin_antiperiodic.nat_mul_eq_of_eq_zero sin_zero n

@[simp]

Depends on / 依赖: nat_mul_eq_of_eq_zero, sin_antiperiodic, sin_antiperiodic.nat_mul_eq_of_eq_zero, sin_zero
-/
theorem sin_nat_mul_pi (n : Nat) : sin (n * π) = 0 :=
  sin_antiperiodic.nat_mul_eq_of_eq_zero sin_zero n

@[simp]
/--
theorem `sin_int_mul_pi` / 定理 `sin_int_mul_pi`

English:
theorem sin_int_mul_pi
  given: (n : Int)
  statement: sin (n * π) = 0
  proof: sin_antiperiodic.int_mul_eq_of_eq_zero sin_zero n

@[simp]

中文:
定理 sin_int_mul_pi
  条件: (n : 整数)
  结论: sin (n * π) = 0
  证明: sin_antiperiodic.int_mul_eq_of_eq_zero sin_zero n

@[simp]

Depends on / 依赖: int_mul_eq_of_eq_zero, sin_antiperiodic, sin_antiperiodic.int_mul_eq_of_eq_zero, sin_zero
-/
theorem sin_int_mul_pi (n : Int) : sin (n * π) = 0 :=
  sin_antiperiodic.int_mul_eq_of_eq_zero sin_zero n

@[simp]
/--
theorem `sin_add_nat_mul_two_pi` / 定理 `sin_add_nat_mul_two_pi`

English:
theorem sin_add_nat_mul_two_pi
  given: (x : Real) (n : Nat)
  statement: sin (x + n * (2 * π)) = sin x
  proof: sin_periodic.nat_mul n x

@[simp]

中文:
定理 sin_add_nat_mul_two_pi
  条件: (x : 实数) (n : 自然数)
  结论: sin (x + n * (2 * π)) = sin x
  证明: sin_periodic.nat_mul n x

@[simp]

Depends on / 依赖: nat_mul, sin_periodic, sin_periodic.nat_mul
-/
theorem sin_add_nat_mul_two_pi (x : Real) (n : Nat) : sin (x + n * (2 * π)) = sin x :=
  sin_periodic.nat_mul n x

@[simp]
/--
theorem `sin_add_int_mul_two_pi` / 定理 `sin_add_int_mul_two_pi`

English:
theorem sin_add_int_mul_two_pi
  given: (x : Real) (n : Int)
  statement: sin (x + n * (2 * π)) = sin x
  proof: sin_periodic.int_mul n x

@[simp]

中文:
定理 sin_add_int_mul_two_pi
  条件: (x : 实数) (n : 整数)
  结论: sin (x + n * (2 * π)) = sin x
  证明: sin_periodic.int_mul n x

@[simp]

Depends on / 依赖: int_mul, sin_periodic, sin_periodic.int_mul
-/
theorem sin_add_int_mul_two_pi (x : Real) (n : Int) : sin (x + n * (2 * π)) = sin x :=
  sin_periodic.int_mul n x

@[simp]
/--
theorem `sin_sub_nat_mul_two_pi` / 定理 `sin_sub_nat_mul_two_pi`

English:
theorem sin_sub_nat_mul_two_pi
  given: (x : Real) (n : Nat)
  statement: sin (x - n * (2 * π)) = sin x
  proof: sin_periodic.sub_nat_mul_eq n

@[simp]

中文:
定理 sin_sub_nat_mul_two_pi
  条件: (x : 实数) (n : 自然数)
  结论: sin (x - n * (2 * π)) = sin x
  证明: sin_periodic.sub_nat_mul_eq n

@[simp]

Depends on / 依赖: sin_periodic, sin_periodic.sub_nat_mul_eq, sub_nat_mul_eq
-/
theorem sin_sub_nat_mul_two_pi (x : Real) (n : Nat) : sin (x - n * (2 * π)) = sin x :=
  sin_periodic.sub_nat_mul_eq n

@[simp]
/--
theorem `sin_sub_int_mul_two_pi` / 定理 `sin_sub_int_mul_two_pi`

English:
theorem sin_sub_int_mul_two_pi
  given: (x : Real) (n : Int)
  statement: sin (x - n * (2 * π)) = sin x
  proof: sin_periodic.sub_int_mul_eq n

@[simp]

中文:
定理 sin_sub_int_mul_two_pi
  条件: (x : 实数) (n : 整数)
  结论: sin (x - n * (2 * π)) = sin x
  证明: sin_periodic.sub_int_mul_eq n

@[simp]

Depends on / 依赖: sin_periodic, sin_periodic.sub_int_mul_eq, sub_int_mul_eq
-/
theorem sin_sub_int_mul_two_pi (x : Real) (n : Int) : sin (x - n * (2 * π)) = sin x :=
  sin_periodic.sub_int_mul_eq n

@[simp]
/--
theorem `sin_nat_mul_two_pi_sub` / 定理 `sin_nat_mul_two_pi_sub`

English:
theorem sin_nat_mul_two_pi_sub
  given: (x : Real) (n : Nat)
  statement: sin (n * (2 * π) - x) = -sin x
  proof: sin_neg x ▸ sin_periodic.nat_mul_sub_eq n

@[simp]

中文:
定理 sin_nat_mul_two_pi_sub
  条件: (x : 实数) (n : 自然数)
  结论: sin (n * (2 * π) - x) = -sin x
  证明: sin_neg x ▸ sin_periodic.nat_mul_sub_eq n

@[simp]

Depends on / 依赖: nat_mul_sub_eq, sin_neg, sin_periodic, sin_periodic.nat_mul_sub_eq
-/
theorem sin_nat_mul_two_pi_sub (x : Real) (n : Nat) : sin (n * (2 * π) - x) = -sin x :=
  sin_neg x ▸ sin_periodic.nat_mul_sub_eq n

@[simp]
/--
theorem `sin_int_mul_two_pi_sub` / 定理 `sin_int_mul_two_pi_sub`

English:
theorem sin_int_mul_two_pi_sub
  given: (x : Real) (n : Int)
  statement: sin (n * (2 * π) - x) = -sin x
  proof: sin_neg x ▸ sin_periodic.int_mul_sub_eq n

中文:
定理 sin_int_mul_two_pi_sub
  条件: (x : 实数) (n : 整数)
  结论: sin (n * (2 * π) - x) = -sin x
  证明: sin_neg x ▸ sin_periodic.int_mul_sub_eq n

Depends on / 依赖: int_mul_sub_eq, sin_neg, sin_periodic, sin_periodic.int_mul_sub_eq
-/
theorem sin_int_mul_two_pi_sub (x : Real) (n : Int) : sin (n * (2 * π) - x) = -sin x :=
  sin_neg x ▸ sin_periodic.int_mul_sub_eq n

/--
theorem `sin_add_int_mul_pi` / 定理 `sin_add_int_mul_pi`

English:
theorem sin_add_int_mul_pi
  given: (x : Real) (n : Int)
  statement: sin (x + n * π) = (-1) ^ n * sin x
  proof: n.cast_negOnePow Real ▸ sin_antiperiodic.add_int_mul_eq n

中文:
定理 sin_add_int_mul_pi
  条件: (x : 实数) (n : 整数)
  结论: sin (x + n * π) = (-1) ^ n * sin x
  证明: n.cast_negOnePow Real ▸ sin_antiperiodic.add_int_mul_eq n

Depends on / 依赖: CanonicallyOverClass, OverClass, add_int_mul_eq, cast_negOnePow, n.cast_negOnePow, sin_antiperiodic, sin_antiperiodic.add_int_mul_eq
-/
theorem sin_add_int_mul_pi (x : Real) (n : Int) : sin (x + n * π) = (-1) ^ n * sin x :=
  n.cast_negOnePow Real ▸ sin_antiperiodic.add_int_mul_eq n

/--
theorem `sin_add_nat_mul_pi` / 定理 `sin_add_nat_mul_pi`

English:
theorem sin_add_nat_mul_pi
  given: (x : Real) (n : Nat)
  statement: sin (x + n * π) = (-1) ^ n * sin x
  proof: sin_antiperiodic.add_nat_mul_eq n

中文:
定理 sin_add_nat_mul_pi
  条件: (x : 实数) (n : 自然数)
  结论: sin (x + n * π) = (-1) ^ n * sin x
  证明: sin_antiperiodic.add_nat_mul_eq n

Depends on / 依赖: add_nat_mul_eq, sin_antiperiodic, sin_antiperiodic.add_nat_mul_eq
-/
theorem sin_add_nat_mul_pi (x : Real) (n : Nat) : sin (x + n * π) = (-1) ^ n * sin x :=
  sin_antiperiodic.add_nat_mul_eq n

/--
theorem `sin_sub_int_mul_pi` / 定理 `sin_sub_int_mul_pi`

English:
theorem sin_sub_int_mul_pi
  given: (x : Real) (n : Int)
  statement: sin (x - n * π) = (-1) ^ n * sin x
  proof: n.cast_negOnePow Real ▸ sin_antiperiodic.sub_int_mul_eq n

中文:
定理 sin_sub_int_mul_pi
  条件: (x : 实数) (n : 整数)
  结论: sin (x - n * π) = (-1) ^ n * sin x
  证明: n.cast_negOnePow Real ▸ sin_antiperiodic.sub_int_mul_eq n

Depends on / 依赖: cast_negOnePow, n.cast_negOnePow, sin_antiperiodic, sin_antiperiodic.sub_int_mul_eq, sub_int_mul_eq
-/
theorem sin_sub_int_mul_pi (x : Real) (n : Int) : sin (x - n * π) = (-1) ^ n * sin x :=
  n.cast_negOnePow Real ▸ sin_antiperiodic.sub_int_mul_eq n

/--
theorem `sin_sub_nat_mul_pi` / 定理 `sin_sub_nat_mul_pi`

English:
theorem sin_sub_nat_mul_pi
  given: (x : Real) (n : Nat)
  statement: sin (x - n * π) = (-1) ^ n * sin x
  proof: sin_antiperiodic.sub_nat_mul_eq n

中文:
定理 sin_sub_nat_mul_pi
  条件: (x : 实数) (n : 自然数)
  结论: sin (x - n * π) = (-1) ^ n * sin x
  证明: sin_antiperiodic.sub_nat_mul_eq n

Depends on / 依赖: sin_antiperiodic, sin_antiperiodic.sub_nat_mul_eq, sub_nat_mul_eq
-/
theorem sin_sub_nat_mul_pi (x : Real) (n : Nat) : sin (x - n * π) = (-1) ^ n * sin x :=
  sin_antiperiodic.sub_nat_mul_eq n

/--
theorem `sin_int_mul_pi_sub` / 定理 `sin_int_mul_pi_sub`

English:
theorem sin_int_mul_pi_sub
  given: (x : Real) (n : Int)
  statement: sin (n * π - x) = -((-1) ^ n * sin x)
  proof: by
  simpa only [sin_neg, mul_neg, Int.cast_negOnePow] using sin_antiperiodic.int_mul_sub_eq n

中文:
定理 sin_int_mul_pi_sub
  条件: (x : 实数) (n : 整数)
  结论: sin (n * π - x) = -((-1) ^ n * sin x)
  证明: by
  simpa only [sin_neg, mul_neg, Int.cast_negOnePow] using sin_antiperiodic.int_mul_sub_eq n

Depends on / 依赖: Int.cast_negOnePow, cast_negOnePow, int_mul_sub_eq, mul_neg, sin_antiperiodic, sin_antiperiodic.int_mul_sub_eq, sin_neg
-/
theorem sin_int_mul_pi_sub (x : Real) (n : Int) : sin (n * π - x) = -((-1) ^ n * sin x) := by
  simpa only [sin_neg, mul_neg, Int.cast_negOnePow] using sin_antiperiodic.int_mul_sub_eq n

/--
theorem `sin_nat_mul_pi_sub` / 定理 `sin_nat_mul_pi_sub`

English:
theorem sin_nat_mul_pi_sub
  given: (x : Real) (n : Nat)
  statement: sin (n * π - x) = -((-1) ^ n * sin x)
  proof: by
  simpa only [sin_neg, mul_neg] using sin_antiperiodic.nat_mul_sub_eq n

中文:
定理 sin_nat_mul_pi_sub
  条件: (x : 实数) (n : 自然数)
  结论: sin (n * π - x) = -((-1) ^ n * sin x)
  证明: by
  simpa only [sin_neg, mul_neg] using sin_antiperiodic.nat_mul_sub_eq n

Depends on / 依赖: mul_neg, nat_mul_sub_eq, sin_antiperiodic, sin_antiperiodic.nat_mul_sub_eq, sin_neg
-/
theorem sin_nat_mul_pi_sub (x : Real) (n : Nat) : sin (n * π - x) = -((-1) ^ n * sin x) := by
  simpa only [sin_neg, mul_neg] using sin_antiperiodic.nat_mul_sub_eq n

/--
theorem `cos_antiperiodic` / 定理 `cos_antiperiodic`

English:
theorem cos_antiperiodic
  statement: Function.Antiperiodic cos π
  proof: by simp [cos_add]

中文:
定理 cos_antiperiodic
  结论: Function.Antiperiodic cos π
  证明: by simp [cos_add]

Depends on / 依赖: cos_add
-/
theorem cos_antiperiodic : Function.Antiperiodic cos π := by simp [cos_add]

/--
theorem `cos_periodic` / 定理 `cos_periodic`

English:
theorem cos_periodic
  statement: Function.Periodic cos (2 * π)
  proof: cos_antiperiodic.periodic_two_mul

@[simp]

中文:
定理 cos_periodic
  结论: Function.Periodic cos (2 * π)
  证明: cos_antiperiodic.periodic_two_mul

@[simp]

Depends on / 依赖: cos_antiperiodic, cos_antiperiodic.periodic_two_mul, periodic_two_mul
-/
theorem cos_periodic : Function.Periodic cos (2 * π) :=
  cos_antiperiodic.periodic_two_mul

@[simp]
/--
theorem `abs_cos_int_mul_pi` / 定理 `abs_cos_int_mul_pi`

English:
theorem abs_cos_int_mul_pi
  given: (k : Int)
  statement: |cos (k * π)| = 1
  proof: by
  simp [abs_cos_eq_sqrt_one_sub_sin_sq]

@[simp]

中文:
定理 abs_cos_int_mul_pi
  条件: (k : 整数)
  结论: |cos (k * π)| = 1
  证明: by
  simp [abs_cos_eq_sqrt_one_sub_sin_sq]

@[simp]

Depends on / 依赖: abs_cos_eq_sqrt_one_sub_sin_sq
-/
theorem abs_cos_int_mul_pi (k : Int) : |cos (k * π)| = 1 := by
  simp [abs_cos_eq_sqrt_one_sub_sin_sq]

@[simp]
/--
theorem `cos_add_pi` / 定理 `cos_add_pi`

English:
theorem cos_add_pi
  given: (x : Real)
  statement: cos (x + π) = -cos x
  proof: cos_antiperiodic x

@[simp]

中文:
定理 cos_add_pi
  条件: (x : 实数)
  结论: cos (x + π) = -cos x
  证明: cos_antiperiodic x

@[simp]

Depends on / 依赖: cos_antiperiodic
-/
theorem cos_add_pi (x : Real) : cos (x + π) = -cos x :=
  cos_antiperiodic x

@[simp]
/--
theorem `cos_add_two_pi` / 定理 `cos_add_two_pi`

English:
theorem cos_add_two_pi
  given: (x : Real)
  statement: cos (x + 2 * π) = cos x
  proof: cos_periodic x

@[simp]

中文:
定理 cos_add_two_pi
  条件: (x : 实数)
  结论: cos (x + 2 * π) = cos x
  证明: cos_periodic x

@[simp]

Depends on / 依赖: cos_periodic
-/
theorem cos_add_two_pi (x : Real) : cos (x + 2 * π) = cos x :=
  cos_periodic x

@[simp]
/--
theorem `cos_sub_pi` / 定理 `cos_sub_pi`

English:
theorem cos_sub_pi
  given: (x : Real)
  statement: cos (x - π) = -cos x
  proof: cos_antiperiodic.sub_eq x

@[simp]

中文:
定理 cos_sub_pi
  条件: (x : 实数)
  结论: cos (x - π) = -cos x
  证明: cos_antiperiodic.sub_eq x

@[simp]

Depends on / 依赖: Over.w, cos_antiperiodic, cos_antiperiodic.sub_eq, sub_eq
-/
theorem cos_sub_pi (x : Real) : cos (x - π) = -cos x :=
  cos_antiperiodic.sub_eq x

@[simp]
/--
theorem `cos_sub_two_pi` / 定理 `cos_sub_two_pi`

English:
theorem cos_sub_two_pi
  given: (x : Real)
  statement: cos (x - 2 * π) = cos x
  proof: cos_periodic.sub_eq x

@[simp]

中文:
定理 cos_sub_two_pi
  条件: (x : 实数)
  结论: cos (x - 2 * π) = cos x
  证明: cos_periodic.sub_eq x

@[simp]

Depends on / 依赖: Over.forget, asOverHom, cos_periodic, cos_periodic.sub_eq, forget, isIso_of_reflects_iso, sub_eq
-/
theorem cos_sub_two_pi (x : Real) : cos (x - 2 * π) = cos x :=
  cos_periodic.sub_eq x

@[simp]
/--
theorem `cos_pi_sub` / 定理 `cos_pi_sub`

English:
theorem cos_pi_sub
  given: (x : Real)
  statement: cos (π - x) = -cos x
  proof: cos_neg x ▸ cos_antiperiodic.sub_eq'

@[simp]

中文:
定理 cos_pi_sub
  条件: (x : 实数)
  结论: cos (π - x) = -cos x
  证明: cos_neg x ▸ cos_antiperiodic.sub_eq'

@[simp]

Depends on / 依赖: cos_antiperiodic, cos_antiperiodic.sub_eq, cos_neg, sub_eq
-/
theorem cos_pi_sub (x : Real) : cos (π - x) = -cos x :=
  cos_neg x ▸ cos_antiperiodic.sub_eq'

@[simp]
/--
theorem `cos_two_pi_sub` / 定理 `cos_two_pi_sub`

English:
theorem cos_two_pi_sub
  given: (x : Real)
  statement: cos (2 * π - x) = cos x
  proof: cos_neg x ▸ cos_periodic.sub_eq'

@[simp]

中文:
定理 cos_two_pi_sub
  条件: (x : 实数)
  结论: cos (2 * π - x) = cos x
  证明: cos_neg x ▸ cos_periodic.sub_eq'

@[simp]

Depends on / 依赖: cos_neg, cos_periodic, cos_periodic.sub_eq, sub_eq
-/
theorem cos_two_pi_sub (x : Real) : cos (2 * π - x) = cos x :=
  cos_neg x ▸ cos_periodic.sub_eq'

@[simp]
/--
theorem `cos_nat_mul_two_pi` / 定理 `cos_nat_mul_two_pi`

English:
theorem cos_nat_mul_two_pi
  given: (n : Nat)
  statement: cos (n * (2 * π)) = 1
  proof: (cos_periodic.nat_mul_eq n).trans cos_zero

@[simp]

中文:
定理 cos_nat_mul_two_pi
  条件: (n : 自然数)
  结论: cos (n * (2 * π)) = 1
  证明: (cos_periodic.nat_mul_eq n).trans cos_zero

@[simp]

Depends on / 依赖: cos_periodic, cos_periodic.nat_mul_eq, cos_zero, nat_mul_eq
-/
theorem cos_nat_mul_two_pi (n : Nat) : cos (n * (2 * π)) = 1 :=
  (cos_periodic.nat_mul_eq n).trans cos_zero

@[simp]
/--
theorem `cos_int_mul_two_pi` / 定理 `cos_int_mul_two_pi`

English:
theorem cos_int_mul_two_pi
  given: (n : Int)
  statement: cos (n * (2 * π)) = 1
  proof: (cos_periodic.int_mul_eq n).trans cos_zero

@[simp]

中文:
定理 cos_int_mul_two_pi
  条件: (n : 整数)
  结论: cos (n * (2 * π)) = 1
  证明: (cos_periodic.int_mul_eq n).trans cos_zero

@[simp]

Depends on / 依赖: Over.mapPullbackAdj, cos_periodic, cos_periodic.int_mul_eq, cos_zero, int_mul_eq, isLeftAdjoint, mapPullbackAdj
-/
theorem cos_int_mul_two_pi (n : Int) : cos (n * (2 * π)) = 1 :=
  (cos_periodic.int_mul_eq n).trans cos_zero

@[simp]
/--
theorem `cos_add_nat_mul_two_pi` / 定理 `cos_add_nat_mul_two_pi`

English:
theorem cos_add_nat_mul_two_pi
  given: (x : Real) (n : Nat)
  statement: cos (x + n * (2 * π)) = cos x
  proof: cos_periodic.nat_mul n x

@[simp]

中文:
定理 cos_add_nat_mul_two_pi
  条件: (x : 实数) (n : 自然数)
  结论: cos (x + n * (2 * π)) = cos x
  证明: cos_periodic.nat_mul n x

@[simp]

Depends on / 依赖: Over.mapPullbackAdj, cos_periodic, cos_periodic.nat_mul, isRightAdjoint, mapPullbackAdj, nat_mul
-/
theorem cos_add_nat_mul_two_pi (x : Real) (n : Nat) : cos (x + n * (2 * π)) = cos x :=
  cos_periodic.nat_mul n x

@[simp]
/--
theorem `cos_add_int_mul_two_pi` / 定理 `cos_add_int_mul_two_pi`

English:
theorem cos_add_int_mul_two_pi
  given: (x : Real) (n : Int)
  statement: cos (x + n * (2 * π)) = cos x
  proof: cos_periodic.int_mul n x

@[simp]

中文:
定理 cos_add_int_mul_two_pi
  条件: (x : 实数) (n : 整数)
  结论: cos (x + n * (2 * π)) = cos x
  证明: cos_periodic.int_mul n x

@[simp]

Depends on / 依赖: cos_periodic, cos_periodic.int_mul, int_mul
-/
theorem cos_add_int_mul_two_pi (x : Real) (n : Int) : cos (x + n * (2 * π)) = cos x :=
  cos_periodic.int_mul n x

@[simp]
/--
theorem `cos_sub_nat_mul_two_pi` / 定理 `cos_sub_nat_mul_two_pi`

English:
theorem cos_sub_nat_mul_two_pi
  given: (x : Real) (n : Nat)
  statement: cos (x - n * (2 * π)) = cos x
  proof: cos_periodic.sub_nat_mul_eq n

@[simp]

中文:
定理 cos_sub_nat_mul_two_pi
  条件: (x : 实数) (n : 自然数)
  结论: cos (x - n * (2 * π)) = cos x
  证明: cos_periodic.sub_nat_mul_eq n

@[simp]

Depends on / 依赖: cos_periodic, cos_periodic.sub_nat_mul_eq, sub_nat_mul_eq
-/
theorem cos_sub_nat_mul_two_pi (x : Real) (n : Nat) : cos (x - n * (2 * π)) = cos x :=
  cos_periodic.sub_nat_mul_eq n

@[simp]
/--
theorem `cos_sub_int_mul_two_pi` / 定理 `cos_sub_int_mul_two_pi`

English:
theorem cos_sub_int_mul_two_pi
  given: (x : Real) (n : Int)
  statement: cos (x - n * (2 * π)) = cos x
  proof: cos_periodic.sub_int_mul_eq n

@[simp]

中文:
定理 cos_sub_int_mul_two_pi
  条件: (x : 实数) (n : 整数)
  结论: cos (x - n * (2 * π)) = cos x
  证明: cos_periodic.sub_int_mul_eq n

@[simp]

Depends on / 依赖: cos_periodic, cos_periodic.sub_int_mul_eq, sub_int_mul_eq
-/
theorem cos_sub_int_mul_two_pi (x : Real) (n : Int) : cos (x - n * (2 * π)) = cos x :=
  cos_periodic.sub_int_mul_eq n

@[simp]
/--
theorem `cos_nat_mul_two_pi_sub` / 定理 `cos_nat_mul_two_pi_sub`

English:
theorem cos_nat_mul_two_pi_sub
  given: (x : Real) (n : Nat)
  statement: cos (n * (2 * π) - x) = cos x
  proof: cos_neg x ▸ cos_periodic.nat_mul_sub_eq n

@[simp]

中文:
定理 cos_nat_mul_two_pi_sub
  条件: (x : 实数) (n : 自然数)
  结论: cos (n * (2 * π) - x) = cos x
  证明: cos_neg x ▸ cos_periodic.nat_mul_sub_eq n

@[simp]

Depends on / 依赖: cos_neg, cos_periodic, cos_periodic.nat_mul_sub_eq, nat_mul_sub_eq
-/
theorem cos_nat_mul_two_pi_sub (x : Real) (n : Nat) : cos (n * (2 * π) - x) = cos x :=
  cos_neg x ▸ cos_periodic.nat_mul_sub_eq n

@[simp]
/--
theorem `cos_int_mul_two_pi_sub` / 定理 `cos_int_mul_two_pi_sub`

English:
theorem cos_int_mul_two_pi_sub
  given: (x : Real) (n : Int)
  statement: cos (n * (2 * π) - x) = cos x
  proof: cos_neg x ▸ cos_periodic.int_mul_sub_eq n

中文:
定理 cos_int_mul_two_pi_sub
  条件: (x : 实数) (n : 整数)
  结论: cos (n * (2 * π) - x) = cos x
  证明: cos_neg x ▸ cos_periodic.int_mul_sub_eq n

Depends on / 依赖: cos_neg, cos_periodic, cos_periodic.int_mul_sub_eq, int_mul_sub_eq
-/
theorem cos_int_mul_two_pi_sub (x : Real) (n : Int) : cos (n * (2 * π) - x) = cos x :=
  cos_neg x ▸ cos_periodic.int_mul_sub_eq n

/--
theorem `cos_add_int_mul_pi` / 定理 `cos_add_int_mul_pi`

English:
theorem cos_add_int_mul_pi
  given: (x : Real) (n : Int)
  statement: cos (x + n * π) = (-1) ^ n * cos x
  proof: n.cast_negOnePow Real ▸ cos_antiperiodic.add_int_mul_eq n

中文:
定理 cos_add_int_mul_pi
  条件: (x : 实数) (n : 整数)
  结论: cos (x + n * π) = (-1) ^ n * cos x
  证明: n.cast_negOnePow Real ▸ cos_antiperiodic.add_int_mul_eq n

Depends on / 依赖: add_int_mul_eq, cast_negOnePow, cos_antiperiodic, cos_antiperiodic.add_int_mul_eq, n.cast_negOnePow
-/
theorem cos_add_int_mul_pi (x : Real) (n : Int) : cos (x + n * π) = (-1) ^ n * cos x :=
  n.cast_negOnePow Real ▸ cos_antiperiodic.add_int_mul_eq n

/--
theorem `cos_int_mul_pi` / 定理 `cos_int_mul_pi`

English:
theorem cos_int_mul_pi
  given: (n : Int)
  statement: cos (n * π) = (-1) ^ n
  proof: by
  simpa using cos_add_int_mul_pi 0 n

中文:
定理 cos_int_mul_pi
  条件: (n : 整数)
  结论: cos (n * π) = (-1) ^ n
  证明: by
  simpa using cos_add_int_mul_pi 0 n

Depends on / 依赖: cos_add_int_mul_pi
-/
theorem cos_int_mul_pi (n : Int) : cos (n * π) = (-1) ^ n := by
  simpa using cos_add_int_mul_pi 0 n

/--
theorem `cos_add_nat_mul_pi` / 定理 `cos_add_nat_mul_pi`

English:
theorem cos_add_nat_mul_pi
  given: (x : Real) (n : Nat)
  statement: cos (x + n * π) = (-1) ^ n * cos x
  proof: cos_antiperiodic.add_nat_mul_eq n

中文:
定理 cos_add_nat_mul_pi
  条件: (x : 实数) (n : 自然数)
  结论: cos (x + n * π) = (-1) ^ n * cos x
  证明: cos_antiperiodic.add_nat_mul_eq n

Depends on / 依赖: add_nat_mul_eq, cos_antiperiodic, cos_antiperiodic.add_nat_mul_eq
-/
theorem cos_add_nat_mul_pi (x : Real) (n : Nat) : cos (x + n * π) = (-1) ^ n * cos x :=
  cos_antiperiodic.add_nat_mul_eq n

/--
theorem `cos_nat_mul_pi` / 定理 `cos_nat_mul_pi`

English:
theorem cos_nat_mul_pi
  given: (n : Nat)
  statement: cos (n * π) = (-1) ^ n
  proof: by
  simpa using cos_add_nat_mul_pi 0 n

中文:
定理 cos_nat_mul_pi
  条件: (n : 自然数)
  结论: cos (n * π) = (-1) ^ n
  证明: by
  simpa using cos_add_nat_mul_pi 0 n

Depends on / 依赖: cos_add_nat_mul_pi
-/
theorem cos_nat_mul_pi (n : Nat) : cos (n * π) = (-1) ^ n := by
  simpa using cos_add_nat_mul_pi 0 n

/--
theorem `cos_sub_int_mul_pi` / 定理 `cos_sub_int_mul_pi`

English:
theorem cos_sub_int_mul_pi
  given: (x : Real) (n : Int)
  statement: cos (x - n * π) = (-1) ^ n * cos x
  proof: n.cast_negOnePow Real ▸ cos_antiperiodic.sub_int_mul_eq n

中文:
定理 cos_sub_int_mul_pi
  条件: (x : 实数) (n : 整数)
  结论: cos (x - n * π) = (-1) ^ n * cos x
  证明: n.cast_negOnePow Real ▸ cos_antiperiodic.sub_int_mul_eq n

Depends on / 依赖: cast_negOnePow, cos_antiperiodic, cos_antiperiodic.sub_int_mul_eq, n.cast_negOnePow, sub_int_mul_eq
-/
theorem cos_sub_int_mul_pi (x : Real) (n : Int) : cos (x - n * π) = (-1) ^ n * cos x :=
  n.cast_negOnePow Real ▸ cos_antiperiodic.sub_int_mul_eq n

/--
theorem `cos_sub_nat_mul_pi` / 定理 `cos_sub_nat_mul_pi`

English:
theorem cos_sub_nat_mul_pi
  given: (x : Real) (n : Nat)
  statement: cos (x - n * π) = (-1) ^ n * cos x
  proof: cos_antiperiodic.sub_nat_mul_eq n

中文:
定理 cos_sub_nat_mul_pi
  条件: (x : 实数) (n : 自然数)
  结论: cos (x - n * π) = (-1) ^ n * cos x
  证明: cos_antiperiodic.sub_nat_mul_eq n

Depends on / 依赖: cos_antiperiodic, cos_antiperiodic.sub_nat_mul_eq, sub_nat_mul_eq
-/
theorem cos_sub_nat_mul_pi (x : Real) (n : Nat) : cos (x - n * π) = (-1) ^ n * cos x :=
  cos_antiperiodic.sub_nat_mul_eq n

/--
theorem `cos_int_mul_pi_sub` / 定理 `cos_int_mul_pi_sub`

English:
theorem cos_int_mul_pi_sub
  given: (x : Real) (n : Int)
  statement: cos (n * π - x) = (-1) ^ n * cos x
  proof: n.cast_negOnePow Real ▸ cos_neg x ▸ cos_antiperiodic.int_mul_sub_eq n

中文:
定理 cos_int_mul_pi_sub
  条件: (x : 实数) (n : 整数)
  结论: cos (n * π - x) = (-1) ^ n * cos x
  证明: n.cast_negOnePow Real ▸ cos_neg x ▸ cos_antiperiodic.int_mul_sub_eq n

Depends on / 依赖: cast_negOnePow, cos_antiperiodic, cos_antiperiodic.int_mul_sub_eq, cos_neg, int_mul_sub_eq, n.cast_negOnePow
-/
theorem cos_int_mul_pi_sub (x : Real) (n : Int) : cos (n * π - x) = (-1) ^ n * cos x :=
  n.cast_negOnePow Real ▸ cos_neg x ▸ cos_antiperiodic.int_mul_sub_eq n

/--
theorem `cos_nat_mul_pi_sub` / 定理 `cos_nat_mul_pi_sub`

English:
theorem cos_nat_mul_pi_sub
  given: (x : Real) (n : Nat)
  statement: cos (n * π - x) = (-1) ^ n * cos x
  proof: cos_neg x ▸ cos_antiperiodic.nat_mul_sub_eq n

中文:
定理 cos_nat_mul_pi_sub
  条件: (x : 实数) (n : 自然数)
  结论: cos (n * π - x) = (-1) ^ n * cos x
  证明: cos_neg x ▸ cos_antiperiodic.nat_mul_sub_eq n

Depends on / 依赖: cos_antiperiodic, cos_antiperiodic.nat_mul_sub_eq, cos_neg, nat_mul_sub_eq
-/
theorem cos_nat_mul_pi_sub (x : Real) (n : Nat) : cos (n * π - x) = (-1) ^ n * cos x :=
  cos_neg x ▸ cos_antiperiodic.nat_mul_sub_eq n

/--
theorem `cos_nat_mul_two_pi_add_pi` / 定理 `cos_nat_mul_two_pi_add_pi`

English:
theorem cos_nat_mul_two_pi_add_pi
  given: (n : Nat)
  statement: cos (n * (2 * π) + π) = -1
  proof: by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).add_antiperiod_eq cos_antiperiodic

中文:
定理 cos_nat_mul_two_pi_add_pi
  条件: (n : 自然数)
  结论: cos (n * (2 * π) + π) = -1
  证明: by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).add_antiperiod_eq cos_antiperiodic

Depends on / 依赖: add_antiperiod_eq, cos_antiperiodic, cos_periodic, cos_periodic.nat_mul, cos_zero, nat_mul
-/
theorem cos_nat_mul_two_pi_add_pi (n : Nat) : cos (n * (2 * π) + π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).add_antiperiod_eq cos_antiperiodic

/--
theorem `cos_int_mul_two_pi_add_pi` / 定理 `cos_int_mul_two_pi_add_pi`

English:
theorem cos_int_mul_two_pi_add_pi
  given: (n : Int)
  statement: cos (n * (2 * π) + π) = -1
  proof: by
  simpa only [cos_zero] using (cos_periodic.int_mul n).add_antiperiod_eq cos_antiperiodic

中文:
定理 cos_int_mul_two_pi_add_pi
  条件: (n : 整数)
  结论: cos (n * (2 * π) + π) = -1
  证明: by
  simpa only [cos_zero] using (cos_periodic.int_mul n).add_antiperiod_eq cos_antiperiodic

Depends on / 依赖: add_antiperiod_eq, cos_antiperiodic, cos_periodic, cos_periodic.int_mul, cos_zero, int_mul
-/
theorem cos_int_mul_two_pi_add_pi (n : Int) : cos (n * (2 * π) + π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.int_mul n).add_antiperiod_eq cos_antiperiodic

/--
theorem `cos_nat_mul_two_pi_sub_pi` / 定理 `cos_nat_mul_two_pi_sub_pi`

English:
theorem cos_nat_mul_two_pi_sub_pi
  given: (n : Nat)
  statement: cos (n * (2 * π) - π) = -1
  proof: by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).sub_antiperiod_eq cos_antiperiodic

中文:
定理 cos_nat_mul_two_pi_sub_pi
  条件: (n : 自然数)
  结论: cos (n * (2 * π) - π) = -1
  证明: by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).sub_antiperiod_eq cos_antiperiodic

Depends on / 依赖: cos_antiperiodic, cos_periodic, cos_periodic.nat_mul, cos_zero, nat_mul, sub_antiperiod_eq
-/
theorem cos_nat_mul_two_pi_sub_pi (n : Nat) : cos (n * (2 * π) - π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).sub_antiperiod_eq cos_antiperiodic

/--
theorem `cos_int_mul_two_pi_sub_pi` / 定理 `cos_int_mul_two_pi_sub_pi`

English:
theorem cos_int_mul_two_pi_sub_pi
  given: (n : Int)
  statement: cos (n * (2 * π) - π) = -1
  proof: by
  simpa only [cos_zero] using (cos_periodic.int_mul n).sub_antiperiod_eq cos_antiperiodic

中文:
定理 cos_int_mul_two_pi_sub_pi
  条件: (n : 整数)
  结论: cos (n * (2 * π) - π) = -1
  证明: by
  simpa only [cos_zero] using (cos_periodic.int_mul n).sub_antiperiod_eq cos_antiperiodic

Depends on / 依赖: cos_antiperiodic, cos_periodic, cos_periodic.int_mul, cos_zero, int_mul, sub_antiperiod_eq
-/
theorem cos_int_mul_two_pi_sub_pi (n : Int) : cos (n * (2 * π) - π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.int_mul n).sub_antiperiod_eq cos_antiperiodic

/--
theorem `sin_pos_of_pos_of_lt_pi` / 定理 `sin_pos_of_pos_of_lt_pi`

English:
theorem sin_pos_of_pos_of_lt_pi
  given: {x : Real} (h0x : 0 < x) (hxp : x < π)
  statement: 0 < sin x
  proof: if hx2 : x <= 2 then sin_pos_of_pos_of_le_two h0x hx2
  else sin_pi_sub x ▸ sin_pos_of_pos_of_le_two (sub_pos.2 hxp) (by linarith [pi_le_four])

中文:
定理 sin_pos_of_pos_of_lt_pi
  条件: {x : 实数} (h0x : 0 < x) (hxp : x < π)
  结论: 0 < sin x
  证明: if hx2 : x <= 2 then sin_pos_of_pos_of_le_two h0x hx2
  else sin_pi_sub x ▸ sin_pos_of_pos_of_le_two (sub_pos.2 hxp) (by linarith [pi_le_four])

Depends on / 依赖: pi_le_four, sin_pi_sub, sin_pos_of_pos_of_le_two, sub_pos
-/
theorem sin_pos_of_pos_of_lt_pi {x : Real} (h0x : 0 < x) (hxp : x < π) : 0 < sin x :=
  if hx2 : x <= 2 then sin_pos_of_pos_of_le_two h0x hx2
  else sin_pi_sub x ▸ sin_pos_of_pos_of_le_two (sub_pos.2 hxp) (by linarith [pi_le_four])

/--
theorem `sin_pos_of_mem_Ioo` / 定理 `sin_pos_of_mem_Ioo`

English:
theorem sin_pos_of_mem_Ioo
  given: {x : Real} (hx : x in Ioo 0 π)
  statement: 0 < sin x
  proof: sin_pos_of_pos_of_lt_pi hx.1 hx.2

中文:
定理 sin_pos_of_mem_Ioo
  条件: {x : 实数} (hx : x in Ioo 0 π)
  结论: 0 < sin x
  证明: sin_pos_of_pos_of_lt_pi hx.1 hx.2

Depends on / 依赖: sin_pos_of_pos_of_lt_pi
-/
theorem sin_pos_of_mem_Ioo {x : Real} (hx : x in Ioo 0 π) : 0 < sin x :=
  sin_pos_of_pos_of_lt_pi hx.1 hx.2

/--
theorem `sin_nonneg_of_mem_Icc` / 定理 `sin_nonneg_of_mem_Icc`

English:
theorem sin_nonneg_of_mem_Icc
  given: {x : Real} (hx : x in Icc 0 π)
  statement: 0 <= sin x
  proof: by
  rw [← closure_Ioo pi_ne_zero.symm] at hx
  exact
    closure_lt_subset_le continuous_const continuous_sin
      (closure_mono (fun y => sin_pos_of_mem_Ioo) hx)

中文:
定理 sin_nonneg_of_mem_Icc
  条件: {x : 实数} (hx : x in Icc 0 π)
  结论: 0 <= sin x
  证明: by
  rw [← closure_Ioo pi_ne_zero.symm] at hx
  exact
    closure_lt_subset_le continuous_const continuous_sin
      (closure_mono (fun y => sin_pos_of_mem_Ioo) hx)

Depends on / 依赖: closure_Ioo, closure_lt_subset_le, closure_mono, continuous_const, continuous_sin, pi_ne_zero, pi_ne_zero.symm, sin_pos_of_mem_Ioo
-/
theorem sin_nonneg_of_mem_Icc {x : Real} (hx : x in Icc 0 π) : 0 <= sin x := by
  rw [← closure_Ioo pi_ne_zero.symm] at hx
  exact
    closure_lt_subset_le continuous_const continuous_sin
      (closure_mono (fun y => sin_pos_of_mem_Ioo) hx)

/--
theorem `sin_nonneg_of_nonneg_of_le_pi` / 定理 `sin_nonneg_of_nonneg_of_le_pi`

English:
theorem sin_nonneg_of_nonneg_of_le_pi
  given: {x : Real} (h0x : 0 <= x) (hxp : x <= π)
  statement: 0 <= sin x
  proof: sin_nonneg_of_mem_Icc ⟨h0x, hxp⟩

中文:
定理 sin_nonneg_of_nonneg_of_le_pi
  条件: {x : 实数} (h0x : 0 <= x) (hxp : x <= π)
  结论: 0 <= sin x
  证明: sin_nonneg_of_mem_Icc ⟨h0x, hxp⟩

Depends on / 依赖: sin_nonneg_of_mem_Icc
-/
theorem sin_nonneg_of_nonneg_of_le_pi {x : Real} (h0x : 0 <= x) (hxp : x <= π) : 0 <= sin x :=
  sin_nonneg_of_mem_Icc ⟨h0x, hxp⟩

/--
theorem `sin_neg_of_neg_of_neg_pi_lt` / 定理 `sin_neg_of_neg_of_neg_pi_lt`

English:
theorem sin_neg_of_neg_of_neg_pi_lt
  given: {x : Real} (hx0 : x < 0) (hpx : -π < x)
  statement: sin x < 0
  proof: neg_pos.1 sin_neg x ▸ sin_pos_of_pos_of_lt_pi (neg_pos.2 hx0) (neg_lt.1 hpx)

中文:
定理 sin_neg_of_neg_of_neg_pi_lt
  条件: {x : 实数} (hx0 : x < 0) (hpx : -π < x)
  结论: sin x < 0
  证明: neg_pos.1 sin_neg x ▸ sin_pos_of_pos_of_lt_pi (neg_pos.2 hx0) (neg_lt.1 hpx)

Depends on / 依赖: neg_lt, neg_pos, sin_neg, sin_pos_of_pos_of_lt_pi
-/
theorem sin_neg_of_neg_of_neg_pi_lt {x : Real} (hx0 : x < 0) (hpx : -π < x) : sin x < 0 :=
neg_pos.1 sin_neg x ▸ sin_pos_of_pos_of_lt_pi (neg_pos.2 hx0) (neg_lt.1 hpx)

/--
theorem `sin_nonpos_of_nonpos_of_neg_pi_le` / 定理 `sin_nonpos_of_nonpos_of_neg_pi_le`

English:
theorem sin_nonpos_of_nonpos_of_neg_pi_le
  given: {x : Real} (hx0 : x <= 0) (hpx : -π <= x)
  statement: sin x <= 0
  proof: neg_nonneg.1 sin_neg x ▸ sin_nonneg_of_nonneg_of_le_pi (neg_nonneg.2 hx0) (neg_le.1 hpx)

中文:
定理 sin_nonpos_of_nonpos_of_neg_pi_le
  条件: {x : 实数} (hx0 : x <= 0) (hpx : -π <= x)
  结论: sin x <= 0
  证明: neg_nonneg.1 sin_neg x ▸ sin_nonneg_of_nonneg_of_le_pi (neg_nonneg.2 hx0) (neg_le.1 hpx)

Depends on / 依赖: neg_le, neg_nonneg, sin_neg, sin_nonneg_of_nonneg_of_le_pi
-/
theorem sin_nonpos_of_nonpos_of_neg_pi_le {x : Real} (hx0 : x <= 0) (hpx : -π <= x) : sin x <= 0 :=
neg_nonneg.1 sin_neg x ▸ sin_nonneg_of_nonneg_of_le_pi (neg_nonneg.2 hx0) (neg_le.1 hpx)

/--
lemma `abs_sin_eq_sin_abs_of_abs_le_pi` / 引理 `abs_sin_eq_sin_abs_of_abs_le_pi`

English:
lemma abs_sin_eq_sin_abs_of_abs_le_pi
  given: {x : Real} (hx : |x| <= π)
  statement: |sin x| = sin |x|
  proof: by
  rcases lt_or_ge x 0 with h | h
  · rw [abs_of_neg h, sin_neg,
      abs_of_nonpos (sin_nonpos_of_nonpos_of_neg_pi_le h.le (abs_le.1 hx).1)]
  · rw [abs_of_nonneg h, abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi h (abs_le.1 hx).2)]

@[simp]

中文:
引理 abs_sin_eq_sin_abs_of_abs_le_pi
  条件: {x : 实数} (hx : |x| <= π)
  结论: |sin x| = sin |x|
  证明: by
  rcases lt_or_ge x 0 with h | h
  · rw [abs_of_neg h, sin_neg,
      abs_of_nonpos (sin_nonpos_of_nonpos_of_neg_pi_le h.le (abs_le.1 hx).1)]
  · rw [abs_of_nonneg h, abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi h (abs_le.1 hx).2)]

@[simp]

Depends on / 依赖: abs_le, abs_of_neg, abs_of_nonneg, abs_of_nonpos, h.le, lt_or_ge, sin_neg, sin_nonneg_of_nonneg_of_le_pi, sin_nonpos_of_nonpos_of_neg_pi_le
-/
lemma abs_sin_eq_sin_abs_of_abs_le_pi {x : Real} (hx : |x| <= π) : |sin x| = sin |x| := by
  rcases lt_or_ge x 0 with h | h
  · rw [abs_of_neg h, sin_neg,
      abs_of_nonpos (sin_nonpos_of_nonpos_of_neg_pi_le h.le (abs_le.1 hx).1)]
  · rw [abs_of_nonneg h, abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi h (abs_le.1 hx).2)]

@[simp]
/--
theorem `sin_pi_div_two` / 定理 `sin_pi_div_two`

English:
theorem sin_pi_div_two
  statement: sin (π / 2) = 1
  proof: have : sin (π / 2) = 1 ∨ sin (π / 2) = -1 := by
    simpa [sq, mul_self_eq_one_iff] using sin_sq_add_cos_sq (π / 2)
  this.resolve_right fun h =>
show ¬(0 : Real) < -1 by simp
      h ▸ sin_pos_of_pos_of_lt_pi pi_div_two_pos (half_lt_self pi_pos)

中文:
定理 sin_pi_div_two
  结论: sin (π / 2) = 1
  证明: have : sin (π / 2) = 1 ∨ sin (π / 2) = -1 := by
    simpa [sq, mul_self_eq_one_iff] using sin_sq_add_cos_sq (π / 2)
  this.resolve_right fun h =>
show ¬(0 : Real) < -1 by simp
      h ▸ sin_pos_of_pos_of_lt_pi pi_div_two_pos (half_lt_self pi_pos)

Depends on / 依赖: half_lt_self, mul_self_eq_one_iff, pi_div_two_pos, pi_pos, resolve_right, sin_pos_of_pos_of_lt_pi, sin_sq_add_cos_sq, this.resolve_right
-/
theorem sin_pi_div_two : sin (π / 2) = 1 :=
  have : sin (π / 2) = 1 ∨ sin (π / 2) = -1 := by
    simpa [sq, mul_self_eq_one_iff] using sin_sq_add_cos_sq (π / 2)
  this.resolve_right fun h =>
show ¬(0 : Real) < -1 by simp
      h ▸ sin_pos_of_pos_of_lt_pi pi_div_two_pos (half_lt_self pi_pos)

/--
theorem `sin_add_pi_div_two` / 定理 `sin_add_pi_div_two`

English:
theorem sin_add_pi_div_two
  given: (x : Real)
  statement: sin (x + π / 2) = cos x
  proof: by simp [sin_add]

中文:
定理 sin_add_pi_div_two
  条件: (x : 实数)
  结论: sin (x + π / 2) = cos x
  证明: by simp [sin_add]

Depends on / 依赖: sin_add
-/
theorem sin_add_pi_div_two (x : Real) : sin (x + π / 2) = cos x := by simp [sin_add]

/--
theorem `sin_sub_pi_div_two` / 定理 `sin_sub_pi_div_two`

English:
theorem sin_sub_pi_div_two
  given: (x : Real)
  statement: sin (x - π / 2) = -cos x
  proof: by simp [sub_eq_add_neg, sin_add]

中文:
定理 sin_sub_pi_div_two
  条件: (x : 实数)
  结论: sin (x - π / 2) = -cos x
  证明: by simp [sub_eq_add_neg, sin_add]

Depends on / 依赖: sin_add, sub_eq_add_neg
-/
theorem sin_sub_pi_div_two (x : Real) : sin (x - π / 2) = -cos x := by simp [sub_eq_add_neg, sin_add]

/--
theorem `sin_pi_div_two_sub` / 定理 `sin_pi_div_two_sub`

English:
theorem sin_pi_div_two_sub
  given: (x : Real)
  statement: sin (π / 2 - x) = cos x
  proof: by simp [sub_eq_add_neg, sin_add]

中文:
定理 sin_pi_div_two_sub
  条件: (x : 实数)
  结论: sin (π / 2 - x) = cos x
  证明: by simp [sub_eq_add_neg, sin_add]

Depends on / 依赖: sin_add, sub_eq_add_neg
-/
theorem sin_pi_div_two_sub (x : Real) : sin (π / 2 - x) = cos x := by simp [sub_eq_add_neg, sin_add]

/--
theorem `cos_add_pi_div_two` / 定理 `cos_add_pi_div_two`

English:
theorem cos_add_pi_div_two
  given: (x : Real)
  statement: cos (x + π / 2) = -sin x
  proof: by simp [cos_add]

中文:
定理 cos_add_pi_div_two
  条件: (x : 实数)
  结论: cos (x + π / 2) = -sin x
  证明: by simp [cos_add]

Depends on / 依赖: cos_add
-/
theorem cos_add_pi_div_two (x : Real) : cos (x + π / 2) = -sin x := by simp [cos_add]

/--
theorem `cos_sub_pi_div_two` / 定理 `cos_sub_pi_div_two`

English:
theorem cos_sub_pi_div_two
  given: (x : Real)
  statement: cos (x - π / 2) = sin x
  proof: by simp [sub_eq_add_neg, cos_add]

中文:
定理 cos_sub_pi_div_two
  条件: (x : 实数)
  结论: cos (x - π / 2) = sin x
  证明: by simp [sub_eq_add_neg, cos_add]

Depends on / 依赖: cos_add, sub_eq_add_neg
-/
theorem cos_sub_pi_div_two (x : Real) : cos (x - π / 2) = sin x := by simp [sub_eq_add_neg, cos_add]

/--
theorem `cos_pi_div_two_sub` / 定理 `cos_pi_div_two_sub`

English:
theorem cos_pi_div_two_sub
  given: (x : Real)
  statement: cos (π / 2 - x) = sin x
  proof: by
  rw [← cos_neg]; rw [neg_sub]; rw [cos_sub_pi_div_two]

中文:
定理 cos_pi_div_two_sub
  条件: (x : 实数)
  结论: cos (π / 2 - x) = sin x
  证明: by
  rw [← cos_neg]; rw [neg_sub]; rw [cos_sub_pi_div_two]

Depends on / 依赖: cos_neg, cos_sub_pi_div_two, neg_sub
-/
theorem cos_pi_div_two_sub (x : Real) : cos (π / 2 - x) = sin x := by
  rw [← cos_neg]; rw [neg_sub]; rw [cos_sub_pi_div_two]

/--
theorem `cos_pos_of_mem_Ioo` / 定理 `cos_pos_of_mem_Ioo`

English:
theorem cos_pos_of_mem_Ioo
  given: {x : Real} (hx : x in Ioo (-(π / 2)) (π / 2))
  statement: 0 < cos x
  proof: sin_add_pi_div_two x ▸ sin_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩

中文:
定理 cos_pos_of_mem_Ioo
  条件: {x : 实数} (hx : x in Ioo (-(π / 2)) (π / 2))
  结论: 0 < cos x
  证明: sin_add_pi_div_two x ▸ sin_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩

Depends on / 依赖: sin_add_pi_div_two, sin_pos_of_mem_Ioo
-/
theorem cos_pos_of_mem_Ioo {x : Real} (hx : x in Ioo (-(π / 2)) (π / 2)) : 0 < cos x :=
  sin_add_pi_div_two x ▸ sin_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩

/--
theorem `cos_nonneg_of_mem_Icc` / 定理 `cos_nonneg_of_mem_Icc`

English:
theorem cos_nonneg_of_mem_Icc
  given: {x : Real} (hx : x in Icc (-(π / 2)) (π / 2))
  statement: 0 <= cos x
  proof: sin_add_pi_div_two x ▸ sin_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2]⟩

中文:
定理 cos_nonneg_of_mem_Icc
  条件: {x : 实数} (hx : x in Icc (-(π / 2)) (π / 2))
  结论: 0 <= cos x
  证明: sin_add_pi_div_two x ▸ sin_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2]⟩

Depends on / 依赖: sin_add_pi_div_two, sin_nonneg_of_mem_Icc
-/
theorem cos_nonneg_of_mem_Icc {x : Real} (hx : x in Icc (-(π / 2)) (π / 2)) : 0 <= cos x :=
  sin_add_pi_div_two x ▸ sin_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2]⟩

/--
theorem `cos_nonneg_of_neg_pi_div_two_le_of_le` / 定理 `cos_nonneg_of_neg_pi_div_two_le_of_le`

English:
theorem cos_nonneg_of_neg_pi_div_two_le_of_le
  given: {x : Real} (hl : -(π / 2) <= x) (hu : x <= π / 2)
  proof: cos_nonneg_of_mem_Icc ⟨hl, hu⟩

中文:
定理 cos_nonneg_of_neg_pi_div_two_le_of_le
  条件: {x : 实数} (hl : -(π / 2) <= x) (hu : x <= π / 2)
  证明: cos_nonneg_of_mem_Icc ⟨hl, hu⟩

Depends on / 依赖: cos_nonneg_of_mem_Icc
-/
theorem cos_nonneg_of_neg_pi_div_two_le_of_le {x : Real} (hl : -(π / 2) <= x) (hu : x <= π / 2) :
    0 <= cos x :=
  cos_nonneg_of_mem_Icc ⟨hl, hu⟩

/--
theorem `cos_neg_of_pi_div_two_lt_of_lt` / 定理 `cos_neg_of_pi_div_two_lt_of_lt`

English:
theorem cos_neg_of_pi_div_two_lt_of_lt
  given: {x : Real} (hx₁ : π / 2 < x) (hx₂ : x < π + π / 2)
  proof: neg_pos.1 cos_pi_sub x ▸ cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

中文:
定理 cos_neg_of_pi_div_two_lt_of_lt
  条件: {x : 实数} (hx₁ : π / 2 < x) (hx₂ : x < π + π / 2)
  证明: neg_pos.1 cos_pi_sub x ▸ cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

Depends on / 依赖: cos_pi_sub, cos_pos_of_mem_Ioo, neg_pos
-/
theorem cos_neg_of_pi_div_two_lt_of_lt {x : Real} (hx₁ : π / 2 < x) (hx₂ : x < π + π / 2) :
    cos x < 0 :=
neg_pos.1 cos_pi_sub x ▸ cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

/--
theorem `cos_nonpos_of_pi_div_two_le_of_le` / 定理 `cos_nonpos_of_pi_div_two_le_of_le`

English:
theorem cos_nonpos_of_pi_div_two_le_of_le
  given: {x : Real} (hx₁ : π / 2 <= x) (hx₂ : x <= π + π / 2)
  proof: neg_nonneg.1 cos_pi_sub x ▸ cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩

中文:
定理 cos_nonpos_of_pi_div_two_le_of_le
  条件: {x : 实数} (hx₁ : π / 2 <= x) (hx₂ : x <= π + π / 2)
  证明: neg_nonneg.1 cos_pi_sub x ▸ cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩

Depends on / 依赖: cos_nonneg_of_mem_Icc, cos_pi_sub, neg_nonneg
-/
theorem cos_nonpos_of_pi_div_two_le_of_le {x : Real} (hx₁ : π / 2 <= x) (hx₂ : x <= π + π / 2) :
    cos x <= 0 :=
neg_nonneg.1 cos_pi_sub x ▸ cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩

/--
theorem `sin_eq_sqrt_one_sub_cos_sq` / 定理 `sin_eq_sqrt_one_sub_cos_sq`

English:
theorem sin_eq_sqrt_one_sub_cos_sq
  given: {x : Real} (hl : 0 <= x) (hu : x <= π)
  proof: by
  rw [← abs_sin_eq_sqrt_one_sub_cos_sq]; rw [abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hl hu)]

中文:
定理 sin_eq_sqrt_one_sub_cos_sq
  条件: {x : 实数} (hl : 0 <= x) (hu : x <= π)
  证明: by
  rw [← abs_sin_eq_sqrt_one_sub_cos_sq]; rw [abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hl hu)]

Depends on / 依赖: abs_of_nonneg, abs_sin_eq_sqrt_one_sub_cos_sq, sin_nonneg_of_nonneg_of_le_pi
-/
theorem sin_eq_sqrt_one_sub_cos_sq {x : Real} (hl : 0 <= x) (hu : x <= π) :
    sin x = √(1 - cos x ^ 2) := by
  rw [← abs_sin_eq_sqrt_one_sub_cos_sq]; rw [abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hl hu)]

/--
theorem `cos_eq_sqrt_one_sub_sin_sq` / 定理 `cos_eq_sqrt_one_sub_sin_sq`

English:
theorem cos_eq_sqrt_one_sub_sin_sq
  given: {x : Real} (hl : -(π / 2) <= x) (hu : x <= π / 2)
  proof: by
  rw [← abs_cos_eq_sqrt_one_sub_sin_sq]; rw [abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨hl]; rw [hu⟩)]

中文:
定理 cos_eq_sqrt_one_sub_sin_sq
  条件: {x : 实数} (hl : -(π / 2) <= x) (hu : x <= π / 2)
  证明: by
  rw [← abs_cos_eq_sqrt_one_sub_sin_sq]; rw [abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨hl]; rw [hu⟩)]

Depends on / 依赖: abs_cos_eq_sqrt_one_sub_sin_sq, abs_of_nonneg, cos_nonneg_of_mem_Icc
-/
theorem cos_eq_sqrt_one_sub_sin_sq {x : Real} (hl : -(π / 2) <= x) (hu : x <= π / 2) :
    cos x = √(1 - sin x ^ 2) := by
  rw [← abs_cos_eq_sqrt_one_sub_sin_sq]; rw [abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨hl]; rw [hu⟩)]

/--
lemma `cos_half` / 引理 `cos_half`

English:
lemma cos_half
  given: {x : Real} (hl : -π <= x) (hr : x <= π)
  statement: cos (x / 2) = √((1 + cos x) / 2)
  proof: by
have : 0 <= cos (x / 2) := cos_nonneg_of_mem_Icc by constructor <;> linarith
  rw [← sqrt_sq this]; rw [cos_sq]; rw [add_div]; rw [two_mul]; rw [add_halves]

中文:
引理 cos_half
  条件: {x : 实数} (hl : -π <= x) (hr : x <= π)
  结论: cos (x / 2) = √((1 + cos x) / 2)
  证明: by
have : 0 <= cos (x / 2) := cos_nonneg_of_mem_Icc by constructor <;> linarith
  rw [← sqrt_sq this]; rw [cos_sq]; rw [add_div]; rw [two_mul]; rw [add_halves]

Depends on / 依赖: add_div, add_halves, cos_nonneg_of_mem_Icc, cos_sq, sqrt_sq, two_mul
-/
lemma cos_half {x : Real} (hl : -π <= x) (hr : x <= π) : cos (x / 2) = √((1 + cos x) / 2) := by
have : 0 <= cos (x / 2) := cos_nonneg_of_mem_Icc by constructor <;> linarith
  rw [← sqrt_sq this]; rw [cos_sq]; rw [add_div]; rw [two_mul]; rw [add_halves]

/--
lemma `abs_sin_half` / 引理 `abs_sin_half`

English:
lemma abs_sin_half
  given: (x : Real)
  statement: |sin (x / 2)| = √((1 - cos x) / 2)
  proof: by
  rw [← sqrt_sq_eq_abs]; rw [sin_sq_eq_half_sub]; rw [two_mul]; rw [add_halves]; rw [sub_div]

中文:
引理 abs_sin_half
  条件: (x : 实数)
  结论: |sin (x / 2)| = √((1 - cos x) / 2)
  证明: by
  rw [← sqrt_sq_eq_abs]; rw [sin_sq_eq_half_sub]; rw [two_mul]; rw [add_halves]; rw [sub_div]

Depends on / 依赖: add_halves, sin_sq_eq_half_sub, sqrt_sq_eq_abs, sub_div, two_mul
-/
lemma abs_sin_half (x : Real) : |sin (x / 2)| = √((1 - cos x) / 2) := by
  rw [← sqrt_sq_eq_abs]; rw [sin_sq_eq_half_sub]; rw [two_mul]; rw [add_halves]; rw [sub_div]

/--
lemma `sin_half_eq_sqrt` / 引理 `sin_half_eq_sqrt`

English:
lemma sin_half_eq_sqrt
  given: {x : Real} (hl : 0 <= x) (hr : x <= 2 * π)
  proof: by
  rw [← abs_sin_half]; rw [abs_of_nonneg]
  apply sin_nonneg_of_nonneg_of_le_pi <;> linarith

中文:
引理 sin_half_eq_sqrt
  条件: {x : 实数} (hl : 0 <= x) (hr : x <= 2 * π)
  证明: by
  rw [← abs_sin_half]; rw [abs_of_nonneg]
  apply sin_nonneg_of_nonneg_of_le_pi <;> linarith

Depends on / 依赖: abs_of_nonneg, abs_sin_half, sin_nonneg_of_nonneg_of_le_pi
-/
lemma sin_half_eq_sqrt {x : Real} (hl : 0 <= x) (hr : x <= 2 * π) :
    sin (x / 2) = √((1 - cos x) / 2) := by
  rw [← abs_sin_half]; rw [abs_of_nonneg]
  apply sin_nonneg_of_nonneg_of_le_pi <;> linarith

/--
lemma `sin_half_eq_neg_sqrt` / 引理 `sin_half_eq_neg_sqrt`

English:
lemma sin_half_eq_neg_sqrt
  given: {x : Real} (hl : -(2 * π) <= x) (hr : x <= 0)
  proof: by
  rw [← abs_sin_half]; rw [abs_of_nonpos]; rw [neg_neg]
  apply sin_nonpos_of_nonpos_of_neg_pi_le <;> linarith

中文:
引理 sin_half_eq_neg_sqrt
  条件: {x : 实数} (hl : -(2 * π) <= x) (hr : x <= 0)
  证明: by
  rw [← abs_sin_half]; rw [abs_of_nonpos]; rw [neg_neg]
  apply sin_nonpos_of_nonpos_of_neg_pi_le <;> linarith

Depends on / 依赖: abs_of_nonpos, abs_sin_half, neg_neg, sin_nonpos_of_nonpos_of_neg_pi_le
-/
lemma sin_half_eq_neg_sqrt {x : Real} (hl : -(2 * π) <= x) (hr : x <= 0) :
    sin (x / 2) = -√((1 - cos x) / 2) := by
  rw [← abs_sin_half]; rw [abs_of_nonpos]; rw [neg_neg]
  apply sin_nonpos_of_nonpos_of_neg_pi_le <;> linarith

/--
theorem `sin_eq_zero_iff_of_lt_of_lt` / 定理 `sin_eq_zero_iff_of_lt_of_lt`

English:
theorem sin_eq_zero_iff_of_lt_of_lt
  given: {x : Real} (hx₁ : -π < x) (hx₂ : x < π)
  statement: sin x = 0 ↔ x = 0
  proof: ⟨fun h => by
    contrapose! h
    cases h.lt_or_gt with
    | inl h0 => exact (sin_neg_of_neg_of_neg_pi_lt h0 hx₁).ne
    | inr h0 => exact (sin_pos_of_pos_of_lt_pi h0 hx₂).ne',
  fun h => by simp [h]⟩

中文:
定理 sin_eq_zero_iff_of_lt_of_lt
  条件: {x : 实数} (hx₁ : -π < x) (hx₂ : x < π)
  结论: sin x = 0 ↔ x = 0
  证明: ⟨fun h => by
    contrapose! h
    cases h.lt_or_gt with
    | inl h0 => exact (sin_neg_of_neg_of_neg_pi_lt h0 hx₁).ne
    | inr h0 => exact (sin_pos_of_pos_of_lt_pi h0 hx₂).ne',
  fun h => by simp [h]⟩

Depends on / 依赖: contrapose, h.lt_or_gt, lt_or_gt, sin_neg_of_neg_of_neg_pi_lt, sin_pos_of_pos_of_lt_pi
-/
theorem sin_eq_zero_iff_of_lt_of_lt {x : Real} (hx₁ : -π < x) (hx₂ : x < π) : sin x = 0 ↔ x = 0 :=
  ⟨fun h => by
    contrapose! h
    cases h.lt_or_gt with
    | inl h0 => exact (sin_neg_of_neg_of_neg_pi_lt h0 hx₁).ne
    | inr h0 => exact (sin_pos_of_pos_of_lt_pi h0 hx₂).ne',
  fun h => by simp [h]⟩

/--
theorem `sin_eq_zero_iff` / 定理 `sin_eq_zero_iff`

English:
theorem sin_eq_zero_iff
  given: {x : Real}
  statement: sin x = 0 ↔ exists n : Int, (n : Real) * π = x
  proof: ⟨fun h =>
    ⟨⌊x / π⌋,
      le_antisymm (sub_nonneg.1 (Int.sub_floor_div_mul_nonneg _ pi_pos))
        (sub_nonpos.1 <|
          le_of_not_gt fun h₃ =>
            (sin_pos_of_pos_of_lt_pi h₃ (Int.sub_floor_div_mul_lt _ pi_pos)).ne
              (by simp [sub_eq_add_neg, sin_add, h, sin_int_mul_p

中文:
定理 sin_eq_zero_iff
  条件: {x : 实数}
  结论: sin x = 0 ↔ 存在 n : 整数, (n : 实数) * π = x
  证明: ⟨fun h =>
    ⟨⌊x / π⌋,
      le_antisymm (sub_nonneg.1 (Int.sub_floor_div_mul_nonneg _ pi_pos))
        (sub_nonpos.1 <|
          le_of_not_gt fun h₃ =>
            (sin_pos_of_pos_of_lt_pi h₃ (Int.sub_floor_div_mul_lt _ pi_pos)).ne
              (by simp [sub_eq_add_neg, sin_add, h, sin_int_mul_p

Depends on / 依赖: Int.sub_floor_div_mul_lt, Int.sub_floor_div_mul_nonneg, le_antisymm, le_of_not_gt, pi_pos, sin_add, sin_int_mul_pi, sin_pos_of_pos_of_lt_pi, sub_eq_add_neg, sub_floor_div_mul_lt, sub_floor_div_mul_nonneg, sub_nonneg, sub_nonpos
-/
theorem sin_eq_zero_iff {x : Real} : sin x = 0 ↔ exists n : Int, (n : Real) * π = x :=
  ⟨fun h =>
    ⟨⌊x / π⌋,
      le_antisymm (sub_nonneg.1 (Int.sub_floor_div_mul_nonneg _ pi_pos))
        (sub_nonpos.1 <|
          le_of_not_gt fun h₃ =>
            (sin_pos_of_pos_of_lt_pi h₃ (Int.sub_floor_div_mul_lt _ pi_pos)).ne
              (by simp [sub_eq_add_neg, sin_add, h, sin_int_mul_pi]))⟩,
    fun ⟨_, hn⟩ => hn ▸ sin_int_mul_pi _⟩

/--
theorem `sin_ne_zero_iff` / 定理 `sin_ne_zero_iff`

English:
theorem sin_ne_zero_iff
  given: {x : Real}
  statement: sin x != 0 ↔ forall n : Int, (n : Real) * π != x
  proof: by
  contrapose!; exact sin_eq_zero_iff

中文:
定理 sin_ne_zero_iff
  条件: {x : 实数}
  结论: sin x != 0 ↔ 对任意 n : 整数, (n : 实数) * π != x
  证明: by
  contrapose!; exact sin_eq_zero_iff

Depends on / 依赖: contrapose, sin_eq_zero_iff
-/
theorem sin_ne_zero_iff {x : Real} : sin x != 0 ↔ forall n : Int, (n : Real) * π != x := by
  contrapose!; exact sin_eq_zero_iff

/--
theorem `sin_eq_zero_iff_cos_eq` / 定理 `sin_eq_zero_iff_cos_eq`

English:
theorem sin_eq_zero_iff_cos_eq
  given: {x : Real}
  statement: sin x = 0 ↔ cos x = 1 ∨ cos x = -1
  proof: by
  rw [← mul_self_eq_one_iff]; rw [← sin_sq_add_cos_sq]; rw [sq]; rw [sq]; rw [right_eq_add]; rw [mul_eq_zero]; rw [or_self]

中文:
定理 sin_eq_zero_iff_cos_eq
  条件: {x : 实数}
  结论: sin x = 0 ↔ cos x = 1 ∨ cos x = -1
  证明: by
  rw [← mul_self_eq_one_iff]; rw [← sin_sq_add_cos_sq]; rw [sq]; rw [sq]; rw [right_eq_add]; rw [mul_eq_zero]; rw [or_self]

Depends on / 依赖: mul_eq_zero, mul_self_eq_one_iff, or_self, right_eq_add, sin_sq_add_cos_sq
-/
theorem sin_eq_zero_iff_cos_eq {x : Real} : sin x = 0 ↔ cos x = 1 ∨ cos x = -1 := by
  rw [← mul_self_eq_one_iff]; rw [← sin_sq_add_cos_sq]; rw [sq]; rw [sq]; rw [right_eq_add]; rw [mul_eq_zero]; rw [or_self]

/--
theorem `cos_eq_zero_iff_sin_eq` / 定理 `cos_eq_zero_iff_sin_eq`

English:
theorem cos_eq_zero_iff_sin_eq
  given: {x : Real}
  statement: cos x = 0 ↔ sin x = 1 ∨ sin x = -1
  proof: by
  rw [← mul_self_eq_one_iff]; rw [← sin_sq_add_cos_sq]; rw [sq]; rw [sq]; rw [left_eq_add]; rw [mul_eq_zero]; rw [or_self]

中文:
定理 cos_eq_zero_iff_sin_eq
  条件: {x : 实数}
  结论: cos x = 0 ↔ sin x = 1 ∨ sin x = -1
  证明: by
  rw [← mul_self_eq_one_iff]; rw [← sin_sq_add_cos_sq]; rw [sq]; rw [sq]; rw [left_eq_add]; rw [mul_eq_zero]; rw [or_self]

Depends on / 依赖: left_eq_add, mul_eq_zero, mul_self_eq_one_iff, or_self, sin_sq_add_cos_sq
-/
theorem cos_eq_zero_iff_sin_eq {x : Real} : cos x = 0 ↔ sin x = 1 ∨ sin x = -1 := by
  rw [← mul_self_eq_one_iff]; rw [← sin_sq_add_cos_sq]; rw [sq]; rw [sq]; rw [left_eq_add]; rw [mul_eq_zero]; rw [or_self]

/--
theorem `cos_eq_one_iff` / 定理 `cos_eq_one_iff`

English:
theorem cos_eq_one_iff
  given: (x : Real)
  statement: cos x = 1 ↔ exists n : Int, (n : Real) * (2 * π) = x
  proof: ⟨fun h =>
    let ⟨n, hn⟩ := sin_eq_zero_iff.1 (sin_eq_zero_iff_cos_eq.2 (Or.inl h))
    ⟨n / 2,
      (Int.emod_two_eq_zero_or_one n).elim
        (fun hn0 => by
          rwa [← mul_assoc, ← @Int.cast_two Real, ← Int.cast_mul,
            Int.ediv_mul_cancel (Int.dvd_iff_emod_eq_zero.2 hn0)])
    

中文:
定理 cos_eq_one_iff
  条件: (x : 实数)
  结论: cos x = 1 ↔ 存在 n : 整数, (n : 实数) * (2 * π) = x
  证明: ⟨fun h =>
    let ⟨n, hn⟩ := sin_eq_zero_iff.1 (sin_eq_zero_iff_cos_eq.2 (Or.inl h))
    ⟨n / 2,
      (Int.emod_two_eq_zero_or_one n).elim
        (fun hn0 => by
          rwa [← mul_assoc, ← @Int.cast_two Real, ← Int.cast_mul,
            Int.ediv_mul_cancel (Int.dvd_iff_emod_eq_zero.2 hn0)])
    

Depends on / 依赖: Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_two, Int.dvd_iff_emod_eq_zero, Int.ediv_mul_cancel, Int.emod_add_mul_ediv, Int.emod_two_eq_zero_or_one, Or.inl, add_comm, add_mul, cast_add, cast_mul, cast_one, cast_two, cos_int_mu, dvd_iff_emod_eq_zero, ediv_mul_cancel, emod_add_mul_ediv, emod_two_eq_zero_or_one
-/
theorem cos_eq_one_iff (x : Real) : cos x = 1 ↔ exists n : Int, (n : Real) * (2 * π) = x :=
  ⟨fun h =>
    let ⟨n, hn⟩ := sin_eq_zero_iff.1 (sin_eq_zero_iff_cos_eq.2 (Or.inl h))
    ⟨n / 2,
      (Int.emod_two_eq_zero_or_one n).elim
        (fun hn0 => by
          rwa [← mul_assoc, ← @Int.cast_two Real, ← Int.cast_mul,
            Int.ediv_mul_cancel (Int.dvd_iff_emod_eq_zero.2 hn0)])
        fun hn1 => by
        rw [← Int.emod_add_mul_ediv n 2]; rw [hn1]; rw [Int.cast_add]; rw [Int.cast_one]; rw [add_mul]; rw [one_mul]; rw [add_comm]; rw [mul_comm (2 : Int)]; rw [Int.cast_mul]; rw [mul_assoc]; rw [Int.cast_two] at hn
        rw [← hn]; rw [cos_int_mul_two_pi_add_pi] at h
        exact absurd h (by norm_num)⟩,
    fun ⟨_, hn⟩ => hn ▸ cos_int_mul_two_pi _⟩

/--
theorem `cos_eq_one_iff_of_lt_of_lt` / 定理 `cos_eq_one_iff_of_lt_of_lt`

English:
theorem cos_eq_one_iff_of_lt_of_lt
  given: {x : Real} (hx₁ : -(2 * π) < x) (hx₂ : x < 2 * π)
  proof: ⟨fun h => by
    rcases (cos_eq_one_iff _).1 h with ⟨n, rfl⟩
    rw [mul_lt_iff_lt_one_left two_pi_pos] at hx₂
    rw [neg_lt]; rw [neg_mul_eq_neg_mul]; rw [mul_lt_iff_lt_one_left two_pi_pos] at hx₁
    norm_cast at hx₁ hx₂
    obtain rfl : n = 0 := le_antisymm (by lia) (by lia)
    simp, fun h => b

中文:
定理 cos_eq_one_iff_of_lt_of_lt
  条件: {x : 实数} (hx₁ : -(2 * π) < x) (hx₂ : x < 2 * π)
  证明: ⟨fun h => by
    rcases (cos_eq_one_iff _).1 h with ⟨n, rfl⟩
    rw [mul_lt_iff_lt_one_left two_pi_pos] at hx₂
    rw [neg_lt]; rw [neg_mul_eq_neg_mul]; rw [mul_lt_iff_lt_one_left two_pi_pos] at hx₁
    norm_cast at hx₁ hx₂
    obtain rfl : n = 0 := le_antisymm (by lia) (by lia)
    simp, fun h => b

Depends on / 依赖: cos_eq_one_iff, le_antisymm, mul_lt_iff_lt_one_left, neg_lt, neg_mul_eq_neg_mul, two_pi_pos
-/
theorem cos_eq_one_iff_of_lt_of_lt {x : Real} (hx₁ : -(2 * π) < x) (hx₂ : x < 2 * π) :
    cos x = 1 ↔ x = 0 :=
  ⟨fun h => by
    rcases (cos_eq_one_iff _).1 h with ⟨n, rfl⟩
    rw [mul_lt_iff_lt_one_left two_pi_pos] at hx₂
    rw [neg_lt]; rw [neg_mul_eq_neg_mul]; rw [mul_lt_iff_lt_one_left two_pi_pos] at hx₁
    norm_cast at hx₁ hx₂
    obtain rfl : n = 0 := le_antisymm (by lia) (by lia)
    simp, fun h => by simp [h]⟩

/--
theorem `sin_lt_sin_of_lt_of_le_pi_div_two` / 定理 `sin_lt_sin_of_lt_of_le_pi_div_two`

English:
theorem sin_lt_sin_of_lt_of_le_pi_div_two
  statement: {x y : Real} (hx₁ : -(π / 2) <= x) (hy₂ : y <= π / 2)
  proof: by
  rw [← sub_pos]; rw [sin_sub_sin]
  have : 0 < sin ((y - x) / 2) := by apply sin_pos_of_pos_of_lt_pi <;> linarith
  have : 0 < cos ((y + x) / 2) := by refine cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;> linarith
  positivity

中文:
定理 sin_lt_sin_of_lt_of_le_pi_div_two
  结论: {x y : 实数} (hx₁ : -(π / 2) <= x) (hy₂ : y <= π / 2)
  证明: by
  rw [← sub_pos]; rw [sin_sub_sin]
  have : 0 < sin ((y - x) / 2) := by apply sin_pos_of_pos_of_lt_pi <;> linarith
  have : 0 < cos ((y + x) / 2) := by refine cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;> linarith
  positivity

Depends on / 依赖: cos_pos_of_mem_Ioo, sin_pos_of_pos_of_lt_pi, sin_sub_sin, sub_pos
-/
theorem sin_lt_sin_of_lt_of_le_pi_div_two {x y : Real} (hx₁ : -(π / 2) <= x) (hy₂ : y <= π / 2)
    (hxy : x < y) : sin x < sin y := by
  rw [← sub_pos]; rw [sin_sub_sin]
  have : 0 < sin ((y - x) / 2) := by apply sin_pos_of_pos_of_lt_pi <;> linarith
  have : 0 < cos ((y + x) / 2) := by refine cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;> linarith
  positivity

/--
theorem `strictMonoOn_sin` / 定理 `strictMonoOn_sin`

English:
theorem strictMonoOn_sin
  statement: StrictMonoOn sin (Icc (-(π / 2)) (π / 2))
  proof: fun _ hx _ hy hxy =>
  sin_lt_sin_of_lt_of_le_pi_div_two hx.1 hy.2 hxy

中文:
定理 strictMonoOn_sin
  结论: StrictMonoOn sin (Icc (-(π / 2)) (π / 2))
  证明: fun _ hx _ hy hxy =>
  sin_lt_sin_of_lt_of_le_pi_div_two hx.1 hy.2 hxy
-/
theorem strictMonoOn_sin : StrictMonoOn sin (Icc (-(π / 2)) (π / 2)) := fun _ hx _ hy hxy =>
  sin_lt_sin_of_lt_of_le_pi_div_two hx.1 hy.2 hxy

/--
theorem `monotoneOn_sin` / 定理 `monotoneOn_sin`

English:
theorem monotoneOn_sin
  statement: MonotoneOn sin (Set.Icc (-(π / 2)) (π / 2))
  proof: strictMonoOn_sin.monotoneOn

中文:
定理 monotoneOn_sin
  结论: MonotoneOn sin (Set.Icc (-(π / 2)) (π / 2))
  证明: strictMonoOn_sin.monotoneOn

Depends on / 依赖: monotoneOn, strictMonoOn_sin, strictMonoOn_sin.monotoneOn
-/
theorem monotoneOn_sin : MonotoneOn sin (Set.Icc (-(π / 2)) (π / 2)) :=
  strictMonoOn_sin.monotoneOn

/--
theorem `cos_lt_cos_of_nonneg_of_le_pi` / 定理 `cos_lt_cos_of_nonneg_of_le_pi`

English:
theorem cos_lt_cos_of_nonneg_of_le_pi
  given: {x y : Real} (hx₁ : 0 <= x) (hy₂ : y <= π) (hxy : x < y)
  proof: by
  rw [← sin_pi_div_two_sub]; rw [← sin_pi_div_two_sub]
  apply sin_lt_sin_of_lt_of_le_pi_div_two <;> linarith

中文:
定理 cos_lt_cos_of_nonneg_of_le_pi
  条件: {x y : 实数} (hx₁ : 0 <= x) (hy₂ : y <= π) (hxy : x < y)
  证明: by
  rw [← sin_pi_div_two_sub]; rw [← sin_pi_div_two_sub]
  apply sin_lt_sin_of_lt_of_le_pi_div_two <;> linarith

Depends on / 依赖: sin_lt_sin_of_lt_of_le_pi_div_two, sin_pi_div_two_sub
-/
theorem cos_lt_cos_of_nonneg_of_le_pi {x y : Real} (hx₁ : 0 <= x) (hy₂ : y <= π) (hxy : x < y) :
    cos y < cos x := by
  rw [← sin_pi_div_two_sub]; rw [← sin_pi_div_two_sub]
  apply sin_lt_sin_of_lt_of_le_pi_div_two <;> linarith

/--
theorem `cos_lt_cos_of_nonneg_of_le_pi_div_two` / 定理 `cos_lt_cos_of_nonneg_of_le_pi_div_two`

English:
theorem cos_lt_cos_of_nonneg_of_le_pi_div_two
  statement: {x y : Real} (hx₁ : 0 <= x) (hy₂ : y <= π / 2)
  proof: cos_lt_cos_of_nonneg_of_le_pi hx₁ (hy₂.trans (by linarith)) hxy

中文:
定理 cos_lt_cos_of_nonneg_of_le_pi_div_two
  结论: {x y : 实数} (hx₁ : 0 <= x) (hy₂ : y <= π / 2)
  证明: cos_lt_cos_of_nonneg_of_le_pi hx₁ (hy₂.trans (by linarith)) hxy

Depends on / 依赖: cos_lt_cos_of_nonneg_of_le_pi
-/
theorem cos_lt_cos_of_nonneg_of_le_pi_div_two {x y : Real} (hx₁ : 0 <= x) (hy₂ : y <= π / 2)
    (hxy : x < y) : cos y < cos x :=
  cos_lt_cos_of_nonneg_of_le_pi hx₁ (hy₂.trans (by linarith)) hxy

/--
theorem `strictAntiOn_cos` / 定理 `strictAntiOn_cos`

English:
theorem strictAntiOn_cos
  statement: StrictAntiOn cos (Icc 0 π)
  proof: fun _ hx _ hy hxy =>
  cos_lt_cos_of_nonneg_of_le_pi hx.1 hy.2 hxy

中文:
定理 strictAntiOn_cos
  结论: StrictAntiOn cos (Icc 0 π)
  证明: fun _ hx _ hy hxy =>
  cos_lt_cos_of_nonneg_of_le_pi hx.1 hy.2 hxy
-/
theorem strictAntiOn_cos : StrictAntiOn cos (Icc 0 π) := fun _ hx _ hy hxy =>
  cos_lt_cos_of_nonneg_of_le_pi hx.1 hy.2 hxy

/--
theorem `antitoneOn_cos` / 定理 `antitoneOn_cos`

English:
theorem antitoneOn_cos
  statement: AntitoneOn cos (Set.Icc 0 π)
  proof: strictAntiOn_cos.antitoneOn

中文:
定理 antitoneOn_cos
  结论: AntitoneOn cos (Set.Icc 0 π)
  证明: strictAntiOn_cos.antitoneOn

Depends on / 依赖: antitoneOn, strictAntiOn_cos, strictAntiOn_cos.antitoneOn
-/
theorem antitoneOn_cos : AntitoneOn cos (Set.Icc 0 π) :=
  strictAntiOn_cos.antitoneOn

/--
theorem `cos_le_cos_of_nonneg_of_le_pi` / 定理 `cos_le_cos_of_nonneg_of_le_pi`

English:
theorem cos_le_cos_of_nonneg_of_le_pi
  given: {x y : Real} (hx₁ : 0 <= x) (hy₂ : y <= π) (hxy : x <= y)
  proof: (strictAntiOn_cos.le_iff_ge ⟨hx₁.trans hxy, hy₂⟩ ⟨hx₁, hxy.trans hy₂⟩).2 hxy

中文:
定理 cos_le_cos_of_nonneg_of_le_pi
  条件: {x y : 实数} (hx₁ : 0 <= x) (hy₂ : y <= π) (hxy : x <= y)
  证明: (strictAntiOn_cos.le_iff_ge ⟨hx₁.trans hxy, hy₂⟩ ⟨hx₁, hxy.trans hy₂⟩).2 hxy

Depends on / 依赖: hxy.trans, le_iff_ge, strictAntiOn_cos, strictAntiOn_cos.le_iff_ge
-/
theorem cos_le_cos_of_nonneg_of_le_pi {x y : Real} (hx₁ : 0 <= x) (hy₂ : y <= π) (hxy : x <= y) :
    cos y <= cos x :=
  (strictAntiOn_cos.le_iff_ge ⟨hx₁.trans hxy, hy₂⟩ ⟨hx₁, hxy.trans hy₂⟩).2 hxy

/--
theorem `sin_le_sin_of_le_of_le_pi_div_two` / 定理 `sin_le_sin_of_le_of_le_pi_div_two`

English:
theorem sin_le_sin_of_le_of_le_pi_div_two
  statement: {x y : Real} (hx₁ : -(π / 2) <= x) (hy₂ : y <= π / 2)
  proof: (strictMonoOn_sin.le_iff_le ⟨hx₁, hxy.trans hy₂⟩ ⟨hx₁.trans hxy, hy₂⟩).2 hxy

中文:
定理 sin_le_sin_of_le_of_le_pi_div_two
  结论: {x y : 实数} (hx₁ : -(π / 2) <= x) (hy₂ : y <= π / 2)
  证明: (strictMonoOn_sin.le_iff_le ⟨hx₁, hxy.trans hy₂⟩ ⟨hx₁.trans hxy, hy₂⟩).2 hxy

Depends on / 依赖: hxy.trans, le_iff_le, strictMonoOn_sin, strictMonoOn_sin.le_iff_le
-/
theorem sin_le_sin_of_le_of_le_pi_div_two {x y : Real} (hx₁ : -(π / 2) <= x) (hy₂ : y <= π / 2)
    (hxy : x <= y) : sin x <= sin y :=
  (strictMonoOn_sin.le_iff_le ⟨hx₁, hxy.trans hy₂⟩ ⟨hx₁.trans hxy, hy₂⟩).2 hxy

/--
theorem `injOn_sin` / 定理 `injOn_sin`

English:
theorem injOn_sin
  statement: InjOn sin (Icc (-(π / 2)) (π / 2))
  proof: strictMonoOn_sin.injOn

中文:
定理 injOn_sin
  结论: InjOn sin (Icc (-(π / 2)) (π / 2))
  证明: strictMonoOn_sin.injOn

Depends on / 依赖: strictMonoOn_sin, strictMonoOn_sin.injOn
-/
theorem injOn_sin : InjOn sin (Icc (-(π / 2)) (π / 2)) :=
  strictMonoOn_sin.injOn

/--
theorem `injOn_cos` / 定理 `injOn_cos`

English:
theorem injOn_cos
  statement: InjOn cos (Icc 0 π)
  proof: strictAntiOn_cos.injOn

中文:
定理 injOn_cos
  结论: InjOn cos (Icc 0 π)
  证明: strictAntiOn_cos.injOn

Depends on / 依赖: strictAntiOn_cos, strictAntiOn_cos.injOn
-/
theorem injOn_cos : InjOn cos (Icc 0 π) :=
  strictAntiOn_cos.injOn

/--
theorem `surjOn_sin` / 定理 `surjOn_sin`

English:
theorem surjOn_sin
  statement: SurjOn sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1)
  proof: by
  simpa only [sin_neg, sin_pi_div_two] using!
    intermediate_value_Icc (neg_le_self pi_div_two_pos.le) continuous_sin.continuousOn

中文:
定理 surjOn_sin
  结论: SurjOn sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1)
  证明: by
  simpa only [sin_neg, sin_pi_div_two] using!
    intermediate_value_Icc (neg_le_self pi_div_two_pos.le) continuous_sin.continuousOn

Depends on / 依赖: continuousOn, continuous_sin, continuous_sin.continuousOn, intermediate_value_Icc, neg_le_self, pi_div_two_pos, pi_div_two_pos.le, sin_neg, sin_pi_div_two
-/
theorem surjOn_sin : SurjOn sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1) := by
  simpa only [sin_neg, sin_pi_div_two] using!
    intermediate_value_Icc (neg_le_self pi_div_two_pos.le) continuous_sin.continuousOn

/--
theorem `surjOn_cos` / 定理 `surjOn_cos`

English:
theorem surjOn_cos
  statement: SurjOn cos (Icc 0 π) (Icc (-1) 1)
  proof: by
  simpa only [cos_zero, cos_pi] using! intermediate_value_Icc' pi_pos.le continuous_cos.continuousOn

中文:
定理 surjOn_cos
  结论: SurjOn cos (Icc 0 π) (Icc (-1) 1)
  证明: by
  simpa only [cos_zero, cos_pi] using! intermediate_value_Icc' pi_pos.le continuous_cos.continuousOn

Depends on / 依赖: continuousOn, continuous_cos, continuous_cos.continuousOn, cos_pi, cos_zero, intermediate_value_Icc, pi_pos, pi_pos.le
-/
theorem surjOn_cos : SurjOn cos (Icc 0 π) (Icc (-1) 1) := by
  simpa only [cos_zero, cos_pi] using! intermediate_value_Icc' pi_pos.le continuous_cos.continuousOn

/--
theorem `sin_mem_Icc` / 定理 `sin_mem_Icc`

English:
theorem sin_mem_Icc
  given: (x : Real)
  statement: sin x in Icc (-1 : Real) 1
  proof: ⟨neg_one_le_sin x, sin_le_one x⟩

中文:
定理 sin_mem_Icc
  条件: (x : 实数)
  结论: sin x in Icc (-1 : 实数) 1
  证明: ⟨neg_one_le_sin x, sin_le_one x⟩

Depends on / 依赖: neg_one_le_sin, sin_le_one
-/
theorem sin_mem_Icc (x : Real) : sin x in Icc (-1 : Real) 1 :=
  ⟨neg_one_le_sin x, sin_le_one x⟩

/--
theorem `cos_mem_Icc` / 定理 `cos_mem_Icc`

English:
theorem cos_mem_Icc
  given: (x : Real)
  statement: cos x in Icc (-1 : Real) 1
  proof: ⟨neg_one_le_cos x, cos_le_one x⟩

中文:
定理 cos_mem_Icc
  条件: (x : 实数)
  结论: cos x in Icc (-1 : 实数) 1
  证明: ⟨neg_one_le_cos x, cos_le_one x⟩

Depends on / 依赖: cos_le_one, neg_one_le_cos
-/
theorem cos_mem_Icc (x : Real) : cos x in Icc (-1 : Real) 1 :=
  ⟨neg_one_le_cos x, cos_le_one x⟩

/--
theorem `mapsTo_sin` / 定理 `mapsTo_sin`

English:
theorem mapsTo_sin
  given: (s : Set Real)
  statement: MapsTo sin s (Icc (-1 : Real) 1)
  proof: fun x _ => sin_mem_Icc x

中文:
定理 mapsTo_sin
  条件: (s : Set 实数)
  结论: MapsTo sin s (Icc (-1 : 实数) 1)
  证明: fun x _ => sin_mem_Icc x

Depends on / 依赖: sin_mem_Icc
-/
theorem mapsTo_sin (s : Set Real) : MapsTo sin s (Icc (-1 : Real) 1) := fun x _ => sin_mem_Icc x

/--
theorem `mapsTo_cos` / 定理 `mapsTo_cos`

English:
theorem mapsTo_cos
  given: (s : Set Real)
  statement: MapsTo cos s (Icc (-1 : Real) 1)
  proof: fun x _ => cos_mem_Icc x

中文:
定理 mapsTo_cos
  条件: (s : Set 实数)
  结论: MapsTo cos s (Icc (-1 : 实数) 1)
  证明: fun x _ => cos_mem_Icc x

Depends on / 依赖: cos_mem_Icc
-/
theorem mapsTo_cos (s : Set Real) : MapsTo cos s (Icc (-1 : Real) 1) := fun x _ => cos_mem_Icc x

/--
theorem `bijOn_sin` / 定理 `bijOn_sin`

English:
theorem bijOn_sin
  statement: BijOn sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1)
  proof: ⟨mapsTo_sin _, injOn_sin, surjOn_sin⟩

中文:
定理 bijOn_sin
  结论: BijOn sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1)
  证明: ⟨mapsTo_sin _, injOn_sin, surjOn_sin⟩

Depends on / 依赖: injOn_sin, mapsTo_sin, surjOn_sin
-/
theorem bijOn_sin : BijOn sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1) :=
  ⟨mapsTo_sin _, injOn_sin, surjOn_sin⟩

/--
theorem `bijOn_cos` / 定理 `bijOn_cos`

English:
theorem bijOn_cos
  statement: BijOn cos (Icc 0 π) (Icc (-1) 1)
  proof: ⟨mapsTo_cos _, injOn_cos, surjOn_cos⟩

@[simp]

中文:
定理 bijOn_cos
  结论: BijOn cos (Icc 0 π) (Icc (-1) 1)
  证明: ⟨mapsTo_cos _, injOn_cos, surjOn_cos⟩

@[simp]

Depends on / 依赖: injOn_cos, mapsTo_cos, surjOn_cos
-/
theorem bijOn_cos : BijOn cos (Icc 0 π) (Icc (-1) 1) :=
  ⟨mapsTo_cos _, injOn_cos, surjOn_cos⟩

@[simp]
/--
theorem `range_cos` / 定理 `range_cos`

English:
theorem range_cos
  statement: range cos = (Icc (-1) 1 : Set Real)
  proof: Subset.antisymm (range_subset_iff.2 cos_mem_Icc) surjOn_cos.subset_range

@[simp]

中文:
定理 range_cos
  结论: range cos = (Icc (-1) 1 : Set 实数)
  证明: Subset.antisymm (range_subset_iff.2 cos_mem_Icc) surjOn_cos.subset_range

@[simp]

Depends on / 依赖: Subset, Subset.antisymm, antisymm, cos_mem_Icc, range_subset_iff, subset_range, surjOn_cos, surjOn_cos.subset_range
-/
theorem range_cos : range cos = (Icc (-1) 1 : Set Real) :=
  Subset.antisymm (range_subset_iff.2 cos_mem_Icc) surjOn_cos.subset_range

@[simp]
/--
theorem `range_sin` / 定理 `range_sin`

English:
theorem range_sin
  statement: range sin = (Icc (-1) 1 : Set Real)
  proof: Subset.antisymm (range_subset_iff.2 sin_mem_Icc) surjOn_sin.subset_range

中文:
定理 range_sin
  结论: range sin = (Icc (-1) 1 : Set 实数)
  证明: Subset.antisymm (range_subset_iff.2 sin_mem_Icc) surjOn_sin.subset_range

Depends on / 依赖: Subset, Subset.antisymm, antisymm, range_subset_iff, sin_mem_Icc, subset_range, surjOn_sin, surjOn_sin.subset_range
-/
theorem range_sin : range sin = (Icc (-1) 1 : Set Real) :=
  Subset.antisymm (range_subset_iff.2 sin_mem_Icc) surjOn_sin.subset_range

/--
theorem `range_cos_infinite` / 定理 `range_cos_infinite`

English:
theorem range_cos_infinite
  statement: (range Real.cos).Infinite
  proof: by
  rw [Real.range_cos]
  exact Icc_infinite (by simp)

中文:
定理 range_cos_infinite
  结论: (range 实数.cos).Infinite
  证明: by
  rw [Real.range_cos]
  exact Icc_infinite (by simp)

Depends on / 依赖: Icc_infinite, Real.range_cos, range_cos
-/
theorem range_cos_infinite : (range Real.cos).Infinite := by
  rw [Real.range_cos]
  exact Icc_infinite (by simp)

/--
theorem `range_sin_infinite` / 定理 `range_sin_infinite`

English:
theorem range_sin_infinite
  statement: (range Real.sin).Infinite
  proof: by
  rw [Real.range_sin]
  exact Icc_infinite (by simp)

中文:
定理 range_sin_infinite
  结论: (range 实数.sin).Infinite
  证明: by
  rw [Real.range_sin]
  exact Icc_infinite (by simp)

Depends on / 依赖: Icc_infinite, Real.range_sin, range_sin
-/
theorem range_sin_infinite : (range Real.sin).Infinite := by
  rw [Real.range_sin]
  exact Icc_infinite (by simp)

section CosDivSq

variable (x : Real)

/-- the series `sqrtTwoAddSeries x n` is `sqrt(2 + sqrt(2 + ... ))` with `n` square roots,
  starting with `x`. We define it here because `cos (pi / 2 ^ (n+1)) = sqrtTwoAddSeries 0 n / 2`
-/
@[simp]
/--
Definition of `sqrtTwoAddSeries` / `sqrtTwoAddSeries` 的定义

English:
definition sqrtTwoAddSeries
  signature: (x : Real)

中文:
定义 sqrtTwoAddSeries
  签名: (x : 实数)
-/
noncomputable def sqrtTwoAddSeries (x : Real) : Nat -> Real
  | 0 => x
  | n + 1 => √(2 + sqrtTwoAddSeries x n)

/--
theorem `sqrtTwoAddSeries_zero` / 定理 `sqrtTwoAddSeries_zero`

English:
theorem sqrtTwoAddSeries_zero
  statement: sqrtTwoAddSeries x 0 = x
  proof: by simp

中文:
定理 sqrtTwoAddSeries_zero
  结论: sqrtTwoAddSeries x 0 = x
  证明: by simp
-/
theorem sqrtTwoAddSeries_zero : sqrtTwoAddSeries x 0 = x := by simp

/--
theorem `sqrtTwoAddSeries_one` / 定理 `sqrtTwoAddSeries_one`

English:
theorem sqrtTwoAddSeries_one
  statement: sqrtTwoAddSeries 0 1 = √2
  proof: by simp

中文:
定理 sqrtTwoAddSeries_one
  结论: sqrtTwoAddSeries 0 1 = √2
  证明: by simp
-/
theorem sqrtTwoAddSeries_one : sqrtTwoAddSeries 0 1 = √2 := by simp

/--
theorem `sqrtTwoAddSeries_two` / 定理 `sqrtTwoAddSeries_two`

English:
theorem sqrtTwoAddSeries_two
  statement: sqrtTwoAddSeries 0 2 = √(2 + √2)
  proof: by simp

中文:
定理 sqrtTwoAddSeries_two
  结论: sqrtTwoAddSeries 0 2 = √(2 + √2)
  证明: by simp
-/
theorem sqrtTwoAddSeries_two : sqrtTwoAddSeries 0 2 = √(2 + √2) := by simp

/--
theorem `sqrtTwoAddSeries_zero_nonneg` / 定理 `sqrtTwoAddSeries_zero_nonneg`

English:
theorem sqrtTwoAddSeries_zero_nonneg
  statement: forall n : Nat, 0 <= sqrtTwoAddSeries 0 n

中文:
定理 sqrtTwoAddSeries_zero_nonneg
  结论: 对任意 n : 自然数, 0 <= sqrtTwoAddSeries 0 n
-/
theorem sqrtTwoAddSeries_zero_nonneg : forall n : Nat, 0 <= sqrtTwoAddSeries 0 n
  | 0 => le_refl 0
  | _ + 1 => sqrt_nonneg _

/--
theorem `sqrtTwoAddSeries_nonneg` / 定理 `sqrtTwoAddSeries_nonneg`

English:
theorem sqrtTwoAddSeries_nonneg
  given: {x : Real} (h : 0 <= x)
  statement: forall n : Nat, 0 <= sqrtTwoAddSeries x n

中文:
定理 sqrtTwoAddSeries_nonneg
  条件: {x : 实数} (h : 0 <= x)
  结论: 对任意 n : 自然数, 0 <= sqrtTwoAddSeries x n
-/
theorem sqrtTwoAddSeries_nonneg {x : Real} (h : 0 <= x) : forall n : Nat, 0 <= sqrtTwoAddSeries x n
  | 0 => h
  | _ + 1 => sqrt_nonneg _

/--
theorem `sqrtTwoAddSeries_lt_two` / 定理 `sqrtTwoAddSeries_lt_two`

English:
theorem sqrtTwoAddSeries_lt_two
  statement: forall n : Nat, sqrtTwoAddSeries 0 n < 2

中文:
定理 sqrtTwoAddSeries_lt_two
  结论: 对任意 n : 自然数, sqrtTwoAddSeries 0 n < 2
-/
theorem sqrtTwoAddSeries_lt_two : forall n : Nat, sqrtTwoAddSeries 0 n < 2
  | 0 => by simp
  | n + 1 => by
    refine lt_of_lt_of_le ?_ (sqrt_sq zero_lt_two.le).le
    rw [sqrtTwoAddSeries]; rw [sqrt_lt_sqrt_iff]; rw [← lt_sub_iff_add_lt']
    · refine (sqrtTwoAddSeries_lt_two n).trans_le ?_
      norm_num
    · exact add_nonneg zero_le_two (sqrtTwoAddSeries_zero_nonneg n)

/--
theorem `sqrtTwoAddSeries_succ` / 定理 `sqrtTwoAddSeries_succ`

English:
theorem sqrtTwoAddSeries_succ
  given: (x : Real)

中文:
定理 sqrtTwoAddSeries_succ
  条件: (x : 实数)
-/
theorem sqrtTwoAddSeries_succ (x : Real) :
    forall n : Nat, sqrtTwoAddSeries x (n + 1) = sqrtTwoAddSeries (√(2 + x)) n
  | 0 => rfl
  | n + 1 => by rw [sqrtTwoAddSeries, sqrtTwoAddSeries_succ _ _, sqrtTwoAddSeries]

@[gcongr]
/--
theorem `sqrtTwoAddSeries_monotone_left` / 定理 `sqrtTwoAddSeries_monotone_left`

English:
theorem sqrtTwoAddSeries_monotone_left
  given: {x y : Real} (h : x <= y)

中文:
定理 sqrtTwoAddSeries_monotone_left
  条件: {x y : 实数} (h : x <= y)
-/
theorem sqrtTwoAddSeries_monotone_left {x y : Real} (h : x <= y) :
    forall n : Nat, sqrtTwoAddSeries x n <= sqrtTwoAddSeries y n
  | 0 => h
  | n + 1 => by
    rw [sqrtTwoAddSeries]; rw [sqrtTwoAddSeries]; gcongr; exact sqrtTwoAddSeries_monotone_left h _

@[simp]
/--
theorem `cos_pi_over_two_pow` / 定理 `cos_pi_over_two_pow`

English:
theorem cos_pi_over_two_pow
  statement: forall n : Nat, cos (π / 2 ^ (n + 1)) = sqrtTwoAddSeries 0 n / 2
  proof: one_lt_pow₀ one_lt_two n.succ_ne_zero
    have B : π / 2 ^ (n + 1) < π := div_lt_self pi_pos A
    have C : 0 < π / 2 ^ (n + 1) := by positivity
    rw [pow_succ]; rw [div_mul_eq_div_div]; rw [cos_half]; rw [cos_pi_over_two_pow n]; rw [sqrtTwoAddSeries]; rw [add_div_eq_mul_add_div]; rw [one_mul]; rw

中文:
定理 cos_pi_over_two_pow
  结论: 对任意 n : 自然数, cos (π / 2 ^ (n + 1)) = sqrtTwoAddSeries 0 n / 2
  证明: one_lt_pow₀ one_lt_two n.succ_ne_zero
    have B : π / 2 ^ (n + 1) < π := div_lt_self pi_pos A
    have C : 0 < π / 2 ^ (n + 1) := by positivity
    rw [pow_succ]; rw [div_mul_eq_div_div]; rw [cos_half]; rw [cos_pi_over_two_pow n]; rw [sqrtTwoAddSeries]; rw [add_div_eq_mul_add_div]; rw [one_mul]; rw

Depends on / 依赖: n.succ_ne_zero, one_lt_two, succ_ne_zero
-/
theorem cos_pi_over_two_pow : forall n : Nat, cos (π / 2 ^ (n + 1)) = sqrtTwoAddSeries 0 n / 2
  | 0 => by simp
  | n + 1 => by
    have A : (1 : Real) < 2 ^ (n + 1) := one_lt_pow₀ one_lt_two n.succ_ne_zero
    have B : π / 2 ^ (n + 1) < π := div_lt_self pi_pos A
    have C : 0 < π / 2 ^ (n + 1) := by positivity
    rw [pow_succ]; rw [div_mul_eq_div_div]; rw [cos_half]; rw [cos_pi_over_two_pow n]; rw [sqrtTwoAddSeries]; rw [add_div_eq_mul_add_div]; rw [one_mul]; rw [← div_mul_eq_div_div]; rw [sqrt_div]; rw [sqrt_mul_self] <;>
      linarith [sqrtTwoAddSeries_nonneg le_rfl n]

/--
theorem `sin_sq_pi_over_two_pow` / 定理 `sin_sq_pi_over_two_pow`

English:
theorem sin_sq_pi_over_two_pow
  given: (n : Nat)
  proof: by
  rw [sin_sq]; rw [cos_pi_over_two_pow]

中文:
定理 sin_sq_pi_over_two_pow
  条件: (n : 自然数)
  证明: by
  rw [sin_sq]; rw [cos_pi_over_two_pow]

Depends on / 依赖: cos_pi_over_two_pow, sin_sq
-/
theorem sin_sq_pi_over_two_pow (n : Nat) :
    sin (π / 2 ^ (n + 1)) ^ 2 = 1 - (sqrtTwoAddSeries 0 n / 2) ^ 2 := by
  rw [sin_sq]; rw [cos_pi_over_two_pow]

/--
theorem `sin_sq_pi_over_two_pow_succ` / 定理 `sin_sq_pi_over_two_pow_succ`

English:
theorem sin_sq_pi_over_two_pow_succ
  given: (n : Nat)
  proof: by
  rw [sin_sq_pi_over_two_pow]; rw [sqrtTwoAddSeries]; rw [div_pow]; rw [sq_sqrt]; rw [add_div]; rw [← sub_sub]
  · congr
    · norm_num
    · norm_num
  · exact add_nonneg two_pos.le (sqrtTwoAddSeries_zero_nonneg _)

@[simp]

中文:
定理 sin_sq_pi_over_two_pow_succ
  条件: (n : 自然数)
  证明: by
  rw [sin_sq_pi_over_two_pow]; rw [sqrtTwoAddSeries]; rw [div_pow]; rw [sq_sqrt]; rw [add_div]; rw [← sub_sub]
  · congr
    · norm_num
    · norm_num
  · exact add_nonneg two_pos.le (sqrtTwoAddSeries_zero_nonneg _)

@[simp]

Depends on / 依赖: add_div, add_nonneg, div_pow, sin_sq_pi_over_two_pow, sq_sqrt, sqrtTwoAddSeries, sqrtTwoAddSeries_zero_nonneg, sub_sub, two_pos, two_pos.le
-/
theorem sin_sq_pi_over_two_pow_succ (n : Nat) :
    sin (π / 2 ^ (n + 2)) ^ 2 = 1 / 2 - sqrtTwoAddSeries 0 n / 4 := by
  rw [sin_sq_pi_over_two_pow]; rw [sqrtTwoAddSeries]; rw [div_pow]; rw [sq_sqrt]; rw [add_div]; rw [← sub_sub]
  · congr
    · norm_num
    · norm_num
  · exact add_nonneg two_pos.le (sqrtTwoAddSeries_zero_nonneg _)

@[simp]
/--
theorem `sin_pi_over_two_pow_succ` / 定理 `sin_pi_over_two_pow_succ`

English:
theorem sin_pi_over_two_pow_succ
  given: (n : Nat)
  proof: by
  rw [eq_div_iff_mul_eq two_ne_zero]; rw [eq_comm]; rw [sqrt_eq_iff_eq_sq]; rw [mul_pow]; rw [sin_sq_pi_over_two_pow_succ]; rw [sub_mul]
  · congr <;> norm_num
  · rw [sub_nonneg]
    exact (sqrtTwoAddSeries_lt_two _).le
  refine mul_nonneg (sin_nonneg_of_nonneg_of_le_pi ?_ ?_) zero_le_two
  · po

中文:
定理 sin_pi_over_two_pow_succ
  条件: (n : 自然数)
  证明: by
  rw [eq_div_iff_mul_eq two_ne_zero]; rw [eq_comm]; rw [sqrt_eq_iff_eq_sq]; rw [mul_pow]; rw [sin_sq_pi_over_two_pow_succ]; rw [sub_mul]
  · congr <;> norm_num
  · rw [sub_nonneg]
    exact (sqrtTwoAddSeries_lt_two _).le
  refine mul_nonneg (sin_nonneg_of_nonneg_of_le_pi ?_ ?_) zero_le_two
  · po

Depends on / 依赖: div_le_self, eq_comm, eq_div_iff_mul_eq, mul_nonneg, mul_pow, one_le_two, pi_pos, pi_pos.le, sin_nonneg_of_nonneg_of_le_pi, sin_sq_pi_over_two_pow_succ, sqrtTwoAddSeries_lt_two, sqrt_eq_iff_eq_sq, sub_mul, sub_nonneg, two_ne_zero, zero_le_two
-/
theorem sin_pi_over_two_pow_succ (n : Nat) :
    sin (π / 2 ^ (n + 2)) = √(2 - sqrtTwoAddSeries 0 n) / 2 := by
  rw [eq_div_iff_mul_eq two_ne_zero]; rw [eq_comm]; rw [sqrt_eq_iff_eq_sq]; rw [mul_pow]; rw [sin_sq_pi_over_two_pow_succ]; rw [sub_mul]
  · congr <;> norm_num
  · rw [sub_nonneg]
    exact (sqrtTwoAddSeries_lt_two _).le
  refine mul_nonneg (sin_nonneg_of_nonneg_of_le_pi ?_ ?_) zero_le_two
  · positivity
· exact div_le_self pi_pos.le one_le_pow₀ one_le_two

@[simp]
/--
theorem `cos_pi_div_four` / 定理 `cos_pi_div_four`

English:
theorem cos_pi_div_four
  statement: cos (π / 4) = √2 / 2
  proof: by
  trans cos (π / 2 ^ 2)
  · congr
    norm_num
  · simp

@[simp]

中文:
定理 cos_pi_div_four
  结论: cos (π / 4) = √2 / 2
  证明: by
  trans cos (π / 2 ^ 2)
  · congr
    norm_num
  · simp

@[simp]
-/
theorem cos_pi_div_four : cos (π / 4) = √2 / 2 := by
  trans cos (π / 2 ^ 2)
  · congr
    norm_num
  · simp

@[simp]
/--
theorem `sin_pi_div_four` / 定理 `sin_pi_div_four`

English:
theorem sin_pi_div_four
  statement: sin (π / 4) = √2 / 2
  proof: by
  trans sin (π / 2 ^ 2)
  · congr
    norm_num
  · simp

@[simp]

中文:
定理 sin_pi_div_four
  结论: sin (π / 4) = √2 / 2
  证明: by
  trans sin (π / 2 ^ 2)
  · congr
    norm_num
  · simp

@[simp]
-/
theorem sin_pi_div_four : sin (π / 4) = √2 / 2 := by
  trans sin (π / 2 ^ 2)
  · congr
    norm_num
  · simp

@[simp]
/--
theorem `cos_pi_div_eight` / 定理 `cos_pi_div_eight`

English:
theorem cos_pi_div_eight
  statement: cos (π / 8) = √(2 + √2) / 2
  proof: by
  trans cos (π / 2 ^ 3)
  · congr
    norm_num
  · simp

@[simp]

中文:
定理 cos_pi_div_eight
  结论: cos (π / 8) = √(2 + √2) / 2
  证明: by
  trans cos (π / 2 ^ 3)
  · congr
    norm_num
  · simp

@[simp]
-/
theorem cos_pi_div_eight : cos (π / 8) = √(2 + √2) / 2 := by
  trans cos (π / 2 ^ 3)
  · congr
    norm_num
  · simp

@[simp]
/--
theorem `sin_pi_div_eight` / 定理 `sin_pi_div_eight`

English:
theorem sin_pi_div_eight
  statement: sin (π / 8) = √(2 - √2) / 2
  proof: by
  trans sin (π / 2 ^ 3)
  · congr
    norm_num
  · simp

@[simp]

中文:
定理 sin_pi_div_eight
  结论: sin (π / 8) = √(2 - √2) / 2
  证明: by
  trans sin (π / 2 ^ 3)
  · congr
    norm_num
  · simp

@[simp]
-/
theorem sin_pi_div_eight : sin (π / 8) = √(2 - √2) / 2 := by
  trans sin (π / 2 ^ 3)
  · congr
    norm_num
  · simp

@[simp]
/--
theorem `cos_pi_div_sixteen` / 定理 `cos_pi_div_sixteen`

English:
theorem cos_pi_div_sixteen
  statement: cos (π / 16) = √(2 + √(2 + √2)) / 2
  proof: by
  trans cos (π / 2 ^ 4)
  · congr
    norm_num
  · simp

@[simp]

中文:
定理 cos_pi_div_sixteen
  结论: cos (π / 16) = √(2 + √(2 + √2)) / 2
  证明: by
  trans cos (π / 2 ^ 4)
  · congr
    norm_num
  · simp

@[simp]
-/
theorem cos_pi_div_sixteen : cos (π / 16) = √(2 + √(2 + √2)) / 2 := by
  trans cos (π / 2 ^ 4)
  · congr
    norm_num
  · simp

@[simp]
/--
theorem `sin_pi_div_sixteen` / 定理 `sin_pi_div_sixteen`

English:
theorem sin_pi_div_sixteen
  statement: sin (π / 16) = √(2 - √(2 + √2)) / 2
  proof: by
  trans sin (π / 2 ^ 4)
  · congr
    norm_num
  · simp

@[simp]

中文:
定理 sin_pi_div_sixteen
  结论: sin (π / 16) = √(2 - √(2 + √2)) / 2
  证明: by
  trans sin (π / 2 ^ 4)
  · congr
    norm_num
  · simp

@[simp]
-/
theorem sin_pi_div_sixteen : sin (π / 16) = √(2 - √(2 + √2)) / 2 := by
  trans sin (π / 2 ^ 4)
  · congr
    norm_num
  · simp

@[simp]
/--
theorem `cos_pi_div_thirty_two` / 定理 `cos_pi_div_thirty_two`

English:
theorem cos_pi_div_thirty_two
  statement: cos (π / 32) = √(2 + √(2 + √(2 + √2))) / 2
  proof: by
  trans cos (π / 2 ^ 5)
  · congr
    norm_num
  · simp

@[simp]

中文:
定理 cos_pi_div_thirty_two
  结论: cos (π / 32) = √(2 + √(2 + √(2 + √2))) / 2
  证明: by
  trans cos (π / 2 ^ 5)
  · congr
    norm_num
  · simp

@[simp]
-/
theorem cos_pi_div_thirty_two : cos (π / 32) = √(2 + √(2 + √(2 + √2))) / 2 := by
  trans cos (π / 2 ^ 5)
  · congr
    norm_num
  · simp

@[simp]
/--
theorem `sin_pi_div_thirty_two` / 定理 `sin_pi_div_thirty_two`

English:
theorem sin_pi_div_thirty_two
  statement: sin (π / 32) = √(2 - √(2 + √(2 + √2))) / 2
  proof: by
  trans sin (π / 2 ^ 5)
  · congr
    norm_num
  · simp

中文:
定理 sin_pi_div_thirty_two
  结论: sin (π / 32) = √(2 - √(2 + √(2 + √2))) / 2
  证明: by
  trans sin (π / 2 ^ 5)
  · congr
    norm_num
  · simp
-/
theorem sin_pi_div_thirty_two : sin (π / 32) = √(2 - √(2 + √(2 + √2))) / 2 := by
  trans sin (π / 2 ^ 5)
  · congr
    norm_num
  · simp

-- This section is also a convenient location for other explicit values of `sin` and `cos`.
/-- The cosine of `π / 3` is `1 / 2`. -/
@[simp]
/--
theorem `cos_pi_div_three` / 定理 `cos_pi_div_three`

English:
theorem cos_pi_div_three
  statement: cos (π / 3) = 1 / 2
  proof: by
  have h₁ : (2 * cos (π / 3) - 1) ^ 2 * (2 * cos (π / 3) + 2) = 0 := by
    have : cos (3 * (π / 3)) = cos π := by
      congr 1
      ring
    linarith [cos_pi, cos_three_mul (π / 3)]
  rcases mul_eq_zero.mp h₁ with h | h
  · linarith [eq_zero_of_pow_eq_zero h]
  · have : cos π < cos (π / 3) := 

中文:
定理 cos_pi_div_three
  结论: cos (π / 3) = 1 / 2
  证明: by
  have h₁ : (2 * cos (π / 3) - 1) ^ 2 * (2 * cos (π / 3) + 2) = 0 := by
    have : cos (3 * (π / 3)) = cos π := by
      congr 1
      ring
    linarith [cos_pi, cos_three_mul (π / 3)]
  rcases mul_eq_zero.mp h₁ with h | h
  · linarith [eq_zero_of_pow_eq_zero h]
  · have : cos π < cos (π / 3) := 

Depends on / 依赖: cos_lt_cos_of_nonneg_of_le_pi, cos_pi, cos_three_mul, eq_zero_of_pow_eq_zero, le_rfl, mul_eq_zero, mul_eq_zero.mp, pi_pos
-/
theorem cos_pi_div_three : cos (π / 3) = 1 / 2 := by
  have h₁ : (2 * cos (π / 3) - 1) ^ 2 * (2 * cos (π / 3) + 2) = 0 := by
    have : cos (3 * (π / 3)) = cos π := by
      congr 1
      ring
    linarith [cos_pi, cos_three_mul (π / 3)]
  rcases mul_eq_zero.mp h₁ with h | h
  · linarith [eq_zero_of_pow_eq_zero h]
  · have : cos π < cos (π / 3) := by
      refine cos_lt_cos_of_nonneg_of_le_pi ?_ le_rfl ?_ <;> linarith [pi_pos]
    linarith [cos_pi]

/-- The cosine of `π / 6` is `√3 / 2`. -/
@[simp]
/--
theorem `cos_pi_div_six` / 定理 `cos_pi_div_six`

English:
theorem cos_pi_div_six
  statement: cos (π / 6) = √3 / 2
  proof: by
  rw [show (6 : Real) = 3 * 2 by norm_num]; rw [div_mul_eq_div_div]; rw [cos_half]; rw [cos_pi_div_three]; rw [one_add_div]; rw [← div_mul_eq_div_div]; rw [two_add_one_eq_three]; rw [sqrt_div]; rw [sqrt_mul_self] <;> linarith [pi_pos]

中文:
定理 cos_pi_div_six
  结论: cos (π / 6) = √3 / 2
  证明: by
  rw [show (6 : Real) = 3 * 2 by norm_num]; rw [div_mul_eq_div_div]; rw [cos_half]; rw [cos_pi_div_three]; rw [one_add_div]; rw [← div_mul_eq_div_div]; rw [two_add_one_eq_three]; rw [sqrt_div]; rw [sqrt_mul_self] <;> linarith [pi_pos]

Depends on / 依赖: cos_half, cos_pi_div_three, div_mul_eq_div_div, one_add_div, pi_pos, sqrt_div, sqrt_mul_self, two_add_one_eq_three
-/
theorem cos_pi_div_six : cos (π / 6) = √3 / 2 := by
  rw [show (6 : Real) = 3 * 2 by norm_num]; rw [div_mul_eq_div_div]; rw [cos_half]; rw [cos_pi_div_three]; rw [one_add_div]; rw [← div_mul_eq_div_div]; rw [two_add_one_eq_three]; rw [sqrt_div]; rw [sqrt_mul_self] <;> linarith [pi_pos]

/--
theorem `sq_cos_pi_div_six` / 定理 `sq_cos_pi_div_six`

English:
theorem sq_cos_pi_div_six
  statement: cos (π / 6) ^ 2 = 3 / 4
  proof: by
  rw [cos_pi_div_six]; rw [div_pow]; rw [sq_sqrt] <;> norm_num

中文:
定理 sq_cos_pi_div_six
  结论: cos (π / 6) ^ 2 = 3 / 4
  证明: by
  rw [cos_pi_div_six]; rw [div_pow]; rw [sq_sqrt] <;> norm_num

Depends on / 依赖: cos_pi_div_six, div_pow, sq_sqrt
-/
theorem sq_cos_pi_div_six : cos (π / 6) ^ 2 = 3 / 4 := by
  rw [cos_pi_div_six]; rw [div_pow]; rw [sq_sqrt] <;> norm_num

/-- The sine of `π / 6` is `1 / 2`. -/
@[simp]
/--
theorem `sin_pi_div_six` / 定理 `sin_pi_div_six`

English:
theorem sin_pi_div_six
  statement: sin (π / 6) = 1 / 2
  proof: by
  rw [← cos_pi_div_two_sub]; rw [← cos_pi_div_three]
  congr
  ring

中文:
定理 sin_pi_div_six
  结论: sin (π / 6) = 1 / 2
  证明: by
  rw [← cos_pi_div_two_sub]; rw [← cos_pi_div_three]
  congr
  ring

Depends on / 依赖: cos_pi_div_three, cos_pi_div_two_sub
-/
theorem sin_pi_div_six : sin (π / 6) = 1 / 2 := by
  rw [← cos_pi_div_two_sub]; rw [← cos_pi_div_three]
  congr
  ring

/--
theorem `sq_sin_pi_div_three` / 定理 `sq_sin_pi_div_three`

English:
theorem sq_sin_pi_div_three
  statement: sin (π / 3) ^ 2 = 3 / 4
  proof: by
  rw [← cos_pi_div_two_sub]; rw [← sq_cos_pi_div_six]
  congr
  ring

中文:
定理 sq_sin_pi_div_three
  结论: sin (π / 3) ^ 2 = 3 / 4
  证明: by
  rw [← cos_pi_div_two_sub]; rw [← sq_cos_pi_div_six]
  congr
  ring

Depends on / 依赖: cos_pi_div_two_sub, sq_cos_pi_div_six
-/
theorem sq_sin_pi_div_three : sin (π / 3) ^ 2 = 3 / 4 := by
  rw [← cos_pi_div_two_sub]; rw [← sq_cos_pi_div_six]
  congr
  ring

/-- The sine of `π / 3` is `√3 / 2`. -/
@[simp]
/--
theorem `sin_pi_div_three` / 定理 `sin_pi_div_three`

English:
theorem sin_pi_div_three
  statement: sin (π / 3) = √3 / 2
  proof: by
  rw [← cos_pi_div_two_sub]; rw [← cos_pi_div_six]
  congr
  ring

中文:
定理 sin_pi_div_three
  结论: sin (π / 3) = √3 / 2
  证明: by
  rw [← cos_pi_div_two_sub]; rw [← cos_pi_div_six]
  congr
  ring

Depends on / 依赖: cos_pi_div_six, cos_pi_div_two_sub
-/
theorem sin_pi_div_three : sin (π / 3) = √3 / 2 := by
  rw [← cos_pi_div_two_sub]; rw [← cos_pi_div_six]
  congr
  ring

/--
theorem `quadratic_root_cos_pi_div_five` / 定理 `quadratic_root_cos_pi_div_five`

English:
theorem quadratic_root_cos_pi_div_five
  proof: cos (π / 5)
    4 * c ^ 2 - 2 * c - 1 = 0 := by
  set θ := π / 5 with hθ
  set c := cos θ
  set s := sin θ
  suffices 2 * c = 4 * c ^ 2 - 1 by simp [this]
  have hs : s != 0 := by
    rw [ne_eq]; rw [sin_eq_zero_iff]; rw [hθ]
    push Not
    intro n hn
    replace hn : n * 5 = 1 := by field_simp at

中文:
定理 quadratic_root_cos_pi_div_five
  证明: cos (π / 5)
    4 * c ^ 2 - 2 * c - 1 = 0 := by
  set θ := π / 5 with hθ
  set c := cos θ
  set s := sin θ
  suffices 2 * c = 4 * c ^ 2 - 1 by simp [this]
  have hs : s != 0 := by
    rw [ne_eq]; rw [sin_eq_zero_iff]; rw [hθ]
    push Not
    intro n hn
    replace hn : n * 5 = 1 := by field_simp at
-/
theorem quadratic_root_cos_pi_div_five :
    letI c := cos (π / 5)
    4 * c ^ 2 - 2 * c - 1 = 0 := by
  set θ := π / 5 with hθ
  set c := cos θ
  set s := sin θ
  suffices 2 * c = 4 * c ^ 2 - 1 by simp [this]
  have hs : s != 0 := by
    rw [ne_eq]; rw [sin_eq_zero_iff]; rw [hθ]
    push Not
    intro n hn
    replace hn : n * 5 = 1 := by field_simp at hn; norm_cast at hn
    lia
  suffices s * (2 * c) = s * (4 * c ^ 2 - 1) from mul_left_cancel₀ hs this
  calc s * (2 * c) = 2 * s * c := by rw [← mul_assoc, mul_comm 2]
                 _ = sin (2 * θ) := by rw [sin_two_mul]
                 _ = sin (π - 2 * θ) := by rw [sin_pi_sub]
                 _ = sin (2 * θ + θ) := by congr; linarith
                 _ = sin (2 * θ) * c + cos (2 * θ) * s := sin_add (2 * θ) θ
                 _ = 2 * s * c * c + cos (2 * θ) * s := by rw [sin_two_mul]
                 _ = 2 * s * c * c + (2 * c ^ 2 - 1) * s := by rw [cos_two_mul]
                 _ = s * (2 * c * c) + s * (2 * c ^ 2 - 1) := by linarith
                 _ = s * (4 * c ^ 2 - 1) := by linarith

open Polynomial in
/--
theorem `Polynomial.isRoot_cos_pi_div_five` / 定理 `Polynomial.isRoot_cos_pi_div_five`

English:
theorem Polynomial.isRoot_cos_pi_div_five
  proof: by
  simpa using quadratic_root_cos_pi_div_five

中文:
定理 Polynomial.isRoot_cos_pi_div_five
  证明: by
  simpa using quadratic_root_cos_pi_div_five

Depends on / 依赖: quadratic_root_cos_pi_div_five
-/
theorem Polynomial.isRoot_cos_pi_div_five :
    (4 • X ^ 2 - 2 • X - C 1 : Real[X]).IsRoot (cos (π / 5)) := by
  simpa using quadratic_root_cos_pi_div_five

/-- The cosine of `π / 5` is `(1 + √5) / 4`. -/
@[simp]
/--
theorem `cos_pi_div_five` / 定理 `cos_pi_div_five`

English:
theorem cos_pi_div_five
  statement: cos (π / 5) = (1 + √5) / 4
  proof: by
  set c := cos (π / 5)
  have : 4 * (c * c) + (-2) * c + (-1) = 0 := by
    rw [← sq]; rw [neg_mul]; rw [← sub_eq_add_neg]; rw [← sub_eq_add_neg]
    exact quadratic_root_cos_pi_div_five
  have hd : discrim 4 (-2) (-1) = (2 * √5) * (2 * √5) := by norm_num [discrim, mul_mul_mul_comm]
  rcases (qua

中文:
定理 cos_pi_div_five
  结论: cos (π / 5) = (1 + √5) / 4
  证明: by
  set c := cos (π / 5)
  have : 4 * (c * c) + (-2) * c + (-1) = 0 := by
    rw [← sq]; rw [neg_mul]; rw [← sub_eq_add_neg]; rw [← sub_eq_add_neg]
    exact quadratic_root_cos_pi_div_five
  have hd : discrim 4 (-2) (-1) = (2 * √5) * (2 * √5) := by norm_num [discrim, mul_mul_mul_comm]
  rcases (qua

Depends on / 依赖: absurd, cos_nonneg_of_mem_Icc, discrim, div_neg_of_neg_of_pos, mul_mul_mul_comm, neg_mul, not_le, pi_pos, pi_pos.le, quadratic_eq_zero_iff, quadratic_root_cos_pi_div_five, sub_eq_add_neg
-/
theorem cos_pi_div_five : cos (π / 5) = (1 + √5) / 4 := by
  set c := cos (π / 5)
  have : 4 * (c * c) + (-2) * c + (-1) = 0 := by
    rw [← sq]; rw [neg_mul]; rw [← sub_eq_add_neg]; rw [← sub_eq_add_neg]
    exact quadratic_root_cos_pi_div_five
  have hd : discrim 4 (-2) (-1) = (2 * √5) * (2 * √5) := by norm_num [discrim, mul_mul_mul_comm]
  rcases (quadratic_eq_zero_iff (by simp) hd c).mp this with h | h
  · simp [h]; linarith
  · absurd (show 0 <= c from cos_nonneg_of_mem_Icc <| by constructor <;> linarith [pi_pos.le])
    rw [not_le]; rw [h]
    exact div_neg_of_neg_of_pos (by norm_num [lt_sqrt]) (by positivity)

end CosDivSq

/--
Definition of `sinOrderIso` / `sinOrderIso` 的定义

English:
definition sinOrderIso
  signature: : Icc (-(π / 2)) (π / 2) ≃o Icc (-1 : Real) 1
  body: (strictMonoOn_sin.orderIso _ _).trans OrderIso.setCongr _ _ bijOn_sin.image_eq

@[simp]

中文:
定义 sinOrderIso
  签名: : Icc (-(π / 2)) (π / 2) ≃o Icc (-1 : 实数) 1
  定义体: (strictMonoOn_sin.orderIso _ _).trans OrderIso.setCongr _ _ bijOn_sin.image_eq

@[simp]

Depends on / 依赖: OrderIso, OrderIso.setCongr, bijOn_sin, bijOn_sin.image_eq, image_eq, orderIso, setCongr, strictMonoOn_sin, strictMonoOn_sin.orderIso
-/
def sinOrderIso : Icc (-(π / 2)) (π / 2) ≃o Icc (-1 : Real) 1 :=
(strictMonoOn_sin.orderIso _ _).trans OrderIso.setCongr _ _ bijOn_sin.image_eq

@[simp]
/--
theorem `coe_sinOrderIso_apply` / 定理 `coe_sinOrderIso_apply`

English:
theorem coe_sinOrderIso_apply
  given: (x : Icc (-(π / 2)) (π / 2))
  statement: (sinOrderIso x : Real) = sin x
  proof: rfl

中文:
定理 coe_sinOrderIso_apply
  条件: (x : Icc (-(π / 2)) (π / 2))
  结论: (sinOrderIso x : 实数) = sin x
  证明: rfl
-/
theorem coe_sinOrderIso_apply (x : Icc (-(π / 2)) (π / 2)) : (sinOrderIso x : Real) = sin x :=
  rfl

/--
theorem `sinOrderIso_apply` / 定理 `sinOrderIso_apply`

English:
theorem sinOrderIso_apply
  given: (x : Icc (-(π / 2)) (π / 2))
  statement: sinOrderIso x = ⟨sin x, sin_mem_Icc x⟩
  proof: rfl

@[simp]

中文:
定理 sinOrderIso_apply
  条件: (x : Icc (-(π / 2)) (π / 2))
  结论: sinOrderIso x = ⟨sin x, sin_mem_Icc x⟩
  证明: rfl

@[simp]
-/
theorem sinOrderIso_apply (x : Icc (-(π / 2)) (π / 2)) : sinOrderIso x = ⟨sin x, sin_mem_Icc x⟩ :=
  rfl

@[simp]
/--
theorem `tan_pi_div_four` / 定理 `tan_pi_div_four`

English:
theorem tan_pi_div_four
  statement: tan (π / 4) = 1
  proof: by
  rw [tan_eq_sin_div_cos]; rw [cos_pi_div_four]; rw [sin_pi_div_four]
  have h : √2 / 2 > 0 := by positivity
  exact div_self (ne_of_gt h)

@[simp]

中文:
定理 tan_pi_div_four
  结论: tan (π / 4) = 1
  证明: by
  rw [tan_eq_sin_div_cos]; rw [cos_pi_div_four]; rw [sin_pi_div_four]
  have h : √2 / 2 > 0 := by positivity
  exact div_self (ne_of_gt h)

@[simp]

Depends on / 依赖: cos_pi_div_four, div_self, ne_of_gt, sin_pi_div_four, tan_eq_sin_div_cos
-/
theorem tan_pi_div_four : tan (π / 4) = 1 := by
  rw [tan_eq_sin_div_cos]; rw [cos_pi_div_four]; rw [sin_pi_div_four]
  have h : √2 / 2 > 0 := by positivity
  exact div_self (ne_of_gt h)

@[simp]
/--
theorem `tan_pi_div_two` / 定理 `tan_pi_div_two`

English:
theorem tan_pi_div_two
  statement: tan (π / 2) = 0
  proof: by simp [tan_eq_sin_div_cos]

@[simp]

中文:
定理 tan_pi_div_two
  结论: tan (π / 2) = 0
  证明: by simp [tan_eq_sin_div_cos]

@[simp]

Depends on / 依赖: tan_eq_sin_div_cos
-/
theorem tan_pi_div_two : tan (π / 2) = 0 := by simp [tan_eq_sin_div_cos]

@[simp]
/--
theorem `tan_pi_div_six` / 定理 `tan_pi_div_six`

English:
theorem tan_pi_div_six
  statement: tan (π / 6) = 1 / √3
  proof: by
  rw [tan_eq_sin_div_cos]; rw [sin_pi_div_six]; rw [cos_pi_div_six]
  ring

@[simp]

中文:
定理 tan_pi_div_six
  结论: tan (π / 6) = 1 / √3
  证明: by
  rw [tan_eq_sin_div_cos]; rw [sin_pi_div_six]; rw [cos_pi_div_six]
  ring

@[simp]

Depends on / 依赖: cos_pi_div_six, sin_pi_div_six, tan_eq_sin_div_cos
-/
theorem tan_pi_div_six : tan (π / 6) = 1 / √3 := by
  rw [tan_eq_sin_div_cos]; rw [sin_pi_div_six]; rw [cos_pi_div_six]
  ring

@[simp]
/--
theorem `tan_pi_div_three` / 定理 `tan_pi_div_three`

English:
theorem tan_pi_div_three
  statement: tan (π / 3) = √3
  proof: by
  rw [tan_eq_sin_div_cos]; rw [sin_pi_div_three]; rw [cos_pi_div_three]
  ring

中文:
定理 tan_pi_div_three
  结论: tan (π / 3) = √3
  证明: by
  rw [tan_eq_sin_div_cos]; rw [sin_pi_div_three]; rw [cos_pi_div_three]
  ring

Depends on / 依赖: cos_pi_div_three, sin_pi_div_three, tan_eq_sin_div_cos
-/
theorem tan_pi_div_three : tan (π / 3) = √3 := by
  rw [tan_eq_sin_div_cos]; rw [sin_pi_div_three]; rw [cos_pi_div_three]
  ring

/--
theorem `tan_pos_of_pos_of_lt_pi_div_two` / 定理 `tan_pos_of_pos_of_lt_pi_div_two`

English:
theorem tan_pos_of_pos_of_lt_pi_div_two
  given: {x : Real} (h0x : 0 < x) (hxp : x < π / 2)
  statement: 0 < tan x
  proof: by
  rw [tan_eq_sin_div_cos]
  exact div_pos (sin_pos_of_pos_of_lt_pi h0x (by linarith)) (cos_pos_of_mem_Ioo ⟨by linarith, hxp⟩)

中文:
定理 tan_pos_of_pos_of_lt_pi_div_two
  条件: {x : 实数} (h0x : 0 < x) (hxp : x < π / 2)
  结论: 0 < tan x
  证明: by
  rw [tan_eq_sin_div_cos]
  exact div_pos (sin_pos_of_pos_of_lt_pi h0x (by linarith)) (cos_pos_of_mem_Ioo ⟨by linarith, hxp⟩)

Depends on / 依赖: cos_pos_of_mem_Ioo, div_pos, sin_pos_of_pos_of_lt_pi, tan_eq_sin_div_cos
-/
theorem tan_pos_of_pos_of_lt_pi_div_two {x : Real} (h0x : 0 < x) (hxp : x < π / 2) : 0 < tan x := by
  rw [tan_eq_sin_div_cos]
  exact div_pos (sin_pos_of_pos_of_lt_pi h0x (by linarith)) (cos_pos_of_mem_Ioo ⟨by linarith, hxp⟩)

/--
theorem `tan_nonneg_of_nonneg_of_le_pi_div_two` / 定理 `tan_nonneg_of_nonneg_of_le_pi_div_two`

English:
theorem tan_nonneg_of_nonneg_of_le_pi_div_two
  given: {x : Real} (h0x : 0 <= x) (hxp : x <= π / 2)
  statement: 0 <= tan x
  proof: match lt_or_eq_of_le h0x, lt_or_eq_of_le hxp with
  | Or.inl hx0, Or.inl hxp => le_of_lt (tan_pos_of_pos_of_lt_pi_div_two hx0 hxp)
  | Or.inl _, Or.inr hxp => by simp [hxp, tan_eq_sin_div_cos]
  | Or.inr hx0, _ => by simp [hx0.symm]

中文:
定理 tan_nonneg_of_nonneg_of_le_pi_div_two
  条件: {x : 实数} (h0x : 0 <= x) (hxp : x <= π / 2)
  结论: 0 <= tan x
  证明: match lt_or_eq_of_le h0x, lt_or_eq_of_le hxp with
  | Or.inl hx0, Or.inl hxp => le_of_lt (tan_pos_of_pos_of_lt_pi_div_two hx0 hxp)
  | Or.inl _, Or.inr hxp => by simp [hxp, tan_eq_sin_div_cos]
  | Or.inr hx0, _ => by simp [hx0.symm]

Depends on / 依赖: Or.inl, Or.inr, hx0.symm, le_of_lt, lt_or_eq_of_le, tan_eq_sin_div_cos, tan_pos_of_pos_of_lt_pi_div_two
-/
theorem tan_nonneg_of_nonneg_of_le_pi_div_two {x : Real} (h0x : 0 <= x) (hxp : x <= π / 2) : 0 <= tan x :=
  match lt_or_eq_of_le h0x, lt_or_eq_of_le hxp with
  | Or.inl hx0, Or.inl hxp => le_of_lt (tan_pos_of_pos_of_lt_pi_div_two hx0 hxp)
  | Or.inl _, Or.inr hxp => by simp [hxp, tan_eq_sin_div_cos]
  | Or.inr hx0, _ => by simp [hx0.symm]

/--
theorem `tan_neg_of_neg_of_pi_div_two_lt` / 定理 `tan_neg_of_neg_of_pi_div_two_lt`

English:
theorem tan_neg_of_neg_of_pi_div_two_lt
  given: {x : Real} (hx0 : x < 0) (hpx : -(π / 2) < x)
  statement: tan x < 0
  proof: neg_pos.1 (tan_neg x ▸ tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith [pi_pos]))

中文:
定理 tan_neg_of_neg_of_pi_div_two_lt
  条件: {x : 实数} (hx0 : x < 0) (hpx : -(π / 2) < x)
  结论: tan x < 0
  证明: neg_pos.1 (tan_neg x ▸ tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith [pi_pos]))

Depends on / 依赖: neg_pos, pi_pos, tan_neg, tan_pos_of_pos_of_lt_pi_div_two
-/
theorem tan_neg_of_neg_of_pi_div_two_lt {x : Real} (hx0 : x < 0) (hpx : -(π / 2) < x) : tan x < 0 :=
  neg_pos.1 (tan_neg x ▸ tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith [pi_pos]))

/--
theorem `tan_nonpos_of_nonpos_of_neg_pi_div_two_le` / 定理 `tan_nonpos_of_nonpos_of_neg_pi_div_two_le`

English:
theorem tan_nonpos_of_nonpos_of_neg_pi_div_two_le
  given: {x : Real} (hx0 : x <= 0) (hpx : -(π / 2) <= x)
  proof: neg_nonneg.1 (tan_neg x ▸ tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith))

中文:
定理 tan_nonpos_of_nonpos_of_neg_pi_div_two_le
  条件: {x : 实数} (hx0 : x <= 0) (hpx : -(π / 2) <= x)
  证明: neg_nonneg.1 (tan_neg x ▸ tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith))

Depends on / 依赖: neg_nonneg, tan_neg, tan_nonneg_of_nonneg_of_le_pi_div_two
-/
theorem tan_nonpos_of_nonpos_of_neg_pi_div_two_le {x : Real} (hx0 : x <= 0) (hpx : -(π / 2) <= x) :
    tan x <= 0 :=
  neg_nonneg.1 (tan_neg x ▸ tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith))

/--
theorem `strictMonoOn_tan` / 定理 `strictMonoOn_tan`

English:
theorem strictMonoOn_tan
  statement: StrictMonoOn tan (Ioo (-(π / 2)) (π / 2))
  proof: by
  rintro x hx y hy hlt
  rw [tan_eq_sin_div_cos]; rw [tan_eq_sin_div_cos]; rw [div_lt_div_iff₀ (cos_pos_of_mem_Ioo hx) (cos_pos_of_mem_Ioo hy)]; rw [mul_comm]; rw [← sub_pos]; rw [← sin_sub]
exact sin_pos_of_pos_of_lt_pi (sub_pos.2 hlt) by linarith [hx.1, hy.2]

中文:
定理 strictMonoOn_tan
  结论: StrictMonoOn tan (Ioo (-(π / 2)) (π / 2))
  证明: by
  rintro x hx y hy hlt
  rw [tan_eq_sin_div_cos]; rw [tan_eq_sin_div_cos]; rw [div_lt_div_iff₀ (cos_pos_of_mem_Ioo hx) (cos_pos_of_mem_Ioo hy)]; rw [mul_comm]; rw [← sub_pos]; rw [← sin_sub]
exact sin_pos_of_pos_of_lt_pi (sub_pos.2 hlt) by linarith [hx.1, hy.2]

Depends on / 依赖: cos_pos_of_mem_Ioo, mul_comm, sin_pos_of_pos_of_lt_pi, sin_sub, sub_pos, tan_eq_sin_div_cos
-/
theorem strictMonoOn_tan : StrictMonoOn tan (Ioo (-(π / 2)) (π / 2)) := by
  rintro x hx y hy hlt
  rw [tan_eq_sin_div_cos]; rw [tan_eq_sin_div_cos]; rw [div_lt_div_iff₀ (cos_pos_of_mem_Ioo hx) (cos_pos_of_mem_Ioo hy)]; rw [mul_comm]; rw [← sub_pos]; rw [← sin_sub]
exact sin_pos_of_pos_of_lt_pi (sub_pos.2 hlt) by linarith [hx.1, hy.2]

/--
theorem `tan_lt_tan_of_lt_of_lt_pi_div_two` / 定理 `tan_lt_tan_of_lt_of_lt_pi_div_two`

English:
theorem tan_lt_tan_of_lt_of_lt_pi_div_two
  statement: {x y : Real} (hx₁ : -(π / 2) < x) (hy₂ : y < π / 2)
  proof: strictMonoOn_tan ⟨hx₁, hxy.trans hy₂⟩ ⟨hx₁.trans hxy, hy₂⟩ hxy

中文:
定理 tan_lt_tan_of_lt_of_lt_pi_div_two
  结论: {x y : 实数} (hx₁ : -(π / 2) < x) (hy₂ : y < π / 2)
  证明: strictMonoOn_tan ⟨hx₁, hxy.trans hy₂⟩ ⟨hx₁.trans hxy, hy₂⟩ hxy

Depends on / 依赖: StructuredArrow, StructuredArrow.Hom, hxy.trans, strictMonoOn_tan
-/
theorem tan_lt_tan_of_lt_of_lt_pi_div_two {x y : Real} (hx₁ : -(π / 2) < x) (hy₂ : y < π / 2)
    (hxy : x < y) : tan x < tan y :=
  strictMonoOn_tan ⟨hx₁, hxy.trans hy₂⟩ ⟨hx₁.trans hxy, hy₂⟩ hxy

/--
theorem `tan_lt_tan_of_nonneg_of_lt_pi_div_two` / 定理 `tan_lt_tan_of_nonneg_of_lt_pi_div_two`

English:
theorem tan_lt_tan_of_nonneg_of_lt_pi_div_two
  statement: {x y : Real} (hx₁ : 0 <= x) (hy₂ : y < π / 2)
  proof: tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) hy₂ hxy

中文:
定理 tan_lt_tan_of_nonneg_of_lt_pi_div_two
  结论: {x y : 实数} (hx₁ : 0 <= x) (hy₂ : y < π / 2)
  证明: tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) hy₂ hxy

Depends on / 依赖: tan_lt_tan_of_lt_of_lt_pi_div_two
-/
theorem tan_lt_tan_of_nonneg_of_lt_pi_div_two {x y : Real} (hx₁ : 0 <= x) (hy₂ : y < π / 2)
    (hxy : x < y) : tan x < tan y :=
  tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) hy₂ hxy

/--
theorem `injOn_tan` / 定理 `injOn_tan`

English:
theorem injOn_tan
  statement: InjOn tan (Ioo (-(π / 2)) (π / 2))
  proof: strictMonoOn_tan.injOn

中文:
定理 injOn_tan
  结论: InjOn tan (Ioo (-(π / 2)) (π / 2))
  证明: strictMonoOn_tan.injOn

Depends on / 依赖: strictMonoOn_tan, strictMonoOn_tan.injOn
-/
theorem injOn_tan : InjOn tan (Ioo (-(π / 2)) (π / 2)) :=
  strictMonoOn_tan.injOn

/--
theorem `tan_inj_of_lt_of_lt_pi_div_two` / 定理 `tan_inj_of_lt_of_lt_pi_div_two`

English:
theorem tan_inj_of_lt_of_lt_pi_div_two
  statement: {x y : Real} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2)
  proof: injOn_tan ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ hxy

中文:
定理 tan_inj_of_lt_of_lt_pi_div_two
  结论: {x y : 实数} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2)
  证明: injOn_tan ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ hxy

Depends on / 依赖: CommaMorphism, CommaMorphism.right, injOn_tan
-/
theorem tan_inj_of_lt_of_lt_pi_div_two {x y : Real} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2)
    (hy₁ : -(π / 2) < y) (hy₂ : y < π / 2) (hxy : tan x = tan y) : x = y :=
  injOn_tan ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ hxy

/--
theorem `tan_periodic` / 定理 `tan_periodic`

English:
theorem tan_periodic
  statement: Function.Periodic tan π
  proof: by
  simpa only [Function.Periodic, tan_eq_sin_div_cos] using! sin_antiperiodic.div cos_antiperiodic

@[simp]

中文:
定理 tan_periodic
  结论: Function.Periodic tan π
  证明: by
  simpa only [Function.Periodic, tan_eq_sin_div_cos] using! sin_antiperiodic.div cos_antiperiodic

@[simp]

Depends on / 依赖: Function, Function.Periodic, Periodic, cos_antiperiodic, sin_antiperiodic, sin_antiperiodic.div, tan_eq_sin_div_cos
-/
theorem tan_periodic : Function.Periodic tan π := by
  simpa only [Function.Periodic, tan_eq_sin_div_cos] using! sin_antiperiodic.div cos_antiperiodic

@[simp]
/--
theorem `tan_pi` / 定理 `tan_pi`

English:
theorem tan_pi
  statement: tan π = 0
  proof: by rw [tan_periodic.eq, tan_zero]

中文:
定理 tan_pi
  结论: tan π = 0
  证明: by rw [tan_periodic.eq, tan_zero]

Depends on / 依赖: StructuredArrow, StructuredArrow.w, tan_periodic, tan_periodic.eq, tan_zero
-/
theorem tan_pi : tan π = 0 := by rw [tan_periodic.eq, tan_zero]

/--
theorem `tan_add_pi` / 定理 `tan_add_pi`

English:
theorem tan_add_pi
  given: (x : Real)
  statement: tan (x + π) = tan x
  proof: tan_periodic x

中文:
定理 tan_add_pi
  条件: (x : 实数)
  结论: tan (x + π) = tan x
  证明: tan_periodic x

Depends on / 依赖: tan_periodic
-/
theorem tan_add_pi (x : Real) : tan (x + π) = tan x :=
  tan_periodic x

/--
theorem `tan_sub_pi` / 定理 `tan_sub_pi`

English:
theorem tan_sub_pi
  given: (x : Real)
  statement: tan (x - π) = tan x
  proof: tan_periodic.sub_eq x

中文:
定理 tan_sub_pi
  条件: (x : 实数)
  结论: tan (x - π) = tan x
  证明: tan_periodic.sub_eq x

Depends on / 依赖: sub_eq, tan_periodic, tan_periodic.sub_eq
-/
theorem tan_sub_pi (x : Real) : tan (x - π) = tan x :=
  tan_periodic.sub_eq x

/--
theorem `tan_pi_sub` / 定理 `tan_pi_sub`

English:
theorem tan_pi_sub
  given: (x : Real)
  statement: tan (π - x) = -tan x
  proof: tan_neg x ▸ tan_periodic.sub_eq'

中文:
定理 tan_pi_sub
  条件: (x : 实数)
  结论: tan (π - x) = -tan x
  证明: tan_neg x ▸ tan_periodic.sub_eq'

Depends on / 依赖: sub_eq, tan_neg, tan_periodic, tan_periodic.sub_eq
-/
theorem tan_pi_sub (x : Real) : tan (π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.sub_eq'

/--
theorem `tan_pi_div_two_sub` / 定理 `tan_pi_div_two_sub`

English:
theorem tan_pi_div_two_sub
  given: (x : Real)
  statement: tan (π / 2 - x) = (tan x)⁻¹
  proof: by
  rw [tan_eq_sin_div_cos]; rw [tan_eq_sin_div_cos]; rw [inv_div]; rw [sin_pi_div_two_sub]; rw [cos_pi_div_two_sub]

中文:
定理 tan_pi_div_two_sub
  条件: (x : 实数)
  结论: tan (π / 2 - x) = (tan x)⁻¹
  证明: by
  rw [tan_eq_sin_div_cos]; rw [tan_eq_sin_div_cos]; rw [inv_div]; rw [sin_pi_div_two_sub]; rw [cos_pi_div_two_sub]

Depends on / 依赖: cos_pi_div_two_sub, inv_div, sin_pi_div_two_sub, tan_eq_sin_div_cos
-/
theorem tan_pi_div_two_sub (x : Real) : tan (π / 2 - x) = (tan x)⁻¹ := by
  rw [tan_eq_sin_div_cos]; rw [tan_eq_sin_div_cos]; rw [inv_div]; rw [sin_pi_div_two_sub]; rw [cos_pi_div_two_sub]

/--
theorem `tan_nat_mul_pi` / 定理 `tan_nat_mul_pi`

English:
theorem tan_nat_mul_pi
  given: (n : Nat)
  statement: tan (n * π) = 0
  proof: tan_zero ▸ tan_periodic.nat_mul_eq n

中文:
定理 tan_nat_mul_pi
  条件: (n : 自然数)
  结论: tan (n * π) = 0
  证明: tan_zero ▸ tan_periodic.nat_mul_eq n

Depends on / 依赖: nat_mul_eq, tan_periodic, tan_periodic.nat_mul_eq, tan_zero
-/
theorem tan_nat_mul_pi (n : Nat) : tan (n * π) = 0 :=
  tan_zero ▸ tan_periodic.nat_mul_eq n

/--
theorem `tan_int_mul_pi` / 定理 `tan_int_mul_pi`

English:
theorem tan_int_mul_pi
  given: (n : Int)
  statement: tan (n * π) = 0
  proof: tan_zero ▸ tan_periodic.int_mul_eq n

中文:
定理 tan_int_mul_pi
  条件: (n : 整数)
  结论: tan (n * π) = 0
  证明: tan_zero ▸ tan_periodic.int_mul_eq n

Depends on / 依赖: int_mul_eq, tan_periodic, tan_periodic.int_mul_eq, tan_zero
-/
theorem tan_int_mul_pi (n : Int) : tan (n * π) = 0 :=
  tan_zero ▸ tan_periodic.int_mul_eq n

/--
theorem `tan_add_nat_mul_pi` / 定理 `tan_add_nat_mul_pi`

English:
theorem tan_add_nat_mul_pi
  given: (x : Real) (n : Nat)
  statement: tan (x + n * π) = tan x
  proof: tan_periodic.nat_mul n x

中文:
定理 tan_add_nat_mul_pi
  条件: (x : 实数) (n : 自然数)
  结论: tan (x + n * π) = tan x
  证明: tan_periodic.nat_mul n x

Depends on / 依赖: nat_mul, tan_periodic, tan_periodic.nat_mul
-/
theorem tan_add_nat_mul_pi (x : Real) (n : Nat) : tan (x + n * π) = tan x :=
  tan_periodic.nat_mul n x

/--
theorem `tan_add_int_mul_pi` / 定理 `tan_add_int_mul_pi`

English:
theorem tan_add_int_mul_pi
  given: (x : Real) (n : Int)
  statement: tan (x + n * π) = tan x
  proof: tan_periodic.int_mul n x

中文:
定理 tan_add_int_mul_pi
  条件: (x : 实数) (n : 整数)
  结论: tan (x + n * π) = tan x
  证明: tan_periodic.int_mul n x

Depends on / 依赖: int_mul, tan_periodic, tan_periodic.int_mul
-/
theorem tan_add_int_mul_pi (x : Real) (n : Int) : tan (x + n * π) = tan x :=
  tan_periodic.int_mul n x

/--
theorem `tan_sub_nat_mul_pi` / 定理 `tan_sub_nat_mul_pi`

English:
theorem tan_sub_nat_mul_pi
  given: (x : Real) (n : Nat)
  statement: tan (x - n * π) = tan x
  proof: tan_periodic.sub_nat_mul_eq n

中文:
定理 tan_sub_nat_mul_pi
  条件: (x : 实数) (n : 自然数)
  结论: tan (x - n * π) = tan x
  证明: tan_periodic.sub_nat_mul_eq n

Depends on / 依赖: sub_nat_mul_eq, tan_periodic, tan_periodic.sub_nat_mul_eq
-/
theorem tan_sub_nat_mul_pi (x : Real) (n : Nat) : tan (x - n * π) = tan x :=
  tan_periodic.sub_nat_mul_eq n

/--
theorem `tan_sub_int_mul_pi` / 定理 `tan_sub_int_mul_pi`

English:
theorem tan_sub_int_mul_pi
  given: (x : Real) (n : Int)
  statement: tan (x - n * π) = tan x
  proof: tan_periodic.sub_int_mul_eq n

中文:
定理 tan_sub_int_mul_pi
  条件: (x : 实数) (n : 整数)
  结论: tan (x - n * π) = tan x
  证明: tan_periodic.sub_int_mul_eq n

Depends on / 依赖: sub_int_mul_eq, tan_periodic, tan_periodic.sub_int_mul_eq
-/
theorem tan_sub_int_mul_pi (x : Real) (n : Int) : tan (x - n * π) = tan x :=
  tan_periodic.sub_int_mul_eq n

/--
theorem `tan_nat_mul_pi_sub` / 定理 `tan_nat_mul_pi_sub`

English:
theorem tan_nat_mul_pi_sub
  given: (x : Real) (n : Nat)
  statement: tan (n * π - x) = -tan x
  proof: tan_neg x ▸ tan_periodic.nat_mul_sub_eq n

中文:
定理 tan_nat_mul_pi_sub
  条件: (x : 实数) (n : 自然数)
  结论: tan (n * π - x) = -tan x
  证明: tan_neg x ▸ tan_periodic.nat_mul_sub_eq n

Depends on / 依赖: nat_mul_sub_eq, tan_neg, tan_periodic, tan_periodic.nat_mul_sub_eq
-/
theorem tan_nat_mul_pi_sub (x : Real) (n : Nat) : tan (n * π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.nat_mul_sub_eq n

/--
theorem `tan_int_mul_pi_sub` / 定理 `tan_int_mul_pi_sub`

English:
theorem tan_int_mul_pi_sub
  given: (x : Real) (n : Int)
  statement: tan (n * π - x) = -tan x
  proof: tan_neg x ▸ tan_periodic.int_mul_sub_eq n

中文:
定理 tan_int_mul_pi_sub
  条件: (x : 实数) (n : 整数)
  结论: tan (n * π - x) = -tan x
  证明: tan_neg x ▸ tan_periodic.int_mul_sub_eq n

Depends on / 依赖: int_mul_sub_eq, tan_neg, tan_periodic, tan_periodic.int_mul_sub_eq
-/
theorem tan_int_mul_pi_sub (x : Real) (n : Int) : tan (n * π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.int_mul_sub_eq n

/--
theorem `tendsto_sin_pi_div_two` / 定理 `tendsto_sin_pi_div_two`

English:
theorem tendsto_sin_pi_div_two
  statement: Tendsto sin (𝓝[<] (π / 2)) (𝓝 1)
  proof: by
  convert! continuous_sin.continuousWithinAt.tendsto
  simp

中文:
定理 tendsto_sin_pi_div_two
  结论: Tendsto sin (𝓝[<] (π / 2)) (𝓝 1)
  证明: by
  convert! continuous_sin.continuousWithinAt.tendsto
  simp

Depends on / 依赖: continuousWithinAt, continuous_sin, continuous_sin.continuousWithinAt.tendsto, convert, tendsto
-/
theorem tendsto_sin_pi_div_two : Tendsto sin (𝓝[<] (π / 2)) (𝓝 1) := by
  convert! continuous_sin.continuousWithinAt.tendsto
  simp

/--
theorem `tendsto_cos_pi_div_two` / 定理 `tendsto_cos_pi_div_two`

English:
theorem tendsto_cos_pi_div_two
  statement: Tendsto cos (𝓝[<] (π / 2)) (𝓝[>] 0)
  proof: by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · convert! continuous_cos.continuousWithinAt.tendsto
    simp
  · filter_upwards [Ioo_mem_nhdsLT (neg_lt_self pi_div_two_pos)] with x hx
    exact cos_pos_of_mem_Ioo hx

中文:
定理 tendsto_cos_pi_div_two
  结论: Tendsto cos (𝓝[<] (π / 2)) (𝓝[>] 0)
  证明: by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · convert! continuous_cos.continuousWithinAt.tendsto
    simp
  · filter_upwards [Ioo_mem_nhdsLT (neg_lt_self pi_div_two_pos)] with x hx
    exact cos_pos_of_mem_Ioo hx

Depends on / 依赖: Ioo_mem_nhdsLT, continuousWithinAt, continuous_cos, continuous_cos.continuousWithinAt.tendsto, convert, cos_pos_of_mem_Ioo, filter_upwards, neg_lt_self, pi_div_two_pos, tendsto, tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
-/
theorem tendsto_cos_pi_div_two : Tendsto cos (𝓝[<] (π / 2)) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · convert! continuous_cos.continuousWithinAt.tendsto
    simp
  · filter_upwards [Ioo_mem_nhdsLT (neg_lt_self pi_div_two_pos)] with x hx
    exact cos_pos_of_mem_Ioo hx

/--
theorem `tendsto_tan_pi_div_two` / 定理 `tendsto_tan_pi_div_two`

English:
theorem tendsto_tan_pi_div_two
  statement: Tendsto tan (𝓝[<] (π / 2)) atTop
  proof: by
  convert!
    tendsto_cos_pi_div_two.inv_tendsto_nhdsGT_zero.atTop_mul_pos zero_lt_one
      tendsto_sin_pi_div_two using 1
  simp only [Pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]

中文:
定理 tendsto_tan_pi_div_two
  结论: Tendsto tan (𝓝[<] (π / 2)) atTop
  证明: by
  convert!
    tendsto_cos_pi_div_two.inv_tendsto_nhdsGT_zero.atTop_mul_pos zero_lt_one
      tendsto_sin_pi_div_two using 1
  simp only [Pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]

Depends on / 依赖: Pi.inv_apply, atTop_mul_pos, convert, div_eq_inv_mul, eqToHom_right, inv_apply, inv_tendsto_nhdsGT_zero, tan_eq_sin_div_cos, tendsto_cos_pi_div_two, tendsto_cos_pi_div_two.inv_tendsto_nhdsGT_zero.atTop_mul_pos, tendsto_sin_pi_div_two, zero_lt_one
-/
theorem tendsto_tan_pi_div_two : Tendsto tan (𝓝[<] (π / 2)) atTop := by
  convert!
    tendsto_cos_pi_div_two.inv_tendsto_nhdsGT_zero.atTop_mul_pos zero_lt_one
      tendsto_sin_pi_div_two using 1
  simp only [Pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]

/--
theorem `tendsto_sin_neg_pi_div_two` / 定理 `tendsto_sin_neg_pi_div_two`

English:
theorem tendsto_sin_neg_pi_div_two
  statement: Tendsto sin (𝓝[>] (-(π / 2))) (𝓝 (-1))
  proof: by
  convert! continuous_sin.continuousWithinAt.tendsto using 2
  simp

中文:
定理 tendsto_sin_neg_pi_div_two
  结论: Tendsto sin (𝓝[>] (-(π / 2))) (𝓝 (-1))
  证明: by
  convert! continuous_sin.continuousWithinAt.tendsto using 2
  simp

Depends on / 依赖: continuousWithinAt, continuous_sin, continuous_sin.continuousWithinAt.tendsto, convert, tendsto
-/
theorem tendsto_sin_neg_pi_div_two : Tendsto sin (𝓝[>] (-(π / 2))) (𝓝 (-1)) := by
  convert! continuous_sin.continuousWithinAt.tendsto using 2
  simp

/--
theorem `tendsto_cos_neg_pi_div_two` / 定理 `tendsto_cos_neg_pi_div_two`

English:
theorem tendsto_cos_neg_pi_div_two
  statement: Tendsto cos (𝓝[>] (-(π / 2))) (𝓝[>] 0)
  proof: by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · convert! continuous_cos.continuousWithinAt.tendsto
    simp
  · filter_upwards [Ioo_mem_nhdsGT (neg_lt_self pi_div_two_pos)] with x hx
    exact cos_pos_of_mem_Ioo hx

中文:
定理 tendsto_cos_neg_pi_div_two
  结论: Tendsto cos (𝓝[>] (-(π / 2))) (𝓝[>] 0)
  证明: by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · convert! continuous_cos.continuousWithinAt.tendsto
    simp
  · filter_upwards [Ioo_mem_nhdsGT (neg_lt_self pi_div_two_pos)] with x hx
    exact cos_pos_of_mem_Ioo hx

Depends on / 依赖: Ioo_mem_nhdsGT, continuousWithinAt, continuous_cos, continuous_cos.continuousWithinAt.tendsto, convert, cos_pos_of_mem_Ioo, eqToHom_right, filter_upwards, neg_lt_self, pi_div_two_pos, tendsto, tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
-/
theorem tendsto_cos_neg_pi_div_two : Tendsto cos (𝓝[>] (-(π / 2))) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · convert! continuous_cos.continuousWithinAt.tendsto
    simp
  · filter_upwards [Ioo_mem_nhdsGT (neg_lt_self pi_div_two_pos)] with x hx
    exact cos_pos_of_mem_Ioo hx

/--
theorem `tendsto_tan_neg_pi_div_two` / 定理 `tendsto_tan_neg_pi_div_two`

English:
theorem tendsto_tan_neg_pi_div_two
  statement: Tendsto tan (𝓝[>] (-(π / 2))) atBot
  proof: by
  convert!
    tendsto_cos_neg_pi_div_two.inv_tendsto_nhdsGT_zero.atTop_mul_neg (by simp)
      tendsto_sin_neg_pi_div_two using 1
  simp only [Pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]

中文:
定理 tendsto_tan_neg_pi_div_two
  结论: Tendsto tan (𝓝[>] (-(π / 2))) atBot
  证明: by
  convert!
    tendsto_cos_neg_pi_div_two.inv_tendsto_nhdsGT_zero.atTop_mul_neg (by simp)
      tendsto_sin_neg_pi_div_two using 1
  simp only [Pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]

Depends on / 依赖: Pi.inv_apply, _comp, atTop_mul_neg, convert, div_eq_inv_mul, inv_apply, inv_tendsto_nhdsGT_zero, tan_eq_sin_div_cos, tendsto_cos_neg_pi_div_two, tendsto_cos_neg_pi_div_two.inv_tendsto_nhdsGT_zero.atTop_mul_neg, tendsto_sin_neg_pi_div_two
-/
theorem tendsto_tan_neg_pi_div_two : Tendsto tan (𝓝[>] (-(π / 2))) atBot := by
  convert!
    tendsto_cos_neg_pi_div_two.inv_tendsto_nhdsGT_zero.atTop_mul_neg (by simp)
      tendsto_sin_neg_pi_div_two using 1
  simp only [Pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]

end Real

namespace Complex

open Real

/--
theorem `sin_eq_zero_iff_cos_eq` / 定理 `sin_eq_zero_iff_cos_eq`

English:
theorem sin_eq_zero_iff_cos_eq
  given: {z : Complex}
  statement: sin z = 0 ↔ cos z = 1 ∨ cos z = -1
  proof: by
  rw [← mul_self_eq_one_iff]; rw [← sin_sq_add_cos_sq]; rw [sq]; rw [sq]; rw [right_eq_add]; rw [mul_eq_zero]; rw [or_self]

中文:
定理 sin_eq_zero_iff_cos_eq
  条件: {z : Complex}
  结论: sin z = 0 ↔ cos z = 1 ∨ cos z = -1
  证明: by
  rw [← mul_self_eq_one_iff]; rw [← sin_sq_add_cos_sq]; rw [sq]; rw [sq]; rw [right_eq_add]; rw [mul_eq_zero]; rw [or_self]

Depends on / 依赖: mul_eq_zero, mul_self_eq_one_iff, or_self, right_eq_add, sin_sq_add_cos_sq
-/
theorem sin_eq_zero_iff_cos_eq {z : Complex} : sin z = 0 ↔ cos z = 1 ∨ cos z = -1 := by
  rw [← mul_self_eq_one_iff]; rw [← sin_sq_add_cos_sq]; rw [sq]; rw [sq]; rw [right_eq_add]; rw [mul_eq_zero]; rw [or_self]

/--
theorem `cos_eq_zero_iff_sin_eq` / 定理 `cos_eq_zero_iff_sin_eq`

English:
theorem cos_eq_zero_iff_sin_eq
  given: {z : Complex}
  statement: cos z = 0 ↔ sin z = 1 ∨ sin z = -1
  proof: by
  rw [← mul_self_eq_one_iff]; rw [← sin_sq_add_cos_sq]; rw [sq]; rw [sq]; rw [left_eq_add]; rw [mul_eq_zero]; rw [or_self]

@[simp]

中文:
定理 cos_eq_zero_iff_sin_eq
  条件: {z : Complex}
  结论: cos z = 0 ↔ sin z = 1 ∨ sin z = -1
  证明: by
  rw [← mul_self_eq_one_iff]; rw [← sin_sq_add_cos_sq]; rw [sq]; rw [sq]; rw [left_eq_add]; rw [mul_eq_zero]; rw [or_self]

@[simp]

Depends on / 依赖: left_eq_add, mul_eq_zero, mul_self_eq_one_iff, or_self, sin_sq_add_cos_sq
-/
theorem cos_eq_zero_iff_sin_eq {z : Complex} : cos z = 0 ↔ sin z = 1 ∨ sin z = -1 := by
  rw [← mul_self_eq_one_iff]; rw [← sin_sq_add_cos_sq]; rw [sq]; rw [sq]; rw [left_eq_add]; rw [mul_eq_zero]; rw [or_self]

@[simp]
/--
theorem `cos_pi_div_two` / 定理 `cos_pi_div_two`

English:
theorem cos_pi_div_two
  statement: cos (π / 2) = 0
  proof: calc
    cos (π / 2) = Real.cos (π / 2) := by rw [ofReal_cos]; simp
    _ = 0 := by simp

@[simp]

中文:
定理 cos_pi_div_two
  结论: cos (π / 2) = 0
  证明: calc
    cos (π / 2) = Real.cos (π / 2) := by rw [ofReal_cos]; simp
    _ = 0 := by simp

@[simp]

Depends on / 依赖: Real.cos, ofReal_cos
-/
theorem cos_pi_div_two : cos (π / 2) = 0 :=
  calc
    cos (π / 2) = Real.cos (π / 2) := by rw [ofReal_cos]; simp
    _ = 0 := by simp

@[simp]
/--
theorem `sin_pi_div_two` / 定理 `sin_pi_div_two`

English:
theorem sin_pi_div_two
  statement: sin (π / 2) = 1
  proof: calc
    sin (π / 2) = Real.sin (π / 2) := by rw [ofReal_sin]; simp
    _ = 1 := by simp

@[simp]

中文:
定理 sin_pi_div_two
  结论: sin (π / 2) = 1
  证明: calc
    sin (π / 2) = Real.sin (π / 2) := by rw [ofReal_sin]; simp
    _ = 1 := by simp

@[simp]

Depends on / 依赖: Real.sin, ofReal_sin
-/
theorem sin_pi_div_two : sin (π / 2) = 1 :=
  calc
    sin (π / 2) = Real.sin (π / 2) := by rw [ofReal_sin]; simp
    _ = 1 := by simp

@[simp]
/--
theorem `sin_pi` / 定理 `sin_pi`

English:
theorem sin_pi
  statement: sin π = 0
  proof: by rw [← ofReal_sin, Real.sin_pi]; simp

@[simp]

中文:
定理 sin_pi
  结论: sin π = 0
  证明: by rw [← ofReal_sin, Real.sin_pi]; simp

@[simp]

Depends on / 依赖: Real.sin_pi, ofReal_sin, sin_pi
-/
theorem sin_pi : sin π = 0 := by rw [← ofReal_sin, Real.sin_pi]; simp

@[simp]
/--
theorem `cos_pi` / 定理 `cos_pi`

English:
theorem cos_pi
  statement: cos π = -1
  proof: by rw [← ofReal_cos, Real.cos_pi]; simp

@[simp]

中文:
定理 cos_pi
  结论: cos π = -1
  证明: by rw [← ofReal_cos, Real.cos_pi]; simp

@[simp]

Depends on / 依赖: Real.cos_pi, cos_pi, ofReal_cos
-/
theorem cos_pi : cos π = -1 := by rw [← ofReal_cos, Real.cos_pi]; simp

@[simp]
/--
theorem `sin_two_pi` / 定理 `sin_two_pi`

English:
theorem sin_two_pi
  statement: sin (2 * π) = 0
  proof: by simp [two_mul, sin_add]

@[simp]

中文:
定理 sin_two_pi
  结论: sin (2 * π) = 0
  证明: by simp [two_mul, sin_add]

@[simp]

Depends on / 依赖: sin_add, two_mul
-/
theorem sin_two_pi : sin (2 * π) = 0 := by simp [two_mul, sin_add]

@[simp]
/--
theorem `cos_two_pi` / 定理 `cos_two_pi`

English:
theorem cos_two_pi
  statement: cos (2 * π) = 1
  proof: by simp [two_mul, cos_add]

中文:
定理 cos_two_pi
  结论: cos (2 * π) = 1
  证明: by simp [two_mul, cos_add]

Depends on / 依赖: cos_add, two_mul
-/
theorem cos_two_pi : cos (2 * π) = 1 := by simp [two_mul, cos_add]

/--
theorem `sin_antiperiodic` / 定理 `sin_antiperiodic`

English:
theorem sin_antiperiodic
  statement: Function.Antiperiodic sin π
  proof: by simp [sin_add]

中文:
定理 sin_antiperiodic
  结论: Function.Antiperiodic sin π
  证明: by simp [sin_add]

Depends on / 依赖: sin_add
-/
theorem sin_antiperiodic : Function.Antiperiodic sin π := by simp [sin_add]

/--
theorem `sin_periodic` / 定理 `sin_periodic`

English:
theorem sin_periodic
  statement: Function.Periodic sin (2 * π)
  proof: sin_antiperiodic.periodic_two_mul

中文:
定理 sin_periodic
  结论: Function.Periodic sin (2 * π)
  证明: sin_antiperiodic.periodic_two_mul

Depends on / 依赖: periodic_two_mul, sin_antiperiodic, sin_antiperiodic.periodic_two_mul
-/
theorem sin_periodic : Function.Periodic sin (2 * π) :=
  sin_antiperiodic.periodic_two_mul

/--
theorem `sin_add_pi` / 定理 `sin_add_pi`

English:
theorem sin_add_pi
  given: (x : Complex)
  statement: sin (x + π) = -sin x
  proof: sin_antiperiodic x

中文:
定理 sin_add_pi
  条件: (x : Complex)
  结论: sin (x + π) = -sin x
  证明: sin_antiperiodic x

Depends on / 依赖: sin_antiperiodic
-/
theorem sin_add_pi (x : Complex) : sin (x + π) = -sin x :=
  sin_antiperiodic x

/--
theorem `sin_add_two_pi` / 定理 `sin_add_two_pi`

English:
theorem sin_add_two_pi
  given: (x : Complex)
  statement: sin (x + 2 * π) = sin x
  proof: sin_periodic x

中文:
定理 sin_add_two_pi
  条件: (x : Complex)
  结论: sin (x + 2 * π) = sin x
  证明: sin_periodic x

Depends on / 依赖: sin_periodic
-/
theorem sin_add_two_pi (x : Complex) : sin (x + 2 * π) = sin x :=
  sin_periodic x

/--
theorem `sin_sub_pi` / 定理 `sin_sub_pi`

English:
theorem sin_sub_pi
  given: (x : Complex)
  statement: sin (x - π) = -sin x
  proof: sin_antiperiodic.sub_eq x

中文:
定理 sin_sub_pi
  条件: (x : Complex)
  结论: sin (x - π) = -sin x
  证明: sin_antiperiodic.sub_eq x

Depends on / 依赖: sin_antiperiodic, sin_antiperiodic.sub_eq, sub_eq
-/
theorem sin_sub_pi (x : Complex) : sin (x - π) = -sin x :=
  sin_antiperiodic.sub_eq x

/--
theorem `sin_sub_two_pi` / 定理 `sin_sub_two_pi`

English:
theorem sin_sub_two_pi
  given: (x : Complex)
  statement: sin (x - 2 * π) = sin x
  proof: sin_periodic.sub_eq x

中文:
定理 sin_sub_two_pi
  条件: (x : Complex)
  结论: sin (x - 2 * π) = sin x
  证明: sin_periodic.sub_eq x

Depends on / 依赖: sin_periodic, sin_periodic.sub_eq, sub_eq
-/
theorem sin_sub_two_pi (x : Complex) : sin (x - 2 * π) = sin x :=
  sin_periodic.sub_eq x

/--
theorem `sin_pi_sub` / 定理 `sin_pi_sub`

English:
theorem sin_pi_sub
  given: (x : Complex)
  statement: sin (π - x) = sin x
  proof: neg_neg (sin x) ▸ sin_neg x ▸ sin_antiperiodic.sub_eq'

中文:
定理 sin_pi_sub
  条件: (x : Complex)
  结论: sin (π - x) = sin x
  证明: neg_neg (sin x) ▸ sin_neg x ▸ sin_antiperiodic.sub_eq'

Depends on / 依赖: neg_neg, sin_antiperiodic, sin_antiperiodic.sub_eq, sin_neg, sub_eq
-/
theorem sin_pi_sub (x : Complex) : sin (π - x) = sin x :=
  neg_neg (sin x) ▸ sin_neg x ▸ sin_antiperiodic.sub_eq'

/--
theorem `sin_two_pi_sub` / 定理 `sin_two_pi_sub`

English:
theorem sin_two_pi_sub
  given: (x : Complex)
  statement: sin (2 * π - x) = -sin x
  proof: sin_neg x ▸ sin_periodic.sub_eq'

中文:
定理 sin_two_pi_sub
  条件: (x : Complex)
  结论: sin (2 * π - x) = -sin x
  证明: sin_neg x ▸ sin_periodic.sub_eq'

Depends on / 依赖: sin_neg, sin_periodic, sin_periodic.sub_eq, sub_eq
-/
theorem sin_two_pi_sub (x : Complex) : sin (2 * π - x) = -sin x :=
  sin_neg x ▸ sin_periodic.sub_eq'

/--
theorem `sin_nat_mul_pi` / 定理 `sin_nat_mul_pi`

English:
theorem sin_nat_mul_pi
  given: (n : Nat)
  statement: sin (n * π) = 0
  proof: sin_antiperiodic.nat_mul_eq_of_eq_zero sin_zero n

中文:
定理 sin_nat_mul_pi
  条件: (n : 自然数)
  结论: sin (n * π) = 0
  证明: sin_antiperiodic.nat_mul_eq_of_eq_zero sin_zero n

Depends on / 依赖: nat_mul_eq_of_eq_zero, sin_antiperiodic, sin_antiperiodic.nat_mul_eq_of_eq_zero, sin_zero
-/
theorem sin_nat_mul_pi (n : Nat) : sin (n * π) = 0 :=
  sin_antiperiodic.nat_mul_eq_of_eq_zero sin_zero n

/--
theorem `sin_int_mul_pi` / 定理 `sin_int_mul_pi`

English:
theorem sin_int_mul_pi
  given: (n : Int)
  statement: sin (n * π) = 0
  proof: sin_antiperiodic.int_mul_eq_of_eq_zero sin_zero n

中文:
定理 sin_int_mul_pi
  条件: (n : 整数)
  结论: sin (n * π) = 0
  证明: sin_antiperiodic.int_mul_eq_of_eq_zero sin_zero n

Depends on / 依赖: int_mul_eq_of_eq_zero, sin_antiperiodic, sin_antiperiodic.int_mul_eq_of_eq_zero, sin_zero
-/
theorem sin_int_mul_pi (n : Int) : sin (n * π) = 0 :=
  sin_antiperiodic.int_mul_eq_of_eq_zero sin_zero n

/--
theorem `sin_add_nat_mul_two_pi` / 定理 `sin_add_nat_mul_two_pi`

English:
theorem sin_add_nat_mul_two_pi
  given: (x : Complex) (n : Nat)
  statement: sin (x + n * (2 * π)) = sin x
  proof: sin_periodic.nat_mul n x

中文:
定理 sin_add_nat_mul_two_pi
  条件: (x : Complex) (n : 自然数)
  结论: sin (x + n * (2 * π)) = sin x
  证明: sin_periodic.nat_mul n x

Depends on / 依赖: nat_mul, sin_periodic, sin_periodic.nat_mul
-/
theorem sin_add_nat_mul_two_pi (x : Complex) (n : Nat) : sin (x + n * (2 * π)) = sin x :=
  sin_periodic.nat_mul n x

/--
theorem `sin_add_int_mul_two_pi` / 定理 `sin_add_int_mul_two_pi`

English:
theorem sin_add_int_mul_two_pi
  given: (x : Complex) (n : Int)
  statement: sin (x + n * (2 * π)) = sin x
  proof: sin_periodic.int_mul n x

中文:
定理 sin_add_int_mul_two_pi
  条件: (x : Complex) (n : 整数)
  结论: sin (x + n * (2 * π)) = sin x
  证明: sin_periodic.int_mul n x

Depends on / 依赖: int_mul, sin_periodic, sin_periodic.int_mul
-/
theorem sin_add_int_mul_two_pi (x : Complex) (n : Int) : sin (x + n * (2 * π)) = sin x :=
  sin_periodic.int_mul n x

/--
theorem `sin_sub_nat_mul_two_pi` / 定理 `sin_sub_nat_mul_two_pi`

English:
theorem sin_sub_nat_mul_two_pi
  given: (x : Complex) (n : Nat)
  statement: sin (x - n * (2 * π)) = sin x
  proof: sin_periodic.sub_nat_mul_eq n

中文:
定理 sin_sub_nat_mul_two_pi
  条件: (x : Complex) (n : 自然数)
  结论: sin (x - n * (2 * π)) = sin x
  证明: sin_periodic.sub_nat_mul_eq n

Depends on / 依赖: sin_periodic, sin_periodic.sub_nat_mul_eq, sub_nat_mul_eq
-/
theorem sin_sub_nat_mul_two_pi (x : Complex) (n : Nat) : sin (x - n * (2 * π)) = sin x :=
  sin_periodic.sub_nat_mul_eq n

/--
theorem `sin_sub_int_mul_two_pi` / 定理 `sin_sub_int_mul_two_pi`

English:
theorem sin_sub_int_mul_two_pi
  given: (x : Complex) (n : Int)
  statement: sin (x - n * (2 * π)) = sin x
  proof: sin_periodic.sub_int_mul_eq n

中文:
定理 sin_sub_int_mul_two_pi
  条件: (x : Complex) (n : 整数)
  结论: sin (x - n * (2 * π)) = sin x
  证明: sin_periodic.sub_int_mul_eq n

Depends on / 依赖: sin_periodic, sin_periodic.sub_int_mul_eq, sub_int_mul_eq
-/
theorem sin_sub_int_mul_two_pi (x : Complex) (n : Int) : sin (x - n * (2 * π)) = sin x :=
  sin_periodic.sub_int_mul_eq n

/--
theorem `sin_nat_mul_two_pi_sub` / 定理 `sin_nat_mul_two_pi_sub`

English:
theorem sin_nat_mul_two_pi_sub
  given: (x : Complex) (n : Nat)
  statement: sin (n * (2 * π) - x) = -sin x
  proof: sin_neg x ▸ sin_periodic.nat_mul_sub_eq n

中文:
定理 sin_nat_mul_two_pi_sub
  条件: (x : Complex) (n : 自然数)
  结论: sin (n * (2 * π) - x) = -sin x
  证明: sin_neg x ▸ sin_periodic.nat_mul_sub_eq n

Depends on / 依赖: nat_mul_sub_eq, sin_neg, sin_periodic, sin_periodic.nat_mul_sub_eq
-/
theorem sin_nat_mul_two_pi_sub (x : Complex) (n : Nat) : sin (n * (2 * π) - x) = -sin x :=
  sin_neg x ▸ sin_periodic.nat_mul_sub_eq n

/--
theorem `sin_int_mul_two_pi_sub` / 定理 `sin_int_mul_two_pi_sub`

English:
theorem sin_int_mul_two_pi_sub
  given: (x : Complex) (n : Int)
  statement: sin (n * (2 * π) - x) = -sin x
  proof: sin_neg x ▸ sin_periodic.int_mul_sub_eq n

中文:
定理 sin_int_mul_two_pi_sub
  条件: (x : Complex) (n : 整数)
  结论: sin (n * (2 * π) - x) = -sin x
  证明: sin_neg x ▸ sin_periodic.int_mul_sub_eq n

Depends on / 依赖: int_mul_sub_eq, sin_neg, sin_periodic, sin_periodic.int_mul_sub_eq
-/
theorem sin_int_mul_two_pi_sub (x : Complex) (n : Int) : sin (n * (2 * π) - x) = -sin x :=
  sin_neg x ▸ sin_periodic.int_mul_sub_eq n

/--
theorem `cos_antiperiodic` / 定理 `cos_antiperiodic`

English:
theorem cos_antiperiodic
  statement: Function.Antiperiodic cos π
  proof: by simp [cos_add]

中文:
定理 cos_antiperiodic
  结论: Function.Antiperiodic cos π
  证明: by simp [cos_add]

Depends on / 依赖: Comma.preRight, Faithful, cos_add, preRight
-/
theorem cos_antiperiodic : Function.Antiperiodic cos π := by simp [cos_add]

/--
theorem `cos_periodic` / 定理 `cos_periodic`

English:
theorem cos_periodic
  statement: Function.Periodic cos (2 * π)
  proof: cos_antiperiodic.periodic_two_mul

中文:
定理 cos_periodic
  结论: Function.Periodic cos (2 * π)
  证明: cos_antiperiodic.periodic_two_mul

Depends on / 依赖: Comma.preRight, cos_antiperiodic, cos_antiperiodic.periodic_two_mul, periodic_two_mul, preRight
-/
theorem cos_periodic : Function.Periodic cos (2 * π) :=
  cos_antiperiodic.periodic_two_mul

/--
theorem `cos_add_pi` / 定理 `cos_add_pi`

English:
theorem cos_add_pi
  given: (x : Complex)
  statement: cos (x + π) = -cos x
  proof: cos_antiperiodic x

中文:
定理 cos_add_pi
  条件: (x : Complex)
  结论: cos (x + π) = -cos x
  证明: cos_antiperiodic x

Depends on / 依赖: Comma.preRight, EssSurj, cos_antiperiodic, preRight
-/
theorem cos_add_pi (x : Complex) : cos (x + π) = -cos x :=
  cos_antiperiodic x

/--
theorem `cos_add_two_pi` / 定理 `cos_add_two_pi`

English:
theorem cos_add_two_pi
  given: (x : Complex)
  statement: cos (x + 2 * π) = cos x
  proof: cos_periodic x

中文:
定理 cos_add_two_pi
  条件: (x : Complex)
  结论: cos (x + 2 * π) = cos x
  证明: cos_periodic x

Depends on / 依赖: cos_periodic
-/
theorem cos_add_two_pi (x : Complex) : cos (x + 2 * π) = cos x :=
  cos_periodic x

/--
theorem `cos_sub_pi` / 定理 `cos_sub_pi`

English:
theorem cos_sub_pi
  given: (x : Complex)
  statement: cos (x - π) = -cos x
  proof: cos_antiperiodic.sub_eq x

中文:
定理 cos_sub_pi
  条件: (x : Complex)
  结论: cos (x - π) = -cos x
  证明: cos_antiperiodic.sub_eq x

Depends on / 依赖: cos_antiperiodic, cos_antiperiodic.sub_eq, sub_eq
-/
theorem cos_sub_pi (x : Complex) : cos (x - π) = -cos x :=
  cos_antiperiodic.sub_eq x

/--
theorem `cos_sub_two_pi` / 定理 `cos_sub_two_pi`

English:
theorem cos_sub_two_pi
  given: (x : Complex)
  statement: cos (x - 2 * π) = cos x
  proof: cos_periodic.sub_eq x

中文:
定理 cos_sub_two_pi
  条件: (x : Complex)
  结论: cos (x - 2 * π) = cos x
  证明: cos_periodic.sub_eq x

Depends on / 依赖: cos_periodic, cos_periodic.sub_eq, ext_iff, sub_eq
-/
theorem cos_sub_two_pi (x : Complex) : cos (x - 2 * π) = cos x :=
  cos_periodic.sub_eq x

/--
theorem `cos_pi_sub` / 定理 `cos_pi_sub`

English:
theorem cos_pi_sub
  given: (x : Complex)
  statement: cos (π - x) = -cos x
  proof: cos_neg x ▸ cos_antiperiodic.sub_eq'

中文:
定理 cos_pi_sub
  条件: (x : Complex)
  结论: cos (π - x) = -cos x
  证明: cos_neg x ▸ cos_antiperiodic.sub_eq'

Depends on / 依赖: G.map_injective, cos_antiperiodic, cos_antiperiodic.sub_eq, cos_neg, f.right, map_injective, sub_eq
-/
theorem cos_pi_sub (x : Complex) : cos (π - x) = -cos x :=
  cos_neg x ▸ cos_antiperiodic.sub_eq'

/--
theorem `cos_two_pi_sub` / 定理 `cos_two_pi_sub`

English:
theorem cos_two_pi_sub
  given: (x : Complex)
  statement: cos (2 * π - x) = cos x
  proof: cos_neg x ▸ cos_periodic.sub_eq'

中文:
定理 cos_two_pi_sub
  条件: (x : Complex)
  结论: cos (2 * π - x) = cos x
  证明: cos_neg x ▸ cos_periodic.sub_eq'

Depends on / 依赖: G.preimage, Iso.refl, cos_neg, cos_periodic, cos_periodic.sub_eq, h.hom, preimage, sub_eq
-/
theorem cos_two_pi_sub (x : Complex) : cos (2 * π - x) = cos x :=
  cos_neg x ▸ cos_periodic.sub_eq'

/--
theorem `cos_nat_mul_two_pi` / 定理 `cos_nat_mul_two_pi`

English:
theorem cos_nat_mul_two_pi
  given: (n : Nat)
  statement: cos (n * (2 * π)) = 1
  proof: (cos_periodic.nat_mul_eq n).trans cos_zero

中文:
定理 cos_nat_mul_two_pi
  条件: (n : 自然数)
  结论: cos (n * (2 * π)) = 1
  证明: (cos_periodic.nat_mul_eq n).trans cos_zero

Depends on / 依赖: cos_periodic, cos_periodic.nat_mul_eq, cos_zero, nat_mul_eq
-/
theorem cos_nat_mul_two_pi (n : Nat) : cos (n * (2 * π)) = 1 :=
  (cos_periodic.nat_mul_eq n).trans cos_zero

/--
theorem `cos_int_mul_two_pi` / 定理 `cos_int_mul_two_pi`

English:
theorem cos_int_mul_two_pi
  given: (n : Int)
  statement: cos (n * (2 * π)) = 1
  proof: (cos_periodic.int_mul_eq n).trans cos_zero

中文:
定理 cos_int_mul_two_pi
  条件: (n : 整数)
  结论: cos (n * (2 * π)) = 1
  证明: (cos_periodic.int_mul_eq n).trans cos_zero

Depends on / 依赖: cos_periodic, cos_periodic.int_mul_eq, cos_zero, int_mul_eq
-/
theorem cos_int_mul_two_pi (n : Int) : cos (n * (2 * π)) = 1 :=
  (cos_periodic.int_mul_eq n).trans cos_zero

/--
theorem `cos_add_nat_mul_two_pi` / 定理 `cos_add_nat_mul_two_pi`

English:
theorem cos_add_nat_mul_two_pi
  given: (x : Complex) (n : Nat)
  statement: cos (x + n * (2 * π)) = cos x
  proof: cos_periodic.nat_mul n x

中文:
定理 cos_add_nat_mul_two_pi
  条件: (x : Complex) (n : 自然数)
  结论: cos (x + n * (2 * π)) = cos x
  证明: cos_periodic.nat_mul n x

Depends on / 依赖: cos_periodic, cos_periodic.nat_mul, nat_mul
-/
theorem cos_add_nat_mul_two_pi (x : Complex) (n : Nat) : cos (x + n * (2 * π)) = cos x :=
  cos_periodic.nat_mul n x

/--
theorem `cos_add_int_mul_two_pi` / 定理 `cos_add_int_mul_two_pi`

English:
theorem cos_add_int_mul_two_pi
  given: (x : Complex) (n : Int)
  statement: cos (x + n * (2 * π)) = cos x
  proof: cos_periodic.int_mul n x

中文:
定理 cos_add_int_mul_two_pi
  条件: (x : Complex) (n : 整数)
  结论: cos (x + n * (2 * π)) = cos x
  证明: cos_periodic.int_mul n x

Depends on / 依赖: cos_periodic, cos_periodic.int_mul, int_mul
-/
theorem cos_add_int_mul_two_pi (x : Complex) (n : Int) : cos (x + n * (2 * π)) = cos x :=
  cos_periodic.int_mul n x

/--
theorem `cos_sub_nat_mul_two_pi` / 定理 `cos_sub_nat_mul_two_pi`

English:
theorem cos_sub_nat_mul_two_pi
  given: (x : Complex) (n : Nat)
  statement: cos (x - n * (2 * π)) = cos x
  proof: cos_periodic.sub_nat_mul_eq n

中文:
定理 cos_sub_nat_mul_two_pi
  条件: (x : Complex) (n : 自然数)
  结论: cos (x - n * (2 * π)) = cos x
  证明: cos_periodic.sub_nat_mul_eq n

Depends on / 依赖: cos_periodic, cos_periodic.sub_nat_mul_eq, sub_nat_mul_eq
-/
theorem cos_sub_nat_mul_two_pi (x : Complex) (n : Nat) : cos (x - n * (2 * π)) = cos x :=
  cos_periodic.sub_nat_mul_eq n

/--
theorem `cos_sub_int_mul_two_pi` / 定理 `cos_sub_int_mul_two_pi`

English:
theorem cos_sub_int_mul_two_pi
  given: (x : Complex) (n : Int)
  statement: cos (x - n * (2 * π)) = cos x
  proof: cos_periodic.sub_int_mul_eq n

中文:
定理 cos_sub_int_mul_two_pi
  条件: (x : Complex) (n : 整数)
  结论: cos (x - n * (2 * π)) = cos x
  证明: cos_periodic.sub_int_mul_eq n

Depends on / 依赖: cos_periodic, cos_periodic.sub_int_mul_eq, sub_int_mul_eq
-/
theorem cos_sub_int_mul_two_pi (x : Complex) (n : Int) : cos (x - n * (2 * π)) = cos x :=
  cos_periodic.sub_int_mul_eq n

/--
theorem `cos_nat_mul_two_pi_sub` / 定理 `cos_nat_mul_two_pi_sub`

English:
theorem cos_nat_mul_two_pi_sub
  given: (x : Complex) (n : Nat)
  statement: cos (n * (2 * π) - x) = cos x
  proof: cos_neg x ▸ cos_periodic.nat_mul_sub_eq n

中文:
定理 cos_nat_mul_two_pi_sub
  条件: (x : Complex) (n : 自然数)
  结论: cos (n * (2 * π) - x) = cos x
  证明: cos_neg x ▸ cos_periodic.nat_mul_sub_eq n

Depends on / 依赖: cos_neg, cos_periodic, cos_periodic.nat_mul_sub_eq, nat_mul_sub_eq
-/
theorem cos_nat_mul_two_pi_sub (x : Complex) (n : Nat) : cos (n * (2 * π) - x) = cos x :=
  cos_neg x ▸ cos_periodic.nat_mul_sub_eq n

/--
theorem `cos_int_mul_two_pi_sub` / 定理 `cos_int_mul_two_pi_sub`

English:
theorem cos_int_mul_two_pi_sub
  given: (x : Complex) (n : Int)
  statement: cos (n * (2 * π) - x) = cos x
  proof: cos_neg x ▸ cos_periodic.int_mul_sub_eq n

中文:
定理 cos_int_mul_two_pi_sub
  条件: (x : Complex) (n : 整数)
  结论: cos (n * (2 * π) - x) = cos x
  证明: cos_neg x ▸ cos_periodic.int_mul_sub_eq n

Depends on / 依赖: cos_neg, cos_periodic, cos_periodic.int_mul_sub_eq, int_mul_sub_eq
-/
theorem cos_int_mul_two_pi_sub (x : Complex) (n : Int) : cos (n * (2 * π) - x) = cos x :=
  cos_neg x ▸ cos_periodic.int_mul_sub_eq n

/--
theorem `cos_nat_mul_two_pi_add_pi` / 定理 `cos_nat_mul_two_pi_add_pi`

English:
theorem cos_nat_mul_two_pi_add_pi
  given: (n : Nat)
  statement: cos (n * (2 * π) + π) = -1
  proof: by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).add_antiperiod_eq cos_antiperiodic

中文:
定理 cos_nat_mul_two_pi_add_pi
  条件: (n : 自然数)
  结论: cos (n * (2 * π) + π) = -1
  证明: by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).add_antiperiod_eq cos_antiperiodic

Depends on / 依赖: add_antiperiod_eq, cos_antiperiodic, cos_periodic, cos_periodic.nat_mul, cos_zero, nat_mul
-/
theorem cos_nat_mul_two_pi_add_pi (n : Nat) : cos (n * (2 * π) + π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).add_antiperiod_eq cos_antiperiodic

/--
theorem `cos_int_mul_two_pi_add_pi` / 定理 `cos_int_mul_two_pi_add_pi`

English:
theorem cos_int_mul_two_pi_add_pi
  given: (n : Int)
  statement: cos (n * (2 * π) + π) = -1
  proof: by
  simpa only [cos_zero] using (cos_periodic.int_mul n).add_antiperiod_eq cos_antiperiodic

中文:
定理 cos_int_mul_two_pi_add_pi
  条件: (n : 整数)
  结论: cos (n * (2 * π) + π) = -1
  证明: by
  simpa only [cos_zero] using (cos_periodic.int_mul n).add_antiperiod_eq cos_antiperiodic

Depends on / 依赖: add_antiperiod_eq, cos_antiperiodic, cos_periodic, cos_periodic.int_mul, cos_zero, int_mul
-/
theorem cos_int_mul_two_pi_add_pi (n : Int) : cos (n * (2 * π) + π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.int_mul n).add_antiperiod_eq cos_antiperiodic

/--
theorem `cos_nat_mul_two_pi_sub_pi` / 定理 `cos_nat_mul_two_pi_sub_pi`

English:
theorem cos_nat_mul_two_pi_sub_pi
  given: (n : Nat)
  statement: cos (n * (2 * π) - π) = -1
  proof: by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).sub_antiperiod_eq cos_antiperiodic

中文:
定理 cos_nat_mul_two_pi_sub_pi
  条件: (n : 自然数)
  结论: cos (n * (2 * π) - π) = -1
  证明: by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).sub_antiperiod_eq cos_antiperiodic

Depends on / 依赖: cos_antiperiodic, cos_periodic, cos_periodic.nat_mul, cos_zero, nat_mul, sub_antiperiod_eq
-/
theorem cos_nat_mul_two_pi_sub_pi (n : Nat) : cos (n * (2 * π) - π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).sub_antiperiod_eq cos_antiperiodic

/--
theorem `cos_int_mul_two_pi_sub_pi` / 定理 `cos_int_mul_two_pi_sub_pi`

English:
theorem cos_int_mul_two_pi_sub_pi
  given: (n : Int)
  statement: cos (n * (2 * π) - π) = -1
  proof: by
  simpa only [cos_zero] using (cos_periodic.int_mul n).sub_antiperiod_eq cos_antiperiodic

中文:
定理 cos_int_mul_two_pi_sub_pi
  条件: (n : 整数)
  结论: cos (n * (2 * π) - π) = -1
  证明: by
  simpa only [cos_zero] using (cos_periodic.int_mul n).sub_antiperiod_eq cos_antiperiodic

Depends on / 依赖: cos_antiperiodic, cos_periodic, cos_periodic.int_mul, cos_zero, int_mul, sub_antiperiod_eq
-/
theorem cos_int_mul_two_pi_sub_pi (n : Int) : cos (n * (2 * π) - π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.int_mul n).sub_antiperiod_eq cos_antiperiodic

/--
theorem `sin_add_pi_div_two` / 定理 `sin_add_pi_div_two`

English:
theorem sin_add_pi_div_two
  given: (x : Complex)
  statement: sin (x + π / 2) = cos x
  proof: by simp [sin_add]

中文:
定理 sin_add_pi_div_two
  条件: (x : Complex)
  结论: sin (x + π / 2) = cos x
  证明: by simp [sin_add]

Depends on / 依赖: sin_add
-/
theorem sin_add_pi_div_two (x : Complex) : sin (x + π / 2) = cos x := by simp [sin_add]

/--
theorem `sin_sub_pi_div_two` / 定理 `sin_sub_pi_div_two`

English:
theorem sin_sub_pi_div_two
  given: (x : Complex)
  statement: sin (x - π / 2) = -cos x
  proof: by simp [sub_eq_add_neg, sin_add]

中文:
定理 sin_sub_pi_div_two
  条件: (x : Complex)
  结论: sin (x - π / 2) = -cos x
  证明: by simp [sub_eq_add_neg, sin_add]

Depends on / 依赖: sin_add, sub_eq_add_neg
-/
theorem sin_sub_pi_div_two (x : Complex) : sin (x - π / 2) = -cos x := by simp [sub_eq_add_neg, sin_add]

/--
theorem `sin_pi_div_two_sub` / 定理 `sin_pi_div_two_sub`

English:
theorem sin_pi_div_two_sub
  given: (x : Complex)
  statement: sin (π / 2 - x) = cos x
  proof: by simp [sub_eq_add_neg, sin_add]

中文:
定理 sin_pi_div_two_sub
  条件: (x : Complex)
  结论: sin (π / 2 - x) = cos x
  证明: by simp [sub_eq_add_neg, sin_add]

Depends on / 依赖: sin_add, sub_eq_add_neg
-/
theorem sin_pi_div_two_sub (x : Complex) : sin (π / 2 - x) = cos x := by simp [sub_eq_add_neg, sin_add]

/--
theorem `cos_add_pi_div_two` / 定理 `cos_add_pi_div_two`

English:
theorem cos_add_pi_div_two
  given: (x : Complex)
  statement: cos (x + π / 2) = -sin x
  proof: by simp [cos_add]

中文:
定理 cos_add_pi_div_two
  条件: (x : Complex)
  结论: cos (x + π / 2) = -sin x
  证明: by simp [cos_add]

Depends on / 依赖: cos_add
-/
theorem cos_add_pi_div_two (x : Complex) : cos (x + π / 2) = -sin x := by simp [cos_add]

/--
theorem `cos_sub_pi_div_two` / 定理 `cos_sub_pi_div_two`

English:
theorem cos_sub_pi_div_two
  given: (x : Complex)
  statement: cos (x - π / 2) = sin x
  proof: by simp [sub_eq_add_neg, cos_add]

中文:
定理 cos_sub_pi_div_two
  条件: (x : Complex)
  结论: cos (x - π / 2) = sin x
  证明: by simp [sub_eq_add_neg, cos_add]

Depends on / 依赖: cos_add, sub_eq_add_neg
-/
theorem cos_sub_pi_div_two (x : Complex) : cos (x - π / 2) = sin x := by simp [sub_eq_add_neg, cos_add]

/--
theorem `cos_pi_div_two_sub` / 定理 `cos_pi_div_two_sub`

English:
theorem cos_pi_div_two_sub
  given: (x : Complex)
  statement: cos (π / 2 - x) = sin x
  proof: by
  rw [← cos_neg]; rw [neg_sub]; rw [cos_sub_pi_div_two]

中文:
定理 cos_pi_div_two_sub
  条件: (x : Complex)
  结论: cos (π / 2 - x) = sin x
  证明: by
  rw [← cos_neg]; rw [neg_sub]; rw [cos_sub_pi_div_two]

Depends on / 依赖: cos_neg, cos_sub_pi_div_two, neg_sub
-/
theorem cos_pi_div_two_sub (x : Complex) : cos (π / 2 - x) = sin x := by
  rw [← cos_neg]; rw [neg_sub]; rw [cos_sub_pi_div_two]

/--
theorem `tan_periodic` / 定理 `tan_periodic`

English:
theorem tan_periodic
  statement: Function.Periodic tan π
  proof: by
  simpa only [tan_eq_sin_div_cos] using! sin_antiperiodic.div cos_antiperiodic

中文:
定理 tan_periodic
  结论: Function.Periodic tan π
  证明: by
  simpa only [tan_eq_sin_div_cos] using! sin_antiperiodic.div cos_antiperiodic

Depends on / 依赖: cos_antiperiodic, sin_antiperiodic, sin_antiperiodic.div, tan_eq_sin_div_cos
-/
theorem tan_periodic : Function.Periodic tan π := by
  simpa only [tan_eq_sin_div_cos] using! sin_antiperiodic.div cos_antiperiodic

/--
theorem `tan_add_pi` / 定理 `tan_add_pi`

English:
theorem tan_add_pi
  given: (x : Complex)
  statement: tan (x + π) = tan x
  proof: tan_periodic x

中文:
定理 tan_add_pi
  条件: (x : Complex)
  结论: tan (x + π) = tan x
  证明: tan_periodic x

Depends on / 依赖: tan_periodic
-/
theorem tan_add_pi (x : Complex) : tan (x + π) = tan x :=
  tan_periodic x

/--
theorem `tan_sub_pi` / 定理 `tan_sub_pi`

English:
theorem tan_sub_pi
  given: (x : Complex)
  statement: tan (x - π) = tan x
  proof: tan_periodic.sub_eq x

中文:
定理 tan_sub_pi
  条件: (x : Complex)
  结论: tan (x - π) = tan x
  证明: tan_periodic.sub_eq x

Depends on / 依赖: CostructuredArrow, CostructuredArrow.Hom, sub_eq, tan_periodic, tan_periodic.sub_eq
-/
theorem tan_sub_pi (x : Complex) : tan (x - π) = tan x :=
  tan_periodic.sub_eq x

/--
theorem `tan_pi_sub` / 定理 `tan_pi_sub`

English:
theorem tan_pi_sub
  given: (x : Complex)
  statement: tan (π - x) = -tan x
  proof: tan_neg x ▸ tan_periodic.sub_eq'

中文:
定理 tan_pi_sub
  条件: (x : Complex)
  结论: tan (π - x) = -tan x
  证明: tan_neg x ▸ tan_periodic.sub_eq'

Depends on / 依赖: commaCategory, sub_eq, tan_neg, tan_periodic, tan_periodic.sub_eq
-/
theorem tan_pi_sub (x : Complex) : tan (π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.sub_eq'

/--
theorem `tan_pi_div_two_sub` / 定理 `tan_pi_div_two_sub`

English:
theorem tan_pi_div_two_sub
  given: (x : Complex)
  statement: tan (π / 2 - x) = (tan x)⁻¹
  proof: by
  rw [tan_eq_sin_div_cos]; rw [tan_eq_sin_div_cos]; rw [inv_div]; rw [sin_pi_div_two_sub]; rw [cos_pi_div_two_sub]

中文:
定理 tan_pi_div_two_sub
  条件: (x : Complex)
  结论: tan (π / 2 - x) = (tan x)⁻¹
  证明: by
  rw [tan_eq_sin_div_cos]; rw [tan_eq_sin_div_cos]; rw [inv_div]; rw [sin_pi_div_two_sub]; rw [cos_pi_div_two_sub]

Depends on / 依赖: cos_pi_div_two_sub, inv_div, sin_pi_div_two_sub, tan_eq_sin_div_cos
-/
theorem tan_pi_div_two_sub (x : Complex) : tan (π / 2 - x) = (tan x)⁻¹ := by
  rw [tan_eq_sin_div_cos]; rw [tan_eq_sin_div_cos]; rw [inv_div]; rw [sin_pi_div_two_sub]; rw [cos_pi_div_two_sub]

/--
theorem `tan_nat_mul_pi` / 定理 `tan_nat_mul_pi`

English:
theorem tan_nat_mul_pi
  given: (n : Nat)
  statement: tan (n * π) = 0
  proof: tan_zero ▸ tan_periodic.nat_mul_eq n

中文:
定理 tan_nat_mul_pi
  条件: (n : 自然数)
  结论: tan (n * π) = 0
  证明: tan_zero ▸ tan_periodic.nat_mul_eq n

Depends on / 依赖: nat_mul_eq, tan_periodic, tan_periodic.nat_mul_eq, tan_zero
-/
theorem tan_nat_mul_pi (n : Nat) : tan (n * π) = 0 :=
  tan_zero ▸ tan_periodic.nat_mul_eq n

/--
theorem `tan_int_mul_pi` / 定理 `tan_int_mul_pi`

English:
theorem tan_int_mul_pi
  given: (n : Int)
  statement: tan (n * π) = 0
  proof: tan_zero ▸ tan_periodic.int_mul_eq n

中文:
定理 tan_int_mul_pi
  条件: (n : 整数)
  结论: tan (n * π) = 0
  证明: tan_zero ▸ tan_periodic.int_mul_eq n

Depends on / 依赖: CommaMorphism, CommaMorphism.left, int_mul_eq, tan_periodic, tan_periodic.int_mul_eq, tan_zero
-/
theorem tan_int_mul_pi (n : Int) : tan (n * π) = 0 :=
  tan_zero ▸ tan_periodic.int_mul_eq n

/--
theorem `tan_add_nat_mul_pi` / 定理 `tan_add_nat_mul_pi`

English:
theorem tan_add_nat_mul_pi
  given: (x : Complex) (n : Nat)
  statement: tan (x + n * π) = tan x
  proof: tan_periodic.nat_mul n x

中文:
定理 tan_add_nat_mul_pi
  条件: (x : Complex) (n : 自然数)
  结论: tan (x + n * π) = tan x
  证明: tan_periodic.nat_mul n x

Depends on / 依赖: nat_mul, tan_periodic, tan_periodic.nat_mul
-/
theorem tan_add_nat_mul_pi (x : Complex) (n : Nat) : tan (x + n * π) = tan x :=
  tan_periodic.nat_mul n x

/--
theorem `tan_add_int_mul_pi` / 定理 `tan_add_int_mul_pi`

English:
theorem tan_add_int_mul_pi
  given: (x : Complex) (n : Int)
  statement: tan (x + n * π) = tan x
  proof: tan_periodic.int_mul n x

中文:
定理 tan_add_int_mul_pi
  条件: (x : Complex) (n : 整数)
  结论: tan (x + n * π) = tan x
  证明: tan_periodic.int_mul n x

Depends on / 依赖: CostructuredArrow, CostructuredArrow.w, int_mul, tan_periodic, tan_periodic.int_mul
-/
theorem tan_add_int_mul_pi (x : Complex) (n : Int) : tan (x + n * π) = tan x :=
  tan_periodic.int_mul n x

/--
theorem `tan_sub_nat_mul_pi` / 定理 `tan_sub_nat_mul_pi`

English:
theorem tan_sub_nat_mul_pi
  given: (x : Complex) (n : Nat)
  statement: tan (x - n * π) = tan x
  proof: tan_periodic.sub_nat_mul_eq n

中文:
定理 tan_sub_nat_mul_pi
  条件: (x : Complex) (n : 自然数)
  结论: tan (x - n * π) = tan x
  证明: tan_periodic.sub_nat_mul_eq n

Depends on / 依赖: sub_nat_mul_eq, tan_periodic, tan_periodic.sub_nat_mul_eq
-/
theorem tan_sub_nat_mul_pi (x : Complex) (n : Nat) : tan (x - n * π) = tan x :=
  tan_periodic.sub_nat_mul_eq n

/--
theorem `tan_sub_int_mul_pi` / 定理 `tan_sub_int_mul_pi`

English:
theorem tan_sub_int_mul_pi
  given: (x : Complex) (n : Int)
  statement: tan (x - n * π) = tan x
  proof: tan_periodic.sub_int_mul_eq n

中文:
定理 tan_sub_int_mul_pi
  条件: (x : Complex) (n : 整数)
  结论: tan (x - n * π) = tan x
  证明: tan_periodic.sub_int_mul_eq n

Depends on / 依赖: sub_int_mul_eq, tan_periodic, tan_periodic.sub_int_mul_eq
-/
theorem tan_sub_int_mul_pi (x : Complex) (n : Int) : tan (x - n * π) = tan x :=
  tan_periodic.sub_int_mul_eq n

/--
theorem `tan_nat_mul_pi_sub` / 定理 `tan_nat_mul_pi_sub`

English:
theorem tan_nat_mul_pi_sub
  given: (x : Complex) (n : Nat)
  statement: tan (n * π - x) = -tan x
  proof: tan_neg x ▸ tan_periodic.nat_mul_sub_eq n

中文:
定理 tan_nat_mul_pi_sub
  条件: (x : Complex) (n : 自然数)
  结论: tan (n * π - x) = -tan x
  证明: tan_neg x ▸ tan_periodic.nat_mul_sub_eq n

Depends on / 依赖: nat_mul_sub_eq, tan_neg, tan_periodic, tan_periodic.nat_mul_sub_eq
-/
theorem tan_nat_mul_pi_sub (x : Complex) (n : Nat) : tan (n * π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.nat_mul_sub_eq n

/--
theorem `tan_int_mul_pi_sub` / 定理 `tan_int_mul_pi_sub`

English:
theorem tan_int_mul_pi_sub
  given: (x : Complex) (n : Int)
  statement: tan (n * π - x) = -tan x
  proof: tan_neg x ▸ tan_periodic.int_mul_sub_eq n

中文:
定理 tan_int_mul_pi_sub
  条件: (x : Complex) (n : 整数)
  结论: tan (n * π - x) = -tan x
  证明: tan_neg x ▸ tan_periodic.int_mul_sub_eq n

Depends on / 依赖: int_mul_sub_eq, tan_neg, tan_periodic, tan_periodic.int_mul_sub_eq
-/
theorem tan_int_mul_pi_sub (x : Complex) (n : Int) : tan (n * π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.int_mul_sub_eq n

/--
theorem `exp_antiperiodic` / 定理 `exp_antiperiodic`

English:
theorem exp_antiperiodic
  statement: Function.Antiperiodic exp (π * I)
  proof: by simp [exp_add, exp_mul_I]

中文:
定理 exp_antiperiodic
  结论: Function.Antiperiodic exp (π * I)
  证明: by simp [exp_add, exp_mul_I]

Depends on / 依赖: exp_add, exp_mul_I
-/
theorem exp_antiperiodic : Function.Antiperiodic exp (π * I) := by simp [exp_add, exp_mul_I]

/--
theorem `exp_periodic` / 定理 `exp_periodic`

English:
theorem exp_periodic
  statement: Function.Periodic exp (2 * π * I)
  proof: (mul_assoc (2 : Complex) π I).symm ▸ exp_antiperiodic.periodic_two_mul

中文:
定理 exp_periodic
  结论: Function.Periodic exp (2 * π * I)
  证明: (mul_assoc (2 : Complex) π I).symm ▸ exp_antiperiodic.periodic_two_mul

Depends on / 依赖: exp_antiperiodic, exp_antiperiodic.periodic_two_mul, mul_assoc, periodic_two_mul
-/
theorem exp_periodic : Function.Periodic exp (2 * π * I) :=
  (mul_assoc (2 : Complex) π I).symm ▸ exp_antiperiodic.periodic_two_mul

/--
theorem `exp_mul_I_antiperiodic` / 定理 `exp_mul_I_antiperiodic`

English:
theorem exp_mul_I_antiperiodic
  statement: Function.Antiperiodic (fun x => exp (x * I)) π
  proof: by
  simpa only [mul_inv_cancel_right₀ I_ne_zero] using exp_antiperiodic.mul_const I_ne_zero

中文:
定理 exp_mul_I_antiperiodic
  结论: Function.Antiperiodic (fun x => exp (x * I)) π
  证明: by
  simpa only [mul_inv_cancel_right₀ I_ne_zero] using exp_antiperiodic.mul_const I_ne_zero

Depends on / 依赖: I_ne_zero, exp_antiperiodic, exp_antiperiodic.mul_const, mul_const
-/
theorem exp_mul_I_antiperiodic : Function.Antiperiodic (fun x => exp (x * I)) π := by
  simpa only [mul_inv_cancel_right₀ I_ne_zero] using exp_antiperiodic.mul_const I_ne_zero

/--
theorem `exp_mul_I_periodic` / 定理 `exp_mul_I_periodic`

English:
theorem exp_mul_I_periodic
  statement: Function.Periodic (fun x => exp (x * I)) (2 * π)
  proof: exp_mul_I_antiperiodic.periodic_two_mul

@[simp]

中文:
定理 exp_mul_I_periodic
  结论: Function.Periodic (fun x => exp (x * I)) (2 * π)
  证明: exp_mul_I_antiperiodic.periodic_two_mul

@[simp]

Depends on / 依赖: exp_mul_I_antiperiodic, exp_mul_I_antiperiodic.periodic_two_mul, periodic_two_mul
-/
theorem exp_mul_I_periodic : Function.Periodic (fun x => exp (x * I)) (2 * π) :=
  exp_mul_I_antiperiodic.periodic_two_mul

@[simp]
/--
theorem `exp_pi_mul_I` / 定理 `exp_pi_mul_I`

English:
theorem exp_pi_mul_I
  statement: exp (π * I) = -1
  proof: exp_zero ▸ exp_antiperiodic.eq

@[simp]

中文:
定理 exp_pi_mul_I
  结论: exp (π * I) = -1
  证明: exp_zero ▸ exp_antiperiodic.eq

@[simp]

Depends on / 依赖: exp_antiperiodic, exp_antiperiodic.eq, exp_zero
-/
theorem exp_pi_mul_I : exp (π * I) = -1 :=
  exp_zero ▸ exp_antiperiodic.eq

@[simp]
/--
theorem `exp_neg_pi_mul_I` / 定理 `exp_neg_pi_mul_I`

English:
theorem exp_neg_pi_mul_I
  statement: exp (-(π * I)) = -1
  proof: by
  simp [Complex.exp_neg]

@[simp]

中文:
定理 exp_neg_pi_mul_I
  结论: exp (-(π * I)) = -1
  证明: by
  simp [Complex.exp_neg]

@[simp]

Depends on / 依赖: Complex.exp_neg, exp_neg
-/
theorem exp_neg_pi_mul_I : exp (-(π * I)) = -1 := by
  simp [Complex.exp_neg]

@[simp]
/--
theorem `exp_two_pi_mul_I` / 定理 `exp_two_pi_mul_I`

English:
theorem exp_two_pi_mul_I
  statement: exp (2 * π * I) = 1
  proof: exp_periodic.eq.trans exp_zero

@[simp]

中文:
定理 exp_two_pi_mul_I
  结论: exp (2 * π * I) = 1
  证明: exp_periodic.eq.trans exp_zero

@[simp]

Depends on / 依赖: exp_periodic, exp_periodic.eq.trans, exp_zero
-/
theorem exp_two_pi_mul_I : exp (2 * π * I) = 1 :=
  exp_periodic.eq.trans exp_zero

@[simp]
/--
lemma `exp_pi_div_two_mul_I` / 引理 `exp_pi_div_two_mul_I`

English:
lemma exp_pi_div_two_mul_I
  statement: exp (π / 2 * I) = I
  proof: by
  rw [← cos_add_sin_I]; rw [cos_pi_div_two]; rw [sin_pi_div_two]; rw [one_mul]; rw [zero_add]

@[simp]

中文:
引理 exp_pi_div_two_mul_I
  结论: exp (π / 2 * I) = I
  证明: by
  rw [← cos_add_sin_I]; rw [cos_pi_div_two]; rw [sin_pi_div_two]; rw [one_mul]; rw [zero_add]

@[simp]

Depends on / 依赖: cos_add_sin_I, cos_pi_div_two, one_mul, sin_pi_div_two, zero_add
-/
lemma exp_pi_div_two_mul_I : exp (π / 2 * I) = I := by
  rw [← cos_add_sin_I]; rw [cos_pi_div_two]; rw [sin_pi_div_two]; rw [one_mul]; rw [zero_add]

@[simp]
/--
lemma `exp_neg_pi_div_two_mul_I` / 引理 `exp_neg_pi_div_two_mul_I`

English:
lemma exp_neg_pi_div_two_mul_I
  statement: exp (-π / 2 * I) = -I
  proof: by
  rw [← cos_add_sin_I]; rw [neg_div]; rw [cos_neg]; rw [cos_pi_div_two]; rw [sin_neg]; rw [sin_pi_div_two]; rw [zero_add]; rw [neg_mul]; rw [one_mul]

@[simp]

中文:
引理 exp_neg_pi_div_two_mul_I
  结论: exp (-π / 2 * I) = -I
  证明: by
  rw [← cos_add_sin_I]; rw [neg_div]; rw [cos_neg]; rw [cos_pi_div_two]; rw [sin_neg]; rw [sin_pi_div_two]; rw [zero_add]; rw [neg_mul]; rw [one_mul]

@[simp]

Depends on / 依赖: cos_add_sin_I, cos_neg, cos_pi_div_two, neg_div, neg_mul, one_mul, sin_neg, sin_pi_div_two, zero_add
-/
lemma exp_neg_pi_div_two_mul_I : exp (-π / 2 * I) = -I := by
  rw [← cos_add_sin_I]; rw [neg_div]; rw [cos_neg]; rw [cos_pi_div_two]; rw [sin_neg]; rw [sin_pi_div_two]; rw [zero_add]; rw [neg_mul]; rw [one_mul]

@[simp]
/--
theorem `exp_nat_mul_two_pi_mul_I` / 定理 `exp_nat_mul_two_pi_mul_I`

English:
theorem exp_nat_mul_two_pi_mul_I
  given: (n : Nat)
  statement: exp (n * (2 * π * I)) = 1
  proof: (exp_periodic.nat_mul_eq n).trans exp_zero

@[simp]

中文:
定理 exp_nat_mul_two_pi_mul_I
  条件: (n : 自然数)
  结论: exp (n * (2 * π * I)) = 1
  证明: (exp_periodic.nat_mul_eq n).trans exp_zero

@[simp]

Depends on / 依赖: exp_periodic, exp_periodic.nat_mul_eq, exp_zero, nat_mul_eq
-/
theorem exp_nat_mul_two_pi_mul_I (n : Nat) : exp (n * (2 * π * I)) = 1 :=
  (exp_periodic.nat_mul_eq n).trans exp_zero

@[simp]
/--
theorem `exp_int_mul_two_pi_mul_I` / 定理 `exp_int_mul_two_pi_mul_I`

English:
theorem exp_int_mul_two_pi_mul_I
  given: (n : Int)
  statement: exp (n * (2 * π * I)) = 1
  proof: (exp_periodic.int_mul_eq n).trans exp_zero

@[simp]

中文:
定理 exp_int_mul_two_pi_mul_I
  条件: (n : 整数)
  结论: exp (n * (2 * π * I)) = 1
  证明: (exp_periodic.int_mul_eq n).trans exp_zero

@[simp]

Depends on / 依赖: eqToHom_left, exp_periodic, exp_periodic.int_mul_eq, exp_zero, int_mul_eq
-/
theorem exp_int_mul_two_pi_mul_I (n : Int) : exp (n * (2 * π * I)) = 1 :=
  (exp_periodic.int_mul_eq n).trans exp_zero

@[simp]
/--
theorem `exp_add_pi_mul_I` / 定理 `exp_add_pi_mul_I`

English:
theorem exp_add_pi_mul_I
  given: (z : Complex)
  statement: exp (z + π * I) = -exp z
  proof: exp_antiperiodic z

@[simp]

中文:
定理 exp_add_pi_mul_I
  条件: (z : Complex)
  结论: exp (z + π * I) = -exp z
  证明: exp_antiperiodic z

@[simp]

Depends on / 依赖: exp_antiperiodic
-/
theorem exp_add_pi_mul_I (z : Complex) : exp (z + π * I) = -exp z :=
  exp_antiperiodic z

@[simp]
/--
theorem `exp_sub_pi_mul_I` / 定理 `exp_sub_pi_mul_I`

English:
theorem exp_sub_pi_mul_I
  given: (z : Complex)
  statement: exp (z - π * I) = -exp z
  proof: exp_antiperiodic.sub_eq z

中文:
定理 exp_sub_pi_mul_I
  条件: (z : Complex)
  结论: exp (z - π * I) = -exp z
  证明: exp_antiperiodic.sub_eq z

Depends on / 依赖: eqToHom_left, exp_antiperiodic, exp_antiperiodic.sub_eq, sub_eq
-/
theorem exp_sub_pi_mul_I (z : Complex) : exp (z - π * I) = -exp z :=
  exp_antiperiodic.sub_eq z

/--
theorem `norm_exp_mul_exp_add_exp_neg_le_of_abs_im_le` / 定理 `norm_exp_mul_exp_add_exp_neg_le_of_abs_im_le`

English:
theorem norm_exp_mul_exp_add_exp_neg_le_of_abs_im_le
  statement: {a b : Real} (ha : a <= 0) {z : Complex}
  proof: by
  simp only [norm_exp, Real.exp_le_exp, re_ofReal_mul, add_re, exp_re, neg_im, Real.cos_neg, ←
    add_mul, mul_assoc, mul_comm (Real.cos b), neg_re, ← Real.cos_abs z.im]
  have : Real.exp |z.re| <= Real.exp z.re + Real.exp (-z.re) :=
    apply_abs_le_add_of_nonneg (fun x => (Real.exp_pos x).le) 

中文:
定理 norm_exp_mul_exp_add_exp_neg_le_of_abs_im_le
  结论: {a b : 实数} (ha : a <= 0) {z : Complex}
  证明: by
  simp only [norm_exp, Real.exp_le_exp, re_ofReal_mul, add_re, exp_re, neg_im, Real.cos_neg, ←
    add_mul, mul_assoc, mul_comm (Real.cos b), neg_re, ← Real.cos_abs z.im]
  have : Real.exp |z.re| <= Real.exp z.re + Real.exp (-z.re) :=
    apply_abs_le_add_of_nonneg (fun x => (Real.exp_pos x).le) 

Depends on / 依赖: Real.cos, Real.cos_abs, Real.cos_le_cos_of_nonneg_of_le_pi, Real.cos_neg, Real.exp, Real.exp_le_exp, Real.exp_pos, Real.pi_pos.le, _comp, _root_, _root_.abs_nonneg, abs_nonneg, add_mul, add_re, apply_abs_le_add_of_nonneg, cos_abs, cos_le_cos_of_nonneg_of_le_pi, cos_neg, exp_le_exp, exp_pos
-/
theorem norm_exp_mul_exp_add_exp_neg_le_of_abs_im_le {a b : Real} (ha : a <= 0) {z : Complex}
    (hz : |z.im| <= b) (hb : b <= π / 2) :
    ‖exp (a * (exp z + exp (-z)))‖ <= Real.exp (a * Real.cos b * Real.exp |z.re|) := by
  simp only [norm_exp, Real.exp_le_exp, re_ofReal_mul, add_re, exp_re, neg_im, Real.cos_neg, ←
    add_mul, mul_assoc, mul_comm (Real.cos b), neg_re, ← Real.cos_abs z.im]
  have : Real.exp |z.re| <= Real.exp z.re + Real.exp (-z.re) :=
    apply_abs_le_add_of_nonneg (fun x => (Real.exp_pos x).le) z.re
  refine mul_le_mul_of_nonpos_left (mul_le_mul this ?_ ?_ ((Real.exp_pos _).le.trans this)) ha
  · exact
      Real.cos_le_cos_of_nonneg_of_le_pi (_root_.abs_nonneg _)
        (hb.trans <| half_le_self <| Real.pi_pos.le) hz
  · refine Real.cos_nonneg_of_mem_Icc ⟨?_, hb⟩
    exact (neg_nonpos.2 <| Real.pi_div_two_pos.le).trans ((_root_.abs_nonneg _).trans hz)

/--
theorem `sinh_antiperiodic` / 定理 `sinh_antiperiodic`

English:
theorem sinh_antiperiodic
  statement: Function.Antiperiodic sinh (π * I)
  proof: by
  simp [Complex.sinh_add, sinh_mul_I, cosh_mul_I]

@[simp]

中文:
定理 sinh_antiperiodic
  结论: Function.Antiperiodic sinh (π * I)
  证明: by
  simp [Complex.sinh_add, sinh_mul_I, cosh_mul_I]

@[simp]

Depends on / 依赖: Complex.sinh_add, cosh_mul_I, sinh_add, sinh_mul_I
-/
theorem sinh_antiperiodic : Function.Antiperiodic sinh (π * I) := by
  simp [Complex.sinh_add, sinh_mul_I, cosh_mul_I]

@[simp]
/--
theorem `sinh_add_pi_mul_I` / 定理 `sinh_add_pi_mul_I`

English:
theorem sinh_add_pi_mul_I
  given: (z : Complex)
  statement: sinh (z + π * I) = -sinh z
  proof: sinh_antiperiodic z

中文:
定理 sinh_add_pi_mul_I
  条件: (z : Complex)
  结论: sinh (z + π * I) = -sinh z
  证明: sinh_antiperiodic z

Depends on / 依赖: sinh_antiperiodic
-/
theorem sinh_add_pi_mul_I (z : Complex) : sinh (z + π * I) = -sinh z :=
  sinh_antiperiodic z

/--
theorem `sinh_periodic` / 定理 `sinh_periodic`

English:
theorem sinh_periodic
  statement: Function.Periodic sinh (2 * π * I)
  proof: by
  convert! sinh_antiperiodic.periodic_two_mul using 1
  ring

@[simp]

中文:
定理 sinh_periodic
  结论: Function.Periodic sinh (2 * π * I)
  证明: by
  convert! sinh_antiperiodic.periodic_two_mul using 1
  ring

@[simp]

Depends on / 依赖: convert, periodic_two_mul, sinh_antiperiodic, sinh_antiperiodic.periodic_two_mul
-/
theorem sinh_periodic : Function.Periodic sinh (2 * π * I) := by
  convert! sinh_antiperiodic.periodic_two_mul using 1
  ring

@[simp]
/--
theorem `sinh_sub_pi_mul_I` / 定理 `sinh_sub_pi_mul_I`

English:
theorem sinh_sub_pi_mul_I
  given: (z : Complex)
  statement: sinh (z - π * I) = -sinh z
  proof: sinh_antiperiodic.sub_eq z

中文:
定理 sinh_sub_pi_mul_I
  条件: (z : Complex)
  结论: sinh (z - π * I) = -sinh z
  证明: sinh_antiperiodic.sub_eq z

Depends on / 依赖: sinh_antiperiodic, sinh_antiperiodic.sub_eq, sub_eq
-/
theorem sinh_sub_pi_mul_I (z : Complex) : sinh (z - π * I) = -sinh z :=
  sinh_antiperiodic.sub_eq z

/--
theorem `cosh_antiperiodic` / 定理 `cosh_antiperiodic`

English:
theorem cosh_antiperiodic
  statement: Function.Antiperiodic cosh (π * I)
  proof: by
  simp [Complex.cosh_add, cosh_mul_I, sinh_mul_I]

@[simp]

中文:
定理 cosh_antiperiodic
  结论: Function.Antiperiodic cosh (π * I)
  证明: by
  simp [Complex.cosh_add, cosh_mul_I, sinh_mul_I]

@[simp]

Depends on / 依赖: Complex.cosh_add, cosh_add, cosh_mul_I, sinh_mul_I
-/
theorem cosh_antiperiodic : Function.Antiperiodic cosh (π * I) := by
  simp [Complex.cosh_add, cosh_mul_I, sinh_mul_I]

@[simp]
/--
theorem `cosh_add_pi_mul_I` / 定理 `cosh_add_pi_mul_I`

English:
theorem cosh_add_pi_mul_I
  given: (z : Complex)
  statement: cosh (z + π * I) = -cosh z
  proof: cosh_antiperiodic z

中文:
定理 cosh_add_pi_mul_I
  条件: (z : Complex)
  结论: cosh (z + π * I) = -cosh z
  证明: cosh_antiperiodic z

Depends on / 依赖: cosh_antiperiodic
-/
theorem cosh_add_pi_mul_I (z : Complex) : cosh (z + π * I) = -cosh z :=
  cosh_antiperiodic z

/--
theorem `cosh_periodic` / 定理 `cosh_periodic`

English:
theorem cosh_periodic
  statement: Function.Periodic cosh (2 * π * I)
  proof: by
  convert! cosh_antiperiodic.periodic_two_mul using 1
  ring

@[simp]

中文:
定理 cosh_periodic
  结论: Function.Periodic cosh (2 * π * I)
  证明: by
  convert! cosh_antiperiodic.periodic_two_mul using 1
  ring

@[simp]

Depends on / 依赖: convert, cosh_antiperiodic, cosh_antiperiodic.periodic_two_mul, periodic_two_mul
-/
theorem cosh_periodic : Function.Periodic cosh (2 * π * I) := by
  convert! cosh_antiperiodic.periodic_two_mul using 1
  ring

@[simp]
/--
theorem `cosh_sub_pi_mul_I` / 定理 `cosh_sub_pi_mul_I`

English:
theorem cosh_sub_pi_mul_I
  given: (z : Complex)
  statement: cosh (z - π * I) = -cosh z
  proof: cosh_antiperiodic.sub_eq z

中文:
定理 cosh_sub_pi_mul_I
  条件: (z : Complex)
  结论: cosh (z - π * I) = -cosh z
  证明: cosh_antiperiodic.sub_eq z

Depends on / 依赖: cosh_antiperiodic, cosh_antiperiodic.sub_eq, sub_eq
-/
theorem cosh_sub_pi_mul_I (z : Complex) : cosh (z - π * I) = -cosh z :=
  cosh_antiperiodic.sub_eq z

/--
theorem `tanh_periodic` / 定理 `tanh_periodic`

English:
theorem tanh_periodic
  statement: Function.Periodic tanh (π * I)
  proof: by
  simp [tanh_eq_sinh_div_cosh]

@[simp]

中文:
定理 tanh_periodic
  结论: Function.Periodic tanh (π * I)
  证明: by
  simp [tanh_eq_sinh_div_cosh]

@[simp]

Depends on / 依赖: tanh_eq_sinh_div_cosh
-/
theorem tanh_periodic : Function.Periodic tanh (π * I) := by
  simp [tanh_eq_sinh_div_cosh]

@[simp]
/--
theorem `tanh_add_pi_mul_I` / 定理 `tanh_add_pi_mul_I`

English:
theorem tanh_add_pi_mul_I
  given: (z : Complex)
  statement: tanh (z + π * I) = tanh z
  proof: tanh_periodic z

@[simp]

中文:
定理 tanh_add_pi_mul_I
  条件: (z : Complex)
  结论: tanh (z + π * I) = tanh z
  证明: tanh_periodic z

@[simp]

Depends on / 依赖: tanh_periodic
-/
theorem tanh_add_pi_mul_I (z : Complex) : tanh (z + π * I) = tanh z :=
  tanh_periodic z

@[simp]
/--
theorem `tanh_sub_pi_mul_I` / 定理 `tanh_sub_pi_mul_I`

English:
theorem tanh_sub_pi_mul_I
  given: (z : Complex)
  statement: tanh (z - π * I) = tanh z
  proof: tanh_periodic.sub_eq z

中文:
定理 tanh_sub_pi_mul_I
  条件: (z : Complex)
  结论: tanh (z - π * I) = tanh z
  证明: tanh_periodic.sub_eq z

Depends on / 依赖: sub_eq, tanh_periodic, tanh_periodic.sub_eq
-/
theorem tanh_sub_pi_mul_I (z : Complex) : tanh (z - π * I) = tanh z :=
  tanh_periodic.sub_eq z

end Complex
