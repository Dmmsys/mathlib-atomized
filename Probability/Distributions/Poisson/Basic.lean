/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Etienne Marion, Hanzhang Cheng
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Tactic.CrossRefAttribute

import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Poisson distributions over ℕ

Define the Poisson measure over the natural numbers. For `r : ℝ≥0`, `poissonMeasure r` is the
measure which to `{n}` associates `exp (-r) * r ^ n / (n)!`.

## Main definition

* `poissonMeasure r`: a Poisson measure on `ℕ`, parametrized by its rate `r : ℝ≥0`.

## Main results

* `poissonMeasure_conv_poissonMeasure`: `Poisson(r₁) ∗ Poisson(r₂) = Poisson(r₁ + r₂)`.
* `IndepFun.hasLaw_add_poissonMeasure`: the sum of two independent Poisson random variables
  is again Poisson.
-/

@[expose] public section

open MeasureTheory Real
open scoped NNReal Nat

namespace ProbabilityTheory

/-- The poisson measure with rate `r : ℝ≥0` as a measure over `ℕ`. -/
@[wikidata Q205692]
noncomputable
/--
Definition of `poissonMeasure` / `poissonMeasure` 的定义

English:
definition poissonMeasure
  signature: (r : Real>=0)
  body: Measure.sum (fun n => ENNReal.ofReal (exp (-r) * r ^ n / (n)!) • (.dirac n))

中文:
定义 poissonMeasure
  签名: (r : 实数>=0)
  定义体: Measure.sum (fun n => ENNReal.ofReal (exp (-r) * r ^ n / (n)!) • (.dirac n))

Depends on / 依赖: ENNReal, ENNReal.ofReal, Measure, Measure.sum, ofReal
-/
def poissonMeasure (r : Real>=0) : Measure Nat :=
  Measure.sum (fun n => ENNReal.ofReal (exp (-r) * r ^ n / (n)!) • (.dirac n))

/-- The Poisson probability distribution with rate `r`. -/
scoped notation3 "Po(" r ")" => poissonMeasure r

/-- The Poisson probability distribution with rate `r` valued in the `AddMonoidWithOne` `R`. -/
scoped notation3 "Po(" R ", " r ")" => (poissonMeasure r).map (Nat.cast : Nat -> R)

/--
lemma `poissonMeasure_singleton` / 引理 `poissonMeasure_singleton`

English:
lemma poissonMeasure_singleton
  given: (r : Real>=0) (n : Nat)
  proof: by
  rw [poissonMeasure]; rw [Measure.sum_smul_dirac_singleton]

中文:
引理 poissonMeasure_singleton
  条件: (r : 实数>=0) (n : 自然数)
  证明: by
  rw [poissonMeasure]; rw [Measure.sum_smul_dirac_singleton]

Depends on / 依赖: Measure, Measure.sum_smul_dirac_singleton, poissonMeasure, sum_smul_dirac_singleton
-/
lemma poissonMeasure_singleton (r : Real>=0) (n : Nat) :
    Po(r) {n} = ENNReal.ofReal (exp (-r) * r ^ n / (n)!) := by
  rw [poissonMeasure]; rw [Measure.sum_smul_dirac_singleton]

/--
lemma `poissonMeasure_real_singleton` / 引理 `poissonMeasure_real_singleton`

English:
lemma poissonMeasure_real_singleton
  given: (r : Real>=0) (n : Nat)
  proof: by
  rw [measureReal_def]; rw [poissonMeasure_singleton]; rw [ENNReal.toReal_ofReal (by positivity)]

中文:
引理 poissonMeasure_real_singleton
  条件: (r : 实数>=0) (n : 自然数)
  证明: by
  rw [measureReal_def]; rw [poissonMeasure_singleton]; rw [ENNReal.toReal_ofReal (by positivity)]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, measureReal_def, poissonMeasure_singleton, toReal_ofReal
-/
lemma poissonMeasure_real_singleton (r : Real>=0) (n : Nat) :
    Po(r).real {n} = exp (-r) * r ^ n / (n)! := by
  rw [measureReal_def]; rw [poissonMeasure_singleton]; rw [ENNReal.toReal_ofReal (by positivity)]

/--
lemma `poissonMeasure_real_singleton_pos` / 引理 `poissonMeasure_real_singleton_pos`

English:
lemma poissonMeasure_real_singleton_pos
  given: {r : Real>=0} (n : Nat) (hr : 0 < r)
  proof: by
  rw [poissonMeasure_real_singleton]
  positivity

中文:
引理 poissonMeasure_real_singleton_pos
  条件: {r : 实数>=0} (n : 自然数) (hr : 0 < r)
  证明: by
  rw [poissonMeasure_real_singleton]
  positivity

Depends on / 依赖: poissonMeasure_real_singleton
-/
lemma poissonMeasure_real_singleton_pos {r : Real>=0} (n : Nat) (hr : 0 < r) :
    0 < Po(r).real {n} := by
  rw [poissonMeasure_real_singleton]
  positivity

/--
lemma `hasSum_one_poissonMeasure` / 引理 `hasSum_one_poissonMeasure`

English:
lemma hasSum_one_poissonMeasure
  given: (r : Real>=0)
  statement: HasSum (fun n => exp (-r) * r ^ n / (n)!) 1
  proof: by
  convert! (NormedSpace.expSeries_div_hasSum_exp (r : Real)).mul_left (exp (-r)) using 1
  · simp_rw [mul_div_assoc]
  · simp [← exp_eq_exp_Real, ← exp_add]

中文:
引理 hasSum_one_poissonMeasure
  条件: (r : 实数>=0)
  结论: HasSum (fun n => exp (-r) * r ^ n / (n)!) 1
  证明: by
  convert! (NormedSpace.expSeries_div_hasSum_exp (r : Real)).mul_left (exp (-r)) using 1
  · simp_rw [mul_div_assoc]
  · simp [← exp_eq_exp_Real, ← exp_add]

Depends on / 依赖: NormedSpace, NormedSpace.expSeries_div_hasSum_exp, convert, expSeries_div_hasSum_exp, exp_add, exp_eq_exp_Real, mul_div_assoc, mul_left, simp_rw
-/
lemma hasSum_one_poissonMeasure (r : Real>=0) : HasSum (fun n => exp (-r) * r ^ n / (n)!) 1 := by
  convert! (NormedSpace.expSeries_div_hasSum_exp (r : Real)).mul_left (exp (-r)) using 1
  · simp_rw [mul_div_assoc]
  · simp [← exp_eq_exp_Real, ← exp_add]

instance (r : Real>=0) : IsProbabilityMeasure Po(r) :=
  (hasSum_one_poissonMeasure r).isProbabilityMeasure_sum_dirac (fun _ => by positivity)

instance (r : Real>=0) {R : Type*} [NatCast R] [MeasurableSpace R] :
    IsProbabilityMeasure Po(R, r) :=
  Measure.isProbabilityMeasure_map .of_discrete

section Integral

variable {E : Type*} [NormedAddCommGroup E]
variable {R : Type*} [NatCast R] [MeasurableSpace R]

/--
lemma `integrable_poissonMeasure_iff` / 引理 `integrable_poissonMeasure_iff`

English:
lemma integrable_poissonMeasure_iff
  given: {r : Real>=0} {f : Nat -> E}
  proof: by
  rw [poissonMeasure]; rw [integrable_sum_dirac_iff (by simp)]
  congrm Summable (fun n => ?_ * _)
  rw [ENNReal.toReal_ofReal (by positivity)]

中文:
引理 integrable_poissonMeasure_iff
  条件: {r : 实数>=0} {f : 自然数 -> E}
  证明: by
  rw [poissonMeasure]; rw [integrable_sum_dirac_iff (by simp)]
  congrm Summable (fun n => ?_ * _)
  rw [ENNReal.toReal_ofReal (by positivity)]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, Summable, congrm, integrable_sum_dirac_iff, poissonMeasure, toReal_ofReal
-/
lemma integrable_poissonMeasure_iff {r : Real>=0} {f : Nat -> E} :
    Integrable f Po(r) ↔ Summable (fun n => exp (-r) * r ^ n / (n)! * ‖f n‖) := by
  rw [poissonMeasure]; rw [integrable_sum_dirac_iff (by simp)]
  congrm Summable (fun n => ?_ * _)
  rw [ENNReal.toReal_ofReal (by positivity)]

/--
lemma `integrable_map_cast_poissonMeasure_iff` / 引理 `integrable_map_cast_poissonMeasure_iff`

English:
lemma integrable_map_cast_poissonMeasure_iff
  statement: {r : Real>=0} [Countable R] [MeasurableSingletonClass R]
  proof: integrable_map_measure .of_discrete .of_discrete

中文:
引理 integrable_map_cast_poissonMeasure_iff
  结论: {r : 实数>=0} [可数 R] [MeasurableSingleton类 R]
  证明: integrable_map_measure .of_discrete .of_discrete

Depends on / 依赖: integrable_map_measure, of_discrete
-/
lemma integrable_map_cast_poissonMeasure_iff {r : Real>=0} [Countable R] [MeasurableSingletonClass R]
  {f : R -> E} : Integrable f Po(R, r) ↔ Integrable (f ∘ Nat.cast) Po(r) :=
  integrable_map_measure .of_discrete .of_discrete

variable [NormedSpace Real E]

/--
lemma `hasSum_integral_poissonMeasure` / 引理 `hasSum_integral_poissonMeasure`

English:
lemma hasSum_integral_poissonMeasure
  statement: [CompleteSpace E] {r : Real>=0} {f : Nat -> E}
  proof: by
  have : (fun n => (exp (-r) * r ^ n / (n)!) • f n) =
      fun n => (ENNReal.ofReal (exp (-r) * r ^ n / (n)!)).toReal • f n := by
    ext; rw [ENNReal.toReal_ofReal (by positivity)]
  rw [this]
  apply hasSum_integral_sum_dirac (by simp)
  convert! integrable_poissonMeasure_iff.1 hf
  rw [ENNRea

中文:
引理 hasSum_integral_poissonMeasure
  结论: [完备空间 E] {r : 实数>=0} {f : 自然数 -> E}
  证明: by
  have : (fun n => (exp (-r) * r ^ n / (n)!) • f n) =
      fun n => (ENNReal.ofReal (exp (-r) * r ^ n / (n)!)).toReal • f n := by
    ext; rw [ENNReal.toReal_ofReal (by positivity)]
  rw [this]
  apply hasSum_integral_sum_dirac (by simp)
  convert! integrable_poissonMeasure_iff.1 hf
  rw [ENNRea

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.toReal_ofReal, convert, hasSum_integral_sum_dirac, integrable_poissonMeasure_iff, ofReal, toReal, toReal_ofReal
-/
lemma hasSum_integral_poissonMeasure [CompleteSpace E] {r : Real>=0} {f : Nat -> E}
    (hf : Integrable f Po(r)) :
    HasSum (fun n => (exp (-r) * r ^ n / (n)!) • f n) (∫ n, f n ∂Po(r)) := by
  have : (fun n => (exp (-r) * r ^ n / (n)!) • f n) =
      fun n => (ENNReal.ofReal (exp (-r) * r ^ n / (n)!)).toReal • f n := by
    ext; rw [ENNReal.toReal_ofReal (by positivity)]
  rw [this]
  apply hasSum_integral_sum_dirac (by simp)
  convert! integrable_poissonMeasure_iff.1 hf
  rw [ENNReal.toReal_ofReal (by positivity)]

/--
lemma `integral_poissonMeasure'` / 引理 `integral_poissonMeasure'`

English:
lemma integral_poissonMeasure'
  statement: [CompleteSpace E] {r : Real>=0} {f : Nat -> E}
  proof: (hasSum_integral_poissonMeasure hf).tsum_eq.symm

中文:
引理 integral_poissonMeasure'
  结论: [完备空间 E] {r : 实数>=0} {f : 自然数 -> E}
  证明: (hasSum_integral_poissonMeasure hf).tsum_eq.symm

Depends on / 依赖: hasSum_integral_poissonMeasure, tsum_eq, tsum_eq.symm
-/
lemma integral_poissonMeasure' [CompleteSpace E] {r : Real>=0} {f : Nat -> E}
    (hf : Integrable f Po(r)) :
    ∫ n, f n ∂Po(r) = ∑' n, (exp (-r) * r ^ n / (n)!) • f n :=
  (hasSum_integral_poissonMeasure hf).tsum_eq.symm

/--
lemma `integral_map_cast_poissonMeasure'` / 引理 `integral_map_cast_poissonMeasure'`

English:
lemma integral_map_cast_poissonMeasure'
  statement: [CompleteSpace E] [Countable R] [MeasurableSingletonClass R]
  proof: by
  rw [integral_map .of_discrete .of_discrete]
  rw [integrable_map_cast_poissonMeasure_iff] at hf
  exact integral_poissonMeasure' hf

中文:
引理 integral_map_cast_poissonMeasure'
  结论: [完备空间 E] [可数 R] [MeasurableSingleton类 R]
  证明: by
  rw [integral_map .of_discrete .of_discrete]
  rw [integrable_map_cast_poissonMeasure_iff] at hf
  exact integral_poissonMeasure' hf

Depends on / 依赖: integrable_map_cast_poissonMeasure_iff, integral_map, integral_poissonMeasure, of_discrete
-/
lemma integral_map_cast_poissonMeasure' [CompleteSpace E] [Countable R] [MeasurableSingletonClass R]
    {r : Real>=0} {f : R -> E} (hf : Integrable f Po(R, r)) :
    ∫ x, f x ∂Po(R, r) = ∑' n, (exp (-r) * r ^ n / (n)!) • f n := by
  rw [integral_map .of_discrete .of_discrete]
  rw [integrable_map_cast_poissonMeasure_iff] at hf
  exact integral_poissonMeasure' hf

/--
lemma `integral_poissonMeasure` / 引理 `integral_poissonMeasure`

English:
lemma integral_poissonMeasure
  given: [FiniteDimensional Real E] (r : Real>=0) (f : Nat -> E)
  proof: by
  rw [poissonMeasure]; rw [integral_sum_dirac (by simp)]
  congr with n
  rw [ENNReal.toReal_ofReal (by positivity)]

中文:
引理 integral_poissonMeasure
  条件: [有限维 实数 E] (r : 实数>=0) (f : 自然数 -> E)
  证明: by
  rw [poissonMeasure]; rw [integral_sum_dirac (by simp)]
  congr with n
  rw [ENNReal.toReal_ofReal (by positivity)]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, integral_sum_dirac, poissonMeasure, toReal_ofReal
-/
lemma integral_poissonMeasure [FiniteDimensional Real E] (r : Real>=0) (f : Nat -> E) :
    ∫ n, f n ∂Po(r) = ∑' n, (exp (-r) * r ^ n / (n)!) • f n := by
  rw [poissonMeasure]; rw [integral_sum_dirac (by simp)]
  congr with n
  rw [ENNReal.toReal_ofReal (by positivity)]

/--
lemma `integral_map_cast_poissonMeasure` / 引理 `integral_map_cast_poissonMeasure`

English:
lemma integral_map_cast_poissonMeasure
  statement: [FiniteDimensional Real E] (r : Real>=0) [Countable R]
  proof: by
  rw [integral_map .of_discrete .of_discrete]; rw [integral_poissonMeasure]

中文:
引理 integral_map_cast_poissonMeasure
  结论: [有限维 实数 E] (r : 实数>=0) [可数 R]
  证明: by
  rw [integral_map .of_discrete .of_discrete]; rw [integral_poissonMeasure]

Depends on / 依赖: integral_map, integral_poissonMeasure, of_discrete
-/
lemma integral_map_cast_poissonMeasure [FiniteDimensional Real E] (r : Real>=0) [Countable R]
  [MeasurableSingletonClass R] (f : R -> E) :
    ∫ x, f x ∂Po(R, r) = ∑' n, (exp (-r) * r ^ n / (n)!) • f n := by
  rw [integral_map .of_discrete .of_discrete]; rw [integral_poissonMeasure]

end Integral

section CharFun

open Complex

/--
lemma `charFun_map_cast_poissonMeasure` / 引理 `charFun_map_cast_poissonMeasure`

English:
lemma charFun_map_cast_poissonMeasure
  given: (r : Real>=0) (t : Real)
  proof: by
  rw [charFun_apply]; rw [integral_map .of_discrete (by fun_prop)]; rw [integral_poissonMeasure r]
  simp_rw [Real.inner_apply]
  calc ∑' a, (rexp (-r) * r ^ a / a ! : Real) * cexp ((a * t : Real) * I)
  _ = ∑' a, (rexp (-r)) * ((r * cexp (t * I)) ^ a / a !) := by
      congr with a
      push_ca

中文:
引理 charFun_map_cast_poissonMeasure
  条件: (r : 实数>=0) (t : 实数)
  证明: by
  rw [charFun_apply]; rw [integral_map .of_discrete (by fun_prop)]; rw [integral_poissonMeasure r]
  simp_rw [Real.inner_apply]
  calc ∑' a, (rexp (-r) * r ^ a / a ! : Real) * cexp ((a * t : Real) * I)
  _ = ∑' a, (rexp (-r)) * ((r * cexp (t * I)) ^ a / a !) := by
      congr with a
      push_ca

Depends on / 依赖: Complex.exp_nat_mul, NormedSpace, NormedSpace.expSeries_div_hasSum_exp, Real.inner_apply, charFun_apply, expSeries_div_hasSum_exp, exp_nat_mul, fun_prop, inner_apply, integral_map, integral_poissonMeasure, mul_pow, of_discrete, ring_nf, simp_rw, tsum_mul_left
-/
lemma charFun_map_cast_poissonMeasure (r : Real>=0) (t : Real) :
    charFun Po(Real, r) t = cexp (r * (cexp (t * I) - 1)) := by
  rw [charFun_apply]; rw [integral_map .of_discrete (by fun_prop)]; rw [integral_poissonMeasure r]
  simp_rw [Real.inner_apply]
  calc ∑' a, (rexp (-r) * r ^ a / a ! : Real) * cexp ((a * t : Real) * I)
  _ = ∑' a, (rexp (-r)) * ((r * cexp (t * I)) ^ a / a !) := by
      congr with a
      push_cast
      rw [mul_pow]; rw [← Complex.exp_nat_mul]
      ring_nf
  _ = (rexp (-r)) * ∑' a, ((r * cexp (t * I)) ^ a / a !) := tsum_mul_left
  _ = (rexp (-r)) * cexp (r * cexp (t * I)) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp (r * cexp (t * I))).tsum_eq]; rw [exp_eq_exp_Complex]
  _ = cexp (r * (cexp (t * I) - 1)) := by
      rw [ofReal_exp]; rw [← Complex.exp_add]
      push_cast
      ring_nf

end CharFun

/-! ### Convolution of Poisson measures -/

section Convolution

variable {R : Type*} [AddMonoidWithOne R] {mR : MeasurableSpace R}

/--
theorem `map_cast_poissonMeasure_conv_real` / 定理 `map_cast_poissonMeasure_conv_real`

English:
theorem map_cast_poissonMeasure_conv_real
  given: (r₁ r₂ : Real>=0)
  proof: by
  apply Measure.ext_of_charFun
  ext t
  simp only [charFun_conv, charFun_map_cast_poissonMeasure, ← Complex.exp_add]
  congr; push_cast; ring

中文:
定理 map_cast_poissonMeasure_conv_real
  条件: (r₁ r₂ : 实数>=0)
  证明: by
  apply Measure.ext_of_charFun
  ext t
  simp only [charFun_conv, charFun_map_cast_poissonMeasure, ← Complex.exp_add]
  congr; push_cast; ring
-/
private theorem map_cast_poissonMeasure_conv_real (r₁ r₂ : Real>=0) :
    Po(Real, r₁) ∗ Po(Real, r₂) = Po(Real, r₁ + r₂) := by
  apply Measure.ext_of_charFun
  ext t
  simp only [charFun_conv, charFun_map_cast_poissonMeasure, ← Complex.exp_add]
  congr; push_cast; ring

/--
theorem `poissonMeasure_conv_poissonMeasure` / 定理 `poissonMeasure_conv_poissonMeasure`

English:
theorem poissonMeasure_conv_poissonMeasure
  given: (r₁ r₂ : Real>=0)
  proof: by
  apply (MeasurableEmbedding.natCast (α := Real)).map_injective
  rw [← Nat.coe_castAddMonoidHom]; rw [Measure.map_conv_addMonoidHom _ (by fun_prop)]
  exact map_cast_poissonMeasure_conv_real _ _

中文:
定理 poissonMeasure_conv_poissonMeasure
  条件: (r₁ r₂ : 实数>=0)
  证明: by
  apply (MeasurableEmbedding.natCast (α := Real)).map_injective
  rw [← Nat.coe_castAddMonoidHom]; rw [Measure.map_conv_addMonoidHom _ (by fun_prop)]
  exact map_cast_poissonMeasure_conv_real _ _

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.natCast, Measure, Measure.map_conv_addMonoidHom, Nat.coe_castAddMonoidHom, coe_castAddMonoidHom, fun_prop, map_cast_poissonMeasure_conv_real, map_conv_addMonoidHom, map_injective, natCast
-/
theorem poissonMeasure_conv_poissonMeasure (r₁ r₂ : Real>=0) :
    Po(r₁) ∗ Po(r₂) = Po(r₁ + r₂) := by
  apply (MeasurableEmbedding.natCast (α := Real)).map_injective
  rw [← Nat.coe_castAddMonoidHom]; rw [Measure.map_conv_addMonoidHom _ (by fun_prop)]
  exact map_cast_poissonMeasure_conv_real _ _

/--
theorem `map_cast_poissonMeasure_conv` / 定理 `map_cast_poissonMeasure_conv`

English:
theorem map_cast_poissonMeasure_conv
  given: [MeasurableAdd₂ R] (r₁ r₂ : Real>=0)
  proof: by
  rw [← Nat.coe_castAddMonoidHom]; rw [← Measure.map_conv_addMonoidHom _ (by fun_prop)]; rw [poissonMeasure_conv_poissonMeasure]

中文:
定理 map_cast_poissonMeasure_conv
  条件: [MeasurableAdd₂ R] (r₁ r₂ : 实数>=0)
  证明: by
  rw [← Nat.coe_castAddMonoidHom]; rw [← Measure.map_conv_addMonoidHom _ (by fun_prop)]; rw [poissonMeasure_conv_poissonMeasure]

Depends on / 依赖: Measure, Measure.map_conv_addMonoidHom, Nat.coe_castAddMonoidHom, coe_castAddMonoidHom, fun_prop, map_conv_addMonoidHom, poissonMeasure_conv_poissonMeasure
-/
theorem map_cast_poissonMeasure_conv [MeasurableAdd₂ R] (r₁ r₂ : Real>=0) :
    Po(R, r₁) ∗ Po(R, r₂) = Po(R, r₁ + r₂) := by
  rw [← Nat.coe_castAddMonoidHom]; rw [← Measure.map_conv_addMonoidHom _ (by fun_prop)]; rw [poissonMeasure_conv_poissonMeasure]

/--
theorem `IndepFun.hasLaw_add_poissonMeasure` / 定理 `IndepFun.hasLaw_add_poissonMeasure`

English:
theorem IndepFun.hasLaw_add_poissonMeasure
  statement: {Ω : Type*} {mΩ : MeasurableSpace Ω}
  proof: by
  rw [← poissonMeasure_conv_poissonMeasure]
  exact hXY.hasLaw_add hX hY

中文:
定理 IndepFun.hasLaw_add_poissonMeasure
  结论: {Ω : 类型} {mΩ : 可测空间 Ω}
  证明: by
  rw [← poissonMeasure_conv_poissonMeasure]
  exact hXY.hasLaw_add hX hY

Depends on / 依赖: hXY.hasLaw_add, hasLaw_add, poissonMeasure_conv_poissonMeasure
-/
theorem IndepFun.hasLaw_add_poissonMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {r₁ r₂ : Real>=0} {X Y : Ω -> Nat}
    (hXY : IndepFun X Y P) (hX : HasLaw X Po(r₁) P) (hY : HasLaw Y Po(r₂) P) :
    HasLaw (X + Y) Po(r₁ + r₂) P := by
  rw [← poissonMeasure_conv_poissonMeasure]
  exact hXY.hasLaw_add hX hY

/--
theorem `IndepFun.hasLaw_add_map_cast_poissonMeasure` / 定理 `IndepFun.hasLaw_add_map_cast_poissonMeasure`

English:
theorem IndepFun.hasLaw_add_map_cast_poissonMeasure
  statement: {Ω : Type*} {mΩ : MeasurableSpace Ω}
  proof: by
  rw [← map_cast_poissonMeasure_conv]
  exact hXY.hasLaw_add hX hY

中文:
定理 IndepFun.hasLaw_add_map_cast_poissonMeasure
  结论: {Ω : 类型} {mΩ : 可测空间 Ω}
  证明: by
  rw [← map_cast_poissonMeasure_conv]
  exact hXY.hasLaw_add hX hY

Depends on / 依赖: hXY.hasLaw_add, hasLaw_add, map_cast_poissonMeasure_conv
-/
theorem IndepFun.hasLaw_add_map_cast_poissonMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [MeasurableAdd₂ R] {r₁ r₂ : Real>=0} {X Y : Ω -> R}
    (hXY : IndepFun X Y P) (hX : HasLaw X Po(R, r₁) P) (hY : HasLaw Y Po(R, r₂) P) :
    HasLaw (X + Y) Po(R, r₁ + r₂) P := by
  rw [← map_cast_poissonMeasure_conv]
  exact hXY.hasLaw_add hX hY

end Convolution

section PoissonPMF

/-- The pmf of the Poisson distribution depending on its rate, as a function to ℝ -/
@[deprecated poissonMeasure (since := "2026-03-08")]
noncomputable
/--
Definition of `poissonPMFReal` / `poissonPMFReal` 的定义

English:
definition poissonPMFReal
  signature: (r : Real>=0) (n : Nat)
  body: exp (-r) * r ^ n / (n)!

@[deprecated (since := "2026-03-08")]
alias poissonPMFRealSum := hasSum_one_poissonMeasure

@[deprecated poissonMeasure_real_singleton_pos (since := "2026-03-08")]

中文:
定义 poissonPMF实数
  签名: (r : 实数>=0) (n : 自然数)
  定义体: exp (-r) * r ^ n / (n)!

@[deprecated (since := "2026-03-08")]
alias poissonPMFRealSum := hasSum_one_poissonMeasure

@[deprecated poissonMeasure_real_singleton_pos (since := "2026-03-08")]
-/
def poissonPMFReal (r : Real>=0) (n : Nat) : Real := exp (-r) * r ^ n / (n)!

@[deprecated (since := "2026-03-08")]
alias poissonPMFRealSum := hasSum_one_poissonMeasure

@[deprecated poissonMeasure_real_singleton_pos (since := "2026-03-08")]
/--
lemma `poissonPMFReal_pos` / 引理 `poissonPMFReal_pos`

English:
lemma poissonPMFReal_pos
  given: {r : Real>=0} {n : Nat} (hr : 0 < r)
  statement: 0 < poissonPMFReal r n
  proof: by
  rw [poissonPMFReal]
  positivity

@[deprecated measureReal_nonneg (since := "2026-03-08")]

中文:
引理 poissonPMF实数_pos
  条件: {r : 实数>=0} {n : 自然数} (hr : 0 < r)
  结论: 0 < poissonPMF实数 r n
  证明: by
  rw [poissonPMFReal]
  positivity

@[deprecated measureReal_nonneg (since := "2026-03-08")]

Depends on / 依赖: poissonPMFReal
-/
lemma poissonPMFReal_pos {r : Real>=0} {n : Nat} (hr : 0 < r) : 0 < poissonPMFReal r n := by
  rw [poissonPMFReal]
  positivity

@[deprecated measureReal_nonneg (since := "2026-03-08")]
/--
lemma `poissonPMFReal_nonneg` / 引理 `poissonPMFReal_nonneg`

English:
lemma poissonPMFReal_nonneg
  given: {r : Real>=0} {n : Nat}
  statement: 0 <= poissonPMFReal r n
  proof: by
  unfold poissonPMFReal
  positivity

中文:
引理 poissonPMF实数_nonneg
  条件: {r : 实数>=0} {n : 自然数}
  结论: 0 <= poissonPMF实数 r n
  证明: by
  unfold poissonPMFReal
  positivity

Depends on / 依赖: poissonPMFReal
-/
lemma poissonPMFReal_nonneg {r : Real>=0} {n : Nat} : 0 <= poissonPMFReal r n := by
  unfold poissonPMFReal
  positivity

/-- The pmf of the Poisson distribution depending on its rate, as a PMF. -/
@[deprecated poissonMeasure (since := "2026-03-08")]
noncomputable
/--
Definition of `poissonPMF` / `poissonPMF` 的定义

English:
definition poissonPMF
  signature: (r : Real>=0)
  body: by
  refine ⟨fun n => ENNReal.ofReal (poissonPMFReal r n), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← toNNReal_one]
  exact (poissonPMFRealSum r).toNNReal (fun n => poissonPMFReal_nonneg)

@[deprecated poissonMeasure (since := "2026-03-08")]

中文:
定义 poissonPMF
  签名: (r : 实数>=0)
  定义体: by
  refine ⟨fun n => ENNReal.ofReal (poissonPMFReal r n), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← toNNReal_one]
  exact (poissonPMFRealSum r).toNNReal (fun n => poissonPMFReal_nonneg)

@[deprecated poissonMeasure (since := "2026-03-08")]

Depends on / 依赖: ENNReal, ENNReal.hasSum_coe.mpr, ENNReal.ofReal, hasSum_coe, ofReal, poissonPMFReal, poissonPMFRealSum, poissonPMFReal_nonneg, toNNReal, toNNReal_one
-/
def poissonPMF (r : Real>=0) : PMF Nat := by
  refine ⟨fun n => ENNReal.ofReal (poissonPMFReal r n), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← toNNReal_one]
  exact (poissonPMFRealSum r).toNNReal (fun n => poissonPMFReal_nonneg)

@[deprecated poissonMeasure (since := "2026-03-08")]
/--
lemma `poissonPMFReal_ofReal_eq_poissonPMF` / 引理 `poissonPMFReal_ofReal_eq_poissonPMF`

English:
lemma poissonPMFReal_ofReal_eq_poissonPMF
  given: (r : Real>=0) (n : Nat)
  proof: by
  simpa only [poissonPMF] using by rfl

@[deprecated Measurable.of_discrete (since := "2026-03-08")]

中文:
引理 poissonPMF实数_of实数_eq_poissonPMF
  条件: (r : 实数>=0) (n : 自然数)
  证明: by
  simpa only [poissonPMF] using by rfl

@[deprecated Measurable.of_discrete (since := "2026-03-08")]

Depends on / 依赖: poissonPMF
-/
lemma poissonPMFReal_ofReal_eq_poissonPMF (r : Real>=0) (n : Nat) :
    ENNReal.ofReal (poissonPMFReal r n) = poissonPMF r n := by
  simpa only [poissonPMF] using by rfl

@[deprecated Measurable.of_discrete (since := "2026-03-08")]
/--
lemma `measurable_poissonPMFReal` / 引理 `measurable_poissonPMFReal`

English:
lemma measurable_poissonPMFReal
  given: (r : Real>=0)
  statement: Measurable (poissonPMFReal r)
  proof: by fun_prop

@[deprecated StronglyMeasurable.of_discrete (since := "2026-03-08")]

中文:
引理 measurable_poissonPMF实数
  条件: (r : 实数>=0)
  结论: 可测 (poissonPMF实数 r)
  证明: by fun_prop

@[deprecated StronglyMeasurable.of_discrete (since := "2026-03-08")]

Depends on / 依赖: fun_prop
-/
lemma measurable_poissonPMFReal (r : Real>=0) : Measurable (poissonPMFReal r) := by fun_prop

@[deprecated StronglyMeasurable.of_discrete (since := "2026-03-08")]
/--
lemma `stronglyMeasurable_poissonPMFReal` / 引理 `stronglyMeasurable_poissonPMFReal`

English:
lemma stronglyMeasurable_poissonPMFReal
  given: (r : Real>=0)
  statement: StronglyMeasurable (poissonPMFReal r)
  proof: stronglyMeasurable_iff_measurable.mpr (measurable_poissonPMFReal r)

中文:
引理 stronglyMeasurable_poissonPMF实数
  条件: (r : 实数>=0)
  结论: StronglyMeasurable (poissonPMF实数 r)
  证明: stronglyMeasurable_iff_measurable.mpr (measurable_poissonPMFReal r)

Depends on / 依赖: measurable_poissonPMFReal, stronglyMeasurable_iff_measurable, stronglyMeasurable_iff_measurable.mpr
-/
lemma stronglyMeasurable_poissonPMFReal (r : Real>=0) : StronglyMeasurable (poissonPMFReal r) :=
  stronglyMeasurable_iff_measurable.mpr (measurable_poissonPMFReal r)

end PoissonPMF

end ProbabilityTheory
