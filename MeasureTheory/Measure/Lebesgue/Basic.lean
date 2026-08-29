/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Lebesgue measure on the real line and on `ℝⁿ`

We show that the Lebesgue measure on the real line (constructed as a particular case of additive
Haar measure on inner product spaces) coincides with the Stieltjes measure associated
to the function `x ↦ x`. We deduce properties of this measure on `ℝ`, and then of the product
Lebesgue measure on `ℝⁿ`. In particular, we prove that they are translation invariant.

We show that, on `ℝⁿ`, a linear map acts on Lebesgue measure by rescaling it through the absolute
value of its determinant, in `Real.map_linearMap_volume_pi_eq_smul_volume_pi`.

More properties of the Lebesgue measure are deduced from this in
`Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`, where they are proved more generally for any
additive Haar measure on a finite-dimensional real vector space.
-/

@[expose] public section


assert_not_exists MeasureTheory.integral

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace Metric

open ENNReal (ofReal)

open scoped ENNReal NNReal Topology

/-!
### Definition of the Lebesgue measure and lengths of intervals
-/


namespace Real

variable {ι : Type*} [Fintype ι]

/--
theorem `volume_eq_stieltjes_id` / 定理 `volume_eq_stieltjes_id`

English:
theorem volume_eq_stieltjes_id
  statement: (volume : Measure Real) = StieltjesFunction.id.measure
  proof: by
  have : IsAddLeftInvariant StieltjesFunction.id.measure :=
    ⟨fun a =>
Eq.symm
        Real.measure_ext_Ioo_rat fun p q => by
          simp only [Measure.map_apply (measurable_const_add a) measurableSet_Ioo,
            sub_sub_sub_cancel_right, StieltjesFunction.measure_Ioo, StieltjesFunction.id_leftLim,
            StieltjesFunction.id_apply, id, preimage_const_add_Ioo]⟩
  have A : StieltjesFunction.id.measure (stdOrthonormalBasis Real Real).toBasis.parallelepiped = 1 := by
    change StieltjesFunction.id.measure (parallelepiped (stdOrthonormalBasis Real Real)) = 1
    rcases parallelepiped_orthonormalBasis_one_dim (stdOrthonormalBasis Real Real) with (H | H) <;>
      simp only [H, StieltjesFunction.measure_Icc, StieltjesFunction.id_apply, id, tsub_zero,
        StieltjesFunction.id_leftLim, sub_neg_eq_add, zero_add, ENNReal.ofReal_one]
  conv_rhs =>
    rw [addHaarMeasure_unique StieltjesFunction.id.measure
        (stdOrthonormalBasis Real Real).toBasis.parallelepiped]; rw [A]
  simp only [volume, Module.Basis.addHaar, one_smul]

中文:
定理 volume_eq_stieltjes_id
  结论: (volume : 测度 实数) = Stieltjes函数.id.measure
  证明: by
  have : IsAddLeftInvariant StieltjesFunction.id.measure :=
    ⟨fun a =>
Eq.symm
        Real.measure_ext_Ioo_rat fun p q => by
          simp only [Measure.map_apply (measurable_const_add a) measurableSet_Ioo,
            sub_sub_sub_cancel_right, StieltjesFunction.measure_Ioo, StieltjesFunction.id_leftLim,
            StieltjesFunction.id_apply, id, preimage_const_add_Ioo]⟩
  have A : StieltjesFunction.id.measure (stdOrthonormalBasis Real Real).toBasis.parallelepiped = 1 := by
    change StieltjesFunction.id.measure (parallelepiped (stdOrthonormalBasis Real Real)) = 1
    rcases parallelepiped_orthonormalBasis_one_dim (stdOrthonormalBasis Real Real) with (H | H) <;>
      simp only [H, StieltjesFunction.measure_Icc, StieltjesFunction.id_apply, id, tsub_zero,
        StieltjesFunction.id_leftLim, sub_neg_eq_add, zero_add, ENNReal.ofReal_one]
  conv_rhs =>
    rw [addHaarMeasure_unique StieltjesFunction.id.measure
        (stdOrthonormalBasis Real Real).toBasis.parallelepiped]; rw [A]
  simp only [volume, Module.Basis.addHaar, one_smul]

Depends on / 依赖: Eq.symm, IsAddLeftInvariant, Measure, Measure.map_apply, Real.measure_ext_Ioo_rat, StieltjesFunction, StieltjesFunction.id.measure, StieltjesFunction.id_apply, StieltjesFunction.id_leftLim, StieltjesFunction.measure_Ioo, id_apply, id_leftLim, map_apply, measurableSet_Ioo, measurable_const_add, measure, measure_Ioo, measure_ext_Ioo_rat, parallelepiped, preimage_const_add_Ioo
-/
theorem volume_eq_stieltjes_id : (volume : Measure Real) = StieltjesFunction.id.measure := by
  have : IsAddLeftInvariant StieltjesFunction.id.measure :=
    ⟨fun a =>
Eq.symm
        Real.measure_ext_Ioo_rat fun p q => by
          simp only [Measure.map_apply (measurable_const_add a) measurableSet_Ioo,
            sub_sub_sub_cancel_right, StieltjesFunction.measure_Ioo, StieltjesFunction.id_leftLim,
            StieltjesFunction.id_apply, id, preimage_const_add_Ioo]⟩
  have A : StieltjesFunction.id.measure (stdOrthonormalBasis Real Real).toBasis.parallelepiped = 1 := by
    change StieltjesFunction.id.measure (parallelepiped (stdOrthonormalBasis Real Real)) = 1
    rcases parallelepiped_orthonormalBasis_one_dim (stdOrthonormalBasis Real Real) with (H | H) <;>
      simp only [H, StieltjesFunction.measure_Icc, StieltjesFunction.id_apply, id, tsub_zero,
        StieltjesFunction.id_leftLim, sub_neg_eq_add, zero_add, ENNReal.ofReal_one]
  conv_rhs =>
    rw [addHaarMeasure_unique StieltjesFunction.id.measure
        (stdOrthonormalBasis Real Real).toBasis.parallelepiped]; rw [A]
  simp only [volume, Module.Basis.addHaar, one_smul]

/--
theorem `volume_val` / 定理 `volume_val`

English:
theorem volume_val
  given: (s)
  statement: volume s = StieltjesFunction.id.measure s
  proof: by
  simp [volume_eq_stieltjes_id]

@[simp]

中文:
定理 volume_val
  条件: (s)
  结论: volume s = Stieltjes函数.id.measure s
  证明: by
  simp [volume_eq_stieltjes_id]

@[simp]

Depends on / 依赖: volume_eq_stieltjes_id
-/
theorem volume_val (s) : volume s = StieltjesFunction.id.measure s := by
  simp [volume_eq_stieltjes_id]

@[simp]
/--
theorem `volume_Ico` / 定理 `volume_Ico`

English:
theorem volume_Ico
  given: {a b : Real}
  statement: volume (Ico a b) = ofReal (b - a)
  proof: by simp [volume_val]

@[simp]

中文:
定理 volume_Ico
  条件: {a b : 实数}
  结论: volume (左闭右开区间 a b) = of实数 (b - a)
  证明: by simp [volume_val]

@[simp]

Depends on / 依赖: volume_val
-/
theorem volume_Ico {a b : Real} : volume (Ico a b) = ofReal (b - a) := by simp [volume_val]

@[simp]
/--
theorem `volume_real_Ico` / 定理 `volume_real_Ico`

English:
theorem volume_real_Ico
  given: {a b : Real}
  statement: volume.real (Ico a b) = max (b - a) 0
  proof: by
  simp [measureReal_def, ENNReal.toReal_ofReal']

中文:
定理 volume_real_Ico
  条件: {a b : 实数}
  结论: volume.real (左闭右开区间 a b) = 最大值 (b - a) 0
  证明: by
  simp [measureReal_def, ENNReal.toReal_ofReal']

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, measureReal_def, toReal_ofReal
-/
theorem volume_real_Ico {a b : Real} : volume.real (Ico a b) = max (b - a) 0 := by
  simp [measureReal_def, ENNReal.toReal_ofReal']

/--
theorem `volume_real_Ico_of_le` / 定理 `volume_real_Ico_of_le`

English:
theorem volume_real_Ico_of_le
  given: {a b : Real} (hab : a <= b)
  statement: volume.real (Ico a b) = b - a
  proof: by
  simp [hab]

@[simp]

中文:
定理 volume_real_Ico_of_le
  条件: {a b : 实数} (hab : a <= b)
  结论: volume.real (左闭右开区间 a b) = b - a
  证明: by
  simp [hab]

@[simp]
-/
theorem volume_real_Ico_of_le {a b : Real} (hab : a <= b) : volume.real (Ico a b) = b - a := by
  simp [hab]

@[simp]
/--
theorem `volume_Icc` / 定理 `volume_Icc`

English:
theorem volume_Icc
  given: {a b : Real}
  statement: volume (Icc a b) = ofReal (b - a)
  proof: by simp [volume_val]

@[simp]

中文:
定理 volume_Icc
  条件: {a b : 实数}
  结论: volume (闭区间 a b) = of实数 (b - a)
  证明: by simp [volume_val]

@[simp]

Depends on / 依赖: volume_val
-/
theorem volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b - a) := by simp [volume_val]

@[simp]
/--
theorem `volume_real_Icc` / 定理 `volume_real_Icc`

English:
theorem volume_real_Icc
  given: {a b : Real}
  statement: volume.real (Icc a b) = max (b - a) 0
  proof: by
  simp [measureReal_def, ENNReal.toReal_ofReal']

中文:
定理 volume_real_Icc
  条件: {a b : 实数}
  结论: volume.real (闭区间 a b) = 最大值 (b - a) 0
  证明: by
  simp [measureReal_def, ENNReal.toReal_ofReal']

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, measureReal_def, toReal_ofReal
-/
theorem volume_real_Icc {a b : Real} : volume.real (Icc a b) = max (b - a) 0 := by
  simp [measureReal_def, ENNReal.toReal_ofReal']

/--
theorem `volume_real_Icc_of_le` / 定理 `volume_real_Icc_of_le`

English:
theorem volume_real_Icc_of_le
  given: {a b : Real} (hab : a <= b)
  statement: volume.real (Icc a b) = b - a
  proof: by
  simp [hab]

@[simp]

中文:
定理 volume_real_Icc_of_le
  条件: {a b : 实数} (hab : a <= b)
  结论: volume.real (闭区间 a b) = b - a
  证明: by
  simp [hab]

@[simp]
-/
theorem volume_real_Icc_of_le {a b : Real} (hab : a <= b) : volume.real (Icc a b) = b - a := by
  simp [hab]

@[simp]
/--
theorem `volume_Ioo` / 定理 `volume_Ioo`

English:
theorem volume_Ioo
  given: {a b : Real}
  statement: volume (Ioo a b) = ofReal (b - a)
  proof: by simp [volume_val]

@[simp]

中文:
定理 volume_Ioo
  条件: {a b : 实数}
  结论: volume (开区间 a b) = of实数 (b - a)
  证明: by simp [volume_val]

@[simp]

Depends on / 依赖: volume_val
-/
theorem volume_Ioo {a b : Real} : volume (Ioo a b) = ofReal (b - a) := by simp [volume_val]

@[simp]
/--
theorem `volume_uIoo` / 定理 `volume_uIoo`

English:
theorem volume_uIoo
  given: {a b : Real}
  statement: volume (uIoo a b) = ofReal |b - a|
  proof: by
  simp [uIoo, volume_Ioo, max_sub_min_eq_abs]

@[simp]

中文:
定理 volume_uIoo
  条件: {a b : 实数}
  结论: volume (uIoo a b) = of实数 |b - a|
  证明: by
  simp [uIoo, volume_Ioo, max_sub_min_eq_abs]

@[simp]

Depends on / 依赖: max_sub_min_eq_abs, volume_Ioo
-/
theorem volume_uIoo {a b : Real} : volume (uIoo a b) = ofReal |b - a| := by
  simp [uIoo, volume_Ioo, max_sub_min_eq_abs]

@[simp]
/--
theorem `volume_real_Ioo` / 定理 `volume_real_Ioo`

English:
theorem volume_real_Ioo
  given: {a b : Real}
  statement: volume.real (Ioo a b) = max (b - a) 0
  proof: by
  simp [measureReal_def, ENNReal.toReal_ofReal']

中文:
定理 volume_real_Ioo
  条件: {a b : 实数}
  结论: volume.real (开区间 a b) = 最大值 (b - a) 0
  证明: by
  simp [measureReal_def, ENNReal.toReal_ofReal']

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, measureReal_def, toReal_ofReal
-/
theorem volume_real_Ioo {a b : Real} : volume.real (Ioo a b) = max (b - a) 0 := by
  simp [measureReal_def, ENNReal.toReal_ofReal']

/--
theorem `volume_real_Ioo_of_le` / 定理 `volume_real_Ioo_of_le`

English:
theorem volume_real_Ioo_of_le
  given: {a b : Real} (hab : a <= b)
  statement: volume.real (Ioo a b) = b - a
  proof: by
  simp [hab]

@[simp]

中文:
定理 volume_real_Ioo_of_le
  条件: {a b : 实数} (hab : a <= b)
  结论: volume.real (开区间 a b) = b - a
  证明: by
  simp [hab]

@[simp]
-/
theorem volume_real_Ioo_of_le {a b : Real} (hab : a <= b) : volume.real (Ioo a b) = b - a := by
  simp [hab]

@[simp]
/--
theorem `volume_Ioc` / 定理 `volume_Ioc`

English:
theorem volume_Ioc
  given: {a b : Real}
  statement: volume (Ioc a b) = ofReal (b - a)
  proof: by simp [volume_val]

@[simp]

中文:
定理 volume_Ioc
  条件: {a b : 实数}
  结论: volume (左开右闭区间 a b) = of实数 (b - a)
  证明: by simp [volume_val]

@[simp]

Depends on / 依赖: volume_val
-/
theorem volume_Ioc {a b : Real} : volume (Ioc a b) = ofReal (b - a) := by simp [volume_val]

@[simp]
/--
theorem `volume_uIoc` / 定理 `volume_uIoc`

English:
theorem volume_uIoc
  given: {a b : Real}
  statement: volume (uIoc a b) = ofReal |b - a|
  proof: by
  simp [uIoc, volume_Ioc, max_sub_min_eq_abs]

@[simp]

中文:
定理 volume_uIoc
  条件: {a b : 实数}
  结论: volume (uIoc a b) = of实数 |b - a|
  证明: by
  simp [uIoc, volume_Ioc, max_sub_min_eq_abs]

@[simp]

Depends on / 依赖: max_sub_min_eq_abs, volume_Ioc
-/
theorem volume_uIoc {a b : Real} : volume (uIoc a b) = ofReal |b - a| := by
  simp [uIoc, volume_Ioc, max_sub_min_eq_abs]

@[simp]
/--
theorem `volume_real_Ioc` / 定理 `volume_real_Ioc`

English:
theorem volume_real_Ioc
  given: {a b : Real}
  statement: volume.real (Ioc a b) = max (b - a) 0
  proof: by
  simp [measureReal_def, ENNReal.toReal_ofReal']

中文:
定理 volume_real_Ioc
  条件: {a b : 实数}
  结论: volume.real (左开右闭区间 a b) = 最大值 (b - a) 0
  证明: by
  simp [measureReal_def, ENNReal.toReal_ofReal']

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, measureReal_def, toReal_ofReal
-/
theorem volume_real_Ioc {a b : Real} : volume.real (Ioc a b) = max (b - a) 0 := by
  simp [measureReal_def, ENNReal.toReal_ofReal']

/--
theorem `volume_real_Ioc_of_le` / 定理 `volume_real_Ioc_of_le`

English:
theorem volume_real_Ioc_of_le
  given: {a b : Real} (hab : a <= b)
  statement: volume.real (Ioc a b) = b - a
  proof: by
  simp [hab]

中文:
定理 volume_real_Ioc_of_le
  条件: {a b : 实数} (hab : a <= b)
  结论: volume.real (左开右闭区间 a b) = b - a
  证明: by
  simp [hab]
-/
theorem volume_real_Ioc_of_le {a b : Real} (hab : a <= b) : volume.real (Ioc a b) = b - a := by
  simp [hab]

/--
theorem `volume_singleton` / 定理 `volume_singleton`

English:
theorem volume_singleton
  given: {a : Real}
  statement: volume ({a} : Set Real) = 0
  proof: by simp

中文:
定理 volume_singleton
  条件: {a : 实数}
  结论: volume ({a} : 集合 实数) = 0
  证明: by simp
-/
theorem volume_singleton {a : Real} : volume ({a} : Set Real) = 0 := by simp

/--
theorem `volume_univ` / 定理 `volume_univ`

English:
theorem volume_univ
  statement: volume (univ : Set Real) = ∞
  proof: ENNReal.eq_top_of_forall_nnreal_le fun r =>
    calc
      (r : Real>=0∞) = volume (Icc (0 : Real) r) := by simp
      _ <= volume univ := measure_mono (subset_univ _)

@[simp]

中文:
定理 volume_univ
  结论: volume (univ : 集合 实数) = ∞
  证明: ENNReal.eq_top_of_forall_nnreal_le fun r =>
    calc
      (r : Real>=0∞) = volume (Icc (0 : Real) r) := by simp
      _ <= volume univ := measure_mono (subset_univ _)

@[simp]

Depends on / 依赖: ENNReal, ENNReal.eq_top_of_forall_nnreal_le, eq_top_of_forall_nnreal_le, measure_mono, subset_univ, volume
-/
theorem volume_univ : volume (univ : Set Real) = ∞ :=
  ENNReal.eq_top_of_forall_nnreal_le fun r =>
    calc
      (r : Real>=0∞) = volume (Icc (0 : Real) r) := by simp
      _ <= volume univ := measure_mono (subset_univ _)

@[simp]
/--
theorem `volume_ball` / 定理 `volume_ball`

English:
theorem volume_ball
  given: (a r : Real)
  statement: volume (Metric.ball a r) = ofReal (2 * r)
  proof: by
  rw [ball_eq_Ioo]; rw [volume_Ioo]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [two_mul]

@[simp]

中文:
定理 volume_ball
  条件: (a r : 实数)
  结论: volume (Metric.ball a r) = of实数 (2 * r)
  证明: by
  rw [ball_eq_Ioo]; rw [volume_Ioo]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [two_mul]

@[simp]

Depends on / 依赖: add_sub_cancel_left, ball_eq_Ioo, sub_add, two_mul, volume_Ioo
-/
theorem volume_ball (a r : Real) : volume (Metric.ball a r) = ofReal (2 * r) := by
  rw [ball_eq_Ioo]; rw [volume_Ioo]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [two_mul]

@[simp]
/--
theorem `volume_real_ball` / 定理 `volume_real_ball`

English:
theorem volume_real_ball
  given: {a r : Real} (hr : 0 <= r)
  statement: volume.real (Metric.ball a r) = 2 * r
  proof: by
  simp [measureReal_def, hr]

@[simp]

中文:
定理 volume_real_ball
  条件: {a r : 实数} (hr : 0 <= r)
  结论: volume.real (Metric.ball a r) = 2 * r
  证明: by
  simp [measureReal_def, hr]

@[simp]

Depends on / 依赖: measureReal_def
-/
theorem volume_real_ball {a r : Real} (hr : 0 <= r) : volume.real (Metric.ball a r) = 2 * r := by
  simp [measureReal_def, hr]

@[simp]
/--
theorem `volume_closedBall` / 定理 `volume_closedBall`

English:
theorem volume_closedBall
  given: (a r : Real)
  statement: volume (Metric.closedBall a r) = ofReal (2 * r)
  proof: by
  rw [closedBall_eq_Icc]; rw [volume_Icc]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [two_mul]

@[simp]

中文:
定理 volume_closedBall
  条件: (a r : 实数)
  结论: volume (Metric.closedBall a r) = of实数 (2 * r)
  证明: by
  rw [closedBall_eq_Icc]; rw [volume_Icc]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [two_mul]

@[simp]

Depends on / 依赖: add_sub_cancel_left, closedBall_eq_Icc, sub_add, two_mul, volume_Icc
-/
theorem volume_closedBall (a r : Real) : volume (Metric.closedBall a r) = ofReal (2 * r) := by
  rw [closedBall_eq_Icc]; rw [volume_Icc]; rw [← sub_add]; rw [add_sub_cancel_left]; rw [two_mul]

@[simp]
/--
theorem `volume_real_closedBall` / 定理 `volume_real_closedBall`

English:
theorem volume_real_closedBall
  given: {a r : Real} (hr : 0 <= r)
  proof: by
  simp [measureReal_def, hr]

@[simp]

中文:
定理 volume_real_closedBall
  条件: {a r : 实数} (hr : 0 <= r)
  证明: by
  simp [measureReal_def, hr]

@[simp]

Depends on / 依赖: measureReal_def
-/
theorem volume_real_closedBall {a r : Real} (hr : 0 <= r) :
    volume.real (Metric.closedBall a r) = 2 * r := by
  simp [measureReal_def, hr]

@[simp]
/--
theorem `volume_eball` / 定理 `volume_eball`

English:
theorem volume_eball
  given: (a : Real) (r : Real>=0∞)
  statement: volume (Metric.eball a r) = 2 * r
  proof: by
  rcases eq_or_ne r ∞ with (rfl | hr)
  · rw [Metric.eball_top, volume_univ, two_mul, _root_.top_add]
  · lift r to Real>=0 using hr
    rw [Metric.eball_coe]; rw [volume_ball]; rw [two_mul]; rw [← NNReal.coe_add]; rw [ENNReal.ofReal_coe_nnreal]; rw [ENNReal.coe_add]; rw [two_mul]

@[deprecated (since := "2026-01-24")]
alias volume_emetric_ball := volume_eball

@[simp]

中文:
定理 volume_eball
  条件: (a : 实数) (r : 实数>=0∞)
  结论: volume (Metric.eball a r) = 2 * r
  证明: by
  rcases eq_or_ne r ∞ with (rfl | hr)
  · rw [Metric.eball_top, volume_univ, two_mul, _root_.top_add]
  · lift r to Real>=0 using hr
    rw [Metric.eball_coe]; rw [volume_ball]; rw [two_mul]; rw [← NNReal.coe_add]; rw [ENNReal.ofReal_coe_nnreal]; rw [ENNReal.coe_add]; rw [two_mul]

@[deprecated (since := "2026-01-24")]
alias volume_emetric_ball := volume_eball

@[simp]

Depends on / 依赖: ENNReal, ENNReal.coe_add, ENNReal.ofReal_coe_nnreal, Metric, Metric.eball_coe, Metric.eball_top, NNReal, NNReal.coe_add, _root_, _root_.top_add, coe_add, eball_coe, eball_top, eq_or_ne, ofReal_coe_nnreal, top_add, two_mul, volume_ball, volume_univ
-/
theorem volume_eball (a : Real) (r : Real>=0∞) : volume (Metric.eball a r) = 2 * r := by
  rcases eq_or_ne r ∞ with (rfl | hr)
  · rw [Metric.eball_top, volume_univ, two_mul, _root_.top_add]
  · lift r to Real>=0 using hr
    rw [Metric.eball_coe]; rw [volume_ball]; rw [two_mul]; rw [← NNReal.coe_add]; rw [ENNReal.ofReal_coe_nnreal]; rw [ENNReal.coe_add]; rw [two_mul]

@[deprecated (since := "2026-01-24")]
alias volume_emetric_ball := volume_eball

@[simp]
/--
theorem `volume_closedEBall` / 定理 `volume_closedEBall`

English:
theorem volume_closedEBall
  given: (a : Real) (r : Real>=0∞)
  statement: volume (Metric.closedEBall a r) = 2 * r
  proof: by
  rcases eq_or_ne r ∞ with (rfl | hr)
  · rw [Metric.closedEBall_top, volume_univ, two_mul, _root_.top_add]
  · lift r to Real>=0 using hr
    rw [Metric.closedEBall_coe]; rw [volume_closedBall]; rw [two_mul]; rw [← NNReal.coe_add]; rw [ENNReal.ofReal_coe_nnreal]; rw [ENNReal.coe_add]; rw [two_mul]

@[deprecated (since := "2026-01-24")]
alias volume_emetric_closedBall := volume_closedEBall

中文:
定理 volume_closedEBall
  条件: (a : 实数) (r : 实数>=0∞)
  结论: volume (Metric.closedEBall a r) = 2 * r
  证明: by
  rcases eq_or_ne r ∞ with (rfl | hr)
  · rw [Metric.closedEBall_top, volume_univ, two_mul, _root_.top_add]
  · lift r to Real>=0 using hr
    rw [Metric.closedEBall_coe]; rw [volume_closedBall]; rw [two_mul]; rw [← NNReal.coe_add]; rw [ENNReal.ofReal_coe_nnreal]; rw [ENNReal.coe_add]; rw [two_mul]

@[deprecated (since := "2026-01-24")]
alias volume_emetric_closedBall := volume_closedEBall

Depends on / 依赖: ENNReal, ENNReal.coe_add, ENNReal.ofReal_coe_nnreal, Metric, Metric.closedEBall_coe, Metric.closedEBall_top, NNReal, NNReal.coe_add, _root_, _root_.top_add, closedEBall_coe, closedEBall_top, coe_add, eq_or_ne, ofReal_coe_nnreal, top_add, two_mul, volume_closedBall, volume_univ
-/
theorem volume_closedEBall (a : Real) (r : Real>=0∞) : volume (Metric.closedEBall a r) = 2 * r := by
  rcases eq_or_ne r ∞ with (rfl | hr)
  · rw [Metric.closedEBall_top, volume_univ, two_mul, _root_.top_add]
  · lift r to Real>=0 using hr
    rw [Metric.closedEBall_coe]; rw [volume_closedBall]; rw [two_mul]; rw [← NNReal.coe_add]; rw [ENNReal.ofReal_coe_nnreal]; rw [ENNReal.coe_add]; rw [two_mul]

@[deprecated (since := "2026-01-24")]
alias volume_emetric_closedBall := volume_closedEBall

/--
Instance `nullSingletonClass_volume` / 实例 `nullSingletonClass_volume`

English:
instance nullSingletonClass_volume
  signature: : NullSingletonClass (volume : Measure Real)
  body: ⟨fun _ => volume_singleton⟩

@[deprecated (since := "2026-06-09")]
alias noAtoms_volume := nullSingletonClass_volume

@[simp]

中文:
实例 nullSingletonClass_volume
  签名: : NullSingleton类 (volume : 测度 实数)
  定义体: ⟨fun _ => volume_singleton⟩

@[deprecated (since := "2026-06-09")]
alias noAtoms_volume := nullSingletonClass_volume

@[simp]

Depends on / 依赖: volume_singleton
-/
instance nullSingletonClass_volume : NullSingletonClass (volume : Measure Real) :=
  ⟨fun _ => volume_singleton⟩

@[deprecated (since := "2026-06-09")]
alias noAtoms_volume := nullSingletonClass_volume

@[simp]
/--
theorem `volume_interval` / 定理 `volume_interval`

English:
theorem volume_interval
  given: {a b : Real}
  statement: volume (uIcc a b) = ofReal |b - a|
  proof: by
  rw [← Icc_min_max]; rw [volume_Icc]; rw [max_sub_min_eq_abs]

@[simp]

中文:
定理 volume_interval
  条件: {a b : 实数}
  结论: volume (uIcc a b) = of实数 |b - a|
  证明: by
  rw [← Icc_min_max]; rw [volume_Icc]; rw [max_sub_min_eq_abs]

@[simp]

Depends on / 依赖: Icc_min_max, max_sub_min_eq_abs, volume_Icc
-/
theorem volume_interval {a b : Real} : volume (uIcc a b) = ofReal |b - a| := by
  rw [← Icc_min_max]; rw [volume_Icc]; rw [max_sub_min_eq_abs]

@[simp]
/--
theorem `volume_real_interval` / 定理 `volume_real_interval`

English:
theorem volume_real_interval
  given: {a b : Real}
  statement: volume.real (uIcc a b) = |b - a|
  proof: by
  simp [measureReal_def]

@[simp]

中文:
定理 volume_real_interval
  条件: {a b : 实数}
  结论: volume.real (uIcc a b) = |b - a|
  证明: by
  simp [measureReal_def]

@[simp]

Depends on / 依赖: measureReal_def
-/
theorem volume_real_interval {a b : Real} : volume.real (uIcc a b) = |b - a| := by
  simp [measureReal_def]

@[simp]
/--
theorem `volume_Ioi` / 定理 `volume_Ioi`

English:
theorem volume_Ioi
  given: {a : Real}
  statement: volume (Ioi a) = ∞
  proof: top_unique
    le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n =>
      calc
        (n : Real>=0∞) = volume (Ioo a (a + n)) := by simp
        _ <= volume (Ioi a) := measure_mono Ioo_subset_Ioi_self

@[simp]

中文:
定理 volume_Ioi
  条件: {a : 实数}
  结论: volume (左开右无界区间 a) = ∞
  证明: top_unique
    le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n =>
      calc
        (n : Real>=0∞) = volume (Ioo a (a + n)) := by simp
        _ <= volume (Ioi a) := measure_mono Ioo_subset_Ioi_self

@[simp]

Depends on / 依赖: ENNReal, ENNReal.tendsto_nat_nhds_top, Ioo_subset_Ioi_self, le_of_tendsto, measure_mono, tendsto_nat_nhds_top, top_unique, volume
-/
theorem volume_Ioi {a : Real} : volume (Ioi a) = ∞ :=
top_unique
    le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n =>
      calc
        (n : Real>=0∞) = volume (Ioo a (a + n)) := by simp
        _ <= volume (Ioi a) := measure_mono Ioo_subset_Ioi_self

@[simp]
/--
theorem `volume_Ici` / 定理 `volume_Ici`

English:
theorem volume_Ici
  given: {a : Real}
  statement: volume (Ici a) = ∞
  proof: by rw [← measure_congr Ioi_ae_eq_Ici]; simp

@[simp]

中文:
定理 volume_Ici
  条件: {a : 实数}
  结论: volume (左闭右无界区间 a) = ∞
  证明: by rw [← measure_congr Ioi_ae_eq_Ici]; simp

@[simp]

Depends on / 依赖: Ioi_ae_eq_Ici, measure_congr
-/
theorem volume_Ici {a : Real} : volume (Ici a) = ∞ := by rw [← measure_congr Ioi_ae_eq_Ici]; simp

@[simp]
/--
theorem `volume_Iio` / 定理 `volume_Iio`

English:
theorem volume_Iio
  given: {a : Real}
  statement: volume (Iio a) = ∞
  proof: top_unique
    le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n =>
      calc
        (n : Real>=0∞) = volume (Ioo (a - n) a) := by simp
        _ <= volume (Iio a) := measure_mono Ioo_subset_Iio_self

@[simp]

中文:
定理 volume_Iio
  条件: {a : 实数}
  结论: volume (左无界右开区间 a) = ∞
  证明: top_unique
    le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n =>
      calc
        (n : Real>=0∞) = volume (Ioo (a - n) a) := by simp
        _ <= volume (Iio a) := measure_mono Ioo_subset_Iio_self

@[simp]

Depends on / 依赖: ENNReal, ENNReal.tendsto_nat_nhds_top, Ioo_subset_Iio_self, le_of_tendsto, measure_mono, tendsto_nat_nhds_top, top_unique, volume
-/
theorem volume_Iio {a : Real} : volume (Iio a) = ∞ :=
top_unique
    le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n =>
      calc
        (n : Real>=0∞) = volume (Ioo (a - n) a) := by simp
        _ <= volume (Iio a) := measure_mono Ioo_subset_Iio_self

@[simp]
/--
theorem `volume_Iic` / 定理 `volume_Iic`

English:
theorem volume_Iic
  given: {a : Real}
  statement: volume (Iic a) = ∞
  proof: by rw [← measure_congr Iio_ae_eq_Iic]; simp

中文:
定理 volume_Iic
  条件: {a : 实数}
  结论: volume (左无界右闭区间 a) = ∞
  证明: by rw [← measure_congr Iio_ae_eq_Iic]; simp

Depends on / 依赖: Iio_ae_eq_Iic, measure_congr
-/
theorem volume_Iic {a : Real} : volume (Iic a) = ∞ := by rw [← measure_congr Iio_ae_eq_Iic]; simp

/--
Instance `locallyFinite_volume` / 实例 `locallyFinite_volume`

English:
instance locallyFinite_volume
  signature: : IsLocallyFiniteMeasure (volume : Measure Real)
  body: ⟨fun x =>
    ⟨Ioo (x - 1) (x + 1),
      IsOpen.mem_nhds isOpen_Ioo ⟨sub_lt_self _ zero_lt_one, lt_add_of_pos_right _ zero_lt_one⟩, by
      simp only [Real.volume_Ioo, ENNReal.ofReal_lt_top]⟩⟩

中文:
实例 locallyFinite_volume
  签名: : 是局部有限测度 (volume : 测度 实数)
  定义体: ⟨fun x =>
    ⟨Ioo (x - 1) (x + 1),
      IsOpen.mem_nhds isOpen_Ioo ⟨sub_lt_self _ zero_lt_one, lt_add_of_pos_right _ zero_lt_one⟩, by
      simp only [Real.volume_Ioo, ENNReal.ofReal_lt_top]⟩⟩

Depends on / 依赖: ENNReal, ENNReal.ofReal_lt_top, IsOpen, IsOpen.mem_nhds, Real.volume_Ioo, isOpen_Ioo, lt_add_of_pos_right, mem_nhds, ofReal_lt_top, sub_lt_self, volume_Ioo, zero_lt_one
-/
instance locallyFinite_volume : IsLocallyFiniteMeasure (volume : Measure Real) :=
  ⟨fun x =>
    ⟨Ioo (x - 1) (x + 1),
      IsOpen.mem_nhds isOpen_Ioo ⟨sub_lt_self _ zero_lt_one, lt_add_of_pos_right _ zero_lt_one⟩, by
      simp only [Real.volume_Ioo, ENNReal.ofReal_lt_top]⟩⟩

/--
Instance `isFiniteMeasure_restrict_Icc` / 实例 `isFiniteMeasure_restrict_Icc`

English:
instance isFiniteMeasure_restrict_Icc
  signature: (x y : Real)
  body: ⟨by simp⟩

中文:
实例 isFiniteMeasure_restrict_Icc
  签名: (x y : 实数)
  定义体: ⟨by simp⟩
-/
instance isFiniteMeasure_restrict_Icc (x y : Real) : IsFiniteMeasure (volume.restrict (Icc x y)) :=
  ⟨by simp⟩

/--
Instance `isFiniteMeasure_restrict_Ico` / 实例 `isFiniteMeasure_restrict_Ico`

English:
instance isFiniteMeasure_restrict_Ico
  signature: (x y : Real)
  body: ⟨by simp⟩

中文:
实例 isFiniteMeasure_restrict_Ico
  签名: (x y : 实数)
  定义体: ⟨by simp⟩
-/
instance isFiniteMeasure_restrict_Ico (x y : Real) : IsFiniteMeasure (volume.restrict (Ico x y)) :=
  ⟨by simp⟩

/--
Instance `isFiniteMeasure_restrict_Ioc` / 实例 `isFiniteMeasure_restrict_Ioc`

English:
instance isFiniteMeasure_restrict_Ioc
  signature: (x y : Real)
  body: ⟨by simp⟩

中文:
实例 isFiniteMeasure_restrict_Ioc
  签名: (x y : 实数)
  定义体: ⟨by simp⟩
-/
instance isFiniteMeasure_restrict_Ioc (x y : Real) : IsFiniteMeasure (volume.restrict (Ioc x y)) :=
  ⟨by simp⟩

/--
Instance `isFiniteMeasure_restrict_Ioo` / 实例 `isFiniteMeasure_restrict_Ioo`

English:
instance isFiniteMeasure_restrict_Ioo
  signature: (x y : Real)
  body: ⟨by simp⟩

中文:
实例 isFiniteMeasure_restrict_Ioo
  签名: (x y : 实数)
  定义体: ⟨by simp⟩
-/
instance isFiniteMeasure_restrict_Ioo (x y : Real) : IsFiniteMeasure (volume.restrict (Ioo x y)) :=
  ⟨by simp⟩

/--
theorem `volume_le_diam` / 定理 `volume_le_diam`

English:
theorem volume_le_diam
  given: (s : Set Real)
  statement: volume s <= ediam s
  proof: by
  by_cases hs : Bornology.IsBounded s
  · rw [Real.ediam_eq hs, ← volume_Icc]
    exact volume.mono hs.subset_Icc_sInf_sSup
  · rw [Metric.ediam_of_unbounded hs]; exact le_top

中文:
定理 volume_le_diam
  条件: (s : 集合 实数)
  结论: volume s <= ediam s
  证明: by
  by_cases hs : Bornology.IsBounded s
  · rw [Real.ediam_eq hs, ← volume_Icc]
    exact volume.mono hs.subset_Icc_sInf_sSup
  · rw [Metric.ediam_of_unbounded hs]; exact le_top

Depends on / 依赖: Bornology, Bornology.IsBounded, IsBounded, Metric, Metric.ediam_of_unbounded, Real.ediam_eq, ediam_eq, ediam_of_unbounded, hs.subset_Icc_sInf_sSup, le_top, subset_Icc_sInf_sSup, volume, volume.mono, volume_Icc
-/
theorem volume_le_diam (s : Set Real) : volume s <= ediam s := by
  by_cases hs : Bornology.IsBounded s
  · rw [Real.ediam_eq hs, ← volume_Icc]
    exact volume.mono hs.subset_Icc_sInf_sSup
  · rw [Metric.ediam_of_unbounded hs]; exact le_top

/--
theorem `_root_.Filter.Eventually.volume_pos_of_nhds_real` / 定理 `_root_.Filter.Eventually.volume_pos_of_nhds_real`

English:
theorem _root_.Filter.Eventually.volume_pos_of_nhds_real
  statement: {p : Real -> Prop} {a : Real}
  proof: by
  rcases h.exists_Ioo_subset with ⟨l, u, hx, hs⟩
  grw [← hs]
  simpa [-mem_Ioo] using hx.1.trans hx.2

中文:
定理 _root_.滤子.Eventually.volume_pos_of_nhds_real
  结论: {p : 实数 -> 命题} {a : 实数}
  证明: by
  rcases h.exists_Ioo_subset with ⟨l, u, hx, hs⟩
  grw [← hs]
  simpa [-mem_Ioo] using hx.1.trans hx.2

Depends on / 依赖: exists_Ioo_subset, h.exists_Ioo_subset, mem_Ioo
-/
theorem _root_.Filter.Eventually.volume_pos_of_nhds_real {p : Real -> Prop} {a : Real}
    (h : forallᶠ x in 𝓝 a, p x) : (0 : Real>=0∞) < volume { x | p x } := by
  rcases h.exists_Ioo_subset with ⟨l, u, hx, hs⟩
  grw [← hs]
  simpa [-mem_Ioo] using hx.1.trans hx.2



/--
theorem `volume_Icc_pi` / 定理 `volume_Icc_pi`

English:
theorem volume_Icc_pi
  given: {a b : ι -> Real}
  statement: volume (Icc a b) = ∏ i, ENNReal.ofReal (b i - a i)
  proof: by
  rw [← pi_univ_Icc]; rw [volume_pi_pi]
  simp only [Real.volume_Icc]

@[simp]

中文:
定理 volume_Icc_pi
  条件: {a b : ι -> 实数}
  结论: volume (闭区间 a b) = ∏ i, 广义非负实数.of实数 (b i - a i)
  证明: by
  rw [← pi_univ_Icc]; rw [volume_pi_pi]
  simp only [Real.volume_Icc]

@[simp]

Depends on / 依赖: Real.volume_Icc, pi_univ_Icc, volume_Icc, volume_pi_pi
-/
theorem volume_Icc_pi {a b : ι -> Real} : volume (Icc a b) = ∏ i, ENNReal.ofReal (b i - a i) := by
  rw [← pi_univ_Icc]; rw [volume_pi_pi]
  simp only [Real.volume_Icc]

@[simp]
/--
theorem `volume_Icc_pi_toReal` / 定理 `volume_Icc_pi_toReal`

English:
theorem volume_Icc_pi_toReal
  given: {a b : ι -> Real} (h : a <= b)
  proof: by
  simp only [volume_Icc_pi, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

中文:
定理 volume_Icc_pi_to实数
  条件: {a b : ι -> 实数} (h : a <= b)
  证明: by
  simp only [volume_Icc_pi, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, ENNReal.toReal_prod, sub_nonneg, toReal_ofReal, toReal_prod, volume_Icc_pi
-/
theorem volume_Icc_pi_toReal {a b : ι -> Real} (h : a <= b) :
    (volume (Icc a b)).toReal = ∏ i, (b i - a i) := by
  simp only [volume_Icc_pi, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

/--
theorem `volume_pi_Ioo` / 定理 `volume_pi_Ioo`

English:
theorem volume_pi_Ioo
  given: {a b : ι -> Real}
  proof: (measure_congr Measure.univ_pi_Ioo_ae_eq_Icc).trans volume_Icc_pi

@[simp]

中文:
定理 volume_pi_Ioo
  条件: {a b : ι -> 实数}
  证明: (measure_congr Measure.univ_pi_Ioo_ae_eq_Icc).trans volume_Icc_pi

@[simp]

Depends on / 依赖: Measure, Measure.univ_pi_Ioo_ae_eq_Icc, measure_congr, univ_pi_Ioo_ae_eq_Icc, volume_Icc_pi
-/
theorem volume_pi_Ioo {a b : ι -> Real} :
    volume (pi univ fun i => Ioo (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i) :=
  (measure_congr Measure.univ_pi_Ioo_ae_eq_Icc).trans volume_Icc_pi

@[simp]
/--
theorem `volume_pi_Ioo_toReal` / 定理 `volume_pi_Ioo_toReal`

English:
theorem volume_pi_Ioo_toReal
  given: {a b : ι -> Real} (h : a <= b)
  proof: by
  simp only [volume_pi_Ioo, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

中文:
定理 volume_pi_Ioo_to实数
  条件: {a b : ι -> 实数} (h : a <= b)
  证明: by
  simp only [volume_pi_Ioo, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, ENNReal.toReal_prod, _mem, finsetSup, sub_nonneg, subset_supClosure, supClosed_supClosure, supClosed_supClosure.finsetSup, toReal_ofReal, toReal_prod, volume_pi_Ioo
-/
theorem volume_pi_Ioo_toReal {a b : ι -> Real} (h : a <= b) :
    (volume (pi univ fun i => Ioo (a i) (b i))).toReal = ∏ i, (b i - a i) := by
  simp only [volume_pi_Ioo, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

/--
theorem `volume_pi_Ioc` / 定理 `volume_pi_Ioc`

English:
theorem volume_pi_Ioc
  given: {a b : ι -> Real}
  proof: (measure_congr Measure.univ_pi_Ioc_ae_eq_Icc).trans volume_Icc_pi

@[simp]

中文:
定理 volume_pi_Ioc
  条件: {a b : ι -> 实数}
  证明: (measure_congr Measure.univ_pi_Ioc_ae_eq_Icc).trans volume_Icc_pi

@[simp]

Depends on / 依赖: Measure, Measure.univ_pi_Ioc_ae_eq_Icc, measure_congr, univ_pi_Ioc_ae_eq_Icc, volume_Icc_pi
-/
theorem volume_pi_Ioc {a b : ι -> Real} :
    volume (pi univ fun i => Ioc (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i) :=
  (measure_congr Measure.univ_pi_Ioc_ae_eq_Icc).trans volume_Icc_pi

@[simp]
/--
theorem `volume_pi_Ioc_toReal` / 定理 `volume_pi_Ioc_toReal`

English:
theorem volume_pi_Ioc_toReal
  given: {a b : ι -> Real} (h : a <= b)
  proof: by
  simp only [volume_pi_Ioc, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

中文:
定理 volume_pi_Ioc_to实数
  条件: {a b : ι -> 实数} (h : a <= b)
  证明: by
  simp only [volume_pi_Ioc, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, ENNReal.toReal_prod, sub_nonneg, toReal_ofReal, toReal_prod, volume_pi_Ioc
-/
theorem volume_pi_Ioc_toReal {a b : ι -> Real} (h : a <= b) :
    (volume (pi univ fun i => Ioc (a i) (b i))).toReal = ∏ i, (b i - a i) := by
  simp only [volume_pi_Ioc, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

/--
theorem `volume_pi_Ico` / 定理 `volume_pi_Ico`

English:
theorem volume_pi_Ico
  given: {a b : ι -> Real}
  proof: (measure_congr Measure.univ_pi_Ico_ae_eq_Icc).trans volume_Icc_pi

@[simp]

中文:
定理 volume_pi_Ico
  条件: {a b : ι -> 实数}
  证明: (measure_congr Measure.univ_pi_Ico_ae_eq_Icc).trans volume_Icc_pi

@[simp]

Depends on / 依赖: Measure, Measure.univ_pi_Ico_ae_eq_Icc, measure_congr, univ_pi_Ico_ae_eq_Icc, volume_Icc_pi
-/
theorem volume_pi_Ico {a b : ι -> Real} :
    volume (pi univ fun i => Ico (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i) :=
  (measure_congr Measure.univ_pi_Ico_ae_eq_Icc).trans volume_Icc_pi

@[simp]
/--
theorem `volume_pi_Ico_toReal` / 定理 `volume_pi_Ico_toReal`

English:
theorem volume_pi_Ico_toReal
  given: {a b : ι -> Real} (h : a <= b)
  proof: by
  simp only [volume_pi_Ico, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

@[simp]
nonrec theorem volume_pi_ball (a : ι -> Real) {r : Real} (hr : 0 < r) :
    volume (Metric.ball a r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
  simp only [MeasureTheory.volume_pi_ball a hr, volume_ball, Finset.prod_const]
  exact (ENNReal.ofReal_pow (mul_nonneg zero_le_two hr.le) _).symm

@[simp]
nonrec theorem volume_pi_closedBall (a : ι -> Real) {r : Real} (hr : 0 <= r) :
    volume (Metric.closedBall a r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
  simp only [MeasureTheory.volume_pi_closedBall a hr, volume_closedBall, Finset.prod_const]
  exact (ENNReal.ofReal_pow (mul_nonneg zero_le_two hr) _).symm

中文:
定理 volume_pi_Ico_to实数
  条件: {a b : ι -> 实数} (h : a <= b)
  证明: by
  simp only [volume_pi_Ico, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

@[simp]
nonrec theorem volume_pi_ball (a : ι -> Real) {r : Real} (hr : 0 < r) :
    volume (Metric.ball a r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
  simp only [MeasureTheory.volume_pi_ball a hr, volume_ball, Finset.prod_const]
  exact (ENNReal.ofReal_pow (mul_nonneg zero_le_two hr.le) _).symm

@[simp]
nonrec theorem volume_pi_closedBall (a : ι -> Real) {r : Real} (hr : 0 <= r) :
    volume (Metric.closedBall a r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
  simp only [MeasureTheory.volume_pi_closedBall a hr, volume_closedBall, Finset.prod_const]
  exact (ENNReal.ofReal_pow (mul_nonneg zero_le_two hr) _).symm

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, ENNReal.toReal_prod, sub_nonneg, toReal_ofReal, toReal_prod, volume_pi_Ico
-/
theorem volume_pi_Ico_toReal {a b : ι -> Real} (h : a <= b) :
    (volume (pi univ fun i => Ico (a i) (b i))).toReal = ∏ i, (b i - a i) := by
  simp only [volume_pi_Ico, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

@[simp]
nonrec theorem volume_pi_ball (a : ι -> Real) {r : Real} (hr : 0 < r) :
    volume (Metric.ball a r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
  simp only [MeasureTheory.volume_pi_ball a hr, volume_ball, Finset.prod_const]
  exact (ENNReal.ofReal_pow (mul_nonneg zero_le_two hr.le) _).symm

@[simp]
nonrec theorem volume_pi_closedBall (a : ι -> Real) {r : Real} (hr : 0 <= r) :
    volume (Metric.closedBall a r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
  simp only [MeasureTheory.volume_pi_closedBall a hr, volume_closedBall, Finset.prod_const]
  exact (ENNReal.ofReal_pow (mul_nonneg zero_le_two hr) _).symm

/--
theorem `volume_pi_le_prod_diam` / 定理 `volume_pi_le_prod_diam`

English:
theorem volume_pi_le_prod_diam
  given: (s : Set (ι -> Real))
  proof: calc
    volume s <= volume (pi univ fun i => closure (Function.eval i '' s)) :=
volume.mono
Subset.trans (subset_pi_eval_image univ s) pi_mono fun _ _ => subset_closure
    _ = ∏ i, volume (closure <| Function.eval i '' s) := volume_pi_pi _
    _ <= ∏ i : ι, ediam (Function.eval i '' s) :=
      Finset.prod_le_prod' fun _ _ => (volume_le_diam _).trans_eq (ediam_closure _)

中文:
定理 volume_pi_le_prod_diam
  条件: (s : 集合 (ι -> 实数))
  证明: calc
    volume s <= volume (pi univ fun i => closure (Function.eval i '' s)) :=
volume.mono
Subset.trans (subset_pi_eval_image univ s) pi_mono fun _ _ => subset_closure
    _ = ∏ i, volume (closure <| Function.eval i '' s) := volume_pi_pi _
    _ <= ∏ i : ι, ediam (Function.eval i '' s) :=
      Finset.prod_le_prod' fun _ _ => (volume_le_diam _).trans_eq (ediam_closure _)

Depends on / 依赖: Finset, Finset.prod_le_prod, Function, Function.eval, Subset, Subset.trans, closure, ediam_closure, pi_mono, prod_le_prod, subset_closure, subset_pi_eval_image, trans_eq, volume, volume.mono, volume_le_diam, volume_pi_pi
-/
theorem volume_pi_le_prod_diam (s : Set (ι -> Real)) :
    volume s <= ∏ i : ι, ediam (Function.eval i '' s) :=
  calc
    volume s <= volume (pi univ fun i => closure (Function.eval i '' s)) :=
volume.mono
Subset.trans (subset_pi_eval_image univ s) pi_mono fun _ _ => subset_closure
    _ = ∏ i, volume (closure <| Function.eval i '' s) := volume_pi_pi _
    _ <= ∏ i : ι, ediam (Function.eval i '' s) :=
      Finset.prod_le_prod' fun _ _ => (volume_le_diam _).trans_eq (ediam_closure _)

/--
theorem `volume_pi_le_diam_pow` / 定理 `volume_pi_le_diam_pow`

English:
theorem volume_pi_le_diam_pow
  given: (s : Set (ι -> Real))
  statement: volume s <= ediam s ^ Fintype.card ι
  proof: calc
    volume s <= ∏ i : ι, ediam (Function.eval i '' s) := volume_pi_le_prod_diam s
    _ <= ∏ _i : ι, (1 : Real>=0) * ediam s :=
      (Finset.prod_le_prod' fun i _ => (LipschitzWith.eval i).ediam_image_le s)
    _ = ediam s ^ Fintype.card ι := by
      simp only [ENNReal.coe_one, one_mul, Finset.prod_const, Fintype.card]

中文:
定理 volume_pi_le_diam_pow
  条件: (s : 集合 (ι -> 实数))
  结论: volume s <= ediam s ^ 有限类型.card ι
  证明: calc
    volume s <= ∏ i : ι, ediam (Function.eval i '' s) := volume_pi_le_prod_diam s
    _ <= ∏ _i : ι, (1 : Real>=0) * ediam s :=
      (Finset.prod_le_prod' fun i _ => (LipschitzWith.eval i).ediam_image_le s)
    _ = ediam s ^ Fintype.card ι := by
      simp only [ENNReal.coe_one, one_mul, Finset.prod_const, Fintype.card]

Depends on / 依赖: ENNReal, ENNReal.coe_one, Finset, Finset.prod_const, Finset.prod_le_prod, Fintype, Fintype.card, Function, Function.eval, LipschitzWith, LipschitzWith.eval, coe_one, ediam_image_le, one_mul, prod_const, prod_le_prod, volume, volume_pi_le_prod_diam
-/
theorem volume_pi_le_diam_pow (s : Set (ι -> Real)) : volume s <= ediam s ^ Fintype.card ι :=
  calc
    volume s <= ∏ i : ι, ediam (Function.eval i '' s) := volume_pi_le_prod_diam s
    _ <= ∏ _i : ι, (1 : Real>=0) * ediam s :=
      (Finset.prod_le_prod' fun i _ => (LipschitzWith.eval i).ediam_image_le s)
    _ = ediam s ^ Fintype.card ι := by
      simp only [ENNReal.coe_one, one_mul, Finset.prod_const, Fintype.card]



/--
theorem `smul_map_volume_mul_left` / 定理 `smul_map_volume_mul_left`

English:
theorem smul_map_volume_mul_left
  given: {a : Real} (h : a != 0)
  proof: by
  refine (Real.measure_ext_Ioo_rat fun p q => ?_).symm
  rcases lt_or_gt_of_ne h with h | h
  · simp only [Real.volume_Ioo, Measure.smul_apply, ← ENNReal.ofReal_mul (le_of_lt <| neg_pos.2 h),
      Measure.map_apply (measurable_const_mul a) measurableSet_Ioo, neg_sub_neg, neg_mul,
      preimage_const_mul_Ioo_of_neg _ _ h, abs_of_neg h, mul_sub, smul_eq_mul,
      mul_div_cancel₀ _ (ne_of_lt h)]
  · simp only [Real.volume_Ioo, Measure.smul_apply, ← ENNReal.ofReal_mul (le_of_lt h),
      Measure.map_apply (measurable_const_mul a) measurableSet_Ioo, preimage_const_mul_Ioo₀ _ _ h,
      abs_of_pos h, mul_sub, mul_div_cancel₀ _ (ne_of_gt h), smul_eq_mul]

中文:
定理 smul_map_volume_mul_left
  条件: {a : 实数} (h : a != 0)
  证明: by
  refine (Real.measure_ext_Ioo_rat fun p q => ?_).symm
  rcases lt_or_gt_of_ne h with h | h
  · simp only [Real.volume_Ioo, Measure.smul_apply, ← ENNReal.ofReal_mul (le_of_lt <| neg_pos.2 h),
      Measure.map_apply (measurable_const_mul a) measurableSet_Ioo, neg_sub_neg, neg_mul,
      preimage_const_mul_Ioo_of_neg _ _ h, abs_of_neg h, mul_sub, smul_eq_mul,
      mul_div_cancel₀ _ (ne_of_lt h)]
  · simp only [Real.volume_Ioo, Measure.smul_apply, ← ENNReal.ofReal_mul (le_of_lt h),
      Measure.map_apply (measurable_const_mul a) measurableSet_Ioo, preimage_const_mul_Ioo₀ _ _ h,
      abs_of_pos h, mul_sub, mul_div_cancel₀ _ (ne_of_gt h), smul_eq_mul]

Depends on / 依赖: ENNReal, ENNReal.ofReal_mul, Measure, Measure.map_apply, Measure.smul_apply, Real.measure_ext_Ioo_rat, Real.volume_Ioo, abs_of_neg, le_of_lt, lt_or_gt_of_ne, map_apply, measurableSet_Ioo, measurable_const_m, measurable_const_mul, measure_ext_Ioo_rat, mul_sub, ne_of_lt, neg_mul, neg_pos, neg_sub_neg
-/
theorem smul_map_volume_mul_left {a : Real} (h : a != 0) :
    ENNReal.ofReal |a| • Measure.map (a * ·) volume = volume := by
  refine (Real.measure_ext_Ioo_rat fun p q => ?_).symm
  rcases lt_or_gt_of_ne h with h | h
  · simp only [Real.volume_Ioo, Measure.smul_apply, ← ENNReal.ofReal_mul (le_of_lt <| neg_pos.2 h),
      Measure.map_apply (measurable_const_mul a) measurableSet_Ioo, neg_sub_neg, neg_mul,
      preimage_const_mul_Ioo_of_neg _ _ h, abs_of_neg h, mul_sub, smul_eq_mul,
      mul_div_cancel₀ _ (ne_of_lt h)]
  · simp only [Real.volume_Ioo, Measure.smul_apply, ← ENNReal.ofReal_mul (le_of_lt h),
      Measure.map_apply (measurable_const_mul a) measurableSet_Ioo, preimage_const_mul_Ioo₀ _ _ h,
      abs_of_pos h, mul_sub, mul_div_cancel₀ _ (ne_of_gt h), smul_eq_mul]

/--
theorem `map_volume_mul_left` / 定理 `map_volume_mul_left`

English:
theorem map_volume_mul_left
  given: {a : Real} (h : a != 0)
  proof: by
  conv_rhs =>
    rw [← Real.smul_map_volume_mul_left h]; rw [smul_smul]; rw [← ENNReal.ofReal_mul (abs_nonneg _)]; rw [←
      abs_mul]; rw [inv_mul_cancel₀ h]; rw [abs_one]; rw [ENNReal.ofReal_one]; rw [one_smul]

@[simp]

中文:
定理 map_volume_mul_left
  条件: {a : 实数} (h : a != 0)
  证明: by
  conv_rhs =>
    rw [← Real.smul_map_volume_mul_left h]; rw [smul_smul]; rw [← ENNReal.ofReal_mul (abs_nonneg _)]; rw [←
      abs_mul]; rw [inv_mul_cancel₀ h]; rw [abs_one]; rw [ENNReal.ofReal_one]; rw [one_smul]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal_mul, ENNReal.ofReal_one, Real.smul_map_volume_mul_left, abs_mul, abs_nonneg, abs_one, conv_rhs, ofReal_mul, ofReal_one, one_smul, smul_map_volume_mul_left, smul_smul
-/
theorem map_volume_mul_left {a : Real} (h : a != 0) :
    Measure.map (a * ·) volume = ENNReal.ofReal |a⁻¹| • volume := by
  conv_rhs =>
    rw [← Real.smul_map_volume_mul_left h]; rw [smul_smul]; rw [← ENNReal.ofReal_mul (abs_nonneg _)]; rw [←
      abs_mul]; rw [inv_mul_cancel₀ h]; rw [abs_one]; rw [ENNReal.ofReal_one]; rw [one_smul]

@[simp]
/--
theorem `volume_preimage_mul_left` / 定理 `volume_preimage_mul_left`

English:
theorem volume_preimage_mul_left
  given: {a : Real} (h : a != 0) (s : Set Real)
  proof: calc
    volume ((a * ·) ⁻¹' s) = Measure.map (a * ·) volume s :=
      ((Homeomorph.mulLeft₀ a h).toMeasurableEquiv.map_apply s).symm
    _ = ENNReal.ofReal (abs a⁻¹) * volume s := by rw [map_volume_mul_left h]; rfl

中文:
定理 volume_preimage_mul_left
  条件: {a : 实数} (h : a != 0) (s : 集合 实数)
  证明: calc
    volume ((a * ·) ⁻¹' s) = Measure.map (a * ·) volume s :=
      ((Homeomorph.mulLeft₀ a h).toMeasurableEquiv.map_apply s).symm
    _ = ENNReal.ofReal (abs a⁻¹) * volume s := by rw [map_volume_mul_left h]; rfl

Depends on / 依赖: ENNReal, ENNReal.ofReal, Homeomorph, Homeomorph.mulLeft, Measure, Measure.map, map_apply, map_volume_mul_left, ofReal, toMeasurableEquiv, toMeasurableEquiv.map_apply, volume
-/
theorem volume_preimage_mul_left {a : Real} (h : a != 0) (s : Set Real) :
    volume ((a * ·) ⁻¹' s) = ENNReal.ofReal (abs a⁻¹) * volume s :=
  calc
    volume ((a * ·) ⁻¹' s) = Measure.map (a * ·) volume s :=
      ((Homeomorph.mulLeft₀ a h).toMeasurableEquiv.map_apply s).symm
    _ = ENNReal.ofReal (abs a⁻¹) * volume s := by rw [map_volume_mul_left h]; rfl

/--
theorem `smul_map_volume_mul_right` / 定理 `smul_map_volume_mul_right`

English:
theorem smul_map_volume_mul_right
  given: {a : Real} (h : a != 0)
  proof: by
  simpa only [mul_comm] using Real.smul_map_volume_mul_left h

中文:
定理 smul_map_volume_mul_right
  条件: {a : 实数} (h : a != 0)
  证明: by
  simpa only [mul_comm] using Real.smul_map_volume_mul_left h

Depends on / 依赖: Real.smul_map_volume_mul_left, mul_comm, smul_map_volume_mul_left
-/
theorem smul_map_volume_mul_right {a : Real} (h : a != 0) :
    ENNReal.ofReal |a| • Measure.map (· * a) volume = volume := by
  simpa only [mul_comm] using Real.smul_map_volume_mul_left h

/--
theorem `map_volume_mul_right` / 定理 `map_volume_mul_right`

English:
theorem map_volume_mul_right
  given: {a : Real} (h : a != 0)
  proof: by
  simpa only [mul_comm] using Real.map_volume_mul_left h

@[simp]

中文:
定理 map_volume_mul_right
  条件: {a : 实数} (h : a != 0)
  证明: by
  simpa only [mul_comm] using Real.map_volume_mul_left h

@[simp]

Depends on / 依赖: Real.map_volume_mul_left, map_volume_mul_left, mul_comm
-/
theorem map_volume_mul_right {a : Real} (h : a != 0) :
    Measure.map (· * a) volume = ENNReal.ofReal |a⁻¹| • volume := by
  simpa only [mul_comm] using Real.map_volume_mul_left h

@[simp]
/--
theorem `volume_preimage_mul_right` / 定理 `volume_preimage_mul_right`

English:
theorem volume_preimage_mul_right
  given: {a : Real} (h : a != 0) (s : Set Real)
  proof: calc
    volume ((· * a) ⁻¹' s) = Measure.map (· * a) volume s :=
      ((Homeomorph.mulRight₀ a h).toMeasurableEquiv.map_apply s).symm
    _ = ENNReal.ofReal (abs a⁻¹) * volume s := by rw [map_volume_mul_right h]; rfl

中文:
定理 volume_preimage_mul_right
  条件: {a : 实数} (h : a != 0) (s : 集合 实数)
  证明: calc
    volume ((· * a) ⁻¹' s) = Measure.map (· * a) volume s :=
      ((Homeomorph.mulRight₀ a h).toMeasurableEquiv.map_apply s).symm
    _ = ENNReal.ofReal (abs a⁻¹) * volume s := by rw [map_volume_mul_right h]; rfl

Depends on / 依赖: ENNReal, ENNReal.ofReal, Homeomorph, Homeomorph.mulRight, Measure, Measure.map, map_apply, map_volume_mul_right, ofReal, toMeasurableEquiv, toMeasurableEquiv.map_apply, volume
-/
theorem volume_preimage_mul_right {a : Real} (h : a != 0) (s : Set Real) :
    volume ((· * a) ⁻¹' s) = ENNReal.ofReal (abs a⁻¹) * volume s :=
  calc
    volume ((· * a) ⁻¹' s) = Measure.map (· * a) volume s :=
      ((Homeomorph.mulRight₀ a h).toMeasurableEquiv.map_apply s).symm
    _ = ENNReal.ofReal (abs a⁻¹) * volume s := by rw [map_volume_mul_right h]; rfl

/-!
### Images of the Lebesgue measure under translation/linear maps in ℝⁿ
-/


open Matrix

/--
theorem `smul_map_diagonal_volume_pi` / 定理 `smul_map_diagonal_volume_pi`

English:
theorem smul_map_diagonal_volume_pi
  given: [DecidableEq ι] {D : ι -> Real} (h : det (diagonal D) != 0)
  proof: by
  refine (Measure.pi_eq fun s hs => ?_).symm
  simp only [det_diagonal, Measure.coe_smul, smul_eq_mul, Pi.smul_apply]
  rw [Measure.map_apply _ (MeasurableSet.univ_pi hs)]
  swap; · exact Continuous.measurable (LinearMap.continuous_on_pi _)
  have :
    (Matrix.toLin' (diagonal D) ⁻¹' Set.pi Set.univ fun i : ι => s i) =
      Set.pi Set.univ fun i : ι => (D i * ·) ⁻¹' s i := by
    ext f
    simp only [LinearMap.coe_proj, smul_eq_mul, LinearMap.smul_apply, mem_univ_pi,
      mem_preimage, LinearMap.pi_apply, diagonal_toLin']
  have B : forall i, ofReal (abs (D i)) * volume ((D i * ·) ⁻¹' s i) = volume (s i) := by
    intro i
    have A : D i != 0 := by
      simp only [det_diagonal, Ne] at h
      exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)
    rw [volume_preimage_mul_left A]; rw [← mul_assoc]; rw [← ENNReal.ofReal_mul (abs_nonneg _)]; rw [← abs_mul]; rw [mul_inv_cancel₀ A]; rw [abs_one]; rw [ENNReal.ofReal_one]; rw [one_mul]
  rw [this]; rw [volume_pi_pi]; rw [Finset.abs_prod]; rw [ENNReal.ofReal_prod_of_nonneg fun i _ => abs_nonneg (D i)]; rw [← Finset.prod_mul_distrib]
  simp only [B]

中文:
定理 smul_map_diagonal_volume_pi
  条件: [DecidableEq ι] {D : ι -> 实数} (h : det (diagonal D) != 0)
  证明: by
  refine (Measure.pi_eq fun s hs => ?_).symm
  simp only [det_diagonal, Measure.coe_smul, smul_eq_mul, Pi.smul_apply]
  rw [Measure.map_apply _ (MeasurableSet.univ_pi hs)]
  swap; · exact Continuous.measurable (LinearMap.continuous_on_pi _)
  have :
    (Matrix.toLin' (diagonal D) ⁻¹' Set.pi Set.univ fun i : ι => s i) =
      Set.pi Set.univ fun i : ι => (D i * ·) ⁻¹' s i := by
    ext f
    simp only [LinearMap.coe_proj, smul_eq_mul, LinearMap.smul_apply, mem_univ_pi,
      mem_preimage, LinearMap.pi_apply, diagonal_toLin']
  have B : forall i, ofReal (abs (D i)) * volume ((D i * ·) ⁻¹' s i) = volume (s i) := by
    intro i
    have A : D i != 0 := by
      simp only [det_diagonal, Ne] at h
      exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)
    rw [volume_preimage_mul_left A]; rw [← mul_assoc]; rw [← ENNReal.ofReal_mul (abs_nonneg _)]; rw [← abs_mul]; rw [mul_inv_cancel₀ A]; rw [abs_one]; rw [ENNReal.ofReal_one]; rw [one_mul]
  rw [this]; rw [volume_pi_pi]; rw [Finset.abs_prod]; rw [ENNReal.ofReal_prod_of_nonneg fun i _ => abs_nonneg (D i)]; rw [← Finset.prod_mul_distrib]
  simp only [B]

Depends on / 依赖: Continuous, Continuous.measurable, LinearMap, LinearMap.coe_proj, LinearMap.continuous_on_pi, LinearMap.pi_apply, LinearMap.smul_apply, Matrix, Matrix.toLin, MeasurableSet, MeasurableSet.univ_pi, Measure, Measure.coe_smul, Measure.map_apply, Measure.pi_eq, Pi.smul_apply, Set.pi, Set.univ, coe_proj, coe_smul
-/
theorem smul_map_diagonal_volume_pi [DecidableEq ι] {D : ι -> Real} (h : det (diagonal D) != 0) :
    ENNReal.ofReal (abs (det (diagonal D))) • Measure.map (toLin' (diagonal D)) volume =
      volume := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  simp only [det_diagonal, Measure.coe_smul, smul_eq_mul, Pi.smul_apply]
  rw [Measure.map_apply _ (MeasurableSet.univ_pi hs)]
  swap; · exact Continuous.measurable (LinearMap.continuous_on_pi _)
  have :
    (Matrix.toLin' (diagonal D) ⁻¹' Set.pi Set.univ fun i : ι => s i) =
      Set.pi Set.univ fun i : ι => (D i * ·) ⁻¹' s i := by
    ext f
    simp only [LinearMap.coe_proj, smul_eq_mul, LinearMap.smul_apply, mem_univ_pi,
      mem_preimage, LinearMap.pi_apply, diagonal_toLin']
  have B : forall i, ofReal (abs (D i)) * volume ((D i * ·) ⁻¹' s i) = volume (s i) := by
    intro i
    have A : D i != 0 := by
      simp only [det_diagonal, Ne] at h
      exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)
    rw [volume_preimage_mul_left A]; rw [← mul_assoc]; rw [← ENNReal.ofReal_mul (abs_nonneg _)]; rw [← abs_mul]; rw [mul_inv_cancel₀ A]; rw [abs_one]; rw [ENNReal.ofReal_one]; rw [one_mul]
  rw [this]; rw [volume_pi_pi]; rw [Finset.abs_prod]; rw [ENNReal.ofReal_prod_of_nonneg fun i _ => abs_nonneg (D i)]; rw [← Finset.prod_mul_distrib]
  simp only [B]

/--
theorem `volume_preserving_transvectionStruct` / 定理 `volume_preserving_transvectionStruct`

English:
theorem volume_preserving_transvectionStruct
  given: [DecidableEq ι] (t : TransvectionStruct ι Real)
  proof: by
  /- We use `lmarginal` to conveniently use Fubini's theorem.
    Along the coordinate where there is a shearing, it acts like a
    translation, and therefore preserves Lebesgue. -/
  have ht : Measurable (toLin' t.toMatrix) :=
    (toLin' t.toMatrix).continuous_of_finiteDimensional.measurable
  refine ⟨ht, ?_⟩
  refine (pi_eq fun s hs => ?_).symm
  have h2s : MeasurableSet (univ.pi s) := .pi countable_univ fun i _ => hs i
  simp_rw [← pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]; rw [volume_pi]
  refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  cases t with | mk t_i t_j t_hij t_c =>
  simp [transvection, single_mulVec, t_hij.symm, ← Function.update_add,
    lintegral_add_right_eq_self fun xᵢ => indicator (univ.pi s) 1 (Function.update x t_i xᵢ)]

中文:
定理 volume_preserving_transvectionStruct
  条件: [DecidableEq ι] (t : 平换结构 ι 实数)
  证明: by
  /- We use `lmarginal` to conveniently use Fubini's theorem.
    Along the coordinate where there is a shearing, it acts like a
    translation, and therefore preserves Lebesgue. -/
  have ht : Measurable (toLin' t.toMatrix) :=
    (toLin' t.toMatrix).continuous_of_finiteDimensional.measurable
  refine ⟨ht, ?_⟩
  refine (pi_eq fun s hs => ?_).symm
  have h2s : MeasurableSet (univ.pi s) := .pi countable_univ fun i _ => hs i
  simp_rw [← pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]; rw [volume_pi]
  refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  cases t with | mk t_i t_j t_hij t_c =>
  simp [transvection, single_mulVec, t_hij.symm, ← Function.update_add,
    lintegral_add_right_eq_self fun xᵢ => indicator (univ.pi s) 1 (Function.update x t_i xᵢ)]
-/
theorem volume_preserving_transvectionStruct [DecidableEq ι] (t : TransvectionStruct ι Real) :
    MeasurePreserving (toLin' t.toMatrix) := by
  /- We use `lmarginal` to conveniently use Fubini's theorem.
    Along the coordinate where there is a shearing, it acts like a
    translation, and therefore preserves Lebesgue. -/
  have ht : Measurable (toLin' t.toMatrix) :=
    (toLin' t.toMatrix).continuous_of_finiteDimensional.measurable
  refine ⟨ht, ?_⟩
  refine (pi_eq fun s hs => ?_).symm
  have h2s : MeasurableSet (univ.pi s) := .pi countable_univ fun i _ => hs i
  simp_rw [← pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]; rw [volume_pi]
  refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  cases t with | mk t_i t_j t_hij t_c =>
  simp [transvection, single_mulVec, t_hij.symm, ← Function.update_add,
    lintegral_add_right_eq_self fun xᵢ => indicator (univ.pi s) 1 (Function.update x t_i xᵢ)]

/--
theorem `map_matrix_volume_pi_eq_smul_volume_pi` / 定理 `map_matrix_volume_pi_eq_smul_volume_pi`

English:
theorem map_matrix_volume_pi_eq_smul_volume_pi
  given: [DecidableEq ι] {M : Matrix ι ι Real} (hM : det M != 0)
  proof: by
  -- This follows from the cases we have already proved, of diagonal matrices and transvections,
  -- as these matrices generate all invertible matrices.
  apply diagonal_transvection_induction_of_det_ne_zero _ M hM
  · intro D hD
    conv_rhs => rw [← smul_map_diagonal_volume_pi hD]
    rw [smul_smul]; rw [← ENNReal.ofReal_mul (abs_nonneg _)]; rw [← abs_mul]; rw [inv_mul_cancel₀ hD]; rw [abs_one]; rw [ENNReal.ofReal_one]; rw [one_smul]
  · intro t
    simp_rw [Matrix.TransvectionStruct.det, _root_.inv_one, abs_one, ENNReal.ofReal_one, one_smul,
      (volume_preserving_transvectionStruct _).map_eq]
  · intro A B _ _ IHA IHB
    rw [toLin'_mul]; rw [det_mul]; rw [LinearMap.coe_comp]; rw [← Measure.map_map]; rw [IHB]; rw [Measure.map_smul]; rw [IHA]; rw [smul_smul]; rw [← ENNReal.ofReal_mul (abs_nonneg _)]; rw [← abs_mul]; rw [mul_comm]; rw [mul_inv]
    · apply Continuous.measurable
      apply LinearMap.continuous_on_pi
    · apply Continuous.measurable
      apply LinearMap.continuous_on_pi

中文:
定理 map_matrix_volume_pi_eq_smul_volume_pi
  条件: [DecidableEq ι] {M : 矩阵 ι ι 实数} (hM : det M != 0)
  证明: by
  -- This follows from the cases we have already proved, of diagonal matrices and transvections,
  -- as these matrices generate all invertible matrices.
  apply diagonal_transvection_induction_of_det_ne_zero _ M hM
  · intro D hD
    conv_rhs => rw [← smul_map_diagonal_volume_pi hD]
    rw [smul_smul]; rw [← ENNReal.ofReal_mul (abs_nonneg _)]; rw [← abs_mul]; rw [inv_mul_cancel₀ hD]; rw [abs_one]; rw [ENNReal.ofReal_one]; rw [one_smul]
  · intro t
    simp_rw [Matrix.TransvectionStruct.det, _root_.inv_one, abs_one, ENNReal.ofReal_one, one_smul,
      (volume_preserving_transvectionStruct _).map_eq]
  · intro A B _ _ IHA IHB
    rw [toLin'_mul]; rw [det_mul]; rw [LinearMap.coe_comp]; rw [← Measure.map_map]; rw [IHB]; rw [Measure.map_smul]; rw [IHA]; rw [smul_smul]; rw [← ENNReal.ofReal_mul (abs_nonneg _)]; rw [← abs_mul]; rw [mul_comm]; rw [mul_inv]
    · apply Continuous.measurable
      apply LinearMap.continuous_on_pi
    · apply Continuous.measurable
      apply LinearMap.continuous_on_pi
-/
theorem map_matrix_volume_pi_eq_smul_volume_pi [DecidableEq ι] {M : Matrix ι ι Real} (hM : det M != 0) :
    Measure.map (toLin' M) volume = ENNReal.ofReal (abs (det M)⁻¹) • volume := by
  -- This follows from the cases we have already proved, of diagonal matrices and transvections,
  -- as these matrices generate all invertible matrices.
  apply diagonal_transvection_induction_of_det_ne_zero _ M hM
  · intro D hD
    conv_rhs => rw [← smul_map_diagonal_volume_pi hD]
    rw [smul_smul]; rw [← ENNReal.ofReal_mul (abs_nonneg _)]; rw [← abs_mul]; rw [inv_mul_cancel₀ hD]; rw [abs_one]; rw [ENNReal.ofReal_one]; rw [one_smul]
  · intro t
    simp_rw [Matrix.TransvectionStruct.det, _root_.inv_one, abs_one, ENNReal.ofReal_one, one_smul,
      (volume_preserving_transvectionStruct _).map_eq]
  · intro A B _ _ IHA IHB
    rw [toLin'_mul]; rw [det_mul]; rw [LinearMap.coe_comp]; rw [← Measure.map_map]; rw [IHB]; rw [Measure.map_smul]; rw [IHA]; rw [smul_smul]; rw [← ENNReal.ofReal_mul (abs_nonneg _)]; rw [← abs_mul]; rw [mul_comm]; rw [mul_inv]
    · apply Continuous.measurable
      apply LinearMap.continuous_on_pi
    · apply Continuous.measurable
      apply LinearMap.continuous_on_pi

/--
theorem `map_linearMap_volume_pi_eq_smul_volume_pi` / 定理 `map_linearMap_volume_pi_eq_smul_volume_pi`

English:
theorem map_linearMap_volume_pi_eq_smul_volume_pi
  statement: {f : (ι -> Real) ->ₗ[Real] ι -> Real}
  proof: by
  classical
    -- this is deduced from the matrix case
    let M := LinearMap.toMatrix' f
    have A : LinearMap.det f = det M := by simp only [M, LinearMap.det_toMatrix']
    have B : f = toLin' M := by simp only [M, toLin'_toMatrix']
    rw [A]; rw [B]
    apply map_matrix_volume_pi_eq_smul_volume_pi
    rwa [A] at hf

中文:
定理 map_linearMap_volume_pi_eq_smul_volume_pi
  结论: {f : (ι -> 实数) ->ₗ[实数] ι -> 实数}
  证明: by
  classical
    -- this is deduced from the matrix case
    let M := LinearMap.toMatrix' f
    have A : LinearMap.det f = det M := by simp only [M, LinearMap.det_toMatrix']
    have B : f = toLin' M := by simp only [M, toLin'_toMatrix']
    rw [A]; rw [B]
    apply map_matrix_volume_pi_eq_smul_volume_pi
    rwa [A] at hf

Depends on / 依赖: classical
-/
theorem map_linearMap_volume_pi_eq_smul_volume_pi {f : (ι -> Real) ->ₗ[Real] ι -> Real}
    (hf : LinearMap.det f != 0) : Measure.map f volume =
      ENNReal.ofReal (abs (LinearMap.det f)⁻¹) • volume := by
  classical
    -- this is deduced from the matrix case
    let M := LinearMap.toMatrix' f
    have A : LinearMap.det f = det M := by simp only [M, LinearMap.det_toMatrix']
    have B : f = toLin' M := by simp only [M, toLin'_toMatrix']
    rw [A]; rw [B]
    apply map_matrix_volume_pi_eq_smul_volume_pi
    rwa [A] at hf

end Real

section regionBetween

variable {α : Type*}

/--
Definition of `regionBetween` / `regionBetween` 的定义

English:
definition regionBetween
  signature: (f g : α -> Real) (s : Set α)
  body: { p : α × Real | p.1 in s ∧ p.2 in Ioo (f p.1) (g p.1) }

中文:
定义 regionBetween
  签名: (f g : α -> 实数) (s : 集合 α)
  定义体: { p : α × Real | p.1 in s ∧ p.2 in Ioo (f p.1) (g p.1) }
-/
def regionBetween (f g : α -> Real) (s : Set α) : Set (α × Real) :=
  { p : α × Real | p.1 in s ∧ p.2 in Ioo (f p.1) (g p.1) }

/--
theorem `regionBetween_subset` / 定理 `regionBetween_subset`

English:
theorem regionBetween_subset
  given: (f g : α -> Real) (s : Set α)
  statement: regionBetween f g s subseteq s ×ˢ univ
  proof: by
  simpa only [prod_univ, regionBetween, Set.preimage, ofPred_subset_ofPred] using fun a => And.left

中文:
定理 regionBetween_subset
  条件: (f g : α -> 实数) (s : 集合 α)
  结论: regionBetween f g s subseteq s ×ˢ univ
  证明: by
  simpa only [prod_univ, regionBetween, Set.preimage, ofPred_subset_ofPred] using fun a => And.left

Depends on / 依赖: And.left, Set.preimage, ofPred_subset_ofPred, preimage, prod_univ, regionBetween
-/
theorem regionBetween_subset (f g : α -> Real) (s : Set α) : regionBetween f g s subseteq s ×ˢ univ := by
  simpa only [prod_univ, regionBetween, Set.preimage, ofPred_subset_ofPred] using fun a => And.left

variable [MeasurableSpace α] {μ : Measure α} {f g : α -> Real} {s : Set α}

/--
theorem `measurableSet_regionBetween` / 定理 `measurableSet_regionBetween`

English:
theorem measurableSet_regionBetween
  given: (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s)
  proof: by
  dsimp only [regionBetween, Ioo, mem_ofPred_eq, ofPred_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_lt (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

中文:
定理 measurableSet_regionBetween
  条件: (hf : 可测 f) (hg : 可测 g) (hs : 可测集 s)
  证明: by
  dsimp only [regionBetween, Ioo, mem_ofPred_eq, ofPred_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_lt (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

Depends on / 依赖: MeasurableSet, MeasurableSet.inter, hf.comp, hg.comp, measurableSet_lt, measurable_fst, measurable_snd, mem_ofPred_eq, ofPred_and, regionBetween
-/
theorem measurableSet_regionBetween (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    MeasurableSet (regionBetween f g s) := by
  dsimp only [regionBetween, Ioo, mem_ofPred_eq, ofPred_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_lt (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

/--
theorem `measurableSet_region_between_oc` / 定理 `measurableSet_region_between_oc`

English:
theorem measurableSet_region_between_oc
  statement: (hf : Measurable f) (hg : Measurable g)
  proof: by
  dsimp only [regionBetween, Ioc, mem_ofPred_eq, ofPred_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_lt (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

中文:
定理 measurableSet_region_between_oc
  结论: (hf : 可测 f) (hg : 可测 g)
  证明: by
  dsimp only [regionBetween, Ioc, mem_ofPred_eq, ofPred_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_lt (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

Depends on / 依赖: MeasurableSet, MeasurableSet.inter, hf.comp, hg.comp, measurableSet_le, measurableSet_lt, measurable_fst, measurable_snd, mem_ofPred_eq, ofPred_and, regionBetween
-/
theorem measurableSet_region_between_oc (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    MeasurableSet { p : α × Real | p.fst in s ∧ p.snd in Ioc (f p.fst) (g p.fst) } := by
  dsimp only [regionBetween, Ioc, mem_ofPred_eq, ofPred_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_lt (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

/--
theorem `measurableSet_region_between_co` / 定理 `measurableSet_region_between_co`

English:
theorem measurableSet_region_between_co
  statement: (hf : Measurable f) (hg : Measurable g)
  proof: by
  dsimp only [regionBetween, Ico, mem_ofPred_eq, ofPred_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_le (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

中文:
定理 measurableSet_region_between_co
  结论: (hf : 可测 f) (hg : 可测 g)
  证明: by
  dsimp only [regionBetween, Ico, mem_ofPred_eq, ofPred_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_le (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

Depends on / 依赖: MeasurableSet, MeasurableSet.inter, hf.comp, hg.comp, measurableSet_le, measurableSet_lt, measurable_fst, measurable_snd, mem_ofPred_eq, ofPred_and, regionBetween
-/
theorem measurableSet_region_between_co (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    MeasurableSet { p : α × Real | p.fst in s ∧ p.snd in Ico (f p.fst) (g p.fst) } := by
  dsimp only [regionBetween, Ico, mem_ofPred_eq, ofPred_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_le (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

/--
theorem `measurableSet_region_between_cc` / 定理 `measurableSet_region_between_cc`

English:
theorem measurableSet_region_between_cc
  statement: (hf : Measurable f) (hg : Measurable g)
  proof: by
  dsimp only [regionBetween, Icc, mem_ofPred_eq, ofPred_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_le (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

中文:
定理 measurableSet_region_between_cc
  结论: (hf : 可测 f) (hg : 可测 g)
  证明: by
  dsimp only [regionBetween, Icc, mem_ofPred_eq, ofPred_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_le (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

Depends on / 依赖: MeasurableSet, MeasurableSet.inter, hf.comp, hg.comp, measurableSet_le, measurable_fst, measurable_snd, mem_ofPred_eq, ofPred_and, regionBetween
-/
theorem measurableSet_region_between_cc (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    MeasurableSet { p : α × Real | p.fst in s ∧ p.snd in Icc (f p.fst) (g p.fst) } := by
  dsimp only [regionBetween, Icc, mem_ofPred_eq, ofPred_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_le (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

/--
theorem `measurableSet_graph` / 定理 `measurableSet_graph`

English:
theorem measurableSet_graph
  given: (hf : Measurable f)
  proof: by
  simpa using measurableSet_region_between_cc hf hf MeasurableSet.univ

中文:
定理 measurableSet_graph
  条件: (hf : 可测 f)
  证明: by
  simpa using measurableSet_region_between_cc hf hf MeasurableSet.univ

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, measurableSet_region_between_cc
-/
theorem measurableSet_graph (hf : Measurable f) :
    MeasurableSet { p : α × Real | p.snd = f p.fst } := by
  simpa using measurableSet_region_between_cc hf hf MeasurableSet.univ

/--
theorem `volume_regionBetween_eq_lintegral'` / 定理 `volume_regionBetween_eq_lintegral'`

English:
theorem volume_regionBetween_eq_lintegral'
  statement: (hf : Measurable f) (hg : Measurable g)
  proof: by
  classical
    rw [Measure.prod_apply]
    · have h :
        (fun x => volume { a | x in s ∧ a in Ioo (f x) (g x) }) =
          s.indicator fun x => ENNReal.ofReal (g x - f x) := by
        funext x
        rw [indicator_apply]
        split_ifs with h
        · have hx : { a | x in s ∧ a in Ioo (f x) (g x) } = Ioo (f x) (g x) := by simp [h, Ioo]
          simp only [hx, Real.volume_Ioo]
        · have hx : { a | x in s ∧ a in Ioo (f x) (g x) } = ∅ := by simp [h]
          simp only [hx, measure_empty]
      dsimp only [regionBetween, preimage_ofPred_eq]
      rw [h]; rw [lintegral_indicator] <;> simp only [hs, Pi.sub_apply]
    · exact measurableSet_regionBetween hf hg hs

中文:
定理 volume_regionBetween_eq_lintegral'
  结论: (hf : 可测 f) (hg : 可测 g)
  证明: by
  classical
    rw [Measure.prod_apply]
    · have h :
        (fun x => volume { a | x in s ∧ a in Ioo (f x) (g x) }) =
          s.indicator fun x => ENNReal.ofReal (g x - f x) := by
        funext x
        rw [indicator_apply]
        split_ifs with h
        · have hx : { a | x in s ∧ a in Ioo (f x) (g x) } = Ioo (f x) (g x) := by simp [h, Ioo]
          simp only [hx, Real.volume_Ioo]
        · have hx : { a | x in s ∧ a in Ioo (f x) (g x) } = ∅ := by simp [h]
          simp only [hx, measure_empty]
      dsimp only [regionBetween, preimage_ofPred_eq]
      rw [h]; rw [lintegral_indicator] <;> simp only [hs, Pi.sub_apply]
    · exact measurableSet_regionBetween hf hg hs

Depends on / 依赖: ENNReal, ENNReal.ofReal, Measure, Measure.prod_apply, Real.volume_Ioo, classical, indicator, indicator_apply, lintegral_indic, measure_empty, ofReal, preimage_ofPred_eq, prod_apply, regionBetween, s.indicator, split_ifs, volume, volume_Ioo
-/
theorem volume_regionBetween_eq_lintegral' (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    μ.prod volume (regionBetween f g s) = ∫⁻ y in s, ENNReal.ofReal ((g - f) y) ∂μ := by
  classical
    rw [Measure.prod_apply]
    · have h :
        (fun x => volume { a | x in s ∧ a in Ioo (f x) (g x) }) =
          s.indicator fun x => ENNReal.ofReal (g x - f x) := by
        funext x
        rw [indicator_apply]
        split_ifs with h
        · have hx : { a | x in s ∧ a in Ioo (f x) (g x) } = Ioo (f x) (g x) := by simp [h, Ioo]
          simp only [hx, Real.volume_Ioo]
        · have hx : { a | x in s ∧ a in Ioo (f x) (g x) } = ∅ := by simp [h]
          simp only [hx, measure_empty]
      dsimp only [regionBetween, preimage_ofPred_eq]
      rw [h]; rw [lintegral_indicator] <;> simp only [hs, Pi.sub_apply]
    · exact measurableSet_regionBetween hf hg hs

/--
theorem `volume_regionBetween_eq_lintegral` / 定理 `volume_regionBetween_eq_lintegral`

English:
theorem volume_regionBetween_eq_lintegral
  statement: [SFinite μ] (hf : AEMeasurable f (μ.restrict s))
  proof: by
  have h₁ :
    (fun y => ENNReal.ofReal ((g - f) y)) =ᵐ[μ.restrict s] fun y =>
      ENNReal.ofReal ((AEMeasurable.mk g hg - AEMeasurable.mk f hf) y) :=
    (hg.ae_eq_mk.sub hf.ae_eq_mk).fun_comp ENNReal.ofReal
  have h₂ :
    (μ.restrict s).prod volume (regionBetween f g s) =
      (μ.restrict s).prod volume
        (regionBetween (AEMeasurable.mk f hf) (AEMeasurable.mk g hg) s) := by
    apply measure_congr
    apply EventuallyEq.rfl.inter
    exact
      ((quasiMeasurePreserving_fst.ae_eq_comp hf.ae_eq_mk).comp₂ _ EventuallyEq.rfl).inter
        (EventuallyEq.rfl.comp₂ _ <| quasiMeasurePreserving_fst.ae_eq_comp hg.ae_eq_mk)
  rw [lintegral_congr_ae h₁]; rw [←
    volume_regionBetween_eq_lintegral' hf.measurable_mk hg.measurable_mk hs]
  convert! h₂ using 1
  · rw [Measure.restrict_prod_eq_prod_univ]
    exact (Measure.restrict_eq_self _ (regionBetween_subset f g s)).symm
  · rw [Measure.restrict_prod_eq_prod_univ]
    exact
      (Measure.restrict_eq_self _
          (regionBetween_subset (AEMeasurable.mk f hf) (AEMeasurable.mk g hg) s)).symm

中文:
定理 volume_regionBetween_eq_lintegral
  结论: [SFinite μ] (hf : 几乎处处可测 f (μ.restrict s))
  证明: by
  have h₁ :
    (fun y => ENNReal.ofReal ((g - f) y)) =ᵐ[μ.restrict s] fun y =>
      ENNReal.ofReal ((AEMeasurable.mk g hg - AEMeasurable.mk f hf) y) :=
    (hg.ae_eq_mk.sub hf.ae_eq_mk).fun_comp ENNReal.ofReal
  have h₂ :
    (μ.restrict s).prod volume (regionBetween f g s) =
      (μ.restrict s).prod volume
        (regionBetween (AEMeasurable.mk f hf) (AEMeasurable.mk g hg) s) := by
    apply measure_congr
    apply EventuallyEq.rfl.inter
    exact
      ((quasiMeasurePreserving_fst.ae_eq_comp hf.ae_eq_mk).comp₂ _ EventuallyEq.rfl).inter
        (EventuallyEq.rfl.comp₂ _ <| quasiMeasurePreserving_fst.ae_eq_comp hg.ae_eq_mk)
  rw [lintegral_congr_ae h₁]; rw [←
    volume_regionBetween_eq_lintegral' hf.measurable_mk hg.measurable_mk hs]
  convert! h₂ using 1
  · rw [Measure.restrict_prod_eq_prod_univ]
    exact (Measure.restrict_eq_self _ (regionBetween_subset f g s)).symm
  · rw [Measure.restrict_prod_eq_prod_univ]
    exact
      (Measure.restrict_eq_self _
          (regionBetween_subset (AEMeasurable.mk f hf) (AEMeasurable.mk g hg) s)).symm

Depends on / 依赖: AEMeasurable, AEMeasurable.mk, ENNReal, ENNReal.ofReal, EventuallyEq, EventuallyEq.rfl, EventuallyEq.rfl.inter, ae_eq_comp, ae_eq_mk, fun_comp, hf.ae_eq_mk, hg.ae_eq_mk.sub, measure_congr, ofReal, quasiMeasurePreserving_fst, quasiMeasurePreserving_fst.ae_eq_comp, regionBetween, restrict, volume
-/
theorem volume_regionBetween_eq_lintegral [SFinite μ] (hf : AEMeasurable f (μ.restrict s))
    (hg : AEMeasurable g (μ.restrict s)) (hs : MeasurableSet s) :
    μ.prod volume (regionBetween f g s) = ∫⁻ y in s, ENNReal.ofReal ((g - f) y) ∂μ := by
  have h₁ :
    (fun y => ENNReal.ofReal ((g - f) y)) =ᵐ[μ.restrict s] fun y =>
      ENNReal.ofReal ((AEMeasurable.mk g hg - AEMeasurable.mk f hf) y) :=
    (hg.ae_eq_mk.sub hf.ae_eq_mk).fun_comp ENNReal.ofReal
  have h₂ :
    (μ.restrict s).prod volume (regionBetween f g s) =
      (μ.restrict s).prod volume
        (regionBetween (AEMeasurable.mk f hf) (AEMeasurable.mk g hg) s) := by
    apply measure_congr
    apply EventuallyEq.rfl.inter
    exact
      ((quasiMeasurePreserving_fst.ae_eq_comp hf.ae_eq_mk).comp₂ _ EventuallyEq.rfl).inter
        (EventuallyEq.rfl.comp₂ _ <| quasiMeasurePreserving_fst.ae_eq_comp hg.ae_eq_mk)
  rw [lintegral_congr_ae h₁]; rw [←
    volume_regionBetween_eq_lintegral' hf.measurable_mk hg.measurable_mk hs]
  convert! h₂ using 1
  · rw [Measure.restrict_prod_eq_prod_univ]
    exact (Measure.restrict_eq_self _ (regionBetween_subset f g s)).symm
  · rw [Measure.restrict_prod_eq_prod_univ]
    exact
      (Measure.restrict_eq_self _
          (regionBetween_subset (AEMeasurable.mk f hf) (AEMeasurable.mk g hg) s)).symm

/--
lemma `nullMeasurableSet_regionBetween` / 引理 `nullMeasurableSet_regionBetween`

English:
lemma nullMeasurableSet_regionBetween
  statement: (μ : Measure α)
  proof: by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · exact nullMeasurableSet_lt (by fun_prop) measurable_snd.aemeasurable
  · exact nullMeasurableSet_lt measurable_snd.aemeasurable (by fun_prop)

中文:
引理 nullMeasurableSet_regionBetween
  结论: (μ : 测度 α)
  证明: by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · exact nullMeasurableSet_lt (by fun_prop) measurable_snd.aemeasurable
  · exact nullMeasurableSet_lt measurable_snd.aemeasurable (by fun_prop)

Depends on / 依赖: NullMeasurableSet, NullMeasurableSet.inter, aemeasurable, fun_prop, measurable_snd, measurable_snd.aemeasurable, nullMeasurableSet_lt, preimage, quasiMeasurePreserving_fst, s_mble, s_mble.preimage
-/
lemma nullMeasurableSet_regionBetween (μ : Measure α)
    {f g : α -> Real} (f_mble : AEMeasurable f μ) (g_mble : AEMeasurable g μ)
    {s : Set α} (s_mble : NullMeasurableSet s μ) :
    NullMeasurableSet {p : α × Real | p.1 in s ∧ p.snd in Ioo (f p.fst) (g p.fst)} (μ.prod volume) := by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · exact nullMeasurableSet_lt (by fun_prop) measurable_snd.aemeasurable
  · exact nullMeasurableSet_lt measurable_snd.aemeasurable (by fun_prop)

/--
lemma `nullMeasurableSet_region_between_oc` / 引理 `nullMeasurableSet_region_between_oc`

English:
lemma nullMeasurableSet_region_between_oc
  statement: (μ : Measure α)
  proof: by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · exact nullMeasurableSet_lt (by fun_prop) measurable_snd.aemeasurable
  · change NullMeasurableSet {p : α × Real | p.snd <= g p.fst} (μ.prod volume)
    rw [show {p : α × Real | p.snd <= g p.fst} = {p : α × Real | g p.fst < p.snd}ᶜ by
          ext p
          simp]
    exact (nullMeasurableSet_lt (by fun_prop) measurable_snd.aemeasurable).compl

中文:
引理 nullMeasurableSet_region_between_oc
  结论: (μ : 测度 α)
  证明: by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · exact nullMeasurableSet_lt (by fun_prop) measurable_snd.aemeasurable
  · change NullMeasurableSet {p : α × Real | p.snd <= g p.fst} (μ.prod volume)
    rw [show {p : α × Real | p.snd <= g p.fst} = {p : α × Real | g p.fst < p.snd}ᶜ by
          ext p
          simp]
    exact (nullMeasurableSet_lt (by fun_prop) measurable_snd.aemeasurable).compl

Depends on / 依赖: NullMeasurableSet, NullMeasurableSet.inter, aemeasurable, fun_prop, measurable_snd, measurable_snd.aemeasurable, nullMeasurableSet_lt, p.fst, p.snd, preimage, quasiMeasurePreserving_fst, s_mble, s_mble.preimage, volume
-/
lemma nullMeasurableSet_region_between_oc (μ : Measure α)
    {f g : α -> Real} (f_mble : AEMeasurable f μ) (g_mble : AEMeasurable g μ)
    {s : Set α} (s_mble : NullMeasurableSet s μ) :
    NullMeasurableSet {p : α × Real | p.1 in s ∧ p.snd in Ioc (f p.fst) (g p.fst)} (μ.prod volume) := by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · exact nullMeasurableSet_lt (by fun_prop) measurable_snd.aemeasurable
  · change NullMeasurableSet {p : α × Real | p.snd <= g p.fst} (μ.prod volume)
    rw [show {p : α × Real | p.snd <= g p.fst} = {p : α × Real | g p.fst < p.snd}ᶜ by
          ext p
          simp]
    exact (nullMeasurableSet_lt (by fun_prop) measurable_snd.aemeasurable).compl

/--
lemma `nullMeasurableSet_region_between_co` / 引理 `nullMeasurableSet_region_between_co`

English:
lemma nullMeasurableSet_region_between_co
  statement: (μ : Measure α)
  proof: by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · change NullMeasurableSet {p : α × Real | f p.fst <= p.snd} (μ.prod volume)
    rw [show {p : α × Real | f p.fst <= p.snd} = {p : α × Real | p.snd < f p.fst}ᶜ by
          ext p
          simp]
    exact (nullMeasurableSet_lt measurable_snd.aemeasurable (by fun_prop)).compl
  · exact nullMeasurableSet_lt measurable_snd.aemeasurable (by fun_prop)

中文:
引理 nullMeasurableSet_region_between_co
  结论: (μ : 测度 α)
  证明: by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · change NullMeasurableSet {p : α × Real | f p.fst <= p.snd} (μ.prod volume)
    rw [show {p : α × Real | f p.fst <= p.snd} = {p : α × Real | p.snd < f p.fst}ᶜ by
          ext p
          simp]
    exact (nullMeasurableSet_lt measurable_snd.aemeasurable (by fun_prop)).compl
  · exact nullMeasurableSet_lt measurable_snd.aemeasurable (by fun_prop)

Depends on / 依赖: NullMeasurableSet, NullMeasurableSet.inter, aemeasurable, fun_prop, measurable_snd, measurable_snd.aemeasurable, nullMeasurableSet_lt, p.fst, p.snd, preimage, quasiMeasurePreserving_fst, s_mble, s_mble.preimage, volume
-/
lemma nullMeasurableSet_region_between_co (μ : Measure α)
    {f g : α -> Real} (f_mble : AEMeasurable f μ) (g_mble : AEMeasurable g μ)
    {s : Set α} (s_mble : NullMeasurableSet s μ) :
    NullMeasurableSet {p : α × Real | p.1 in s ∧ p.snd in Ico (f p.fst) (g p.fst)} (μ.prod volume) := by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · change NullMeasurableSet {p : α × Real | f p.fst <= p.snd} (μ.prod volume)
    rw [show {p : α × Real | f p.fst <= p.snd} = {p : α × Real | p.snd < f p.fst}ᶜ by
          ext p
          simp]
    exact (nullMeasurableSet_lt measurable_snd.aemeasurable (by fun_prop)).compl
  · exact nullMeasurableSet_lt measurable_snd.aemeasurable (by fun_prop)

/--
lemma `nullMeasurableSet_region_between_cc` / 引理 `nullMeasurableSet_region_between_cc`

English:
lemma nullMeasurableSet_region_between_cc
  statement: (μ : Measure α)
  proof: by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · change NullMeasurableSet {p : α × Real | f p.fst <= p.snd} (μ.prod volume)
    rw [show {p : α × Real | f p.fst <= p.snd} = {p : α × Real | p.snd < f p.fst}ᶜ by
          ext p
          simp]
    exact (nullMeasurableSet_lt measurable_snd.aemeasurable (by fun_prop)).compl
  · change NullMeasurableSet {p : α × Real | p.snd <= g p.fst} (μ.prod volume)
    rw [show {p : α × Real | p.snd <= g p.fst} = {p : α × Real | g p.fst < p.snd}ᶜ by
          ext p
          simp]
    exact (nullMeasurableSet_lt (by fun_prop) measurable_snd.aemeasurable).compl

中文:
引理 nullMeasurableSet_region_between_cc
  结论: (μ : 测度 α)
  证明: by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · change NullMeasurableSet {p : α × Real | f p.fst <= p.snd} (μ.prod volume)
    rw [show {p : α × Real | f p.fst <= p.snd} = {p : α × Real | p.snd < f p.fst}ᶜ by
          ext p
          simp]
    exact (nullMeasurableSet_lt measurable_snd.aemeasurable (by fun_prop)).compl
  · change NullMeasurableSet {p : α × Real | p.snd <= g p.fst} (μ.prod volume)
    rw [show {p : α × Real | p.snd <= g p.fst} = {p : α × Real | g p.fst < p.snd}ᶜ by
          ext p
          simp]
    exact (nullMeasurableSet_lt (by fun_prop) measurable_snd.aemeasurable).compl

Depends on / 依赖: NullMeasurableSet, NullMeasurableSet.inter, aemeasurable, fun_prop, measurable_snd, measurable_snd.aemeasurable, nullMeasurableSet_lt, p.fst, p.snd, preimage, quasiMeasurePreserving_fst, s_mble, s_mble.preimage, volume
-/
lemma nullMeasurableSet_region_between_cc (μ : Measure α)
    {f g : α -> Real} (f_mble : AEMeasurable f μ) (g_mble : AEMeasurable g μ)
    {s : Set α} (s_mble : NullMeasurableSet s μ) :
    NullMeasurableSet {p : α × Real | p.1 in s ∧ p.snd in Icc (f p.fst) (g p.fst)} (μ.prod volume) := by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · change NullMeasurableSet {p : α × Real | f p.fst <= p.snd} (μ.prod volume)
    rw [show {p : α × Real | f p.fst <= p.snd} = {p : α × Real | p.snd < f p.fst}ᶜ by
          ext p
          simp]
    exact (nullMeasurableSet_lt measurable_snd.aemeasurable (by fun_prop)).compl
  · change NullMeasurableSet {p : α × Real | p.snd <= g p.fst} (μ.prod volume)
    rw [show {p : α × Real | p.snd <= g p.fst} = {p : α × Real | g p.fst < p.snd}ᶜ by
          ext p
          simp]
    exact (nullMeasurableSet_lt (by fun_prop) measurable_snd.aemeasurable).compl

end regionBetween

/--
theorem `ae_restrict_of_ae_restrict_inter_Ioo` / 定理 `ae_restrict_of_ae_restrict_inter_Ioo`

English:
theorem ae_restrict_of_ae_restrict_inter_Ioo
  statement: {μ : Measure Real} [NullSingletonClass μ] {s : Set Real}
  proof: by
  /- By second-countability, we cover `s` by countably many intervals `(a, b)` (except maybe for
    two endpoints, which don't matter since `μ` does not have any atom). -/
  let T : s × s -> Set Real := fun p => Ioo p.1 p.2
  let u := ⋃ i : ↥s × ↥s, T i
  have hfinite : (s \ u).Finite := s.finite_sdiff_iUnion_Ioo'
  obtain ⟨A, A_count, hA⟩ :
    exists A : Set (↥s × ↥s), A.Countable ∧ ⋃ i in A, T i = ⋃ i : ↥s × ↥s, T i :=
    isOpen_iUnion_countable _ fun p => isOpen_Ioo
  have : s subseteq s \ u union ⋃ p in A, s inter T p := by
    intro x hx
    by_cases h'x : x in ⋃ i : ↥s × ↥s, T i
    · rw [← hA] at h'x
      obtain ⟨p, pA, xp⟩ : exists p : ↥s × ↥s, p in A ∧ x in T p := by
        simpa only [mem_iUnion, exists_prop, SetCoe.exists, exists_and_right] using h'x
      right
      exact mem_biUnion pA ⟨hx, xp⟩
    · exact Or.inl ⟨hx, h'x⟩
  apply ae_restrict_of_ae_restrict_of_subset this
  rw [ae_restrict_union_iff]; rw [ae_restrict_biUnion_iff _ A_count]
  constructor
  · have : μ.restrict (s \ u) = 0 := by simp only [restrict_eq_zero, hfinite.measure_zero]
    simp only [this, ae_zero, eventually_bot]
  · rintro ⟨⟨a, as⟩, ⟨b, bs⟩⟩ -
    dsimp [T]
    rcases le_or_gt b a with (hba | hab)
    · simp only [Ioo_eq_empty_of_le hba, inter_empty, restrict_empty, ae_zero, eventually_bot]
    · exact h a b as bs hab

中文:
定理 ae_restrict_of_ae_restrict_inter_Ioo
  结论: {μ : 测度 实数} [NullSingleton类 μ] {s : 集合 实数}
  证明: by
  /- By second-countability, we cover `s` by countably many intervals `(a, b)` (except maybe for
    two endpoints, which don't matter since `μ` does not have any atom). -/
  let T : s × s -> Set Real := fun p => Ioo p.1 p.2
  let u := ⋃ i : ↥s × ↥s, T i
  have hfinite : (s \ u).Finite := s.finite_sdiff_iUnion_Ioo'
  obtain ⟨A, A_count, hA⟩ :
    exists A : Set (↥s × ↥s), A.Countable ∧ ⋃ i in A, T i = ⋃ i : ↥s × ↥s, T i :=
    isOpen_iUnion_countable _ fun p => isOpen_Ioo
  have : s subseteq s \ u union ⋃ p in A, s inter T p := by
    intro x hx
    by_cases h'x : x in ⋃ i : ↥s × ↥s, T i
    · rw [← hA] at h'x
      obtain ⟨p, pA, xp⟩ : exists p : ↥s × ↥s, p in A ∧ x in T p := by
        simpa only [mem_iUnion, exists_prop, SetCoe.exists, exists_and_right] using h'x
      right
      exact mem_biUnion pA ⟨hx, xp⟩
    · exact Or.inl ⟨hx, h'x⟩
  apply ae_restrict_of_ae_restrict_of_subset this
  rw [ae_restrict_union_iff]; rw [ae_restrict_biUnion_iff _ A_count]
  constructor
  · have : μ.restrict (s \ u) = 0 := by simp only [restrict_eq_zero, hfinite.measure_zero]
    simp only [this, ae_zero, eventually_bot]
  · rintro ⟨⟨a, as⟩, ⟨b, bs⟩⟩ -
    dsimp [T]
    rcases le_or_gt b a with (hba | hab)
    · simp only [Ioo_eq_empty_of_le hba, inter_empty, restrict_empty, ae_zero, eventually_bot]
    · exact h a b as bs hab
-/
theorem ae_restrict_of_ae_restrict_inter_Ioo {μ : Measure Real} [NullSingletonClass μ] {s : Set Real}
    {p : Real -> Prop} (h : forall a b, a in s -> b in s -> a < b -> forallᵐ x ∂μ.restrict (s inter Ioo a b), p x) :
    forallᵐ x ∂μ.restrict s, p x := by
  /- By second-countability, we cover `s` by countably many intervals `(a, b)` (except maybe for
    two endpoints, which don't matter since `μ` does not have any atom). -/
  let T : s × s -> Set Real := fun p => Ioo p.1 p.2
  let u := ⋃ i : ↥s × ↥s, T i
  have hfinite : (s \ u).Finite := s.finite_sdiff_iUnion_Ioo'
  obtain ⟨A, A_count, hA⟩ :
    exists A : Set (↥s × ↥s), A.Countable ∧ ⋃ i in A, T i = ⋃ i : ↥s × ↥s, T i :=
    isOpen_iUnion_countable _ fun p => isOpen_Ioo
  have : s subseteq s \ u union ⋃ p in A, s inter T p := by
    intro x hx
    by_cases h'x : x in ⋃ i : ↥s × ↥s, T i
    · rw [← hA] at h'x
      obtain ⟨p, pA, xp⟩ : exists p : ↥s × ↥s, p in A ∧ x in T p := by
        simpa only [mem_iUnion, exists_prop, SetCoe.exists, exists_and_right] using h'x
      right
      exact mem_biUnion pA ⟨hx, xp⟩
    · exact Or.inl ⟨hx, h'x⟩
  apply ae_restrict_of_ae_restrict_of_subset this
  rw [ae_restrict_union_iff]; rw [ae_restrict_biUnion_iff _ A_count]
  constructor
  · have : μ.restrict (s \ u) = 0 := by simp only [restrict_eq_zero, hfinite.measure_zero]
    simp only [this, ae_zero, eventually_bot]
  · rintro ⟨⟨a, as⟩, ⟨b, bs⟩⟩ -
    dsimp [T]
    rcases le_or_gt b a with (hba | hab)
    · simp only [Ioo_eq_empty_of_le hba, inter_empty, restrict_empty, ae_zero, eventually_bot]
    · exact h a b as bs hab

/--
theorem `ae_of_mem_of_ae_of_mem_inter_Ioo` / 定理 `ae_of_mem_of_ae_of_mem_inter_Ioo`

English:
theorem ae_of_mem_of_ae_of_mem_inter_Ioo
  statement: {μ : Measure Real} [NullSingletonClass μ] {s : Set Real}
  proof: by
  /- By second-countability, we cover `s` by countably many intervals `(a, b)` (except maybe for
    two endpoints, which don't matter since `μ` does not have any atom). -/
  let T : s × s -> Set Real := fun p => Ioo p.1 p.2
  let u := ⋃ i : ↥s × ↥s, T i
  have hfinite : (s \ u).Finite := s.finite_sdiff_iUnion_Ioo'
  obtain ⟨A, A_count, hA⟩ :
    exists A : Set (↥s × ↥s), A.Countable ∧ ⋃ i in A, T i = ⋃ i : ↥s × ↥s, T i :=
    isOpen_iUnion_countable _ fun p => isOpen_Ioo
  have M : forallᵐ x ∂μ, x ∉ s \ u := hfinite.countable.ae_notMem _
  have M' : forallᵐ x ∂μ, forall (i : ↥s × ↥s), i in A -> x in s inter T i -> p x := by
    rw [ae_ball_iff A_count]
    rintro ⟨⟨a, as⟩, ⟨b, bs⟩⟩ -
    change forallᵐ x : Real ∂μ, x in s inter Ioo a b -> p x
    rcases le_or_gt b a with (hba | hab)
    · simp only [Ioo_eq_empty_of_le hba, inter_empty, IsEmpty.forall_iff, eventually_true,
        mem_empty_iff_false]
    · exact h a b as bs hab
  filter_upwards [M, M'] with x hx h'x
  intro xs
  by_cases Hx : x in ⋃ i : ↥s × ↥s, T i
  · rw [← hA] at Hx
    obtain ⟨p, pA, xp⟩ : exists p : ↥s × ↥s, p in A ∧ x in T p := by
      simpa only [mem_iUnion, exists_prop, SetCoe.exists, exists_and_right] using Hx
    apply h'x p pA ⟨xs, xp⟩
  · exact False.elim (hx ⟨xs, Hx⟩)

中文:
定理 ae_of_mem_of_ae_of_mem_inter_Ioo
  结论: {μ : 测度 实数} [NullSingleton类 μ] {s : 集合 实数}
  证明: by
  /- By second-countability, we cover `s` by countably many intervals `(a, b)` (except maybe for
    two endpoints, which don't matter since `μ` does not have any atom). -/
  let T : s × s -> Set Real := fun p => Ioo p.1 p.2
  let u := ⋃ i : ↥s × ↥s, T i
  have hfinite : (s \ u).Finite := s.finite_sdiff_iUnion_Ioo'
  obtain ⟨A, A_count, hA⟩ :
    exists A : Set (↥s × ↥s), A.Countable ∧ ⋃ i in A, T i = ⋃ i : ↥s × ↥s, T i :=
    isOpen_iUnion_countable _ fun p => isOpen_Ioo
  have M : forallᵐ x ∂μ, x ∉ s \ u := hfinite.countable.ae_notMem _
  have M' : forallᵐ x ∂μ, forall (i : ↥s × ↥s), i in A -> x in s inter T i -> p x := by
    rw [ae_ball_iff A_count]
    rintro ⟨⟨a, as⟩, ⟨b, bs⟩⟩ -
    change forallᵐ x : Real ∂μ, x in s inter Ioo a b -> p x
    rcases le_or_gt b a with (hba | hab)
    · simp only [Ioo_eq_empty_of_le hba, inter_empty, IsEmpty.forall_iff, eventually_true,
        mem_empty_iff_false]
    · exact h a b as bs hab
  filter_upwards [M, M'] with x hx h'x
  intro xs
  by_cases Hx : x in ⋃ i : ↥s × ↥s, T i
  · rw [← hA] at Hx
    obtain ⟨p, pA, xp⟩ : exists p : ↥s × ↥s, p in A ∧ x in T p := by
      simpa only [mem_iUnion, exists_prop, SetCoe.exists, exists_and_right] using Hx
    apply h'x p pA ⟨xs, xp⟩
  · exact False.elim (hx ⟨xs, Hx⟩)
-/
theorem ae_of_mem_of_ae_of_mem_inter_Ioo {μ : Measure Real} [NullSingletonClass μ] {s : Set Real}
    {p : Real -> Prop} (h : forall a b, a in s -> b in s -> a < b -> forallᵐ x ∂μ, x in s inter Ioo a b -> p x) :
    forallᵐ x ∂μ, x in s -> p x := by
  /- By second-countability, we cover `s` by countably many intervals `(a, b)` (except maybe for
    two endpoints, which don't matter since `μ` does not have any atom). -/
  let T : s × s -> Set Real := fun p => Ioo p.1 p.2
  let u := ⋃ i : ↥s × ↥s, T i
  have hfinite : (s \ u).Finite := s.finite_sdiff_iUnion_Ioo'
  obtain ⟨A, A_count, hA⟩ :
    exists A : Set (↥s × ↥s), A.Countable ∧ ⋃ i in A, T i = ⋃ i : ↥s × ↥s, T i :=
    isOpen_iUnion_countable _ fun p => isOpen_Ioo
  have M : forallᵐ x ∂μ, x ∉ s \ u := hfinite.countable.ae_notMem _
  have M' : forallᵐ x ∂μ, forall (i : ↥s × ↥s), i in A -> x in s inter T i -> p x := by
    rw [ae_ball_iff A_count]
    rintro ⟨⟨a, as⟩, ⟨b, bs⟩⟩ -
    change forallᵐ x : Real ∂μ, x in s inter Ioo a b -> p x
    rcases le_or_gt b a with (hba | hab)
    · simp only [Ioo_eq_empty_of_le hba, inter_empty, IsEmpty.forall_iff, eventually_true,
        mem_empty_iff_false]
    · exact h a b as bs hab
  filter_upwards [M, M'] with x hx h'x
  intro xs
  by_cases Hx : x in ⋃ i : ↥s × ↥s, T i
  · rw [← hA] at Hx
    obtain ⟨p, pA, xp⟩ : exists p : ↥s × ↥s, p in A ∧ x in T p := by
      simpa only [mem_iUnion, exists_prop, SetCoe.exists, exists_and_right] using Hx
    apply h'x p pA ⟨xs, xp⟩
  · exact False.elim (hx ⟨xs, Hx⟩)
