/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.Additive
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Box-additive functions defined by measures

In this file we prove a few simple facts about rectangular boxes, partitions, and measures:

- given a box `I : Box ι`, its coercion to `Set (ι → ℝ)` and `I.Icc` are measurable sets;
- if `μ` is a locally finite measure, then `(I : Set (ι → ℝ))` and `I.Icc` have finite measure;
- if `μ` is a locally finite measure, then `fun J ↦ μ.real J` is a box additive function.

For the last statement, we both prove it as a proposition and define a bundled
`BoxIntegral.BoxAdditiveMap` function.

## Tags

rectangular box, measure
-/

@[expose] public section

open Set

noncomputable section

open scoped ENNReal BoxIntegral

variable {ι : Type*}

namespace BoxIntegral

open MeasureTheory

namespace Box

variable (I : Box ι)

/--
theorem `measure_Icc_lt_top` / 定理 `measure_Icc_lt_top`

English:
theorem measure_Icc_lt_top
  given: (μ : Measure (ι -> Real)) [IsLocallyFiniteMeasure μ]
  statement: μ (Box.Icc I) < ∞
  proof: show μ (Icc I.lower I.upper) < ∞ from I.isCompact_Icc.measure_lt_top

中文:
定理 measure_Icc_lt_top
  条件: (μ : 测度 (ι -> 实数)) [是局部有限测度 μ]
  结论: μ (Box.闭区间 I) < ∞
  证明: show μ (Icc I.lower I.upper) < ∞ from I.isCompact_Icc.measure_lt_top

Depends on / 依赖: I.isCompact_Icc.measure_lt_top, I.lower, I.upper, isCompact_Icc, measure_lt_top
-/
theorem measure_Icc_lt_top (μ : Measure (ι -> Real)) [IsLocallyFiniteMeasure μ] : μ (Box.Icc I) < ∞ :=
  show μ (Icc I.lower I.upper) < ∞ from I.isCompact_Icc.measure_lt_top

/--
theorem `measure_coe_lt_top` / 定理 `measure_coe_lt_top`

English:
theorem measure_coe_lt_top
  given: (μ : Measure (ι -> Real)) [IsLocallyFiniteMeasure μ]
  statement: μ I < ∞
  proof: (measure_mono <| coe_subset_Icc).trans_lt (I.measure_Icc_lt_top μ)

中文:
定理 measure_coe_lt_top
  条件: (μ : 测度 (ι -> 实数)) [是局部有限测度 μ]
  结论: μ I < ∞
  证明: (measure_mono <| coe_subset_Icc).trans_lt (I.measure_Icc_lt_top μ)

Depends on / 依赖: I.measure_Icc_lt_top, coe_subset_Icc, measure_Icc_lt_top, measure_mono, trans_lt
-/
theorem measure_coe_lt_top (μ : Measure (ι -> Real)) [IsLocallyFiniteMeasure μ] : μ I < ∞ :=
  (measure_mono <| coe_subset_Icc).trans_lt (I.measure_Icc_lt_top μ)

section Countable

variable [Countable ι]

/--
theorem `measurableSet_coe` / 定理 `measurableSet_coe`

English:
theorem measurableSet_coe
  statement: MeasurableSet (I : Set (ι -> Real))
  proof: by
  rw [coe_eq_pi]
  exact MeasurableSet.univ_pi fun i => measurableSet_Ioc

中文:
定理 measurableSet_coe
  结论: 可测集 (I : 集合 (ι -> 实数))
  证明: by
  rw [coe_eq_pi]
  exact MeasurableSet.univ_pi fun i => measurableSet_Ioc

Depends on / 依赖: MeasurableSet, MeasurableSet.univ_pi, coe_eq_pi, measurableSet_Ioc, univ_pi
-/
theorem measurableSet_coe : MeasurableSet (I : Set (ι -> Real)) := by
  rw [coe_eq_pi]
  exact MeasurableSet.univ_pi fun i => measurableSet_Ioc

/--
theorem `measurableSet_Icc` / 定理 `measurableSet_Icc`

English:
theorem measurableSet_Icc
  statement: MeasurableSet (Box.Icc I)
  proof: _root_.measurableSet_Icc

中文:
定理 measurableSet_Icc
  结论: 可测集 (Box.闭区间 I)
  证明: _root_.measurableSet_Icc

Depends on / 依赖: _root_, _root_.measurableSet_Icc, measurableSet_Icc
-/
theorem measurableSet_Icc : MeasurableSet (Box.Icc I) :=
  _root_.measurableSet_Icc

/--
theorem `measurableSet_Ioo` / 定理 `measurableSet_Ioo`

English:
theorem measurableSet_Ioo
  statement: MeasurableSet (Box.Ioo I)
  proof: MeasurableSet.univ_pi fun _ => _root_.measurableSet_Ioo

中文:
定理 measurableSet_Ioo
  结论: 可测集 (Box.开区间 I)
  证明: MeasurableSet.univ_pi fun _ => _root_.measurableSet_Ioo

Depends on / 依赖: MeasurableSet, MeasurableSet.univ_pi, _root_, _root_.measurableSet_Ioo, measurableSet_Ioo, univ_pi
-/
theorem measurableSet_Ioo : MeasurableSet (Box.Ioo I) :=
  MeasurableSet.univ_pi fun _ => _root_.measurableSet_Ioo

end Countable

variable [Fintype ι]

/--
theorem `coe_ae_eq_Icc` / 定理 `coe_ae_eq_Icc`

English:
theorem coe_ae_eq_Icc
  statement: (I : Set (ι -> Real)) =ᵐ[volume] Box.Icc I
  proof: by
  rw [coe_eq_pi]
  exact Measure.univ_pi_Ioc_ae_eq_Icc

中文:
定理 coe_ae_eq_Icc
  结论: (I : 集合 (ι -> 实数)) =ᵐ[volume] Box.闭区间 I
  证明: by
  rw [coe_eq_pi]
  exact Measure.univ_pi_Ioc_ae_eq_Icc

Depends on / 依赖: Measure, Measure.univ_pi_Ioc_ae_eq_Icc, coe_eq_pi, univ_pi_Ioc_ae_eq_Icc
-/
theorem coe_ae_eq_Icc : (I : Set (ι -> Real)) =ᵐ[volume] Box.Icc I := by
  rw [coe_eq_pi]
  exact Measure.univ_pi_Ioc_ae_eq_Icc

/--
theorem `Ioo_ae_eq_Icc` / 定理 `Ioo_ae_eq_Icc`

English:
theorem Ioo_ae_eq_Icc
  statement: Box.Ioo I =ᵐ[volume] Box.Icc I
  proof: Measure.univ_pi_Ioo_ae_eq_Icc

中文:
定理 Ioo_ae_eq_Icc
  结论: Box.开区间 I =ᵐ[volume] Box.闭区间 I
  证明: Measure.univ_pi_Ioo_ae_eq_Icc

Depends on / 依赖: Measure, Measure.univ_pi_Ioo_ae_eq_Icc, univ_pi_Ioo_ae_eq_Icc
-/
theorem Ioo_ae_eq_Icc : Box.Ioo I =ᵐ[volume] Box.Icc I :=
  Measure.univ_pi_Ioo_ae_eq_Icc

end Box

/--
theorem `Prepartition.measure_iUnion_toReal` / 定理 `Prepartition.measure_iUnion_toReal`

English:
theorem Prepartition.measure_iUnion_toReal
  statement: [Finite ι] {I : Box ι} (π : Prepartition I)
  proof: by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_sum (fun J _ => (J.measure_coe_lt_top μ).ne)]; rw [π.iUnion_def]
  simp only [← mem_boxes]
  rw [measure_biUnion_finset π.pairwiseDisjoint]
  exact fun J _ => J.measurableSet_coe

中文:
定理 预分拆.measure_iUnion_to实数
  结论: [有限 ι] {I : Box ι} (π : 预分拆 I)
  证明: by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_sum (fun J _ => (J.measure_coe_lt_top μ).ne)]; rw [π.iUnion_def]
  simp only [← mem_boxes]
  rw [measure_biUnion_finset π.pairwiseDisjoint]
  exact fun J _ => J.measurableSet_coe

Depends on / 依赖: ENNReal, ENNReal.toReal_sum, J.measurableSet_coe, J.measure_coe_lt_top, iUnion_def, measurableSet_coe, measureReal_def, measure_biUnion_finset, measure_coe_lt_top, mem_boxes, pairwiseDisjoint, toReal_sum
-/
theorem Prepartition.measure_iUnion_toReal [Finite ι] {I : Box ι} (π : Prepartition I)
    (μ : Measure (ι -> Real)) [IsLocallyFiniteMeasure μ] :
    μ.real π.iUnion = ∑ J in π.boxes, μ.real J := by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_sum (fun J _ => (J.measure_coe_lt_top μ).ne)]; rw [π.iUnion_def]
  simp only [← mem_boxes]
  rw [measure_biUnion_finset π.pairwiseDisjoint]
  exact fun J _ => J.measurableSet_coe

end BoxIntegral

open BoxIntegral BoxIntegral.Box

namespace MeasureTheory

namespace Measure

/-- If `μ` is a locally finite measure on `ℝⁿ`, then `fun J ↦ μ.real J` is a box-additive
function. -/
@[simps]
/--
Definition of `toBoxAdditive` / `toBoxAdditive` 的定义

English:
definition toBoxAdditive
  signature: [Finite ι] (μ : Measure (ι -> Real)) [IsLocallyFiniteMeasure μ]
  body: μ.real J
  sum_partition_boxes' J _ π hπ := by rw [← π.measure_iUnion_toReal, hπ.iUnion_eq]

中文:
定义 toBoxAdditive
  签名: [有限 ι] (μ : 测度 (ι -> 实数)) [是局部有限测度 μ]
  定义体: μ.real J
  sum_partition_boxes' J _ π hπ := by rw [← π.measure_iUnion_toReal, hπ.iUnion_eq]
-/
def toBoxAdditive [Finite ι] (μ : Measure (ι -> Real)) [IsLocallyFiniteMeasure μ] : ι ->ᵇᵃ[⊤] Real where
  toFun J := μ.real J
  sum_partition_boxes' J _ π hπ := by rw [← π.measure_iUnion_toReal, hπ.iUnion_eq]

end Measure

end MeasureTheory

namespace BoxIntegral

open MeasureTheory

namespace Box

variable [Fintype ι]

-- This is not a `simp` lemma because the left-hand side simplifies already.
-- See `volume_apply'` for the relevant `simp` lemma.
/--
theorem `volume_apply` / 定理 `volume_apply`

English:
theorem volume_apply
  given: (I : Box ι)
  proof: by
  rw [Measure.toBoxAdditive_apply]; rw [coe_eq_pi]; rw [measureReal_def]; rw [Real.volume_pi_Ioc_toReal I.lower_le_upper]

@[simp]

中文:
定理 volume_apply
  条件: (I : Box ι)
  证明: by
  rw [Measure.toBoxAdditive_apply]; rw [coe_eq_pi]; rw [measureReal_def]; rw [Real.volume_pi_Ioc_toReal I.lower_le_upper]

@[simp]

Depends on / 依赖: I.lower_le_upper, Measure, Measure.toBoxAdditive_apply, Real.volume_pi_Ioc_toReal, coe_eq_pi, lower_le_upper, measureReal_def, toBoxAdditive_apply, volume_pi_Ioc_toReal
-/
theorem volume_apply (I : Box ι) :
    (volume : Measure (ι -> Real)).toBoxAdditive I = ∏ i, (I.upper i - I.lower i) := by
  rw [Measure.toBoxAdditive_apply]; rw [coe_eq_pi]; rw [measureReal_def]; rw [Real.volume_pi_Ioc_toReal I.lower_le_upper]

@[simp]
/--
theorem `volume_apply'` / 定理 `volume_apply'`

English:
theorem volume_apply'
  given: (I : Box ι)
  proof: by
  rw [coe_eq_pi]; rw [Real.volume_pi_Ioc_toReal I.lower_le_upper]

中文:
定理 volume_apply'
  条件: (I : Box ι)
  证明: by
  rw [coe_eq_pi]; rw [Real.volume_pi_Ioc_toReal I.lower_le_upper]

Depends on / 依赖: I.lower_le_upper, Real.volume_pi_Ioc_toReal, coe_eq_pi, lower_le_upper, volume_pi_Ioc_toReal
-/
theorem volume_apply' (I : Box ι) :
    ((volume : Measure (ι -> Real)) I).toReal = ∏ i, (I.upper i - I.lower i) := by
  rw [coe_eq_pi]; rw [Real.volume_pi_Ioc_toReal I.lower_le_upper]

/--
theorem `volume_face_mul` / 定理 `volume_face_mul`

English:
theorem volume_face_mul
  given: {n} (i : Fin (n + 1)) (I : Box (Fin (n + 1)))
  proof: by
  simp only [face_lower, face_upper, Fin.prod_univ_succAbove _ i, mul_comm]

中文:
定理 volume_face_mul
  条件: {n} (i : 有限集 (n + 1)) (I : Box (有限集 (n + 1)))
  证明: by
  simp only [face_lower, face_upper, Fin.prod_univ_succAbove _ i, mul_comm]

Depends on / 依赖: Fin.prod_univ_succAbove, face_lower, face_upper, mul_comm, prod_univ_succAbove
-/
theorem volume_face_mul {n} (i : Fin (n + 1)) (I : Box (Fin (n + 1))) :
    (∏ j, ((I.face i).upper j - (I.face i).lower j)) * (I.upper i - I.lower i) =
      ∏ j, (I.upper j - I.lower j) := by
  simp only [face_lower, face_upper, Fin.prod_univ_succAbove _ i, mul_comm]

end Box

namespace BoxAdditiveMap

variable [Fintype ι]

/--
Definition of `volume` / `volume` 的定义

English:
definition volume
  signature: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  body: (volume : Measure (ι -> Real)).toBoxAdditive.toSMul

中文:
定义 volume
  签名: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  定义体: (volume : Measure (ι -> Real)).toBoxAdditive.toSMul
-/
protected def volume {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] : ι ->ᵇᵃ E ->L[Real] E :=
  (volume : Measure (ι -> Real)).toBoxAdditive.toSMul

/--
theorem `volume_apply` / 定理 `volume_apply`

English:
theorem volume_apply
  given: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] (I : Box ι) (x : E)
  proof: by
  rw [BoxAdditiveMap.volume]; rw [toSMul_apply]
  exact congr_arg₂ (· • ·) I.volume_apply rfl

中文:
定理 volume_apply
  条件: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E] (I : Box ι) (x : E)
  证明: by
  rw [BoxAdditiveMap.volume]; rw [toSMul_apply]
  exact congr_arg₂ (· • ·) I.volume_apply rfl

Depends on / 依赖: BoxAdditiveMap, BoxAdditiveMap.volume, I.volume_apply, toSMul_apply, volume, volume_apply
-/
theorem volume_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] (I : Box ι) (x : E) :
    BoxAdditiveMap.volume I x = (∏ j, (I.upper j - I.lower j)) • x := by
  rw [BoxAdditiveMap.volume]; rw [toSMul_apply]
  exact congr_arg₂ (· • ·) I.volume_apply rfl

end BoxAdditiveMap

end BoxIntegral
