/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Lebesgue integral over finite and countable types, sets and measures

The lemmas in this file require at least one of the following of the Lebesgue integral:
* The type of the set of integration is finite or countable
* The set of integration is finite or countable
* The measure is finite, s-finite or sigma-finite
-/

public section

namespace MeasureTheory

open Set ENNReal NNReal Measure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

section FiniteMeasure

/--
theorem `setLIntegral_const_lt_top` / 定理 `setLIntegral_const_lt_top`

English:
theorem setLIntegral_const_lt_top
  given: [IsFiniteMeasure μ] (s : Set α) {c : Real>=0∞} (hc : c != ∞)
  proof: by
  rw [lintegral_const]
  exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top (μ.restrict s) univ)

中文:
定理 setL整数egral_const_lt_top
  条件: [是有限测度 μ] (s : 集合 α) {c : 实数>=0∞} (hc : c != ∞)
  证明: by
  rw [lintegral_const]
  exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top (μ.restrict s) univ)

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top, hc.lt_top, lintegral_const, lt_top, measure_lt_top, mul_lt_top, restrict
-/
theorem setLIntegral_const_lt_top [IsFiniteMeasure μ] (s : Set α) {c : Real>=0∞} (hc : c != ∞) :
    ∫⁻ _ in s, c ∂μ < ∞ := by
  rw [lintegral_const]
  exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top (μ.restrict s) univ)

/--
theorem `lintegral_const_lt_top` / 定理 `lintegral_const_lt_top`

English:
theorem lintegral_const_lt_top
  given: [IsFiniteMeasure μ] {c : Real>=0∞} (hc : c != ∞)
  statement: ∫⁻ _, c ∂μ < ∞
  proof: by
  simpa only [Measure.restrict_univ] using setLIntegral_const_lt_top (univ : Set α) hc

中文:
定理 lintegral_const_lt_top
  条件: [是有限测度 μ] {c : 实数>=0∞} (hc : c != ∞)
  结论: ∫⁻ _, c ∂μ < ∞
  证明: by
  simpa only [Measure.restrict_univ] using setLIntegral_const_lt_top (univ : Set α) hc

Depends on / 依赖: Measure, Measure.restrict_univ, restrict_univ, setLIntegral_const_lt_top
-/
theorem lintegral_const_lt_top [IsFiniteMeasure μ] {c : Real>=0∞} (hc : c != ∞) : ∫⁻ _, c ∂μ < ∞ := by
  simpa only [Measure.restrict_univ] using setLIntegral_const_lt_top (univ : Set α) hc

/--
lemma `lintegral_eq_const` / 引理 `lintegral_eq_const`

English:
lemma lintegral_eq_const
  statement: [IsProbabilityMeasure μ] {f : α -> Real>=0∞} {c : Real>=0∞}
  proof: by simp [lintegral_congr_ae hf]

中文:
引理 lintegral_eq_const
  结论: [是概率测度 μ] {f : α -> 实数>=0∞} {c : 实数>=0∞}
  证明: by simp [lintegral_congr_ae hf]

Depends on / 依赖: lintegral_congr_ae
-/
lemma lintegral_eq_const [IsProbabilityMeasure μ] {f : α -> Real>=0∞} {c : Real>=0∞}
    (hf : forallᵐ x ∂μ, f x = c) : ∫⁻ x, f x ∂μ = c := by simp [lintegral_congr_ae hf]

/--
lemma `lintegral_le_const` / 引理 `lintegral_le_const`

English:
lemma lintegral_le_const
  statement: [IsProbabilityMeasure μ] {f : α -> Real>=0∞} {c : Real>=0∞}
  proof: (lintegral_mono_ae hf).trans_eq (by simp)

中文:
引理 lintegral_le_const
  结论: [是概率测度 μ] {f : α -> 实数>=0∞} {c : 实数>=0∞}
  证明: (lintegral_mono_ae hf).trans_eq (by simp)

Depends on / 依赖: lintegral_mono_ae, trans_eq
-/
lemma lintegral_le_const [IsProbabilityMeasure μ] {f : α -> Real>=0∞} {c : Real>=0∞}
    (hf : forallᵐ x ∂μ, f x <= c) : ∫⁻ x, f x ∂μ <= c :=
  (lintegral_mono_ae hf).trans_eq (by simp)

/--
lemma `iInf_le_lintegral` / 引理 `iInf_le_lintegral`

English:
lemma iInf_le_lintegral
  given: [IsProbabilityMeasure μ] (f : α -> Real>=0∞)
  statement: ⨅ x, f x <= ∫⁻ x, f x ∂μ
  proof: le_trans (by simp) (iInf_mul_le_lintegral f)

中文:
引理 iInf_le_lintegral
  条件: [是概率测度 μ] (f : α -> 实数>=0∞)
  结论: ⨅ x, f x <= ∫⁻ x, f x ∂μ
  证明: le_trans (by simp) (iInf_mul_le_lintegral f)

Depends on / 依赖: iInf_mul_le_lintegral, le_trans
-/
lemma iInf_le_lintegral [IsProbabilityMeasure μ] (f : α -> Real>=0∞) : ⨅ x, f x <= ∫⁻ x, f x ∂μ :=
  le_trans (by simp) (iInf_mul_le_lintegral f)

/--
lemma `lintegral_le_iSup` / 引理 `lintegral_le_iSup`

English:
lemma lintegral_le_iSup
  given: [IsProbabilityMeasure μ] (f : α -> Real>=0∞)
  statement: ∫⁻ x, f x ∂μ <= ⨆ x, f x
  proof: le_trans (lintegral_le_iSup_mul f) (by simp)

中文:
引理 lintegral_le_iSup
  条件: [是概率测度 μ] (f : α -> 实数>=0∞)
  结论: ∫⁻ x, f x ∂μ <= ⨆ x, f x
  证明: le_trans (lintegral_le_iSup_mul f) (by simp)

Depends on / 依赖: le_trans, lintegral_le_iSup_mul
-/
lemma lintegral_le_iSup [IsProbabilityMeasure μ] (f : α -> Real>=0∞) : ∫⁻ x, f x ∂μ <= ⨆ x, f x :=
  le_trans (lintegral_le_iSup_mul f) (by simp)

variable (μ) in
/--
theorem `_root_.IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal` / 定理 `_root_.IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal`

English:
theorem _root_.IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
  proof: by
  rw [← μ.restrict_univ]
  refine setLIntegral_lt_top_of_le_nnreal (measure_ne_top _ _) ?_
  simpa using f_bdd

中文:
定理 _root_.是有限测度.lintegral_lt_top_of_bounded_to_ennreal
  证明: by
  rw [← μ.restrict_univ]
  refine setLIntegral_lt_top_of_le_nnreal (measure_ne_top _ _) ?_
  simpa using f_bdd

Depends on / 依赖: f_bdd, measure_ne_top, restrict_univ, setLIntegral_lt_top_of_le_nnreal
-/
theorem _root_.IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
    [IsFiniteMeasure μ] {f : α -> Real>=0∞} (f_bdd : exists c : Real>=0, forall x, f x <= c) : ∫⁻ x, f x ∂μ < ∞ := by
  rw [← μ.restrict_univ]
  refine setLIntegral_lt_top_of_le_nnreal (measure_ne_top _ _) ?_
  simpa using f_bdd

end FiniteMeasure

section DiracAndCount

/--
theorem `lintegral_dirac'` / 定理 `lintegral_dirac'`

English:
theorem lintegral_dirac'
  given: (a : α) {f : α -> Real>=0∞} (hf : Measurable f)
  statement: ∫⁻ a, f a ∂dirac a = f a
  proof: by
  simp [lintegral_congr_ae (ae_eq_dirac' hf)]

@[simp]

中文:
定理 lintegral_dirac'
  条件: (a : α) {f : α -> 实数>=0∞} (hf : 可测 f)
  结论: ∫⁻ a, f a ∂dirac a = f a
  证明: by
  simp [lintegral_congr_ae (ae_eq_dirac' hf)]

@[simp]

Depends on / 依赖: ae_eq_dirac, lintegral_congr_ae
-/
theorem lintegral_dirac' (a : α) {f : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a := by
  simp [lintegral_congr_ae (ae_eq_dirac' hf)]

@[simp]
/--
theorem `lintegral_dirac` / 定理 `lintegral_dirac`

English:
theorem lintegral_dirac
  given: [MeasurableSingletonClass α] (a : α) (f : α -> Real>=0∞)
  proof: by simp [lintegral_congr_ae (ae_eq_dirac f)]

中文:
定理 lintegral_dirac
  条件: [MeasurableSingleton类 α] (a : α) (f : α -> 实数>=0∞)
  证明: by simp [lintegral_congr_ae (ae_eq_dirac f)]

Depends on / 依赖: ae_eq_dirac, lintegral_congr_ae
-/
theorem lintegral_dirac [MeasurableSingletonClass α] (a : α) (f : α -> Real>=0∞) :
    ∫⁻ a, f a ∂dirac a = f a := by simp [lintegral_congr_ae (ae_eq_dirac f)]

/--
theorem `setLIntegral_dirac'` / 定理 `setLIntegral_dirac'`

English:
theorem setLIntegral_dirac'
  statement: {a : α} {f : α -> Real>=0∞} (hf : Measurable f) {s : Set α}
  proof: by
  rw [restrict_dirac' hs]
  split_ifs
  · exact lintegral_dirac' _ hf
  · exact lintegral_zero_measure _

中文:
定理 setL整数egral_dirac'
  结论: {a : α} {f : α -> 实数>=0∞} (hf : 可测 f) {s : 集合 α}
  证明: by
  rw [restrict_dirac' hs]
  split_ifs
  · exact lintegral_dirac' _ hf
  · exact lintegral_zero_measure _

Depends on / 依赖: lintegral_dirac, lintegral_zero_measure, restrict_dirac, split_ifs
-/
theorem setLIntegral_dirac' {a : α} {f : α -> Real>=0∞} (hf : Measurable f) {s : Set α}
    (hs : MeasurableSet s) [Decidable (a in s)] :
    ∫⁻ x in s, f x ∂Measure.dirac a = if a in s then f a else 0 := by
  rw [restrict_dirac' hs]
  split_ifs
  · exact lintegral_dirac' _ hf
  · exact lintegral_zero_measure _

/--
theorem `setLIntegral_dirac` / 定理 `setLIntegral_dirac`

English:
theorem setLIntegral_dirac
  statement: {a : α} (f : α -> Real>=0∞) (s : Set α) [MeasurableSingletonClass α]
  proof: by
  rw [restrict_dirac]
  split_ifs
  · exact lintegral_dirac _ _
  · exact lintegral_zero_measure _

中文:
定理 setL整数egral_dirac
  结论: {a : α} (f : α -> 实数>=0∞) (s : 集合 α) [MeasurableSingleton类 α]
  证明: by
  rw [restrict_dirac]
  split_ifs
  · exact lintegral_dirac _ _
  · exact lintegral_zero_measure _

Depends on / 依赖: lintegral_dirac, lintegral_zero_measure, restrict_dirac, split_ifs
-/
theorem setLIntegral_dirac {a : α} (f : α -> Real>=0∞) (s : Set α) [MeasurableSingletonClass α]
    [Decidable (a in s)] : ∫⁻ x in s, f x ∂Measure.dirac a = if a in s then f a else 0 := by
  rw [restrict_dirac]
  split_ifs
  · exact lintegral_dirac _ _
  · exact lintegral_zero_measure _

/--
theorem `lintegral_count'` / 定理 `lintegral_count'`

English:
theorem lintegral_count'
  given: {f : α -> Real>=0∞} (hf : Measurable f)
  statement: ∫⁻ a, f a ∂count = ∑' a, f a
  proof: by
  rw [count]; rw [lintegral_sum_measure]
  congr
  exact funext fun a => lintegral_dirac' a hf

中文:
定理 lintegral_count'
  条件: {f : α -> 实数>=0∞} (hf : 可测 f)
  结论: ∫⁻ a, f a ∂count = ∑' a, f a
  证明: by
  rw [count]; rw [lintegral_sum_measure]
  congr
  exact funext fun a => lintegral_dirac' a hf

Depends on / 依赖: lintegral_dirac, lintegral_sum_measure
-/
theorem lintegral_count' {f : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂count = ∑' a, f a := by
  rw [count]; rw [lintegral_sum_measure]
  congr
  exact funext fun a => lintegral_dirac' a hf

/--
theorem `lintegral_count` / 定理 `lintegral_count`

English:
theorem lintegral_count
  given: [MeasurableSingletonClass α] (f : α -> Real>=0∞)
  proof: by
  rw [count]; rw [lintegral_sum_measure]
  congr
  exact funext fun a => lintegral_dirac a f

中文:
定理 lintegral_count
  条件: [MeasurableSingleton类 α] (f : α -> 实数>=0∞)
  证明: by
  rw [count]; rw [lintegral_sum_measure]
  congr
  exact funext fun a => lintegral_dirac a f

Depends on / 依赖: lintegral_dirac, lintegral_sum_measure
-/
theorem lintegral_count [MeasurableSingletonClass α] (f : α -> Real>=0∞) :
    ∫⁻ a, f a ∂count = ∑' a, f a := by
  rw [count]; rw [lintegral_sum_measure]
  congr
  exact funext fun a => lintegral_dirac a f

/--
theorem `_root_.ENNReal.count_const_le_le_of_tsum_le` / 定理 `_root_.ENNReal.count_const_le_le_of_tsum_le`

English:
theorem _root_.ENNReal.count_const_le_le_of_tsum_le
  statement: [MeasurableSingletonClass α] {a : α -> Real>=0∞}
  proof: by
  rw [← lintegral_count] at tsum_le_c
  apply (MeasureTheory.meas_ge_le_lintegral_div a_mble.aemeasurable ε_ne_zero ε_ne_top).trans
  exact ENNReal.div_le_div tsum_le_c rfl.le

中文:
定理 _root_.广义非负实数.count_const_le_le_of_tsum_le
  结论: [MeasurableSingleton类 α] {a : α -> 实数>=0∞}
  证明: by
  rw [← lintegral_count] at tsum_le_c
  apply (MeasureTheory.meas_ge_le_lintegral_div a_mble.aemeasurable ε_ne_zero ε_ne_top).trans
  exact ENNReal.div_le_div tsum_le_c rfl.le

Depends on / 依赖: ENNReal, ENNReal.div_le_div, MeasureTheory, MeasureTheory.meas_ge_le_lintegral_div, a_mble, a_mble.aemeasurable, aemeasurable, div_le_div, lintegral_count, meas_ge_le_lintegral_div, rfl.le, tsum_le_c
-/
theorem _root_.ENNReal.count_const_le_le_of_tsum_le [MeasurableSingletonClass α] {a : α -> Real>=0∞}
    (a_mble : Measurable a) {c : Real>=0∞} (tsum_le_c : ∑' i, a i <= c) {ε : Real>=0∞} (ε_ne_zero : ε != 0)
    (ε_ne_top : ε != ∞) : Measure.count { i : α | ε <= a i } <= c / ε := by
  rw [← lintegral_count] at tsum_le_c
  apply (MeasureTheory.meas_ge_le_lintegral_div a_mble.aemeasurable ε_ne_zero ε_ne_top).trans
  exact ENNReal.div_le_div tsum_le_c rfl.le

/--
theorem `_root_.NNReal.count_const_le_le_of_tsum_le` / 定理 `_root_.NNReal.count_const_le_le_of_tsum_le`

English:
theorem _root_.NNReal.count_const_le_le_of_tsum_le
  statement: [MeasurableSingletonClass α] {a : α -> Real>=0}
  proof: by
  rw [show (fun i => ε <= a i) = fun i => (ε : Real>=0∞) <= ((↑) ∘ a) i by
      simp only [ENNReal.coe_le_coe]; rw [Function.comp]]
  apply
    ENNReal.count_const_le_le_of_tsum_le (measurable_coe_nnreal_ennreal.comp a_mble) _
      (mod_cast ε_ne_zero) (@ENNReal.coe_ne_top ε)
  convert! ENNReal

中文:
定理 _root_.非负实数.count_const_le_le_of_tsum_le
  结论: [MeasurableSingleton类 α] {a : α -> 实数>=0}
  证明: by
  rw [show (fun i => ε <= a i) = fun i => (ε : Real>=0∞) <= ((↑) ∘ a) i by
      simp only [ENNReal.coe_le_coe]; rw [Function.comp]]
  apply
    ENNReal.count_const_le_le_of_tsum_le (measurable_coe_nnreal_ennreal.comp a_mble) _
      (mod_cast ε_ne_zero) (@ENNReal.coe_ne_top ε)
  convert! ENNReal

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.coe_le_coe.mpr, ENNReal.coe_ne_top, ENNReal.count_const_le_le_of_tsum_le, ENNReal.tsum_coe_eq, Function, Function.comp, Function.comp_apply, a_mble, a_summable, a_summable.hasSum, coe_le_coe, coe_ne_top, comp_apply, convert, count_const_le_le_of_tsum_le, hasSum, measurable_coe_nnreal_ennreal, measurable_coe_nnreal_ennreal.comp
-/
theorem _root_.NNReal.count_const_le_le_of_tsum_le [MeasurableSingletonClass α] {a : α -> Real>=0}
    (a_mble : Measurable a) (a_summable : Summable a) {c : Real>=0} (tsum_le_c : ∑' i, a i <= c)
    {ε : Real>=0} (ε_ne_zero : ε != 0) : Measure.count { i : α | ε <= a i } <= c / ε := by
  rw [show (fun i => ε <= a i) = fun i => (ε : Real>=0∞) <= ((↑) ∘ a) i by
      simp only [ENNReal.coe_le_coe]; rw [Function.comp]]
  apply
    ENNReal.count_const_le_le_of_tsum_le (measurable_coe_nnreal_ennreal.comp a_mble) _
      (mod_cast ε_ne_zero) (@ENNReal.coe_ne_top ε)
  convert! ENNReal.coe_le_coe.mpr tsum_le_c
  simp_rw [Function.comp_apply]
  rw [ENNReal.tsum_coe_eq a_summable.hasSum]

end DiracAndCount

section Countable

/--
theorem `lintegral_countable'` / 定理 `lintegral_countable'`

English:
theorem lintegral_countable'
  given: [Countable α] [MeasurableSingletonClass α] (f : α -> Real>=0∞)
  proof: by
  conv_lhs => rw [← sum_smul_dirac μ, lintegral_sum_measure]
  congr 1 with a : 1
  simp [mul_comm]

中文:
定理 lintegral_countable'
  条件: [可数 α] [MeasurableSingleton类 α] (f : α -> 实数>=0∞)
  证明: by
  conv_lhs => rw [← sum_smul_dirac μ, lintegral_sum_measure]
  congr 1 with a : 1
  simp [mul_comm]

Depends on / 依赖: conv_lhs, lintegral_sum_measure, mul_comm, sum_smul_dirac
-/
theorem lintegral_countable' [Countable α] [MeasurableSingletonClass α] (f : α -> Real>=0∞) :
    ∫⁻ a, f a ∂μ = ∑' a, f a * μ {a} := by
  conv_lhs => rw [← sum_smul_dirac μ, lintegral_sum_measure]
  congr 1 with a : 1
  simp [mul_comm]

/--
theorem `lintegral_singleton'` / 定理 `lintegral_singleton'`

English:
theorem lintegral_singleton'
  given: {f : α -> Real>=0∞} (hf : Measurable f) (a : α)
  proof: by
  simp [lintegral_dirac' _ hf, mul_comm]

中文:
定理 lintegral_singleton'
  条件: {f : α -> 实数>=0∞} (hf : 可测 f) (a : α)
  证明: by
  simp [lintegral_dirac' _ hf, mul_comm]

Depends on / 依赖: lintegral_dirac, mul_comm
-/
theorem lintegral_singleton' {f : α -> Real>=0∞} (hf : Measurable f) (a : α) :
    ∫⁻ x in {a}, f x ∂μ = f a * μ {a} := by
  simp [lintegral_dirac' _ hf, mul_comm]

/--
theorem `lintegral_singleton` / 定理 `lintegral_singleton`

English:
theorem lintegral_singleton
  given: [MeasurableSingletonClass α] (f : α -> Real>=0∞) (a : α)
  proof: by
  simp [mul_comm]

中文:
定理 lintegral_singleton
  条件: [MeasurableSingleton类 α] (f : α -> 实数>=0∞) (a : α)
  证明: by
  simp [mul_comm]

Depends on / 依赖: mul_comm
-/
theorem lintegral_singleton [MeasurableSingletonClass α] (f : α -> Real>=0∞) (a : α) :
    ∫⁻ x in {a}, f x ∂μ = f a * μ {a} := by
  simp [mul_comm]

/--
theorem `lintegral_countable` / 定理 `lintegral_countable`

English:
theorem lintegral_countable
  statement: [MeasurableSingletonClass α] (f : α -> Real>=0∞) {s : Set α}
  proof: calc
    ∫⁻ a in s, f a ∂μ = ∫⁻ a in ⋃ x in s, {x}, f a ∂μ := by rw [biUnion_of_singleton]
    _ = ∑' a : s, ∫⁻ x in {(a : α)}, f x ∂μ :=
      (lintegral_biUnion hs (fun _ _ => measurableSet_singleton _) (pairwiseDisjoint_fiber id s) _)
    _ = ∑' a : s, f a * μ {(a : α)} := by simp only [lintegral

中文:
定理 lintegral_countable
  结论: [MeasurableSingleton类 α] (f : α -> 实数>=0∞) {s : 集合 α}
  证明: calc
    ∫⁻ a in s, f a ∂μ = ∫⁻ a in ⋃ x in s, {x}, f a ∂μ := by rw [biUnion_of_singleton]
    _ = ∑' a : s, ∫⁻ x in {(a : α)}, f x ∂μ :=
      (lintegral_biUnion hs (fun _ _ => measurableSet_singleton _) (pairwiseDisjoint_fiber id s) _)
    _ = ∑' a : s, f a * μ {(a : α)} := by simp only [lintegral

Depends on / 依赖: biUnion_of_singleton, lintegral_biUnion, lintegral_singleton, measurableSet_singleton, pairwiseDisjoint_fiber
-/
theorem lintegral_countable [MeasurableSingletonClass α] (f : α -> Real>=0∞) {s : Set α}
    (hs : s.Countable) : ∫⁻ a in s, f a ∂μ = ∑' a : s, f a * μ {(a : α)} :=
  calc
    ∫⁻ a in s, f a ∂μ = ∫⁻ a in ⋃ x in s, {x}, f a ∂μ := by rw [biUnion_of_singleton]
    _ = ∑' a : s, ∫⁻ x in {(a : α)}, f x ∂μ :=
      (lintegral_biUnion hs (fun _ _ => measurableSet_singleton _) (pairwiseDisjoint_fiber id s) _)
    _ = ∑' a : s, f a * μ {(a : α)} := by simp only [lintegral_singleton]

/--
theorem `lintegral_insert` / 定理 `lintegral_insert`

English:
theorem lintegral_insert
  statement: [MeasurableSingletonClass α] {a : α} {s : Set α} (h : a ∉ s)
  proof: by
  rw [← union_singleton]; rw [lintegral_union (measurableSet_singleton a)]; rw [lintegral_singleton]; rw [add_comm]
  rwa [disjoint_singleton_right]

中文:
定理 lintegral_insert
  结论: [MeasurableSingleton类 α] {a : α} {s : 集合 α} (h : a ∉ s)
  证明: by
  rw [← union_singleton]; rw [lintegral_union (measurableSet_singleton a)]; rw [lintegral_singleton]; rw [add_comm]
  rwa [disjoint_singleton_right]

Depends on / 依赖: add_comm, disjoint_singleton_right, lintegral_singleton, lintegral_union, measurableSet_singleton, union_singleton
-/
theorem lintegral_insert [MeasurableSingletonClass α] {a : α} {s : Set α} (h : a ∉ s)
    (f : α -> Real>=0∞) : ∫⁻ x in insert a s, f x ∂μ = f a * μ {a} + ∫⁻ x in s, f x ∂μ := by
  rw [← union_singleton]; rw [lintegral_union (measurableSet_singleton a)]; rw [lintegral_singleton]; rw [add_comm]
  rwa [disjoint_singleton_right]

/--
theorem `lintegral_finset` / 定理 `lintegral_finset`

English:
theorem lintegral_finset
  given: [MeasurableSingletonClass α] (s : Finset α) (f : α -> Real>=0∞)
  proof: by
  simp only [lintegral_countable _ s.countable_toSet, ← Finset.tsum_subtype']

中文:
定理 lintegral_finset
  条件: [MeasurableSingleton类 α] (s : 有限集 α) (f : α -> 实数>=0∞)
  证明: by
  simp only [lintegral_countable _ s.countable_toSet, ← Finset.tsum_subtype']

Depends on / 依赖: Finset, Finset.tsum_subtype, countable_toSet, lintegral_countable, s.countable_toSet, tsum_subtype
-/
theorem lintegral_finset [MeasurableSingletonClass α] (s : Finset α) (f : α -> Real>=0∞) :
    ∫⁻ x in s, f x ∂μ = ∑ x in s, f x * μ {x} := by
  simp only [lintegral_countable _ s.countable_toSet, ← Finset.tsum_subtype']

/--
theorem `lintegral_fintype` / 定理 `lintegral_fintype`

English:
theorem lintegral_fintype
  given: [MeasurableSingletonClass α] [Fintype α] (f : α -> Real>=0∞)
  proof: by
  rw [← lintegral_finset]; rw [Finset.coe_univ]; rw [Measure.restrict_univ]

中文:
定理 lintegral_fintype
  条件: [MeasurableSingleton类 α] [有限类型 α] (f : α -> 实数>=0∞)
  证明: by
  rw [← lintegral_finset]; rw [Finset.coe_univ]; rw [Measure.restrict_univ]

Depends on / 依赖: Finset, Finset.coe_univ, Measure, Measure.restrict_univ, coe_univ, lintegral_finset, restrict_univ
-/
theorem lintegral_fintype [MeasurableSingletonClass α] [Fintype α] (f : α -> Real>=0∞) :
    ∫⁻ x, f x ∂μ = ∑ x, f x * μ {x} := by
  rw [← lintegral_finset]; rw [Finset.coe_univ]; rw [Measure.restrict_univ]

/--
theorem `lintegral_unique` / 定理 `lintegral_unique`

English:
theorem lintegral_unique
  given: [Unique α] (f : α -> Real>=0∞)
  statement: ∫⁻ x, f x ∂μ = f default * μ univ
  proof: calc
∫⁻ x, f x ∂μ = ∫⁻ _, f default ∂μ := lintegral_congr Unique.forall_iff.2 rfl
    _ = f default * μ univ := lintegral_const _

中文:
定理 lintegral_unique
  条件: [唯一 α] (f : α -> 实数>=0∞)
  结论: ∫⁻ x, f x ∂μ = f default * μ univ
  证明: calc
∫⁻ x, f x ∂μ = ∫⁻ _, f default ∂μ := lintegral_congr Unique.forall_iff.2 rfl
    _ = f default * μ univ := lintegral_const _

Depends on / 依赖: Unique, Unique.forall_iff, forall_iff, lintegral_congr, lintegral_const
-/
theorem lintegral_unique [Unique α] (f : α -> Real>=0∞) : ∫⁻ x, f x ∂μ = f default * μ univ :=
  calc
∫⁻ x, f x ∂μ = ∫⁻ _, f default ∂μ := lintegral_congr Unique.forall_iff.2 rfl
    _ = f default * μ univ := lintegral_const _

end Countable

section SFinite

variable (μ) in
/--
theorem `exists_measurable_le_forall_setLIntegral_eq` / 定理 `exists_measurable_le_forall_setLIntegral_eq`

English:
theorem exists_measurable_le_forall_setLIntegral_eq
  given: [SFinite μ] (f : α -> Real>=0∞)
  proof: by
  -- We only need to prove the `≤` inequality for the integrals, the other one follows from `g ≤ f`.
  rsuffices ⟨g, hgm, hgle, hleg⟩ :
      exists g : α -> Real>=0∞, Measurable g ∧ g <= f ∧ forall s, ∫⁻ a in s, f a ∂μ <= ∫⁻ a in s, g a ∂μ
  · exact ⟨g, hgm, hgle, fun s => (hleg s).antisymm (lin

中文:
定理 存在_measurable_le_对任意_setL整数egral_eq
  条件: [SFinite μ] (f : α -> 实数>=0∞)
  证明: by
  -- We only need to prove the `≤` inequality for the integrals, the other one follows from `g ≤ f`.
  rsuffices ⟨g, hgm, hgle, hleg⟩ :
      exists g : α -> Real>=0∞, Measurable g ∧ g <= f ∧ forall s, ∫⁻ a in s, f a ∂μ <= ∫⁻ a in s, g a ∂μ
  · exact ⟨g, hgm, hgle, fun s => (hleg s).antisymm (lin
-/
theorem exists_measurable_le_forall_setLIntegral_eq [SFinite μ] (f : α -> Real>=0∞) :
    exists g : α -> Real>=0∞, Measurable g ∧ g <= f ∧ forall s, ∫⁻ a in s, f a ∂μ = ∫⁻ a in s, g a ∂μ := by
  -- We only need to prove the `≤` inequality for the integrals, the other one follows from `g ≤ f`.
  rsuffices ⟨g, hgm, hgle, hleg⟩ :
      exists g : α -> Real>=0∞, Measurable g ∧ g <= f ∧ forall s, ∫⁻ a in s, f a ∂μ <= ∫⁻ a in s, g a ∂μ
  · exact ⟨g, hgm, hgle, fun s => (hleg s).antisymm (lintegral_mono hgle)⟩
  -- Without loss of generality, `μ` is a finite measure.
  wlog h : IsFiniteMeasure μ generalizing μ
  · choose g hgm hgle hgint using fun n => @this (sfiniteSeq μ n) _ inferInstance
    refine ⟨fun x => ⨆ n, g n x, .iSup hgm, fun x => iSup_le (hgle · x), fun s => ?_⟩
    rw [← sum_sfiniteSeq μ]; rw [Measure.restrict_sum_of_countable]; rw [lintegral_sum_measure]; rw [lintegral_sum_measure]
    exact ENNReal.tsum_le_tsum fun n => (hgint n s).trans (lintegral_mono fun x => le_iSup (g · x) _)
  -- According to `exists_measurable_le_lintegral_eq`, for any natural `n`
  -- we can choose a measurable function $g_{n}$
  -- such that $g_{n}(x) ≤ \min (f(x), n)$ for all $x$
  -- and both sides have the same integral over the whole space w.r.t. $μ$.
  have (n : Nat) : exists g : α -> Real>=0∞, Measurable g ∧ g <= f ∧ g <= n ∧
      ∫⁻ a, min (f a) n ∂μ = ∫⁻ a, g a ∂μ := by
    simpa [and_assoc] using exists_measurable_le_lintegral_eq μ (f ⊓ n)
  choose g hgm hgf hgle hgint using this
  -- Let `φ` be the pointwise supremum of the functions $g_{n}$.
  -- Clearly, `φ` is a measurable function and `φ ≤ f`.
  set φ : α -> Real>=0∞ := fun x => ⨆ n, g n x
  have hφm : Measurable φ := by fun_prop
  have hφle : φ <= f := fun x => iSup_le (hgf · x)
  refine ⟨φ, hφm, hφle, fun s => ?_⟩
  -- Now we show the inequality between set integrals.
  -- Choose a simple function `ψ ≤ f` with values in `ℝ≥0` and prove for `ψ`.
  rw [lintegral_eq_nnreal]
  refine iSup₂_le fun ψ hψ => ?_
  -- Choose `n` such that `ψ x ≤ n` for all `x`.
  obtain ⟨n, hn⟩ : exists n : Nat, forall x, ψ x <= n := by
    rcases ψ.range.bddAbove with ⟨C, hC⟩
    exact ⟨⌈C⌉₊, fun x => (hC <| ψ.mem_range_self x).trans (Nat.le_ceil _)⟩
  calc
    (ψ.map (↑)).lintegral (μ.restrict s) = ∫⁻ a in s, ψ a ∂μ :=
.symm SimpleFunc.lintegral_eq_lintegral ..
    _ <= ∫⁻ a in s, min (f a) n ∂μ :=
      lintegral_mono fun a => le_min (hψ _) (ENNReal.coe_le_coe.2 (hn a))
    _ <= ∫⁻ a in s, g n a ∂μ := by
      have : ∫⁻ a in (toMeasurable μ s)ᶜ, min (f a) n ∂μ != ∞ :=
.ne IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal _ ⟨n, fun _ => min_le_right ..⟩
      have hsm : MeasurableSet (toMeasurable μ s) := measurableSet_toMeasurable ..
      apply ENNReal.le_of_add_le_add_right this
      rw [← μ.restrict_toMeasurable_of_sFinite]; rw [lintegral_add_compl _ hsm]; rw [hgint]; rw [← lintegral_add_compl _ hsm]
      gcongr with x
      exact le_min (hgf n x) (hgle n x)
    _ <= _ := lintegral_mono fun x => le_iSup (g · x) n

/--
theorem `exists_pos_lintegral_lt_of_sigmaFinite` / 定理 `exists_pos_lintegral_lt_of_sigmaFinite`

English:
theorem exists_pos_lintegral_lt_of_sigmaFinite
  statement: (μ : Measure α) [SigmaFinite μ] {ε : Real>=0∞}
  proof: by
  /- Let `s` be a covering of `α` by pairwise disjoint measurable sets of finite measure. Let
    `δ : ℕ → ℝ≥0` be a positive function such that `∑' i, μ (s i) * δ i < ε`. Then the function that
     is equal to `δ n` on `s n` is a positive function with integral less than `ε`. -/
  set s : Nat -

中文:
定理 存在_pos_lintegral_lt_of_sigmaFinite
  结论: (μ : 测度 α) [σ有限 μ] {ε : 实数>=0∞}
  证明: by
  /- Let `s` be a covering of `α` by pairwise disjoint measurable sets of finite measure. Let
    `δ : ℕ → ℝ≥0` be a positive function such that `∑' i, μ (s i) * δ i < ε`. Then the function that
     is equal to `δ n` on `s n` is a positive function with integral less than `ε`. -/
  set s : Nat -
-/
theorem exists_pos_lintegral_lt_of_sigmaFinite (μ : Measure α) [SigmaFinite μ] {ε : Real>=0∞}
    (ε0 : ε != 0) : exists g : α -> Real>=0, (forall x, 0 < g x) ∧ Measurable g ∧ ∫⁻ x, g x ∂μ < ε := by
  /- Let `s` be a covering of `α` by pairwise disjoint measurable sets of finite measure. Let
    `δ : ℕ → ℝ≥0` be a positive function such that `∑' i, μ (s i) * δ i < ε`. Then the function that
     is equal to `δ n` on `s n` is a positive function with integral less than `ε`. -/
  set s : Nat -> Set α := disjointed (spanningSets μ)
  have : forall n, μ (s n) < ∞ := fun n =>
    (measure_mono <| disjointed_subset _ _).trans_lt (measure_spanningSets_lt_top μ n)
  obtain ⟨δ, δpos, δsum⟩ : exists δ : Nat -> Real>=0, (forall i, 0 < δ i) ∧ (∑' i, μ (s i) * δ i) < ε :=
    ENNReal.exists_pos_tsum_mul_lt_of_countable ε0 _ fun n => (this n).ne
  set N : α -> Nat := spanningSetsIndex μ
  have hN_meas : Measurable N := measurableSet_spanningSetsIndex μ
  have hNs : forall n, N ⁻¹' {n} = s n := preimage_spanningSetsIndex_singleton μ
  refine ⟨δ ∘ N, fun x => δpos _, measurable_from_nat.comp hN_meas, ?_⟩
  simp_rw [Function.comp_apply, ← Function.comp_apply (f := (fun n => (↑(δ n) : Real>=0∞))),
    lintegral_comp measurable_from_nat.coe_nnreal_ennreal hN_meas]
  simpa [N, hNs, lintegral_countable', measurableSet_spanningSetsIndex, mul_comm] using δsum

omit [MeasurableSpace α]

variable {m m0 : MeasurableSpace α}

local infixr:25 " ->ₛ " => SimpleFunc

/--
theorem `univ_le_of_forall_fin_meas_le` / 定理 `univ_le_of_forall_fin_meas_le`

English:
theorem univ_le_of_forall_fin_meas_le
  statement: {μ : Measure α} (hm : m <= m0) [SigmaFinite (μ.trim hm)]
  proof: by
  let S := @spanningSets _ m (μ.trim hm) _
  have hS_mono : Monotone S := @monotone_spanningSets _ m (μ.trim hm) _
  have hS_meas : forall n, MeasurableSet[m] (S n) := @measurableSet_spanningSets _ m (μ.trim hm) _
  rw [← @iUnion_spanningSets _ m (μ.trim hm)]
  refine (h_F_lim S hS_meas hS_mono).

中文:
定理 univ_le_of_对任意_fin_meas_le
  结论: {μ : 测度 α} (hm : m <= m0) [σ有限 (μ.trim hm)]
  证明: by
  let S := @spanningSets _ m (μ.trim hm) _
  have hS_mono : Monotone S := @monotone_spanningSets _ m (μ.trim hm) _
  have hS_meas : forall n, MeasurableSet[m] (S n) := @measurableSet_spanningSets _ m (μ.trim hm) _
  rw [← @iUnion_spanningSets _ m (μ.trim hm)]
  refine (h_F_lim S hS_meas hS_mono).

Depends on / 依赖: MeasurableSet, Monotone, hS_meas, hS_mono, h_F_lim, iSup_le, iUnion_spanningSets, le_trim, measurableSet_spanningSets, measure_spanningSets_lt_top, monotone_spanningSets, spanningSets, trans_lt
-/
theorem univ_le_of_forall_fin_meas_le {μ : Measure α} (hm : m <= m0) [SigmaFinite (μ.trim hm)]
    (C : Real>=0∞) {f : Set α -> Real>=0∞} (hf : forall s, MeasurableSet[m] s -> μ s != ∞ -> f s <= C)
    (h_F_lim :
      forall S : Nat -> Set α, (forall n, MeasurableSet[m] (S n)) -> Monotone S -> f (⋃ n, S n) <= ⨆ n, f (S n)) :
    f univ <= C := by
  let S := @spanningSets _ m (μ.trim hm) _
  have hS_mono : Monotone S := @monotone_spanningSets _ m (μ.trim hm) _
  have hS_meas : forall n, MeasurableSet[m] (S n) := @measurableSet_spanningSets _ m (μ.trim hm) _
  rw [← @iUnion_spanningSets _ m (μ.trim hm)]
  refine (h_F_lim S hS_meas hS_mono).trans ?_
  refine iSup_le fun n => hf (S n) (hS_meas n) ?_
  exact ((le_trim hm).trans_lt (@measure_spanningSets_lt_top _ m (μ.trim hm) _ n)).ne

/--
theorem `lintegral_le_of_forall_fin_meas_trim_le` / 定理 `lintegral_le_of_forall_fin_meas_trim_le`

English:
theorem lintegral_le_of_forall_fin_meas_trim_le
  statement: {μ : Measure α} (hm : m <= m0)
  proof: by
  have : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ := by simp only [Measure.restrict_univ]
  rw [← this]
  refine univ_le_of_forall_fin_meas_le hm C hf fun S _ hS_mono => ?_
  rw [setLIntegral_iUnion_of_directed]
  exact directed_of_isDirected_le hS_mono

alias lintegral_le_of_forall_fin_meas_le_of_mea

中文:
定理 lintegral_le_of_对任意_fin_meas_trim_le
  结论: {μ : 测度 α} (hm : m <= m0)
  证明: by
  have : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ := by simp only [Measure.restrict_univ]
  rw [← this]
  refine univ_le_of_forall_fin_meas_le hm C hf fun S _ hS_mono => ?_
  rw [setLIntegral_iUnion_of_directed]
  exact directed_of_isDirected_le hS_mono

alias lintegral_le_of_forall_fin_meas_le_of_mea

Depends on / 依赖: Measure, Measure.restrict_univ, directed_of_isDirected_le, hS_mono, restrict_univ, setLIntegral_iUnion_of_directed, univ_le_of_forall_fin_meas_le
-/
theorem lintegral_le_of_forall_fin_meas_trim_le {μ : Measure α} (hm : m <= m0)
    [SigmaFinite (μ.trim hm)] (C : Real>=0∞) {f : α -> Real>=0∞}
    (hf : forall s, MeasurableSet[m] s -> μ s != ∞ -> ∫⁻ x in s, f x ∂μ <= C) : ∫⁻ x, f x ∂μ <= C := by
  have : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ := by simp only [Measure.restrict_univ]
  rw [← this]
  refine univ_le_of_forall_fin_meas_le hm C hf fun S _ hS_mono => ?_
  rw [setLIntegral_iUnion_of_directed]
  exact directed_of_isDirected_le hS_mono

alias lintegral_le_of_forall_fin_meas_le_of_measurable := lintegral_le_of_forall_fin_meas_trim_le

/--
theorem `lintegral_le_of_forall_fin_meas_le` / 定理 `lintegral_le_of_forall_fin_meas_le`

English:
theorem lintegral_le_of_forall_fin_meas_le
  statement: [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
  proof: have : SigmaFinite (μ.trim le_rfl) := by rwa [trim_eq_self]
  lintegral_le_of_forall_fin_meas_trim_le _ C hf

中文:
定理 lintegral_le_of_对任意_fin_meas_le
  结论: [可测空间 α] {μ : 测度 α} [σ有限 μ]
  证明: have : SigmaFinite (μ.trim le_rfl) := by rwa [trim_eq_self]
  lintegral_le_of_forall_fin_meas_trim_le _ C hf

Depends on / 依赖: SigmaFinite, le_rfl, lintegral_le_of_forall_fin_meas_trim_le, trim_eq_self
-/
theorem lintegral_le_of_forall_fin_meas_le [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    (C : Real>=0∞) {f : α -> Real>=0∞}
    (hf : forall s, MeasurableSet s -> μ s != ∞ -> ∫⁻ x in s, f x ∂μ <= C) : ∫⁻ x, f x ∂μ <= C :=
  have : SigmaFinite (μ.trim le_rfl) := by rwa [trim_eq_self]
  lintegral_le_of_forall_fin_meas_trim_le _ C hf

/--
theorem `SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral` / 定理 `SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral`

English:
theorem SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral
  statement: {m : MeasurableSpace α}
  proof: by
  induction f using MeasureTheory.SimpleFunc.induction generalizing L with
  | @const c s hs =>
    simp only [hs, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero, univ_inter,
      piecewise_eq_indicator, lintegral_indicator, lintegral_const, Measure.restrict_apply',
      ENNReal.coe_

中文:
定理 SimpleFunc.存在_lt_lintegral_simpleFunc_of_lt_lintegral
  结论: {m : 可测空间 α}
  证明: by
  induction f using MeasureTheory.SimpleFunc.induction generalizing L with
  | @const c s hs =>
    simp only [hs, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero, univ_inter,
      piecewise_eq_indicator, lintegral_indicator, lintegral_const, Measure.restrict_apply',
      ENNReal.coe_

Depends on / 依赖: ENNReal, ENNReal.coe_indicator, ENNReal.coe_zero, ENNReal.div_lt_iff, Function, Function.const_apply, Measure, Measure.restrict_apply, MeasureTheory, MeasureTheory.SimpleFunc.induction, SimpleFunc, SimpleFunc.coe_zero, c_ne_ze, c_ne_zero, coe_const, coe_indicator, coe_piecewise, coe_zero, const_apply, const_zero
-/
theorem SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral {m : MeasurableSpace α}
    {μ : Measure α} [SigmaFinite μ] {f : α ->ₛ Real>=0} {L : Real>=0∞} (hL : L < ∫⁻ x, f x ∂μ) :
    exists g : α ->ₛ Real>=0, (forall x, g x <= f x) ∧ ∫⁻ x, g x ∂μ < ∞ ∧ L < ∫⁻ x, g x ∂μ := by
  induction f using MeasureTheory.SimpleFunc.induction generalizing L with
  | @const c s hs =>
    simp only [hs, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero, univ_inter,
      piecewise_eq_indicator, lintegral_indicator, lintegral_const, Measure.restrict_apply',
      ENNReal.coe_indicator, Function.const_apply] at hL
    have c_ne_zero : c != 0 := by
      intro hc
      simp only [hc, ENNReal.coe_zero, zero_mul, not_lt_zero] at hL
    have : L / c < μ s := by
      rwa [ENNReal.div_lt_iff, mul_comm]
      · simp only [c_ne_zero, Ne, ENNReal.coe_eq_zero, not_false_iff, true_or]
      · simp only [Ne, coe_ne_top, not_false_iff, true_or]
    obtain ⟨t, ht, ts, mlt, t_top⟩ :
      exists t : Set α, MeasurableSet t ∧ t subseteq s ∧ L / ↑c < μ t ∧ μ t < ∞ :=
      Measure.exists_subset_measure_lt_top hs this
    refine ⟨piecewise t ht (const α c) (const α 0), fun x => ?_, ?_, ?_⟩
    · refine indicator_le_indicator_of_subset ts (fun x => ?_) x
      exact zero_le
    · simp only [ht, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero, univ_inter,
        piecewise_eq_indicator, ENNReal.coe_indicator, Function.const_apply, lintegral_indicator,
        lintegral_const, Measure.restrict_apply', ENNReal.mul_lt_top ENNReal.coe_lt_top t_top]
    · simp only [ht, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero,
        piecewise_eq_indicator, ENNReal.coe_indicator, Function.const_apply, lintegral_indicator,
        lintegral_const, Measure.restrict_apply', univ_inter]
      rwa [mul_comm, ← ENNReal.div_lt_iff]
      · simp only [c_ne_zero, Ne, ENNReal.coe_eq_zero, not_false_iff, true_or]
      · simp only [Ne, coe_ne_top, not_false_iff, true_or]
  | @add f₁ f₂ _ h₁ h₂ =>
    replace hL : L < ∫⁻ x, f₁ x ∂μ + ∫⁻ x, f₂ x ∂μ := by
      rwa [← lintegral_add_left f₁.measurable.coe_nnreal_ennreal]
    by_cases hf₁ : ∫⁻ x, f₁ x ∂μ = 0
    · simp only [hf₁, zero_add] at hL
      rcases h₂ hL with ⟨g, g_le, g_top, gL⟩
      refine ⟨g, fun x => (g_le x).trans ?_, g_top, gL⟩
      simp only [SimpleFunc.coe_add, Pi.add_apply, le_add_iff_nonneg_left, zero_le]
    by_cases hf₂ : ∫⁻ x, f₂ x ∂μ = 0
    · simp only [hf₂, add_zero] at hL
      rcases h₁ hL with ⟨g, g_le, g_top, gL⟩
      refine ⟨g, fun x => (g_le x).trans ?_, g_top, gL⟩
      simp only [SimpleFunc.coe_add, Pi.add_apply, le_add_iff_nonneg_right, zero_le]
    obtain ⟨L₁, hL₁, L₂, hL₂, hL⟩ : exists L₁ < ∫⁻ x, f₁ x ∂μ, exists L₂ < ∫⁻ x, f₂ x ∂μ, L < L₁ + L₂ :=
      ENNReal.exists_lt_add_of_lt_add hL hf₁ hf₂
    rcases h₁ hL₁ with ⟨g₁, g₁_le, g₁_top, hg₁⟩
    rcases h₂ hL₂ with ⟨g₂, g₂_le, g₂_top, hg₂⟩
    refine ⟨g₁ + g₂, fun x => add_le_add (g₁_le x) (g₂_le x), ?_, ?_⟩
    · apply lt_of_le_of_lt _ (add_lt_top.2 ⟨g₁_top, g₂_top⟩)
      rw [← lintegral_add_left g₁.measurable.coe_nnreal_ennreal]
      exact le_rfl
    · apply hL.trans ((ENNReal.add_lt_add hg₁ hg₂).trans_le _)
      rw [← lintegral_add_left g₁.measurable.coe_nnreal_ennreal]
      simp only [coe_add, Pi.add_apply, ENNReal.coe_add, le_rfl]

/--
theorem `exists_lt_lintegral_simpleFunc_of_lt_lintegral` / 定理 `exists_lt_lintegral_simpleFunc_of_lt_lintegral`

English:
theorem exists_lt_lintegral_simpleFunc_of_lt_lintegral
  statement: {m : MeasurableSpace α} {μ : Measure α}
  proof: by
  simp_rw [lintegral_eq_nnreal, lt_iSup_iff] at hL
  rcases hL with ⟨g₀, hg₀, g₀L⟩
  have h'L : L < ∫⁻ x, g₀ x ∂μ := by
    convert! g₀L
    rw [← SimpleFunc.lintegral_eq_lintegral]; rw [SimpleFunc.coe_map]
    simp only [Function.comp_apply]
  rcases SimpleFunc.exists_lt_lintegral_simpleFunc_of_

中文:
定理 存在_lt_lintegral_simpleFunc_of_lt_lintegral
  结论: {m : 可测空间 α} {μ : 测度 α}
  证明: by
  simp_rw [lintegral_eq_nnreal, lt_iSup_iff] at hL
  rcases hL with ⟨g₀, hg₀, g₀L⟩
  have h'L : L < ∫⁻ x, g₀ x ∂μ := by
    convert! g₀L
    rw [← SimpleFunc.lintegral_eq_lintegral]; rw [SimpleFunc.coe_map]
    simp only [Function.comp_apply]
  rcases SimpleFunc.exists_lt_lintegral_simpleFunc_of_

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, Function, Function.comp_apply, SimpleFunc, SimpleFunc.coe_map, SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral, SimpleFunc.lintegral_eq_lintegral, coe_le_coe, coe_map, comp_apply, convert, exists_lt_lintegral_simpleFunc_of_lt_lintegral, lintegral_eq_lintegral, lintegral_eq_nnreal, lt_iSup_iff, simp_rw
-/
theorem exists_lt_lintegral_simpleFunc_of_lt_lintegral {m : MeasurableSpace α} {μ : Measure α}
    [SigmaFinite μ] {f : α -> Real>=0} {L : Real>=0∞} (hL : L < ∫⁻ x, f x ∂μ) :
    exists g : α ->ₛ Real>=0, (forall x, g x <= f x) ∧ ∫⁻ x, g x ∂μ < ∞ ∧ L < ∫⁻ x, g x ∂μ := by
  simp_rw [lintegral_eq_nnreal, lt_iSup_iff] at hL
  rcases hL with ⟨g₀, hg₀, g₀L⟩
  have h'L : L < ∫⁻ x, g₀ x ∂μ := by
    convert! g₀L
    rw [← SimpleFunc.lintegral_eq_lintegral]; rw [SimpleFunc.coe_map]
    simp only [Function.comp_apply]
  rcases SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral h'L with ⟨g, hg, gL, gtop⟩
  exact ⟨g, fun x => (hg x).trans (ENNReal.coe_le_coe.1 (hg₀ x)), gL, gtop⟩

end SFinite

end MeasureTheory
