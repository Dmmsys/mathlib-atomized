/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.MetricSpace.ThickenedIndicator

/-!
# Spaces where indicators of closed sets have decreasing approximations by continuous functions

In this file we define a typeclass `HasOuterApproxClosed` for topological spaces in which indicator
functions of closed sets have sequences of bounded continuous functions approximating them from
above. All pseudo-emetrizable spaces have this property, see `instHasOuterApproxClosed`.

In spaces with the `HasOuterApproxClosed` property, finite Borel measures are uniquely characterized
by the integrals of bounded continuous functions. Also weak convergence of finite measures and
convergence in distribution for random variables behave somewhat well in spaces with this property.

## Main definitions

* `HasOuterApproxClosed`: the typeclass for topological spaces in which indicator functions of
  closed sets have sequences of bounded continuous functions approximating them.
* `IsClosed.apprSeq`: a (non-constructive) choice of an approximating sequence to the indicator
  function of a closed set.

## Main results

* `instHasOuterApproxClosed`: Any pseudo-emetrizable space has the property `HasOuterApproxClosed`.
* `tendsto_lintegral_apprSeq`: The integrals of the approximating functions to the indicator of a
  closed set tend to the measure of the set.
* `ext_of_forall_lintegral_eq_of_IsFiniteMeasure`: Two finite measures are equal if the integrals
  of all bounded continuous functions with respect to both agree.

-/

@[expose] public section

open BoundedContinuousFunction MeasureTheory Topology Metric Filter Set ENNReal NNReal
open scoped Topology ENNReal NNReal BoundedContinuousFunction

section auxiliary

namespace MeasureTheory

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]

/--
theorem `tendsto_lintegral_nn_filter_of_le_const` / 定理 `tendsto_lintegral_nn_filter_of_le_const`

English:
theorem tendsto_lintegral_nn_filter_of_le_const
  statement: {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
  proof: by
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => c)
    (Eventually.of_forall fun i => (ENNReal.continuous_coe.comp (fs i).continuous).measurable) ?_
    (@lintegral_const_lt_top _ _ μ _ _ (@ENNReal.coe_ne_top c)).ne ?_
  · simpa only [Function.comp_apply, ENNReal.coe_le_coe] 

中文:
定理 tendsto_lintegral_nn_filter_of_le_const
  结论: {ι : 类型} {L : 滤子 ι} [L.是余untablyGenerated]
  证明: by
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => c)
    (Eventually.of_forall fun i => (ENNReal.continuous_coe.comp (fs i).continuous).measurable) ?_
    (@lintegral_const_lt_top _ _ μ _ _ (@ENNReal.coe_ne_top c)).ne ?_
  · simpa only [Function.comp_apply, ENNReal.coe_le_coe] 

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.coe_ne_top, ENNReal.continuous_coe.comp, ENNReal.tendsto_coe, Eventually, Eventually.of_forall, Function, Function.comp_apply, coe_le_coe, coe_ne_top, comp_apply, continuous, continuous_coe, fs_le_const, fs_lim, lintegral_const_lt_top, measurable, of_forall, tendsto_coe
-/
theorem tendsto_lintegral_nn_filter_of_le_const {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    (μ : Measure Ω) [IsFiniteMeasure μ] {fs : ι -> Ω ->ᵇ Real>=0} {c : Real>=0}
    (fs_le_const : forallᶠ i in L, forallᵐ ω : Ω ∂μ, fs i ω <= c) {f : Ω -> Real>=0}
    (fs_lim : forallᵐ ω : Ω ∂μ, Tendsto (fun i => fs i ω) L (𝓝 (f ω))) :
    Tendsto (fun i => ∫⁻ ω, fs i ω ∂μ) L (𝓝 (∫⁻ ω, f ω ∂μ)) := by
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => c)
    (Eventually.of_forall fun i => (ENNReal.continuous_coe.comp (fs i).continuous).measurable) ?_
    (@lintegral_const_lt_top _ _ μ _ _ (@ENNReal.coe_ne_top c)).ne ?_
  · simpa only [Function.comp_apply, ENNReal.coe_le_coe] using fs_le_const
  · simpa only [Function.comp_apply, ENNReal.tendsto_coe] using fs_lim

/--
theorem `measure_of_cont_bdd_of_tendsto_filter_indicator` / 定理 `measure_of_cont_bdd_of_tendsto_filter_indicator`

English:
theorem measure_of_cont_bdd_of_tendsto_filter_indicator
  statement: {ι : Type*} {L : Filter ι}
  proof: by
  convert! tendsto_lintegral_nn_filter_of_le_const μ fs_bdd fs_lim
  have aux : forall ω, indicator E (fun _ => (1 : Real>=0∞)) ω = ↑(indicator E (fun _ => (1 : Real>=0)) ω) :=
    fun ω => by simp only [ENNReal.coe_indicator, ENNReal.coe_one]
  simp_rw [← aux, lintegral_indicator E_mble]
  simp 

中文:
定理 measure_of_cont_bdd_of_tendsto_filter_indicator
  结论: {ι : 类型} {L : 滤子 ι}
  证明: by
  convert! tendsto_lintegral_nn_filter_of_le_const μ fs_bdd fs_lim
  have aux : forall ω, indicator E (fun _ => (1 : Real>=0∞)) ω = ↑(indicator E (fun _ => (1 : Real>=0)) ω) :=
    fun ω => by simp only [ENNReal.coe_indicator, ENNReal.coe_one]
  simp_rw [← aux, lintegral_indicator E_mble]
  simp 

Depends on / 依赖: ENNReal, ENNReal.coe_indicator, ENNReal.coe_one, E_mble, MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_apply, coe_indicator, coe_one, convert, fs_bdd, fs_lim, indicator, lintegral_indicator, lintegral_one, restrict_apply, simp_rw, tendsto_lintegral_nn_filter_of_le_const, univ_inter
-/
theorem measure_of_cont_bdd_of_tendsto_filter_indicator {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (μ : Measure Ω)
    [IsFiniteMeasure μ] {c : Real>=0} {E : Set Ω} (E_mble : MeasurableSet E) (fs : ι -> Ω ->ᵇ Real>=0)
    (fs_bdd : forallᶠ i in L, forallᵐ ω : Ω ∂μ, fs i ω <= c)
    (fs_lim : forallᵐ ω ∂μ, Tendsto (fun i => fs i ω) L (𝓝 (indicator E (fun _ => (1 : Real>=0)) ω))) :
    Tendsto (fun n => lintegral μ fun ω => fs n ω) L (𝓝 (μ E)) := by
  convert! tendsto_lintegral_nn_filter_of_le_const μ fs_bdd fs_lim
  have aux : forall ω, indicator E (fun _ => (1 : Real>=0∞)) ω = ↑(indicator E (fun _ => (1 : Real>=0)) ω) :=
    fun ω => by simp only [ENNReal.coe_indicator, ENNReal.coe_one]
  simp_rw [← aux, lintegral_indicator E_mble]
  simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]

/--
theorem `measure_of_cont_bdd_of_tendsto_indicator` / 定理 `measure_of_cont_bdd_of_tendsto_indicator`

English:
theorem measure_of_cont_bdd_of_tendsto_indicator
  proof: by
  have fs_lim' :
    forall ω, Tendsto (fun n : Nat => (fs n ω : Real>=0)) atTop (𝓝 (indicator E (fun _ => (1 : Real>=0)) ω)) := by
    rw [tendsto_pi_nhds] at fs_lim
    exact fun ω => fs_lim ω
  apply measure_of_cont_bdd_of_tendsto_filter_indicator μ E_mble fs
    (Eventually.of_forall fun n =>

中文:
定理 measure_of_cont_bdd_of_tendsto_indicator
  证明: by
  have fs_lim' :
    forall ω, Tendsto (fun n : Nat => (fs n ω : Real>=0)) atTop (𝓝 (indicator E (fun _ => (1 : Real>=0)) ω)) := by
    rw [tendsto_pi_nhds] at fs_lim
    exact fun ω => fs_lim ω
  apply measure_of_cont_bdd_of_tendsto_filter_indicator μ E_mble fs
    (Eventually.of_forall fun n =>

Depends on / 依赖: E_mble, Eventually, Eventually.of_forall, Tendsto, fs_bdd, fs_lim, indicator, measure_of_cont_bdd_of_tendsto_filter_indicator, of_forall, tendsto_pi_nhds
-/
theorem measure_of_cont_bdd_of_tendsto_indicator
    (μ : Measure Ω) [IsFiniteMeasure μ] {c : Real>=0} {E : Set Ω} (E_mble : MeasurableSet E)
    (fs : Nat -> Ω ->ᵇ Real>=0) (fs_bdd : forall n ω, fs n ω <= c)
    (fs_lim : Tendsto (fun n ω => fs n ω) atTop (𝓝 (indicator E fun _ => (1 : Real>=0)))) :
    Tendsto (fun n => lintegral μ fun ω => fs n ω) atTop (𝓝 (μ E)) := by
  have fs_lim' :
    forall ω, Tendsto (fun n : Nat => (fs n ω : Real>=0)) atTop (𝓝 (indicator E (fun _ => (1 : Real>=0)) ω)) := by
    rw [tendsto_pi_nhds] at fs_lim
    exact fun ω => fs_lim ω
  apply measure_of_cont_bdd_of_tendsto_filter_indicator μ E_mble fs
    (Eventually.of_forall fun n => Eventually.of_forall (fs_bdd n)) (Eventually.of_forall fs_lim')

/--
theorem `tendsto_lintegral_thickenedIndicator_of_isClosed` / 定理 `tendsto_lintegral_thickenedIndicator_of_isClosed`

English:
theorem tendsto_lintegral_thickenedIndicator_of_isClosed
  statement: {Ω : Type*} {mΩ : MeasurableSpace Ω}
  proof: by
  apply measure_of_cont_bdd_of_tendsto_indicator μ F_closed.measurableSet
    (fun n => thickenedIndicator (δs_pos n) F) fun n ω => thickenedIndicator_le_one (δs_pos n) F ω
  have key := thickenedIndicator_tendsto_indicator_closure δs_pos δs_lim F
  rwa [F_closed.closure_eq] at key

中文:
定理 tendsto_lintegral_thickenedIndicator_of_isClosed
  结论: {Ω : 类型} {mΩ : 可测空间 Ω}
  证明: by
  apply measure_of_cont_bdd_of_tendsto_indicator μ F_closed.measurableSet
    (fun n => thickenedIndicator (δs_pos n) F) fun n ω => thickenedIndicator_le_one (δs_pos n) F ω
  have key := thickenedIndicator_tendsto_indicator_closure δs_pos δs_lim F
  rwa [F_closed.closure_eq] at key

Depends on / 依赖: F_closed, F_closed.closure_eq, F_closed.measurableSet, closure_eq, measurableSet, measure_of_cont_bdd_of_tendsto_indicator, thickenedIndicator, thickenedIndicator_le_one, thickenedIndicator_tendsto_indicator_closure
-/
theorem tendsto_lintegral_thickenedIndicator_of_isClosed {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {F : Set Ω}
    (F_closed : IsClosed F) {δs : Nat -> Real} (δs_pos : forall n, 0 < δs n)
    (δs_lim : Tendsto δs atTop (𝓝 0)) :
    Tendsto (fun n => lintegral μ fun ω => (thickenedIndicator (δs_pos n) F ω : Real>=0∞)) atTop
      (𝓝 (μ F)) := by
  apply measure_of_cont_bdd_of_tendsto_indicator μ F_closed.measurableSet
    (fun n => thickenedIndicator (δs_pos n) F) fun n ω => thickenedIndicator_le_one (δs_pos n) F ω
  have key := thickenedIndicator_tendsto_indicator_closure δs_pos δs_lim F
  rwa [F_closed.closure_eq] at key

/--
lemma `integrable_thickenedIndicator` / 引理 `integrable_thickenedIndicator`

English:
lemma integrable_thickenedIndicator
  statement: {Ω : Type*} {mΩ : MeasurableSpace Ω}
  proof: by
  refine .of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
  simpa using thickenedIndicator_le_one δ_pos F x

中文:
引理 integrable_thickenedIndicator
  结论: {Ω : 类型} {mΩ : 可测空间 Ω}
  证明: by
  refine .of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
  simpa using thickenedIndicator_le_one δ_pos F x

Depends on / 依赖: ae_of_all, fun_prop, of_bound, thickenedIndicator_le_one
-/
lemma integrable_thickenedIndicator {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] (F : Set Ω)
    {δ : Real} (δ_pos : 0 < δ) :
    Integrable (fun ω => (thickenedIndicator δ_pos F ω : Real)) μ := by
  refine .of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
  simpa using thickenedIndicator_le_one δ_pos F x

/--
lemma `tendsto_integral_thickenedIndicator_of_isClosed` / 引理 `tendsto_integral_thickenedIndicator_of_isClosed`

English:
lemma tendsto_integral_thickenedIndicator_of_isClosed
  statement: {Ω : Type*} {mΩ : MeasurableSpace Ω}
  proof: by
  -- we switch to the `lintegral` formulation and apply the corresponding lemma there
  let fs : Nat -> Ω -> Real := fun n ω => thickenedIndicator (δs_pos n) F ω
  have h := tendsto_lintegral_thickenedIndicator_of_isClosed μ F_closed δs_pos δs_lim
  have h_eq (n : Nat) : ∫⁻ ω, thickenedIndicator 

中文:
引理 tendsto_integral_thickenedIndicator_of_isClosed
  结论: {Ω : 类型} {mΩ : 可测空间 Ω}
  证明: by
  -- we switch to the `lintegral` formulation and apply the corresponding lemma there
  let fs : Nat -> Ω -> Real := fun n ω => thickenedIndicator (δs_pos n) F ω
  have h := tendsto_lintegral_thickenedIndicator_of_isClosed μ F_closed δs_pos δs_lim
  have h_eq (n : Nat) : ∫⁻ ω, thickenedIndicator 
-/
lemma tendsto_integral_thickenedIndicator_of_isClosed {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {F : Set Ω}
    (F_closed : IsClosed F) {δs : Nat -> Real} (δs_pos : forall (n : Nat), 0 < δs n)
    (δs_lim : Tendsto δs atTop (𝓝 0)) :
    Tendsto (fun n : Nat => ∫ ω, (thickenedIndicator (δs_pos n) F ω : Real) ∂μ) atTop (𝓝 (μ.real F)) := by
  -- we switch to the `lintegral` formulation and apply the corresponding lemma there
  let fs : Nat -> Ω -> Real := fun n ω => thickenedIndicator (δs_pos n) F ω
  have h := tendsto_lintegral_thickenedIndicator_of_isClosed μ F_closed δs_pos δs_lim
  have h_eq (n : Nat) : ∫⁻ ω, thickenedIndicator (δs_pos n) F ω ∂μ
      = ENNReal.ofReal (∫ ω, fs n ω ∂μ) := by
    rw [lintegral_coe_eq_integral]
    exact integrable_thickenedIndicator F (δs_pos _)
  simp_rw [h_eq] at h
  rw [Measure.real_def]
  have h_eq' : (fun n => ∫ ω, fs n ω ∂μ) = fun n => (ENNReal.ofReal (∫ ω, fs n ω ∂μ)).toReal := by
    ext n
    rw [ENNReal.toReal_ofReal]
    exact integral_nonneg fun x => by simp [fs]
  rwa [h_eq', ENNReal.tendsto_toReal_iff (by simp) (by finiteness)]

end MeasureTheory -- namespace

end auxiliary -- section

section HasOuterApproxClosed

/--
Definition of `HasOuterApproxClosed` / `HasOuterApproxClosed` 的定义

English:
class HasOuterApproxClosed
  parameters: (X : Type*) [TopologicalSpace X]
  axioms and operations (1):
    - exAppr : forall (F : Set X), IsClosed F -> exists (fseq : Nat -> (X ->ᵇ Real>=0)), (forall n x, fseq n x <= 1) ∧ (forall n x, x in F -> 1 <= fseq n x) ∧ Tendsto (fun n : Nat => (fun x => fseq n x)) atTop (𝓝 (indicator F fun _ => (1 : Real>=0)))

中文:
类 有OuterApproxClosed
  参数: (X : 类型) [拓扑空间 X]
  公理与运算 (1 个):
    - exAppr : 对任意 (F : 集合 X), 是闭集 F -> 存在 (fseq : 自然数 -> (X ->ᵇ 实数>=0)), (对任意 n x, fseq n x <= 1) ∧ (对任意 n x, x in F -> 1 <= fseq n x) ∧ 收敛 (fun n : 自然数 => (fun x => fseq n x)) atTop (𝓝 (indicator F fun _ => (1 : 实数>=0)))
-/
class HasOuterApproxClosed (X : Type*) [TopologicalSpace X] : Prop where
  exAppr : forall (F : Set X), IsClosed F -> exists (fseq : Nat -> (X ->ᵇ Real>=0)),
    (forall n x, fseq n x <= 1) ∧ (forall n x, x in F -> 1 <= fseq n x) ∧
    Tendsto (fun n : Nat => (fun x => fseq n x)) atTop (𝓝 (indicator F fun _ => (1 : Real>=0)))

namespace HasOuterApproxClosed

variable {X : Type*} [TopologicalSpace X] [HasOuterApproxClosed X]
variable {F : Set X} (hF : IsClosed F)

/--
Definition of `_root_.IsClosed.apprSeq` / `_root_.IsClosed.apprSeq` 的定义

English:
definition _root_.IsClosed.apprSeq
  signature: : Nat -> (X ->ᵇ Real>=0)
  body: Exists.choose (HasOuterApproxClosed.exAppr F hF)

中文:
定义 _root_.是闭集.apprSeq
  签名: : 自然数 -> (X ->ᵇ 实数>=0)
  定义体: Exists.choose (HasOuterApproxClosed.exAppr F hF)

Depends on / 依赖: Exists, Exists.choose, HasOuterApproxClosed, HasOuterApproxClosed.exAppr, exAppr
-/
noncomputable def _root_.IsClosed.apprSeq : Nat -> (X ->ᵇ Real>=0) :=
  Exists.choose (HasOuterApproxClosed.exAppr F hF)

/--
lemma `apprSeq_apply_le_one` / 引理 `apprSeq_apply_le_one`

English:
lemma apprSeq_apply_le_one
  given: (n : Nat) (x : X)
  proof: (Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).1 n x

中文:
引理 apprSeq_apply_le_one
  条件: (n : 自然数) (x : X)
  证明: (Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).1 n x

Depends on / 依赖: Exists, Exists.choose_spec, HasOuterApproxClosed, HasOuterApproxClosed.exAppr, choose_spec, exAppr
-/
lemma apprSeq_apply_le_one (n : Nat) (x : X) :
    hF.apprSeq n x <= 1 :=
  (Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).1 n x

/--
lemma `apprSeq_apply_eq_one` / 引理 `apprSeq_apply_eq_one`

English:
lemma apprSeq_apply_eq_one
  given: (n : Nat) {x : X} (hxF : x in F)
  proof: le_antisymm (apprSeq_apply_le_one _ _ _)
    ((Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).2.1 n x hxF)

中文:
引理 apprSeq_apply_eq_one
  条件: (n : 自然数) {x : X} (hxF : x in F)
  证明: le_antisymm (apprSeq_apply_le_one _ _ _)
    ((Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).2.1 n x hxF)

Depends on / 依赖: Exists, Exists.choose_spec, HasOuterApproxClosed, HasOuterApproxClosed.exAppr, apprSeq_apply_le_one, choose_spec, exAppr, le_antisymm
-/
lemma apprSeq_apply_eq_one (n : Nat) {x : X} (hxF : x in F) :
    hF.apprSeq n x = 1 :=
  le_antisymm (apprSeq_apply_le_one _ _ _)
    ((Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).2.1 n x hxF)

/--
lemma `tendsto_apprSeq` / 引理 `tendsto_apprSeq`

English:
lemma tendsto_apprSeq
  proof: (Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).2.2

中文:
引理 tendsto_apprSeq
  证明: (Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).2.2

Depends on / 依赖: Exists, Exists.choose_spec, HasOuterApproxClosed, HasOuterApproxClosed.exAppr, choose_spec, exAppr
-/
lemma tendsto_apprSeq :
    Tendsto (fun n : Nat => (fun x => hF.apprSeq n x)) atTop (𝓝 (indicator F fun _ => (1 : Real>=0))) :=
  (Exists.choose_spec (HasOuterApproxClosed.exAppr F hF)).2.2

/--
lemma `indicator_le_apprSeq` / 引理 `indicator_le_apprSeq`

English:
lemma indicator_le_apprSeq
  given: (n : Nat)
  proof: by
  intro x
  by_cases hxF : x in F
  · simp only [hxF, indicator_of_mem, apprSeq_apply_eq_one hF n, le_refl]
  · simp only [hxF, not_false_eq_true, indicator_of_notMem, zero_le]

中文:
引理 indicator_le_apprSeq
  条件: (n : 自然数)
  证明: by
  intro x
  by_cases hxF : x in F
  · simp only [hxF, indicator_of_mem, apprSeq_apply_eq_one hF n, le_refl]
  · simp only [hxF, not_false_eq_true, indicator_of_notMem, zero_le]

Depends on / 依赖: apprSeq_apply_eq_one, indicator_of_mem, indicator_of_notMem, le_refl, not_false_eq_true, zero_le
-/
lemma indicator_le_apprSeq (n : Nat) :
    indicator F (fun _ => 1) <= hF.apprSeq n := by
  intro x
  by_cases hxF : x in F
  · simp only [hxF, indicator_of_mem, apprSeq_apply_eq_one hF n, le_refl]
  · simp only [hxF, not_false_eq_true, indicator_of_notMem, zero_le]

/--
theorem `measure_le_lintegral` / 定理 `measure_le_lintegral`

English:
theorem measure_le_lintegral
  given: [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) (n : Nat)
  proof: by
  convert_to ∫⁻ x, (F.indicator (fun _ => (1 : Real>=0∞))) x ∂μ <= ∫⁻ x, hF.apprSeq n x ∂μ
  · rw [lintegral_indicator hF.measurableSet]
    simp only [lintegral_one, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
  · apply lintegral_mono
    intro x
    by_cases hxF : x in F
    · simp 

中文:
定理 measure_le_lintegral
  条件: [可测空间 X] [OpensMeasurable空间 X] (μ : 测度 X) (n : 自然数)
  证明: by
  convert_to ∫⁻ x, (F.indicator (fun _ => (1 : Real>=0∞))) x ∂μ <= ∫⁻ x, hF.apprSeq n x ∂μ
  · rw [lintegral_indicator hF.measurableSet]
    simp only [lintegral_one, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
  · apply lintegral_mono
    intro x
    by_cases hxF : x in F
    · simp 

Depends on / 依赖: ENNReal, ENNReal.coe_one, F.indicator, MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_apply, apprSeq, apprSeq_apply_eq_one, coe_one, convert_to, hF.apprSeq, hF.measurableSet, indicator, indicator_of_mem, indicator_of_notMem, le_refl, lintegral_indicator, lintegral_mono, lintegral_one
-/
theorem measure_le_lintegral [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) (n : Nat) :
    μ F <= ∫⁻ x, (hF.apprSeq n x : Real>=0∞) ∂μ := by
  convert_to ∫⁻ x, (F.indicator (fun _ => (1 : Real>=0∞))) x ∂μ <= ∫⁻ x, hF.apprSeq n x ∂μ
  · rw [lintegral_indicator hF.measurableSet]
    simp only [lintegral_one, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
  · apply lintegral_mono
    intro x
    by_cases hxF : x in F
    · simp only [hxF, indicator_of_mem, apprSeq_apply_eq_one hF n hxF, ENNReal.coe_one, le_refl]
    · simp only [hxF, not_false_eq_true, indicator_of_notMem, zero_le]

/--
lemma `tendsto_lintegral_apprSeq` / 引理 `tendsto_lintegral_apprSeq`

English:
lemma tendsto_lintegral_apprSeq
  statement: [MeasurableSpace X] [OpensMeasurableSpace X]
  proof: measure_of_cont_bdd_of_tendsto_indicator μ hF.measurableSet hF.apprSeq
    (apprSeq_apply_le_one hF) (tendsto_apprSeq hF)

中文:
引理 tendsto_lintegral_apprSeq
  结论: [可测空间 X] [OpensMeasurable空间 X]
  证明: measure_of_cont_bdd_of_tendsto_indicator μ hF.measurableSet hF.apprSeq
    (apprSeq_apply_le_one hF) (tendsto_apprSeq hF)

Depends on / 依赖: apprSeq, apprSeq_apply_le_one, hF.apprSeq, hF.measurableSet, measurableSet, measure_of_cont_bdd_of_tendsto_indicator, tendsto_apprSeq
-/
lemma tendsto_lintegral_apprSeq [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    Tendsto (fun n => ∫⁻ x, hF.apprSeq n x ∂μ) atTop (𝓝 ((μ : Measure X) F)) :=
  measure_of_cont_bdd_of_tendsto_indicator μ hF.measurableSet hF.apprSeq
    (apprSeq_apply_le_one hF) (tendsto_apprSeq hF)

end HasOuterApproxClosed --namespace

noncomputable instance (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] : HasOuterApproxClosed X := by
  let : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  refine ⟨fun F hF => ?_⟩
  use fun n => thickenedIndicator (δ := (1 : Real) / (n + 1)) Nat.one_div_pos_of_nat F
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · exact fun n x => thickenedIndicator_le_one Nat.one_div_pos_of_nat F x
  · exact fun n x hxF => one_le_thickenedIndicator_apply X Nat.one_div_pos_of_nat hxF
  · have key := thickenedIndicator_tendsto_indicator_closure
              (δseq := fun (n : Nat) => (1 : Real) / (n + 1))
              (fun _ => Nat.one_div_pos_of_nat) tendsto_one_div_add_atTop_nhds_zero_nat F
    rw [tendsto_pi_nhds] at *
    intro x
    nth_rw 2 [← IsClosed.closure_eq hF]
    exact key x

namespace MeasureTheory

/--
theorem `measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure` / 定理 `measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure`

English:
theorem measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure
  statement: {Ω : Type*}
  proof: by
  have ν_finite : IsFiniteMeasure ν := by
    constructor
    have whole := h 1
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, ENNReal.coe_one, lintegral_const,
      one_mul] at whole
    simp [← whole]
  have obs_μ := HasOuterApproxClosed.tendsto_lintegral_apprSeq F_closed μ
  

中文:
定理 measure_isClosed_eq_of_对任意_lintegral_eq_of_isFiniteMeasure
  结论: {Ω : 类型}
  证明: by
  have ν_finite : IsFiniteMeasure ν := by
    constructor
    have whole := h 1
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, ENNReal.coe_one, lintegral_const,
      one_mul] at whole
    simp [← whole]
  have obs_μ := HasOuterApproxClosed.tendsto_lintegral_apprSeq F_closed μ
  

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.coe_one, ENNReal, ENNReal.coe_one, F_closed, HasOuterApproxClosed, HasOuterApproxClosed.tendsto_lintegral_apprSeq, IsFiniteMeasure, Pi.one_apply, coe_one, lintegral_const, one_apply, one_mul, simp_rw, tendsto_lintegral_apprSeq, tendsto_nhds_unique
-/
theorem measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure {Ω : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [OpensMeasurableSpace Ω] {μ ν : Measure Ω} [IsFiniteMeasure μ]
    (h : forall (f : Ω ->ᵇ Real>=0), ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν) {F : Set Ω} (F_closed : IsClosed F) :
    μ F = ν F := by
  have ν_finite : IsFiniteMeasure ν := by
    constructor
    have whole := h 1
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, ENNReal.coe_one, lintegral_const,
      one_mul] at whole
    simp [← whole]
  have obs_μ := HasOuterApproxClosed.tendsto_lintegral_apprSeq F_closed μ
  have obs_ν := HasOuterApproxClosed.tendsto_lintegral_apprSeq F_closed ν
  simp_rw [h] at obs_μ
  exact tendsto_nhds_unique obs_μ obs_ν

/--
theorem `ext_of_forall_lintegral_eq_of_IsFiniteMeasure` / 定理 `ext_of_forall_lintegral_eq_of_IsFiniteMeasure`

English:
theorem ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  statement: {Ω : Type*}
  proof: by
  have key := @measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure Ω _ _ _ _ μ ν _ h
  apply ext_of_generate_finite _ ?_ isPiSystem_isClosed
  · exact fun F F_closed => key F_closed
  · exact key isClosed_univ
  · rw [BorelSpace.measurable_eq (α := Ω), borel_eq_generateFrom_isClosed]

中文:
定理 ext_of_对任意_lintegral_eq_of_IsFiniteMeasure
  结论: {Ω : 类型}
  证明: by
  have key := @measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure Ω _ _ _ _ μ ν _ h
  apply ext_of_generate_finite _ ?_ isPiSystem_isClosed
  · exact fun F F_closed => key F_closed
  · exact key isClosed_univ
  · rw [BorelSpace.measurable_eq (α := Ω), borel_eq_generateFrom_isClosed]

Depends on / 依赖: BorelSpace, BorelSpace.measurable_eq, F_closed, borel_eq_generateFrom_isClosed, ext_of_generate_finite, isClosed_univ, isPiSystem_isClosed, measurable_eq, measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure
-/
theorem ext_of_forall_lintegral_eq_of_IsFiniteMeasure {Ω : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [BorelSpace Ω] {μ ν : Measure Ω} [IsFiniteMeasure μ]
    (h : forall (f : Ω ->ᵇ Real>=0), ∫⁻ x, f x ∂μ = ∫⁻ x, f x ∂ν) :
    μ = ν := by
  have key := @measure_isClosed_eq_of_forall_lintegral_eq_of_isFiniteMeasure Ω _ _ _ _ μ ν _ h
  apply ext_of_generate_finite _ ?_ isPiSystem_isClosed
  · exact fun F F_closed => key F_closed
  · exact key isClosed_univ
  · rw [BorelSpace.measurable_eq (α := Ω), borel_eq_generateFrom_isClosed]

/--
theorem `ext_of_forall_integral_eq_of_IsFiniteMeasure` / 定理 `ext_of_forall_integral_eq_of_IsFiniteMeasure`

English:
theorem ext_of_forall_integral_eq_of_IsFiniteMeasure
  statement: {Ω : Type*}
  proof: by
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  apply (ENNReal.toReal_eq_toReal_iff' (lintegral_lt_top_of_nnreal μ f).ne
      (lintegral_lt_top_of_nnreal ν f).ne).mp
  rw [toReal_lintegral_coe_eq_integral f μ]; rw [toReal_lintegral_coe_eq_integral f ν]
  exact h ⟨⟨fun x => (f x

中文:
定理 ext_of_对任意_integral_eq_of_IsFiniteMeasure
  结论: {Ω : 类型}
  证明: by
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  apply (ENNReal.toReal_eq_toReal_iff' (lintegral_lt_top_of_nnreal μ f).ne
      (lintegral_lt_top_of_nnreal ν f).ne).mp
  rw [toReal_lintegral_coe_eq_integral f μ]; rw [toReal_lintegral_coe_eq_integral f ν]
  exact h ⟨⟨fun x => (f x

Depends on / 依赖: Continuous, Continuous.comp, ENNReal, ENNReal.toReal_eq_toReal_iff, NNReal, NNReal.continuous_coe, continuous, continuous_coe, ext_of_forall_lintegral_eq_of_IsFiniteMeasure, f.continuous, f.map_bounded, lintegral_lt_top_of_nnreal, map_bounded, toReal, toReal_eq_toReal_iff, toReal_lintegral_coe_eq_integral
-/
theorem ext_of_forall_integral_eq_of_IsFiniteMeasure {Ω : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [BorelSpace Ω] {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : forall (f : Ω ->ᵇ Real), ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ = ν := by
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  apply (ENNReal.toReal_eq_toReal_iff' (lintegral_lt_top_of_nnreal μ f).ne
      (lintegral_lt_top_of_nnreal ν f).ne).mp
  rw [toReal_lintegral_coe_eq_integral f μ]; rw [toReal_lintegral_coe_eq_integral f ν]
  exact h ⟨⟨fun x => (f x).toReal, Continuous.comp' NNReal.continuous_coe f.continuous⟩,
      f.map_bounded'⟩

end MeasureTheory -- namespace

end HasOuterApproxClosed -- section
