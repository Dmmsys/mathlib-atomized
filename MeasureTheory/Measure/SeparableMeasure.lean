/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.SetAlgebra

/-!
# Separable measure

The goal of this file is to give a sufficient condition on the measure space `(X, μ)` and the
`NormedAddCommGroup E` for the space `MeasureTheory.Lp E p μ` to have `SecondCountableTopology` when
`1 ≤ p < ∞`. To do so we define the notion of a `MeasureTheory.MeasureDense` family and a
separable measure (`MeasureTheory.IsSeparable`).
We prove that if `X` is `MeasurableSpace.CountablyGenerated` and `μ` is s-finite, then `μ`
is separable. We then prove that if `μ` is separable and `E` is second-countable,
then `Lp E p μ` is second-countable.

A family `𝒜` of subsets of `X` is said to be **measure-dense** if it contains only measurable sets
and can approximate any measurable set with finite measure, in the sense that
for any measurable set `s` such that `μ s ≠ ∞`, `μ (s ∆ t)` can be made
arbitrarily small when `t ∈ 𝒜`. We show below that such a family can be chosen to contain only
sets with finite measure.
The term "measure-dense" is justified by the fact that the approximating condition translates
to the usual notion of density in the metric space made by constant indicators of measurable sets
equipped with the `Lᵖ` norm.

A measure `μ` is **separable** if it admits a countable and measure-dense family of sets.
The term "separable" is justified by the fact that the definition translates to the usual notion
of separability in the metric space made by constant indicators equipped with the `Lᵖ` norm.

## Main definitions

* `MeasureTheory.Measure.MeasureDense μ 𝒜`: `𝒜` is a measure-dense family if it only contains
  measurable sets and if the following condition is satisfied: if `s` is measurable with finite
  measure, then for any `ε > 0` there exists `t ∈ 𝒜` such that `μ (s ∆ t) < ε`.
* `MeasureTheory.IsSeparable`: A measure is separable if there exists a countable and
  measure-dense family.

## Main statements

* `MeasureTheory.instSecondCountableLp`: If `μ` is separable, `E` is second-countable and
  `1 ≤ p < ∞` then `Lp E p μ` is second-countable. This is in particular true if `X` is countably
  generated and `μ` is s-finite.

## Implementation notes

Through the whole file we consider a measurable space `X` equipped with a measure `μ`, and also
a normed commutative group `E`. We also consider an extended non-negative real `p` such that
`1 ≤ p < ∞`. This is registered as instances via `one_le_p : Fact (1 ≤ p)` and
`p_ne_top : Fact (p ≠ ∞)`, so the properties are accessible via `one_le_p.elim` and `p_ne_top.elim`.

Through the whole file, when we write that an extended non-negative real is finite, it is always
written `≠ ∞` rather than `< ∞`. See `Ne.lt_top` and `ne_of_lt` to switch from one to the other.

## References

* [D. L. Cohn, *Measure Theory*][cohn2013measure]

## Tags

separable measure, measure-dense, Lp space, second-countable
-/

public section

open MeasurableSpace Set ENNReal TopologicalSpace symmDiff Real

namespace MeasureTheory

variable {X E : Type*} [m : MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}
variable {p : Real>=0∞} [one_le_p : Fact (1 <= p)] [p_ne_top : Fact (p != ∞)] {𝒜 : Set (Set X)}

section MeasureDense

/-! ### Definition of a measure-dense family, basic properties and sufficient conditions -/

/--
Definition of `Measure.MeasureDense` / `Measure.MeasureDense` 的定义

English:
structure Measure.MeasureDense
  parameters: (μ : Measure X) (𝒜 : Set (Set X))
  axioms and operations (2):
    - measurable : forall s in 𝒜, MeasurableSet s
    - approx : forall s, MeasurableSet s -> μ s != ∞ -> forall ε : Real, 0 < ε -> exists t in 𝒜, μ (s ∆ t) < ENNReal.ofReal ε

中文:
结构 测度.测度稠密
  参数: (μ : 测度 X) (𝒜 : 集合 (集合 X))
  公理与运算 (2 个):
    - measurable : 对任意 s in 𝒜, 可测集 s
    - approx : 对任意 s, 可测集 s -> μ s != ∞ -> 对任意 ε : 实数, 0 < ε -> 存在 t in 𝒜, μ (s ∆ t) < 广义非负实数.of实数 ε
-/
structure Measure.MeasureDense (μ : Measure X) (𝒜 : Set (Set X)) : Prop where
  /-- Each set has to be measurable. -/
  measurable : forall s in 𝒜, MeasurableSet s
  /-- Any measurable set can be approximated by sets in the family. -/
  approx : forall s, MeasurableSet s -> μ s != ∞ -> forall ε : Real, 0 < ε -> exists t in 𝒜, μ (s ∆ t) < ENNReal.ofReal ε

/--
theorem `Measure.MeasureDense.nonempty` / 定理 `Measure.MeasureDense.nonempty`

English:
theorem Measure.MeasureDense.nonempty
  given: (h𝒜 : μ.MeasureDense 𝒜)
  statement: 𝒜.Nonempty
  proof: by
  rcases h𝒜.approx ∅ MeasurableSet.empty (by simp) 1 (by simp) with ⟨t, ht, -⟩
  exact ⟨t, ht⟩

中文:
定理 测度.测度稠密.nonempty
  条件: (h𝒜 : μ.测度稠密 𝒜)
  结论: 𝒜.非空
  证明: by
  rcases h𝒜.approx ∅ MeasurableSet.empty (by simp) 1 (by simp) with ⟨t, ht, -⟩
  exact ⟨t, ht⟩

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, approx
-/
theorem Measure.MeasureDense.nonempty (h𝒜 : μ.MeasureDense 𝒜) : 𝒜.Nonempty := by
  rcases h𝒜.approx ∅ MeasurableSet.empty (by simp) 1 (by simp) with ⟨t, ht, -⟩
  exact ⟨t, ht⟩

/--
theorem `Measure.MeasureDense.nonempty'` / 定理 `Measure.MeasureDense.nonempty'`

English:
theorem Measure.MeasureDense.nonempty'
  given: (h𝒜 : μ.MeasureDense 𝒜)
  proof: by
  rcases h𝒜.approx ∅ MeasurableSet.empty (by simp) 1 (by simp) with ⟨t, ht, hμt⟩
  refine ⟨t, ht, ?_⟩
  convert! ne_top_of_lt hμt
  rw [← bot_eq_empty]; rw [bot_symmDiff]

中文:
定理 测度.测度稠密.nonempty'
  条件: (h𝒜 : μ.测度稠密 𝒜)
  证明: by
  rcases h𝒜.approx ∅ MeasurableSet.empty (by simp) 1 (by simp) with ⟨t, ht, hμt⟩
  refine ⟨t, ht, ?_⟩
  convert! ne_top_of_lt hμt
  rw [← bot_eq_empty]; rw [bot_symmDiff]

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, approx, bot_eq_empty, bot_symmDiff, convert, ne_top_of_lt
-/
theorem Measure.MeasureDense.nonempty' (h𝒜 : μ.MeasureDense 𝒜) :
    {s | s in 𝒜 ∧ μ s != ∞}.Nonempty := by
  rcases h𝒜.approx ∅ MeasurableSet.empty (by simp) 1 (by simp) with ⟨t, ht, hμt⟩
  refine ⟨t, ht, ?_⟩
  convert! ne_top_of_lt hμt
  rw [← bot_eq_empty]; rw [bot_symmDiff]

/--
theorem `measureDense_measurableSet` / 定理 `measureDense_measurableSet`

English:
theorem measureDense_measurableSet
  statement: μ.MeasureDense {s | MeasurableSet s} where
  proof: h
  approx s hs _ ε ε_pos := ⟨s, hs, by simpa⟩

中文:
定理 measureDense_measurableSet
  结论: μ.测度稠密 {s | 可测集 s} where
  证明: h
  approx s hs _ ε ε_pos := ⟨s, hs, by simpa⟩
-/
theorem measureDense_measurableSet : μ.MeasureDense {s | MeasurableSet s} where
  measurable _ h := h
  approx s hs _ ε ε_pos := ⟨s, hs, by simpa⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Measure.MeasureDense.completion` / 定理 `Measure.MeasureDense.completion`

English:
theorem Measure.MeasureDense.completion
  given: (h𝒜 : μ.MeasureDense 𝒜)
  statement: μ.completion.MeasureDense 𝒜 where
  proof: (h𝒜.measurable s hs).nullMeasurableSet
  approx s hs hμs ε ε_pos := by
    obtain ⟨t, ht, hμst⟩ :=
      h𝒜.approx (toMeasurable μ s) (measurableSet_toMeasurable μ s) (by simpa) ε ε_pos
    refine ⟨t, ht, ?_⟩
    convert! hμst using 1
    rw [completion_apply]
exact measure_congr ae_eq_set_symmDiff (NullMeasurableSet.toMeasurable_ae_eq hs).symm
      Filter.EventuallyEq.rfl

中文:
定理 测度.测度稠密.completion
  条件: (h𝒜 : μ.测度稠密 𝒜)
  结论: μ.completion.测度稠密 𝒜 where
  证明: (h𝒜.measurable s hs).nullMeasurableSet
  approx s hs hμs ε ε_pos := by
    obtain ⟨t, ht, hμst⟩ :=
      h𝒜.approx (toMeasurable μ s) (measurableSet_toMeasurable μ s) (by simpa) ε ε_pos
    refine ⟨t, ht, ?_⟩
    convert! hμst using 1
    rw [completion_apply]
exact measure_congr ae_eq_set_symmDiff (NullMeasurableSet.toMeasurable_ae_eq hs).symm
      Filter.EventuallyEq.rfl

Depends on / 依赖: measurable, nullMeasurableSet
-/
theorem Measure.MeasureDense.completion (h𝒜 : μ.MeasureDense 𝒜) : μ.completion.MeasureDense 𝒜 where
  measurable s hs := (h𝒜.measurable s hs).nullMeasurableSet
  approx s hs hμs ε ε_pos := by
    obtain ⟨t, ht, hμst⟩ :=
      h𝒜.approx (toMeasurable μ s) (measurableSet_toMeasurable μ s) (by simpa) ε ε_pos
    refine ⟨t, ht, ?_⟩
    convert! hμst using 1
    rw [completion_apply]
exact measure_congr ae_eq_set_symmDiff (NullMeasurableSet.toMeasurable_ae_eq hs).symm
      Filter.EventuallyEq.rfl

/--
lemma `Measure.MeasureDense.fin_meas_approx` / 引理 `Measure.MeasureDense.fin_meas_approx`

English:
lemma Measure.MeasureDense.fin_meas_approx
  statement: (h𝒜 : μ.MeasureDense 𝒜) {s : Set X}
  proof: by
  rcases h𝒜.approx s ms hμs ε ε_pos with ⟨t, t_mem, ht⟩
  exact ⟨t, t_mem, (measure_ne_top_iff_of_symmDiff <| ne_top_of_lt ht).1 hμs, ht⟩

中文:
引理 测度.测度稠密.fin_meas_approx
  结论: (h𝒜 : μ.测度稠密 𝒜) {s : 集合 X}
  证明: by
  rcases h𝒜.approx s ms hμs ε ε_pos with ⟨t, t_mem, ht⟩
  exact ⟨t, t_mem, (measure_ne_top_iff_of_symmDiff <| ne_top_of_lt ht).1 hμs, ht⟩

Depends on / 依赖: approx, measure_ne_top_iff_of_symmDiff, ne_top_of_lt, t_mem
-/
lemma Measure.MeasureDense.fin_meas_approx (h𝒜 : μ.MeasureDense 𝒜) {s : Set X}
    (ms : MeasurableSet s) (hμs : μ s != ∞) (ε : Real) (ε_pos : 0 < ε) :
    exists t in 𝒜, μ t != ∞ ∧ μ (s ∆ t) < ENNReal.ofReal ε := by
  rcases h𝒜.approx s ms hμs ε ε_pos with ⟨t, t_mem, ht⟩
  exact ⟨t, t_mem, (measure_ne_top_iff_of_symmDiff <| ne_top_of_lt ht).1 hμs, ht⟩

variable (p) in
/--
theorem `Measure.MeasureDense.indicatorConstLp_subset_closure` / 定理 `Measure.MeasureDense.indicatorConstLp_subset_closure`

English:
theorem Measure.MeasureDense.indicatorConstLp_subset_closure
  given: (h𝒜 : μ.MeasureDense 𝒜) (c : E)
  proof: by
  obtain rfl | hc := eq_or_ne c 0
  · refine Subset.trans ?_ subset_closure
    rintro - ⟨s, ms, hμs, rfl⟩
    obtain ⟨t, ht, hμt⟩ := h𝒜.nonempty'
    refine ⟨t, ht, hμt, ?_⟩
    simp_rw [indicatorConstLp]
    simp
  · have p_pos : 0 < p := lt_of_lt_of_le (by simp) one_le_p.elim
    rintro - ⟨s, ms, hμs, rfl⟩
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    have aux : 0 < (ε / ‖c‖) ^ p.toReal := rpow_pos_of_pos (div_pos hε (norm_pos_iff.2 hc)) _
    obtain ⟨t, ht, hμt, hμst⟩ := h𝒜.fin_meas_approx ms hμs ((ε / ‖c‖) ^ p.toReal) aux
    refine ⟨indicatorConstLp p (h𝒜.measurable t ht) hμt c,
      ⟨t, ht, hμt, rfl⟩, ?_⟩
    rw [dist_indicatorConstLp_eq_norm]; rw [norm_indicatorConstLp p_pos.ne.symm p_ne_top.elim]
    calc
      ‖c‖ * μ.real (s ∆ t) ^ (1 / p.toReal)
        < ‖c‖ * (ENNReal.ofReal ((ε / ‖c‖) ^ p.toReal)).toReal ^ (1 / p.toReal) := by
          have := toReal_pos p_pos.ne.symm p_ne_top.elim
          rw [measureReal_def]
          gcongr
          exact ofReal_ne_top
      _ = ε := by
        rw [toReal_ofReal (by positivity)]; rw [one_div]; rw [Real.rpow_rpow_inv (by positivity) (toReal_pos p_pos.ne.symm p_ne_top.elim).ne']; rw [mul_div_cancel₀ _ (norm_ne_zero_iff.2 hc)]

中文:
定理 测度.测度稠密.indicatorConstLp_subset_closure
  条件: (h𝒜 : μ.测度稠密 𝒜) (c : E)
  证明: by
  obtain rfl | hc := eq_or_ne c 0
  · refine Subset.trans ?_ subset_closure
    rintro - ⟨s, ms, hμs, rfl⟩
    obtain ⟨t, ht, hμt⟩ := h𝒜.nonempty'
    refine ⟨t, ht, hμt, ?_⟩
    simp_rw [indicatorConstLp]
    simp
  · have p_pos : 0 < p := lt_of_lt_of_le (by simp) one_le_p.elim
    rintro - ⟨s, ms, hμs, rfl⟩
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    have aux : 0 < (ε / ‖c‖) ^ p.toReal := rpow_pos_of_pos (div_pos hε (norm_pos_iff.2 hc)) _
    obtain ⟨t, ht, hμt, hμst⟩ := h𝒜.fin_meas_approx ms hμs ((ε / ‖c‖) ^ p.toReal) aux
    refine ⟨indicatorConstLp p (h𝒜.measurable t ht) hμt c,
      ⟨t, ht, hμt, rfl⟩, ?_⟩
    rw [dist_indicatorConstLp_eq_norm]; rw [norm_indicatorConstLp p_pos.ne.symm p_ne_top.elim]
    calc
      ‖c‖ * μ.real (s ∆ t) ^ (1 / p.toReal)
        < ‖c‖ * (ENNReal.ofReal ((ε / ‖c‖) ^ p.toReal)).toReal ^ (1 / p.toReal) := by
          have := toReal_pos p_pos.ne.symm p_ne_top.elim
          rw [measureReal_def]
          gcongr
          exact ofReal_ne_top
      _ = ε := by
        rw [toReal_ofReal (by positivity)]; rw [one_div]; rw [Real.rpow_rpow_inv (by positivity) (toReal_pos p_pos.ne.symm p_ne_top.elim).ne']; rw [mul_div_cancel₀ _ (norm_ne_zero_iff.2 hc)]

Depends on / 依赖: Metric, Metric.mem_closure_iff, Subset, Subset.trans, div_pos, eq_or_ne, fin_meas_approx, indicatorConstLp, lt_of_lt_of_le, mem_closure_iff, nonempty, norm_pos_iff, one_le_p, one_le_p.elim, p.toReal, p_pos, rpow_pos_of_pos, simp_rw, subset_closure, toReal
-/
theorem Measure.MeasureDense.indicatorConstLp_subset_closure (h𝒜 : μ.MeasureDense 𝒜) (c : E) :
    {indicatorConstLp p hs hμs c | (s : Set X) (hs : MeasurableSet s) (hμs : μ s != ∞)} subseteq
    closure {indicatorConstLp p (h𝒜.measurable s hs) hμs c |
      (s : Set X) (hs : s in 𝒜) (hμs : μ s != ∞)} := by
  obtain rfl | hc := eq_or_ne c 0
  · refine Subset.trans ?_ subset_closure
    rintro - ⟨s, ms, hμs, rfl⟩
    obtain ⟨t, ht, hμt⟩ := h𝒜.nonempty'
    refine ⟨t, ht, hμt, ?_⟩
    simp_rw [indicatorConstLp]
    simp
  · have p_pos : 0 < p := lt_of_lt_of_le (by simp) one_le_p.elim
    rintro - ⟨s, ms, hμs, rfl⟩
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    have aux : 0 < (ε / ‖c‖) ^ p.toReal := rpow_pos_of_pos (div_pos hε (norm_pos_iff.2 hc)) _
    obtain ⟨t, ht, hμt, hμst⟩ := h𝒜.fin_meas_approx ms hμs ((ε / ‖c‖) ^ p.toReal) aux
    refine ⟨indicatorConstLp p (h𝒜.measurable t ht) hμt c,
      ⟨t, ht, hμt, rfl⟩, ?_⟩
    rw [dist_indicatorConstLp_eq_norm]; rw [norm_indicatorConstLp p_pos.ne.symm p_ne_top.elim]
    calc
      ‖c‖ * μ.real (s ∆ t) ^ (1 / p.toReal)
        < ‖c‖ * (ENNReal.ofReal ((ε / ‖c‖) ^ p.toReal)).toReal ^ (1 / p.toReal) := by
          have := toReal_pos p_pos.ne.symm p_ne_top.elim
          rw [measureReal_def]
          gcongr
          exact ofReal_ne_top
      _ = ε := by
        rw [toReal_ofReal (by positivity)]; rw [one_div]; rw [Real.rpow_rpow_inv (by positivity) (toReal_pos p_pos.ne.symm p_ne_top.elim).ne']; rw [mul_div_cancel₀ _ (norm_ne_zero_iff.2 hc)]

/--
theorem `Measure.MeasureDense.fin_meas` / 定理 `Measure.MeasureDense.fin_meas`

English:
theorem Measure.MeasureDense.fin_meas
  given: (h𝒜 : μ.MeasureDense 𝒜)
  proof: h𝒜.measurable s h.1
  approx s ms hμs ε ε_pos := by
    rcases Measure.MeasureDense.fin_meas_approx h𝒜 ms hμs ε ε_pos with ⟨t, t_mem, hμt, hμst⟩
    exact ⟨t, ⟨t_mem, hμt⟩, hμst⟩

中文:
定理 测度.测度稠密.fin_meas
  条件: (h𝒜 : μ.测度稠密 𝒜)
  证明: h𝒜.measurable s h.1
  approx s ms hμs ε ε_pos := by
    rcases Measure.MeasureDense.fin_meas_approx h𝒜 ms hμs ε ε_pos with ⟨t, t_mem, hμt, hμst⟩
    exact ⟨t, ⟨t_mem, hμt⟩, hμst⟩

Depends on / 依赖: measurable
-/
theorem Measure.MeasureDense.fin_meas (h𝒜 : μ.MeasureDense 𝒜) :
    μ.MeasureDense {s | s in 𝒜 ∧ μ s != ∞} where
  measurable s h := h𝒜.measurable s h.1
  approx s ms hμs ε ε_pos := by
    rcases Measure.MeasureDense.fin_meas_approx h𝒜 ms hμs ε ε_pos with ⟨t, t_mem, hμt, hμst⟩
    exact ⟨t, ⟨t_mem, hμt⟩, hμst⟩

variable (μ) in
/--
theorem `Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite` / 定理 `Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite`

English:
theorem Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
  statement: [IsFiniteMeasure μ]
  proof: hgen ▸ measurableSet_generateFrom hs
  approx s ms := by
    -- We want to show that any measurable set can be approximated by sets in `𝒜`. To do so, it is
    -- enough to show that such sets constitute a `σ`-algebra containing `𝒜`. This is contained in
    -- the theorem `generateFrom_induction`.
    have : MeasurableSet s ∧ forall (ε : Real), 0 < ε -> exists t in 𝒜, μ.real (s ∆ t) < ε := by
      rw [hgen] at ms
      induction s, ms using generateFrom_induction with
      -- If `t ∈ 𝒜`, then `μ (t ∆ t) = 0` which is less than any `ε > 0`.
      | hC t t_mem _ =>
        exact ⟨hgen ▸ measurableSet_generateFrom t_mem, fun ε ε_pos => ⟨t, t_mem, by simpa⟩⟩
      -- `∅ ∈ 𝒜` and `μ (∅ ∆ ∅) = 0` which is less than any `ε > 0`.
      | empty => exact ⟨MeasurableSet.empty, fun ε ε_pos => ⟨∅, h𝒜.empty_mem, by simpa⟩⟩
      -- If `s` is measurable and `t ∈ 𝒜` such that `μ (s ∆ t) < ε`, then `tᶜ ∈ 𝒜` and
      -- `μ (sᶜ ∆ tᶜ) = μ (s ∆ t) < ε` so `sᶜ` can be approximated.
      | compl t _ ht =>
        refine ⟨ht.1.compl, fun ε ε_pos => ?_⟩
        obtain ⟨u, u_mem, hμtcu⟩ := ht.2 ε ε_pos
        exact ⟨uᶜ, h𝒜.compl_mem u_mem, by rwa [compl_symmDiff_compl]⟩
      -- Let `(fₙ)` be a sequence of measurable sets and `ε > 0`.
      | iUnion f _ hf =>
        refine ⟨MeasurableSet.iUnion (fun n => (hf n).1), fun ε ε_pos => ?_⟩
        -- We have `μ (⋃ n ≤ N, fₙ) ⟶ μ (⋃ n, fₙ)`.
        have := tendsto_measure_iUnion_accumulate (μ := μ) (f := f)
        rw [← tendsto_toReal_iff (fun _ => measure_ne_top _ _) (measure_ne_top _ _)] at this
        -- So there exists `N` such that `μ (⋃ n, fₙ) - μ (⋃ n ≤ N, fₙ) < ε/2`.
        rcases Metric.tendsto_atTop.1 this (ε / 2) (by linarith [ε_pos]) with ⟨N, hN⟩
        -- For any `n ≤ N` there exists `gₙ ∈ 𝒜` such that `μ (fₙ ∆ gₙ) < ε/(2*(N+1))`.
        choose g g_mem hg using fun n => (hf n).2 (ε / (2 * (N + 1))) (div_pos ε_pos (by linarith))
        -- Therefore we have
        -- `μ ((⋃ n, fₙ) ∆ (⋃ n ≤ N, gₙ))`
        -- `≤ μ ((⋃ n, fₙ) ∆ (⋃ n ≤ N, fₙ)) + μ ((⋃ n ≤ N, fₙ) ∆ (⋃ n ≤ N, gₙ))`
        -- `< ε/2 + ∑ n ≤ N, μ (fₙ ∆ gₙ)` (see `biSup_symmDiff_biSup_le`)
        -- `< ε/2 + (N+1)*ε/(2*(N+1)) = ε/2`.
        refine ⟨⋃ n in Finset.range (N + 1), g n, h𝒜.biUnion_mem _ (fun i _ => g_mem i), ?_⟩
        calc
          μ.real ((⋃ n, f n) ∆ (⋃ n in (Finset.range (N + 1)), g n))
            <= (μ ((⋃ n, f n) \ ((⋃ n in (Finset.range (N + 1)), f n)) union
              ((⋃ n in (Finset.range (N + 1)), f n) ∆
              (⋃ n in (Finset.range (N + 1)), g ↑n)))).toReal :=
                toReal_mono (measure_ne_top _ _)
                  (measure_mono <| symmDiff_of_ge (iUnion_subset <|
                  fun i => iUnion_subset (fun _ => subset_iUnion f i)) ▸ symmDiff_triangle ..)
          _ <= (μ ((⋃ n, f n) \
              ((⋃ n in (Finset.range (N + 1)), f n)))).toReal +
              (μ ((⋃ n in (Finset.range (N + 1)), f n) ∆
              (⋃ n in (Finset.range (N + 1)), g ↑n))).toReal := by
                rw [← toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
exact toReal_mono (add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
                  measure_union_le _ _
          _ < ε := by
                rw [← add_halves ε]
                apply _root_.add_lt_add
                · rw [measure_sdiff (h_fin := measure_ne_top _ _),
                    toReal_sub_of_le (ha := measure_ne_top _ _)]
                  · apply lt_of_le_of_lt (sub_le_dist ..)
                    simp only [Finset.mem_range, Nat.lt_add_one_iff]
                    exact (dist_comm (α := Real) .. ▸ hN N (le_refl N))
· exact measure_mono iUnion_subset
                      fun i => iUnion_subset fun _ => subset_iUnion f i
· exact iUnion_subset fun i => iUnion_subset (fun _ => subset_iUnion f i)
                  · exact MeasurableSet.biUnion (countable_coe_iff.1 inferInstance)
                      (fun n _ => (hf n).1.nullMeasurableSet)
                · calc
                    (μ ((⋃ n in (Finset.range (N + 1)), f n) ∆
                    (⋃ n in (Finset.range (N + 1)), g ↑n))).toReal
                      <= μ.real (⋃ n in (Finset.range (N + 1)), f n ∆ g n) :=
                          toReal_mono (measure_ne_top _ _) (measure_mono biSup_symmDiff_biSup_le)
                    _ <= ∑ n in Finset.range (N + 1), μ.real (f n ∆ g n) := by
                          simp_rw [measureReal_def, ← toReal_sum (fun _ _ => measure_ne_top _ _)]
                          exact toReal_mono (ne_of_lt <| sum_lt_top.2 fun _ _ => measure_lt_top μ _)
                            (measure_biUnion_finset_le _ _)
                    _ < ∑ n in Finset.range (N + 1), (ε / (2 * (N + 1))) :=
                          Finset.sum_lt_sum (fun i _ => le_of_lt (hg i)) ⟨0, by simp, hg 0⟩
                    _ <= ε / 2 := by
                          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                            Nat.cast_add, Nat.cast_one]
                          rw [div_mul_eq_div_mul_one_div]; rw [← mul_assoc]; rw [mul_comm ((N : Real) + 1)]; rw [mul_assoc]
exact mul_le_of_le_one_right (by linarith [ε_pos])
le_of_eq mul_one_div_cancel Nat.cast_add_one_ne_zero _
    rintro - ε ε_pos
    rcases this.2 ε ε_pos with ⟨t, t_mem, hμst⟩
    exact ⟨t, t_mem, (lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).2 hμst⟩

中文:
定理 测度.测度稠密.of_generateFrom_isSetAlgebra_finite
  结论: [是有限测度 μ]
  证明: hgen ▸ measurableSet_generateFrom hs
  approx s ms := by
    -- We want to show that any measurable set can be approximated by sets in `𝒜`. To do so, it is
    -- enough to show that such sets constitute a `σ`-algebra containing `𝒜`. This is contained in
    -- the theorem `generateFrom_induction`.
    have : MeasurableSet s ∧ forall (ε : Real), 0 < ε -> exists t in 𝒜, μ.real (s ∆ t) < ε := by
      rw [hgen] at ms
      induction s, ms using generateFrom_induction with
      -- If `t ∈ 𝒜`, then `μ (t ∆ t) = 0` which is less than any `ε > 0`.
      | hC t t_mem _ =>
        exact ⟨hgen ▸ measurableSet_generateFrom t_mem, fun ε ε_pos => ⟨t, t_mem, by simpa⟩⟩
      -- `∅ ∈ 𝒜` and `μ (∅ ∆ ∅) = 0` which is less than any `ε > 0`.
      | empty => exact ⟨MeasurableSet.empty, fun ε ε_pos => ⟨∅, h𝒜.empty_mem, by simpa⟩⟩
      -- If `s` is measurable and `t ∈ 𝒜` such that `μ (s ∆ t) < ε`, then `tᶜ ∈ 𝒜` and
      -- `μ (sᶜ ∆ tᶜ) = μ (s ∆ t) < ε` so `sᶜ` can be approximated.
      | compl t _ ht =>
        refine ⟨ht.1.compl, fun ε ε_pos => ?_⟩
        obtain ⟨u, u_mem, hμtcu⟩ := ht.2 ε ε_pos
        exact ⟨uᶜ, h𝒜.compl_mem u_mem, by rwa [compl_symmDiff_compl]⟩
      -- Let `(fₙ)` be a sequence of measurable sets and `ε > 0`.
      | iUnion f _ hf =>
        refine ⟨MeasurableSet.iUnion (fun n => (hf n).1), fun ε ε_pos => ?_⟩
        -- We have `μ (⋃ n ≤ N, fₙ) ⟶ μ (⋃ n, fₙ)`.
        have := tendsto_measure_iUnion_accumulate (μ := μ) (f := f)
        rw [← tendsto_toReal_iff (fun _ => measure_ne_top _ _) (measure_ne_top _ _)] at this
        -- So there exists `N` such that `μ (⋃ n, fₙ) - μ (⋃ n ≤ N, fₙ) < ε/2`.
        rcases Metric.tendsto_atTop.1 this (ε / 2) (by linarith [ε_pos]) with ⟨N, hN⟩
        -- For any `n ≤ N` there exists `gₙ ∈ 𝒜` such that `μ (fₙ ∆ gₙ) < ε/(2*(N+1))`.
        choose g g_mem hg using fun n => (hf n).2 (ε / (2 * (N + 1))) (div_pos ε_pos (by linarith))
        -- Therefore we have
        -- `μ ((⋃ n, fₙ) ∆ (⋃ n ≤ N, gₙ))`
        -- `≤ μ ((⋃ n, fₙ) ∆ (⋃ n ≤ N, fₙ)) + μ ((⋃ n ≤ N, fₙ) ∆ (⋃ n ≤ N, gₙ))`
        -- `< ε/2 + ∑ n ≤ N, μ (fₙ ∆ gₙ)` (see `biSup_symmDiff_biSup_le`)
        -- `< ε/2 + (N+1)*ε/(2*(N+1)) = ε/2`.
        refine ⟨⋃ n in Finset.range (N + 1), g n, h𝒜.biUnion_mem _ (fun i _ => g_mem i), ?_⟩
        calc
          μ.real ((⋃ n, f n) ∆ (⋃ n in (Finset.range (N + 1)), g n))
            <= (μ ((⋃ n, f n) \ ((⋃ n in (Finset.range (N + 1)), f n)) union
              ((⋃ n in (Finset.range (N + 1)), f n) ∆
              (⋃ n in (Finset.range (N + 1)), g ↑n)))).toReal :=
                toReal_mono (measure_ne_top _ _)
                  (measure_mono <| symmDiff_of_ge (iUnion_subset <|
                  fun i => iUnion_subset (fun _ => subset_iUnion f i)) ▸ symmDiff_triangle ..)
          _ <= (μ ((⋃ n, f n) \
              ((⋃ n in (Finset.range (N + 1)), f n)))).toReal +
              (μ ((⋃ n in (Finset.range (N + 1)), f n) ∆
              (⋃ n in (Finset.range (N + 1)), g ↑n))).toReal := by
                rw [← toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
exact toReal_mono (add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
                  measure_union_le _ _
          _ < ε := by
                rw [← add_halves ε]
                apply _root_.add_lt_add
                · rw [measure_sdiff (h_fin := measure_ne_top _ _),
                    toReal_sub_of_le (ha := measure_ne_top _ _)]
                  · apply lt_of_le_of_lt (sub_le_dist ..)
                    simp only [Finset.mem_range, Nat.lt_add_one_iff]
                    exact (dist_comm (α := Real) .. ▸ hN N (le_refl N))
· exact measure_mono iUnion_subset
                      fun i => iUnion_subset fun _ => subset_iUnion f i
· exact iUnion_subset fun i => iUnion_subset (fun _ => subset_iUnion f i)
                  · exact MeasurableSet.biUnion (countable_coe_iff.1 inferInstance)
                      (fun n _ => (hf n).1.nullMeasurableSet)
                · calc
                    (μ ((⋃ n in (Finset.range (N + 1)), f n) ∆
                    (⋃ n in (Finset.range (N + 1)), g ↑n))).toReal
                      <= μ.real (⋃ n in (Finset.range (N + 1)), f n ∆ g n) :=
                          toReal_mono (measure_ne_top _ _) (measure_mono biSup_symmDiff_biSup_le)
                    _ <= ∑ n in Finset.range (N + 1), μ.real (f n ∆ g n) := by
                          simp_rw [measureReal_def, ← toReal_sum (fun _ _ => measure_ne_top _ _)]
                          exact toReal_mono (ne_of_lt <| sum_lt_top.2 fun _ _ => measure_lt_top μ _)
                            (measure_biUnion_finset_le _ _)
                    _ < ∑ n in Finset.range (N + 1), (ε / (2 * (N + 1))) :=
                          Finset.sum_lt_sum (fun i _ => le_of_lt (hg i)) ⟨0, by simp, hg 0⟩
                    _ <= ε / 2 := by
                          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                            Nat.cast_add, Nat.cast_one]
                          rw [div_mul_eq_div_mul_one_div]; rw [← mul_assoc]; rw [mul_comm ((N : Real) + 1)]; rw [mul_assoc]
exact mul_le_of_le_one_right (by linarith [ε_pos])
le_of_eq mul_one_div_cancel Nat.cast_add_one_ne_zero _
    rintro - ε ε_pos
    rcases this.2 ε ε_pos with ⟨t, t_mem, hμst⟩
    exact ⟨t, t_mem, (lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).2 hμst⟩

Depends on / 依赖: measurableSet_generateFrom
-/
theorem Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite [IsFiniteMeasure μ]
    (h𝒜 : IsSetAlgebra 𝒜) (hgen : m = MeasurableSpace.generateFrom 𝒜) : μ.MeasureDense 𝒜 where
  measurable s hs := hgen ▸ measurableSet_generateFrom hs
  approx s ms := by
    -- We want to show that any measurable set can be approximated by sets in `𝒜`. To do so, it is
    -- enough to show that such sets constitute a `σ`-algebra containing `𝒜`. This is contained in
    -- the theorem `generateFrom_induction`.
    have : MeasurableSet s ∧ forall (ε : Real), 0 < ε -> exists t in 𝒜, μ.real (s ∆ t) < ε := by
      rw [hgen] at ms
      induction s, ms using generateFrom_induction with
      -- If `t ∈ 𝒜`, then `μ (t ∆ t) = 0` which is less than any `ε > 0`.
      | hC t t_mem _ =>
        exact ⟨hgen ▸ measurableSet_generateFrom t_mem, fun ε ε_pos => ⟨t, t_mem, by simpa⟩⟩
      -- `∅ ∈ 𝒜` and `μ (∅ ∆ ∅) = 0` which is less than any `ε > 0`.
      | empty => exact ⟨MeasurableSet.empty, fun ε ε_pos => ⟨∅, h𝒜.empty_mem, by simpa⟩⟩
      -- If `s` is measurable and `t ∈ 𝒜` such that `μ (s ∆ t) < ε`, then `tᶜ ∈ 𝒜` and
      -- `μ (sᶜ ∆ tᶜ) = μ (s ∆ t) < ε` so `sᶜ` can be approximated.
      | compl t _ ht =>
        refine ⟨ht.1.compl, fun ε ε_pos => ?_⟩
        obtain ⟨u, u_mem, hμtcu⟩ := ht.2 ε ε_pos
        exact ⟨uᶜ, h𝒜.compl_mem u_mem, by rwa [compl_symmDiff_compl]⟩
      -- Let `(fₙ)` be a sequence of measurable sets and `ε > 0`.
      | iUnion f _ hf =>
        refine ⟨MeasurableSet.iUnion (fun n => (hf n).1), fun ε ε_pos => ?_⟩
        -- We have `μ (⋃ n ≤ N, fₙ) ⟶ μ (⋃ n, fₙ)`.
        have := tendsto_measure_iUnion_accumulate (μ := μ) (f := f)
        rw [← tendsto_toReal_iff (fun _ => measure_ne_top _ _) (measure_ne_top _ _)] at this
        -- So there exists `N` such that `μ (⋃ n, fₙ) - μ (⋃ n ≤ N, fₙ) < ε/2`.
        rcases Metric.tendsto_atTop.1 this (ε / 2) (by linarith [ε_pos]) with ⟨N, hN⟩
        -- For any `n ≤ N` there exists `gₙ ∈ 𝒜` such that `μ (fₙ ∆ gₙ) < ε/(2*(N+1))`.
        choose g g_mem hg using fun n => (hf n).2 (ε / (2 * (N + 1))) (div_pos ε_pos (by linarith))
        -- Therefore we have
        -- `μ ((⋃ n, fₙ) ∆ (⋃ n ≤ N, gₙ))`
        -- `≤ μ ((⋃ n, fₙ) ∆ (⋃ n ≤ N, fₙ)) + μ ((⋃ n ≤ N, fₙ) ∆ (⋃ n ≤ N, gₙ))`
        -- `< ε/2 + ∑ n ≤ N, μ (fₙ ∆ gₙ)` (see `biSup_symmDiff_biSup_le`)
        -- `< ε/2 + (N+1)*ε/(2*(N+1)) = ε/2`.
        refine ⟨⋃ n in Finset.range (N + 1), g n, h𝒜.biUnion_mem _ (fun i _ => g_mem i), ?_⟩
        calc
          μ.real ((⋃ n, f n) ∆ (⋃ n in (Finset.range (N + 1)), g n))
            <= (μ ((⋃ n, f n) \ ((⋃ n in (Finset.range (N + 1)), f n)) union
              ((⋃ n in (Finset.range (N + 1)), f n) ∆
              (⋃ n in (Finset.range (N + 1)), g ↑n)))).toReal :=
                toReal_mono (measure_ne_top _ _)
                  (measure_mono <| symmDiff_of_ge (iUnion_subset <|
                  fun i => iUnion_subset (fun _ => subset_iUnion f i)) ▸ symmDiff_triangle ..)
          _ <= (μ ((⋃ n, f n) \
              ((⋃ n in (Finset.range (N + 1)), f n)))).toReal +
              (μ ((⋃ n in (Finset.range (N + 1)), f n) ∆
              (⋃ n in (Finset.range (N + 1)), g ↑n))).toReal := by
                rw [← toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
exact toReal_mono (add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
                  measure_union_le _ _
          _ < ε := by
                rw [← add_halves ε]
                apply _root_.add_lt_add
                · rw [measure_sdiff (h_fin := measure_ne_top _ _),
                    toReal_sub_of_le (ha := measure_ne_top _ _)]
                  · apply lt_of_le_of_lt (sub_le_dist ..)
                    simp only [Finset.mem_range, Nat.lt_add_one_iff]
                    exact (dist_comm (α := Real) .. ▸ hN N (le_refl N))
· exact measure_mono iUnion_subset
                      fun i => iUnion_subset fun _ => subset_iUnion f i
· exact iUnion_subset fun i => iUnion_subset (fun _ => subset_iUnion f i)
                  · exact MeasurableSet.biUnion (countable_coe_iff.1 inferInstance)
                      (fun n _ => (hf n).1.nullMeasurableSet)
                · calc
                    (μ ((⋃ n in (Finset.range (N + 1)), f n) ∆
                    (⋃ n in (Finset.range (N + 1)), g ↑n))).toReal
                      <= μ.real (⋃ n in (Finset.range (N + 1)), f n ∆ g n) :=
                          toReal_mono (measure_ne_top _ _) (measure_mono biSup_symmDiff_biSup_le)
                    _ <= ∑ n in Finset.range (N + 1), μ.real (f n ∆ g n) := by
                          simp_rw [measureReal_def, ← toReal_sum (fun _ _ => measure_ne_top _ _)]
                          exact toReal_mono (ne_of_lt <| sum_lt_top.2 fun _ _ => measure_lt_top μ _)
                            (measure_biUnion_finset_le _ _)
                    _ < ∑ n in Finset.range (N + 1), (ε / (2 * (N + 1))) :=
                          Finset.sum_lt_sum (fun i _ => le_of_lt (hg i)) ⟨0, by simp, hg 0⟩
                    _ <= ε / 2 := by
                          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                            Nat.cast_add, Nat.cast_one]
                          rw [div_mul_eq_div_mul_one_div]; rw [← mul_assoc]; rw [mul_comm ((N : Real) + 1)]; rw [mul_assoc]
exact mul_le_of_le_one_right (by linarith [ε_pos])
le_of_eq mul_one_div_cancel Nat.cast_add_one_ne_zero _
    rintro - ε ε_pos
    rcases this.2 ε ε_pos with ⟨t, t_mem, hμst⟩
    exact ⟨t, t_mem, (lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).2 hμst⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite` / 定理 `Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite`

English:
theorem Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite
  statement: (h𝒜 : IsSetAlgebra 𝒜)
  proof: hgen ▸ measurableSet_generateFrom hs
  approx s ms hμs ε ε_pos := by
    -- We use partial unions of (Sₙ) to get a monotone family spanning `X`.
    let T := accumulate S.set
    have T_mem (n) : T n in 𝒜 := by
      simpa using! h𝒜.biUnion_mem {k | k <= n}.toFinset (fun k _ => S.set_mem k)
    have T_finite (n) : μ (T n) < ∞ := by
      simpa using! measure_biUnion_lt_top {k | k <= n}.toFinset.finite_toSet
        (fun k _ => S.finite k)
    have T_spanning : ⋃ n, T n = univ := S.spanning ▸ iUnion_accumulate
    -- We use the fact that we already know this is true for finite measures. As `⋃ n, T n = X`,
    -- we have that `μ ((T n) ∩ s) ⟶ μ s`.
    have mono : Monotone (fun n => (T n) inter s) := fun m n hmn => inter_subset_inter_left s
        (biUnion_subset_biUnion_left fun k hkm => Nat.le_trans hkm hmn)
    have := tendsto_measure_iUnion_atTop (μ := μ) mono
    rw [← tendsto_toReal_iff] at this
    · -- We can therefore choose `N` such that `μ s - μ ((S N) ∩ s) < ε/2`.
      rcases Metric.tendsto_atTop.1 this (ε / 2) (by linarith [ε_pos]) with ⟨N, hN⟩
have : Fact (μ (T N) < ∞) := Fact.mk T_finite N
      -- Then we can apply the previous result to the measure `μ ((S N) ∩ •)`.
      -- There exists `t ∈ 𝒜` such that `μ ((S N) ∩ (s ∆ t)) < ε/2`.
      rcases (Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
        (μ.restrict (T N)) h𝒜 hgen).approx s ms
        (ne_of_lt (lt_of_le_of_lt (μ.restrict_apply_le _ s) hμs.lt_top))
        (ε / 2) (by linarith [ε_pos])
        with ⟨t, t_mem, ht⟩
      -- We can then use `t ∩ (S N)`, because `S N ∈ 𝒜` by hypothesis.
      -- `μ (s ∆ (t ∩ S N))`
      -- `≤ μ (s ∆ (s ∩ S N)) + μ ((s ∩ S N) ∆ (t ∩ S N))`
      -- `= μ s - μ (s ∩ S N) + μ (s ∆ t) ∩ S N) < ε`.
      refine ⟨t inter T N, h𝒜.inter_mem t_mem (T_mem N), ?_⟩
      calc
        μ (s ∆ (t inter T N))
          <= μ (s \ (s inter T N)) + μ ((s ∆ t) inter T N) := by
              rw [← symmDiff_of_le (inter_subset_left ..)]; rw [symmDiff_comm _ s]; rw [inter_symmDiff_distrib_right]
              exact measure_symmDiff_le _ _ _
        _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
              apply ENNReal.add_lt_add
              · rw [measure_sdiff
                    (inter_subset_left ..)
                    (ms.inter (hgen ▸ measurableSet_generateFrom (T_mem N))).nullMeasurableSet
                    (ne_top_of_le_ne_top hμs (measure_mono (inter_subset_left ..))),
                  lt_ofReal_iff_toReal_lt (sub_ne_top hμs),
                  toReal_sub_of_le (measure_mono (inter_subset_left ..)) hμs]
                apply lt_of_le_of_lt (sub_le_dist ..)
                nth_rw 1 [← univ_inter s]
                rw [inter_comm s]; rw [dist_comm]; rw [← T_spanning]; rw [iUnion_inter _ T]
                apply hN N (le_refl _)
              · rwa [← μ.restrict_apply' (hgen ▸ measurableSet_generateFrom (T_mem N))]
        _ = ENNReal.ofReal ε := by
              rw [← ofReal_add (by linarith [ε_pos]) (by linarith [ε_pos]), add_halves]
    · exact fun n => ne_top_of_le_ne_top hμs (measure_mono (inter_subset_right ..))
    · exact ne_top_of_le_ne_top hμs
        (measure_mono (iUnion_subset (fun i => inter_subset_right ..)))

中文:
定理 测度.测度稠密.of_generateFrom_isSetAlgebra_sigmaFinite
  结论: (h𝒜 : 是集合代数 𝒜)
  证明: hgen ▸ measurableSet_generateFrom hs
  approx s ms hμs ε ε_pos := by
    -- We use partial unions of (Sₙ) to get a monotone family spanning `X`.
    let T := accumulate S.set
    have T_mem (n) : T n in 𝒜 := by
      simpa using! h𝒜.biUnion_mem {k | k <= n}.toFinset (fun k _ => S.set_mem k)
    have T_finite (n) : μ (T n) < ∞ := by
      simpa using! measure_biUnion_lt_top {k | k <= n}.toFinset.finite_toSet
        (fun k _ => S.finite k)
    have T_spanning : ⋃ n, T n = univ := S.spanning ▸ iUnion_accumulate
    -- We use the fact that we already know this is true for finite measures. As `⋃ n, T n = X`,
    -- we have that `μ ((T n) ∩ s) ⟶ μ s`.
    have mono : Monotone (fun n => (T n) inter s) := fun m n hmn => inter_subset_inter_left s
        (biUnion_subset_biUnion_left fun k hkm => Nat.le_trans hkm hmn)
    have := tendsto_measure_iUnion_atTop (μ := μ) mono
    rw [← tendsto_toReal_iff] at this
    · -- We can therefore choose `N` such that `μ s - μ ((S N) ∩ s) < ε/2`.
      rcases Metric.tendsto_atTop.1 this (ε / 2) (by linarith [ε_pos]) with ⟨N, hN⟩
have : Fact (μ (T N) < ∞) := Fact.mk T_finite N
      -- Then we can apply the previous result to the measure `μ ((S N) ∩ •)`.
      -- There exists `t ∈ 𝒜` such that `μ ((S N) ∩ (s ∆ t)) < ε/2`.
      rcases (Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
        (μ.restrict (T N)) h𝒜 hgen).approx s ms
        (ne_of_lt (lt_of_le_of_lt (μ.restrict_apply_le _ s) hμs.lt_top))
        (ε / 2) (by linarith [ε_pos])
        with ⟨t, t_mem, ht⟩
      -- We can then use `t ∩ (S N)`, because `S N ∈ 𝒜` by hypothesis.
      -- `μ (s ∆ (t ∩ S N))`
      -- `≤ μ (s ∆ (s ∩ S N)) + μ ((s ∩ S N) ∆ (t ∩ S N))`
      -- `= μ s - μ (s ∩ S N) + μ (s ∆ t) ∩ S N) < ε`.
      refine ⟨t inter T N, h𝒜.inter_mem t_mem (T_mem N), ?_⟩
      calc
        μ (s ∆ (t inter T N))
          <= μ (s \ (s inter T N)) + μ ((s ∆ t) inter T N) := by
              rw [← symmDiff_of_le (inter_subset_left ..)]; rw [symmDiff_comm _ s]; rw [inter_symmDiff_distrib_right]
              exact measure_symmDiff_le _ _ _
        _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
              apply ENNReal.add_lt_add
              · rw [measure_sdiff
                    (inter_subset_left ..)
                    (ms.inter (hgen ▸ measurableSet_generateFrom (T_mem N))).nullMeasurableSet
                    (ne_top_of_le_ne_top hμs (measure_mono (inter_subset_left ..))),
                  lt_ofReal_iff_toReal_lt (sub_ne_top hμs),
                  toReal_sub_of_le (measure_mono (inter_subset_left ..)) hμs]
                apply lt_of_le_of_lt (sub_le_dist ..)
                nth_rw 1 [← univ_inter s]
                rw [inter_comm s]; rw [dist_comm]; rw [← T_spanning]; rw [iUnion_inter _ T]
                apply hN N (le_refl _)
              · rwa [← μ.restrict_apply' (hgen ▸ measurableSet_generateFrom (T_mem N))]
        _ = ENNReal.ofReal ε := by
              rw [← ofReal_add (by linarith [ε_pos]) (by linarith [ε_pos]), add_halves]
    · exact fun n => ne_top_of_le_ne_top hμs (measure_mono (inter_subset_right ..))
    · exact ne_top_of_le_ne_top hμs
        (measure_mono (iUnion_subset (fun i => inter_subset_right ..)))

Depends on / 依赖: measurableSet_generateFrom
-/
theorem Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite (h𝒜 : IsSetAlgebra 𝒜)
    (S : μ.FiniteSpanningSetsIn 𝒜) (hgen : m = MeasurableSpace.generateFrom 𝒜) :
    μ.MeasureDense 𝒜 where
  measurable s hs := hgen ▸ measurableSet_generateFrom hs
  approx s ms hμs ε ε_pos := by
    -- We use partial unions of (Sₙ) to get a monotone family spanning `X`.
    let T := accumulate S.set
    have T_mem (n) : T n in 𝒜 := by
      simpa using! h𝒜.biUnion_mem {k | k <= n}.toFinset (fun k _ => S.set_mem k)
    have T_finite (n) : μ (T n) < ∞ := by
      simpa using! measure_biUnion_lt_top {k | k <= n}.toFinset.finite_toSet
        (fun k _ => S.finite k)
    have T_spanning : ⋃ n, T n = univ := S.spanning ▸ iUnion_accumulate
    -- We use the fact that we already know this is true for finite measures. As `⋃ n, T n = X`,
    -- we have that `μ ((T n) ∩ s) ⟶ μ s`.
    have mono : Monotone (fun n => (T n) inter s) := fun m n hmn => inter_subset_inter_left s
        (biUnion_subset_biUnion_left fun k hkm => Nat.le_trans hkm hmn)
    have := tendsto_measure_iUnion_atTop (μ := μ) mono
    rw [← tendsto_toReal_iff] at this
    · -- We can therefore choose `N` such that `μ s - μ ((S N) ∩ s) < ε/2`.
      rcases Metric.tendsto_atTop.1 this (ε / 2) (by linarith [ε_pos]) with ⟨N, hN⟩
have : Fact (μ (T N) < ∞) := Fact.mk T_finite N
      -- Then we can apply the previous result to the measure `μ ((S N) ∩ •)`.
      -- There exists `t ∈ 𝒜` such that `μ ((S N) ∩ (s ∆ t)) < ε/2`.
      rcases (Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
        (μ.restrict (T N)) h𝒜 hgen).approx s ms
        (ne_of_lt (lt_of_le_of_lt (μ.restrict_apply_le _ s) hμs.lt_top))
        (ε / 2) (by linarith [ε_pos])
        with ⟨t, t_mem, ht⟩
      -- We can then use `t ∩ (S N)`, because `S N ∈ 𝒜` by hypothesis.
      -- `μ (s ∆ (t ∩ S N))`
      -- `≤ μ (s ∆ (s ∩ S N)) + μ ((s ∩ S N) ∆ (t ∩ S N))`
      -- `= μ s - μ (s ∩ S N) + μ (s ∆ t) ∩ S N) < ε`.
      refine ⟨t inter T N, h𝒜.inter_mem t_mem (T_mem N), ?_⟩
      calc
        μ (s ∆ (t inter T N))
          <= μ (s \ (s inter T N)) + μ ((s ∆ t) inter T N) := by
              rw [← symmDiff_of_le (inter_subset_left ..)]; rw [symmDiff_comm _ s]; rw [inter_symmDiff_distrib_right]
              exact measure_symmDiff_le _ _ _
        _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
              apply ENNReal.add_lt_add
              · rw [measure_sdiff
                    (inter_subset_left ..)
                    (ms.inter (hgen ▸ measurableSet_generateFrom (T_mem N))).nullMeasurableSet
                    (ne_top_of_le_ne_top hμs (measure_mono (inter_subset_left ..))),
                  lt_ofReal_iff_toReal_lt (sub_ne_top hμs),
                  toReal_sub_of_le (measure_mono (inter_subset_left ..)) hμs]
                apply lt_of_le_of_lt (sub_le_dist ..)
                nth_rw 1 [← univ_inter s]
                rw [inter_comm s]; rw [dist_comm]; rw [← T_spanning]; rw [iUnion_inter _ T]
                apply hN N (le_refl _)
              · rwa [← μ.restrict_apply' (hgen ▸ measurableSet_generateFrom (T_mem N))]
        _ = ENNReal.ofReal ε := by
              rw [← ofReal_add (by linarith [ε_pos]) (by linarith [ε_pos]), add_halves]
    · exact fun n => ne_top_of_le_ne_top hμs (measure_mono (inter_subset_right ..))
    · exact ne_top_of_le_ne_top hμs
        (measure_mono (iUnion_subset (fun i => inter_subset_right ..)))

end MeasureDense

section IsSeparable

/-! ### Definition of a separable measure space, sufficient condition -/

/--
Definition of `IsSeparable` / `IsSeparable` 的定义

English:
class IsSeparable
  parameters: (μ : Measure X)
  axioms and operations (1):
    - exists_countable_measureDense : exists 𝒜, 𝒜.Countable ∧ μ.MeasureDense 𝒜

中文:
类 是可分
  参数: (μ : 测度 X)
  公理与运算 (1 个):
    - exists_countable_measureDense : 存在 𝒜, 𝒜.可数 ∧ μ.测度稠密 𝒜
-/
class IsSeparable (μ : Measure X) : Prop where
  exists_countable_measureDense : exists 𝒜, 𝒜.Countable ∧ μ.MeasureDense 𝒜

variable (μ)

/--
theorem `exists_countable_measureDense` / 定理 `exists_countable_measureDense`

English:
theorem exists_countable_measureDense
  given: [IsSeparable μ]
  proof: IsSeparable.exists_countable_measureDense

中文:
定理 存在_countable_measureDense
  条件: [是可分 μ]
  证明: IsSeparable.exists_countable_measureDense

Depends on / 依赖: IsSeparable, IsSeparable.exists_countable_measureDense, exists_countable_measureDense
-/
theorem exists_countable_measureDense [IsSeparable μ] :
    exists 𝒜, 𝒜.Countable ∧ μ.MeasureDense 𝒜 :=
  IsSeparable.exists_countable_measureDense

/--
theorem `isSeparable_of_sigmaFinite` / 定理 `isSeparable_of_sigmaFinite`

English:
theorem isSeparable_of_sigmaFinite
  given: [CountablyGenerated X] [SigmaFinite μ]
  proof: by
    have h := countable_countableGeneratingSet (α := X)
    have hgen := generateFrom_countableGeneratingSet (α := X)
    let 𝒜 := (countableGeneratingSet X) union {μ.toFiniteSpanningSetsIn.set n | n : Nat}
    have count_𝒜 : 𝒜.Countable :=
      countable_union.2 ⟨h, countable_iff_exists_subset_range.2
        ⟨μ.toFiniteSpanningSetsIn.set, fun _ hx => hx⟩⟩
    refine ⟨generateSetAlgebra 𝒜, countable_generateSetAlgebra count_𝒜,
      Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite isSetAlgebra_generateSetAlgebra
      { set := μ.toFiniteSpanningSetsIn.set
set_mem := fun n => self_subset_generateSetAlgebra (𝒜 := 𝒜) Or.inr ⟨n, rfl⟩
        finite := μ.toFiniteSpanningSetsIn.finite
        spanning := μ.toFiniteSpanningSetsIn.spanning }
      (le_antisymm ?_ (generateFrom_le (fun s hs => ?_)))⟩
    · rw [← hgen]
exact generateFrom_mono le_trans self_subset_generateSetAlgebra
generateSetAlgebra_mono subset_union_left ..
    · induction hs with
      | base t t_mem =>
        rcases t_mem with t_mem | ⟨n, rfl⟩
        · exact hgen ▸ measurableSet_generateFrom t_mem
        · exact μ.toFiniteSpanningSetsIn.set_mem n
      | empty => exact MeasurableSet.empty
      | compl t _ t_mem => exact MeasurableSet.compl t_mem
      | union t u _ _ t_mem u_mem => exact MeasurableSet.union t_mem u_mem

中文:
定理 isSeparable_of_sigmaFinite
  条件: [余untablyGenerated X] [σ有限 μ]
  证明: by
    have h := countable_countableGeneratingSet (α := X)
    have hgen := generateFrom_countableGeneratingSet (α := X)
    let 𝒜 := (countableGeneratingSet X) union {μ.toFiniteSpanningSetsIn.set n | n : Nat}
    have count_𝒜 : 𝒜.Countable :=
      countable_union.2 ⟨h, countable_iff_exists_subset_range.2
        ⟨μ.toFiniteSpanningSetsIn.set, fun _ hx => hx⟩⟩
    refine ⟨generateSetAlgebra 𝒜, countable_generateSetAlgebra count_𝒜,
      Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite isSetAlgebra_generateSetAlgebra
      { set := μ.toFiniteSpanningSetsIn.set
set_mem := fun n => self_subset_generateSetAlgebra (𝒜 := 𝒜) Or.inr ⟨n, rfl⟩
        finite := μ.toFiniteSpanningSetsIn.finite
        spanning := μ.toFiniteSpanningSetsIn.spanning }
      (le_antisymm ?_ (generateFrom_le (fun s hs => ?_)))⟩
    · rw [← hgen]
exact generateFrom_mono le_trans self_subset_generateSetAlgebra
generateSetAlgebra_mono subset_union_left ..
    · induction hs with
      | base t t_mem =>
        rcases t_mem with t_mem | ⟨n, rfl⟩
        · exact hgen ▸ measurableSet_generateFrom t_mem
        · exact μ.toFiniteSpanningSetsIn.set_mem n
      | empty => exact MeasurableSet.empty
      | compl t _ t_mem => exact MeasurableSet.compl t_mem
      | union t u _ _ t_mem u_mem => exact MeasurableSet.union t_mem u_mem

Depends on / 依赖: Countable, Measure, Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite, MeasureDense, countableGeneratingSet, countable_countableGeneratingSet, countable_generateSetAlgebra, countable_iff_exists_subset_range, countable_union, generateFrom_countableGeneratingSet, generateSetAlgebra, isSetAlgebra_generateSetAlgebra, of_generateFrom_isSetAlgebra_sigmaFinite, toFiniteSpanningSetsIn, toFiniteSpanningSetsIn.set
-/
theorem isSeparable_of_sigmaFinite [CountablyGenerated X] [SigmaFinite μ] :
    IsSeparable μ where
  exists_countable_measureDense := by
    have h := countable_countableGeneratingSet (α := X)
    have hgen := generateFrom_countableGeneratingSet (α := X)
    let 𝒜 := (countableGeneratingSet X) union {μ.toFiniteSpanningSetsIn.set n | n : Nat}
    have count_𝒜 : 𝒜.Countable :=
      countable_union.2 ⟨h, countable_iff_exists_subset_range.2
        ⟨μ.toFiniteSpanningSetsIn.set, fun _ hx => hx⟩⟩
    refine ⟨generateSetAlgebra 𝒜, countable_generateSetAlgebra count_𝒜,
      Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite isSetAlgebra_generateSetAlgebra
      { set := μ.toFiniteSpanningSetsIn.set
set_mem := fun n => self_subset_generateSetAlgebra (𝒜 := 𝒜) Or.inr ⟨n, rfl⟩
        finite := μ.toFiniteSpanningSetsIn.finite
        spanning := μ.toFiniteSpanningSetsIn.spanning }
      (le_antisymm ?_ (generateFrom_le (fun s hs => ?_)))⟩
    · rw [← hgen]
exact generateFrom_mono le_trans self_subset_generateSetAlgebra
generateSetAlgebra_mono subset_union_left ..
    · induction hs with
      | base t t_mem =>
        rcases t_mem with t_mem | ⟨n, rfl⟩
        · exact hgen ▸ measurableSet_generateFrom t_mem
        · exact μ.toFiniteSpanningSetsIn.set_mem n
      | empty => exact MeasurableSet.empty
      | compl t _ t_mem => exact MeasurableSet.compl t_mem
      | union t u _ _ t_mem u_mem => exact MeasurableSet.union t_mem u_mem

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CountablyGenerated
  signature: X] [SFinite μ] : IsSeparable μ where
  body: by
    have := isSeparable_of_sigmaFinite (μ.restrict μ.sigmaFiniteSet)
    rcases exists_countable_measureDense (μ.restrict μ.sigmaFiniteSet) with ⟨𝒜, count_𝒜, h𝒜⟩
    let ℬ := {s inter μ.sigmaFiniteSet | s in 𝒜}
    refine ⟨ℬ, count_𝒜.image (fun s => s inter μ.sigmaFiniteSet), ?_, ?_⟩
    · rintro - ⟨s, s_mem, rfl⟩
      exact (h𝒜.measurable s s_mem).inter measurableSet_sigmaFiniteSet
    · intro s ms hμs ε ε_pos
      rcases restrict_compl_sigmaFiniteSet_eq_zero_or_top μ s with hs | hs
      · have : (μ.restrict μ.sigmaFiniteSet) s != ∞ :=
ne_top_of_le_ne_top hμs μ.restrict_le_self _
        rcases h𝒜.approx s ms this ε ε_pos with ⟨t, t_mem, ht⟩
        refine ⟨t inter μ.sigmaFiniteSet, ⟨t, t_mem, rfl⟩, ?_⟩
        have : μ (s ∆ (t inter μ.sigmaFiniteSet) \ μ.sigmaFiniteSet) = 0 := by
          rw [sdiff_eq_compl_inter]; rw [inter_symmDiff_distrib_left]; rw [← ENNReal.bot_eq_zero]; rw [eq_bot_iff]
          calc
            μ ((μ.sigmaFiniteSetᶜ inter s) ∆ (μ.sigmaFiniteSetᶜ inter (t inter μ.sigmaFiniteSet)))
              <= μ ((μ.sigmaFiniteSetᶜ inter s) union (μ.sigmaFiniteSetᶜ inter (t inter μ.sigmaFiniteSet))) :=
                measure_mono symmDiff_subset_union
            _ <= μ (μ.sigmaFiniteSetᶜ inter s) + μ (μ.sigmaFiniteSetᶜ inter (t inter μ.sigmaFiniteSet)) :=
                measure_union_le _ _
            _ = 0 := by
                rw [inter_comm]; rw [← μ.restrict_apply ms]; rw [hs]; rw [← inter_assoc]; rw [inter_comm]; rw [← inter_assoc]; rw [inter_compl_self]; rw [empty_inter]; rw [measure_empty]; rw [zero_add]
        rwa [← measure_inter_add_sdiff _ measurableSet_sigmaFiniteSet, this, add_zero,
          inter_symmDiff_distrib_right, inter_assoc, inter_self, ← inter_symmDiff_distrib_right,
          ← μ.restrict_apply' measurableSet_sigmaFiniteSet]
· refine False.elim hμs ?_
        rw [eq_top_iff]; rw [← hs]
        exact μ.restrict_le_self _

中文:
实例 [余untablyGenerated
  签名: X] [SFinite μ] : 是可分 μ where
  定义体: by
    have := isSeparable_of_sigmaFinite (μ.restrict μ.sigmaFiniteSet)
    rcases exists_countable_measureDense (μ.restrict μ.sigmaFiniteSet) with ⟨𝒜, count_𝒜, h𝒜⟩
    let ℬ := {s inter μ.sigmaFiniteSet | s in 𝒜}
    refine ⟨ℬ, count_𝒜.image (fun s => s inter μ.sigmaFiniteSet), ?_, ?_⟩
    · rintro - ⟨s, s_mem, rfl⟩
      exact (h𝒜.measurable s s_mem).inter measurableSet_sigmaFiniteSet
    · intro s ms hμs ε ε_pos
      rcases restrict_compl_sigmaFiniteSet_eq_zero_or_top μ s with hs | hs
      · have : (μ.restrict μ.sigmaFiniteSet) s != ∞ :=
ne_top_of_le_ne_top hμs μ.restrict_le_self _
        rcases h𝒜.approx s ms this ε ε_pos with ⟨t, t_mem, ht⟩
        refine ⟨t inter μ.sigmaFiniteSet, ⟨t, t_mem, rfl⟩, ?_⟩
        have : μ (s ∆ (t inter μ.sigmaFiniteSet) \ μ.sigmaFiniteSet) = 0 := by
          rw [sdiff_eq_compl_inter]; rw [inter_symmDiff_distrib_left]; rw [← ENNReal.bot_eq_zero]; rw [eq_bot_iff]
          calc
            μ ((μ.sigmaFiniteSetᶜ inter s) ∆ (μ.sigmaFiniteSetᶜ inter (t inter μ.sigmaFiniteSet)))
              <= μ ((μ.sigmaFiniteSetᶜ inter s) union (μ.sigmaFiniteSetᶜ inter (t inter μ.sigmaFiniteSet))) :=
                measure_mono symmDiff_subset_union
            _ <= μ (μ.sigmaFiniteSetᶜ inter s) + μ (μ.sigmaFiniteSetᶜ inter (t inter μ.sigmaFiniteSet)) :=
                measure_union_le _ _
            _ = 0 := by
                rw [inter_comm]; rw [← μ.restrict_apply ms]; rw [hs]; rw [← inter_assoc]; rw [inter_comm]; rw [← inter_assoc]; rw [inter_compl_self]; rw [empty_inter]; rw [measure_empty]; rw [zero_add]
        rwa [← measure_inter_add_sdiff _ measurableSet_sigmaFiniteSet, this, add_zero,
          inter_symmDiff_distrib_right, inter_assoc, inter_self, ← inter_symmDiff_distrib_right,
          ← μ.restrict_apply' measurableSet_sigmaFiniteSet]
· refine False.elim hμs ?_
        rw [eq_top_iff]; rw [← hs]
        exact μ.restrict_le_self _

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, exists_countable_measureDense, isSeparable_of_sigmaFinite, measurable, measurableSet_sigmaFiniteSet, restrict, restrict_compl_sigmaFiniteSet_eq_zero_or_top, s_mem, sigmaFiniteSet
-/
instance [CountablyGenerated X] [SFinite μ] : IsSeparable μ where
  exists_countable_measureDense := by
    have := isSeparable_of_sigmaFinite (μ.restrict μ.sigmaFiniteSet)
    rcases exists_countable_measureDense (μ.restrict μ.sigmaFiniteSet) with ⟨𝒜, count_𝒜, h𝒜⟩
    let ℬ := {s inter μ.sigmaFiniteSet | s in 𝒜}
    refine ⟨ℬ, count_𝒜.image (fun s => s inter μ.sigmaFiniteSet), ?_, ?_⟩
    · rintro - ⟨s, s_mem, rfl⟩
      exact (h𝒜.measurable s s_mem).inter measurableSet_sigmaFiniteSet
    · intro s ms hμs ε ε_pos
      rcases restrict_compl_sigmaFiniteSet_eq_zero_or_top μ s with hs | hs
      · have : (μ.restrict μ.sigmaFiniteSet) s != ∞ :=
ne_top_of_le_ne_top hμs μ.restrict_le_self _
        rcases h𝒜.approx s ms this ε ε_pos with ⟨t, t_mem, ht⟩
        refine ⟨t inter μ.sigmaFiniteSet, ⟨t, t_mem, rfl⟩, ?_⟩
        have : μ (s ∆ (t inter μ.sigmaFiniteSet) \ μ.sigmaFiniteSet) = 0 := by
          rw [sdiff_eq_compl_inter]; rw [inter_symmDiff_distrib_left]; rw [← ENNReal.bot_eq_zero]; rw [eq_bot_iff]
          calc
            μ ((μ.sigmaFiniteSetᶜ inter s) ∆ (μ.sigmaFiniteSetᶜ inter (t inter μ.sigmaFiniteSet)))
              <= μ ((μ.sigmaFiniteSetᶜ inter s) union (μ.sigmaFiniteSetᶜ inter (t inter μ.sigmaFiniteSet))) :=
                measure_mono symmDiff_subset_union
            _ <= μ (μ.sigmaFiniteSetᶜ inter s) + μ (μ.sigmaFiniteSetᶜ inter (t inter μ.sigmaFiniteSet)) :=
                measure_union_le _ _
            _ = 0 := by
                rw [inter_comm]; rw [← μ.restrict_apply ms]; rw [hs]; rw [← inter_assoc]; rw [inter_comm]; rw [← inter_assoc]; rw [inter_compl_self]; rw [empty_inter]; rw [measure_empty]; rw [zero_add]
        rwa [← measure_inter_add_sdiff _ measurableSet_sigmaFiniteSet, this, add_zero,
          inter_symmDiff_distrib_right, inter_assoc, inter_self, ← inter_symmDiff_distrib_right,
          ← μ.restrict_apply' measurableSet_sigmaFiniteSet]
· refine False.elim hμs ?_
        rw [eq_top_iff]; rw [← hs]
        exact μ.restrict_le_self _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hμ
  signature: : IsSeparable μ] : IsSeparable μ.completion
  body: by
  obtain ⟨𝒜, count_𝒜, h𝒜⟩ := exists_countable_measureDense μ
  exact ⟨𝒜, count_𝒜, h𝒜.completion⟩

中文:
实例 [hμ
  签名: : 是可分 μ] : 是可分 μ.completion
  定义体: by
  obtain ⟨𝒜, count_𝒜, h𝒜⟩ := exists_countable_measureDense μ
  exact ⟨𝒜, count_𝒜, h𝒜.completion⟩

Depends on / 依赖: completion, exists_countable_measureDense
-/
instance [hμ : IsSeparable μ] : IsSeparable μ.completion := by
  obtain ⟨𝒜, count_𝒜, h𝒜⟩ := exists_countable_measureDense μ
  exact ⟨𝒜, count_𝒜, h𝒜.completion⟩

end IsSeparable

section SecondCountableLp

/-! ### A sufficient condition for $L^p$ spaces to be second-countable -/

/--
Instance `Lp.SecondCountableTopology` / 实例 `Lp.SecondCountableTopology`

English:
instance Lp.SecondCountableTopology
  signature: [IsSeparable μ] [TopologicalSpace.SeparableSpace E]
  body: by
  -- It is enough to show that the space is separable, i.e. admits a countable and dense subset.
  refine @UniformSpace.secondCountable_of_separable _ _ _ ?_
  -- There exists a countable and measure-dense family, and we can keep only the sets with finite
  -- measure while preserving the two properties. This family is denoted `𝒜₀`.
  rcases exists_countable_measureDense μ with ⟨𝒜, count_𝒜, h𝒜⟩
  have h𝒜₀ := Measure.MeasureDense.fin_meas h𝒜
  set 𝒜₀ := {s | s in 𝒜 ∧ μ s != ∞}
  have count_𝒜₀ : 𝒜₀.Countable := count_𝒜.mono fun _ ⟨h, _⟩ => h
  -- `1 ≤ p` so `p ≠ 0`, we prove it now as it is often needed.
have p_ne_zero : p != 0 := ne_of_gt lt_of_lt_of_le (by simp) one_le_p.elim
  -- `E` is second-countable, therefore separable and admits a countable and dense subset `u`.
  rcases exists_countable_dense E with ⟨u, countable_u, dense_u⟩
  -- The countable and dense subset of `Lᵖ` we are going to build is the set of finite sums of
  -- constant indicators with support in `𝒜₀`, and is denoted `D`. To make manipulations easier,
  -- we define the function `key` which given an integer `n` and two families of `n` elements
  -- in `u` and `𝒜₀` associates the corresponding sum.
  let key (n : Nat) (d : Fin n -> u) (s : Fin n -> 𝒜₀) : (Lp E p μ) :=
    ∑ i, indicatorConstLp p (h𝒜₀.measurable (s i) (Subtype.mem (s i))) (s i).2.2 (d i : E)
  let D := {s : Lp E p μ | exists n d t, s = key n d t}
  refine ⟨D, ?_, ?_⟩
  · -- Countability directly follows from countability of `u` and `𝒜₀`. The function `f` below
    -- is the uncurried version of `key`, which is easier to manipulate as countability of the
    -- domain is automatically inferred.
    let f (nds : Σ n : Nat, (Fin n -> u) × (Fin n -> 𝒜₀)) : Lp E p μ := key nds.1 nds.2.1 nds.2.2
    have := count_𝒜₀.to_subtype
    have := countable_u.to_subtype
    have : D subseteq range f := by
      rintro - ⟨n, d, s, rfl⟩
      use ⟨n, (d, s)⟩
    exact (countable_range f).mono this
  · -- Let's turn to the density. Thanks to the density of simple functions in `Lᵖ`, it is enough
    -- to show that the closure of `D` contains constant indicators which are in `Lᵖ` (i. e. the
    -- set has finite measure), is closed by sum and closed.
    -- This is given by `Lp.induction`.
    refine Lp.induction p_ne_top.elim (motive := fun f => f in closure D) ?_ ?_ isClosed_closure
    · intro a s ms hμs
      -- We want to approximate `a • 𝟙ₛ`.
      apply ne_of_lt at hμs
      rw [SeminormedAddCommGroup.mem_closure_iff]
      intro ε ε_pos
      have μs_pow_nonneg : 0 <= μ.real s ^ (1 / p.toReal) := by positivity
      -- To do so, we first pick `b ∈ u` such that `‖a - b‖ < ε / (3 * (1 + (μ s)^(1/p)))`.
      have approx_a_pos : 0 < ε / (3 * (1 + μ.real s ^ (1 / p.toReal))) :=
        div_pos ε_pos (by linarith [μs_pow_nonneg])
      have ⟨b, b_mem, hb⟩ := SeminormedAddCommGroup.mem_closure_iff.1 (dense_u a) _ approx_a_pos
      -- Then we pick `t ∈ 𝒜₀` such that `‖b • 𝟙ₛ - b • 𝟙ₜ‖ < ε / 3`.
      rcases SeminormedAddCommGroup.mem_closure_iff.1
        (h𝒜₀.indicatorConstLp_subset_closure p b ⟨s, ms, hμs, rfl⟩)
          (ε / 3) (by linarith [ε_pos]) with ⟨-, ⟨t, ht, hμt, rfl⟩, hst⟩
      have mt := h𝒜₀.measurable t ht
      -- We now show that `‖a • 𝟙ₛ - b • 𝟙ₜ‖ₚ < ε`, as follows:
      -- `‖a • 𝟙ₛ - b • 𝟙ₜ‖ₚ`
      -- `= ‖a • 𝟙ₛ - b • 𝟙ₛ + b • 𝟙ₛ - b • 𝟙ₜ‖ₚ`
      -- `≤ ‖a - b‖ * ‖𝟙ₛ‖ₚ + ε / 3`
      -- `= ‖a - b‖ * (μ s)^(1/p) + ε / 3`
      -- `< ε * (μ s)^(1/p) / (3 * (1 + (μ s)^(1/p))) + ε / 3`
      -- `≤ ε / 3 + ε / 3 < ε`.
      refine ⟨indicatorConstLp p mt hμt b,
        ⟨1, fun _ => ⟨b, b_mem⟩, fun _ => ⟨t, ht⟩, by simp [key]⟩, ?_⟩
      rw [Lp.simpleFunc.coe_indicatorConst]; rw [← sub_add_sub_cancel _ (indicatorConstLp p ms hμs b)]; rw [← add_halves ε]
      refine lt_of_le_of_lt (b := ε / 3 + ε / 3) (norm_add_le_of_le ?_ hst.le) (by linarith [ε_pos])
      rw [indicatorConstLp_sub]; rw [norm_indicatorConstLp p_ne_zero p_ne_top.elim]
      calc
        ‖a - b‖ * μ.real s ^ (1 / p.toReal)
          <= (ε / (3 * (1 + μ.real s ^ (1 / p.toReal)))) * μ.real s ^ (1 / p.toReal) :=
              mul_le_mul_of_nonneg_right (le_of_lt hb) μs_pow_nonneg
        _ <= ε / 3 := by
            rw [← mul_one (ε / 3)]; rw [div_mul_eq_div_mul_one_div]; rw [mul_assoc]; rw [one_div_mul_eq_div]
            exact mul_le_mul_of_nonneg_left
              ((div_le_one (by linarith [μs_pow_nonneg])).2 (by linarith))
              (by linarith [ε_pos])
    · -- Now we have to show that the closure of `D` is closed by sum. Let `f` and `g` be two
      -- functions in `Lᵖ` which are also in the closure of `D`.
      rintro f g hf hg - f_mem g_mem
      rw [SeminormedAddCommGroup.mem_closure_iff] at *
      intro ε ε_pos
      -- For `ε > 0`, there exists `bf, bg ∈ D` such that `‖f - bf‖ₚ < ε/2` and `‖g - bg‖ₚ < ε/2`.
      rcases f_mem (ε / 2) (by linarith [ε_pos]) with ⟨bf, ⟨nf, df, sf, bf_eq⟩, hbf⟩
      rcases g_mem (ε / 2) (by linarith [ε_pos]) with ⟨bg, ⟨ng, dg, sg, bg_eq⟩, hbg⟩
      -- It is obvious that `D` is closed by sum, it suffices to concatenate the family of
      -- elements of `u` and the family of elements of `𝒜₀`.
      let d := fun i : Fin (nf + ng) => if h : i < nf
        then df (Fin.castLT i h)
        else dg (Fin.subNat nf (Fin.cast (Nat.add_comm ..) i) (le_of_not_gt h))
      let s := fun i : Fin (nf + ng) => if h : i < nf
        then sf (Fin.castLT i h)
        else sg (Fin.subNat nf (Fin.cast (Nat.add_comm ..) i) (le_of_not_gt h))
      -- So we can use `bf + bg`.
      refine ⟨bf + bg, ⟨nf + ng, d, s, ?_⟩, ?_⟩
      · simp [key, d, s, Fin.sum_univ_add, bf_eq, bg_eq]
      · -- We have
        -- `‖f + g - (bf + bg)‖ₚ`
        -- `≤ ‖f - bf‖ₚ + ‖g - bg‖ₚ`
        -- `< ε/2 + ε/2 = ε`.
        calc
          ‖MemLp.toLp f hf + MemLp.toLp g hg - (bf + bg)‖
            = ‖(MemLp.toLp f hf) - bf + ((MemLp.toLp g hg) - bg)‖ := by congr; abel
          _ <= ‖(MemLp.toLp f hf) - bf‖ + ‖(MemLp.toLp g hg) - bg‖ := norm_add_le ..
          _ < ε := by linarith [hbf, hbg]

中文:
实例 Lp.第二可数拓扑
  签名: [是可分 μ] [拓扑空间.可分空间 E]
  定义体: by
  -- It is enough to show that the space is separable, i.e. admits a countable and dense subset.
  refine @UniformSpace.secondCountable_of_separable _ _ _ ?_
  -- There exists a countable and measure-dense family, and we can keep only the sets with finite
  -- measure while preserving the two properties. This family is denoted `𝒜₀`.
  rcases exists_countable_measureDense μ with ⟨𝒜, count_𝒜, h𝒜⟩
  have h𝒜₀ := Measure.MeasureDense.fin_meas h𝒜
  set 𝒜₀ := {s | s in 𝒜 ∧ μ s != ∞}
  have count_𝒜₀ : 𝒜₀.Countable := count_𝒜.mono fun _ ⟨h, _⟩ => h
  -- `1 ≤ p` so `p ≠ 0`, we prove it now as it is often needed.
have p_ne_zero : p != 0 := ne_of_gt lt_of_lt_of_le (by simp) one_le_p.elim
  -- `E` is second-countable, therefore separable and admits a countable and dense subset `u`.
  rcases exists_countable_dense E with ⟨u, countable_u, dense_u⟩
  -- The countable and dense subset of `Lᵖ` we are going to build is the set of finite sums of
  -- constant indicators with support in `𝒜₀`, and is denoted `D`. To make manipulations easier,
  -- we define the function `key` which given an integer `n` and two families of `n` elements
  -- in `u` and `𝒜₀` associates the corresponding sum.
  let key (n : Nat) (d : Fin n -> u) (s : Fin n -> 𝒜₀) : (Lp E p μ) :=
    ∑ i, indicatorConstLp p (h𝒜₀.measurable (s i) (Subtype.mem (s i))) (s i).2.2 (d i : E)
  let D := {s : Lp E p μ | exists n d t, s = key n d t}
  refine ⟨D, ?_, ?_⟩
  · -- Countability directly follows from countability of `u` and `𝒜₀`. The function `f` below
    -- is the uncurried version of `key`, which is easier to manipulate as countability of the
    -- domain is automatically inferred.
    let f (nds : Σ n : Nat, (Fin n -> u) × (Fin n -> 𝒜₀)) : Lp E p μ := key nds.1 nds.2.1 nds.2.2
    have := count_𝒜₀.to_subtype
    have := countable_u.to_subtype
    have : D subseteq range f := by
      rintro - ⟨n, d, s, rfl⟩
      use ⟨n, (d, s)⟩
    exact (countable_range f).mono this
  · -- Let's turn to the density. Thanks to the density of simple functions in `Lᵖ`, it is enough
    -- to show that the closure of `D` contains constant indicators which are in `Lᵖ` (i. e. the
    -- set has finite measure), is closed by sum and closed.
    -- This is given by `Lp.induction`.
    refine Lp.induction p_ne_top.elim (motive := fun f => f in closure D) ?_ ?_ isClosed_closure
    · intro a s ms hμs
      -- We want to approximate `a • 𝟙ₛ`.
      apply ne_of_lt at hμs
      rw [SeminormedAddCommGroup.mem_closure_iff]
      intro ε ε_pos
      have μs_pow_nonneg : 0 <= μ.real s ^ (1 / p.toReal) := by positivity
      -- To do so, we first pick `b ∈ u` such that `‖a - b‖ < ε / (3 * (1 + (μ s)^(1/p)))`.
      have approx_a_pos : 0 < ε / (3 * (1 + μ.real s ^ (1 / p.toReal))) :=
        div_pos ε_pos (by linarith [μs_pow_nonneg])
      have ⟨b, b_mem, hb⟩ := SeminormedAddCommGroup.mem_closure_iff.1 (dense_u a) _ approx_a_pos
      -- Then we pick `t ∈ 𝒜₀` such that `‖b • 𝟙ₛ - b • 𝟙ₜ‖ < ε / 3`.
      rcases SeminormedAddCommGroup.mem_closure_iff.1
        (h𝒜₀.indicatorConstLp_subset_closure p b ⟨s, ms, hμs, rfl⟩)
          (ε / 3) (by linarith [ε_pos]) with ⟨-, ⟨t, ht, hμt, rfl⟩, hst⟩
      have mt := h𝒜₀.measurable t ht
      -- We now show that `‖a • 𝟙ₛ - b • 𝟙ₜ‖ₚ < ε`, as follows:
      -- `‖a • 𝟙ₛ - b • 𝟙ₜ‖ₚ`
      -- `= ‖a • 𝟙ₛ - b • 𝟙ₛ + b • 𝟙ₛ - b • 𝟙ₜ‖ₚ`
      -- `≤ ‖a - b‖ * ‖𝟙ₛ‖ₚ + ε / 3`
      -- `= ‖a - b‖ * (μ s)^(1/p) + ε / 3`
      -- `< ε * (μ s)^(1/p) / (3 * (1 + (μ s)^(1/p))) + ε / 3`
      -- `≤ ε / 3 + ε / 3 < ε`.
      refine ⟨indicatorConstLp p mt hμt b,
        ⟨1, fun _ => ⟨b, b_mem⟩, fun _ => ⟨t, ht⟩, by simp [key]⟩, ?_⟩
      rw [Lp.simpleFunc.coe_indicatorConst]; rw [← sub_add_sub_cancel _ (indicatorConstLp p ms hμs b)]; rw [← add_halves ε]
      refine lt_of_le_of_lt (b := ε / 3 + ε / 3) (norm_add_le_of_le ?_ hst.le) (by linarith [ε_pos])
      rw [indicatorConstLp_sub]; rw [norm_indicatorConstLp p_ne_zero p_ne_top.elim]
      calc
        ‖a - b‖ * μ.real s ^ (1 / p.toReal)
          <= (ε / (3 * (1 + μ.real s ^ (1 / p.toReal)))) * μ.real s ^ (1 / p.toReal) :=
              mul_le_mul_of_nonneg_right (le_of_lt hb) μs_pow_nonneg
        _ <= ε / 3 := by
            rw [← mul_one (ε / 3)]; rw [div_mul_eq_div_mul_one_div]; rw [mul_assoc]; rw [one_div_mul_eq_div]
            exact mul_le_mul_of_nonneg_left
              ((div_le_one (by linarith [μs_pow_nonneg])).2 (by linarith))
              (by linarith [ε_pos])
    · -- Now we have to show that the closure of `D` is closed by sum. Let `f` and `g` be two
      -- functions in `Lᵖ` which are also in the closure of `D`.
      rintro f g hf hg - f_mem g_mem
      rw [SeminormedAddCommGroup.mem_closure_iff] at *
      intro ε ε_pos
      -- For `ε > 0`, there exists `bf, bg ∈ D` such that `‖f - bf‖ₚ < ε/2` and `‖g - bg‖ₚ < ε/2`.
      rcases f_mem (ε / 2) (by linarith [ε_pos]) with ⟨bf, ⟨nf, df, sf, bf_eq⟩, hbf⟩
      rcases g_mem (ε / 2) (by linarith [ε_pos]) with ⟨bg, ⟨ng, dg, sg, bg_eq⟩, hbg⟩
      -- It is obvious that `D` is closed by sum, it suffices to concatenate the family of
      -- elements of `u` and the family of elements of `𝒜₀`.
      let d := fun i : Fin (nf + ng) => if h : i < nf
        then df (Fin.castLT i h)
        else dg (Fin.subNat nf (Fin.cast (Nat.add_comm ..) i) (le_of_not_gt h))
      let s := fun i : Fin (nf + ng) => if h : i < nf
        then sf (Fin.castLT i h)
        else sg (Fin.subNat nf (Fin.cast (Nat.add_comm ..) i) (le_of_not_gt h))
      -- So we can use `bf + bg`.
      refine ⟨bf + bg, ⟨nf + ng, d, s, ?_⟩, ?_⟩
      · simp [key, d, s, Fin.sum_univ_add, bf_eq, bg_eq]
      · -- We have
        -- `‖f + g - (bf + bg)‖ₚ`
        -- `≤ ‖f - bf‖ₚ + ‖g - bg‖ₚ`
        -- `< ε/2 + ε/2 = ε`.
        calc
          ‖MemLp.toLp f hf + MemLp.toLp g hg - (bf + bg)‖
            = ‖(MemLp.toLp f hf) - bf + ((MemLp.toLp g hg) - bg)‖ := by congr; abel
          _ <= ‖(MemLp.toLp f hf) - bf‖ + ‖(MemLp.toLp g hg) - bg‖ := norm_add_le ..
          _ < ε := by linarith [hbf, hbg]

Depends on / 依赖: f.hom
-/
instance Lp.SecondCountableTopology [IsSeparable μ] [TopologicalSpace.SeparableSpace E] :
    SecondCountableTopology (Lp E p μ) := by
  -- It is enough to show that the space is separable, i.e. admits a countable and dense subset.
  refine @UniformSpace.secondCountable_of_separable _ _ _ ?_
  -- There exists a countable and measure-dense family, and we can keep only the sets with finite
  -- measure while preserving the two properties. This family is denoted `𝒜₀`.
  rcases exists_countable_measureDense μ with ⟨𝒜, count_𝒜, h𝒜⟩
  have h𝒜₀ := Measure.MeasureDense.fin_meas h𝒜
  set 𝒜₀ := {s | s in 𝒜 ∧ μ s != ∞}
  have count_𝒜₀ : 𝒜₀.Countable := count_𝒜.mono fun _ ⟨h, _⟩ => h
  -- `1 ≤ p` so `p ≠ 0`, we prove it now as it is often needed.
have p_ne_zero : p != 0 := ne_of_gt lt_of_lt_of_le (by simp) one_le_p.elim
  -- `E` is second-countable, therefore separable and admits a countable and dense subset `u`.
  rcases exists_countable_dense E with ⟨u, countable_u, dense_u⟩
  -- The countable and dense subset of `Lᵖ` we are going to build is the set of finite sums of
  -- constant indicators with support in `𝒜₀`, and is denoted `D`. To make manipulations easier,
  -- we define the function `key` which given an integer `n` and two families of `n` elements
  -- in `u` and `𝒜₀` associates the corresponding sum.
  let key (n : Nat) (d : Fin n -> u) (s : Fin n -> 𝒜₀) : (Lp E p μ) :=
    ∑ i, indicatorConstLp p (h𝒜₀.measurable (s i) (Subtype.mem (s i))) (s i).2.2 (d i : E)
  let D := {s : Lp E p μ | exists n d t, s = key n d t}
  refine ⟨D, ?_, ?_⟩
  · -- Countability directly follows from countability of `u` and `𝒜₀`. The function `f` below
    -- is the uncurried version of `key`, which is easier to manipulate as countability of the
    -- domain is automatically inferred.
    let f (nds : Σ n : Nat, (Fin n -> u) × (Fin n -> 𝒜₀)) : Lp E p μ := key nds.1 nds.2.1 nds.2.2
    have := count_𝒜₀.to_subtype
    have := countable_u.to_subtype
    have : D subseteq range f := by
      rintro - ⟨n, d, s, rfl⟩
      use ⟨n, (d, s)⟩
    exact (countable_range f).mono this
  · -- Let's turn to the density. Thanks to the density of simple functions in `Lᵖ`, it is enough
    -- to show that the closure of `D` contains constant indicators which are in `Lᵖ` (i. e. the
    -- set has finite measure), is closed by sum and closed.
    -- This is given by `Lp.induction`.
    refine Lp.induction p_ne_top.elim (motive := fun f => f in closure D) ?_ ?_ isClosed_closure
    · intro a s ms hμs
      -- We want to approximate `a • 𝟙ₛ`.
      apply ne_of_lt at hμs
      rw [SeminormedAddCommGroup.mem_closure_iff]
      intro ε ε_pos
      have μs_pow_nonneg : 0 <= μ.real s ^ (1 / p.toReal) := by positivity
      -- To do so, we first pick `b ∈ u` such that `‖a - b‖ < ε / (3 * (1 + (μ s)^(1/p)))`.
      have approx_a_pos : 0 < ε / (3 * (1 + μ.real s ^ (1 / p.toReal))) :=
        div_pos ε_pos (by linarith [μs_pow_nonneg])
      have ⟨b, b_mem, hb⟩ := SeminormedAddCommGroup.mem_closure_iff.1 (dense_u a) _ approx_a_pos
      -- Then we pick `t ∈ 𝒜₀` such that `‖b • 𝟙ₛ - b • 𝟙ₜ‖ < ε / 3`.
      rcases SeminormedAddCommGroup.mem_closure_iff.1
        (h𝒜₀.indicatorConstLp_subset_closure p b ⟨s, ms, hμs, rfl⟩)
          (ε / 3) (by linarith [ε_pos]) with ⟨-, ⟨t, ht, hμt, rfl⟩, hst⟩
      have mt := h𝒜₀.measurable t ht
      -- We now show that `‖a • 𝟙ₛ - b • 𝟙ₜ‖ₚ < ε`, as follows:
      -- `‖a • 𝟙ₛ - b • 𝟙ₜ‖ₚ`
      -- `= ‖a • 𝟙ₛ - b • 𝟙ₛ + b • 𝟙ₛ - b • 𝟙ₜ‖ₚ`
      -- `≤ ‖a - b‖ * ‖𝟙ₛ‖ₚ + ε / 3`
      -- `= ‖a - b‖ * (μ s)^(1/p) + ε / 3`
      -- `< ε * (μ s)^(1/p) / (3 * (1 + (μ s)^(1/p))) + ε / 3`
      -- `≤ ε / 3 + ε / 3 < ε`.
      refine ⟨indicatorConstLp p mt hμt b,
        ⟨1, fun _ => ⟨b, b_mem⟩, fun _ => ⟨t, ht⟩, by simp [key]⟩, ?_⟩
      rw [Lp.simpleFunc.coe_indicatorConst]; rw [← sub_add_sub_cancel _ (indicatorConstLp p ms hμs b)]; rw [← add_halves ε]
      refine lt_of_le_of_lt (b := ε / 3 + ε / 3) (norm_add_le_of_le ?_ hst.le) (by linarith [ε_pos])
      rw [indicatorConstLp_sub]; rw [norm_indicatorConstLp p_ne_zero p_ne_top.elim]
      calc
        ‖a - b‖ * μ.real s ^ (1 / p.toReal)
          <= (ε / (3 * (1 + μ.real s ^ (1 / p.toReal)))) * μ.real s ^ (1 / p.toReal) :=
              mul_le_mul_of_nonneg_right (le_of_lt hb) μs_pow_nonneg
        _ <= ε / 3 := by
            rw [← mul_one (ε / 3)]; rw [div_mul_eq_div_mul_one_div]; rw [mul_assoc]; rw [one_div_mul_eq_div]
            exact mul_le_mul_of_nonneg_left
              ((div_le_one (by linarith [μs_pow_nonneg])).2 (by linarith))
              (by linarith [ε_pos])
    · -- Now we have to show that the closure of `D` is closed by sum. Let `f` and `g` be two
      -- functions in `Lᵖ` which are also in the closure of `D`.
      rintro f g hf hg - f_mem g_mem
      rw [SeminormedAddCommGroup.mem_closure_iff] at *
      intro ε ε_pos
      -- For `ε > 0`, there exists `bf, bg ∈ D` such that `‖f - bf‖ₚ < ε/2` and `‖g - bg‖ₚ < ε/2`.
      rcases f_mem (ε / 2) (by linarith [ε_pos]) with ⟨bf, ⟨nf, df, sf, bf_eq⟩, hbf⟩
      rcases g_mem (ε / 2) (by linarith [ε_pos]) with ⟨bg, ⟨ng, dg, sg, bg_eq⟩, hbg⟩
      -- It is obvious that `D` is closed by sum, it suffices to concatenate the family of
      -- elements of `u` and the family of elements of `𝒜₀`.
      let d := fun i : Fin (nf + ng) => if h : i < nf
        then df (Fin.castLT i h)
        else dg (Fin.subNat nf (Fin.cast (Nat.add_comm ..) i) (le_of_not_gt h))
      let s := fun i : Fin (nf + ng) => if h : i < nf
        then sf (Fin.castLT i h)
        else sg (Fin.subNat nf (Fin.cast (Nat.add_comm ..) i) (le_of_not_gt h))
      -- So we can use `bf + bg`.
      refine ⟨bf + bg, ⟨nf + ng, d, s, ?_⟩, ?_⟩
      · simp [key, d, s, Fin.sum_univ_add, bf_eq, bg_eq]
      · -- We have
        -- `‖f + g - (bf + bg)‖ₚ`
        -- `≤ ‖f - bf‖ₚ + ‖g - bg‖ₚ`
        -- `< ε/2 + ε/2 = ε`.
        calc
          ‖MemLp.toLp f hf + MemLp.toLp g hg - (bf + bg)‖
            = ‖(MemLp.toLp f hf) - bf + ((MemLp.toLp g hg) - bg)‖ := by congr; abel
          _ <= ‖(MemLp.toLp f hf) - bf‖ + ‖(MemLp.toLp g hg) - bg‖ := norm_add_le ..
          _ < ε := by linarith [hbf, hbg]

end SecondCountableLp

end MeasureTheory
