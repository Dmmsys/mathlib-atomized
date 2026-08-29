/-
Copyright (c) 2022 Rémy Degenne, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.Egorov
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Convergence in measure

We define convergence in measure which is one of the many notions of convergence in probability.
A sequence of functions `f` is said to converge in measure to some function `g`
if for all `ε > 0`, the measure of the set `{x | ε ≤ edist (f i x) (g x)}` tends to 0 as `i`
converges along some given filter `l`.

Convergence in measure is most notably used in the formulation of the weak law of large numbers
and is also useful in theorems such as the Vitali convergence theorem. This file provides some
basic lemmas for working with convergence in measure and establishes some relations between
convergence in measure and other notions of convergence.

## Main definitions

* `MeasureTheory.TendstoInMeasure (μ : Measure α) (f : ι → α → E) (g : α → E)`: `f` converges
  in `μ`-measure to `g`.

## Main results

* `MeasureTheory.tendstoInMeasure_of_tendsto_ae`: convergence almost everywhere in a finite
  measure space implies convergence in measure.
* `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`: if `f` is a sequence of functions
  which converges in measure to `g`, then `f` has a subsequence which converges almost
  everywhere to `g`.
* `MeasureTheory.exists_seq_tendstoInMeasure_atTop_iff`: for a sequence of functions `f`,
  convergence in measure is equivalent to the fact that every subsequence has another subsequence
  that converges almost surely.
* `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm`: convergence in Lp implies convergence
  in measure.
-/

@[expose] public section


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory Topology

namespace MeasureTheory

variable {α ι κ E : Type*} {m : MeasurableSpace α} {μ : Measure α}

/--
Definition of `TendstoInMeasure` / `TendstoInMeasure` 的定义

English:
definition TendstoInMeasure
  signature: [EDist E] {_ : MeasurableSpace α} (μ : Measure α) (f : ι -> α -> E)
  body: forall ε, 0 < ε -> Tendsto (fun i => μ { x | ε <= edist (f i x) (g x) }) l (𝓝 0)

中文:
定义 TendstoInMeasure
  签名: [EDist E] {_ : 可测空间 α} (μ : 测度 α) (f : ι -> α -> E)
  定义体: forall ε, 0 < ε -> Tendsto (fun i => μ { x | ε <= edist (f i x) (g x) }) l (𝓝 0)

Depends on / 依赖: Tendsto
-/
def TendstoInMeasure [EDist E] {_ : MeasurableSpace α} (μ : Measure α) (f : ι -> α -> E)
    (l : Filter ι) (g : α -> E) : Prop :=
  forall ε, 0 < ε -> Tendsto (fun i => μ { x | ε <= edist (f i x) (g x) }) l (𝓝 0)

/--
lemma `tendstoInMeasure_of_ne_top` / 引理 `tendstoInMeasure_of_ne_top`

English:
lemma tendstoInMeasure_of_ne_top
  statement: [EDist E] {f : ι -> α -> E} {l : Filter ι} {g : α -> E}
  proof: by
  intro ε hε
  by_cases hε_top : ε = ∞
  · have h1 : Tendsto (fun n => μ {ω | 1 <= edist (f n ω) (g ω)}) l (𝓝 0) := h 1 (by simp) (by simp)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le) ?_
    intro n
    simp only [hε_top]
    gcongr
    simp
  · exact h ε hε hε_top

中文:
引理 tendstoInMeasure_of_ne_top
  结论: [EDist E] {f : ι -> α -> E} {l : 滤子 ι} {g : α -> E}
  证明: by
  intro ε hε
  by_cases hε_top : ε = ∞
  · have h1 : Tendsto (fun n => μ {ω | 1 <= edist (f n ω) (g ω)}) l (𝓝 0) := h 1 (by simp) (by simp)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le) ?_
    intro n
    simp only [hε_top]
    gcongr
    simp
  · exact h ε hε hε_top

Depends on / 依赖: Tendsto, tendsto_const_nhds, tendsto_of_tendsto_of_tendsto_of_le_of_le, zero_le
-/
lemma tendstoInMeasure_of_ne_top [EDist E] {f : ι -> α -> E} {l : Filter ι} {g : α -> E}
    (h : forall ε, 0 < ε -> ε != ∞ -> Tendsto (fun i => μ { x | ε <= edist (f i x) (g x) }) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  intro ε hε
  by_cases hε_top : ε = ∞
  · have h1 : Tendsto (fun n => μ {ω | 1 <= edist (f n ω) (g ω)}) l (𝓝 0) := h 1 (by simp) (by simp)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le) ?_
    intro n
    simp only [hε_top]
    gcongr
    simp
  · exact h ε hε hε_top

/--
theorem `tendstoInMeasure_iff_enorm` / 定理 `tendstoInMeasure_iff_enorm`

English:
theorem tendstoInMeasure_iff_enorm
  statement: [SeminormedAddCommGroup E] {l : Filter ι} {f : ι -> α -> E}
  proof: by
  simp_rw [← edist_eq_enorm_sub]
  exact ⟨fun h ε hε hε_top => h ε hε, tendstoInMeasure_of_ne_top⟩

中文:
定理 tendstoInMeasure_iff_enorm
  结论: [SeminormedAddComm群 E] {l : 滤子 ι} {f : ι -> α -> E}
  证明: by
  simp_rw [← edist_eq_enorm_sub]
  exact ⟨fun h ε hε hε_top => h ε hε, tendstoInMeasure_of_ne_top⟩

Depends on / 依赖: edist_eq_enorm_sub, simp_rw, tendstoInMeasure_of_ne_top
-/
theorem tendstoInMeasure_iff_enorm [SeminormedAddCommGroup E] {l : Filter ι} {f : ι -> α -> E}
    {g : α -> E} :
    TendstoInMeasure μ f l g ↔
      forall ε, 0 < ε -> ε != ∞ -> Tendsto (fun i => μ { x | ε <= ‖f i x - g x‖ₑ }) l (𝓝 0) := by
  simp_rw [← edist_eq_enorm_sub]
  exact ⟨fun h ε hε hε_top => h ε hε, tendstoInMeasure_of_ne_top⟩

/--
theorem `tendstoInMeasure_iff_measureReal_enorm` / 定理 `tendstoInMeasure_iff_measureReal_enorm`

English:
theorem tendstoInMeasure_iff_measureReal_enorm
  statement: [SeminormedAddCommGroup E] [IsFiniteMeasure μ]
  proof: by
  rw [tendstoInMeasure_iff_enorm]
  congr! with ε hε hε_top
  simp_rw [measureReal_def, ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)]

中文:
定理 tendstoInMeasure_iff_measure实数_enorm
  结论: [SeminormedAddComm群 E] [是有限测度 μ]
  证明: by
  rw [tendstoInMeasure_iff_enorm]
  congr! with ε hε hε_top
  simp_rw [measureReal_def, ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)]

Depends on / 依赖: ENNReal, ENNReal.tendsto_toReal_zero_iff, measureReal_def, measure_ne_top, simp_rw, tendstoInMeasure_iff_enorm, tendsto_toReal_zero_iff
-/
theorem tendstoInMeasure_iff_measureReal_enorm [SeminormedAddCommGroup E] [IsFiniteMeasure μ]
    {l : Filter ι} {f : ι -> α -> E} {g : α -> E} :
    TendstoInMeasure μ f l g ↔
      forall ε, 0 < ε -> ε != ∞ -> Tendsto (fun i => μ.real { x | ε <= ‖f i x - g x‖ₑ }) l (𝓝 0) := by
  rw [tendstoInMeasure_iff_enorm]
  congr! with ε hε hε_top
  simp_rw [measureReal_def, ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)]

/--
lemma `tendstoInMeasure_iff_dist` / 引理 `tendstoInMeasure_iff_dist`

English:
lemma tendstoInMeasure_iff_dist
  given: [PseudoMetricSpace E] {f : ι -> α -> E} {l : Filter ι} {g : α -> E}
  proof: by
  refine ⟨fun h ε hε => ?_, fun h => ?_⟩
  · convert! h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε) with i a
    rw [edist_dist]; rw [ENNReal.ofReal_le_ofReal_iff (by positivity)]
  · refine tendstoInMeasure_of_ne_top fun ε hε hε_top => ?_
    convert! h ε.toReal (ENNReal.toReal_pos hε.ne' hε_top) with i a
    rw [edist_dist]; rw [ENNReal.le_ofReal_iff_toReal_le hε_top (by positivity)]

中文:
引理 tendstoInMeasure_iff_dist
  条件: [伪度量空间 E] {f : ι -> α -> E} {l : 滤子 ι} {g : α -> E}
  证明: by
  refine ⟨fun h ε hε => ?_, fun h => ?_⟩
  · convert! h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε) with i a
    rw [edist_dist]; rw [ENNReal.ofReal_le_ofReal_iff (by positivity)]
  · refine tendstoInMeasure_of_ne_top fun ε hε hε_top => ?_
    convert! h ε.toReal (ENNReal.toReal_pos hε.ne' hε_top) with i a
    rw [edist_dist]; rw [ENNReal.le_ofReal_iff_toReal_le hε_top (by positivity)]

Depends on / 依赖: ENNReal, ENNReal.le_ofReal_iff_toReal_le, ENNReal.ofReal, ENNReal.ofReal_le_ofReal_iff, ENNReal.ofReal_pos.mpr, ENNReal.toReal_pos, convert, edist_dist, le_ofReal_iff_toReal_le, ofReal, ofReal_le_ofReal_iff, ofReal_pos, tendstoInMeasure_of_ne_top, toReal, toReal_pos
-/
lemma tendstoInMeasure_iff_dist [PseudoMetricSpace E] {f : ι -> α -> E} {l : Filter ι} {g : α -> E} :
    TendstoInMeasure μ f l g
      ↔ forall ε, 0 < ε -> Tendsto (fun i => μ { x | ε <= dist (f i x) (g x) }) l (𝓝 0) := by
  refine ⟨fun h ε hε => ?_, fun h => ?_⟩
  · convert! h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε) with i a
    rw [edist_dist]; rw [ENNReal.ofReal_le_ofReal_iff (by positivity)]
  · refine tendstoInMeasure_of_ne_top fun ε hε hε_top => ?_
    convert! h ε.toReal (ENNReal.toReal_pos hε.ne' hε_top) with i a
    rw [edist_dist]; rw [ENNReal.le_ofReal_iff_toReal_le hε_top (by positivity)]

/--
lemma `tendstoInMeasure_iff_measureReal_dist` / 引理 `tendstoInMeasure_iff_measureReal_dist`

English:
lemma tendstoInMeasure_iff_measureReal_dist
  statement: [PseudoMetricSpace E] [IsFiniteMeasure μ]
  proof: by
  rw [tendstoInMeasure_iff_dist]
  congr! with ε hε hε_top
  simp_rw [measureReal_def, ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)]

中文:
引理 tendstoInMeasure_iff_measure实数_dist
  结论: [伪度量空间 E] [是有限测度 μ]
  证明: by
  rw [tendstoInMeasure_iff_dist]
  congr! with ε hε hε_top
  simp_rw [measureReal_def, ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)]

Depends on / 依赖: ENNReal, ENNReal.tendsto_toReal_zero_iff, measureReal_def, measure_ne_top, simp_rw, tendstoInMeasure_iff_dist, tendsto_toReal_zero_iff
-/
lemma tendstoInMeasure_iff_measureReal_dist [PseudoMetricSpace E] [IsFiniteMeasure μ]
    {f : ι -> α -> E} {l : Filter ι} {g : α -> E} :
    TendstoInMeasure μ f l g ↔
      forall ε, 0 < ε -> Tendsto (fun i => μ.real { x | ε <= dist (f i x) (g x) }) l (𝓝 0) := by
  rw [tendstoInMeasure_iff_dist]
  congr! with ε hε hε_top
  simp_rw [measureReal_def, ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)]

/--
theorem `tendstoInMeasure_iff_norm` / 定理 `tendstoInMeasure_iff_norm`

English:
theorem tendstoInMeasure_iff_norm
  statement: [SeminormedAddCommGroup E] {l : Filter ι} {f : ι -> α -> E}
  proof: by
  simp_rw [tendstoInMeasure_iff_dist, dist_eq_norm_sub]

中文:
定理 tendstoInMeasure_iff_norm
  结论: [SeminormedAddComm群 E] {l : 滤子 ι} {f : ι -> α -> E}
  证明: by
  simp_rw [tendstoInMeasure_iff_dist, dist_eq_norm_sub]

Depends on / 依赖: dist_eq_norm_sub, simp_rw, tendstoInMeasure_iff_dist
-/
theorem tendstoInMeasure_iff_norm [SeminormedAddCommGroup E] {l : Filter ι} {f : ι -> α -> E}
    {g : α -> E} :
    TendstoInMeasure μ f l g ↔
      forall ε, 0 < ε -> Tendsto (fun i => μ { x | ε <= ‖f i x - g x‖ }) l (𝓝 0) := by
  simp_rw [tendstoInMeasure_iff_dist, dist_eq_norm_sub]

/--
lemma `tendstoInMeasure_iff_measureReal_norm` / 引理 `tendstoInMeasure_iff_measureReal_norm`

English:
lemma tendstoInMeasure_iff_measureReal_norm
  statement: [SeminormedAddCommGroup E] [IsFiniteMeasure μ]
  proof: by
  rw [tendstoInMeasure_iff_norm]
  congr! with ε hε hε_top
  simp_rw [measureReal_def, ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)]

中文:
引理 tendstoInMeasure_iff_measure实数_norm
  结论: [SeminormedAddComm群 E] [是有限测度 μ]
  证明: by
  rw [tendstoInMeasure_iff_norm]
  congr! with ε hε hε_top
  simp_rw [measureReal_def, ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)]

Depends on / 依赖: ENNReal, ENNReal.tendsto_toReal_zero_iff, measureReal_def, measure_ne_top, simp_rw, tendstoInMeasure_iff_norm, tendsto_toReal_zero_iff
-/
lemma tendstoInMeasure_iff_measureReal_norm [SeminormedAddCommGroup E] [IsFiniteMeasure μ]
    {l : Filter ι} {f : ι -> α -> E} {g : α -> E} :
    TendstoInMeasure μ f l g ↔
      forall ε, 0 < ε -> Tendsto (fun i => μ.real { x | ε <= ‖f i x - g x‖ }) l (𝓝 0) := by
  rw [tendstoInMeasure_iff_norm]
  congr! with ε hε hε_top
  simp_rw [measureReal_def, ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)]

/--
theorem `tendstoInMeasure_iff_tendsto_toNNReal` / 定理 `tendstoInMeasure_iff_tendsto_toNNReal`

English:
theorem tendstoInMeasure_iff_tendsto_toNNReal
  statement: [EDist E] [IsFiniteMeasure μ]
  proof: by
  have hfin ε i : μ { x | ε <= edist (f i x) (g x) } != ⊤ :=
    measure_ne_top μ {x | ε <= edist (f i x) (g x)}
  refine ⟨fun h ε hε => ?_, fun h ε hε => ?_⟩
  · have hf : (fun i => (μ { x | ε <= edist (f i x) (g x) }).toNNReal) =
        ENNReal.toNNReal ∘ (fun i => (μ { x | ε <= edist (f i x) (g x) })) := rfl
    rw [hf]; rw [ENNReal.tendsto_toNNReal_iff' (hfin ε)]
    exact h ε hε
  · rw [← ENNReal.tendsto_toNNReal_iff ENNReal.zero_ne_top (hfin ε)]
    exact h ε hε

中文:
定理 tendstoInMeasure_iff_tendsto_toNN实数
  结论: [EDist E] [是有限测度 μ]
  证明: by
  have hfin ε i : μ { x | ε <= edist (f i x) (g x) } != ⊤ :=
    measure_ne_top μ {x | ε <= edist (f i x) (g x)}
  refine ⟨fun h ε hε => ?_, fun h ε hε => ?_⟩
  · have hf : (fun i => (μ { x | ε <= edist (f i x) (g x) }).toNNReal) =
        ENNReal.toNNReal ∘ (fun i => (μ { x | ε <= edist (f i x) (g x) })) := rfl
    rw [hf]; rw [ENNReal.tendsto_toNNReal_iff' (hfin ε)]
    exact h ε hε
  · rw [← ENNReal.tendsto_toNNReal_iff ENNReal.zero_ne_top (hfin ε)]
    exact h ε hε

Depends on / 依赖: ENNReal, ENNReal.tendsto_toNNReal_iff, ENNReal.toNNReal, ENNReal.zero_ne_top, measure_ne_top, tendsto_toNNReal_iff, toNNReal, zero_ne_top
-/
theorem tendstoInMeasure_iff_tendsto_toNNReal [EDist E] [IsFiniteMeasure μ]
    {f : ι -> α -> E} {l : Filter ι} {g : α -> E} :
    TendstoInMeasure μ f l g ↔
      forall ε, 0 < ε -> Tendsto (fun i => (μ { x | ε <= edist (f i x) (g x) }).toNNReal) l (𝓝 0) := by
  have hfin ε i : μ { x | ε <= edist (f i x) (g x) } != ⊤ :=
    measure_ne_top μ {x | ε <= edist (f i x) (g x)}
  refine ⟨fun h ε hε => ?_, fun h ε hε => ?_⟩
  · have hf : (fun i => (μ { x | ε <= edist (f i x) (g x) }).toNNReal) =
        ENNReal.toNNReal ∘ (fun i => (μ { x | ε <= edist (f i x) (g x) })) := rfl
    rw [hf]; rw [ENNReal.tendsto_toNNReal_iff' (hfin ε)]
    exact h ε hε
  · rw [← ENNReal.tendsto_toNNReal_iff ENNReal.zero_ne_top (hfin ε)]
    exact h ε hε

namespace TendstoInMeasure

variable [EDist E] {l : Filter ι} {f f' : ι -> α -> E} {g g' : α -> E}

/--
lemma `mono` / 引理 `mono`

English:
lemma mono
  given: {v : Filter ι} (huv : v <= l) (hg : TendstoInMeasure μ f l g)
  proof: fun ε hε => (hg ε hε).mono_left huv

中文:
引理 mono
  条件: {v : 滤子 ι} (huv : v <= l) (hg : TendstoInMeasure μ f l g)
  证明: fun ε hε => (hg ε hε).mono_left huv

Depends on / 依赖: mono_left
-/
lemma mono {v : Filter ι} (huv : v <= l) (hg : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ f v g := fun ε hε => (hg ε hε).mono_left huv

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  statement: {v : Filter κ} {ns : κ -> ι} (hg : TendstoInMeasure μ f l g)
  proof: fun ε hε => (hg ε hε).comp hns

中文:
引理 comp
  结论: {v : 滤子 κ} {ns : κ -> ι} (hg : TendstoInMeasure μ f l g)
  证明: fun ε hε => (hg ε hε).comp hns
-/
lemma comp {v : Filter κ} {ns : κ -> ι} (hg : TendstoInMeasure μ f l g)
    (hns : Tendsto ns v l) : TendstoInMeasure μ (f ∘ ns) v g := fun ε hε => (hg ε hε).comp hns

/--
theorem `indicator` / 定理 `indicator`

English:
theorem indicator
  statement: {F : Type*} [PseudoEMetricSpace F] [Zero F] {f : ι -> α -> F} {g : α -> F}
  proof: by
  refine fun ε hε => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg ε hε) ?_ ?_
  · intro; simp
  · refine fun n => measure_mono (fun x hx => ?_)
    by_cases x in s <;> simp_all

中文:
定理 indicator
  结论: {F : 类型} [PseudoEMetric空间 F] [零 F] {f : ι -> α -> F} {g : α -> F}
  证明: by
  refine fun ε hε => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg ε hε) ?_ ?_
  · intro; simp
  · refine fun n => measure_mono (fun x hx => ?_)
    by_cases x in s <;> simp_all

Depends on / 依赖: measure_mono, tendsto_const_nhds, tendsto_of_tendsto_of_tendsto_of_le_of_le
-/
theorem indicator {F : Type*} [PseudoEMetricSpace F] [Zero F] {f : ι -> α -> F} {g : α -> F}
    (hg : TendstoInMeasure μ f l g) (s : Set α) :
    TendstoInMeasure μ (fun i => s.indicator (f i)) l (s.indicator g) := by
  refine fun ε hε => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg ε hε) ?_ ?_
  · intro; simp
  · refine fun n => measure_mono (fun x hx => ?_)
    by_cases x in s <;> simp_all

/--
theorem `congr'` / 定理 `congr'`

English:
theorem congr'
  statement: (h_left : forallᶠ i in l, f i =ᵐ[μ] f' i) (h_right : g =ᵐ[μ] g')
  proof: by
  intro ε hε
  suffices
    (fun i => μ { x | ε <= edist (f' i x) (g' x) }) =ᶠ[l] fun i => μ { x | ε <= edist (f i x) (g x) } by
    rw [tendsto_congr' this]
    exact h_tendsto ε hε
  filter_upwards [h_left] with i h_ae_eq
  refine measure_congr ?_
  filter_upwards [h_ae_eq, h_right] with x hxf hxg
  rw [eq_iff_iff]
  change ε <= edist (f' i x) (g' x) ↔ ε <= edist (f i x) (g x)
  rw [hxg]; rw [hxf]

中文:
定理 congr'
  结论: (h_left : 对任意ᶠ i in l, f i =ᵐ[μ] f' i) (h_right : g =ᵐ[μ] g')
  证明: by
  intro ε hε
  suffices
    (fun i => μ { x | ε <= edist (f' i x) (g' x) }) =ᶠ[l] fun i => μ { x | ε <= edist (f i x) (g x) } by
    rw [tendsto_congr' this]
    exact h_tendsto ε hε
  filter_upwards [h_left] with i h_ae_eq
  refine measure_congr ?_
  filter_upwards [h_ae_eq, h_right] with x hxf hxg
  rw [eq_iff_iff]
  change ε <= edist (f' i x) (g' x) ↔ ε <= edist (f i x) (g x)
  rw [hxg]; rw [hxf]
-/
protected theorem congr' (h_left : forallᶠ i in l, f i =ᵐ[μ] f' i) (h_right : g =ᵐ[μ] g')
    (h_tendsto : TendstoInMeasure μ f l g) : TendstoInMeasure μ f' l g' := by
  intro ε hε
  suffices
    (fun i => μ { x | ε <= edist (f' i x) (g' x) }) =ᶠ[l] fun i => μ { x | ε <= edist (f i x) (g x) } by
    rw [tendsto_congr' this]
    exact h_tendsto ε hε
  filter_upwards [h_left] with i h_ae_eq
  refine measure_congr ?_
  filter_upwards [h_ae_eq, h_right] with x hxf hxg
  rw [eq_iff_iff]
  change ε <= edist (f' i x) (g' x) ↔ ε <= edist (f i x) (g x)
  rw [hxg]; rw [hxf]

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  statement: (h_left : forall i, f i =ᵐ[μ] f' i) (h_right : g =ᵐ[μ] g')
  proof: TendstoInMeasure.congr' (Eventually.of_forall h_left) h_right h_tendsto

中文:
定理 congr
  结论: (h_left : 对任意 i, f i =ᵐ[μ] f' i) (h_right : g =ᵐ[μ] g')
  证明: TendstoInMeasure.congr' (Eventually.of_forall h_left) h_right h_tendsto
-/
protected theorem congr (h_left : forall i, f i =ᵐ[μ] f' i) (h_right : g =ᵐ[μ] g')
    (h_tendsto : TendstoInMeasure μ f l g) : TendstoInMeasure μ f' l g' :=
  TendstoInMeasure.congr' (Eventually.of_forall h_left) h_right h_tendsto

/--
theorem `congr_left` / 定理 `congr_left`

English:
theorem congr_left
  given: (h : forall i, f i =ᵐ[μ] f' i) (h_tendsto : TendstoInMeasure μ f l g)
  proof: h_tendsto.congr h EventuallyEq.rfl

中文:
定理 congr_left
  条件: (h : 对任意 i, f i =ᵐ[μ] f' i) (h_tendsto : TendstoInMeasure μ f l g)
  证明: h_tendsto.congr h EventuallyEq.rfl

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl, h_tendsto, h_tendsto.congr
-/
theorem congr_left (h : forall i, f i =ᵐ[μ] f' i) (h_tendsto : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ f' l g :=
  h_tendsto.congr h EventuallyEq.rfl

/--
theorem `congr_right` / 定理 `congr_right`

English:
theorem congr_right
  given: (h : g =ᵐ[μ] g') (h_tendsto : TendstoInMeasure μ f l g)
  proof: h_tendsto.congr (fun _ => EventuallyEq.rfl) h

中文:
定理 congr_right
  条件: (h : g =ᵐ[μ] g') (h_tendsto : TendstoInMeasure μ f l g)
  证明: h_tendsto.congr (fun _ => EventuallyEq.rfl) h

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl, h_tendsto, h_tendsto.congr
-/
theorem congr_right (h : g =ᵐ[μ] g') (h_tendsto : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ f l g' :=
  h_tendsto.congr (fun _ => EventuallyEq.rfl) h

end TendstoInMeasure

section ExistsSeqTendstoAe

variable [PseudoEMetricSpace E]
variable {f : Nat -> α -> E} {g : α -> E}

/--
theorem `tendstoInMeasure_of_tendsto_ae_of_measurable_edist` / 定理 `tendstoInMeasure_of_tendsto_ae_of_measurable_edist`

English:
theorem tendstoInMeasure_of_tendsto_ae_of_measurable_edist
  statement: [IsFiniteMeasure μ]
  proof: by
  refine fun ε hε => ENNReal.tendsto_atTop_zero.mpr fun δ hδ => ?_
  by_cases hδi : δ = ∞
  · simp only [hδi, imp_true_iff, le_top, exists_const]
  lift δ to Real>=0 using hδi
  rw [gt_iff_lt]; rw [ENNReal.coe_pos]; rw [← NNReal.coe_pos] at hδ
  obtain ⟨t, _, ht, hunif⟩ :=
    tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist' hf hfg hδ
  rw [ENNReal.ofReal_coe_nnreal] at ht
  rw [EMetric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif ε hε)
  refine ⟨N, fun n hn => ?_⟩
  suffices { x : α | ε <= edist (f n x) (g x) } subseteq t from (measure_mono this).trans ht
  rw [← Set.compl_subset_compl]
  intro x hx
  rw [Set.mem_compl_iff]; rw [Set.notMem_ofPred_iff]; rw [edist_comm]; rw [not_le]
  exact hN n hn x hx

中文:
定理 tendstoInMeasure_of_tendsto_ae_of_measurable_edist
  结论: [是有限测度 μ]
  证明: by
  refine fun ε hε => ENNReal.tendsto_atTop_zero.mpr fun δ hδ => ?_
  by_cases hδi : δ = ∞
  · simp only [hδi, imp_true_iff, le_top, exists_const]
  lift δ to Real>=0 using hδi
  rw [gt_iff_lt]; rw [ENNReal.coe_pos]; rw [← NNReal.coe_pos] at hδ
  obtain ⟨t, _, ht, hunif⟩ :=
    tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist' hf hfg hδ
  rw [ENNReal.ofReal_coe_nnreal] at ht
  rw [EMetric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif ε hε)
  refine ⟨N, fun n hn => ?_⟩
  suffices { x : α | ε <= edist (f n x) (g x) } subseteq t from (measure_mono this).trans ht
  rw [← Set.compl_subset_compl]
  intro x hx
  rw [Set.mem_compl_iff]; rw [Set.notMem_ofPred_iff]; rw [edist_comm]; rw [not_le]
  exact hN n hn x hx

Depends on / 依赖: EMetric, EMetric.tendstoUniformlyOn_iff, ENNReal, ENNReal.coe_pos, ENNReal.ofReal_coe_nnreal, ENNReal.tendsto_atTop_zero.mpr, NNReal, NNReal.coe_pos, coe_pos, eventually_atTop, exists_const, gt_iff_lt, imp_true_iff, le_top, ofReal_coe_nnreal, tendstoUniformlyOn_iff, tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist, tendsto_atTop_zero
-/
theorem tendstoInMeasure_of_tendsto_ae_of_measurable_edist [IsFiniteMeasure μ]
    (hf : forall n, Measurable (fun a => edist (f n a) (g a)))
    (hfg : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : TendstoInMeasure μ f atTop g := by
  refine fun ε hε => ENNReal.tendsto_atTop_zero.mpr fun δ hδ => ?_
  by_cases hδi : δ = ∞
  · simp only [hδi, imp_true_iff, le_top, exists_const]
  lift δ to Real>=0 using hδi
  rw [gt_iff_lt]; rw [ENNReal.coe_pos]; rw [← NNReal.coe_pos] at hδ
  obtain ⟨t, _, ht, hunif⟩ :=
    tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist' hf hfg hδ
  rw [ENNReal.ofReal_coe_nnreal] at ht
  rw [EMetric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif ε hε)
  refine ⟨N, fun n hn => ?_⟩
  suffices { x : α | ε <= edist (f n x) (g x) } subseteq t from (measure_mono this).trans ht
  rw [← Set.compl_subset_compl]
  intro x hx
  rw [Set.mem_compl_iff]; rw [Set.notMem_ofPred_iff]; rw [edist_comm]; rw [not_le]
  exact hN n hn x hx

/--
theorem `tendstoInMeasure_of_tendsto_ae` / 定理 `tendstoInMeasure_of_tendsto_ae`

English:
theorem tendstoInMeasure_of_tendsto_ae
  statement: [IsFiniteMeasure μ] (hf : forall n, AEStronglyMeasurable (f n) μ)
  proof: by
  have hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae _ hf hfg
  refine TendstoInMeasure.congr (fun i => (hf i).ae_eq_mk.symm) hg.ae_eq_mk.symm ?_
  refine tendstoInMeasure_of_tendsto_ae_of_measurable_edist
    (fun n => ((hf n).stronglyMeasurable_mk.edist hg.stronglyMeasurable_mk).measurable) ?_
  have hf_eq_ae : forallᵐ x ∂μ, forall n, (hf n).mk (f n) x = f n x :=
    ae_all_iff.mpr fun n => (hf n).ae_eq_mk.symm
  filter_upwards [hf_eq_ae, hg.ae_eq_mk, hfg] with x hxf hxg hxfg
  rw [← hxg]; rw [funext fun n => hxf n]
  exact hxfg

中文:
定理 tendstoInMeasure_of_tendsto_ae
  结论: [是有限测度 μ] (hf : 对任意 n, AEStronglyMeasurable (f n) μ)
  证明: by
  have hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae _ hf hfg
  refine TendstoInMeasure.congr (fun i => (hf i).ae_eq_mk.symm) hg.ae_eq_mk.symm ?_
  refine tendstoInMeasure_of_tendsto_ae_of_measurable_edist
    (fun n => ((hf n).stronglyMeasurable_mk.edist hg.stronglyMeasurable_mk).measurable) ?_
  have hf_eq_ae : forallᵐ x ∂μ, forall n, (hf n).mk (f n) x = f n x :=
    ae_all_iff.mpr fun n => (hf n).ae_eq_mk.symm
  filter_upwards [hf_eq_ae, hg.ae_eq_mk, hfg] with x hxf hxg hxfg
  rw [← hxg]; rw [funext fun n => hxf n]
  exact hxfg

Depends on / 依赖: AEStronglyMeasurable, TendstoInMeasure, TendstoInMeasure.congr, ae_all_iff, ae_all_iff.mpr, ae_eq_mk, ae_eq_mk.symm, aestronglyMeasurable_of_tendsto_ae, filter_upwards, hf_eq_ae, hg.ae_eq_mk, hg.ae_eq_mk.symm, hg.stronglyMeasurable_mk, measurable, stronglyMeasurable_mk, stronglyMeasurable_mk.edist, tendstoInMeasure_of_tendsto_ae_of_measurable_edist
-/
theorem tendstoInMeasure_of_tendsto_ae [IsFiniteMeasure μ] (hf : forall n, AEStronglyMeasurable (f n) μ)
    (hfg : forallᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : TendstoInMeasure μ f atTop g := by
  have hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae _ hf hfg
  refine TendstoInMeasure.congr (fun i => (hf i).ae_eq_mk.symm) hg.ae_eq_mk.symm ?_
  refine tendstoInMeasure_of_tendsto_ae_of_measurable_edist
    (fun n => ((hf n).stronglyMeasurable_mk.edist hg.stronglyMeasurable_mk).measurable) ?_
  have hf_eq_ae : forallᵐ x ∂μ, forall n, (hf n).mk (f n) x = f n x :=
    ae_all_iff.mpr fun n => (hf n).ae_eq_mk.symm
  filter_upwards [hf_eq_ae, hg.ae_eq_mk, hfg] with x hxf hxg hxfg
  rw [← hxg]; rw [funext fun n => hxf n]
  exact hxfg

namespace ExistsSeqTendstoAe

/--
theorem `exists_nat_measure_lt_two_inv` / 定理 `exists_nat_measure_lt_two_inv`

English:
theorem exists_nat_measure_lt_two_inv
  given: (hfg : TendstoInMeasure μ f atTop g) (n : Nat)
  proof: by
  specialize hfg ((2⁻¹ : Real>=0∞) ^ n) (ENNReal.pow_pos (by simp) _)
  rw [ENNReal.tendsto_atTop_zero] at hfg
  exact hfg ((2 : Real>=0∞)⁻¹ ^ n) (pos_iff_ne_zero.mpr <| pow_ne_zero _ <| by simp)

中文:
定理 存在_nat_measure_lt_two_inv
  条件: (hfg : TendstoInMeasure μ f atTop g) (n : 自然数)
  证明: by
  specialize hfg ((2⁻¹ : Real>=0∞) ^ n) (ENNReal.pow_pos (by simp) _)
  rw [ENNReal.tendsto_atTop_zero] at hfg
  exact hfg ((2 : Real>=0∞)⁻¹ ^ n) (pos_iff_ne_zero.mpr <| pow_ne_zero _ <| by simp)

Depends on / 依赖: ENNReal, ENNReal.pow_pos, ENNReal.tendsto_atTop_zero, pos_iff_ne_zero, pos_iff_ne_zero.mpr, pow_ne_zero, pow_pos, specialize, tendsto_atTop_zero
-/
theorem exists_nat_measure_lt_two_inv (hfg : TendstoInMeasure μ f atTop g) (n : Nat) :
    exists N, forall m >= N, μ { x | (2 : Real>=0∞)⁻¹ ^ n <= edist (f m x) (g x) } <= (2⁻¹ : Real>=0∞) ^ n := by
  specialize hfg ((2⁻¹ : Real>=0∞) ^ n) (ENNReal.pow_pos (by simp) _)
  rw [ENNReal.tendsto_atTop_zero] at hfg
  exact hfg ((2 : Real>=0∞)⁻¹ ^ n) (pos_iff_ne_zero.mpr <| pow_ne_zero _ <| by simp)

/--
Definition of `seqTendstoAeSeqAux` / `seqTendstoAeSeqAux` 的定义

English:
definition seqTendstoAeSeqAux
  signature: (hfg : TendstoInMeasure μ f atTop g) (n : Nat)
  body: Classical.choose (exists_nat_measure_lt_two_inv hfg n)

中文:
定义 seqTendstoAeSeqAux
  签名: (hfg : TendstoInMeasure μ f atTop g) (n : 自然数)
  定义体: Classical.choose (exists_nat_measure_lt_two_inv hfg n)

Depends on / 依赖: Classical, Classical.choose, exists_nat_measure_lt_two_inv
-/
noncomputable def seqTendstoAeSeqAux (hfg : TendstoInMeasure μ f atTop g) (n : Nat) :=
  Classical.choose (exists_nat_measure_lt_two_inv hfg n)

/--
Definition of `seqTendstoAeSeq` / `seqTendstoAeSeq` 的定义

English:
definition seqTendstoAeSeq
  signature: (hfg : TendstoInMeasure μ f atTop g)

中文:
定义 seqTendstoAeSeq
  签名: (hfg : TendstoInMeasure μ f atTop g)
-/
noncomputable def seqTendstoAeSeq (hfg : TendstoInMeasure μ f atTop g) : Nat -> Nat
  | 0 => seqTendstoAeSeqAux hfg 0
  | n + 1 => max (seqTendstoAeSeqAux hfg (n + 1)) (seqTendstoAeSeq hfg n + 1)

/--
theorem `seqTendstoAeSeq_succ` / 定理 `seqTendstoAeSeq_succ`

English:
theorem seqTendstoAeSeq_succ
  given: (hfg : TendstoInMeasure μ f atTop g) {n : Nat}
  proof: by
  rw [seqTendstoAeSeq]

中文:
定理 seqTendstoAeSeq_succ
  条件: (hfg : TendstoInMeasure μ f atTop g) {n : 自然数}
  证明: by
  rw [seqTendstoAeSeq]

Depends on / 依赖: seqTendstoAeSeq
-/
theorem seqTendstoAeSeq_succ (hfg : TendstoInMeasure μ f atTop g) {n : Nat} :
    seqTendstoAeSeq hfg (n + 1) =
      max (seqTendstoAeSeqAux hfg (n + 1)) (seqTendstoAeSeq hfg n + 1) := by
  rw [seqTendstoAeSeq]

/--
theorem `seqTendstoAeSeq_spec` / 定理 `seqTendstoAeSeq_spec`

English:
theorem seqTendstoAeSeq_spec
  statement: (hfg : TendstoInMeasure μ f atTop g) (n k : Nat)
  proof: by
  cases n
  · exact Classical.choose_spec (exists_nat_measure_lt_two_inv hfg 0) k hn
  · exact Classical.choose_spec
      (exists_nat_measure_lt_two_inv hfg _) _ (le_trans (le_max_left _ _) hn)

中文:
定理 seqTendstoAeSeq_spec
  结论: (hfg : TendstoInMeasure μ f atTop g) (n k : 自然数)
  证明: by
  cases n
  · exact Classical.choose_spec (exists_nat_measure_lt_two_inv hfg 0) k hn
  · exact Classical.choose_spec
      (exists_nat_measure_lt_two_inv hfg _) _ (le_trans (le_max_left _ _) hn)

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, exists_nat_measure_lt_two_inv, le_max_left, le_trans
-/
theorem seqTendstoAeSeq_spec (hfg : TendstoInMeasure μ f atTop g) (n k : Nat)
    (hn : seqTendstoAeSeq hfg n <= k) :
    μ { x | (2 : Real>=0∞)⁻¹ ^ n <= edist (f k x) (g x) } <= (2 : Real>=0∞)⁻¹ ^ n := by
  cases n
  · exact Classical.choose_spec (exists_nat_measure_lt_two_inv hfg 0) k hn
  · exact Classical.choose_spec
      (exists_nat_measure_lt_two_inv hfg _) _ (le_trans (le_max_left _ _) hn)

/--
theorem `seqTendstoAeSeq_strictMono` / 定理 `seqTendstoAeSeq_strictMono`

English:
theorem seqTendstoAeSeq_strictMono
  given: (hfg : TendstoInMeasure μ f atTop g)
  proof: by
  refine strictMono_nat_of_lt_succ fun n => ?_
  rw [seqTendstoAeSeq_succ]
  exact lt_of_lt_of_le (lt_add_one <| seqTendstoAeSeq hfg n) (le_max_right _ _)

中文:
定理 seqTendstoAeSeq_strictMono
  条件: (hfg : TendstoInMeasure μ f atTop g)
  证明: by
  refine strictMono_nat_of_lt_succ fun n => ?_
  rw [seqTendstoAeSeq_succ]
  exact lt_of_lt_of_le (lt_add_one <| seqTendstoAeSeq hfg n) (le_max_right _ _)

Depends on / 依赖: le_max_right, lt_add_one, lt_of_lt_of_le, seqTendstoAeSeq, seqTendstoAeSeq_succ, strictMono_nat_of_lt_succ
-/
theorem seqTendstoAeSeq_strictMono (hfg : TendstoInMeasure μ f atTop g) :
    StrictMono (seqTendstoAeSeq hfg) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  rw [seqTendstoAeSeq_succ]
  exact lt_of_lt_of_le (lt_add_one <| seqTendstoAeSeq hfg n) (le_max_right _ _)

end ExistsSeqTendstoAe

/--
theorem `TendstoInMeasure.exists_seq_tendsto_ae` / 定理 `TendstoInMeasure.exists_seq_tendsto_ae`

English:
theorem TendstoInMeasure.exists_seq_tendsto_ae
  given: (hfg : TendstoInMeasure μ f atTop g)
  proof: by
  /- Since `f` tends to `g` in measure, it has a subsequence `k ↦ f (ns k)` such that
    `μ {|f (ns k) - g| ≥ 2⁻ᵏ} ≤ 2⁻ᵏ` for all `k`. Defining
    `s := ⋂ k, ⋃ i ≥ k, {|f (ns k) - g| ≥ 2⁻ᵏ}`, we see that `μ s = 0` by the
    first Borel-Cantelli lemma.

    On the other hand, as `s` is precisely the set for which `f (ns k)`
    doesn't converge to `g`, `f (ns k)` converges almost everywhere to `g` as required. -/
  have h_lt_ε_real (ε : Real>=0∞) (hε : 0 < ε) : exists k : Nat, 2 * (2 : Real>=0∞)⁻¹ ^ k < ε := by
    obtain ⟨k, h_k⟩ : exists k : Nat, (2 : Real>=0∞)⁻¹ ^ k < ε := ENNReal.exists_inv_two_pow_lt hε.ne'
    refine ⟨k + 1, lt_of_eq_of_lt ?_ h_k⟩
    rw [pow_succ']; rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel]; rw [one_mul]
    · positivity
    · simp
  set ns := ExistsSeqTendstoAe.seqTendstoAeSeq hfg
  use ns
  let S := fun k => { x | (2 : Real>=0∞)⁻¹ ^ k <= edist (f (ns k) x) (g x) }
  have hμS_le : forall k, μ (S k) <= (2 : Real>=0∞)⁻¹ ^ k :=
    fun k => ExistsSeqTendstoAe.seqTendstoAeSeq_spec hfg k (ns k) le_rfl
  set s := Filter.atTop.limsup S with hs
  have hμs : μ s = 0 := by
    refine measure_limsup_atTop_eq_zero (ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hμS_le))
    simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using ENNReal.ofNat_ne_top
  have h_tendsto : forall x in sᶜ, Tendsto (fun i => f (ns i) x) atTop (𝓝 (g x)) := by
    refine fun x hx => EMetric.tendsto_atTop.mpr fun ε hε => ?_
    rw [hs]; rw [limsup_eq_iInf_iSup_of_nat] at hx
    simp only [S, Set.iSup_eq_iUnion, Set.iInf_eq_iInter, Set.compl_iInter, Set.compl_iUnion,
      Set.mem_iUnion, Set.mem_iInter, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
    obtain ⟨N, hNx⟩ := hx
    obtain ⟨k, hk_lt_ε⟩ := h_lt_ε_real ε hε
    refine ⟨max N (k - 1), fun n hn_ge => lt_of_le_of_lt ?_ hk_lt_ε⟩
    specialize hNx n ((le_max_left _ _).trans hn_ge)
    have h_inv_n_le_k : (2 : Real>=0∞)⁻¹ ^ n <= 2 * (2 : Real>=0∞)⁻¹ ^ k := by
      nth_rw 2 [← pow_one (2 : Real>=0∞)]
      rw [mul_comm]; rw [← ENNReal.inv_pow]; rw [← ENNReal.inv_pow]; rw [ENNReal.inv_le_iff_le_mul]; rw [← mul_assoc]; rw [mul_comm (_ ^ n)]; rw [mul_assoc]; rw [← ENNReal.inv_le_iff_le_mul]; rw [inv_inv]; rw [← pow_add]
      · gcongr
        · simp
        · omega
      all_goals simp
    exact le_trans hNx.le h_inv_n_le_k
  rw [ae_iff]
  refine ⟨ExistsSeqTendstoAe.seqTendstoAeSeq_strictMono hfg, measure_mono_null (fun x => ?_) hμs⟩
  rw [Set.mem_ofPred_eq]; rw [← @Classical.not_not (x in s)]; rw [not_imp_not]
  exact h_tendsto x

中文:
定理 TendstoInMeasure.存在_seq_tendsto_ae
  条件: (hfg : TendstoInMeasure μ f atTop g)
  证明: by
  /- Since `f` tends to `g` in measure, it has a subsequence `k ↦ f (ns k)` such that
    `μ {|f (ns k) - g| ≥ 2⁻ᵏ} ≤ 2⁻ᵏ` for all `k`. Defining
    `s := ⋂ k, ⋃ i ≥ k, {|f (ns k) - g| ≥ 2⁻ᵏ}`, we see that `μ s = 0` by the
    first Borel-Cantelli lemma.

    On the other hand, as `s` is precisely the set for which `f (ns k)`
    doesn't converge to `g`, `f (ns k)` converges almost everywhere to `g` as required. -/
  have h_lt_ε_real (ε : Real>=0∞) (hε : 0 < ε) : exists k : Nat, 2 * (2 : Real>=0∞)⁻¹ ^ k < ε := by
    obtain ⟨k, h_k⟩ : exists k : Nat, (2 : Real>=0∞)⁻¹ ^ k < ε := ENNReal.exists_inv_two_pow_lt hε.ne'
    refine ⟨k + 1, lt_of_eq_of_lt ?_ h_k⟩
    rw [pow_succ']; rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel]; rw [one_mul]
    · positivity
    · simp
  set ns := ExistsSeqTendstoAe.seqTendstoAeSeq hfg
  use ns
  let S := fun k => { x | (2 : Real>=0∞)⁻¹ ^ k <= edist (f (ns k) x) (g x) }
  have hμS_le : forall k, μ (S k) <= (2 : Real>=0∞)⁻¹ ^ k :=
    fun k => ExistsSeqTendstoAe.seqTendstoAeSeq_spec hfg k (ns k) le_rfl
  set s := Filter.atTop.limsup S with hs
  have hμs : μ s = 0 := by
    refine measure_limsup_atTop_eq_zero (ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hμS_le))
    simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using ENNReal.ofNat_ne_top
  have h_tendsto : forall x in sᶜ, Tendsto (fun i => f (ns i) x) atTop (𝓝 (g x)) := by
    refine fun x hx => EMetric.tendsto_atTop.mpr fun ε hε => ?_
    rw [hs]; rw [limsup_eq_iInf_iSup_of_nat] at hx
    simp only [S, Set.iSup_eq_iUnion, Set.iInf_eq_iInter, Set.compl_iInter, Set.compl_iUnion,
      Set.mem_iUnion, Set.mem_iInter, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
    obtain ⟨N, hNx⟩ := hx
    obtain ⟨k, hk_lt_ε⟩ := h_lt_ε_real ε hε
    refine ⟨max N (k - 1), fun n hn_ge => lt_of_le_of_lt ?_ hk_lt_ε⟩
    specialize hNx n ((le_max_left _ _).trans hn_ge)
    have h_inv_n_le_k : (2 : Real>=0∞)⁻¹ ^ n <= 2 * (2 : Real>=0∞)⁻¹ ^ k := by
      nth_rw 2 [← pow_one (2 : Real>=0∞)]
      rw [mul_comm]; rw [← ENNReal.inv_pow]; rw [← ENNReal.inv_pow]; rw [ENNReal.inv_le_iff_le_mul]; rw [← mul_assoc]; rw [mul_comm (_ ^ n)]; rw [mul_assoc]; rw [← ENNReal.inv_le_iff_le_mul]; rw [inv_inv]; rw [← pow_add]
      · gcongr
        · simp
        · omega
      all_goals simp
    exact le_trans hNx.le h_inv_n_le_k
  rw [ae_iff]
  refine ⟨ExistsSeqTendstoAe.seqTendstoAeSeq_strictMono hfg, measure_mono_null (fun x => ?_) hμs⟩
  rw [Set.mem_ofPred_eq]; rw [← @Classical.not_not (x in s)]; rw [not_imp_not]
  exact h_tendsto x
-/
theorem TendstoInMeasure.exists_seq_tendsto_ae (hfg : TendstoInMeasure μ f atTop g) :
    exists ns : Nat -> Nat, StrictMono ns ∧ forallᵐ x ∂μ, Tendsto (fun i => f (ns i) x) atTop (𝓝 (g x)) := by
  /- Since `f` tends to `g` in measure, it has a subsequence `k ↦ f (ns k)` such that
    `μ {|f (ns k) - g| ≥ 2⁻ᵏ} ≤ 2⁻ᵏ` for all `k`. Defining
    `s := ⋂ k, ⋃ i ≥ k, {|f (ns k) - g| ≥ 2⁻ᵏ}`, we see that `μ s = 0` by the
    first Borel-Cantelli lemma.

    On the other hand, as `s` is precisely the set for which `f (ns k)`
    doesn't converge to `g`, `f (ns k)` converges almost everywhere to `g` as required. -/
  have h_lt_ε_real (ε : Real>=0∞) (hε : 0 < ε) : exists k : Nat, 2 * (2 : Real>=0∞)⁻¹ ^ k < ε := by
    obtain ⟨k, h_k⟩ : exists k : Nat, (2 : Real>=0∞)⁻¹ ^ k < ε := ENNReal.exists_inv_two_pow_lt hε.ne'
    refine ⟨k + 1, lt_of_eq_of_lt ?_ h_k⟩
    rw [pow_succ']; rw [← mul_assoc]; rw [ENNReal.mul_inv_cancel]; rw [one_mul]
    · positivity
    · simp
  set ns := ExistsSeqTendstoAe.seqTendstoAeSeq hfg
  use ns
  let S := fun k => { x | (2 : Real>=0∞)⁻¹ ^ k <= edist (f (ns k) x) (g x) }
  have hμS_le : forall k, μ (S k) <= (2 : Real>=0∞)⁻¹ ^ k :=
    fun k => ExistsSeqTendstoAe.seqTendstoAeSeq_spec hfg k (ns k) le_rfl
  set s := Filter.atTop.limsup S with hs
  have hμs : μ s = 0 := by
    refine measure_limsup_atTop_eq_zero (ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hμS_le))
    simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using ENNReal.ofNat_ne_top
  have h_tendsto : forall x in sᶜ, Tendsto (fun i => f (ns i) x) atTop (𝓝 (g x)) := by
    refine fun x hx => EMetric.tendsto_atTop.mpr fun ε hε => ?_
    rw [hs]; rw [limsup_eq_iInf_iSup_of_nat] at hx
    simp only [S, Set.iSup_eq_iUnion, Set.iInf_eq_iInter, Set.compl_iInter, Set.compl_iUnion,
      Set.mem_iUnion, Set.mem_iInter, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
    obtain ⟨N, hNx⟩ := hx
    obtain ⟨k, hk_lt_ε⟩ := h_lt_ε_real ε hε
    refine ⟨max N (k - 1), fun n hn_ge => lt_of_le_of_lt ?_ hk_lt_ε⟩
    specialize hNx n ((le_max_left _ _).trans hn_ge)
    have h_inv_n_le_k : (2 : Real>=0∞)⁻¹ ^ n <= 2 * (2 : Real>=0∞)⁻¹ ^ k := by
      nth_rw 2 [← pow_one (2 : Real>=0∞)]
      rw [mul_comm]; rw [← ENNReal.inv_pow]; rw [← ENNReal.inv_pow]; rw [ENNReal.inv_le_iff_le_mul]; rw [← mul_assoc]; rw [mul_comm (_ ^ n)]; rw [mul_assoc]; rw [← ENNReal.inv_le_iff_le_mul]; rw [inv_inv]; rw [← pow_add]
      · gcongr
        · simp
        · omega
      all_goals simp
    exact le_trans hNx.le h_inv_n_le_k
  rw [ae_iff]
  refine ⟨ExistsSeqTendstoAe.seqTendstoAeSeq_strictMono hfg, measure_mono_null (fun x => ?_) hμs⟩
  rw [Set.mem_ofPred_eq]; rw [← @Classical.not_not (x in s)]; rw [not_imp_not]
  exact h_tendsto x

/--
theorem `TendstoInMeasure.exists_seq_tendstoInMeasure_atTop` / 定理 `TendstoInMeasure.exists_seq_tendstoInMeasure_atTop`

English:
theorem TendstoInMeasure.exists_seq_tendstoInMeasure_atTop
  statement: {u : Filter ι} [NeBot u]
  proof: by
  obtain ⟨ns, h_tendsto_ns⟩ : exists ns : Nat -> ι, Tendsto ns atTop u := exists_seq_tendsto u
  exact ⟨ns, h_tendsto_ns, fun ε hε => (hfg ε hε).comp h_tendsto_ns⟩

中文:
定理 TendstoInMeasure.存在_seq_tendstoInMeasure_atTop
  结论: {u : 滤子 ι} [NeBot u]
  证明: by
  obtain ⟨ns, h_tendsto_ns⟩ : exists ns : Nat -> ι, Tendsto ns atTop u := exists_seq_tendsto u
  exact ⟨ns, h_tendsto_ns, fun ε hε => (hfg ε hε).comp h_tendsto_ns⟩

Depends on / 依赖: Tendsto, exists_seq_tendsto, h_tendsto_ns
-/
theorem TendstoInMeasure.exists_seq_tendstoInMeasure_atTop {u : Filter ι} [NeBot u]
    [IsCountablyGenerated u] {f : ι -> α -> E} {g : α -> E} (hfg : TendstoInMeasure μ f u g) :
    exists ns : Nat -> ι, Tendsto ns atTop u ∧ TendstoInMeasure μ (fun n => f (ns n)) atTop g := by
  obtain ⟨ns, h_tendsto_ns⟩ : exists ns : Nat -> ι, Tendsto ns atTop u := exists_seq_tendsto u
  exact ⟨ns, h_tendsto_ns, fun ε hε => (hfg ε hε).comp h_tendsto_ns⟩

/--
theorem `TendstoInMeasure.exists_seq_tendsto_ae'` / 定理 `TendstoInMeasure.exists_seq_tendsto_ae'`

English:
theorem TendstoInMeasure.exists_seq_tendsto_ae'
  statement: {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
  proof: by
  obtain ⟨ms, hms1, hms2⟩ := hfg.exists_seq_tendstoInMeasure_atTop
  obtain ⟨ns, hns1, hns2⟩ := hms2.exists_seq_tendsto_ae
  exact ⟨ms ∘ ns, hms1.comp hns1.tendsto_atTop, hns2⟩

中文:
定理 TendstoInMeasure.存在_seq_tendsto_ae'
  结论: {u : 滤子 ι} [NeBot u] [是余untablyGenerated u]
  证明: by
  obtain ⟨ms, hms1, hms2⟩ := hfg.exists_seq_tendstoInMeasure_atTop
  obtain ⟨ns, hns1, hns2⟩ := hms2.exists_seq_tendsto_ae
  exact ⟨ms ∘ ns, hms1.comp hns1.tendsto_atTop, hns2⟩

Depends on / 依赖: exists_seq_tendstoInMeasure_atTop, exists_seq_tendsto_ae, hfg.exists_seq_tendstoInMeasure_atTop, hms1.comp, hms2.exists_seq_tendsto_ae, hns1.tendsto_atTop, tendsto_atTop
-/
theorem TendstoInMeasure.exists_seq_tendsto_ae' {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι -> α -> E} {g : α -> E} (hfg : TendstoInMeasure μ f u g) :
    exists ns : Nat -> ι, Tendsto ns atTop u ∧ forallᵐ x ∂μ, Tendsto (fun i => f (ns i) x) atTop (𝓝 (g x)) := by
  obtain ⟨ms, hms1, hms2⟩ := hfg.exists_seq_tendstoInMeasure_atTop
  obtain ⟨ns, hns1, hns2⟩ := hms2.exists_seq_tendsto_ae
  exact ⟨ms ∘ ns, hms1.comp hns1.tendsto_atTop, hns2⟩

/--
theorem `exists_seq_tendstoInMeasure_atTop_iff` / 定理 `exists_seq_tendstoInMeasure_atTop_iff`

English:
theorem exists_seq_tendstoInMeasure_atTop_iff
  statement: [IsFiniteMeasure μ]
  proof: by
  refine ⟨fun hfg _ hns => (hfg.comp hns.tendsto_atTop).exists_seq_tendsto_ae, fun h1 => ?_⟩
  rw [tendstoInMeasure_iff_tendsto_toNNReal]
  by_contra! ⟨ε, hε, h2⟩
  obtain ⟨δ, ns, hδ, hns, h3⟩ : exists (δ : Real>=0) (ns : Nat -> Nat), 0 < δ ∧ StrictMono ns ∧
      forall n, δ <= (μ {x | ε <= edist (f (ns n) x) (g x)}).toNNReal := by
    obtain ⟨s, hs, h4⟩ := not_tendsto_iff_exists_frequently_notMem.1 h2
    obtain ⟨δ, hδ, h5⟩ := NNReal.nhds_zero_basis.mem_iff.1 hs
    obtain ⟨ns, hns, h6⟩ := extraction_of_frequently_atTop h4
    exact ⟨δ, ns, hδ, hns, fun n => Set.notMem_Iio.1 (Set.notMem_subset h5 (h6 n))⟩
  obtain ⟨ns', _, h6⟩ := h1 ns hns
have h7 := tendstoInMeasure_iff_tendsto_toNNReal.mp
    tendstoInMeasure_of_tendsto_ae (fun n => hf _) h6
  exact lt_irrefl _ (lt_of_le_of_lt (ge_of_tendsto' (h7 ε hε) (fun n => h3 _)) hδ)

中文:
定理 存在_seq_tendstoInMeasure_atTop_iff
  结论: [是有限测度 μ]
  证明: by
  refine ⟨fun hfg _ hns => (hfg.comp hns.tendsto_atTop).exists_seq_tendsto_ae, fun h1 => ?_⟩
  rw [tendstoInMeasure_iff_tendsto_toNNReal]
  by_contra! ⟨ε, hε, h2⟩
  obtain ⟨δ, ns, hδ, hns, h3⟩ : exists (δ : Real>=0) (ns : Nat -> Nat), 0 < δ ∧ StrictMono ns ∧
      forall n, δ <= (μ {x | ε <= edist (f (ns n) x) (g x)}).toNNReal := by
    obtain ⟨s, hs, h4⟩ := not_tendsto_iff_exists_frequently_notMem.1 h2
    obtain ⟨δ, hδ, h5⟩ := NNReal.nhds_zero_basis.mem_iff.1 hs
    obtain ⟨ns, hns, h6⟩ := extraction_of_frequently_atTop h4
    exact ⟨δ, ns, hδ, hns, fun n => Set.notMem_Iio.1 (Set.notMem_subset h5 (h6 n))⟩
  obtain ⟨ns', _, h6⟩ := h1 ns hns
have h7 := tendstoInMeasure_iff_tendsto_toNNReal.mp
    tendstoInMeasure_of_tendsto_ae (fun n => hf _) h6
  exact lt_irrefl _ (lt_of_le_of_lt (ge_of_tendsto' (h7 ε hε) (fun n => h3 _)) hδ)

Depends on / 依赖: NNReal, NNReal.nhds_zero_basis.mem_iff, StrictMono, exists_seq_tendsto_ae, extraction_of_frequently_a, hfg.comp, hns.tendsto_atTop, mem_iff, nhds_zero_basis, not_tendsto_iff_exists_frequently_notMem, tendstoInMeasure_iff_tendsto_toNNReal, tendsto_atTop, toNNReal
-/
theorem exists_seq_tendstoInMeasure_atTop_iff [IsFiniteMeasure μ]
    {f : Nat -> α -> E} (hf : forall (n : Nat), AEStronglyMeasurable (f n) μ) {g : α -> E} :
    TendstoInMeasure μ f atTop g ↔
      forall ns : Nat -> Nat, StrictMono ns -> exists ns' : Nat -> Nat, StrictMono ns' ∧
        forallᵐ (ω : α) ∂μ, Tendsto (fun i => f (ns (ns' i)) ω) atTop (𝓝 (g ω)) := by
  refine ⟨fun hfg _ hns => (hfg.comp hns.tendsto_atTop).exists_seq_tendsto_ae, fun h1 => ?_⟩
  rw [tendstoInMeasure_iff_tendsto_toNNReal]
  by_contra! ⟨ε, hε, h2⟩
  obtain ⟨δ, ns, hδ, hns, h3⟩ : exists (δ : Real>=0) (ns : Nat -> Nat), 0 < δ ∧ StrictMono ns ∧
      forall n, δ <= (μ {x | ε <= edist (f (ns n) x) (g x)}).toNNReal := by
    obtain ⟨s, hs, h4⟩ := not_tendsto_iff_exists_frequently_notMem.1 h2
    obtain ⟨δ, hδ, h5⟩ := NNReal.nhds_zero_basis.mem_iff.1 hs
    obtain ⟨ns, hns, h6⟩ := extraction_of_frequently_atTop h4
    exact ⟨δ, ns, hδ, hns, fun n => Set.notMem_Iio.1 (Set.notMem_subset h5 (h6 n))⟩
  obtain ⟨ns', _, h6⟩ := h1 ns hns
have h7 := tendstoInMeasure_iff_tendsto_toNNReal.mp
    tendstoInMeasure_of_tendsto_ae (fun n => hf _) h6
  exact lt_irrefl _ (lt_of_le_of_lt (ge_of_tendsto' (h7 ε hε) (fun n => h3 _)) hδ)

end ExistsSeqTendstoAe

/--
lemma `eLpNorm_le_of_tendstoInMeasure` / 引理 `eLpNorm_le_of_tendstoInMeasure`

English:
lemma eLpNorm_le_of_tendstoInMeasure
  statement: {ι : Type*} [SeminormedAddGroup E]
  proof: by
  obtain ⟨l, hl⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact Lp.eLpNorm_le_of_ae_tendsto (hl.1.eventually bound) (fun n => hf (l n)) hl.2

中文:
引理 eLpNorm_le_of_tendstoInMeasure
  结论: {ι : 类型} [半赋范加群 E]
  证明: by
  obtain ⟨l, hl⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact Lp.eLpNorm_le_of_ae_tendsto (hl.1.eventually bound) (fun n => hf (l n)) hl.2

Depends on / 依赖: Lp.eLpNorm_le_of_ae_tendsto, eLpNorm_le_of_ae_tendsto, eventually, exists_seq_tendsto_ae, h_tendsto, h_tendsto.exists_seq_tendsto_ae
-/
lemma eLpNorm_le_of_tendstoInMeasure {ι : Type*} [SeminormedAddGroup E]
    {u : Filter ι} [NeBot u] [IsCountablyGenerated u] {f : ι -> α -> E} {g : α -> E} {C : Real>=0∞}
    {p : Real>=0∞} (bound : forallᶠ i in u, eLpNorm (f i) p μ <= C) (h_tendsto : TendstoInMeasure μ f u g)
    (hf : forall i, AEStronglyMeasurable (f i) μ) : eLpNorm g p μ <= C := by
  obtain ⟨l, hl⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact Lp.eLpNorm_le_of_ae_tendsto (hl.1.eventually bound) (fun n => hf (l n)) hl.2

section TendstoInMeasureUnique

/--
theorem `tendstoInMeasure_ae_unique` / 定理 `tendstoInMeasure_ae_unique`

English:
theorem tendstoInMeasure_ae_unique
  statement: [EMetricSpace E] {g h : α -> E} {f : ι -> α -> E} {u : Filter ι}
  proof: by
  obtain ⟨ns, h1, h1'⟩ := hg.exists_seq_tendsto_ae'
  obtain ⟨ns', h2, h2'⟩ := (hh.comp h1).exists_seq_tendsto_ae'
  filter_upwards [h1', h2'] with ω hg1 hh1
  exact tendsto_nhds_unique (hg1.comp h2) hh1

中文:
定理 tendstoInMeasure_ae_unique
  结论: [广义度量空间 E] {g h : α -> E} {f : ι -> α -> E} {u : 滤子 ι}
  证明: by
  obtain ⟨ns, h1, h1'⟩ := hg.exists_seq_tendsto_ae'
  obtain ⟨ns', h2, h2'⟩ := (hh.comp h1).exists_seq_tendsto_ae'
  filter_upwards [h1', h2'] with ω hg1 hh1
  exact tendsto_nhds_unique (hg1.comp h2) hh1

Depends on / 依赖: exists_seq_tendsto_ae, filter_upwards, hg.exists_seq_tendsto_ae, hg1.comp, hh.comp, tendsto_nhds_unique
-/
theorem tendstoInMeasure_ae_unique [EMetricSpace E] {g h : α -> E} {f : ι -> α -> E} {u : Filter ι}
    [NeBot u] [IsCountablyGenerated u] (hg : TendstoInMeasure μ f u g)
    (hh : TendstoInMeasure μ f u h) : g =ᵐ[μ] h := by
  obtain ⟨ns, h1, h1'⟩ := hg.exists_seq_tendsto_ae'
  obtain ⟨ns', h2, h2'⟩ := (hh.comp h1).exists_seq_tendsto_ae'
  filter_upwards [h1', h2'] with ω hg1 hh1
  exact tendsto_nhds_unique (hg1.comp h2) hh1

end TendstoInMeasureUnique

section AEMeasurableOf

variable [PseudoEMetricSpace E]

/--
theorem `TendstoInMeasure.aestronglyMeasurable` / 定理 `TendstoInMeasure.aestronglyMeasurable`

English:
theorem TendstoInMeasure.aestronglyMeasurable
  statement: {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
  proof: by
  obtain ⟨ns, -, hns⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => hf (ns n)) hns

中文:
定理 TendstoInMeasure.aestronglyMeasurable
  结论: {u : 滤子 ι} [NeBot u] [是余untablyGenerated u]
  证明: by
  obtain ⟨ns, -, hns⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => hf (ns n)) hns

Depends on / 依赖: aestronglyMeasurable_of_tendsto_ae, exists_seq_tendsto_ae, h_tendsto, h_tendsto.exists_seq_tendsto_ae
-/
theorem TendstoInMeasure.aestronglyMeasurable {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι -> α -> E} {g : α -> E} (hf : forall n, AEStronglyMeasurable (f n) μ)
    (h_tendsto : TendstoInMeasure μ f u g) : AEStronglyMeasurable g μ := by
  obtain ⟨ns, -, hns⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => hf (ns n)) hns

variable [MeasurableSpace E] [BorelSpace E]

/--
theorem `TendstoInMeasure.aemeasurable` / 定理 `TendstoInMeasure.aemeasurable`

English:
theorem TendstoInMeasure.aemeasurable
  statement: {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
  proof: by
  obtain ⟨ns, -, hns⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact aemeasurable_of_tendsto_metrizable_ae atTop (fun n => hf (ns n)) hns

中文:
定理 TendstoInMeasure.aemeasurable
  结论: {u : 滤子 ι} [NeBot u] [是余untablyGenerated u]
  证明: by
  obtain ⟨ns, -, hns⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact aemeasurable_of_tendsto_metrizable_ae atTop (fun n => hf (ns n)) hns

Depends on / 依赖: aemeasurable_of_tendsto_metrizable_ae, exists_seq_tendsto_ae, h_tendsto, h_tendsto.exists_seq_tendsto_ae
-/
theorem TendstoInMeasure.aemeasurable {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι -> α -> E} {g : α -> E} (hf : forall n, AEMeasurable (f n) μ)
    (h_tendsto : TendstoInMeasure μ f u g) : AEMeasurable g μ := by
  obtain ⟨ns, -, hns⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact aemeasurable_of_tendsto_metrizable_ae atTop (fun n => hf (ns n)) hns

end AEMeasurableOf

section TendstoInMeasureOf

variable {p : Real>=0∞}
variable {f : ι -> α -> E} {g : α -> E}

/--
theorem `tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable` / 定理 `tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable`

English:
theorem tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable
  statement: [SeminormedAddCommGroup E]
  proof: by
  refine tendstoInMeasure_of_ne_top fun ε hε hε_top => ?_
  replace hfg := ENNReal.Tendsto.const_mul (a := 1 / ε ^ p.toReal)
    (Tendsto.ennrpow_const p.toReal hfg) (Or.inr <| by simp [hε.ne'])
  simp only [mul_zero,
    ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp_ne_zero hp_ne_top)] at hfg
  rw [ENNReal.tendsto_nhds_zero] at hfg ⊢
  intro δ hδ
  refine (hfg δ hδ).mono fun n hn => ?_
  refine le_trans ?_ hn
  rw [one_div]; rw [← ENNReal.inv_mul_le_iff]; rw [inv_inv]
  · convert!
      mul_meas_ge_le_pow_eLpNorm' μ hp_ne_zero hp_ne_top ((hf n).sub hg).aestronglyMeasurable ε
      using 6
    simp [edist_eq_enorm_sub]
  · simp [hε_top]
  · simp [hε.ne']

中文:
定理 tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable
  结论: [SeminormedAddComm群 E]
  证明: by
  refine tendstoInMeasure_of_ne_top fun ε hε hε_top => ?_
  replace hfg := ENNReal.Tendsto.const_mul (a := 1 / ε ^ p.toReal)
    (Tendsto.ennrpow_const p.toReal hfg) (Or.inr <| by simp [hε.ne'])
  simp only [mul_zero,
    ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp_ne_zero hp_ne_top)] at hfg
  rw [ENNReal.tendsto_nhds_zero] at hfg ⊢
  intro δ hδ
  refine (hfg δ hδ).mono fun n hn => ?_
  refine le_trans ?_ hn
  rw [one_div]; rw [← ENNReal.inv_mul_le_iff]; rw [inv_inv]
  · convert!
      mul_meas_ge_le_pow_eLpNorm' μ hp_ne_zero hp_ne_top ((hf n).sub hg).aestronglyMeasurable ε
      using 6
    simp [edist_eq_enorm_sub]
  · simp [hε_top]
  · simp [hε.ne']

Depends on / 依赖: ENNReal, ENNReal.Tendsto.const_mul, ENNReal.inv_mul_le_iff, ENNReal.tendsto_nhds_zero, ENNReal.toReal_pos, ENNReal.zero_rpow_of_pos, Or.inr, Tendsto, Tendsto.ennrpow_const, const_mul, convert, ennrpow_const, hp_n, hp_ne_top, hp_ne_zero, inv_inv, inv_mul_le_iff, le_trans, mul_meas_ge_le_pow_eLpNorm, mul_zero
-/
theorem tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable [SeminormedAddCommGroup E]
    (hp_ne_zero : p != 0)
    (hp_ne_top : p != ∞) (hf : forall n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    {l : Filter ι} (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  refine tendstoInMeasure_of_ne_top fun ε hε hε_top => ?_
  replace hfg := ENNReal.Tendsto.const_mul (a := 1 / ε ^ p.toReal)
    (Tendsto.ennrpow_const p.toReal hfg) (Or.inr <| by simp [hε.ne'])
  simp only [mul_zero,
    ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp_ne_zero hp_ne_top)] at hfg
  rw [ENNReal.tendsto_nhds_zero] at hfg ⊢
  intro δ hδ
  refine (hfg δ hδ).mono fun n hn => ?_
  refine le_trans ?_ hn
  rw [one_div]; rw [← ENNReal.inv_mul_le_iff]; rw [inv_inv]
  · convert!
      mul_meas_ge_le_pow_eLpNorm' μ hp_ne_zero hp_ne_top ((hf n).sub hg).aestronglyMeasurable ε
      using 6
    simp [edist_eq_enorm_sub]
  · simp [hε_top]
  · simp [hε.ne']

/--
theorem `tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top` / 定理 `tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top`

English:
theorem tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top
  statement: [SeminormedAddCommGroup E]
  proof: by
  refine TendstoInMeasure.congr (fun i => (hf i).ae_eq_mk.symm) hg.ae_eq_mk.symm ?_
  refine tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable
    hp_ne_zero hp_ne_top (fun i => (hf i).stronglyMeasurable_mk) hg.stronglyMeasurable_mk ?_
  have : (fun n => eLpNorm ((hf n).mk (f n) - hg.mk g) p μ) = fun n => eLpNorm (f n - g) p μ := by
    ext1 n; refine eLpNorm_congr_ae (EventuallyEq.sub (hf n).ae_eq_mk.symm hg.ae_eq_mk.symm)
  rw [this]
  exact hfg

中文:
定理 tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top
  结论: [SeminormedAddComm群 E]
  证明: by
  refine TendstoInMeasure.congr (fun i => (hf i).ae_eq_mk.symm) hg.ae_eq_mk.symm ?_
  refine tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable
    hp_ne_zero hp_ne_top (fun i => (hf i).stronglyMeasurable_mk) hg.stronglyMeasurable_mk ?_
  have : (fun n => eLpNorm ((hf n).mk (f n) - hg.mk g) p μ) = fun n => eLpNorm (f n - g) p μ := by
    ext1 n; refine eLpNorm_congr_ae (EventuallyEq.sub (hf n).ae_eq_mk.symm hg.ae_eq_mk.symm)
  rw [this]
  exact hfg

Depends on / 依赖: EventuallyEq, EventuallyEq.sub, TendstoInMeasure, TendstoInMeasure.congr, ae_eq_mk, ae_eq_mk.symm, eLpNorm, eLpNorm_congr_ae, hg.ae_eq_mk.symm, hg.mk, hg.stronglyMeasurable_mk, hp_ne_top, hp_ne_zero, stronglyMeasurable_mk, tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable
-/
theorem tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top [SeminormedAddCommGroup E]
    (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
    (hf : forall n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ) {l : Filter ι}
    (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) l (𝓝 0)) : TendstoInMeasure μ f l g := by
  refine TendstoInMeasure.congr (fun i => (hf i).ae_eq_mk.symm) hg.ae_eq_mk.symm ?_
  refine tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable
    hp_ne_zero hp_ne_top (fun i => (hf i).stronglyMeasurable_mk) hg.stronglyMeasurable_mk ?_
  have : (fun n => eLpNorm ((hf n).mk (f n) - hg.mk g) p μ) = fun n => eLpNorm (f n - g) p μ := by
    ext1 n; refine eLpNorm_congr_ae (EventuallyEq.sub (hf n).ae_eq_mk.symm hg.ae_eq_mk.symm)
  rw [this]
  exact hfg

/--
theorem `tendstoInMeasure_of_tendsto_eLpNorm_top` / 定理 `tendstoInMeasure_of_tendsto_eLpNorm_top`

English:
theorem tendstoInMeasure_of_tendsto_eLpNorm_top
  statement: {E} [SeminormedAddCommGroup E] {f : ι -> α -> E}
  proof: by
  refine tendstoInMeasure_of_ne_top fun δ hδ hδ_top => ?_
  simp only [eLpNorm_exponent_top, eLpNormEssSup] at hfg
  rw [ENNReal.tendsto_nhds_zero] at hfg ⊢
  intro ε hε
  specialize hfg (δ / 2) (ENNReal.div_pos_iff.2 ⟨hδ.ne', ENNReal.ofNat_ne_top⟩)
  refine hfg.mono fun n hn => ?_
  simp only [Pi.sub_apply] at *
  have : essSup (fun x : α => ‖f n x - g x‖ₑ) μ < δ :=
    hn.trans_lt (ENNReal.half_lt_self hδ.ne' hδ_top)
  refine ((le_of_eq ?_).trans (ae_lt_of_essSup_lt this).le).trans hε.le
  congr with x
  simp [edist_eq_enorm_sub]

中文:
定理 tendstoInMeasure_of_tendsto_eLpNorm_top
  结论: {E} [SeminormedAddComm群 E] {f : ι -> α -> E}
  证明: by
  refine tendstoInMeasure_of_ne_top fun δ hδ hδ_top => ?_
  simp only [eLpNorm_exponent_top, eLpNormEssSup] at hfg
  rw [ENNReal.tendsto_nhds_zero] at hfg ⊢
  intro ε hε
  specialize hfg (δ / 2) (ENNReal.div_pos_iff.2 ⟨hδ.ne', ENNReal.ofNat_ne_top⟩)
  refine hfg.mono fun n hn => ?_
  simp only [Pi.sub_apply] at *
  have : essSup (fun x : α => ‖f n x - g x‖ₑ) μ < δ :=
    hn.trans_lt (ENNReal.half_lt_self hδ.ne' hδ_top)
  refine ((le_of_eq ?_).trans (ae_lt_of_essSup_lt this).le).trans hε.le
  congr with x
  simp [edist_eq_enorm_sub]

Depends on / 依赖: ENNReal, ENNReal.div_pos_iff, ENNReal.half_lt_self, ENNReal.ofNat_ne_top, ENNReal.tendsto_nhds_zero, Pi.sub_apply, ae_lt_of_essSup_lt, div_pos_iff, eLpNormEssSup, eLpNorm_exponent_top, essSup, half_lt_self, hfg.mono, hn.trans_lt, le_of_eq, ofNat_ne_top, specialize, sub_apply, tendstoInMeasure_of_ne_top, tendsto_nhds_zero
-/
theorem tendstoInMeasure_of_tendsto_eLpNorm_top {E} [SeminormedAddCommGroup E] {f : ι -> α -> E}
    {g : α -> E} {l : Filter ι} (hfg : Tendsto (fun n => eLpNorm (f n - g) ∞ μ) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  refine tendstoInMeasure_of_ne_top fun δ hδ hδ_top => ?_
  simp only [eLpNorm_exponent_top, eLpNormEssSup] at hfg
  rw [ENNReal.tendsto_nhds_zero] at hfg ⊢
  intro ε hε
  specialize hfg (δ / 2) (ENNReal.div_pos_iff.2 ⟨hδ.ne', ENNReal.ofNat_ne_top⟩)
  refine hfg.mono fun n hn => ?_
  simp only [Pi.sub_apply] at *
  have : essSup (fun x : α => ‖f n x - g x‖ₑ) μ < δ :=
    hn.trans_lt (ENNReal.half_lt_self hδ.ne' hδ_top)
  refine ((le_of_eq ?_).trans (ae_lt_of_essSup_lt this).le).trans hε.le
  congr with x
  simp [edist_eq_enorm_sub]

/--
theorem `tendstoInMeasure_of_tendsto_eLpNorm` / 定理 `tendstoInMeasure_of_tendsto_eLpNorm`

English:
theorem tendstoInMeasure_of_tendsto_eLpNorm
  statement: [NormedAddCommGroup E]
  proof: by
  by_cases hp_ne_top : p = ∞
  · subst hp_ne_top
    exact tendstoInMeasure_of_tendsto_eLpNorm_top hfg
  · exact tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top hp_ne_zero hp_ne_top hf hg hfg

中文:
定理 tendstoInMeasure_of_tendsto_eLpNorm
  结论: [赋范交换加群 E]
  证明: by
  by_cases hp_ne_top : p = ∞
  · subst hp_ne_top
    exact tendstoInMeasure_of_tendsto_eLpNorm_top hfg
  · exact tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top hp_ne_zero hp_ne_top hf hg hfg

Depends on / 依赖: hp_ne_top, hp_ne_zero, tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top, tendstoInMeasure_of_tendsto_eLpNorm_top
-/
theorem tendstoInMeasure_of_tendsto_eLpNorm [NormedAddCommGroup E]
    {l : Filter ι} (hp_ne_zero : p != 0)
    (hf : forall n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) l (𝓝 0)) : TendstoInMeasure μ f l g := by
  by_cases hp_ne_top : p = ∞
  · subst hp_ne_top
    exact tendstoInMeasure_of_tendsto_eLpNorm_top hfg
  · exact tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top hp_ne_zero hp_ne_top hf hg hfg

/--
theorem `tendstoInMeasure_of_tendsto_Lp` / 定理 `tendstoInMeasure_of_tendsto_Lp`

English:
theorem tendstoInMeasure_of_tendsto_Lp
  statement: [NormedAddCommGroup E] [hp : Fact (1 <= p)]
  proof: tendstoInMeasure_of_tendsto_eLpNorm (zero_lt_one.trans_le hp.elim).ne.symm
    (fun _ => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hfg)

中文:
定理 tendstoInMeasure_of_tendsto_Lp
  结论: [赋范交换加群 E] [hp : Fact (1 <= p)]
  证明: tendstoInMeasure_of_tendsto_eLpNorm (zero_lt_one.trans_le hp.elim).ne.symm
    (fun _ => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hfg)

Depends on / 依赖: Lp.aestronglyMeasurable, Lp.tendsto_Lp_iff_tendsto_eLpNorm, aestronglyMeasurable, hp.elim, ne.symm, tendstoInMeasure_of_tendsto_eLpNorm, tendsto_Lp_iff_tendsto_eLpNorm, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem tendstoInMeasure_of_tendsto_Lp [NormedAddCommGroup E] [hp : Fact (1 <= p)]
    {f : ι -> Lp E p μ} {g : Lp E p μ}
    {l : Filter ι} (hfg : Tendsto f l (𝓝 g)) : TendstoInMeasure μ (fun n => f n) l g :=
  tendstoInMeasure_of_tendsto_eLpNorm (zero_lt_one.trans_le hp.elim).ne.symm
    (fun _ => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hfg)

end TendstoInMeasureOf

end MeasureTheory
