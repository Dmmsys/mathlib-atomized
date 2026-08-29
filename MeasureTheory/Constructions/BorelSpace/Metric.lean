/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Borel sigma algebras on (pseudo-)metric spaces

## Main statements

* `measurable_dist`, `measurable_infEDist`, `measurable_norm`, `measurable_enorm`,
  `Measurable.dist`, `Measurable.infEDist`, `Measurable.norm`, `Measurable.enorm`:
  measurability of various metric-related notions;
* `tendsto_measure_thickening_of_isClosed`:
  the measure of a closed set is the limit of the measure of its ε-thickenings as ε → 0.
* `exists_borelSpace_of_countablyGenerated_of_separatesPoints`:
  if a measurable space is countably generated and separates points, it arises as the Borel sets
  of some second countable separable metrizable topology.

-/

public section

open Set Filter MeasureTheory MeasurableSpace TopologicalSpace

open scoped Topology NNReal ENNReal MeasureTheory

universe u v w x y

variable {α β γ δ : Type*} {ι : Sort y} {s t u : Set α}

section PseudoMetricSpace

variable [PseudoMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
variable [MeasurableSpace β] {x : α} {ε : Real}

open Metric

@[measurability]
/--
theorem `measurableSet_ball` / 定理 `measurableSet_ball`

English:
theorem measurableSet_ball
  statement: MeasurableSet (Metric.ball x ε)
  proof: Metric.isOpen_ball.measurableSet

@[measurability]

中文:
定理 measurableSet_ball
  结论: MeasurableSet (Metric.ball x ε)
  证明: Metric.isOpen_ball.measurableSet

@[measurability]

Depends on / 依赖: Metric, Metric.isOpen_ball.measurableSet, isOpen_ball, measurableSet
-/
theorem measurableSet_ball : MeasurableSet (Metric.ball x ε) :=
  Metric.isOpen_ball.measurableSet

@[measurability]
/--
theorem `measurableSet_closedBall` / 定理 `measurableSet_closedBall`

English:
theorem measurableSet_closedBall
  statement: MeasurableSet (Metric.closedBall x ε)
  proof: Metric.isClosed_closedBall.measurableSet

中文:
定理 measurableSet_closedBall
  结论: MeasurableSet (Metric.closedBall x ε)
  证明: Metric.isClosed_closedBall.measurableSet

Depends on / 依赖: Metric, Metric.isClosed_closedBall.measurableSet, isClosed_closedBall, measurableSet
-/
theorem measurableSet_closedBall : MeasurableSet (Metric.closedBall x ε) :=
  Metric.isClosed_closedBall.measurableSet

/--
theorem `measurable_infDist` / 定理 `measurable_infDist`

English:
theorem measurable_infDist
  given: {s : Set α}
  statement: Measurable fun x => infDist x s
  proof: (continuous_infDist_pt s).measurable

@[fun_prop]

中文:
定理 measurable_infDist
  条件: {s : Set α}
  结论: Measurable fun x => infDist x s
  证明: (continuous_infDist_pt s).measurable

@[fun_prop]

Depends on / 依赖: continuous_infDist_pt, measurable
-/
theorem measurable_infDist {s : Set α} : Measurable fun x => infDist x s :=
  (continuous_infDist_pt s).measurable

@[fun_prop]
/--
theorem `Measurable.infDist` / 定理 `Measurable.infDist`

English:
theorem Measurable.infDist
  given: {f : β -> α} (hf : Measurable f) {s : Set α}
  proof: measurable_infDist.comp hf

中文:
定理 Measurable.infDist
  条件: {f : β -> α} (hf : Measurable f) {s : Set α}
  证明: measurable_infDist.comp hf

Depends on / 依赖: measurable_infDist, measurable_infDist.comp
-/
theorem Measurable.infDist {f : β -> α} (hf : Measurable f) {s : Set α} :
    Measurable fun x => infDist (f x) s :=
  measurable_infDist.comp hf

/--
theorem `measurable_infNndist` / 定理 `measurable_infNndist`

English:
theorem measurable_infNndist
  given: {s : Set α}
  statement: Measurable fun x => infNndist x s
  proof: (continuous_infNndist_pt s).measurable

@[fun_prop]

中文:
定理 measurable_infNndist
  条件: {s : Set α}
  结论: Measurable fun x => infNndist x s
  证明: (continuous_infNndist_pt s).measurable

@[fun_prop]

Depends on / 依赖: continuous_infNndist_pt, measurable
-/
theorem measurable_infNndist {s : Set α} : Measurable fun x => infNndist x s :=
  (continuous_infNndist_pt s).measurable

@[fun_prop]
/--
theorem `Measurable.infNndist` / 定理 `Measurable.infNndist`

English:
theorem Measurable.infNndist
  given: {f : β -> α} (hf : Measurable f) {s : Set α}
  proof: measurable_infNndist.comp hf

中文:
定理 Measurable.infNndist
  条件: {f : β -> α} (hf : Measurable f) {s : Set α}
  证明: measurable_infNndist.comp hf

Depends on / 依赖: measurable_infNndist, measurable_infNndist.comp
-/
theorem Measurable.infNndist {f : β -> α} (hf : Measurable f) {s : Set α} :
    Measurable fun x => infNndist (f x) s :=
  measurable_infNndist.comp hf

section

variable [SecondCountableTopology α]

/--
theorem `measurable_dist` / 定理 `measurable_dist`

English:
theorem measurable_dist
  statement: Measurable fun p : α × α => dist p.1 p.2
  proof: continuous_dist.measurable

@[fun_prop]

中文:
定理 measurable_dist
  结论: Measurable fun p : α × α => dist p.1 p.2
  证明: continuous_dist.measurable

@[fun_prop]

Depends on / 依赖: continuous_dist, continuous_dist.measurable, measurable
-/
theorem measurable_dist : Measurable fun p : α × α => dist p.1 p.2 :=
  continuous_dist.measurable

@[fun_prop]
/--
theorem `Measurable.dist` / 定理 `Measurable.dist`

English:
theorem Measurable.dist
  given: {f g : β -> α} (hf : Measurable f) (hg : Measurable g)
  proof: continuous_dist.measurable2 hf hg

@[fun_prop]

中文:
定理 Measurable.dist
  条件: {f g : β -> α} (hf : Measurable f) (hg : Measurable g)
  证明: continuous_dist.measurable2 hf hg

@[fun_prop]

Depends on / 依赖: continuous_dist, continuous_dist.measurable2, measurable2
-/
theorem Measurable.dist {f g : β -> α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun b => dist (f b) (g b) :=
  continuous_dist.measurable2 hf hg

@[fun_prop]
/--
lemma `AEMeasurable.dist` / 引理 `AEMeasurable.dist`

English:
lemma AEMeasurable.dist
  statement: {f g : β -> α} {μ : Measure β}
  proof: continuous_dist.aemeasurable2 hf hg

中文:
引理 AEMeasurable.dist
  结论: {f g : β -> α} {μ : Measure β}
  证明: continuous_dist.aemeasurable2 hf hg

Depends on / 依赖: aemeasurable2, continuous_dist, continuous_dist.aemeasurable2
-/
lemma AEMeasurable.dist {f g : β -> α} {μ : Measure β}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun b => dist (f b) (g b)) μ :=
  continuous_dist.aemeasurable2 hf hg

/--
theorem `measurable_nndist` / 定理 `measurable_nndist`

English:
theorem measurable_nndist
  statement: Measurable fun p : α × α => nndist p.1 p.2
  proof: continuous_nndist.measurable

@[fun_prop]

中文:
定理 measurable_nndist
  结论: Measurable fun p : α × α => nndist p.1 p.2
  证明: continuous_nndist.measurable

@[fun_prop]

Depends on / 依赖: continuous_nndist, continuous_nndist.measurable, measurable
-/
theorem measurable_nndist : Measurable fun p : α × α => nndist p.1 p.2 :=
  continuous_nndist.measurable

@[fun_prop]
/--
theorem `Measurable.nndist` / 定理 `Measurable.nndist`

English:
theorem Measurable.nndist
  given: {f g : β -> α} (hf : Measurable f) (hg : Measurable g)
  proof: continuous_nndist.measurable2 hf hg

中文:
定理 Measurable.nndist
  条件: {f g : β -> α} (hf : Measurable f) (hg : Measurable g)
  证明: continuous_nndist.measurable2 hf hg

Depends on / 依赖: continuous_nndist, continuous_nndist.measurable2, measurable2
-/
theorem Measurable.nndist {f g : β -> α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun b => nndist (f b) (g b) :=
  continuous_nndist.measurable2 hf hg

end

end PseudoMetricSpace

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
variable [MeasurableSpace β] {x : α} {ε : Real>=0∞}

open Metric

@[measurability]
/--
theorem `measurableSet_eball` / 定理 `measurableSet_eball`

English:
theorem measurableSet_eball
  statement: MeasurableSet (Metric.eball x ε)
  proof: Metric.isOpen_eball.measurableSet

@[fun_prop]

中文:
定理 measurableSet_eball
  结论: MeasurableSet (Metric.eball x ε)
  证明: Metric.isOpen_eball.measurableSet

@[fun_prop]

Depends on / 依赖: Metric, Metric.isOpen_eball.measurableSet, isOpen_eball, measurableSet
-/
theorem measurableSet_eball : MeasurableSet (Metric.eball x ε) :=
  Metric.isOpen_eball.measurableSet

@[fun_prop]
/--
theorem `measurable_edist_right` / 定理 `measurable_edist_right`

English:
theorem measurable_edist_right
  statement: Measurable (edist x)
  proof: by fun_prop

@[fun_prop]

中文:
定理 measurable_edist_right
  结论: Measurable (edist x)
  证明: by fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop
-/
theorem measurable_edist_right : Measurable (edist x) := by fun_prop

@[fun_prop]
/--
theorem `measurable_edist_left` / 定理 `measurable_edist_left`

English:
theorem measurable_edist_left
  statement: Measurable fun y => edist y x
  proof: by fun_prop

中文:
定理 measurable_edist_left
  结论: Measurable fun y => edist y x
  证明: by fun_prop

Depends on / 依赖: fun_prop
-/
theorem measurable_edist_left : Measurable fun y => edist y x := by fun_prop

/--
theorem `measurable_infEDist` / 定理 `measurable_infEDist`

English:
theorem measurable_infEDist
  given: {s : Set α}
  statement: Measurable fun x => infEDist x s
  proof: continuous_infEDist.measurable

@[deprecated (since := "2026-01-08")]
alias measurable_infEdist := measurable_infEDist

@[fun_prop]

中文:
定理 measurable_infEDist
  条件: {s : Set α}
  结论: Measurable fun x => infEDist x s
  证明: continuous_infEDist.measurable

@[deprecated (since := "2026-01-08")]
alias measurable_infEdist := measurable_infEDist

@[fun_prop]

Depends on / 依赖: continuous_infEDist, continuous_infEDist.measurable, measurable
-/
theorem measurable_infEDist {s : Set α} : Measurable fun x => infEDist x s :=
  continuous_infEDist.measurable

@[deprecated (since := "2026-01-08")]
alias measurable_infEdist := measurable_infEDist

@[fun_prop]
/--
theorem `Measurable.infEDist` / 定理 `Measurable.infEDist`

English:
theorem Measurable.infEDist
  given: {f : β -> α} (hf : Measurable f) {s : Set α}
  proof: measurable_infEDist.comp hf

@[deprecated (since := "2026-01-08")]
alias Measurable.infEdist := Measurable.infEDist

中文:
定理 Measurable.infEDist
  条件: {f : β -> α} (hf : Measurable f) {s : Set α}
  证明: measurable_infEDist.comp hf

@[deprecated (since := "2026-01-08")]
alias Measurable.infEdist := Measurable.infEDist
-/
protected theorem Measurable.infEDist {f : β -> α} (hf : Measurable f) {s : Set α} :
    Measurable fun x => infEDist (f x) s :=
  measurable_infEDist.comp hf

@[deprecated (since := "2026-01-08")]
alias Measurable.infEdist := Measurable.infEDist

/--
theorem `tendsto_measure_cthickening` / 定理 `tendsto_measure_cthickening`

English:
theorem tendsto_measure_cthickening
  statement: {μ : Measure α} {s : Set α}
  proof: by
  have A : Tendsto (fun r => μ (cthickening r s)) (𝓝[Ioi 0] 0) (𝓝 (μ (closure s))) := by
    rw [closure_eq_iInter_cthickening]
    exact
      tendsto_measure_biInter_gt (fun r _ => isClosed_cthickening.nullMeasurableSet)
        (fun i j _ ij => cthickening_mono ij _) hs
  have B : Tendsto (fun

中文:
定理 tendsto_measure_cthickening
  结论: {μ : Measure α} {s : Set α}
  证明: by
  have A : Tendsto (fun r => μ (cthickening r s)) (𝓝[Ioi 0] 0) (𝓝 (μ (closure s))) := by
    rw [closure_eq_iInter_cthickening]
    exact
      tendsto_measure_biInter_gt (fun r _ => isClosed_cthickening.nullMeasurableSet)
        (fun i j _ ij => cthickening_mono ij _) hs
  have B : Tendsto (fun

Depends on / 依赖: B.sup, Tendsto, Tendsto.congr, closure, closure_eq_iInter_cthickening, convert, cthickening, cthickening_mono, cthickening_of_nonpos, filter_upwards, isClosed_cthickening, isClosed_cthickening.nullMeasurableSet, nullMeasurableSet, self_mem_nhdsWithin, tendsto_const_nhds, tendsto_measure_biInter_gt
-/
theorem tendsto_measure_cthickening {μ : Measure α} {s : Set α}
    (hs : exists R > 0, μ (cthickening R s) != ∞) :
    Tendsto (fun r => μ (cthickening r s)) (𝓝 0) (𝓝 (μ (closure s))) := by
  have A : Tendsto (fun r => μ (cthickening r s)) (𝓝[Ioi 0] 0) (𝓝 (μ (closure s))) := by
    rw [closure_eq_iInter_cthickening]
    exact
      tendsto_measure_biInter_gt (fun r _ => isClosed_cthickening.nullMeasurableSet)
        (fun i j _ ij => cthickening_mono ij _) hs
  have B : Tendsto (fun r => μ (cthickening r s)) (𝓝[Iic 0] 0) (𝓝 (μ (closure s))) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin (α := Real)] with _ hr
    rw [cthickening_of_nonpos hr]
  convert! B.sup A
  exact (nhdsLE_sup_nhdsGT 0).symm

/--
theorem `tendsto_measure_cthickening_of_isClosed` / 定理 `tendsto_measure_cthickening_of_isClosed`

English:
theorem tendsto_measure_cthickening_of_isClosed
  statement: {μ : Measure α} {s : Set α}
  proof: by
  convert! tendsto_measure_cthickening hs
  exact h's.closure_eq.symm

中文:
定理 tendsto_measure_cthickening_of_isClosed
  结论: {μ : Measure α} {s : Set α}
  证明: by
  convert! tendsto_measure_cthickening hs
  exact h's.closure_eq.symm

Depends on / 依赖: closure_eq, convert, s.closure_eq.symm, tendsto_measure_cthickening
-/
theorem tendsto_measure_cthickening_of_isClosed {μ : Measure α} {s : Set α}
    (hs : exists R > 0, μ (cthickening R s) != ∞) (h's : IsClosed s) :
    Tendsto (fun r => μ (cthickening r s)) (𝓝 0) (𝓝 (μ s)) := by
  convert! tendsto_measure_cthickening hs
  exact h's.closure_eq.symm

/--
theorem `tendsto_measure_thickening` / 定理 `tendsto_measure_thickening`

English:
theorem tendsto_measure_thickening
  statement: {μ : Measure α} {s : Set α}
  proof: by
  rw [closure_eq_iInter_thickening]
  exact tendsto_measure_biInter_gt (fun r _ => isOpen_thickening.nullMeasurableSet)
      (fun i j _ ij => thickening_mono ij _) hs

中文:
定理 tendsto_measure_thickening
  结论: {μ : Measure α} {s : Set α}
  证明: by
  rw [closure_eq_iInter_thickening]
  exact tendsto_measure_biInter_gt (fun r _ => isOpen_thickening.nullMeasurableSet)
      (fun i j _ ij => thickening_mono ij _) hs

Depends on / 依赖: closure_eq_iInter_thickening, isOpen_thickening, isOpen_thickening.nullMeasurableSet, nullMeasurableSet, tendsto_measure_biInter_gt, thickening_mono
-/
theorem tendsto_measure_thickening {μ : Measure α} {s : Set α}
    (hs : exists R > 0, μ (thickening R s) != ∞) :
    Tendsto (fun r => μ (thickening r s)) (𝓝[>] 0) (𝓝 (μ (closure s))) := by
  rw [closure_eq_iInter_thickening]
  exact tendsto_measure_biInter_gt (fun r _ => isOpen_thickening.nullMeasurableSet)
      (fun i j _ ij => thickening_mono ij _) hs

/--
theorem `tendsto_measure_thickening_of_isClosed` / 定理 `tendsto_measure_thickening_of_isClosed`

English:
theorem tendsto_measure_thickening_of_isClosed
  statement: {μ : Measure α} {s : Set α}
  proof: by
  convert! tendsto_measure_thickening hs
  exact h's.closure_eq.symm

中文:
定理 tendsto_measure_thickening_of_isClosed
  结论: {μ : Measure α} {s : Set α}
  证明: by
  convert! tendsto_measure_thickening hs
  exact h's.closure_eq.symm

Depends on / 依赖: closure_eq, convert, s.closure_eq.symm, tendsto_measure_thickening
-/
theorem tendsto_measure_thickening_of_isClosed {μ : Measure α} {s : Set α}
    (hs : exists R > 0, μ (thickening R s) != ∞) (h's : IsClosed s) :
    Tendsto (fun r => μ (thickening r s)) (𝓝[>] 0) (𝓝 (μ s)) := by
  convert! tendsto_measure_thickening hs
  exact h's.closure_eq.symm

variable [SecondCountableTopology α]

/--
theorem `measurable_edist` / 定理 `measurable_edist`

English:
theorem measurable_edist
  statement: Measurable fun p : α × α => edist p.1 p.2
  proof: continuous_edist.measurable

@[fun_prop]

中文:
定理 measurable_edist
  结论: Measurable fun p : α × α => edist p.1 p.2
  证明: continuous_edist.measurable

@[fun_prop]

Depends on / 依赖: continuous_edist, continuous_edist.measurable, measurable
-/
theorem measurable_edist : Measurable fun p : α × α => edist p.1 p.2 :=
  continuous_edist.measurable

@[fun_prop]
/--
theorem `Measurable.edist` / 定理 `Measurable.edist`

English:
theorem Measurable.edist
  given: {f g : β -> α} (hf : Measurable f) (hg : Measurable g)
  proof: continuous_edist.measurable2 hf hg

@[fun_prop]

中文:
定理 Measurable.edist
  条件: {f g : β -> α} (hf : Measurable f) (hg : Measurable g)
  证明: continuous_edist.measurable2 hf hg

@[fun_prop]

Depends on / 依赖: continuous_edist, continuous_edist.measurable2, measurable2
-/
theorem Measurable.edist {f g : β -> α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun b => edist (f b) (g b) :=
  continuous_edist.measurable2 hf hg

@[fun_prop]
/--
theorem `AEMeasurable.edist` / 定理 `AEMeasurable.edist`

English:
theorem AEMeasurable.edist
  statement: {f g : β -> α} {μ : Measure β} (hf : AEMeasurable f μ)
  proof: continuous_edist.aemeasurable2 hf hg

中文:
定理 AEMeasurable.edist
  结论: {f g : β -> α} {μ : Measure β} (hf : AEMeasurable f μ)
  证明: continuous_edist.aemeasurable2 hf hg

Depends on / 依赖: aemeasurable2, continuous_edist, continuous_edist.aemeasurable2
-/
theorem AEMeasurable.edist {f g : β -> α} {μ : Measure β} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (fun a => edist (f a) (g a)) μ :=
  continuous_edist.aemeasurable2 hf hg

end PseudoEMetricSpace

/--
theorem `tendsto_measure_cthickening_of_isCompact` / 定理 `tendsto_measure_cthickening_of_isCompact`

English:
theorem tendsto_measure_cthickening_of_isCompact
  statement: [MetricSpace α] [MeasurableSpace α]
  proof: tendsto_measure_cthickening_of_isClosed
    ⟨1, zero_lt_one, hs.isBounded.cthickening.measure_lt_top.ne⟩ hs.isClosed

中文:
定理 tendsto_measure_cthickening_of_isCompact
  结论: [MetricSpace α] [MeasurableSpace α]
  证明: tendsto_measure_cthickening_of_isClosed
    ⟨1, zero_lt_one, hs.isBounded.cthickening.measure_lt_top.ne⟩ hs.isClosed

Depends on / 依赖: cthickening, hs.isBounded.cthickening.measure_lt_top.ne, hs.isClosed, isBounded, isClosed, measure_lt_top, tendsto_measure_cthickening_of_isClosed, zero_lt_one
-/
theorem tendsto_measure_cthickening_of_isCompact [MetricSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [ProperSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {s : Set α} (hs : IsCompact s) :
    Tendsto (fun r => μ (Metric.cthickening r s)) (𝓝 0) (𝓝 (μ s)) :=
  tendsto_measure_cthickening_of_isClosed
    ⟨1, zero_lt_one, hs.isBounded.cthickening.measure_lt_top.ne⟩ hs.isClosed

/--
theorem `exists_borelSpace_of_countablyGenerated_of_separatesPoints` / 定理 `exists_borelSpace_of_countablyGenerated_of_separatesPoints`

English:
theorem exists_borelSpace_of_countablyGenerated_of_separatesPoints
  statement: (α : Type*)
  proof: by
  rcases measurableEquiv_nat_bool_of_countablyGenerated α with ⟨s, ⟨f⟩⟩
  let := induced f inferInstance
let F := f.toEquiv.toHomeomorphOfIsInducing .induced _
  exact ⟨inferInstance, F.secondCountableTopology, F.symm.t4Space,
    f.measurableEmbedding.borelSpace F.isInducing⟩

中文:
定理 exists_borelSpace_of_countablyGenerated_of_separatesPoints
  结论: (α : 类型)
  证明: by
  rcases measurableEquiv_nat_bool_of_countablyGenerated α with ⟨s, ⟨f⟩⟩
  let := induced f inferInstance
let F := f.toEquiv.toHomeomorphOfIsInducing .induced _
  exact ⟨inferInstance, F.secondCountableTopology, F.symm.t4Space,
    f.measurableEmbedding.borelSpace F.isInducing⟩

Depends on / 依赖: F.isInducing, F.secondCountableTopology, F.symm.t4Space, borelSpace, f.measurableEmbedding.borelSpace, f.toEquiv.toHomeomorphOfIsInducing, induced, isInducing, measurableEmbedding, measurableEquiv_nat_bool_of_countablyGenerated, secondCountableTopology, t4Space, toEquiv, toHomeomorphOfIsInducing
-/
theorem exists_borelSpace_of_countablyGenerated_of_separatesPoints (α : Type*)
    [m : MeasurableSpace α] [CountablyGenerated α] [SeparatesPoints α] :
    exists _ : TopologicalSpace α, SecondCountableTopology α ∧ T4Space α ∧ BorelSpace α := by
  rcases measurableEquiv_nat_bool_of_countablyGenerated α with ⟨s, ⟨f⟩⟩
  let := induced f inferInstance
let F := f.toEquiv.toHomeomorphOfIsInducing .induced _
  exact ⟨inferInstance, F.secondCountableTopology, F.symm.t4Space,
    f.measurableEmbedding.borelSpace F.isInducing⟩

/--
theorem `exists_opensMeasurableSpace_of_countablySeparated` / 定理 `exists_opensMeasurableSpace_of_countablySeparated`

English:
theorem exists_opensMeasurableSpace_of_countablySeparated
  statement: (α : Type*)
  proof: by
  rcases exists_countablyGenerated_le_of_countablySeparated α with ⟨m', _, _, m'le⟩
  rcases exists_borelSpace_of_countablyGenerated_of_separatesPoints (m := m') with ⟨τ, _, _, τm'⟩
  exact ⟨τ, ‹_›, ‹_›, @OpensMeasurableSpace.mk _ _ m (τm'.measurable_eq.symm.le.trans m'le)⟩

中文:
定理 exists_opensMeasurableSpace_of_countablySeparated
  结论: (α : 类型)
  证明: by
  rcases exists_countablyGenerated_le_of_countablySeparated α with ⟨m', _, _, m'le⟩
  rcases exists_borelSpace_of_countablyGenerated_of_separatesPoints (m := m') with ⟨τ, _, _, τm'⟩
  exact ⟨τ, ‹_›, ‹_›, @OpensMeasurableSpace.mk _ _ m (τm'.measurable_eq.symm.le.trans m'le)⟩

Depends on / 依赖: OpensMeasurableSpace, OpensMeasurableSpace.mk, exists_borelSpace_of_countablyGenerated_of_separatesPoints, exists_countablyGenerated_le_of_countablySeparated, measurable_eq, measurable_eq.symm.le.trans
-/
theorem exists_opensMeasurableSpace_of_countablySeparated (α : Type*)
    [m : MeasurableSpace α] [CountablySeparated α] :
    exists _ : TopologicalSpace α, SecondCountableTopology α ∧ T4Space α ∧ OpensMeasurableSpace α := by
  rcases exists_countablyGenerated_le_of_countablySeparated α with ⟨m', _, _, m'le⟩
  rcases exists_borelSpace_of_countablyGenerated_of_separatesPoints (m := m') with ⟨τ, _, _, τm'⟩
  exact ⟨τ, ‹_›, ‹_›, @OpensMeasurableSpace.mk _ _ m (τm'.measurable_eq.symm.le.trans m'le)⟩


section ContinuousENorm

variable {ε : Type*} [MeasurableSpace ε] [TopologicalSpace ε] [ContinuousENorm ε]
  [OpensMeasurableSpace ε] [MeasurableSpace β]

@[fun_prop]
/--
lemma `measurable_enorm` / 引理 `measurable_enorm`

English:
lemma measurable_enorm
  statement: Measurable (enorm : ε -> Real>=0∞)
  proof: continuous_enorm.measurable

@[fun_prop]

中文:
引理 measurable_enorm
  结论: Measurable (enorm : ε -> 实数>=0∞)
  证明: continuous_enorm.measurable

@[fun_prop]

Depends on / 依赖: continuous_enorm, continuous_enorm.measurable, measurable
-/
lemma measurable_enorm : Measurable (enorm : ε -> Real>=0∞) := continuous_enorm.measurable

@[fun_prop]
/--
lemma `Measurable.enorm` / 引理 `Measurable.enorm`

English:
lemma Measurable.enorm
  given: {f : β -> ε} (hf : Measurable f)
  statement: Measurable (‖f ·‖ₑ)
  proof: measurable_enorm.comp hf

@[fun_prop]

中文:
引理 Measurable.enorm
  条件: {f : β -> ε} (hf : Measurable f)
  结论: Measurable (‖f ·‖ₑ)
  证明: measurable_enorm.comp hf

@[fun_prop]
-/
protected lemma Measurable.enorm {f : β -> ε} (hf : Measurable f) : Measurable (‖f ·‖ₑ) :=
  measurable_enorm.comp hf

@[fun_prop]
/--
lemma `AEMeasurable.enorm` / 引理 `AEMeasurable.enorm`

English:
lemma AEMeasurable.enorm
  given: {f : β -> ε} {μ : Measure β} (hf : AEMeasurable f μ)
  proof: measurable_enorm.comp_aemeasurable hf

中文:
引理 AEMeasurable.enorm
  条件: {f : β -> ε} {μ : Measure β} (hf : AEMeasurable f μ)
  证明: measurable_enorm.comp_aemeasurable hf
-/
protected lemma AEMeasurable.enorm {f : β -> ε} {μ : Measure β} (hf : AEMeasurable f μ) :
    AEMeasurable (‖f ·‖ₑ) μ :=
  measurable_enorm.comp_aemeasurable hf

end ContinuousENorm

section NormedAddCommGroup

variable [MeasurableSpace α] [NormedAddCommGroup α] [OpensMeasurableSpace α] [MeasurableSpace β]

@[fun_prop]
/--
theorem `measurable_norm` / 定理 `measurable_norm`

English:
theorem measurable_norm
  statement: Measurable (norm : α -> Real)
  proof: continuous_norm.measurable

@[fun_prop]

中文:
定理 measurable_norm
  结论: Measurable (norm : α -> 实数)
  证明: continuous_norm.measurable

@[fun_prop]

Depends on / 依赖: continuous_norm, continuous_norm.measurable, measurable
-/
theorem measurable_norm : Measurable (norm : α -> Real) :=
  continuous_norm.measurable

@[fun_prop]
/--
theorem `Measurable.norm` / 定理 `Measurable.norm`

English:
theorem Measurable.norm
  given: {f : β -> α} (hf : Measurable f)
  statement: Measurable fun a => norm (f a)
  proof: measurable_norm.comp hf

@[fun_prop]

中文:
定理 Measurable.norm
  条件: {f : β -> α} (hf : Measurable f)
  结论: Measurable fun a => norm (f a)
  证明: measurable_norm.comp hf

@[fun_prop]

Depends on / 依赖: measurable_norm, measurable_norm.comp
-/
theorem Measurable.norm {f : β -> α} (hf : Measurable f) : Measurable fun a => norm (f a) :=
  measurable_norm.comp hf

@[fun_prop]
/--
theorem `AEMeasurable.norm` / 定理 `AEMeasurable.norm`

English:
theorem AEMeasurable.norm
  given: {f : β -> α} {μ : Measure β} (hf : AEMeasurable f μ)
  proof: measurable_norm.comp_aemeasurable hf

中文:
定理 AEMeasurable.norm
  条件: {f : β -> α} {μ : Measure β} (hf : AEMeasurable f μ)
  证明: measurable_norm.comp_aemeasurable hf

Depends on / 依赖: comp_aemeasurable, measurable_norm, measurable_norm.comp_aemeasurable
-/
theorem AEMeasurable.norm {f : β -> α} {μ : Measure β} (hf : AEMeasurable f μ) :
    AEMeasurable (fun a => norm (f a)) μ :=
  measurable_norm.comp_aemeasurable hf

/--
theorem `measurable_nnnorm` / 定理 `measurable_nnnorm`

English:
theorem measurable_nnnorm
  statement: Measurable (nnnorm : α -> Real>=0)
  proof: continuous_nnnorm.measurable

@[fun_prop]

中文:
定理 measurable_nnnorm
  结论: Measurable (nnnorm : α -> 实数>=0)
  证明: continuous_nnnorm.measurable

@[fun_prop]

Depends on / 依赖: continuous_nnnorm, continuous_nnnorm.measurable, measurable
-/
theorem measurable_nnnorm : Measurable (nnnorm : α -> Real>=0) :=
  continuous_nnnorm.measurable

@[fun_prop]
/--
theorem `Measurable.nnnorm` / 定理 `Measurable.nnnorm`

English:
theorem Measurable.nnnorm
  given: {f : β -> α} (hf : Measurable f)
  statement: Measurable fun a => ‖f a‖₊
  proof: measurable_nnnorm.comp hf

@[fun_prop]

中文:
定理 Measurable.nnnorm
  条件: {f : β -> α} (hf : Measurable f)
  结论: Measurable fun a => ‖f a‖₊
  证明: measurable_nnnorm.comp hf

@[fun_prop]
-/
protected theorem Measurable.nnnorm {f : β -> α} (hf : Measurable f) : Measurable fun a => ‖f a‖₊ :=
  measurable_nnnorm.comp hf

@[fun_prop]
/--
lemma `AEMeasurable.nnnorm` / 引理 `AEMeasurable.nnnorm`

English:
lemma AEMeasurable.nnnorm
  given: {f : β -> α} {μ : Measure β} (hf : AEMeasurable f μ)
  proof: measurable_nnnorm.comp_aemeasurable hf

中文:
引理 AEMeasurable.nnnorm
  条件: {f : β -> α} {μ : Measure β} (hf : AEMeasurable f μ)
  证明: measurable_nnnorm.comp_aemeasurable hf
-/
protected lemma AEMeasurable.nnnorm {f : β -> α} {μ : Measure β} (hf : AEMeasurable f μ) :
    AEMeasurable (fun a => ‖f a‖₊) μ :=
  measurable_nnnorm.comp_aemeasurable hf

end NormedAddCommGroup
