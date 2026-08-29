/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Bhavik Mehta
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Links between an integral and its "improper" version

In its current state, mathlib only knows how to talk about definite ("proper") integrals,
in the sense that it treats integrals over `[x, +∞)` the same as it treats integrals over
`[y, z]`. For example, the integral over `[1, +∞)` is **not** defined to be the limit of
the integral over `[1, x]` as `x` tends to `+∞`, which is known as an **improper integral**.

Indeed, the "proper" definition is stronger than the "improper" one. The usual counterexample
is `x ↦ sin(x)/x`, which has an improper integral over `[1, +∞)` but no definite integral.

Although definite integrals have better properties, they are hardly usable when it comes to
computing integrals on unbounded sets, which is much easier using limits. Thus, in this file,
we prove various ways of studying the proper integral by studying the improper one.

## Definitions

The main definition of this file is `MeasureTheory.AECover`. It is a rather technical definition
whose sole purpose is generalizing and factoring proofs. Given an index type `ι`, a countably
generated filter `l` over `ι`, and an `ι`-indexed family `φ` of subsets of a measurable space `α`
equipped with a measure `μ`, one should think of a hypothesis `hφ : MeasureTheory.AECover μ l φ` as
a sufficient condition for being able to interpret `∫ x, f x ∂μ` (if it exists) as the limit of `∫ x
in φ i, f x ∂μ` as `i` tends to `l`.

When using this definition with a measure restricted to a set `s`, which happens fairly often, one
should not try too hard to use a `MeasureTheory.AECover` of subsets of `s`, as it often makes proofs
more complicated than necessary. See for example the proof of
`MeasureTheory.integrableOn_Iic_of_intervalIntegral_norm_tendsto` where we use `(fun x ↦ oi x)` as a
`MeasureTheory.AECover` w.r.t. `μ.restrict (Iic b)`, instead of using `(fun x ↦ Ioc x b)`.

## Main statements

- `MeasureTheory.AECover.lintegral_tendsto_of_countably_generated` : if `φ` is a
  `MeasureTheory.AECover μ l`, where `l` is a countably generated filter, and if `f` is a measurable
  `ENNReal`-valued function, then `∫⁻ x in φ n, f x ∂μ` tends to `∫⁻ x, f x ∂μ` as `n` tends to `l`

- `MeasureTheory.AECover.integrable_of_integral_norm_tendsto` : if `φ` is a
  `MeasureTheory.AECover μ l`, where `l` is a countably generated filter, if `f` is measurable and
  integrable on each `φ n`, and if `∫ x in φ n, ‖f x‖ ∂μ` tends to some `I : ℝ` as n tends to `l`,
  then `f` is integrable

- `MeasureTheory.AECover.integral_tendsto_of_countably_generated` : if `φ` is a
  `MeasureTheory.AECover μ l`, where `l` is a countably generated filter, and if `f` is measurable
  and integrable (globally), then `∫ x in φ n, f x ∂μ` tends to `∫ x, f x ∂μ` as `n` tends to `+∞`.

We then specialize these lemmas to various use cases involving intervals, which are frequent
in analysis. In particular,

- `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto` is a version of FTC-2 on the interval
  `(a, +∞)`, giving the formula `∫ x in (a, +∞), g' x = l - g a` if `g'` is integrable and
  `g` tends to `l` at `+∞`.
- `MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg` gives the same result assuming that
  `g'` is nonnegative instead of integrable. Its automatic integrability in this context is proved
  in `MeasureTheory.integrableOn_Ioi_deriv_of_nonneg`.
- `MeasureTheory.integral_deriv_smul_comp_Ioi` is a version of the change of variables formula
  on semi-infinite intervals.
- `MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi` shows that a function whose
  derivative is integrable on `(a, +∞)` has a limit at `+∞`.
- `MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi` shows that an integrable function
  whose derivative is integrable on `(a, +∞)` tends to `0` at `+∞`.

Versions of these results are also given on the intervals `(-∞, a]` and `(-∞, +∞)`, as well as
the corresponding versions of integration by parts.
-/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace Topology
open scoped ENNReal NNReal

namespace MeasureTheory

section AECover

variable {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (l : Filter ι)

/--
Definition of `AECover` / `AECover` 的定义

English:
structure AECover
  parameters: (φ : ι -> Set α)
  axioms and operations (1):
    - ae_eventually_mem : forallᵐ x ∂μ, forallᶠ i in l, x in φ i

中文:
结构 AECover
  参数: (φ : ι -> 集合 α)
  公理与运算 (1 个):
    - ae_eventually_mem : 对任意ᵐ x ∂μ, 对任意ᶠ i in l, x in φ i
-/
structure AECover (φ : ι -> Set α) : Prop where
  ae_eventually_mem : forallᵐ x ∂μ, forallᶠ i in l, x in φ i
protected measurableSet : forall i, MeasurableSet φ i

variable {μ} {l}

namespace AECover

/-!
## Operations on `AECover`s
-/

/--
theorem `inter` / 定理 `inter`

English:
theorem inter
  given: {φ ψ : ι -> Set α} (hφ : AECover μ l φ) (hψ : AECover μ l ψ)
  proof: hψ.1.mp hφ.1.mono fun _ => Eventually.and
  measurableSet _ := (hφ.2 _).inter (hψ.2 _)

中文:
定理 inter
  条件: {φ ψ : ι -> 集合 α} (hφ : AECover μ l φ) (hψ : AECover μ l ψ)
  证明: hψ.1.mp hφ.1.mono fun _ => Eventually.and
  measurableSet _ := (hφ.2 _).inter (hψ.2 _)

Depends on / 依赖: Eventually, Eventually.and
-/
theorem inter {φ ψ : ι -> Set α} (hφ : AECover μ l φ) (hψ : AECover μ l ψ) :
    AECover μ l (fun i => φ i inter ψ i) where
ae_eventually_mem := hψ.1.mp hφ.1.mono fun _ => Eventually.and
  measurableSet _ := (hφ.2 _).inter (hψ.2 _)

/--
theorem `superset` / 定理 `superset`

English:
theorem superset
  statement: {φ ψ : ι -> Set α} (hφ : AECover μ l φ) (hsub : forall i, φ i subseteq ψ i)
  proof: ⟨hφ.1.mono fun _x hx => hx.mono fun i hi => hsub i hi, hmeas⟩

中文:
定理 superset
  结论: {φ ψ : ι -> 集合 α} (hφ : AECover μ l φ) (hsub : 对任意 i, φ i subseteq ψ i)
  证明: ⟨hφ.1.mono fun _x hx => hx.mono fun i hi => hsub i hi, hmeas⟩

Depends on / 依赖: hx.mono
-/
theorem superset {φ ψ : ι -> Set α} (hφ : AECover μ l φ) (hsub : forall i, φ i subseteq ψ i)
    (hmeas : forall i, MeasurableSet (ψ i)) : AECover μ l ψ :=
  ⟨hφ.1.mono fun _x hx => hx.mono fun i hi => hsub i hi, hmeas⟩

/--
theorem `mono_ac` / 定理 `mono_ac`

English:
theorem mono_ac
  given: {ν : Measure α} {φ : ι -> Set α} (hφ : AECover μ l φ) (hle : ν ≪ μ)
  proof: ⟨hle hφ.1, hφ.2⟩

中文:
定理 mono_ac
  条件: {ν : 测度 α} {φ : ι -> 集合 α} (hφ : AECover μ l φ) (hle : ν ≪ μ)
  证明: ⟨hle hφ.1, hφ.2⟩
-/
theorem mono_ac {ν : Measure α} {φ : ι -> Set α} (hφ : AECover μ l φ) (hle : ν ≪ μ) :
    AECover ν l φ := ⟨hle hφ.1, hφ.2⟩

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: {ν : Measure α} {φ : ι -> Set α} (hφ : AECover μ l φ) (hle : ν <= μ)
  proof: hφ.mono_ac hle.absolutelyContinuous

中文:
定理 mono
  条件: {ν : 测度 α} {φ : ι -> 集合 α} (hφ : AECover μ l φ) (hle : ν <= μ)
  证明: hφ.mono_ac hle.absolutelyContinuous

Depends on / 依赖: absolutelyContinuous, hle.absolutelyContinuous, mono_ac
-/
theorem mono {ν : Measure α} {φ : ι -> Set α} (hφ : AECover μ l φ) (hle : ν <= μ) :
    AECover ν l φ := hφ.mono_ac hle.absolutelyContinuous

end AECover

section MetricSpace

variable [PseudoMetricSpace α] [OpensMeasurableSpace α]

/--
theorem `aecover_ball` / 定理 `aecover_ball`

English:
theorem aecover_ball
  given: {x : α} {r : ι -> Real} (hr : Tendsto r l atTop)
  proof: Metric.isOpen_ball.measurableSet
  ae_eventually_mem := by
    filter_upwards with y
    filter_upwards [hr (Ioi_mem_atTop (dist x y))] with a ha using by simpa [dist_comm] using ha

中文:
定理 aecover_ball
  条件: {x : α} {r : ι -> 实数} (hr : 收敛 r l atTop)
  证明: Metric.isOpen_ball.measurableSet
  ae_eventually_mem := by
    filter_upwards with y
    filter_upwards [hr (Ioi_mem_atTop (dist x y))] with a ha using by simpa [dist_comm] using ha

Depends on / 依赖: Metric, Metric.isOpen_ball.measurableSet, isOpen_ball, measurableSet
-/
theorem aecover_ball {x : α} {r : ι -> Real} (hr : Tendsto r l atTop) :
    AECover μ l (fun i => Metric.ball x (r i)) where
  measurableSet _ := Metric.isOpen_ball.measurableSet
  ae_eventually_mem := by
    filter_upwards with y
    filter_upwards [hr (Ioi_mem_atTop (dist x y))] with a ha using by simpa [dist_comm] using ha

/--
theorem `aecover_closedBall` / 定理 `aecover_closedBall`

English:
theorem aecover_closedBall
  given: {x : α} {r : ι -> Real} (hr : Tendsto r l atTop)
  proof: Metric.isClosed_closedBall.measurableSet
  ae_eventually_mem := by
    filter_upwards with y
    filter_upwards [hr (Ici_mem_atTop (dist x y))] with a ha using by simpa [dist_comm] using ha

中文:
定理 aecover_closedBall
  条件: {x : α} {r : ι -> 实数} (hr : 收敛 r l atTop)
  证明: Metric.isClosed_closedBall.measurableSet
  ae_eventually_mem := by
    filter_upwards with y
    filter_upwards [hr (Ici_mem_atTop (dist x y))] with a ha using by simpa [dist_comm] using ha

Depends on / 依赖: Metric, Metric.isClosed_closedBall.measurableSet, isClosed_closedBall, measurableSet
-/
theorem aecover_closedBall {x : α} {r : ι -> Real} (hr : Tendsto r l atTop) :
    AECover μ l (fun i => Metric.closedBall x (r i)) where
  measurableSet _ := Metric.isClosed_closedBall.measurableSet
  ae_eventually_mem := by
    filter_upwards with y
    filter_upwards [hr (Ici_mem_atTop (dist x y))] with a ha using by simpa [dist_comm] using ha

end MetricSpace

section Preorderα

variable [Preorder α] [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α]
  {a b : ι -> α}

/--
theorem `aecover_Ici` / 定理 `aecover_Ici`

English:
theorem aecover_Ici
  given: (ha : Tendsto a l atBot)
  statement: AECover μ l fun i => Ici (a i) where
  proof: ae_of_all μ ha.eventually_le_atBot
  measurableSet _ := measurableSet_Ici

中文:
定理 aecover_Ici
  条件: (ha : 收敛 a l atBot)
  结论: AECover μ l fun i => 左闭右无界区间 (a i) where
  证明: ae_of_all μ ha.eventually_le_atBot
  measurableSet _ := measurableSet_Ici

Depends on / 依赖: ae_of_all, eventually_le_atBot, ha.eventually_le_atBot
-/
theorem aecover_Ici (ha : Tendsto a l atBot) : AECover μ l fun i => Ici (a i) where
  ae_eventually_mem := ae_of_all μ ha.eventually_le_atBot
  measurableSet _ := measurableSet_Ici

/--
theorem `aecover_Iic` / 定理 `aecover_Iic`

English:
theorem aecover_Iic
  given: (hb : Tendsto b l atTop)
  statement: AECover μ l fun i => Iic b i
  proof: aecover_Ici (α := αᵒᵈ) hb

中文:
定理 aecover_Iic
  条件: (hb : 收敛 b l atTop)
  结论: AECover μ l fun i => 左无界右闭区间 b i
  证明: aecover_Ici (α := αᵒᵈ) hb

Depends on / 依赖: aecover_Ici
-/
theorem aecover_Iic (hb : Tendsto b l atTop) : AECover μ l fun i => Iic b i :=
  aecover_Ici (α := αᵒᵈ) hb

/--
theorem `aecover_Icc` / 定理 `aecover_Icc`

English:
theorem aecover_Icc
  given: (ha : Tendsto a l atBot) (hb : Tendsto b l atTop)
  proof: (aecover_Ici ha).inter (aecover_Iic hb)

中文:
定理 aecover_Icc
  条件: (ha : 收敛 a l atBot) (hb : 收敛 b l atTop)
  证明: (aecover_Ici ha).inter (aecover_Iic hb)

Depends on / 依赖: aecover_Ici, aecover_Iic
-/
theorem aecover_Icc (ha : Tendsto a l atBot) (hb : Tendsto b l atTop) :
    AECover μ l fun i => Icc (a i) (b i) :=
  (aecover_Ici ha).inter (aecover_Iic hb)

end Preorderα

section LinearOrderα

variable [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α]
  {a b : ι -> α} (ha : Tendsto a l atBot) (hb : Tendsto b l atTop)

include ha in
/--
theorem `aecover_Ioi` / 定理 `aecover_Ioi`

English:
theorem aecover_Ioi
  given: [NoMinOrder α]
  statement: AECover μ l fun i => Ioi (a i) where
  proof: ae_of_all μ ha.eventually_lt_atBot
  measurableSet _ := measurableSet_Ioi

include hb in

中文:
定理 aecover_Ioi
  条件: [NoMin序 α]
  结论: AECover μ l fun i => 左开右无界区间 (a i) where
  证明: ae_of_all μ ha.eventually_lt_atBot
  measurableSet _ := measurableSet_Ioi

include hb in

Depends on / 依赖: ae_of_all, eventually_lt_atBot, ha.eventually_lt_atBot
-/
theorem aecover_Ioi [NoMinOrder α] : AECover μ l fun i => Ioi (a i) where
  ae_eventually_mem := ae_of_all μ ha.eventually_lt_atBot
  measurableSet _ := measurableSet_Ioi

include hb in
/--
theorem `aecover_Iio` / 定理 `aecover_Iio`

English:
theorem aecover_Iio
  given: [NoMaxOrder α]
  statement: AECover μ l fun i => Iio (b i)
  proof: aecover_Ioi (α := αᵒᵈ) hb

include ha hb

中文:
定理 aecover_Iio
  条件: [NoMax序 α]
  结论: AECover μ l fun i => 左无界右开区间 (b i)
  证明: aecover_Ioi (α := αᵒᵈ) hb

include ha hb

Depends on / 依赖: aecover_Ioi
-/
theorem aecover_Iio [NoMaxOrder α] : AECover μ l fun i => Iio (b i) := aecover_Ioi (α := αᵒᵈ) hb

include ha hb

/--
theorem `aecover_Ioo` / 定理 `aecover_Ioo`

English:
theorem aecover_Ioo
  given: [NoMinOrder α] [NoMaxOrder α]
  statement: AECover μ l fun i => Ioo (a i) (b i)
  proof: (aecover_Ioi ha).inter (aecover_Iio hb)

中文:
定理 aecover_Ioo
  条件: [NoMin序 α] [NoMax序 α]
  结论: AECover μ l fun i => 开区间 (a i) (b i)
  证明: (aecover_Ioi ha).inter (aecover_Iio hb)

Depends on / 依赖: aecover_Iio, aecover_Ioi
-/
theorem aecover_Ioo [NoMinOrder α] [NoMaxOrder α] : AECover μ l fun i => Ioo (a i) (b i) :=
  (aecover_Ioi ha).inter (aecover_Iio hb)

/--
theorem `aecover_Ioc` / 定理 `aecover_Ioc`

English:
theorem aecover_Ioc
  given: [NoMinOrder α]
  statement: AECover μ l fun i => Ioc (a i) (b i)
  proof: (aecover_Ioi ha).inter (aecover_Iic hb)

中文:
定理 aecover_Ioc
  条件: [NoMin序 α]
  结论: AECover μ l fun i => 左开右闭区间 (a i) (b i)
  证明: (aecover_Ioi ha).inter (aecover_Iic hb)

Depends on / 依赖: aecover_Iic, aecover_Ioi
-/
theorem aecover_Ioc [NoMinOrder α] : AECover μ l fun i => Ioc (a i) (b i) :=
  (aecover_Ioi ha).inter (aecover_Iic hb)

/--
theorem `aecover_Ico` / 定理 `aecover_Ico`

English:
theorem aecover_Ico
  given: [NoMaxOrder α]
  statement: AECover μ l fun i => Ico (a i) (b i)
  proof: (aecover_Ici ha).inter (aecover_Iio hb)

中文:
定理 aecover_Ico
  条件: [NoMax序 α]
  结论: AECover μ l fun i => 左闭右开区间 (a i) (b i)
  证明: (aecover_Ici ha).inter (aecover_Iio hb)

Depends on / 依赖: aecover_Ici, aecover_Iio
-/
theorem aecover_Ico [NoMaxOrder α] : AECover μ l fun i => Ico (a i) (b i) :=
  (aecover_Ici ha).inter (aecover_Iio hb)

end LinearOrderα

section FiniteIntervals

variable [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α]
  {a b c d : ι -> α} {A B : α} (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
  (hc : Tendsto c l atBot) (hd : Tendsto d l atTop)

include ha in
/--
theorem `aecover_Ioi_of_Ioi` / 定理 `aecover_Ioi_of_Ioi`

English:
theorem aecover_Ioi_of_Ioi
  statement: AECover (μ.restrict (Ioi A)) l fun i => Ioi (a i) where
  proof: (ae_restrict_mem measurableSet_Ioi).mono fun _x hx => ha.eventually
    eventually_lt_nhds hx
  measurableSet _ := measurableSet_Ioi

include hb in

中文:
定理 aecover_Ioi_of_Ioi
  结论: AECover (μ.restrict (左开右无界区间 A)) l fun i => 左开右无界区间 (a i) where
  证明: (ae_restrict_mem measurableSet_Ioi).mono fun _x hx => ha.eventually
    eventually_lt_nhds hx
  measurableSet _ := measurableSet_Ioi

include hb in

Depends on / 依赖: ae_restrict_mem, eventually, ha.eventually, measurableSet_Ioi
-/
theorem aecover_Ioi_of_Ioi : AECover (μ.restrict (Ioi A)) l fun i => Ioi (a i) where
ae_eventually_mem := (ae_restrict_mem measurableSet_Ioi).mono fun _x hx => ha.eventually
    eventually_lt_nhds hx
  measurableSet _ := measurableSet_Ioi

include hb in
/--
theorem `aecover_Iio_of_Iio` / 定理 `aecover_Iio_of_Iio`

English:
theorem aecover_Iio_of_Iio
  statement: AECover (μ.restrict (Iio B)) l fun i => Iio (b i)
  proof: aecover_Ioi_of_Ioi (α := αᵒᵈ) hb

include ha in

中文:
定理 aecover_Iio_of_Iio
  结论: AECover (μ.restrict (左无界右开区间 B)) l fun i => 左无界右开区间 (b i)
  证明: aecover_Ioi_of_Ioi (α := αᵒᵈ) hb

include ha in

Depends on / 依赖: aecover_Ioi_of_Ioi
-/
theorem aecover_Iio_of_Iio : AECover (μ.restrict (Iio B)) l fun i => Iio (b i) :=
  aecover_Ioi_of_Ioi (α := αᵒᵈ) hb

include ha in
/--
theorem `aecover_Ioi_of_Ici` / 定理 `aecover_Ioi_of_Ici`

English:
theorem aecover_Ioi_of_Ici
  statement: AECover (μ.restrict (Ioi A)) l fun i => Ici (a i)
  proof: (aecover_Ioi_of_Ioi ha).superset (fun _ => Ioi_subset_Ici_self) fun _ => measurableSet_Ici

include hb in

中文:
定理 aecover_Ioi_of_Ici
  结论: AECover (μ.restrict (左开右无界区间 A)) l fun i => 左闭右无界区间 (a i)
  证明: (aecover_Ioi_of_Ioi ha).superset (fun _ => Ioi_subset_Ici_self) fun _ => measurableSet_Ici

include hb in

Depends on / 依赖: Ioi_subset_Ici_self, aecover_Ioi_of_Ioi, measurableSet_Ici, superset
-/
theorem aecover_Ioi_of_Ici : AECover (μ.restrict (Ioi A)) l fun i => Ici (a i) :=
  (aecover_Ioi_of_Ioi ha).superset (fun _ => Ioi_subset_Ici_self) fun _ => measurableSet_Ici

include hb in
/--
theorem `aecover_Iio_of_Iic` / 定理 `aecover_Iio_of_Iic`

English:
theorem aecover_Iio_of_Iic
  statement: AECover (μ.restrict (Iio B)) l fun i => Iic (b i)
  proof: aecover_Ioi_of_Ici (α := αᵒᵈ) hb

include hb hc in

中文:
定理 aecover_Iio_of_Iic
  结论: AECover (μ.restrict (左无界右开区间 B)) l fun i => 左无界右闭区间 (b i)
  证明: aecover_Ioi_of_Ici (α := αᵒᵈ) hb

include hb hc in

Depends on / 依赖: aecover_Ioi_of_Ici
-/
theorem aecover_Iio_of_Iic : AECover (μ.restrict (Iio B)) l fun i => Iic (b i) :=
  aecover_Ioi_of_Ici (α := αᵒᵈ) hb

include hb hc in
/--
theorem `aecover_Iio_of_Ico` / 定理 `aecover_Iio_of_Ico`

English:
theorem aecover_Iio_of_Ico
  statement: AECover (μ.restrict (Iio B)) l fun i => Ico (c i) (b i) where
  proof: by
    refine (ae_restrict_mem measurableSet_Iio).mono fun _x hx => ?_
    simp only [mem_Ico, eventually_and]
    exact ⟨hc.eventually (eventually_le_atBot _x), hb.eventually (eventually_gt_nhds hx)⟩
  measurableSet _ := measurableSet_Ico

include hd in

中文:
定理 aecover_Iio_of_Ico
  结论: AECover (μ.restrict (左无界右开区间 B)) l fun i => 左闭右开区间 (c i) (b i) where
  证明: by
    refine (ae_restrict_mem measurableSet_Iio).mono fun _x hx => ?_
    simp only [mem_Ico, eventually_and]
    exact ⟨hc.eventually (eventually_le_atBot _x), hb.eventually (eventually_gt_nhds hx)⟩
  measurableSet _ := measurableSet_Ico

include hd in

Depends on / 依赖: ae_restrict_mem, eventually, eventually_and, eventually_gt_nhds, eventually_le_atBot, hb.eventually, hc.eventually, measurableSet, measurableSet_Ico, measurableSet_Iio, mem_Ico
-/
theorem aecover_Iio_of_Ico : AECover (μ.restrict (Iio B)) l fun i => Ico (c i) (b i) where
  ae_eventually_mem := by
    refine (ae_restrict_mem measurableSet_Iio).mono fun _x hx => ?_
    simp only [mem_Ico, eventually_and]
    exact ⟨hc.eventually (eventually_le_atBot _x), hb.eventually (eventually_gt_nhds hx)⟩
  measurableSet _ := measurableSet_Ico

include hd in
/--
theorem `aecover_Ici_of_Ico` / 定理 `aecover_Ici_of_Ico`

English:
theorem aecover_Ici_of_Ico
  given: [NoMaxOrder α]
  statement: AECover (μ.restrict (Ici B)) l fun i => Ico B (d i) where
  proof: by
    refine (ae_restrict_mem measurableSet_Ici).mono fun _x hx => ?_
    simp only [mem_Ico, eventually_and]
    exact⟨.of_forall fun i => hx, hd.eventually (eventually_gt_atTop _x)⟩
  measurableSet _ := measurableSet_Ico

include ha hb in

中文:
定理 aecover_Ici_of_Ico
  条件: [NoMax序 α]
  结论: AECover (μ.restrict (左闭右无界区间 B)) l fun i => 左闭右开区间 B (d i) where
  证明: by
    refine (ae_restrict_mem measurableSet_Ici).mono fun _x hx => ?_
    simp only [mem_Ico, eventually_and]
    exact⟨.of_forall fun i => hx, hd.eventually (eventually_gt_atTop _x)⟩
  measurableSet _ := measurableSet_Ico

include ha hb in

Depends on / 依赖: ae_restrict_mem, eventually, eventually_and, eventually_gt_atTop, hd.eventually, measurableSet, measurableSet_Ici, measurableSet_Ico, mem_Ico, of_forall
-/
theorem aecover_Ici_of_Ico [NoMaxOrder α] : AECover (μ.restrict (Ici B)) l fun i => Ico B (d i) where
  ae_eventually_mem := by
    refine (ae_restrict_mem measurableSet_Ici).mono fun _x hx => ?_
    simp only [mem_Ico, eventually_and]
    exact⟨.of_forall fun i => hx, hd.eventually (eventually_gt_atTop _x)⟩
  measurableSet _ := measurableSet_Ico

include ha hb in
/--
theorem `aecover_Ioo_of_Ioo` / 定理 `aecover_Ioo_of_Ioo`

English:
theorem aecover_Ioo_of_Ioo
  statement: AECover (μ.restrict <| Ioo A B) l fun i => Ioo (a i) (b i)
  proof: ((aecover_Ioi_of_Ioi ha).mono <| Measure.restrict_mono Ioo_subset_Ioi_self le_rfl).inter
    ((aecover_Iio_of_Iio hb).mono <| Measure.restrict_mono Ioo_subset_Iio_self le_rfl)

include ha hb in

中文:
定理 aecover_Ioo_of_Ioo
  结论: AECover (μ.restrict <| 开区间 A B) l fun i => 开区间 (a i) (b i)
  证明: ((aecover_Ioi_of_Ioi ha).mono <| Measure.restrict_mono Ioo_subset_Ioi_self le_rfl).inter
    ((aecover_Iio_of_Iio hb).mono <| Measure.restrict_mono Ioo_subset_Iio_self le_rfl)

include ha hb in

Depends on / 依赖: Ioo_subset_Iio_self, Ioo_subset_Ioi_self, Measure, Measure.restrict_mono, aecover_Iio_of_Iio, aecover_Ioi_of_Ioi, le_rfl, restrict_mono
-/
theorem aecover_Ioo_of_Ioo : AECover (μ.restrict <| Ioo A B) l fun i => Ioo (a i) (b i) :=
  ((aecover_Ioi_of_Ioi ha).mono <| Measure.restrict_mono Ioo_subset_Ioi_self le_rfl).inter
    ((aecover_Iio_of_Iio hb).mono <| Measure.restrict_mono Ioo_subset_Iio_self le_rfl)

include ha hb in
/--
theorem `aecover_Ioo_of_Icc` / 定理 `aecover_Ioo_of_Icc`

English:
theorem aecover_Ioo_of_Icc
  statement: AECover (μ.restrict <| Ioo A B) l fun i => Icc (a i) (b i)
  proof: (aecover_Ioo_of_Ioo ha hb).superset (fun _ => Ioo_subset_Icc_self) fun _ => measurableSet_Icc

include ha hb in

中文:
定理 aecover_Ioo_of_Icc
  结论: AECover (μ.restrict <| 开区间 A B) l fun i => 闭区间 (a i) (b i)
  证明: (aecover_Ioo_of_Ioo ha hb).superset (fun _ => Ioo_subset_Icc_self) fun _ => measurableSet_Icc

include ha hb in

Depends on / 依赖: Ioo_subset_Icc_self, aecover_Ioo_of_Ioo, measurableSet_Icc, superset
-/
theorem aecover_Ioo_of_Icc : AECover (μ.restrict <| Ioo A B) l fun i => Icc (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).superset (fun _ => Ioo_subset_Icc_self) fun _ => measurableSet_Icc

include ha hb in
/--
theorem `aecover_Ioo_of_Ico` / 定理 `aecover_Ioo_of_Ico`

English:
theorem aecover_Ioo_of_Ico
  statement: AECover (μ.restrict <| Ioo A B) l fun i => Ico (a i) (b i)
  proof: (aecover_Ioo_of_Ioo ha hb).superset (fun _ => Ioo_subset_Ico_self) fun _ => measurableSet_Ico

include ha hb in

中文:
定理 aecover_Ioo_of_Ico
  结论: AECover (μ.restrict <| 开区间 A B) l fun i => 左闭右开区间 (a i) (b i)
  证明: (aecover_Ioo_of_Ioo ha hb).superset (fun _ => Ioo_subset_Ico_self) fun _ => measurableSet_Ico

include ha hb in

Depends on / 依赖: Ioo_subset_Ico_self, aecover_Ioo_of_Ioo, measurableSet_Ico, superset
-/
theorem aecover_Ioo_of_Ico : AECover (μ.restrict <| Ioo A B) l fun i => Ico (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).superset (fun _ => Ioo_subset_Ico_self) fun _ => measurableSet_Ico

include ha hb in
/--
theorem `aecover_Ioo_of_Ioc` / 定理 `aecover_Ioo_of_Ioc`

English:
theorem aecover_Ioo_of_Ioc
  statement: AECover (μ.restrict <| Ioo A B) l fun i => Ioc (a i) (b i)
  proof: (aecover_Ioo_of_Ioo ha hb).superset (fun _ => Ioo_subset_Ioc_self) fun _ => measurableSet_Ioc

中文:
定理 aecover_Ioo_of_Ioc
  结论: AECover (μ.restrict <| 开区间 A B) l fun i => 左开右闭区间 (a i) (b i)
  证明: (aecover_Ioo_of_Ioo ha hb).superset (fun _ => Ioo_subset_Ioc_self) fun _ => measurableSet_Ioc

Depends on / 依赖: Ioo_subset_Ioc_self, aecover_Ioo_of_Ioo, measurableSet_Ioc, superset
-/
theorem aecover_Ioo_of_Ioc : AECover (μ.restrict <| Ioo A B) l fun i => Ioc (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).superset (fun _ => Ioo_subset_Ioc_self) fun _ => measurableSet_Ioc

variable [NullSingletonClass μ]

/--
theorem `aecover_Ioc_of_Icc` / 定理 `aecover_Ioc_of_Icc`

English:
theorem aecover_Ioc_of_Icc
  given: (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
  proof: (aecover_Ioo_of_Icc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge

中文:
定理 aecover_Ioc_of_Icc
  条件: (ha : 收敛 a l (𝓝 A)) (hb : 收敛 b l (𝓝 B))
  证明: (aecover_Ioo_of_Icc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge

Depends on / 依赖: Ioo_ae_eq_Ioc, Measure, Measure.restrict_congr_set, aecover_Ioo_of_Icc, restrict_congr_set
-/
theorem aecover_Ioc_of_Icc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ioc A B) l fun i => Icc (a i) (b i) :=
  (aecover_Ioo_of_Icc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge

/--
theorem `aecover_Ioc_of_Ico` / 定理 `aecover_Ioc_of_Ico`

English:
theorem aecover_Ioc_of_Ico
  given: (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
  proof: (aecover_Ioo_of_Ico ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge

中文:
定理 aecover_Ioc_of_Ico
  条件: (ha : 收敛 a l (𝓝 A)) (hb : 收敛 b l (𝓝 B))
  证明: (aecover_Ioo_of_Ico ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge

Depends on / 依赖: Ioo_ae_eq_Ioc, Measure, Measure.restrict_congr_set, aecover_Ioo_of_Ico, restrict_congr_set
-/
theorem aecover_Ioc_of_Ico (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ioc A B) l fun i => Ico (a i) (b i) :=
  (aecover_Ioo_of_Ico ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge

/--
theorem `aecover_Ioc_of_Ioc` / 定理 `aecover_Ioc_of_Ioc`

English:
theorem aecover_Ioc_of_Ioc
  given: (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
  proof: (aecover_Ioo_of_Ioc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge

中文:
定理 aecover_Ioc_of_Ioc
  条件: (ha : 收敛 a l (𝓝 A)) (hb : 收敛 b l (𝓝 B))
  证明: (aecover_Ioo_of_Ioc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge

Depends on / 依赖: Ioo_ae_eq_Ioc, Measure, Measure.restrict_congr_set, aecover_Ioo_of_Ioc, restrict_congr_set
-/
theorem aecover_Ioc_of_Ioc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ioc A B) l fun i => Ioc (a i) (b i) :=
  (aecover_Ioo_of_Ioc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge

/--
theorem `aecover_Ioc_of_Ioo` / 定理 `aecover_Ioc_of_Ioo`

English:
theorem aecover_Ioc_of_Ioo
  given: (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
  proof: (aecover_Ioo_of_Ioo ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge

中文:
定理 aecover_Ioc_of_Ioo
  条件: (ha : 收敛 a l (𝓝 A)) (hb : 收敛 b l (𝓝 B))
  证明: (aecover_Ioo_of_Ioo ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge

Depends on / 依赖: Ioo_ae_eq_Ioc, Measure, Measure.restrict_congr_set, aecover_Ioo_of_Ioo, restrict_congr_set
-/
theorem aecover_Ioc_of_Ioo (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ioc A B) l fun i => Ioo (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge

/--
theorem `aecover_Ico_of_Icc` / 定理 `aecover_Ico_of_Icc`

English:
theorem aecover_Ico_of_Icc
  given: (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
  proof: (aecover_Ioo_of_Icc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge

中文:
定理 aecover_Ico_of_Icc
  条件: (ha : 收敛 a l (𝓝 A)) (hb : 收敛 b l (𝓝 B))
  证明: (aecover_Ioo_of_Icc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge

Depends on / 依赖: Ioo_ae_eq_Ico, Measure, Measure.restrict_congr_set, aecover_Ioo_of_Icc, restrict_congr_set
-/
theorem aecover_Ico_of_Icc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ico A B) l fun i => Icc (a i) (b i) :=
  (aecover_Ioo_of_Icc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge

/--
theorem `aecover_Ico_of_Ico` / 定理 `aecover_Ico_of_Ico`

English:
theorem aecover_Ico_of_Ico
  given: (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
  proof: (aecover_Ioo_of_Ico ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge

中文:
定理 aecover_Ico_of_Ico
  条件: (ha : 收敛 a l (𝓝 A)) (hb : 收敛 b l (𝓝 B))
  证明: (aecover_Ioo_of_Ico ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge

Depends on / 依赖: Ioo_ae_eq_Ico, Measure, Measure.restrict_congr_set, aecover_Ioo_of_Ico, restrict_congr_set
-/
theorem aecover_Ico_of_Ico (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ico A B) l fun i => Ico (a i) (b i) :=
  (aecover_Ioo_of_Ico ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge

/--
theorem `aecover_Ico_of_Ioc` / 定理 `aecover_Ico_of_Ioc`

English:
theorem aecover_Ico_of_Ioc
  given: (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
  proof: (aecover_Ioo_of_Ioc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge

中文:
定理 aecover_Ico_of_Ioc
  条件: (ha : 收敛 a l (𝓝 A)) (hb : 收敛 b l (𝓝 B))
  证明: (aecover_Ioo_of_Ioc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge

Depends on / 依赖: Ioo_ae_eq_Ico, Measure, Measure.restrict_congr_set, aecover_Ioo_of_Ioc, restrict_congr_set
-/
theorem aecover_Ico_of_Ioc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ico A B) l fun i => Ioc (a i) (b i) :=
  (aecover_Ioo_of_Ioc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge

/--
theorem `aecover_Ico_of_Ioo` / 定理 `aecover_Ico_of_Ioo`

English:
theorem aecover_Ico_of_Ioo
  given: (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
  proof: (aecover_Ioo_of_Ioo ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge

中文:
定理 aecover_Ico_of_Ioo
  条件: (ha : 收敛 a l (𝓝 A)) (hb : 收敛 b l (𝓝 B))
  证明: (aecover_Ioo_of_Ioo ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge

Depends on / 依赖: Ioo_ae_eq_Ico, Measure, Measure.restrict_congr_set, aecover_Ioo_of_Ioo, restrict_congr_set
-/
theorem aecover_Ico_of_Ioo (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ico A B) l fun i => Ioo (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge

/--
theorem `aecover_Icc_of_Icc` / 定理 `aecover_Icc_of_Icc`

English:
theorem aecover_Icc_of_Icc
  given: (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
  proof: (aecover_Ioo_of_Icc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

中文:
定理 aecover_Icc_of_Icc
  条件: (ha : 收敛 a l (𝓝 A)) (hb : 收敛 b l (𝓝 B))
  证明: (aecover_Ioo_of_Icc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

Depends on / 依赖: Ioo_ae_eq_Icc, Measure, Measure.restrict_congr_set, aecover_Ioo_of_Icc, restrict_congr_set
-/
theorem aecover_Icc_of_Icc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Icc A B) l fun i => Icc (a i) (b i) :=
  (aecover_Ioo_of_Icc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

/--
theorem `aecover_Icc_of_Ico` / 定理 `aecover_Icc_of_Ico`

English:
theorem aecover_Icc_of_Ico
  given: (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
  proof: (aecover_Ioo_of_Ico ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

中文:
定理 aecover_Icc_of_Ico
  条件: (ha : 收敛 a l (𝓝 A)) (hb : 收敛 b l (𝓝 B))
  证明: (aecover_Ioo_of_Ico ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

Depends on / 依赖: Ioo_ae_eq_Icc, Measure, Measure.restrict_congr_set, aecover_Ioo_of_Ico, restrict_congr_set
-/
theorem aecover_Icc_of_Ico (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Icc A B) l fun i => Ico (a i) (b i) :=
  (aecover_Ioo_of_Ico ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

/--
theorem `aecover_Icc_of_Ioc` / 定理 `aecover_Icc_of_Ioc`

English:
theorem aecover_Icc_of_Ioc
  given: (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
  proof: (aecover_Ioo_of_Ioc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

中文:
定理 aecover_Icc_of_Ioc
  条件: (ha : 收敛 a l (𝓝 A)) (hb : 收敛 b l (𝓝 B))
  证明: (aecover_Ioo_of_Ioc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

Depends on / 依赖: Ioo_ae_eq_Icc, Measure, Measure.restrict_congr_set, aecover_Ioo_of_Ioc, restrict_congr_set
-/
theorem aecover_Icc_of_Ioc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Icc A B) l fun i => Ioc (a i) (b i) :=
  (aecover_Ioo_of_Ioc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

/--
theorem `aecover_Icc_of_Ioo` / 定理 `aecover_Icc_of_Ioo`

English:
theorem aecover_Icc_of_Ioo
  given: (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
  proof: (aecover_Ioo_of_Ioo ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

中文:
定理 aecover_Icc_of_Ioo
  条件: (ha : 收敛 a l (𝓝 A)) (hb : 收敛 b l (𝓝 B))
  证明: (aecover_Ioo_of_Ioo ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

Depends on / 依赖: Ioo_ae_eq_Icc, Measure, Measure.restrict_congr_set, aecover_Ioo_of_Ioo, restrict_congr_set
-/
theorem aecover_Icc_of_Ioo (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Icc A B) l fun i => Ioo (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

end FiniteIntervals

/--
theorem `AECover.restrict` / 定理 `AECover.restrict`

English:
theorem AECover.restrict
  given: {φ : ι -> Set α} (hφ : AECover μ l φ) {s : Set α}
  proof: hφ.mono Measure.restrict_le_self

中文:
定理 AECover.restrict
  条件: {φ : ι -> 集合 α} (hφ : AECover μ l φ) {s : 集合 α}
  证明: hφ.mono Measure.restrict_le_self
-/
protected theorem AECover.restrict {φ : ι -> Set α} (hφ : AECover μ l φ) {s : Set α} :
    AECover (μ.restrict s) l φ :=
  hφ.mono Measure.restrict_le_self

/--
theorem `aecover_restrict_of_ae_imp` / 定理 `aecover_restrict_of_ae_imp`

English:
theorem aecover_restrict_of_ae_imp
  statement: {s : Set α} {φ : ι -> Set α} (hs : MeasurableSet s)
  proof: by rwa [ae_restrict_iff' hs]
  measurableSet := measurable

中文:
定理 aecover_restrict_of_ae_imp
  结论: {s : 集合 α} {φ : ι -> 集合 α} (hs : 可测集 s)
  证明: by rwa [ae_restrict_iff' hs]
  measurableSet := measurable

Depends on / 依赖: ae_restrict_iff, measurable, measurableSet
-/
theorem aecover_restrict_of_ae_imp {s : Set α} {φ : ι -> Set α} (hs : MeasurableSet s)
    (ae_eventually_mem : forallᵐ x ∂μ, x in s -> forallᶠ n in l, x in φ n)
    (measurable : forall n, MeasurableSet <| φ n) : AECover (μ.restrict s) l φ where
  ae_eventually_mem := by rwa [ae_restrict_iff' hs]
  measurableSet := measurable

/--
theorem `AECover.inter_restrict` / 定理 `AECover.inter_restrict`

English:
theorem AECover.inter_restrict
  statement: {φ : ι -> Set α} (hφ : AECover μ l φ) {s : Set α}
  proof: aecover_restrict_of_ae_imp hs
    (hφ.ae_eventually_mem.mono fun _x hx hxs => hx.mono fun _i hi => ⟨hi, hxs⟩) fun i =>
    (hφ.measurableSet i).inter hs

中文:
定理 AECover.inter_restrict
  结论: {φ : ι -> 集合 α} (hφ : AECover μ l φ) {s : 集合 α}
  证明: aecover_restrict_of_ae_imp hs
    (hφ.ae_eventually_mem.mono fun _x hx hxs => hx.mono fun _i hi => ⟨hi, hxs⟩) fun i =>
    (hφ.measurableSet i).inter hs

Depends on / 依赖: ae_eventually_mem, ae_eventually_mem.mono, aecover_restrict_of_ae_imp, hx.mono, measurableSet
-/
theorem AECover.inter_restrict {φ : ι -> Set α} (hφ : AECover μ l φ) {s : Set α}
    (hs : MeasurableSet s) : AECover (μ.restrict s) l fun i => φ i inter s :=
  aecover_restrict_of_ae_imp hs
    (hφ.ae_eventually_mem.mono fun _x hx hxs => hx.mono fun _i hi => ⟨hi, hxs⟩) fun i =>
    (hφ.measurableSet i).inter hs

/--
theorem `AECover.ae_tendsto_indicator` / 定理 `AECover.ae_tendsto_indicator`

English:
theorem AECover.ae_tendsto_indicator
  statement: {β : Type*} [Zero β] [TopologicalSpace β] (f : α -> β)
  proof: hφ.ae_eventually_mem.mono fun _x hx =>
tendsto_const_nhds.congr' hx.mono fun _n hn => (indicator_of_mem hn _).symm

中文:
定理 AECover.ae_tendsto_indicator
  结论: {β : 类型} [零 β] [拓扑空间 β] (f : α -> β)
  证明: hφ.ae_eventually_mem.mono fun _x hx =>
tendsto_const_nhds.congr' hx.mono fun _n hn => (indicator_of_mem hn _).symm

Depends on / 依赖: ae_eventually_mem, ae_eventually_mem.mono, hx.mono, indicator_of_mem, tendsto_const_nhds, tendsto_const_nhds.congr
-/
theorem AECover.ae_tendsto_indicator {β : Type*} [Zero β] [TopologicalSpace β] (f : α -> β)
    {φ : ι -> Set α} (hφ : AECover μ l φ) :
    forallᵐ x ∂μ, Tendsto (fun i => (φ i).indicator f x) l (𝓝 <| f x) :=
  hφ.ae_eventually_mem.mono fun _x hx =>
tendsto_const_nhds.congr' hx.mono fun _n hn => (indicator_of_mem hn _).symm

/--
theorem `AECover.aemeasurable` / 定理 `AECover.aemeasurable`

English:
theorem AECover.aemeasurable
  statement: {β : Type*} [MeasurableSpace β] [l.IsCountablyGenerated] [l.NeBot]
  proof: by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  have := aemeasurable_iUnion_iff.mpr fun n : Nat => hfm (u n)
  rwa [Measure.restrict_eq_self_of_ae_mem] at this
  filter_upwards [hφ.ae_eventually_mem] with x hx using
    mem_iUnion.mpr (hu.eventually hx).exists

中文:
定理 AECover.aemeasurable
  结论: {β : 类型} [可测空间 β] [l.是余untablyGenerated] [l.NeBot]
  证明: by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  have := aemeasurable_iUnion_iff.mpr fun n : Nat => hfm (u n)
  rwa [Measure.restrict_eq_self_of_ae_mem] at this
  filter_upwards [hφ.ae_eventually_mem] with x hx using
    mem_iUnion.mpr (hu.eventually hx).exists

Depends on / 依赖: Measure, Measure.restrict_eq_self_of_ae_mem, ae_eventually_mem, aemeasurable_iUnion_iff, aemeasurable_iUnion_iff.mpr, eventually, exists_seq_tendsto, filter_upwards, hu.eventually, l.exists_seq_tendsto, mem_iUnion, mem_iUnion.mpr, restrict_eq_self_of_ae_mem
-/
theorem AECover.aemeasurable {β : Type*} [MeasurableSpace β] [l.IsCountablyGenerated] [l.NeBot]
    {f : α -> β} {φ : ι -> Set α} (hφ : AECover μ l φ)
    (hfm : forall i, AEMeasurable f (μ.restrict <| φ i)) : AEMeasurable f μ := by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  have := aemeasurable_iUnion_iff.mpr fun n : Nat => hfm (u n)
  rwa [Measure.restrict_eq_self_of_ae_mem] at this
  filter_upwards [hφ.ae_eventually_mem] with x hx using
    mem_iUnion.mpr (hu.eventually hx).exists

/--
theorem `AECover.aestronglyMeasurable` / 定理 `AECover.aestronglyMeasurable`

English:
theorem AECover.aestronglyMeasurable
  statement: {β : Type*} [TopologicalSpace β] [PseudoMetrizableSpace β]
  proof: by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  have := aestronglyMeasurable_iUnion_iff.mpr fun n : Nat => hfm (u n)
  rwa [Measure.restrict_eq_self_of_ae_mem] at this
  filter_upwards [hφ.ae_eventually_mem] with x hx using mem_iUnion.mpr (hu.eventually hx).exists

中文:
定理 AECover.aestronglyMeasurable
  结论: {β : 类型} [拓扑空间 β] [PseudoMetrizable空间 β]
  证明: by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  have := aestronglyMeasurable_iUnion_iff.mpr fun n : Nat => hfm (u n)
  rwa [Measure.restrict_eq_self_of_ae_mem] at this
  filter_upwards [hφ.ae_eventually_mem] with x hx using mem_iUnion.mpr (hu.eventually hx).exists

Depends on / 依赖: Measure, Measure.restrict_eq_self_of_ae_mem, ae_eventually_mem, aestronglyMeasurable_iUnion_iff, aestronglyMeasurable_iUnion_iff.mpr, eventually, exists_seq_tendsto, filter_upwards, hu.eventually, l.exists_seq_tendsto, mem_iUnion, mem_iUnion.mpr, restrict_eq_self_of_ae_mem
-/
theorem AECover.aestronglyMeasurable {β : Type*} [TopologicalSpace β] [PseudoMetrizableSpace β]
    [l.IsCountablyGenerated] [l.NeBot] {f : α -> β} {φ : ι -> Set α} (hφ : AECover μ l φ)
    (hfm : forall i, AEStronglyMeasurable f (μ.restrict <| φ i)) : AEStronglyMeasurable f μ := by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  have := aestronglyMeasurable_iUnion_iff.mpr fun n : Nat => hfm (u n)
  rwa [Measure.restrict_eq_self_of_ae_mem] at this
  filter_upwards [hφ.ae_eventually_mem] with x hx using mem_iUnion.mpr (hu.eventually hx).exists

end AECover

/--
theorem `AECover.comp_tendsto` / 定理 `AECover.comp_tendsto`

English:
theorem AECover.comp_tendsto
  statement: {α ι ι' : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
  proof: hφ.ae_eventually_mem.mono fun _x hx => hu.eventually hx
  measurableSet i := hφ.measurableSet (u i)

中文:
定理 AECover.comp_tendsto
  结论: {α ι ι' : 类型} [可测空间 α] {μ : 测度 α} {l : 滤子 ι}
  证明: hφ.ae_eventually_mem.mono fun _x hx => hu.eventually hx
  measurableSet i := hφ.measurableSet (u i)

Depends on / 依赖: ae_eventually_mem, ae_eventually_mem.mono, eventually, hu.eventually
-/
theorem AECover.comp_tendsto {α ι ι' : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
    {l' : Filter ι'} {φ : ι -> Set α} (hφ : AECover μ l φ) {u : ι' -> ι} (hu : Tendsto u l' l) :
    AECover μ l' (φ ∘ u) where
  ae_eventually_mem := hφ.ae_eventually_mem.mono fun _x hx => hu.eventually hx
  measurableSet i := hφ.measurableSet (u i)

section AECoverUnionInterCountable

variable {α ι : Type*} [Countable ι] [MeasurableSpace α] {μ : Measure α}

/--
theorem `AECover.biUnion_Iic_aecover` / 定理 `AECover.biUnion_Iic_aecover`

English:
theorem AECover.biUnion_Iic_aecover
  given: [Preorder ι] {φ : ι -> Set α} (hφ : AECover μ atTop φ)
  proof: hφ.superset (fun _ => subset_biUnion_of_mem self_mem_Iic) fun _ => .biUnion (to_countable _)
    fun _ _ => (hφ.2 _)

中文:
定理 AECover.biUnion_Iic_aecover
  条件: [预序 ι] {φ : ι -> 集合 α} (hφ : AECover μ atTop φ)
  证明: hφ.superset (fun _ => subset_biUnion_of_mem self_mem_Iic) fun _ => .biUnion (to_countable _)
    fun _ _ => (hφ.2 _)

Depends on / 依赖: biUnion, self_mem_Iic, subset_biUnion_of_mem, superset, to_countable
-/
theorem AECover.biUnion_Iic_aecover [Preorder ι] {φ : ι -> Set α} (hφ : AECover μ atTop φ) :
    AECover μ atTop fun n : ι => ⋃ (k) (_h : k in Iic n), φ k :=
  hφ.superset (fun _ => subset_biUnion_of_mem self_mem_Iic) fun _ => .biUnion (to_countable _)
    fun _ _ => (hφ.2 _)

/--
theorem `AECover.biInter_Ici_aecover` / 定理 `AECover.biInter_Ici_aecover`

English:
theorem AECover.biInter_Ici_aecover
  statement: [Preorder ι] {φ : ι -> Set α}
  proof: hφ.ae_eventually_mem.mono fun x h => by
    simpa only [mem_iInter, mem_Ici, eventually_forall_ge_atTop]
  measurableSet _ := .biInter (to_countable _) fun n _ => hφ.measurableSet n

中文:
定理 AECover.bi整数er_Ici_aecover
  结论: [预序 ι] {φ : ι -> 集合 α}
  证明: hφ.ae_eventually_mem.mono fun x h => by
    simpa only [mem_iInter, mem_Ici, eventually_forall_ge_atTop]
  measurableSet _ := .biInter (to_countable _) fun n _ => hφ.measurableSet n

Depends on / 依赖: ae_eventually_mem, ae_eventually_mem.mono, biInter, eventually_forall_ge_atTop, measurableSet, mem_Ici, mem_iInter, to_countable
-/
theorem AECover.biInter_Ici_aecover [Preorder ι] {φ : ι -> Set α}
    (hφ : AECover μ atTop φ) : AECover μ atTop fun n : ι => ⋂ (k) (_h : k in Ici n), φ k where
  ae_eventually_mem := hφ.ae_eventually_mem.mono fun x h => by
    simpa only [mem_iInter, mem_Ici, eventually_forall_ge_atTop]
  measurableSet _ := .biInter (to_countable _) fun n _ => hφ.measurableSet n

end AECoverUnionInterCountable

section Lintegral

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}

/--
theorem `lintegral_tendsto_of_monotone_of_nat` / 定理 `lintegral_tendsto_of_monotone_of_nat`

English:
theorem lintegral_tendsto_of_monotone_of_nat
  statement: {φ : Nat -> Set α} (hφ : AECover μ atTop φ)
  proof: let F n := (φ n).indicator f
  have key₁ : forall n, AEMeasurable (F n) μ := fun n => hfm.indicator (hφ.measurableSet n)
  have key₂ : forallᵐ x : α ∂μ, Monotone fun n => F n x := ae_of_all _ fun x _i _j hij => by
    dsimp [F]; grw [hmono hij]
  have key₃ : forallᵐ x : α ∂μ, Tendsto (fun n => F n x

中文:
定理 lintegral_tendsto_of_monotone_of_nat
  结论: {φ : 自然数 -> 集合 α} (hφ : AECover μ atTop φ)
  证明: let F n := (φ n).indicator f
  have key₁ : forall n, AEMeasurable (F n) μ := fun n => hfm.indicator (hφ.measurableSet n)
  have key₂ : forallᵐ x : α ∂μ, Monotone fun n => F n x := ae_of_all _ fun x _i _j hij => by
    dsimp [F]; grw [hmono hij]
  have key₃ : forallᵐ x : α ∂μ, Tendsto (fun n => F n x
-/
private theorem lintegral_tendsto_of_monotone_of_nat {φ : Nat -> Set α} (hφ : AECover μ atTop φ)
    (hmono : Monotone φ) {f : α -> Real>=0∞} (hfm : AEMeasurable f μ) :
    Tendsto (fun i => ∫⁻ x in φ i, f x ∂μ) atTop (𝓝 <| ∫⁻ x, f x ∂μ) :=
  let F n := (φ n).indicator f
  have key₁ : forall n, AEMeasurable (F n) μ := fun n => hfm.indicator (hφ.measurableSet n)
  have key₂ : forallᵐ x : α ∂μ, Monotone fun n => F n x := ae_of_all _ fun x _i _j hij => by
    dsimp [F]; grw [hmono hij]
  have key₃ : forallᵐ x : α ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := hφ.ae_tendsto_indicator f
  (lintegral_tendsto_of_tendsto_of_monotone key₁ key₂ key₃).congr fun n =>
    lintegral_indicator (hφ.measurableSet n) _

/--
theorem `AECover.lintegral_tendsto_of_nat` / 定理 `AECover.lintegral_tendsto_of_nat`

English:
theorem AECover.lintegral_tendsto_of_nat
  statement: {φ : Nat -> Set α} (hφ : AECover μ atTop φ) {f : α -> Real>=0∞}
  proof: by
  have lim₁ := lintegral_tendsto_of_monotone_of_nat hφ.biInter_Ici_aecover
    (fun i j hij => biInter_subset_biInter_left (Ici_subset_Ici.mpr hij)) hfm
  have lim₂ := lintegral_tendsto_of_monotone_of_nat hφ.biUnion_Iic_aecover
    (fun i j hij => biUnion_subset_biUnion_left (Iic_subset_Iic.mpr h

中文:
定理 AECover.lintegral_tendsto_of_nat
  结论: {φ : 自然数 -> 集合 α} (hφ : AECover μ atTop φ) {f : α -> 实数>=0∞}
  证明: by
  have lim₁ := lintegral_tendsto_of_monotone_of_nat hφ.biInter_Ici_aecover
    (fun i j hij => biInter_subset_biInter_left (Ici_subset_Ici.mpr hij)) hfm
  have lim₂ := lintegral_tendsto_of_monotone_of_nat hφ.biUnion_Iic_aecover
    (fun i j hij => biUnion_subset_biUnion_left (Iic_subset_Iic.mpr h

Depends on / 依赖: Ici_subset_Ici, Ici_subset_Ici.mpr, Iic_subset_Iic, Iic_subset_Iic.mpr, biInter_Ici_aecover, biInter_subset_biInter_left, biInter_subset_of_mem, biUnion_Iic_aecover, biUnion_subset_biUnion_left, exacts, lintegral_mono_set, lintegral_tendsto_of_monotone_of_nat, self_mem_Ici, self_mem_Ii, subset_biUnion_of_mem, tendsto_of_tendsto_of_tendsto_of_le_of_le
-/
theorem AECover.lintegral_tendsto_of_nat {φ : Nat -> Set α} (hφ : AECover μ atTop φ) {f : α -> Real>=0∞}
    (hfm : AEMeasurable f μ) : Tendsto (∫⁻ x in φ ·, f x ∂μ) atTop (𝓝 <| ∫⁻ x, f x ∂μ) := by
  have lim₁ := lintegral_tendsto_of_monotone_of_nat hφ.biInter_Ici_aecover
    (fun i j hij => biInter_subset_biInter_left (Ici_subset_Ici.mpr hij)) hfm
  have lim₂ := lintegral_tendsto_of_monotone_of_nat hφ.biUnion_Iic_aecover
    (fun i j hij => biUnion_subset_biUnion_left (Iic_subset_Iic.mpr hij)) hfm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le lim₁ lim₂ (fun n => ?_) fun n => ?_
  exacts [lintegral_mono_set (biInter_subset_of_mem self_mem_Ici),
    lintegral_mono_set (subset_biUnion_of_mem self_mem_Iic)]

/--
theorem `AECover.lintegral_tendsto_of_countably_generated` / 定理 `AECover.lintegral_tendsto_of_countably_generated`

English:
theorem AECover.lintegral_tendsto_of_countably_generated
  statement: [l.IsCountablyGenerated] {φ : ι -> Set α}
  proof: tendsto_of_seq_tendsto fun _u hu => (hφ.comp_tendsto hu).lintegral_tendsto_of_nat hfm

中文:
定理 AECover.lintegral_tendsto_of_countably_generated
  结论: [l.是余untablyGenerated] {φ : ι -> 集合 α}
  证明: tendsto_of_seq_tendsto fun _u hu => (hφ.comp_tendsto hu).lintegral_tendsto_of_nat hfm

Depends on / 依赖: comp_tendsto, lintegral_tendsto_of_nat, tendsto_of_seq_tendsto
-/
theorem AECover.lintegral_tendsto_of_countably_generated [l.IsCountablyGenerated] {φ : ι -> Set α}
    (hφ : AECover μ l φ) {f : α -> Real>=0∞} (hfm : AEMeasurable f μ) :
    Tendsto (fun i => ∫⁻ x in φ i, f x ∂μ) l (𝓝 <| ∫⁻ x, f x ∂μ) :=
  tendsto_of_seq_tendsto fun _u hu => (hφ.comp_tendsto hu).lintegral_tendsto_of_nat hfm

/--
theorem `AECover.lintegral_eq_of_tendsto` / 定理 `AECover.lintegral_eq_of_tendsto`

English:
theorem AECover.lintegral_eq_of_tendsto
  statement: [l.NeBot] [l.IsCountablyGenerated] {φ : ι -> Set α}
  proof: tendsto_nhds_unique (hφ.lintegral_tendsto_of_countably_generated hfm) htendsto

中文:
定理 AECover.lintegral_eq_of_tendsto
  结论: [l.NeBot] [l.是余untablyGenerated] {φ : ι -> 集合 α}
  证明: tendsto_nhds_unique (hφ.lintegral_tendsto_of_countably_generated hfm) htendsto

Depends on / 依赖: htendsto, lintegral_tendsto_of_countably_generated, tendsto_nhds_unique
-/
theorem AECover.lintegral_eq_of_tendsto [l.NeBot] [l.IsCountablyGenerated] {φ : ι -> Set α}
    (hφ : AECover μ l φ) {f : α -> Real>=0∞} (I : Real>=0∞) (hfm : AEMeasurable f μ)
    (htendsto : Tendsto (fun i => ∫⁻ x in φ i, f x ∂μ) l (𝓝 I)) : ∫⁻ x, f x ∂μ = I :=
  tendsto_nhds_unique (hφ.lintegral_tendsto_of_countably_generated hfm) htendsto

/--
theorem `AECover.iSup_lintegral_eq_of_countably_generated` / 定理 `AECover.iSup_lintegral_eq_of_countably_generated`

English:
theorem AECover.iSup_lintegral_eq_of_countably_generated
  statement: [Nonempty ι] [l.NeBot]
  proof: by
  have := hφ.lintegral_tendsto_of_countably_generated hfm
  refine ciSup_eq_of_forall_le_of_forall_lt_exists_gt
    (fun i => lintegral_mono' Measure.restrict_le_self le_rfl) fun w hw => ?_
  exact (this.eventually_const_lt hw).exists

中文:
定理 AECover.iSup_lintegral_eq_of_countably_generated
  结论: [非空 ι] [l.NeBot]
  证明: by
  have := hφ.lintegral_tendsto_of_countably_generated hfm
  refine ciSup_eq_of_forall_le_of_forall_lt_exists_gt
    (fun i => lintegral_mono' Measure.restrict_le_self le_rfl) fun w hw => ?_
  exact (this.eventually_const_lt hw).exists

Depends on / 依赖: Measure, Measure.restrict_le_self, ciSup_eq_of_forall_le_of_forall_lt_exists_gt, eventually_const_lt, le_rfl, lintegral_mono, lintegral_tendsto_of_countably_generated, restrict_le_self, this.eventually_const_lt
-/
theorem AECover.iSup_lintegral_eq_of_countably_generated [Nonempty ι] [l.NeBot]
    [l.IsCountablyGenerated] {φ : ι -> Set α} (hφ : AECover μ l φ) {f : α -> Real>=0∞}
    (hfm : AEMeasurable f μ) : ⨆ i : ι, ∫⁻ x in φ i, f x ∂μ = ∫⁻ x, f x ∂μ := by
  have := hφ.lintegral_tendsto_of_countably_generated hfm
  refine ciSup_eq_of_forall_le_of_forall_lt_exists_gt
    (fun i => lintegral_mono' Measure.restrict_le_self le_rfl) fun w hw => ?_
  exact (this.eventually_const_lt hw).exists

end Lintegral

section Integrable

variable {α ι E : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} [NormedAddCommGroup E]

/--
theorem `AECover.integrable_of_lintegral_enorm_bounded` / 定理 `AECover.integrable_of_lintegral_enorm_bounded`

English:
theorem AECover.integrable_of_lintegral_enorm_bounded
  statement: [l.NeBot] [l.IsCountablyGenerated]
  proof: by
  refine ⟨hfm, (le_of_tendsto ?_ hbounded).trans_lt ENNReal.ofReal_lt_top⟩
  exact hφ.lintegral_tendsto_of_countably_generated hfm.enorm

中文:
定理 AECover.integrable_of_lintegral_enorm_bounded
  结论: [l.NeBot] [l.是余untablyGenerated]
  证明: by
  refine ⟨hfm, (le_of_tendsto ?_ hbounded).trans_lt ENNReal.ofReal_lt_top⟩
  exact hφ.lintegral_tendsto_of_countably_generated hfm.enorm

Depends on / 依赖: ENNReal, ENNReal.ofReal_lt_top, hbounded, hfm.enorm, le_of_tendsto, lintegral_tendsto_of_countably_generated, ofReal_lt_top, trans_lt
-/
theorem AECover.integrable_of_lintegral_enorm_bounded [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι -> Set α} (hφ : AECover μ l φ) {f : α -> E} (I : Real) (hfm : AEStronglyMeasurable f μ)
    (hbounded : forallᶠ i in l, ∫⁻ x in φ i, ‖f x‖ₑ ∂μ <= ENNReal.ofReal I) : Integrable f μ := by
  refine ⟨hfm, (le_of_tendsto ?_ hbounded).trans_lt ENNReal.ofReal_lt_top⟩
  exact hφ.lintegral_tendsto_of_countably_generated hfm.enorm

/--
theorem `AECover.integrable_of_lintegral_enorm_tendsto` / 定理 `AECover.integrable_of_lintegral_enorm_tendsto`

English:
theorem AECover.integrable_of_lintegral_enorm_tendsto
  statement: [l.NeBot] [l.IsCountablyGenerated]
  proof: by
  refine hφ.integrable_of_lintegral_enorm_bounded (max 1 (I + 1)) hfm ?_
  refine htendsto.eventually (ge_mem_nhds ?_)
  refine (ENNReal.ofReal_lt_ofReal_iff (lt_max_of_lt_left zero_lt_one)).2 ?_
  exact lt_max_of_lt_right (lt_add_one I)

中文:
定理 AECover.integrable_of_lintegral_enorm_tendsto
  结论: [l.NeBot] [l.是余untablyGenerated]
  证明: by
  refine hφ.integrable_of_lintegral_enorm_bounded (max 1 (I + 1)) hfm ?_
  refine htendsto.eventually (ge_mem_nhds ?_)
  refine (ENNReal.ofReal_lt_ofReal_iff (lt_max_of_lt_left zero_lt_one)).2 ?_
  exact lt_max_of_lt_right (lt_add_one I)

Depends on / 依赖: ENNReal, ENNReal.ofReal_lt_ofReal_iff, eventually, ge_mem_nhds, htendsto, htendsto.eventually, integrable_of_lintegral_enorm_bounded, lt_add_one, lt_max_of_lt_left, lt_max_of_lt_right, ofReal_lt_ofReal_iff, zero_lt_one
-/
theorem AECover.integrable_of_lintegral_enorm_tendsto [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι -> Set α} (hφ : AECover μ l φ) {f : α -> E} (I : Real) (hfm : AEStronglyMeasurable f μ)
    (htendsto : Tendsto (fun i => ∫⁻ x in φ i, ‖f x‖ₑ ∂μ) l (𝓝 <| .ofReal I)) :
    Integrable f μ := by
  refine hφ.integrable_of_lintegral_enorm_bounded (max 1 (I + 1)) hfm ?_
  refine htendsto.eventually (ge_mem_nhds ?_)
  refine (ENNReal.ofReal_lt_ofReal_iff (lt_max_of_lt_left zero_lt_one)).2 ?_
  exact lt_max_of_lt_right (lt_add_one I)

/--
theorem `AECover.integrable_of_lintegral_enorm_bounded'` / 定理 `AECover.integrable_of_lintegral_enorm_bounded'`

English:
theorem AECover.integrable_of_lintegral_enorm_bounded'
  statement: [l.NeBot] [l.IsCountablyGenerated]
  proof: hφ.integrable_of_lintegral_enorm_bounded I hfm
    (by simpa only [ENNReal.ofReal_coe_nnreal] using hbounded)

中文:
定理 AECover.integrable_of_lintegral_enorm_bounded'
  结论: [l.NeBot] [l.是余untablyGenerated]
  证明: hφ.integrable_of_lintegral_enorm_bounded I hfm
    (by simpa only [ENNReal.ofReal_coe_nnreal] using hbounded)

Depends on / 依赖: ENNReal, ENNReal.ofReal_coe_nnreal, hbounded, integrable_of_lintegral_enorm_bounded, ofReal_coe_nnreal
-/
theorem AECover.integrable_of_lintegral_enorm_bounded' [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι -> Set α} (hφ : AECover μ l φ) {f : α -> E} (I : Real>=0) (hfm : AEStronglyMeasurable f μ)
    (hbounded : forallᶠ i in l, ∫⁻ x in φ i, ‖f x‖ₑ ∂μ <= I) : Integrable f μ :=
  hφ.integrable_of_lintegral_enorm_bounded I hfm
    (by simpa only [ENNReal.ofReal_coe_nnreal] using hbounded)

/--
theorem `AECover.integrable_of_lintegral_enorm_tendsto'` / 定理 `AECover.integrable_of_lintegral_enorm_tendsto'`

English:
theorem AECover.integrable_of_lintegral_enorm_tendsto'
  statement: [l.NeBot] [l.IsCountablyGenerated]
  proof: hφ.integrable_of_lintegral_enorm_tendsto I hfm
    (by simpa only [ENNReal.ofReal_coe_nnreal] using htendsto)

中文:
定理 AECover.integrable_of_lintegral_enorm_tendsto'
  结论: [l.NeBot] [l.是余untablyGenerated]
  证明: hφ.integrable_of_lintegral_enorm_tendsto I hfm
    (by simpa only [ENNReal.ofReal_coe_nnreal] using htendsto)

Depends on / 依赖: ENNReal, ENNReal.ofReal_coe_nnreal, htendsto, integrable_of_lintegral_enorm_tendsto, ofReal_coe_nnreal
-/
theorem AECover.integrable_of_lintegral_enorm_tendsto' [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι -> Set α} (hφ : AECover μ l φ) {f : α -> E} (I : Real>=0) (hfm : AEStronglyMeasurable f μ)
    (htendsto : Tendsto (fun i => ∫⁻ x in φ i, ‖f x‖ₑ ∂μ) l (𝓝 I)) : Integrable f μ :=
  hφ.integrable_of_lintegral_enorm_tendsto I hfm
    (by simpa only [ENNReal.ofReal_coe_nnreal] using htendsto)

/--
theorem `AECover.integrable_of_integral_norm_bounded` / 定理 `AECover.integrable_of_integral_norm_bounded`

English:
theorem AECover.integrable_of_integral_norm_bounded
  statement: [l.NeBot] [l.IsCountablyGenerated]
  proof: by
  have hfm : AEStronglyMeasurable f μ :=
    hφ.aestronglyMeasurable fun i => (hfi i).aestronglyMeasurable
  refine hφ.integrable_of_lintegral_enorm_bounded I hfm ?_
  conv at hbounded in integral _ _ =>
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => @norm_nonneg E _ (f x))
    

中文:
定理 AECover.integrable_of_integral_norm_bounded
  结论: [l.NeBot] [l.是余untablyGenerated]
  证明: by
  have hfm : AEStronglyMeasurable f μ :=
    hφ.aestronglyMeasurable fun i => (hfi i).aestronglyMeasurable
  refine hφ.integrable_of_lintegral_enorm_bounded I hfm ?_
  conv at hbounded in integral _ _ =>
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => @norm_nonneg E _ (f x))
    

Depends on / 依赖: AEStronglyMeasurable, ENNReal, ENNReal.ofReal, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal, ae_of_all, aestronglyMeasurable, coe_nnnorm, hasFiniteIntegral_iff_enor, hbounded, hbounded.mono, hfm.norm.restrict, integrable_of_lintegral_enorm_bounded, integral, integral_eq_lintegral_of_nonneg_ae, ne_top_of_lt, norm_nonneg, ofReal, ofReal_coe_nnreal, ofReal_toReal
-/
theorem AECover.integrable_of_integral_norm_bounded [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι -> Set α} (hφ : AECover μ l φ) {f : α -> E} (I : Real) (hfi : forall i, IntegrableOn f (φ i) μ)
    (hbounded : forallᶠ i in l, (∫ x in φ i, ‖f x‖ ∂μ) <= I) : Integrable f μ := by
  have hfm : AEStronglyMeasurable f μ :=
    hφ.aestronglyMeasurable fun i => (hfi i).aestronglyMeasurable
  refine hφ.integrable_of_lintegral_enorm_bounded I hfm ?_
  conv at hbounded in integral _ _ =>
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => @norm_nonneg E _ (f x))
        hfm.norm.restrict]
  conv at hbounded in ENNReal.ofReal _ =>
    rw [← coe_nnnorm]; rw [ENNReal.ofReal_coe_nnreal]
  refine hbounded.mono fun i hi => ?_
  rw [← ENNReal.ofReal_toReal <| ne_top_of_lt <| hasFiniteIntegral_iff_enorm.mp (hfi i).2]
  apply ENNReal.ofReal_le_ofReal hi

/--
theorem `AECover.integrable_of_integral_norm_tendsto` / 定理 `AECover.integrable_of_integral_norm_tendsto`

English:
theorem AECover.integrable_of_integral_norm_tendsto
  statement: [l.NeBot] [l.IsCountablyGenerated]
  proof: let ⟨I', hI'⟩ := htendsto.isBoundedUnder_le
  hφ.integrable_of_integral_norm_bounded I' hfi hI'

中文:
定理 AECover.integrable_of_integral_norm_tendsto
  结论: [l.NeBot] [l.是余untablyGenerated]
  证明: let ⟨I', hI'⟩ := htendsto.isBoundedUnder_le
  hφ.integrable_of_integral_norm_bounded I' hfi hI'

Depends on / 依赖: btw_total, htendsto, htendsto.isBoundedUnder_le, integrable_of_integral_norm_bounded, isBoundedUnder_le
-/
theorem AECover.integrable_of_integral_norm_tendsto [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι -> Set α} (hφ : AECover μ l φ) {f : α -> E} (I : Real) (hfi : forall i, IntegrableOn f (φ i) μ)
    (htendsto : Tendsto (fun i => ∫ x in φ i, ‖f x‖ ∂μ) l (𝓝 I)) : Integrable f μ :=
  let ⟨I', hI'⟩ := htendsto.isBoundedUnder_le
  hφ.integrable_of_integral_norm_bounded I' hfi hI'

/--
theorem `AECover.integrable_of_integral_bounded_of_nonneg_ae` / 定理 `AECover.integrable_of_integral_bounded_of_nonneg_ae`

English:
theorem AECover.integrable_of_integral_bounded_of_nonneg_ae
  statement: [l.NeBot] [l.IsCountablyGenerated]
  proof: hφ.integrable_of_integral_norm_bounded I hfi hbounded.mono fun _i hi =>
    (integral_congr_ae <| ae_restrict_of_ae <| hnng.mono fun _ => Real.norm_of_nonneg).le.trans hi

中文:
定理 AECover.integrable_of_integral_bounded_of_nonneg_ae
  结论: [l.NeBot] [l.是余untablyGenerated]
  证明: hφ.integrable_of_integral_norm_bounded I hfi hbounded.mono fun _i hi =>
    (integral_congr_ae <| ae_restrict_of_ae <| hnng.mono fun _ => Real.norm_of_nonneg).le.trans hi

Depends on / 依赖: Real.norm_of_nonneg, ae_restrict_of_ae, hbounded, hbounded.mono, hnng.mono, integrable_of_integral_norm_bounded, integral_congr_ae, le.trans, norm_of_nonneg
-/
theorem AECover.integrable_of_integral_bounded_of_nonneg_ae [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι -> Set α} (hφ : AECover μ l φ) {f : α -> Real} (I : Real) (hfi : forall i, IntegrableOn f (φ i) μ)
    (hnng : forallᵐ x ∂μ, 0 <= f x) (hbounded : forallᶠ i in l, (∫ x in φ i, f x ∂μ) <= I) : Integrable f μ :=
hφ.integrable_of_integral_norm_bounded I hfi hbounded.mono fun _i hi =>
    (integral_congr_ae <| ae_restrict_of_ae <| hnng.mono fun _ => Real.norm_of_nonneg).le.trans hi

/--
theorem `AECover.integrable_of_integral_tendsto_of_nonneg_ae` / 定理 `AECover.integrable_of_integral_tendsto_of_nonneg_ae`

English:
theorem AECover.integrable_of_integral_tendsto_of_nonneg_ae
  statement: [l.NeBot] [l.IsCountablyGenerated]
  proof: let ⟨I', hI'⟩ := htendsto.isBoundedUnder_le
  hφ.integrable_of_integral_bounded_of_nonneg_ae I' hfi hnng hI'

中文:
定理 AECover.integrable_of_integral_tendsto_of_nonneg_ae
  结论: [l.NeBot] [l.是余untablyGenerated]
  证明: let ⟨I', hI'⟩ := htendsto.isBoundedUnder_le
  hφ.integrable_of_integral_bounded_of_nonneg_ae I' hfi hnng hI'

Depends on / 依赖: htendsto, htendsto.isBoundedUnder_le, integrable_of_integral_bounded_of_nonneg_ae, isBoundedUnder_le
-/
theorem AECover.integrable_of_integral_tendsto_of_nonneg_ae [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι -> Set α} (hφ : AECover μ l φ) {f : α -> Real} (I : Real) (hfi : forall i, IntegrableOn f (φ i) μ)
    (hnng : forallᵐ x ∂μ, 0 <= f x) (htendsto : Tendsto (fun i => ∫ x in φ i, f x ∂μ) l (𝓝 I)) :
    Integrable f μ :=
  let ⟨I', hI'⟩ := htendsto.isBoundedUnder_le
  hφ.integrable_of_integral_bounded_of_nonneg_ae I' hfi hnng hI'

end Integrable

section Integral

variable {α ι E : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} [NormedAddCommGroup E]
  [NormedSpace Real E]

/--
theorem `AECover.integral_tendsto_of_countably_generated` / 定理 `AECover.integral_tendsto_of_countably_generated`

English:
theorem AECover.integral_tendsto_of_countably_generated
  statement: [l.IsCountablyGenerated] {φ : ι -> Set α}
  proof: suffices h : Tendsto (fun i => ∫ x : α, (φ i).indicator f x ∂μ) l (𝓝 (∫ x : α, f x ∂μ)) from by
    convert! h using 2; rw [integral_indicator (hφ.measurableSet _)]
  tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
    (Eventually.of_forall fun i => hfi.aestronglyMeasurable.indicat

中文:
定理 AECover.integral_tendsto_of_countably_generated
  结论: [l.是余untablyGenerated] {φ : ι -> 集合 α}
  证明: suffices h : Tendsto (fun i => ∫ x : α, (φ i).indicator f x ∂μ) l (𝓝 (∫ x : α, f x ∂μ)) from by
    convert! h using 2; rw [integral_indicator (hφ.measurableSet _)]
  tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
    (Eventually.of_forall fun i => hfi.aestronglyMeasurable.indicat

Depends on / 依赖: Eventually, Eventually.of_forall, Tendsto, ae_of_all, ae_tendsto_indicator, aestronglyMeasurable, convert, hfi.aestronglyMeasurable.indicator, hfi.norm, indicator, integral_indicator, measurableSet, norm_indicator_le_norm_self, of_forall, tendsto_integral_filter_of_dominated_convergence
-/
theorem AECover.integral_tendsto_of_countably_generated [l.IsCountablyGenerated] {φ : ι -> Set α}
    (hφ : AECover μ l φ) {f : α -> E} (hfi : Integrable f μ) :
    Tendsto (fun i => ∫ x in φ i, f x ∂μ) l (𝓝 <| ∫ x, f x ∂μ) :=
  suffices h : Tendsto (fun i => ∫ x : α, (φ i).indicator f x ∂μ) l (𝓝 (∫ x : α, f x ∂μ)) from by
    convert! h using 2; rw [integral_indicator (hφ.measurableSet _)]
  tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
    (Eventually.of_forall fun i => hfi.aestronglyMeasurable.indicator <| hφ.measurableSet i)
    (Eventually.of_forall fun _ => ae_of_all _ fun _ => norm_indicator_le_norm_self _ _) hfi.norm
    (hφ.ae_tendsto_indicator f)

/--
theorem `AECover.integral_eq_of_tendsto` / 定理 `AECover.integral_eq_of_tendsto`

English:
theorem AECover.integral_eq_of_tendsto
  statement: [l.NeBot] [l.IsCountablyGenerated] {φ : ι -> Set α}
  proof: tendsto_nhds_unique (hφ.integral_tendsto_of_countably_generated hfi) h

中文:
定理 AECover.integral_eq_of_tendsto
  结论: [l.NeBot] [l.是余untablyGenerated] {φ : ι -> 集合 α}
  证明: tendsto_nhds_unique (hφ.integral_tendsto_of_countably_generated hfi) h

Depends on / 依赖: integral_tendsto_of_countably_generated, tendsto_nhds_unique
-/
theorem AECover.integral_eq_of_tendsto [l.NeBot] [l.IsCountablyGenerated] {φ : ι -> Set α}
    (hφ : AECover μ l φ) {f : α -> E} (I : E) (hfi : Integrable f μ)
    (h : Tendsto (fun n => ∫ x in φ n, f x ∂μ) l (𝓝 I)) : ∫ x, f x ∂μ = I :=
  tendsto_nhds_unique (hφ.integral_tendsto_of_countably_generated hfi) h

/--
theorem `AECover.integral_eq_of_tendsto_of_nonneg_ae` / 定理 `AECover.integral_eq_of_tendsto_of_nonneg_ae`

English:
theorem AECover.integral_eq_of_tendsto_of_nonneg_ae
  statement: [l.NeBot] [l.IsCountablyGenerated]
  proof: have hfi' : Integrable f μ := hφ.integrable_of_integral_tendsto_of_nonneg_ae I hfi hnng htendsto
  hφ.integral_eq_of_tendsto I hfi' htendsto

中文:
定理 AECover.integral_eq_of_tendsto_of_nonneg_ae
  结论: [l.NeBot] [l.是余untablyGenerated]
  证明: have hfi' : Integrable f μ := hφ.integrable_of_integral_tendsto_of_nonneg_ae I hfi hnng htendsto
  hφ.integral_eq_of_tendsto I hfi' htendsto

Depends on / 依赖: Integrable, htendsto, integrable_of_integral_tendsto_of_nonneg_ae, integral_eq_of_tendsto
-/
theorem AECover.integral_eq_of_tendsto_of_nonneg_ae [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι -> Set α} (hφ : AECover μ l φ) {f : α -> Real} (I : Real) (hnng : 0 <=ᵐ[μ] f)
    (hfi : forall n, IntegrableOn f (φ n) μ) (htendsto : Tendsto (fun n => ∫ x in φ n, f x ∂μ) l (𝓝 I)) :
    ∫ x, f x ∂μ = I :=
  have hfi' : Integrable f μ := hφ.integrable_of_integral_tendsto_of_nonneg_ae I hfi hnng htendsto
  hφ.integral_eq_of_tendsto I hfi' htendsto

end Integral

section IntegrableOfIntervalIntegral

variable {ι E : Type*} {μ : Measure Real} {l : Filter ι} [Filter.NeBot l] [IsCountablyGenerated l]
  [NormedAddCommGroup E] {a b : ι -> Real} {f : Real -> E}

/--
theorem `integrable_of_intervalIntegral_norm_bounded` / 定理 `integrable_of_intervalIntegral_norm_bounded`

English:
theorem integrable_of_intervalIntegral_norm_bounded
  statement: (I : Real)
  proof: by
  have hφ : AECover μ l _ := aecover_Ioc ha hb
  refine hφ.integrable_of_integral_norm_bounded I hfi (h.mp ?_)
  filter_upwards [ha.eventually (eventually_le_atBot 0),
    hb.eventually (eventually_ge_atTop 0)] with i hai hbi ht
  rwa [← intervalIntegral.integral_of_le (hai.trans hbi)]

中文:
定理 integrable_of_interval整数egral_norm_bounded
  结论: (I : 实数)
  证明: by
  have hφ : AECover μ l _ := aecover_Ioc ha hb
  refine hφ.integrable_of_integral_norm_bounded I hfi (h.mp ?_)
  filter_upwards [ha.eventually (eventually_le_atBot 0),
    hb.eventually (eventually_ge_atTop 0)] with i hai hbi ht
  rwa [← intervalIntegral.integral_of_le (hai.trans hbi)]

Depends on / 依赖: AECover, aecover_Ioc, eventually, eventually_ge_atTop, eventually_le_atBot, filter_upwards, h.mp, ha.eventually, hai.trans, hb.eventually, integrable_of_integral_norm_bounded, integral_of_le, intervalIntegral, intervalIntegral.integral_of_le
-/
theorem integrable_of_intervalIntegral_norm_bounded (I : Real)
    (hfi : forall i, IntegrableOn f (Ioc (a i) (b i)) μ) (ha : Tendsto a l atBot)
    (hb : Tendsto b l atTop) (h : forallᶠ i in l, (∫ x in a i..b i, ‖f x‖ ∂μ) <= I) : Integrable f μ := by
  have hφ : AECover μ l _ := aecover_Ioc ha hb
  refine hφ.integrable_of_integral_norm_bounded I hfi (h.mp ?_)
  filter_upwards [ha.eventually (eventually_le_atBot 0),
    hb.eventually (eventually_ge_atTop 0)] with i hai hbi ht
  rwa [← intervalIntegral.integral_of_le (hai.trans hbi)]

/--
theorem `integrable_of_intervalIntegral_norm_tendsto` / 定理 `integrable_of_intervalIntegral_norm_tendsto`

English:
theorem integrable_of_intervalIntegral_norm_tendsto
  statement: (I : Real)
  proof: let ⟨I', hI'⟩ := h.isBoundedUnder_le
  integrable_of_intervalIntegral_norm_bounded I' hfi ha hb hI'

中文:
定理 integrable_of_interval整数egral_norm_tendsto
  结论: (I : 实数)
  证明: let ⟨I', hI'⟩ := h.isBoundedUnder_le
  integrable_of_intervalIntegral_norm_bounded I' hfi ha hb hI'

Depends on / 依赖: h.isBoundedUnder_le, integrable_of_intervalIntegral_norm_bounded, isBoundedUnder_le
-/
theorem integrable_of_intervalIntegral_norm_tendsto (I : Real)
    (hfi : forall i, IntegrableOn f (Ioc (a i) (b i)) μ) (ha : Tendsto a l atBot)
    (hb : Tendsto b l atTop) (h : Tendsto (fun i => ∫ x in a i..b i, ‖f x‖ ∂μ) l (𝓝 I)) :
    Integrable f μ :=
  let ⟨I', hI'⟩ := h.isBoundedUnder_le
  integrable_of_intervalIntegral_norm_bounded I' hfi ha hb hI'

/--
theorem `integrableOn_Iic_of_intervalIntegral_norm_bounded` / 定理 `integrableOn_Iic_of_intervalIntegral_norm_bounded`

English:
theorem integrableOn_Iic_of_intervalIntegral_norm_bounded
  statement: (I b : Real)
  proof: by
  have hφ : AECover (μ.restrict <| Iic b) l _ := aecover_Ioi ha
  have hfi : forall i, IntegrableOn f (Ioi (a i)) (μ.restrict <| Iic b) := by
    intro i
    rw [IntegrableOn]; rw [Measure.restrict_restrict (hφ.measurableSet i)]
    exact hfi i
  refine hφ.integrable_of_integral_norm_bounded I hf

中文:
定理 integrableOn_Iic_of_interval整数egral_norm_bounded
  结论: (I b : 实数)
  证明: by
  have hφ : AECover (μ.restrict <| Iic b) l _ := aecover_Ioi ha
  have hfi : forall i, IntegrableOn f (Ioi (a i)) (μ.restrict <| Iic b) := by
    intro i
    rw [IntegrableOn]; rw [Measure.restrict_restrict (hφ.measurableSet i)]
    exact hfi i
  refine hφ.integrable_of_integral_norm_bounded I hf

Depends on / 依赖: AECover, IntegrableOn, Measure, Measure.restrict_restrict, aecover_Ioi, eventually, eventually_le_atBot, filter_upwards, h.mp, ha.eventually, integrable_of_integral_norm_bounded, integral_of_le, intervalIntegral, intervalIntegral.integral_of_le, measurableSet, restrict, restrict_restrict
-/
theorem integrableOn_Iic_of_intervalIntegral_norm_bounded (I b : Real)
    (hfi : forall i, IntegrableOn f (Ioc (a i) b) μ) (ha : Tendsto a l atBot)
    (h : forallᶠ i in l, (∫ x in a i..b, ‖f x‖ ∂μ) <= I) : IntegrableOn f (Iic b) μ := by
  have hφ : AECover (μ.restrict <| Iic b) l _ := aecover_Ioi ha
  have hfi : forall i, IntegrableOn f (Ioi (a i)) (μ.restrict <| Iic b) := by
    intro i
    rw [IntegrableOn]; rw [Measure.restrict_restrict (hφ.measurableSet i)]
    exact hfi i
  refine hφ.integrable_of_integral_norm_bounded I hfi (h.mp ?_)
  filter_upwards [ha.eventually (eventually_le_atBot b)] with i hai
  rw [intervalIntegral.integral_of_le hai]; rw [Measure.restrict_restrict (hφ.measurableSet i)]
  exact id

/--
theorem `integrableOn_Iic_of_intervalIntegral_norm_tendsto` / 定理 `integrableOn_Iic_of_intervalIntegral_norm_tendsto`

English:
theorem integrableOn_Iic_of_intervalIntegral_norm_tendsto
  statement: (I b : Real)
  proof: let ⟨I', hI'⟩ := h.isBoundedUnder_le
  integrableOn_Iic_of_intervalIntegral_norm_bounded I' b hfi ha hI'

中文:
定理 integrableOn_Iic_of_interval整数egral_norm_tendsto
  结论: (I b : 实数)
  证明: let ⟨I', hI'⟩ := h.isBoundedUnder_le
  integrableOn_Iic_of_intervalIntegral_norm_bounded I' b hfi ha hI'

Depends on / 依赖: h.isBoundedUnder_le, integrableOn_Iic_of_intervalIntegral_norm_bounded, isBoundedUnder_le
-/
theorem integrableOn_Iic_of_intervalIntegral_norm_tendsto (I b : Real)
    (hfi : forall i, IntegrableOn f (Ioc (a i) b) μ) (ha : Tendsto a l atBot)
    (h : Tendsto (fun i => ∫ x in a i..b, ‖f x‖ ∂μ) l (𝓝 I)) : IntegrableOn f (Iic b) μ :=
  let ⟨I', hI'⟩ := h.isBoundedUnder_le
  integrableOn_Iic_of_intervalIntegral_norm_bounded I' b hfi ha hI'

/--
theorem `integrableOn_Ioi_of_intervalIntegral_norm_bounded` / 定理 `integrableOn_Ioi_of_intervalIntegral_norm_bounded`

English:
theorem integrableOn_Ioi_of_intervalIntegral_norm_bounded
  statement: (I a : Real)
  proof: by
  have hφ : AECover (μ.restrict <| Ioi a) l _ := aecover_Iic hb
  have hfi : forall i, IntegrableOn f (Iic (b i)) (μ.restrict <| Ioi a) := by
    intro i
    rw [IntegrableOn]; rw [Measure.restrict_restrict (hφ.measurableSet i)]; rw [inter_comm]
    exact hfi i
  refine hφ.integrable_of_integral_

中文:
定理 integrableOn_Ioi_of_interval整数egral_norm_bounded
  结论: (I a : 实数)
  证明: by
  have hφ : AECover (μ.restrict <| Ioi a) l _ := aecover_Iic hb
  have hfi : forall i, IntegrableOn f (Iic (b i)) (μ.restrict <| Ioi a) := by
    intro i
    rw [IntegrableOn]; rw [Measure.restrict_restrict (hφ.measurableSet i)]; rw [inter_comm]
    exact hfi i
  refine hφ.integrable_of_integral_

Depends on / 依赖: AECover, IntegrableOn, Measure, Measure.restrict_restrict, aecover_Iic, eventually, eventually_ge_atTop, filter_upwards, h.mp, hb.eventually, integrable_of_integral_norm_bounded, integral_of_le, inter_comm, intervalIntegral, intervalIntegral.integral_of_le, measurableSet, restrict, restrict_restrict
-/
theorem integrableOn_Ioi_of_intervalIntegral_norm_bounded (I a : Real)
    (hfi : forall i, IntegrableOn f (Ioc a (b i)) μ) (hb : Tendsto b l atTop)
    (h : forallᶠ i in l, (∫ x in a..b i, ‖f x‖ ∂μ) <= I) : IntegrableOn f (Ioi a) μ := by
  have hφ : AECover (μ.restrict <| Ioi a) l _ := aecover_Iic hb
  have hfi : forall i, IntegrableOn f (Iic (b i)) (μ.restrict <| Ioi a) := by
    intro i
    rw [IntegrableOn]; rw [Measure.restrict_restrict (hφ.measurableSet i)]; rw [inter_comm]
    exact hfi i
  refine hφ.integrable_of_integral_norm_bounded I hfi (h.mp ?_)
  filter_upwards [hb.eventually (eventually_ge_atTop a)] with i hbi
  rw [intervalIntegral.integral_of_le hbi]; rw [Measure.restrict_restrict (hφ.measurableSet i)]; rw [inter_comm]
  exact id

/--
theorem `integrableOn_Ioi_of_intervalIntegral_norm_tendsto` / 定理 `integrableOn_Ioi_of_intervalIntegral_norm_tendsto`

English:
theorem integrableOn_Ioi_of_intervalIntegral_norm_tendsto
  statement: (I a : Real)
  proof: let ⟨I', hI'⟩ := h.isBoundedUnder_le
  integrableOn_Ioi_of_intervalIntegral_norm_bounded I' a hfi hb hI'

中文:
定理 integrableOn_Ioi_of_interval整数egral_norm_tendsto
  结论: (I a : 实数)
  证明: let ⟨I', hI'⟩ := h.isBoundedUnder_le
  integrableOn_Ioi_of_intervalIntegral_norm_bounded I' a hfi hb hI'

Depends on / 依赖: h.isBoundedUnder_le, integrableOn_Ioi_of_intervalIntegral_norm_bounded, isBoundedUnder_le
-/
theorem integrableOn_Ioi_of_intervalIntegral_norm_tendsto (I a : Real)
    (hfi : forall i, IntegrableOn f (Ioc a (b i)) μ) (hb : Tendsto b l atTop)
    (h : Tendsto (fun i => ∫ x in a..b i, ‖f x‖ ∂μ) l (𝓝 <| I)) : IntegrableOn f (Ioi a) μ :=
  let ⟨I', hI'⟩ := h.isBoundedUnder_le
  integrableOn_Ioi_of_intervalIntegral_norm_bounded I' a hfi hb hI'

/--
theorem `integrableOn_Ioc_of_intervalIntegral_norm_bounded` / 定理 `integrableOn_Ioc_of_intervalIntegral_norm_bounded`

English:
theorem integrableOn_Ioc_of_intervalIntegral_norm_bounded
  statement: {I a₀ b₀ : Real}
  proof: by
  refine (aecover_Ioc_of_Ioc ha hb).integrable_of_integral_norm_bounded I
    (fun i => (hfi i).restrict) (h.mono fun i hi => ?_)
  rw [Measure.restrict_restrict measurableSet_Ioc]
  grw [← hi]
  gcongr
  · apply ae_of_all
    simp
  · exact (hfi i).norm
  · exact inter_subset_left

中文:
定理 integrableOn_Ioc_of_interval整数egral_norm_bounded
  结论: {I a₀ b₀ : 实数}
  证明: by
  refine (aecover_Ioc_of_Ioc ha hb).integrable_of_integral_norm_bounded I
    (fun i => (hfi i).restrict) (h.mono fun i hi => ?_)
  rw [Measure.restrict_restrict measurableSet_Ioc]
  grw [← hi]
  gcongr
  · apply ae_of_all
    simp
  · exact (hfi i).norm
  · exact inter_subset_left

Depends on / 依赖: Measure, Measure.restrict_restrict, ae_of_all, aecover_Ioc_of_Ioc, h.mono, integrable_of_integral_norm_bounded, inter_subset_left, measurableSet_Ioc, restrict, restrict_restrict
-/
theorem integrableOn_Ioc_of_intervalIntegral_norm_bounded {I a₀ b₀ : Real}
    (hfi : forall i, IntegrableOn f <| Ioc (a i) (b i)) (ha : Tendsto a l <| 𝓝 a₀)
    (hb : Tendsto b l <| 𝓝 b₀) (h : forallᶠ i in l, (∫ x in Ioc (a i) (b i), ‖f x‖) <= I) :
    IntegrableOn f (Ioc a₀ b₀) := by
  refine (aecover_Ioc_of_Ioc ha hb).integrable_of_integral_norm_bounded I
    (fun i => (hfi i).restrict) (h.mono fun i hi => ?_)
  rw [Measure.restrict_restrict measurableSet_Ioc]
  grw [← hi]
  gcongr
  · apply ae_of_all
    simp
  · exact (hfi i).norm
  · exact inter_subset_left

/--
theorem `integrableOn_Ioc_of_intervalIntegral_norm_bounded_left` / 定理 `integrableOn_Ioc_of_intervalIntegral_norm_bounded_left`

English:
theorem integrableOn_Ioc_of_intervalIntegral_norm_bounded_left
  statement: {I a₀ b : Real}
  proof: integrableOn_Ioc_of_intervalIntegral_norm_bounded hfi ha tendsto_const_nhds h

中文:
定理 integrableOn_Ioc_of_interval整数egral_norm_bounded_left
  结论: {I a₀ b : 实数}
  证明: integrableOn_Ioc_of_intervalIntegral_norm_bounded hfi ha tendsto_const_nhds h

Depends on / 依赖: integrableOn_Ioc_of_intervalIntegral_norm_bounded, tendsto_const_nhds
-/
theorem integrableOn_Ioc_of_intervalIntegral_norm_bounded_left {I a₀ b : Real}
    (hfi : forall i, IntegrableOn f <| Ioc (a i) b) (ha : Tendsto a l <| 𝓝 a₀)
    (h : forallᶠ i in l, (∫ x in Ioc (a i) b, ‖f x‖) <= I) : IntegrableOn f (Ioc a₀ b) :=
  integrableOn_Ioc_of_intervalIntegral_norm_bounded hfi ha tendsto_const_nhds h

/--
theorem `integrableOn_Ioc_of_intervalIntegral_norm_bounded_right` / 定理 `integrableOn_Ioc_of_intervalIntegral_norm_bounded_right`

English:
theorem integrableOn_Ioc_of_intervalIntegral_norm_bounded_right
  statement: {I a b₀ : Real}
  proof: integrableOn_Ioc_of_intervalIntegral_norm_bounded hfi tendsto_const_nhds hb h

中文:
定理 integrableOn_Ioc_of_interval整数egral_norm_bounded_right
  结论: {I a b₀ : 实数}
  证明: integrableOn_Ioc_of_intervalIntegral_norm_bounded hfi tendsto_const_nhds hb h

Depends on / 依赖: integrableOn_Ioc_of_intervalIntegral_norm_bounded, tendsto_const_nhds
-/
theorem integrableOn_Ioc_of_intervalIntegral_norm_bounded_right {I a b₀ : Real}
    (hfi : forall i, IntegrableOn f <| Ioc a (b i)) (hb : Tendsto b l <| 𝓝 b₀)
    (h : forallᶠ i in l, (∫ x in Ioc a (b i), ‖f x‖) <= I) : IntegrableOn f (Ioc a b₀) :=
  integrableOn_Ioc_of_intervalIntegral_norm_bounded hfi tendsto_const_nhds hb h

end IntegrableOfIntervalIntegral

section IntegralOfIntervalIntegral

variable {ι E : Type*} {μ : Measure Real} {l : Filter ι} [IsCountablyGenerated l]
  [NormedAddCommGroup E] [NormedSpace Real E] {a b : ι -> Real} {f : Real -> E}

/--
theorem `intervalIntegral_tendsto_integral` / 定理 `intervalIntegral_tendsto_integral`

English:
theorem intervalIntegral_tendsto_integral
  statement: (hfi : Integrable f μ) (ha : Tendsto a l atBot)
  proof: by
  let φ i := Ioc (a i) (b i)
  have hφ : AECover μ l φ := aecover_Ioc ha hb
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' ?_
  filter_upwards [ha.eventually (eventually_le_atBot 0),
    hb.eventually (eventually_ge_atTop 0)] with i hai hbi
  exact (intervalIntegral.integral_of_

中文:
定理 interval整数egral_tendsto_integral
  结论: (hfi : 可积 f μ) (ha : 收敛 a l atBot)
  证明: by
  let φ i := Ioc (a i) (b i)
  have hφ : AECover μ l φ := aecover_Ioc ha hb
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' ?_
  filter_upwards [ha.eventually (eventually_le_atBot 0),
    hb.eventually (eventually_ge_atTop 0)] with i hai hbi
  exact (intervalIntegral.integral_of_

Depends on / 依赖: AECover, aecover_Ioc, eventually, eventually_ge_atTop, eventually_le_atBot, filter_upwards, ha.eventually, hai.trans, hb.eventually, integral_of_le, integral_tendsto_of_countably_generated, intervalIntegral, intervalIntegral.integral_of_le
-/
theorem intervalIntegral_tendsto_integral (hfi : Integrable f μ) (ha : Tendsto a l atBot)
    (hb : Tendsto b l atTop) : Tendsto (fun i => ∫ x in a i..b i, f x ∂μ) l (𝓝 <| ∫ x, f x ∂μ) := by
  let φ i := Ioc (a i) (b i)
  have hφ : AECover μ l φ := aecover_Ioc ha hb
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' ?_
  filter_upwards [ha.eventually (eventually_le_atBot 0),
    hb.eventually (eventually_ge_atTop 0)] with i hai hbi
  exact (intervalIntegral.integral_of_le (hai.trans hbi)).symm

/--
theorem `intervalIntegral_tendsto_integral_Iic` / 定理 `intervalIntegral_tendsto_integral_Iic`

English:
theorem intervalIntegral_tendsto_integral_Iic
  statement: (b : Real) (hfi : IntegrableOn f (Iic b) μ)
  proof: by
  let φ i := Ioi (a i)
  have hφ : AECover (μ.restrict <| Iic b) l φ := aecover_Ioi ha
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' ?_
  filter_upwards [ha.eventually (eventually_le_atBot <| b)] with i hai
  rw [intervalIntegral.integral_of_le hai]; rw [Measure.restrict_restri

中文:
定理 interval整数egral_tendsto_integral_Iic
  结论: (b : 实数) (hfi : 整数egrableOn f (左无界右闭区间 b) μ)
  证明: by
  let φ i := Ioi (a i)
  have hφ : AECover (μ.restrict <| Iic b) l φ := aecover_Ioi ha
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' ?_
  filter_upwards [ha.eventually (eventually_le_atBot <| b)] with i hai
  rw [intervalIntegral.integral_of_le hai]; rw [Measure.restrict_restri

Depends on / 依赖: AECover, Measure, Measure.restrict_restrict, aecover_Ioi, eventually, eventually_le_atBot, filter_upwards, ha.eventually, integral_of_le, integral_tendsto_of_countably_generated, intervalIntegral, intervalIntegral.integral_of_le, measurableSet, restrict, restrict_restrict
-/
theorem intervalIntegral_tendsto_integral_Iic (b : Real) (hfi : IntegrableOn f (Iic b) μ)
    (ha : Tendsto a l atBot) :
    Tendsto (fun i => ∫ x in a i..b, f x ∂μ) l (𝓝 <| ∫ x in Iic b, f x ∂μ) := by
  let φ i := Ioi (a i)
  have hφ : AECover (μ.restrict <| Iic b) l φ := aecover_Ioi ha
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' ?_
  filter_upwards [ha.eventually (eventually_le_atBot <| b)] with i hai
  rw [intervalIntegral.integral_of_le hai]; rw [Measure.restrict_restrict (hφ.measurableSet i)]
  rfl

/--
theorem `tendsto_integral_Iic_zero` / 定理 `tendsto_integral_Iic_zero`

English:
theorem tendsto_integral_Iic_zero
  given: (ha : Tendsto a l atBot)
  proof: by
  by_cases! h : forall b, ¬ IntegrableOn f (Iic b) μ
  · exact tendsto_const_nhds.congr (fun i => (integral_undef (h (a i))).symm)
  obtain ⟨b, hb⟩ := h
  have : forallᶠ i in l, ∫ x in Iic b, f x ∂μ - ∫ x in a i..b, f x ∂μ = ∫ x in Iic (a i), f x ∂μ := by
    filter_upwards [ha.eventually_mem (Ii

中文:
定理 tendsto_integral_Iic_zero
  条件: (ha : 收敛 a l atBot)
  证明: by
  by_cases! h : forall b, ¬ IntegrableOn f (Iic b) μ
  · exact tendsto_const_nhds.congr (fun i => (integral_undef (h (a i))).symm)
  obtain ⟨b, hb⟩ := h
  have : forallᶠ i in l, ∫ x in Iic b, f x ∂μ - ∫ x in a i..b, f x ∂μ = ∫ x in Iic (a i), f x ∂μ := by
    filter_upwards [ha.eventually_mem (Ii

Depends on / 依赖: Iic_mem_atBot, Iic_subset_Iic, IntegrableOn, Tendsto, Tendsto.con, Tendsto.congr, eventually_mem, filter_upwards, ha.eventually_mem, hb.mono_set, integral_Iic_sub_Iic, integral_undef, intervalIntegral, intervalIntegral.integral_Iic_sub_Iic, mono_set, sub_eq_iff_comm, sub_self, tendsto_const_nhds, tendsto_const_nhds.congr
-/
theorem tendsto_integral_Iic_zero (ha : Tendsto a l atBot) :
    Tendsto (fun i => ∫ x in Iic (a i), f x ∂μ) l (𝓝 0) := by
  by_cases! h : forall b, ¬ IntegrableOn f (Iic b) μ
  · exact tendsto_const_nhds.congr (fun i => (integral_undef (h (a i))).symm)
  obtain ⟨b, hb⟩ := h
  have : forallᶠ i in l, ∫ x in Iic b, f x ∂μ - ∫ x in a i..b, f x ∂μ = ∫ x in Iic (a i), f x ∂μ := by
    filter_upwards [ha.eventually_mem (Iic_mem_atBot b)] with i hi
    rw [sub_eq_iff_comm]; rw [intervalIntegral.integral_Iic_sub_Iic (hb.mono_set (Iic_subset_Iic.2 hi)) hb]
  rw [← sub_self (∫ x in Iic b]; rw [f x ∂μ)]
  exact Tendsto.congr' this (Tendsto.const_sub _ <| intervalIntegral_tendsto_integral_Iic b hb ha)

/--
theorem `tendsto_integral_Ico_integral_Iio` / 定理 `tendsto_integral_Ico_integral_Iio`

English:
theorem tendsto_integral_Ico_integral_Iio
  statement: (b : Real) (hfi : IntegrableOn f (Iio b) μ)
  proof: ((aecover_Iio_of_Ico tendsto_const_nhds ha).integral_tendsto_of_countably_generated hfi).congr'
    (by simp)

中文:
定理 tendsto_integral_Ico_integral_Iio
  结论: (b : 实数) (hfi : 整数egrableOn f (左无界右开区间 b) μ)
  证明: ((aecover_Iio_of_Ico tendsto_const_nhds ha).integral_tendsto_of_countably_generated hfi).congr'
    (by simp)

Depends on / 依赖: aecover_Iio_of_Ico, integral_tendsto_of_countably_generated, tendsto_const_nhds
-/
theorem tendsto_integral_Ico_integral_Iio (b : Real) (hfi : IntegrableOn f (Iio b) μ)
    (ha : Tendsto a l atBot) :
    Tendsto (fun i => ∫ x in Ico (a i) b, f x ∂μ) l (𝓝 <| ∫ x in Iio b, f x ∂μ) :=
  ((aecover_Iio_of_Ico tendsto_const_nhds ha).integral_tendsto_of_countably_generated hfi).congr'
    (by simp)

/--
theorem `tendsto_integral_Iio_zero` / 定理 `tendsto_integral_Iio_zero`

English:
theorem tendsto_integral_Iio_zero
  given: (ha : Tendsto a l atBot)
  proof: by
  by_cases! h : forall b, ¬ IntegrableOn f (Iio b) μ
  · exact tendsto_const_nhds.congr (fun i => (integral_undef (h (a i))).symm)
  obtain ⟨b, hb⟩ := h
  have : forallᶠ i in l, ∫ x in Iio b, f x ∂μ - ∫ x in Ico (a i) b, f x ∂μ =
      ∫ x in Iio (a i), f x ∂μ := by
    filter_upwards [ha.eventua

中文:
定理 tendsto_integral_Iio_zero
  条件: (ha : 收敛 a l atBot)
  证明: by
  by_cases! h : forall b, ¬ IntegrableOn f (Iio b) μ
  · exact tendsto_const_nhds.congr (fun i => (integral_undef (h (a i))).symm)
  obtain ⟨b, hb⟩ := h
  have : forallᶠ i in l, ∫ x in Iio b, f x ∂μ - ∫ x in Ico (a i) b, f x ∂μ =
      ∫ x in Iio (a i), f x ∂μ := by
    filter_upwards [ha.eventua

Depends on / 依赖: Iic_mem_atBot, IntegrableOn, Tendsto, Tendsto.congr, Tendsto.const_sub, const_sub, eventually_mem, filter_upwards, ha.eventually_mem, integral_Iio_sub_Iio, integral_undef, intervalIntegral, intervalIntegral.integral_Iio_sub_Iio, sub_eq_iff_comm, sub_self, tendsto_const_nhds, tendsto_const_nhds.congr, tendsto_integral
-/
theorem tendsto_integral_Iio_zero (ha : Tendsto a l atBot) :
    Tendsto (fun i => ∫ x in Iio (a i), f x ∂μ) l (𝓝 0) := by
  by_cases! h : forall b, ¬ IntegrableOn f (Iio b) μ
  · exact tendsto_const_nhds.congr (fun i => (integral_undef (h (a i))).symm)
  obtain ⟨b, hb⟩ := h
  have : forallᶠ i in l, ∫ x in Iio b, f x ∂μ - ∫ x in Ico (a i) b, f x ∂μ =
      ∫ x in Iio (a i), f x ∂μ := by
    filter_upwards [ha.eventually_mem (Iic_mem_atBot b)] with i hi
    rw [sub_eq_iff_comm]; rw [intervalIntegral.integral_Iio_sub_Iio hb hi]
  rw [← sub_self (∫ x in Iio b]; rw [f x ∂μ)]
  exact Tendsto.congr' this (Tendsto.const_sub _ <| tendsto_integral_Ico_integral_Iio b hb ha)

/--
theorem `intervalIntegral_tendsto_integral_Ioi` / 定理 `intervalIntegral_tendsto_integral_Ioi`

English:
theorem intervalIntegral_tendsto_integral_Ioi
  statement: (a : Real) (hfi : IntegrableOn f (Ioi a) μ)
  proof: by
  let φ i := Iic (b i)
  have hφ : AECover (μ.restrict <| Ioi a) l φ := aecover_Iic hb
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' ?_
  filter_upwards [hb.eventually (eventually_ge_atTop <| a)] with i hbi
  rw [intervalIntegral.integral_of_le hbi]; rw [Measure.restrict_restri

中文:
定理 interval整数egral_tendsto_integral_Ioi
  结论: (a : 实数) (hfi : 整数egrableOn f (左开右无界区间 a) μ)
  证明: by
  let φ i := Iic (b i)
  have hφ : AECover (μ.restrict <| Ioi a) l φ := aecover_Iic hb
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' ?_
  filter_upwards [hb.eventually (eventually_ge_atTop <| a)] with i hbi
  rw [intervalIntegral.integral_of_le hbi]; rw [Measure.restrict_restri

Depends on / 依赖: AECover, Measure, Measure.restrict_restrict, aecover_Iic, eventually, eventually_ge_atTop, filter_upwards, hb.eventually, integral_of_le, integral_tendsto_of_countably_generated, inter_comm, intervalIntegral, intervalIntegral.integral_of_le, measurableSet, restrict, restrict_restrict
-/
theorem intervalIntegral_tendsto_integral_Ioi (a : Real) (hfi : IntegrableOn f (Ioi a) μ)
    (hb : Tendsto b l atTop) :
    Tendsto (fun i => ∫ x in a..b i, f x ∂μ) l (𝓝 <| ∫ x in Ioi a, f x ∂μ) := by
  let φ i := Iic (b i)
  have hφ : AECover (μ.restrict <| Ioi a) l φ := aecover_Iic hb
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' ?_
  filter_upwards [hb.eventually (eventually_ge_atTop <| a)] with i hbi
  rw [intervalIntegral.integral_of_le hbi]; rw [Measure.restrict_restrict (hφ.measurableSet i)]; rw [inter_comm]
  rfl

/--
theorem `tendsto_integral_Ioi_zero` / 定理 `tendsto_integral_Ioi_zero`

English:
theorem tendsto_integral_Ioi_zero
  given: (hb : Tendsto b l atTop)
  proof: by
  by_cases! h : forall a, ¬ IntegrableOn f (Ioi a) μ
  · exact tendsto_const_nhds.congr (fun i => (integral_undef (h (b i))).symm)
  obtain ⟨a, ha⟩ := h
  have : forallᶠ i in l, ∫ x in Ioi a, f x ∂μ - ∫ x in a..b i, f x ∂μ = ∫ x in Ioi (b i), f x ∂μ := by
    filter_upwards [hb.eventually_mem (Ic

中文:
定理 tendsto_integral_Ioi_zero
  条件: (hb : 收敛 b l atTop)
  证明: by
  by_cases! h : forall a, ¬ IntegrableOn f (Ioi a) μ
  · exact tendsto_const_nhds.congr (fun i => (integral_undef (h (b i))).symm)
  obtain ⟨a, ha⟩ := h
  have : forallᶠ i in l, ∫ x in Ioi a, f x ∂μ - ∫ x in a..b i, f x ∂μ = ∫ x in Ioi (b i), f x ∂μ := by
    filter_upwards [hb.eventually_mem (Ic

Depends on / 依赖: Ici_mem_atTop, IntegrableOn, Ioi_subset_Ioi, Tendsto, Tendsto.congr, eventually_mem, filter_upwards, ha.mono_set, hb.eventually_mem, integral_interval_add_Ioi, integral_undef, intervalIntegral, intervalIntegral.integral_interval_add_Ioi, mono_set, sub_eq_iff_eq_add, sub_self, tendsto_const_nhds, tendsto_const_nhds.congr
-/
theorem tendsto_integral_Ioi_zero (hb : Tendsto b l atTop) :
    Tendsto (fun i => ∫ x in Ioi (b i), f x ∂μ) l (𝓝 0) := by
  by_cases! h : forall a, ¬ IntegrableOn f (Ioi a) μ
  · exact tendsto_const_nhds.congr (fun i => (integral_undef (h (b i))).symm)
  obtain ⟨a, ha⟩ := h
  have : forallᶠ i in l, ∫ x in Ioi a, f x ∂μ - ∫ x in a..b i, f x ∂μ = ∫ x in Ioi (b i), f x ∂μ := by
    filter_upwards [hb.eventually_mem (Ici_mem_atTop a)] with i hi
    rw [sub_eq_iff_eq_add']; rw [intervalIntegral.integral_interval_add_Ioi ha (ha.mono_set (Ioi_subset_Ioi hi))]
  rw [← sub_self (∫ x in Ioi a]; rw [f x ∂μ)]
  exact Tendsto.congr' this (Tendsto.const_sub _ <| intervalIntegral_tendsto_integral_Ioi a ha hb)

/--
theorem `tendsto_integral_Ico_integral_Ici` / 定理 `tendsto_integral_Ico_integral_Ici`

English:
theorem tendsto_integral_Ico_integral_Ici
  statement: (b : Real) (hfi : IntegrableOn f (Ici b) μ)
  proof: ((aecover_Ici_of_Ico ha).integral_tendsto_of_countably_generated hfi).congr' (by simp)

中文:
定理 tendsto_integral_Ico_integral_Ici
  结论: (b : 实数) (hfi : 整数egrableOn f (左闭右无界区间 b) μ)
  证明: ((aecover_Ici_of_Ico ha).integral_tendsto_of_countably_generated hfi).congr' (by simp)

Depends on / 依赖: aecover_Ici_of_Ico, integral_tendsto_of_countably_generated
-/
theorem tendsto_integral_Ico_integral_Ici (b : Real) (hfi : IntegrableOn f (Ici b) μ)
    (ha : Tendsto a l atTop) :
    Tendsto (fun i => ∫ x in Ico b (a i), f x ∂μ) l (𝓝 <| ∫ x in Ici b, f x ∂μ) :=
  ((aecover_Ici_of_Ico ha).integral_tendsto_of_countably_generated hfi).congr' (by simp)

/--
theorem `tendsto_integral_Ici_zero` / 定理 `tendsto_integral_Ici_zero`

English:
theorem tendsto_integral_Ici_zero
  given: (ha : Tendsto a l atTop)
  proof: by
  by_cases! h : forall b, ¬ IntegrableOn f (Ici b) μ
  · exact tendsto_const_nhds.congr (fun i => (integral_undef (h (a i))).symm)
  obtain ⟨b, hb⟩ := h
  have : forallᶠ i in l, ∫ x in Ici b, f x ∂μ - ∫ x in Ico b (a i), f x ∂μ =
      ∫ x in Ici (a i), f x ∂μ := by
    filter_upwards [ha.eventua

中文:
定理 tendsto_integral_Ici_zero
  条件: (ha : 收敛 a l atTop)
  证明: by
  by_cases! h : forall b, ¬ IntegrableOn f (Ici b) μ
  · exact tendsto_const_nhds.congr (fun i => (integral_undef (h (a i))).symm)
  obtain ⟨b, hb⟩ := h
  have : forallᶠ i in l, ∫ x in Ici b, f x ∂μ - ∫ x in Ico b (a i), f x ∂μ =
      ∫ x in Ici (a i), f x ∂μ := by
    filter_upwards [ha.eventua

Depends on / 依赖: Ici_mem_atTop, IntegrableOn, Tendsto, Tendsto.congr, Tendsto.const_sub, const_sub, eventually_mem, filter_upwards, ha.eventually_mem, integral_Ici_sub_Ici, integral_undef, intervalIntegral, intervalIntegral.integral_Ici_sub_Ici, sub_eq_iff_comm, sub_self, tendsto_const_nhds, tendsto_const_nhds.congr, tendsto_integral
-/
theorem tendsto_integral_Ici_zero (ha : Tendsto a l atTop) :
    Tendsto (fun i => ∫ x in Ici (a i), f x ∂μ) l (𝓝 0) := by
  by_cases! h : forall b, ¬ IntegrableOn f (Ici b) μ
  · exact tendsto_const_nhds.congr (fun i => (integral_undef (h (a i))).symm)
  obtain ⟨b, hb⟩ := h
  have : forallᶠ i in l, ∫ x in Ici b, f x ∂μ - ∫ x in Ico b (a i), f x ∂μ =
      ∫ x in Ici (a i), f x ∂μ := by
    filter_upwards [ha.eventually_mem (Ici_mem_atTop b)] with i hi
    rw [sub_eq_iff_comm]; rw [intervalIntegral.integral_Ici_sub_Ici hb hi]
  rw [← sub_self (∫ x in Ici b]; rw [f x ∂μ)]
  exact Tendsto.congr' this (Tendsto.const_sub _ <| tendsto_integral_Ico_integral_Ici b hb ha)

end IntegralOfIntervalIntegral

open Real

open scoped Interval

section IoiFTC

variable {E : Type*} {f f' : Real -> E} {g g' : Real -> Real} {a l : Real} {m : E} [NormedAddCommGroup E]
  [NormedSpace Real E]

/--
theorem `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi` / 定理 `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`

English:
theorem tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
  statement: [CompleteSpace E]
  proof: by
  suffices exists a, Tendsto f atTop (𝓝 a) from tendsto_nhds_limUnder this
  suffices CauchySeq f from cauchySeq_tendsto_of_complete this
  apply Metric.cauchySeq_iff'.2 (fun ε εpos => ?_)
  have A : forallᶠ (n : Nat) in atTop, ∫ (x : Real) in Ici ↑n, ‖f' x‖ < ε := by
    have L : Tendsto (fun (n

中文:
定理 tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
  结论: [完备空间 E]
  证明: by
  suffices exists a, Tendsto f atTop (𝓝 a) from tendsto_nhds_limUnder this
  suffices CauchySeq f from cauchySeq_tendsto_of_complete this
  apply Metric.cauchySeq_iff'.2 (fun ε εpos => ?_)
  have A : forallᶠ (n : Nat) in atTop, ∫ (x : Real) in Ici ↑n, ‖f' x‖ < ε := by
    have L : Tendsto (fun (n

Depends on / 依赖: CauchySeq, Ici_subset_Ici, Metric, Metric.cauchySeq_iff, Tendsto, cauchySeq_iff, cauchySeq_tendsto_of_complete, measurableSet_Ici, tendsto_nhds_limUnder, tendsto_setIntegral_of_antitone
-/
theorem tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi [CompleteSpace E]
    (hderiv : forall x in Ioi a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Ioi a)) :
    Tendsto f atTop (𝓝 (limUnder atTop f)) := by
  suffices exists a, Tendsto f atTop (𝓝 a) from tendsto_nhds_limUnder this
  suffices CauchySeq f from cauchySeq_tendsto_of_complete this
  apply Metric.cauchySeq_iff'.2 (fun ε εpos => ?_)
  have A : forallᶠ (n : Nat) in atTop, ∫ (x : Real) in Ici ↑n, ‖f' x‖ < ε := by
    have L : Tendsto (fun (n : Nat) => ∫ x in Ici (n : Real), ‖f' x‖) atTop
        (𝓝 (∫ x in ⋂ (n : Nat), Ici (n : Real), ‖f' x‖)) := by
      apply tendsto_setIntegral_of_antitone (fun n => measurableSet_Ici)
      · intro m n hmn
        exact Ici_subset_Ici.2 (Nat.cast_le.mpr hmn)
      · rcases exists_nat_gt a with ⟨n, hn⟩
        exact ⟨n, IntegrableOn.mono_set f'int.norm (Ici_subset_Ioi.2 hn)⟩
    have B : ⋂ (n : Nat), Ici (n : Real) = ∅ := by
      apply eq_empty_of_forall_notMem (fun x => ?_)
      simpa only [mem_iInter, mem_Ici, not_forall, not_le] using exists_nat_gt x
    simp only [B, Measure.restrict_empty, integral_zero_measure] at L
    exact (tendsto_order.1 L).2 _ εpos
  have B : forallᶠ (n : Nat) in atTop, a < n := by
    rcases exists_nat_gt a with ⟨n, hn⟩
    filter_upwards [Ioi_mem_atTop n] with m (hm : n < m) using hn.trans (Nat.cast_lt.mpr hm)
  rcases (A.and B).exists with ⟨N, hN, h'N⟩
  refine ⟨N, fun x hx => ?_⟩
  calc
  dist (f x) (f ↑N)
    = ‖f x - f N‖ := dist_eq_norm _ _
  _ = ‖∫ t in Ioc ↑N x, f' t‖ := by
      rw [← intervalIntegral.integral_of_le hx]; rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
      · intro y hy
        simp only [hx, uIcc_of_le, mem_Icc] at hy
        exact hderiv _ (h'N.trans_le hy.1)
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
        exact f'int.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi h'N.le))
  _ <= ∫ t in Ioc ↑N x, ‖f' t‖ := norm_integral_le_integral_norm fun a => f' a
  _ <= ∫ t in Ici ↑N, ‖f' t‖ := by
      apply setIntegral_mono_set
      · apply IntegrableOn.mono_set f'int.norm (Ici_subset_Ioi.2 h'N)
      · filter_upwards with x using norm_nonneg _
      · have : Ioc (↑N) x subseteq Ici ↑N := Ioc_subset_Ioi_self.trans Ioi_subset_Ici_self
        exact this.eventuallyLE
  _ < ε := hN

open UniformSpace in
/--
theorem `tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi` / 定理 `tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi`

English:
theorem tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
  proof: by
  let F : E ->L[Real] Completion E := Completion.toComplL
  have Fderiv : forall x in Ioi a, HasDerivAt (F ∘ f) (F (f' x)) x :=
    fun x hx => F.hasFDerivAt.comp_hasDerivAt _ (hderiv x hx)
  have Fint : IntegrableOn (F ∘ f) (Ioi a) := by apply F.integrable_comp fint
  have F'int : IntegrableOn (

中文:
定理 tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
  证明: by
  let F : E ->L[Real] Completion E := Completion.toComplL
  have Fderiv : forall x in Ioi a, HasDerivAt (F ∘ f) (F (f' x)) x :=
    fun x hx => F.hasFDerivAt.comp_hasDerivAt _ (hderiv x hx)
  have Fint : IntegrableOn (F ∘ f) (Ioi a) := by apply F.integrable_comp fint
  have F'int : IntegrableOn (

Depends on / 依赖: Completion, Completion.toComplL, F.hasFDerivAt.comp_hasDerivAt, F.integrable_comp, Fderiv, HasDerivAt, IntegrableOn, Tendsto, comp_hasDerivAt, hasFDerivAt, hderiv, integrable_comp, limUnder, tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi, toComplL
-/
theorem tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (hderiv : forall x in Ioi a, HasDerivAt f (f' x) x)
    (f'int : IntegrableOn f' (Ioi a)) (fint : IntegrableOn f (Ioi a)) :
    Tendsto f atTop (𝓝 0) := by
  let F : E ->L[Real] Completion E := Completion.toComplL
  have Fderiv : forall x in Ioi a, HasDerivAt (F ∘ f) (F (f' x)) x :=
    fun x hx => F.hasFDerivAt.comp_hasDerivAt _ (hderiv x hx)
  have Fint : IntegrableOn (F ∘ f) (Ioi a) := by apply F.integrable_comp fint
  have F'int : IntegrableOn (F ∘ f') (Ioi a) := by apply F.integrable_comp f'int
  have A : Tendsto (F ∘ f) atTop (𝓝 (limUnder atTop (F ∘ f))) := by
    apply tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi Fderiv F'int
  have B : limUnder atTop (F ∘ f) = F 0 := by
    have : IntegrableAtFilter (F ∘ f) atTop := by exact ⟨Ioi a, Ioi_mem_atTop _, Fint⟩
    apply IntegrableAtFilter.eq_zero_of_tendsto this ?_ A
    intro s hs
    rcases mem_atTop_sets.1 hs with ⟨b, hb⟩
    rw [← top_le_iff]; rw [← volume_Ici (a := b)]
    exact measure_mono hb
  rwa [B, ← IsEmbedding.tendsto_nhds_iff] at A
  exact (Completion.isUniformEmbedding_coe E).isEmbedding

variable [CompleteSpace E]

/--
theorem `integral_Ioi_of_hasDerivAt_of_tendsto` / 定理 `integral_Ioi_of_hasDerivAt_of_tendsto`

English:
theorem integral_Ioi_of_hasDerivAt_of_tendsto
  statement: (hcont : ContinuousWithinAt f (Ici a) a)
  proof: by
  have hcont : ContinuousOn f (Ici a) := by
    intro x hx
    rcases hx.out.eq_or_lt with rfl | hx
    · exact hcont
    · exact (hderiv x hx).continuousAt.continuousWithinAt
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi a f'int tendsto_id) ?_
  apply Tendsto.congr' _ (hf.s

中文:
定理 integral_Ioi_of_hasDerivAt_of_tendsto
  结论: (hcont : ContinuousWithinAt f (左闭右无界区间 a) a)
  证明: by
  have hcont : ContinuousOn f (Ici a) := by
    intro x hx
    rcases hx.out.eq_or_lt with rfl | hx
    · exact hcont
    · exact (hderiv x hx).continuousAt.continuousWithinAt
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi a f'int tendsto_id) ?_
  apply Tendsto.congr' _ (hf.s

Depends on / 依赖: ContinuousOn, Icc_subset_Ici_self, Ioi_mem_atTop, Tendsto, Tendsto.congr, continuousAt, continuousAt.continuousWithinAt, continuousWithinAt, eq_or_lt, filter_upwards, hcont.mono, hderiv, hf.sub_const, hx.out.eq_or_lt, integral_eq_sub_of_hasDerivAt_of_le, intervalIntegral, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le, intervalIntegral_tendsto_integral_Ioi, le_of_lt, sub_const
-/
theorem integral_Ioi_of_hasDerivAt_of_tendsto (hcont : ContinuousWithinAt f (Ici a) a)
    (hderiv : forall x in Ioi a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Ioi a))
    (hf : Tendsto f atTop (𝓝 m)) : ∫ x in Ioi a, f' x = m - f a := by
  have hcont : ContinuousOn f (Ici a) := by
    intro x hx
    rcases hx.out.eq_or_lt with rfl | hx
    · exact hcont
    · exact (hderiv x hx).continuousAt.continuousWithinAt
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi a f'int tendsto_id) ?_
  apply Tendsto.congr' _ (hf.sub_const _)
  filter_upwards [Ioi_mem_atTop a] with x hx
  have h'x : a <= id x := le_of_lt hx
  symm
  apply
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h'x (hcont.mono Icc_subset_Ici_self)
      fun y hy => hderiv y hy.1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h'x]
  exact f'int.mono (fun y hy => hy.1) le_rfl

/--
theorem `integral_Ioi_of_hasDerivAt_of_tendsto'` / 定理 `integral_Ioi_of_hasDerivAt_of_tendsto'`

English:
theorem integral_Ioi_of_hasDerivAt_of_tendsto'
  statement: (hderiv : forall x in Ici a, HasDerivAt f (f' x) x)
  proof: by
  refine integral_Ioi_of_hasDerivAt_of_tendsto ?_ (fun x hx => hderiv x hx.out.le)
    f'int hf
  exact (hderiv a self_mem_Ici).continuousAt.continuousWithinAt

中文:
定理 integral_Ioi_of_hasDerivAt_of_tendsto'
  结论: (hderiv : 对任意 x in 左闭右无界区间 a, 在点处可导 f (f' x) x)
  证明: by
  refine integral_Ioi_of_hasDerivAt_of_tendsto ?_ (fun x hx => hderiv x hx.out.le)
    f'int hf
  exact (hderiv a self_mem_Ici).continuousAt.continuousWithinAt

Depends on / 依赖: continuousAt, continuousAt.continuousWithinAt, continuousWithinAt, hderiv, hx.out.le, integral_Ioi_of_hasDerivAt_of_tendsto, self_mem_Ici
-/
theorem integral_Ioi_of_hasDerivAt_of_tendsto' (hderiv : forall x in Ici a, HasDerivAt f (f' x) x)
    (f'int : IntegrableOn f' (Ioi a)) (hf : Tendsto f atTop (𝓝 m)) :
    ∫ x in Ioi a, f' x = m - f a := by
  refine integral_Ioi_of_hasDerivAt_of_tendsto ?_ (fun x hx => hderiv x hx.out.le)
    f'int hf
  exact (hderiv a self_mem_Ici).continuousAt.continuousWithinAt

/--
theorem `_root_.HasCompactSupport.integral_Ioi_deriv_eq` / 定理 `_root_.HasCompactSupport.integral_Ioi_deriv_eq`

English:
theorem _root_.HasCompactSupport.integral_Ioi_deriv_eq
  statement: (hf : ContDiff Real 1 f)
  proof: by
.hasDerivAt have := fun x (_ : x in Ioi b) => hf.differentiable one_ne_zero x
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hf.continuous.continuousWithinAt this]; rw [zero_sub]
.integrableOn .integrable_of_hasCompactSupport h2f.deriv · refine hf.continuous_deriv le_rfl
  rw [hasCompactSupport_iff_

中文:
定理 _root_.HasCompactSupport.integral_Ioi_deriv_eq
  结论: (hf : 连续可微 实数 1 f)
  证明: by
.hasDerivAt have := fun x (_ : x in Ioi b) => hf.differentiable one_ne_zero x
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hf.continuous.continuousWithinAt this]; rw [zero_sub]
.integrableOn .integrable_of_hasCompactSupport h2f.deriv · refine hf.continuous_deriv le_rfl
  rw [hasCompactSupport_iff_

Depends on / 依赖: Filter, Filter.coclosedCompact_eq_cocompact, _root_, _root_.atTop_le_cocompact, atTop_le_cocompact, coclosedCompact_eq_cocompact, continuous, continuousWithinAt, continuous_deriv, differentiable, filter_mono, h2f.deriv, h2f.filter_mono, hasCompactSupport_iff_eventuallyEq, hasDerivAt, hf.continuous.continuousWithinAt, hf.continuous_deriv, hf.differentiable, integrableOn, integrable_of_hasCompactSupport
-/
theorem _root_.HasCompactSupport.integral_Ioi_deriv_eq (hf : ContDiff Real 1 f)
    (h2f : HasCompactSupport f) (b : Real) : ∫ x in Ioi b, deriv f x = - f b := by
.hasDerivAt have := fun x (_ : x in Ioi b) => hf.differentiable one_ne_zero x
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hf.continuous.continuousWithinAt this]; rw [zero_sub]
.integrableOn .integrable_of_hasCompactSupport h2f.deriv · refine hf.continuous_deriv le_rfl
  rw [hasCompactSupport_iff_eventuallyEq]; rw [Filter.coclosedCompact_eq_cocompact] at h2f
.tendsto exact h2f.filter_mono _root_.atTop_le_cocompact

/--
theorem `integrableOn_Ioi_deriv_of_nonneg` / 定理 `integrableOn_Ioi_deriv_of_nonneg`

English:
theorem integrableOn_Ioi_deriv_of_nonneg
  statement: (hcont : ContinuousWithinAt g (Ici a) a)
  proof: by
  have hcont : ContinuousOn g (Ici a) := by
    intro x hx
    rcases hx.out.eq_or_lt with rfl | hx
    · exact hcont
    · exact (hderiv x hx).continuousAt.continuousWithinAt
  refine integrableOn_Ioi_of_intervalIntegral_norm_tendsto (l - g a) a (fun x => ?_) tendsto_id ?_
  · exact intervalInte

中文:
定理 integrableOn_Ioi_deriv_of_nonneg
  结论: (hcont : ContinuousWithinAt g (左闭右无界区间 a) a)
  证明: by
  have hcont : ContinuousOn g (Ici a) := by
    intro x hx
    rcases hx.out.eq_or_lt with rfl | hx
    · exact hcont
    · exact (hderiv x hx).continuousAt.continuousWithinAt
  refine integrableOn_Ioi_of_intervalIntegral_norm_tendsto (l - g a) a (fun x => ?_) tendsto_id ?_
  · exact intervalInte

Depends on / 依赖: ContinuousOn, Icc_subset_Ici_self, Ioi_mem_atTop, Tendsto, Tendsto.congr, continuousAt, continuousAt.continuousWithinAt, continuousWithinAt, eq_or_lt, filter_upwards, hcont.mono, hderiv, hg.sub_const, hx.out.eq_or_lt, integrableOn_Ioi_of_intervalIntegral_norm_tendsto, integrableOn_deriv_of_nonneg, intervalIntegral, intervalIntegral.integrableOn_deriv_of_nonneg, sub_const, tendsto_id
-/
theorem integrableOn_Ioi_deriv_of_nonneg (hcont : ContinuousWithinAt g (Ici a) a)
    (hderiv : forall x in Ioi a, HasDerivAt g (g' x) x) (g'pos : forall x in Ioi a, 0 <= g' x)
    (hg : Tendsto g atTop (𝓝 l)) : IntegrableOn g' (Ioi a) := by
  have hcont : ContinuousOn g (Ici a) := by
    intro x hx
    rcases hx.out.eq_or_lt with rfl | hx
    · exact hcont
    · exact (hderiv x hx).continuousAt.continuousWithinAt
  refine integrableOn_Ioi_of_intervalIntegral_norm_tendsto (l - g a) a (fun x => ?_) tendsto_id ?_
  · exact intervalIntegral.integrableOn_deriv_of_nonneg (hcont.mono Icc_subset_Ici_self)
      (fun y hy => hderiv y hy.1) fun y hy => g'pos y hy.1
  apply Tendsto.congr' _ (hg.sub_const _)
  filter_upwards [Ioi_mem_atTop a] with x hx
  have h'x : a <= id x := le_of_lt hx
  calc
    g x - g a = ∫ y in a..id x, g' y := by
      symm
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h'x
        (hcont.mono Icc_subset_Ici_self) fun y hy => hderiv y hy.1
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h'x]
      exact intervalIntegral.integrableOn_deriv_of_nonneg (hcont.mono Icc_subset_Ici_self)
        (fun y hy => hderiv y hy.1) fun y hy => g'pos y hy.1
    _ = ∫ y in a..id x, ‖g' y‖ := by
      simp_rw [intervalIntegral.integral_of_le h'x]
      refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
      dsimp
      rw [abs_of_nonneg]
      exact g'pos _ hy.1

/--
theorem `integrableOn_Ioi_deriv_of_nonneg'` / 定理 `integrableOn_Ioi_deriv_of_nonneg'`

English:
theorem integrableOn_Ioi_deriv_of_nonneg'
  statement: (hderiv : forall x in Ici a, HasDerivAt g (g' x) x)
  proof: by
  refine integrableOn_Ioi_deriv_of_nonneg ?_ (fun x hx => hderiv x hx.out.le) g'pos hg
  exact (hderiv a self_mem_Ici).continuousAt.continuousWithinAt

中文:
定理 integrableOn_Ioi_deriv_of_nonneg'
  结论: (hderiv : 对任意 x in 左闭右无界区间 a, 在点处可导 g (g' x) x)
  证明: by
  refine integrableOn_Ioi_deriv_of_nonneg ?_ (fun x hx => hderiv x hx.out.le) g'pos hg
  exact (hderiv a self_mem_Ici).continuousAt.continuousWithinAt

Depends on / 依赖: continuousAt, continuousAt.continuousWithinAt, continuousWithinAt, hderiv, hx.out.le, integrableOn_Ioi_deriv_of_nonneg, self_mem_Ici
-/
theorem integrableOn_Ioi_deriv_of_nonneg' (hderiv : forall x in Ici a, HasDerivAt g (g' x) x)
    (g'pos : forall x in Ioi a, 0 <= g' x) (hg : Tendsto g atTop (𝓝 l)) : IntegrableOn g' (Ioi a) := by
  refine integrableOn_Ioi_deriv_of_nonneg ?_ (fun x hx => hderiv x hx.out.le) g'pos hg
  exact (hderiv a self_mem_Ici).continuousAt.continuousWithinAt

/--
theorem `integral_Ioi_of_hasDerivAt_of_nonneg` / 定理 `integral_Ioi_of_hasDerivAt_of_nonneg`

English:
theorem integral_Ioi_of_hasDerivAt_of_nonneg
  statement: (hcont : ContinuousWithinAt g (Ici a) a)
  proof: integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_Ioi_deriv_of_nonneg hcont hderiv g'pos hg) hg

中文:
定理 integral_Ioi_of_hasDerivAt_of_nonneg
  结论: (hcont : ContinuousWithinAt g (左闭右无界区间 a) a)
  证明: integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_Ioi_deriv_of_nonneg hcont hderiv g'pos hg) hg

Depends on / 依赖: hderiv, integrableOn_Ioi_deriv_of_nonneg, integral_Ioi_of_hasDerivAt_of_tendsto
-/
theorem integral_Ioi_of_hasDerivAt_of_nonneg (hcont : ContinuousWithinAt g (Ici a) a)
    (hderiv : forall x in Ioi a, HasDerivAt g (g' x) x) (g'pos : forall x in Ioi a, 0 <= g' x)
    (hg : Tendsto g atTop (𝓝 l)) : ∫ x in Ioi a, g' x = l - g a :=
  integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_Ioi_deriv_of_nonneg hcont hderiv g'pos hg) hg

/--
theorem `integral_Ioi_of_hasDerivAt_of_nonneg'` / 定理 `integral_Ioi_of_hasDerivAt_of_nonneg'`

English:
theorem integral_Ioi_of_hasDerivAt_of_nonneg'
  statement: (hderiv : forall x in Ici a, HasDerivAt g (g' x) x)
  proof: integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_Ioi_deriv_of_nonneg' hderiv g'pos hg)
    hg

中文:
定理 integral_Ioi_of_hasDerivAt_of_nonneg'
  结论: (hderiv : 对任意 x in 左闭右无界区间 a, 在点处可导 g (g' x) x)
  证明: integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_Ioi_deriv_of_nonneg' hderiv g'pos hg)
    hg

Depends on / 依赖: hderiv, integrableOn_Ioi_deriv_of_nonneg, integral_Ioi_of_hasDerivAt_of_tendsto
-/
theorem integral_Ioi_of_hasDerivAt_of_nonneg' (hderiv : forall x in Ici a, HasDerivAt g (g' x) x)
    (g'pos : forall x in Ioi a, 0 <= g' x) (hg : Tendsto g atTop (𝓝 l)) : ∫ x in Ioi a, g' x = l - g a :=
  integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_Ioi_deriv_of_nonneg' hderiv g'pos hg)
    hg

/--
theorem `integrableOn_Ioi_deriv_of_nonpos` / 定理 `integrableOn_Ioi_deriv_of_nonpos`

English:
theorem integrableOn_Ioi_deriv_of_nonpos
  statement: (hcont : ContinuousWithinAt g (Ici a) a)
  proof: by
  apply integrable_neg_iff.1
  exact integrableOn_Ioi_deriv_of_nonneg hcont.neg (fun x hx => (hderiv x hx).neg)
    (fun x hx => neg_nonneg_of_nonpos (g'neg x hx)) hg.neg

中文:
定理 integrableOn_Ioi_deriv_of_nonpos
  结论: (hcont : ContinuousWithinAt g (左闭右无界区间 a) a)
  证明: by
  apply integrable_neg_iff.1
  exact integrableOn_Ioi_deriv_of_nonneg hcont.neg (fun x hx => (hderiv x hx).neg)
    (fun x hx => neg_nonneg_of_nonpos (g'neg x hx)) hg.neg

Depends on / 依赖: hcont.neg, hderiv, hg.neg, integrableOn_Ioi_deriv_of_nonneg, integrable_neg_iff, neg_nonneg_of_nonpos
-/
theorem integrableOn_Ioi_deriv_of_nonpos (hcont : ContinuousWithinAt g (Ici a) a)
    (hderiv : forall x in Ioi a, HasDerivAt g (g' x) x) (g'neg : forall x in Ioi a, g' x <= 0)
    (hg : Tendsto g atTop (𝓝 l)) : IntegrableOn g' (Ioi a) := by
  apply integrable_neg_iff.1
  exact integrableOn_Ioi_deriv_of_nonneg hcont.neg (fun x hx => (hderiv x hx).neg)
    (fun x hx => neg_nonneg_of_nonpos (g'neg x hx)) hg.neg

/--
theorem `integrableOn_Ioi_deriv_of_nonpos'` / 定理 `integrableOn_Ioi_deriv_of_nonpos'`

English:
theorem integrableOn_Ioi_deriv_of_nonpos'
  statement: (hderiv : forall x in Ici a, HasDerivAt g (g' x) x)
  proof: by
  refine integrableOn_Ioi_deriv_of_nonpos ?_ (fun x hx => hderiv x hx.out.le) g'neg hg
  exact (hderiv a self_mem_Ici).continuousAt.continuousWithinAt

中文:
定理 integrableOn_Ioi_deriv_of_nonpos'
  结论: (hderiv : 对任意 x in 左闭右无界区间 a, 在点处可导 g (g' x) x)
  证明: by
  refine integrableOn_Ioi_deriv_of_nonpos ?_ (fun x hx => hderiv x hx.out.le) g'neg hg
  exact (hderiv a self_mem_Ici).continuousAt.continuousWithinAt

Depends on / 依赖: continuousAt, continuousAt.continuousWithinAt, continuousWithinAt, hderiv, hx.out.le, integrableOn_Ioi_deriv_of_nonpos, self_mem_Ici
-/
theorem integrableOn_Ioi_deriv_of_nonpos' (hderiv : forall x in Ici a, HasDerivAt g (g' x) x)
    (g'neg : forall x in Ioi a, g' x <= 0) (hg : Tendsto g atTop (𝓝 l)) : IntegrableOn g' (Ioi a) := by
  refine integrableOn_Ioi_deriv_of_nonpos ?_ (fun x hx => hderiv x hx.out.le) g'neg hg
  exact (hderiv a self_mem_Ici).continuousAt.continuousWithinAt

/--
theorem `integral_Ioi_of_hasDerivAt_of_nonpos` / 定理 `integral_Ioi_of_hasDerivAt_of_nonpos`

English:
theorem integral_Ioi_of_hasDerivAt_of_nonpos
  statement: (hcont : ContinuousWithinAt g (Ici a) a)
  proof: integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_Ioi_deriv_of_nonpos hcont hderiv g'neg hg) hg

中文:
定理 integral_Ioi_of_hasDerivAt_of_nonpos
  结论: (hcont : ContinuousWithinAt g (左闭右无界区间 a) a)
  证明: integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_Ioi_deriv_of_nonpos hcont hderiv g'neg hg) hg

Depends on / 依赖: hderiv, integrableOn_Ioi_deriv_of_nonpos, integral_Ioi_of_hasDerivAt_of_tendsto
-/
theorem integral_Ioi_of_hasDerivAt_of_nonpos (hcont : ContinuousWithinAt g (Ici a) a)
    (hderiv : forall x in Ioi a, HasDerivAt g (g' x) x) (g'neg : forall x in Ioi a, g' x <= 0)
    (hg : Tendsto g atTop (𝓝 l)) : ∫ x in Ioi a, g' x = l - g a :=
  integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_Ioi_deriv_of_nonpos hcont hderiv g'neg hg) hg

/--
theorem `integral_Ioi_of_hasDerivAt_of_nonpos'` / 定理 `integral_Ioi_of_hasDerivAt_of_nonpos'`

English:
theorem integral_Ioi_of_hasDerivAt_of_nonpos'
  statement: (hderiv : forall x in Ici a, HasDerivAt g (g' x) x)
  proof: integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_Ioi_deriv_of_nonpos' hderiv g'neg hg)
    hg

中文:
定理 integral_Ioi_of_hasDerivAt_of_nonpos'
  结论: (hderiv : 对任意 x in 左闭右无界区间 a, 在点处可导 g (g' x) x)
  证明: integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_Ioi_deriv_of_nonpos' hderiv g'neg hg)
    hg

Depends on / 依赖: hderiv, integrableOn_Ioi_deriv_of_nonpos, integral_Ioi_of_hasDerivAt_of_tendsto
-/
theorem integral_Ioi_of_hasDerivAt_of_nonpos' (hderiv : forall x in Ici a, HasDerivAt g (g' x) x)
    (g'neg : forall x in Ioi a, g' x <= 0) (hg : Tendsto g atTop (𝓝 l)) : ∫ x in Ioi a, g' x = l - g a :=
  integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_Ioi_deriv_of_nonpos' hderiv g'neg hg)
    hg

end IoiFTC

section IicFTC

variable {E : Type*} {f f' : Real -> E} {a : Real} {m : E} [NormedAddCommGroup E]
  [NormedSpace Real E]

/--
theorem `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic` / 定理 `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic`

English:
theorem tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic
  statement: [CompleteSpace E]
  proof: by
  suffices exists a, Tendsto f atBot (𝓝 a) from tendsto_nhds_limUnder this
  let g := f ∘ (fun x => -x)
  have hdg : forall x in Ioi (-a), HasDerivAt g (-f' (-x)) x := by
    intro x hx
    have : -x in Iic a := by grind
    simpa using HasDerivAt.scomp x (hderiv (-x) this) (hasDerivAt_neg' x)
  

中文:
定理 tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic
  结论: [完备空间 E]
  证明: by
  suffices exists a, Tendsto f atBot (𝓝 a) from tendsto_nhds_limUnder this
  let g := f ∘ (fun x => -x)
  have hdg : forall x in Ioi (-a), HasDerivAt g (-f' (-x)) x := by
    intro x hx
    have : -x in Iic a := by grind
    simpa using HasDerivAt.scomp x (hderiv (-x) this) (hasDerivAt_neg' x)
  

Depends on / 依赖: HasDerivAt, HasDerivAt.scomp, Homeomorph, Homeomorph.neg, Measure, Measure.measurePreserving_neg, MeasurePreserving, MeasurePreserving.integrableOn_comp_preimage, Tendsto, hasDerivAt_neg, hderiv, integrableOn_comp_preimage, limUnder, measurePreserving_neg, tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi, tendsto_nhds_limUnder
-/
theorem tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic [CompleteSpace E]
    (hderiv : forall x in Iic a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Iic a)) :
    Tendsto f atBot (𝓝 (limUnder atBot f)) := by
  suffices exists a, Tendsto f atBot (𝓝 a) from tendsto_nhds_limUnder this
  let g := f ∘ (fun x => -x)
  have hdg : forall x in Ioi (-a), HasDerivAt g (-f' (-x)) x := by
    intro x hx
    have : -x in Iic a := by grind
    simpa using HasDerivAt.scomp x (hderiv (-x) this) (hasDerivAt_neg' x)
  have L : Tendsto g atTop (𝓝 (limUnder atTop g)) := by
    apply tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi hdg
    exact ((MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg _)
      (Homeomorph.neg Real).measurableEmbedding).2 f'int.neg).mono_set (by simp)
  refine ⟨limUnder atTop g, ?_⟩
  have : Tendsto (fun x => g (-x)) atBot (𝓝 (limUnder atTop g)) := L.comp tendsto_neg_atBot_atTop
  simpa [g] using this

open UniformSpace in
/--
theorem `tendsto_zero_of_hasDerivAt_of_integrableOn_Iic` / 定理 `tendsto_zero_of_hasDerivAt_of_integrableOn_Iic`

English:
theorem tendsto_zero_of_hasDerivAt_of_integrableOn_Iic
  proof: by
  let F : E ->L[Real] Completion E := Completion.toComplL
  have Fderiv : forall x in Iic a, HasDerivAt (F ∘ f) (F (f' x)) x :=
    fun x hx => F.hasFDerivAt.comp_hasDerivAt _ (hderiv x hx)
  have Fint : IntegrableOn (F ∘ f) (Iic a) := by apply F.integrable_comp fint
  have F'int : IntegrableOn (

中文:
定理 tendsto_zero_of_hasDerivAt_of_integrableOn_Iic
  证明: by
  let F : E ->L[Real] Completion E := Completion.toComplL
  have Fderiv : forall x in Iic a, HasDerivAt (F ∘ f) (F (f' x)) x :=
    fun x hx => F.hasFDerivAt.comp_hasDerivAt _ (hderiv x hx)
  have Fint : IntegrableOn (F ∘ f) (Iic a) := by apply F.integrable_comp fint
  have F'int : IntegrableOn (

Depends on / 依赖: Completion, Completion.toComplL, F.hasFDerivAt.comp_hasDerivAt, F.integrable_comp, Fderiv, HasDerivAt, IntegrableOn, Tendsto, comp_hasDerivAt, hasFDerivAt, hderiv, integrable_comp, limUnder, tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic, toComplL
-/
theorem tendsto_zero_of_hasDerivAt_of_integrableOn_Iic
    (hderiv : forall x in Iic a, HasDerivAt f (f' x) x)
    (f'int : IntegrableOn f' (Iic a)) (fint : IntegrableOn f (Iic a)) :
    Tendsto f atBot (𝓝 0) := by
  let F : E ->L[Real] Completion E := Completion.toComplL
  have Fderiv : forall x in Iic a, HasDerivAt (F ∘ f) (F (f' x)) x :=
    fun x hx => F.hasFDerivAt.comp_hasDerivAt _ (hderiv x hx)
  have Fint : IntegrableOn (F ∘ f) (Iic a) := by apply F.integrable_comp fint
  have F'int : IntegrableOn (F ∘ f') (Iic a) := by apply F.integrable_comp f'int
  have A : Tendsto (F ∘ f) atBot (𝓝 (limUnder atBot (F ∘ f))) := by
    apply tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic Fderiv F'int
  have B : limUnder atBot (F ∘ f) = F 0 := by
    have : IntegrableAtFilter (F ∘ f) atBot := by exact ⟨Iic a, Iic_mem_atBot _, Fint⟩
    apply IntegrableAtFilter.eq_zero_of_tendsto this ?_ A
    intro s hs
    rcases mem_atBot_sets.1 hs with ⟨b, hb⟩
    apply le_antisymm (le_top)
    rw [← volume_Iic (a := b)]
    exact measure_mono hb
  rwa [B, ← IsEmbedding.tendsto_nhds_iff] at A
  exact (Completion.isUniformEmbedding_coe E).isEmbedding

variable [CompleteSpace E]

/--
theorem `integral_Iic_of_hasDerivAt_of_tendsto` / 定理 `integral_Iic_of_hasDerivAt_of_tendsto`

English:
theorem integral_Iic_of_hasDerivAt_of_tendsto
  statement: (hcont : ContinuousWithinAt f (Iic a) a)
  proof: by
  have hcont : ContinuousOn f (Iic a) := by
    intro x hx
    rcases hx.out.eq_or_lt with rfl | hx
    · exact hcont
    · exact (hderiv x hx).continuousAt.continuousWithinAt
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Iic a f'int tendsto_id) ?_
  apply Tendsto.congr' _ (hf.c

中文:
定理 integral_Iic_of_hasDerivAt_of_tendsto
  结论: (hcont : ContinuousWithinAt f (左无界右闭区间 a) a)
  证明: by
  have hcont : ContinuousOn f (Iic a) := by
    intro x hx
    rcases hx.out.eq_or_lt with rfl | hx
    · exact hcont
    · exact (hderiv x hx).continuousAt.continuousWithinAt
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Iic a f'int tendsto_id) ?_
  apply Tendsto.congr' _ (hf.c

Depends on / 依赖: ContinuousOn, Icc_subset_Iic_self, Iic_mem_atBot, Tendsto, Tendsto.congr, const_sub, continuousAt, continuousAt.continuousWithinAt, continuousWithinAt, eq_or_lt, filter_upwards, hcont.mono, hderiv, hf.const_sub, hx.out.eq_or_lt, integral_eq_sub_of_hasDerivAt_of_le, intervalIntegrable_iff_integrableOn_I, intervalIntegral, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le, intervalIntegral_tendsto_integral_Iic
-/
theorem integral_Iic_of_hasDerivAt_of_tendsto (hcont : ContinuousWithinAt f (Iic a) a)
    (hderiv : forall x in Iio a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Iic a))
    (hf : Tendsto f atBot (𝓝 m)) : ∫ x in Iic a, f' x = f a - m := by
  have hcont : ContinuousOn f (Iic a) := by
    intro x hx
    rcases hx.out.eq_or_lt with rfl | hx
    · exact hcont
    · exact (hderiv x hx).continuousAt.continuousWithinAt
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Iic a f'int tendsto_id) ?_
  apply Tendsto.congr' _ (hf.const_sub _)
  filter_upwards [Iic_mem_atBot a] with x hx
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx
    (hcont.mono Icc_subset_Iic_self) fun y hy => hderiv y hy.2
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  exact f'int.mono (fun y hy => hy.2) le_rfl

/--
theorem `integral_Iic_of_hasDerivAt_of_tendsto'` / 定理 `integral_Iic_of_hasDerivAt_of_tendsto'`

English:
theorem integral_Iic_of_hasDerivAt_of_tendsto'
  proof: by
  refine integral_Iic_of_hasDerivAt_of_tendsto ?_ (fun x hx => hderiv x hx.out.le)
    f'int hf
  exact (hderiv a self_mem_Iic).continuousAt.continuousWithinAt

中文:
定理 integral_Iic_of_hasDerivAt_of_tendsto'
  证明: by
  refine integral_Iic_of_hasDerivAt_of_tendsto ?_ (fun x hx => hderiv x hx.out.le)
    f'int hf
  exact (hderiv a self_mem_Iic).continuousAt.continuousWithinAt

Depends on / 依赖: continuousAt, continuousAt.continuousWithinAt, continuousWithinAt, hderiv, hx.out.le, integral_Iic_of_hasDerivAt_of_tendsto, self_mem_Iic
-/
theorem integral_Iic_of_hasDerivAt_of_tendsto'
    (hderiv : forall x in Iic a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Iic a))
    (hf : Tendsto f atBot (𝓝 m)) : ∫ x in Iic a, f' x = f a - m := by
  refine integral_Iic_of_hasDerivAt_of_tendsto ?_ (fun x hx => hderiv x hx.out.le)
    f'int hf
  exact (hderiv a self_mem_Iic).continuousAt.continuousWithinAt

/--
theorem `_root_.HasCompactSupport.integral_Iic_deriv_eq` / 定理 `_root_.HasCompactSupport.integral_Iic_deriv_eq`

English:
theorem _root_.HasCompactSupport.integral_Iic_deriv_eq
  statement: (hf : ContDiff Real 1 f)
  proof: by
.hasDerivAt have := fun x (_ : x in Iio b) => hf.differentiable one_ne_zero x
  rw [integral_Iic_of_hasDerivAt_of_tendsto hf.continuous.continuousWithinAt this]; rw [sub_zero]
.integrableOn .integrable_of_hasCompactSupport h2f.deriv · refine hf.continuous_deriv le_rfl
  rw [hasCompactSupport_iff_

中文:
定理 _root_.HasCompactSupport.integral_Iic_deriv_eq
  结论: (hf : 连续可微 实数 1 f)
  证明: by
.hasDerivAt have := fun x (_ : x in Iio b) => hf.differentiable one_ne_zero x
  rw [integral_Iic_of_hasDerivAt_of_tendsto hf.continuous.continuousWithinAt this]; rw [sub_zero]
.integrableOn .integrable_of_hasCompactSupport h2f.deriv · refine hf.continuous_deriv le_rfl
  rw [hasCompactSupport_iff_

Depends on / 依赖: Filter, Filter.coclosedCompact_eq_cocompact, _root_, _root_.atBot_le_cocompact, atBot_le_cocompact, coclosedCompact_eq_cocompact, continuous, continuousWithinAt, continuous_deriv, differentiable, filter_mono, h2f.deriv, h2f.filter_mono, hasCompactSupport_iff_eventuallyEq, hasDerivAt, hf.continuous.continuousWithinAt, hf.continuous_deriv, hf.differentiable, integrableOn, integrable_of_hasCompactSupport
-/
theorem _root_.HasCompactSupport.integral_Iic_deriv_eq (hf : ContDiff Real 1 f)
    (h2f : HasCompactSupport f) (b : Real) : ∫ x in Iic b, deriv f x = f b := by
.hasDerivAt have := fun x (_ : x in Iio b) => hf.differentiable one_ne_zero x
  rw [integral_Iic_of_hasDerivAt_of_tendsto hf.continuous.continuousWithinAt this]; rw [sub_zero]
.integrableOn .integrable_of_hasCompactSupport h2f.deriv · refine hf.continuous_deriv le_rfl
  rw [hasCompactSupport_iff_eventuallyEq]; rw [Filter.coclosedCompact_eq_cocompact] at h2f
.tendsto exact h2f.filter_mono _root_.atBot_le_cocompact

open UniformSpace in
/--
lemma `_root_.HasCompactSupport.enorm_le_lintegral_Ici_deriv` / 引理 `_root_.HasCompactSupport.enorm_le_lintegral_Ici_deriv`

English:
lemma _root_.HasCompactSupport.enorm_le_lintegral_Ici_deriv
  proof: by
  let I : F ->L[Real] Completion F := Completion.toComplL
  let f' : Real -> Completion F := I ∘ f
  have hf' : ContDiff Real 1 f' := hf.continuousLinearMap_comp I
  have h'f' : HasCompactSupport f' := h'f.comp_left rfl
  have : ‖f' x‖ₑ <= ∫⁻ y in Iic x, ‖deriv f' y‖ₑ := by
    rw [← HasCompactSu

中文:
引理 _root_.HasCompactSupport.enorm_le_lintegral_Ici_deriv
  证明: by
  let I : F ->L[Real] Completion F := Completion.toComplL
  let f' : Real -> Completion F := I ∘ f
  have hf' : ContDiff Real 1 f' := hf.continuousLinearMap_comp I
  have h'f' : HasCompactSupport f' := h'f.comp_left rfl
  have : ‖f' x‖ₑ <= ∫⁻ y in Iic x, ‖deriv f' y‖ₑ := by
    rw [← HasCompactSu

Depends on / 依赖: Completion, Completion.enorm_coe, Completion.toComplL, ContDiff, HasCompactSupport, HasCompactSupport.integral_Iic_deriv_eq, I.differentiableAt, comp_left, continuousLinearMap_comp, convert, differentiable, differentiableAt, enorm_coe, enorm_integral_le_lintegral_enorm, f.comp_left, fderiv_comp_deriv, hf.continuousLinearMap_comp, hf.differentiable, integral_Iic_deriv_eq, one_ne_zer
-/
lemma _root_.HasCompactSupport.enorm_le_lintegral_Ici_deriv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    {f : Real -> F} (hf : ContDiff Real 1 f) (h'f : HasCompactSupport f) (x : Real) :
    ‖f x‖ₑ <= ∫⁻ y in Iic x, ‖deriv f y‖ₑ := by
  let I : F ->L[Real] Completion F := Completion.toComplL
  let f' : Real -> Completion F := I ∘ f
  have hf' : ContDiff Real 1 f' := hf.continuousLinearMap_comp I
  have h'f' : HasCompactSupport f' := h'f.comp_left rfl
  have : ‖f' x‖ₑ <= ∫⁻ y in Iic x, ‖deriv f' y‖ₑ := by
    rw [← HasCompactSupport.integral_Iic_deriv_eq hf' h'f' x]
    exact enorm_integral_le_lintegral_enorm _
  convert! this with y
  · simp [f', I, Completion.enorm_coe]
  · rw [fderiv_comp_deriv _ I.differentiableAt (hf.differentiable one_ne_zero _)]
    simp only [ContinuousLinearMap.fderiv]
    simp [I]

end IicFTC

section UnivFTC

variable {E : Type*} {f f' : Real -> E} {m n : E} [NormedAddCommGroup E]
  [NormedSpace Real E]

/--
theorem `integral_of_hasDerivAt_of_tendsto` / 定理 `integral_of_hasDerivAt_of_tendsto`

English:
theorem integral_of_hasDerivAt_of_tendsto
  statement: [CompleteSpace E]
  proof: by
  rw [← setIntegral_univ]; rw [← Set.Iic_union_Ioi (a := 0)]; rw [setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hf'.integrableOn hf'.integrableOn]; rw [integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hderiv x) hf'.integrableOn hbot]; rw [integral_Ioi_of_hasDerivAt_of_tendsto' (

中文:
定理 integral_of_hasDerivAt_of_tendsto
  结论: [完备空间 E]
  证明: by
  rw [← setIntegral_univ]; rw [← Set.Iic_union_Ioi (a := 0)]; rw [setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hf'.integrableOn hf'.integrableOn]; rw [integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hderiv x) hf'.integrableOn hbot]; rw [integral_Ioi_of_hasDerivAt_of_tendsto' (

Depends on / 依赖: Iic_disjoint_Ioi, Iic_union_Ioi, Set.Iic_union_Ioi, hderiv, integrableOn, integral_Iic_of_hasDerivAt_of_tendsto, integral_Ioi_of_hasDerivAt_of_tendsto, le_rfl, measurableSet_Ioi, setIntegral_union, setIntegral_univ
-/
theorem integral_of_hasDerivAt_of_tendsto [CompleteSpace E]
    (hderiv : forall x, HasDerivAt f (f' x) x) (hf' : Integrable f')
    (hbot : Tendsto f atBot (𝓝 m)) (htop : Tendsto f atTop (𝓝 n)) : ∫ x, f' x = n - m := by
  rw [← setIntegral_univ]; rw [← Set.Iic_union_Ioi (a := 0)]; rw [setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hf'.integrableOn hf'.integrableOn]; rw [integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hderiv x) hf'.integrableOn hbot]; rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hderiv x) hf'.integrableOn htop]
  abel

/--
theorem `integral_eq_zero_of_hasDerivAt_of_integrable` / 定理 `integral_eq_zero_of_hasDerivAt_of_integrable`

English:
theorem integral_eq_zero_of_hasDerivAt_of_integrable
  proof: by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE]
  have A : Tendsto f atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0) (fun x _hx => hderiv x)
      hf'.integrableOn hf.integrableOn
  have B : Tendsto f atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integr

中文:
定理 integral_eq_zero_of_hasDerivAt_of_integrable
  证明: by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE]
  have A : Tendsto f atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0) (fun x _hx => hderiv x)
      hf'.integrableOn hf.integrableOn
  have B : Tendsto f atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integr

Depends on / 依赖: CompleteSpace, Tendsto, hderiv, hf.integrableOn, integrableOn, integral, integral_of_hasDerivAt_of_tendsto, tendsto_zero_of_hasDerivAt_of_integrableOn_Iic, tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
-/
theorem integral_eq_zero_of_hasDerivAt_of_integrable
    (hderiv : forall x, HasDerivAt f (f' x) x) (hf' : Integrable f') (hf : Integrable f) :
    ∫ x, f' x = 0 := by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE]
  have A : Tendsto f atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0) (fun x _hx => hderiv x)
      hf'.integrableOn hf.integrableOn
  have B : Tendsto f atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun x _hx => hderiv x)
      hf'.integrableOn hf.integrableOn
  simpa using integral_of_hasDerivAt_of_tendsto hderiv hf' A B

end UnivFTC

section IoiChangeVariables

open Real

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/--
theorem `integral_deriv_smul_comp_Ioi` / 定理 `integral_deriv_smul_comp_Ioi`

English:
theorem integral_deriv_smul_comp_Ioi
  statement: {f f' : Real -> Real} {g : Real -> E} {a : Real}
  proof: by
  have eq : forall b : Real, a < b -> (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := fun b hb => by
    have i1 : Ioo (min a b) (max a b) subseteq Ioi a := by
      rw [min_eq_left hb.le]
      exact Ioo_subset_Ioi_self
    have i2 : [[a, b]] subseteq Ici a := by rw [uIcc_of_le hb.le];

中文:
定理 integral_deriv_smul_comp_Ioi
  结论: {f f' : 实数 -> 实数} {g : 实数 -> E} {a : 实数}
  证明: by
  have eq : forall b : Real, a < b -> (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := fun b hb => by
    have i1 : Ioo (min a b) (max a b) subseteq Ioi a := by
      rw [min_eq_left hb.le]
      exact Ioo_subset_Ioi_self
    have i2 : [[a, b]] subseteq Ici a := by rw [uIcc_of_le hb.le];

Depends on / 依赖: Icc_subset_Ici_self, Ioo_subset_Ioi_self, hb.le, hf.mono, hg1.mono_set, hg2.mono_set, hg_cont, hg_cont.mono, image_mono, integral_deriv_smul_comp, intervalIntegral, intervalIntegral.integral_deriv_smul_comp, mem_of_mem_of_subset, min_eq_left, mono_set, subseteq, uIcc_of_le
-/
theorem integral_deriv_smul_comp_Ioi {f f' : Real -> Real} {g : Real -> E} {a : Real}
    (hf : ContinuousOn f <| Ici a) (hft : Tendsto f atTop atTop)
    (hff' : forall x in Ioi a, HasDerivWithinAt f (f' x) (Ioi x) x)
    (hg_cont : ContinuousOn g <| f '' Ioi a) (hg1 : IntegrableOn g <| f '' Ici a)
    (hg2 : IntegrableOn (fun x => f' x • (g ∘ f) x) (Ici a)) :
    (∫ x in Ioi a, f' x • (g ∘ f) x) = ∫ u in Ioi (f a), g u := by
  have eq : forall b : Real, a < b -> (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := fun b hb => by
    have i1 : Ioo (min a b) (max a b) subseteq Ioi a := by
      rw [min_eq_left hb.le]
      exact Ioo_subset_Ioi_self
    have i2 : [[a, b]] subseteq Ici a := by rw [uIcc_of_le hb.le]; exact Icc_subset_Ici_self
    refine
      intervalIntegral.integral_deriv_smul_comp''' (hf.mono i2)
        (fun x hx => hff' x <| mem_of_mem_of_subset hx i1) (hg_cont.mono <| image_mono ?_)
        (hg1.mono_set <| image_mono ?_) (hg2.mono_set i2) <;> assumption
  rw [integrableOn_Ici_iff_integrableOn_Ioi] at hg2
  have t2 := intervalIntegral_tendsto_integral_Ioi _ hg2 tendsto_id
  have : Ioi (f a) subseteq f '' Ici a :=
Ioi_subset_Ici_self.trans
      IsPreconnected.intermediate_value_Ici isPreconnected_Ici self_mem_Ici
        (le_principal_iff.mpr <| Ici_mem_atTop _) hf hft
  have t1 := (intervalIntegral_tendsto_integral_Ioi _ (hg1.mono_set this) tendsto_id).comp hft
  exact tendsto_nhds_unique (Tendsto.congr' (eventuallyEq_of_mem (Ioi_mem_atTop a) eq) t2) t1

@[deprecated (since := "2026-03-19")]
alias integral_comp_smul_deriv_Ioi := integral_deriv_smul_comp_Ioi

/--
theorem `integral_comp_mul_deriv_Ioi` / 定理 `integral_comp_mul_deriv_Ioi`

English:
theorem integral_comp_mul_deriv_Ioi
  statement: {f f' : Real -> Real} {g : Real -> Real} {a : Real}
  proof: by
  have hg2' : IntegrableOn (fun x => f' x • (g ∘ f) x) (Ici a) := by simpa [mul_comm] using hg2
  simpa [mul_comm] using integral_deriv_smul_comp_Ioi hf hft hff' hg_cont hg1 hg2'

中文:
定理 integral_comp_mul_deriv_Ioi
  结论: {f f' : 实数 -> 实数} {g : 实数 -> 实数} {a : 实数}
  证明: by
  have hg2' : IntegrableOn (fun x => f' x • (g ∘ f) x) (Ici a) := by simpa [mul_comm] using hg2
  simpa [mul_comm] using integral_deriv_smul_comp_Ioi hf hft hff' hg_cont hg1 hg2'

Depends on / 依赖: IntegrableOn, hg_cont, integral_deriv_smul_comp_Ioi, mul_comm
-/
theorem integral_comp_mul_deriv_Ioi {f f' : Real -> Real} {g : Real -> Real} {a : Real}
    (hf : ContinuousOn f <| Ici a) (hft : Tendsto f atTop atTop)
    (hff' : forall x in Ioi a, HasDerivWithinAt f (f' x) (Ioi x) x)
    (hg_cont : ContinuousOn g <| f '' Ioi a) (hg1 : IntegrableOn g <| f '' Ici a)
    (hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici a)) :
    (∫ x in Ioi a, (g ∘ f) x * f' x) = ∫ u in Ioi (f a), g u := by
  have hg2' : IntegrableOn (fun x => f' x • (g ∘ f) x) (Ici a) := by simpa [mul_comm] using hg2
  simpa [mul_comm] using integral_deriv_smul_comp_Ioi hf hft hff' hg_cont hg1 hg2'

/--
theorem `integral_comp_rpow_Ioi` / 定理 `integral_comp_rpow_Ioi`

English:
theorem integral_comp_rpow_Ioi
  given: (g : Real -> E) {p : Real} (hp : p != 0)
  proof: by
  have a : (· ^ p) '' (Ioi 0) = Ioi (0 : Real) := by
    ext1 x; rw [mem_image]; constructor
    · rintro ⟨y, hy, rfl⟩; exact rpow_pos_of_pos hy p
    · exact fun hx => ⟨x ^ (1 / p), rpow_pos_of_pos hx _, by simp [← rpow_mul (le_of_lt hx), hp]⟩
  have := integral_image_eq_integral_abs_deriv_smul 

中文:
定理 integral_comp_rpow_Ioi
  条件: (g : 实数 -> E) {p : 实数} (hp : p != 0)
  证明: by
  have a : (· ^ p) '' (Ioi 0) = Ioi (0 : Real) := by
    ext1 x; rw [mem_image]; constructor
    · rintro ⟨y, hy, rfl⟩; exact rpow_pos_of_pos hy p
    · exact fun hx => ⟨x ^ (1 / p), rpow_pos_of_pos hx _, by simp [← rpow_mul (le_of_lt hx), hp]⟩
  have := integral_image_eq_integral_abs_deriv_smul 

Depends on / 依赖: Or.inl, hasDerivAt_rpow_const, hasDerivWithinAt, integral_image_eq_integral_abs_deriv_smul, le_of_lt, measurableSet_Ioi, mem_Ioi, mem_Ioi.mp, mem_image, rpow_left_injOn, rpow_mul, rpow_pos_of_pos, setIntegral_congr_fun
-/
theorem integral_comp_rpow_Ioi (g : Real -> E) {p : Real} (hp : p != 0) :
    ∫ x in Ioi 0, (|p| * x ^ (p - 1)) • g (x ^ p) = ∫ y in Ioi 0, g y := by
  have a : (· ^ p) '' (Ioi 0) = Ioi (0 : Real) := by
    ext1 x; rw [mem_image]; constructor
    · rintro ⟨y, hy, rfl⟩; exact rpow_pos_of_pos hy p
    · exact fun hx => ⟨x ^ (1 / p), rpow_pos_of_pos hx _, by simp [← rpow_mul (le_of_lt hx), hp]⟩
  have := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x hx => (hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp hx).ne')).hasDerivWithinAt)
    ((rpow_left_injOn hp).mono (by grind)) g
  rw [a] at this; rw [this]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [abs_mul]; rw [abs_of_nonneg (rpow_nonneg (le_of_lt hx) _)]

/--
theorem `integral_comp_rpow_Ioi_of_pos` / 定理 `integral_comp_rpow_Ioi_of_pos`

English:
theorem integral_comp_rpow_Ioi_of_pos
  given: {g : Real -> E} {p : Real} (hp : 0 < p)
  proof: by
  simpa [abs_of_nonneg hp.le] using integral_comp_rpow_Ioi g hp.ne'

中文:
定理 integral_comp_rpow_Ioi_of_pos
  条件: {g : 实数 -> E} {p : 实数} (hp : 0 < p)
  证明: by
  simpa [abs_of_nonneg hp.le] using integral_comp_rpow_Ioi g hp.ne'

Depends on / 依赖: abs_of_nonneg, hp.le, hp.ne, integral_comp_rpow_Ioi
-/
theorem integral_comp_rpow_Ioi_of_pos {g : Real -> E} {p : Real} (hp : 0 < p) :
    ∫ x in Ioi 0, (p * x ^ (p - 1)) • g (x ^ p) = ∫ y in Ioi 0, g y := by
  simpa [abs_of_nonneg hp.le] using integral_comp_rpow_Ioi g hp.ne'

/--
theorem `integral_comp_rpow_Ioi_of_pos'` / 定理 `integral_comp_rpow_Ioi_of_pos'`

English:
theorem integral_comp_rpow_Ioi_of_pos'
  given: {g : Real -> E} {p : Real} (hp : 0 < p) {c : Real} (hc : 0 <= c)
  proof: by
  have : 0 <= c ^ p⁻¹ := by positivity
  have : Ioi c = (· ^ p) '' Ioi (c ^ p⁻¹) := by
    rw [(continuous_rpow_const hp.le).continuousOn.image_Ioi_of_strictMonoOn
          ((strictMonoOn_rpow_Ici_of_exponent_pos hp).mono (by grind)) (tendsto_rpow_atTop hp)]
    simp [← rpow_mul hc, hp.ne.symm]


中文:
定理 integral_comp_rpow_Ioi_of_pos'
  条件: {g : 实数 -> E} {p : 实数} (hp : 0 < p) {c : 实数} (hc : 0 <= c)
  证明: by
  have : 0 <= c ^ p⁻¹ := by positivity
  have : Ioi c = (· ^ p) '' Ioi (c ^ p⁻¹) := by
    rw [(continuous_rpow_const hp.le).continuousOn.image_Ioi_of_strictMonoOn
          ((strictMonoOn_rpow_Ici_of_exponent_pos hp).mono (by grind)) (tendsto_rpow_atTop hp)]
    simp [← rpow_mul hc, hp.ne.symm]


Depends on / 依赖: Ioi_subset_Ici, Set.Ioi_subset_Ici, continuousOn, continuousOn.image_Ioi_of_strictMonoOn, continuous_rpow_const, hasDerivAt_rpow_const, hasDerivWithinAt, hp.le, hp.ne.symm, image_Ioi_of_strictMonoOn, integral_image_eq_integral_abs_deriv_smul, measurableSet_Ioi, positi, rpow_left_injOn, rpow_mul, strictMonoOn_rpow_Ici_of_exponent_pos, tendsto_rpow_atTop
-/
theorem integral_comp_rpow_Ioi_of_pos' {g : Real -> E} {p : Real} (hp : 0 < p) {c : Real} (hc : 0 <= c) :
    ∫ x in Ioi (c ^ p⁻¹), (p * x ^ (p - 1)) • g (x ^ p) = ∫ y in Ioi c, g y := by
  have : 0 <= c ^ p⁻¹ := by positivity
  have : Ioi c = (· ^ p) '' Ioi (c ^ p⁻¹) := by
    rw [(continuous_rpow_const hp.le).continuousOn.image_Ioi_of_strictMonoOn
          ((strictMonoOn_rpow_Ici_of_exponent_pos hp).mono (by grind)) (tendsto_rpow_atTop hp)]
    simp [← rpow_mul hc, hp.ne.symm]
  rw [this]; rw [integral_image_eq_integral_abs_deriv_smul (measurableSet_Ioi (a := c ^ p⁻¹))
      (fun _ _ => (hasDerivAt_rpow_const (by grind)).hasDerivWithinAt)
      ((rpow_left_injOn hp.ne.symm).mono (Set.Ioi_subset_Ici (by positivity)))]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  have : 0 <= x := by grind
  rw [abs_of_nonneg (by positivity)]

/--
theorem `integral_comp_exp_Ioi` / 定理 `integral_comp_exp_Ioi`

English:
theorem integral_comp_exp_Ioi
  given: (g : Real -> E) (a : Real)
  proof: by
  symm; rw [← image_exp_Ioi]
  simpa [abs_of_pos (exp_pos _)] using integral_image_eq_integral_abs_deriv_smul
      (measurableSet_Ioi (a := a)) (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt)
      (fun x _ y _ hxy => exp_injective hxy) g

中文:
定理 integral_comp_exp_Ioi
  条件: (g : 实数 -> E) (a : 实数)
  证明: by
  symm; rw [← image_exp_Ioi]
  simpa [abs_of_pos (exp_pos _)] using integral_image_eq_integral_abs_deriv_smul
      (measurableSet_Ioi (a := a)) (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt)
      (fun x _ y _ hxy => exp_injective hxy) g

Depends on / 依赖: abs_of_pos, exp_injective, exp_pos, hasDerivAt_exp, hasDerivWithinAt, image_exp_Ioi, integral_image_eq_integral_abs_deriv_smul, measurableSet_Ioi
-/
theorem integral_comp_exp_Ioi (g : Real -> E) (a : Real) :
    ∫ x in Ioi a, exp x • g (exp x) = ∫ y in Ioi (exp a), g y := by
  symm; rw [← image_exp_Ioi]
  simpa [abs_of_pos (exp_pos _)] using integral_image_eq_integral_abs_deriv_smul
      (measurableSet_Ioi (a := a)) (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt)
      (fun x _ y _ hxy => exp_injective hxy) g

/--
theorem `integrableOn_comp_exp_Ioi` / 定理 `integrableOn_comp_exp_Ioi`

English:
theorem integrableOn_comp_exp_Ioi
  given: (g : Real -> E) (a : Real)
  proof: by
  symm; rw [← image_exp_Ioi]
  simpa [abs_of_pos (exp_pos _)] using integrableOn_image_iff_integrableOn_abs_deriv_smul
      (measurableSet_Ioi (a := a)) (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt)
      (fun x _ y _ hxy => exp_injective hxy) g

中文:
定理 integrableOn_comp_exp_Ioi
  条件: (g : 实数 -> E) (a : 实数)
  证明: by
  symm; rw [← image_exp_Ioi]
  simpa [abs_of_pos (exp_pos _)] using integrableOn_image_iff_integrableOn_abs_deriv_smul
      (measurableSet_Ioi (a := a)) (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt)
      (fun x _ y _ hxy => exp_injective hxy) g

Depends on / 依赖: abs_of_pos, exp_injective, exp_pos, hasDerivAt_exp, hasDerivWithinAt, image_exp_Ioi, integrableOn_image_iff_integrableOn_abs_deriv_smul, measurableSet_Ioi
-/
theorem integrableOn_comp_exp_Ioi (g : Real -> E) (a : Real) :
    IntegrableOn (fun x => exp x • g (exp x)) (Ioi a) ↔ IntegrableOn g (Ioi (exp a)) := by
  symm; rw [← image_exp_Ioi]
  simpa [abs_of_pos (exp_pos _)] using integrableOn_image_iff_integrableOn_abs_deriv_smul
      (measurableSet_Ioi (a := a)) (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt)
      (fun x _ y _ hxy => exp_injective hxy) g

/--
theorem `integral_comp_log_Ioi` / 定理 `integral_comp_log_Ioi`

English:
theorem integral_comp_log_Ioi
  given: (g : Real -> E) {a : Real} (ha : 0 < a)
  proof: by
  simpa [exp_log ha] using (integral_comp_exp_Ioi (fun x => x⁻¹ • g (log x)) (log a)).symm

中文:
定理 integral_comp_log_Ioi
  条件: (g : 实数 -> E) {a : 实数} (ha : 0 < a)
  证明: by
  simpa [exp_log ha] using (integral_comp_exp_Ioi (fun x => x⁻¹ • g (log x)) (log a)).symm

Depends on / 依赖: exp_log, integral_comp_exp_Ioi
-/
theorem integral_comp_log_Ioi (g : Real -> E) {a : Real} (ha : 0 < a) :
    ∫ x in Ioi a, x⁻¹ • g (log x) = ∫ y in Ioi (log a), g y := by
  simpa [exp_log ha] using (integral_comp_exp_Ioi (fun x => x⁻¹ • g (log x)) (log a)).symm

/--
theorem `integrableOn_comp_log_Ioi` / 定理 `integrableOn_comp_log_Ioi`

English:
theorem integrableOn_comp_log_Ioi
  given: (g : Real -> E) {a : Real} (ha : 0 < a)
  proof: by
  symm
  simpa [exp_log ha] using integrableOn_comp_exp_Ioi (fun x => x⁻¹ • g (log x)) (log a)

中文:
定理 integrableOn_comp_log_Ioi
  条件: (g : 实数 -> E) {a : 实数} (ha : 0 < a)
  证明: by
  symm
  simpa [exp_log ha] using integrableOn_comp_exp_Ioi (fun x => x⁻¹ • g (log x)) (log a)

Depends on / 依赖: exp_log, integrableOn_comp_exp_Ioi
-/
theorem integrableOn_comp_log_Ioi (g : Real -> E) {a : Real} (ha : 0 < a) :
    IntegrableOn (fun x => x⁻¹ • g (log x)) (Ioi a) ↔ IntegrableOn g (Ioi (log a)) := by
  symm
  simpa [exp_log ha] using integrableOn_comp_exp_Ioi (fun x => x⁻¹ • g (log x)) (log a)

/--
theorem `integral_comp_mul_left_Ioi` / 定理 `integral_comp_mul_left_Ioi`

English:
theorem integral_comp_mul_left_Ioi
  given: (g : Real -> E) (a : Real) {b : Real} (hb : 0 < b)
  proof: by
  have : forall c : Real, MeasurableSet (Ioi c) := fun c => measurableSet_Ioi
  rw [← integral_indicator (this _)]; rw [← integral_indicator (this _)]; rw [← abs_of_pos (inv_pos.mpr hb)]; rw [← Measure.integral_comp_mul_left]
  congr
  ext1 x
  rw [← indicator_comp_right]; rw [preimage_const_mul_

中文:
定理 integral_comp_mul_left_Ioi
  条件: (g : 实数 -> E) (a : 实数) {b : 实数} (hb : 0 < b)
  证明: by
  have : forall c : Real, MeasurableSet (Ioi c) := fun c => measurableSet_Ioi
  rw [← integral_indicator (this _)]; rw [← integral_indicator (this _)]; rw [← abs_of_pos (inv_pos.mpr hb)]; rw [← Measure.integral_comp_mul_left]
  congr
  ext1 x
  rw [← indicator_comp_right]; rw [preimage_const_mul_

Depends on / 依赖: Function, Function.comp_def, MeasurableSet, Measure, Measure.integral_comp_mul_left, abs_of_pos, comp_def, hb.ne, indicator_comp_right, integral_comp_mul_left, integral_indicator, inv_pos, inv_pos.mpr, measurableSet_Ioi
-/
theorem integral_comp_mul_left_Ioi (g : Real -> E) (a : Real) {b : Real} (hb : 0 < b) :
    ∫ x in Ioi a, g (b * x) = b⁻¹ • ∫ x in Ioi (b * a), g x := by
  have : forall c : Real, MeasurableSet (Ioi c) := fun c => measurableSet_Ioi
  rw [← integral_indicator (this _)]; rw [← integral_indicator (this _)]; rw [← abs_of_pos (inv_pos.mpr hb)]; rw [← Measure.integral_comp_mul_left]
  congr
  ext1 x
  rw [← indicator_comp_right]; rw [preimage_const_mul_Ioi₀ _ hb]; rw [mul_div_cancel_left₀ _ hb.ne']; rw [Function.comp_def]

/--
theorem `integral_comp_mul_left_Ioi'` / 定理 `integral_comp_mul_left_Ioi'`

English:
theorem integral_comp_mul_left_Ioi'
  given: (g : Real -> E) (a : Real) {b : Real} (hb : 0 < b)
  proof: by
  simp [integral_comp_mul_left_Ioi g a hb, smul_smul, mul_inv_cancel₀ hb.ne']

中文:
定理 integral_comp_mul_left_Ioi'
  条件: (g : 实数 -> E) (a : 实数) {b : 实数} (hb : 0 < b)
  证明: by
  simp [integral_comp_mul_left_Ioi g a hb, smul_smul, mul_inv_cancel₀ hb.ne']

Depends on / 依赖: hb.ne, integral_comp_mul_left_Ioi, smul_smul
-/
theorem integral_comp_mul_left_Ioi' (g : Real -> E) (a : Real) {b : Real} (hb : 0 < b) :
    b • ∫ x in Ioi a, g (b * x) = ∫ x in Ioi (b * a), g x := by
  simp [integral_comp_mul_left_Ioi g a hb, smul_smul, mul_inv_cancel₀ hb.ne']

/--
theorem `integral_comp_mul_right_Ioi` / 定理 `integral_comp_mul_right_Ioi`

English:
theorem integral_comp_mul_right_Ioi
  given: (g : Real -> E) (a : Real) {b : Real} (hb : 0 < b)
  proof: by
  simpa [mul_comm] using integral_comp_mul_left_Ioi g a hb

中文:
定理 integral_comp_mul_right_Ioi
  条件: (g : 实数 -> E) (a : 实数) {b : 实数} (hb : 0 < b)
  证明: by
  simpa [mul_comm] using integral_comp_mul_left_Ioi g a hb

Depends on / 依赖: integral_comp_mul_left_Ioi, mul_comm
-/
theorem integral_comp_mul_right_Ioi (g : Real -> E) (a : Real) {b : Real} (hb : 0 < b) :
    ∫ x in Ioi a, g (x * b) = b⁻¹ • ∫ x in Ioi (a * b), g x := by
  simpa [mul_comm] using integral_comp_mul_left_Ioi g a hb

/--
theorem `integral_comp_mul_right_Ioi'` / 定理 `integral_comp_mul_right_Ioi'`

English:
theorem integral_comp_mul_right_Ioi'
  given: (g : Real -> E) (a : Real) {b : Real} (hb : 0 < b)
  proof: by
  simp [integral_comp_mul_right_Ioi g a hb, smul_smul, mul_inv_cancel₀ hb.ne']

中文:
定理 integral_comp_mul_right_Ioi'
  条件: (g : 实数 -> E) (a : 实数) {b : 实数} (hb : 0 < b)
  证明: by
  simp [integral_comp_mul_right_Ioi g a hb, smul_smul, mul_inv_cancel₀ hb.ne']

Depends on / 依赖: hb.ne, integral_comp_mul_right_Ioi, smul_smul
-/
theorem integral_comp_mul_right_Ioi' (g : Real -> E) (a : Real) {b : Real} (hb : 0 < b) :
    b • ∫ x in Ioi a, g (x * b) = ∫ x in Ioi (a * b), g x := by
  simp [integral_comp_mul_right_Ioi g a hb, smul_smul, mul_inv_cancel₀ hb.ne']

end IoiChangeVariables

section IoiIntegrability

open Real

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E]

/--
theorem `integrableOn_Ioi_comp_rpow_iff` / 定理 `integrableOn_Ioi_comp_rpow_iff`

English:
theorem integrableOn_Ioi_comp_rpow_iff
  given: [NormedSpace Real E] (f : Real -> E) {p : Real} (hp : p != 0)
  proof: by
  let S := Ioi (0 : Real)
  have a1 : forall x : Real, x in S -> HasDerivWithinAt (fun t : Real => t ^ p) (p * x ^ (p - 1)) S x :=
    fun x hx => (hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp hx).ne')).hasDerivWithinAt
  have a2 : InjOn (fun x : Real => x ^ p) S := by
    rcases lt_or_gt_of_ne hp w

中文:
定理 integrableOn_Ioi_comp_rpow_iff
  条件: [赋范空间 实数 E] (f : 实数 -> E) {p : 实数} (hp : p != 0)
  证明: by
  let S := Ioi (0 : Real)
  have a1 : forall x : Real, x in S -> HasDerivWithinAt (fun t : Real => t ^ p) (p * x ^ (p - 1)) S x :=
    fun x hx => (hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp hx).ne')).hasDerivWithinAt
  have a2 : InjOn (fun x : Real => x ^ p) S := by
    rcases lt_or_gt_of_ne hp w

Depends on / 依赖: HasDerivWithinAt, Or.inl, StrictAntiOn, StrictAntiOn.injOn, hasDerivAt_rpow_const, hasDerivWithinAt, le_of_lt, lt_or_gt_of_ne, mem_Ioi, mem_Ioi.mp, rpow_lt_rpow, rpow_neg, rpow_pos_of_pos
-/
theorem integrableOn_Ioi_comp_rpow_iff [NormedSpace Real E] (f : Real -> E) {p : Real} (hp : p != 0) :
    IntegrableOn (fun x => (|p| * x ^ (p - 1)) • f (x ^ p)) (Ioi 0) ↔ IntegrableOn f (Ioi 0) := by
  let S := Ioi (0 : Real)
  have a1 : forall x : Real, x in S -> HasDerivWithinAt (fun t : Real => t ^ p) (p * x ^ (p - 1)) S x :=
    fun x hx => (hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp hx).ne')).hasDerivWithinAt
  have a2 : InjOn (fun x : Real => x ^ p) S := by
    rcases lt_or_gt_of_ne hp with (h | h)
    · apply StrictAntiOn.injOn
      intro x hx y hy hxy
      rw [← inv_lt_inv₀ (rpow_pos_of_pos hx p) (rpow_pos_of_pos hy p)]; rw [← rpow_neg (le_of_lt hx)]; rw [←
        rpow_neg (le_of_lt hy)]
      exact rpow_lt_rpow (le_of_lt hx) hxy (neg_pos.mpr h)
    exact StrictMonoOn.injOn fun x hx y _hy hxy => rpow_lt_rpow (mem_Ioi.mp hx).le hxy h
  have a3 : (fun t : Real => t ^ p) '' S = S := by
    ext1 x; rw [mem_image]; constructor
    · rintro ⟨y, hy, rfl⟩; exact rpow_pos_of_pos hy p
    · intro hx; refine ⟨x ^ (1 / p), rpow_pos_of_pos hx _, ?_⟩
      rw [← rpow_mul (le_of_lt hx)]; rw [one_div_mul_cancel hp]; rw [rpow_one]
  have := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi a1 a2 f
  rw [a3] at this
  rw [this]
  refine integrableOn_congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp_rw [abs_mul, abs_of_nonneg (rpow_nonneg (le_of_lt hx) _)]

/--
theorem `integrableOn_Ioi_comp_rpow_iff'` / 定理 `integrableOn_Ioi_comp_rpow_iff'`

English:
theorem integrableOn_Ioi_comp_rpow_iff'
  given: [NormedSpace Real E] (f : Real -> E) {p : Real} (hp : p != 0)
  proof: by
  simpa only [← integrableOn_Ioi_comp_rpow_iff f hp, mul_smul] using!
    (integrable_smul_iff (abs_pos.mpr hp).ne' _).symm

中文:
定理 integrableOn_Ioi_comp_rpow_iff'
  条件: [赋范空间 实数 E] (f : 实数 -> E) {p : 实数} (hp : p != 0)
  证明: by
  simpa only [← integrableOn_Ioi_comp_rpow_iff f hp, mul_smul] using!
    (integrable_smul_iff (abs_pos.mpr hp).ne' _).symm

Depends on / 依赖: abs_pos, abs_pos.mpr, integrableOn_Ioi_comp_rpow_iff, integrable_smul_iff, mul_smul
-/
theorem integrableOn_Ioi_comp_rpow_iff' [NormedSpace Real E] (f : Real -> E) {p : Real} (hp : p != 0) :
    IntegrableOn (fun x => x ^ (p - 1) • f (x ^ p)) (Ioi 0) ↔ IntegrableOn f (Ioi 0) := by
  simpa only [← integrableOn_Ioi_comp_rpow_iff f hp, mul_smul] using!
    (integrable_smul_iff (abs_pos.mpr hp).ne' _).symm

/--
theorem `integrableOn_Ioi_comp_mul_left_iff` / 定理 `integrableOn_Ioi_comp_mul_left_iff`

English:
theorem integrableOn_Ioi_comp_mul_left_iff
  given: (f : Real -> E) (c : Real) {a : Real} (ha : 0 < a)
  proof: by
  rw [← integrable_indicator_iff (measurableSet_Ioi : MeasurableSet <| Ioi c)]
  rw [← integrable_indicator_iff (measurableSet_Ioi : MeasurableSet <| Ioi <| a * c)]
  convert! integrable_comp_mul_left_iff ((Ioi (a * c)).indicator f) ha.ne' using 2
  ext1 x
  rw [← indicator_comp_right]; rw [preim

中文:
定理 integrableOn_Ioi_comp_mul_left_iff
  条件: (f : 实数 -> E) (c : 实数) {a : 实数} (ha : 0 < a)
  证明: by
  rw [← integrable_indicator_iff (measurableSet_Ioi : MeasurableSet <| Ioi c)]
  rw [← integrable_indicator_iff (measurableSet_Ioi : MeasurableSet <| Ioi <| a * c)]
  convert! integrable_comp_mul_left_iff ((Ioi (a * c)).indicator f) ha.ne' using 2
  ext1 x
  rw [← indicator_comp_right]; rw [preim

Depends on / 依赖: Function, Function.comp_def, MeasurableSet, comp_def, convert, ha.ne, indicator, indicator_comp_right, integrable_comp_mul_left_iff, integrable_indicator_iff, measurableSet_Ioi, mul_comm
-/
theorem integrableOn_Ioi_comp_mul_left_iff (f : Real -> E) (c : Real) {a : Real} (ha : 0 < a) :
    IntegrableOn (fun x => f (a * x)) (Ioi c) ↔ IntegrableOn f (Ioi <| a * c) := by
  rw [← integrable_indicator_iff (measurableSet_Ioi : MeasurableSet <| Ioi c)]
  rw [← integrable_indicator_iff (measurableSet_Ioi : MeasurableSet <| Ioi <| a * c)]
  convert! integrable_comp_mul_left_iff ((Ioi (a * c)).indicator f) ha.ne' using 2
  ext1 x
  rw [← indicator_comp_right]; rw [preimage_const_mul_Ioi₀ _ ha]; rw [mul_comm a c]; rw [mul_div_cancel_right₀ _ ha.ne']; rw [Function.comp_def]

/--
theorem `integrableOn_Ioi_comp_mul_right_iff` / 定理 `integrableOn_Ioi_comp_mul_right_iff`

English:
theorem integrableOn_Ioi_comp_mul_right_iff
  given: (f : Real -> E) (c : Real) {a : Real} (ha : 0 < a)
  proof: by
  simpa only [mul_comm, mul_zero] using integrableOn_Ioi_comp_mul_left_iff f c ha

中文:
定理 integrableOn_Ioi_comp_mul_right_iff
  条件: (f : 实数 -> E) (c : 实数) {a : 实数} (ha : 0 < a)
  证明: by
  simpa only [mul_comm, mul_zero] using integrableOn_Ioi_comp_mul_left_iff f c ha

Depends on / 依赖: integrableOn_Ioi_comp_mul_left_iff, mul_comm, mul_zero
-/
theorem integrableOn_Ioi_comp_mul_right_iff (f : Real -> E) (c : Real) {a : Real} (ha : 0 < a) :
    IntegrableOn (fun x => f (x * a)) (Ioi c) ↔ IntegrableOn f (Ioi <| c * a) := by
  simpa only [mul_comm, mul_zero] using integrableOn_Ioi_comp_mul_left_iff f c ha

end IoiIntegrability

/-!
## Integration by parts
-/

section IntegrationByPartsBilinear

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F] [NormedAddCommGroup G] [NormedSpace Real G]
  {L : E ->L[Real] F ->L[Real] G} {u : Real -> E} {v : Real -> F} {u' : Real -> E} {v' : Real -> F}
  {m n : G}

/--
theorem `integral_bilinear_hasDerivAt_eq_sub` / 定理 `integral_bilinear_hasDerivAt_eq_sub`

English:
theorem integral_bilinear_hasDerivAt_eq_sub
  statement: [CompleteSpace G]
  proof: integral_of_hasDerivAt_of_tendsto (fun x => L.hasDerivAt_of_bilinear (hu x) (hv x))
    huv h_bot h_top

中文:
定理 integral_bilinear_hasDerivAt_eq_sub
  结论: [完备空间 G]
  证明: integral_of_hasDerivAt_of_tendsto (fun x => L.hasDerivAt_of_bilinear (hu x) (hv x))
    huv h_bot h_top

Depends on / 依赖: L.hasDerivAt_of_bilinear, h_bot, h_top, hasDerivAt_of_bilinear, integral_of_hasDerivAt_of_tendsto
-/
theorem integral_bilinear_hasDerivAt_eq_sub [CompleteSpace G]
    (hu : forall x in tsupport v, HasDerivAt u (u' x) x)
    (hv : forall x in tsupport u, HasDerivAt v (v' x) x)
    (huv : Integrable (fun x => L (u x) (v' x) + L (u' x) (v x)))
    (h_bot : Tendsto (fun x => L (u x) (v x)) atBot (𝓝 m))
    (h_top : Tendsto (fun x => L (u x) (v x)) atTop (𝓝 n)) :
    ∫ (x : Real), L (u x) (v' x) + L (u' x) (v x) = n - m :=
  integral_of_hasDerivAt_of_tendsto (fun x => L.hasDerivAt_of_bilinear (hu x) (hv x))
    huv h_bot h_top

/--
theorem `integral_bilinear_hasDerivAt_right_eq_sub` / 定理 `integral_bilinear_hasDerivAt_right_eq_sub`

English:
theorem integral_bilinear_hasDerivAt_right_eq_sub
  statement: [CompleteSpace G]
  proof: by
  rw [eq_sub_iff_add_eq]; rw [← integral_add huv' hu'v]
  exact integral_bilinear_hasDerivAt_eq_sub hu hv (huv'.add hu'v) h_bot h_top

中文:
定理 integral_bilinear_hasDerivAt_right_eq_sub
  结论: [完备空间 G]
  证明: by
  rw [eq_sub_iff_add_eq]; rw [← integral_add huv' hu'v]
  exact integral_bilinear_hasDerivAt_eq_sub hu hv (huv'.add hu'v) h_bot h_top

Depends on / 依赖: eq_sub_iff_add_eq, h_bot, h_top, integral_add, integral_bilinear_hasDerivAt_eq_sub
-/
theorem integral_bilinear_hasDerivAt_right_eq_sub [CompleteSpace G]
    (hu : forall x in tsupport v, HasDerivAt u (u' x) x)
    (hv : forall x in tsupport u, HasDerivAt v (v' x) x)
    (huv' : Integrable (fun x => L (u x) (v' x))) (hu'v : Integrable (fun x => L (u' x) (v x)))
    (h_bot : Tendsto (fun x => L (u x) (v x)) atBot (𝓝 m))
    (h_top : Tendsto (fun x => L (u x) (v x)) atTop (𝓝 n)) :
    ∫ (x : Real), L (u x) (v' x) = n - m - ∫ (x : Real), L (u' x) (v x) := by
  rw [eq_sub_iff_add_eq]; rw [← integral_add huv' hu'v]
  exact integral_bilinear_hasDerivAt_eq_sub hu hv (huv'.add hu'v) h_bot h_top

/--
theorem `integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable` / 定理 `integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable`

English:
theorem integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
  proof: by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  have I : Tendsto (fun x => L (u x) (v x)) atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
      (fun x _hx => L.hasDerivAt_of_bilinear (hu x) (hv x))
      (huv'.add hu'v).integrableOn huv.integrableOn
  ha

中文:
定理 integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
  证明: by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  have I : Tendsto (fun x => L (u x) (v x)) atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
      (fun x _hx => L.hasDerivAt_of_bilinear (hu x) (hv x))
      (huv'.add hu'v).integrableOn huv.integrableOn
  ha

Depends on / 依赖: CompleteSpace, L.hasDerivAt_of_bilinear, Tendsto, hasDerivAt_of_bilinear, huv.integrableOn, integra, integrableOn, integral, tendsto_zero_of_hasDerivAt_of_integrableOn_Iic, tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
-/
theorem integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (hu : forall x in tsupport v, HasDerivAt u (u' x) x)
    (hv : forall x in tsupport u, HasDerivAt v (v' x) x)
    (huv' : Integrable (fun x => L (u x) (v' x))) (hu'v : Integrable (fun x => L (u' x) (v x)))
    (huv : Integrable (fun x => L (u x) (v x))) :
    ∫ (x : Real), L (u x) (v' x) = - ∫ (x : Real), L (u' x) (v x) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  have I : Tendsto (fun x => L (u x) (v x)) atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
      (fun x _hx => L.hasDerivAt_of_bilinear (hu x) (hv x))
      (huv'.add hu'v).integrableOn huv.integrableOn
  have J : Tendsto (fun x => L (u x) (v x)) atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
      (fun x _hx => L.hasDerivAt_of_bilinear (hu x) (hv x))
      (huv'.add hu'v).integrableOn huv.integrableOn
  simp [integral_bilinear_hasDerivAt_right_eq_sub hu hv huv' hu'v I J]

end IntegrationByPartsBilinear

section IntegrationByPartsAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra Real A]
  {a : Real} {a' b' : A} {u : Real -> A} {v : Real -> A} {u' : Real -> A} {v' : Real -> A}

/--
theorem `integral_deriv_mul_eq_sub` / 定理 `integral_deriv_mul_eq_sub`

English:
theorem integral_deriv_mul_eq_sub
  statement: [CompleteSpace A]
  proof: by
  refine integral_of_hasDerivAt_of_tendsto (fun x => ?_) huv h_bot h_top
  simpa [add_comm] using! (ContinuousLinearMap.mul Real A).hasDerivAt_of_bilinear (hu x) (hv x)

中文:
定理 integral_deriv_mul_eq_sub
  结论: [完备空间 A]
  证明: by
  refine integral_of_hasDerivAt_of_tendsto (fun x => ?_) huv h_bot h_top
  simpa [add_comm] using! (ContinuousLinearMap.mul Real A).hasDerivAt_of_bilinear (hu x) (hv x)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, add_comm, h_bot, h_top, hasDerivAt_of_bilinear, integral_of_hasDerivAt_of_tendsto
-/
theorem integral_deriv_mul_eq_sub [CompleteSpace A]
    (hu : forall x in tsupport v, HasDerivAt u (u' x) x)
    (hv : forall x in tsupport u, HasDerivAt v (v' x) x)
    (huv : Integrable (u' * v + u * v'))
    (h_bot : Tendsto (u * v) atBot (𝓝 a')) (h_top : Tendsto (u * v) atTop (𝓝 b')) :
    ∫ (x : Real), u' x * v x + u x * v' x = b' - a' := by
  refine integral_of_hasDerivAt_of_tendsto (fun x => ?_) huv h_bot h_top
  simpa [add_comm] using! (ContinuousLinearMap.mul Real A).hasDerivAt_of_bilinear (hu x) (hv x)

/--
theorem `integral_mul_deriv_eq_deriv_mul` / 定理 `integral_mul_deriv_eq_deriv_mul`

English:
theorem integral_mul_deriv_eq_deriv_mul
  statement: [CompleteSpace A]
  proof: integral_bilinear_hasDerivAt_right_eq_sub (L := ContinuousLinearMap.mul Real A)
    hu hv huv' hu'v h_bot h_top

中文:
定理 integral_mul_deriv_eq_deriv_mul
  结论: [完备空间 A]
  证明: integral_bilinear_hasDerivAt_right_eq_sub (L := ContinuousLinearMap.mul Real A)
    hu hv huv' hu'v h_bot h_top

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, h_bot, h_top, integral_bilinear_hasDerivAt_right_eq_sub
-/
theorem integral_mul_deriv_eq_deriv_mul [CompleteSpace A]
    (hu : forall x in tsupport v, HasDerivAt u (u' x) x)
    (hv : forall x in tsupport u, HasDerivAt v (v' x) x)
    (huv' : Integrable (u * v')) (hu'v : Integrable (u' * v))
    (h_bot : Tendsto (u * v) atBot (𝓝 a')) (h_top : Tendsto (u * v) atTop (𝓝 b')) :
    ∫ (x : Real), u x * v' x = b' - a' - ∫ (x : Real), u' x * v x :=
  integral_bilinear_hasDerivAt_right_eq_sub (L := ContinuousLinearMap.mul Real A)
    hu hv huv' hu'v h_bot h_top

/--
theorem `integral_mul_deriv_eq_deriv_mul_of_integrable` / 定理 `integral_mul_deriv_eq_deriv_mul_of_integrable`

English:
theorem integral_mul_deriv_eq_deriv_mul_of_integrable
  proof: integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable (L := ContinuousLinearMap.mul Real A)
    hu hv huv' hu'v huv

中文:
定理 integral_mul_deriv_eq_deriv_mul_of_integrable
  证明: integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable (L := ContinuousLinearMap.mul Real A)
    hu hv huv' hu'v huv

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.mul, integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
-/
theorem integral_mul_deriv_eq_deriv_mul_of_integrable
    (hu : forall x in tsupport v, HasDerivAt u (u' x) x)
    (hv : forall x in tsupport u, HasDerivAt v (v' x) x)
    (huv' : Integrable (u * v')) (hu'v : Integrable (u' * v)) (huv : Integrable (u * v)) :
    ∫ (x : Real), u x * v' x = - ∫ (x : Real), u' x * v x :=
  integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable (L := ContinuousLinearMap.mul Real A)
    hu hv huv' hu'v huv

variable [CompleteSpace A]

-- TODO: also apply `Tendsto _ (𝓝[>] a) (𝓝 a')` generalization to
-- `integral_Ioi_of_hasDerivAt_of_tendsto` and `integral_Iic_of_hasDerivAt_of_tendsto`
/--
theorem `integral_Ioi_deriv_mul_eq_sub` / 定理 `integral_Ioi_deriv_mul_eq_sub`

English:
theorem integral_Ioi_deriv_mul_eq_sub
  proof: by
  rw [← Ici_sdiff_left] at h_zero
  let f := Function.update (u * v) a a'
  have hderiv : forall x in Ioi a, HasDerivAt f (u' x * v x + u x * v' x) x := by
    intro x (hx : a < x)
    apply ((hu x hx).mul (hv x hx)).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx.ne.symm] with y 

中文:
定理 integral_Ioi_deriv_mul_eq_sub
  证明: by
  rw [← Ici_sdiff_left] at h_zero
  let f := Function.update (u * v) a a'
  have hderiv : forall x in Ioi a, HasDerivAt f (u' x * v x + u x * v' x) x := by
    intro x (hx : a < x)
    apply ((hu x hx).mul (hv x hx)).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx.ne.symm] with y 

Depends on / 依赖: Function, Function.update, Function.update_of_ne, HasDerivAt, Ici_sdiff_left, Tendsto, congr_of_eventuallyEq, eventually_ne_atTop, eventually_ne_nhds, filter_upwards, h_infty, h_infty.congr, h_zero, hderiv, htendsto, hx.ne.symm, update, update_of_ne
-/
theorem integral_Ioi_deriv_mul_eq_sub
    (hu : forall x in Ioi a, HasDerivAt u (u' x) x) (hv : forall x in Ioi a, HasDerivAt v (v' x) x)
    (huv : IntegrableOn (u' * v + u * v') (Ioi a))
    (h_zero : Tendsto (u * v) (𝓝[>] a) (𝓝 a')) (h_infty : Tendsto (u * v) atTop (𝓝 b')) :
    ∫ (x : Real) in Ioi a, u' x * v x + u x * v' x = b' - a' := by
  rw [← Ici_sdiff_left] at h_zero
  let f := Function.update (u * v) a a'
  have hderiv : forall x in Ioi a, HasDerivAt f (u' x * v x + u x * v' x) x := by
    intro x (hx : a < x)
    apply ((hu x hx).mul (hv x hx)).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx.ne.symm] with y hy
    exact Function.update_of_ne hy a' (u * v)
  have htendsto : Tendsto f atTop (𝓝 b') := by
    apply h_infty.congr'
    filter_upwards [eventually_ne_atTop a] with x hx
    exact (Function.update_of_ne hx a' (u * v)).symm
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto
    (continuousWithinAt_update_same.mpr h_zero) hderiv huv htendsto

/--
theorem `integral_Ioi_mul_deriv_eq_deriv_mul` / 定理 `integral_Ioi_mul_deriv_eq_deriv_mul`

English:
theorem integral_Ioi_mul_deriv_eq_deriv_mul
  proof: by
  rw [Pi.mul_def] at huv' hu'v
  rw [eq_sub_iff_add_eq]; rw [← integral_add huv' hu'v]
  simpa only [add_comm] using integral_Ioi_deriv_mul_eq_sub hu hv (hu'v.add huv') h_zero h_infty

中文:
定理 integral_Ioi_mul_deriv_eq_deriv_mul
  证明: by
  rw [Pi.mul_def] at huv' hu'v
  rw [eq_sub_iff_add_eq]; rw [← integral_add huv' hu'v]
  simpa only [add_comm] using integral_Ioi_deriv_mul_eq_sub hu hv (hu'v.add huv') h_zero h_infty

Depends on / 依赖: Pi.mul_def, add_comm, eq_sub_iff_add_eq, h_infty, h_zero, integral_Ioi_deriv_mul_eq_sub, integral_add, mul_def, v.add
-/
theorem integral_Ioi_mul_deriv_eq_deriv_mul
    (hu : forall x in Ioi a, HasDerivAt u (u' x) x) (hv : forall x in Ioi a, HasDerivAt v (v' x) x)
    (huv' : IntegrableOn (u * v') (Ioi a)) (hu'v : IntegrableOn (u' * v) (Ioi a))
    (h_zero : Tendsto (u * v) (𝓝[>] a) (𝓝 a')) (h_infty : Tendsto (u * v) atTop (𝓝 b')) :
    ∫ (x : Real) in Ioi a, u x * v' x = b' - a' - ∫ (x : Real) in Ioi a, u' x * v x := by
  rw [Pi.mul_def] at huv' hu'v
  rw [eq_sub_iff_add_eq]; rw [← integral_add huv' hu'v]
  simpa only [add_comm] using integral_Ioi_deriv_mul_eq_sub hu hv (hu'v.add huv') h_zero h_infty

/--
theorem `integral_Iic_deriv_mul_eq_sub` / 定理 `integral_Iic_deriv_mul_eq_sub`

English:
theorem integral_Iic_deriv_mul_eq_sub
  proof: by
  rw [← Iic_sdiff_right] at h_zero
  let f := Function.update (u * v) a a'
  have hderiv : forall x in Iio a, HasDerivAt f (u' x * v x + u x * v' x) x := by
    intro x hx
    apply ((hu x hx).mul (hv x hx)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with x (hx : x < a)
    exact 

中文:
定理 integral_Iic_deriv_mul_eq_sub
  证明: by
  rw [← Iic_sdiff_right] at h_zero
  let f := Function.update (u * v) a a'
  have hderiv : forall x in Iio a, HasDerivAt f (u' x * v x + u x * v' x) x := by
    intro x hx
    apply ((hu x hx).mul (hv x hx)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with x (hx : x < a)
    exact 

Depends on / 依赖: Function, Function.update, Function.update_of_ne, HasDerivAt, Iic_sdiff_right, Iio_mem_atBot, Iio_mem_nhds, Tendsto, congr_of_eventuallyEq, filter_upwards, h_infty, h_infty.congr, h_zero, hderiv, htendsto, ne_of_lt, update, update_of_ne
-/
theorem integral_Iic_deriv_mul_eq_sub
    (hu : forall x in Iio a, HasDerivAt u (u' x) x) (hv : forall x in Iio a, HasDerivAt v (v' x) x)
    (huv : IntegrableOn (u' * v + u * v') (Iic a))
    (h_zero : Tendsto (u * v) (𝓝[<] a) (𝓝 a')) (h_infty : Tendsto (u * v) atBot (𝓝 b')) :
    ∫ (x : Real) in Iic a, u' x * v x + u x * v' x = a' - b' := by
  rw [← Iic_sdiff_right] at h_zero
  let f := Function.update (u * v) a a'
  have hderiv : forall x in Iio a, HasDerivAt f (u' x * v x + u x * v' x) x := by
    intro x hx
    apply ((hu x hx).mul (hv x hx)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with x (hx : x < a)
    exact Function.update_of_ne (ne_of_lt hx) a' (u * v)
  have htendsto : Tendsto f atBot (𝓝 b') := by
    apply h_infty.congr'
    filter_upwards [Iio_mem_atBot a] with x (hx : x < a)
    exact (Function.update_of_ne (ne_of_lt hx) a' (u * v)).symm
  simpa using integral_Iic_of_hasDerivAt_of_tendsto
    (continuousWithinAt_update_same.mpr h_zero) hderiv huv htendsto

/--
theorem `integral_Iic_mul_deriv_eq_deriv_mul` / 定理 `integral_Iic_mul_deriv_eq_deriv_mul`

English:
theorem integral_Iic_mul_deriv_eq_deriv_mul
  proof: by
  rw [Pi.mul_def] at huv' hu'v
  rw [eq_sub_iff_add_eq]; rw [← integral_add huv' hu'v]
  simpa only [add_comm] using integral_Iic_deriv_mul_eq_sub hu hv (hu'v.add huv') h_zero h_infty

中文:
定理 integral_Iic_mul_deriv_eq_deriv_mul
  证明: by
  rw [Pi.mul_def] at huv' hu'v
  rw [eq_sub_iff_add_eq]; rw [← integral_add huv' hu'v]
  simpa only [add_comm] using integral_Iic_deriv_mul_eq_sub hu hv (hu'v.add huv') h_zero h_infty

Depends on / 依赖: Pi.mul_def, add_comm, eq_sub_iff_add_eq, h_infty, h_zero, integral_Iic_deriv_mul_eq_sub, integral_add, mul_def, v.add
-/
theorem integral_Iic_mul_deriv_eq_deriv_mul
    (hu : forall x in Iio a, HasDerivAt u (u' x) x) (hv : forall x in Iio a, HasDerivAt v (v' x) x)
    (huv' : IntegrableOn (u * v') (Iic a)) (hu'v : IntegrableOn (u' * v) (Iic a))
    (h_zero : Tendsto (u * v) (𝓝[<] a) (𝓝 a')) (h_infty : Tendsto (u * v) atBot (𝓝 b')) :
    ∫ (x : Real) in Iic a, u x * v' x = a' - b' - ∫ (x : Real) in Iic a, u' x * v x := by
  rw [Pi.mul_def] at huv' hu'v
  rw [eq_sub_iff_add_eq]; rw [← integral_add huv' hu'v]
  simpa only [add_comm] using integral_Iic_deriv_mul_eq_sub hu hv (hu'v.add huv') h_zero h_infty

end IntegrationByPartsAlgebra

end MeasureTheory
