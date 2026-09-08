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
variable [MeasurableSpace β] {x : α} {ε : ℝ}

open Metric

@[measurability]
/-
**measurableSet_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_ball : MeasurableSet (Metric.ball x ε)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
-/
theorem measurableSet_ball : MeasurableSet (Metric.ball x ε) :=
  Metric.isOpen_ball.measurableSet

@[measurability]
/-
**measurableSet_closedBall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_closedBall : MeasurableSet (Metric.closedBall x ε)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
-/
theorem measurableSet_closedBall : MeasurableSet (Metric.closedBall x ε) :=
  Metric.isClosed_closedBall.measurableSet
/-
**measurable_infDist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_infDist {s : Set α} : Measurable fun x => infDist x s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Metric.continuous_infDist_pt`：continuous_infDist_pt : Continuous (infDis
t · s)
-/
theorem measurable_infDist {s : Set α} : Measurable fun x => infDist x s :=
  (continuous_infDist_pt s).measurable

@[fun_prop]
/-
**Measurable.infDist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.infDist {f : β -> α} (hf : Measurable f) {s : Set α} : Measurab
le fun x => infDist (f x) s
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_infDist`：measurable_infDist {s : Set α} : Measurable fun x =>
 infDist x s
-/
theorem Measurable.infDist {f : β → α} (hf : Measurable f) {s : Set α} :
    Measurable fun x => infDist (f x) s :=
  measurable_infDist.comp hf
/-
**measurable_infNndist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_infNndist {s : Set α} : Measurable fun x => infNndist x s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Metric.continuous_infNndist_pt`：continuous_infNndist_pt (s : Set α) : Co
ntinuous fun x => infNndist x s
-/
theorem measurable_infNndist {s : Set α} : Measurable fun x => infNndist x s :=
  (continuous_infNndist_pt s).measurable

@[fun_prop]
/-
**Measurable.infNndist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.infNndist {f : β -> α} (hf : Measurable f) {s : Set α} : Measur
able fun x => infNndist (f x) s
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_infNndist`：measurable_infNndist {s : Set α} : Measurable fun 
x => infNndist x s
-/
theorem Measurable.infNndist {f : β → α} (hf : Measurable f) {s : Set α} :
    Measurable fun x => infNndist (f x) s :=
  measurable_infNndist.comp hf

section

variable [SecondCountableTopology α]

/-
**measurable_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_dist : Measurable fun p : α × α => dist p.1 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用引理 `continuous_dist`：continuous_dist : Continuous fun p : α × α => dist p.1 
p.2
-/
theorem measurable_dist : Measurable fun p : α × α => dist p.1 p.2 :=
  continuous_dist.measurable

@[fun_prop]
/-
**Measurable.dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.dist {f g : β -> α} (hf : Measurable f) (hg : Measurable g) : M
easurable fun b => dist (f b) (g b)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable2`：Continuous.measurable2 [SecondCountableTopologyE
ither α β] {f : δ -> α} {g : δ -> β} {c : α -> β -> γ} (h : Continuous fun p : α
 × β => c p.…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用引理 `continuous_dist`：continuous_dist : Continuous fun p : α × α => dist p.1 
p.2
-/
theorem Measurable.dist {f g : β → α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun b => dist (f b) (g b) :=
  continuous_dist.measurable2 hf hg

@[fun_prop]
/-
**AEMeasurable.dist** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AEMeasurable.dist {f g : β -> α} {μ : Measure β} (hf : AEMeasurable f μ) (
hg : AEMeasurable g μ) : AEMeasurable (fun b => dist (f b) (g b)) μ
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.aemeasurable2`：Continuous.aemeasurable2 [SecondCountableTopol
ogyEither α β] {f : δ -> α} {g : δ -> β} {c : α -> β -> γ} {μ : Measure δ} (h : 
Continuous fun…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用引理 `continuous_dist`：continuous_dist : Continuous fun p : α × α => dist p.1 
p.2
-/
lemma AEMeasurable.dist {f g : β → α} {μ : Measure β}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun b ↦ dist (f b) (g b)) μ :=
  continuous_dist.aemeasurable2 hf hg
/-
**measurable_nndist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_nndist : Measurable fun p : α × α => nndist p.1 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用引理 `continuous_nndist`：continuous_nndist : Continuous fun p : α × α => nndis
t p.1 p.2
-/
theorem measurable_nndist : Measurable fun p : α × α => nndist p.1 p.2 :=
  continuous_nndist.measurable

@[fun_prop]
/-
**Measurable.nndist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.nndist {f g : β -> α} (hf : Measurable f) (hg : Measurable g) :
 Measurable fun b => nndist (f b) (g b)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable2`：Continuous.measurable2 [SecondCountableTopologyE
ither α β] {f : δ -> α} {g : δ -> β} {c : α -> β -> γ} (h : Continuous fun p : α
 × β => c p.…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用引理 `continuous_nndist`：continuous_nndist : Continuous fun p : α × α => nndis
t p.1 p.2
-/
theorem Measurable.nndist {f g : β → α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun b => nndist (f b) (g b) :=
  continuous_nndist.measurable2 hf hg

end

end PseudoMetricSpace

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
variable [MeasurableSpace β] {x : α} {ε : ℝ≥0∞}

open Metric

@[measurability]
/-
**measurableSet_eball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_eball : MeasurableSet (Metric.eball x ε)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `Metric.isOpen_eball`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x : α
} {ε : ENNReal}, IsOpen (Metric.eball x ε)
-/
theorem measurableSet_eball : MeasurableSet (Metric.eball x ε) :=
  Metric.isOpen_eball.measurableSet

@[fun_prop]
/-
**measurable_edist_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_edist_right : Measurable (edist x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Continuous.edist`：Continuous.edist [TopologicalSpace β] {f g : β -> α} (
hf : Continuous f) (hg : Continuous g) : Continuous fun b => edist (f b) (g b)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
-/
theorem measurable_edist_right : Measurable (edist x) := by fun_prop

@[fun_prop]
/-
**measurable_edist_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_edist_left : Measurable fun y => edist y x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Continuous.edist`：Continuous.edist [TopologicalSpace β] {f g : β -> α} (
hf : Continuous f) (hg : Continuous g) : Continuous fun b => edist (f b) (g b)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem measurable_edist_left : Measurable fun y ↦ edist y x := by fun_prop
/-
**measurable_infEDist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_infEDist {s : Set α} : Measurable fun x => infEDist x s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Metric.continuous_infEDist`：continuous_infEDist : Continuous fun x => in
fEDist x s
-/
theorem measurable_infEDist {s : Set α} : Measurable fun x => infEDist x s :=
  continuous_infEDist.measurable

@[deprecated (since := "2026-01-08")]
alias measurable_infEdist := measurable_infEDist

@[fun_prop]
/-
**Measurable.infEDist** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoEMetricSpace α] [inst_1 : Me
asurableSpace α] [OpensMeasurableSpace α]   [inst_3 : MeasurableSpace β] {f : β 
→ α}, Measurable f → ∀ {s : Set α}, Measurable fun x => Metric.infEDist (f x) s
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_infEDist`：measurable_infEDist {s : Set α} : Measurable fun x 
=> infEDist x s
-/
protected theorem Measurable.infEDist {f : β → α} (hf : Measurable f) {s : Set α} :
    Measurable fun x => infEDist (f x) s :=
  measurable_infEDist.comp hf

@[deprecated (since := "2026-01-08")]
alias Measurable.infEdist := Measurable.infEDist

/-- If a set has a closed thickening with finite measure, then the measure of its `r`-closed
thickenings converges to the measure of its closure as `r` tends to `0`. -/
/-
**tendsto_measure_cthickening** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_measure_cthickening {μ : Measure α} {s : Set α} (hs : exists R > 0
, μ (cthickening R s) != ∞) : Tendsto (fun r => μ (cthickening r s)) (𝓝 0) (𝓝 (μ
 (closure s)))
参数：hs : exists R > 0, μ (cthickening R s) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.closure_eq_iInter_cthickening`：closure_eq_iInter_cthickening (E :
 Set α) : closure E = ⋂ (δ : Real) (_ : 0 < δ), cthickening δ E
· 使用定理 `MeasureTheory.tendsto_measure_biInter_gt`：tendsto_measure_biInter_gt {ι 
: Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [FirstCountableT
opology ι] {s : ι -> Set α} {a…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IsClosed.nullMeasurableSet`：IsClosed.nullMeasurableSet {μ} (h : IsClosed
 s) : NullMeasurableSet s μ
· 使用定理 `Metric.isClosed_cthickening`：isClosed_cthickening {δ : Real} {E : Set α}
 : IsClosed (cthickening δ E)
· 使用定理 `Metric.cthickening_mono`：cthickening_mono {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂
) (E : Set α) : cthickening δ₁ E subseteq cthickening δ₂ E
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Metric.cthickening_of_nonpos`：cthickening_of_nonpos {δ : Real} (hδ : δ <
= 0) (E : Set α) : cthickening δ E = closure E
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsLE_sup_nhdsGT`：nhdsLE_sup_nhdsGT (a : α) : 𝓝[<=] a ⊔ 𝓝[>] a = 𝓝 a
· 使用定理 `Filter.Tendsto.sup`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y : Filter β},   Filter.Tendsto f x₁ y → Filter.Tendsto f x₂ y → Fil
ter.Tend…

--- 原说明 ---
If a set has a closed thickening with finite measure, then the measure of its `r
`-closed
thickenings converges to the measure of its closure as `r` tends to `0`.
-/
theorem tendsto_measure_cthickening {μ : Measure α} {s : Set α}
    (hs : ∃ R > 0, μ (cthickening R s) ≠ ∞) :
    Tendsto (fun r => μ (cthickening r s)) (𝓝 0) (𝓝 (μ (closure s))) := by
  have A : Tendsto (fun r => μ (cthickening r s)) (𝓝[Ioi 0] 0) (𝓝 (μ (closure s))) := by
    rw [closure_eq_iInter_cthickening]
    exact
      tendsto_measure_biInter_gt (fun r _ => isClosed_cthickening.nullMeasurableSet)
        (fun i j _ ij => cthickening_mono ij _) hs
  have B : Tendsto (fun r => μ (cthickening r s)) (𝓝[Iic 0] 0) (𝓝 (μ (closure s))) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin (α := ℝ)] with _ hr
    rw [cthickening_of_nonpos hr]
  convert! B.sup A
  exact (nhdsLE_sup_nhdsGT 0).symm

/-- If a closed set has a closed thickening with finite measure, then the measure of its closed
`r`-thickenings converge to its measure as `r` tends to `0`. -/
/-
**tendsto_measure_cthickening_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_measure_cthickening_of_isClosed {μ : Measure α} {s : Set α} (hs : 
exists R > 0, μ (cthickening R s) != ∞) (h's : IsClosed s) : Tendsto (fun r => μ
 (cthickening r s)) (𝓝 0) (𝓝 (μ s))
参数：hs : exists R > 0, μ (cthickening R s) != ∞；h's : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `tendsto_measure_cthickening`：tendsto_measure_cthickening {μ : Measure α}
 {s : Set α} (hs : exists R > 0, μ (cthickening R s) != ∞) : Tendsto (fun r => μ
 (cthickening r s…

--- 原说明 ---
If a closed set has a closed thickening with finite measure, then the measure of
 its closed
`r`-thickenings converge to its measure as `r` tends to `0`.
-/
theorem tendsto_measure_cthickening_of_isClosed {μ : Measure α} {s : Set α}
    (hs : ∃ R > 0, μ (cthickening R s) ≠ ∞) (h's : IsClosed s) :
    Tendsto (fun r => μ (cthickening r s)) (𝓝 0) (𝓝 (μ s)) := by
  convert! tendsto_measure_cthickening hs
  exact h's.closure_eq.symm

/-- If a set has a thickening with finite measure, then the measures of its `r`-thickenings
converge to the measure of its closure as `r > 0` tends to `0`. -/
/-
**tendsto_measure_thickening** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_measure_thickening {μ : Measure α} {s : Set α} (hs : exists R > 0,
 μ (thickening R s) != ∞) : Tendsto (fun r => μ (thickening r s)) (𝓝[>] 0) (𝓝 (μ
 (closure s)))
参数：hs : exists R > 0, μ (thickening R s) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.closure_eq_iInter_thickening`：closure_eq_iInter_thickening (E : S
et α) : closure E = ⋂ (δ : Real) (_ : 0 < δ), thickening δ E
· 使用定理 `MeasureTheory.tendsto_measure_biInter_gt`：tendsto_measure_biInter_gt {ι 
: Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [FirstCountableT
opology ι] {s : ι -> Set α} {a…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IsOpen.nullMeasurableSet`：IsOpen.nullMeasurableSet {μ} (h : IsOpen s) : 
NullMeasurableSet s μ
· 使用定理 `Metric.isOpen_thickening`：isOpen_thickening {δ : Real} {E : Set α} : IsO
pen (thickening δ E)
· 使用定理 `Metric.thickening_mono`：thickening_mono {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) 
(E : Set α) : thickening δ₁ E subseteq thickening δ₂ E

--- 原说明 ---
If a set has a thickening with finite measure, then the measures of its `r`-thic
kenings
converge to the measure of its closure as `r > 0` tends to `0`.
-/
theorem tendsto_measure_thickening {μ : Measure α} {s : Set α}
    (hs : ∃ R > 0, μ (thickening R s) ≠ ∞) :
    Tendsto (fun r => μ (thickening r s)) (𝓝[>] 0) (𝓝 (μ (closure s))) := by
  rw [closure_eq_iInter_thickening]
  exact tendsto_measure_biInter_gt (fun r _ => isOpen_thickening.nullMeasurableSet)
      (fun i j _ ij => thickening_mono ij _) hs

/-- If a closed set has a thickening with finite measure, then the measure of its
`r`-thickenings converge to its measure as `r > 0` tends to `0`. -/
/-
**tendsto_measure_thickening_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_measure_thickening_of_isClosed {μ : Measure α} {s : Set α} (hs : e
xists R > 0, μ (thickening R s) != ∞) (h's : IsClosed s) : Tendsto (fun r => μ (
thickening r s)) (𝓝[>] 0) (𝓝 (μ s))
参数：hs : exists R > 0, μ (thickening R s) != ∞；h's : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `tendsto_measure_thickening`：tendsto_measure_thickening {μ : Measure α} {
s : Set α} (hs : exists R > 0, μ (thickening R s) != ∞) : Tendsto (fun r => μ (t
hickening r s)) …

--- 原说明 ---
If a closed set has a thickening with finite measure, then the measure of its
`r`-thickenings converge to its measure as `r > 0` tends to `0`.
-/
theorem tendsto_measure_thickening_of_isClosed {μ : Measure α} {s : Set α}
    (hs : ∃ R > 0, μ (thickening R s) ≠ ∞) (h's : IsClosed s) :
    Tendsto (fun r => μ (thickening r s)) (𝓝[>] 0) (𝓝 (μ s)) := by
  convert! tendsto_measure_thickening hs
  exact h's.closure_eq.symm

variable [SecondCountableTopology α]
/-
**measurable_edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_edist : Measurable fun p : α × α => edist p.1 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `continuous_edist`：continuous_edist : Continuous fun p : α × α => edist p
.1 p.2
-/
theorem measurable_edist : Measurable fun p : α × α => edist p.1 p.2 :=
  continuous_edist.measurable

@[fun_prop]
/-
**Measurable.edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.edist {f g : β -> α} (hf : Measurable f) (hg : Measurable g) : 
Measurable fun b => edist (f b) (g b)
参数：hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable2`：Continuous.measurable2 [SecondCountableTopologyE
ither α β] {f : δ -> α} {g : δ -> β} {c : α -> β -> γ} (h : Continuous fun p : α
 × β => c p.…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `continuous_edist`：continuous_edist : Continuous fun p : α × α => edist p
.1 p.2
-/
theorem Measurable.edist {f g : β → α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun b => edist (f b) (g b) :=
  continuous_edist.measurable2 hf hg

@[fun_prop]
/-
**AEMeasurable.edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.edist {f g : β -> α} {μ : Measure β} (hf : AEMeasurable f μ) 
(hg : AEMeasurable g μ) : AEMeasurable (fun a => edist (f a) (g a)) μ
参数：hf : AEMeasurable f μ；hg : AEMeasurable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.aemeasurable2`：Continuous.aemeasurable2 [SecondCountableTopol
ogyEither α β] {f : δ -> α} {g : δ -> β} {c : α -> β -> γ} {μ : Measure δ} (h : 
Continuous fun…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `continuous_edist`：continuous_edist : Continuous fun p : α × α => edist p
.1 p.2
-/
theorem AEMeasurable.edist {f g : β → α} {μ : Measure β} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (fun a => edist (f a) (g a)) μ :=
  continuous_edist.aemeasurable2 hf hg

end PseudoEMetricSpace

/-- Given a compact set in a proper space, the measure of its `r`-closed thickenings converges to
its measure as `r` tends to `0`. -/
/-
**tendsto_measure_cthickening_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_measure_cthickening_of_isCompact [MetricSpace α] [MeasurableSpace 
α] [OpensMeasurableSpace α] [ProperSpace α] {μ : Measure α} [IsFiniteMeasureOnCo
mpacts μ] {s : Set α} (hs : IsCompact s) : Tendsto (fun r => μ (Metric.cthickeni
ng r s)) (𝓝 0) (𝓝 (μ s))
参数：hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_measure_cthickening_of_isClosed`：tendsto_measure_cthickening_of_
isClosed {μ : Measure α} {s : Set α} (hs : exists R > 0, μ (cthickening R s) != 
∞) (h's : IsClosed s) : Tends…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Bornology.IsBounded.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} [inst : PseudoMetricSpace α] [ProperSpace α] {μ : MeasureTheory.Measure α}
   [MeasureTheory.IsFini…
· 使用定理 `Bornology.IsBounded.cthickening`：∀ {α : Type u_2} [inst : PseudoMetricSp
ace α] {δ : ℝ} {E : Set α},   Bornology.IsBounded E → Bornology.IsBounded (Metri
c.cthickening δ E)
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α

--- 原说明 ---
Given a compact set in a proper space, the measure of its `r`-closed thickenings
 converges to
its measure as `r` tends to `0`.
-/
theorem tendsto_measure_cthickening_of_isCompact [MetricSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [ProperSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {s : Set α} (hs : IsCompact s) :
    Tendsto (fun r => μ (Metric.cthickening r s)) (𝓝 0) (𝓝 (μ s)) :=
  tendsto_measure_cthickening_of_isClosed
    ⟨1, zero_lt_one, hs.isBounded.cthickening.measure_lt_top.ne⟩ hs.isClosed

/-- If a measurable space is countably generated and separates points, it arises as
the Borel sets of some second countable t4 topology (i.e. a separable metrizable one). -/
/-
**exists_borelSpace_of_countablyGenerated_of_separatesPoints** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：exists_borelSpace_of_countablyGenerated_of_separatesPoints (α : Type*) [m 
: MeasurableSpace α] [CountablyGenerated α] [SeparatesPoints α] : exists _ : Top
ologicalSpace α, SecondCountableTopology α ∧ T4Space α ∧ BorelSpace α
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.measurableEquiv_nat_bool_of_countablyGenerated`：measurab
leEquiv_nat_bool_of_countablyGenerated [MeasurableSpace α] [CountablyGenerated α
] [SeparatesPoints α] : exists s : Set (Nat -> Bool)…
· 使用定理 `Topology.IsInducing.induced`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace Y] (f : X → Y), Topology.IsInducing f
· 使用定理 `Homeomorph.secondCountableTopology`：∀ {X : Type u_1} {Y : Type u_2} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [SecondCountableTopology Y
]   (h : X ≃ₜ Y), Second…
· 使用定理 `TopologicalSpace.Subtype.secondCountableTopology`：∀ {α : Type u} [t : To
pologicalSpace α] (s : Set α) [SecondCountableTopology α], SecondCountableTopolo
gy ↑s
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `TopologicalSpace.DiscreteTopology.metrizableSpace`：∀ {X : Type u_2} [ins
t : TopologicalSpace X] [DiscreteTopology X], TopologicalSpace.MetrizableSpace X
· 使用定理 `instDiscreteTopologyBool`：DiscreteTopology Bool
· 使用定理 `Homeomorph.t4Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T4Space X] (h : X ≃ₜ Y),   T4Space Y
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `instT1SpaceForall`：∀ {ι : Type u_3} {X : ι → Type u_4} [inst : (i : ι) →
 TopologicalSpace (X i)] [∀ (i : ι), T1Space (X i)],   T1Space ((i : ι) → X i)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `instCompletelyNormalSpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSp
ace X] [CompletelyNormalSpace X] {p : X → Prop},   CompletelyNormalSpace { x // 
p x }
· 使用定理 `CompletelyNormalSpace.of_regularSpace_secondCountableTopology`：∀ {X : Ty
pe u_1} [inst : TopologicalSpace X] [RegularSpace X] [SecondCountableTopology X]
, CompletelyNormalSpace X
· 使用定理 `instRegularSpaceForall`：∀ {ι : Type u_3} {X : ι → Type u_4} [inst : (i :
 ι) → TopologicalSpace (X i)] [∀ (i : ι), RegularSpace (X i)],   RegularSpace ((
i : ι) → X i…
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用引理 `MeasurableEmbedding.borelSpace`：MeasurableEmbedding.borelSpace {α β : Ty
pe*} [MeasurableSpace α] [TopologicalSpace α] [MeasurableSpace β] [TopologicalSp
ace β] [hβ : BorelSp…
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h

--- 原说明 ---
If a measurable space is countably generated and separates points, it arises as
the Borel sets of some second countable t4 topology (i.e. a separable metrizable
 one).
-/
theorem exists_borelSpace_of_countablyGenerated_of_separatesPoints (α : Type*)
    [m : MeasurableSpace α] [CountablyGenerated α] [SeparatesPoints α] :
    ∃ _ : TopologicalSpace α, SecondCountableTopology α ∧ T4Space α ∧ BorelSpace α := by
  rcases measurableEquiv_nat_bool_of_countablyGenerated α with ⟨s, ⟨f⟩⟩
  let := induced f inferInstance
  let F := f.toEquiv.toHomeomorphOfIsInducing <| .induced _
  exact ⟨inferInstance, F.secondCountableTopology, F.symm.t4Space,
    f.measurableEmbedding.borelSpace F.isInducing⟩

/-- If a measurable space on `α` is countably generated and separates points, there is some
second countable t4 topology on `α` (i.e. a separable metrizable one) for which every
open set is measurable. -/
/-
**exists_opensMeasurableSpace_of_countablySeparated** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：exists_opensMeasurableSpace_of_countablySeparated (α : Type*) [m : Measura
bleSpace α] [CountablySeparated α] : exists _ : TopologicalSpace α, SecondCounta
bleTopology α ∧ T4Space α ∧ OpensMeasurableSpace α
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.exists_countablyGenerated_le_of_countablySeparated`：exis
ts_countablyGenerated_le_of_countablySeparated [m : MeasurableSpace α] [h : Coun
tablySeparated α] : exists m' : MeasurableSpace α, @Coun…
· 使用定理 `exists_borelSpace_of_countablyGenerated_of_separatesPoints`：exists_borel
Space_of_countablyGenerated_of_separatesPoints (α : Type*) [m : MeasurableSpace 
α] [CountablyGenerated α] [SeparatesPoints α] : …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BorelSpace.measurable_eq`：∀ {α : Type u_6} {inst : TopologicalSpace α} {
inst_1 : MeasurableSpace α} [self : BorelSpace α], inst_1 = borel α

--- 原说明 ---
If a measurable space on `α` is countably generated and separates points, there 
is some
second countable t4 topology on `α` (i.e. a separable metrizable one) for which 
every
open set is measurable.
-/
theorem exists_opensMeasurableSpace_of_countablySeparated (α : Type*)
    [m : MeasurableSpace α] [CountablySeparated α] :
    ∃ _ : TopologicalSpace α, SecondCountableTopology α ∧ T4Space α ∧ OpensMeasurableSpace α := by
  rcases exists_countablyGenerated_le_of_countablySeparated α with ⟨m', _, _, m'le⟩
  rcases exists_borelSpace_of_countablyGenerated_of_separatesPoints (m := m') with ⟨τ, _, _, τm'⟩
  exact ⟨τ, ‹_›, ‹_›, @OpensMeasurableSpace.mk _ _ m (τm'.measurable_eq.symm.le.trans m'le)⟩


section ContinuousENorm

variable {ε : Type*} [MeasurableSpace ε] [TopologicalSpace ε] [ContinuousENorm ε]
  [OpensMeasurableSpace ε] [MeasurableSpace β]

@[fun_prop]
/-
**measurable_enorm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurable_enorm : Measurable (enorm : ε -> Real>=0∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用引理 `continuous_enorm`：continuous_enorm : Continuous fun a : E => ‖a‖ₑ
-/
lemma measurable_enorm : Measurable (enorm : ε → ℝ≥0∞) := continuous_enorm.measurable

@[fun_prop]
/-
**Measurable.enorm** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {β : Type u_2} {ε : Type u_5} [inst : MeasurableSpace ε] [inst_1 : Topol
ogicalSpace ε] [inst_2 : ContinuousENorm ε]   [OpensMeasurableSpace ε] [inst_4 :
 MeasurableSpace β] {f : β → ε}, Measurable f → Measurable fun x => ‖f x‖ₑ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用引理 `measurable_enorm`：measurable_enorm : Measurable (enorm : ε -> Real>=0∞)
-/
protected lemma Measurable.enorm {f : β → ε} (hf : Measurable f) : Measurable (‖f ·‖ₑ) :=
  measurable_enorm.comp hf

@[fun_prop]
/-
**AEMeasurable.enorm** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {β : Type u_2} {ε : Type u_5} [inst : MeasurableSpace ε] [inst_1 : Topol
ogicalSpace ε] [inst_2 : ContinuousENorm ε]   [OpensMeasurableSpace ε] [inst_4 :
 MeasurableSpace β] {f : β → ε} {μ : MeasureTheory.Measure β},   AEMeasurable f 
μ → AEMeasurable (fun x => ‖f x‖ₑ) μ
参数：fun x => ‖f x‖ₑ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用引理 `measurable_enorm`：measurable_enorm : Measurable (enorm : ε -> Real>=0∞)
-/
protected lemma AEMeasurable.enorm {f : β → ε} {μ : Measure β} (hf : AEMeasurable f μ) :
    AEMeasurable (‖f ·‖ₑ) μ :=
  measurable_enorm.comp_aemeasurable hf

end ContinuousENorm

section NormedAddCommGroup

variable [MeasurableSpace α] [NormedAddCommGroup α] [OpensMeasurableSpace α] [MeasurableSpace β]

@[fun_prop]
/-
**measurable_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_norm : Measurable (norm : α -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
-/
theorem measurable_norm : Measurable (norm : α → ℝ) :=
  continuous_norm.measurable

@[fun_prop]
/-
**Measurable.norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.norm {f : β -> α} (hf : Measurable f) : Measurable fun a => nor
m (f a)
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_norm`：measurable_norm : Measurable (norm : α -> Real)
-/
theorem Measurable.norm {f : β → α} (hf : Measurable f) : Measurable fun a => norm (f a) :=
  measurable_norm.comp hf

@[fun_prop]
/-
**AEMeasurable.norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.norm {f : β -> α} {μ : Measure β} (hf : AEMeasurable f μ) : A
EMeasurable (fun a => norm (f a)) μ
参数：hf : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `measurable_norm`：measurable_norm : Measurable (norm : α -> Real)
-/
theorem AEMeasurable.norm {f : β → α} {μ : Measure β} (hf : AEMeasurable f μ) :
    AEMeasurable (fun a => norm (f a)) μ :=
  measurable_norm.comp_aemeasurable hf
/-
**measurable_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_nnnorm : Measurable (nnnorm : α -> Real>=0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `continuous_nnnorm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Conti
nuous fun a => ‖a‖₊
-/
theorem measurable_nnnorm : Measurable (nnnorm : α → ℝ≥0) :=
  continuous_nnnorm.measurable

@[fun_prop]
/-
**Measurable.nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup α] [OpensMeasurableSpace α]   [inst_3 : MeasurableSpace β] {f : β 
→ α}, Measurable f → Measurable fun a => ‖f a‖₊
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_nnnorm`：measurable_nnnorm : Measurable (nnnorm : α -> Real>=0
)
-/
protected theorem Measurable.nnnorm {f : β → α} (hf : Measurable f) : Measurable fun a => ‖f a‖₊ :=
  measurable_nnnorm.comp hf

@[fun_prop]
/-
**AEMeasurable.nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `AEMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup α] [OpensMeasurableSpace α]   [inst_3 : MeasurableSpace β] {f : β 
→ α} {μ : MeasureTheory.Measure β},   AEMeasurable f μ → AEMeasurable (fun a => 
‖f a‖₊) μ
参数：fun a => ‖f a‖₊。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `measurable_nnnorm`：measurable_nnnorm : Measurable (nnnorm : α -> Real>=0
)
-/
protected lemma AEMeasurable.nnnorm {f : β → α} {μ : Measure β} (hf : AEMeasurable f μ) :
    AEMeasurable (fun a => ‖f a‖₊) μ :=
  measurable_nnnorm.comp_aemeasurable hf

end NormedAddCommGroup

