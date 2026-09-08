/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Jensen's inequality for integrals

In this file we prove several forms of Jensen's inequality for integrals.

- for convex sets: `Convex.average_mem`, `Convex.set_average_mem`, `Convex.integral_mem`;

- for convex functions: `ConvexOn.average_mem_epigraph`, `ConvexOn.map_average_le`,
  `ConvexOn.set_average_mem_epigraph`, `ConvexOn.map_set_average_le`, `ConvexOn.map_integral_le`;

- for strictly convex sets: `StrictConvex.ae_eq_const_or_average_mem_interior`;

- for a closed ball in a strictly convex normed space:
  `ae_eq_const_or_norm_integral_lt_of_norm_le_const`;

- for strictly convex functions: `StrictConvexOn.ae_eq_const_or_map_average_lt`.

## TODO

- Use a typeclass for strict convexity of a closed ball.

## Tags

convex, integral, center mass, average value, Jensen's inequality
-/

public section


open MeasureTheory MeasureTheory.Measure Metric Set Filter TopologicalSpace Function

open scoped Topology ENNReal Convex

variable {α E : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure α} {s : Set E} {t : Set α} {f : α → E} {g : E → ℝ} {C : ℝ}

/-!
### Non-strict Jensen's inequality
-/


/-- If `μ` is a probability measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the expected value of `f` belongs to `s`:
`∫ x, f x ∂μ ∈ s`. See also `Convex.sum_mem` for a finite sum version of this lemma. -/
/-
**Convex.integral_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.integral_mem [IsProbabilityMeasure μ] (hs : Convex Real s) (hsc : I
sClosed s) (hf : forallᵐ x ∂μ, f x in s) (hfi : Integrable f μ) : (∫ x, f x ∂μ) 
in s
参数：hs : Convex Real s；hsc : IsClosed s；hf : forallᵐ x ∂μ, f x in s；hfi : Integra
ble f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `TopologicalSpace.IsSeparable.separableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] {s : Set X},   Topo
logicalSpace.IsSeparable s → Topo…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TopologicalSpace.IsSeparable.mono`：∀ {α : Type u} [t : TopologicalSpace 
α] {s u : Set α},   TopologicalSpace.IsSeparable s → u ⊆ s → TopologicalSpace.Is
Separable u
· 使用定理 `MeasureTheory.StronglyMeasurable.isSeparable_range`：∀ {α : Type u_1} {β 
: Type u_2} {f : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β],   M
easureTheory.StronglyMeasurable f → Topo…
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `MeasureTheory.Measure.ae.neBot`：∀ {α : Type u_1} {m0 : MeasurableSpace α
} {μ : MeasureTheory.Measure α} [NeZero μ], (MeasureTheory.ae μ).NeBot
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.EventuallyEq.rw`：∀ {α : Type u} {β : Type v} {l : Filter α} {f g 
: α → β},   f =ᶠ[l] g → ∀ (p : α → β → Prop), (∀ᶠ (x : α) in l, p x (f x)) → ∀ᶠ 
(x : α) in l…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `MeasureTheory.tendsto_integral_approxOn_of_measurable`：tendsto_integral_
approxOn_of_measurable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {f :
 α -> E} {s : Set E} [SeparableSpace s] (hf…
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
If `μ` is a probability measure on `α`, `s` is a convex closed set in `E`, and `
f` is an
integrable function sending `μ`-a.e. points to `s`, then the expected value of `
f` belongs to `s`:
`∫ x, f x ∂μ ∈ s`. See also `Convex.sum_mem` for a finite sum version of this le
mma.
-/
theorem Convex.integral_mem [IsProbabilityMeasure μ] (hs : Convex ℝ s) (hsc : IsClosed s)
    (hf : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) : (∫ x, f x ∂μ) ∈ s := by
  borelize E
  rcases hfi.aestronglyMeasurable with ⟨g, hgm, hfg⟩
  have : SeparableSpace (range g ∩ s : Set E) :=
    (hgm.isSeparable_range.mono inter_subset_left).separableSpace
  obtain ⟨y₀, h₀⟩ : (range g ∩ s).Nonempty := by
    rcases (hf.and hfg).exists with ⟨x₀, h₀⟩
    exact ⟨f x₀, by simp only [h₀.2, mem_range_self], h₀.1⟩
  rw [integral_congr_ae hfg]; rw [integrable_congr hfg] at hfi
  have hg : ∀ᵐ x ∂μ, g x ∈ closure (range g ∩ s) := by
    filter_upwards [hfg.rw (fun _ y => y ∈ s) hf] with x hx
    apply subset_closure
    exact ⟨mem_range_self _, hx⟩
  set G : ℕ → SimpleFunc α E := SimpleFunc.approxOn _ hgm.measurable (range g ∩ s) y₀ h₀
  have : Tendsto (fun n => (G n).integral μ) atTop (𝓝 <| ∫ x, g x ∂μ) :=
    tendsto_integral_approxOn_of_measurable hfi _ hg _ (integrable_const _)
  refine hsc.mem_of_tendsto this (Eventually.of_forall fun n => hs.sum_mem ?_ ?_ ?_)
  · exact fun _ _ => ENNReal.toReal_nonneg
  · simp_rw [measureReal_def]
    rw [← ENNReal.toReal_sum, (G n).sum_range_measure_preimage_singleton, measure_univ,
      ENNReal.toReal_one]
    finiteness
  · simp only [SimpleFunc.mem_range, forall_mem_range]
    intro x
    apply (range g).inter_subset_right
    exact SimpleFunc.approxOn_mem hgm.measurable h₀ _ _

/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `s`:
`⨍ x, f x ∂μ ∈ s`. See also `Convex.centerMass_mem` for a finite sum version of this lemma. -/
/-
**Convex.average_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.average_mem [IsFiniteMeasure μ] [NeZero μ] (hs : Convex Real s) (hs
c : IsClosed s) (hfs : forallᵐ x ∂μ, f x in s) (hfi : Integrable f μ) : (⨍ x, f 
x ∂μ) in s
参数：hs : Convex Real s；hsc : IsClosed s；hfs : forallᵐ x ∂μ, f x in s；hfi : Integr
able f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Convex.integral_mem`：Convex.integral_mem [IsProbabilityMeasure μ] (hs : 
Convex Real s) (hsc : IsClosed s) (hf : forallᵐ x ∂μ, f x in s) (hfi : Integrabl
e f μ) : …
· 使用定理 `MeasureTheory.Measure.ae_mono'`：∀ {α : Type u_1} {mα : MeasurableSpace α
} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν → MeasureTheory.ae
 μ ≤ MeasureTheory.a…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.smul_absolutelyContinuous`：smul_absolutelyContinuo
us {c : Real>=0∞} : c • μ ≪ μ
· 使用定理 `MeasureTheory.Integrable.to_average`：∀ {α : Type u_1} {m : MeasurableSpa
ce α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]  
 [inst_1 : ESeminormedAdd…

--- 原说明 ---
If `μ` is a non-zero finite measure on `α`, `s` is a convex closed set in `E`, a
nd `f` is an
integrable function sending `μ`-a.e. points to `s`, then the average value of `f
` belongs to `s`:
`⨍ x, f x ∂μ ∈ s`. See also `Convex.centerMass_mem` for a finite sum version of 
this lemma.
-/
theorem Convex.average_mem [IsFiniteMeasure μ] [NeZero μ] (hs : Convex ℝ s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) : (⨍ x, f x ∂μ) ∈ s :=
  hs.integral_mem hsc (ae_mono' smul_absolutelyContinuous hfs) hfi.to_average

/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `s`:
`⨍ x, f x ∂μ ∈ s`. See also `Convex.centerMass_mem` for a finite sum version of this lemma. -/
/-
**Convex.set_average_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.set_average_mem (hs : Convex Real s) (hsc : IsClosed s) (h0 : μ t !
= 0) (ht : μ t != ∞) (hfs : forallᵐ x ∂μ.restrict t, f x in s) (hfi : Integrable
On f t μ) : (⨍ x in t, f x ∂μ) in s
参数：hs : Convex Real s；hsc : IsClosed s；h0 : μ t != 0；ht : μ t != ∞；hfs : forallᵐ
 x ∂μ.restrict t, f x in s；hfi : IntegrableOn f t μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Convex.average_mem`：Convex.average_mem [IsFiniteMeasure μ] [NeZero μ] (h
s : Convex Real s) (hsc : IsClosed s) (hfs : forallᵐ x ∂μ, f x in s) (hfi : Inte
grable f…
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
· 使用定理 `MeasureTheory.Measure.restrict.neZero`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s : Set α} [NeZero (μ s)],   NeZero (μ.r
estrict s)

--- 原说明 ---
If `μ` is a non-zero finite measure on `α`, `s` is a convex closed set in `E`, a
nd `f` is an
integrable function sending `μ`-a.e. points to `s`, then the average value of `f
` belongs to `s`:
`⨍ x, f x ∂μ ∈ s`. See also `Convex.centerMass_mem` for a finite sum version of 
this lemma.
-/
theorem Convex.set_average_mem (hs : Convex ℝ s) (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞)
    (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) (hfi : IntegrableOn f t μ) : (⨍ x in t, f x ∂μ) ∈ s :=
  have := Fact.mk ht.lt_top
  have := NeZero.mk h0
  hs.average_mem hsc hfs hfi

/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex set in `E`, and `f` is an integrable
function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `closure s`:
`⨍ x, f x ∂μ ∈ s`. See also `Convex.centerMass_mem` for a finite sum version of this lemma. -/
/-
**Convex.set_average_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.set_average_mem_closure (hs : Convex Real s) (h0 : μ t != 0) (ht : 
μ t != ∞) (hfs : forallᵐ x ∂μ.restrict t, f x in s) (hfi : IntegrableOn f t μ) :
 (⨍ x in t, f x ∂μ) in closure s
参数：hs : Convex Real s；h0 : μ t != 0；ht : μ t != ∞；hfs : forallᵐ x ∂μ.restrict t,
 f x in s；hfi : IntegrableOn f t μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Convex.set_average_mem`：Convex.set_average_mem (hs : Convex Real s) (hsc
 : IsClosed s) (h0 : μ t != 0) (ht : μ t != ∞) (hfs : forallᵐ x ∂μ.restrict t, f
 x in s) (hf…
· 使用定理 `Convex.closure`：∀ {𝕜 : Type u_2} {E : Type u_3} [inst : Field 𝕜] [inst_1
 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] [ins
t_4 …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
If `μ` is a non-zero finite measure on `α`, `s` is a convex set in `E`, and `f` 
is an integrable
function sending `μ`-a.e. points to `s`, then the average value of `f` belongs t
o `closure s`:
`⨍ x, f x ∂μ ∈ s`. See also `Convex.centerMass_mem` for a finite sum version of 
this lemma.
-/
theorem Convex.set_average_mem_closure (hs : Convex ℝ s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞)
    (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) (hfi : IntegrableOn f t μ) :
    (⨍ x in t, f x ∂μ) ∈ closure s :=
  hs.closure.set_average_mem isClosed_closure h0 ht (hfs.mono fun _ hx => subset_closure hx) hfi
/-
**ConvexOn.average_mem_epigraph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.average_mem_epigraph [IsFiniteMeasure μ] [NeZero μ] (hg : ConvexO
n Real s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : forallᵐ x ∂μ, f x
 in s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) : (⨍ x, f x ∂μ, ⨍ x, 
g (f x) ∂μ) in {p : E × Real | p.1 in s ∧ g p.1 <= p.2}
参数：hg : ConvexOn Real s g；hgc : ContinuousOn g s；hsc : IsClosed s；hfs : forallᵐ 
x ∂μ, f x in s；hfi : Integrable f μ；hgi : Integrable (g ∘ f) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Convex.average_mem`：Convex.average_mem [IsFiniteMeasure μ] [NeZero μ] (h
s : Convex Real s) (hsc : IsClosed s) (hfs : forallᵐ x ∂μ, f x in s) (hfi : Inte
grable f…
· 使用定理 `ConvexOn.convex_epigraph`：ConvexOn.convex_epigraph (hf : ConvexOn 𝕜 s f)
 : Convex 𝕜 { p : E × β | p.1 in s ∧ f p.1 <= p.2 }
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `IsClosed.epigraph`：IsClosed.epigraph [TopologicalSpace β] {f : β -> α} {
s : Set β} (hs : IsClosed s) (hf : ContinuousOn f s) : IsClosed { p : β × α | p.
1 in s …
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.Integrable.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Ty
pe u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAd
dCommGroup β] [inst_1…
· 使用定理 `MeasureTheory.average_pair`：average_pair [CompleteSpace E] {f : α -> E} 
{g : α -> F} (hfi : Integrable f μ) (hgi : Integrable g μ) : ⨍ x, (f x, g x) ∂μ 
= (⨍ x, f x ∂μ, …
-/
theorem ConvexOn.average_mem_epigraph [IsFiniteMeasure μ] [NeZero μ] (hg : ConvexOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s)
    (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, f x ∂μ, ⨍ x, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} := by
  have ht_mem : ∀ᵐ x ∂μ, (f x, g (f x)) ∈ {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} :=
    hfs.mono fun x hx => ⟨hx, le_rfl⟩
  exact average_pair hfi hgi ▸
    hg.convex_epigraph.average_mem (hsc.epigraph hgc) ht_mem (hfi.prodMk hgi)
/-
**ConcaveOn.average_mem_hypograph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.average_mem_hypograph [IsFiniteMeasure μ] [NeZero μ] (hg : Conca
veOn Real s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : forallᵐ x ∂μ, 
f x in s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) : (⨍ x, f x ∂μ, ⨍ 
x, g (f x) ∂μ) in {p : E × Real | p.1 in s ∧ p.2 <= g p.1}
参数：hg : ConcaveOn Real s g；hgc : ContinuousOn g s；hsc : IsClosed s；hfs : forallᵐ
 x ∂μ, f x in s；hfi : Integrable f μ；hgi : Integrable (g ∘ f) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.average_neg`：average_neg (f : α -> E) : ⨍ x, -f x ∂μ = -⨍ 
x, f x ∂μ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ConvexOn.average_mem_epigraph`：ConvexOn.average_mem_epigraph [IsFiniteMe
asure μ] [NeZero μ] (hg : ConvexOn Real s g) (hgc : ContinuousOn g s) (hsc : IsC
losed s) (hfs : for…
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `ContinuousOn.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X 
→ G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
-/
theorem ConcaveOn.average_mem_hypograph [IsFiniteMeasure μ] [NeZero μ] (hg : ConcaveOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s)
    (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, f x ∂μ, ⨍ x, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ p.2 ≤ g p.1} := by
  simpa only [mem_ofPred_eq, Pi.neg_apply, average_neg, neg_le_neg_iff] using
    hg.neg.average_mem_epigraph hgc.neg hsc hfs hfi hgi.neg

/-- **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points to `s`, then the value of `g` at the average value of `f` is less than or equal to
the average value of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also
`ConvexOn.map_centerMass_le` for a finite sum version of this lemma. -/
/-
**ConvexOn.map_average_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.map_average_le [IsFiniteMeasure μ] [NeZero μ] (hg : ConvexOn Real
 s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : forallᵐ x ∂μ, f x in s)
 (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) : g (⨍ x, f x ∂μ) <= ⨍ x, g
 (f x) ∂μ
参数：hg : ConvexOn Real s g；hgc : ContinuousOn g s；hsc : IsClosed s；hfs : forallᵐ 
x ∂μ, f x in s；hfi : Integrable f μ；hgi : Integrable (g ∘ f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ConvexOn.average_mem_epigraph`：ConvexOn.average_mem_epigraph [IsFiniteMe
asure μ] [NeZero μ] (hg : ConvexOn Real s g) (hgc : ContinuousOn g s) (hsc : IsC
losed s) (hfs : for…

--- 原说明 ---
**Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a
 convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function 
sending
`μ`-a.e. points to `s`, then the value of `g` at the average value of `f` is les
s than or equal to
the average value of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. 
See also
`ConvexOn.map_centerMass_le` for a finite sum version of this lemma.
-/
theorem ConvexOn.map_average_le [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    g (⨍ x, f x ∂μ) ≤ ⨍ x, g (f x) ∂μ :=
  (hg.average_mem_epigraph hgc hsc hfs hfi hgi).2

/-- **Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points to `s`, then the average value of `g ∘ f` is less than or equal to the value of `g`
at the average value of `f` provided that both `f` and `g ∘ f` are integrable. See also
`ConcaveOn.le_map_centerMass` for a finite sum version of this lemma. -/
/-
**ConcaveOn.le_map_average** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.le_map_average [IsFiniteMeasure μ] [NeZero μ] (hg : ConcaveOn Re
al s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : forallᵐ x ∂μ, f x in 
s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) : (⨍ x, g (f x) ∂μ) <= g 
(⨍ x, f x ∂μ)
参数：hg : ConcaveOn Real s g；hgc : ContinuousOn g s；hsc : IsClosed s；hfs : forallᵐ
 x ∂μ, f x in s；hfi : Integrable f μ；hgi : Integrable (g ∘ f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ConcaveOn.average_mem_hypograph`：ConcaveOn.average_mem_hypograph [IsFini
teMeasure μ] [NeZero μ] (hg : ConcaveOn Real s g) (hgc : ContinuousOn g s) (hsc 
: IsClosed s) (hfs : …

--- 原说明 ---
**Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on 
a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function 
sending
`μ`-a.e. points to `s`, then the average value of `g ∘ f` is less than or equal 
to the value of `g`
at the average value of `f` provided that both `f` and `g ∘ f` are integrable. S
ee also
`ConcaveOn.le_map_centerMass` for a finite sum version of this lemma.
-/
theorem ConcaveOn.le_map_average [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, g (f x) ∂μ) ≤ g (⨍ x, f x ∂μ) :=
  (hg.average_mem_hypograph hgc hsc hfs hfi hgi).2

/-- **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points of a set `t` to `s`, then the value of `g` at the average value of `f` over `t` is
less than or equal to the average value of `g ∘ f` over `t` provided that both `f` and `g ∘ f` are
integrable. -/
/-
**ConvexOn.set_average_mem_epigraph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.set_average_mem_epigraph (hg : ConvexOn Real s g) (hgc : Continuo
usOn g s) (hsc : IsClosed s) (h0 : μ t != 0) (ht : μ t != ∞) (hfs : forallᵐ x ∂μ
.restrict t, f x in s) (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t 
μ) : (⨍ x in t, f x ∂μ, ⨍ x in t, g (f x) ∂μ) in {p : E × Real | p.1 in s ∧ g p.
1 <= p.2}
参数：hg : ConvexOn Real s g；hgc : ContinuousOn g s；hsc : IsClosed s；h0 : μ t != 0；
ht : μ t != ∞；hfs : forallᵐ x ∂μ.restrict t, f x in s；hfi : IntegrableOn f t μ；h
gi : IntegrableOn (g ∘ f) t μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ConvexOn.average_mem_epigraph`：ConvexOn.average_mem_epigraph [IsFiniteMe
asure μ] [NeZero μ] (hg : ConvexOn Real s g) (hgc : ContinuousOn g s) (hsc : IsC
losed s) (hfs : for…
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
· 使用定理 `MeasureTheory.Measure.restrict.neZero`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s : Set α} [NeZero (μ s)],   NeZero (μ.r
estrict s)

--- 原说明 ---
**Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a
 convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function 
sending
`μ`-a.e. points of a set `t` to `s`, then the value of `g` at the average value 
of `f` over `t` is
less than or equal to the average value of `g ∘ f` over `t` provided that both `
f` and `g ∘ f` are
integrable.
-/
theorem ConvexOn.set_average_mem_epigraph (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    (⨍ x in t, f x ∂μ, ⨍ x in t, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} :=
  have := Fact.mk ht.lt_top
  have := NeZero.mk h0
  hg.average_mem_epigraph hgc hsc hfs hfi hgi

/-- **Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points of a set `t` to `s`, then the average value of `g ∘ f` over `t` is less than or
equal to the value of `g` at the average value of `f` over `t` provided that both `f` and `g ∘ f`
are integrable. -/
/-
**ConcaveOn.set_average_mem_hypograph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.set_average_mem_hypograph (hg : ConcaveOn Real s g) (hgc : Conti
nuousOn g s) (hsc : IsClosed s) (h0 : μ t != 0) (ht : μ t != ∞) (hfs : forallᵐ x
 ∂μ.restrict t, f x in s) (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f)
 t μ) : (⨍ x in t, f x ∂μ, ⨍ x in t, g (f x) ∂μ) in {p : E × Real | p.1 in s ∧ p
.2 <= g p.1}
参数：hg : ConcaveOn Real s g；hgc : ContinuousOn g s；hsc : IsClosed s；h0 : μ t != 0
；ht : μ t != ∞；hfs : forallᵐ x ∂μ.restrict t, f x in s；hfi : IntegrableOn f t μ；
hgi : IntegrableOn (g ∘ f) t μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.average_neg`：average_neg (f : α -> E) : ⨍ x, -f x ∂μ = -⨍ 
x, f x ∂μ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ConvexOn.set_average_mem_epigraph`：ConvexOn.set_average_mem_epigraph (hg
 : ConvexOn Real s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (h0 : μ t != 0
) (ht : μ t != ∞) (hfs …
· 使用定理 `ConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [inst : Se
miring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : AddCo
mmG…
· 使用定理 `ContinuousOn.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X 
→ G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.IntegrableOn.neg`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f : α → …

--- 原说明 ---
**Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on 
a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function 
sending
`μ`-a.e. points of a set `t` to `s`, then the average value of `g ∘ f` over `t` 
is less than or
equal to the value of `g` at the average value of `f` over `t` provided that bot
h `f` and `g ∘ f`
are integrable.
-/
theorem ConcaveOn.set_average_mem_hypograph (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    (⨍ x in t, f x ∂μ, ⨍ x in t, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ p.2 ≤ g p.1} := by
  simpa only [mem_ofPred_eq, Pi.neg_apply, average_neg, neg_le_neg_iff] using
    hg.neg.set_average_mem_epigraph hgc.neg hsc h0 ht hfs hfi hgi.neg

/-- **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points of a set `t` to `s`, then the value of `g` at the average value of `f` over `t` is
less than or equal to the average value of `g ∘ f` over `t` provided that both `f` and `g ∘ f` are
integrable. -/
/-
**ConvexOn.map_set_average_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.map_set_average_le (hg : ConvexOn Real s g) (hgc : ContinuousOn g
 s) (hsc : IsClosed s) (h0 : μ t != 0) (ht : μ t != ∞) (hfs : forallᵐ x ∂μ.restr
ict t, f x in s) (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) : g
 (⨍ x in t, f x ∂μ) <= ⨍ x in t, g (f x) ∂μ
参数：hg : ConvexOn Real s g；hgc : ContinuousOn g s；hsc : IsClosed s；h0 : μ t != 0；
ht : μ t != ∞；hfs : forallᵐ x ∂μ.restrict t, f x in s；hfi : IntegrableOn f t μ；h
gi : IntegrableOn (g ∘ f) t μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ConvexOn.set_average_mem_epigraph`：ConvexOn.set_average_mem_epigraph (hg
 : ConvexOn Real s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (h0 : μ t != 0
) (ht : μ t != ∞) (hfs …

--- 原说明 ---
**Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a
 convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function 
sending
`μ`-a.e. points of a set `t` to `s`, then the value of `g` at the average value 
of `f` over `t` is
less than or equal to the average value of `g ∘ f` over `t` provided that both `
f` and `g ∘ f` are
integrable.
-/
theorem ConvexOn.map_set_average_le (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    g (⨍ x in t, f x ∂μ) ≤ ⨍ x in t, g (f x) ∂μ :=
  (hg.set_average_mem_epigraph hgc hsc h0 ht hfs hfi hgi).2

/-- **Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points of a set `t` to `s`, then the average value of `g ∘ f` over `t` is less than or
equal to the value of `g` at the average value of `f` over `t` provided that both `f` and `g ∘ f`
are integrable. -/
/-
**ConcaveOn.le_map_set_average** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.le_map_set_average (hg : ConcaveOn Real s g) (hgc : ContinuousOn
 g s) (hsc : IsClosed s) (h0 : μ t != 0) (ht : μ t != ∞) (hfs : forallᵐ x ∂μ.res
trict t, f x in s) (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
 (⨍ x in t, g (f x) ∂μ) <= g (⨍ x in t, f x ∂μ)
参数：hg : ConcaveOn Real s g；hgc : ContinuousOn g s；hsc : IsClosed s；h0 : μ t != 0
；ht : μ t != ∞；hfs : forallᵐ x ∂μ.restrict t, f x in s；hfi : IntegrableOn f t μ；
hgi : IntegrableOn (g ∘ f) t μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ConcaveOn.set_average_mem_hypograph`：ConcaveOn.set_average_mem_hypograph
 (hg : ConcaveOn Real s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (h0 : μ t
 != 0) (ht : μ t != ∞) (h…

--- 原说明 ---
**Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on 
a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function 
sending
`μ`-a.e. points of a set `t` to `s`, then the average value of `g ∘ f` over `t` 
is less than or
equal to the value of `g` at the average value of `f` over `t` provided that bot
h `f` and `g ∘ f`
are integrable.
-/
theorem ConcaveOn.le_map_set_average (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    (⨍ x in t, g (f x) ∂μ) ≤ g (⨍ x in t, f x ∂μ) :=
  (hg.set_average_mem_hypograph hgc hsc h0 ht hfs hfi hgi).2

/-- **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex closed
set `s`, `μ` is a probability measure on `α`, and `f : α → E` is a function sending `μ`-a.e.  points
to `s`, then the value of `g` at the expected value of `f` is less than or equal to the expected
value of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also
`ConvexOn.map_centerMass_le` for a finite sum version of this lemma. -/
/-
**ConvexOn.map_integral_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.map_integral_le [IsProbabilityMeasure μ] (hg : ConvexOn Real s g)
 (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : forallᵐ x ∂μ, f x in s) (hfi
 : Integrable f μ) (hgi : Integrable (g ∘ f) μ) : g (∫ x, f x ∂μ) <= ∫ x, g (f x
) ∂μ
参数：hg : ConvexOn Real s g；hgc : ContinuousOn g s；hsc : IsClosed s；hfs : forallᵐ 
x ∂μ, f x in s；hfi : Integrable f μ；hgi : Integrable (g ∘ f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.average_eq_integral`：average_eq_integral [IsProbabilityMea
sure μ] (f : α -> E) : ⨍ x, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `ConvexOn.map_average_le`：ConvexOn.map_average_le [IsFiniteMeasure μ] [Ne
Zero μ] (hg : ConvexOn Real s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (hf
s : forallᵐ x…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ

--- 原说明 ---
**Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a
 convex closed
set `s`, `μ` is a probability measure on `α`, and `f : α → E` is a function send
ing `μ`-a.e.  points
to `s`, then the value of `g` at the expected value of `f` is less than or equal
 to the expected
value of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also
`ConvexOn.map_centerMass_le` for a finite sum version of this lemma.
-/
theorem ConvexOn.map_integral_le [IsProbabilityMeasure μ] (hg : ConvexOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) : g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ := by
  simpa only [average_eq_integral] using hg.map_average_le hgc hsc hfs hfi hgi

/-- **Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on a convex closed
set `s`, `μ` is a probability measure on `α`, and `f : α → E` is a function sending `μ`-a.e.  points
to `s`, then the expected value of `g ∘ f` is less than or equal to the value of `g` at the expected
value of `f` provided that both `f` and `g ∘ f` are integrable. -/
/-
**ConcaveOn.le_map_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.le_map_integral [IsProbabilityMeasure μ] (hg : ConcaveOn Real s 
g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : forallᵐ x ∂μ, f x in s) (h
fi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) : (∫ x, g (f x) ∂μ) <= g (∫ x,
 f x ∂μ)
参数：hg : ConcaveOn Real s g；hgc : ContinuousOn g s；hsc : IsClosed s；hfs : forallᵐ
 x ∂μ, f x in s；hfi : Integrable f μ；hgi : Integrable (g ∘ f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.average_eq_integral`：average_eq_integral [IsProbabilityMea
sure μ] (f : α -> E) : ⨍ x, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `ConcaveOn.le_map_average`：ConcaveOn.le_map_average [IsFiniteMeasure μ] [
NeZero μ] (hg : ConcaveOn Real s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) 
(hfs : forallᵐ…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.neZero`：∀ {α : Type u_1} {m0 : Measur
ableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ
], NeZero μ

--- 原说明 ---
**Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on 
a convex closed
set `s`, `μ` is a probability measure on `α`, and `f : α → E` is a function send
ing `μ`-a.e.  points
to `s`, then the expected value of `g ∘ f` is less than or equal to the value of
 `g` at the expected
value of `f` provided that both `f` and `g ∘ f` are integrable.
-/
theorem ConcaveOn.le_map_integral [IsProbabilityMeasure μ] (hg : ConcaveOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) : (∫ x, g (f x) ∂μ) ≤ g (∫ x, f x ∂μ) := by
  simpa only [average_eq_integral] using hg.le_map_average hgc hsc hfs hfi hgi

/-!
### Strict Jensen's inequality
-/


/-- If `f : α → E` is an integrable function, then either it is a.e. equal to the constant
`⨍ x, f x ∂μ` or there exists a measurable set such that `μ t ≠ 0`, `μ tᶜ ≠ 0`, and the average
values of `f` over `t` and `tᶜ` are different. -/
/-
**ae_eq_const_or_exists_average_ne_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_eq_const_or_exists_average_ne_compl [IsFiniteMeasure μ] (hfi : Integrab
le f μ) : f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ exists t, MeasurableSet t ∧ μ t != 0 ∧
 μ tᶜ != 0 ∧ (⨍ x in t, f x ∂μ) != ⨍ x in tᶜ, f x ∂μ
参数：hfi : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq`：∀ {α : Type u_1
} {E : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : 
NormedAddCommGroup E]   [inst_1 : NormedSpace…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setIntegral_const`：setIntegral_const [CompleteSpace E] (c 
: E) : ∫ _ in s, c ∂μ = μ.real s • c
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `ENNReal.toReal_zero`：ENNReal.toReal 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_eq_univ`：ae_eq_univ : s =ᵐ[μ] (univ : Set α) ↔ μ sᶜ = 0
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `MeasureTheory.measureReal_congr`：measureReal_congr (H : s =ᵐ[μ] t) : μ.r
eal s = μ.real t
· 使用定理 `MeasureTheory.measure_smul_average`：measure_smul_average [IsFiniteMeasur
e μ] (f : α -> E) : μ.real univ • ⨍ x, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.average_mem_openSegment_compl_self`：average_mem_openSegmen
t_compl_self [IsFiniteMeasure μ] {f : α -> E} {s : Set α} (hs : NullMeasurableSe
t s μ) (hs₀ : μ s != 0) (hsc₀ : μ sᶜ !…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `openSegment_same`：openSegment_same (x : E) : openSegment 𝕜 x x = {x}
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : α → E` is an integrable function, then either it is a.e. equal to the co
nstant
`⨍ x, f x ∂μ` or there exists a measurable set such that `μ t ≠ 0`, `μ tᶜ ≠ 0`, 
and the average
values of `f` over `t` and `tᶜ` are different.
-/
theorem ae_eq_const_or_exists_average_ne_compl [IsFiniteMeasure μ] (hfi : Integrable f μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨
      ∃ t, MeasurableSet t ∧ μ t ≠ 0 ∧ μ tᶜ ≠ 0 ∧ (⨍ x in t, f x ∂μ) ≠ ⨍ x in tᶜ, f x ∂μ := by
  refine or_iff_not_imp_right.mpr fun H => ?_; push Not at H
  refine hfi.ae_eq_of_forall_setIntegral_eq _ _ (integrable_const _) fun t ht ht' => ?_; clear ht'
  simp only [const_apply, setIntegral_const]
  by_cases h₀ : μ t = 0
  · rw [restrict_eq_zero.2 h₀, integral_zero_measure, measureReal_def, h₀,
      ENNReal.toReal_zero, zero_smul]
  by_cases h₀' : μ tᶜ = 0
  · rw [← ae_eq_univ] at h₀'
    rw [restrict_congr_set h₀', restrict_univ, measureReal_congr h₀', measure_smul_average]
  have := average_mem_openSegment_compl_self ht.nullMeasurableSet h₀ h₀' hfi
  rw [← H t ht h₀ h₀', openSegment_same, mem_singleton_iff] at this
  rw [this, measure_smul_setAverage _ (by finiteness)]

/-- If an integrable function `f : α → E` takes values in a convex set `s` and for some set `t` of
positive measure, the average value of `f` over `t` belongs to the interior of `s`, then the average
of `f` over the whole space belongs to the interior of `s`. -/
/-
**Convex.average_mem_interior_of_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.average_mem_interior_of_set [IsFiniteMeasure μ] (hs : Convex Real s
) (h0 : μ t != 0) (hfs : forallᵐ x ∂μ, f x in s) (hfi : Integrable f μ) (ht : (⨍
 x in t, f x ∂μ) in interior s) : (⨍ x, f x ∂μ) in interior s
参数：hs : Convex Real s；h0 : μ t != 0；hfs : forallᵐ x ∂μ, f x in s；hfi : Integrabl
e f μ；ht : (⨍ x in t, f x ∂μ) in interior s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_eq_univ`：ae_eq_univ : s =ᵐ[μ] (univ : Set α) ↔ μ sᶜ = 0
· 使用定理 `MeasureTheory.Measure.restrict_toMeasurable`：restrict_toMeasurable (h : 
μ s != ∞) : μ.restrict (toMeasurable μ s) = μ.restrict s
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `Convex.openSegment_interior_closure_subset_interior`：Convex.openSegment_
interior_closure_subset_interior {s : Set E} (hs : Convex 𝕜 s) {x y : E} (hx : x
 in interior s) (hy : y in closure s) : o…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Convex.set_average_mem_closure`：Convex.set_average_mem_closure (hs : Con
vex Real s) (h0 : μ t != 0) (ht : μ t != ∞) (hfs : forallᵐ x ∂μ.restrict t, f x 
in s) (hfi : Integra…
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.average_mem_openSegment_compl_self`：average_mem_openSegmen
t_compl_self [IsFiniteMeasure μ] {f : α -> E} {s : Set α} (hs : NullMeasurableSe
t s μ) (hs₀ : μ s != 0) (hsc₀ : μ sᶜ !…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s

--- 原说明 ---
If an integrable function `f : α → E` takes values in a convex set `s` and for s
ome set `t` of
positive measure, the average value of `f` over `t` belongs to the interior of `
s`, then the average
of `f` over the whole space belongs to the interior of `s`.
-/
theorem Convex.average_mem_interior_of_set [IsFiniteMeasure μ] (hs : Convex ℝ s) (h0 : μ t ≠ 0)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (ht : (⨍ x in t, f x ∂μ) ∈ interior s) :
    (⨍ x, f x ∂μ) ∈ interior s := by
  rw [← measure_toMeasurable] at h0; rw [← restrict_toMeasurable (by finiteness)] at ht
  by_cases h0' : μ (toMeasurable μ t)ᶜ = 0
  · rw [← ae_eq_univ] at h0'
    rwa [restrict_congr_set h0', restrict_univ] at ht
  exact hs.openSegment_interior_closure_subset_interior ht
      (hs.set_average_mem_closure h0' (by finiteness) (ae_restrict_of_ae hfs) hfi.integrableOn)
      (average_mem_openSegment_compl_self (measurableSet_toMeasurable μ t).nullMeasurableSet h0
        h0' hfi)

/-- If an integrable function `f : α → E` takes values in a strictly convex closed set `s`, then
either it is a.e. equal to its average value, or its average value belongs to the interior of
`s`. -/
/-
**StrictConvex.ae_eq_const_or_average_mem_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.ae_eq_const_or_average_mem_interior [IsFiniteMeasure μ] (hs :
 StrictConvex Real s) (hsc : IsClosed s) (hfs : forallᵐ x ∂μ, f x in s) (hfi : I
ntegrable f μ) : f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ (⨍ x, f x ∂μ) in interior s
参数：hs : StrictConvex Real s；hsc : IsClosed s；hfs : forallᵐ x ∂μ, f x in s；hfi : 
Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Convex.set_average_mem`：Convex.set_average_mem (hs : Convex Real s) (hsc
 : IsClosed s) (h0 : μ t != 0) (ht : μ t != ∞) (hfs : forallᵐ x ∂μ.restrict t, f
 x in s) (hf…
· 使用定理 `StrictConvex.convex`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Semiring 𝕜]
 [inst_1 : PartialOrder 𝕜] [inst_2 : TopologicalSpace E]   [inst_3 : AddCommMono
id E] [in…
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `StrictConvex.openSegment_subset`：StrictConvex.openSegment_subset (hs : S
trictConvex 𝕜 s) (hx : x in s) (hy : y in s) (h : x != y) : openSegment 𝕜 x y su
bseteq interior s
· 使用定理 `MeasureTheory.average_mem_openSegment_compl_self`：average_mem_openSegmen
t_compl_self [IsFiniteMeasure μ] {f : α -> E} {s : Set α} (hs : NullMeasurableSe
t s μ) (hs₀ : μ s != 0) (hsc₀ : μ sᶜ !…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `ae_eq_const_or_exists_average_ne_compl`：ae_eq_const_or_exists_average_ne
_compl [IsFiniteMeasure μ] (hfi : Integrable f μ) : f =ᵐ[μ] const α (⨍ x, f x ∂μ
) ∨ exists t, MeasurableSet …

--- 原说明 ---
If an integrable function `f : α → E` takes values in a strictly convex closed s
et `s`, then
either it is a.e. equal to its average value, or its average value belongs to th
e interior of
`s`.
-/
theorem StrictConvex.ae_eq_const_or_average_mem_interior [IsFiniteMeasure μ] (hs : StrictConvex ℝ s)
    (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ (⨍ x, f x ∂μ) ∈ interior s := by
  have : ∀ {t}, μ t ≠ 0 → (⨍ x in t, f x ∂μ) ∈ s := fun ht =>
    hs.convex.set_average_mem hsc ht (by finiteness) (ae_restrict_of_ae hfs) hfi.integrableOn
  refine (ae_eq_const_or_exists_average_ne_compl hfi).imp_right ?_
  rintro ⟨t, hm, h₀, h₀', hne⟩
  exact
    hs.openSegment_subset (this h₀) (this h₀') hne
      (average_mem_openSegment_compl_self hm.nullMeasurableSet h₀ h₀' hfi)

/-- **Jensen's inequality**, strict version: if an integrable function `f : α → E` takes values in a
convex closed set `s`, and `g : E → ℝ` is continuous and strictly convex on `s`, then
either `f` is a.e. equal to its average value, or `g (⨍ x, f x ∂μ) < ⨍ x, g (f x) ∂μ`. -/
/-
**StrictConvexOn.ae_eq_const_or_map_average_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.ae_eq_const_or_map_average_lt [IsFiniteMeasure μ] (hg : Str
ictConvexOn Real s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : forallᵐ
 x ∂μ, f x in s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) : f =ᵐ[μ] c
onst α (⨍ x, f x ∂μ) ∨ g (⨍ x, f x ∂μ) < ⨍ x, g (f x) ∂μ
参数：hg : StrictConvexOn Real s g；hgc : ContinuousOn g s；hsc : IsClosed s；hfs : fo
rallᵐ x ∂μ, f x in s；hfi : Integrable f μ；hgi : Integrable (g ∘ f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ConvexOn.set_average_mem_epigraph`：ConvexOn.set_average_mem_epigraph (hg
 : ConvexOn Real s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (h0 : μ t != 0
) (ht : μ t != ∞) (hfs …
· 使用定理 `StrictConvexOn.convexOn`：StrictConvexOn.convexOn {s : Set E} {f : E -> β
} (hf : StrictConvexOn 𝕜 s f) : ConvexOn 𝕜 s f
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `MeasureTheory.average_mem_openSegment_compl_self`：average_mem_openSegmen
t_compl_self [IsFiniteMeasure μ] {f : α -> E} {s : Set α} (hs : NullMeasurableSe
t s μ) (hs₀ : μ s != 0) (hsc₀ : μ sᶜ !…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasureTheory.Integrable.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Ty
pe u_3} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : NormedAd
dCommGroup β] [inst_1…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Prod.mk_inj`：mk_inj {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ =
 a₂ ∧ b₁ = b₂
· 使用定理 `Prod.mk_add_mk`：∀ {M : Type u_8} {N : Type u_9} [inst : Add M] [inst_1 :
 Add N] (a₁ a₂ : M) (b₁ b₂ : N),   (a₁, b₁) + (a₂, b₂) = (a₁ + a₂, b₁ + b₂)
· 使用定理 `Prod.smul_mk`：∀ {E : Type u_8} {α : Type u_9} {β : Type u_10} [inst : SM
ul E α] [inst_1 : SMul E β] (c : E) (a : α) (b : β),   c • (a, b) = (c • a, c • 
b)
· 使用定理 `MeasureTheory.average_pair`：average_pair [CompleteSpace E] {f : α -> E} 
{g : α -> F} (hfi : Integrable f μ) (hgi : Integrable g μ) : ⨍ x, (f x, g x) ∂μ 
= (⨍ x, f x ∂μ, …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ae_eq_const_or_exists_average_ne_compl`：ae_eq_const_or_exists_average_ne
_compl [IsFiniteMeasure μ] (hfi : Integrable f μ) : f =ᵐ[μ] const α (⨍ x, f x ∂μ
) ∨ exists t, MeasurableSet …

--- 原说明 ---
**Jensen's inequality**, strict version: if an integrable function `f : α → E` t
akes values in a
convex closed set `s`, and `g : E → ℝ` is continuous and strictly convex on `s`,
 then
either `f` is a.e. equal to its average value, or `g (⨍ x, f x ∂μ) < ⨍ x, g (f x
) ∂μ`.
-/
theorem StrictConvexOn.ae_eq_const_or_map_average_lt [IsFiniteMeasure μ] (hg : StrictConvexOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ g (⨍ x, f x ∂μ) < ⨍ x, g (f x) ∂μ := by
  have : ∀ {t}, μ t ≠ 0 → (⨍ x in t, f x ∂μ) ∈ s ∧ g (⨍ x in t, f x ∂μ) ≤ ⨍ x in t, g (f x) ∂μ :=
    fun ht =>
    hg.convexOn.set_average_mem_epigraph hgc hsc ht (by finiteness) (ae_restrict_of_ae hfs)
      hfi.integrableOn hgi.integrableOn
  refine (ae_eq_const_or_exists_average_ne_compl hfi).imp_right ?_
  rintro ⟨t, hm, h₀, h₀', hne⟩
  rcases average_mem_openSegment_compl_self hm.nullMeasurableSet h₀ h₀' (hfi.prodMk hgi) with
    ⟨a, b, ha, hb, hab, h_avg⟩
  rw [average_pair hfi hgi, average_pair hfi.integrableOn hgi.integrableOn,
    average_pair hfi.integrableOn hgi.integrableOn, Prod.smul_mk,
    Prod.smul_mk, Prod.mk_add_mk, Prod.mk_inj] at h_avg
  simp only [Function.comp] at h_avg
  rw [← h_avg.1, ← h_avg.2]
  calc
    g ((a • ⨍ x in t, f x ∂μ) + b • ⨍ x in tᶜ, f x ∂μ) <
        a * g (⨍ x in t, f x ∂μ) + b * g (⨍ x in tᶜ, f x ∂μ) :=
      hg.2 (this h₀).1 (this h₀').1 hne ha hb hab
    _ ≤ (a * ⨍ x in t, g (f x) ∂μ) + b * ⨍ x in tᶜ, g (f x) ∂μ := by
      gcongr
      exacts [(this h₀).2, (this h₀').2]

/-- **Jensen's inequality**, strict version: if an integrable function `f : α → E` takes values in a
convex closed set `s`, and `g : E → ℝ` is continuous and strictly concave on `s`, then
either `f` is a.e. equal to its average value, or `⨍ x, g (f x) ∂μ < g (⨍ x, f x ∂μ)`. -/
/-
**StrictConcaveOn.ae_eq_const_or_lt_map_average** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.ae_eq_const_or_lt_map_average [IsFiniteMeasure μ] (hg : St
rictConcaveOn Real s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : foral
lᵐ x ∂μ, f x in s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) : f =ᵐ[μ]
 const α (⨍ x, f x ∂μ) ∨ (⨍ x, g (f x) ∂μ) < g (⨍ x, f x ∂μ)
参数：hg : StrictConcaveOn Real s g；hgc : ContinuousOn g s；hsc : IsClosed s；hfs : f
orallᵐ x ∂μ, f x in s；hfi : Integrable f μ；hgi : Integrable (g ∘ f) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.average_neg`：average_neg (f : α -> E) : ⨍ x, -f x ∂μ = -⨍ 
x, f x ∂μ
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `StrictConvexOn.ae_eq_const_or_map_average_lt`：StrictConvexOn.ae_eq_const
_or_map_average_lt [IsFiniteMeasure μ] (hg : StrictConvexOn Real s g) (hgc : Con
tinuousOn g s) (hsc : IsClosed s) …
· 使用定理 `StrictConcaveOn.neg`：∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_5} [ins
t : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 :
 AddCommG…
· 使用定理 `ContinuousOn.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : X 
→ G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…

--- 原说明 ---
**Jensen's inequality**, strict version: if an integrable function `f : α → E` t
akes values in a
convex closed set `s`, and `g : E → ℝ` is continuous and strictly concave on `s`
, then
either `f` is a.e. equal to its average value, or `⨍ x, g (f x) ∂μ < g (⨍ x, f x
 ∂μ)`.
-/
theorem StrictConcaveOn.ae_eq_const_or_lt_map_average [IsFiniteMeasure μ]
    (hg : StrictConcaveOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ (⨍ x, g (f x) ∂μ) < g (⨍ x, f x ∂μ) := by
  simpa only [Pi.neg_apply, average_neg, neg_lt_neg_iff] using
    hg.neg.ae_eq_const_or_map_average_lt hgc.neg hsc hfs hfi hgi.neg

/-- If `E` is a strictly convex normed space and `f : α → E` is a function such that `‖f x‖ ≤ C`
a.e., then either this function is a.e. equal to its average value, or the norm of its average value
is strictly less than `C`. -/
/-
**ae_eq_const_or_norm_average_lt_of_norm_le_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_eq_const_or_norm_average_lt_of_norm_le_const [StrictConvexSpace Real E]
 (h_le : forallᵐ x ∂μ, ‖f x‖ <= C) : f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ ‖⨍ x, f x ∂
μ‖ < C
参数：h_le : forallᵐ x ∂μ, ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.average_congr`：average_congr {f g : α -> E} (h : f =ᵐ[μ] g
) : ⨍ x, f x ∂μ = ⨍ x, g x ∂μ
· 使用定理 `MeasureTheory.average_zero`：average_zero : ⨍ _, (0 : E) ∂μ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.average_eq`：average_eq (f : α -> E) : ⨍ x, f x ∂μ = (μ.rea
l univ)⁻¹ • ∫ x, f x ∂μ
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `interior_closedBall`：interior_closedBall (x : E) {r : Real} (hr : r != 0
) : interior (closedBall x r) = ball x r
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `StrictConvex.ae_eq_const_or_average_mem_interior`：StrictConvex.ae_eq_con
st_or_average_mem_interior [IsFiniteMeasure μ] (hs : StrictConvex Real s) (hsc :
 IsClosed s) (hfs : forallᵐ x ∂μ, f x …
· 使用定理 `strictConvex_closedBall`：strictConvex_closedBall [StrictConvexSpace 𝕜 E]
 (x : E) (r : Real) : StrictConvex 𝕜 (closedBall x r)
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0

--- 原说明 ---
If `E` is a strictly convex normed space and `f : α → E` is a function such that
 `‖f x‖ ≤ C`
a.e., then either this function is a.e. equal to its average value, or the norm 
of its average value
is strictly less than `C`.
-/
theorem ae_eq_const_or_norm_average_lt_of_norm_le_const [StrictConvexSpace ℝ E]
    (h_le : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ ‖⨍ x, f x ∂μ‖ < C := by
  rcases le_or_gt C 0 with hC0 | hC0
  · have : f =ᵐ[μ] 0 := h_le.mono fun x hx => norm_le_zero_iff.1 (hx.trans hC0)
    simp only [average_congr this, Pi.zero_apply, average_zero]
    exact Or.inl this
  by_cases hfi : Integrable f μ; swap
  · simp [average_eq, integral_undef hfi, hC0]
  rcases (le_top : μ univ ≤ ∞).eq_or_lt with hμt | hμt
  · simp [average_eq, measureReal_def, hμt, hC0]
  have : IsFiniteMeasure μ := ⟨hμt⟩
  replace h_le : ∀ᵐ x ∂μ, f x ∈ closedBall (0 : E) C := by simpa only [mem_closedBall_zero_iff]
  simpa only [interior_closedBall _ hC0.ne', mem_ball_zero_iff] using
    (strictConvex_closedBall ℝ (0 : E) C).ae_eq_const_or_average_mem_interior isClosed_closedBall
      h_le hfi

/-- If `E` is a strictly convex normed space and `f : α → E` is a function such that `‖f x‖ ≤ C`
a.e., then either this function is a.e. equal to its average value, or the norm of its integral is
strictly less than `μ.real univ * C`. -/
/-
**ae_eq_const_or_norm_integral_lt_of_norm_le_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_eq_const_or_norm_integral_lt_of_norm_le_const [StrictConvexSpace Real E
] [IsFiniteMeasure μ] (h_le : forallᵐ x ∂μ, ‖f x‖ <= C) : f =ᵐ[μ] const α (⨍ x, 
f x ∂μ) ∨ ‖∫ x, f x ∂μ‖ < μ.real univ * C
参数：h_le : forallᵐ x ∂μ, ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.average_zero_measure`：average_zero_measure (f : α -> E) : 
⨍ x, f x ∂(0 : Measure α) = 0
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用引理 `div_lt_iff₀'`：div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If `E` is a strictly convex normed space and `f : α → E` is a function such that
 `‖f x‖ ≤ C`
a.e., then either this function is a.e. equal to its average value, or the norm 
of its integral is
strictly less than `μ.real univ * C`.
-/
theorem ae_eq_const_or_norm_integral_lt_of_norm_le_const [StrictConvexSpace ℝ E] [IsFiniteMeasure μ]
    (h_le : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ ‖∫ x, f x ∂μ‖ < μ.real univ * C := by
  rcases eq_or_ne μ 0 with h₀ | h₀; · simp [h₀, EventuallyEq]
  have hμ : 0 < μ.real univ := by
    simp [measureReal_def, ENNReal.toReal_pos_iff, pos_iff_ne_zero, h₀, measure_lt_top]
  refine (ae_eq_const_or_norm_average_lt_of_norm_le_const h_le).imp_right fun H => ?_
  rwa [average_eq, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hμ, ← div_eq_inv_mul,
    div_lt_iff₀' hμ] at H

/-- If `E` is a strictly convex normed space and `f : α → E` is a function such that `‖f x‖ ≤ C`
a.e. on a set `t` of finite measure, then either this function is a.e. equal to its average value on
`t`, or the norm of its integral over `t` is strictly less than `μ.real t * C`. -/
/-
**ae_eq_const_or_norm_setIntegral_lt_of_norm_le_const** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：ae_eq_const_or_norm_setIntegral_lt_of_norm_le_const [StrictConvexSpace Rea
l E] (ht : μ t != ∞) (h_le : forallᵐ x ∂μ.restrict t, ‖f x‖ <= C) : f =ᵐ[μ.restr
ict t] const α (⨍ x in t, f x ∂μ) ∨ ‖∫ x in t, f x ∂μ‖ < μ.real t * C
参数：ht : μ t != ∞；h_le : forallᵐ x ∂μ.restrict t, ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measureReal_restrict_apply_univ`：measureReal_restrict_appl
y_univ (s : Set α) : (μ.restrict s).real univ = μ.real s
· 使用定理 `ae_eq_const_or_norm_integral_lt_of_norm_le_const`：ae_eq_const_or_norm_in
tegral_lt_of_norm_le_const [StrictConvexSpace Real E] [IsFiniteMeasure μ] (h_le 
: forallᵐ x ∂μ, ‖f x‖ <= C) : f =ᵐ[μ] …
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…

--- 原说明 ---
If `E` is a strictly convex normed space and `f : α → E` is a function such that
 `‖f x‖ ≤ C`
a.e. on a set `t` of finite measure, then either this function is a.e. equal to 
its average value on
`t`, or the norm of its integral over `t` is strictly less than `μ.real t * C`.
-/
theorem ae_eq_const_or_norm_setIntegral_lt_of_norm_le_const [StrictConvexSpace ℝ E] (ht : μ t ≠ ∞)
    (h_le : ∀ᵐ x ∂μ.restrict t, ‖f x‖ ≤ C) :
    f =ᵐ[μ.restrict t] const α (⨍ x in t, f x ∂μ) ∨ ‖∫ x in t, f x ∂μ‖ < μ.real t * C := by
  have := Fact.mk ht.lt_top
  rw [← measureReal_restrict_apply_univ]
  exact ae_eq_const_or_norm_integral_lt_of_norm_le_const h_le
