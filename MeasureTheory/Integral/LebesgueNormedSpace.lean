/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.Normed.Module.Basic

/-! # A lemma about measurability with density under scalar multiplication in normed spaces -/

public section


open MeasureTheory Filter ENNReal Set

open NNReal ENNReal

variable {α : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}

/-
**aemeasurable_withDensity_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_withDensity_iff {E : Type*} [NormedAddCommGroup E] [NormedSpa
ce Real E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {f : α
 -> Real>=0} (hf : Measurable f) {g : α -> E} : AEMeasurable g (μ.withDensity fu
n x => (f x : Real>=0∞)) ↔ AEMeasurable (fun x => (f x : Real) • g x) μ
参数：hf : Measurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `NNReal.instSecondCountableTopology`：SecondCountableTopology NNReal
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `NNReal.instCompleteSpace`：CompleteSpace NNReal
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Measurable.smul`：Measurable.smul [MeasurableSMul₂ M X] (hf : Measurable 
f) (hg : Measurable g) : Measurable (f • g)
· 使用定理 `ContinuousSMul.measurableSMul₂`：∀ {M : Type u_7} {α : Type u_8} [inst : 
TopologicalSpace M] [inst_1 : MeasurableSpace M] [OpensMeasurableSpace M]   [ins
t_3 : TopologicalSpa…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Measurable.coe_nnreal_real`：Measurable.coe_nnreal_real {f : α -> Real>=0
} (hf : Measurable f) : Measurable fun x => (f x : Real)
· 使用定理 `MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl`：ae_of_ae_restrict_
of_ae_restrict_compl (t : Set α) {p : α -> Prop} (ht : forallᵐ x ∂μ.restrict t, 
p x) (htc : forallᵐ x ∂μ.restrict tᶜ, p x)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_withDensity_iff`：ae_withDensity_iff {p : α -> Prop} {f 
: α -> Real>=0∞} (hf : Measurable f) : (forallᵐ x ∂μ.withDensity f, p x) ↔ foral
lᵐ x ∂μ, f x != 0 -> p…
· 使用定理 `Measurable.coe_nnreal_ennreal`：Measurable.coe_nnreal_ennreal {f : α -> R
eal>=0} (hf : Measurable f) : Measurable fun x => (f x : Real>=0∞)
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
（共 46 条，此处仅展示前 30 条）
-/
theorem aemeasurable_withDensity_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {f : α → ℝ≥0}
    (hf : Measurable f) {g : α → E} :
    AEMeasurable g (μ.withDensity fun x => (f x : ℝ≥0∞)) ↔
      AEMeasurable (fun x => (f x : ℝ) • g x) μ := by
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet { x : α | f x ≠ 0 } := (hf (measurableSet_singleton 0)).compl
    refine ⟨fun x => (f x : ℝ) • g' x, hf.coe_nnreal_real.smul g'meas, ?_⟩
    apply @ae_of_ae_restrict_of_ae_restrict_compl _ _ _ { x | f x ≠ 0 }
    · rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg']
      intro a ha h'a
      have : (f a : ℝ≥0∞) ≠ 0 := by simpa only [Ne, ENNReal.coe_eq_zero] using h'a
      rw [ha this]
    · filter_upwards [ae_restrict_mem A.compl]
      intro x hx
      simp only [Classical.not_not, mem_ofPred_eq, mem_compl_iff] at hx
      simp [hx]
  · rintro ⟨g', g'meas, hg'⟩
    refine ⟨fun x => (f x : ℝ)⁻¹ • g' x, hf.coe_nnreal_real.inv.smul g'meas, ?_⟩
    rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal]
    filter_upwards [hg']
    intro x hx h'x
    rw [← hx, smul_smul, inv_mul_cancel₀, one_smul]
    simp only [Ne, ENNReal.coe_eq_zero] at h'x
    simpa only [NNReal.coe_eq_zero, Ne] using h'x
