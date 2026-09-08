/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Strongly measurable and finitely strongly measurable functions

This file contains some further development of strongly measurable and finitely strongly measurable
functions, started in `Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`.

## References

* [Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.][Hytonen_VanNeerven_Veraar_Wies_2016]

-/

public section

open MeasureTheory Filter Set ENNReal NNReal

variable {α β γ : Type*} {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β]
  [TopologicalSpace γ] {f g : α → β}

@[fun_prop]
/-
**aestronglyMeasurable_dirac** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：aestronglyMeasurable_dirac [MeasurableSingletonClass α] {a : α} {f : α -> 
β} : AEStronglyMeasurable f (Measure.dirac a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `MeasureTheory.ae_eq_dirac`：ae_eq_dirac [MeasurableSingletonClass α] {a :
 α} (f : α -> δ) : f =ᵐ[dirac a] const α (f a)
-/
lemma aestronglyMeasurable_dirac [MeasurableSingletonClass α] {a : α} {f : α → β} :
    AEStronglyMeasurable f (Measure.dirac a) :=
  ⟨fun _ ↦ f a, stronglyMeasurable_const, ae_eq_dirac f⟩
/-
**MeasureTheory.AEStronglyMeasurable.comp_measurePreserving** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：MeasureTheory.AEStronglyMeasurable.comp_measurePreserving {γ : Type*} {_ :
 MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α} {μ : Measure γ} {ν : Me
asure α} (hg : AEStronglyMeasurable g ν) (hf : MeasurePreserving f μ ν) : AEStro
nglyMeasurable (g ∘ f) μ
参数：hg : AEStronglyMeasurable g ν；hf : MeasurePreserving f μ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_quasiMeasurePreserving`：comp_qua
siMeasurePreserving {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} 
{f : γ -> α} {μ : Measure γ} {ν : Measure α} (hg : A…
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
-/
theorem MeasureTheory.AEStronglyMeasurable.comp_measurePreserving
    {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ → α} {μ : Measure γ}
    {ν : Measure α} (hg : AEStronglyMeasurable g ν) (hf : MeasurePreserving f μ ν) :
    AEStronglyMeasurable (g ∘ f) μ :=
  hg.comp_quasiMeasurePreserving hf.quasiMeasurePreserving
/-
**MeasureTheory.MeasurePreserving.aestronglyMeasurable_comp_iff** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：MeasureTheory.MeasurePreserving.aestronglyMeasurable_comp_iff {β : Type*} 
{f : α -> β} {mα : MeasurableSpace α} {μa : Measure α} {mβ : MeasurableSpace β} 
{μb : Measure β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f) {
g : β -> γ} : AEStronglyMeasurable (g ∘ f) μa ↔ AEStronglyMeasurable g μb
参数：hf : MeasurePreserving f μa μb；h₂ : MeasurableEmbedding f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasurableEmbedding.aestronglyMeasurable_map_iff`：∀ {α : Type u_1} {β : 
Type u_2} [inst : TopologicalSpace β] {γ : Type u_5} {mγ : MeasurableSpace γ}   
{mα : MeasurableSpace α} {f : γ → α} {…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem MeasureTheory.MeasurePreserving.aestronglyMeasurable_comp_iff {β : Type*}
    {f : α → β} {mα : MeasurableSpace α} {μa : Measure α} {mβ : MeasurableSpace β} {μb : Measure β}
    (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f) {g : β → γ} :
    AEStronglyMeasurable (g ∘ f) μa ↔ AEStronglyMeasurable g μb := by
  rw [← hf.map_eq, h₂.aestronglyMeasurable_map_iff]

section NormedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-
**aestronglyMeasurable_smul_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aestronglyMeasurable_smul_const_iff {f : α -> 𝕜} {c : E} (hc : c != 0) : A
EStronglyMeasurable (fun x => f x • c) μ ↔ AEStronglyMeasurable f μ
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.aestronglyMeasurable_comp_iff`：∀ {α : Type u_1} {β 
: Type u_2} {γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpac
e γ]   {m₀ : MeasurableSpace α} {μ : Mea…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
· 使用定理 `isClosedEmbedding_smul_left`：isClosedEmbedding_smul_left [T2Space E] {c 
: E} (hc : c != 0) : IsClosedEmbedding fun x : 𝕜 => x • c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem aestronglyMeasurable_smul_const_iff {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
    AEStronglyMeasurable (fun x => f x • c) μ ↔ AEStronglyMeasurable f μ :=
  (isClosedEmbedding_smul_left hc).isEmbedding.aestronglyMeasurable_comp_iff

end NormedSpace

section ContinuousLinearMapNontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-
**StronglyMeasurable.apply_continuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StronglyMeasurable.apply_continuousLinearMap {_m : MeasurableSpace α} {φ :
 α -> F ->L[𝕜] E} (hφ : StronglyMeasurable φ) (v : F) : StronglyMeasurable fun a
 => φ a v
参数：hφ : StronglyMeasurable φ；v : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.comp_stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ :
 Type u_3} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [inst_1 : Topol
ogicalSpace γ] {g : β → …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem StronglyMeasurable.apply_continuousLinearMap
    {_m : MeasurableSpace α} {φ : α → F →L[𝕜] E} (hφ : StronglyMeasurable φ) (v : F) :
    StronglyMeasurable fun a => φ a v :=
  (ContinuousLinearMap.apply 𝕜 E v).continuous.comp_stronglyMeasurable hφ

@[fun_prop]
/-
**MeasureTheory.AEStronglyMeasurable.apply_continuousLinearMap** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：MeasureTheory.AEStronglyMeasurable.apply_continuousLinearMap {φ : α -> F -
>L[𝕜] E} (hφ : AEStronglyMeasurable φ μ) (v : F) : AEStronglyMeasurable (fun a =
> φ a v) μ
参数：hφ : AEStronglyMeasurable φ μ；v : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem MeasureTheory.AEStronglyMeasurable.apply_continuousLinearMap {φ : α → F →L[𝕜] E}
    (hφ : AEStronglyMeasurable φ μ) (v : F) :
    AEStronglyMeasurable (fun a => φ a v) μ :=
  (ContinuousLinearMap.apply 𝕜 E v).continuous.comp_aestronglyMeasurable hφ
/-
**ContinuousLinearMap.aestronglyMeasurable_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContinuousLinearMap.aestronglyMeasurable_comp₂ (L : E →L[𝕜] F →L[𝕜] G) {f : α → E}
    {g : α → F} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => L (f x) (g x)) μ :=
  L.continuous₂.comp_aestronglyMeasurable₂ hf hg

end ContinuousLinearMapNontriviallyNormedField

/-
**aestronglyMeasurable_withDensity_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aestronglyMeasurable_withDensity_iff {E : Type*} [NormedAddCommGroup E] [N
ormedSpace Real E] {f : α -> Real>=0} (hf : Measurable f) {g : α -> E} : AEStron
glyMeasurable g (μ.withDensity fun x => (f x : Real>=0∞)) ↔ AEStronglyMeasurable
 (fun x => (f x : Real) • g x) μ
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
· 使用定理 `MeasureTheory.StronglyMeasurable.smul`：∀ {α : Type u_1} {β : Type u_2} {
mα : MeasurableSpace α} [inst : TopologicalSpace β] {𝕜 : Type u_5}   [inst_1 : T
opologicalSpace 𝕜] [inst_2 …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
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
（共 47 条，此处仅展示前 30 条）
-/
theorem aestronglyMeasurable_withDensity_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : α → ℝ≥0} (hf : Measurable f) {g : α → E} :
    AEStronglyMeasurable g (μ.withDensity fun x => (f x : ℝ≥0∞)) ↔
      AEStronglyMeasurable (fun x => (f x : ℝ) • g x) μ := by
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet { x : α | f x ≠ 0 } := (hf (measurableSet_singleton 0)).compl
    refine ⟨fun x => (f x : ℝ) • g' x, hf.coe_nnreal_real.stronglyMeasurable.smul g'meas, ?_⟩
    apply @ae_of_ae_restrict_of_ae_restrict_compl _ _ _ { x | f x ≠ 0 }
    · rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg'] with a ha h'a
      have : (f a : ℝ≥0∞) ≠ 0 := by simpa only [Ne, ENNReal.coe_eq_zero] using h'a
      rw [ha this]
    · filter_upwards [ae_restrict_mem A.compl] with x hx
      simp only [Classical.not_not, mem_ofPred_eq, mem_compl_iff] at hx
      simp [hx]
  · rintro ⟨g', g'meas, hg'⟩
    refine ⟨fun x => (f x : ℝ)⁻¹ • g' x, hf.coe_nnreal_real.inv.stronglyMeasurable.smul g'meas, ?_⟩
    rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal]
    filter_upwards [hg'] with x hx h'x
    rw [← hx, smul_smul, inv_mul_cancel₀, one_smul]
    simp only [Ne, ENNReal.coe_eq_zero] at h'x
    simpa only [NNReal.coe_eq_zero, Ne] using h'x
