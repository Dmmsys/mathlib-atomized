/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def
public import Mathlib.Probability.HasLaw

import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Gaussian random variables

In this file we prove basic properties of Gaussian random variables.

## Implementation note

Many lemmas are duplicated with an expanded form of some function. For instance there is
`HasGaussianLaw.add` and `HasGaussianLaw.fun_add`. The reason is that if someone wants for instance
to rewrite using `HasGaussianLaw.charFunDual_map_eq` and provide the proof of `HasGaussianLaw`
directly through dot notation, the lemma used must syntactically correspond to the random variable.

## Tags

Gaussian random variable
-/

public section

open MeasureTheory ENNReal WithLp Complex
open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {Ω E F ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section Basic

variable [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] [mE : MeasurableSpace E]
  {X Y : Ω → E}

/-
**ProbabilityTheory.HasGaussianLaw.congr** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory.HasGaussianLaw`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} [inst : TopologicalSpace E]   [inst_1 : AddCommMonoid E] [inst_2 : 
_root_.Module ℝ E] [mE : MeasurableSpace E] {X Y : Ω → E},   ProbabilityTheory.H
asGaussianLaw X P → X =ᵐ[P] Y → ProbabilityTheory.HasGaussianLaw Y P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isGaussian_map`：∀ {Ω : Type u_1} {E : T
ype u_2} {mΩ : MeasurableSpace Ω} [inst : TopologicalSpace E] [inst_1 : AddCommM
onoid E]   [inst_2 : _root_.Module ℝ …
-/
lemma HasGaussianLaw.congr {Y : Ω → E} (hX : HasGaussianLaw X P) (h : X =ᵐ[P] Y) :
    HasGaussianLaw Y P where
  isGaussian_map := by
    rw [← Measure.map_congr h]
    exact hX.isGaussian_map
/-
**ProbabilityTheory.IsGaussian.hasGaussianLaw** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.IsGaussian`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} [inst : TopologicalSpace E]   [inst_1 : AddCommMonoid E] [inst_2 : 
_root_.Module ℝ E] [mE : MeasurableSpace E] {X : Ω → E}   [ProbabilityTheory.IsG
aussian (MeasureTheory.Measure.map X P)], ProbabilityTheory.HasGaussianLaw X P
参数：MeasureTheory.Measure.map X P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsGaussian.hasGaussianLaw [IsGaussian (P.map X)] : HasGaussianLaw X P where
  isGaussian_map := inferInstance

variable {mE} in
/-
**ProbabilityTheory.IsGaussian.hasGaussianLaw_id** 是 Mathlib 中的一个定理，位于命名空间 `Prob
abilityTheory.IsGaussian`。
形式化陈述：∀ {E : Type u_2} [inst : TopologicalSpace E] [inst_1 : AddCommMonoid E] [i
nst_2 : _root_.Module ℝ E]   {mE : MeasurableSpace E} {μ : MeasureTheory.Measure
 E} [ProbabilityTheory.IsGaussian μ],   ProbabilityTheory.HasGaussianLaw id μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
-/
lemma IsGaussian.hasGaussianLaw_id {μ : Measure E} [IsGaussian μ] : HasGaussianLaw id μ where
  isGaussian_map := by rwa [Measure.map_id]

@[fun_prop]
/-
**ProbabilityTheory.HasGaussianLaw.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory.HasGaussianLaw`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} [inst : TopologicalSpace E]   [inst_1 : AddCommMonoid E] [inst_2 : 
_root_.Module ℝ E] [mE : MeasurableSpace E] {X : Ω → E},   ProbabilityTheory.Has
GaussianLaw X P → AEMeasurable X P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.of_map_ne_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Measu
rableSpace α} {mβ : MeasurableSpace β} {f : α → β}   {μ : MeasureTheory.Measure 
α}, MeasureTheory…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0
· 使用定理 `ProbabilityTheory.IsGaussian.toIsProbabilityMeasure`：∀ {E : Type u_1} [i
nst : TopologicalSpace E] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module ℝ E
]   {mE : MeasurableSpace E} (μ : Measure…
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isGaussian_map`：∀ {Ω : Type u_1} {E : T
ype u_2} {mΩ : MeasurableSpace Ω} [inst : TopologicalSpace E] [inst_1 : AddCommM
onoid E]   [inst_2 : _root_.Module ℝ …
-/
lemma HasGaussianLaw.aemeasurable (hX : HasGaussianLaw X P) : AEMeasurable X P :=
  AEMeasurable.of_map_ne_zero hX.isGaussian_map.toIsProbabilityMeasure.ne_zero
/-
**ProbabilityTheory.HasGaussianLaw.isProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.HasGaussianLaw`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} [inst : TopologicalSpace E]   [inst_1 : AddCommMonoid E] [inst_2 : 
_root_.Module ℝ E] [mE : MeasurableSpace E] {X : Ω → E},   ProbabilityTheory.Has
GaussianLaw X P → MeasureTheory.IsProbabilityMeasure P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_of_map`：∀ {α : Type u_1} {β :
 Type u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheor
y.Measure α}   (f : α → β) [MeasureTheo…
· 使用定理 `ProbabilityTheory.IsGaussian.toIsProbabilityMeasure`：∀ {E : Type u_1} [i
nst : TopologicalSpace E] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module ℝ E
]   {mE : MeasurableSpace E} (μ : Measure…
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isGaussian_map`：∀ {Ω : Type u_1} {E : T
ype u_2} {mΩ : MeasurableSpace Ω} [inst : TopologicalSpace E] [inst_1 : AddCommM
onoid E]   [inst_2 : _root_.Module ℝ …
-/
lemma HasGaussianLaw.isProbabilityMeasure (hX : HasGaussianLaw X P) : IsProbabilityMeasure P :=
    haveI := hX.isGaussian_map
    P.isProbabilityMeasure_of_map X

variable {mE} in
/-
**ProbabilityTheory.HasLaw.hasGaussianLaw** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory.HasLaw`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} [inst : TopologicalSpace E]   [inst_1 : AddCommMonoid E] [inst_2 : 
_root_.Module ℝ E] {mE : MeasurableSpace E} {X : Ω → E}   {μ : MeasureTheory.Mea
sure E},   ProbabilityTheory.HasLaw X μ P → ∀ [ProbabilityTheory.IsGaussian μ], 
ProbabilityTheory.HasGaussianLaw X P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.HasLaw.map_eq`：∀ {Ω : Type u_1} {𝓧 : Type u_2} {mΩ : M
easurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧}   {μ : MeasureTheory.Meas
ure 𝓧} {P : autoParam…
-/
lemma HasLaw.hasGaussianLaw {μ : Measure E} (hX : HasLaw X μ P) [IsGaussian μ] :
    HasGaussianLaw X P where
  isGaussian_map := by rwa [hX.map_eq]
/-
**ProbabilityTheory.HasGaussianLaw.map_of_measurable** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.HasGaussianLaw`。
形式化陈述：∀ {Ω : Type u_1} {E : Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheor
y.Measure Ω} [inst : TopologicalSpace E]   [inst_1 : AddCommMonoid E] [inst_2 : 
_root_.Module ℝ E] [mE : MeasurableSpace E] {X : Ω → E} {F : Type u_5}   [inst_3
 : TopologicalSpace F] [inst_4 : AddCommMonoid F] [inst_5 : _root_.Module ℝ F] [
inst_6 : MeasurableSpace F]   [OpensMeasurableSpace F] (L : E →L[ℝ] F),   Probab
ilityTheory.HasGaussianLaw X P → Measurable ⇑L → ProbabilityTheory.HasGaussianLa
w (⇑L ∘ X) P
参数：L : E →L[ℝ] F；⇑L ∘ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isGaussian_map`：∀ {Ω : Type u_1} {E : T
ype u_2} {mΩ : MeasurableSpace Ω} [inst : TopologicalSpace E] [inst_1 : AddCommM
onoid E]   [inst_2 : _root_.Module ℝ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AEMeasurable.map_map_of_aemeasurable`：map_map_of_aemeasurable {g : β -> 
γ} {f : α -> β} (hg : AEMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) 
: (μ.map f).map g = μ.map …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ProbabilityTheory.HasGaussianLaw.aemeasurable`：∀ {Ω : Type u_1} {E : Typ
e u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : Topologica
lSpace E]   [inst_1 : AddCommMonoid…
· 使用引理 `ProbabilityTheory.isGaussian_map_of_measurable`：isGaussian_map_of_measur
able {E F : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module Real E] {mE : 
MeasurableSpace E} [TopologicalSpace…
-/
lemma HasGaussianLaw.map_of_measurable {F : Type*} [TopologicalSpace F] [AddCommMonoid F]
    [Module ℝ F] [MeasurableSpace F] [OpensMeasurableSpace F]
    (L : E →L[ℝ] F) (hX : HasGaussianLaw X P) (hL : Measurable L) :
    HasGaussianLaw (L ∘ X) P where
  isGaussian_map := by
    have := hX.isGaussian_map
    rw [← AEMeasurable.map_map_of_aemeasurable]
    · exact isGaussian_map_of_measurable hL
    all_goals fun_prop
/-
**ProbabilityTheory.HasGaussianLaw.map_eq_gaussianReal** 是 Mathlib 中的一个定理，位于命名空间
 `ProbabilityTheory.HasGaussianLaw`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} {X
 : Ω → ℝ},   ProbabilityTheory.HasGaussianLaw X P →     MeasureTheory.Measure.ma
p X P =       ProbabilityTheory.gaussianReal (∫ (x : Ω), X x ∂P) (ProbabilityThe
ory.variance X P).toNNReal
参数：∫ (x : Ω), X x ∂P；ProbabilityTheory.variance X P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IsGaussian.eq_gaussianReal`：∀ (μ : MeasureTheory.Measu
re ℝ),   ProbabilityTheory.IsGaussian μ →     μ = ProbabilityTheory.gaussianReal
 (∫ (x : ℝ), id x ∂μ) (Probability…
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isGaussian_map`：∀ {Ω : Type u_1} {E : T
ype u_2} {mΩ : MeasurableSpace Ω} [inst : TopologicalSpace E] [inst_1 : AddCommM
onoid E]   [inst_2 : _root_.Module ℝ …
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `ProbabilityTheory.HasGaussianLaw.aemeasurable`：∀ {Ω : Type u_1} {E : Typ
e u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : Topologica
lSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `ProbabilityTheory.variance_map`：variance_map {Ω' : Type*} {mΩ' : Measura
bleSpace Ω'} {μ : Measure Ω'} {Y : Ω' -> Ω} (hX : AEMeasurable X (μ.map Y)) (hY 
: AEMeasurable Y μ) …
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
-/
lemma HasGaussianLaw.map_eq_gaussianReal {X : Ω → ℝ} (h : HasGaussianLaw X P) :
    P.map X = gaussianReal P[X] Var[X; P].toNNReal := by
  rw [h.isGaussian_map.eq_gaussianReal (.map _ _), integral_map, variance_map]
  · rfl
  all_goals fun_prop

end Basic

namespace HasGaussianLaw

variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {X : Ω → E}

/-
**ProbabilityTheory.HasGaussianLaw.of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Pr
obabilityTheory.HasGaussianLaw`。
形式化陈述：of_subsingleton [NormedSpace Real E] [Subsingleton E] [IsProbabilityMeasur
e P] : HasGaussianLaw X P where isGaussian_map
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.isProbabilityMeasure_map`：∀ {α : Type u_1} {β : Ty
pe u_2} {m0 : MeasurableSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.M
easure α}   [MeasureTheory.IsProbabi…
· 使用定理 `aemeasurable_of_subsingleton_codomain`：aemeasurable_of_subsingleton_codo
main [Subsingleton β] : AEMeasurable f μ
· 使用定理 `ProbabilityTheory.IsGaussian.of_subsingleton`：∀ {E : Type u_1} [inst : N
ormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : MeasurableSpace E] [Bo
relSpace E]   {μ : MeasureTheory.M…
-/
lemma of_subsingleton [NormedSpace ℝ E] [Subsingleton E] [IsProbabilityMeasure P] :
    HasGaussianLaw X P where
  isGaussian_map := by
    have : IsProbabilityMeasure (P.map X) := P.isProbabilityMeasure_map (by fun_prop)
    exact .of_subsingleton
/-
**ProbabilityTheory.HasGaussianLaw.charFun_map_eq** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory.HasGaussianLaw`。
形式化陈述：charFun_map_eq [InnerProductSpace Real E] (t : E) (hX : HasGaussianLaw X P
) : charFun (P.map X) t = exp ((P[fun ω => ⟪t, X ω⟫] : Real) * I - Var[fun ω => 
⟪t, X ω⟫; P] / 2)
参数：t : E；hX : HasGaussianLaw X P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IsGaussian.charFun_eq`：∀ {E : Type u_3} [inst : Normed
AddCommGroup E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : MeasurableSpace E]   
[BorelSpace E] {μ : MeasureTh…
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isGaussian_map`：∀ {Ω : Type u_1} {E : T
ype u_2} {mΩ : MeasurableSpace Ω} [inst : TopologicalSpace E] [inst_1 : AddCommM
onoid E]   [inst_2 : _root_.Module ℝ …
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `ProbabilityTheory.HasGaussianLaw.aemeasurable`：∀ {Ω : Type u_1} {E : Typ
e u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : Topologica
lSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Continuous.inner`：Continuous.inner (hf : Continuous f) (hg : Continuous 
g) : Continuous fun t => ⟪f t, g t⟫
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用引理 `ProbabilityTheory.variance_map`：variance_map {Ω' : Type*} {mΩ' : Measura
bleSpace Ω'} {μ : Measure Ω'} {Y : Ω' -> Ω} (hX : AEMeasurable X (μ.map Y)) (hY 
: AEMeasurable Y μ) …
· 使用定理 `Continuous.aemeasurable`：Continuous.aemeasurable {f : α -> γ} (h : Conti
nuous f) {μ : Measure α} : AEMeasurable f μ
· 使用定理 `integral_complex_ofReal`：integral_complex_ofReal {f : X -> Real} : ∫ x, 
(f x : Complex) ∂μ = ∫ x, f x ∂μ
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
lemma charFun_map_eq [InnerProductSpace ℝ E] (t : E) (hX : HasGaussianLaw X P) :
    charFun (P.map X) t = exp ((P[fun ω ↦ ⟪t, X ω⟫] : ℝ) * I - Var[fun ω ↦ ⟪t, X ω⟫; P] / 2) := by
  rw [hX.isGaussian_map.charFun_eq, integral_map hX.aemeasurable (by fun_prop),
    variance_map (by fun_prop) hX.aemeasurable, integral_complex_ofReal, Function.comp_def]
/-
**ProbabilityTheory.HasGaussianLaw._root_.ProbabilityTheory.hasGaussianLaw_iff_c
harFun_map_eq** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.HasGaussianLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ProbabilityTheory.hasGaussianLaw_iff_charFun_map_eq [CompleteSpace E]
    [InnerProductSpace ℝ E] [IsFiniteMeasure P] (hX : AEMeasurable X P) :
    HasGaussianLaw X P ↔ ∀ t,
    charFun (P.map X) t = exp ((P[fun ω ↦ ⟪t, X ω⟫] : ℝ) * I - Var[fun ω ↦ ⟪t, X ω⟫; P] / 2) where
  mp h := h.charFun_map_eq
  mpr h := by
    refine ⟨isGaussian_iff_charFun_eq.2 fun t ↦ ?_⟩
    rw [h, integral_map, variance_map, integral_complex_ofReal, Function.comp_def]
    all_goals fun_prop

variable [NormedSpace ℝ E]
/-
**ProbabilityTheory.HasGaussianLaw.charFunDual_map_eq** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory.HasGaussianLaw`。
形式化陈述：charFunDual_map_eq (L : StrongDual Real E) (hX : HasGaussianLaw X P) : cha
rFunDual (P.map X) L = exp ((P[L ∘ X] : Real) * I - Var[L ∘ X; P] / 2)
参数：L : StrongDual Real E；hX : HasGaussianLaw X P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IsGaussian.charFunDual_eq`：∀ {E : Type u_1} [inst : No
rmedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : MeasurableSpace E] [Bor
elSpace E]   {μ : MeasureTheory.M…
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isGaussian_map`：∀ {Ω : Type u_1} {E : T
ype u_2} {mΩ : MeasurableSpace Ω} [inst : TopologicalSpace E] [inst_1 : AddCommM
onoid E]   [inst_2 : _root_.Module ℝ …
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `ProbabilityTheory.HasGaussianLaw.aemeasurable`：∀ {Ω : Type u_1} {E : Typ
e u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : Topologica
lSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Continuous.clm_apply`：Continuous.clm_apply {f : X -> E ->L[𝕜] F} {g : X 
-> E} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => f x (g x))
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用引理 `ProbabilityTheory.variance_map`：variance_map {Ω' : Type*} {mΩ' : Measura
bleSpace Ω'} {μ : Measure Ω'} {Y : Ω' -> Ω} (hX : AEMeasurable X (μ.map Y)) (hY 
: AEMeasurable Y μ) …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…
· 使用定理 `integral_complex_ofReal`：integral_complex_ofReal {f : X -> Real} : ∫ x, 
(f x : Complex) ∂μ = ∫ x, f x ∂μ
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
lemma charFunDual_map_eq (L : StrongDual ℝ E) (hX : HasGaussianLaw X P) :
    charFunDual (P.map X) L = exp ((P[L ∘ X] : ℝ) * I - Var[L ∘ X; P] / 2) := by
  rw [hX.isGaussian_map.charFunDual_eq, integral_map hX.aemeasurable (by fun_prop),
    variance_map (by fun_prop) hX.aemeasurable, integral_complex_ofReal, Function.comp_def]
/-
**ProbabilityTheory.HasGaussianLaw._root_.ProbabilityTheory.hasGaussianLaw_iff_c
harFunDual_map_eq** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory.HasGaussianLaw`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ProbabilityTheory.hasGaussianLaw_iff_charFunDual_map_eq
    [IsFiniteMeasure P] (hX : AEMeasurable X P) :
    HasGaussianLaw X P ↔ ∀ L,
    charFunDual (P.map X) L = exp ((P[L ∘ X] : ℝ) * I - Var[L ∘ X; P] / 2) where
  mp h := h.charFunDual_map_eq
  mpr h := by
    refine ⟨isGaussian_iff_charFunDual_eq.2 fun t ↦ ?_⟩
    rw [h, integral_map, variance_map, integral_complex_ofReal, Function.comp_def]
    all_goals fun_prop
/-
**ProbabilityTheory.HasGaussianLaw.charFunDual_map_eq_fun** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory.HasGaussianLaw`。
形式化陈述：charFunDual_map_eq_fun (L : StrongDual Real E) (hX : HasGaussianLaw X P) :
 charFunDual (P.map X) L = exp ((∫ ω, L (X ω) ∂P) * I - Var[fun ω => L (X ω); P]
 / 2)
参数：L : StrongDual Real E；hX : HasGaussianLaw X P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.HasGaussianLaw.charFunDual_map_eq`：charFunDual_map_eq 
(L : StrongDual Real E) (hX : HasGaussianLaw X P) : charFunDual (P.map X) L = ex
p ((P[L ∘ X] : Real) * I - Var[L ∘ X; P] …
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
lemma charFunDual_map_eq_fun (L : StrongDual ℝ E) (hX : HasGaussianLaw X P) :
    charFunDual (P.map X) L = exp ((∫ ω, L (X ω) ∂P) * I - Var[fun ω ↦ L (X ω); P] / 2) := by
  rw [hX.charFunDual_map_eq, Function.comp_def]

/-- A Gaussian random variable has moments of all orders. -/
/-
**ProbabilityTheory.HasGaussianLaw.memLp** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory.HasGaussianLaw`。
形式化陈述：memLp [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X
 P) {p : Real>=0∞} (hp : p != ∞) : MemLp X p P
参数：hX : HasGaussianLaw X P；hp : p != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
· 使用定理 `MeasureTheory.memLp_map_measure_iff`：memLp_map_measure_iff (hg : AEStron
glyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) : MemLp g p (Measure.
map f μ) ↔ MemLp (g ∘ f) …
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ProbabilityTheory.HasGaussianLaw.aemeasurable`：∀ {Ω : Type u_1} {E : Typ
e u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : Topologica
lSpace E]   [inst_1 : AddCommMonoid…
· 使用引理 `ProbabilityTheory.IsGaussian.memLp_id`：memLp_id (μ : Measure E) [IsGauss
ian μ] (p : Real>=0∞) (hp : p != ∞) : MemLp id p μ
· 使用定理 `ProbabilityTheory.HasGaussianLaw.isGaussian_map`：∀ {Ω : Type u_1} {E : T
ype u_2} {mΩ : MeasurableSpace Ω} [inst : TopologicalSpace E] [inst_1 : AddCommM
onoid E]   [inst_2 : _root_.Module ℝ …

--- 原说明 ---
A Gaussian random variable has moments of all orders.
-/
lemma memLp [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P)
    {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp X p P := by
  rw [← Function.id_comp X, ← memLp_map_measure_iff]
  · exact hX.isGaussian_map.memLp_id _ p hp
  all_goals fun_prop
/-
**ProbabilityTheory.HasGaussianLaw.memLp_two** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.HasGaussianLaw`。
形式化陈述：memLp_two [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianL
aw X P) : MemLp X 2 P
参数：hX : HasGaussianLaw X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.memLp`：memLp [CompleteSpace E] [SecondC
ountableTopology E] (hX : HasGaussianLaw X P) {p : Real>=0∞} (hp : p != ∞) : Mem
Lp X p P
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false`：¬False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma memLp_two [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P) :
    MemLp X 2 P := hX.memLp (by norm_num)
/-
**ProbabilityTheory.HasGaussianLaw.integrable** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory.HasGaussianLaw`。
形式化陈述：integrable [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussian
Law X P) : Integrable X P
参数：hX : HasGaussianLaw X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用引理 `ProbabilityTheory.HasGaussianLaw.memLp`：memLp [CompleteSpace E] [SecondC
ountableTopology E] (hX : HasGaussianLaw X P) {p : Real>=0∞} (hp : p != ∞) : Mem
Lp X p P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false`：¬False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma integrable [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P) :
    Integrable X P :=
  memLp_one_iff_integrable.1 <| hX.memLp (by norm_num)

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
/-
**ProbabilityTheory.HasGaussianLaw.map** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory.HasGaussianLaw`。
形式化陈述：map (hX : HasGaussianLaw X P) (L : E ->L[Real] F) : HasGaussianLaw (L ∘ X)
 P
参数：hX : HasGaussianLaw X P；L : E ->L[Real] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.map_of_measurable`：∀ {Ω : Type u_1} {E 
: Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : Topol
ogicalSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ContinuousLinearMap.measurable`：∀ {R : Type u_2} {E : Type u_3} {F : Typ
e u_4} [inst : Semiring R] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root
_.Module R E] [inst_…
-/
lemma map (hX : HasGaussianLaw X P) (L : E →L[ℝ] F) : HasGaussianLaw (L ∘ X) P :=
  hX.map_of_measurable L (by fun_prop)
/-
**ProbabilityTheory.HasGaussianLaw.map_fun** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.HasGaussianLaw`。
形式化陈述：map_fun (hX : HasGaussianLaw X P) (L : E ->L[Real] F) : HasGaussianLaw (fu
n ω => L (X ω)) P
参数：hX : HasGaussianLaw X P；L : E ->L[Real] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map`：map (hX : HasGaussianLaw X P) (L :
 E ->L[Real] F) : HasGaussianLaw (L ∘ X) P
-/
lemma map_fun (hX : HasGaussianLaw X P) (L : E →L[ℝ] F) : HasGaussianLaw (fun ω ↦ L (X ω)) P :=
  hX.map L
/-
**ProbabilityTheory.HasGaussianLaw.map_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory.HasGaussianLaw`。
形式化陈述：map_equiv (hX : HasGaussianLaw X P) (L : E ≃L[Real] F) : HasGaussianLaw (L
 ∘ X) P
参数：hX : HasGaussianLaw X P；L : E ≃L[Real] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map`：map (hX : HasGaussianLaw X P) (L :
 E ->L[Real] F) : HasGaussianLaw (L ∘ X) P
-/
lemma map_equiv (hX : HasGaussianLaw X P) (L : E ≃L[ℝ] F) : HasGaussianLaw (L ∘ X) P :=
  hX.map L.toContinuousLinearMap
/-
**ProbabilityTheory.HasGaussianLaw.map_equiv_fun** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory.HasGaussianLaw`。
形式化陈述：map_equiv_fun (hX : HasGaussianLaw X P) (L : E ≃L[Real] F) : HasGaussianLa
w (fun ω => L (X ω)) P
参数：hX : HasGaussianLaw X P；L : E ≃L[Real] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map_equiv`：map_equiv (hX : HasGaussianL
aw X P) (L : E ≃L[Real] F) : HasGaussianLaw (L ∘ X) P
-/
lemma map_equiv_fun (hX : HasGaussianLaw X P) (L : E ≃L[ℝ] F) :
    HasGaussianLaw (fun ω ↦ L (X ω)) P := hX.map_equiv L

section SpecificMaps

/-
**ProbabilityTheory.HasGaussianLaw.smul** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.HasGaussianLaw`。
形式化陈述：smul (c : Real) (hX : HasGaussianLaw X P) : HasGaussianLaw (c • X) P
参数：c : Real；hX : HasGaussianLaw X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map`：map (hX : HasGaussianLaw X P) (L :
 E ->L[Real] F) : HasGaussianLaw (L ∘ X) P
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma smul (c : ℝ) (hX : HasGaussianLaw X P) : HasGaussianLaw (c • X) P :=
  hX.map (.lsmul ℝ ℝ c)
/-
**ProbabilityTheory.HasGaussianLaw.fun_smul** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory.HasGaussianLaw`。
形式化陈述：fun_smul (c : Real) (hX : HasGaussianLaw X P) : HasGaussianLaw (fun ω => c
 • (X ω)) P
参数：c : Real；hX : HasGaussianLaw X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.smul`：smul (c : Real) (hX : HasGaussian
Law X P) : HasGaussianLaw (c • X) P
-/
lemma fun_smul (c : ℝ) (hX : HasGaussianLaw X P) : HasGaussianLaw (fun ω ↦ c • (X ω)) P :=
  hX.smul c
/-
**ProbabilityTheory.HasGaussianLaw.neg** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory.HasGaussianLaw`。
形式化陈述：neg (hX : HasGaussianLaw X P) : HasGaussianLaw (-X) P
参数：hX : HasGaussianLaw X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `ProbabilityTheory.HasGaussianLaw.smul`：smul (c : Real) (hX : HasGaussian
Law X P) : HasGaussianLaw (c • X) P
-/
lemma neg (hX : HasGaussianLaw X P) : HasGaussianLaw (-X) P := by simpa using hX.smul (-1)
/-
**ProbabilityTheory.HasGaussianLaw.fun_neg** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.HasGaussianLaw`。
形式化陈述：fun_neg (hX : HasGaussianLaw X P) : HasGaussianLaw (fun ω => -(X ω)) P
参数：hX : HasGaussianLaw X P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.neg`：neg (hX : HasGaussianLaw X P) : Ha
sGaussianLaw (-X) P
-/
lemma fun_neg (hX : HasGaussianLaw X P) : HasGaussianLaw (fun ω ↦ -(X ω)) P :=
  hX.neg

section Prod

variable {Y : Ω → F}

/-
**ProbabilityTheory.HasGaussianLaw.toLp_prodMk** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory.HasGaussianLaw`。
形式化陈述：toLp_prodMk [SecondCountableTopologyEither E F] (p : Real>=0∞) [Fact (1 <=
 p)] (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) : HasGaussianLaw (fun ω => t
oLp p (X ω, Y ω)) P
参数：p : Real>=0∞；1 <= p；hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map_equiv`：map_equiv (hX : HasGaussianL
aw X P) (L : E ≃L[Real] F) : HasGaussianLaw (L ∘ X) P
-/
lemma toLp_prodMk [SecondCountableTopologyEither E F] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω ↦ toLp p (X ω, Y ω)) P :=
  hXY.map_equiv (WithLp.prodContinuousLinearEquiv p ℝ E F).symm

omit [BorelSpace F] in
/-
**ProbabilityTheory.HasGaussianLaw.fst** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory.HasGaussianLaw`。
形式化陈述：fst (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) : HasGaussianLaw X P
参数：hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.map_of_measurable`：∀ {Ω : Type u_1} {E 
: Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : Topol
ogicalSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
-/
lemma fst (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) : HasGaussianLaw X P :=
  hXY.map_of_measurable (.fst ℝ E F) measurable_fst

omit [BorelSpace E] in
/-
**ProbabilityTheory.HasGaussianLaw.snd** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory.HasGaussianLaw`。
形式化陈述：snd (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) : HasGaussianLaw Y P
参数：hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.map_of_measurable`：∀ {Ω : Type u_1} {E 
: Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : Topol
ogicalSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
lemma snd (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) : HasGaussianLaw Y P :=
  hXY.map_of_measurable (.snd ℝ E F) measurable_snd

variable [SecondCountableTopology E] {Y : Ω → E}
/-
**ProbabilityTheory.HasGaussianLaw.add** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory.HasGaussianLaw`。
形式化陈述：add (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) : HasGaussianLaw (X + Y
) P
参数：hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map`：map (hX : HasGaussianLaw X P) (L :
 E ->L[Real] F) : HasGaussianLaw (L ∘ X) P
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
lemma add (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) : HasGaussianLaw (X + Y) P :=
  hXY.map (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E)
/-
**ProbabilityTheory.HasGaussianLaw.fun_add** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.HasGaussianLaw`。
形式化陈述：fun_add (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) : HasGaussianLaw (f
un ω => X ω + Y ω) P
参数：hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.add`：add (hXY : HasGaussianLaw (fun ω =
> (X ω, Y ω)) P) : HasGaussianLaw (X + Y) P
-/
lemma fun_add (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω ↦ X ω + Y ω) P :=
  hXY.add
/-
**ProbabilityTheory.HasGaussianLaw.sub** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory.HasGaussianLaw`。
形式化陈述：sub (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) : HasGaussianLaw (X - Y
) P
参数：hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map`：map (hX : HasGaussianLaw X P) (L :
 E ->L[Real] F) : HasGaussianLaw (L ∘ X) P
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
lemma sub (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) : HasGaussianLaw (X - Y) P :=
  hXY.map (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E)
/-
**ProbabilityTheory.HasGaussianLaw.fun_sub** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.HasGaussianLaw`。
形式化陈述：fun_sub (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) : HasGaussianLaw (f
un ω => X ω - Y ω) P
参数：hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.sub`：sub (hXY : HasGaussianLaw (fun ω =
> (X ω, Y ω)) P) : HasGaussianLaw (X - Y) P
-/
lemma fun_sub (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω ↦ X ω - Y ω) P :=
  hXY.sub

end Prod

section Pi

variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  {X : (i : ι) → Ω → E i}

/-
**ProbabilityTheory.HasGaussianLaw.eval** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory.HasGaussianLaw`。
形式化陈述：eval (hX : HasGaussianLaw (fun ω => (X · ω)) P) (i : ι) : HasGaussianLaw (
X i) P
参数：hX : HasGaussianLaw (fun ω => (X · ω)) P；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.HasGaussianLaw.map_of_measurable`：∀ {Ω : Type u_1} {E 
: Type u_2} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [inst : Topol
ogicalSpace E]   [inst_1 : AddCommMonoid…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
lemma eval (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (i : ι) :
    HasGaussianLaw (X i) P := hX.map_of_measurable (.proj i) (measurable_pi_apply i)

variable [∀ i, SecondCountableTopology (E i)]
/-
**ProbabilityTheory.HasGaussianLaw.prodMk** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory.HasGaussianLaw`。
形式化陈述：prodMk [Finite ι] (hX : HasGaussianLaw (fun ω => (X · ω)) P) (i j : ι) : H
asGaussianLaw (fun ω => (X i ω, X j ω)) P
参数：hX : HasGaussianLaw (fun ω => (X · ω)) P；i j : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map`：map (hX : HasGaussianLaw X P) (L :
 E ->L[Real] F) : HasGaussianLaw (L ∘ X) P
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
-/
lemma prodMk [Finite ι] (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (i j : ι) :
    HasGaussianLaw (fun ω ↦ (X i ω, X j ω)) P :=
  letI := Fintype.ofFinite ι
  hX.map (.prod (.proj i) (.proj j))
/-
**ProbabilityTheory.HasGaussianLaw.toLp_pi** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.HasGaussianLaw`。
形式化陈述：toLp_pi [Finite ι] (p : Real>=0∞) [Fact (1 <= p)] (hX : HasGaussianLaw (fu
n ω => (X · ω)) P) : HasGaussianLaw (fun ω => toLp p (X · ω)) P
参数：p : Real>=0∞；1 <= p；hX : HasGaussianLaw (fun ω => (X · ω)) P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map_equiv`：map_equiv (hX : HasGaussianL
aw X P) (L : E ≃L[Real] F) : HasGaussianLaw (L ∘ X) P
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
-/
lemma toLp_pi [Finite ι] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) :
    HasGaussianLaw (fun ω ↦ toLp p (X · ω)) P :=
  have := Fintype.ofFinite ι
  hX.map_equiv (PiLp.continuousLinearEquiv p ℝ E).symm

variable [Fintype ι]
/-
**ProbabilityTheory.HasGaussianLaw.sum** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory.HasGaussianLaw`。
形式化陈述：sum {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpa
ce E] [BorelSpace E] [SecondCountableTopology E] {X : ι -> Ω -> E} (hX : HasGaus
sianLaw (fun ω => (X · ω)) P) : HasGaussianLaw (∑ i, X i) P
参数：hX : HasGaussianLaw (fun ω => (X · ω)) P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.HasGaussianLaw.map`：map (hX : HasGaussianLaw X P) (L :
 E ->L[Real] F) : HasGaussianLaw (L ∘ X) P
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {X : ι → Ω → E} (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) :
    HasGaussianLaw (∑ i, X i) P := by
  convert! hX.map (∑ i, .proj i)
  ext; simp
/-
**ProbabilityTheory.HasGaussianLaw.fun_sum** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory.HasGaussianLaw`。
形式化陈述：fun_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [Measurabl
eSpace E] [BorelSpace E] [SecondCountableTopology E] {X : ι -> Ω -> E} (hX : Has
GaussianLaw (fun ω => (X · ω)) P) : HasGaussianLaw (fun ω => ∑ i, X i ω) P
参数：hX : HasGaussianLaw (fun ω => (X · ω)) P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.HasGaussianLaw.sum`：sum {E : Type*} [NormedAddCommGrou
p E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTop
ology E] {X : ι -> Ω -> E}…
-/
lemma fun_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {X : ι → Ω → E} (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) :
    HasGaussianLaw (fun ω ↦ ∑ i, X i ω) P := by
  convert! hX.sum
  simp

end Pi

end SpecificMaps

end HasGaussianLaw

end ProbabilityTheory

