/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Convolution of functions

This file defines the convolution on two functions, i.e. `x ↦ ∫ f(t)g(x - t) ∂t`.
In the general case, these functions can be vector-valued, and have an arbitrary (additive)
group as domain. We use a continuous bilinear operation `L` on these function values as
"multiplication". The domain must be equipped with a Haar measure `μ`
(though many individual results have weaker conditions on `μ`).

For many applications we can take `L = ContinuousLinearMap.lsmul ℝ ℝ` or
`L = ContinuousLinearMap.mul ℝ ℝ`.

We also define `ConvolutionExists` and `ConvolutionExistsAt` to state that the convolution is
well-defined (everywhere or at a single point). These conditions are needed for pointwise
computations (e.g. `ConvolutionExistsAt.distrib_add`), but are generally not strong enough for any
local (or global) properties of the convolution. For this we need stronger assumptions on `f`
and/or `g`, and generally if we impose stronger conditions on one of the functions, we can impose
weaker conditions on the other.
We have proven many of the properties of the convolution assuming one of these functions
has compact support (in which case the other function only needs to be locally integrable).
We still need to prove the properties for other pairs of conditions (e.g. both functions are
rapidly decreasing)

## Design Decisions

We use a bilinear map `L` to "multiply" the two functions in the integrand.
This generality has several advantages

* This allows us to compute the total derivative of the convolution, in case the functions are
  multivariate. The total derivative is again a convolution, but where the codomains of the
  functions can be higher-dimensional. See `HasCompactSupport.hasFDerivAt_convolution_right`.
* This allows us to use `@[to_additive]` everywhere (which would not be possible if we would use
  `mul`/`smul` in the integral, since `@[to_additive]` will incorrectly also try to additivize
  those definitions).
* We need to support the case where at least one of the functions is vector-valued, but if we use
  `smul` to multiply the functions, that would be an asymmetric definition.

## Main Definitions

* `MeasureTheory.convolution f g L μ x = (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ`
  is the convolution of `f` and `g` w.r.t. the continuous bilinear map `L` and measure `μ`.
* `MeasureTheory.ConvolutionExistsAt f g x L μ` states that the convolution `(f ⋆[L, μ] g) x`
  is well-defined (i.e. the integral exists).
* `MeasureTheory.ConvolutionExists f g L μ` states that the convolution `f ⋆[L, μ] g`
  is well-defined at each point.

## Main Results

* `MeasureTheory.convolution_tendsto_right`: Given a sequence of nonnegative normalized functions
  whose support tends to a small neighborhood around `0`, the convolution tends to the right
  argument. This is specialized to bump functions in `ContDiffBump.convolution_tendsto_right`.

## Notation

The following notations are localized in the scope `Convolution`:
* `f ⋆[L, μ] g` for the convolution. Note: you have to use parentheses to apply the convolution
  to an argument: `(f ⋆[L, μ] g) x`.
* `f ⋆[L] g := f ⋆[L, volume] g`
* `f ⋆ g := f ⋆[lsmul ℝ ℝ] g`

## To do

* Existence and (uniform) continuity of the convolution if
  one of the maps is in `ℒ^p` and the other in `ℒ^q` with `1 / p + 1 / q = 1`.
  This might require a generalization of `MeasureTheory.MemLp.smul` where `smul` is generalized
  to a continuous bilinear map.
  (see e.g. [Fremlin, *Measure Theory* (volume 2)][fremlin_vol2], 255K)
* The convolution is an `AEStronglyMeasurable` function
  (see e.g. [Fremlin, *Measure Theory* (volume 2)][fremlin_vol2], 255I).
* Prove properties about the convolution if both functions are rapidly decreasing.
* Use `@[to_additive]` everywhere (this likely requires changes in `to_additive`)
-/

assert_not_exists ContDiffAt HasDerivAt

@[expose] public section
open Set Function Filter MeasureTheory MeasureTheory.Measure TopologicalSpace

open Bornology ContinuousLinearMap Metric Topology
open scoped Pointwise NNReal Filter

universe u𝕜 uG uE uE' uE'' uF uF' uF'' uP

variable {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {E'' : Type uE''} {F : Type uF}
  {F' : Type uF'} {F'' : Type uF''} {P : Type uP}

variable [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup E'']
  [NormedAddCommGroup F] {f f' : G → E} {g g' : G → E'} {x x' : G} {y y' : E}

namespace MeasureTheory
section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 E''] [NormedSpace 𝕜 F]
variable (L : E →L[𝕜] E' →L[𝕜] F)

section NoMeasurability

variable [AddGroup G] [TopologicalSpace G]

/-
**MeasureTheory.convolution_integrand_bound_right_of_le_of_subset** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：convolution_integrand_bound_right_of_le_of_subset {C : Real} (hC : forall 
i, ‖g i‖ <= C) {x t : G} {s u : Set G} (hx : x in s) (hu : -tsupport g + s subse
teq u) : ‖L (f t) (g (x - t))‖ <= u.indicator (fun t => ‖L‖ * ‖f t‖ * C) t
参数：hC : forall i, ‖g i‖ <= C；hx : x in s；hu : -tsupport g + s subseteq u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Set.le_indicator`：∀ {α : Type u_2} {M : Type u_3} [inst : LE M] [inst_1 
: Zero M] {s : Set α} {f g : α → M},   (∀ a ∈ s, f a ≤ g a) → (∀ a ∉ s, f a ≤ 0)
 → f ≤…
· 使用定理 `ContinuousLinearMap.le_of_opNorm₂_le_of_le`：le_of_opNorm₂_le_of_le [Ring
HomIsometric σ₁₃] (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) {x : E} {y : F} {a b c : Real}
 (hf : ‖f‖ <= a) (hx : ‖x‖ <= b)…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.neg_mem_neg`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s : Set α} {
a : α}, -a ∈ -s ↔ a ∈ s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.notMem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M]
 {f : ι → M} {x : ι}, x ∉ Function.support f ↔ f x = 0
· 使用定理 `ContinuousLinearMap.map_zero`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : 
Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 
: TopologicalSpace…
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
-/
theorem convolution_integrand_bound_right_of_le_of_subset {C : ℝ} (hC : ∀ i, ‖g i‖ ≤ C) {x t : G}
    {s u : Set G} (hx : x ∈ s) (hu : -tsupport g + s ⊆ u) :
    ‖L (f t) (g (x - t))‖ ≤ u.indicator (fun t => ‖L‖ * ‖f t‖ * C) t := by
  -- Porting note: had to add `f := _`
  refine le_indicator (f := fun t ↦ ‖L (f t) (g (x - t))‖) (fun t _ => ?_) (fun t ht => ?_) t
  · apply_rules [L.le_of_opNorm₂_le_of_le, le_rfl]
  · have : x - t ∉ support g := by
      refine mt (fun hxt => hu ?_) ht
      refine ⟨_, Set.neg_mem_neg.mpr (subset_closure hxt), _, hx, ?_⟩
      simp only [neg_sub, sub_add_cancel]
    simp only [notMem_support.mp this, (L _).map_zero, norm_zero, le_rfl]
/-
**MeasureTheory._root_.HasCompactSupport.convolution_integrand_bound_right_of_su
bset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.HasCompactSupport.convolution_integrand_bound_right_of_subset
    (hcg : HasCompactSupport g) (hg : Continuous g)
    {x t : G} {s u : Set G} (hx : x ∈ s) (hu : -tsupport g + s ⊆ u) :
    ‖L (f t) (g (x - t))‖ ≤ u.indicator (fun t => ‖L‖ * ‖f t‖ * ⨆ i, ‖g i‖) t := by
  refine convolution_integrand_bound_right_of_le_of_subset _ (fun i => ?_) hx hu
  exact le_ciSup (hg.norm.bddAbove_range_of_hasCompactSupport hcg.norm) _
/-
**MeasureTheory._root_.HasCompactSupport.convolution_integrand_bound_right** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.HasCompactSupport.convolution_integrand_bound_right (hcg : HasCompactSupport g)
    (hg : Continuous g) {x t : G} {s : Set G} (hx : x ∈ s) :
    ‖L (f t) (g (x - t))‖ ≤ (-tsupport g + s).indicator (fun t => ‖L‖ * ‖f t‖ * ⨆ i, ‖g i‖) t :=
  hcg.convolution_integrand_bound_right_of_subset L hg hx Subset.rfl
/-
**MeasureTheory._root_.Continuous.convolution_integrand_fst** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Continuous.convolution_integrand_fst [ContinuousSub G] (hg : Continuous g) (t : G) :
    Continuous fun x => L (f t) (g (x - t)) :=
  L.continuous₂.comp₂ continuous_const <| by fun_prop
/-
**MeasureTheory._root_.HasCompactSupport.convolution_integrand_bound_left** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.HasCompactSupport.convolution_integrand_bound_left (hcf : HasCompactSupport f)
    (hf : Continuous f) {x t : G} {s : Set G} (hx : x ∈ s) :
    ‖L (f (x - t)) (g t)‖ ≤
      (-tsupport f + s).indicator (fun t => (‖L‖ * ⨆ i, ‖f i‖) * ‖g t‖) t := by
  convert! hcf.convolution_integrand_bound_right L.flip hf hx using 1
  simp_rw [L.opNorm_flip, mul_right_comm]

end NoMeasurability

section Measurability
variable [MeasurableSpace G] {μ ν : Measure G}

/-- The convolution of `f` and `g` exists at `x` when the function `t ↦ L (f t) (g (x - t))` is
integrable. There are various conditions on `f` and `g` to prove this. -/
/-
**MeasureTheory.ConvolutionExistsAt** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：ConvolutionExistsAt [Sub G] (f : G -> E) (g : G -> E') (x : G) (L : E ->L[
𝕜] E' ->L[𝕜] F) (μ : Measure G
参数：f : G -> E；g : G -> E'；x : G；L : E ->L[𝕜] E' ->L[𝕜] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The convolution of `f` and `g` exists at `x` when the function `t ↦ L (f t) (g (
x - t))` is
integrable. There are various conditions on `f` and `g` to prove this.
-/
def ConvolutionExistsAt [Sub G] (f : G → E) (g : G → E') (x : G) (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measure G := by volume_tac) : Prop :=
  Integrable (fun t => L (f t) (g (x - t))) μ

/-- The convolution of `f` and `g` exists when the function `t ↦ L (f t) (g (x - t))` is integrable
for all `x : G`. There are various conditions on `f` and `g` to prove this. -/
/-
**MeasureTheory.ConvolutionExists** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：ConvolutionExists [Sub G] (f : G -> E) (g : G -> E') (L : E ->L[𝕜] E' ->L[
𝕜] F) (μ : Measure G
参数：f : G -> E；g : G -> E'；L : E ->L[𝕜] E' ->L[𝕜] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The convolution of `f` and `g` exists when the function `t ↦ L (f t) (g (x - t))
` is integrable
for all `x : G`. There are various conditions on `f` and `g` to prove this.
-/
def ConvolutionExists [Sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measure G := by volume_tac) : Prop :=
  ∀ x : G, ConvolutionExistsAt f g x L μ

section ConvolutionExists

variable {L} in
/-
**MeasureTheory.ConvolutionExistsAt.integrable** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.ConvolutionExistsAt`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f : G → E} {g : G → E'}   [inst_3 : NontriviallyNormedField 𝕜]
 [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : NormedSpace 𝕜 
F]   {L : E →L[𝕜] E' →L[𝕜] F} [inst_7 : MeasurableSpace G] {μ : MeasureTheory.Me
asure G} [inst_8 : Sub G] {x : G},   MeasureTheory.ConvolutionExistsAt f g x L μ
 → MeasureTheory.Integrable (fun t => (L (f t)) (g (x - t))) μ
参数：fun t => (L (f t)) (g (x - t))。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem ConvolutionExistsAt.integrable [Sub G] {x : G} (h : ConvolutionExistsAt f g x L μ) :
    Integrable (fun t => L (f t) (g (x - t))) μ :=
  h

section Group

variable [AddGroup G]

/-
**MeasureTheory.AEStronglyMeasurable.convolution_integrand'** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f : G → E} {g : G → E'}   [inst_3 : NontriviallyNormedField 𝕜]
 [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : NormedSpace 𝕜 
F]   (L : E →L[𝕜] E' →L[𝕜] F) [inst_7 : MeasurableSpace G] {μ ν : MeasureTheory.
Measure G} [inst_8 : AddGroup G]   [MeasurableAdd₂ G] [MeasurableNeg G],   Measu
reTheory.AEStronglyMeasurable f ν →     MeasureTheory.AEStronglyMeasurable g (Me
asureTheory.Measure.map (fun p => p.1 - p.2) (μ.prod ν)) →       MeasureTheory.A
EStronglyMeasurable (fun p => (L (f p.2)) (g (p.1 - p.2))) (μ.prod ν)
参数：L : E →L[𝕜] E' →L[𝕜] F；MeasureTheory.Measure.map (fun p => p.1 - p.2) (μ.prod
 ν)；fun p => (L (f p.2)) (g (p.1 - p.2))；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `ContinuousLinearMap.aestronglyMeasurable_comp₂`：ContinuousLinearMap.aest
ronglyMeasurable_comp₂ (L : E ->L[𝕜] F ->L[𝕜] G) {f : α -> E} {g : α -> F} (hf :
 AEStronglyMeasurable f μ) (hg : AES…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_snd`：MeasureTheory.AEStronglyMea
surable.comp_snd {γ} [TopologicalSpace γ] {f : β -> γ} (hf : AEStronglyMeasurabl
e f ν) : AEStronglyMeasurable (fu…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_measurable`：comp_measurable {γ :
 Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α} {μ : Measur
e γ} (hg : AEStronglyMeasurable g (Measu…
· 使用定理 `MeasurableSub₂.measurable_sub`：∀ {G : Type u_2} {inst : MeasurableSpace 
G} {inst_1 : Sub G} [self : MeasurableSub₂ G], Measurable fun p => p.1 - p.2
· 使用定理 `measurableDiv₂_of_add_neg`：∀ (G : Type u_2) [inst : MeasurableSpace G] [
inst_1 : SubNegMonoid G] [MeasurableAdd₂ G] [MeasurableNeg G],   MeasurableSub₂ 
G
-/
theorem AEStronglyMeasurable.convolution_integrand' [MeasurableAdd₂ G]
    [MeasurableNeg G] (hf : AEStronglyMeasurable f ν)
    (hg : AEStronglyMeasurable g <| map (fun p : G × G => p.1 - p.2) (μ.prod ν)) :
    AEStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
  L.aestronglyMeasurable_comp₂ hf.comp_snd <| hg.comp_measurable measurable_sub

section

variable [MeasurableAdd G] [MeasurableNeg G]

/-
**MeasureTheory.AEStronglyMeasurable.convolution_integrand_snd'** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f : G → E} {g : G → E'}   [inst_3 : NontriviallyNormedField 𝕜]
 [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : NormedSpace 𝕜 
F]   (L : E →L[𝕜] E' →L[𝕜] F) [inst_7 : MeasurableSpace G] {μ : MeasureTheory.Me
asure G} [inst_8 : AddGroup G]   [MeasurableAdd G] [MeasurableNeg G],   MeasureT
heory.AEStronglyMeasurable f μ →     ∀ {x : G},       MeasureTheory.AEStronglyMe
asurable g (MeasureTheory.Measure.map (fun t => x - t) μ) →         MeasureTheor
y.AEStronglyMeasurable (fun t => (L (f t)) (g (x - t))) μ
参数：L : E →L[𝕜] E' →L[𝕜] F；MeasureTheory.Measure.map (fun t => x - t) μ；fun t => 
(L (f t)) (g (x - t))。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `ContinuousLinearMap.aestronglyMeasurable_comp₂`：ContinuousLinearMap.aest
ronglyMeasurable_comp₂ (L : E ->L[𝕜] F ->L[𝕜] G) {f : α -> E} {g : α -> F} (hf :
 AEStronglyMeasurable f μ) (hg : AES…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_measurable`：comp_measurable {γ :
 Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α} {μ : Measur
e γ} (hg : AEStronglyMeasurable g (Measu…
· 使用定理 `Measurable.const_sub`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurable
Space G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   [MeasurableSub G
], Measura…
· 使用定理 `measurableSub_of_add_neg`：∀ (G : Type u_2) [inst : MeasurableSpace G] [i
nst_1 : SubNegMonoid G] [MeasurableAdd G] [MeasurableNeg G],   MeasurableSub G
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
theorem AEStronglyMeasurable.convolution_integrand_snd'
    (hf : AEStronglyMeasurable f μ) {x : G}
    (hg : AEStronglyMeasurable g <| map (fun t => x - t) μ) :
    AEStronglyMeasurable (fun t => L (f t) (g (x - t))) μ :=
  L.aestronglyMeasurable_comp₂ hf <| hg.comp_measurable <| measurable_id.const_sub x
/-
**MeasureTheory.AEStronglyMeasurable.convolution_integrand_swap_snd'** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f : G → E} {g : G → E'}   [inst_3 : NontriviallyNormedField 𝕜]
 [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : NormedSpace 𝕜 
F]   (L : E →L[𝕜] E' →L[𝕜] F) [inst_7 : MeasurableSpace G] {μ : MeasureTheory.Me
asure G} [inst_8 : AddGroup G]   [MeasurableAdd G] [MeasurableNeg G] {x : G},   
MeasureTheory.AEStronglyMeasurable f (MeasureTheory.Measure.map (fun t => x - t)
 μ) →     MeasureTheory.AEStronglyMeasurable g μ → MeasureTheory.AEStronglyMeasu
rable (fun t => (L (f (x - t))) (g t)) μ
参数：L : E →L[𝕜] E' →L[𝕜] F；MeasureTheory.Measure.map (fun t => x - t) μ；fun t => 
(L (f (x - t))) (g t)。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `ContinuousLinearMap.aestronglyMeasurable_comp₂`：ContinuousLinearMap.aest
ronglyMeasurable_comp₂ (L : E ->L[𝕜] F ->L[𝕜] G) {f : α -> E} {g : α -> F} (hf :
 AEStronglyMeasurable f μ) (hg : AES…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_measurable`：comp_measurable {γ :
 Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α} {μ : Measur
e γ} (hg : AEStronglyMeasurable g (Measu…
· 使用定理 `Measurable.const_sub`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurable
Space G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   [MeasurableSub G
], Measura…
· 使用定理 `measurableSub_of_add_neg`：∀ (G : Type u_2) [inst : MeasurableSpace G] [i
nst_1 : SubNegMonoid G] [MeasurableAdd G] [MeasurableNeg G],   MeasurableSub G
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
theorem AEStronglyMeasurable.convolution_integrand_swap_snd' {x : G}
    (hf : AEStronglyMeasurable f <| map (fun t => x - t) μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun t => L (f (x - t)) (g t)) μ :=
  L.aestronglyMeasurable_comp₂ (hf.comp_measurable <| measurable_id.const_sub x) hg

/-- A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that `f` is integrable on a set `s` and `g` is bounded and ae strongly measurable
on `x₀ - s` (note that both properties hold if `g` is continuous with compact support). -/
/-
**MeasureTheory._root_.BddAbove.convolutionExistsAt'** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that `f` is integrable on a set `s` and `g` is bounded and ae strongly
 measurable
on `x₀ - s` (note that both properties hold if `g` is continuous with compact su
pport).
-/
theorem _root_.BddAbove.convolutionExistsAt' {x₀ : G} {s : Set G}
    (hbg : BddAbove ((fun i => ‖g i‖) '' ((fun t => -t + x₀) ⁻¹' s))) (hs : MeasurableSet s)
    (h2s : (support fun t => L (f t) (g (x₀ - t))) ⊆ s) (hf : IntegrableOn f s μ)
    (hmg : AEStronglyMeasurable g <| map (fun t => x₀ - t) (μ.restrict s)) :
    ConvolutionExistsAt f g x₀ L μ := by
  rw [ConvolutionExistsAt]
  rw [← integrableOn_iff_integrable_of_support_subset h2s]
  set s' := (fun t => -t + x₀) ⁻¹' s
  have : ∀ᵐ t : G ∂μ.restrict s,
      ‖L (f t) (g (x₀ - t))‖ ≤ s.indicator (fun t => ‖L‖ * ‖f t‖ * ⨆ i : s', ‖g i‖) t := by
    filter_upwards
    refine le_indicator (fun t ht => ?_) fun t ht => ?_
    · apply_rules [L.le_of_opNorm₂_le_of_le, le_rfl]
      refine (le_ciSup_set hbg <| mem_preimage.mpr ?_)
      rwa [neg_sub, sub_add_cancel]
    · have : t ∉ support fun t => L (f t) (g (x₀ - t)) := mt (fun h => h2s h) ht
      rw [notMem_support.mp this, norm_zero]
  refine Integrable.mono' ?_ ?_ this
  · rw [integrable_indicator_iff hs]; exact ((hf.norm.const_mul _).mul_const _).integrableOn
  · exact hf.aestronglyMeasurable.convolution_integrand_snd' L hmg

/-- If `‖f‖ *[μ] ‖g‖` exists, then `f *[L, μ] g` exists. -/
/-
**MeasureTheory.ConvolutionExistsAt.of_norm'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.ConvolutionExistsAt`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f : G → E} {g : G → E'}   [inst_3 : NontriviallyNormedField 𝕜]
 [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : NormedSpace 𝕜 
F]   (L : E →L[𝕜] E' →L[𝕜] F) [inst_7 : MeasurableSpace G] {μ : MeasureTheory.Me
asure G} [inst_8 : AddGroup G]   [MeasurableAdd G] [MeasurableNeg G] {x₀ : G},  
 MeasureTheory.ConvolutionExistsAt (fun x => ‖f x‖) (fun x => ‖g x‖) x₀ (Continu
ousLinearMap.mul ℝ ℝ) μ →     MeasureTheory.AEStronglyMeasurable f μ →       Mea
sureTheory.AEStronglyMeasurable g (MeasureTheory.Measure.map (fun t => x₀ - t) μ
) →         MeasureTheory.ConvolutionExistsAt f g x₀ L μ
参数：L : E →L[𝕜] E' →L[𝕜] F；fun x => ‖f x‖；fun x => ‖g x‖；ContinuousLinearMap.mul 
ℝ ℝ；MeasureTheory.Measure.map (fun t => x₀ - t) μ。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.convolution_integrand_snd'`：∀ {𝕜 : Ty
pe u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedA
ddCommGroup E]   [inst_1 : NormedAddCommGroup E'] […
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousLinearMap.mul_apply'`：mul_apply' (x y : R) : mul 𝕜 R x y = x *
 y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ContinuousLinearMap.le_opNorm₂`：le_opNorm₂ [RingHomIsometric σ₁₃] (f : E
 ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F) : ‖f x y‖ <= ‖f‖ * ‖x‖ * ‖y‖

--- 原说明 ---
If `‖f‖ *[μ] ‖g‖` exists, then `f *[L, μ] g` exists.
-/
theorem ConvolutionExistsAt.of_norm' {x₀ : G}
    (h : ConvolutionExistsAt (fun x => ‖f x‖) (fun x => ‖g x‖) x₀ (mul ℝ ℝ) μ)
    (hmf : AEStronglyMeasurable f μ) (hmg : AEStronglyMeasurable g <| map (fun t => x₀ - t) μ) :
    ConvolutionExistsAt f g x₀ L μ := by
  refine (h.const_mul ‖L‖).mono'
    (hmf.convolution_integrand_snd' L hmg) (Eventually.of_forall fun x => ?_)
  rw [mul_apply', ← mul_assoc]
  apply L.le_opNorm₂

end

section Left

variable [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ] [IsAddRightInvariant μ]

/-
**MeasureTheory.AEStronglyMeasurable.convolution_integrand_snd** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f : G → E} {g : G → E'}   [inst_3 : NontriviallyNormedField 𝕜]
 [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : NormedSpace 𝕜 
F]   (L : E →L[𝕜] E' →L[𝕜] F) [inst_7 : MeasurableSpace G] {μ : MeasureTheory.Me
asure G} [inst_8 : AddGroup G]   [MeasurableAdd₂ G] [MeasurableNeg G] [MeasureTh
eory.SFinite μ] [μ.IsAddRightInvariant],   MeasureTheory.AEStronglyMeasurable f 
μ →     MeasureTheory.AEStronglyMeasurable g μ →       ∀ (x : G), MeasureTheory.
AEStronglyMeasurable (fun t => (L (f t)) (g (x - t))) μ
参数：L : E →L[𝕜] E' →L[𝕜] F；x : G；fun t => (L (f t)) (g (x - t))。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MeasureTheory.AEStronglyMeasurable.convolution_integrand_snd'`：∀ {𝕜 : Ty
pe u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedA
ddCommGroup E]   [inst_1 : NormedAddCommGroup E'] […
· 使用定理 `MeasurableAdd₂.toMeasurableAdd`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Add M] [MeasurableAdd₂ M], MeasurableAdd M
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_ac`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ ν : MeasureTheory.
Measure α}   {f : α → β},   ν.Ab…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
· 使用定理 `MeasureTheory.quasiMeasurePreserving_sub_left_of_right_invariant`：∀ {G :
 Type u_1} [inst : MeasurableSpace G] [inst_1 : AddGroup G] [MeasurableAdd₂ G] (
μ : MeasureTheory.Measure G)   [MeasureTheory.SFinite …
-/
theorem AEStronglyMeasurable.convolution_integrand_snd (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (x : G) :
    AEStronglyMeasurable (fun t => L (f t) (g (x - t))) μ :=
  hf.convolution_integrand_snd' L <|
    hg.mono_ac <| (quasiMeasurePreserving_sub_left_of_right_invariant μ x).absolutelyContinuous
/-
**MeasureTheory.AEStronglyMeasurable.convolution_integrand_swap_snd** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f : G → E} {g : G → E'}   [inst_3 : NontriviallyNormedField 𝕜]
 [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : NormedSpace 𝕜 
F]   (L : E →L[𝕜] E' →L[𝕜] F) [inst_7 : MeasurableSpace G] {μ : MeasureTheory.Me
asure G} [inst_8 : AddGroup G]   [MeasurableAdd₂ G] [MeasurableNeg G] [MeasureTh
eory.SFinite μ] [μ.IsAddRightInvariant],   MeasureTheory.AEStronglyMeasurable f 
μ →     MeasureTheory.AEStronglyMeasurable g μ →       ∀ (x : G), MeasureTheory.
AEStronglyMeasurable (fun t => (L (f (x - t))) (g t)) μ
参数：L : E →L[𝕜] E' →L[𝕜] F；x : G；fun t => (L (f (x - t))) (g t)。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MeasureTheory.AEStronglyMeasurable.convolution_integrand_swap_snd'`：∀ {𝕜
 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : No
rmedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] […
· 使用定理 `MeasurableAdd₂.toMeasurableAdd`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Add M] [MeasurableAdd₂ M], MeasurableAdd M
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_ac`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ ν : MeasureTheory.
Measure α}   {f : α → β},   ν.Ab…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
· 使用定理 `MeasureTheory.quasiMeasurePreserving_sub_left_of_right_invariant`：∀ {G :
 Type u_1} [inst : MeasurableSpace G] [inst_1 : AddGroup G] [MeasurableAdd₂ G] (
μ : MeasureTheory.Measure G)   [MeasureTheory.SFinite …
-/
theorem AEStronglyMeasurable.convolution_integrand_swap_snd
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (x : G) :
    AEStronglyMeasurable (fun t => L (f (x - t)) (g t)) μ :=
  (hf.mono_ac
        (quasiMeasurePreserving_sub_left_of_right_invariant μ
            x).absolutelyContinuous).convolution_integrand_swap_snd'
    L hg

/-- If `‖f‖ *[μ] ‖g‖` exists, then `f *[L, μ] g` exists. -/
/-
**MeasureTheory.ConvolutionExistsAt.of_norm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.ConvolutionExistsAt`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f : G → E} {g : G → E'}   [inst_3 : NontriviallyNormedField 𝕜]
 [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : NormedSpace 𝕜 
F]   (L : E →L[𝕜] E' →L[𝕜] F) [inst_7 : MeasurableSpace G] {μ : MeasureTheory.Me
asure G} [inst_8 : AddGroup G]   [MeasurableAdd₂ G] [MeasurableNeg G] [MeasureTh
eory.SFinite μ] [μ.IsAddRightInvariant] {x₀ : G},   MeasureTheory.ConvolutionExi
stsAt (fun x => ‖f x‖) (fun x => ‖g x‖) x₀ (ContinuousLinearMap.mul ℝ ℝ) μ →    
 MeasureTheory.AEStronglyMeasurable f μ →       MeasureTheory.AEStronglyMeasurab
le g μ → MeasureTheory.ConvolutionExistsAt f g x₀ L μ
参数：L : E →L[𝕜] E' →L[𝕜] F；fun x => ‖f x‖；fun x => ‖g x‖；ContinuousLinearMap.mul 
ℝ ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MeasureTheory.ConvolutionExistsAt.of_norm'`：∀ {𝕜 : Type u𝕜} {G : Type uG
} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E]   [i
nst_1 : NormedAddCommGroup E'] […
· 使用定理 `MeasurableAdd₂.toMeasurableAdd`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Add M] [MeasurableAdd₂ M], MeasurableAdd M
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_ac`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ ν : MeasureTheory.
Measure α}   {f : α → β},   ν.Ab…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
· 使用定理 `MeasureTheory.quasiMeasurePreserving_sub_left_of_right_invariant`：∀ {G :
 Type u_1} [inst : MeasurableSpace G] [inst_1 : AddGroup G] [MeasurableAdd₂ G] (
μ : MeasureTheory.Measure G)   [MeasureTheory.SFinite …

--- 原说明 ---
If `‖f‖ *[μ] ‖g‖` exists, then `f *[L, μ] g` exists.
-/
theorem ConvolutionExistsAt.of_norm {x₀ : G}
    (h : ConvolutionExistsAt (fun x => ‖f x‖) (fun x => ‖g x‖) x₀ (mul ℝ ℝ) μ)
    (hmf : AEStronglyMeasurable f μ) (hmg : AEStronglyMeasurable g μ) :
    ConvolutionExistsAt f g x₀ L μ :=
  h.of_norm' L hmf <|
    hmg.mono_ac (quasiMeasurePreserving_sub_left_of_right_invariant μ x₀).absolutelyContinuous

end Left

section Right

variable [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ] [IsAddRightInvariant μ] [SFinite ν]

/-
**MeasureTheory.AEStronglyMeasurable.convolution_integrand** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.AEStronglyMeasurable`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f : G → E} {g : G → E'}   [inst_3 : NontriviallyNormedField 𝕜]
 [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : NormedSpace 𝕜 
F]   (L : E →L[𝕜] E' →L[𝕜] F) [inst_7 : MeasurableSpace G] {μ ν : MeasureTheory.
Measure G} [inst_8 : AddGroup G]   [MeasurableAdd₂ G] [MeasurableNeg G] [Measure
Theory.SFinite μ] [μ.IsAddRightInvariant] [MeasureTheory.SFinite ν],   MeasureTh
eory.AEStronglyMeasurable f ν →     MeasureTheory.AEStronglyMeasurable g μ →    
   MeasureTheory.AEStronglyMeasurable (fun p => (L (f p.2)) (g (p.1 - p.2))) (μ.
prod ν)
参数：L : E →L[𝕜] E' →L[𝕜] F；fun p => (L (f p.2)) (g (p.1 - p.2))；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MeasureTheory.AEStronglyMeasurable.convolution_integrand'`：∀ {𝕜 : Type u
𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCo
mmGroup E]   [inst_1 : NormedAddCommGroup E'] […
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_ac`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ ν : MeasureTheory.
Measure α}   {f : α → β},   ν.Ab…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
· 使用定理 `MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant`：∀ {G : Type
 u_1} [inst : MeasurableSpace G] [inst_1 : AddGroup G] [MeasurableAdd₂ G] (μ ν :
 MeasureTheory.Measure G)   [MeasureTheory.SFinit…
-/
theorem AEStronglyMeasurable.convolution_integrand (hf : AEStronglyMeasurable f ν)
    (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
  hf.convolution_integrand' L <|
    hg.mono_ac (quasiMeasurePreserving_sub_of_right_invariant μ ν).absolutelyContinuous
/-
**MeasureTheory.Integrable.convolution_integrand** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Integrable`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f : G → E} {g : G → E'}   [inst_3 : NontriviallyNormedField 𝕜]
 [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : NormedSpace 𝕜 
F]   (L : E →L[𝕜] E' →L[𝕜] F) [inst_7 : MeasurableSpace G] {μ ν : MeasureTheory.
Measure G} [inst_8 : AddGroup G]   [MeasurableAdd₂ G] [MeasurableNeg G] [Measure
Theory.SFinite μ] [μ.IsAddRightInvariant] [MeasureTheory.SFinite ν],   MeasureTh
eory.Integrable f ν →     MeasureTheory.Integrable g μ → MeasureTheory.Integrabl
e (fun p => (L (f p.2)) (g (p.1 - p.2))) (μ.prod ν)
参数：L : E →L[𝕜] E' →L[𝕜] F；fun p => (L (f p.2)) (g (p.1 - p.2))；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MeasureTheory.AEStronglyMeasurable.convolution_integrand`：∀ {𝕜 : Type u𝕜
} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCom
mGroup E]   [inst_1 : NormedAddCommGroup E'] […
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`：MeasureTheory.A
EStronglyMeasurable.integral_prod_right' [SFinite ν] [NormedSpace Real E] ⦃f : α
 × β -> E⦄ (hf : AEStronglyMeasurable f (μ.pr…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prod_swap`：∀ {α : Type u_1} {β : Type
 u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory
.Measure α}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integrable_prod_iff'`：integrable_prod_iff' [SFinite μ] ⦃f 
: α × β -> E⦄ (h1f : AEStronglyMeasurable f (μ.prod ν)) : Integrable f (μ.prod ν
) ↔ (forallᵐ y ∂ν, Integ…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
· 使用定理 `MeasureTheory.Integrable.comp_sub_right`：∀ {G : Type u_4} {F : Type u_6}
 [inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory.M
easure G}   [inst_2 : AddGrou…
· 使用定理 `MeasurableAdd₂.toMeasurableAdd`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Add M] [MeasurableAdd₂ M], MeasurableAdd M
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_sub_right_eq_self`：∀ {G : Type u_4} {E : Type u_5
} [inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpa
ce ℝ E]   {μ : MeasureTheory.M…
· 使用定理 `MeasureTheory.Integrable.mul_const`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
（共 33 条，此处仅展示前 30 条）
-/
theorem Integrable.convolution_integrand (hf : Integrable f ν) (hg : Integrable g μ) :
    Integrable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) := by
  have h_meas : AEStronglyMeasurable (fun p : G × G => L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
    hf.aestronglyMeasurable.convolution_integrand L hg.aestronglyMeasurable
  have h2_meas : AEStronglyMeasurable (fun y : G => ∫ x : G, ‖L (f y) (g (x - y))‖ ∂μ) ν :=
    h_meas.prod_swap.norm.integral_prod_right'
  simp_rw [integrable_prod_iff' h_meas]
  refine ⟨Eventually.of_forall fun t => (L (f t)).integrable_comp (hg.comp_sub_right t), ?_⟩
  refine Integrable.mono' ?_ h2_meas
      (Eventually.of_forall fun t => (?_ : _ ≤ ‖L‖ * ‖f t‖ * ∫ x, ‖g (x - t)‖ ∂μ))
  · simp only [integral_sub_right_eq_self (‖g ·‖)]
    fun_prop
  · simp_rw [← integral_const_mul]
    rw [Real.norm_of_nonneg (by positivity)]
    exact integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
      ((hg.comp_sub_right t).norm.const_mul _) (Eventually.of_forall fun t => L.le_opNorm₂ _ _)
/-
**MeasureTheory.Integrable.ae_convolution_exists** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Integrable`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f : G → E} {g : G → E'}   [inst_3 : NontriviallyNormedField 𝕜]
 [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : NormedSpace 𝕜 
F]   (L : E →L[𝕜] E' →L[𝕜] F) [inst_7 : MeasurableSpace G] {μ ν : MeasureTheory.
Measure G} [inst_8 : AddGroup G]   [MeasurableAdd₂ G] [MeasurableNeg G] [Measure
Theory.SFinite μ] [μ.IsAddRightInvariant] [MeasureTheory.SFinite ν],   MeasureTh
eory.Integrable f ν →     MeasureTheory.Integrable g μ → ∀ᵐ (x : G) ∂μ, MeasureT
heory.ConvolutionExistsAt f g x L ν
参数：L : E →L[𝕜] E' →L[𝕜] F；x : G。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_prod_iff`：integrable_prod_iff ⦃f : α × β -> E⦄ 
(h1f : AEStronglyMeasurable f (μ.prod ν)) : Integrable f (μ.prod ν) ↔ (forallᵐ x
 ∂μ, Integrable (fun y …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.convolution_integrand`：∀ {𝕜 : Type u𝕜
} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCom
mGroup E]   [inst_1 : NormedAddCommGroup E'] […
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.Integrable.convolution_integrand`：∀ {𝕜 : Type u𝕜} {G : Typ
e uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E] 
  [inst_1 : NormedAddCommGroup E'] […
-/
theorem Integrable.ae_convolution_exists (hf : Integrable f ν) (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, ConvolutionExistsAt f g x L ν :=
  ((integrable_prod_iff <|
          hf.aestronglyMeasurable.convolution_integrand L hg.aestronglyMeasurable).mp <|
      hf.convolution_integrand L hg).1

end Right

variable [TopologicalSpace G] [IsTopologicalAddGroup G] [BorelSpace G]

/-
**MeasureTheory._root_.HasCompactSupport.convolutionExistsAt** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.HasCompactSupport.convolutionExistsAt {x₀ : G}
    (h : HasCompactSupport fun t => L (f t) (g (x₀ - t))) (hf : LocallyIntegrable f μ)
    (hg : Continuous g) : ConvolutionExistsAt f g x₀ L μ := by
  let u := (Homeomorph.neg G).trans (Homeomorph.addRight x₀)
  let v := (Homeomorph.neg G).trans (Homeomorph.addLeft x₀)
  apply ((u.isCompact_preimage.mpr h).bddAbove_image hg.norm.continuousOn).convolutionExistsAt' L
    isClosed_closure.measurableSet subset_closure (hf.integrableOn_isCompact h)
  have A : AEStronglyMeasurable (g ∘ v)
      (μ.restrict (tsupport fun t : G => L (f t) (g (x₀ - t)))) := by
    apply (hg.comp v.continuous).continuousOn.aestronglyMeasurable_of_isCompact h
    exact (isClosed_tsupport _).measurableSet
  convert!
    ((v.continuous.measurable.measurePreserving
              (μ.restrict (tsupport fun t => L (f t) (g (x₀ - t))))).aestronglyMeasurable_comp_iff
          v.measurableEmbedding).1
      A
  ext x
  simp only [v, Homeomorph.neg, sub_eq_add_neg, val_toAddUnits_apply, Homeomorph.trans_apply,
    Equiv.neg_apply, Homeomorph.homeomorph_mk_coe, Homeomorph.coe_addLeft]
/-
**MeasureTheory._root_.HasCompactSupport.convolutionExists_right** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.HasCompactSupport.convolutionExists_right (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : ConvolutionExists f g L μ := by
  intro x₀
  refine HasCompactSupport.convolutionExistsAt L ?_ hf hg
  refine (hcg.comp_homeomorph (Homeomorph.subLeft x₀)).mono ?_
  refine fun t => mt fun ht : g (x₀ - t) = 0 => ?_
  simp_rw [ht, (L _).map_zero]
/-
**MeasureTheory._root_.HasCompactSupport.convolutionExists_left_of_continuous_ri
ght** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.HasCompactSupport.convolutionExists_left_of_continuous_right
    (hcf : HasCompactSupport f) (hf : LocallyIntegrable f μ) (hg : Continuous g) :
    ConvolutionExists f g L μ := by
  intro x₀
  refine HasCompactSupport.convolutionExistsAt L ?_ hf hg
  refine hcf.mono ?_
  refine fun t => mt fun ht : f t = 0 => ?_
  simp_rw [ht, L.map_zero₂]

end Group

section CommGroup

variable [AddCommGroup G]

section MeasurableGroup

variable [MeasurableNeg G] [IsAddLeftInvariant μ]

/-- A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that the integrand has compact support and `g` is bounded on this support (note that
both properties hold if `g` is continuous with compact support). We also require that `f` is
integrable on the support of the integrand, and that both functions are strongly measurable.

This is a variant of `BddAbove.convolutionExistsAt'` in an abelian group with a left-invariant
measure. This allows us to state the boundedness and measurability of `g` in a more natural way. -/
/-
**MeasureTheory._root_.BddAbove.convolutionExistsAt** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that the integrand has compact support and `g` is bounded on this supp
ort (note that
both properties hold if `g` is continuous with compact support). We also require
 that `f` is
integrable on the support of the integrand, and that both functions are strongly
 measurable.

This is a variant of `BddAbove.convolutionExistsAt'` in an abelian group with a 
left-invariant
measure. This allows us to state the boundedness and measurability of `g` in a m
ore natural way.
-/
theorem _root_.BddAbove.convolutionExistsAt [MeasurableAdd₂ G] [SFinite μ] {x₀ : G} {s : Set G}
    (hbg : BddAbove ((fun i => ‖g i‖) '' ((fun t => x₀ - t) ⁻¹' s))) (hs : MeasurableSet s)
    (h2s : (support fun t => L (f t) (g (x₀ - t))) ⊆ s) (hf : IntegrableOn f s μ)
    (hmg : AEStronglyMeasurable g μ) : ConvolutionExistsAt f g x₀ L μ := by
  refine BddAbove.convolutionExistsAt' L ?_ hs h2s hf ?_
  · simp_rw [← sub_eq_neg_add, hbg]
  · have : AEStronglyMeasurable g (map (fun t : G => x₀ - t) μ) :=
      hmg.mono_ac (quasiMeasurePreserving_sub_left_of_right_invariant μ x₀).absolutelyContinuous
    apply this.mono_measure
    exact map_mono restrict_le_self (measurable_const.sub measurable_id')

variable {L} [MeasurableAdd G] [IsNegInvariant μ]
/-
**MeasureTheory.convolutionExistsAt_flip** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：convolutionExistsAt_flip : ConvolutionExistsAt g f x L.flip μ ↔ Convolutio
nExistsAt f g x L μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrable_comp_sub_left`：∀ {G : Type u_4} {F : Type u_6} 
[inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory.Me
asure G}   [inst_2 : AddGrou…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem convolutionExistsAt_flip :
    ConvolutionExistsAt g f x L.flip μ ↔ ConvolutionExistsAt f g x L μ := by
  simp_rw [ConvolutionExistsAt, ← integrable_comp_sub_left (fun t => L (f t) (g (x - t))) x,
    sub_sub_cancel, flip_apply]
/-
**MeasureTheory.ConvolutionExistsAt.integrable_swap** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.ConvolutionExistsAt`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f : G → E} {g : G → E'} {x : G}   [inst_3 : NontriviallyNormed
Field 𝕜] [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : Normed
Space 𝕜 F]   {L : E →L[𝕜] E' →L[𝕜] F} [inst_7 : MeasurableSpace G] {μ : MeasureT
heory.Measure G} [inst_8 : AddCommGroup G]   [MeasurableNeg G] [μ.IsAddLeftInvar
iant] [MeasurableAdd G] [μ.IsNegInvariant],   MeasureTheory.ConvolutionExistsAt 
f g x L μ → MeasureTheory.Integrable (fun t => (L (f (x - t))) (g t)) μ
参数：fun t => (L (f (x - t))) (g t)。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_self`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - (a
 - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Integrable.comp_sub_left`：∀ {G : Type u_4} {F : Type u_6} 
[inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory.Me
asure G}   [inst_2 : AddGrou…
-/
theorem ConvolutionExistsAt.integrable_swap (h : ConvolutionExistsAt f g x L μ) :
    Integrable (fun t => L (f (x - t)) (g t)) μ := by
  convert! h.comp_sub_left x
  simp_rw [sub_sub_self]
/-
**MeasureTheory.convolutionExistsAt_iff_integrable_swap** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：convolutionExistsAt_iff_integrable_swap : ConvolutionExistsAt f g x L μ ↔ 
Integrable (fun t => L (f (x - t)) (g t)) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasureTheory.convolutionExistsAt_flip`：convolutionExistsAt_flip : Convo
lutionExistsAt g f x L.flip μ ↔ ConvolutionExistsAt f g x L μ
-/
theorem convolutionExistsAt_iff_integrable_swap :
    ConvolutionExistsAt f g x L μ ↔ Integrable (fun t => L (f (x - t)) (g t)) μ :=
  convolutionExistsAt_flip.symm

end MeasurableGroup

variable [TopologicalSpace G] [IsTopologicalAddGroup G] [BorelSpace G]
variable [IsAddLeftInvariant μ] [IsNegInvariant μ]

/-
**MeasureTheory._root_.HasCompactSupport.convolutionExists_left** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.HasCompactSupport.convolutionExists_left
    (hcf : HasCompactSupport f) (hf : Continuous f)
    (hg : LocallyIntegrable g μ) : ConvolutionExists f g L μ := fun x₀ =>
  convolutionExistsAt_flip.mp <| hcf.convolutionExists_right L.flip hg hf x₀
/-
**MeasureTheory._root_.HasCompactSupport.convolutionExists_right_of_continuous_l
eft** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.HasCompactSupport.convolutionExists_right_of_continuous_left
    (hcg : HasCompactSupport g) (hf : Continuous f) (hg : LocallyIntegrable g μ) :
    ConvolutionExists f g L μ := fun x₀ =>
  convolutionExistsAt_flip.mp <| hcg.convolutionExists_left_of_continuous_right L.flip hg hf x₀

end CommGroup

end ConvolutionExists

variable [NormedSpace ℝ F]

/-- The convolution of two functions `f` and `g` with respect to a continuous bilinear map `L` and
measure `μ`. It is defined to be `(f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ`. -/
/-
**MeasureTheory.convolution** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：convolution [Sub G] (f : G -> E) (g : G -> E') (L : E ->L[𝕜] E' ->L[𝕜] F) 
(μ : Measure G
参数：f : G -> E；g : G -> E'；L : E ->L[𝕜] E' ->L[𝕜] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The convolution of two functions `f` and `g` with respect to a continuous biline
ar map `L` and
measure `μ`. It is defined to be `(f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ`
.
-/
noncomputable def convolution [Sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
    (μ : Measure G := by volume_tac) : G → F := fun x =>
  ∫ t, L (f t) (g (x - t)) ∂μ

/-- The convolution of two functions with respect to a bilinear operation `L` and a measure `μ`. -/
scoped[Convolution] notation:67 f " ⋆[" L:67 ", " μ:67 "] " g:66 => convolution f g L μ

/-- The convolution of two functions with respect to a bilinear operation `L` and the volume. -/
scoped[Convolution]
  notation:67 f " ⋆[" L:67 "] " g:66 => convolution f g L MeasureSpace.volume

/-- The convolution of two real-valued functions with respect to volume. -/
scoped[Convolution]
  notation:67 f " ⋆ " g:66 =>
    convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureSpace.volume

open scoped Convolution

/-
**MeasureTheory.convolution_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：convolution_def [Sub G] : (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem convolution_def [Sub G] : (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ :=
  rfl

/-- The definition of convolution where the bilinear operator is scalar multiplication.
Note: it often helps the elaborator to give the type of the convolution explicitly. -/
/-
**MeasureTheory.convolution_lsmul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：convolution_lsmul [Sub G] {f : G -> 𝕜} {g : G -> F} : (f ⋆[lsmul 𝕜 𝕜, μ] g
 : G -> F) x = ∫ t, f t • g (x - t) ∂μ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The definition of convolution where the bilinear operator is scalar multiplicati
on.
Note: it often helps the elaborator to give the type of the convolution explicit
ly.
-/
theorem convolution_lsmul [Sub G] {f : G → 𝕜} {g : G → F} :
    (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f t • g (x - t) ∂μ :=
  rfl

/-- The definition of convolution where the bilinear operator is multiplication. -/
/-
**MeasureTheory.convolution_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：convolution_mul [Sub G] [NormedSpace Real 𝕜] {f : G -> 𝕜} {g : G -> 𝕜} : (
f ⋆[mul 𝕜 𝕜, μ] g) x = ∫ t, f t * g (x - t) ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
The definition of convolution where the bilinear operator is multiplication.
-/
theorem convolution_mul [Sub G] [NormedSpace ℝ 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
    (f ⋆[mul 𝕜 𝕜, μ] g) x = ∫ t, f t * g (x - t) ∂μ :=
  rfl

section Group

variable {L} [AddGroup G]

/-
**MeasureTheory.smul_convolution** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：smul_convolution [SMulCommClass Real 𝕜 F] {y : 𝕜} : y • f ⋆[L, μ] g = y • 
(f ⋆[L, μ] g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.map_smul₂`：map_smul₂ (f : E ->L[𝕜₃] F ->SL[σ₂₃] G) (
c : 𝕜₃) (x : E) (y : F) : f (c • x) y = c • f x y
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_convolution [SMulCommClass ℝ 𝕜 F] {y : 𝕜} : y • f ⋆[L, μ] g = y • (f ⋆[L, μ] g) := by
  ext; simp only [Pi.smul_apply, convolution_def, ← integral_smul, L.map_smul₂]
/-
**MeasureTheory.convolution_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：convolution_smul [SMulCommClass Real 𝕜 F] {y : 𝕜} : f ⋆[L, μ] y • g = y • 
(f ⋆[L, μ] g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.map_smul`：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁
 : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁]   {M₂ : 
Type u_6} [inst_3 …
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convolution_smul [SMulCommClass ℝ 𝕜 F] {y : 𝕜} : f ⋆[L, μ] y • g = y • (f ⋆[L, μ] g) := by
  ext; simp only [Pi.smul_apply, convolution_def, ← integral_smul, (L _).map_smul]

@[simp]
/-
**MeasureTheory.zero_convolution** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：zero_convolution : 0 ⋆[L, μ] g = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.map_zero₂`：map_zero₂ (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
 (y : F) : f 0 y = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_convolution : 0 ⋆[L, μ] g = 0 := by
  ext
  simp_rw [convolution_def, Pi.zero_apply, L.map_zero₂, integral_zero]

@[simp]
/-
**MeasureTheory.convolution_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：convolution_zero : f ⋆[L, μ] 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.map_zero`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : 
Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 
: TopologicalSpace…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convolution_zero : f ⋆[L, μ] 0 = 0 := by
  ext
  simp_rw [convolution_def, Pi.zero_apply, (L _).map_zero, integral_zero]
/-
**MeasureTheory.ConvolutionExistsAt.distrib_add** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.ConvolutionExistsAt`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f : G → E} {g g' : G → E'}   [inst_3 : NontriviallyNormedField
 𝕜] [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : NormedSpace
 𝕜 F]   {L : E →L[𝕜] E' →L[𝕜] F} [inst_7 : MeasurableSpace G] {μ : MeasureTheory
.Measure G} [inst_8 : NormedSpace ℝ F]   [inst_9 : AddGroup G] {x : G},   Measur
eTheory.ConvolutionExistsAt f g x L μ →     MeasureTheory.ConvolutionExistsAt f 
g' x L μ →       MeasureTheory.convolution f (g + g') L μ x =         MeasureThe
ory.convolution f g L μ x + MeasureTheory.convolution f g' L μ x
参数：g + g'。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.map_add`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ConvolutionExistsAt.distrib_add {x : G} (hfg : ConvolutionExistsAt f g x L μ)
    (hfg' : ConvolutionExistsAt f g' x L μ) :
    (f ⋆[L, μ] (g + g')) x = (f ⋆[L, μ] g) x + (f ⋆[L, μ] g') x := by
  simp only [convolution_def, (L _).map_add, Pi.add_apply, integral_add hfg hfg']
/-
**MeasureTheory.ConvolutionExists.distrib_add** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.ConvolutionExists`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f : G → E} {g g' : G → E'}   [inst_3 : NontriviallyNormedField
 𝕜] [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : NormedSpace
 𝕜 F]   {L : E →L[𝕜] E' →L[𝕜] F} [inst_7 : MeasurableSpace G] {μ : MeasureTheory
.Measure G} [inst_8 : NormedSpace ℝ F]   [inst_9 : AddGroup G],   MeasureTheory.
ConvolutionExists f g L μ →     MeasureTheory.ConvolutionExists f g' L μ →      
 MeasureTheory.convolution f (g + g') L μ = MeasureTheory.convolution f g L μ + 
MeasureTheory.convolution f g' L μ
参数：g + g'。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.ConvolutionExistsAt.distrib_add`：∀ {𝕜 : Type u𝕜} {G : Type
 uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E]  
 [inst_1 : NormedAddCommGroup E'] […
-/
theorem ConvolutionExists.distrib_add (hfg : ConvolutionExists f g L μ)
    (hfg' : ConvolutionExists f g' L μ) : f ⋆[L, μ] (g + g') = f ⋆[L, μ] g + f ⋆[L, μ] g' := by
  ext x
  exact (hfg x).distrib_add (hfg' x)
/-
**MeasureTheory.ConvolutionExistsAt.add_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.ConvolutionExistsAt`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f f' : G → E} {g : G → E'}   [inst_3 : NontriviallyNormedField
 𝕜] [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : NormedSpace
 𝕜 F]   {L : E →L[𝕜] E' →L[𝕜] F} [inst_7 : MeasurableSpace G] {μ : MeasureTheory
.Measure G} [inst_8 : NormedSpace ℝ F]   [inst_9 : AddGroup G] {x : G},   Measur
eTheory.ConvolutionExistsAt f g x L μ →     MeasureTheory.ConvolutionExistsAt f'
 g x L μ →       MeasureTheory.convolution (f + f') g L μ x =         MeasureThe
ory.convolution f g L μ x + MeasureTheory.convolution f' g L μ x
参数：f + f'。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.map_add₂`：map_add₂ (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (
x x' : E) (y : F) : f (x + x') y = f x y + f x' y
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ConvolutionExistsAt.add_distrib {x : G} (hfg : ConvolutionExistsAt f g x L μ)
    (hfg' : ConvolutionExistsAt f' g x L μ) :
    ((f + f') ⋆[L, μ] g) x = (f ⋆[L, μ] g) x + (f' ⋆[L, μ] g) x := by
  simp only [convolution_def, L.map_add₂, Pi.add_apply, integral_add hfg hfg']
/-
**MeasureTheory.ConvolutionExists.add_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.ConvolutionExists`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f f' : G → E} {g : G → E'}   [inst_3 : NontriviallyNormedField
 𝕜] [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : NormedSpace
 𝕜 F]   {L : E →L[𝕜] E' →L[𝕜] F} [inst_7 : MeasurableSpace G] {μ : MeasureTheory
.Measure G} [inst_8 : NormedSpace ℝ F]   [inst_9 : AddGroup G],   MeasureTheory.
ConvolutionExists f g L μ →     MeasureTheory.ConvolutionExists f' g L μ →      
 MeasureTheory.convolution (f + f') g L μ = MeasureTheory.convolution f g L μ + 
MeasureTheory.convolution f' g L μ
参数：f + f'。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.ConvolutionExistsAt.add_distrib`：∀ {𝕜 : Type u𝕜} {G : Type
 uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E]  
 [inst_1 : NormedAddCommGroup E'] […
-/
theorem ConvolutionExists.add_distrib (hfg : ConvolutionExists f g L μ)
    (hfg' : ConvolutionExists f' g L μ) : (f + f') ⋆[L, μ] g = f ⋆[L, μ] g + f' ⋆[L, μ] g := by
  ext x
  exact (hfg x).add_distrib (hfg' x)
/-
**MeasureTheory.convolution_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：convolution_mono_right {f g g' : G -> Real} (hfg : ConvolutionExistsAt f g
 x (lsmul Real Real) μ) (hfg' : ConvolutionExistsAt f g' x (lsmul Real Real) μ) 
(hf : forall x, 0 <= f x) (hg : forall x, g x <= g' x) : (f ⋆[lsmul Real Real, μ
] g) x <= (f ⋆[lsmul Real Real, μ] g') x
参数：hfg : ConvolutionExistsAt f g x (lsmul Real Real) μ；hfg' : ConvolutionExistsA
t f g' x (lsmul Real Real) μ；hf : forall x, 0 <= f x；hg : forall x, g x <= g' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.integral_mono`：integral_mono {f g : α -> E} (hf : Integrab
le f μ) (hg : Integrable g μ) (h : f <= g) : ∫ x, f x ∂μ <= ∫ x, g x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem convolution_mono_right {f g g' : G → ℝ} (hfg : ConvolutionExistsAt f g x (lsmul ℝ ℝ) μ)
    (hfg' : ConvolutionExistsAt f g' x (lsmul ℝ ℝ) μ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ g' x) :
    (f ⋆[lsmul ℝ ℝ, μ] g) x ≤ (f ⋆[lsmul ℝ ℝ, μ] g') x := by
  apply integral_mono hfg hfg'
  simp only [lsmul_apply, smul_eq_mul]
  intro t
  dsimp
  gcongr
  exacts [hf _, hg _]
/-
**MeasureTheory.convolution_mono_right_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：convolution_mono_right_of_nonneg {f g g' : G -> Real} (hfg' : ConvolutionE
xistsAt f g' x (lsmul Real Real) μ) (hf : forall x, 0 <= f x) (hg : forall x, g 
x <= g' x) (hg' : forall x, 0 <= g' x) : (f ⋆[lsmul Real Real, μ] g) x <= (f ⋆[l
smul Real Real, μ] g') x
参数：hfg' : ConvolutionExistsAt f g' x (lsmul Real Real) μ；hf : forall x, 0 <= f x
；hg : forall x, g x <= g' x；hg' : forall x, 0 <= g' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.convolution_mono_right`：convolution_mono_right {f g g' : G
 -> Real} (hfg : ConvolutionExistsAt f g x (lsmul Real Real) μ) (hfg' : Convolut
ionExistsAt f g' x (lsmul …
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem convolution_mono_right_of_nonneg {f g g' : G → ℝ}
    (hfg' : ConvolutionExistsAt f g' x (lsmul ℝ ℝ) μ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ g' x)
    (hg' : ∀ x, 0 ≤ g' x) : (f ⋆[lsmul ℝ ℝ, μ] g) x ≤ (f ⋆[lsmul ℝ ℝ, μ] g') x := by
  by_cases H : ConvolutionExistsAt f g x (lsmul ℝ ℝ) μ
  · exact convolution_mono_right H hfg' hf hg
  have : (f ⋆[lsmul ℝ ℝ, μ] g) x = 0 := integral_undef H
  rw [this]
  exact integral_nonneg fun y => mul_nonneg (hf y) (hg' (x - y))

variable (L)
/-
**MeasureTheory.convolution_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：convolution_congr [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ] [IsAddR
ightInvariant μ] (h1 : f =ᵐ[μ] f') (h2 : g =ᵐ[μ] g') : f ⋆[L, μ] g = f' ⋆[L, μ] 
g'
参数：h1 : f =ᵐ[μ] f'；h2 : g =ᵐ[μ] g'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `Filter.EventuallyEq.prodMk`：∀ {α : Type u} {β : Type v} {γ : Type w} {l 
: Filter α} {f f' : α → β},   f =ᶠ[l] f' → ∀ {g g' : α → γ}, g =ᶠ[l] g' → (fun x
 => (f x, g x)) …
· 使用定理 `Filter.EventuallyEq.comp_tendsto`：Filter.EventuallyEq.comp_tendsto {l : 
Filter α} {f : α -> β} {f' : α -> β} (H : f =ᶠ[l] f') {g : γ -> α} {lc : Filter 
γ} (hg : Tendsto g lc …
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.tendsto_ae`：tendsto_ae (h :
 QuasiMeasurePreserving f μa μb) : Tendsto f (ae μa) (ae μb)
· 使用定理 `MeasureTheory.quasiMeasurePreserving_sub_left_of_right_invariant`：∀ {G :
 Type u_1} [inst : MeasurableSpace G] [inst_1 : AddGroup G] [MeasurableAdd₂ G] (
μ : MeasureTheory.Measure G)   [MeasureTheory.SFinite …
-/
theorem convolution_congr [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ]
    [IsAddRightInvariant μ] (h1 : f =ᵐ[μ] f') (h2 : g =ᵐ[μ] g') : f ⋆[L, μ] g = f' ⋆[L, μ] g' := by
  ext x
  apply integral_congr_ae
  exact (h1.prodMk <| h2.comp_tendsto
    (quasiMeasurePreserving_sub_left_of_right_invariant μ x).tendsto_ae).fun_comp ↿fun x y ↦ L x y
/-
**MeasureTheory.support_convolution_subset_swap** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：support_convolution_subset_swap : support (f ⋆[L, μ] g) subseteq support g
 + support f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.convolution_def`：convolution_def [Sub G] : (f ⋆[L, μ] g) x
 = ∫ t, L (f t) (g (x - t)) ∂μ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.map_zero`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : 
Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 
: TopologicalSpace…
· 使用定理 `ContinuousLinearMap.map_zero₂`：map_zero₂ (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
 (y : F) : f 0 y = 0
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
-/
theorem support_convolution_subset_swap : support (f ⋆[L, μ] g) ⊆ support g + support f := by
  intro x h2x
  by_contra hx
  apply h2x
  simp_rw [Set.mem_add, ← exists_and_left, not_exists, not_and_or, notMem_support] at hx
  rw [convolution_def]
  convert! integral_zero G F using 2
  ext t
  rcases hx (x - t) t with (h | h | h)
  · rw [h, (L _).map_zero]
  · rw [h, L.map_zero₂]
  · exact (h <| sub_add_cancel x t).elim

section

variable [MeasurableAdd₂ G] [MeasurableNeg G] [SFinite μ] [IsAddRightInvariant μ]

/-
**MeasureTheory.Integrable.integrable_convolution** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Integrable`。
形式化陈述：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {F : Type uF} 
[inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup E'] [inst_2 : Norme
dAddCommGroup F] {f : G → E} {g : G → E'}   [inst_3 : NontriviallyNormedField 𝕜]
 [inst_4 : NormedSpace 𝕜 E] [inst_5 : NormedSpace 𝕜 E'] [inst_6 : NormedSpace 𝕜 
F]   (L : E →L[𝕜] E' →L[𝕜] F) [inst_7 : MeasurableSpace G] {μ : MeasureTheory.Me
asure G} [inst_8 : NormedSpace ℝ F]   [inst_9 : AddGroup G] [MeasurableAdd₂ G] [
MeasurableNeg G] [MeasureTheory.SFinite μ] [μ.IsAddRightInvariant],   MeasureThe
ory.Integrable f μ →     MeasureTheory.Integrable g μ → MeasureTheory.Integrable
 (MeasureTheory.convolution f g L μ) μ
参数：L : E →L[𝕜] E' →L[𝕜] F；MeasureTheory.convolution f g L μ。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MeasureTheory.Integrable.integral_prod_left`：∀ {α : Type u_1} {β : Type 
u_2} {E : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ
 : MeasureTheory.Measure α} {ν : …
· 使用定理 `MeasureTheory.Integrable.convolution_integrand`：∀ {𝕜 : Type u𝕜} {G : Typ
e uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E] 
  [inst_1 : NormedAddCommGroup E'] […
-/
theorem Integrable.integrable_convolution (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (f ⋆[L, μ] g) μ :=
  (hf.convolution_integrand L hg).integral_prod_left

end

variable [TopologicalSpace G]
variable [IsTopologicalAddGroup G]

/-
**MeasureTheory._root_.HasCompactSupport.convolution** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.HasCompactSupport.convolution [T2Space G] (hcf : HasCompactSupport f)
    (hcg : HasCompactSupport g) : HasCompactSupport (f ⋆[L, μ] g) :=
  (hcg.isCompact.add hcf).of_isClosed_subset isClosed_closure <|
    closure_minimal
      ((support_convolution_subset_swap L).trans <| add_subset_add subset_closure subset_closure)
      (hcg.isCompact.add hcf).isClosed

variable [BorelSpace G] [TopologicalSpace P]

/-- The convolution `f * g` is continuous if `f` is locally integrable and `g` is continuous and
compactly supported. Version where `g` depends on an additional parameter in a subset `s` of
a parameter space `P` (and the compact support `k` is independent of the parameter in `s`). -/
/-
**MeasureTheory.continuousOn_convolution_right_with_param** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：continuousOn_convolution_right_with_param {g : P -> G -> E'} {s : Set P} {
k : Set G} (hk : IsCompact k) (hgs : forall p, forall x, p in s -> x ∉ k -> g p 
x = 0) (hf : LocallyIntegrable f μ) (hg : ContinuousOn ↿g (s ×ˢ univ)) : Continu
ousOn (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ)
参数：hk : IsCompact k；hgs : forall p, forall x, p in s -> x ∉ k -> g p x = 0；hf : 
LocallyIntegrable f μ；hg : ContinuousOn ↿g (s ×ˢ univ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `MeasureTheory.integral_eq_zero_of_ae`：integral_eq_zero_of_ae {f : α -> G
} (hf : f =ᵐ[μ] 0) : ∫ a, f a ∂μ = 0
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.support_subset_iff'`：∀ {ι : Type u_1} {M : Type u_3} [inst : Ze
ro M] {f : ι → M} {s : Set ι}, Function.support f ⊆ s ↔ ∀ x ∉ s, f x = 0
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_addGroup`：
∀ {G : Type w} {α : Type u} [inst : TopologicalSpace G] [inst_1 : AddGroup G] [I
sTopologicalAddGroup G]   [inst_3 : TopologicalSpace α] [ins…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
The convolution `f * g` is continuous if `f` is locally integrable and `g` is co
ntinuous and
compactly supported. Version where `g` depends on an additional parameter in a s
ubset `s` of
a parameter space `P` (and the compact support `k` is independent of the paramet
er in `s`).
-/
theorem continuousOn_convolution_right_with_param {g : P → G → E'} {s : Set P} {k : Set G}
    (hk : IsCompact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
    (hf : LocallyIntegrable f μ) (hg : ContinuousOn ↿g (s ×ˢ univ)) :
    ContinuousOn (fun q : P × G => (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) := by
  /- First get rid of the case where the space is not locally compact. Then `g` vanishes everywhere
  and the conclusion is trivial. -/
  by_cases! H : ∀ p ∈ s, ∀ x, g p x = 0
  · apply (continuousOn_const (c := 0)).congr
    rintro ⟨p, x⟩ ⟨hp, -⟩
    apply integral_eq_zero_of_ae (Eventually.of_forall (fun y ↦ ?_))
    simp [H p hp _]
  have : LocallyCompactSpace G := by
    rcases H with ⟨p, hp, x, hx⟩
    have A : support (g p) ⊆ k := support_subset_iff'.2 (fun y hy ↦ hgs p y hp hy)
    have B : Continuous (g p) := by
      refine hg.comp_continuous (.prodMk_right _) fun x => ?_
      simpa only [prodMk_mem_set_prod_eq, mem_univ, and_true] using hp
    rcases eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_addGroup hk A B with H | H
    · simp [H] at hx
    · exact H
  /- Since `G` is locally compact, one may thicken `k` a little bit into a larger compact set
  `(-k) + t`, outside of which all functions that appear in the convolution vanish. Then we can
  apply a continuity statement for integrals depending on a parameter, with respect to
  locally integrable functions and compactly supported continuous functions. -/
  rintro ⟨q₀, x₀⟩ ⟨hq₀, -⟩
  obtain ⟨t, t_comp, ht⟩ : ∃ t, IsCompact t ∧ t ∈ 𝓝 x₀ := exists_compact_mem_nhds x₀
  let k' : Set G := (-k) +ᵥ t
  have k'_comp : IsCompact k' := IsCompact.vadd_set hk.neg t_comp
  let g' : (P × G) → G → E' := fun p x ↦ g p.1 (p.2 - x)
  let s' : Set (P × G) := s ×ˢ t
  have A : ContinuousOn g'.uncurry (s' ×ˢ univ) := by
    have : g'.uncurry = g.uncurry ∘ (fun w ↦ (w.1.1, w.1.2 - w.2)) := by ext y; rfl
    rw [this]
    refine hg.comp (by fun_prop) ?_
    simp +contextual [s', MapsTo]
  have B : ContinuousOn (fun a ↦ ∫ x, L (f x) (g' a x) ∂μ) s' := by
    apply continuousOn_integral_bilinear_of_locally_integrable_of_compact_support L k'_comp A _
      (hf.integrableOn_isCompact k'_comp)
    rintro ⟨p, x⟩ y ⟨hp, hx⟩ hy
    apply hgs p _ hp
    contrapose hy
    exact ⟨y - x, by simpa using hy, x, hx, by simp⟩
  apply ContinuousWithinAt.mono_of_mem_nhdsWithin (B (q₀, x₀) ⟨hq₀, mem_of_mem_nhds ht⟩)
  exact mem_nhdsWithin_prod_iff.2 ⟨s, self_mem_nhdsWithin, t, nhdsWithin_le_nhds ht, Subset.rfl⟩

/-- The convolution `f * g` is continuous if `f` is locally integrable and `g` is continuous and
compactly supported. Version where `g` depends on an additional parameter in an open subset `s` of
a parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
given in terms of compositions with an additional continuous map. -/
/-
**MeasureTheory.continuousOn_convolution_right_with_param_comp** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：continuousOn_convolution_right_with_param_comp {s : Set P} {v : P -> G} (h
v : ContinuousOn v s) {g : P -> G -> E'} {k : Set G} (hk : IsCompact k) (hgs : f
orall p, forall x, p in s -> x ∉ k -> g p x = 0) (hf : LocallyIntegrable f μ) (h
g : ContinuousOn ↿g (s ×ˢ univ)) : ContinuousOn (fun x => (f ⋆[L, μ] g x) (v x))
 s
参数：hv : ContinuousOn v s；hk : IsCompact k；hgs : forall p, forall x, p in s -> x 
∉ k -> g p x = 0；hf : LocallyIntegrable f μ；hg : ContinuousOn ↿g (s ×ˢ univ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `MeasureTheory.continuousOn_convolution_right_with_param`：continuousOn_co
nvolution_right_with_param {g : P -> G -> E'} {s : Set P} {k : Set G} (hk : IsCo
mpact k) (hgs : forall p, forall x, p in s ->…
· 使用定理 `ContinuousOn.prodMk`：ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : 
Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => 
(f x, g x…
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
The convolution `f * g` is continuous if `f` is locally integrable and `g` is co
ntinuous and
compactly supported. Version where `g` depends on an additional parameter in an 
open subset `s` of
a parameter space `P` (and the compact support `k` is independent of the paramet
er in `s`),
given in terms of compositions with an additional continuous map.
-/
theorem continuousOn_convolution_right_with_param_comp {s : Set P} {v : P → G}
    (hv : ContinuousOn v s) {g : P → G → E'} {k : Set G} (hk : IsCompact k)
    (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0) (hf : LocallyIntegrable f μ)
    (hg : ContinuousOn ↿g (s ×ˢ univ)) : ContinuousOn (fun x => (f ⋆[L, μ] g x) (v x)) s := by
  apply
    (continuousOn_convolution_right_with_param L hk hgs hf hg).comp (continuousOn_id.prodMk hv)
  intro x hx
  simp only [hx, prodMk_mem_set_prod_eq, mem_univ, and_self_iff, _root_.id]

/-- The convolution is continuous if one function is locally integrable and the other has compact
support and is continuous. -/
/-
**MeasureTheory._root_.HasCompactSupport.continuous_convolution_right** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The convolution is continuous if one function is locally integrable and the othe
r has compact
support and is continuous.
-/
theorem _root_.HasCompactSupport.continuous_convolution_right (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : Continuous g) : Continuous (f ⋆[L, μ] g) := by
  rw [← continuousOn_univ]
  let g' : G → G → E' := fun _ q => g q
  have : ContinuousOn ↿g' (univ ×ˢ univ) := (hg.comp continuous_snd).continuousOn
  exact continuousOn_convolution_right_with_param_comp L
    (continuousOn_univ.2 continuous_id) hcg
    (fun p x _ hx => image_eq_zero_of_notMem_tsupport hx) hf this

/-- The convolution is continuous if one function is integrable and the other is bounded and
continuous. -/
/-
**MeasureTheory._root_.BddAbove.continuous_convolution_right_of_integrable** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The convolution is continuous if one function is integrable and the other is bou
nded and
continuous.
-/
theorem _root_.BddAbove.continuous_convolution_right_of_integrable
    [FirstCountableTopology G] [SecondCountableTopologyEither G E']
    (hbg : BddAbove (range fun x => ‖g x‖)) (hf : Integrable f μ) (hg : Continuous g) :
    Continuous (f ⋆[L, μ] g) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t : G ∂μ, ‖L (f t) (g (x - t))‖ ≤ ‖L‖ * ‖f t‖ * ⨆ i, ‖g i‖ := by
    filter_upwards with x; filter_upwards with t
    apply_rules [L.le_of_opNorm₂_le_of_le, le_rfl, le_ciSup hbg (x - t)]
  refine continuousAt_of_dominated ?_ this (by fun_prop) ?_
  · exact Eventually.of_forall fun x =>
      hf.aestronglyMeasurable.convolution_integrand_snd' L hg.aestronglyMeasurable
  · filter_upwards with t; fun_prop

end Group

section CommGroup

variable [AddCommGroup G]

/-
**MeasureTheory.support_convolution_subset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：support_convolution_subset : support (f ⋆[L, μ] g) subseteq support f + su
pport g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.support_convolution_subset_swap`：support_convolution_subse
t_swap : support (f ⋆[L, μ] g) subseteq support g + support f
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem support_convolution_subset : support (f ⋆[L, μ] g) ⊆ support f + support g :=
  (support_convolution_subset_swap L).trans (add_comm _ _).subset

variable [IsAddLeftInvariant μ] [IsNegInvariant μ]

section Measurable

variable [MeasurableNeg G]
variable [MeasurableAdd G]

/-- Commutativity of convolution -/
/-
**MeasureTheory.convolution_flip** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：convolution_flip : g ⋆[L.flip, μ] f = f ⋆[L, μ] g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_sub_left_eq_self`：∀ {G : Type u_4} {E : Type u_5}
 [inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpac
e ℝ E]   [inst_3 : AddGroup G…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_sub_self`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - (a
 - b) = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Commutativity of convolution
-/
theorem convolution_flip : g ⋆[L.flip, μ] f = f ⋆[L, μ] g := by
  ext1 x
  simp_rw [convolution_def]
  rw [← integral_sub_left_eq_self _ μ x]
  simp_rw [sub_sub_self, flip_apply]

/-- The symmetric definition of convolution. -/
/-
**MeasureTheory.convolution_eq_swap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：convolution_eq_swap : (f ⋆[L, μ] g) x = ∫ t, L (f (x - t)) (g t) ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.convolution_flip`：convolution_flip : g ⋆[L.flip, μ] f = f 
⋆[L, μ] g

--- 原说明 ---
The symmetric definition of convolution.
-/
theorem convolution_eq_swap : (f ⋆[L, μ] g) x = ∫ t, L (f (x - t)) (g t) ∂μ := by
  rw [← convolution_flip]; rfl

/-- The symmetric definition of convolution where the bilinear operator is scalar multiplication. -/
/-
**MeasureTheory.convolution_lsmul_swap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：convolution_lsmul_swap {f : G -> 𝕜} {g : G -> F} : (f ⋆[lsmul 𝕜 𝕜, μ] g : 
G -> F) x = ∫ t, f (x - t) • g t ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.convolution_eq_swap`：convolution_eq_swap : (f ⋆[L, μ] g) x
 = ∫ t, L (f (x - t)) (g t) ∂μ

--- 原说明 ---
The symmetric definition of convolution where the bilinear operator is scalar mu
ltiplication.
-/
theorem convolution_lsmul_swap {f : G → 𝕜} {g : G → F} :
    (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f (x - t) • g t ∂μ :=
  convolution_eq_swap _

/-- The symmetric definition of convolution where the bilinear operator is multiplication. -/
/-
**MeasureTheory.convolution_mul_swap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：convolution_mul_swap [NormedSpace Real 𝕜] {f : G -> 𝕜} {g : G -> 𝕜} : (f ⋆
[mul 𝕜 𝕜, μ] g) x = ∫ t, f (x - t) * g t ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.convolution_eq_swap`：convolution_eq_swap : (f ⋆[L, μ] g) x
 = ∫ t, L (f (x - t)) (g t) ∂μ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
The symmetric definition of convolution where the bilinear operator is multiplic
ation.
-/
theorem convolution_mul_swap [NormedSpace ℝ 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
    (f ⋆[mul 𝕜 𝕜, μ] g) x = ∫ t, f (x - t) * g t ∂μ :=
  convolution_eq_swap _

/-- The convolution of two even functions is also even. -/
/-
**MeasureTheory.convolution_neg_of_neg_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：convolution_neg_of_neg_eq (h1 : forallᵐ x ∂μ, f (-x) = f x) (h2 : forallᵐ 
x ∂μ, g (-x) = g x) : (f ⋆[L, μ] g) (-x) = (f ⋆[L, μ] g) x
参数：h1 : forallᵐ x ∂μ, f (-x) = f x；h2 : forallᵐ x ∂μ, g (-x) = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.eventually_add_left_iff`：∀ {G : Type u_1} [inst : Measurab
leSpace G] [inst_1 : AddGroup G] [MeasurableAdd G] (μ : MeasureTheory.Measure G)
   [μ.IsAddLeftInvariant] (…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_add'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a + b) = -a - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_neg_eq_self`：∀ {G : Type u_4} {E : Type u_5} [ins
t : MeasurableSpace G] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E
]   [inst_3 : AddGroup G…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a

--- 原说明 ---
The convolution of two even functions is also even.
-/
theorem convolution_neg_of_neg_eq (h1 : ∀ᵐ x ∂μ, f (-x) = f x) (h2 : ∀ᵐ x ∂μ, g (-x) = g x) :
    (f ⋆[L, μ] g) (-x) = (f ⋆[L, μ] g) x :=
  calc
    ∫ t : G, (L (f t)) (g (-x - t)) ∂μ = ∫ t : G, (L (f (-t))) (g (x + t)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [h1, (eventually_add_left_iff μ x).2 h2] with t ht h't
      simp_rw [ht, ← h't, neg_add']
    _ = ∫ t : G, (L (f t)) (g (x - t)) ∂μ := by
      rw [← integral_neg_eq_self]
      simp only [neg_neg, ← sub_eq_add_neg]

end Measurable

variable [TopologicalSpace G]
variable [IsTopologicalAddGroup G]
variable [BorelSpace G]

/-
**MeasureTheory._root_.HasCompactSupport.continuous_convolution_left** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.HasCompactSupport.continuous_convolution_left
    (hcf : HasCompactSupport f) (hf : Continuous f) (hg : LocallyIntegrable g μ) :
    Continuous (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact hcf.continuous_convolution_right L.flip hg hf
/-
**MeasureTheory._root_.BddAbove.continuous_convolution_left_of_integrable** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.BddAbove.continuous_convolution_left_of_integrable
    [FirstCountableTopology G] [SecondCountableTopologyEither G E]
    (hbf : BddAbove (range fun x => ‖f x‖)) (hf : Continuous f) (hg : Integrable g μ) :
    Continuous (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact hbf.continuous_convolution_right_of_integrable L.flip hg hf

end CommGroup

section NormedAddCommGroup

variable [SeminormedAddCommGroup G]

/-- Compute `(f ⋆ g) x₀` if the support of the `f` is within `Metric.ball 0 R`, and `g` is constant
on `Metric.ball x₀ R`.

We can simplify the RHS further if we assume `f` is integrable, but also if `L = (•)` or more
generally if `L` has an `AntilipschitzWith`-condition. -/
/-
**MeasureTheory.convolution_eq_right'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：convolution_eq_right' {x₀ : G} {R : Real} (hf : support f subseteq ball (0
 : G) R) (hg : forall x in ball x₀ R, g x = g x₀) : (f ⋆[L, μ] g) x₀ = ∫ t, L (f
 t) (g x₀) ∂μ
参数：hf : support f subseteq ball (0 : G) R；hg : forall x in ball x₀ R, g x = g x₀
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `add_mem_ball_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E
] {a b : E} {r : ℝ}, a + b ∈ Metric.ball a r ↔ ‖b‖ < r
· 使用定理 `mem_ball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E
} {r : ℝ}, a ∈ Metric.ball 0 r ↔ ‖a‖ < r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.notMem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M]
 {f : ι → M} {x : ι}, x ∉ Function.support f ↔ f x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.map_zero₂`：map_zero₂ (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
 (y : F) : f 0 y = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Compute `(f ⋆ g) x₀` if the support of the `f` is within `Metric.ball 0 R`, and 
`g` is constant
on `Metric.ball x₀ R`.

We can simplify the RHS further if we assume `f` is integrable, but also if `L =
 (•)` or more
generally if `L` has an `AntilipschitzWith`-condition.
-/
theorem convolution_eq_right' {x₀ : G} {R : ℝ} (hf : support f ⊆ ball (0 : G) R)
    (hg : ∀ x ∈ ball x₀ R, g x = g x₀) : (f ⋆[L, μ] g) x₀ = ∫ t, L (f t) (g x₀) ∂μ := by
  have h2 : ∀ t, L (f t) (g (x₀ - t)) = L (f t) (g x₀) := fun t ↦ by
    by_cases ht : t ∈ support f
    · have h2t := hf ht
      rw [mem_ball_zero_iff] at h2t
      specialize hg (x₀ - t)
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg
      rw [hg h2t]
    · rw [notMem_support] at ht
      simp_rw [ht, L.map_zero₂]
  simp_rw [convolution_def, h2]

variable [BorelSpace G] [SecondCountableTopology G]
variable [IsAddLeftInvariant μ] [SFinite μ]

/-- Approximate `(f ⋆ g) x₀` if the support of the `f` is bounded within a ball, and `g` is near
`g x₀` on a ball with the same radius around `x₀`. See `dist_convolution_le` for a special case.

We can simplify the second argument of `dist` further if we add some extra type-classes on `E`
and `𝕜` or if `L` is scalar multiplication. -/
/-
**MeasureTheory.dist_convolution_le'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：dist_convolution_le' {x₀ : G} {R ε : Real} {z₀ : E'} (hε : 0 <= ε) (hif : 
Integrable f μ) (hf : support f subseteq ball (0 : G) R) (hmg : AEStronglyMeasur
able g μ) (hg : forall x in ball x₀ R, dist (g x) z₀ <= ε) : dist ((f ⋆[L, μ] g 
: G -> F) x₀) (∫ t, L (f t) z₀ ∂μ) <= (‖L‖ * ∫ x, ‖f x‖ ∂μ) * ε
参数：hε : 0 <= ε；hif : Integrable f μ；hf : support f subseteq ball (0 : G) R；hmg :
 AEStronglyMeasurable g μ；hg : forall x in ball x₀ R, dist (g x) z₀ <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `BddAbove.convolutionExistsAt`：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE
} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E]   [inst_1 : Normed
AddCommGroup E'] […
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bddAbove_def`：bddAbove_def : BddAbove s ↔ exists x, forall y in s, y <= 
x
· 使用定理 `norm_le_norm_add_const_of_dist_le`：∀ {E : Type u_5} [inst : SeminormedAd
dGroup E] {a b : E} {r : ℝ}, dist a b ≤ r → ‖a‖ ≤ ‖b‖ + r
· 使用定理 `mem_ball_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] {a
 b : E} {r : ℝ}, b ∈ Metric.ball a r ↔ ‖b - a‖ < r
· 使用定理 `norm_sub_rev`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), 
‖a - b‖ = ‖b - a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_ball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E
} {r : ℝ}, a ∈ Metric.ball 0 r ↔ ‖a‖ < r
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.map_zero₂`：map_zero₂ (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G)
 (y : F) : f 0 y = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ContinuousLinearMap.dist_le_opNorm`：dist_le_opNorm (x y : E) : dist (f x
) (f y) <= ‖f‖ * dist x y
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
Approximate `(f ⋆ g) x₀` if the support of the `f` is bounded within a ball, and
 `g` is near
`g x₀` on a ball with the same radius around `x₀`. See `dist_convolution_le` for
 a special case.

We can simplify the second argument of `dist` further if we add some extra type-
classes on `E`
and `𝕜` or if `L` is scalar multiplication.
-/
theorem dist_convolution_le' {x₀ : G} {R ε : ℝ} {z₀ : E'} (hε : 0 ≤ ε) (hif : Integrable f μ)
    (hf : support f ⊆ ball (0 : G) R) (hmg : AEStronglyMeasurable g μ)
    (hg : ∀ x ∈ ball x₀ R, dist (g x) z₀ ≤ ε) :
    dist ((f ⋆[L, μ] g : G → F) x₀) (∫ t, L (f t) z₀ ∂μ) ≤ (‖L‖ * ∫ x, ‖f x‖ ∂μ) * ε := by
  have hfg : ConvolutionExistsAt f g x₀ L μ := by
    refine BddAbove.convolutionExistsAt L ?_ Metric.isOpen_ball.measurableSet (Subset.trans ?_ hf)
      hif.integrableOn hmg
    swap; · refine fun t => mt fun ht : f t = 0 => ?_; simp_rw [ht, L.map_zero₂]
    rw [bddAbove_def]
    refine ⟨‖z₀‖ + ε, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    refine norm_le_norm_add_const_of_dist_le (hg x ?_)
    rwa [mem_ball_iff_norm, norm_sub_rev, ← mem_ball_zero_iff]
  have h2 : ∀ t, dist (L (f t) (g (x₀ - t))) (L (f t) z₀) ≤ ‖L (f t)‖ * ε := by
    intro t; by_cases ht : t ∈ support f
    · have h2t := hf ht
      rw [mem_ball_zero_iff] at h2t
      specialize hg (x₀ - t)
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg
      refine ((L (f t)).dist_le_opNorm _ _).trans ?_
      gcongr
      exact hg h2t
    · rw [notMem_support] at ht
      simp_rw [ht, L.map_zero₂, L.map_zero, norm_zero, zero_mul, dist_self]
      rfl
  simp_rw [convolution_def]
  simp_rw [dist_eq_norm] at h2 ⊢
  rw [← integral_sub hfg.integrable]; swap; · exact (L.flip z₀).integrable_comp hif
  refine (norm_integral_le_of_norm_le ((L.integrable_comp hif).norm.mul_const ε)
    (Eventually.of_forall h2)).trans ?_
  rw [integral_mul_const]
  gcongr
  have h3 : ∀ t, ‖L (f t)‖ ≤ ‖L‖ * ‖f t‖ := by
    intro t
    exact L.le_opNorm (f t)
  refine (integral_mono (L.integrable_comp hif).norm (hif.norm.const_mul _) h3).trans_eq ?_
  rw [integral_const_mul]

variable [NormedSpace ℝ E] [NormedSpace ℝ E'] [CompleteSpace E']

/-- Approximate `f ⋆ g` if the support of the `f` is bounded within a ball, and `g` is near `g x₀`
on a ball with the same radius around `x₀`.

This is a special case of `dist_convolution_le'` where `L` is `(•)`, `f` has integral 1 and `f` is
nonnegative. -/
/-
**MeasureTheory.dist_convolution_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：dist_convolution_le {f : G -> Real} {x₀ : G} {R ε : Real} {z₀ : E'} (hε : 
0 <= ε) (hf : support f subseteq ball (0 : G) R) (hnf : forall x, 0 <= f x) (hin
tf : ∫ x, f x ∂μ = 1) (hmg : AEStronglyMeasurable g μ) (hg : forall x in ball x₀
 R, dist (g x) z₀ <= ε) : dist ((f ⋆[lsmul Real Real, μ] g : G -> E') x₀) z₀ <= 
ε
参数：hε : 0 <= ε；hf : support f subseteq ball (0 : G) R；hnf : forall x, 0 <= f x；h
intf : ∫ x, f x ∂μ = 1；hmg : AEStronglyMeasurable g μ；hg : forall x in ball x₀ R
, dist (g x) z₀ <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_of_integral_eq_one`：integrable_of_integral_eq_o
ne {f : α -> Real} (h : ∫ x, f x ∂μ = 1) : Integrable f μ
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `integral_smul_const`：integral_smul_const {𝕜 : Type*} [RCLike 𝕜] [NormedS
pace 𝕜 E] [CompleteSpace E] (f : X -> 𝕜) (c : E) : ∫ x, f x • c ∂μ = (∫ x, f x ∂
μ) • c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.dist_convolution_le'`：dist_convolution_le' {x₀ : G} {R ε :
 Real} {z₀ : E'} (hε : 0 <= ε) (hif : Integrable f μ) (hf : support f subseteq b
all (0 : G) R) (hmg : AE…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `ContinuousLinearMap.opNorm_lsmul_le`：opNorm_lsmul_le : ‖(lsmul 𝕜 R : R -
>L[𝕜] E ->L[𝕜] E)‖ <= 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
Approximate `f ⋆ g` if the support of the `f` is bounded within a ball, and `g` 
is near `g x₀`
on a ball with the same radius around `x₀`.

This is a special case of `dist_convolution_le'` where `L` is `(•)`, `f` has int
egral 1 and `f` is
nonnegative.
-/
theorem dist_convolution_le {f : G → ℝ} {x₀ : G} {R ε : ℝ} {z₀ : E'} (hε : 0 ≤ ε)
    (hf : support f ⊆ ball (0 : G) R) (hnf : ∀ x, 0 ≤ f x) (hintf : ∫ x, f x ∂μ = 1)
    (hmg : AEStronglyMeasurable g μ) (hg : ∀ x ∈ ball x₀ R, dist (g x) z₀ ≤ ε) :
    dist ((f ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) z₀ ≤ ε := by
  have hif : Integrable f μ := integrable_of_integral_eq_one hintf
  convert! (dist_convolution_le' (lsmul ℝ ℝ) hε hif hf hmg hg).trans _
  · simp_rw [lsmul_apply, integral_smul_const, hintf, one_smul]
  · simp_rw [Real.norm_of_nonneg (hnf _), hintf, mul_one]
    exact (mul_le_mul_of_nonneg_right opNorm_lsmul_le hε).trans_eq (one_mul ε)

/-- `(φ i ⋆ g i) (k i)` tends to `z₀` as `i` tends to some filter `l` if
* `φ` is a sequence of nonnegative functions with integral `1` as `i` tends to `l`;
* The support of `φ` tends to small neighborhoods around `(0 : G)` as `i` tends to `l`;
* `g i` is `mu`-a.e. strongly measurable as `i` tends to `l`;
* `g i x` tends to `z₀` as `(i, x)` tends to `l ×ˢ 𝓝 x₀`;
* `k i` tends to `x₀`.

See also `ContDiffBump.convolution_tendsto_right`.
-/
/-
**MeasureTheory.convolution_tendsto_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：convolution_tendsto_right {ι} {g : ι -> G -> E'} {l : Filter ι} {x₀ : G} {
z₀ : E'} {φ : ι -> G -> Real} {k : ι -> G} (hnφ : forallᶠ i in l, forall x, 0 <=
 φ i x) (hiφ : forallᶠ i in l, ∫ x, φ i x ∂μ = 1) -- todo: we could weaken this 
to "the integral tends to 1" (hφ : Tendsto (fun n => support (φ n)) l (𝓝 0).smal
lSets) (hmg : forallᶠ i in l, AEStronglyMeasurable (g i) μ) (hcg : Tendsto (uncu
rry g) (l ×ˢ 𝓝 x₀) (𝓝 z₀)) (hk : Tendsto k l (𝓝 x₀)) : Tendsto (fun i : ι => (φ 
i ⋆[lsmul Real Real, μ] g 
参数：hnφ : forallᶠ i in l, forall x, 0 <= φ i x；hiφ : forallᶠ i in l, ∫ x, φ i x ∂
μ = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.tendsto_nhds`：tendsto_nhds {f : Filter β} {u : β -> α} {a : α} : 
Tendsto u f (𝓝 a) ↔ forall ε > 0, forallᶠ x in f, dist (u x) a < ε
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `half_lt_self`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : PartialOrd
er α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 < a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `dist_triangle_right`：dist_triangle_right (x y z : α) : dist x y <= dist 
x z + dist y z
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
（共 75 条，此处仅展示前 30 条）

--- 原说明 ---
`(φ i ⋆ g i) (k i)` tends to `z₀` as `i` tends to some filter `l` if
* `φ` is a sequence of nonnegative functions with integral `1` as `i` tends to `
l`;
* The support of `φ` tends to small neighborhoods around `(0 : G)` as `i` tends 
to `l`;
* `g i` is `mu`-a.e. strongly measurable as `i` tends to `l`;
* `g i x` tends to `z₀` as `(i, x)` tends to `l ×ˢ 𝓝 x₀`;
* `k i` tends to `x₀`.

See also `ContDiffBump.convolution_tendsto_right`.
-/
theorem convolution_tendsto_right {ι} {g : ι → G → E'} {l : Filter ι} {x₀ : G} {z₀ : E'}
    {φ : ι → G → ℝ} {k : ι → G} (hnφ : ∀ᶠ i in l, ∀ x, 0 ≤ φ i x)
    (hiφ : ∀ᶠ i in l, ∫ x, φ i x ∂μ = 1)
    -- todo: we could weaken this to "the integral tends to 1"
    (hφ : Tendsto (fun n => support (φ n)) l (𝓝 0).smallSets)
    (hmg : ∀ᶠ i in l, AEStronglyMeasurable (g i) μ) (hcg : Tendsto (uncurry g) (l ×ˢ 𝓝 x₀) (𝓝 z₀))
    (hk : Tendsto k l (𝓝 x₀)) :
    Tendsto (fun i : ι => (φ i ⋆[lsmul ℝ ℝ, μ] g i : G → E') (k i)) l (𝓝 z₀) := by
  simp_rw [tendsto_smallSets_iff] at hφ
  rw [Metric.tendsto_nhds] at hcg ⊢
  simp_rw [Metric.eventually_prod_nhds_iff] at hcg
  intro ε hε
  have h2ε : 0 < ε / 3 := div_pos hε (by simp)
  obtain ⟨p, hp, δ, hδ, hgδ⟩ := hcg _ h2ε
  dsimp only [uncurry] at hgδ
  have h2k := hk.eventually (ball_mem_nhds x₀ <| half_pos hδ)
  have h2φ := hφ (ball (0 : G) _) <| ball_mem_nhds _ (half_pos hδ)
  filter_upwards [hp, h2k, h2φ, hnφ, hiφ, hmg] with i hpi hki hφi hnφi hiφi hmgi
  have hgi : dist (g i (k i)) z₀ < ε / 3 := hgδ hpi (hki.trans <| half_lt_self hδ)
  have h1 : ∀ x' ∈ ball (k i) (δ / 2), dist (g i x') (g i (k i)) ≤ ε / 3 + ε / 3 := by
    intro x' hx'
    grw [dist_triangle_right, hgδ hpi ?_, hgi]
    grw [dist_triangle, hx'.out, hki, add_halves]
  have := dist_convolution_le (add_pos h2ε h2ε).le hφi hnφi hiφi hmgi h1
  refine ((dist_triangle _ _ _).trans_lt (add_lt_add_of_le_of_lt this hgi)).trans_eq ?_
  ring

end NormedAddCommGroup

end Measurability

end NontriviallyNormedField

open scoped Convolution

section RCLike
variable [RCLike 𝕜]
variable [NormedSpace 𝕜 E]
variable [NormedSpace 𝕜 E']
variable [NormedSpace 𝕜 E'']
variable [NormedSpace ℝ F] [NormedSpace 𝕜 F]
variable {n : ℕ∞}
variable [MeasurableSpace G] {μ ν : Measure G}
variable (L : E →L[𝕜] E' →L[𝕜] F)

section Assoc
variable [CompleteSpace F]
variable [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [CompleteSpace F']
variable [NormedAddCommGroup F''] [NormedSpace ℝ F''] [NormedSpace 𝕜 F''] [CompleteSpace F'']
variable {k : G → E''}
variable (L₂ : F →L[𝕜] E'' →L[𝕜] F')
variable (L₃ : E →L[𝕜] F'' →L[𝕜] F')
variable (L₄ : E' →L[𝕜] E'' →L[𝕜] F'')
variable [AddGroup G]
variable [SFinite μ] [SFinite ν] [IsAddRightInvariant μ]

/-
**MeasureTheory.integral_convolution** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_convolution [MeasurableAdd₂ G] [MeasurableNeg G] [NormedSpace Rea
l E] [NormedSpace Real E'] [CompleteSpace E] [CompleteSpace E'] (hf : Integrable
 f ν) (hg : Integrable g μ) : ∫ x, (f ⋆[L, ν] g) x ∂μ = L (∫ x, f x ∂ν) (∫ x, g 
x ∂μ)
参数：hf : Integrable f ν；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_integral_swap`：integral_integral_swap ⦃f : α -> β
 -> E⦄ (hf : Integrable (uncurry f) (μ.prod ν)) : ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫
 x, f x y ∂μ ∂ν
· 使用定理 `MeasureTheory.Integrable.convolution_integrand`：∀ {𝕜 : Type u𝕜} {G : Typ
e uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E] 
  [inst_1 : NormedAddCommGroup E'] […
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `MeasureTheory.Integrable.comp_sub_right`：∀ {G : Type u_4} {F : Type u_6}
 [inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory.M
easure G}   [inst_2 : AddGrou…
· 使用定理 `MeasurableAdd₂.toMeasurableAdd`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Add M] [MeasurableAdd₂ M], MeasurableAdd M
· 使用定理 `MeasureTheory.integral_sub_right_eq_self`：∀ {G : Type u_4} {E : Type u_5
} [inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpa
ce ℝ E]   {μ : MeasureTheory.M…
-/
theorem integral_convolution [MeasurableAdd₂ G] [MeasurableNeg G] [NormedSpace ℝ E]
    [NormedSpace ℝ E'] [CompleteSpace E] [CompleteSpace E'] (hf : Integrable f ν)
    (hg : Integrable g μ) : ∫ x, (f ⋆[L, ν] g) x ∂μ = L (∫ x, f x ∂ν) (∫ x, g x ∂μ) := by
  refine (integral_integral_swap (by apply hf.convolution_integrand L hg)).trans ?_
  simp_rw [integral_comp_comm _ (hg.comp_sub_right _), integral_sub_right_eq_self]
  exact (L.flip (∫ x, g x ∂μ)).integral_comp_comm hf

variable [MeasurableAdd₂ G] [IsAddRightInvariant ν] [MeasurableNeg G]

/-- Convolution is associative. This has a weak but inconvenient integrability condition.
See also `MeasureTheory.convolution_assoc`. -/
/-
**MeasureTheory.convolution_assoc'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：convolution_assoc' (hL : forall (x : E) (y : E') (z : E''), L₂ (L x y) z =
 L₃ x (L₄ y z)) {x₀ : G} (hfg : forallᵐ y ∂μ, ConvolutionExistsAt f g y L ν) (hg
k : forallᵐ x ∂ν, ConvolutionExistsAt g k x L₄ μ) (hi : Integrable (uncurry fun 
x y => (L₃ (f y)) ((L₄ (g (x - y))) (k (x₀ - x)))) (μ.prod ν)) : ((f ⋆[L, ν] g) 
⋆[L₂, μ] k) x₀ = (f ⋆[L₃, ν] g ⋆[L₄, μ] k) x₀
参数：hL : forall (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z)；hfg : fo
rallᵐ y ∂μ, ConvolutionExistsAt f g y L ν；hgk : forallᵐ x ∂ν, ConvolutionExistsA
t g k x L₄ μ；hi : Integrable (uncurry fun x y => (L₃ (f y)) ((L₄ (g (x - y))) (k
 (x₀ - x)))) (μ.prod ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_integral_swap`：integral_integral_swap ⦃f : α -> β
 -> E⦄ (hf : Integrable (uncurry f) (μ.prod ν)) : ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫
 x, f x y ∂μ ∂ν
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `MeasureTheory.integral_sub_right_eq_self`：∀ {G : Type u_4} {E : Type u_5
} [inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpa
ce ℝ E]   {μ : MeasureTheory.M…
· 使用定理 `MeasurableAdd₂.toMeasurableAdd`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Add M] [MeasurableAdd₂ M], MeasurableAdd M
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.ae`：ae (h : QuasiMeasurePre
serving f μa μb) {p : β -> Prop} (hg : forallᵐ x ∂μb, p x) : forallᵐ x ∂μa, p (f
 x)
· 使用定理 `MeasureTheory.quasiMeasurePreserving_sub_left_of_right_invariant`：∀ {G :
 Type u_1} [inst : MeasurableSpace G] [inst_1 : AddGroup G] [MeasurableAdd₂ G] (
μ : MeasureTheory.Measure G)   [MeasureTheory.SFinite …

--- 原说明 ---
Convolution is associative. This has a weak but inconvenient integrability condi
tion.
See also `MeasureTheory.convolution_assoc`.
-/
theorem convolution_assoc' (hL : ∀ (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z))
    {x₀ : G} (hfg : ∀ᵐ y ∂μ, ConvolutionExistsAt f g y L ν)
    (hgk : ∀ᵐ x ∂ν, ConvolutionExistsAt g k x L₄ μ)
    (hi : Integrable (uncurry fun x y => (L₃ (f y)) ((L₄ (g (x - y))) (k (x₀ - x)))) (μ.prod ν)) :
    ((f ⋆[L, ν] g) ⋆[L₂, μ] k) x₀ = (f ⋆[L₃, ν] g ⋆[L₄, μ] k) x₀ :=
  calc
    ((f ⋆[L, ν] g) ⋆[L₂, μ] k) x₀ = ∫ t, L₂ (∫ s, L (f s) (g (t - s)) ∂ν) (k (x₀ - t)) ∂μ := rfl
    _ = ∫ t, ∫ s, L₂ (L (f s) (g (t - s))) (k (x₀ - t)) ∂ν ∂μ :=
      (integral_congr_ae (hfg.mono fun t ht => ((L₂.flip (k (x₀ - t))).integral_comp_comm ht).symm))
    _ = ∫ t, ∫ s, L₃ (f s) (L₄ (g (t - s)) (k (x₀ - t))) ∂ν ∂μ := by simp_rw [hL]
    _ = ∫ s, ∫ t, L₃ (f s) (L₄ (g (t - s)) (k (x₀ - t))) ∂μ ∂ν := by rw [integral_integral_swap hi]
    _ = ∫ s, ∫ u, L₃ (f s) (L₄ (g u) (k (x₀ - s - u))) ∂μ ∂ν := by
      congr; ext t
      rw [eq_comm, ← integral_sub_right_eq_self _ t]
      simp_rw [sub_sub_sub_cancel_right]
    _ = ∫ s, L₃ (f s) (∫ u, L₄ (g u) (k (x₀ - s - u)) ∂μ) ∂ν := by
      refine integral_congr_ae ?_
      refine ((quasiMeasurePreserving_sub_left_of_right_invariant ν x₀).ae hgk).mono fun t ht => ?_
      exact (L₃ (f t)).integral_comp_comm ht
    _ = (f ⋆[L₃, ν] g ⋆[L₄, μ] k) x₀ := rfl

/-- Convolution is associative. This requires that
* all maps are a.e. strongly measurable w.r.t. one of the measures
* `f ⋆[L, ν] g` exists almost everywhere
* `‖g‖ ⋆[μ] ‖k‖` exists almost everywhere
* `‖f‖ ⋆[ν] (‖g‖ ⋆[μ] ‖k‖)` exists at `x₀` -/
/-
**MeasureTheory.convolution_assoc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：convolution_assoc (hL : forall (x : E) (y : E') (z : E''), L₂ (L x y) z = 
L₃ x (L₄ y z)) {x₀ : G} (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurab
le g μ) (hk : AEStronglyMeasurable k μ) (hfg : forallᵐ y ∂μ, ConvolutionExistsAt
 f g y L ν) (hgk : forallᵐ x ∂ν, ConvolutionExistsAt (fun x => ‖g x‖) (fun x => 
‖k x‖) x (mul Real Real) μ) (hfgk : ConvolutionExistsAt (fun x => ‖f x‖) ((fun x
 => ‖g x‖) ⋆[mul Real Real, μ] fun x => ‖k x‖) x₀ (mul Real Real) ν) : ((f ⋆[L, 
ν] g) ⋆[L₂, μ] k) x₀ = (f 
参数：hL : forall (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z)；hf : AES
tronglyMeasurable f ν；hg : AEStronglyMeasurable g μ；hk : AEStronglyMeasurable k 
μ；hfg : forallᵐ y ∂μ, ConvolutionExistsAt f g y L ν；hgk : forallᵐ x ∂ν, Convolut
ionExistsAt (fun x => ‖g x‖) (fun x => ‖k x‖) x (mul Real Real) μ；hfgk : Convolu
tionExistsAt (fun x => ‖f x‖) ((fun x => ‖g x‖) ⋆[mul Real Real, μ] fun x => ‖k 
x‖) x₀ (mul Real Real) ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MeasureTheory.convolution_assoc'`：convolution_assoc' (hL : forall (x : E
) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z)) {x₀ : G} (hfg : forallᵐ y ∂μ
, ConvolutionExistsAt …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.ConvolutionExistsAt.of_norm`：∀ {𝕜 : Type u𝕜} {G : Type uG}
 {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E]   [in
st_1 : NormedAddCommGroup E'] […
· 使用定理 `ContinuousLinearMap.aestronglyMeasurable_comp₂`：ContinuousLinearMap.aest
ronglyMeasurable_comp₂ (L : E ->L[𝕜] F ->L[𝕜] G) {f : α -> E} {g : α -> F} (hf :
 AEStronglyMeasurable f μ) (hg : AES…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_snd`：MeasureTheory.AEStronglyMea
surable.comp_snd {γ} [TopologicalSpace γ] {f : β -> γ} (hf : AEStronglyMeasurabl
e f ν) : AEStronglyMeasurable (fu…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_fst`：MeasureTheory.AEStronglyMea
surable.comp_fst {γ} [TopologicalSpace γ] {f : α -> γ} (hf : AEStronglyMeasurabl
e f μ) : AEStronglyMeasurable (fu…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_measurable`：comp_measurable {γ :
 Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α} {μ : Measur
e γ} (hg : AEStronglyMeasurable g (Measu…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_ac`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ ν : MeasureTheory.
Measure α}   {f : α → β},   ν.Ab…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
· 使用定理 `MeasureTheory.QuasiMeasurePreserving.prod_of_left`：prod_of_left {α β γ} 
[MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α × β -> γ} {μ 
: Measure α} {ν : Measure β} {τ : Measu…
· 使用定理 `Measurable.fun_sub`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSp
ace G] [inst_1 : Sub G] {m : MeasurableSpace α} {f g : α → G}   [MeasurableSub₂ 
G], Meas…
· 使用定理 `measurableDiv₂_of_add_neg`：∀ (G : Type u_2) [inst : MeasurableSpace G] [
inst_1 : SubNegMonoid G] [MeasurableAdd₂ G] [MeasurableNeg G],   MeasurableSub₂ 
G
· 使用定理 `Measurable.const_sub`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurable
Space G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   [MeasurableSub G
], Measura…
· 使用定理 `measurableSub_of_add_neg`：∀ (G : Type u_2) [inst : MeasurableSpace G] [i
nst_1 : SubNegMonoid G] [MeasurableAdd G] [MeasurableNeg G],   MeasurableSub G
· 使用定理 `MeasurableAdd₂.toMeasurableAdd`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Add M] [MeasurableAdd₂ M], MeasurableAdd M
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.quasiMeasurePreserving_sub_left_of_right_invariant`：∀ {G :
 Type u_1} [inst : MeasurableSpace G] [inst_1 : AddGroup G] [MeasurableAdd₂ G] (
μ : MeasureTheory.Measure G)   [MeasureTheory.SFinite …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.integral_prod_right'`：MeasureTheory.A
EStronglyMeasurable.integral_prod_right' [SFinite ν] [NormedSpace Real E] ⦃f : α
 × β -> E⦄ (hf : AEStronglyMeasurable f (μ.pr…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prod_swap`：∀ {α : Type u_1} {β : Type
 u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory
.Measure α}   {ν : MeasureTheory.M…
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
Convolution is associative. This requires that
* all maps are a.e. strongly measurable w.r.t. one of the measures
* `f ⋆[L, ν] g` exists almost everywhere
* `‖g‖ ⋆[μ] ‖k‖` exists almost everywhere
* `‖f‖ ⋆[ν] (‖g‖ ⋆[μ] ‖k‖)` exists at `x₀`
-/
theorem convolution_assoc (hL : ∀ (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z)) {x₀ : G}
    (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g μ) (hk : AEStronglyMeasurable k μ)
    (hfg : ∀ᵐ y ∂μ, ConvolutionExistsAt f g y L ν)
    (hgk : ∀ᵐ x ∂ν, ConvolutionExistsAt (fun x => ‖g x‖) (fun x => ‖k x‖) x (mul ℝ ℝ) μ)
    (hfgk :
      ConvolutionExistsAt (fun x => ‖f x‖) ((fun x => ‖g x‖) ⋆[mul ℝ ℝ, μ] fun x => ‖k x‖) x₀
        (mul ℝ ℝ) ν) :
    ((f ⋆[L, ν] g) ⋆[L₂, μ] k) x₀ = (f ⋆[L₃, ν] g ⋆[L₄, μ] k) x₀ := by
  refine convolution_assoc' L L₂ L₃ L₄ hL hfg (hgk.mono fun x hx => hx.of_norm L₄ hg hk) ?_
  -- the following is similar to `Integrable.convolution_integrand`
  have h_meas :
    AEStronglyMeasurable (uncurry fun x y => L₃ (f y) (L₄ (g x) (k (x₀ - y - x))))
      (μ.prod ν) := by
    refine L₃.aestronglyMeasurable_comp₂ hf.comp_snd ?_
    refine L₄.aestronglyMeasurable_comp₂ hg.comp_fst ?_
    refine (hk.mono_ac ?_).comp_measurable (by fun_prop)
    refine QuasiMeasurePreserving.absolutelyContinuous ?_
    refine QuasiMeasurePreserving.prod_of_left (by fun_prop) (Eventually.of_forall fun y => ?_)
    dsimp only
    exact quasiMeasurePreserving_sub_left_of_right_invariant μ _
  have h2_meas :
      AEStronglyMeasurable (fun y => ∫ x, ‖L₃ (f y) (L₄ (g x) (k (x₀ - y - x)))‖ ∂μ) ν :=
    h_meas.prod_swap.norm.integral_prod_right'
  have h3 : map (fun z : G × G => (z.1 - z.2, z.2)) (μ.prod ν) = μ.prod ν :=
    (measurePreserving_sub_prod μ ν).map_eq
  suffices Integrable (uncurry fun x y => L₃ (f y) (L₄ (g x) (k (x₀ - y - x)))) (μ.prod ν) by
    rw [← h3] at this
    convert! this.comp_measurable (measurable_sub.prodMk measurable_snd)
    ext ⟨x, y⟩
    simp +unfoldPartialApp only [uncurry, Function.comp_apply,
      sub_sub_sub_cancel_right]
  simp_rw [integrable_prod_iff' h_meas]
  refine ⟨((quasiMeasurePreserving_sub_left_of_right_invariant ν x₀).ae hgk).mono fun t ht =>
    (L₃ (f t)).integrable_comp <| ht.of_norm L₄ hg hk, ?_⟩
  refine (hfgk.const_mul (‖L₃‖ * ‖L₄‖)).mono' h2_meas
    (((quasiMeasurePreserving_sub_left_of_right_invariant ν x₀).ae hgk).mono fun t ht => ?_)
  simp_rw [convolution_def, mul_apply', mul_mul_mul_comm ‖L₃‖ ‖L₄‖, ← integral_const_mul]
  rw [Real.norm_of_nonneg (by positivity)]
  refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
    ((ht.const_mul _).const_mul _) (Eventually.of_forall fun s => ?_)
  simp only [← mul_assoc ‖L₄‖]
  apply_rules [ContinuousLinearMap.le_of_opNorm₂_le_of_le, le_rfl]

end Assoc

/-
**MeasureTheory.convolution_precompR_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：convolution_precompR_apply [NormedAddCommGroup G] [BorelSpace G] {g : G ->
 E'' ->L[𝕜] E'} (hf : LocallyIntegrable f μ) (hcg : HasCompactSupport g) (hg : C
ontinuous g) (x₀ : G) (x : E'') : (f ⋆[L.precompR E'', μ] g) x₀ x = (f ⋆[L, μ] f
un a => g a x) x₀
参数：hf : LocallyIntegrable f μ；hcg : HasCompactSupport g；hg : Continuous g；x₀ : G
；x : E''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `HasCompactSupport.convolutionExists_right`：∀ {𝕜 : Type u𝕜} {G : Type uG}
 {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E]   [in
st_1 : NormedAddCommGroup E'] […
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.integral_apply`：integral_apply {H : Type*} [NormedAd
dCommGroup H] [NormedSpace 𝕜 H] {φ : X -> H ->L[𝕜] E} (φ_int : Integrable φ μ) (
v : H) : (∫ x, φ x ∂μ) v…
-/
theorem convolution_precompR_apply [NormedAddCommGroup G] [BorelSpace G]
    {g : G → E'' →L[𝕜] E'} (hf : LocallyIntegrable f μ)
    (hcg : HasCompactSupport g) (hg : Continuous g) (x₀ : G) (x : E'') :
    (f ⋆[L.precompR E'', μ] g) x₀ x = (f ⋆[L, μ] fun a => g a x) x₀ := by
  have := hcg.convolutionExists_right (L.precompR E'' :) hf hg x₀
  simp_rw [convolution_def, ContinuousLinearMap.integral_apply this]
  rfl

end RCLike

section Nonneg

variable [NormedSpace ℝ E] [NormedSpace ℝ E'] [NormedSpace ℝ F]

/-- The forward convolution of two functions `f` and `g` on `ℝ`, with respect to a continuous
bilinear map `L` and measure `ν`. It is defined to be the function mapping `x` to
`∫ t in 0..x, L (f t) (g (x - t)) ∂ν` if `0 < x`, and 0 otherwise. -/
/-
**MeasureTheory.posConvolution** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：posConvolution (f : Real -> E) (g : Real -> E') (L : E ->L[Real] E' ->L[Re
al] F) (ν : Measure Real
参数：f : Real -> E；g : Real -> E'；L : E ->L[Real] E' ->L[Real] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forward convolution of two functions `f` and `g` on `ℝ`, with respect to a c
ontinuous
bilinear map `L` and measure `ν`. It is defined to be the function mapping `x` t
o
`∫ t in 0..x, L (f t) (g (x - t)) ∂ν` if `0 < x`, and 0 otherwise.
-/
noncomputable def posConvolution (f : ℝ → E) (g : ℝ → E') (L : E →L[ℝ] E' →L[ℝ] F)
    (ν : Measure ℝ := by volume_tac) : ℝ → F :=
  indicator (Ioi (0 : ℝ)) fun x => ∫ t in 0..x, L (f t) (g (x - t)) ∂ν
/-
**MeasureTheory.posConvolution_eq_convolution_indicator** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：posConvolution_eq_convolution_indicator (f : Real -> E) (g : Real -> E') (
L : E ->L[Real] E' ->L[Real] F) (ν : Measure Real
参数：f : Real -> E；g : Real -> E'；L : E ->L[Real] E' ->L[Real] F。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.convolution.eq_1`：∀ {𝕜 : Type u𝕜} {G : Type uG} {E : Type 
uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E]   [inst_1 : Norm
edAddCommGroup E'] […
· 使用定理 `MeasureTheory.posConvolution.eq_1`：∀ {E : Type uE} {E' : Type uE'} {F : 
Type uF} [inst : NormedAddCommGroup E] [inst_1 : NormedAddCommGroup E']   [inst_
2 : NormedAddCommGroup …
· 使用定理 `Set.indicator.eq_1`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s :
 Set α) (f : α → M) (x : α),   s.indicator f x = if x ∈ s then f x else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.integral_Ioc_eq_integral_Ioo`：integral_Ioc_eq_integral_Ioo
 : ∫ t in Ioc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `Set.notMem_Ioo_of_le`：notMem_Ioo_of_le (ha : c <= a) : c ∉ Ioo a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.notMem_Ioi`：notMem_Ioi : c ∉ Ioi a ↔ c <= a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
（共 55 条，此处仅展示前 30 条）
-/
theorem posConvolution_eq_convolution_indicator (f : ℝ → E) (g : ℝ → E') (L : E →L[ℝ] E' →L[ℝ] F)
    (ν : Measure ℝ := by volume_tac) [NullSingletonClass ν] :
    posConvolution f g L ν = convolution (indicator (Ioi 0) f) (indicator (Ioi 0) g) L ν := by
  ext1 x
  rw [convolution, posConvolution, indicator]
  split_ifs with h
  · rw [intervalIntegral.integral_of_le (le_of_lt h), integral_Ioc_eq_integral_Ioo, ←
      integral_indicator (measurableSet_Ioo : MeasurableSet (Ioo 0 x))]
    congr 1 with t : 1
    have : t ≤ 0 ∨ t ∈ Ioo 0 x ∨ x ≤ t := by
      rcases le_or_gt t 0 with (h | h)
      · exact Or.inl h
      · rcases lt_or_ge t x with (h' | h')
        exacts [Or.inr (Or.inl ⟨h, h'⟩), Or.inr (Or.inr h')]
    rcases this with (ht | ht | ht)
    · rw [indicator_of_notMem (notMem_Ioo_of_le ht), indicator_of_notMem (notMem_Ioi.mpr ht),
        map_zero, zero_apply]
    · rw [indicator_of_mem ht, indicator_of_mem (mem_Ioi.mpr ht.1),
          indicator_of_mem (mem_Ioi.mpr <| sub_pos.mpr ht.2)]
    · rw [indicator_of_notMem (notMem_Ioo_of_ge ht),
          indicator_of_notMem (notMem_Ioi.mpr (sub_nonpos_of_le ht)), map_zero]
  · convert! (integral_zero ℝ F).symm with t
    by_cases ht : 0 < t
    · rw [indicator_of_notMem (_ : x - t ∉ Ioi 0), map_zero]
      rw [notMem_Ioi] at h ⊢
      exact sub_nonpos.mpr (h.trans ht.le)
    · rw [indicator_of_notMem (mem_Ioi.not.mpr ht), map_zero, zero_apply]
/-
**MeasureTheory.integrable_posConvolution** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integrable_posConvolution {f : Real -> E} {g : Real -> E'} {μ ν : Measure 
Real} [SFinite μ] [SFinite ν] [IsAddRightInvariant μ] [NullSingletonClass ν] (hf
 : IntegrableOn f (Ioi 0) ν) (hg : IntegrableOn g (Ioi 0) μ) (L : E ->L[Real] E'
 ->L[Real] F) : Integrable (posConvolution f g L ν) μ
参数：hf : IntegrableOn f (Ioi 0) ν；hg : IntegrableOn g (Ioi 0) μ；L : E ->L[Real] E
' ->L[Real] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.posConvolution_eq_convolution_indicator`：posConvolution_eq
_convolution_indicator (f : Real -> E) (g : Real -> E') (L : E ->L[Real] E' ->L[
Real] F) (ν : Measure Real
· 使用定理 `MeasureTheory.Integrable.integral_prod_left`：∀ {α : Type u_1} {β : Type 
u_2} {E : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {μ
 : MeasureTheory.Measure α} {ν : …
· 使用定理 `MeasureTheory.Integrable.convolution_integrand`：∀ {𝕜 : Type u𝕜} {G : Typ
e uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E] 
  [inst_1 : NormedAddCommGroup E'] […
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem integrable_posConvolution {f : ℝ → E} {g : ℝ → E'} {μ ν : Measure ℝ} [SFinite μ]
    [SFinite ν] [IsAddRightInvariant μ] [NullSingletonClass ν] (hf : IntegrableOn f (Ioi 0) ν)
    (hg : IntegrableOn g (Ioi 0) μ) (L : E →L[ℝ] E' →L[ℝ] F) :
    Integrable (posConvolution f g L ν) μ := by
  rw [← integrable_indicator_iff (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] at hf hg
  rw [posConvolution_eq_convolution_indicator f g L ν]
  exact (hf.convolution_integrand L hg).integral_prod_left

/-- The integral over `Ioi 0` of a forward convolution of two functions is equal to the product
of their integrals over this set. (Compare `integral_convolution` for the two-sided convolution.) -/
/-
**MeasureTheory.integral_posConvolution** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：integral_posConvolution [CompleteSpace E] [CompleteSpace E'] [CompleteSpac
e F] {μ ν : Measure Real} [SFinite μ] [SFinite ν] [IsAddRightInvariant μ] [NullS
ingletonClass ν] {f : Real -> E} {g : Real -> E'} (hf : IntegrableOn f (Ioi 0) ν
) (hg : IntegrableOn g (Ioi 0) μ) (L : E ->L[Real] E' ->L[Real] F) : ∫ x : Real 
in Ioi 0, ∫ t : Real in 0..x, L (f t) (g (x - t)) ∂ν ∂μ = L (∫ x : Real in Ioi 0
, f x ∂ν) (∫ x : Real in Ioi 0, g x ∂μ)
参数：hf : IntegrableOn f (Ioi 0) ν；hg : IntegrableOn g (Ioi 0) μ；L : E ->L[Real] E
' ->L[Real] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.posConvolution_eq_convolution_indicator`：posConvolution_eq
_convolution_indicator (f : Real -> E) (g : Real -> E') (L : E ->L[Real] E' ->L[
Real] F) (ν : Measure Real
· 使用定理 `MeasureTheory.integral_convolution`：integral_convolution [MeasurableAdd₂
 G] [MeasurableNeg G] [NormedSpace Real E] [NormedSpace Real E'] [CompleteSpace 
E] [CompleteSpace E'] (h…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ

--- 原说明 ---
The integral over `Ioi 0` of a forward convolution of two functions is equal to 
the product
of their integrals over this set. (Compare `integral_convolution` for the two-si
ded convolution.)
-/
theorem integral_posConvolution [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    {μ ν : Measure ℝ}
    [SFinite μ] [SFinite ν] [IsAddRightInvariant μ] [NullSingletonClass ν] {f : ℝ → E} {g : ℝ → E'}
    (hf : IntegrableOn f (Ioi 0) ν) (hg : IntegrableOn g (Ioi 0) μ) (L : E →L[ℝ] E' →L[ℝ] F) :
    ∫ x : ℝ in Ioi 0, ∫ t : ℝ in 0..x, L (f t) (g (x - t)) ∂ν ∂μ =
      L (∫ x : ℝ in Ioi 0, f x ∂ν) (∫ x : ℝ in Ioi 0, g x ∂μ) := by
  rw [← integrable_indicator_iff measurableSet_Ioi] at hf hg
  simp_rw [← integral_indicator measurableSet_Ioi]
  convert! integral_convolution L hf hg using 4 with x
  apply posConvolution_eq_convolution_indicator

end Nonneg
end MeasureTheory

