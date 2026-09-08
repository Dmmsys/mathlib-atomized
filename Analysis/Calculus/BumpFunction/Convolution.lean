/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Covering.Differentiation
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Convolution with a bump function

In this file we prove lemmas about convolutions `(φ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x₀`,
where `φ : ContDiffBump 0` is a smooth bump function.

We prove that this convolution is equal to `g x₀`
if `g` is a constant on `Metric.ball x₀ φ.rOut`.
We also provide estimates in the case if `g x` is close to `g x₀` on this ball.

## Main results

- `ContDiffBump.convolution_tendsto_right_of_continuous`:
  Let `g` be a continuous function; let `φ i` be a family of `ContDiffBump 0` functions with.
  If `(φ i).rOut` tends to zero along a filter `l`,
  then `((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) x₀` tends to `g x₀` along the same filter.
- `ContDiffBump.convolution_tendsto_right`: generalization of the above lemma.
- `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`: let `g` be a locally
  integrable function. Then the convolution of `g` with a family of bump functions with
  support tending to `0` converges almost everywhere to `g`.

## Keywords

convolution, smooth function, bump function
-/

public section

universe uG uE'

open ContinuousLinearMap Metric MeasureTheory Filter Function Measure Set
open scoped Convolution Topology

namespace ContDiffBump

variable {G : Type uG} {E' : Type uE'} [NormedAddCommGroup E'] {g : G → E'} [MeasurableSpace G]
  {μ : MeasureTheory.Measure G} [NormedSpace ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [CompleteSpace E'] {φ : ContDiffBump (0 : G)} {x₀ : G}

/-- If `φ` is a bump function, compute `(φ ⋆ g) x₀`
if `g` is constant on `Metric.ball x₀ φ.rOut`. -/
/-
**ContDiffBump.convolution_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：convolution_eq_right [HasContDiffBump G] {x₀ : G} (hg : forall x in ball x
₀ φ.rOut, g x = g x₀) : (φ ⋆[lsmul Real Real, μ] g : G -> E') x₀ = integral μ φ 
• g x₀
参数：hg : forall x in ball x₀ φ.rOut, g x = g x₀。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.convolution_eq_right'`：convolution_eq_right' {x₀ : G} {R :
 Real} (hf : support f subseteq ball (0 : G) R) (hg : forall x in ball x₀ R, g x
 = g x₀) : (f ⋆[L, μ] g) …
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `ContDiffBump.support_eq`：support_eq : Function.support f = Metric.ball c
 f.rOut
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `integral_smul_const`：integral_smul_const {𝕜 : Type*} [RCLike 𝕜] [NormedS
pace 𝕜 E] [CompleteSpace E] (f : X -> 𝕜) (c : E) : ∫ x, f x • c ∂μ = (∫ x, f x ∂
μ) • c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `φ` is a bump function, compute `(φ ⋆ g) x₀`
if `g` is constant on `Metric.ball x₀ φ.rOut`.
-/
theorem convolution_eq_right [HasContDiffBump G] {x₀ : G} (hg : ∀ x ∈ ball x₀ φ.rOut, g x = g x₀) :
    (φ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = integral μ φ • g x₀ := by
  simp_rw [convolution_eq_right' _ φ.support_eq.subset hg, lsmul_apply, integral_smul_const]

variable [BorelSpace G] [FiniteDimensional ℝ G]

/-- If `φ` is a normed bump function, compute `φ ⋆ g`
if `g` is constant on `Metric.ball x₀ φ.rOut`. -/
/-
**ContDiffBump.normed_convolution_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBu
mp`。
形式化陈述：normed_convolution_eq_right [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure
] {x₀ : G} (hg : forall x in ball x₀ φ.rOut, g x = g x₀) : (φ.normed μ ⋆[lsmul R
eal Real, μ] g : G -> E') x₀ = g x₀
参数：hg : forall x in ball x₀ φ.rOut, g x = g x₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsContDiffBumpBase.instHasContDiffBumpOfFiniteDimensionalReal`：∀ {E 
: Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDime
nsional ℝ E], HasContDiffBump E
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
· 使用定理 `MeasureTheory.convolution_eq_right'`：convolution_eq_right' {x₀ : G} {R :
 Real} (hf : support f subseteq ball (0 : G) R) (hg : forall x in ball x₀ R, g x
 = g x₀) : (f ⋆[L, μ] g) …
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `ContDiffBump.support_normed_eq`：support_normed_eq : Function.support (f.
normed μ) = Metric.ball c f.rOut
· 使用定理 `ContDiffBump.integral_normed_smul`：integral_normed_smul {X} [NormedAddCo
mmGroup X] [NormedSpace Real X] [CompleteSpace X] (z : X) : ∫ x, f.normed μ x • 
z ∂μ = z

--- 原说明 ---
If `φ` is a normed bump function, compute `φ ⋆ g`
if `g` is constant on `Metric.ball x₀ φ.rOut`.
-/
theorem normed_convolution_eq_right [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] {x₀ : G}
    (hg : ∀ x ∈ ball x₀ φ.rOut, g x = g x₀) :
    (φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = g x₀ := by
  rw [convolution_eq_right' _ φ.support_normed_eq.subset hg]
  exact integral_normed_smul φ μ (g x₀)

variable [μ.IsAddHaarMeasure]

/-- If `φ` is a normed bump function, approximate `(φ ⋆ g) x₀`
if `g` is near `g x₀` on a ball with radius `φ.rOut` around `x₀`. -/
/-
**ContDiffBump.dist_normed_convolution_le** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBum
p`。
形式化陈述：dist_normed_convolution_le {x₀ : G} {ε : Real} (hmg : AEStronglyMeasurable
 g μ) (hg : forall x in ball x₀ φ.rOut, dist (g x) (g x₀) <= ε) : dist ((φ.norme
d μ ⋆[lsmul Real Real, μ] g : G -> E') x₀) (g x₀) <= ε
参数：hmg : AEStronglyMeasurable g μ；hg : forall x in ball x₀ φ.rOut, dist (g x) (g
 x₀) <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dist_convolution_le`：dist_convolution_le {f : G -> Real} {
x₀ : G} {R ε : Real} {z₀ : E'} (hε : 0 <= ε) (hf : support f subseteq ball (0 : 
G) R) (hnf : forall x, …
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `ExistsContDiffBumpBase.instHasContDiffBumpOfFiniteDimensionalReal`：∀ {E 
: Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDime
nsional ℝ E], HasContDiffBump E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
· 使用定理 `ContDiffBump.rOut_pos`：rOut_pos {c : E} (f : ContDiffBump c) : 0 < f.rOu
t
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `ContDiffBump.support_normed_eq`：support_normed_eq : Function.support (f.
normed μ) = Metric.ball c f.rOut
· 使用定理 `MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`：∀ {α 
: Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace α]   [WeaklyLocallyCompactSpace α] [Measure…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u
_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace 
G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `ContDiffBump.nonneg_normed`：nonneg_normed (x : E) : 0 <= f.normed μ x
· 使用定理 `ContDiffBump.integral_normed`：integral_normed : ∫ x, f.normed μ x ∂μ = 1

--- 原说明 ---
If `φ` is a normed bump function, approximate `(φ ⋆ g) x₀`
if `g` is near `g x₀` on a ball with radius `φ.rOut` around `x₀`.
-/
theorem dist_normed_convolution_le {x₀ : G} {ε : ℝ} (hmg : AEStronglyMeasurable g μ)
    (hg : ∀ x ∈ ball x₀ φ.rOut, dist (g x) (g x₀) ≤ ε) :
    dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) (g x₀) ≤ ε :=
  dist_convolution_le (by simp_rw [← dist_self (g x₀), hg x₀ (mem_ball_self φ.rOut_pos)])
    φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed hmg hg

/-- `(φ i ⋆ g i) (k i)` tends to `z₀` as `i` tends to some filter `l` if
* `φ` is a sequence of normed bump functions
  such that `(φ i).rOut` tends to `0` as `i` tends to `l`;
* `g i` is `μ`-a.e. strongly measurable as `i` tends to `l`;
* `g i x` tends to `z₀` as `(i, x)` tends to `l ×ˢ 𝓝 x₀`;
* `k i` tends to `x₀`. -/
nonrec theorem convolution_tendsto_right {ι} {φ : ι → ContDiffBump (0 : G)} {g : ι → G → E'}
    {k : ι → G} {x₀ : G} {z₀ : E'} {l : Filter ι} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hig : ∀ᶠ i in l, AEStronglyMeasurable (g i) μ) (hcg : Tendsto (uncurry g) (l ×ˢ 𝓝 x₀) (𝓝 z₀))
    (hk : Tendsto k l (𝓝 x₀)) :
    Tendsto (fun i => ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] g i) (k i)) l (𝓝 z₀) :=
  convolution_tendsto_right (Eventually.of_forall fun i => (φ i).nonneg_normed)
    (Eventually.of_forall fun i => (φ i).integral_normed) (tendsto_support_normed_smallSets hφ) hig
    hcg hk

/-- Special case of `ContDiffBump.convolution_tendsto_right` where `g` is continuous,
  and the limit is taken only in the first function. -/
/-
**ContDiffBump.convolution_tendsto_right_of_continuous** 是 Mathlib 中的一个定理，位于命名空间
 `ContDiffBump`。
形式化陈述：convolution_tendsto_right_of_continuous {ι} {φ : ι -> ContDiffBump (0 : G)
} {l : Filter ι} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (hg : Continuous g
) (x₀ : G) : Tendsto (fun i => ((φ i).normed μ ⋆[lsmul Real Real, μ] g) x₀) l (𝓝
 (g x₀))
参数：0 : G；hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)；hg : Continuous g；x₀ : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffBump.convolution_tendsto_right`：∀ {G : Type uG} {E' : Type uE'} 
[inst : NormedAddCommGroup E'] [inst_1 : MeasurableSpace G]   {μ : MeasureTheory
.Measure G} [inst_2 : Normed…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)

--- 原说明 ---
Special case of `ContDiffBump.convolution_tendsto_right` where `g` is continuous
,
  and the limit is taken only in the first function.
-/
theorem convolution_tendsto_right_of_continuous {ι} {φ : ι → ContDiffBump (0 : G)} {l : Filter ι}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (hg : Continuous g) (x₀ : G) :
    Tendsto (fun i => ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) x₀) l (𝓝 (g x₀)) :=
  convolution_tendsto_right hφ (Eventually.of_forall fun _ => hg.aestronglyMeasurable)
    ((hg.tendsto x₀).comp tendsto_snd) tendsto_const_nhds

/-- If a function `g` is locally integrable, then the convolution `φ i * g` converges almost
everywhere to `g` if `φ i` is a sequence of bump functions with support tending to `0`, provided
that the ratio between the inner and outer radii of `φ i` remains bounded. -/
/-
**ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable** 是 Mathlib 中的一
个定理，位于命名空间 `ContDiffBump`。
形式化陈述：ae_convolution_tendsto_right_of_locallyIntegrable {ι} {φ : ι -> ContDiffBu
mp (0 : G)} {l : Filter ι} {K : Real} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0
)) (h'φ : forallᶠ i in l, (φ i).rOut <= K * (φ i).rIn) (hg : LocallyIntegrable g
 μ) : forallᵐ x₀ ∂μ, Tendsto (fun i => ((φ i).normed μ ⋆[lsmul Real Real, μ] g) 
x₀) l (𝓝 (g x₀))
参数：0 : G；hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)；h'φ : forallᶠ i in l, (φ i).
rOut <= K * (φ i).rIn；hg : LocallyIntegrable g μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Besicovitch.instHasBesicovitchCovering`：∀ (E : Type u_1) [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E],   HasBesicovi
tchCovering E
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `ExistsContDiffBumpBase.instHasContDiffBumpOfFiniteDimensionalReal`：∀ {E 
: Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDime
nsional ℝ E], HasContDiffBump E
· 使用定理 `VitaliFamily.ae_tendsto_average_norm_sub`：ae_tendsto_average_norm_sub {f
 : α -> E} (hf : LocallyIntegrable f μ) : forallᵐ x ∂μ, Tendsto (fun a => ⨍ y in
 a, ‖f y - f x‖ ∂μ) (v.filterA…
· 使用定理 `MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`：∀ {α 
: Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace α]   [WeaklyLocallyCompactSpace α] [Measure…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.convolution_eq_swap`：convolution_eq_swap : (f ⋆[L, μ] g) x
 = ∫ t, L (f (x - t)) (g t) ∂μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular`：∀
 {G : Type u_1} [inst : AddCommGroup G] [inst_1 : TopologicalSpace G] [IsTopolog
icalAddGroup G]   [inst_3 : MeasurableSpace G] [BorelSpace …
· 使用定理 `MeasureTheory.Measure.instInnerRegularOfPseudoMetrizableSpaceOfSigmaComp
actSpaceOfBorelSpaceOfSigmaFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] 
[TopologicalSpace.PseudoMetrizableSpace X] [SigmaCompactSpace X]   [inst_3 : Mea
surableSpace X]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
If a function `g` is locally integrable, then the convolution `φ i * g` converge
s almost
everywhere to `g` if `φ i` is a sequence of bump functions with support tending 
to `0`, provided
that the ratio between the inner and outer radii of `φ i` remains bounded.
-/
theorem ae_convolution_tendsto_right_of_locallyIntegrable
    {ι} {φ : ι → ContDiffBump (0 : G)} {l : Filter ι} {K : ℝ}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0))
    (h'φ : ∀ᶠ i in l, (φ i).rOut ≤ K * (φ i).rIn) (hg : LocallyIntegrable g μ) : ∀ᵐ x₀ ∂μ,
    Tendsto (fun i ↦ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] g) x₀) l (𝓝 (g x₀)) := by
  -- By Lebesgue differentiation theorem, the average of `g` on a small ball converges
  -- almost everywhere to the value of `g` as the radius shrinks to zero.
  -- We will see that this set of points satisfies the desired conclusion.
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_average_norm_sub hg] with x₀ h₀
  simp only [convolution_eq_swap, lsmul_apply]
  have hφ' : Tendsto (fun i ↦ (φ i).rOut) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hφ, Eventually.of_forall (fun i ↦ (φ i).rOut_pos)⟩
  have := (h₀.comp (Besicovitch.tendsto_filterAt μ x₀)).comp hφ'
  apply tendsto_integral_smul_of_tendsto_average_norm_sub (K ^ (Module.finrank ℝ G)) this
  · filter_upwards with i using
      hg.integrableOn_isCompact (isCompact_closedBall _ _)
  · apply tendsto_const_nhds.congr (fun i ↦ ?_)
    rw [← integral_neg_eq_self]
    simp only [sub_neg_eq_add, integral_add_left_eq_self, integral_normed]
  · filter_upwards with i
    change support ((ContDiffBump.normed (φ i) μ) ∘ (fun y ↦ x₀ - y)) ⊆ closedBall x₀ (φ i).rOut
    simp only [support_comp_eq_preimage, support_normed_eq]
    intro x hx
    simp only [mem_preimage, mem_ball, dist_zero_right] at hx
    simpa [dist_eq_norm_sub'] using hx.le
  · filter_upwards [h'φ] with i hi x
    rw [abs_of_nonneg (nonneg_normed _ _), addHaar_real_closedBall_center]
    exact (φ i).normed_le_div_measure_closedBall_rOut _ _ hi _

end ContDiffBump

