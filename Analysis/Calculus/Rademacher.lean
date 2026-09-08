/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Measurable
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-!
# Rademacher's theorem: a Lipschitz function is differentiable almost everywhere

This file proves Rademacher's theorem: a Lipschitz function between finite-dimensional real vector
spaces is differentiable almost everywhere with respect to the Lebesgue measure. This is the content
of `LipschitzWith.ae_differentiableAt`. Versions for functions which are Lipschitz on sets are also
given (see `LipschitzOnWith.ae_differentiableWithinAt`).

## Implementation

There are many proofs of Rademacher's theorem. We follow the one by Morrey, which is not the most
elementary but maybe the most elegant once necessary prerequisites are set up.
* Step 0: without loss of generality, one may assume that `f` is real-valued.
* Step 1: Since a one-dimensional Lipschitz function has bounded variation, it is differentiable
  almost everywhere. With a Fubini argument, it follows that given any vector `v` then `f` is ae
  differentiable in the direction of `v`. See `LipschitzWith.ae_lineDifferentiableAt`.
* Step 2: the line derivative `LineDeriv ℝ f x v` is ae linear in `v`. Morrey proves this by a
  duality argument, integrating against a smooth compactly supported function `g`, passing the
  derivative to `g` by integration by parts, and using the linearity of the derivative of `g`.
  See `LipschitzWith.ae_lineDeriv_sum_eq`.
* Step 3: consider a countable dense set `s` of directions. Almost everywhere, the function `f`
  is line-differentiable in all these directions and the line derivative is linear. Approximating
  any direction by a direction in `s` and using the fact that `f` is Lipschitz to control the error,
  it follows that `f` is Fréchet-differentiable at these points.
  See `LipschitzWith.hasFDerivAt_of_hasLineDerivAt_of_closure`.

## References

* [Pertti Mattila, Geometry of sets and measures in Euclidean spaces, Theorem 7.3][Federer1996]
-/

public section

open Filter MeasureTheory Measure Module Metric Set Asymptotics

open scoped NNReal ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {C D : ℝ≥0} {f g : E → ℝ} {s : Set E}
  {μ : Measure E}

namespace LipschitzWith

/-!
### Step 1: A Lipschitz function is ae differentiable in any given direction

This follows from the one-dimensional result that a Lipschitz function on `ℝ` has bounded
variation, and is therefore ae differentiable, together with a Fubini argument.
-/


/-
**LipschitzWith.memLp_lineDeriv** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：memLp_lineDeriv (hf : LipschitzWith C f) (v : E) : MemLp (fun x => lineDer
iv Real f x v) ∞ μ
参数：hf : LipschitzWith C f；v : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.memLp_top_of_bound`：memLp_top_of_bound {f : α -> E} (hf : 
AEStronglyMeasurable f μ) (C : Real) (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : MemLp f 
∞ μ
· 使用定理 `aestronglyMeasurable_lineDeriv`：aestronglyMeasurable_lineDeriv [SecondCo
untableTopologyEither E F] (hf : Continuous f) (μ : Measure E) : AEStronglyMeasu
rable (fun x => line…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `norm_lineDeriv_le_of_lipschitz`：norm_lineDeriv_le_of_lipschitz {f : E ->
 F} {x₀ : E} {C : Real>=0} (hlip : LipschitzWith C f) : ‖lineDeriv 𝕜 f x₀ v‖ <= 
C * ‖v‖

--- 原说明 ---
### Step 1: A Lipschitz function is ae differentiable in any given direction

This follows from the one-dimensional result that a Lipschitz function on `ℝ` ha
s bounded
variation, and is therefore ae differentiable, together with a Fubini argument.
-/
theorem memLp_lineDeriv (hf : LipschitzWith C f) (v : E) :
    MemLp (fun x ↦ lineDeriv ℝ f x v) ∞ μ :=
  memLp_top_of_bound (aestronglyMeasurable_lineDeriv hf.continuous μ)
    (C * ‖v‖) (.of_forall fun _x ↦ norm_lineDeriv_le_of_lipschitz ℝ hf)

variable [FiniteDimensional ℝ E] [IsAddHaarMeasure μ]
/-
**LipschitzWith.ae_lineDifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith
`。
形式化陈述：ae_lineDifferentiableAt (hf : LipschitzWith C f) (v : E) : forallᵐ p ∂μ, L
ineDifferentiableAt Real f p v
参数：hf : LipschitzWith C f；v : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LipschitzWith.ae_differentiableAt_real`：LipschitzWith.ae_differentiableA
t_real {C : Real>=0} {f : Real -> V} (h : LipschitzWith C f) : forallᵐ x, Differ
entiableAt Real f x
· 使用定理 `LipschitzWith.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpac
e γ] {Kf…
· 使用定理 `LipschitzWith.add`：∀ {α : Type u_4} {E : Type u_5} [inst : SeminormedAdd
CommGroup E] [inst_1 : PseudoEMetricSpace α] {Kf Kg : NNReal}   {f g : α → E}, L
ipschit…
· 使用定理 `LipschitzWith.const`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] (b : β),   LipschitzWith 0 fun x => b
· 使用定理 `ContinuousLinearMap.lipschitz`：lipschitz (f : E ->SL[σ₁₂] F) : Lipschitz
With ‖f‖₊ f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `DifferentiableAt.const_add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type u_…
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DifferentiableAt.comp`：DifferentiableAt.comp {g : F -> G} (hg : Differen
tiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x
· 使用引理 `MeasureTheory.ae_mem_of_ae_add_linearMap_mem`：ae_mem_of_ae_add_linearMap
_mem [LocallyCompactSpace F] {s : Set F} (hs : MeasurableSet s) (h : forall y, f
orallᵐ x ∂μ, y + L x in s) : foral…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `measurableSet_lineDifferentiableAt`：measurableSet_lineDifferentiableAt (
hf : Continuous f) : MeasurableSet {x : E | LineDifferentiableAt 𝕜 f x v}
（共 32 条，此处仅展示前 30 条）
-/
theorem ae_lineDifferentiableAt
    (hf : LipschitzWith C f) (v : E) :
    ∀ᵐ p ∂μ, LineDifferentiableAt ℝ f p v := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  suffices A : ∀ p, ∀ᵐ (t : ℝ) ∂volume, LineDifferentiableAt ℝ f (p + t • v) v from
    ae_mem_of_ae_add_linearMap_mem L.toLinearMap volume μ
      (measurableSet_lineDifferentiableAt hf.continuous) A
  intro p
  have : ∀ᵐ (s : ℝ), DifferentiableAt ℝ (fun t ↦ f (p + t • v)) s :=
    (hf.comp ((LipschitzWith.const p).add L.lipschitz)).ae_differentiableAt_real
  filter_upwards [this] with s hs
  have h's : DifferentiableAt ℝ (fun t ↦ f (p + t • v)) (s + 0) := by simpa using hs
  have : DifferentiableAt ℝ (fun t ↦ s + t) 0 := differentiableAt_id.const_add _
  simp only [LineDifferentiableAt]
  convert! h's.comp 0 this with _ t
  simp only [add_assoc, Function.comp_apply, add_smul]
/-
**LipschitzWith.locallyIntegrable_lineDeriv** 是 Mathlib 中的一个定理，位于命名空间 `Lipschitz
With`。
形式化陈述：locallyIntegrable_lineDeriv (hf : LipschitzWith C f) (v : E) : LocallyInte
grable (fun x => lineDeriv Real f x v) μ
参数：hf : LipschitzWith C f；v : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.locallyIntegrable`：∀ {X : Type u_1} {ε : Type u_3} [
inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : TopologicalSpa
ce ε]   [inst_3 : Continuou…
· 使用定理 `MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`：∀ {α 
: Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace α]   [WeaklyLocallyCompactSpace α] [Measure…
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `LipschitzWith.memLp_lineDeriv`：memLp_lineDeriv (hf : LipschitzWith C f) 
(v : E) : MemLp (fun x => lineDeriv Real f x v) ∞ μ
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem locallyIntegrable_lineDeriv (hf : LipschitzWith C f) (v : E) :
    LocallyIntegrable (fun x ↦ lineDeriv ℝ f x v) μ :=
  (hf.memLp_lineDeriv v).locallyIntegrable le_top

/-!
### Step 2: the ae line derivative is linear

Surprisingly, this is the hardest step. We prove it using an elegant but slightly sophisticated
argument by Morrey, with a distributional flavor: we integrate against a smooth function, and push
the derivative to the smooth function by integration by parts. As the derivative of a smooth
function is linear, this gives the result.
-/

/-
**LipschitzWith.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul** 是 Mat
hlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul (hf : LipschitzWi
th C f) (hg : Integrable g μ) (v : E) : Tendsto (fun (t : Real) => ∫ x, (t⁻¹ • (
f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0) (𝓝 (∫ x, lineDeriv Real f x v * g x ∂μ)
)
参数：hf : LipschitzWith C f；hg : Integrable g μ；v : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`：tendsto_
integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGenera
ted] {F : ι -> α -> G} {f : α -> G} (bound : α -> Re…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_smul`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {𝕜 : Type u_5} [inst_…
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `AEMeasurable.add_const`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurab
leSpace M] [inst_1 : Add M] {m : MeasurableSpace α} {f : α → M}   {μ : MeasureTh
eory.Measure…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `aemeasurable_id'`：aemeasurable_id' : AEMeasurable (fun x => x) μ
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
（共 97 条，此处仅展示前 30 条）

--- 原说明 ---
### Step 2: the ae line derivative is linear

Surprisingly, this is the hardest step. We prove it using an elegant but slightl
y sophisticated
argument by Morrey, with a distributional flavor: we integrate against a smooth 
function, and push
the derivative to the smooth function by integration by parts. As the derivative
 of a smooth
function is linear, this gives the result.
-/
theorem integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul
    (hf : LipschitzWith C f) (hg : Integrable g μ) (v : E) :
    Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, lineDeriv ℝ f x v * g x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ (C * ‖v‖) * ‖g x‖)
  · filter_upwards with t
    apply AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
    apply aestronglyMeasurable_const.fun_smul
    apply AEStronglyMeasurable.sub _ hf.continuous.measurable.aestronglyMeasurable
    apply AEMeasurable.aestronglyMeasurable
    exact hf.continuous.measurable.comp_aemeasurable' (aemeasurable_id'.add_const _)
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    filter_upwards with x
    calc ‖t⁻¹ • (f (x + t • v) - f x) * g x‖
      = (t⁻¹ * ‖f (x + t • v) - f x‖) * ‖g x‖ := by simp [norm_mul, ht.le]
    _ ≤ (t⁻¹ * (C * ‖(x + t • v) - x‖)) * ‖g x‖ := by
      gcongr; exact LipschitzWith.norm_sub_le hf (x + t • v) x
    _ = (C * ‖v‖) * ‖g x‖ := by simp [field, norm_smul, abs_of_nonneg ht.le]
  · exact hg.norm.const_mul _
  · filter_upwards [hf.ae_lineDifferentiableAt v] with x hx
    exact hx.hasLineDerivAt.tendsto_slope_zero_right.mul tendsto_const_nhds
/-
**LipschitzWith.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'** 是 Ma
thlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul' (hf : LipschitzW
ith C f) (h'f : HasCompactSupport f) (hg : Continuous g) (v : E) : Tendsto (fun 
(t : Real) => ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0) (𝓝 (∫ x, lin
eDeriv Real f x v * g x ∂μ))
参数：hf : LipschitzWith C f；h'f : HasCompactSupport f；hg : Continuous g；v : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.cthickening`：∀ {α : Type u_2} [inst : PseudoMetricSpace α] [Pr
operSpace α] {s : Set α},   IsCompact s → ∀ {r : ℝ}, IsCompact (Metric.cthickeni
ng r s)
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`：tendsto_
integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGenera
ted] {F : ι -> α -> G} {f : α -> G} (bound : α -> Re…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_smul`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {𝕜 : Type u_5} [inst_…
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.comp_aemeasurable'`：Measurable.comp_aemeasurable' [Measurable
Space δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) :
 AEMeasurable (fun …
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `AEMeasurable.add_const`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurab
leSpace M] [inst_1 : Add M] {m : MeasurableSpace α} {f : α → M}   {μ : MeasureTh
eory.Measure…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `aemeasurable_id'`：aemeasurable_id' : AEMeasurable (fun x => x) μ
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
（共 134 条，此处仅展示前 30 条）
-/
theorem integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'
    (hf : LipschitzWith C f) (h'f : HasCompactSupport f) (hg : Continuous g) (v : E) :
    Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, lineDeriv ℝ f x v * g x ∂μ)) := by
  let K := cthickening (‖v‖) (tsupport f)
  have K_compact : IsCompact K := IsCompact.cthickening h'f
  apply tendsto_integral_filter_of_dominated_convergence
      (K.indicator (fun x ↦ (C * ‖v‖) * ‖g x‖))
  · filter_upwards with t
    apply AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
    apply aestronglyMeasurable_const.fun_smul
    apply AEStronglyMeasurable.sub _ hf.continuous.measurable.aestronglyMeasurable
    apply AEMeasurable.aestronglyMeasurable
    exact hf.continuous.measurable.comp_aemeasurable' (aemeasurable_id'.add_const _)
  · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
    have t_pos : 0 < t := ht.1
    filter_upwards with x
    by_cases hx : x ∈ K
    · calc ‖t⁻¹ • (f (x + t • v) - f x) * g x‖
        = (t⁻¹ * ‖f (x + t • v) - f x‖) * ‖g x‖ := by simp [norm_mul, t_pos.le]
      _ ≤ (t⁻¹ * (C * ‖(x + t • v) - x‖)) * ‖g x‖ := by
        gcongr; exact LipschitzWith.norm_sub_le hf (x + t • v) x
      _ = (C * ‖v‖) * ‖g x‖ := by simp [field, norm_smul, abs_of_nonneg t_pos.le]
      _ = K.indicator (fun x ↦ (C * ‖v‖) * ‖g x‖) x := by rw [indicator_of_mem hx]
    · have A : f x = 0 := by
        rw [← Function.notMem_support]
        contrapose hx
        exact self_subset_cthickening _ (subset_tsupport _ hx)
      have B : f (x + t • v) = 0 := by
        rw [← Function.notMem_support]
        contrapose hx
        apply mem_cthickening_of_dist_le _ _ (‖v‖) (tsupport f) (subset_tsupport _ hx)
        simp only [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg t_pos.le]
        exact mul_le_of_le_one_left (norm_nonneg v) ht.2
      simp only [B, A, _root_.sub_self, smul_eq_mul, mul_zero, zero_mul, norm_zero]
      exact indicator_nonneg (fun y _hy ↦ by positivity) _
  · rw [integrable_indicator_iff K_compact.measurableSet]
    exact ContinuousOn.integrableOn_compact K_compact (by fun_prop)
  · filter_upwards [hf.ae_lineDifferentiableAt v] with x hx
    exact hx.hasLineDerivAt.tendsto_slope_zero_right.mul tendsto_const_nhds

/-- Integration by parts formula for the line derivative of Lipschitz functions, assuming one of
them is compactly supported. -/
/-
**LipschitzWith.integral_lineDeriv_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWi
th`。
形式化陈述：integral_lineDeriv_mul_eq (hf : LipschitzWith C f) (hg : LipschitzWith D g
) (h'g : HasCompactSupport g) (v : E) : ∫ x, lineDeriv Real f x v * g x ∂μ = ∫ x
, lineDeriv Real g x (-v) * f x ∂μ
参数：hf : LipschitzWith C f；hg : LipschitzWith D g；h'g : HasCompactSupport g；v : E
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul`：
integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul (hf : LipschitzWith C f
) (hg : Integrable g μ) (v : E) : Tendsto (fun (t : Real) =>…
· 使用定理 `Continuous.integrable_of_hasCompactSupport`：Continuous.integrable_of_has
CompactSupport (hf : Continuous f) (hcf : HasCompactSupport f) : Integrable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `LipschitzWith.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'`
：integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul' (hf : LipschitzWith C
 f) (h'f : HasCompactSupport f) (hg : Continuous g) (v : E) :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_add_right_eq_self`：∀ {G : Type u_4} {E : Type u_5
} [inst : MeasurableSpace G] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpa
ce ℝ E]   {μ : MeasureTheory.M…
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.IsAddLeftInvariant.isAddRightInvariant`：∀ {G : Type u_1} [
inst : MeasurableSpace G] [inst_1 : AddCommSemigroup G] {μ : MeasureTheory.Measu
re G}   [μ.IsAddLeftInvariant], μ.IsAddRig…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_add_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ -b + b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
Integration by parts formula for the line derivative of Lipschitz functions, ass
uming one of
them is compactly supported.
-/
theorem integral_lineDeriv_mul_eq
    (hf : LipschitzWith C f) (hg : LipschitzWith D g) (h'g : HasCompactSupport g) (v : E) :
    ∫ x, lineDeriv ℝ f x v * g x ∂μ = ∫ x, lineDeriv ℝ g x (-v) * f x ∂μ := by
  /- Write down the line derivative as the limit of `(f (x + t v) - f x) / t` and
  `(g (x - t v) - g x) / t`, and therefore the integrals as limits of the corresponding integrals
  thanks to the dominated convergence theorem. At fixed positive `t`, the integrals coincide
  (with the change of variables `y = x + t v`), so the limits also coincide. -/
  have A : Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0)
              (𝓝 (∫ x, lineDeriv ℝ f x v * g x ∂μ)) :=
    integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul
      hf (hg.continuous.integrable_of_hasCompactSupport h'g) v
  have B : Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (g (x + t • (-v)) - g x)) * f x ∂μ) (𝓝[>] 0)
              (𝓝 (∫ x, lineDeriv ℝ g x (-v) * f x ∂μ)) :=
    integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul' hg h'g hf.continuous (-v)
  suffices S1 : ∀ (t : ℝ), ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ =
                            ∫ x, (t⁻¹ • (g (x + t • (-v)) - g x)) * f x ∂μ by
    simp only [S1] at A; exact tendsto_nhds_unique A B
  intro t
  suffices S2 : ∫ x, (f (x + t • v) - f x) * g x ∂μ = ∫ x, f x * (g (x + t • (-v)) - g x) ∂μ by
    simp only [smul_eq_mul, mul_assoc, integral_const_mul, S2, mul_comm (f _)]
  have S3 : ∫ x, f (x + t • v) * g x ∂μ = ∫ x, f x * g (x + t • (-v)) ∂μ := by
    rw [← integral_add_right_eq_self _ (t • (-v))]; simp
  simp_rw [_root_.sub_mul, _root_.mul_sub]
  rw [integral_sub, integral_sub, S3]
  · apply Continuous.integrable_of_hasCompactSupport
    · exact hf.continuous.mul (hg.continuous.comp (continuous_add_const _))
    · exact (h'g.comp_homeomorph (Homeomorph.addRight (t • (-v)))).mul_left
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport h'g.mul_left
  · apply Continuous.integrable_of_hasCompactSupport
    · exact (hf.continuous.comp (continuous_add_const _)).mul hg.continuous
    · exact h'g.mul_left
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport h'g.mul_left

/-- The line derivative of a Lipschitz function is almost everywhere linear with respect to fixed
coefficients. -/
/-
**LipschitzWith.ae_lineDeriv_sum_eq** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：ae_lineDeriv_sum_eq (hf : LipschitzWith C f) {ι : Type*} (s : Finset ι) (a
 : ι -> Real) (v : ι -> E) : forallᵐ x ∂μ, lineDeriv Real f x (∑ i in s, a i • v
 i) = ∑ i in s, a i • lineDeriv Real f x (v i)
参数：hf : LipschitzWith C f；s : Finset ι；a : ι -> Real；v : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ae_eq_of_integral_contDiff_smul_eq`：ae_eq_of_integral_contDiff_smul_eq (
hf : LocallyIntegrable f μ) (hf' : LocallyIntegrable f' μ) (h : forall (g : E ->
 Real), ContDiff Real ∞ …
· 使用定理 `LipschitzWith.locallyIntegrable_lineDeriv`：locallyIntegrable_lineDeriv (
hf : LipschitzWith C f) (v : E) : LocallyIntegrable (fun x => lineDeriv Real f x
 v) μ
· 使用定理 `MeasureTheory.locallyIntegrable_finsetSum`：locallyIntegrable_finsetSum {
ι} (s : Finset ι) {f : ι -> X -> ε'''} (hf : forall i in s, LocallyIntegrable (f
 i) μ) : LocallyIntegrable (fun…
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
· 使用定理 `MeasureTheory.LocallyIntegrable.smul`：∀ {X : Type u_1} {E : Type u_6} [i
nst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : NormedAddCommGr
oup E]   {μ : MeasureTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `MeasureTheory.Integrable.smul_of_top_left`：∀ {α : Type u_1} {β : Type u_
2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGr
oup β]   {𝕜 : Type u_8} [inst_1…
· 使用定理 `Continuous.integrable_of_hasCompactSupport`：Continuous.integrable_of_has
CompactSupport (hf : Continuous f) (hcf : HasCompactSupport f) : Integrable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `ContDiff.continuous`：ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuo
us f
· 使用定理 `MeasureTheory.MemLp.const_smul`：∀ {α : Type u_1} {F : Type u_2} {m : Mea
surableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup F] {f : α →…
· 使用定理 `LipschitzWith.memLp_lineDeriv`：memLp_lineDeriv (hf : LipschitzWith C f) 
(v : E) : MemLp (fun x => lineDeriv Real f x v) ∞ μ
· 使用定理 `MeasureTheory.integral_finsetSum`：integral_finsetSum {ι} (s : Finset ι) 
{f : ι -> α -> G} (hf : forall i in s, Integrable (f i) μ) : ∫ a, ∑ i in s, f i 
a ∂μ = ∑ i in s, ∫ a, …
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Continuous.clm_apply`：Continuous.clm_apply {f : X -> E ->L[𝕜] F} {g : X 
-> E} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => f x (g x))
· 使用定理 `ContDiff.continuous_fderiv`：ContDiff.continuous_fderiv (h : ContDiff 𝕜 n
 f) (hn : n != 0) : Continuous (fderiv 𝕜 f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
The line derivative of a Lipschitz function is almost everywhere linear with res
pect to fixed
coefficients.
-/
theorem ae_lineDeriv_sum_eq
    (hf : LipschitzWith C f) {ι : Type*} (s : Finset ι) (a : ι → ℝ) (v : ι → E) :
    ∀ᵐ x ∂μ, lineDeriv ℝ f x (∑ i ∈ s, a i • v i) = ∑ i ∈ s, a i • lineDeriv ℝ f x (v i) := by
  /- Clever argument by Morrey: integrate against a smooth compactly supported function `g`, switch
  the derivative to `g` by integration by parts, and use the linearity of the derivative of `g` to
  conclude that the initial integrals coincide. -/
  apply ae_eq_of_integral_contDiff_smul_eq (hf.locallyIntegrable_lineDeriv _)
    (locallyIntegrable_finsetSum _ (fun i hi ↦ (hf.locallyIntegrable_lineDeriv (v i)).smul (a i)))
    (fun g g_smooth g_comp ↦ ?_)
  simp_rw [Finset.smul_sum]
  have A : ∀ i ∈ s, Integrable (fun x ↦ g x • (a i • fun x ↦ lineDeriv ℝ f x (v i)) x) μ :=
    fun i hi ↦ (g_smooth.continuous.integrable_of_hasCompactSupport g_comp).smul_of_top_left
      ((hf.memLp_lineDeriv (v i)).const_smul (a i))
  rw [integral_finsetSum _ A]
  suffices S1 : ∫ x, lineDeriv ℝ f x (∑ i ∈ s, a i • v i) * g x ∂μ
      = ∑ i ∈ s, a i * ∫ x, lineDeriv ℝ f x (v i) * g x ∂μ by
    dsimp only [smul_eq_mul, Pi.smul_apply]
    simp_rw [← mul_assoc, mul_comm _ (a _), mul_assoc, integral_const_mul, mul_comm (g _), S1]
  suffices S2 : ∫ x, (∑ i ∈ s, a i * fderiv ℝ g x (v i)) * f x ∂μ =
                  ∑ i ∈ s, a i * ∫ x, fderiv ℝ g x (v i) * f x ∂μ by
    obtain ⟨D, g_lip⟩ : ∃ D, LipschitzWith D g :=
      ContDiff.lipschitzWith_of_hasCompactSupport g_comp g_smooth (by simp)
    simp_rw [integral_lineDeriv_mul_eq hf g_lip g_comp]
    simp_rw [(g_smooth.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    simp only [map_neg, _root_.map_sum, map_smul, smul_eq_mul, neg_mul]
    simp only [integral_neg, mul_neg, Finset.sum_neg_distrib, neg_inj]
    exact S2
  suffices B : ∀ i ∈ s, Integrable (fun x ↦ a i * (fderiv ℝ g x (v i) * f x)) μ by
    simp_rw [Finset.sum_mul, mul_assoc, integral_finsetSum s B, integral_const_mul]
  intro i _hi
  let L : StrongDual ℝ E → ℝ := fun f ↦ f (v i)
  change Integrable (fun x ↦ a i * ((L ∘ (fderiv ℝ g)) x * f x)) μ
  refine (Continuous.integrable_of_hasCompactSupport ?_ ?_).const_mul _
  · exact ((g_smooth.continuous_fderiv (by simp)).clm_apply continuous_const).mul
      hf.continuous
  · exact ((g_comp.fderiv ℝ).comp_left rfl).mul_right

/-!
### Step 3: construct the derivative using the line derivatives along a basis
-/

/-
**LipschitzWith.ae_exists_fderiv_of_countable** 是 Mathlib 中的一个定理，位于命名空间 `Lipschi
tzWith`。
形式化陈述：ae_exists_fderiv_of_countable (hf : LipschitzWith C f) {s : Set E} (hs : s
.Countable) : forallᵐ x ∂μ, exists (L : StrongDual Real E), forall v in s, HasLi
neDerivAt Real f (L v) x v
参数：hf : LipschitzWith C f；hs : s.Countable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_ball_iff`：ae_ball_iff {ι : Type*} {S : Set ι} (hS : S.C
ountable) {p : α -> forall i in S, Prop} : (forallᵐ x ∂μ, forall i (hi : i in S)
, p x i hi) ↔ f…
· 使用定理 `LipschitzWith.ae_lineDeriv_sum_eq`：ae_lineDeriv_sum_eq (hf : LipschitzWi
th C f) {ι : Type*} (s : Finset ι) (a : ι -> Real) (v : ι -> E) : forallᵐ x ∂μ, 
lineDeriv Real f x (∑ i…
· 使用定理 `LipschitzWith.ae_lineDifferentiableAt`：ae_lineDifferentiableAt (hf : Lip
schitzWith C f) (v : E) : forallᵐ p ∂μ, LineDifferentiableAt Real f p v
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.constr_apply_fintype`：constr_apply_fintype [Fintype ι] (b :
 Basis ι R M) (f : ι -> M') (x : M) : (constr (M'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LineDifferentiableAt.hasLineDerivAt`：LineDifferentiableAt.hasLineDerivAt
 (h : LineDifferentiableAt 𝕜 f x v) : HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v

--- 原说明 ---
### Step 3: construct the derivative using the line derivatives along a basis
-/
theorem ae_exists_fderiv_of_countable
    (hf : LipschitzWith C f) {s : Set E} (hs : s.Countable) :
    ∀ᵐ x ∂μ, ∃ (L : StrongDual ℝ E), ∀ v ∈ s, HasLineDerivAt ℝ f (L v) x v := by
  have B := Basis.ofVectorSpace ℝ E
  have I1 : ∀ᵐ (x : E) ∂μ, ∀ v ∈ s, lineDeriv ℝ f x (∑ i, (B.repr v i) • B i) =
                                  ∑ i, B.repr v i • lineDeriv ℝ f x (B i) :=
    (ae_ball_iff hs).2 (fun v _ ↦ hf.ae_lineDeriv_sum_eq _ _ _)
  have I2 : ∀ᵐ (x : E) ∂μ, ∀ v ∈ s, LineDifferentiableAt ℝ f x v :=
    (ae_ball_iff hs).2 (fun v _ ↦ hf.ae_lineDifferentiableAt v)
  filter_upwards [I1, I2] with x hx h'x
  let L : StrongDual ℝ E :=
    LinearMap.toContinuousLinearMap (B.constr ℝ (fun i ↦ lineDeriv ℝ f x (B i)))
  refine ⟨L, fun v hv ↦ ?_⟩
  have J : L v = lineDeriv ℝ f x v := by convert! (hx v hv).symm <;> simp [L, B.sum_repr v]
  simpa [J] using (h'x v hv).hasLineDerivAt

omit [MeasurableSpace E] in
/-- If a Lipschitz functions has line derivatives in a dense set of directions, all of them given by
a single continuous linear map `L`, then it admits `L` as Fréchet derivative. -/
/-
**LipschitzWith.hasFDerivAt_of_hasLineDerivAt_of_closure** 是 Mathlib 中的一个定理，位于命名
空间 `LipschitzWith`。
形式化陈述：hasFDerivAt_of_hasLineDerivAt_of_closure {f : E -> F} (hf : LipschitzWith 
C f) {s : Set E} (hs : sphere 0 1 subseteq closure s) {L : E ->L[Real] F} {x : E
} (hL : forall v in s, HasLineDerivAt Real f (L v) x v) : HasFDerivAt f L x
参数：hf : LipschitzWith C f；hs : sphere 0 1 subseteq closure s；hL : forall v in s,
 HasLineDerivAt Real f (L v) x v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasFDerivAt_iff_isLittleO_nhds_zero`：hasFDerivAt_iff_isLittleO_nhds_zero
 : HasFDerivAt f f' x ↔ (fun h : E => f (x + h) - f x - f' h) =o[𝓝 0] fun h => h
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_closure_iff`：mem_closure_iff {s : Set α} {a : α} : a in closu
re s ↔ forall ε > 0, exists b in s, dist a b < ε
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `IsCompact.elim_finite_subcover_image`：IsCompact.elim_finite_subcover_ima
ge {b : Set ι} {c : ι -> Set X} (hs : IsCompact s) (hc₁ : forall i in b, IsOpen 
(c i)) (hc₂ : s subseteq ⋃…
· 使用定理 `isCompact_sphere`：isCompact_sphere {α : Type*} [PseudoMetricSpace α] [Pr
operSpace α] (x : α) (r : Real) : IsCompact (sphere x r)
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.eventually_all`：∀ {α : Type u} {ι : Type u_2} {I : Set ι},   
I.Finite → ∀ {l : Filter α} {p : ι → α → Prop}, (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x
) ↔ ∀ i ∈ I, ∀ᶠ…
· 使用定理 `Asymptotics.IsLittleO.def`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Filte
r α}, f =o[l] g…
· 使用定理 `hasLineDerivAt_iff_isLittleO_nhds_zero`：hasLineDerivAt_iff_isLittleO_nhd
s_zero : HasLineDerivAt 𝕜 f f' x v ↔ (fun t : 𝕜 => f (x + t • v) - f x - t • f')
 =o[𝓝 0] fun t => t
（共 94 条，此处仅展示前 30 条）

--- 原说明 ---
If a Lipschitz functions has line derivatives in a dense set of directions, all 
of them given by
a single continuous linear map `L`, then it admits `L` as Fréchet derivative.
-/
theorem hasFDerivAt_of_hasLineDerivAt_of_closure
    {f : E → F} (hf : LipschitzWith C f) {s : Set E} (hs : sphere 0 1 ⊆ closure s)
    {L : E →L[ℝ] F} {x : E} (hL : ∀ v ∈ s, HasLineDerivAt ℝ f (L v) x v) :
    HasFDerivAt f L x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε εpos
  obtain ⟨δ, δpos, hδ⟩ : ∃ δ, 0 < δ ∧ (C + ‖L‖ + 1) * δ = ε :=
    ⟨ε / (C + ‖L‖ + 1), by positivity, mul_div_cancel₀ ε (by positivity)⟩
  obtain ⟨q, hqs, q_fin, hq⟩ : ∃ q, q ⊆ s ∧ q.Finite ∧ sphere 0 1 ⊆ ⋃ y ∈ q, ball y δ := by
    have : sphere 0 1 ⊆ ⋃ y ∈ s, ball y δ := by
      apply hs.trans (fun z hz ↦ ?_)
      obtain ⟨y, ys, hy⟩ : ∃ y ∈ s, dist z y < δ := Metric.mem_closure_iff.1 hz δ δpos
      exact mem_biUnion ys hy
    exact (isCompact_sphere 0 1).elim_finite_subcover_image (fun y _hy ↦ isOpen_ball) this
  have I : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ v ∈ q, ‖f (x + t • v) - f x - t • L v‖ ≤ δ * ‖t‖ := by
    apply (Finite.eventually_all q_fin).2 (fun v hv ↦ ?_)
    apply Asymptotics.IsLittleO.def ?_ δpos
    exact hasLineDerivAt_iff_isLittleO_nhds_zero.1 (hL v (hqs hv))
  obtain ⟨r, r_pos, hr⟩ : ∃ (r : ℝ), 0 < r ∧ ∀ (t : ℝ), ‖t‖ < r →
      ∀ v ∈ q, ‖f (x + t • v) - f x - t • L v‖ ≤ δ * ‖t‖ := by
    rcases Metric.mem_nhds_iff.1 I with ⟨r, r_pos, hr⟩
    exact ⟨r, r_pos, fun t ht v hv ↦ hr (mem_ball_zero_iff.2 ht) v hv⟩
  apply Metric.mem_nhds_iff.2 ⟨r, r_pos, fun v hv ↦ ?_⟩
  rcases eq_or_ne v 0 with rfl | v_ne
  · simp
  obtain ⟨w, ρ, w_mem, hvw, hρ⟩ : ∃ w ρ, w ∈ sphere 0 1 ∧ v = ρ • w ∧ ρ = ‖v‖ := by
    refine ⟨‖v‖⁻¹ • v, ‖v‖, by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 v_ne)], ?_, rfl⟩
    simp [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 v_ne)]
  have norm_rho : ‖ρ‖ = ρ := by rw [hρ, norm_norm]
  have rho_pos : 0 ≤ ρ := by simp [hρ]
  obtain ⟨y, yq, hy⟩ : ∃ y ∈ q, ‖w - y‖ < δ := by simpa [← dist_eq_norm] using hq w_mem
  have : ‖y - w‖ < δ := by rwa [norm_sub_rev]
  calc ‖f (x + v) - f x - L v‖
      = ‖f (x + ρ • w) - f x - ρ • L w‖ := by simp [hvw]
    _ = ‖(f (x + ρ • w) - f (x + ρ • y)) + (ρ • L y - ρ • L w)
          + (f (x + ρ • y) - f x - ρ • L y)‖ := by congr; abel
    _ ≤ ‖f (x + ρ • w) - f (x + ρ • y)‖ + ‖ρ • L y - ρ • L w‖
          + ‖f (x + ρ • y) - f x - ρ • L y‖ := norm_add₃_le
    _ ≤ C * ‖(x + ρ • w) - (x + ρ • y)‖ + ρ * (‖L‖ * ‖y - w‖) + δ * ρ := by
      gcongr
      · exact hf.norm_sub_le _ _
      · rw [← smul_sub, norm_smul, norm_rho]
        gcongr
        exact L.lipschitz.norm_sub_le _ _
      · conv_rhs => rw [← norm_rho]
        apply hr _ _ _ yq
        simpa [norm_rho, hρ] using hv
    _ ≤ C * (ρ * δ) + ρ * (‖L‖ * δ) + δ * ρ := by
      simp only [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, norm_rho]; gcongr
    _ = ((C + ‖L‖ + 1) * δ) * ρ := by ring
    _ = ε * ‖v‖ := by rw [hδ, hρ]

/-- A real-valued function on a finite-dimensional space which is Lipschitz is
differentiable almost everywhere. Superseded by
`LipschitzWith.ae_differentiableAt` which works for functions taking value in any
finite-dimensional space. -/
/-
**LipschitzWith.ae_differentiableAt_of_real** 是 Mathlib 中的一个定理，位于命名空间 `Lipschitz
With`。
形式化陈述：ae_differentiableAt_of_real (hf : LipschitzWith C f) : forallᵐ x ∂μ, Diffe
rentiableAt Real f x
参数：hf : LipschitzWith C f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.exists_countable_dense`：exists_countable_dense [Separab
leSpace α] : exists s : Set α, s.Countable ∧ Dense s
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `LipschitzWith.ae_exists_fderiv_of_countable`：ae_exists_fderiv_of_countab
le (hf : LipschitzWith C f) {s : Set E} (hs : s.Countable) : forallᵐ x ∂μ, exist
s (L : StrongDual Real E), forall…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `LipschitzWith.hasFDerivAt_of_hasLineDerivAt_of_closure`：hasFDerivAt_of_h
asLineDerivAt_of_closure {f : E -> F} (hf : LipschitzWith C f) {s : Set E} (hs :
 sphere 0 1 subseteq closure s) {L : E ->L[R…

--- 原说明 ---
A real-valued function on a finite-dimensional space which is Lipschitz is
differentiable almost everywhere. Superseded by
`LipschitzWith.ae_differentiableAt` which works for functions taking value in an
y
finite-dimensional space.
-/
theorem ae_differentiableAt_of_real (hf : LipschitzWith C f) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ f x := by
  obtain ⟨s, s_count, s_dense⟩ : ∃ (s : Set E), s.Countable ∧ Dense s :=
    TopologicalSpace.exists_countable_dense E
  have hs : sphere 0 1 ⊆ closure s := by rw [s_dense.closure_eq]; exact subset_univ _
  filter_upwards [hf.ae_exists_fderiv_of_countable s_count]
  rintro x ⟨L, hL⟩
  exact (hf.hasFDerivAt_of_hasLineDerivAt_of_closure hs hL).differentiableAt

end LipschitzWith

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsAddHaarMeasure μ]

namespace LipschitzOnWith

/-- A real-valued function on a finite-dimensional space which is Lipschitz on a set is
differentiable almost everywhere in this set. Superseded by
`LipschitzOnWith.ae_differentiableWithinAt_of_mem` which works for functions taking value in any
finite-dimensional space. -/
/-
**LipschitzOnWith.ae_differentiableWithinAt_of_mem_of_real** 是 Mathlib 中的一个定理，位于
命名空间 `LipschitzOnWith`。
形式化陈述：ae_differentiableWithinAt_of_mem_of_real (hf : LipschitzOnWith C f s) : fo
rallᵐ x ∂μ, x in s -> DifferentiableWithinAt Real f s x
参数：hf : LipschitzOnWith C f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LipschitzOnWith.extend_real`：LipschitzOnWith.extend_real {f : α -> Real}
 {s : Set α} {K : Real>=0} (hf : LipschitzOnWith K f s) : exists g : α -> Real, 
LipschitzWith K g…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `LipschitzWith.ae_differentiableAt_of_real`：ae_differentiableAt_of_real (
hf : LipschitzWith C f) : forallᵐ x ∂μ, DifferentiableAt Real f x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `DifferentiableWithinAt.congr`：DifferentiableWithinAt.congr (h : Differen
tiableWithinAt 𝕜 f s x) (ht : forall x in s, f₁ x = f x) (hx : f₁ x = f x) : Dif
ferentiableWithinA…
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x

--- 原说明 ---
A real-valued function on a finite-dimensional space which is Lipschitz on a set
 is
differentiable almost everywhere in this set. Superseded by
`LipschitzOnWith.ae_differentiableWithinAt_of_mem` which works for functions tak
ing value in any
finite-dimensional space.
-/
theorem ae_differentiableWithinAt_of_mem_of_real (hf : LipschitzOnWith C f s) :
    ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  obtain ⟨g, g_lip, hg⟩ : ∃ (g : E → ℝ), LipschitzWith C g ∧ EqOn f g s := hf.extend_real
  filter_upwards [g_lip.ae_differentiableAt_of_real] with x hx xs
  exact hx.differentiableWithinAt.congr hg (hg xs)

/-- A function on a finite-dimensional space which is Lipschitz on a set and taking values in a
product space is differentiable almost everywhere in this set. Superseded by
`LipschitzOnWith.ae_differentiableWithinAt_of_mem` which works for functions taking value in any
finite-dimensional space. -/
/-
**LipschitzOnWith.ae_differentiableWithinAt_of_mem_pi** 是 Mathlib 中的一个定理，位于命名空间 
`LipschitzOnWith`。
形式化陈述：ae_differentiableWithinAt_of_mem_pi {ι : Type*} [Fintype ι] {f : E -> ι ->
 Real} {s : Set E} (hf : LipschitzOnWith C f s) : forallᵐ x ∂μ, x in s -> Differ
entiableWithinAt Real f s x
参数：hf : LipschitzOnWith C f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.eval`：∀ {ι : Type x} {α : ι → Type u} [inst : (i : ι) → Ps
eudoEMetricSpace (α i)] [inst_1 : Fintype ι] (i : ι),   LipschitzWith 1 (Functio
n.eval i…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LipschitzOnWith.ae_differentiableWithinAt_of_mem_of_real`：ae_differentia
bleWithinAt_of_mem_of_real (hf : LipschitzOnWith C f s) : forallᵐ x ∂μ, x in s -
> DifferentiableWithinAt Real f s x
· 使用定理 `LipschitzWith.comp_lipschitzOnWith`：comp_lipschitzOnWith {Kf Kg : Real>=
0} {f : β -> γ} {g : α -> β} {s : Set α} (hf : LipschitzWith Kf f) (hg : Lipschi
tzOnWith Kg g s) : Lipsc…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `differentiableWithinAt_pi`：differentiableWithinAt_pi : DifferentiableWit
hinAt 𝕜 Φ s x ↔ forall i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x

--- 原说明 ---
A function on a finite-dimensional space which is Lipschitz on a set and taking 
values in a
product space is differentiable almost everywhere in this set. Superseded by
`LipschitzOnWith.ae_differentiableWithinAt_of_mem` which works for functions tak
ing value in any
finite-dimensional space.
-/
theorem ae_differentiableWithinAt_of_mem_pi
    {ι : Type*} [Fintype ι] {f : E → ι → ℝ} {s : Set E}
    (hf : LipschitzOnWith C f s) : ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  have A : ∀ i : ι, LipschitzWith 1 (fun x : ι → ℝ ↦ x i) := fun i => LipschitzWith.eval i
  have : ∀ i : ι, ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ (fun x : E ↦ f x i) s x := fun i ↦ by
    apply ae_differentiableWithinAt_of_mem_of_real
    exact LipschitzWith.comp_lipschitzOnWith (A i) hf
  filter_upwards [ae_all_iff.2 this] with x hx xs
  exact differentiableWithinAt_pi.2 (fun i ↦ hx i xs)

/-- *Rademacher's theorem*: a function between finite-dimensional real vector spaces which is
Lipschitz on a set is differentiable almost everywhere in this set. -/
/-
**LipschitzOnWith.ae_differentiableWithinAt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Li
pschitzOnWith`。
形式化陈述：ae_differentiableWithinAt_of_mem {f : E -> F} (hf : LipschitzOnWith C f s)
 : forallᵐ x ∂μ, x in s -> DifferentiableWithinAt Real f s x
参数：hf : LipschitzOnWith C f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LipschitzOnWith.ae_differentiableWithinAt_of_mem_pi`：ae_differentiableWi
thinAt_of_mem_pi {ι : Type*} [Fintype ι] {f : E -> ι -> Real} {s : Set E} (hf : 
LipschitzOnWith C f s) : forallᵐ x ∂μ, x …
· 使用定理 `LipschitzWith.comp_lipschitzOnWith`：comp_lipschitzOnWith {Kf Kg : Real>=
0} {f : β -> γ} {g : α -> β} {s : Set α} (hf : LipschitzWith Kf f) (hg : Lipschi
tzOnWith Kg g s) : Lipsc…
· 使用定理 `ContinuousLinearEquiv.lipschitz`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : T
ype u_4} {F : Type u_5} [inst : NontriviallyNormedField 𝕜]   [inst_1 : Nontrivia
llyNormedField 𝕜₂] [i…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearEquiv.symm_comp_self`：symm_comp_self (e : M₁ ≃SL[σ₁₂] M₂
) : (e.symm : M₂ -> M₁) ∘ (e : M₁ -> M₂) = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DifferentiableAt.comp_differentiableWithinAt`：DifferentiableAt.comp_diff
erentiableWithinAt {g : F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : Differen
tiableWithinAt 𝕜 f s x) : Differen…
· 使用定理 `ContinuousLinearEquiv.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] {F : Type u_…

--- 原说明 ---
*Rademacher's theorem*: a function between finite-dimensional real vector spaces
 which is
Lipschitz on a set is differentiable almost everywhere in this set.
-/
theorem ae_differentiableWithinAt_of_mem {f : E → F} (hf : LipschitzOnWith C f s) :
    ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  have A := (Basis.ofVectorSpace ℝ F).equivFun.toContinuousLinearEquiv
  suffices H : ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ (A ∘ f) s x by
    filter_upwards [H] with x hx xs
    have : f = (A.symm ∘ A) ∘ f := by
      simp only [ContinuousLinearEquiv.symm_comp_self, Function.id_comp]
    rw [this]
    exact A.symm.differentiableAt.comp_differentiableWithinAt x (hx xs)
  apply ae_differentiableWithinAt_of_mem_pi
  exact A.lipschitz.comp_lipschitzOnWith hf

/-- *Rademacher's theorem*: a function between finite-dimensional real vector spaces which is
Lipschitz on a set is differentiable almost everywhere in this set. -/
/-
**LipschitzOnWith.ae_differentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `Lipschitz
OnWith`。
形式化陈述：ae_differentiableWithinAt {f : E -> F} (hf : LipschitzOnWith C f s) (hs : 
MeasurableSet s) : forallᵐ x ∂(μ.restrict s), DifferentiableWithinAt Real f s x
参数：hf : LipschitzOnWith C f s；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `LipschitzOnWith.ae_differentiableWithinAt_of_mem`：ae_differentiableWithi
nAt_of_mem {f : E -> F} (hf : LipschitzOnWith C f s) : forallᵐ x ∂μ, x in s -> D
ifferentiableWithinAt Real f s x

--- 原说明 ---
*Rademacher's theorem*: a function between finite-dimensional real vector spaces
 which is
Lipschitz on a set is differentiable almost everywhere in this set.
-/
theorem ae_differentiableWithinAt {f : E → F} (hf : LipschitzOnWith C f s)
    (hs : MeasurableSet s) :
    ∀ᵐ x ∂(μ.restrict s), DifferentiableWithinAt ℝ f s x := by
  rw [ae_restrict_iff' hs]
  exact hf.ae_differentiableWithinAt_of_mem

end LipschitzOnWith

/-- *Rademacher's theorem*: a Lipschitz function between finite-dimensional real vector spaces is
differentiable almost everywhere. -/
/-
**LipschitzWith.ae_differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.ae_differentiableAt {f : E -> F} (h : LipschitzWith C f) : f
orallᵐ x ∂μ, DifferentiableAt Real f x
参数：h : LipschitzWith C f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LipschitzOnWith.ae_differentiableWithinAt_of_mem`：ae_differentiableWithi
nAt_of_mem {f : E -> F} (hf : LipschitzOnWith C f s) : forallᵐ x ∂μ, x in s -> D
ifferentiableWithinAt Real f s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lipschitzOnWith_univ`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricS
pace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   LipschitzOnW
ith K f Se…

--- 原说明 ---
*Rademacher's theorem*: a Lipschitz function between finite-dimensional real vec
tor spaces is
differentiable almost everywhere.
-/
theorem LipschitzWith.ae_differentiableAt {f : E → F} (h : LipschitzWith C f) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ f x := by
  rw [← lipschitzOnWith_univ] at h
  simpa [differentiableWithinAt_univ] using h.ae_differentiableWithinAt_of_mem

/-- In a real finite-dimensional normed vector space,
  the norm is almost everywhere differentiable. -/
/-
**ae_differentiableAt_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_differentiableAt_norm : forallᵐ x ∂μ, DifferentiableAt Real (‖·‖) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.ae_differentiableAt`：LipschitzWith.ae_differentiableAt {f 
: E -> F} (h : LipschitzWith C f) : forallᵐ x ∂μ, DifferentiableAt Real f x
· 使用定理 `lipschitzWith_one_norm`：∀ {E : Type u_2} [inst : SeminormedAddGroup E], 
LipschitzWith 1 norm

--- 原说明 ---
In a real finite-dimensional normed vector space,
  the norm is almost everywhere differentiable.
-/
theorem ae_differentiableAt_norm :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ (‖·‖) x := lipschitzWith_one_norm.ae_differentiableAt

omit [MeasurableSpace E] in
/-- In a real finite-dimensional normed vector space,
  the set of points where the norm is differentiable at is dense. -/
/-
**dense_differentiableAt_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_differentiableAt_norm : Dense {x : E | DifferentiableAt Real (‖·‖) x
}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.dense_of_ae`：dense_of_ae {p : X -> Prop} (hp : for
allᵐ x ∂μ, p x) : Dense {x | p x}
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u
_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace 
G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `isAddHaarMeasure_basis_addHaar`：∀ {ι : Type u_1} {E : Type u_3} [inst : 
Fintype ι] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E]   [inst_3 
: MeasurableSpace E]…
· 使用定理 `ae_differentiableAt_norm`：ae_differentiableAt_norm : forallᵐ x ∂μ, Diffe
rentiableAt Real (‖·‖) x

--- 原说明 ---
In a real finite-dimensional normed vector space,
  the set of points where the norm is differentiable at is dense.
-/
theorem dense_differentiableAt_norm :
    Dense {x : E | DifferentiableAt ℝ (‖·‖) x} :=
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let w := Basis.ofVectorSpace ℝ E
  MeasureTheory.Measure.dense_of_ae (ae_differentiableAt_norm (μ := w.addHaar))
