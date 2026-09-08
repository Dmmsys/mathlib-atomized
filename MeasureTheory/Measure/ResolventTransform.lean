/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Measure.Support

import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Resolvent Transform of a Measure

Given a normed algebra `A` over a normed field `𝕜`, and `μ : Measure 𝕜`, we define the
resolvent transform of `μ` by the formula

`resolventTransform μ a = ∫ x, resolvent a x ∂μ = ∫ x, (↑ₐ x - a)⁻¹ʳ ∂μ`

This is not a standard notion in the literature, but specializes to a few standard notions,
namely the case `𝕜 = ℝ` and `A = ℂ` is the Stieltjes transform, and the case `𝕜 = A = ℂ` is the
Cauchy transform, given by the formulas:

`∫ (x : ℝ), (↑x - a)⁻¹ ∂μ` and `∫ (x : ℂ), (↑x - a)⁻¹ ∂μ` respectively.

## Main definitions

* `resolventTransform μ a`: The resolvent transform of a measure `μ` at `a`

## Main statements

* `hasDerivAt_resolventTransform`: For any `a` not in the support of `μ`,
  the `resolventTransform` has derivative `∫ x, resolvent a x ^ 2 ∂u` at `a`.
* `analyticOn_resolventTransform`: In the case `A = ℂ`, the `resolventTransform`
  is holomorphic on the complement of `μ.support`.

## Tags

resolvent transform, Stieljes transform, Cauchy transform
-/

public section

variable {𝕜 A : Type*}

open MeasureTheory Measure Metric Complex spectrum

open scoped Topology

namespace MeasureTheory

section resolvent

variable [NontriviallyNormedField 𝕜] [MeasurableSpace 𝕜]

set_option backward.isDefEq.respectTransparency.types false in
@[fun_prop]
/-
**MeasureTheory.measurable_resolvent** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measurable_resolvent {a : A} [OpensMeasurableSpace 𝕜] [NormedRing A] [Norm
edAlgebra 𝕜 A] [CompleteSpace A] [MeasurableSpace A] [BorelSpace A] : Measurable
 (resolvent (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.continuousOn`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 
𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {s 
: Set 𝕜} {f f…
· 使用定理 `spectrum.hasDerivAt_resolvent_const_left`：hasDerivAt_resolvent_const_lef
t {a : A} {k : 𝕜} (hk : k in resolventSet 𝕜 a) : HasDerivAt (resolvent a) (-reso
lvent a k ^ 2) k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `spectrum.resolvent_zero_of_mem_spectrum`：resolvent_zero_of_mem_spectrum 
{r : R} {a : A} (hr : r in σ a) : resolvent a r = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `spectrum.isOpen_resolventSet`：isOpen_resolventSet (a : A) : IsOpen (ρ a)
· 使用定理 `Set.piecewise_same`：piecewise_same : s.piecewise f f = f
· 使用定理 `ContinuousOn.measurable_piecewise`：ContinuousOn.measurable_piecewise {f 
g : α -> γ} {s : Set α} [forall j : α, Decidable (j in s)] (hf : ContinuousOn f 
s) (hg : ContinuousOn g…
-/
theorem measurable_resolvent {a : A} [OpensMeasurableSpace 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
    [CompleteSpace A] [MeasurableSpace A] [BorelSpace A] :
    Measurable (resolvent (R := 𝕜) a) := by
  classical
  have h1 : ContinuousOn (resolvent (R := 𝕜) a) (resolventSet 𝕜 a) :=
    HasDerivAt.continuousOn (fun _ hx ↦ hasDerivAt_resolvent_const_left hx)
  have h2 : ContinuousOn (resolvent (R := 𝕜) a) (resolventSet 𝕜 a)ᶜ := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_const (y := (0 : A)) with x
    simp
  have h3 : MeasurableSet (resolventSet 𝕜 a) := (isOpen_resolventSet a).measurableSet
  simpa using h1.measurable_piecewise h2 h3

variable [CompleteSpace 𝕜] [NormedDivisionRing A] [NormedAlgebra 𝕜 A]
/-
**MeasureTheory.norm_resolvent_le_inv_infDist_support** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：norm_resolvent_le_inv_infDist_support {μ : Measure 𝕜} {a : A} (hz : a ∉ al
gebraMap 𝕜 A '' μ.support) {x : 𝕜} (hx : x in μ.support) : ‖resolvent a x‖ <= (i
nfDist a (algebraMap 𝕜 A '' μ.support))⁻¹
参数：hz : a ∉ algebraMap 𝕜 A '' μ.support；hx : x in μ.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsClosed.notMem_iff_infDist_pos`：∀ {α : Type u} [inst : PseudoMetricSpac
e α] {s : Set α} {x : α},   IsClosed s → s.Nonempty → (x ∉ s ↔ 0 < Metric.infDis
t x s)
· 使用定理 `Topology.IsClosedEmbedding.isClosed_iff_image_isClosed`：∀ {X : Type u_1}
 {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpa
ce Y],   Topology.IsClosedEmbedding f → ∀ {s…
· 使用定理 `Isometry.isClosedEmbedding`：isClosedEmbedding [CompleteSpace α] [EMetric
Space γ] {f : α -> γ} (hf : Isometry f) : IsClosedEmbedding f
· 使用定理 `algebraMap_isometry`：algebraMap_isometry [NormOneClass 𝕜'] : Isometry (a
lgebraMap 𝕜 𝕜')
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用引理 `MeasureTheory.Measure.isClosed_support`：isClosed_support {μ : Measure X}
 : IsClosed μ.support
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Set.nonempty_of_mem`：nonempty_of_mem {x} (h : x in s) : s.Nonempty
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Metric.infDist_le_dist_of_mem`：infDist_le_dist_of_mem (h : y in s) : inf
Dist x s <= dist x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instFaithfulSMul_1`：∀ (R : Type u_1) (A : Type u_2) [inst : CommRing R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] [IsSimpleRing R]   [Nontrivial A], 
Faithful…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `resolvent.eq_1`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] (a : A) (r : R),   resolvent a r = Ring.inv
erse…
· 使用定理 `Ring.inverse_eq_inv'`：Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) =
 Inv.inv
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用引理 `inv_le_inv₀`：inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ <= b⁻¹ ↔ b <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
（共 61 条，此处仅展示前 30 条）
-/
theorem norm_resolvent_le_inv_infDist_support {μ : Measure 𝕜} {a : A}
    (hz : a ∉ algebraMap 𝕜 A '' μ.support) {x : 𝕜} (hx : x ∈ μ.support) :
    ‖resolvent a x‖ ≤ (infDist a (algebraMap 𝕜 A '' μ.support))⁻¹ := by
  have : 0 < infDist a (algebraMap 𝕜 A '' μ.support) := by
    refine (IsClosed.notMem_iff_infDist_pos ?_ ((Set.nonempty_of_mem hx).image _)).mp hz
    refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
    exact (algebraMap_isometry 𝕜 A).isClosedEmbedding
  have : infDist a (algebraMap 𝕜 A '' μ.support) ≤ ‖(algebraMap 𝕜 A) x - a‖ := by
    grw [infDist_le_dist_of_mem (y := (algebraMap 𝕜 A) x), ← dist_eq_norm, dist_comm]
    simp [hx]
  grw [resolvent, Ring.inverse_eq_inv', norm_inv, inv_le_inv₀ (by linarith) (by positivity), this]
/-
**MeasureTheory.integrable_resolvent** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_resolvent [HereditarilyLindelofSpace 𝕜] [OpensMeasurableSpace 𝕜
] [CompleteSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace 
A] {μ : Measure 𝕜} [IsFiniteMeasure μ] {a : A} (hz : a ∉ algebraMap 𝕜 A '' μ.sup
port) : Integrable (resolvent a) μ
参数：hz : a ∉ algebraMap 𝕜 A '' μ.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.measurable_resolvent`：measurable_resolvent {a : A} [OpensM
easurableSpace 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [Measurab
leSpace A] [BorelSpace A…
· 使用定理 `MeasureTheory.HasFiniteIntegral.of_bounded`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   [MeasureTheory.IsFinit…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.support_mem_ae`：support_mem_ae : μ.support in ae μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.norm_resolvent_le_inv_infDist_support`：norm_resolvent_le_i
nv_infDist_support {μ : Measure 𝕜} {a : A} (hz : a ∉ algebraMap 𝕜 A '' μ.support
) {x : 𝕜} (hx : x in μ.support) : ‖resolv…
-/
theorem integrable_resolvent [HereditarilyLindelofSpace 𝕜] [OpensMeasurableSpace 𝕜]
    [CompleteSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
    {μ : Measure 𝕜} [IsFiniteMeasure μ] {a : A} (hz : a ∉ algebraMap 𝕜 A '' μ.support) :
    Integrable (resolvent a) μ := by
  refine ⟨by fun_prop, ?_⟩
  apply HasFiniteIntegral.of_bounded
  filter_upwards [support_mem_ae] with x hx using norm_resolvent_le_inv_infDist_support hz hx

end resolvent

section Definition

variable [NormedField 𝕜] [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra 𝕜 A]
  {m𝕜 : MeasurableSpace 𝕜}

/-- The resolvent transform of a measure. -/
noncomputable
/-
**MeasureTheory.resolventTransform** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：resolventTransform (μ : Measure 𝕜) (a : A)
参数：μ : Measure 𝕜；a : A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def resolventTransform (μ : Measure 𝕜) (a : A) :=
  ∫ x, resolvent a x ∂μ
/-
**MeasureTheory.resolventTransform_def** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：resolventTransform_def (μ : Measure 𝕜) : resolventTransform μ = fun (a : A
) => (∫ x, resolvent a x ∂μ)
参数：μ : Measure 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma resolventTransform_def (μ : Measure 𝕜) :
    resolventTransform μ = fun (a : A) ↦ (∫ x, resolvent a x ∂μ) := by rfl
/-
**MeasureTheory.resolventTransform_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：resolventTransform_apply (μ : Measure 𝕜) (a : A) : resolventTransform μ a 
= ∫ x, resolvent a x ∂μ
参数：μ : Measure 𝕜；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma resolventTransform_apply (μ : Measure 𝕜) (a : A) :
    resolventTransform μ a = ∫ x, resolvent a x ∂μ := by rfl

@[simp]
/-
**MeasureTheory.resolventTransform_zero_measure** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory`。
形式化陈述：resolventTransform_zero_measure : resolventTransform (0 : Measure 𝕜) = (0 
: A -> A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `MeasureTheory.resolventTransform_def`：resolventTransform_def (μ : Measur
e 𝕜) : resolventTransform μ = fun (a : A) => (∫ x, resolvent a x ∂μ)
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma resolventTransform_zero_measure : resolventTransform (0 : Measure 𝕜) = (0 : A → A) := by
  ext
  simp [resolventTransform_def]

@[simp]
/-
**MeasureTheory.resolventTransform_dirac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：resolventTransform_dirac [MeasurableSingletonClass 𝕜] [CompleteSpace A] (x
 : 𝕜) (a : A) : resolventTransform (.dirac x) a = resolvent a x
参数：x : 𝕜；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `MeasureTheory.resolventTransform_def`：resolventTransform_def (μ : Measur
e 𝕜) : resolventTransform μ = fun (a : A) => (∫ x, resolvent a x ∂μ)
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma resolventTransform_dirac [MeasurableSingletonClass 𝕜] [CompleteSpace A]
    (x : 𝕜) (a : A) : resolventTransform (.dirac x) a = resolvent a x := by
  simp [resolventTransform_def]

end Definition

section Deriv

variable [NontriviallyNormedField 𝕜] [HereditarilyLindelofSpace 𝕜] [CompleteSpace 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-
**MeasureTheory.hasDerivAt_resolventTransform** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：hasDerivAt_resolventTransform [RCLike A] [NormedAlgebra 𝕜 A] {μ : Measure 
𝕜} [IsFiniteMeasure μ] (a : A) (ha : a ∉ algebraMap 𝕜 A '' μ.support) : HasDeriv
At (resolventTransform μ) (∫ x, resolvent a x ^ 2 ∂μ) a
参数：a : A；ha : a ∉ algebraMap 𝕜 A '' μ.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.resolventTransform_def`：resolventTransform_def (μ : Measur
e 𝕜) : resolventTransform μ = fun (a : A) => (∫ x, resolvent a x ∂μ)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsClosed.notMem_iff_infDist_pos`：∀ {α : Type u} [inst : PseudoMetricSpac
e α] {s : Set α} {x : α},   IsClosed s → s.Nonempty → (x ∉ s ↔ 0 < Metric.infDis
t x s)
· 使用定理 `Topology.IsClosedEmbedding.isClosed_iff_image_isClosed`：∀ {X : Type u_1}
 {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpa
ce Y],   Topology.IsClosedEmbedding f → ∀ {s…
· 使用定理 `Isometry.isClosedEmbedding`：isClosedEmbedding [CompleteSpace α] [EMetric
Space γ] {f : α -> γ} (hf : Isometry f) : IsClosedEmbedding f
· 使用定理 `algebraMap_isometry`：algebraMap_isometry [NormOneClass 𝕜'] : Isometry (a
lgebraMap 𝕜 𝕜')
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用引理 `MeasureTheory.Measure.isClosed_support`：isClosed_support {μ : Measure X}
 : IsClosed μ.support
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Metric.ball_subset_ball`：ball_subset_ball (h : ε₁ <= ε₂) : ball x ε₁ sub
seteq ball x ε₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Metric.ball_infDist_subset_compl`：ball_infDist_subset_compl : ball x (in
fDist x s) subseteq sᶜ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
（共 88 条，此处仅展示前 30 条）
-/
theorem hasDerivAt_resolventTransform [RCLike A] [NormedAlgebra 𝕜 A] {μ : Measure 𝕜}
    [IsFiniteMeasure μ] (a : A) (ha : a ∉ algebraMap 𝕜 A '' μ.support) :
    HasDerivAt (resolventTransform μ) (∫ x, resolvent a x ^ 2 ∂μ) a := by
  by_cases! h : μ.support.Nonempty; swap
  · simp [support_eq_empty_iff.mp h]
  rw [resolventTransform_def]
  have : 0 < infDist a (algebraMap 𝕜 A '' μ.support) := by
    refine (IsClosed.notMem_iff_infDist_pos ?_ (h.image _)).mp ha
    refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
    exact (algebraMap_isometry 𝕜 A).isClosedEmbedding
  let s : Set A := ball a ((infDist a (algebraMap 𝕜 A '' μ.support)) / 2)
  have hs_z : s ∈ 𝓝 a := ball_mem_nhds _ (by positivity)
  have hs_μ : s ⊆ (algebraMap 𝕜 A '' μ.support)ᶜ := by
    unfold s
    grw [ball_subset_ball, ball_infDist_subset_compl]
    grind
  have resolvent_meas : ∀ᶠ w in nhds a, AEStronglyMeasurable (resolvent w) μ := by
    filter_upwards with _ using by fun_prop
  have resolvent'_bound : ∀ᵐ x ∂μ, ∀ w ∈ s,
      ‖(resolvent w x) ^ 2‖ ≤ ((infDist a (algebraMap 𝕜 A '' μ.support)) / 2)⁻¹ ^ 2 := by
    filter_upwards [support_mem_ae] with x hx w hw
    grw [resolvent, Ring.inverse_eq_inv, norm_pow, norm_inv]
    gcongr
    calc infDist a (algebraMap 𝕜 A '' μ.support) / 2
      _ ≤ infDist a (algebraMap 𝕜 A '' μ.support)
        - infDist a (algebraMap 𝕜 A '' μ.support) / 2 := by grind
      _ ≤ ‖(algebraMap 𝕜 A) x - a‖ - ‖a - w‖ := by
        gcongr
        · grw [infDist_le_dist_of_mem (y := (algebraMap 𝕜 A) x) (by simp [hx]), dist_comm,
            dist_eq_norm]
        · apply le_of_lt
          simpa [s, ← dist_eq_norm, dist_comm w a] using hw
      _ ≤ ‖(algebraMap 𝕜 A) x - w‖ := by grw [norm_sub_le_norm_add]; grind
  have h_deriv : ∀ᵐ x ∂μ, ∀ w ∈ s, HasDerivAt (fun w ↦ resolvent w x) (resolvent w x ^ 2) w := by
    filter_upwards [support_mem_ae] with x hx w hw
    apply hasDerivAt_resolvent_const_right
    replace hw := hs_μ hw
    contrapose! hw
    rw [Set.notMem_compl_iff]
    use x, hx
    simpa [resolventSet, sub_eq_zero] using hw
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_z resolvent_meas
    (integrable_resolvent (by simp [ha])) (by fun_prop) resolvent'_bound (by fun_prop) h_deriv |>.2
/-
**MeasureTheory.analyticOn_resolventTransform** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：analyticOn_resolventTransform [NormedAlgebra 𝕜 Complex] {μ : Measure 𝕜} [I
sFiniteMeasure μ] : AnalyticOn Complex (resolventTransform μ) (algebraMap 𝕜 Comp
lex '' μ.support)ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.analyticOn_iff_differentiableOn`：analyticOn_iff_differentiableOn
 {f : Complex -> E} {s : Set Complex} (o : IsOpen s) : AnalyticOn Complex f s ↔ 
DifferentiableOn Complex f s
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsClosedEmbedding.isClosed_iff_image_isClosed`：∀ {X : Type u_1}
 {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpa
ce Y],   Topology.IsClosedEmbedding f → ∀ {s…
· 使用定理 `Isometry.isClosedEmbedding`：isClosedEmbedding [CompleteSpace α] [EMetric
Space γ] {f : α -> γ} (hf : Isometry f) : IsClosedEmbedding f
· 使用定理 `algebraMap_isometry`：algebraMap_isometry [NormOneClass 𝕜'] : Isometry (a
lgebraMap 𝕜 𝕜')
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用引理 `MeasureTheory.Measure.isClosed_support`：isClosed_support {μ : Measure X}
 : IsClosed μ.support
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `MeasureTheory.hasDerivAt_resolventTransform`：hasDerivAt_resolventTransfo
rm [RCLike A] [NormedAlgebra 𝕜 A] {μ : Measure 𝕜} [IsFiniteMeasure μ] (a : A) (h
a : a ∉ algebraMap 𝕜 A '' μ.suppo…
-/
theorem analyticOn_resolventTransform [NormedAlgebra 𝕜 ℂ] {μ : Measure 𝕜} [IsFiniteMeasure μ] :
    AnalyticOn ℂ (resolventTransform μ) (algebraMap 𝕜 ℂ '' μ.support)ᶜ := by
  rw [analyticOn_iff_differentiableOn]
  · intro z hz
    exact (hasDerivAt_resolventTransform z hz).differentiableAt.differentiableWithinAt
  apply isOpen_compl_iff.mpr
  refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
  exact (algebraMap_isometry 𝕜 ℂ).isClosedEmbedding

end Deriv

end MeasureTheory

