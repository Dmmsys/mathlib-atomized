/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Integral with respect to a sum of measures

In this file we prove that a function `f` is integrable with respect to a countable sum of measures
`Measure.sum μ` if and only if `f` is integrable with respect to each `μ i` and the sequence
`fun i ↦ ∫ x, ‖f x‖ ∂μ i` is summable. We then show that under this integrability condition,
`∫ x, f x ∂Measure.sum μ = ∑' i, ∫ f x ∂μ i`.

We specialize these results to the case where each measure is a Dirac mass,
i.e. `μ i = (c i) • .dirac (x i)`.

Finally we compute integrals over countable and finite spaces or sets.

## Main statements

* `integrable_sum_measure_iff`: A function `f` is integrable with respect to a countable sum
  of measures `Measure.sum μ` if and only if `f` is integrable with respect to each `μ i` and the
  sequence `fun i ↦ ∫ x, ‖f x‖ ∂μ i` is summable.
* `integrable_sum_dirac_iff`: A function `f` is integrable with respect to a countable sum
  of Dirac masses `Measure.sum (fun i ↦ (c i) • Measure.dirac (x i))` if and only if
  the sequence `fun i ↦ (c i).toReal * ‖f (x i)‖` is summable.
* `hasSum_integral_measure`: If `f` is integrable with respect to `Measure.sum μ`,
  then the sequence `fun i ↦ ∫ x, f x ∂μ i` is summable and its sum is `∫ x, f x ∂Measure.sum μ`.
* `integral_sum_dirac_eq_tsum`: If the sequence `fun i ↦ (c i).toReal * ‖f (x i)‖` is summable,
  then `∑' i, (c i).toReal • f (x i) = ∫ x, f x, ∂Measure.sum (fun i ↦ (c i) • .dirac (x i))`.

## Tags

sum of measures, integral, Dirac mass
-/

public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {ι X E : Type*} [Countable ι] {mX : MeasurableSpace X} [NormedAddCommGroup E]
  {μ : ι → Measure X} {f : X → E}

section Integrable

/-
**MeasureTheory.integrable_sum_measure** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：integrable_sum_measure (hf : forall i, Integrable f (μ i)) (h : Summable (
fun i => ∫ x, ‖f x‖ ∂μ i)) : Integrable f (Measure.sum μ)
参数：hf : forall i, Integrable f (μ i)；h : Summable (fun i => ∫ x, ‖f x‖ ∂μ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `aestronglyMeasurable_sum_measure_iff`：∀ {α : Type u_1} {β : Type u_2} {ι
 : Type u_4} [Countable ι] [inst : TopologicalSpace β] {f : α → β}   [Topologica
lSpace.PseudoMetrizableSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.HasFiniteIntegral.eq_1`：∀ {α : Type u_1} {ε : Type u_4} [i
nst : ENorm ε] {x : MeasurableSpace α} (f : α → ε) (μ : MeasureTheory.Measure α)
,   MeasureTheory.HasFinit…
· 使用定理 `MeasureTheory.lintegral_sum_measure`：lintegral_sum_measure {m : Measurab
leSpace α} {ι} (f : α -> Real>=0∞) (μ : ι -> Measure α) : ∫⁻ a, f a ∂Measure.sum
 μ = ∑' i, ∫⁻ a, f a ∂μ i
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Summable.tsum_ofReal_lt_top`：Summable.tsum_ofReal_lt_top {f : α -> Real}
 (hf : Summable f) : ∑' i, .ofReal (f i) < ∞
-/
lemma integrable_sum_measure
    (hf : ∀ i, Integrable f (μ i)) (h : Summable (fun i ↦ ∫ x, ‖f x‖ ∂μ i)) :
    Integrable f (Measure.sum μ) := by
  refine ⟨aestronglyMeasurable_sum_measure_iff.mpr fun i ↦ (hf i).aestronglyMeasurable, ?_⟩
  · rw [HasFiniteIntegral, lintegral_sum_measure]
    convert! h.tsum_ofReal_lt_top with i
    rw [ofReal_integral_eq_lintegral_ofReal (hf i).norm]
    · simp_rw [ofReal_norm]
    · exact ae_of_all _ fun _ ↦ by positivity

omit [Countable ι] in
/-
**MeasureTheory.Integrable.summable_integral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Integrable`。
形式化陈述：∀ {ι : Type u_1} {X : Type u_2} {E : Type u_3} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   {μ : ι → MeasureTheory.Measure X} {f : X → E},   M
easureTheory.Integrable f (MeasureTheory.Measure.sum μ) → Summable fun i => ∫ (x
 : X), ‖f x‖ ∂μ i
参数：MeasureTheory.Measure.sum μ；x : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_toReal`：integral_toReal {f : α -> Real>=0∞} (hfm 
: AEMeasurable f μ) (hf : forallᵐ x ∂μ, f x < ∞) : ∫ a, (f a).toReal ∂μ = (∫⁻ a,
 f a ∂μ).toReal
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_measure`：mono_measure {ν : Measu
re α} (hf : AEStronglyMeasurable[m] f μ) (h : ν <= μ) : AEStronglyMeasurable[m] 
f ν
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.Measure.le_sum`：le_sum (μ : ι -> Measure α) (i : ι) : μ i 
<= sum μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `toReal_enorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ‖x
‖ₑ.toReal = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.summable_toReal`：summable_toReal {f : α -> Real>=0∞} (hsum : ∑' 
x, f x != ∞) : Summable fun x => (f x).toReal
· 使用定理 `MeasureTheory.lintegral_sum_measure`：lintegral_sum_measure {m : Measurab
leSpace α} {ι} (f : α -> Real>=0∞) (μ : ι -> Measure α) : ∫⁻ a, f a ∂Measure.sum
 μ = ∑' i, ∫⁻ a, f a ∂μ i
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma Integrable.summable_integral (hf : Integrable f (Measure.sum μ)) :
    Summable (fun i ↦ ∫ x, ‖f x‖ ∂μ i) := by
  convert! ENNReal.summable_toReal (f := fun i ↦ ∫⁻ x, ‖f x‖ₑ ∂μ i) ?_ with i
  · rw [← integral_toReal ?_ (by simp)]
    · simp
    · exact (hf.aestronglyMeasurable.mono_measure (Measure.le_sum _ i)).enorm
  rw [← lintegral_sum_measure]
  exact hf.2.ne

/-- A function `f` is integrable with respect to a countable sum of measures `Measure.sum μ`
if and only if `f` is integrable with respect to each `μ i` and
the sequence `fun i ↦ ∫ x, ‖f x‖ ∂μ i` is summable. -/
/-
**MeasureTheory.integrable_sum_measure_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：integrable_sum_measure_iff : Integrable f (Measure.sum μ) ↔ (forall i, Int
egrable f (μ i)) ∧ Summable (fun i => ∫ x, ‖f x‖ ∂μ i) where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `MeasureTheory.Measure.le_sum`：le_sum (μ : ι -> Measure α) (i : ι) : μ i 
<= sum μ
· 使用定理 `MeasureTheory.Integrable.summable_integral`：∀ {ι : Type u_1} {X : Type u
_2} {E : Type u_3} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E]   {μ :
 ι → MeasureTheory.Measure X} {f…
· 使用引理 `MeasureTheory.integrable_sum_measure`：integrable_sum_measure (hf : foral
l i, Integrable f (μ i)) (h : Summable (fun i => ∫ x, ‖f x‖ ∂μ i)) : Integrable 
f (Measure.sum μ)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A function `f` is integrable with respect to a countable sum of measures `Measur
e.sum μ`
if and only if `f` is integrable with respect to each `μ i` and
the sequence `fun i ↦ ∫ x, ‖f x‖ ∂μ i` is summable.
-/
lemma integrable_sum_measure_iff :
    Integrable f (Measure.sum μ) ↔
      (∀ i, Integrable f (μ i)) ∧ Summable (fun i ↦ ∫ x, ‖f x‖ ∂μ i) where
  mp h := ⟨fun i ↦ h.mono_measure (Measure.le_sum _ i), h.summable_integral⟩
  mpr h := integrable_sum_measure h.1 h.2

section Dirac

variable [MeasurableSingletonClass X] {x : ι → X} {c : ι → ℝ≥0∞}

/-
**MeasureTheory.integrable_sum_dirac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_sum_dirac (hc : forall i, c i != ∞) (h : Summable (fun i => (c 
i).toReal * ‖f (x i)‖)) : Integrable f (Measure.sum (fun i => (c i) • .dirac (x 
i)))
参数：hc : forall i, c i != ∞；h : Summable (fun i => (c i).toReal * ‖f (x i)‖)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integrable_sum_measure`：integrable_sum_measure (hf : foral
l i, Integrable f (μ i)) (h : Summable (fun i => ∫ x, ‖f x‖ ∂μ i)) : Integrable 
f (Measure.sum μ)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Integrable.smul_measure`：∀ {α : Type u_1} {m : MeasurableS
pace α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]
   [inst_1 : ESeminormedAdd…
· 使用引理 `MeasureTheory.integrable_dirac`：integrable_dirac [MeasurableSingletonCla
ss α] {a : α} {f : α -> ε} (hfa : ‖f a‖ₑ < ∞) : Integrable f (Measure.dirac a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
-/
lemma integrable_sum_dirac (hc : ∀ i, c i ≠ ∞) (h : Summable (fun i ↦ (c i).toReal * ‖f (x i)‖)) :
    Integrable f (Measure.sum (fun i ↦ (c i) • .dirac (x i))) :=
  integrable_sum_measure (fun i ↦ (integrable_dirac (by simp)).smul_measure (hc i))
    (by simpa using h)

omit [Countable ι] in
/-
**MeasureTheory.Integrable.summable_of_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Integrable`。
形式化陈述：∀ {ι : Type u_1} {X : Type u_2} {E : Type u_3} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E] {f : X → E}   [MeasurableSingletonClass X] {x : ι → 
X} {c : ι → ENNReal},   MeasureTheory.Integrable f (MeasureTheory.Measure.sum fu
n i => c i • MeasureTheory.Measure.dirac (x i)) →     Summable fun i => (c i).to
Real * ‖f (x i)‖
参数：MeasureTheory.Measure.sum fun i => c i • MeasureTheory.Measure.dirac (x i)；c 
i；x i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `MeasureTheory.Integrable.summable_integral`：∀ {ι : Type u_1} {X : Type u
_2} {E : Type u_3} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E]   {μ :
 ι → MeasureTheory.Measure X} {f…
-/
lemma Integrable.summable_of_dirac
    (hf : Integrable f (Measure.sum (fun i ↦ (c i) • .dirac (x i)))) :
    Summable (fun i ↦ (c i).toReal * ‖f (x i)‖) := by
  simpa using hf.summable_integral

/-- A function `f` is integrable with respect to a countable sum of
Dirac masses `Measure.sum (fun i ↦ (c i) • Measure.dirac (x i))` if and only if
the sequence `fun i ↦ (c i).toReal * ‖f (x i)‖` is summable. -/
/-
**MeasureTheory.integrable_sum_dirac_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integrable_sum_dirac_iff (hc : forall i, c i != ∞) : Integrable f (Measure
.sum (fun i => (c i) • .dirac (x i))) ↔ Summable (fun i => (c i).toReal * ‖f (x 
i)‖) where mp h
参数：hc : forall i, c i != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Integrable.summable_of_dirac`：∀ {ι : Type u_1} {X : Type u
_2} {E : Type u_3} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E] {f : X
 → E}   [MeasurableSingletonClas…
· 使用引理 `MeasureTheory.integrable_sum_dirac`：integrable_sum_dirac (hc : forall i,
 c i != ∞) (h : Summable (fun i => (c i).toReal * ‖f (x i)‖)) : Integrable f (Me
asure.sum (fun i => (c i…

--- 原说明 ---
A function `f` is integrable with respect to a countable sum of
Dirac masses `Measure.sum (fun i ↦ (c i) • Measure.dirac (x i))` if and only if
the sequence `fun i ↦ (c i).toReal * ‖f (x i)‖` is summable.
-/
lemma integrable_sum_dirac_iff (hc : ∀ i, c i ≠ ∞) :
    Integrable f (Measure.sum (fun i ↦ (c i) • .dirac (x i))) ↔
      Summable (fun i ↦ (c i).toReal * ‖f (x i)‖) where
  mp h := h.summable_of_dirac
  mpr h := integrable_sum_dirac hc h

end Dirac

end Integrable

section Integral

variable [NormedSpace ℝ E]

omit [Countable ι] in
/-- If `f` is integrable with respect to `Measure.sum μ`, then the sequence
`fun i ↦ ∫ x, f x ∂μ i` is summable and its sum is `∫ x, f x ∂Measure.sum μ`. -/
/-
**MeasureTheory.hasSum_integral_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：hasSum_integral_measure (hf : Integrable f (Measure.sum μ)) : HasSum (fun 
i => ∫ x, f x ∂μ i) (∫ x, f x ∂Measure.sum μ)
参数：hf : Integrable f (Measure.sum μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `MeasureTheory.Measure.le_sum`：le_sum (μ : ι -> Measure α) (i : ι) : μ i 
<= sum μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_finsetSum_measure`：integral_finsetSum_measure {ι}
 {m : MeasurableSpace α} {f : α -> G} {μ : ι -> Measure α} {s : Finset ι} (hf : 
forall i in s, Integrable f (μ…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `lt_mem_nhds`：lt_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : foral
lᶠ x in 𝓝 b, a < x
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_ne_zero`：∀ {r : NNReal}, ↑r ≠ 0 ↔ r ≠ 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `MeasureTheory.hasSum_lintegral_measure`：hasSum_lintegral_measure {ι} {_ 
: MeasurableSpace α} (f : α -> Real>=0∞) (μ : ι -> Measure α) : HasSum (fun i =>
 ∫⁻ a, f a ∂μ i) (∫⁻ a, f a …
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is integrable with respect to `Measure.sum μ`, then the sequence
`fun i ↦ ∫ x, f x ∂μ i` is summable and its sum is `∫ x, f x ∂Measure.sum μ`.
-/
theorem hasSum_integral_measure (hf : Integrable f (Measure.sum μ)) :
    HasSum (fun i ↦ ∫ x, f x ∂μ i) (∫ x, f x ∂Measure.sum μ) := by
  have hfi : ∀ i, Integrable f (μ i) := fun i ↦ hf.mono_measure (Measure.le_sum _ _)
  simp only [HasSum, ← integral_finsetSum_measure fun i _ ↦ hfi i]
  refine Metric.nhds_basis_ball.tendsto_right_iff.mpr fun ε ε0 ↦ ?_
  lift ε to ℝ≥0 using ε0.le
  have hf_lt : (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ) < ∞ := hf.2
  have hmem : ∀ᶠ y in 𝓝 (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ), (∫⁻ x, ‖f x‖ₑ ∂Measure.sum μ) < y + ε := by
    refine tendsto_id.add tendsto_const_nhds (lt_mem_nhds (α := ℝ≥0∞) <| ENNReal.lt_add_right ?_ ?_)
    exacts [hf_lt.ne, ENNReal.coe_ne_zero.2 (NNReal.coe_ne_zero.1 ε0.ne')]
  refine ((hasSum_lintegral_measure (fun x ↦ ‖f x‖ₑ) μ).eventually hmem).mono fun s hs ↦ ?_
  obtain ⟨ν, hν⟩ : ∃ ν, (∑ i ∈ s, μ i) + ν = Measure.sum μ := by
    refine ⟨Measure.sum fun i : ↥(sᶜ : Set ι) ↦ μ i, ?_⟩
    simpa only [← Measure.sum_coe_finset] using! Measure.sum_add_sum_compl (s : Set ι) μ
  rw [Metric.mem_ball, ← coe_nndist, NNReal.coe_lt_coe, ← ENNReal.coe_lt_coe, ← hν]
  rw [← hν, integrable_add_measure] at hf
  refine (nndist_integral_add_measure_le_lintegral hf.1 hf.2).trans_lt ?_
  rw [← hν, lintegral_add_measure, lintegral_finsetSum_measure] at hs
  exact lt_of_add_lt_add_left hs

omit [Countable ι] in
/-
**MeasureTheory.integral_sum_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_sum_measure (hf : Integrable f (Measure.sum μ)) : ∫ x, f x ∂Measu
re.sum μ = ∑' i, ∫ x, f x ∂μ i
参数：hf : Integrable f (Measure.sum μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `MeasureTheory.hasSum_integral_measure`：hasSum_integral_measure (hf : Int
egrable f (Measure.sum μ)) : HasSum (fun i => ∫ x, f x ∂μ i) (∫ x, f x ∂Measure.
sum μ)
-/
theorem integral_sum_measure (hf : Integrable f (Measure.sum μ)) :
    ∫ x, f x ∂Measure.sum μ = ∑' i, ∫ x, f x ∂μ i :=
  (hasSum_integral_measure hf).tsum_eq.symm

section Dirac

variable [MeasurableSingletonClass X] {x : ι → X} {c : ι → ℝ≥0∞}

/-
**MeasureTheory.integral_sum_dirac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_sum_dirac [FiniteDimensional Real E] (hc : forall i, c i != ∞) : 
∫ x, f x ∂Measure.sum (fun i => (c i) • .dirac (x i)) = ∑' i, (c i).toReal • f (
x i)
参数：hc : forall i, c i != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_sum_measure`：integral_sum_measure (hf : Integrabl
e f (Measure.sum μ)) : ∫ x, f x ∂Measure.sum μ = ∑' i, ∫ x, f x ∂μ i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `tsum_eq_zero_of_not_summable`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → 
α}, ¬Summable f L …
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Summable.norm`：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]   {f : α → E}, Summable 
f →…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `ENNReal.abs_toReal`：abs_toReal {x : Real>=0∞} : |x.toReal| = x.toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.integrable_sum_dirac`：integrable_sum_dirac (hc : forall i,
 c i != ∞) (h : Summable (fun i => (c i).toReal * ‖f (x i)‖)) : Integrable f (Me
asure.sum (fun i => (c i…
-/
lemma integral_sum_dirac [FiniteDimensional ℝ E] (hc : ∀ i, c i ≠ ∞) :
    ∫ x, f x ∂Measure.sum (fun i ↦ (c i) • .dirac (x i)) = ∑' i, (c i).toReal • f (x i) := by
  by_cases hf : Integrable f (.sum (fun i ↦ (c i) • .dirac (x i)))
  · rw [integral_sum_measure hf]
    congr with i
    rw [integral_smul_measure, integral_dirac]
  · rw [integral_undef hf, tsum_eq_zero_of_not_summable]
    apply mt Summable.norm
    convert! mt (integrable_sum_dirac hc) hf
    simp [norm_smul]
/-
**MeasureTheory.hasSum_integral_sum_dirac** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：hasSum_integral_sum_dirac [CompleteSpace E] (hc : forall i, c i != ∞) (hf 
: Summable (fun i => (c i).toReal * ‖f (x i)‖)) : HasSum (fun i => (c i).toReal 
• f (x i)) (∫ x, f x ∂Measure.sum (fun i => (c i) • .dirac (x i)))
参数：hc : forall i, c i != ∞；hf : Summable (fun i => (c i).toReal * ‖f (x i)‖)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `MeasureTheory.hasSum_integral_measure`：hasSum_integral_measure (hf : Int
egrable f (Measure.sum μ)) : HasSum (fun i => ∫ x, f x ∂μ i) (∫ x, f x ∂Measure.
sum μ)
· 使用引理 `MeasureTheory.integrable_sum_dirac`：integrable_sum_dirac (hc : forall i,
 c i != ∞) (h : Summable (fun i => (c i).toReal * ‖f (x i)‖)) : Integrable f (Me
asure.sum (fun i => (c i…
-/
lemma hasSum_integral_sum_dirac [CompleteSpace E] (hc : ∀ i, c i ≠ ∞)
    (hf : Summable (fun i ↦ (c i).toReal * ‖f (x i)‖)) :
    HasSum (fun i ↦ (c i).toReal • f (x i))
      (∫ x, f x ∂Measure.sum (fun i ↦ (c i) • .dirac (x i))) := by
  simpa using hasSum_integral_measure (integrable_sum_dirac hc hf)

/-- If the sequence `fun i ↦ (c i).toReal * ‖f (x i)‖` is summable, then
`∫ x, f x, ∂Measure.sum (fun i ↦ (c i) • .dirac (x i)) = ∑' i, (c i).toReal • f (x i)`. -/
/-
**MeasureTheory.integral_sum_dirac_eq_tsum** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：integral_sum_dirac_eq_tsum [CompleteSpace E] (hc : forall i, c i != ∞) (hf
 : Summable (fun i => (c i).toReal * ‖f (x i)‖)) : ∫ x, f x ∂Measure.sum (fun i 
=> (c i) • .dirac (x i)) = ∑' i, (c i).toReal • f (x i)
参数：hc : forall i, c i != ∞；hf : Summable (fun i => (c i).toReal * ‖f (x i)‖)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `MeasureTheory.hasSum_integral_sum_dirac`：hasSum_integral_sum_dirac [Comp
leteSpace E] (hc : forall i, c i != ∞) (hf : Summable (fun i => (c i).toReal * ‖
f (x i)‖)) : HasSum (fun i =>…

--- 原说明 ---
If the sequence `fun i ↦ (c i).toReal * ‖f (x i)‖` is summable, then
`∫ x, f x, ∂Measure.sum (fun i ↦ (c i) • .dirac (x i)) = ∑' i, (c i).toReal • f 
(x i)`.
-/
lemma integral_sum_dirac_eq_tsum [CompleteSpace E] (hc : ∀ i, c i ≠ ∞)
    (hf : Summable (fun i ↦ (c i).toReal * ‖f (x i)‖)) :
    ∫ x, f x ∂Measure.sum (fun i ↦ (c i) • .dirac (x i)) = ∑' i, (c i).toReal • f (x i) :=
  (hasSum_integral_sum_dirac hc hf).tsum_eq.symm

end Dirac

section DiscreteSpace

variable [CompleteSpace E] [MeasurableSingletonClass X] {μ : Measure X}

/-
**MeasureTheory.integral_countable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_countable [Countable X] (hf : Integrable f μ) : ∫ x, f x ∂μ = ∑' 
x, μ.real {x} • f x
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.sum_smul_dirac`：sum_smul_dirac [Countable α] [Meas
urableSingletonClass α] (μ : Measure α) : (sum fun a => μ {a} • dirac a) = μ
· 使用定理 `MeasureTheory.integral_sum_measure`：integral_sum_measure (hf : Integrabl
e f (Measure.sum μ)) : ∫ x, f x ∂Measure.sum μ = ∑' i, ∫ x, f x ∂μ i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
-/
theorem integral_countable [Countable X] (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑' x, μ.real {x} • f x := by
  rw [← Measure.sum_smul_dirac μ] at hf
  rw [← Measure.sum_smul_dirac μ, integral_sum_measure hf]
  congr 1 with a : 1
  rw [integral_smul_measure, integral_dirac, Measure.sum_smul_dirac, measureReal_def]

@[deprecated (since := "2026-03-09")] alias integral_countable' := integral_countable
/-
**MeasureTheory.setIntegral_countable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_countable (f : X -> E) {s : Set X} (hs : s.Countable) (hf : In
tegrableOn f s μ) : ∫ x in s, f x ∂μ = ∑' x : s, μ.real {(x : X)} • f x
参数：f : X -> E；hs : s.Countable；hf : IntegrableOn f s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.countable_coe_iff`：countable_coe_iff {s : Set α} : Countable s ↔ s.C
ountable
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_comap_subtype_coe`：map_comap_subtype_coe {m0 : MeasurableSpace α} {s
 : Set α} (hs : MeasurableSet s) (μ : Measure α) : (comap (↑) μ).map ((↑) : s ->
 α) = μ.res…
· 使用定理 `Set.Countable.measurableSet`：Set.Countable.measurableSet {s : Set α} (hs
 : s.Countable) : MeasurableSet s
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
· 使用定理 `MeasureTheory.integral_subtype_comap`：integral_subtype_comap {α} [Measur
ableSpace α] {μ : Measure α} {s : Set α} (hs : MeasurableSet s) (f : α -> G) : ∫
 x : s, f (x : α) ∂(Measur…
· 使用定理 `MeasureTheory.integral_countable`：integral_countable [Countable X] (hf :
 Integrable f μ) : ∫ x, f x ∂μ = ∑' x, μ.real {x} • f x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `MeasureTheory.Measure.comap_apply`：comap_apply (f : α -> β) (hfi : Injec
tive f) (hf : forall s, MeasurableSet s -> MeasurableSet (f '' s)) (μ : Measure 
β) (hs : MeasurableSet …
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `MeasurableSet.subtype_image`：MeasurableSet.subtype_image {s : Set α} {t 
: Set s} (hs : MeasurableSet s) : MeasurableSet t -> MeasurableSet (((↑) : s -> 
α) '' t)
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setIntegral_countable (f : X → E) {s : Set X} (hs : s.Countable) (hf : IntegrableOn f s μ) :
    ∫ x in s, f x ∂μ = ∑' x : s, μ.real {(x : X)} • f x := by
  have hi : Countable { x // x ∈ s } := Iff.mpr countable_coe_iff hs
  have hf' : Integrable (fun (x : s) ↦ f x) (Measure.comap Subtype.val μ) := by
    rw [IntegrableOn, ← map_comap_subtype_coe, integrable_map_measure] at hf
    · apply hf
    · exact Integrable.aestronglyMeasurable hf
    · exact Measurable.aemeasurable measurable_subtype_coe
    · exact Countable.measurableSet hs
  rw [← integral_subtype_comap hs.measurableSet, integral_countable hf']
  congr 1 with a : 1
  rw [measureReal_def, Measure.comap_apply Subtype.val Subtype.coe_injective
    (fun s' hs' ↦ MeasurableSet.subtype_image (Countable.measurableSet hs) hs') _
    (MeasurableSet.singleton a)]
  simp [measureReal_def]
/-
**MeasureTheory.setIntegral_finset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_finset (s : Finset X) (hf : IntegrableOn f s μ) : ∫ x in s, f 
x ∂μ = ∑ x in s, μ.real {x} • f x
参数：s : Finset X；hf : IntegrableOn f s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setIntegral_countable`：setIntegral_countable (f : X -> E) 
{s : Set X} (hs : s.Countable) (hf : IntegrableOn f s μ) : ∫ x in s, f x ∂μ = ∑'
 x : s, μ.real {(x : X)} …
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.tsum_subtype'`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMon
oid α] [inst_1 : TopologicalSpace α] (s : Finset β) (f : β → α),   ∑' (x : ↑↑s),
 f ↑x = ∑ …
-/
theorem setIntegral_finset (s : Finset X) (hf : IntegrableOn f s μ) :
    ∫ x in s, f x ∂μ = ∑ x ∈ s, μ.real {x} • f x := by
  rw [setIntegral_countable _ s.countable_toSet hf, ← Finset.tsum_subtype']

@[deprecated (since := "2026-03-09")] alias integral_finset := setIntegral_finset
/-
**MeasureTheory.integral_fintype** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_fintype [Fintype X] (hf : Integrable f μ) : ∫ x, f x ∂μ = ∑ x, μ.
real {x} • f x
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_finset`：setIntegral_finset (s : Finset X) (hf 
: IntegrableOn f s μ) : ∫ x in s, f x ∂μ = ∑ x in s, μ.real {x} • f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
-/
theorem integral_fintype [Fintype X] (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ x, μ.real {x} • f x := by
  -- NB: Integrable f does not follow from Fintype, because the measure itself could be non-finite
  rw [← setIntegral_finset .univ, Finset.coe_univ, Measure.restrict_univ]
  simp [Finset.coe_univ, hf]
/-
**MeasureTheory.integral_count** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {X : Type u_2} {E : Type u_3} {mX : MeasurableSpace X} [inst : NormedAdd
CommGroup E] [inst_1 : NormedSpace ℝ E]   [CompleteSpace E] [MeasurableSingleton
Class X] [inst_4 : Fintype X] (f : X → E),   ∫ (x : X), f x ∂MeasureTheory.Measu
re.count = ∑ a, f a
参数：f : X → E；x : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_fintype`：integral_fintype [Fintype X] (hf : Integ
rable f μ) : ∫ x, f x ∂μ = ∑ x, μ.real {x} • f x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.count.isFiniteMeasure`：∀ {α : Type u_1} [inst : Me
asurableSpace α] [Finite α], MeasureTheory.IsFiniteMeasure MeasureTheory.Measure
.count
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.count_real_singleton'`：∀ {α : Type u_1} [inst : Measurable
Space α] {a : α}, MeasurableSet {a} → MeasureTheory.Measure.count.real {a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma integral_count [Fintype X] (f : X → E) :
    ∫ x, f x ∂.count = ∑ a, f a := by simp [integral_fintype]

end DiscreteSpace

end Integral

end MeasureTheory

