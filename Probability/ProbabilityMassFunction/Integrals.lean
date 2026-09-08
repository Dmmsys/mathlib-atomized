/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Integrals with a measure derived from probability mass functions.

This file connects `PMF` with `integral`. The main result is that the integral (i.e. the expected
value) with regard to a measure derived from a `PMF` is a sum weighted by the `PMF`.

It also provides the expected value for specific probability mass functions.
-/

public section

namespace PMF

open MeasureTheory NNReal ENNReal TopologicalSpace

section General

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-
**PMF.integral_eq_tsum** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：integral_eq_tsum (p : PMF α) (f : α -> E) (hf : Integrable f p.toMeasure) 
: ∫ a, f a ∂(p.toMeasure) = ∑' a, (p a).toReal • f a
参数：p : PMF α；f : α -> E；hf : Integrable f p.toMeasure。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.restrict_toMeasure_support`：restrict_toMeasure_support : p.toMeasure
.restrict p.support = p.toMeasure
· 使用定理 `MeasureTheory.setIntegral_countable`：setIntegral_countable (f : X -> E) 
{s : Set X} (hs : s.Countable) (hf : IntegrableOn f s μ) : ∫ x in s, f x ∂μ = ∑'
 x : s, μ.real {(x : X)} …
· 使用定理 `PMF.support_countable`：support_countable (p : PMF α) : p.support.Countab
le
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PMF.toMeasure_apply_singleton`：toMeasure_apply_singleton (a : α) (h : Me
asurableSet ({a} : Set α)) : p.toMeasure {a} = p a
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
· 使用定理 `tsum_subtype_eq_of_support_subset`：∀ {α : Type u_1} {β : Type u_2} [inst
 : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α} {s : Set β},   Fun
ction.support f ⊆ s → ∑…
· 使用引理 `Function.support_smul_subset_left`：support_smul_subset_left [Zero R] [Ze
ro M] [SMulWithZero R M] (f : α -> R) (g : α -> M) : support (f • g) subseteq su
pport f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_eq_tsum (p : PMF α) (f : α → E) (hf : Integrable f p.toMeasure) :
    ∫ a, f a ∂(p.toMeasure) = ∑' a, (p a).toReal • f a := calc
  _ = ∫ a in p.support, f a ∂(p.toMeasure) := by rw [restrict_toMeasure_support p]
  _ = ∑' (a : support p), (p.toMeasure {a.val}).toReal • f a := by
    apply setIntegral_countable f p.support_countable
    rwa [IntegrableOn, restrict_toMeasure_support p]
  _ = ∑' (a : support p), (p a).toReal • f a := by
    congr with x; congr 2
    apply PMF.toMeasure_apply_singleton p x (MeasurableSet.singleton _)
  _ = ∑' a, (p a).toReal • f a :=
    tsum_subtype_eq_of_support_subset <| calc
      (fun a ↦ (p a).toReal • f a).support ⊆ (fun a ↦ (p a).toReal).support :=
        Function.support_smul_subset_left _ _
      _ ⊆ support p := fun x h1 h2 => h1 (by simp [h2])
/-
**PMF.integral_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：integral_eq_sum [Fintype α] (p : PMF α) (f : α -> E) : ∫ a, f a ∂(p.toMeas
ure) = ∑ a, (p a).toReal • f a
参数：p : PMF α；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_fintype`：integral_fintype [Fintype X] (hf : Integ
rable f μ) : ∫ x, f x ∂μ = ∑ x, μ.real {x} • f x
· 使用定理 `MeasureTheory.Integrable.of_finite`：∀ {α : Type u_1} {β : Type u_2} {m :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β] 
  [Finite α] [Measurable…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `PMF.toMeasure.isProbabilityMeasure`：∀ {α : Type u_1} [inst : MeasurableS
pace α] (p : PMF α), MeasureTheory.IsProbabilityMeasure p.toMeasure
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `PMF.toMeasure_apply_singleton`：toMeasure_apply_singleton (a : α) (h : Me
asurableSet ({a} : Set α)) : p.toMeasure {a} = p a
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
-/
theorem integral_eq_sum [Fintype α] (p : PMF α) (f : α → E) :
    ∫ a, f a ∂(p.toMeasure) = ∑ a, (p a).toReal • f a := by
  rw [integral_fintype .of_finite]
  congr with x
  rw [measureReal_def]
  congr 2
  exact PMF.toMeasure_apply_singleton p x (MeasurableSet.singleton _)

end General

@[deprecated ProbabilityTheory.integral_bernoulliMeasure (since := "2026-04-07")]
/-
**PMF.bernoulli_expectation** 是 Mathlib 中的一个定理，位于命名空间 `PMF`。
形式化陈述：bernoulli_expectation {p : Real>=0} (h : p <= 1) : ∫ b, cond b 1 0 ∂((bern
oulli p h).toMeasure) = p.toReal
参数：h : p <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PMF.integral_eq_sum`：integral_eq_sum [Fintype α] (p : PMF α) (f : α -> E
) : ∫ a, f a ∂(p.toMeasure) = ∑ a, (p a).toReal • f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PMF.bernoulli_apply`：bernoulli_apply : bernoulli p h b = cond b p (1 - p
)
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bernoulli_expectation {p : ℝ≥0} (h : p ≤ 1) :
    ∫ b, cond b 1 0 ∂((bernoulli p h).toMeasure) = p.toReal := by
  simp [integral_eq_sum, bernoulli_apply]

end PMF

