/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Kullback-Leibler divergence

The Kullback-Leibler divergence is a measure of the difference between two measures.

## Main definitions

* `klDiv μ ν`: Kullback-Leibler divergence between two measures, with value in `ℝ≥0∞`,
  defined as `∞` if `μ` is not absolutely continuous with respect to `ν` or
  if the log-likelihood ratio `llr μ ν` is not integrable with respect to `μ`, and by
  `ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real - μ.real univ)` otherwise.

Note that our Kullback-Leibler divergence is nonnegative by definition (it takes value in `ℝ≥0∞`).
However `∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ` is nonnegative for all finite
measures `μ ≪ ν`, as proved in the lemma `integral_llr_add_sub_measure_univ_nonneg`.
That lemma is our version of Gibbs' inequality ("the Kullback-Leibler divergence is nonnegative").

## Main statements

* `klDiv_eq_zero_iff` : the Kullback-Leibler divergence between two finite measures is zero if and
  only if the two measures are equal.

## Implementation details

The Kullback-Leibler divergence on probability measures is `∫ x, llr μ ν x ∂μ` if `μ ≪ ν`
(and the log-likelihood ratio is integrable) and `∞` otherwise.
The definition we use extends this to finite measures by introducing a correction term
`ν.real univ - μ.real univ`. The definition of the divergence thus uses the formula
`∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ`, which is nonnegative for all finite
measures `μ ≪ ν`. This also makes `klDiv μ ν` equal to an f-divergence: it equals the integral
`∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν`, in which `klFun x = x * log x + 1 - x`.

-/

@[expose] public section

open Real MeasureTheory Set

open scoped ENNReal NNReal

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

open scoped Classical in
/-- Kullback-Leibler divergence between two measures. -/
noncomputable irreducible_def klDiv (μ ν : Measure α) : ℝ≥0∞ :=
  if μ ≪ ν ∧ Integrable (llr μ ν) μ
    then ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ)
    else ∞

/-
**InformationTheory.klDiv_of_ac_of_integrable** 是 Mathlib 中的一个引理，位于命名空间 `Informa
tionTheory`。
形式化陈述：klDiv_of_ac_of_integrable (h1 : μ ≪ ν) (h2 : Integrable (llr μ ν) μ) : klD
iv μ ν = ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ)
参数：h1 : μ ≪ ν；h2 : Integrable (llr μ ν) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InformationTheory.klDiv_def`：∀ {α : Type u_2} {mα : MeasurableSpace α} (
μ ν : MeasureTheory.Measure α),   InformationTheory.klDiv μ ν =     if μ.Absolut
elyContinuous ν ∧…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma klDiv_of_ac_of_integrable (h1 : μ ≪ ν) (h2 : Integrable (llr μ ν) μ) :
    klDiv μ ν = ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ) := by
  rw [klDiv_def]
  exact if_pos ⟨h1, h2⟩

@[simp]
/-
**InformationTheory.klDiv_of_not_ac** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheory
`。
形式化陈述：klDiv_of_not_ac (h : ¬ μ ≪ ν) : klDiv μ ν = ∞
参数：h : ¬ μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InformationTheory.klDiv_def`：∀ {α : Type u_2} {mα : MeasurableSpace α} (
μ ν : MeasureTheory.Measure α),   InformationTheory.klDiv μ ν =     if μ.Absolut
elyContinuous ν ∧…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `not_and_of_not_left`：∀ {a : Prop} (b : Prop), ¬a → ¬(a ∧ b)
-/
lemma klDiv_of_not_ac (h : ¬ μ ≪ ν) : klDiv μ ν = ∞ := by
  rw [klDiv_def]
  exact if_neg (not_and_of_not_left _ h)

@[simp]
/-
**InformationTheory.klDiv_of_not_integrable** 是 Mathlib 中的一个引理，位于命名空间 `Informati
onTheory`。
形式化陈述：klDiv_of_not_integrable (h : ¬ Integrable (llr μ ν) μ) : klDiv μ ν = ∞
参数：h : ¬ Integrable (llr μ ν) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InformationTheory.klDiv_def`：∀ {α : Type u_2} {mα : MeasurableSpace α} (
μ ν : MeasureTheory.Measure α),   InformationTheory.klDiv μ ν =     if μ.Absolut
elyContinuous ν ∧…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `not_and_of_not_right`：∀ (a : Prop) {b : Prop}, ¬b → ¬(a ∧ b)
-/
lemma klDiv_of_not_integrable (h : ¬ Integrable (llr μ ν) μ) : klDiv μ ν = ∞ := by
  rw [klDiv_def]
  exact if_neg (not_and_of_not_right _ h)

@[simp]
/-
**InformationTheory.klDiv_self** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheory`。
形式化陈述：klDiv_self (μ : Measure α) [SigmaFinite μ] : klDiv μ μ = 0
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.llr_self`：llr_self (μ : Measure α) [SigmaFinite μ] : llr μ
 μ =ᵐ[μ] 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InformationTheory.klDiv_def`：∀ {α : Type u_2} {mα : MeasurableSpace α} (
μ ν : MeasureTheory.Measure α),   InformationTheory.klDiv μ ν =     if μ.Absolut
elyContinuous ν ∧…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma klDiv_self (μ : Measure α) [SigmaFinite μ] : klDiv μ μ = 0 := by
  have h := llr_self μ
  rw [klDiv_def, if_pos]
  · simp [integral_congr_ae h]
  · rw [integrable_congr h]
    exact ⟨Measure.AbsolutelyContinuous.rfl, integrable_zero _ _ μ⟩

@[simp]
/-
**InformationTheory.klDiv_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheory
`。
形式化陈述：klDiv_zero_left [IsFiniteMeasure ν] : klDiv 0 ν = ν univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `MeasureTheory.ofReal_measureReal`：ofReal_measureReal (h : μ s != ∞
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `InformationTheory.klDiv_of_ac_of_integrable`：klDiv_of_ac_of_integrable (
h1 : μ ≪ ν) (h2 : Integrable (llr μ ν) μ) : klDiv μ ν = ENNReal.ofReal (∫ x, llr
 μ ν x ∂μ + ν.real univ - μ.real …
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.zero`：∀ {α : Type u_1} {mα : 
MeasurableSpace α} (μ : MeasureTheory.Measure α), MeasureTheory.Measure.Absolute
lyContinuous 0 μ
· 使用定理 `MeasureTheory.integrable_zero_measure`：integrable_zero_measure {f : α ->
 ε} : Integrable f (0 : Measure α)
-/
lemma klDiv_zero_left [IsFiniteMeasure ν] : klDiv 0 ν = ν univ := by
  convert! klDiv_of_ac_of_integrable (Measure.AbsolutelyContinuous.zero _) integrable_zero_measure
  simp

@[simp]
/-
**InformationTheory.klDiv_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheor
y`。
形式化陈述：klDiv_zero_right [NeZero μ] : klDiv μ 0 = ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `InformationTheory.klDiv_of_not_ac`：klDiv_of_not_ac (h : ¬ μ ≪ ν) : klDiv
 μ ν = ∞
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_zero_iff`：absolutelyContinuou
s_zero_iff : μ ≪ 0 ↔ μ = 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
lemma klDiv_zero_right [NeZero μ] : klDiv μ 0 = ∞ :=
  klDiv_of_not_ac (Measure.absolutelyContinuous_zero_iff.mp.mt (NeZero.ne _))
/-
**InformationTheory.klDiv_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheor
y`。
形式化陈述：klDiv_eq_top_iff : klDiv μ ν = ∞ ↔ μ ≪ ν -> ¬ Integrable (llr μ ν) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `InformationTheory.klDiv_of_ac_of_integrable`：klDiv_of_ac_of_integrable (
h1 : μ ≪ ν) (h2 : Integrable (llr μ ν) μ) : klDiv μ ν = ENNReal.ofReal (∫ x, llr
 μ ν x ∂μ + ν.real univ - μ.real …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_not_of_imp`：or_not_of_imp : (a -> b) -> b ∨ ¬a
· 使用引理 `InformationTheory.klDiv_of_not_integrable`：klDiv_of_not_integrable (h : 
¬ Integrable (llr μ ν) μ) : klDiv μ ν = ∞
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `InformationTheory.klDiv_of_not_ac`：klDiv_of_not_ac (h : ¬ μ ≪ ν) : klDiv
 μ ν = ∞
-/
lemma klDiv_eq_top_iff : klDiv μ ν = ∞ ↔ μ ≪ ν → ¬ Integrable (llr μ ν) μ := by
  constructor <;> intro h
  · contrapose! h
    simp [klDiv_of_ac_of_integrable h.1 h.2]
  · rcases or_not_of_imp h with (h | h) <;> simp [h]
/-
**InformationTheory.klDiv_ne_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheor
y`。
形式化陈述：klDiv_ne_top_iff : klDiv μ ν != ∞ ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma klDiv_ne_top_iff : klDiv μ ν ≠ ∞ ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ := by
  simp [ne_eq, klDiv_eq_top_iff]
/-
**InformationTheory.klDiv_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheory`。
形式化陈述：klDiv_ne_top (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : klDiv μ ν !=
 ∞
参数：hμν : μ ≪ ν；h_int : Integrable (llr μ ν) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `InformationTheory.klDiv_ne_top_iff`：klDiv_ne_top_iff : klDiv μ ν != ∞ ↔ 
μ ≪ ν ∧ Integrable (llr μ ν) μ
-/
lemma klDiv_ne_top (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : klDiv μ ν ≠ ∞ :=
  klDiv_ne_top_iff.mpr ⟨hμν, h_int⟩

section AlternativeFormulas

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

open scoped Classical in
/-
**InformationTheory.klDiv_eq_integral_klFun** 是 Mathlib 中的一个引理，位于命名空间 `Informati
onTheory`。
形式化陈述：klDiv_eq_integral_klFun : klDiv μ ν = if μ ≪ ν ∧ Integrable (llr μ ν) μ th
en ENNReal.ofReal (∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν) else ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InformationTheory.klDiv_def`：∀ {α : Type u_2} {mα : MeasurableSpace α} (
μ ν : MeasureTheory.Measure α),   InformationTheory.klDiv μ ν =     if μ.Absolut
elyContinuous ν ∧…
· 使用定理 `if_ctx_congr`：if_ctx_congr (h_c : P ↔ Q) (h_t : Q -> x = u) (h_e : ¬Q ->
 y = v) : ite P x y = ite Q u v
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `InformationTheory.integral_klFun_rnDeriv`：integral_klFun_rnDeriv (hμν : 
μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν =
 ∫ x, llr μ ν x ∂μ + ν.real un…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma klDiv_eq_integral_klFun :
    klDiv μ ν = if μ ≪ ν ∧ Integrable (llr μ ν) μ
      then ENNReal.ofReal (∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν)
      else ∞ := by
  rw [klDiv_def]
  exact if_ctx_congr Iff.rfl (fun h ↦ by rw [integral_klFun_rnDeriv h.1 h.2]) fun _ ↦ rfl

open scoped Classical in
/-
**InformationTheory.klDiv_eq_lintegral_klFun** 是 Mathlib 中的一个引理，位于命名空间 `Informat
ionTheory`。
形式化陈述：klDiv_eq_lintegral_klFun : klDiv μ ν = if μ ≪ ν then ∫⁻ x, ENNReal.ofReal 
(klFun (μ.rnDeriv ν x).toReal) ∂ν else ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InformationTheory.klDiv_eq_integral_klFun`：klDiv_eq_integral_klFun : klD
iv μ ν = if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, klFun (μ.rn
Deriv ν x).toReal ∂ν) else ∞
· 使用引理 `MeasureTheory.lintegral_ofReal_ne_top_iff_integrable`：lintegral_ofReal_n
e_top_iff_integrable {f : α -> Real} (hfm : AEStronglyMeasurable f μ) (hf : 0 <=
ᵐ[μ] f) : ∫⁻ a, ENNReal.ofReal (f a) ∂μ !=…
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用引理 `InformationTheory.measurable_klFun`：measurable_klFun : Measurable klFun
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `InformationTheory.klFun_nonneg`：klFun_nonneg (hx : 0 <= x) : 0 <= klFun 
x
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用引理 `InformationTheory.integrable_klFun_rnDeriv_iff`：integrable_klFun_rnDeriv
_iff (hμν : μ ≪ ν) : Integrable (fun x => klFun (μ.rnDeriv ν x).toReal) ν ↔ Inte
grable (llr μ ν) μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Decidable.not_not`：∀ {p : Prop} [Decidable p], ¬¬p ↔ p
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
（共 34 条，此处仅展示前 30 条）
-/
lemma klDiv_eq_lintegral_klFun :
    klDiv μ ν = if μ ≪ ν then ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν else ∞ := by
  rw [klDiv_eq_integral_klFun]
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  have h_int_iff := lintegral_ofReal_ne_top_iff_integrable
    (f := fun x ↦ klFun (μ.rnDeriv ν x).toReal) (μ := ν) ?_ ?_
  rotate_left
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ fun _ ↦ klFun_nonneg ENNReal.toReal_nonneg
  by_cases h_int : Integrable (llr μ ν) μ
  · simp only [hμν, h_int, and_self, ↓reduceIte]
    rw [ofReal_integral_eq_lintegral_ofReal]
    · rwa [integrable_klFun_rnDeriv_iff hμν]
    · exact ae_of_all _ fun _ ↦ klFun_nonneg ENNReal.toReal_nonneg
  · rw [← not_iff_not, ne_eq, Decidable.not_not] at h_int_iff
    symm
    simp [hμν, h_int, h_int_iff, integrable_klFun_rnDeriv_iff hμν]
/-
**InformationTheory.klDiv_eq_lintegral_klFun_of_ac** 是 Mathlib 中的一个引理，位于命名空间 `In
formationTheory`。
形式化陈述：klDiv_eq_lintegral_klFun_of_ac (h_ac : μ ≪ ν) : klDiv μ ν = ∫⁻ x, ENNReal.
ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν
参数：h_ac : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InformationTheory.klDiv_eq_lintegral_klFun`：klDiv_eq_lintegral_klFun : k
lDiv μ ν = if μ ≪ ν then ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν 
else ∞
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma klDiv_eq_lintegral_klFun_of_ac (h_ac : μ ≪ ν) :
    klDiv μ ν = ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν := by
  simp [klDiv_eq_lintegral_klFun, h_ac]

end AlternativeFormulas

section Real

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- **Gibbs' inequality**: the Kullback-Leibler divergence is nonnegative.
Note that since `klDiv` takes value in `ℝ≥0∞` (defined when it is finite as `ENNReal.ofReal (...)`),
it is nonnegative by definition. This lemma proves that the argument of `ENNReal.ofReal`
is also nonnegative. -/
/-
**InformationTheory.integral_llr_add_sub_measure_univ_nonneg** 是 Mathlib 中的一个引理，
位于命名空间 `InformationTheory`。
形式化陈述：integral_llr_add_sub_measure_univ_nonneg (hμν : μ ≪ ν) (h_int : Integrable
 (llr μ ν) μ) : 0 <= ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ
参数：hμν : μ ≪ ν；h_int : Integrable (llr μ ν) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `InformationTheory.integral_klFun_rnDeriv`：integral_klFun_rnDeriv (hμν : 
μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν =
 ∫ x, llr μ ν x ∂μ + ν.real un…
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
· 使用引理 `InformationTheory.klFun_nonneg`：klFun_nonneg (hx : 0 <= x) : 0 <= klFun 
x
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal

--- 原说明 ---
**Gibbs' inequality**: the Kullback-Leibler divergence is nonnegative.
Note that since `klDiv` takes value in `ℝ≥0∞` (defined when it is finite as `ENN
Real.ofReal (...)`),
it is nonnegative by definition. This lemma proves that the argument of `ENNReal
.ofReal`
is also nonnegative.
-/
lemma integral_llr_add_sub_measure_univ_nonneg (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    0 ≤ ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ := by
  rw [← integral_klFun_rnDeriv hμν h_int]
  exact integral_nonneg fun x ↦ klFun_nonneg ENNReal.toReal_nonneg
/-
**InformationTheory.toReal_klDiv** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheory`。
形式化陈述：toReal_klDiv (h : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : (klDiv μ ν).to
Real = ∫ a, llr μ ν a ∂μ + ν.real univ - μ.real univ
参数：h : μ ≪ ν；h_int : Integrable (llr μ ν) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InformationTheory.klDiv_of_ac_of_integrable`：klDiv_of_ac_of_integrable (
h1 : μ ≪ ν) (h2 : Integrable (llr μ ν) μ) : klDiv μ ν = ENNReal.ofReal (∫ x, llr
 μ ν x ∂μ + ν.real univ - μ.real …
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用引理 `InformationTheory.integral_llr_add_sub_measure_univ_nonneg`：integral_llr
_add_sub_measure_univ_nonneg (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : 0 
<= ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ
-/
lemma toReal_klDiv (h : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ + ν.real univ - μ.real univ := by
  rw [klDiv_of_ac_of_integrable h h_int, ENNReal.toReal_ofReal]
  exact integral_llr_add_sub_measure_univ_nonneg h h_int

/-- If `μ ≪ ν` and `μ univ = ν univ`, then `toReal` of the Kullback-Leibler divergence is equal to
an integral, without any integrability condition. -/
/-
**InformationTheory.toReal_klDiv_of_measure_eq** 是 Mathlib 中的一个引理，位于命名空间 `Inform
ationTheory`。
形式化陈述：toReal_klDiv_of_measure_eq (h : μ ≪ ν) (h_eq : μ univ = ν univ) : (klDiv μ
 ν).toReal = ∫ a, llr μ ν a ∂μ
参数：h : μ ≪ ν；h_eq : μ univ = ν univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InformationTheory.toReal_klDiv`：toReal_klDiv (h : μ ≪ ν) (h_int : Integr
able (llr μ ν) μ) : (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ + ν.real univ - μ.rea
l univ
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `InformationTheory.klDiv_of_not_integrable`：klDiv_of_not_integrable (h : 
¬ Integrable (llr μ ν) μ) : klDiv μ ν = ∞
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `ENNReal.toReal_top`：⊤.toReal = 0

--- 原说明 ---
If `μ ≪ ν` and `μ univ = ν univ`, then `toReal` of the Kullback-Leibler divergen
ce is equal to
an integral, without any integrability condition.
-/
lemma toReal_klDiv_of_measure_eq (h : μ ≪ ν) (h_eq : μ univ = ν univ) :
    (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ := by
  by_cases h_int : Integrable (llr μ ν) μ
  · simp [toReal_klDiv h h_int, h_eq, measureReal_def]
  · rw [klDiv_of_not_integrable h_int, integral_undef h_int, ENNReal.toReal_top]
/-
**InformationTheory.toReal_klDiv_eq_integral_klFun** 是 Mathlib 中的一个引理，位于命名空间 `In
formationTheory`。
形式化陈述：toReal_klDiv_eq_integral_klFun (h : μ ≪ ν) : (klDiv μ ν).toReal = ∫ x, klF
un (μ.rnDeriv ν x).toReal ∂ν
参数：h : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InformationTheory.klDiv_eq_integral_klFun`：klDiv_eq_integral_klFun : klD
iv μ ν = if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, klFun (μ.rn
Deriv ν x).toReal ∂ν) else ∞
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
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
· 使用引理 `InformationTheory.klFun_nonneg`：klFun_nonneg (hx : 0 <= x) : 0 <= klFun 
x
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用引理 `InformationTheory.integrable_klFun_rnDeriv_iff`：integrable_klFun_rnDeriv
_iff (hμν : μ ≪ ν) : Integrable (fun x => klFun (μ.rnDeriv ν x).toReal) ν ↔ Inte
grable (llr μ ν) μ
· 使用引理 `InformationTheory.klDiv_of_not_integrable`：klDiv_of_not_integrable (h : 
¬ Integrable (llr μ ν) μ) : klDiv μ ν = ∞
· 使用定理 `ENNReal.toReal_top`：⊤.toReal = 0
-/
lemma toReal_klDiv_eq_integral_klFun (h : μ ≪ ν) :
    (klDiv μ ν).toReal = ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν := by
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [klDiv_eq_integral_klFun, if_pos ⟨h, h_int⟩, ENNReal.toReal_ofReal]
    exact integral_nonneg fun _ ↦ klFun_nonneg ENNReal.toReal_nonneg
  · rw [integral_undef]
    · rw [klDiv_of_not_integrable h_int, ENNReal.toReal_top]
    · rwa [integrable_klFun_rnDeriv_iff h]
/-
**InformationTheory.toReal_klDiv_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `Informatio
nTheory`。
形式化陈述：toReal_klDiv_smul_left (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) (c :
 Real>=0) : (klDiv (c • μ) ν).toReal = c * (klDiv μ ν).toReal + (1 - c) * ν.real
 univ + c * log c * μ.real univ
参数：hμν : μ ≪ ν；h_int : Integrable (llr μ ν) μ；c : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `InformationTheory.klDiv_zero_left`：klDiv_zero_left [IsFiniteMeasure ν] :
 klDiv 0 ν = ν univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.llr_smul_nnreal_left`：llr_smul_nnreal_left [IsFiniteMeasur
e μ] [Measure.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) (c : Real>=0) (hc : c
 != 0) : llr (c • μ) ν =…
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用引理 `InformationTheory.toReal_klDiv`：toReal_klDiv (h : μ ≪ ν) (h_int : Integr
able (llr μ ν) μ) : (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ + ν.real univ - μ.rea
l univ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.smul_left`：∀ {α : Type u_1} {
R : Type u_5} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : S
Mul R ENNReal]   [inst_1 : IsScalarTower R…
· 使用定理 `MeasureTheory.Integrable.smul_measure_nnreal`：∀ {α : Type u_1} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalS
pace ε]   [inst_1 : ESeminormedAdd…
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.Integrable.fun_add`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   
[inst_1 : ESeminormedA…
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
（共 71 条，此处仅展示前 30 条）
-/
lemma toReal_klDiv_smul_left (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) (c : ℝ≥0) :
    (klDiv (c • μ) ν).toReal =
      c * (klDiv μ ν).toReal + (1 - c) * ν.real univ + c * log c * μ.real univ := by
  by_cases hc : c = 0
  · simp [hc, measureReal_def]
  have h_llr := llr_smul_nnreal_left hμν c (by simpa)
  rw [toReal_klDiv hμν h_int, toReal_klDiv (hμν.smul_left c)]
  swap
  · refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr h_llr]
    fun_prop
  simp only [integral_smul_nnreal_measure, measureReal_nnreal_smul_apply]
  rw [integral_congr_ae h_llr, integral_add h_int (integrable_const _)]
  have h_smul (a : ℝ) : c • a = c * a := rfl
  simp [h_smul]
  ring
/-
**InformationTheory.toReal_klDiv_smul_right_eq_smul_left** 是 Mathlib 中的一个引理，位于命名
空间 `InformationTheory`。
形式化陈述：toReal_klDiv_smul_right_eq_smul_left (hμν : μ ≪ ν) (h_int : Integrable (ll
r μ ν) μ) (c : Real>=0) : (klDiv μ (c • ν)).toReal = c * (klDiv (c⁻¹ • μ) ν).toR
eal
参数：hμν : μ ≪ ν；h_int : Integrable (llr μ ν) μ；c : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用引理 `InformationTheory.klDiv_zero_left`：klDiv_zero_left [IsFiniteMeasure ν] :
 klDiv 0 ν = ν univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `InformationTheory.klDiv_self`：klDiv_self (μ : Measure α) [SigmaFinite μ]
 : klDiv μ μ = 0
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `InformationTheory.klDiv_zero_right`：klDiv_zero_right [NeZero μ] : klDiv 
μ 0 = ∞
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.llr_smul_nnreal_left`：llr_smul_nnreal_left [IsFiniteMeasur
e μ] [Measure.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) (c : Real>=0) (hc : c
 != 0) : llr (c • μ) ν =…
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用引理 `MeasureTheory.llr_smul_nnreal_right`：llr_smul_nnreal_right [IsFiniteMeas
ure μ] [Measure.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) (c : Real>=0) (hc :
 c != 0) : llr μ (c • ν) …
· 使用引理 `InformationTheory.toReal_klDiv`：toReal_klDiv (h : μ ≪ ν) (h_int : Integr
able (llr μ ν) μ) : (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ + ν.real univ - μ.rea
l univ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.smul_right`：∀ {α : Type u_1} 
{mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuo
us ν → ∀ {c : ENNReal}, c ≠ 0 → μ.Absolutel…
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.Integrable.sub'`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
g : α → β},   Measu…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.smul_left`：∀ {α : Type u_1} {
R : Type u_5} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : S
Mul R ENNReal]   [inst_1 : IsScalarTower R…
· 使用定理 `MeasureTheory.Integrable.smul_measure_nnreal`：∀ {α : Type u_1} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalS
pace ε]   [inst_1 : ESeminormedAdd…
· 使用定理 `MeasureTheory.Integrable.fun_add`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   
[inst_1 : ESeminormedA…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
（共 43 条，此处仅展示前 30 条）
-/
lemma toReal_klDiv_smul_right_eq_smul_left (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
    (c : ℝ≥0) :
    (klDiv μ (c • ν)).toReal = c * (klDiv (c⁻¹ • μ) ν).toReal := by
  by_cases hc : c = 0
  · simp only [hc, zero_smul, NNReal.coe_zero, inv_zero, klDiv_zero_left, zero_mul]
    rcases eq_zero_or_neZero μ with rfl | hμ <;> simp
  have h_llr_left := llr_smul_nnreal_left hμν c⁻¹ (by simpa)
  have h_llr_right := llr_smul_nnreal_right hμν c (by simpa)
  rw [toReal_klDiv, toReal_klDiv]
  rotate_left
  · exact hμν.smul_left _
  · refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr h_llr_left]
    fun_prop
  · exact hμν.smul_right (by simpa)
  · rw [integrable_congr h_llr_right]
    fun_prop
  have h_smul (c : ℝ≥0) (a : ℝ) : c • a = c * a := rfl
  simp only [measureReal_nnreal_smul_apply, integral_smul_nnreal_measure, h_smul, NNReal.coe_inv]
  have h_llr_smul_inv := llr_smul_inv_left_eq_smul_right hμν c (by simpa) (by simp)
  simp only [← ENNReal.coe_inv hc, Measure.coe_nnreal_smul] at h_llr_smul_inv
  rw [integral_congr_ae h_llr_smul_inv, mul_sub, mul_add, mul_inv_cancel_left₀ (by simpa),
    mul_inv_cancel_left₀ (by simpa)]
/-
**InformationTheory.toReal_klDiv_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `Informati
onTheory`。
形式化陈述：toReal_klDiv_smul_right (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) {c 
: Real>=0} (hc : c != 0) : (klDiv μ (c • ν)).toReal = (klDiv μ ν).toReal + (c - 
1) * ν.real univ - log c * μ.real univ
参数：hμν : μ ≪ ν；h_int : Integrable (llr μ ν) μ；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InformationTheory.toReal_klDiv_smul_right_eq_smul_left`：toReal_klDiv_smu
l_right_eq_smul_left (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) (c : Real>=0
) : (klDiv μ (c • ν)).toReal = c * (klDiv (c…
· 使用引理 `InformationTheory.toReal_klDiv_smul_left`：toReal_klDiv_smul_left (hμν : 
μ ≪ ν) (h_int : Integrable (llr μ ν) μ) (c : Real>=0) : (klDiv (c • μ) ν).toReal
 = c * (klDiv μ ν).toReal + (1…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.log_inv`：log_inv (x : Real) : log x⁻¹ = -log x
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
（共 47 条，此处仅展示前 30 条）
-/
lemma toReal_klDiv_smul_right (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
    {c : ℝ≥0} (hc : c ≠ 0) :
    (klDiv μ (c • ν)).toReal =
      (klDiv μ ν).toReal + (c - 1) * ν.real univ - log c * μ.real univ := by
  rw [toReal_klDiv_smul_right_eq_smul_left hμν h_int c, toReal_klDiv_smul_left hμν h_int c⁻¹]
  simp only [NNReal.coe_inv, log_inv, mul_neg, neg_mul, ← sub_eq_add_neg]
  field_simp
/-
**InformationTheory.toReal_klDiv_smul_same** 是 Mathlib 中的一个引理，位于命名空间 `Informatio
nTheory`。
形式化陈述：toReal_klDiv_smul_same (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) (c :
 Real>=0) : (klDiv (c • μ) (c • ν)).toReal = c * (klDiv μ ν).toReal
参数：hμν : μ ≪ ν；h_int : Integrable (llr μ ν) μ；c : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `InformationTheory.klDiv_self`：klDiv_self (μ : Measure α) [SigmaFinite μ]
 : klDiv μ μ = 0
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `InformationTheory.toReal_klDiv_smul_right_eq_smul_left`：toReal_klDiv_smu
l_right_eq_smul_left (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) (c : Real>=0
) : (klDiv μ (c • ν)).toReal = c * (klDiv (c…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.smul_left`：∀ {α : Type u_1} {
R : Type u_5} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : S
Mul R ENNReal]   [inst_1 : IsScalarTower R…
· 使用定理 `MeasureTheory.Integrable.smul_measure_nnreal`：∀ {α : Type u_1} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalS
pace ε]   [inst_1 : ESeminormedAdd…
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用引理 `MeasureTheory.llr_smul_nnreal_left`：llr_smul_nnreal_left [IsFiniteMeasur
e μ] [Measure.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) (c : Real>=0) (hc : c
 != 0) : llr (c • μ) ν =…
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Integrable.fun_add`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   
[inst_1 : ESeminormedA…
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
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma toReal_klDiv_smul_same (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) (c : ℝ≥0) :
    (klDiv (c • μ) (c • ν)).toReal = c * (klDiv μ ν).toReal := by
  by_cases hc : c = 0
  · simp [hc]
  rw [toReal_klDiv_smul_right_eq_smul_left, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · exact hμν.smul_left c
  · refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr (llr_smul_nnreal_left hμν c (by simpa))]
    fun_prop

end Real

/-
**InformationTheory.klDiv_smul_right_eq_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `Inf
ormationTheory`。
形式化陈述：klDiv_smul_right_eq_smul_left [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c :
 Real>=0} (hc : c != 0) : klDiv μ (c • ν) = c * klDiv (c⁻¹ • μ) ν
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.smul_right`：∀ {α : Type u_1} 
{mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuo
us ν → ∀ {c : ENNReal}, c ≠ 0 → μ.Absolutel…
· 使用定理 `MeasureTheory.Integrable.smul_measure_nnreal`：∀ {α : Type u_1} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalS
pace ε]   [inst_1 : ESeminormedAdd…
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用引理 `MeasureTheory.llr_smul_nnreal_left`：llr_smul_nnreal_left [IsFiniteMeasur
e μ] [Measure.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) (c : Real>=0) (hc : c
 != 0) : llr (c • μ) ν =…
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Integrable.fun_add`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   
[inst_1 : ESeminormedA…
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
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用引理 `MeasureTheory.llr_smul_nnreal_right`：llr_smul_nnreal_right [IsFiniteMeas
ure μ] [Measure.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) (c : Real>=0) (hc :
 c != 0) : llr μ (c • ν) …
· 使用定理 `MeasureTheory.Integrable.sub'`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
g : α → β},   Measu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用引理 `InformationTheory.klDiv_ne_top`：klDiv_ne_top (hμν : μ ≪ ν) (h_int : Inte
grable (llr μ ν) μ) : klDiv μ ν != ∞
· 使用引理 `InformationTheory.toReal_klDiv_smul_right_eq_smul_left`：toReal_klDiv_smu
l_right_eq_smul_left (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) (c : Real>=0
) : (klDiv μ (c • ν)).toReal = c * (klDiv (c…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
（共 38 条，此处仅展示前 30 条）
-/
lemma klDiv_smul_right_eq_smul_left [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c : ℝ≥0} (hc : c ≠ 0) :
    klDiv μ (c • ν) = c * klDiv (c⁻¹ • μ) ν := by
  have hc' : (c : ℝ≥0∞) ≠ 0 := by simpa
  have hμ_smul : μ = c • (c⁻¹ • μ) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hν_smul : ν = c⁻¹ • (c • ν) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  by_cases hμν : μ ≪ ν
  swap
  · rw [klDiv_of_not_ac, klDiv_of_not_ac, ENNReal.mul_top hc']
    · refine fun h_contra ↦ hμν ?_
      rw [hμ_smul]
      exact h_contra.smul_left _
    · refine fun h_contra ↦ hμν ?_
      rw [hν_smul]
      exact h_contra.smul_right (by simpa)
  have hμν_right := hμν.smul_right hc'
  simp only [Measure.coe_nnreal_smul] at hμν_right
  by_cases h_int : Integrable (llr μ ν) μ
  swap
  · rw [klDiv_of_not_integrable, klDiv_of_not_integrable, ENNReal.mul_top hc']
    · refine fun h_contra ↦ h_int ?_
      rw [hμ_smul]
      refine Integrable.smul_measure_nnreal ?_
      rw [integrable_congr (llr_smul_nnreal_left (hμν.smul_left _) c hc)]
      fun_prop
    · refine fun h_contra ↦ h_int ?_
      rw [hν_smul]
      have : IsFiniteMeasure ((c : ℝ≥0∞) • ν) := by
        simp only [Measure.coe_nnreal_smul]
        infer_instance
      have h := llr_smul_nnreal_right (hμν.smul_right hc') c⁻¹ (by simpa)
      simp only [Measure.coe_nnreal_smul, NNReal.coe_inv, log_inv, sub_neg_eq_add] at h
      rw [integrable_congr h]
      fun_prop
  have h_int_left : Integrable (llr (c⁻¹ • μ) ν) (c⁻¹ • μ) := by
    refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr (llr_smul_nnreal_left hμν c⁻¹ (by simpa))]
    fun_prop
  have h_int_right : Integrable (llr μ (c • ν)) μ := by
    rw [integrable_congr (llr_smul_nnreal_right hμν c (by simpa))]
    fun_prop
  rw [← ENNReal.ofReal_toReal (klDiv_ne_top hμν_right h_int_right),
    toReal_klDiv_smul_right_eq_smul_left hμν h_int c]
  simp only [NNReal.zero_le_coe, ENNReal.ofReal_mul, ENNReal.ofReal_coe_nnreal]
  rw [ENNReal.ofReal_toReal]
  exact klDiv_ne_top (hμν.smul_left _) h_int_left
/-
**InformationTheory.klDiv_smul_same** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheory
`。
形式化陈述：klDiv_smul_same [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : Real>=0) : kl
Div (c • μ) (c • ν) = c * klDiv μ ν
参数：c : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `InformationTheory.klDiv_self`：klDiv_self (μ : Measure α) [SigmaFinite μ]
 : klDiv μ μ = 0
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用引理 `InformationTheory.klDiv_ne_top`：klDiv_ne_top (hμν : μ ≪ ν) (h_int : Inte
grable (llr μ ν) μ) : klDiv μ ν != ∞
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.smul`：∀ {α : Type u_1} {R : T
ype u_5} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : SMul R
 ENNReal]   [inst_1 : IsScalarTower R…
· 使用定理 `MeasureTheory.Integrable.smul_measure_nnreal`：∀ {α : Type u_1} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalS
pace ε]   [inst_1 : ESeminormedAdd…
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用引理 `MeasureTheory.llr_smul_nnreal_same`：llr_smul_nnreal_same [IsFiniteMeasur
e μ] [Measure.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) (c : Real>=0) (hc : c
 != 0) : llr (c • μ) (c …
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用引理 `InformationTheory.toReal_klDiv_smul_same`：toReal_klDiv_smul_same (hμν : 
μ ≪ ν) (h_int : Integrable (llr μ ν) μ) (c : Real>=0) : (klDiv (c • μ) (c • ν)).
toReal = c * (klDiv μ ν).toRea…
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用引理 `InformationTheory.klDiv_of_not_integrable`：klDiv_of_not_integrable (h : 
¬ Integrable (llr μ ν) μ) : klDiv μ ν = ∞
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
· 使用引理 `InformationTheory.klDiv_of_not_ac`：klDiv_of_not_ac (h : ¬ μ ≪ ν) : klDiv
 μ ν = ∞
-/
lemma klDiv_smul_same [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : ℝ≥0) :
    klDiv (c • μ) (c • ν) = c * klDiv μ ν := by
  by_cases hc : c = 0
  · simp [hc]
  have hc' : (c : ℝ≥0∞) ≠ 0 := by simpa
  have hμ_smul (μ : Measure α) : μ = c⁻¹ • (c • μ) := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  by_cases hμν : μ ≪ ν
  swap
  · rw [klDiv_of_not_ac hμν, klDiv_of_not_ac, ENNReal.mul_top hc']
    refine fun h_contra ↦ hμν ?_
    rw [hμ_smul μ, hμ_smul ν]
    exact h_contra.smul _
  by_cases h_int : Integrable (llr μ ν) μ
  swap
  · rw [klDiv_of_not_integrable h_int, klDiv_of_not_integrable, ENNReal.mul_top hc']
    refine fun h_contra ↦ h_int ?_
    rw [hμ_smul μ, hμ_smul ν]
    refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr (llr_smul_nnreal_same (hμν.smul c) c⁻¹ (by simpa))]
    fun_prop
  rw [← ENNReal.ofReal_toReal (klDiv_ne_top (hμν.smul c) _),
    ← ENNReal.ofReal_toReal (klDiv_ne_top hμν h_int)]
  swap
  · refine Integrable.smul_measure_nnreal ?_
    rw [integrable_congr (llr_smul_nnreal_same hμν c hc)]
    fun_prop
  simp [toReal_klDiv_smul_same hμν h_int]

section Inequalities

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-
**InformationTheory.integral_llr_add_mul_log_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `I
nformationTheory`。
形式化陈述：integral_llr_add_mul_log_nonneg (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν
) μ) : 0 <= ∫ x, llr μ ν x ∂μ + μ.real univ * log (ν.real univ) + 1 - μ.real uni
v
参数：hμν : μ ≪ ν；h_int : Integrable (llr μ ν) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_zero_iff`：absolutelyContinuou
s_zero_iff : μ ≪ 0 ↔ μ = 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trans`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous μ₂ → μ₂.AbsolutelyContinuous μ₃ → …
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_smul`：absolutelyContinuous_sm
ul {c : Real>=0∞} (hc : c != 0) : μ ≪ c • μ
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `InformationTheory.integral_llr_add_sub_measure_univ_nonneg`：integral_llr
_add_sub_measure_univ_nonneg (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : 0 
<= ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ
· 使用定理 `MeasureTheory.IsFiniteMeasure.average`：∀ {α : Type u_1} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α},   MeasureTheory.IsFiniteMeasure ((μ Set.
univ)⁻¹ • μ)
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用引理 `MeasureTheory.llr_smul_right`：llr_smul_right [IsFiniteMeasure μ] [Measur
e.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) (c : Real>=0∞) (hc : c != 0) (hc_
ne_top : c != ∞) :…
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
（共 38 条，此处仅展示前 30 条）
-/
lemma integral_llr_add_mul_log_nonneg (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    0 ≤ ∫ x, llr μ ν x ∂μ + μ.real univ * log (ν.real univ) + 1 - μ.real univ := by
  by_cases hμ : μ = 0
  · simp [hμ]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    exact Measure.absolutelyContinuous_zero_iff.mp hμν
  have : NeZero ν := ⟨hν⟩
  let ν' := (ν univ)⁻¹ • ν
  have hμν' : μ ≪ ν' := hμν.trans (Measure.absolutelyContinuous_smul (by simp))
  have h := integral_llr_add_sub_measure_univ_nonneg hμν' ?_
  swap
  · rw [integrable_congr (llr_smul_right hμν (ν univ)⁻¹ (by simp) (by simp [hν]))]
    exact h_int.sub (integrable_const _)
  rw [integral_congr_ae (llr_smul_right hμν (ν univ)⁻¹ (by simp) (by simp [hν])),
    integral_sub h_int (integrable_const _), integral_const, smul_eq_mul] at h
  simpa using! h
/-
**InformationTheory.mul_klFun_le_toReal_klDiv** 是 Mathlib 中的一个引理，位于命名空间 `Informa
tionTheory`。
形式化陈述：mul_klFun_le_toReal_klDiv (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
 ν.real univ * klFun (μ.real univ / ν.real univ) <= (klDiv μ ν).toReal
参数：hμν : μ ≪ ν；h_int : Integrable (llr μ ν) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.mul_le_integral_rnDeriv_of_ac`：mul_le_integral_rnDeriv_of_
ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hf_cvx : ConvexOn Real (Ici 0) f) (h
f_cont : ContinuousWithinAt f (Ic…
· 使用引理 `InformationTheory.convexOn_klFun`：convexOn_klFun : ConvexOn Real (Ici 0)
 klFun
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用引理 `InformationTheory.continuous_klFun`：continuous_klFun : Continuous klFun
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InformationTheory.integrable_klFun_rnDeriv_iff`：integrable_klFun_rnDeriv
_iff (hμν : μ ≪ ν) : Integrable (fun x => klFun (μ.rnDeriv ν x).toReal) ν ↔ Inte
grable (llr μ ν) μ
· 使用引理 `InformationTheory.toReal_klDiv_eq_integral_klFun`：toReal_klDiv_eq_integr
al_klFun (h : μ ≪ ν) : (klDiv μ ν).toReal = ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν
-/
lemma mul_klFun_le_toReal_klDiv (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    ν.real univ * klFun (μ.real univ / ν.real univ) ≤ (klDiv μ ν).toReal := by
  calc ν.real univ * klFun (μ.real univ / ν.real univ)
  _ ≤ ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν := by
    refine mul_le_integral_rnDeriv_of_ac convexOn_klFun continuous_klFun.continuousWithinAt ?_ hμν
    rwa [integrable_klFun_rnDeriv_iff hμν]
  _ = (klDiv μ ν).toReal := by rw [toReal_klDiv_eq_integral_klFun hμν]
/-
**InformationTheory.mul_log_le_toReal_klDiv** 是 Mathlib 中的一个引理，位于命名空间 `Informati
onTheory`。
形式化陈述：mul_log_le_toReal_klDiv (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : μ
.real univ * log (μ.real univ / ν.real univ) + ν.real univ - μ.real univ <= (klD
iv μ ν).toReal
参数：hμν : μ ≪ ν；h_int : Integrable (llr μ ν) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `InformationTheory.klDiv_zero_left`：klDiv_zero_left [IsFiniteMeasure ν] :
 klDiv 0 ν = ν univ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_zero_iff`：absolutelyContinuou
s_zero_iff : μ ≪ 0 ↔ μ = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `InformationTheory.klFun.eq_1`：∀ (x : ℝ), InformationTheory.klFun x = x *
 Real.log x + 1 - x
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `InformationTheory.mul_klFun_le_toReal_klDiv`：mul_klFun_le_toReal_klDiv (
hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : ν.real univ * klFun (μ.real univ
 / ν.real univ) <= (klDiv μ ν).to…
-/
lemma mul_log_le_toReal_klDiv (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    μ.real univ * log (μ.real univ / ν.real univ) + ν.real univ - μ.real univ
      ≤ (klDiv μ ν).toReal := by
  by_cases hμ : μ = 0
  · simp [hμ, measureReal_def]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    exact Measure.absolutelyContinuous_zero_iff.mp hμν
  refine (le_of_eq ?_).trans (mul_klFun_le_toReal_klDiv hμν h_int)
  have : ν.real univ * (μ.real univ / ν.real univ) = μ.real univ := by
    rw [mul_div_cancel₀]; simp [ENNReal.toReal_eq_zero_iff, hν, measureReal_def]
  rw [klFun, mul_sub, mul_add, mul_one, ← mul_assoc, this]
/-
**InformationTheory.mul_log_le_klDiv** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheor
y`。
形式化陈述：mul_log_le_klDiv (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
 : ENNReal.ofReal (μ.real univ * log (μ.real univ / ν.real univ) + ν.real univ -
 μ.real univ) <= klDiv μ ν
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用引理 `InformationTheory.klDiv_ne_top_iff`：klDiv_ne_top_iff : klDiv μ ν != ∞ ↔ 
μ ≪ ν ∧ Integrable (llr μ ν) μ
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用引理 `InformationTheory.mul_log_le_toReal_klDiv`：mul_log_le_toReal_klDiv (hμν 
: μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : μ.real univ * log (μ.real univ / ν.r
eal univ) + ν.real univ - μ.rea…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `InformationTheory.klDiv_of_not_integrable`：klDiv_of_not_integrable (h : 
¬ Integrable (llr μ ν) μ) : klDiv μ ν = ∞
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `InformationTheory.klDiv_of_not_ac`：klDiv_of_not_ac (h : ¬ μ ≪ ν) : klDiv
 μ ν = ∞
-/
lemma mul_log_le_klDiv (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ENNReal.ofReal (μ.real univ * log (μ.real univ / ν.real univ)
        + ν.real univ - μ.real univ)
      ≤ klDiv μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [h_int]
  rw [← ENNReal.ofReal_toReal (a := klDiv μ ν)]
  · exact ENNReal.ofReal_le_ofReal (mul_log_le_toReal_klDiv hμν h_int)
  · rw [klDiv_ne_top_iff]
    exact ⟨hμν, h_int⟩

end Inequalities

/-- **Converse Gibbs' inequality**: the Kullback-Leibler divergence between two finite measures is
zero if and only if the two measures are equal. -/
/-
**InformationTheory.klDiv_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheo
ry`。
形式化陈述：klDiv_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] : klDiv μ ν = 0 
↔ μ = ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.rnDeriv_eq_one_iff_eq`：rnDeriv_eq_one_iff_eq [Have
LebesgueDecomposition μ ν] [SigmaFinite ν] (hμν : μ ≪ ν) : μ.rnDeriv ν =ᵐ[ν] 1 ↔
 μ = ν
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `InformationTheory.klDiv_ne_top_iff`：klDiv_ne_top_iff : klDiv μ ν != ∞ ↔ 
μ ≪ ν ∧ Integrable (llr μ ν) μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `Measurable.ennreal_ofReal`：Measurable.ennreal_ofReal {f : α -> Real} (hf
 : Measurable f) : Measurable fun x => ENNReal.ofReal (f x)
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用引理 `InformationTheory.measurable_klFun`：measurable_klFun : Measurable klFun
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `InformationTheory.klDiv_eq_lintegral_klFun`：klDiv_eq_lintegral_klFun : k
lDiv μ ν = if μ ≪ ν then ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν 
else ∞
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `InformationTheory.klFun_nonneg`：klFun_nonneg (hx : 0 <= x) : 0 <= klFun 
x
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `ENNReal.toReal_eq_one_iff`：toReal_eq_one_iff (x : Real>=0∞) : x.toReal =
 1 ↔ x = 1
· 使用引理 `InformationTheory.klFun_eq_zero_iff`：klFun_eq_zero_iff (hx : 0 <= x) : k
lFun x = 0 ↔ x = 1
· 使用引理 `InformationTheory.klDiv_self`：klDiv_self (μ : Measure α) [SigmaFinite μ]
 : klDiv μ μ = 0

--- 原说明 ---
**Converse Gibbs' inequality**: the Kullback-Leibler divergence between two fini
te measures is
zero if and only if the two measures are equal.
-/
lemma klDiv_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ klDiv_self _⟩
  have h_ne : klDiv μ ν ≠ ⊤ := by simp [h]
  rw [klDiv_ne_top_iff] at h_ne
  rw [klDiv_eq_lintegral_klFun, if_pos h_ne.1, lintegral_eq_zero_iff (by fun_prop)] at h
  refine (Measure.rnDeriv_eq_one_iff_eq h_ne.1).mp ?_
  filter_upwards [h] with x hx
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
  have hx' : klFun (μ.rnDeriv ν x).toReal = 0 := le_antisymm hx (klFun_nonneg ENNReal.toReal_nonneg)
  rwa [klFun_eq_zero_iff ENNReal.toReal_nonneg, ENNReal.toReal_eq_one_iff] at hx'

end InformationTheory

