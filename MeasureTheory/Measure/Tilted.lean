/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Exponentially tilted measures

The exponential tilting of a measure `μ` on `α` by a function `f : α → ℝ` is the measure with
density `x ↦ exp (f x) / ∫ y, exp (f y) ∂μ` with respect to `μ`. This is sometimes also called
the Esscher transform.

The definition is mostly used for `f` linear, in which case the exponentially tilted measure belongs
to the natural exponential family of the base measure. Exponentially tilted measures for general `f`
can be used for example to establish variational expressions for the Kullback-Leibler divergence.

## Main definitions

* `Measure.tilted μ f`: exponential tilting of `μ` by `f`, equal to
  `μ.withDensity (fun x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ))`.

-/

@[expose] public section

open Real

open scoped ENNReal NNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}

/-- Exponentially tilted measure. When `x ↦ exp (f x)` is integrable, `μ.tilted f` is the
probability measure with density with respect to `μ` proportional to `exp (f x)`. Otherwise it is 0.
-/
noncomputable
/-
**MeasureTheory.Measure.tilted** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`
。
形式化陈述：{α : Type u_1} → {mα : MeasurableSpace α} → MeasureTheory.Measure α → (α →
 ℝ) → MeasureTheory.Measure α
参数：α → ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Measure.tilted (μ : Measure α) (f : α → ℝ) : Measure α :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ))

@[simp]
/-
**MeasureTheory.tilted_of_not_integrable** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：tilted_of_not_integrable (hf : ¬ Integrable (fun x => exp (f x)) μ) : μ.ti
lted f = 0
参数：hf : ¬ Integrable (fun x => exp (f x)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.tilted.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpac
e α} (μ : MeasureTheory.Measure α) (f : α → ℝ),   μ.tilted f = μ.withDensity fun
 x => ENNReal.ofReal (R…
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `MeasureTheory.withDensity_const`：withDensity_const (c : Real>=0∞) : μ.wi
thDensity (fun _ => c) = c • μ
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tilted_of_not_integrable (hf : ¬ Integrable (fun x ↦ exp (f x)) μ) : μ.tilted f = 0 := by
  rw [Measure.tilted, integral_undef hf]
  simp

@[simp]
/-
**MeasureTheory.tilted_of_not_aemeasurable** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：tilted_of_not_aemeasurable (hf : ¬ AEMeasurable f μ) : μ.tilted f = 0
参数：hf : ¬ AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.tilted_of_not_integrable`：tilted_of_not_integrable (hf : ¬
 Integrable (fun x => exp (f x)) μ) : μ.tilted f = 0
· 使用引理 `Real.aemeasurable_of_aemeasurable_exp`：aemeasurable_of_aemeasurable_exp 
(hf : AEMeasurable (fun x => exp (f x)) μ) : AEMeasurable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma tilted_of_not_aemeasurable (hf : ¬ AEMeasurable f μ) : μ.tilted f = 0 := by
  refine tilted_of_not_integrable ?_
  suffices ¬ AEMeasurable (fun x ↦ exp (f x)) μ by exact fun h ↦ this h.1.aemeasurable
  exact fun h ↦ hf (aemeasurable_of_aemeasurable_exp h)

@[simp]
/-
**MeasureTheory.tilted_zero_measure** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：tilted_zero_measure (f : α -> Real) : (0 : Measure α).tilted f = 0
参数：f : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `MeasureTheory.withDensity_const`：withDensity_const (c : Real>=0∞) : μ.wi
thDensity (fun _ => c) = c • μ
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tilted_zero_measure (f : α → ℝ) : (0 : Measure α).tilted f = 0 := by simp [Measure.tilted]

@[simp]
/-
**MeasureTheory.tilted_const'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：tilted_const' (μ : Measure α) (c : Real) : μ.tilted (fun _ => c) = (μ Set.
univ)⁻¹ • μ
参数：μ : Measure α；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MeasureTheory.tilted_zero_measure`：tilted_zero_measure (f : α -> Real) :
 (0 : Measure α).tilted f = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.withDensity_const`：withDensity_const (c : Real>=0∞) : μ.wi
thDensity (fun _ => c) = c • μ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
（共 34 条，此处仅展示前 30 条）
-/
lemma tilted_const' (μ : Measure α) (c : ℝ) :
    μ.tilted (fun _ ↦ c) = (μ Set.univ)⁻¹ • μ := by
  cases eq_zero_or_neZero μ with
  | inl h => rw [h]; simp
  | inr h0 =>
    simp only [Measure.tilted, withDensity_const, integral_const, smul_eq_mul]
    by_cases h_univ : μ Set.univ = ∞
    · simp only [measureReal_def, h_univ, ENNReal.toReal_top, zero_mul, div_zero,
      ENNReal.ofReal_zero, zero_smul, ENNReal.inv_top]
    congr
    rw [div_eq_mul_inv, mul_inv, mul_comm, mul_assoc, inv_mul_cancel₀ (exp_pos _).ne', mul_one,
      measureReal_def, ← ENNReal.toReal_inv, ENNReal.ofReal_toReal]
    simp [h0.out]
/-
**MeasureTheory.tilted_const** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：tilted_const (μ : Measure α) [IsProbabilityMeasure μ] (c : Real) : μ.tilte
d (fun _ => c) = μ
参数：μ : Measure α；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.tilted_const'`：tilted_const' (μ : Measure α) (c : Real) : 
μ.tilted (fun _ => c) = (μ Set.univ)⁻¹ • μ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tilted_const (μ : Measure α) [IsProbabilityMeasure μ] (c : ℝ) :
    μ.tilted (fun _ ↦ c) = μ := by simp

@[simp]
/-
**MeasureTheory.tilted_zero'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：tilted_zero' (μ : Measure α) : μ.tilted 0 = (μ Set.univ)⁻¹ • μ
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.tilted_const'`：tilted_const' (μ : Measure α) (c : Real) : 
μ.tilted (fun _ => c) = (μ Set.univ)⁻¹ • μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tilted_zero' (μ : Measure α) : μ.tilted 0 = (μ Set.univ)⁻¹ • μ := by
  change μ.tilted (fun _ ↦ 0) = (μ Set.univ)⁻¹ • μ
  simp
/-
**MeasureTheory.tilted_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：tilted_zero (μ : Measure α) [IsProbabilityMeasure μ] : μ.tilted 0 = μ
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.tilted_zero'`：tilted_zero' (μ : Measure α) : μ.tilted 0 = 
(μ Set.univ)⁻¹ • μ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tilted_zero (μ : Measure α) [IsProbabilityMeasure μ] : μ.tilted 0 = μ := by simp
/-
**MeasureTheory.tilted_congr** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：tilted_congr {g : α -> Real} (hfg : f =ᵐ[μ] g) : μ.tilted f = μ.tilted g
参数：hfg : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.withDensity_congr_ae`：withDensity_congr_ae {f g : α -> Rea
l>=0∞} (h : f =ᵐ[μ] g) : μ.withDensity f = μ.withDensity g
-/
lemma tilted_congr {g : α → ℝ} (hfg : f =ᵐ[μ] g) :
    μ.tilted f = μ.tilted g := by
  have h_int_eq : ∫ x, exp (f x) ∂μ = ∫ x, exp (g x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hfg] with x hx
    rw [hx]
  refine withDensity_congr_ae ?_
  filter_upwards [hfg] with x hx
  rw [h_int_eq, hx]
/-
**MeasureTheory.tilted_eq_withDensity_nnreal** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory`。
形式化陈述：tilted_eq_withDensity_nnreal (μ : Measure α) (f : α -> Real) : μ.tilted f 
= μ.withDensity (fun x => ((↑) : Real>=0 -> Real>=0∞) (.mk (exp (f x) / ∫ x, exp
 (f x) ∂μ) (by positivity)))
参数：μ : Measure α；f : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.tilted.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpac
e α} (μ : MeasureTheory.Measure α) (f : α → ℝ),   μ.tilted f = μ.withDensity fun
 x => ENNReal.ofReal (R…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.ofReal_eq_coe_nnreal`：ofReal_eq_coe_nnreal {x : Real} (h : 0 <= 
x) : ENNReal.ofReal x = ofNNReal (NNReal.mk x h)
-/
lemma tilted_eq_withDensity_nnreal (μ : Measure α) (f : α → ℝ) :
    μ.tilted f = μ.withDensity (fun x ↦ ((↑) : ℝ≥0 → ℝ≥0∞)
      (.mk (exp (f x) / ∫ x, exp (f x) ∂μ) (by positivity))) := by
  rw [Measure.tilted]
  congr with x
  rw [ENNReal.ofReal_eq_coe_nnreal]
/-
**MeasureTheory.tilted_apply'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：tilted_apply' (μ : Measure α) (f : α -> Real) {s : Set α} (hs : Measurable
Set s) : μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal (exp (f a) / ∫ x, exp (f x) ∂μ
) ∂μ
参数：μ : Measure α；f : α -> Real；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.tilted.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpac
e α} (μ : MeasureTheory.Measure α) (f : α → ℝ),   μ.tilted f = μ.withDensity fun
 x => ENNReal.ofReal (R…
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
-/
lemma tilted_apply' (μ : Measure α) (f : α → ℝ) {s : Set α} (hs : MeasurableSet s) :
    μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal (exp (f a) / ∫ x, exp (f x) ∂μ) ∂μ := by
  rw [Measure.tilted, withDensity_apply _ hs]
/-
**MeasureTheory.tilted_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：tilted_apply (μ : Measure α) [SFinite μ] (f : α -> Real) (s : Set α) : μ.t
ilted f s = ∫⁻ a in s, ENNReal.ofReal (exp (f a) / ∫ x, exp (f x) ∂μ) ∂μ
参数：μ : Measure α；f : α -> Real；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.tilted.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpac
e α} (μ : MeasureTheory.Measure α) (f : α → ℝ),   μ.tilted f = μ.withDensity fun
 x => ENNReal.ofReal (R…
· 使用定理 `MeasureTheory.withDensity_apply'`：withDensity_apply' [SFinite μ] (f : α 
-> Real>=0∞) (s : Set α) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
-/
lemma tilted_apply (μ : Measure α) [SFinite μ] (f : α → ℝ) (s : Set α) :
    μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal (exp (f a) / ∫ x, exp (f x) ∂μ) ∂μ := by
  rw [Measure.tilted, withDensity_apply' _ s]
/-
**MeasureTheory.tilted_apply_eq_ofReal_integral'** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：tilted_apply_eq_ofReal_integral' {s : Set α} (f : α -> Real) (hs : Measura
bleSet s) : μ.tilted f s = ENNReal.ofReal (∫ a in s, exp (f a) / ∫ x, exp (f x) 
∂μ ∂μ)
参数：f : α -> Real；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.tilted_apply'`：tilted_apply' (μ : Measure α) (f : α -> Rea
l) {s : Set α} (hs : MeasurableSet s) : μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal
 (exp (f a) / ∫ x…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用定理 `MeasureTheory.Integrable.div_const`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedDivisionRing 𝕜] 
  {f : α → 𝕜}, MeasureTh…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
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
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.tilted_of_not_integrable`：tilted_of_not_integrable (hf : ¬
 Integrable (fun x => exp (f x)) μ) : μ.tilted f = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
（共 33 条，此处仅展示前 30 条）
-/
lemma tilted_apply_eq_ofReal_integral' {s : Set α} (f : α → ℝ) (hs : MeasurableSet s) :
    μ.tilted f s = ENNReal.ofReal (∫ a in s, exp (f a) / ∫ x, exp (f x) ∂μ ∂μ) := by
  by_cases hf : Integrable (fun x ↦ exp (f x)) μ
  · rw [tilted_apply' _ _ hs, ← ofReal_integral_eq_lintegral_ofReal]
    · exact hf.integrableOn.div_const _
    · exact ae_of_all _ (fun _ ↦ by positivity)
  · simp only [hf, not_false_eq_true, tilted_of_not_integrable, Measure.coe_zero,
      Pi.zero_apply, integral_undef hf, div_zero, integral_zero, ENNReal.ofReal_zero]
/-
**MeasureTheory.tilted_apply_eq_ofReal_integral** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory`。
形式化陈述：tilted_apply_eq_ofReal_integral [SFinite μ] (f : α -> Real) (s : Set α) : 
μ.tilted f s = ENNReal.ofReal (∫ a in s, exp (f a) / ∫ x, exp (f x) ∂μ ∂μ)
参数：f : α -> Real；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.tilted_apply`：tilted_apply (μ : Measure α) [SFinite μ] (f 
: α -> Real) (s : Set α) : μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal (exp (f a) /
 ∫ x, exp (f x) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用定理 `MeasureTheory.Integrable.div_const`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedDivisionRing 𝕜] 
  {f : α → 𝕜}, MeasureTh…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
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
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.tilted_of_not_integrable`：tilted_of_not_integrable (hf : ¬
 Integrable (fun x => exp (f x)) μ) : μ.tilted f = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
（共 31 条，此处仅展示前 30 条）
-/
lemma tilted_apply_eq_ofReal_integral [SFinite μ] (f : α → ℝ) (s : Set α) :
    μ.tilted f s = ENNReal.ofReal (∫ a in s, exp (f a) / ∫ x, exp (f x) ∂μ ∂μ) := by
  by_cases hf : Integrable (fun x ↦ exp (f x)) μ
  · rw [tilted_apply _ _, ← ofReal_integral_eq_lintegral_ofReal]
    · exact hf.integrableOn.div_const _
    · exact ae_of_all _ (fun _ ↦ by positivity)
  · simp [tilted_of_not_integrable hf, integral_undef hf]
/-
**MeasureTheory.isProbabilityMeasure_tilted** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：isProbabilityMeasure_tilted [NeZero μ] (hf : Integrable (fun x => exp (f x
)) μ) : IsProbabilityMeasure (μ.tilted f)
参数：hf : Integrable (fun x => exp (f x)) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.tilted_apply'`：tilted_apply' (μ : Measure α) (f : α -> Rea
l) {s : Set α} (hs : MeasurableSet s) : μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal
 (exp (f a) / ∫ x…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.ofReal_div_of_pos`：ofReal_div_of_pos {x y : Real} (hy : 0 < y) :
 ENNReal.ofReal (x / y) = ENNReal.ofReal x / ENNReal.ofReal y
· 使用引理 `MeasureTheory.integral_exp_pos`：integral_exp_pos {μ : Measure α} {f : α 
-> Real} [hμ : NeZero μ] (hf : Integrable (fun x => Real.exp (f x)) μ) : 0 < ∫ x
, Real.exp (f x) ∂μ
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `MeasureTheory.lintegral_mul_const''`：lintegral_mul_const'' (r : Real>=0∞
) {f : α -> Real>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ
) * r
· 使用引理 `AEMeasurable.ennreal_ofReal`：AEMeasurable.ennreal_ofReal {f : α -> Real}
 {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ENNReal.ofReal
 (f x)) μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma isProbabilityMeasure_tilted [NeZero μ] (hf : Integrable (fun x ↦ exp (f x)) μ) :
    IsProbabilityMeasure (μ.tilted f) := by
  constructor
  simp_rw [tilted_apply' _ _ MeasurableSet.univ, setLIntegral_univ,
    ENNReal.ofReal_div_of_pos (integral_exp_pos hf), div_eq_mul_inv]
  rw [lintegral_mul_const'' _ hf.1.aemeasurable.ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun _ ↦ (exp_pos _).le),
    ENNReal.mul_inv_cancel]
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact integral_exp_pos hf
  · simp
/-
**MeasureTheory.isZeroOrProbabilityMeasure_tilted** 是 Mathlib 中的一个实例，位于命名空间 `Mea
sureTheory`。
形式化陈述：isZeroOrProbabilityMeasure_tilted : IsZeroOrProbabilityMeasure (μ.tilted f
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.tilted_zero_measure`：tilted_zero_measure (f : α -> Real) :
 (0 : Measure α).tilted f = 0
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfNatMeasure`：∀ {α : Type u_
1} {m0 : MeasurableSpace α}, MeasureTheory.IsZeroOrProbabilityMeasure 0
· 使用引理 `MeasureTheory.isProbabilityMeasure_tilted`：isProbabilityMeasure_tilted [
NeZero μ] (hf : Integrable (fun x => exp (f x)) μ) : IsProbabilityMeasure (μ.til
ted f)
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用引理 `MeasureTheory.tilted_of_not_integrable`：tilted_of_not_integrable (hf : ¬
 Integrable (fun x => exp (f x)) μ) : μ.tilted f = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
instance isZeroOrProbabilityMeasure_tilted : IsZeroOrProbabilityMeasure (μ.tilted f) := by
  rcases eq_zero_or_neZero μ with hμ | hμ
  · simp only [hμ, tilted_zero_measure]
    infer_instance
  by_cases hf : Integrable (fun x ↦ exp (f x)) μ
  · have := isProbabilityMeasure_tilted hf
    infer_instance
  · simp only [hf, not_false_eq_true, tilted_of_not_integrable]
    infer_instance

section lintegral

/-
**MeasureTheory.setLIntegral_tilted'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_tilted' (f : α -> Real) (g : α -> Real>=0∞) {s : Set α} (hs :
 MeasurableSet s) : ∫⁻ x in s, g x ∂(μ.tilted f) = ∫⁻ x in s, ENNReal.ofReal (ex
p (f x) / ∫ x, exp (f x) ∂μ) * g x ∂μ
参数：f : α -> Real；g : α -> Real>=0∞；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.tilted.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpac
e α} (μ : MeasureTheory.Measure α) (f : α → ℝ),   μ.tilted f = μ.withDensity fun
 x => ENNReal.ofReal (R…
· 使用定理 `MeasureTheory.setLIntegral_withDensity_eq_setLIntegral_mul_non_measurabl
e₀`：setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ (μ : Measure α)
 {f : α -> Real>=0∞} {s : Set α} (hf : AEMeasurable f (μ.restric…
· 使用定理 `AEMeasurable.restrict`：AEMeasurable.restrict (hfm : AEMeasurable f μ) {s
} : AEMeasurable f (μ.restrict s)
· 使用引理 `AEMeasurable.ennreal_ofReal`：AEMeasurable.ennreal_ofReal {f : α -> Real}
 {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ENNReal.ofReal
 (f x)) μ
· 使用定理 `AEMeasurable.div_const`：AEMeasurable.div_const [MeasurableDiv G] (hf : A
EMeasurable f μ) (c : G) : AEMeasurable (fun x => f x / c) μ
· 使用定理 `measurableDiv_of_mul_inv`：∀ (G : Type u_2) [inst : MeasurableSpace G] [i
nst_1 : DivInvMonoid G] [MeasurableMul G] [MeasurableInv G],   MeasurableDiv G
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousInv₀.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : GroupWithZero γ]   [T1S
pace γ] [Continuou…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Real.measurable_exp`：measurable_exp : Measurable exp
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Real.aemeasurable_of_aemeasurable_exp`：aemeasurable_of_aemeasurable_exp 
(hf : AEMeasurable (fun x => exp (f x)) μ) : AEMeasurable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
（共 46 条，此处仅展示前 30 条）
-/
lemma setLIntegral_tilted' (f : α → ℝ) (g : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, g x ∂(μ.tilted f)
      = ∫⁻ x in s, ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ) * g x ∂μ := by
  by_cases hf : AEMeasurable f μ
  · rw [Measure.tilted, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀]
    · simp only [Pi.mul_apply]
    · refine AEMeasurable.restrict ?_
      exact ((measurable_exp.comp_aemeasurable hf).div_const _).ennreal_ofReal
    · exact hs
    · filter_upwards
      simp only [ENNReal.ofReal_lt_top, implies_true]
  · have hf' : ¬ Integrable (fun x ↦ exp (f x)) μ := by
      exact fun h ↦ hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      lintegral_zero_measure]
    rw [integral_undef hf']
    simp
/-
**MeasureTheory.setLIntegral_tilted** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_tilted [SFinite μ] (f : α -> Real) (g : α -> Real>=0∞) (s : S
et α) : ∫⁻ x in s, g x ∂(μ.tilted f) = ∫⁻ x in s, ENNReal.ofReal (exp (f x) / ∫ 
x, exp (f x) ∂μ) * g x ∂μ
参数：f : α -> Real；g : α -> Real>=0∞；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.tilted.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpac
e α} (μ : MeasureTheory.Measure α) (f : α → ℝ),   μ.tilted f = μ.withDensity fun
 x => ENNReal.ofReal (R…
· 使用定理 `MeasureTheory.setLIntegral_withDensity_eq_setLIntegral_mul_non_measurabl
e₀'`：setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀' (μ : Measure 
α) [SFinite μ] {f : α -> Real>=0∞} (s : Set α) (hf : AEMeasurable…
· 使用定理 `AEMeasurable.restrict`：AEMeasurable.restrict (hfm : AEMeasurable f μ) {s
} : AEMeasurable f (μ.restrict s)
· 使用引理 `AEMeasurable.ennreal_ofReal`：AEMeasurable.ennreal_ofReal {f : α -> Real}
 {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ENNReal.ofReal
 (f x)) μ
· 使用定理 `AEMeasurable.div_const`：AEMeasurable.div_const [MeasurableDiv G] (hf : A
EMeasurable f μ) (c : G) : AEMeasurable (fun x => f x / c) μ
· 使用定理 `measurableDiv_of_mul_inv`：∀ (G : Type u_2) [inst : MeasurableSpace G] [i
nst_1 : DivInvMonoid G] [MeasurableMul G] [MeasurableInv G],   MeasurableDiv G
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousInv₀.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : GroupWithZero γ]   [T1S
pace γ] [Continuou…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Real.measurable_exp`：measurable_exp : Measurable exp
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Real.aemeasurable_of_aemeasurable_exp`：aemeasurable_of_aemeasurable_exp 
(hf : AEMeasurable (fun x => exp (f x)) μ) : AEMeasurable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
（共 46 条，此处仅展示前 30 条）
-/
lemma setLIntegral_tilted [SFinite μ] (f : α → ℝ) (g : α → ℝ≥0∞) (s : Set α) :
    ∫⁻ x in s, g x ∂(μ.tilted f)
      = ∫⁻ x in s, ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ) * g x ∂μ := by
  by_cases hf : AEMeasurable f μ
  · rw [Measure.tilted, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀']
    · simp only [Pi.mul_apply]
    · refine AEMeasurable.restrict ?_
      exact ((measurable_exp.comp_aemeasurable hf).div_const _).ennreal_ofReal
    · filter_upwards
      simp only [ENNReal.ofReal_lt_top, implies_true]
  · have hf' : ¬ Integrable (fun x ↦ exp (f x)) μ := by
      exact fun h ↦ hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      lintegral_zero_measure]
    rw [integral_undef hf']
    simp
/-
**MeasureTheory.lintegral_tilted** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_tilted (f : α -> Real) (g : α -> Real>=0∞) : ∫⁻ x, g x ∂(μ.tilte
d f) = ∫⁻ x, ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ) * (g x) ∂μ
参数：f : α -> Real；g : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用引理 `MeasureTheory.setLIntegral_tilted'`：setLIntegral_tilted' (f : α -> Real)
 (g : α -> Real>=0∞) {s : Set α} (hs : MeasurableSet s) : ∫⁻ x in s, g x ∂(μ.til
ted f) = ∫⁻ x in s, ENNR…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
lemma lintegral_tilted (f : α → ℝ) (g : α → ℝ≥0∞) :
    ∫⁻ x, g x ∂(μ.tilted f)
      = ∫⁻ x, ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ) * (g x) ∂μ := by
  rw [← setLIntegral_univ, setLIntegral_tilted' f g MeasurableSet.univ, setLIntegral_univ]

end lintegral

section integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
**MeasureTheory.setIntegral_tilted'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_tilted' (f : α -> Real) (g : α -> E) {s : Set α} (hs : Measura
bleSet s) : ∫ x in s, g x ∂(μ.tilted f) = ∫ x in s, (exp (f x) / ∫ x, exp (f x) 
∂μ) • (g x) ∂μ
参数：f : α -> Real；g : α -> E；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.tilted_eq_withDensity_nnreal`：tilted_eq_withDensity_nnreal
 (μ : Measure α) (f : α -> Real) : μ.tilted f = μ.withDensity (fun x => ((↑) : R
eal>=0 -> Real>=0∞) (.mk (exp (f…
· 使用定理 `setIntegral_withDensity_eq_setIntegral_smul₀`：setIntegral_withDensity_eq
_setIntegral_smul₀ {f : X -> Real>=0} {s : Set X} (hf : AEMeasurable f (μ.restri
ct s)) (g : X -> E) (hs : Measurab…
· 使用定理 `AEMeasurable.div_const`：AEMeasurable.div_const [MeasurableDiv G] (hf : A
EMeasurable f μ) (c : G) : AEMeasurable (fun x => f x / c) μ
· 使用定理 `measurableDiv_of_mul_inv`：∀ (G : Type u_2) [inst : MeasurableSpace G] [i
nst_1 : DivInvMonoid G] [MeasurableMul G] [MeasurableInv G],   MeasurableDiv G
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousInv₀.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : GroupWithZero γ]   [T1S
pace γ] [Continuou…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Real.measurable_exp`：measurable_exp : Measurable exp
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `aemeasurable_coe_nnreal_real_iff`：aemeasurable_coe_nnreal_real_iff {f : 
α -> Real>=0} {μ : Measure α} : AEMeasurable (fun x => f x : α -> Real) μ ↔ AEMe
asurable f μ
· 使用定理 `AEMeasurable.restrict`：AEMeasurable.restrict (hfm : AEMeasurable f μ) {s
} : AEMeasurable f (μ.restrict s)
· 使用引理 `Real.aemeasurable_of_aemeasurable_exp`：aemeasurable_of_aemeasurable_exp 
(hf : AEMeasurable (fun x => exp (f x)) μ) : AEMeasurable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MeasureTheory.tilted_of_not_aemeasurable`：tilted_of_not_aemeasurable (hf
 : ¬ AEMeasurable f μ) : μ.tilted f = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 40 条，此处仅展示前 30 条）
-/
lemma setIntegral_tilted' (f : α → ℝ) (g : α → E) {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.tilted f) = ∫ x in s, (exp (f x) / ∫ x, exp (f x) ∂μ) • (g x) ∂μ := by
  by_cases hf : AEMeasurable f μ
  · rw [tilted_eq_withDensity_nnreal, setIntegral_withDensity_eq_setIntegral_smul₀ _ _ hs]
    · congr
    · suffices AEMeasurable (fun x ↦ exp (f x) / ∫ x, exp (f x) ∂μ) μ by
        rw [← aemeasurable_coe_nnreal_real_iff]
        refine AEMeasurable.restrict ?_
        simpa only [NNReal.coe_mk]
      exact (measurable_exp.comp_aemeasurable hf).div_const _
  · have hf' : ¬ Integrable (fun x ↦ exp (f x)) μ := by
      exact fun h ↦ hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      integral_zero_measure]
    rw [integral_undef hf']
    simp
/-
**MeasureTheory.setIntegral_tilted** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_tilted [SFinite μ] (f : α -> Real) (g : α -> E) (s : Set α) : 
∫ x in s, g x ∂(μ.tilted f) = ∫ x in s, (exp (f x) / ∫ x, exp (f x) ∂μ) • (g x) 
∂μ
参数：f : α -> Real；g : α -> E；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.tilted_eq_withDensity_nnreal`：tilted_eq_withDensity_nnreal
 (μ : Measure α) (f : α -> Real) : μ.tilted f = μ.withDensity (fun x => ((↑) : R
eal>=0 -> Real>=0∞) (.mk (exp (f…
· 使用定理 `setIntegral_withDensity_eq_setIntegral_smul₀'`：setIntegral_withDensity_e
q_setIntegral_smul₀' [SFinite μ] {f : X -> Real>=0} (s : Set X) (hf : AEMeasurab
le f (μ.restrict s)) (g : X -> E) :…
· 使用定理 `AEMeasurable.div_const`：AEMeasurable.div_const [MeasurableDiv G] (hf : A
EMeasurable f μ) (c : G) : AEMeasurable (fun x => f x / c) μ
· 使用定理 `measurableDiv_of_mul_inv`：∀ (G : Type u_2) [inst : MeasurableSpace G] [i
nst_1 : DivInvMonoid G] [MeasurableMul G] [MeasurableInv G],   MeasurableDiv G
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousInv₀.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : GroupWithZero γ]   [T1S
pace γ] [Continuou…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Real.measurable_exp`：measurable_exp : Measurable exp
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `aemeasurable_coe_nnreal_real_iff`：aemeasurable_coe_nnreal_real_iff {f : 
α -> Real>=0} {μ : Measure α} : AEMeasurable (fun x => f x : α -> Real) μ ↔ AEMe
asurable f μ
· 使用定理 `AEMeasurable.restrict`：AEMeasurable.restrict (hfm : AEMeasurable f μ) {s
} : AEMeasurable f (μ.restrict s)
· 使用引理 `Real.aemeasurable_of_aemeasurable_exp`：aemeasurable_of_aemeasurable_exp 
(hf : AEMeasurable (fun x => exp (f x)) μ) : AEMeasurable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MeasureTheory.tilted_of_not_aemeasurable`：tilted_of_not_aemeasurable (hf
 : ¬ AEMeasurable f μ) : μ.tilted f = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 40 条，此处仅展示前 30 条）
-/
lemma setIntegral_tilted [SFinite μ] (f : α → ℝ) (g : α → E) (s : Set α) :
    ∫ x in s, g x ∂(μ.tilted f) = ∫ x in s, (exp (f x) / ∫ x, exp (f x) ∂μ) • (g x) ∂μ := by
  by_cases hf : AEMeasurable f μ
  · rw [tilted_eq_withDensity_nnreal, setIntegral_withDensity_eq_setIntegral_smul₀']
    · congr
    · suffices AEMeasurable (fun x ↦ exp (f x) / ∫ x, exp (f x) ∂μ) μ by
        rw [← aemeasurable_coe_nnreal_real_iff]
        refine AEMeasurable.restrict ?_
        simpa only [NNReal.coe_mk]
      exact (measurable_exp.comp_aemeasurable hf).div_const _
  · have hf' : ¬ Integrable (fun x ↦ exp (f x)) μ := by
      exact fun h ↦ hf (aemeasurable_of_aemeasurable_exp h.1.aemeasurable)
    simp only [hf, not_false_eq_true, tilted_of_not_aemeasurable, Measure.restrict_zero,
      integral_zero_measure]
    rw [integral_undef hf']
    simp
/-
**MeasureTheory.integral_tilted** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_tilted (f : α -> Real) (g : α -> E) : ∫ x, g x ∂(μ.tilted f) = ∫ 
x, (exp (f x) / ∫ x, exp (f x) ∂μ) • (g x) ∂μ
参数：f : α -> Real；g : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用引理 `MeasureTheory.setIntegral_tilted'`：setIntegral_tilted' (f : α -> Real) (
g : α -> E) {s : Set α} (hs : MeasurableSet s) : ∫ x in s, g x ∂(μ.tilted f) = ∫
 x in s, (exp (f x) / ∫…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
lemma integral_tilted (f : α → ℝ) (g : α → E) :
    ∫ x, g x ∂(μ.tilted f) = ∫ x, (exp (f x) / ∫ x, exp (f x) ∂μ) • (g x) ∂μ := by
  rw [← setIntegral_univ, setIntegral_tilted' f g MeasurableSet.univ, setIntegral_univ]

end integral

/-
**MeasureTheory.integral_exp_tilted** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_exp_tilted (f g : α -> Real) : ∫ x, exp (g x) ∂(μ.tilted f) = (∫ 
x, exp ((f + g) x) ∂μ) / ∫ x, exp (f x) ∂μ
参数：f g : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.tilted_zero_measure`：tilted_zero_measure (f : α -> Real) :
 (0 : Measure α).tilted f = 0
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.integral_tilted`：integral_tilted (f : α -> Real) (g : α ->
 E) : ∫ x, g x ∂(μ.tilted f) = ∫ x, (exp (f x) / ∫ x, exp (f x) ∂μ) • (g x) ∂μ
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 38 条，此处仅展示前 30 条）
-/
lemma integral_exp_tilted (f g : α → ℝ) :
    ∫ x, exp (g x) ∂(μ.tilted f) = (∫ x, exp ((f + g) x) ∂μ) / ∫ x, exp (f x) ∂μ := by
  cases eq_zero_or_neZero μ with
  | inl h => rw [h]; simp
  | inr h0 =>
    rw [integral_tilted f]
    simp_rw [smul_eq_mul]
    have : ∀ x, (exp (f x) / ∫ x, exp (f x) ∂μ) * exp (g x)
        = (exp ((f + g) x) / ∫ x, exp (f x) ∂μ) := by
      intro x
      rw [Pi.add_apply, exp_add]
      ring
    simp_rw [this, div_eq_mul_inv]
    rw [integral_mul_const]
/-
**MeasureTheory.tilted_tilted** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：tilted_tilted (hf : Integrable (fun x => exp (f x)) μ) (g : α -> Real) : (
μ.tilted f).tilted g = μ.tilted (f + g)
参数：hf : Integrable (fun x => exp (f x)) μ；g : α -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.tilted_zero_measure`：tilted_zero_measure (f : α -> Real) :
 (0 : Measure α).tilted f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用引理 `MeasureTheory.tilted_apply'`：tilted_apply' (μ : Measure α) (f : α -> Rea
l) {s : Set α} (hs : MeasurableSet s) : μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal
 (exp (f a) / ∫ x…
· 使用引理 `MeasureTheory.setLIntegral_tilted'`：setLIntegral_tilted' (f : α -> Real)
 (g : α -> Real>=0∞) {s : Set α} (hs : MeasurableSet s) : ∫⁻ x in s, g x ∂(μ.til
ted f) = ∫⁻ x in s, ENNR…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
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
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `MeasureTheory.integral_exp_tilted`：integral_exp_tilted (f g : α -> Real)
 : ∫ x, exp (g x) ∂(μ.tilted f) = (∫ x, exp ((f + g) x) ∂μ) / ∫ x, exp (f x) ∂μ
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
（共 61 条，此处仅展示前 30 条）
-/
lemma tilted_tilted (hf : Integrable (fun x ↦ exp (f x)) μ) (g : α → ℝ) :
    (μ.tilted f).tilted g = μ.tilted (f + g) := by
  cases eq_zero_or_neZero μ with
  | inl h => simp [h]
  | inr h0 =>
    ext1 s hs
    rw [tilted_apply' _ _ hs, tilted_apply' _ _ hs, setLIntegral_tilted' f _ hs]
    congr with x
    rw [← ENNReal.ofReal_mul (by positivity),
      integral_exp_tilted f, Pi.add_apply, exp_add]
    congr 1
    simp only [Pi.add_apply]
    have := (integral_exp_pos hf).ne'
    simp [field]
/-
**MeasureTheory.tilted_comm** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：tilted_comm (hf : Integrable (fun x => exp (f x)) μ) {g : α -> Real} (hg :
 Integrable (fun x => exp (g x)) μ) : (μ.tilted f).tilted g = (μ.tilted g).tilte
d f
参数：hf : Integrable (fun x => exp (f x)) μ；hg : Integrable (fun x => exp (g x)) μ
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.tilted_tilted`：tilted_tilted (hf : Integrable (fun x => ex
p (f x)) μ) (g : α -> Real) : (μ.tilted f).tilted g = μ.tilted (f + g)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma tilted_comm (hf : Integrable (fun x ↦ exp (f x)) μ) {g : α → ℝ}
    (hg : Integrable (fun x ↦ exp (g x)) μ) :
    (μ.tilted f).tilted g = (μ.tilted g).tilted f := by
  rw [tilted_tilted hf, add_comm, tilted_tilted hg]

@[simp]
/-
**MeasureTheory.tilted_neg_same'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：tilted_neg_same' (hf : Integrable (fun x => exp (f x)) μ) : (μ.tilted f).t
ilted (-f) = (μ Set.univ)⁻¹ • μ
参数：hf : Integrable (fun x => exp (f x)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.tilted_tilted`：tilted_tilted (hf : Integrable (fun x => ex
p (f x)) μ) (g : α -> Real) : (μ.tilted f).tilted g = μ.tilted (f + g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用引理 `MeasureTheory.tilted_zero'`：tilted_zero' (μ : Measure α) : μ.tilted 0 = 
(μ Set.univ)⁻¹ • μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tilted_neg_same' (hf : Integrable (fun x ↦ exp (f x)) μ) :
    (μ.tilted f).tilted (-f) = (μ Set.univ)⁻¹ • μ := by
  rw [tilted_tilted hf]; simp
/-
**MeasureTheory.tilted_neg_same** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：tilted_neg_same [IsProbabilityMeasure μ] (hf : Integrable (fun x => exp (f
 x)) μ) : (μ.tilted f).tilted (-f) = μ
参数：hf : Integrable (fun x => exp (f x)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.tilted_neg_same'`：tilted_neg_same' (hf : Integrable (fun x
 => exp (f x)) μ) : (μ.tilted f).tilted (-f) = (μ Set.univ)⁻¹ • μ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tilted_neg_same [IsProbabilityMeasure μ] (hf : Integrable (fun x ↦ exp (f x)) μ) :
    (μ.tilted f).tilted (-f) = μ := by
  simp [hf]
/-
**MeasureTheory.tilted_absolutelyContinuous** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：tilted_absolutelyContinuous (μ : Measure α) (f : α -> Real) : μ.tilted f ≪
 μ
参数：μ : Measure α；f : α -> Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
-/
lemma tilted_absolutelyContinuous (μ : Measure α) (f : α → ℝ) : μ.tilted f ≪ μ :=
  withDensity_absolutelyContinuous _ _
/-
**MeasureTheory.absolutelyContinuous_tilted** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：absolutelyContinuous_tilted (hf : Integrable (fun x => exp (f x)) μ) : μ ≪
 μ.tilted f
参数：hf : Integrable (fun x => exp (f x)) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.tilted_zero_measure`：tilted_zero_measure (f : α -> Real) :
 (0 : Measure α).tilted f = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.withDensity_absolutelyContinuous'`：withDensity_absolutelyC
ontinuous' {μ : Measure α} {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (hf_ne_ze
ro : forallᵐ x ∂μ, f x != 0) : μ ≪ μ.…
· 使用引理 `AEMeasurable.ennreal_ofReal`：AEMeasurable.ennreal_ofReal {f : α -> Real}
 {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ENNReal.ofReal
 (f x)) μ
· 使用定理 `AEMeasurable.div_const`：AEMeasurable.div_const [MeasurableDiv G] (hf : A
EMeasurable f μ) (c : G) : AEMeasurable (fun x => f x / c) μ
· 使用定理 `measurableDiv_of_mul_inv`：∀ (G : Type u_2) [inst : MeasurableSpace G] [i
nst_1 : DivInvMonoid G] [MeasurableMul G] [MeasurableInv G],   MeasurableDiv G
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousInv₀.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : GroupWithZero γ]   [T1S
pace γ] [Continuou…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 36 条，此处仅展示前 30 条）
-/
lemma absolutelyContinuous_tilted (hf : Integrable (fun x ↦ exp (f x)) μ) : μ ≪ μ.tilted f := by
  cases eq_zero_or_neZero μ with
  | inl h => simp only [h, tilted_zero_measure]; exact fun _ _ ↦ by simp
  | inr h0 =>
    refine withDensity_absolutelyContinuous' ?_ ?_
    · exact (hf.1.aemeasurable.div_const _).ennreal_ofReal
    · filter_upwards
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact fun _ ↦ div_pos (exp_pos _) (integral_exp_pos hf)
/-
**MeasureTheory.integrable_tilted_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_tilted_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace Real
 E] {f : α -> Real} (hf : Integrable (fun x => exp (f x)) μ) (g : α -> E) : Inte
grable g (μ.tilted f) ↔ Integrable (fun x => exp (f x) • g x) μ
参数：hf : Integrable (fun x => exp (f x)) μ；g : α -> E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.tilted_zero_measure`：tilted_zero_measure (f : α -> Real) :
 (0 : Measure α).tilted f = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Real.aemeasurable_of_aemeasurable_exp`：aemeasurable_of_aemeasurable_exp 
(hf : AEMeasurable (fun x => exp (f x)) μ) : AEMeasurable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Measure.tilted.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpac
e α} (μ : MeasureTheory.Measure α) (f : α → ℝ),   μ.tilted f = μ.withDensity fun
 x => ENNReal.ofReal (R…
· 使用定理 `MeasureTheory.integrable_withDensity_iff_integrable_smul₀'`：integrable_w
ithDensity_iff_integrable_smul₀' {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (hf
lt : forallᵐ x ∂μ, f x < ∞) {g : α -> E} : Integ…
· 使用引理 `AEMeasurable.ennreal_ofReal`：AEMeasurable.ennreal_ofReal {f : α -> Real}
 {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ENNReal.ofReal
 (f x)) μ
· 使用定理 `AEMeasurable.div_const`：AEMeasurable.div_const [MeasurableDiv G] (hf : A
EMeasurable f μ) (c : G) : AEMeasurable (fun x => f x / c) μ
· 使用定理 `measurableDiv_of_mul_inv`：∀ (G : Type u_2) [inst : MeasurableSpace G] [i
nst_1 : DivInvMonoid G] [MeasurableMul G] [MeasurableInv G],   MeasurableDiv G
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousInv₀.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : GroupWithZero γ]   [T1S
pace γ] [Continuou…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `AEMeasurable.exp`：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureT
heory.Measure α} {f : α → ℝ},   AEMeasurable f μ → AEMeasurable (fun x => Real.e
xp (f …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
（共 53 条，此处仅展示前 30 条）
-/
lemma integrable_tilted_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α → ℝ} (hf : Integrable (fun x ↦ exp (f x)) μ) (g : α → E) :
    Integrable g (μ.tilted f) ↔ Integrable (fun x ↦ exp (f x) • g x) μ := by
  by_cases hμ : μ = 0
  · simp [hμ]
  have hf_meas : AEMeasurable f μ := aemeasurable_of_aemeasurable_exp hf.1.aemeasurable
  rw [Measure.tilted, integrable_withDensity_iff_integrable_smul₀' (by fun_prop) (by simp)]
  calc Integrable (fun x ↦ (ENNReal.ofReal (exp (f x) / ∫ a, exp (f a) ∂μ)).toReal • g x) μ
  _ ↔ Integrable (fun x ↦ (exp (f x) / ∫ a, exp (f a) ∂μ) • g x) μ := by
    congr! with a
    rw [ENNReal.toReal_ofReal]
    positivity
  _ ↔ Integrable (fun x ↦ (∫ a, exp (f a) ∂μ)⁻¹ • exp (f x) • g x) μ := by
    congr! 2 with a
    rw [smul_smul, div_eq_inv_mul]
  _ ↔ Integrable (fun x ↦ exp (f x) • g x) μ := by
    rw [integrable_fun_smul_iff]
    simp only [ne_eq, inv_eq_zero]
    have : NeZero μ := ⟨hμ⟩
    exact (integral_exp_pos hf).ne'
/-
**MeasureTheory.rnDeriv_tilted_right** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：rnDeriv_tilted_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] (hf
 : Integrable (fun x => exp (f x)) ν) : μ.rnDeriv (ν.tilted f) =ᵐ[ν] fun x => EN
NReal.ofReal (exp (-f x) * ∫ x, exp (f x) ∂ν) * μ.rnDeriv ν x
参数：μ ν : Measure α；hf : Integrable (fun x => exp (f x)) ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `Filter.eventually_bot`：eventually_bot {p : α -> Prop} : forallᶠ x in ⊥, 
p x
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用引理 `MeasureTheory.Measure.rnDeriv_withDensity_right`：rnDeriv_withDensity_rig
ht (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] (hf : AEMeasurable f ν) (hf
_ne_zero : forallᵐ x ∂ν, f x != 0) (h…
· 使用引理 `AEMeasurable.ennreal_ofReal`：AEMeasurable.ennreal_ofReal {f : α -> Real}
 {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ENNReal.ofReal
 (f x)) μ
· 使用定理 `AEMeasurable.div_const`：AEMeasurable.div_const [MeasurableDiv G] (hf : A
EMeasurable f μ) (c : G) : AEMeasurable (fun x => f x / c) μ
· 使用定理 `measurableDiv_of_mul_inv`：∀ (G : Type u_2) [inst : MeasurableSpace G] [i
nst_1 : DivInvMonoid G] [MeasurableMul G] [MeasurableInv G],   MeasurableDiv G
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousInv₀.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : GroupWithZero γ]   [T1S
pace γ] [Continuou…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
（共 48 条，此处仅展示前 30 条）
-/
lemma rnDeriv_tilted_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hf : Integrable (fun x ↦ exp (f x)) ν) :
    μ.rnDeriv (ν.tilted f)
      =ᵐ[ν] fun x ↦ ENNReal.ofReal (exp (-f x) * ∫ x, exp (f x) ∂ν) * μ.rnDeriv ν x := by
  cases eq_zero_or_neZero ν with
  | inl h => simp_rw [h, ae_zero, Filter.EventuallyEq]; exact Filter.eventually_bot
  | inr h0 =>
    refine (Measure.rnDeriv_withDensity_right μ ν ?_ ?_ ?_).trans ?_
    · exact (hf.1.aemeasurable.div_const _).ennreal_ofReal
    · filter_upwards
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact fun _ ↦ div_pos (exp_pos _) (integral_exp_pos hf)
    · refine ae_of_all _ (by simp)
    · filter_upwards with x
      congr
      rw [← ENNReal.ofReal_inv_of_pos, inv_div', ← exp_neg, div_eq_mul_inv, inv_inv]
      exact div_pos (exp_pos _) (integral_exp_pos hf)
/-
**MeasureTheory.toReal_rnDeriv_tilted_right** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：toReal_rnDeriv_tilted_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite
 ν] (hf : Integrable (fun x => exp (f x)) ν) : (fun x => (μ.rnDeriv (ν.tilted f)
 x).toReal) =ᵐ[ν] fun x => exp (-f x) * (∫ x, exp (f x) ∂ν) * (μ.rnDeriv ν x).to
Real
参数：μ ν : Measure α；hf : Integrable (fun x => exp (f x)) ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.rnDeriv_tilted_right`：rnDeriv_tilted_right (μ ν : Measure 
α) [SigmaFinite μ] [SigmaFinite ν] (hf : Integrable (fun x => exp (f x)) ν) : μ.
rnDeriv (ν.tilted f) =ᵐ[…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
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
-/
lemma toReal_rnDeriv_tilted_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hf : Integrable (fun x ↦ exp (f x)) ν) :
    (fun x ↦ (μ.rnDeriv (ν.tilted f) x).toReal)
      =ᵐ[ν] fun x ↦ exp (-f x) * (∫ x, exp (f x) ∂ν) * (μ.rnDeriv ν x).toReal := by
  filter_upwards [rnDeriv_tilted_right μ ν hf] with x hx
  rw [hx]
  simp only [ENNReal.toReal_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
  exact Or.inl (by positivity)

variable (μ) in
/-
**MeasureTheory.rnDeriv_tilted_left** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：rnDeriv_tilted_left {ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hfν :
 AEMeasurable f ν) : (μ.tilted f).rnDeriv ν =ᵐ[ν] fun x => ENNReal.ofReal (exp (
f x) / (∫ x, exp (f x) ∂μ)) * μ.rnDeriv ν x
参数：hfν : AEMeasurable f ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.rnDeriv_withDensity_left`：rnDeriv_withDensity_left
 {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hfν : AEMeasurable f ν) (hf_
ne_top : forallᵐ x ∂μ, f x != ∞) : (…
· 使用引理 `AEMeasurable.ennreal_ofReal`：AEMeasurable.ennreal_ofReal {f : α -> Real}
 {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ENNReal.ofReal
 (f x)) μ
· 使用定理 `AEMeasurable.div_const`：AEMeasurable.div_const [MeasurableDiv G] (hf : A
EMeasurable f μ) (c : G) : AEMeasurable (fun x => f x / c) μ
· 使用定理 `measurableDiv_of_mul_inv`：∀ (G : Type u_2) [inst : MeasurableSpace G] [i
nst_1 : DivInvMonoid G] [MeasurableMul G] [MeasurableInv G],   MeasurableDiv G
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousInv₀.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : GroupWithZero γ]   [T1S
pace γ] [Continuou…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Real.measurable_exp`：measurable_exp : Measurable exp
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma rnDeriv_tilted_left {ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hfν : AEMeasurable f ν) :
    (μ.tilted f).rnDeriv ν
      =ᵐ[ν] fun x ↦ ENNReal.ofReal (exp (f x) / (∫ x, exp (f x) ∂μ)) * μ.rnDeriv ν x := by
  let g := fun x ↦ ENNReal.ofReal (exp (f x) / (∫ x, exp (f x) ∂μ))
  refine Measure.rnDeriv_withDensity_left (μ := μ) (ν := ν) (f := g) ?_ ?_
  · exact ((measurable_exp.comp_aemeasurable hfν).div_const _).ennreal_ofReal
  · exact ae_of_all _ (fun x ↦ by simp [g])

variable (μ) in
/-
**MeasureTheory.toReal_rnDeriv_tilted_left** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：toReal_rnDeriv_tilted_left {ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
 (hfν : AEMeasurable f ν) : (fun x => ((μ.tilted f).rnDeriv ν x).toReal) =ᵐ[ν] f
un x => exp (f x) / (∫ x, exp (f x) ∂μ) * (μ.rnDeriv ν x).toReal
参数：hfν : AEMeasurable f ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.rnDeriv_tilted_left`：rnDeriv_tilted_left {ν : Measure α} [
SigmaFinite μ] [SigmaFinite ν] (hfν : AEMeasurable f ν) : (μ.tilted f).rnDeriv ν
 =ᵐ[ν] fun x => ENNReal…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
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
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma toReal_rnDeriv_tilted_left {ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (hfν : AEMeasurable f ν) :
    (fun x ↦ ((μ.tilted f).rnDeriv ν x).toReal)
      =ᵐ[ν] fun x ↦ exp (f x) / (∫ x, exp (f x) ∂μ) * (μ.rnDeriv ν x).toReal := by
  filter_upwards [rnDeriv_tilted_left μ hfν] with x hx
  rw [hx]
  simp only [ENNReal.toReal_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
  exact Or.inl (by positivity)
/-
**MeasureTheory.rnDeriv_tilted_left_self** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：rnDeriv_tilted_left_self [SigmaFinite μ] (hf : AEMeasurable f μ) : (μ.tilt
ed f).rnDeriv μ =ᵐ[μ] fun x => ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ)
参数：hf : AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.rnDeriv_tilted_left`：rnDeriv_tilted_left {ν : Measure α} [
SigmaFinite μ] [SigmaFinite ν] (hfν : AEMeasurable f ν) : (μ.tilted f).rnDeriv ν
 =ᵐ[ν] fun x => ENNReal…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `MeasureTheory.Measure.rnDeriv_self`：rnDeriv_self (μ : Measure α) [SigmaF
inite μ] : μ.rnDeriv μ =ᵐ[μ] fun _ => 1
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma rnDeriv_tilted_left_self [SigmaFinite μ] (hf : AEMeasurable f μ) :
    (μ.tilted f).rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ) := by
  refine (rnDeriv_tilted_left μ hf).trans ?_
  filter_upwards [Measure.rnDeriv_self μ] with x hx
  rw [hx, mul_one]
/-
**MeasureTheory.log_rnDeriv_tilted_left_self** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory`。
形式化陈述：log_rnDeriv_tilted_left_self [SigmaFinite μ] (hf : Integrable (fun x => ex
p (f x)) μ) : (fun x => log ((μ.tilted f).rnDeriv μ x).toReal) =ᵐ[μ] fun x => f 
x - log (∫ x, exp (f x) ∂μ)
参数：hf : Integrable (fun x => exp (f x)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `Filter.eventually_bot`：eventually_bot {p : α -> Prop} : forallᶠ x in ⊥, 
p x
· 使用引理 `Real.aemeasurable_of_aemeasurable_exp`：aemeasurable_of_aemeasurable_exp 
(hf : AEMeasurable (fun x => exp (f x)) μ) : AEMeasurable f μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `MeasureTheory.rnDeriv_tilted_left_self`：rnDeriv_tilted_left_self [SigmaF
inite μ] (hf : AEMeasurable f μ) : (μ.tilted f).rnDeriv μ =ᵐ[μ] fun x => ENNReal
.ofReal (exp (f x) / ∫ x, ex…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_pos_of_nonneg`：div_nonneg_of_pos_o
f_nonneg [PosMulReflectLT α] (ha : 0 < a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
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
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.log_div`：log_div (hx : x != 0) (hy : y != 0) : log (x / y) = log x 
- log y
（共 33 条，此处仅展示前 30 条）
-/
lemma log_rnDeriv_tilted_left_self [SigmaFinite μ] (hf : Integrable (fun x ↦ exp (f x)) μ) :
    (fun x ↦ log ((μ.tilted f).rnDeriv μ x).toReal)
      =ᵐ[μ] fun x ↦ f x - log (∫ x, exp (f x) ∂μ) := by
  cases eq_zero_or_neZero μ with
  | inl h => simp_rw [h, ae_zero, Filter.EventuallyEq]; exact Filter.eventually_bot
  | inr h0 =>
    have hf' : AEMeasurable f μ := aemeasurable_of_aemeasurable_exp hf.1.aemeasurable
    filter_upwards [rnDeriv_tilted_left_self hf'] with x hx
    rw [hx, ENNReal.toReal_ofReal (by positivity), log_div (exp_pos _).ne', log_exp]
    exact (integral_exp_pos hf).ne'

end MeasureTheory

