/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies, Louis (Yiyang) Liu
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integral average of a function

In this file we define `MeasureTheory.average μ f` (notation: `⨍ x, f x ∂μ`) to be the average
value of `f` with respect to measure `μ`. It is defined as `∫ x, f x ∂((μ univ)⁻¹ • μ)`, so it
is equal to zero if `f` is not integrable or if `μ` is an infinite measure. If `μ` is a probability
measure, then the average of any function is equal to its integral.

For the average on a set, we use `⨍ x in s, f x ∂μ` (notation for `⨍ x, f x ∂(μ.restrict s)`). For
average w.r.t. the volume, one can omit `∂volume`.

Both have a version for the Lebesgue integral rather than Bochner.

We prove several versions of the first moment method: An integrable function is below/above its
average on a set of positive measure:
* `measure_le_setLAverage_pos` for the Lebesgue integral
* `measure_le_setAverage_pos` for the Bochner integral

## Implementation notes

The average is defined as an integral over `(μ univ)⁻¹ • μ` so that all theorems about Bochner
integrals work for the average without modifications. For theorems that require integrability of a
function, we provide a convenience lemma `MeasureTheory.Integrable.to_average`.

## Tags

integral, center mass, average value, set average
-/

@[expose] public section


open ENNReal MeasureTheory MeasureTheory.Measure Metric Set Filter TopologicalSpace Function

open scoped Topology ENNReal Convex

variable {α E F : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {μ ν : Measure α}
  {s t : Set α}

/-!
### Average value of a function w.r.t. a measure

The (Bochner, Lebesgue) average value of a function `f` w.r.t. a measure `μ` (notation:
`⨍ x, f x ∂μ`, `⨍⁻ x, f x ∂μ`) is defined as the (Bochner, Lebesgue) integral divided by the total
measure, so it is equal to zero if `μ` is an infinite measure, and (typically) equal to infinity if
`f` is not integrable. If `μ` is a probability measure, then the average of any function is equal to
its integral.
-/

namespace MeasureTheory
section ENNReal
variable (μ) {f g : α → ℝ≥0∞}

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. a measure `μ`, denoted `⨍⁻ x, f x ∂μ`.

It is equal to `(μ univ)⁻¹ * ∫⁻ x, f x ∂μ`, so it takes value zero if `μ` is an infinite measure. If
`μ` is a probability measure, then the average of any function is equal to its integral.

For the average on a set, use `⨍⁻ x in s, f x ∂μ`, defined as `⨍⁻ x, f x ∂(μ.restrict s)`. For the
average w.r.t. the volume, one can omit `∂volume`. -/
/-
**MeasureTheory.laverage** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：laverage (f : α -> Real>=0∞)
参数：f : α -> Real>=0∞。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Average value of an `ℝ≥0∞`-valued function `f` w.r.t. a measure `μ`, denoted `⨍⁻
 x, f x ∂μ`.

It is equal to `(μ univ)⁻¹ * ∫⁻ x, f x ∂μ`, so it takes value zero if `μ` is an 
infinite measure. If
`μ` is a probability measure, then the average of any function is equal to its i
ntegral.

For the average on a set, use `⨍⁻ x in s, f x ∂μ`, defined as `⨍⁻ x, f x ∂(μ.res
trict s)`. For the
average w.r.t. the volume, one can omit `∂volume`.
-/
noncomputable def laverage (f : α → ℝ≥0∞) := ∫⁻ x, f x ∂(μ univ)⁻¹ • μ

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. a measure `μ`.

It is equal to `(μ univ)⁻¹ * ∫⁻ x, f x ∂μ`, so it takes value zero if `μ` is an infinite measure. If
`μ` is a probability measure, then the average of any function is equal to its integral.

For the average on a set, use `⨍⁻ x in s, f x ∂μ`, defined as `⨍⁻ x, f x ∂(μ.restrict s)`. For the
average w.r.t. the volume, one can omit `∂volume`. -/
notation3 "⨍⁻ " (...) ", " r:60:(scoped f => f) " ∂" μ:70 => laverage μ r

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. the standard measure.

It is equal to `(volume univ)⁻¹ * ∫⁻ x, f x`, so it takes value zero if the space has infinite
measure. In a probability space, the average of any function is equal to its integral.

For the average on a set, use `⨍⁻ x in s, f x`, defined as `⨍⁻ x, f x ∂(volume.restrict s)`. -/
notation3 "⨍⁻ " (...) ", " r:60:(scoped f => laverage volume f) => r

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. a measure `μ` on a set `s`.

It is equal to `(μ s)⁻¹ * ∫⁻ x, f x ∂μ`, so it takes value zero if `s` has infinite measure. If `s`
has measure `1`, then the average of any function is equal to its integral.

For the average w.r.t. the volume, one can omit `∂volume`. -/
notation3 "⨍⁻ " (...) " in " s ", " r:60:(scoped f => f) " ∂" μ:70 =>
  laverage (Measure.restrict μ s) r

/-- Average value of an `ℝ≥0∞`-valued function `f` w.r.t. the standard measure on a set `s`.

It is equal to `(volume s)⁻¹ * ∫⁻ x, f x`, so it takes value zero if `s` has infinite measure. If
`s` has measure `1`, then the average of any function is equal to its integral. -/
notation3 (prettyPrint := false)
  "⨍⁻ " (...) " in " s ", " r:60:(scoped f => laverage Measure.restrict volume s f) => r

@[simp]
/-
**MeasureTheory.laverage_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：laverage_zero : ⨍⁻ _x, (0 : Real>=0∞) ∂μ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.laverage.eq_1`：∀ {α : Type u_1} {m0 : MeasurableSpace α} (
μ : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.laverage μ f = ∫
⁻ (x : α), f x ∂(…
· 使用定理 `MeasureTheory.lintegral_zero`：lintegral_zero : ∫⁻ _ : α, 0 ∂μ = 0
-/
theorem laverage_zero : ⨍⁻ _x, (0 : ℝ≥0∞) ∂μ = 0 := by rw [laverage, lintegral_zero]

@[simp]
/-
**MeasureTheory.laverage_zero_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：laverage_zero_measure (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂(0 : Measure α) = 0
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem laverage_zero_measure (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂(0 : Measure α) = 0 := by simp [laverage]
/-
**MeasureTheory.laverage_eq'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：laverage_eq' (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂(μ univ)⁻¹ • 
μ
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem laverage_eq' (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂(μ univ)⁻¹ • μ := rfl
/-
**MeasureTheory.laverage_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：laverage_eq (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂μ = (∫⁻ x, f x ∂μ) / μ univ
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.laverage_eq'`：laverage_eq' (f : α -> Real>=0∞) : ⨍⁻ x, f x
 ∂μ = ∫⁻ x, f x ∂(μ univ)⁻¹ • μ
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
· 使用定理 `ENNReal.div_eq_inv_mul`：∀ {a b : ENNReal}, a / b = b⁻¹ * a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
-/
theorem laverage_eq (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂μ = (∫⁻ x, f x ∂μ) / μ univ := by
  rw [laverage_eq', lintegral_smul_measure, ENNReal.div_eq_inv_mul, smul_eq_mul]
/-
**MeasureTheory.laverage_eq_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：laverage_eq_lintegral [IsProbabilityMeasure μ] (f : α -> Real>=0∞) : ⨍⁻ x,
 f x ∂μ = ∫⁻ x, f x ∂μ
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.laverage.eq_1`：∀ {α : Type u_1} {m0 : MeasurableSpace α} (
μ : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.laverage μ f = ∫
⁻ (x : α), f x ∂(…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem laverage_eq_lintegral [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) :
    ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ := by rw [laverage, measure_univ, inv_one, one_smul]

@[simp]
/-
**MeasureTheory.measure_mul_laverage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_mul_laverage [IsFiniteMeasure μ] (f : α -> Real>=0∞) : μ univ * ⨍⁻
 x, f x ∂μ = ∫⁻ x, f x ∂μ
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `MeasureTheory.laverage_zero_measure`：laverage_zero_measure (f : α -> Rea
l>=0∞) : ⨍⁻ x, f x ∂(0 : Measure α) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MeasureTheory.laverage_eq`：laverage_eq (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂
μ = (∫⁻ x, f x ∂μ) / μ univ
· 使用定理 `ENNReal.mul_div_cancel`：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * (b / a) =
 b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.measure_univ_ne_zero`：measure_univ_ne_zero : μ uni
v != 0 ↔ μ != 0
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem measure_mul_laverage [IsFiniteMeasure μ] (f : α → ℝ≥0∞) :
    μ univ * ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ := by
  rcases eq_or_ne μ 0 with hμ | hμ
  · rw [hμ, lintegral_zero_measure, laverage_zero_measure, mul_zero]
  · rw [laverage_eq, ENNReal.mul_div_cancel (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)]
/-
**MeasureTheory.setLAverage_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLAverage_eq (f : α -> Real>=0∞) (s : Set α) : ⨍⁻ x in s, f x ∂μ = (∫⁻ x
 in s, f x ∂μ) / μ s
参数：f : α -> Real>=0∞；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.laverage_eq`：laverage_eq (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂
μ = (∫⁻ x, f x ∂μ) / μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply_univ`：restrict_apply_univ (s : Set 
α) : μ.restrict s univ = μ s
-/
theorem setLAverage_eq (f : α → ℝ≥0∞) (s : Set α) :
    ⨍⁻ x in s, f x ∂μ = (∫⁻ x in s, f x ∂μ) / μ s := by rw [laverage_eq, restrict_apply_univ]
/-
**MeasureTheory.setLAverage_eq'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLAverage_eq' (f : α -> Real>=0∞) (s : Set α) : ⨍⁻ x in s, f x ∂μ = ∫⁻ x
, f x ∂(μ s)⁻¹ • μ.restrict s
参数：f : α -> Real>=0∞；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply_univ`：restrict_apply_univ (s : Set 
α) : μ.restrict s univ = μ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setLAverage_eq' (f : α → ℝ≥0∞) (s : Set α) :
    ⨍⁻ x in s, f x ∂μ = ∫⁻ x, f x ∂(μ s)⁻¹ • μ.restrict s := by
  simp only [laverage_eq', restrict_apply_univ]

variable {μ}
/-
**MeasureTheory.laverage_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：laverage_congr {f g : α -> Real>=0∞} (h : f =ᵐ[μ] g) : ⨍⁻ x, f x ∂μ = ⨍⁻ x
, g x ∂μ
参数：h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.laverage_eq`：laverage_eq (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂
μ = (∫⁻ x, f x ∂μ) / μ univ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem laverage_congr {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) : ⨍⁻ x, f x ∂μ = ⨍⁻ x, g x ∂μ := by
  simp only [laverage_eq, lintegral_congr_ae h]
/-
**MeasureTheory.setLAverage_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLAverage_congr (h : s =ᵐ[μ] t) : ⨍⁻ x in s, f x ∂μ = ⨍⁻ x in t, f x ∂μ
参数：h : s =ᵐ[μ] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLAverage_eq`：setLAverage_eq (f : α -> Real>=0∞) (s : Se
t α) : ⨍⁻ x in s, f x ∂μ = (∫⁻ x in s, f x ∂μ) / μ s
· 使用定理 `MeasureTheory.setLIntegral_congr`：setLIntegral_congr {f : α -> Real>=0∞}
 {s t : Set α} (h : s =ᵐ[μ] t) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setLAverage_congr (h : s =ᵐ[μ] t) : ⨍⁻ x in s, f x ∂μ = ⨍⁻ x in t, f x ∂μ := by
  simp only [setLAverage_eq, setLIntegral_congr h, measure_congr h]
/-
**MeasureTheory.setLAverage_congr_fun_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：setLAverage_congr_fun_ae (hs : MeasurableSet s) (h : forallᵐ x ∂μ, x in s 
-> f x = g x) : ⨍⁻ x in s, f x ∂μ = ⨍⁻ x in s, g x ∂μ
参数：hs : MeasurableSet s；h : forallᵐ x ∂μ, x in s -> f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.laverage_eq`：laverage_eq (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂
μ = (∫⁻ x, f x ∂μ) / μ univ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.setLIntegral_congr_fun_ae`：setLIntegral_congr_fun_ae {f g 
: α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : forallᵐ x ∂μ, x in s 
-> f x = g x) : ∫⁻ x in s, f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setLAverage_congr_fun_ae (hs : MeasurableSet s) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
    ⨍⁻ x in s, f x ∂μ = ⨍⁻ x in s, g x ∂μ := by
  simp only [laverage_eq, setLIntegral_congr_fun_ae hs h]
/-
**MeasureTheory.setLAverage_congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLAverage_congr_fun (hs : MeasurableSet s) (h : EqOn f g s) : ⨍⁻ x in s,
 f x ∂μ = ⨍⁻ x in s, g x ∂μ
参数：hs : MeasurableSet s；h : EqOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.laverage_eq`：laverage_eq (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂
μ = (∫⁻ x, f x ∂μ) / μ univ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setLAverage_congr_fun (hs : MeasurableSet s) (h : EqOn f g s) :
    ⨍⁻ x in s, f x ∂μ = ⨍⁻ x in s, g x ∂μ := by
  simp only [laverage_eq, setLIntegral_congr_fun hs h]
/-
**MeasureTheory.laverage_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：laverage_lt_top (hf : ∫⁻ x, f x ∂μ != ∞) : ⨍⁻ x, f x ∂μ < ∞
参数：hf : ∫⁻ x, f x ∂μ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.laverage_zero_measure`：laverage_zero_measure (f : α -> Rea
l>=0∞) : ⨍⁻ x, f x ∂(0 : Measure α) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.laverage_eq`：laverage_eq (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂
μ = (∫⁻ x, f x ∂μ) / μ univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.measure_univ_ne_zero`：measure_univ_ne_zero : μ uni
v != 0 ↔ μ != 0
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENNReal.div_ne_top`：div_ne_top {x y : Real>=0∞} (h1 : x != ∞) (h2 : y !=
 0) : x / y != ∞
-/
theorem laverage_lt_top (hf : ∫⁻ x, f x ∂μ ≠ ∞) : ⨍⁻ x, f x ∂μ < ∞ := by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [laverage_eq]
    finiteness [measure_univ_ne_zero.2 hμ]
/-
**MeasureTheory.setLAverage_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLAverage_lt_top : ∫⁻ x in s, f x ∂μ != ∞ -> ⨍⁻ x in s, f x ∂μ < ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.laverage_lt_top`：laverage_lt_top (hf : ∫⁻ x, f x ∂μ != ∞) 
: ⨍⁻ x, f x ∂μ < ∞
-/
theorem setLAverage_lt_top : ∫⁻ x in s, f x ∂μ ≠ ∞ → ⨍⁻ x in s, f x ∂μ < ∞ :=
  laverage_lt_top
/-
**MeasureTheory.laverage_add_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：laverage_add_measure : ⨍⁻ x, f x ∂(μ + ν) = μ univ / (μ univ + ν univ) * ⨍
⁻ x, f x ∂μ + ν univ / (μ univ + ν univ) * ⨍⁻ x, f x ∂ν
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
· 使用定理 `MeasureTheory.measure_mul_laverage`：measure_mul_laverage [IsFiniteMeasur
e μ] (f : α -> Real>=0∞) : μ univ * ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.laverage_eq`：laverage_eq (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂
μ = (∫⁻ x, f x ∂μ) / μ univ
· 使用定理 `MeasureTheory.lintegral_add_measure`：lintegral_add_measure (f : α -> Rea
l>=0∞) (μ ν : Measure α) : ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν
· 使用引理 `MeasureTheory.not_isFiniteMeasure_iff`：not_isFiniteMeasure_iff : ¬IsFini
teMeasure μ ↔ μ univ = ∞
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `ENNReal.div_top`：∀ {a : ENNReal}, a / ⊤ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
-/
theorem laverage_add_measure :
    ⨍⁻ x, f x ∂(μ + ν) =
      μ univ / (μ univ + ν univ) * ⨍⁻ x, f x ∂μ + ν univ / (μ univ + ν univ) * ⨍⁻ x, f x ∂ν := by
  by_cases hμ : IsFiniteMeasure μ; swap
  · rw [not_isFiniteMeasure_iff] at hμ
    simp [laverage_eq, hμ]
  by_cases hν : IsFiniteMeasure ν; swap
  · rw [not_isFiniteMeasure_iff] at hν
    simp [laverage_eq, hν]
  simp only [← ENNReal.mul_div_right_comm, measure_mul_laverage, ← ENNReal.add_div,
    ← lintegral_add_measure, ← Measure.add_apply, ← laverage_eq]
/-
**MeasureTheory.measure_mul_setLAverage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measure_mul_setLAverage (f : α -> Real>=0∞) (h : μ s != ∞) : μ s * ⨍⁻ x in
 s, f x ∂μ = ∫⁻ x in s, f x ∂μ
参数：f : α -> Real>=0∞；h : μ s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_mul_laverage`：measure_mul_laverage [IsFiniteMeasur
e μ] (f : α -> Real>=0∞) : μ univ * ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
· 使用定理 `MeasureTheory.Measure.restrict_apply_univ`：restrict_apply_univ (s : Set 
α) : μ.restrict s univ = μ s
-/
theorem measure_mul_setLAverage (f : α → ℝ≥0∞) (h : μ s ≠ ∞) :
    μ s * ⨍⁻ x in s, f x ∂μ = ∫⁻ x in s, f x ∂μ := by
  have := Fact.mk h.lt_top
  rw [← measure_mul_laverage, restrict_apply_univ]
/-
**MeasureTheory.laverage_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：laverage_union (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ) : ⨍⁻ x
 in s union t, f x ∂μ = μ s / (μ s + μ t) * ⨍⁻ x in s, f x ∂μ + μ t / (μ s + μ t
) * ⨍⁻ x in t, f x ∂μ
参数：hd : AEDisjoint μ s t；ht : NullMeasurableSet t μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_union₀`：restrict_union₀ (h : AEDisjoint μ
 s t) (ht : NullMeasurableSet t μ) : μ.restrict (s union t) = μ.restrict s + μ.r
estrict t
· 使用定理 `MeasureTheory.laverage_add_measure`：laverage_add_measure : ⨍⁻ x, f x ∂(μ
 + ν) = μ univ / (μ univ + ν univ) * ⨍⁻ x, f x ∂μ + ν univ / (μ univ + ν univ) *
 ⨍⁻ x, f x ∂ν
· 使用定理 `MeasureTheory.Measure.restrict_apply_univ`：restrict_apply_univ (s : Set 
α) : μ.restrict s univ = μ s
-/
theorem laverage_union (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ) :
    ⨍⁻ x in s ∪ t, f x ∂μ =
      μ s / (μ s + μ t) * ⨍⁻ x in s, f x ∂μ + μ t / (μ s + μ t) * ⨍⁻ x in t, f x ∂μ := by
  rw [restrict_union₀ hd ht, laverage_add_measure, restrict_apply_univ, restrict_apply_univ]
/-
**MeasureTheory.laverage_union_mem_openSegment** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：laverage_union_mem_openSegment (hd : AEDisjoint μ s t) (ht : NullMeasurabl
eSet t μ) (hs₀ : μ s != 0) (ht₀ : μ t != 0) (hsμ : μ s != ∞) (htμ : μ t != ∞) : 
⨍⁻ x in s union t, f x ∂μ in openSegment Real>=0∞ (⨍⁻ x in s, f x ∂μ) (⨍⁻ x in t
, f x ∂μ)
参数：hd : AEDisjoint μ s t；ht : NullMeasurableSet t μ；hs₀ : μ s != 0；ht₀ : μ t != 
0；hsμ : μ s != ∞；htμ : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.div_pos`：∀ {a b : ENNReal}, a ≠ 0 → b ≠ ⊤ → 0 < a / b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_ne_top`：add_ne_top : a + b != ∞ ↔ a != ∞ ∧ b != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.add_div`：∀ {a b c : ENNReal}, (a + b) / c = a / c + b / c
· 使用定理 `ENNReal.div_self`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a / a = 1
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `add_eq_zero`：∀ {α : Type u} [inst : AddCommMonoid α] [Subsingleton (AddU
nits α)] {a b : α}, a + b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.laverage_union`：laverage_union (hd : AEDisjoint μ s t) (ht
 : NullMeasurableSet t μ) : ⨍⁻ x in s union t, f x ∂μ = μ s / (μ s + μ t) * ⨍⁻ x
 in s, f x ∂μ + μ …
-/
theorem laverage_union_mem_openSegment (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hs₀ : μ s ≠ 0) (ht₀ : μ t ≠ 0) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) :
    ⨍⁻ x in s ∪ t, f x ∂μ ∈ openSegment ℝ≥0∞ (⨍⁻ x in s, f x ∂μ) (⨍⁻ x in t, f x ∂μ) := by
  refine
    ⟨μ s / (μ s + μ t), μ t / (μ s + μ t), ENNReal.div_pos hs₀ <| add_ne_top.2 ⟨hsμ, htμ⟩,
      ENNReal.div_pos ht₀ <| add_ne_top.2 ⟨hsμ, htμ⟩, ?_, (laverage_union hd ht).symm⟩
  rw [← ENNReal.add_div,
    ENNReal.div_self (add_eq_zero.not.2 fun h => hs₀ h.1) (add_ne_top.2 ⟨hsμ, htμ⟩)]

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.laverage_union_mem_segment** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：laverage_union_mem_segment (hd : AEDisjoint μ s t) (ht : NullMeasurableSet
 t μ) (hsμ : μ s != ∞) (htμ : μ t != ∞) : ⨍⁻ x in s union t, f x ∂μ in [⨍⁻ x in 
s, f x ∂μ -[Real>=0∞] ⨍⁻ x in t, f x ∂μ]
参数：hd : AEDisjoint μ s t；ht : NullMeasurableSet t μ；hsμ : μ s != ∞；htμ : μ t != 
∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `Filter.EventuallyEq.union`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∪ s' =ᶠ[l] t ∪ t'
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_eq_empty`：ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `right_mem_segment`：right_mem_segment (x y : E) : y in [x -[𝕜] y]
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.add_div`：∀ {a b c : ENNReal}, (a + b) / c = a / c + b / c
· 使用定理 `ENNReal.div_self`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a / a = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `add_eq_zero`：∀ {α : Type u} [inst : AddCommMonoid α] [Subsingleton (AddU
nits α)] {a b : α}, a + b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ENNReal.add_ne_top`：add_ne_top : a + b != ∞ ↔ a != ∞ ∧ b != ∞
· 使用定理 `MeasureTheory.laverage_union`：laverage_union (hd : AEDisjoint μ s t) (ht
 : NullMeasurableSet t μ) : ⨍⁻ x in s union t, f x ∂μ = μ s / (μ s + μ t) * ⨍⁻ x
 in s, f x ∂μ + μ …
-/
theorem laverage_union_mem_segment (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) :
    ⨍⁻ x in s ∪ t, f x ∂μ ∈ [⨍⁻ x in s, f x ∂μ -[ℝ≥0∞] ⨍⁻ x in t, f x ∂μ] := by
  by_cases hs₀ : μ s = 0
  · rw [← ae_eq_empty] at hs₀
    rw [restrict_congr_set (hs₀.union EventuallyEq.rfl), empty_union]
    exact right_mem_segment _ _ _
  · refine
      ⟨μ s / (μ s + μ t), μ t / (μ s + μ t), zero_le, zero_le, ?_, (laverage_union hd ht).symm⟩
    rw [← ENNReal.add_div,
      ENNReal.div_self (add_eq_zero.not.2 fun h => hs₀ h.1) (add_ne_top.2 ⟨hsμ, htμ⟩)]
/-
**MeasureTheory.laverage_mem_openSegment_compl_self** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：laverage_mem_openSegment_compl_self [IsFiniteMeasure μ] (hs : NullMeasurab
leSet s μ) (hs₀ : μ s != 0) (hsc₀ : μ sᶜ != 0) : ⨍⁻ x, f x ∂μ in openSegment Rea
l>=0∞ (⨍⁻ x in s, f x ∂μ) (⨍⁻ x in sᶜ, f x ∂μ)
参数：hs : NullMeasurableSet s μ；hs₀ : μ s != 0；hsc₀ : μ sᶜ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `MeasureTheory.laverage_union_mem_openSegment`：laverage_union_mem_openSeg
ment (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ) (hs₀ : μ s != 0) (ht₀ 
: μ t != 0) (hsμ : μ s != ∞) (htμ …
· 使用定理 `MeasureTheory.aedisjoint_compl_right`：aedisjoint_compl_right : AEDisjoin
t μ s sᶜ
· 使用定理 `MeasureTheory.NullMeasurableSet.compl`：compl (h : NullMeasurableSet s μ)
 : NullMeasurableSet sᶜ μ
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem laverage_mem_openSegment_compl_self [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ)
    (hs₀ : μ s ≠ 0) (hsc₀ : μ sᶜ ≠ 0) :
    ⨍⁻ x, f x ∂μ ∈ openSegment ℝ≥0∞ (⨍⁻ x in s, f x ∂μ) (⨍⁻ x in sᶜ, f x ∂μ) := by
  simpa only [union_compl_self, restrict_univ] using
    laverage_union_mem_openSegment aedisjoint_compl_right hs.compl hs₀ hsc₀ (measure_ne_top _ _)
      (measure_ne_top _ _)

@[simp]
/-
**MeasureTheory.laverage_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：laverage_const (μ : Measure α) [IsFiniteMeasure μ] [h : NeZero μ] (c : Rea
l>=0∞) : ⨍⁻ _x, c ∂μ = c
参数：μ : Measure α；c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem laverage_const (μ : Measure α) [IsFiniteMeasure μ] [h : NeZero μ] (c : ℝ≥0∞) :
    ⨍⁻ _x, c ∂μ = c := by
  simp only [laverage, lintegral_const, measure_univ, mul_one]
/-
**MeasureTheory.setLAverage_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLAverage_const (hs₀ : μ s != 0) (hs : μ s != ∞) (c : Real>=0∞) : ⨍⁻ _x 
in s, c ∂μ = c
参数：hs₀ : μ s != 0；hs : μ s != ∞；c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLAverage_eq`：setLAverage_eq (f : α -> Real>=0∞) (s : Se
t α) : ⨍⁻ x in s, f x ∂μ = (∫⁻ x in s, f x ∂μ) / μ s
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setLAverage_const (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (c : ℝ≥0∞) : ⨍⁻ _x in s, c ∂μ = c := by
  simp only [setLAverage_eq, lintegral_const, Measure.restrict_apply, MeasurableSet.univ,
    univ_inter, div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hs₀ hs, mul_one]
/-
**MeasureTheory.laverage_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：laverage_one [IsFiniteMeasure μ] [NeZero μ] : ⨍⁻ _x, (1 : Real>=0∞) ∂μ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.laverage_const`：laverage_const (μ : Measure α) [IsFiniteMe
asure μ] [h : NeZero μ] (c : Real>=0∞) : ⨍⁻ _x, c ∂μ = c
-/
theorem laverage_one [IsFiniteMeasure μ] [NeZero μ] : ⨍⁻ _x, (1 : ℝ≥0∞) ∂μ = 1 :=
  laverage_const _ _
/-
**MeasureTheory.setLAverage_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLAverage_one (hs₀ : μ s != 0) (hs : μ s != ∞) : ⨍⁻ _x in s, (1 : Real>=
0∞) ∂μ = 1
参数：hs₀ : μ s != 0；hs : μ s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setLAverage_const`：setLAverage_const (hs₀ : μ s != 0) (hs 
: μ s != ∞) (c : Real>=0∞) : ⨍⁻ _x in s, c ∂μ = c
-/
theorem setLAverage_one (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) : ⨍⁻ _x in s, (1 : ℝ≥0∞) ∂μ = 1 :=
  setLAverage_const hs₀ hs _

@[simp]
/-
**MeasureTheory.laverage_mul_measure_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：laverage_mul_measure_univ (μ : Measure α) [IsFiniteMeasure μ] (f : α -> Re
al>=0∞) : (⨍⁻ (a : α), f a ∂μ) * μ univ = ∫⁻ x, f x ∂μ
参数：μ : Measure α；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.laverage_zero_measure`：laverage_zero_measure (f : α -> Rea
l>=0∞) : ⨍⁻ x, f x ∂(0 : Measure α) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.laverage_eq`：laverage_eq (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂
μ = (∫⁻ x, f x ∂μ) / μ univ
· 使用定理 `ENNReal.div_mul_cancel`：∀ {a b : ENNReal}, a ≠ 0 → a ≠ ⊤ → b / a * a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.measure_univ_ne_zero`：measure_univ_ne_zero : μ uni
v != 0 ↔ μ != 0
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem laverage_mul_measure_univ (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ≥0∞) :
    (⨍⁻ (a : α), f a ∂μ) * μ univ = ∫⁻ x, f x ∂μ := by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [laverage_eq, ENNReal.div_mul_cancel (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)]
/-
**MeasureTheory.lintegral_laverage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_laverage (μ : Measure α) [IsFiniteMeasure μ] (f : α -> Real>=0∞)
 : ∫⁻ _x, ⨍⁻ a, f a ∂μ ∂μ = ∫⁻ x, f x ∂μ
参数：μ : Measure α；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.laverage_mul_measure_univ`：laverage_mul_measure_univ (μ : 
Measure α) [IsFiniteMeasure μ] (f : α -> Real>=0∞) : (⨍⁻ (a : α), f a ∂μ) * μ un
iv = ∫⁻ x, f x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_laverage (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ≥0∞) :
    ∫⁻ _x, ⨍⁻ a, f a ∂μ ∂μ = ∫⁻ x, f x ∂μ := by
  simp
/-
**MeasureTheory.setLIntegral_setLAverage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：setLIntegral_setLAverage (μ : Measure α) [IsFiniteMeasure μ] (f : α -> Rea
l>=0∞) (s : Set α) : ∫⁻ _x in s, ⨍⁻ a in s, f a ∂μ ∂μ = ∫⁻ x in s, f x ∂μ
参数：μ : Measure α；f : α -> Real>=0∞；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_laverage`：lintegral_laverage (μ : Measure α) [Is
FiniteMeasure μ] (f : α -> Real>=0∞) : ∫⁻ _x, ⨍⁻ a, f a ∂μ ∂μ = ∫⁻ x, f x ∂μ
-/
theorem setLIntegral_setLAverage (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ≥0∞) (s : Set α) :
    ∫⁻ _x in s, ⨍⁻ a in s, f a ∂μ ∂μ = ∫⁻ x in s, f x ∂μ :=
  lintegral_laverage _ _

@[gcongr]
/-
**MeasureTheory.laverage_mono_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：laverage_mono_ae (h : f <=ᶠ[ae μ] g) : ⨍⁻ a, f a ∂μ <= ⨍⁻ a, g a ∂μ
参数：h : f <=ᶠ[ae μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.ae_mono'`：∀ {α : Type u_1} {mα : MeasurableSpace α
} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν → MeasureTheory.ae
 μ ≤ MeasureTheory.a…
· 使用引理 `MeasureTheory.Measure.smul_absolutelyContinuous`：smul_absolutelyContinuo
us {c : Real>=0∞} : c • μ ≪ μ
-/
theorem laverage_mono_ae (h : f ≤ᶠ[ae μ] g) :
    ⨍⁻ a, f a ∂μ ≤ ⨍⁻ a, g a ∂μ :=
  lintegral_mono_ae <| h.filter_mono <| Measure.ae_mono' Measure.smul_absolutelyContinuous

@[gcongr]
/-
**MeasureTheory.setLAverage_mono_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLAverage_mono_ae (s : Set α) (h : f <=ᶠ[ae μ] g) : ⨍⁻ a in s, f a ∂μ <=
 ⨍⁻ a in s, g a ∂μ
参数：s : Set α；h : f <=ᶠ[ae μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.laverage_mono_ae`：laverage_mono_ae (h : f <=ᶠ[ae μ] g) : ⨍
⁻ a, f a ∂μ <= ⨍⁻ a, g a ∂μ
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
-/
theorem setLAverage_mono_ae (s : Set α) (h : f ≤ᶠ[ae μ] g) :
    ⨍⁻ a in s, f a ∂μ ≤ ⨍⁻ a in s, g a ∂μ :=
  laverage_mono_ae <| h.filter_mono <| ae_mono Measure.restrict_le_self
/-
**MeasureTheory.setLAverage_le_essSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLAverage_le_essSup (s : Set α) (f : α -> Real>=0∞) : ⨍⁻ x in s, f x ∂μ 
<= essSup f μ
参数：s : Set α；f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.laverage.eq_1`：∀ {α : Type u_1} {m0 : MeasurableSpace α} (
μ : MeasureTheory.Measure α) (f : α → ENNReal),   MeasureTheory.laverage μ f = ∫
⁻ (x : α), f x ∂(…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `MeasureTheory.setLIntegral_measure_zero`：setLIntegral_measure_zero (s : 
Set α) (f : α -> Real>=0∞) (hs' : μ s = 0) : ∫⁻ x in s, f x ∂μ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.laverage_mono_ae`：laverage_mono_ae (h : f <=ᶠ[ae μ] g) : ⨍
⁻ a, f a ∂μ <= ⨍⁻ a, g a ∂μ
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.ae_restrict_le`：ae_restrict_le : ae (μ.restrict s) <= ae μ
· 使用定理 `ae_le_essSup`：ae_le_essSup (hf : IsBoundedUnder (· <= ·) (ae μ) f
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `MeasureTheory.Measure.restrict.neZero`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s : Set α} [NeZero (μ s)],   NeZero (μ.r
estrict s)
· 使用定理 `MeasureTheory.laverage_const`：laverage_const (μ : Measure α) [IsFiniteMe
asure μ] [h : NeZero μ] (c : Real>=0∞) : ⨍⁻ _x, c ∂μ = c
（共 36 条，此处仅展示前 30 条）
-/
theorem setLAverage_le_essSup (s : Set α) (f : α → ℝ≥0∞) : ⨍⁻ x in s, f x ∂μ ≤ essSup f μ := by
  by_cases hμ : IsFiniteMeasure (μ.restrict s); swap
  · simp [laverage, not_isFiniteMeasure_iff.mp hμ]
  by_cases hμ0 : μ s = 0
  · rw [laverage, ← setLIntegral_univ]
    exact le_of_eq_of_le (setLIntegral_measure_zero univ f <| by simp [hμ0]) zero_le
  apply le_of_le_of_eq (laverage_mono_ae <| Eventually.filter_mono ae_restrict_le ae_le_essSup)
  have : NeZero (μ.restrict s) :=
    have : NeZero (μ s) := { out := hμ0 }
    restrict.neZero
  exact laverage_const (μ.restrict s) _
/-
**MeasureTheory.laverage_le_essSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：laverage_le_essSup (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂μ <= essSup f μ
参数：f : α -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `MeasureTheory.setLAverage_le_essSup`：setLAverage_le_essSup (s : Set α) (
f : α -> Real>=0∞) : ⨍⁻ x in s, f x ∂μ <= essSup f μ
-/
theorem laverage_le_essSup (f : α → ℝ≥0∞) : ⨍⁻ x, f x ∂μ ≤ essSup f μ := by
  simpa using setLAverage_le_essSup univ f

end ENNReal

section NormedAddCommGroup

variable (μ)
variable {f g : α → E}

/-- Average value of a function `f` w.r.t. a measure `μ`, denoted `⨍ x, f x ∂μ`.

It is equal to `(μ.real univ)⁻¹ • ∫ x, f x ∂μ`, so it takes value zero if `f` is not integrable or
if `μ` is an infinite measure. If `μ` is a probability measure, then the average of any function is
equal to its integral.

For the average on a set, use `⨍ x in s, f x ∂μ`, defined as `⨍ x, f x ∂(μ.restrict s)`. For the
average w.r.t. the volume, one can omit `∂volume`. -/
/-
**MeasureTheory.average** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：average (f : α -> E)
参数：f : α -> E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Average value of a function `f` w.r.t. a measure `μ`, denoted `⨍ x, f x ∂μ`.

It is equal to `(μ.real univ)⁻¹ • ∫ x, f x ∂μ`, so it takes value zero if `f` is
 not integrable or
if `μ` is an infinite measure. If `μ` is a probability measure, then the average
 of any function is
equal to its integral.

For the average on a set, use `⨍ x in s, f x ∂μ`, defined as `⨍ x, f x ∂(μ.restr
ict s)`. For the
average w.r.t. the volume, one can omit `∂volume`.
-/
noncomputable def average (f : α → E) :=
  ∫ x, f x ∂(μ univ)⁻¹ • μ

/-- Average value of a function `f` w.r.t. a measure `μ`.

It is equal to `(μ.real univ)⁻¹ • ∫ x, f x ∂μ`, so it takes value zero if `f` is not integrable or
if `μ` is an infinite measure. If `μ` is a probability measure, then the average of any function is
equal to its integral.

For the average on a set, use `⨍ x in s, f x ∂μ`, defined as `⨍ x, f x ∂(μ.restrict s)`. For the
average w.r.t. the volume, one can omit `∂volume`. -/
notation3 "⨍ " (...) ", " r:60:(scoped f => f) " ∂" μ:70 => average μ r

/-- Average value of a function `f` w.r.t. the standard measure.

It is equal to `(volume.real univ)⁻¹ * ∫ x, f x`, so it takes value zero if `f` is not integrable
or if the space has infinite measure. In a probability space, the average of any function is equal
to its integral.

For the average on a set, use `⨍ x in s, f x`, defined as `⨍ x, f x ∂(volume.restrict s)`. -/
notation3 "⨍ " (...) ", " r:60:(scoped f => average volume f) => r

/-- Average value of a function `f` w.r.t. a measure `μ` on a set `s`.

It is equal to `(μ.real s)⁻¹ * ∫ x, f x ∂μ`, so it takes value zero if `f` is not integrable on
`s` or if `s` has infinite measure. If `s` has measure `1`, then the average of any function is
equal to its integral.

For the average w.r.t. the volume, one can omit `∂volume`. -/
notation3 "⨍ " (...) " in " s ", " r:60:(scoped f => f) " ∂" μ:70 =>
  average (Measure.restrict μ s) r

/-- Average value of a function `f` w.r.t. the standard measure on a set `s`.

It is equal to `(volume.real s)⁻¹ * ∫ x, f x`, so it takes value zero `f` is not integrable on `s`
or if `s` has infinite measure. If `s` has measure `1`, then the average of any function is equal to
its integral. -/
notation3 "⨍ " (...) " in " s ", " r:60:(scoped f => average (Measure.restrict volume s) f) => r

@[simp]
/-
**MeasureTheory.average_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：average_zero : ⨍ _, (0 : E) ∂μ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.average.eq_1`：∀ {α : Type u_1} {E : Type u_2} {m0 : Measur
ableSpace α} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   (μ : Mea
sureTheory.Measu…
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
-/
theorem average_zero : ⨍ _, (0 : E) ∂μ = 0 := by rw [average, integral_zero]

@[simp]
/-
**MeasureTheory.average_zero_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：average_zero_measure (f : α -> E) : ⨍ x, f x ∂(0 : Measure α) = 0
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.average.eq_1`：∀ {α : Type u_1} {E : Type u_2} {m0 : Measur
ableSpace α} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   (μ : Mea
sureTheory.Measu…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
-/
theorem average_zero_measure (f : α → E) : ⨍ x, f x ∂(0 : Measure α) = 0 := by
  rw [average, smul_zero, integral_zero_measure]

@[simp]
/-
**MeasureTheory.average_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：average_neg (f : α -> E) : ⨍ x, -f x ∂μ = -⨍ x, f x ∂μ
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
-/
theorem average_neg (f : α → E) : ⨍ x, -f x ∂μ = -⨍ x, f x ∂μ :=
  integral_neg f
/-
**MeasureTheory.average_eq'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：average_eq' (f : α -> E) : ⨍ x, f x ∂μ = ∫ x, f x ∂(μ univ)⁻¹ • μ
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem average_eq' (f : α → E) : ⨍ x, f x ∂μ = ∫ x, f x ∂(μ univ)⁻¹ • μ :=
  rfl
/-
**MeasureTheory.average_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：average_eq (f : α -> E) : ⨍ x, f x ∂μ = (μ.real univ)⁻¹ • ∫ x, f x ∂μ
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.average_eq'`：average_eq' (f : α -> E) : ⨍ x, f x ∂μ = ∫ x,
 f x ∂(μ univ)⁻¹ • μ
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
-/
theorem average_eq (f : α → E) : ⨍ x, f x ∂μ = (μ.real univ)⁻¹ • ∫ x, f x ∂μ := by
  rw [average_eq', integral_smul_measure, ENNReal.toReal_inv, measureReal_def]
/-
**MeasureTheory.average_eq_integral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：average_eq_integral [IsProbabilityMeasure μ] (f : α -> E) : ⨍ x, f x ∂μ = 
∫ x, f x ∂μ
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.average.eq_1`：∀ {α : Type u_1} {E : Type u_2} {m0 : Measur
ableSpace α} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   (μ : Mea
sureTheory.Measu…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem average_eq_integral [IsProbabilityMeasure μ] (f : α → E) : ⨍ x, f x ∂μ = ∫ x, f x ∂μ := by
  rw [average, measure_univ, inv_one, one_smul]

@[simp]
/-
**MeasureTheory.measure_smul_average** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_smul_average [IsFiniteMeasure μ] (f : α -> E) : μ.real univ • ⨍ x,
 f x ∂μ = ∫ x, f x ∂μ
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `MeasureTheory.average_zero_measure`：average_zero_measure (f : α -> E) : 
⨍ x, f x ∂(0 : Measure α) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MeasureTheory.average_eq`：average_eq (f : α -> E) : ⨍ x, f x ∂μ = (μ.rea
l univ)⁻¹ • ∫ x, f x ∂μ
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem measure_smul_average [IsFiniteMeasure μ] (f : α → E) :
    μ.real univ • ⨍ x, f x ∂μ = ∫ x, f x ∂μ := by
  rcases eq_or_ne μ 0 with hμ | hμ
  · rw [hμ, integral_zero_measure, average_zero_measure, smul_zero]
  · rw [average_eq, smul_inv_smul₀]
    refine (ENNReal.toReal_pos ?_ <| measure_ne_top _ _).ne'
    rwa [Ne, measure_univ_eq_zero]
/-
**MeasureTheory.setAverage_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setAverage_eq (f : α -> E) (s : Set α) : ⨍ x in s, f x ∂μ = (μ.real s)⁻¹ •
 ∫ x in s, f x ∂μ
参数：f : α -> E；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.average_eq`：average_eq (f : α -> E) : ⨍ x, f x ∂μ = (μ.rea
l univ)⁻¹ • ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.measureReal_restrict_apply_univ`：measureReal_restrict_appl
y_univ (s : Set α) : (μ.restrict s).real univ = μ.real s
-/
theorem setAverage_eq (f : α → E) (s : Set α) :
    ⨍ x in s, f x ∂μ = (μ.real s)⁻¹ • ∫ x in s, f x ∂μ := by
  rw [average_eq, measureReal_restrict_apply_univ]
/-
**MeasureTheory.setAverage_eq'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setAverage_eq' (f : α -> E) (s : Set α) : ⨍ x in s, f x ∂μ = ∫ x, f x ∂(μ 
s)⁻¹ • μ.restrict s
参数：f : α -> E；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply_univ`：restrict_apply_univ (s : Set 
α) : μ.restrict s univ = μ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setAverage_eq' (f : α → E) (s : Set α) :
    ⨍ x in s, f x ∂μ = ∫ x, f x ∂(μ s)⁻¹ • μ.restrict s := by
  simp only [average_eq', restrict_apply_univ]

variable {μ}
/-
**MeasureTheory.average_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：average_congr {f g : α -> E} (h : f =ᵐ[μ] g) : ⨍ x, f x ∂μ = ⨍ x, g x ∂μ
参数：h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.average_eq`：average_eq (f : α -> E) : ⨍ x, f x ∂μ = (μ.rea
l univ)⁻¹ • ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem average_congr {f g : α → E} (h : f =ᵐ[μ] g) : ⨍ x, f x ∂μ = ⨍ x, g x ∂μ := by
  simp only [average_eq, integral_congr_ae h]
/-
**MeasureTheory.setAverage_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setAverage_congr (h : s =ᵐ[μ] t) : ⨍ x in s, f x ∂μ = ⨍ x in t, f x ∂μ
参数：h : s =ᵐ[μ] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setAverage_eq`：setAverage_eq (f : α -> E) (s : Set α) : ⨍ 
x in s, f x ∂μ = (μ.real s)⁻¹ • ∫ x in s, f x ∂μ
· 使用定理 `MeasureTheory.measureReal_congr`：measureReal_congr (H : s =ᵐ[μ] t) : μ.r
eal s = μ.real t
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setAverage_congr (h : s =ᵐ[μ] t) : ⨍ x in s, f x ∂μ = ⨍ x in t, f x ∂μ := by
  simp only [setAverage_eq, setIntegral_congr_set h, measureReal_congr h]
/-
**MeasureTheory.setAverage_congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setAverage_congr_fun (hs : MeasurableSet s) (h : forallᵐ x ∂μ, x in s -> f
 x = g x) : ⨍ x in s, f x ∂μ = ⨍ x in s, g x ∂μ
参数：hs : MeasurableSet s；h : forallᵐ x ∂μ, x in s -> f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.average_eq`：average_eq (f : α -> E) : ⨍ x, f x ∂μ = (μ.rea
l univ)⁻¹ • ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setAverage_congr_fun (hs : MeasurableSet s) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
    ⨍ x in s, f x ∂μ = ⨍ x in s, g x ∂μ := by simp only [average_eq, setIntegral_congr_ae hs h]
/-
**MeasureTheory.average_add_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：average_add_measure [IsFiniteMeasure μ] {ν : Measure α} [IsFiniteMeasure ν
] {f : α -> E} (hμ : Integrable f μ) (hν : Integrable f ν) : ⨍ x, f x ∂(μ + ν) =
 (μ.real univ / (μ.real univ + ν.real univ)) • ⨍ x, f x ∂μ + (ν.real univ / (μ.r
eal univ + ν.real univ)) • ⨍ x, f x ∂ν
参数：hμ : Integrable f μ；hν : Integrable f ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `MeasureTheory.measure_smul_average`：measure_smul_average [IsFiniteMeasur
e μ] (f : α -> E) : μ.real univ • ⨍ x, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_add_measure`：integral_add_measure {f : α -> G} (h
μ : Integrable f μ) (hν : Integrable f ν) : ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ 
x, f x ∂ν
· 使用定理 `MeasureTheory.average_eq`：average_eq (f : α -> E) : ⨍ x, f x ∂μ = (μ.rea
l univ)⁻¹ • ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.measureReal_add_apply`：measureReal_add_apply {μ₁ μ₂ : Meas
ure α} (h₁ : μ₁ s != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem average_add_measure [IsFiniteMeasure μ] {ν : Measure α} [IsFiniteMeasure ν] {f : α → E}
    (hμ : Integrable f μ) (hν : Integrable f ν) :
    ⨍ x, f x ∂(μ + ν) =
      (μ.real univ / (μ.real univ + ν.real univ)) • ⨍ x, f x ∂μ +
        (ν.real univ / (μ.real univ + ν.real univ)) • ⨍ x, f x ∂ν := by
  simp only [div_eq_inv_mul, mul_smul, measure_smul_average, ← smul_add,
    ← integral_add_measure hμ hν]
  rw [average_eq, measureReal_add_apply]
/-
**MeasureTheory.average_pair** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：average_pair [CompleteSpace E] {f : α -> E} {g : α -> F} (hfi : Integrable
 f μ) (hgi : Integrable g μ) : ⨍ x, (f x, g x) ∂μ = (⨍ x, f x ∂μ, ⨍ x, g x ∂μ)
参数：hfi : Integrable f μ；hgi : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `integral_pair`：integral_pair [CompleteSpace E] [CompleteSpace F] {f : X 
-> E} {g : X -> F} (hf : Integrable f μ) (hg : Integrable g μ) : ∫ x, (f x, g x)
 ∂μ…
· 使用定理 `MeasureTheory.Integrable.to_average`：∀ {α : Type u_1} {m : MeasurableSpa
ce α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]  
 [inst_1 : ESeminormedAdd…
-/
theorem average_pair [CompleteSpace E]
    {f : α → E} {g : α → F} (hfi : Integrable f μ) (hgi : Integrable g μ) :
    ⨍ x, (f x, g x) ∂μ = (⨍ x, f x ∂μ, ⨍ x, g x ∂μ) :=
  integral_pair hfi.to_average hgi.to_average
/-
**MeasureTheory.measure_smul_setAverage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measure_smul_setAverage (f : α -> E) {s : Set α} (h : μ s != ∞) : μ.real s
 • ⨍ x in s, f x ∂μ = ∫ x in s, f x ∂μ
参数：f : α -> E；h : μ s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_smul_average`：measure_smul_average [IsFiniteMeasur
e μ] (f : α -> E) : μ.real univ • ⨍ x, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
· 使用定理 `MeasureTheory.measureReal_restrict_apply_univ`：measureReal_restrict_appl
y_univ (s : Set α) : (μ.restrict s).real univ = μ.real s
-/
theorem measure_smul_setAverage (f : α → E) {s : Set α} (h : μ s ≠ ∞) :
    μ.real s • ⨍ x in s, f x ∂μ = ∫ x in s, f x ∂μ := by
  have := Fact.mk h.lt_top
  rw [← measure_smul_average, measureReal_restrict_apply_univ]
/-
**MeasureTheory.average_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：average_union {f : α -> E} {s t : Set α} (hd : AEDisjoint μ s t) (ht : Nul
lMeasurableSet t μ) (hsμ : μ s != ∞) (htμ : μ t != ∞) (hfs : IntegrableOn f s μ)
 (hft : IntegrableOn f t μ) : ⨍ x in s union t, f x ∂μ = (μ.real s / (μ.real s +
 μ.real t)) • ⨍ x in s, f x ∂μ + (μ.real t / (μ.real s + μ.real t)) • ⨍ x in t, 
f x ∂μ
参数：hd : AEDisjoint μ s t；ht : NullMeasurableSet t μ；hsμ : μ s != ∞；htμ : μ t != 
∞；hfs : IntegrableOn f s μ；hft : IntegrableOn f t μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_union₀`：restrict_union₀ (h : AEDisjoint μ
 s t) (ht : NullMeasurableSet t μ) : μ.restrict (s union t) = μ.restrict s + μ.r
estrict t
· 使用定理 `MeasureTheory.average_add_measure`：average_add_measure [IsFiniteMeasure 
μ] {ν : Measure α} [IsFiniteMeasure ν] {f : α -> E} (hμ : Integrable f μ) (hν : 
Integrable f ν) : ⨍ x, …
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
· 使用定理 `MeasureTheory.measureReal_restrict_apply_univ`：measureReal_restrict_appl
y_univ (s : Set α) : (μ.restrict s).real univ = μ.real s
-/
theorem average_union {f : α → E} {s t : Set α} (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    ⨍ x in s ∪ t, f x ∂μ =
      (μ.real s / (μ.real s + μ.real t)) • ⨍ x in s, f x ∂μ +
        (μ.real t / (μ.real s + μ.real t)) • ⨍ x in t, f x ∂μ := by
  have := Fact.mk hsμ.lt_top; have := Fact.mk htμ.lt_top
  rw [restrict_union₀ hd ht, average_add_measure hfs hft, measureReal_restrict_apply_univ,
    measureReal_restrict_apply_univ]
/-
**MeasureTheory.average_union_mem_openSegment** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：average_union_mem_openSegment {f : α -> E} {s t : Set α} (hd : AEDisjoint 
μ s t) (ht : NullMeasurableSet t μ) (hs₀ : μ s != 0) (ht₀ : μ t != 0) (hsμ : μ s
 != ∞) (htμ : μ t != ∞) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) : 
⨍ x in s union t, f x ∂μ in openSegment Real (⨍ x in s, f x ∂μ) (⨍ x in t, f x ∂
μ)
参数：hd : AEDisjoint μ s t；ht : NullMeasurableSet t μ；hs₀ : μ s != 0；ht₀ : μ t != 
0；hsμ : μ s != ∞；htμ : μ t != ∞；hfs : IntegrableOn f s μ；hft : IntegrableOn f t 
μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_openSegment_iff_div`：mem_openSegment_iff_div : x in openSegment 𝕜 y 
z ↔ exists a b : 𝕜, 0 < a ∧ 0 < b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.average_union`：average_union {f : α -> E} {s t : Set α} (h
d : AEDisjoint μ s t) (ht : NullMeasurableSet t μ) (hsμ : μ s != ∞) (htμ : μ t !
= ∞) (hfs : Integ…
-/
theorem average_union_mem_openSegment {f : α → E} {s t : Set α} (hd : AEDisjoint μ s t)
    (ht : NullMeasurableSet t μ) (hs₀ : μ s ≠ 0) (ht₀ : μ t ≠ 0) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞)
    (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    ⨍ x in s ∪ t, f x ∂μ ∈ openSegment ℝ (⨍ x in s, f x ∂μ) (⨍ x in t, f x ∂μ) := by
  replace hs₀ : 0 < μ.real s := ENNReal.toReal_pos hs₀ hsμ
  replace ht₀ : 0 < μ.real t := ENNReal.toReal_pos ht₀ htμ
  exact mem_openSegment_iff_div.mpr
    ⟨μ.real s, μ.real t, hs₀, ht₀, (average_union hd ht hsμ htμ hfs hft).symm⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.average_union_mem_segment** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：average_union_mem_segment {f : α -> E} {s t : Set α} (hd : AEDisjoint μ s 
t) (ht : NullMeasurableSet t μ) (hsμ : μ s != ∞) (htμ : μ t != ∞) (hfs : Integra
bleOn f s μ) (hft : IntegrableOn f t μ) : ⨍ x in s union t, f x ∂μ in [⨍ x in s,
 f x ∂μ -[Real] ⨍ x in t, f x ∂μ]
参数：hd : AEDisjoint μ s t；ht : NullMeasurableSet t μ；hsμ : μ s != ∞；htμ : μ t != 
∞；hfs : IntegrableOn f s μ；hft : IntegrableOn f t μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `Filter.EventuallyEq.union`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∪ s' =ᶠ[l] t ∪ t'
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_eq_empty`：ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `right_mem_segment`：right_mem_segment (x y : E) : y in [x -[𝕜] y]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_segment_iff_div`：mem_segment_iff_div : x in [y -[𝕜] z] ↔ exists a b 
: 𝕜, 0 <= a ∧ 0 <= b ∧ 0 < a + b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.average_union`：average_union {f : α -> E} {s t : Set α} (h
d : AEDisjoint μ s t) (ht : NullMeasurableSet t μ) (hsμ : μ s != ∞) (htμ : μ t !
= ∞) (hfs : Integ…
-/
theorem average_union_mem_segment {f : α → E} {s t : Set α} (hd : AEDisjoint μ s t)
    (ht : NullMeasurableSet t μ) (hsμ : μ s ≠ ∞) (htμ : μ t ≠ ∞) (hfs : IntegrableOn f s μ)
    (hft : IntegrableOn f t μ) :
    ⨍ x in s ∪ t, f x ∂μ ∈ [⨍ x in s, f x ∂μ -[ℝ] ⨍ x in t, f x ∂μ] := by
  by_cases hse : μ s = 0
  · rw [← ae_eq_empty] at hse
    rw [restrict_congr_set (hse.union EventuallyEq.rfl), empty_union]
    exact right_mem_segment _ _ _
  · refine
      mem_segment_iff_div.mpr
        ⟨μ.real s, μ.real t, ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, ?_,
          (average_union hd ht hsμ htμ hfs hft).symm⟩
    calc
      0 < μ.real s := ENNReal.toReal_pos hse hsμ
      _ ≤ _ := le_add_of_nonneg_right ENNReal.toReal_nonneg
/-
**MeasureTheory.average_mem_openSegment_compl_self** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：average_mem_openSegment_compl_self [IsFiniteMeasure μ] {f : α -> E} {s : S
et α} (hs : NullMeasurableSet s μ) (hs₀ : μ s != 0) (hsc₀ : μ sᶜ != 0) (hfi : In
tegrable f μ) : ⨍ x, f x ∂μ in openSegment Real (⨍ x in s, f x ∂μ) (⨍ x in sᶜ, f
 x ∂μ)
参数：hs : NullMeasurableSet s μ；hs₀ : μ s != 0；hsc₀ : μ sᶜ != 0；hfi : Integrable f
 μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `MeasureTheory.average_union_mem_openSegment`：average_union_mem_openSegme
nt {f : α -> E} {s t : Set α} (hd : AEDisjoint μ s t) (ht : NullMeasurableSet t 
μ) (hs₀ : μ s != 0) (ht₀ : μ t !=…
· 使用定理 `MeasureTheory.aedisjoint_compl_right`：aedisjoint_compl_right : AEDisjoin
t μ s sᶜ
· 使用定理 `MeasureTheory.NullMeasurableSet.compl`：compl (h : NullMeasurableSet s μ)
 : NullMeasurableSet sᶜ μ
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
-/
theorem average_mem_openSegment_compl_self [IsFiniteMeasure μ] {f : α → E} {s : Set α}
    (hs : NullMeasurableSet s μ) (hs₀ : μ s ≠ 0) (hsc₀ : μ sᶜ ≠ 0) (hfi : Integrable f μ) :
    ⨍ x, f x ∂μ ∈ openSegment ℝ (⨍ x in s, f x ∂μ) (⨍ x in sᶜ, f x ∂μ) := by
  simpa only [union_compl_self, restrict_univ] using
    average_union_mem_openSegment aedisjoint_compl_right hs.compl hs₀ hsc₀ (measure_ne_top _ _)
      (measure_ne_top _ _) hfi.integrableOn hfi.integrableOn

variable [CompleteSpace E]

@[simp]
/-
**MeasureTheory.average_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：average_const (μ : Measure α) [IsFiniteMeasure μ] [h : NeZero μ] (c : E) :
 ⨍ _x, c ∂μ = c
参数：μ : Measure α；c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.average.eq_1`：∀ {α : Type u_1} {E : Type u_2} {m0 : Measur
ableSpace α} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   (μ : Mea
sureTheory.Measu…
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `ENNReal.toReal_one`：ENNReal.toReal 1 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem average_const (μ : Measure α) [IsFiniteMeasure μ] [h : NeZero μ] (c : E) :
    ⨍ _x, c ∂μ = c := by
  rw [average, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
/-
**MeasureTheory.setAverage_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setAverage_const {s : Set α} (hs₀ : μ s != 0) (hs : μ s != ∞) (c : E) : ⨍ 
_ in s, c ∂μ = c
参数：hs₀ : μ s != 0；hs : μ s != ∞；c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.average_const`：average_const (μ : Measure α) [IsFiniteMeas
ure μ] [h : NeZero μ] (c : E) : ⨍ _x, c ∂μ = c
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
· 使用定理 `MeasureTheory.Measure.restrict.neZero`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s : Set α} [NeZero (μ s)],   NeZero (μ.r
estrict s)
-/
theorem setAverage_const {s : Set α} (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (c : E) :
    ⨍ _ in s, c ∂μ = c :=
  have := NeZero.mk hs₀; have := Fact.mk hs.lt_top; average_const _ _
/-
**MeasureTheory.integral_average** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_average (μ : Measure α) [IsFiniteMeasure μ] (f : α -> E) : ∫ _, ⨍
 a, f a ∂μ ∂μ = ∫ x, f x ∂μ
参数：μ : Measure α；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.measure_smul_average`：measure_smul_average [IsFiniteMeasur
e μ] (f : α -> E) : μ.real univ • ⨍ x, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_average (μ : Measure α) [IsFiniteMeasure μ] (f : α → E) :
    ∫ _, ⨍ a, f a ∂μ ∂μ = ∫ x, f x ∂μ := by simp
/-
**MeasureTheory.setIntegral_setAverage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：setIntegral_setAverage (μ : Measure α) [IsFiniteMeasure μ] (f : α -> E) (s
 : Set α) : ∫ _ in s, ⨍ a in s, f a ∂μ ∂μ = ∫ x in s, f x ∂μ
参数：μ : Measure α；f : α -> E；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_average`：integral_average (μ : Measure α) [IsFini
teMeasure μ] (f : α -> E) : ∫ _, ⨍ a, f a ∂μ ∂μ = ∫ x, f x ∂μ
-/
theorem setIntegral_setAverage (μ : Measure α) [IsFiniteMeasure μ] (f : α → E) (s : Set α) :
    ∫ _ in s, ⨍ a in s, f a ∂μ ∂μ = ∫ x in s, f x ∂μ :=
  integral_average _ _
/-
**MeasureTheory.integral_sub_average** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_sub_average (μ : Measure α) [IsFiniteMeasure μ] (f : α -> E) : ∫ 
x, f x - ⨍ a, f a ∂μ ∂μ = 0
参数：μ : Measure α；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.integral_average`：integral_average (μ : Measure α) [IsFini
teMeasure μ] (f : α -> E) : ∫ _, ⨍ a, f a ∂μ ∂μ = ∫ x, f x ∂μ
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem integral_sub_average (μ : Measure α) [IsFiniteMeasure μ] (f : α → E) :
    ∫ x, f x - ⨍ a, f a ∂μ ∂μ = 0 := by
  by_cases hf : Integrable f μ
  · rw [integral_sub hf (integrable_const _), integral_average, sub_self]
  refine integral_undef fun h => hf ?_
  convert! h.add (integrable_const (⨍ a, f a ∂μ))
  exact (sub_add_cancel _ _).symm
/-
**MeasureTheory.setAverage_sub_setAverage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：setAverage_sub_setAverage (hs : μ s != ∞) (f : α -> E) : ∫ x in s, f x - ⨍
 a in s, f a ∂μ ∂μ = 0
参数：hs : μ s != ∞；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_sub_average`：integral_sub_average (μ : Measure α)
 [IsFiniteMeasure μ] (f : α -> E) : ∫ x, f x - ⨍ a, f a ∂μ ∂μ = 0
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
theorem setAverage_sub_setAverage (hs : μ s ≠ ∞) (f : α → E) :
    ∫ x in s, f x - ⨍ a in s, f a ∂μ ∂μ = 0 :=
  haveI : Fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩
  integral_sub_average _ _
/-
**MeasureTheory.integral_average_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_average_sub [IsFiniteMeasure μ] (hf : Integrable f μ) : ∫ x, ⨍ a,
 f a ∂μ - f x ∂μ = 0
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.integral_average`：integral_average (μ : Measure α) [IsFini
teMeasure μ] (f : α -> E) : ∫ _, ⨍ a, f a ∂μ ∂μ = ∫ x, f x ∂μ
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem integral_average_sub [IsFiniteMeasure μ] (hf : Integrable f μ) :
    ∫ x, ⨍ a, f a ∂μ - f x ∂μ = 0 := by
  rw [integral_sub (integrable_const _) hf, integral_average, sub_self]
/-
**MeasureTheory.setIntegral_setAverage_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：setIntegral_setAverage_sub (hs : μ s != ∞) (hf : IntegrableOn f s μ) : ∫ x
 in s, ⨍ a in s, f a ∂μ - f x ∂μ = 0
参数：hs : μ s != ∞；hf : IntegrableOn f s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_average_sub`：integral_average_sub [IsFiniteMeasur
e μ] (hf : Integrable f μ) : ∫ x, ⨍ a, f a ∂μ - f x ∂μ = 0
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
theorem setIntegral_setAverage_sub (hs : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    ∫ x in s, ⨍ a in s, f a ∂μ - f x ∂μ = 0 :=
  haveI : Fact (μ s < ∞) := ⟨lt_top_iff_ne_top.2 hs⟩
  integral_average_sub hf

end NormedAddCommGroup

/-
**MeasureTheory.ofReal_average** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ofReal_average {f : α -> Real} (hf : Integrable f μ) (hf₀ : 0 <=ᵐ[μ] f) : 
ENNReal.ofReal (⨍ x, f x ∂μ) = (∫⁻ x, ENNReal.ofReal (f x) ∂μ) / μ univ
参数：hf : Integrable f μ；hf₀ : 0 <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.average_zero_measure`：average_zero_measure (f : α -> E) : 
⨍ x, f x ∂(0 : Measure α) = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `ENNReal.zero_div`：∀ {a : ENNReal}, 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.average_eq`：average_eq (f : α -> E) : ⨍ x, f x ∂μ = (μ.rea
l univ)⁻¹ • ∫ x, f x ∂μ
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_ne_top`：inv_ne_top : a⁻¹ != ∞ ↔ a != 0
· 使用定理 `MeasureTheory.Measure.measure_univ_ne_zero`：measure_univ_ne_zero : μ uni
v != 0 ↔ μ != 0
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用定理 `ENNReal.div_eq_inv_mul`：∀ {a b : ENNReal}, a / b = b⁻¹ * a
-/
theorem ofReal_average {f : α → ℝ} (hf : Integrable f μ) (hf₀ : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (⨍ x, f x ∂μ) = (∫⁻ x, ENNReal.ofReal (f x) ∂μ) / μ univ := by
  obtain rfl | hμ := eq_or_ne μ 0
  · simp
  · rw [average_eq, smul_eq_mul, measureReal_def, ← toReal_inv, ofReal_mul toReal_nonneg,
      ofReal_toReal (inv_ne_top.2 <| measure_univ_ne_zero.2 hμ),
      ofReal_integral_eq_lintegral_ofReal hf hf₀, ENNReal.div_eq_inv_mul]
/-
**MeasureTheory.ofReal_setAverage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ofReal_setAverage {f : α -> Real} (hf : IntegrableOn f s μ) (hf₀ : 0 <=ᵐ[μ
.restrict s] f) : ENNReal.ofReal (⨍ x in s, f x ∂μ) = (∫⁻ x in s, ENNReal.ofReal
 (f x) ∂μ) / μ s
参数：hf : IntegrableOn f s μ；hf₀ : 0 <=ᵐ[μ.restrict s] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.ofReal_average`：ofReal_average {f : α -> Real} (hf : Integ
rable f μ) (hf₀ : 0 <=ᵐ[μ] f) : ENNReal.ofReal (⨍ x, f x ∂μ) = (∫⁻ x, ENNReal.of
Real (f x) ∂μ) / μ…
-/
theorem ofReal_setAverage {f : α → ℝ} (hf : IntegrableOn f s μ) (hf₀ : 0 ≤ᵐ[μ.restrict s] f) :
    ENNReal.ofReal (⨍ x in s, f x ∂μ) = (∫⁻ x in s, ENNReal.ofReal (f x) ∂μ) / μ s := by
  simpa using ofReal_average hf hf₀
/-
**MeasureTheory.toReal_laverage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：toReal_laverage {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (hf' : forallᵐ
 x ∂μ, f x != ∞) : (⨍⁻ x, f x ∂μ).toReal = ⨍ x, (f x).toReal ∂μ
参数：hf : AEMeasurable f μ；hf' : forallᵐ x ∂μ, f x != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.average_eq`：average_eq (f : α -> E) : ⨍ x, f x ∂μ = (μ.rea
l univ)⁻¹ • ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.laverage_eq`：laverage_eq (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂
μ = (∫⁻ x, f x ∂μ) / μ univ
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ENNReal.toReal_div`：∀ (a b : ENNReal), (a / b).toReal = a.toReal / b.toR
eal
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_toReal`：integral_toReal {f : α -> Real>=0∞} (hfm 
: AEMeasurable f μ) (hf : forallᵐ x ∂μ, f x < ∞) : ∫ a, (f a).toReal ∂μ = (∫⁻ a,
 f a ∂μ).toReal
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
-/
theorem toReal_laverage {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf' : ∀ᵐ x ∂μ, f x ≠ ∞) :
    (⨍⁻ x, f x ∂μ).toReal = ⨍ x, (f x).toReal ∂μ := by
    rw [average_eq, laverage_eq, smul_eq_mul, toReal_div, div_eq_inv_mul, ←
      integral_toReal hf (hf'.mono fun _ => lt_top_iff_ne_top.2), measureReal_def]
/-
**MeasureTheory.toReal_setLAverage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：toReal_setLAverage {f : α -> Real>=0∞} (hf : AEMeasurable f (μ.restrict s)
) (hf' : forallᵐ x ∂μ.restrict s, f x != ∞) : (⨍⁻ x in s, f x ∂μ).toReal = ⨍ x i
n s, (f x).toReal ∂μ
参数：hf : AEMeasurable f (μ.restrict s)；hf' : forallᵐ x ∂μ.restrict s, f x != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.laverage_eq`：laverage_eq (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂
μ = (∫⁻ x, f x ∂μ) / μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `ENNReal.toReal_div`：∀ (a b : ENNReal), (a / b).toReal = a.toReal / b.toR
eal
· 使用定理 `MeasureTheory.toReal_laverage`：toReal_laverage {f : α -> Real>=0∞} (hf :
 AEMeasurable f μ) (hf' : forallᵐ x ∂μ, f x != ∞) : (⨍⁻ x, f x ∂μ).toReal = ⨍ x,
 (f x).toReal ∂μ
-/
theorem toReal_setLAverage {f : α → ℝ≥0∞} (hf : AEMeasurable f (μ.restrict s))
    (hf' : ∀ᵐ x ∂μ.restrict s, f x ≠ ∞) :
    (⨍⁻ x in s, f x ∂μ).toReal = ⨍ x in s, (f x).toReal ∂μ := by
  simpa [laverage_eq] using toReal_laverage hf hf'

/-! ### First moment method -/

section FirstMomentReal
variable {N : Set α} {f : α → ℝ}

/-- **First moment method**. An integrable function is smaller than its mean on a set of positive
measure. -/
/-
**MeasureTheory.measure_le_setAverage_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：measure_le_setAverage_pos (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : Integrabl
eOn f s μ) : 0 < μ ({x in s | f x <= ⨍ a in s, f a ∂μ})
参数：hμ : μ s != 0；hμ₁ : μ s != ∞；hf : IntegrableOn f s μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply₀`：restrict_apply₀ (ht : NullMeasura
bleSet t (μ.restrict s)) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_le`：nullMeasurableS
et_le [Preorder β] [OrderClosedTopology β] [PseudoMetrizableSpace β] {f g : α ->
 β} (hf : AEStronglyMeasurable f μ) (hg : AES…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Eq.not_gt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬b < 
a
· 使用定理 `MeasureTheory.integral_sub_average`：integral_sub_average (μ : Measure α)
 [IsFiniteMeasure μ] (f : α -> E) : ∫ x, f x - ⨍ a, f a ∂μ ∂μ = 0
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
· 使用定理 `MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae`：setIntegral_pos_
iff_support_of_nonneg_ae {f : X -> Real} (hf : 0 <=ᵐ[μ.restrict s] f) (hfi : Int
egrableOn f s μ) : (0 < ∫ x in s, f x ∂μ) ↔ …
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.IntegrableOn.sub`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f g : α …
· 使用定理 `MeasureTheory.integrableOn_const`：integrableOn_const {C : ε'} (hs : μ s 
!= ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
**First moment method**. An integrable function is smaller than its mean on a se
t of positive
measure.
-/
theorem measure_le_setAverage_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    0 < μ ({x ∈ s | f x ≤ ⨍ a in s, f a ∂μ}) := by
  refine pos_iff_ne_zero.2 fun H => ?_
  replace H : (μ.restrict s) {x | f x ≤ ⨍ a in s, f a ∂μ} = 0 := by
    rwa [restrict_apply₀, inter_comm]
    exact AEStronglyMeasurable.nullMeasurableSet_le hf.1 aestronglyMeasurable_const
  have := Fact.mk hμ₁.lt_top
  refine (integral_sub_average (μ.restrict s) f).not_gt ?_
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ ?_).2 ?_
  · refine measure_mono_null (fun x hx ↦ ?_) H
    simp only [Pi.zero_apply, sub_nonneg, mem_compl_iff, mem_ofPred_eq, not_le] at hx
    exact hx.le
  · exact hf.sub (integrableOn_const hμ₁)
  · rwa [pos_iff_ne_zero, inter_comm, ← sdiff_compl, ← sdiff_inter_self_eq_sdiff,
      measure_sdiff_null]
    refine measure_mono_null ?_ (measure_inter_eq_zero_of_restrict H)
    exact inter_subset_inter_left _ fun a ha => (sub_eq_zero.1 <| of_not_not ha).le

/-- **First moment method**. An integrable function is greater than its mean on a set of positive
measure. -/
/-
**MeasureTheory.measure_setAverage_le_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：measure_setAverage_le_pos (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : Integrabl
eOn f s μ) : 0 < μ ({x in s | ⨍ a in s, f a ∂μ <= f x})
参数：hμ : μ s != 0；hμ₁ : μ s != ∞；hf : IntegrableOn f s μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.average_neg`：average_neg (f : α -> E) : ⨍ x, -f x ∂μ = -⨍ 
x, f x ∂μ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.measure_le_setAverage_pos`：measure_le_setAverage_pos (hμ :
 μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ) : 0 < μ ({x in s | f x <= 
⨍ a in s, f a ∂μ})
· 使用定理 `MeasureTheory.IntegrableOn.neg`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f : α → …

--- 原说明 ---
**First moment method**. An integrable function is greater than its mean on a se
t of positive
measure.
-/
theorem measure_setAverage_le_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    0 < μ ({x ∈ s | ⨍ a in s, f a ∂μ ≤ f x}) := by
  simpa [integral_neg, neg_div] using measure_le_setAverage_pos hμ hμ₁ hf.neg

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
/-
**MeasureTheory.exists_le_setAverage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_le_setAverage (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f
 s μ) : exists x in s, f x <= ⨍ a in s, f a ∂μ
参数：hμ : μ s != 0；hμ₁ : μ s != ∞；hf : IntegrableOn f s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.measure_le_setAverage_pos`：measure_le_setAverage_pos (hμ :
 μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ) : 0 < μ ({x in s | f x <= 
⨍ a in s, f a ∂μ})

--- 原说明 ---
**First moment method**. The minimum of an integrable function is smaller than i
ts mean.
-/
theorem exists_le_setAverage (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    ∃ x ∈ s, f x ≤ ⨍ a in s, f a ∂μ :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_setAverage_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩

/-- **First moment method**. The maximum of an integrable function is greater than its mean. -/
/-
**MeasureTheory.exists_setAverage_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_setAverage_le (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f
 s μ) : exists x in s, ⨍ a in s, f a ∂μ <= f x
参数：hμ : μ s != 0；hμ₁ : μ s != ∞；hf : IntegrableOn f s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.measure_setAverage_le_pos`：measure_setAverage_le_pos (hμ :
 μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ) : 0 < μ ({x in s | ⨍ a in 
s, f a ∂μ <= f x})

--- 原说明 ---
**First moment method**. The maximum of an integrable function is greater than i
ts mean.
-/
theorem exists_setAverage_le (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : IntegrableOn f s μ) :
    ∃ x ∈ s, ⨍ a in s, f a ∂μ ≤ f x :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_setAverage_le_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩

section FiniteMeasure

variable [IsFiniteMeasure μ]

/-- **First moment method**. An integrable function is smaller than its mean on a set of positive
measure. -/
/-
**MeasureTheory.measure_le_average_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measure_le_average_pos (hμ : μ != 0) (hf : Integrable f μ) : 0 < μ {x | f 
x <= ⨍ a, f a ∂μ}
参数：hμ : μ != 0；hf : Integrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MeasureTheory.measure_le_setAverage_pos`：measure_le_setAverage_pos (hμ :
 μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ) : 0 < μ ({x in s | f x <= 
⨍ a in s, f a ∂μ})
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.measure_univ_ne_zero`：measure_univ_ne_zero : μ uni
v != 0 ↔ μ != 0
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…

--- 原说明 ---
**First moment method**. An integrable function is smaller than its mean on a se
t of positive
measure.
-/
theorem measure_le_average_pos (hμ : μ ≠ 0) (hf : Integrable f μ) :
    0 < μ {x | f x ≤ ⨍ a, f a ∂μ} := by
  simpa using measure_le_setAverage_pos (Measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
    hf.integrableOn

/-- **First moment method**. An integrable function is greater than its mean on a set of positive
measure. -/
/-
**MeasureTheory.measure_average_le_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measure_average_le_pos (hμ : μ != 0) (hf : Integrable f μ) : 0 < μ {x | ⨍ 
a, f a ∂μ <= f x}
参数：hμ : μ != 0；hf : Integrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MeasureTheory.measure_setAverage_le_pos`：measure_setAverage_le_pos (hμ :
 μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ) : 0 < μ ({x in s | ⨍ a in 
s, f a ∂μ <= f x})
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.measure_univ_ne_zero`：measure_univ_ne_zero : μ uni
v != 0 ↔ μ != 0
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…

--- 原说明 ---
**First moment method**. An integrable function is greater than its mean on a se
t of positive
measure.
-/
theorem measure_average_le_pos (hμ : μ ≠ 0) (hf : Integrable f μ) :
    0 < μ {x | ⨍ a, f a ∂μ ≤ f x} := by
  simpa using measure_setAverage_le_pos (Measure.measure_univ_ne_zero.2 hμ) (measure_ne_top _ _)
    hf.integrableOn

/-- **First moment method**. The minimum of an integrable function is smaller than its mean. -/
/-
**MeasureTheory.exists_le_average** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_le_average (hμ : μ != 0) (hf : Integrable f μ) : exists x, f x <= ⨍
 a, f a ∂μ
参数：hμ : μ != 0；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.measure_le_average_pos`：measure_le_average_pos (hμ : μ != 
0) (hf : Integrable f μ) : 0 < μ {x | f x <= ⨍ a, f a ∂μ}

--- 原说明 ---
**First moment method**. The minimum of an integrable function is smaller than i
ts mean.
-/
theorem exists_le_average (hμ : μ ≠ 0) (hf : Integrable f μ) : ∃ x, f x ≤ ⨍ a, f a ∂μ :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_average_pos hμ hf).ne'
  ⟨x, hx⟩

/-- **First moment method**. The maximum of an integrable function is greater than its mean. -/
/-
**MeasureTheory.exists_average_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_average_le (hμ : μ != 0) (hf : Integrable f μ) : exists x, ⨍ a, f a
 ∂μ <= f x
参数：hμ : μ != 0；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.measure_average_le_pos`：measure_average_le_pos (hμ : μ != 
0) (hf : Integrable f μ) : 0 < μ {x | ⨍ a, f a ∂μ <= f x}

--- 原说明 ---
**First moment method**. The maximum of an integrable function is greater than i
ts mean.
-/
theorem exists_average_le (hμ : μ ≠ 0) (hf : Integrable f μ) : ∃ x, ⨍ a, f a ∂μ ≤ f x :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_average_le_pos hμ hf).ne'
  ⟨x, hx⟩

/-- **First moment method**. The minimum of an integrable function is smaller than its mean, while
avoiding a null set. -/
/-
**MeasureTheory.exists_notMem_null_le_average** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：exists_notMem_null_le_average (hμ : μ != 0) (hf : Integrable f μ) (hN : μ 
N = 0) : exists x, x ∉ N ∧ f x <= ⨍ a, f a ∂μ
参数：hμ : μ != 0；hf : Integrable f μ；hN : μ N = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_le_average_pos`：measure_le_average_pos (hμ : μ != 
0) (hf : Integrable f μ) : 0 < μ {x | f x <= ⨍ a, f a ∂μ}
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_sdiff_null`：measure_sdiff_null (ht : μ t = 0) : μ 
(s \ t) = μ s
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
**First moment method**. The minimum of an integrable function is smaller than i
ts mean, while
avoiding a null set.
-/
theorem exists_notMem_null_le_average (hμ : μ ≠ 0) (hf : Integrable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ f x ≤ ⨍ a, f a ∂μ := by
  have := measure_le_average_pos hμ hf
  rw [← measure_sdiff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩

/-- **First moment method**. The maximum of an integrable function is greater than its mean, while
avoiding a null set. -/
/-
**MeasureTheory.exists_notMem_null_average_le** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：exists_notMem_null_average_le (hμ : μ != 0) (hf : Integrable f μ) (hN : μ 
N = 0) : exists x, x ∉ N ∧ ⨍ a, f a ∂μ <= f x
参数：hμ : μ != 0；hf : Integrable f μ；hN : μ N = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.average_neg`：average_neg (f : α -> E) : ⨍ x, -f x ∂μ = -⨍ 
x, f x ∂μ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.exists_notMem_null_le_average`：exists_notMem_null_le_avera
ge (hμ : μ != 0) (hf : Integrable f μ) (hN : μ N = 0) : exists x, x ∉ N ∧ f x <=
 ⨍ a, f a ∂μ
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…

--- 原说明 ---
**First moment method**. The maximum of an integrable function is greater than i
ts mean, while
avoiding a null set.
-/
theorem exists_notMem_null_average_le (hμ : μ ≠ 0) (hf : Integrable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ ⨍ a, f a ∂μ ≤ f x := by
  simpa [integral_neg, neg_div] using exists_notMem_null_le_average hμ hf.neg hN

end FiniteMeasure

section ProbabilityMeasure

variable [IsProbabilityMeasure μ]

/-- **First moment method**. An integrable function is smaller than its integral on a set of
positive measure. -/
/-
**MeasureTheory.measure_le_integral_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measure_le_integral_pos (hf : Integrable f μ) : 0 < μ {x | f x <= ∫ a, f a
 ∂μ}
参数：hf : Integrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.average_eq_integral`：average_eq_integral [IsProbabilityMea
sure μ] (f : α -> E) : ⨍ x, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.measure_le_average_pos`：measure_le_average_pos (hμ : μ != 
0) (hf : Integrable f μ) : 0 < μ {x | f x <= ⨍ a, f a ∂μ}
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0

--- 原说明 ---
**First moment method**. An integrable function is smaller than its integral on 
a set of
positive measure.
-/
theorem measure_le_integral_pos (hf : Integrable f μ) : 0 < μ {x | f x ≤ ∫ a, f a ∂μ} := by
  simpa only [average_eq_integral] using
    measure_le_average_pos (IsProbabilityMeasure.ne_zero μ) hf

/-- **First moment method**. An integrable function is greater than its integral on a set of
positive measure. -/
/-
**MeasureTheory.measure_integral_le_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measure_integral_le_pos (hf : Integrable f μ) : 0 < μ {x | ∫ a, f a ∂μ <= 
f x}
参数：hf : Integrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.average_eq_integral`：average_eq_integral [IsProbabilityMea
sure μ] (f : α -> E) : ⨍ x, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.measure_average_le_pos`：measure_average_le_pos (hμ : μ != 
0) (hf : Integrable f μ) : 0 < μ {x | ⨍ a, f a ∂μ <= f x}
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0

--- 原说明 ---
**First moment method**. An integrable function is greater than its integral on 
a set of
positive measure.
-/
theorem measure_integral_le_pos (hf : Integrable f μ) : 0 < μ {x | ∫ a, f a ∂μ ≤ f x} := by
  simpa only [average_eq_integral] using
    measure_average_le_pos (IsProbabilityMeasure.ne_zero μ) hf

/-- **First moment method**. The minimum of an integrable function is smaller than its integral. -/
/-
**MeasureTheory.exists_le_integral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_le_integral (hf : Integrable f μ) : exists x, f x <= ∫ a, f a ∂μ
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.average_eq_integral`：average_eq_integral [IsProbabilityMea
sure μ] (f : α -> E) : ⨍ x, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.exists_le_average`：exists_le_average (hμ : μ != 0) (hf : I
ntegrable f μ) : exists x, f x <= ⨍ a, f a ∂μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0

--- 原说明 ---
**First moment method**. The minimum of an integrable function is smaller than i
ts integral.
-/
theorem exists_le_integral (hf : Integrable f μ) : ∃ x, f x ≤ ∫ a, f a ∂μ := by
  simpa only [average_eq_integral] using exists_le_average (IsProbabilityMeasure.ne_zero μ) hf

/-- **First moment method**. The maximum of an integrable function is greater than its integral. -/
/-
**MeasureTheory.exists_integral_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_integral_le (hf : Integrable f μ) : exists x, ∫ a, f a ∂μ <= f x
参数：hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.average_eq_integral`：average_eq_integral [IsProbabilityMea
sure μ] (f : α -> E) : ⨍ x, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.exists_average_le`：exists_average_le (hμ : μ != 0) (hf : I
ntegrable f μ) : exists x, ⨍ a, f a ∂μ <= f x
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0

--- 原说明 ---
**First moment method**. The maximum of an integrable function is greater than i
ts integral.
-/
theorem exists_integral_le (hf : Integrable f μ) : ∃ x, ∫ a, f a ∂μ ≤ f x := by
  simpa only [average_eq_integral] using exists_average_le (IsProbabilityMeasure.ne_zero μ) hf

/-- **First moment method**. The minimum of an integrable function is smaller than its integral,
while avoiding a null set. -/
/-
**MeasureTheory.exists_notMem_null_le_integral** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：exists_notMem_null_le_integral (hf : Integrable f μ) (hN : μ N = 0) : exis
ts x, x ∉ N ∧ f x <= ∫ a, f a ∂μ
参数：hf : Integrable f μ；hN : μ N = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.average_eq_integral`：average_eq_integral [IsProbabilityMea
sure μ] (f : α -> E) : ⨍ x, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.exists_notMem_null_le_average`：exists_notMem_null_le_avera
ge (hμ : μ != 0) (hf : Integrable f μ) (hN : μ N = 0) : exists x, x ∉ N ∧ f x <=
 ⨍ a, f a ∂μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0

--- 原说明 ---
**First moment method**. The minimum of an integrable function is smaller than i
ts integral,
while avoiding a null set.
-/
theorem exists_notMem_null_le_integral (hf : Integrable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ f x ≤ ∫ a, f a ∂μ := by
  simpa only [average_eq_integral] using
    exists_notMem_null_le_average (IsProbabilityMeasure.ne_zero μ) hf hN

/-- **First moment method**. The maximum of an integrable function is greater than its integral,
while avoiding a null set. -/
/-
**MeasureTheory.exists_notMem_null_integral_le** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：exists_notMem_null_integral_le (hf : Integrable f μ) (hN : μ N = 0) : exis
ts x, x ∉ N ∧ ∫ a, f a ∂μ <= f x
参数：hf : Integrable f μ；hN : μ N = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.average_eq_integral`：average_eq_integral [IsProbabilityMea
sure μ] (f : α -> E) : ⨍ x, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.exists_notMem_null_average_le`：exists_notMem_null_average_
le (hμ : μ != 0) (hf : Integrable f μ) (hN : μ N = 0) : exists x, x ∉ N ∧ ⨍ a, f
 a ∂μ <= f x
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0

--- 原说明 ---
**First moment method**. The maximum of an integrable function is greater than i
ts integral,
while avoiding a null set.
-/
theorem exists_notMem_null_integral_le (hf : Integrable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ ∫ a, f a ∂μ ≤ f x := by
  simpa only [average_eq_integral] using
    exists_notMem_null_average_le (IsProbabilityMeasure.ne_zero μ) hf hN

end ProbabilityMeasure
end FirstMomentReal

section FirstMomentENNReal
variable {N : Set α} {f : α → ℝ≥0∞}

/-- **First moment method**. A measurable function is smaller than its mean on a set of positive
measure. -/
/-
**MeasureTheory.measure_le_setLAverage_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measure_le_setLAverage_pos (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : AEMeasur
able f (μ.restrict s)) : 0 < μ {x in s | f x <= ⨍⁻ a in s, f a ∂μ}
参数：hμ : μ s != 0；hμ₁ : μ s != ∞；hf : AEMeasurable f (μ.restrict s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.measure_le_setAverage_pos`：measure_le_setAverage_pos (hμ :
 μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ) : 0 < μ ({x in s | f x <= 
⨍ a in s, f a ∂μ})
· 使用定理 `MeasureTheory.integrable_toReal_of_lintegral_ne_top`：integrable_toReal_o
f_lintegral_ne_top {f : α -> Real>=0∞} (hfm : AEMeasurable f μ) (hfi : ∫⁻ x, f x
 ∂μ != ∞) : Integrable (fun x => (f x).to…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ofPred_inter_eq_sep`：ofPred_inter_eq_sep (p : α -> Prop) (s : Set α)
 : {a | p a} inter s = {a in s | p a}
· 使用定理 `MeasureTheory.Measure.restrict_apply₀`：restrict_apply₀ (ht : NullMeasura
bleSet t (μ.restrict s)) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_le`：nullMeasurableS
et_le [Preorder β] [OrderClosedTopology β] [PseudoMetrizableSpace β] {f g : α ->
 β} (hf : AEStronglyMeasurable f μ) (hg : AES…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
**First moment method**. A measurable function is smaller than its mean on a set
 of positive
measure.
-/
theorem measure_le_setLAverage_pos (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞)
    (hf : AEMeasurable f (μ.restrict s)) : 0 < μ {x ∈ s | f x ≤ ⨍⁻ a in s, f a ∂μ} := by
  obtain h | h := eq_or_ne (∫⁻ a in s, f a ∂μ) ∞
  · simpa [mul_top, hμ₁, laverage, h, top_div_of_ne_top hμ₁, pos_iff_ne_zero] using hμ
  have := measure_le_setAverage_pos hμ hμ₁ (integrable_toReal_of_lintegral_ne_top hf h)
  rw [← ofPred_inter_eq_sep, ← Measure.restrict_apply₀
    (hf.aestronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const)]
  rw [← ofPred_inter_eq_sep, ← Measure.restrict_apply₀
    (hf.ennreal_toReal.aestronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const),
    ← measure_sdiff_null (measure_eq_top_of_lintegral_ne_top hf h)] at this
  refine this.trans_le (measure_mono ?_)
  rintro x ⟨hfx, hx⟩
  dsimp at hfx
  rwa [← toReal_laverage hf, toReal_le_toReal hx (setLAverage_lt_top h).ne] at hfx
  simp_rw [ae_iff, not_ne_iff]
  exact measure_eq_top_of_lintegral_ne_top hf h

/-- **First moment method**. A measurable function is greater than its mean on a set of positive
measure. -/
/-
**MeasureTheory.measure_setLAverage_le_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measure_setLAverage_le_pos (hμ : μ s != 0) (hs : NullMeasurableSet s μ) (h
int : ∫⁻ a in s, f a ∂μ != ∞) : 0 < μ {x in s | ⨍⁻ a in s, f a ∂μ <= f x}
参数：hμ : μ s != 0；hs : NullMeasurableSet s μ；hint : ∫⁻ a in s, f a ∂μ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.setLAverage_eq`：setLAverage_eq (f : α -> Real>=0∞) (s : Se
t α) : ⨍⁻ x in s, f x ∂μ = (∫⁻ x in s, f x ∂μ) / μ s
· 使用定理 `ENNReal.div_top`：∀ {a : ENNReal}, a / ⊤ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `MeasureTheory.exists_measurable_le_lintegral_eq`：exists_measurable_le_li
ntegral_eq (f : α -> Real>=0∞) : exists g : α -> Real>=0∞, Measurable g ∧ g <= f
 ∧ ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.laverage_eq`：laverage_eq (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂
μ = (∫⁻ x, f x ∂μ) / μ univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_setAverage_le_pos`：measure_setAverage_le_pos (hμ :
 μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ) : 0 < μ ({x in s | ⨍ a in 
s, f a ∂μ <= f x})
· 使用定理 `MeasureTheory.integrable_toReal_of_lintegral_ne_top`：integrable_toReal_o
f_lintegral_ne_top {f : α -> Real>=0∞} (hfm : AEMeasurable f μ) (hfi : ∫⁻ x, f x
 ∂μ != ∞) : Integrable (fun x => (f x).to…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_apply₀'`：restrict_apply₀' (hs : NullMeasu
rableSet s μ) : μ.restrict s t = μ (t inter s)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `MeasureTheory.measure_sdiff_null`：measure_sdiff_null (ht : μ t = 0) : μ 
(s \ t) = μ s
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_eq_top_of_lintegral_ne_top`：measure_eq_top_of_lint
egral_ne_top {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (hμf : ∫⁻ x, f x ∂μ != 
∞) : μ {x | f x = ∞} = 0
· 使用定理 `Set.ofPred_inter_eq_sep`：ofPred_inter_eq_sep (p : α -> Prop) (s : Set α)
 : {a | p a} inter s = {a in s | p a}
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ENNReal.toReal_le_toReal`：toReal_le_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal <= b.toReal ↔ a <= b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.setLAverage_lt_top`：setLAverage_lt_top : ∫⁻ x in s, f x ∂μ
 != ∞ -> ⨍⁻ x in s, f x ∂μ < ∞
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
**First moment method**. A measurable function is greater than its mean on a set
 of positive
measure.
-/
theorem measure_setLAverage_le_pos (hμ : μ s ≠ 0) (hs : NullMeasurableSet s μ)
    (hint : ∫⁻ a in s, f a ∂μ ≠ ∞) : 0 < μ {x ∈ s | ⨍⁻ a in s, f a ∂μ ≤ f x} := by
  obtain hμ₁ | hμ₁ := eq_or_ne (μ s) ∞
  · simp [setLAverage_eq, hμ₁]
  obtain ⟨g, hg, hgf, hfg⟩ := exists_measurable_le_lintegral_eq (μ.restrict s) f
  have hfg' : ⨍⁻ a in s, f a ∂μ = ⨍⁻ a in s, g a ∂μ := by simp_rw [laverage_eq, hfg]
  rw [hfg] at hint
  have :=
    measure_setAverage_le_pos hμ hμ₁ (integrable_toReal_of_lintegral_ne_top hg.aemeasurable hint)
  simp_rw [← ofPred_inter_eq_sep, ← Measure.restrict_apply₀' hs, hfg']
  rw [← ofPred_inter_eq_sep, ← Measure.restrict_apply₀' hs, ←
    measure_sdiff_null (measure_eq_top_of_lintegral_ne_top hg.aemeasurable hint)] at this
  refine this.trans_le (measure_mono ?_)
  rintro x ⟨hfx, hx⟩
  dsimp at hfx
  rw [← toReal_laverage hg.aemeasurable, toReal_le_toReal (setLAverage_lt_top hint).ne hx] at hfx
  · exact hfx.trans (hgf _)
  · simp_rw [ae_iff, not_ne_iff]
    exact measure_eq_top_of_lintegral_ne_top hg.aemeasurable hint

/-- **First moment method**. The minimum of a measurable function is smaller than its mean. -/
/-
**MeasureTheory.exists_le_setLAverage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_le_setLAverage (hμ : μ s != 0) (hμ₁ : μ s != ∞) (hf : AEMeasurable 
f (μ.restrict s)) : exists x in s, f x <= ⨍⁻ a in s, f a ∂μ
参数：hμ : μ s != 0；hμ₁ : μ s != ∞；hf : AEMeasurable f (μ.restrict s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.measure_le_setLAverage_pos`：measure_le_setLAverage_pos (hμ
 : μ s != 0) (hμ₁ : μ s != ∞) (hf : AEMeasurable f (μ.restrict s)) : 0 < μ {x in
 s | f x <= ⨍⁻ a in s, f a ∂μ}

--- 原说明 ---
**First moment method**. The minimum of a measurable function is smaller than it
s mean.
-/
theorem exists_le_setLAverage (hμ : μ s ≠ 0) (hμ₁ : μ s ≠ ∞) (hf : AEMeasurable f (μ.restrict s)) :
    ∃ x ∈ s, f x ≤ ⨍⁻ a in s, f a ∂μ :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_le_setLAverage_pos hμ hμ₁ hf).ne'
  ⟨x, hx, h⟩

/-- **First moment method**. The maximum of a measurable function is greater than its mean. -/
/-
**MeasureTheory.exists_setLAverage_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_setLAverage_le (hμ : μ s != 0) (hs : NullMeasurableSet s μ) (hint :
 ∫⁻ a in s, f a ∂μ != ∞) : exists x in s, ⨍⁻ a in s, f a ∂μ <= f x
参数：hμ : μ s != 0；hs : NullMeasurableSet s μ；hint : ∫⁻ a in s, f a ∂μ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.measure_setLAverage_le_pos`：measure_setLAverage_le_pos (hμ
 : μ s != 0) (hs : NullMeasurableSet s μ) (hint : ∫⁻ a in s, f a ∂μ != ∞) : 0 < 
μ {x in s | ⨍⁻ a in s, f a ∂μ …

--- 原说明 ---
**First moment method**. The maximum of a measurable function is greater than it
s mean.
-/
theorem exists_setLAverage_le (hμ : μ s ≠ 0) (hs : NullMeasurableSet s μ)
    (hint : ∫⁻ a in s, f a ∂μ ≠ ∞) : ∃ x ∈ s, ⨍⁻ a in s, f a ∂μ ≤ f x :=
  let ⟨x, hx, h⟩ := nonempty_of_measure_ne_zero (measure_setLAverage_le_pos hμ hs hint).ne'
  ⟨x, hx, h⟩

/-- **First moment method**. A measurable function is greater than its mean on a set of positive
measure. -/
/-
**MeasureTheory.measure_laverage_le_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measure_laverage_le_pos (hμ : μ != 0) (hint : ∫⁻ a, f a ∂μ != ∞) : 0 < μ {
x | ⨍⁻ a, f a ∂μ <= f x}
参数：hμ : μ != 0；hint : ∫⁻ a, f a ∂μ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.measure_setLAverage_le_pos`：measure_setLAverage_le_pos (hμ
 : μ s != 0) (hs : NullMeasurableSet s μ) (hint : ∫⁻ a in s, f a ∂μ != ∞) : 0 < 
μ {x in s | ⨍⁻ a in s, f a ∂μ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.measure_univ_ne_zero`：measure_univ_ne_zero : μ uni
v != 0 ↔ μ != 0
· 使用定理 `MeasureTheory.nullMeasurableSet_univ`：nullMeasurableSet_univ : NullMeasu
rableSet univ μ

--- 原说明 ---
**First moment method**. A measurable function is greater than its mean on a set
 of positive
measure.
-/
theorem measure_laverage_le_pos (hμ : μ ≠ 0) (hint : ∫⁻ a, f a ∂μ ≠ ∞) :
    0 < μ {x | ⨍⁻ a, f a ∂μ ≤ f x} := by
  simpa [hint] using
    @measure_setLAverage_le_pos _ _ _ _ f (measure_univ_ne_zero.2 hμ) nullMeasurableSet_univ

/-- **First moment method**. The maximum of a measurable function is greater than its mean. -/
/-
**MeasureTheory.exists_laverage_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_laverage_le (hμ : μ != 0) (hint : ∫⁻ a, f a ∂μ != ∞) : exists x, ⨍⁻
 a, f a ∂μ <= f x
参数：hμ : μ != 0；hint : ∫⁻ a, f a ∂μ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.measure_laverage_le_pos`：measure_laverage_le_pos (hμ : μ !
= 0) (hint : ∫⁻ a, f a ∂μ != ∞) : 0 < μ {x | ⨍⁻ a, f a ∂μ <= f x}

--- 原说明 ---
**First moment method**. The maximum of a measurable function is greater than it
s mean.
-/
theorem exists_laverage_le (hμ : μ ≠ 0) (hint : ∫⁻ a, f a ∂μ ≠ ∞) : ∃ x, ⨍⁻ a, f a ∂μ ≤ f x :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_laverage_le_pos hμ hint).ne'
  ⟨x, hx⟩

/-- **First moment method**. The maximum of a measurable function is greater than its mean, while
avoiding a null set. -/
/-
**MeasureTheory.exists_notMem_null_laverage_le** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：exists_notMem_null_laverage_le (hμ : μ != 0) (hint : ∫⁻ a : α, f a ∂μ != ∞
) (hN : μ N = 0) : exists x, x ∉ N ∧ ⨍⁻ a, f a ∂μ <= f x
参数：hμ : μ != 0；hint : ∫⁻ a : α, f a ∂μ != ∞；hN : μ N = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_laverage_le_pos`：measure_laverage_le_pos (hμ : μ !
= 0) (hint : ∫⁻ a, f a ∂μ != ∞) : 0 < μ {x | ⨍⁻ a, f a ∂μ <= f x}
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_sdiff_null`：measure_sdiff_null (ht : μ t = 0) : μ 
(s \ t) = μ s
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
**First moment method**. The maximum of a measurable function is greater than it
s mean, while
avoiding a null set.
-/
theorem exists_notMem_null_laverage_le (hμ : μ ≠ 0) (hint : ∫⁻ a : α, f a ∂μ ≠ ∞) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ ⨍⁻ a, f a ∂μ ≤ f x := by
  have := measure_laverage_le_pos hμ hint
  rw [← measure_sdiff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩

section FiniteMeasure
variable [IsFiniteMeasure μ]

/-- **First moment method**. A measurable function is smaller than its mean on a set of positive
measure. -/
/-
**MeasureTheory.measure_le_laverage_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measure_le_laverage_pos (hμ : μ != 0) (hf : AEMeasurable f μ) : 0 < μ {x |
 f x <= ⨍⁻ a, f a ∂μ}
参数：hμ : μ != 0；hf : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MeasureTheory.measure_le_setLAverage_pos`：measure_le_setLAverage_pos (hμ
 : μ s != 0) (hμ₁ : μ s != ∞) (hf : AEMeasurable f (μ.restrict s)) : 0 < μ {x in
 s | f x <= ⨍⁻ a in s, f a ∂μ}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.measure_univ_ne_zero`：measure_univ_ne_zero : μ uni
v != 0 ↔ μ != 0
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `AEMeasurable.restrict`：AEMeasurable.restrict (hfm : AEMeasurable f μ) {s
} : AEMeasurable f (μ.restrict s)

--- 原说明 ---
**First moment method**. A measurable function is smaller than its mean on a set
 of positive
measure.
-/
theorem measure_le_laverage_pos (hμ : μ ≠ 0) (hf : AEMeasurable f μ) :
    0 < μ {x | f x ≤ ⨍⁻ a, f a ∂μ} := by
  simpa using
    measure_le_setLAverage_pos (measure_univ_ne_zero.2 hμ) (measure_ne_top _ _) hf.restrict

/-- **First moment method**. The minimum of a measurable function is smaller than its mean. -/
/-
**MeasureTheory.exists_le_laverage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_le_laverage (hμ : μ != 0) (hf : AEMeasurable f μ) : exists x, f x <
= ⨍⁻ a, f a ∂μ
参数：hμ : μ != 0；hf : AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MeasureTheory.measure_le_laverage_pos`：measure_le_laverage_pos (hμ : μ !
= 0) (hf : AEMeasurable f μ) : 0 < μ {x | f x <= ⨍⁻ a, f a ∂μ}

--- 原说明 ---
**First moment method**. The minimum of a measurable function is smaller than it
s mean.
-/
theorem exists_le_laverage (hμ : μ ≠ 0) (hf : AEMeasurable f μ) : ∃ x, f x ≤ ⨍⁻ a, f a ∂μ :=
  let ⟨x, hx⟩ := nonempty_of_measure_ne_zero (measure_le_laverage_pos hμ hf).ne'
  ⟨x, hx⟩

/-- **First moment method**. The minimum of a measurable function is smaller than its mean, while
avoiding a null set. -/
/-
**MeasureTheory.exists_notMem_null_le_laverage** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：exists_notMem_null_le_laverage (hμ : μ != 0) (hf : AEMeasurable f μ) (hN :
 μ N = 0) : exists x, x ∉ N ∧ f x <= ⨍⁻ a, f a ∂μ
参数：hμ : μ != 0；hf : AEMeasurable f μ；hN : μ N = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_le_laverage_pos`：measure_le_laverage_pos (hμ : μ !
= 0) (hf : AEMeasurable f μ) : 0 < μ {x | f x <= ⨍⁻ a, f a ∂μ}
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_sdiff_null`：measure_sdiff_null (ht : μ t = 0) : μ 
(s \ t) = μ s
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
**First moment method**. The minimum of a measurable function is smaller than it
s mean, while
avoiding a null set.
-/
theorem exists_notMem_null_le_laverage (hμ : μ ≠ 0) (hf : AEMeasurable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ f x ≤ ⨍⁻ a, f a ∂μ := by
  have := measure_le_laverage_pos hμ hf
  rw [← measure_sdiff_null hN] at this
  obtain ⟨x, hx, hxN⟩ := nonempty_of_measure_ne_zero this.ne'
  exact ⟨x, hxN, hx⟩

end FiniteMeasure

section ProbabilityMeasure

variable [IsProbabilityMeasure μ]

/-- **First moment method**. A measurable function is smaller than its integral on a set f
positive measure. -/
/-
**MeasureTheory.measure_le_lintegral_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：measure_le_lintegral_pos (hf : AEMeasurable f μ) : 0 < μ {x | f x <= ∫⁻ a,
 f a ∂μ}
参数：hf : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.laverage_eq_lintegral`：laverage_eq_lintegral [IsProbabilit
yMeasure μ] (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.measure_le_laverage_pos`：measure_le_laverage_pos (hμ : μ !
= 0) (hf : AEMeasurable f μ) : 0 < μ {x | f x <= ⨍⁻ a, f a ∂μ}
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0

--- 原说明 ---
**First moment method**. A measurable function is smaller than its integral on a
 set f
positive measure.
-/
theorem measure_le_lintegral_pos (hf : AEMeasurable f μ) : 0 < μ {x | f x ≤ ∫⁻ a, f a ∂μ} := by
  simpa only [laverage_eq_lintegral] using
    measure_le_laverage_pos (IsProbabilityMeasure.ne_zero μ) hf

/-- **First moment method**. A measurable function is greater than its integral on a set f
positive measure. -/
/-
**MeasureTheory.measure_lintegral_le_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：measure_lintegral_le_pos (hint : ∫⁻ a, f a ∂μ != ∞) : 0 < μ {x | ∫⁻ a, f a
 ∂μ <= f x}
参数：hint : ∫⁻ a, f a ∂μ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.laverage_eq_lintegral`：laverage_eq_lintegral [IsProbabilit
yMeasure μ] (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.measure_laverage_le_pos`：measure_laverage_le_pos (hμ : μ !
= 0) (hint : ∫⁻ a, f a ∂μ != ∞) : 0 < μ {x | ⨍⁻ a, f a ∂μ <= f x}
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0

--- 原说明 ---
**First moment method**. A measurable function is greater than its integral on a
 set f
positive measure.
-/
theorem measure_lintegral_le_pos (hint : ∫⁻ a, f a ∂μ ≠ ∞) : 0 < μ {x | ∫⁻ a, f a ∂μ ≤ f x} := by
  simpa only [laverage_eq_lintegral] using
    measure_laverage_le_pos (IsProbabilityMeasure.ne_zero μ) hint

/-- **First moment method**. The minimum of a measurable function is smaller than its integral. -/
/-
**MeasureTheory.exists_le_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_le_lintegral (hf : AEMeasurable f μ) : exists x, f x <= ∫⁻ a, f a ∂
μ
参数：hf : AEMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.laverage_eq_lintegral`：laverage_eq_lintegral [IsProbabilit
yMeasure μ] (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.exists_le_laverage`：exists_le_laverage (hμ : μ != 0) (hf :
 AEMeasurable f μ) : exists x, f x <= ⨍⁻ a, f a ∂μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0

--- 原说明 ---
**First moment method**. The minimum of a measurable function is smaller than it
s integral.
-/
theorem exists_le_lintegral (hf : AEMeasurable f μ) : ∃ x, f x ≤ ∫⁻ a, f a ∂μ := by
  simpa only [laverage_eq_lintegral] using exists_le_laverage (IsProbabilityMeasure.ne_zero μ) hf

/-- **First moment method**. The maximum of a measurable function is greater than its integral. -/
/-
**MeasureTheory.exists_lintegral_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_lintegral_le (hint : ∫⁻ a, f a ∂μ != ∞) : exists x, ∫⁻ a, f a ∂μ <=
 f x
参数：hint : ∫⁻ a, f a ∂μ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.laverage_eq_lintegral`：laverage_eq_lintegral [IsProbabilit
yMeasure μ] (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.exists_laverage_le`：exists_laverage_le (hμ : μ != 0) (hint
 : ∫⁻ a, f a ∂μ != ∞) : exists x, ⨍⁻ a, f a ∂μ <= f x
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0

--- 原说明 ---
**First moment method**. The maximum of a measurable function is greater than it
s integral.
-/
theorem exists_lintegral_le (hint : ∫⁻ a, f a ∂μ ≠ ∞) : ∃ x, ∫⁻ a, f a ∂μ ≤ f x := by
  simpa only [laverage_eq_lintegral] using
    exists_laverage_le (IsProbabilityMeasure.ne_zero μ) hint

/-- **First moment method**. The minimum of a measurable function is smaller than its integral,
while avoiding a null set. -/
/-
**MeasureTheory.exists_notMem_null_le_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：exists_notMem_null_le_lintegral (hf : AEMeasurable f μ) (hN : μ N = 0) : e
xists x, x ∉ N ∧ f x <= ∫⁻ a, f a ∂μ
参数：hf : AEMeasurable f μ；hN : μ N = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.laverage_eq_lintegral`：laverage_eq_lintegral [IsProbabilit
yMeasure μ] (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.exists_notMem_null_le_laverage`：exists_notMem_null_le_lave
rage (hμ : μ != 0) (hf : AEMeasurable f μ) (hN : μ N = 0) : exists x, x ∉ N ∧ f 
x <= ⨍⁻ a, f a ∂μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0

--- 原说明 ---
**First moment method**. The minimum of a measurable function is smaller than it
s integral,
while avoiding a null set.
-/
theorem exists_notMem_null_le_lintegral (hf : AEMeasurable f μ) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ f x ≤ ∫⁻ a, f a ∂μ := by
  simpa only [laverage_eq_lintegral] using
    exists_notMem_null_le_laverage (IsProbabilityMeasure.ne_zero μ) hf hN

/-- **First moment method**. The maximum of a measurable function is greater than its integral,
while avoiding a null set. -/
/-
**MeasureTheory.exists_notMem_null_lintegral_le** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：exists_notMem_null_lintegral_le (hint : ∫⁻ a, f a ∂μ != ∞) (hN : μ N = 0) 
: exists x, x ∉ N ∧ ∫⁻ a, f a ∂μ <= f x
参数：hint : ∫⁻ a, f a ∂μ != ∞；hN : μ N = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.laverage_eq_lintegral`：laverage_eq_lintegral [IsProbabilit
yMeasure μ] (f : α -> Real>=0∞) : ⨍⁻ x, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.exists_notMem_null_laverage_le`：exists_notMem_null_laverag
e_le (hμ : μ != 0) (hint : ∫⁻ a : α, f a ∂μ != ∞) (hN : μ N = 0) : exists x, x ∉
 N ∧ ⨍⁻ a, f a ∂μ <= f x
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0

--- 原说明 ---
**First moment method**. The maximum of a measurable function is greater than it
s integral,
while avoiding a null set.
-/
theorem exists_notMem_null_lintegral_le (hint : ∫⁻ a, f a ∂μ ≠ ∞) (hN : μ N = 0) :
    ∃ x, x ∉ N ∧ ∫⁻ a, f a ∂μ ≤ f x := by
  simpa only [laverage_eq_lintegral] using
    exists_notMem_null_laverage_le (IsProbabilityMeasure.ne_zero μ) hint hN

end ProbabilityMeasure
end FirstMomentENNReal

/-- If the average of a function `f` along a sequence of sets `aₙ` converges to `c` (more precisely,
we require that `⨍ y in a i, ‖f y - c‖ ∂μ` tends to `0`), then the integral of `gₙ • f` also tends
to `c` if `gₙ` is supported in `aₙ`, has integral converging to one and supremum at most `K / μ aₙ`.
-/
/-
**MeasureTheory.tendsto_integral_smul_of_tendsto_average_norm_sub** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_integral_smul_of_tendsto_average_norm_sub [CompleteSpace E] {ι : T
ype*} {a : ι -> Set α} {l : Filter ι} {f : α -> E} {c : E} {g : ι -> α -> Real} 
(K : Real) (hf : Tendsto (fun i => ⨍ y in a i, ‖f y - c‖ ∂μ) l (𝓝 0)) (f_int : f
orallᶠ i in l, IntegrableOn f (a i) μ) (hg : Tendsto (fun i => ∫ y, g i y ∂μ) l 
(𝓝 1)) (g_supp : forallᶠ i in l, Function.support (g i) subseteq a i) (g_bound :
 forallᶠ i in l, forall x, |g i x| <= K / μ.real (a i)) : Tendsto (fun i => ∫ y,
 g i y • f y ∂μ) l (𝓝 c)
参数：K : Real；hf : Tendsto (fun i => ⨍ y in a i, ‖f y - c‖ ∂μ) l (𝓝 0)；f_int : for
allᶠ i in l, IntegrableOn f (a i) μ；hg : Tendsto (fun i => ∫ y, g i y ∂μ) l (𝓝 1
)；g_supp : forallᶠ i in l, Function.support (g i) subseteq a i；g_bound : forallᶠ
 i in l, forall x, |g i x| <= K / μ.real (a i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `integral_smul_const`：integral_smul_const {𝕜 : Type*} [RCLike 𝕜] [NormedS
pace 𝕜 E] [CompleteSpace E] (f : X -> 𝕜) (c : E) : ∫ x, f x • c ∂μ = (∫ x, f x ∂
μ) • c
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用引理 `Function.support_smul_subset_left`：support_smul_subset_left [Zero R] [Ze
ro M] [SMulWithZero R M] (f : α -> R) (g : α -> M) : support (f • g) subseteq su
pport f
· 使用定理 `MeasureTheory.integrableOn_iff_integrable_of_support_subset`：integrableO
n_iff_integrable_of_support_subset {f : α -> ε'} (h1s : support f subseteq s) : 
IntegrableOn f s μ ↔ Integrable f μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Integrable.smul_of_top_right`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   {𝕜 : Type u_8} [inst_1…
· 使用定理 `MeasureTheory.memLp_top_of_bound`：memLp_top_of_bound {f : α -> E} (hf : 
AEStronglyMeasurable f μ) (C : Real) (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : MemLp f 
∞ μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.restrict`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {f : α → β},   Measur…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
（共 82 条，此处仅展示前 30 条）

--- 原说明 ---
If the average of a function `f` along a sequence of sets `aₙ` converges to `c` 
(more precisely,
we require that `⨍ y in a i, ‖f y - c‖ ∂μ` tends to `0`), then the integral of `
gₙ • f` also tends
to `c` if `gₙ` is supported in `aₙ`, has integral converging to one and supremum
 at most `K / μ aₙ`.
-/
theorem tendsto_integral_smul_of_tendsto_average_norm_sub
    [CompleteSpace E]
    {ι : Type*} {a : ι → Set α} {l : Filter ι} {f : α → E} {c : E} {g : ι → α → ℝ} (K : ℝ)
    (hf : Tendsto (fun i ↦ ⨍ y in a i, ‖f y - c‖ ∂μ) l (𝓝 0))
    (f_int : ∀ᶠ i in l, IntegrableOn f (a i) μ)
    (hg : Tendsto (fun i ↦ ∫ y, g i y ∂μ) l (𝓝 1))
    (g_supp : ∀ᶠ i in l, Function.support (g i) ⊆ a i)
    (g_bound : ∀ᶠ i in l, ∀ x, |g i x| ≤ K / μ.real (a i)) :
    Tendsto (fun i ↦ ∫ y, g i y • f y ∂μ) l (𝓝 c) := by
  have g_int : ∀ᶠ i in l, Integrable (g i) μ := by
    filter_upwards [(tendsto_order.1 hg).1 _ zero_lt_one] with i hi
    contrapose hi
    simp only [integral_undef hi, lt_self_iff_false, not_false_eq_true]
  have I : ∀ᶠ i in l, ∫ y, g i y • (f y - c) ∂μ + (∫ y, g i y ∂μ) • c = ∫ y, g i y • f y ∂μ := by
    filter_upwards [f_int, g_int, g_supp, g_bound] with i hif hig hisupp hibound
    rw [← integral_smul_const, ← integral_add]
    · simp only [smul_sub, sub_add_cancel]
    · simp_rw [smul_sub]
      apply Integrable.sub _ (hig.smul_const _)
      have A : Function.support (fun y ↦ g i y • f y) ⊆ a i := by
        apply Subset.trans _ hisupp
        exact Function.support_smul_subset_left _ _
      rw [← integrableOn_iff_integrable_of_support_subset A]
      apply Integrable.smul_of_top_right hif
      exact memLp_top_of_bound hig.aestronglyMeasurable.restrict
        (K / μ.real (a i)) (Eventually.of_forall hibound)
    · exact hig.smul_const _
  have L0 : Tendsto (fun i ↦ ∫ y, g i y • (f y - c) ∂μ) l (𝓝 0) := by
    have := hf.const_mul K
    simp only [mul_zero] at this
    refine squeeze_zero_norm' ?_ this
    filter_upwards [g_supp, g_bound, f_int, (tendsto_order.1 hg).1 _ zero_lt_one]
      with i hi h'i h''i hi_int
    have mu_ai : μ (a i) < ∞ := by
      rw [lt_top_iff_ne_top]
      intro h
      simp only [h, ENNReal.toReal_top, _root_.div_zero, abs_nonpos_iff, measureReal_def] at h'i
      have : ∫ (y : α), g i y ∂μ = ∫ (y : α), 0 ∂μ := by congr; ext y; exact h'i y
      simp [this] at hi_int
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [average_eq, smul_eq_mul, ← integral_const_mul, norm_smul, ← mul_assoc,
      ← div_eq_mul_inv]
    have : ∀ x, x ∉ a i → ‖g i x‖ * ‖(f x - c)‖ = 0 := by
      intro x hx
      have : g i x = 0 := by rw [← Function.notMem_support]; exact fun h ↦ hx (hi h)
      simp [this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero this (μ := μ)]
    refine integral_mono_of_nonneg (Eventually.of_forall (fun x ↦ by positivity)) ?_
      (Eventually.of_forall (fun x ↦ ?_))
    · apply (Integrable.sub h''i _).norm.const_mul
      change IntegrableOn (fun _ ↦ c) (a i) μ
      simp [mu_ai]
    · dsimp; gcongr; simpa using h'i x
  have := L0.add (hg.smul_const c)
  simp only [one_smul, zero_add] at this
  exact Tendsto.congr' I this

/-- If `s` is a connected set of finite, nonzero `μ`-measure and `f : α → ℝ` is continuous on `s`
and integrable on `s` w.r.t. `μ`, then `f` attains its `μ`-average on `s`. -/
/-
**MeasureTheory.exists_eq_setAverage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_eq_setAverage [TopologicalSpace α] {f : α -> Real} (hs : IsConnecte
d s) (hf : ContinuousOn f s) (hint : IntegrableOn f s μ) (hμfin : μ s != ⊤) (hμ0
 : μ s != 0) : exists c in s, f c = ⨍ x in s, f x ∂μ
参数：hs : IsConnected s；hf : ContinuousOn f s；hint : IntegrableOn f s μ；hμfin : μ 
s != ⊤；hμ0 : μ s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_le_setAverage_pos`：measure_le_setAverage_pos (hμ :
 μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ) : 0 < μ ({x in s | f x <= 
⨍ a in s, f a ∂μ})
· 使用定理 `MeasureTheory.measure_setAverage_le_pos`：measure_setAverage_le_pos (hμ :
 μ s != 0) (hμ₁ : μ s != ∞) (hf : IntegrableOn f s μ) : 0 < μ ({x in s | ⨍ a in 
s, f a ∂μ <= f x})
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `IsPreconnected.intermediate_value`：IsPreconnected.intermediate_value {s 
: Set X} (hs : IsPreconnected s) {a b : X} (ha : a in s) (hb : b in s) {f : X ->
 α} (hf : ContinuousOn …
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
If `s` is a connected set of finite, nonzero `μ`-measure and `f : α → ℝ` is cont
inuous on `s`
and integrable on `s` w.r.t. `μ`, then `f` attains its `μ`-average on `s`.
-/
theorem exists_eq_setAverage
    [TopologicalSpace α] {f : α → ℝ} (hs : IsConnected s) (hf : ContinuousOn f s)
    (hint : IntegrableOn f s μ) (hμfin : μ s ≠ ⊤) (hμ0 : μ s ≠ 0) :
    ∃ c ∈ s, f c = ⨍ x in s, f x ∂μ := by
  let ave := ⨍ x in s, f x ∂μ
  let S₁ : Set α := {x | x ∈ s ∧ f x ≤ ave}
  let S₂ : Set α := {x | x ∈ s ∧ ave ≤ f x}
  have hS₁ : 0 < μ S₁ := measure_le_setAverage_pos hμ0 hμfin hint
  have hS₂ : 0 < μ S₂ := measure_setAverage_le_pos hμ0 hμfin hint
  rcases nonempty_of_measure_ne_zero hS₁.ne' with ⟨c₁, hc₁⟩
  rcases nonempty_of_measure_ne_zero hS₂.ne' with ⟨c₂, hc₂⟩
  apply hs.isPreconnected.intermediate_value hc₁.1 hc₂.1 hf
  grind

end MeasureTheory

