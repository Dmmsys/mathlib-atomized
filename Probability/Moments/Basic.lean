/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integration

/-!
# Moments and moment-generating function

## Main definitions

* `ProbabilityTheory.moment X p μ`: `p`th moment of a real random variable `X` with respect to
  measure `μ`, `μ[X^p]`
* `ProbabilityTheory.centralMoment X p μ`:`p`th central moment of `X` with respect to measure `μ`,
  `μ[(X - μ[X])^p]`
* `ProbabilityTheory.mgf X μ t`: moment-generating function of `X` with respect to measure `μ`,
  `μ[exp(t*X)]`
* `ProbabilityTheory.cgf X μ t`: cumulant-generating function, logarithm of the moment-generating
  function

## Main results

* `ProbabilityTheory.IndepFun.mgf_add`: if two real random variables `X` and `Y` are independent
  and their moment-generating functions are defined at `t`, then
  `mgf (X + Y) μ t = mgf X μ t * mgf Y μ t`
* `ProbabilityTheory.IndepFun.cgf_add`: if two real random variables `X` and `Y` are independent
  and their cumulant-generating functions are defined at `t`, then
  `cgf (X + Y) μ t = cgf X μ t + cgf Y μ t`
* `ProbabilityTheory.measure_ge_le_exp_cgf` and `ProbabilityTheory.measure_le_le_exp_cgf`:
  Chernoff bound on the upper (resp. lower) tail of a random variable. For `t` nonnegative such that
  the cumulant-generating function exists, `ℙ(ε ≤ X) ≤ exp(- t*ε + cgf X ℙ t)`. See also
  `ProbabilityTheory.measure_ge_le_exp_mul_mgf` and
  `ProbabilityTheory.measure_le_le_exp_mul_mgf` for versions of these results using `mgf` instead
  of `cgf`.
-/

@[expose] public section


open MeasureTheory Filter Finset Real

noncomputable section

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {p : ℕ} {μ : Measure Ω}

/-- Moment of a real random variable, `μ[X ^ p]`. -/
/-
**ProbabilityTheory.moment** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：moment (X : Ω -> Real) (p : Nat) (μ : Measure Ω) : Real
参数：X : Ω -> Real；p : Nat；μ : Measure Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Moment of a real random variable, `μ[X ^ p]`.
-/
def moment (X : Ω → ℝ) (p : ℕ) (μ : Measure Ω) : ℝ :=
  μ[X ^ p]
/-
**ProbabilityTheory.moment_def** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：moment_def (X : Ω -> Real) (p : Nat) (μ : Measure Ω) : moment X p μ = μ[X 
^ p]
参数：X : Ω -> Real；p : Nat；μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma moment_def (X : Ω → ℝ) (p : ℕ) (μ : Measure Ω) :
    moment X p μ = μ[X ^ p] := rfl

/-- Central moment of a real random variable, `μ[(X - μ[X]) ^ p]`. -/
/-
**ProbabilityTheory.centralMoment** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：centralMoment (X : Ω -> Real) (p : Nat) (μ : Measure Ω) : Real
参数：X : Ω -> Real；p : Nat；μ : Measure Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Central moment of a real random variable, `μ[(X - μ[X]) ^ p]`.
-/
def centralMoment (X : Ω → ℝ) (p : ℕ) (μ : Measure Ω) : ℝ :=
  μ[(X - fun (_ : Ω) => μ[X]) ^ p]

@[simp]
/-
**ProbabilityTheory.moment_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：moment_zero (hp : p != 0) : moment 0 p μ = 0
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem moment_zero (hp : p ≠ 0) : moment 0 p μ = 0 := by
  simp only [moment, hp, zero_pow, Ne, not_false_iff, Pi.zero_apply, integral_const,
    smul_eq_mul, mul_zero]

@[simp]
/-
**ProbabilityTheory.moment_zero_measure** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：moment_zero_measure : moment X p (0 : Measure Ω) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma moment_zero_measure : moment X p (0 : Measure Ω) = 0 := by simp [moment]

@[simp]
/-
**ProbabilityTheory.centralMoment_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：centralMoment_zero (hp : p != 0) : centralMoment 0 p μ = 0
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem centralMoment_zero (hp : p ≠ 0) : centralMoment 0 p μ = 0 := by
  simp only [centralMoment, hp, Pi.zero_apply, integral_const, smul_eq_mul,
    mul_zero, zero_sub, Pi.pow_apply, Pi.neg_apply, neg_zero, zero_pow, Ne, not_false_iff]
/-
**ProbabilityTheory.moment_one** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：moment_one (X : Ω -> Real) (μ : Measure Ω) : moment X 1 μ = μ[X]
参数：X : Ω -> Real；μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma moment_one (X : Ω → ℝ) (μ : Measure Ω) :
    moment X 1 μ = μ[X] := by simp [moment]

@[simp]
/-
**ProbabilityTheory.centralMoment_zero_measure** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：centralMoment_zero_measure : centralMoment X p (0 : Measure Ω) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma centralMoment_zero_measure : centralMoment X p (0 : Measure Ω) = 0 := by
  simp [centralMoment]
/-
**ProbabilityTheory.centralMoment_one'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：centralMoment_one' [IsFiniteMeasure μ] (h_int : Integrable X μ) : centralM
oment X 1 μ = (1 - μ.real Set.univ) * μ[X]
参数：h_int : Integrable X μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem centralMoment_one' [IsFiniteMeasure μ] (h_int : Integrable X μ) :
    centralMoment X 1 μ = (1 - μ.real Set.univ) * μ[X] := by
  simp only [centralMoment, Pi.sub_apply, pow_one]
  rw [integral_sub h_int (integrable_const _)]
  simp only [sub_mul, integral_const, smul_eq_mul, one_mul]

@[simp]
/-
**ProbabilityTheory.centralMoment_one** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：centralMoment_one [IsZeroOrProbabilityMeasure μ] : centralMoment X 1 μ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.eq_zero_or_isProbabilityMeasure`：eq_zero_or_isProbabilityM
easure : μ = 0 ∨ IsProbabilityMeasure μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.centralMoment_one'`：centralMoment_one' [IsFiniteMeasur
e μ] (h_int : Integrable X μ) : centralMoment X 1 μ = (1 - μ.real Set.univ) * μ[
X]
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
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
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
-/
theorem centralMoment_one [IsZeroOrProbabilityMeasure μ] : centralMoment X 1 μ = 0 := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp [centralMoment]
  by_cases h_int : Integrable X μ
  · rw [centralMoment_one' h_int]
    simp
  · simp only [centralMoment, Pi.sub_apply, pow_one]
    have : ¬Integrable (fun x => X x - integral μ X) μ := by
      refine fun h_sub => h_int ?_
      have h_add : X = (fun x => X x - integral μ X) + fun _ => integral μ X := by ext1 x; simp
      rw [h_add]
      fun_prop
    rw [integral_undef this]
/-
**ProbabilityTheory.centralMoment_two_eq_variance** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：centralMoment_two_eq_variance (hX : AEMeasurable X μ) : centralMoment X 2 
μ = variance X μ
参数：hX : AEMeasurable X μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.variance_eq_integral`：variance_eq_integral (hX : AEMea
surable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ
-/
lemma centralMoment_two_eq_variance (hX : AEMeasurable X μ) : centralMoment X 2 μ = variance X μ :=
  (variance_eq_integral hX).symm

/-- Central moments are equal for almost-everywhere equal random variables. -/
/-
**ProbabilityTheory.centralMoment_congr_ae** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：centralMoment_congr_ae {X Y : Ω -> Real} (hXY : X =ᵐ[μ] Y) : centralMoment
 X p μ = centralMoment Y p μ
参数：hXY : X =ᵐ[μ] Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Central moments are equal for almost-everywhere equal random variables.
-/
lemma centralMoment_congr_ae {X Y : Ω → ℝ} (hXY : X =ᵐ[μ] Y) :
    centralMoment X p μ = centralMoment Y p μ := by
  simp only [centralMoment, integral_congr_ae hXY]
  refine integral_congr_ae ?_
  filter_upwards [hXY] with x hx using by simp [hx]

section MomentGeneratingFunction

variable {t : ℝ}

/-- Moment-generating function of a real random variable `X`: `fun t => μ[exp(t*X)]`. -/
/-
**ProbabilityTheory.mgf** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf (X : Ω -> Real) (μ : Measure Ω) (t : Real) : Real
参数：X : Ω -> Real；μ : Measure Ω；t : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Moment-generating function of a real random variable `X`: `fun t => μ[exp(t*X)]`
.
-/
def mgf (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  μ[fun ω => exp (t * X ω)]

/-- Cumulant-generating function of a real random variable `X`: `fun t => log μ[exp(t*X)]`. -/
/-
**ProbabilityTheory.cgf** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：cgf (X : Ω -> Real) (μ : Measure Ω) (t : Real) : Real
参数：X : Ω -> Real；μ : Measure Ω；t : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cumulant-generating function of a real random variable `X`: `fun t => log μ[exp(
t*X)]`.
-/
def cgf (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  log (mgf X μ t)

@[simp]
/-
**ProbabilityTheory.mgf_zero_fun** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_zero_fun : mgf 0 μ t = μ.real Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mgf_zero_fun : mgf 0 μ t = μ.real Set.univ := by
  simp only [mgf, Pi.zero_apply, mul_zero, exp_zero, integral_const, smul_eq_mul, mul_one]

@[simp]
/-
**ProbabilityTheory.cgf_zero_fun** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：cgf_zero_fun : cgf 0 μ t = log (μ.real Set.univ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf_zero_fun`：mgf_zero_fun : mgf 0 μ t = μ.real Set.un
iv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cgf_zero_fun : cgf 0 μ t = log (μ.real Set.univ) := by simp only [cgf, mgf_zero_fun]

@[simp]
/-
**ProbabilityTheory.mgf_zero_measure** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：mgf_zero_measure : mgf X (0 : Measure Ω) = 0
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
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mgf_zero_measure : mgf X (0 : Measure Ω) = 0 := by ext; simp [mgf]

@[simp]
/-
**ProbabilityTheory.cgf_zero_measure** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：cgf_zero_measure : cgf X (0 : Measure Ω) = 0
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
· 使用定理 `ProbabilityTheory.mgf_zero_measure`：mgf_zero_measure : mgf X (0 : Measur
e Ω) = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cgf_zero_measure : cgf X (0 : Measure Ω) = 0 := by ext; simp [cgf]

@[simp]
/-
**ProbabilityTheory.mgf_const'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_const' (c : Real) : mgf (fun _ => c) μ t = μ.real Set.univ * exp (t * 
c)
参数：c : Real。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mgf_const' (c : ℝ) : mgf (fun _ => c) μ t = μ.real Set.univ * exp (t * c) := by
  simp only [mgf, integral_const, smul_eq_mul]
/-
**ProbabilityTheory.mgf_const** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_const (c : Real) [IsProbabilityMeasure μ] : mgf (fun _ => c) μ t = exp
 (t * c)
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf_const'`：mgf_const' (c : Real) : mgf (fun _ => c) μ
 t = μ.real Set.univ * exp (t * c)
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mgf_const (c : ℝ) [IsProbabilityMeasure μ] : mgf (fun _ => c) μ t = exp (t * c) := by
  simp

@[simp]
/-
**ProbabilityTheory.cgf_const'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：cgf_const' [IsFiniteMeasure μ] (hμ : μ != 0) (c : Real) : cgf (fun _ => c)
 μ t = log (μ.real Set.univ) + t * c
参数：hμ : μ != 0；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf_const'`：mgf_const' (c : Real) : mgf (fun _ => c) μ
 t = μ.real Set.univ * exp (t * c)
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `MeasureTheory.measureReal_eq_zero_iff`：measureReal_eq_zero_iff (h : μ s 
!= ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
-/
theorem cgf_const' [IsFiniteMeasure μ] (hμ : μ ≠ 0) (c : ℝ) :
    cgf (fun _ => c) μ t = log (μ.real Set.univ) + t * c := by
  simp only [cgf, mgf_const']
  rw [log_mul _ (exp_pos _).ne']
  · rw [log_exp _]
  · rw [Ne, measureReal_eq_zero_iff, Measure.measure_univ_eq_zero]
    simp only [hμ, not_false_iff]

@[simp]
/-
**ProbabilityTheory.cgf_const** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：cgf_const [IsProbabilityMeasure μ] (c : Real) : cgf (fun _ => c) μ t = t *
 c
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf_const`：mgf_const (c : Real) [IsProbabilityMeasure 
μ] : mgf (fun _ => c) μ t = exp (t * c)
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cgf_const [IsProbabilityMeasure μ] (c : ℝ) : cgf (fun _ => c) μ t = t * c := by
  simp only [cgf, mgf_const, log_exp]

@[simp]
/-
**ProbabilityTheory.mgf_zero'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_zero' : mgf X μ 0 = μ.real Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mgf_zero' : mgf X μ 0 = μ.real Set.univ := by
  simp only [mgf, zero_mul, exp_zero, integral_const, smul_eq_mul, mul_one]
/-
**ProbabilityTheory.mgf_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_zero [IsProbabilityMeasure μ] : mgf X μ 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf_zero'`：mgf_zero' : mgf X μ 0 = μ.real Set.univ
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mgf_zero [IsProbabilityMeasure μ] : mgf X μ 0 = 1 := by
  simp [mgf_zero']
/-
**ProbabilityTheory.cgf_zero'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：cgf_zero' : cgf X μ 0 = log (μ.real Set.univ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf_zero'`：mgf_zero' : mgf X μ 0 = μ.real Set.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cgf_zero' : cgf X μ 0 = log (μ.real Set.univ) := by simp only [cgf, mgf_zero']

@[simp]
/-
**ProbabilityTheory.cgf_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：cgf_zero [IsZeroOrProbabilityMeasure μ] : cgf X μ 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.eq_zero_or_isProbabilityMeasure`：eq_zero_or_isProbabilityM
easure : μ = 0 ∨ IsProbabilityMeasure μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cgf_zero'`：cgf_zero' : cgf X μ 0 = log (μ.real Set.uni
v)
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
-/
theorem cgf_zero [IsZeroOrProbabilityMeasure μ] : cgf X μ 0 = 0 := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h <;> simp [cgf_zero']
/-
**ProbabilityTheory.mgf_undef** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_undef (hX : ¬Integrable (fun ω => exp (t * X ω)) μ) : mgf X μ t = 0
参数：hX : ¬Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mgf_undef (hX : ¬Integrable (fun ω => exp (t * X ω)) μ) : mgf X μ t = 0 := by
  simp only [mgf, integral_undef hX]
/-
**ProbabilityTheory.cgf_undef** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：cgf_undef (hX : ¬Integrable (fun ω => exp (t * X ω)) μ) : cgf X μ t = 0
参数：hX : ¬Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf_undef`：mgf_undef (hX : ¬Integrable (fun ω => exp (
t * X ω)) μ) : mgf X μ t = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cgf_undef (hX : ¬Integrable (fun ω => exp (t * X ω)) μ) : cgf X μ t = 0 := by
  simp only [cgf, mgf_undef hX, log_zero]
/-
**ProbabilityTheory.mgf_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_nonneg : 0 <= mgf X μ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
-/
theorem mgf_nonneg : 0 ≤ mgf X μ t := by
  unfold mgf; positivity
/-
**ProbabilityTheory.mgf_pos'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_pos' (hμ : μ != 0) (h_int_X : Integrable (fun ω => exp (t * X ω)) μ) :
 0 < mgf X μ t
参数：hμ : μ != 0；h_int_X : Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae`：setIntegral_pos_
iff_support_of_nonneg_ae {f : X -> Real} (hf : 0 <=ᵐ[μ.restrict s] f) (hfi : Int
egrableOn f s μ) : (0 < ∫ x in s, f x ∂μ) ↔ …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `MeasureTheory.integrableOn_univ`：integrableOn_univ : IntegrableOn f univ
 μ ↔ Integrable f μ
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem mgf_pos' (hμ : μ ≠ 0) (h_int_X : Integrable (fun ω => exp (t * X ω)) μ) :
    0 < mgf X μ t := by
  simp_rw [mgf]
  have : ∫ x : Ω, exp (t * X x) ∂μ = ∫ x : Ω in Set.univ, exp (t * X x) ∂μ := by
    simp only [Measure.restrict_univ]
  rw [this, setIntegral_pos_iff_support_of_nonneg_ae _ _]
  · have h_eq_univ : (Function.support fun x : Ω => exp (t * X x)) = Set.univ := by
      ext1 x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (exp_pos _).ne'
    rw [h_eq_univ, Set.inter_univ _]
    refine Ne.bot_lt ?_
    simp only [hμ, ENNReal.bot_eq_zero, Ne, Measure.measure_univ_eq_zero, not_false_iff]
  · filter_upwards with x
    rw [Pi.zero_apply]
    exact (exp_pos _).le
  · rwa [integrableOn_univ]
/-
**ProbabilityTheory.mgf_pos** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_pos [IsProbabilityMeasure μ] (h_int_X : Integrable (fun ω => exp (t * 
X ω)) μ) : 0 < mgf X μ t
参数：h_int_X : Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.mgf_pos'`：mgf_pos' (hμ : μ != 0) (h_int_X : Integrable
 (fun ω => exp (t * X ω)) μ) : 0 < mgf X μ t
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0
-/
theorem mgf_pos [IsProbabilityMeasure μ] (h_int_X : Integrable (fun ω => exp (t * X ω)) μ) :
    0 < mgf X μ t :=
  mgf_pos' (IsProbabilityMeasure.ne_zero μ) h_int_X
/-
**ProbabilityTheory.mgf_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_pos_iff [hμ : NeZero μ] : 0 < mgf X μ t ↔ Integrable (fun ω => exp (t 
* X ω)) μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf_undef`：mgf_undef (hX : ¬Integrable (fun ω => exp (
t * X ω)) μ) : mgf X μ t = 0
· 使用定理 `ProbabilityTheory.mgf_pos'`：mgf_pos' (hμ : μ != 0) (h_int_X : Integrable
 (fun ω => exp (t * X ω)) μ) : 0 < mgf X μ t
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
-/
lemma mgf_pos_iff [hμ : NeZero μ] :
    0 < mgf X μ t ↔ Integrable (fun ω ↦ exp (t * X ω)) μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ mgf_pos' hμ.out h⟩
  contrapose! h with h
  simp [mgf_undef h]
/-
**ProbabilityTheory.exp_cgf** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：exp_cgf [hμ : NeZero μ] (hX : Integrable (fun ω => exp (t * X ω)) μ) : exp
 (cgf X μ t) = mgf X μ t
参数：hX : Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.cgf.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (X 
: Ω → ℝ) (μ : MeasureTheory.Measure Ω) (t : ℝ),   ProbabilityTheory.cgf X μ t = 
Real.log (Probab…
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `ProbabilityTheory.mgf_pos'`：mgf_pos' (hμ : μ != 0) (h_int_X : Integrable
 (fun ω => exp (t * X ω)) μ) : 0 < mgf X μ t
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
-/
lemma exp_cgf [hμ : NeZero μ] (hX : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    exp (cgf X μ t) = mgf X μ t := by rw [cgf, exp_log (mgf_pos' hμ.out hX)]
/-
**ProbabilityTheory.mgf_map** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {Y : Ω' -
> Ω} {X : Ω -> Real} (hY : AEMeasurable Y μ) {t : Real} (hX : AEStronglyMeasurab
le (fun ω => exp (t * X ω)) (μ.map Y)) : mgf X (μ.map Y) t = mgf (X ∘ Y) μ t
参数：hY : AEMeasurable Y μ；hX : AEStronglyMeasurable (fun ω => exp (t * X ω)) (μ.m
ap Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mgf_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {Y : Ω' → Ω} {X : Ω → ℝ}
    (hY : AEMeasurable Y μ) {t : ℝ} (hX : AEStronglyMeasurable (fun ω ↦ exp (t * X ω)) (μ.map Y)) :
    mgf X (μ.map Y) t = mgf (X ∘ Y) μ t := by
  simp_rw [mgf, integral_map hY hX, Function.comp_apply]
/-
**ProbabilityTheory.mgf_id_map** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_id_map (hX : AEMeasurable X μ) : mgf id (μ.map X) = mgf X μ
参数：hX : AEMeasurable X μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.mgf_map`：mgf_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω
'} {μ : Measure Ω'} {Y : Ω' -> Ω} {X : Ω -> Real} (hY : AEMeasurable Y μ) {t : R
eal} (hX : AESt…
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.exp`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Me
asurable f → Measurable fun x => Real.exp (f x)
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
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
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
-/
lemma mgf_id_map (hX : AEMeasurable X μ) : mgf id (μ.map X) = mgf X μ := by
  ext t
  rw [mgf_map hX, Function.id_comp]
  exact (measurable_const_mul _).exp.aestronglyMeasurable
/-
**ProbabilityTheory.mgf_congr** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_congr {Y : Ω -> Real} (h : X =ᵐ[μ] Y) : mgf X μ t = mgf Y μ t
参数：h : X =ᵐ[μ] Y。
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
-/
lemma mgf_congr {Y : Ω → ℝ} (h : X =ᵐ[μ] Y) : mgf X μ t = mgf Y μ t :=
  integral_congr_ae <| by filter_upwards [h] with ω hω using by rw [hω]
/-
**ProbabilityTheory.mgf_congr_identDistrib** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：mgf_congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measu
re Ω'} {Y : Ω' -> Real} (h : IdentDistrib X Y μ μ') : mgf X μ = mgf Y μ'
参数：h : IdentDistrib X Y μ μ'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.mgf_id_map`：mgf_id_map (hX : AEMeasurable X μ) : mgf i
d (μ.map X) = mgf X μ
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_fst`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `ProbabilityTheory.IdentDistrib.aemeasurable_snd`：∀ {α : Type u_1} {β : T
ype u_2} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] 
  [inst_2 : MeasurableSpace γ] {f : α…
· 使用定理 `ProbabilityTheory.IdentDistrib.map_eq`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {f : α…
-/
lemma mgf_congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {Y : Ω' → ℝ} (h : IdentDistrib X Y μ μ') :
    mgf X μ = mgf Y μ' := by
  rw [← mgf_id_map h.aemeasurable_fst, ← mgf_id_map h.aemeasurable_snd, h.map_eq]
/-
**ProbabilityTheory.mgf_neg** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_neg : mgf (-X) μ t = mgf X μ (-t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mgf_neg : mgf (-X) μ t = mgf X μ (-t) := by simp_rw [mgf, Pi.neg_apply, mul_neg, neg_mul]
/-
**ProbabilityTheory.cgf_neg** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：cgf_neg : cgf (-X) μ t = cgf X μ (-t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf_neg`：mgf_neg : mgf (-X) μ t = mgf X μ (-t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cgf_neg : cgf (-X) μ t = cgf X μ (-t) := by simp_rw [cgf, mgf_neg]
/-
**ProbabilityTheory.mgf_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_smul_left (α : Real) : mgf (α • X) μ t = mgf X μ (α * t)
参数：α : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mgf_smul_left (α : ℝ) : mgf (α • X) μ t = mgf X μ (α * t) := by
  simp_rw [mgf, Pi.smul_apply, smul_eq_mul, mul_comm α t, mul_assoc]
/-
**ProbabilityTheory.mgf_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_const_mul (α : Real) : mgf (fun ω => α * X ω) μ t = mgf X μ (α * t)
参数：α : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.mgf_smul_left`：mgf_smul_left (α : Real) : mgf (α • X) 
μ t = mgf X μ (α * t)
-/
theorem mgf_const_mul (α : ℝ) : mgf (fun ω ↦ α * X ω) μ t = mgf X μ (α * t) := mgf_smul_left α
/-
**ProbabilityTheory.mgf_const_add** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_const_add (α : Real) : mgf (fun ω => α + X ω) μ t = exp (t * α) * mgf 
X μ t
参数：α : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (X 
: Ω → ℝ) (μ : MeasureTheory.Measure Ω) (t : ℝ),   ProbabilityTheory.mgf X μ t = 
∫ (x : Ω), (fun …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
-/
theorem mgf_const_add (α : ℝ) : mgf (fun ω => α + X ω) μ t = exp (t * α) * mgf X μ t := by
  rw [mgf, mgf, ← integral_const_mul]
  congr with x
  dsimp
  rw [mul_add, exp_add]
/-
**ProbabilityTheory.mgf_add_const** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_add_const (α : Real) : mgf (fun ω => X ω + α) μ t = mgf X μ t * exp (t
 * α)
参数：α : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ProbabilityTheory.mgf_const_add`：mgf_const_add (α : Real) : mgf (fun ω =
> α + X ω) μ t = exp (t * α) * mgf X μ t
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mgf_add_const (α : ℝ) : mgf (fun ω => X ω + α) μ t = mgf X μ t * exp (t * α) := by
  simp only [add_comm, mgf_const_add, mul_comm]
/-
**ProbabilityTheory.mgf_add_measure** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：mgf_add_measure {ν : Measure Ω} (hμ : Integrable (fun ω => exp (t * X ω)) 
μ) (hν : Integrable (fun ω => exp (t * X ω)) ν) : mgf X (μ + ν) t = mgf X μ t + 
mgf X ν t
参数：hμ : Integrable (fun ω => exp (t * X ω)) μ；hν : Integrable (fun ω => exp (t *
 X ω)) ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (X 
: Ω → ℝ) (μ : MeasureTheory.Measure Ω) (t : ℝ),   ProbabilityTheory.mgf X μ t = 
∫ (x : Ω), (fun …
· 使用定理 `MeasureTheory.integral_add_measure`：integral_add_measure {f : α -> G} (h
μ : Integrable f μ) (hν : Integrable f ν) : ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ 
x, f x ∂ν
-/
lemma mgf_add_measure {ν : Measure Ω}
    (hμ : Integrable (fun ω ↦ exp (t * X ω)) μ) (hν : Integrable (fun ω ↦ exp (t * X ω)) ν) :
    mgf X (μ + ν) t = mgf X μ t + mgf X ν t := by
  rw [mgf, integral_add_measure hμ hν, mgf, mgf]
/-
**ProbabilityTheory.mgf_sum_measure** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：mgf_sum_measure {ι : Type*} {μ : ι -> Measure Ω} (hμ : Integrable (fun ω =
> exp (t * X ω)) (Measure.sum μ)) : mgf X (Measure.sum μ) t = ∑' i, mgf X (μ i) 
t
参数：hμ : Integrable (fun ω => exp (t * X ω)) (Measure.sum μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_sum_measure`：integral_sum_measure (hf : Integrabl
e f (Measure.sum μ)) : ∫ x, f x ∂Measure.sum μ = ∑' i, ∫ x, f x ∂μ i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mgf_sum_measure {ι : Type*} {μ : ι → Measure Ω}
    (hμ : Integrable (fun ω ↦ exp (t * X ω)) (Measure.sum μ)) :
    mgf X (Measure.sum μ) t = ∑' i, mgf X (μ i) t := by
  simp_rw [mgf, integral_sum_measure hμ]
/-
**ProbabilityTheory.mgf_smul_measure** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：mgf_smul_measure (c : Real>=0∞) : mgf X (c • μ) t = c.toReal * mgf X μ t
参数：c : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (X 
: Ω → ℝ) (μ : MeasureTheory.Measure Ω) (t : ℝ),   ProbabilityTheory.mgf X μ t = 
∫ (x : Ω), (fun …
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
-/
lemma mgf_smul_measure (c : ℝ≥0∞) : mgf X (c • μ) t = c.toReal * mgf X μ t := by
  rw [mgf, integral_smul_measure, mgf, smul_eq_mul]

/-- The moment-generating function is monotone in the random variable for `t ≥ 0`. -/
/-
**ProbabilityTheory.mgf_mono_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：mgf_mono_of_nonneg {Y : Ω -> Real} (hXY : X <=ᵐ[μ] Y) (ht : 0 <= t) (htY :
 Integrable (fun ω => exp (t * Y ω)) μ) : mgf X μ t <= mgf Y μ t
参数：hXY : X <=ᵐ[μ] Y；ht : 0 <= t；htY : Integrable (fun ω => exp (t * Y ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.integral_mono_ae`：integral_mono_ae {f g : α -> E} (hf : In
tegrable f μ) (hg : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ x, f x ∂μ <= ∫ x, g x ∂
μ
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
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Real.exp_monotone`：exp_monotone : Monotone exp
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf_undef`：mgf_undef (hX : ¬Integrable (fun ω => exp (
t * X ω)) μ) : mgf X μ t = 0
· 使用定理 `ProbabilityTheory.mgf_nonneg`：mgf_nonneg : 0 <= mgf X μ t

--- 原说明 ---
The moment-generating function is monotone in the random variable for `t ≥ 0`.
-/
lemma mgf_mono_of_nonneg {Y : Ω → ℝ} (hXY : X ≤ᵐ[μ] Y) (ht : 0 ≤ t)
    (htY : Integrable (fun ω ↦ exp (t * Y ω)) μ) :
    mgf X μ t ≤ mgf Y μ t := by
  by_cases htX : Integrable (fun ω ↦ exp (t * X ω)) μ
  · refine integral_mono_ae htX htY ?_
    filter_upwards [hXY] with ω hω using by gcongr
  · rw [mgf_undef htX]
    exact mgf_nonneg

/-- The moment-generating function is antitone in the random variable for `t ≤ 0`. -/
/-
**ProbabilityTheory.mgf_anti_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：mgf_anti_of_nonpos {Y : Ω -> Real} (hXY : X <=ᵐ[μ] Y) (ht : t <= 0) (htX :
 Integrable (fun ω => exp (t * X ω)) μ) : mgf Y μ t <= mgf X μ t
参数：hXY : X <=ᵐ[μ] Y；ht : t <= 0；htX : Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.integral_mono_ae`：integral_mono_ae {f g : α -> E} (hf : In
tegrable f μ) (hg : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ x, f x ∂μ <= ∫ x, g x ∂
μ
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
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Real.exp_monotone`：exp_monotone : Monotone exp
· 使用定理 `mul_le_mul_of_nonpos_left`：mul_le_mul_of_nonpos_left [ExistsAddOfLE R] [
PosMulMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0) 
: c * a <= c * …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf_undef`：mgf_undef (hX : ¬Integrable (fun ω => exp (
t * X ω)) μ) : mgf X μ t = 0
· 使用定理 `ProbabilityTheory.mgf_nonneg`：mgf_nonneg : 0 <= mgf X μ t

--- 原说明 ---
The moment-generating function is antitone in the random variable for `t ≤ 0`.
-/
lemma mgf_anti_of_nonpos {Y : Ω → ℝ} (hXY : X ≤ᵐ[μ] Y) (ht : t ≤ 0)
    (htX : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    mgf Y μ t ≤ mgf X μ t := by
  by_cases htY : Integrable (fun ω ↦ exp (t * Y ω)) μ
  · refine integral_mono_ae htY htX ?_
    filter_upwards [hXY] with ω hω using exp_monotone <| mul_le_mul_of_nonpos_left hω ht
  · rw [mgf_undef htY]
    exact mgf_nonneg

section IndepFun

/-- This is a trivial application of `IndepFun.comp` but it will come up frequently. -/
/-
**ProbabilityTheory.IndepFun.exp_mul** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {X 
Y : Ω → ℝ},   ProbabilityTheory.IndepFun X Y μ →     ∀ (s t : ℝ), ProbabilityThe
ory.IndepFun (fun ω => Real.exp (s * X ω)) (fun ω => Real.exp (t * Y ω)) μ
参数：s t : ℝ；fun ω => Real.exp (s * X ω)；fun ω => Real.exp (t * Y ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.exp`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Me
asurable f → Measurable fun x => Real.exp (f x)
· 使用定理 `Measurable.const_mul`：Measurable.const_mul [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => c * f x
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
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `ProbabilityTheory.IndepFun.comp`：∀ {Ω : Type u_1} {β : Type u_6} {β' : T
ype u_7} {γ : Type u_8} {γ' : Type u_9} {_mΩ : MeasurableSpace Ω}   {μ : Measure
Theory.Measure Ω} {f …

--- 原说明 ---
This is a trivial application of `IndepFun.comp` but it will come up frequently.
-/
theorem IndepFun.exp_mul {X Y : Ω → ℝ} (h_indep : X ⟂ᵢ[μ] Y) (s t : ℝ) :
    (fun ω => exp (s * X ω)) ⟂ᵢ[μ] (fun ω => exp (t * Y ω)) := by
  have h_meas : ∀ t, Measurable fun x => exp (t * x) := fun t => (measurable_id'.const_mul t).exp
  change IndepFun ((fun x => exp (s * x)) ∘ X) ((fun x => exp (t * x)) ∘ Y) μ
  exact IndepFun.comp h_indep (h_meas s) (h_meas t)
/-
**ProbabilityTheory.IndepFun.mgf_add** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {t 
: ℝ} {X Y : Ω → ℝ},   ProbabilityTheory.IndepFun X Y μ →     MeasureTheory.AEStr
onglyMeasurable (fun ω => Real.exp (t * X ω)) μ →       MeasureTheory.AEStrongly
Measurable (fun ω => Real.exp (t * Y ω)) μ →         ProbabilityTheory.mgf (X + 
Y) μ t = ProbabilityTheory.mgf X μ t * ProbabilityTheory.mgf Y μ t
参数：fun ω => Real.exp (t * X ω)；fun ω => Real.exp (t * Y ω)；X + Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral`：∀ {Ω : Type u_1
} {𝕜 : Type u_2} [inst : RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.M
easure Ω} {X Y : Ω → 𝕜},   ProbabilityTheory.…
· 使用定理 `ProbabilityTheory.IndepFun.exp_mul`：∀ {Ω : Type u_1} {m : MeasurableSpac
e Ω} {μ : MeasureTheory.Measure Ω} {X Y : Ω → ℝ},   ProbabilityTheory.IndepFun X
 Y μ →     ∀ (s t : ℝ), …
-/
theorem IndepFun.mgf_add {X Y : Ω → ℝ} (h_indep : X ⟂ᵢ[μ] Y)
    (hX : AEStronglyMeasurable (fun ω => exp (t * X ω)) μ)
    (hY : AEStronglyMeasurable (fun ω => exp (t * Y ω)) μ) :
    mgf (X + Y) μ t = mgf X μ t * mgf Y μ t := by
  simp_rw [mgf, Pi.add_apply, mul_add, exp_add]
  exact (h_indep.exp_mul t t).integral_mul_eq_mul_integral hX hY
/-
**ProbabilityTheory.IndepFun.mgf_add'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {t 
: ℝ} {X Y : Ω → ℝ},   ProbabilityTheory.IndepFun X Y μ →     MeasureTheory.AEStr
onglyMeasurable X μ →       MeasureTheory.AEStronglyMeasurable Y μ →         Pro
babilityTheory.mgf (X + Y) μ t = ProbabilityTheory.mgf X μ t * ProbabilityTheory
.mgf Y μ t
参数：X + Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.rexp`：Continuous.rexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
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
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_aemeasurable`：comp_aemeasurable 
{γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α} {μ : Me
asure γ} (hg : AEStronglyMeasurable g (Mea…
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
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `ProbabilityTheory.IndepFun.mgf_add`：∀ {Ω : Type u_1} {m : MeasurableSpac
e Ω} {μ : MeasureTheory.Measure Ω} {t : ℝ} {X Y : Ω → ℝ},   ProbabilityTheory.In
depFun X Y μ →     Measu…
-/
theorem IndepFun.mgf_add' {X Y : Ω → ℝ} (h_indep : X ⟂ᵢ[μ] Y) (hX : AEStronglyMeasurable X μ)
    (hY : AEStronglyMeasurable Y μ) : mgf (X + Y) μ t = mgf X μ t * mgf Y μ t := by
  have A : Continuous fun x : ℝ => exp (t * x) := by fun_prop
  have h'X : AEStronglyMeasurable (fun ω => exp (t * X ω)) μ :=
    A.aestronglyMeasurable.comp_aemeasurable hX.aemeasurable
  have h'Y : AEStronglyMeasurable (fun ω => exp (t * Y ω)) μ :=
    A.aestronglyMeasurable.comp_aemeasurable hY.aemeasurable
  exact h_indep.mgf_add h'X h'Y
/-
**ProbabilityTheory.IndepFun.cgf_add** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {t 
: ℝ} {X Y : Ω → ℝ},   ProbabilityTheory.IndepFun X Y μ →     MeasureTheory.Integ
rable (fun ω => Real.exp (t * X ω)) μ →       MeasureTheory.Integrable (fun ω =>
 Real.exp (t * Y ω)) μ →         ProbabilityTheory.cgf (X + Y) μ t = Probability
Theory.cgf X μ t + ProbabilityTheory.cgf Y μ t
参数：fun ω => Real.exp (t * X ω)；fun ω => Real.exp (t * Y ω)；X + Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ProbabilityTheory.cgf_zero_measure`：cgf_zero_measure : cgf X (0 : Measur
e Ω) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.IndepFun.mgf_add`：∀ {Ω : Type u_1} {m : MeasurableSpac
e Ω} {μ : MeasureTheory.Measure Ω} {t : ℝ} {X Y : Ω → ℝ},   ProbabilityTheory.In
depFun X Y μ →     Measu…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ProbabilityTheory.mgf_pos'`：mgf_pos' (hμ : μ != 0) (h_int_X : Integrable
 (fun ω => exp (t * X ω)) μ) : 0 < mgf X μ t
-/
theorem IndepFun.cgf_add {X Y : Ω → ℝ} (h_indep : X ⟂ᵢ[μ] Y)
    (h_int_X : Integrable (fun ω => exp (t * X ω)) μ)
    (h_int_Y : Integrable (fun ω => exp (t * Y ω)) μ) :
    cgf (X + Y) μ t = cgf X μ t + cgf Y μ t := by
  by_cases hμ : μ = 0
  · simp [hμ]
  simp only [cgf, h_indep.mgf_add h_int_X.aestronglyMeasurable h_int_Y.aestronglyMeasurable]
  exact log_mul (mgf_pos' hμ h_int_X).ne' (mgf_pos' hμ h_int_Y).ne'
/-
**ProbabilityTheory.aestronglyMeasurable_exp_mul_add** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：aestronglyMeasurable_exp_mul_add {X Y : Ω -> Real} (h_int_X : AEStronglyMe
asurable (fun ω => exp (t * X ω)) μ) (h_int_Y : AEStronglyMeasurable (fun ω => e
xp (t * Y ω)) μ) : AEStronglyMeasurable (fun ω => exp (t * (X + Y) ω)) μ
参数：h_int_X : AEStronglyMeasurable (fun ω => exp (t * X ω)) μ；h_int_Y : AEStrongl
yMeasurable (fun ω => exp (t * Y ω)) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
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
-/
theorem aestronglyMeasurable_exp_mul_add {X Y : Ω → ℝ}
    (h_int_X : AEStronglyMeasurable (fun ω => exp (t * X ω)) μ)
    (h_int_Y : AEStronglyMeasurable (fun ω => exp (t * Y ω)) μ) :
    AEStronglyMeasurable (fun ω => exp (t * (X + Y) ω)) μ := by
  simp_rw [Pi.add_apply, mul_add, exp_add]
  exact AEStronglyMeasurable.mul h_int_X h_int_Y
/-
**ProbabilityTheory.aestronglyMeasurable_exp_mul_sum** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：aestronglyMeasurable_exp_mul_sum {X : ι -> Ω -> Real} {s : Finset ι} (h_in
t : forall i in s, AEStronglyMeasurable (fun ω => exp (t * X i ω)) μ) : AEStrong
lyMeasurable (fun ω => exp (t * (∑ i in s, X i) ω)) μ
参数：h_int : forall i in s, AEStronglyMeasurable (fun ω => exp (t * X i ω)) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `ProbabilityTheory.aestronglyMeasurable_exp_mul_add`：aestronglyMeasurable
_exp_mul_add {X Y : Ω -> Real} (h_int_X : AEStronglyMeasurable (fun ω => exp (t 
* X ω)) μ) (h_int_Y : AEStronglyMeasurab…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
-/
theorem aestronglyMeasurable_exp_mul_sum {X : ι → Ω → ℝ} {s : Finset ι}
    (h_int : ∀ i ∈ s, AEStronglyMeasurable (fun ω => exp (t * X i ω)) μ) :
    AEStronglyMeasurable (fun ω => exp (t * (∑ i ∈ s, X i) ω)) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_apply, sum_empty, mul_zero, exp_zero]
    exact aestronglyMeasurable_const
  | insert i s hi_notin_s h_rec =>
    have : ∀ i : ι, i ∈ s → AEStronglyMeasurable (fun ω : Ω => exp (t * X i ω)) μ := fun i hi =>
      h_int i (mem_insert_of_mem hi)
    specialize h_rec this
    rw [sum_insert hi_notin_s]
    apply aestronglyMeasurable_exp_mul_add (h_int i (mem_insert_self _ _)) h_rec
/-
**ProbabilityTheory.IndepFun.integrable_exp_mul_add** 是 Mathlib 中的一个定理，位于命名空间 `P
robabilityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {t 
: ℝ} {X Y : Ω → ℝ},   ProbabilityTheory.IndepFun X Y μ →     MeasureTheory.Integ
rable (fun ω => Real.exp (t * X ω)) μ →       MeasureTheory.Integrable (fun ω =>
 Real.exp (t * Y ω)) μ →         MeasureTheory.Integrable (fun ω => Real.exp (t 
* (X + Y) ω)) μ
参数：fun ω => Real.exp (t * X ω)；fun ω => Real.exp (t * Y ω)；fun ω => Real.exp (t 
* (X + Y) ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `ProbabilityTheory.IndepFun.integrable_mul`：∀ {Ω : Type u_1} {mΩ : Measur
ableSpace Ω} {μ : MeasureTheory.Measure Ω} {E : Type u_5} [inst : TopologicalSpa
ce E]   [inst_1 : ContinuousENo…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instENormSMulClass`：∀ {α : Type u_1} {β : Type u_2} [inst : SeminormedRi
ng α] [inst_1 : SeminormedAddGroup β] [inst_2 : SMul α β]   [NormSMulClass α β],
 ENormSM…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ProbabilityTheory.IndepFun.exp_mul`：∀ {Ω : Type u_1} {m : MeasurableSpac
e Ω} {μ : MeasureTheory.Measure Ω} {X Y : Ω → ℝ},   ProbabilityTheory.IndepFun X
 Y μ →     ∀ (s t : ℝ), …
-/
theorem IndepFun.integrable_exp_mul_add {X Y : Ω → ℝ} (h_indep : X ⟂ᵢ[μ] Y)
    (h_int_X : Integrable (fun ω => exp (t * X ω)) μ)
    (h_int_Y : Integrable (fun ω => exp (t * Y ω)) μ) :
    Integrable (fun ω => exp (t * (X + Y) ω)) μ := by
  simp_rw [Pi.add_apply, mul_add, exp_add]
  exact (h_indep.exp_mul t t).integrable_mul h_int_X h_int_Y
/-
**ProbabilityTheory.iIndepFun.integrable_exp_mul_sum** 是 Mathlib 中的一个定理，位于命名空间 `
ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} {μ : MeasureTheory
.Measure Ω} {t : ℝ}   [MeasureTheory.IsFiniteMeasure μ] {X : ι → Ω → ℝ},   Proba
bilityTheory.iIndepFun X μ →     (∀ (i : ι), Measurable (X i)) →       ∀ {s : Fi
nset ι},         (∀ i ∈ s, MeasureTheory.Integrable (fun ω => Real.exp (t * X i 
ω)) μ) →           MeasureTheory.Integrable (fun ω => Real.exp (t * (∑ i ∈ s, X 
i) ω)) μ
参数：∀ (i : ι), Measurable (X i)；∀ i ∈ s, MeasureTheory.Integrable (fun ω => Real.
exp (t * X i ω)) μ；fun ω => Real.exp (t * (∑ i ∈ s, X i) ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `ProbabilityTheory.IndepFun.integrable_exp_mul_add`：∀ {Ω : Type u_1} {m :
 MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {t : ℝ} {X Y : Ω → ℝ},   Proba
bilityTheory.IndepFun X Y μ →     Measu…
· 使用定理 `ProbabilityTheory.IndepFun.symm`：∀ {Ω : Type u_1} {β : Type u_6} {β' : T
ype u_7} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {f : Ω → β}   {
g : Ω → β'} {x : Meas…
· 使用定理 `ProbabilityTheory.iIndepFun.indepFun_finsetSum_of_notMem`：∀ {Ω : Type u_
1} {ι : Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : T
ype u_10}   {m : MeasurableSpace β} [inst : Ad…
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
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
-/
theorem iIndepFun.integrable_exp_mul_sum [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    {s : Finset ι} (h_int : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ) :
    Integrable (fun ω => exp (t * (∑ i ∈ s, X i) ω)) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_apply, sum_empty, mul_zero, exp_zero]
    exact integrable_const _
  | insert i s hi_notin_s h_rec =>
    have : ∀ i : ι, i ∈ s → Integrable (fun ω : Ω => exp (t * X i ω)) μ := fun i hi =>
      h_int i (mem_insert_of_mem hi)
    specialize h_rec this
    rw [sum_insert hi_notin_s]
    refine IndepFun.integrable_exp_mul_add ?_ (h_int i (mem_insert_self _ _)) h_rec
    exact (h_indep.indepFun_finsetSum_of_notMem h_meas hi_notin_s).symm
/-
**ProbabilityTheory.iIndepFun.mgf_sum** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} {μ : MeasureTheory
.Measure Ω} {t : ℝ} {X : ι → Ω → ℝ},   ProbabilityTheory.iIndepFun X μ →     (∀ 
(i : ι), Measurable (X i)) →       ∀ (s : Finset ι), ProbabilityTheory.mgf (∑ i 
∈ s, X i) μ t = ∏ i ∈ s, ProbabilityTheory.mgf (X i) μ t
参数：∀ (i : ι), Measurable (X i)；s : Finset ι；∑ i ∈ s, X i；X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.mgf_sum₀`：∀ {Ω : Type u_1} {ι : Type u_2} {m
 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {t : ℝ} {X : ι → Ω → ℝ},   P
robabilityTheory.iIndepFun…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem iIndepFun.mgf_sum₀ {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, AEMeasurable (X i) μ)
    (s : Finset ι) : mgf (∑ i ∈ s, X i) μ t = ∏ i ∈ s, mgf (X i) μ t := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi_notin_s h_rec =>
    have h_int' : ∀ i : ι, AEStronglyMeasurable (fun ω : Ω => exp (t * X i ω)) μ := fun i =>
      ((h_meas i).const_mul t).exp.aestronglyMeasurable
    rw [sum_insert hi_notin_s,
      IndepFun.mgf_add (h_indep.indepFun_finsetSum_of_notMem₀ h_meas hi_notin_s).symm (h_int' i)
        (aestronglyMeasurable_exp_mul_sum fun i _ => h_int' i),
      h_rec, prod_insert hi_notin_s]
/-
**ProbabilityTheory.iIndepFun.mgf_sum** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} {μ : MeasureTheory
.Measure Ω} {t : ℝ} {X : ι → Ω → ℝ},   ProbabilityTheory.iIndepFun X μ →     (∀ 
(i : ι), Measurable (X i)) →       ∀ (s : Finset ι), ProbabilityTheory.mgf (∑ i 
∈ s, X i) μ t = ∏ i ∈ s, ProbabilityTheory.mgf (X i) μ t
参数：∀ (i : ι), Measurable (X i)；s : Finset ι；∑ i ∈ s, X i；X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.mgf_sum₀`：∀ {Ω : Type u_1} {ι : Type u_2} {m
 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {t : ℝ} {X : ι → Ω → ℝ},   P
robabilityTheory.iIndepFun…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem iIndepFun.mgf_sum {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (s : Finset ι) : mgf (∑ i ∈ s, X i) μ t = ∏ i ∈ s, mgf (X i) μ t :=
  h_indep.mgf_sum₀ (by fun_prop) s
/-
**ProbabilityTheory.iIndepFun.cgf_sum** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} {μ : MeasureTheory
.Measure Ω} {t : ℝ} {X : ι → Ω → ℝ},   ProbabilityTheory.iIndepFun X μ →     (∀ 
(i : ι), Measurable (X i)) →       ∀ {s : Finset ι},         (∀ i ∈ s, MeasureTh
eory.Integrable (fun ω => Real.exp (t * X i ω)) μ) →           ProbabilityTheory
.cgf (∑ i ∈ s, X i) μ t = ∑ i ∈ s, ProbabilityTheory.cgf (X i) μ t
参数：∀ (i : ι), Measurable (X i)；∀ i ∈ s, MeasureTheory.Integrable (fun ω => Real.
exp (t * X i ω)) μ；∑ i ∈ s, X i；X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.cgf_sum₀`：∀ {Ω : Type u_1} {ι : Type u_2} {m
 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {t : ℝ} {X : ι → Ω → ℝ},   P
robabilityTheory.iIndepFun…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem iIndepFun.cgf_sum₀ {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, AEMeasurable (X i) μ)
    {s : Finset ι} (h_int : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ) :
    cgf (∑ i ∈ s, X i) μ t = ∑ i ∈ s, cgf (X i) μ t := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  simp_rw [cgf]
  rw [← log_prod fun j hj => ?_]
  · rw [h_indep.mgf_sum₀ h_meas]
  · exact (mgf_pos (h_int j hj)).ne'
/-
**ProbabilityTheory.iIndepFun.cgf_sum** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω} {μ : MeasureTheory
.Measure Ω} {t : ℝ} {X : ι → Ω → ℝ},   ProbabilityTheory.iIndepFun X μ →     (∀ 
(i : ι), Measurable (X i)) →       ∀ {s : Finset ι},         (∀ i ∈ s, MeasureTh
eory.Integrable (fun ω => Real.exp (t * X i ω)) μ) →           ProbabilityTheory
.cgf (∑ i ∈ s, X i) μ t = ∑ i ∈ s, ProbabilityTheory.cgf (X i) μ t
参数：∀ (i : ι), Measurable (X i)；∀ i ∈ s, MeasureTheory.Integrable (fun ω => Real.
exp (t * X i ω)) μ；∑ i ∈ s, X i；X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.cgf_sum₀`：∀ {Ω : Type u_1} {ι : Type u_2} {m
 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {t : ℝ} {X : ι → Ω → ℝ},   P
robabilityTheory.iIndepFun…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem iIndepFun.cgf_sum {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    {s : Finset ι} (h_int : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ) :
    cgf (∑ i ∈ s, X i) μ t = ∑ i ∈ s, cgf (X i) μ t :=
  h_indep.cgf_sum₀ (by fun_prop) h_int

end IndepFun

/-
**ProbabilityTheory.mgf_congr_of_identDistrib** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：mgf_congr_of_identDistrib (X : Ω -> Real) {Ω' : Type*} {m' : MeasurableSpa
ce Ω'} {μ' : Measure Ω'} (X' : Ω' -> Real) (hident : IdentDistrib X X' μ μ') (t 
: Real) : .integral_eq mgf X μ t = mgf X' μ' t
参数：X : Ω -> Real；X' : Ω' -> Real；hident : IdentDistrib X X' μ μ'；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IdentDistrib.integral_eq`：integral_eq [NormedAddCommGr
oup γ] [NormedSpace Real γ] [BorelSpace γ] (h : IdentDistrib f g μ ν) : ∫ x, f x
 ∂μ = ∫ x, g x ∂ν
· 使用定理 `ProbabilityTheory.IdentDistrib.comp`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} {δ : Type u_4} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace 
β]   [inst_2 : Measurable…
· 使用定理 `Measurable.exp`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Me
asurable f → Measurable fun x => Real.exp (f x)
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
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
-/
theorem mgf_congr_of_identDistrib
    (X : Ω → ℝ) {Ω' : Type*} {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} (X' : Ω' → ℝ)
    (hident : IdentDistrib X X' μ μ') (t : ℝ) :
    mgf X μ t = mgf X' μ' t := hident.comp (measurable_const_mul t).exp |>.integral_eq
/-
**ProbabilityTheory.mgf_sum_of_identDistrib** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：mgf_sum_of_identDistrib {X : ι -> Ω -> Real} {s : Finset ι} {j : ι} (h_mea
s : forall i, Measurable (X i)) (h_indep : iIndepFun X μ) (hident : forall i in 
s, forall j in s, IdentDistrib (X i) (X j) μ μ) (hj : j in s) (t : Real) : mgf (
∑ i in s, X i) μ t = mgf (X j) μ t ^ #s
参数：h_meas : forall i, Measurable (X i)；h_indep : iIndepFun X μ；hident : forall i
 in s, forall j in s, IdentDistrib (X i) (X j) μ μ；hj : j in s；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.mgf_sum_of_identDistrib₀`：mgf_sum_of_identDistrib₀ {X 
: ι -> Ω -> Real} {s : Finset ι} {j : ι} (h_meas : forall i, AEMeasurable (X i) 
μ) (h_indep : iIndepFun X μ) (hi…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem mgf_sum_of_identDistrib₀
    {X : ι → Ω → ℝ}
    {s : Finset ι} {j : ι}
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_indep : iIndepFun X μ)
    (hident : ∀ i ∈ s, ∀ j ∈ s, IdentDistrib (X i) (X j) μ μ)
    (hj : j ∈ s) (t : ℝ) : mgf (∑ i ∈ s, X i) μ t = mgf (X j) μ t ^ #s := by
  rw [h_indep.mgf_sum₀ h_meas]
  exact Finset.prod_eq_pow_card fun i hi =>
    mgf_congr_of_identDistrib (X i) (X j) (hident i hi j hj) t
/-
**ProbabilityTheory.mgf_sum_of_identDistrib** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：mgf_sum_of_identDistrib {X : ι -> Ω -> Real} {s : Finset ι} {j : ι} (h_mea
s : forall i, Measurable (X i)) (h_indep : iIndepFun X μ) (hident : forall i in 
s, forall j in s, IdentDistrib (X i) (X j) μ μ) (hj : j in s) (t : Real) : mgf (
∑ i in s, X i) μ t = mgf (X j) μ t ^ #s
参数：h_meas : forall i, Measurable (X i)；h_indep : iIndepFun X μ；hident : forall i
 in s, forall j in s, IdentDistrib (X i) (X j) μ μ；hj : j in s；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.mgf_sum_of_identDistrib₀`：mgf_sum_of_identDistrib₀ {X 
: ι -> Ω -> Real} {s : Finset ι} {j : ι} (h_meas : forall i, AEMeasurable (X i) 
μ) (h_indep : iIndepFun X μ) (hi…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem mgf_sum_of_identDistrib
    {X : ι → Ω → ℝ}
    {s : Finset ι} {j : ι}
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    (hident : ∀ i ∈ s, ∀ j ∈ s, IdentDistrib (X i) (X j) μ μ)
    (hj : j ∈ s) (t : ℝ) : mgf (∑ i ∈ s, X i) μ t = mgf (X j) μ t ^ #s :=
  mgf_sum_of_identDistrib₀ (by fun_prop) h_indep hident hj t

section Chernoff

/-- **Chernoff bound** on the upper tail of a real random variable. -/
/-
**ProbabilityTheory.measure_ge_le_exp_mul_mgf** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：measure_ge_le_exp_mul_mgf [IsFiniteMeasure μ] (ε : Real) (ht : 0 <= t) (h_
int : Integrable (fun ω => exp (t * X ω)) μ) : μ.real {ω | ε <= X ω} <= exp (-t 
* ε) * mgf X μ t
参数：ε : Real；ht : 0 <= t；h_int : Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `ProbabilityTheory.mgf_zero'`：mgf_zero' : mgf X μ 0 = μ.real Set.univ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.measureReal_mono`：∀ {α : Type u_1} {x : MeasurableSpace α}
 {μ : MeasureTheory.Measure α} {s₁ s₂ : Set α},   s₁ ⊆ s₂ → autoParam (μ s₂ ≠ ⊤)
 MeasureTheory.measu…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_of_mul_le_mul_left`：le_of_mul_le_mul_left [PosMulReflectLE α] (bc : a
 * b <= a * c) (a0 : 0 < a) : b <= c
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MeasureTheory.mul_meas_ge_le_integral_of_nonneg`：mul_meas_ge_le_integral
_of_nonneg {f : α -> Real} (hf_nonneg : 0 <=ᵐ[μ] f) (hf_int : Integrable f μ) (ε
 : Real) : ε * μ.real { x | ε <= f x …
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
**Chernoff bound** on the upper tail of a real random variable.
-/
theorem measure_ge_le_exp_mul_mgf [IsFiniteMeasure μ] (ε : ℝ) (ht : 0 ≤ t)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ exp (-t * ε) * mgf X μ t := by
  rcases ht.eq_or_lt with ht_zero_eq | ht_pos
  · rw [ht_zero_eq.symm]
    simp only [neg_zero, zero_mul, exp_zero, mgf_zero', one_mul]
    gcongr
    exacts [measure_ne_top _ _, Set.subset_univ _]
  calc
    μ.real {ω | ε ≤ X ω} = μ.real {ω | exp (t * ε) ≤ exp (t * X ω)} := by
      congr 1 with ω
      simp only [Set.mem_ofPred_eq, exp_le_exp]
      exact ⟨fun h => mul_le_mul_of_nonneg_left h ht_pos.le,
        fun h => le_of_mul_le_mul_left h ht_pos⟩
    _ ≤ (exp (t * ε))⁻¹ * μ[fun ω => exp (t * X ω)] := by
      have : exp (t * ε) * μ.real {ω | exp (t * ε) ≤ exp (t * X ω)} ≤
          μ[fun ω => exp (t * X ω)] :=
        mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => (exp_pos _).le) h_int _
      rwa [mul_comm (exp (t * ε))⁻¹, ← div_eq_mul_inv, le_div_iff₀' (exp_pos _)]
    _ = exp (-t * ε) * mgf X μ t := by rw [neg_mul, exp_neg]; rfl

/-- **Chernoff bound** on the lower tail of a real random variable. -/
/-
**ProbabilityTheory.measure_le_le_exp_mul_mgf** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：measure_le_le_exp_mul_mgf [IsFiniteMeasure μ] (ε : Real) (ht : t <= 0) (h_
int : Integrable (fun ω => exp (t * X ω)) μ) : μ.real {ω | X ω <= ε} <= exp (-t 
* ε) * mgf X μ t
参数：ε : Real；ht : t <= 0；h_int : Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `ProbabilityTheory.mgf_neg`：mgf_neg : mgf (-X) μ t = mgf X μ (-t)
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.measure_ge_le_exp_mul_mgf`：measure_ge_le_exp_mul_mgf [
IsFiniteMeasure μ] (ε : Real) (ht : 0 <= t) (h_int : Integrable (fun ω => exp (t
 * X ω)) μ) : μ.real {ω | ε <= X …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
**Chernoff bound** on the lower tail of a real random variable.
-/
theorem measure_le_le_exp_mul_mgf [IsFiniteMeasure μ] (ε : ℝ) (ht : t ≤ 0)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.real {ω | X ω ≤ ε} ≤ exp (-t * ε) * mgf X μ t := by
  rw [← neg_neg t, ← mgf_neg, neg_neg, ← neg_mul_neg (-t)]
  refine Eq.trans_le ?_ (measure_ge_le_exp_mul_mgf (-ε) (neg_nonneg.mpr ht) ?_)
  · simp only [Pi.neg_apply, neg_le_neg_iff]
  · simp_rw [Pi.neg_apply, neg_mul_neg]
    exact h_int

/-- **Chernoff bound** on the upper tail of a real random variable. -/
/-
**ProbabilityTheory.measure_ge_le_exp_cgf** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory`。
形式化陈述：measure_ge_le_exp_cgf [IsFiniteMeasure μ] (ε : Real) (ht : 0 <= t) (h_int 
: Integrable (fun ω => exp (t * X ω)) μ) : μ.real {ω | ε <= X ω} <= exp (-t * ε 
+ cgf X μ t)
参数：ε : Real；ht : 0 <= t；h_int : Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ProbabilityTheory.measure_ge_le_exp_mul_mgf`：measure_ge_le_exp_mul_mgf [
IsFiniteMeasure μ] (ε : Real) (ht : 0 <= t) (h_int : Integrable (fun ω => exp (t
 * X ω)) μ) : μ.real {ω | ε <= X …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Real.le_exp_log`：le_exp_log (x : Real) : x <= exp (log x)
· 使用定理 `ProbabilityTheory.mgf_nonneg`：mgf_nonneg : 0 <= mgf X μ t
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x

--- 原说明 ---
**Chernoff bound** on the upper tail of a real random variable.
-/
theorem measure_ge_le_exp_cgf [IsFiniteMeasure μ] (ε : ℝ) (ht : 0 ≤ t)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ exp (-t * ε + cgf X μ t) := by
  refine (measure_ge_le_exp_mul_mgf ε ht h_int).trans ?_
  rw [exp_add]
  exact mul_le_mul le_rfl (le_exp_log _) mgf_nonneg (exp_pos _).le

/-- **Chernoff bound** on the lower tail of a real random variable. -/
/-
**ProbabilityTheory.measure_le_le_exp_cgf** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory`。
形式化陈述：measure_le_le_exp_cgf [IsFiniteMeasure μ] (ε : Real) (ht : t <= 0) (h_int 
: Integrable (fun ω => exp (t * X ω)) μ) : μ.real {ω | X ω <= ε} <= exp (-t * ε 
+ cgf X μ t)
参数：ε : Real；ht : t <= 0；h_int : Integrable (fun ω => exp (t * X ω)) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ProbabilityTheory.measure_le_le_exp_mul_mgf`：measure_le_le_exp_mul_mgf [
IsFiniteMeasure μ] (ε : Real) (ht : t <= 0) (h_int : Integrable (fun ω => exp (t
 * X ω)) μ) : μ.real {ω | X ω <= …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Real.le_exp_log`：le_exp_log (x : Real) : x <= exp (log x)
· 使用定理 `ProbabilityTheory.mgf_nonneg`：mgf_nonneg : 0 <= mgf X μ t
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x

--- 原说明 ---
**Chernoff bound** on the lower tail of a real random variable.
-/
theorem measure_le_le_exp_cgf [IsFiniteMeasure μ] (ε : ℝ) (ht : t ≤ 0)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    μ.real {ω | X ω ≤ ε} ≤ exp (-t * ε + cgf X μ t) := by
  refine (measure_le_le_exp_mul_mgf ε ht h_int).trans ?_
  rw [exp_add]
  exact mul_le_mul le_rfl (le_exp_log _) mgf_nonneg (exp_pos _).le

end Chernoff

/-
**ProbabilityTheory.mgf_dirac** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_dirac {x : Real} (hX : μ.map X = .dirac x) (t : Real) : mgf X μ t = ex
p (x * t)
参数：hX : μ.map X = .dirac x；t : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.mgf_id_map`：mgf_id_map (hX : AEMeasurable X μ) : mgf i
d (μ.map X) = mgf X μ
· 使用定理 `AEMeasurable.of_map_ne_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Measu
rableSpace α} {mβ : MeasurableSpace β} {f : α → β}   {μ : MeasureTheory.Measure 
α}, MeasureTheory…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.ne_zero`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure 
μ], μ ≠ 0
· 使用定理 `ProbabilityTheory.mgf.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (X 
: Ω → ℝ) (μ : MeasureTheory.Measure Ω) (t : ℝ),   ProbabilityTheory.mgf X μ t = 
∫ (x : Ω), (fun …
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `id_def`：∀ {α : Sort u} (a : α), id a = a
-/
lemma mgf_dirac {x : ℝ} (hX : μ.map X = .dirac x) (t : ℝ) : mgf X μ t = exp (x * t) := by
  have : IsProbabilityMeasure (μ.map X) := by rw [hX]; infer_instance
  rw [← mgf_id_map (.of_map_ne_zero <| IsProbabilityMeasure.ne_zero _), mgf, hX, integral_dirac,
    mul_comm, id_def]
/-
**ProbabilityTheory.mgf_dirac'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：mgf_dirac' [MeasurableSingletonClass Ω] {ω : Ω} : mgf X (Measure.dirac ω) 
t = exp (t * X ω)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.mgf.eq_1`：∀ {Ω : Type u_1} {m : MeasurableSpace Ω} (X 
: Ω → ℝ) (μ : MeasureTheory.Measure Ω) (t : ℝ),   ProbabilityTheory.mgf X μ t = 
∫ (x : Ω), (fun …
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
-/
lemma mgf_dirac' [MeasurableSingletonClass Ω] {ω : Ω} :
    mgf X (Measure.dirac ω) t = exp (t * X ω) := by
  rw [mgf, integral_dirac]

end MomentGeneratingFunction

/-
**ProbabilityTheory.aemeasurable_exp_mul** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：aemeasurable_exp_mul {X : Ω -> Real} (t : Real) (hX : AEMeasurable X μ) : 
AEStronglyMeasurable (fun ω => rexp (t * X ω)) μ
参数：t : Real；hX : AEMeasurable X μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Real.measurable_exp`：measurable_exp : Measurable exp
· 使用定理 `AEMeasurable.const_mul`：AEMeasurable.const_mul [MeasurableMul M] (hf : A
EMeasurable f μ) (c : M) : AEMeasurable (fun x => c * f x) μ
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
-/
lemma aemeasurable_exp_mul {X : Ω → ℝ} (t : ℝ) (hX : AEMeasurable X μ) :
    AEStronglyMeasurable (fun ω ↦ rexp (t * X ω)) μ :=
  (measurable_exp.comp_aemeasurable (hX.const_mul t)).aestronglyMeasurable
/-
**ProbabilityTheory.integrable_exp_mul_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：integrable_exp_mul_of_le [IsFiniteMeasure μ] {X : Ω -> Real} (t b : Real) 
(ht : 0 <= t) (hX : AEMeasurable X μ) (hb : forallᵐ ω ∂μ, X ω <= b) : Integrable
 (fun ω => exp (t * X ω)) μ
参数：t b : Real；ht : 0 <= t；hX : AEMeasurable X μ；hb : forallᵐ ω ∂μ, X ω <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.of_mem_Icc`：∀ {α : Type u_1} {m : MeasurableSpa
ce α} {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ] (a b : ℝ) 
  {X : α → ℝ}, AEMeasurab…
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Real.measurable_exp`：measurable_exp : Measurable exp
· 使用定理 `AEMeasurable.const_mul`：AEMeasurable.const_mul [MeasurableMul M] (hf : A
EMeasurable f μ) (c : M) : AEMeasurable (fun x => c * f x) μ
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
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Real.exp_monotone`：exp_monotone : Monotone exp
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma integrable_exp_mul_of_le [IsFiniteMeasure μ] {X : Ω → ℝ} (t b : ℝ) (ht : 0 ≤ t)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ≤ b) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  refine .of_mem_Icc 0 (rexp (t * b)) (measurable_exp.comp_aemeasurable (hX.const_mul t)) ?_
  filter_upwards [hb] with ω hb
  exact ⟨by positivity, by gcongr⟩
/-
**ProbabilityTheory.integrable_exp_mul_of_mem_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：integrable_exp_mul_of_mem_Icc [IsFiniteMeasure μ] {X : Ω -> Real} {a b t :
 Real} (hm : AEMeasurable X μ) (hb : forallᵐ ω ∂μ, X ω in Set.Icc a b) : Integra
ble (fun ω => exp (t * X ω)) μ
参数：hm : AEMeasurable X μ；hb : forallᵐ ω ∂μ, X ω in Set.Icc a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.of_mem_Icc`：∀ {α : Type u_1} {m : MeasurableSpa
ce α} {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ] (a b : ℝ) 
  {X : α → ℝ}, AEMeasurab…
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Real.measurable_exp`：measurable_exp : Measurable exp
· 使用定理 `AEMeasurable.const_mul`：AEMeasurable.const_mul [MeasurableMul M] (hf : A
EMeasurable f μ) (c : M) : AEMeasurable (fun x => c * f x) μ
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
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 68 条，此处仅展示前 30 条）
-/
lemma integrable_exp_mul_of_mem_Icc [IsFiniteMeasure μ] {X : Ω → ℝ} {a b t : ℝ}
    (hm : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable (fun ω ↦ exp (t * X ω)) μ := by
  apply Integrable.of_mem_Icc (exp (min (a * t) (b * t))) (exp (max (a * t) (b * t)))
  · exact (measurable_exp.comp_aemeasurable (hm.const_mul t))
  filter_upwards [hb] with ω ⟨hl, hr⟩
  simp only [Set.mem_Icc, exp_le_exp, inf_le_iff, le_sup_iff]
  by_cases ht : 0 ≤ t
  · exact ⟨Or.inl (by nlinarith), Or.inr (by nlinarith)⟩
  · exact ⟨Or.inr (by nlinarith), Or.inl (by nlinarith)⟩

end ProbabilityTheory

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace ℝ E] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace E]
    [CompleteSpace F] [MeasurableSpace E] {μ : Measure E}

/-
**ContinuousLinearMap.integral_comp_id_comm'** 是 Mathlib 中的一个引理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：integral_comp_id_comm' (h : Integrable id μ) (L : E ->L[𝕜] F) : μ[L] = L μ
[id]
参数：h : Integrable id μ；L : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
-/
lemma integral_comp_id_comm' (h : Integrable id μ) (L : E →L[𝕜] F) :
    μ[L] = L μ[id] := by
  change ∫ x, L (id x) ∂μ = _
  rw [L.integral_comp_comm h]
/-
**ContinuousLinearMap.integral_comp_id_comm** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：integral_comp_id_comm (h : Integrable id μ) (L : E ->L[𝕜] F) : μ[L] = L (∫
 x, x ∂μ)
参数：h : Integrable id μ；L : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.integral_comp_id_comm'`：integral_comp_id_comm' (h : 
Integrable id μ) (L : E ->L[𝕜] F) : μ[L] = L μ[id]
-/
lemma integral_comp_id_comm (h : Integrable id μ) (L : E →L[𝕜] F) :
    μ[L] = L (∫ x, x ∂μ) :=
  L.integral_comp_id_comm' h

variable [OpensMeasurableSpace E] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
/-
**ContinuousLinearMap.integral_id_map** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：integral_id_map (h : Integrable id μ) (L : E ->L[𝕜] F) : ∫ x, x ∂(μ.map L)
 = L (∫ x, x ∂μ)
参数：h : Integrable id μ；L : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `Continuous.aemeasurable`：Continuous.aemeasurable {f : α -> γ} (h : Conti
nuous f) {μ : Measure α} : AEMeasurable f μ
· 使用定理 `Continuous.clm_apply`：Continuous.clm_apply {f : X -> E ->L[𝕜] F} {g : X 
-> E} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => f x (g x))
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `aestronglyMeasurable_id`：∀ {α : Type u_5} [inst : TopologicalSpace α] [T
opologicalSpace.PseudoMetrizableSpace α] {x : MeasurableSpace α}   [OpensMeasura
bleSpace α] […
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ContinuousLinearMap.integral_comp_id_comm`：integral_comp_id_comm (h : In
tegrable id μ) (L : E ->L[𝕜] F) : μ[L] = L (∫ x, x ∂μ)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_id_map (h : Integrable id μ) (L : E →L[𝕜] F) :
    ∫ x, x ∂(μ.map L) = L (∫ x, x ∂μ) := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp [L.integral_comp_id_comm h]

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace ℝ E] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [CompleteSpace E]
    [CompleteSpace F] [MeasurableSpace E] {μ : Measure E}

/-
**ContinuousLinearEquiv.integral_comp_id_comm'** 是 Mathlib 中的一个引理，位于命名空间 `Contin
uousLinearEquiv`。
形式化陈述：integral_comp_id_comm' (L : E ≃L[𝕜] F) : μ[L] = L μ[id]
参数：L : E ≃L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearMap.integral_comp_id_comm'`：integral_comp_id_comm' (h : 
Integrable id μ) (L : E ->L[𝕜] F) : μ[L] = L μ[id]
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearEquiv.integrable_comp_iff`：ContinuousLinearEquiv.integra
ble_comp_iff {φ : α -> H} (L : H ≃SL[σ] E) : Integrable (fun a : α => L (φ a)) μ
 ↔ Integrable φ μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
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
· 使用定理 `ContinuousSemilinearEquivClass.continuousSemilinearMapClass`：∀ (F : Type
 u_1) {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] (σ
 : R →+* S) {σ' : S →+* R}   [inst_2 : RingHomInv…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_comp_id_comm' (L : E ≃L[𝕜] F) :
    μ[L] = L μ[id] := by
  by_cases h : Integrable (fun x ↦ x) μ
  · exact ContinuousLinearMap.integral_comp_id_comm' h L.toContinuousLinearMap
  have : ¬ Integrable L μ := mt L.integrable_comp_iff.1 h
  simp_all [integral_undef]
/-
**ContinuousLinearEquiv.integral_comp_id_comm** 是 Mathlib 中的一个引理，位于命名空间 `Continu
ousLinearEquiv`。
形式化陈述：integral_comp_id_comm (L : E ≃L[𝕜] F) : μ[L] = L (∫ x, x ∂μ)
参数：L : E ≃L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousLinearEquiv.integral_comp_id_comm'`：integral_comp_id_comm' (L 
: E ≃L[𝕜] F) : μ[L] = L μ[id]
-/
lemma integral_comp_id_comm (L : E ≃L[𝕜] F) :
    μ[L] = L (∫ x, x ∂μ) := L.integral_comp_id_comm'

variable [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
/-
**ContinuousLinearEquiv.integral_id_map** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLin
earEquiv`。
形式化陈述：integral_id_map (L : E ≃L[𝕜] F) : ∫ x, x ∂(μ.map L) = L (∫ x, x ∂μ)
参数：L : E ≃L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_map_equiv`：integral_map_equiv {β} [MeasurableSpac
e β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ContinuousLinearEquiv.integral_comp_id_comm`：integral_comp_id_comm (L : 
E ≃L[𝕜] F) : μ[L] = L (∫ x, x ∂μ)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_id_map (L : E ≃L[𝕜] F) :
    ∫ x, x ∂(μ.map L) = L (∫ x, x ∂μ) := by
  rw [show ⇑L = ⇑L.toHomeomorph.toMeasurableEquiv from rfl, integral_map_equiv]
  simp [L.integral_comp_id_comm]

end ContinuousLinearEquiv

