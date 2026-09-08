/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Kexing Ying
-/
module

public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.Probability.Independence.Integrable

/-!
# Variance of random variables

We define the variance of a real-valued random variable as `Var[X] = 𝔼[(X - 𝔼[X])^2]` (in the
`ProbabilityTheory` locale).

## Main definitions

* `ProbabilityTheory.evariance`: the variance of a real-valued random variable as an extended
  non-negative real.
* `ProbabilityTheory.variance`: the variance of a real-valued random variable as a real number.

## Main results

* `ProbabilityTheory.variance_le_expectation_sq`: the inequality `Var[X] ≤ 𝔼[X^2]`.
* `ProbabilityTheory.meas_ge_le_variance_div_sq`: Chebyshev's inequality, i.e.,
      `ℙ {ω | c ≤ |X ω - 𝔼[X]|} ≤ ENNReal.ofReal (Var[X] / c ^ 2)`.
* `ProbabilityTheory.meas_ge_le_evariance_div_sq`: Chebyshev's inequality formulated with
  `evariance` without requiring the random variables to be L².
* `ProbabilityTheory.IndepFun.variance_add`: the variance of the sum of two independent
  random variables is the sum of the variances.
* `ProbabilityTheory.IndepFun.variance_sum`: the variance of a finite sum of pairwise
  independent random variables is the sum of the variances.
* `ProbabilityTheory.variance_le_sub_mul_sub`: the variance of a random variable `X` satisfying
  `a ≤ X ≤ b` almost everywhere is at most `(b - 𝔼 X) * (𝔼 X - a)`.
* `ProbabilityTheory.variance_le_sq_of_bounded`: the variance of a random variable `X` satisfying
  `a ≤ X ≤ b` almost everywhere is at most `((b - a) / 2) ^ 2`.
-/

@[expose] public section

open MeasureTheory Filter Finset

noncomputable section

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : Measure Ω}

variable (X μ) in
-- TODO: Consider if `evariance` or `eVariance` is better. Also,
-- consider `eVariationOn` in `Mathlib.Analysis.BoundedVariation`.
/-- The `ℝ≥0∞`-valued variance of a real-valued random variable defined as the Lebesgue integral of
`‖X - 𝔼[X]‖^2`. -/
/-
**ProbabilityTheory.evariance** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：evariance : Real>=0∞
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ℝ≥0∞`-valued variance of a real-valued random variable defined as the Lebes
gue integral of
`‖X - 𝔼[X]‖^2`.
-/
def evariance : ℝ≥0∞ := ∫⁻ ω, ‖X ω - μ[X]‖ₑ ^ 2 ∂μ

variable (X μ) in
/-- The `ℝ`-valued variance of a real-valued random variable defined by applying `ENNReal.toReal`
to `evariance`. -/
@[wikidata Q175199]
/-
**ProbabilityTheory.variance** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：variance : Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ℝ`-valued variance of a real-valued random variable defined by applying `EN
NReal.toReal`
to `evariance`.
-/
def variance : ℝ := (evariance X μ).toReal

/-- The `ℝ≥0∞`-valued variance of the real-valued random variable `X` according to the measure `μ`.

This is defined as the Lebesgue integral of `(X - 𝔼[X])^2`. -/
scoped notation "eVar[" X "; " μ "]" => ProbabilityTheory.evariance X μ

/-- The `ℝ≥0∞`-valued variance of the real-valued random variable `X` according to the volume
measure.

This is defined as the Lebesgue integral of `(X - 𝔼[X])^2`. -/
scoped notation "eVar[" X "]" => eVar[X; MeasureTheory.MeasureSpace.volume]

/-- The `ℝ`-valued variance of the real-valued random variable `X` according to the measure `μ`.

It is set to `0` if `X` has infinite variance. -/
scoped notation "Var[" X "; " μ "]" => ProbabilityTheory.variance X μ

/-- The `ℝ`-valued variance of the real-valued random variable `X` according to the volume measure.

It is set to `0` if `X` has infinite variance. -/
scoped notation "Var[" X "]" => Var[X; MeasureTheory.MeasureSpace.volume]

/-
**ProbabilityTheory.evariance_congr** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：evariance_congr (h : X =ᵐ[μ] Y) : eVar[X; μ] = eVar[Y; μ]
参数：h : X =ᵐ[μ] Y。
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
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evariance_congr (h : X =ᵐ[μ] Y) : eVar[X; μ] = eVar[Y; μ] := by
  simp_rw [evariance, integral_congr_ae h]
  apply lintegral_congr_ae
  filter_upwards [h] with ω hω using by simp [hω]
/-
**ProbabilityTheory.variance_congr** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：variance_congr (h : X =ᵐ[μ] Y) : Var[X; μ] = Var[Y; μ]
参数：h : X =ᵐ[μ] Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.evariance_congr`：evariance_congr (h : X =ᵐ[μ] Y) : eVa
r[X; μ] = eVar[Y; μ]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem variance_congr (h : X =ᵐ[μ] Y) : Var[X; μ] = Var[Y; μ] := by
  simp_rw [variance, evariance_congr h]
/-
**ProbabilityTheory.evariance_zero_measure** 是 Mathlib 中的一个定理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {X : Ω → ℝ}, ProbabilityTheory.e
variance X 0 = 0
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
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma evariance_zero_measure : eVar[X; (0 : Measure Ω)] = 0 := by simp [evariance]
/-
**ProbabilityTheory.variance_zero_measure** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {X : Ω → ℝ}, ProbabilityTheory.v
ariance X 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.evariance_zero_measure`：∀ {Ω : Type u_1} {mΩ : Measura
bleSpace Ω} {X : Ω → ℝ}, ProbabilityTheory.evariance X 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma variance_zero_measure : Var[X; (0 : Measure Ω)] = 0 := by simp [variance]
/-
**ProbabilityTheory.evariance_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：evariance_lt_top [IsFiniteMeasure μ] (hX : MemLp X 2 μ) : evariance X μ < 
∞
参数：hX : MemLp X 2 μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ENNReal.pow_lt_top`：pow_lt_top (ha : a < ∞) : a ^ n < ∞
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.MemLp.sub`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} [inst : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measur
e α} {f g : α…
· 使用定理 `MeasureTheory.memLp_const`：memLp_const (c : E) [IsFiniteMeasure μ] : Mem
Lp (fun _ : α => c) p μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.rpow_two`：rpow_two (x : Real>=0∞) : x ^ (2 : Real) = x ^ 2
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.toReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).t
oReal = OfNat.ofNat n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal`：eLpNorm_eq_lintegr
al_rpow_enorm_toReal (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε} : e
LpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ…
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
-/
theorem evariance_lt_top [IsFiniteMeasure μ] (hX : MemLp X 2 μ) : evariance X μ < ∞ := by
  have := ENNReal.pow_lt_top (hX.sub <| memLp_const <| μ[X]).2 (n := 2)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ← ENNReal.rpow_two]
    at this
  simp only [ENNReal.toReal_ofNat, Pi.sub_apply, one_div] at this
  rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), ENNReal.rpow_one] at this
  simp_rw [ENNReal.rpow_two] at this
  exact this
/-
**ProbabilityTheory.evariance_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：evariance_ne_top [IsFiniteMeasure μ] (hX : MemLp X 2 μ) : evariance X μ !=
 ∞
参数：hX : MemLp X 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ProbabilityTheory.evariance_lt_top`：evariance_lt_top [IsFiniteMeasure μ]
 (hX : MemLp X 2 μ) : evariance X μ < ∞
-/
lemma evariance_ne_top [IsFiniteMeasure μ] (hX : MemLp X 2 μ) : evariance X μ ≠ ∞ :=
  (evariance_lt_top hX).ne
/-
**ProbabilityTheory.evariance_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：evariance_eq_top [IsFiniteMeasure μ] (hXm : AEStronglyMeasurable X μ) (hX 
: ¬MemLp X 2 μ) : evariance X μ = ∞
参数：hXm : AEStronglyMeasurable X μ；hX : ¬MemLp X 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_sub`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f g : α → β} [inst_1…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal`：eLpNorm_eq_lintegr
al_rpow_enorm_toReal (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε} : e
LpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ…
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.toReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).t
oReal = OfNat.ofNat n
· 使用定理 `ENNReal.rpow_two`：rpow_two (x : Real>=0∞) : x ^ (2 : Real) = x ^ 2
· 使用定理 `ENNReal.rpow_lt_top_of_nonneg`：rpow_lt_top_of_nonneg {x : Real>=0∞} {y :
 Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y < ⊤
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 80 条，此处仅展示前 30 条）
-/
theorem evariance_eq_top [IsFiniteMeasure μ] (hXm : AEStronglyMeasurable X μ) (hX : ¬MemLp X 2 μ) :
    evariance X μ = ∞ := by
  by_contra h
  rw [← Ne, ← lt_top_iff_ne_top] at h
  have : MemLp (fun ω => X ω - μ[X]) 2 μ := by
    refine ⟨by fun_prop, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    exact ENNReal.rpow_lt_top_of_nonneg (by linarith) h.ne
  refine hX ?_
  convert! this.add (memLp_const μ[X])
  ext ω
  rw [Pi.add_apply, sub_add_cancel]
/-
**ProbabilityTheory.evariance_lt_top_iff_memLp** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：evariance_lt_top_iff_memLp [IsFiniteMeasure μ] (hX : AEStronglyMeasurable 
X μ) : evariance X μ < ∞ ↔ MemLp X 2 μ where mp
参数：hX : AEStronglyMeasurable X μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `ProbabilityTheory.evariance_eq_top`：evariance_eq_top [IsFiniteMeasure μ]
 (hXm : AEStronglyMeasurable X μ) (hX : ¬MemLp X 2 μ) : evariance X μ = ∞
· 使用定理 `ProbabilityTheory.evariance_lt_top`：evariance_lt_top [IsFiniteMeasure μ]
 (hX : MemLp X 2 μ) : evariance X μ < ∞
-/
theorem evariance_lt_top_iff_memLp [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ) :
    evariance X μ < ∞ ↔ MemLp X 2 μ where
  mp := by contrapose!; rw [top_le_iff]; exact evariance_eq_top hX
  mpr := evariance_lt_top
/-
**ProbabilityTheory.evariance_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：evariance_eq_top_iff [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ) :
 evariance X μ = ∞ ↔ ¬ MemLp X 2 μ
参数：hX : AEStronglyMeasurable X μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.evariance_lt_top_iff_memLp`：evariance_lt_top_iff_memLp
 [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ) : evariance X μ < ∞ ↔ MemLp
 X 2 μ where mp
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma evariance_eq_top_iff [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ) :
    evariance X μ = ∞ ↔ ¬ MemLp X 2 μ := by simp [← evariance_lt_top_iff_memLp hX]
/-
**ProbabilityTheory.variance_of_not_memLp** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：variance_of_not_memLp [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ) 
(hX_not : ¬ MemLp X 2 μ) : variance X μ = 0
参数：hX : AEStronglyMeasurable X μ；hX_not : ¬ MemLp X 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ProbabilityTheory.evariance_eq_top_iff`：evariance_eq_top_iff [IsFiniteMe
asure μ] (hX : AEStronglyMeasurable X μ) : evariance X μ = ∞ ↔ ¬ MemLp X 2 μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma variance_of_not_memLp [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ)
    (hX_not : ¬ MemLp X 2 μ) :
    variance X μ = 0 := by simp [variance, (evariance_eq_top_iff hX).mpr hX_not]
/-
**ProbabilityTheory.memLp_two_of_variance_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：memLp_two_of_variance_ne_zero [IsFiniteMeasure μ] (hX : AEStronglyMeasurab
le X μ) (h : Var[X; μ] != 0) : MemLp X 2 μ
参数：hX : AEStronglyMeasurable X μ；h : Var[X; μ] != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.variance_of_not_memLp`：variance_of_not_memLp [IsFinite
Measure μ] (hX : AEStronglyMeasurable X μ) (hX_not : ¬ MemLp X 2 μ) : variance X
 μ = 0
-/
lemma memLp_two_of_variance_ne_zero [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ)
    (h : Var[X; μ] ≠ 0) : MemLp X 2 μ := by
  contrapose h
  exact variance_of_not_memLp hX h
/-
**ProbabilityTheory.ofReal_variance** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：ofReal_variance [IsFiniteMeasure μ] (hX : MemLp X 2 μ) : .ofReal (variance
 X μ) = evariance X μ
参数：hX : MemLp X 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.variance.eq_1`：∀ {Ω : Type u_1} {mΩ : MeasurableSpace 
Ω} (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω),   ProbabilityTheory.variance X μ =
 (ProbabilityTheory.e…
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用引理 `ProbabilityTheory.evariance_ne_top`：evariance_ne_top [IsFiniteMeasure μ]
 (hX : MemLp X 2 μ) : evariance X μ != ∞
-/
theorem ofReal_variance [IsFiniteMeasure μ] (hX : MemLp X 2 μ) :
    .ofReal (variance X μ) = evariance X μ := by
  rw [variance, ENNReal.ofReal_toReal]
  exact evariance_ne_top hX

protected alias _root_.MeasureTheory.MemLp.evariance_lt_top := evariance_lt_top
protected alias _root_.MeasureTheory.MemLp.evariance_ne_top := evariance_ne_top
protected alias _root_.MeasureTheory.MemLp.ofReal_variance_eq := ofReal_variance

variable (X μ) in
/-
**ProbabilityTheory.evariance_eq_lintegral_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：evariance_eq_lintegral_ofReal : evariance X μ = ∫⁻ ω, ENNReal.ofReal ((X ω
 - μ[X]) ^ 2) ∂μ
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
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Real.enorm_of_nonneg`：enorm_of_nonneg (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evariance_eq_lintegral_ofReal :
    evariance X μ = ∫⁻ ω, ENNReal.ofReal ((X ω - μ[X]) ^ 2) ∂μ := by
  simp [evariance, ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
/-
**ProbabilityTheory.variance_eq_integral** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：variance_eq_integral (hX : AEMeasurable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X
]) ^ 2 ∂μ
参数：hX : AEMeasurable X μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_toReal`：integral_toReal {f : α -> Real>=0∞} (hfm 
: AEMeasurable f μ) (hf : forallᵐ x ∂μ, f x < ∞) : ∫ a, (f a).toReal ∂μ = (∫⁻ a,
 f a ∂μ).toReal
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `AEMeasurable.enorm`：∀ {β : Type u_2} {ε : Type u_5} [inst : MeasurableSp
ace ε] [inst_1 : TopologicalSpace ε] [inst_2 : ContinuousENorm ε]   [OpensMeasur
ableSpac…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `AEMeasurable.sub_const`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurab
leSpace G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   {μ : MeasureTh
eory.Measure…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ENNReal.pow_lt_top`：pow_lt_top (ha : a < ∞) : a ^ n < ∞
· 使用定理 `enorm_lt_top`：∀ {E : Type u_8} [inst : NNNorm E] {x : E}, ‖x‖ₑ < ⊤
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.toReal_pow`：toReal_pow (a : Real>=0∞) (n : Nat) : (a ^ n).toReal
 = a.toReal ^ n
· 使用定理 `toReal_enorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ‖x
‖ₑ.toReal = ‖x‖
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma variance_eq_integral (hX : AEMeasurable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ := by
  simp [variance, evariance, toReal_enorm, ← integral_toReal ((hX.sub_const _).enorm.pow_const _) <|
    .of_forall fun _ ↦ ENNReal.pow_lt_top enorm_lt_top]

/-- A random variable with variance `0` is almost surely constant. -/
/-
**ProbabilityTheory.ae_eq_integral_of_variance_eq_zero** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：ae_eq_integral_of_variance_eq_zero [IsFiniteMeasure μ] (hX : MemLp X 2 μ) 
(h : Var[X; μ] = 0) : forallᵐ ω ∂μ, X ω = μ[X]
参数：hX : MemLp X 2 μ；h : Var[X; μ] = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_zero_iff_of_nonneg`：integral_eq_zero_iff_of_no
nneg {f : α -> Real} (hf : 0 <= f) (hfi : Integrable f μ) : ∫ x, f x ∂μ = 0 ↔ f 
=ᵐ[μ] 0
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `sub_sq`：sub_sq (a b : R) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2
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
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `MeasureTheory.MemLp.integrable_sq`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.MemLp f 2 μ → Mea
sureTheory.Integrable (…
· 使用定理 `MeasureTheory.Integrable.mul_const`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.MemLp.integrable`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
A random variable with variance `0` is almost surely constant.
-/
lemma ae_eq_integral_of_variance_eq_zero [IsFiniteMeasure μ] (hX : MemLp X 2 μ)
    (h : Var[X; μ] = 0) :
    ∀ᵐ ω ∂μ, X ω = μ[X] := by
  rw [variance_eq_integral hX.aemeasurable, integral_eq_zero_iff_of_nonneg] at h
  · filter_upwards [h] with ω hω
    simp at hω
    grind
  · exact fun _ ↦ by positivity
  · simp_rw [sub_sq]
    exact (hX.integrable_sq.sub (((hX.integrable (by simp)).const_mul _).mul_const _)).add
      (integrable_const _)
/-
**ProbabilityTheory.variance_of_integral_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：variance_of_integral_eq_zero (hX : AEMeasurable X μ) (hXint : μ[X] = 0) : 
variance X μ = ∫ ω, X ω ^ 2 ∂μ
参数：hX : AEMeasurable X μ；hXint : μ[X] = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.variance_eq_integral`：variance_eq_integral (hX : AEMea
surable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma variance_of_integral_eq_zero (hX : AEMeasurable X μ) (hXint : μ[X] = 0) :
    variance X μ = ∫ ω, X ω ^ 2 ∂μ := by
  simp [variance_eq_integral hX, hXint]

@[simp]
/-
**ProbabilityTheory.evariance_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：evariance_zero : evariance 0 μ = 0
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
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem evariance_zero : evariance 0 μ = 0 := by simp [evariance]
/-
**ProbabilityTheory.evariance_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory`。
形式化陈述：evariance_eq_zero_iff (hX : AEMeasurable X μ) : evariance X μ = 0 ↔ X =ᵐ[μ
] fun _ => μ[X]
参数：hX : AEMeasurable X μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff'`：lintegral_eq_zero_iff' {f : α -> R
eal>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `AEMeasurable.enorm`：∀ {β : Type u_2} {ε : Type u_5} [inst : MeasurableSp
ace ε] [inst_1 : TopologicalSpace ε] [inst_2 : ContinuousENorm ε]   [OpensMeasur
ableSpac…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `AEMeasurable.sub_const`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurab
leSpace G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   {μ : MeasureTh
eory.Measure…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem evariance_eq_zero_iff (hX : AEMeasurable X μ) :
    evariance X μ = 0 ↔ X =ᵐ[μ] fun _ => μ[X] := by
  simp [evariance, lintegral_eq_zero_iff' ((hX.sub_const _).enorm.pow_const _), EventuallyEq,
    sub_eq_zero]
/-
**ProbabilityTheory.evariance_mul** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：evariance_mul (c : Real) (X : Ω -> Real) (μ : Measure Ω) : evariance (fun 
ω => c * X ω) μ = ENNReal.ofReal (c ^ 2) * evariance X μ
参数：c : Real；X : Ω -> Real；μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.evariance.eq_1`：∀ {Ω : Type u_1} {mΩ : MeasurableSpace
 Ω} (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω),   ProbabilityTheory.evariance X μ
 = ∫⁻ (ω : Ω), ‖X ω - …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_const_mul'`：lintegral_const_mul' (r : Real>=0∞) 
(f : α -> Real>=0∞) (hr : r != ∞) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `enorm_mul`：∀ {α : Type u_2} [inst : SeminormedAddCommGroup α] [inst_1 : 
Mul α] [NormMulClass α] (a b : α), ‖a * b‖ₑ = ‖a‖ₑ * ‖b‖ₑ
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `enorm_pow`：∀ {α : Type u_2} [inst : SeminormedRing α] [NormOneClass α] [
NormMulClass α] (a : α) (n : ℕ), ‖a ^ n‖ₑ = ‖a‖ₑ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用引理 `Real.enorm_of_nonneg`：enorm_of_nonneg (hr : 0 <= r) : ‖r‖ₑ = .ofReal r
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem evariance_mul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    evariance (fun ω => c * X ω) μ = ENNReal.ofReal (c ^ 2) * evariance X μ := by
  rw [evariance, evariance, ← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
  congr with ω
  rw [integral_const_mul, ← mul_sub, enorm_mul, mul_pow, ← enorm_pow,
    Real.enorm_of_nonneg (sq_nonneg _)]

@[simp]
/-
**ProbabilityTheory.variance_zero** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：variance_zero (μ : Measure Ω) : variance 0 μ = 0
参数：μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.evariance_zero`：evariance_zero : evariance 0 μ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem variance_zero (μ : Measure Ω) : variance 0 μ = 0 := by
  simp only [variance, evariance_zero, ENNReal.toReal_zero]
/-
**ProbabilityTheory.covariance_self** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：covariance_self {X : Ω -> Real} (hX : AEMeasurable X μ) : cov[X, X; μ] = V
ar[X; μ]
参数：hX : AEMeasurable X μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.covariance.eq_1`：∀ {Ω : Type u_1} {mΩ : MeasurableSpac
e Ω} (X Y : Ω → ℝ) (μ : MeasureTheory.Measure Ω),   ProbabilityTheory.covariance
 X Y μ = ∫ (ω : Ω), (X …
· 使用引理 `ProbabilityTheory.variance_eq_integral`：variance_eq_integral (hX : AEMea
surable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 47 条，此处仅展示前 30 条）
-/
lemma covariance_self {X : Ω → ℝ} (hX : AEMeasurable X μ) :
    cov[X, X; μ] = Var[X; μ] := by
  rw [covariance, variance_eq_integral hX]
  congr with x
  ring

@[simp]
/-
**ProbabilityTheory.variance_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：variance_nonneg (X : Ω -> Real) (μ : Measure Ω) : 0 <= variance X μ
参数：X : Ω -> Real；μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
-/
theorem variance_nonneg (X : Ω → ℝ) (μ : Measure Ω) : 0 ≤ variance X μ :=
  ENNReal.toReal_nonneg
/-
**ProbabilityTheory.variance_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：variance_const_mul (c : Real) (X : Ω -> Real) (μ : Measure Ω) : variance (
fun ω => c * X ω) μ = c ^ 2 * variance X μ
参数：c : Real；X : Ω -> Real；μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.variance.eq_1`：∀ {Ω : Type u_1} {mΩ : MeasurableSpace 
Ω} (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω),   ProbabilityTheory.variance X μ =
 (ProbabilityTheory.e…
· 使用定理 `ProbabilityTheory.evariance_mul`：evariance_mul (c : Real) (X : Ω -> Real
) (μ : Measure Ω) : evariance (fun ω => c * X ω) μ = ENNReal.ofReal (c ^ 2) * ev
ariance X μ
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem variance_const_mul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    variance (fun ω => c * X ω) μ = c ^ 2 * variance X μ := by
  rw [variance, evariance_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl
/-
**ProbabilityTheory.variance_mul_const** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：variance_mul_const (c : Real) (X : Ω -> Real) (μ : Measure Ω) : variance (
fun ω => X ω * c) μ = variance X μ * c ^ 2
参数：c : Real；X : Ω -> Real；μ : Measure Ω。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ProbabilityTheory.variance_const_mul`：variance_const_mul (c : Real) (X :
 Ω -> Real) (μ : Measure Ω) : variance (fun ω => c * X ω) μ = c ^ 2 * variance X
 μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem variance_mul_const (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    variance (fun ω => X ω * c) μ = variance X μ * c ^ 2 := by
  simp [mul_comm, variance_const_mul]
/-
**ProbabilityTheory.variance_smul** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：variance_smul (c : Real) (X : Ω -> Real) (μ : Measure Ω) : variance (c • X
) μ = c ^ 2 * variance X μ
参数：c : Real；X : Ω -> Real；μ : Measure Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.variance_const_mul`：variance_const_mul (c : Real) (X :
 Ω -> Real) (μ : Measure Ω) : variance (fun ω => c * X ω) μ = c ^ 2 * variance X
 μ
-/
theorem variance_smul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    variance (c • X) μ = c ^ 2 * variance X μ :=
  variance_const_mul c X μ
/-
**ProbabilityTheory.variance_smul'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：variance_smul' {A : Type*} [CommSemiring A] [Algebra A Real] (c : A) (X : 
Ω -> Real) (μ : Measure Ω) : variance (c • X) μ = c ^ 2 • variance X μ
参数：c : A；X : Ω -> Real；μ : Measure Ω。
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
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `ProbabilityTheory.variance_smul`：variance_smul (c : Real) (X : Ω -> Real
) (μ : Measure Ω) : variance (c • X) μ = c ^ 2 * variance X μ
-/
theorem variance_smul' {A : Type*} [CommSemiring A] [Algebra A ℝ] (c : A) (X : Ω → ℝ)
    (μ : Measure Ω) : variance (c • X) μ = c ^ 2 • variance X μ := by
  convert! variance_smul (algebraMap A ℝ c) X μ using 1
  · simp only [algebraMap_smul]
  · simp only [Algebra.smul_def, map_pow]
/-
**ProbabilityTheory.variance_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：variance_eq_sub [IsProbabilityMeasure μ] {X : Ω -> Real} (hX : MemLp X 2 μ
) : variance X μ = μ[X ^ 2] - μ[X] ^ 2
参数：hX : MemLp X 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.covariance_self`：covariance_self {X : Ω -> Real} (hX :
 AEMeasurable X μ) : cov[X, X; μ] = Var[X; μ]
· 使用定理 `MeasureTheory.MemLp.aemeasurable`：∀ {α : Type u_1} {ε : Type u_2} {m0 : 
MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [inst_1 : Me
asurableSpace ε] [inst…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `ProbabilityTheory.covariance_eq_sub`：covariance_eq_sub [IsProbabilityMea
sure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) : cov[X, Y; μ] = μ[X * Y] - μ[X] *
 μ[Y]
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
theorem variance_eq_sub [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    variance X μ = μ[X ^ 2] - μ[X] ^ 2 := by
  rw [← covariance_self hX.aemeasurable, covariance_eq_sub hX hX, pow_two, pow_two]
/-
**ProbabilityTheory.variance_add_const** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：variance_add_const [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ
) (c : Real) : Var[fun ω => X ω + c; μ] = Var[X; μ]
参数：hX : AEStronglyMeasurable X μ；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.MemLp.integrable`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.variance_eq_integral`：variance_eq_integral (hX : AEMea
surable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.add_const`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.
Measure α}   {f : α → β} [inst_1 :…
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
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 53 条，此处仅展示前 30 条）
-/
lemma variance_add_const [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : ℝ) :
    Var[fun ω ↦ X ω + c; μ] = Var[X; μ] := by
  by_cases hX_Lp : MemLp X 2 μ
  · have hX_int : Integrable X μ := hX_Lp.integrable one_le_two
    rw [variance_eq_integral (hX.add_const _).aemeasurable,
      integral_add hX_int (by fun_prop), integral_const, variance_eq_integral hX.aemeasurable]
    simp
  · rw [variance_of_not_memLp (hX.add_const _), variance_of_not_memLp hX hX_Lp]
    refine fun h_memLp ↦ hX_Lp ?_
    have : X = fun ω ↦ X ω + c - c := by ext; ring
    rw [this]
    exact h_memLp.sub (memLp_const c)
/-
**ProbabilityTheory.variance_const_add** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：variance_const_add [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ
) (c : Real) : Var[fun ω => c + X ω; μ] = Var[X; μ]
参数：hX : AEStronglyMeasurable X μ；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.variance_add_const`：variance_add_const [IsProbabilityM
easure μ] (hX : AEStronglyMeasurable X μ) (c : Real) : Var[fun ω => X ω + c; μ] 
= Var[X; μ]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma variance_const_add [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : ℝ) :
    Var[fun ω ↦ c + X ω; μ] = Var[X; μ] := by
  simp_rw [add_comm c, variance_add_const hX c]
/-
**ProbabilityTheory.variance_fun_neg** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：variance_fun_neg : Var[fun ω => -X ω; μ] = Var[X; μ]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
（共 36 条，此处仅展示前 30 条）
-/
lemma variance_fun_neg : Var[fun ω ↦ -X ω; μ] = Var[X; μ] := by
  convert! variance_const_mul (-1) X μ
  · ext; ring
  · simp
/-
**ProbabilityTheory.variance_neg** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：variance_neg : Var[-X; μ] = Var[X; μ]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.variance_fun_neg`：variance_fun_neg : Var[fun ω => -X ω
; μ] = Var[X; μ]
-/
lemma variance_neg : Var[-X; μ] = Var[X; μ] := variance_fun_neg
/-
**ProbabilityTheory.variance_sub_const** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：variance_sub_const [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ
) (c : Real) : Var[fun ω => X ω - c; μ] = Var[X; μ]
参数：hX : AEStronglyMeasurable X μ；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ProbabilityTheory.variance_add_const`：variance_add_const [IsProbabilityM
easure μ] (hX : AEStronglyMeasurable X μ) (c : Real) : Var[fun ω => X ω + c; μ] 
= Var[X; μ]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma variance_sub_const [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : ℝ) :
    Var[fun ω ↦ X ω - c; μ] = Var[X; μ] := by
  simp_rw [sub_eq_add_neg, variance_add_const hX (-c)]
/-
**ProbabilityTheory.variance_const_sub** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：variance_const_sub [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ
) (c : Real) : Var[fun ω => c - X ω; μ] = Var[X; μ]
参数：hX : AEStronglyMeasurable X μ；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `ProbabilityTheory.variance_const_add`：variance_const_add [IsProbabilityM
easure μ] (hX : AEStronglyMeasurable X μ) (c : Real) : Var[fun ω => c + X ω; μ] 
= Var[X; μ]
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_neg`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 :…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ProbabilityTheory.variance_fun_neg`：variance_fun_neg : Var[fun ω => -X ω
; μ] = Var[X; μ]
-/
lemma variance_const_sub [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : ℝ) :
    Var[fun ω ↦ c - X ω; μ] = Var[X; μ] := by
  simp_rw [sub_eq_add_neg]
  rw [variance_const_add (by fun_prop) c, variance_fun_neg]
/-
**ProbabilityTheory.variance_add** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：variance_add [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) : V
ar[X + Y; μ] = Var[X; μ] + 2 * cov[X, Y; μ] + Var[Y; μ]
参数：hX : MemLp X 2 μ；hY : MemLp Y 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.covariance_self`：covariance_self {X : Ω -> Real} (hX :
 AEMeasurable X μ) : cov[X, X; μ] = Var[X; μ]
· 使用定理 `AEMeasurable.add`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSpac
e M] [inst_1 : Add M] {m : MeasurableSpace α} {f g : α → M}   {μ : MeasureTheory
.Measu…
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
· 使用定理 `MeasureTheory.MemLp.aemeasurable`：∀ {α : Type u_1} {ε : Type u_2} {m0 : 
MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [inst_1 : Me
asurableSpace ε] [inst…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `ProbabilityTheory.covariance_add_left`：covariance_add_left [IsFiniteMeas
ure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) : cov[X + Y, Z; 
μ] = cov[X, Z; μ] + cov[Y, …
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用引理 `ProbabilityTheory.covariance_add_right`：covariance_add_right [IsFiniteMe
asure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) : cov[X, Y + Z
; μ] = cov[X, Y; μ] + cov[X,…
· 使用引理 `ProbabilityTheory.covariance_comm`：covariance_comm : cov[X, Y; μ] = cov[
Y, X; μ]
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 39 条，此处仅展示前 30 条）
-/
lemma variance_add [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Var[X + Y; μ] = Var[X; μ] + 2 * cov[X, Y; μ] + Var[Y; μ] := by
  rw [← covariance_self, covariance_add_left hX hY (hX.add hY), covariance_add_right hX hX hY,
    covariance_add_right hY hX hY, covariance_self, covariance_self, covariance_comm]
  · ring
  · exact hY.aemeasurable
  · exact hX.aemeasurable
  · exact hX.aemeasurable.add hY.aemeasurable
/-
**ProbabilityTheory.variance_fun_add** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：variance_fun_add [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
 : Var[fun ω => X ω + Y ω; μ] = Var[X; μ] + 2 * cov[X, Y; μ] + Var[Y; μ]
参数：hX : MemLp X 2 μ；hY : MemLp Y 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.variance_add`：variance_add [IsFiniteMeasure μ] (hX : M
emLp X 2 μ) (hY : MemLp Y 2 μ) : Var[X + Y; μ] = Var[X; μ] + 2 * cov[X, Y; μ] + 
Var[Y; μ]
-/
lemma variance_fun_add [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Var[fun ω ↦ X ω + Y ω; μ] = Var[X; μ] + 2 * cov[X, Y; μ] + Var[Y; μ] :=
  variance_add hX hY
/-
**ProbabilityTheory.variance_sub** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：variance_sub [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) : V
ar[X - Y; μ] = Var[X; μ] - 2 * cov[X, Y; μ] + Var[Y; μ]
参数：hX : MemLp X 2 μ；hY : MemLp Y 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `ProbabilityTheory.variance_add`：variance_add [IsFiniteMeasure μ] (hX : M
emLp X 2 μ) (hY : MemLp Y 2 μ) : Var[X + Y; μ] = Var[X; μ] + 2 * cov[X, Y; μ] + 
Var[Y; μ]
· 使用定理 `MeasureTheory.MemLp.neg`：∀ {α : Type u_1} {E : Type u_4} {m0 : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGro
up E] {f : α …
· 使用引理 `ProbabilityTheory.variance_neg`：variance_neg : Var[-X; μ] = Var[X; μ]
· 使用引理 `ProbabilityTheory.covariance_neg_right`：covariance_neg_right : cov[X, -Y
; μ] = -cov[X, Y; μ]
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 38 条，此处仅展示前 30 条）
-/
lemma variance_sub [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
     Var[X - Y; μ] = Var[X; μ] - 2 * cov[X, Y; μ] + Var[Y; μ] := by
   rw [sub_eq_add_neg, variance_add hX hY.neg, variance_neg, covariance_neg_right]
   ring
/-
**ProbabilityTheory.variance_fun_sub** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：variance_fun_sub [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
 : Var[fun ω => X ω - Y ω; μ] = Var[X; μ] - 2 * cov[X, Y; μ] + Var[Y; μ]
参数：hX : MemLp X 2 μ；hY : MemLp Y 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.variance_sub`：variance_sub [IsFiniteMeasure μ] (hX : M
emLp X 2 μ) (hY : MemLp Y 2 μ) : Var[X - Y; μ] = Var[X; μ] - 2 * cov[X, Y; μ] + 
Var[Y; μ]
-/
lemma variance_fun_sub [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Var[fun ω ↦ X ω - Y ω; μ] = Var[X; μ] - 2 * cov[X, Y; μ] + Var[Y; μ] :=
  variance_sub hX hY

variable {ι : Type*} {s : Finset ι} {X : (i : ι) → Ω → ℝ}
/-
**ProbabilityTheory.variance_sum'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：variance_sum' [IsFiniteMeasure μ] (hX : forall i in s, MemLp (X i) 2 μ) : 
Var[∑ i in s, X i; μ] = ∑ i in s, ∑ j in s, cov[X i, X j; μ]
参数：hX : forall i in s, MemLp (X i) 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.covariance_self`：covariance_self {X : Ω -> Real} (hX :
 AEMeasurable X μ) : cov[X, X; μ] = Var[X; μ]
· 使用定理 `MeasureTheory.MemLp.aemeasurable`：∀ {α : Type u_1} {ε : Type u_2} {m0 : 
MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [inst_1 : Me
asurableSpace ε] [inst…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.memLp_finsetSum'`：memLp_finsetSum' [ContinuousAdd ε'] {ι} 
(s : Finset ι) {f : ι -> α -> ε'} (hf : forall i in s, MemLp (f i) p μ) : MemLp 
(∑ i in s, f i) p μ
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
· 使用引理 `ProbabilityTheory.covariance_sum_left'`：covariance_sum_left' (hX : foral
l i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) : cov[∑ i in s, X i, Y; μ] = ∑ i i
n s, cov[X i, Y; μ]
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `ProbabilityTheory.covariance_sum_right'`：covariance_sum_right' (hX : for
all i in s, MemLp (X i) 2 μ) (hY : MemLp Y 2 μ) : cov[Y, ∑ i in s, X i; μ] = ∑ i
 in s, cov[Y, X i; μ]
-/
lemma variance_sum' [IsFiniteMeasure μ] (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    Var[∑ i ∈ s, X i; μ] = ∑ i ∈ s, ∑ j ∈ s, cov[X i, X j; μ] := by
  rw [← covariance_self, covariance_sum_left' (by simpa)]
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [covariance_sum_right' (by simpa) (hX i hi)]
  · exact memLp_finsetSum' _ (by simpa)
  · exact (memLp_finsetSum' _ (by simpa)).aemeasurable
/-
**ProbabilityTheory.variance_sum** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：variance_sum [IsFiniteMeasure μ] [Fintype ι] (hX : forall i, MemLp (X i) 2
 μ) : Var[∑ i, X i; μ] = ∑ i, ∑ j, cov[X i, X j; μ]
参数：hX : forall i, MemLp (X i) 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.variance_sum'`：variance_sum' [IsFiniteMeasure μ] (hX :
 forall i in s, MemLp (X i) 2 μ) : Var[∑ i in s, X i; μ] = ∑ i in s, ∑ j in s, c
ov[X i, X j; μ]
-/
lemma variance_sum [IsFiniteMeasure μ] [Fintype ι] (hX : ∀ i, MemLp (X i) 2 μ) :
    Var[∑ i, X i; μ] = ∑ i, ∑ j, cov[X i, X j; μ] :=
  variance_sum' (fun _ _ ↦ hX _)
/-
**ProbabilityTheory.variance_fun_sum'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：variance_fun_sum' [IsFiniteMeasure μ] (hX : forall i in s, MemLp (X i) 2 μ
) : Var[fun ω => ∑ i in s, X i ω; μ] = ∑ i in s, ∑ j in s, cov[X i, X j; μ]
参数：hX : forall i in s, MemLp (X i) 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.variance_sum'`：variance_sum' [IsFiniteMeasure μ] (hX :
 forall i in s, MemLp (X i) 2 μ) : Var[∑ i in s, X i; μ] = ∑ i in s, ∑ j in s, c
ov[X i, X j; μ]
-/
lemma variance_fun_sum' [IsFiniteMeasure μ] (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    Var[fun ω ↦ ∑ i ∈ s, X i ω; μ] = ∑ i ∈ s, ∑ j ∈ s, cov[X i, X j; μ] := by
  convert! variance_sum' hX
  simp
/-
**ProbabilityTheory.variance_fun_sum** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：variance_fun_sum [IsFiniteMeasure μ] [Fintype ι] (hX : forall i, MemLp (X 
i) 2 μ) : Var[fun ω => ∑ i, X i ω; μ] = ∑ i, ∑ j, cov[X i, X j; μ]
参数：hX : forall i, MemLp (X i) 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.variance_sum`：variance_sum [IsFiniteMeasure μ] [Fintyp
e ι] (hX : forall i, MemLp (X i) 2 μ) : Var[∑ i, X i; μ] = ∑ i, ∑ j, cov[X i, X 
j; μ]
-/
lemma variance_fun_sum [IsFiniteMeasure μ] [Fintype ι] (hX : ∀ i, MemLp (X i) 2 μ) :
    Var[fun ω ↦ ∑ i, X i ω; μ] = ∑ i, ∑ j, cov[X i, X j; μ] := by
  convert! variance_sum hX
  simp

variable {X : Ω → ℝ}

@[simp]
/-
**ProbabilityTheory.variance_dirac** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：variance_dirac [MeasurableSingletonClass Ω] (x : Ω) : Var[X; Measure.dirac
 x] = 0
参数：x : Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.variance_eq_integral`：variance_eq_integral (hX : AEMea
surable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ
· 使用引理 `MeasureTheory.aemeasurable_dirac`：aemeasurable_dirac [MeasurableSingleto
nClass α] {a : α} {f : α -> β} : AEMeasurable f (Measure.dirac a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_dirac`：integral_dirac [MeasurableSpace α] [Measur
ableSingletonClass α] (f : α -> E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma variance_dirac [MeasurableSingletonClass Ω] (x : Ω) : Var[X; Measure.dirac x] = 0 := by
  rw [variance_eq_integral]
  · simp
  · exact aemeasurable_dirac
/-
**ProbabilityTheory.variance_map** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：variance_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {Y :
 Ω' -> Ω} (hX : AEMeasurable X (μ.map Y)) (hY : AEMeasurable Y μ) : Var[X; μ.map
 Y] = Var[X ∘ Y; μ]
参数：hX : AEMeasurable X (μ.map Y)；hY : AEMeasurable Y μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.variance_eq_integral`：variance_eq_integral (hX : AEMea
surable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.pow`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f : α → β} [inst_1 :…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `AEMeasurable.sub_const`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurab
leSpace G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   {μ : MeasureTh
eory.Measure…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `AEMeasurable.comp_aemeasurable`：comp_aemeasurable {f : α -> δ} {g : δ ->
 β} (hg : AEMeasurable g (μ.map f)) (hf : AEMeasurable f μ) : AEMeasurable (g ∘ 
f) μ
-/
lemma variance_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {Y : Ω' → Ω} (hX : AEMeasurable X (μ.map Y)) (hY : AEMeasurable Y μ) :
    Var[X; μ.map Y] = Var[X ∘ Y; μ] := by
  rw [variance_eq_integral hX, integral_map hY, variance_eq_integral (hX.comp_aemeasurable hY),
    integral_map hY]
  · congr
  · exact hX.aestronglyMeasurable
  · refine AEStronglyMeasurable.pow ?_ _
    exact AEMeasurable.aestronglyMeasurable (by fun_prop)
/-
**ProbabilityTheory._root_.MeasureTheory.MeasurePreserving.variance_fun_comp** 是
 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.MeasurePreserving.variance_fun_comp {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'} {X : Ω → Ω'}
    (hX : MeasurePreserving X μ ν) {f : Ω' → ℝ} (hf : AEMeasurable f ν) :
    Var[fun ω ↦ f (X ω); μ] = Var[f; ν] := by
  rw [← hX.map_eq, variance_map (hX.map_eq ▸ hf) hX.aemeasurable, Function.comp_def]
/-
**ProbabilityTheory.variance_map_equiv** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：variance_map_equiv {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'
} (X : Ω -> Real) (Y : Ω' ≃ᵐ Ω) : Var[X; μ.map Y] = Var[X ∘ Y; μ]
参数：X : Ω -> Real；Y : Ω' ≃ᵐ Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_map_equiv`：lintegral_map_equiv (f : β -> Real>=0
∞) (g : α ≃ᵐ β) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_map_equiv`：integral_map_equiv {β} [MeasurableSpac
e β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma variance_map_equiv {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    (X : Ω → ℝ) (Y : Ω' ≃ᵐ Ω) :
    Var[X; μ.map Y] = Var[X ∘ Y; μ] := by
  simp_rw [variance, evariance, lintegral_map_equiv, integral_map_equiv, Function.comp_apply]
/-
**ProbabilityTheory.variance_id_map** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：variance_id_map (hX : AEMeasurable X μ) : Var[id; μ.map X] = Var[X; μ]
参数：hX : AEMeasurable X μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.variance_map`：variance_map {Ω' : Type*} {mΩ' : Measura
bleSpace Ω'} {μ : Measure Ω'} {Y : Ω' -> Ω} (hX : AEMeasurable X (μ.map Y)) (hY 
: AEMeasurable Y μ) …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma variance_id_map (hX : AEMeasurable X μ) : Var[id; μ.map X] = Var[X; μ] := by
  simp [variance_map measurable_id.aemeasurable hX]
/-
**ProbabilityTheory.variance_le_expectation_sq** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：variance_le_expectation_sq [IsProbabilityMeasure μ] {X : Ω -> Real} (hm : 
AEStronglyMeasurable X μ) : variance X μ <= μ[X ^ 2]
参数：hm : AEStronglyMeasurable X μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.variance_eq_sub`：variance_eq_sub [IsProbabilityMeasure
 μ] {X : Ω -> Real} (hX : MemLp X 2 μ) : variance X μ = μ[X ^ 2] - μ[X] ^ 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `ProbabilityTheory.variance.eq_1`：∀ {Ω : Type u_1} {mΩ : MeasurableSpace 
Ω} (X : Ω → ℝ) (μ : MeasureTheory.Measure Ω),   ProbabilityTheory.variance X μ =
 (ProbabilityTheory.e…
· 使用定理 `ProbabilityTheory.evariance_eq_lintegral_ofReal`：evariance_eq_lintegral_
ofReal : evariance X μ = ∫⁻ ω, ENNReal.ofReal ((X ω - μ[X]) ^ 2) ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `ContinuousMul.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Mul γ] [Con…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `AEMeasurable.sub_const`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurab
leSpace G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   {μ : MeasureTh
eory.Measure…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
（共 55 条，此处仅展示前 30 条）
-/
theorem variance_le_expectation_sq [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hm : AEStronglyMeasurable X μ) : variance X μ ≤ μ[X ^ 2] := by
  by_cases hX : MemLp X 2 μ
  · rw [variance_eq_sub hX]
    simp only [sq_nonneg, sub_le_self_iff]
  rw [variance, evariance_eq_lintegral_ofReal, ← integral_eq_lintegral_of_nonneg_ae]
  · by_cases hint : Integrable X μ; swap
    · simp only [integral_undef hint, Pi.pow_apply, sub_zero]
      exact le_rfl
    · rw [integral_undef]
      · exact integral_nonneg fun a => sq_nonneg _
      intro h
      have A : MemLp (X - fun ω : Ω => μ[X]) 2 μ :=
        (memLp_two_iff_integrable_sq (by fun_prop)).2 h
      have B : MemLp (fun _ : Ω => μ[X]) 2 μ := memLp_const _
      apply hX
      convert! A.add B
      simp
  · exact Eventually.of_forall fun x => sq_nonneg _
  · exact (AEMeasurable.pow_const (hm.aemeasurable.sub_const _) _).aestronglyMeasurable
/-
**ProbabilityTheory.evariance_def'** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：evariance_def' [IsProbabilityMeasure μ] {X : Ω -> Real} (hX : AEStronglyMe
asurable X μ) : evariance X μ = (∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂μ) - ENNReal.ofReal (μ[X] ^ 2
)
参数：hX : AEStronglyMeasurable X μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.ofReal_variance`：ofReal_variance [IsFiniteMeasure μ] (
hX : MemLp X 2 μ) : .ofReal (variance X μ) = evariance X μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `ProbabilityTheory.variance_eq_sub`：variance_eq_sub [IsProbabilityMeasure
 μ] {X : Ω -> Real} (hX : MemLp X 2 μ) : variance X μ = μ[X ^ 2] - μ[X] ^ 2
· 使用定理 `ENNReal.ofReal_sub`：ofReal_sub (p : Real) {q : Real} (hq : 0 <= q) : ENN
Real.ofReal (p - q) = ENNReal.ofReal p - ENNReal.ofReal q
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `MeasureTheory.lintegral_coe_eq_integral`：lintegral_coe_eq_integral (f : 
α -> Real>=0) (hfi : Integrable (fun x => (f x : Real)) μ) : ∫⁻ a, f a ∂μ = ENNR
eal.ofReal (∫ a, f a ∂μ)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nnnorm_pow`：nnnorm_pow (a : α) (n : Nat) : ‖a ^ n‖₊ = ‖a‖₊ ^ n
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `MeasureTheory.MemLp.integrable_sq`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.MemLp f 2 μ → Mea
sureTheory.Integrable (…
· 使用定理 `MeasureTheory.MemLp.abs`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} {p : ENNReal}   [inst : NormedAddCommGrou
p E] [inst_1 …
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ProbabilityTheory.evariance_eq_top`：evariance_eq_top [IsFiniteMeasure μ]
 (hXm : AEStronglyMeasurable X μ) (hX : ¬MemLp X 2 μ) : evariance X μ = ∞
· 使用定理 `ENNReal.sub_eq_top_iff`：∀ {a b : ENNReal}, a - b = ⊤ ↔ a = ⊤ ∧ b ≠ ⊤
· 使用定理 `ENNReal.rpow_natCast`：rpow_natCast (x : Real>=0∞) (n : Nat) : x ^ (n : R
eal) = x ^ n
· 使用引理 `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal`：eLpNorm_eq_lintegr
al_rpow_enorm_toReal (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε} : e
LpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ…
（共 46 条，此处仅展示前 30 条）
-/
theorem evariance_def' [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ) :
    evariance X μ = (∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂μ) - ENNReal.ofReal (μ[X] ^ 2) := by
  by_cases hℒ : MemLp X 2 μ
  · rw [← ofReal_variance hℒ, variance_eq_sub hℒ, ENNReal.ofReal_sub _ (sq_nonneg _)]
    congr
    simp_rw [← enorm_pow, enorm]
    rw [lintegral_coe_eq_integral]
    · simp
    · simpa using hℒ.abs.integrable_sq
  · symm
    rw [evariance_eq_top hX hℒ, ENNReal.sub_eq_top_iff]
    refine ⟨?_, ENNReal.ofReal_ne_top⟩
    rw [MemLp, not_and] at hℒ
    specialize hℒ hX
    simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, not_lt,
      top_le_iff, ENNReal.toReal_ofNat, one_div, ENNReal.rpow_eq_top_iff, inv_lt_zero, inv_pos,
      and_true, or_iff_not_imp_left, not_and_or, zero_lt_two] at hℒ
    exact mod_cast hℒ fun _ => zero_le_two

/-- **Chebyshev's inequality** for `ℝ≥0∞`-valued variance. -/
/-
**ProbabilityTheory.meas_ge_le_evariance_div_sq** 是 Mathlib 中的一个定理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：meas_ge_le_evariance_div_sq {X : Ω -> Real} (hX : AEStronglyMeasurable X μ
) {c : Real>=0} (hc : c != 0) : μ {ω | ↑c <= |X ω - μ[X]|} <= evariance X μ / c 
^ 2
参数：hX : AEStronglyMeasurable X μ；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `ENNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal`：eLpNorm_eq_lintegr
al_rpow_enorm_toReal (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε} : e
LpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ…
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.toReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).t
oReal = OfNat.ofNat n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.inv_pow`：∀ {a : ENNReal} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.rpow_two`：rpow_two (x : Real>=0∞) : x ^ (2 : Real) = x ^ 2
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm`：meas_ge_le_mul_pow_eLpNo
rm_enorm (hp_ne_zero : p != 0) (hp_ne_top : p != ∞) {f : α -> ε'} (hf : AEStrong
lyMeasurable f μ) {ε : Real>=0∞} (hε…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
**Chebyshev's inequality** for `ℝ≥0∞`-valued variance.
-/
theorem meas_ge_le_evariance_div_sq {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ) {c : ℝ≥0}
    (hc : c ≠ 0) : μ {ω | ↑c ≤ |X ω - μ[X]|} ≤ evariance X μ / c ^ 2 := by
  have A : (c : ℝ≥0∞) ≠ 0 := by rwa [Ne, ENNReal.coe_eq_zero]
  have B : AEStronglyMeasurable (fun _ : Ω => μ[X]) μ := aestronglyMeasurable_const
  convert!
      meas_ge_le_mul_pow_eLpNorm_enorm μ two_ne_zero ENNReal.ofNat_ne_top (hX.sub B) A (by simp)
    using 1
  · norm_cast
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, one_div, Pi.sub_apply]
  rw [div_eq_mul_inv, ENNReal.inv_pow, mul_comm, ENNReal.rpow_two]
  congr
  simp_rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), ENNReal.rpow_two,
    ENNReal.rpow_one, evariance]

/-- **Chebyshev's inequality**: one can control the deviation probability of a real random variable
from its expectation in terms of the variance. -/
/-
**ProbabilityTheory.meas_ge_le_variance_div_sq** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：meas_ge_le_variance_div_sq [IsFiniteMeasure μ] {X : Ω -> Real} (hX : MemLp
 X 2 μ) {c : Real} (hc : 0 < c) : μ {ω | c <= |X ω - μ[X]|} <= ENNReal.ofReal (v
ariance X μ / c ^ 2)
参数：hX : MemLp X 2 μ；hc : 0 < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_div_of_pos`：ofReal_div_of_pos {x y : Real} (hy : 0 < y) :
 ENNReal.ofReal (x / y) = ENNReal.ofReal x / ENNReal.ofReal y
· 使用定理 `sq_pos_of_ne_zero`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Linear
Order R] [IsStrictOrderedRing R] [ExistsAddOfLE R] {a : R},   a ≠ 0 → 0 < a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.MemLp.ofReal_variance_eq`：∀ {Ω : Type u_1} {mΩ : Measurabl
eSpace Ω} {X : Ω → ℝ} {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasu
re μ],   MeasureTheory.MemLp…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.ofReal_pow`：ofReal_pow {p : Real} (hp : 0 <= p) (n : Nat) : ENNR
eal.ofReal (p ^ n) = ENNReal.ofReal p ^ n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ProbabilityTheory.meas_ge_le_evariance_div_sq`：meas_ge_le_evariance_div_
sq {X : Ω -> Real} (hX : AEStronglyMeasurable X μ) {c : Real>=0} (hc : c != 0) :
 μ {ω | ↑c <= |X ω - μ[X]|} <= evar…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
**Chebyshev's inequality**: one can control the deviation probability of a real 
random variable
from its expectation in terms of the variance.
-/
theorem meas_ge_le_variance_div_sq [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) {c : ℝ}
    (hc : 0 < c) : μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (variance X μ / c ^ 2) := by
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_ne_zero hc.ne.symm), hX.ofReal_variance_eq]
  convert! @meas_ge_le_evariance_div_sq _ _ _ _ hX.1 c.toNNReal (by simp [hc]) using 1
  · simp
  · rw [ENNReal.ofReal_pow hc.le]
    rfl

/-- The variance of the sum of two independent random variables is the sum of the variances. -/
nonrec theorem IndepFun.variance_add {X Y : Ω → ℝ} (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) (h : X ⟂ᵢ[μ] Y) : Var[X + Y; μ] = Var[X; μ] + Var[Y; μ] := by
  by_cases h' : X =ᵐ[μ] 0
  · rw [variance_congr h', variance_congr h'.add_right]
    simp
  have := hX.isProbabilityMeasure_of_indepFun X Y (by simp) (by simp) h' h
  rw [variance_add hX hY, h.covariance_eq_zero hX hY]
  simp

/-- The variance of the sum of two independent random variables is the sum of the variances. -/
/-
**ProbabilityTheory.IndepFun.variance_fun_add** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.IndepFun`。
形式化陈述：∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {X
 Y : Ω → ℝ},   MeasureTheory.MemLp X 2 μ →     MeasureTheory.MemLp Y 2 μ →      
 ProbabilityTheory.IndepFun X Y μ →         ProbabilityTheory.variance (fun ω =>
 X ω + Y ω) μ =           ProbabilityTheory.variance X μ + ProbabilityTheory.var
iance Y μ
参数：fun ω => X ω + Y ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ProbabilityTheory.IndepFun.variance_add`：∀ {Ω : Type u_1} {mΩ : Measurab
leSpace Ω} {μ : MeasureTheory.Measure Ω} {X Y : Ω → ℝ},   MeasureTheory.MemLp X 
2 μ →     MeasureTheory.MemLp…

--- 原说明 ---
The variance of the sum of two independent random variables is the sum of the va
riances.
-/
lemma IndepFun.variance_fun_add {X Y : Ω → ℝ} (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) (h : X ⟂ᵢ[μ] Y) : Var[fun ω ↦ X ω + Y ω; μ] = Var[X; μ] + Var[Y; μ] :=
  h.variance_add hX hY

/-- The variance of a finite sum of pairwise independent random variables is the sum of the
variances. -/
nonrec theorem IndepFun.variance_sum {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι}
    (hs : ∀ i ∈ s, MemLp (X i) 2 μ)
    (h : Set.Pairwise ↑s fun i j => X i ⟂ᵢ[μ] X j) :
    variance (∑ i ∈ s, X i) μ = ∑ i ∈ s, variance (X i) μ := by
  by_cases h'' : ∀ i ∈ s, X i =ᵐ[μ] 0
  · rw [variance_congr (Y := 0), variance_zero]
    · symm
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      simp [variance_congr (h'' i hi)]
    · have := fun (i : s) ↦ h'' i.1 i.2
      filter_upwards [ae_all_iff.2 this] with ω hω
      simp only [Finset.sum_apply, Pi.zero_apply]
      exact Finset.sum_eq_zero fun i hi ↦ hω ⟨i, hi⟩
  obtain ⟨j, hj1, hj2⟩ := not_forall₂.1 h''
  obtain rfl | h' := s.eq_singleton_or_nontrivial hj1
  · simp
  obtain ⟨k, hk1, hk2⟩ := h'.exists_ne j
  have := (hs j hj1).isProbabilityMeasure_of_indepFun (X j) (X k) (by simp) (by simp) hj2
    (h hj1 hk1 hk2.symm)
  rw [variance_sum' hs]
  refine Finset.sum_congr rfl (fun i hi ↦ ?_)
  rw [← covariance_self (hs i hi).aemeasurable]
  refine Finset.sum_eq_single_of_mem i hi fun j hj1 hj2 ↦ ?_
  exact (h hi hj1 hj2.symm).covariance_eq_zero (hs i hi) (hs j hj1)

/-
**ProbabilityTheory.variance_sum_pi** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：variance_sum_pi [Fintype ι] {Ω : ι -> Type*} {mΩ : forall i, MeasurableSpa
ce (Ω i)} {μ : (i : ι) -> Measure (Ω i)} [forall i, IsProbabilityMeasure (μ i)] 
{X : Π i, Ω i -> Real} (h : forall i, MemLp (X i) 2 (μ i)) : Var[∑ i, fun ω => X
 i (ω i); Measure.pi μ] = ∑ i, Var[X i; μ i]
参数：Ω i；i : ι；Ω i；μ i；h : forall i, MemLp (X i) 2 (μ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IndepFun.variance_sum`：∀ {Ω : Type u_1} {mΩ : Measurab
leSpace Ω} {μ : MeasureTheory.Measure Ω} {ι : Type u_3} {X : ι → Ω → ℝ} {s : Fin
set ι},   (∀ i ∈ s, MeasureTh…
· 使用定理 `MeasureTheory.MemLp.comp_measurePreserving`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst
 : TopologicalSpace ε] [inst_1 :…
· 使用定理 `MeasureTheory.measurePreserving_eval`：∀ {ι : Type u_1} {α : ι → Type u_3
} [inst : Fintype ι] [inst_1 : (i : ι) → MeasurableSpace (α i)]   (μ : (i : ι) →
 MeasureTheory.Measure (α …
· 使用定理 `ProbabilityTheory.iIndepFun.indepFun`：∀ {Ω : Type u_1} {ι : Type u_2} {_
mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type u_6}   {m : 
(x : ι) → MeasurableSpace …
· 使用引理 `ProbabilityTheory.iIndepFun_pi`：iIndepFun_pi (mX : forall i, AEMeasurabl
e (X i) (μ i)) : iIndepFun (fun i ω => X i (ω i)) (Measure.pi μ)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.variance_map`：variance_map {Ω' : Type*} {mΩ' : Measura
bleSpace Ω'} {μ : Measure Ω'} {Y : Ω' -> Ω} (hX : AEMeasurable X (μ.map Y)) (hY 
: AEMeasurable Y μ) …
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
-/
lemma variance_sum_pi [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
    {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {X : Π i, Ω i → ℝ} (h : ∀ i, MemLp (X i) 2 (μ i)) :
    Var[∑ i, fun ω ↦ X i (ω i); Measure.pi μ] = ∑ i, Var[X i; μ i] := by
  rw [IndepFun.variance_sum]
  · congr with i
    change Var[(X i) ∘ (fun ω ↦ ω i); Measure.pi μ] = _
    rw [← variance_map, (measurePreserving_eval _ i).map_eq]
    · rw [(measurePreserving_eval _ i).map_eq]
      exact (h i).aestronglyMeasurable.aemeasurable
    · exact Measurable.aemeasurable (by fun_prop)
  · exact fun i _ ↦ (h i).comp_measurePreserving (measurePreserving_eval _ i)
  · exact fun i _ j _ hij ↦
      (iIndepFun_pi fun i ↦ (h i).aestronglyMeasurable.aemeasurable).indepFun hij

/-- **The Bhatia-Davis inequality on variance**

The variance of a random variable `X` satisfying `a ≤ X ≤ b` almost everywhere is at most
`(b - 𝔼 X) * (𝔼 X - a)`. -/
/-
**ProbabilityTheory.variance_le_sub_mul_sub** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：variance_le_sub_mul_sub [IsProbabilityMeasure μ] {a b : Real} {X : Ω -> Re
al} (h : forallᵐ ω ∂μ, X ω in Set.Icc a b) (hX : AEMeasurable X μ) : variance X 
μ <= (b - μ[X]) * (μ[X] - a)
参数：h : forallᵐ ω ∂μ, X ω in Set.Icc a b；hX : AEMeasurable X μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `MeasureTheory.MemLp.integrable_sq`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.MemLp f 2 μ → Mea
sureTheory.Integrable (…
· 使用定理 `MeasureTheory.memLp_of_bounded`：memLp_of_bounded [IsFiniteMeasure μ] {a 
b : Real} {f : α -> Real} (h : forallᵐ x ∂μ, f x in Set.Icc a b) (hX : AEStrongl
yMeasurable f μ) (p …
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.Integrable.mono'`：∀ {α : Type u_1} {β : Type u_2} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f
 : α → β} {g : α → ℝ…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `abs_le_max_abs_abs`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : L
inearOrder G] [IsOrderedAddMonoid G] {a b c : G},   a ≤ b → b ≤ c → |b| ≤ max |a
| |c|
· 使用引理 `MeasureTheory.integral_nonneg_of_ae`：integral_nonneg_of_ae {f : α -> E} 
(hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x, f x ∂μ
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
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
（共 98 条，此处仅展示前 30 条）

--- 原说明 ---
**The Bhatia-Davis inequality on variance**

The variance of a random variable `X` satisfying `a ≤ X ≤ b` almost everywhere i
s at most
`(b - 𝔼 X) * (𝔼 X - a)`.
-/
lemma variance_le_sub_mul_sub [IsProbabilityMeasure μ] {a b : ℝ} {X : Ω → ℝ}
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hX : AEMeasurable X μ) :
    variance X μ ≤ (b - μ[X]) * (μ[X] - a) := by
  have ha : ∀ᵐ ω ∂μ, a ≤ X ω := h.mono fun ω h => h.1
  have hb : ∀ᵐ ω ∂μ, X ω ≤ b := h.mono fun ω h => h.2
  have hX_int₂ : Integrable (fun ω ↦ -X ω ^ 2) μ :=
    (memLp_of_bounded h hX.aestronglyMeasurable 2).integrable_sq.neg
  have hX_int₁ : Integrable (fun ω ↦ (a + b) * X ω) μ :=
    ((integrable_const (max |a| |b|)).mono' hX.aestronglyMeasurable
      (by filter_upwards [ha, hb] with ω using abs_le_max_abs_abs)).const_mul (a + b)
  have h0 : 0 ≤ -μ[X ^ 2] + (a + b) * μ[X] - a * b :=
    calc
      _ ≤ ∫ ω, (b - X ω) * (X ω - a) ∂μ := by
        apply integral_nonneg_of_ae
        filter_upwards [ha, hb] with ω ha' hb'
        exact mul_nonneg (by linarith : 0 ≤ b - X ω) (by linarith : 0 ≤ X ω - a)
      _ = ∫ ω, -X ω ^ 2 + (a + b) * X ω - a * b ∂μ :=
        integral_congr_ae <| ae_of_all μ fun ω ↦ by ring
      _ = ∫ ω, - X ω ^ 2 + (a + b) * X ω ∂μ - ∫ _, a * b ∂μ :=
        integral_sub (by fun_prop) (integrable_const (a * b))
      _ = ∫ ω, - X ω ^ 2 + (a + b) * X ω ∂μ - a * b := by simp
      _ = - μ[X ^ 2] + (a + b) * μ[X] - a * b := by
        simp [← integral_neg, ← integral_const_mul, integral_add hX_int₂ hX_int₁]
  calc
    _ ≤ (a + b) * μ[X] - a * b - μ[X] ^ 2 := by
      rw [variance_eq_sub (memLp_of_bounded h hX.aestronglyMeasurable 2)]
      linarith
    _ = (b - μ[X]) * (μ[X] - a) := by ring

/-- **Popoviciu's inequality on variances**

The variance of a random variable `X` satisfying `a ≤ X ≤ b` almost everywhere is at most
`((b - a) / 2) ^ 2`. -/
/-
**ProbabilityTheory.variance_le_sq_of_bounded** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：variance_le_sq_of_bounded [IsProbabilityMeasure μ] {a b : Real} {X : Ω -> 
Real} (h : forallᵐ ω ∂μ, X ω in Set.Icc a b) (hX : AEMeasurable X μ) : variance 
X μ <= ((b - a) / 2) ^ 2
参数：h : forallᵐ ω ∂μ, X ω in Set.Icc a b；hX : AEMeasurable X μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.variance_le_sub_mul_sub`：variance_le_sub_mul_sub [IsPr
obabilityMeasure μ] {a b : Real} {X : Ω -> Real} (h : forallᵐ ω ∂μ, X ω in Set.I
cc a b) (hX : AEMeasurable X μ)…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
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
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 77 条，此处仅展示前 30 条）

--- 原说明 ---
**Popoviciu's inequality on variances**

The variance of a random variable `X` satisfying `a ≤ X ≤ b` almost everywhere i
s at most
`((b - a) / 2) ^ 2`.
-/
lemma variance_le_sq_of_bounded [IsProbabilityMeasure μ] {a b : ℝ} {X : Ω → ℝ}
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hX : AEMeasurable X μ) :
    variance X μ ≤ ((b - a) / 2) ^ 2 :=
  calc
    _ ≤ (b - μ[X]) * (μ[X] - a) := variance_le_sub_mul_sub h hX
    _ = ((b - a) / 2) ^ 2 - (μ[X] - (b + a) / 2) ^ 2 := by ring
    _ ≤ ((b - a) / 2) ^ 2 := sub_le_self _ (sq_nonneg _)

section Prod

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {X : Ω → ℝ} {Y : Ω' → ℝ}

/-
**ProbabilityTheory.variance_add_prod** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：variance_add_prod (hfμ : MemLp X 2 μ) (hgν : MemLp Y 2 ν) : Var[fun p => X
 p.1 + Y p.2; μ.prod ν] = Var[X; μ] + Var[Y; ν]
参数：hfμ : MemLp X 2 μ；hgν : MemLp Y 2 ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProbabilityTheory.IndepFun.variance_fun_add`：∀ {Ω : Type u_1} {mΩ : Meas
urableSpace Ω} {μ : MeasureTheory.Measure Ω} {X Y : Ω → ℝ},   MeasureTheory.MemL
p X 2 μ →     MeasureTheory.MemLp…
· 使用定理 `MeasureTheory.MemLp.comp_fst`：∀ {α : Type u_1} {β : Type u_2} {ε : Type 
u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   [inst : TopologicalSpac
e ε] [inst_1 : Con…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.MemLp.comp_snd`：∀ {α : Type u_1} {β : Type u_2} {ε : Type 
u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   [inst : TopologicalSpac
e ε] [inst_1 : Con…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用引理 `ProbabilityTheory.indepFun_prod₀`：indepFun_prod₀ (mX : AEMeasurable X μ)
 (mY : AEMeasurable Y ν) : (fun ω => X ω.1) ⟂ᵢ[μ.prod ν] (fun ω => Y ω.2)
· 使用定理 `MeasureTheory.MemLp.aemeasurable`：∀ {α : Type u_1} {ε : Type u_2} {m0 : 
MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [inst_1 : Me
asurableSpace ε] [inst…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.MeasurePreserving.variance_fun_comp`：∀ {Ω : Type u_1} {mΩ 
: MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {Ω' : Type u_3} {mΩ' : Measur
ableSpace Ω'}   {ν : MeasureTheory.Meas…
· 使用定理 `MeasureTheory.measurePreserving_fst`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure 
α}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.measurePreserving_snd`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure 
α}   {ν : MeasureTheory.M…
-/
lemma variance_add_prod (hfμ : MemLp X 2 μ) (hgν : MemLp Y 2 ν) :
    Var[fun p ↦ X p.1 + Y p.2; μ.prod ν] = Var[X; μ] + Var[Y; ν] := by
  refine (IndepFun.variance_fun_add (hfμ.comp_fst ν) (hgν.comp_snd μ) ?_).trans ?_
  · exact indepFun_prod₀ hfμ.aemeasurable hgν.aemeasurable
  · rw [measurePreserving_fst.variance_fun_comp hfμ.aemeasurable,
      measurePreserving_snd.variance_fun_comp hgν.aemeasurable]

end Prod

section NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {mE : MeasurableSpace E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {mF : MeasurableSpace F}
  {μ : Measure E} [IsProbabilityMeasure μ] {ν : Measure F} [IsProbabilityMeasure ν]

/-
**ProbabilityTheory.variance_dual_prod'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：variance_dual_prod' {L : StrongDual Real (E × F)} (hLμ : MemLp (L.comp (.i
nl Real E F)) 2 μ) (hLν : MemLp (L.comp (.inr Real E F)) 2 ν) : Var[L; μ.prod ν]
 = Var[L.comp (.inl Real E F); μ] + Var[L.comp (.inr Real E F); ν]
参数：E × F；hLμ : MemLp (L.comp (.inl Real E F)) 2 μ；hLν : MemLp (L.comp (.inr Real
 E F)) 2 ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousLinearMap.comp_inl_add_comp_inr`：comp_inl_add_comp_inr (L : M₁
 × M₂ ->L[R] M₃) (v : M₁ × M₂) : L.comp (.inl R M₁ M₂) v.1 + L.comp (.inr R M₁ M
₂) v.2 = L v
· 使用引理 `ProbabilityTheory.variance_add_prod`：variance_add_prod (hfμ : MemLp X 2 
μ) (hgν : MemLp Y 2 ν) : Var[fun p => X p.1 + Y p.2; μ.prod ν] = Var[X; μ] + Var
[Y; ν]
-/
lemma variance_dual_prod' {L : StrongDual ℝ (E × F)}
    (hLμ : MemLp (L.comp (.inl ℝ E F)) 2 μ) (hLν : MemLp (L.comp (.inr ℝ E F)) 2 ν) :
    Var[L; μ.prod ν] = Var[L.comp (.inl ℝ E F); μ] + Var[L.comp (.inr ℝ E F); ν] := by
  have : L = fun x : E × F ↦ L.comp (.inl ℝ E F) x.1 + L.comp (.inr ℝ E F) x.2 := by
    ext; rw [L.comp_inl_add_comp_inr]
  rw [this, variance_add_prod hLμ hLν]
/-
**ProbabilityTheory.variance_dual_prod** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：variance_dual_prod {L : StrongDual Real (E × F)} (hLμ : MemLp id 2 μ) (hLν
 : MemLp id 2 ν) : Var[L; μ.prod ν] = Var[L.comp (.inl Real E F); μ] + Var[L.com
p (.inr Real E F); ν]
参数：E × F；hLμ : MemLp id 2 μ；hLν : MemLp id 2 ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ProbabilityTheory.variance_dual_prod'`：variance_dual_prod' {L : StrongDu
al Real (E × F)} (hLμ : MemLp (L.comp (.inl Real E F)) 2 μ) (hLν : MemLp (L.comp
 (.inr Real E F)) 2 ν) : Va…
· 使用定理 `ContinuousLinearMap.comp_memLp'`：comp_memLp' (L : E ->SL[σ] F) {f : α ->
 E} (hf : MemLp f p μ) : MemLp (L ∘ f) p μ
-/
lemma variance_dual_prod {L : StrongDual ℝ (E × F)} (hLμ : MemLp id 2 μ) (hLν : MemLp id 2 ν) :
    Var[L; μ.prod ν] = Var[L.comp (.inl ℝ E F); μ] + Var[L.comp (.inr ℝ E F); ν] :=
  variance_dual_prod' (ContinuousLinearMap.comp_memLp' _ hLμ)
    (ContinuousLinearMap.comp_memLp' _ hLν)

end NormedSpace

end ProbabilityTheory

