/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Geometric distributions

We define the geometric distributions over natural numbers. For `0 < p ≤ 1`, `geometricMeasure p`
is the measure which to `{n}` associates `(1 - p) ^ n * n`.

As the parameter `p` needs to lie between `0` and `1`, we define `geometricMeasure p` with
`p : unitInterval`.

Imagine a certain experience which has success probability `p`. If you repeat this experience
infinitely many times and independently, the number of failures before the first success
follows a geometric distribution with parameter `p`.

## Main definition

* `geometricMeasure p`: a geometric measure on a semiring `R`,
  parametrized by its success probability `p`.

## Implementation note

To avoid having to carry around a hypothesis `p ≠ 0`, we define
`geometricMeasure 0 := Measure.dirac 0`. That way `IsProbabilityMeasure (geometricMeasure p)`
can be automatically inferred.

## Tags

geometric distribution
-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

variable {p : unitInterval}

/-- The geometric measure with success probability `p` as a measure over `ℕ`. -/
/-
**ProbabilityTheory.geometricMeasure** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：geometricMeasure (p : unitInterval) : Measure Nat
参数：p : unitInterval。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The geometric measure with success probability `p` as a measure over `ℕ`.
-/
noncomputable def geometricMeasure (p : unitInterval) : Measure ℕ := if p ≠ 0
  then
    Measure.sum (fun n ↦ ENNReal.ofReal ((1 - p) ^ n * p) • .dirac n)
  else
    .dirac 0
/-
**ProbabilityTheory.geometricMeasure_eq** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：geometricMeasure_eq (hp : p != 0) : geometricMeasure p = Measure.sum (fun 
n => ENNReal.ofReal ((1 - p) ^ n * p) • .dirac n)
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma geometricMeasure_eq (hp : p ≠ 0) :
    geometricMeasure p =
      Measure.sum (fun n ↦ ENNReal.ofReal ((1 - p) ^ n * p) • .dirac n) :=
  if_pos hp

/-- The `positivty` tactic does not work for this goal. Use this lemma to rewrite
`(ENNReal.ofReal ((1 - p) ^ n * p)).toReal = (1 - p) ^ n * p`. -/
/-
**ProbabilityTheory.geometricMeasure_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：geometricMeasure_nonneg (p : unitInterval) n : 0 <= (1 - p : Real) ^ n * p
参数：p : unitInterval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The `positivty` tactic does not work for this goal. Use this lemma to rewrite
`(ENNReal.ofReal ((1 - p) ^ n * p)).toReal = (1 - p) ^ n * p`.
-/
lemma geometricMeasure_nonneg (p : unitInterval) n :
    0 ≤ (1 - p : ℝ) ^ n * p := mul_nonneg (pow_nonneg (by grind) n) p.2.1
/-
**ProbabilityTheory.geometricMeasure_pos** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：geometricMeasure_pos (h1 : p != 0) (h2 : p != 1) n : 0 < (1 - p : Real) ^ 
n * p
参数：h1 : p != 0；h2 : p != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
-/
lemma geometricMeasure_pos (h1 : p ≠ 0) (h2 : p ≠ 1) n :
    0 < (1 - p : ℝ) ^ n * p := mul_pos (pow_pos (by grind) n) (by grind)
/-
**ProbabilityTheory.geometricMeasure_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：geometricMeasure_singleton (hp : p != 0) n : geometricMeasure p {n} = ENNR
eal.ofReal ((1 - p) ^ n * p)
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.geometricMeasure_eq`：geometricMeasure_eq (hp : p != 0)
 : geometricMeasure p = Measure.sum (fun n => ENNReal.ofReal ((1 - p) ^ n * p) •
 .dirac n)
· 使用引理 `MeasureTheory.Measure.sum_smul_dirac_singleton`：sum_smul_dirac_singleton
 [MeasurableSingletonClass α] {f : α -> Real>=0∞} {a : α} : sum (fun b : α => f 
b • dirac b) {a} = f a
-/
lemma geometricMeasure_singleton (hp : p ≠ 0) n :
    geometricMeasure p {n} = ENNReal.ofReal ((1 - p) ^ n * p) := by
  rw [geometricMeasure_eq hp, Measure.sum_smul_dirac_singleton]
/-
**ProbabilityTheory.geometricMeasure_real_singleton** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：geometricMeasure_real_singleton (hp : p != 0) n : (geometricMeasure p).rea
l {n} = (1 - p) ^ n * p
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用引理 `ProbabilityTheory.geometricMeasure_singleton`：geometricMeasure_singleton
 (hp : p != 0) n : geometricMeasure p {n} = ENNReal.ofReal ((1 - p) ^ n * p)
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用引理 `ProbabilityTheory.geometricMeasure_nonneg`：geometricMeasure_nonneg (p : 
unitInterval) n : 0 <= (1 - p : Real) ^ n * p
-/
lemma geometricMeasure_real_singleton (hp : p ≠ 0) n :
    (geometricMeasure p).real {n} = (1 - p) ^ n * p := by
  rw [measureReal_def, geometricMeasure_singleton hp,
    ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]
/-
**ProbabilityTheory.geometricMeasure_real_singleton_pos** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory`。
形式化陈述：geometricMeasure_real_singleton_pos (h1 : p != 0) (h2 : p != 1) n : 0 < (g
eometricMeasure p).real {n}
参数：h1 : p != 0；h2 : p != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.geometricMeasure_real_singleton`：geometricMeasure_real
_singleton (hp : p != 0) n : (geometricMeasure p).real {n} = (1 - p) ^ n * p
· 使用引理 `ProbabilityTheory.geometricMeasure_pos`：geometricMeasure_pos (h1 : p != 
0) (h2 : p != 1) n : 0 < (1 - p : Real) ^ n * p
-/
lemma geometricMeasure_real_singleton_pos (h1 : p ≠ 0) (h2 : p ≠ 1) n :
    0 < (geometricMeasure p).real {n} := by
  rw [geometricMeasure_real_singleton h1]
  exact geometricMeasure_pos h1 h2 n
/-
**ProbabilityTheory.hasSum_one_geometricMeasure** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：hasSum_one_geometricMeasure (hp : p != 0) : HasSum (fun n => (1 - p : Real
) ^ n * p) 1
参数：hp : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.mul_right`：HasSum.mul_right (a₂) (hf : HasSum f a₁ L) : HasSum (f
un i => f i * a₂) (a₁ * a₂) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `hasSum_geometric_of_lt_one`：hasSum_geometric_of_lt_one {r : Real} (h₁ : 
0 <= r) (h₂ : r < 1) : HasSum (fun n : Nat => r ^ n) (1 - r)⁻¹
-/
lemma hasSum_one_geometricMeasure (hp : p ≠ 0) :
    HasSum (fun n ↦ (1 - p : ℝ) ^ n * p) 1 := by
  convert! (hasSum_geometric_of_lt_one (r := 1 - p) (by grind) (by grind)).mul_right (p : ℝ)
  grind
/-
**ProbabilityTheory.isProbabilityMeasure_geometricMeasure** 是 Mathlib 中的一个实例，位于命
名空间 `ProbabilityTheory`。
形式化陈述：isProbabilityMeasure_geometricMeasure : IsProbabilityMeasure (geometricMea
sure p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.geometricMeasure.eq_1`：∀ (p : ↑unitInterval),   Probab
ilityTheory.geometricMeasure p =     if p ≠ 0 then MeasureTheory.Measure.sum fun
 n => ENNReal.ofReal ((1 - ↑p…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `HasSum.isProbabilityMeasure_sum_dirac`：∀ {δ : Type u_3} {ι : Type u_4} {
mδ : MeasurableSpace δ} {c : ι → ℝ} {d : ι → δ},   (∀ (i : ι), 0 ≤ c i) →     Ha
sSum c 1 →       MeasureThe…
· 使用引理 `ProbabilityTheory.geometricMeasure_nonneg`：geometricMeasure_nonneg (p : 
unitInterval) n : 0 <= (1 - p : Real) ^ n * p
· 使用引理 `ProbabilityTheory.hasSum_one_geometricMeasure`：hasSum_one_geometricMeasu
re (hp : p != 0) : HasSum (fun n => (1 - p : Real) ^ n * p) 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
-/
instance isProbabilityMeasure_geometricMeasure :
    IsProbabilityMeasure (geometricMeasure p) := by
  rw [geometricMeasure]
  split_ifs with h
  · exact (hasSum_one_geometricMeasure h).isProbabilityMeasure_sum_dirac
      (geometricMeasure_nonneg p)
  · infer_instance

section Integral

variable {E : Type*} [NormedAddCommGroup E] {f : ℕ → E}

/-
**ProbabilityTheory.integrable_geometricMeasure_iff** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：integrable_geometricMeasure_iff (hp : p != 0) : Integrable f (geometricMea
sure p) ↔ Summable (fun n => (1 - p : Real) ^ n * p * ‖f n‖)
参数：hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.geometricMeasure_eq`：geometricMeasure_eq (hp : p != 0)
 : geometricMeasure p = Measure.sum (fun n => ENNReal.ofReal ((1 - p) ^ n * p) •
 .dirac n)
· 使用引理 `MeasureTheory.integrable_sum_dirac_iff`：integrable_sum_dirac_iff (hc : f
orall i, c i != ∞) : Integrable f (Measure.sum (fun i => (c i) • .dirac (x i))) 
↔ Summable (fun i => (c i).t…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用引理 `ProbabilityTheory.geometricMeasure_nonneg`：geometricMeasure_nonneg (p : 
unitInterval) n : 0 <= (1 - p : Real) ^ n * p
-/
lemma integrable_geometricMeasure_iff (hp : p ≠ 0) :
    Integrable f (geometricMeasure p) ↔ Summable (fun n ↦ (1 - p : ℝ) ^ n * p * ‖f n‖) := by
  rw [geometricMeasure_eq hp, integrable_sum_dirac_iff (by simp)]
  congrm Summable (fun n ↦ ?_ * _)
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

variable [NormedSpace ℝ E]
/-
**ProbabilityTheory.hasSum_integral_geometricMeasure** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：hasSum_integral_geometricMeasure [CompleteSpace E] (hp : p != 0) (hf : Int
egrable f (geometricMeasure p)) : HasSum (fun n => ((1 - p : Real) ^ n * p) • f 
n) (∫ n, f n ∂geometricMeasure p)
参数：hp : p != 0；hf : Integrable f (geometricMeasure p)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用引理 `ProbabilityTheory.geometricMeasure_nonneg`：geometricMeasure_nonneg (p : 
unitInterval) n : 0 <= (1 - p : Real) ^ n * p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `ProbabilityTheory.geometricMeasure_eq`：geometricMeasure_eq (hp : p != 0)
 : geometricMeasure p = Measure.sum (fun n => ENNReal.ofReal ((1 - p) ^ n * p) •
 .dirac n)
· 使用引理 `MeasureTheory.hasSum_integral_sum_dirac`：hasSum_integral_sum_dirac [Comp
leteSpace E] (hc : forall i, c i != ∞) (hf : Summable (fun i => (c i).toReal * ‖
f (x i)‖)) : HasSum (fun i =>…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ProbabilityTheory.integrable_geometricMeasure_iff`：integrable_geometricM
easure_iff (hp : p != 0) : Integrable f (geometricMeasure p) ↔ Summable (fun n =
> (1 - p : Real) ^ n * p * ‖f n‖)
-/
lemma hasSum_integral_geometricMeasure [CompleteSpace E]
    (hp : p ≠ 0) (hf : Integrable f (geometricMeasure p)) :
    HasSum (fun n ↦ ((1 - p : ℝ) ^ n * p) • f n) (∫ n, f n ∂geometricMeasure p) := by
  have : (fun n ↦ ((1 - p : ℝ) ^ n * p) • f n) =
      fun n ↦ (ENNReal.ofReal ((1 - p) ^ n * p)).toReal • f n := by
    ext n; rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]
  rw [this, geometricMeasure_eq hp]
  apply hasSum_integral_sum_dirac (by simp)
  convert! (integrable_geometricMeasure_iff hp).1 hf with n
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

/-- If a function is integrable with respect to `geometricMeasure p`, then its integral
against this measure is given by its sum weighted by `(1 - p) ^ n * p`.

See `integral_geometricMeasure` for a version where the codomain is finite-dimensional
and does not require the integrability hypothesis. -/
/-
**ProbabilityTheory.integral_geometricMeasure'** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：integral_geometricMeasure' [CompleteSpace E] (hp : p != 0) (hf : Integrabl
e f (geometricMeasure p)) : ∫ n, f n ∂geometricMeasure p = ∑' n : Nat, ((1 - p :
 Real) ^ n * p) • f n
参数：hp : p != 0；hf : Integrable f (geometricMeasure p)。
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
· 使用引理 `ProbabilityTheory.hasSum_integral_geometricMeasure`：hasSum_integral_geom
etricMeasure [CompleteSpace E] (hp : p != 0) (hf : Integrable f (geometricMeasur
e p)) : HasSum (fun n => ((1 - p : Real)…

--- 原说明 ---
If a function is integrable with respect to `geometricMeasure p`, then its integ
ral
against this measure is given by its sum weighted by `(1 - p) ^ n * p`.

See `integral_geometricMeasure` for a version where the codomain is finite-dimen
sional
and does not require the integrability hypothesis.
-/
lemma integral_geometricMeasure' [CompleteSpace E] (hp : p ≠ 0)
    (hf : Integrable f (geometricMeasure p)) :
    ∫ n, f n ∂geometricMeasure p = ∑' n : ℕ, ((1 - p : ℝ) ^ n * p) • f n :=
  (hasSum_integral_geometricMeasure hp hf).tsum_eq.symm

/-- The integral of a function taking values in a finite-dimensional space
against `geometricMeasure p` is given by its sum weighted by `(1 - p) ^ n * p`. This version
does not require integrability, as the integral exists if and only if the sum exists, and otherwise
they are both defined to be zero.

See `integral_geometricMeasure'` with a general codomain which assumes integrability. -/
/-
**ProbabilityTheory.integral_geometricMeasure** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：integral_geometricMeasure [FiniteDimensional Real E] (hp : p != 0) (f : Na
t -> E) : ∫ n, f n ∂geometricMeasure p = ∑' n : Nat, ((1 - p : Real) ^ n * p) • 
f n
参数：hp : p != 0；f : Nat -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.geometricMeasure_eq`：geometricMeasure_eq (hp : p != 0)
 : geometricMeasure p = Measure.sum (fun n => ENNReal.ofReal ((1 - p) ^ n * p) •
 .dirac n)
· 使用引理 `MeasureTheory.integral_sum_dirac`：integral_sum_dirac [FiniteDimensional 
Real E] (hc : forall i, c i != ∞) : ∫ x, f x ∂Measure.sum (fun i => (c i) • .dir
ac (x i)) = ∑' i, (c i…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用引理 `ProbabilityTheory.geometricMeasure_nonneg`：geometricMeasure_nonneg (p : 
unitInterval) n : 0 <= (1 - p : Real) ^ n * p

--- 原说明 ---
The integral of a function taking values in a finite-dimensional space
against `geometricMeasure p` is given by its sum weighted by `(1 - p) ^ n * p`. 
This version
does not require integrability, as the integral exists if and only if the sum ex
ists, and otherwise
they are both defined to be zero.

See `integral_geometricMeasure'` with a general codomain which assumes integrabi
lity.
-/
lemma integral_geometricMeasure [FiniteDimensional ℝ E] (hp : p ≠ 0) (f : ℕ → E) :
    ∫ n, f n ∂geometricMeasure p = ∑' n : ℕ, ((1 - p : ℝ) ^ n * p) • f n := by
  rw [geometricMeasure_eq hp, integral_sum_dirac (by simp)]
  congr with n
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

end Integral

section GeometricPMF

variable {p : ℝ}

/-- The pmf of the geometric distribution depending on its success probability. -/
@[deprecated geometricMeasure (since := "2026-03-08")]
noncomputable
/-
**ProbabilityTheory.geometricPMFReal** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：geometricPMFReal (p : Real) (n : Nat) : Real
参数：p : Real；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def geometricPMFReal (p : ℝ) (n : ℕ) : ℝ := (1 - p) ^ n * p

@[deprecated hasSum_one_geometricMeasure (since := "2026-03-08")]
/-
**ProbabilityTheory.geometricPMFRealSum** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：geometricPMFRealSum (hp_pos : 0 < p) (hp_le_one : p <= 1) : HasSum (fun n 
=> geometricPMFReal p n) 1
参数：hp_pos : 0 < p；hp_le_one : p <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasSum_geometric_of_lt_one`：hasSum_geometric_of_lt_one {r : Real} (h₁ : 
0 <= r) (h₂ : r < 1) : HasSum (fun n : Nat => r ^ n) (1 - r)⁻¹
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_lt_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] (a : α) {b : α}, 0 < b → a - b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `hasSum_mul_right_iff`：hasSum_mul_right_iff (h : a₂ != 0) : HasSum (fun i
 => f i * a₂) (a₁ * a₂) L ↔ HasSum f a₁ L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
-/
lemma geometricPMFRealSum (hp_pos : 0 < p) (hp_le_one : p ≤ 1) :
    HasSum (fun n ↦ geometricPMFReal p n) 1 := by
  unfold geometricPMFReal
  have := hasSum_geometric_of_lt_one (sub_nonneg.mpr hp_le_one) (sub_lt_self 1 hp_pos)
  apply (hasSum_mul_right_iff (hp_pos.ne')).mpr at this
  simp only [sub_sub_cancel] at this
  rw [inv_mul_eq_div, div_self hp_pos.ne'] at this
  exact this

@[deprecated geometricMeasure_real_singleton_pos (since := "2026-03-08")]
/-
**ProbabilityTheory.geometricPMFReal_pos** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：geometricPMFReal_pos {n : Nat} (hp_pos : 0 < p) (hp_lt_one : p < 1) : 0 < 
geometricPMFReal p n
参数：hp_pos : 0 < p；hp_lt_one : p < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.geometricPMFReal.eq_1`：∀ (p : ℝ) (n : ℕ), ProbabilityT
heory.geometricPMFReal p n = (1 - p) ^ n * p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `sub_pos_of_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRi
ghtStrictMono α] {a b : α}, b < a → 0 < a - b
-/
lemma geometricPMFReal_pos {n : ℕ} (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    0 < geometricPMFReal p n := by
  rw [geometricPMFReal]
  positivity [sub_pos.mpr hp_lt_one]

@[deprecated measureReal_nonneg (since := "2026-03-08")]
/-
**ProbabilityTheory.geometricPMFReal_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：geometricPMFReal_nonneg {n : Nat} (hp_pos : 0 < p) (hp_le_one : p <= 1) : 
0 <= geometricPMFReal p n
参数：hp_pos : 0 < p；hp_le_one : p <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.geometricPMFReal.eq_1`：∀ (p : ℝ) (n : ℕ), ProbabilityT
heory.geometricPMFReal p n = (1 - p) ^ n * p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma geometricPMFReal_nonneg {n : ℕ} (hp_pos : 0 < p) (hp_le_one : p ≤ 1) :
    0 ≤ geometricPMFReal p n := by
  rw [geometricPMFReal]
  positivity [sub_nonneg.mpr hp_le_one]

/-- Geometric distribution with success probability `p`. -/
@[deprecated geometricMeasure (since := "2026-03-08")]
noncomputable
/-
**ProbabilityTheory.geometricPMF** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：geometricPMF (hp_pos : 0 < p) (hp_le_one : p <= 1) : PMF Nat
参数：hp_pos : 0 < p；hp_le_one : p <= 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def geometricPMF (hp_pos : 0 < p) (hp_le_one : p ≤ 1) : PMF ℕ :=
  ⟨fun n ↦ ENNReal.ofReal (geometricPMFReal p n), by
    apply ENNReal.hasSum_coe.mpr
    rw [← toNNReal_one]
    exact (geometricPMFRealSum hp_pos hp_le_one).toNNReal
      (fun n ↦ geometricPMFReal_nonneg hp_pos hp_le_one)⟩

@[deprecated Measurable.of_discrete (since := "2026-03-08")]
/-
**ProbabilityTheory.measurable_geometricPMFReal** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：measurable_geometricPMFReal : Measurable (geometricPMFReal p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.of_discrete`：∀ {α : Type u_1} {β : Type u_2} [inst : Measurab
leSpace α] [inst_1 : MeasurableSpace β] [DiscreteMeasurableSpace α]   {f : α → β
}, Measurabl…
· 使用定理 `instDiscreteMeasurableSpace`：∀ {α : Type u_1}, DiscreteMeasurableSpace α
-/
lemma measurable_geometricPMFReal : Measurable (geometricPMFReal p) := by
  fun_prop

@[deprecated StronglyMeasurable.of_discrete (since := "2026-03-08")]
/-
**ProbabilityTheory.stronglyMeasurable_geometricPMFReal** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory`。
形式化陈述：stronglyMeasurable_geometricPMFReal : StronglyMeasurable (geometricPMFReal
 p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `stronglyMeasurable_iff_measurable`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : Topologic
alSpace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用引理 `ProbabilityTheory.measurable_geometricPMFReal`：measurable_geometricPMFRe
al : Measurable (geometricPMFReal p)
-/
lemma stronglyMeasurable_geometricPMFReal : StronglyMeasurable (geometricPMFReal p) :=
  stronglyMeasurable_iff_measurable.mpr measurable_geometricPMFReal

end GeometricPMF

end ProbabilityTheory

